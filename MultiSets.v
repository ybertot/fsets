(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

Require Import FSets FMaps Arith Min Compare_dec NArith Nnat Pnat Ndec.
Import Morphisms.

Set Implicit Arguments.

Open Scope N_scope.

Module Type S.

  Declare Module E : OrderedType.
  Definition elt := E.t.

  Parameter t : Type. (** the abstract type of sets *)

  Parameter empty : t.
  (** The empty set. *)

  Parameter multi : elt -> t -> N.
  (** [multi t s] gives the multiplicity of [t] in the multiset [s]. *)

  Parameter update : elt -> N -> t -> t.
  (** [update x m s] returns a multiset identical to [s], except that 
    multiplicity of [x] is now [m] *)

  Parameter union : t -> t -> t.

  Parameter inter : t -> t -> t.

  Parameter diff : t -> t -> t.

  Parameter equal : t -> t -> bool.

  Parameter subset : t -> t -> bool.

  Parameter fold : forall A : Type, (elt -> positive -> A -> A) -> t -> A -> A.
  (** [fold] encounters only elements with non-null multiplicity *)

  Parameter elements : t -> list (elt * positive).
  (** [elements] returns the list of elements with non-null multiplicity *) 


  (** Logical predicates *)
  Definition Equal s s' := forall a : elt, multi a s = multi a s'.
  Definition Subset s s' := forall a : elt, multi a s <= multi a s'.
  Definition Empty s := forall a : elt, multi a s = 0.
  
  Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
  Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).

  Section Spec. 

  Variable s s' s'' : t.
  Variable x y : elt.
  Variable n : N.
  Variable p : positive.

  (** Specification of [equal] *) 
  Parameter equal_1 : s[=]s' -> equal s s' = true.
  Parameter equal_2 : equal s s' = true ->s[=]s'.

  (** Specification of [subset] *)
  Parameter subset_1 : s[<=]s' -> subset s s' = true.
  Parameter subset_2 : subset s s' = true -> s[<=]s'.

  (** Specification of [empty] *)
  Parameter empty_1 : Empty empty.

  (** Specification of [update] *)
  Parameter update_1 : E.eq x y -> multi y (update x n s) = n.
  Parameter update_2 : ~E.eq x y -> multi y (update x n s) = multi y s.

  (** Specification of [union] *)
  Parameter union_1 : multi x (union s s') = multi x s + multi x s'.

  (** Specification of [inter] *)
  Parameter inter_1 : multi x (inter s s') = N.min (multi x s) (multi x s').

  (** Specification of [diff] *)
  Parameter diff_1 : multi x (diff s s') = multi x s - multi x s'.
 
  (** Specification of [fold] *)  
  Parameter fold_1 : forall (A : Type) (i : A) (f : elt -> positive -> A -> A),
      fold f s i = fold_left (fun a p => f (fst p) (snd p) a) (elements s) i.

  Definition eq_pair (p p':elt*positive) :=
    E.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Definition lt_pair (p p':elt*positive) := E.lt (fst p) (fst p').

  (** Specification of [elements] *)
  Parameter elements_1 : multi x s = Npos p -> InA eq_pair (x,p) (elements s).
  Parameter elements_2 : InA eq_pair (x,p) (elements s) -> multi x s = Npos p.
  Parameter elements_3 : sort lt_pair (elements s).  

  End Spec.

End S.

Module Multi (X:OrderedType)(M:FMapInterface.S with Module E:=X) 
 <: S with Module E:=X.

 Module E := X.

 Definition elt:=E.t.

 Definition t := M.t positive.
 Definition empty := M.empty positive.
 Definition multi x t := match M.find x t with 
  | None => 0 
  | Some p => Npos p 
 end.

 Definition update x n s := match n with 
  | N0 => M.remove x s
  | Npos p => M.add x p s
 end.

 Definition union := M.map2 
   (fun o o' => 
      match o,o' with 
        | None, None => None
        | None, Some p => Some p
        | Some p, None => Some p
        | Some p, Some p' => Some (Pplus p p')
      end).

 Definition inter := M.map2 
   (fun o o' => 
      match o,o' with 
        | Some p, Some p' => Some (Pos.min p p')
        | _, _ => None
      end).

 Definition diff := M.map2 
   (fun o o' => 
      match o,o' with 
        | None, _ => None
        | Some p, None => Some p
        | Some p, Some p' => match Pcompare p p' Eq with 
            | Lt | Eq => None 
            | Gt => Some (Pminus p p')
          end
      end).

 Definition fold := @M.fold positive.

 Definition elements := @M.elements positive.

 Definition equal := M.equal Pos.eqb.

 Definition subset s s' := equal (diff s s') empty.


 Definition Equal s s' := forall a : elt, multi a s = multi a s'.
 Definition Subset s s' := forall a : elt, multi a s <= multi a s'.
 Definition Empty s := forall a : elt, multi a s = 0.
  
 Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
 Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).

  Module F := FMapFacts.Facts(M).

  Section Spec. 

  Variable s s' s'' : t.
  Variable x y : elt.
  Variable n : N.
  Variable p : positive.

  (** Specification of [empty] *)
  Lemma empty_1 : Empty empty.
  Proof.
  unfold Empty, empty, multi; intros.
  rewrite F.empty_o; auto.
  Qed.

  (** Specification of [update] *)
  Lemma update_1 : E.eq x y -> multi y (update x n s) = n.
  Proof.
  unfold update, multi; intros.
  destruct n.
  rewrite F.remove_eq_o; auto.
  rewrite F.add_eq_o; auto.
  Qed.

  Lemma update_2 : ~E.eq x y -> multi y (update x n s) = multi y s.
  Proof.
  unfold update, multi; intros.
  destruct n.
  rewrite F.remove_neq_o; auto.
  rewrite F.add_neq_o; auto.
  Qed.

  (** Specification of [union] *)
  Lemma union_1 : multi x (union s s') = multi x s + multi x s'.
  Proof.
  unfold union, multi; intros.
  rewrite F.map2_1bis; auto.
  destruct (M.find x s); destruct (M.find x s'); auto.
  Qed.

  (** Specification of [inter] *)
  Lemma inter_1 : multi x (inter s s') = N.min (multi x s) (multi x s').
  Proof.
  unfold inter, multi; intros.
  rewrite F.map2_1bis; auto.
  destruct (M.find x s); destruct (M.find x s'); auto.
  unfold N.min, Pos.min, N.le.
  simpl.
  destruct (Pos.compare p0 p1); auto.
  Qed.

  (** Specification of [diff] *)
  Lemma diff_1 : multi x (diff s s') = multi x s - multi x s'.
  Proof.
  unfold diff, multi; intros.
  rewrite F.map2_1bis; auto.
  destruct (M.find x s); destruct (M.find x s'); auto.
  simpl.
  case_eq (Pcompare p0 p1 Eq); intro H.
  apply Pcompare_Eq_eq in H. rewrite H. now rewrite Pminus_mask_diag.
  now rewrite (Pminus_mask_Lt p0 p1 H).
  pose proof (Pminus_mask_Gt p0 p1 H) as H1. unfold Pminus.
  destruct H1 as [h [H1 _]]; now rewrite H1.
  Qed.

  (** Specification of [fold] *)  
  Lemma fold_1 : forall (A : Type) (i : A) (f : elt -> positive -> A -> A),
      fold f s i = fold_left (fun a p => f (fst p) (snd p) a) (elements s) i.
  Proof.
  intros; unfold fold, elements.
  apply M.fold_1.
  Qed.

  Definition eq_pair (p p':elt*positive) :=
    E.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Definition lt_pair (p p':elt*positive) := E.lt (fst p) (fst p').

  (** Specification of [elements] *)
  Lemma elements_1 : multi x s = Npos p -> InA eq_pair (x,p) (elements s).
  Proof.
  unfold multi, elements; intros.
  apply (@M.elements_1 positive).
  apply M.find_2.
  destruct (M.find x s); congruence || discriminate.
  Qed.

  Lemma elements_2 : InA eq_pair (x,p) (elements s) -> multi x s = Npos p.
  Proof.
  unfold multi, elements; intros.
  assert (H0:=@M.elements_2 positive _ _ _ H).
  rewrite F.find_mapsto_iff in H0; rewrite H0; auto.
  Qed.

  Lemma elements_3 : sort lt_pair (elements s).
  Proof.
  apply (@M.elements_3 positive).
  Qed.
 
  (** Specification of [equal] *) 
  Lemma equal_1 : s[=]s' -> equal s s' = true.
  Proof.
  unfold equal, Equal, multi; intros.
  apply M.equal_1.
  unfold M.Equivb, Cmp; intros.
  split; intros.
  generalize (H k); clear H; intros H.
  unfold M.In.
  split; intros (e,He); exists e; rewrite F.find_mapsto_iff in *.
   rewrite He in H; simpl in *.
   destruct (M.find k s'); auto; discriminate || congruence.
   rewrite He in H; simpl in *.
   destruct (M.find k s); auto; discriminate || congruence.
  rewrite F.find_mapsto_iff in *.
  generalize (H k); clear H.
  rewrite H0; rewrite H1; simpl.
  inversion 1; subst; apply Peqb_correct.
  Qed.

  Lemma equal_2 : equal s s' = true ->s[=]s'.
  Proof.
  unfold equal, Equal, multi; intros.
  generalize (M.equal_2 H); clear H; intros H.
  destruct H.
  unfold Cmp in *.
  case_eq (M.find a s); case_eq (M.find a s'); simpl; intros; auto.
  assert (H3:=H0 a p1 p0).
  do 2 rewrite F.find_mapsto_iff in H3.
  f_equal.
  apply Peqb_complete; auto.
  assert (M.In a s) by (exists p0; apply M.find_2; auto).
  rewrite H in H3.
  destruct H3; rewrite F.find_mapsto_iff in H3; congruence.
  assert (M.In a s') by (exists p0; apply M.find_2; auto).
  rewrite <- H in H3.
  destruct H3; rewrite F.find_mapsto_iff in H3; congruence.
  Qed.

  End Spec.

  (** Specification of [subset] *)
  Lemma subset_1 : forall s s', s[<=]s' -> subset s s' = true.
  Proof.
  unfold subset, Subset; intros.
  apply equal_1.
  red; intros.
  rewrite diff_1.
  rewrite empty_1.
  apply <- Nminus_N0_Nle; auto.
  Qed.

  Lemma subset_2 : forall s s', subset s s' = true -> s[<=]s'.
  Proof.
  unfold subset, Subset; intros.
  assert (H0:=equal_2 H a).
  rewrite diff_1 in H0.
  rewrite empty_1 in H0.
  apply -> Nminus_N0_Nle; auto.
  Qed.

End Multi.


(* Example : A multiset on elements in type N *)

Module Ma := FMapList.Make N_as_OT.
Module Mu := Multi N_as_OT Ma.

Definition mens1 := Mu.update 2 7 (Mu.update 3 5 (Mu.empty)).
Definition mens2 := Mu.update 1 4 (Mu.update 3 6 (Mu.empty)).

Eval compute in Mu.elements (Mu.union mens1 mens2). 

(* Example: total multiplicity *)

Definition fmu := fun (_:Ma.key) p s => (Npos p) + s.

Definition total_multi s := Mu.fold fmu s 0.

Module Import NP := FMapFacts.Properties Ma.
Import NP.F.
Module Import NP' := FMapFacts.OrdProperties Ma.

Lemma fmu_compat : Proper (eq==>eq==>eq==>eq) fmu.
Proof.
 repeat red; intros; subst; auto.
Qed.

Lemma fmu_transp : transpose_neqkey eq fmu.
Proof.
 red; intros.
 unfold fmu; do 2 rewrite Nplus_assoc; f_equal; apply Nplus_comm; auto.
Qed.
Hint Resolve fmu_compat fmu_transp : core.

Lemma total_multi_union:
 forall s s', total_multi (Mu.union s s') = total_multi s + total_multi s'.
Proof.
unfold total_multi, Mu.fold.
induction s using map_induction; intros.
rewrite elements_Empty in H.
rewrite (@fold_Equal _ (Mu.union s s') s' _ (@eq N)); auto.
rewrite (Ma.fold_1 s); rewrite H; auto.
 red; intros; unfold Mu.union; rewrite map2_1bis; auto.
 rewrite (elements_o s); rewrite H; simpl.
 destruct (Ma.find y s'); auto.

replace (Ma.fold fmu s2 0) with (fmu x e (Ma.fold fmu s1 0))
 by (symmetry; apply fold_Add; auto).
unfold fmu at 2; simpl @snd.
rewrite <- Nplus_assoc.
rewrite <- IHs1.
case_eq (Ma.find x s'); intros.
(* x may appear in s' hence in (Mu.union s1 s'). In this case we introduce 
   artificially (Ma.remove x (Mu.union s1 s')) and reason in two steps. *)
set (u:=Ma.remove x (Mu.union s1 s')).
replace (Ma.fold fmu (Mu.union s2 s') 0) with (fmu x (Pplus e p) (Ma.fold fmu u 0)); 
 [ | symmetry; apply fold_Add; auto ].
replace (Ma.fold fmu (Mu.union s1 s') 0) with (fmu x p (Ma.fold fmu u 0)); 
 [ | symmetry; apply fold_Add; auto ].
unfold fmu at 1 3; rewrite Nplus_assoc; f_equal.
unfold u; apply Ma.remove_1; auto.
unfold u, Mu.union; red; intros; rewrite add_o; rewrite remove_o.
rewrite map2_1bis; auto.
(* destruct (eq_dec x y); auto. ----> Not_found *)
destruct (P.F.eq_dec x y); auto.
compute in e0; subst; rewrite H1; auto.
rewrite not_find_mapsto_iff in H; rewrite H; auto.
unfold u; apply Ma.remove_1; auto.
unfold u, Mu.union; red; intros; rewrite add_o; rewrite remove_o.
do 2 (rewrite map2_1bis; auto).
rewrite H0; rewrite add_o.
destruct (P.F.eq_dec x y); auto.
compute in e0; subst; rewrite H1; auto.
(* simple situation where x isn't in s' *)
change (Nplus (Npos e)) with (fmu x e).
apply fold_Add; auto.
rewrite not_find_mapsto_iff; rewrite not_find_mapsto_iff in H.
unfold Mu.union; rewrite map2_1bis; auto; rewrite H1; rewrite H; auto.
red; intros; unfold Mu.union; rewrite add_o.
do 2 (rewrite map2_1bis; auto).
rewrite H0; rewrite add_o.
destruct (P.F.eq_dec x y); auto.
compute in e0; subst; rewrite H1; auto.
Qed.

Lemma total_multi_update: forall s x n, 
 total_multi (Mu.update x n s) + Mu.multi x s  = total_multi s + n.
Proof.
unfold total_multi, Mu.fold.
induction s using map_induction; intros.

rewrite elements_Empty in H.
unfold Mu.multi.
rewrite elements_o; rewrite H; simpl.
unfold Mu.update; destruct n.
do 2 rewrite Nplus_0_r.
apply fold_Equal with (eqA:=@eq _); auto.
 red; intros; rewrite remove_o; rewrite elements_o; rewrite H; simpl.
 destruct (P.F.eq_dec x y); auto.
rewrite Nplus_0_r; rewrite Nplus_comm.
change (Nplus (Npos p)) with (fmu x p).
apply fold_Add with (eqA:=@eq _); auto.
 rewrite not_find_mapsto_iff; rewrite elements_o; rewrite H; auto.
 red; auto.

rename x0 into y; rename H into A1; rename H0 into A2.
replace (Ma.fold fmu s2 0) with (fmu x e (Ma.fold fmu s1 0)) 
 by (symmetry; apply fold_Add; auto).
unfold fmu at 2; rewrite <- Nplus_assoc. 
rewrite <- (IHs1 y n); clear IHs1; rewrite Nplus_assoc.
destruct (P.F.eq_dec x y) as [E|E].
(* x=y *)
compute in E; subst y.
replace (Mu.multi x s2) with (Npos e).
replace (Mu.multi x s1) with 0.
rewrite Nplus_0_r; rewrite Nplus_comm; f_equal.
apply fold_Equal with (eqA:=@eq _); eauto.
red; intros; unfold Mu.update; destruct n.
do 2 rewrite remove_o; rewrite A2; rewrite add_o.
destruct (P.F.eq_dec x y); auto.
do 2 rewrite add_o; rewrite A2; rewrite add_o.
destruct (P.F.eq_dec x y); auto.
unfold Mu.multi; rewrite not_find_mapsto_iff in A1; rewrite A1; auto.
unfold Mu.multi.
rewrite A2; rewrite add_o.
destruct (P.F.eq_dec x x) as [_|H]; [ auto | elim H; ME.order ].
(* x<>y *)
replace (Mu.multi y s2) with (Mu.multi y s1).
f_equal.
change (Nplus (Npos e)) with (fmu x e).
apply fold_Add; auto.
rewrite not_find_mapsto_iff; rewrite not_find_mapsto_iff in A1.
assert (y<>x) by (contradict E; auto).
generalize (Mu.update_2 s1 n H).
unfold Mu.multi; rewrite A1.
destruct (Ma.find x (Mu.update y n s1)); intros; discriminate || auto.
red; intros; rewrite add_o.
unfold Mu.update; destruct n; 
 rewrite ?remove_o, ?add_o, A2, ?remove_o, ?add_o; 
 destruct P.F.eq_dec; destruct P.F.eq_dec; auto; congruence.
unfold Mu.multi; rewrite A2, add_o.
destruct (P.F.eq_dec x y) as [H|_]; [ elim E; auto | auto ].
Qed.
