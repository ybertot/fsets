(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

Require Import FSets FMaps Arith Min Compare_dec NArith Nnat Pnat Ndec.

Set Implicit Arguments.
Open Scope N_scope.

Module Type S.

  Declare Module E : OrderedType.
  Definition elt := E.t.

  Parameter t : Set. (** the abstract type of sets *)

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
  Parameter inter_1 : multi x (inter s s') = Nmin (multi x s) (multi x s').

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
        | Some p, Some p' => Some (Pmin p p')
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

 Definition equal := M.equal Peqb.

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
  Lemma inter_1 : multi x (inter s s') = Nmin (multi x s) (multi x s').
  Proof.
  unfold inter, multi; intros.
  rewrite F.map2_1bis; auto.
  destruct (M.find x s); destruct (M.find x s'); auto.
  unfold Nmin, Pmin, Nle.
  simpl.
  destruct (Pcompare p0 p1 Eq); auto.
  Qed.

  (** Specification of [diff] *)
  Lemma diff_1 : multi x (diff s s') = multi x s - multi x s'.
  Proof.
  unfold diff, multi; intros.
  rewrite F.map2_1bis; auto.
  destruct (M.find x s); destruct (M.find x s'); auto.
  simpl.
  destruct (Pcompare p0 p1 Eq); auto.
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
  unfold M.Equal; intros.
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
  apply Nle_Nminus_N0; auto.
  Qed.

  Lemma subset_2 : forall s s', subset s s' = true -> s[<=]s'.
  Proof.
  unfold subset, Subset; intros.
  assert (H0:=equal_2 H a).
  rewrite diff_1 in H0.
  rewrite empty_1 in H0.
  apply Nminus_N0_Nle; auto.
  Qed.

End Multi.


(* Example : A multiset on elements in type N *)
Module NMap := FMapList.Make N_as_OT.
Module NMulti := Multi N_as_OT NMap.

Definition mens1 := NMulti.update 2 7 (NMulti.update 3 5 (NMulti.empty)).
Definition mens2 := NMulti.update 1 4 (NMulti.update 3 6 (NMulti.empty)).

Eval compute in NMulti.elements (NMulti.union mens1 mens2). 

(* Example: total multiplicity *)

Definition total_multi s := NMulti.fold (fun _ p s => (Npos p+s)) s 0.

(*
Lemma total_multi_update: forall x n s, 
 total_multi (NMulti.update x n s) = total_multi s - NMulti.multi x s + n.
Proof.
unfold total_multi; intros.
do 2 rewrite NMulti.fold_1.
Admitted.

Lemma total_multi_union: 
 forall s s', total_multi (NMulti.union s s') = total_multi s + total_multi s'.
Proof.
Admitted.
*)

(* Well, these two last statements are certainly provable, but not without a 
 good deal of sweat. See the end of FSetProperties for something similar about 
 cardinals of (simple) sets. *)





