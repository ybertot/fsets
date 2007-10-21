
Require Import OrderedTypeEx FSetFacts FSetProperties.

Set Implicit Arguments.
Unset Strict Implicit.

Module UsualFacts (E:UsualOrderedType)(M:S with Module E:=E).
Module ME := OrderedTypeFacts M.E.  
Module MF := FSetFacts.Facts M.
Module MP := FSetProperties.Properties M.
Import ME.
Import MF.
Import M.
Import Logic. (* to unmask [eq] *)  
Import Peano. (* to unmask [lt] *)

(** * Specifications written using equivalences *)

Section IffSpec. 
Variable s s' s'' : t.
Variable x y z : elt.

Lemma singleton_iff : In y (singleton x) <-> x=y. 
Proof. apply singleton_iff. Qed.

Lemma add_iff : In y (add x s) <-> x=y \/ In y s.
Proof. apply add_iff. Qed.

Lemma add_neq_iff : x<>y -> (In y (add x s)  <-> In y s).
Proof. apply add_neq_iff. Qed.

Lemma remove_iff : In y (remove x s) <-> In y s /\ x<>y.
Proof. apply remove_iff. Qed.

Lemma remove_neq_iff : x<>y -> (In y (remove x s) <-> In y s).
Proof. apply remove_neq_iff. Qed.

Variable f : elt->bool.

Lemma filter_iff :  In x (filter f s) <-> In x s /\ f x = true.
Proof. apply filter_iff; congruence. Qed.

Lemma for_all_iff : 
  For_all (fun x => f x = true) s <-> for_all f s = true.
Proof. apply for_all_iff; congruence. Qed.
 
Lemma exists_iff :
  Exists (fun x => f x = true) s <-> exists_ f s = true.
Proof. apply exists_iff; congruence. Qed.

Lemma elements_iff : In x s <-> List.In x (elements s).
Proof. 
rewrite elements_iff.
rewrite SetoidList.InA_alt.
split; intros.
destruct H as (u,(H1,H2)); compute in H1; subst; auto.
exists x; split; compute; auto.
Qed.

End IffSpec.

(** Useful tactic for simplifying expressions like [In y (add x (union s s'))] *)
  
Ltac set_iff := 
 repeat (progress (
  rewrite add_iff || rewrite remove_iff || rewrite singleton_iff 
  || rewrite union_iff || rewrite inter_iff || rewrite diff_iff
  || rewrite empty_iff)).


(** Two equivalent sorted lists are in fact equal. *)

Definition equivlist (l l':list elt) := forall x, List.In x l <-> List.In x l'.

Lemma list_unique : forall l l', 
 sort E.lt l -> sort E.lt l' -> equivlist l l' -> l=l'.
Proof.
induction l; destruct l'; simpl; auto; intros.
elimtype False; rewrite (H1 t0); simpl; auto.
elimtype False; rewrite <- (H1 a); simpl; auto.
inversion_clear H; inversion_clear H0.
assert (forall y, List.In y l -> M.E.lt a y).
 intros; eapply Sort_Inf_In with (l:=l); eauto.
assert (forall y, List.In y l' -> M.E.lt t0 y).
 intros; eapply Sort_Inf_In with (l:=l'); eauto.
clear H3 H4.
assert (a=t0).
 destruct (H1 a).
 destruct (H1 t0).
 simpl in H3; destruct H3; auto.
 simpl in H7; destruct H7; auto.
 elimtype False; generalize (H5 _ H3) (H0 _ H7).
 ME.order.
f_equal; auto.
apply IHl; auto.
split; intros.
destruct (H1 x).
destruct H6; simpl; auto.
elimtype False; generalize (H0 _ H4); subst a; subst x; ME.order.
destruct (H1 x).
destruct H7; simpl; auto.
elimtype False; generalize (H5 _ H4); subst a; subst x; ME.order.
Qed. 

Lemma Equal_elements_equivlist : 
 forall s s', s[=]s' <-> equivlist (elements s) (elements s').
Proof.
unfold Equal; split; intros.
red; intros.
do 2 rewrite <- elements_iff; auto.
do 2 rewrite elements_iff; auto.
Qed.

Lemma Equal_eq_elements : 
 forall s s', s[=]s' <-> elements s = elements s'.
Proof.
split; intros.
apply list_unique; auto with set.
rewrite <- Equal_elements_equivlist; auto.
red; intros; do 2 rewrite elements_iff; auto.
rewrite H; split; auto.
Qed.

Lemma elements_min : forall s x,
 min_elt s = Some x -> 
 elements s = x::elements (remove x s).
Proof.
intros.
apply list_unique; auto with set.
constructor; auto with set.
rewrite Inf_alt; auto with set; intros.
rewrite <- MF.elements_iff in H0.
assert (H1:=@min_elt_2 _ _ y H).
destruct (E.compare x y); auto.
elim (remove_1 e H0).
elim H1; auto.
eapply remove_3; eauto.

red; intros; simpl.
do 2 rewrite <- elements_iff; set_iff; intuition.
destruct (ME.eq_dec x x0); unfold E.eq; intuition.
subst x0.
apply min_elt_1; auto.
Qed.

Lemma elements_max : forall s x,
 max_elt s = Some x -> 
 elements s = elements (remove x s)++x::nil.
Proof.
intros.
apply list_unique; auto with set.
apply SortA_app with M.E.eq; try red; auto with set.
intros z y H0; revert y; rewrite <- Inf_alt; auto; constructor.
rewrite <- MF.elements_iff in H0.
assert (H1:=@max_elt_2 _ _ z H).
destruct (E.compare x z); auto.
elim H1; auto.
eapply remove_3; eauto.
elim (remove_1 e H0).

split; intros.
apply in_or_app; simpl.
intros; rewrite <- elements_iff in *.
destruct (ME.eq_dec x x0); unfold E.eq; intuition.
destruct (in_app_or _ _ _ H0); clear H0.
intros; rewrite <- elements_iff in *; eauto with set.
simpl in H1; inversion H1; subst; auto.
intros; rewrite <- elements_iff in *; auto with set.
contradiction.
Qed.

End UsualFacts.


Module FoldEquiv (E:UsualOrderedType)(M:S with Module E:=E).
Module UF := UsualFacts E M.
Import UF M.
Section Fold.

Variable A:Type.
Variable f:elt->A->A.

(** a few definitions equivalent to fold *)

Fixpoint fold_direct (n:nat)(s:t)(i:A) { struct n } : A := 
 match n with 
  | O => i 
  | S n => match max_elt s with 
           | None => i
           | Some x => f x (fold_direct n (remove x s) i)
           end
  end.

Fixpoint fold_tail (n:nat)(s:t)(i:A) { struct n } : A := 
 match n with 
  | O => i 
  | S n => match min_elt s with 
           | None => i
           | Some x => fold_tail n (remove x s) (f x i)
           end
  end.

Lemma fold_direct_1 : 
 forall s i, fold_direct (cardinal s) s i = fold f s i.
Proof.
intros s; remember (cardinal s) as n; revert s Heqn; induction n; simpl; intros.
rewrite fold_1.
rewrite cardinal_1 in Heqn.
destruct (elements s); [clear Heqn|inversion Heqn]; simpl; auto.
rewrite fold_1.
case_eq (max_elt s); intros.
rewrite (elements_max H).
rewrite fold_left_app.
simpl; f_equal.
rewrite <- fold_1.
apply IHn.
assert (S (cardinal (remove e s)) = S n).
 rewrite Heqn.
 apply MP.remove_cardinal_1.
 apply max_elt_1; auto.
inversion H0; auto.
rewrite (MP.cardinal_1 (max_elt_3 H)) in Heqn; inversion Heqn.
Qed.

Lemma fold_tail_1_aux : 
 forall n l s s' i, n = cardinal s' -> 
  elements s = l++elements s' -> 
  fold_tail n s' (fold_left (fun x y => f y x) l i) = fold f s i.
Proof.
induction n.
simpl.
intros; rewrite fold_1.
rewrite cardinal_1 in H.
destruct (elements s'); [clear H|inversion H]; simpl; auto.
rewrite <- app_nil_end in H0; subst l; auto.

simpl; intros.
case_eq (min_elt s'); intros.
rewrite (elements_min H1) in H0.
rewrite <- (IHn (l++e::nil) s (remove e s')).
rewrite fold_left_app; simpl; auto.
assert (S (cardinal (remove e s')) = S n).
 rewrite H.
 apply MP.remove_cardinal_1.
 apply min_elt_1; auto.
inversion H2; auto.

rewrite app_ass; simpl; auto.

rewrite (MP.cardinal_1 (min_elt_3 H1)) in H; inversion H.
Qed.

Lemma fold_tail_1 : forall s i, 
 fold_tail (cardinal s) s i = fold f s i.
Proof.
intros; apply (@fold_tail_1_aux (cardinal s) nil s s i); auto.
Qed.

End Fold.
End FoldEquiv.


(* Beware: a Program version needs extensionnality! *)
Require Import Coq.Program.Utils FunctionalExtensionality.

Module FoldProgram (E:UsualOrderedType)(M:S with Module E:=E).
Module UF := UsualFacts E M.
Import UF M.
Section Fold.

Variable A:Type.
Variable f:elt->A->A.

Program Fixpoint fold_direct_prog (s:t)(i:A)
 { measure cardinal s } : A := 
  match max_elt s with 
  | None => i
  | Some x => f x (fold_direct_prog (remove x s) i)
  end.

Next Obligation.
 symmetry in Heq_anonymous.
 rewrite <- (@MP.remove_cardinal_1 s x); auto with arith set.
Qed.

Program Fixpoint fold_tail_prog (s:t)(i:A)
 { measure cardinal s } : A := 
  match min_elt s with 
  | None => i
  | Some x => fold_tail_prog (remove x s) (f x i)
  end.

Next Obligation.
 symmetry in Heq_anonymous.
 rewrite <- (@MP.remove_cardinal_1 s x); auto with arith set.
Qed.

Lemma fold_direct_prog_1 : 
 forall s i, fold_direct_prog s i = fold f s i.
Proof.
intros s; remember (cardinal s) as n; revert s Heqn.
induction n using Wf_nat.lt_wf_ind; intros.
unfold fold_direct_prog.
rewrite fix_sub_measure_eq_ext; auto.
simpl.
generalize (@max_elt_1 s) (@max_elt_2 s) (@max_elt_3 s) (@elements_max s).
destruct (max_elt s); intros.
change (f e (fold_direct_prog (remove e s) i) = fold f s i).
rewrite fold_1.
rewrite (H3 e); auto.
rewrite fold_left_app; simpl; f_equal.
rewrite <- fold_1.
assert (S (cardinal (remove e s)) = n).
 rewrite Heqn.
 apply MP.remove_cardinal_1; auto.
apply H with (cardinal (remove e s)); auto.
rewrite <- H4; auto with arith.

rewrite fold_1.
generalize (cardinal_1 s).
rewrite MP.cardinal_1; auto.
destruct (elements s); simpl; auto; inversion 1.
Qed.

Lemma fold_tail_prog_1_aux : 
 forall n l s s' i, n = cardinal s' -> 
  elements s = l++elements s' -> 
  fold_tail_prog s' (fold_left (fun x y => f y x) l i) = fold f s i.
Proof.
induction n using Wf_nat.lt_wf_ind; intros.
unfold fold_tail_prog.
rewrite fix_sub_measure_eq_ext; auto.
simpl.
generalize (@min_elt_1 s') (@min_elt_2 s') (@min_elt_3 s') (@elements_min s').
destruct (min_elt s'); intros.
change (fold_tail_prog (remove e s') (f e (fold_left (fun x y => f y x) l i)) 
        = fold f s i).
rewrite (H5 e) in H1; auto.
assert (S (cardinal (remove e s')) = n).
 rewrite H0.
 apply MP.remove_cardinal_1; auto.
assert (cardinal (remove e s') < n).
 rewrite <- H6; auto.
rewrite <- (@H _ H7 (l++e::nil) s (remove e s')); auto.
rewrite fold_left_app; simpl; auto.

rewrite app_ass; simpl; auto.

rewrite fold_1.
generalize (cardinal_1 s').
rewrite MP.cardinal_1; auto.
destruct (elements s'); simpl; auto; inversion 1.
rewrite <- app_nil_end in H1; subst l; auto.
Qed.

Lemma fold_tail_prog_1 : forall s i, 
 fold_tail_prog s i = fold f s i.
Proof.
intros; apply (@fold_tail_prog_1_aux (cardinal s) nil s s i); auto.
Qed.

End Fold.
End FoldProgram.

