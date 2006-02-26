(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Finite sets library.  
 * Authors: Pierre Letouzey and Jean-Christophe Filliâtre 
 * Institution: LRI, CNRS UMR 8623 - Université Paris Sud
 *              91405 Orsay, France *)

(* $Id$ *)

(** This functor derives additional properties from [FSetInterface.S].
    Contrary to the functor in [FSetEqProperties] it uses 
    predicates over sets instead of sets operations, i.e.
    [In x s] instead of [mem x s=true], 
    [Equal s s'] instead of [equal s s'=true], etc. *)

Require Import Omega.

Open Scope nat_scope.

Require Export FSetInterface. 
Require Export Bool.
Require Export Sumbool.
Require Export Zerob. 
Set Implicit Arguments.
Unset Strict Implicit.

Section Misc.
Variable A B : Set.
Variable eqA : A -> A -> Prop. 
Variable eqB : B -> B -> Prop.

(** Two-argument functions that allow to reorder its arguments. *)
Definition transpose (f : A -> B -> B) :=
  forall (x y : A) (z : B), eqB (f x (f y z)) (f y (f x z)). 

(** Compatibility of a two-argument function with respect to two equalities. *)
Definition compat_op (f : A -> B -> B) :=
  forall (x x' : A) (y y' : B), eqA x x' -> eqB y y' -> eqB (f x y) (f x' y').

(** Compatibility of a function upon natural numbers. *)
Definition compat_nat (f : A -> nat) :=
  forall x x' : A, eqA x x' -> f x = f x'.

End Misc.
Hint Unfold transpose compat_op compat_nat.

(** To prove [(Setoid_Theory ? (eq ?))] *)
Ltac ST :=
  constructor; intros;
   [ trivial | symmetry  in |- *; trivial | eapply trans_eq; eauto ].
Hint Extern 1 (Setoid_Theory _ (eq (A:=_))) => ST: core.

Definition gen_st : forall A : Set, Setoid_Theory _ (eq (A:=A)).
auto.
Qed.

(** Usual syntax for lists. *)
Notation "[]" := nil (at level 0).


Module Properties (M: S).
  Import M.
  Import Logic. (* to unmask [eq] *)  
  Import Peano. (* to unmask [lt] *)
  
  Module ME := OrderedTypeFacts E.  
   (** Results about lists without duplicates *)

  Notation NoRedun := (noredunA E.eq).

  Section noredunA_Remove.

  Definition remove_list x l := 
    remove_1st (fun y => if ME.eq_dec x y then true else false) l.
 
  Lemma remove_list_correct :
    forall s x,
    NoRedun s -> NoRedun (remove_list x s) /\
    (forall y : elt, ME.In y (remove_list x s) <-> ME.In y s /\ ~ E.eq x y).
   Proof.
   simple induction s; simpl in |- *.
   split; auto.
   intuition.
   inversion H0.
   intros; inversion_clear H0; case (ME.eq_dec x a); trivial.  
   intuition.
   apply H1; eapply ME.In_eq with y; eauto.
   inversion_clear H3; auto.
   elim H4; eauto. 
   elim (H x H2); intros.
   split.
   elim (H3 a); constructor; intuition.
   intro y; elim (H3 y); clear H3; intros.
   intuition.  
   inversion_clear H4; auto.
   elim (H3 H6); auto.
   inversion_clear H4; auto.
   intuition eauto.
   elim (H3 H7); firstorder.
   inversion_clear H6; firstorder. 
   Qed. 

   Let ListEq l l' := forall y : elt, ME.In y l <-> ME.In y l'.
   Let ListAdd x l l' := forall y : elt, ME.In y l' <-> E.eq y x \/ ME.In y l.

   Lemma remove_list_equal :
    forall (s s' : list elt) (x : elt),
    NoRedun (x :: s) ->
    NoRedun s' -> ListEq (x :: s) s' -> ListEq s (remove_list x s').
   Proof.  
   unfold ListEq in |- *; intros. 
   inversion_clear H.
   elim (remove_list_correct x H0); intros.
   elim (H4 y); intros.
   elim (H1 y); intros.
   split; intros.
   apply H6; split; auto. 
   intro.
   elim H2; apply ME.In_eq with y; eauto.
   elim (H5 H9); intros.
   assert (H12 := H8 H10). 
   inversion_clear H12; auto.
   elim H11; eauto. 
   Qed. 

   Lemma remove_list_add :
    forall (s s' : list elt) (x x' : elt),
    NoRedun s ->
    NoRedun (x' :: s') ->
    ~ E.eq x x' ->
    ~ ME.In x s -> ListAdd x s (x' :: s') -> ListAdd x (remove_list x' s) s'.
   Proof.
   unfold ListAdd in |- *; intros.
   inversion_clear H0.
   elim (remove_list_correct x' H); intros.
   elim (H6 y); intros.
   elim (H3 y); intros.
   split; intros.
   elim H9; auto; intros.
   elim (ME.eq_dec y x); auto; intros.
   right; apply H8; split; auto.
   intro; elim H4; apply ME.In_eq with y; auto.
   inversion_clear H11.
   assert (ME.In y (x' :: s')). auto.
   inversion_clear H11; auto.
   elim H1; eauto.
   elim (H7 H12); intros.
   assert (ME.In y (x' :: s')). auto.
   inversion_clear H14; auto.
   elim H13; auto. 
   Qed.

   Lemma remove_list_fold_right :
    forall (A : Set) (eqA : A -> A -> Prop) (st : Setoid_Theory A eqA)
      (i : A) (f : elt -> A -> A),
    compat_op E.eq eqA f ->
    transpose eqA f ->
    forall (s : list elt) (x : elt),
    NoRedun s ->
    ME.In x s ->
    eqA (fold_right f i s) (f x (fold_right f i (remove_list x s))).
   Proof.
   simple induction s; simpl in |- *.  
   intros; inversion H2.
   intros.
   inversion_clear H2.
   case (ME.eq_dec x a); simpl in |- *; intros.
   apply H; auto. 
   apply Seq_refl; auto. 
   inversion_clear H3. 
   elim n; auto.
   apply
    (Seq_trans _ _ st) with (f a (f x (fold_right f i (remove_list x l)))).
   apply H; auto.
   apply H0; auto.
   Qed.   

   Lemma fold_right_equal :
    forall (A : Set) (eqA : A -> A -> Prop) (st : Setoid_Theory A eqA)
      (i : A) (f : elt -> A -> A),
    compat_op E.eq eqA f ->
    transpose eqA f ->
    forall s s' : list elt,
    NoRedun s ->
    NoRedun s' ->
    ListEq s s' -> eqA (fold_right f i s) (fold_right f i s').
   Proof.
   simple induction s.
   intro s'; case s'; simpl in |- *. 
   intros; apply Seq_refl; auto.
   unfold ListEq in |- *; intros.
   elim (H3 e); intros. 
   assert (X : ME.In e []); auto; inversion X.
   intros x l Hrec s' U U' E.
   simpl in |- *.   
   apply (Seq_trans _ _ st) with (f x (fold_right f i (remove_list x s'))).
   apply H; auto.
   apply Hrec; auto.
   inversion U; auto.
   elim (remove_list_correct x U'); auto.
   apply remove_list_equal; auto.
   apply Seq_sym; auto.
   apply remove_list_fold_right with (eqA := eqA); auto.
   unfold ListEq in E; firstorder.
   Qed.

   Lemma fold_right_add :
    forall (A : Set) (eqA : A -> A -> Prop) (st : Setoid_Theory A eqA)
      (i : A) (f : elt -> A -> A),
    compat_op E.eq eqA f ->
    transpose eqA f ->
    forall (s' s : list elt) (x : elt),
    NoRedun s ->
    NoRedun s' ->
    ~ ME.In x s ->
    ListAdd x s s' -> eqA (fold_right f i s') (f x (fold_right f i s)).
   Proof.   
   simple induction s'.
   unfold ListAdd in |- *; intros.
   elim (H4 x); intros. 
   assert (X : ME.In x []); auto; inversion X.
   intros x' l' Hrec s x U U' IN EQ; simpl in |- *.
   (* if x=x' *)
   case (ME.eq_dec x x'); intros.
   apply H; auto.
   apply fold_right_equal with (eqA := eqA); auto.
   inversion_clear U'; trivial.
   unfold ListEq in |- *; unfold ListAdd in EQ.
   intros. 
   elim (EQ y); intros.
   split; intros.
   elim H1; auto.
   intros; inversion_clear U'.
   elim H5; apply ME.In_eq with y; eauto.
   assert (ME.In y (x' :: l')); auto; inversion_clear H4; auto.
   elim IN; apply ME.In_eq with y; eauto.
   (* else x<>x' *)   
   apply
    (Seq_trans _ _ st) with (f x' (f x (fold_right f i (remove_list x' s)))).
   apply H; auto.
   apply Hrec; auto.
   elim (remove_list_correct x' U); auto.
   inversion_clear U'; auto.
   elim (remove_list_correct x' U); intros; intro.
   firstorder.
   apply remove_list_add; auto.
   apply
    (Seq_trans _ _ st) with (f x (f x' (fold_right f i (remove_list x' s)))).
   apply H0; auto.
   apply H; auto.
   apply Seq_sym; auto.
   apply remove_list_fold_right with (eqA := eqA); auto.
   elim (EQ x'); intros. 
   elim H1; auto; intros; elim n; auto.
   Qed.

  End noredunA_Remove.


  (** * Alternative (weaker) specification for [fold],
        based on [empty] ([fold_1]) and [add] ([fold_2]). *)

  Section Old_Spec_Now_Properties. 


  (** When [FSets] was first designed, the order in which Ocaml's [Set.fold]
        takes the set elements was unspecified. This specification reflects this fact: 
  *)

  Lemma fold_0 : 
      forall (s:t) (A : Set) (i : A) (f : elt -> A -> A),
      exists l : list elt,
        NoRedun l /\
        (forall x : elt, In x s <-> InA E.eq x l) /\
        fold f s i = fold_right f i l.
  Proof.
  intros; exists (rev (elements s)).
  split.
  apply noredunA_rev; eauto.
  split.
  intros.
  destruct (InA_alt E.eq x (rev (elements s))).
  destruct (InA_alt E.eq x (elements s)).
  split; intros.
  destruct (H1 (elements_1 H3)) as (y, (H4,H5)).
  apply H0; exists y; split; auto.
  rewrite <- In_rev; auto.
  destruct (H H3) as (y,(H4,H5)).
  apply elements_2.
  apply H2; exists y; split; auto.
  rewrite In_rev; auto.
  rewrite fold_left_rev_right.
  apply fold_1.
  Qed.

  Lemma cardinal_0 :
    forall s, exists l : list elt,
        noredunA E.eq l /\
        (forall x : elt, In x s <-> InA E.eq x l) /\ cardinal s = length l.
  Proof. 
  intros; exists (rev (elements s)).
  split.
  apply noredunA_rev; eauto.
  split.
  intros.
  destruct (InA_alt E.eq x (rev (elements s))).
  destruct (InA_alt E.eq x (elements s)).
  split; intros.
  destruct (H1 (elements_1 H3)) as (y, (H4,H5)).
  apply H0; exists y; split; auto.
  rewrite <- In_rev; auto.
  destruct (H H3) as (y,(H4,H5)).
  apply elements_2.
  apply H2; exists y; split; auto.
  rewrite In_rev; auto.
  rewrite cardinal_1.
  symmetry; apply rev_length.
  Qed.

  (** An alternate (and previous) specification for [fold] was based on 
      the recursive structure of a set. It is now lemmas [fold_1] and 
      [fold_2]. *)

  Definition Add (x : elt) (s s' : t) :=
    forall y : elt, In y s' <-> E.eq y x \/ In y s.

  Lemma fold_1 :
   forall (s : t) (A : Set) (eqA : A -> A -> Prop) 
     (st : Setoid_Theory A eqA) (i : A) (f : elt -> A -> A),
   Empty s -> eqA (fold f s i) i.
  Proof.
  intros; elim (fold_0 s i f); intros l (H1, (H2, H3)).
  rewrite H3; clear H3.
  unfold Empty in H; generalize H H2; clear H H2; case l; simpl in |- *;
   intros.
  apply Seq_refl; trivial.
  elim (H e).
  elim (H2 e); intuition. 
  Qed.

  Lemma fold_2 :
   forall (s s' : t) (x : elt) (A : Set) (eqA : A -> A -> Prop)
     (st : Setoid_Theory A eqA) (i : A) (f : elt -> A -> A),
   compat_op E.eq eqA f ->
   transpose eqA f ->
   ~ In x s -> Add x s s' -> eqA (fold f s' i) (f x (fold f s i)).
  Proof.
  intros; elim (fold_0 s i f); intros l (Hl, (Hl1, Hl2)).
  elim (fold_0 s' i f); intros l' (Hl', (Hl'1, Hl'2)).
  rewrite Hl2; clear Hl2.
  rewrite Hl'2; clear Hl'2.
  assert (forall y : elt, ME.In y l' <-> E.eq y x \/ ME.In y l).
   intros; elim (H2 y); intros; split; elim (Hl1 y); intros; elim (Hl'1 y);
    intuition.
  assert (~ ME.In x l).
   intro; elim H1; firstorder.
  clear H1 H2 Hl'1 Hl1 H1 s' s.
  apply fold_right_add with (eqA := eqA); auto.
  Qed.

  (** Similar specification for [cardinal]. *)

  Lemma cardinal_fold : forall s : t, cardinal s = fold (fun _ => S) s 0.
  Proof.
  intros; elim (cardinal_0 s); intros l (Hl, (Hl1, Hl2)).
  elim (fold_0 s 0 (fun _ => S)); intros l' (Hl', (Hl'1, Hl'2)).
  rewrite Hl2; rewrite Hl'2; clear Hl2 Hl'2.
  assert (forall l : list elt, length l = fold_right (fun _ => S) 0 l).
   simple induction l0; simpl in |- *; auto.
  rewrite H.
  apply fold_right_equal with (eqA := eq (A:=nat)); auto; firstorder.
  Qed.

  Lemma cardinal_1 : forall s : t, Empty s -> cardinal s = 0.
  Proof.
  intros; rewrite cardinal_fold; apply fold_1; auto.
  Qed.

  Lemma cardinal_2 :
   forall (s s' : t) (x : elt), ~ In x s -> Add x s s' -> cardinal s' = S (cardinal s).
  Proof.
  intros; do 2 rewrite cardinal_fold.
  change S with ((fun _ => S) x) in |- *.
  apply fold_2 with (eqA := eq (A:=nat)); auto.
  Qed.

  Hint Resolve cardinal_1 cardinal_2.

  End Old_Spec_Now_Properties.


  (** * Induction principle over sets *)

  Lemma Add_add : forall (s : t) (x : elt), Add x s (add x s).
  Proof.
    unfold Add in |- *; intros; intuition.
    elim (ME.eq_dec x y); intros; auto.
    right.
    eapply add_3; eauto.
  Qed.

  Lemma Add_remove : forall (s : t) (x : elt), In x s -> Add x (remove x s) s. 
  Proof. 
    intros; unfold Add in |- *; intuition.
    elim (ME.eq_dec x y); intros; auto.
    apply In_1 with x; auto.
    eauto.
  Qed.
 
  Hint Resolve Add_add Add_remove. 

  Lemma Equal_remove :
   forall (s s' : t) (x : elt), In x s -> Equal s s' -> Equal (remove x s) (remove x s').
  Proof.
     unfold Equal in |- *; intros.
     elim (ME.eq_dec x a); intros; auto. 
     split; intros.
     absurd (In x (remove x s)); auto; apply In_1 with a; auto.
     absurd (In x (remove x s')); auto; apply In_1 with a; auto. 
     elim (H0 a); intros. 
     split; intros; apply remove_2; auto; [ apply H1 | apply H2 ];
      eapply remove_3; eauto.    
  Qed.

  Hint Resolve Equal_remove.

  Lemma cardinal_inv_1 : forall s : t, cardinal s = 0 -> Empty s. 
  Proof. 
    intros; generalize (choose_1 (s:=s)) (choose_2 (s:=s)).
    elim (choose s); intuition.
    clear H1; assert (In a s); auto.
    rewrite (cardinal_2 (s:=remove a s) (s':=s) (x:=a)) in H; auto.
    inversion H.
  Qed.
  Hint Resolve cardinal_inv_1.
 
  Lemma cardinal_inv_2 :
   forall (s : t) (n : nat), cardinal s = S n -> exists x : elt, In x s.
  Proof. 
    intros; generalize (choose_1 (s:=s)) (choose_2 (s:=s)).
    elim (choose s); intuition. 
    exists a; auto.
    intros; rewrite cardinal_1 in H; auto; inversion H.
  Qed.

  Lemma Equal_cardinal_aux :
   forall (n : nat) (s s' : t), cardinal s = n -> Equal s s' -> cardinal s = cardinal s'.
  Proof.
     simple induction n.
     intros.  
     rewrite H.
     symmetry  in |- *.
     apply cardinal_1.
     generalize (cardinal_inv_1 H) H0.
     unfold Empty, Equal in |- *; intuition.
     generalize (H1 a) (H2 a); intuition.
     intros.
     elim (cardinal_inv_2 H0); intros.
     assert (In x s'). 
       generalize (H1 x); intuition.  
     generalize H0.
     rewrite (cardinal_2 (s:=remove x s) (s':=s) (x:=x)); auto.
     rewrite (cardinal_2 (s:=remove x s') (s':=s') (x:=x)); auto.
  Qed.

  Lemma Equal_cardinal : forall s s' : t, Equal s s' -> cardinal s = cardinal s'.
  Proof. 
    intros; eapply Equal_cardinal_aux; eauto.
  Qed.

  Hint Resolve Add_add Add_remove Equal_remove cardinal_inv_1 Equal_cardinal.

  Lemma empty_cardinal : cardinal empty = 0.
  Proof.
  rewrite cardinal_fold; auto.
  apply fold_1; auto.
  Qed.

  Lemma empty_cardinal_2 : forall s : t, Empty s -> cardinal s = 0.
  Proof.
  intros; replace 0 with (cardinal empty). 
  apply Equal_cardinal. 
  unfold Empty in H; unfold Equal in |- *; firstorder.
  absurd (In a empty); auto.
  apply empty_cardinal.
  Qed.

  Hint Immediate empty_cardinal empty_cardinal_2: set.

  Lemma cardinal_induction :
   forall P : t -> Prop,
   (forall s : t, Empty s -> P s) ->
   (forall s s' : t, P s -> forall x : elt, ~In x s -> Add x s s' -> P s') ->
   forall (n : nat) (s : t), cardinal s = n -> P s.
  Proof.
  simple induction n.
  intros; apply H; auto.
  intros; elim (cardinal_inv_2 H2); intros. 
  apply H0 with (remove x s) x; auto.
  apply H1; auto.
  assert (S (cardinal (remove x s)) = S n0); auto. 
  rewrite <- H2; symmetry  in |- *.
  eapply cardinal_2; eauto.
  Qed.

  Lemma set_induction :
   forall P : t -> Prop,
   (forall s : t, Empty s -> P s) ->
   (forall s s' : t, P s -> forall x : elt, ~In x s -> Add x s s' -> P s') ->
   forall s : t, P s.
  Proof.
  intros; eapply cardinal_induction; eauto.
  Qed.  

  (** Other formulation of [fold_1] and [fold_2]. *)

  Section Fold. 

  Variable s s' : t.
  Variable x : elt.

  Variable A : Set. 
  Variable eqA : A -> A -> Prop.
  Variable st : Setoid_Theory _ eqA.
  Variable i : A.
  Variable f : elt -> A -> A.
  Variable Comp : compat_op E.eq eqA f. 
  Variable Assoc : transpose eqA f.
 
  Lemma fold_empty : eqA (fold f empty i) i.
  Proof. 
  apply fold_1; auto.
  Qed.

  Lemma fold_equal : Equal s s' -> eqA (fold f s i) (fold f s' i).
  Proof. 
     pattern s in |- *; apply set_induction; intros.
     apply (Seq_trans _ _ st) with i; auto.
     apply fold_1; auto.
     apply Seq_sym; auto; apply fold_1; auto.
     apply cardinal_inv_1; rewrite <- (Equal_cardinal H0); auto with set.
     apply (Seq_trans _ _ st) with (f x0 (fold f s0 i)); auto.
     apply fold_2 with (eqA := eqA); auto.
     apply Seq_sym; auto; apply fold_2 with (eqA := eqA); auto.
     generalize H2 H1; unfold Add, Equal in |- *; intros; elim (H4 y);
      elim (H3 y); intuition.
  Qed.
   
  Lemma fold_add : ~In x s -> eqA (fold f (add x s) i) (f x (fold f s i)).
  Proof. 
    intros; apply fold_2 with (eqA := eqA); auto.
  Qed.

  End Fold.

  (** properties of [Equal] *)

  Lemma equal_refl : forall s : t, Equal s s.
  Proof.
  unfold Equal in |- *; intuition.
  Qed.

  Lemma equal_sym : forall s s' : t, Equal s s' -> Equal s' s.
  Proof.
  unfold Equal in |- *; firstorder.
  Qed.

  Lemma equal_trans : forall s u v : t, Equal s u -> Equal u v -> Equal s v.
  Proof.
  firstorder. 
  Qed.

  Hint Resolve equal_refl equal_trans: set.
  Hint Immediate equal_sym: set.

  (** properties of [Subset] *)

  Lemma subset_refl : forall s : t, Subset s s. 
  Proof.
  unfold Subset in |- *; intuition.
  Qed.

  Lemma subset_antisym : forall s s' : t, Subset s s' -> Subset s' s -> Equal s s'.
  Proof.
  unfold Subset, Equal in |- *; intuition.
  Qed.

  Lemma subset_trans : forall s t_ u : t, Subset s t_ -> Subset t_ u -> Subset s u.
  Proof.
  unfold Subset in |- *; intuition.
  Qed.

  Lemma subset_equal : forall s s' : t, Equal s s' -> Subset s s'.
  Proof.
  unfold Subset, Equal in |- *; firstorder.
  Qed.

  Lemma subset_empty : forall s : t, Subset empty s.
  Proof.
  unfold Subset in |- *; intuition.
  absurd (In a empty); auto.
  Qed.

  Lemma subset_remove_3 :
   forall (s1 s2 : t) (x : elt), Subset s1 s2 -> Subset (remove x s1) s2.
  Proof.
  unfold Subset in |- *; intuition.
  apply (H a).
  apply remove_3 with x; auto.
  Qed.

  Lemma subset_diff : forall s1 s2 s3 : t, Subset s1 s3 -> Subset (diff s1 s2) s3.
  Proof.
  unfold Subset in |- *; intuition.
  apply (H a).
  apply diff_1 with s2; intuition.
  Qed.

  Lemma subset_add_3 :
   forall (s1 s2 : t) (x : elt), In x s2 -> Subset s1 s2 -> Subset (add x s1) s2.
  Proof.
  unfold Subset in |- *; intuition.
  case (ME.eq_dec x a); intuition.
  apply In_1 with x; auto.
  apply (H0 a).
  apply add_3 with x; auto.
  Qed.

  Lemma subset_add_2 : forall (s1 s2 : t) (x : elt), Subset s1 s2 -> Subset s1 (add x s2).
  Proof.
  unfold Subset in |- *; intuition.
  Qed.

  Lemma in_subset : forall (s1 s2 : t) (x : elt), In x s1 -> Subset s1 s2 -> In x s2.
  Proof.
  unfold Subset in |- *; intuition.
  Qed.

  Hint Resolve subset_refl subset_equal subset_antisym subset_trans
    subset_empty subset_remove_3 subset_diff subset_add_3 subset_add_2
    in_subset: set.

  (** properties of [empty] *)

  Lemma empty_is_empty_1 : forall s : t, Empty s -> Equal s empty.
  Proof.
  unfold Empty, Equal in |- *; firstorder.
  absurd (In a empty); auto.
  Qed.

  Lemma empty_is_empty_2 : forall s : t, Equal s empty -> Empty s.
  Proof.
  unfold Empty, Equal in |- *; firstorder.
  intro; absurd (In a empty); firstorder.
  Qed.

  Hint Resolve empty_is_empty_1 empty_is_empty_2: set.

  (** properties of [add] *)

  Ltac Add_ y x s :=
    generalize (add_1 s (x:=x) (y:=y)) (add_2 (s:=s) x (y:=y))
     (add_3 (s:=s) (x:=x) (y:=y)).

  Lemma add_equal : forall (s : t) (x : elt), In x s -> Equal (add x s) s.
  Proof.
  unfold Equal in |- *; intuition.
  elim (ME.eq_dec x a); Add_ a x s; firstorder.
  eauto.
  Qed.

  Hint Resolve add_equal: set.

  (** properties of [remove] *)

  Ltac Remove_ a x s :=
    generalize (remove_1 (s:=s) (x:=x) (y:=a))
     (remove_2 (s:=s) (x:=x) (y:=a)) (remove_3 (s:=s) (x:=x) (y:=a)).

  Lemma remove_equal : forall (s : t) (x : elt), ~ In x s -> Equal (remove x s) s.
  Proof.
  unfold Equal in |- *; intuition.
  eauto.
  elim (ME.eq_dec x a); Remove_ a x s; firstorder.
  absurd (In x s); auto.
  apply In_1 with a; auto.
  Qed.

  Hint Resolve remove_equal: set.

  (** properties of [add] and [remove] *)

  Lemma add_remove :
   forall (s : t) (x : elt), In x s -> Equal (add x (remove x s)) s.
  Proof.
  unfold Equal in |- *; intuition.
  elim (ME.eq_dec x a); intuition.
  apply In_1 with x; auto.
  Add_ a x (remove x s); Remove_ a x s; firstorder.
  elim (ME.eq_dec x a); intuition.
  Qed.

  Lemma remove_add :
   forall (s : t) (x : elt), ~ In x s -> Equal (remove x (add x s)) s.
  Proof.
  unfold Equal in |- *; intuition.
  elim (ME.eq_dec x a); intuition.
  absurd (In a (remove x (add x s))); auto.
  Remove_ a x (add x s); Add_ a x s; firstorder.
  elim (ME.eq_dec x a); intuition.
  elim H; apply In_1 with a; auto.
  Qed.

  Hint Immediate add_remove remove_add: set.

  (** properties of [singleton] *)

  Ltac Singleton a x :=
    generalize (singleton_1 (x:=x) (y:=a)) (singleton_2 (x:=x) (y:=a)).

  Lemma singleton_equal_add : forall x : elt, Equal (singleton x) (add x empty).
  Proof.
  unfold Equal in |- *; intros; Singleton ipattern:a ipattern:x; intuition.
  apply H0; clear H H0.
  Add_ a x empty; intuition.
  elim (ME.eq_dec x a); intuition.
  absurd (In a empty); auto.
  Qed.

  Lemma singleton_cardinal : forall x : elt, cardinal (singleton x) = 1.
  Proof.
  intros.
  rewrite (Equal_cardinal (singleton_equal_add x)).
  replace 0 with (cardinal empty ); auto with set.
  apply cardinal_2 with x; auto with set.
  Qed.

  Hint Resolve singleton_equal_add singleton_cardinal: set.

  (** properties of [union] *)

  Ltac union a s s' :=
    generalize (union_1 (s:=s) (s':=s') (x:=a)) (union_2 (s:=s) s' (x:=a))
     (union_3 s (s':=s') (x:=a)).

  Lemma union_sym : forall s s' : t, Equal (union s s') (union s' s).
  Proof.
  unfold Equal in |- *; intuition; union ipattern:a ipattern:s ipattern:s';
   union ipattern:a ipattern:s' ipattern:s; intuition.
  Qed.

  Lemma union_subset_equal : forall s s' : t, Subset s s' -> Equal (union s s') s'.
  Proof.
  unfold Subset, Equal in |- *; intuition;
   union ipattern:a ipattern:s ipattern:s'; intuition.
  Qed.

  Lemma union_equal_1 : forall s s' s'' : t, Equal s s' ->  Equal (union s s'') (union s' s'').
  Proof.
  unfold Equal in |- *; intuition; union ipattern:a ipattern:s ipattern:s'';
   union ipattern:a ipattern:s' ipattern:s''; firstorder.
  Qed.

  Lemma union_equal_2 : forall s s' s'' : t, Equal s' s'' -> Equal (union s s') (union s s'').
  Proof.
  unfold Equal in |- *; intuition; union ipattern:a ipattern:s ipattern:s';
   union ipattern:a ipattern:s ipattern:s''; firstorder.
  Qed.

  Lemma union_assoc :
   forall s s' s'' : t, Equal (union (union s s') s'') (union s (union s' s'')).
  Proof.
  unfold Equal in |- *; intuition; union ipattern:a (union s s') ipattern:s'';
   union ipattern:a ipattern:s ipattern:s';
   union ipattern:a ipattern:s (union s' s'');
   union ipattern:a ipattern:s' ipattern:s''; firstorder.
  Qed.

  Hint Resolve union_subset_equal union_equal_1 union_equal_2 union_assoc:
    set.
  Hint Immediate union_sym.

  Lemma add_union_singleton :
   forall (s : t) (x : elt), Equal (add x s) (union (singleton x) s).
  Proof.
  unfold Equal in |- *; intuition; Add_ ipattern:a ipattern:x ipattern:s;
   Singleton ipattern:a ipattern:x; firstorder.
  elim (ME.eq_dec x a); firstorder.
  union a (singleton x) s; firstorder.
  Qed.

  Lemma union_add :
   forall (s s' : t) (x : elt), Equal (union (add x s) s') (add x (union s s')).
  Proof.
  unfold Equal in |- *; intuition.
  union a (add x s) s'; intuition.
  generalize (Add_add s x); unfold Add in |- *; firstorder.
  generalize (Add_add (union s s') x); unfold Add in |- *; firstorder.
  generalize (H0 a); clear H0; firstorder.
  union a s s'; intuition.
  Qed.

  Lemma union_subset_1 : forall s s' : t, Subset s (union s s').
  Proof.
  unfold Subset in |- *; intuition.
  Qed.

  Lemma union_subset_2 : forall s s' : t, Subset s' (union s s').
  Proof.
  unfold Subset in |- *; intuition.
  Qed.

  Lemma subset_union :
   forall s s' s'' : t, Subset s s'' -> Subset s' s'' ->  Subset (union s s') s''.
  Proof.
  unfold Subset in |- *; intuition.
  union a s s'; intuition.
  Qed.

  Hint Resolve add_union_singleton union_add union_subset_1 union_subset_2
    subset_union: set.

  (** properties of [inter] *)

  Ltac Inter a s s' :=
    generalize (inter_1 (s:=s) (s':=s') (x:=a))
     (inter_2 (s:=s) (s':=s') (x:=a)) (inter_3 (s:=s) (s':=s') (x:=a)).

  Lemma inter_sym : forall s s' : t, Equal (inter s s') (inter s' s).
  Proof.
  unfold Equal in |- *; intros s s' a.
  Inter a s s'; Inter a s' s; intuition.
  Qed.

  Lemma inter_subset_equal : forall s s' : t, Subset s s' -> Equal (inter s s') s.
  Proof.
  unfold Equal in |- *; intros.
  Inter a s s'; intuition.
  Qed.

  Lemma inter_equal_1 : forall s s' s'' : t, Equal s s' -> Equal (inter s s'') (inter s' s'').
  Proof.
  unfold Equal in |- *; intuition.
  Inter a s s''; firstorder.
  Inter a s' s''; firstorder.
  Qed.

  Lemma inter_equal_2 : forall s s' s'' : t, Equal s' s'' -> Equal (inter s s') (inter s s'').
  Proof.
  unfold Equal in |- *; intuition.
  Inter a s s'; firstorder.
  Inter a s s''; firstorder.
  Qed.

  Hint Immediate inter_sym: set.
  Hint Resolve inter_subset_equal inter_equal_1 inter_equal_2: set.

  Lemma inter_assoc :
   forall s s' s'' : t, Equal (inter (inter s s') s'') (inter s (inter s' s'')).
  Proof.
  unfold Equal in |- *; intuition.
  Inter a (inter s s') s''; Inter a s s'; firstorder.
  Inter a s (inter s' s''); Inter a s' s''; firstorder.
  Qed.

  Lemma union_inter_1 :
   forall s s' s'' : t, Equal (inter (union s s') s'') (union (inter s s'') (inter s' s'')).
  Proof.
  unfold Equal in |- *; intuition.
  Inter a (union s s') s''; union a s s'; firstorder.
  union a (inter s s'') (inter s' s''); Inter a s s''; Inter a s' s''; firstorder.
  Qed.

  Lemma union_inter_2 :
   forall s s' s'' : t, Equal (union (inter s s') s'') (inter (union s s'') (union s' s'')).
  Proof.
  unfold Equal in |- *; intuition.
  union a (inter s s') s''; Inter a s s'; firstorder.
  Inter a (union s s'') (union s' s''); union a s s''; union a s' s''; firstorder.
  Qed.

  Lemma inter_add_1 :
   forall (s s' : t) (x : elt), In x s' -> Equal (inter (add x s) s') (add x (inter s s')).
  Proof.
  unfold Equal in |- *; intuition.
  Inter a (add x s) s'; Add_ a x s; firstorder.
  elim (ME.eq_dec x a); auto.
  generalize (Add_add (inter s s') x); unfold Add in |- *; firstorder.
  generalize (H1 a); clear H1; intuition.
  apply inter_3; auto.
  apply In_1 with x; auto.
  apply inter_3; auto.
  apply add_2; auto.
  Inter a s s'; intuition.
  Inter a s s'; intuition.
  Qed.

  Lemma inter_add_2 :
   forall (s s' : t) (x : elt), ~ In x s' -> Equal (inter (add x s) s') (inter s s').
  Proof.
  unfold Equal in |- *; intuition.
  Inter a (add x s) s'; Add_ a x s; firstorder.
  elim (ME.eq_dec x a); intuition.
  absurd (In x s'); auto.
  apply In_1 with a; auto.
  Inter a s s'; intuition.
  Qed.

  Hint Resolve inter_assoc union_inter_1 union_inter_2 inter_add_1
    inter_add_2: set.

  (** properties of [Subset] *)

  Lemma inter_subset_1 : forall s s' : t, Subset (inter s s') s.
  Proof.
  unfold Subset in |- *; intuition.
  Inter a s s'; intuition.
  Qed.

  Lemma inter_subset_2 : forall s s' : t, Subset (inter s s') s'.
  Proof.
  unfold Subset in |- *; intros; Inter ipattern:a ipattern:s ipattern:s';
   intuition.
  Qed.

  Lemma inter_subset_3 :
   forall s s' s'' : t, Subset s'' s -> Subset s'' s' -> Subset s'' (inter s s').
  Proof.
  unfold Subset in |- *; intuition.
  Qed.

  Hint Resolve inter_subset_1 inter_subset_2 inter_subset_3: set.

  (** Properties of [diff] *)

  Ltac Diff a s s' :=
    generalize (diff_1 (s:=s) (s':=s') (x:=a))
     (diff_2 (s:=s) (s':=s') (x:=a)) (diff_3 (s:=s) (s':=s') (x:=a)).

  Lemma diff_subset : forall s s' : t, Subset (diff s s') s.
  Proof.
  unfold Subset in |- *; intuition.
  Diff a s s'; intuition.
  Qed.

  Lemma diff_subset_equal : forall s s' : t, Subset s s' -> Equal (diff s s') empty.
  Proof.
  unfold Subset, Equal in |- *; intuition.
  Diff a s s'; firstorder.
  absurd (In a empty); auto.
  Qed.

  Lemma remove_inter_singleton :
   forall (s : t) (x : elt), Equal (remove x s) (diff s (singleton x)).
  Proof.
  unfold Equal in |- *; intuition.
  Remove_ a x s; intuition.
  elim (ME.eq_dec x a); intuition.
  Diff a s (singleton x); intuition.
  Qed.

  Lemma diff_inter_empty : forall s s' : t, Equal (inter (diff s s') (inter s s')) empty. 
  Proof.
  unfold Equal in |- *; intuition.
  Inter a (diff s s') (inter s s'); intuition.
  Inter a s s'; Diff a s s'; intuition.
  absurd (In a empty); auto.
  Qed.

  (* TOMOVE *)
  Lemma In_dec : forall (x : elt) (s : t), {In x s} + {~ In x s}.
  Proof.
  intros x s; generalize (mem_1 (s:=s) (x:=x)) (mem_2 (s:=s) (x:=x));
   case (mem x s); intuition.
  Qed.

  Lemma diff_inter_all : forall s s' : t, Equal (union (diff s s') (inter s s')) s.
  Proof.
  unfold Equal in |- *; intuition.
  union a (diff s s') (inter s s'); intuition.
  Diff a s s'; intuition.
  Inter a s s'; intuition.
  elim (In_dec a s'); auto.
  Qed.

  Hint Resolve diff_subset diff_subset_equal remove_inter_singleton
    diff_inter_empty diff_inter_all: set.

  Lemma fold_plus :
   forall (s : t) (p : nat),
   fold (fun _ => S) s p = fold (fun _ => S) s 0 + p.
  Proof.
  assert (st := gen_st nat).
  assert (fe : compat_op E.eq (eq (A:=_)) (fun _ : elt => S)). unfold compat_op in |- *; auto. 
  assert (fp : transpose (eq (A:=_)) (fun _ : elt => S)). unfold transpose in |- *; auto.
  intros s p; pattern s in |- *; apply set_induction.
  intros; rewrite (fold_1 st p (fun _ : elt => S) H).
  rewrite (fold_1 st 0 (fun _ : elt => S) H); trivial.
  intros.
  assert
   (forall (p : nat) (s1 : t),
    Add x s0 s1 -> fold (fun _ => S) s1 p = S (fold (fun _ => S) s0 p)).
  change S with ((fun _ => S) x) in |- *. 
  intros; apply fold_2 with (eqA := eq (A:=nat)); auto.
  rewrite (H2 p); auto.
  rewrite (H2 0); auto.
  rewrite H.
  simpl in |- *; auto.
  Qed.

  (** properties of [cardinal] *)

  Lemma empty_inter_1 : forall s s' : t, Empty s -> Empty (inter s s').
  Proof.
  unfold Empty in |- *; intuition; Inter ipattern:a ipattern:s ipattern:s';
   firstorder.
  Qed.

  Lemma empty_inter_2 : forall s s' : t, Empty s' -> Empty (inter s s').
  Proof.
  unfold Empty in |- *; intuition; Inter ipattern:a ipattern:s ipattern:s';
   firstorder.
  Qed.

  Lemma empty_union_1 : forall s s' : t, Empty s -> Equal (union s s') s'.
  Proof.
  unfold Equal, Empty in |- *; intuition;
   union ipattern:a ipattern:s ipattern:s'; firstorder.
  Qed.

  Lemma empty_union_2 : forall s s' : t, Empty s -> Equal (union s' s) s'.
  Proof.
  unfold Equal, Empty in |- *; intuition;
   union ipattern:a ipattern:s' ipattern:s; firstorder.
  Qed.

  Lemma empty_diff_1 : forall s s' : t, Empty s -> Empty (diff s s'). 
  Proof.
  unfold Empty, Equal in |- *; intuition;
   Diff ipattern:a ipattern:s ipattern:s'; firstorder.
  Qed.

  Lemma empty_diff_2 : forall s s' : t, Empty s -> Equal (diff s' s) s'.
  Proof.
  unfold Empty, Equal in |- *; intuition;
   Diff ipattern:a ipattern:s' ipattern:s; firstorder.
  Qed.

  Hint Resolve empty_inter_1 empty_inter_2 empty_union_1 empty_union_2
    empty_diff_1 empty_diff_2: set.

  Lemma union_Add :
   forall (s s' s'' : t) (x : elt), Add x s s' -> Add x (union s s'') (union s' s'').
  Proof. 
  unfold Add in |- *; intuition. 
  union y s' s''; firstorder.   
  union y s' s''; firstorder. 
  union y s s''; firstorder. 
  Qed.

  Lemma inter_Add :
   forall (s s' s'' : t) (x : elt),
   In x s'' -> Add x s s' -> Add x (inter s s'') (inter s' s'').
  Proof. 
  unfold Add in |- *; intuition. 
  Inter y s' s''; firstorder.   
  Inter y s' s''; firstorder. 
  apply H4; auto. 
  elim (H0 y); intuition.
  apply In_1 with x; auto. 
  Inter y s s''; firstorder. 
  Qed.  

  Lemma union_Equal :
   forall (s s' s'' : t) (x : elt),
   In x s'' -> Add x s s' -> Equal (union s s'') (union s' s'').
  Proof. 
  unfold Add, Equal in |- *; intuition. 
  union a s s''; firstorder. 
  union a s' s''; firstorder. 
  elim (H0 a); intuition. 
  union a s s''; firstorder. 
  apply H10; apply In_1 with x; auto. 
  Qed.  

  Lemma inter_Add_2 :
   forall (s s' s'' : t) (x : elt),
   ~In x s'' -> Add x s s' -> Equal (inter s s'') (inter s' s'').
  Proof.
  unfold Add, Equal in |- *; intuition. 
  Inter a s s''; firstorder. 
  elim (H0 a); clear H0; Inter a s' s''; firstorder. 
  absurd (In x s''); auto. 
  apply In_1 with a; auto. 
  Qed.

  Lemma not_in_union :
   forall (x : elt) (s s' : t), ~In x s -> ~In x s' -> ~In x (union s s'). 
  Proof.
  intuition. 
  union x s s'; firstorder. 
  Qed.  

  Hint Resolve union_Add inter_Add union_Equal inter_Add_2 not_in_union: set. 

  Lemma fold_commutes :
   forall (A : Set) (f : elt -> A -> A) (i : A),
   compat_op E.eq (eq (A:=_)) f ->
   transpose (eq (A:=_)) f ->
   forall (s : t) (x : elt), fold f s (f x i) = f x (fold f s i).
  Proof.
  intro A.
  set (st := gen_st A) in *.
  intros; pattern s in |- *; apply set_induction.
  intros.
  rewrite (fold_1 st i f H1).
  rewrite (fold_1 st (f x i) f H1).
  apply H; auto. 
  intros. 
  apply (Seq_trans _ _ st) with (f x0 (fold f s0 (f x i))).
  rewrite (fold_2 st (f x i) H H0 H2 H3).
  apply (Seq_trans _ _ st) with (f x0 (f x (fold f s0 i))).
  apply H; auto.
  rewrite H1; auto. 
  rewrite (fold_2 st i H H0 H2 H3).
  rewrite H1; auto. 
  Qed.

  Lemma fold_union_inter :
   forall (A : Set) (f : elt -> A -> A) (i : A),
   compat_op E.eq (eq (A:=_)) f ->
   transpose (eq (A:=_)) f ->
   forall s s' : t,
   fold f (union s s') (fold f (inter s s') i) = fold f s (fold f s' i).
  Proof.
  intro A.
  set (st := gen_st A) in *.
  intros; pattern s in |- *; apply set_induction.
  intros; rewrite (fold_1 st (fold f s' i) f H1).
  assert (H2 : Empty (inter s0 s')). auto with set.
  rewrite (fold_1 st i f H2).
  assert (H3 : Equal (union s0 s') s'). auto with set.
  rewrite (fold_equal st i H H0 H3); auto.
  intros.
  assert (H4 : Add x (union s0 s') (union s'0 s')). 
  auto with set. 
  case (In_dec x s'); intro.
  (* In x s' *)
  assert (Add x (inter s0 s') (inter s'0 s')).
  auto with set.
  assert (~In x (inter s0 s')).
  Inter x s0 s'; intuition.
  rewrite (fold_2 st i H H0 H6 H5).
  rewrite (fold_2 st (fold f s' i) H H0 H2 H3).
  assert (Equal (union s'0 s') (union s0 s')).
  apply equal_sym; eauto with set. 
  rewrite (fold_equal st (f x (fold f (inter s0 s') i)) H H0 H7).
  rewrite fold_commutes; auto.
  (* ~(In x s') *)
  rewrite (fold_2 st (fold f s' i) H H0 H2 H3).
  assert (Equal (inter s'0 s') (inter s0 s')). 
  apply equal_sym; eauto with set. 
  rewrite (fold_equal st i H H0 H5).
  assert (Add x (union s0 s') (union s'0 s')). 
  auto with set. 
  assert (~In x (union s0 s')). 
  auto with set. 
  rewrite (fold_2 st (fold f (inter s0 s') i) H H0 H7 H6).
  auto. 
  Qed.

  Lemma fold_diff_inter :
   forall (A : Set) (f : elt -> A -> A) (i : A),
   compat_op E.eq (eq (A:=A)) f ->
   transpose (eq (A:=A)) f ->
   forall s s' : t, fold f (diff s s') (fold f (inter s s') i) = fold f s i.
  Proof.
  intros.
  assert (st := gen_st A).
  rewrite <- (fold_union_inter i H H0 (diff s s') (inter s s')).
  rewrite (fold_equal st i H H0 (diff_inter_empty s s')).
  rewrite (fold_empty st).
  apply fold_equal with (eqA := eq (A:=A)); auto.
  apply diff_inter_all.
  Qed.

  Lemma diff_inter_cardinal :
   forall s s' : t, cardinal (diff s s')  + cardinal (inter s s') = cardinal s .
  Proof.
  intro s; pattern s in |- *; apply set_induction; intuition.
  assert (Empty (diff s0 s')); auto with set.  
  rewrite (empty_cardinal_2 H0). 
  assert (Empty (inter s0 s')); auto with set.  
  rewrite (empty_cardinal_2 H1).
  rewrite (empty_cardinal_2 H); auto. 
  intros.
  do 3 rewrite cardinal_fold.
  rewrite <- fold_plus.
  apply fold_diff_inter; auto.
  Qed.

  Lemma subset_cardinal : forall s s' : t, Subset s s' -> cardinal s <= cardinal s' .
  Proof.
  intros.
  rewrite <- (diff_inter_cardinal s' s).
  rewrite (Equal_cardinal (inter_sym s' s)).
  rewrite (Equal_cardinal (inter_subset_equal H)); auto with arith.
  Qed.

  Lemma union_inter_cardinal :
   forall s s' : t, cardinal (union s s') + cardinal (inter s s')  = cardinal s  + cardinal s' .
  Proof.
  intros.
  do 4 rewrite cardinal_fold.
  do 2 rewrite <- fold_plus.
  apply fold_union_inter; auto.
  Qed.

  Lemma union_cardinal : forall s s' : t, cardinal (union s s') <= cardinal s  + cardinal s' .
  Proof.
    intros; generalize (union_inter_cardinal s s'); intros; omega.
  Qed.

  Lemma add_cardinal_1 : forall (s : t) (x : elt), In x s -> cardinal (add x s) = cardinal s .
  Proof.
  auto with set.  
  Qed.

  Lemma add_cardinal_2 :
   forall (s : t) (x : elt), ~In x s -> cardinal (add x s)  = S (cardinal s).
  Proof.
  intros.
  do 2 rewrite cardinal_fold.
  change S with ((fun _ => S) x) in |- *;
   apply fold_add with (eqA := eq (A:=nat)); auto.
  Qed.

  Hint Resolve subset_cardinal union_cardinal add_cardinal_1 add_cardinal_2.

End Properties.
