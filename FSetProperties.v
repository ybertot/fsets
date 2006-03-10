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

Require Export FSetInterface. 
Require Import FSetFacts.
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

Hint Extern 1 (Setoid_Theory _ _) => constructor; congruence.

Definition gen_st : forall A : Set, Setoid_Theory _ (eq (A:=A)).
Proof. auto. Qed.

Module Properties (M: S).
  Module ME := OrderedTypeFacts M.E.  
  Import ME.
  Import M.
  Import Logic. (* to unmask [eq] *)  
  Import Peano. (* to unmask [lt] *)
  
   (** Results about lists without duplicates *)

  Module FM := Facts M.
  Import FM.

  Definition Add (x : elt) (s s' : t) :=
    forall y : elt, In y s' <-> E.eq x y \/ In y s.

  Lemma In_dec : forall x s, {In x s} + {~ In x s}.
  Proof.
  intros; generalize (mem_iff s x); case (mem x s); intuition.
  Qed.

  Section BasicProperties.
  Variable s s' s'' s1 s2 s3 : t.
  Variable x : elt.

  (** properties of [Equal] *)

  Lemma equal_refl : s[=]s.
  Proof.
  apply eq_refl.
  Qed.

  Lemma equal_sym : s[=]s' -> s'[=]s.
  Proof.
  apply eq_sym. 
  Qed.

  Lemma equal_trans : s1[=]s2 -> s2[=]s3 -> s1[=]s3.
  Proof.
  intros; apply eq_trans with s2; auto.
  Qed.

  (** properties of [Subset] *)
  
  Lemma subset_refl : s[<=]s. 
  Proof.
  unfold Subset; intuition.
  Qed.

  Lemma subset_antisym : s[<=]s' -> s'[<=]s -> s[=]s'.
  Proof.
  unfold Subset, Equal; intuition.
  Qed.

  Lemma subset_trans : s1[<=]s2 -> s2[<=]s3 -> s1[<=]s3.
  Proof.
  unfold Subset; intuition.
  Qed.

  Lemma subset_equal : s[=]s' -> s[<=]s'.
  Proof.
  unfold Subset, Equal; firstorder.
  Qed.

  Lemma subset_empty : empty[<=]s.
  Proof.
  unfold Subset; intuition.
  absurd (In a empty); auto.
  Qed.

  Lemma subset_remove_3 : s1[<=]s2 -> remove x s1 [<=] s2.
  Proof.
  unfold Subset; intros H a; set_iff; intuition.
  Qed.

  Lemma subset_diff : s1[<=]s3 -> diff s1 s2 [<=] s3.
  Proof.
  unfold Subset; intros H a; set_iff; intuition.
  Qed.

  Lemma subset_add_3 : In x s2 -> s1[<=]s2 -> add x s1 [<=] s2.
  Proof.
  unfold Subset; intros H H0 a; set_iff; intuition.
  rewrite <- H2; auto.
  Qed.

  Lemma subset_add_2 : s1[<=]s2 -> s1[<=] add x s2.
  Proof.
  unfold Subset; intuition.
  Qed.

  Lemma in_subset : In x s1 -> s1[<=]s2 -> In x s2.
  Proof.
  unfold Subset; intuition.
  Qed.

  (** properties of [empty] *)

  Lemma empty_is_empty_1 : Empty s -> s[=]empty.
  Proof.
  unfold Empty, Equal; firstorder.
  absurd (In a empty); auto.
  Qed.

  Lemma empty_is_empty_2 : s[=]empty -> Empty s.
  Proof.
  unfold Empty, Equal; firstorder.
  intro; absurd (In a empty); firstorder.
  Qed.

  (** properties of [add] *)

  Lemma add_equal : In x s -> add x s [=] s.
  Proof.
  unfold Equal; intros; set_iff; intuition.
  rewrite <- H1; auto.
  Qed.

  (** properties of [remove] *)

  Lemma remove_equal : ~ In x s -> remove x s [=] s.
  Proof.
  unfold Equal; intros; set_iff; intuition.
  rewrite H1 in H; auto.
  Qed.

  Lemma Equal_remove : s[=]s' -> remove x s [=] remove x s'.
  Proof.
    intros; rewrite H; apply eq_refl.
  Qed.

  (** properties of [add] and [remove] *)

  Lemma add_remove : In x s -> add x (remove x s) [=] s.
  Proof.
  unfold Equal; intros; set_iff; elim (eq_dec x a); intuition.
  rewrite <- H1; auto.
  Qed.

  Lemma remove_add : ~ In x s -> remove x (add x s) [=] s.
  Proof.
  unfold Equal; intros; set_iff; elim (eq_dec x a); intuition.
  rewrite H1 in H; auto.
  Qed.

  (** properties of [singleton] *)

  Lemma singleton_equal_add : singleton x [=] add x empty.
  Proof.
  unfold Equal; intros; set_iff; intuition.
  absurd (In a empty); auto.
  Qed.

  (** properties of [union] *)

  Lemma union_sym : union s s' [=] union s' s.
  Proof.
  unfold Equal; intros; set_iff; tauto.
  Qed.

  Lemma union_subset_equal : s[<=]s' -> union s s' [=] s'.
  Proof.
  unfold Subset, Equal; intros; set_iff; intuition.
  Qed.

  Lemma union_equal_1 : s[=]s' -> union s s'' [=] union s' s''.
  Proof.
  intros; rewrite H; apply eq_refl.
  Qed.

  Lemma union_equal_2 : s'[=]s'' -> union s s' [=] union s s''.
  Proof.
  intros; rewrite H; apply eq_refl.
  Qed.

  Lemma union_assoc : union (union s s') s'' [=] union s (union s' s'').
  Proof.
  unfold Equal; intros; set_iff; tauto.
  Qed.

  Lemma add_union_singleton : add x s [=] union (singleton x) s.
  Proof.
  unfold Equal; intros; set_iff; tauto.
  Qed.

  Lemma union_add : union (add x s) s' [=] add x (union s s').
  Proof.
  unfold Equal; intros; set_iff; tauto.
  Qed.

  Lemma union_subset_1 : s [<=] union s s'.
  Proof.
  unfold Subset; intuition.
  Qed.

  Lemma union_subset_2 : s' [<=] union s s'.
  Proof.
  unfold Subset; intuition.
  Qed.

  Lemma subset_union : s[<=]s'' -> s'[<=]s'' -> union s s' [<=] s''.
  Proof.
  unfold Subset; intros H H0 a; set_iff; intuition.
  Qed.

  Lemma empty_union_1 : Empty s -> Equal (union s s') s'.
  Proof.
  unfold Equal, Empty; intros; set_iff; firstorder.
  Qed.

  Lemma empty_union_2 : Empty s -> union s' s [=] s'.
  Proof.
  unfold Equal, Empty; intros; set_iff; firstorder.
  Qed.

  Lemma not_in_union : ~In x s -> ~In x s' -> ~In x (union s s'). 
  Proof.
  intros; set_iff; intuition. 
  Qed.  

  (** properties of [inter] *)

  Lemma inter_sym : inter s s' [=] inter s' s.
  Proof.
  unfold Equal; intros; set_iff; tauto.
  Qed.

  Lemma inter_subset_equal : s[<=]s' -> inter s s' [=] s.
  Proof.
  unfold Equal; intros; set_iff; intuition.
  Qed.

  Lemma inter_equal_1 : s[=]s' -> inter s s'' [=] inter s' s''.
  Proof.
  intros; rewrite H; apply eq_refl.
  Qed.

  Lemma inter_equal_2 : s'[=]s'' -> inter s s' [=] inter s s''.
  Proof.
  intros; rewrite H; apply eq_refl.
  Qed.

  Lemma inter_assoc : inter (inter s s') s'' [=] inter s (inter s' s'').
  Proof.
  unfold Equal; intros; set_iff; tauto.
  Qed.

  Lemma union_inter_1 : inter (union s s') s'' [=] union (inter s s'') (inter s' s'').
  Proof.
  unfold Equal; intros; set_iff; tauto.
  Qed.

  Lemma union_inter_2 : union (inter s s') s'' [=] inter (union s s'') (union s' s'').
  Proof.
  unfold Equal; intros; set_iff; tauto.
  Qed.

  Lemma inter_add_1 : In x s' -> inter (add x s) s' [=] add x (inter s s').
  Proof.
  unfold Equal; intros; set_iff; intuition.
  rewrite <- H1; auto.
  Qed.

  Lemma inter_add_2 : ~ In x s' -> inter (add x s) s' [=] inter s s'.
  Proof.
  unfold Equal; intros; set_iff; intuition.
  destruct H; rewrite H0; auto.
  Qed.

  Lemma empty_inter_1 : Empty s -> Empty (inter s s').
  Proof.
  unfold Empty; intros; set_iff; firstorder.
  Qed.

  Lemma empty_inter_2 : Empty s' -> Empty (inter s s').
  Proof.
  unfold Empty; intros; set_iff; firstorder.
  Qed.

  Lemma inter_subset_1 : inter s s' [<=] s.
  Proof.
  unfold Subset; intro a; set_iff; tauto.
  Qed.

  Lemma inter_subset_2 : inter s s' [<=] s'.
  Proof.
  unfold Subset; intro a; set_iff; tauto.
  Qed.

  Lemma inter_subset_3 :
   s''[<=]s -> s''[<=]s' -> s''[<=] inter s s'.
  Proof.
  unfold Subset; intros H H' a; set_iff; intuition.
  Qed.

  (** properties of [diff] *)

  Lemma empty_diff_1 : Empty s -> Empty (diff s s'). 
  Proof.
  unfold Empty, Equal; intros; set_iff; firstorder.
  Qed.

  Lemma empty_diff_2 : Empty s -> diff s' s [=] s'.
  Proof.
  unfold Empty, Equal; intros; set_iff; firstorder.
  Qed.

  Lemma diff_subset : diff s s' [<=] s.
  Proof.
  unfold Subset; intros a; set_iff; tauto.
  Qed.

  Lemma diff_subset_equal : s[<=]s' -> diff s s' [=] empty.
  Proof.
  unfold Subset, Equal; intros; set_iff; intuition; absurd (In a empty); auto.
  Qed.

  Lemma remove_diff_singleton :
   remove x s [=] diff s (singleton x).
  Proof.
  unfold Equal; intros; set_iff; intuition.
  Qed.

  Lemma diff_inter_empty : inter (diff s s') (inter s s') [=] empty. 
  Proof.
  unfold Equal; intros; set_iff; intuition; absurd (In a empty); auto.
  Qed.

  Lemma diff_inter_all : union (diff s s') (inter s s') [=] s.
  Proof.
  unfold Equal; intros; set_iff; intuition.
  elim (In_dec a s'); auto.
  Qed.

  (** properties of [Add] *)

  Lemma Add_add : Add x s (add x s).
  Proof.
   unfold Add; intros; set_iff; intuition.
  Qed.

  Lemma Add_remove : In x s -> Add x (remove x s) s. 
  Proof. 
    unfold Add; intros; set_iff; intuition.
    elim (eq_dec x y); auto.
    rewrite <- H1; auto.
  Qed.

  Lemma union_Add : Add x s s' -> Add x (union s s'') (union s' s'').
  Proof. 
  unfold Add; intros; set_iff; rewrite H; tauto.
  Qed.

  Lemma inter_Add :
   In x s'' -> Add x s s' -> Add x (inter s s'') (inter s' s'').
  Proof. 
  unfold Add; intros; set_iff; rewrite H0; intuition.
  rewrite <- H2; auto.
  Qed.  

  Lemma union_Equal :
   In x s'' -> Add x s s' -> union s s'' [=] union s' s''.
  Proof. 
  unfold Add, Equal; intros; set_iff; rewrite H0; intuition. 
  rewrite <- H1; auto.
  Qed.  

  Lemma inter_Add_2 :
   ~In x s'' -> Add x s s' -> inter s s'' [=] inter s' s''.
  Proof.
  unfold Add, Equal; intros; set_iff; rewrite H0; intuition.
  destruct H; rewrite H1; auto.
  Qed.

  End BasicProperties.

  Hint Immediate equal_sym: set.
  Hint Resolve equal_refl equal_trans : set.

  Hint Immediate add_remove remove_add union_sym inter_sym: set.
  Hint Resolve subset_refl subset_equal subset_antisym 
    subset_trans subset_empty subset_remove_3 subset_diff subset_add_3 
    subset_add_2 in_subset empty_is_empty_1 empty_is_empty_2 add_equal
    remove_equal singleton_equal_add union_subset_equal union_equal_1 
    union_equal_2 union_assoc add_union_singleton union_add union_subset_1 
    union_subset_2 subset_union inter_subset_equal inter_equal_1 inter_equal_2
    inter_assoc union_inter_1 union_inter_2 inter_add_1 inter_add_2
    empty_inter_1 empty_inter_2 empty_union_1 empty_union_2 empty_diff_1 
    empty_diff_2 union_Add inter_Add union_Equal inter_Add_2 not_in_union 
    inter_subset_1 inter_subset_2 inter_subset_3 diff_subset diff_subset_equal 
    remove_diff_singleton diff_inter_empty diff_inter_all Add_add Add_remove
    Equal_remove : set.

  Notation NoRedun := (noredunA E.eq).

  Section noredunA_Remove.

  Definition remove_list x l := remove_such (eqb x) l.

  Lemma remove_list_correct :
    forall s x, NoRedun s -> 
    NoRedun (remove_list x s) /\
    (forall y : elt, ME.In y (remove_list x s) <-> ME.In y s /\ ~ E.eq x y).
  Proof.
   simple induction s; simpl; intros.
   repeat (split; trivial).
   inversion H0.
   destruct 1; inversion H0.
   inversion_clear H0; unfold eqb; destruct (eq_dec x a); trivial.  
   intuition.
   apply H1; apply In_eq with y; auto; order.
   inversion_clear H3; auto.
   destruct H4; order. 
   destruct (H x H2) as (H3,H4).
   split.
   constructor; trivial.
   rewrite H4; intuition.
   intro y; destruct (H4 y); clear H4.
   repeat split.
   inversion_clear H4; auto.
   elim (H0 H6); auto.
   inversion_clear H4; auto.
   order.
   destruct (H0 H6); auto.
   destruct 1.
   inversion_clear H4; auto.
  Qed. 

  Let ListEq l l' := forall y : elt, ME.In y l <-> ME.In y l'.

  Lemma remove_list_equal :
    forall s s' x, NoRedun (x :: s) -> NoRedun s' -> 
    ListEq (x :: s) s' -> ListEq s (remove_list x s').
  Proof.  
   unfold ListEq; intros. 
   inversion_clear H.
   destruct (remove_list_correct x H0).
   destruct (H4 y); clear H4.
   destruct (H1 y); clear H1.
   split; intros.
   apply H6; split; auto. 
   swap H2; apply In_eq with y; auto; order.
   destruct (H5 H1); intros.
   generalize (H7 H8); inversion_clear 1; auto.
   destruct H9; auto.
  Qed. 

  Let ListAdd x l l' := forall y : elt, ME.In y l' <-> E.eq x y \/ ME.In y l.

  Lemma remove_list_add :
    forall s s' x x', NoRedun s -> NoRedun (x' :: s') ->
    ~ E.eq x x' -> ~ ME.In x s -> 
    ListAdd x s (x' :: s') -> ListAdd x (remove_list x' s) s'.
  Proof.
   unfold ListAdd; intros.
   inversion_clear H0.
   destruct (remove_list_correct x' H).
   destruct (H6 y); clear H6.
   destruct (H3 y); clear H3.
   split; intros.
   destruct H6; auto.
   destruct (eq_dec x y); auto; intros.
   right; apply H8; split; auto.
   swap H4; apply In_eq with y; auto.
   destruct H3.
   assert (ME.In y (x' :: s')). auto.
   inversion_clear H10; auto.
   destruct H1; order.
   destruct (H7 H3).
   assert (ME.In y (x' :: s')). auto.
   inversion_clear H12; auto.
   destruct H11; auto. 
  Qed.

  Variable A : Set.
  Variable eqA : A -> A -> Prop.
  Variable st : Setoid_Theory A eqA.
  Variable i:A.
  Variable f: elt -> A -> A.
  Hypothesis Hf1 : compat_op E.eq eqA f.
  Hypothesis Hf2 : transpose eqA f.

  Lemma remove_list_fold_right :
    forall s x, NoRedun s -> ME.In x s ->
    eqA (fold_right f i s) (f x (fold_right f i (remove_list x s))).
  Proof.
   simple induction s; simpl.  
   inversion_clear 2.
   intros.
   inversion_clear H0.
   unfold eqb; destruct (eq_dec x a); simpl; intros.
   apply Hf1; auto. 
   apply Seq_refl; auto. 
   inversion_clear H1. 
   destruct n; auto.
   apply (Seq_trans _ _ st) with (f a (f x (fold_right f i (remove_list x l)))).
   apply Hf1; auto.
   apply Hf2; auto.
  Qed.   

  Lemma fold_right_equal :
    forall s s', NoRedun s -> NoRedun s' ->
    ListEq s s' -> eqA (fold_right f i s) (fold_right f i s').
  Proof.
   simple induction s.
   destruct s'; simpl.
   intros; apply Seq_refl; auto.
   unfold ListEq; intros.
   destruct (H1 t0).
   assert (X : ME.In t0 nil); auto; inversion X.
   intros x l Hrec s' N N' E; simpl in *.
   apply (Seq_trans _ _ st) with (f x (fold_right f i (remove_list x s'))).
   apply Hf1; auto.
   apply Hrec; auto.
   inversion N; auto.
   destruct (remove_list_correct x N'); auto.
   apply remove_list_equal; auto.
   apply Seq_sym; auto.
   apply remove_list_fold_right; auto.
   unfold ListEq in E.
   rewrite <- E; auto.
  Qed.

  Lemma fold_right_add :
    forall s' s x, NoRedun s -> NoRedun s' -> ~ ME.In x s ->
    ListAdd x s s' -> eqA (fold_right f i s') (f x (fold_right f i s)).
  Proof.   
   simple induction s'.
   unfold ListAdd; intros.
   destruct (H2 x); clear H2.
   assert (X : ME.In x nil); auto; inversion X.
   intros x' l' Hrec s x N N' IN EQ; simpl.
   (* if x=x' *)
   destruct (eq_dec x x').
   apply Hf1; auto.
   apply fold_right_equal; auto.
   inversion_clear N'; trivial.
   unfold ListEq; unfold ListAdd in EQ; intros.
   destruct (EQ y); clear EQ.
   split; intros.
   destruct H; auto.
   inversion_clear N'.
   destruct H2; apply In_eq with y; auto; order.
   assert (X:ME.In y (x' :: l')); auto; inversion_clear X; auto.
   destruct IN; apply In_eq with y; auto; order.
   (* else x<>x' *)   
   apply (Seq_trans _ _ st) with (f x' (f x (fold_right f i (remove_list x' s)))).
   apply Hf1; auto.
   apply Hrec; auto.
   destruct (remove_list_correct x' N); auto.
   inversion_clear N'; auto.
   destruct (remove_list_correct x' N).
   rewrite H0; clear H0.
   intuition.
   apply remove_list_add; auto.
   apply (Seq_trans _ _ st) with (f x (f x' (fold_right f i (remove_list x' s)))).
   apply Hf2; auto.
   apply Hf1; auto.
   apply Seq_sym; auto.
   apply remove_list_fold_right; auto.
   destruct (EQ x'). 
   destruct H; auto; destruct n; auto.
  Qed.

  End noredunA_Remove.

  (** * Alternative (weaker) specifications for [fold] *)

  Section Old_Spec_Now_Properties. 

  (** When [FSets] was first designed, the order in which Ocaml's [Set.fold]
        takes the set elements was unspecified. This specification reflects this fact: 
  *)

  Lemma fold_0 : 
      forall s (A : Set) (i : A) (f : elt -> A -> A),
      exists l : list elt,
        NoRedun l /\
        (forall x : elt, In x s <-> InA E.eq x l) /\
        fold f s i = fold_right f i l.
  Proof.
  intros; exists (rev (elements s)); split.
  apply noredunA_rev; auto.
  exact E.eq_trans.
  split; intros.
  rewrite elements_iff; do 2 rewrite InA_alt.
  split; destruct 1; generalize (In_rev (elements s) x0); exists x0; intuition.
  rewrite fold_left_rev_right.
  apply fold_1.
  Qed.

  (** An alternate (and previous) specification for [fold] was based on 
      the recursive structure of a set. It is now lemmas [fold_1] and 
      [fold_2]. *)

  Lemma fold_1 :
   forall s (A : Set) (eqA : A -> A -> Prop) 
     (st : Setoid_Theory A eqA) (i : A) (f : elt -> A -> A),
   Empty s -> eqA (fold f s i) i.
  Proof.
  unfold Empty; intros; destruct (fold_0 s i f) as (l,(H1, (H2, H3))).
  rewrite H3; clear H3.
  generalize H H2; clear H H2; case l; simpl; intros.
  apply Seq_refl; trivial.
  elim (H e).
  elim (H2 e); intuition. 
  Qed.

  Lemma fold_2 :
   forall s s' x (A : Set) (eqA : A -> A -> Prop)
     (st : Setoid_Theory A eqA) (i : A) (f : elt -> A -> A),
   compat_op E.eq eqA f ->
   transpose eqA f ->
   ~ In x s -> Add x s s' -> eqA (fold f s' i) (f x (fold f s i)).
  Proof.
  intros; destruct (fold_0 s i f) as (l,(Hl, (Hl1, Hl2))); 
    destruct (fold_0 s' i f) as (l',(Hl', (Hl'1, Hl'2))).
  rewrite Hl2; rewrite Hl'2; clear Hl2 Hl'2.
  apply fold_right_add with (eqA := eqA); auto.
  rewrite <- Hl1; auto.
  intros; rewrite <- Hl1; rewrite <- Hl'1; auto.
  Qed.

  (** Similar specification for [cardinal]. *)

  Lemma cardinal_fold : forall s, cardinal s = fold (fun _ => S) s 0.
  Proof.
  intros; rewrite cardinal_1; rewrite M.fold_1.
  symmetry; apply fold_left_length; auto.
  Qed.

  Lemma cardinal_0 :
     forall s, exists l : list elt,
        noredunA E.eq l /\
        (forall x : elt, In x s <-> InA E.eq x l) /\ 
        cardinal s = length l.
  Proof. 
  intros; exists (elements s); intuition; apply cardinal_1.
  Qed.

  Lemma cardinal_1 : forall s, Empty s -> cardinal s = 0.
  Proof.
  intros; rewrite cardinal_fold; apply fold_1; auto.
  Qed.

  Lemma cardinal_2 :
    forall s s' x, ~ In x s -> Add x s s' -> cardinal s' = S (cardinal s).
  Proof.
  intros; do 2 rewrite cardinal_fold.
  change S with ((fun _ => S) x).
  apply fold_2; auto.
  Qed.

  End Old_Spec_Now_Properties.

  (** * Induction principle over sets *)

  Lemma cardinal_inv_1 : forall s, cardinal s = 0 -> Empty s. 
  Proof. 
    intros s; rewrite M.cardinal_1; intros H a; red.
    rewrite elements_iff.
    destruct (elements s); simpl in *; discriminate || inversion 1.
  Qed.
  Hint Resolve cardinal_inv_1.
 
  Lemma cardinal_inv_2 :
   forall s n, cardinal s = S n -> exists x : elt, In x s.
  Proof. 
    intros; rewrite M.cardinal_1 in H.
    generalize (elements_2 (s:=s)).
    destruct (elements s); try discriminate. 
    exists e; auto.
  Qed.

  Lemma Equal_cardinal_aux :
   forall n s s', cardinal s = n -> s[=]s' -> cardinal s = cardinal s'.
  Proof.
     simple induction n; intros.
     rewrite H; symmetry .
     apply cardinal_1.
     rewrite <- H0; auto.
     destruct (cardinal_inv_2 H0).
     revert H0.
     rewrite (cardinal_2 (s:=remove x s) (s':=s) (x:=x)); auto with set.
     rewrite (cardinal_2 (s:=remove x s') (s':=s') (x:=x)); auto with set.
     rewrite H1 in H2; auto with set.
  Qed.

  Lemma Equal_cardinal : forall s s', s[=]s' -> cardinal s = cardinal s'.
  Proof. 
    intros; apply Equal_cardinal_aux with (cardinal s); auto.
  Qed.

  Add Morphism cardinal : cardinal_m.
  Proof.
  exact Equal_cardinal.
  Qed.

  Hint Resolve Add_add Add_remove Equal_remove cardinal_inv_1 Equal_cardinal.

  Lemma empty_cardinal : cardinal empty = 0.
  Proof.
  rewrite cardinal_fold; apply fold_1; auto.
  Qed.

  Hint Immediate empty_cardinal cardinal_1 : set.

  Lemma cardinal_induction :
   forall P : t -> Prop,
   (forall s, Empty s -> P s) ->
   (forall s s', P s -> forall x, ~In x s -> Add x s s' -> P s') ->
   forall n s, cardinal s = n -> P s.
  Proof.
  simple induction n; intros; auto.
  destruct (cardinal_inv_2 H2). 
  apply H0 with (remove x s) x; auto.
  apply H1; auto.
  rewrite (cardinal_2 (x:=x)(s:=remove x s)(s':=s)) in H2; auto.
  Qed.

  Lemma set_induction :
   forall P : t -> Prop,
   (forall s : t, Empty s -> P s) ->
   (forall s s' : t, P s -> forall x : elt, ~In x s -> Add x s s' -> P s') ->
   forall s : t, P s.
  Proof.
  intros; apply cardinal_induction with (cardinal s); auto.
  Qed.  

  (** Other formulation of [fold_1] and [fold_2]. *)

  Section Fold. 

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

  Lemma fold_equal : forall s s', s[=]s' -> eqA (fold f s i) (fold f s' i).
  Proof. 
     intros s; pattern s; apply set_induction; clear s; intros.
     apply (Seq_trans _ _ st) with i; auto.
     apply fold_1; auto.
     apply Seq_sym; auto; apply fold_1; auto.
     rewrite <- H0; auto.
     apply (Seq_trans _ _ st) with (f x (fold f s i)); auto.
     apply fold_2 with (eqA := eqA); auto.
     apply Seq_sym; auto; apply fold_2 with (eqA := eqA); auto.
     unfold Add in *; intros.
     rewrite <- H2; auto.
  Qed.
   
  Lemma fold_add : forall s x, ~In x s -> eqA (fold f (add x s) i) (f x (fold f s i)).
  Proof. 
    intros; apply fold_2 with (eqA := eqA); auto.
  Qed.

  End Fold.

  (** properties of [cardinal] *)

  Lemma singleton_cardinal : forall x, cardinal (singleton x) = 1.
  Proof.
  intros.
  rewrite (singleton_equal_add x).
  replace 0 with (cardinal empty); auto with set.
  apply cardinal_2 with x; auto with set.
  Qed.

  Hint Resolve singleton_cardinal: set.

  Lemma fold_plus :
   forall s (p : nat), fold (fun _ => S) s p = fold (fun _ => S) s 0 + p.
  Proof.
  assert (st := gen_st nat).
  assert (fe : compat_op E.eq (eq (A:=_)) (fun _ => S)) by unfold compat_op; auto. 
  assert (fp : transpose (eq (A:=_)) (fun _:elt => S)) by unfold transpose; auto.
  intros s p; pattern s; apply set_induction; clear s; intros.
  rewrite (fold_1 st p (fun _ => S) H).
  rewrite (fold_1 st 0 (fun _ => S) H); trivial.
  assert (forall p s', Add x s s' -> fold (fun _ => S) s' p = S (fold (fun _ => S) s p)).
   change S with ((fun _ => S) x).  
   intros; apply fold_2; auto.
  rewrite H2; auto.
  rewrite (H2 0); auto.
  rewrite H.
  simpl; auto.
  Qed.

  Lemma fold_commutes :
   forall (A : Set) (f : elt -> A -> A) (i : A),
   compat_op E.eq (eq (A:=_)) f ->
   transpose (eq (A:=_)) f ->
   forall s x, fold f s (f x i) = f x (fold f s i).
  Proof.
  intro A.
  assert (st := gen_st A). 
  intros; pattern s; apply set_induction; clear s; intros.
  rewrite (fold_1 st i f H1).
  rewrite (fold_1 st (f x i) f H1).
  apply H; auto. 
  apply (Seq_trans _ _ st) with (f x0 (fold f s (f x i))).
  rewrite (fold_2 st (f x i) H H0 H2 H3).
  apply (Seq_trans _ _ st) with (f x0 (f x (fold f s i))).
  apply H; auto.
  rewrite H1; auto. 
  rewrite (fold_2 st i H H0 H2 H3).
  rewrite H1; auto. 
  Qed.

  Lemma fold_union_inter :
   forall (A : Set) (f : elt -> A -> A) (i : A),
   compat_op E.eq (eq (A:=_)) f ->
   transpose (eq (A:=_)) f ->
   forall s s',
   fold f (union s s') (fold f (inter s s') i) = fold f s (fold f s' i).
  Proof.
  intro A.
  assert (st := gen_st A). 
  intros; pattern s; apply set_induction; clear s; intros.
  rewrite (fold_1 st (fold f s' i) f H1).
  rewrite (fold_1 st i f (empty_inter_1 (s':=s') H1)).
  assert (H3 : Equal (union s s') s') by auto with set.
  rewrite (fold_equal st i H H0 H3); auto.
  assert (H4 : Add x (union s s') (union s'0 s')) by auto with set.
  case (In_dec x s'); intro.
  (* In x s' *)
  assert (H5:Add x (inter s s') (inter s'0 s')) by auto with set.
  assert (H6:~In x (inter s s')) by rewrite inter_iff; intuition.
  rewrite (fold_2 st i H H0 H6 H5).
  rewrite (fold_2 st (fold f s' i) H H0 H2 H3).
  assert (H7:Equal (union s'0 s') (union s s')).
   apply equal_sym; eauto with set. 
  rewrite (fold_equal st (f x (fold f (inter s s') i)) H H0 H7).
  rewrite fold_commutes; auto.
  (* ~(In x s') *)
  rewrite (fold_2 st (fold f s' i) H H0 H2 H3).
  assert (H5: Equal (inter s'0 s') (inter s s')).
   apply equal_sym; eauto with set. 
  rewrite (fold_equal st i H H0 H5).
  assert (H6:Add x (union s s') (union s'0 s')) by auto with set. 
  assert (H7:~In x (union s s')) by auto with set. 
  rewrite (fold_2 st (fold f (inter s s') i) H H0 H7 H6); auto.
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
   forall s s', cardinal (diff s s')  + cardinal (inter s s') = cardinal s .
  Proof.
  intro s; pattern s; apply set_induction; clear s; intuition.
  assert (Empty (diff s s')) by auto with set.  
  rewrite (cardinal_1 H0). 
  assert (Empty (inter s s')) by auto with set.  
  rewrite (cardinal_1 H1).
  rewrite (cardinal_1 H); auto. 
  do 3 rewrite cardinal_fold.
  rewrite <- fold_plus.
  apply fold_diff_inter; auto.
  Qed.

  Lemma subset_cardinal : forall s s', s[<=]s' -> cardinal s <= cardinal s' .
  Proof.
  intros.
  rewrite <- (diff_inter_cardinal s' s).
  rewrite (Equal_cardinal (inter_sym s' s)).
  rewrite (Equal_cardinal (inter_subset_equal H)); auto with arith.
  Qed.

  Lemma union_inter_cardinal :
   forall s s', cardinal (union s s') + cardinal (inter s s')  = cardinal s  + cardinal s' .
  Proof.
  intros.
  do 4 rewrite cardinal_fold.
  do 2 rewrite <- fold_plus.
  apply fold_union_inter; auto.
  Qed.

  Lemma union_cardinal : forall s s', cardinal (union s s') <= cardinal s  + cardinal s' .
  Proof.
    intros; generalize (union_inter_cardinal s s'); intros; rewrite <- H; auto with arith.
  Qed.

  Lemma add_cardinal_1 : forall s x, In x s -> cardinal (add x s) = cardinal s .
  Proof.
  auto with set.  
  Qed.

  Lemma add_cardinal_2 :
   forall s x, ~In x s -> cardinal (add x s)  = S (cardinal s).
  Proof.
  intros.
  do 2 rewrite cardinal_fold.
  change S with ((fun _ => S) x);
   apply fold_add with (eqA := eq (A:=nat)); auto.
  Qed.

  Hint Resolve subset_cardinal union_cardinal add_cardinal_1 add_cardinal_2.

End Properties.
