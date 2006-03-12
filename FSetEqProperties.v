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

(** This module proves many properties of finite sets that 
    are consequences of the axiomatization in [FsetInterface] 
    Contrary to the functor in [FsetProperties] it uses 
    sets operations instead of predicates over sets, i.e.
    [mem x s=true] instead of [In x s], 
    [equal s s'=true] instead of [Equal s s'], etc. *)


Require Import FSetProperties.
Require Import Zerob.
Require Import Sumbool.
Require Import Omega.

Module EqProperties (M:S).
  Import M.
  Import Logic. (* to unmask [eq] *)  
  Import Peano. (* to unmask [lt] *)
  
  Module ME := OrderedTypeFacts E.  
  Module MP := Properties M.
  Import MP.
  Import MP.FM.

  Definition Add := MP.Add.

  Section Old_Spec_Now_Properties. 

  (** Other old specifications written with boolean equalities. *) 

  Variable s s' : t.
  Variable x y z : elt.

  Lemma mem_eq: 
    E.eq x y -> mem x s=mem y s.
  Proof. 
  intro H; rewrite H; auto.
  Qed.

  Lemma equal_mem_1: 
    (forall a, mem a s=mem a s') -> equal s s'=true.
  Proof. 
  intros; apply equal_1; unfold Equal; intros.
  do 2 rewrite mem_iff; rewrite H; tauto.
  Qed.

  Lemma equal_mem_2: 
    equal s s'=true -> forall a, mem a s=mem a s'.
  Proof. 
  intros; rewrite (equal_2 H); auto.
  Qed.

  Lemma subset_mem_1: 
    (forall a, mem a s=true->mem a s'=true) -> subset s s'=true.
  Proof. 
  intros; apply subset_1; unfold Subset; intros a.
  do 2 rewrite mem_iff; auto.
  Qed.

  Lemma subset_mem_2: 
    subset s s'=true -> forall a, mem a s=true -> mem a s'=true.
  Proof. 
  intros H a; do 2 rewrite <- mem_iff; apply subset_2; auto.
  Qed.
  
  Lemma empty_mem: mem x empty=false.
  Proof. 
  rewrite <- not_mem_iff; auto.
  Qed.

  Lemma is_empty_equal_empty: is_empty s = equal s empty.
  Proof. 
  apply bool_1; split; intros.
  rewrite <- (empty_is_empty_1 (s:=empty)); auto with set.
  rewrite <- is_empty_iff; auto with set.
  Qed.
  
  Lemma choose_mem_1: choose s=Some x -> mem x s=true.
  Proof.  
  auto.
  Qed.

  Lemma choose_mem_2: choose s=None -> is_empty s=true.
  Proof.
  auto.
  Qed.

  Lemma add_mem_1: mem x (add x s)=true.
  Proof.
  auto.
  Qed.  
 
  Lemma add_mem_2: 
  ~ E.eq x y -> mem y (add x s)=mem y s.
  Proof. 
  apply add_neq_b.
  Qed.

  Lemma remove_mem_1: mem x (remove x s)=false.
  Proof. 
  rewrite <- not_mem_iff; auto.
  Qed. 
 
  Lemma remove_mem_2: 
  ~ E.eq x y -> mem y (remove x s)=mem y s.
  Proof. 
  apply remove_neq_b.
  Qed.

  Lemma singleton_equal_add: 
    equal (singleton x) (add x empty)=true.
  Proof.
  rewrite (singleton_equal_add x); auto with set.
  Qed.  

  Lemma union_mem: 
    mem x (union s s')=mem x s || mem x s'.
  Proof. 
  apply union_b.
  Qed.

  Lemma inter_mem: 
    mem x (inter s s')=mem x s && mem x s'.
  Proof. 
  apply inter_b.
  Qed.

  Lemma diff_mem: 
    mem x (diff s s')=mem x s && negb (mem x s').
  Proof. 
  apply diff_b.
  Qed.

  Section fold. 

  Variable A:Set. 
  Variable eqA:A->A->Prop.
  Variable st:Setoid_Theory _ eqA.
  Variable i:A.
  Variable f:elt->A->A.
  Variable Comp:compat_op E.eq eqA f. 
  Variable Assoc:transpose eqA f.
 
  Lemma fold_empty: eqA (fold f empty i) i.
  Proof. 
  apply fold_empty; auto.
  Qed.

  Lemma fold_equal: 
    equal s s'=true -> eqA (fold f s i) (fold f s' i).
  Proof. 
  intros; apply fold_equal with (eqA:=eqA); auto.
  Qed.
   
  Lemma fold_add: 
    mem x s=false -> eqA (fold f (add x s) i) (f x (fold f s i)).
  Proof. 
    intros; apply fold_add with (eqA:=eqA); auto.
    rewrite not_mem_iff; auto.
  Qed.

  End fold.

  Section Filter.
  
  Variable f:elt->bool.
  Variable Comp: compat_bool E.eq f.

  Lemma filter_mem: mem x (filter f s)=mem x s && f x.
  Proof. 
  apply filter_b; auto.
  Qed.

  Lemma for_all_filter: 
    for_all f s=is_empty (filter (fun x => negb (f x)) s).
  Proof. 
  assert (Comp' : compat_bool E.eq (fun x =>negb (f x))). 
    generalize Comp; unfold compat_bool; intros; f_equal; auto. 
  apply bool_1; split; intros.
  apply is_empty_1.
  unfold Empty; intros. 
  rewrite filter_iff; auto.
  red; destruct 1.
  rewrite <- (@for_all_iff s f) in H; auto.
  rewrite (H a H0) in H1; discriminate.
  apply for_all_1; auto; red; intros.
  revert H; rewrite <- is_empty_iff.
  unfold Empty; intro H; generalize (H x0); clear H.
  rewrite filter_iff; auto.
  destruct (f x0); auto.
  Qed.

  Lemma exists_filter : 
    exists_ f s=negb (is_empty (filter f s)).
  Proof. 
  apply bool_1; split; intros. 
  destruct (exists_2 Comp H) as (a,(Ha1,Ha2)).
  apply bool_6.
  red; intros; apply (@is_empty_2 _ H0 a); auto.
  generalize (@choose_1 (filter f s)) (@choose_2 (filter f s)).
  destruct (choose (filter f s)).
  intros H0 _; apply exists_1; auto.
  exists e; generalize (H0 e); rewrite filter_iff; auto.
  intros _ H0.
  rewrite (is_empty_1 (H0 (refl_equal None))) in H; auto; discriminate.
  Qed.

  Lemma partition_filter_1: 
     equal (fst (partition f s)) (filter f s)=true.
  Proof. 
  auto.
  Qed.

  Lemma partition_filter_2: 
     equal (snd (partition f s)) (filter (fun x => negb (f x)) s)=true.
  Proof. 
  auto.
  Qed.

  End Filter.
  End Old_Spec_Now_Properties.

  Hint Immediate empty_mem is_empty_equal_empty add_mem_1
    remove_mem_1 singleton_equal_add union_mem inter_mem
    diff_mem filter_mem for_all_filter exists_filter : set. 
  Hint Resolve equal_mem_1 subset_mem_1 choose_mem_1
    choose_mem_2 add_mem_2 remove_mem_2 : set.

Section MoreProperties.

(** properties of [mem] *)

Lemma mem_3 : forall s x, ~In x s -> mem x s=false.
Proof.
intros; rewrite <- not_mem_iff; auto.
Qed.

Lemma mem_4 : forall s x, mem x s=false -> ~In x s.
Proof.
intros; rewrite not_mem_iff; auto.
Qed.

(** Properties of [equal] *) 

Lemma equal_refl: forall s, equal s s=true.
Proof.
auto with set.
Qed.

Lemma equal_sym: forall s s', equal s s'=equal s' s.
Proof.
intros; apply bool_1; do 2 rewrite <- equal_iff; intuition.
Qed.

Lemma equal_trans: 
 forall s u v, equal s u=true -> equal u v=true -> equal s v=true.
Proof.
intros; rewrite (equal_2 H); auto.
Qed.

Lemma equal_equal: 
 forall s s' s'', equal s s'=true -> equal s s''=equal s' s''.
Proof.
intros; rewrite (equal_2 H); auto.
Qed.

Lemma equal_cardinal: 
 forall s s', equal s s'=true -> cardinal s=cardinal s'.
Proof.
intros; rewrite (equal_2 H); auto.
Qed.

Hint Resolve equal_refl equal_cardinal equal_equal:set.
Hint Immediate equal_sym :set.

(* Properties of [subset] *)

Lemma subset_refl: forall s, subset s s=true. 
Proof.
auto with set.
Qed.

Lemma subset_antisym: 
 forall s s', subset s s'=true -> subset s' s=true -> equal s s'=true.
Proof.
intros s s'; do 2 rewrite <- subset_iff; rewrite <- equal_iff.
apply subset_antisym.
Qed.

Lemma subset_trans: 
 forall s s' s'', subset s s'=true -> subset s' s''=true -> subset s s''=true.
Proof.
intros s s' s''; do 3 rewrite <- subset_iff; intros.
apply subset_trans with s'; auto.
Qed.

Lemma subset_equal: 
 forall s s', equal s s'=true -> subset s s'=true.
Proof.
intros; rewrite (equal_2 H); auto with set.
Qed.

Hint Resolve subset_refl subset_equal subset_antisym :set.

(** Properties of [choose] *)

Lemma choose_mem_3: 
 forall s, is_empty s=false -> {x:elt|choose s=Some x /\ mem x s=true}.
Proof.
intros.
generalize (@choose_mem_1 s) (@choose_mem_2 s).
case (choose s);intros.
exists e;auto.
lapply H1;trivial;intros.
rewrite H in H2;discriminate H2.
Qed.

Lemma choose_mem_4: choose empty=None.
Proof.
generalize (@choose_mem_1 empty).
case (@choose empty);intros;auto.
absurd (true=false);auto with bool.
rewrite <- (H e);auto with set.
Qed.

(** Properties of [add] *)

Lemma add_mem_3: 
 forall s x y, mem y s=true -> mem y (add x s)=true.
Proof.
auto.
Qed.

Lemma add_equal: 
 forall s x, mem x s=true -> equal (add x s) s=true.
Proof.
intros s x; rewrite <- mem_iff; intros; apply equal_1; auto with set.
Qed.

Hint Resolve add_mem_3 add_equal :set.

Lemma add_fold: 
 forall (A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory _ eqA))
 (f:elt->A->A)(i:A), (compat_op E.eq eqA f) -> (transpose eqA f) ->
 forall (s:t)(x:elt), mem x s=true -> (eqA (fold f (add x s) i) (fold f s i)).
Proof.
intros; apply fold_equal with (eqA:=eqA); auto with set.
Qed.

Lemma add_cardinal_1: 
 forall s x, mem x s=true -> cardinal (add x s)=cardinal s.
Proof.
auto with set.
Qed.

Lemma add_cardinal_2: 
 forall s x, mem x s=false -> cardinal (add x s)=S (cardinal s).
Proof.
intros.
do 2 rewrite MP.cardinal_fold.
change S with ((fun _ =>S) x); apply fold_add with (eqA:=@eq nat); auto.
Qed.

(** Properties of [remove] *)

Lemma remove_mem_3: 
 forall s x y, mem y (remove x s)=true -> mem y s=true.
Proof.
intros s x y; rewrite remove_b; intros H;destruct (andb_prop _ _ H); auto.
Qed.

Lemma remove_equal: 
 forall s x, mem x s=false -> equal (remove x s) s=true.
Proof.
intros; apply equal_1; apply remove_equal.
intro H0; rewrite (mem_1 H0) in H; discriminate.
Qed.

Hint Resolve remove_mem_3 remove_equal : set.

Lemma add_remove: 
 forall s x, mem x s=true -> equal (add x (remove x s)) s=true.
Proof.
intros; apply equal_1; apply add_remove; auto.
Qed.

Lemma remove_add: 
 forall s x, mem x s=false -> equal (remove x (add x s)) s=true.
Proof.
intros; apply equal_1; apply remove_add; auto.
intro H0; rewrite (mem_1 H0) in H; discriminate.
Qed.

Hint Immediate add_remove remove_add : set.

Lemma remove_fold_1: 
 forall (A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory _ eqA))
 (f:elt->A->A)(i:A), (compat_op E.eq eqA f) -> (transpose eqA f) ->
 forall s x, mem x s=true -> 
 eqA (f x (fold f (remove x s) i)) (fold f s i).
Proof.
intros.
apply Seq_sym; auto.
apply MP.fold_2 with (eqA:=eqA); auto.
Qed.

Lemma remove_fold_2: 
 forall (A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory _ eqA))
 (f:elt->A->A)(i:A), (compat_op E.eq eqA f) -> (transpose eqA f) ->
 forall s x, mem x s=false -> 
 eqA (fold f (remove x s) i) (fold f s i).
Proof.
intros.
apply fold_equal with (eqA:=eqA); auto with set.
Qed.

Lemma remove_cardinal_1: 
 forall s x, mem x s=true -> S (cardinal (remove x s))=cardinal s.
Proof.
intros.
do 2 rewrite cardinal_fold.
change S with ((fun _ =>S) x).
apply remove_fold_1 with (eqA:=@eq nat); auto.
Qed.

Lemma remove_cardinal_2: 
 forall s x, mem x s=false -> cardinal (remove x s)=cardinal s.
Proof.
auto with set.
Qed.

(** Properties of [is_empty] *)

Lemma is_empty_cardinal: forall s, is_empty s = zerob (cardinal s).
Proof.
intros; apply bool_1; split; intros.
rewrite cardinal_1; simpl; auto.
assert (cardinal s = 0) by apply zerob_true_elim; auto.
auto.
Qed.

(** Properties of [singleton] *)

Lemma singleton_mem_1: forall x, mem x (singleton x)=true.
Proof.
intros; apply mem_1; auto.
Qed.

Lemma singleton_mem_2: forall x y, ~E.eq x y -> mem y (singleton x)=false.
Proof.
intros; rewrite singleton_b.
unfold ME.eqb; destruct (ME.eq_dec x y); intuition.
Qed.

Lemma singleton_mem_3: forall x y, mem y (singleton x)=true -> E.eq x y.
Proof.
auto.
Qed.

(* General recursion principes based on [cardinal] *)

Lemma cardinal_set_rec:  forall (P:t->Type),
 (forall s s', equal s s'=true -> P s -> P s') -> 
 (forall s x, mem x s=false -> P s -> P (add x s)) -> 
 P empty -> forall n s, cardinal s=n -> P s.
Proof.
intros.
apply cardinal_induction with n; auto; intros.
apply X with empty; auto with set.
apply X with (add x s0); auto with set.
apply equal_1; intro a; rewrite add_iff; rewrite (H1 a); tauto.
apply X0; auto with set; apply mem_3; auto.
Qed.

Lemma set_rec:  forall (P:t->Type),
 (forall s s', equal s s'=true -> P s -> P s') ->
 (forall s x, mem x s=false -> P s -> P (add x s)) -> 
 P empty -> forall s, P s.
Proof.
intros;apply cardinal_set_rec with (cardinal s);auto.
Qed.

(** Properties of [union] *)

Lemma union_sym:
 forall s s', equal (union s s') (union s' s)=true.
Proof.
intros;apply equal_1;apply union_sym. 
Qed.

Lemma union_subset_equal: 
 forall s s', subset s s'=true -> equal (union s s') s'=true.
Proof.
intros; apply equal_1; apply union_subset_equal; auto.
Qed.

Lemma union_equal_1: 
 forall s s' s'', equal s s'=true->
 equal (union s s'') (union s' s'')=true.
Proof.
intros; apply equal_1; apply union_equal_1; auto.
Qed.

Lemma union_equal_2: 
 forall s s' s'', equal s' s''=true->
 equal (union s s') (union s s'')=true.
Proof.
intros;apply equal_1;apply union_equal_2; auto.
Qed.

Lemma union_assoc: 
 forall s s' s'',
 equal (union (union s s') s'') (union s (union s' s''))=true.
Proof.
intros;apply equal_1;apply union_assoc; auto.
Qed.

Lemma add_union_singleton: 
 forall s x, equal (add x s) (union (singleton x) s)=true.
Proof.
intros;apply equal_1;apply add_union_singleton.
Qed.

Lemma union_add: 
 forall s s' x,
 equal (union (add x s) s') (add x (union s s'))=true.
Proof.
intros;apply equal_1;apply union_add.
Qed.

(* caracterisation of [union] via [subset] *)

Lemma union_subset_1:
 forall s s',(subset s (union s s'))=true.
Proof.
intros;apply subset_mem_1;intros;rewrite union_mem;rewrite H;auto.
Qed.

Lemma union_subset_2:
 forall s s',(subset s' (union s s'))=true.
Proof.
intros;apply subset_mem_1;intros;rewrite union_mem;rewrite H;apply orb_b_true.
Qed.

Lemma union_subset_3:
 forall s s' s'', (subset s s'')=true -> (subset s' s'')=true -> 
    (subset (union s s') s'')=true.
Proof.
intros;apply subset_mem_1;intros;rewrite union_mem in H1.
elim (orb_true_elim _ _ H1);intros.
apply (subset_mem_2 _ _ H _ a0).
apply (subset_mem_2 _ _ H0 _ b).
Qed.

(** Properties of [inter] *) 

Lemma inter_sym:
 forall s s',(equal (inter s s') (inter s' s))=true.
Proof.
intros;apply equal_mem_1;intros.
do 2 rewrite inter_mem.
auto with bool.
Qed.

Lemma inter_subset_equal: 
 forall s s',(subset s s')=true->(equal (inter s s') s)=true.
Proof.
intros.
apply equal_mem_1;intros.
rewrite inter_mem.
apply (bool_eq_ind (mem a s));intros;simpl;auto.
rewrite (subset_mem_2 _ _ H _ H0);auto.
Qed.

Lemma inter_equal_1: 
 forall s s' s'', equal s s'=true->
 equal (inter s s'') (inter s' s'')=true.
Proof.
intros s s' s''; do 2 rewrite <- equal_iff; apply inter_equal_1.
Qed.

Lemma inter_equal_2: 
 forall s s' s'', equal s' s''=true->
 equal (inter s s') (inter s s'')=true.
Proof.
intros s s' s''; do 2 rewrite <- equal_iff; apply inter_equal_2.
Qed.

Lemma inter_assoc: 
 forall s s' s'',
 equal (inter (inter s s') s'') (inter s (inter s' s''))=true.
Proof.
intros; apply equal_1; apply inter_assoc.
Qed.

Lemma union_inter_1: 
 forall s s' s'',
 equal (inter (union s s') s'') (union (inter s s'') (inter s' s''))=true.
Proof.
intros;apply equal_1;apply union_inter_1.
Qed.

Lemma union_inter_2: 
 forall s s' s'',
 equal (union (inter s s') s'') (inter (union s s'') (union s' s''))=true.
Proof.
intros; apply equal_1; apply union_inter_2.
Qed.

Lemma inter_add_1: 
 forall s s' x, mem x s'=true -> 
 equal (inter (add x s) s') (add x (inter s s'))=true.
Proof.
intros; apply equal_1; apply inter_add_1; auto with set.
Qed.

Lemma inter_add_2: 
 forall s s' x, mem x s'=false -> 
 equal (inter (add x s) s') (inter s s')=true.
Proof.
intros; apply equal_1; apply inter_add_2.
rewrite not_mem_iff; auto.
Qed.

(* caracterisation of [union] via [subset] *)

Lemma inter_subset_1:
 forall s s',(subset (inter s s') s)=true.
Proof.
intros;apply subset_mem_1;intros;rewrite inter_mem in H;elim (andb_prop _ _ H);auto.
Qed.

Lemma inter_subset_2:
 forall s s',(subset (inter s s') s')=true.
Proof.
intros;apply subset_mem_1;intros;rewrite inter_mem in H;elim (andb_prop _ _ H);auto.
Qed.

Lemma inter_subset_3:
 forall s s' s'',(subset s'' s)=true -> (subset s'' s')=true -> 
    (subset s'' (inter s s'))=true.
intros;apply subset_mem_1;intros;rewrite inter_mem.
rewrite (subset_mem_2 _ _ H _ H1);
rewrite (subset_mem_2 _ _ H0 _ H1);auto.
Qed.

(** Properties of [union],[inter],[fold] and [cardinal] *)

Lemma exclusive_set : forall s s' x,
 ~In x s\/~In x s' <-> mem x s && mem x s'=false.
Proof.
intros; do 2 rewrite not_mem_iff.
destruct (mem x s); destruct (mem x s'); intuition.
Qed.

Lemma fold_union: 
 forall (A:Set)(f:elt->A->A)(i:A), 
 compat_op E.eq (@eq A) f -> transpose (@eq A) f -> 
 forall s s', (forall x, mem x s && mem x s'=false) -> 
 fold f (union s s') i = fold f s (fold f s' i).
Proof.
intros; apply fold_union; auto; intros.
rewrite exclusive_set; auto.
Qed.

Lemma union_cardinal: 
 forall s s', (forall x, mem x s && mem x s'=false) -> 
 cardinal (union s s')=cardinal s+cardinal s'.
Proof.
intros; apply union_cardinal; auto; intros.
rewrite exclusive_set; auto.
Qed.

(** Properties of [diff] *)

Lemma diff_subset: 
 forall s s', subset (diff s s') s=true.
Proof.
intros.
apply subset_mem_1;intros.
rewrite diff_mem in H.
elim (andb_prop _ _ H);auto.
Qed.

Lemma diff_subset_equal:
 forall s s', subset s s'=true -> equal (diff s s') empty=true.
Proof.
intros.
apply equal_mem_1;intros.
rewrite empty_mem.
rewrite diff_mem.
generalize (@subset_mem_2 _ _ H a).
case (mem a s);simpl;intros;auto.
rewrite H0;auto.
Qed.

Lemma remove_inter_singleton: 
 forall s x, equal (remove x s) (diff s (singleton x))=true.
Proof.
intros;apply equal_mem_1;intros.
rewrite diff_mem.
elim (ME.eq_dec x a); intros.
rewrite <- (mem_eq (remove x s) _ _ a0).
rewrite <- (mem_eq s _ _ a0).
rewrite <- (mem_eq (singleton x) _ _ a0).
rewrite remove_mem_1;rewrite singleton_mem_1;rewrite andb_b_false;auto.
rewrite singleton_mem_2;auto;simpl;rewrite andb_b_true;auto with set.
Qed.

Lemma diff_inter_empty:
 forall s s', equal (inter (diff s s') (inter s s')) empty=true. 
Proof.
intros; apply equal_1; apply diff_inter_empty; auto.
Qed.

Lemma diff_inter_all: 
forall s s', equal (union (diff s s') (inter s s')) s=true.
Proof.
intros; apply equal_1; apply diff_inter_all; auto.
Qed.

Lemma diff_inter_cardinal: 
 forall s s',(cardinal (diff s s'))+(cardinal (inter s s'))=(cardinal s).
Proof.
intros.
do 3 rewrite MP.cardinal_fold.
rewrite <- fold_plus.
apply fold_diff_inter; auto.
Qed.

Lemma subset_cardinal: 
 forall s s', subset s s'=true -> cardinal s<=cardinal s'.
Proof.
intros.
rewrite <- (diff_inter_cardinal s' s).
rewrite (equal_cardinal _ _ (inter_sym s' s)).
rewrite (equal_cardinal _ _ (inter_subset_equal _ _ H)); auto with arith.
Qed.

(** Properties of [for_all] *)

Section For_all.

Variable f : elt->bool.
Variable Comp : (compat_bool E.eq f).

Let Comp' : (compat_bool E.eq (fun x =>negb (f x))).
Proof.
generalize Comp; unfold compat_bool; intros; apply (f_equal negb);auto.
Qed.

Lemma for_all_mem_1: 
 forall s, (forall x, (mem x s)=true->(f x)=true) -> (for_all f s)=true.
Proof.
intros.
rewrite for_all_filter; auto.
rewrite is_empty_equal_empty.
apply equal_mem_1;intros.
rewrite filter_mem; auto.
rewrite empty_mem.
generalize (H a); case (mem a s);intros;auto.
rewrite H0;auto.
Qed.

Lemma for_all_mem_2: 
 forall s, (for_all f s)=true -> forall x,(mem x s)=true -> (f x)=true. 
Proof.
intros.
rewrite for_all_filter in H; auto.
rewrite is_empty_equal_empty in H.
generalize (equal_mem_2 _ _ H x).
rewrite filter_mem; auto.
rewrite empty_mem.
rewrite H0; simpl;intros.
replace true with (negb false);auto;apply negb_sym;auto.
Qed.

Lemma for_all_mem_3: 
 forall s x,(mem x s)=true -> (f x)=false -> (for_all f s)=false.
Proof.
intros.
apply (bool_eq_ind (for_all f s));intros;auto.
rewrite for_all_filter in H1; auto.
rewrite is_empty_equal_empty in H1.
generalize (equal_mem_2 _ _ H1 x).
rewrite filter_mem; auto.
rewrite empty_mem.
rewrite H.
rewrite H0.
simpl;auto.
Qed.

Lemma for_all_mem_4: 
 forall s, (for_all f s)=false -> {x:elt | (mem x s)=true /\ (f x)=false}.
intros.
rewrite for_all_filter in H; auto.
elim (choose_mem_3 _ H);intros;elim p;intros.
exists x.
rewrite filter_mem in H1; auto.
elim (andb_prop _ _ H1).
split;auto.
replace false with (negb true);auto;apply negb_sym;auto.
Qed.

End For_all.

(** Properties of [exists] *)

Section exists_.

Variable f : elt->bool.
Variable Comp : (compat_bool E.eq f).

Let Comp' : (compat_bool E.eq (fun x => negb (f x))).
Proof.
generalize Comp; unfold compat_bool; intros; apply (f_equal negb);auto.
Qed.

Lemma for_all_exists: 
 forall s, (exists_ f s)=(negb (for_all (fun x =>negb (f x)) s)).
Proof.
intros.
rewrite for_all_filter; auto.
rewrite exists_filter; auto.
apply (f_equal negb).
do 2 rewrite is_empty_equal_empty.
apply equal_equal.
apply equal_mem_1;intros.
do 2 (rewrite filter_mem; auto).
rewrite negb_elim;auto.
generalize Comp'; unfold compat_bool; intros; apply (f_equal negb); auto.
Qed.

Lemma exists_mem_1: 
 forall s, (forall x, (mem x s)=true->(f x)=false) -> (exists_ f s)=false.
Proof.
intros.
rewrite for_all_exists; auto.
rewrite for_all_mem_1;auto with bool.
intros;generalize (H x H0);intros. 
symmetry;apply negb_sym;simpl;auto.
Qed.

Lemma exists_mem_2: 
 forall s, (exists_ f s)=false -> forall x, (mem x s)=true -> (f x)=false. 
Proof.
intros.
rewrite for_all_exists in H.
replace false with (negb true);auto;apply negb_sym;symmetry.
rewrite (for_all_mem_2 (fun x => negb (f x)) Comp' s);simpl;auto.
replace true with (negb false);auto;apply negb_sym;auto.
Qed.

Lemma exists_mem_3: 
 forall s x,(mem x s)=true -> (f x)=true -> (exists_ f s)=true.
Proof.
intros.
rewrite for_all_exists.
symmetry;apply negb_sym;simpl.
apply for_all_mem_3 with x;auto.
rewrite H0;auto.
Qed.

Lemma exists_mem_4: 
 forall s, (exists_ f s)=true -> {x:elt | (mem x s)=true /\ (f x)=true}.
Proof.
intros.
rewrite for_all_exists in H.
elim (for_all_mem_4 (fun x =>negb (f x)) Comp' s);intros.
elim p;intros.
exists x;split;auto.
replace true with (negb false);auto;apply negb_sym;auto.
replace false with (negb true);auto;apply negb_sym;auto.
Qed.

End exists_.

Section Sum.


Definition sum (f:elt -> nat)(s:t) := fold (fun x => plus (f x)) s 0. 

Lemma sum_plus : 
  forall f g, (compat_nat E.eq f) -> (compat_nat E.eq g) -> 
    forall s, (sum (fun x =>(f x)+(g x)) s) = (sum f s)+(sum g s).
Proof.
unfold sum.
intros f g Hf Hg.
assert (fc : compat_op E.eq (@eq _) (fun x:elt =>plus (f x))).  auto.
assert (ft : transpose (@eq _) (fun x:elt =>plus (f x))). red; intros; omega.
assert (gc : compat_op E.eq (@eq _) (fun x:elt => plus (g x))). auto.
assert (gt : transpose (@eq _) (fun x:elt =>plus (g x))). red; intros; omega.
assert (fgc : compat_op E.eq (@eq _) (fun x:elt =>plus ((f x)+(g x)))). auto.
assert (fgt : transpose (@eq _) (fun x:elt=>plus ((f x)+(g x)))). red; intros; omega.
assert (st := gen_st nat).
intros s;pattern s; apply set_rec.
intros.
rewrite <- (fold_equal _ _ _ _ st O _ fc ft H).
rewrite <- (fold_equal _ _ _ _ st O _ gc gt H).
rewrite <- (fold_equal _ _ _ _ st O _ fgc fgt H); auto.
assert (fold_add' := fun s t =>(fold_add s t _ _ st)).
intros; do 3 (rewrite fold_add';auto).
rewrite H0;simpl;omega.
intros; do 3 rewrite (fold_empty _ _ st);auto.
Qed.

Lemma filter_equal : forall f, (compat_bool E.eq f) -> 
     forall s s',(Equal s s') -> (Equal (filter f s) (filter f s')).
Proof.
unfold Equal; split; intros; elim (H0 a); intros; apply filter_3; eauto.
Qed.

Lemma add_filter_1 : forall f, (compat_bool E.eq f) -> 
  forall s s' x, (f x)=true -> (Add x s s') -> (Add x (filter f s) (filter f s')).
Proof.
unfold Add; split; intros; elim (H1 y); clear H1; intros.
elim H1; [ auto | right; eauto | eauto ].
apply filter_3; auto.
elim H2; intros.
intuition.
apply H3; right; eauto.
elim H2; intros.
rewrite <- H0; auto.
eauto.
Qed.

Lemma add_filter_2 :  forall f, (compat_bool E.eq f) -> 
  forall s s' x, (f x)=false -> (Add x s s') -> (Equal (filter f s) (filter f s')).
Proof.
unfold Add, Equal; split; intros; elim (H1 a); clear H1; intros.
elim H1; intros. 
absurd (true=false); auto with bool.
rewrite <- H0. 
rewrite <- (filter_2 H H2); auto.
apply filter_3; eauto.
apply H3; right; eauto.

elim H1; intros. 
absurd (true=false); auto with bool.
rewrite <- H0. 
rewrite <- (filter_2 H H2); auto.
eauto.
eauto.
Qed.

Lemma sum_filter : forall f, (compat_bool E.eq f) -> 
  forall s, (sum (fun x => if f x then 1 else 0) s) = (cardinal (filter f s)).
Proof.
unfold sum; intros f Hf.
assert (st := gen_st nat).
assert (fold_add' := fun s t => fold_add s t _ _ st).
assert (cc : compat_op E.eq (@eq _) (fun x => plus (if f x then 1 else 0))). 
 unfold compat_op; intros.
 rewrite (Hf x x' H); auto.
assert (ct : transpose (@eq _) (fun x => plus (if f x then 1 else 0))).
 unfold transpose; intros; omega.
intros s;pattern s; apply set_rec.
intros.
change elt with E.t.
rewrite <- (fold_equal _ _ _ _ st O _ cc ct H).
rewrite <- (MP.Equal_cardinal (filter_equal _ Hf _ _ (equal_2 H))); auto.
intros; rewrite fold_add'; auto.
generalize (@add_filter_1 f Hf s0 (add x s0) x) (@add_filter_2 f Hf s0 (add x s0) x) .
assert (~ In x (filter f s0)).
 intro H1; rewrite (mem_1 (filter_1 Hf H1)) in H; discriminate H.
case (f x); simpl; intuition.
rewrite (MP.cardinal_2 H1 (H4 (MP.Add_add s0 x))); auto.
rewrite <- (MP.Equal_cardinal (H4 (MP.Add_add s0 x))); auto.
intros; rewrite (fold_empty _ _ st);auto.
rewrite MP.cardinal_1; auto.
unfold Empty; intuition.
elim (@empty_1 a); eauto.
Qed.

Lemma fold_compat : 
  forall (A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory _ eqA))
  (f g:elt->A->A),
  (compat_op E.eq eqA f) -> (transpose eqA f) -> 
  (compat_op E.eq eqA g) -> (transpose eqA g) -> 
  forall (i:A)(s:t),(forall x:elt, (In x s) -> forall y, (eqA (f x y) (g x y))) -> 
  (eqA (fold f s i) (fold g s i)).
Proof.
intros A eqA st f g fc ft gc gt i.
intro s; pattern s; apply set_rec; intros.
apply (Seq_trans _ _ st) with (fold f s0 i).
apply fold_equal with (eqA:=eqA); auto.
rewrite equal_sym; auto.
apply (Seq_trans _ _ st) with (fold g s0 i).
apply H0; intros; apply H1; auto.
elim  (equal_2 H x); intuition.
apply fold_equal with (eqA:=eqA); auto.
apply (Seq_trans _ _ st) with (f x (fold f s0 i)).
apply fold_add with (eqA:=eqA); auto.
apply (Seq_trans _ _ st) with (g x (fold f s0 i)).
apply H1; auto with set.
apply (Seq_trans _ _ st) with (g x (fold g s0 i)).
apply gc; auto.
apply Seq_sym; auto; apply fold_add with (eqA:=eqA); auto.
apply (Seq_trans _ _ st) with i; [idtac | apply Seq_sym; auto]; apply fold_empty; auto.
Qed.

Lemma sum_compat : 
  forall f g, (compat_nat E.eq f) -> (compat_nat E.eq g) -> 
  forall s, (forall x, (In x s) -> (f x)=(g x)) -> (sum f s)=(sum g s).
intros.
unfold sum; apply (fold_compat _ (@eq nat)); auto.
unfold transpose; intros; omega.
unfold transpose; intros; omega.
Qed.

End Sum.

Lemma filter_orb: forall f g, (compat_bool E.eq f) -> (compat_bool E.eq g) ->
  forall s, (Equal (filter (fun x=>orb (f x) (g x)) s) (union (filter f s) (filter g s))).
Proof.
intros.
assert (compat_bool E.eq (fun x => orb (f x) (g x))).
  unfold compat_bool; intros.
  rewrite (H x y H1).
  rewrite (H0 x y H1); auto.
unfold Equal; split; intros.
assert (H3 := filter_1 H1 H2).
assert (H4 := filter_2 H1 H2).
elim (orb_prop _ _ H4); intros; eauto.
elim (union_1 H2); intros. 
apply filter_3; [ auto | eauto | rewrite (filter_2 H H3); auto ].
apply filter_3; [ auto | eauto | rewrite (filter_2 H0 H3); auto with bool].
Qed.

End MoreProperties.

End EqProperties. 
