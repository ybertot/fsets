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

Module EqProperties (M:S).
  Import M.
  Import Logic. (* to unmask [eq] *)  
  Import Peano. (* to unmask [lt] *)
  
  Module ME := OrderedTypeFacts E.  
  Module MP := Properties M.

  Definition Add := MP.Add.

  Section Old_Spec_Now_Properties. 

  (** Other old specifications written with boolean equalities. *) 

  Variable s s' : t.
  Variable x y z : elt.

  Lemma mem_eq: 
    (E.eq x y) -> (mem x s)=(mem y s).
  Proof. 
  intros; apply bool_1.
  generalize (@mem_1 s x) (@mem_1 s y) (@mem_2 s x) (@mem_2 s y).
  intuition. 
  eauto.
  apply H0; apply In_1 with y; auto.
  Qed.

  Lemma equal_mem_1: 
    (forall (a:elt), (mem a s)=(mem a s')) -> (equal s s')=true.
  Proof. 
  intros; apply equal_1; unfold Equal; intuition; eauto.
  Qed.

  Lemma equal_mem_2: 
    (equal s s')=true -> forall (a:elt), (mem a s)=(mem a s').
  Proof. 
  intros; apply bool_1.
  intros; cut (Equal s s'); [clear H; unfold Equal|auto].
  intros H; generalize (H a); intuition.
  Qed.

  Lemma subset_mem_1: 
    (forall (a:elt), (mem a s)=true->(mem a s')=true) -> (subset s s')=true.
  Proof. 
  intros; apply subset_1; unfold Subset; intuition; eauto.
  Qed.

  Lemma subset_mem_2: 
    (subset s s')=true -> forall (a:elt), (mem a s)=true -> (mem a s')=true.
  Proof. 
  intros; apply bool_1.
  cut (Subset s s'); [clear H; unfold Subset|auto].
  intros H; generalize (H a); intuition.
  Qed.
  
  Lemma empty_mem: (mem x empty)=false.
  Proof. 
  apply not_true_is_false; intro; absurd (In x empty); auto.
  Qed.

  Lemma is_empty_equal_empty: (is_empty s)=(equal s empty).
  Proof. 
  generalize empty_1 (@is_empty_1 s) (@is_empty_2 s) 
            (@equal_1 s empty) (@equal_2 s empty).
  unfold Empty, Equal.
  case (is_empty s); case (equal s empty); intuition.
  clear H3 H1.
  symmetry; apply H2; intuition.
  generalize (H4 a); intuition.
  generalize (H a); intuition.
  clear H1 H3.
  apply H0; intuition.
  generalize (H4 a); intuition.
  generalize (H a); intuition.
  Qed.
  
  Lemma choose_mem_1: (choose s)=(Some x) -> (mem x s)=true.
  Proof.  
  auto.
  Qed.

  Lemma choose_mem_2: (choose s)=None -> (is_empty s)=true.
  Proof.
  auto.
  Qed.

  Lemma add_mem_1: (mem x (add x s))=true.
  Proof.
  auto.
  Qed.  
 
  Lemma add_mem_2: 
  ~ (E.eq x y) -> (mem y (add x s))=(mem y s).
  Proof. 
  intros; apply bool_1; intuition; eauto.
  Qed.

  Lemma remove_mem_1: (mem x (remove x s))=false.
  Proof. 
  apply not_true_is_false; intro; absurd (In x (remove x s)); auto.
  Qed. 
 
  Lemma remove_mem_2: 
  ~ (E.eq x y) -> (mem y (remove x s))=(mem y s).
  Proof. 
  intros; apply bool_1; intuition; eauto. 
  Qed.

  Lemma singleton_equal_add: 
    (equal (singleton x) (add x empty))=true.
  Proof.
  apply equal_1; unfold Equal; intuition.
  apply In_1 with x; auto.
  assert (E.eq a x); auto.
  elim (ME.eq_dec a x); auto.
  intros; assert (In a empty). 
  eapply add_3; eauto.  
  generalize (empty_1 H0); intuition.
  Qed.  

  Lemma union_mem: 
    (mem x (union s s'))=(orb (mem x s) (mem x s')).
  Proof. 
  apply bool_1; intuition.
  elim (@union_1 s s' x); intuition.
  elim (orb_prop _ _ H); intuition.
  Qed.

  Lemma inter_mem: 
    (mem x (inter s s'))=(andb (mem x s) (mem x s')).
  Proof. 
  apply bool_1; intuition.
  apply andb_true_intro; intuition eauto.
  elim (andb_prop _ _ H); intuition.
  Qed.

  Lemma diff_mem: 
    (mem x (diff s s'))=(andb (mem x s) (negb (mem x s'))).
  Proof. 
  generalize (@diff_1 s s' x) (@diff_2 s s' x) (@diff_3 s s' x).
  set (s0 := diff s s').
  generalize (@mem_1 s x) (@mem_1 s' x) (@mem_1 s0 x) 
             (@mem_2 s x) (@mem_2 s' x) (@mem_2 s0 x).
  case (mem x s); case (mem x s'); case (mem x s0); intuition.
  Qed.

  Section fold. 

  Variable A:Set. 
  Variable eqA:A->A->Prop.
  Variable st:(Setoid_Theory _ eqA).
  Variable i:A.
  Variable f:elt->A->A.
  Variable Comp:(compat_op E.eq eqA f). 
  Variable Assoc:(transpose eqA f).
 
  Lemma fold_empty: (eqA (fold f empty i) i).
  Proof. 
  apply MP.fold_1; auto.
  Qed.

  Lemma fold_equal: 
    (equal s s')=true -> (eqA (fold f s i) (fold f s' i)).
  Proof. 
     pattern s; apply MP.set_induction; intros.
     apply (Seq_trans _ _ st) with i; auto.
     apply MP.fold_1; auto.
     apply Seq_sym; auto; apply MP.fold_1; auto.
     apply MP.cardinal_inv_1; rewrite <- (MP.Equal_cardinal (equal_2 H0)); auto.
     apply MP.empty_cardinal_2; auto.
     apply (Seq_trans _ _ st) with (f x0 (fold f s0 i)); auto.
     apply MP.fold_2 with (eqA:=eqA); auto.
     apply Seq_sym; auto; apply MP.fold_2 with (eqA := eqA); auto.
     generalize (equal_2 H2) H1; unfold MP.Add, Equal; intros;
       elim (H4 y0); elim (H3 y0); intuition.
  Qed.
   
  Lemma fold_add: 
    (mem x s)=false -> (eqA (fold f (add x s) i) (f x (fold f s i))).
  Proof. 
    intros; apply MP.fold_2 with (eqA:=eqA); auto.
    intro; rewrite mem_1 in H; auto; discriminate H. 
  Qed.

  End fold.

  Section Filter.
  
  Variable f:elt->bool.
  Variable Comp: (compat_bool E.eq f).

  Lemma filter_mem: (mem x (filter f s))=(andb (mem x s) (f x)).
  Proof. 
  apply bool_1; intuition.
  apply andb_true_intro; intuition; eauto.
  elim (andb_prop _ _ H); intuition. 
  Qed.

  Lemma for_all_filter: 
    (for_all f s)=(is_empty (filter (fun x => negb (f x)) s)).
  Proof. 
  assert (Comp' : compat_bool E.eq (fun x =>negb (f x))). 
    generalize Comp; unfold compat_bool; intros; apply (f_equal negb); auto. 
  apply bool_1; intuition. 
  apply is_empty_1.
  unfold Empty; intros. 
  intro.
  assert (In a s); eauto.
  generalize (filter_2 Comp' H0).
  generalize (for_all_2 Comp H H1); auto.
  intros Eq; rewrite Eq; intuition.
  apply for_all_1; unfold For_all; intros; auto. 
  apply bool_3.
  red; intros.
  elim (@is_empty_2 _ H x0); auto.
  Qed.

  Lemma exists_filter : 
    (exists_ f s)=(negb (is_empty (filter f s))).
  Proof. 
  apply bool_1; intuition. 
  elim (exists_2 Comp H); intuition.
  apply bool_6.
  red; intros; apply (@is_empty_2 _ H0 x0); auto.
  generalize (@choose_1 (filter f s)) (@choose_2 (filter f s)).
  case (choose (filter f s)).
  intros. 
  clear H1. 
  apply exists_1; auto.
  exists e; generalize (H0 e); intuition; eauto.
  intros. 
  clear H0.
  rewrite (@is_empty_1 (filter f s)) in H; auto.
  discriminate H.
  Qed.

  Lemma partition_filter_1: 
    (equal (fst (partition f s)) (filter f s))=true.
  Proof. 
  auto.
  Qed.

  Lemma partition_filter_2: 
    (equal (snd (partition f s)) (filter (fun x => negb (f x)) s))=true.
  Proof. 
  auto.
  Qed.

  End Filter.
  End Old_Spec_Now_Properties.

  Hint Immediate 
  empty_mem   
  is_empty_equal_empty 
  add_mem_1
  remove_mem_1
  singleton_equal_add
  union_mem
  inter_mem
  diff_mem 
  filter_mem
  for_all_filter
  exists_filter : set. 

  Hint Resolve 
  equal_mem_1
  subset_mem_1
  choose_mem_1
  choose_mem_2
  add_mem_2
  remove_mem_2 : set.

Section MoreProperties.

(** properties of [mem] *)

Lemma mem_3 : forall s x, ~(In x s) -> (mem x s)=false.
Proof.
intros s x.
generalize (@mem_1 s x) (@mem_2 s x); case (mem x s); intuition.
Qed.

Lemma mem_4 : forall s x, (mem x s)=false -> ~(In x s).
Proof.
intros s x.
generalize (@mem_1 s x) (@mem_2 s x); case (mem x s); intuition.
Qed.

(** Properties of [equal] *) 

Lemma equal_refl: forall s, (equal s s)=true.
Proof.
auto with set.
Qed.

Lemma equal_sym: forall s s', (equal s s')=(equal s' s).
Proof.
intros.
apply bool_eq_ind;intros.
rewrite equal_mem_1;auto.
symmetry;apply equal_mem_2;auto.
apply (bool_eq_ind (equal s s'));intros;auto.
rewrite equal_mem_1 in H;auto.
symmetry;apply equal_mem_2;auto.
Qed.

Lemma equal_trans: 
 forall s u v, (equal s u)=true -> (equal u v)=true -> (equal s v)=true.
Proof.
intros.
apply equal_mem_1;intros.
transitivity (mem a u);
firstorder with equal_mem_2.
Qed.

Lemma equal_equal: 
 forall s t_ u, (equal s t_)=true -> (equal s u)=(equal t_ u).
Proof.
intros.
apply bool_eq_ind;intros.
apply equal_trans with t_;auto with set.
symmetry; apply bool_eq_ind;intros;auto.
rewrite <- H0.
apply equal_trans with s;auto with set.
rewrite equal_sym;auto.
Qed.

Lemma equal_cardinal: 
 forall s s', (equal s s')=true -> (cardinal s)=(cardinal s').
Proof.
intros; apply MP.Equal_cardinal; auto.
Qed.

Hint Resolve equal_refl equal_cardinal equal_equal:set.
Hint Immediate equal_sym :set.

(* Properties of [subset] *)

Lemma subset_refl: forall s, (subset s s)=true. 
Proof.
auto with set.
Qed.

Lemma subset_antisym: 
 forall s s', (subset s s')=true -> (subset s' s)=true -> (equal s s')=true.
Proof.
intros;apply equal_mem_1;intros.
apply bool_eq_ind;intros.
eapply subset_mem_2;eauto.
apply (bool_eq_ind (mem a s));intros;auto.
rewrite <- (subset_mem_2 _ _ H _ H2);assumption.
Qed.

Lemma subset_trans: 
 forall s t_ u, (subset s t_)=true -> (subset t_ u)=true -> (subset s u)=true.
Proof.
intros.
apply subset_mem_1;intros.
apply subset_mem_2 with t_;intros;auto.
apply subset_mem_2 with s;auto.
Qed.

Lemma subset_equal: 
 forall s s', (equal s s')=true -> (subset s s')=true.
Proof.
intros.
apply subset_mem_1;intros.
rewrite <- (equal_mem_2 _ _ H);auto.
Qed.

Hint Resolve subset_refl subset_equal subset_antisym :set.

(** Properties of [choose] *)

Lemma choose_mem_3: 
 forall s, (is_empty s)=false -> {x:elt|(choose s)=(Some x)/\(mem x s)=true}.
Proof.
intros.
generalize (@choose_mem_1 s).
generalize (@choose_mem_2 s).
case (choose s);intros.
exists e;auto.
lapply H0;trivial;intros.
rewrite H in H2;discriminate H2.
Qed.

Lemma choose_mem_4: (choose empty)=None.
Proof.
generalize (@choose_mem_1 empty).
case (@choose empty);intros;auto.
absurd (true=false);auto with bool.
rewrite <- (H e);auto with set.
Qed.

(** Properties of [add] *)

Lemma add_mem_3: 
 forall s x y, (mem y s)=true -> (mem y (add x s))=true.
Proof.
auto.
Qed.

Lemma add_equal: 
 forall s x, (mem x s)=true -> (equal (add x s) s)=true.
Proof.
intros;apply equal_mem_1;intros.
elim (ME.eq_dec x a); intros; auto with set.
rewrite <- (mem_eq s x);auto.
rewrite <- (mem_eq (add x s) _ _ a0);auto.
rewrite H;auto with set.
Qed.

Hint Resolve add_mem_3 add_equal :set.

Lemma add_fold: 
 forall (A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory _ eqA))
 (f:elt->A->A)(i:A), (compat_op E.eq eqA f) -> (transpose eqA f) ->
 forall (s:t)(x:elt), (mem x s)=true -> (eqA (fold f (add x s) i) (fold f s i)).
Proof.
intros; apply fold_equal with (eqA:=eqA); auto with set.
Qed.

Lemma add_cardinal_1: 
 forall s x, (mem x s)=true -> (cardinal (add x s))=(cardinal s).
Proof.
auto with set.
Qed.

Lemma add_cardinal_2: 
 forall s x, (mem x s)=false -> (cardinal (add x s))=(S (cardinal s)).
Proof.
intros.
do 2 rewrite MP.cardinal_fold.
change S with ((fun _ =>S) x); apply fold_add with (eqA:=@eq nat); auto.
Qed.

(** Properties of [remove] *)

Lemma remove_mem_3: 
 forall s x y, (mem y (remove x s))=true -> (mem y s)=true.
Proof.
intros s x y;elim (ME.eq_dec x y); intro e.
rewrite <- mem_eq with (x:=x);auto.
rewrite <- (mem_eq s _ _ e);auto.
rewrite (remove_mem_1 s x);intro H;discriminate H.
intros;rewrite <- H;symmetry;auto with set.
Qed.

Lemma remove_equal: 
 forall s x,(mem x s)=false -> (equal (remove x s) s)=true.
Proof.
intros;apply equal_mem_1;intros.
elim (ME.eq_dec x a); intros;auto with set.
rewrite <- mem_eq with (x:=x);auto.
rewrite <- (mem_eq s _ _ a0);auto;rewrite H;auto with set.
Qed.

Hint Resolve remove_mem_3 remove_equal : set.

Lemma add_remove: 
 forall s x,(mem x s)=true -> (equal (add x (remove x s)) s)=true.
Proof.
intros;apply equal_mem_1;intros.
elim (ME.eq_dec x a); intros;auto with set.
rewrite <- mem_eq with (x:=x);auto.
rewrite <- (mem_eq s _ _ a0);auto;rewrite H;auto with set.
transitivity (mem a (remove x s));auto with set.
Qed.

Lemma remove_add: 
 forall s x,(mem x s)=false -> (equal (remove x (add x s)) s)=true.
Proof.
intros;apply equal_mem_1;intros.
elim (ME.eq_dec x a); intros;auto with set.
rewrite <- mem_eq with (x:=x);auto.
rewrite <- (mem_eq s _ _ a0);auto;rewrite H;auto with set.
transitivity (mem a (add x s));auto with set.
Qed.

Hint Immediate add_remove remove_add : set.

Lemma remove_fold_1: 
 forall (A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory _ eqA))
 (f:elt->A->A)(i:A), (compat_op E.eq eqA f) -> (transpose eqA f) ->
 forall s x,(mem x s)=true -> 
 (eqA (f x (fold f (remove x s) i)) (fold f s i)).
Proof.
intros.
apply Seq_sym; auto.
apply MP.fold_2 with (eqA:=eqA); auto.
Qed.

Lemma remove_fold_2: 
 forall (A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory _ eqA))
 (f:elt->A->A)(i:A), (compat_op E.eq eqA f) -> (transpose eqA f) ->
 forall s x,(mem x s)=false -> 
 (eqA (fold f (remove x s) i) (fold f s i)).
Proof.
intros.
apply fold_equal with (eqA:=eqA); auto with set.
Qed.

Lemma remove_cardinal_1: 
 forall s x,(mem x s)=true -> (S (cardinal (remove x s)))=(cardinal s).
Proof.
intros.
do 2 rewrite MP.cardinal_fold.
change S with ((fun _ =>S) x).
apply remove_fold_1 with (eqA:=@eq nat); auto.
Qed.

Lemma remove_cardinal_2: 
 forall s x,(mem x s)=false -> (cardinal (remove x s))=(cardinal s).
Proof.
auto with set.
Qed.

(** Properties of [is_empty] *)

Lemma is_empty_cardinal: forall s,(is_empty s)=(zerob (cardinal s)).
Proof.
intros.
apply (bool_eq_ind (is_empty s));intros.
rewrite (@equal_cardinal s empty).
rewrite MP.empty_cardinal;simpl;trivial.
rewrite <- H;symmetry;auto with set.
elim (choose_mem_3 _ H);intros.
elim p;intros.
rewrite <- (remove_cardinal_1 _ _ H1).
simpl;trivial.
Qed.

(** Properties of [singleton] *)

Lemma singleton_mem_1: forall x,(mem x (singleton x))=true.
Proof.
intros.
rewrite (equal_mem_2 _ _ (singleton_equal_add x));auto with set.
Qed.

Lemma singleton_mem_2: forall x y,~(E.eq x y) -> (mem y (singleton x))=false.
Proof.
intros.
rewrite (equal_mem_2 _ _ (singleton_equal_add x)).
rewrite <- (empty_mem y);auto with set.
Qed.

Lemma singleton_mem_3: forall x y, (mem y (singleton x))=true -> (E.eq x y).
Proof.
intros.
elim (ME.eq_dec x y);intros;auto.
Qed.

(* General recursion principes based on [cardinal] *)

Lemma cardinal_set_rec:  forall (P:t->Set),
 (forall s s',(equal s s')=true -> (P s) -> (P s')) -> 
 (forall s x,(mem x s)=false -> (P s) -> (P (add x s))) -> 
 (P empty) -> forall n s, (cardinal s)=n -> (P s).
Proof.
induction n; intro s; generalize (is_empty_cardinal s); 
  intros eq1 eq2; rewrite eq2 in eq1; simpl in eq1.
rewrite is_empty_equal_empty in eq1.
rewrite equal_sym in eq1.
apply (H empty s eq1);auto.
elim (choose_mem_3 _ eq1);intros;elim p;clear p;intros.
apply (H (add x (remove x s)) s);auto with set.
apply H0;auto with set.
apply IHn.
rewrite <- (remove_cardinal_1 _ _ H3) in eq2.
inversion eq2;trivial.
Qed.

Lemma set_rec:  forall (P:t->Set),
 (forall s s',(equal s s')=true -> (P s) -> (P s')) ->
 (forall s x,(mem x s)=false -> (P s) -> (P (add x s))) -> 
 (P empty) -> forall s, (P s).
Proof.
intros;eapply cardinal_set_rec;eauto.
Qed.

Lemma cardinal_set_ind:  forall (P:t->Prop),
 (forall s s',(equal s s')=true -> (P s) -> (P s')) -> 
 (forall s x,(mem x s)=false -> (P s) -> (P (add x s))) -> 
 (P empty) -> forall n s, (cardinal s)=n -> (P s).
Proof.
induction n; intro s; generalize (is_empty_cardinal s); 
  intros eq1 eq2; rewrite eq2 in eq1; simpl in eq1.
rewrite is_empty_equal_empty in eq1.
rewrite equal_sym in eq1.
apply (H empty s eq1);auto.
elim (choose_mem_3 _ eq1);intros;elim p;clear p;intros.
apply (H (add x (remove x s)) s);auto with set.
apply H0;auto with set.
apply IHn.
rewrite <- (remove_cardinal_1 _ _ H3) in eq2.
inversion eq2;trivial.
Qed.

Lemma set_ind:  forall (P:t->Prop),
 (forall s s',(equal s s')=true -> (P s) -> (P s')) ->
 (forall s x,(mem x s)=false -> (P s) -> (P (add x s))) -> 
 (P empty) -> forall s, (P s).
Proof.
intros;eapply cardinal_set_ind;eauto.
Qed.

(** Properties of [fold] *)

Lemma fold_commutes:
 forall (A:Set)(eqA:A->A->Prop)(st:(Setoid_Theory _ eqA))
 (f:elt->A->A)(i:A), (compat_op E.eq eqA f) -> (transpose eqA f) -> forall s x,
 (eqA (fold f s (f x i)) (f x (fold f s i))).
Proof.
intros; pattern s; apply set_ind.
intros.
apply (Seq_trans _ _ st) with (fold f s0 (f x i)).
apply fold_equal with (eqA:=eqA); auto with set.
rewrite equal_sym; auto.
apply (Seq_trans _ _ st) with (f x (fold f s0 i)); auto.
apply H; auto.
apply fold_equal with (eqA:=eqA); auto.
intros. 
apply (Seq_trans _ _ st) with (f x0 (fold f s0 (f x i))).
apply fold_add with (eqA:=eqA); auto.
apply (Seq_trans _ _ st) with (f x0 (f x (fold f s0 i))).
apply H; auto.
apply (Seq_trans _ _ st) with (f x (f x0 (fold f s0 i))).
apply H0; auto.
apply H; auto.
apply Seq_sym; auto.
apply fold_add with (eqA:=eqA); auto.
apply (Seq_trans _ _ st) with (f x i).
apply fold_empty; auto.
apply Seq_sym; auto.
apply H; auto.
apply fold_empty; auto.
Qed.

Lemma fold_plus: 
 forall s p, (fold (fun _ =>S) s p)=(fold (fun _ => S) s O)+p.
Proof.
assert (st := gen_st nat).
assert (fe : compat_op E.eq (@eq _) (fun _ =>S)). unfold compat_op; auto. 
assert (fp : transpose (@eq _) (fun _:E.t =>S)). unfold transpose;auto.
intros s p;pattern s;apply set_ind.
intros. change elt with E.t.
rewrite <- (fold_equal _ _ _ _ st p _ fe fp H).
rewrite <- (fold_equal _ _ _ _ st O _ fe fp H);assumption.
intros.
assert (forall p, fold (fun _ => S) (add x s0) p = S (fold (fun _ => S) s0 p)).
change S with ((fun _ => S) x). 
intros; apply fold_add with (eqA:=@eq nat); auto.
rewrite (H1 p).
rewrite (H1 O).
rewrite H0.
simpl; auto.
intros; do 2 rewrite (fold_empty _ _ st);auto.
Qed.

(** Properties of [union] *)

Lemma union_sym:
 forall s s',(equal (union s s') (union s' s))=true.
Proof.
intros;apply equal_mem_1;intros.
do 2 rewrite union_mem;auto with bool.
Qed.

Lemma union_subset_equal: 
 forall s s',(subset s s')=true->(equal (union s s') s')=true.
Proof.
intros;apply equal_mem_1;intros.
rewrite union_mem.
apply (bool_eq_ind (mem a s));intros;simpl;auto with set.
rewrite (subset_mem_2 _ _ H _ H0);auto.
Qed.

Lemma union_equal_1: 
 forall s s' s'', (equal s s')=true->
 (equal (union s s'') (union s' s''))=true.
Proof.
intros;apply equal_mem_1;intros.
do 2 (rewrite union_mem;idtac).
rewrite (equal_mem_2 _ _ H a);auto.
Qed.

Lemma union_equal_2: 
 forall s s' s'',(equal s' s'')=true->
 (equal (union s s') (union s s''))=true.
Proof.
intros;apply equal_mem_1;intros.
do 2 (rewrite union_mem;idtac).
rewrite (equal_mem_2 _ _ H a);auto.
Qed.

Lemma union_assoc: 
 forall s s' s'',
 (equal (union (union s s') s'') (union s (union s' s'')))=true.
Proof.
intros;apply equal_mem_1;intros.
do 4 rewrite union_mem.
rewrite orb_assoc;auto.
Qed.

Lemma add_union_singleton: 
 forall s x,(equal (add x s) (union (singleton x) s))=true.
Proof.
intros;apply equal_mem_1;intros.
rewrite union_mem.
elim (ME.eq_dec x a);intros.
rewrite <- (mem_eq (add x s) _ _ a0).
rewrite <- (mem_eq (singleton x) _ _ a0).
rewrite <- (mem_eq s _ _ a0).
rewrite add_mem_1;rewrite singleton_mem_1;simpl;auto.
rewrite singleton_mem_2;simpl;auto with set.
Qed.

Lemma union_add: 
 forall s s' x,
 (equal (union (add x s) s') (add x (union s s')))=true.
Proof.
intros;apply equal_trans with (union (union (singleton x) s) s').
apply union_equal_1;apply add_union_singleton.
apply equal_trans with (union (singleton x) (union s s')).
apply union_assoc.
rewrite equal_sym;apply add_union_singleton.
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
 forall s s' s'', (equal s s')=true->
 (equal (inter s s'') (inter s' s''))=true.
Proof.
intros;apply equal_mem_1;intros.
do 2 (rewrite inter_mem;idtac).
rewrite (equal_mem_2 _ _ H a);auto.
Qed.

Lemma inter_equal_2: 
 forall s s' s'',(equal s' s'')=true->
 (equal (inter s s') (inter s s''))=true.
Proof.
intros;apply equal_mem_1;intros.
do 2 (rewrite inter_mem;idtac).
rewrite (equal_mem_2 _ _ H a);auto.
Qed.

Lemma inter_assoc: 
 forall s s' s'',
 (equal (inter (inter s s') s'') (inter s (inter s' s'')))=true.
Proof.
intros;apply equal_mem_1;intros.
do 4 rewrite inter_mem.
rewrite andb_assoc;auto.
Qed.

Lemma union_inter_1: 
 forall s s' s'',
 (equal (inter (union s s') s'') (union (inter s s'') (inter s' s'')))=true.
Proof.
intros;apply equal_mem_1;intros.
rewrite union_mem.
do 3 rewrite inter_mem.
rewrite union_mem. 
apply demorgan2.
Qed.

Lemma union_inter_2: 
 forall s s' s'',
 (equal (union (inter s s') s'') (inter (union s s'') (union s' s'')))=true.
Proof.
intros;apply equal_mem_1;intros.
rewrite union_mem.
do 2 rewrite inter_mem.
do 2 rewrite union_mem. 
apply demorgan4.
Qed.

Lemma inter_add_1: 
 forall s s' x,(mem x s')=true -> 
 (equal (inter (add x s) s') (add x (inter s s')))=true.
Proof.
intros;apply equal_trans with (inter (union (singleton x) s) s').
apply inter_equal_1;apply add_union_singleton.
apply equal_trans with (union (inter (singleton x) s') (inter s s')).
apply union_inter_1.
apply equal_trans with (union (singleton x) (inter s s')).
apply union_equal_1.
apply inter_subset_equal.
apply subset_mem_1;intros.
rewrite <- (mem_eq s' _ _ (singleton_mem_3 _ _ H0));auto.
rewrite equal_sym;apply add_union_singleton.
Qed.

Lemma inter_add_2: 
 forall s s' x, (mem x s')=false -> 
 (equal (inter (add x s) s') (inter s s'))=true.
Proof.
intros;apply equal_trans with (inter (union (singleton x) s) s').
apply inter_equal_1;apply add_union_singleton.
apply equal_trans with (union (inter (singleton x) s') (inter s s')).
apply union_inter_1.
apply union_subset_equal.
apply subset_mem_1;intros.
rewrite inter_mem in H0.
elim (andb_prop _ _ H0);intros.
absurd (mem a s' = true);auto.
rewrite <- (mem_eq s' _ _ (singleton_mem_3 _ _ H1));auto.
rewrite H;auto with bool.
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

Lemma fold_union_inter: 
 forall (A:Set)(f:elt->A->A)(i:A), 
 (compat_op E.eq (@eq _) f) -> (transpose (@eq _) f) -> 
 forall s s',(fold f (union s s') (fold f (inter s s') i))
  = (fold f s (fold f s' i)).
Proof.
intro A.
set (st := gen_st A).
intros;pattern s;apply set_ind.
intros; rewrite <- (fold_equal _ _ _ _ st i _ H H0 (inter_equal_1 _ _ s' H1)).
rewrite <- (fold_equal _ _ _ _ st (fold f s' i) _ H H0 H1).
rewrite <- (fold_equal _ _ _ _ st (fold f (inter s0 s') i) _ H H0 (union_equal_1 _ _ s' H1));auto.
intros.
rewrite 
 (fold_equal _ _ _ _ st (fold f (inter (add x s0) s') i) _ H H0 (union_add s0 s' x)).
generalize (refl_equal (mem x s')); pattern (mem x s') at -1; case (mem x s');intros.
rewrite (fold_equal _ _ _ _ st i _ H H0 (inter_add_1 s0 _ _ H3)).
cut (mem x (inter s0 s') = false);intros.
cut (mem x (union s0 s') = true);intros.
rewrite (fold_add _ _ _ _ st i _ H H0 H4).
rewrite (fold_commutes _ _ st);auto.
rewrite (fold_equal _ _ _ _ st (fold f (inter s0 s') i) _ H H0 (add_equal _ _ H5)).
rewrite (fold_add _ _ _ _ st (fold f s' i) _ H H0 H1).
rewrite H2;auto.
rewrite union_mem;rewrite H3;apply orb_b_true.
rewrite inter_mem;rewrite H1;simpl;auto.
rewrite (fold_equal _ _ _ _ st i _ H H0 (inter_add_2 s0 _ _ H3)).
cut (mem x (union s0 s') = false);intros.
rewrite (fold_add _ _ _ _ st (fold f (inter s0 s') i) _ H H0 H4).
rewrite (fold_add _ _ _ _ st (fold f s' i) _ H H0 H1).
rewrite H2;auto.
rewrite union_mem;rewrite H3; rewrite H1;auto.
cut (subset empty s' = true);intros.
rewrite (fold_equal _ _ _ _ st i _ H H0 (inter_subset_equal _ _ H1)).
do 2 rewrite (fold_empty _ _ st);apply fold_equal with (eqA:=@eq A);auto.
apply union_subset_equal;auto.
apply subset_mem_1;intros.
rewrite empty_mem in H1;absurd (true=false);auto with bool.
Qed.

Lemma union_inter_cardinal: 
 forall s s',(cardinal (union s s'))+(cardinal (inter s s'))
  = (cardinal s)+(cardinal s').
Proof.
intros.
do 4 rewrite MP.cardinal_fold.
do 2 rewrite <- fold_plus.
apply fold_union_inter;auto.
Qed.

Lemma fold_union: 
 forall (A:Set)(f:elt->A->A)(i:A), (compat_op E.eq (@eq A) f) -> (transpose (@eq A) f) -> 
 forall s s',(forall x, (andb (mem x s) (mem x s'))=false) -> 
 (fold f (union s s') i)=(fold f s (fold f s' i)).
Proof.
intros.
assert (st:= gen_st A).
rewrite <- (fold_union_inter _ _ i H H0 s s').
cut (equal (inter s s') empty = true);intros.
rewrite (fold_equal _ _ _ _ st i _ H H0 H2). 
rewrite (fold_empty _ _ st);auto.
apply equal_mem_1;intros.
rewrite inter_mem; rewrite empty_mem;auto.
Qed.

Lemma union_cardinal: 
 forall s s',(forall x, (andb (mem x s) (mem x s'))=false) -> 
 (cardinal (union s s'))=(cardinal s)+(cardinal s').
Proof.
intros.
do 3 rewrite MP.cardinal_fold.
rewrite fold_union;auto.
apply fold_plus;auto.
Qed.

(** Properties of [diff] *)

Lemma diff_subset: 
 forall s s',(subset (diff s s') s)=true.
Proof.
intros.
apply subset_mem_1;intros.
rewrite diff_mem in H.
elim (andb_prop _ _ H);auto.
Qed.

Lemma diff_subset_equal:
 forall s s',(subset s s')=true->(equal (diff s s') empty)=true.
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
 forall s x,(equal (remove x s) (diff s (singleton x)))=true.
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
 forall s s',(equal (inter (diff s s') (inter s s')) empty)=true. 
Proof.
intros;apply equal_mem_1;intros.
rewrite empty_mem;do 2 rewrite inter_mem;rewrite diff_mem.
case (mem a s);case (mem a s');simpl;auto.
Qed.

Lemma diff_inter_all: 
forall s s',(equal (union (diff s s') (inter s s')) s)=true.
Proof.
intros;apply equal_mem_1;intros.
rewrite union_mem;rewrite inter_mem;rewrite diff_mem.
case (mem a s);case (mem a s');simpl;auto.
Qed.

Lemma fold_diff_inter: 
 forall (A:Set)(f:elt->A->A)(i:A), (compat_op E.eq (@eq A) f) -> (transpose (@eq A) f) ->
 forall s s',(fold f (diff s s') (fold f (inter s s') i))=(fold f s i).
Proof.
intros.
assert (st := gen_st A).
rewrite <- (fold_union_inter _ _ i H H0 (diff s s') (inter s s')).
rewrite (fold_equal _ _ _ _ st i _ H H0 (diff_inter_empty s s')).
rewrite (fold_empty _ _ st).
apply fold_equal with (eqA:=@eq A);auto.
apply diff_inter_all.
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
 forall s s',(subset s s')=true -> (le (cardinal s) (cardinal s')).
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
intros s;pattern s; apply set_ind.
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
intros s;pattern s; apply set_ind.
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
intro s; pattern s; apply set_ind; intros.
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
