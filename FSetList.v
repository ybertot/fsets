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

(** This file proposes an implementation of the non-dependant 
    interface [FSetInterface.S] using strictly ordered list. *)

Require Export FSetInterface.

Set Implicit Arguments.
Unset Strict Implicit.

(** Usual syntax for lists. *)
Notation "[]" := nil (at level 0).


(** * Functions over lists

   First, we provide sets as lists which are not necessarily sorted.
   The specs are proved under the additional condition of being sorted. 
   And the functions returning sets are proved to preserve this invariant. *)

Module Raw (X: OrderedType).
 
  Module E := X.
  Module ME := OrderedTypeFacts X.

  Definition elt := E.t.
  Definition t := list elt.

  Definition empty : t := [].

  Definition is_empty (l : t) : bool := if l then true else false.

  (** ** The set operations. *)

  Fixpoint mem (x : elt) (s : t) {struct s} : bool :=
    match s with
    | [] => false
    | y :: l =>
        match E.compare x y with
        | FSetInterface.Lt _ => false
        | FSetInterface.Eq _ => true
        | FSetInterface.Gt _ => mem x l
        end
    end.

  Fixpoint add (x : elt) (s : t) {struct s} : t :=
    match s with
    | [] => x :: []
    | y :: l =>
        match E.compare x y with
        | FSetInterface.Lt _ => x :: s
        | FSetInterface.Eq _ => s
        | FSetInterface.Gt _ => y :: add x l
        end
    end.

  Definition singleton (x : elt) : t := x :: []. 

  Fixpoint remove (x : elt) (s : t) {struct s} : t :=
    match s with
    | [] => []
    | y :: l =>
        match E.compare x y with
        | FSetInterface.Lt _ => s
        | FSetInterface.Eq _ => l
        | FSetInterface.Gt _ => y :: remove x l
        end
    end.  
  
  Fixpoint union (s : t) : t -> t :=
    match s with
    | [] => fun s' => s'
    | x :: l =>
        (fix union_aux (s' : t) : t :=
           match s' with
           | [] => s
           | x' :: l' =>
               match E.compare x x' with
               | FSetInterface.Lt _ => x :: union l s'
               | FSetInterface.Eq _ => x :: union l l'
               | FSetInterface.Gt _ => x' :: union_aux l'
               end
           end)
    end.      

  Fixpoint inter (s : t) : t -> t :=
    match s with
    | [] => fun _ => []
    | x :: l =>
        (fix inter_aux (s' : t) : t :=
           match s' with
           | [] => []
           | x' :: l' =>
               match E.compare x x' with
               | FSetInterface.Lt _ => inter l s'
               | FSetInterface.Eq _ => x :: inter l l'
               | FSetInterface.Gt _ => inter_aux l'
               end
           end)
    end.  
  
  Fixpoint diff (s : t) : t -> t :=
    match s with
    | [] => fun _ => []
    | x :: l =>
        (fix diff_aux (s' : t) : t :=
           match s' with
           | [] => s
           | x' :: l' =>
               match E.compare x x' with
               | FSetInterface.Lt _ => x :: diff l s'
               | FSetInterface.Eq _ => diff l l'
               | FSetInterface.Gt _ => diff_aux l'
               end
           end)
    end.  
   
  Fixpoint equal (s : t) : t -> bool :=
    fun s' : t =>
    match s, s' with
    | [], [] => true
    | x :: l, x' :: l' =>
        match E.compare x x' with
        | FSetInterface.Eq _ => equal l l'
        | _ => false
        end
    | _, _ => false
    end.

  Fixpoint subset (s s' : t) {struct s'} : bool :=
    match s, s' with
    | [], _ => true
    | x :: l, x' :: l' =>
        match E.compare x x' with
        | FSetInterface.Lt _ => false
        | FSetInterface.Eq _ => subset l l'
        | FSetInterface.Gt _ => subset s l'
        end
    | _, _ => false
    end.

  Fixpoint fold (B : Set) (f : elt -> B -> B) (s : t) {struct s} : 
   B -> B := fun i => match s with
                      | [] => i
                      | x :: l => f x (fold f l i)
                      end.  

  Fixpoint filter (f : elt -> bool) (s : t) {struct s} : t :=
    match s with
    | [] => []
    | x :: l => if f x then x :: filter f l else filter f l
    end.  

  Fixpoint for_all (f : elt -> bool) (s : t) {struct s} : bool :=
    match s with
    | [] => true
    | x :: l => if f x then for_all f l else false
    end.  
 
  Fixpoint exists_ (f : elt -> bool) (s : t) {struct s} : bool :=
    match s with
    | [] => false
    | x :: l => if f x then true else exists_ f l
    end.

  Fixpoint partition (f : elt -> bool) (s : t) {struct s} : 
   t * t :=
    match s with
    | [] => ([], [])
    | x :: l =>
        let (s1, s2) := partition f l in
        if f x then (x :: s1, s2) else (s1, x :: s2)
    end.

  Definition cardinal (s : t) : nat := fold (fun _ => S) s 0.

  Definition elements (x : t) : list elt := x.

  Definition min_elt (s : t) : option elt :=
    match s with
    | [] => None
    | x :: _ => Some x
    end.

  Fixpoint max_elt (s : t) : option elt :=
    match s with
    | [] => None
    | x :: [] => Some x
    | _ :: l => max_elt l
    end.

  Definition choose := min_elt.

  (** ** Proofs of set operation specifications. *)

  Definition In : elt -> t -> Prop := InList E.eq.

  Notation Sort := (sort E.lt).
  Notation Inf := (lelistA E.lt).
  Notation "'In' x l" := (InList E.eq x l) (at level 10, x, l at next level).

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Add (x : elt) (s s' : t) :=
    forall y : elt, In y s' <-> E.eq y x \/ In y s.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) (s : t) :=
    forall x : elt, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s : t) :=
    exists x : elt, In x s /\ P x.

  Definition In_eq :
    forall (s : t) (x y : elt), E.eq x y -> In x s -> In y s := ME.In_eq.
  Definition Inf_lt :
    forall (s : t) (x y : elt), E.lt x y -> Inf y s -> Inf x s := ME.Inf_lt.
  Definition Inf_eq :
    forall (s : t) (x y : elt), E.eq x y -> Inf y s -> Inf x s := ME.Inf_eq.
  Definition In_sort :
    forall (s : t) (x a : elt), Inf a s -> In x s -> Sort s -> E.lt a x :=
    ME.In_sort.
  Hint Resolve Inf_lt Inf_eq. 
  Hint Immediate In_eq.

  Lemma mem_1 :
   forall (s : t) (Hs : Sort s) (x : elt), In x s -> mem x s = true. 
  Proof.
  simple induction s; intros.
  inversion H.
  inversion_clear Hs.
  inversion_clear H0.
  simpl in |- *; replace E.compare with X.compare; auto.
  elim (ME.elim_compare_eq (x:=x) (y:=a));
   [ intros A B; rewrite B; auto | auto ].
  simpl in |- *; replace E.compare with X.compare; auto.
  elim (ME.elim_compare_gt (x:=x) (y:=a));
   [ intros A B; rewrite B; auto | auto ].
  eapply In_sort; eauto.
  Qed.

  Lemma mem_2 : forall (s : t) (x : elt), mem x s = true -> In x s.
  Proof.
  simple induction s. 
  intros; inversion H.
  intros a l Hrec x.
  simpl in |- *; elim (E.compare x a); firstorder.
  inversion H.
  Qed.

  Lemma add_Inf :
   forall (s : t) (x a : elt), Inf a s -> E.lt a x -> Inf a (add x s).
  Proof.
  simple induction s.  
  simpl in |- *; intuition.
  simpl in |- *; intros; case (E.compare x a); intuition; inversion H0;
   intuition.
  Qed.
  Hint Resolve add_Inf.
  
  Lemma add_sort : forall (s : t) (Hs : Sort s) (x : elt), Sort (add x s).
  Proof.
  simple induction s.
  simpl in |- *; intuition.
  simpl in |- *; intros; case (E.compare x a); intuition; inversion_clear Hs;
   auto.
  Qed. 

  Lemma add_1 :
   forall (s : t) (Hs : Sort s) (x y : elt), E.eq y x -> In y (add x s).
  Proof.
  simple induction s. 
  simpl in |- *; intuition.
  simpl in |- *; intros; case (E.compare x a); intuition; inversion_clear Hs;
   firstorder.
  eauto.
  Qed.

  Lemma add_2 :
   forall (s : t) (Hs : Sort s) (x y : elt), In y s -> In y (add x s).
  Proof.
  simple induction s. 
  simpl in |- *; intuition.
  simpl in |- *; intros; case (E.compare x a); intuition.
  inversion_clear Hs; inversion_clear H0; eauto.
  Qed.

  Lemma add_3 :
   forall (s : t) (Hs : Sort s) (x y : elt),
   ~ E.eq x y -> In y (add x s) -> In y s.
  Proof.
  simple induction s. 
  simpl in |- *; intuition.
  inversion_clear H0; firstorder; absurd (E.eq x y); auto.
  simpl in |- *; intros a l Hrec Hs x y; case (E.compare x a); intros;
   inversion_clear H0; inversion_clear Hs; firstorder; 
   absurd (E.eq x y); auto.
  Qed.

  Lemma remove_Inf :
   forall (s : t) (Hs : Sort s) (x a : elt), Inf a s -> Inf a (remove x s).
  Proof.
  simple induction s.  
  simpl in |- *; intuition.
  simpl in |- *; intros; case (E.compare x a); intuition; inversion_clear H0;
   firstorder.
  inversion_clear Hs; firstorder; eauto.
  Qed.
  Hint Resolve remove_Inf.

  Lemma remove_sort :
   forall (s : t) (Hs : Sort s) (x : elt), Sort (remove x s).
  Proof.
  simple induction s.
  simpl in |- *; intuition.
  simpl in |- *; intros; case (E.compare x a); intuition; inversion_clear Hs;
   auto.
  Qed. 

  Lemma remove_1 :
   forall (s : t) (Hs : Sort s) (x y : elt), E.eq y x -> ~ In y (remove x s).
  Proof.
  simple induction s. 
  simpl in |- *; red in |- *; intros; inversion H0.
  simpl in |- *; intros; case (E.compare x a); intuition; inversion_clear Hs. 
  inversion_clear H1.
  absurd (E.eq x a); eauto. 
  absurd (E.lt a x); auto; eapply In_sort; eauto.
  absurd (E.lt a x); auto; eapply In_sort; eauto.
  inversion_clear H1; firstorder. 
  absurd (E.eq x a); eauto.
  Qed.

  Lemma remove_2 :
   forall (s : t) (Hs : Sort s) (x y : elt),
   ~ E.eq x y -> In y s -> In y (remove x s).
  Proof.
  simple induction s. 
  simpl in |- *; intuition.
  simpl in |- *; intros; case (E.compare x a); intuition; inversion_clear Hs;
   inversion_clear H1; auto. 
  absurd (E.eq x y); eauto. 
  Qed.

  Lemma remove_3 :
   forall (s : t) (Hs : Sort s) (x y : elt), In y (remove x s) -> In y s.
  Proof.
  simple induction s. 
  simpl in |- *; intuition.
  simpl in |- *; intros a l Hrec Hs x y; case (E.compare x a); intuition.
  inversion_clear Hs; inversion_clear H; firstorder.
  Qed.
  
  Lemma singleton_sort : forall x : elt, Sort (singleton x).
  Proof.
  unfold singleton in |- *; simpl in |- *; firstorder.
  Qed.

  Lemma singleton_1 : forall x y : elt, In y (singleton x) -> E.eq x y.
  Proof.
  unfold singleton in |- *; simpl in |- *; intuition.
  inversion_clear H; auto; inversion H0.
  Qed. 

  Lemma singleton_2 : forall x y : elt, E.eq x y -> In y (singleton x).
  Proof.
  unfold singleton in |- *; simpl in |- *; intuition.
  Qed. 

  Ltac DoubleInd :=
    simple induction s;
     [ simpl in |- *; auto; try solve [ intros; inversion H ]
     | intros x l Hrec; simple induction s';
        [ simpl in |- *; auto; try solve [ intros; inversion H ]
        | intros x' l' Hrec' Hs Hs'; inversion Hs; inversion Hs'; subst;
           simpl in |- * ] ].

  Lemma union_Inf :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (a : elt),
   Inf a s -> Inf a s' -> Inf a (union s s').
  Proof.
  DoubleInd.
  intros i His His'; inversion_clear His; inversion_clear His'.
  case (E.compare x x'); firstorder.
  Qed.
  Hint Resolve union_Inf.
 
  Lemma union_sort :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Sort (union s s').
  Proof.
  DoubleInd; case (E.compare x x'); intuition; constructor; auto.
  eauto.
  change (Inf x' (union (x :: l) l')) in |- *; firstorder.
  Qed.  
  
  Lemma union_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (union s s') -> In x s \/ In x s'.
  Proof.
  DoubleInd; case (E.compare x x'); intuition; inversion_clear H; intuition.
  elim (Hrec (x' :: l') H1 Hs' x0); intuition.
  elim (Hrec l' H1 H5 x0); intuition.
  elim (H0 x0); intuition.
  Qed.

  Lemma union_2 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x s -> In x (union s s').
  Proof.
  DoubleInd.
  intros i Hi; case (E.compare x x'); intuition; inversion_clear Hi; auto.
  Qed.

  Lemma union_3 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x s' -> In x (union s s').
  Proof.
  DoubleInd. 
  intros i Hi; case (E.compare x x'); inversion_clear Hi; intuition; eauto.
  Qed.
    
  Lemma inter_Inf :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (a : elt),
   Inf a s -> Inf a s' -> Inf a (inter s s').
  Proof.
  DoubleInd.
  intros i His His'; inversion His; inversion His'; subst.
  case (E.compare x x'); intuition; eauto.
  Qed.
  Hint Resolve inter_Inf. 

  Lemma inter_sort :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Sort (inter s s').
  Proof.
  DoubleInd; case (E.compare x x'); eauto.
  Qed.  
  
  Lemma inter_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (inter s s') -> In x s.
  Proof.
  DoubleInd; case (E.compare x x'); intuition.
  eauto. 
  inversion_clear H; eauto.
  Qed.

  Lemma inter_2 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (inter s s') -> In x s'.
  Proof.
  DoubleInd; case (E.compare x x'); intuition; inversion_clear H; eauto. 
  Qed.

  Lemma inter_3 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x s -> In x s' -> In x (inter s s').
  Proof.
  DoubleInd.
  intros i His His'; elim (E.compare x x'); intuition.

  inversion_clear His. 
  absurd (E.lt i x); eauto.
  apply In_sort with (x' :: l'); auto.
  constructor; eapply ME.eq_lt; eauto.
  eapply In_eq; eauto.
  eapply In_eq; eauto.

  inversion_clear His; [ eauto | inversion_clear His' ]; eauto.

  change (In i (inter (x :: l) l')) in |- *. 
  inversion_clear His'.
  absurd (E.lt i x'); eauto.
  apply In_sort with (x :: l); auto. 
  constructor; eapply ME.eq_lt; eauto.
  eapply In_eq; eauto.
  eapply In_eq; eauto.
  Qed.

  Lemma diff_Inf :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (a : elt),
   Inf a s -> Inf a s' -> Inf a (diff s s').
  Proof.
  DoubleInd.
  intros i His His'; inversion His; inversion His'.
  case (E.compare x x'); intuition; eauto.
  Qed.
  Hint Resolve diff_Inf. 

  Lemma diff_sort :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Sort (diff s s').
  Proof.
  DoubleInd; case (E.compare x x'); eauto.
  Qed.  
  
  Lemma diff_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (diff s s') -> In x s.
  Proof.
  DoubleInd; case (E.compare x x'); intuition.
  inversion_clear H; eauto.
  eauto.
  Qed.

  Lemma diff_2 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x (diff s s') -> ~ In x s'.
  Proof.
  DoubleInd.
  intros; intro Abs; inversion Abs. 
  case (E.compare x x'); intuition.

  inversion_clear H.
  absurd (E.lt x x); eauto. 
  apply In_sort with (x' :: l'); auto. 
  eapply In_eq; eauto.
  eauto.
  
  inversion_clear H3.
  generalize (diff_1 H1 H5 H); intros. 
  absurd (E.lt x x0); eauto.
  apply In_sort with l; eauto.
  eauto.
  
  inversion_clear H3. 
  generalize (diff_1 Hs H5 H); intros. 
  absurd (E.lt x' x'); eauto.
  apply In_sort with (x :: l); auto.
  eapply In_eq; eauto.
  eauto.  
  Qed.

  Lemma diff_3 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s') (x : elt),
   In x s -> ~ In x s' -> In x (diff s s').
  Proof.
  DoubleInd.
  intros i His His'; elim (E.compare x x'); intuition; inversion_clear His.
  eauto.
  eauto.
  elim His'; eauto.
  eauto.
  Qed.  

  Lemma equal_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'),
   Equal s s' -> equal s s' = true.
  Proof.
  simple induction s; unfold Equal in |- *.
  intro s'; case s'; auto.
  simpl in |- *; intuition.
  elim (H e); intros; assert (A : In e []); auto; inversion A.
  intros x l Hrec s'.
  case s'.
  intros; elim (H x); intros; assert (A : In x []); auto; inversion A.
  intros x' l' Hs Hs'; inversion Hs; inversion Hs'; subst.
  simpl in |- *; case (E.compare x); intros; auto.

  elim (H x); intros.
  assert (A : In x (x' :: l')); auto; inversion_clear A.
  absurd (E.eq x x'); eauto.
  absurd (E.lt x' x); auto.
  apply In_sort with l'; eauto.
  
  apply Hrec; intuition; elim (H a); intros.
  assert (A : In a (x' :: l')); auto; inversion_clear A; auto.
  absurd (E.lt x' x); auto. 
  apply In_sort with l; auto;
   [ apply Inf_eq with x; auto | apply In_eq with a; eauto ].
  assert (A : In a (x :: l)); auto; inversion_clear A; auto.
  absurd (E.lt x x'); auto. 
  apply In_sort with l'; auto;
   [ apply Inf_eq with x'; auto | apply In_eq with a; eauto ].

  elim (H x'); intros.
  assert (A : In x' (x :: l)); auto; inversion_clear A.
  absurd (E.eq x' x); eauto.
  absurd (E.lt x x'); auto.
  apply In_sort with l; eauto.
  Qed.

  Lemma equal_2 : forall s s' : t, equal s s' = true -> Equal s s'.
  Proof.
  simple induction s; unfold Equal in |- *.
  intro s'; case s'; intros.
  intuition.
  simpl in H; discriminate H.
  intros x l Hrec s'.
  case s'.
  intros; simpl in H; discriminate H.
  intros x' l'; simpl in |- *; case (E.compare x); intros; auto.
  discriminate H.
  elim (Hrec l' H a); intuition; inversion_clear H2; eauto.
  discriminate H.  
  Qed.  
  
  Lemma subset_1 :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'),
   Subset s s' -> subset s s' = true.
  Proof.
  intros s s'; generalize s' s; clear s s'.
  simple induction s'; unfold Subset in |- *.
  intro s; case s; auto.
  intros; elim (H e); intros; assert (A : In e []); auto; inversion A. 
  intros x' l' Hrec s; case s.
  simpl in |- *; auto.
  intros x l Hs Hs'; inversion Hs; inversion Hs'; subst.
  simpl in |- *; case (E.compare x); intros; auto.

  assert (A : In x (x' :: l')); auto; inversion_clear A.
  absurd (E.eq x x'); eauto.
  absurd (E.lt x' x); auto.
  apply In_sort with l'; eauto.
  
  apply Hrec; intuition.
  assert (A : In a (x' :: l')); auto; inversion_clear A; auto.
  absurd (E.lt x' x); auto. 
  apply In_sort with l; auto;
   [ apply Inf_eq with x; auto | apply In_eq with a; eauto ].

  apply Hrec; intuition.
  assert (A : In a (x' :: l')); auto; inversion_clear A; auto.
  inversion_clear H0.  
  absurd (E.lt x' x); eauto.
  absurd (E.lt x x'); auto. 
  apply In_sort with l; eauto.
  Qed.

  Lemma subset_2 : forall s s' : t, subset s s' = true -> Subset s s'.
  Proof.
  intros s s'; generalize s' s; clear s s'.
  simple induction s'; unfold Subset in |- *.
  intro s; case s; auto.
  simpl in |- *; intros; discriminate H.
  intros x' l' Hrec s; case s.
  intros; inversion H0.
  intros x l; simpl in |- *; case (E.compare x); intros; auto.
  discriminate H.  
  inversion_clear H0; eauto.
  eauto.
  Qed.  
  
  Lemma empty_sort : Sort empty.
  Proof.
  unfold empty in |- *; constructor.
  Qed.

  Lemma empty_1 : Empty empty.
  Proof.
  unfold Empty, empty in |- *; intuition; inversion H.
  Qed. 

  Lemma is_empty_1 : forall s : t, Empty s -> is_empty s = true.
  Proof.
  unfold Empty in |- *; intro s; case s; simpl in |- *; intuition.
  elim (H e); auto.
  Qed.
  
  Lemma is_empty_2 : forall s : t, is_empty s = true -> Empty s. 
  Proof.
  unfold Empty in |- *; intro s; case s; simpl in |- *; intuition;
   inversion H0.
  Qed.

  Lemma elements_1 : forall (s : t) (x : elt), In x s -> In x (elements s).
  Proof.
  unfold elements in |- *; auto.
  Qed.

  Lemma elements_2 : forall (s : t) (x : elt), In x (elements s) -> In x s.
  Proof. 
  unfold elements in |- *; auto.
  Qed.
 
  Lemma elements_3 : forall (s : t) (Hs : Sort s), Sort (elements s).  
  Proof. 
  unfold elements in |- *; auto.
  Qed.

  Lemma min_elt_1 : forall (s : t) (x : elt), min_elt s = Some x -> In x s. 
  Proof.
  intro s; case s; simpl in |- *; intros; inversion H; auto.
  Qed.  

  Lemma min_elt_2 :
   forall (s : t) (Hs : Sort s) (x y : elt),
   min_elt s = Some x -> In y s -> ~ E.lt y x. 
  Proof.
  simple induction s; simpl in |- *.
  intros; inversion H.
  intros a l; case l; intros; inversion H0; inversion_clear H1; subst. 
  eauto.
  inversion H2.
  eauto.
  inversion_clear Hs.
  inversion_clear H3.
  intro; absurd (E.lt y e); eauto.
  Qed. 

  Lemma min_elt_3 : forall s : t, min_elt s = None -> Empty s.
  Proof.
  unfold Empty in |- *; intro s; case s; simpl in |- *; intuition;
   inversion H; inversion H0.
  Qed.

  Lemma max_elt_1 : forall (s : t) (x : elt), max_elt s = Some x -> In x s. 
  Proof. 
  simple induction s; simpl in |- *.
  intros; inversion H.
  intros x l; case l; simpl in |- *.
  intuition.
  inversion H0; auto.
  eauto.
  Qed.
 
  Lemma max_elt_2 :
   forall (s : t) (Hs : Sort s) (x y : elt),
   max_elt s = Some x -> In y s -> ~ E.lt x y. 
  Proof.
  simple induction s; simpl in |- *.
  intros; inversion H.
  intros x l; case l; simpl in |- *.
  intuition.
  inversion H0; subst.
  inversion_clear H1.
  absurd (E.eq y x0); auto. 
  inversion H3.
  intros; inversion_clear Hs; inversion_clear H3; inversion_clear H1.
  assert (~ E.lt x0 e).
   eapply H; eauto.
  intro.
  elim H1; apply E.lt_trans with x; auto; eapply ME.lt_eq; eauto.
  eapply H; eauto.
  Qed. 

  Lemma max_elt_3 : forall s : t, max_elt s = None -> Empty s.
  Proof.
  unfold Empty in |- *; simple induction s; simpl in |- *.
  red in |- *; intros; inversion H0.
  intros x l; case l; simpl in |- *; intros.
  inversion H0.
  elim (H H0 e); auto.
  Qed.

  Definition choose_1 :
    forall (s : t) (x : elt), choose s = Some x -> In x s := min_elt_1.

  Definition choose_2 : forall s : t, choose s = None -> Empty s := min_elt_3.

  Lemma fold_1 :
   forall (s : t) (Hs : Sort s) (A : Set) (i : A) (f : elt -> A -> A),
   exists l : list elt,
     Unique E.eq l /\
     (forall x : elt, In x s <-> In x l) /\ fold f s i = fold_right f i l.
  Proof.
  intros; exists s; split; intuition.
  apply ME.Sort_Unique; auto.
  induction  s as [| a s Hrecs]; simpl in |- *; trivial.
  rewrite Hrecs; trivial.
  inversion_clear Hs; trivial.
  Qed.

  Lemma cardinal_1 :
   forall (s : t) (Hs : Sort s),
   exists l : list elt,
     Unique E.eq l /\
     (forall x : elt, In x s <-> In x l) /\ cardinal s = length l.
  Proof.
  intros; exists s; split; intuition.
  apply ME.Sort_Unique; auto.  
  unfold cardinal in |- *; induction  s as [| a s Hrecs]; simpl in |- *;
   trivial.
  rewrite Hrecs; trivial.
  inversion_clear Hs; trivial.
  Qed.

  Lemma filter_Inf :
   forall (s : t) (Hs : Sort s) (x : elt) (f : elt -> bool),
   Inf x s -> Inf x (filter f s).
  Proof.
  simple induction s; simpl in |- *.
  intuition.  
  intros x l Hrec Hs a f Ha; inversion_clear Hs; inversion Ha.
  case (f x); [ constructor; auto | eauto ]. 
  Qed.

  Lemma filter_sort :
   forall (s : t) (Hs : Sort s) (f : elt -> bool), Sort (filter f s).
  Proof.
  simple induction s; simpl in |- *.
  auto.
  intros x l Hrec Hs f; inversion_clear Hs.
  case (f x); auto.
  constructor; auto.
  apply filter_Inf; auto. 
  Qed.

  Lemma filter_1 :
   forall (s : t) (x : elt) (f : elt -> bool),
   compat_bool E.eq f -> In x (filter f s) -> In x s.
  Proof.
  simple induction s; simpl in |- *.
  intros; inversion H0.
  intros x l Hrec a f Hf.
  case (f x); simpl in |- *; firstorder.
  inversion H; firstorder.
  Qed.

   Lemma filter_2 :
    forall (s : t) (x : elt) (f : elt -> bool),
    compat_bool E.eq f -> In x (filter f s) -> f x = true.   
   Proof.
  simple induction s; simpl in |- *.
  intros; inversion H0.
  intros x l Hrec a f Hf.
  generalize (Hf x); case (f x); simpl in |- *; firstorder.
  inversion H0; firstorder.
  symmetry  in |- *; firstorder.
  Qed.
 
  Lemma filter_3 :
   forall (s : t) (x : elt) (f : elt -> bool),
   compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s).     
  Proof.
  simple induction s; simpl in |- *.
  intros; inversion H0.
  intros x l Hrec a f Hf.
  generalize (Hf x); case (f x); simpl in |- *; firstorder; inversion H0;
   firstorder.
  rewrite <- (H a) in H1; auto; discriminate H1.
  Qed.

  Lemma for_all_1 :
   forall (s : t) (f : elt -> bool),
   compat_bool E.eq f ->
   For_all (fun x => f x = true) s -> for_all f s = true.
  Proof. 
  simple induction s; simpl in |- *; auto; unfold For_all in |- *.
  intros x l Hrec f Hf. 
  generalize (Hf x); case (f x); simpl in |- *; firstorder. 
  rewrite (H x); auto.
  Qed.

  Lemma for_all_2 :
   forall (s : t) (f : elt -> bool),
   compat_bool E.eq f ->
   for_all f s = true -> For_all (fun x => f x = true) s.
  Proof. 
  simple induction s; simpl in |- *; auto; unfold For_all in |- *.
  intros; inversion H1.
  intros x l Hrec f Hf. 
  intros A a; intros. 
  assert (f x = true).
   generalize A; case (f x); auto.
  rewrite H0 in A; simpl in A.
  inversion H; firstorder.
  rewrite (Hf a x); auto.
  Qed.

  Lemma exists_1 :
   forall (s : t) (f : elt -> bool),
   compat_bool E.eq f -> Exists (fun x => f x = true) s -> exists_ f s = true.
  Proof.
  simple induction s; simpl in |- *; auto; unfold Exists in |- *.
  intros.
  elim H0; intuition. 
  inversion H2.
  intros x l Hrec f Hf. 
  generalize (Hf x); case (f x); simpl in |- *; firstorder. 
  inversion_clear H0.
  absurd (false = true); auto with bool.
  rewrite (H x); auto.
  rewrite <- H1.
  firstorder.
  firstorder.
  Qed.

  Lemma exists_2 :
   forall (s : t) (f : elt -> bool),
   compat_bool E.eq f -> exists_ f s = true -> Exists (fun x => f x = true) s.
  Proof. 
  simple induction s; simpl in |- *; auto; unfold Exists in |- *.
  intros; discriminate.
  intros x l Hrec f Hf.
  generalize (refl_equal (f x)); pattern (f x) at -1 in |- *; case (f x). 
  intros; exists x; auto.
  intros; elim (Hrec f); auto; firstorder.
  Qed.

  Lemma partition_Inf_1 :
   forall (s : t) (Hs : Sort s) (f : elt -> bool) (x : elt),
   Inf x s -> Inf x (fst (partition f s)).
  Proof.
  simple induction s; simpl in |- *.
  intuition.  
  intros x l Hrec Hs f a Ha; inversion_clear Hs; inversion Ha.
  generalize (Hrec H f a).
  case (f x); case (partition f l); simpl in |- *.
  intros; constructor; auto.
  eauto.
  Qed.

  Lemma partition_Inf_2 :
   forall (s : t) (Hs : Sort s) (f : elt -> bool) (x : elt),
   Inf x s -> Inf x (snd (partition f s)).
  Proof.
  simple induction s; simpl in |- *.
  intuition.  
  intros x l Hrec Hs f a Ha; inversion_clear Hs; inversion Ha.
  generalize (Hrec H f a).
  case (f x); case (partition f l); simpl in |- *.
  eauto.
  intros; constructor; auto.
  Qed.

  Lemma partition_sort_1 :
   forall (s : t) (Hs : Sort s) (f : elt -> bool), Sort (fst (partition f s)).
  Proof.
  simple induction s; simpl in |- *.
  auto.
  intros x l Hrec Hs f; inversion_clear Hs.
  generalize (Hrec H f); generalize (partition_Inf_1 H f).
  case (f x); case (partition f l); simpl in |- *; auto.
  Qed.
  
  Lemma partition_sort_2 :
   forall (s : t) (Hs : Sort s) (f : elt -> bool), Sort (snd (partition f s)).
  Proof.
  simple induction s; simpl in |- *.
  auto.
  intros x l Hrec Hs f; inversion_clear Hs.
  generalize (Hrec H f); generalize (partition_Inf_2 H f).
  case (f x); case (partition f l); simpl in |- *; auto.
  Qed.

  Lemma partition_1 :
   forall (s : t) (f : elt -> bool),
   compat_bool E.eq f -> Equal (fst (partition f s)) (filter f s).
  Proof.
  simple induction s; simpl in |- *; auto; unfold Equal in |- *.
  firstorder.
  intros x l Hrec f Hf.
  generalize (Hrec f Hf); clear Hrec.
  case (partition f l); intros s1 s2; simpl in |- *; intros.
  case (f x); simpl in |- *; firstorder; inversion H0; intros; firstorder. 
  Qed.
   
  Lemma partition_2 :
   forall (s : t) (f : elt -> bool),
   compat_bool E.eq f ->
   Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof.
  simple induction s; simpl in |- *; auto; unfold Equal in |- *.
  firstorder.
  intros x l Hrec f Hf. 
  generalize (Hrec f Hf); clear Hrec.
  case (partition f l); intros s1 s2; simpl in |- *; intros.
  case (f x); simpl in |- *; firstorder; inversion H0; intros; firstorder. 
  Qed.
 
  Definition eq : t -> t -> Prop := Equal.

  Lemma eq_refl : forall s : t, eq s s. 
  Proof. 
  unfold eq, Equal in |- *; intuition.
  Qed.

  Lemma eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Proof. 
  unfold eq, Equal in |- *; firstorder.
  Qed.

  Lemma eq_trans : forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Proof. 
  unfold eq, Equal in |- *; firstorder.
  Qed.

  Inductive lt : t -> t -> Prop :=
    | lt_nil : forall (x : elt) (s : t), lt [] (x :: s)
    | lt_cons_lt :
        forall (x y : elt) (s s' : t), E.lt x y -> lt (x :: s) (y :: s')
    | lt_cons_eq :
        forall (x y : elt) (s s' : t),
        E.eq x y -> lt s s' -> lt (x :: s) (y :: s').
  Hint Constructors lt.
   
  Lemma lt_trans : forall s s' s'' : t, lt s s' -> lt s' s'' -> lt s s''.
  Proof. 
  intros s s' s'' H; generalize s''; clear s''; elim H.
  intros x l s'' H'; inversion_clear H'; auto.
  intros x x' l l' E s'' H'; inversion_clear H'; auto. 
  eauto.
  constructor 2; apply ME.lt_eq with x'; auto.
  intros.
  inversion_clear H3.
  constructor 2; apply ME.eq_lt with y; auto.
  constructor 3; eauto.  
  Qed. 

  Lemma lt_not_eq :
   forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), lt s s' -> ~ eq s s'.
  Proof. 
  unfold eq, Equal in |- *. 
  intros s s' Hs Hs' H; generalize Hs Hs'; clear Hs Hs'; elim H; intros;
   intro.
  elim (H0 x); intros.
  assert (X : In x []); auto; inversion X.
  inversion_clear Hs; inversion_clear Hs'.
  elim (H1 x); intros. 
  assert (X : In x (y :: s'0)); auto; inversion_clear X.
  absurd (E.eq x y); eauto.
  absurd (E.lt y x); auto.
  eapply In_sort; eauto.
  inversion_clear Hs; inversion_clear Hs'.
  elim H2; auto; intuition.
  elim (H3 a); intros.
  assert (X : In a (y :: s'0)); auto; inversion_clear X; auto.
  absurd (E.lt x a); eauto.
  eapply In_sort with s0; eauto.
  elim (H3 a); intros.
  assert (X : In a (x :: s0)); auto; inversion_clear X; auto.
  absurd (E.lt y a); eauto.
  eapply In_sort with s'0; eauto.
  Qed.

  Definition compare :
    forall (s s' : t) (Hs : Sort s) (Hs' : Sort s'), Compare lt eq s s'.
  Proof.
  simple induction s.
  intros; case s'. 
  constructor 2; apply eq_refl. 
  constructor 1; auto.
  intros a l Hrec s'; case s'.
  constructor 3; auto.
  intros a' l' Hs Hs'.
  case (E.compare a a'); [ constructor 1 | idtac | constructor 3 ]; auto.
  elim (Hrec l');
   [ constructor 1
   | constructor 2
   | constructor 3
   | inversion Hs
   | inversion Hs' ]; auto.
  generalize e; unfold eq, Equal in |- *; intuition; inversion_clear H; eauto;
   elim (e1 a0); auto.
  Defined.

End Raw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we 
   need to encapsulate everything into a type of strictly ordered lists. *)

Module Make (X: OrderedType) <: S with Module E := X.

 Module E := X.
 Module Raw := Raw X. 

 Record slist : Set :=  {this :> Raw.t; sorted : sort E.lt this}.
 Definition t := slist. 
 Definition elt := X.t.
 
 Definition In (x : elt) (s : t) := Raw.In x s.
 Definition Equal s s' := forall a : elt, In a s <-> In a s'.
 Definition Subset s s' := forall a : elt, In a s -> In a s'.
 Definition Add (x : elt) (s s' : t) :=
   forall y : elt, In y s' <-> E.eq y x \/ In y s.
 Definition Empty s := forall a : elt, ~ In a s.
 Definition For_all (P : elt -> Prop) (s : t) :=
   forall x : elt, In x s -> P x.
 Definition Exists (P : elt -> Prop) (s : t) := exists x : elt, In x s /\ P x.
  
 Definition In_1 (s : t) := Raw.In_eq (s:=s).
 
 Definition mem (x : elt) (s : t) := Raw.mem x s.
 Definition mem_1 (s : t) := Raw.mem_1 (sorted s). 
 Definition mem_2 (s : t) := Raw.mem_2 (s:=s).

 Definition add x s := Build_slist (Raw.add_sort (sorted s) x).
 Definition add_1 (s : t) := Raw.add_1 (sorted s).
 Definition add_2 (s : t) := Raw.add_2 (sorted s).
 Definition add_3 (s : t) := Raw.add_3 (sorted s).

 Definition remove x s := Build_slist (Raw.remove_sort (sorted s) x).
 Definition remove_1 (s : t) := Raw.remove_1 (sorted s).
 Definition remove_2 (s : t) := Raw.remove_2 (sorted s).
 Definition remove_3 (s : t) := Raw.remove_3 (sorted s).
 
 Definition singleton x := Build_slist (Raw.singleton_sort x).
 Definition singleton_1 := Raw.singleton_1.
 Definition singleton_2 := Raw.singleton_2.
  
 Definition union (s s' : t) :=
   Build_slist (Raw.union_sort (sorted s) (sorted s')). 
 Definition union_1 (s s' : t) := Raw.union_1 (sorted s) (sorted s').
 Definition union_2 (s s' : t) := Raw.union_2 (sorted s) (sorted s').
 Definition union_3 (s s' : t) := Raw.union_3 (sorted s) (sorted s').

 Definition inter (s s' : t) :=
   Build_slist (Raw.inter_sort (sorted s) (sorted s')). 
 Definition inter_1 (s s' : t) := Raw.inter_1 (sorted s) (sorted s').
 Definition inter_2 (s s' : t) := Raw.inter_2 (sorted s) (sorted s').
 Definition inter_3 (s s' : t) := Raw.inter_3 (sorted s) (sorted s').
 
 Definition diff (s s' : t) :=
   Build_slist (Raw.diff_sort (sorted s) (sorted s')). 
 Definition diff_1 (s s' : t) := Raw.diff_1 (sorted s) (sorted s').
 Definition diff_2 (s s' : t) := Raw.diff_2 (sorted s) (sorted s').
 Definition diff_3 (s s' : t) := Raw.diff_3 (sorted s) (sorted s').
 
 Definition equal (s s' : t) := Raw.equal s s'. 
 Definition equal_1 (s s' : t) := Raw.equal_1 (sorted s) (sorted s').  
 Definition equal_2 (s s' : t) := Raw.equal_2 (s:=s) (s':=s').
 
 Definition subset (s s' : t) := Raw.subset s s'.
 Definition subset_1 (s s' : t) := Raw.subset_1 (sorted s) (sorted s').  
 Definition subset_2 (s s' : t) := Raw.subset_2 (s:=s) (s':=s').

 Definition empty := Build_slist Raw.empty_sort.
 Definition empty_1 := Raw.empty_1.
 
 Definition is_empty (s : t) := Raw.is_empty s.
 Definition is_empty_1 (s : t) := Raw.is_empty_1 (s:=s).
 Definition is_empty_2 (s : t) := Raw.is_empty_2 (s:=s).

 Definition elements (s : t) := Raw.elements s.
 Definition elements_1 (s : t) := Raw.elements_1 (s:=s).
 Definition elements_2 (s : t) := Raw.elements_2 (s:=s).
 Definition elements_3 (s : t) := Raw.elements_3 (sorted s).
 
 Definition min_elt (s : t) := Raw.min_elt s.
 Definition min_elt_1 (s : t) := Raw.min_elt_1 (s:=s).
 Definition min_elt_2 (s : t) := Raw.min_elt_2 (sorted s).
 Definition min_elt_3 (s : t) := Raw.min_elt_3 (s:=s).

 Definition max_elt (s : t) := Raw.max_elt s.
 Definition max_elt_1 (s : t) := Raw.max_elt_1 (s:=s).
 Definition max_elt_2 (s : t) := Raw.max_elt_2 (sorted s).
 Definition max_elt_3 (s : t) := Raw.max_elt_3 (s:=s).
  
 Definition choose := min_elt.
 Definition choose_1 := min_elt_1.
 Definition choose_2 := min_elt_3.
 
 Definition fold (B : Set) (f : elt -> B -> B) (s : t) := Raw.fold (B:=B) f s. 
 Definition fold_1 (s : t) := Raw.fold_1 (sorted s). 
 
 Definition cardinal (s : t) := Raw.cardinal s.
 Definition cardinal_1 (s : t) := Raw.cardinal_1 (sorted s). 
 
 Definition filter (f : elt -> bool) (s : t) :=
   Build_slist (Raw.filter_sort (sorted s) f).
 Definition filter_1 (s : t) := Raw.filter_1 (s:=s).
 Definition filter_2 (s : t) := Raw.filter_2 (s:=s).
 Definition filter_3 (s : t) := Raw.filter_3 (s:=s).
 
 Definition for_all (f : elt -> bool) (s : t) := Raw.for_all f s.
 Definition for_all_1 (s : t) := Raw.for_all_1 (s:=s). 
 Definition for_all_2 (s : t) := Raw.for_all_2 (s:=s). 

 Definition exists_ (f : elt -> bool) (s : t) := Raw.exists_ f s.
 Definition exists_1 (s : t) := Raw.exists_1 (s:=s). 
 Definition exists_2 (s : t) := Raw.exists_2 (s:=s). 

 Definition partition (f : elt -> bool) (s : t) :=
   let p := Raw.partition f s in
   (Build_slist (this:=fst p) (Raw.partition_sort_1 (sorted s) f),
   Build_slist (this:=snd p) (Raw.partition_sort_2 (sorted s) f)).
 Definition partition_1 (s : t) := Raw.partition_1 s.
 Definition partition_2 (s : t) := Raw.partition_2 s. 

 Definition eq (s s' : t) := Raw.eq s s'.
 Definition eq_refl (s : t) := Raw.eq_refl s.
 Definition eq_sym (s s' : t) := Raw.eq_sym (s:=s) (s':=s').
 Definition eq_trans (s s' s'' : t) :=
   Raw.eq_trans (s:=s) (s':=s') (s'':=s'').
  
 Definition lt (s s' : t) := Raw.lt s s'.
 Definition lt_trans (s s' s'' : t) :=
   Raw.lt_trans (s:=s) (s':=s') (s'':=s'').
 Definition lt_not_eq (s s' : t) := Raw.lt_not_eq (sorted s) (sorted s').

 Definition compare : forall s s' : t, Compare lt eq s s'.
 Proof.
 intros; elim (Raw.compare (sorted s) (sorted s'));
  [ constructor 1 | constructor 2 | constructor 3 ]; 
  auto. 
 Defined.

End Make.
