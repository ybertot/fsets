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

(** This module implements sets using red-black trees *)

Require Import FSetInterface.
Require Import FSetList.
Require Import FSetBridge.

Require Import Omega.
Require Import ZArith.

Open Scope Z_scope.

Set Firstorder Depth 3.

Module Make (X: OrderedType) <: Sdep with Module E := X.

  Module E := X.
  Module ME := OrderedTypeFacts X.

  Definition elt := X.t.

  (** * Red-black trees *)

  Inductive color : Set :=
    | red : color
    | black : color.

  Inductive tree : Set :=
    | Leaf : tree
    | Node : color -> tree -> X.t -> tree -> tree.

  (** * Occurrence in a tree *)

  Inductive In_tree (x : elt) : tree -> Prop :=
    | IsRoot :
        forall (l r : tree) (c : color) (y : elt),
        X.eq x y -> In_tree x (Node c l y r)
    | InLeft :
        forall (l r : tree) (c : color) (y : elt),
        In_tree x l -> In_tree x (Node c l y r)
    | InRight :
        forall (l r : tree) (c : color) (y : elt),
        In_tree x r -> In_tree x (Node c l y r).

  Hint Constructors In_tree.

  (** [In_tree] is color-insensitive *)

  Lemma In_color :
   forall (c c' : color) (x y : elt) (l r : tree),
   In_tree y (Node c l x r) -> In_tree y (Node c' l x r).
  Proof.
    inversion 1; auto.
  Qed.
  Hint Resolve In_color.

  (** * Binary search trees *)

  (** [lt_tree x s]: all elements in [s] are smaller than [x] 
      (resp. greater for [gt_tree]) *)

  Definition lt_tree (x : elt) (s : tree) :=
    forall y : elt, In_tree y s -> X.lt y x.
  Definition gt_tree (x : elt) (s : tree) :=
    forall y : elt, In_tree y s -> X.lt x y.

  Hint Unfold lt_tree gt_tree.

  (** Results about [lt_tree] and [gt_tree] *)

  Lemma lt_leaf : forall x : elt, lt_tree x Leaf.
  Proof.
    unfold lt_tree in |- *; intros; inversion H.
  Qed.

  Lemma gt_leaf : forall x : elt, gt_tree x Leaf.
  Proof.
    unfold gt_tree in |- *; intros; inversion H.
  Qed.

  Lemma lt_tree_node :
   forall (x y : elt) (l r : tree) (c : color),
   lt_tree x l -> lt_tree x r -> X.lt y x -> lt_tree x (Node c l y r).
  Proof.
    unfold lt_tree in |- *; intuition.
    inversion_clear H2; intuition.
    apply ME.eq_lt with y; auto.
  Qed.

  Lemma gt_tree_node :
   forall (x y : elt) (l r : tree) (c : color),
   gt_tree x l -> gt_tree x r -> E.lt x y -> gt_tree x (Node c l y r).
  Proof.
    unfold gt_tree in |- *; intuition.
    inversion_clear H2; intuition.
    apply ME.lt_eq with y; auto.
  Qed.

  Hint Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.

  Lemma lt_node_lt :
   forall (x y : elt) (l r : tree) (c : color),
   lt_tree x (Node c l y r) -> E.lt y x.
  Proof.
    intros; apply H; auto.
  Qed.

  Lemma gt_node_gt :
   forall (x y : elt) (l r : tree) (c : color),
   gt_tree x (Node c l y r) -> E.lt x y.
  Proof.
    intros; apply H; auto.
  Qed.

  Lemma lt_left :
   forall (x y : elt) (l r : tree) (c : color),
   lt_tree x (Node c l y r) -> lt_tree x l.
  Proof.
    intros; red in |- *; intros; apply H; auto.
  Qed.

  Lemma lt_right :
   forall (x y : elt) (l r : tree) (c : color),
   lt_tree x (Node c l y r) -> lt_tree x r.
  Proof.
    intros; red in |- *; intros; apply H; auto.
  Qed.

  Lemma gt_left :
   forall (x y : elt) (l r : tree) (c : color),
   gt_tree x (Node c l y r) -> gt_tree x l.
  Proof.
    intros; red in |- *; intros; apply H; auto.
  Qed.

  Lemma gt_right :
   forall (x y : elt) (l r : tree) (c : color),
   gt_tree x (Node c l y r) -> gt_tree x r.
  Proof.
    intros; red in |- *; intros; apply H; auto.
  Qed.

  Hint Resolve lt_node_lt gt_node_gt lt_left lt_right gt_left gt_right.

  Lemma lt_tree_not_in :
   forall (x : elt) (t : tree), lt_tree x t -> ~ In_tree x t.
  Proof.
    unfold lt_tree in |- *; intros; red in |- *; intros.
    generalize (H x H0); intro; absurd (X.lt x x); auto.
  Qed.

  Lemma lt_tree_trans :
   forall x y : elt, X.lt x y -> forall t : tree, lt_tree x t -> lt_tree y t.
  Proof.
    unfold lt_tree in |- *; firstorder eauto.
  Qed.

  Lemma gt_tree_not_in :
   forall (x : elt) (t : tree), gt_tree x t -> ~ In_tree x t.
  Proof.
    unfold gt_tree in |- *; intros; red in |- *; intros.
    generalize (H x H0); intro; absurd (X.lt x x); auto.
  Qed.

  Lemma gt_tree_trans :
   forall x y : elt, X.lt y x -> forall t : tree, gt_tree x t -> gt_tree y t.
  Proof.
    unfold gt_tree in |- *; firstorder eauto.
  Qed.

  Hint Resolve lt_tree_not_in lt_tree_trans gt_tree_not_in gt_tree_trans.

  (** [bst t] : [t] is a binary search tree *)

  Inductive bst : tree -> Prop :=
    | BSLeaf : bst Leaf
    | BSNode :
        forall (x : elt) (l r : tree) (c : color),
        bst l -> bst r -> lt_tree x l -> gt_tree x r -> bst (Node c l x r).

  Hint Constructors bst.

  (** Results about [bst] *)
 
  Lemma bst_left :
   forall (x : elt) (l r : tree) (c : color), bst (Node c l x r) -> bst l.
  Proof.
    intros x l r c H; inversion H; auto.
  Qed.

  Lemma bst_right :
   forall (x : elt) (l r : tree) (c : color), bst (Node c l x r) -> bst r.
  Proof.
    intros x l r c H; inversion H; auto.
  Qed.

  Implicit Arguments bst_left. Implicit Arguments bst_right.
  Hint Resolve bst_left bst_right.

  Lemma bst_color :
   forall (c c' : color) (x : elt) (l r : tree),
   bst (Node c l x r) -> bst (Node c' l x r).
  Proof.
    inversion 1; auto.
  Qed.
  Hint Resolve bst_color.

  (** Key fact about binary search trees: rotations preserve the 
      [bst] property *)

  Lemma rotate_left :
   forall (x y : elt) (a b c : tree) (c1 c2 c3 c4 : color),
   bst (Node c1 a x (Node c2 b y c)) -> bst (Node c3 (Node c4 a x b) y c).
  Proof.
    intros; inversion H; intuition.
    constructor; intuition.
    constructor; eauto.
    eauto.
    apply lt_tree_node; intuition.
    apply lt_tree_trans with x; auto.
    inversion H5; auto.
    inversion H5; auto.
  Qed.

  Lemma rotate_right :
   forall (x y : elt) (a b c : tree) (c1 c2 c3 c4 : color),
   bst (Node c3 (Node c4 a x b) y c) -> bst (Node c1 a x (Node c2 b y c)).
  Proof.
    intros; inversion H; intuition.
    constructor; intuition.
    eauto.
    constructor; auto.
    inversion H4; auto.
    inversion H4; auto.
    apply gt_tree_node; intuition.
    inversion H4; auto.
    apply gt_tree_trans with y; auto.
    eauto.
  Qed.

  Hint Resolve rotate_left rotate_right.

  (** * Balanced red-black trees *)

  (** [rbtree n t]: [t] is a properly balanced red-black tree, i.e. it
      satisfies the following two invariants:
      - a red node has no red son
      - any path from the root to a leaf has exactly [n] black nodes *)
       
  Definition is_not_red (t : tree) :=
    match t with
    | Leaf => True
    | Node black x0 x1 x2 => True
    | Node red x0 x1 x2 => False
    end.

  Hint Unfold is_not_red.  

  Inductive rbtree : nat -> tree -> Prop :=
    | RBLeaf : rbtree 0%nat Leaf
    | RBRed :
        forall (x : elt) (l r : tree) (n : nat),
        rbtree n l ->
        rbtree n r ->
        is_not_red l -> is_not_red r -> rbtree n (Node red l x r)
    | RBBlack :
        forall (x : elt) (l r : tree) (n : nat),
        rbtree n l -> rbtree n r -> rbtree (S n) (Node black l x r).

  Hint Constructors rbtree.

  (** Results about [rbtree] *)

  Lemma rbtree_left :
   forall (x : elt) (l r : tree) (c : color),
   (exists n : nat, rbtree n (Node c l x r)) -> exists n : nat, rbtree n l.
  Proof.
    intros x l r c (n, Hn); inversion_clear Hn; intuition eauto.
  Qed.

  Lemma rbtree_right :
   forall (x : elt) (l r : tree) (c : color),
   (exists n : nat, rbtree n (Node c l x r)) -> exists n : nat, rbtree n r.
  Proof.
    intros x l r c (n, Hn); inversion_clear Hn; intuition eauto.
  Qed.

  Implicit Arguments rbtree_left. Implicit Arguments rbtree_right.
  Hint Resolve rbtree_left rbtree_right.

  (** * Sets as red-black trees *)

  (** A set is implement as a record [t], containing a tree, 
      a proof that it is a binary search tree and a proof that it is 
      a properly balanced red-black tree *)

  Record t_ : Set := t_intro
    {the_tree :> tree;
     is_bst : bst the_tree;
     is_rbtree : exists n : nat, rbtree n the_tree}.
  Definition t := t_.

  (** Projections *)

  Lemma t_is_bst : forall s : t, bst s.
  Proof.
    simple destruct s; auto.
  Qed.
  Hint Resolve t_is_bst.

  (** * Logical appartness *)

  Definition In (x : elt) (s : t) : Prop := In_tree x s.

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Add (x : elt) (s s' : t) :=
    forall y : elt, In y s' <-> E.eq y x \/ In y s.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) (s : t) :=
    forall x : elt, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s : t) :=
    exists x : elt, In x s /\ P x.

  Lemma eq_In : forall (s : t) (x y : elt), E.eq x y -> In x s -> In y s.
  Proof.
    unfold In in |- *; simple destruct s; simpl in |- *;
     intuition clear is_bst0 is_rbtree0.
    induction  the_tree0
     as [| c the_tree0_1 Hrecthe_tree0_1 t0 the_tree0_0 Hrecthe_tree0_0];
     inversion_clear H0; intuition.
    apply IsRoot; eauto.
  Qed.

  Hint Resolve eq_In.

  (** * Empty set *)

  Definition t_empty : t.
  Proof.
    exists Leaf; auto; exists 0%nat; auto.
  Defined.

  Definition empty : {s : t | forall x : elt, ~ In x s}. 
  Proof.
    exists t_empty.
    unfold In in |- *; red in |- *; intros.
    inversion H.
  Defined.

  (** * Emptyness test *)

  Definition is_empty : forall s : t, {Empty s} + {~ Empty s}.
  Proof.
    unfold Empty, In in |- *; simple destruct s; simple destruct the_tree0;
     simpl in |- *; intros.
    left; auto.
    right; intuition.
    apply (H t1); auto.
  Defined.

  (** * Appartness *)

  (** The [mem] function is deciding appartness. It exploits the [bst] property
      to achieve logarithmic complexity. *)

  Definition mem : forall (x : elt) (s : t), {In x s} + {~ In x s}.
  Proof.
    intros x (s, Hs, Hrb).
    unfold In in |- *; simpl in |- *; clear Hrb.
    generalize Hs; elim s; simpl in |- *; intros.
  (* Leaf *)
    right. 
    unfold In in |- *; red in |- *; intros; inversion H.
  (* Node *)
    elim (X.compare x t1); intro.
    (* lt x t1 *)
    case H; intros.
    eauto.
    left; auto.
    right; intro.
    inversion H1; intuition.
    absurd (X.eq x t1); auto.
    inversion Hs0.
    absurd (In_tree x t2); eauto.
    (* eq x t1 *)
    left; auto.
    (* lt t1 x *)
    case H0; intros.
    eauto.
    left; auto.
    right; intro.
    inversion H1; intuition.
    absurd (X.eq t1 x); auto.
    inversion Hs0.
    absurd (In_tree x t0); eauto.
  Defined.

  (** * Singleton set *)

  Definition singleton_tree (x : elt) := Node red Leaf x Leaf.

  Lemma singleton_bst : forall x : elt, bst (singleton_tree x).
  Proof.
    unfold singleton_tree in |- *; auto.
  Qed.

  Lemma singleton_rbtree :
   forall x : elt, exists n : nat, rbtree n (singleton_tree x).
  Proof.
    unfold singleton_tree in |- *; eauto.
  Qed.

  Definition singleton :
    forall x : elt, {s : t | forall y : elt, In y s <-> E.eq x y}.
  Proof.
    intro x;
     exists
      (t_intro (singleton_tree x) (singleton_bst x) (singleton_rbtree x)).
    unfold In, singleton_tree in |- *; simpl in |- *; intuition.
    inversion_clear H; auto; inversion H0.
  Defined.

  (** * Insertion *)

  (** [almost_rbtree n t]: [t] may have one red-red conflict at its root;
      it satisfies [rbtree n] everywhere else *)

  Inductive almost_rbtree : nat -> tree -> Prop :=
    | ARBLeaf : almost_rbtree 0%nat Leaf
    | ARBRed :
        forall (x : elt) (l r : tree) (n : nat),
        rbtree n l -> rbtree n r -> almost_rbtree n (Node red l x r)
    | ARBBlack :
        forall (x : elt) (l r : tree) (n : nat),
        rbtree n l -> rbtree n r -> almost_rbtree (S n) (Node black l x r).

  Hint Constructors almost_rbtree.

  (** Results about [almost_rbtree] *)

  Lemma rbtree_almost_rbtree :
   forall (n : nat) (t : tree), rbtree n t -> almost_rbtree n t.
  Proof.
    simple destruct 1; intuition.
  Qed.

  Hint Resolve rbtree_almost_rbtree.

  Lemma rbtree_almost_rbtree_ex :
   forall s : tree,
   (exists n : nat, rbtree n s) -> exists n : nat, almost_rbtree n s.
  Proof.
    intros s (n, Hn); exists n; auto.
  Qed.

  Hint Resolve rbtree_almost_rbtree_ex.

  Lemma almost_rbtree_rbtree_black :
   forall (x : elt) (l r : tree) (n : nat),
   almost_rbtree n (Node black l x r) -> rbtree n (Node black l x r).
  Proof.
    inversion 1; auto.
  Qed.
  Hint Resolve almost_rbtree_rbtree_black.

  (** Balancing functions [lbalance] and [rbalance] (see below) require
      a rather complex pattern-matching; it is realized by the following
      function [conflict] which returns in the sum type [Conflict] *)

  Inductive Conflict (s : tree) : Set :=
    | NoConflict :
        (forall n : nat, almost_rbtree n s -> rbtree n s) -> Conflict s
    | RedRedConflict :
        forall (a b c : tree) (x y : elt),
        bst a ->
        bst b ->
        bst c ->
        lt_tree x a ->
        gt_tree x b ->
        lt_tree y b ->
        gt_tree y c ->
        X.lt x y ->
        (forall z : elt,
         In_tree z s <->
         X.eq z x \/ X.eq z y \/ In_tree z a \/ In_tree z b \/ In_tree z c) ->
        (forall n : nat,
         almost_rbtree n s -> rbtree n a /\ rbtree n b /\ rbtree n c) ->
        Conflict s.

  Definition conflict : forall s : tree, bst s -> Conflict s.
  Proof.
    simple destruct s; intros.
    (* s = Leaf *)
    constructor 1; inversion 1; auto.
    (* s = Node c t0 t1 t2 *)
    induction  c as [| ].
    (* s = Node red t0 t1 t2 *)
    generalize H; clear H; case t0; intros.
    (* s = Node red Leaf t1 t2 *)
    generalize H; clear H; case t2; intros.
    (* s = Node red Leaf t1 Leaf *)
    constructor 1; inversion_clear 1; intros.
    constructor; intuition.
    (* s = Node red Leaf t1 (Node c t3 t4 t5) *)
    induction  c as [| ].
    (* s = Node red Leaf t1 (Node red t3 t4 t5) *)
    constructor 2 with (a := Leaf) (b := t3) (c := t5) (x := t1) (y := t4);
     intuition; solve
     [ inversion_clear H; auto; inversion_clear H1; auto
     | inversion_clear H0; auto; inversion_clear H2; auto
     | inversion_clear H0; auto; inversion_clear H1; auto
     | inversion_clear H1; auto ].
    (* s = Node red Leaf t1 (Node black t3 t4 t5) *)
    constructor 1; inversion_clear 1; intros.
    constructor; intuition.
    (* s = Node red (Node c t3 t4 t5) t1 t2 *)
    induction  c as [| ].
    (* s = Node red (Node red t3 t4 t5) t1 t2 *)
    constructor 2 with (a := t3) (b := t5) (c := t2) (x := t4) (y := t1);
     intuition; solve
     [ inversion_clear H; auto; inversion_clear H0; auto
     | inversion_clear H0; auto; inversion_clear H1; auto
     | inversion_clear H1; auto ].
    (* s = Node red (Node black t3 t4 t5) t1 t2 *)
    generalize H; clear H; case t2; intros.
    (* s = Node red (Node black t3 t4 t5) t1 Leaf *)
    constructor 1; inversion_clear 1; intros.
    constructor; intuition.
    (* s = Node red (Node black t3 t4 t5) t1 (Node c t6 t7 t8) *)
    induction  c as [| ].
    (* s = Node red (Node black t3 t4 t5) t1 (Node red t6 t7 t8) *)
    constructor 2
     with (a := Node black t3 t4 t5) (b := t6) (c := t8) (x := t1) (y := t7);
     intuition; solve
     [ inversion_clear H; auto; inversion_clear H1; auto
     | inversion_clear H0; auto; inversion_clear H2; auto
     | inversion_clear H0; auto; inversion_clear H1; auto
     | inversion_clear H1; auto ].
    (* s = Node red (Node black t3 t4 t5) t1 (Node black t6 t7 t8) *)
    constructor 1; inversion_clear 1; intros.
    constructor; intuition.
    (* s = Node black t0 t1 t2 *)
    constructor 1; inversion_clear 1; intros.
    constructor; intuition.
  Defined.

  (** [lbalance c x l r] acts as a black node constructor,
      solving a possible red-red conflict on [l], using the following
      schema: 
<<   
     B (R (R a x b) y c) z d
     B (R a x (R b y c)) z d -> R (B a x b) y (R c z d) 
     B a x b -> B a x b 
>> 
      The result is not necessarily a black node. *)

  Definition lbalance :
    forall (l : tree) (x : elt) (r : tree),
    lt_tree x l ->
    gt_tree x r ->
    bst l ->
    bst r ->
    {s : tree |
    bst s /\
    (forall n : nat, almost_rbtree n l /\ rbtree n r -> rbtree (S n) s) /\
    (forall y : elt, In_tree y s <-> E.eq y x \/ In_tree y l \/ In_tree y r)}.
  Proof.
    intros; case (conflict l).
    assumption.
    (* no conflict *)
    exists (Node black l x r); intuition. 
    inversion H3; auto. 
    (* red red conflict *)
    intros; exists (Node red (Node black a x0 b) y (Node black c x r));
     intuition.
    constructor; intuition.
    constructor; intuition.
    intro z; generalize (i z); intuition.
    apply lt_tree_node; intuition.
    apply lt_tree_trans with x0; auto.
    assert (In_tree y l). firstorder. 
    apply gt_tree_node; intuition.
    intro z; generalize (i z); intuition.
    apply X.lt_trans with x; auto.
    apply H; assumption.
    generalize (a0 n H4); constructor; intuition.
    generalize (i y0); inversion_clear H3; intuition; inversion_clear H4;
     intuition.
    (* bug Firstorder *) generalize (i y0); intuition.
  Defined.

  (** [rbalance l x r] is similar to [lbalance], solving a possible red-red
      conflict on [r]. The balancing schema is similar:
<<
     B a x (R (R b y c) z d)
     B a x (R b y (R c z d)) -> R (B a x b) y (R c z d) 
     B a x b -> B a x b 
>> *)

  Definition rbalance :
    forall (l : tree) (x : elt) (r : tree),
    lt_tree x l ->
    gt_tree x r ->
    bst l ->
    bst r ->
    {s : tree |
    bst s /\
    (forall n : nat, almost_rbtree n r /\ rbtree n l -> rbtree (S n) s) /\
    (forall y : elt, In_tree y s <-> E.eq y x \/ In_tree y l \/ In_tree y r)}.
  Proof.
    intros; case (conflict r).
    assumption.
    (* no conflict *)
    exists (Node black l x r); intuition. 
    inversion H3; auto. 
    (* red red conflict *)
    intros; exists (Node red (Node black l x a) x0 (Node black b y c));
     intuition.
    constructor; intuition.
    constructor; intuition.
    intro z; generalize (i z); intuition.
    assert (X.lt x x0).
    assert (In_tree x0 r). firstorder. 
    apply H0; assumption.
    apply lt_tree_node; intuition.
    apply lt_tree_trans with x; auto.
    apply gt_tree_node; intuition.
    apply gt_tree_trans with y; auto.
    generalize (a0 n H4); constructor; intuition.
    generalize (i y0); inversion_clear H3; intuition; inversion_clear H4;
     intuition.
    (* bug Firstorder *) generalize (i y0); intuition.
  Defined.

  (** [insert x s] inserts [x] in tree [s], resulting in a possible top red-red
      conflict when [s] is red. Its code is:
<<  
     insert x Empty = 
       Node red Empty x Empty
     insert x (Node red a y b) = 
       if lt x y then Node red (insert x a) y b
       else if lt y x then Node red a y (insert x b)
       else (Node c a y b) 
     insert x (Node black a y b) = 
       if lt x y then lbalance (insert x a) y b
       else if lt y x then rbalance a y (insert x b)
       else (Node c a y b) 
>> *)

  Definition insert :
    forall (x : elt) (s : t),
    {s' : tree |
    bst s' /\
    (forall n : nat,
     rbtree n s -> almost_rbtree n s' /\ (is_not_red s -> rbtree n s')) /\
    (forall y : elt, In_tree y s' <-> E.eq y x \/ In_tree y s)}.
  Proof.
    intros x (s, Hs, Hrb).
    generalize Hs Hrb; clear Hs Hrb;
     induction  s as [| c s1 Hrecs1 t0 s0 Hrecs0]; 
     simpl in |- *; intros.
    (* Empty *)
    exists (singleton_tree x); unfold singleton_tree in |- *; simpl in |- *;
     intuition.
    inversion H; eauto.
    (* Node c t0 t1 t2 *)
    simpl in Hrecs0, Hrecs1.
    induction  c as [| ].
    (* c = red => usual insertion in BST *)
    elim (X.compare x t0); intro.
    (* lt x t1 *)
    clear Hrecs0; case Hrecs1; clear Hrecs1; intros. eauto. eauto.
    intuition.
    exists (Node red x0 t0 s0); intuition.
    constructor; intuition.
    inversion Hs; auto.
    red in |- *; intros.
    generalize (H2 y); intuition.
    apply ME.eq_lt with x; auto.
    inversion Hs; auto.
    inversion Hs; auto.
    inversion_clear H0; generalize (H1 n); intuition.  (* BUG Firstorder *)
    generalize (H2 y); inversion H0; intuition.
    generalize (H2 y); intuition.
    generalize (H2 y); inversion H3; intuition.
    (* eq x t1 *)
    clear Hrecs1 Hrecs0.
    exists (Node red s1 t0 s0); intuition.
    apply IsRoot; eauto.
    (* lt t1 x *)
    clear Hrecs1; case Hrecs0; clear Hrecs0; intros. eauto. eauto.
    intuition.
    exists (Node red s1 t0 x0); intuition.
    constructor; intuition.
    inversion Hs; auto.
    inversion Hs; auto.
    red in |- *; intros.
    generalize (H2 y); intuition.
    apply ME.lt_eq with x; auto.
    inversion Hs; auto.
    inversion_clear H0;  (* bug Firstorder *) generalize (H1 n); intuition.
    generalize (H2 y); inversion H0; intuition.
    generalize (H2 y); intuition.
    generalize (H2 y); inversion H3; intuition.

    (* c = black => same code using smart constructors *)
    elim (X.compare x t0); intro.
    (* lt x t1 *)
    clear Hrecs0; case Hrecs1; clear Hrecs1; intros. eauto. eauto.
    intuition.
    case (lbalance x0 t0 s0); intuition.
    red in |- *; intros.
    generalize (H2 y); intuition.
    apply ME.eq_lt with x; auto.
    inversion Hs; auto.
    inversion Hs; auto.
    inversion Hs; auto.
    exists x1; intuition.
    inversion_clear H3; firstorder.
    inversion_clear H3; firstorder.
    generalize (H2 y); generalize (H5 y); intuition.
    generalize (H2 y); generalize (H5 y); intuition.
    inversion H6; generalize (H2 y); generalize (H5 y); intuition.
    (* eq x t1 *)
    clear Hrecs1 Hrecs0.
    exists (Node black s1 t0 s0); intuition.
    apply IsRoot; eauto.
    (* lt t1 x *)
    clear Hrecs1; case Hrecs0; clear Hrecs0; intros. eauto. eauto.
    intuition.
    case (rbalance s1 t0 x0); intuition.
    inversion Hs; auto.
    red in |- *; intros.
    generalize (H2 y); intuition.
    apply ME.lt_eq with x; auto.
    inversion Hs; auto.
    inversion Hs; auto.
    exists x1; intuition.
    inversion_clear H3; firstorder.
    inversion_clear H3; firstorder.
    generalize (H2 y); generalize (H5 y); intuition.
    generalize (H2 y); generalize (H5 y); intuition.
    inversion H6; generalize (H2 y); generalize (H5 y); intuition.
  Defined.


  (** Finally [add x s] calls [insert] and recolors the root as black:
<<
      add x s = match insert x s with 
        | Node _ a y b -> Node black a y b
        | Empty -> assert false (* absurd *)
>> *)

  Definition add : forall (x : elt) (s : t), {s' : t | Add x s s'}.
  Proof.
    intros x s; case (insert x s). 
    elim s; clear s; intros s Hbs Hrb; simpl in |- *; simple destruct x0;
     intuition.
    (* Leaf => absurd *)
    absurd (In_tree x Leaf).
    intro; inversion H0.
    firstorder.
    (* Node c t0 t1 t2 *)
    induction  c as [| ].
    (* c = red => changed to black *)
    set (s' := Node black t0 t1 t2) in *.
    assert (s'bst : bst s').
    unfold s' in |- *; eauto.
    assert (s'rbtree : exists n : nat, rbtree n s').
    elim Hrb; clear Hrb; intros n Hrb.
    generalize (H1 n Hrb); intuition.
    exists (S n); unfold s' in |- *.
    inversion H3; auto.
    exists (t_intro s' s'bst s'rbtree); unfold s', Add, In in |- *;
     simpl in |- *.
    intro y; generalize (H2 y); clear H2; intuition;
     try (apply In_color with red; assumption).
    assert (In_tree y (Node red t0 t1 t2)); auto.
    apply In_color with black; assumption.
    (* c = black => unchanged *)
    assert (s'rbtree : exists n : nat, rbtree n (Node black t0 t1 t2)).
    elim Hrb; clear Hrb; intros n Hrb.
    exists n; firstorder. 
    exists (t_intro (Node black t0 t1 t2) H s'rbtree); intuition.
  Defined.

  (** * Deletion *)

  (** [UnbalancedLeft n t]: [t] is a tree of black height [S n]
     on its left side and [n] on its right side (the root color
     is taken into account, whathever it is) *)
     
  Inductive UnbalancedLeft : nat -> tree -> Prop :=
    | ULRed :
        forall (x : elt) (l r : tree) (n : nat),
        rbtree (S n) l ->
        rbtree n r -> is_not_red l -> UnbalancedLeft n (Node red l x r)
    | ULBlack :
        forall (x : elt) (l r : tree) (n : nat),
        rbtree (S n) l ->
        rbtree n r -> UnbalancedLeft (S n) (Node black l x r).

  (** when a tree is unbalanced on its left, it can be repared *)

  Definition unbalanced_left :
    forall s : tree,
    bst s ->
    {r : tree * bool |
    let (s', b) := r in
    bst s' /\
    (is_not_red s /\ b = false -> is_not_red s') /\
    (forall n : nat,
     UnbalancedLeft n s -> if b then rbtree n s' else rbtree (S n) s') /\
    (forall y : elt, In_tree y s' <-> In_tree y s)}.
  Proof.
    simple destruct s.
    (* s = Leaf => Absurd *)
    intro; exists (Leaf, false); intuition; inversion H0.
    (* s = Node c t0 t1 t2 *)
    simple induction c.
    (* s = Node red t0 t1 t2 *)
    simple destruct t0.
    (* s = Node red Leaf t1 t2 => Absurd *)
    intros; exists (Node black Leaf t1 t2, false); intuition.
    apply bst_color with red; auto.
    inversion H0.
    inversion H5.
    apply In_color with black; auto.
    apply In_color with red; auto.
    (* s = Node red (Node c0 t1 t2 t3) t4 t5 *)
    simple induction c0.
    (* s = Node red (Node red t1 t2 t3) t4 t5 => Absurd *)
    intros; exists (Node black (Node red t1 t2 t3) t4 t5, false); intuition.
    apply bst_color with red; auto.
    inversion H0; elim H7.
    apply In_color with black; auto.
    apply In_color with red; auto.
    (* s = Node red (Node black t1 t2 t3) t4 t5 *)
    intros.
    case (lbalance (Node red t1 t2 t3) t4 t5).
    inversion H; auto.
    inversion H; unfold gt_tree in |- *; firstorder with In_color.
    inversion H; apply bst_color with black; auto.
    inversion H; auto.
    intros t' Ht'; exists (t', false); intuition.
    elim H4.
    apply H2; intuition.
    constructor; inversion H1; auto.
    inversion_clear H8; auto.
    inversion_clear H8; auto.
    inversion_clear H1; auto.
    generalize (H3 y); clear H3; intuition.
    constructor 2; firstorder with In_color.
    inversion_clear H1; firstorder with In_color.
    (* s = Node black t0 t1 t2 *)
    simple destruct t0.
    (* s = Node black Leaf t1 t2 => Absurd *)
    intros; exists (Node black Leaf t1 t2, false); intuition.
    inversion H0.
    inversion H4.
    (* s = Node black (Node c0 t1 t2 t3) t4 t5 *)
    simple induction c0.
    (* s = Node black (Node red t1 t2 t3) t4 t5 *)
    simple destruct t3.
    (* s = Node black (Node red t1 t2 Leaf) t4 t5 => Absurd *)
    intros; exists (Node black (Node red t1 t2 Leaf) t4 t5, false); intuition.
    inversion H0; inversion H4; inversion H12.
    (* s = Node black (Node red t1 t2 (Node c1 t4 t5 t6)) t7 t8) *)
    simple induction c1.
    (* s = Node black (Node red t1 t2 (Node red t4 t5 t6)) t7 t8) => absurd *)
    intros;
     exists (Node black (Node red t1 t2 (Node red t4 t5 t6)) t7 t8, false);
     intuition.
    inversion H0; inversion H4; elim H14. 
    (* s = Node black (Node red t1 t2 (Node black t4 t5 t6)) t7 t8) *)
    intros.
    case (lbalance (Node red t4 t5 t6) t7 t8).
    inversion H; unfold lt_tree in |- *; firstorder with In_color.
    inversion H; auto.
    inversion H; inversion H4; apply bst_color with black; auto.
    inversion H; auto.
    intros t' Ht'; exists (Node black t1 t2 t', false); intuition.
    constructor; intuition.
    inversion_clear H; inversion_clear H1; trivial.
    inversion_clear H; inversion_clear H1; trivial.
    intro; generalize (H3 y); clear H3; intuition.
    apply ME.lt_eq with t7; auto.
    inversion_clear H; apply H9; auto.
    inversion_clear H; inversion_clear H5; apply H13;
     firstorder with In_color.
    inversion_clear H; apply X.lt_trans with t7; auto.
    constructor; intuition.
    inversion_clear H1; inversion_clear H4; trivial.
    inversion H1.
    apply H2; intuition.
    inversion_clear H7; constructor; intuition.
    inversion_clear H11; trivial.
    inversion_clear H11; trivial.
    generalize (H3 y); clear H3; inversion_clear H1; intuition.
    firstorder with In_color.
    generalize (H3 y); clear H3; inversion_clear H1; intuition.
    inversion_clear H3; intuition.
    apply InRight; apply H5; apply In_color with black; trivial.
    (* s = Node black (Node black t1 t2 t3) t4 t5 *)
    intros.
    case (lbalance (Node red t1 t2 t3) t4 t5).
    inversion H; auto.
    inversion H; auto.
    inversion H; apply bst_color with black; auto.
    inversion H; auto.
    intros t' Ht'; exists (t', true); intuition.
    discriminate H5.
    inversion H1.
    apply H2; intuition.
    constructor.
    inversion_clear H7; auto.
    inversion_clear H7; auto.
    generalize (H3 y); clear H3; intuition.
    constructor 2; firstorder with In_color.
    inversion_clear H1; firstorder with In_color.
  Defined.


  (** [UnbalancedRight n t]: [t] is a tree of black height [S n]
      on its right side and [n] on its left side (the root color
      is taken into account, whathever it is) *)
     
  Inductive UnbalancedRight : nat -> tree -> Prop :=
    | URRed :
        forall (x : elt) (l r : tree) (n : nat),
        rbtree n l ->
        rbtree (S n) r -> is_not_red r -> UnbalancedRight n (Node red l x r)
    | URBlack :
        forall (x : elt) (l r : tree) (n : nat),
        rbtree n l ->
        rbtree (S n) r -> UnbalancedRight (S n) (Node black l x r).

  (** when a tree is unbalanced on its right, it can be repared *)

  Definition unbalanced_right :
    forall s : tree,
    bst s ->
    {r : tree * bool |
    let (s', b) := r in
    bst s' /\
    (is_not_red s /\ b = false -> is_not_red s') /\
    (forall n : nat,
     UnbalancedRight n s -> if b then rbtree n s' else rbtree (S n) s') /\
    (forall y : elt, In_tree y s' <-> In_tree y s)}.
  Proof.
    simple destruct s.
    (* s = Leaf => Absurd *)
    intro; exists (Leaf, false); intuition; inversion H0.
    (* s = Node c t0 t1 t2 *)
    simple induction c.
    (* s = Node red t0 t1 t2 *)
    simple destruct t2.
    (* s = Node red t0 t1 Leaf => Absurd *)
    intro; exists (Node black t0 t1 Leaf, false); intuition.
    apply bst_color with red; auto.
    inversion H0.
    inversion H6.
    apply In_color with black; auto.
    apply In_color with red; auto.
    (* s = Node red t0 t1 (Node c0 t3 t4 t5) *)
    simple induction c0.
    (* s = Node red t0 t1 (Node red t3 t4 t5) => Absurd *)
    intros; exists (Node black t0 t1 (Node red t3 t4 t5), false); intuition.
    apply bst_color with red; auto.
    inversion H0; elim H7.
    apply In_color with black; auto.
    apply In_color with red; auto.
    (* s = Node red t0 t1 (Node black t3 t4 t5) *)
    intros.
    case (rbalance t0 t1 (Node red t3 t4 t5)).
    inversion H; auto.
    inversion H; unfold gt_tree in |- *; firstorder with In_color.
    inversion H; auto.
    inversion H; apply bst_color with black; auto.
    intros t' Ht'; exists (t', false); intuition.
    elim H4.
    apply H2; intuition.
    constructor; inversion H1; auto.
    inversion_clear H9; auto.
    inversion_clear H9; auto.
    inversion_clear H1; auto.
    generalize (H3 y); clear H3; intuition.
    constructor 3; firstorder with In_color.
    inversion_clear H1; firstorder with In_color.
    (* s = Node black t0 t1 t2 *)
    simple destruct t2.
    (* s = Node black t0 t1 Leaf => Absurd *)
    intro; exists (Node black t0 t1 Leaf, false); intuition.
    inversion H0.
    inversion H6.
    (* s = Node black t0 t1 (Node c0 t3 t4 t5) *)
    simple induction c0.
    (* s = Node black t0 t1 (Node red t3 t4 t5) *)
    simple destruct t3.
    (* s = Node black t0 t1 (Node red Leaf t4 t5) => Absurd *)
    intros; exists (Node black t0 t1 (Node red Leaf t4 t5), false); intuition.
    inversion H0; inversion H6; inversion H10.
    (* s = Node black t0 t1 (Node red (Node c1 t4 t5 t6) t7 t8) *)
    simple induction c1.
    (* s = Node black t0 t1 (Node red (Node red t4 t5 t6) t7 t8) => Absurd *)
    intros;
     exists (Node black t0 t1 (Node red (Node red t4 t5 t6) t7 t8), false);
     intuition.
    inversion H0; inversion H6; elim H13. 
    (* s = Node black t0 t1 (Node red (Node black t4 t5 t6) t7 t8) *)
    intros.
    case (rbalance t0 t1 (Node red t4 t5 t6)).
    inversion H; auto.
    inversion H; unfold gt_tree in |- *; firstorder with In_color.
    inversion H; auto.
    inversion H; inversion H5; apply bst_color with black; auto.
    intros t' Ht'; exists (Node black t' t7 t8, false); intuition.
    constructor; intuition.
    inversion_clear H; inversion_clear H4; trivial.
    intro; generalize (H3 y); clear H3; intuition.
    apply ME.eq_lt with t1; auto.
    inversion_clear H; apply H10; auto.
    inversion_clear H; apply X.lt_trans with t1; auto.
    inversion_clear H; inversion_clear H8; apply H12;
     firstorder with In_color.
    inversion_clear H; inversion_clear H4; trivial.
    constructor; intuition.
    inversion H1.
    apply H2; intuition.
    inversion_clear H9; constructor; intuition.
    inversion_clear H10; trivial.
    inversion_clear H10; trivial.
    inversion_clear H1; inversion_clear H5; trivial.
    generalize (H3 y); clear H3; inversion_clear H1; intuition.
    firstorder with In_color.
    generalize (H3 y); clear H3; inversion_clear H1; intuition.
    inversion_clear H3; intuition.
    apply InLeft; apply H7; apply In_color with black; trivial.
    (* s = Node black t0 t1 (Node black t3 t4 t5) *)
    intros.
    case (rbalance t0 t1 (Node red t3 t4 t5)).
    inversion H; auto.
    inversion H; unfold gt_tree in |- *; firstorder with In_color.
    inversion H; auto.
    inversion H; apply bst_color with black; auto.
    intros t' Ht'; exists (t', true); intuition.
    discriminate H5.
    inversion H1.
    apply H2; intuition.
    constructor.
    inversion_clear H9; auto.
    inversion_clear H9; auto.
    generalize (H3 y); clear H3; intuition.
    constructor 3; firstorder with In_color.
    inversion_clear H1; firstorder with In_color.
  Defined.

  (** [remove_min s] extracts the minimum elements of [s] and indicates
      whether the black height has decreased. *)

  Definition remove_min :
    forall s : tree,
    bst s ->
    s <> Leaf ->
    {r : tree * (elt * bool) |
    let (s', r') := r in
    let (m, b) := r' in
    bst s' /\
    (is_not_red s /\ b = false -> is_not_red s') /\
    (forall n : nat,
     rbtree n s ->
     if b then (0 < n)%nat /\ rbtree (pred n) s' else rbtree n s') /\
    (forall y : elt, In_tree y s' -> E.lt m y) /\
    (forall y : elt, In_tree y s <-> E.eq y m \/ In_tree y s')}.
  Proof.
    simple induction s.
    (* s = Leaf => absurd *)
    intuition.
    (* s = Node c t0 t1 t2 *)
    simple destruct t0.
    induction  c as [| ].
    (* s = Node red Leaf t1 t2 *)
    intros; clear H H0. 
    exists (t2, (t1, false)); simpl in |- *; intuition.
    inversion_clear H1; auto.
    inversion_clear H; auto.
    inversion_clear H1; apply H5; auto.
    inversion_clear H; auto; inversion H0.
    (* s = Node black Leaf t1 t2 *)
    simple destruct t2; intros; clear H H0.
    (* s = Node black Leaf t1 Leaf *)
    exists (Leaf, (t1, true)); simpl in |- *; intuition.
    inversion_clear H; auto with arith.
    inversion_clear H; auto.
    inversion H.
    inversion_clear H; auto.
    (* s = Node black Leaf t1 (Node c t3 t4 t5) *)
    exists (Node black t3 t4 t5, (t1, false)); intuition.
    inversion_clear H1; apply bst_color with c; auto.
    induction  c as [| ].
    inversion_clear H; inversion_clear H3; auto.
    inversion_clear H; inversion H3; inversion H0.
    rewrite <- H9 in H5; discriminate H5.
    inversion_clear H1; apply H5; apply In_color with black; auto.
    inversion_clear H; auto.
    inversion H0.
    right; apply In_color with c; auto.
    apply InRight; apply In_color with black; auto.
    (* s = Node c (Node c0 t1 t2 t3) t4 t5 *)
    intros; clear H0.
    set (l := Node c0 t1 t2 t3) in *.
    case H; clear H. (* remove_min l = l',m,d *)
    inversion H1; auto.
    discriminate.
    simple destruct x; clear x; intro l'; simple destruct p; clear p;
     intros m d.
    intuition. 
    induction  d as [| ].
    (* d = true *)
    case (unbalanced_right (Node c l' t4 t5)).
    inversion H1; constructor; auto.
    intro; firstorder.
    simple destruct x; clear x; intros t' d'; intuition.
    exists (t', (m, d')); repeat split.
    intuition.
    intuition.
    induction  c as [| ]; intuition.
    (* c = red *)
    assert (0 < n)%nat.
    unfold l in H8.
    induction  c0 as [| ]; inversion H8; try apply lt_O_Sn.
    inversion H13; inversion H17.
    inversion H14; apply lt_O_Sn.
    induction  d' as [| ]; intuition.
    (* d' = true *)
    apply H7; clear H7.
    constructor; inversion_clear H8; auto.
    generalize (H0 n); intuition.
    rewrite <- (S_pred n 0 H11); auto.
    (* d' = false *)
    rewrite (S_pred n 0 H11); auto.
    apply H7; clear H7.
    constructor; inversion_clear H8; auto.
    generalize (H0 n); intuition.
    rewrite <- (S_pred n 0 H11); auto.
(* OK*)
    (* c = black *)
    assert ((n <= 1)%nat \/ (0 < pred n)%nat); [ omega | intuition ].
    (* n = 1 => absurd *)
    inversion H8.
    absurd (n <= 1)%nat; auto.
    generalize (H0 n0 H15); omega.
    (* n > 1 *)
    induction  d' as [| ]. intuition.
    (* d' = true *)
    apply H7; clear H7.
    rewrite (S_pred (pred n) 0 H12); auto.
    constructor; inversion H8; simpl in |- *; auto.
    firstorder. 
    rewrite <- (S_pred n0 0); auto. omega.
    (* d' = false *)
    rewrite (S_pred n 0); auto. 
    apply H7; clear H7.
    rewrite (S_pred (pred n) 0 H12); auto.
    constructor; inversion H8; simpl in |- *; auto.
    firstorder. 
    rewrite <- (S_pred n0 0); auto. omega.
    omega. 
    (* â y:elt,(In_tree y t') â E.lt m y *)
    intros y Hy; generalize (H10 y); clear H10; intuition.
    inversion_clear H8.
      (* y=t4 *)
      inversion H1.
      apply ME.lt_eq with t4; auto.
      apply H17; firstorder.
      (* y in l' *)
      firstorder. 
      (* y in t5 *)
      inversion H1.
      apply E.lt_trans with t4; [ apply H17 | apply H18 ]; firstorder.
    (* (In_tree y (Node c l t4 t5)) â (E.eq y m) â¨ In_tree y t' *)
    generalize (H10 y); clear H10; intuition.
    inversion_clear H10.
    firstorder. 
    generalize (H6 y); clear H6; intuition. 
    firstorder.
    (* ((E.eq y m) â¨ In_tree y t') â In_tree y (Node c l t4 t5) *)
    intuition.
    firstorder.
    generalize (H10 y); clear H10; intuition.
    inversion_clear H8; firstorder.
    (* d = false *)
    exists (Node c l' t4 t5, (m, false)); simpl in |- *; intuition.
    inversion_clear H1; constructor; auto.
    intro; generalize (H6 y); clear H6; intuition.
    inversion_clear H3; constructor; auto.
    inversion_clear H3; auto.
    inversion H1.
    apply ME.lt_eq with t4; auto.
    apply H13; firstorder.
    inversion H1.
    apply E.lt_trans with t4; [ apply H13 | apply H14 ]; firstorder.
    generalize (H6 y); clear H6; intuition.
    inversion_clear H3; intuition.
    firstorder.
    generalize (H6 y); clear H6; intuition.
    inversion_clear H7; firstorder.
  Defined.

  (** [blackify] colors the root node in [Black] *)

  Definition blackify :
    forall s : tree,
    bst s ->
    {r : tree * bool |
    let (s', b) := r in
    is_not_red s' /\
    bst s' /\
    (forall n : nat, rbtree n s -> if b then rbtree n s' else rbtree (S n) s') /\
    (forall y : elt, In_tree y s <-> In_tree y s')}.
  Proof.
    simple destruct s; intros.
    (* s = Leaf *)
    exists (Leaf, true); intuition.
    (* s = Node c t0 t1 t2 *)
    induction  c as [| ];
     [ exists (Node black t0 t1 t2, false)
     | exists (Node black t0 t1 t2, true) ]; intuition try inversion H0; auto.
    apply bst_color with red; trivial.
  Defined.

  (** [remove_aux x s] removes [x] from [s] and indicates whether the black
      height has decreased. *)

  Definition remove_aux :
    forall (x : elt) (s : tree),
    bst s ->
    {r : tree * bool |
    let (s', b) := r in
    bst s' /\
    (is_not_red s /\ b = false -> is_not_red s') /\
    (forall n : nat,
     rbtree n s ->
     if b then (0 < n)%nat /\ rbtree (pred n) s' else rbtree n s') /\
    (forall y : elt, In_tree y s' <-> ~ E.eq y x /\ In_tree y s)}.
  Proof.
    simple induction s.
    (* s = Leaf *)
    intros; exists (Leaf, false); intuition.
    inversion H0.
    (* s = Node c t0 t1 t2 *)
    intros.
    case (X.compare x t1); intro.
    (* lt x t1 *)
    clear H0; case H; clear H.
    inversion H1; trivial.
    intros (l', d); induction  d as [| ]; intuition.
      (* d = true => unbalanced_right *)
      case (unbalanced_right (Node c l' t1 t2)).
      constructor; inversion_clear H1; auto.
      intro; generalize (H4 y); intuition.
      intros (s', d'); intros; exists (s', d').
      intuition.
      clear H4 H8; induction  c as [| ].
      assert (UnbalancedRight (pred n) (Node red l' t1 t2)).
      inversion_clear H6; generalize (H0 n); constructor; intuition.
      rewrite <- (S_pred n 0); trivial.
      induction  d' as [| ]; intuition.
      inversion_clear H6; firstorder.
      rewrite (S_pred n 0); trivial. apply H5; trivial.
      inversion_clear H6; firstorder.
      assert (UnbalancedRight (pred n) (Node black l' t1 t2)).
      inversion H6; simpl in |- *; generalize (H0 n0); intuition.
      rewrite (S_pred n0 0); trivial.
      constructor; intuition.
      rewrite <- (S_pred n0 0); trivial.
      induction  d' as [| ]; intuition.
      inversion_clear H6; firstorder.
      rewrite (S_pred n 0); trivial. apply H5; trivial.
      inversion_clear H6; firstorder.
      (* In_tree y s' -> y <> x *)
      clear H0 H5.
      generalize (H8 y); clear H8; generalize (H4 y); clear H4; intuition.
      inversion_clear H4.
      apply (E.lt_not_eq (x:=x) (y:=t1)); auto.
      apply E.eq_trans with y; auto.
      intuition.
      apply (ME.lt_not_gt (x:=y) (y:=t1)); auto.
      apply ME.eq_lt with x; trivial.
      inversion_clear H1; auto.
      (* In_tree y s' -> In_tree y (Node c t0 t1 t2)) *)
      clear H0 H5.
      generalize (H8 y); clear H8; generalize (H4 y); clear H4; intuition.
      inversion_clear H4; intuition.
      (* In_tree y (Node c t0 t1 t2)) -> In_tree y s' *)
      clear H0 H5.
      generalize (H8 y); clear H8; generalize (H4 y); clear H4; intuition.
      inversion_clear H10; auto.
      (* d = false => Node c l' t1 t2, false *)
      exists (Node c l' t1 t2, false); intuition.
      inversion_clear H1; constructor; intuition.
      intro; intro; generalize (H4 y); clear H4; intuition.
      inversion_clear H2; constructor; firstorder.
      generalize (H4 y); clear H4; intuition.
      inversion_clear H2; inversion_clear H1; intuition.
      apply (E.lt_not_eq (x:=x) (y:=t1)); auto.
      apply E.eq_trans with y; auto.
      apply (ME.lt_not_gt (x:=y) (y:=t1)); auto.
      apply ME.eq_lt with x; trivial.
      generalize (H4 y); clear H4; inversion_clear H2; intuition.
      generalize (H4 y); clear H4; inversion_clear H6; intuition.
    (* eq x t1 *)
    clear H H0.
    generalize dependent t2; simple destruct t2; intros.
      (* t2 = Leaf *)
      induction  c as [| ].
      (* c = red => t0, false *)
      exists (t0, false); intuition.
      inversion_clear H1; trivial.
      inversion H0.
      inversion_clear H; trivial.
      apply (E.lt_not_eq (x:=y) (y:=t1)); auto.
      inversion_clear H1; apply H4; trivial.
      apply E.eq_trans with x; auto.
      inversion_clear H2; intuition.
      absurd (X.eq y x); auto.
      apply E.eq_trans with t1; auto.
      inversion H.
      (* c = black => blackify t0 *)
      case (blackify t0).
      inversion_clear H1; trivial.
      intros (s', d); intros; exists (s', d); intuition.
      inversion H3; induction  d as [| ]; intuition.
      generalize (H4 y); clear H4; inversion_clear H1; intuition.
      apply (E.lt_not_eq (x:=y) (y:=t1)); auto.
      apply H7; auto.
      apply E.eq_trans with x; auto.
      firstorder. 
      generalize (H4 y); clear H4; inversion_clear H6; intuition.
      absurd (X.eq y x); auto.
      apply E.eq_trans with t1; auto.
      inversion H3.
      (* t2 = Node c0 t3 t4 t5 *)
      case (remove_min (Node c0 t3 t4 t5)).
      inversion_clear H1; trivial.
      discriminate.
      intros (r', (m, d)); induction  d as [| ]; intuition.
      (* d = true => unbalanced_left *)
      case (unbalanced_left (Node c t0 m r')).
      inversion_clear H1; constructor; trivial.
      intro; intro; apply E.lt_trans with t1.
      apply H7; trivial.
      apply H8; firstorder.
      intros (s', d); intros; exists (s', d); intuition.
      clear H3 H5 H9; induction  c as [| ].
      assert (UnbalancedLeft (pred n) (Node red t0 m r')).
      inversion_clear H7; generalize (H0 n); constructor; intuition.
      rewrite <- (S_pred n 0); trivial.
      induction  d as [| ]; intuition.
      inversion_clear H7; firstorder.
      rewrite (S_pred n 0); trivial. apply H6; trivial.
      inversion_clear H7; firstorder.
      assert (UnbalancedLeft (pred n) (Node black t0 m r')).
      inversion H7; simpl in |- *; generalize (H0 n0); intuition.
      rewrite (S_pred n0 0); trivial.
      constructor; intuition.
      rewrite <- (S_pred n0 0); trivial.
      induction  d as [| ]; intuition.
      inversion_clear H7; firstorder.
      rewrite (S_pred n 0); trivial. apply H6; trivial.
      inversion_clear H7; firstorder.
      (* In_tree y s' -> y <> x *)
      clear H0 H6.
      generalize (H9 y); clear H9; generalize (H5 y); generalize (H3 y);
       clear H3; intuition.
      inversion_clear H6.
      apply (E.lt_not_eq (x:=x) (y:=m)); auto.
      inversion_clear H1.
      apply ME.eq_lt with t1; trivial.
      apply H16; firstorder.
      apply E.eq_trans with y; auto.
      apply (E.lt_not_eq (x:=y) (y:=t1)); auto.
      inversion_clear H1; apply H15; trivial.
      apply E.eq_trans with x; auto.
      intuition.
      apply (E.lt_not_eq (x:=m) (y:=y)); auto.
      apply (ME.lt_not_gt (x:=t1) (y:=m)); auto.
      inversion_clear H1.
      apply H16; firstorder.
      apply ME.lt_eq with y; trivial.
      apply E.eq_trans with x; auto.
      (* In_tree y s' -> In_tree y (Node c t0 t1 t2)) *)
      clear H0 H4 H6.
      generalize (H9 y); clear H9; generalize (H5 y); clear H5; intuition.
      inversion_clear H4; intuition.
      (* In_tree y (Node c t0 t1 t2)) -> In_tree y s' *)
      clear H0 H4 H6.
      generalize (H9 y); clear H9; generalize (H5 y); clear H5; intuition.
      inversion_clear H11; intuition.
      absurd (X.eq y x); auto.
      apply E.eq_trans with t1; auto.
      (* d = false => Node c t0 m r', false *)
      exists (Node c t0 m r', false); intuition.
      inversion_clear H1; constructor; intuition.
      intro; intro; apply E.lt_trans with t1.
      apply H7; trivial.
      generalize (H5 m); clear H5; intuition.
      apply H8; intuition.
      inversion_clear H2; constructor; firstorder.
      generalize (H5 y); intuition.
      inversion_clear H2; inversion_clear H1.
      generalize (H7 H9); intro.
      apply (E.lt_not_eq (x:=t1) (y:=y)); auto.
      apply H13; trivial.
      apply E.eq_trans with x; auto.
      apply (E.lt_not_eq (x:=y) (y:=t1)); auto.
      apply H12; trivial.
      apply E.eq_trans with x; auto.
      generalize (H10 H9); intro.
      apply (E.lt_not_eq (x:=t1) (y:=y)); auto.
      apply H13; trivial.
      apply E.eq_trans with x; auto.
      generalize (H5 y); clear H5; inversion_clear H2; intuition.
      generalize (H5 y); clear H5; inversion_clear H7; intuition.
      absurd (X.eq y x); auto.
      apply E.eq_trans with t1; auto.
     (* lt t1 x *)
    clear H; case H0; clear H0.
    inversion H1; trivial.
    intros (r', d); induction  d as [| ]; intuition.
      (* d = true => unbalanced_left *)
      case (unbalanced_left (Node c t0 t1 r')).
      constructor; inversion_clear H1; auto.
      intro; generalize (H4 y); intuition.
      intros (s', d'); intros; exists (s', d').
      intuition.
      clear H4 H8; induction  c as [| ].
      assert (UnbalancedLeft (pred n) (Node red t0 t1 r')).
      inversion_clear H6; generalize (H0 n); constructor; intuition.
      rewrite <- (S_pred n 0); trivial.
      induction  d' as [| ]; intuition.
      inversion_clear H6; firstorder.
      rewrite (S_pred n 0); trivial. apply H5; trivial.
      inversion_clear H6; firstorder.
      assert (UnbalancedLeft (pred n) (Node black t0 t1 r')).
      inversion H6; simpl in |- *; generalize (H0 n0); intuition.
      rewrite (S_pred n0 0); trivial.
      constructor; intuition.
      rewrite <- (S_pred n0 0); trivial.
      induction  d' as [| ]; intuition.
      inversion_clear H6; firstorder.
      rewrite (S_pred n 0); trivial. apply H5; trivial.
      inversion_clear H6; firstorder.
      (* In_tree y s' -> y <> x *)
      clear H0 H5.
      generalize (H8 y); clear H8; generalize (H4 y); clear H4; intuition.
      inversion_clear H4.
      apply (E.lt_not_eq (x:=t1) (y:=x)); auto.
      apply E.eq_trans with y; auto.
      apply (ME.lt_not_gt (x:=t1) (y:=y)); auto.
      apply ME.lt_eq with x; auto.
      inversion_clear H1; auto.
      intuition.
      (* In_tree y s' -> In_tree y (Node c t0 t1 t2)) *)
      clear H0 H5.
      generalize (H8 y); clear H8; generalize (H4 y); clear H4; intuition.
      inversion_clear H4; intuition.
      (* In_tree y (Node c t0 t1 t2)) -> In_tree y s' *)
      clear H0 H5.
      generalize (H8 y); clear H8; generalize (H4 y); clear H4; intuition.
      inversion_clear H10; auto.
      (* d = false => Node c t0 t1 r', false *)
      exists (Node c t0 t1 r', false); intuition.
      inversion_clear H1; constructor; intuition.
      intro; intro; generalize (H4 y); clear H4; intuition.
      inversion_clear H2; constructor; firstorder.
      generalize (H4 y); clear H4; intuition.
      inversion_clear H2; inversion_clear H1; intuition.
      apply (E.lt_not_eq (x:=t1) (y:=x)); auto.
      apply E.eq_trans with y; auto.
      apply (ME.lt_not_gt (x:=t1) (y:=y)); auto.
      apply ME.lt_eq with x; auto.
      generalize (H4 y); clear H4; inversion_clear H2; intuition.
      generalize (H4 y); clear H4; inversion_clear H6; intuition.
  Defined.

  (** [remove] is just a call to [remove_aux] *)

  Definition remove :
    forall (x : elt) (s : t),
    {s' : t | forall y : elt, In y s' <-> ~ E.eq y x /\ In y s}.
  Proof.
    intros x (s, Hs, Hrb); case (remove_aux x s).
    trivial.
    intros (s', b); intuition; clear H2.
    assert (s'rbtree : exists n : nat, rbtree n s').
    elim Hrb; clear Hrb; intros n Hn; induction  b as [| ]; firstorder.
    exists (t_intro s' H s'rbtree); unfold In in |- *; simpl in |- *;
     intuition.
  Defined.

  (** * From lists to red-black trees *)
  
  (** [of_list] builds a red-black tree from a sorted list *)

  Set Implicit Arguments.
Unset Strict Implicit.
  Record of_list_aux_Invariant (k n : Z) (l l' : list elt) 
    (r : tree) : Prop := make_olai
    {olai_bst : bst r;
     olai_rb : exists kn : nat, Z_of_nat kn = k /\ rbtree kn r;
     olai_sort : sort E.lt l';
     olai_length : Zlength l' = Zlength l - n;
     olai_same :
      forall x : elt, InList E.eq x l <-> In_tree x r \/ InList E.eq x l';
     olai_order :
      forall x y : elt, In_tree x r -> InList E.eq y l' -> E.lt x y}.
  Set Strict Implicit.
Unset Implicit Arguments.

  Lemma power_invariant :
   forall n k : Z,
   0 < k ->
   two_p k <= n + 1 <= two_p (Zsucc k) ->
   let (nn, _) := Zeven.Zsplit2 (n - 1) in
   let (n1, n2) := nn in
   two_p (Zpred k) <= n1 + 1 <= two_p k /\
   two_p (Zpred k) <= n2 + 1 <= two_p k.
  Proof.
    intros.
    case (Zeven.Zsplit2 (n - 1)).
    intros (n1, n2) X.
    generalize H0; pattern k at 1 in |- *; rewrite (Zsucc_pred k).
    rewrite two_p_S; auto with zarith.
    rewrite two_p_S; auto with zarith.
    apply Zorder.Zlt_0_le_0_pred; auto.
  Qed.

  Definition of_list_aux :
    forall k : Z,
    0 <= k ->
    forall n : Z,
    two_p k <= n + 1 <= two_p (Zsucc k) ->
    forall l : list elt,
    sort E.lt l ->
    n <= Zlength l ->
    {rl' : tree * list elt |
    let (r, l') := rl' in of_list_aux_Invariant k n l l' r}.
  Proof.
  intros k Hk; pattern k in |- *; apply natlike_rec3; try assumption.
  intro n; case (Z_eq_dec 0 n).
  (* k=0 n=0 *)
  intros Hn1 Hn2 l Hl1 Hl2; exists (Leaf, l); intuition. 
  apply make_olai; intuition.
  exists 0%nat; auto.
  inversion H2.
  inversion H1.
  (* k=0 n>0 (in fact 1) *)
  intros Hn1 Hn2.
  assert (n = 1). rewrite two_p_S in Hn2; simpl in Hn2; auto with zarith.
  rewrite H.
  intro l; case l.
   (* l = [], absurd case. *)
   intros Hl1 Hl2; unfold Zlength, Zlt in Hl2; elim Hl2; trivial.
   (* l = x::l' *)
   intros x l' Hl1 Hl2; exists (Node red Leaf x Leaf, l'); intuition.
   apply make_olai; intuition.
   exists 0%nat; auto.
   inversion Hl1; auto.   
   rewrite Zlength_cons; auto with zarith.
   inversion_clear H2; auto.
   inversion_clear H3; auto; inversion_clear H2.
   inversion_clear H2; try solve [ inversion H4 ].
   inversion_clear Hl1.
   apply ME.In_sort with l'; auto.
   eapply ME.Inf_eq; eauto.   
  (* k>0 *)
  clear k Hk; intros k Hk Hrec n Hn l Hl1 Hl2.
  rewrite <- Zsucc_pred in Hrec.
  generalize (power_invariant n k Hk).
  elim (Zeven.Zsplit2 (n - 1)); intros (n1, n2) (A, B) C.  
  elim (C Hn); clear C; intros Hn1 Hn2.
  (* First recursive call : (of_list_aux (Zpred k) n1 l) gives (lft,l') *)
  elim (Hrec n1 Hn1 l Hl1). 
  intro p; case p; clear p; intros lft l'; case l'.
   (* l' = [], absurd case. *)
   intros o; elimtype False.  
   generalize (olai_length o).
   unfold Zlength at 1 in |- *; simpl in |- *; intros X. 
   assert (n1 = Zlength l). omega. clear X.
   rewrite <- H in Hl2.
   assert (n <= n2).
     apply Zle_trans with n1; auto; inversion H; omega.
   assert (0 < n + 1).
    apply Zlt_le_trans with (two_p k).
    generalize (two_p_gt_ZERO k); omega.
    inversion_clear Hn; trivial.
   omega. 
   (* l' = x :: l'' *)
   intros x l'' o1.
   (* Second recursive call : (of_list_aux (Zpred k) n2 l'') gives (rht,l''') *)
   elim (Hrec n2 Hn2 l''); clear Hrec.
   intro p; case p; clear p; intros rht l''' o2.
   exists (Node black lft x rht, l''').   
   apply make_olai.
   (* inv1 : bst *)
   constructor; try solve [ eapply olai_bst; eauto ].
   unfold lt_tree in |- *; intros.
   apply (olai_order o1 (x:=y) (y:=x) H); auto.
   assert (sorted := olai_sort o1). 
   inversion_clear sorted.   
   unfold gt_tree in |- *; intros.
   apply ME.In_sort with l''; auto.
   elim (olai_same o2 y); auto.
   (* inv2 : rb *)  
   elim (Z_of_nat_complete k); [ intros kn; case kn | omega ].
   simpl in |- *; intros X; rewrite X in Hk; absurd (0 < 0); auto with zarith.
   clear kn; intro kn.
   exists (S kn); split; auto. 
   constructor.
   elim (olai_rb o1); intros kn' (Hkn', Hrb); rewrite Znat.inj_S in H.
   rewrite H in Hkn'; rewrite <- Zpred_succ in Hkn'.
   elim (eq_nat_dec kn kn'); intro X; [ subst | elim (Znat.inj_neq _ _ X) ];
    auto.
   elim (olai_rb o2); intros kn' (Hkn', Hrb); rewrite Znat.inj_S in H.
   rewrite H in Hkn'; rewrite <- Zpred_succ in Hkn'.
   elim (eq_nat_dec kn kn'); intro X; [ subst | elim (Znat.inj_neq _ _ X) ];
    auto.
   (* inv3 : sort *)
   exact (olai_sort o2).
   (* inv4 : length *)
   rewrite (olai_length o2).
   rewrite (Zpred_succ (Zlength l'')).
   rewrite <- (Zlength_cons x l'').
   rewrite (olai_length o1); unfold Zpred in |- *; omega.
   (* inv5 : same *)
   intro y; generalize (olai_same o1 y); generalize (olai_same o2 y).
   assert (InList E.eq y (x :: l'') <-> E.eq y x \/ InList E.eq y l'').
    split; intro H; inversion H; auto.
   generalize H; clear H A B Hn Hn1 Hn2 o1 o2.
   intuition; inversion_clear H9; intuition.
   (* inv6 : order *)  
   intros a b In_r In_l'''.
   inversion_clear In_r.
   assert (sorted := olai_sort o1).
   inversion_clear sorted.
   apply ME.eq_lt with x; auto.
   apply ME.In_sort with l''; auto.  
   generalize (olai_same o2 b); intros (_, X); auto.
   apply (olai_order o1 (x:=a) (y:=b)); auto.
   constructor 2.
   generalize (olai_same o2 b); intros (_, X); auto.
   apply (olai_order o2 (x:=a) (y:=b)); auto.
  (* misc preconditions to ensure *)
  assert (sorted := olai_sort o1); inversion_clear sorted; trivial.
  rewrite (Zpred_succ (Zlength l'')).
  rewrite <- (Zlength_cons x l'').
  rewrite (olai_length o1); unfold Zpred in |- *; omega.
  omega. 
  Defined.

  Definition of_list :
    forall l : list elt,
    sort E.lt l -> {s : t | forall x : elt, In x s <-> InList E.eq x l}. 
  Proof.
  intros.
  set (n := Zlength l) in *.
  set (k := N_digits n) in *.
  assert (0 <= n). 
   unfold n in |- *; rewrite Zlength_correct; auto with zarith.
  assert (two_p k <= n + 1 <= two_p (Zsucc k)).
    unfold k in |- *; generalize H0; case n; intros.
    rewrite two_p_S; simpl in |- *; omega.
    unfold N_digits in |- *; generalize (log_inf_correct p); omega.
    unfold Zle in H1; elim H1; auto.
  elim (of_list_aux k (ZERO_le_N_digits n) n H1 l); auto.
  intros (r, l') o.
  assert (exists n : nat, rbtree n r).
   elim (olai_rb o); intros kn Hkn; exists kn; intuition.
  exists (t_intro r (olai_bst o) H2).
  unfold In in |- *; simpl in |- *.
  intro x; generalize (olai_same o x).
  rewrite (Zlength_nil_inv l').
  intuition; inversion_clear H1.
  rewrite (olai_length o); unfold n in |- *; omega.
  unfold n in |- *; omega. 
  Qed. 
  
  (** * Elements *)

  (** [elements_tree_aux acc t] catenates the elements of [t] in infix
      order to the list [acc] *)

  Fixpoint elements_tree_aux (acc : list X.t) (t : tree) {struct t} :
   list X.t :=
    match t with
    | Leaf => acc
    | Node _ l x r => elements_tree_aux (x :: elements_tree_aux acc r) l
    end.

  (** then [elements_tree] is an instanciation with an empty [acc] *)

  Definition elements_tree := elements_tree_aux [].

  Lemma elements_tree_aux_acc_1 :
   forall (s : tree) (acc : list elt) (x : elt),
   InList E.eq x acc -> InList E.eq x (elements_tree_aux acc s).
  Proof.
    simple induction s; simpl in |- *; intuition.
  Qed.
  Hint Resolve elements_tree_aux_acc_1.

  Lemma elements_tree_aux_1 :
   forall (s : tree) (acc : list elt) (x : elt),
   In_tree x s -> InList E.eq x (elements_tree_aux acc s).
  Proof.
    simple induction s; simpl in |- *; intuition.
    inversion H.
    inversion_clear H1; firstorder.
  Qed.

  Lemma elements_tree_1 :
   forall (s : tree) (x : elt),
   In_tree x s -> InList E.eq x (elements_tree s).
  Proof.
    unfold elements_tree in |- *; intros; apply elements_tree_aux_1; auto.
  Qed.
  Hint Resolve elements_tree_1.

  Lemma elements_tree_aux_acc_2 :
   forall (s : tree) (acc : list elt) (x : elt),
   InList E.eq x (elements_tree_aux acc s) ->
   InList E.eq x acc \/ In_tree x s.
  Proof.
    simple induction s; simpl in |- *; intuition.
    elim (H _ _ H1); intuition.
    inversion_clear H2; intuition.
    elim (H0 _ _ H3); intuition.
  Qed.
  Hint Resolve elements_tree_aux_acc_2.

  Lemma elements_tree_2 :
   forall (s : tree) (x : elt),
   InList E.eq x (elements_tree s) -> In_tree x s.
  Proof.
    unfold elements_tree in |- *; intros.
    elim (elements_tree_aux_acc_2 _ _ _ H); auto.
    intros; inversion H0.
  Qed.
  Hint Resolve elements_tree_2.

  Lemma elements_tree_aux_sort :
   forall s : tree,
   bst s ->
   forall acc : list elt,
   sort E.lt acc ->
   (forall x : elt,
    InList E.eq x acc -> forall y : elt, In_tree y s -> E.lt y x) ->
   sort E.lt (elements_tree_aux acc s).
  Proof.
    simple induction s; simpl in |- *; intuition.
    apply H.
    inversion H1; auto.
    constructor. 
    apply H0; auto.
    inversion H1; auto.
    apply ME.Inf_In_2.
    replace X.eq with E.eq; replace X.lt with E.lt; auto.
    intros.
    elim (elements_tree_aux_acc_2 t2 acc y); intuition.
    inversion_clear H1.
    apply H9; auto.
    intuition.
    inversion_clear H4.
    apply ME.lt_eq with t1; auto.
    inversion_clear H1.
    apply H8; auto.
    elim (elements_tree_aux_acc_2 _ _ _ H6); intuition.
    apply E.lt_trans with t1.
    inversion_clear H1; apply H9; auto.
    inversion_clear H1; apply H10; auto.
  Qed.

  Lemma elements_tree_sort :
   forall s : tree, bst s -> sort E.lt (elements_tree s).
  Proof.
    intros; unfold elements_tree in |- *; apply elements_tree_aux_sort; auto.
    intros; inversion H0.
  Qed.
  Hint Resolve elements_tree_sort.

  Definition elements :
    forall s : t,
    {l : list elt |
    sort E.lt l /\ (forall x : elt, In x s <-> InList E.eq x l)}.
  Proof.
    intros (s, Hs, Hrb); unfold In in |- *; simpl in |- *.
    exists (elements_tree s); repeat split.
    apply elements_tree_sort; auto.
    apply elements_tree_1; auto.
    apply elements_tree_2; auto.
  Defined.

  (** * Isomorphism with [FSetList] *)

  Module Lists := FSetList.Make X.

  Definition of_slist :
    forall l : Lists.t, {s : t | forall x : elt, Lists.In x l <-> In x s}. 
  Proof.
  intros (l, Hl).
  elim (of_list l Hl); intros s Hls. 
  exists s; unfold Lists.In, Lists.Raw.In in |- *; simpl in |- *; firstorder.
  Defined.

  Definition to_slist :
    forall s : t, {l : Lists.t | forall x : elt, In x s <-> Lists.In x l}. 
  Proof.
  intro s; elim (elements s); intros l (Hl1, Hl2).
  exists (Lists.Build_slist Hl1).
  unfold Lists.In, Lists.Raw.In in |- *; simpl in |- *; firstorder.
  Defined.

  (** * Union *)

  Definition union :
    forall s s' : t,
    {s'' : t | forall x : elt, In x s'' <-> In x s \/ In x s'}.
  Proof.
  intros s s'.
  elim (to_slist s); intros l Hl.
  elim (to_slist s'); intros l' Hl'.
  elim (of_slist (Lists.union l l')); intros r Hr.
  exists r; intuition.
  elim (Lists.union_1 (s:=l) (s':=l') (x:=x)); firstorder.
  elim (Hr x); intros A _; apply A; apply (Lists.union_2 (s:=l) l' (x:=x));
   firstorder.
  elim (Hr x); intros A _; apply A; apply (Lists.union_3 l (s':=l') (x:=x));
   firstorder.
  Defined.

  (** * Intersection *)

  Lemma inter :
   forall s s' : t,
   {s'' : t | forall x : elt, In x s'' <-> In x s /\ In x s'}.
  Proof.
  intros s s'.
  elim (to_slist s); intros l Hl.
  elim (to_slist s'); intros l' Hl'.
  elim (of_slist (Lists.inter l l')); intros r Hr.
  exists r; intuition.
  elim (Hl x); intros _ A; apply A;
   apply (Lists.inter_1 (s:=l) (s':=l') (x:=x)); firstorder.
  elim (Hl' x); intros _ A; apply A;
   apply (Lists.inter_2 (s:=l) (s':=l') (x:=x)); firstorder.
  elim (Hr x); intros A _; apply A;
   apply (Lists.inter_3 (s:=l) (s':=l') (x:=x)); firstorder.
  Defined.

  (** * Difference *)

  Lemma diff :
   forall s s' : t,
   {s'' : t | forall x : elt, In x s'' <-> In x s /\ ~ In x s'}.
  Proof.
  intros s s'.
  elim (to_slist s); intros l Hl.
  elim (to_slist s'); intros l' Hl'.
  elim (of_slist (Lists.diff l l')); intros r Hr.
  exists r; intuition.
  elim (Hl x); intros _ A; apply A;
   apply (Lists.diff_1 (s:=l) (s':=l') (x:=x)); firstorder.
  elim (Lists.diff_2 (s:=l) (s':=l') (x:=x)); firstorder.  
  elim (Hr x); intros A _; apply A;
   apply (Lists.diff_3 (s:=l) (s':=l') (x:=x)); firstorder.
  Defined.

  (** * Equality test *)

Set Firstorder Depth 5.

  Lemma equal : forall s s' : t, {Equal s s'} + {~ Equal s s'}.
  Proof. 
  intros s s'.
  elim (to_slist s); intros l Hl.
  elim (to_slist s'); intros l' Hl'.
  assert (Lists.Equal l l' -> Lists.equal l l' = true). exact (Lists.equal_1 (s:=l) (s':=l')).
  assert (Lists.equal l l' = true -> Lists.Equal l l'). exact (Lists.equal_2 (s:=l) (s':=l')).
  generalize H H0; case (Lists.equal l l'); unfold Lists.Equal, Equal in |- *. 
  left; intros; generalize (H2 (refl_equal true)); firstorder.
  right; intros; intro. 
  absurd (false = true); [ auto with bool | firstorder ].
  Defined.

  (** * Inclusion test *)

  Lemma subset : forall s s' : t, {Subset s s'} + {~ Subset s s'}.
  Proof. 
  intros s s'.
  elim (to_slist s); intros l Hl.
  elim (to_slist s'); intros l' Hl'.
  assert (Lists.Subset l l' -> Lists.subset l l' = true). exact (Lists.subset_1 (s:=l) (s':=l')).
  assert (Lists.subset l l' = true -> Lists.Subset l l'). exact (Lists.subset_2 (s:=l) (s':=l')).
  generalize H H0; case (Lists.subset l l');
   unfold Lists.Subset, Subset in |- *. 
  left; intros; generalize (H2 (refl_equal true)); firstorder.  
  right; intros; intro. 
  absurd (false = true); [ auto with bool | firstorder ].
  Defined.

  (** * Fold *)

  Fixpoint fold_tree (A : Set) (f : elt -> A -> A) 
   (s : tree) {struct s} : A -> A :=
    match s with
    | Leaf => fun a => a
    | Node _ l x r => fun a => fold_tree A f l (f x (fold_tree A f r a))
    end.
  Implicit Arguments fold_tree [A].

  Definition fold_tree' (A : Set) (f : elt -> A -> A) 
    (s : tree) := Lists.Raw.fold f (elements_tree s).
  Implicit Arguments fold_tree' [A].

  Lemma fold_tree_equiv_aux :
   forall (A : Set) (s : tree) (f : elt -> A -> A) (a : A) (acc : list elt),
   Lists.Raw.fold f (elements_tree_aux acc s) a =
   fold_tree f s (Lists.Raw.fold f acc a).
  Proof.
  simple induction s.
  simpl in |- *; intuition.
  simpl in |- *; intros.
  rewrite H.
  rewrite <- H0.
  simpl in |- *; auto.
  Qed.

  Lemma fold_tree_equiv :
   forall (A : Set) (s : tree) (f : elt -> A -> A) (a : A),
   fold_tree f s a = fold_tree' f s a.
  Proof.
  unfold fold_tree', elements_tree in |- *. 
  simple induction s; simpl in |- *; auto; intros.
  rewrite fold_tree_equiv_aux.
  rewrite H0.
  simpl in |- *; auto.
  Qed.

  Definition fold :
    forall (A : Set) (f : elt -> A -> A) (s : t) (i : A),
    {r : A |
    exists l : list elt,
      Unique E.eq l /\
      (forall x : elt, In x s <-> InList E.eq x l) /\ r = fold_right f i l}.
  Proof.
    intros A f s i; exists (fold_tree f s i).
    rewrite fold_tree_equiv.
    unfold fold_tree' in |- *.
    elim (Lists.Raw.fold_1 (elements_tree_sort _ (is_bst s)) i f); intro l.
    exists l; elim H; clear H; intros H1 (H2, H3); split; auto.
    split; auto.
    intros x; generalize (elements_tree_1 s x) (elements_tree_2 s x).
    generalize (H2 x); unfold In in |- *; firstorder.
  Defined.

  (** * Cardinal *)

  Definition cardinal :
    forall s : t,
    {r : nat |
    exists l : list elt,
      Unique E.eq l /\
      (forall x : elt, In x s <-> InList E.eq x l) /\ r = length l}.
  Proof.
    intros; elim (fold nat (fun _ => S) s 0%nat); intro n; exists n.
    assert (forall l : list elt, length l = fold_right (fun _ => S) 0%nat l). 
     simple induction l; simpl in |- *; auto.
    elim p; intro l; exists l; rewrite H; auto.
  Qed.

  (** * Filter *)

  Module DLists := DepOfNodep Lists.

  Definition filter :
    forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x}) (s : t),
    {s' : t | compat_P E.eq P -> forall x : elt, In x s' <-> In x s /\ P x}.
  Proof.
  intros.
  elim (to_slist s); intros l Hl.
  elim (DLists.filter Pdec l); intros l' Hl'.
  elim (of_slist l'); intros r Hr.
  exists r.
  intros C; generalize (Hl' C); firstorder.
  Qed.

  Lemma for_all :
   forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x}) (s : t),
   {compat_P E.eq P -> For_all P s} + {compat_P E.eq P -> ~ For_all P s}.
  Proof.
  intros; unfold For_all in |- *.
  elim (to_slist s); intros l Hl.
  elim (DLists.for_all Pdec l); unfold Lists.For_all in |- *; intro H;
   [ left | right ]; intro C; generalize (H C); firstorder.
  Qed.

  Lemma exists_ :
   forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x}) (s : t),
   {compat_P E.eq P -> Exists P s} + {compat_P E.eq P -> ~ Exists P s}.
  Proof.
  intros; unfold Exists in |- *.
  elim (to_slist s); intros l Hl.
  elim (DLists.exists_ Pdec l); unfold Lists.Exists in |- *; intro H;
   [ left | right ]; intro C; generalize (H C); firstorder.
  Qed.

  Lemma partition :
   forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x}) (s : t),
   {partition : t * t |
   let (s1, s2) := partition in
   compat_P E.eq P ->
   For_all P s1 /\
   For_all (fun x => ~ P x) s2 /\
   (forall x : elt, In x s <-> In x s1 \/ In x s2)}.
  Proof.
  intros; unfold For_all in |- *.
  elim (to_slist s); intros l Hl.
  elim (DLists.partition Pdec l); unfold Lists.For_all in |- *;
   intros (l1, l2) H.
  elim (of_slist l1); intros s1 Hs1.
  elim (of_slist l2); intros s2 Hs2.
  exists (s1, s2).
  intro Comp; elim (H Comp); intros A (B, C); clear H Comp.
  intuition.
  apply A; firstorder.
  apply (B x); firstorder.
  elim (C x); intros D _; elim D; [ left | right | idtac ]; firstorder.
  firstorder.
  firstorder.
  Qed.

  (** * Minimum element *)

  Definition min_elt :
    forall s : t,
    {x : elt | In x s /\ For_all (fun y => ~ E.lt y x) s} + {Empty s}.
  Proof.
    intros (s, Hs, Hrb).
    unfold For_all, Empty, In in |- *; simpl in |- *.
    generalize Hs; clear Hs Hrb; induction  s as [| c s1 Hrecs1 t0 s0 Hrecs0];
     simpl in |- *; intros.
    (* s = Leaf *)
    right; intros; intro; inversion H.
    (* s = Node c s1 t0 s0 *)
    clear Hrecs0; generalize Hs Hrecs1; clear Hs Hrecs1; case s1; intros.
    (* s1 = Leaf *)
    left; exists t0; intuition.
    inversion_clear H.
    absurd (X.eq x t0); auto.
    inversion H1.
    inversion_clear Hs; absurd (E.lt x t0); auto.
    (* s1 = Node c0 t1 t2 t3 *)
    case Hrecs1; clear Hrecs1.
    inversion Hs; auto.
    (* a minimum for [s1] *)
    intros (m, Hm); left; exists m; intuition.
    apply (H0 x); auto.
    assert (X.lt m t0).
    inversion_clear Hs; auto.
    inversion_clear H1; auto.
    elim (X.lt_not_eq (x:=x) (y:=t0)); [ eauto | auto ].
    inversion_clear Hs.
    elim (ME.lt_not_gt (x:=x) (y:=t0)); [ eauto | auto ].
    (* non minimum for [s1] => absurd *)
    intro; right; intuition.
    apply (n t2); auto.
  Defined.

  (** * Maximum element *)

  Definition max_elt :
    forall s : t,
    {x : elt | In x s /\ For_all (fun y => ~ E.lt x y) s} + {Empty s}.
   Proof.
    intros (s, Hs, Hrb).
    unfold For_all, Empty, In in |- *; simpl in |- *.
    generalize Hs; clear Hs Hrb; induction  s as [| c s1 Hrecs1 t0 s0 Hrecs0];
     simpl in |- *; intros.
    (* s = Leaf *)
    right; intros; intro; inversion H.
    (* s = Node c s1 t0 s0 *)
    clear Hrecs1; generalize Hs Hrecs0; clear Hs Hrecs0; case s0; intros.
    (* s0 = Leaf *)
    left; exists t0; intuition.
    inversion_clear H.
    absurd (X.eq x t0); auto.
    inversion_clear Hs; absurd (E.lt t0 x); auto.
    inversion H1.
    (* s0 = Node c0 t1 t2 t3 *)
    case Hrecs0; clear Hrecs0.
    inversion Hs; auto.
    (* a maximum for [s0] *)
    intros (m, Hm); left; exists m; intuition.
    apply (H0 x); auto.
    assert (X.lt t0 m).
    inversion_clear Hs; auto.
    inversion_clear H1; auto.
    elim (X.lt_not_eq (x:=x) (y:=t0)); [ eauto | auto ].
    inversion_clear Hs.
    elim (ME.lt_not_gt (x:=t0) (y:=x)); [ eauto | auto ].
    (* non maximum for [s0] => absurd *)
    intro; right; intuition.
    apply (n t2); auto.
  Defined.

  (** * Any element *)

  Definition choose : forall s : t, {x : elt | In x s} + {Empty s}.
  Proof.
    intros (s, Hs, Hrb); unfold Empty, In in |- *; simpl in |- *; case s;
     intuition.
    right; intros; inversion H.
    left; exists t1; auto.
  Defined.

  (** * Comparison *)
  
  Definition eq : t -> t -> Prop := Equal.

  Definition lt (s s' : t) : Prop :=
    let (l, _) := to_slist s in let (l', _) := to_slist s' in Lists.lt l l'.

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

  Lemma lt_trans : forall s s' s'' : t, lt s s' -> lt s' s'' -> lt s s''.
  Proof.
    intros s s' s''; unfold lt in |- *.
    elim (to_slist s); intros l Hl.
    elim (to_slist s'); intros l' Hl'.
    elim (to_slist s''); intros l'' Hl''.
    exact (Lists.lt_trans (s:=l) (s':=l') (s'':=l'')).
  Qed.

  Definition eql (s s' : t) : Prop :=
    let (l, _) := to_slist s in let (l', _) := to_slist s' in Lists.eq l l'.

  Lemma eq_eql : forall s s' : t, eq s s' -> eql s s'.
  Proof.
    unfold eq, Equal, eql, Lists.eq, Lists.Raw.eq, Lists.Raw.Equal in |- *.
    intros s s'.
    elim (to_slist s); unfold Lists.In, Lists.Raw.In in |- *; simpl in |- *;
     intros l Hl.
    elim (to_slist s'); unfold Lists.In, Lists.Raw.In in |- *; simpl in |- *;
     intros l' Hl'.
    firstorder.
   Qed.

  Lemma eql_eq : forall s s' : t, eql s s' -> eq s s'.
  Proof.
    unfold eq, Equal, eql, Lists.eq, Lists.Raw.eq, Lists.Raw.Equal in |- *.
    intros s s'.
    elim (to_slist s); unfold Lists.In, Lists.Raw.In in |- *; simpl in |- *;
     intros l Hl.
    elim (to_slist s'); unfold Lists.In, Lists.Raw.In in |- *; simpl in |- *;
     intros l' Hl'.
    firstorder.
  Qed.

  Lemma lt_not_eq : forall s s' : t, lt s s' -> ~ eq s s'.
  Proof.
    intros s s' H; intro.
    generalize (eq_eql s s' H0).
    generalize H; unfold lt, eql in |- *.
    elim (to_slist s); intros l Hl.
    elim (to_slist s'); intros l' Hl'.
    exact (Lists.lt_not_eq (s:=l) (s':=l')).
  Qed.
  
  Definition compare : forall s s' : t, Compare lt eq s s'.
  Proof.
    intros s s'.
    cut (lt s s' -> Compare lt eq s s').    
    cut (eq s s' -> Compare lt eq s s'). 
    cut (lt s' s -> Compare lt eq s s'). 
    unfold lt at 1 4 in |- *.
    generalize (eql_eq s s'); unfold eql in |- *.
    elim (to_slist s); intros l Hl.
    elim (to_slist s'); intros l' Hl'.
    elim (Lists.compare l l'); intuition.
    constructor 3; trivial.
    constructor 2; trivial.
    constructor 1; trivial.
  Defined.

End Make.


