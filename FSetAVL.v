
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

(** This module implements sets using AVL trees.
    It follows the implementation from Ocaml's standard library. *)

Require Import FSetInterface.
Require Import FSetList.

Require Import ZArith.
Open Scope Z_scope.

Set Firstorder Depth 3.

Module Make (X: OrderedType) : Sdep with Module E := X.

  Module E := X.
  Module ME := OrderedTypeFacts X.

  Definition elt := X.t.

  (** * Trees *)

  Inductive tree : Set :=
    | Leaf : tree
    | Node : tree -> X.t -> tree -> Z -> tree.

  (** The fourth field of [Node] is the height of the tree *)

  (** * Occurrence in a tree *)

  Inductive In_tree (x : elt) : tree -> Prop :=
    | IsRoot :
        forall (l r : tree) (h : Z) (y : elt),
        X.eq x y -> In_tree x (Node l y r h)
    | InLeft :
        forall (l r : tree) (h : Z) (y : elt),
        In_tree x l -> In_tree x (Node l y r h)
    | InRight :
        forall (l r : tree) (h : Z) (y : elt),
        In_tree x r -> In_tree x (Node l y r h).

  Hint Constructors In_tree.

  (** [In_tree] is compatible with [X.eq] *)

  Lemma eq_In_tree :
   forall (s : tree) (x y : elt), E.eq x y -> In_tree x s -> In_tree y s.
  Proof.
    simple induction s; simpl in |- *; intuition.
    inversion_clear H0.
    inversion_clear H2; intuition eauto.
  Qed.

  (** [In_tree] is height-insensitive *)

  Lemma In_height :
   forall (h h' : Z) (x y : elt) (l r : tree),
   In_tree y (Node l x r h) -> In_tree y (Node l x r h').
  Proof.
    inversion 1; auto.
  Qed.
  Hint Resolve In_height.

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
   forall (x y : elt) (l r : tree) (h : Z),
   lt_tree x l -> lt_tree x r -> X.lt y x -> lt_tree x (Node l y r h).
  Proof.
    unfold lt_tree in |- *; intuition.
    inversion_clear H2; intuition.
    apply ME.eq_lt with y; auto.
  Qed.

  Lemma gt_tree_node :
   forall (x y : elt) (l r : tree) (h : Z),
   gt_tree x l -> gt_tree x r -> E.lt x y -> gt_tree x (Node l y r h).
  Proof.
    unfold gt_tree in |- *; intuition.
    inversion_clear H2; intuition.
    apply ME.lt_eq with y; auto.
  Qed.

  Hint Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.

  Lemma lt_node_lt :
   forall (x y : elt) (l r : tree) (h : Z),
   lt_tree x (Node l y r h) -> E.lt y x.
  Proof.
    intros; apply H; auto.
  Qed.

  Lemma gt_node_gt :
   forall (x y : elt) (l r : tree) (h : Z),
   gt_tree x (Node l y r h) -> E.lt x y.
  Proof.
    intros; apply H; auto.
  Qed.

  Lemma lt_left :
   forall (x y : elt) (l r : tree) (h : Z),
   lt_tree x (Node l y r h) -> lt_tree x l.
  Proof.
    intros; red in |- *; intros; apply H; auto.
  Qed.

  Lemma lt_right :
   forall (x y : elt) (l r : tree) (h : Z),
   lt_tree x (Node l y r h) -> lt_tree x r.
  Proof.
    intros; red in |- *; intros; apply H; auto.
  Qed.

  Lemma gt_left :
   forall (x y : elt) (l r : tree) (h : Z),
   gt_tree x (Node l y r h) -> gt_tree x l.
  Proof.
    intros; red in |- *; intros; apply H; auto.
  Qed.

  Lemma gt_right :
   forall (x y : elt) (l r : tree) (h : Z),
   gt_tree x (Node l y r h) -> gt_tree x r.
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
        forall (x : elt) (l r : tree) (h : Z),
        bst l -> bst r -> lt_tree x l -> gt_tree x r -> bst (Node l x r h).

  Hint Constructors bst.

  (** Results about [bst] *)
 
  Lemma bst_left :
   forall (x : elt) (l r : tree) (h : Z), bst (Node l x r h) -> bst l.
  Proof.
    intros x l r h H; inversion H; auto.
  Qed.

  Lemma bst_right :
   forall (x : elt) (l r : tree) (h : Z), bst (Node l x r h) -> bst r.
  Proof.
    intros x l r h H; inversion H; auto.
  Qed.

  Implicit Arguments bst_left. Implicit Arguments bst_right.
  Hint Resolve bst_left bst_right.

  Lemma bst_height :
   forall (h h' : Z) (x : elt) (l r : tree),
   bst (Node l x r h) -> bst (Node l x r h').
  Proof.
    inversion 1; auto.
  Qed.
  Hint Resolve bst_height.

  (** Key fact about binary search trees: rotations preserve the 
      [bst] property *)

  Lemma rotate_left :
   forall (x y : elt) (a b c : tree) (h1 h2 h3 h4 : Z),
   bst (Node a x (Node b y c h2) h1) -> bst (Node (Node a x b h4) y c h3).
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
   forall (x y : elt) (a b c : tree) (h1 h2 h3 h4 : Z),
   bst (Node (Node a x b h4) y c h3) -> bst (Node a x (Node b y c h2) h1).
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

  (** * AVL trees *)

  (** [avl s] : [s] is a properly balanced AVL tree,
      i.e. for any node the heights of the two children
      differ by at most 2 *)

  Definition height (s : tree) : Z :=
    match s with
    | Leaf => 0
    | Node _ _ _ h => h
    end.

  Definition max (x y : Z) : Z :=
    if Z_lt_ge_dec x y then y else x.

  (** Instead of writing [h = 1 + (max (height l) (height r))] we prefer 
      the following relation [height_of_node l r h] to ease the use of 
      [Omega] *)

  Definition height_of_node (l r : tree) (h : Z) :=
    height l >= height r /\ h = height l + 1 \/
    height r >= height l /\ h = height r + 1.

  Inductive avl : tree -> Prop :=
    | RBLeaf : avl Leaf
    | RBNode :
        forall (x : elt) (l r : tree) (h : Z),
        avl l ->
        avl r ->
        -2 <= height l - height r <= 2 ->
        height_of_node l r h -> avl (Node l x r h).

  Hint Constructors avl.

 (** Results about [avl] *)

  Lemma avl_left :
   forall (x : elt) (l r : tree) (h : Z), avl (Node l x r h) -> avl l.
  Proof.
    intros x l r h H; inversion_clear H; intuition.
  Qed.

  Lemma avl_right :
   forall (x : elt) (l r : tree) (h : Z), avl (Node l x r h) -> avl l.
  Proof.
    intros x l r c H; inversion_clear H; intuition.
  Qed.

  Implicit Arguments avl_left. Implicit Arguments avl_right.
  Hint Resolve avl_left avl_right.

  Ltac MaxCase x y :=
    unfold max in |- *; case (Z_lt_ge_dec x y); simpl in |- *.

  Lemma avl_node :
   forall (x : elt) (l r : tree),
   avl l ->
   avl r ->
   -2 <= height l - height r <= 2 ->
   avl (Node l x r (max (height l) (height r) + 1)).
  Proof.
    intros; constructor; unfold height_of_node in |- *;
     MaxCase (height l) (height r); intuition.
  Qed.
  Hint Resolve avl_node.

  (** The [AVL] tactic *)

  Lemma height_non_negative : forall s : tree, avl s -> height s >= 0.
  Proof.
    simple induction s; simpl in |- *; intros.
    omega.
    inversion_clear H1; unfold height_of_node in H5; intuition.
  Qed.
  
  Lemma height_equation :
   forall (l r : tree) (x : elt) (h : Z),
   avl (Node l x r h) ->
   -2 <= height l - height r <= 2 /\
   (height l >= height r /\ h = height l + 1 \/
    height r >= height l /\ h = height r + 1).
  Proof.
    inversion 1; intuition.
  Qed.

  Implicit Arguments height_non_negative. 
  Implicit Arguments height_equation.

  (** If [h] is a proof of [avl (Node l x r h)], then tactic
      [AVL h] is adding all information about [h] to the context *)
  Ltac AVL h :=
    generalize (height_non_negative h); try simpl in |- *;
     try generalize (height_equation h); intros.

  (** * Sets as AVL trees *)

  (** A set is implement as a record [t], containing a tree, 
      a proof that it is a binary search tree and a proof that it is 
      a properly balanced AVL tree *)

  Record t_ : Set := t_intro
    {the_tree :> tree; is_bst : bst the_tree; is_avl : avl the_tree}.
  Definition t := t_.

  (** Projections *)

  Lemma t_is_bst : forall s : t, bst s.
  Proof.
    simple destruct s; auto.
  Qed.
  Hint Resolve t_is_bst.

  Lemma t_is_avl : forall s : t, avl s.
  Proof.
    simple destruct s; auto.
  Qed.
  Hint Resolve t_is_avl.

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
     intuition clear is_bst0 is_avl0.
    induction  the_tree0
     as [| the_tree0_1 Hrecthe_tree0_1 t0 the_tree0_0 Hrecthe_tree0_0 z];
     inversion_clear H0; intuition.
    apply IsRoot; eauto.
  Qed.

  Hint Resolve eq_In.

  (** * Empty set *)

  Definition t_empty : t.
  Proof.
    exists Leaf; auto.
  Defined.

  Definition empty : {s : t | forall x : elt, ~ In x s}. 
  Proof.
    exists t_empty.
    unfold In in |- *; red in |- *; intros.
    inversion H.
  Qed.

  (** * Emptyness test *)

  Definition is_empty : forall s : t, {Empty s} + {~ Empty s}.
  Proof.
    unfold Empty, In in |- *; simple destruct s; simple destruct the_tree0;
     simpl in |- *; intros.
    left; auto.
    right; intuition.
    apply (H t1); auto.
  Qed.

  (** * Appartness *)

  (** The [mem] function is deciding appartness. It exploits the [bst] property
      to achieve logarithmic complexity. *)

  Definition mem : forall (x : elt) (s : t), {In x s} + {~ In x s}.
  Proof.
    intros x (s, Hs, Ha).
    unfold In in |- *; simpl in |- *; clear Ha.
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
  Qed.

  (** * Singleton set *)

  Definition singleton_tree (x : elt) := Node Leaf x Leaf 1.

  Lemma singleton_bst : forall x : elt, bst (singleton_tree x).
  Proof.
    unfold singleton_tree in |- *; auto.
  Qed.

  Lemma singleton_avl : forall x : elt, avl (singleton_tree x).
  Proof.
    unfold singleton_tree in |- *; intro.
    constructor; auto; unfold height_of_node, height in |- *; simpl in |- *;
     omega.
  Qed.

  Definition singleton :
    forall x : elt, {s : t | forall y : elt, In y s <-> E.eq x y}.
  Proof.
    intro x;
     exists (t_intro (singleton_tree x) (singleton_bst x) (singleton_avl x)).
    unfold In, singleton_tree in |- *; simpl in |- *; intuition.
    inversion_clear H; auto; inversion H0.
  Qed.

  (** * Helper functions *)

  (** [create l x r] creates a node, assuming [l] and [r]
      to be balanced and [|height l - height r| <= 2]. *)

  Definition create :
    forall (l : tree) (x : elt) (r : tree),
    bst l ->
    avl l ->
    bst r ->
    avl r ->
    lt_tree x l ->
    gt_tree x r ->
    -2 <= height l - height r <= 2 ->
    {s : tree |
    bst s /\
    avl s /\
    height_of_node l r (height s) /\
    (forall y : elt, In_tree y s <-> X.eq y x \/ In_tree y l \/ In_tree y r)}.
  Proof.
    unfold height_of_node in |- *; intros.
    exists (Node l x r (max (height l) (height r) + 1)).
    intuition.
    MaxCase (height l) (height r); intuition.
    inversion_clear H5; intuition.
  Qed.

  (** [bal l x r] acts as [create], but performs one step of
      rebalancing if necessary, i.e. assumes [|height l - height r| <= 3]. *)

  Definition bal :
    forall (l : tree) (x : elt) (r : tree),
    bst l ->
    avl l ->
    bst r ->
    avl r ->
    lt_tree x l ->
    gt_tree x r ->
    -3 <= height l - height r <= 3 ->
    {s : tree |
    bst s /\
    avl s /\
    
    (* height may be decreased by 1 *)
    ((height_of_node l r (height s) \/ height_of_node l r (height s + 1)) /\
     
     (* ...but is unchanged when no rebalancing *)
     (-2 <= height l - height r <= 2 -> height_of_node l r (height s))) /\
    
    (* elements are those of (l,x,r) *)
    (forall y : elt, In_tree y s <-> X.eq y x \/ In_tree y l \/ In_tree y r)}.
  Proof.
    intros l x r bst_l avl_l bst_r avl_r; simpl in |- *.
    intros Hl Hr Hh.
    set (hl := height l) in *.
    set (hr := height r) in *.
    case (Z_gt_le_dec hl (hr + 2)); intro.
    (* hl > hr + 2 *)
    destruct l as [| t0 t1 t2 z0].
    (* l = Leaf => absurd *)
    simpl in (value of hl); unfold hl in |- *.
    absurd (hl > hr + 2); trivial.
    generalize (height_non_negative avl_r).
    unfold hl, hr in |- *; omega.
    (* l = Node t0 t1 t2 z0 *)
    case (Z_ge_lt_dec (height t0) (height t2)); intro.
    (* height t0 >= height t2 *)
    case (create t2 x r); auto.
    inversion_clear bst_l; trivial. 
    inversion_clear avl_l; trivial.
    generalize Hh z; clear Hh z; simpl in (value of hl);
     unfold hl, hr in |- *.
    AVL avl_l; AVL avl_r; intuition try omega.
    intro t2xr; intuition.
    case (create t0 t1 t2xr).
    inversion_clear bst_l; trivial. 
    inversion_clear avl_l; trivial.
    intuition.
    intuition.
    inversion_clear bst_l; trivial.     
    inversion_clear bst_l; trivial. 
    clear H2; intro; intro; intuition; generalize (H5 y); intuition.
    apply ME.lt_eq with x; auto. 
    apply E.lt_trans with x; auto.
    apply Hl; auto.
    apply Hr; auto.
    clear H5.
    generalize z H H0; clear z H H0; simpl in (value of hl);
     unfold hl, hr in |- *.
    unfold height_of_node in H2; AVL avl_l; AVL H3; omega.
    intros s (s_bst, (s_avl, (Hs1, Hs2))).
    exists s; simpl in |- *.
    do 3 (split; trivial).
    unfold height_of_node in |- *; simpl in |- *.
    clear H5 Hs2.
    generalize z H H0; clear z H H0; simpl in (value of hl);
     unfold hl, hr in |- *.
    unfold height_of_node in H2, Hs1; AVL avl_l; AVL H3; AVL s_avl; omega.
    intuition; generalize (Hs2 y); generalize (H5 y); clear Hs2 H5; intuition.
    inversion_clear H4; intuition.
    (* height t0 < height t2 *)
    destruct t2 as [| t2 t3 t4 z2].
    (* t2 = Leaf => absurd *)
    simpl in z1.
    absurd (height t0 < 0); trivial.
    inversion_clear avl_l; AVL ipattern:H; omega.
    (* t2 = Node t2 t3 t4 z2 *)
    case (create t4 x r); auto.
    inversion_clear bst_l; inversion_clear H0; auto.
    inversion_clear avl_l; inversion_clear H0; auto.
    generalize z Hh; clear z Hh; simpl in (value of hl);
     unfold hl, hr in |- *.
    simpl in z1; AVL avl_l; simpl in H.
    inversion_clear avl_l; unfold height_of_node in H4; simpl in H3, H4.
    AVL H2; omega.
    intros r' (r'_bst, (r'_avl, (r'_h1, r'_h2))).
    case (create t0 t1 t2).
    inversion_clear bst_l; trivial.
    inversion_clear avl_l; trivial.
    inversion_clear bst_l; inversion_clear H0; trivial.
    inversion_clear avl_l; inversion_clear H0; trivial.
    inversion_clear bst_l; trivial.
    inversion_clear bst_l; intro; intro; apply H2; eauto.
    generalize z Hh; clear z Hh; simpl in (value of hl);
     unfold hl, hr in |- *.
    simpl in z1; AVL avl_l; simpl in H.
    inversion_clear avl_l; unfold height_of_node in H4; simpl in H3, H4.
    AVL H2; omega.
    intros l' (l'_bst, (l'_avl, (l'_h1, l'_h2))).
    case (create l' t3 r'); auto.
    inversion_clear bst_l; inversion_clear H0.
    intro; intro; generalize (l'_h2 y); clear l'_h2; intuition.
    apply ME.eq_lt with t1; auto.
    apply E.lt_trans with t1; [ apply H1 | apply H2 ]; auto.
    inversion_clear bst_l; inversion_clear H0.
    intro; intro; generalize (r'_h2 y); clear r'_h2; intuition.
    apply ME.lt_eq with x; auto.
    apply E.lt_trans with x; [ apply Hl | apply Hr ]; auto.
    generalize z Hh; clear z Hh; simpl in (value of hl);
     unfold hl, hr in |- *.
    simpl in z1; AVL avl_l; simpl in H.
    inversion_clear avl_l; unfold height_of_node in H4; simpl in H3, H4.
    AVL H2; unfold height_of_node in r'_h1, l'_h1; omega.
    intros s (s_bst, (s_avl, (s_h1, s_h2))).
    exists s; simpl in |- *; do 3 (split; trivial).
    clear r'_h2 l'_h2 s_h2.
    generalize z Hh; clear z Hh; simpl in (value of hl);
     unfold hl, hr in |- *.
    AVL avl_l; inversion_clear avl_l.
    AVL H2; unfold height_of_node in H4; simpl in H4.
    unfold height_of_node in |- *; simpl in |- *.
    unfold height_of_node in s_h1, r'_h1, l'_h1; simpl in |- *.
    simpl in z1; AVL r'_avl; AVL l'_avl; simpl in H.
    clear bst_l bst_r avl_r Hl Hr hl hr r'_bst r'_avl l'_bst l'_avl s_bst
     s_avl H1 H2; intuition omega. (* 9 seconds *)
    intro y; generalize (r'_h2 y); generalize (l'_h2 y); generalize (s_h2 y);
     clear r'_h2 l'_h2 s_h2; intuition.
    inversion_clear H10; intuition.
    inversion_clear H14; intuition.
    (* hl <= hr + 2 *)
    case (Z_gt_le_dec hr (hl + 2)); intro.
    (* hr > hl + 2 *)
    destruct r as [| t0 t1 t2 z1].
    (* r = Leaf => absurd *)
    simpl in (value of hr); unfold hr in |- *.
    absurd (hr > hl + 2); trivial.
    AVL avl_l; unfold hl, hr in |- *; omega.
    (* r = Node t0 t1 t2 z0 *)
    case (Z_ge_lt_dec (height t2) (height t0)); intro.
    (* height t2 >= height t0 *)
    case (create l x t0); auto.
    inversion_clear bst_r; trivial. 
    inversion_clear avl_r; trivial.
    generalize Hh z z0; clear Hh z z0; simpl in (value of hr);
     unfold hl, hr in |- *.
    AVL avl_l; AVL avl_r; intuition try omega.
    intro lxt0; intuition.
    case (create lxt0 t1 t2); auto.
    inversion_clear bst_r; trivial. 
    inversion_clear avl_r; trivial.
    clear H2; intro; intro; intuition; generalize (H5 y); intuition.
    apply ME.eq_lt with x; auto. 
    apply E.lt_trans with x; [ apply Hl | apply Hr ]; auto.
    inversion_clear bst_r; auto. 
    inversion_clear bst_r; auto. 
    clear H5.
    generalize z z0 H H0; clear z z0 H H0; simpl in (value of hr);
     unfold hl, hr in |- *.
    unfold height_of_node in H2; AVL avl_r; AVL H3; omega.
    intros s (s_bst, (s_avl, (Hs1, Hs2))).
    exists s; simpl in |- *; do 3 (split; trivial).
    unfold height_of_node in |- *; simpl in |- *.
    clear H5 Hs2.
    generalize z z0 H H0; clear z z0 H H0; simpl in (value of hr);
     unfold hl, hr in |- *.
    unfold height_of_node in H2, Hs1; AVL avl_r; AVL H3; AVL s_avl; omega.
    intuition; generalize (Hs2 y); generalize (H5 y); clear Hs2 H5; intuition.
    inversion_clear H4; intuition.
    (* height t2 < height t0 *)
    destruct t0 as [| t0 t3 t4 z3].
    (* t0 = Leaf => absurd *)
    simpl in z2.
    absurd (height t2 < 0); trivial.
    inversion_clear avl_r; AVL ipattern:H0; omega.
    (* t0 = Node t0 t3 t4 z2 *)
    case (create l x t0); auto.
    inversion_clear bst_r; inversion_clear H; auto.
    inversion_clear avl_r; inversion_clear H; auto.
    generalize z z0 Hh; clear z z0 Hh; simpl in (value of hr);
     unfold hl, hr in |- *.
    simpl in z2; AVL avl_r; simpl in H.
    inversion_clear avl_r; unfold height_of_node in H4; simpl in H3, H4.
    AVL H1; omega.
    intros l' (l'_bst, (l'_avl, (l'_h1, l'_h2))).
    case (create t4 t1 t2).
    inversion_clear bst_r; inversion_clear H; trivial.
    inversion_clear avl_r; inversion_clear H; trivial.
    inversion_clear bst_r; trivial.
    inversion_clear avl_r; trivial.
    inversion_clear bst_r; intro; intro; apply H1; eauto.
    inversion_clear bst_r; trivial.
    generalize z z0 Hh; clear z z0 Hh; simpl in (value of hr);
     unfold hl, hr in |- *.
    simpl in z2; AVL avl_r; simpl in H.
    inversion_clear avl_r; unfold height_of_node in H4; simpl in H3, H4.
    AVL H1; omega.
    intros r' (r'_bst, (r'_avl, (r'_h1, r'_h2))).
    case (create l' t3 r'); auto.
    inversion_clear bst_r; inversion_clear H.
    intro; intro; generalize (l'_h2 y); clear l'_h2; intuition.
    apply ME.eq_lt with x; auto.
    apply E.lt_trans with x; [ apply Hl | apply Hr ]; auto.
    inversion_clear bst_r; inversion_clear H.
    intro; intro; generalize (r'_h2 y); clear r'_h2; intuition.
    apply ME.lt_eq with t1; auto.
    apply E.lt_trans with t1; [ apply H1 | apply H2 ]; auto.
    generalize z z0 Hh; clear z z0 Hh; simpl in (value of hr);
     unfold hl, hr in |- *.
    simpl in z2; AVL avl_r; simpl in H.
    inversion_clear avl_r; unfold height_of_node in H4; simpl in H3, H4.
    AVL H1; unfold height_of_node in r'_h1, l'_h1; omega.
    intros s (s_bst, (s_avl, (s_h1, s_h2))).
    exists s; simpl in |- *; do 3 (split; trivial).
    clear r'_h2 l'_h2 s_h2.
    generalize z z0 Hh; clear z z0 Hh; simpl in (value of hr);
     unfold hl, hr in |- *.
    AVL avl_r; inversion_clear avl_r.
    AVL H1; unfold height_of_node in H4; simpl in H4.
    unfold height_of_node in |- *; simpl in |- *.
    unfold height_of_node in s_h1, r'_h1, l'_h1; simpl in |- *.
    simpl in z2; AVL r'_avl; AVL l'_avl; simpl in H.
    clear bst_l bst_r avl_l Hl Hr hl hr r'_bst r'_avl l'_bst l'_avl s_bst
     s_avl H1 H2; intuition omega. (* 9 seconds *)
    intro y; generalize (r'_h2 y); generalize (l'_h2 y); generalize (s_h2 y);
     clear r'_h2 l'_h2 s_h2; intuition.
    inversion_clear H10; intuition.
    inversion_clear H14; intuition.
    (* hr <= hl + 2 *)
    set (s := Node l x r (max (height l) (height r) + 1)) in *.
    assert (bst s). 
    unfold s in |- *; auto.
    assert (avl s). 
    unfold s in |- *; constructor; auto.
    generalize z z0; unfold hl, hr in |- *; intros; omega.
    unfold height_of_node in |- *; MaxCase (height l) (height r); intros;
     omega.
    exists s; unfold s, height_of_node in |- *; simpl in |- *;
     do 3 (split; trivial).
    generalize z z0; unfold hl, hr in |- *; MaxCase (height l) (height r);
     intros; omega.
    intuition; inversion_clear H3; intuition.
  Qed.

  (** * Insertion *)

  Definition add_tree :
    forall (x : elt) (s : tree),
    bst s ->
    avl s ->
    {s' : tree |
    bst s' /\
    avl s' /\
    0 <= height s' - height s <= 1 /\
    (forall y : elt, In_tree y s' <-> E.eq y x \/ In_tree y s)}.
  Proof.
    simple induction s; simpl in |- *; intros.
    (* s = Leaf *)
    exists (Node Leaf x Leaf 1); simpl in |- *; intuition.
    constructor; unfold height_of_node in |- *; simpl in |- *;
     intuition try omega.
    inversion_clear H1; intuition.
    (* s = Node t0 t1 t2 *)
    case (X.compare x t1); intro.
    (* x < t1 *)
    clear H0; case H; clear H.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    intro l'; simpl in |- *; intuition.
    case (bal l' t1 t2); auto.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    intro; intro; generalize (H5 y); clear H5; intuition.
    apply ME.eq_lt with x; auto.
    inversion_clear H1; auto.
    inversion_clear H1; auto.
    clear H5; AVL H2; AVL H3; intuition.
    intros s' (s'_bst, (s'_avl, (s'_h1, s'_h2))).
    exists s'; simpl in |- *; do 3 (split; trivial).
    clear s'_h2 H; unfold height_of_node in s'_h1.
    AVL H2; AVL H3; AVL s'_avl. omega.
    clear s'_h1; intro.
    generalize (s'_h2 y) (H5 y); clear s'_h2 H5; intuition.
    inversion_clear H13; intuition.
    (* x = t1 *)
    clear H H0.
    exists (Node t0 t1 t2 z); simpl in |- *; intuition.
    apply IsRoot; apply E.eq_trans with x; auto.
    (* x > t1 *)
    clear H; case H0; clear H0.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    intros r' (r'_bst, (r'_avl, H3)); simpl in |- *; intuition.
    case (bal t0 t1 r'); auto.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    intro; intro; generalize (H0 y); clear H0; intuition.
    inversion_clear H1; auto.
    intro; intro; generalize (H0 y); clear H0; intuition.
    apply ME.lt_eq with x; auto.
    inversion_clear H1; auto.
    clear H0; AVL H2; AVL r'_avl; intuition.
    intros s' (s'_bst, (s'_avl, (s'_h1, s'_h2))).
    exists s'; simpl in |- *; do 3 (split; trivial).
    clear s'_h2 H0; unfold height_of_node in s'_h1.
    AVL H2; AVL r'_avl; AVL s'_avl; omega.
    clear s'_h1; intro.
    generalize (s'_h2 y) (H0 y); clear s'_h2 H0; intuition.
    inversion_clear H11; intuition.
  Qed.

  Definition add : forall (x : elt) (s : t), {s' : t | Add x s s'}.
  Proof.
    intros x (s, s_bst, s_avl); unfold Add, In in |- *.
    case (add_tree x s); trivial.
    intros s' (s'_bst, (s'_avl, Hs')).
    exists (t_intro s' s'_bst s'_avl); intuition.
  Qed.

  (** * Join

      Same as [bal] but does not assumme anything regarding heights
      of [l] and [r]. Code is
<<
    let rec join l v r =
      match (l, r) with
        (Empty, _) -> add v r
      | (_, Empty) -> add v l
      | (Node(ll, lv, lr, lh), Node(rl, rv, rr, rh)) ->
          if lh > rh + 2 then bal ll lv (join lr v r) else
          if rh > lh + 2 then bal (join l v rl) rv rr else
          create l v r
>>
  *)

  Definition join :
    forall (l : tree) (x : elt) (r : tree),
    bst l ->
    avl l ->
    bst r ->
    avl r ->
    lt_tree x l ->
    gt_tree x r ->
    {s : tree |
    bst s /\
    avl s /\
    (height_of_node l r (height s) \/ height_of_node l r (height s + 1)) /\
    (forall y : elt, In_tree y s <-> X.eq y x \/ In_tree y l \/ In_tree y r)}.
  Proof.
    simple induction l; simpl in |- *.
    (* l = Leaf *)
    intros; case (add_tree x r); trivial.
    intros s' (s'_bst, (s'_avl, Hs')); simpl in |- *; exists s'; intuition.
    unfold height_of_node in |- *; simpl in |- *. AVL H2; AVL s'_avl; intuition omega.
    firstorder. firstorder. inversion_clear H5. firstorder.
    intros; clear H.
    induction  r as [| r1 Hrecr1 t3 r0 Hrecr0 z0]; simpl in |- *.
    (* r = Leaf *)
    clear H0.
    intros; case (add_tree x (Node t0 t1 t2 z)); simpl in |- *; trivial.
    intros s' (s'_bst, (s'_avl, Hs')); simpl in |- *; exists s'; intuition.
    unfold height_of_node in |- *; simpl in |- *. AVL s'_avl; intuition omega.
    firstorder. firstorder. firstorder. inversion_clear H.
    (* l = Node t0 t1 t2 z and r = Node r1 t3 r0 z0 *)
    intros.
    case (Z_gt_le_dec z (z0 + 2)); intro.
    (* z > z0+2 *)
    clear Hrecr1 Hrecr0.
    case (H0 x (Node r1 t3 r0 z0)); clear H0; auto.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    intro s'; unfold height_of_node in |- *; simpl in |- *; intuition.
    case (bal t0 t1 s'); auto.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    inversion_clear H1; trivial.
    clear H0; intro; intro; generalize (H9 y); clear H9; intuition.
    apply ME.lt_eq with x; auto.
    inversion_clear H1; auto.
    apply X.lt_trans with x; auto.
    clear H9; AVL H2; intuition omega.
    intro s''; unfold height_of_node in |- *; simpl in |- *; intuition.
    exists s''; do 3 (split; trivial).
    clear H5 H6 H7 H8 H9 H13; AVL H2; clear H2; intuition omega.
    clear H0 H12 H10; firstorder.
    inversion_clear H0; firstorder.
    (* z <= z0 + 2 *)
    case (Z_gt_le_dec z0 (z + 2)); intro.
    (* z0 > z+2 *)
    clear H0 Hrecr0.
    case Hrecr1; clear Hrecr1; auto.
    inversion_clear H3; trivial.
    inversion_clear H4; trivial.
    intro s'; unfold height_of_node in |- *; simpl in |- *; intuition.
    case (bal s' t3 r0); auto.
    inversion_clear H3; trivial.
    inversion_clear H4; trivial.
    inversion_clear H3; trivial.
    clear H0; intro; intro; generalize (H9 y); clear H9; intuition.
    apply ME.eq_lt with x; auto.
    apply X.lt_trans with x; auto.
    inversion_clear H3; auto.
    clear H9; AVL H4; intuition omega.
    intro s''; unfold height_of_node in |- *; simpl in |- *; intuition.
    exists s''; do 3 (split; trivial).
    clear H5 H6 H7 H8 H9 H13; AVL H4; clear H4; intuition omega.
    clear H0 H12 H10; firstorder.
    inversion_clear H0; firstorder.
    (* -2 <= z-z0 <= 2 *)
    clear H0 Hrecr0 Hrecr1.
    case (create (Node t0 t1 t2 z) x (Node r1 t3 r0 z0)); simpl in |- *;
     intuition.
    exists x0; intuition.
  Qed.

  (** * Extraction of minimum and maximum element *)

  Definition remove_min :
    forall s : tree,
    bst s ->
    avl s ->
    s <> Leaf ->
    {r : tree * elt |
    let (s', m) := r in
    bst s' /\
    avl s' /\
    (height s' = height s \/ height s' = height s - 1) /\
    (forall y : elt, In_tree y s' -> E.lt m y) /\
    (forall y : elt, In_tree y s <-> E.eq y m \/ In_tree y s')}.
  Proof.
    simple induction s; simpl in |- *; intros.
    elim H1; trivial.
    (* s = Node t0 t1 t2 *)
    destruct t0 as [| t0 t3 t4 z0].
    (* t0 = Leaf *)
    clear H H0.
    exists (t2, t1); intuition.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    AVL H2; simpl in H; inversion_clear H2; AVL ipattern:H5; intuition; omega.
    inversion_clear H1; apply H6; auto.
    inversion_clear H; auto; inversion_clear H0.
    (* t0 = Node t0 t3 t4 *)
    clear H0; case H; clear H.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    discriminate.
    intros (l', m); intuition.
    case (bal l' t1 t2); auto.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    intro; intros; generalize (H7 y) (H5 y); clear H7 H5 H0; intuition.
    elim (ME.eq_not_gt (x:=y) (y:=m)); auto.
    inversion_clear H1; auto.
    inversion_clear H1; trivial.
    clear H5 H7.
    AVL H2; omega. 
    intro s'; unfold height_of_node in |- *; intuition.
    exists (s', m).
    do 3 (split; trivial).
    clear H5 H7 H11; AVL H2; AVL H4; AVL H9; omega.
    clear H0 H10 H8; intuition.
    generalize (H5 y) (H7 y) (H11 y); clear H5 H11; intuition.
    apply ME.lt_eq with t1; auto.
    generalize (H7 m); inversion_clear H1; intuition.
    apply X.lt_trans with t1; auto.
    inversion_clear H1; apply H18; firstorder.
    inversion_clear H1; auto.
    inversion_clear H0; firstorder.
    apply InLeft; firstorder.
    firstorder.
  Qed.

  Definition remove_max :
    forall s : tree,
    bst s ->
    avl s ->
    s <> Leaf ->
    {r : tree * elt |
    let (s', m) := r in
    bst s' /\
    avl s' /\
    (height s' = height s \/ height s' = height s - 1) /\
    (forall y : elt, In_tree y s' -> E.lt y m) /\
    (forall y : elt, In_tree y s <-> E.eq y m \/ In_tree y s')}.
  Proof.
    simple induction s; simpl in |- *; intros.
    elim H1; trivial.
    (* s = Node t0 t1 t2 *)
    destruct t2 as [| t2 t3 t4 z0].
    (* t2 = Leaf *)
    clear H H0.
    exists (t0, t1); intuition.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    AVL H2; simpl in H; inversion_clear H2; AVL ipattern:H4; intuition; omega.
    inversion_clear H1; apply H5; auto.
    inversion_clear H; auto; inversion_clear H0.
    (* t2 = Node t2 t3 t4 *)
    clear H; case H0; clear H0.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    discriminate.
    intros (r', m); intuition.
    case (bal t0 t1 r'); auto.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    inversion_clear H1; auto.
    intro; intros; generalize (H7 y) (H5 y); clear H7 H5 H0; intuition.
    elim (ME.eq_not_lt (x:=y) (y:=m)); auto.
    inversion_clear H1; auto.
    clear H5 H7.
    AVL H2; omega. 
    intro s'; unfold height_of_node in |- *; intuition.
    exists (s', m).
    do 3 (split; trivial).
    clear H5 H7 H11; AVL H2; AVL H4; AVL H9; omega.
    clear H0 H10 H8; intuition.
    generalize (H5 y) (H7 y) (H11 y); clear H5 H11; intuition.
    apply ME.eq_lt with t1; auto.
    generalize (H7 m); inversion_clear H1; intuition.
    apply X.lt_trans with t1; auto.
    inversion_clear H1; apply H18; firstorder.
    inversion_clear H1; firstorder.
    inversion_clear H0; firstorder.
    apply InRight; firstorder.
    firstorder.
  Qed.

  (** * Merging two trees

    [merge t1 t2] builds the union of [t1] and [t2] assuming all elements
    of [t1] to be smaller than all elements of [t2], and
    [|height t1 - height t2| <= 2]. Code is
<<
    let merge t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) -> let (m,t'2) = remove_min t2 in bal t1 m t'2
>> 
  *)

  Definition merge :
    forall s1 s2 : tree,
    bst s1 ->
    avl s1 ->
    bst s2 ->
    avl s2 ->
    (forall y1 y2 : elt, In_tree y1 s1 -> In_tree y2 s2 -> X.lt y1 y2) ->
    -2 <= height s1 - height s2 <= 2 ->
    {s : tree |
    bst s /\
    avl s /\
    (height_of_node s1 s2 (height s) \/ height_of_node s1 s2 (height s + 1)) /\
    (forall y : elt, In_tree y s <-> In_tree y s1 \/ In_tree y s2)}.
  Proof.
    simple destruct s1; simpl in |- *.
    (* s1 = Leaf *)
    intros; exists s2; unfold height_of_node in |- *; simpl in |- *;
     intuition.
    AVL H2; omega.
    inversion_clear H7.
    (* s1 = Node t0 t1 t2 *)
    simple destruct s2; simpl in |- *.
    (* s2 = Leaf *)
    intros; exists (Node t0 t1 t2 z); unfold height_of_node in |- *;
     simpl in |- *; intuition.
    AVL H0; omega.
    inversion_clear H7.
    (* s2 = Node t3 t4 t5 *)
    intros.
    case (remove_min (Node t3 t4 t5 z0)); auto.
    discriminate.
    intros (s'2, m); intuition.
    case (bal (Node t0 t1 t2 z) m s'2); auto.
    firstorder.
    clear H3 H11; AVL H0; AVL H2; AVL H8; simpl in H7; omega.
    intro s'; unfold height_of_node in |- *; intuition. 
    exists s'.
    do 3 (split; trivial).
    clear H3 H9 H11 H15; AVL H0; AVL H2; AVL H8; AVL H13.
    simpl in H7, H14, H12; simpl in |- *; intuition omega.
    clear H7 H12 H14; firstorder.
  Qed.

  (** Variant where we remove from the biggest subtree *)

  Definition merge_bis :
    forall s1 s2 : tree,
    bst s1 ->
    avl s1 ->
    bst s2 ->
    avl s2 ->
    (forall y1 y2 : elt, In_tree y1 s1 -> In_tree y2 s2 -> X.lt y1 y2) ->
    -2 <= height s1 - height s2 <= 2 ->
    {s : tree |
    bst s /\
    avl s /\
    (height_of_node s1 s2 (height s) \/ height_of_node s1 s2 (height s + 1)) /\
    (forall y : elt, In_tree y s <-> In_tree y s1 \/ In_tree y s2)}.
  Proof.
    simple destruct s1; simpl in |- *.
    (* s1 = Leaf *)
    intros; exists s2; unfold height_of_node in |- *; simpl in |- *;
     intuition.
    AVL H2; omega.
    inversion_clear H7.
    (* s1 = Node t0 t1 t2 *)
    simple destruct s2; simpl in |- *.
    (* s2 = Leaf *)
    intros; exists (Node t0 t1 t2 z); unfold height_of_node in |- *;
     simpl in |- *; intuition.
    AVL H0; omega.
    inversion_clear H7.
    (* s2 = Node t3 t4 t5 *)
    intros; case (Z_ge_lt_dec z z0); intro.
    (* z >= z0 *)
    case (remove_max (Node t0 t1 t2 z)); auto.
    discriminate.
    intros (s'1, m); intuition.
    case (create s'1 m (Node t3 t4 t5 z0)); auto.
    firstorder.
    clear H3 H11; AVL H0; AVL H2; AVL H8; simpl in H7; omega.
    intro s'; unfold height_of_node in |- *; intuition. 
    exists s'.
    do 3 (split; trivial).
    clear H3 H9 H11 H15; AVL H0; AVL H2; AVL H8; AVL H13.
    simpl in H7, H14, H12; simpl in |- *.
    intuition omega.
    clear H7 H12; firstorder.
    (* z < z0 *)
    case (remove_min (Node t3 t4 t5 z0)); auto.
    discriminate.
    intros (s'2, m); intuition.
    case (create (Node t0 t1 t2 z) m s'2); auto.
    firstorder.
    clear H3 H11; AVL H0; AVL H2; AVL H8; simpl in H7; omega.
    intro s'; unfold height_of_node in |- *; intuition. 
    exists s'.
    do 3 (split; trivial).
    clear H3 H9 H11 H15; AVL H0; AVL H2; AVL H8; AVL H13.
    simpl in H7, H14, H12; simpl in |- *.
    intuition omega.
    clear H7 H12; firstorder.
  Qed.

  (** * Deletion *)

  Definition remove_tree :
    forall (x : elt) (s : tree),
    bst s ->
    avl s ->
    {s' : tree |
    bst s' /\
    avl s' /\
    (height s' = height s \/ height s' = height s - 1) /\
    (forall y : elt, In_tree y s' <-> ~ E.eq y x /\ In_tree y s)}.
  Proof.
    simple induction s; simpl in |- *; intuition.
    (* s = Leaf *)
    exists Leaf; simpl in |- *; intuition;
     inversion_clear H1 || inversion_clear H3.
    (* s = Node t0 t1 t2 *)
    case (X.compare x t1); intro.
    (* x < t1 *)
    clear H0; case H; clear H.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    intros t'0; intuition.
    case (bal t'0 t1 t2); auto.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    clear H0; intro; intro; generalize (H5 y); clear H5; intuition.
    inversion_clear H1; auto.
    inversion_clear H1; auto.
    clear H5; AVL H2; AVL H3; omega.
    intros s'; unfold height_of_node in |- *; intuition.
    exists s'; do 3 (split; trivial).
    clear H5 H9; AVL H2; AVL H3; AVL H7; omega.
    clear H0 H8 H6; intuition.
    generalize (H9 y) (H5 y); clear H5 H9; intuition.
    apply (ME.eq_not_lt (x:=y) (y:=t1)); auto.
    apply ME.eq_lt with x; auto.
    apply (ME.lt_not_gt (x:=t1) (y:=y)); auto.
    inversion_clear H1; apply H16; auto.
    apply ME.eq_lt with x; auto.
    generalize (H9 y) (H5 y); clear H5 H9; intuition.
    inversion_clear H8; generalize (H9 y) (H5 y); clear H5 H9; intuition.
    (* x = t1 *)
    clear H H0; case (merge t0 t2).
    inversion_clear H1; auto.
    inversion_clear H2; auto.
    inversion_clear H1; auto.
    inversion_clear H2; auto.
    intros; apply X.lt_trans with t1; inversion_clear H1; auto.
    AVL H2; omega.
    intro s'; unfold height_of_node in |- *; intuition.
    exists s'; do 3 (split; trivial).
    clear H5; AVL H2; AVL H3; omega.
    clear H0; intro; generalize (H5 y); clear H5; intuition.
    apply (E.lt_not_eq (x:=y) (y:=t1)); auto.
    inversion_clear H1; apply H10; auto.
    apply X.eq_trans with x; auto.
    apply (E.lt_not_eq (x:=t1) (y:=y)); auto.
    inversion_clear H1; apply H11; auto.
    apply X.eq_trans with x; auto.
    inversion_clear H8; intuition.
    absurd (X.eq y x); auto.
    apply X.eq_trans with t1; auto.
    (* t1 < x *)
    clear H; case H0; clear H0.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    intros t'2; intuition.
    case (bal t0 t1 t'2); auto.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    inversion_clear H1; auto.
    inversion_clear H1; auto.
    clear H0; intro; intro; generalize (H5 y); clear H5; intuition.
    clear H5; AVL H2; AVL H3; omega.
    intros s'; unfold height_of_node in |- *; intuition.
    exists s'; do 3 (split; trivial).
    clear H5 H9; AVL H2; AVL H3; AVL H7; omega.
    clear H0 H8 H6; intuition.
    generalize (H9 y) (H5 y); clear H5 H9; intuition.
    apply (ME.eq_not_lt (x:=t1) (y:=y)); auto.
    apply ME.lt_eq with x; auto.
    apply (ME.lt_not_gt (x:=y) (y:=t1)); auto.
    inversion_clear H1; apply H15; auto.
    apply ME.lt_eq with x; auto.
    generalize (H9 y) (H5 y); clear H5 H9; intuition.
    inversion_clear H8; generalize (H9 y) (H5 y); clear H5 H9; intuition.
  Qed.

  Definition remove :
    forall (x : elt) (s : t),
    {s' : t | forall y : elt, In y s' <-> ~ E.eq y x /\ In y s}.
  Proof.
    intros x (s, Hs, Hrb); case (remove_tree x s); trivial.
    intros s'; intuition; clear H0.
    exists (t_intro s' H H1); intuition.
  Qed.

 (** * Minimum element *)

  Definition min_elt :
    forall s : t,
    {x : elt | In x s /\ For_all (fun y => ~ E.lt y x) s} + {Empty s}.
  Proof.
    intros (s, Hs, Ha).
    unfold For_all, Empty, In in |- *; simpl in |- *.
    generalize Hs; clear Hs Ha; induction  s as [| s1 Hrecs1 t0 s0 Hrecs0 z];
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
  Qed.

  (** * Maximum element *)

  Definition max_elt :
    forall s : t,
    {x : elt | In x s /\ For_all (fun y => ~ E.lt x y) s} + {Empty s}.
   Proof.
    intros (s, Hs, Ha).
    unfold For_all, Empty, In in |- *; simpl in |- *.
    generalize Hs; clear Hs Ha; induction  s as [| s1 Hrecs1 t0 s0 Hrecs0 z];
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
  Qed.

  (** * Any element *)

  Definition choose : forall s : t, {x : elt | In x s} + {Empty s}.
  Proof.
    intro s; destruct (min_elt s) as [(x,(H,_))|H]; 
      [ left; exists  x | right ]; trivial.
  Qed.

  (** * Concatenation

      Same as [merge] but does not assume anything about heights. Code is 
<<
    let concat t1 t2 =
      match (t1, t2) with
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) -> join t1 (min_elt t2) (remove_min_elt t2)
>> 
  *)

  Definition concat :
    forall s1 s2 : tree,
    bst s1 ->
    avl s1 ->
    bst s2 ->
    avl s2 ->
    (forall y1 y2 : elt, In_tree y1 s1 -> In_tree y2 s2 -> X.lt y1 y2) ->
    {s : tree |
    bst s /\
    avl s /\ (forall y : elt, In_tree y s <-> In_tree y s1 \/ In_tree y s2)}.
  Proof.
    simple destruct s1; simpl in |- *.
    (* s1 = Leaf *)
    intros; exists s2; simpl in |- *; intuition.
    inversion_clear H5.
    (* s1 = Node t0 t1 t2 *)
    simple destruct s2; simpl in |- *.
    (* s2 = Leaf *)
    intros; exists (Node t0 t1 t2 z); simpl in |- *; intuition.
    inversion_clear H5.
    (* s2 = Node t3 t4 t5 *)
    intros.
    case (remove_min (Node t3 t4 t5 z0)); auto.
    discriminate.
    intros (s'2, m); intuition.
    case (join (Node t0 t1 t2 z) m s'2); auto.
    firstorder.
    intro s'; intuition. 
    exists s'.
    do 2 (split; trivial).
    clear H5 H10; firstorder.
  Qed.

  (** * Splitting 

      [split x s] returns a triple [(l, present, r)] where
      - [l] is the set of elements of [s] that are [< x]
      - [r] is the set of elements of [s] that are [> x]
      - [present] is [true] if and only if [s] contains  [x].

<<
    let rec split x = function
        Empty ->
          (Empty, false, Empty)
      | Node(l, v, r, _) ->
          let c = Ord.compare x v in
          if c = 0 then (l, true, r)
          else if c < 0 then
            let (ll, pres, rl) = split x l in (ll, pres, join rl v r)
          else
            let (lr, pres, rr) = split x r in (join l v lr, pres, rr)
>> 
  *)

  Definition split :
    forall (x : elt) (s : tree),
    bst s ->
    avl s ->
    {res : tree * (bool * tree) |
    let (l, res') := res in
    let (b, r) := res' in
    bst l /\
    avl l /\
    bst r /\
    avl r /\
    (forall y : elt, In_tree y l <-> In_tree y s /\ X.lt y x) /\
    (forall y : elt, In_tree y r <-> In_tree y s /\ X.lt x y) /\
    (b = true <-> In_tree x s)}.
  Proof.
    simple induction s; simpl in |- *; intuition.
    (* s = Leaf *)
    exists (Leaf, (false, Leaf)); simpl in |- *; intuition;
     inversion_clear H1.
    (* s = Node t0 t1 t2 z *)
    case (X.compare x t1); intro.
    (* x < t1 *)
    clear H0; case H; clear H.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    intros (ll, (pres, rl)); intuition.
    case (join rl t1 t2); auto.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    inversion_clear H1; firstorder.
    inversion_clear H1; firstorder.
    intros s' (s'_bst, (s'_avl, (s'_h, s'_y))); clear s'_h.
    exists (ll, (pres, s')); intuition.
    firstorder.
    firstorder.
    inversion_clear H10; firstorder.
    absurd (X.eq y t1); auto.
    apply E.lt_not_eq; apply X.lt_trans with x; auto.
    inversion_clear H1; absurd (X.lt y t1); auto.
    apply X.lt_trans with x; auto.
    firstorder.
    generalize (s'_y y); clear s'_y; firstorder.
    apply ME.lt_eq with t1; auto.
    apply X.lt_trans with t1; inversion_clear H1; firstorder.
    inversion_clear H10; firstorder.
    inversion_clear H8; intuition.
    absurd (X.eq x t1); auto.
    absurd (X.lt x t1); inversion_clear H1; auto.
    (* x = t1 *)
    clear H H0.
    exists (t0, (true, t2)); simpl in |- *.
    split. inversion_clear H1; trivial.
    split. inversion_clear H2; trivial.
    split. inversion_clear H1; trivial.
    split. inversion_clear H2; trivial.
    inversion_clear H1; firstorder.
    apply ME.lt_eq with t1; auto.
    inversion_clear H1; auto.
    absurd (X.eq y t1); auto.
    apply E.lt_not_eq; apply ME.lt_eq with x; auto.
    absurd (X.lt y x); auto.
    apply ME.lt_not_gt; apply ME.eq_lt with t1; auto.
    apply ME.eq_lt with t1; auto.
    inversion_clear H1; auto.
    absurd (X.eq x t1); auto.
    apply E.lt_not_eq; apply ME.lt_eq with y; auto.
    absurd (X.lt x y); auto.
    apply ME.lt_not_gt; apply ME.lt_eq with t1; auto.
    (* x > t1 *)
    clear H; case H0; clear H0.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    intros (lr, (pres, rr)); intuition.
    case (join t0 t1 lr); auto.
    inversion_clear H1; trivial.
    inversion_clear H2; trivial.
    inversion_clear H1; firstorder.
    inversion_clear H1; firstorder.
    intros s' (s'_bst, (s'_avl, (s'_h, s'_y))); clear s'_h.
    exists (s', (pres, rr)); inversion_clear H1; intuition.
    firstorder.
    generalize (s'_y y); clear s'_y; firstorder.
    apply ME.eq_lt with t1; auto.
    apply X.lt_trans with t1; auto.
    inversion_clear H13; firstorder.
    firstorder.
    firstorder.
    inversion_clear H13; intuition.
    absurd (X.lt t1 x); auto.
    apply ME.lt_not_gt; apply ME.lt_eq with y; auto.
    absurd (X.lt x y); auto.
    apply ME.lt_not_gt; apply X.lt_trans with t1; auto.
    firstorder.
    inversion_clear H1; auto.
    absurd (X.eq x t1); auto.
    absurd (X.lt x t1); auto.
  Qed.

  (** * Intersection
<<
    let rec inter s1 s2 =
      match (s1, s2) with
        (Empty, t2) -> Empty
      | (t1, Empty) -> Empty
      | (Node(l1, v1, r1, _), t2) ->
          match split v1 t2 with
            (l2, false, r2) ->
              concat (inter l1 l2) (inter r1 r2)
          | (l2, true, r2) ->
              join (inter l1 l2) v1 (inter r1 r2)
>> 
  *)

  Definition inter :
    forall s1 s2 : t,
    {s' : t | forall x : elt, In x s' <-> In x s1 /\ In x s2}.
  Proof.
    intros (s1, s1_bst, s1_avl) (s2, s2_bst, s2_avl).
    generalize s1_bst s1_avl s2 s2_bst s2_avl;
     clear s1_bst s1_avl s2_bst s2_avl.
    unfold In in |- *; induction  s1 as [| s1_1 Hrecs1_1 t0 s1_0 Hrecs1_0 z];
     simpl in |- *; intuition.
    (* s1 = Leaf *)
    exists (t_intro Leaf s1_bst s1_avl); simpl in |- *; intuition.
    inversion_clear H.
    (* s1 = Node s1_1 t0 s1_0 *)
    destruct s0 as [| t1 t2 t3 z0]; simpl in |- *.
    (* s2 = Leaf *)
    clear Hrecs1_1 Hrecs1_0.
    exists (t_intro Leaf s2_bst s2_avl); simpl in |- *; intuition.
    inversion_clear H.
    (* s2 = Node t1 t2 t3 *)
    case (split t0 (Node t1 t2 t3 z0)); auto.
    intros (l2, (b, r2)); simpl in |- *; intuition.
    assert (s1_1_bst : bst s1_1). inversion_clear s1_bst; trivial.
    assert (s1_1_avl : avl s1_1). inversion_clear s1_avl; trivial.
    case (Hrecs1_1 s1_1_bst s1_1_avl l2 H H1); clear Hrecs1_1.
    intros (inter_s1_1_l2, s1_1_l2_bst, s1_1_l2_avl); simpl in |- *;
     intuition.
    assert (s1_0_bst : bst s1_0). inversion_clear s1_bst; trivial.
    assert (s1_0_avl : avl s1_0). inversion_clear s1_avl; trivial.
    case (Hrecs1_0 s1_0_bst s1_0_avl r2 H0 H2); clear Hrecs1_0.
    intros (inter_s1_0_r2, s1_0_r2_bst, s1_0_r2_avl); simpl in |- *;
     intuition.
    induction  b as [| ]; simpl in |- *; intuition.
    (* b = true *)
    case (join inter_s1_1_l2 t0 inter_s1_0_r2); auto.
    firstorder.
    firstorder.
    intros s' (s'_bst, (s'_avl, (s'_h, s'_y))); clear s'_h.
    exists (t_intro s' s'_bst s'_avl); simpl in |- *; intros.
    generalize (s'_y x) (a0 x) (a x) (H3 x) (H4 x); clear s'_y a0 a H3 H4;
     intuition.
    assert (In_tree x (Node t1 t2 t3 z0)); auto.
    apply eq_In_tree with t0; auto.
    inversion_clear H18; intuition.
    case (X.compare x t0); intuition.
    absurd (X.lt t0 x); inversion_clear s1_bst; auto.
    case (X.compare x t0); intuition.
    absurd (X.lt x t0); inversion_clear s1_bst; auto.
    (* b = false *)
    case (concat inter_s1_1_l2 inter_s1_0_r2); auto.
    intuition.
    apply X.lt_trans with t0; inversion_clear s1_bst; firstorder.
    intros s' (s'_bst, (s'_avl, s'_y)).
    exists (t_intro s' s'_bst s'_avl); simpl in |- *; intros.
    generalize (s'_y x) (a0 x) (a x) (H3 x) (H4 x); clear s'_y a0 a H3 H4;
     intuition.
    assert (~ X.eq x t0). intro.
    assert (false = true). apply H7; apply eq_In_tree with x; auto.
    discriminate H19.
    inversion_clear H17; intuition.
    case (X.compare x t0); intuition.
    absurd (X.lt t0 x); inversion_clear s1_bst; auto.
    case (X.compare x t0); intuition.
    absurd (X.lt x t0); inversion_clear s1_bst; auto.
  Qed.

  (** * Difference
<<
     let rec diff s1 s2 =
      match (s1, s2) with
        (Empty, t2) -> Empty
      | (t1, Empty) -> t1
      | (Node(l1, v1, r1, _), t2) ->
          match split v1 t2 with
            (l2, false, r2) ->
              join (diff l1 l2) v1 (diff r1 r2)
          | (l2, true, r2) ->
              concat (diff l1 l2) (diff r1 r2)
>> 
  *)

  Definition diff :
    forall s1 s2 : t,
    {s' : t | forall x : elt, In x s' <-> In x s1 /\ ~ In x s2}.
  Proof.
    intros (s1, s1_bst, s1_avl) (s2, s2_bst, s2_avl).
    generalize s1_bst s1_avl s2 s2_bst s2_avl;
     clear s1_bst s1_avl s2_bst s2_avl.
    unfold In in |- *; induction  s1 as [| s1_1 Hrecs1_1 t0 s1_0 Hrecs1_0 z];
     simpl in |- *; intuition.
    (* s1 = Leaf *)
    exists (t_intro Leaf s1_bst s1_avl); simpl in |- *; intuition.
    inversion_clear H.
    (* s1 = Node s1_1 t0 s1_0 *)
    destruct s0 as [| t1 t2 t3 z0]; simpl in |- *.
    (* s2 = Leaf *)
    clear Hrecs1_1 Hrecs1_0.
    exists (t_intro (Node s1_1 t0 s1_0 z) s1_bst s1_avl); simpl in |- *;
     intuition.
    inversion_clear H0.
    (* s2 = Node t1 t2 t3 *)
    case (split t0 (Node t1 t2 t3 z0)); auto.
    intros (l2, (b, r2)); simpl in |- *; intuition.
    assert (s1_1_bst : bst s1_1). inversion_clear s1_bst; trivial.
    assert (s1_1_avl : avl s1_1). inversion_clear s1_avl; trivial.
    case (Hrecs1_1 s1_1_bst s1_1_avl l2 H H1); clear Hrecs1_1.
    intros (diff_s1_1_l2, s1_1_l2_bst, s1_1_l2_avl); simpl in |- *; intuition.
    assert (s1_0_bst : bst s1_0). inversion_clear s1_bst; trivial.
    assert (s1_0_avl : avl s1_0). inversion_clear s1_avl; trivial.
    case (Hrecs1_0 s1_0_bst s1_0_avl r2 H0 H2); clear Hrecs1_0.
    intros (diff_s1_0_r2, s1_0_r2_bst, s1_0_r2_avl); simpl in |- *; intuition.
    induction  b as [| ]; simpl in |- *; intuition.
    (* b = true *)
    case (concat diff_s1_1_l2 diff_s1_0_r2); auto.
    intuition.
    apply X.lt_trans with t0; inversion_clear s1_bst; firstorder.
    intros s' (s'_bst, (s'_avl, s'_y)).
    exists (t_intro s' s'_bst s'_avl); simpl in |- *; intros.
    generalize (s'_y x); clear s'_y; intuition.
    apply InLeft; firstorder.
    clear a0 H4; generalize (a x) (H3 x); clear a H3; intuition.
    assert (X.lt x t0); inversion_clear s1_bst; auto.
    apply InRight; firstorder.
    clear a H3; generalize (a0 x) (H4 x); clear a0 H4; intuition.
    assert (X.lt t0 x); inversion_clear s1_bst; auto.
    inversion_clear H11; intuition.
    elim H12; apply eq_In_tree with t0; auto.
    apply H7; clear a0 H4; firstorder.
    apply H10; clear a H3; firstorder.
    (* b = false *)
    case (join diff_s1_1_l2 t0 diff_s1_0_r2); auto.
    intro; inversion_clear s1_bst; firstorder.
    intro; inversion_clear s1_bst; firstorder.
    intros s' (s'_bst, (s'_avl, (s'_h, s'_y))); clear s'_h.
    exists (t_intro s' s'_bst s'_avl); simpl in |- *; intros.
    intuition.
    generalize (s'_y x); clear s'_y; intuition.
    apply InLeft; firstorder.
    apply InRight; firstorder.
    generalize (s'_y x); clear s'_y; intuition.
    assert (false = true). apply H7; apply eq_In_tree with x; auto.
    discriminate H12.
    clear a0 H4; generalize (a x) (H3 x); clear a H3; intuition.
    assert (X.lt x t0); inversion_clear s1_bst; auto.
    clear a H3; generalize (a0 x) (H4 x); clear a0 H4; intuition.
    assert (X.lt t0 x); inversion_clear s1_bst; auto.
    generalize (s'_y x); clear s'_y; intuition.
    inversion_clear H8; intuition.
    clear a0 H4; generalize (a x) (H3 x); clear a H3; intuition.
    clear a H3; generalize (a0 x) (H4 x); clear a0 H4; intuition.
  Qed.

  (** * Elements *)

  (** [elements_tree_aux acc t] catenates the elements of [t] in infix
      order to the list [acc] *)

  Fixpoint elements_tree_aux (acc : list X.t) (t : tree) {struct t} :
   list X.t :=
    match t with
    | Leaf => acc
    | Node l x r _ => elements_tree_aux (x :: elements_tree_aux acc r) l
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
  Qed.

  (** * Cardinal *)

  Fixpoint cardinal_tree (s : tree) : nat :=
    match s with
    | Leaf => 0%nat
    | Node l _ r _ => S (cardinal_tree l + cardinal_tree r)
    end.

  Lemma cardinal_elements_1 :
   forall (s : tree) (acc : list X.t),
   (length acc + cardinal_tree s)%nat = length (elements_tree_aux acc s).
  Proof.
    simple induction s; simpl in |- *; intuition.
    rewrite <- H.
    simpl in |- *.
    rewrite <- H0; omega.
  Qed.

  Lemma cardinal_elements_2 :
   forall s : tree, cardinal_tree s = length (elements_tree s).
  Proof.
    exact (fun s => cardinal_elements_1 s []).
  Qed.

  Definition cardinal :
    forall s : t,
    {r : nat |
    exists l : list elt,
      Unique E.eq l /\
      (forall x : elt, In x s <-> InList E.eq x l) /\ r = length l}.
  Proof.
    intros (s, s_bst, s_avl); unfold In in |- *; simpl in |- *; clear s_avl.
    exists (cardinal_tree s).
    exists (elements_tree s); intuition.
    apply ME.Sort_Unique; auto.
    exact (cardinal_elements_2 s).
  Qed.

  (** Induction over cardinals *)

  Lemma sorted_subset_cardinal :
   forall l' l : list X.t,
   ME.Sort l ->
   ME.Sort l' ->
   (forall x : elt, ME.In x l -> ME.In x l') -> (length l <= length l')%nat.
  Proof.
    simple induction l'; simpl in |- *; intuition.
    destruct l; trivial; intros.
    absurd (ME.In t0 []); intuition.
    inversion_clear H2.
    inversion_clear H1.
    destruct l0; simpl in |- *; intuition.
    inversion_clear H0.
    apply le_n_S.
    case (X.compare t0 a); intro.
    absurd (ME.In t0 (a :: l)).
    intro.
    inversion_clear H0.
    apply (X.lt_not_eq (x:=t0) (y:=a)); auto.
    assert (X.lt a t0).
    apply ME.In_sort with l; auto.
    apply (ME.lt_not_gt (x:=t0) (y:=a)); auto.
    firstorder.
    apply H; auto.
    intros.
    assert (ME.In x (a :: l)).
    apply H2; auto.
    inversion_clear H6; auto.
    assert (X.lt t0 x).
    apply ME.In_sort with l0; auto.
    elim (X.lt_not_eq (x:=t0) (y:=x)); auto.
    apply X.eq_trans with a; auto.
    apply le_trans with (length (t0 :: l0)).
    simpl in |- *; omega.
    apply (H (t0 :: l0)); auto.
    intros.
    assert (ME.In x (a :: l)); firstorder.
    inversion_clear H6; auto.
    assert (X.lt a x).
    apply ME.In_sort with (t0 :: l0); auto.
    elim (X.lt_not_eq (x:=a) (y:=x)); auto.
  Qed.

  Lemma cardinal_subset :
   forall a b : tree,
   bst a ->
   bst b ->
   (forall y : elt, In_tree y a -> In_tree y b) ->
   (cardinal_tree a <= cardinal_tree b)%nat.
  Proof.
    intros.
    do 2 rewrite cardinal_elements_2.
    apply sorted_subset_cardinal; auto.
  Qed.

  Lemma cardinal_left :
   forall (l r : tree) (x : elt) (h : Z),
   (cardinal_tree l < cardinal_tree (Node l x r h))%nat.
  Proof.
    simpl in |- *; intuition.
  Qed. 

  Lemma cardinal_right :
   forall (l r : tree) (x : elt) (h : Z),
   (cardinal_tree r < cardinal_tree (Node l x r h))%nat.
  Proof.
    simpl in |- *; intuition.
  Qed. 

  Lemma cardinal_rec2 :
   forall P : tree -> tree -> Set,
   (forall x x' : tree,
    (forall y y' : tree,
     (cardinal_tree y + cardinal_tree y' < cardinal_tree x + cardinal_tree x')%nat ->
     P y y') -> P x x') -> forall x x' : tree, P x x'.
  Proof.
    intros P H x x'.
    apply
     well_founded_induction_type_2
      with
        (R := fun yy' xx' : tree * tree =>
              (cardinal_tree (fst yy') + cardinal_tree (snd yy') <
               cardinal_tree (fst xx') + cardinal_tree (snd xx'))%nat); 
     auto.                      
    apply
     (Wf_nat.well_founded_ltof _
        (fun xx' : tree * tree =>
         (cardinal_tree (fst xx') + cardinal_tree (snd xx'))%nat)).
(***
    Intros P H.
    Assert (n:nat)(x,x':tree)n=(plus (cardinal_tree x) (cardinal_tree x'))->(P x x').
    Intros n; Pattern n; Apply Wf_nat.lt_wf_rec.
    Intuition.
    Apply H; Intros.
    Apply (H0 (plus (cardinal_tree y) (cardinal_tree y'))).
    Omega.
    Omega.
    Intros; Apply (H0 (plus (cardinal_tree x) (cardinal_tree x'))); Trivial.
***)
  Qed.

  Lemma height_0 :
   forall s : tree, avl s -> height s = 0 -> forall x : elt, ~ In_tree x s.
  Proof.
    simple destruct 1; intuition.
    inversion_clear H1.
    unfold height_of_node in H3.
    AVL H; AVL H0; AVL H1; simpl in H4; omega.
  Qed.
  Implicit Arguments height_0.

  (** * Union

      [union s1 s2] does an induction over the sum of the cardinals of
      [s1] and [s2]. Code is
<<
    let rec union s1 s2 =
      match (s1, s2) with
        (Empty, t2) -> t2
      | (t1, Empty) -> t1
      | (Node(l1, v1, r1, h1), Node(l2, v2, r2, h2)) ->
          if h1 >= h2 then
            if h2 = 1 then add v2 s1 else begin
              let (l2, _, r2) = split v1 s2 in
              join (union l1 l2) v1 (union r1 r2)
            end
          else
            if h1 = 1 then add v1 s2 else begin
              let (l1, _, r1) = split v2 s1 in
              join (union l1 l2) v2 (union r1 r2)
            end
>>
  *)

  Definition union :
    forall s1 s2 : t,
    {s' : t | forall x : elt, In x s' <-> In x s1 \/ In x s2}.
  Proof.
    intros (s1, s1_bst, s1_avl) (s2, s2_bst, s2_avl).
    generalize s1_bst s1_avl s2_bst s2_avl; clear s1_bst s2_bst.
    pattern s1, s2 in |- *; apply cardinal_rec2.
    unfold In in |- *; simple destruct x; simpl in |- *; intuition.
    (* x = Leaf *)
    clear H.
    exists (t_intro x' s2_bst s2_avl0); simpl in |- *; intuition.
    inversion_clear H0.
    (* x = Node t0 t1 t2 *)
    destruct x' as [| t3 t4 t5 z0]; simpl in |- *.
    (* x' = Leaf *)
    clear H.
    exists (t_intro (Node t0 t1 t2 z) s1_bst s1_avl0); simpl in |- *;
     intuition.
    inversion_clear H0.
    (* x' = Node t3 t4 t5 *)
    case (Z_ge_lt_dec z z0); intro.
    (* z >= z0 *)
    case (Z_eq_dec z0 1); intro.
    (* z0 = 1 *)
    clear H.
    case (add_tree t4 (Node t0 t1 t2 z)); simpl in |- *; auto.
    intros s' (s'_bst, (s'_avl, (s'_h, s'_y))).
    exists (t_intro s' s'_bst s'_avl); simpl in |- *; intros.
    generalize (s'_y x0); clear s'_y; intuition.
    inversion_clear H5; intuition.
    assert (height t3 = 0).
    inversion s2_avl0; AVL s2_avl0; AVL ipattern:H9; AVL ipattern:H10; omega.
    inversion_clear s2_avl0; elim (height_0 H6 H5 H3).
    assert (height t5 = 0).
    inversion s2_avl0; AVL s2_avl0; AVL ipattern:H9; AVL ipattern:H10; omega.
    inversion_clear s2_avl0; elim (height_0 H7 H5 H3).
    (* z0 <> 1 *)
    intros.
    case (split t1 (Node t3 t4 t5 z0)); auto.
    intros (l2, (b, r2)); simpl in |- *; intuition.
    assert (t0_bst : bst t0). inversion_clear s1_bst; trivial.
    assert (t0_avl : avl t0). inversion_clear s1_avl0; trivial.
    case (H t0 l2); trivial.
    assert (cardinal_tree l2 <= cardinal_tree (Node t3 t4 t5 z0))%nat.
    apply cardinal_subset; trivial.
    firstorder. omega.
    intros (union_t0_l2, t0_l2_bst, t0_l2_avl); simpl in |- *; intuition.
    assert (t2_bst : bst t2). inversion_clear s1_bst; trivial.
    assert (t2_avl : avl t2). inversion_clear s1_avl0; trivial.
    case (H t2 r2); trivial.
    assert (cardinal_tree r2 <= cardinal_tree (Node t3 t4 t5 z0))%nat.
    apply cardinal_subset; trivial.
    firstorder. omega.
    intros (union_t2_r2, t2_r2_bst, t2_r2_avl); simpl in |- *; intuition.
    case (join union_t0_l2 t1 union_t2_r2); auto.
    inversion_clear s1_bst; firstorder.
    inversion_clear s1_bst; firstorder.
    intros s' (s'_bst, (s'_avl, (s'_h, s'_y))); clear s'_h.
    exists (t_intro s' s'_bst s'_avl); simpl in |- *; intros.
    generalize (s'_y x0) (a0 x0) (a x0) (H4 x0) (H5 x0);
     clear s'_y a0 a H4 H5; intuition.
    inversion_clear H21; intuition.
    case (X.compare x0 t1); intuition.
    (* z < z0 *)
    case (Z_eq_dec z 1); intro.
    (* z = 1 *)
    case (add_tree t1 (Node t3 t4 t5 z0)); simpl in |- *; auto.
    intros s' (s'_bst, (s'_avl, (s'_h, s'_y))).
    exists (t_intro s' s'_bst s'_avl); simpl in |- *; intros.
    generalize (s'_y x0); clear s'_y; intuition.
    inversion_clear H6; intuition.
    assert (height t0 = 0).
    inversion s1_avl0; AVL s1_avl0; AVL ipattern:H10; AVL ipattern:H11; omega.
    inversion_clear s1_avl0; elim (height_0 H7 H6 H4).
    assert (height t2 = 0).
    inversion s1_avl0; AVL s1_avl0; AVL ipattern:H10; AVL ipattern:H11; omega.
    inversion_clear s1_avl0; elim (height_0 H8 H6 H4).
    (* z <> 1 *)
    intros.
    case (split t4 (Node t0 t1 t2 z)); auto.
    intros (l1, (b, r1)); simpl in |- *; intuition.
    assert (t3_bst : bst t3). inversion_clear s2_bst; trivial.
    assert (t3_avl : avl t3). inversion_clear s2_avl0; trivial.
    case (H l1 t3); trivial.
    assert (cardinal_tree l1 <= cardinal_tree (Node t0 t1 t2 z))%nat.
    apply cardinal_subset; trivial.
    firstorder. simpl in H7; simpl in |- *; omega.
    intros (union_l1_t3, l1_t3_bst, l1_t3_avl); simpl in |- *; intuition.
    assert (t5_bst : bst t5). inversion_clear s2_bst; trivial.
    assert (t5_avl : avl t5). inversion_clear s2_avl0; trivial.
    case (H r1 t5); trivial.
    assert (cardinal_tree r1 <= cardinal_tree (Node t0 t1 t2 z))%nat.
    apply cardinal_subset; trivial.
    firstorder. simpl in H7; simpl in |- *; omega.
    intros (union_r1_t5, r1_t5_bst, r1_t5_avl); simpl in |- *; intuition.
    case (join union_l1_t3 t4 union_r1_t5); auto.
    inversion_clear s2_bst; firstorder.
    inversion_clear s2_bst; firstorder.
    intros s' (s'_bst, (s'_avl, (s'_h, s'_y))); clear s'_h.
    exists (t_intro s' s'_bst s'_avl); simpl in |- *; intros.
    generalize (s'_y x0) (a0 x0) (a x0) (H4 x0) (H5 x0);
     clear s'_y a0 a H4 H5; intuition.
    case (X.compare x0 t4); intuition.
    inversion_clear H21; intuition.
  Qed.

  (** * Filter
<<
    let filter p s =
      let rec filt accu = function
        | Empty -> accu
        | Node(l, v, r, _) ->
            filt (filt (if p v then add v accu else accu) l) r in
      filt Empty s
>> 
  *)

  Definition filter_acc :
    forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
      (s acc : tree),
    bst s ->
    avl s ->
    bst acc ->
    avl acc ->
    {s' : tree |
    bst s' /\
    avl s' /\
    (compat_P E.eq P ->
     forall x : elt, In_tree x s' <-> In_tree x acc \/ In_tree x s /\ P x)}.
  Proof.
    simple induction s; simpl in |- *; intuition.
    (* s = Leaf *)
    exists acc; intuition.
    inversion_clear H4.
    (* s = Node t0 t1 t2 *)
    case (Pdec t1); intro.
    (* P t1 *)
    case (add_tree t1 acc); auto.
    intros acc'; intuition; clear H8 H10.
    case (H acc'); clear H; auto.
    inversion_clear H1; auto.
    inversion_clear H2; auto.
    intros acc''; intuition.
    case (H0 acc''); clear H0; auto.
    inversion_clear H1; auto.
    inversion_clear H2; auto.
    intros s'; intuition; exists s'; do 2 (split; trivial).
    intros HP x; generalize (H9 x) (H10 HP x) (H12 HP x); clear H9 H10 H12;
     intuition.
    right; split.
    apply IsRoot; auto.
    unfold compat_P in HP; apply HP with t1; auto.
    inversion_clear H18; intuition.
    (* ~(P t1) *)
    case (H acc); clear H; auto.
    inversion_clear H1; auto.
    inversion_clear H2; auto.
    intros acc'; intuition.
    case (H0 acc'); clear H0; auto.
    inversion_clear H1; auto.
    inversion_clear H2; auto.
    intros s'; intuition; exists s'; do 2 (split; trivial).
    intros HP x; generalize (H7 HP x) (H9 HP x); clear H7 H9; intuition.
    inversion_clear H13; intuition.
    absurd (P t1); auto.
    unfold compat_P in HP; apply HP with x; auto.
  Qed.

  Definition filter :
    forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x}) (s : t),
    {s' : t | compat_P E.eq P -> forall x : elt, In x s' <-> In x s /\ P x}.
  Proof.
    intros P Pdec (s, s_bst, s_avl).
    case (filter_acc P Pdec s Leaf); auto.
    intros s'; intuition.
    exists (t_intro s' H H1); unfold In in |- *; simpl in |- *; intros.
    generalize (H2 H0 x); clear H2; intuition; inversion_clear H3.
  Qed.

  (** * Partition
<<
    let partition p s =
      let rec part (t, f as accu) = function
        | Empty -> accu
        | Node(l, v, r, _) ->
            part (part (if p v then (add v t, f) else (t, add v f)) l) r in
      part (Empty, Empty) s
>>
  *)

  Definition partition_acc :
    forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
      (s acct accf : tree),
    bst s ->
    avl s ->
    bst acct ->
    avl acct ->
    bst accf ->
    avl accf ->
    {partition : tree * tree |
    let (s1, s2) := partition in
    bst s1 /\
    avl s1 /\
    bst s2 /\
    avl s2 /\
    (compat_P E.eq P ->
     forall x : elt,
     (In_tree x s1 <-> In_tree x acct \/ In_tree x s /\ P x) /\
     (In_tree x s2 <-> In_tree x accf \/ In_tree x s /\ ~ P x))}.
  Proof.
    simple induction s; simpl in |- *; intuition.
    (* s = Leaf *)
    exists (acct, accf); simpl in |- *; intuition; inversion_clear H6.
    (* s = Node t0 t1 t2 *)
    case (Pdec t1); intro.
    (* P t1 *)
    case (add_tree t1 acct); auto.
    intro acct'; intuition; clear H10 H12.
    case (H acct' accf); clear H; auto.
    inversion_clear H1; auto.
    inversion_clear H2; auto.
    intros (acct'', accf'); intuition.
    case (H0 acct'' accf'); clear H0; auto.
    inversion_clear H1; auto.
    inversion_clear H2; auto.
    intros (s1, s2); intuition; exists (s1, s2); do 4 (split; trivial).
    intros HP x; generalize (H11 x) (H14 HP x) (H18 HP x); clear H11 H14 H18;
     intros.
    decompose [and] H11; clear H11.
    decompose [and] H14; clear H14.
    decompose [and] H17; clear H17.
    repeat split; intros.
    elim (H24 H17); intros.
    elim (H21 H20); intros.
    elim (H18 H27); intros.
    right; split; auto.
    apply (HP t1); auto.
    auto.
    right; decompose [and] H27; auto.
    right; decompose [and] H20; auto.
    elim H17; intros.
    apply H25; left; apply H22; left; apply H19; right; trivial.
    decompose [and] H20; clear H20.
    inversion_clear H27.
    apply H25; left; apply H22; left; apply H19; left; trivial.
    apply H25; left; apply H22; right; auto.
    apply H25; right; auto.
    elim (H14 H17); intros.
    elim (H11 H20); intros.
    auto.
    right; decompose [and] H27; auto.
    right; decompose [and] H20; auto.
    elim H17; intros.
    gintuition.
    gintuition.
    inversion_clear H17; gintuition; elim H33; apply (HP t1); auto.
    (* ~(P t1) *)
    case (add_tree t1 accf); auto.
    intro accf'; intuition; clear H10 H12.
    case (H acct accf'); clear H; auto.
    inversion_clear H1; auto.
    inversion_clear H2; auto.
    intros (acct', accf''); intuition.
    case (H0 acct' accf''); clear H0; auto.
    inversion_clear H1; auto.
    inversion_clear H2; auto.
    intros (s1, s2); intuition; exists (s1, s2); do 4 (split; trivial).
    intros HP x; generalize (H11 x) (H14 HP x) (H18 HP x); clear H11 H14 H18;
     intros.
    decompose [and] H11; clear H11.
    decompose [and] H14; clear H14.
    decompose [and] H17; clear H17.
    repeat split; intros.
    elim (H24 H17); intros.
    elim (H21 H20); intros.
    auto.
    right; decompose [and] H27; auto.
    right; decompose [and] H20; auto.
    elim H17; intros.
    apply H25; left; apply H22; left; auto.
    decompose [and] H20; clear H20.
    inversion_clear H27.
    elim f; apply (HP x); auto.
    gintuition.
    gintuition.
    elim (H14 H17); intros.
    elim (H11 H20); intros.
    elim (H18 H27); auto; intros.
    right; split; auto; intro; apply f; apply (HP x); auto.
    right; decompose [and] H27; auto.
    right; decompose [and] H20; auto.
    gintuition.
    inversion_clear H17; gintuition; elim H33; apply (HP t1); auto.
  Qed.

  Definition partition :
    forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x}) (s : t),
    {partition : t * t |
    let (s1, s2) := partition in
    compat_P E.eq P ->
    For_all P s1 /\
    For_all (fun x => ~ P x) s2 /\
    (forall x : elt, In x s <-> In x s1 \/ In x s2)}.
  Proof.
    intros P Pdec (s, s_bst, s_avl).
    case (partition_acc P Pdec s Leaf Leaf); auto.
    intros (s1, s2); intuition.
    exists (t_intro s1 H H1, t_intro s2 H0 H2); unfold In in |- *;
     simpl in |- *; intros.
    unfold For_all, In in |- *; simpl in |- *.
    split; [ idtac | split ]; intro x; generalize (H4 H3 x); clear H4;
     intuition.
    inversion_clear H4.
    inversion_clear H4.
    inversion_clear H7.
    inversion_clear H7.
    case (Pdec x); auto.
    inversion_clear H5.
    inversion_clear H4.
  Qed.

  (** * Subset
<<
    let rec subset s1 s2 =
      match (s1, s2) with
        Empty, _ ->
          true
      | _, Empty ->
          false
      | Node (l1, v1, r1, _), (Node (l2, v2, r2, _) as t2) ->
          let c = Ord.compare v1 v2 in
          if c = 0 then
            subset l1 l2 && subset r1 r2
          else if c < 0 then
            subset (Node (l1, v1, Empty, 0)) l2 && subset r1 t2
          else
            subset (Node (Empty, v1, r1, 0)) r2 && subset l1 t2
>>
  *)

  Definition subset : forall s1 s2 : t, {Subset s1 s2} + {~ Subset s1 s2}.
  Proof.
    unfold Subset, In in |- *.
    intros (s1, s1_bst, s1_avl) (s2, s2_bst, s2_avl); simpl in |- *.
    generalize s1_bst s2_bst; clear s1_bst s1_avl s2_bst s2_avl.
    pattern s1, s2 in |- *; apply cardinal_rec2.
    simple destruct x; simpl in |- *; intuition.
    (* x = Leaf *)
    clear H; left; intros; inversion_clear H.
    (* x = Node t0 t1 t2 z *)
    destruct x' as [| t3 t4 t5 z0]; simpl in |- *; intuition.
    (* x' = Leaf *)
    right; intros.
    assert (In_tree t1 Leaf); auto.
    inversion_clear H1.
    (* x' = Node t3 t4 t5 z0 *)
    case (X.compare t1 t4); intro.
    (* t1 < t4 *)
    case (H (Node t0 t1 Leaf 0) t3); auto; intros.
    simpl in |- *; omega.
    constructor; inversion_clear s1_bst; auto.
    inversion_clear s2_bst; auto.
    (* Subset (Node t0 t1 Leaf) t3 *)
    intros; case (H t2 (Node t3 t4 t5 z0)); auto; intros.
    simpl in |- *; omega.
    inversion_clear s1_bst; auto.
    (* Subset t2 (Node t3 t4 t5 z0) *)
    clear H; left; intuition.
    generalize (i a) (i0 a); clear i i0; inversion_clear H; intuition.
    (* ~ (Subset t2 (Node t3 t4 t5 z0)) *)
    clear H; right; intuition.
    apply f; intuition.
    assert (In_tree a (Node t3 t4 t5 z0)).
    apply H; inversion_clear H0; auto.
    inversion_clear H1.
    inversion_clear H1; auto.
    inversion_clear H0; auto.
    elim (X.lt_not_eq (x:=t1) (y:=t4)); auto.
    apply X.eq_trans with a; auto.
    assert (X.lt a t1).
    inversion_clear s1_bst; apply H4; auto.
    elim (X.lt_not_eq (x:=a) (y:=t4)); auto.
    apply X.lt_trans with t1; auto.
    inversion_clear H1.
    assert (X.lt t4 a).
    inversion_clear s2_bst; apply H5; auto.
    inversion_clear H0; auto.
    elim (X.lt_not_eq (x:=t1) (y:=a)); auto.
    apply X.lt_trans with t4; auto.
    assert (X.lt a t1).
    inversion_clear s1_bst; apply H5; auto.
    elim (ME.lt_not_gt (x:=a) (y:=t1)); auto.
    apply X.lt_trans with t4; auto.
    inversion_clear H3.
    (* t1 = t4 *)
    case (H t0 t3); auto; intros.
    simpl in |- *; omega.
    inversion_clear s1_bst; auto.
    inversion_clear s2_bst; auto.
    (* Subset t0 t3 *)
    case (H t2 t5); auto; intros.
    simpl in |- *; omega.
    inversion_clear s1_bst; auto.
    inversion_clear s2_bst; auto.
    (* Subset t2 t5 *)
    clear H; left; intuition.
    inversion_clear H; intuition.
    apply IsRoot; apply X.eq_trans with t1; auto.
    (* ~(Subset t2 t5) *)
    clear H; right; intuition.
    apply f; intros.
    assert (In_tree a (Node t3 t4 t5 z0)).
    apply H; auto.
    inversion_clear H1; auto.
    elim (X.lt_not_eq (x:=t1) (y:=a)); auto.
    inversion_clear s1_bst; apply H5; auto.
    apply X.eq_trans with t4; auto.
    elim (ME.lt_not_gt (x:=a) (y:=t1)); auto.
    inversion_clear s2_bst.  
    apply ME.lt_eq with t4; auto.
    inversion_clear s1_bst; auto.
    (* ~(Subset t0 t3) *)
    clear H; right; intuition.
    apply f; intros.
    assert (In_tree a (Node t3 t4 t5 z0)).
    apply H; auto.
    inversion_clear H1; auto.
    elim (X.lt_not_eq (x:=a) (y:=t1)); auto.
    inversion_clear s1_bst; auto.
    apply X.eq_trans with t4; auto.
    elim (ME.lt_not_gt (x:=a) (y:=t1)); auto.
    inversion_clear s1_bst; auto.
    inversion_clear s2_bst.  
    apply ME.eq_lt with t4; auto.
    (* t4 < t1 *)
    case (H (Node Leaf t1 t2 0) t5); auto; intros.
    simpl in |- *; omega.
    constructor; inversion_clear s1_bst; auto.
    inversion_clear s2_bst; auto.
    (* Subset (Node Leaf t1 t2) t5 *)
    intros; case (H t0 (Node t3 t4 t5 z0)); auto; intros.
    simpl in |- *; omega.
    inversion_clear s1_bst; auto.
    (* Subset t0 (Node t3 t4 t5 z0) *)
    clear H; left; intuition.
    generalize (i a) (i0 a); clear i i0; inversion_clear H; intuition.
    (* ~ (Subset t2 (Node t3 t4 t5 z0)) *)
    clear H; right; intuition.
    apply f; intuition.
    assert (In_tree a (Node t3 t4 t5 z0)).
    apply H; inversion_clear H0; auto.
    inversion_clear H1.
    inversion_clear H1; auto.
    inversion_clear H0; auto.
    elim (X.lt_not_eq (x:=t4) (y:=t1)); auto.
    apply X.eq_trans with a; auto.
    inversion_clear H1.
    elim (ME.lt_not_gt (x:=a) (y:=t1)); auto.
    apply ME.eq_lt with t4; auto.
    inversion_clear s1_bst; auto.
    inversion_clear H0; auto.
    elim (ME.lt_not_gt (x:=a) (y:=t4)); auto.
    inversion_clear s2_bst; auto.
    apply ME.lt_eq with t1; auto.
    inversion_clear H1.
    elim (ME.lt_not_gt (x:=a) (y:=t1)); auto.
    apply X.lt_trans with t4; inversion_clear s2_bst; auto.
    inversion_clear s1_bst; auto.
  Qed.

  (** [for_all] and [exists] *)

  Definition for_all :
    forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x}) (s : t),
    {compat_P E.eq P -> For_all P s} + {compat_P E.eq P -> ~ For_all P s}.
  Proof.
     intros P Pdec (s, s_bst, s_avl); unfold For_all, In in |- *;
      simpl in |- *. 
     clear s_bst s_avl; induction  s as [| s1 Hrecs1 t0 s0 Hrecs0 z];
      simpl in |- *.
     (* Leaf *)
     left; intros; inversion_clear H0.
     (* Node s1 t0 s0 z *)
     case (Pdec t0); intro.
     (* P t0 *)
     case Hrecs1; clear Hrecs1; intro.
     case Hrecs0; clear Hrecs0; [ left | right ]; intuition.
     inversion_clear H2; firstorder.
     clear Hrecs0; right; firstorder.
     (* ~(P t0) *)
     clear Hrecs0 Hrecs1; right; intros; firstorder.
  Qed.

  Definition exists_ :
    forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x}) (s : t),
    {compat_P E.eq P -> Exists P s} + {compat_P E.eq P -> ~ Exists P s}.
  Proof.
    intros P Pdec (s, s_bst, s_avl); unfold Exists, In in |- *; simpl in |- *. 
    clear s_bst s_avl; induction  s as [| s1 Hrecs1 t0 s0 Hrecs0 z];
     simpl in |- *.
    (* Leaf *)
    right; intros; intro; elim H0; intuition; inversion_clear H2.
    (* Node s1 t0 s0 z *)
    case (Pdec t0); intro.
    (* P t0 *)
    clear Hrecs0 Hrecs1; left; intro; exists t0; auto.
    (* ~(P t0) *)
    case Hrecs1; clear Hrecs1; intro.
    left; intro; elim (e H); intuition; exists x; intuition.
    case Hrecs0; clear Hrecs0; intro.
    left; intro; elim (e H); intuition; exists x; intuition.
    right; intros; intro.
    elim H0; intuition.
    inversion_clear H4; firstorder.
  Qed.

  (** * Fold *)

  Module L := Raw E.

  Fixpoint fold_tree (A : Set) (f : elt -> A -> A) 
   (s : tree) {struct s} : A -> A :=
    match s with
    | Leaf => fun a => a
    | Node l x r _ => fun a => fold_tree A f l (f x (fold_tree A f r a))
    end.
  Implicit Arguments fold_tree [A].

  Definition fold_tree' (A : Set) (f : elt -> A -> A) 
    (s : tree) := L.fold f (elements_tree s).
  Implicit Arguments fold_tree' [A].

  Lemma fold_tree_equiv_aux :
   forall (A : Set) (s : tree) (f : elt -> A -> A) (a : A) (acc : list elt),
   L.fold f (elements_tree_aux acc s) a = fold_tree f s (L.fold f acc a).
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
      (forall x : elt, In x s <-> L.MX.In x l) /\ r = fold_right f i l}.
  Proof.
    intros A f s i; exists (fold_tree f s i).
    rewrite fold_tree_equiv.
    unfold fold_tree' in |- *.
    elim (L.fold_1 (elements_tree_sort _ (is_bst s)) i f); intro l.
    exists l; elim H; clear H; intros H1 (H2, H3); split; auto.
    split; auto.
    intros x; generalize (elements_tree_1 s x) (elements_tree_2 s x).
    generalize (H2 x); unfold In in |- *; firstorder.
  Qed.

  (** * Comparison *)

  (** ** Relations [eq] and [lt] over trees *)
  
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

  Lemma eq_L_eq :
   forall s s' : t, eq s s' -> L.eq (elements_tree s) (elements_tree s').
  Proof.
    unfold eq, Equal, L.eq, L.Equal in |- *; intros.
    generalize (elements_tree_1 s a) (elements_tree_2 s a)
     (elements_tree_1 s' a) (elements_tree_2 s' a) 
     (H a).
    intuition.
  Qed.

  Lemma L_eq_eq :
   forall s s' : t, L.eq (elements_tree s) (elements_tree s') -> eq s s'.
  Proof.
    unfold eq, Equal, L.eq, L.Equal in |- *; intros.
    generalize (elements_tree_1 s a) (elements_tree_2 s a)
     (elements_tree_1 s' a) (elements_tree_2 s' a) 
     (H a).
    intuition.
  Qed.
  Hint Resolve eq_L_eq L_eq_eq.

  Definition lt (s1 s2 : t) : Prop :=
    L.lt (elements_tree s1) (elements_tree s2).

  Definition lt_trans (s s' s'' : t) (h : lt s s') 
    (h' : lt s' s'') : lt s s'' := L.lt_trans h h'.

  Lemma lt_not_eq : forall s s' : t, lt s s' -> ~ eq s s'.
  Proof.
    unfold lt in |- *; intros; intro.
    apply L.lt_not_eq with (s := elements_tree s) (s' := elements_tree s');
     auto.
  Qed.

  (** ** Comparison algorithm 

      The code for [compare s1 s2] is basically comparing
      [elements s1] and [elements s2] in lexicographic order. But it builds
      these lists lazily (it is doing deforestation). It uses
      a function [compare_aux] comparing two lists of trees.

      We slightly modify the original code to get a 
      simplest termination argument. 
      The resulting code is even a bit more efficient.
<<
    let rec compare_aux l1 l2 =
        match (l1, l2) with
        ([], []) -> 0
      | ([], _)  -> -1
      | (_, []) -> 1
      | (Empty :: t1, Empty :: t2) ->
          compare_aux t1 t2
      | (Node(Empty, v1, r1, _) :: t1, Node(Empty, v2, r2, _) :: t2) ->
          let c = Ord.compare v1 v2 in
          if c <> 0 then c else compare_aux (r1::t1) (r2::t2)
      | (Node(Empty, v1, r1, _) :: t1, Empty :: t2) ->
          compare_aux (Node(Empty, v1, r1, 0) :: t1) t2
      | (Node(l1, v1, r1, _) :: t1, t2) when l1 <> Empty ->
          compare_aux (l1 :: Node(Empty, v1, r1, 0) :: t1) t2
      | (Empty :: t1, Node(Empty, v2, r2, _) :: t2) ->
          compare_aux t1 (Node(Empty, v2, r2, 0) :: t2)
      | (t1, Node(l2, v2, r2, _) :: t2) (* when l2 <> Empty *) ->
          compare_aux t1 (l2 :: Node(Empty, v2, r2, 0) :: t2)
>>
*)

  (** ** Lists of trees *)

  (** [flatten l] returns the list of elements of [l] i.e. the list
      of elements actually compared *)
  
  Fixpoint flatten (l : list tree) : list elt :=
    match l with
    | [] => []
    | t :: r => elements_tree t ++ flatten r
    end.

  (** [sorted_l l] expresses that elements in the trees of [l] are
      sorted, and that all trees in [l] are binary search trees. *)

  Inductive In_tree_l : elt -> list tree -> Prop :=
    | InHd :
        forall (x : elt) (s : tree) (l : list tree),
        In_tree x s -> In_tree_l x (s :: l)
    | InTl :
        forall (x : elt) (s : tree) (l : list tree),
        In_tree_l x l -> In_tree_l x (s :: l).

  Hint Constructors In_tree_l.

  Inductive sorted_l : list tree -> Prop :=
    | SortedLNil : sorted_l []
    | SortedLCons :
        forall (s : tree) (l : list tree),
        bst s ->
        sorted_l l ->
        (forall x : elt,
         In_tree x s -> forall y : elt, In_tree_l y l -> X.lt x y) ->
        sorted_l (s :: l).

  Hint Constructors sorted_l.

  Lemma sort_app :
   forall l1 l2 : list elt,
   L.MX.Sort l1 ->
   L.MX.Sort l2 ->
   (forall x y : elt, L.MX.In x l1 -> L.MX.In y l2 -> X.lt x y) ->
   L.MX.Sort (l1 ++ l2).
  Proof.
    simple induction l1; simpl in |- *; intuition.
    apply cons_sort; auto.
    apply H; auto.
    inversion_clear H0; trivial.
    induction  l as [| a0 l Hrecl]; simpl in |- *; intuition.
    induction  l2 as [| a0 l2 Hrecl2]; simpl in |- *; intuition. 
   inversion_clear H0; inversion_clear H4; auto.
  Qed.

  Lemma in_app :
   forall (x : elt) (l1 l2 : list elt),
   L.MX.In x (l1 ++ l2) -> L.MX.In x l1 \/ L.MX.In x l2.
  Proof.
    simple induction l1; simpl in |- *; intuition.
    inversion_clear H0; auto.
    elim (H l2 H1); auto.
  Qed.

  Lemma in_flatten :
   forall (x : elt) (l : list tree), L.MX.In x (flatten l) -> In_tree_l x l.
  Proof.
    simple induction l; simpl in |- *; intuition.
    inversion_clear H.
    elim (in_app x _ _ H0); auto.
  Qed.

  Lemma sorted_flatten :
   forall l : list tree, sorted_l l -> L.MX.Sort (flatten l).
  Proof.
    simple induction l; simpl in |- *; intuition.
    apply sort_app; inversion H0; auto.
    intros; apply H5; auto.
    apply in_flatten; auto.
  Qed.

  (** ** Termination of [compare_aux]

     The measure is given by
     [m([]) = 0], [m(s :: l) = m(s) + m(l)],
     [m(Leaf) = 1], and [m(Node(l,_,r,_) = 1 + 3m(l) + m(r)] *)

  Fixpoint measure_t (s : tree) : Z :=
    match s with
    | Leaf => 1
    | Node l _ r _ => 1 + 3 * measure_t l + measure_t r
    end.

  Fixpoint measure_l (l : list tree) : Z :=
    match l with
    | [] => 0
    | s :: l => measure_t s + measure_l l
    end.

  Ltac Measure_t := unfold measure_t in |- *; fold measure_t in |- *.
  Ltac Measure_l := unfold measure_l in |- *; fold measure_l in |- *.

  Lemma measure_t_1 : forall s : tree, measure_t s >= 1.
  Proof.
    simple induction s.
    simpl in |- *; omega.
    intros.
    Measure_t; omega. (* BUG Simpl! *)
  Qed.

  Ltac Measure_t_1 s := generalize (measure_t_1 s); intro.

  Lemma measure_t_3 :
   forall (l r : tree) (x : elt) (z : Z), measure_t (Node l x r z) >= 3.
  Proof.
    intros; Measure_t.
    generalize (measure_t_1 l) (measure_t_1 r); intros; omega.
  Qed.

  Ltac Measure_t_3 l x r z := generalize (measure_t_3 l x r z); intro.

  Lemma measure_l_0 : forall l : list tree, measure_l l >= 0.
  Proof.
    simple induction l.
    simpl in |- *; omega.
    intros.
    Measure_l; Measure_t_1 a; omega.
  Qed.

  Ltac Measure_l_0 l := generalize (measure_l_0 l); intro.

  (** Induction principle over the sum of the measures for two lists *)

  Definition compare_rec2 :
    forall P : list tree -> list tree -> Set,
    (forall x x' : list tree,
     (forall y y' : list tree,
      measure_l y + measure_l y' < measure_l x + measure_l x' -> P y y') ->
     P x x') -> forall x x' : list tree, P x x'.
  Proof.
    intros P H x x'.
    apply
     well_founded_induction_type_2
      with
        (R := fun yy' xx' : list tree * list tree =>
              measure_l (fst yy') + measure_l (snd yy') <
              measure_l (fst xx') + measure_l (snd xx')); 
     auto.                      
    apply
     Wf_nat.well_founded_lt_compat
      with
        (f := fun xx' : list tree * list tree =>
              Zabs_nat (measure_l (fst xx') + measure_l (snd xx'))).
    intros; apply Zabs.Zabs_nat_lt.
    Measure_l_0 (fst x0); Measure_l_0 (snd x0); Measure_l_0 (fst y);
     Measure_l_0 (snd y); intros; omega.
(***
    Intros P H.
    Assert (n:Z)0<=n->(x,x':(list tree))n=(measure_l x)+(measure_l x')->(P x x').
    Intros n Hn; Pattern n; Apply Z_lt_rec; Auto.
    Intuition.
    Apply H; Intros.
    Apply (H0 ((measure_l y)+(measure_l y'))).
    Measure_l_0 y; Measure_l_0 y'; Omega.
    Omega.
    Intros; Apply (H0 ((measure_l x)+(measure_l x'))); Trivial.
    Measure_l_0 x; Measure_l_0 x'; Omega.
***)
  Qed.

  (** ** Lemmas for the correctness of [compare] *)

  Lemma lt_nil_elements_tree_Node :
   forall (l r : tree) (x : elt) (z : Z),
   L.lt [] (elements_tree (Node l x r z)).
  Proof.
    unfold elements_tree in |- *; simpl in |- *; intros l r x z; clear z.
    generalize (elements_tree_aux [] r) x.
    induction l; simpl in |- *; intuition.
  Qed.

  Lemma lt_app : forall l1 l2 l3 : list elt, L.lt l1 l2 -> L.lt l1 (l2 ++ l3). 
  Proof.
    simple induction 1; simpl in |- *; intuition.
  Qed.

  Lemma lt_app_eq :
   forall l1 l2 l3 : list elt, L.lt l2 l3 -> L.lt (l1 ++ l2) (l1 ++ l3). 
  Proof.
    simple induction l1; simpl in |- *; intuition.
  Qed.

  Lemma lt_eq_1 :
   forall l1 l2 l3 : list elt, l1 = l2 -> L.lt l1 l3 -> L.lt l2 l3. 
  Proof.
    intros; rewrite <- H; auto.
  Qed.

  Lemma lt_eq_2 :
   forall l1 l2 l3 : list elt, l2 = l3 -> L.lt l1 l2 -> L.lt l1 l3. 
  Proof.
    intros; rewrite <- H; auto.
  Qed.

  Lemma eq_eq_1 :
   forall l1 l2 l3 : list elt, l1 = l2 -> L.eq l1 l3 -> L.eq l2 l3. 
  Proof.
    intros; rewrite <- H; auto.
  Qed.

  Lemma eq_eq_2 :
   forall l1 l2 l3 : list elt, l2 = l3 -> L.eq l1 l2 -> L.eq l1 l3. 
  Proof.
    intros; rewrite <- H; auto.
  Qed.

  Lemma l_eq_cons :
   forall (l1 l2 : list elt) (x y : elt),
   X.eq x y -> L.eq l1 l2 -> L.eq (x :: l1) (y :: l2).
  Proof.
    unfold L.eq, L.Equal in |- *; intuition.
    inversion_clear H1; generalize (H0 a); clear H0; intuition.
    apply L.In_eq with x; auto.
    inversion_clear H1; generalize (H0 a); clear H0; intuition.
    apply L.In_eq with y; auto.
  Qed.

  Hint Resolve lt_nil_elements_tree_Node lt_app lt_app_eq lt_eq_1 lt_eq_2
    eq_eq_1 eq_eq_2 l_eq_cons.

  Lemma elements_app :
   forall (s : tree) (acc : list elt),
   elements_tree_aux acc s = elements_tree s ++ acc.
  Proof.
    simple induction s; simpl in |- *; intuition.
    rewrite H0.
    rewrite H.
    unfold elements_tree in |- *; simpl in |- *.
    do 2 rewrite H.
    rewrite H0.
    repeat rewrite <- app_nil_end.
    repeat rewrite app_ass; auto.
  Qed.

  (** main lemma for correctness of [compare] *)
  Lemma compare_flatten :
   forall (l r : tree) (x : elt) (z : Z) (tl : list tree),
   flatten (Node l x r z :: tl) = flatten (l :: Node Leaf x r z :: tl).
  Proof.
    simpl in |- *; unfold elements_tree in |- *; simpl in |- *; intuition.
    repeat rewrite elements_app.
    repeat rewrite <- app_nil_end.
    repeat rewrite app_ass; auto.
  Qed.

  Hint Resolve compare_flatten.

  (** same lemma, expressed differently *)
  Lemma compare_flatten_1 :
   forall (t0 t2 : tree) (t1 : elt) (z : Z) (l : list elt),
   elements_tree t0 ++ t1 :: elements_tree t2 ++ l =
   elements_tree (Node t0 t1 t2 z) ++ l.
  Proof.
    simpl in |- *; unfold elements_tree in |- *; simpl in |- *; intuition.
    repeat rewrite elements_app.
    repeat rewrite <- app_nil_end.
    repeat rewrite app_ass; auto.
  Qed.

  Hint Resolve compare_flatten_1.

  (** invariant for [compare l1 l2]: [Leaf] may only occur on head
      of [l1] and [l2], and only when the other list is non-empty *)

  Fixpoint no_leaf (l : list tree) : Prop :=
    match l with
    | [] => True
    | Leaf :: _ => False
    | _ :: r => no_leaf r
    end.

  Inductive leaf_invariant : list tree -> list tree -> Prop :=
    | LI_nil_l : forall l : list tree, no_leaf l -> leaf_invariant [] l
    | LI_l_nil : forall l : list tree, no_leaf l -> leaf_invariant l []
    | LI_leaf_leaf :
        forall l1 l2 : list tree,
        no_leaf l1 -> no_leaf l2 -> leaf_invariant (Leaf :: l1) (Leaf :: l2)
    | LI_leaf_l :
        forall l1 l2 : list tree,
        no_leaf l1 ->
        no_leaf l2 -> l2 <> [] -> leaf_invariant (Leaf :: l1) l2
    | LI_l_leaf :
        forall l1 l2 : list tree,
        no_leaf l1 ->
        no_leaf l2 -> l1 <> [] -> leaf_invariant l1 (Leaf :: l2)
    | LI_l_l :
        forall l1 l2 : list tree,
        no_leaf l1 ->
        no_leaf l2 -> l1 <> [] -> l2 <> [] -> leaf_invariant l1 l2.

  Hint Constructors leaf_invariant.

  Lemma no_leaf_invariant :
   forall l1 l2 : list tree, no_leaf l1 -> no_leaf l2 -> leaf_invariant l1 l2.
  Proof.
    simple destruct l1; simple destruct l2; intuition.
  Qed.

  Hint Resolve no_leaf_invariant.

  (** ** [compare_aux] and [compare] *) 

  Definition compare_aux :
    forall l1 l2 : list tree,
    sorted_l l1 ->
    sorted_l l2 ->
    leaf_invariant l1 l2 -> Compare L.lt L.eq (flatten l1) (flatten l2).
  Proof.
    intros l1 l2; pattern l1, l2 in |- *; apply compare_rec2.
    simple destruct x; simple destruct x'; intuition.
    (* x = x' = nil *)
    constructor 2; unfold L.eq, L.Equal in |- *; intuition.
    (* x = nil *)
    constructor 1; simpl in |- *; auto.
    inversion_clear H2; intuition.
    destruct t0 as [| t0 t1 t2 z]; inversion_clear H1; simpl in |- *.
    elim H3.
    auto.
    (* x <> nil, x' = nil *)
    constructor 3; simpl in |- *; auto.
    destruct t0 as [| t0 t1 t2 z]; inversion_clear H0; simpl in |- *.
    inversion_clear H2; intuition.
    elim H0.
    auto.
    (* x,x' <> nil *)
    destruct t0 as [| t0 t2 t3 z];
     [ destruct t1 as [| t0 t1 t2 z] | destruct t1 as [| t1 t4 t5 z0] ];
     simpl in |- *.
    (* Leaf :: l, Leaf :: l0 *)
    case (H l l0); clear H; auto; intros.
    Measure_l; unfold measure_t in |- *; omega.
    inversion_clear H0; trivial.
    inversion_clear H1; trivial.
    inversion_clear H2; intuition.
    elim H3. elim H. elim H.
    constructor 1; auto.
    constructor 2; auto.    
    constructor 3; auto.
    (* Leaf :: l, (Node t0 t1 t2) :: l0 *)
    destruct t0 as [| t0 t3 t4 z0]; simpl in |- *.
    (* Leaf :: l, (Node Leaf t1 t2) :: l0 *)
    case (H l (Node Leaf t1 t2 z :: l0)); clear H; auto; intros.
    Measure_l; Measure_t; omega.
    inversion_clear H0; auto.
    inversion_clear H2; intuition; elim H.
    constructor 1; auto.
    constructor 2; auto.
    constructor 3; auto.
    (* Leaf :: l, (Node (Node t0 t3 t4) t1 t2) :: l0 *)
    case (H (Leaf :: l) (Node t0 t3 t4 z0 :: Node Leaf t1 t2 z :: l0));
     clear H; auto; intros.
    Measure_l; Measure_t. Measure_t_1 t0; Measure_t_1 t4; omega.
    constructor; inversion_clear H1; auto.
    inversion_clear H; auto.
    constructor; auto.
    inversion_clear H; auto.
    intros; inversion_clear H1.
    apply H4; auto.
    inversion_clear H6.
    apply H4; auto.
    intros; inversion_clear H5; auto.
    inversion_clear H.
    inversion_clear H6; auto.
    apply ME.lt_eq with t1; auto.
    inversion_clear H.
    apply X.lt_trans with t1; auto.
    inversion_clear H2; intuition.
    constructor 1; rewrite <- compare_flatten_1; auto.
    constructor 2; rewrite <- compare_flatten_1; auto.
    constructor 3; rewrite <- compare_flatten_1; auto.
    (* (Node t0 t2 t3) :: l, Leaf :: l0 *)
    destruct t0 as [| t0 t1 t4 z0]; simpl in |- *.
    (* (Node Leaf t2 t3) :: l, Leaf :: l0 *)
    case (H (Node Leaf t2 t3 z :: l) l0); clear H; auto; intros.
    Measure_l; Measure_t; omega.
    inversion_clear H1; auto.
    inversion_clear H2; intuition; elim H3.
    constructor 1; auto.
    constructor 2; auto.
    constructor 3; auto.
    (* (Node (Node t0 t1 t4) t2 t3) :: l, Leaf :: l0 *)
    case (H (Node t0 t1 t4 z0 :: Node Leaf t2 t3 z :: l) (Leaf :: l0));
     clear H; auto; intros.
    Measure_l; Measure_t. Measure_t_1 t0; Measure_t_1 t4; omega.
    constructor; inversion_clear H0; auto.
    inversion_clear H; auto.
    constructor; auto.
    inversion_clear H; auto.
    intros; inversion_clear H0.
    apply H4; auto.
    inversion_clear H6.
    apply H4; auto.
    intros; inversion_clear H5; auto.
    inversion_clear H6; auto.
    apply ME.lt_eq with t2; auto.
    inversion_clear H; auto.
    inversion_clear H5.
    apply X.lt_trans with t2; inversion_clear H; auto.
    inversion_clear H2; intuition; elim H3.
    constructor 1; rewrite <- compare_flatten_1; auto. 
    constructor 2; rewrite <- compare_flatten_1; auto. 
    constructor 3; rewrite <- compare_flatten_1; auto. 
    (* (Node t0 t2 t3)::l, (Node t1 t4 t5)::l0) *)
    destruct t0 as [| t0 t6 t7 z1];
     [ destruct t1 as [| t0 t1 t6 z1] | destruct t1 as [| t1 t8 t9 z2] ];
     simpl in |- *.
    (* (Node Leaf t2 t3)::l, (Node Leaf t4 t5)::l0) *)
    case (X.compare t2 t4); intro.
    (* t2 < t4 *)
    constructor 1; auto.
    (* t2 = t4 *)
    case (H (t3 :: l) (t5 :: l0)); clear H; auto; intros.
    Measure_l; Measure_t. Measure_t_1 t3; Measure_t_1 t5; omega.
    constructor; inversion_clear H0; auto.
    inversion_clear H; trivial.
    inversion_clear H1; constructor; intuition.
    inversion_clear H; trivial.
    inversion_clear H2; intros.
    destruct t3 as [| t0 t1 t3 z1];
     [ destruct t5 as [| t0 t1 t3 z1] | destruct t5 as [| t5 t6 t7 z2] ];
     intuition.
    constructor 1; auto.
    constructor 2; auto.
    constructor 3; auto.
    (* t4 < t2 *)
    constructor 3; auto.
    (* (Node Leaf t2 t3)::l, (Node (Node t0 t1 t6) t4 t5)::l0) *)
    case
     (H (Node Leaf t2 t3 z :: l)
        (Node t0 t1 t6 z1 :: Node Leaf t4 t5 z0 :: l0)); 
     clear H; auto; intros.
    Measure_l; Measure_t. 
    Measure_t_1 t3; Measure_t_1 t5; Measure_t_1 t0; Measure_t_1 t6; omega.
    inversion_clear H1.
    constructor; intuition.
    inversion_clear H; trivial.
    constructor; intuition.
    inversion_clear H; auto.
    inversion_clear H1; auto.
    inversion_clear H6.
    inversion_clear H.
    inversion_clear H5; auto.
    inversion_clear H; auto.
    apply ME.lt_eq with t4; auto.
    inversion_clear H5.
    apply X.lt_trans with t4; auto.
    inversion_clear H2; intuition.
    constructor 1; rewrite <- compare_flatten_1; auto. 
    constructor 2; rewrite <- compare_flatten_1; auto. 
    constructor 3; rewrite <- compare_flatten_1; auto. 
    (* Node (Node t0 t6 t7) t2 t3 :: l, Node Leaf t4 t5 :: l0 *)
    case
     (H (Node t0 t6 t7 z1 :: Node Leaf t2 t3 z :: l)
        (Node Leaf t4 t5 z0 :: l0)); clear H; auto; 
     intros.
    Measure_l; Measure_t. 
    Measure_t_1 t3; Measure_t_1 t5; Measure_t_1 t0; Measure_t_1 t5;
     Measure_t_1 t7; omega.
    inversion_clear H0.
    constructor; intuition.
    inversion_clear H; trivial.
    constructor; intuition.
    inversion_clear H; auto.
    inversion_clear H0; auto.
    inversion_clear H6.
    inversion_clear H.
    inversion_clear H5; auto.
    inversion_clear H; auto.
    apply ME.lt_eq with t2; auto.
    inversion_clear H5.
    apply X.lt_trans with t2; auto.
    inversion_clear H2; intuition.
    constructor 1; rewrite <- compare_flatten_1; auto. 
    constructor 2; rewrite <- compare_flatten_1; auto. 
    constructor 3; rewrite <- compare_flatten_1; auto. 
    (* Node (Node t0 t6 t7) t2 t3 :: l, Node (Node t1 t8 t9) t4 t5 :: l0 *)
    case
     (H (Node t0 t6 t7 z1 :: Node Leaf t2 t3 z :: l)
        (Node (Node t1 t8 t9 z2) t4 t5 z0 :: l0)); 
     clear H; auto; intros.
    Measure_l; Measure_t. 
    Measure_t_1 t3; Measure_t_1 t5; Measure_t_1 t0; Measure_t_1 t5;
     Measure_t_1 t7; omega.
    inversion_clear H0.
    constructor; intuition.
    inversion_clear H; trivial.
    constructor; intuition.
    inversion_clear H; auto.
    inversion_clear H0; auto.
    inversion_clear H6.
    inversion_clear H.
    inversion_clear H5; auto.
    inversion_clear H; auto.
    apply ME.lt_eq with t2; auto.
    inversion_clear H5.
    apply X.lt_trans with t2; auto.
    inversion_clear H2; intuition.
    constructor 1; rewrite <- compare_flatten_1; auto. 
    constructor 2; rewrite <- compare_flatten_1; auto. 
    constructor 3; rewrite <- (compare_flatten_1 (Node t0 t6 t7 z1)); auto. 
  Qed.

  Lemma flatten_elements :
   forall s : tree, flatten (s :: []) = elements_tree s.
  Proof.
    simpl in |- *; intros; rewrite <- app_nil_end; auto.
  Qed.

  Definition compare : forall s1 s2 : t, Compare lt eq s1 s2.
  Proof.
    intros (s1, s1_bst, s1_avl) (s2, s2_bst, s2_avl); unfold lt, eq in |- *;
     simpl in |- *.
    case (compare_aux (s1 :: []) (s2 :: [])); intros.
    constructor; intuition; inversion_clear H0.
    constructor; intuition; inversion_clear H0.
    destruct s1 as [| t0 t1 t2 z];
     [ destruct s2 as [| t0 t1 t2 z] | destruct s2 as [| t3 t4 t5 z0] ];
     simpl in |- *; constructor; simpl in |- *; intuition; 
     discriminate H.
    constructor 1; simpl in |- *; repeat rewrite <- flatten_elements; auto.
    constructor 2.
    apply L_eq_eq; simpl in |- *; repeat rewrite <- flatten_elements; auto.
    constructor 3; simpl in |- *; repeat rewrite <- flatten_elements; auto.
  Qed.

  (** * Equality test *)

  Definition equal : forall s s' : t, {Equal s s'} + {~ Equal s s'}.
  Proof.
    intros s s'; case (compare s s'); intro.
    right; apply lt_not_eq; auto.
    left; auto.
    right; intro; apply (lt_not_eq s' s); auto; apply eq_sym; auto.
  Qed.


  (** A new comparison algorithm suggested by Xavier Leroy:

type enumeration = End | More of elt * t * enumeration

let rec cons s e = match s with
  | Empty -> e
  | Node(l, v, r, _) -> cons l (More(v, r, e))

let rec compare_aux e1 e2 = match (e1, e2) with
  | (End, End) -> 0
  | (End, More _) -> -1
  | (More _, End) -> 1
  | (More(v1, r1, k1), More(v2, r2, k2)) ->
      let c = Ord.compare v1 v2 in
      if c <> 0 then c else compare_aux (cons r1 k1) (cons r2 k2)

let compare s1 s2 = compare_aux (cons s1 End) (cons s2 End)
*)

  (** ** Enumeration of the elements of a tree *)

  Inductive enumeration : Set :=
   | End : enumeration
   | More : elt -> tree -> enumeration -> enumeration.

  (** [flatten_e e] returns the list of elements of [e] i.e. the list
      of elements actually compared *)
 
   Fixpoint flatten_e (e : enumeration) : list elt :=
    match e with
    | End => []
    | More x t r => x :: elements_tree t ++ flatten_e r
    end.

  (** [sorted_e e] expresses that elements in the enumeration [e] are
      sorted, and that all trees in [e] are binary search trees. *)

  Inductive In_tree_e (x:elt) : enumeration -> Prop :=
    | InEHd1 :
        forall (y : elt) (s : tree) (e : enumeration),
        X.eq x y -> In_tree_e x (More y s e)
    | InEHd2 :
        forall (y : elt) (s : tree) (e : enumeration),
        In_tree x s -> In_tree_e x (More y s e)
    | InETl :
        forall (y : elt) (s : tree) (e : enumeration),
        In_tree_e x e -> In_tree_e x (More y s e).

  Hint Constructors In_tree_e.

  Inductive sorted_e : enumeration -> Prop :=
    | SortedEEnd : sorted_e End
    | SortedEMore :
        forall (x : elt) (s : tree) (e : enumeration),
        bst s ->
        (gt_tree x s) ->
        sorted_e e ->
        (forall y : elt, In_tree_e y e -> X.lt x y) ->
        (forall y : elt,
         In_tree y s -> forall z : elt, In_tree_e z e -> X.lt y z) ->
        sorted_e (More x s e).

  Hint Constructors sorted_e.

  Lemma in_flatten_e :
   forall (x : elt) (e : enumeration), L.MX.In x (flatten_e e) -> In_tree_e x e.
  Proof.
    simple induction e; simpl in |- *; intuition.
    inversion_clear H.
    inversion_clear H0; auto.
    elim (in_app x _ _ H1); auto.
  Qed.

  Lemma sorted_flatten_e :
   forall e : enumeration, sorted_e e -> L.MX.Sort (flatten_e e).
  Proof.
    simple induction e; simpl in |- *; intuition.
    apply cons_sort.
    apply sort_app; inversion H0; auto.
    intros; apply H8; auto.
    apply in_flatten_e; auto.
    apply L.MX.Inf_In.
    inversion_clear H0.
    intros; elim (in_app_or _ _ _ H0); intuition.
    apply H4; apply in_flatten_e; auto.
  Qed.

  (** key lemma for correctness *)

  Lemma flatten_e_elements :
    forall (x : elt) (l r : tree) (z : Z) (e : enumeration),
    elements_tree l ++ flatten_e (More x r e) =
    elements_tree (Node l x r z) ++ flatten_e e.
  Proof.
    intros; simpl.
    apply compare_flatten_1.
  Qed.

  (** termination of [compare_aux] *)
 
  Fixpoint measure_e_t (s : tree) : Z :=
    match s with
    | Leaf => 0
    | Node l _ r _ => 1 + measure_e_t l + measure_e_t r
    end.

  Fixpoint measure_e (e : enumeration) : Z :=
    match e with
    | End => 0
    | More _ s r => 1 + measure_e_t s + measure_e r
    end.

  Ltac Measure_e_t := unfold measure_e_t in |- *; fold measure_e_t in |- *.
  Ltac Measure_e := unfold measure_e in |- *; fold measure_e in |- *.

  Lemma measure_e_t_0 : forall s : tree, measure_e_t s >= 0.
  Proof.
    simple induction s.
    simpl in |- *; omega.
    intros.
    Measure_e_t; omega. (* BUG Simpl! *)
  Qed.

  Ltac Measure_e_t_0 s := generalize (measure_e_t_0 s); intro.

  Lemma measure_e_0 : forall e : enumeration, measure_e e >= 0.
  Proof.
    simple induction e.
    simpl in |- *; omega.
    intros.
    Measure_e; Measure_e_t_0 t0; omega.
  Qed.

  Ltac Measure_e_0 e := generalize (measure_e_0 e); intro.

  (** Induction principle over the sum of the measures for two lists *)

  Definition compare2_rec2 :
    forall P : enumeration -> enumeration -> Set,
    (forall x x' : enumeration,
     (forall y y' : enumeration,
      measure_e y + measure_e y' < measure_e x + measure_e x' -> P y y') ->
     P x x') -> forall x x' : enumeration, P x x'.
  Proof.
    intros P H x x'.
    apply
     well_founded_induction_type_2
      with
        (R := fun yy' xx' : enumeration * enumeration =>
              measure_e (fst yy') + measure_e (snd yy') <
              measure_e (fst xx') + measure_e (snd xx')); 
     auto.                      
    apply
     Wf_nat.well_founded_lt_compat
      with
        (f := fun xx' : enumeration * enumeration =>
              Zabs_nat (measure_e (fst xx') + measure_e (snd xx'))).
    intros; apply Zabs.Zabs_nat_lt.
    Measure_e_0 (fst x0); Measure_e_0 (snd x0); Measure_e_0 (fst y);
     Measure_e_0 (snd y); intros; omega.
  Qed.

  (** [cons t e] adds the elements of tree [t] on the head of 
      enumeration [e]. Code:
 
  let rec cons s e = match s with
  | Empty -> e
  | Node(l, v, r, _) -> cons l (More(v, r, e))
  *)

  Definition cons :
    forall (s : tree) (e : enumeration),
    bst s ->
    sorted_e e ->
    (forall (x y : elt), In_tree x s -> In_tree_e y e -> X.lt x y) ->
    { r : enumeration 
    | sorted_e r /\ 
      measure_e r = measure_e_t s + measure_e e /\
      flatten_e r = elements_tree s ++ flatten_e e
      (* forall (x : elt), In_tree_e x r <-> (In_tree x s \/ In_tree_e x e) *)
    }.
  Proof.
    simple induction s; intuition.
    (* s = Leaf *)
    exists e; intuition.
    (* s = Node t0 t1 t2 z *)
    clear H0.
    case (H (More t1 t2 e)); clear H; intuition.
    inversion_clear H1; auto.
    constructor; inversion_clear H1; auto.
    inversion_clear H0; intuition.
    inversion_clear H1.
    apply ME.lt_eq with t1; auto.
    inversion_clear H1.
    apply X.lt_trans with t1; auto.
    exists x; intuition.
    generalize H4; Measure_e; intros; Measure_e_t; omega.
    rewrite H5.
    apply flatten_e_elements.
  Qed.

  Definition compare2_aux :
    forall e1 e2 : enumeration,
    sorted_e e1 ->
    sorted_e e2 ->
    Compare L.lt L.eq (flatten_e e1) (flatten_e e2).
  Proof.
    intros e1 e2; pattern e1, e2 in |- *; apply compare2_rec2.
    simple destruct x; simple destruct x'; intuition.
    (* x = x' = End *)
    constructor 2; unfold L.eq, L.Equal in |- *; intuition.
    (* x = End x' = More *)
    constructor 1; simpl in |- *; auto.
    (* x = More x' = End *)
    constructor 3; simpl in |- *; auto.
    (* x = More e t0 e0, x' = More e3 t1 e4 *)
    case (X.compare e e3); intro.
    (* e < e3 *)
    constructor 1; simpl; auto.
    (* e = e3 *)
    case (cons t0 e0).
    inversion_clear H0; auto.
    inversion_clear H0; auto.
    inversion_clear H0; auto.
    intro c1; intuition.
    case (cons t1 e4).
    inversion_clear H1; auto.
    inversion_clear H1; auto.
    inversion_clear H1; auto.
    intro c2; intuition.
    case (H c1 c2); clear H; intuition.
    Measure_e; omega.
    constructor 1; simpl.
    apply L.lt_cons_eq; auto.
    rewrite H5 in l; rewrite H8 in l; auto.
    constructor 2; simpl.
    apply l_eq_cons; auto.
    rewrite H5 in e6; rewrite H8 in e6; auto.
    constructor 3; simpl.
    apply L.lt_cons_eq; auto.
    rewrite H5 in l; rewrite H8 in l; auto.
    (* e > e3 *)
    constructor 3; simpl; auto.
  Qed.

  Definition compare2 : forall s1 s2 : t, Compare lt eq s1 s2.
  Proof.
    intros (s1, s1_bst, s1_avl) (s2, s2_bst, s2_avl); unfold lt, eq in |- *;
     simpl in |- *.
    case (cons s1 End); intuition.
    inversion_clear H0.
    case (cons s2 End); intuition.
    inversion_clear H3.
    simpl in H2; rewrite <- app_nil_end in H2.
    simpl in H5; rewrite <- app_nil_end in H5.
    case (compare2_aux x x0); intuition.
    constructor 1; simpl in |- *.
    rewrite H2 in l; rewrite H5 in l; auto.
    constructor 2; apply L_eq_eq; simpl in |- *.
    rewrite H2 in e; rewrite H5 in e; auto.
    constructor 3; simpl in |- *.
    rewrite H2 in l; rewrite H5 in l; auto.
  Qed.

End Make.






