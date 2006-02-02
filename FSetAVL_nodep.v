
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

Module Raw (X: OrderedType).

  Module E := X.
  Module ME := OrderedTypeFacts X.

  Definition elt := X.t.

  (** * Trees *)

  Inductive tree : Set :=
    | Leaf : tree
    | Node : tree -> X.t -> tree -> Z -> tree.

  (** The fourth field of [Node] is the height of the tree *)

  (** * Occurrence in a tree *)

  Inductive In (x : elt) : tree -> Prop :=
    | IsRoot :
        forall (l r : tree) (h : Z) (y : elt),
        X.eq x y -> In x (Node l y r h)
    | InLeft :
        forall (l r : tree) (h : Z) (y : elt),
        In x l -> In x (Node l y r h)
    | InRight :
        forall (l r : tree) (h : Z) (y : elt),
        In x r -> In x (Node l y r h).

  Hint Constructors In.

  (** [In] is compatible with [X.eq] *)

  Lemma In_1 :
   forall (s : tree) (x y : elt), X.eq x y -> In x s -> In y s.
  Proof.
    simple induction s; simpl in |- *; intuition.
    inversion_clear H0.
    inversion_clear H2; intuition eauto.
  Qed.
 
  Hint Immediate In_1.

  (** [In] is height-insensitive *)

  Lemma In_height :
   forall (h h' : Z) (x y : elt) (l r : tree),
   In y (Node l x r h) -> In y (Node l x r h').
  Proof.
    inversion 1; auto.
  Qed.
  Hint Resolve In_height.

  (** * Binary search trees *)

  (** [lt_tree x s]: all elements in [s] are smaller than [x] 
      (resp. greater for [gt_tree]) *)

  Definition lt_tree (x : elt) (s : tree) :=
    forall y : elt, In y s -> X.lt y x.
  Definition gt_tree (x : elt) (s : tree) :=
    forall y : elt, In y s -> X.lt x y.

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
   forall (x : elt) (t : tree), lt_tree x t -> ~ In x t.
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
   forall (x : elt) (t : tree), gt_tree x t -> ~ In x t.
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

  (** * AVL trees *)

  (** [avl s] : [s] is a properly balanced AVL tree,
      i.e. for any node the heights of the two children
      differ by at most 2 *)

  Definition height (s : tree) : Z :=
    match s with
    | Leaf => 0
    | Node _ _ _ h => h
    end.

  Notation max := Zmax. 

 Lemma max_spec : forall x y, 
    x >= y /\ max x y = x  \/
    x <= y /\ max x y = y.
 Proof.
 intros.
 unfold max, Zle, Zge.
 destruct (Zcompare x y). 
 left; split; auto; discriminate.
 right; split; auto; discriminate.
 left; split; auto; discriminate.
 Qed.

 Ltac omega_max := 
   let om x y := 
       generalize (max_spec x y); 
       let z := fresh "z" in 
       let Hz := fresh "Hz" in 
       (set (z:=Zmax x y) in *; clearbody z; intro Hz)
   in 
   match goal with 
      | |- context id [ max ?x ?y ] => om x y; omega_max
      | H:context id [ max ?x ?y ] |- _ => om x y; omega_max
      | _ => intros; try omega
    end.

  Inductive avl : tree -> Prop :=
    | RBLeaf : avl Leaf
    | RBNode :
        forall (x : elt) (l r : tree) (h : Z),
        avl l ->
        avl r ->
        -2 <= height l - height r <= 2 ->
        h = max (height l) (height r) +1 -> 
        avl (Node l x r h).

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

  Lemma avl_node :
   forall (x : elt) (l r : tree),
   avl l ->
   avl r ->
   -2 <= height l - height r <= 2 ->
   avl (Node l x r (max (height l) (height r) + 1)).
  Proof.
    intros; auto.
  Qed.
  Hint Resolve avl_node.

  (** The tactics *)

  Lemma height_non_negative : forall s : tree, avl s -> height s >= 0.
  Proof.
    simple induction s; simpl in |- *; intros.
    omega.
    inversion_clear H1; intuition.
    omega_max.
  Qed.

  Implicit Arguments height_non_negative. 

  Ltac avl_nn_hyp h := 
     let nz := fresh "nz" in assert (nz := height_non_negative h).

  Ltac avl_nn h := 
    match type of h with 
     | Prop => avl_nn_hyp h
     | _ => match goal with H : avl h |- _ => avl_nn_hyp H end
   end.

  Ltac avl_inv :=
    match goal with 
       | H:avl Leaf |- _ => clear H; avl_inv
       | H:avl (Node _ _ _ _) |- _ => inversion_clear H; avl_inv
       | _ => idtac
     end.

  Ltac bst_inv :=
    match goal with 
       | H:bst Leaf |- _ => clear H; bst_inv
       | H:bst (Node _ _ _ _) |- _ => inversion_clear H; bst_inv
       | _ => idtac
     end.

  Notation t := tree.

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Add (x : elt) (s s' : t) :=
    forall y : elt, In y s' <-> X.eq y x \/ In y s.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) (s : t) :=
    forall x : elt, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s : t) :=
    exists x : elt, In x s /\ P x.

  (** * Empty set *)

  Definition empty := Leaf.

  Lemma empty_bst : bst empty.
  Proof.
  auto.
  Qed.

  Lemma empty_avl : avl empty.
  Proof. 
  auto.
  Qed.

  Lemma empty_1 : Empty empty.
  Proof.
  intro; intro.
  inversion H.
  Qed.

  (** * Emptyness test *)

  Definition is_empty (s:t) := match s with Leaf => true | _ => false end.

  Lemma is_empty_1 : forall s, Empty s -> is_empty s = true. 
  Proof.
  destruct s; simpl; auto.
  intros.
  elim (H t); auto.
  Qed.

  Lemma is_empty_2 : forall s, is_empty s = true -> Empty s.
  Proof. 
  destruct s; simpl; intros; try discriminate.
  red; auto.
  Qed.

  (** * Appartness *)

  (** The [mem] function is deciding appartness. It exploits the [bst] property
      to achieve logarithmic complexity. *)

  Fixpoint mem (x:elt)(s:t) { struct s } : bool := 
     match s with 
       |  Leaf => false 
       |  Node l y r _ => match X.compare x y with 
               | Lt _ => mem x l 
               | Eq _ => true
               | Gt _ => mem x r
           end
     end.

  Lemma mem_1 : forall s (Hs1:bst s)(Hs2:avl s) x,  In x s -> mem x s = true.
  Proof. 
  intros s Hs1 Hs2 x; generalize Hs1; clear Hs1 Hs2.
  functional induction mem x s; auto; inversion_clear 1.
  inversion_clear 1.
  inversion_clear 1; auto; absurd (X.lt x y); eauto.
  inversion_clear 1; auto; absurd (X.lt y x); eauto.
  Qed.

  Lemma mem_2 : forall s x, mem x s = true -> In x s. 
  Proof. 
  intros s x. 
  functional induction mem x s; auto; intros; try discriminate.
  Qed.

  (** * Singleton set *)

  Definition singleton (x : elt) := Node Leaf x Leaf 1.

  Lemma singleton_bst : forall x : elt, bst (singleton x).
  Proof.
  unfold singleton;  auto.
  Qed.

  Lemma singleton_avl : forall x : elt, avl (singleton x).
  Proof.
    unfold singleton; intro.
    constructor; auto; try red; simpl; try omega.
  Qed.

  Lemma singleton_1 : forall x y, In y (singleton x) -> X.eq x y. 
  Proof. 
  unfold singleton; inversion_clear 1; auto; inversion_clear H0.
  Qed.

  Lemma singleton_2 : forall x y, X.eq x y -> In y (singleton x). 
  Proof. 
  unfold singleton; auto.
  Qed.

  (** * Helper functions *)

  (** [create l x r] creates a node, assuming [l] and [r]
      to be balanced and [|height l - height r| <= 2]. *)

  Definition create l x r := 
     Node l x r (max (height l) (height r) + 1).

  Lemma create_bst : 
     forall l x r, bst l -> bst r -> lt_tree x l -> gt_tree x r -> bst (create l x r).
  Proof.
  unfold create; auto.
  Qed.
  Hint Resolve create_bst.

  Lemma create_avl : 
    forall l x r, avl l -> avl r ->  -2 <= height l - height r <= 2 -> avl (create l x r).
  Proof.
  unfold create; auto.
  Qed.

  Lemma create_height : 
    forall l x r, avl l -> avl r ->  -2 <= height l - height r <= 2 -> 
    height (create l x r) = max (height l) (height r) +1.
  Proof.
  unfold create; intros; auto.
  Qed.

  Lemma create_in : 
    forall l x r y,  In y (create l x r) <-> X.eq y x \/ In y l \/ In y r.
  Proof.
  unfold create; split; [ inversion_clear 1 | ]; intuition.
  Qed.

  (** trick for emulating [assert false] in Coq *)

  Definition assert_false := Leaf.

  (** [bal l x r] acts as [create], but performs one step of
      rebalancing if necessary, i.e. assumes [|height l - height r| <= 3]. *)

  Definition bal l x r := 
    let hl := height l in 
    let hr := height r in
    if Z_gt_le_dec hl (hr+2) then 
        match l with 
          | Leaf => assert_false
          | Node t0 t1 t2 z0 => 
               if  Z_ge_lt_dec (height t0) (height t2) then 
                    create t0 t1 (create t2 x r)
               else 
                    match t2 with 
                      | Leaf => assert_false 
                      | Node t3 t4 t5 z2 => create (create t0 t1 t3) t4 (create t5 x r)
                    end
       end
   else 
      if Z_gt_le_dec hr (hl+2) then 
          match r with
            | Leaf => assert_false
            | Node t0 t1 t2 z1 =>
                  if Z_ge_lt_dec (height t2) (height t0) then 
                      create (create l x t0) t1 t2
                  else 
                      match t0 with
                         | Leaf => assert_false
                         | Node t3 t4 t5 z3 => create (create l x t3) t4 (create t5 t1 t2) 
                      end
         end
      else 
         create l x r. 

  Ltac create_bst :=  
    bst_inv; 
    match goal with
     | |- (bst (create _ _ _)) => apply create_bst; auto; create_bst
     | |- (lt_tree _ (create _ _ _)) => 
         unfold create; apply lt_tree_node; auto; try solve [eapply lt_tree_trans; eauto]
     | |- (gt_tree _ (create _ _ _)) => 
         unfold create; apply gt_tree_node; auto; try solve [eapply gt_tree_trans; eauto]
     | |- _ => idtac
    end; eauto.

  Lemma bal_bst : forall l x r,
     bst l -> bst r -> lt_tree x l -> gt_tree x r -> bst (bal l x r).
  Proof.
  (*admit.*)
  intros l x r.
  (* functional induction bal l x r. MARCHE PAS !*) 
  intros; 
  unfold bal; 
  destruct (Z_gt_le_dec (height l) (height r + 2)); 
    [ destruct l; 
       [ | destruct (Z_ge_lt_dec (height l1) (height l2)); 
            [ | destruct l2 ]]
    | destruct (Z_gt_le_dec (height r) (height l + 2)); 
       [ destruct r;
            [ | destruct (Z_ge_lt_dec (height r2) (height r1)); 
                 [ | destruct r1 ]]
       | ]]; 
  create_bst.
  Qed.

  Ltac create_avl :=  
    avl_inv; simpl in *;
    match goal with
     | |- (avl (create _ _ _)) => apply create_avl; auto; simpl in *; create_avl
     | _ => try omega_max; trivial
    end.

  Lemma bal_avl : forall l x r, avl l -> avl r -> -3 <= height l - height r <= 3 ->
    avl (bal l x r).
  Proof.
  (*admit.*)
  intros;
  unfold bal; 
  destruct (Z_gt_le_dec (height l) (height r + 2)); 
    [ destruct l; 
       [ | destruct (Z_ge_lt_dec (height l1) (height l2)); 
            [ | destruct l2 ]]
    | destruct (Z_gt_le_dec (height r) (height l + 2)); 
       [ destruct r;
            [ | destruct (Z_ge_lt_dec (height r2) (height r1)); 
                 [ | destruct r1 ]]
       | ]]; 
  create_avl.
  Qed.

  Lemma bal_height_1 : forall l x r, avl l -> avl r -> -3 <= height l - height r <= 3 ->
     0<= height (bal l x r) - max (height l) (height r) <= 1.
  Proof.
  (*admit.*)
  intros;
  unfold bal; 
  destruct (Z_gt_le_dec (height l) (height r + 2)); 
    [ destruct l; 
       [ | destruct (Z_ge_lt_dec (height l1) (height l2)); 
            [ | destruct l2 ]]
    | destruct (Z_gt_le_dec (height r) (height l + 2)); 
       [ destruct r;
            [ | destruct (Z_ge_lt_dec (height r2) (height r1)); 
                 [ | destruct r1 ]]
       | ]]; 
  avl_inv; simpl in *; try omega_max.
  avl_nn l1; omega.
  avl_nn r2; omega.
  Qed.

  Lemma bal_height_2 : forall l x r, avl l -> avl r -> -2 <= height l - height r <= 2 -> 
     height (bal l x r) = max (height l) (height r) +1.
  Proof.
  (*admit.*)
  intros;
  unfold bal; 
  destruct (Z_gt_le_dec (height l) (height r + 2)); 
    [ destruct l; 
       [ | destruct (Z_ge_lt_dec (height l1) (height l2)); 
            [ | destruct l2 ]]
    | destruct (Z_gt_le_dec (height r) (height l + 2)); 
       [ destruct r;
            [ | destruct (Z_ge_lt_dec (height r2) (height r1)); 
                 [ | destruct r1 ]]
       | ]]; 
  avl_inv; simpl in *; try omega_max.
  Qed.

  Lemma bal_in : forall l x r y, avl l -> avl r -> 
     (In y (bal l x r) <-> X.eq y x \/ In y l \/ In y r).
  Proof.
  (*admit.*)
  intros;
  unfold bal; 
  destruct (Z_gt_le_dec (height l) (height r + 2)); 
    [ destruct l; 
       [ | destruct (Z_ge_lt_dec (height l1) (height l2)); 
            [ | destruct l2 ]]
    | destruct (Z_gt_le_dec (height r) (height l + 2)); 
       [ destruct r;
            [ | destruct (Z_ge_lt_dec (height r2) (height r1)); 
                 [ | destruct r1 ]]
       | ]]; 
  avl_inv; simpl in *.
  avl_nn r; elimtype False; omega.
  do 2 rewrite create_in; intuition.
    inversion_clear H3; auto.
  avl_nn l1; elimtype False; omega.
  do 3 rewrite create_in; intuition.
    inversion_clear H6; auto.
    inversion_clear H10; auto.
  avl_nn l; elimtype False; omega.
  do 2 rewrite create_in; intuition.
    inversion_clear H3; auto.
  avl_nn r2; elimtype False; omega.
  do 3 rewrite create_in; intuition.
    inversion_clear H6; auto.
    inversion_clear H10; auto.
  rewrite create_in; intuition.
  Qed.

  (** * Insertion *)

  Fixpoint add (x:elt)(s:t) { struct s } : t := match s with 
     | Leaf => Node Leaf x Leaf 1
     | Node l y r h => 
        match X.compare x y with
           | Lt _ => bal (add x l) y r
           | Eq _ => Node l y r h
           | Gt _ => bal l y (add x r)
        end
    end.

  Lemma add_avl_1 : forall s x, avl s -> 
     avl (add x s) /\ 0 <= height (add x s) - height s <= 1.
  Proof. 
  (*admit.*)
  intros s x; functional induction add x s; intros; avl_inv; simpl in *; 
    try solve [intuition].
  (* Lt *)
  destruct H; auto.
  split.
  apply bal_avl; auto; omega.
  generalize (bal_height_1 (add x l) y r H H2).
  generalize (bal_height_2 (add x l) y r H H2).
  omega_max.
  (* Gt *)
  destruct H; auto.
  split.
  apply bal_avl; auto; omega.
  generalize (bal_height_1 l y (add x r) H1 H).
  generalize (bal_height_2 l y (add x r) H1 H).
  omega_max.
  Qed.

  Lemma add_avl : forall s x, avl s -> avl (add x s).
  Proof.
  intros; generalize (add_avl_1 s x H); intuition.
  Qed.
  Hint Resolve add_avl.

  Lemma add_in : forall s x y, avl s -> 
      (In y (add x s) <-> X.eq y x \/ In y s).
  Proof.
  (*admit.*)
  intros s x; functional induction add x s; auto; intros.
  intuition.
  inversion_clear H0; auto.
  (* Lt *)
  avl_inv.
  rewrite bal_in; auto.
  rewrite (H y0 H1).
  intuition.
  inversion_clear H6; intuition.
  (* Eq *)  
  avl_inv.
  intuition.
  eapply In_1; eauto.
  (* Gt *)
  avl_inv.
  rewrite bal_in; auto.
  rewrite (H y0 H2).
  intuition.
  inversion_clear H6; intuition.
  Qed.

  Lemma add_bst : forall s x, bst s -> avl s -> bst (add x s).
  Proof. 
  (*admit.*)
  intros s x; functional induction add x s; auto; intros.
  bst_inv; avl_inv; apply bal_bst; auto.
  (* lt_tree -> lt_tree (add ...) *)
  red; red in H4.
  intros.
  rewrite (add_in l x y0 H0) in H1.
  intuition.
  eauto.
  bst_inv; avl_inv; apply bal_bst; auto.
  (* gt_tree -> gt_tree (add ...) *)
  red; red in H4.
  intros.
  rewrite (add_in r x y0 H6) in H1.
  intuition.
  apply ME.lt_eq with x; auto.
  Qed.

  (** * Join

      Same as [bal] but does not assume anything regarding heights
      of [l] and [r].
  *)

  Fixpoint join (l:t) : elt -> t -> t :=
    match l with
      | Leaf => add
      | Node ll lx lr lh => fun x => 
         fix join_aux (r:t) : t := match r with 
            | Leaf =>  add x l
            | Node rl rx rr rh =>  
                 if Z_gt_le_dec lh (rh+2) then bal ll lx (join lr x r)
                 else if Z_gt_le_dec rh (lh+2) then bal (join_aux rl) rx rr 
                 else create l x r
            end
    end.

  Lemma join_avl_1 : forall l x r, avl l -> avl r -> avl (join l x r) /\
     0<= height (join l x r) - max (height l) (height r) <= 1.
  Proof. 
  (*admit.*)
  (* intros l x r; functional induction join l x r. AUTRE PROBLEME! *)
  induction l as [| ll _ lx lr Hlr lh]; 
    [ | induction r as [| rl Hrl rx rr _ rh]; unfold join;
        [ | destruct (Z_gt_le_dec lh (rh+2)); 
             [ | destruct (Z_gt_le_dec rh (lh+2)) ]]]; intros.
   split; simpl; auto. 
   destruct (add_avl_1 r x H0).
   avl_nn r; omega_max.
   split; auto.
   set (l:=Node ll lx lr lh) in *.
   destruct (add_avl_1 l x H).
   simpl (height Leaf).
   avl_nn l; omega_max.

   match goal with |- context b [ bal ?a ?b ?c] => 
      replace (bal a b c) with (bal ll lx (join lr x (Node rl rx rr rh))); auto end.
   inversion_clear H.
   assert (height (Node rl rx rr rh) = rh); auto.
   set (r := Node rl rx rr rh) in *; clearbody r.
   destruct (Hlr x r H2 H0); clear Hrl Hlr.
   set (j := join lr x r) in *; clearbody j.
   simpl.
   assert (-3 <= height ll - height j <= 3) by omega_max.
   split.
   apply bal_avl; auto.
   generalize (bal_height_1 ll lx j H1 H5 H7).
   generalize (bal_height_2 ll lx j H1 H5).
   omega_max.

   match goal with |- context b [ bal ?a ?b ?c] => 
      replace (bal a b c) with (bal (join (Node ll lx lr lh) x rl) rx rr); auto end.
   inversion_clear H0.
   assert (height (Node ll lx lr lh) = lh); auto.
   set (l := Node ll lx lr lh) in *; clearbody l.
   destruct (Hrl H H1); clear Hrl Hlr.
   set (j := join l x rl) in *; clearbody j.
   simpl.
   assert (-3 <= height j - height rr <= 3) by omega_max.
   split.
   apply bal_avl; auto.
   generalize (bal_height_1 j rx rr H5 H2 H7).
   generalize (bal_height_2 j rx rr H5 H2).
   omega_max.

   clear Hrl Hlr.
   assert (height (Node ll lx lr lh) = lh); auto.
   assert (height (Node rl rx rr rh) = rh); auto.
   set (l := Node ll lx lr lh) in *; clearbody l.
   set (r := Node rl rx rr rh) in *; clearbody r.
   assert (-2 <= height l - height r <= 2) by omega.
   split.
   apply create_avl; auto.
   rewrite create_height; auto; omega.
   Qed.

  Lemma join_avl : forall l x r, avl l -> avl r -> avl (join l x r).
  Proof.
  intros; generalize (join_avl_1 l x r H H0); intuition.
  Qed.

  Lemma join_in : forall l x r y, avl l -> avl r -> 
       (In y (join l x r) <-> X.eq y x \/ In y l \/ In y r).
  Proof.
  (*admit.*)
  induction l as [| ll _ lx lr Hlr lh]; 
    [ | induction r as [| rl Hrl rx rr _ rh]; unfold join;
        [ | destruct (Z_gt_le_dec lh (rh+2)); 
             [ | destruct (Z_gt_le_dec rh (lh+2)) ]]]; intros.
   simpl.
   rewrite add_in; auto.
   intuition.
   inversion H1.

   rewrite add_in; auto.
   intuition.
   inversion H1.

   match goal with |- context b [ bal ?a ?b ?c] => 
      replace (bal a b c) with (bal ll lx (join lr x (Node rl rx rr rh))); auto end.
   avl_inv.
   rewrite bal_in; auto.
   apply join_avl; auto.
   rewrite Hlr; clear Hlr Hrl; auto.
   intuition.
   inversion_clear H6; auto.

   match goal with |- context b [ bal ?a ?b ?c] => 
      replace (bal a b c) with (bal (join (Node ll lx lr lh) x rl) rx rr); auto end.
   avl_inv.
   rewrite bal_in; auto.
   apply join_avl; auto.
   rewrite Hrl; clear Hlr Hrl; auto.
   intuition.
   inversion_clear H6; auto.

   apply create_in.
   Qed.

  Lemma join_bst : 
    forall l x r, bst l -> avl l -> bst r -> avl r -> lt_tree x l -> gt_tree x r -> bst (join l x r).
  Proof.
  (*admit.*)
    induction l as [| ll _ lx lr Hlr lh]; 
    [ | induction r as [| rl Hrl rx rr _ rh]; unfold join;
        [ | destruct (Z_gt_le_dec lh (rh+2)); 
             [ | destruct (Z_gt_le_dec rh (lh+2)) ]]]; intros.
   simpl.
   apply add_bst; auto.
   apply add_bst; auto.

   match goal with |- context b [ bal ?a ?b ?c] => 
      replace (bal a b c) with (bal ll lx (join lr x (Node rl rx rr rh))); auto end.
   bst_inv.
   (*ast_inv*) generalize H0 H2; inversion_clear H0; inversion_clear H2; intros.
   apply bal_bst; auto.
   clear Hrl Hlr H13 H14 H16 H17 z; intro; intros.
   set (r:=Node rl rx rr rh) in *; clearbody r.
   rewrite (join_in lr x r y H12 H18) in H13.
   intuition.
   apply ME.lt_eq with x; eauto.
   eauto.

   match goal with |- context b [ bal ?a ?b ?c] => 
      replace (bal a b c) with (bal (join (Node ll lx lr lh) x rl) rx rr); auto end.
   bst_inv.
   (*ast_inv*) generalize H0 H2; inversion_clear H0; inversion_clear H2; intros.
   apply bal_bst; auto.
   clear Hrl Hlr H13 H14 H16 H17 z; intro; intros.
   set (l:=Node ll lx lr lh) in *; clearbody l.
   rewrite (join_in l x rl y H2 H0) in H13.
   intuition.
   apply ME.eq_lt with x; eauto.
   eauto.

   apply create_bst; auto.
   Qed.

  (** * Extraction of minimum element *)

   (* morally, [remove_min] is to be applied to a non-empty tree 
       [t = Node l x r h]. Since we can't deal here with [assert false] 
       for [t=Leaf], we pre-unpack [t] (and forget about [h]) *)
 
   Fixpoint remove_min (l:t)(x:elt)(r:t) { struct l } : t*elt := 
     match l with 
       | Leaf => (r,x)
       | Node ll lx lr lh => let (l',m) := remove_min ll lx lr in (bal l' x r, m)
     end.

  Lemma remove_min_avl_1 : forall l x r h, avl (Node l x r h) -> 
      avl (fst (remove_min l x r)) /\ 
      0 <= height (Node l x r h) - height (fst (remove_min l x r)) <= 1.
  Proof.
  (*admit.*)
  intros l x r; functional induction remove_min l x r; simpl in *; intros.
  avl_inv; simpl in *; split; auto.
  avl_nn r; omega_max.
  (* l = Node *)
  inversion_clear H0.
  destruct (H lh); auto.
  split. 
  apply bal_avl; auto.
  simpl in *; omega_max.
  simpl in *.
  generalize (bal_height_1 l' x r H0 H2).
  generalize (bal_height_2 l' x r H0 H2).
  omega_max.
  Qed.

  Lemma remove_min_avl : forall l x r h, avl (Node l x r h) -> 
      avl (fst (remove_min l x r)). 
  Proof.
  intros; generalize (remove_min_avl_1 l x r h H); intuition.
  Qed.

  Lemma remove_min_in : forall l x r h y, avl (Node l x r h) -> 
       (In y (Node l x r h) <-> 
        X.eq y (snd (remove_min l x r)) \/ In y (fst (remove_min l x r))).
  Proof.
  (*admit.*)
  intros l x r; functional induction remove_min l x r; simpl in *; intros.
  intuition.
  inversion_clear H0; auto.
  inversion_clear H1.
  (* l = Node *)
  inversion_clear H0.
  generalize (remove_min_avl ll lx lr lh H1).
  rewrite H_eq_0; simpl; intros.
  rewrite bal_in; auto.
  generalize (H lh y H1).
  intuition.
  inversion_clear H8; intuition.
  Qed.

  Lemma remove_min_bst : forall l x r h, bst (Node l x r h) -> avl (Node l x r h) ->
      bst (fst (remove_min l x r)).
  Proof.
  (*admit.*)
  intros l x r; functional induction remove_min l x r; simpl in *; intros.
  bst_inv; auto.
  inversion_clear H0; inversion_clear H1.
  apply bal_bst; auto.
  firstorder.
  intro; intros.
  generalize (remove_min_in ll lx lr lh y H0).
  rewrite H_eq_0; simpl.
  destruct 1.
  apply H4; intuition.
  Qed.
  
  Lemma remove_min_gt_tree : forall l x r h, bst (Node l x r h) ->  avl (Node l x r h) -> 
      gt_tree (snd (remove_min l x r)) (fst (remove_min l x r)).
  Proof.
  (*admit.*)
  intros l x r; functional induction remove_min l x r; simpl in *; intros.
  bst_inv; auto.
  inversion_clear H0; inversion_clear H1.
  intro; intro.
  generalize (H lh H2 H0); clear H8 H7 H.
  generalize (remove_min_avl ll lx lr lh H0).
  generalize (remove_min_in ll lx lr lh m H0).
  rewrite H_eq_0; simpl; intros.
  rewrite (bal_in l' x r y H7 H6) in H1.
  destruct H.
  firstorder.
  apply ME.lt_eq with x; auto.
  apply E.lt_trans with x.
  apply H4; auto.
  apply H5; auto.
  Qed.

  (** * Merging two trees

    [merge t1 t2] builds the union of [t1] and [t2] assuming all elements
    of [t1] to be smaller than all elements of [t2], and
    [|height t1 - height t2| <= 2].
  *)

  Definition merge s1 s2 :=  match s1,s2 with 
    | Leaf, _ => s2 
    | _, Leaf => s1
    | _, Node l2 x2 r2 h2 => 
          let (s2',m) := remove_min l2 x2 r2 in bal s1 m s2'
  end.

  Lemma merge_avl_1 : forall s1 s2, avl s1 -> avl s2 -> 
    -2 <= height s1 - height s2 <= 2 -> 
    avl (merge s1 s2) /\ 
    0<= height (merge s1 s2) - max (height s1) (height s2) <=1.
  Proof.
  (*admit.*) 
  intros s1 s2; functional induction merge s1 s2; simpl in *; intros.
  split; auto.
  avl_nn s2; omega_max.
  split; auto.
  avl_nn_hyp H. (* pourquoi pas avl_nn ? *)
  simpl in *; omega_max.
  generalize (remove_min_avl_1 l2 x2 r2 h2 H0).
  rewrite H_eq_1; simpl; destruct 1.
  split.
  apply bal_avl; auto.
  simpl; omega_max.
  generalize (bal_height_1 (Node t t0 t1 z) m s2' H H2).
  generalize (bal_height_2 (Node t t0 t1 z) m s2' H H2).
  simpl in *; omega_max.
  Qed.
  
  Lemma merge_avl : forall s1 s2, avl s1 -> avl s2 -> 
    -2 <= height s1 - height s2 <= 2 -> avl (merge s1 s2).
  Proof. 
  intros; generalize (merge_avl_1 s1 s2 H H0 H1); intuition.
  Qed.

  Lemma merge_in : forall s1 s2 y, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
    (In y (merge s1 s2) <-> In y s1 \/ In y s2).
  Proof. 
  (*admit.*) 
  intros s1 s2; functional induction merge s1 s2; simpl in *; intros.
  intuition.
  inversion_clear H4.
  intuition.
  inversion_clear H4.
  rewrite bal_in; auto.
  generalize (remove_min_avl l2 x2 r2 h2 H2); rewrite H_eq_1; simpl; auto.
  generalize (remove_min_in l2 x2 r2 h2 y H2); rewrite H_eq_1; simpl; intro.
  rewrite H3.
  intuition.
  Qed.

  Lemma merge_bst : forall s1 s2, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
    (forall y1 y2 : elt, In y1 s1 -> In y2 s2 -> X.lt y1 y2) -> 
    bst (merge s1 s2). 
  Proof.
  (*admit.*) 
  intros s1 s2; functional induction merge s1 s2; simpl in *; intros; auto.
  apply bal_bst; auto.
  generalize (remove_min_bst l2 x2 r2 h2 H1 H2); rewrite H_eq_1; simpl in *; auto.
  intro; intro.
  apply H3; auto.
  generalize (remove_min_in l2 x2 r2 h2 m H2); rewrite H_eq_1; simpl; intuition.
  generalize (remove_min_gt_tree l2 x2 r2 h2 H1 H2); rewrite H_eq_1; simpl; auto.
  Qed. 

  (** * Deletion *)

  Fixpoint remove (x:elt)(s:tree) { struct s } : t := match s with 
    | Leaf => Leaf
    | Node l y r h =>
        match X.compare x y with
           | Lt _ => bal (remove x l) y r
           | Eq _ => merge l r
           | Gt _ => bal l  y (remove x r)
        end
     end.

  Lemma remove_avl_1 : forall s x, avl s -> 
         avl (remove x s) /\ 
         0 <= height s - height (remove x s) <= 1.
  Proof.
  (*admit.*) 
  intros s x; functional induction remove x s; simpl; intros.
  intuition.
  (* Lt *)
  avl_inv.
  destruct (H H1).
  split. 
  apply bal_avl; auto.
  omega_max.
  generalize (bal_height_1 (remove x l) y r H0 H2).
  generalize (bal_height_2 (remove x l) y r H0 H2).
  omega_max.
  (* Eq *)
  avl_inv. 
  generalize (merge_avl_1 l r H0 H1 H2).
  intuition omega_max.
  (* Gt *)
  avl_inv.
  destruct (H H2).
  split. 
  apply bal_avl; auto.
  omega_max.
  generalize (bal_height_1 l y (remove x r) H1 H0).
  generalize (bal_height_2 l y (remove x r) H1 H0).
  omega_max.
  Qed.

  Lemma remove_avl : forall s x, avl s -> avl (remove x s).
  Proof. 
   intros; generalize (remove_avl_1 s x H); intuition.
  Qed.

  Lemma remove_in : forall s x y, bst s -> avl s -> 
     (In y (remove x s) <-> ~ X.eq y x /\ In y s).
  Proof.
  (*admit.*) 
  intros s x; functional induction remove x s; simpl; intros.
  intuition.
  inversion_clear H1.
  (* Lt *)
  avl_inv; bst_inv.
  rewrite bal_in; auto.
  apply remove_avl; auto.
  generalize (H y0 H1); intuition.
  absurd (X.eq x y); eauto.
  absurd (X.eq y0 x); eauto.
  inversion_clear H13; intuition.
  (* Eq *)
  avl_inv; bst_inv.
  rewrite merge_in; intuition.
  absurd (X.eq y0 y); eauto.
  absurd (X.eq y0 y); eauto.
  inversion_clear H10; eauto.
  elim H9; eauto.
  (* Gt *)
  avl_inv; bst_inv.
  rewrite bal_in; auto.
  apply remove_avl; auto.
  generalize (H y0 H6); intuition.
  absurd (X.eq x y); eauto.
  absurd (X.eq y0 x); eauto.
  inversion_clear H13; intuition.
  Qed.
  
  Lemma remove_bst : forall s x, bst s -> avl s -> bst (remove x s).
  Proof. 
  (*admit.*)
  intros s x; functional induction remove x s; simpl; intros.
  auto.
  (* Lt *)
  avl_inv; bst_inv.
  apply bal_bst; auto.
  intro; intro.
  rewrite (remove_in l x y0) in H0; auto.
  destruct H0; eauto.
  (* Eq *)
  avl_inv; bst_inv.
  apply merge_bst; eauto.
  (* Gt *) 
  avl_inv; bst_inv.
  apply bal_bst; auto.
  intro; intro.
  rewrite (remove_in r x y0) in H0; auto.
  destruct H0; eauto.
  Qed.

 (** * Minimum element *)

  Fixpoint min_elt (s:t) : option elt := match s with 
     | Leaf => None
     | Node Leaf y _  _ => Some y
     | Node l _ _ _ => min_elt l
  end.

  Lemma min_elt_1 : forall s x, min_elt s = Some x -> In x s. 
  Proof. 
  intro s; functional induction min_elt s; simpl.
  inversion 1.
  inversion 1; auto.
  intros.
  destruct t0; auto.
  Qed.

  Lemma min_elt_2 : forall s x y, bst s -> min_elt s = Some x -> In y s -> ~ X.lt y x. 
  Proof.
  intro s; functional induction min_elt s; simpl.
  inversion_clear 2.
  inversion_clear 1.
  inversion 1; subst.
  inversion_clear 1; auto.
  inversion_clear H5.
  inversion_clear 1.
  destruct t0.
  inversion 1; subst.
  inversion_clear 1; auto; intro.
  absurd (X.lt y0 y); eauto.
  absurd (X.lt x y0); eauto.
  inversion_clear 2; auto.
  assert (~ X.lt t1 x) by auto.
  intro; elim H5; clear H5.
  apply X.lt_trans with y; auto.
  apply ME.eq_lt with y0; auto.
  assert (~ X.lt t1 x) by auto.
  intro; elim H5; clear H5.
  generalize  (H4 _ H6); eauto.
  Qed.

  Lemma min_elt_3 : forall s, min_elt s = None -> Empty s.
  Proof.
  intro s; functional induction min_elt s; simpl.
  red; auto.
  inversion 1.
  destruct t0.
  inversion 1.
  intros H0; destruct (H H0 t1); auto.
  Qed.


  (** * Maximum element *)

  Fixpoint max_elt (s:t) : option elt := match s with 
     | Leaf => None
     | Node _ y Leaf  _ => Some y
     | Node _ _ r _ => max_elt r
  end.

  Lemma max_elt_1 : forall s x, max_elt s = Some x -> In x s. 
  Proof. 
  intro s; functional induction max_elt s; simpl.
  inversion 1.
  inversion 1; auto.
  intros.
  destruct t2; auto.
  Qed.

  Lemma max_elt_2 : forall s x y, bst s -> max_elt s = Some x -> In y s -> ~ X.lt x y. 
  Proof.
  intro s; functional induction max_elt s; simpl.
  inversion_clear 2.
  inversion_clear 1.
  inversion 1; subst.
  inversion_clear 1; auto.
  inversion_clear H5.
  inversion_clear 1.
  destruct t2.
  inversion 1; subst.
  inversion_clear 1; auto; intro.
  absurd (X.lt y y0); eauto.
  absurd (X.lt y0 x); eauto.
  inversion_clear 2; auto.
  assert (~ X.lt x t1) by auto.
  intro; elim H5; clear H5.
  apply X.lt_trans with y; auto.
  apply ME.lt_eq with y0; auto.
  assert (~ X.lt x t1) by auto.
  intro; elim H5; clear H5.
  generalize  (H3 _ H6); eauto.
  Qed.

  Lemma max_elt_3 : forall s, max_elt s = None -> Empty s.
  Proof.
  intro s; functional induction max_elt s; simpl.
  red; auto.
  inversion 1.
  destruct t2.
  inversion 1.
  intros H0; destruct (H H0 t1); auto.
  Qed.

  (** * Any element *)

  Definition choose := min_elt.

  Lemma choose_1 : forall s x, choose s = Some x -> In x s.
  Proof. 
  exact min_elt_1.
  Qed.

  Lemma choose_2 : forall s, choose s = None -> Empty s.
  Proof. 
  exact min_elt_3.
  Qed.

  (** * Concatenation

      Same as [merge] but does not assume anything about heights.
  *)

  Definition concat s1 s2 := 
     match s1, s2 with 
        | Leaf, _ => s2 
        | _, Leaf => s1
        | _, Node l2 x2 r2 h2 => 
              let (s2',m) := remove_min l2 x2 r2 in 
              join s1 m s2'
     end.

  Lemma concat_avl : forall s1 s2, avl s1 -> avl s2 -> avl (concat s1 s2).
  Proof.
  intros s1 s2; functional induction concat s1 s2; auto.
  intros; change (avl (join (Node t t0 t1 z) m s2')).
  rewrite <- H_eq_ in H; rewrite <- H_eq_.
  apply join_avl; auto.
  generalize (remove_min_avl l2 x2 r2 h2 H0); rewrite H_eq_1; simpl; auto.
  Qed.
 
  Lemma concat_bst :   forall s1 s2, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
   (forall y1 y2 : elt, In y1 s1 -> In y2 s2 -> X.lt y1 y2) -> 
   bst (concat s1 s2).
  Proof. 
  intros s1 s2; functional induction concat s1 s2; auto.
  intros; change (bst (join (Node t t0 t1 z) m s2')).
  rewrite <- H_eq_ in H; rewrite <- H_eq_ in H0; rewrite <- H_eq_ in H3; rewrite <- H_eq_.
  apply join_bst; auto.
  generalize (remove_min_bst l2 x2 r2 h2 H1 H2); rewrite H_eq_1; simpl; auto.
  generalize (remove_min_avl l2 x2 r2 h2 H2); rewrite H_eq_1; simpl; auto.
  generalize (remove_min_in l2 x2 r2 h2 m H2); rewrite H_eq_1; simpl; auto.
  destruct 1; intuition.
  generalize (remove_min_gt_tree l2 x2 r2 h2 H1 H2); rewrite H_eq_1; simpl; auto.
  Qed.

  Lemma concat_in : forall s1 s2 y, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
   (forall y1 y2 : elt, In y1 s1 -> In y2 s2 -> X.lt y1 y2) -> 
   (In y (concat s1 s2) <-> In y s1 \/ In y s2).
  Proof.
  intros s1 s2; functional induction concat s1 s2.
  intuition.
  inversion_clear H5.
  intuition.
  inversion_clear H5.
  intros. 
  change (In y (join (Node t t0 t1 z) m s2') <-> 
                In y (Node t t0 t1 z) \/ In y (Node l2 x2 r2 h2)).
  rewrite <- H_eq_ in H; rewrite <- H_eq_ in H0; rewrite <- H_eq_ in H3; rewrite <- H_eq_.
  rewrite (join_in s1 m s2' y H0).
  generalize (remove_min_avl l2 x2 r2 h2 H2); rewrite H_eq_1; simpl; auto.
  generalize (remove_min_in l2 x2 r2 h2 y H2); rewrite H_eq_1; simpl.
  intro Eq; rewrite Eq; intuition.
  Qed.

  (** * Splitting 

      [split x s] returns a triple [(l, present, r)] where
      - [l] is the set of elements of [s] that are [< x]
      - [r] is the set of elements of [s] that are [> x]
      - [present] is [true] if and only if [s] contains  [x].
  *)

  Fixpoint split (x:elt)(s:t) {struct s} : t * (bool * t) := match s with 
    | Leaf => (Leaf, (false, Leaf))
    | Node l y r h => match X.compare x y with 
        | Lt _ => let (ll, p) := split x l in let (pres, rl) := p in (ll, (pres, join rl y r))
        | Eq _ => (l, (true, r))
        | Gt _ => let (rl,p) := split x r in let (pres, rr) := p in (join l y rl, (pres, rr))
      end
   end.

  Lemma split_avl : forall s x, avl s -> 
    avl (fst (split x s)) /\ avl (snd (snd (split x s))).
  Proof. 
  intros s x; functional induction split x s.
  auto.
  destruct p; simpl in *.
  inversion_clear 1; intuition.
  apply join_avl; auto.
  simpl; inversion_clear 1; auto.
  destruct p; simpl in *.
  inversion_clear 1; intuition.
  apply join_avl; auto.
  Qed.

  Lemma split_in_1 : forall s x y, bst s -> avl s -> 
    (In y (fst (split x s)) <-> In y s /\ X.lt y x).
  Proof. 
  intros s x; functional induction split x s.
  intuition; try inversion_clear H1.
  (* Lt *)
  destruct p; simpl in *; inversion_clear 1; inversion_clear 1; clear H7 H8.
  rewrite (H y0 H1 H5); clear H.
  intuition.
  inversion_clear H0; auto.
  absurd (X.lt y x); eauto.
  apply ME.eq_lt with y0; eauto.
  absurd (X.lt y x); eauto.
  (* Eq *)
  simpl in *; inversion_clear 1; inversion_clear 1; clear H6 H7.
  intuition.
  apply ME.lt_eq with y; eauto.
  inversion_clear H6; auto.
  absurd (X.eq y0 y); eauto.
  absurd (X.lt y x); eauto.
  (* Gt *)
  destruct p; simpl in *; inversion_clear 1; inversion_clear 1; clear H7 H8.
  rewrite join_in; auto.
  generalize (split_avl r x H6); rewrite H_eq_1; simpl; intuition.
  rewrite (H y0 H2 H6); clear H.
  intuition; eauto.
  inversion_clear H0; auto.
  Qed.

  Lemma split_in_2 : forall s x y, bst s -> avl s -> 
    (In y (snd (snd (split x s))) <-> In y s /\ X.lt x y).
  Proof. 
  intros s x; functional induction split x s.
  intuition; try inversion_clear H1.
  (* Lt *)
  destruct p; simpl in *; inversion_clear 1; inversion_clear 1; clear H7 H8.
  rewrite join_in; auto.
  generalize (split_avl l x H5); rewrite H_eq_1; simpl; intuition.
  rewrite (H y0 H1 H5); clear H.
  intuition; eauto.
  apply ME.lt_eq with y; eauto.
  inversion_clear H0; auto.
  (* Eq *)
  simpl in *; inversion_clear 1; inversion_clear 1; clear H6 H7.
  intuition.
  apply ME.eq_lt with y; eauto.
  inversion_clear H6; auto.
  absurd (X.lt x y); eauto.
  absurd (X.lt x y); eauto.
  (* Gt *)
  destruct p; simpl in *; inversion_clear 1; inversion_clear 1; clear H7 H8.
  rewrite (H y0 H2 H6); clear H.
  intuition.
  inversion_clear H0; auto.
  absurd (X.lt y x); eauto.
  absurd (X.lt y x); eauto.
  Qed.

  Lemma split_in_3 : forall s x, bst s -> avl s -> 
    (fst (snd (split x s)) = true <-> In x s).
  Proof. 
  intros s x; functional induction split x s.
  intuition; try inversion_clear H1.
  (* Lt *)
  destruct p; simpl in *; inversion_clear 1; inversion_clear 1; clear H7 H8.
  rewrite H; auto.
  intuition.
  inversion_clear H; auto; absurd (X.lt x y); eauto.
  (* Eq *)
  simpl in *; inversion_clear 1; inversion_clear 1; intuition.
  (* Gt *)
  destruct p; simpl in *; inversion_clear 1; inversion_clear 1; clear H7 H8.
  rewrite H; auto.
  intuition.
  inversion_clear H; auto; absurd (X.lt y x); eauto.
  Qed.

  Lemma split_bst : forall s x, bst s -> avl s -> 
    bst (fst (split x s)) /\ bst (snd (snd (split x s))).
  Proof. 
  intros s x; functional induction split x s.
  intuition.
  (* Lt *)
  destruct p; simpl in *; inversion_clear 1; inversion_clear 1.
  intuition.
  apply join_bst; auto.
  generalize (split_avl l x H5); rewrite H_eq_1; simpl; intuition.
  intro; intro.
  generalize (split_in_2 l x y0 H1 H5); rewrite H_eq_1; simpl; intuition.
  (* Eq *)
  simpl in *; inversion_clear 1; inversion_clear 1; intuition.
  (* Gt *)
  destruct p; simpl in *; inversion_clear 1; inversion_clear 1.
  intuition.
  apply join_bst; auto.
  generalize (split_avl r x H6); rewrite H_eq_1; simpl; intuition.
  intro; intro.
  generalize (split_in_1 r x y0 H2 H6); rewrite H_eq_1; simpl; intuition.
  Qed.

  (** * Intersection *)

   Fixpoint inter (s1 s2 : t) {struct s1} : t := match s1, s2 with 
      | Leaf,_ => Leaf
      | _,Leaf => Leaf
      | Node l1 x1 r1 h1, _ => 
              match split x1 s2 with
                 | (l2',(true,r2')) => join (inter l1 l2') x1 (inter r1 r2')
                 | (l2',(false,r2')) => concat (inter l1 l2') (inter r1 r2')
              end
      end.

  Lemma inter_avl : forall s1 s2, avl s1 -> avl s2 -> avl (inter s1 s2). 
  Proof. 
  (* intros s1 s2; functional induction inter s1 s2; auto. BOF BOF *)
  induction s1 as [ | l1 Hl1 x1 r1 Hr1 h1].
  simpl; auto.
  destruct s2 as [ | l2 x2 r2 h2].
  simpl; auto.
  intros.
  simpl.
  change (avl (match split x1 (Node l2 x2 r2 h2) with
                 | (l2',(true,r2')) => join (inter l1 l2') x1 (inter r1 r2')
                 | (l2',(false,r2')) => concat (inter l1 l2') (inter r1 r2')
              end)).
  generalize H0; avl_inv.
  set (r:=Node l2 x2 r2 h2) in *; clearbody r; intros. 
  destruct (split_avl r x1 H8).
  destruct (split x1 r) as [l2' (b,r2')]; simpl in *.
  destruct b; [ apply join_avl | apply concat_avl ]; auto.
  Qed.

  Lemma inter_bst_in : forall s1 s2, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
     bst (inter s1 s2) /\ (forall y, In y (inter s1 s2) <-> In y s1 /\ In y s2).
  Proof. 
  induction s1 as [ | l1 Hl1 x1 r1 Hr1 h1].
  simpl; intuition; inversion_clear H3.
  destruct s2 as [ | l2 x2 r2 h2].
  simpl; intuition; inversion_clear H3.
  intros; simpl.
  match goal with |- context id [bst ?a] => replace a with 
               (match split x1 (Node l2 x2 r2 h2) with
                 | (l2',(true,r2')) => join (inter l1 l2') x1 (inter r1 r2')
                 | (l2',(false,r2')) => concat (inter l1 l2') (inter r1 r2')
              end); auto end.
  generalize H1 H2; avl_inv; bst_inv.
  set (r:=Node l2 x2 r2 h2) in *; clearbody r; intros.
  destruct (split_avl r x1 H17).
  destruct (split_bst r x1 H16 H17).
  split.
  (* bst *)
  destruct (split x1 r) as [l2' (b,r2')]; simpl in *.
  destruct (Hl1 l2'); auto.
  destruct (Hr1 r2'); auto.
  destruct b.
  (* bst join *)
  apply join_bst; try apply inter_avl; firstorder.
  (* bst concat *)
  apply concat_bst; try apply inter_avl; auto.
  intros; generalize (H22 y1) (H24 y2); intuition eauto.
  (* in *)
  intros.
  destruct (split_in_1 r x1 y H16 H17). 
  destruct (split_in_2 r x1 y H16 H17).
  destruct (split_in_3 r x1 H16 H17).
  destruct (split x1 r) as [l2' (b,r2')]; simpl in *.
  destruct (Hl1 l2'); auto.
  destruct (Hr1 r2'); auto.
  destruct b.
  (* in join *)
  rewrite join_in; try apply inter_avl; auto.
  rewrite H30.
  rewrite H28.
  intuition.
  apply In_1 with x1; auto.
  inversion_clear H34; intuition.
  (* in concat *)
  rewrite concat_in; try apply inter_avl; auto.
  intros.
  intros; generalize (H28 y1) (H30 y2); intuition eauto.
  rewrite H30.
  rewrite H28.
  intuition.
  inversion_clear H34; intuition.
  generalize (H26 (In_1 _ _ _ H22 H35)); intro; discriminate.
  Qed.

  Lemma inter_bst : forall s1 s2, 
     bst s1 -> avl s1 -> bst s2 -> avl s2 -> bst (inter s1 s2). 
  Proof. 
  intros; generalize (inter_bst_in s1 s2); intuition.
  Qed.

  Lemma inter_in : forall s1 s2 y, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
     (In y (inter s1 s2) <-> In y s1 /\ In y s2).
  Proof. 
  intros; generalize (inter_bst_in s1 s2); firstorder.
  Qed.

(* A SUIVRE ....
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
  Defined.

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
    {r : nat | let (l,_) := elements s in r = length l }.
  Proof.
    intros (s, s_bst, s_avl); unfold In in |- *; simpl in |- *; clear s_avl.
    exists (cardinal_tree s).
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
   (s : tree) {struct s} : A -> A := fun a => 
    match s with
    | Leaf => a
    | Node l x r _ => fold_tree A f r (f x (fold_tree A f l a))
    end.
  Implicit Arguments fold_tree [A].

  Definition fold_tree' (A : Set) (f : elt -> A -> A) 
    (s : tree) := L.fold f (elements_tree s).
  Implicit Arguments fold_tree' [A].

  Lemma fold_tree_equiv_aux :
   forall (A : Set) (s : tree) (f : elt -> A -> A) (a : A) (acc : list elt),
   L.fold f (elements_tree_aux acc s) a = 
   L.fold f acc (fold_tree f s a).
  Proof.
  simple induction s.
  simpl in |- *; intuition.
  simpl in |- *; intros.
  rewrite H.
  simpl.
  apply H0.
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
    {r : A | let (l,_) := elements s in 
                  r = fold_left (fun a e => f e a) l i}. 
  Proof.
    intros A f s i; exists (fold_tree f s i).
    rewrite fold_tree_equiv.
    unfold fold_tree' in |- *.
    assert (H:=L.fold_1 (elements_tree_sort _ (is_bst s)) i f).
    destruct s; simpl in *.
    auto.
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

*)

End Raw.





