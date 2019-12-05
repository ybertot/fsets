
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

Require Import Coq.Program.Program.
Require Import FSetInterface.
Require Import FSetList0.
Require Import ZArith.
Require Import Int.
Require Import Lia.
Require Import FunInd.

Set Firstorder Depth 3.

Set Firstorder Solver auto.
Ltac intuition ::= intuition auto.

Module Raw (I:Int)(X:OrderedType).
Import I.
Module II:=MoreInt(I).
Import II.
Open Scope Int_scope.
Local Notation int := I.t.

Ltac omega_max := i2z_refl; lia; auto with Z.

Module MX := OrderedTypeFacts X.

Definition elt := X.t.

(** * Trees *)

Inductive tree :=
  | Leaf : tree
  | Node : tree -> X.t -> tree -> int -> tree.

Notation t := tree.

(** The fourth field of [Node] is the height of the tree *)

(** A tactic to repeat [inversion_clear] on all hyps of the 
    form [(f (Node _ _ _ _))] *)
Ltac inv f :=
  match goal with 
     | H:f Leaf |- _ => inversion_clear H; inv f
     | H:f _ Leaf |- _ => inversion_clear H; inv f
     | H:f (Node _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ (Node _ _ _ _) |- _ => inversion_clear H; inv f
     | _ => idtac
  end.

(** Same, but with a backup of the original hypothesis. *)

Ltac safe_inv f := match goal with 
  | H:f (Node _ _ _ _) |- _ => 
        generalize H; inversion_clear H; safe_inv f
  | _ => intros 
 end.

(** * Occurrence in a tree *)

Inductive In (x : elt) : tree -> Prop :=
  | IsRoot :
      forall (l r : tree) (h : int) (y : elt),
      X.eq x y -> In x (Node l y r h)
  | InLeft :
      forall (l r : tree) (h : int) (y : elt),
      In x l -> In x (Node l y r h)
  | InRight :
      forall (l r : tree) (h : int) (y : elt),
      In x r -> In x (Node l y r h).

Hint Constructors In.

Ltac intuition_in := repeat progress (intuition; inv In).

(** [In] is compatible with [X.eq] *)

Lemma In_1 :
 forall s x y, X.eq x y -> In x s -> In y s.
Proof.
 induction s; simpl; intuition_in; eauto.
Qed.
Hint Immediate In_1.

(** * Binary search trees *)

(** [lt_tree x s]: all elements in [s] are smaller than [x] 
   (resp. greater for [gt_tree]) *)

Definition lt_tree (x : elt) (s : tree) := 
 forall y:elt, In y s -> X.lt y x.
Definition gt_tree (x : elt) (s : tree) := 
 forall y:elt, In y s -> X.lt x y.

Hint Unfold lt_tree gt_tree.

Ltac order := match goal with 
 | H: lt_tree ?x ?s, H1: In ?y ?s |- _ => generalize (H _ H1); clear H; order
 | H: gt_tree ?x ?s, H1: In ?y ?s |- _ => generalize (H _ H1); clear H; order
 | _ => MX.order
end.

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
 forall (x y : elt) (l r : tree) (h : int),
 lt_tree x l -> lt_tree x r -> X.lt y x -> lt_tree x (Node l y r h).
Proof.
 unfold lt_tree in *; intuition_in; order.
Qed.

Lemma gt_tree_node :
 forall (x y : elt) (l r : tree) (h : int),
 gt_tree x l -> gt_tree x r -> X.lt x y -> gt_tree x (Node l y r h).
Proof.
 unfold gt_tree in *; intuition_in; order.
Qed.

Hint Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.

Lemma lt_tree_not_in :
 forall (x : elt) (t : tree), lt_tree x t -> ~ In x t.
Proof.
 intros; intro; order.
Qed.

Lemma lt_tree_trans :
 forall x y, X.lt x y -> forall t, lt_tree x t -> lt_tree y t.
Proof.
 firstorder eauto.
Qed.

Lemma gt_tree_not_in :
 forall (x : elt) (t : tree), gt_tree x t -> ~ In x t.
Proof.
 intros; intro; order.
Qed.

Lemma gt_tree_trans :
 forall x y, X.lt y x -> forall t, gt_tree x t -> gt_tree y t.
Proof.
 firstorder eauto.
Qed.

Hint Resolve lt_tree_not_in lt_tree_trans gt_tree_not_in gt_tree_trans.

(** [bst t] : [t] is a binary search tree *)

Inductive bst : tree -> Prop :=
  | BSLeaf : bst Leaf
  | BSNode :
      forall (x : elt) (l r : tree) (h : int),
      bst l -> bst r -> lt_tree x l -> gt_tree x r -> bst (Node l x r h).

Hint Constructors bst.

(** * AVL trees *)

(** [avl s] : [s] is a properly balanced AVL tree,
    i.e. for any node the heights of the two children
    differ by at most 2 *)

Definition height (s : tree) : int :=
  match s with
  | Leaf => 0
  | Node _ _ _ h => h
  end.

Inductive avl : tree -> Prop :=
  | RBLeaf : avl Leaf
  | RBNode :
      forall (x : elt) (l r : tree) (h : int),
      avl l ->
      avl r ->
      -(2) <= height l - height r <= 2 ->
      h = max (height l) (height r) + 1 -> 
      avl (Node l x r h).

Hint Constructors avl.

(** Results about [avl] *)

Lemma avl_node :
 forall (x : elt) (l r : tree),
 avl l ->
 avl r ->
 -(2) <= height l - height r <= 2 ->
 avl (Node l x r (max (height l) (height r) + 1)).
Proof.
  intros; auto.
Qed.
Hint Resolve avl_node.

(** The tactics *)

Lemma height_non_negative : forall s : tree, avl s -> height s >= 0.
Proof.
 induction s; simpl; intros; auto with zarith.
 inv avl; intuition; omega_max.
Qed.
Arguments height_non_negative : default implicits. 

(** When [H:avl r], typing [avl_nn H] or [avl_nn r] adds [height r>=0] *)

Ltac avl_nn_hyp H := 
     let nz := fresh "nz" in assert (nz := height_non_negative H).

Ltac avl_nn h := 
  let t := type of h in 
  match type of t with 
   | Prop => avl_nn_hyp h
   | _ => match goal with H : avl h |- _ => avl_nn_hyp H end
  end.

(* Repeat the previous tactic. 
   Drawback: need to clear the [avl _] hyps ... Thank you Ltac *)

Ltac avl_nns :=
  match goal with 
     | H:avl _ |- _ => avl_nn_hyp H; clear H; avl_nns
     | _ => idtac
  end.

(** * Some shortcuts. *)

Definition Equal s s' := forall a : elt, In a s <-> In a s'.
Definition Subset s s' := forall a : elt, In a s -> In a s'.
Definition Empty s := forall a : elt, ~ In a s.
Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

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
 destruct s as [|r x l h]; simpl; auto.
 intro H; elim (H x); auto.
Qed.

Lemma is_empty_2 : forall s, is_empty s = true -> Empty s.
Proof. 
 destruct s; simpl; intros; try discriminate; red; auto.
Qed.

(** * Appartness *)

(** The [mem] function is deciding appartness. It exploits the [bst] property
    to achieve logarithmic complexity. *)

Function mem (x:elt)(s:t) { struct s } : bool := 
   match s with 
     |  Leaf => false 
     |  Node l y r _ => match X.compare x y with 
             | LT _ => mem x l 
             | EQ _ => true
             | GT _ => mem x r
         end
   end.

Lemma mem_1 : forall s x, bst s -> In x s -> mem x s = true.
Proof. 
 intros s x.
 functional induction (mem x s); inversion_clear 1; auto.
 inversion_clear 1.
 inversion_clear 1; auto; absurd (X.lt x y); eauto.
 inversion_clear 1; auto; absurd (X.lt y x); eauto.
Qed.

Lemma mem_2 : forall s x, mem x s = true -> In x s. 
Proof. 
 intros s x. 
 functional induction (mem x s); auto; intros; try discriminate.
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
 constructor; auto; try red; simpl; omega_max.
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
 forall l x r, bst l -> bst r -> lt_tree x l -> gt_tree x r -> 
 bst (create l x r).
Proof.
 unfold create; auto.
Qed.
Hint Resolve create_bst.

Lemma create_avl : 
 forall l x r, avl l -> avl r ->  -(2) <= height l - height r <= 2 -> 
 avl (create l x r).
Proof.
 unfold create; auto.
Qed.

Lemma create_height : 
 forall l x r, avl l -> avl r ->  -(2) <= height l - height r <= 2 -> 
 height (create l x r) = max (height l) (height r) + 1.
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
  if gt_le_dec hl (hr+2) then 
    match l with 
     | Leaf => assert_false
     | Node ll lx lr _ => 
       if ge_lt_dec (height ll) (height lr) then 
         create ll lx (create lr x r)
       else 
         match lr with 
          | Leaf => assert_false 
          | Node lrl lrx lrr _ => 
              create (create ll lx lrl) lrx (create lrr x r)
         end
    end
  else 
    if gt_le_dec hr (hl+2) then 
      match r with
       | Leaf => assert_false
       | Node rl rx rr _ =>
         if ge_lt_dec (height rr) (height rl) then 
            create (create l x rl) rx rr
         else 
           match rl with
            | Leaf => assert_false
            | Node rll rlx rlr _ => 
                create (create l x rll) rlx (create rlr rx rr) 
           end
      end
    else 
      create l x r. 

Ltac bal_tac := 
 intros l x r;
 unfold bal; 
 destruct (gt_le_dec (height l) (height r + 2)); 
   [ destruct l as [ |ll lx lr lh]; 
     [ | destruct (ge_lt_dec (height ll) (height lr)); 
          [ | destruct lr ] ]
   | destruct (gt_le_dec (height r) (height l + 2)); 
     [ destruct r as [ |rl rx rr rh];
          [ | destruct (ge_lt_dec (height rr) (height rl)); 
               [ | destruct rl ] ]
     | ] ]; intros.

Lemma bal_bst : forall l x r, bst l -> bst r -> 
 lt_tree x l -> gt_tree x r -> bst (bal l x r).
Proof.
 (* intros l x r; functional induction bal l x r. MARCHE PAS !*) 
 bal_tac; 
 inv bst; repeat apply create_bst; auto; unfold create; 
 apply lt_tree_node || apply gt_tree_node; auto; 
 eapply lt_tree_trans || eapply gt_tree_trans || eauto; eauto.
Qed.

Lemma bal_avl : forall l x r, avl l -> avl r -> 
 -(3) <= height l - height r <= 3 -> avl (bal l x r).
Proof.
 bal_tac; inv avl; repeat apply create_avl; simpl in *; auto; omega_max.
Qed.

Lemma bal_height_1 : forall l x r, avl l -> avl r -> 
 -(3) <= height l - height r <= 3 ->
 0 <= height (bal l x r) - max (height l) (height r) <= 1.
Proof.
 bal_tac; inv avl; avl_nns; simpl in *; omega_max.
Qed.

Lemma bal_height_2 : 
 forall l x r, avl l -> avl r -> -(2) <= height l - height r <= 2 -> 
 height (bal l x r) == max (height l) (height r) +1.
Proof.
 bal_tac; inv avl; simpl in *; omega_max.
Qed.

Lemma bal_in : forall l x r y, avl l -> avl r -> 
 (In y (bal l x r) <-> X.eq y x \/ In y l \/ In y r).
Proof.
 bal_tac; 
 solve [repeat rewrite create_in; intuition_in
       |inv avl; avl_nns; simpl in *; omega_max ].
Qed.

Ltac omega_bal := match goal with 
  | H:avl ?l, H':avl ?r |- context [ bal ?l ?x ?r ] => 
     generalize (bal_height_1 l x r H H') (bal_height_2 l x r H H'); 
     omega_max
  end. 

(** * Insertion *)

Function add (x:elt)(s:t) { struct s } : t := match s with 
   | Leaf => Node Leaf x Leaf 1
   | Node l y r h => 
      match X.compare x y with
         | LT _ => bal (add x l) y r
         | EQ _ => Node l y r h
         | GT _ => bal l y (add x r)
      end
  end.

Lemma add_avl_1 :  forall s x, avl s -> 
 avl (add x s) /\ 0 <= height (add x s) - height s <= 1.
Proof. 
 intros s x; functional induction (add x s); subst;intros; inv avl; simpl in *.
 intuition; try constructor; simpl; auto; try omega_max.
 (* LT *)
 destruct IHt; auto.
 split.
 apply bal_avl; auto; omega_max.
 omega_bal.
 (* EQ *)
 intuition; omega_max.
 (* GT *)
 destruct IHt; auto.
 split.
 apply bal_avl; auto; omega_max.
 omega_bal.
Qed.

Lemma add_avl : forall s x, avl s -> avl (add x s).
Proof.
 intros; generalize (add_avl_1 s x H); intuition.
Qed.
Hint Resolve add_avl.

Lemma add_in : forall s x y, avl s -> 
 (In y (add x s) <-> X.eq y x \/ In y s).
Proof.
 intros s x; functional induction (add x s); auto; intros.
 intuition_in.
 (* LT *)
 inv avl.
 rewrite bal_in; auto.
 rewrite (IHt y0 H0); intuition_in.
 (* EQ *)  
 inv avl.
 intuition.
 eapply In_1; eauto.
 (* GT *)
 inv avl.
 rewrite bal_in; auto.
 rewrite (IHt y0 H1); intuition_in.
Qed.

Lemma add_bst : forall s x, bst s -> avl s -> bst (add x s).
Proof. 
 intros s x; functional induction (add x s); auto; intros.
 inv bst; inv avl; apply bal_bst; auto.
 (* lt_tree -> lt_tree (add ...) *)
 red; red in H4.
 intros.
 rewrite (add_in l x y0 H) in H0.
 intuition.
 eauto.
 inv bst; inv avl; apply bal_bst; auto.
 (* gt_tree -> gt_tree (add ...) *)
 red; red in H4.
 intros.
 rewrite (add_in r x y0 H5) in H0.
 intuition.
 apply MX.lt_eq with x; auto.
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
               if gt_le_dec lh (rh+2) then bal ll lx (join lr x r)
               else if gt_le_dec rh (lh+2) then bal (join_aux rl) rx rr 
               else create l x r
          end
  end.

Ltac join_tac := 
 let l := fresh "l" in
 intro l; induction l as [| ll _ lx lr Hlr lh]; 
   [ | intros x r; induction r as [| rl Hrl rx rr _ rh]; unfold join;
     [ | destruct (gt_le_dec lh (rh+2)); 
       [ match goal with |- context b [ bal ?a ?b ?c] => 
           replace (bal a b c) 
           with (bal ll lx (join lr x (Node rl rx rr rh))); [ | auto] 
         end 
       | destruct (gt_le_dec rh (lh+2)); 
         [ match goal with |- context b [ bal ?a ?b ?c] => 
             replace (bal a b c) 
             with (bal (join (Node ll lx lr lh) x rl) rx rr); [ | auto] 
           end
         | ] ] ] ]; intros.

Lemma join_avl_1 : forall l x r, avl l -> avl r -> avl (join l x r) /\
 0<= height (join l x r) - max (height l) (height r) <= 1.
Proof. 
 (* intros l x r; functional induction join l x r. AUTRE PROBLEME! *)
 join_tac.

 split; simpl; auto. 
 destruct (add_avl_1 r x H0).
 avl_nns; omega_max.
 split; auto.
 set (l:=Node ll lx lr lh) in *.
 destruct (add_avl_1 l x H).
 simpl (height Leaf).
 avl_nns; omega_max.

 inversion_clear H.
 assert (height (Node rl rx rr rh) = rh); auto.
 set (r := Node rl rx rr rh) in *; clearbody r.
 destruct (Hlr x r H2 H0); clear Hrl Hlr.
 set (j := join lr x r) in *; clearbody j.
 simpl.
 assert (-(3) <= height ll - height j <= 3) by omega_max.
 split.
 apply bal_avl; auto.
 omega_bal.

 inversion_clear H0.
 assert (height (Node ll lx lr lh) = lh); auto.
 set (l' := Node ll lx lr lh) in *; clearbody l'.
 destruct (Hrl H H1); clear Hrl Hlr.
 set (j := join l' x rl) in *; clearbody j.
 simpl.
 assert (-(3) <= height j - height rr <= 3) by omega_max.
 split.
 apply bal_avl; auto.
 omega_bal.

 clear Hrl Hlr.
 assert (height (Node ll lx lr lh) = lh); auto.
 assert (height (Node rl rx rr rh) = rh); auto.
 set (l' := Node ll lx lr lh) in *; clearbody l'.
 set (r := Node rl rx rr rh) in *; clearbody r.
 assert (-(2) <= height l' - height r <= 2) by omega_max.
 split.
 apply create_avl; auto.
 rewrite create_height; auto; omega_max.
Qed.

Lemma join_avl : forall l x r, avl l -> avl r -> avl (join l x r).
Proof.
 intros; generalize (join_avl_1 l x r H H0); intuition.
Qed.
Hint Resolve join_avl.

Lemma join_in : forall l x r y, avl l -> avl r -> 
     (In y (join l x r) <-> X.eq y x \/ In y l \/ In y r).
Proof.
 join_tac.
 simpl.
 rewrite add_in; intuition_in.

 rewrite add_in; intuition_in.

 inv avl.
 rewrite bal_in; auto.
 rewrite Hlr; clear Hlr Hrl; intuition_in.

 inv avl.
 rewrite bal_in; auto.
 rewrite Hrl; clear Hlr Hrl; intuition_in.

 apply create_in.
Qed.

Lemma join_bst : forall l x r, bst l -> avl l -> bst r -> avl r -> 
 lt_tree x l -> gt_tree x r -> bst (join l x r).
Proof.
 join_tac.
 apply add_bst; auto.
 apply add_bst; auto.

 inv bst; safe_inv avl.
 apply bal_bst; auto.
 clear Hrl Hlr H13 H14 H16 H17; intro; intros.
 set (r:=Node rl rx rr rh) in *; clearbody r.
 rewrite (join_in lr x r y) in H13; auto.
 intuition.
 apply MX.lt_eq with x; eauto.
 eauto.

 inv bst; safe_inv avl.
 apply bal_bst; auto.
 clear Hrl Hlr H13 H14 H16 H17; intro; intros.
 set (l':=Node ll lx lr lh) in *; clearbody l'.
 rewrite (join_in l' x rl y) in H13; auto.
 intuition.
 apply MX.eq_lt with x; eauto.
 eauto.

 apply create_bst; auto.
Qed.

(** * Extraction of minimum element

  morally, [remove_min] is to be applied to a non-empty tree 
  [t = Node l x r h]. Since we can't deal here with [assert false] 
  for [t=Leaf], we pre-unpack [t] (and forget about [h]). 
*)
 
Function remove_min (l:t)(x:elt)(r:t) { struct l } : t*elt := 
  match l with 
    | Leaf => (r,x)
    | Node ll lx lr lh => let (l',m) := (remove_min ll lx lr : t*elt) in (bal l' x r, m)
  end.

Lemma remove_min_avl_1 : forall l x r h, avl (Node l x r h) -> 
 avl (fst (remove_min l x r)) /\ 
 0 <= height (Node l x r h) - height (fst (remove_min l x r)) <= 1.
Proof.
 intros l x r; functional induction (remove_min l x r); subst;simpl in *; intros.
 inv avl; simpl in *; split; auto.
 avl_nns; omega_max.
 (* l = Node *)
 inversion_clear H.
 rewrite e0 in IHp;simpl in IHp;destruct (IHp lh); auto.
 split; simpl in *. 
 apply bal_avl; auto; omega_max.
 omega_bal.
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
 intros l x r; functional induction (remove_min l x r); simpl in *; intros.
 intuition_in.
 (* l = Node *)
 inversion_clear H.
 generalize (remove_min_avl ll lx lr lh H0).
 rewrite e0; simpl; intros.
 rewrite bal_in; auto.
 rewrite e0 in IHp;generalize (IHp lh y H0).
 intuition.
 inversion_clear H7; intuition.
Qed.

Lemma remove_min_bst : forall l x r h, 
 bst (Node l x r h) -> avl (Node l x r h) -> bst (fst (remove_min l x r)).
Proof.
 intros l x r; functional induction (remove_min l x r); subst;simpl in *; intros.
 inv bst; auto.
 inversion_clear H; inversion_clear H0.
 rewrite_all e0;simpl in *.
 apply bal_bst; auto.
 firstorder.
 intro; intros.
 generalize (remove_min_in ll lx lr lh y H).
 rewrite e0; simpl.
 destruct 1.
 apply H3; intuition.
Qed.

Lemma remove_min_gt_tree : forall l x r h, 
 bst (Node l x r h) -> avl (Node l x r h) -> 
 gt_tree (snd (remove_min l x r)) (fst (remove_min l x r)).
Proof.
 intros l x r; functional induction (remove_min l x r); subst;simpl in *; intros.
 inv bst; auto.
 inversion_clear H; inversion_clear H0.
 intro; intro.
 generalize (IHp lh H1 H); clear H6 H7 IHp.
 generalize (remove_min_avl ll lx lr lh H).
 generalize (remove_min_in ll lx lr lh m H).
 rewrite e0; simpl; intros.
 rewrite (bal_in l' x r y H7 H5) in H0.
 destruct H6.
 firstorder.
 apply MX.lt_eq with x; auto.
 apply X.lt_trans with x; auto.
Qed.

(** * Merging two trees

  [merge t1 t2] builds the union of [t1] and [t2] assuming all elements
  of [t1] to be smaller than all elements of [t2], and
  [|height t1 - height t2| <= 2].
*)

Function merge (s1 s2 :t) : t:=  match s1,s2 with 
  | Leaf, _ => s2 
  | _, Leaf => s1
  | _, Node l2 x2 r2 h2 => 
        let (s2',m) := remove_min l2 x2 r2 in bal s1 m s2'
end.

Lemma merge_avl_1 : forall s1 s2, avl s1 -> avl s2 -> 
 -(2) <= height s1 - height s2 <= 2 -> 
 avl (merge s1 s2) /\ 
 0<= height (merge s1 s2) - max (height s1) (height s2) <=1.
Proof.
 intros s1 s2; functional induction (merge s1 s2); subst;simpl in *; intros.
 split; auto; avl_nns; omega_max.
 split; auto; avl_nns; simpl in *; omega_max.
 destruct s1;try contradiction;clear y.
 generalize (remove_min_avl_1 l2 x2 r2 h2 H0).
 rewrite e1; simpl; destruct 1.
 split.
 apply bal_avl; auto.
 simpl; omega_max.
 omega_bal.
Qed.

Lemma merge_avl : forall s1 s2, avl s1 -> avl s2 -> 
  -(2) <= height s1 - height s2 <= 2 -> avl (merge s1 s2).
Proof. 
 intros; generalize (merge_avl_1 s1 s2 H H0 H1); intuition.
Qed.

Lemma merge_in : forall s1 s2 y, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
 (In y (merge s1 s2) <-> In y s1 \/ In y s2).
Proof. 
 intros s1 s2; functional induction (merge s1 s2); subst; simpl in *; intros.
 intuition_in.
 intuition_in.
 destruct s1;try contradiction;clear y.
 replace s2' with (fst (remove_min l2 x2 r2)); [|rewrite e1; auto].
 rewrite bal_in; auto.
 generalize (remove_min_in l2 x2 r2 h2 y0); rewrite e1; simpl; intro.
 rewrite H3 ; intuition.
 generalize (remove_min_avl l2 x2 r2 h2); rewrite e1; simpl; auto.
Qed.

Lemma merge_bst : forall s1 s2, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
 (forall y1 y2 : elt, In y1 s1 -> In y2 s2 -> X.lt y1 y2) -> 
 bst (merge s1 s2). 
Proof.
 intros s1 s2; functional induction (merge s1 s2); subst;simpl in *; intros; auto.
 destruct s1;try contradiction;clear y.
 apply bal_bst; auto.
 generalize (remove_min_bst l2 x2 r2 h2); rewrite e1; simpl in *; auto.
 intro; intro.
 apply H3; auto.
 generalize (remove_min_in l2 x2 r2 h2 m); rewrite e1; simpl; intuition.
 generalize (remove_min_gt_tree l2 x2 r2 h2); rewrite e1; simpl; auto.
Qed. 

(** * Deletion *)

Function remove (x:elt)(s:tree) { struct s } : t := match s with 
  | Leaf => Leaf
  | Node l y r h =>
      match X.compare x y with
         | LT _ => bal (remove x l) y r
         | EQ _ => merge l r
         | GT _ => bal l  y (remove x r)
      end
   end.

Lemma remove_avl_1 : forall s x, avl s -> 
 avl (remove x s) /\ 0 <= height s - height (remove x s) <= 1.
Proof.
 intros s x; functional induction (remove x s); subst;simpl; intros.
 intuition; omega_max.
 (* LT *)
 inv avl.
 destruct (IHt H0).
 split. 
 apply bal_avl; auto.
 omega_max.
 omega_bal.
 (* EQ *)
 inv avl. 
 generalize (merge_avl_1 l r H0 H1 H2).
 intuition omega_max.
 (* GT *)
 inv avl.
 destruct (IHt H1).
 split. 
 apply bal_avl; auto.
 omega_max.
 omega_bal.
Qed.

Lemma remove_avl : forall s x, avl s -> avl (remove x s).
Proof. 
 intros; generalize (remove_avl_1 s x H); intuition.
Qed.
Hint Resolve remove_avl.

Lemma remove_in : forall s x y, bst s -> avl s -> 
 (In y (remove x s) <-> ~ X.eq y x /\ In y s).
Proof.
 intros s x; functional induction (remove x s); subst;simpl; intros.
 intuition_in.
 (* LT *)
 inv avl; inv bst; clear e0.
 rewrite bal_in; auto.
 generalize (IHt y0 H0); intuition; [ order | order | intuition_in ].
 (* EQ *)
 inv avl; inv bst; clear e0.
 rewrite merge_in; intuition; [ order | order | intuition_in ].
 elim H9; eauto.
 (* GT *)
 inv avl; inv bst; clear e0.
 rewrite bal_in; auto.
 generalize (IHt y0 H5); intuition; [ order | order | intuition_in ].
Qed.

Lemma remove_bst : forall s x, bst s -> avl s -> bst (remove x s).
Proof. 
 intros s x; functional induction (remove x s); simpl; intros.
 auto.
 (* LT *)
 inv avl; inv bst.
 apply bal_bst; auto.
 intro; intro.
 rewrite (remove_in l x y0) in H; auto.
 destruct H; eauto.
 (* EQ *)
 inv avl; inv bst.
 apply merge_bst; eauto.
 (* GT *) 
 inv avl; inv bst.
 apply bal_bst; auto.
 intro; intro.
 rewrite (remove_in r x y0) in H; auto.
 destruct H; eauto.
Qed.

 (** * Minimum element *)

Function min_elt (s:t) : option elt := match s with 
   | Leaf => None
   | Node Leaf y _  _ => Some y
   | Node l _ _ _ => min_elt l
end.

Lemma min_elt_1 : forall s x, min_elt s = Some x -> In x s. 
Proof. 
 intro s; functional induction (min_elt s); subst; simpl.
 inversion 1.
 inversion 1; auto.
 intros.
 destruct l; auto.
Qed.

Lemma min_elt_2 : forall s x y, bst s -> 
 min_elt s = Some x -> In y s -> ~ X.lt y x. 
Proof.
 intro s; functional induction (min_elt s); subst;simpl.
 inversion_clear 2.
 inversion_clear 1.
 inversion 1; subst.
 inversion_clear 1; auto.
 inversion_clear H5.
 destruct l;try contradiction.
 inversion_clear 1.
 simpl.
 destruct l1.
 inversion 1; subst.
 assert (X.lt x _x) by (apply H2; auto).
 inversion_clear 1; auto; order.
 assert (X.lt t _x) by auto.
 inversion_clear 2; auto; 
   (assert (~ X.lt t x) by auto); order.
Qed.

Lemma min_elt_3 : forall s, min_elt s = None -> Empty s.
Proof.
 intro s; functional induction (min_elt s); subst;simpl.
 red; auto.
 inversion 1.
 destruct l;try contradiction. 
 clear y;intro H0.
 destruct (IHo H0 t);  auto.
Qed.

(** * Maximum element *)

Function max_elt (s:t) : option elt := match s with 
   | Leaf => None
   | Node _ y Leaf  _ => Some y
   | Node _ _ r _ => max_elt r
end.

Lemma max_elt_1 : forall s x, max_elt s = Some x -> In x s. 
Proof. 
 intro s; functional induction (max_elt s); subst;simpl.
 inversion 1.
 inversion 1; auto.
 destruct r;try contradiction; auto.
Qed.

Lemma max_elt_2 : forall s x y, bst s -> 
 max_elt s = Some x -> In y s -> ~ X.lt x y. 
Proof.
 intro s; functional induction (max_elt s); subst;simpl.
 inversion_clear 2.
 inversion_clear 1.
 inversion 1; subst.
 inversion_clear 1; auto.
 inversion_clear H5.
 destruct r;try contradiction.
 inversion_clear 1.
(*  inversion 1; subst. *)
(*  assert (X.lt y x) by (apply H4; auto). *)
(*  inversion_clear 1; auto; order. *)
 assert (X.lt _x0 t) by auto.
 inversion_clear 2; auto; 
  (assert (~ X.lt x t) by auto); order.
Qed.

Lemma max_elt_3 : forall s, max_elt s = None -> Empty s.
Proof.
 intro s; functional induction (max_elt s); subst;simpl.
 red; auto.
 inversion 1.
 destruct r;try contradiction.
 intros H0; destruct (IHo H0 t); auto.
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

Lemma choose_3 : forall s s', bst s -> avl s -> bst s' -> avl s' -> 
 forall x x', choose s = Some x -> choose s' = Some x' -> 
  Equal s s' -> X.eq x x'.
Proof.
 unfold choose, Equal; intros s s' Hb Ha Hb' Ha' x x' Hx Hx' H.
 assert (~X.lt x x').
  apply min_elt_2 with s'; auto.
  rewrite <-H; auto using min_elt_1.
 assert (~X.lt x' x).
  apply min_elt_2 with s; auto.
  rewrite H; auto using min_elt_1.
 destruct (X.compare x x'); intuition.
Qed.

(** * Concatenation

    Same as [merge] but does not assume anything about heights.
*)

Function concat (s1 s2 : t) : t  := 
   match s1, s2 with 
      | Leaf, _ => s2 
      | _, Leaf => s1
      | _, Node l2 x2 r2 h2 => 
            let (s2',m) := remove_min l2 x2 r2 in 
            join s1 m s2'
   end.

Lemma concat_avl : forall s1 s2, avl s1 -> avl s2 -> avl (concat s1 s2).
Proof.
 intros s1 s2; functional induction (concat s1 s2); subst;auto.
 destruct s1;try contradiction;clear y.
 intros; apply join_avl; auto.
 generalize (remove_min_avl l2 x2 r2 h2 H0); rewrite e1; simpl; auto.
Qed.
 
Lemma concat_bst :   forall s1 s2, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
 (forall y1 y2 : elt, In y1 s1 -> In y2 s2 -> X.lt y1 y2) -> 
 bst (concat s1 s2).
Proof. 
 intros s1 s2; functional induction (concat s1 s2); subst ;auto.
 destruct s1;try contradiction;clear y. 
 intros;  apply join_bst; auto.
 generalize (remove_min_bst l2 x2 r2 h2 H1 H2); rewrite e1; simpl; auto.
 generalize (remove_min_avl l2 x2 r2 h2 H2); rewrite e1; simpl; auto.
 generalize (remove_min_in l2 x2 r2 h2 m H2); rewrite e1; simpl; auto.
 destruct 1; intuition.
 generalize (remove_min_gt_tree l2 x2 r2 h2 H1 H2); rewrite e1; simpl; auto.
Qed.

Lemma concat_in : forall s1 s2 y, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
 (forall y1 y2 : elt, In y1 s1 -> In y2 s2 -> X.lt y1 y2) -> 
 (In y (concat s1 s2) <-> In y s1 \/ In y s2).
Proof.
 intros s1 s2; functional induction (concat s1 s2);subst;simpl.
 intuition.
 inversion_clear H5.
 destruct s1;try contradiction;clear y;intuition.
 inversion_clear H5.
 destruct s1;try contradiction;clear y; intros. 
 rewrite (join_in _ m s2' y H0).
 generalize (remove_min_in l2 x2 r2 h2 y H2); rewrite e1; simpl.
 intro EQ; rewrite EQ; intuition.
 generalize (remove_min_avl l2 x2 r2 h2 H2); rewrite e1; simpl; auto.
Qed.

(** * Splitting 

    [split x s] returns a triple [(l, present, r)] where
    - [l] is the set of elements of [s] that are [< x]
    - [r] is the set of elements of [s] that are [> x]
    - [present] is [true] if and only if [s] contains  [x].
*)

Function split (x:elt)(s:t) {struct s} : t * (bool * t) := match s with 
  | Leaf => (Leaf, (false, Leaf))
  | Node l y r h => 
     match X.compare x y with 
      | LT _ => match split x l with 
                 | (ll,(pres,rl)) => (ll, (pres, join rl y r))
                end
      | EQ _ => (l, (true, r))
      | GT _ => match split x r with 
                 | (rl,(pres,rr)) => (join l y rl, (pres, rr))
                end
     end
 end.

Lemma split_avl : forall s x, avl s -> 
  avl (fst (split x s)) /\ avl (snd (snd (split x s))).
Proof. 
 intros s x; functional induction (split x s);subst;simpl in *.
 auto.
 rewrite e1 in IHp;simpl in IHp;inversion_clear 1; intuition.
 simpl; inversion_clear 1; auto.
 rewrite e1 in IHp;simpl in IHp;inversion_clear 1; intuition.
Qed.

Lemma split_in_1 : forall s x y, bst s -> avl s -> 
 (In y (fst (split x s)) <-> In y s /\ X.lt y x).
Proof. 
 intros s x; functional induction (split x s);subst;simpl in *.
 intuition; try inversion_clear H1.
 (* LT *)
 rewrite e1 in IHp;simpl in *; inversion_clear 1; inversion_clear 1; clear  H7 H6.
 rewrite (IHp y0 H0 H4); clear IHp e0.
 intuition.
 inversion_clear H6; auto; order.
 (* EQ *)
 simpl in *; inversion_clear 1; inversion_clear 1; clear H6 H5 e0.
 intuition.
 order.
 intuition_in; order.
 (* GT *)
 rewrite e1 in IHp;simpl in *; inversion_clear 1; inversion_clear 1; clear H7 H6.
 rewrite join_in; auto.
 rewrite (IHp y0 H1 H5); clear e1.
 intuition; [ eauto | eauto | intuition_in ].
 generalize (split_avl r x H5); rewrite e1; simpl; intuition.
Qed.

Lemma split_in_2 : forall s x y, bst s -> avl s -> 
 (In y (snd (snd (split x s))) <-> In y s /\ X.lt x y).
Proof. 
 intros s x; functional induction (split x s);subst;simpl in *.
 intuition; try inversion_clear H1.
 (* LT *)
 rewrite e1 in IHp; simpl in *; inversion_clear 1; inversion_clear 1; clear H7 H6.
 rewrite join_in; auto.
 rewrite (IHp y0 H0 H4); clear IHp e0.
 intuition; [ order | order | intuition_in ].
 generalize (split_avl l x H4); rewrite e1; simpl; intuition.
 (* EQ *)
 simpl in *; inversion_clear 1; inversion_clear 1; clear H6 H5 e0.
 intuition; [ order | intuition_in; order ]. 
 (* GT *)
 rewrite e1 in IHp; simpl in *; inversion_clear 1; inversion_clear 1; clear H7 H6.
 rewrite (IHp y0 H1 H5); clear IHp e0.
 intuition; intuition_in; order. 
Qed.

Lemma split_in_3 : forall s x, bst s -> avl s -> 
 (fst (snd (split x s)) = true <-> In x s).
Proof. 
 intros s x; functional induction (split x s);subst;simpl in *.
 intuition; try inversion_clear H1.
 (* LT *)
 rewrite e1 in IHp; simpl in *; inversion_clear 1; inversion_clear 1; clear H7 H6.
 rewrite IHp; auto.
 intuition_in; absurd (X.lt x y); eauto.
 (* EQ *)
 simpl in *; inversion_clear 1; inversion_clear 1; intuition.
 (* GT *)
 rewrite e1 in IHp; simpl in *; inversion_clear 1; inversion_clear 1; clear H7 H6.
 rewrite IHp; auto.
 intuition_in; absurd (X.lt y x); eauto.
Qed.

Lemma split_bst : forall s x, bst s -> avl s -> 
 bst (fst (split x s)) /\ bst (snd (snd (split x s))).
Proof. 
 intros s x; functional induction (split x s);subst;simpl in *.  
 intuition.
 (* LT *)
 rewrite e1 in IHp; simpl in *; inversion_clear 1; inversion_clear 1.
 intuition.
 apply join_bst; auto.
 generalize (split_avl l x H4); rewrite e1; simpl; intuition.
 intro; intro.
 generalize (split_in_2 l x y0 H0 H4); rewrite e1; simpl; intuition.
 (* EQ *)
 simpl in *; inversion_clear 1; inversion_clear 1; intuition.
 (* GT *)
 rewrite e1 in IHp; simpl in *; inversion_clear 1; inversion_clear 1.
 intuition.
 apply join_bst; auto.
 generalize (split_avl r x H5); rewrite e1; simpl; intuition.
 intro; intro.
 generalize (split_in_1 r x y0 H1 H5); rewrite e1; simpl; intuition.
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
 induction s1 as [ | l1 Hl1 x1 r1 Hr1 h1]; simpl; auto.
 destruct s2 as [ | l2 x2 r2 h2]; intros; auto.
 generalize H0; inv avl.
 set (r:=Node l2 x2 r2 h2) in *; clearbody r; intros. 
 destruct (split_avl r x1 H8).
 destruct (split x1 r) as [l2' (b,r2')]; simpl in *.
 destruct b; [ apply join_avl | apply concat_avl ]; auto.
Qed.

Lemma inter_bst_in : forall s1 s2, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
 bst (inter s1 s2) /\ (forall y, In y (inter s1 s2) <-> In y s1 /\ In y s2).
Proof. 
 induction s1 as [ | l1 Hl1 x1 r1 Hr1 h1]; simpl; auto.
 intuition; inversion_clear H3.
 destruct s2 as [ | l2 x2 r2 h2]; intros.
 simpl; intuition; inversion_clear H3.
 generalize H1 H2; inv avl; inv bst.
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
 apply join_bst; try apply inter_avl; auto; 
  intro y; [rewrite (H22 y)|rewrite (H24 y)]; intuition.
 (* bst concat *)
 apply concat_bst; try apply inter_avl; auto.
 intros y1 y2; rewrite (H22 y1), (H24 y2); intuition eauto.
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
 rewrite H30, H28; intuition_in.
 apply In_1 with x1; auto.
 (* in concat *)
 rewrite concat_in; try apply inter_avl; auto.
 rewrite H30, H28; intuition_in.
 generalize (H26 (In_1 _ _ _ H22 H35)); intro; discriminate.
 intros y1 y2; rewrite (H28 y1), (H30 y2); intuition eauto.
Qed.

Lemma inter_bst : forall s1 s2, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
 bst (inter s1 s2). 
Proof. 
 intros s1 s2 B1 A1 B2 A2; destruct (inter_bst_in s1 s2 B1 A1 B2 A2); auto.
Qed.

Lemma inter_in : forall s1 s2 y, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
 (In y (inter s1 s2) <-> In y s1 /\ In y s2).
Proof. 
 intros s1 s2 y B1 A1 B2 A2; destruct (inter_bst_in s1 s2 B1 A1 B2 A2); auto.
Qed.

(** * Difference *)

Fixpoint diff (s1 s2 : t) { struct s1 } : t := match s1, s2 with 
 | Leaf, _ => Leaf
 | _, Leaf => s1
 | Node l1 x1 r1 h1, _ => 
    match split x1 s2 with 
      | (l2',(true,r2')) => concat (diff l1 l2') (diff r1 r2')
      | (l2',(false,r2')) => join (diff l1 l2') x1 (diff r1 r2')
    end
end. 

Lemma diff_avl : forall s1 s2, avl s1 -> avl s2 -> avl (diff s1 s2). 
Proof. 
 (* intros s1 s2; functional induction diff s1 s2; auto. BOF BOF *)
 induction s1 as [ | l1 Hl1 x1 r1 Hr1 h1]; simpl; auto.
 destruct s2 as [ | l2 x2 r2 h2]; intros; auto.
 generalize H0; inv avl.
 set (r:=Node l2 x2 r2 h2) in *; clearbody r; intros. 
 destruct (split_avl r x1 H8).
 destruct (split x1 r) as [l2' (b,r2')]; simpl in *.
 destruct b; [ apply concat_avl | apply join_avl ]; auto.
Qed.

Lemma diff_bst_in : forall s1 s2, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
 bst (diff s1 s2) /\ (forall y, In y (diff s1 s2) <-> In y s1 /\ ~In y s2).
Proof. 
 induction s1 as [ | l1 Hl1 x1 r1 Hr1 h1]; simpl; auto.
 intuition; inversion_clear H3.
 destruct s2 as [ | l2 x2 r2 h2]; intros; auto.
 intuition; inversion_clear H4.
 generalize H1 H2; inv avl; inv bst.
 set (r:=Node l2 x2 r2 h2) in *; clearbody r; intros.
 destruct (split_avl r x1 H17).
 destruct (split_bst r x1 H16 H17).
 split.
 (* bst *)
 destruct (split x1 r) as [l2' (b,r2')]; simpl in *.
 destruct (Hl1 l2'); auto.
 destruct (Hr1 r2'); auto.
 destruct b.
 (* bst concat *)
 apply concat_bst; try apply diff_avl; auto.
 intros y1 y2; rewrite (H22 y1), (H24 y2); intuition eauto.
 (* bst join *)
 apply join_bst; try apply diff_avl; auto; 
  intro y; [rewrite (H22 y)|rewrite (H24 y)]; intuition.
 (* in *)
 intros.
 destruct (split_in_1 r x1 y H16 H17). 
 destruct (split_in_2 r x1 y H16 H17).
 destruct (split_in_3 r x1 H16 H17).
 destruct (split x1 r) as [l2' (b,r2')]; simpl in *.
 destruct (Hl1 l2'); auto.
 destruct (Hr1 r2'); auto.
 destruct b.
 (* in concat *)
 rewrite concat_in; try apply diff_avl; auto.
 rewrite H30, H28; intuition_in.
 elim H35; apply In_1 with x1; auto.
 intros; generalize (H28 y1) (H30 y2); intuition eauto.
 (* in join *)
 rewrite join_in; try apply diff_avl; auto.
 rewrite H30, H28; intuition_in.
 generalize (H26 (In_1 _ _ _ H34 H24)); intro; discriminate.
Qed.

Lemma diff_bst : forall s1 s2, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
 bst (diff s1 s2). 
Proof. 
 intros s1 s2 B1 A1 B2 A2; destruct (diff_bst_in s1 s2 B1 A1 B2 A2); auto.
Qed.

Lemma diff_in : forall s1 s2 y, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
 (In y (diff s1 s2) <-> In y s1 /\ ~In y s2).
Proof. 
 intros s1 s2 y B1 A1 B2 A2; destruct (diff_bst_in s1 s2 B1 A1 B2 A2); auto.
Qed.

(** * Elements *)

(** [elements_tree_aux acc t] catenates the elements of [t] in infix
    order to the list [acc] *)

Fixpoint elements_aux (acc : list X.t) (t : tree) {struct t} : list X.t :=
  match t with
   | Leaf => acc
   | Node l x r _ => elements_aux (x :: elements_aux acc r) l
  end.

(** then [elements] is an instanciation with an empty [acc] *)

Definition elements := elements_aux nil.

Lemma elements_aux_in : forall s acc x, 
 InA X.eq x (elements_aux acc s) <-> In x s \/ InA X.eq x acc.
Proof.
 induction s as [ | l Hl x r Hr h ]; simpl; auto.
 intuition.
 inversion H0.
 intros.
 rewrite Hl.
 destruct (Hr acc x0); clear Hl Hr.
 intuition; inversion_clear H3; intuition.
Qed.

Lemma elements_in : forall s x, InA X.eq x (elements s) <-> In x s. 
Proof. 
 intros; generalize (elements_aux_in s nil x); intuition.
 inversion_clear H0.
Qed.

Lemma elements_aux_sort : forall s acc, bst s -> sort X.lt acc ->
 (forall x y : elt, InA X.eq x acc -> In y s -> X.lt y x) ->
 sort X.lt (elements_aux acc s).
Proof.
 induction s as [ | l Hl y r Hr h]; simpl; intuition.
 inv bst.
 apply Hl; auto.
 constructor. 
 apply Hr; auto.
 apply MX.In_Inf; intros.
 destruct (elements_aux_in r acc y0); intuition.
 intros.
 inversion_clear H.
 order.
 destruct (elements_aux_in r acc x); intuition eauto.
Qed.

Lemma elements_sort : forall s : tree, bst s -> sort X.lt (elements s).
Proof.
 intros; unfold elements; apply elements_aux_sort; auto.
 intros; inversion H0.
Qed.
Hint Resolve elements_sort.

Lemma elements_nodup : forall s : tree, bst s -> NoDupA X.eq (elements s).
Proof.
 auto.
Qed.

(** * Filter *)

Section F.
Variable f : elt -> bool.

Fixpoint filter_acc (acc:t)(s:t) { struct s } : t := match s with 
  | Leaf => acc
  | Node l x r h => 
     filter_acc (filter_acc (if f x then add x acc else acc) l) r 
 end.

Definition filter := filter_acc Leaf. 

Lemma filter_acc_avl : forall s acc, avl s -> avl acc -> 
 avl (filter_acc acc s).
Proof.
 induction s; simpl; auto.
 intros.
 inv avl.
 apply IHs2; auto.
 apply IHs1; auto.
 destruct (f t); auto.
Qed. 
Hint Resolve filter_acc_avl.

Lemma filter_acc_bst : forall s acc, bst s -> avl s -> bst acc -> avl acc -> 
 bst (filter_acc acc s).
Proof.
 induction s; simpl; auto.
 intros.
 inv avl; inv bst.
 destruct (f t); auto.
 apply IHs2; auto.
 apply IHs1; auto.
 apply add_bst; auto.
Qed. 

Lemma filter_acc_in : forall s acc, avl s -> avl acc -> 
 compat_bool X.eq f -> forall x : elt, 
 In x (filter_acc acc s) <-> In x acc \/ In x s /\ f x = true.
Proof.  
 induction s; simpl; intros.
 intuition_in.
 inv bst; inv avl.
 rewrite IHs2 by (destruct (f t); auto).
 rewrite IHs1 by (destruct (f t); auto).
 case_eq (f t); intros.
 rewrite (add_in); auto.
 intuition_in.
 rewrite (H1 _ _ H8).
 intuition.
 intuition_in.
 rewrite (H1 _ _ H8) in H9.
 rewrite H in H9; discriminate.
Qed.

Lemma filter_avl : forall s, avl s -> avl (filter s). 
Proof.
 unfold filter; intros; apply filter_acc_avl; auto.
Qed.

Lemma filter_bst : forall s, bst s -> avl s -> bst (filter s). 
Proof.
 unfold filter; intros; apply filter_acc_bst; auto.
Qed.

Lemma filter_in : forall s, avl s -> 
 compat_bool X.eq f -> forall x : elt, 
 In x (filter s) <-> In x s /\ f x = true.
Proof.
 unfold filter; intros; rewrite filter_acc_in; intuition_in.
Qed. 

(** * Partition *)

Fixpoint partition_acc (acc : t*t)(s : t) { struct s } : t*t := 
  match s with 
   | Leaf => acc
   | Node l x r _ => 
      let (acct,accf) := acc in 
      partition_acc 
        (partition_acc 
           (if f x then (add x acct, accf) else (acct, add x accf)) l) r
  end. 

Definition partition := partition_acc (Leaf,Leaf).

Lemma partition_acc_avl_1 : forall s acc, avl s -> 
 avl (fst acc) -> avl (fst (partition_acc acc s)).
Proof.
 induction s; simpl; auto.
 destruct acc as [acct accf]; simpl in *.
 intros.
 inv avl.
 apply IHs2; auto.
 apply IHs1; auto.
 destruct (f t); simpl; auto.
Qed. 

Lemma partition_acc_avl_2 : forall s acc, avl s -> 
 avl (snd acc) -> avl (snd (partition_acc acc s)).
Proof.
 induction s; simpl; auto.
 destruct acc as [acct accf]; simpl in *.
 intros.
 inv avl.
 apply IHs2; auto.
 apply IHs1; auto.
 destruct (f t); simpl; auto.
Qed. 
Hint Resolve partition_acc_avl_1 partition_acc_avl_2.

Lemma partition_acc_bst_1 : forall s acc, bst s -> avl s -> 
 bst (fst acc) -> avl (fst acc) -> 
 bst (fst (partition_acc acc s)).
Proof.
 induction s; simpl; auto.
 destruct acc as [acct accf]; simpl in *.
 intros.
 inv avl; inv bst.
 destruct (f t); auto.
 apply IHs2; simpl; auto.
 apply IHs1; simpl; auto.
 apply add_bst; auto.
 apply partition_acc_avl_1; simpl; auto.
Qed. 

Lemma partition_acc_bst_2 : forall s acc, bst s -> avl s -> 
 bst (snd acc) -> avl (snd acc) -> 
 bst (snd (partition_acc acc s)).
Proof.
 induction s; simpl; auto.
 destruct acc as [acct accf]; simpl in *.
 intros.
 inv avl; inv bst.
 destruct (f t); auto.
 apply IHs2; simpl; auto.
 apply IHs1; simpl; auto.
 apply add_bst; auto.
 apply partition_acc_avl_2; simpl; auto.
Qed. 

Lemma partition_acc_in_1 : forall s acc, avl s -> avl (fst acc) -> 
 compat_bool X.eq f -> forall x : elt, 
 In x (fst (partition_acc acc s)) <-> 
 In x (fst acc) \/ In x s /\ f x = true.
Proof.  
 induction s; simpl; intros.
 intuition_in.
 destruct acc as [acct accf]; simpl in *.
 inv bst; inv avl.
 rewrite IHs2 by (destruct (f t); auto; apply partition_acc_avl_1; simpl; auto).
 rewrite IHs1 by (destruct (f t); simpl; auto).
 case_eq (f t); simpl; intros.
 rewrite (add_in); auto.
 intuition_in.
 rewrite (H1 _ _ H8).
 intuition.
 intuition_in.
 rewrite (H1 _ _ H8) in H9.
 rewrite H in H9; discriminate.
Qed.

Lemma partition_acc_in_2 : forall s acc, avl s -> avl (snd acc) -> 
 compat_bool X.eq f -> forall x : elt, 
 In x (snd (partition_acc acc s)) <-> 
 In x (snd acc) \/ In x s /\ f x = false.
Proof.  
 induction s; simpl; intros.
 intuition_in.
 destruct acc as [acct accf]; simpl in *.
 inv bst; inv avl.
 rewrite IHs2 by (destruct (f t); auto; apply partition_acc_avl_2; simpl; auto).
 rewrite IHs1 by (destruct (f t); simpl; auto).
 case_eq (f t); simpl; intros.
 intuition.
 intuition_in.
 rewrite (H1 _ _ H8) in H9.
 rewrite H in H9; discriminate.
 rewrite (add_in); auto.
 intuition_in.
 rewrite (H1 _ _ H8).
 intuition.
Qed. 

Lemma partition_avl_1 : forall s, avl s -> avl (fst (partition s)). 
Proof.
 unfold partition; intros; apply partition_acc_avl_1; auto.
Qed.

Lemma partition_avl_2 : forall s, avl s -> avl (snd (partition s)). 
Proof.
 unfold partition; intros; apply partition_acc_avl_2; auto.
Qed.

Lemma partition_bst_1 : forall s, bst s -> avl s -> 
 bst (fst (partition s)). 
Proof.
 unfold partition; intros; apply partition_acc_bst_1; auto.
Qed.

Lemma partition_bst_2 : forall s, bst s -> avl s -> 
 bst (snd (partition s)). 
Proof.
 unfold partition; intros; apply partition_acc_bst_2; auto.
Qed.

Lemma partition_in_1 : forall s, avl s -> 
 compat_bool X.eq f -> forall x : elt, 
 In x (fst (partition s)) <-> In x s /\ f x = true.
Proof.
 unfold partition; intros; rewrite partition_acc_in_1; 
 simpl in *; intuition_in.
Qed. 

Lemma partition_in_2 : forall s, avl s -> 
 compat_bool X.eq f -> forall x : elt, 
 In x (snd (partition s)) <-> In x s /\ f x = false.
Proof.
 unfold partition; intros; rewrite partition_acc_in_2; 
 simpl in *; intuition_in.
Qed. 

(** [for_all] and [exists] *)

Fixpoint for_all (s:t) : bool := match s with 
  | Leaf => true
  | Node l x r _ => f x && for_all l && for_all r
end.

Lemma for_all_1 : forall s, compat_bool X.eq f ->
 For_all (fun x => f x = true) s -> for_all s = true.
Proof.
 induction s; simpl; auto.
 intros.
 rewrite IHs1; try red; auto.
 rewrite IHs2; try red; auto.
 generalize (H0 t).
 destruct (f t); simpl; auto.
Qed.

Lemma for_all_2 : forall s, compat_bool X.eq f ->
 for_all s = true -> For_all (fun x => f x = true) s.
Proof.
 induction s; simpl; auto; intros; red; intros; inv In.
 destruct (andb_prop _ _ H0); auto.
 destruct (andb_prop _ _ H1); eauto.
 apply IHs1; auto.
 destruct (andb_prop _ _ H0); auto.
 destruct (andb_prop _ _ H1); auto.
 apply IHs2; auto.
 destruct (andb_prop _ _ H0); auto.
Qed.

Fixpoint exists_ (s:t) : bool := match s with 
  | Leaf => false
  | Node l x r _ => f x || exists_ l || exists_ r
end.  

Lemma exists_1 : forall s, compat_bool X.eq f ->
 Exists (fun x => f x = true) s -> exists_ s = true.
Proof.
 induction s; simpl; destruct 2 as (x,(U,V)); inv In.
 rewrite (H _ _ (X.eq_sym H0)); rewrite V; auto.
 apply orb_true_intro; left.
 apply orb_true_intro; right; apply IHs1; firstorder.
 apply orb_true_intro; right; apply IHs2; firstorder.
Qed.

Lemma exists_2 : forall s, compat_bool X.eq f ->
 exists_ s = true -> Exists (fun x => f x = true) s.
Proof. 
 induction s; simpl; intros.
 discriminate.
 destruct (orb_true_elim _ _ H0) as [H1|H1]. 
 destruct (orb_true_elim _ _ H1) as [H2|H2].
 exists t; auto.
 destruct (IHs1 H H2); firstorder.
 destruct (IHs2 H H1); firstorder.
Qed. 

End F.

(** * Fold *)

Module L := FSetList0.Raw X.

Fixpoint fold (A : Type) (f : elt -> A -> A)(s : tree) {struct s} : A -> A := 
 fun a => match s with
  | Leaf => a
  | Node l x r _ => fold A f r (f x (fold A f l a))
 end.
Arguments fold [A].

Definition fold' (A : Type) (f : elt -> A -> A)(s : tree) := 
  L.fold f (elements s).
Arguments fold' [A].

Lemma fold_equiv_aux :
 forall (A : Type) (s : tree) (f : elt -> A -> A) (a : A) (acc : list elt),
 L.fold f (elements_aux acc s) a = L.fold f acc (fold f s a).
Proof.
 simple induction s.
 simpl in |- *; intuition.
 simpl in |- *; intros.
 rewrite H.
 simpl.
 apply H0.
Qed.

Lemma fold_equiv :
 forall (A : Type) (s : tree) (f : elt -> A -> A) (a : A),
 fold f s a = fold' f s a.
Proof.
 unfold fold', elements in |- *. 
 simple induction s; simpl in |- *; auto; intros.
 rewrite fold_equiv_aux.
 rewrite H0.
 simpl in |- *; auto.
Qed.

Lemma fold_1 : 
 forall (s:t)(Hs:bst s)(A : Type)(f : elt -> A -> A)(i : A),
 fold f s i = fold_left (fun a e => f e a) (elements s) i.
Proof.
 intros.
 rewrite fold_equiv.
 unfold fold'.
 rewrite L.fold_1.
 unfold L.elements; auto.
 apply elements_sort; auto.
Qed.

(** * Cardinal *)

Fixpoint cardinal (s : tree) : nat :=
  match s with
   | Leaf => 0%nat
   | Node l _ r _ => S (cardinal l + cardinal r)
  end.

Lemma cardinal_elements_aux_1 :
 forall s acc, (length acc + cardinal s)%nat = length (elements_aux acc s).
Proof.
 simple induction s; simpl in |- *; intuition.
 rewrite <- H.
 simpl in |- *.
 rewrite <- H0; omega.
Qed.

Lemma cardinal_elements_1 : forall s : tree, cardinal s = length (elements s).
Proof.
 exact (fun s => cardinal_elements_aux_1 s nil).
Qed.

(** Induction over cardinals *)

Lemma sorted_subset_cardinal : forall l' l : list X.t,
 sort X.lt l -> sort X.lt l' ->
 (forall x : elt, InA X.eq x l -> InA X.eq x l') -> (length l <= length l')%nat.
Proof.
 simple induction l'; simpl in |- *; intuition.
 destruct l; trivial; intros.
 absurd (InA X.eq t nil); intuition.
 inversion_clear H2.
 inversion_clear H1.
 destruct l0; simpl in |- *; intuition auto with arith.
 inversion_clear H0.
 apply le_n_S.
 case (X.compare t a); intro.
 absurd (InA X.eq t (a :: l)).
 intro.
 inversion_clear H0.
 order.
 assert (X.lt a t).
 apply MX.Sort_Inf_In with l; auto.
 order.
 firstorder.
 apply H; auto.
 intros.
 assert (InA X.eq x (a :: l)).
 apply H2; auto.
 inversion_clear H6; auto.
 assert (X.lt t x).
 apply MX.Sort_Inf_In with l0; auto.
 order.
 apply le_trans with (length (t :: l0)).
 simpl in |- *; omega.
 apply (H (t :: l0)); auto.
 intros.
 assert (InA X.eq x (a :: l)); firstorder.
 inversion_clear H6; auto.
 assert (X.lt a x).
 apply MX.Sort_Inf_In with (t :: l0); auto.
 elim (X.lt_not_eq (x:=a) (y:=x)); auto.
Qed.

Lemma cardinal_subset : forall a b : tree, bst a -> bst b ->
 (forall y : elt, In y a -> In y b) ->
 (cardinal a <= cardinal b)%nat.
Proof.
 intros.
 do 2 rewrite cardinal_elements_1.
 apply sorted_subset_cardinal; auto.
 intros.
 generalize (elements_in a x) (elements_in b x).
 intuition.
Qed.

Lemma height_0 : forall s, avl s -> height s = 0 -> s = Leaf.
Proof.
 destruct 1; intuition; simpl in *.
 avl_nns; simpl in *; elimtype False; omega_max.
Qed.

Notation "s #1" := (fst s) (at level 9).
Notation "s #2" := (snd s) (at level 9).

Definition cardinal2 (s:t*t) := 
 (cardinal s#1 + cardinal s#2)%nat.

(** * Union *)

Obligation Tactic := 
 simpl ; intros ; destruct_exists ; simpl in * ; try subst; 
 unfold cardinal2; simpl @fst in *; simpl @snd in *; 
 try match goal with u:forall s:_,{x:_|_} |- _ => clear u end; 
 try match goal with a: _ /\ _ /\ _ /\ _ |- _ => 
   destruct a as (B1 & A1 & B2 & A2)
 end.

Program Fixpoint union
 (s : t * t | bst s#1 /\ avl s#1 /\ bst s#2 /\ avl s#2) 
 { measure (cardinal2 s) } : 
 { s' : t | bst s' /\ avl s' /\ 
           forall x, In x s' <-> In x s#1 \/ In x s#2 }
 :=
 match s with 
  | (Leaf, Leaf) => s#2
  | (Leaf, Node _ _ _ _) => s#2
  | (Node _ _ _ _, Leaf) => s#1
  | (Node l1 x1 r1 h1, Node l2 x2 r2 h2) => 
        if ge_lt_dec h1 h2 then
          if eq_dec h2 1 then add x2 s#1 else
          let '(l2',(_,r2')) := split x1 s#2 in
             join (union (l1,l2')) x1 (union (r1,r2'))
        else
          if eq_dec h1 1 then add x1 s#2 else
          let '(l1',(_,r1')) := split x2 s#1 in 
             join (union (l1',l2)) x2 (union (r1',r2))
 end.

Next Obligation. (* 1: postcondition about s2 *)
 intuition_in.
Qed.

Next Obligation. (* 2: postcondition about s2 *)
 intuition_in.
Qed.

Next Obligation. (* 3: postcondition about s1 *)
 intuition_in.
Qed.

Next Obligation. (* 4: postcondition about (add x2 s1) *)
  try rename g into H. (* compatibility 8.9 *)
  try rename e into H0. (* compatibility 8.9 *)
  split.
  apply add_bst; auto.
  split; auto.
  intros.
  rewrite add_in; auto.
  inv avl; inv bst.
  avl_nn l2; avl_nn r2.
  rewrite (height_0 _ H1); [ | omega_max].
  rewrite (height_0 _ H2); [ | omega_max].
  intuition_in.
Qed.

Next Obligation. (* 5: precondition for (union (l1,l2')) *)
  generalize (split_avl _ x1 A2).
  generalize (split_bst _ x1 B2 A2).
  rewrite <- Heq_anonymous; simpl.
  inv avl; inv bst; intuition.
Qed.

Next Obligation. (* 6: decreasing of (union (l1,l2')) *)
  assert (l2' = (split x1 (Node l2 x2 r2 h2))#1).
    rewrite <- Heq_anonymous; auto.
  clear Heq_anonymous.
  assert (cardinal l2' <= cardinal (Node l2 x2 r2 h2))%nat.
    subst l2'.
    apply cardinal_subset; auto.
    destruct (split_bst _ x1 B2 A2); auto.
    intros y; rewrite (split_in_1 _ x1 y B2 A2); tauto.
  simpl (cardinal (Node l1 x1 r1 h1)).
 omega.
Qed.

Next Obligation. (* 7: precondition for (union (r1,r2')) *)
  generalize (split_avl _ x1 A2).
  generalize (split_bst _ x1 B2 A2).
  rewrite <- Heq_anonymous; simpl.
  inv avl; inv bst; intuition.
Qed.

Next Obligation. (* 8: decreasing of (union (r1,r2')) *)
  assert (r2' = (split x1 (Node l2 x2 r2 h2))#2#2).
    rewrite <- Heq_anonymous; auto.
  clear Heq_anonymous.
  assert (cardinal r2' <= cardinal (Node l2 x2 r2 h2))%nat.
    subst r2'.
    apply cardinal_subset; auto.
      destruct (split_bst _ x1 B2 A2); auto.
      intros y; rewrite (split_in_2 _ x1 y B2 A2); tauto.
  simpl (cardinal (Node l1 x1 r1 h1)).
  omega.
Qed.

Next Obligation. (* 9: postcondition for (join (union (l1,l2')) x1 (union (r1,r2'))) *)
  try rename g into H. (* compatibility 8.9 *)
  try rename n into H0. (* compatibility 8.9 *)
  do 2 destruct_call union. simpl in a, a0 |- *.
  decompose [and] a; clear a.
  decompose [and] a0; clear a0.
  clear union; simpl @snd in *; simpl @fst in *.
  rename x into l; rename x2 into r.
  assert (l2' = (split x1 (Node l2 r r2 h2))#1
    /\ r2' = (split x1 (Node l2 r r2 h2))#2#2).
  rewrite <- Heq_anonymous; auto.
  destruct H5; subst l2' r2'; clear Heq_anonymous.
  split.
  apply join_bst; auto. 
  red; intro.
  rewrite H4; destruct 1.
  inv bst; auto.
  rewrite (split_in_1 _ x1 y B2 A2) in H5; tauto.
  red; intro.
  rewrite H7; destruct 1.
  inv bst; auto.
  rewrite (split_in_2 _ x1 y B2 A2) in H5; tauto.
  split; auto.
  intro y.
  rewrite join_in; auto.
  rewrite H4; rewrite H7; clear H4 H7.
  rewrite (split_in_1 _ x1 y B2 A2); rewrite (split_in_2 _ x1 y B2 A2).
  case (X.compare y x1); intuition_in.
Qed.

Next Obligation. (* 10: postcondition about (add x1 s2) *)
 try rename l into H. (* compatibility 8.9 *)
 try rename e into H0. (* compatibility 8.9 *)
 split.
 apply add_bst; auto.
 split; auto.
 intros.
 rewrite add_in; auto.
 inv avl; inv bst.
 avl_nn l1; avl_nn r1.
 rewrite (height_0 _ H5); [ | omega_max].
 rewrite (height_0 _ H6); [ | omega_max].
 intuition_in.
Qed.

Next Obligation. (* 11: precondition for (union (l1',l2)) *)
 generalize (split_avl _ x2 A1).
 generalize (split_bst _ x2 B1 A1).
 rewrite <- Heq_anonymous; simpl.
 inv avl; inv bst; intuition.
Qed.

Next Obligation. (* 12: decreasing of (union (l1',l2)) *)
 assert (l1' = (split x2 (Node l1 x1 r1 h1))#1).
   rewrite <- Heq_anonymous; auto.
 clear Heq_anonymous.
 assert (cardinal l1' <= cardinal (Node l1 x1 r1 h1))%nat.
  subst l1'.
  apply cardinal_subset; auto.
  destruct (split_bst _ x2 B1 A1); auto.
  intros y; rewrite (split_in_1 _ x2 y B1 A1); tauto.
 simpl (cardinal (Node l2 x2 r2 h2)).
 omega.
Qed.

Next Obligation. (* 13: precondition for (union (r1',r2)) *)
 generalize (split_avl _ x2 A1).
 generalize (split_bst _ x2 B1 A1).
 rewrite <- Heq_anonymous; simpl.
 inv avl; inv bst; intuition.
Qed.

Next Obligation. (* 14: decreasing of (union (r1',r2)) *)
 assert (r1' = (split x2 (Node l1 x1 r1 h1))#2#2).
   rewrite <- Heq_anonymous; auto.
 clear Heq_anonymous.
 assert (cardinal r1' <= cardinal (Node l1 x1 r1 h1))%nat.
  subst r1'.
  apply cardinal_subset; auto.
  destruct (split_bst _ x2 B1 A1); auto.
  intros y; rewrite (split_in_2 _ x2 y B1 A1); tauto.
 simpl (cardinal (Node l2 x2 r2 h2)).
 omega.
Qed.

Next Obligation. (* 15: postcondition for (join (union (l1',l2)) x2 (union (snd pr1',r2))) *)
 try rename l into H. (* compatibility 8.9 *)
 try rename n into H0. (* compatibility 8.9 *)
 do 2 destruct_call union; simpl in a, a0 |- *.
 decompose [and] a; clear a.
 decompose [and] a0; clear a0.
 simpl @snd in *; simpl @fst in *.
 clear union; rename x into l; rename x2 into r.
 assert (l1' = (split r (Node l1 x1 r1 h1))#1 
      /\ r1' = (split r (Node l1 x1 r1 h1))#2#2).
   rewrite <- Heq_anonymous; auto.
 destruct H5; subst l1' r1'; clear Heq_anonymous.
 split.
 apply join_bst; auto. 
 red; intro.
 rewrite H4; destruct 1.
 rewrite (split_in_1 _ r y B1 A1) in H5; tauto.
 inv bst; auto.
 red; intro.
 rewrite H7; destruct 1.
 rewrite (split_in_2 _ r y B1 A1) in H5; tauto.
 inv bst; auto.
 split; auto.
 intro y.
 rewrite join_in; auto.
 rewrite H4; rewrite H7; clear H4 H7.
 rewrite (split_in_1 _ r y B1 A1); rewrite (split_in_2 _ r y B1 A1).
 case (X.compare y r); intuition_in.
Qed.

Next Obligation. (* Well_foundedness *)
auto with arith.
Defined.

(** * Subset *)

Local Open Scope program_scope.

Notation "a && b" := 
 (if a then if b then in_left else in_right else in_right).

Obligation Tactic := 
 simpl ; intros ; destruct_exists ; simpl in * ; try subst; 
 unfold cardinal2;
 simpl @fst in *; simpl @snd in *; 
 try match goal with u:forall s:_,{_}+{_} |- _ => clear u end;
 try match goal with a:_ /\ _ |- _ => destruct a as (B1,B2) end.

Program Fixpoint subset (s:t*t|bst s#1 /\ bst s#2) 
 { measure (cardinal2 s) }
 : { Subset s#1 s#2 } + {~Subset s#1 s#2 } :=
 match s with 
  | (Leaf, Leaf) => in_left
  | (Leaf, Node _ _ _ _) => in_left
  | (Node _ _ _ _, Leaf) => in_right
  | (Node l1 x1 r1 h1, Node l2 x2 r2 h2) => 
     match X.compare x1 x2 with 
      | EQ _ => subset (l1,l2) && subset (r1,r2)
      | LT _ => subset (Node l1 x1 Leaf 0, l2) && subset (r1,s#2)
      | GT _ => subset (Node Leaf x1 r1 0, r2) && subset (l1,s#2)
     end
 end.

Next Obligation. (* post Leaf,Leaf *)
 red; auto.
Qed.

Next Obligation. (* post Leaf,Node *)
 red; intros; inv In.
Qed.

Next Obligation. (* post Node,Leaf *)
 intro; assert (In wildcard'0 Leaf) by auto; inv In.
Qed.

Next Obligation. (* pre subset (l1,l2) *)
 inv bst; auto.
Qed.

Next Obligation. (* decr subset (l1,l2) *)
 simpl; omega.
Qed.

Next Obligation. (* pre subset (r1,r2) *)
 inv bst; auto.
Qed.

Next Obligation. (* decr subset (r1,r2) *)
 simpl; omega.
Qed.

Next Obligation. (* post EQ + left + left *)
 clear Heq_anonymous. 
 red; intros. 
 intuition_in; constructor; order.
Qed.

Next Obligation. (* post EQ + left + right *)
 clear Heq_anonymous.
 unfold Subset in *; contradict H0; intros.
 assert (In a (Node l2 x2 r2 h2)) by auto.
 inv bst; intuition_in; order.
Qed.

Next Obligation. (* post EQ + right + _ *)
 clear Heq_anonymous.
 unfold Subset in *; contradict H; intros.
 assert (In a (Node l2 x2 r2 h2)) by auto.
 inv bst; intuition_in; order.
Qed.

Next Obligation. (* pre subset (Node l1 x1 Leaf 0, l2) *)
 inv bst; auto.
Qed.

Next Obligation. (* decr subset (Node l1 x1 Leaf 0, l2) *)
 simpl; omega.
Qed.

Next Obligation. (* pre subset (r1,s2) *)
 split; auto; inv bst; auto.
Qed.

Next Obligation. (* decr subset (r1,s2) *)
 simpl; omega.
Qed.

Next Obligation. (* post LT + left + left *)
 clear Heq_anonymous.
 unfold Subset in *; intros.
 inv bst; intuition_in; order.
Qed.

Next Obligation. (* post LT + left + right *)
 clear Heq_anonymous.
 unfold Subset in *; contradict H0; intros. 
 inv bst; intuition_in; order.
Qed.

Next Obligation. (* post LT + right + _ *)
 clear Heq_anonymous.
 unfold Subset in *; contradict H; intros. 
 assert (In a (Node l2 x2 r2 h2)) by (inv In; auto).
 inv bst; intuition_in; order.
Qed.

Next Obligation. (* pre subset (Node Leaf x1 r1 0, r2) *)
 split; auto; inv bst; auto.
Qed.

Next Obligation. (* decr subset (Node Leaf x1 r1 0, r2) *)
 simpl; omega.
Qed.

Next Obligation. (* pre subset (l1,s2) *)
 split; auto; inv bst; auto.
Qed.

Next Obligation. (* decr subset (l1,s2) *)
 simpl; omega.
Qed.

Next Obligation. (* post GT + left + left *)
 unfold Subset in *; intros.
 inv bst; intuition_in; order.
Qed.

Next Obligation. (* post GT + left + right *)
 unfold Subset in *; contradict H0; intros.
 inv bst; intuition_in; order.
Qed.

Next Obligation. (* post GT + right + _ *)
 clear Heq_anonymous.
 unfold Subset in *; contradict H; intros.
 assert (In a (Node l2 x2 r2 h2)) by (inv In; auto).
 inv bst; intuition_in; order.
Qed.

Next Obligation. (* well-founded *)
  auto with arith.
Defined.


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
 forall s s' : t, eq s s' -> L.eq (elements s) (elements s').
Proof.
 unfold eq, Equal, L.eq, L.Equal in |- *; intros.
 generalize (elements_in s a) (elements_in s' a).
 firstorder.
Qed.

Lemma L_eq_eq :
 forall s s' : t, L.eq (elements s) (elements s') -> eq s s'.
Proof.
 unfold eq, Equal, L.eq, L.Equal in |- *; intros.
 generalize (elements_in s a) (elements_in s' a).
 firstorder.
Qed.
Hint Resolve eq_L_eq L_eq_eq.

Definition lt (s1 s2 : t) : Prop := L.lt (elements s1) (elements s2).

Definition lt_trans (s s' s'' : t) (h : lt s s') 
  (h' : lt s' s'') : lt s s'' := L.lt_trans h h'.

Lemma lt_not_eq : forall s s' : t, bst s -> bst s' -> lt s s' -> ~ eq s s'.
Proof.
 unfold lt in |- *; intros; intro.
 apply L.lt_not_eq with (s := elements s) (s' := elements s'); auto.
Qed.

(** * A new comparison algorithm suggested by Xavier Leroy *)

(** ** Enumeration of the elements of a tree *)

Inductive enumeration :=
 | End : enumeration
 | More : elt -> tree -> enumeration -> enumeration.

(** [flatten_e e] returns the list of elements of [e] i.e. the list
    of elements actually compared *)
 
Fixpoint flatten_e (e : enumeration) : list elt := match e with
  | End => nil
  | More x t r => x :: elements t ++ flatten_e r
 end.

(** [sorted_e e] expresses that elements in the enumeration [e] are
    sorted, and that all trees in [e] are binary search trees. *)

Inductive In_e (x:elt) : enumeration -> Prop :=
  | InEHd1 :
      forall (y : elt) (s : tree) (e : enumeration),
      X.eq x y -> In_e x (More y s e)
  | InEHd2 :
      forall (y : elt) (s : tree) (e : enumeration),
      In x s -> In_e x (More y s e)
  | InETl :
      forall (y : elt) (s : tree) (e : enumeration),
      In_e x e -> In_e x (More y s e).

Inductive sorted_e : enumeration -> Prop :=
  | SortedEEnd : sorted_e End
  | SortedEMore :
      forall (x : elt) (s : tree) (e : enumeration),
      bst s ->
      (gt_tree x s) ->
      sorted_e e ->
      (forall y : elt, In_e y e -> X.lt x y) ->
      (forall y : elt,
       In y s -> forall z : elt, In_e z e -> X.lt y z) ->
      sorted_e (More x s e).

Hint Constructors In_e sorted_e.

Lemma elements_app :
 forall (s : tree) (acc : list elt), elements_aux acc s = elements s ++ acc.
Proof.
 simple induction s; simpl in |- *; intuition.
 rewrite H0.
 rewrite H.
 unfold elements; simpl.
 do 2 rewrite H.
 rewrite H0.
 repeat rewrite <- app_nil_end.
 repeat rewrite app_ass; auto.
Qed.

Lemma compare_flatten_1 :
 forall (t0 t2 : tree) (t1 : elt) (z : int) (l : list elt),
 elements t0 ++ t1 :: elements t2 ++ l =
 elements (Node t0 t1 t2 z) ++ l.
Proof.
 simpl in |- *; unfold elements in |- *; simpl in |- *; intuition.
 repeat rewrite elements_app.
 repeat rewrite <- app_nil_end.
 repeat rewrite app_ass; auto.
Qed.

(** key lemma for correctness *)

Lemma flatten_e_elements :
 forall (x : elt) (l r : tree) (z : int) (e : enumeration),
 elements l ++ flatten_e (More x r e) = elements (Node l x r z) ++ flatten_e e.
Proof.
 intros; simpl.
 apply compare_flatten_1.
Qed.

(** termination of [compare_aux] *)

Open Scope nat_scope.
 
Fixpoint measure_e_t (s : tree) : nat := match s with
  | Leaf => 0
  | Node l _ r _ => 1 + measure_e_t l + measure_e_t r
 end.

Fixpoint measure_e (e : enumeration) : nat := match e with
  | End => 0
  | More _ s r => 1 + measure_e_t s + measure_e r
 end.

(** [cons t e] adds the elements of tree [t] on the head of 
    enumeration [e]. *)

Fixpoint cons s e {struct s} : enumeration := 
 match s with 
  | Leaf => e
  | Node l x r h => cons l (More x r e)
 end.

Lemma cons_1 : forall s e, 
  bst s -> sorted_e e ->
  (forall (x y : elt), In x s -> In_e y e -> X.lt x y) ->
  sorted_e (cons s e) /\ 
  measure_e (cons s e) = measure_e_t s + measure_e e /\
  flatten_e (cons s e) = elements s ++ flatten_e e.
Proof.
 induction s; simpl; auto.
 clear IHs2; intros.
 inv bst.
 destruct (IHs1 (More t s2 e)); clear IHs1; intuition.
 inversion_clear H6; subst; auto; order.
 simpl in *; omega.
 rewrite H8.
 apply flatten_e_elements.
Qed.

Lemma l_eq_cons :
 forall (l1 l2 : list elt) (x y : elt),
 X.eq x y -> L.eq l1 l2 -> L.eq (x :: l1) (y :: l2).
Proof.
 unfold L.eq, L.Equal in |- *; intuition.
 inversion_clear H1; generalize (H0 a); clear H0; intuition.
 apply InA_eqA with x; eauto with *.
 inversion_clear H1; generalize (H0 a); clear H0; intuition.
 apply InA_eqA with y; eauto with *.
Qed.

Definition measure2 e := measure_e e#1 + measure_e e#2.

Obligation Tactic := 
 simpl ; intros ; destruct_exists ;  
 unfold measure2; simpl in *; 
 try match goal with c:forall e:_,Compare _ _ _ _ |- _ => clear c end;
 try match goal with a:_/\_|-_=>destruct a as (S1,S2) end; 
 try subst; simpl in *.

Program Fixpoint compare_aux 
 (e:enumeration*enumeration|sorted_e e#1 /\ sorted_e e#2)
 { measure (measure2 e) } : 
 Compare L.lt L.eq (flatten_e e#1) (flatten_e e#2) 
 :=
 match e with 
 | (End,End) => EQ _
 | (End,More _ _ _) => LT _ 
 | (More _ _ _, End) => GT _ 
 | (More x1 r1 e1, More x2 r2 e2) => 
       match X.compare x1 x2 with 
        | EQ _ => match compare_aux (cons r1 e1, cons r2 e2) with 
             | EQ _ => EQ _
             | LT _ => LT _
             | GT _ => GT _
             end
        | LT _ => LT _ 
        | GT _ => GT _ 
       end
 end.

Next Obligation. (* post End,End *)
 unfold L.eq, L.Equal; intuition.
Qed.

Next Obligation. (* post End,More *)
 simpl; auto.
Qed.

Next Obligation. (* post More,End *)
 simpl; auto.
Qed.

Next Obligation. (* pre compare_aux (cons r1 e1, cons r2 e2) *)
 inversion S1; inversion S2; subst.
  destruct (cons_1 r1 e1) as (H,_); auto.
  destruct (cons_1 r2 e2) as (H',_); auto.
Qed.

Next Obligation. (* decr compare_aux (cons r1 e1, cons r2 e2) *)
 inversion S1; inversion S2; subst.
 destruct (cons_1 r1 e1) as (_,(H,_)); auto.
 destruct (cons_1 r2 e2) as (_,(H0,_)); auto.
 rewrite H; rewrite H0; simpl; omega.
Qed.

Next Obligation. (* post compare_aux (cons r1 e1, cons r2 e2) = EQ *)
 clear Heq_anonymous0 Heq_anonymous compare_aux.
 subst; simpl in *.
 inversion S1; inversion S2; subst.
 destruct (cons_1 r1 e1) as (_,(_,H)); auto.
 destruct (cons_1 r2 e2) as (_,(_,H0)); auto.
 rewrite <- H; rewrite <- H0; simpl.
 apply l_eq_cons; auto.
Qed.

Next Obligation. (* post compare_aux (cons r1 e1, cons r2 e2) = LT *)
 clear Heq_anonymous0 Heq_anonymous compare_aux.
 subst; simpl in *.
 inversion S1; inversion S2; subst.
 destruct (cons_1 r1 e1) as (_,(_,H)); auto.
 destruct (cons_1 r2 e2) as (_,(_,H0)); auto.
 rewrite <- H; rewrite <- H0; simpl.
 apply L.lt_cons_eq; auto.
Qed.

Next Obligation. (* post compare_aux (cons r1 e1, cons r2 e2) = GT *)
 clear Heq_anonymous0 Heq_anonymous compare_aux.
 subst; simpl in *.
 inversion S1; inversion S2; subst.
 destruct (cons_1 r1 e1) as (_,(_,H)); auto.
 destruct (cons_1 r2 e2) as (_,(_,H0)); auto.
 rewrite <- H; rewrite <- H0; simpl.
 apply L.lt_cons_eq; auto.
Qed.

Next Obligation. (* post X.compare x1 x2 = LT *)
 simpl; auto.
Qed.

Next Obligation. (* post X.compare x1 x2 = GT *)
 simpl; auto.
Qed.

Next Obligation. (* well-founded *)
  auto with arith.
Defined.

Opaque compare_aux.

Program Definition compare (s1:t|bst s1)(s2:t|bst s2) : 
 Compare lt eq s1 s2 := 
 match compare_aux (cons s1 End, cons s2 End) with 
  | EQ _ => EQ _ 
  | LT _ => LT _ 
  | GT _ => GT _ 
 end.

Next Obligation. (* pre compare_aux *)
 destruct (cons_1 s1 End); auto; try inversion 2.
 destruct (cons_1 s2 End); auto; try inversion 2.
Qed.

Next Obligation. (* post EQ *)
 destruct (cons_1 s1 End) as (_,(_,H')); auto; try inversion 2.
 destruct (cons_1 s2 End) as (_,(_,H0')); auto; try inversion 2.
 simpl in *; rewrite <- app_nil_end in *.
 apply L_eq_eq; rewrite <- H0'; rewrite <- H'; auto.
Qed.

Next Obligation. (* post LT *)
 destruct (cons_1 s1 End) as (_,(_,H')); auto; try inversion 2.
 destruct (cons_1 s2 End) as (_,(_,H0')); auto; try inversion 2.
 simpl in *; rewrite <- app_nil_end in *.
 red; intros; rewrite <- H0'; rewrite <- H'; auto.
Qed.

Next Obligation. (* post GT *)
 destruct (cons_1 s1 End) as (_,(_,H')); auto; try inversion 2.
 destruct (cons_1 s2 End) as (_,(_,H0')); auto; try inversion 2.
 simpl in *; rewrite <- app_nil_end in *.
 red; intros; rewrite <- H0'; rewrite <- H'; auto.
Qed.

Transparent compare_aux.

Close Scope nat_scope.

(** * Equality test *)

Opaque compare.

Program Definition equal (s1:t|bst s1)(s2:t|bst s2) : bool := 
 match compare s1 s2 with 
  | EQ _ => true
  | LT _ => false 
  | GT _ => false 
 end.

Transparent compare.

Lemma equal_1 : forall s1 s2 (Hs1:bst s1)(Hs2:bst s2),  
 Equal s1 s2 -> equal (exist _ s1 Hs1) (exist _ s2 Hs2) = true.
Proof.
unfold equal; intros.
destruct_call compare; simpl in *; auto.
generalize (lt_not_eq _ _ Hs1 Hs2 l); auto.
assert (eq s2 s1) by (apply eq_sym; auto).
generalize (lt_not_eq _ _ Hs2 Hs1 l); auto.
Qed.

Lemma equal_2 : forall s1 s2 (Hs1:bst s1)(Hs2:bst s2),  
 equal (exist _ s1 Hs1) (exist _ s2 Hs2) = true -> Equal s1 s2.
Proof.
unfold equal; intros.
destruct_call compare; simpl in *; auto; discriminate.
Qed.

End Raw.

(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we 
   need to encapsulate everything into a type of balanced binary search trees. *)

Module IntMake (I:Int)(X: OrderedType) <: S with Module E := X.

 Module E := X.
 Module Raw := Raw I X. 

 Record bbst := Bbst {this :> Raw.t; is_bst : Raw.bst this; is_avl: Raw.avl this}.
 Definition t := bbst. 
 Definition elt := E.t.
 
 Definition In (x : elt) (s : t) : Prop := Raw.In x s.
 Definition Equal (s s':t) : Prop := forall a : elt, In a s <-> In a s'.
 Definition Subset (s s':t) : Prop := forall a : elt, In a s -> In a s'.
 Definition Empty (s:t) : Prop := forall a : elt, ~ In a s.
 Definition For_all (P : elt -> Prop) (s:t) : Prop := forall x, In x s -> P x.
 Definition Exists (P : elt -> Prop) (s:t) : Prop := exists x, In x s /\ P x.
  
 Lemma In_1 : forall (s:t)(x y:elt), E.eq x y -> In x s -> In y s. 
 Proof. intro s; exact (Raw.In_1 s). Qed.
 
 Definition mem (x:elt)(s:t) : bool := Raw.mem x s.

 Definition empty : t := Bbst _ Raw.empty_bst Raw.empty_avl.
 Definition is_empty (s:t) : bool := Raw.is_empty s.
 Definition singleton (x:elt) : t := Bbst _ (Raw.singleton_bst x) (Raw.singleton_avl x).
 Definition add (x:elt)(s:t) : t := 
   Bbst _ (Raw.add_bst s x (is_bst s) (is_avl s)) 
          (Raw.add_avl s x (is_avl s)). 
 Definition remove (x:elt)(s:t) : t := 
   Bbst _ (Raw.remove_bst s x (is_bst s) (is_avl s)) 
          (Raw.remove_avl s x (is_avl s)). 
 Definition inter (s s':t) : t := 
   Bbst _ (Raw.inter_bst _ _ (is_bst s) (is_avl s) (is_bst s') (is_avl s'))  
          (Raw.inter_avl _ _ (is_avl s) (is_avl s')).
 Definition diff (s s':t) : t := 
   Bbst _ (Raw.diff_bst _ _ (is_bst s) (is_avl s) (is_bst s') (is_avl s'))  
          (Raw.diff_avl _ _ (is_avl s) (is_avl s')).
 Definition elements (s:t) : list elt := Raw.elements s.
 Definition min_elt (s:t) : option elt := Raw.min_elt s.
 Definition max_elt (s:t) : option elt := Raw.max_elt s.
 Definition choose (s:t) : option elt := Raw.choose s.
 Definition fold (B : Type) (f : elt -> B -> B) (s:t) : B -> B := Raw.fold f s. 
 Definition cardinal (s:t) : nat := Raw.cardinal s.
 Definition filter (f : elt -> bool) (s:t) : t := 
   Bbst _ (Raw.filter_bst f _ (is_bst s) (is_avl s))
          (Raw.filter_avl f _ (is_avl s)). 
 Definition for_all (f : elt -> bool) (s:t) : bool := Raw.for_all f s.
 Definition exists_ (f : elt -> bool) (s:t) : bool := Raw.exists_ f s.
 Definition partition (f : elt -> bool) (s:t) : t * t :=
   let p := Raw.partition f s in
   (Bbst (fst p) (Raw.partition_bst_1 f _ (is_bst s) (is_avl s)) 
                 (Raw.partition_avl_1 f _ (is_avl s)),
    Bbst (snd p) (Raw.partition_bst_2 f _ (is_bst s) (is_avl s)) 
                 (Raw.partition_avl_2 f _ (is_avl s))).

 Opaque Raw.union Raw.subset Raw.compare.

 Obligation Tactic := simpl ; intros ; destruct_exists ; simpl in * ; try subst.

 Program Definition union (s s':t) : t :=
   Bbst (Raw.union (s.(this),s'.(this))) _ _.

 Next Obligation. destruct s; destruct s'; auto. Qed.
 Next Obligation. destruct_call Raw.union; simpl; tauto. Qed.
 Next Obligation. destruct_call Raw.union; simpl; tauto. Qed.

 Definition equal (s s':t) : bool := 
  Raw.equal (exist _ _ s.(is_bst)) (exist _ _ s'.(is_bst)).

 Program Definition subset (s s':t) : bool := 
  if Raw.subset (s.(this),s'.(this)) then true else false.

 Next Obligation. destruct s; destruct s'; auto. Qed.

 Definition eq (s s':t) : Prop := Raw.eq s s'.
 Definition lt (s s':t) : Prop := Raw.lt s s'.

 Program Definition compare (s s':t) : Compare lt eq s s' := 
  match Raw.compare (s:Raw.t) (s':Raw.t) with 
   | LT _ => LT _ 
   | EQ _ => EQ _ 
   | GT _ => GT _
  end.

 Next Obligation. destruct s; auto. Qed. 
 Next Obligation. destruct s'; auto. Qed.
 Next Obligation. auto. Qed.
 Next Obligation. auto. Qed.
 Next Obligation. auto. Qed. (* COUTEUX si compare_aux est transparent !! *)

 (* specs *)
 Section Specs. 
 Variable s s' s'': t. 
 Variable x y : elt.

 Hint Resolve is_bst is_avl.
 
 Lemma mem_1 : In x s -> mem x s = true. 
 Proof. exact (Raw.mem_1 s x (is_bst s)). Qed.
 Lemma mem_2 : mem x s = true -> In x s.
 Proof. exact (Raw.mem_2 s x). Qed.

 Lemma equal_1 : Equal s s' -> equal s s' = true.
 Proof. exact (Raw.equal_1 s s' (is_bst s) (is_bst s')). Qed.
 Lemma equal_2 : equal s s' = true -> Equal s s'.
 Proof. exact (Raw.equal_2 s s' (is_bst s) (is_bst s')). Qed.

 Lemma subset_1 : Subset s s' -> subset s s' = true.
 Proof. 
 unfold subset; destruct_call Raw.subset; simpl in *; intuition.
 Qed.

 Lemma subset_2 : subset s s' = true -> Subset s s'.
 Proof. 
 unfold subset; destruct_call Raw.subset; simpl in *; intuition discriminate.
 Qed.

 Lemma empty_1 : Empty empty.
 Proof. exact Raw.empty_1. Qed.

 Lemma is_empty_1 : Empty s -> is_empty s = true.
 Proof. exact (Raw.is_empty_1 s). Qed.
 Lemma is_empty_2 : is_empty s = true -> Empty s. 
 Proof. exact (Raw.is_empty_2 s). Qed.
 
 Lemma add_1 : E.eq x y -> In y (add x s).
 Proof. 
 unfold add, In; simpl; rewrite Raw.add_in; auto.
 Qed.

 Lemma add_2 : In y s -> In y (add x s).
 Proof.
 unfold add, In; simpl; rewrite Raw.add_in; auto.
 Qed.

 Lemma add_3 : ~ E.eq x y -> In y (add x s) -> In y s. 
 Proof. 
 unfold add, In; simpl; rewrite Raw.add_in; intuition auto with exfalso sets.
 Qed.

 Lemma remove_1 : E.eq x y -> ~ In y (remove x s).
 Proof. 
 unfold remove, In; simpl; rewrite Raw.remove_in; intuition.
 Qed.

 Lemma remove_2 : ~ E.eq x y -> In y s -> In y (remove x s).
 Proof. 
 unfold remove, In; simpl; rewrite Raw.remove_in; intuition.
 Qed.

 Lemma remove_3 : In y (remove x s) -> In y s.
 Proof. 
 unfold remove, In; simpl; rewrite Raw.remove_in; intuition.
 Qed.

 Lemma singleton_1 : In y (singleton x) -> E.eq x y. 
 Proof. exact (Raw.singleton_1 x y). Qed.
 Lemma singleton_2 : E.eq x y -> In y (singleton x). 
 Proof. exact (Raw.singleton_2 x y). Qed.

 Lemma union_1 : In x (union s s') -> In x s \/ In x s'.
 Proof.
 unfold union, In; simpl.
 destruct_call Raw.union; simpl in *.
 decompose [and] a.
 destruct (H2 x); auto.
 Qed.

 Lemma union_2 : In x s -> In x (union s s'). 
 Proof.
 unfold union, In; simpl.
 destruct_call Raw.union; simpl in *.
 decompose [and] a.
 destruct (H2 x); auto.
 Qed.

 Lemma union_3 : In x s' -> In x (union s s').
 Proof.
 unfold union, In; simpl.
 destruct_call Raw.union; simpl in *.
 decompose [and] a.
 destruct (H2 x); auto.
 Qed.

 Lemma inter_1 : In x (inter s s') -> In x s.
 Proof.
 unfold inter, In; simpl; rewrite Raw.inter_in; intuition.
 Qed.

 Lemma inter_2 : In x (inter s s') -> In x s'.
 Proof. 
 unfold inter, In; simpl; rewrite Raw.inter_in; intuition.
 Qed.

 Lemma inter_3 : In x s -> In x s' -> In x (inter s s').
 Proof. 
 unfold inter, In; simpl; rewrite Raw.inter_in; intuition.
 Qed.
 
 Lemma diff_1 : In x (diff s s') -> In x s. 
 Proof. 
 unfold diff, In; simpl; rewrite Raw.diff_in; intuition.
 Qed.

 Lemma diff_2 : In x (diff s s') -> ~ In x s'.
 Proof. 
 unfold diff, In; simpl; rewrite Raw.diff_in; intuition.
 Qed.

 Lemma diff_3 : In x s -> ~ In x s' -> In x (diff s s').
 Proof. 
 unfold diff, In; simpl; rewrite Raw.diff_in; intuition.
 Qed.
 
 Lemma fold_1 : forall (A : Type) (i : A) (f : elt -> A -> A),
      fold A f s i = fold_left (fun a e => f e a) (elements s) i.
 Proof. 
 unfold fold, elements; intros; apply Raw.fold_1; auto.
 Qed.

 Lemma cardinal_1 : cardinal s = length (elements s).
 Proof. 
 unfold cardinal, elements; intros; apply Raw.cardinal_elements_1; auto.
 Qed.

 Section Filter.
 Variable f : elt -> bool.

 Lemma filter_1 : compat_bool E.eq f -> In x (filter f s) -> In x s. 
 Proof. 
 intro; unfold filter, In; simpl; rewrite Raw.filter_in; intuition.
 Qed.

 Lemma filter_2 : compat_bool E.eq f -> In x (filter f s) -> f x = true. 
 Proof. 
 intro; unfold filter, In; simpl; rewrite Raw.filter_in; intuition.
 Qed.

 Lemma filter_3 : compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s).
 Proof. 
 intro; unfold filter, In; simpl; rewrite Raw.filter_in; intuition.
 Qed.

 Lemma for_all_1 : compat_bool E.eq f -> For_all (fun x => f x = true) s -> for_all f s = true.
 Proof. exact (Raw.for_all_1 f s). Qed.
 Lemma for_all_2 : compat_bool E.eq f -> for_all f s = true -> For_all (fun x => f x = true) s.
 Proof. exact (Raw.for_all_2 f s). Qed.

 Lemma exists_1 : compat_bool E.eq f -> Exists (fun x => f x = true) s -> exists_ f s = true.
 Proof. exact (Raw.exists_1 f s). Qed.
 Lemma exists_2 : compat_bool E.eq f -> exists_ f s = true -> Exists (fun x => f x = true) s.
 Proof. exact (Raw.exists_2 f s). Qed.

 Lemma partition_1 : compat_bool E.eq f -> 
  Equal (fst (partition f s)) (filter f s).
 Proof.
 unfold partition, filter, Equal, In; simpl ;intros H a.
 rewrite Raw.partition_in_1; auto.
 rewrite Raw.filter_in; intuition.
 Qed.

 Lemma partition_2 : compat_bool E.eq f -> 
  Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
 Proof.
 unfold partition, filter, Equal, In; simpl ;intros H a.
 rewrite Raw.partition_in_2; auto.
 rewrite Raw.filter_in; intuition.
 rewrite H2; auto.
 destruct (f a); auto.
 repeat red; intros; f_equal.
 rewrite (H _ _ H0); auto.
 Qed.

 End Filter.

 Lemma elements_1 : In x s -> InA E.eq x (elements s).
 Proof. 
 unfold elements, In; rewrite Raw.elements_in; auto.
 Qed.

 Lemma elements_2 : InA E.eq x (elements s) -> In x s.
 Proof. 
 unfold elements, In; rewrite Raw.elements_in; auto.
 Qed.

 Lemma elements_3 : sort E.lt (elements s).
 Proof. exact (Raw.elements_sort _ (is_bst s)). Qed.

 Lemma elements_3w : NoDupA E.eq (elements s).
 Proof. exact (Raw.elements_nodup _ (is_bst s)). Qed.

 Lemma min_elt_1 : min_elt s = Some x -> In x s. 
 Proof. exact (Raw.min_elt_1 s x). Qed.
 Lemma min_elt_2 : min_elt s = Some x -> In y s -> ~ E.lt y x.
 Proof. exact (Raw.min_elt_2 s x y (is_bst s)). Qed.
 Lemma min_elt_3 : min_elt s = None -> Empty s.
 Proof. exact (Raw.min_elt_3 s). Qed.

 Lemma max_elt_1 : max_elt s = Some x -> In x s. 
 Proof. exact (Raw.max_elt_1 s x). Qed.
 Lemma max_elt_2 : max_elt s = Some x -> In y s -> ~ E.lt x y.
 Proof. exact (Raw.max_elt_2 s x y (is_bst s)). Qed.
 Lemma max_elt_3 : max_elt s = None -> Empty s.
 Proof. exact (Raw.max_elt_3 s). Qed.

 Lemma choose_1 : choose s = Some x -> In x s.
 Proof. exact (Raw.choose_1 s x). Qed.
 Lemma choose_2 : choose s = None -> Empty s.
 Proof. exact (Raw.choose_2 s). Qed.
 Lemma choose_3 : choose s = Some x -> choose s' = Some y ->
  Equal s s' -> E.eq x y.
 Proof.
  exact (@Raw.choose_3 _ _ (is_bst s) (is_avl s) (is_bst s') (is_avl s') x y).
 Qed.

 Lemma eq_refl : eq s s. 
 Proof. exact (Raw.eq_refl s). Qed.
 Lemma eq_sym : eq s s' -> eq s' s.
 Proof. exact (Raw.eq_sym s s'). Qed.
 Lemma eq_trans : eq s s' -> eq s' s'' -> eq s s''.
 Proof. exact (Raw.eq_trans s s' s''). Qed.
  
 Lemma lt_trans : lt s s' -> lt s' s'' -> lt s s''.
 Proof. exact (Raw.lt_trans s s' s''). Qed.
 Lemma lt_not_eq : lt s s' -> ~eq s s'.
 Proof. exact (Raw.lt_not_eq _ _ (is_bst s) (is_bst s')). Qed.

 Transparent Raw.union Raw.subset Raw.compare.

 End Specs.

 Definition eq_dec : forall s s' : t, {eq s s'} + {~ eq s s'}.
 Proof.
   intros.
   case_eq (equal s s'); intro H; [left|right].
   apply equal_2; auto.
   intro H'; rewrite equal_1 in H; auto; discriminate.
 Defined.

End IntMake.

(* For concrete use inside Coq, we propose an instantiation of [Int] by [Z]. *)

Module Make (X: OrderedType) <: S with Module E := X
 :=IntMake(Z_as_Int)(X).


