
(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Finite map library.  *)

(* $Id$ *)

(** This module implements map using AVL trees.
    It follows the implementation from Ocaml's standard library. *)

Require Import FSetInterface.
Require Import FMapInterface.
Require Import FMapList.

Require Import ZArith.
Open Scope Z_scope.

Set Firstorder Depth 3.

(** First, we need a max-aware omega tactic. *)

Notation max := Zmax. 

Lemma max_spec : forall x y, 
  x >= y /\ max x y = x  \/
  x <= y /\ max x y = y.
Proof.
 intros; unfold max, Zle, Zge.
 destruct (Zcompare x y); [ left | right | left ]; split; auto; discriminate.
Qed.

Ltac omega_max := 
  let om x y := 
    generalize (max_spec x y); 
    let z := fresh "z" in let Hz := fresh "Hz" in 
    (set (z:=Zmax x y) in *; clearbody z; intro Hz)
  in 
  match goal with 
    | |- context id [ max ?x ?y ] => om x y; omega_max
    | H:context id [ max ?x ?y ] |- _ => om x y; omega_max
    | _ => intros; try omega
  end.

Ltac false_omega := elimtype False; omega.
Ltac false_omega_max := elimtype False; omega_max.



Module Raw (X: OrderedType).

Module E := X.
Module MX := OrderedTypeFacts X.
Module PX := PairOrderedType X.
Module L := FMapList.Raw X.
Import MX. 
Import PX.

Definition key := X.t.

(** * Trees *)

Section Elt.

Variable elt : Set.

(* Now in PairOrderedType:
Definition eqk (p p':key*elt) := X.eq (fst p) (fst p').
Definition eqke (p p':key*elt) := 
         X.eq (fst p) (fst p') /\ (snd p) = (snd p').
Definition ltk (p p':key*elt) := X.lt (fst p) (fst p').
*)

Notation eqk := (eqk (elt:= elt)).
Notation eqke := (eqke (elt:= elt)).
Notation ltk := (ltk (elt:= elt)).


Inductive tree  : Set :=
  | Leaf : tree
  | Node : tree -> key -> elt -> tree -> Z -> tree.

Notation t := tree.

(** The Fifth field of [Node] is the height of the tree *)

(** A tactic to repeat [inversion_clear] on all hyps of the 
    form [(f (Node _ _ _ _))] *)
Ltac inv f :=
  match goal with 
     | H:f Leaf |- _ => inversion_clear H; inv f
     | H:f _ Leaf |- _ => inversion_clear H; inv f
     | H:f _ _ Leaf |- _ => inversion_clear H; inv f
     | H:f (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | H:f _ _ (Node _ _ _ _ _) |- _ => inversion_clear H; inv f
     | _ => idtac
  end.

(** Same, but with a backup of the original hypothesis. *)

Ltac safe_inv f := match goal with 
  | H:f (Node _ _ _ _ _) |- _ => 
        generalize H; inversion_clear H; safe_inv f
  | _ => intros 
 end.

Ltac inv_all f := 
  match goal with 
   | H: f _ |- _ => inversion_clear H; inv f
   | H: f _ _ |- _ => inversion_clear H; inv f
   | H: f _ _ _ |- _ => inversion_clear H; inv f
   | _ => idtac
  end.

(** * Occurrence in a tree *)

Inductive MapsTo (x : key)(e : elt) : tree -> Prop :=
  | MapsRoot : forall l r h y,
      X.eq x y -> MapsTo x e (Node l y e r h)
  | MapsLeft : forall l r h y e', 
      MapsTo x e l -> MapsTo x e (Node l y e' r h)
  | MapsRight : forall l r h y e', 
      MapsTo x e r -> MapsTo x e (Node l y e' r h).
Hint Constructors MapsTo.

Inductive In (x : key) : tree -> Prop :=
  | InRoot : forall l r h y e,
      X.eq x y -> In x (Node l y e r h)
  | InLeft : forall l r h y e', 
      In x l -> In x (Node l y e' r h)
  | InRight : forall l r h y e', 
      In x r -> In x (Node l y e' r h).
Hint Constructors In.

Ltac intuition_in := repeat progress (intuition; inv In; inv MapsTo).
Ltac firstorder_in := repeat progress (firstorder; inv In; inv MapsTo).

Lemma MapsTo_In : forall k e m, MapsTo k e m -> In k m.
Proof.
 induction 1; auto.
Qed.
Hint Resolve MapsTo_In.

Lemma In_MapsTo : forall k m, In k m -> exists e, MapsTo k e m.
Proof.
 induction 1; try destruct IHIn as (e,He); exists e; auto.
Qed.

Definition In0 (k:key)(m:t) : Prop := exists e:elt, MapsTo k e m.

Lemma In_alt : forall k m, In0 k m <-> In k m.
Proof. 
 split.
 intros (e,H); eauto.
 exact (In_MapsTo k m).
Qed.

(** [MapsTo] is compatible with [X.eq] *)

Lemma MapsTo_1 :
 forall m x y e, X.eq x y -> MapsTo x e m -> MapsTo y e m.
Proof.
 induction m; simpl; intuition_in; eauto.
Qed.
Hint Immediate MapsTo_1.

Lemma In_1 : 
 forall m x y, X.eq x y -> In x m -> In y m.
Proof.
 intros m x y; induction m; simpl; intuition_in; eauto.
Qed.

(** * Binary search trees *)

(** [lt_tree x s]: all elements in [s] are smaller than [x] 
   (resp. greater for [gt_tree]) *)

Definition lt_tree x s := forall y:key, In y s -> X.lt y x.
Definition gt_tree x s := forall y:key, In y s -> X.lt x y.

Hint Unfold lt_tree gt_tree.

Ltac order := match goal with 
 | H: lt_tree ?x ?s, H1: In ?y ?s |- _ => generalize (H _ H1); clear H; order
 | H: gt_tree ?x ?s, H1: In ?y ?s |- _ => generalize (H _ H1); clear H; order
 | _ => MX.order
end.

(** Results about [lt_tree] and [gt_tree] *)

Lemma lt_leaf : forall x, lt_tree x Leaf.
Proof.
 unfold lt_tree in |- *; intros; intuition_in.
Qed.

Lemma gt_leaf : forall x, gt_tree x Leaf.
Proof.
  unfold gt_tree in |- *; intros; intuition_in.
Qed.

Lemma lt_tree_node : forall x y l r e h, 
 lt_tree x l -> lt_tree x r -> X.lt y x -> lt_tree x (Node l y e r h).
Proof.
 unfold lt_tree in *; firstorder_in; order.
Qed.

Lemma gt_tree_node : forall x y l r e h,
 gt_tree x l -> gt_tree x r -> X.lt x y -> gt_tree x (Node l y e r h).
Proof.
 unfold gt_tree in *; firstorder_in; order.
Qed.

Hint Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.

Lemma lt_left : forall x y l r e h, 
 lt_tree x (Node l y e r h) -> lt_tree x l.
Proof.
 intuition_in.
Qed.

Lemma lt_right : forall x y l r e h, 
 lt_tree x (Node l y e r h) -> lt_tree x r.
Proof.
 intuition_in.
Qed.

Lemma gt_left : forall x y l r e h, 
 gt_tree x (Node l y e r h) -> gt_tree x l.
Proof.
 intuition_in.
Qed.

Lemma gt_right : forall x y l r e h, 
 gt_tree x (Node l y e r h) -> gt_tree x r.
Proof.
 intuition_in.
Qed.

Hint Resolve lt_left lt_right gt_left gt_right.

Lemma lt_tree_not_in :
 forall (x : key) (t : tree), lt_tree x t -> ~ In x t.
Proof.
 intros; intro; generalize (H _ H0); order.
Qed.

Lemma lt_tree_trans :
 forall x y, X.lt x y -> forall t, lt_tree x t -> lt_tree y t.
Proof.
 firstorder eauto.
Qed.

Lemma gt_tree_not_in :
 forall (x : key) (t : tree), gt_tree x t -> ~ In x t.
Proof.
 intros; intro; generalize (H _ H0); order.
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
  | BSNode : forall x e l r h, 
      bst l -> bst r -> lt_tree x l -> gt_tree x r -> bst (Node l x e r h).

Hint Constructors bst.

(** * AVL trees *)

(** [avl s] : [s] is a properly balanced AVL tree,
    i.e. for any node the heights of the two children
    differ by at most 2 *)

Definition height (s : tree) : Z :=
  match s with
  | Leaf => 0
  | Node _ _ _ _ h => h
  end.

Inductive avl : tree -> Prop :=
  | RBLeaf : avl Leaf
  | RBNode : forall x e l r h, 
      avl l ->
      avl r ->
      -2 <= height l - height r <= 2 ->
      h = max (height l) (height r) + 1 -> 
      avl (Node l x e r h).

Hint Constructors avl.

(** Results about [avl] *)

Lemma avl_node : forall x e l r, 
 avl l ->
 avl r ->
 -2 <= height l - height r <= 2 ->
 avl (Node l x e r (max (height l) (height r) + 1)).
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
Implicit Arguments height_non_negative. 

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

(** * Empty map *)

Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

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
 unfold empty, Empty; intuition_in.
Qed.

(** * Emptyness test *)

Definition is_empty (s:t) := match s with Leaf => true | _ => false end.

Lemma is_empty_1 : forall s, Empty s -> is_empty s = true. 
Proof.
 destruct s as [|r x e l h]; simpl; auto.
 intro H; elim (H x e); auto.
Qed.

Lemma is_empty_2 : forall s, is_empty s = true -> Empty s.
Proof. 
 destruct s; simpl; intros; try discriminate; red; intuition_in.
Qed.

(** * Appartness *)

(** The [mem] function is deciding appartness. It exploits the [bst] property
    to achieve logarithmic complexity. *)

Fixpoint mem (x:key)(m:t) { struct m } : bool := 
   match m with 
     |  Leaf => false 
     |  Node l y e r _ => match X.compare x y with 
             | Lt _ => mem x l 
             | Eq _ => true
             | Gt _ => mem x r
         end
   end.

Lemma mem_1 : forall s x, bst s -> In x s -> mem x s = true.
Proof. 
 intros s x.
 functional induction mem x s; inversion_clear 1; auto.
 intuition_in.
 intuition_in; firstorder; absurd (X.lt x y); eauto. (* bug order ?! *)
 intuition_in; firstorder; absurd (X.lt y x); eauto.
Qed.

Lemma mem_2 : forall s x, mem x s = true -> In x s. 
Proof. 
 intros s x. 
 functional induction mem x s; firstorder; intros; try discriminate.
Qed.

Fixpoint find (x:key)(m:t) { struct m } : option elt := 
   match m with 
     |  Leaf => None 
     |  Node l y e r _ => match X.compare x y with 
             | Lt _ => find x l 
             | Eq _ => Some e
             | Gt _ => find x r
         end
   end.

Lemma find_1 : forall m x e, bst m -> MapsTo x e m -> find x m = Some e.
Proof. 
 intros m x e.
 functional induction find x m; inversion_clear 1; auto.
 intuition_in.
 intuition_in; firstorder; absurd (X.lt x y); eauto. (* bug order ?! *)
 intuition_in; auto.
  absurd (X.lt x y); eauto.
  absurd (X.lt y x); eauto.
 intuition_in; firstorder; absurd (X.lt y x); eauto.
Qed.

Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
Proof. 
 intros m x.
 functional induction find x m; firstorder; intros; try discriminate.
 inversion H; subst; auto.
Qed.

(** * Helper functions *)

(** [create l x r] creates a node, assuming [l] and [r]
    to be balanced and [|height l - height r| <= 2]. *)

Definition create l x e r := 
   Node l x e r (max (height l) (height r) + 1).

Lemma create_bst : 
 forall l x e r, bst l -> bst r -> lt_tree x l -> gt_tree x r -> 
 bst (create l x e r).
Proof.
 unfold create; auto.
Qed.
Hint Resolve create_bst.

Lemma create_avl : 
 forall l x e r, avl l -> avl r ->  -2 <= height l - height r <= 2 -> 
 avl (create l x e r).
Proof.
 unfold create; auto.
Qed.

Lemma create_height : 
 forall l x e r, avl l -> avl r ->  -2 <= height l - height r <= 2 -> 
 height (create l x e r) = max (height l) (height r) + 1.
Proof.
 unfold create; intros; auto.
Qed.

Lemma create_in : 
 forall l x e r y,  In y (create l x e r) <-> X.eq y x \/ In y l \/ In y r.
Proof.
 unfold create; split; [ inversion_clear 1 | ]; intuition.
Qed.

(** trick for emulating [assert false] in Coq *)

Definition assert_false := Leaf.

(** [bal l x e r] acts as [create], but performs one step of
    rebalancing if necessary, i.e. assumes [|height l - height r| <= 3]. *)

Definition bal l x e r := 
  let hl := height l in 
  let hr := height r in
  if Z_gt_le_dec hl (hr+2) then 
    match l with 
     | Leaf => assert_false
     | Node ll lx le lr _ => 
       if Z_ge_lt_dec (height ll) (height lr) then 
         create ll lx le (create lr x e r)
       else 
         match lr with 
          | Leaf => assert_false 
          | Node lrl lrx lre lrr _ => 
              create (create ll lx le lrl) lrx lre (create lrr x e r)
         end
    end
  else 
    if Z_gt_le_dec hr (hl+2) then 
      match r with
       | Leaf => assert_false
       | Node rl rx re rr _ =>
         if Z_ge_lt_dec (height rr) (height rl) then 
            create (create l x e rl) rx re rr
         else 
           match rl with
            | Leaf => assert_false
            | Node rll rlx rle rlr _ => 
                create (create l x e rll) rlx rle (create rlr rx re rr) 
           end
      end
    else 
      create l x e r. 

Ltac bal_tac := 
 intros l x e r;
 unfold bal; 
 destruct (Z_gt_le_dec (height l) (height r + 2)); 
   [ destruct l as [ |ll lx le lr lh]; 
     [ | destruct (Z_ge_lt_dec (height ll) (height lr)); 
          [ | destruct lr ]]
   | destruct (Z_gt_le_dec (height r) (height l + 2)); 
     [ destruct r as [ |rl rx re rr rh];
          [ | destruct (Z_ge_lt_dec (height rr) (height rl)); 
               [ | destruct rl ]]
     | ]]; intros.

Ltac bal_tac_imp := match goal with 
  | |- context id [ assert_false ] => 
      inv avl; avl_nns; simpl in *; false_omega
  | _ => idtac
end.

Lemma bal_bst : forall l x e r, bst l -> bst r -> 
 lt_tree x l -> gt_tree x r -> bst (bal l x e r).
Proof.
 (* intros l x r; functional induction bal l x r. MARCHE PAS !*) 
 bal_tac;
 inv bst; repeat apply create_bst; auto; unfold create; 
 apply lt_tree_node || apply gt_tree_node; auto; 
 eapply lt_tree_trans || eapply gt_tree_trans || eauto; eauto.
Qed.

Lemma bal_avl : forall l x e r, avl l -> avl r -> 
 -3 <= height l - height r <= 3 -> avl (bal l x e r).
Proof.
 bal_tac; inv avl; repeat apply create_avl; simpl in *; auto; omega_max.
Qed.

Lemma bal_height_1 : forall l x e r, avl l -> avl r -> 
 -3 <= height l - height r <= 3 ->
 0 <= height (bal l x e r) - max (height l) (height r) <= 1.
Proof.
 bal_tac; inv avl; avl_nns; simpl in *; omega_max.
Qed.

Lemma bal_height_2 : 
 forall l x e r, avl l -> avl r -> -2 <= height l - height r <= 2 -> 
 height (bal l x e r) = max (height l) (height r) +1.
Proof.
 bal_tac; inv avl; simpl in *; omega_max.
Qed.

Lemma bal_in : forall l x e r y, avl l -> avl r -> 
 (In y (bal l x e r) <-> X.eq y x \/ In y l \/ In y r).
Proof.
 bal_tac; bal_tac_imp; repeat rewrite create_in; intuition_in.
Qed.

Lemma bal_mapsto : forall l x e r y e', avl l -> avl r -> 
 (MapsTo y e' (bal l x e r) <-> MapsTo y e' (create l x e r)).
Proof.
 bal_tac; bal_tac_imp; unfold create; intuition_in.
Qed.

Ltac omega_bal := match goal with 
  | H:avl ?l, H':avl ?r |- context id [ bal ?l ?x ?e ?r ] => 
     generalize (bal_height_1 l x e r H H') (bal_height_2 l x e r H H'); 
     omega_max
  end. 

(** * Insertion *)

Fixpoint add (x:key)(e:elt)(s:t) { struct s } : t := match s with 
   | Leaf => Node Leaf x e Leaf 1
   | Node l y e' r h => 
      match X.compare x y with
         | Lt _ => bal (add x e l) y e' r
         | Eq _ => Node l y e r h
         | Gt _ => bal l y e' (add x e r)
      end
  end.

Lemma add_avl_1 :  forall m x e, avl m -> 
 avl (add x e m) /\ 0 <= height (add x e m) - height m <= 1.
Proof. 
 intros m x e; functional induction add x e m; intros; inv avl; simpl in *; 
  try solve [intuition].
 (* Lt *)
 destruct H; auto.
 split.
 apply bal_avl; auto; omega.
 omega_bal.
 (* Gt *)
 destruct H; auto.
 split.
 apply bal_avl; auto; omega.
 omega_bal.
Qed.

Lemma add_avl : forall m x e, avl m -> avl (add x e m).
Proof.
 intros; generalize (add_avl_1 m x e H); intuition.
Qed.
Hint Resolve add_avl.

Lemma add_in : forall m x y e, avl m -> 
 (In y (add x e m) <-> X.eq y x \/ In y m).
Proof.
 intros m x y e; functional induction add x e m; auto; intros.
 intuition_in.
 (* Lt *)
 inv avl.
 rewrite bal_in; auto.
 rewrite (H H1); intuition_in.
 (* Eq *)  
 inv avl.
 firstorder_in.
 eapply In_1; eauto.
 (* Gt *)
 inv avl.
 rewrite bal_in; auto.
 rewrite (H H2); intuition_in.
Qed.

Lemma add_bst : forall m x e, bst m -> avl m -> bst (add x e m).
Proof. 
 intros m x e; functional induction add x e m; 
   intros; inv bst; inv avl; auto; apply bal_bst; auto.
 (* lt_tree -> lt_tree (add ...) *)
 red; red in H4.
 intros.
 rewrite (add_in l x y0 e H0) in H1.
 intuition.
 eauto.
 (* gt_tree -> gt_tree (add ...) *)
 red; red in H4.
 intros.
 rewrite (add_in r x y0 e H6) in H1.
 intuition.
 apply MX.lt_eq with x; auto.
Qed.

Lemma add_1 : forall m x y e, avl m -> X.eq y x -> MapsTo y e (add x e m).
Proof. 
 intros m x y e; functional induction add x e m; 
   intros; inv bst; inv avl; try rewrite bal_mapsto; unfold create; eauto.
Qed. 

Lemma add_2 : forall m x y e e', avl m -> ~X.eq y x -> 
 MapsTo y e m -> MapsTo y e (add x e' m).
Proof.
 intros m x y e e'; functional induction add x e' m; 
   intros; inv bst; inv avl; try rewrite bal_mapsto; unfold create; auto; 
   inv MapsTo; auto.
 clear H_eq_0; order.
Qed.

Lemma add_3 : forall m x y e e', avl m -> ~X.eq y x -> 
 MapsTo y e (add x e' m) -> MapsTo y e m.
Proof.
 intros m x y e e'; functional induction add x e' m; intro; inv avl; 
  try rewrite bal_mapsto; auto; unfold create; intros; inv MapsTo; auto; 
  try clear H_eq_0; order. 
 (* BUG rewrite bal_mapsto in H2 *)
Qed.

(** * Extraction of minimum binding

  morally, [remove_min] is to be applied to a non-empty tree 
  [t = Node l x e r h]. Since we can't deal here with [assert false] 
  for [t=Leaf], we pre-unpack [t] (and forget about [h]). 
*)
 
Fixpoint remove_min (l:t)(x:key)(e:elt)(r:t) { struct l } : t*(key*elt) := 
  match l with 
    | Leaf => (r,(x,e))
    | Node ll lx le lr lh => let (l',m) := remove_min ll lx le lr in (bal l' x e r, m)
  end.

Lemma remove_min_avl_1 : forall l x e r h, avl (Node l x e r h) -> 
 avl (fst (remove_min l x e r)) /\ 
 0 <= height (Node l x e r h) - height (fst (remove_min l x e r)) <= 1.
Proof.
 intros l x e r; functional induction remove_min l x e r; simpl in *; intros.
 inv avl; simpl in *; split; auto.
 avl_nns; omega_max.
 (* l = Node *)
 inversion_clear H0.
 destruct (H lh); auto.
 split; simpl in *. 
 apply bal_avl; auto; omega_max.
 omega_bal.
Qed.

Lemma remove_min_avl : forall l x e r h, avl (Node l x e r h) -> 
    avl (fst (remove_min l x e r)). 
Proof.
 intros; generalize (remove_min_avl_1 l x e r h H); intuition.
Qed.

Lemma remove_min_in : forall l x e r h y, avl (Node l x e r h) -> 
 (In y (Node l x e r h) <-> 
  X.eq y (fst (snd (remove_min l x e r))) \/ In y (fst (remove_min l x e r))).
Proof.
 intros l x e r; functional induction remove_min l x e r; simpl in *; intros.
 intuition_in.
 (* l = Node *)
 inversion_clear H0.
 generalize (remove_min_avl ll lx le lr lh H1).
 rewrite H_eq_0; simpl; intros.
 rewrite bal_in; auto.
 generalize (H lh y H1).
 intuition.
 inversion_clear H8; intuition.
Qed.

Lemma remove_min_mapsto : forall l x e r h y e', avl (Node l x e r h) -> 
 (MapsTo y e' (Node l x e r h) <-> 
   ((X.eq y (fst (snd (remove_min l x e r))) /\ e' = (snd (snd (remove_min l x e r))))
    \/ MapsTo y e' (fst (remove_min l x e r)))).
Proof.
 intros l x e r; functional induction remove_min l x e r; simpl in *; intros.
 intuition_in; subst; auto.
 (* l = Node *)
 inversion_clear H0.
 generalize (remove_min_avl ll lx le lr lh H1).
 rewrite H_eq_0; simpl; intros.
 rewrite bal_mapsto; auto; unfold create.
 destruct (H lh y e').
 auto.
 intuition.
 inversion_clear H3; intuition.
 inversion_clear H10; intuition.
Qed.

Lemma remove_min_bst : forall l x e r h, 
 bst (Node l x e r h) -> avl (Node l x e r h) -> bst (fst (remove_min l x e r)).
Proof.
 intros l x e r; functional induction remove_min l x e r; simpl in *; intros.
 inv bst; auto.
 inversion_clear H0; inversion_clear H1.
 apply bal_bst; auto.
 firstorder.
 intro; intros.
 generalize (remove_min_in ll lx le lr lh y H0).
 rewrite H_eq_0; simpl.
 destruct 1.
 apply H4; intuition.
Qed.

Lemma remove_min_gt_tree : forall l x e r h, 
 bst (Node l x e r h) -> avl (Node l x e r h) -> 
 gt_tree (fst (snd (remove_min l x e r))) (fst (remove_min l x e r)).
Proof.
 intros l x e r; functional induction remove_min l x e r; simpl in *; intros.
 inv bst; auto.
 inversion_clear H0; inversion_clear H1.
 intro; intro.
 generalize (H lh H2 H0); clear H8 H7 H.
 generalize (remove_min_avl ll lx le lr lh H0).
 generalize (remove_min_in ll lx le lr lh (fst m) H0).
 rewrite H_eq_0; simpl; intros.
 rewrite (bal_in l' x e r y H7 H6) in H1.
 destruct H.
 firstorder.
 apply MX.lt_eq with x; auto.
 apply X.lt_trans with x; auto.
Qed.

(** * Merging two trees

  [merge t1 t2] builds the union of [t1] and [t2] assuming all elements
  of [t1] to be smaller than all elements of [t2], and
  [|height t1 - height t2| <= 2].
*)

Definition merge s1 s2 :=  match s1,s2 with 
  | Leaf, _ => s2 
  | _, Leaf => s1
  | _, Node l2 x2 e2 r2 h2 => 
        let (s2',m) := remove_min l2 x2 e2 r2 in 
        let (x,e) := m in 
        bal s1 x e s2'
end.

Lemma merge_avl_1 : forall s1 s2, avl s1 -> avl s2 -> 
 -2 <= height s1 - height s2 <= 2 -> 
 avl (merge s1 s2) /\ 
 0<= height (merge s1 s2) - max (height s1) (height s2) <=1.
Proof.
 intros s1 s2; functional induction merge s1 s2; simpl in *; intros.
 split; auto; avl_nns; omega_max.
 split; auto; avl_nns; simpl in *; omega_max.
 generalize (remove_min_avl_1 l2 x2 e2 r2 h2 H0).
 rewrite H_eq_1; simpl; destruct 1.
 rewrite H_eq_2; simpl.
 split.
 apply bal_avl; auto.
 simpl; omega_max.
 omega_bal.
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
 intros s1 s2; functional induction merge s1 s2; simpl in *; intros.
 intuition_in.
 intuition_in.
 rewrite H_eq_2; rewrite H_eq_2 in H_eq_1; clear H_eq_2.
 replace s2' with (fst (remove_min l2 x2 e2 r2)); [|rewrite H_eq_1; auto].
 rewrite bal_in; auto.
 generalize (remove_min_avl l2 x2 e2 r2 h2); rewrite H_eq_1; simpl; auto.
 generalize (remove_min_in l2 x2 e2 r2 h2 y); rewrite H_eq_1; simpl; intro.
 rewrite H3; intuition.
Qed.

Lemma merge_mapsto : forall s1 s2 y e, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
  (MapsTo y e (merge s1 s2) <-> MapsTo y e s1 \/ MapsTo y e s2).
Proof.
 intros s1 s2; functional induction merge s1 s2; simpl in *; intros.
 intuition_in.
 intuition_in.
 rewrite H_eq_2; rewrite H_eq_2 in H_eq_1; clear H_eq_2.
 replace s2' with (fst (remove_min l2 x2 e2 r2)); [|rewrite H_eq_1; auto].
 rewrite bal_mapsto; auto; unfold create.
 generalize (remove_min_avl l2 x2 e2 r2 h2); rewrite H_eq_1; simpl; auto.
 generalize (remove_min_mapsto l2 x2 e2 r2 h2 y e1); rewrite H_eq_1; simpl; intro.
 rewrite H3; intuition (try subst; auto).
 inversion_clear H4; intuition.
Qed.

Lemma merge_bst : forall s1 s2, bst s1 -> avl s1 -> bst s2 -> avl s2 -> 
 (forall y1 y2 : key, In y1 s1 -> In y2 s2 -> X.lt y1 y2) -> 
 bst (merge s1 s2). 
Proof.
 intros s1 s2; functional induction merge s1 s2; simpl in *; intros; auto.
 rewrite H_eq_2; rewrite H_eq_2 in H_eq_1; clear H_eq_2.
 apply bal_bst; auto.
 generalize (remove_min_bst l2 x2 e2 r2 h2); rewrite H_eq_1; simpl in *; auto.
 intro; intro.
 apply H3; auto.
 generalize (remove_min_in l2 x2 e2 r2 h2 x); rewrite H_eq_1; simpl; intuition.
 generalize (remove_min_gt_tree l2 x2 e2 r2 h2); rewrite H_eq_1; simpl; auto.
Qed. 

(** * Deletion *)

Fixpoint remove (x:key)(s:tree) { struct s } : t := match s with 
  | Leaf => Leaf
  | Node l y e r h =>
      match X.compare x y with
         | Lt _ => bal (remove x l) y e r
         | Eq _ => merge l r
         | Gt _ => bal l y e (remove x r)
      end
   end.

Lemma remove_avl_1 : forall s x, avl s -> 
 avl (remove x s) /\ 0 <= height s - height (remove x s) <= 1.
Proof.
 intros s x; functional induction remove x s; simpl; intros.
 intuition.
 (* Lt *)
 inv avl.
 destruct (H H1).
 split. 
 apply bal_avl; auto.
 omega_max.
 omega_bal.
 (* Eq *)
 inv avl. 
 generalize (merge_avl_1 l r H0 H1 H2).
 intuition omega_max.
 (* Gt *)
 inv avl.
 destruct (H H2).
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
 intros s x; functional induction remove x s; simpl; intros.
 intuition_in.
 (* Lt *)
 inv avl; inv bst; clear H_eq_0.
 rewrite bal_in; auto.
 generalize (H y0 H1); intuition; [ order | order | intuition_in ].
 (* Eq *)
 inv avl; inv bst; clear H_eq_0.
 rewrite merge_in; intuition; [ order | order | intuition_in ].
 elim H9; eauto.
 (* Gt *)
 inv avl; inv bst; clear H_eq_0.
 rewrite bal_in; auto.
 generalize (H y0 H6); intuition; [ order | order | intuition_in ].
Qed.

Lemma remove_bst : forall s x, bst s -> avl s -> bst (remove x s).
Proof. 
 intros s x; functional induction remove x s; simpl; intros.
 auto.
 (* Lt *)
 inv avl; inv bst.
 apply bal_bst; auto.
 intro; intro.
 rewrite (remove_in l x y0) in H0; auto.
 destruct H0; eauto.
 (* Eq *)
 inv avl; inv bst.
 apply merge_bst; eauto.
 (* Gt *) 
 inv avl; inv bst.
 apply bal_bst; auto.
 intro; intro.
 rewrite (remove_in r x y0) in H0; auto.
 destruct H0; eauto.
Qed.

Lemma remove_1 : forall m x y, bst m -> avl m -> X.eq y x -> ~ In y (remove x m).
Proof. 
 intros; rewrite remove_in; intuition.
Qed. 

Lemma remove_2 : forall m x y e, bst m -> avl m -> ~X.eq y x -> 
 MapsTo y e m -> MapsTo y e (remove x m).
Proof.
 intros m x y e; functional induction remove x m; 
   intros; inv bst; inv avl; try rewrite bal_mapsto; unfold create; auto; 
   try solve [inv MapsTo; auto].
 rewrite merge_mapsto; auto.
 inv MapsTo; auto.
 clear H_eq_0; order.
Qed.

Lemma remove_3 : forall m x y e, bst m -> avl m ->
 MapsTo y e (remove x m) -> MapsTo y e m.
Proof.
 intros m x y e; functional induction remove x m; intros Bs Av; inv avl; inv bst; 
  try rewrite bal_mapsto; auto; unfold create.
  intros; inv MapsTo; auto. 
  rewrite merge_mapsto; intuition.
  intros; inv MapsTo; auto.
Qed.

(** * Elements *)

(** [elements_tree_aux acc t] catenates the elements of [t] in infix
    order to the list [acc] *)

Fixpoint elements_aux (acc : list (key*elt)) (t : tree) {struct t} : list (key*elt) :=
  match t with
   | Leaf => acc
   | Node l x e r _ => elements_aux ((x,e) :: elements_aux acc r) l
  end.

(** then [elements] is an instanciation with an empty [acc] *)

Definition elements := elements_aux [].

Lemma elements_aux_mapsto : forall s acc x e, 
 InA eqke (x,e) (elements_aux acc s) <-> MapsTo x e s \/ InA eqke (x,e) acc.
Proof.
 induction s as [ | l Hl x e r Hr h ]; simpl; auto.
 intuition.
 inversion H0.
 intros.
 rewrite Hl.
 destruct (Hr acc x0 e0); clear Hl Hr.
 intuition; inversion_clear H3; intuition.
 destruct H0; simpl in *; subst; intuition.
Qed.

Lemma elements_mapsto : forall s x e, InA eqke (x,e) (elements s) <-> MapsTo x e s. 
Proof. 
 intros; generalize (elements_aux_mapsto s [] x e); intuition.
 inversion_clear H0.
Qed.

Lemma elements_in : forall s x, L.PX.In x (elements s) <-> In x s.
Proof.
 intros.
 unfold L.PX.In.
 rewrite <- In_alt; unfold In0.
 firstorder.
 exists x0.
 rewrite <- elements_mapsto; auto.
 exists x0.
 unfold L.PX.MapsTo; rewrite elements_mapsto; auto.
Qed.

Lemma elements_aux_sort : forall s acc, bst s -> sort ltk acc ->
 (forall x e y, InA eqke (x,e) acc -> In y s -> X.lt y x) ->
 sort ltk (elements_aux acc s).
Proof.
 induction s as [ | l Hl y e r Hr h]; simpl; intuition.
 inv bst.
 apply Hl; auto.
 constructor. 
 apply Hr; eauto.
 apply (InA_InfA (eqke_refl (elt:=elt))); intros (y',e') H6.
 destruct (elements_aux_mapsto r acc y' e'); intuition.
 red; simpl; eauto.
 red; simpl; eauto.
 intros.
 inversion_clear H.
 destruct H7; simpl in *.
 order.
 destruct (elements_aux_mapsto r acc x e0); intuition eauto.
Qed.

Lemma elements_sort : forall s : tree, bst s -> sort ltk (elements s).
Proof.
 intros; unfold elements; apply elements_aux_sort; auto.
 intros; inversion H0.
Qed.
Hint Resolve elements_sort.


(** * Fold *)

Fixpoint fold (A : Set) (f : key -> elt -> A -> A)(s : tree) {struct s} : A -> A := 
 fun a => match s with
  | Leaf => a
  | Node l x e r _ => fold A f r (f x e (fold A f l a))
 end.
Implicit Arguments fold [A].

Definition fold' (A : Set) (f : key -> elt -> A -> A)(s : tree) := 
  L.fold f (elements s).
Implicit Arguments fold' [A].

Lemma fold_equiv_aux :
 forall (A : Set) (s : tree) (f : key -> elt -> A -> A) (a : A) acc,
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
 forall (A : Set) (s : tree) (f : key -> elt -> A -> A) (a : A),
 fold f s a = fold' f s a.
Proof.
 unfold fold', elements in |- *. 
 simple induction s; simpl in |- *; auto; intros.
 rewrite fold_equiv_aux.
 rewrite H0.
 simpl in |- *; auto.
Qed.

Lemma fold_1 : 
 forall (s:t)(Hs:bst s)(A : Set)(f : key -> elt -> A -> A)(i : A),
 fold f s i = fold_left (fun a p => f (fst p) (snd p) a) (elements s) i.
Proof.
 intros.
 rewrite fold_equiv.
 unfold fold'.
 rewrite L.fold_1.
 unfold L.elements; auto.
Qed.

Definition Equal cmp m m' := 
  (forall k, In k m <-> In k m') /\ 
  (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).  

(** * Comparison *)

(** ** Enumeration of the elements of a tree *)

Inductive enumeration : Set :=
 | End : enumeration
 | More : key -> elt -> tree -> enumeration -> enumeration.

(** [flatten_e e] returns the list of elements of [e] i.e. the list
    of elements actually compared *)
 
Fixpoint flatten_e (e : enumeration) : list (key*elt) := match e with
  | End => []
  | More x e t r => (x,e) :: elements t ++ flatten_e r
 end.

(** [sorted_e e] expresses that elements in the enumeration [e] are
    sorted, and that all trees in [e] are binary search trees. *)

Inductive In_e (p:key*elt) : enumeration -> Prop :=
  | InEHd1 :
      forall (y : key)(d:elt) (s : tree) (e : enumeration),
      eqke p (y,d) -> In_e p (More y d s e)
  | InEHd2 :
      forall (y : key) (d:elt) (s : tree) (e : enumeration),
      MapsTo (fst p) (snd p) s -> In_e p (More y d s e)
  | InETl :
      forall (y : key) (d:elt) (s : tree) (e : enumeration),
      In_e p e -> In_e p (More y d s e).

Hint Constructors In_e.

Inductive sorted_e : enumeration -> Prop :=
  | SortedEEnd : sorted_e End
  | SortedEMore :
      forall (x : key) (d:elt) (s : tree) (e : enumeration),
      bst s ->
      (gt_tree x s) ->
      sorted_e e ->
      (forall p, In_e p e -> ltk (x,d) p) ->
      (forall p,
       MapsTo (fst p) (snd p) s -> forall q, In_e q e -> ltk p q) ->
      sorted_e (More x d s e).

Hint Constructors sorted_e.

Lemma in_flatten_e :
 forall p e, InA eqke p (flatten_e e) -> In_e p e.
Proof.
 simple induction e; simpl in |- *; intuition.
 inversion_clear H.
 inversion_clear H0; auto.
 elim (InA_app H1); auto.
 destruct (elements_mapsto t a b); auto.
Qed.

Lemma sorted_flatten_e :
 forall e : enumeration, sorted_e e -> sort ltk (flatten_e e).
Proof.
 simple induction e; simpl in |- *; intuition.
 apply cons_sort.
 apply (SortA_app (eqke_refl (elt:=elt))); inversion_clear H0; auto.
 intros; apply H5; auto.
 rewrite <- elements_mapsto; auto; destruct x; auto.
 apply in_flatten_e; auto.
 inversion_clear H0.
 apply In_InfA; intros.
 intros; elim (in_app_or _ _ _ H0); intuition.
 generalize (In_InA (eqke_refl (elt:=elt)) H6).
 destruct y; rewrite elements_mapsto; eauto.
 apply H4; apply in_flatten_e; auto.
 apply In_InA; auto.
Qed.

Lemma elements_app :
 forall s acc, elements_aux acc s = elements s ++ acc.
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
 forall t1 t2 x e z l,
 elements t1 ++ (x,e) :: elements t2 ++ l =
 elements (Node t1 x e t2 z) ++ l.
Proof.
 simpl in |- *; unfold elements in |- *; simpl in |- *; intuition.
 repeat rewrite elements_app.
 repeat rewrite <- app_nil_end.
 repeat rewrite app_ass; auto.
Qed.

(** key lemma for correctness *)

Lemma flatten_e_elements :
 forall l r x d z e,
 elements l ++ flatten_e (More x d r e) = 
 elements (Node l x d r z) ++ flatten_e e.
Proof.
 intros; simpl.
 apply compare_flatten_1.
Qed.

(** termination of [compare_aux] *)
 
Fixpoint measure_e_t (s : tree) : Z := match s with
  | Leaf => 0
  | Node l _ _ r _ => 1 + measure_e_t l + measure_e_t r
 end.

Fixpoint measure_e (e : enumeration) : Z := match e with
  | End => 0
  | More _ _ s r => 1 + measure_e_t s + measure_e r
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
 Measure_e; Measure_e_t_0 t; omega.
Qed.

Ltac Measure_e_0 e := generalize (measure_e_0 e); intro.

(** Induction principle over the sum of the measures for two lists *)

Definition compare_rec2 :
 forall P : enumeration -> enumeration -> Set,
  (forall x x' : enumeration,
   (forall y y' : enumeration,
    measure_e y + measure_e y' < measure_e x + measure_e x' -> P y y') ->
   P x x') -> 
 forall x x' : enumeration, P x x'.
Proof.
 intros P H x x'.
 apply well_founded_induction_type_2
 with (R := fun yy' xx' : enumeration * enumeration =>
            measure_e (fst yy') + measure_e (snd yy') <
            measure_e (fst xx') + measure_e (snd xx')); auto.    
 apply Wf_nat.well_founded_lt_compat
 with (f := fun xx' : enumeration * enumeration =>
            Zabs_nat (measure_e (fst xx') + measure_e (snd xx'))).
 intros; apply Zabs.Zabs_nat_lt.
 Measure_e_0 (fst x0); Measure_e_0 (snd x0); Measure_e_0 (fst y);
 Measure_e_0 (snd y); intros; omega.
Qed.

(** [cons t e] adds the elements of tree [t] on the head of 
    enumeration [e]. Code:
 
let rec cons s e = match s with
 | Empty -> e
 | Node(l, k, d, r, _) -> cons l (More(k, d, r, e))
*)

Definition cons : forall s e, bst s -> sorted_e e ->
  (forall x y, MapsTo (fst x) (snd x) s -> In_e y e -> ltk x y) ->
  { r : enumeration 
  | sorted_e r /\ 
    measure_e r = measure_e_t s + measure_e e /\
    flatten_e r = elements s ++ flatten_e e
  }.
Proof.
 simple induction s; intuition.
 (* s = Leaf *)
 exists e; intuition.
 (* s = Node t k e t0 z *)
 clear H0.
 case (H (More k e t0 e0)); clear H; intuition.
 inv bst; auto.
 constructor; inversion_clear H1; auto.
 inversion_clear H0; inv bst; intuition.
 destruct y; red; red in H4; simpl in *; intuition.
 apply lt_eq with k; eauto.
 destruct y; red; simpl in *; intuition.
 apply X.lt_trans with k; eauto.
 exists x; intuition.
 generalize H4; Measure_e; intros; Measure_e_t; omega.
 rewrite H5.
 apply flatten_e_elements.
Qed.

Lemma l_eq_cons :
 forall cmp l1 l2 x y, sort ltk (x::l1) -> sort ltk (y::l2) ->
 eqk x y -> cmp (snd x) (snd y) = true -> 
 (L.Equal cmp l1 l2 <-> L.Equal cmp (x :: l1) (y :: l2)).
Proof.
 unfold L.Equal in |- *; intros cmp l1 l2 (k,e) (k',e') S1 S2 H H0.
 compute in H, H0; intuition.
 (* -> *)
 destruct (In_inv H1).
 exists e'; eauto.
 destruct (H2 k0).
 destruct (H5 H4).
 exists x; auto.
 destruct (In_inv H1).
 exists e; eauto.
 destruct (H2 k0).
 destruct (H6 H4).
 exists x; auto.
 inversion_clear H4; inversion_clear H1.
 compute in H5, H4; destruct H5; destruct H4; subst; auto.
 compute in H5; destruct H5.
 generalize (Sort_In_cons_1 S1 (InA_eqke_eqk H4)).
 compute; order.
 compute in H4; destruct H4.
 generalize (Sort_In_cons_1 S2 (InA_eqke_eqk H5)).
 compute; order.
 eapply H3; eauto.
 (* <- *)
 assert (H4:=Sort_In_cons_3 S1 H1).
 destruct (H2 k0).
 destruct H5.
 destruct H1; exists x; eauto.
 inversion_clear H5.
 compute in H7; destruct H7; order.
 exists x; eauto. 
 assert (H4:=Sort_In_cons_3 S2 H1).
 destruct (H2 k0).
 destruct H6.
 destruct H1; exists x; eauto.
 inversion_clear H6.
 compute in H7; destruct H7; order.
 exists x; eauto. 
 apply (H3 k0); eauto.
Qed.

Definition equal_aux : 
 forall (cmp: elt -> elt -> bool)(e1 e2:enumeration), 
 sorted_e e1 -> sorted_e e2 -> 
 { L.Equal cmp (flatten_e e1) (flatten_e e2) } +
 { ~ L.Equal cmp (flatten_e e1) (flatten_e e2) }.
Proof.
 intros cmp e1 e2; pattern e1, e2 in |- *; apply compare_rec2.
 simple destruct x; simple destruct x'; intuition.
 (* x = x' = End *)
 left; unfold L.Equal in |- *; intuition.
 inversion H2.
 (* x = End x' = More *)
 right; simpl in |- *; auto.
 destruct 1.
 destruct (H2 k).
 destruct H5; auto.
 exists e; auto.
 inversion H5.
 (* x = More x' = End *)
 right; simpl in |- *; auto.
 destruct 1.
 destruct (H2 k).
 destruct H4; auto.
 exists e; auto.
 inversion H4.
 (* x = More k e t e0, x' = More k0 e3 t0 e4 *)
 case (X.compare k k0); intro.
 (* k < k0 *)
 right.
 destruct 1. 
 clear H3 H.
 assert (L.PX.In k (flatten_e (More k0 e3 t0 e4))).
  destruct (H2 k).
  apply H; simpl; exists e; auto.
 destruct H. 
 generalize (Sort_In_cons_2 (sorted_flatten_e _ H1) (InA_eqke_eqk H)).
 compute.
 intuition order. 
 (* k = k0 *)
 case_eq (cmp e e3).
 intros Eq.
 destruct (cons t e0) as [c1 (H2,(H3,H4))]; try inversion_clear H0; auto.
 destruct (cons t0 e4) as [c2 (H5,(H6,H7))]; try inversion_clear H1; auto.
 destruct (H c1 c2); clear H; intuition.
 Measure_e; omega.
 left.
 rewrite H4 in e6; rewrite H7 in e6.
 simpl; rewrite <- l_eq_cons; auto.
 apply (sorted_flatten_e _ H0).
 apply (sorted_flatten_e _ H1).
 right.
 simpl; rewrite <- l_eq_cons; auto.
 apply (sorted_flatten_e _ H0).
 apply (sorted_flatten_e _ H1).
 swap f.
 rewrite H4; rewrite H7; auto.
 right.
 destruct 1.
 rewrite (H4 k) in H2; try discriminate; simpl; auto.
 (* k > k0 *)
 right.
 destruct 1. 
 clear H3 H.
 assert (L.PX.In k0 (flatten_e (More k e t e0))).
  destruct (H2 k0).
  apply H3; simpl; exists e3; auto.
 destruct H. 
 generalize (Sort_In_cons_2 (sorted_flatten_e _ H0) (InA_eqke_eqk H)).
 compute.
 intuition order. 
Qed.

Lemma Equal_elements : forall cmp s s', 
 Equal cmp s s' <-> L.Equal cmp (elements s) (elements s').
Proof.
unfold Equal, L.Equal; split; split; intros.
do 2 rewrite elements_in; firstorder.
destruct H.
apply (H2 k); rewrite <- elements_mapsto; auto.
do 2 rewrite <- elements_in; firstorder.
destruct H.
apply (H2 k); unfold L.PX.MapsTo; rewrite elements_mapsto; auto.
Qed.

Definition equal : forall cmp s s', bst s -> bst s' -> 
  {Equal cmp s s'} + {~ Equal cmp s s'}.
Proof.
 intros cmp s1 s2 s1_bst s2_bst; simpl.
 destruct (cons s1 End); auto.
 inversion_clear 2.
 destruct (cons s2 End); auto.
 inversion_clear 2.
 simpl in a; rewrite <- app_nil_end in a.
 simpl in a0; rewrite <- app_nil_end in a0.
 destruct (equal_aux cmp x x0); intuition.
 left.
 rewrite H4 in e; rewrite H5 in e.
 rewrite Equal_elements; auto.
 right.
 swap n.
 rewrite H4; rewrite H5.
 rewrite <- Equal_elements; auto.
Qed.

(*** MANQUE ENCORE: map mapi map2 ***)

End Elt.
End Raw.
(*
(** * Encapsulation

   Now, in order to really provide a functor implementing [S], we 
   need to encapsulate everything into a type of balanced binary search trees. *)

Module Make (X: OrderedType) <: S with Module E := X.

 Module E := X.
 Module Raw := Raw X. 
 Import Raw.

 Record bbst : Set := Bbst {this :> t; is_bst : bst this; is_avl: avl this}.
 Definition t := bbst. 
 Definition key := X.t.
 
 Definition In (x : key) (s : t) := In x s.
 Definition Equal s s' := forall a : key, In a s <-> In a s'.
 Definition Subset s s' := forall a : key, In a s -> In a s'.
 Definition Add (x : key) (s s' : t) :=
   forall y : key, In y s' <-> X.eq y x \/ In y s.
 Definition Empty s := forall a : key, ~ In a s.
 Definition For_all (P : key -> Prop) (s : t) :=
   forall x : key, In x s -> P x.
 Definition Exists (P : key -> Prop) (s : t) := exists x : key, In x s /\ P x.

 Implicit Types s : t.
 Implicit Types x y : key.
  
 Definition In_1 s := In_1 s.
 
 Definition mem x s := mem x s.

 Definition empty := Bbst _ empty_bst empty_avl.
 Definition is_empty s := is_empty s.
 Definition singleton x := Bbst _ (singleton_bst x) (singleton_avl x).
 Definition add x s := 
   Bbst _ (add_bst s x (is_bst s) (is_avl s)) 
          (add_avl s x (is_avl s)). 
 Definition remove x s := 
   Bbst _ (remove_bst s x (is_bst s) (is_avl s)) 
          (remove_avl s x (is_avl s)). 
 Definition inter s s' := 
   Bbst _ (inter_bst _ _ (is_bst s) (is_avl s) (is_bst s') (is_avl s'))  
          (inter_avl _ _ (is_avl s) (is_avl s')).
 Definition diff s s' := 
   Bbst _ (diff_bst _ _ (is_bst s) (is_avl s) (is_bst s') (is_avl s'))  
          (diff_avl _ _ (is_avl s) (is_avl s')).
 Definition elements s := elements s.
 Definition min_key s := min_key s.
 Definition max_key s := max_key s.
 Definition choose s := choose s.
 Definition fold (B : Set) (f : key -> B -> B) s := fold f s. 
 Definition cardinal s := cardinal s.
 Definition filter (f : key -> bool) s := 
   Bbst _ (filter_bst f _ (is_bst s) (is_avl s))
          (filter_avl f _ (is_avl s)). 
 Definition for_all (f : key -> bool) s := for_all f s.
 Definition exists_ (f : key -> bool) s := exists_ f s.
 Definition partition (f : key -> bool) s :=
   let p := partition f s in
   (Bbst (fst p) (partition_bst_1 f _ (is_bst s) (is_avl s)) 
                 (partition_avl_1 f _ (is_avl s)),
    Bbst (snd p) (partition_bst_2 f _ (is_bst s) (is_avl s)) 
                 (partition_avl_2 f _ (is_avl s))).

 Definition union s s' :=
   let (u,p) := union _ _ (is_bst s) (is_avl s) (is_bst s') (is_avl s') in 
   let (b,p) := p in 
   let (a,_) := p in 
   Bbst u b a.

 Definition union' s s' := 
   Bbst _ (union'_bst _ _ (is_bst s) (is_avl s) (is_bst s') (is_avl s'))  
          (union'_avl _ _ (is_avl s) (is_avl s')).

 Definition equal s s':= if equal _ _ (is_bst s) (is_bst s') then true else false. 
 Definition equal' s s' := equal' s s'.

 Definition subset s s':= if subset _ _ (is_bst s) (is_bst s') then true else false.
 Definition subset' s s' := subset' s s'.

 Definition eq s s' := eq s s'.
 Definition lt s s' := lt s s'.

 Definition compare  s s' : Compare lt eq s s'.
 Proof.
 intros; elim (compare _ _ (is_bst s) (is_bst s'));
  [ constructor 1 | constructor 2 | constructor 3 ]; 
  auto. 
 Defined.

 (* specs *)
 Section Specs. 
 Variable s s' : t. 
 Variable x y : key.

 Hint Resolve is_bst is_avl.
 
 Definition mem_1 := mem_1 s x (is_bst s). 
 Definition mem_2 := mem_2 s x.

 Lemma equal_1 : Equal s s' -> equal s s' = true.
 Proof. 
 unfold equal; destruct (Raw.equal s s'); simpl; auto.
 Qed.

 Lemma equal_2 : equal s s' = true -> Equal s s'.
 Proof. 
 unfold equal; destruct (Raw.equal s s'); simpl; intuition; discriminate.
 Qed.

 Definition equal'_1 s s' :=
  equal'_1 _ _ (is_bst s) (is_avl s) (is_bst s') (is_avl s').
 Definition equal'_2 s s' :=
  equal'_2 _ _ (is_bst s) (is_avl s) (is_bst s') (is_avl s').

 Lemma subset_1 : Subset s s' -> subset s s' = true.
 Proof. 
 unfold subset; destruct (Raw.subset s s'); simpl; intuition.
 Qed.

 Lemma subset_2 : subset s s' = true -> Subset s s'.
 Proof. 
 unfold subset; destruct (Raw.subset s s'); simpl; intuition discriminate.
 Qed.

 Definition subset'_1 s s' := 
  subset'_1 _ _ (is_bst s) (is_avl s) (is_bst s') (is_avl s').
 Definition subset'_2 s s' := 
  subset'_2 _ _ (is_bst s) (is_avl s) (is_bst s') (is_avl s').

 Definition empty_1 : Empty empty := empty_1.

 Definition is_empty_1 : Empty s -> is_empty s = true  := is_empty_1 s.
 Definition is_empty_2 : is_empty s = true -> Empty s  := is_empty_2 s.
 
 Lemma add_1 : X.eq y x -> In y (add x s).
 Proof. 
 unfold add, In; simpl; rewrite add_in; auto.
 Qed.

 Lemma add_2 : In y s -> In y (add x s).
 Proof.
 unfold add, In; simpl; rewrite add_in; auto.
 Qed.

 Lemma add_3 : ~ X.eq x y -> In y (add x s) -> In y s. 
 Proof. 
 unfold add, In; simpl; rewrite add_in; intuition.
 elim H; auto.
 Qed.

 Lemma remove_1 : E.eq y x -> ~ In y (remove x s).
 Proof. 
 unfold remove, In; simpl; rewrite remove_in; intuition.
 Qed.

 Lemma remove_2 : ~ E.eq x y -> In y s -> In y (remove x s).
 Proof. 
 unfold remove, In; simpl; rewrite remove_in; intuition.
 Qed.

 Lemma remove_3 : In y (remove x s) -> In y s.
 Proof. 
 unfold remove, In; simpl; rewrite remove_in; intuition.
 Qed.

 Definition singleton_1 := singleton_1 x y.
 Definition singleton_2 := singleton_2 x y. 

 Lemma union_1 : In x (union s s') -> In x s \/ In x s'.
 Proof.
 unfold union, In; simpl.
 destruct (Raw.union s s' (is_bst s) (is_avl s) (is_bst s') (is_avl s')) 
  as (u,(b,(a,i))).
 simpl in *; rewrite i; auto.
 Qed.

 Lemma union_2 : In x s -> In x (union s s'). 
 Proof.
 unfold union, In; simpl.
 destruct (Raw.union s s' (is_bst s) (is_avl s) (is_bst s') (is_avl s')) 
  as (u,(b,(a,i))).
 simpl in *; rewrite i; auto.
 Qed.

 Lemma union_3 : In x s' -> In x (union s s').
 Proof.
 unfold union, In; simpl.
 destruct (Raw.union s s' (is_bst s) (is_avl s) (is_bst s') (is_avl s')) 
  as (u,(b,(a,i))).
 simpl in *; rewrite i; auto.
 Qed.

 Lemma union'_1 : In x (union' s s') -> In x s \/ In x s'.
 Proof.
 unfold union', In; simpl; rewrite union'_in; intuition.
 Qed.

 Lemma union'_2 : In x s -> In x (union' s s'). 
 Proof.
 unfold union', In; simpl; rewrite union'_in; intuition.
 Qed.

 Lemma union'_3 : In x s' -> In x (union' s s').
 Proof.
 unfold union', In; simpl; rewrite union'_in; intuition.
 Qed.

 Lemma inter_1 : In x (inter s s') -> In x s.
 Proof.
 unfold inter, In; simpl; rewrite inter_in; intuition.
 Qed.

 Lemma inter_2 : In x (inter s s') -> In x s'.
 Proof. 
 unfold inter, In; simpl; rewrite inter_in; intuition.
 Qed.

 Lemma inter_3 : In x s -> In x s' -> In x (inter s s').
 Proof. 
 unfold inter, In; simpl; rewrite inter_in; intuition.
 Qed.
 
 Lemma diff_1 : In x (diff s s') -> In x s. 
 Proof. 
 unfold diff, In; simpl; rewrite diff_in; intuition.
 Qed.

 Lemma diff_2 : In x (diff s s') -> ~ In x s'.
 Proof. 
 unfold diff, In; simpl; rewrite diff_in; intuition.
 Qed.

 Lemma diff_3 : In x s -> ~ In x s' -> In x (diff s s').
 Proof. 
 unfold diff, In; simpl; rewrite diff_in; intuition.
 Qed.
 
 Lemma fold_1 : forall (A : Set) (i : A) (f : key -> A -> A),
      fold A f s i = fold_left (fun a e => f e a) (elements s) i.
 Proof. 
 unfold fold, elements; intros; apply fold_1; auto.
 Qed.

 Lemma cardinal_1 : cardinal s = length (elements s).
 Proof. 
 unfold cardinal, elements; intros; apply cardinal_elements_1; auto.
 Qed.

 Section Filter.
 Variable f : key -> bool.

 Lemma filter_1 : compat_bool E.eq f -> In x (filter f s) -> In x s. 
 Proof. 
 intro; unfold filter, In; simpl; rewrite filter_in; intuition.
 Qed.

 Lemma filter_2 : compat_bool E.eq f -> In x (filter f s) -> f x = true. 
 Proof. 
 intro; unfold filter, In; simpl; rewrite filter_in; intuition.
 Qed.

 Lemma filter_3 : compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s).
 Proof. 
 intro; unfold filter, In; simpl; rewrite filter_in; intuition.
 Qed.

 Definition for_all_1 := for_all_1 f s.
 Definition for_all_2 := for_all_2 f s.

 Definition exists_1 := exists_1 f s.
 Definition exists_2 := exists_2 f s.

 Lemma partition_1 : compat_bool E.eq f -> 
  Equal (fst (partition f s)) (filter f s).
 Proof.
 unfold partition, filter, Equal, In; simpl ;intros H a.
 rewrite partition_in_1; auto.
 rewrite filter_in; intuition.
 Qed.

 Lemma partition_2 : compat_bool E.eq f -> 
  Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
 Proof.
 unfold partition, filter, Equal, In; simpl ;intros H a.
 rewrite partition_in_2; auto.
 rewrite filter_in; intuition.
 red; intros.
 f_equal; auto.
 destruct (f a); auto.
 destruct (f a); auto.
 Qed.

 End Filter.

 Lemma elements_1 : In x s -> InA E.eq x (elements s).
 Proof. 
 unfold elements, In; rewrite elements_in; auto.
 Qed.

 Lemma elements_2 : InA E.eq x (elements s) -> In x s.
 Proof. 
 unfold elements, In; rewrite elements_in; auto.
 Qed.

 Definition elements_3 : sort E.lt (elements s) := elements_sort _ (is_bst s).

 Definition min_key_1 := min_key_1 s x.
 Definition min_key_2 := min_key_2 s x y (is_bst s). 
 Definition min_key_3 := min_key_3 s.

 Definition max_key_1 := max_key_1 s x.
 Definition max_key_2 := max_key_2 s x y (is_bst s).
 Definition max_key_3 := max_key_3 s.

 Definition choose_1 := choose_1 s x.
 Definition choose_2 := choose_2 s.

 Definition eq_refl s := eq_refl s.
 Definition eq_sym s s' := eq_sym s s'.
 Definition eq_trans s s' s'' := eq_trans s s' s''.
  
 Definition lt_trans s s' s'' := lt_trans s s' s''.
 Definition lt_not_eq s s' := lt_not_eq _ _ (is_bst s) (is_bst s').

 End Specs.
End Make.

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
*)