(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** * MSetFullAVL : some complements to MSetAVL

   - Functor [AvlProofs] proves that trees of [MSetAVL] are not only
   binary search trees, but moreover well-balanced ones. This is done
   by proving that the operations in [MSetAVL.Ops] preserve the balancing.

   - We propose two functors [IntMake] and [Make] similar to the ones
   of [MSetAVL], except that the two invariants (bst and avl)
   are maintained instead of only the first one.

   - Functor [OcamlOps] contains variants of [union], [subset],
   [compare] and [equal] that are faithful to the original ocaml codes,
   while the versions in MSetAVL have been adapted to perform only
   structural recursive code.
*)

Require Import ZArith Int ROmega MSetInterface MSetAVL NPeano.

Module AvlProofs (Import I:Int)(X:OrderedType).
Include MSetAVL.MakeRaw I X.
Module Import II := MoreInt I.
Local Open Scope pair_scope.
Local Open Scope Int_scope.

Ltac omega_max := i2z_refl; romega with Z.
Ltac mysubst :=
 match goal with
   | E : _=_ |- _ => rewrite E in *; clear E; mysubst
   | _ => idtac
 end.

(** * AVL trees *)

(** [avl s] : [s] is a properly balanced AVL tree,
    i.e. for any node the heights of the two children
    differ by at most 2 *)

Inductive avl : tree -> Prop :=
  | RBLeaf : avl Leaf
  | RBNode : forall x l r h, avl l -> avl r ->
      -(2) <= height l - height r <= 2 ->
      h = max (height l) (height r) + 1 ->
      avl (Node h l x r).

Class Avl (t:tree) : Prop := mkAvl : avl t.

Instance avl_Avl s (Hs : avl s) : Avl s := Hs.

(** * Automation and dedicated tactics *)

Local Hint Constructors avl.

(** A tactic for cleaning hypothesis after use of functional induction. *)

Ltac clearf :=
 match goal with
  | H : (@Logic.eq (sumbool _ _) _ _) |- _ => clear H; clearf
  | H : (_ =? _) = true |- _ => rewrite II.eqb_eq in H; clearf
  | H : (_ <? _) = true |- _ => rewrite II.ltb_lt in H; clearf
  | H : (_ <=? _) = true |- _ => rewrite II.leb_le in H; clearf
  | H : (_ =? _) = false |- _ => rewrite II.eqb_neq in H; clearf
  | H : (_ <? _) = false |- _ => rewrite II.ltb_nlt in H; clearf
  | H : (_ <=? _) = false |- _ => rewrite II.leb_nle in H; clearf
  | _ => idtac
 end.

Ltac avl2Avl := change avl with Avl in *.
Ltac Avl2avl := change Avl with avl in *.
Ltac inv_avl := Avl2avl; invtree avl; avl2Avl.
(* Similar, but non-recursive *)
Ltac inv_avl' :=
  match goal with H : Avl (Node _ _ _ _) |- _ =>
    inversion_clear H; avl2Avl
  end.

(** Tactics about [avl] *)

Lemma height_non_negative : forall s `{Avl s}, height s >= 0.
Proof.
 induction s; simpl; intros; auto with zarith.
 inv_avl; intuition; omega_max.
Qed.

(** When [H:Avl r], typing [avl_nn H] adds [height r >= 0] *)

Ltac avl_nn H :=
  let nz := fresh "nz" in assert (nz := @height_non_negative _ H).

(* Repeat the previous tactic, clearing the [Avl _] hyps *)

Ltac avl_nns :=
  match goal with
     | H:Avl _ |- _ => avl_nn H; clear H; avl_nns
     | _ => idtac
  end.

(** Results about [height] *)

Lemma height_0 : forall s `{Avl s}, height s = 0 -> s = Leaf.
Proof.
 destruct 1; avl2Avl; intuition; simpl in *.
 avl_nns. simpl in *; exfalso; omega_max.
Qed.

(** Results about [avl] *)

Lemma avl_node :
 forall x l r `{Avl l, Avl r},
 -(2) <= height l - height r <= 2 ->
 Avl (Node (max (height l) (height r) + 1) l x r).
Proof.
  auto_tc.
Qed.
Hint Resolve avl_node.

(** * AVL trees have indeed logarithmic depth *)

Module LogDepth.

Local Open Scope nat_scope.

(** The minimal cardinal of an AVL tree of a given height.
    NB: this minimal cardinal is optimal, i.e. for any height,
    we could build an AVL tree of this cardinal. *)

Fixpoint mincard n :=
 match n with
 | O => O
 | 1 => 1
 | 2 => 2
 | S (S (S n) as p) => S (mincard n + mincard p)
 end.

(** First, some basic properties of [mincard] *)

Lemma mincard_eqn n :
 mincard (S (S (S n))) = S (mincard n + mincard (2+n)).
Proof.
 reflexivity.
Qed.

Lemma mincard_incr n : mincard n < mincard (S n).
Proof.
 induction n using lt_wf_ind.
 do 3 (destruct n; auto).
 rewrite 2 mincard_eqn.
 apply -> Nat.succ_lt_mono.
 apply Nat.add_lt_mono; eauto.
Qed.

Lemma mincard_lt_mono n m : n < m -> mincard n < mincard m.
Proof.
 induction m; inversion_clear 1.
 - apply mincard_incr.
 - transitivity (mincard m); auto using mincard_incr.
Qed.

Lemma mincard_le_mono n m : n <= m -> mincard n <= mincard m.
Proof.
 induction 1; auto.
 transitivity (mincard m); auto using mincard_incr with arith.
Qed.

Lemma mincard_bound n m : m <= 2+n ->
 mincard (S m) <= S (mincard n + mincard m).
Proof.
 intros H.
 destruct m as [|[|m]].
 - simpl. auto with arith.
 - simpl. auto with arith.
 - rewrite mincard_eqn.
   apply -> Nat.succ_le_mono.
   apply Nat.add_le_mono; eauto.
   apply mincard_le_mono; omega.
Qed.

(** [mincard] has an exponential behavior *)

Lemma mincard_twice n : 2 * mincard n < mincard (2+n).
Proof.
 induction n as [n IH] using lt_wf_ind.
 do 3 (destruct n; [simpl; auto with arith|]).
 change (2 + S (S (S n))) with (S (S (S (2+n)))).
 rewrite 2 mincard_eqn.
 generalize (IH n) (IH (2+n)). omega.
Qed.

Lemma mincard_even n : n<>0 -> 2^n <= mincard (2*n).
Proof.
 induction n.
 - now destruct 1.
 - intros _.
   destruct (Nat.eq_dec n 0).
   * subst; simpl; auto.
   * rewrite Nat.pow_succ_r', Nat.mul_succ_r, Nat.add_comm.
     transitivity (2 * mincard (2*n)).
     + apply Nat.mul_le_mono_l; auto.
     + apply Nat.lt_le_incl. apply mincard_twice.
Qed.

Lemma mincard_odd n : 2^n <= mincard (2*n+1).
Proof.
 destruct (Nat.eq_dec n 0).
 - subst; auto.
 - transitivity (mincard (2*n)).
   * now apply mincard_even.
   * apply mincard_le_mono. omega.
Qed.

Lemma mincard_log n : n <= 2 * Nat.log2 (mincard n) + 1.
Proof.
 rewrite (Nat.div2_odd n).
 set (m := Nat.div2 n); clearbody m.
 destruct (Nat.odd n); simpl Nat.b2n; rewrite ?Nat.add_0_r; clear n.
 + apply Nat.add_le_mono_r, Nat.mul_le_mono_l.
   apply Nat.log2_le_pow2.
   apply (mincard_lt_mono 0); auto with arith.
   apply mincard_odd.
 + destruct (Nat.eq_dec m 0); [subst; simpl; auto|].
   transitivity (2*Nat.log2 (mincard (2*m))); [|omega].
   apply Nat.mul_le_mono_l.
   apply Nat.log2_le_pow2.
   apply (mincard_lt_mono 0); omega.
   now apply mincard_even.
Qed.

(** We now prove that [mincard] gives indeed a lower bound
    of the cardinal of AVL trees. *)

Lemma maxdepth_heigth s : Avl s ->
 Z.of_nat (maxdepth s) = i2z (height s).
Proof.
 induction 1.
 simpl. omega_max.
 simpl maxdepth. simpl height. subst h.
 rewrite Nat2Z.inj_succ, Nat2Z.inj_max. omega_max.
Qed.

Lemma mincard_maxdepth s :
 Avl s -> mincard (maxdepth s) <= cardinal s.
Proof.
 induction 1.
 - simpl; auto.
 - simpl maxdepth. simpl cardinal. subst h.
   destruct (Nat.max_spec (maxdepth l) (maxdepth r)) as [(U,->)|(U,->)].
   * rewrite mincard_bound.
     apply -> Nat.succ_le_mono.
     apply Nat.add_le_mono; eauto.
     apply Nat2Z.inj_le. rewrite Nat2Z.inj_add.
     rewrite 2 maxdepth_heigth by auto. simpl Z.of_nat.
     i2z. omega.
   * rewrite Nat.add_comm, mincard_bound.
     apply -> Nat.succ_le_mono.
     apply Nat.add_le_mono; eauto.
     apply Nat2Z.inj_le. rewrite Nat2Z.inj_add.
     rewrite 2 maxdepth_heigth by auto. simpl Z.of_nat.
     i2z. omega.
Qed.

(** We can now prove that the depth of an AVL tree is
    logarithmic in its size. *)

Lemma maxdepth_upperbound s : Avl s ->
 maxdepth s <= 2 * Nat.log2 (cardinal s) + 1.
Proof.
 intros.
 transitivity (2 * Nat.log2 (mincard (maxdepth s)) + 1).
 apply mincard_log.
 apply Nat.add_le_mono_r, Nat.mul_le_mono_l, Nat.log2_le_mono.
 now apply mincard_maxdepth.
Qed.

Lemma maxdepth_lowerbound s : s<>Leaf ->
 Nat.log2 (cardinal s) < maxdepth s.
Proof.
 apply maxdepth_log_cardinal.
Qed.

End LogDepth.

(** * The AVL invariant is preserved by set operations *)

(** empty *)

Instance empty_avl : Avl empty.
Proof.
 auto_tc.
Qed.

(** singleton *)

Instance singleton_avl (x:elt) : Avl (singleton x).
Proof.
 unfold singleton. constructor; auto; simpl; omega_max.
Qed.

(** create *)

Lemma create_avl :
 forall l x r `{Avl l, Avl r},
   -(2) <= height l - height r <= 2 ->
   Avl (create l x r).
Proof.
 unfold create; auto.
Qed.

Lemma create_height :
 forall l x r `{Avl l, Avl r},
   -(2) <= height l - height r <= 2 ->
   height (create l x r) = max (height l) (height r) + 1.
Proof.
 unfold create; auto.
Qed.

(** bal *)

Ltac when f :=
 match goal with |- context [f] => idtac | _ => fail end.

Lemma bal_avl :
  forall l x r `{Avl l, Avl r},
    -(3) <= height l - height r <= 3 ->
    Avl (bal l x r).
Proof.
 intros l x r; functional induction bal l x r; intros; clearf;
 inv_avl; simpl in *; try (when assert_false; avl_nns);
 repeat apply create_avl; simpl in *; auto; omega_max.
Qed.

Lemma bal_height_1 :
  forall l x r `{Avl l, Avl r},
    -(3) <= height l - height r <= 3 ->
    0 <= height (bal l x r) - max (height l) (height r) <= 1.
Proof.
 intros l x r; functional induction bal l x r; intros; clearf;
 inv_avl; avl_nns; simpl in *; omega_max.
Qed.

Lemma bal_height_2 :
 forall l x r `{Avl l, Avl r},
   -(2) <= height l - height r <= 2 ->
   height (bal l x r) == max (height l) (height r) +1.
Proof.
 intros l x r; functional induction bal l x r; intros; clearf;
 inv_avl; simpl in *; omega_max.
Qed.

Ltac omega_bal := match goal with
  | _:Avl ?l, _:Avl ?r |- context [ bal ?l ?x ?r ] =>
     generalize (bal_height_1 l x r) (bal_height_2 l x r);
     omega_max
  end.

(** add *)

Lemma add_avl_1 : forall s x `{Avl s},
 Avl (add x s) /\ 0 <= height (add x s) - height s <= 1.
Proof.
 induct s x; inv_avl.
 - intuition; try constructor; simpl; auto; omega_max.
 - (* Eq *)
   simpl. intuition; omega_max.
 - (* Lt *)
   destruct (IHl x); trivial.
   split.
   * apply bal_avl; trivial; omega_max.
   * omega_bal.
 - (* Gt *)
   destruct (IHr x); trivial.
   split.
   * apply bal_avl; trivial; omega_max.
   * omega_bal.
Qed.

Instance add_avl s x `{Avl s} : Avl (add x s).
Proof.
 now destruct (add_avl_1 s x).
Qed.

(** join *)

Ltac remtree t s :=
 match t with Node ?h _ _ _ =>
  assert (height t = h) by trivial;
  set (s := t) in *; clearbody s
 end.

Lemma join_avl_1 : forall l x r `{Avl l, Avl r},
 Avl (join l x r) /\
 0<= height (join l x r) - max (height l) (height r) <= 1.
Proof.
 join_tac; clearf.

 - simpl. destruct (add_avl_1 r x). split; trivial.
   avl_nns; omega_max.

 - remtree (Node lh ll lx lr) l.
   split; auto_tc.
   destruct (add_avl_1 l x).
   simpl. avl_nns; omega_max.

 - remtree (Node rh rl rx rr) r.
   inv_avl.
   destruct (Hlr x r); trivial; clear Hrl Hlr.
   set (j := join lr x r) in *; clearbody j.
   simpl.
   assert (-(3) <= height ll - height j <= 3) by omega_max.
   split.
   * apply bal_avl; trivial.
   * omega_bal.

 - remtree (Node lh ll lx lr) l.
   inv_avl.
   destruct Hrl; trivial; clear Hlr.
   set (j := join l x rl) in *; clearbody j.
   simpl.
   assert (-(3) <= height j - height rr <= 3) by omega_max.
   split.
   * apply bal_avl; trivial.
   * omega_bal.

 - clear Hrl Hlr.
   remtree (Node lh ll lx lr) l.
   remtree (Node rh rl rx rr) r.
   assert (-(2) <= height l - height r <= 2) by omega_max.
   split.
   * apply create_avl; trivial.
   * rewrite create_height; trivial; omega_max.
Qed.

Instance join_avl l x r `{Avl l, Avl r} : Avl (join l x r).
Proof.
 now destruct (join_avl_1 l x r).
Qed.

(** remove_min *)

Lemma remove_min_avl_1 : forall l x r h `{Avl (Node h l x r)},
 Avl (remove_min l x r)#1 /\
 0 <= height (Node h l x r) - height (remove_min l x r)#1 <= 1.
Proof.
 intros l x r; functional induction (remove_min l x r);
 subst; simpl in *; intros.
 - inv_avl; simpl in *; split; auto. avl_nns; omega_max.
 - mysubst. inv_avl'; simpl in *.
   edestruct IHp; clear IHp; [eauto|].
   split.
   * apply bal_avl; trivial; omega_max.
   * omega_bal.
Qed.

Instance remove_min_avl l x r h `{Avl (Node h l x r)} :
  Avl (remove_min l x r)#1.
Proof.
 now destruct (remove_min_avl_1 l x r h).
Qed.

(** merge *)

Lemma merge_avl_1 : forall s1 s2 `{Avl s1, Avl s2},
 -(2) <= height s1 - height s2 <= 2 ->
 Avl (merge s1 s2) /\
 0<= height (merge s1 s2) - max (height s1) (height s2) <=1.
Proof.
 intros s1 s2; functional induction (merge s1 s2); intros;
 try (factornode s1).
 - simpl; split; auto; avl_nns; omega_max.
 - simpl; split; auto; avl_nns; simpl in *; omega_max.
 - generalize (@remove_min_avl_1 l2 x2 r2 _ _).
   mysubst. destruct 1; simpl in *.
   split.
   * apply bal_avl; trivial. simpl; omega_max.
   * omega_bal.
Qed.

Lemma merge_avl s1 s2 `{Avl s1, Avl s2} :
  -(2) <= height s1 - height s2 <= 2 -> Avl (merge s1 s2).
Proof.
 intros; now destruct (merge_avl_1 s1 s2).
Qed.


(** remove *)

Lemma remove_avl_1 : forall s x `{Avl s},
 Avl (remove x s) /\ 0 <= height s - height (remove x s) <= 1.
Proof.
 induct s x; inv_avl.
 - intuition; omega_max.
 - (* Eq *)
   generalize (merge_avl_1 l r).
   intuition omega_max.
 - (* Lt *)
   destruct (IHl x); trivial.
   split.
   * apply bal_avl; trivial; omega_max.
   * omega_bal.
 - (* Gt *)
   destruct (IHr x); trivial.
   split.
   * apply bal_avl; trivial; omega_max.
   * omega_bal.
Qed.

Instance remove_avl s x `{Avl s} : Avl (remove x s).
Proof.
 now destruct (remove_avl_1 s x).
Qed.

(** concat *)

Instance concat_avl s1 s2 `{Avl s1, Avl s2} : Avl (concat s1 s2).
Proof.
 functional induction (concat s1 s2); auto.
 apply join_avl; auto.
 generalize (remove_min_avl l2 x2 r2 _). now mysubst.
Qed.

(** split *)

Functional Scheme split_ind := Induction for split Sort Prop.

Lemma split_avl : forall s x `{Avl s},
  Avl (split x s)#l /\ Avl (split x s)#r.
Proof.
 intros s x. functional induction (split x s); simpl; auto.
 - intros. inv_avl; auto.
 - mysubst; simpl in *; inversion_clear 1; intuition.
 - mysubst; simpl in *; inversion_clear 1; intuition.
Qed.

(** inter *)

Ltac split_tac x1 :=
 let s2 := fresh "s2" in
 auto; factornode s2; generalize (split_avl s2 x1);
 mysubst; simpl; destruct 1; inv_avl; auto_tc.

Instance inter_avl s1 s2 `{Avl s1, Avl s2} : Avl (inter s1 s2).
Proof.
 functional induction inter s1 s2; split_tac x1.
Qed.

(** diff *)

Instance diff_avl s1 s2 `{Avl s1, Avl s2} : Avl (diff s1 s2).
Proof.
 functional induction diff s1 s2; split_tac x1.
Qed.

(** union *)

Instance union_avl s1 s2 `{Avl s1, Avl s2} : Avl (union s1 s2).
Proof.
 functional induction union s1 s2; split_tac x1.
Qed.

(** filter *)

Instance filter_avl f s `{Avl s} : Avl (filter f s).
Proof.
 induction s; simpl; auto. inv_avl. destruct (f _); auto_tc.
Qed.

(** partition *)

Instance partition_avl_1 f s `{Avl s} : Avl (partition f s)#1.
Proof.
 induction s; simpl; auto. inv_avl.
 destruct (partition f s1), (partition f s2), (f _); simpl; auto_tc.
Qed.

Instance partition_avl_2 f s `{Avl s} : Avl (partition f s)#2.
Proof.
 induction s; simpl; auto. inv_avl.
 destruct (partition f s1), (partition f s2), (f _); simpl; auto_tc.
Qed.

End AvlProofs.


(** * Encapsulation

   We can implement [S] with balanced binary search trees.
   When compared to [MSetAVL], we maintain here two invariants
   (bst and avl) instead of only bst, which is enough for fulfilling
   the MSet interface.
*)

Module IntMake (I:Int)(X: OrderedType) <: S with Module E := X.

 Module E := X.
 Module Import Raw := AvlProofs I X.

 Record t_ := Mkt
   { this :> tree;
     is_bst : Ok this;
     is_avl : Avl this }.
 Arguments Mkt this {is_bst} {is_avl}.

 Definition t := t_.
 Definition elt := E.t.

 Existing Instance is_bst.
 Existing Instance is_avl.

 (** Functions *)

 Definition mem (x:elt)(s:t) : bool := mem x s.
 Definition empty : t := Mkt empty.
 Definition is_empty (s:t) : bool := is_empty s.
 Definition singleton (x:elt) : t := Mkt (singleton x).
 Definition add (x:elt)(s:t) : t := Mkt (add x s).
 Definition remove (x:elt)(s:t) : t := Mkt (remove x s).
 Definition inter (s s':t) : t := Mkt (inter s s').
 Definition union (s s':t) : t := Mkt (union s s').
 Definition diff (s s':t) : t := Mkt (diff s s').
 Definition elements (s:t) : list elt := elements s.
 Definition min_elt (s:t) : option elt := min_elt s.
 Definition max_elt (s:t) : option elt := max_elt s.
 Definition choose (s:t) : option elt := choose s.
 Definition fold {B : Type} (f : elt -> B -> B) (s:t) : B -> B := fold f s.
 Definition cardinal (s:t) : nat := cardinal s.
 Definition filter (f : elt -> bool) (s:t) : t := Mkt (filter f s).
 Definition for_all (f : elt -> bool) (s:t) : bool := for_all f s.
 Definition exists_ (f : elt -> bool) (s:t) : bool := exists_ f s.
 Definition partition (f : elt -> bool) (s:t) : t * t :=
   let p := partition f s in (Mkt (fst p), Mkt (snd p)).

 Definition equal (s s':t) : bool := equal s s'.
 Definition subset (s s':t) : bool := subset s s'.

 Definition compare (s s':t) := compare s s'.

 (** Predicates *)

 Definition In (x : elt) (s : t) : Prop := In x s.
 Definition Equal (s s':t) : Prop := forall a : elt, In a s <-> In a s'.
 Definition Subset (s s':t) : Prop := forall a : elt, In a s -> In a s'.
 Definition Empty (s:t) : Prop := forall a : elt, ~ In a s.
 Definition For_all (P : elt -> Prop) (s:t) : Prop := forall x, In x s -> P x.
 Definition Exists (P : elt -> Prop) (s:t) : Prop := exists x, In x s /\ P x.

 Instance In_compat : Proper (E.eq==>Logic.eq==>iff) In.
 Proof. repeat red. intros; apply In_compat; congruence. Qed.

 Definition eq (s s':t) : Prop := Equal s s'.
 Definition lt (s s':t) : Prop := lt s s'.

 Instance eq_equiv : Equivalence eq.
 Proof. firstorder. Qed.

 Definition eq_dec : forall (s s':t), { eq s s' }+{ ~eq s s' }.
 Proof.
  intros (s,Bs,As) (s',Bs',As').
  change ({Raw.Equal s s'}+{~Raw.Equal s s'}).
  destruct (Raw.equal s s') as [ ]_eqn:H; [left|right];
   rewrite <- equal_spec; congruence.
 Defined.

 Instance lt_strorder : StrictOrder lt.
 Proof. constructor ; unfold lt; red.
   unfold complement. red. intros. apply (irreflexivity H).
   intros. transitivity y; auto.
 Qed.

 Instance lt_compat : Proper (eq==>eq==>iff) lt.
 Proof.
 repeat red. unfold eq, lt.
 intros (s1,B1,A1) (s2,B2,A2) E (s1',B1',A1') (s2',B2',A2') E'; simpl.
 change (Raw.eq s1 s2) in E.
 change (Raw.eq s1' s2') in E'.
 rewrite E,E'; intuition.
 Qed.

 (* Specs *)

 Section Specs.
 Variable s s' s'': t.
 Variable x y : elt.
 Variable f : elt -> bool.
 Notation compatb := (Proper (E.eq==>Logic.eq)) (only parsing).

 Lemma mem_spec : mem x s = true <-> In x s.
 Proof. exact (@mem_spec _ _ _). Qed.
 Lemma equal_spec : equal s s' = true <-> Equal s s'.
 Proof. exact (@equal_spec _ _ _ _). Qed.
 Lemma subset_spec : subset s s' = true <-> Subset s s'.
 Proof. exact (@subset_spec _ _ _ _). Qed.
 Lemma empty_spec : Empty empty.
 Proof. exact empty_spec. Qed.
 Lemma is_empty_spec : is_empty s = true <-> Empty s.
 Proof. exact (@is_empty_spec _). Qed.
 Lemma add_spec : In y (add x s) <-> E.eq y x \/ In y s.
 Proof. exact (@add_spec _ _ _ _). Qed.
 Lemma remove_spec : In y (remove x s) <-> In y s /\ ~E.eq y x.
 Proof. exact (@remove_spec _ _ _ _). Qed.
 Lemma singleton_spec : In y (singleton x) <-> E.eq y x.
 Proof. exact (@singleton_spec _ _). Qed.
 Lemma union_spec : In x (union s s') <-> In x s \/ In x s'.
 Proof. exact (@union_spec _ _ _ _ _). Qed.
 Lemma inter_spec : In x (inter s s') <-> In x s /\ In x s'.
 Proof. exact (@inter_spec _ _ _ _ _). Qed.
 Lemma diff_spec : In x (diff s s') <-> In x s /\ ~In x s'.
 Proof. exact (@diff_spec _ _ _ _ _). Qed.
 Lemma fold_spec : forall (A : Type) (i : A) (f : elt -> A -> A),
     fold f s i = fold_left (fun a e => f e a) (elements s) i.
 Proof. exact (@fold_spec _). Qed.
 Lemma cardinal_spec : cardinal s = length (elements s).
 Proof. exact (@cardinal_spec s _). Qed.
 Lemma filter_spec : compatb f ->
   (In x (filter f s) <-> In x s /\ f x = true).
 Proof. exact (@filter_spec _ _ _). Qed.
 Lemma for_all_spec : compatb f ->
   (for_all f s = true <-> For_all (fun x => f x = true) s).
 Proof. exact (@for_all_spec _ _). Qed.
 Lemma exists_spec : compatb f ->
   (exists_ f s = true <-> Exists (fun x => f x = true) s).
 Proof. exact (@exists_spec _ _). Qed.
 Lemma partition_spec1 : compatb f -> Equal (fst (partition f s)) (filter f s).
 Proof. exact (@partition_spec1 _ _). Qed.
 Lemma partition_spec2 : compatb f ->
   Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
 Proof. exact (@partition_spec2 _ _). Qed.
 Lemma elements_spec1 : InA E.eq x (elements s) <-> In x s.
 Proof. exact (@elements_spec1 _ _). Qed.
 Lemma elements_spec2w : NoDupA E.eq (elements s).
 Proof. exact (@elements_spec2w _ _). Qed.
 Lemma choose_spec1 : choose s = Some x -> In x s.
 Proof. exact (@choose_spec1 _ _). Qed.
 Lemma choose_spec2 : choose s = None -> Empty s.
 Proof. exact (@choose_spec2 _). Qed.

 Lemma compare_spec : CompSpec eq lt s s' (compare s s').
 Proof. unfold compare; destruct (@compare_spec s s' _ _); auto. Qed.
 Lemma elements_spec2 : sort X.lt (elements s).
 Proof. exact (@elements_spec2 _ _). Qed.
 Lemma min_elt_spec1 : min_elt s = Some x -> In x s.
 Proof. exact (@min_elt_spec1 _ _). Qed.
 Lemma min_elt_spec2 : min_elt s = Some x -> In y s -> ~ X.lt y x.
 Proof. exact (@min_elt_spec2 _ _ _ _). Qed.
 Lemma min_elt_spec3 : min_elt s = None -> Empty s.
 Proof. exact (@min_elt_spec3 _). Qed.
 Lemma max_elt_spec1 : max_elt s = Some x -> In x s.
 Proof. exact (@max_elt_spec1 _ _). Qed.
 Lemma max_elt_spec2 : max_elt s = Some x -> In y s -> ~ X.lt x y.
 Proof. exact (@max_elt_spec2 _ _ _ _). Qed.
 Lemma max_elt_spec3 : max_elt s = None -> Empty s.
 Proof. exact (@max_elt_spec3 _). Qed.
 Lemma choose_spec3 :
    choose s = Some x -> choose s' = Some y -> Equal s s' -> X.eq x y.
  Proof. exact (@choose_spec3 _ _ _ _ _ _). Qed.

End Specs.
End IntMake.

(* For concrete use inside Coq, we propose an instantiation of [Int] by [Z]. *)

Module Make (X: OrderedType) <: S with Module E := X
 :=IntMake(Z_as_Int)(X).



Require Import Recdef.

Module OcamlOps (Import I:Int)(X:OrderedType).
Module Import Raw := AvlProofs I X.
Import II.
Local Open Scope pair_scope.
Local Open Scope nat_scope.
Local Hint Resolve MX.eq_refl MX.eq_trans MX.lt_trans @ok.
Local Hint Immediate MX.eq_sym.
Local Hint Unfold In lt_tree gt_tree.
Local Hint Constructors InT bst.
Local Hint Unfold Ok.
Local Hint Resolve lt_leaf gt_leaf lt_tree_node gt_tree_node.

Ltac avl_nn' h :=
  let t := type of h in
  match type of t with
   | Prop => avl_nn h
   | _ => match goal with H : Avl h |- _ => avl_nn H end
  end.

(** Properties of cardinal *)

Lemma bal_cardinal : forall l x r,
 cardinal (bal l x r) = S (cardinal l + cardinal r).
Proof.
 intros l x r; functional induction bal l x r; intros; clearf;
 simpl; auto with arith; romega with *.
Qed.

Lemma add_cardinal : forall x s,
 cardinal (add x s) <= S (cardinal s).
Proof.
 induct s x; simpl; auto with arith;
 rewrite bal_cardinal; romega with *.
Qed.

Lemma join_cardinal : forall l x r,
 cardinal (join l x r) <= S (cardinal l + cardinal r).
Proof.
 join_tac; clearf; auto with arith.
 - simpl; apply add_cardinal.
 - simpl; destruct X.compare; simpl.
   * auto with arith.
   * generalize (bal_cardinal (add x ll) lx lr) (add_cardinal x ll);
     romega with *.
   * generalize (bal_cardinal ll lx (add x lr)) (add_cardinal x lr);
     romega with *.
 - generalize (bal_cardinal ll lx (join lr x (Node rh rl rx rr)))
  (Hlr x (Node rh rl rx rr)); simpl; romega with *.
 - simpl (S _) in *; generalize (bal_cardinal (join (Node lh ll lx lr) x rl) rx rr).
   romega with *.
Qed.

Lemma split_cardinal_1 : forall x s,
 (cardinal (split x s)#l <= cardinal s)%nat.
Proof.
 intros x s; functional induction split x s; simpl; auto.
 - romega with *.
 - rewrite e1 in IHt0; simpl in *.
   romega with *.
 - rewrite e1 in IHt0; simpl in *.
   generalize (@join_cardinal l y rl); romega with *.
Qed.

Lemma split_cardinal_2 : forall x s,
 (cardinal (split x s)#r <= cardinal s)%nat.
Proof.
 intros x s; functional induction split x s; simpl; auto.
 - romega with *.
 - rewrite e1 in IHt0; simpl in *.
   generalize (@join_cardinal rl y r); romega with *.
 - rewrite e1 in IHt0; simpl in *; romega with *.
Qed.

(** * [ocaml_union], an union faithful to the original ocaml code *)

Definition cardinal2 (s:t*t) := (cardinal s#1 + cardinal s#2)%nat.

Ltac ocaml_union_tac :=
 intros; unfold cardinal2; simpl fst in *; simpl snd in *;
 match goal with H: split ?x ?s = _ |- _ =>
  generalize (split_cardinal_1 x s) (split_cardinal_2 x s);
  rewrite H; simpl; romega with *
 end.

Function ocaml_union (s : t * t) { measure cardinal2 s } : t  :=
 match s with
  | (Leaf, Leaf) => s#2
  | (Leaf, Node _ _ _ _) => s#2
  | (Node _ _ _ _, Leaf) => s#1
  | (Node h1 l1 x1 r1, Node h2 l2 x2 r2) =>
        if ge_lt_dec h1 h2 then
          if eq_dec h2 1%I then add x2 s#1 else
          let (l2',_,r2') := split x1 s#2 in
             join (ocaml_union (l1,l2')) x1 (ocaml_union (r1,r2'))
        else
          if eq_dec h1 1%I then add x1 s#2 else
          let (l1',_,r1') := split x2 s#1 in
             join (ocaml_union (l1',l2)) x2 (ocaml_union (r1',r2))
 end.
Proof.
abstract ocaml_union_tac.
abstract ocaml_union_tac.
abstract ocaml_union_tac.
abstract ocaml_union_tac.
Defined.

Lemma ocaml_union_in : forall s y,
 Ok s#1 -> Avl s#1 -> Ok s#2 -> Avl s#2 ->
 (InT y (ocaml_union s) <-> InT y s#1 \/ InT y s#2).
Proof.
 intros s; functional induction ocaml_union s; intros y B1 A1 B2 A2;
  simpl (@fst) in *; simpl (@snd) in *; try clear e0 e1.
 - intuition_in.
 - intuition_in. 
 - intuition_in. 
 - (* add x2 s#1 *)
   inv_avl.
   rewrite (height_0 l2) by (avl_nn' l2; omega_max).
   rewrite (height_0 r2) by (avl_nn' r2; omega_max).
   rewrite add_spec; intuition_in.
 - (* join (union (l1,l2')) x1 (union (r1,r2')) *)
   clear _x _x0. factornode s2.
   generalize
    (split_avl s2 x1) (@split_ok s2 x1 B2)
    (@split_spec1 s2 x1 y B2) (@split_spec2 s2 x1 y B2).
   rewrite e2; simpl.
   destruct 1; destruct 1; inv_avl; invtree Ok.
   rewrite join_spec, IHt0, IHt1; auto.
   do 2 (intro Eq; rewrite Eq; clear Eq).
   destruct (X.compare_spec y x1); intuition_in.
 - (* add x1 s#2 *)
   inv_avl.
   rewrite (height_0 l1) by (avl_nn' l1; omega_max).
   rewrite (height_0 r1) by (avl_nn' r1; omega_max).
   rewrite add_spec; auto; intuition_in.
 - (* join (union (l1',l2)) x1 (union (r1',r2)) *)
   clear _x _x0. factornode s1.
   generalize
    (split_avl s1 x2) (@split_ok s1 x2 B1)
    (@split_spec1 s1 x2 y B1) (@split_spec2 s1 x2 y B1).
   rewrite e2; simpl.
   destruct 1; destruct 1; inv_avl; invtree Ok.
   rewrite join_spec, IHt0, IHt1; auto.
   do 2 (intro Eq; rewrite Eq; clear Eq).
   destruct (X.compare_spec y x2); intuition_in.
Qed.

Lemma ocaml_union_bst : forall s,
 Ok s#1 -> Avl s#1 -> Ok s#2 -> Avl s#2 -> Ok (ocaml_union s).
Proof.
 intros s; functional induction ocaml_union s; intros B1 A1 B2 A2;
  simpl @fst in *; simpl @snd in *; try clear e0 e1;
  try apply add_ok; auto.
 - (* join (union (l1,l2')) x1 (union (r1,r2')) *)
 clear _x _x0; factornode s2.
 generalize (split_avl s2 x1) (@split_ok _ x1 B2)
  (@split_spec1 s2 x1)(@split_spec2 s2 x1).
 rewrite e2; simpl.
 destruct 1; destruct 1; intros.
 invtree Ok; inv_avl.
 apply join_ok; auto.
 intro y; rewrite ocaml_union_in, H3; intuition_in.
 intro y; rewrite ocaml_union_in, H4; intuition_in.
 - (* join (union (l1',l2)) x1 (union (r1',r2)) *)
 clear _x _x0; factornode s1.
 generalize (split_avl s1 x2) (@split_ok _ x2 B1)
  (@split_spec1 s1 x2)(@split_spec2 s1 x2).
 rewrite e2; simpl.
 destruct 1; destruct 1; intros.
 invtree Ok; inv_avl.
 apply join_ok; auto.
 intro y; rewrite ocaml_union_in, H3; intuition_in.
 intro y; rewrite ocaml_union_in, H4; intuition_in.
Qed.

Lemma ocaml_union_avl : forall s,
 Avl s#1 -> Avl s#2 -> Avl (ocaml_union s).
Proof.
 intros s; functional induction ocaml_union s;
  simpl @fst in *; simpl @snd in *; auto_tc.
 intros A1 A2; generalize (@split_avl _ x1 A2); rewrite e2; simpl.
 inv_avl; destruct 1; auto_tc.
 intros A1 A2; generalize (@split_avl _ x2 A1); rewrite e2; simpl.
 inv_avl; destruct 1; auto_tc.
Qed.

Lemma ocaml_union_alt : forall s, Ok s#1 -> Avl s#1 -> Ok s#2 -> Avl s#2 ->
 Equal (ocaml_union s) (union s#1 s#2).
Proof.
 red; intros; rewrite ocaml_union_in, union_spec; simpl; intuition.
Qed.


(** * [ocaml_subset], a subset faithful to the original ocaml code *)

Function ocaml_subset (s:t*t) { measure cardinal2 s } : bool :=
 match s with
  | (Leaf, _) => true
  | (Node _ _ _ _, Leaf) => false
  | (Node _ l1 x1 r1, Node _ l2 x2 r2) =>
     match X.compare x1 x2 with
      | Eq => ocaml_subset (l1,l2) && ocaml_subset (r1,r2)
      | Lt => ocaml_subset (Node 0%I l1 x1 Leaf, l2) && ocaml_subset (r1,s#2)
      | Gt => ocaml_subset (Node 0%I Leaf x1 r1, r2) && ocaml_subset (l1,s#2)
     end
 end.

Proof.
 intros; unfold cardinal2; simpl; abstract romega with *.
 intros; unfold cardinal2; simpl; abstract romega with *.
 intros; unfold cardinal2; simpl; abstract romega with *.
 intros; unfold cardinal2; simpl; abstract romega with *.
 intros; unfold cardinal2; simpl; abstract romega with *.
 intros; unfold cardinal2; simpl; abstract romega with *.
Defined.

Ltac ocaml_subset_tac :=
 simpl in *; invtree Ok; rewrite andb_true_iff;
 match goal with _ : X.compare ?x1 ?x2 = _ |- _ =>
  destruct (X.compare_spec x1 x2); try discriminate
 end;
 repeat
  (match goal with H : context [ocaml_subset] |- _ => rewrite H; clear H end);
 unfold Subset; intuition_in;
 match goal with
  | H : forall a, InT a _ -> InT a ?s |- InT ?a _ =>
    assert (InT a s) by auto; intuition_in; order
  | _ => apply IsRoot; order
 end.

Lemma ocaml_subset_12 : forall s,
 Ok s#1 -> Ok s#2 ->
 (ocaml_subset s = true <-> Subset s#1 s#2).
Proof.
 intros s; functional induction ocaml_subset s; simpl; intros B1 B2.
 - intuition.
   red; auto; inversion 1.
 - split; intros; try discriminate.
   assert (H': In _x1 Leaf) by auto; inversion H'.
 - ocaml_subset_tac.
 - ocaml_subset_tac.
 - ocaml_subset_tac.
Qed.

Lemma ocaml_subset_alt : forall s, Ok s#1 -> Ok s#2 ->
 ocaml_subset s = subset s#1 s#2.
Proof.
 intros.
 generalize (ocaml_subset_12 _ H H0). rewrite <- subset_spec by auto.
 destruct ocaml_subset; destruct subset; intuition.
Qed.



(** [ocaml_compare], a compare faithful to the original ocaml code *)

(** termination of [compare_aux] *)

Fixpoint cardinal_e e := match e with
  | End => 0
  | More _ s r => S (cardinal s + cardinal_e r)
 end.

Lemma cons_cardinal_e : forall s e,
 cardinal_e (cons s e) = cardinal s + cardinal_e e.
Proof.
 induction s; simpl; intros; auto.
 rewrite IHs1; simpl; rewrite <- plus_n_Sm; auto with arith.
Qed.

Definition cardinal_e_2 e := cardinal_e e#1 + cardinal_e e#2.

Function ocaml_compare_aux
 (e:enumeration*enumeration) { measure cardinal_e_2 e } : comparison :=
 match e with
 | (End,End) => Eq
 | (End,More _ _ _) => Lt
 | (More _ _ _, End) => Gt
 | (More x1 r1 e1, More x2 r2 e2) =>
       match X.compare x1 x2 with
        | Eq => ocaml_compare_aux (cons r1 e1, cons r2 e2)
        | Lt => Lt
        | Gt => Gt
       end
 end.

Proof.
intros; unfold cardinal_e_2; simpl;
abstract (do 2 rewrite cons_cardinal_e; romega with * ).
Defined.

Definition ocaml_compare s1 s2 :=
 ocaml_compare_aux (cons s1 End, cons s2 End).

Local Hint Constructors L.lt_list.

Lemma ocaml_compare_aux_Cmp : forall e,
 Cmp (ocaml_compare_aux e) (flatten_e e#1) (flatten_e e#2).
Proof.
 intros e; functional induction ocaml_compare_aux e; simpl; intros;
  try constructor; auto;
  try destruct (X.compare_spec x1 x2); try discriminate; auto.
 reflexivity.
 apply L.cons_CompSpec; trivial. now rewrite <- !cons_1.
Qed.

Lemma ocaml_compare_Cmp : forall s1 s2,
 Cmp (ocaml_compare s1 s2) (elements s1) (elements s2).
Proof.
 unfold ocaml_compare; intros.
 assert (H1:=cons_1 s1 End).
 assert (H2:=cons_1 s2 End).
 simpl in *; rewrite <- app_nil_end in *; rewrite <-H1,<-H2.
 apply (@ocaml_compare_aux_Cmp (cons s1 End, cons s2 End)).
Qed.

Lemma ocaml_compare_alt : forall s1 s2, Ok s1 -> Ok s2 ->
 ocaml_compare s1 s2 = compare s1 s2.
Proof.
 intros s1 s2 B1 B2.
 generalize (ocaml_compare_Cmp s1 s2)(compare_Cmp s1 s2).
 destruct ocaml_compare; destruct compare; auto; intros; exfalso;
 inversion_clear H; inversion_clear H0; rewrite <- ?eq_Leq in *;
 repeat match goal with
  | H : L.lt (elements ?s1) (elements ?s2) |- _ =>
    assert (lt s1 s2) by (exists s1; exists s2; intuition); clear H
 end.
 rewrite H1 in H0. now apply StrictOrder_Irreflexive with s2.
 rewrite H1 in H0. now apply StrictOrder_Irreflexive with s2.
 rewrite H in H0. now apply StrictOrder_Irreflexive with s2.
 apply StrictOrder_Irreflexive with s2. now transitivity s1.
 rewrite H in H0. now apply StrictOrder_Irreflexive with s2.
 apply StrictOrder_Irreflexive with s2. now transitivity s1.
Qed.


(** * Equality test *)

Definition ocaml_equal s1 s2 : bool :=
 match ocaml_compare s1 s2 with
  | Eq => true
  | _ => false
 end.

Lemma ocaml_equal_alt : forall s1 s2, Ok s1 -> Ok s2 ->
 ocaml_equal s1 s2 = equal s1 s2.
Proof.
intros; unfold ocaml_equal, equal; rewrite ocaml_compare_alt; auto.
Qed.

Lemma ocaml_equal_1 : forall s1 s2, Ok s1 -> Ok s2 ->
 Equal s1 s2 -> ocaml_equal s1 s2 = true.
Proof.
intros. rewrite ocaml_equal_alt; trivial. now apply equal_spec.
Qed.

Lemma ocaml_equal_2 : forall s1 s2,
 ocaml_equal s1 s2 = true -> Equal s1 s2.
Proof.
unfold ocaml_equal; intros s1 s2 E.
generalize (ocaml_compare_Cmp s1 s2);
 destruct ocaml_compare; auto; try discriminate.
inversion 1. now apply eq_Leq.
Qed.

End OcamlOps.
