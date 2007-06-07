Require Import FSets ZArith EqNat UsualFacts MapFunction.
Set Implicit Arguments.

(* Sets of positive numbers *)
Module PS := FSetList.Make Positive_as_OT.
(* Sets of sets of positive numbers *)
Module PSS := FSetList.Make PS.
(* adding a map function to PSS... *)
Module PSS' := MapFunction.MapFunction PSS.



(** Computing the set of all subsets of a particular set [s] *)

Definition powerset s := 
  PS.fold 
   (fun (x:PS.elt)(ss:PSS.t) => PSS.union ss (PSS'.map (PS.add x) ss)) 
   s 
   (PSS.singleton PS.empty).



(** An example: *)

Open Scope positive_scope.

(* The set containing numbers 1..n *)
Fixpoint interval (n:nat) {struct n} : PS.t := match n with 
 | O => PS.empty
 | S n => PS.add (P_of_succ_nat n) (interval n)
 end.

Eval vm_compute in PS.elements (interval 10).

Definition powerset_5 := powerset (interval 5).

Eval vm_compute in map PS.elements (PSS.elements powerset_5).

Definition subsets_size2_in5 := 
 PSS.filter (fun s => beq_nat (PS.cardinal s) 2) powerset_5.

Eval vm_compute in map PS.elements (PSS.elements subsets_size2_in5).



(** Proofs about powerset *)

Module U := UsualFacts.UsualFacts Positive_as_OT PS.
Module F := U.MF.
Module P := U.MP.
Module PP := FSetProperties.Properties PSS.
Module FF := PP.FM.
Module Fold := UsualFacts.FoldEquiv Positive_as_OT PS.

Lemma powerset_is_powerset: 
 forall s s', PS.Subset s' s <-> PSS.In s' (powerset s).
Proof.
intros.
unfold powerset.
rewrite <- Fold.fold_direct_1.
remember (PS.cardinal s) as n.
revert s s' Heqn.
induction n; simpl; intros.

rewrite FF.singleton_iff.
unfold PSS.E.eq.
change (PS.Subset s' s <-> PS.Equal PS.empty s').
generalize (P.cardinal_inv_1 (sym_eq Heqn)).
intros.
unfold PS.Subset, PS.Equal, PS.Empty in *; intuition.
rewrite F.empty_iff in *; intuition.
rewrite F.empty_iff in *; intuition eauto.
generalize (H0 a); rewrite F.empty_iff in *; intuition.

case_eq (PS.max_elt s); intros.
rewrite FF.union_iff.
assert (S (PS.cardinal (PS.remove e s)) = S n).
 rewrite Heqn.
 apply P.remove_cardinal_1; auto.
 apply PS.max_elt_1; auto.
injection H0; clear H0; intros.
rewrite <- IHn; auto.

rewrite PSS'.map_In.
intros; apply F.add_m; auto.
case_eq (PS.mem e s'); intros.
split; intros.
right.
exists (PS.remove e s').
rewrite <- IHn; auto.
split.
red; intros a; F.set_iff.
generalize (H2 a); intuition.
change PSS.E.eq with PS.Equal.
red; intros a; F.set_iff.
rewrite <- F.mem_iff in H1.
destruct (F.ME.eq_dec e a); intuition.
compute in H4; subst e; auto.
destruct H2.
red; intros a; generalize (H2 a); F.set_iff; intuition.
destruct H2 as (b,(H2,H3)).
rewrite <- IHn in H2; auto.
rewrite <- F.mem_iff in H1.
assert (PS.Subset (PS.add e b) s).
 apply P.subset_add_3.
 apply PS.max_elt_1; auto.
 red; intros a; generalize (H2 a); F.set_iff; intuition.
red; intros a; generalize (H3 a)(H4 a); F.set_iff; intuition.

rewrite <- F.not_mem_iff in H1.
split; intros.
left.
 red; intros a; generalize (H2 a); F.set_iff; intuition.
 compute in H3; subst a; intuition.
destruct H2.
red; intros a; generalize (H2 a); F.set_iff; intuition.
destruct H2 as (b,(H2,H3)).
rewrite <- IHn in H2; auto.
assert (PS.Subset (PS.add e b) s).
 apply P.subset_add_3.
 apply PS.max_elt_1; auto.
 red; intros a; generalize (H2 a); F.set_iff; intuition.
red; intros a; generalize (H3 a)(H4 a); F.set_iff; intuition.

rewrite (P.cardinal_1 (PS.max_elt_3 H)) in Heqn; inversion Heqn.
Qed.

Open Scope nat_scope.

Fixpoint two_power (n:nat) : nat := match n with 
 | O => 1
 | S n => 2 * (two_power n)
 end.

Lemma powerset_cardinal: 
 forall s, PSS.cardinal (powerset s) = two_power (PS.cardinal s).
Proof.
intros.
unfold powerset.
rewrite <- Fold.fold_direct_1.
remember (PS.cardinal s) as n.
revert s Heqn.
induction n; simpl; intros.
apply PP.singleton_cardinal.

case_eq (PS.max_elt s); intros.
assert (S (PS.cardinal (PS.remove e s)) = S n).
 rewrite Heqn.
 apply P.remove_cardinal_1; auto.
 apply PS.max_elt_1; auto.
injection H0; clear H0; intros.
generalize (IHn (PS.remove e s) (sym_eq H0)); clear IHn.
rewrite <-H0; rewrite Fold.fold_direct_1.
fold (powerset (PS.remove e s)); intros.
rewrite PP.union_cardinal; auto.
rewrite PSS'.map_cardinal.
rewrite H1; auto.
intros; apply F.add_m; auto.
intros x y; do 2 rewrite <- powerset_is_powerset.
unfold PSS.E.eq; change PS.eq with PS.Equal.
red; intros.
generalize (H2 a) (H3 a) (H4 a).
F.set_iff; intuition.
intros.
case_eq (PS.mem e x); intros.
left; intros.
rewrite <- powerset_is_powerset.
red; intros.
rewrite <- F.mem_iff in H2.
generalize (H3 e H2).
apply PS.remove_1; auto.
right; intros.
rewrite PSS'.map_In.
intros; apply F.add_m; auto.
unfold PSS.E.eq; change PS.eq with PS.Equal.
red; intros.
destruct H3 as (b,(H3,H4)).
rewrite <- powerset_is_powerset in H3.
rewrite <- F.not_mem_iff in H2.
elim H2.
rewrite <- (H4 e).
rewrite F.add_iff; auto.

rewrite (P.cardinal_1 (PS.max_elt_3 H)) in Heqn; inversion Heqn.
Qed.


(* Later: results about cardinals and binomial numbers ? *)