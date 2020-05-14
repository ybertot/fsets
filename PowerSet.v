Require Import FSets MapFunction.
Require Import Arith EqNat Euclid ArithRing ZArith.
Set Implicit Arguments.

(** First, let's define powers of 2 and binomial function 
    for later expressing the cardinal of powersets. *)

Fixpoint two_power (n:nat) : nat := match n with 
 | O => 1
 | S n => 2 * (two_power n)
 end.

Fixpoint binomial n k { struct n } := match n, k with 
  | _, O => 1
  | O, _ => 0 
  | S n', S k' => binomial n' k' + binomial n' k
 end. 

Fixpoint fact n := match n with 
  | O => 1 
  | S n' => n * (fact n') 
 end.

Lemma binomial_0 : forall n k, k>n -> binomial n k = 0.
Proof.
induction n; destruct k; simpl; auto.
inversion 1.
inversion 1.
intros.
do 2 (rewrite IHn; auto with arith).
Qed.

Lemma binomial_rec : forall n k, k<=n -> 
 (binomial n k)*(fact k * fact (n-k)) = fact n.
Proof.
induction n; destruct k.
simpl; auto.
inversion 1.
simpl; intros; ring.
intros.
change (fact (S n)) with ((1+n)*(fact n)).
change (fact (S k)) with ((1+k)*(fact k)).
simpl (S n - S k).
simpl binomial.
inversion_clear H.
rewrite (@binomial_0 n (S n)); auto.
pattern (fact n) at 2; rewrite <- (IHn n); auto; ring.
cut ((binomial n k)*(fact k*fact (n-k))*(1+k) + 
     (binomial n (S k))*(fact (S k)*fact (n-S k))*(n-k) = 
     (1+n)*fact n).
intros H; rewrite <- H.
replace (n-k) with (S (n-S k)) by omega.
simpl; ring.
rewrite (IHn k); auto with arith.
rewrite (IHn (S k)); auto with arith.
cut (((1+k)+(n-k))*(fact n) = (1+n)*(fact n)).
intro H; rewrite <- H; ring.
replace (1+k+(n-k)) with (1+n) by omega; auto.
Qed.

Lemma fact_pos : forall k, fact k > 0.
Proof.
 induction k; simpl; auto with arith.
Qed.

Lemma binomial_den_pos : forall n k, fact k * fact (n-k) > 0.
Proof.
 intros; generalize (fact_pos k) (fact_pos (n-k)).
 unfold gt; intros.
 change 0 with (0*(fact (n-k))).
 apply mult_lt_compat_r; auto with arith.
Qed.

Definition binomial' n k := 
 let (q,_) := quotient (fact k * fact (n-k)) (binomial_den_pos n k) (fact n)
 in q.

Lemma binomial_alt : forall n k, k<=n -> 
 binomial n k = binomial' n k.
Proof.
intros.
unfold binomial'.
destruct quotient as (q,(r,(H1,H2))).
assert (H3:=binomial_rec H).
assert (H4:=binomial_den_pos n k).
set (D:=fact k * fact (n-k)) in *.
assert (r = fact n - q * D) by omega.
rewrite <- H3 in H0.
assert (r = (binomial n k - q)*D) by (rewrite H0;auto with arith).
rewrite H5 in H2; unfold gt in H2.
case_eq (binomial n k - q); intros.
rewrite H6 in *; simpl in *.
rewrite H5 in *; simpl in *.
rewrite plus_comm in H1; simpl in H1.
rewrite H1 in H3.
assert (0 = q*D - binomial n k*D) by (rewrite H3; auto with arith).
assert (0 = (q - binomial n k)*D) by (rewrite H7; auto with arith).
case_eq (q - binomial n k); intros.
omega.
assert (0 * D < S n0 * D).
 apply mult_lt_compat_r; auto with arith.
rewrite <- H9 in H10; rewrite <- H8 in H10; simpl in H10; inversion H10.
assert (1 * D <= S n0 * D).
 apply mult_le_compat; auto with arith.
rewrite <- H6 in H7.
simpl in H7; rewrite plus_comm in H7; simpl in H7.
omega.
Qed.


Module PowerSet (M:S).

(* M is our base sets structure. *)
(* MM is a "sets of sets" structure: *)
Module MM := FSetList.Make M.
(* Adding a map function to MM... *)
Module MM' := MapFunction.MapFunction MM.
(* Properties functors *)
Module P := FSetProperties.Properties M.
Module P' := FSetProperties.OrdProperties M.
Module F := P.FM.
Module PEP := FSetEqProperties.EqProperties MM.
Module PP := PEP.MP.
Module FF := PP.FM.
Module ME := OrderedTypeFacts M.E.

Infix "[=]" := M.Equal (at level 70, no associativity).
Infix "[==]" := MM.Equal (at level 70, no associativity).

(** Computing the set of all subsets of a particular set [s] *)

Definition powerset s := 
  M.fold 
   (fun (x:M.elt)(ss:MM.t) => MM.union ss (MM'.map (M.add x) ss)) 
   s 
   (MM.singleton M.empty).

(** Proofs about powerset *)

Lemma map_add : forall s s' x, MM.In s' (MM'.map (M.add x) s)
 <-> M.In x s' /\ (MM.In s' s \/ MM.In (M.remove x s') s).
Proof.
intros.
rewrite MM'.map_In by (intros; rewrite H; reflexivity).
unfold M.eq in *.
split; [intros (b & IN & EQ) | intros (IN,[OR1|OR2]) ].
assert (M.In x s') by (rewrite <- EQ; auto with *).
split; auto.
destruct (P.In_dec x b); [left|right]; 
 apply MM.In_1 with (2:=IN); P.Dec.fsetdec.
 (* sans le P.Dec.fsetdec : 
     rewrite <- IN; red; intro a; F.set_iff; intuition.
     eauto with set. ----> anomaly *)

exists s'; split; auto; P.Dec.fsetdec.
exists (M.remove x s'); split; auto; P.Dec.fsetdec.
Qed.

Lemma compat_op_pow :
 compat_op M.E.eq MM.Equal
  (fun x0 ss => MM.union ss (MM'.map (M.add x0) ss)).
Proof.
repeat red; intros; FF.set_iff.
do 2 rewrite map_add; rewrite H; rewrite H0; intuition.
Qed.
Hint Resolve compat_op_pow : set.

Lemma singleton_empty : forall s, MM.In s (MM.singleton M.empty) <-> M.Empty s.
Proof.
intros.
rewrite FF.singleton_iff; split; unfold M.eq; auto with set.
Qed.

Lemma powerset_base : forall s, M.Empty s -> powerset s [==] MM.singleton M.empty.
Proof.
intros; unfold powerset.
rewrite (@P.fold_1 s MM.t MM.Equal FF.Equal_ST); auto with set.
Qed.

Lemma powerset_step : forall s1 s2 x, P'.Above x s1 -> P.Add x s1 s2 -> 
 powerset s2 [==] MM.union (powerset s1) (MM'.map (M.add x) (powerset s1)). 
Proof.
intros; unfold powerset.
rewrite (@P'.fold_3 s1 s2 x MM.t MM.Equal FF.Equal_ST); auto with set.
Qed.

Lemma powerset_is_powerset: 
 forall s s', MM.In s' (powerset s) <-> M.Subset s' s.
Proof.
induction s using P'.set_induction_max; intros.

rewrite (powerset_base H).
rewrite singleton_empty; firstorder.

rewrite (powerset_step H H0).
FF.set_iff.
rewrite map_add.
do 2 rewrite IHs1; clear IHs1.
split; [intros [U|[U [V|V]]]|intros U].
firstorder.
firstorder.
red; intro a; generalize (H a)(H0 a); F.set_iff; destruct (F.eq_dec a x); intuition.
(*eauto with set. (* Anomaly: uncaught exception Failure "Cannot print a global reference". *)*)
apply H6; apply V; auto with *.
destruct (P.In_dec x s'); [right|left].
split; auto.
right.
red; intro a; generalize (U a)(H0 a); F.set_iff; intuition.
red; intro a; generalize (U a)(H0 a); intuition.
elim n; rewrite H4; auto.
Qed.

Lemma powerset_cardinal: 
 forall s, MM.cardinal (powerset s) = two_power (M.cardinal s).
Proof.
induction s using P'.set_induction_max; intros.

rewrite (powerset_base H).
rewrite PP.singleton_cardinal.
rewrite P.cardinal_1; simpl; auto.

rewrite (powerset_step H H0).
rewrite PP.union_cardinal.
rewrite MM'.map_cardinal.
rewrite IHs1.
rewrite (@P.cardinal_2 s1 s2 x); auto.
simpl; auto.
red; intros.
elim (@M.E.lt_not_eq x x); auto with *.
intros; rewrite H1; reflexivity.
intros u v; do 2 rewrite powerset_is_powerset.
red; red; intros.
generalize (H3 a) (H1 a) (H2 a); F.set_iff; clear H3 H1 H2.
intuition; elim (@M.E.lt_not_eq a x); auto with *.
intros u (A,B).
rewrite powerset_is_powerset in A.
rewrite map_add in B; destruct B as (B,_).
elim (@M.E.lt_not_eq x x); auto with *.
Qed.

(** Computing the set of all subsets of cardinal k for a particular set [s] *)

Definition powerset_k s k := 
 MM.filter (fun s => beq_nat (M.cardinal s) k) (powerset s).


(** Proofs about powerset_k *)

Lemma powerset_k_is_powerset_k : forall k s s', 
 MM.In s' (powerset_k s k) <-> M.Subset s' s /\ M.cardinal s' = k.
Proof.
unfold powerset_k; intros.
rewrite FF.filter_iff by (red; intros; f_equal; auto with *).
rewrite powerset_is_powerset. 
intuition.
apply beq_nat_eq; auto.
subst; symmetry; apply beq_nat_refl.
Qed.

Lemma powerset_k_cardinal : forall s k, 
 MM.cardinal (powerset_k s k) = binomial (M.cardinal s) k.
Proof.
assert (forall k, compat_bool M.Equal (fun s0 => beq_nat (M.cardinal s0) k)).
 red; intros; f_equal; auto with *.
induction s using P'.set_induction_max; unfold powerset_k; intros.

rewrite P.cardinal_1; auto.
destruct k.
rewrite <- (@PP.Equal_cardinal (MM.singleton M.empty)).
 apply PP.singleton_cardinal.
 red; intros.
 rewrite FF.filter_iff; auto.
 rewrite powerset_base; auto.
 rewrite singleton_empty.
 intuition.
 rewrite P.cardinal_1; auto.
rewrite <- (@PP.Equal_cardinal MM.empty).
 apply PP.cardinal_1; auto with *.
 red; intros.
 rewrite FF.empty_iff; rewrite FF.filter_iff; auto.
 rewrite powerset_base; auto.
 rewrite singleton_empty.
 intuition.
 rewrite (P.cardinal_1 H2) in H3; simpl in H3; discriminate.

assert (H2 := powerset_step H0 H1).
rewrite (FF.filter_equal (H k) H2).
rewrite PEP.filter_union; auto with *.
rewrite PP.union_cardinal; auto.
unfold powerset_k in IHs1.
rewrite IHs1.
rewrite MM'.map_filter by (auto; intros; rewrite H3; reflexivity).
rewrite MM'.map_cardinal. 
destruct k.
rewrite PP.cardinal_1.
destruct (M.cardinal s1); destruct (M.cardinal s2); auto.
red; intro a; rewrite FF.filter_iff.
red; destruct 1.
case_eq (M.cardinal (M.add x a)); intros.
elim (@P.cardinal_inv_1 _ H5 x); F.set_iff; auto with *.
rewrite H5 in H4; simpl in H4; inversion H4.
repeat red; intros; f_equal; rewrite H3; auto.
assert (MM.filter (fun x0 => beq_nat (M.cardinal (M.add x x0)) (S k)) (powerset s1)
   [==] MM.filter (fun x0 => beq_nat (M.cardinal x0) k) (powerset s1)).
red; intros.
rewrite FF.filter_iff by (repeat red; intros; f_equal; rewrite H3; auto).
rewrite FF.filter_iff by (repeat red; intros; f_equal; rewrite H3; auto).
rewrite powerset_is_powerset.
intuition.
assert (~M.In x a).
 red; intros; elim (@ME.lt_antirefl x); auto.
rewrite P.add_cardinal_2 in H5; simpl in H5; auto.
assert (~M.In x a).
 red; intros. elim (@ME.lt_antirefl x); auto.
rewrite P.add_cardinal_2; simpl; auto.
rewrite H3.
rewrite IHs1.
rewrite (@P.cardinal_2 s1 s2 x); auto.
simpl; auto with arith.
red; intros; elim (@ME.lt_antirefl x); auto. 

intros; rewrite H3; reflexivity.

intros.
rewrite FF.filter_iff in H3.
destruct H3.
rewrite FF.filter_iff in H4.
destruct H4.
rewrite powerset_is_powerset in H3.
rewrite powerset_is_powerset in H4.
assert (~M.In x x0).
 red; intros; elim (@ME.lt_antirefl x); auto with *.
assert (~M.In x y).
 red; intros; elim (@ME.lt_antirefl x); auto.
red; red; intros.
generalize (H5 a); clear H5; do 2 rewrite F.add_iff.
intuition.
now elim H8; apply M.In_1 with a; auto with *.
now elim H8; apply M.In_1 with a; auto with *.
now elim H9; apply M.In_1 with a; auto with *.
now elim H9; apply M.In_1 with a; auto.
repeat red; intros; f_equal; rewrite H7; auto.
repeat red; intros; f_equal; rewrite H6; auto.

intros.
rewrite !FF.filter_iff by (red; intros; subst; auto with *).
rewrite map_add.
rewrite !powerset_is_powerset.
intros ((A,_),((B,_),_)).
elim (@ME.lt_antirefl x); auto.
Qed.

(** A more "direct" definition *)

Definition powerset_k' s := 
  M.fold 
  (fun (x:M.elt)(ff:nat->MM.t)(k:nat) => match k with 
    | O => ff 0
    | S k' => MM.union (ff k) (MM'.map (M.add x) (ff k'))
   end) 
  s 
  (fun k => if k then MM.singleton M.empty else MM.empty).

Lemma powerset_k'_is_powerset_k : 
 forall s s' k, MM.In s' (powerset_k' s k) <-> M.Subset s' s /\ M.cardinal s' = k.
Proof.
assert (ST : Setoid_Theory _ (fun g h => forall k:nat, g k [==] h k)).
 constructor; red; auto with set.
 intros; apply PP.equal_trans with (y k); auto with set.

induction s using P'.set_induction_max; intros.

intros; unfold powerset_k'.
assert (T:=P.fold_1 ST (s:=s)).
simpl in T; rewrite T; clear T; auto.

destruct k.
rewrite singleton_empty.
intuition idtac.
firstorder.
intuition.
intuition.
rewrite FF.empty_iff.
intuition.
rewrite P.cardinal_1 in H2; try discriminate; firstorder.

intros; unfold powerset_k'.
assert (T:=P'.fold_3 ST (s:=s1) (s':=s2) (x:=x)).
simpl in T; rewrite T; clear T; auto.

change (MM.In s' (match k with 
         | O => powerset_k' s1 0
         | S k' => MM.union (powerset_k' s1 k) (MM'.map (M.add x) (powerset_k' s1 k'))
         end) <-> M.Subset s' s2 /\ M.cardinal s' = k).
destruct k.
rewrite IHs1.
intuition idtac.
red; intros.
elim (P.cardinal_inv_1 H3 H1).
red; intros.
elim (P.cardinal_inv_1 H3 H1).
FF.set_iff.
rewrite map_add.
do 3 rewrite IHs1; clear IHs1.
split; destruct 1.
destruct H1; split; auto.
apply P.subset_trans with s1; auto; red; intros; rewrite (H0 a); auto.
destruct H1.
destruct H2; intuition idtac.
firstorder.
elim (@M.E.lt_not_eq x x); auto with *.
red; intro a; generalize (H3 a)(H0 a); F.set_iff; destruct (F.eq_dec a x); intuition.
rewrite <- H4.
symmetry; apply P.remove_cardinal_1; auto.
destruct (P.In_dec x s').
right.
 split; auto.
 right; split.
 red; intro a; generalize (H1 a)(H0 a); F.set_iff; intuition.
 generalize (P.remove_cardinal_1 i); auto.
 rewrite H2; inversion 1; auto.
left.
 split; auto.
 red; intro a; generalize (H1 a)(H0 a); intuition.
 elim n; rewrite H6; auto.

unfold compat_op, Proper, respectful; intros.
destruct k0; auto.
red; intros; FF.set_iff.
rewrite !map_add, !H2, H1; split; auto.
Qed.

Lemma powerset_k_alt : 
 forall s k, powerset_k' s k [==] powerset_k s k.
Proof.
red; intros.
rewrite powerset_k'_is_powerset_k. 
rewrite powerset_k_is_powerset_k.
split; auto.
Qed.

End PowerSet.

(** An example: *)

Open Scope positive_scope.

Module P := FSetList.Make Positive_as_OT.
Module PS := PowerSet P.
Module PP := PS.MM.

(* The set containing numbers 1..n *)
Fixpoint interval (n:nat) {struct n} : P.t := match n with 
 | O => P.empty
 | S n => P.add (P_of_succ_nat n) (interval n)
 end.

Eval vm_compute in P.elements (interval 10).

Definition powerset_5 := PS.powerset (interval 5).

Eval vm_compute in map P.elements (PP.elements powerset_5).

Definition subsets_size2_in5 := PS.powerset_k' (interval 5) 2. 

Eval vm_compute in map P.elements (PP.elements subsets_size2_in5).





