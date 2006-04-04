
Require Import OrderedType.
Require Import ZArith.
Require Import Compare_dec.

(** [nat] is an ordered type with respect to the usual order on natural numbers. *)

Module Nat_as_OT : OrderedType.

  Definition t := nat.

  Definition eq := eq (A:=nat).
  Definition lt := lt.

  Lemma eq_refl : forall x : t, eq x x. 
  Proof. unfold eq in |- *; auto. Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. unfold eq in |- *; auto. Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. unfold eq in |- *; intros; rewrite H; auto. Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. unfold lt in |- *; intros; apply lt_trans with y; auto. Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. unfold lt, eq in |- *; intros; omega. Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros; case (lt_eq_lt_dec x y).
    simple destruct 1; intro.
    constructor 1; auto.
    constructor 2; auto.
    intro; constructor 3; auto.
  Qed.

End Nat_as_OT.



(** [Z] is an ordered type with respect to the usual order on integers. *)

Open Scope Z_scope.

Module Z_as_OT <: OrderedType.

  Definition t := Z.
  Definition eq (x y:Z) := (x=y).
  Definition lt (x y:Z) := (x<y).

  Section xyz.
  Variables x y z : Z.

  Lemma eq_refl : x=x .  
  Proof. auto. Qed.

  Lemma eq_sym : x=y -> y=x.
  Proof. auto. Qed.

  Lemma eq_trans : x=y -> y=z -> x=z.
  Proof. auto with zarith. Qed.

  Lemma lt_trans : x<y -> y<z -> x<z.
  Proof. auto with zarith. Qed.

  Lemma lt_not_eq : x<y -> ~ x=y.
  Proof. auto with zarith. Qed.

  Definition compare : Compare lt eq x y.
  Proof.
    case_eq (x ?= y); intros.
    apply EQ; unfold eq; apply Zcompare_Eq_eq; auto.
    apply LT; unfold lt, Zlt; auto.
    apply GT; unfold lt, Zlt; rewrite <- Zcompare_Gt_Lt_antisym; auto.
  Defined.

  End xyz.
End Z_as_OT.



(** [positive] is an ordered type with respect to the usual order on natural numbers. *) 

Open Scope positive_scope.

Module Positive_as_OT <: OrderedType.
  Definition t:=positive.
  Definition eq:=@eq positive.
  Definition lt p q:= (p ?= q) Eq = Lt.

  Lemma eq_refl : forall x : t, eq x x.
  Proof. red; auto. Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. red; auto. Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. red; intros; transitivity y; auto. Qed.
 
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. 
  unfold lt; intros x y z.
  change ((Zpos x < Zpos y)%Z -> (Zpos y < Zpos z)%Z -> (Zpos x < Zpos z)%Z).
  auto with zarith.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
  intros; intro.
  rewrite H0 in H.
  unfold lt in H.
  rewrite Pcompare_refl in H; discriminate.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
  intros x y.
  case_eq ((x ?= y) Eq); intros.
  apply EQ; apply Pcompare_Eq_eq; auto.
  apply LT; unfold lt; auto.
  apply GT; unfold lt.
  replace Eq with (CompOpp Eq); auto.
  rewrite <- Pcompare_antisym; rewrite H; auto.
  Qed.

End Positive_as_OT.

(** From two ordered types, we can build a new OrderedType 
   over their cartesian product, using the lexicographic order. *)

Module PairOrderedType(O1 O2:OrderedType) <: OrderedType.
 Module MO1:=OrderedTypeFacts(O1).
 Module MO2:=OrderedTypeFacts(O2).

 Definition t := prod O1.t O2.t.
  
 Definition eq x y := O1.eq (fst x) (fst y) /\ O2.eq (snd x) (snd y).

 Definition lt x y := 
    O1.lt (fst x) (fst y) \/ 
    (O1.eq (fst x) (fst y) /\ O2.lt (snd x) (snd y)).

 Lemma eq_refl : forall x : t, eq x x.
 Proof. 
 intros (x1,x2); red; simpl; auto.
 Qed.

 Lemma eq_sym : forall x y : t, eq x y -> eq y x.
 Proof. 
 intros (x1,x2) (y1,y2); unfold eq; simpl; intuition.
 Qed.

 Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
 Proof. 
 intros (x1,x2) (y1,y2) (z1,z2); unfold eq; simpl; intuition eauto.
 Qed.
 
 Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z. 
 Proof.
 intros (x1,x2) (y1,y2) (z1,z2); unfold eq, lt; simpl; intuition.
 left; eauto.
 left; eapply MO1.lt_eq; eauto.
 left; eapply MO1.eq_lt; eauto.
 right; split; eauto.
 Qed.

 Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
 Proof.
 intros (x1,x2) (y1,y2); unfold eq, lt; simpl; intuition.
 apply (O1.lt_not_eq H0 H1).
 apply (O2.lt_not_eq H3 H2).
 Qed.

 Definition compare : forall x y : t, Compare lt eq x y.
 intros (x1,x2) (y1,y2).
 destruct (O1.compare x1 y1).
 apply LT; unfold lt; auto.
 destruct (O2.compare x2 y2).
 apply LT; unfold lt; auto.
 apply EQ; unfold eq; auto.
 apply GT; unfold lt; auto.
 apply GT; unfold lt; auto.
 Qed.

End PairOrderedType.



