Require Import FSetInterface.
Require Import FSetAVL_nodep.
Require Import FSetAVL_int.
Require Import ZArith.
Open Scope Z_scope.

Module ZOT <: OrderedType.

  Definition t := Z.

  Definition eq := eq (A:=Z).
  Definition lt := Zlt.

  Lemma eq_refl : forall x : t, eq x x. 
  Proof. unfold eq in |- *; auto. Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof. unfold eq in |- *; auto. Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof. unfold eq in |- *; intros; rewrite H; auto. Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof. unfold lt in |- *; intros; omega. Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof. unfold lt, eq in |- *; intros; omega. Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros x y; case_eq (Zcompare x y).
    constructor 2; unfold eq; apply Zcompare_Eq_eq; auto.
    constructor 1; unfold lt, Zlt; auto.
    constructor 3; unfold lt, Zlt; rewrite <- Zcompare_Gt_Lt_antisym; auto.
  Defined.

End ZOT.

Module M := FSetAVL_nodep.Make(ZOT).

Eval compute in (M.min_elt (M.union'  (M.add 3 (M.add 0 (M.empty))) (M.add 1 (M.add 2 (M.empty))))).

Module MI := FSetAVL_int.Make(Int.Z_as_Int)(ZOT).

Eval compute in (MI.min_elt (MI.union'  (MI.add 3 (MI.add 0 (MI.empty))) (MI.add 1 (MI.add 2 (MI.empty))))).

