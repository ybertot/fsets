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

(* extraction *)

Require Import FSet.
Require Import ZArith.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive sumor => "option" [ "Some" "None" ].
Extraction Inline Wf_nat.lt_wf_rec.
Extraction Inline Z_lt_rec.
Extraction Inline Acc_iter_2 well_founded_induction_type_2.

Module Nat : OrderedType.

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

End Nat.

Module NatRBT := FSetRBT.Make Nat.

Extraction "rbt.ml" NatRBT.empty.

Module NatAVL := FSetAVL.Make Nat.

Extraction "avl.ml" NatAVL.empty.