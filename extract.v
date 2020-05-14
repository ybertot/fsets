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

Require Import FSets.
Require Import FSetAVL.
Require Import FSetAVL_dep.
Require Import FSetRBT.
Require Import ZArith.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive sumor => "option" [ "Some" "None" ].
Extraction Inline Wf_nat.lt_wf_rec.
Extraction Inline Z_lt_rec.
Extraction Inline Fix_F well_founded_induction_type_2.

Set Warnings "-extraction-opaque-accessed".

Module NatRBT := FSetRBT.Make Nat_as_OT.
Extraction "rbt.ml" NatRBT.empty.

Module NatAVL := FSetAVL.Make Nat_as_OT.
Extraction "avl.ml" NatAVL.empty.

Module NatAVL_dep := FSetAVL_dep.Make Nat_as_OT.
Extraction "avl_dep.ml" NatAVL_dep.empty.
