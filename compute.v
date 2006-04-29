Require Import FSets.
Require Import FSetAVL.
Require Import FSetAVL_z.
Require Import ZArith.
Open Scope Z_scope.

Module M := FSetAVL.Make(Z_as_OT).

Eval compute in (M.min_elt (M.union' (M.add 3 (M.add 0 (M.empty))) (M.add 1 (M.add 2 (M.empty))))).

Module M' := FSetAVL_z.Make(Z_as_OT).

Eval compute in (M'.min_elt (M'.union' (M'.add 3 (M'.add 0 (M'.empty))) (M'.add 1 (M'.add 2 (M'.empty))))).

