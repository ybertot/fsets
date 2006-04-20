Require Import FSetInterface.
Require Import FSetAVL.
Require Import FSetAVL_int.
Require Import ZArith.
Require Import SomeOrderedType.
Open Scope Z_scope.

Module M := FSetAVL.Make(Z_as_OT).

Eval compute in (M.min_elt (M.union'  (M.add 3 (M.add 0 (M.empty))) (M.add 1 (M.add 2 (M.empty))))).

Module MI := FSetAVL_int.Make(Z_as_OT).

Eval compute in (MI.min_elt (MI.union'  (MI.add 3 (MI.add 0 (MI.empty))) (MI.add 1 (MI.add 2 (MI.empty))))).

