Require Import ZArith MSets MSetAVL.

Module M := MSetAVL.Make(Z_as_OT).

Open Scope Z_scope.

Definition ens1 := M.add 3 (M.add 0 (M.add 2 (M.empty))).
Definition ens2 := M.add 0 (M.add 2 (M.add 4 (M.empty))).
Definition ens3 := M.inter ens1 ens2.
Definition ens4 := M.union ens1 ens2.

Eval vm_compute in (M.mem 2 ens3).
Eval vm_compute in (M.elements ens3).
Eval vm_compute in (M.elements ens4).
Eval vm_compute in M.compare ens3 ens4.

(* Sets by themselves are ugly (proof parts), but who cares *)
Eval vm_compute in ens1.
Eval vm_compute in ens3.
Eval vm_compute in ens4.

(** Some more intense tests. *)

Fixpoint multiples (m:Z)(start:Z)(n:nat) {struct n} : list Z :=
  match n with
   | O => nil
   | S n => start::(multiples m (m+start) n)
  end.

Eval vm_compute in (multiples 2 0 200%nat).

Definition bigens1 := fold_right M.add M.empty (multiples 2 0 400%nat).
Definition bigens2 := fold_right M.add M.empty (multiples 3 0 400%nat).
Time Eval vm_compute in (M.elements (M.inter bigens1 bigens2)).
Time Eval vm_compute in (M.elements (M.union bigens1 bigens2)).

Definition bigens3 := fold_right M.add M.empty (multiples 2 0 (100*100)%nat).
Definition bigens4 := fold_right M.add M.empty (multiples 3 0 (100*100)%nat).
Time Eval vm_compute in (M.cardinal bigens3). (* computation of bigens3 done once and forall *)
Time Eval vm_compute in (M.cardinal bigens4). (* computation of bigens4 done once and forall *)
Time Eval vm_compute in (M.cardinal (M.inter bigens3 bigens4)).
Time Eval vm_compute in (M.cardinal (M.union bigens3 bigens4)).

(* Experimental illustration of the cardinal law: |AUB|+|A^B|=|A|+|B| *)
Time Eval vm_compute in (M.cardinal (M.union bigens3 bigens4)
                                         +M.cardinal (M.inter bigens3 bigens4))%nat.
(*   = 20000%nat
     : nat
*)

