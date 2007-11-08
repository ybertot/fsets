Require Import FMaps NArith MultiSets FMapListEq.

(* If we have: 
    - A UsualOrderedType for elements (i.e. a decidable order 
       compatible with Coq equality).
    - Proof Irrelevance axiom
   then we can build Multisets relying on Finite Maps implemented
   as sorted lists, in such a way that the equality on Multisets
   is the usual equality of Coq.
*)

Module UsualEqual (U:UsualOrderedType).

  Module Import UE:= FMapListEq.UsualEqual U.
  Module Mu := MultiSets.Multi U UE.M.

  Lemma Equal_eq : forall m m' : Mu.t, Mu.Equal m m' -> m = m'.
  Proof.
   intros.
   unfold Mu.t, Mu.Equal, Mu.multi in *.
   apply UE.Equal_eq.
   red; intros.
   generalize (H y); clear H.
   do 2 destruct M.find; inversion 1; auto.
  Qed.

  (* An example of consequence. *)

  Lemma union_commutes : forall m m', Mu.union m m' = Mu.union m' m.
  Proof.
    intros.
    apply Equal_eq.
    red; intros.
    do 2 rewrite Mu.union_1.
    apply Nplus_comm.
  Qed.

End UsualEqual.