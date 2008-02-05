Require Import FMaps.
Require Import ProofIrrelevance.

(* For the equality on maps to be the one of Coq, we need: 
    - an order on keys, and not just a decidable equality 
       (hence an OrdereredType leading to some FMaps instead of 
        a DecidableType leading to some FMapWeak).
    - the equality on keys must be the one of Coq
       (hence a UsualOrderedType instead of just a OrderedType)
    - an implementation of maps with canonical representation, 
       for instance FMapList based on sorted lists.
    - the proof irrelevance axiom, since an implementation such 
       as FMapList isn't really canonical: a set comes with 
       a well-sortedness certificate.
*)

Module UsualEqual (U:UsualOrderedType).

  Module Import M := FMapList.Make U.
  Module Import P := FMapFacts.Properties M.
  Module Import P' := FMapFacts.OrdProperties M.

  (* True in any FMap: *) 

  Check elements_Equal_eqlistA.

  (* Since U.eq is Coq eq, then eqlistA is also Coq eq *)

  Lemma eqlistA_eq : forall (elt:Set)(l l' : list (U.t*elt)), 
   eqlistA (@O.eqke elt) l l' -> l=l'.
  Proof.
  induction 1; auto; f_equal; auto.
  red in H.
  destruct x; destruct x'; simpl in *; f_equal; intuition.
  Qed.

  (* Finally, for FMapList, elements is the identity. 
     Or more precisely, the removal of a proof of well-sortedness. 
     So we need proof irrelevance. *)

  Lemma Equal_eq : forall (elt:Set)(m m' : t elt), Equal m m' -> m = m'.
  Proof.
   intros; generalize (eqlistA_eq _ _ _ (elements_Equal_eqlistA H)); clear H.
   destruct m as [m Hm]; destruct m' as [m' Hm']; simpl.
   intros.
   rewrite proof_irrelevance with (p1:=Hm') (p2:=eq_rect m (sort (@Raw.PX.ltk elt)) Hm m' H). 
   elim H using eq_indd.
   reflexivity.
  Qed.

End UsualEqual.

