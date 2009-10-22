Require Import FSets.
Require Import ProofIrrelevance.

(* For the equality on sets to be the one of Coq, we need: 
    - an order on elements, and not just a decidable equality 
       (hence an OrdereredType leading to some FSets instead of 
        a DecidableType leading to some FSetWeak).
    - the equality on elements must be the one of Coq
       (hence a UsualOrderedType instead of just a OrderedType)
    - an implementation of sets with canonical representation, 
       for instance FSetList based on sorted lists.
    - the proof irrelevance axiom, since an implementation such 
       as FSetList isn't really canonical: a set comes with 
       a well-sortedness certificate.
*)

Module UsualEqual (U:UsualOrderedType).

  Module Import M := FSetList.Make U.
  Module Import P := FSetProperties.Properties M.
  Module Import P' := FSetProperties.OrdProperties M.

  (* True in any FSet: *) 

  Lemma Equal_elements_eqlistA : forall s s' : t, Equal s s' -> 
   eqlistA U.eq (elements s) (elements s').
  Proof.
  intros; apply sort_equivlistA_eqlistA; auto; apply elements_3.
  Qed.

  (* Since U.eq is Coq eq, then eqlistA is also Coq eq *)

  Lemma eqlistA_eq : forall (l l' : list U.t), 
   eqlistA U.eq l l' -> l=l'.
  Proof.
  induction 1; auto; f_equal; auto.
  Qed.

  (* Finally, for FSetList, elements is the identity. 
     Or more precisely, the removal of a proof of well-sortedness. 
     So we need proof irrelevance. *)

  Lemma Equal_eq : forall s s' : t, Equal s s' -> s = s'.
  Proof.
   intros; generalize (eqlistA_eq _ _ (Equal_elements_eqlistA _ _ H)); clear H.
   destruct s as [s Hs]; destruct s' as [s' Hs']; simpl.
   intros.
   rewrite proof_irrelevance with (p1:=Hs') (p2:=eq_rect s _ Hs s' H).
   elim H using eq_indd.
   reflexivity.
  Qed.

End UsualEqual.

