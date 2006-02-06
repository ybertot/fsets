(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Finite maps library.  
 * Authors: Pierre Courtieu and Pierre Letouzey 
 * Institutions: Cédric (CNAM) & PPS (Université Paris 7) *)

(** This file proposes an implementation of the non-dependant interface
 [FMapInterface.S] using lists of pairs ordered (increasing) with respect to
 left projection. *)

Require Import FSetInterface. 
Require Import FMapInterface.

Set Implicit Arguments.
Unset Strict Implicit.

(** Usual syntax for lists. *)
Notation "[]" := nil (at level 0).
Arguments Scope list [type_scope].

Ltac absurd_hyp h := 
  let T := type of h in 
  absurd T.

Module Raw (X:OrderedType).
  Module E := X.
  Module MX := OrderedTypeFacts X.

  Definition key := X.t.
  Definition t (elt:Set) := list (X.t * elt).

  Section Elt.

  Variable elt : Set.

  Definition eqk (p p':key*elt) := X.eq (fst p) (fst p').
  Definition eqke (p p':key*elt) := 
          X.eq (fst p) (fst p') /\ (snd p) = (snd p').
  Definition ltk (p p':key*elt) := X.lt (fst p) (fst p').

  Hint Unfold eqk eqke ltk.
  Hint Extern 2 (eqke ?a ?b) => split.

  Ltac simpl_eqke :=
    match goal with
    	H:(eqke _ _) |- _ => 
          let x:= fresh "eqk" in 
	  let y := fresh "eqe" in (destruct H as (x,y); simpl in y; simpl in x)
    end.

  Ltac sintuition := try simpl_eqke; intuition.

  (* eqk, eqke are equalities, ltk is a strict order *)
 
  Lemma eqk_refl : forall e, eqk e e.
    auto.
  Qed.

  Lemma eqke_refl : forall e, eqke e e.
    auto.
  Qed.

  Lemma eqk_sym : forall e e', eqk e e' -> eqk e' e.
    auto.
  Qed.

  Lemma eqke_sym : forall e e', eqke e e' -> eqke e' e.
    intros; sintuition.
  Qed.

  Lemma eqk_trans : forall e e' e'', eqk e e' -> eqk e' e'' -> eqk e e''.
    eauto. 
  Qed.

  Lemma eqke_trans : forall e e' e'', eqke e e' -> eqke e' e'' -> eqke e e''.
    unfold eqke; intuition eauto; congruence.
  Qed.

  Hint Resolve eqk_trans eqke_trans eqk_sym eqke_sym eqk_refl eqke_refl.

  Lemma ltk_trans : forall e e' e'', ltk e e' -> ltk e' e'' -> ltk e e''.
     eauto.
  Qed.

  Lemma ltk_not_eqk : forall e e', ltk e e' -> ~ eqk e e'.
    unfold eqk, ltk; auto. (* Hint Unfold devrait rendre ce unfold inutile ? *)
  Qed.  

   Lemma eqk_not_ltk : forall x x', eqk x x' -> ~ltk x x'.
     unfold eqk, ltk; auto.
   Qed.
   Hint Resolve ltk_not_eqk eqk_not_ltk. 

   Lemma ltk_eqk : forall e e' e'', ltk e e' -> eqk e' e'' -> ltk e e''.
      eauto.
   Qed.
   Hint Resolve ltk_eqk.

   Hint Resolve MX.eq_lt MX.lt_eq.

   Lemma eqk_ltk : forall e e' e'', ltk e e'' -> eqk e e' -> ltk e' e''.
      intros (k,e) (k',e') (k'',e'').
      unfold ltk, eqk; eauto.
   Qed.
   Hint Resolve eqk_ltk.

   (* eqke is a stricter equality than eqk *)
 
   Lemma eqke_eqk : forall x x', eqke x x' -> eqk x x'.
     unfold eqk, eqke; intuition.
   Qed.
   Hint Resolve eqke_eqk.

  (* ltk ignore the second components *)

   Lemma ltk_right_r : forall x k e e', ltk x (k,e) -> ltk x (k,e').
      auto.
    Qed.
    Hint Resolve ltk_right_r.

    Lemma ltk_right_l : forall x k e e', ltk (k,e) x -> ltk (k,e') x.
      auto.
    Qed.
    Hint Resolve ltk_right_l.


  Definition MapsTo (k:key)(e:elt):= InList eqke (k,e).
  Definition In k m := exists e:elt, MapsTo k e m.

  Hint Unfold MapsTo In.

  Lemma InList_eqke_eqk : 
     forall x m, InList eqke x m -> InList eqk x m.
  Proof.
    induction 1; sintuition.
  Qed.
  Hint Resolve InList_eqke_eqk.

  (* An alternative formulation for [In k l] is [exists e, InList eqk (k,e) l] *)

  Lemma InList_eqk_In : forall k e l, InList eqk (k,e) l -> In k l.
  Proof.
     induction 1.
     destruct y.
     exists e0.
     eauto.
     induction IHInList.
     exists x;eauto.
  Qed.
  Hint Resolve InList_eqk_In.

  Lemma In_InList_eqk : forall k e l, In k l -> InList eqk (k,e) l.
  Proof.
     induction 1.
     induction H; simpl; sintuition.
  Qed.
  Hint Resolve In_InList_eqk.

  Lemma altern_In : forall k l, In k l <-> exists e:elt, InList eqk (k,e) l.
  Proof.
   split.
   destruct 1. 
   exists x; auto. 
   intros (x,H); eauto.
  Qed.

(*
    (* could also be proved as a corollary of previous lemma *)
    Lemma InList_In : forall k e l, InList eqke (k,e) l -> In k l.
      intros k e l H. exists e;auto.
    Qed.
    Hint Resolve InList_In.
*)

    Lemma notin_empty : forall k, ~ In k [].
      intros k abs.
      inversion abs.
      inversion H.
    Qed.
    Hint Resolve notin_empty.


    Notation Sort := (sort ltk).
    Notation Inf := (lelistA ltk).

    Hint Resolve nil_sort cons_sort.

    Lemma lt_sort_tl : forall e l, Sort (e::l) -> Sort l.
      intros e l sorted.
      inversion sorted.
      inversion H1; auto.
    Qed.
     Hint Resolve lt_sort_tl.

    Lemma lt_sort_tl2 : forall e e' l, Sort (e::e'::l) -> Sort (e::l).
      intros e e' l sorted.
      inversion sorted.
      inversion H1.
      apply cons_sort.
      assumption.
      inversion H6.
      apply nil_leA.
      apply cons_leA.
      subst.
      apply ltk_trans with e';auto.
      inversion sorted.
      inversion H4.
      assumption.
    Qed.
    Hint Resolve lt_sort_tl2.

    Lemma all_lt_Inf: forall x l, 
      (forall e, InList eqke e l -> ltk x e) -> Inf x l.
      destruct l;auto.
    Qed.
    Hint Resolve all_lt_Inf.

    Lemma sort_in_tl : forall e l e', Sort (e::l) -> InList eqk e' l -> ltk e e'.
      intros e l e' sorted Hin.
      induction Hin;eauto.

      apply ltk_eqk with y;eauto.
      inversion sorted.
      subst.
      inversion H3;eauto.
    Qed.

    Lemma sort_in : forall l e e', Sort (e::l) -> InList eqk e' (e::l) 
      -> ltk e e' \/ eqk e e'.
      intros l e e' sorted Hin.
      inversion Hin;eauto.
      left.
      apply sort_in_tl with l;assumption.
    Qed.

    Lemma sort_lt_notin : forall l k e, Sort l -> Inf (k,e) l ->  ~In k l.
      intros l k e sorted Hlt.
      inversion Hlt.
      intro abs. inversion abs. inversion H0. 
      intro Hin. subst.
      inversion Hin.
      assert (ltk b (k,x) \/ eqk b (k,x)).
      eapply sort_in with l0. auto.
      auto.
      decompose [or] H1;clear H1.
      assert (ltk (k,x) b).
      apply ltk_right_l with e;assumption.
      absurd (ltk b (k, x));auto.
      destruct b.
      unfold ltk; simpl.
      apply MX.lt_not_gt;auto.

      destruct b.
      unfold eqk in H2; simpl in H2.
      unfold ltk in H; simpl in H.
      absurd (X.eq k0 k); simpl;eauto.
    Qed.
    Hint Resolve sort_lt_notin.

(*
    Lemma sort_lt_notin2 : forall l k e, Sort l -> Inf (k,e) l -> 
          ~(exists e:elt, InList eqk (k,e) l).
    Proof.
      intros.
      generalize (altern_In k l).
      generalize (sort_lt_notin H H0).
      intuition.
    Qed.
*)

    Lemma sorted_unique: forall l, Sort l -> Unique eqk l.
      intros l sorted.
      induction sorted;auto.
      apply Unique_cons;auto.
      destruct a;auto.
      assert (abs:~In k l).
      eapply sort_lt_notin with e;auto.
      intro abs2.
      elim abs.
      eauto.
    Qed.

(*
    Lemma sorted_unique_key_eq: forall l, Unique eqk l -> Unique eqke l.
      induction 1;auto.
    Qed.
*)

    Lemma Inf_eq : forall x x' l, eqk x x' -> Inf x l -> Inf x' l.
    Proof.  
     intros x x' l H H0.
     inversion H0; eauto.
    Qed.

    Lemma Inf_lt : forall x x' l, ltk x x' -> Inf x' l -> Inf x l.
    Proof.
     induction 2; auto.
     constructor.
     eapply ltk_trans; eauto.
   Qed.     

   Hint Resolve Inf_eq Inf_lt.

   Lemma sorted_in_cons_not_eq : forall x l k e, Sort ((k,e)::l) -> In x l -> ~X.eq x k.
      intros x l k e sorted.
      inversion_clear sorted.
      intros Hin.
      intro abs.
      absurd (In x l);auto.
      eapply sort_lt_notin with e;auto.      
      eapply Inf_eq with (k,e);simpl;auto.
    Qed.

    Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> X.eq k k' \/ In k l.
      intros k k' e l H.
      inversion H.
      inversion_clear H0; unfold eqke in H1; simpl in *; intuition; eauto.
    Qed.      

    Lemma In_inv2 : forall x x' l, 
      InList eqk x (x' :: l) -> eqk x x' \/ InList eqk x l.
      intros x x' l inlist.
      inversion inlist;auto.
    Qed.

    Lemma In_inv3 : forall x x' l, 
      InList eqke x (x' :: l) -> eqke x x' \/ InList eqke x l.
      intros x x' l inlist.
      inversion inlist;auto.
    Qed.

    Lemma In_inv4 : forall k k' e e' l, 
      InList eqk (k, e) ((k', e') :: l) -> ~ X.eq k k' -> InList eqk (k, e) l.
      intros k k' e e' l H H0.
      elim (@In_inv2 (k,e) (k',e') l);intros;auto.
      elim H0;auto.
    Qed.

    Lemma In_inv5 : forall x x' l, 
      InList eqke x (x' :: l) -> ~ eqk x x' -> InList eqke x l.
      intros x x' l H H0.
      induction (@In_inv3 x x' l);auto. 
      elim H0.
      unfold eqke in *; unfold eqk; intuition.
    Qed.

    Lemma InList_eqk : forall x x' l, 
      InList eqk x l -> eqk x x' -> InList eqk x' l.
      intros x x' l H H0.
      induction H;eauto.
    Qed.

    Hint Resolve In_inv4 In_inv5.

   (** end of auxiliary results *)

    Definition empty : t elt := [].

    (** Specification of [empty] *)

    Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

    Lemma empty_1 : Empty empty.
      unfold Empty,empty,MapsTo.
      intros a e.
      intro abs.
      inversion abs.
    Qed.

    Hint Resolve empty_1.

    Lemma empty_sorted : Sort empty.
    Proof. 
     unfold empty; auto.
    Qed.

    Definition is_empty (l : t elt) : bool := if l then true else false.

    (** Specification of [is_empty] *)

    Lemma is_empty_1 :forall m, Empty m -> is_empty m = true. 
      unfold Empty,MapsTo.
      intros m.
      case m;auto.
      intros p l inlist.
      destruct p.
      absurd (InList eqke (k, e) ((k, e) :: l));auto.
    Qed.


    Lemma is_empty_2 : forall m, is_empty m = true -> Empty m.
      intros m.
      case m;auto.
      intros p l abs.
      inversion abs.
    Qed.


    Fixpoint mem (k : key) (s : t elt) {struct s} : bool :=
      match s with
	| [] => false
	| (k',_) :: l =>
          match X.compare k k' with
            | Lt _ => false
            | Eq _ => true
            | Gt _ => mem k l
          end
      end.
    
    (** Specification of [mem] *)

    Lemma mem_1 : forall m (Hm:Sort m) x, In x m -> mem x m = true.
      intros m Hm x; generalize Hm; clear Hm.      
      functional induction mem x m;intros sorted belong1;trivial.
      
      inversion belong1. inversion H.
      
      absurd (In k ((k', e) :: l));try assumption.
      eapply sort_lt_notin with e;auto.

      apply H.
      elim (sort_inv sorted);auto.
      elim (In_inv belong1);auto.
      intro abs.
      absurd (X.eq k k');auto.
    Qed. 


    Lemma mem_2 : forall m (Hm:Sort m) x, mem x m = true -> In x m. 
      intros m Hm x; generalize Hm; clear Hm; unfold In,MapsTo.
      functional induction mem x m; intros sorted hyp;try ((inversion hyp);fail).
      exists e;eauto. 
      induction H; eauto.
    Save.


    Fixpoint find (k:key) (s: t elt) {struct s} : option elt :=
      match s with
	| [] => None
	| (k',x)::s' => 
	  match X.compare k k' with
	    | Lt _ => None
	    | Eq _ => Some x
	    | Gt _ => find k s'
	  end
      end.

    (** Specification of [find] *)

    Lemma find_2 :  forall m x e, find x m = Some e -> MapsTo x e m.
      intros m x. unfold MapsTo.
      functional induction find x m;simpl;intros e' eqfind; inversion eqfind; auto.
    Qed.

    Lemma find_1 :  forall m (Hm:Sort m) x e, MapsTo x e m -> find x m = Some e. 
      intros m Hm x e; generalize Hm; clear Hm; unfold MapsTo.
      functional induction find x m;simpl; subst; try clear H_eq_1.

      inversion 2.

      intros; elimtype False.
      inversion_clear H.
      absurd (X.eq k k'); auto.
      unfold eqke in H0; simpl in H0; intuition. 
      assert (H2 := sort_in_tl Hm (InList_eqke_eqk H0)).
      unfold ltk in H2; simpl in H2; intuition. 
      absurd (X.lt k k'); auto.
    
     intros.
     inversion_clear H.
     unfold eqke in H0; simpl in H0; intuition congruence. 
     assert (H2 := sort_in_tl Hm (InList_eqke_eqk H0)).
     unfold ltk in H2; simpl in H2; intuition. 
     absurd (X.eq k k'); auto.

     intros.
     inversion_clear H0.
     absurd (X.eq k k'); auto.
     unfold eqke in H1; simpl in H1; intuition.
     eauto.
    Qed.


    Fixpoint add (k : key) (x : elt) (s : t elt) {struct s} : t elt :=
      match s with
	| [] => (k,x) :: []
	| (k',y) :: l =>
          match X.compare k k' with
            | Lt _ => (k,x)::s
            | Eq _ => (k,x)::l
            | Gt _ => (k',y) :: add k x l
          end
      end.


    (** Specification of [add] *)

    Lemma add_1 : forall m x y e, X.eq y x -> MapsTo y e (add x e m).
      intros m x y e; generalize y; clear y.
      unfold MapsTo.
      functional induction add x e m;simpl;auto.
    Qed.

    Lemma add_2 : forall m x y e e', 
      ~ X.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
      intros m x  y e e'. 
      generalize y e; clear y e; unfold MapsTo.
      functional induction add x e' m;simpl;auto.
      intros y' e' eqky' mapsto1.
      
      assert (InList eqke (y', e') l); intuition; eauto.

      intros y' e' eqky' mapsto1.
      elim (@In_inv3 (y',e') (k',y) l);auto.
    Qed.
      
    Lemma add_3 : forall m x y e e',
      ~ X.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
      intros m x y e e'. generalize y e; clear y e; unfold MapsTo.
      functional induction add x e' m;simpl;eauto.
      intros e' y' eqky' Hinlist.
      inversion Hinlist;eauto.
    Qed.

   Lemma add_Inf :
     forall (m : t elt) (x x':key)(e e':elt), Inf (x',e') m -> ltk (x',e') (x,e) -> Inf (x',e') (add x e m).
   Proof.
     induction m.  
     simpl; intuition.
     intros.
     destruct a as (x'',e'').
     inversion_clear H.
     unfold ltk in H0,H1; simpl in H0, H1.
     simpl; case (X.compare x x''); intuition.
  Qed.
  Hint Resolve add_Inf.

  Lemma add_sorted : forall m (Hm:Sort m) x e, Sort (add x e m).
  Proof.
  induction m.
  simpl; intuition.
  intros.
  destruct a as (x',e').
  simpl; case (X.compare x x'); intuition; inversion_clear Hm; auto.
  constructor; auto.
  apply Inf_eq with (x',e'); auto.
  Qed.  

  Fixpoint remove (k : key) (s : t elt) {struct s} : t elt :=
      match s with
	| [] => []
	| (k',x) :: l =>
          match X.compare k k' with
            | Lt _ => s
            | Eq _ => l
            | Gt _ => (k',x) :: remove k l
          end
      end.  


   (** Specification of [remove] *)

    Lemma remove_1 : forall m (Hm:Sort m) x y, X.eq y x -> ~ In y (remove x m).
      intros m Hm x y; generalize Hm; clear Hm.
      functional induction remove x m;simpl;intros;auto.

      subst.
      eapply sort_lt_notin with x.
      eauto.
      apply cons_leA;simpl.
      unfold ltk; eapply MX.lt_eq;eauto.
      
      eapply sort_lt_notin with x. eauto. 
      inversion Hm.
      eapply Inf_eq with (k',x) ;simpl;auto.
      intuition; eauto.

      assert (notin:~ In y (remove k l)). apply H;eauto.
      intros (x0,abs).
      inversion_clear abs; eauto. 
      simpl_eqke; simpl in *; subst.
      absurd (X.eq y k');eauto.
      Qed.
      
      
    Lemma remove_2 : forall m (Hm:Sort m) x y e, 
      ~ X.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
      intros m Hm x y e; generalize Hm; clear Hm; unfold MapsTo.
      functional induction remove x m;auto.
      intros sorted noteqky inlist.
      elim (@In_inv3 (y, e) (k', x) l);auto;simpl;intuition;eauto.
      intros sorted noteqky inlist.
      elim (@In_inv3 (y, e) (k', x) l); auto. 
      intro inlist2.

      assert (InList eqke (y, e) (remove k l));auto.
      apply H;auto.
      eauto.
    Qed.


    Lemma remove_3 : forall m (Hm:Sort m) x y e, MapsTo y e (remove x m) -> MapsTo y e m.
      intros m Hm x y e; generalize Hm; clear Hm; unfold MapsTo.
      functional induction remove x m;auto.
      intros sorted inlist.
      elim (@In_inv3 (y, e) (k', x) (remove k l)); auto.
      intros inlist2.
      eauto.
    Qed.

   Lemma remove_Inf :
     forall (m : t elt) (Hm : Sort m)(x x':key)(e':elt), Inf (x',e') m -> Inf (x',e') (remove x m).
   Proof.
     induction m.  
     simpl; intuition.
     intros.
     destruct a as (x'',e'').
     inversion_clear H.
     unfold ltk in H0; simpl in H0.
     simpl; case (X.compare x x''); intuition.
     inversion_clear Hm.
     eapply Inf_lt; eauto.
     unfold ltk; auto.
  Qed.
  Hint Resolve remove_Inf.

  Lemma remove_sorted : forall m (Hm:Sort m) x, Sort (remove x m).
  Proof.
  induction m.
  simpl; intuition.
  intros.
  destruct a as (x',e').
  simpl; case (X.compare x x'); intuition; inversion_clear Hm; auto.
  Qed.  


    (** Specification of [MapsTo] *)

    Lemma MapsTo_1 : forall m x y e, X.eq x y -> MapsTo x e m -> MapsTo y e m.
      unfold MapsTo.
      intros m x y e eqxy inlist.
      induction inlist;eauto.

      apply InList_cons_hd;auto.
      eapply eqke_trans with (x, e);auto.
    Qed.

    Definition elements (m: t elt) := m.

    Lemma elements_1 : forall m x e, 
        MapsTo x e m -> InList eqke (x,e) (elements m).
    Proof.
    auto.
    Qed.

    Lemma elements_2 : forall m x e, 
        InList eqke (x,e) (elements m) -> MapsTo x e m.
    Proof. 
    auto.
    Qed.

    Lemma elements_3 : forall m (Hm:Sort m),
       sort ltk (elements m). 
    Proof. 
    auto.
    Qed.

    Fixpoint fold (A:Set) (f:key -> elt -> A -> A) (m:t elt) {struct m} : A -> A :=
      fun acc => 
      match m with
	| [] => acc
	| (k,e)::m' => fold f m' (f k e acc)
      end.

    Lemma fold_1 : 
	forall m (A : Set) (i : A) (f : key -> elt -> A -> A),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
     Proof. 
     intros; functional induction fold A f m i; auto.
     Qed.

     Fixpoint equal (cmp: elt -> elt -> bool)(m m' : t elt) { struct m } : bool := 
       match m, m' with 
        | [], [] => true
        | (x,e)::l, (x',e')::l' => 
            match X.compare x x' with 
             | Eq _ => cmp e e' && equal cmp l l'
             | _       => false
            end 
        | _, _ => false 
       end.

     Definition Equal cmp m m' := 
         (forall k, In k m <-> In k m') /\ 
         (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).  

     (** Specification of [equal] *)
        Lemma equal_1 : forall m (Hm:Sort m) m' (Hm': Sort m') cmp, 
           Equal cmp m m' -> equal cmp m m' = true. 
        Proof. 
        intros m Hm m' Hm' cmp; generalize Hm Hm'; clear Hm Hm'.
        functional induction equal cmp m m'; simpl; auto; unfold Equal; intuition.

        destruct p as (k,e).
        destruct (H0 k).
        destruct H2.
        exists e; auto.
        inversion H2.

        destruct (H0 x).
        destruct H.
        exists e; auto.
        inversion H.

        subst; clear H_eq_3.
        destruct (H0 x).
        assert (In x ((x',e')::l')). 
          apply H; auto.
          exists e; auto.
        destruct (In_inv H3).
        absurd (X.lt x x'); eauto.
        inversion_clear Hm'.
        assert (Inf (x,e) l').
        eapply Inf_lt; eauto; auto. (* eauto n'est pas strictement plus fort que auto ??! *)
        elim (sort_lt_notin H5 H7 H4).
        
        subst.
        assert (cmp e e' = true).
          apply H2 with x; auto.
        rewrite H0; simpl.
       apply H; auto.
       inversion_clear Hm; auto.
       inversion_clear Hm'; auto.
       unfold Equal; intuition.
       destruct (H1 k).
       assert (In k ((x,e) ::l)).
         destruct H3 as (e'', hyp); exists e''; auto.
       destruct (In_inv (H4 H6)); auto.
       inversion_clear Hm.
       elim (sort_lt_notin H8 H9).
       destruct H3 as (e'', hyp); exists e''; auto.
       apply MapsTo_1 with k; eauto.
       destruct (H1 k).
       assert (In k ((x',e') ::l')).
         destruct H3 as (e'', hyp); exists e''; auto.
       destruct (In_inv (H5 H6)); auto.
       inversion_clear Hm'.
       elim (sort_lt_notin H8 H9).
       destruct H3 as (e'', hyp); exists e''; auto.
       apply MapsTo_1 with k; eauto.
       apply H2 with k; destruct (MX.eq_dec x k); auto.

        subst; clear H_eq_3.
        destruct (H0 x').
        assert (In x' ((x,e)::l)). 
          apply H2; auto.
          exists e'; auto.
        destruct (In_inv H3).
        absurd (X.lt x' x); eauto.
        inversion_clear Hm.
        assert (Inf (x',e') l).
        eapply Inf_lt; eauto; auto. (* eauto n'est pas strictement plus fort que auto ??! *)
        elim (sort_lt_notin H5 H7 H4).
     Qed.

      Lemma equal_2 : forall m (Hm:Sort m) m' (Hm:Sort m') cmp, 
         equal cmp m m' = true -> Equal cmp m m'.
      Proof.
       intros m Hm m' Hm' cmp; generalize Hm Hm'; clear Hm Hm'.
       functional induction equal cmp m m'; simpl; auto; unfold Equal; intuition; try discriminate; subst.
       inversion H0.

       destruct (andb_prop _ _ H0); clear H0.
       inversion_clear Hm; inversion_clear Hm'.
       destruct (H H0 H5 H3).
       destruct (In_inv H1).
       exists e'; eauto.
       destruct (H7 k).
       destruct (H10 H9) as (e'',hyp).
       exists e''; eauto.

       destruct (andb_prop _ _ H0); clear H0.
       inversion_clear Hm; inversion_clear Hm'.
       destruct (H H0 H5 H3).
       destruct (In_inv H1).
       exists e; eauto.
       destruct (H7 k).
       destruct (H11 H9) as (e'',hyp).
       exists e''; eauto.

       destruct (andb_prop _ _ H0); clear H0.
       inversion_clear Hm; inversion_clear Hm'.
       destruct (H H0 H6 H4).
       inversion_clear H1.
       simpl_eqke; simpl in *; subst.
       inversion_clear H2. 
       simpl_eqke; simpl in *; subst; auto.
       elim (sort_lt_notin H6 H7).
       exists e'0; apply MapsTo_1 with k; eauto.
       inversion_clear H2. 
       simpl_eqke; simpl in *; subst; auto.
       elim (sort_lt_notin H0 H5).
       exists e1; apply MapsTo_1 with k; eauto.
       apply H9 with k; eauto.
      Qed. 

      Variable elt':Set.
      
      Fixpoint map (f:elt -> elt') (m:t elt) {struct m} : t elt' :=
	match m with
	  | [] => []
	  | (k,e)::m' => (k,f e) :: map f m'
	end.

      Fixpoint mapi (f: key -> elt -> elt') (m:t elt) {struct m} : t elt' :=
	match m with
	  | [] => []
	  | (k,e)::m' => (k,f k e) :: mapi f m'
	end.

      End Elt.
      Section Elt2. 
      (* For previous definitions to work with different [elt], especially [MapsTo]... *)
      
      Variable elt elt' : Set.

    (** Specification of [map] *)

      Lemma map_1 : forall (m:t elt)(x:key)(e:elt)(f:elt->elt'), 
        MapsTo x e m -> MapsTo x (f e) (map f m).
      Proof.
	intros m x e f.
	(* functional induction map elt elt' f m.  *) (* Marche pas ??? *)
        induction m.
        inversion 1.
        
        destruct a as (x',e').
        simpl. 
        inversion_clear 1.
        constructor 1.
        unfold eqke in *; simpl in *; intuition congruence.
        constructor 2.
        unfold MapsTo in *; auto.
      Qed.

      Lemma map_2 : forall (m:t elt)(x:key)(f:elt->elt'), 
        In x (map f m) -> In x m.
      Proof.
	intros m x f. 
        (* functional induction map elt elt' f m. *) (* Marche pas ??? *)
        induction m; simpl.
        intros (e,abs).
        inversion abs.
        
        destruct a as (x',e).
	intros hyp.
	inversion hyp. clear hyp.
	inversion H; subst; rename x0 into e'.
        exists e; constructor.
        unfold eqke in *; simpl in *; intuition.
        destruct IHm as (e'',hyp).
        exists e'; auto.
        exists e''.
        constructor 2; auto.
      Qed.

      Lemma map_lelistA : 
         forall (m: t elt)(x:key)(e:elt)(e':elt')(f:elt->elt'),
         lelistA (@ltk elt) (x,e) m -> 
         lelistA (@ltk elt') (x,e') (map f m).
      Proof. 
        induction m; simpl; auto.
        intros.
        destruct a as (x0,e0).
        inversion_clear H; auto.
      Qed.

      Hint Resolve map_lelistA.

      Lemma map_sorted : 
         forall (m: t elt)(Hm : sort (@ltk elt) m)(f:elt -> elt'), 
         sort (@ltk elt') (map f m).
      Proof.   
      induction m; simpl; auto.
      intros.
      destruct a as (x',e').
      inversion_clear Hm; eauto.
      Qed.      
      
 
    (** Specification of [mapi] *)

      Lemma mapi_1 : forall (m:t elt)(x:key)(e:elt)
        (f:key->elt->elt'), MapsTo x e m -> 
        exists y, X.eq y x /\ MapsTo x (f y e) (mapi f m).
      Proof.
	intros m x e f.
	(* functional induction mapi elt elt' f m. *) (* Marche pas ??? *)
        induction m.
        inversion 1.
        
        destruct a as (x',e').
        simpl. 
        inversion_clear 1.
        exists x'.
        destruct H0; simpl in *.
        split; auto.
        constructor 1.
        unfold eqke in *; simpl in *; intuition congruence.
        destruct IHm as (y, hyp); auto.
        exists y; intuition.
        constructor 2.
        unfold MapsTo in *; auto.
      Qed.  


      Lemma mapi_2 : forall (m:t elt)(x:key)
        (f:key->elt->elt'), In x (mapi f m) -> In x m.
      Proof.
	intros m x f. 
        (* functional induction mapi elt elt' f m. *) (* Marche pas ??? *)
        induction m; simpl.
        intros (e,abs).
        inversion abs.
        
        destruct a as (x',e).
	intros hyp.
	inversion hyp. clear hyp.
	inversion H; subst; rename x0 into e'.
        exists e; constructor.
        unfold eqke in *; simpl in *; intuition.
        destruct IHm as (e'',hyp).
        exists e'; auto.
        exists e''.
        constructor 2; auto.
      Qed.

      Lemma mapi_lelistA : 
         forall (m: t elt)(x:key)(e:elt)(f:key->elt->elt'),
         lelistA (@ltk elt) (x,e) m -> 
         lelistA (@ltk elt') (x,f x e) (mapi f m).
      Proof. 
        induction m; simpl; auto.
        intros.
        destruct a as (x',e').
        inversion_clear H; auto.
      Qed.

      Hint Resolve mapi_lelistA.

      Lemma mapi_sorted : 
         forall (m: t elt)(Hm : sort (@ltk elt) m)(f: key ->elt -> elt'), 
         sort (@ltk elt') (mapi f m).
      Proof.
      induction m; simpl; auto.
      intros.
      destruct a as (x',e').
      inversion_clear Hm; auto.
      Qed.

    End Elt2. 
    Section Elt3.

      Variable elt elt' elt'' : Set.
      Variable f : option elt -> option elt' -> option elt''.

      Definition option_cons (A:Set)(k:key)(o:option A)(l:list (key*A)) := 
         match o with 
           | Some e => (k,e)::l
           | None => l
         end.

      Fixpoint map2_l (m : t elt) : t elt'' := 
        match m with 
          | [] => [] 
          | (k,e)::l => option_cons k (f (Some e) None) (map2_l l)
        end. 

      Fixpoint map2_r (m' : t elt') : t elt'' := 
        match m' with 
          | [] => [] 
          | (k,e')::l' => option_cons k (f None (Some e')) (map2_r l')
        end. 

      Fixpoint map2 (m : t elt) : t elt' -> t elt'' :=
        match m with
          | [] => map2_r 
          | (k,e) :: l =>
            fix map2_aux (m' : t elt') : t elt'' :=
              match m' with
                | [] => map2_l m
                | (k',e') :: l' =>
                  match X.compare k k' with
                    | Lt _ => option_cons k (f (Some e) None) (map2 l m')
                    | Eq _ => option_cons k (f (Some e) (Some e')) (map2 l l')
                    | Gt _ => option_cons k' (f None (Some e')) (map2_aux l')
                  end
              end
        end.      

     Fixpoint combine (m : t elt) : t elt' -> t (option elt * option elt') :=
        match m with
          | [] => map (fun e' => (None,Some e'))
          | (k,e) :: l =>
            fix combine_aux (m' : t elt') : list (key * (option elt * option elt')) :=
              match m' with
                | [] => map (fun e => (Some e,None)) m
                | (k',e') :: l' =>
                  match X.compare k k' with
                    | Lt _ => (k,(Some e, None))::combine l m'
                    | Eq _ => (k,(Some e, Some e'))::combine l l'
                    | Gt _ => (k',(None,Some e'))::combine_aux l'
                  end
              end
        end. 

    Definition fold_right_pair (A B C:Set)(f: A -> B -> C -> C)(l:list (A*B))(i:C) := 
           List.fold_right (fun p => f (fst p) (snd p)) i l.

    Definition map2_alt m m' := 
      let m0 : t (option elt * option elt') := combine m m' in 
      let m1 : t (option elt'') := map (fun p => f (fst p) (snd p)) m0 in 
      fold_right_pair (option_cons (A:=elt'')) m1 nil.

    Lemma map2_alt_equiv : 
      forall m m', map2_alt m m' = map2 m m'.
    Proof.
    unfold map2_alt.
    induction m.
    simpl; auto; intros.
    (* map2_r *)
    induction m'; try destruct a; simpl; auto.
    rewrite IHm'; auto.
    (* fin map2_r *)
    induction m'; destruct a.
    simpl; f_equal.
    (* map2_l *)
    clear IHm.
    induction m; try destruct a; simpl; auto.
    rewrite IHm; auto.
    (* fin map2_l *)
    destruct a0.
    simpl.
    destruct (X.compare t0 t1); simpl; f_equal.
    apply IHm.
    apply IHm.
    apply IHm'.
    Qed.

   Lemma combine_lelistA : 
      forall (m: t elt)(m': t elt')(x:key)(e:elt)(e':elt')(e'':option elt * option elt'), 
        lelistA (@ltk elt) (x,e) m -> 
        lelistA (@ltk elt') (x,e') m' -> 
        lelistA (@ltk (option elt * option elt')) (x,e'') (combine m m').
    Proof.
    induction m. 
    intros.
    simpl.
    eapply map_lelistA; eauto.
    induction m'. 
    intros.
    destruct a.
    replace (combine ((t0, e0) :: m) []) with 
                 (map (fun e => (Some e,None (A:=elt'))) ((t0,e0)::m)); auto.
    eapply map_lelistA; eauto.
    intros.
    simpl.
    destruct a as (k,e0); destruct a0 as (k',e0').
    destruct (X.compare k k').
    inversion_clear H; auto.
    inversion_clear H; auto.
    inversion_clear H0; auto.
    Qed.
    Hint Resolve combine_lelistA.

    Lemma combine_sorted : 
      forall (m: t elt)(Hm : sort (@ltk elt) m)(m': t elt')(Hm' : sort (@ltk elt') m'), 
      sort (@ltk (option elt * option elt')) (combine m m').
    Proof.
    induction m. 
    intros; clear Hm.
    simpl.
    apply map_sorted; auto.
    induction m'. 
    intros; clear Hm'.
    destruct a.
    replace (combine ((t0, e) :: m) []) with 
                 (map (fun e => (Some e,None (A:=elt'))) ((t0,e)::m)); auto.
    apply map_sorted; auto.
    intros.
    simpl.
    destruct a as (k,e); destruct a0 as (k',e').
    destruct (X.compare k k').
    inversion_clear Hm.
    constructor; auto.
    eapply combine_lelistA with (e':=e'); eauto.
    inversion_clear Hm; inversion_clear Hm'.
    constructor; eauto.
    eapply combine_lelistA with (e':=e'); eauto.
    eapply Inf_eq; eauto; red; eauto.
    inversion_clear Hm; inversion_clear Hm'.
    constructor; auto.
    change (lelistA (ltk (elt:=option elt * option elt')) (k', (None, Some e'))
                     (combine ((k,e)::m) m')).
    eapply combine_lelistA with (e:=e); eauto.
    Qed.
    
    Lemma map2_sorted : 
      forall (m: t elt)(Hm : sort (@ltk elt) m)(m': t elt')(Hm' : sort (@ltk elt') m'), 
      sort (@ltk elt'') (map2 m m').
     Proof.
     intros.
     rewrite <- map2_alt_equiv.
     unfold map2_alt.
     assert (H0:=combine_sorted Hm Hm').
     set (l0:=combine m m') in *; clearbody l0.
     set (f':= fun p : option elt * option elt' => f (fst p) (snd p)).
     assert (H1:=map_sorted (elt' := option elt'') H0 f').
     set (l1:=map f' l0) in *; clearbody l1. 
     clear f' f H0 l0 Hm Hm' m m'.
     induction l1.
     simpl; auto.
     inversion_clear H1.
     destruct a; destruct o; auto.
     simpl.
     constructor; auto.
     clear IHl1.
     induction l1.
     simpl; auto.
     destruct a; destruct o; simpl; auto.
     inversion_clear H0; auto.
     inversion_clear H0.
     red in H1; simpl in H1.
     inversion_clear H.
     apply IHl1; auto.
     eapply Inf_lt; eauto.
     red; auto.
     Qed.
     
     Definition at_least_one (o:option elt)(o':option elt') := 
         match o, o' with 
           | None, None => None 
           | _, _  => Some (o,o')
         end.

    Lemma combine_1 : 
      forall (m: t elt)(Hm : sort (@ltk elt) m)(m': t elt')(Hm' : sort (@ltk elt') m') 
      (x:key), 
      find x (combine m m') = at_least_one (find x m) (find x m'). 
    Proof.
    induction m.
    intros.
    simpl.
    induction m'.
    intros; simpl; auto.
    simpl; destruct a.
    simpl; destruct (X.compare x t0); simpl; auto.
    inversion_clear Hm'; auto.
    induction m'.
    (* m' = [] *)
    intros; destruct a; simpl.
    destruct (X.compare x t0); simpl; auto.
    inversion_clear Hm; clear H0 l Hm' IHm t0.
    induction m; simpl; auto.
    inversion_clear H.
    destruct a.
    simpl; destruct (X.compare x t0); simpl; auto.
    (* m' <> [] *)
    intros.
    destruct a as (k,e); destruct a0 as (k',e'); simpl.
    inversion Hm; inversion Hm'; subst.
    destruct (X.compare k k'); simpl;
      destruct (X.compare x k); 
        MX.compare || destruct (X.compare x k'); simpl; auto.
    rewrite IHm; auto; simpl; MX.compare; auto.
    rewrite IHm; auto; simpl; MX.compare; auto.
    rewrite IHm; auto; simpl; MX.compare; auto.
    change ((find x (combine ((k, e) :: m) m')) = at_least_one None (find x m')).
    rewrite IHm'; auto. 
    simpl find; MX.compare; auto.
    change ((find x (combine ((k, e) :: m) m')) = Some (Some e, find x m')).
    rewrite IHm'; auto. 
    simpl find; MX.compare; auto.
    change ((find x (combine ((k, e) :: m) m')) = at_least_one (find x m) (find x m')).
    rewrite IHm'; auto. 
    simpl find; MX.compare; auto.
    Qed.

    Definition at_least_one_then_f (o:option elt)(o':option elt') := 
         match o, o' with 
           | None, None => None 
           | _, _  => f o o'
         end.

    Lemma map2_0 : 
      forall (m: t elt)(Hm : sort (@ltk elt) m)(m': t elt')(Hm' : sort (@ltk elt') m') 
      (x:key), 
      find x (map2 m m') = at_least_one_then_f (find x m) (find x m'). 
    Proof.
    intros.
    rewrite <- map2_alt_equiv.
    unfold map2_alt.
    assert (H:=combine_1 Hm Hm' x).
    assert (H2:=combine_sorted Hm Hm').
    set (f':= fun p : option elt * option elt' => f (fst p) (snd p)).
    set (m0 := combine m m') in *; clearbody m0.
    set (o:=find x m) in *; clearbody o. 
    set (o':=find x m') in *; clearbody o'.
    clear Hm Hm' m m'.
    generalize H; clear H.
    match goal with |- ?g => 
       assert (g /\ (find x m0 = None -> 
                           find x (fold_right_pair (option_cons (A:=elt'')) (map f' m0) []) 
                           = None)); 
       [ | intuition ] end.
    induction m0; simpl in *; intuition.
    destruct o; destruct o'; simpl in *; try discriminate; auto.
    destruct a as (k,(oo,oo')); simpl in *.
    inversion_clear H2.
    destruct (X.compare x k); simpl in *.
    (* x < k *)
    destruct (f' (oo,oo')); simpl.
    MX.compare.
    destruct o; destruct o'; simpl in *; try discriminate; auto.
    destruct (IHm0 H0) as (H2,_); apply H2; auto.
    rewrite <- H.
    case_eq (find x m0); intros; auto.
    assert (ltk (elt:=option elt * option elt') (x,(oo,oo')) (k,(oo,oo'))).
     red; auto.
    destruct (sort_lt_notin H0 (Inf_lt H4 H1)).
    exists p; apply find_2; eauto.
    (* x = k *)
    assert (at_least_one_then_f o o' = f oo oo').
      destruct o; destruct o'; simpl in *; inversion_clear H; auto.
    rewrite H2.
    unfold f'; simpl.
    destruct (f oo oo'); simpl.
    MX.compare; auto.
    destruct (IHm0 H0) as (_,H4); apply H4; auto.
    case_eq (find x m0); intros; auto.
    assert (eqk (elt:=option elt * option elt') (k,(oo,oo')) (x,(oo,oo'))).
     red; auto.
    destruct (sort_lt_notin H0 (Inf_eq H5 H1)).
    exists p; apply find_2; eauto.
    (* k < x *)
    unfold f'; simpl.
    destruct (f oo oo'); simpl.
    MX.compare; auto.
    destruct (IHm0 H0) as (H3,_); apply H3; auto.
    destruct (IHm0 H0) as (H3,_); apply H3; auto.

    (* None -> None *)
    destruct a as (k,(oo,oo')).
    simpl.
    inversion_clear H2.
    destruct (X.compare x k).
    (* x < k *)
    unfold f'; simpl.
    destruct (f oo oo'); simpl.
    MX.compare; auto.
    destruct (IHm0 H0) as (_,H4); apply H4; auto.
    case_eq (find x m0); intros; auto.
    assert (ltk (elt:=option elt * option elt') (x,(oo,oo')) (k,(oo,oo'))).
     red; auto.
    destruct (sort_lt_notin H0 (Inf_lt H3 H1)).
    exists p; apply find_2; eauto.
    (* x = k *)
    discriminate.
    (* k < x *)
    unfold f'; simpl.
    destruct (f oo oo'); simpl.
    MX.compare; auto.
    destruct (IHm0 H0) as (_,H4); apply H4; auto.
    destruct (IHm0 H0) as (_,H4); apply H4; auto.
    Qed.

     (** Specification of [map2] *)
     Lemma map2_1 : forall (m: t elt)(Hm : sort (@ltk elt) m)
        (m': t elt')(Hm' : sort (@ltk elt') m')(x:key),
	In x m \/ In x m' -> 
        find x (map2 m m') = f (find x m) (find x m'). 
     Proof.
     intros.
     rewrite map2_0; auto.
     destruct H as [(e,H)|(e,H)].
     rewrite (find_1 Hm H).
     destruct (find x m'); simpl; auto.
     rewrite (find_1 Hm' H).
     destruct (find x m); simpl; auto.
     Qed.
     
     Lemma map2_2 : forall (m: t elt)(Hm : sort (@ltk elt) m)
        (m': t elt')(Hm' : sort (@ltk elt') m')(x:key), 
        In x (map2 m m') -> In x m \/ In x m'. 
     Proof.
     intros.
     destruct H as (e,H).
     generalize (map2_0 Hm Hm' x).
     rewrite (find_1 (map2_sorted Hm Hm') H).
     generalize (@find_2 _ m x).
     generalize (@find_2 _ m' x).
     destruct (find x m); 
       destruct (find x m'); simpl; intros.
     left; exists e0; auto. 
     left; exists e0; auto.
     right; exists e0; auto.
     discriminate.
     Qed.

   End Elt3.

End Raw.

Module Make (X: OrderedType) <: S with Module E := X.
  Module Raw := Raw X. 
  Module E := X.

  Definition key := X.t.

  Record slist (elt:Set) : Set :=  {this :> Raw.t elt; sorted : sort (@Raw.ltk elt) this}.
  Definition t (elt:Set) := slist elt. 

 Section Elt. 
 Variable elt elt' elt'':Set. 

 Implicit Types m : t elt.

 Definition empty := Build_slist (Raw.empty_sorted elt).
 Definition is_empty m := Raw.is_empty m.(this).
 Definition add x e m := Build_slist (Raw.add_sorted m.(sorted) x e).
 Definition find x m := Raw.find x m.(this).
 Definition remove x m := Build_slist (Raw.remove_sorted m.(sorted) x). 
 Definition mem x m := Raw.mem x m.(this).
 Definition map f m : t elt' := Build_slist (Raw.map_sorted m.(sorted) f).
 Definition mapi f m : t elt' := Build_slist (Raw.mapi_sorted m.(sorted) f).
 Definition map2 f m (m':t elt') : t elt'' := 
     Build_slist (Raw.map2_sorted f m.(sorted) m'.(sorted)).
 Definition elements m := @Raw.elements elt m.(this).
 Definition fold A f m i := @Raw.fold elt A f m.(this) i.
 Definition equal cmp m m' := @Raw.equal elt cmp m.(this) m'.(this).

 Definition MapsTo x e m := Raw.MapsTo x e m.(this).
 Definition In x m := Raw.In x m.(this).
 Definition Empty m := Raw.Empty m.(this).
 Definition Equal cmp m m' := @Raw.Equal elt cmp m.(this) m'.(this).

 Definition eq_key (p p':key*elt) := X.eq (fst p) (fst p').
     
 Definition eq_key_elt (p p':key*elt) := 
          X.eq (fst p) (fst p') /\ (snd p) = (snd p').

 Definition lt_key (p p':key*elt) := X.lt (fst p) (fst p').

 Definition MapsTo_1 m := @Raw.MapsTo_1 elt m.(this).

 Definition mem_1 m := @Raw.mem_1 elt m.(this) m.(sorted).
 Definition mem_2 m := @Raw.mem_2 elt m.(this) m.(sorted).

 Definition empty_1 := @Raw.empty_1.

 Definition is_empty_1 m := @Raw.is_empty_1 elt m.(this).
 Definition is_empty_2 m := @Raw.is_empty_2 elt m.(this).

 Definition add_1 m := @Raw.add_1 elt m.(this).
 Definition add_2 m := @Raw.add_2 elt m.(this).
 Definition add_3 m := @Raw.add_3 elt m.(this).

 Definition remove_1 m := @Raw.remove_1 elt m.(this) m.(sorted).
 Definition remove_2 m := @Raw.remove_2 elt m.(this) m.(sorted).
 Definition remove_3 m := @Raw.remove_3 elt m.(this) m.(sorted).

 Definition find_1 m := @Raw.find_1 elt m.(this) m.(sorted).
 Definition find_2 m := @Raw.find_2 elt m.(this).

 Definition elements_1 m := @Raw.elements_1 elt m.(this). 
 Definition elements_2 m := @Raw.elements_2 elt m.(this). 
 Definition elements_3 m := @Raw.elements_3 elt m.(this) m.(sorted). 

 Definition fold_1 m := @Raw.fold_1 elt m.(this).

 Definition map_1 m := @Raw.map_1 elt elt' m.(this).
 Definition map_2 m := @Raw.map_2 elt elt' m.(this).

 Definition mapi_1 m := @Raw.mapi_1 elt elt' m.(this).
 Definition mapi_2 m := @Raw.mapi_2 elt elt' m.(this).

 Definition map2_1 m (m':t elt') x f := 
    @Raw.map2_1 elt elt' elt'' f m.(this) m.(sorted) m'.(this) m'.(sorted) x.
 Definition map2_2 m (m':t elt') x f := 
    @Raw.map2_2 elt elt' elt'' f m.(this) m.(sorted) m'.(this) m'.(sorted) x.

 Definition equal_1 m m' := @Raw.equal_1 elt m.(this) m.(sorted) m'.(this) m'.(sorted).
 Definition equal_2 m m' := @Raw.equal_2 elt m.(this) m.(sorted) m'.(this) m'.(sorted).

 End Elt.
End Make.

Module Make_ord (X: OrderedType)(Data : OrderedType) <: 
    Sord with Module Data := Data 
            with Module MapS.E := X.

  Module Data := Data.
  Module MapS := Make(X). 
  Import MapS.

  Module MD := OrderedTypeFacts(Data).
  Import MD.

  Definition t := MapS.t Data.t. 

  Definition cmp e e' := match Data.compare e e' with Eq _ => true | _ => false end.	

  Fixpoint eq_list (m m' : list (X.t * Data.t)) { struct m } : Prop := 
       match m, m' with 
        | [], [] => True
        | (x,e)::l, (x',e')::l' => 
            match X.compare x x' with 
             | Eq _ => Data.eq e e' /\ eq_list l l'
             | _       => False
            end 
        | _, _ => False
       end.

  Definition eq m m' := eq_list m.(this) m'.(this).

  Fixpoint lt_list (m m' : list (X.t * Data.t)) {struct m} : Prop := match m, m' with 
    | [], [] => False
    | [], _  => True
    | _, []  => False
    | (x,e)::l, (x',e')::l' => 
        match X.compare x x' with 
          | Lt _ => True
          | Gt _ => False
          | Eq _ => Data.lt e e' \/ (Data.eq e e' /\ lt_list l l')
        end
    end.

  Definition lt m m' := lt_list m.(this) m'.(this).

  Lemma eq_equal : forall m m', eq m m' <-> equal cmp m m' = true.
  Proof.
  intros (l,Hl); induction l.
  intros (l',Hl'); unfold eq; simpl.
  destruct l'; unfold equal; simpl; intuition.
  intros (l',Hl'); unfold eq.
  destruct l'.
  destruct a; unfold equal; simpl; intuition.
  destruct a as (x,e).
  destruct p as (x',e').
  unfold equal; simpl. 
  destruct (X.compare x x'); simpl; intuition.
  unfold cmp at 1. 
  MD.compare; clear H; simpl.
  inversion_clear Hl.
  inversion_clear Hl'.
  destruct (IHl H (Build_slist H3)).
  unfold equal, eq in H5; simpl in H5; auto.
  destruct (andb_prop _ _ H); clear H.
  generalize H0; unfold cmp.
  MD.compare; auto; intro; discriminate.
  destruct (andb_prop _ _ H); clear H.
  inversion_clear Hl.
  inversion_clear Hl'.
  destruct (IHl H (Build_slist H3)).
  unfold equal, eq in H6; simpl in H6; auto.
 Qed.

  Lemma eq_1 : forall m m', Equal cmp m m' -> eq m m'.
  intros.
  generalize (@equal_1 Data.t m m' cmp).
  generalize (@eq_equal m m').
  intuition.
  Qed.

  Lemma eq_2 : forall m m', eq m m' -> Equal cmp m m'.
  intros.
  generalize (@equal_2 Data.t m m' cmp).
  generalize (@eq_equal m m').
  intuition.
  Qed.

  Lemma eq_refl : forall m : t, eq m m.
  Proof.
     intros (m,Hm); induction m; unfold eq; simpl; auto.
     destruct a.
     destruct (X.compare t0 t0); auto.
     apply (MapS.Raw.MX.lt_antirefl l); auto.
     split.
     apply Data.eq_refl.
     inversion_clear Hm.
     apply (IHm H).
     apply (MapS.Raw.MX.lt_antirefl l); auto.
  Qed.

  Lemma  eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
  Proof.
     intros (m,Hm); induction m; 
     intros (m', Hm'); destruct m'; unfold eq; simpl;
     try destruct a as (x,e); try destruct p as (x',e'); auto.
     destruct (X.compare x x'); MapS.Raw.MX.compare; intuition.
     inversion_clear Hm; inversion_clear Hm'.
     apply (IHm H0 (Build_slist H4)); auto.
  Qed.

  Lemma eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
     intros (m1,Hm1); induction m1; 
     intros (m2, Hm2); destruct m2; 
     intros (m3, Hm3); destruct m3; unfold eq; simpl; 
     try destruct a as (x,e); 
     try destruct p as (x',e'); 
     try destruct p0 as (x'',e''); try contradiction; auto.
     destruct (X.compare x x'); 
       destruct (X.compare x' x''); 
         MapS.Raw.MX.compare.
     intuition.
     eauto.
     inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm3.
     apply (IHm1 H1 (Build_slist H6) (Build_slist H8)); intuition.
   Qed.

  Lemma lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
  Proof.
     intros (m1,Hm1); induction m1; 
     intros (m2, Hm2); destruct m2; 
     intros (m3, Hm3); destruct m3; unfold lt; simpl; 
     try destruct a as (x,e); 
     try destruct p as (x',e'); 
     try destruct p0 as (x'',e''); try contradiction; auto.
     destruct (X.compare x x'); 
       destruct (X.compare x' x''); 
         MapS.Raw.MX.compare; auto.
    intuition; try solve [left; eauto].
    right.
    split; eauto.
     inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm3.
     apply (IHm1 H2 (Build_slist H6) (Build_slist H8)); intuition.
   Qed.

  Lemma lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.
     intros (m1,Hm1); induction m1; 
     intros (m2, Hm2); destruct m2; unfold eq, lt; simpl; 
     try destruct a as (x,e); 
     try destruct p as (x',e'); try contradiction; auto.
     destruct (X.compare x x'); auto.
     intuition.
     absurd (Data.lt e e'); eauto.
     inversion_clear Hm1; inversion_clear Hm2.
     apply (IHm1 H0 (Build_slist H5)); intuition.
   Qed.

  Definition compare : forall m1 m2, Compare lt eq m1 m2.
    intros (m1,Hm1); induction m1; 
    intros (m2, Hm2); destruct m2.
    apply Eq; unfold eq; simpl; auto.
    apply Lt; unfold lt; simpl; auto.
    apply Gt; unfold lt; simpl; auto. 
    destruct a as (x,e); destruct p as (x',e'). 
    destruct (X.compare x x').
    apply Lt; unfold lt; simpl; 
     destruct (X.compare x x'); auto; absurd (X.lt x x'); eauto.
    destruct (Data.compare e e').
    apply Lt; unfold lt; simpl;
     destruct (X.compare x x'); auto; absurd (X.eq x x'); eauto.
    assert (Hm11 : sort (Raw.ltk (elt:=Data.t)) m1).
     inversion_clear Hm1; auto.
    assert (Hm22 : sort (Raw.ltk (elt:=Data.t)) m2).
     inversion_clear Hm2; auto.
    destruct (IHm1 Hm11 (Build_slist Hm22)).
    apply Lt; unfold lt; simpl; MapS.Raw.MX.compare; right; auto.
    apply Eq; unfold eq; simpl; MapS.Raw.MX.compare; auto.
    apply Gt; unfold lt; simpl; MapS.Raw.MX.compare; auto.
    apply Gt; unfold lt; simpl; MapS.Raw.MX.compare; auto.
    apply Gt; unfold lt; simpl; MapS.Raw.MX.compare; auto.
    Qed.

End Make_ord. 
