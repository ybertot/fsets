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
 [FMapInterface.S] using lists of pairs,  unordered but without redundancy. *)

(** NB: There is no FMapWeakInterface file, since the interface [S] in FMapInterface 
      is precisely crafted to suit keys in both OrderedType and DecidableType. *)

Require Import FSetInterface. 
Require Import FSetWeakInterface.
Require Import FMapWeakInterface.

Set Implicit Arguments.
Unset Strict Implicit.

(** Usual syntax for lists. *)
Notation "[]" := nil (at level 0).
Arguments Scope list [type_scope].

Module Raw (X:DecidableType).

  Definition key := X.t.
  Definition t (elt:Set) := list (X.t * elt).

  Section Elt.

  Variable elt : Set.

  Definition eqk (p p':key*elt) := X.eq (fst p) (fst p').
  Definition eqke (p p':key*elt) := 
          X.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Hint Unfold eqk eqke.
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

   (* eqke is a stricter equality than eqk *)
 
   Lemma eqke_eqk : forall x x', eqke x x' -> eqk x x'.
     unfold eqk, eqke; intuition.
   Qed.
   Hint Resolve eqke_eqk.

  Definition MapsTo (k:key)(e:elt):= InA eqke (k,e).
  Definition In k m := exists e:elt, MapsTo k e m.

  Hint Unfold MapsTo In.

  Lemma InA_eqke_eqk : 
     forall x m, InA eqke x m -> InA eqk x m.
  Proof.
    induction 1; sintuition.
  Qed.
  Hint Resolve InA_eqke_eqk.

  (* An alternative formulation for [In k l] is [exists e, InA eqk (k,e) l] *)

  Lemma InA_eqk_In : forall k e l, InA eqk (k,e) l -> In k l.
  Proof.
     induction 1.
     destruct y.
     exists e0.
     eauto.
     induction IHInA.
     exists x;eauto.
  Qed.
  Hint Resolve InA_eqk_In.

  Lemma In_InA_eqk : forall k e l, In k l -> InA eqk (k,e) l.
  Proof.
     induction 1.
     induction H; simpl; sintuition.
  Qed.
  Hint Resolve In_InA_eqk.

  Lemma altern_In : forall k l, In k l <-> exists e:elt, InA eqk (k,e) l.
  Proof.
   split.
   destruct 1. 
   exists x; auto. 
   intros (x,H); eauto.
  Qed.

    Lemma notin_empty : forall k, ~ In k [].
      intros k abs.
      inversion abs.
      inversion H.
    Qed.
    Hint Resolve notin_empty.

    Notation noredunA := (noredunA eqk).

    Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> X.eq k k' \/ In k l.
      intros k k' e l H.
      inversion H.
      inversion_clear H0; unfold eqke in H1; simpl in *; intuition; eauto.
    Qed.      

    Lemma In_inv2 : forall x x' l, 
      InA eqk x (x' :: l) -> eqk x x' \/ InA eqk x l.
      intros x x' l inlist.
      inversion inlist;auto.
    Qed.

    Lemma In_inv3 : forall x x' l, 
      InA eqke x (x' :: l) -> eqke x x' \/ InA eqke x l.
      intros x x' l inlist.
      inversion inlist;auto.
    Qed.

    Lemma In_inv4 : forall k k' e e' l, 
      InA eqk (k, e) ((k', e') :: l) -> ~ X.eq k k' -> InA eqk (k, e) l.
      intros k k' e e' l H H0.
      elim (@In_inv2 (k,e) (k',e') l);intros;auto.
      elim H0;auto.
    Qed.

    Lemma In_inv5 : forall x x' l, 
      InA eqke x (x' :: l) -> ~ eqk x x' -> InA eqke x l.
      intros x x' l H H0.
      induction (@In_inv3 x x' l);auto. 
      elim H0.
      unfold eqke in *; unfold eqk; intuition.
    Qed.

    Lemma InA_eqk : forall x x' l, 
      InA eqk x l -> eqk x x' -> InA eqk x' l.
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

    Lemma empty_unique : noredunA empty.
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
      absurd (InA eqke (k, e) ((k, e) :: l));auto.
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
	| (k',_) :: l => if X.eq_dec k k' then true else mem k l
      end.

    (** Specification of [mem] *)

    Lemma mem_1 : forall m (Hm:noredunA m) x, In x m -> mem x m = true.
    Proof.
      intros m Hm x; generalize Hm; clear Hm.      
      functional induction mem x m;intros unique belong1;trivial.
      inversion belong1. inversion H.
      inversion_clear unique.
      inversion_clear belong1.
      inversion_clear H3.
      compute in H4; destruct H4.
      elim H; auto.
      apply H0; firstorder.
    Qed. 


    Lemma mem_2 : forall m (Hm:noredunA m) x, mem x m = true -> In x m. 
    Proof.
      intros m Hm x; generalize Hm; clear Hm; unfold In,MapsTo.
      functional induction mem x m; intros unique hyp;try ((inversion hyp);fail).
      exists e;eauto. 
      inversion_clear unique.
      destruct H0; auto.
      exists x; eauto.
    Qed.

    Fixpoint find (k:key) (s: t elt) {struct s} : option elt :=
      match s with
	| [] => None
	| (k',x)::s' => if X.eq_dec k k' then Some x else find k s'
      end.

    (** Specification of [find] *)

    Lemma find_2 :  forall m x e, find x m = Some e -> MapsTo x e m.
    Proof.
      intros m x. unfold MapsTo.
      functional induction find x m;simpl;intros e' eqfind; inversion eqfind; auto.
    Qed.

    Lemma find_1 :  forall m (Hm:noredunA m) x e, MapsTo x e m -> find x m = Some e. 
    Proof.
      intros m Hm x e; generalize Hm; clear Hm; unfold MapsTo.
      functional induction find x m;simpl; subst; try clear H_eq_1.

      inversion 2.
    
     intros.
     inversion_clear H0.
     compute in H1; destruct H1.
     congruence.
     inversion_clear Hm.
     elim H0.
     apply InA_eqk with (k,e); auto.

     intros.
     inversion_clear H1.
     compute in H2; destruct H2.
     absurd (X.eq k k'); auto.
     inversion_clear Hm; auto.
    Qed.


    Fixpoint add (k : key) (x : elt) (s : t elt) {struct s} : t elt :=
      match s with
	| [] => (k,x) :: []
	| (k',y) :: l => if X.eq_dec k k' then (k,x)::l else (k',y)::add k x l
      end.


    (** Specification of [add] *)

    Lemma add_1 : forall m x y e, X.eq y x -> MapsTo y e (add x e m).
    Proof.
      intros m x y e; generalize y; clear y.
      unfold MapsTo.
      functional induction add x e m;simpl;auto.
    Qed.

    Lemma add_2 : forall m x y e e', 
      ~ X.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
    Proof.
      intros m x  y e e'. 
      generalize y e; clear y e; unfold MapsTo.
      functional induction add x e' m;simpl;auto.
      intros y' e' eqky' mapsto1.
      
      assert (InA eqke (y', e') l); intuition; eauto.

      intros y' e' eqky' mapsto1.
      elim (@In_inv3 (y',e') (k',y) l);auto.
    Qed.
      
    Lemma add_3 : forall m x y e e',
      ~ X.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
    Proof.
      intros m x y e e'. generalize y e; clear y e; unfold MapsTo.
      functional induction add x e' m;simpl;eauto.
      intros e' y' eqky' Hinlist.
      inversion Hinlist;eauto.
    Qed.

    Lemma add_unique : forall m (Hm:noredunA m) x e, noredunA (add x e m).
    Proof.
    induction m.
    simpl; constructor; auto; red; inversion 1.
    intros.
    destruct a as (x',e').
    simpl; case (X.eq_dec x x'); inversion_clear Hm; auto.
    constructor; auto.
    intro H1; apply H; eapply InA_eqk; eauto.
    constructor; auto.
    swap H.
    (* we need add_3, but with eqk instead of eqke *)
    generalize H1 n; clear IHm H0 H1 n.
    functional induction add x e m; simpl; eauto; intros.
    inversion_clear H1; auto. 
    Qed.

    Fixpoint remove (k : key) (s : t elt) {struct s} : t elt :=
      match s with
	| [] => []
	| (k',x) :: l => if X.eq_dec k k' then l else (k',x) :: remove k l
      end.  

   (** Specification of [remove] *)

    Lemma remove_1 : forall m (Hm:noredunA m) x y, X.eq y x -> ~ In y (remove x m).
    Proof.
      intros m Hm x y; generalize Hm; clear Hm.
      functional induction remove x m;simpl;intros;auto.

      inversion_clear Hm.
      subst.
      swap H1.
      destruct H3 as (e,H3); unfold MapsTo in H3.
      apply InA_eqk with (y,e); auto.
      red; eauto.
      
      intro H2.
      destruct H2 as (e,H2); inversion_clear H2.
      compute in H3; destruct H3.
      elim H; eauto.
      inversion_clear Hm.
      firstorder.
      Qed.
      
      
    Lemma remove_2 : forall m (Hm:noredunA m) x y e, 
      ~ X.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
    Proof.
      intros m Hm x y e; generalize Hm; clear Hm; unfold MapsTo.
      functional induction remove x m;auto.
      intros unique noteqky inlist.
      elim (@In_inv3 (y, e) (k', x) l);auto;simpl;intuition;eauto.
      intros unique noteqky inlist.
      elim (@In_inv3 (y, e) (k', x) l); auto. 
      intro inlist2.

      assert (InA eqke (y, e) (remove k l));auto.
      apply H0;auto.
      inversion_clear unique; auto.
    Qed.

    Lemma remove_3 : forall m (Hm:noredunA m) x y e, 
      MapsTo y e (remove x m) -> MapsTo y e m.
    Proof.
      intros m Hm x y e; generalize Hm; clear Hm; unfold MapsTo.
      functional induction remove x m;auto.
      intros unique inlist.
      inversion_clear unique.
      elim (@In_inv3 (y, e) (k', x) (remove k l)); auto.
    Qed.

    Lemma remove_unique : forall m (Hm:noredunA m) x, noredunA (remove x m).
    Proof.
    induction m.
    simpl; intuition.
    intros.
    inversion_clear Hm.
    destruct a as (x',e').
    simpl; case (X.eq_dec x x'); auto.
    constructor; eauto.
    swap H.
    generalize H0 H1 n; clear H0 H1 n IHm.
    functional induction remove x m; simpl; eauto; intros.
    inversion_clear H1.
    inversion_clear H2; auto.
    Qed.  


    (** Specification of [MapsTo] *)

    Lemma MapsTo_1 : forall m x y e, X.eq x y -> MapsTo x e m -> MapsTo y e m.
      unfold MapsTo.
      intros m x y e eqxy inlist.
      induction inlist;eauto.

      apply InA_cons_hd;auto.
      eapply eqke_trans with (x, e);auto.
    Qed.

    Definition elements (m: t elt) := m.

    Lemma elements_1 : forall m x e, 
        MapsTo x e m -> InA eqke (x,e) (elements m).
    Proof.
    auto.
    Qed.

    Lemma elements_2 : forall m x e, 
        InA eqke (x,e) (elements m) -> MapsTo x e m.
    Proof. 
    auto.
    Qed.

    Lemma elements_3 : forall m (Hm:noredunA m),
       noredunA (elements m). 
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

     Definition check (cmp : elt -> elt -> bool)(k:key)(e:elt)(m': t elt) := 
         match find k m' with 
            | None => false
            | Some e' => cmp e e'
         end.

     Definition submap (cmp : elt -> elt -> bool)(m m' : t elt) : bool := 
       fold (fun k e b => andb (check cmp k e m') b) m true. 
       
     Definition equal (cmp : elt -> elt -> bool)(m m' : t elt) : bool :=
       andb (submap cmp m m') (submap (fun e' e => cmp e e') m' m).

     Definition Submap cmp m m' := 
         (forall k, In k m -> In k m') /\ 
         (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).  

     Definition Equal cmp m m' := 
         (forall k, In k m <-> In k m') /\ 
         (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).  

     Lemma submap_1 : forall m (Hm:noredunA m) m' (Hm': noredunA m') cmp, 
          Submap cmp m m' -> submap cmp m m' = true. 
     Proof.
     unfold Submap, submap.
     induction m.
     simpl; auto.
     destruct a; simpl; intros.
     destruct H.
     inversion_clear Hm.
     assert (H3 : In k m').
     apply H; exists e; auto.
     destruct H3 as (e', H3).
     unfold check at 2; rewrite (find_1 Hm' H3).
     rewrite (H0 k); simpl; auto.
     eapply IHm; auto.
     split; intuition.
     apply H.
     destruct H5 as (e'',H5); exists e''; auto.
     eapply H0; eauto; auto.
     Qed.
       
     Lemma submap_2 : forall m (Hm:noredunA m) m' (Hm': noredunA m') cmp, 
          submap cmp m m' = true -> Submap cmp m m'. 
     Proof.
     unfold Submap, submap.
     induction m.
     simpl; auto.
     intuition.
     destruct H0; inversion H0.
     inversion H0.
     
     destruct a; simpl; intros.
     inversion_clear Hm.
     rewrite andb_b_true in H.
     assert (check cmp k e m' = true).
       clear H1 H0 Hm' IHm.
       set (b:=check cmp k e m') in *.
       generalize H; clear H; generalize b; clear b.
       induction m; simpl; auto; intros.
       destruct a; simpl in *.
       destruct (andb_prop _ _ (IHm _ H)); auto.
     rewrite H2 in H.
     destruct (IHm H1 m' Hm' cmp H); auto.
     unfold check in H2.
     case_eq (find k m'); [intros e' H5 | intros H5]; rewrite H5 in H2; try discriminate.
     split; intros.
     destruct H6 as (e0,H6); inversion_clear H6.
     compute in H7; destruct H7; subst.
     exists e'.
     apply MapsTo_1 with k; auto.
     apply find_2; auto.
     apply H3.
     exists e0; auto.
     inversion_clear H6.
     compute in H8; destruct H8; subst.
     rewrite (find_1 Hm' (MapsTo_1 H6 H7)) in H5; congruence.
     eapply H4; eauto.
     Qed.


     (** Specification of [equal] *)
     Lemma equal_1 : forall m (Hm:noredunA m) m' (Hm': noredunA m') cmp, 
           Equal cmp m m' -> equal cmp m m' = true. 
     Proof. 
     unfold Equal, equal.
     intuition.
     apply andb_true_intro; split; 
       apply submap_1; unfold Submap; firstorder.
     Qed.

      Lemma equal_2 : forall m (Hm:noredunA m) m' (Hm':noredunA m') cmp, 
         equal cmp m m' = true -> Equal cmp m m'.
      Proof.
      unfold Equal, equal.
      intros.
      destruct (andb_prop _ _ H); clear H.
      generalize (submap_2 Hm Hm' H0).
      generalize (submap_2 Hm' Hm H1).
      firstorder.
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

      Lemma map_unique : 
         forall (m: t elt)(Hm : noredunA (@eqk elt) m)(f:elt -> elt'), 
         noredunA (@eqk elt') (map f m).
      Proof.   
      induction m; simpl; auto.
      intros.
      destruct a as (x',e').
      inversion_clear Hm.
      constructor; auto.
      swap H.
      (* il faut un map_1 avec eqk au lieu de eqke *)
      clear IHm H0. 
      induction m; simpl in *; auto.
      inversion H1.
      destruct a; inversion H1; auto.
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

      Lemma mapi_unique : 
         forall (m: t elt)(Hm : noredunA (@eqk elt) m)(f: key ->elt -> elt'), 
         noredunA (@eqk elt') (mapi f m).
      Proof.
      induction m; simpl; auto.
      intros.
      destruct a as (x',e').
      inversion_clear Hm; auto.
      constructor; auto.
      swap H.
      clear IHm H0.
      induction m; simpl in *; auto.
      inversion_clear H1.
      destruct a; inversion_clear H1; auto.
      Qed.

    Lemma find_eq : forall (m: t elt)(Hm : noredunA (@eqk elt) m)(x x':key), 
       X.eq x x' -> find x m = find x' m.
    Proof.
    intros.
    case_eq (find x' m); intros.
    apply find_1; auto.
    apply MapsTo_1 with x'; eauto.
    apply find_2; auto.
    case_eq (find x m); intros; auto.
    rewrite <- H0; symmetry.
    apply find_1; auto.
    apply MapsTo_1 with x; eauto.
    apply find_2; auto.
    Qed.

    Lemma add_eq : forall (m: t elt)(Hm : noredunA (@eqk elt) m)(x a:key)(e:elt), 
       X.eq x a -> find x (add a e m) = Some e.
     Proof.
     intros.
     apply find_1; auto.
     apply add_unique; auto.
     apply add_1; eauto.
    Qed.

    Lemma add_not_eq : forall (m: t elt)(Hm : noredunA (@eqk elt) m)(x a:key)(e:elt), 
       ~X.eq x a -> find x (add a e m) = find x m.
     Proof.
     intros.
     case_eq (find x m); intros.
     apply find_1; auto.
     apply add_unique; auto.
     apply add_2; eauto.
     apply find_2; auto.
     case_eq (find x (add a e m)); intros; auto.
    rewrite <- H0; symmetry.
    apply find_1; auto.
    eapply add_3; eauto.
    eapply find_2; eauto.
    Qed.

    End Elt2. 
    Section Elt3.

      Variable elt elt' elt'' : Set.
	
      Definition combine_l (m : t elt)(m' : t elt') : t (option elt * option elt') :=
        mapi (fun k e => (Some e, find k m')) m.	

      Definition combine_r (m : t elt)(m' : t elt') : t (option elt * option elt') :=
        mapi (fun k e' => (find k m, Some e')) m'.	
    
      Definition fold_right_pair (A B C:Set)(f: A -> B -> C -> C)(l:list (A*B))(i:C) := 
         List.fold_right (fun p => f (fst p) (snd p)) i l.

      Definition combine (m : t elt)(m' : t elt') : t (option elt * option elt') := 
         let l := combine_l m m' in 
         let r := combine_r m m' in 
         fold_right_pair (add (elt:=option elt * option elt')) l r.

    Lemma combine_unique : 
      forall (m: t elt)(Hm : noredunA (@eqk elt) m)(m': t elt')(Hm' : noredunA (@eqk elt') m'), 
      noredunA (@eqk (option elt * option elt')) (combine m m').
    Proof.
    unfold combine, combine_r, combine_l.
    intros.
    set (f1 := fun (k : key) (e : elt) => (Some e, find k m')).
    set (f2 := fun (k : key) (e' : elt') => (find k m, Some e')).
    generalize (mapi_unique Hm f1).
    generalize (mapi_unique Hm' f2).
    set (l := mapi f1 m); clearbody l.
    set (r := mapi f2 m'); clearbody r.
    clear f1 f2 Hm Hm' m m'.
    induction l.
    simpl; auto.
    intros.
    inversion_clear H0.
    destruct a; simpl; auto.
    apply add_unique; auto.
    Qed.

    Definition at_least_left (o:option elt)(o':option elt') := 
         match o with 
           | None => None 
           | _  => Some (o,o')
         end.

    Definition at_least_right (o:option elt)(o':option elt') := 
         match o' with 
           | None => None 
           | _  => Some (o,o')
         end.

    Lemma combine_l_1 : 
      forall (m: t elt)(Hm : noredunA (@eqk elt) m)(m': t elt')(Hm' : noredunA (@eqk elt') m') 
      (x:key), 
      find x (combine_l m m') = at_least_left (find x m) (find x m'). 
    Proof.
    unfold combine_l.
    intros.
    case_eq (find x m); intros.
    simpl.
    apply find_1.
    apply mapi_unique; auto.
    destruct (mapi_1 (fun k e => (Some e, find k m')) (find_2 H)) as (y,(H0,H1)).
    rewrite (find_eq Hm' (X.eq_sym H0)); auto.
    simpl.
    case_eq (find x (mapi (fun k e => (Some e, find k m')) m)); intros; auto.
    destruct (@mapi_2 _ _ m x (fun k e => (Some e, find k m'))).
    exists p; apply find_2; auto.
    rewrite (find_1 Hm H1) in H; discriminate.
    Qed.

    Lemma combine_r_1 : 
      forall (m: t elt)(Hm : noredunA (@eqk elt) m)(m': t elt')(Hm' : noredunA (@eqk elt') m') 
      (x:key), 
      find x (combine_r m m') = at_least_right (find x m) (find x m'). 
    Proof.
    unfold combine_r.
    intros.
    case_eq (find x m'); intros.
    simpl.
    apply find_1.
    apply mapi_unique; auto.
    destruct (mapi_1 (fun k e => (find k m, Some e)) (find_2 H)) as (y,(H0,H1)).
    rewrite (find_eq Hm (X.eq_sym H0)); auto.
    simpl.
    case_eq (find x (mapi (fun k e' => (find k m, Some e')) m')); intros; auto.
    destruct (@mapi_2 _ _ m' x (fun k e' => (find k m, Some e'))).
    exists p; apply find_2; auto.
    rewrite (find_1 Hm' H1) in H; discriminate.
    Qed.
    
    Definition at_least_one (o:option elt)(o':option elt') := 
         match o, o' with 
           | None, None => None 
           | _, _  => Some (o,o')
         end.

    Lemma combine_1 : 
      forall (m: t elt)(Hm : noredunA (@eqk elt) m)(m': t elt')(Hm' : noredunA (@eqk elt') m') 
      (x:key), 
      find x (combine m m') = at_least_one (find x m) (find x m'). 
    Proof.
    unfold combine.
    intros.
    generalize (combine_r_1 Hm Hm' x).
    generalize (combine_l_1 Hm Hm' x).
    assert (noredunA (eqk (elt:=option elt * option elt')) (combine_l m m')).
      unfold combine_l.
      apply mapi_unique; auto.
    assert (noredunA (eqk (elt:=option elt * option elt')) (combine_r m m')).
      unfold combine_r.
      apply mapi_unique; auto.
    set (l := combine_l m m') in *; clearbody l.
    set (r := combine_r m m') in *; clearbody r.
    set (o := find x m); clearbody o.
    set (o' := find x m'); clearbody o'.
    clear Hm' Hm m m'.
    induction l.
    destruct o; destruct o'; simpl; intros; discriminate || auto.
    destruct a; simpl in *; intros.
    destruct (X.eq_dec x t0); simpl in *.
    unfold at_least_left in H1.
    destruct o; simpl in *; try discriminate.
    inversion H1; subst.
    apply add_eq; auto.
    inversion_clear H.
    (* begin *)
    clear H2 H1 H3 e IHl o' e0 t0 x.
    induction l; simpl; auto.
    destruct a; simpl; auto.
    inversion_clear H4.
    apply add_unique; eauto.
    (* end *)
    inversion_clear H.
    rewrite <- IHl; auto.
    apply add_not_eq; auto.
    (* begin *)
    clear H2 H1 H3 n IHl o o' t0 x p.
    induction l; simpl; auto.
    destruct a; simpl; auto.
    inversion_clear H4.
    apply add_unique; eauto.
    (* end *)
    Qed.

      Variable f : option elt -> option elt' -> option elt''.

      Definition option_cons (A:Set)(k:key)(o:option A)(l:list (key*A)) := 
         match o with 
           | Some e => (k,e)::l
           | None => l
         end.

      Definition map2 m m' := 
        let m0 : t (option elt * option elt') := combine m m' in 
        let m1 : t (option elt'') := map (fun p => f (fst p) (snd p)) m0 in 
        fold_right_pair (option_cons (A:=elt'')) m1 nil.
    
    Lemma map2_unique : 
      forall (m: t elt)(Hm : noredunA (@eqk elt) m)(m': t elt')(Hm' : noredunA (@eqk elt') m'), 
      noredunA (@eqk elt'') (map2 m m').
     Proof.
     intros.
     unfold map2.
     assert (H0:=combine_unique Hm Hm').
     set (l0:=combine m m') in *; clearbody l0.
     set (f':= fun p : option elt * option elt' => f (fst p) (snd p)).
     assert (H1:=map_unique (elt' := option elt'') H0 f').
     set (l1:=map f' l0) in *; clearbody l1. 
     clear f' f H0 l0 Hm Hm' m m'.
     induction l1.
     simpl; auto.
     inversion_clear H1.
     destruct a; destruct o; simpl; auto.
     constructor; auto.
     swap H.
     clear IHl1.
     induction l1.
     inversion H1.
     inversion_clear H0.
     destruct a; destruct o; simpl in *; auto.
     inversion_clear  H1; auto.
     Qed.

    Definition at_least_one_then_f (o:option elt)(o':option elt') := 
         match o, o' with 
           | None, None => None 
           | _, _  => f o o'
         end.

    Lemma map2_0 : 
      forall (m: t elt)(Hm : noredunA (@eqk elt) m)(m': t elt')(Hm' : noredunA (@eqk elt') m') 
      (x:key), 
      find x (map2 m m') = at_least_one_then_f (find x m) (find x m'). 
    Proof.
    intros.
    unfold map2.
    assert (H:=combine_1 Hm Hm' x).
    assert (H2:=combine_unique Hm Hm').
    set (f':= fun p : option elt * option elt' => f (fst p) (snd p)).
    set (m0 := combine m m') in *; clearbody m0.
    set (o:=find x m) in *; clearbody o. 
    set (o':=find x m') in *; clearbody o'.
    clear Hm Hm' m m'.
    generalize H; clear H.
    match goal with |- ?g => 
       assert (g /\ (find x m0 = None -> 
                           find x (fold_right_pair (option_cons (A:=elt'')) (map f' m0) []) = None)); 
       [ | intuition ] end.
    induction m0; simpl in *; intuition.
    destruct o; destruct o'; simpl in *; try discriminate; auto.
    destruct a as (k,(oo,oo')); simpl in *.
    inversion_clear H2.
    destruct (X.eq_dec x k); simpl in *.
    (* x = k *)
    assert (at_least_one_then_f o o' = f oo oo').
      destruct o; destruct o'; simpl in *; inversion_clear H; auto.
    rewrite H2.
    unfold f'; simpl.
    destruct (f oo oo'); simpl.
    destruct (X.eq_dec x k); [ auto | absurd_hyp n; eauto ].
    destruct (IHm0 H1) as (_,H4); apply H4; auto.
    case_eq (find x m0); intros; auto.
    elim H0.
    apply InA_eqk with (x,p).
    apply InA_eqke_eqk.
    exact (find_2 H3). 
    red; auto.
    (* k < x *)
    unfold f'; simpl.
    destruct (f oo oo'); simpl.
    destruct (X.eq_dec x k); [ absurd_hyp n; eauto | auto].
    destruct (IHm0 H1) as (H3,_); apply H3; auto.
    destruct (IHm0 H1) as (H3,_); apply H3; auto.

    (* None -> None *)
    destruct a as (k,(oo,oo')).
    simpl.
    inversion_clear H2.
    destruct (X.eq_dec x k).
    (* x = k *)
    discriminate.
    (* k < x *)
    unfold f'; simpl.
    destruct (f oo oo'); simpl.
    destruct (X.eq_dec x k); [ absurd_hyp n; eauto | auto].
    destruct (IHm0 H1) as (_,H4); apply H4; auto.
    destruct (IHm0 H1) as (_,H4); apply H4; auto.
    Qed.

     (** Specification of [map2] *)
     Lemma map2_1 : forall (m: t elt)(Hm : noredunA (@eqk elt) m)
        (m': t elt')(Hm' : noredunA (@eqk elt') m')(x:key),
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
     
     Lemma map2_2 : forall (m: t elt)(Hm : noredunA (@eqk elt) m)
        (m': t elt')(Hm' : noredunA (@eqk elt') m')(x:key), 
        In x (map2 m m') -> In x m \/ In x m'. 
     Proof.
     intros.
     destruct H as (e,H).
     generalize (map2_0 Hm Hm' x).
     rewrite (find_1 (map2_unique Hm Hm') H).
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


Module Make (X: DecidableType) <: S with Module E:=X.
  Module Raw := Raw X. 

  Module E := X.
  Definition key := X.t. 

  Record slist (elt:Set) : Set :=  {this :> Raw.t elt; unique : noredunA (@Raw.eqk elt) this}.
  Definition t (elt:Set) := slist elt. 

 Section Elt. 
 Variable elt elt' elt'':Set. 

 Implicit Types m : t elt.

 Definition empty := Build_slist (Raw.empty_unique elt).
 Definition is_empty m := Raw.is_empty m.(this).
 Definition add x e m := Build_slist (Raw.add_unique m.(unique) x e).
 Definition find x m := Raw.find x m.(this).
 Definition remove x m := Build_slist (Raw.remove_unique m.(unique) x). 
 Definition mem x m := Raw.mem x m.(this).
 Definition map f m : t elt' := Build_slist (Raw.map_unique m.(unique) f).
 Definition mapi f m : t elt' := Build_slist (Raw.mapi_unique m.(unique) f).
 Definition map2 f m (m':t elt') : t elt'' := 
     Build_slist (Raw.map2_unique f m.(unique) m'.(unique)).
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

 Definition MapsTo_1 m := @Raw.MapsTo_1 elt m.(this).

 Definition mem_1 m := @Raw.mem_1 elt m.(this) m.(unique).
 Definition mem_2 m := @Raw.mem_2 elt m.(this) m.(unique).

 Definition empty_1 := @Raw.empty_1.

 Definition is_empty_1 m := @Raw.is_empty_1 elt m.(this).
 Definition is_empty_2 m := @Raw.is_empty_2 elt m.(this).

 Definition add_1 m := @Raw.add_1 elt m.(this).
 Definition add_2 m := @Raw.add_2 elt m.(this).
 Definition add_3 m := @Raw.add_3 elt m.(this).

 Definition remove_1 m := @Raw.remove_1 elt m.(this) m.(unique).
 Definition remove_2 m := @Raw.remove_2 elt m.(this) m.(unique).
 Definition remove_3 m := @Raw.remove_3 elt m.(this) m.(unique).

 Definition find_1 m := @Raw.find_1 elt m.(this) m.(unique).
 Definition find_2 m := @Raw.find_2 elt m.(this).

 Definition elements_1 m := @Raw.elements_1 elt m.(this).
 Definition elements_2 m := @Raw.elements_2 elt m.(this).
 Definition elements_3 m := @Raw.elements_3 elt m.(this) m.(unique).

 Definition fold_1 m := @Raw.fold_1 elt m.(this).

 Definition map_1 m := @Raw.map_1 elt elt' m.(this).
 Definition map_2 m := @Raw.map_2 elt elt' m.(this).

 Definition mapi_1 m := @Raw.mapi_1 elt elt' m.(this).
 Definition mapi_2 m := @Raw.mapi_2 elt elt' m.(this).

 Definition map2_1 m (m':t elt') x f := 
    @Raw.map2_1 elt elt' elt'' f m.(this) m.(unique) m'.(this) m'.(unique) x.
 Definition map2_2 m (m':t elt') x f := 
    @Raw.map2_2 elt elt' elt'' f m.(this) m.(unique) m'.(this) m'.(unique) x.

 Definition equal_1 m m' := @Raw.equal_1 elt m.(this) m.(unique) m'.(this) m'.(unique).
 Definition equal_2 m m' := @Raw.equal_2 elt m.(this) m.(unique) m'.(this) m'.(unique).

 End Elt.
End Make.


