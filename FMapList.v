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

Module Raw (X:OrderedType).
  Module MX := OrderedTypeFacts X.

  Definition key := X.t.
  Definition t (elt:Set) := list (X.t * elt).

  Section Elt.

  Variable elt : Set.

  Definition eq_key (p p':key*elt) := X.eq (fst p) (fst p').
  Definition eq_key_elt (p p':key*elt) := 
          X.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Definition lt_key (p p':key*elt) := X.lt (fst p) (fst p').

  Definition MapsTo (k:key)(e:elt):= InList eq_key_elt (k,e).
  Definition In k m := exists e:elt, MapsTo k e m.
  Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

  Lemma InList_eq_key_el_eq_key : 
      forall x m, InList eq_key_elt x m -> InList eq_key x m.
      induction m; simpl; inversion_clear 1; auto.
      unfold eq_key, eq_key_elt in *; intuition.
    Qed.
      
    Hint Unfold MapsTo eq_key_elt eq_key lt_key In.
    Hint Constructors InList.
    Hint Resolve InList_eq_key_el_eq_key.

    Lemma notin_empty : forall k, ~ In k [].
      intros k abs.
      inversion abs.
      inversion H.
    Qed.

    Hint Resolve notin_empty.

    Hint Extern 2 (eq_key_elt ?a ?b) => split.

    Ltac dec_eq_key_elt :=
      match goal with
	H:(eq_key_elt ?a ?b) |- ?c 
	  => let x:= fresh "eqk" in 
	    let y := fresh "eqe" in (elim H;clear H;intros x y)
      end.

    Lemma InList_In_eq_key : forall k e l, InList eq_key (k,e) l -> In k l.
      unfold eq_key.
      intros k e l H. 
      induction H.
      destruct y.
      exists e0.
      eauto.
      induction IHInList.
      exists x;eauto.
    Qed.
    Hint Resolve InList_In_eq_key.

    (* could also be proved as a corollary of previous lemma *)
    Lemma InList_In : forall k e l, InList eq_key_elt (k,e) l -> In k l.
      intros k e l H. exists e;auto.
    Qed.
    Hint Resolve InList_In.

   Lemma lt_key_right_r : forall x k e e', lt_key x (k,e) -> lt_key x (k,e').
      auto.
    Qed.

    Lemma lt_key_right_l : forall x k e e', lt_key (k,e) x -> lt_key (k,e') x.
      auto.
    Qed.

    Hint Resolve lt_key_right_l lt_key_right_r.

    Hint Resolve MX.lt_eq.

    Lemma eq_key_no_lt_key : forall x x', eq_key x x' -> ~lt_key x x'.
      intros (k,e) (k',e') abs1 abs2.
      absurd (X.eq k k'); auto.
    Qed.

    Hint Resolve eq_key_no_lt_key. 

    Lemma eq_key_elt_no_lt_key : forall x x', eq_key_elt x x' -> ~lt_key x x'.
      intros (k,e) (k',e') abs1.
      destruct abs1; auto.
    Qed.

    Hint Resolve eq_key_elt_no_lt_key. 

    Lemma lt_key_trans : forall e e' e'', lt_key e e' -> lt_key e' e'' -> lt_key e e''.
      eauto.
    Qed.

    Lemma lt_key_eq_key : forall e e' e'', lt_key e e' -> eq_key e' e'' -> lt_key e e''.
      intros (k,e) (k',e') (k'',e'').
      unfold lt_key, eq_key; simpl; intros.
      eapply MX.lt_eq;eauto.
    Qed.

    Hint Resolve lt_key_eq_key.

    Lemma eq_key_lt_key : forall e e' e'', lt_key e e'' -> eq_key e e' -> lt_key e' e''.
      intros (k,e) (k',e') (k'',e'').
      unfold lt_key, eq_key; simpl; intros.
      apply MX.eq_lt with k;eauto.
    Qed.

    Hint Resolve eq_key_lt_key.

    Lemma eq_key_refl : forall e, eq_key e e.
      auto.
    Qed.

    Lemma eq_key_elt_refl : forall e, eq_key_elt e e.
      auto.
    Qed.

    Lemma eq_key_sym : forall e e', eq_key e e' -> eq_key e' e.
      auto.
    Qed.

    Lemma eq_key_elt_sym : forall e e', eq_key_elt e e' -> eq_key_elt e' e.
      unfold eq_key_elt; intuition.
    Qed.

    Lemma eq_key_trans : forall e e' e'', eq_key e e' -> eq_key e' e'' -> eq_key e e''.
      eauto. 
    Qed.

    Lemma eq_key_elt_trans : forall e e' e'', 
      eq_key_elt e e' -> eq_key_elt e' e'' -> eq_key_elt e e''.
      unfold eq_key_elt; intuition eauto; congruence.
    Qed.

    Hint Resolve eq_key_trans eq_key_elt_trans eq_key_sym eq_key_elt_sym eq_key_refl 
      eq_key_elt_refl.

    Notation Sort := (sort lt_key).
    Notation Inf := (lelistA lt_key).

    Hint Resolve nil_sort cons_sort.

    Lemma lt_sort_tl : forall e l (sorted:Sort (e::l)), Sort l.
      intros e l sorted.
      inversion sorted.
      inversion H1; auto.
    Qed.

     Hint Resolve lt_sort_tl.

    Lemma lt_sort_tl2 : forall e e' l (sorted:Sort (e::e'::l)), Sort (e::l).
      intros e e' l sorted.
      inversion sorted.
      inversion H1.
      apply cons_sort.
      assumption.
      inversion H6.
      apply nil_leA.
      apply cons_leA.
      subst.
      apply lt_key_trans with e';auto.
      inversion sorted.
      inversion H4.
      assumption.
    Qed.
      
    Hint Resolve lt_sort_tl2.

    Lemma all_lt_Inf: forall x l, 
      (forall e, InList eq_key_elt e l -> lt_key x e) -> Inf x l.
      intros x l H. destruct l;auto.
    Qed.

    Hint Resolve all_lt_Inf.

    Lemma sort_in_tl : forall e l e', Sort (e::l) -> InList eq_key e' l -> lt_key e e'.
      intros e l e' sorted Hin.
      induction Hin;eauto.

      apply lt_key_eq_key with y;eauto.
      inversion sorted.
      subst.
      inversion H3;eauto.
    Qed.

    Lemma sort_in : forall l e e', Sort (e::l) -> InList eq_key e' (e::l) 
      -> lt_key e e' \/ eq_key e e'.
      intros l e e' sorted Hin.
      inversion Hin;eauto.
      left.
      apply sort_in_tl with l;assumption.
    Qed.

    Lemma sort_lt_notin : forall l k e (sorted : Sort l), 
      Inf (k,e) l ->  ~In k l.
      intros l k e sorted Hlt.
      inversion Hlt.
      intro abs. inversion abs. inversion H0. 
      intro Hin. subst.
      inversion Hin.
      assert (lt_key b (k,x) \/ eq_key b (k,x)).
      eapply sort_in with l0. auto.
      auto.
      decompose [or] H1;clear H1.
      assert (lt_key (k,x) b).
      apply lt_key_right_l with e;assumption.
      absurd (lt_key b (k, x));auto.
      destruct b.
      unfold lt_key; simpl.
      apply MX.lt_not_gt;auto.

      destruct b.
      unfold eq_key in H2; simpl in H2.
      unfold lt_key in H; simpl in H.
      absurd (X.eq k0 k); simpl;eauto.
    Qed.


    Lemma sort_lt_notin2 : forall l k e (sorted : Sort l), 
      Inf (k,e) l -> ~(exists e:elt, InList eq_key (k,e) l).
      intros l k e sorted Hlt.
      inversion Hlt.
      intro abs. inversion abs. inversion H0. 
      intro Hin. subst.
      inversion Hin.
      assert (lt_key b (k,x) \/ eq_key b (k,x)).
      eapply sort_in with l0. auto.
      auto.
      decompose [or] H1;clear H1.
      assert (lt_key (k,x) b).
      apply lt_key_right_l with e;assumption.
      absurd (lt_key b (k, x));auto.
      destruct b.
      unfold lt_key; simpl.
      apply MX.lt_not_gt;auto.

      destruct b.
      unfold eq_key in H2; simpl in H2.
      unfold lt_key in H; simpl in H.
      absurd (X.eq k0 k); simpl;eauto.
    Qed.

    Hint Resolve sort_lt_notin.

    Lemma sorted_unique: forall l, Sort l -> Unique eq_key l.
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

    Lemma sorted_unique2: forall l, Sort l -> Unique eq_key_elt l.
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

    Lemma sorted_unique_key_eq: forall l, Unique eq_key l -> Unique eq_key_elt l.
      intros l unique.
      induction unique;auto.
    Qed.
      

    Lemma Inf_eq : forall x x' l, 
      eq_key x x' -> Inf x l -> Inf x' l.
    Proof.  
     intros x x' l H H0.
     inversion H0; eauto.
    Qed.

    Lemma Inf_lt : forall x x' l, lt_key x x' -> Inf x' l -> Inf x l.
    Proof.
     induction 2; auto.
     constructor.
     eapply lt_key_trans; eauto.
   Qed.     

   Hint Resolve Inf_eq Inf_lt.

   Lemma sorted_in_cons_not_eq : forall x l k e (sorted:Sort ((k,e)::l)) (Hin: In x l),
      ~X.eq x k.
      intros x l k e sorted.
      inversion sorted.
      intros Hin.
      intro abs.
      absurd (In x l);auto.
      eapply sort_lt_notin with e;auto.      
      eapply Inf_eq with (k,e);simpl;auto.
    Qed.

    Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> X.eq k k' \/ In k l.
      intros k k' e l H.
      inversion H.
      inversion_clear H0; unfold eq_key_elt in H1; simpl in *; intuition; eauto.
    Qed.      

    Lemma In_inv2 : forall x x' l, 
      InList eq_key x (x' :: l) -> eq_key x x' \/ InList eq_key x l.
      intros x x' l inlist.
      inversion inlist;auto.
    Qed.

    Lemma In_inv3 : forall x x' l, 
      InList eq_key_elt x (x' :: l) -> eq_key_elt x x' \/ InList eq_key_elt x l.
      intros x x' l inlist.
      inversion inlist;auto.
    Qed.

   (** end of auxiliary results *)

    Definition empty : t elt := [].

    (** Specification of [empty] *)

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
      absurd (InList eq_key_elt (k, e) ((k, e) :: l));auto.
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
            | FSetInterface.Lt _ => false
            | FSetInterface.Eq _ => true
            | FSetInterface.Gt _ => mem k l
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
	    | (FSetInterface.Lt _) => None
	    | (FSetInterface.Eq _) => Some x
	    | (FSetInterface.Gt _) => find k s'
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
      unfold eq_key_elt in H0; simpl in H0; intuition. 
      assert (H2 := sort_in_tl Hm (InList_eq_key_el_eq_key H0)).
      unfold lt_key in H2; simpl in H2; intuition. 
      absurd (X.lt k k'); auto.
    
     intros.
     inversion_clear H.
     unfold eq_key_elt in H0; simpl in H0; intuition congruence. 
     assert (H2 := sort_in_tl Hm (InList_eq_key_el_eq_key H0)).
     unfold lt_key in H2; simpl in H2; intuition. 
     absurd (X.eq k k'); auto.

     intros.
     inversion_clear H0.
     absurd (X.eq k k'); auto.
     unfold eq_key_elt in H1; simpl in H1; intuition.
     eauto.
    Qed.


    Fixpoint add (k : key) (x : elt) (s : t elt) {struct s} : t elt :=
      match s with
	| [] => (k,x) :: []
	| (k',y) :: l =>
          match X.compare k k' with
            | FSetInterface.Lt _ => (k,x)::s
            | FSetInterface.Eq _ => (k,x)::l
            | FSetInterface.Gt _ => (k',y) :: add k x l
          end
      end.


    (** Specification of [add] *)

    Lemma add_1 : forall m x y e, X.eq y x -> MapsTo y e (add x e m).
      intros m x y e; generalize y; clear y.
      unfold MapsTo.
      functional induction add x e m;simpl;auto.
    Qed.

    Lemma aux' : forall k k' e e' l, 
      InList eq_key (k, e) ((k', e') :: l) -> ~ X.eq k k' -> InList eq_key (k, e) l.
      intros k k' e e' l H H0.
      elim (@In_inv2 (k,e) (k',e') l);intros;auto.
      elim H0;auto.
    Qed.

    Lemma aux'' : forall x x' l, 
      InList eq_key_elt x (x' :: l) -> ~ eq_key x x' -> InList eq_key_elt x l.
      intros x x' l H H0.
      induction (@In_inv3 x x' l);auto. 
      elim H0.
      unfold eq_key_elt in *; unfold eq_key; intuition.
    Qed.

    Lemma aux''' : forall x x' l, 
      InList eq_key x l -> eq_key x x' -> InList eq_key x' l.
      intros x x' l H H0.
      induction H;eauto.
    Qed.

    Hint Resolve aux'' aux'.

    Lemma add_2 : forall m x y e e', 
      ~ X.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
      intros m x  y e e'. 
      generalize y e; clear y e; unfold MapsTo.
      functional induction add x e' m;simpl;auto.
      intros y' e' eqky' mapsto1.
      
      assert (InList eq_key_elt (y', e') l); intuition; eauto.

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
     forall (m : t elt) (x x':key)(e e':elt), Inf (x',e') m -> lt_key (x',e') (x,e) -> Inf (x',e') (add x e m).
   Proof.
     induction m.  
     simpl; intuition.
     intros.
     destruct a as (x'',e'').
     inversion_clear H.
     unfold lt_key in H0,H1; simpl in H0, H1.
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
            | FSetInterface.Lt _ => s
            | FSetInterface.Eq _ => l
            | FSetInterface.Gt _ => (k',x) :: remove k l
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
      unfold lt_key; eapply MX.lt_eq;eauto.
      
      eapply sort_lt_notin with x. eauto. 
      inversion Hm.
      eapply Inf_eq with (k',x) ;simpl;auto.
      intuition; eauto.

      assert (notin:~ In y (remove k l)). apply H;eauto.
      intros (x0,abs).
      inversion_clear abs; eauto. 
      dec_eq_key_elt; simpl in *; subst.
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

      assert (InList eq_key_elt (y, e) (remove k l));auto.
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
     unfold lt_key in H0; simpl in H0.
     simpl; case (X.compare x x''); intuition.
     inversion_clear Hm.
     eapply Inf_lt; eauto.
     unfold lt_key; auto.
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
      eapply eq_key_elt_trans with (x, e);auto.
    Qed.



    Fixpoint fold (A:Set) (f:key -> elt -> A -> A) (m:t elt) {struct m} : A -> A :=
      fun acc => 
      match m with
	| [] => acc
	| (k,e)::m' => f k e (fold f m' acc)
      end.

      (** Specification of [fold] *)  

      Lemma fold_1' :
	forall (m: t elt)(Hm:Sort m)(A : Set) (acc : A) (f : key -> elt -> A -> A) ,
	  exists l : list (key*elt),
            Sort l /\
            (forall (k:key)(x:elt), MapsTo k x m <-> InList eq_key_elt (k,x) l) 
            /\
            fold f m acc = fold_right (fun p => f (fst p) (snd p)) acc l.
        intros m Hm A acc f; generalize Hm; clear Hm.
        functional induction fold A f m acc;intro sorted;subst.
        exists (@nil (key*elt)). 
	split;[|split;[intros ;split|]];subst;auto.

	elim H;eauto.
	clear H. intros x hyp.
	decompose [and] hyp. clear hyp.
        exists ((k, e) ::x);intuition.

	apply cons_sort;auto.
	assert (Inf (k, e) m').

	inversion sorted;auto.

	apply all_lt_Inf.
	intros e' hyp.
	destruct e'.
	elim (H1 k0 e0);intros .
	assert (InList eq_key_elt (k0, e0) m').
	apply H4;assumption.
	eapply sort_in_tl with m';auto.

	unfold MapsTo in H0.
	inversion H0.
	auto.
	apply InList_cons_tl.
	
	elim (H1 k0 x0);intros .
	auto.

	inversion H0.
	auto.
	unfold MapsTo.
	apply InList_cons_tl.
	
	elim (H1 k0 x0).
	intros H6 H7.	
	unfold MapsTo in H7.
	auto.

	rewrite H2.
	simpl.
	trivial.
      Qed.
	

      Lemma fold_1 :
	forall (m:t elt)(Hm:Sort m)(A : Set) (acc : A) (f : key -> elt -> A -> A),
	  exists l : list (key*elt),
            Unique eq_key l /\
            (forall (k:key)(x:elt), MapsTo k x m <-> InList eq_key_elt (k,x) l) 
            /\
            fold f m acc = fold_right (fun p => f (fst p) (snd p)) acc l.
	intros m Hm A acc f.
	elim (@fold_1' m Hm A acc f).
	intros x H0.	
	exists x;intuition;auto.
	apply sorted_unique;auto.
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
        destruct H2; eauto.
        inversion H2.

        destruct (H0 x).
        destruct H; eauto.
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
       dec_eq_key_elt; simpl in *; subst.
       inversion_clear H2. 
       dec_eq_key_elt; simpl in *; subst; auto.
       elim (sort_lt_notin H6 H7).
       exists e'0; apply MapsTo_1 with k; eauto.
       inversion_clear H2. 
       dec_eq_key_elt; simpl in *; subst; auto.
       elim (sort_lt_notin H0 H5).
       exists e1; apply MapsTo_1 with k; eauto.
       apply H9 with k; eauto.
      Qed. 
      

      Variable elt' elt'':Set.
      
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
                    | FSetInterface.Lt _ => option_cons k (f (Some e) None) (map2 l m')
                    | FSetInterface.Eq _ => option_cons k (f (Some e) (Some e')) (map2 l l')
                    | FSetInterface.Gt _ => option_cons k' (f None (Some e')) (map2_aux l')
                  end
              end
        end.      


  End Elt.

    (** Specification of [map] *)

      Lemma map_1 : forall (elt elt':Set)(m:t elt)(x:key)(e:elt)(f:elt->elt'), 
        MapsTo x e m -> MapsTo x (f e) (map f m).
      Proof.
	intros elt elt' m x e f.
	(* functional induction map elt elt' f m.  *) (* Marche pas ??? *)
        induction m.
        inversion 1.
        
        destruct a as (x',e').
        simpl. 
        inversion_clear 1.
        constructor 1.
        unfold eq_key_elt in *; simpl in *; intuition congruence.
        constructor 2.
        unfold MapsTo in *; auto.
      Qed.

      Lemma map_2 : forall (elt elt':Set)(m:t elt)(x:key)(f:elt->elt'), 
        In x (map f m) -> In x m.
      Proof.
	intros elt elt' m x f. 
        (* functional induction map elt elt' f m. *) (* Marche pas ??? *)
        induction m; simpl.
        intros (e,abs).
        inversion abs.
        
        destruct a as (x',e).
	intros hyp.
	inversion hyp. clear hyp.
	inversion H; subst; rename x0 into e'.
        exists e; constructor.
        unfold eq_key_elt in *; simpl in *; intuition.
        destruct IHm as (e'',hyp).
        exists e'; auto.
        exists e''.
        constructor 2; auto.
      Qed.

      Lemma map_lelistA : 
         forall (elt elt':Set)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
         lelistA (@lt_key elt) (x,e) m -> 
         lelistA (@lt_key elt') (x,f e) (map f m).
      Proof. 
        induction m; simpl; auto.
        intros.
        destruct a as (x',e').
        inversion_clear H; auto.
      Qed.

      Hint Resolve map_lelistA.

      Lemma map_sorted : 
         forall (elt elt':Set)(m: t elt)(Hm : sort (@lt_key elt) m)(f:elt -> elt'), 
         sort (@lt_key elt') (map f m).
      Proof.   
      induction m; simpl; auto.
      intros.
      destruct a as (x',e').
      inversion_clear Hm; auto.
      Qed.      
      
 
    (** Specification of [mapi] *)

      Lemma mapi_1 : forall (elt elt':Set)(m:t elt)(x:key)(e:elt)
        (f:key->elt->elt'), MapsTo x e m -> 
        exists y, X.eq y x /\ MapsTo x (f y e) (mapi f m).
      Proof.
	intros elt elt' m x e f.
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
        unfold eq_key_elt in *; simpl in *; intuition congruence.
        destruct IHm as (y, hyp); auto.
        exists y; intuition.
        constructor 2.
        unfold MapsTo in *; auto.
      Qed.  


      Lemma mapi_2 : forall (elt elt':Set)(m:t elt)(x:key)
        (f:key->elt->elt'), In x (mapi f m) -> In x m.
      Proof.
	intros elt elt' m x f. 
        (* functional induction mapi elt elt' f m. *) (* Marche pas ??? *)
        induction m; simpl.
        intros (e,abs).
        inversion abs.
        
        destruct a as (x',e).
	intros hyp.
	inversion hyp. clear hyp.
	inversion H; subst; rename x0 into e'.
        exists e; constructor.
        unfold eq_key_elt in *; simpl in *; intuition.
        destruct IHm as (e'',hyp).
        exists e'; auto.
        exists e''.
        constructor 2; auto.
      Qed.

      Lemma mapi_lelistA : 
         forall (elt elt':Set)(m: t elt)(x:key)(e:elt)(f:key->elt->elt'),
         lelistA (@lt_key elt) (x,e) m -> 
         lelistA (@lt_key elt') (x,f x e) (mapi f m).
      Proof. 
        induction m; simpl; auto.
        intros.
        destruct a as (x',e').
        inversion_clear H; auto.
      Qed.

      Hint Resolve mapi_lelistA.

      Lemma mapi_sorted : 
         forall (elt elt':Set)(m: t elt)(Hm : sort (@lt_key elt) m)(f: key ->elt -> elt'), 
         sort (@lt_key elt') (mapi f m).
      Proof.   
      induction m; simpl; auto.
      intros.
      destruct a as (x',e').
      inversion_clear Hm; auto.
      Qed.      

     Lemma map2_r_1 : forall (elt elt' elt'':Set)
        (m': t elt')(Hm' : sort (@lt_key elt') m')
	(x:key)(f:option elt->option elt'->option elt''), 
        (In x m' -> find x (map2_r f m') = f None (find x m'))
        /\
        (In x (map2_r f m') -> In x m'). 
     Proof.
     induction m'.
     intros.
     split; simpl; destruct 1; inversion H.
     destruct a as (k',e').
     split; simpl; intros.
     unfold option_cons.
     destruct H as (e,H).
     inversion_clear H. 
     destruct H0; simpl in *; subst. 
     destruct (X.compare x k'); try solve [absurd (X.eq x k'); eauto]. 
     destruct (f None (Some e')); simpl.
     destruct (X.compare x k'); try solve [absurd (X.eq x k'); eauto]; auto. 
     inversion_clear Hm'.
     destruct (IHm' H0 k' f) as (_,H2).
     case_eq (find x (map2_r f m')); auto; intros.
     absurd (In k' m').
     eapply sort_lt_notin; eauto.
     apply H2.
     exists e0.
     apply MapsTo_1 with x; auto.
     apply find_2; auto.
     inversion_clear Hm'.
     destruct (IHm' H x f) as (H2,H3).
     assert (X.lt k' x).
       admit. (* TODO *)
     destruct (X.compare x k'); try solve [absurd (X.lt k' x); eauto].
     destruct (f None (Some e')); simpl.
     destruct (X.compare x k'); try solve [absurd (X.lt k' x); eauto].
     apply H2; exists e; auto.
     apply H2; exists e; auto.
     unfold option_cons in H.
     destruct (f None (Some e')).
     destruct H.
     inversion_clear H.
     destruct H0; simpl in *; subst.
     exists e'; eauto.
     constructor; split; simpl; auto.
     inversion_clear Hm'.
     destruct (IHm' H x f) as (H2,H3).
     destruct H3 as (e'',H4).
     exists x0; auto.
     exists e''.
     constructor 2; auto.
     inversion_clear Hm'.
     destruct (IHm' H0 x f) as (H2,H3).
     destruct H3 as (e'',H4); auto.
     exists e''.
     constructor 2; auto.
     Qed.

     (** Specification of [map2] *)
     Lemma map2_1 : forall (elt elt' elt'':Set)(m: t elt)(Hm : sort (@lt_key elt) m)
        (m': t elt')(Hm' : sort (@lt_key elt') m')
	(x:key)(f:option elt->option elt'->option elt''), 
	In x m \/ In x m' -> 
        find x (map2 f m m') = f (find x m) (find x m'). 
     Proof.
     induction m.
     simpl; intros.
     clear Hm.
     destruct H.
     destruct H.
     inversion H.
     Admitted.

     Lemma map2_2 : forall (elt elt' elt'':Set)(m: t elt)(Hm : sort (@lt_key elt) m)
        (m': t elt')(Hm' : sort (@lt_key elt') m')
	(x:key)(f:option elt->option elt'->option elt''), 
        In x (map2 f m m') -> In x m \/ In x m'.
     Admitted.

     Lemma map2_sorted : forall (elt elt' elt'':Set)(m: t elt)(Hm : sort (@lt_key elt) m)
        (m': t elt')(Hm' : sort (@lt_key elt') m')
        (f:option elt->option elt'->option elt''), 
        sort (@lt_key elt'') (map2 f m m').
     Admitted.


End Raw.


Module Make (X: OrderedType) <: S with Definition key := X.t with Definition keq := X.eq.
  Module Raw := Raw X. 

  Definition key := X.t. 
  Definition keq := X.eq.

  Record slist (elt:Set) : Set :=  {this :> Raw.t elt; sorted : sort (@Raw.lt_key elt) this}.
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
     Build_slist (Raw.map2_sorted m.(sorted) m'.(sorted) f).
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

 Definition fold_1 m := @Raw.fold_1 elt m.(this) m.(sorted).

 Definition map_1 m := @Raw.map_1 elt elt' m.(this).
 Definition map_2 m := @Raw.map_2 elt elt' m.(this).

 Definition mapi_1 m := @Raw.mapi_1 elt elt' m.(this).
 Definition mapi_2 m := @Raw.mapi_2 elt elt' m.(this).

 Definition map2_1 m (m':t elt') := 
    @Raw.map2_1 elt elt' elt'' m.(this) m.(sorted) m'.(this) m'.(sorted).
 Definition map2_2 m (m':t elt') := 
    @Raw.map2_2 elt elt' elt'' m.(this) m.(sorted) m'.(this) m'.(sorted).

 Definition equal_1 m m' := @Raw.equal_1 elt m.(this) m.(sorted) m'.(this) m'.(sorted).
 Definition equal_2 m m' := @Raw.equal_2 elt m.(this) m.(sorted) m'.(this) m'.(sorted).

 End Elt.
End Make.



Module Make_ord (X: OrderedType)(Data : OrderedType) <: 
    Sord with Module Data := Data 
            with Definition MapS.key := X.t 
            with Definition MapS.keq := X.eq.

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
  destruct (Data.compare e e'); simpl; intuition. 
  absurd (Data.lt e e'); eauto.
  inversion_clear Hl.
  inversion_clear Hl'.
  destruct (IHl H (Build_slist H3)).
  unfold equal, eq in H5; simpl in H5; auto.
  absurd (Data.lt e' e); eauto.
  unfold cmp in H; destruct (Data.compare e e'); simpl in H; auto; discriminate.
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
     destruct (X.compare x x'); destruct (X.compare x' x); intuition; 
      try solve [absurd (X.eq x x'); eauto]. 
     inversion_clear Hm; inversion_clear Hm'.
     apply (IHm H (Build_slist H3)); auto.
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
         destruct (X.compare x x''); intros; auto; 
            try solve [ contradiction | 
                            absurd (X.lt x x''); eauto | 
                            absurd (X.lt x' x''); eauto | 
                            absurd (X.lt x'' x'); eauto ].
    split; intuition eauto.
     inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm3.
     apply (IHm1 H0 (Build_slist H5) (Build_slist H7)); intuition.
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
         destruct (X.compare x x''); intros; auto; 
            try solve [ contradiction | 
                            absurd (X.lt x x''); eauto | 
                            absurd (X.lt x' x''); eauto | 
                            absurd (X.lt x'' x'); eauto ].
    intuition; try solve [left; eauto].
    right. 
    split; eauto.
     inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm3.
     apply (IHm1 H1 (Build_slist H5) (Build_slist H7)); intuition.
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
    assert (Hm11 : sort (Raw.lt_key (elt:=Data.t)) m1).
     inversion_clear Hm1; auto.
    assert (Hm22 : sort (Raw.lt_key (elt:=Data.t)) m2).
     inversion_clear Hm2; auto.
    destruct (IHm1 Hm11 (Build_slist Hm22)).
    apply Lt; unfold lt; simpl; 
      destruct (X.compare x x'); try (right; auto); absurd (X.eq x x'); eauto.
    apply Eq; unfold eq; simpl; 
       destruct (X.compare x x'); auto; absurd (X.eq x x'); eauto.
    apply Gt; unfold lt; simpl;
     destruct (X.compare x' x); auto; absurd (X.eq x x'); eauto.
    apply Gt; unfold lt; simpl;
     destruct (X.compare x' x); auto; absurd (X.eq x x'); eauto.
    apply Gt; unfold lt; simpl;
     destruct (X.compare x' x); auto; absurd (X.lt x' x); eauto.
    Qed.

End Make_ord. 
