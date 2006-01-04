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
Implicit Arguments equivalence.
Implicit Arguments order.
Implicit Arguments reflexive.
Implicit Arguments transitive.
Implicit Arguments symmetric.
Implicit Arguments antisymmetric.

(** Usual syntax for lists. *)
Notation "[]" := nil (at level 0).

(*
Module PairLeftOrderedType(X:OrderedType).

  Module E := X. (* À quoi cela sert-il? *)
  Module ME := OrderedTypeFacts X.
  Definition key := X.t.
    
  Section Elt.
    Variable elt:Set.
    Variable eq_elt:elt -> elt -> Prop.
    Variable eq_elt_equiv:equivalence eq_elt.

    Hint Resolve (equiv_refl _ _ eq_elt_equiv) (equiv_trans _ _ eq_elt_equiv)
      .

    Definition t := (key*elt)%type.

    Definition eq (c1 c2: key * elt):Prop :=
      let (x,y) := c1 in let (x',y') := c2 in  E.eq x x' /\ eq_elt y y'.

    Definition eq_key (c1 c2: key * elt):Prop :=
      let (x,y) := c1 in let (x',y') := c2 in  E.eq x x'.

    Definition lt (c1 c2: key * elt):Prop :=
      let (x,y) := c1 in let (x',y') := c2 in  E.lt x x'.


    Lemma eq_eq_key : forall e e', eq e e' -> eq_key e e'.
      intros e e'.
      case e. case e'. simpl.
      intros k e0 k0 e1 hyp.
      decompose [and] hyp;auto. 
      (* do not use intuition here, because it produces a dependency on
         eq_elt_equiv above*)
    Qed.

    Lemma eq_refl : forall e, eq e e.
      intro e. case e;simpl; auto.
    Qed.

    Lemma eq_key_refl : forall e, eq_key e e.
      intro e. case e;simpl; auto.
    Qed.

    Lemma eq_sym : forall e e', eq_key e e' -> eq_key e' e.
      intros e e'. case e. case e'. simpl. intuition.
    Qed.

    Lemma eq_key_sym : forall e e', eq_key e e' -> eq_key e' e.
      intros e e'. case e. case e'. simpl;intuition.
    Qed.

    Lemma eq_trans : forall e e' e'', eq e e' -> eq e' e'' -> eq e e''.
      intros e e' e''. case e. case e'. case e''. simpl;intuition;eauto.
    Qed.

    Lemma eq_key_trans : forall e e' e'', eq_key e e' -> eq_key e' e'' -> eq_key e e''.
      intros e e' e''. case e. case e'. case e''. simpl;intuition;eauto.
    Qed.

    Lemma lt_not_eq : forall e e', lt e e' -> ~eq e e'.
      intros e e'. case e. case e'. simpl.
      intros k e0 k0 e1 H.
      intro abs;destruct abs.
      elim (E.lt_not_eq H); assumption.
    Qed.

    Lemma lt_not_eq_key : forall e e', lt e e' -> ~eq_key e e'.
      intros e e'. case e. case e'. simpl.
      intros k e0 k0 e1 H.
      intro abs.
      elim (E.lt_not_eq H); assumption.
    Qed.

    Lemma lt_trans : forall e e' e'', lt e e' -> lt e' e'' -> lt e e''.
      intros e e' e''. case e. case e'. case e''. simpl;eauto.
    Qed.

  End Elt.
End PairLeftOrderedType.
*)


Module Raw (X:OrderedType).
  Module E := X. (* À quoi cel sert-il? *)
  Module ME := OrderedTypeFacts X.

(*  Module PE := PairLeftOrderedType X. *)

  Definition key := X.t.
  Arguments Scope list [type_scope].
  Definition t (elt:Set) := list (X.t * elt).

  Section Elt.

  Variable elt : Set.

  Definition eq_key (p p':key*elt) := E.eq (fst p) (fst p').
  Definition eq_key_elt (p p':key*elt) := 
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Definition lt_key (p p':key*elt) := E.lt (fst p) (fst p').

  Definition MapsTo (k:key)(e:elt):= InList eq_key_elt (k,e).
  Definition In k m := exists e:elt, MapsTo k e m.
  Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.
  Definition Equal m m' := forall (a : key) (e e': elt), 
      (In a m <-> In a m') /\
      (MapsTo a e m -> MapsTo a e' m' -> e = e'). 

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

    Hint Resolve ME.lt_eq.

    Lemma eq_key_no_lt_key : forall x x', eq_key x x' -> ~lt_key x x'.
      intros (k,e) (k',e') abs1 abs2.
      absurd (E.eq k k'); auto.
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
      eapply ME.lt_eq;eauto.
    Qed.

    Hint Resolve lt_key_eq_key.

    Lemma eq_key_lt_key : forall e e' e'', lt_key e e'' -> eq_key e e' -> lt_key e' e''.
      intros (k,e) (k',e') (k'',e'').
      unfold lt_key, eq_key; simpl; intros.
      apply ME.eq_lt with k;eauto.
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

(*    Lemma sorted_hd_all_lt: forall x l e, 
      Sort (x::l) -> InList eq_key_elt e l -> ltkey x e.
      intros x l e sorted inl.
      induction inl;eauto.
      assert (ltkey x y);eauto.
      inversion sorted.
      inversion H3;auto.
    Qed.

    Hint Resolve sorted_hd_all_lt.
*)
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
      apply ME.lt_not_gt;auto.

      destruct b.
      unfold eq_key in H2; simpl in H2.
      unfold lt_key in H; simpl in H.
      absurd (E.eq k0 k); simpl;eauto.
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
      apply ME.lt_not_gt;auto.

      destruct b.
      unfold eq_key in H2; simpl in H2.
      unfold lt_key in H; simpl in H.
      absurd (E.eq k0 k); simpl;eauto.
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
      ~E.eq x k.
      intros x l k e sorted.
      inversion sorted.
      intros Hin.
      intro abs.
      absurd (In x l);auto.
      eapply sort_lt_notin with e;auto.      
      eapply Inf_eq with (k,e);simpl;auto.
    Qed.

    Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> E.eq k k' \/ In k l.
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
      absurd (E.eq k k');auto.
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
	  match E.compare k k' with
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
      absurd (E.eq k k'); auto.
      unfold eq_key_elt in H0; simpl in H0; intuition. 
      assert (H2 := sort_in_tl Hm (InList_eq_key_el_eq_key H0)).
      unfold lt_key in H2; simpl in H2; intuition. 
      absurd (E.lt k k'); auto.
    
     intros.
     inversion_clear H.
     unfold eq_key_elt in H0; simpl in H0; intuition congruence. 
     assert (H2 := sort_in_tl Hm (InList_eq_key_el_eq_key H0)).
     unfold lt_key in H2; simpl in H2; intuition. 
     absurd (E.eq k k'); auto.

     intros.
     inversion_clear H0.
     absurd (E.eq k k'); auto.
     unfold eq_key_elt in H1; simpl in H1; intuition.
     eauto.
    Qed.


    Fixpoint add (k : key) (x : elt) (s : t elt) {struct s} : t elt :=
      match s with
	| [] => (k,x) :: []
	| (k',y) :: l =>
          match E.compare k k' with
            | FSetInterface.Lt _ => (k,x)::s
            | FSetInterface.Eq _ => (k,x)::l
            | FSetInterface.Gt _ => (k',y) :: add k x l
          end
      end.


    (** Specification of [add] *)

    Lemma add_1 : forall m x y e, E.eq y x -> MapsTo y e (add x e m).
      intros m x y e; generalize y; clear y.
      unfold MapsTo.
      functional induction add x e m;simpl;auto.
    Qed.

    Lemma aux' : forall k k' e e' l, 
      InList eq_key (k, e) ((k', e') :: l) -> ~ E.eq k k' -> InList eq_key (k, e) l.
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
      ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
      intros m x  y e e'. 
      generalize y e; clear y e; unfold MapsTo.
      functional induction add x e' m;simpl;auto.
      intros y' e' eqky' mapsto1.
      
      assert (InList eq_key_elt (y', e') l); intuition; eauto.

      intros y' e' eqky' mapsto1.
      elim (@In_inv3 (y',e') (k',y) l);auto.
    Qed.
      
    Lemma add_3 : forall m x y e e',
      ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
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
     simpl; case (E.compare x x''); intuition.
  Qed.
  Hint Resolve add_Inf.

  Lemma add_sorted : forall m (Hm:Sort m) x e, Sort (add x e m).
  Proof.
  induction m.
  simpl; intuition.
  intros.
  destruct a as (x',e').
  simpl; case (E.compare x x'); intuition; inversion_clear Hm; auto.
  constructor; auto.
  apply Inf_eq with (x',e'); auto.
  Qed.  

  Fixpoint remove (k : key) (s : t elt) {struct s} : t elt :=
      match s with
	| [] => []
	| (k',x) :: l =>
          match E.compare k k' with
            | FSetInterface.Lt _ => s
            | FSetInterface.Eq _ => l
            | FSetInterface.Gt _ => (k',x) :: remove k l
          end
      end.  


   (** Specification of [remove] *)

    Lemma remove_1 : forall m (Hm:Sort m) x y, E.eq y x -> ~ In y (remove x m).
      intros m Hm x y; generalize Hm; clear Hm.
      functional induction remove x m;simpl;intros;auto.

      subst.
      eapply sort_lt_notin with x.
      eauto.
      apply cons_leA;simpl.
      unfold lt_key; eapply ME.lt_eq;eauto.
      
      eapply sort_lt_notin with x. eauto. 
      inversion Hm.
      eapply Inf_eq with (k',x) ;simpl;auto.
      intuition; eauto.

      assert (notin:~ In y (remove k l)). apply H;eauto.
      intros (x0,abs).
      inversion_clear abs; eauto. 
      dec_eq_key_elt; simpl in *; subst.
      absurd (E.eq y k');eauto.
      Qed.
      
      
    Lemma remove_2 : forall m (Hm:Sort m) x y e, 
      ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
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
     simpl; case (E.compare x x''); intuition.
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
  simpl; case (E.compare x x'); intuition; inversion_clear Hm; auto.
  Qed.  


    (** Specification of [MapsTo] *)

    Lemma MapsTo_1 : forall m x y e, E.eq x y -> MapsTo x e m -> MapsTo y e m.
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

(* 	apply sorted_unique. *)
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
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
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

End Raw.


Module Make (X: OrderedType) <: S with Module E := X.
  Module E := X.
  Module Raw := Raw X. 

  Record slist (elt:Set) : Set :=  {this :> Raw.t elt; sorted : sort (@Raw.lt_key elt) this}.
  Definition t (elt:Set) := slist elt. 

  Definition key := X.t.

 Section Elt. 
 Variable elt elt':Set. 

 Implicit Types m : t elt.

 Definition empty := Build_slist (Raw.empty_sorted elt).
 Definition is_empty m := Raw.is_empty m.(this).
 Definition add x e m := Build_slist (Raw.add_sorted m.(sorted) x e).
 Definition find x m := Raw.find x m.(this).
 Definition remove x m := Build_slist (Raw.remove_sorted m.(sorted) x). 
 Definition mem x m := Raw.mem x m.(this).
 Definition map f m : t elt' := Build_slist (Raw.map_sorted m.(sorted) f).
 Definition mapi f m : t elt' := Build_slist (Raw.mapi_sorted m.(sorted) f).
 Definition fold A f m i := @Raw.fold elt A f m.(this) i.

 Definition MapsTo x e m := Raw.MapsTo x e m.(this).
 Definition In x m := Raw.In x m.(this).
 Definition Empty m := Raw.Empty m.(this).

 Definition eq_key (p p':key*elt) := E.eq (fst p) (fst p').
     
 Definition eq_key_elt (p p':key*elt) := 
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

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

 
 End Elt.


End Make.


(* TO BE CONTINUED ....








 
    Definition eq := Equal.
    
    Inductive lt (ltelt: elt -> elt -> Prop) : t elt -> t elt -> Prop :=
      | lt_nil : forall (k: key) (x : elt) (s : t elt), lt ltelt [] ((k,x) :: s)
      | lt_cons_lt : 
	forall k x k' y (s s' : t elt), 
	  E.lt k k' -> lt ltelt ((k,x) :: s) ((k',y) :: s')
      | lt_cons_eq_lt :
        forall k x k' y (s s' : t elt), 
	  E.eq k k' -> ltelt x y -> lt ltelt ((k,x) :: s) ((k',y) :: s').
    Hint Constructors lt.



 
(* 
    Definition compare (elt_eq:forall e e', Compare lt_elt (Logic.eq (A:=elt)) e e'): 
      forall m m' : t elt, Compare (lt lt_elt) (eq eq_elt) m m'.
 *)


(*
  (** Very useful lemma. It means that if the list of pairs is sorted, then there
      is unicity of MapsTo. *)

    Lemma Equal_refl : forall m, Sort m -> Equal m m.
      intros m sorted.
      unfold Equal.
      intros e e' e''.
      split. split;auto.
      unfold MapsTo.
      intros mapsto1 mapsto2.
      induction mapsto1.

      inversion mapsto2.
      destruct y.
      unfold eq_key_elt in H1,H; simpl in H1,H.
      intuition congruence.

      destruct y.
      subst.      
      dec_eq_key_elt; simpl in *.
      absurd (E.eq e k);auto.
      eapply sorted_in_cons_not_eq with l e0;eauto.

      apply IHmapsto1;eauto.
      inversion mapsto2;try assumption.
      destruct y.
      dec_eq_key_elt; simpl in *.
      absurd (E.eq e k); auto.
      eapply sorted_in_cons_not_eq with l e0;eauto.
    Qed.

Ltac Equal_inv m x e e' := 
  assert (_Equal_hyp: Equal m m);
    [ apply Equal_refl;assumption
  | unfold Equal in _Equal_hyp;elim (_Equal_hyp x e e')
  ].

    Lemma MapsTo_sorted_eq_elt :  forall k m e e', Sort m -> MapsTo k e m 
      -> MapsTo k e' m -> e = e'.
      intros x m e e' sorted.
      Equal_inv m x e e'. (* m is sorted, so MapsTo is unique modulo eq_elt *)
      auto.
    Qed.
*)


      (** Specification of [equal] *) 
      Variable fcompare: elt->elt->bool.
      Variable fcompare_ok1:forall e e', fcompare e e' = true -> eq_elt e e'.
      Variable fcompare_ok2:forall e e', fcompare e e' = false -> ~eq_elt e e'.

      Fixpoint equal (s : t elt) {struct s} : t elt -> bool :=
	fun s' : t elt =>
	  match s, s' with
	    | [], [] => true
	    | (k,x) :: l, (k',x') :: l' =>
              match E.compare k k' with
		| FSetInterface.Eq _ => if fcompare x x' then equal l l' else false
		| _ => false
              end
	    | _, _ => false
	  end.

       
      Axiom XXX: forall x e l, In x l -> In x (e::l).
      Axiom YYY: forall a k x l, (In a ((k, x) :: l)) -> ~E.eq a k -> (In a l).

      Lemma InList_eq_key : forall x x' l,
	InList eq_key x l -> eq_key x x' -> InList eq_key x' l.
	intros x x' l H H0.
	induction H;eauto.
      Qed.
	

      Lemma unique_in_eq_key : forall x x' l, Unique eq_key (x'::l)
	-> InList eq_key_elt x (x'::l) -> eq_key x x' -> eq_key_elt x x'.
	intros x x' l uniq inl eqk.
	inversion inl;auto.
	subst.
	inversion uniq.
	elim H2.
	assert ( inl2 : InList eq_key x l );auto.
	eapply InList_eq_key with x;auto.
      Qed.

      Lemma unique_in_eq_key2 : forall x x' l, Unique eq_key l
	-> InList eq_key_elt x l -> InList eq_key_elt x' l 
	-> eq_key x x' -> eq_key_elt x x'.
	intros x x' l uniq inl1 inl2 eqk.
	induction inl1.
	inversion inl2.
	eauto.
	absurd (InList eq_key y l).
	inversion uniq.
	assumption.

	subst.
	eapply InList_eq_key with x'. auto. eauto.

	apply IHinl1.
	inversion uniq;auto.
	eapply aux'' with y;auto.
	intro abs.
	absurd (InList eq_key x' l);eauto 5.
	2: eapply InList_eq_key with x;auto.
	intro abs2.
	inversion uniq.
	elim H1.
	eapply InList_eq_key with x';auto.
      Qed.


      Lemma ZZZ : forall a e e' l, 
	Unique eq_key l -> MapsTo a e l -> MapsTo a e' l -> eq_elt e e'.
	unfold MapsTo,mapsto.
	intros a e e' l sorted inl1 inl2.

(*
	assert (Unique eq_key l). apply sorted_unique;auto. *)
	induction sorted.
	inversion inl1. 

	elim (@In_inv3 (a, e) x l);auto;intro hyp.
	assert (eq2:eq_key_elt (a, e) (a,e')).
	eapply eq_key_elt_trans with x;auto.
	apply eq_key_elt_sym.
	eapply unique_in_eq_key with l;auto.
	simpl in hyp.
	destruct x;intuition.
	simpl in eq2;intuition.

	assert ( eqk : eq_key_elt (a,e) (a,e'));try (simpl in *;intuition;fail).
	eapply unique_in_eq_key2 with (x::l);simpl;eauto.
      Qed.	


      Lemma equal_1 : forall m m', Sort m -> Sort m' 
	-> Equal eq_elt m m' -> equal m m' = true.
	intros m m'. unfold Equal.
	functional induction equal m m';simpl;auto;subst
	  ; intros sorted1 sorted2 big
	    ; [destruct t0 as [k x];elim (big k x x) |elim (big k x x)|elim (big k x x)

	      |apply H;eauto;clear H;intros a e' e'';elim(big a e' e'')

	      |elim (big k x x')|elim (big k' x x)];clear big
	      ; try (intros hyp1 hyp2;elim hyp1 ; clear hyp1; intros in1 in2).


	absurd (In k []);eauto. 
	absurd (In k []);eauto.
	absurd (In k ((k', x') :: l')).
	eapply sort_lt_notin with x;auto. 
	eauto.

	split.
	split.
	intro inal.
	assert (noteqak : ~ E.eq a k).
	eapply sorted_in_cons_not_eq with l x;auto.

	assert (In a ((k', x') :: l')).
	apply in1.
	apply XXX;auto.
	eapply YYY with k' x';auto.
	intro abs.
	elim noteqak; eauto.

	intro inal'.
	assert (noteqak : ~ E.eq a k').
	eapply sorted_in_cons_not_eq with l' x';auto.
	assert (In a ((k, x) :: l)).
	apply in2.
	apply XXX;auto.
	eapply YYY with k x;auto.
	intro abs.
	elim noteqak; eauto.

	intros mapsto1 mapsto2.
	apply hyp2;auto.

	absurd (eq_elt x x');auto 6.
	
	absurd (In k' ((k, x) :: l)).
	eapply sort_lt_notin with x';auto.
	eauto.
      Qed.


      Lemma equal_2 :forall m m', Sort m -> Sort m' -> 
	equal m m' = true -> Equal eq_elt m m.
	intros m m'. unfold Equal.
      	functional induction equal m m';simpl;auto;subst;intro eq1;auto
	  ; intros hyp hyp2 a e' e''; try (inversion hyp2;fail)
	    ;(split;[split;auto|]);intros H1 H2. 
	inversion H1.
	eapply ZZZ with a ((k, x) :: l);auto.
        apply sorted_unique;auto.
      Qed.




















Axiom eq: nat -> nat -> Prop.
Axiom eqall: forall n m:nat, eq n m.
Definition lt := Peano.lt.
Axiom eq_refl : forall x : nat, eq x x.
Axiom eq_sym : forall x y : nat, eq x y -> eq y x.
Axiom eq_trans : forall x y z : nat, eq x y -> eq y z -> eq x z.

Axiom lt_trans : forall x y z : nat, lt x y -> lt y z -> lt x z.
Axiom lt_not_eq : forall x y : nat, lt x y -> ~ eq x y.

Require Import Compare_dec.
Require Import Arith.
Require Import Le.
Require Import Lt.
Module A : OrderedType.
  Definition t := nat.


  Definition compare : forall x y : nat, Compare lt eq x y.
    intros n m.
    assert ({n < m} + {n = m} + {m < n}).
    apply lt_eq_lt_dec.
    destruct H.
    destruct s.
    apply Lt. 
    assumption.
    apply Eq. 
    apply eqall.
    apply Gt.
    assumption.
  Qed.



  


  Definition eq := eq.
  Definition lt := lt.
  Definition eq_refl:= eq_refl.
  Definition eq_sym:= eq_sym.
  Definition eq_trans:= eq_trans.
  Definition lt_trans:= lt_trans.
  Definition lt_not_eq:= lt_not_eq.
End A.

Module B : S with Module E:=A.


  Eval compute in (Raw.equal ((1,23)::(2,34)::[]) ((1,23)::(2,34)::[])).

*)
