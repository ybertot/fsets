  (***********************************************************************)
  (*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
  (* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
  (*   \VV/  *************************************************************)
  (*    //   *      This file is distributed under the terms of the      *)
  (*         *       GNU Lesser General Public License Version 2.1       *)
  (***********************************************************************)

  (* Finite sets library.  
   * Authors: Pierre Letouzey and Pierre Courtieu 
   * Institution:  *)

  (** This file proposes an implementation of the non-dependant 
      interface [FMapInterface.S] using lists of
      pairs ordered (increasing) with respect to
      left projection. *)

Require Import FMapInterface.
Require Import FSetInterface. 

Set Implicit Arguments.
Unset Strict Implicit.

  (** Usual syntax for lists. *)
Notation "[]" := nil (at level 0).


(* Comment définir un OrderedType sur les paires à partir d'un OrderedType et
   d'un type quelconque en prenant l'ordre sur la projection gauche. *)

(* Type quelconque *)
Module Type TypeAlone.
  Parameter t:Set.
End TypeAlone.

Module OrderedTypePair(X:OrderedType).

  Module E := X. (* À quoi cela sert-il? *)
  Module ME := OrderedTypeFacts X.
  Definition key := X.t.
(*   Definition elt := Elt.t. *)

    
  Section Elt.
    Variable elt:Set.
    
    Definition t := (key*elt)%type.

    Definition eq (c1 c2: key * elt):Prop :=
      let (x,y) := c1 in let (x',y') := c2 in  E.eq x x'.

    Definition lt (c1 c2: key * elt):Prop :=
      let (x,y) := c1 in let (x',y') := c2 in  E.lt x x'.

    Lemma eq_refl : forall e, eq e e.
      intro e. case e;simpl;auto.
    Qed.

    Lemma eq_sym : forall e e', eq e e' -> eq e' e.
      intros e e'. case e. case e'. simpl;auto.
    Qed.

    Lemma eq_trans : forall e e' e'', eq e e' -> eq e' e'' -> eq e e''.
      intros e e' e''. case e. case e'. case e''. simpl;eauto.
    Qed.

    Lemma lt_not_eq : forall e e', lt e e' -> ~eq e e'.
      intros e e'. case e. case e'. simpl;auto.
    Qed.

    Lemma lt_trans : forall e e' e'', lt e e' -> lt e' e'' -> lt e e''.
      intros e e' e''. case e. case e'. case e''. simpl;eauto.
    Qed.

    Definition compare (e e' : t) : Compare lt eq e e'.
      intros e e'.
      case e. case e'.
      intros k e0 k0 e1.
      case (E.compare k0 k);intro hyp.
      apply Lt. simpl;assumption.
      apply Eq. simpl;assumption.
      apply Gt. simpl;assumption.
    Defined.
  End Elt.
End OrderedTypePair.
      
(*
Module OrderedTypePairValid (X:OrderedType) (Elt:TypeAlone): OrderedType.
  Module E:=X.
  Module MOTP:=OrderedTypePair X.
  Definition key := X.t.
  Definition elt := Elt.t.
  Definition t := (key*elt)%type.
  Definition eq (c1 c2: key * elt):Prop :=
    let (x,y) := c1 in let (x',y') := c2 in  E.eq x x'.

  Definition lt (c1 c2: key * elt):Prop :=
    let (x,y) := c1 in let (x',y') := c2 in  E.lt x x'.

  Definition eq_refl := @MOTP.eq_refl elt.

  Definition eq_sym := @MOTP.eq_sym elt.
      
  Definition eq_trans := @MOTP.eq_trans elt.

  Definition lt_not_eq := @MOTP.lt_not_eq elt.

  Definition lt_trans := @MOTP.lt_trans elt.

  Definition compare := @MOTP.compare elt.
End OrderedTypePairValid.


Module OrderedTypePairFacts (X:OrderedType) (Elt:TypeAlone).
  Module OTV := (OrderedTypePairValid X Elt).   
  Module Facts := OrderedTypeFacts OTV.
  Export Facts.
End OrderedTypePairFacts.

*)


Module Raw (X:OrderedType).
  Module E := X. (* À quoi cel sert-il? *)
  Module ME := OrderedTypeFacts X.

  Module PE := OrderedTypePair X.
(* 
  Module PEF := OrderedTypePairFacts X T. 
 *)

  Definition key := X.t.
  Definition t := fun elt:Set => list (key*elt).

  Section Elt.

    Variable elt : Set.

    
    Definition eqkey := @PE.eq elt.

    Hint Unfold eqkey.

    Definition eqkey' (c1 c2: key * elt):Prop := 
      let (x,y) := c1 in let (x',y') := c2 in  E.eq x x'.

    Definition ltkey := @PE.lt elt.
    Definition ltkey' (c1 c2: key * elt):Prop :=
      let (x,y) := c1 in let (x',y') := c2 in  E.lt x x'.

    Definition MapsTo := fun k e => InList eqkey (k,e).
    Definition In (k:key)(m: t elt) : Prop := exists e:elt, MapsTo k e m. 
    Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

    Definition Equal (eq: elt -> elt -> Prop) m m' := forall (a : key) (e e': elt), 
      (In a m <-> In a m') /\
      (MapsTo a e m -> MapsTo a e' m' -> eq e e'). 

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


    Lemma ltkey_right_r : forall x k e e', ltkey x (k,e) -> ltkey x (k,e').
      intros x. case x. trivial.
    Qed.

    Lemma ltkey_right_l : forall x k e e', ltkey (k,e) x -> ltkey (k,e') x.
      intros x. case x. trivial.
    Qed.

    Hint Resolve ltkey_right_l ltkey_right_r.

    Hint Resolve (@PE.lt_not_eq elt) (@PE.eq_sym elt) (@PE.eq_trans elt) (@PE.lt_trans elt) (@ME.lt_eq).
    Lemma eqkey_no_ltkey : forall x x',eqkey x x' -> ~ltkey x x'.
      intros x x' abs1 abs2.
      absurd (eqkey x x'); auto.
    Qed.

    Hint Resolve eqkey_no_ltkey. 

    Lemma ltkey_trans : forall e e' e'', ltkey e e' -> ltkey e' e'' -> ltkey e e''.
      intros e e' e''.
      case e. case e'. case e'';simpl;eauto. 
    Qed.

    Lemma ltkey_eqkey : forall e e' e'', ltkey e e' -> eqkey e' e'' -> ltkey e e''.
      intros e e' e''.
      case e. case e'. case e'';simpl;eauto. intros.
      eapply ME.lt_eq;eauto.
    Qed.

    Hint Resolve ltkey_eqkey.

    Lemma eqkey_sym : forall e e', eqkey e e' -> eqkey e' e.
      intros e e'. case e. case e';eauto.
    Qed.

    Notation Sort := (sort (ltkey)).


    Lemma lt_sort_tl : forall e e' l (sorted:Sort (e::e'::l)), Sort (e::l).
      intros e e' l sorted.
      inversion sorted.
      inversion H1.
      apply cons_sort.
      assumption.
      inversion H6.
      apply nil_leA.
      apply cons_leA.
      subst.
      apply ltkey_trans with e';auto.
      inversion sorted.
      inversion H4.
      assumption.
    Qed.
      
    Hint Resolve lt_sort_tl.

    Lemma sort_in_tl : forall e l e', Sort (e::l) -> InList eqkey e' l -> ltkey e e'.
      intros e l e' sorted Hin.
      induction Hin;eauto.

      apply ltkey_eqkey with y;eauto.
      inversion sorted.
      subst.
      inversion H3;eauto.
    Qed.

    Lemma sort_in : forall l e e', Sort (e::l) -> InList eqkey e' (e::l) 
      -> ltkey e e' \/ eqkey e e'.
      intros l e e' sorted Hin.
      inversion Hin;eauto.
      left.
      apply sort_in_tl with l;assumption.
    Qed.

     
(*     Lemma ltkey_no_eqkey : forall x x',ltkey x x' -> ~eqkey x x'.       *)
(*       intros x x'. *)
(*       apply (@PE.lt_not_eq elt). *)
(*       case x. case x'. *)
(*       intros. *)
(*       unfold eqkey. *)
(*       apply PE.lt_not_eq. *)
(*       simpl. *)
(*       intros k e k0 e0 H. *)
(*       apply E.lt_not_eq;assumption. *)
(*     Qed. *)


    Lemma sort_lt_notin : 
      forall l (sorted : Sort l) k e (Hlt : lelistA ltkey (k,e) l), ~In k l.
      intros l sorted k e Hlt.
      inversion Hlt.
      intro abs. inversion abs. inversion H0. 

      intro Hin.

      subst.
      inversion Hin.
      assert (ltkey b (k,x) \/ eqkey b (k,x)).      
      eapply sort_in with l0. auto.
      info auto.
      decompose [or] H1.
      assert (ltkey (k,x) b).
      apply ltkey_right_l with e;assumption.
      absurd (ltkey b (k, x));auto.
      generalize H3.
      case b;simpl;intros.
      apply ME.lt_not_gt;auto.

      absurd (eqkey (k, x) b);eauto.
    Qed.

    Lemma InList_In : forall k e l, InList eqkey (k,e) l -> In k l.
      intros k e l H. exists e;auto.
    Qed.
    Hint Resolve InList_In.
      


    Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> E.eq k k' \/ In k l.
      intros k k' e l H.
      inversion H. inversion H0;eauto.
    Qed.
      


    Definition empty : t elt := [].

    Definition is_empty (l : t elt) : bool := if l then true else false.

      (** ** The set operations. *)

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



      
      
    
    Lemma mem_1 : forall x m, Sort m -> In x m -> mem x m = true.
      intros x m.      
      functional induction mem x m;intros sorted belong;trivial.
      
      inversion belong. inversion H.
      
      absurd (In k ((k', e) :: l));try assumption.
      eapply sort_lt_notin with e;auto.

      apply H.
      elim (sort_inv sorted);auto.
      elim (In_inv belong);auto.
      intro abs.
      absurd (E.eq k k');auto.
    Qed.      

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

    (*   Definition singleton (x : elt) : t elt := x :: [].  *)

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

    (* Utile?
      Fixpoint union (s : t elt) : t elt -> t :=
	match s with
	| [] => fun s' => s'
	| (k,x) :: l =>
            (fix union_aux (s' : t elt) : t elt :=
               match s' with
               | [] => s
               | (k',x') :: l' =>
		   match E.compare k k' with
		   | FSetInterface.Lt _ => (k,x) :: union l s'
		   | FSetInterface.Eq _ => (k,x) :: union l l'
		   | FSetInterface.Gt _ => (k',x') :: union_aux l'
		   end
               end)
	end.
     *)


    Fixpoint equal (compare:elt -> elt -> bool) (s : t elt) {struct s} : t elt -> bool :=
      fun s' : t elt =>
	match s, s' with
	  | [], [] => true
	  | (k,x) :: l, (k',x') :: l' =>
            match E.compare k k' with
              | FSetInterface.Eq _ => if compare x x' then equal compare l l' else false
              | _ => false
            end
	  | _, _ => false
	end.






(*

    Section Iterators.
      Variable elt' : Set. 
      Axiom map : (elt -> elt') -> t elt -> t elt'.
      Axiom mapi : (key -> elt -> elt') -> t elt -> t elt'.
      Axiom fold : forall A: Set, (key -> elt -> A -> A) -> t elt -> A -> A.
    End Iterators.
*)
    Section Spec. 
      
      Variable m m' m'' : t elt.
      Variable x y z : key.
      Variable e e' : elt.

(* 
      Definition ltfst (c1 c2: Raw.key * elt):Prop :=
	match c1,c2 with
	  | (x,y),(x',y') => E.lt x x'
	end.
 *)


      Section Eq_elt.
	Variables eq_elt lt_elt: elt -> elt -> Prop.
	Variable eq_elt_refl : FMapInterface.Eq_elt.eq_elt_refl eq_elt.

	Definition compare : 
	  (forall e e', Compare lt_elt (Logic.eq (A:=elt)) e e') -> 
	  forall m m' : t elt, Compare (lt lt_elt) (eq eq_elt) m m'.

      Lemma eq_refl : eq eq_elt m m.
	unfold eq, Equal.
	intros a e0 e'0.

	
	exact eq_refl.

      Axiom eq_sym : eq m m' -> eq m' m.
      Axiom eq_trans : eq m m' -> eq m' m'' -> eq m m''.


      (** Specification of [MapsTo] *)
      Lemma MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
	unfold E.eq.
	intros hyp1 hyp2.
	unfold MapsTo in hyp2.
	induction hyp2.
	generalize H.
	case y0.
	intros k e0 H0.
	assert (X.eq y x).
	apply X. tran

	
	unfold eqkey in H0.
	unfold MapsTo.
	apply InList_cons_hd.
	unfold eqkey.

	eapply H0.
	

	

      
	(** Specification of [lt] *)
      Section Lt. 
	Variable lt_elt : elt -> elt -> Prop. 
	Axiom lt_trans : 
	  (forall e e' e'', lt_elt e e' -> lt_elt e' e'' -> lt_elt e e'') -> 
	  lt lt_elt m m' -> lt lt_elt m' m'' -> lt lt_elt m m''.
	Axiom lt_not_eq : 
	  (forall e e', lt_elt e e' -> e<>e') ->  
	  lt lt_elt m m' -> ~ eq m m'.
      End Lt.

	(** Specification of [mem] *)
      Axiom mem_1 : In x m -> mem x m = true.
      Axiom mem_2 : mem x m = true -> In x m. 
      
	(** Specification of [empty] *)
      Axiom empty_1 : Empty empty.

	(** Specification of [is_empty] *)
      Axiom is_empty_1 : Empty m -> is_empty m = true. 
      Axiom is_empty_2 : is_empty m = true -> Empty m.
      
	(** Specification of [add] *)
      Axiom add_1 : E.eq y x -> MapsTo y e (add x e m).
      Axiom add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
      Axiom add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.

	(** Specification of [remove] *)
      Axiom remove_1 : E.eq y x -> ~ In y (remove x m).
      Axiom remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
      Axiom remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.

	(** Specification of [find] *)
      Axiom find_1 : MapsTo x e m -> find x m = Some e. 
      Axiom find_2 : find x m = Some e -> MapsTo x e m.


      Definition key_eq := 
	fun (p p':key*elt) => E.eq (fst p) (fst p').
      
      Definition key_elt_eq := 
	fun (p p':key*elt) => E.eq (fst p) (fst p') /\ (snd p) = (snd p').

	(** Specification of [fold] *)  
      Axiom
	fold_1 :
	forall (A : Set) (i : A) (f : key -> elt -> A -> A),
	  exists l : list (key*elt),
            Unique key_eq l /\
            (forall (k:key)(x:elt), MapsTo k x m <-> InList key_elt_eq (k,x) l) 
            /\
            fold f m i = fold_right (fun p => f (fst p) (snd p)) i l.

	(** Specification of [equal] *) 
      Variable f: elt->elt->bool.
      Axiom equal_1 : Equal f m m' -> equal f m m' = true.
      Axiom equal_2 : equal f m m' = true -> Equal f m m.

    
    End Spec. 
  End Elt.

  Section Iterators_facts.
    Variable elt elt':Set.

      (** Specification of [map] *)
    Axiom map_1 : forall (x:key)(e:elt)(m:t elt)(f:elt->elt'), 
      MapsTo x e m -> MapsTo x (f e) (map f m).
    
    Axiom map_2 : forall (elt':Set)(x:key)(m: t elt)(f:elt->elt'), 
      In x (map f m) -> In x m.

	  (** Specification of [mapi] *)
    Axiom mapi_1 : forall (elt':Set)(x:key)(e:elt)(m: t elt)
      (f:key->elt->elt'), MapsTo x e m -> 
      exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
    Axiom mapi_2 : forall (elt':Set)(x:key)(m: t elt)
      (f:key->elt->elt'), In x (mapi f m) -> In x m.
  End Iterators_facts.

End Raw.


Module Make (X: OrderedType) <: S with Module E := X.
  Module E := X.
  Module Raw := Raw X. 

  Section orderedPairList.
    Variable elt:Set.

    Record spairlist : Set :=  {
      this :> Raw.t elt;
      sorted : sort ltfst this
    }.

    Definition t := spairlist. 
  End orderedPairList.

  Definition elt := X.t.

  Definition empty := Raw.empty.
  Definition is_empty := Raw.is_empty .
  Definition add := Raw.add .
  Definition find := Raw.find . 
  Definition remove := Raw.remove .
  Definition mem := Raw.mem .
  Definition eq := Raw.eq .
  Definition lt := Raw.lt .
  Definition compare := Raw.compare .
  Definition equal := Raw.equal .

(*   Variable elt' : Set.  *)

  Definition map := Raw.map .
  Definition mapi := Raw.mapi .
  Definition fold := Raw.fold.
  Definition MapsTo := Raw.MapsTo .
  Definition In:= Raw.In. 
  Definition Empty := Raw.Empty.
  Definition Equal := Raw.Equal.
  Definition MapsTo_1 := Raw.MapsTo_1 .
  Definition eq_refl := Raw.eq_refl . 
  Definition eq_sym := Raw.eq_sym .
  Definition eq_trans := Raw.eq_trans .
  Variable lt_elt : elt -> elt -> Prop. 
  Definition lt_trans := Raw.lt_trans .
  Definition lt_not_eq := Raw.lt_not_eq .

  Definition mem_1 := Raw.mem_1 .
  Definition mem_2 := Raw.mem_2 . 
 
  Definition empty_1 := Raw.empty_1 .

  Definition is_empty_1 := Raw.is_empty_1 . 
  Definition is_empty_2 := Raw.is_empty_2 .

  Definition add_1 := Raw.add_1 .
  Definition add_2 := Raw.add_2 .
  Definition add_3 := Raw.add_3 .

  (** Specification of [remove] *)
  Definition remove_1 := Raw.remove_1 .
  Definition remove_2 := Raw.remove_2 .
  Definition remove_3 := Raw.remove_3 .

  (** Specification of [find] *)
  Definition find_1 := Raw.find_1 . 
  Definition find_2 := Raw.find_2 .


  Definition key_eq := Raw.key_eq.
  Definition key_elt_eq := Raw.key_elt_eq.

  Definition fold_1 := Raw.fold_1 .

  Definition equal_1 := Raw.equal_1 .
  Definition equal_2 := Raw.equal_2 .


  (** Specification of [map] *)
  Definition map_1 := Raw.map_1 .
  Definition map_2 := Raw.map_2 .

  (** Specification of [mapi] *)
  Definition mapi_1 := Raw.mapi_1 .
  Definition mapi_2 := Raw.mapi_2 .
End Make.













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
