  (***********************************************************************)
  (*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
  (* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
  (*   \VV/  *************************************************************)
  (*    //   *      This file is distributed under the terms of the      *)
  (*         *       GNU Lesser General Public License Version 2.1       *)
  (***********************************************************************)

  (* Finite maps library.  
   * Authors: Pierre Letouzey and Pierre Courtieu 
   * Institution:  *)

  (** This file proposes an implementation of the non-dependant interface
   [FMapInterface.S] using lists of pairs ordered (increasing) with respect to
   left projection. *)

Require Import FMapInterface.
Require Import FSetInterface. 

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



Module Raw (X:OrderedType).
  Module E := X. (* À quoi cel sert-il? *)
  Module ME := OrderedTypeFacts X.

  Module PE := PairLeftOrderedType X.


  Definition key := X.t.
  Definition t := fun elt => list (PE.t elt). 
(*   fun elt : Set => (X.t * elt)%type.  *)

  Definition mapsto := 
    fun (A:Set) (eq_elt: A -> A -> Prop) (k:key) (e:A) => InList (PE.eq eq_elt) (k,e).

  Definition belong (A:Set) (eq_elt:A -> A -> Prop) (k:key) (m: t A) : Prop :=
    exists e:A, mapsto eq_elt k e m. 


  Section Elt.

    Variable elt : Set.
    Variables eq_elt lt_elt: elt -> elt -> Prop.
    Variable eq_elt_equiv : equivalence eq_elt.
    Variable lt_elt_order : order lt_elt.

    Hint Resolve 
      (equiv_refl elt eq_elt eq_elt_equiv)
      (equiv_trans elt eq_elt eq_elt_equiv)
      (equiv_sym elt eq_elt eq_elt_equiv)
      .

    Definition eq_key := @PE.eq_key elt.
    Definition eq_key_elt := @PE.eq elt eq_elt.

    Hint Unfold eq_key_elt eq_key PE.eq_key PE.eq.
    Hint Resolve (@PE.eq_eq_key elt eq_elt).

    Definition ltkey := @PE.lt elt.
(*     Notation MapsTo := (@mapsto _ eq_elt). *)
    Definition MapsTo := fun k e => InList eq_key_elt (k,e).
(*     Definition MapsTo := fun k e => InList (@PE.eq elt eq_elt) (k,e). *)

(*     Definition In (k:key)(m: t elt) : Prop := exists e:elt, MapsTo k e m. *)
(*     Definition In (k:key)(m: t elt) : Prop := exists e:elt, mapsto eq_elt k e m. *)
    Definition In (k:key)(m: t elt) := belong eq_elt k m.


    Lemma InList_eq_key_el_eq_key : 
      forall x m,InList eq_key_elt x m -> InList eq_key x m.
      intros x m hyp. induction hyp;auto.
    Qed.
      
    Hint Unfold MapsTo mapsto eq_key_elt eq_key belong In.
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

    Hint Extern 2 (eq_key_elt ?a ?b) => split.

    Lemma InList_In_eq_key : forall k e l, InList eq_key (k,e) l -> In k l.
      unfold eq_key.
      intros k e l H. clear lt_elt_order.
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

    Hint Resolve (@PE.lt_not_eq elt) (@PE.eq_sym elt) (@PE.eq_trans elt) (@PE.lt_trans elt) (ME.lt_eq).



    Lemma eq_key_no_ltkey : forall x x',eq_key x x' -> ~ltkey x x'.
      intros x x' abs1 abs2.
      destruct x;destruct x'.
      simpl in abs1.
      absurd (E.eq k k0); auto.
    Qed.

    Hint Resolve eq_key_no_ltkey. 


    Lemma eq_key_elt_no_ltkey : forall x x',eq_key_elt x x' -> ~ltkey x x'.
      intros x x' abs1.
      destruct x;destruct x'.
      destruct abs1;auto.
    Qed.

    Hint Resolve eq_key_elt_no_ltkey. 


    Lemma ltkey_trans : forall e e' e'', ltkey e e' -> ltkey e' e'' -> ltkey e e''.
      intros e e' e''.
      case e. case e'. case e'';simpl;eauto. 
    Qed.

    Lemma ltkey_eq_key : forall e e' e'', ltkey e e' -> eq_key e' e'' -> ltkey e e''.
      intros e e' e''.
      case e. case e'. case e''.
      intros k e0 k0 e1 k1 e2 ltk eqk.
      simpl in *.
      eapply ME.lt_eq;eauto.
    Qed.

    Hint Resolve ltkey_eq_key.

    Lemma eq_key_ltkey : forall e e' e'', ltkey e e'' -> eq_key e e' -> ltkey e' e''.
      intros e e' e''.
      case e. case e'. case e''.
      simpl.
      intros k e0 k0 e1 k1 e2 ltk eqk.
      assert (PE.E.eq k0 k1);eauto.
      eapply ME.eq_lt;eauto.
    Qed.

    Hint Resolve eq_key_ltkey.

    Lemma eq_key_refl : forall e, eq_key e e.
      intro e. case e. simpl; eauto.
    Qed.

    Lemma eq_key_elt_refl : forall e, eq_key_elt e e.
      intro e. case e. simpl; eauto.
    Qed.

    Lemma eq_key_sym : forall e e', eq_key e e' -> eq_key e' e.
      intros e e'. case e. case e';eauto.
    Qed.

    Lemma eq_key_elt_sym : forall e e', eq_key_elt e e' -> eq_key_elt e' e.
      intros e e'. case e. case e';simpl.
      intros k e0 k0 e1 hyp.
      decompose [and] hyp.
      eauto. 
    Qed.

    Lemma eq_key_trans : forall e e' e'', eq_key e e' -> eq_key e' e'' -> eq_key e e''.
      intros e e' e''. case e. case e'. case e''. simpl. eauto.
    Qed.

    Lemma eq_key_elt_trans : forall e e' e'', 
      eq_key_elt e e' -> eq_key_elt e' e'' -> eq_key_elt e e''.
      intros e e' e''. case e. case e'. case e''. simpl.
      intros k e0 k0 e1 k1 e2 hyp1 hyp2.
      elim hyp1. elim hyp2. eauto.
    Qed.

    Hint Resolve eq_key_trans eq_key_elt_trans eq_key_sym eq_key_elt_sym eq_key_refl 
      eq_key_elt_refl.

    Notation Sort := (sort (ltkey)).

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
      apply ltkey_trans with e';auto.
      inversion sorted.
      inversion H4.
      assumption.
    Qed.
      
    Hint Resolve lt_sort_tl2.

    Lemma all_lt_lelist: forall x l, 
      (forall e, InList eq_key_elt e l -> ltkey x e) -> lelistA ltkey x l.
      intros x l H. destruct l;auto.
    Qed.

    Hint Resolve all_lt_lelist.

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
    Lemma sort_in_tl : forall e l e', Sort (e::l) -> InList eq_key e' l -> ltkey e e'.
      intros e l e' sorted Hin.
      induction Hin;eauto.

      apply ltkey_eq_key with y;eauto.
      inversion sorted.
      subst.
      inversion H3;eauto.
    Qed.

    Lemma sort_in : forall l e e', Sort (e::l) -> InList eq_key e' (e::l) 
      -> ltkey e e' \/ eq_key e e'.
      intros l e e' sorted Hin.
      inversion Hin;eauto.
      left.
      apply sort_in_tl with l;assumption.
    Qed.

    Lemma sort_lt_notin : forall l k e (sorted : Sort l), 
      lelistA ltkey (k,e) l ->  ~In k l.
      intros l k e sorted Hlt.
      inversion Hlt.
      intro abs. inversion abs. inversion H0. 
      intro Hin. subst.
      inversion Hin.
      assert (ltkey b (k,x) \/ eq_key b (k,x)).
      eapply sort_in with l0. auto.
      auto.
      decompose [or] H1;clear H1.
      assert (ltkey (k,x) b).
      apply ltkey_right_l with e;assumption.
      absurd (ltkey b (k, x));auto.
      destruct b.
      simpl.
      apply ME.lt_not_gt;auto.

      destruct b.
      simpl in H2.
      simpl in H.
(*       destruct H2. *)
      absurd (eq_key (k0,e0) (k, x) ); simpl;eauto.
(*       intro abs;destruct abs. *)
(*       elim (E.lt_not_eq H); eauto. *)
    Qed.



    Lemma sort_lt_notin2 : forall l k e (sorted : Sort l), 
      lelistA ltkey (k,e) l -> ~(exists e:elt, InList eq_key (k,e) l).
      intros l k e sorted Hlt.
      inversion Hlt.
      intro abs. inversion abs. inversion H0. 
      intro Hin. subst.
      inversion Hin.
      assert (ltkey b (k,x) \/ eq_key b (k,x)).
      eapply sort_in with l0. auto.
      auto.
      decompose [or] H1;clear H1.
      assert (ltkey (k,x) b).
      apply ltkey_right_l with e;assumption.
      absurd (ltkey b (k, x));auto.
      destruct b.
      simpl.
      apply ME.lt_not_gt;auto.

      destruct b.
      simpl in H2.
      simpl in H.
(*       destruct H2. *)
      absurd (eq_key (k0,e0) (k, x) ); simpl;eauto.
(*       intro abs;destruct abs. *)
(*       elim (E.lt_not_eq H); eauto. *)
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
      

    Lemma lelist_eq : forall x x' l, 
      eq_key x x' -> lelistA ltkey x l -> lelistA ltkey x' l.
      intros x x' l H H0.
      induction H0;auto.
      assert (ltkey x' b).
      eapply eq_key_ltkey with x;auto.
      eauto.
    Qed.

    Hint Resolve lelist_eq.

    Lemma sorted_in_cons_not_eq : forall x l k e (sorted:Sort ((k,e)::l)) (Hin: In x l),
      ~E.eq x k.
      intros x l k e sorted.
      inversion sorted.
      intros Hin.
      intro abs.
      absurd (In x l);auto.
      eapply sort_lt_notin with e;auto.      
      eapply lelist_eq with (k,e);simpl;auto.
    Qed.


  (** Very useful lemma. It means that if the list of pairs is sorted, then there
      is unicity (modulo eq_elt) of MapsTo. *)

    Lemma Equal_refl : forall m, Sort m -> eq eq_elt m m.
      intros m sorted.
      unfold eq,Equal.
      intros e e' e''.
      split. split;auto.
      unfold MapsTo,mapsto.
      intros mapsto1 mapsto2.
      induction mapsto1.

      inversion mapsto2.
      destruct y.
      dec_eq_key_elt. dec_eq_key_elt.
      eauto.

      destruct y.
      subst.      
      simpl in H.
      decompose [and] H.
      absurd (E.eq e k);auto.
      eapply sorted_in_cons_not_eq with l e0;eauto.

      apply IHmapsto1;eauto.
      inversion mapsto2;try assumption.
      destruct y.
      absurd (E.eq e k);simpl in H0;decompose [and] H0;auto.
      eapply sorted_in_cons_not_eq with l e0;eauto.
    Qed.


Ltac Equal_inv m x e e' := 
  assert (_Equal_hyp: eq eq_elt m m);
    [ apply Equal_refl;assumption
  | unfold eq,Equal in _Equal_hyp;elim (_Equal_hyp x e e')
  ].



    Lemma MapsTo_sorted_eq_elt :  forall x m e e', Sort m -> MapsTo x e m 
      -> MapsTo x e' m -> eq_elt e e'.
      intros x m e e' sorted.
      Equal_inv m x e e'. (* m is sorted, so MapsTo is unique modulo eq_elt *)
      auto.
    Qed.

    Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> E.eq k k' \/ In k l.
      intros k k' e l H.
      inversion H. inversion H0; simpl in * ;eauto;intuition.
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

    Definition empty : t elt := [].

    (** Specification of [empty] *)
    Lemma empty_1 : Empty empty.
      unfold Empty,empty,MapsTo.
      intros a e.
      intro abs.
      inversion abs.
    Qed.

    Hint Resolve empty_1.

    Definition is_empty (l : t elt) : bool := if l then true else false.

    (** Specification of [is_empty] *)
    Lemma is_empty_1 :forall m, Empty m -> is_empty m = true. 
      unfold Empty,MapsTo,mapsto.
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

    Lemma mem_1 : forall x m, Sort m -> In x m -> mem x m = true.
      intros x m.      
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


    Lemma mem_2 : forall x m, Sort m -> mem x m = true -> In x m. 
      intros x m;unfold In,MapsTo,belong,mapsto.
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

    Lemma find_2 :  forall x m e, find x m = Some e -> MapsTo x e m.
      intros x m. unfold MapsTo,mapsto.
      functional induction find x m;simpl;intros e' eqfind; inversion eqfind; auto.
    Qed.


    Lemma find_1 :  forall x m e e', Sort m -> MapsTo x e m -> find x m = Some e' 
      -> eq_elt e e'.
      intros x m e e' sorted mapsto1 eqfind.
      assert (MapsTo x e' m).
      apply find_2;assumption.
      eapply MapsTo_sorted_eq_elt;eauto.
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
    Lemma add_1 : forall m x e y, E.eq y x -> MapsTo y e (add x e m).
      intros m x e.
      unfold MapsTo,mapsto.
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
      elim H0;auto.
    Qed.

    Lemma aux''' : forall x x' l, 
      InList eq_key x l -> eq_key x x' -> InList eq_key x' l.
      intros x x' l H H0.
      induction H;eauto.
    Qed.


    Hint Resolve aux'' aux'.

    Lemma add_2 :forall x e' m y e, 
      ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
      intros x e' m. unfold MapsTo,mapsto.
      functional induction add x e' m;simpl;auto.
      intros y' e' eqky' mapsto1.
      
      assert (InList eq_key_elt (y', e') l);auto;intuition. 
      solve [ (* eauto is too slow *)
	(eapply aux' with k' y; try assumption; intro;eauto) 
	| idtac "falling back to eauto, you should adapt the script. " ; eauto ] .  

      intros y' e' eqky' mapsto1.
      elim (@In_inv3 (y',e') (k',y) l);auto.
    Qed.
      
    Lemma add_3 : forall x e' m e y,
      ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
      intros x e' m. unfold MapsTo,mapsto.
      functional induction add x e' m;simpl;eauto.
      intros e' y' eqky' Hinlist.
      inversion Hinlist;eauto.
    Qed.
      
   (* Definition singleton (x : elt) : t elt := x :: [].  *)

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


    Lemma eq_key_lelist :forall x x' l, 
      eq_key x x' -> lelistA ltkey x l -> lelistA ltkey x' l.
    Proof.
      intros x x' l eqxx' lelxl.
      inversion lelxl;eauto.
    Qed.


   (** Specification of [remove] *)
    Lemma remove_1 :forall x y m, Sort m -> E.eq y x -> ~ In y (remove x m).
      intros x y m.
      functional induction remove x m;simpl;intros;auto.

      subst.
      eapply sort_lt_notin with x.
      eauto.
      apply cons_leA;simpl.
      eapply ME.lt_eq;eauto.
      
      eapply sort_lt_notin with x. eauto. 
      inversion H.
      eapply eq_key_lelist with (k',x) ;simpl;auto.
      intuition; eauto.

      assert (notin:~ In y (remove k l)). apply H;eauto.
      intro abs.
      inversion abs.
      unfold MapsTo,mapsto in H2.
      elim notin.
      inversion H2; eauto. 
      simpl in H4.
      decompose [and] H4.
      absurd (PE.E.eq y k');eauto.
      Qed.
      
      
    Lemma remove_2 : forall x y e m, 
      Sort m -> ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
      intros x y e m. unfold MapsTo,mapsto.
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


    Lemma remove_3 : forall x y e m, Sort m -> MapsTo y e (remove x m) -> MapsTo y e m.
      intros x y e m. unfold MapsTo,mapsto.
      functional induction remove x m;auto.
      intros sorted inlist.
      elim (@In_inv3 (y, e) (k', x) (remove k l)); auto.
      intros inlist2.
      eauto.
    Qed.


    (** Specification of [MapsTo] *)
    Lemma MapsTo_1 : forall x y e m, E.eq x y -> MapsTo x e m -> MapsTo y e m.
      unfold MapsTo,mapsto.
      intros x y e m eqxy inlist.
      induction inlist;eauto.

      apply InList_cons_hd;auto.
      eapply eq_key_elt_trans with (x, e);auto.
    Qed.


(* 
    Definition compare (elt_eq:forall e e', Compare lt_elt (Logic.eq (A:=elt)) e e'): 
      forall m m' : t elt, Compare (lt lt_elt) (eq eq_elt) m m'.
 *)


    Fixpoint fold (A:Set) (acc:A) (f:key -> elt -> A -> A) (m:t elt) {struct m} : A :=
      match m with
	| [] => acc
	| (k,e)::m' => f k e (fold acc f m')
      end.


    

(*       Definition eq_key_elt := eq_key_elt. *)
(* 	fun (p p':key*elt) => E.eq (fst p) (fst p') /\ (snd p) = (snd p'). *)

	(** Specification of [fold] *)  
      Lemma fold_1' :
	forall (A : Set) (acc : A) (f : key -> elt -> A -> A) (m: t elt),
          Sort m -> 
	  exists l : list (key*elt),
            Sort l /\
            (forall (k:key)(x:elt), MapsTo k x m <-> InList eq_key_elt (k,x) l) 
            /\
            fold acc f m = fold_right (fun p => f (fst p) (snd p)) acc l.
        intros A acc f m.
        functional induction fold A acc f m ;intro sorted;subst.
        exists (@nil (PE.t elt)). 
	split;[|split;[intros ;split|]];subst;auto.

	clear eq_elt_equiv lt_elt_order.
	elim H;eauto.
	clear H. intros x hyp.
	decompose [and] hyp. clear hyp.
        exists ((k, e) ::x);intuition.

(* 	apply sorted_unique. *)
	apply cons_sort;auto.
	assert (lelistA ltkey (k, e) m').

	inversion sorted;auto.

	apply all_lt_lelist.
	intros e' hyp.
	destruct e'.
	elim (H1 k0 e0);intros .
	assert (InList eq_key_elt (k0, e0) m').
	apply H4;assumption.
	eapply sort_in_tl with m';auto.

	unfold MapsTo,mapsto in H0.
	inversion H0.
	auto.
	apply InList_cons_tl.
	
	elim (H1 k0 x0);intros .
	auto.

	inversion H0.
	auto.
	unfold MapsTo,mapsto.
	apply InList_cons_tl.
	
	elim (H1 k0 x0).
	intros H6 H7.	
	unfold MapsTo,mapsto in H7.
	auto.

	rewrite H2.
	simpl.
	trivial.
      Qed.
	



	

      Lemma fold_1 :
	forall (A : Set) (acc : A) (f : key -> elt -> A -> A) (m: t elt),
          Sort m -> 
	  exists l : list (key*elt),
            Unique eq_key l /\
            (forall (k:key)(x:elt), MapsTo k x m <-> InList eq_key_elt (k,x) l) 
            /\
            fold acc f m = fold_right (fun p => f (fst p) (snd p)) acc l.
	intros A acc f m H.
	elim (@fold_1' A acc f m H).
	clear eq_elt_equiv lt_elt_order.
	intros x H0.	
	exists x;intuition;auto.
	apply sorted_unique;auto.
      Qed.
        


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



      Variable elt':Set.
      
      Fixpoint map (f:elt -> elt') (m:t elt) {struct m} : t elt' :=
	match m with
	  | [] => []
	  | (k,e)::m' => (k,f e) :: map f m'
	end.

      Lemma map_1 : forall (x:key)(e:elt)(m:t elt)(f:elt->elt'), 
        MapsTo x e m -> 
        exists e', eq_elt e e' /\ mapsto (@Logic.eq elt') x (f e') (map f m).
      Proof.
	intros x e m f.
	functional induction map f m.
	intro abs. inversion abs.
	intros mapsto1.
	inversion mapsto1.
	subst.
	exists e0.
	split.
	elim H1;auto.
	unfold mapsto.
	apply InList_cons_hd.
	split;auto.
	elim H1;auto.

	subst.
	elim H;eauto. clear H.
	intros x0 H.
	elim H. clear H.
	intros H H2.
	exists x0;auto.
      Qed.


      Lemma map_2 :forall (x:key)(m:t elt)(f:elt->elt'), 
        belong (@Logic.eq elt') x (map f m) -> In x m.
	unfold belong,mapsto.
	intros x m f. 
	functional induction map f m.
	intros hyp.
	inversion hyp.
	inversion H.

	intros hyp.
	inversion hyp. clear hyp.
	inversion H0.
	simpl in H2.
	elim H2. clear H2.
	eauto.

	elim H;eauto.
	intros x1 H4.
	exists x1;auto.
      Qed.


      Fixpoint mapi (f: key -> elt -> elt') (m:t elt) {struct m} : t elt' :=
	match m with
	  | [] => []
	  | (k,e)::m' => (k,f k e) :: mapi f m'
	end.


    (** Specification of [mapi] *)
      Lemma mapi_1 : forall (x:key)(e:elt)(m:t elt)
        (f:key->elt->elt'), MapsTo x e m -> 
        exists x', exists e', 
	  E.eq x' x /\ mapsto (@Logic.eq elt') x (f x' e') (mapi f m).
      Proof.
	intros x e m f.
	functional induction mapi f m.
	intro abs. inversion abs.

	intros mapsto1.
	inversion mapsto1.
	subst.
	exists k.
	exists e0.
	split.
	elim H1;auto.
	unfold mapsto.
	apply InList_cons_hd.
	split;auto.
	elim H1;auto.

	subst.
	elim H;eauto. clear H.
	intros x0 H.
	elim H. clear H.
	intros x1 hyp.
	elim hyp. clear hyp.
	intros H0 H2.
	exists x0. 
	exists x1.
	auto.
      Qed.

      Lemma mapi_2 : forall (x:key)(m:t elt) (f:key->elt->elt'),
	belong (@Logic.eq elt') x (mapi f m) -> In x m.
	unfold belong,mapsto.
	intros x m f. 
	functional induction mapi f m.
	intros hyp.
	inversion hyp.
	inversion H.

	intros hyp.
	elim hyp. clear hyp.
	intros x0 hyp.
	inversion hyp.
	simpl in H1.
	elim H1. clear H1.
	eauto.

	subst.
	elim H;eauto.
	intros x1 H0.
	exists x1;auto.
      Qed.

    End Elt.

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
