(* $Id$ *)

(** Map interface *)

Require Export Bool.
Require Export List.
Require Export Sorting.
Require Export Setoid.
Set Implicit Arguments.
Unset Strict Implicit.
Implicit Arguments equivalence.
Implicit Arguments reflexive.
Implicit Arguments transitive.
Implicit Arguments symmetric.
Implicit Arguments antisymmetric.

Require Import FSetInterface. 


(** * Non-dependent signature

    Signature [S] presents sets as purely informative programs 
    together with axioms *)

Module Type S.

  Declare Module E : OrderedType.
  Definition key := E.t.

  Parameter t : Set -> Set. (** the abstract type of maps *)
 
  Section Types. 

  Variable elt:Set.

  Parameter empty : t elt.
  (** The empty map. *)

  Parameter is_empty : t elt -> bool.
  (** Test whether a map is empty or not. *)

  Parameter add : key -> elt -> t elt -> t elt.
  (** [add x y m] returns a map containing the same bindings as [m], 
      plus a binding of [x] to [y]. If [x] was already bound in [m], 
      its previous binding disappears. *)

  Parameter find : key -> t elt -> option elt. 
  (** [find x m] returns the current binding of [x] in [m], 
      or raises [Not_found] if no such binding exists.
      NB: in Coq, the exception mechanism becomes a option type. *)

  Parameter remove : key -> t elt -> t elt.
  (** [remove x m] returns a map containing the same bindings as [m], 
      except for [x] which is unbound in the returned map. *)

  Parameter mem : key -> t elt -> bool.
  (** [mem x m] returns [true] if [m] contains a binding for [x], 
      and [false] otherwise. *)

(* bugée?: *)
(*   Parameter eq : t elt -> t elt -> Prop. *)
(* plutôt ça? attention refl,trans et sym sont
   conditionnée par refl trans et sym de l'égalité sur les éléments *)
  Parameter eq : (elt -> elt -> Prop) -> t elt -> t elt -> Prop.
  Parameter lt : (elt -> elt -> Prop) -> t elt -> t elt -> Prop.

(* bugée ?: *)
(* 
  Parameter compare : 
    forall lt_elt : elt -> elt -> Prop, 
    (forall e e', Compare lt_elt (Logic.eq (A:=elt)) e e') -> 
    forall m m' : t elt, Compare (lt lt_elt) eq m m'.
 *)

  Parameter compare : 
    forall eq_elt lt_elt : elt -> elt -> Prop, 
      (forall e e', Compare lt_elt (Logic.eq (A:=elt)) e e') -> 
      forall m m' : t elt, Compare (lt lt_elt) (eq eq_elt) m m'.



  (** Total ordering between maps. The first (in Coq: second) argument is 
      a total ordering used to compare data associated with equal keys 
      in the two maps. *)

  Parameter equal : (elt -> elt -> bool) -> t elt -> t elt -> bool.
  (** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are equal, 
      that is, contain equal keys and associate them with equal data. 
      [cmp] is the equality predicate used to compare the data associated 
      with the keys. *)

  (** Coq comment: [iter] is useless in a purely functional world *)
  (** val iter : (key -> 'a -> unit) -> 'a t -> unit *)
  (** iter f m applies f to all bindings in map m. f receives the key as 
      first argument, and the associated value as second argument. 
      The bindings are passed to f in increasing order with respect to the 
      ordering over the type of the keys. Only current bindings are 
      presented to f: bindings hidden by more recent bindings are not 
      passed to f. *)

  Variable elt' : Set. 

  Parameter map : (elt -> elt') -> t elt -> t elt'.
  (** [map f m] returns a map with same domain as [m], where the associated 
      value a of all bindings of [m] has been replaced by the result of the
      application of [f] to [a]. The bindings are passed to [f] in 
      increasing order with respect to the ordering over the type of the 
      keys. *)

  Parameter mapi : (key -> elt -> elt') -> t elt -> t elt'.
  (** Same as [S.map], but the function receives as arguments both the 
      key and the associated value for each binding of the map. *)

  Parameter fold : forall A: Set, (key -> elt -> A -> A) -> t elt -> A -> A.
  (** [fold f m a] computes [(f kN dN ... (f k1 d1 a)...)], 
      where [k1] ... [kN] are the keys of all bindings in [m] 
      (in increasing order), and [d1] ... [dN] are the associated data. *)

  Section Spec. 
 
  Variable m m' m'' : t elt.
  Variable x y z : key.
  Variable e e' : elt.

  Parameter MapsTo : key  -> elt -> t elt -> Prop.
  Definition In (k:key)(m: t elt) : Prop := exists e:elt, MapsTo k e m. 
  Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

  Definition Equal f m m' := forall (a : key) (e e': elt), 
   (In a m <-> In a m') /\
   (MapsTo a e m -> MapsTo a e' m' -> f e e' = true). 



  Section Eq. 
    Variable eq_elt: elt -> elt -> Prop.
    (** Specification of [eq] *)
    Parameter eq_equiv: equivalence eq_elt -> equivalence (eq eq_elt).
  End Eq.

(*  Definition Add (x : key) (s s' : t) :=
    forall y : key, In y s' <-> E.eq y x \/ In y s.
  Definition For_all (P : key -> Prop) (s : t) :=
    forall x : key, In x s -> P x.
  Definition Exists (P : key -> Prop) (s : t) :=
    exists x : key, In x s /\ P x. *)

  (** Specification of [MapsTo] *)
  Parameter MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
  



  (** Specification of [lt] *)
  Section Lt. 
  Variable lt_elt : elt -> elt -> Prop. 
  Variable eq_elt : elt -> elt -> Prop. 
  Parameter lt_trans :  transitive lt_elt. (* plus? *)
  Parameter lt_not_eq : 
    (forall e e', lt_elt e e' -> e<>e') ->  
    lt lt_elt m m' -> ~ eq eq_elt m m'.
  End Lt.

  (** Specification of [mem] *)
  Parameter mem_1 : In x m -> mem x m = true.
  Parameter mem_2 : mem x m = true -> In x m. 
 
  (** Specification of [empty] *)
  Parameter empty_1 : Empty empty.

  (** Specification of [is_empty] *)
  Parameter is_empty_1 : Empty m -> is_empty m = true. 
  Parameter is_empty_2 : is_empty m = true -> Empty m.
 
  (** Specification of [add] *)
  Parameter add_1 : E.eq y x -> MapsTo y e (add x e m).
  Parameter add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Parameter add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.

  (** Specification of [remove] *)
  Parameter remove_1 : E.eq y x -> ~ In y (remove x m).
  Parameter remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
  Parameter remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.

  (** Specification of [find] *)
  Parameter find_1 : MapsTo x e m -> find x m = Some e. 
  Parameter find_2 : find x m = Some e -> MapsTo x e m.


  Definition key_eq := 
    fun (p p':key*elt) => E.eq (fst p) (fst p').
 
  Definition key_elt_eq := 
    fun (p p':key*elt) => E.eq (fst p) (fst p') /\ (snd p) = (snd p').

  (** Specification of [fold] *)  
  Parameter
    fold_1 :
      forall (A : Set) (i : A) (f : key -> elt -> A -> A),
      exists l : list (key*elt),
        Unique key_eq l /\
        (forall (k:key)(x:elt), MapsTo k x m <-> InList key_elt_eq (k,x) l) 
        /\
        fold f m i = fold_right (fun p => f (fst p) (snd p)) i l.

  (** Specification of [equal] *) 
  Variable f: elt->elt->bool.
  Parameter equal_1 : Equal f m m' -> equal f m m' = true.
  Parameter equal_2 : equal f m m' = true -> Equal f m m.

  
  End Spec. 
  End Types. 

  (** Specification of [map] *)
  Parameter map_1 : forall (elt elt':Set)(x:key)(e:elt)(m:t elt)(f:elt->elt'), 
   MapsTo x e m -> MapsTo x (f e) (map f m).
  Parameter map_2 : forall (elt elt':Set)(x:key)(m:t elt)(f:elt->elt'), 
   In x (map f m) -> In x m.

  (** Specification of [mapi] *)
  Parameter mapi_1 : forall (elt elt':Set)(x:key)(e:elt)(m:t elt)
   (f:key->elt->elt'), MapsTo x e m -> 
     exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
  Parameter mapi_2 : forall (elt elt':Set)(x:key)(m:t elt)
   (f:key->elt->elt'), In x (mapi f m) -> In x m.

  
  Notation "âˆ…" := empty.
  Notation "a âˆˆ b" := (In a b) (at level 20).
  Notation "a âˆ‰ b" := (~ a âˆˆ b) (at level 20).
  Notation "a â‰¡ b" := (Equal a b) (at level 20).
  Notation "a â‰¢ b" := (~ a â‰¡ b) (at level 20).

(* 
  Hint Immediate In_1.
  
  Hint Resolve mem_1 mem_2 equal_1 equal_2 subset_1 subset_2 empty_1
    is_empty_1 is_empty_2 choose_1 choose_2 add_1 add_2 add_3 remove_1
    remove_2 remove_3 singleton_1 singleton_2 union_1 union_2 union_3 inter_1
    inter_2 inter_3 diff_1 diff_2 diff_3 filter_1 filter_2 filter_3 for_all_1
    for_all_2 exists_1 exists_2 partition_1 partition_2 elements_1 elements_2
    elements_3 min_elt_1 min_elt_2 min_elt_3 max_elt_1 max_elt_2 max_elt_3.
*)

End S.
