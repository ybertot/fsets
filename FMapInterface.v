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

(* $Id$ *)

(** This file proposes an interface for finite maps *)

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


(** When compared with Ocaml Map, this signature has been split in three: 
   - The first part [S] contains the usual operators (add, find, ...)
     It only requires a ordered key type, the data type can be arbitrary. 
   - The second part [S2] extends [S] with an [equal] operator on maps. 
     Here, the data type should have a decidable equality. 
   - Finally, [S3] extends [S] with a complete comparison fonction. For 
     that, the data type should have a decidable total ordering. 
*)      


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

    Parameter equal : (elt -> elt -> bool) -> t elt -> t elt -> bool.
    (** [equal cmp m1 m2] tests whether the maps [m1] and [m2] are equal, 
      that is, contain equal keys and associate them with equal data. 
      [cmp] is the equality predicate used to compare the data associated 
      with the keys. *)

    Section Spec. 
      
      Variable m m' m'' : t elt.
      Variable x y z : key.
      Variable e e' : elt.

      Parameter MapsTo : key -> elt -> t elt -> Prop.

      Definition In (k:key)(m: t elt) : Prop := exists e:elt, MapsTo k e m.

      Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

      Definition eq_key (p p':key*elt) := E.eq (fst p) (fst p').
      
      Definition eq_key_elt (p p':key*elt) := 
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

    (** Specification of [MapsTo] *)
      Parameter MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
      
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

    (** Specification of [fold] *)  
      Parameter
	fold_1 :
	forall (A : Set) (i : A) (f : key -> elt -> A -> A),
	  exists l : list (key*elt),
            Unique eq_key l /\
            (forall (k:key)(x:elt), MapsTo k x m <-> InList eq_key_elt (k,x) l) 
            /\
            fold f m i = fold_right (fun p => f (fst p) (snd p)) i l.
 
   Definition Equal cmp m m' := 
         (forall k, In k m <-> In k m') /\ 
         (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).  

   Variable cmp : elt -> elt -> bool. 

   (** Specification of [equal] *)
     Parameter equal_1 : Equal cmp m m' -> equal cmp m m' = true. 
     Parameter equal_2 : equal cmp m m' = true -> Equal cmp m m'.

    End Spec. 
   End Types. 

    (** Specification of [map] *)
      Parameter map_1 : forall (elt elt':Set)(m: t elt)(x:key)(e:elt)(f:elt->elt'), 
        MapsTo x e m -> MapsTo x (f e) (map f m).
      Parameter map_2 : forall (elt elt':Set)(m: t elt)(x:key)(f:elt->elt'), 
        In x (map f m) -> In x m.
 
    (** Specification of [mapi] *)
      Parameter mapi_1 : forall (elt elt':Set)(m: t elt)(x:key)(e:elt)
        (f:key->elt->elt'), MapsTo x e m -> 
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
      Parameter mapi_2 : forall (elt elt':Set)(m: t elt)(x:key)
        (f:key->elt->elt'), In x (mapi f m) -> In x m.

  Notation "∅" := empty.
  Notation "a ∈ b" := (In a b) (at level 20).
  Notation "a ∉ b" := (~ a ∈ b) (at level 20).

  Hint Immediate MapsTo_1 mem_2 is_empty_2.
  
  Hint Resolve mem_1 is_empty_1 is_empty_2 add_1 add_2 add_3 remove_1
    remove_2 remove_3 find_1 find_2 fold_1 map_1 map_2 mapi_1 mapi_2. 

End S.


Module Type Sord.
 
  Declare Module Data : OrderedType.   
  Declare Module MapS : S. 
  Import MapS.
  
  Definition t := MapS.t Data.t. 

  Parameter eq : t -> t -> Prop.
  Parameter lt : t -> t -> Prop. 
 
  Axiom eq_refl : forall m : t, eq m m.
  Axiom eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
  Axiom eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
  Axiom lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
  Axiom lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.

  Definition cmp e e' := match Data.compare e e' with Eq _ => true | _ => false end.	

  Parameter eq_1 : forall m m', Equal cmp m m' -> eq m m'.
  Parameter eq_2 : forall m m', eq m m' -> Equal cmp m m'.

  Parameter compare : forall m1 m2, Compare lt eq m1 m2.
  (** Total ordering between maps. The first argument (in Coq: Data.compare) 
      is a total ordering used to compare data associated with equal keys 
      in the two maps. *)

End Sord.