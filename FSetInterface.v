(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Finite sets library.  
 * Authors: Pierre Letouzey and Jean-Christophe Filliâtre 
 * Institution: LRI, CNRS UMR 8623 - Université Paris Sud
 *              91405 Orsay, France *)

(* $Id$ *)

(** Set interfaces *)

Require Export Bool.
Require Export List.
Require Export Sorting.
Require Export Setoid.
Set Implicit Arguments.
Unset Strict Implicit.

(** Misc properties used in specifications. *)

Section Misc.
Variable A B : Set.
Variable eqA : A -> A -> Prop. 
Variable eqB : B -> B -> Prop.

(** Compatibility of a  boolean function with respect to an equality. *)
Definition compat_bool (f : A -> bool) :=
  forall x y : A, eqA x y -> f x = f y.

(** Compatibility of a predicate with respect to an equality. *)
Definition compat_P (P : A -> Prop) := forall x y : A, eqA x y -> P x -> P y.

(** Being in a list modulo an equality relation. *)
Inductive InList (x : A) : list A -> Prop :=
  | InList_cons_hd :
      forall (y : A) (l : list A), eqA x y -> InList x (y :: l)
  | InList_cons_tl :
      forall (y : A) (l : list A), InList x l -> InList x (y :: l).

Hint Constructors InList.

Lemma InList_alt : forall x l, InList x l <-> exists y, eqA x y /\ List.In y l.
Proof. 
 induction l; intuition.
 inversion H.
 firstorder.
 inversion H1; firstorder.
 firstorder; subst; auto.
Qed.

(** A list without redondancy. *)
Inductive Unique : list A -> Prop :=
  | Unique_nil : Unique nil
  | Unique_cons :
      forall (x : A) (l : list A),
      ~ InList x l -> Unique l -> Unique (x :: l).

End Misc.

Hint Constructors InList.
Hint Constructors Unique.
Hint Constructors sort.
Hint Constructors lelistA.
Hint Unfold compat_bool compat_P.

(** * Ordered types *)

Inductive Compare (X : Set) (lt eq : X -> X -> Prop) (x y : X) : Set :=
  | Lt : lt x y -> Compare lt eq x y
  | Eq : eq x y -> Compare lt eq x y
  | Gt : lt y x -> Compare lt eq x y.

Module Type OrderedType.

  Parameter t : Set.

  Parameter eq : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.

  Axiom eq_refl : forall x : t, eq x x.
  Axiom eq_sym : forall x y : t, eq x y -> eq y x.
  Axiom eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
 
  Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.

  Parameter compare : forall x y : t, Compare lt eq x y.

  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans lt_not_eq lt_trans.

End OrderedType.

(** * Non-dependent signature

    Signature [S] presents sets as purely informative programs 
    together with axioms *)

Module Type S.

  Declare Module E : OrderedType.
  Definition elt := E.t.

  Parameter t : Set. (** the abstract type of sets *)
 
  Parameter empty : t.
  (** The empty set. *)

  Parameter is_empty : t -> bool.
  (** Test whether a set is empty or not. *)

  Parameter mem : elt -> t -> bool.
  (** [mem x s] tests whether [x] belongs to the set [s]. *)

  Parameter add : elt -> t -> t.
  (** [add x s] returns a set containing all elements of [s],
  plus [x]. If [x] was already in [s], [s] is returned unchanged. *)

  Parameter singleton : elt -> t.
  (** [singleton x] returns the one-element set containing only [x]. *)

  Parameter remove : elt -> t -> t.
  (** [remove x s] returns a set containing all elements of [s],
  except [x]. If [x] was not in [s], [s] is returned unchanged. *)

  Parameter union : t -> t -> t.
  (** Set union. *)

  Parameter inter : t -> t -> t.
  (** Set intersection. *)

  Parameter diff : t -> t -> t.
  (** Set difference. *)

  Parameter eq : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.
  Parameter compare : forall s s' : t, Compare lt eq s s'.
  (** Total ordering between sets. Can be used as the ordering function
  for doing sets of sets. *)

  Parameter equal : t -> t -> bool.
  (** [equal s1 s2] tests whether the sets [s1] and [s2] are
  equal, that is, contain equal elements. *)

  Parameter subset : t -> t -> bool.
  (** [subset s1 s2] tests whether the set [s1] is a subset of
  the set [s2]. *)

  (** Coq comment: [iter] is useless in a purely functional world *)
  (**  iter: (elt -> unit) -> set -> unit. i*)
  (** [iter f s] applies [f] in turn to all elements of [s].
  The order in which the elements of [s] are presented to [f]
  is unspecified. *)

  Parameter fold : forall A : Set, (elt -> A -> A) -> t -> A -> A.
  (** [fold f s a] computes [(f xN ... (f x2 (f x1 a))...)],
  where [x1 ... xN] are the elements of [s].
  The order in which elements of [s] are presented to [f] is
  unspecified. *)

  Parameter for_all : (elt -> bool) -> t -> bool.
  (** [for_all p s] checks if all elements of the set
  satisfy the predicate [p]. *)

  Parameter exists_ : (elt -> bool) -> t -> bool.
  (** [exists p s] checks if at least one element of
  the set satisfies the predicate [p]. *)

  Parameter filter : (elt -> bool) -> t -> t.
  (** [filter p s] returns the set of all elements in [s]
  that satisfy predicate [p]. *)

  Parameter partition : (elt -> bool) -> t -> t * t.
  (** [partition p s] returns a pair of sets [(s1, s2)], where
  [s1] is the set of all the elements of [s] that satisfy the
  predicate [p], and [s2] is the set of all the elements of
  [s] that do not satisfy [p]. *)

  Parameter cardinal : t -> nat.
  (** Return the number of elements of a set. *)
  (** Coq comment: nat instead of int ... *)

  Parameter elements : t -> list elt.
  (** Return the list of all elements of the given set.
  The returned list is sorted in increasing order with respect
  to the ordering [Ord.compare], where [Ord] is the argument
  given to {!Set.Make}. *)

  Parameter min_elt : t -> option elt.
  (** Return the smallest element of the given set
  (with respect to the [Ord.compare] ordering), or raise
  [Not_found] if the set is empty. *)
  (** Coq comment: [Not_found] is represented by the option type *)

  Parameter max_elt : t -> option elt.
  (** Same as {!Set.S.min_elt}, but returns the largest element of the
  given set. *)
  (** Coq comment: [Not_found] is represented by the option type *)

  Parameter choose : t -> option elt.
  (** Return one element of the given set, or raise [Not_found] if
  the set is empty. Which element is chosen is unspecified,
  but equal elements will be chosen for equal sets. *)
  (** Coq comment: [Not_found] is represented by the option type *)

  Section Spec. 

  Variable s s' s'' : t.
  Variable x y z : elt.

  Parameter In : elt -> t -> Prop.
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Add (x : elt) (s s' : t) :=
    forall y : elt, In y s' <-> E.eq y x \/ In y s.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) (s : t) :=
    forall x : elt, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s : t) :=
    exists x : elt, In x s /\ P x.

  (** Specification of [In] *)
  Parameter In_1 : E.eq x y -> In x s -> In y s.

  (** Specification of [eq] *)
  Parameter eq_refl : eq s s. 
  Parameter eq_sym : eq s s' -> eq s' s.
  Parameter eq_trans : eq s s' -> eq s' s'' -> eq s s''.
 
  (** Specification of [lt] *)
  Parameter lt_trans : lt s s' -> lt s' s'' -> lt s s''.
  Parameter lt_not_eq : lt s s' -> ~ eq s s'.

  (** Specification of [mem] *)
  Parameter mem_1 : In x s -> mem x s = true.
  Parameter mem_2 : mem x s = true -> In x s. 
 
  (** Specification of [equal] *) 
  Parameter equal_1 : Equal s s' -> equal s s' = true.
  Parameter equal_2 : equal s s' = true -> Equal s s'.

  (** Specification of [subset] *)
  Parameter subset_1 : Subset s s' -> subset s s' = true.
  Parameter subset_2 : subset s s' = true -> Subset s s'.

  (** Specification of [empty] *)
  Parameter empty_1 : Empty empty.

  (** Specification of [is_empty] *)
  Parameter is_empty_1 : Empty s -> is_empty s = true. 
  Parameter is_empty_2 : is_empty s = true -> Empty s.
 
  (** Specification of [add] *)
  Parameter add_1 : E.eq y x -> In y (add x s).
  Parameter add_2 : In y s -> In y (add x s).
  Parameter add_3 : ~ E.eq x y -> In y (add x s) -> In y s. 

  (** Specification of [remove] *)
  Parameter remove_1 : E.eq y x -> ~ In y (remove x s).
  Parameter remove_2 : ~ E.eq x y -> In y s -> In y (remove x s).
  Parameter remove_3 : In y (remove x s) -> In y s.

  (** Specification of [singleton] *)
  Parameter singleton_1 : In y (singleton x) -> E.eq x y. 
  Parameter singleton_2 : E.eq x y -> In y (singleton x). 

  (** Specification of [union] *)
  Parameter union_1 : In x (union s s') -> In x s \/ In x s'.
  Parameter union_2 : In x s -> In x (union s s'). 
  Parameter union_3 : In x s' -> In x (union s s').

  (** Specification of [inter] *)
  Parameter inter_1 : In x (inter s s') -> In x s.
  Parameter inter_2 : In x (inter s s') -> In x s'.
  Parameter inter_3 : In x s -> In x s' -> In x (inter s s').

  (** Specification of [diff] *)
  Parameter diff_1 : In x (diff s s') -> In x s. 
  Parameter diff_2 : In x (diff s s') -> ~ In x s'.
  Parameter diff_3 : In x s -> ~ In x s' -> In x (diff s s').
 
  (** Specification of [fold] *)  
  Parameter
    fold_1 :
      forall (A : Set) (i : A) (f : elt -> A -> A),
      exists l : list elt,
        Unique E.eq l /\
        (forall x : elt, In x s <-> InList E.eq x l) /\
        fold f s i = fold_right f i l.

  (** Specification of [cardinal] *)  
  Parameter
    cardinal_1 :
      exists l : list elt,
        Unique E.eq l /\
        (forall x : elt, In x s <-> InList E.eq x l) /\ cardinal s = length l.

  Section Filter.
  
  Variable f : elt -> bool.

  (** Specification of [filter] *)
  Parameter filter_1 : compat_bool E.eq f -> In x (filter f s) -> In x s. 
  Parameter filter_2 : compat_bool E.eq f -> In x (filter f s) -> f x = true. 
  Parameter
    filter_3 :
      compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s).

  (** Specification of [for_all] *)
  Parameter
    for_all_1 :
      compat_bool E.eq f ->
      For_all (fun x => f x = true) s -> for_all f s = true.
  Parameter
    for_all_2 :
      compat_bool E.eq f ->
      for_all f s = true -> For_all (fun x => f x = true) s.

  (** Specification of [exists] *)
  Parameter
    exists_1 :
      compat_bool E.eq f ->
      Exists (fun x => f x = true) s -> exists_ f s = true.
  Parameter
    exists_2 :
      compat_bool E.eq f ->
      exists_ f s = true -> Exists (fun x => f x = true) s.

  (** Specification of [partition] *)
  Parameter
    partition_1 :
      compat_bool E.eq f -> Equal (fst (partition f s)) (filter f s).
  Parameter
    partition_2 :
      compat_bool E.eq f ->
      Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).

  (** Specification of [elements] *)
  Parameter elements_1 : In x s -> InList E.eq x (elements s).
  Parameter elements_2 : InList E.eq x (elements s) -> In x s.
  Parameter elements_3 : sort E.lt (elements s).  

  (** Specification of [min_elt] *)
  Parameter min_elt_1 : min_elt s = Some x -> In x s. 
  Parameter min_elt_2 : min_elt s = Some x -> In y s -> ~ E.lt y x. 
  Parameter min_elt_3 : min_elt s = None -> Empty s.

  (** Specification of [max_elt] *)  
  Parameter max_elt_1 : max_elt s = Some x -> In x s. 
  Parameter max_elt_2 : max_elt s = Some x -> In y s -> ~ E.lt x y. 
  Parameter max_elt_3 : max_elt s = None -> Empty s.

  (** Specification of [choose] *)
  Parameter choose_1 : choose s = Some x -> In x s.
  Parameter choose_2 : choose s = None -> Empty s.
  (*i Parameter choose_equal: 
      (equal s s')=true -> E.eq (choose s) (choose s'). i*)

  End Filter.
  End Spec.

  Notation "∅" := empty.
  Notation "a ⋃ b" := (union a b) (at level 20).
  Notation "a ⋂ b" := (inter a b) (at level 20). 
  Notation "∥ a ∥" := (cardinal a) (at level 20).
  Notation "a ∈ b" := (In a b) (at level 20).
  Notation "a ∉ b" := (~ a ∈ b) (at level 20).
  Notation "a ≡ b" := (Equal a b) (at level 20).
  Notation "a ≢ b" := (~ a ≡ b) (at level 20).
  Notation "a ⊆ b" := (Subset a b) (at level 20).
  Notation "a ⊈ b" := (~ a ⊆ b) (at level 20).  

  Hint Immediate In_1.
  
  Hint Resolve mem_1 mem_2 equal_1 equal_2 subset_1 subset_2 empty_1
    is_empty_1 is_empty_2 choose_1 choose_2 add_1 add_2 add_3 remove_1
    remove_2 remove_3 singleton_1 singleton_2 union_1 union_2 union_3 inter_1
    inter_2 inter_3 diff_1 diff_2 diff_3 filter_1 filter_2 filter_3 for_all_1
    for_all_2 exists_1 exists_2 partition_1 partition_2 elements_1 elements_2
    elements_3 min_elt_1 min_elt_2 min_elt_3 max_elt_1 max_elt_2 max_elt_3.

End S.

(** * Dependent signature 

    Signature [Sdep] presents sets using dependent types *)

Module Type Sdep.

  Declare Module E : OrderedType.
  Definition elt := E.t.

  Parameter t : Set.

  Parameter eq : t -> t -> Prop.
  Parameter lt : t -> t -> Prop.
  Parameter compare : forall s s' : t, Compare lt eq s s'.

  Parameter eq_refl : forall s : t, eq s s. 
  Parameter eq_sym : forall s s' : t, eq s s' -> eq s' s.
  Parameter eq_trans : forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
  Parameter lt_trans : forall s s' s'' : t, lt s s' -> lt s' s'' -> lt s s''.
  Parameter lt_not_eq : forall s s' : t, lt s s' -> ~ eq s s'.

  Parameter In : elt -> t -> Prop.
  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Add (x : elt) (s s' : t) :=
    forall y : elt, In y s' <-> E.eq y x \/ In y s.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) (s : t) :=
    forall x : elt, In x s -> P x.
  Definition Exists (P : elt -> Prop) (s : t) :=
    exists x : elt, In x s /\ P x.

  Parameter eq_In : forall (s : t) (x y : elt), E.eq x y -> In x s -> In y s.

  Parameter empty : {s : t | Empty s}.

  Parameter is_empty : forall s : t, {Empty s} + {~ Empty s}.

  Parameter mem : forall (x : elt) (s : t), {In x s} + {~ In x s}.

  Parameter add : forall (x : elt) (s : t), {s' : t | Add x s s'}.

  Parameter
    singleton : forall x : elt, {s : t | forall y : elt, In y s <-> E.eq x y}.
  
  Parameter
    remove :
      forall (x : elt) (s : t),
      {s' : t | forall y : elt, In y s' <-> ~ E.eq y x /\ In y s}.

  Parameter
    union :
      forall s s' : t,
      {s'' : t | forall x : elt, In x s'' <-> In x s \/ In x s'}.

  Parameter
    inter :
      forall s s' : t,
      {s'' : t | forall x : elt, In x s'' <-> In x s /\ In x s'}.

  Parameter
    diff :
      forall s s' : t,
      {s'' : t | forall x : elt, In x s'' <-> In x s /\ ~ In x s'}.

  Parameter equal : forall s s' : t, {Equal s s'} + {~ Equal s s'}.
 
  Parameter subset : forall s s' : t, {Subset s s'} + {~ Subset s s'}.

  Parameter
    fold :
      forall (A : Set) (f : elt -> A -> A) (s : t) (i : A),
      {r : A |
      exists l : list elt,
        Unique E.eq l /\
        (forall x : elt, In x s <-> InList E.eq x l) /\ r = fold_right f i l}.

  Parameter
    cardinal :
      forall s : t,
      {r : nat |
      exists l : list elt,
        Unique E.eq l /\
        (forall x : elt, In x s <-> InList E.eq x l) /\ r = length l}.

  Parameter
    filter :
      forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
        (s : t),
      {s' : t | compat_P E.eq P -> forall x : elt, In x s' <-> In x s /\ P x}.

  Parameter
    for_all :
      forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
        (s : t),
      {compat_P E.eq P -> For_all P s} + {compat_P E.eq P -> ~ For_all P s}.
  
  Parameter
    exists_ :
      forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
        (s : t),
      {compat_P E.eq P -> Exists P s} + {compat_P E.eq P -> ~ Exists P s}.

  Parameter
    partition :
      forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
        (s : t),
      {partition : t * t |
      let (s1, s2) := partition in
      compat_P E.eq P ->
      For_all P s1 /\
      For_all (fun x => ~ P x) s2 /\
      (forall x : elt, In x s <-> In x s1 \/ In x s2)}.

  Parameter
    elements :
      forall s : t,
      {l : list elt |
      sort E.lt l /\ (forall x : elt, In x s <-> InList E.eq x l)}.

  Parameter
    min_elt :
      forall s : t,
      {x : elt | In x s /\ For_all (fun y => ~ E.lt y x) s} + {Empty s}.

  Parameter
    max_elt :
      forall s : t,
      {x : elt | In x s /\ For_all (fun y => ~ E.lt x y) s} + {Empty s}.

  Parameter choose : forall s : t, {x : elt | In x s} + {Empty s}.

  Notation "∅" := empty.
  Notation "a ⋃ b" := (union a b) (at level 20).
  Notation "a ⋂ b" := (inter a b) (at level 20).
  Notation "a ∈ b" := (In a b) (at level 20).
  Notation "a ∉ b" := (~ a ∈ b) (at level 20).
  Notation "a ≡ b" := (Equal a b) (at level 20).
  Notation "a ≢ b" := (~ a ≡ b) (at level 20).
  Notation "a ⊆ b" := (Subset a b) (at level 20).
  Notation "a ⊈ b" := (~ a ⊆ b) (at level 20).  
	
End Sdep.

(** * Ordered types properties *)

(** Additional properties that can be derived from signature
    [OrderedType]. *)

Module OrderedTypeFacts (O: OrderedType). 

  Lemma gt_not_eq : forall x y : O.t, O.lt y x -> ~ O.eq x y.
  Proof.
   intros; intro; absurd (O.eq y x); auto.
  Qed.	
 
  Lemma eq_not_lt : forall x y : O.t, O.eq x y -> ~ O.lt x y.
  Proof. 
   intros; intro; absurd (O.eq x y); auto.
  Qed.

  Hint Resolve gt_not_eq eq_not_lt.

  Lemma eq_not_gt : forall x y : O.t, O.eq x y -> ~ O.lt y x.
  Proof. 
   auto. 
  Qed.
  
  Lemma lt_antirefl : forall x : O.t, ~ O.lt x x.
  Proof.
   intros; intro; absurd (O.eq x x); auto. 
  Qed.

  Lemma lt_not_gt : forall x y : O.t, O.lt x y -> ~ O.lt y x.
  Proof. 
   intros; intro; absurd (O.eq x x); eauto.
  Qed.

  Hint Resolve eq_not_gt lt_antirefl lt_not_gt.
 
  Lemma lt_eq : forall x y z : O.t, O.lt x y -> O.eq y z -> O.lt x z.
  Proof. 
   intros; case (O.compare x z); intros; auto.
   elimtype False.
   absurd (O.eq x y); eauto.
   absurd (O.eq z y); eauto. 
  Qed. 

  Lemma eq_lt : forall x y z : O.t, O.eq x y -> O.lt y z -> O.lt x z.    
  Proof.
   intros; case (O.compare x z); intros; auto.
   absurd (O.eq y z); eauto.
   absurd (O.eq x y); eauto. 
  Qed. 

  Hint Immediate eq_lt lt_eq.

  Lemma elim_compare_eq :
   forall x y : O.t,
   O.eq x y -> exists H : O.eq x y, O.compare x y = Eq _ H.
  Proof. 
   intros; case (O.compare x y); intros H'.
   absurd (O.eq x y); auto. 
   exists H'; auto.   
   absurd (O.eq x y); auto.
  Qed.

  Lemma elim_compare_lt :
   forall x y : O.t,
   O.lt x y -> exists H : O.lt x y, O.compare x y = Lt _ H.
  Proof. 
   intros; case (O.compare x y); intros H'.
   exists H'; auto.   
   absurd (O.eq x y); auto. 
   absurd (O.lt x x); eauto.
  Qed.

  Lemma elim_compare_gt :
   forall x y : O.t,
   O.lt y x -> exists H : O.lt y x, O.compare x y = Gt _ H.
  Proof. 
   intros; case (O.compare x y); intros H'.
   absurd (O.lt x x); eauto.
   absurd (O.eq x y); auto.
   exists H'; auto.   
  Qed.

  Ltac compare := 
    match goal with 
      | |- ?e => match e with 
           | context ctx [ O.compare ?a ?b ] =>
                let H := fresh in 
                (destruct (O.compare a b) as [H|H|H]; 
                 try solve [ intros; elimtype False; apply (absurd False H); eauto])
         end
    end.

  Ltac compare_eq x y :=
    elim (elim_compare_eq (x:=x) (y:=y));
     [ intros _1 _2; rewrite _2; clear _1 _2 | auto ]. 

  Ltac compare_lt x y :=
    elim (elim_compare_lt (x:=x) (y:=y));
     [ intros _1 _2; rewrite _2; clear _1 _2 | auto ]. 

  Ltac compare_gt x y :=
    elim (elim_compare_gt (x:=x) (y:=y));
     [ intros _1 _2; rewrite _2; clear _1 _2 | auto ].

  Lemma eq_dec : forall x y : O.t, {O.eq x y} + {~ O.eq x y}.
  Proof.
   intros; elim (O.compare x y); [ right | left | right ]; auto.
  Qed.
 
  Lemma lt_dec : forall x y : O.t, {O.lt x y} + {~ O.lt x y}.
  Proof.
   intros; elim (O.compare x y); [ left | right | right ]; auto.
  Qed.

  (** Results concerning lists modulo E.eq *)

  Notation Sort := (sort O.lt).
  Notation Inf := (lelistA O.lt).
  Notation In := (InList O.eq).

  Lemma In_eq :
   forall (s : list O.t) (x y : O.t), O.eq x y -> In x s -> In y s.
  Proof. 
   intros s x y.
   do 2 (setoid_rewrite InList_alt).
   firstorder eauto.
  Qed.
  Hint Immediate In_eq.

  Lemma Inf_lt :
   forall (s : list O.t) (x y : O.t), O.lt x y -> Inf y s -> Inf x s.
  Proof.
  intro s; case s; constructor; inversion H0; eauto.
  Qed.
 
  Lemma Inf_eq :
   forall (s : list O.t) (x y : O.t), O.eq x y -> Inf y s -> Inf x s.
  Proof.
  intro s; case s; constructor; inversion H0; eapply eq_lt; eauto.
  Qed.
  Hint Resolve Inf_lt Inf_eq. 

  Lemma In_sort :
   forall (s : list O.t) (x a : O.t), Inf a s -> In x s -> Sort s -> O.lt a x.
  Proof. 
  simple induction s.
  intros; inversion H0.
  intros.
  inversion_clear H0; inversion_clear H2; inversion_clear H1.
  eapply lt_eq; eauto.
  eauto.
  Qed.
  
  Lemma Inf_In :
   forall (l : list O.t) (x : O.t),
   (forall y : O.t, List.In y l -> O.lt x y) -> Inf x l.
  Proof.
    simple induction l; simpl in |- *; intros; constructor; auto.
  Qed.
 
  Lemma Inf_In_2 :
   forall (l : list O.t) (x : O.t),
   (forall y : O.t, In y l -> O.lt x y) -> Inf x l.
  Proof.
    simple induction l; simpl in |- *; intros; constructor; auto.
  Qed.
  
  Lemma In_InList : forall (l : list O.t) (x : O.t), List.In x l -> In x l.
  Proof.
   simple induction l; simpl in |- *; intuition.
    subst; auto.  
  Qed.
  Hint Resolve In_InList.

  Lemma Sort_Unique : forall l : list O.t, Sort l -> Unique O.eq l.
  Proof.
  simple induction l; auto.
  intros x l' H H0.
  inversion_clear H0.
  constructor; auto.  
  intro.
  absurd (O.lt x x); auto.
  eapply In_sort; eauto.
  Qed.

End OrderedTypeFacts.
