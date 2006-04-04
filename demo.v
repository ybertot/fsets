Require Import FSetInterface.
Require Import FSetAVL.
Require Import FSetAVL_int.
Require Import SomeOrderedType.
Require Import ZArith.
Require Import Omega.
Open Scope Z_scope.
Set Implicit Arguments.

(** * Ordered types *)

(* starting point: the OrderedType interface of Ocaml: 

module type OrderedType =
  sig
    type t
    val compare : t -> t -> int
  end
*)


(*excerpt from OrderedType.v *)                                                                                                                                                            Module Demo1.
Inductive Compare (X : Set) (lt eq : X -> X -> Prop) (x y : X) : Set :=
  | LT : lt x y -> Compare lt eq x y
  | EQ : eq x y -> Compare lt eq x y
  | GT : lt y x -> Compare lt eq x y.

Extraction Compare.

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

End OrderedType.
(*/excerpt*)                                                                                                                                                            End Demo1.




(** * [Z] integers seen as orderered types *)

(* excerpt from SomeOrderedType.v *)                                                                                                                 Module Demo2.
Module Z_as_OT <: OrderedType.

  Definition t := Z.
  Definition eq (x y:Z) := (x=y).
  Definition lt (x y:Z) := (x<y).

  Section xyz.
  Variables x y z : Z.

  Lemma eq_refl : x=x .  
  Proof. auto. Qed.

  Lemma eq_sym : x=y -> y=x.
  Proof. auto. Qed.

  Lemma eq_trans : x=y -> y=z -> x=z.
  Proof. auto with zarith. Qed.

  Lemma lt_trans : x<y -> y<z -> x<z.
  Proof. auto with zarith. Qed.

  Lemma lt_not_eq : x<y -> ~ x=y.
  Proof. auto with zarith. Qed.

  Definition compare : Compare lt eq x y.
  Proof.
    case_eq (x ?= y); intros.
    apply EQ; unfold eq; apply Zcompare_Eq_eq; auto.
    apply LT; unfold lt, Zlt; auto.
    apply GT; unfold lt, Zlt; rewrite <- Zcompare_Gt_Lt_antisym; auto.
  Defined.

  End xyz.
End Z_as_OT.
(* /excerpt *)                                                                                                                                                                            End Demo2.

Extraction Z_as_OT.





(** * Let's build some sets of [Z] integers ... *)

Module M := FSetAVL.Make(Z_as_OT).

Print M.

Definition ens1 := M.add 3 (M.add 0 (M.add 2 (M.empty))).
Definition ens2 := M.add 0 (M.add 2 (M.add 4 (M.empty))).
Definition ens3 := M.inter ens1 ens2.

Eval compute in (M.mem 2 ens3).
Eval compute in (M.elements ens3).

Check (M.elements_3 ens3).
Eval red in M.Raw.E.lt.

Import M.Raw.
Eval compute in ens1.
Eval compute in ens3.

(* In order to avoid the continuous expansion of proofs parts, we can work on 
    "pure" or "raw" datatypes (i.e. without built-in invariants). *)

Module R:=M.Raw.

Definition raw1 := R.add 3 (R.add 0 (R.add 2 R.empty)).
Definition raw2 := R.add 0 (R.add 2 (R.add 4 R.empty)).
Definition raw3 := R.inter raw1 raw2.
Eval compute in raw3.
Eval compute in (R.elements raw3).

(* ... but then there is more work for deriving properties. *)

Hint Resolve inter_bst add_bst. 
Lemma raw1_avl : avl raw1. Proof. unfold raw1; auto. Qed. 
Lemma raw1_bst : bst raw1. Proof. unfold raw1; auto. Qed.
Lemma raw2_avl : avl raw2. Proof. unfold raw2; auto. Qed. 
Lemma raw2_bst : bst raw2. Proof. unfold raw2; auto. Qed.
Hint Resolve raw1_bst raw1_avl raw2_bst raw2_avl.
Lemma raw3_bst : bst raw3. Proof. unfold raw3; auto. Qed.

Check (elements_sort raw3 raw3_bst).




(** * union *) 

(* This function isn't based on a structural recursion, but rather on 
   a well-founded one. Hence it cannot compute in Coq. *)
Eval compute in (R.union raw1 raw2).

(* A naive additional version [union' = fold@add] that can compute. *)
Eval compute in (R.union' raw1 raw2).
Eval compute in (R.elements (R.union' raw1 raw2)).

(* Of course, you'd better use [union] after extraction... *)

Extraction M.





(** * Some sets of sets ... *)

Module MM := FSetAVL.Make(M).

Definition eens1 := MM.add ens1 (MM.add ens2 (MM.empty)).

(* ... that cannot be computed in Coq (due to [compare]) *)
Eval compute in (MM.elements eens1).






(** Some more intense tests. *)

Fixpoint multiples (m:Z)(start:Z)(n:nat) {struct n} : list Z := 
  match n with 
   | O => nil
   | S n => start::(multiples m (m+start) n)
  end.

Eval compute in (multiples 2 0 200%nat).

Definition bigens1 := fold_right M.add M.empty (multiples 2 0 400%nat).
Definition bigens2 := fold_right M.add M.empty (multiples 3 0 400%nat).
Time Eval compute in (M.elements (M.inter bigens1 bigens2)).
(* takes a few seconds, but we can also take advantage of Coq new virtual 
    machine (VM), that performs the same job in almost no time. *) 
Time Eval vm_compute in (M.elements (M.inter bigens1 bigens2)).

(*
Definition bigens3 := fold_right M.add M.empty (multiples 2 0 10000%nat).
Definition bigens4 := fold_right M.add M.empty (multiples 3 0 10000%nat).
Time Eval vm_compute in (M.elements (M.inter bigens3 bigens4)).
(* 11s for this intersection of 2 sets of 10000 elements !! *)
*)


(* You can also use "pure" sets. *)

(*
Definition bigraw1 := fold_right R.add R.empty (multiples 2 0 10000%nat).
Definition bigraw2 := fold_right R.add R.empty (multiples 3 0 10000%nat).
Time Eval vm_compute in (length (R.elements (R.inter bigraw1 bigraw2))).
(* 11s for computing the result 3334 *)
*)




(** * What about maps ? it's the same ! *)

Require Import FMapAVL.

Module F := FMapAVL.Make(Z_as_OT).

(* As in Ocaml, everything is polymorphic with respect to the datas. *)

Check F.add.

Definition map1 := 
  F.add 2 (1::2::nil) 
   (F.add 3 nil 
     (F.add 1 (0::nil) 
       (F.empty _))).

Eval compute in (F.find 1 map1).
Eval compute in (F.mem 1 map1).

Eval compute in ((F.map (@length _) map1).(F.this)).

(* Not in Ocaml's map: [elements] *)

Eval compute in (F.elements (F.map (@length _) map1)).

(* ... and [map2] *)

Check F.map2.

(* Unlike keys, we need no particular structure over datas.
    Only two exceptions: [equal] and [compare]. *)

Check F.equal.

(* Concerning [compare], we need a ternary decidable comparison  
 over datas. We hence diverge slightly apart from Ocaml, by placing 
 this [compare] in a separate functor requiring 2 [OrderedType], 
 one for the keys and one for the datas. *)








(** How to get more efficient AVL trees after extraction : 
     the [Int] module to get rid of [Z] not-so-fast integers. *)

Print R.tree.
Eval compute in (Zpos (xO (xI xH))).

(*excerpt from Int.v*)                                                                                                                                                     Module Demo3.
Module Type Int.

 Parameter int : Set. 

 Parameter i2z : int -> Z.
 Parameter z2i : Z -> int. 

 Parameter _0 : int. 
 Parameter _1 : int. 
 Parameter plus : int -> int -> int. 
 Parameter opp : int -> int.
 Parameter minus : int -> int -> int. 
 Parameter mult : int -> int -> int.
 Parameter max : int -> int -> int. 

(* Concerning logical relations, there is no need for additional 
   parameters: we take directly advantage of the [Z] ones, via 
   [i2z]. This simplifies the writing of translation tactics from  
   [int] to [Z].  *)

 Notation "x == y" := (i2z x = i2z y)
   (at level 70, y at next level, no associativity) : Int_scope.
 Notation "x <= y" := (Zle (i2z x) (i2z y)): Int_scope.
 Notation "x < y" := (Zlt (i2z x) (i2z y)) : Int_scope.
 Notation "x >= y" := (Zge (i2z x) (i2z y)) : Int_scope.
 Notation "x > y" := (Zgt (i2z x) (i2z y)): Int_scope.

 (* We also need some decidability facts. *) 

 Open Scope Int_scope.
 Parameter gt_le_dec : forall x y: int, {x > y} + {x <= y}.
 Parameter ge_lt_dec :  forall x y : int, {x >= y} + {x < y}.
 Parameter eq_dec : forall x y : int, { x == y } + {~ x==y }.
 Open Scope Z_scope.

 (* Specification of [int] parameters. *)

 (* First, [int] and [Z] are isomorphic. *)

 Axiom z2i2z : forall z, i2z (z2i z) = z.
 Axiom i2z2i : forall i,  z2i (i2z i) = i.

 (* Then, all the operators are morphisms. *)

 Axiom i2z_0 : i2z _0 = 0.
 Axiom i2z_1 : i2z _1 = 1.
 Axiom i2z_plus : forall n p, i2z (plus n p) = i2z n + i2z p.
 Axiom i2z_opp : forall n, i2z (opp n) = -i2z n.
 Axiom i2z_minus : forall n p, i2z (minus n p) = i2z n - i2z p.
 Axiom i2z_mult : forall n p, i2z (mult n p) = i2z n * i2z p.
 Axiom i2z_max : forall n p, i2z (max n p) = Zmax (i2z n) (i2z p).

End Int. 
(*/excerpt*)                                                                                                                                                              End Demo3.

(* [FSetAVL_int] is then a clone of [FSetAVL] where a 
   module [Int] is used instead of [Z] for every height.
   Similarly from Map. *)

Module MI := FSetAVL_int.Make(Int.Z_as_Int)(Z_as_OT).

Eval compute in 
 (MI.elements 
   (MI.union'  
     (MI.add 3 (MI.add 0 (MI.empty))) 
     (MI.add 1 (MI.add 2 (MI.empty))))).

Extraction MI.
(* We can then easily write a module [Int] in Ocaml
    based on Bigint or native int. *)

