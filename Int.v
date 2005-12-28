
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

(** An axiomatization of integers. *) 

(* We define a signature for an integer datatype based on [Z]. 
   The goal is to allow a switch after extraction to ocaml's 
   [big_int] or even [int] when finiteness isn't a problem 
   (typically : when mesuring the height of an AVL tree). 
*)

Require Import ZArith. 

Module Type Int.

 Delimit Scope Int_scope with I.
 Open Scope Int_scope.

 Parameter int : Set. 

 Parameter i2z : int -> Z.
 Parameter z2i : Z -> int. 
 Arguments Scope i2z [ Int_scope ].
 Arguments Scope z2i [ Z_scope ].
 Notation "[[ n ]]" := (z2i n).  
 Notation "{{ n }}" := (i2z n).

 Parameter _0 : int. 
 Parameter _1 : int. 
 Parameter _2 : int. 
 Parameter _3 : int.
 Parameter plus : int -> int -> int. 
 Parameter opp : int -> int.
 Parameter minus : int -> int -> int. 
 Parameter mult : int -> int -> int.
 Parameter max : int -> int -> int. 

 Infix "+" := plus : Int_scope.
 Infix "-" := minus : Int_scope.
 Infix "*" := mult : Int_scope.
 Notation "- x" := (opp x) : Int_scope.

(* For logical relations, we can rely on their counterparts in Z, 
   since they don't appear after extraction. Moreover, using tactics 
   like omega is easier this way. *)

 Notation "x == y" := ({{x}} = {{y}})%Z 
   (at level 70, y at next level, no associativity) : Int_scope.
 Notation "x <= y" := ({{x}} <= {{y}})%Z : Int_scope.
 Notation "x < y" := ({{x}} < {{y}})%Z : Int_scope.
 Notation "x >= y" := ({{x}} >= {{y}})%Z : Int_scope.
 Notation "x > y" := ({{x}} > {{y}})%Z: Int_scope.
 Notation "x <= y <= z" := (x <= y /\ y <= z) : Int_scope.
 Notation "x <= y < z" := (x <= y /\ y < z) : Int_scope.
 Notation "x < y < z" := (x < y /\ y < z) : Int_scope.
 Notation "x < y <= z" := (x < y /\ y <= z) : Int_scope.

 (* Some decidability fonctions (informative). *)

 Axiom gt_le_dec : forall x y: int, {x > y} + {x <= y}.
 Axiom ge_lt_dec :  forall x y : int, {x >= y} + {x < y}.
 Axiom eq_dec : forall x y : int, { x == y } + {~ x==y }.

 (** Specifications *)

 (* First, we have a bijection between [int] and [Z]. *) 

 Axiom z2i2z : forall z, {{ [[z]] }} = z.
 Axiom i2z2i : forall i, [[ {{ i }} ]] = i.
 Arguments Scope i2z2i [ Int_scope ].
 Arguments Scope z2i2z [ Z_scope ].

 (* Then, we express the specifications of the above parameters using their 
    Z counterparts. *)

 Open Scope Z_scope.
 Axiom i2z_0 : {{ _0 }} = 0.
 Axiom i2z_1 : {{ _1 }} = 1.
 Axiom i2z_2 : {{ _2 }} = 2.
 Axiom i2z_3 : {{ _3 }} = 3.
 Axiom i2z_plus : forall n p, {{ n + p }} = {{n}}+{{p}}.
 Axiom i2z_opp : forall n, {{-n}} = -{{n}}.
 Axiom i2z_minus : forall n p, {{ n - p }} = {{n}}-{{p}}.
 Axiom i2z_mult : forall n p, {{ n * p }} = {{n}}*{{p}}.
 Axiom i2z_max : forall n p, {{ max n p }} = Zmax {{n}} {{p}}.

 (* Our ad-hoc equality [==] and the generic [=] are in fact equivalent. 
    We define [==] nonetheless since the translation to [Z] for using 
    automatic tactic is easier. 

    This equivalence property is a consequence of [i2z2i]. We state it 
    explicitely since it is needed for the following tactic. 
    By the way: too bad there isn't any proof editing mode in interfaces... 
 *)

(*
 Lemma i2z_eq (n p :int) : n == p -> n = p.
 Proof. 
 intro H ; rewrite <- (i2z2i n); rewrite H; apply i2z2i. 
 Qed.
*)
 
 Definition i2z_eq (n p : int) :  n == p -> n = p := 
   fun H => eq_ind [[{{n}}]] (fun q => q = p)
                   (eq_ind_r (fun z => [[z]] = p) (i2z2i p) H) n (i2z2i n).
 Opaque i2z_eq.

 (** A magic (but costly) tactic that goes from [int] back to the [Z] 
     friendly world ... *)

 Hint Rewrite -> 
   i2z_0 i2z_1 i2z_2 i2z_3 i2z_plus i2z_opp i2z_minus i2z_mult i2z_max 
   i2z2i z2i2z : i2z.

 Ltac i2z := match goal with 
  | H : (eq (A:=int) ?a ?b) |- _ => 
       generalize (f_equal i2z H); 
       try autorewrite with i2z; clear H; intro H; i2z
  | |- (eq (A:=int) ?a ?b) => apply (i2z_eq a b); try autorewrite with i2z; i2z
  | H : _ |- _ => progress autorewrite with i2z in H; i2z
  | _ => try autorewrite with i2z
 end.

 Ltac iauto := i2z; auto with zarith.
 Ltac iomega := i2z; omega.

End Int. 

Module MoreInt (I:Int).
 Import I.
 Open Scope Int_scope.

 (** additional (provable) properties on [int]. For now we only need a 
      alternative definition of [max] more suitable for proving. *)     

 Definition max_if (x y:int) : int := if ge_lt_dec x y then x else y.

 Lemma max_equiv : forall x y, max x y = max_if x y.
   intros; unfold max_if.
   destruct (ge_lt_dec x y) as [H|H]; i2z.
   unfold Zmax; unfold Zge in *.
   destruct ({{x}} ?= {{y}}); auto with zarith.
   destruct H; auto.
   unfold Zmax; rewrite H; auto.
 Qed.

  Ltac MaxCase x y :=
    repeat rewrite max_equiv; unfold max_if in |- *; 
    case (ge_lt_dec x y); simpl in |- *. 

End MoreInt.


(** Even if it's useless, it's always nice to know that our [Int] 
     interface is realizable :-) *)

Module Z_as_Int <: Int.
 Open Scope Z_scope.
 Definition int := Z.
 Definition _0 := 0.
 Definition _1 := 1.
 Definition _2 := 2.
 Definition _3 := 3.
 Definition plus := Zplus.
 Definition opp := Zopp.
 Definition minus := Zminus.
 Definition mult := Zmult.
 Definition max := Zmax.
 Definition gt_le_dec := Z_gt_le_dec. 
 Definition ge_lt_dec := Z_ge_lt_dec.
 Definition eq_dec := Z_eq_dec.
 Definition i2z : int -> Z := fun n => n.
 Definition z2i : Z -> int := fun n => n.
 Notation "[[ n ]]" := (z2i n).  
 Notation "{{ n }}" := (i2z n).
 Lemma z2i2z : forall z, {{ [[z]] }} = z.  Proof. auto. Qed.
 Lemma i2z2i : forall i, [[ {{ i }} ]] = i.  Proof. auto. Qed.
 Lemma i2z_0 : {{ _0 }} = 0.  Proof. auto. Qed.
 Lemma i2z_1 : {{ _1 }} = 1.  Proof. auto. Qed.
 Lemma i2z_2 : {{ _2 }} = 2.  Proof. auto. Qed.
 Lemma i2z_3 : {{ _3 }} = 3.  Proof. auto. Qed.
 Lemma i2z_plus : forall n p, {{ n + p }} = {{n}}+{{p}}.  Proof. auto. Qed.
 Lemma i2z_opp : forall n, {{ - n }} = - {{n}}.  Proof. auto. Qed.
 Lemma i2z_minus : forall n p, {{ n - p }} = {{n}}-{{p}}.  Proof. auto. Qed.
 Lemma i2z_mult : forall n p, {{ n * p }} = {{n}}*{{p}}.  Proof. auto. Qed.
 Lemma i2z_max : forall n p, {{max n p}} = Zmax {{n}} {{p}}. Proof. auto. Qed.
 Definition i2z_eq (n p : int) :  {{n}} = {{p}} -> n = p := 
   fun H => eq_ind [[{{n}}]] (fun q => q = p)
                   (eq_ind_r (fun z => [[z]] = p) (i2z2i p) H) n (i2z2i n).

End Z_as_Int.

