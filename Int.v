
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
Require Import ROmega. 

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


 Notation "0" := _0 : Int_scope.
 Notation "1" := _1 : Int_scope. 
 Notation "2" := _2 : Int_scope. 
 Notation "3" := _3 : Int_scope.
 Infix "+" := plus : Int_scope.
 Infix "-" := minus : Int_scope.
 Infix "*" := mult : Int_scope.
 Notation "- x" := (opp x) : Int_scope.

(* For logical relations, we can rely on their counterparts in Z, 
   since they don't appear after extraction. Moreover, using tactics 
   like omega is easier this way. *)

 Notation "x == y" := ({{x}} = {{y}})
   (at level 70, y at next level, no associativity) : Int_scope.
 Notation "x <= y" := (Zle {{x}} {{y}}) : Int_scope.
 Notation "x < y" := (Zlt {{x}} {{y}}) : Int_scope.
 Notation "x >= y" := (Zge {{x}} {{y}}) : Int_scope.
 Notation "x > y" := (Zgt {{x}} {{y}}): Int_scope.
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
(*
 Ltac iauto := i2z; auto with zarith.
 Ltac iomega := i2z; omega.
*)
End Int. 

Module MoreInt (I:Int).
 Import I.
  
  (* a reflexive version of the [i2z] tactic *)

  Ltac i2z_gen := match goal with 
    | |- (eq (A:=int) ?a ?b) => apply (i2z_eq a b); i2z_gen
    | H : (eq (A:=int) ?a ?b) |- _ => 
       generalize (f_equal i2z H); clear H; i2z_gen
    | H : (eq (A:=Z) ?a ?b) |- _ => generalize H; clear H; i2z_gen
    | H : (Zlt ?a ?b) |- _ => generalize H; clear H; i2z_gen
    | H : (Zle ?a ?b) |- _ => generalize H; clear H; i2z_gen
    | H : (Zgt ?a ?b) |- _ => generalize H; clear H; i2z_gen
    | H : (Zge ?a ?b) |- _ => generalize H; clear H; i2z_gen
    | H : _ -> ?X |- _ => match type of X with 
       | Type => clear H; i2z_gen
       | Prop => generalize H; clear H; i2z_gen
      end
    | H : _ <-> _ |- _ => generalize H; clear H; i2z_gen
    | H : _ /\ _ |- _ => generalize H; clear H; i2z_gen
    | H : _ \/ _ |- _ => generalize H; clear H; i2z_gen
    | H : ~ _ |- _ => generalize H; clear H; i2z_gen
    | _ => idtac
   end.

  Inductive ExprI : Set := 
   | EI0 : ExprI
   | EI1 : ExprI
   | EI2 : ExprI 
   | EI3 : ExprI
   | EIplus : ExprI -> ExprI -> ExprI
   | EIopp : ExprI -> ExprI
   | EIminus : ExprI -> ExprI -> ExprI
   | EImult : ExprI -> ExprI -> ExprI
   | EImax : ExprI -> ExprI -> ExprI
   | EIofZ : ExprZ -> ExprI
   | EIraw : int -> ExprI
  with 
  ExprZ : Set := 
   | EZplus : ExprZ -> ExprZ -> ExprZ
   | EZopp : ExprZ -> ExprZ
   | EZminus : ExprZ -> ExprZ -> ExprZ
   | EZmult : ExprZ -> ExprZ -> ExprZ
   | EZmax : ExprZ -> ExprZ -> ExprZ
   | EZofI : ExprI -> ExprZ
   | EZraw : Z -> ExprZ.

  Inductive ExprP : Type := 
   | EPeq : ExprZ -> ExprZ -> ExprP 
   | EPlt : ExprZ -> ExprZ -> ExprP 
   | EPle : ExprZ -> ExprZ -> ExprP 
   | EPgt : ExprZ -> ExprZ -> ExprP 
   | EPge : ExprZ -> ExprZ -> ExprP 
   | EPimpl : ExprP -> ExprP -> ExprP
   | EPequiv : ExprP -> ExprP -> ExprP
   | EPand : ExprP -> ExprP -> ExprP
   | EPor : ExprP -> ExprP -> ExprP
   | EPneg : ExprP -> ExprP
   | EPraw : Prop -> ExprP.

Ltac interp_int trm := 
 match constr:trm with 
    | (plus ?X1 ?X2) => 
        let e1 := interp_int X1 with e2 := interp_int X2 
        in constr:(EIplus e1 e2)
    | (minus ?X1 ?X2) => 
       let e1 := interp_int X1 with e2 := interp_int X2 
        in constr:(EIminus e1 e2)
    | (mult ?X1 ?X2) => 
       let e1 := interp_int X1 with e2 := interp_int X2 
        in constr:(EImult e1 e2)
    | (max ?X1 ?X2) => 
       let e1 := interp_int X1 with e2 := interp_int X2 
        in constr:(EImax e1 e2)
    | (opp ?X1) => 
        let e1 := interp_int X1 in constr:(EIopp e1)
    | (_0) => constr:EI0
    | (_1) => constr:EI1
    | (_2) => constr:EI2
    | (_3) => constr:EI3
    | (z2i ?X1) => 
        let e1 := interp_z X1 in constr:(EIofZ e1)
    | ?X1 => constr:(EIraw X1)
   end
with interp_z trm := 
   match constr:trm with 
    | (Zplus ?X1 ?X2) => 
        let e1 := interp_z X1 with e2 := interp_z X2 
        in constr:(EZplus e1 e2)
    | (Zminus ?X1 ?X2) => 
        let e1 := interp_z X1 with e2 := interp_z X2 
        in constr:(EZminus e1 e2)
    | (Zmult ?X1 ?X2) => 
        let e1 := interp_z X1 with e2 := interp_z X2 
        in constr:(EZmult e1 e2)
    | (Zmax ?X1 ?X2) => 
        let e1 := interp_z X1 with e2 := interp_z X2 
        in constr:(EZmax e1 e2)
    | (Zopp ?X1) => 
        let e1 := interp_z X1 in constr:(EZopp e1)
    | (i2z ?X1) => 
        let e1 := interp_int X1 in constr:(EZofI e1)
    | ?X1 => constr:(EZraw X1)
   end.

Ltac interp_prop trm :=
  match constr:trm with
    | (?X1 <-> ?X2) => 
        let e1 := interp_prop X1 with e2 := interp_prop X2 
        in constr:(EPequiv e1 e2)
    | (?X1 -> ?X2) => 
        let e1 := interp_prop X1 with e2 := interp_prop X2 
        in constr:(EPimpl e1 e2)
    | (?X1 /\ ?X2) => 
        let e1 := interp_prop X1 with e2 := interp_prop X2 
        in constr:(EPand e1 e2)
    | (?X1 \/ ?X2) => 
        let e1 := interp_prop X1 with e2 := interp_prop X2 
        in constr:(EPor e1 e2)
    | (~ ?X1) =>
        let e1 := interp_prop X1 in constr:(EPneg e1)
    | (eq (A:=Z) ?X1 ?X2) => 
        let e1 := interp_z X1 with e2 := interp_z X2 
        in constr:(EPeq e1 e2)
    | (Zlt ?X1 ?X2) =>
        let e1 := interp_z X1 with e2 := interp_z X2 
        in constr:(EPlt e1 e2)
    | (Zle ?X1 ?X2) =>
        let e1 := interp_z X1 with e2 := interp_z X2 
        in constr:(EPle e1 e2)   
    | (Zgt ?X1 ?X2) =>
        let e1 := interp_z X1 with e2 := interp_z X2 
        in constr:(EPgt e1 e2)   
    | (Zge ?X1 ?X2) =>
        let e1 := interp_z X1 with e2 := interp_z X2 
        in constr:(EPge e1 e2)
    | ?X1 =>  constr:(EPraw X1)
   end.   

Fixpoint interp_ExprI (e:ExprI) : int :=
  match e with
  | EI0 => _0
  | EI1 => _1
  | EI2 => _2
  | EI3 => _3 
  | EIplus e1 e2 => plus (interp_ExprI e1) (interp_ExprI e2)
  | EIminus e1 e2 => minus (interp_ExprI e1) (interp_ExprI e2)
  | EImult e1 e2 => mult (interp_ExprI e1) (interp_ExprI e2)
  | EImax e1 e2 => max (interp_ExprI e1) (interp_ExprI e2)
  | EIopp e1 => opp (interp_ExprI e1)
  | EIofZ e1 => z2i (interp_ExprZ e1)
  | EIraw i => i 
  end 
with interp_ExprZ (e:ExprZ) : Z := 
 match e with 
  | EZraw z => z
  | EZplus e1 e2 => Zplus (interp_ExprZ e1) (interp_ExprZ e2)
  | EZminus e1 e2 => Zminus (interp_ExprZ e1) (interp_ExprZ e2)
  | EZmult e1 e2 => Zmult (interp_ExprZ e1) (interp_ExprZ e2)
  | EZmax e1 e2 => Zmax (interp_ExprZ e1) (interp_ExprZ e2)
  | EZopp e1 => Zopp (interp_ExprZ e1)
  | EZofI e1 => i2z (interp_ExprI e1)
  end.

Fixpoint interp_ExprP (e:ExprP) : Prop := 
 match e with 
   | EPeq e1 e2 => (interp_ExprZ e1) = (interp_ExprZ e2)
   | EPlt e1 e2 => Zlt (interp_ExprZ e1) (interp_ExprZ e2)
   | EPle e1 e2 => Zle (interp_ExprZ e1) (interp_ExprZ e2)
   | EPgt e1 e2 => Zgt (interp_ExprZ e1) (interp_ExprZ e2)
   | EPge e1 e2 => Zge (interp_ExprZ e1) (interp_ExprZ e2)
   | EPimpl e1 e2 => (interp_ExprP e1) -> (interp_ExprP e2)
   | EPequiv e1 e2 => (interp_ExprP e1) <-> (interp_ExprP e2)
   | EPand e1 e2 => (interp_ExprP e1) /\ (interp_ExprP e2)
   | EPor e1 e2 => (interp_ExprP e1) \/ (interp_ExprP e2)
   | EPneg e1 => ~ (interp_ExprP e1)
   | EPraw p => p
 end.

Fixpoint norm_ExprZ (e:ExprZ) : ExprZ := 
 match e with 
  | EZraw z => EZraw z
  | EZplus e1 e2 => EZplus (norm_ExprZ e1) (norm_ExprZ e2)
  | EZminus e1 e2 => EZminus (norm_ExprZ e1) (norm_ExprZ e2)
  | EZmult e1 e2 => EZmult (norm_ExprZ e1) (norm_ExprZ e2)
  | EZmax e1 e2 => EZmax (norm_ExprZ e1) (norm_ExprZ e2)
  | EZopp e1 => EZopp (norm_ExprZ e1)
  | EZofI e1 =>  norm_ExprI_i2z e1
 end
with norm_ExprI_i2z (e:ExprI) : ExprZ := 
 match e with 
  | EI0 => EZraw (0%Z)
  | EI1 => EZraw (1%Z)
  | EI2 => EZraw (2%Z)
  | EI3 => EZraw (3%Z) 
  | EIplus e1 e2 => EZplus (norm_ExprI_i2z e1) (norm_ExprI_i2z e2)
  | EIminus e1 e2 => EZminus (norm_ExprI_i2z e1) (norm_ExprI_i2z e2)
  | EImult e1 e2 => EZmult (norm_ExprI_i2z e1) (norm_ExprI_i2z e2)
  | EImax e1 e2 => EZmax (norm_ExprI_i2z e1) (norm_ExprI_i2z e2)
  | EIopp e1 => EZopp (norm_ExprI_i2z e1)
  | EIofZ e1 => norm_ExprZ e1
  | EIraw i => EZofI (EIraw i) 
 end.

Fixpoint norm_ExprP (e:ExprP) : ExprP := 
  match e with 
   | EPeq e1 e2 => EPeq (norm_ExprZ e1) (norm_ExprZ e2)
   | EPlt e1 e2 => EPlt (norm_ExprZ e1) (norm_ExprZ e2)
   | EPle e1 e2 => EPle (norm_ExprZ e1) (norm_ExprZ e2)
   | EPgt e1 e2 => EPgt (norm_ExprZ e1) (norm_ExprZ e2)
   | EPge e1 e2 => EPge (norm_ExprZ e1) (norm_ExprZ e2)
   | EPimpl e1 e2 => EPimpl (norm_ExprP e1) (norm_ExprP e2)
   | EPequiv e1 e2 => EPequiv (norm_ExprP e1) (norm_ExprP e2)
   | EPand e1 e2 => EPand (norm_ExprP e1) (norm_ExprP e2)
   | EPor e1 e2 => EPor (norm_ExprP e1) (norm_ExprP e2)
   | EPneg e1 => EPneg (norm_ExprP e1)
   | EPraw p => EPraw p
 end.

Scheme ExprZ_mrec := Induction for ExprZ Sort Prop
with ExprI_mrec := Induction for ExprI Sort Prop.

Lemma norm_ExprIZ_correct : 
  forall e:ExprZ, interp_ExprZ (norm_ExprZ e) = interp_ExprZ e.
Proof.
  set (P:= fun e => interp_ExprZ (norm_ExprZ e) = interp_ExprZ e).
  set (Q:= fun e => interp_ExprZ (norm_ExprI_i2z e) = i2z (interp_ExprI e)).
  apply (ExprZ_mrec P Q); unfold P, Q; simpl; intros; i2z; auto; try congruence.
Qed. 

Lemma norm_ExprP_correct : 
  forall e:ExprP, interp_ExprP (norm_ExprP e) <-> interp_ExprP e.
Proof.
induction e; simpl; repeat (rewrite norm_ExprIZ_correct); intuition.
Qed.

Lemma norm_ExprP_correct2 : 
  forall e:ExprP, interp_ExprP (norm_ExprP e) -> interp_ExprP e.
Proof.
intros; destruct (norm_ExprP_correct e); auto.
Qed.

Ltac i2z_refl := 
  i2z_gen;
  match goal with |- ?t => 
     let e := interp_prop t 
     in 
     (change (interp_ExprP e); 
      apply norm_ExprP_correct2; 
      simpl)
   end.

Ltac iauto := i2z_refl; auto.
Ltac iomega := i2z_refl; intros; romega.

  Open Scope Z_scope.

  Lemma max_spec : forall (x y:Z), 
  x >= y /\ Zmax x y = x  \/
  x <= y /\ Zmax x y = y.
  Proof.
  intros; unfold Zmax, Zle, Zge.
  destruct (Zcompare x y); [ left | right | left ]; split; auto; discriminate.
  Qed.

  Ltac omega_max_genspec x y := 
    generalize (max_spec x y); 
    let z := fresh "z" in let Hz := fresh "Hz" in 
    (set (z:=Zmax x y); clearbody z).

  Ltac omega_max_loop := 
    match goal with 
      (* hack: we don't want [i2z (height ...)] to be reduced by romega later... *)
      | |- context [ i2z (?f ?x) ] => 
          let i := fresh "i2z" in (set (i:=i2z (f x)); clearbody i); omega_max_loop
      | |- context [ Zmax ?x ?y ] => omega_max_genspec x y; omega_max_loop
      | _ => intros
    end.

  Ltac omega_max := i2z_refl; omega_max_loop; try romega.

  Ltac false_omega := elimtype False; i2z_refl; intros; romega.
  Ltac false_omega_max := elimtype False; omega_max.

 Open Scope Int_scope.
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

