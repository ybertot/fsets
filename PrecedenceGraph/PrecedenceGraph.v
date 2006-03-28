
(** * Precedence Graph *)

(** Example using finite sets: *)

(** A precedence graph is an oriented acyclic graph with no redondancy:
    If a ->  ... -> b, then there is no a -> b edge. *)

(** The main result is a bound on the edge number E:
     for all acyclic precedence graph of size N,  E <= N^2/4 *)

(** Reference: J. Beauqier, B. Berard, Systemes d'exploitations, Mac Graw Hill *)

Require Import FSets.

Require Import Sumbool.
Require Import Compare_dec.
Require Import Even.
Require Import Div2.
Require Import Omega.
Require Import ArithRing.
Open Scope nat_scope.

Set Implicit Arguments.

(** We choose natural numbers to label the nodes. 
    With a little more work, any OrderedType could have fit. *)

Module Nat <: OrderedType.

  Definition t := nat.

  Definition eq := @eq nat.
  Definition lt := lt.

  Lemma eq_refl : forall (x:t), eq x x. 
    unfold eq; auto. Save.
  Lemma eq_sym : forall (x y:t), (eq x y) -> (eq y x). 
    unfold eq; auto. Save.
  Lemma eq_trans : forall (x y z:t), (eq x y) -> (eq y z) -> (eq x z).
    unfold eq; intros; rewrite H; auto. Save.
  Lemma lt_trans : forall (x y z:t), (lt x y) -> (lt y z) -> (lt x z).
    exact Lt.lt_trans. Save.
  Lemma lt_not_eq : forall (x y:t), (lt x y) -> ~(eq x y).
    unfold lt, eq; red; intros.
    subst x; exact (lt_irrefl y H).
    Save.
  Definition compare : forall (x y:t),(Compare lt eq x y).
    unfold lt, eq; intros x y; elim (lt_eq_lt_dec x y); auto.
    destruct 1.
    apply LT; auto.
    apply EQ; auto.
    intro; apply GT; auto.
  Defined.

  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans lt_not_eq lt_trans.

End Nat.

Module Type Natset := S with Module E := Nat.

Module Precedence (M:Natset).
Import M.

Module MP := EqProperties(M).
Import MP.MP.
Import MP.

(** A graph is composed of a set of nodes and a transition function *)

Record Graph : Set := {
  nodes:> t;
  to: nat -> nat -> bool
}. 

(** basic definitions *)

Section Defs.

Variable G:Graph.

Variable n:nat.

Definition nb_nodes := (cardinal G).

Definition is_succ (m:elt) := (to G n m).
Definition set_succ := (filter is_succ G).
Definition nb_succ := (cardinal set_succ).

Definition is_pred (m:elt) := (to G m n).
Definition set_pred := (filter is_pred G).
Definition nb_pred := (cardinal set_pred).

Definition is_linked (m:elt) := (orb (is_pred m) (is_succ m)).
Definition set_linked := (filter is_linked G).
Definition nb_linked := (cardinal set_linked).

Definition arity := (plus nb_pred nb_succ).

Definition node_remove :=  (Build_Graph (remove n G) (to G)).

End Defs.
Definition nb_edges (G:Graph) := (sum (nb_succ G) G).

(** edge number of a graph with one node removed *)

Lemma node_remove_1 :
forall (G:Graph)(n m:nat),
(In n G)->(In m G)->(is_pred G n m)=false -> 
(nb_succ G m)=(nb_succ (node_remove G n) m).
Proof.
unfold nb_succ, set_succ; simpl.
unfold is_succ, is_pred; simpl.
intros; apply Equal_cardinal.
unfold Equal; split; intros.
assert (to G m a = true).
 change ((fun m0 =>to G m m0) a = true).
 eapply filter_2; eauto.
apply filter_3; intuition.
apply remove_2.
red; intros.
rewrite H4 in H1; rewrite H3 in H1; discriminate H1.
eapply filter_1; eauto.
apply filter_3; intuition.
apply remove_3 with n; auto.
eapply filter_1; eauto.
change ((fun m0 => to G m m0) a = true).
eapply filter_2; eauto.
Qed.

Lemma node_remove_2 :
forall (G:Graph)(n m:nat), 
(In n G)->(In m G)->(is_pred G n m)=true -> 
(nb_succ G m)=(S (nb_succ (node_remove G n) m)).
Proof.
unfold nb_succ, set_succ; simpl.
unfold is_succ, is_pred; simpl; intros. 
assert (~ In n (filter (fun m0 => to G m m0) (remove n G))).
intro.
elim remove_1 with G n n; auto.
eapply filter_1; eauto.
apply cardinal_2 with n; auto.
unfold Add; split; intros.

elim (eq_nat_dec y n); intros.
left; auto.
right.
apply filter_3; auto.
apply remove_2; auto.
eapply filter_1; eauto.
change ((fun m0 => to G m m0) y = true); eapply filter_2; eauto.

elim (eq_nat_dec y n); intros.
rewrite a; apply filter_3; auto.
elim H3; intros; [absurd (y=n) | apply filter_3 ]; auto.
apply remove_3 with n; auto.
eapply filter_1; eauto.
change ((fun m0 => to G m m0) y =true); eapply filter_2; eauto.
Qed.

Lemma node_remove_3:
forall (G:Graph)(n m:nat),
(In n G)->(In m G)-> 
(nb_succ G m)=(nb_succ (node_remove G n) m)+(if (is_pred G n m) then 1 else 0).
Proof.
intros.
generalize (@node_remove_1 G n m H H0) (@node_remove_2 G n m H H0).
case (is_pred G n m); simpl; intuition. 
Qed.

Theorem edges_remove : forall (G:Graph)(n:nat), (In n G)->
(to G n n)=false->
(nb_edges G) = (nb_edges (node_remove G n))+(arity G n).
Proof.
unfold nb_edges, arity; simpl; intros.
set (f1 := fun m => nb_succ (node_remove G n) m).
replace (nb_succ (node_remove G n)) with f1; auto.
set (f2 := fun m => if (is_pred G n m) then 1 else 0).
set (g := fun m => f1 m + f2 m).
rewrite sum_compat with (nb_succ G) g G; auto.
unfold g; rewrite sum_plus; auto.
unfold f2; rewrite sum_filter; auto.
unfold nb_pred.
unfold set_pred.
unfold sum.
rewrite (@fold_2 (remove n G) G n _ _  (gen_st nat) 0 (fun x => plus (f1 x))); auto.
assert (f1 n  = nb_succ G n).
unfold f1, nb_succ, set_succ, node_remove, is_succ; simpl.
apply Equal_cardinal.
eapply add_filter_2; unfold Add; eauto.
rewrite H1; omega.
unfold transpose; intros; omega.
unfold g, f1, f2; intros; apply node_remove_3; auto.
Qed.

(** * Acyclic graph *)

Inductive chain (G:Graph) : elt->elt->Set:=
 chain_i :  forall i j, In i G -> In j G -> to G i j = true -> chain G i j
| chain_t : forall i j k,chain G i j -> chain G j k -> chain G i k.

Definition acyclic (G:Graph) := forall i, chain G i i ->False.

Record AcyclicGraph : Set := {
 graph_support :> Graph;
 Hacyclic : (acyclic graph_support)
}.

(** the two definitions of arity correspond *)  

Lemma arity_isom : 
 forall (G: AcyclicGraph)(n:elt), (In n G)->
 (nb_linked G n)=(arity G n).
Proof.
unfold nb_linked, arity, nb_pred, nb_succ; intros.
rewrite Equal_cardinal with (set_linked G n) (union (set_pred G n) (set_succ G n)).
rewrite union_cardinal; auto.
intros.
assert (mem x (set_pred G n) = true -> (mem x (set_succ G n))=true -> False).
  intros; unfold set_pred, is_pred, set_succ, is_succ in H0, H1.
  rewrite filter_mem in H0; rewrite filter_mem in H1; auto.
  elim (andb_prop _ _  H0); elim (andb_prop _ _ H1); intros.
  elim (@Hacyclic G n); apply chain_t with x; apply chain_i; auto.
generalize H0; case (mem x (set_pred G n)); case (mem x (set_succ G n)); intuition.
unfold set_linked, is_linked, set_pred, set_succ; apply eq_sym; apply union_filter; auto.
Qed.

(** Any acyclic graph has an initial element *)

Lemma get_init_aux : 
forall (G:AcyclicGraph)(n:nat)(non_visited:t), 
(cardinal non_visited)=n -> n<=(cardinal G) ->  forall (current:elt),(In current G) -> 
(forall k, In k G ->~(In k non_visited) ->(chain G current k))->
{p:nat|(In p G)/\(nb_pred G p)=O}.
Proof.
induction n; simpl; intros.
elim (@Hacyclic G current).
apply H2; auto.
apply (cardinal_inv_1 H).
generalize (@choose_1 (set_pred G current)) (@choose_2 (set_pred G current)).
case (choose (set_pred G current)).
intros newcurrent Hnc _.
generalize (Hnc newcurrent (refl_equal _)); clear Hnc; intro Hnc.
unfold set_pred, is_pred in Hnc.
assert (Hc: compat_bool E.eq (fun m => to G m current)). auto.
generalize (filter_1 Hc Hnc) (filter_2 Hc Hnc); clear Hnc Hc; intros Hnc1 Hnc2.
assert (Hc: In current non_visited).
 apply mem_2; generalize (H2 current) (@mem_1 non_visited current).
 case (mem current non_visited); intuition.
 elim (@Hacyclic G current); auto.
apply IHn with (remove current non_visited) newcurrent; auto. 
assert (S (cardinal (remove current non_visited))  = (S n)).
 rewrite <- H; apply remove_cardinal_1; auto.
 inversion H3; auto.
auto with arith.
intros; elim (ME.eq_dec current k).
intros Eq; rewrite <- Eq; auto.
apply chain_i; auto.
intros; apply chain_t with current; auto; apply chain_i; auto.
intros _ A. 
exists current; split; auto.
unfold nb_pred; apply cardinal_1; auto.
Qed.

Theorem get_init : forall (G:AcyclicGraph), 0 < (nb_nodes G) ->
{p:nat|(In p G)/\((nb_pred G p)=0)}.
Proof.
intro G.
generalize (@choose_1 G) (@choose_2 G).
case (choose G).
intros start; intros.
eapply (@get_init_aux G (cardinal G) G); eauto. 
intros; elim (H3 H2).
intros; elimtype False.
unfold nb_nodes in H1; rewrite cardinal_1 in H1.
inversion H1.
apply H0; auto.
Qed.

(** remove results for acyclic nodes *)

Lemma chain_remove : forall (G:Graph)(n i j:nat),
(chain (node_remove G n) i j)->(chain G i j).
Proof.
unfold node_remove; intros G n i j c; elim c; simpl; intros. 
apply chain_i; eauto.
eapply chain_t; eauto.
Qed.

Lemma remove_acyclic : forall (G:AcyclicGraph)(n:nat), (acyclic (node_remove G n)).
Proof.
unfold acyclic;intros;elim (Hacyclic _ (chain_remove H));auto.
Qed.

Definition acyclic_node_remove (G:AcyclicGraph)(n:nat) :=
 (Build_AcyclicGraph (@remove_acyclic G n)).

Theorem acyclic_node_remove_correct : 
 forall (G:AcyclicGraph)(n:nat), (In n G)->
(nb_edges G) = (plus (nb_edges (acyclic_node_remove G n)) (nb_linked G n)).
Proof.
unfold acyclic_node_remove;simpl.
intros;rewrite arity_isom;auto.
intros;apply edges_remove;auto.
assert (~ to G n n =true).
 intro Abs; elim (Hacyclic _ (chain_i _ H H Abs)).
generalize H0; case (to G n n); intuition.
Qed.

(** * Precedence Graph *)

Fixpoint length_chain (G:Graph)(i j:nat)(c: chain G i j) 
  {struct c} : nat := 
 match c with
   chain_i _ _ _ _ _  => 1
 | chain_t _ _ _ c1 c2 => (length_chain c1) + (length_chain c2)
 end.

Definition precedence (G: Graph) := forall (i j:nat)(c:chain G i j),
  1 < (length_chain c) ->  to G i j =false.

Definition weak_precedence (G: Graph) := forall (i j k:nat),
 (In i G)-> (In j G)-> (In k G)->
 (to G i j)=true -> (to G j k)=true -> (to G i k)=false.

Theorem prec_impl_weak_prec : 
 forall (G:Graph), (precedence G)->(weak_precedence G).
Proof.
unfold precedence, weak_precedence;intros.
apply (H i k (chain_t (chain_i _ H0 H1 H3) (chain_i _ H1 H2 H4)));simpl;auto.
Qed.

(** The converse is false, but that doesn't matter. *)

Record WPrecGraph:Set := {
  graph_support2:>AcyclicGraph;
  Hprec:(weak_precedence graph_support2)
}. 

Lemma wprec_remove : forall (G:AcyclicGraph)(n:nat), 
(weak_precedence G)->
(weak_precedence (acyclic_node_remove G n)).
Proof.
unfold weak_precedence;simpl;intros;auto.
apply (H i j k);eauto.
Qed.

Definition wprec_node_remove (G:WPrecGraph)(n:nat) :=
(Build_WPrecGraph _ (@wprec_remove G n (@Hprec G))).

(** A precedence graph has at least one node with low arity *)

Theorem low_arity : forall (p:nat)(G:WPrecGraph),
0 < (nb_nodes G) ->
(forall n, In n G -> p < (nb_linked G n))->
(double (S p)) <= (nb_nodes G). 
Proof.
intros;elim (get_init _ H);intros i (H1,H2).
cut (p < nb_succ G i);intros.
generalize (@choose_1 (set_succ G i)) (@choose_2 (set_succ G i)).
case (choose (set_succ G i)).
intros j Hj _; generalize (Hj j (refl_equal _)); clear Hj; intro Hj.
apply le_trans with (plus (nb_succ G i) (nb_linked G j)). 
unfold double; apply plus_le_compat;auto.
lapply (H0 j);auto.
unfold set_succ, is_succ  in Hj; eapply filter_1; eauto.
unfold nb_succ, nb_linked, nb_nodes;simpl.
rewrite <- union_cardinal;auto.
apply subset_cardinal.
apply subset_1; unfold Subset; intros.
elim (union_1 H4); unfold set_succ, is_succ, set_linked, is_linked; intros; 
  eapply filter_1; eauto.
unfold set_succ, is_succ in Hj; intros.
assert (compat_bool E.eq (fun m=>to G i m)); auto.
generalize (filter_1 H4 Hj) (filter_2 H4 Hj); clear H4 Hj; intros Hj1 Hj2.
apply (bool_eq_ind (mem x (set_succ G i))); simpl; auto; intros.
apply (bool_eq_ind (mem x (set_linked G j))); simpl; auto; intros.
unfold set_succ, is_succ in H4; rewrite filter_mem in H4; auto;
  elim (andb_prop _ _ H4); clear H4; intros.
unfold set_linked, is_linked in H5; rewrite filter_mem in H5; auto.
elim (andb_prop _ _ H5); clear H5; intros.
elim (orb_prop _ _ H7); clear H7; intros.
unfold is_pred in H7.
rewrite (@Hprec G i x j) in Hj2; auto; discriminate Hj2.
rewrite (@Hprec G i j x) in H6; auto; discriminate H6.
unfold compat_bool; intros; rewrite H7; auto.
intros _ A.
unfold nb_succ in H3; rewrite cardinal_1 in H3; auto.
inversion H3.
change (p<0+nb_succ G i); rewrite <- H2.
generalize (@arity_isom G i H1); unfold arity; firstorder.
Qed.
 
Theorem low_arity_constr: forall (p:nat)(G:WPrecGraph),
 0 < (nb_nodes G) ->
(nb_nodes G) < (double (S p)) ->
{k:nat|(In k G)/\(nb_linked G k) <= p}.
Proof.
intros.
set (s := filter (fun k => if le_lt_dec (nb_linked G k) p then true else false) G).
generalize (@choose_1 s) (@choose_2 s).
case (choose s).
unfold s; intros x Hx _; generalize (mem_1 (Hx x (refl_equal _))); clear Hx; 
  rewrite filter_mem.
intros Hx; elim (andb_prop _ _ Hx); clear Hx; intros.
exists x; split; intros; auto.
generalize H2; case (le_lt_dec (nb_linked G x) p); auto; intros; discriminate H3.
unfold compat_bool; intros; rewrite H1; auto.
intros _ A; generalize (A (refl_equal _)); clear A; unfold Empty, s; intros A.
absurd (double (S p)  <= nb_nodes G); auto with arith.
apply low_arity; auto.
intros.
elim (le_lt_dec (nb_linked G n) p); intros; auto.
elim (A n).
apply filter_3; auto. 
unfold compat_bool; intros; rewrite H2; auto.
generalize a; case (le_lt_dec (nb_linked G n) p); auto with arith.
intros; absurd (nb_linked G n <= p); auto with arith.
Qed.

(**  Arithmetic equalities *)

Lemma Eq1: forall p q r, (le r p)->
(le (mult q (4)) (mult (double p) (double p)))->
(le (S (mult (plus q r) (4))) 
    (S (plus (double p) (mult (double p) (S (double p)))))).
Proof.
intros;cut (le (mult r (4)) (mult (double p) (2)));[intros|unfold double;omega].
clear H. apply le_n_S.
cut (forall n q, plus n (mult n q)= mult n (S q));[intros|intros;ring;simpl;auto].
rewrite <- (H (double p));omega.
ring.
Qed.

Lemma Eq2: forall p q r, (le r (S p))->
(le (S (mult q (4))) (mult (S (double p)) (S (double p))))->
(le (mult (plus q r) (4)) 
    (S (plus (S (double p)) (mult (S (double p)) (S (S (double p))))))).
Proof.
intros;cut (le (mult r (4)) (plus (2) (mult (S (double p)) (2))));[intros|unfold double;omega].
cut (forall n q, plus n (mult n q)=mult n (S q));[intros|intros;ring;simpl;auto].
rewrite <- (H2 (S (double p)));omega.
ring.
Qed.

(** The main theorem *)

Theorem TheBound_aux : forall n (G:WPrecGraph), ((nb_nodes G)=n)->
((even n)-> (nb_edges G)*4 <= (mult n n))/\
((odd n)->(S ((nb_edges G)*4)) <= (mult n n)).
Proof.
induction n;simpl.
unfold nb_edges, nb_nodes, sum.
intros. 
rewrite (@fold_1 G _ (@Logic.eq nat)); intuition.
inversion H0.
elim (even_odd_dec n);intro parity.
(* even *)
split;intros.
inversion_clear H0.
elim (not_even_and_odd n);auto.
elim (even_2n n parity);intros p Hp.
rewrite Hp.
intros;elim (@low_arity_constr p G);intros.
inversion_clear p0.
set (G':=wprec_node_remove G x).
lapply (IHn G');intros.
inversion_clear H3.
generalize (H4 parity);intros.
rewrite Hp in H3.
cut (nb_edges G = plus (nb_edges G') (nb_linked G x));intros.
rewrite H6.
apply Eq1;auto.
unfold G'.
rewrite (acyclic_node_remove_correct _ H1);simpl;auto.
unfold G'.
assert (S (nb_nodes (wprec_node_remove G x))=(S n)).
rewrite <-H.
unfold nb_nodes, wprec_node_remove;simpl.
apply remove_cardinal_1;auto.
inversion H3; auto.
rewrite H;auto with arith.
rewrite H;auto with arith.
rewrite Hp;simpl.
unfold double;simpl;auto with arith.
(* odd *)
split;intros.
2:inversion_clear H0;elim (not_even_and_odd n);auto.
elim (odd_S2n n parity);intros p Hp.
rewrite Hp.
intros;elim (@low_arity_constr (S p) G);intros.
inversion_clear p0.
set (G':=wprec_node_remove G x).
lapply (IHn G');intros.
inversion_clear H3.
generalize (H5 parity);intros.
rewrite Hp in H3.
cut (nb_edges G = plus (nb_edges G') (nb_linked G x));intros.
rewrite H6.
apply Eq2;auto.
unfold G'.
rewrite (acyclic_node_remove_correct _ H1);simpl;auto.
unfold G'.
assert (S (nb_nodes (wprec_node_remove G x))=S n).
rewrite <-H.
unfold nb_nodes, wprec_node_remove;simpl.
apply remove_cardinal_1;auto.
inversion H3; auto.
rewrite H;auto with arith.
rewrite H;auto.
rewrite Hp;simpl;auto.
unfold double;simpl;auto with arith.
Qed.

Theorem TheBound : forall G:WPrecGraph,
(nb_edges G)*4 <= (nb_nodes G)*(nb_nodes G).
Proof.
intros;elim (@TheBound_aux (nb_nodes G) G);auto;intros.
elim (even_odd_dec (nb_nodes G));intros.
exact (H a).
generalize (H0 b);auto with arith.
Qed.

End Precedence.
