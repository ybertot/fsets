
(** * Precedence Graph *)

(** Example using finite sets: *)

(** A precedence graph is an oriented acyclic graph with no redondancy:
    If a ->  ... -> b, then there is no a -> b edge. *)

(** The main result is a bound on the edge number E:
     for all acyclic precedence graph of size N,  E <= N^2/4 *)

(** Reference: J. Beauqier, B. Berard, Systemes d'exploitations, Mac Graw Hill *)

Require FSet.

Require Compare_dec.
Require Export Even.
Require Export Div2.
Require Omega.
Require ArithRing.
Import nat_scope.
Open Scope nat_scope.

Set Implicit Arguments.

(** We choose natural numbers to label the nodes. 
    With a little more work, any OrderedType could have fit. *)

Module Nat <: OrderedType.

  Definition t := nat.

  Definition eq := (eq nat).
  Definition lt := lt.

  Lemma eq_refl : (x:t) (eq x x). 
    Unfold eq; Auto. Save.
  Lemma eq_sym : (x,y:t) (eq x y) -> (eq y x). 
    Unfold eq; Auto. Save.
  Lemma eq_trans : (x,y,z:t) (eq x y) -> (eq y z) -> (eq x z).
    Unfold eq; Intros; Rewrite H; Auto. Save.
  Lemma lt_trans : (x,y,z:t) (lt x y) -> (lt y z) -> (lt x z).
    Exact Lt.lt_trans. Save.
  Lemma lt_not_eq : (x,y:t) (lt x y) -> ~(eq x y).
    Unfold lt eq; Red; Intros.
    Subst x; Exact (Lt.lt_n_n y H).
    Save.
  Definition compare : (x,y:t)(Compare lt eq x y).
    Unfold lt eq; Intros x y; Elim (lt_eq_lt_dec x y); Auto.
    Destruct 1; Intro.
    Apply Lt; Auto.
    Apply Eq; Auto.
    Intro; Apply Gt; Auto.
  Defined.

  Hints Immediate eq_sym.
  Hints Resolve eq_refl eq_trans lt_not_eq lt_trans.

End Nat.

Module Type NatSet := S with Module E := Nat.

Module Precedence [M:NatSet].
Import M.

Module MP := Properties(M).
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

Definition is_succ := [m:elt](to G n m).
Definition set_succ := (filter is_succ G).
Definition nb_succ := (cardinal set_succ).

Definition is_pred := [m:elt](to G m n).
Definition set_pred := (filter is_pred G).
Definition nb_pred := (cardinal set_pred).

Definition is_linked := [m:elt] (orb (is_pred m) (is_succ m)).
Definition set_linked := (filter is_linked G).
Definition nb_linked := (cardinal set_linked).

Definition arity := (plus nb_pred nb_succ).

Definition node_remove :=  (Build_Graph (remove n G) (to G)).

End Defs.
Definition nb_edges := [G:Graph](sum (nb_succ G) G).

(** edge number of a graph with one node removed *)

Lemma node_remove_1 :
(G:Graph;n,m:nat)
(In n G)->(In m G)->(is_pred G n m)=false -> 
(nb_succ G m)=(nb_succ (node_remove G n) m).
Proof.
Unfold nb_succ set_succ. (* Simpl. -> Anomaly *)
Unfold is_succ is_pred; Simpl.
Intros; Apply Equal_cardinal.
Unfold Equal; Split; Intros.
Assert (to G m a)=true.
 (* Replace [m0:nat](to G m m0) with (to G m) in H2. -> Anomaly *)
 Change ([m0](to G m m0) a)=true.
 EApply filter_2; EAuto.
Apply filter_3; Intuition.
Apply remove_2.
Red; Intros.
Rewrite H4 in H1; Rewrite H3 in H1; Discriminate H1.
EApply filter_1; EAuto.
Apply filter_3; Intuition.
Apply remove_3 with n; Auto.
EApply filter_1; EAuto.
Change ([m0](to G m m0) a)=true.
EApply filter_2; EAuto.
Qed.

Lemma node_remove_2 :
(G:Graph;n,m:nat)
(In n G)->(In m G)->(is_pred G n m)=true -> 
(nb_succ G m)=(S (nb_succ (node_remove G n) m)).
Proof.
Unfold nb_succ set_succ. (* Simpl. -> Anomaly *)
Unfold is_succ is_pred; Simpl; Intros. 
Assert ~(In n (filter [m0:nat](to G m m0) (remove n G))).
Intro.
Elim remove_1 with G n n; Auto.
EApply filter_1; EAuto.
Apply cardinal_2 with n; Auto.
Unfold Add; Split; Intros.

Elim (eq_nat_dec y n); Intros.
Left; Auto.
Right.
Apply filter_3; Auto.
Apply remove_2; Auto.
EApply filter_1; EAuto.
Change ([m0](to G m m0) y)=true; EApply filter_2; EAuto.

Elim (eq_nat_dec y n); Intros.
Rewrite a; Apply filter_3; Auto.
Elim H3; Intros; [Absurd y=n | Apply filter_3 ]; Auto.
Apply remove_3 with n; Auto.
EApply filter_1; EAuto.
Change ([m0](to G m m0) y)=true; EApply filter_2; EAuto.
Qed.

Lemma node_remove_3:
(G:Graph;n,m:nat)
(In n G)->(In m G)-> 
(nb_succ G m)=(nb_succ (node_remove G n) m)+(if (is_pred G n m) then 1 else 0).
Proof.
Intros.
Generalize (!node_remove_1 G n m H H0) (!node_remove_2 G n m H H0).
Case (is_pred G n m); Simpl; Intuition. 
Qed.

Theorem edges_remove : (G:Graph;n:nat)(In n G)->
(to G n n)=false->
(nb_edges G) = (nb_edges (node_remove G n))+(arity G n).
Proof.
Unfold nb_edges arity; Simpl; Intros.
LetTac f1 := [m:elt](nb_succ (node_remove G n) m).
Replace (nb_succ (node_remove G n)) with f1; Auto.
LetTac f2 := [m:elt](if (is_pred G n m) then 1 else 0).
LetTac g := [m:elt]((f1 m)+(f2 m)).
Rewrite sum_compat with (nb_succ G) g G; Auto.
Unfold g; Rewrite sum_plus; Auto.
Unfold f2; Rewrite sum_filter; Auto.
Unfold nb_pred.
Unfold set_pred.
Unfold sum.
Rewrite (!fold_2 (remove n G) G n ?? (gen_st nat) 0 [x](plus (f1 x))); Auto.
Assert (f1 n) = (nb_succ G n).
Unfold f1 nb_succ set_succ node_remove is_succ; Simpl.
Apply Equal_cardinal.
EApply add_filter_2; EAuto.
Apply Add_remove; Auto.
Rewrite H1; Omega.
Unfold transpose; Intros; Omega.
Apply Add_remove; Auto.
Unfold g f1 f2; Intros; Apply node_remove_3; Auto.
Qed.

(** * Acyclic graph *)

Inductive chain [G:Graph] : elt->elt->Set:=
 chain_i :  
 (i,j:elt)(In i G)->(In j G)->(to G i j)=true ->(chain G i j)
| chain_t : (i,j,k:elt)(chain G i j)->(chain G j k)->(chain G i k).

Definition acyclic := [G:Graph](i:nat)(chain G i i)->False.

Record AcyclicGraph :Set := {
 graph_support :> Graph;
 Hacyclic : (acyclic graph_support)
}.

(** the two definitions of arity correspond *)  

Lemma arity_isom : 
 (G: AcyclicGraph)(n:elt)(In n G)->
 (nb_linked G n)=(arity G n).
Proof.
Unfold nb_linked arity nb_pred nb_succ; Intros.
Rewrite Equal_cardinal with (set_linked G n) (union (set_pred G n) (set_succ G n)).
Rewrite union_cardinal; Auto.
Intros.
Assert (mem x (set_pred G n))=true -> (mem x (set_succ G n))=true -> False.
  Intros; Unfold set_pred is_pred set_succ is_succ in H0 H1.
  Rewrite filter_mem in H0; Rewrite filter_mem in H1; Auto.
  Elim (andb_prop ?? H0); Elim (andb_prop ?? H1); Intros.
  Elim (!Hacyclic G n); Apply chain_t with x; Apply chain_i; Auto.
Generalize H0; Case (mem x (set_pred G n)); Case (mem x (set_succ G n)); Intuition.
Unfold set_linked is_linked set_pred set_succ; Apply filter_orb; Auto.
Qed.

(** Any acyclic graph has an initial element *)

Lemma get_init_aux : (G:AcyclicGraph)(n:nat)(non_visited:t)
(cardinal non_visited)=n -> n<=(cardinal G) ->  (current:elt)(In current G) -> 
((k:elt )(In k G)->~(In k non_visited) ->(chain G current k))->
{p:nat|(In p G)/\(nb_pred G p)=O}.
Proof.
NewInduction n; Simpl; Intros.
Elim (!Hacyclic G current).
Apply H2; Auto.
Apply (cardinal_inv_1 H).
Generalize (!choose_1 (set_pred G current)) (!choose_2 (set_pred G current)).
Case (choose (set_pred G current)).
Intros newcurrent Hnc _.
Generalize (Hnc newcurrent (refl_equal ??)); Clear Hnc; Intro Hnc.
Unfold set_pred is_pred in Hnc.
Assert Hc: (compat_bool E.eq [m:elt](to G m current)). Auto.
Generalize (filter_1 Hc Hnc) (filter_2 Hc Hnc); Clear Hnc Hc; Intros Hnc1 Hnc2.
Assert Hc : (In current non_visited).
 Apply mem_2; Generalize (H2 current) (!mem_1 non_visited current).
 Case (mem current non_visited); Intuition.
 Elim (!Hacyclic G current); Auto.
Apply IHn with (remove current non_visited) newcurrent; Auto. 
Assert (S (cardinal (remove current non_visited))) = (S n).
 Rewrite <- H; Apply remove_cardinal_1; Auto.
 Inversion H3; Auto.
Auto with arith.
Intros; Elim (ME.eq_dec current k).
Intros Eq; Rewrite <- Eq; Auto.
Apply chain_i; Auto.
Intros; Apply chain_t with current; Auto; Apply chain_i; Auto.
Intros _ A. 
Exists current; Split; Auto.
Unfold nb_pred; Apply cardinal_1; Auto.
Qed.

Theorem get_init : (G:AcyclicGraph) 0 < (nb_nodes G) ->
{p:nat|(In p G)/\((nb_pred G p)=0)}.
Proof.
Intro G.
Generalize (!choose_1 G) (!choose_2 G).
Case (choose G).
Intros start; Intros.
EApply (!get_init_aux G (cardinal G) G); EAuto. 
Intros; Elim (H3 H2).
Intros; ElimType False.
Unfold nb_nodes in H1; Rewrite cardinal_1 in H1.
Inversion H1.
Apply H0; Auto.
Qed.

(** remove results for acyclic nodes *)

Lemma chain_remove : (G:Graph)(n,i,j:nat)
(chain (node_remove G n) i j)->(chain G i j).
Proof.
Unfold node_remove; Intros G n i j c; Elim c; Simpl; Intros. 
Apply chain_i; EAuto.
EApply chain_t; EAuto.
Qed.

Lemma remove_acyclic : (G:AcyclicGraph)(n:nat)(acyclic (node_remove G n)).
Proof.
Unfold acyclic;Intros;Elim (Hacyclic (chain_remove H));Auto.
Qed.

Definition acyclic_node_remove :=
 [G:AcyclicGraph;n:nat]
 (Build_AcyclicGraph (!remove_acyclic G n)).

Theorem acyclic_node_remove_correct : (G:AcyclicGraph;n:nat)(In n G)->
(nb_edges G) = (plus (nb_edges (acyclic_node_remove G n)) (nb_linked G n)).
Proof.
Unfold acyclic_node_remove;Simpl.
Intros;Rewrite arity_isom;Auto.
Intros;Apply edges_remove;Auto.
Assert ~(to G n n)=true.
 Intro Abs; Elim (Hacyclic (chain_i H H Abs)).
Generalize H0; Case (to G n n); Intuition.
Qed.

(** * Precedence Graph *)

Fixpoint length_chain [G:Graph;i,j:nat;c:(chain G i j)] : nat := 
 Cases c of 
  (chain_i _ _ _ _ _)=> 1
 |(chain_t _ _ _ c1 c2) => (length_chain c1) + (length_chain c2)
 end.

Definition precedence := [G: Graph]
 (i,j:nat;c:(chain G i j))
 (1 < (length_chain c))->(to G i j)=false.

Definition weak_precedence := [G: Graph]
 (i,j,k:nat) (In i G)-> (In j G)-> (In k G)->
 (to G i j)=true -> (to G j k)=true -> (to G i k)=false.

Theorem prec_impl_weak_prec : 
 (G: Graph)(precedence G)->(weak_precedence G).
Proof.
Unfold precedence weak_precedence;Intros.
Apply (H i k (chain_t (chain_i H0 H1 H3) (chain_i H1 H2 H4)));Simpl;Auto.
Qed.

(** The converse is false, but that doesn't matter. *)

Record WPrecGraph:Set := {
  graph_support2:>AcyclicGraph;
  Hprec:(weak_precedence graph_support2)
}. 

Lemma wprec_remove :(G:AcyclicGraph)(n:nat)(weak_precedence G)->
(weak_precedence (acyclic_node_remove G n)).
Proof.
Unfold weak_precedence;Simpl;Intros;Auto.
Apply (H i j k);EAuto.
Qed.

Definition wprec_node_remove:=[G:WPrecGraph;n:nat]
(Build_WPrecGraph (!wprec_remove G n (!Hprec G))).

(** A precedence graph has at least one node with low arity *)

Theorem low_arity : (p:nat)(G:WPrecGraph)
0 < (nb_nodes G) ->
((n:nat)(In n G)-> p < (nb_linked G n))->
(double (S p)) <= (nb_nodes G). 
Proof.
Intros;Elim (get_init H);Intros i (H1,H2).
Cut p < (nb_succ G i);Intros.
Generalize (!choose_1 (set_succ G i)) (!choose_2 (set_succ G i)).
Case (choose (set_succ G i)).
Intros j Hj _; Generalize (Hj j (refl_equal ??)); Clear Hj; Intro Hj.
Apply le_trans with (plus (nb_succ G i) (nb_linked G j)). 
Unfold double; Apply le_plus_plus;Auto.
LApply (H0 j);Auto.
Unfold set_succ is_succ  in Hj; EApply filter_1; EAuto.
Unfold nb_succ nb_linked nb_nodes;Simpl.
Rewrite <- union_cardinal;Auto.
Apply subset_cardinal.
Apply subset_1; Unfold Subset; Intros.
Elim (union_1 H4); Unfold set_succ is_succ set_linked is_linked; Intros; 
  EApply filter_1; EAuto.
Unfold set_succ is_succ in Hj; Intros.
Assert (compat_bool E.eq [m:elt](to G i m)); Auto.
Generalize (filter_1 H4 Hj) (filter_2 H4 Hj); Clear H4 Hj; Intros Hj1 Hj2.
Apply (bool_eq_ind (mem x (set_succ G i))); Simpl; Auto; Intros.
Apply (bool_eq_ind (mem x (set_linked G j))); Simpl; Auto; Intros.
Unfold set_succ is_succ in H4; Rewrite filter_mem in H4; Auto;
  Elim (andb_prop ?? H4); Clear H4; Intros.
Unfold set_linked is_linked in H5; Rewrite filter_mem in H5; Auto.
Elim (andb_prop ?? H5); Clear H5; Intros.
Elim (orb_prop ?? H7); Clear H7; Intros.
Unfold is_pred in H7.
Rewrite (!Hprec G i x j) in Hj2; Auto; Discriminate Hj2.
Rewrite (!Hprec G i j x) in H6; Auto; Discriminate H6.
Unfold compat_bool; Intros; Rewrite H7; Auto.
Intros _ A.
Unfold nb_succ in H3; Rewrite cardinal_1 in H3; Auto.
Inversion H3.
Change p<0+(nb_succ G i); Rewrite <- H2.
Generalize (!arity_isom G i H1); Unfold arity; Firstorder.
Qed.
 
Theorem low_arity_constr: (p:nat)(G:WPrecGraph) 0 < (nb_nodes G) ->
(nb_nodes G) < (double (S p)) ->
{k:nat|(In k G)/\(nb_linked G k) <= p}.
Proof.
Intros.
LetTac s := (filter [k:elt](if (le_lt_dec (nb_linked G k) p) then [_]true else [_]false) G).
Generalize (!choose_1 s) (!choose_2 s).
Case (choose s).
Unfold s; Intros x Hx _; Generalize (mem_1 (Hx x (refl_equal ??))); Clear Hx; 
  Rewrite filter_mem.
Intros Hx; Elim (andb_prop ?? Hx); Clear Hx; Intros.
Exists x; Split; Intros; Auto.
Generalize H2; Case (le_lt_dec (nb_linked G x) p); Auto; Intros; Discriminate H3.
Unfold compat_bool; Intros; Rewrite H1; Auto.
Intros _ A; Generalize (A (refl_equal ??)); Clear A; Unfold Empty s; Intros A.
Absurd (double (S p)) <= (nb_nodes G); Auto with arith.
Apply low_arity; Auto.
Intros.
Elim (le_lt_dec (nb_linked G n) p); Intros; Auto.
Elim (A n).
Apply filter_3; Auto. 
Unfold compat_bool; Intros; Rewrite H2; Auto.
Generalize a; Case (le_lt_dec (nb_linked G n) p); Auto with arith.
Intros; Absurd (nb_linked G n) <= p; Auto with arith.
Qed.

(**  Arithmetic equalities *)

Lemma Eq1:(p,q,r:nat)(le r p)->
(le (mult q (4)) (mult (double p) (double p)))->
(le (S (mult (plus q r) (4))) 
    (S (plus (double p) (mult (double p) (S (double p)))))).
Proof.
Intros;Cut (le (mult r (4)) (mult (double p) (2)));[Intros|Unfold double;Omega].
Clear H. Apply le_n_S.
Cut (n,q:nat)(plus n (mult n q))=(mult n (S q));[Intros|Intros;Ring;Simpl;Auto].
Rewrite <- (H (double p));Omega.
Ring.
Qed.

Lemma Eq2:(p,q,r:nat)(le r (S p))->
(le (S (mult q (4))) (mult (S (double p)) (S (double p))))->
(le (mult (plus q r) (4)) 
    (S (plus (S (double p)) (mult (S (double p)) (S (S (double p))))))).
Proof.
Intros;Cut (le (mult r (4)) (plus (2) (mult (S (double p)) (2))));[Intros|Unfold double;Omega].
Cut (n,q:nat)(plus n (mult n q))=(mult n (S q));[Intros|Intros;Ring;Simpl;Auto].
Rewrite <- (H2 (S (double p)));Omega.
Ring.
Qed.

(** The main theorem *)

Theorem TheBound_aux : (n:nat)(G:WPrecGraph)((nb_nodes G)=n)->
((even n)-> (nb_edges G)*4 <= (mult n n))/\
((odd n)->(S ((nb_edges G)*4)) <= (mult n n)).
Proof.
NewInduction n;Simpl.
Unfold nb_edges nb_nodes sum.
Intros. 
Rewrite (!fold_1 G ? (Logic.eq nat)); Intuition.
Inversion H0.
Apply cardinal_inv_1; Auto.
Elim (even_odd_dec n);Intro parity.
(* even *)
Split;Intros.
Inversion_clear H0.
Elim (not_even_and_odd n);Auto.
Elim (even_2n n parity);Intros p Hp.
Rewrite Hp.
Intros;Elim (!low_arity_constr p G);Intros.
Inversion_clear p0.
LetTac G':=(wprec_node_remove G x).
LApply (IHn G');Intros.
Inversion_clear H3.
Generalize (H4 parity);Intros.
Rewrite Hp in H3.
Cut (nb_edges G)=(plus (nb_edges G') (nb_linked G x));Intros.
Rewrite H6.
Apply Eq1;Auto.
Unfold G'.
Rewrite (acyclic_node_remove_correct H1);Simpl;Auto.
Unfold G'.
Assert (S (nb_nodes (wprec_node_remove G x)))=(S n).
Rewrite <-H.
Unfold nb_nodes wprec_node_remove;Simpl.
Apply remove_cardinal_1;Auto.
Inversion H3; Auto.
Rewrite H;Auto with arith.
Rewrite H;Auto with arith.
Rewrite Hp;Simpl.
Unfold double;Simpl;Auto with arith.
(* odd *)
Split;Intros.
2:Inversion_clear H0;Elim (not_even_and_odd n);Auto.
Elim (odd_S2n n parity);Intros p Hp.
Rewrite Hp.
Intros;Elim (!low_arity_constr (S p) G);Intros.
Inversion_clear p0.
LetTac G':=(wprec_node_remove G x).
LApply (IHn G');Intros.
Inversion_clear H3.
Generalize (H5 parity);Intros.
Rewrite Hp in H3.
Cut (nb_edges G)=(plus (nb_edges G') (nb_linked G x));Intros.
Rewrite H6.
Apply Eq2;Auto.
Unfold G'.
Rewrite (acyclic_node_remove_correct H1);Simpl;Auto.
Unfold G'.
Assert (S (nb_nodes (wprec_node_remove G x)))=(S n).
Rewrite <-H.
Unfold nb_nodes wprec_node_remove;Simpl.
Apply remove_cardinal_1;Auto.
Inversion H3; Auto.
Rewrite H;Auto with arith.
Rewrite H;Auto.
Rewrite Hp;Simpl;Auto.
Unfold double;Simpl;Auto with arith.
Qed.

Theorem TheBound : (G:WPrecGraph)
(nb_edges G)*4 <= (nb_nodes G)*(nb_nodes G).
Proof.
Intros;Elim (!TheBound_aux (nb_nodes G) G);Auto;Intros.
Elim (even_odd_dec (nb_nodes G));Intros.
Exact (H a).
Generalize (H0 b);Auto with arith.
Qed.

End Precedence.
