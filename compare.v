
Restore State "toto".

(* 
type enumeration = End | More of elt * t * enumeration

let rec cons s e = match s with
  | Empty -> e
  | Node(l, v, r, _) -> cons l (More(v, r, e))

let rec compare_aux e1 e2 = match (e1, e2) with
  | (End, End) -> 0
  | (End, More _) -> -1
  | (More _, End) -> 1
  | (More(v1, r1, k1), More(v2, r2, k2)) ->
      let c = Ord.compare v1 v2 in
      if c <> 0 then c else compare_aux (cons r1 k1) (cons r2 k2)

let compare s1 s2 = compare_aux (cons s1 End) (cons s2 End)
*)

  (** ** Enumeration of the elements of a tree *)

  Inductive enumeration : Set :=
   | End : enumeration
   | More : elt -> tree -> enumeration -> enumeration.

  (** [flatten_e e] returns the list of elements of [e] i.e. the list
      of elements actually compared *)
 
   Fixpoint flatten_e (e : enumeration) : list elt :=
    match e with
    | End => []
    | More x t r => x :: elements_tree t ++ flatten_e r
    end.

  (** [sorted_e e] expresses that elements in the enumeration [e] are
      sorted, and that all trees in [e] are binary search trees. *)

  Inductive In_tree_e (x:elt) : enumeration -> Prop :=
    | InEHd1 :
        forall (y : elt) (s : tree) (e : enumeration),
        X.eq x y -> In_tree_e x (More y s e)
    | InEHd2 :
        forall (y : elt) (s : tree) (e : enumeration),
        In_tree x s -> In_tree_e x (More y s e)
    | InETl :
        forall (y : elt) (s : tree) (e : enumeration),
        In_tree_e x e -> In_tree_e x (More y s e).

  Hint Constructors In_tree_e.

  Inductive sorted_e : enumeration -> Prop :=
    | SortedEEnd : sorted_e End
    | SortedEMore :
        forall (x : elt) (s : tree) (e : enumeration),
        bst s ->
        (gt_tree x s) ->
        sorted_e e ->
        (forall y : elt, In_tree_e y e -> X.lt x y) ->
        (forall y : elt,
         In_tree y s -> forall z : elt, In_tree_e z e -> X.lt y z) ->
        sorted_e (More x s e).

  Hint Constructors sorted_e.

  Lemma in_flatten_e :
   forall (x : elt) (e : enumeration), L.ME.In x (flatten_e e) -> In_tree_e x e.
  Proof.
    simple induction e; simpl in |- *; intuition.
    inversion_clear H.
    inversion_clear H0; auto.
    elim (in_app x _ _ H1); auto.
  Qed.

  Lemma sorted_flatten_e :
   forall e : enumeration, sorted_e e -> L.ME.Sort (flatten_e e).
  Proof.
    simple induction e; simpl in |- *; intuition.
    apply cons_sort.
    apply sort_app; inversion H0; auto.
    intros; apply H8; auto.
    apply in_flatten_e; auto.
    apply L.ME.Inf_In.
    inversion_clear H0.
    intros; elim (in_app_or _ _ _ H0); intuition.
    apply H2; auto.
    apply H4; apply in_flatten_e; auto.
  Qed.

  (** termination of [compare_aux] *)
 
  Fixpoint measure_e_t (s : tree) : Z :=
    match s with
    | Leaf => 0
    | Node l _ r _ => 1 + measure_e_t l + measure_e_t r
    end.

  Fixpoint measure_e (e : enumeration) : Z :=
    match e with
    | End => 0
    | More _ s r => 1 + measure_e_t s + measure_e r
    end.

 (** Induction principle over the sum of the measures for two lists *)

  Definition compare2_rec2 :
    forall P : list tree -> list tree -> Set,
    (forall x x' : list tree,
     (forall y y' : list tree,
      measure_l y + measure_l y' < measure_l x + measure_l x' -> P y y') ->
     P x x') -> forall x x' : list tree, P x x'.
  Proof.
    intros P H x x'.
    apply
     well_founded_induction_type_2
      with
        (R := fun yy' xx' : list tree * list tree =>
              measure_l (fst yy') + measure_l (snd yy') <
              measure_l (fst xx') + measure_l (snd xx')); 
     auto.                      
    apply
     Wf_nat.well_founded_lt_compat
      with
        (f := fun xx' : list tree * list tree =>
              Zabs_nat (measure_l (fst xx') + measure_l (snd xx'))).
    intros; apply Zabs.Zabs_nat_lt.
    Measure_l_0 (fst x0); Measure_l_0 (snd x0); Measure_l_0 (fst y);
     Measure_l_0 (snd y); intros; omega.

 (** [cons t e] adds the elements of tree [t] on the head of 
      enumeration [e] *)

  Definition compare2_aux :
    forall e1 e2 : enumeration,
    sorted_e e1 ->
    sorted_e e2 ->
    leaf_invariant l1 l2 -> Compare L.lt L.eq (flatten_e e1) (flatten_e e2).
  Proof.
 