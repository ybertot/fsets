
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

  (** key lemma for correctness *)

  Lemma flatten_e_elements :
    forall (x : elt) (l r : tree) (z : Z) (e : enumeration),
    elements_tree (Node l x r z) ++ flatten_e e =
    elements_tree l ++ flatten_e (More x r e).
  Proof.

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

  Ltac Measure_e_t := unfold measure_e_t in |- *; fold measure_e_t in |- *.
  Ltac Measure_e := unfold measure_e in |- *; fold measure_e in |- *.

  Lemma measure_e_t_0 : forall s : tree, measure_e_t s >= 0.
  Proof.
    simple induction s.
    simpl in |- *; omega.
    intros.
    Measure_e_t; omega. (* BUG Simpl! *)
  Qed.

  Ltac Measure_e_t_0 s := generalize (measure_e_t_0 s); intro.

  Lemma measure_e_0 : forall e : enumeration, measure_e e >= 0.
  Proof.
    simple induction e.
    simpl in |- *; omega.
    intros.
    Measure_e; Measure_e_t_0 t0; omega.
  Qed.

  Ltac Measure_e_0 e := generalize (measure_e_0 e); intro.

  (** Induction principle over the sum of the measures for two lists *)

  Definition compare2_rec2 :
    forall P : enumeration -> enumeration -> Set,
    (forall x x' : enumeration,
     (forall y y' : enumeration,
      measure_e y + measure_e y' < measure_e x + measure_e x' -> P y y') ->
     P x x') -> forall x x' : enumeration, P x x'.
  Proof.
    intros P H x x'.
    apply
     well_founded_induction_type_2
      with
        (R := fun yy' xx' : enumeration * enumeration =>
              measure_e (fst yy') + measure_e (snd yy') <
              measure_e (fst xx') + measure_e (snd xx')); 
     auto.                      
    apply
     Wf_nat.well_founded_lt_compat
      with
        (f := fun xx' : enumeration * enumeration =>
              Zabs_nat (measure_e (fst xx') + measure_e (snd xx'))).
    intros; apply Zabs.Zabs_nat_lt.
    Measure_e_0 (fst x0); Measure_e_0 (snd x0); Measure_e_0 (fst y);
     Measure_e_0 (snd y); intros; omega.
  Qed.

  (** [cons t e] adds the elements of tree [t] on the head of 
      enumeration [e]. Code:
 
  let rec cons s e = match s with
  | Empty -> e
  | Node(l, v, r, _) -> cons l (More(v, r, e))
  *)

  Definition cons :
    forall (s : tree) (e : enumeration),
    bst s ->
    sorted_e e ->
    (forall (x y : elt), In_tree x s -> In_tree_e y e -> X.lt x y) ->
    { r : enumeration 
    | sorted_e r /\ 
      measure_e r = measure_e_t s + measure_e e /\
      flatten_e r = elements_tree s ++ flatten_e e
      (* forall (x : elt), In_tree_e x r <-> (In_tree x s \/ In_tree_e x e) *)
    }.
  Proof.
    simple induction s; intuition.
    (* s = Leaf *)
    exists e; intuition.
    (* s = Node t0 t1 t2 z *)
    clear H0.
    case (H (More t1 t2 e)); clear H; intuition.
    inversion_clear H1; auto.
    constructor; inversion_clear H1; auto.
    inversion_clear H0; intuition.
    inversion_clear H1.
    apply ME.lt_eq with t1; auto.
    inversion_clear H1.
    apply X.lt_trans with t1; auto.
    exists x; intuition.
    generalize H4; Measure_e; intros; Measure_e_t; omega.
    unfold elements_tree; simpl.
    (* ... *)
  Admitted. (*Qed.*)

  Definition compare2_aux :
    forall e1 e2 : enumeration,
    sorted_e e1 ->
    sorted_e e2 ->
    Compare L.lt L.eq (flatten_e e1) (flatten_e e2).
  Proof.
    intros e1 e2; pattern e1, e2 in |- *; apply compare2_rec2.
    simple destruct x; simple destruct x'; intuition.
    (* x = x' = End *)
    constructor 2; unfold L.eq, L.Equal in |- *; intuition.
    (* x = End x' = More *)
    constructor 1; simpl in |- *; auto.
    (* x = More x' = End *)
    constructor 3; simpl in |- *; auto.
    (* x = More e t0 e0, x' = More e3 t1 e4 *)
    case (X.compare e e3); intro.
    (* e < e3 *)
    constructor 1; simpl; auto.
    (* e = e3 *)
    case (cons t0 e0).
    inversion_clear H0; auto.
    inversion_clear H0; auto.
    inversion_clear H0; auto.
    intro c1; intuition.
    case (cons t1 e4).
    inversion_clear H1; auto.
    inversion_clear H1; auto.
    inversion_clear H1; auto.
    intro c2; intuition.
    case (H c1 c2); clear H; intuition.
    Measure_e; omega.
    constructor 1; simpl.
    apply L.lt_cons_eq; auto.
    rewrite H5 in l; rewrite H8 in l; auto.
    constructor 2; simpl.
    apply l_eq_cons; auto.
    rewrite H5 in e6; rewrite H8 in e6; auto.
    constructor 3; simpl.
    apply L.lt_cons_eq; auto.
    rewrite H5 in l; rewrite H8 in l; auto.
    (* e > e3 *)
    constructor 3; simpl; auto.
  Defined.

  Definition compare2 : forall s1 s2 : t, Compare lt eq s1 s2.
  Proof.
    intros (s1, s1_bst, s1_avl) (s2, s2_bst, s2_avl); unfold lt, eq in |- *;
     simpl in |- *.
    case (cons s1 End); intuition.
    inversion_clear H0.
    case (cons s2 End); intuition.
    inversion_clear H3.
    simpl in H2; rewrite <- app_nil_end in H2.
    simpl in H5; rewrite <- app_nil_end in H5.
    case (compare2_aux x x0); intuition.
    constructor 1; simpl in |- *.
    rewrite H2 in l; rewrite H5 in l; auto.
    constructor 2; apply L_eq_eq; simpl in |- *.
    rewrite H2 in e; rewrite H5 in e; auto.
    constructor 3; simpl in |- *.
    rewrite H2 in l; rewrite H5 in l; auto.
  Defined.
