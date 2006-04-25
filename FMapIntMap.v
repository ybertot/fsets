Require Import Bool.
Require Import NArith Ndigits Ndec Nnat. 
Require Import Allmaps.
Require Import OrderedType.
Require Import FMapInterface.
Require Import SomeOrderedType.

Set Implicit Arguments.

(** [N] is an ordered type, using not the usual order on numbers, 
   but the one on bits (lower bit considered first). *) 

Module NUsualOrderedType <: UsualOrderedType.
  Definition t:=N.
  Definition eq:=@eq N.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.

  Definition lt p q:= Nless p q = true.
 
  Definition lt_trans := Nless_trans.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
  intros; intro.
  rewrite H0 in H.
  red in H.
  rewrite Nless_not_refl in H; discriminate.
  Qed.

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
  intros x y.
  destruct (Nless_total x y) as [[H|H]|H].
  apply LT; unfold lt; auto.
  apply GT; unfold lt; auto.
  apply EQ; auto.
  Qed.

End NUsualOrderedType.
 

(** The module of maps over [N] keys based on [IntMap] *)

Module MapIntMap <: S with Module E:=NUsualOrderedType.

  Module E:=NUsualOrderedType.
  Module PE:=OrderedType.PairOrderedType(E).

  Definition key := N.

  Definition t := Map.

  Section A.
  Variable A:Set.

  Definition empty : t A := M0 A.
 
  Definition is_empty (m : t A) : bool := 
    MapEmptyp _ (MapCanonicalize _ m).

  Definition find (x:key)(m: t A) : option A := MapGet _ m x.

  Definition mem (x:key)(m: t A) : bool := 
    match find x m with 
     | Some _ => true
     | None => false
    end.

  Definition add (x:key)(v:A)(m:t A) : t A := MapPut _ m x v.
  
  Definition remove (x:key)(m:t A) : t A := MapRemove _ m x.

  Definition elements (m : t A) : list (N*A) := alist_of_Map _ m.

  Definition MapsTo (x:key)(v:A)(m:t A) := find x m = Some v.

  Definition In (x:key)(m:t A) := exists e:A, MapsTo x e m.

  Definition Empty m := forall (a : key)(e:A) , ~ MapsTo a e m.

  Definition eq_key (p p':key*A) := E.eq (fst p) (fst p').
      
  Definition eq_key_elt (p p':key*A) := 
          E.eq (fst p) (fst p') /\ (snd p) = (snd p').

  Definition lt_key (p p':key*A) := E.lt (fst p) (fst p').

  Lemma Empty_alt : forall m, Empty m <-> forall a, find a m = None.
  Proof.
  unfold Empty, MapsTo.
  intuition.
  generalize (H a).
  destruct (find a m); intuition.
  elim (H0 a0); auto.
  rewrite H in H0; discriminate.
  Qed.

  Section Spec. 
  Variable  m m' m'' : t A.
  Variable x y z : key.
  Variable e e' : A.

  Lemma MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
  Proof. intros; rewrite <- H; auto. Qed.

  Lemma find_1 : MapsTo x e m -> find x m = Some e.
  Proof. unfold MapsTo; auto. Qed.

  Lemma find_2 : find x m = Some e -> MapsTo x e m.
  Proof. red; auto. Qed.

  Lemma empty_1 : Empty empty.
  Proof.
  rewrite Empty_alt; intros; unfold empty, find; simpl; auto.
  Qed.

  Lemma is_empty_1 : Empty m -> is_empty m = true. 
  Proof.
  unfold Empty, is_empty, find; intros.
  cut (MapCanonicalize _ m = M0 _).
  intros; rewrite H0; simpl; auto.
  apply mapcanon_unique.
  apply mapcanon_exists_2.
  constructor.
  red; red; simpl; intros.
  rewrite <- (mapcanon_exists_1 _ m).
  unfold MapsTo, find in *.
  generalize (H a).
  destruct (MapGet _ m a); auto.
  intros; generalize (H0 a0); destruct 1; auto.
  Qed.  

  Lemma is_empty_2 : is_empty m = true -> Empty m.
  Proof.
  unfold Empty, is_empty, MapsTo, find; intros.
  generalize (MapEmptyp_complete _ _ H); clear H; intros.
  rewrite (mapcanon_exists_1 _ m).
  rewrite H; simpl; auto.
  discriminate.
  Qed.

  Lemma mem_1 : In x m -> mem x m = true.
  Proof.
  unfold In, MapsTo, mem.
  destruct (find x m); auto.
  destruct 1; discriminate.
  Qed.

  Lemma mem_2 : forall m x, mem x m = true -> In x m. 
  Proof.
  unfold In, MapsTo, mem.
  intros.
  destruct (find x0 m0); auto; try discriminate.
  exists a; auto.
  Qed.

  Lemma add_1 : E.eq x y -> MapsTo y e (add x e m).
  Proof.
  unfold MapsTo, find, add.
  intro H; rewrite H; clear H.
  rewrite MapPut_semantics.
  rewrite Neqb_correct; auto.
  Qed.

  Lemma add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof.
  unfold MapsTo, find, add.
  intros.
  rewrite MapPut_semantics.
  rewrite H0.
  generalize (Neqb_complete x y).
  destruct (Neqb x y); auto.
  intros.
  elim H; auto.
  apply H1; auto.
  Qed.

  Lemma add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof.
  unfold MapsTo, find, add.
  rewrite MapPut_semantics.
  intro H.
  generalize (Neqb_complete x y).
  destruct (Neqb x y); auto.
  intros; elim H; auto.
  apply H0; auto.
  Qed.

  Lemma remove_1 : E.eq x y -> ~ In y (remove x m).
  Proof. 
  unfold In, MapsTo, find, remove.
  rewrite MapRemove_semantics.
  intro H.
  rewrite H; rewrite Neqb_correct.
  red; destruct 1; discriminate.
  Qed.

  Lemma remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof.
  unfold MapsTo, find, remove.
  rewrite MapRemove_semantics.
  intros.
  rewrite H0.
  generalize (Neqb_complete x y).
  destruct (Neqb x y); auto.
  intros; elim H; apply H1; auto.
  Qed.

  Lemma remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
  Proof. 
  unfold MapsTo, find, remove.
  rewrite MapRemove_semantics.
  destruct (Neqb x y); intros; auto.
  discriminate.
  Qed.

  Lemma alist_sorted_sort : forall l, alist_sorted A l=true -> sort lt_key l.
  Proof.
  induction l.
  auto.
  simpl.
  destruct a.
  destruct l.
  auto.
  destruct p.
  intros; destruct (andb_prop _ _ H); auto.
  Qed.

  Lemma elements_3 : sort lt_key (elements m). 
  Proof.
  unfold elements.
  apply alist_sorted_sort.
  apply alist_of_Map_sorts.
  Qed.
  
  Lemma elements_1 : 
     MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
  Proof.
  unfold MapsTo, find, elements.
  rewrite InA_alt.
  intro H.
  exists (x,e).
  split.
  red; simpl; unfold E.eq; auto.
  rewrite alist_of_Map_semantics in H.
  generalize H.
  set (l:=alist_of_Map A m); clearbody l; clear.
  induction l; simpl; auto.
  intro; discriminate.
  destruct a; simpl; auto.
  generalize (Neqb_complete a x).
  destruct (Neqb a x); auto.
  left.
  injection H0; auto.
  intros; f_equal; auto.
  Qed.

  Lemma elements_2 : 
     InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
  Proof.
  generalize elements_3.
  unfold MapsTo, find, elements.
  rewrite InA_alt.
  intros H ((e0,a),(H0,H1)).
  red in H0; simpl in H0; unfold E.eq in H0; destruct H0; subst.
  rewrite alist_of_Map_semantics.
  generalize H H1; clear H H1.
  set (l:=alist_of_Map A m); clearbody l; clear.
  induction l; simpl; auto.
  intro; contradiction.
  intros.
  destruct a0; simpl.
  inversion H1. 
  injection H0; intros; subst.
  rewrite Neqb_correct; auto.
  assert (InA eq_key (e0,a) l).
  rewrite InA_alt.
  exists (e0,a); split; auto.
  red; simpl; auto; red; auto.
  generalize (PE.Sort_In_cons_1 H H2).
  unfold PE.ltk; simpl.
  intros H3; generalize (E.lt_not_eq H3).
  generalize (Neqb_complete a0 e0).
  destruct (Neqb a0 e0); auto.
  destruct 2.
  apply H4; auto.
  inversion H; auto.
  Qed.

  Definition Equal cmp m m' := 
         (forall k, In k m <-> In k m') /\ 
         (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).  


  (** TO BE DEFINED AND PROVED LATER ... AXIOMS FOR NOW *)

  Parameter fold : forall (B:Set), (key -> A -> B -> B) -> t A -> B -> B.

  Parameter fold_1 :
	forall (B:Set) (i : B) (f : key -> A -> B -> B),
        fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.

  Parameter equal : (A -> A -> bool) -> t A -> t A -> bool.

  Variable cmp : A -> A -> bool. 

  Parameter equal_1 : Equal cmp m m' -> equal cmp m m' = true. 
  Parameter equal_2 : equal cmp m m' = true -> Equal cmp m m'.

  End Spec.

  Variable B C : Set.

  Parameter mapi : (N -> A -> B) -> t A -> t B.

  Parameter map : (A -> B) -> t A -> t B.

  Parameter map2 : (option A -> option B -> option C) -> t A -> t B ->  t C.

  End A.

  Parameter map_1 : forall (elt elt':Set)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
        MapsTo x e m -> MapsTo x (f e) (map f m).
  Parameter map_2 : forall (elt elt':Set)(m: t elt)(x:key)(f:elt->elt'), 
        In x (map f m) -> In x m.
  Parameter mapi_1 : forall (elt elt':Set)(m: t elt)(x:key)(e:elt)
        (f:key->elt->elt'), MapsTo x e m -> 
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
  Parameter mapi_2 : forall (elt elt':Set)(m: t elt)(x:key)
        (f:key->elt->elt'), In x (mapi f m) -> In x m.
  Parameter map2_1 : forall (elt elt' elt'':Set)(m: t elt)(m': t elt')
	(x:key)(f:option elt->option elt'->option elt''), 
	In x m \/ In x m' -> 
        find x (map2 f m m') = f (find x m) (find x m').       
  Parameter map2_2 : forall (elt elt' elt'':Set)(m: t elt)(m': t elt')
	(x:key)(f:option elt->option elt'->option elt''), 
        In x (map2 f m m') -> In x m \/ In x m'.

End MapIntMap.

