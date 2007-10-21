Require Import FSets.

(** no map function over sets, so let's define one (at least for f:E.t->E.t) *)

Module MapFunction (M:S).
 Module MP:=Properties M.
 Import MP M.
 Section Map.

 Variable f : elt -> elt.

 Definition map s := fold (fun x s => add (f x) s) s empty.

 Hypothesis f_comp : forall x y, E.eq x y -> E.eq (f x) (f y).

 Lemma map_In_aux : forall s a i, 
   In a (fold (fun x s => add (f x) s) s i) <-> 
   In a i \/ exists b, In b s /\ E.eq (f b) a.
 Proof.
 induction s using set_induction; intros.
 generalize (@MP.fold_1 s t Equal).
 intros H'.
 unfold Equal at 2 in H'; rewrite H'; auto.
 constructor; [apply eq_refl|apply eq_sym|eapply eq_trans]; eauto.
 intuition.
 destruct H1 as (b,(H1,H2)).
 elim (H b); auto.

 generalize (@MP.fold_2 s1 s2 x t Equal).
 intros H'.
 unfold Equal at 4 in H'; rewrite H'; clear H'; auto.
 constructor; [apply eq_refl|apply eq_sym|eapply eq_trans]; eauto.
 red; intros.
 apply FM.add_m; auto.
 red; intros.
 apply add_add.
 rewrite FM.add_iff.
 rewrite IHs1.
 intuition.
 right; exists x; split; auto.
 red in H0; rewrite H0; auto.
 destruct H1 as (b,(H1,H2)).
 right; exists b; split; auto.
 red in H0; rewrite H0; auto.
 destruct H2 as (b,(H2,H3)).
 destruct (FM.ME.eq_dec x b).
 left.
 apply E.eq_trans with (f b); auto.
 right; right; exists b; split; auto.
 generalize (H0 b).
 intuition.
Qed.

Lemma map_In : forall s a, 
 In a (map s) <-> exists b, In b s /\ E.eq (f b) a.
Proof.
intros.
unfold map; rewrite map_In_aux; auto.
intuition.
rewrite FM.empty_iff in H0; intuition.
Qed.

Lemma map_cardinal_aux : forall s i, 
 (forall x y, In x s -> In y s -> E.eq (f x) (f y) -> E.eq x y) ->
 (forall x, In x s -> ~In (f x) i) -> 
 cardinal (fold (fun x s => add (f x) s) s i) = cardinal i + cardinal s.
Proof.
 rename f_comp into H.
 assert (Setoid_Theory t Equal) by 
   (constructor; [apply eq_refl|apply eq_sym|eapply eq_trans]; eauto).
 set (F:=fun (x:elt) (s:t) => add (f x) s).

 induction s using set_induction; intros.
 generalize (MP.fold_1 H0 i F H1); intros.
 rewrite (Equal_cardinal H4).
 rewrite (MP.cardinal_1 H1); auto with arith.

 generalize (@MP.fold_2 s1 s2 x _ _ H0 i F); intros.
 assert (compat_op E.eq Equal F).
  red; unfold F; intros.
  apply FM.add_m; auto.
 assert (transpose Equal F).
  red; unfold F; intros.
  apply add_add; auto.
 rewrite (Equal_cardinal (H5 H6 H7 H1 H2)).
 unfold F at 1.
 rewrite add_cardinal_2.
 rewrite IHs1.
 rewrite (cardinal_2 H1 H2); auto with arith.
 intros.
 apply H3; auto.
 rewrite (H2 x0).
 destruct (ME.eq_dec x x0); intuition.
 rewrite (H2 y).
 destruct (ME.eq_dec x y); intuition.
 intros.
 apply H4.
 rewrite (H2 x0).
 destruct (ME.eq_dec x x0); intuition.
 red; intros.
 unfold F in H8; rewrite map_In_aux in H8.
 destruct H8.
 elim (H4 x); auto.
 rewrite (H2 x); auto.
 destruct H8 as (b,(H8,H9)).
 assert (E.eq b x).
  apply H3; auto.
  rewrite (H2 b).
  destruct (ME.eq_dec x b); intuition.
  rewrite (H2 x); auto.
 elim H1.
 rewrite <- (FM.In_eq_iff s1 H10); auto.
Qed.

Lemma map_cardinal : forall s, 
 (forall x y, In x s -> In y s -> E.eq (f x) (f y) -> E.eq x y) ->
 cardinal (map s) = cardinal s.
Proof.
 intros; unfold map; rewrite map_cardinal_aux; auto with set.
 rewrite empty_cardinal; auto with set.
Qed.

End Map.

Lemma map_filter : forall f g s, 
 compat_bool E.eq f -> 
 (forall x y, E.eq x y -> E.eq (g x) (g y)) ->
 filter f (map g s) [=] map g (filter (fun x => f (g x)) s).
Proof.
intros.
red; intros.
rewrite FM.filter_iff; auto.
rewrite map_In; auto.
rewrite map_In; auto.
intuition.
destruct H2 as (b,(H2,H4)).
exists b; split; auto.
rewrite FM.filter_iff; auto.
split; auto.
rewrite <- H3; auto.
destruct H1 as (b,(H2,H4)).
exists b; split; auto.
rewrite FM.filter_iff in H2; intuition.
destruct H1 as (b,(H2,H4)).
rewrite FM.filter_iff in H2; intuition.
rewrite <- H3; auto.
Qed.

End MapFunction.
