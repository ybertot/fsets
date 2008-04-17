Require Import FSets.

(** * A map function for FSet *)

(** The FSet interface provides no map function over sets, 
    so let's define one. *)

(** The most general case: two set structures M and M', 
    one as source and the other one as destination. *)

Module MapFunctionGen (M:S)(M':S).
 Module PM:=Properties M.
 Module PM':=Properties M'.
 Module E:=M.E.
 Module E':=M'.E.
 Module FM := PM.FM.
 Module FM' := PM'.FM.
 Section Map.

 Variable f : M.elt -> M'.elt.

 Definition map s := M.fold (fun x s => M'.add (f x) s) s M'.empty.

 Hypothesis f_comp : forall x y, E.eq x y -> E'.eq (f x) (f y).

 Lemma map_In_aux : forall s a i, 
   M'.In a (M.fold (fun x s => M'.add (f x) s) s i) <-> 
   M'.In a i \/ exists b, M.In b s /\ E'.eq (f b) a.
 Proof.
 set (F := fun x s => M'.add (f x) s).
 assert (ST := FM'.Equal_ST : Setoid_Theory _ M'.Equal).
 assert (C:compat_op E.eq M'.Equal F) by (red; intros; apply FM'.add_m; auto).
 assert (T:transpose M'.Equal F) by (red; intros; apply PM'.add_add; auto).

 induction s as [ s EM | s1 s2 IHs1 x NI AD] using PM.set_induction; intros.
 rewrite (PM.fold_1 ST (s:=s)); firstorder.
 rewrite (PM.fold_2 ST i C T NI AD); auto.
 unfold F; rewrite FM'.add_iff, IHs1; clear ST C T IHs1.
 assert (M.In x s2) by (rewrite (AD x); auto).
 assert (M.Subset s1 s2) by (intros y Hy; rewrite (AD y); auto).
 intuition.
 right; exists x; auto.
 right; destruct H1 as {b,?,?}; exists b; auto.
 destruct H2 as {b,H1,H2}; rewrite (AD b) in H1; destruct H1.
 left; eauto.
 right; right; exists b; auto.
Qed.

Lemma map_In : forall s a, 
 M'.In a (map s) <-> exists b, M.In b s /\ E'.eq (f b) a.
Proof.
intros; unfold map; rewrite map_In_aux, FM'.empty_iff; intuition.
Qed.

Lemma map_cardinal_aux : forall s i, 
 (forall x y, M.In x s -> M.In y s -> E'.eq (f x) (f y) -> E.eq x y) ->
 (forall x, M.In x s -> ~M'.In (f x) i) -> 
 M'.cardinal (M.fold (fun x s => M'.add (f x) s) s i) = 
 M'.cardinal i + M.cardinal s.
Proof.
 set (F := fun x s => M'.add (f x) s).
 assert (ST := FM'.Equal_ST : Setoid_Theory _ M'.Equal).
 assert (C:compat_op E.eq M'.Equal F) by (red; intros; apply FM'.add_m; auto).
 assert (T:transpose M'.Equal F) by (red; intros; apply PM'.add_add; auto).

 induction s as [ s EM | s1 s2 IHs1 x NI AD] using PM.set_induction; intros.
 rewrite (PM.fold_1 ST (s:=s)), (PM.cardinal_1 EM); auto.
 rewrite (PM.fold_2 ST i C T NI AD); auto.
 assert (M.In x s2) by (rewrite (AD x); auto).
 assert (M.Subset s1 s2) by (intros y Hy; rewrite (AD y); auto).
 unfold F; rewrite PM'.add_cardinal_2, IHs1, (PM.cardinal_2 NI AD); auto.
 rewrite map_In_aux; red; destruct 1 as [ | {b,?,?} ].
 firstorder.
 rewrite <- (H b x) in NI; auto.
Qed.

Lemma map_cardinal : forall s, 
 (forall x y, M.In x s -> M.In y s -> E'.eq (f x) (f y) -> E.eq x y) ->
 M'.cardinal (map s) = M.cardinal s.
Proof.
 intros; unfold map; rewrite map_cardinal_aux; auto with set.
 rewrite PM'.empty_cardinal; auto with set.
Qed.

End Map.

Lemma map_filter : forall f g s, 
 compat_bool E'.eq f -> 
 (forall x y, E.eq x y -> E'.eq (g x) (g y)) ->
 M'.Equal (M'.filter f (map g s)) (map g (M.filter (fun x => f (g x)) s)).
Proof.
intros.
red; intros.
rewrite FM'.filter_iff, 2 map_In by auto.
split; [intros [(b,Hb) F] | intros (b,Hb)]; try split; try exists b; 
 try rewrite FM.filter_iff in *; intuition; eauto.
Qed.

End MapFunctionGen.

(* The particular (but common) situation: same source and destination M *)

Module MapFunction (M:S) := MapFunctionGen M M.
