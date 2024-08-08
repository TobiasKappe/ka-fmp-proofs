Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.micromega.Lia.

Require Import KA.Booleans.

Local Open Scope program_scope.

Ltac clean_exists :=
  repeat match goal with
         | H: existT ?P ?p _ = existT ?P ?p _ |- _ =>
           apply Eqdep.EqdepTheory.inj_pair2 in H
         end;
  subst.

Ltac fold_compose :=
  match goal with
  | H: context [ fun x => ?y (?z x) ] |- _ =>
    replace (fun x => y (z x)) with (y ∘ z) in H by reflexivity
  | |- context [ fun x => ?y (?z x) ] =>
    replace (fun x => y (z x)) with (y ∘ z) by reflexivity
  end.

Ltac handle_lists :=
  repeat rewrite ?in_map_iff, ?in_prod_iff, ?in_app_iff, ?filter_In;
  repeat rewrite ?map_map, ?map_app in *;
  try match goal with
  | H: In _ (map _ _) |- _ =>
    apply in_map_iff in H;
    destruct H as [? [? ?]]
  | H: In _ (list_prod _ _) |- _ =>
    apply in_prod_iff in H;
    destruct H as [? ?]
  | H: In _ (_ ++ _) |- _ =>
    apply in_app_iff in H
  | H:  In _ (filter _ _) |- _ =>
    apply filter_In in H
  | H: map _ _ = _ ++ _ |- _ =>
    apply map_eq_app in H;
    destruct H as [? [? [? [? ?]]]]
  | H: map _ _ = _ :: _ |- _ =>
    apply map_eq_cons in H;
    destruct H as [? [? [? [? ?]]]]
  | H: map _ _ = nil |- _ =>
    apply map_eq_nil in H
  end.

Ltac propify :=
  try setoid_rewrite eq_iff_eq_true;
  repeat (
    try setoid_rewrite orb_true_iff;
    try setoid_rewrite orb_false_iff;
    try setoid_rewrite andb_true_iff;
    try setoid_rewrite andb_false_iff;
    try setoid_rewrite eqb_true_iff;
    try setoid_rewrite eqb_false_iff;
    try setoid_rewrite negb_false_iff;
    try setoid_rewrite disj_true;
    try setoid_rewrite disj_false;
    try setoid_rewrite conj_true;
    rewrite ?orb_true_iff, ?orb_false_iff,
            ?andb_true_iff, ?andb_false_iff,
            ?eqb_true_iff, ?eqb_false_iff,
            ?negb_false_iff,
            ?disj_true, ?disj_false, ?conj_true
            in *
  ).

Lemma function_instantiation {X Y: Type} (f g: X -> Y) (x: X):
  f = g -> f x = g x
.
Proof.
  intros; now subst.
Qed.

Section ListAppend.
  Lemma app_match_left
    {X: Type}
    (l1 l2 l3 l4: list X)
  :
    length l1 = length l3 ->
    l1 ++ l2 = l3 ++ l4 ->
    l1 = l3
  .
  Proof.
    intros.
    apply (f_equal (firstn (length l1))) in H0.
    repeat rewrite firstn_app in H0.
    replace (length l1 - length l1) with 0%nat in H0 by lia.
    replace (length l1 - length l3) with 0%nat in H0 by lia.
    repeat rewrite firstn_O in H0.
    repeat rewrite app_nil_r in H0.
    rewrite H in H0 at 2.
    now repeat rewrite firstn_all in H0.
  Qed.

  Lemma app_match_right
    {X: Type}
    (l1 l2 l3 l4: list X)
  :
    length l1 = length l3 ->
    l1 ++ l2 = l3 ++ l4 ->
    l2 = l4
  .
  Proof.
    intros.
    apply (f_equal (skipn (length l1))) in H0.
    repeat rewrite skipn_app in H0.
    replace (length l1 - length l1) with 0%nat in H0 by lia.
    replace (length l1 - length l3) with 0%nat in H0 by lia.
    rewrite H in H0 at 2.
    repeat rewrite skipn_all in H0.
    repeat rewrite skipn_O in H0.
    now repeat rewrite app_nil_l in H0.
  Qed.
End ListAppend.
