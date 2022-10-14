Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Ltac clean_exists :=
  repeat match goal with
  | H: existT ?P ?p _ = existT ?P ?p _ |- _ =>
    apply Eqdep.EqdepTheory.inj_pair2 in H
         end;
  subst.

Lemma function_instantiation {X Y: Type} (f g: X -> Y) (x: X):
  f = g -> f x = g x
.
Proof.
  intros; now subst.
Qed.

Section ListAppend.
  Lemma map_app_lift {X Y: Type} (f: X -> Y) (lx: list X) (ly1 ly2: list Y):
    map f lx = ly1 ++ ly2 ->
    exists (lx1 lx2: list X),
      lx = lx1 ++ lx2 /\
      map f lx1 = ly1 /\
      map f lx2 = ly2
  .
  Proof.
    intros; revert lx H; induction ly1; intros.
    - rewrite app_nil_l in H.
      exists nil, lx.
      intuition.
    - destruct lx; simpl in H.
      + discriminate.
      + inversion H; subst.
        apply IHly1 in H2.
        destruct H2 as [lx1 [lx2 [? [? ?]]]].
        exists (x :: lx1), lx2; simpl.
        intuition congruence.
  Qed.

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
