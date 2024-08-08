Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Program.Basics.

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
