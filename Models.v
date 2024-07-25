Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import KA.Finite.
Require Import KA.Scope.
Require Import KA.Structure.
Local Open Scope ka_scope.

Section RelationalModels.
  Definition monoid_relational_unit {X: Type} (x x': X) := x = x'.

  Definition monoid_relational_compose
    {X: Type}
    (R1 R2: X -> X -> Prop)
    (x x': X)
  :=
    exists x'',
      R1 x x'' /\
      R2 x'' x'
  .

  Fixpoint monoid_relational_repeat
    {X: Type}
    (R: X -> X -> Prop)
    (n: nat)
  :=
    match n with
    | 0 => monoid_relational_unit
    | S n => monoid_relational_compose R (monoid_relational_repeat R n)
    end
  .

  Program Definition monoid_relational (X: Type): monoid (X -> X -> Prop) := {|
    monoid_unit := monoid_relational_unit;
    monoid_compose := monoid_relational_compose;
  |}.
  Next Obligation.
    extensionality x; extensionality x'.
    apply propositional_extensionality.
    unfold monoid_relational_compose; firstorder.
  Qed.
  Next Obligation.
    extensionality x'; extensionality x''.
    apply propositional_extensionality.
    unfold monoid_relational_compose; firstorder.
    unfold monoid_relational_unit in H0; now subst.
  Qed.
  Next Obligation.
    extensionality x'; extensionality x''.
    apply propositional_extensionality.
    unfold monoid_relational_compose; firstorder.
    unfold monoid_relational_unit in H; now subst.
  Qed.

  Inductive kleene_relational_star
    {X: Type}
    (R: X -> X -> Prop)
  :
    X -> X -> Prop
  :=
  | KleeneRelationalStarBase:
      forall x, kleene_relational_star R x x
  | KleeneRelationalStarStep:
      forall x x' x'',
        R x x' ->
        kleene_relational_star R x' x'' ->
        kleene_relational_star R x x''
  .

  Definition kleene_relational_repeat
    {X: Type}
    (R: X -> X -> Prop)
    (x x': X)
  :
    Prop
  :=
    exists n, monoid_relational_repeat R n x x'
  .

  Lemma kleene_relational_star_is_repeat
    {X: Type}
    (R: X -> X -> Prop)
  :
    kleene_relational_star R = kleene_relational_repeat R
  .
  Proof.
    extensionality x; extensionality x'.
    apply propositional_extensionality; split; intros.
    - unfold kleene_relational_repeat.
      induction H.
      + now exists 0.
      + destruct IHkleene_relational_star as [n ?].
        now exists (S n), x'.
    - destruct H as [n ?].
      revert x x' H; induction n; intros.
      + simpl in H.
        unfold monoid_relational_unit in H; subst.
        apply KleeneRelationalStarBase.
      + destruct H as [? [? ?]].
        eapply KleeneRelationalStarStep; intuition.
  Qed.

  Definition kleene_relational_plus
    {X: Type}
    (R1 R2: X -> X -> Prop)
    (x x': X)
  :=
    R1 x x' \/ R2 x x'
  .

  Lemma kleene_relational_plus_containment
    {X: Type}
    (R1 R2: X -> X -> Prop)
  :
    (forall x x', R1 x x' -> R2 x x') <->
    kleene_relational_plus R1 R2 = R2
  .
  Proof.
    split; intros.
    - unfold kleene_relational_plus.
      extensionality x; extensionality x'.
      apply propositional_extensionality.
      firstorder.
    - rewrite <- H.
      unfold kleene_relational_plus.
      intuition.
  Qed.

  Definition kleene_relational_zero
    {X: Type}
    (x x': X)
  :=
    False
  .

  Program Definition kleene_algebra_relational (X: Type) := {|
    kleene_monoid := monoid_relational X;
    kleene_star := kleene_relational_star;
    kleene_plus := kleene_relational_plus;
    kleene_zero := kleene_relational_zero;
  |}.
  Next Obligation.
    extensionality x; extensionality x'.
    apply propositional_extensionality.
    unfold kleene_relational_plus; intuition.
  Qed.
  Next Obligation.
    extensionality x'; extensionality x''.
    apply propositional_extensionality.
    unfold kleene_relational_plus, kleene_relational_zero; intuition.
  Qed.
  Next Obligation.
    extensionality x'; extensionality x''.
    apply propositional_extensionality.
    unfold kleene_relational_plus; intuition.
  Qed.
  Next Obligation.
    extensionality x'; extensionality x''.
    apply propositional_extensionality.
    unfold kleene_relational_plus; intuition.
  Qed.
  Next Obligation.
    extensionality x'; extensionality x''.
    apply propositional_extensionality.
    unfold monoid_relational_compose, kleene_relational_zero; firstorder.
  Qed.
  Next Obligation.
    extensionality x'; extensionality x''.
    apply propositional_extensionality.
    unfold monoid_relational_compose, kleene_relational_zero; firstorder.
  Qed.
  Next Obligation.
    extensionality x'; extensionality x''.
    apply propositional_extensionality.
    unfold monoid_relational_compose, kleene_relational_plus; firstorder.
  Qed.
  Next Obligation.
    extensionality x'; extensionality x''.
    apply propositional_extensionality.
    unfold monoid_relational_compose, kleene_relational_plus; firstorder.
  Qed.
  Next Obligation.
    extensionality x'; extensionality x''.
    apply propositional_extensionality.
    split; intros.
    - unfold kleene_relational_plus in H; destruct H.
      + unfold monoid_relational_unit in H; subst.
        apply KleeneRelationalStarBase.
      + unfold monoid_relational_compose in H.
        destruct H as [x''' [? ?]].
        eapply KleeneRelationalStarStep; eauto.
    - induction H.
      + unfold kleene_relational_plus; now left.
      + unfold kleene_relational_plus; right.
        unfold monoid_relational_compose.
        exists x'; intuition.
  Qed.
  Next Obligation.
    apply kleene_relational_plus_containment; intros.
    rewrite <- kleene_relational_plus_containment in H.
    unfold monoid_relational_compose in H0.
    destruct H0 as [? [? ?]].
    induction H0.
    - apply H; now right.
    - apply H; left.
      exists x'0.
      intuition.
  Qed.
End RelationalModels.

Section StarContinuity.
  Fixpoint kleene_power
    {X: Type}
    (K: kleene_algebra X)
    (x: X)
    (n: nat)
  :
    X
  :=
    match n with
    | 0 => kleene_unit K
    | S n => kleene_multiply K x (kleene_power K x n)
    end
  .

  Definition kleene_star_continuous
    {X: Type}
    (K: kleene_algebra X)
  :=
    forall x y u v,
      (forall n, kleene_plus K (kleene_compose K u (kleene_compose K (kleene_power K x n) v)) y = y) ->
      kleene_plus K (kleene_compose K u (kleene_compose K (kleene_star K x) v)) y = y
  .

  Lemma kleene_power_is_relational_repeat
    {X: Type}
    (R: X -> X -> Prop)
    (n: nat)
  :
    monoid_relational_repeat R n =
    kleene_power (kleene_algebra_relational X) R n
  .
  Proof.
    induction n; simpl.
    - reflexivity.
    - now rewrite IHn.
  Qed.

  Lemma kleene_relational_star_continuous (X: Type):
    kleene_star_continuous (kleene_algebra_relational X)
  .
  Proof.
    unfold kleene_star_continuous; intros R; intros.
    simpl kleene_star; rewrite kleene_relational_star_is_repeat.
    apply kleene_relational_plus_containment; intros.
    destruct H0 as [x1 [? [x2 [[n ?] ?]]]].
    rewrite <- (H n); left.
    repeat (eexists; intuition; eauto).
    now rewrite <- kleene_power_is_relational_repeat.
  Qed.
End StarContinuity.
