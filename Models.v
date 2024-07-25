Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.micromega.Lia.

Require Import KA.Finite.
Require Import KA.Scope.
Require Import KA.Terms.
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
    | 0%nat => monoid_relational_unit
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
      + now exists 0%nat.
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

Section Sums.
  Lemma kleene_mutual_containment
    {X: Type}
    (K: kleene_algebra X)
    (x1 x2: X)
  :
    kleene_plus K x1 x2 = x2 ->
    kleene_plus K x2 x1 = x1 ->
    x1 = x2
  .
  Proof.
    intros.
    rewrite <- H.
    rewrite <- H0 at 1.
    now rewrite kleene_plus_commute.
  Qed.

  Lemma kleene_plus_split
    {X: Type}
    (K: kleene_algebra X)
    (x1 x2 x3: X)
  :
    kleene_plus K x1 x3 = x3 ->
    kleene_plus K x2 x3 = x3 ->
    kleene_plus K (kleene_plus K x1 x2) x3 = x3
  .
  Proof.
    intros.
    rewrite kleene_plus_assoc.
    now rewrite H0.
  Qed.

  Fixpoint kleene_sum
    {X: Type}
    (K: kleene_algebra X)
    (l: list X)
  :=
    match l with
    | nil => kleene_zero K
    | x :: l => kleene_plus K x (kleene_sum K l)
    end
  .

  Lemma kleene_sum_below_all
    {X: Type}
    (K: kleene_algebra X)
    (l: list X)
    (x: X)
  :
    (forall x', In x' l -> kleene_plus K x' x = x) ->
    kleene_plus K (kleene_sum K l) x = x
  .
  Proof.
    intros.
    induction l.
    - simpl; now rewrite kleene_plus_commute, kleene_plus_unit.
    - simpl.
      rewrite kleene_plus_assoc.
      rewrite IHl; intuition.
  Qed.

  Lemma kleene_sum_member
    {X: Type}
    (K: kleene_algebra X)
    (l: list X)
    (x: X)
  :
    In x l ->
    kleene_plus K x (kleene_sum K l) = kleene_sum K l
  .
  Proof.
    intros.
    induction l.
    - destruct H.
    - simpl.
      rewrite <- kleene_plus_assoc.
      destruct H; subst.
      + now rewrite kleene_plus_idempotent.
      + rewrite kleene_plus_commute with (x1 := x).
        now rewrite kleene_plus_assoc, IHl.
  Qed.

  Lemma kleene_sum_distributes_right
    {X: Type}
    (K: kleene_algebra X)
    (l: list X)
    (x: X)
  :
    kleene_multiply K (kleene_sum K l) x =
    kleene_sum K (map (fun x' => kleene_multiply K x' x) l)
  .
  Proof.
    induction l.
    - apply kleene_multiply_zero_left.
    - simpl.
      rewrite kleene_distribute_right.
      now rewrite <- IHl.
  Qed.

  Lemma kleene_sum_distributes_left
    {X: Type}
    (K: kleene_algebra X)
    (l: list X)
    (x: X)
  :
    kleene_multiply K x (kleene_sum K l) =
    kleene_sum K (map (kleene_multiply K x) l)
  .
  Proof.
    induction l.
    - apply kleene_multiply_zero_right.
    - simpl.
      rewrite kleene_distribute_left.
      now rewrite <- IHl.
  Qed.
End Sums.

Section Powers.
  Fixpoint kleene_power
    {X: Type}
    (K: kleene_algebra X)
    (x: X)
    (n: nat)
  :
    X
  :=
    match n with
    | 0%nat => kleene_unit K
    | S n => kleene_multiply K x (kleene_power K x n)
    end
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

  Definition kleene_star_sum_powers_finite
    {X: Type}
    `{Finite X}
    (K: kleene_algebra X)
    (x: X)
  :=
    kleene_sum K (map (kleene_power K x) (seq 0 (length finite_enum)))
  .

  Lemma kleene_power_sum
    {X: Type}
    (K: kleene_algebra X)
    (x: X)
    (n m: nat)
  :
    kleene_multiply K (kleene_power K x n) (kleene_power K x m) =
    kleene_power K x (n + m)
  .
  Proof.
    induction n; simpl.
    - unfold kleene_multiply, kleene_unit.
      now rewrite monoid_unit_right.
    - unfold kleene_multiply in *.
      rewrite monoid_compose_assoc.
      now rewrite IHn.
  Qed.

  Lemma kleene_power_reduce
    {X: Type}
    (K: kleene_algebra X)
    (x: X)
    (n m k: nat)
  :
    n <= m <= k ->
    kleene_power K x n = kleene_power K x m ->
    kleene_power K x k = kleene_power K x (k - (m - n))
  .
  Proof.
    intros.
    replace (k - (m - n)) with (k - m + n)%nat by lia.
    rewrite <- kleene_power_sum.
    rewrite H0, kleene_power_sum.
    f_equal; lia.
  Qed.

  Lemma kleene_power_finite
    {X: Type}
    `{Finite X}
    (K: kleene_algebra X)
    (x: X)
  :
    In (kleene_power K x (length finite_enum))
       (map (kleene_power K x) (seq 0 (length finite_enum)))
  .
  Proof.
    apply in_map_iff.
    pose proof (pigeonhole_principle (map (kleene_power K x)
                                          (seq 0 (S (length finite_enum))))).
    destruct H0.
    - rewrite map_length, seq_length; lia.
    - destruct H0 as [l1 [l2 [xr ?]]].
      apply map_eq_app in H0.
      destruct H0 as [l1' [l2' [? [? ?]]]].
      apply map_eq_app in H2.
      destruct H2 as [l3' [l4' [? [? ?]]]].
      apply map_eq_app in H4.
      destruct H4 as [l5' [l6' [? [? ?]]]].
      apply map_eq_app in H6.
      destruct H6 as [l7' [l8' [? [? ?]]]].
      apply map_eq_cons in H3.
      destruct H3 as [n0 [? [? [? ?]]]].
      apply map_eq_cons in H7.
      destruct H7 as [n1 [? [? [? ?]]]].
      apply map_eq_nil in H12, H10.
      subst.
      assert (0 <= n1 < S (length finite_enum)).
      + replace (S (length finite_enum)) with (0 + S (length finite_enum))%nat by lia.
        rewrite <- in_seq.
        rewrite H0.
        apply in_or_app; right.
        apply in_or_app; right.
        apply in_or_app; right.
        simpl; now left.
      + rewrite app_assoc in H0.
        eapply seq_order with (n := n0) (m := n1) in H0.
        * exists (length finite_enum - (n1 - n0)); split.
          -- erewrite <- kleene_power_reduce; try lia; auto.
          -- apply in_seq; lia.
        * apply in_or_app; right.
          simpl; now left.
        * apply in_or_app; right.
          apply in_or_app; left.
          simpl; now left.
  Qed.

  Lemma kleene_star_sum_powers_overlap
    {X: Type}
    `{Finite X}
    (K: kleene_algebra X)
    (x: X)
  :
    kleene_plus K (kleene_multiply K x (kleene_star_sum_powers_finite K x))
                  (kleene_star_sum_powers_finite K x) =
    kleene_star_sum_powers_finite K x
  .
  Proof.
    unfold kleene_star_sum_powers_finite.
    rewrite kleene_sum_distributes_left.
    apply kleene_sum_below_all; intros.
    apply in_map_iff in H0.
    destruct H0 as [x'' [? ?]]; subst.
    apply in_map_iff in H1.
    destruct H1 as [n [? ?]]; subst.
    apply in_seq in H1; simpl in H1.
    destruct H1 as [_ ?].
    apply kleene_sum_member.
    replace (kleene_multiply K x (kleene_power K x n))
      with (kleene_power K x (S n)) by reflexivity.
    destruct (Compare_dec.le_gt_dec (length finite_enum) (S n)).
    - assert (S n = length finite_enum) by lia.
      rewrite H1; clear H0 l H1.
      apply kleene_power_finite.
    - apply in_map_iff.
      exists (S n); intuition.
      apply in_seq; lia.
  Qed.

  Lemma kleene_star_sum_powers_unit
    {X: Type}
    `{Finite X}
    (K: kleene_algebra X)
    (x: X)
  :
    kleene_plus K (kleene_unit K)
                  (kleene_star_sum_powers_finite K x) =
    kleene_star_sum_powers_finite K x
  .
  Proof.
    unfold kleene_star_sum_powers_finite.
    eapply kleene_sum_member.
    apply in_map_iff.
    exists 0%nat; intuition.
    apply in_seq.
    enough (length finite_enum <> 0%nat) by lia.
    assert (In (kleene_unit K) finite_enum) by (apply finite_cover).
    intro; apply length_zero_iff_nil in H1.
    rewrite H1 in H0.
    now apply in_nil in H0.
  Qed.

  Lemma kleene_star_finite
    {X: Type}
    `{Finite X}
    (K: kleene_algebra X)
    (x: X)
  :
    kleene_star K x = kleene_star_sum_powers_finite K x
  .
  Proof.
    eapply kleene_mutual_containment with (K := K).
    - rewrite <- monoid_unit_left
        with (x := kleene_star K x) (m := kleene_monoid K).
      replace (monoid_compose (kleene_monoid K))
        with (kleene_multiply K) by reflexivity.
      apply kleene_star_fixpoint.
      apply kleene_plus_split.
      + apply kleene_star_sum_powers_overlap.
      + apply kleene_star_sum_powers_unit.
    - apply kleene_sum_below_all; intros.
      apply in_map_iff in H0.
      destruct H0 as [n [? ?]]; subst.
      induction n.
      + simpl.
        rewrite <- kleene_star_unroll.
        rewrite <- kleene_plus_assoc.
        now rewrite kleene_plus_idempotent.
      + simpl.
        rewrite <- kleene_star_unroll.
        rewrite kleene_plus_commute.
        rewrite kleene_plus_assoc.
        rewrite <- kleene_distribute_left.
        rewrite kleene_plus_commute with (x1 := kleene_star K x).
        rewrite IHn; auto.
        apply in_seq.
        apply in_seq in H1.
        lia.
  Qed.
End Powers.

Section StarContinuity.
  Definition kleene_star_continuous
    {X: Type}
    (K: kleene_algebra X)
  :=
    forall x y u v,
      (forall n, kleene_plus K (kleene_multiply K u (kleene_multiply K (kleene_power K x n) v)) y = y) ->
      kleene_plus K (kleene_multiply K u (kleene_multiply K (kleene_star K x) v)) y = y
  .

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

  Lemma kleene_finite_star_continuous
    {X: Type}
    `{Finite X}
    (K: kleene_algebra X)
  :
    kleene_star_continuous K
  .
  Proof.
    unfold kleene_star_continuous; intros.
    rewrite kleene_star_finite.
    unfold kleene_star_sum_powers_finite.
    rewrite kleene_sum_distributes_right.
    rewrite kleene_sum_distributes_left.
    apply kleene_sum_below_all; intros.
    apply in_map_iff in H1.
    destruct H1 as [x1 [? ?]]; subst.
    apply in_map_iff in H2.
    destruct H2 as [x2 [? ?]]; subst.
    apply in_map_iff in H2.
    destruct H2 as [x3 [? ?]]; subst.
    apply H0.
  Qed.
End StarContinuity.

Section EquationalTheories.
  Definition kleene_satisfies
    {A X: Type}
    (K: kleene_algebra X)
    (t1 t2: term A)
  :=
    forall (h: A -> X),
      kleene_interp K h t1 = kleene_interp K h t2
  .

  Definition kleene_satisfies_class
    {A: Type}
    (Ks: forall {X: Type}, kleene_algebra X -> Prop)
    (t1 t2: term A)
  :=
    forall {X: Type} (K: kleene_algebra X),
      Ks K ->
      kleene_satisfies K t1 t2
  .

  Variant kleene_relational:
    forall {X: Type}, kleene_algebra X -> Prop :=
  | KleeneRelational:
      forall (X: Type), kleene_relational (kleene_algebra_relational X)
  .

  Variant kleene_finite:
    forall {X: Type}, kleene_algebra X -> Prop :=
  | KleeneFinite:
      forall (X: Type) (K: kleene_algebra X),
        Finite X -> kleene_finite K
  .

  Variant kleene_finite_relational:
    forall {X: Type}, kleene_algebra X -> Prop :=
  | KleeneFiniteRelational:
      forall (X: Type),
        Finite X ->
        kleene_finite_relational (kleene_algebra_relational X)
  .

  Lemma kleene_class_contained_preserves
    (Ks Ks': forall {X: Type}, kleene_algebra X -> Prop)
  :
    (forall (X: Type) (K: kleene_algebra X), Ks' K -> Ks K) ->
    forall (A: Type) (t1 t2: term A),
      kleene_satisfies_class (@Ks) t1 t2 ->
      kleene_satisfies_class (@Ks') t1 t2
  .
  Proof.
    unfold kleene_satisfies_class, kleene_satisfies; firstorder.
  Qed.

  Lemma kleene_preserve_equation_star_continuous_relational
    {A X: Type}
    (K: kleene_algebra X)
    (t1 t2: term A)
  :
    kleene_satisfies_class (@kleene_star_continuous) t1 t2 ->
    kleene_satisfies_class (@kleene_relational) t1 t2
  .
  Proof.
    apply kleene_class_contained_preserves; intros.
    destruct H; apply kleene_relational_star_continuous.
  Qed.

  Lemma kleene_preserve_equation_star_continuous_finite
    {A X: Type}
    (K: kleene_algebra X)
    (t1 t2: term A)
  :
    kleene_satisfies_class (@kleene_star_continuous) t1 t2 ->
    kleene_satisfies_class (@kleene_finite) t1 t2
  .
  Proof.
    apply kleene_class_contained_preserves; intros.
    destruct H; apply kleene_finite_star_continuous.
  Qed.
End EquationalTheories.
