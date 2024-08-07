Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.micromega.Lia.
Require Import Coq.btauto.Btauto.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.

Require Import KA.Booleans.
Require Import KA.Finite.
Require Import KA.Scope.
Require Import KA.Terms.
Require Import KA.Vectors.
Require Import KA.Utilities.

Local Open Scope ka_scope.
Local Open Scope program_scope.

Section StructureDefinitions.
  Record monoid {X: Type} := {
    monoid_compose: X -> X -> X;
    monoid_unit: X;

    monoid_compose_assoc:
      forall (x1 x2 x3: X),
        monoid_compose (monoid_compose x1 x2) x3 =
        monoid_compose x1 (monoid_compose x2 x3);
    monoid_unit_left:
      forall (x: X),
      monoid_compose x monoid_unit = x;
    monoid_unit_right:
      forall (x: X),
      monoid_compose monoid_unit x = x;
  }.
  Arguments monoid X : clear implicits.

  Equations monoid_interp
    {X A: Type}
    (M: monoid X)
    (h: A -> X)
    (w: list A)
  :
    X
  := {
    monoid_interp M h nil := monoid_unit M;
    monoid_interp M h (a :: w) := monoid_compose M (h a) (monoid_interp M h w);
  }.

  Lemma monoid_interp_app
    {X A: Type}
    (M: monoid X)
    (h: A -> X)
    (w1 w2: list A)
  :
    monoid_interp M h (w1 ++ w2) =
    monoid_compose M (monoid_interp M h w1) (monoid_interp M h w2)
  .
  Proof.
    induction w1; simpl.
    - autorewrite with monoid_interp.
      now rewrite monoid_unit_right.
    - autorewrite with monoid_interp.
      rewrite monoid_compose_assoc.
      congruence.
  Qed.

  Record kleene_algebra {X: Type} := {
    kleene_monoid: monoid X;
    kleene_plus: X -> X -> X;
    kleene_star: X -> X;
    kleene_zero: X;

    kleene_unit := monoid_unit kleene_monoid;
    kleene_multiply := monoid_compose kleene_monoid;

    kleene_plus_assoc:
      forall (x1 x2 x3: X),
        kleene_plus (kleene_plus x1 x2) x3 =
        kleene_plus x1 (kleene_plus x2 x3);
    kleene_plus_unit:
      forall (x: X),
        kleene_plus x kleene_zero = x;
    kleene_plus_idempotent:
      forall (x: X),
        kleene_plus x x = x;
    kleene_plus_commute:
      forall (x1 x2: X),
        kleene_plus x1 x2 = kleene_plus x2 x1;
    kleene_multiply_zero_left:
      forall (x: X),
        kleene_multiply kleene_zero x = kleene_zero;
    kleene_multiply_zero_right:
      forall (x: X),
        kleene_multiply x kleene_zero = kleene_zero;
    kleene_multiply_unit_right :=
      monoid_unit_right kleene_monoid;
    kleene_multiply_unit_left :=
      monoid_unit_left kleene_monoid;
    kleene_distribute_left:
      forall (x1 x2 x3: X),
        kleene_multiply x1 (kleene_plus x2 x3) =
        kleene_plus (kleene_multiply x1 x2) (kleene_multiply x1 x3);
    kleene_distribute_right:
      forall (x1 x2 x3: X),
        kleene_multiply (kleene_plus x1 x2) x3 =
        kleene_plus (kleene_multiply x1 x3) (kleene_multiply x2 x3);
    kleene_star_unroll:
      forall (x: X),
        kleene_plus kleene_unit (kleene_multiply x (kleene_star x)) =
        kleene_star x;
    kleene_star_fixpoint:
      forall (x1 x2 x3: X),
        kleene_plus (kleene_plus (kleene_multiply x1 x2) x3) x2 = x2 ->
        kleene_plus (kleene_multiply (kleene_star x1) x3) x2 = x2
  }.
  Arguments kleene_algebra X : clear implicits.

  Equations kleene_interp
    {X A: Type}
    (K: kleene_algebra X)
    (f: A -> X)
    (t: term A)
  :
    X
  := {
    kleene_interp K f zero := kleene_zero K;
    kleene_interp K f one := kleene_unit K;
    kleene_interp K f (letter a) := f a;
    kleene_interp K f (t1 + t2) :=
      kleene_plus K (kleene_interp K f t1) (kleene_interp K f t2);
    kleene_interp K f (t1 ;; t2) :=
      kleene_multiply K (kleene_interp K f t1) (kleene_interp K f t2);
    kleene_interp K f (t*) :=
      kleene_star K (kleene_interp K f t)
  }.

  Lemma kleene_interp_sound
    {X A: Type}
    (K: kleene_algebra X)
    (f: A -> X)
    (t1 t2: term A)
  :
    t1 == t2 ->
    kleene_interp K f t1 = kleene_interp K f t2
  .
  Proof.
    intros; dependent induction H;
    autorewrite with kleene_interp in *;
    try congruence; try apply K.
    - now rewrite kleene_plus_assoc.
    - unfold kleene_multiply.
      now rewrite monoid_compose_assoc.
    - now rewrite kleene_distribute_left.
    - now rewrite kleene_distribute_right.
    - rewrite kleene_plus_commute.
      now rewrite kleene_star_unroll.
    - now apply kleene_star_fixpoint.
  Qed.
End StructureDefinitions.

Arguments monoid X : clear implicits.
Arguments kleene_algebra X : clear implicits.

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

Section FiniteRelationalModels.
  Program Definition monoid_finite_relational
    (X: Type)
    `{Finite X}
  :
    monoid (X -> X -> bool)
  := {|
    monoid_compose := matrix_product_bool;
    monoid_unit := finite_eqb;
  |}.
  Next Obligation.
    apply matrix_product_bool_associative.
  Qed.
  Next Obligation.
    apply matrix_product_bool_unit_right.
  Qed.
  Next Obligation.
    apply matrix_product_bool_unit_left.
  Qed.

  Definition matrix_plus
    {X: Type}
    (R1 R2: X -> X -> bool)
    (x1 x2: X)
  :=
    orb (R1 x1 x2) (R2 x1 x2)
  .

  Lemma matrix_plus_commute
    {X: Type}
    (R1 R2: X -> X -> bool)
  :
    matrix_plus R1 R2 =
    matrix_plus R2 R1
  .
  Proof.
    extensionality x1; extensionality x2.
    unfold matrix_plus; btauto.
  Qed.

  Definition matrix_empty
    {X: Type}
    (x1 x2: X)
  :=
    false
  .

  Global Program Instance matrix_order
    (X: Type)
  :
    PartialOrderZero (X -> X -> bool)
  := {|
    partial_order_rel xs1 xs2 :=
      forall x1 x2, xs1 x1 x2 = true -> xs2 x1 x2 = true;
    partial_order_zero := matrix_empty;
  |}.
  Next Obligation.
    extensionality x; extensionality x'.
    destruct (x1 x x') eqn:?;
    destruct (x2 x x') eqn:?;
    intuition.
    - apply H in Heqb.
      congruence.
    - apply H0 in Heqb0.
      congruence.
  Qed.

  Definition matrix_iterate
    {X: Type}
    `{Finite X}
    (Rbias Rstep R: X -> X -> bool)
  :=
    matrix_plus Rbias (matrix_product_bool Rstep R)
  .

  Program Definition matrix_star
    {X: Type}
    `{Finite X}
    (R: X -> X -> bool)
  :=
    mono_fixpoint (matrix_iterate finite_eqb R)
  .

  Lemma matrix_plus_partial_order_rel
    {X: Type}
    (R1 R2: X -> X -> bool)
  :
    matrix_plus R1 R2 = R2 <->
    partial_order_rel R1 R2
  .
  Proof.
    split; intros.
    - simpl; intros.
      rewrite <- H.
      unfold matrix_plus.
      now rewrite H0.
    - extensionality x; extensionality x'.
      unfold matrix_plus.
      destruct (R1 x x') eqn:?.
      + apply H in Heqb.
        now rewrite Heqb.
      + reflexivity.
  Qed.

  Lemma matrix_plus_monotone
    {X: Type}
    (R1 R2 R1' R2': X -> X -> bool)
  :
    partial_order_rel R1 R1' ->
    partial_order_rel R2 R2' ->
    partial_order_rel (matrix_plus R1 R2) (matrix_plus R1' R2')
  .
  Proof.
    simpl; unfold matrix_plus; intros.
    apply Bool.orb_true_iff.
    apply Bool.orb_true_iff in H1.
    destruct H1; firstorder.
  Qed.

  Lemma matrix_product_monotone
    {X: Type}
    `{Finite X}
    (R1 R2 R1' R2': X -> X -> bool)
  :
    partial_order_rel R1 R1' ->
    partial_order_rel R2 R2' ->
    partial_order_rel (matrix_product_bool R1 R2)
                      (matrix_product_bool R1' R2')
  .
  Proof.
    simpl; unfold matrix_product_bool, vector_inner_product_bool; intros.
    apply disj_true in H2.
    apply in_map_iff in H2.
    destruct H2 as [x [? _]].
    apply Bool.andb_true_iff in H2.
    destruct H2.
    apply disj_true.
    apply in_map_iff.
    eexists; intuition.
  Qed.

  Lemma matrix_iterate_monotone
    {X: Type}
    `{Finite X}
    (R Rbias: X -> X -> bool)
  :
    monotone (matrix_iterate Rbias R)
  .
  Proof.
    split; intros.
    unfold matrix_iterate.
    apply matrix_plus_monotone.
    - apply partial_order_refl.
    - apply matrix_product_monotone; auto.
      apply partial_order_refl.
  Qed.

  Lemma matrix_plus_split
    {X: Type}
    (R1 R2 R3: X -> X -> bool)
  :
    partial_order_rel R1 R3 ->
    partial_order_rel R2 R3 ->
    partial_order_rel (matrix_plus R1 R2) R3
  .
  Proof.
    simpl; intros.
    unfold matrix_plus in H1.
    apply Bool.orb_true_iff in H1.
    destruct H1; intuition.
  Qed.

  Lemma matrix_plus_covered_left
    {X: Type}
    (R1 R2: X -> X -> bool)
  :
    partial_order_rel R1 (matrix_plus R1 R2)
  .
  Proof.
    simpl; intros.
    unfold matrix_plus.
    now rewrite H.
  Qed.

  Fixpoint matrix_power
    {X: Type}
    `{Finite X}
    (R: X -> X -> bool)
    (n: nat)
  :=
    match n with
    | 0%nat => finite_eqb
    | S n => matrix_product_bool R (matrix_power R n)
    end
  .

  Fixpoint matrix_power_series
    {X: Type}
    `{Finite X}
    (R1 R2: X -> X -> bool)
    (n: nat)
  :=
    match n with
    | 0%nat => matrix_empty
    | S n => matrix_plus (matrix_power_series R1 R2 n)
                         (matrix_product_bool (matrix_power R1 n) R2)
    end
  .

  Lemma matrix_product_empty_left
    {X: Type}
    `{Finite X}
    (R: X -> X -> bool)
  :
    matrix_product_bool matrix_empty R = matrix_empty
  .
  Proof.
    extensionality x1; extensionality x2.
    unfold matrix_product_bool, matrix_empty, vector_inner_product_bool.
    apply disj_false; intros.
    apply in_map_iff in H0.
    destruct H0 as [? [? ?]].
    now simpl in H0.
  Qed.

  Lemma matrix_product_empty_right
    {X: Type}
    `{Finite X}
    (R: X -> X -> bool)
  :
    matrix_product_bool R matrix_empty = matrix_empty
  .
  Proof.
    extensionality x1; extensionality x2.
    unfold matrix_product_bool, matrix_empty, vector_inner_product_bool.
    apply disj_false; intros.
    apply in_map_iff in H0.
    destruct H0 as [? [? ?]].
    now rewrite Bool.andb_false_r in H0.
  Qed.

  Lemma matrix_product_distribute_right
    {X: Type}
    `{Finite X}
    (R1 R2 R3: X -> X -> bool)
  :
    matrix_product_bool (matrix_plus R1 R2) R3 =
    matrix_plus (matrix_product_bool R1 R3)
                (matrix_product_bool R2 R3)
  .
  Proof.
    extensionality x; extensionality x'.
    unfold matrix_product_bool, vector_inner_product_bool, matrix_plus.
    apply Bool.eq_bool_prop_intro; split; intros.
    - apply Bool.Is_true_eq_true in H0.
      apply Bool.Is_true_eq_left.
      apply Bool.orb_true_iff.
      apply disj_true in H0.
      apply in_map_iff in H0.
      destruct H0 as [x'' [? _]].
      apply Bool.andb_true_iff in H0; destruct H0.
      apply Bool.orb_true_iff in H0; destruct H0.
      + left; apply disj_true.
        apply in_map_iff.
        eexists; intuition.
      + right; apply disj_true.
        apply in_map_iff.
        eexists; intuition.
    - apply Bool.Is_true_eq_true in H0.
      apply Bool.orb_true_iff in H0.
      apply Bool.Is_true_eq_left.
      apply disj_true.
      apply in_map_iff.
      destruct H0.
      + apply disj_true in H0.
        apply in_map_iff in H0.
        destruct H0 as [x'' [? _]].
        eexists; intuition.
      + apply disj_true in H0.
        apply in_map_iff in H0.
        destruct H0 as [x'' [? _]].
        eexists; intuition.
  Qed.

  Lemma matrix_product_distribute_left
    {X: Type}
    `{Finite X}
    (R1 R2 R3: X -> X -> bool)
  :
    matrix_product_bool R1 (matrix_plus R2 R3) =
    matrix_plus (matrix_product_bool R1 R2)
                (matrix_product_bool R1 R3)
  .
  Proof.
    extensionality x; extensionality x'.
    unfold matrix_product_bool, vector_inner_product_bool, matrix_plus.
    apply Bool.eq_bool_prop_intro; split; intros.
    - apply Bool.Is_true_eq_true in H0.
      apply Bool.Is_true_eq_left.
      apply Bool.orb_true_iff.
      apply disj_true in H0.
      apply in_map_iff in H0.
      destruct H0 as [x'' [? _]].
      apply Bool.andb_true_iff in H0; destruct H0.
      apply Bool.orb_true_iff in H1; destruct H1.
      + left; apply disj_true.
        apply in_map_iff.
        eexists; intuition.
      + right; apply disj_true.
        apply in_map_iff.
        eexists; intuition.
    - apply Bool.Is_true_eq_true in H0.
      apply Bool.orb_true_iff in H0.
      apply Bool.Is_true_eq_left.
      apply disj_true.
      apply in_map_iff.
      destruct H0.
      + apply disj_true in H0.
        apply in_map_iff in H0.
        destruct H0 as [x'' [? _]].
        eexists; intuition.
      + apply disj_true in H0.
        apply in_map_iff in H0.
        destruct H0 as [x'' [? _]].
        eexists; intuition.
  Qed.

  Lemma matrix_power_series_assoc
    {X: Type}
    `{Finite X}
    (R1 R2 R3: X -> X -> bool)
    (n: nat)
  :
    matrix_product_bool (matrix_power_series R1 R2 n) R3 =
    matrix_power_series R1 (matrix_product_bool R2 R3) n
  .
  Proof.
    induction n; simpl.
    - now rewrite matrix_product_empty_left.
    - rewrite matrix_product_distribute_right.
      rewrite <- matrix_product_bool_associative.
      now rewrite IHn.
  Qed.

  Lemma matrix_plus_unit_right
    {X: Type}
    (R: X -> X -> bool)
  :
    matrix_plus R matrix_empty = R
  .
  Proof.
    extensionality x1; extensionality x2.
    unfold matrix_plus, matrix_empty; btauto.
  Qed.

  Lemma matrix_plus_associative
    {X: Type}
    (R1 R2 R3: X -> X -> bool)
  :
    matrix_plus (matrix_plus R1 R2) R3 =
    matrix_plus R1 (matrix_plus R2 R3)
  .
  Proof.
    extensionality x; extensionality x'.
    unfold matrix_plus; btauto.
  Qed.

  Lemma matrix_power_series_unfold
    {X: Type}
    `{Finite X}
    (R1 R2: X -> X -> bool)
    (n: nat)
  :
    matrix_plus R2 (matrix_product_bool R1 (matrix_power_series R1 R2 n)) =
    matrix_plus (matrix_power_series R1 R2 n)
      (matrix_product_bool (matrix_power R1 n) R2)
  .
  Proof.
    induction n; simpl.
    - rewrite matrix_product_empty_right.
      rewrite matrix_plus_unit_right.
      rewrite matrix_plus_commute.
      rewrite matrix_plus_unit_right.
      rewrite matrix_product_bool_unit_left.
      reflexivity.
    - rewrite matrix_product_distribute_left.
      rewrite <- matrix_plus_associative.
      rewrite matrix_product_bool_associative.
      now rewrite IHn.
  Qed.

  Lemma iterate_power_series
    {X: Type}
    `{Finite X}
    (R1 R2: X -> X -> bool)
    (n: nat)
  :
    iterate (matrix_iterate R2 R1) partial_order_zero n =
    matrix_power_series R1 R2 n
  .
  Proof.
    induction n; simpl.
    - reflexivity.
    - simpl in IHn; rewrite IHn.
      unfold matrix_iterate.
      apply matrix_power_series_unfold.
  Qed.

  Lemma iterate_distribute_right
    {X: Type}
    `{Finite X}
    (R1 R2 R3: X -> X -> bool)
    (n: nat)
  :
    matrix_product_bool (iterate (matrix_iterate R2 R1) partial_order_zero n) R3 =
    iterate (matrix_iterate (matrix_product_bool R2 R3) R1) partial_order_zero n
  .
  Proof.
    repeat rewrite iterate_power_series.
    apply matrix_power_series_assoc.
  Qed.

  Lemma matrix_iterate_shift_fixpoint
    {X: Type}
    `{Finite X}
    (R Rbias: X -> X -> bool)
  :
    matrix_product_bool (mono_fixpoint (matrix_iterate finite_eqb R)) Rbias =
    mono_fixpoint (matrix_iterate Rbias R)
  .
  Proof.
    apply partial_order_antisym.
    - unfold mono_fixpoint.
      rewrite iterate_distribute_right.
      rewrite matrix_product_bool_unit_left.
      apply partial_order_refl.
    - apply mono_fixpoint_least.
      + apply matrix_iterate_monotone.
      + unfold matrix_iterate at 1.
        apply matrix_plus_split.
        * rewrite <- matrix_product_bool_unit_left with (m := Rbias) at 1.
          apply matrix_product_monotone.
          -- rewrite <- mono_fixpoint_fixpoint.
             ++ unfold matrix_iterate.
                apply matrix_plus_covered_left.
             ++ apply matrix_iterate_monotone.
          -- apply partial_order_refl.
        * rewrite <- matrix_product_bool_associative.
          apply matrix_product_monotone.
          -- eapply partial_order_trans
               with (x2 := matrix_iterate finite_eqb R (mono_fixpoint (matrix_iterate finite_eqb R))).
             ++ unfold matrix_iterate at 2.
                rewrite matrix_plus_commute.
                apply matrix_plus_covered_left.
             ++ rewrite mono_fixpoint_fixpoint.
                ** apply partial_order_refl.
                ** apply matrix_iterate_monotone.
          -- apply partial_order_refl.
  Qed.

  Program Definition kleene_algebra_finite_relational
    (X: Type)
    `{Finite X}
  :
    kleene_algebra (X -> X -> bool)
  := {|
    kleene_monoid := monoid_finite_relational X;
    kleene_plus := matrix_plus;
    kleene_zero := matrix_empty;
    kleene_star := matrix_star;
  |}.
  Next Obligation.
    apply matrix_plus_associative.
  Qed.
  Next Obligation.
    apply matrix_plus_unit_right.
  Qed.
  Next Obligation.
    extensionality x1; extensionality x2.
    unfold matrix_plus; btauto.
  Qed.
  Next Obligation.
    apply matrix_plus_commute.
  Qed.
  Next Obligation.
    apply matrix_product_empty_left.
  Qed.
  Next Obligation.
    apply matrix_product_empty_right.
  Qed.
  Next Obligation.
    apply matrix_product_distribute_left.
  Qed.
  Next Obligation.
    apply matrix_product_distribute_right.
  Qed.
  Next Obligation.
    unfold matrix_star.
    rewrite <- mono_fixpoint_fixpoint at 2.
    - reflexivity.
    - split; simpl; intros.
      unfold matrix_plus in *.
      apply Bool.orb_prop in H1.
      rewrite finite_eqb_eq in H1.
      destruct H1.
      + subst.
        apply Bool.orb_true_iff; left.
        now apply finite_eqb_eq.
      + apply Bool.orb_true_iff; right.
        unfold matrix_product_bool in *.
        unfold vector_inner_product_bool in *.
        apply disj_true.
        apply in_map_iff.
        apply disj_true in H1.
        apply in_map_iff in H1.
        destruct H1 as [? [? ?]].
        eexists; intuition.
  Qed.
  Next Obligation.
    apply matrix_plus_partial_order_rel.
    apply matrix_plus_partial_order_rel in H0.
    rewrite matrix_plus_commute in H0.
    replace (matrix_plus x3 (matrix_product_bool x1 x2))
      with (matrix_iterate x3 x1 x2) in H0 by reflexivity.
    apply mono_fixpoint_least in H0.
    - unfold matrix_star.
      now rewrite matrix_iterate_shift_fixpoint.
    - apply matrix_iterate_monotone.
  Qed.
End FiniteRelationalModels.

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
    forall (X: Type) (K: kleene_algebra X),
      Ks K ->
      kleene_satisfies K t1 t2
  .

  Lemma kleene_satisfies_class_symmetric
    {A: Type}
    (Ks: forall {X: Type}, kleene_algebra X -> Prop)
    (t1 t2: term A)
  :
    kleene_satisfies_class (@Ks) t1 t2 ->
    kleene_satisfies_class (@Ks) t2 t1
  .
  Proof.
    firstorder.
  Qed.

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
      forall (X: Type) `{Finite X},
        kleene_finite_relational (kleene_algebra_finite_relational X)
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

  Lemma kleene_preserve_equation_finite_finite_relational
    {A X: Type}
    (K: kleene_algebra X)
    (t1 t2: term A)
  :
    kleene_satisfies_class (@kleene_finite) t1 t2 ->
    kleene_satisfies_class (@kleene_finite_relational) t1 t2
  .
  Proof.
    apply kleene_class_contained_preserves; intros.
    destruct H.
    constructor.
    typeclasses eauto.
  Qed.
End EquationalTheories.

Section RelationalVsFiniteRelational.
  Definition kleene_finite_relational_to_relational
    {X: Type}
    (f: X -> X -> bool)
    (x x': X)
  :
    Prop
  :=
    f x x' = true
  .

  Lemma kleene_finite_relational_to_relational_injective
    {X: Type}
    (f1 f2: X -> X -> bool)
  :
    kleene_finite_relational_to_relational f1 =
    kleene_finite_relational_to_relational f2 ->
    f1 = f2
  .
  Proof.
    intros.
    extensionality x; extensionality x'.
    unfold kleene_finite_relational_to_relational in H.
    apply function_instantiation with (x := x) in H.
    apply function_instantiation with (x := x') in H.
    apply Bool.eq_true_iff_eq.
    now rewrite H.
  Qed.

  Lemma kleene_finite_relational_to_relational_plus
    {X: Type}
    `{Finite X}
  :
    let K := kleene_algebra_finite_relational X in
    let K' := kleene_algebra_relational X in
    forall m m',
      kleene_plus K' (kleene_finite_relational_to_relational m)
                     (kleene_finite_relational_to_relational m') =
      kleene_finite_relational_to_relational (kleene_plus K m m')
  .
  Proof.
    simpl; intros.
    extensionality x; extensionality x'; simpl.
    unfold kleene_relational_plus.
    unfold kleene_finite_relational_to_relational.
    apply propositional_extensionality.
    unfold matrix_plus.
    now rewrite Bool.orb_true_iff.
  Qed.

  Lemma kleene_finite_relational_to_relational_multiply
    {X: Type}
    `{Finite X}
  :
    let K := kleene_algebra_finite_relational X in
    let K' := kleene_algebra_relational X in
    forall m m',
      kleene_multiply K' (kleene_finite_relational_to_relational m)
                     (kleene_finite_relational_to_relational m') =
      kleene_finite_relational_to_relational (kleene_multiply K m m')
  .
  Proof.
    simpl; unfold kleene_multiply; intros.
    extensionality x; extensionality x'; simpl.
    unfold monoid_relational_compose.
    unfold kleene_finite_relational_to_relational.
    apply propositional_extensionality.
    now rewrite matrix_product_characterise.
  Qed.

  Lemma kleene_finite_relational_to_relational_star
    {X: Type}
    `{Finite X}
  :
    let K := kleene_algebra_finite_relational X in
    let K' := kleene_algebra_relational X in
    forall m,
      kleene_star K' (kleene_finite_relational_to_relational m) =
      kleene_finite_relational_to_relational (kleene_star K m)
  .
  Proof.
    simpl; intros.
    extensionality x; extensionality x'; simpl.
    unfold kleene_finite_relational_to_relational.
    apply propositional_extensionality.
    unfold matrix_star; intuition.
    - induction H0.
      + rewrite <- mono_fixpoint_fixpoint.
        * unfold matrix_iterate, matrix_plus.
          rewrite Bool.orb_true_iff; left.
          now rewrite finite_eqb_eq.
        * apply matrix_iterate_monotone.
      + rewrite <- mono_fixpoint_fixpoint.
        * unfold matrix_iterate, matrix_plus.
          rewrite Bool.orb_true_iff; right.
          apply matrix_product_characterise; eexists.
          intuition eauto.
        * apply matrix_iterate_monotone.
    - unfold mono_fixpoint in H0.
      revert x x' H0;
      generalize (length (@finite_enum _ (@matrix_finite X X H H))); intro.
      induction n; intros.
      + simpl in H0.
        unfold matrix_empty in H0.
        discriminate.
      + simpl in H0.
        unfold matrix_iterate in H0 at 1.
        unfold matrix_plus in H0.
        rewrite Bool.orb_true_iff in H0.
        destruct H0.
        * rewrite finite_eqb_eq in H0; subst.
          apply KleeneRelationalStarBase.
        * rewrite matrix_product_characterise in H0.
          destruct H0 as [x'' [? ?]].
          eapply KleeneRelationalStarStep; eauto.
  Qed.

  Lemma kleene_finite_relational_to_relational_commute
    {X A: Type}
    `{Finite X}
    (h: A -> X -> X -> bool)
    (t: term A)
  :
  kleene_finite_relational_to_relational
    (kleene_interp (kleene_algebra_finite_relational X) h t) =
  kleene_interp (kleene_algebra_relational X)
                (kleene_finite_relational_to_relational ∘ h) t
  .
  Proof.
    induction t; autorewrite with kleene_interp.
    - simpl.
      unfold kleene_finite_relational_to_relational.
      unfold kleene_relational_zero.
      unfold matrix_empty.
      extensionality x; extensionality x'.
      apply propositional_extensionality.
      intuition.
    - unfold kleene_unit; simpl.
      unfold monoid_relational_unit.
      unfold kleene_finite_relational_to_relational.
      extensionality x; extensionality x'.
      apply propositional_extensionality.
      now rewrite finite_eqb_eq.
    - reflexivity.
    - rewrite <- kleene_finite_relational_to_relational_plus; congruence.
    - rewrite <- kleene_finite_relational_to_relational_multiply; congruence.
    - rewrite <- kleene_finite_relational_to_relational_star; congruence.
  Qed.

  Lemma kleene_preserve_equation_relational_finite_relational
    {A: Type}
    (t1 t2: term A)
  :
    kleene_satisfies_class (@kleene_relational) t1 t2 ->
    kleene_satisfies_class (@kleene_finite_relational) t1 t2
  .
  Proof.
    unfold kleene_satisfies_class, kleene_satisfies; intros.
    destruct H0.
    apply kleene_finite_relational_to_relational_injective.
    repeat rewrite kleene_finite_relational_to_relational_commute.
    now apply H.
  Qed.
End RelationalVsFiniteRelational.

Section FiniteEmbedding.
  Equations substring
    {A: Type}
    (w: list A)
    (p0 p1: position (S (length w)))
  :
    list A + unit
  := {
    substring _ PHere PHere :=
      inl nil;
    substring (a :: w) PHere (PThere p1) :=
      match substring w PHere p1 with
      | inl w => inl (a :: w)
      | inr _ => inr tt
      end;
    substring (a :: w) (PThere p0) (PThere p1) :=
      substring w p0 p1;
    substring _ (PThere p0) PHere :=
      inr tt;
  }.

  Equations embed_word
    {A: Type}
    `{Finite A}
    (w: list A)
    (a: A)
    (p0 p1: position (S (length w)))
  :
    bool
  := {
    embed_word (a :: w) b PHere (PThere PHere) :=
      finite_eqb a b;
    embed_word (a :: w) b (PThere p0) (PThere p1) :=
      embed_word w b p0 p1;
    embed_word _ _ _ _ :=
      false;
  }.

  Definition kleene_finite_words
    {A: Type}
    (w: list A)
  :=
    kleene_algebra_finite_relational (position (S (length w)))
  .

  Lemma substring_nil
    {A: Type}
    `{Finite A}
    (w: list A)
    (p0 p1: position (S (length w)))
  :
    substring w p0 p1 = inl nil ->
    p0 = p1
  .
  Proof.
    intros; dependent induction w.
    - dependent destruction p0.
      + now repeat dependent destruction p1.
      + dependent destruction p0.
    - dependent destruction p0.
      + dependent destruction p1; auto.
        dependent destruction p1;
        autorewrite with substring in H0.
        * discriminate.
        * destruct (substring w _ _);
          discriminate.
      + dependent destruction p1.
        * now autorewrite with substring in H0.
        * autorewrite with substring in H0.
          f_equal; intuition.
  Qed.

  Lemma substring_single
    {A: Type}
    `{Finite A}
    (a: A)
    (w w0 w1: list A)
    (p0 p1: position (S (length w)))
  :
    substring w p0 p1 = inl (a :: nil) ->
    embed_word w a p0 p1 = true
  .
  Proof.
    intros; dependent induction w.
    - dependent destruction p0.
      + dependent destruction p1.
        * now autorewrite with substring in H0.
        * dependent destruction p1.
      + dependent destruction p0.
    - dependent destruction p0.
      + dependent destruction p1.
        * now autorewrite with substring in H0.
        * autorewrite with substring in H0.
          destruct (substring w _ _) eqn:?; try discriminate.
          inversion H0; subst.
          clear IHw H0.
          revert Heqs; dependent induction w; intros.
          -- repeat dependent destruction p1.
             autorewrite with embed_word.
             now apply finite_eqb_eq.
          -- dependent destruction p1.
             ++ autorewrite with embed_word.
                now apply finite_eqb_eq.
             ++ autorewrite with embed_word.
                autorewrite with substring in Heqs.
                destruct (substring w _ _) eqn:?; discriminate.
      + dependent destruction p1.
        ++ now autorewrite with substring in H0.
        ++ autorewrite with substring in H0.
           autorewrite with embed_word.
           intuition.
  Qed.

  Lemma substring_app
    {A: Type}
    `{Finite A}
    (w w0 w1: list A)
    (p0 p1: position (S (length w)))
  :
    substring w p0 p1 = inl (w0 ++ w1) ->
    exists p2,
      substring w p0 p2 = inl w0 /\
      substring w p2 p1 = inl w1
  .
  Proof.
    revert w0 w1 p0 p1; dependent induction w; intros.
    - repeat dependent destruction p0.
      repeat dependent destruction p1.
      autorewrite with substring in H0; inversion H0.
      symmetry in H2; apply app_eq_nil in H2; destruct H2; subst.
      exists PHere; intuition.
    - dependent destruction p0.
      + dependent destruction p1.
        * autorewrite with substring in H0; inversion H0.
          symmetry in H2; apply app_eq_nil in H2; destruct H2; subst.
          exists PHere; intuition.
        * autorewrite with substring in H0.
          destruct (substring w _ _) eqn:?; try discriminate.
          inversion H0.
          destruct w0; simpl in H2.
          -- exists PHere; intuition.
             autorewrite with substring.
             now rewrite Heqs.
          -- inversion H2; subst.
             apply IHw in Heqs.
             destruct Heqs as [p2 [? ?]].
             exists (PThere p2).
             autorewrite with substring; intuition.
             now rewrite H1.
      + dependent destruction p1.
        * now autorewrite with substring in H0.
        * autorewrite with substring in H0.
          apply IHw in H0.
          destruct H0 as [p2 [? ?]].
          exists (PThere p2).
          now autorewrite with substring.
  Qed.

  Lemma kleene_finite_embed
    {A: Type}
    `{Finite A}
    (w x: list A)
    (p0 p1: position (S (length w)))
    (t: term A)
  :
    substring w p0 p1 = inl x ->
    term_matches t x ->
    kleene_interp (kleene_finite_words w) (embed_word w) t p0 p1 = true
  .
  Proof.
    revert w x p0 p1; dependent induction t; intros.
    - dependent destruction H1.
    - dependent destruction H1.
      autorewrite with kleene_interp.
      unfold kleene_unit; simpl.
      now apply finite_eqb_eq, substring_nil.
    - dependent destruction H1.
      autorewrite with kleene_interp.
      now apply substring_single.
    - autorewrite with kleene_interp.
      simpl; unfold matrix_plus.
      apply Bool.orb_true_iff.
      dependent destruction H1.
      + left; eapply IHt1; eauto.
      + right; eapply IHt2; eauto.
    - dependent destruction H1.
      autorewrite with kleene_interp.
      unfold kleene_multiply; simpl.
      apply matrix_product_characterise.
      apply substring_app in H0.
      destruct H0 as [p2 [? ?]].
      exists p2; intuition.
    - autorewrite with kleene_interp; simpl.
      dependent induction H1.
      + unfold matrix_star.
        rewrite <- mono_fixpoint_fixpoint
          by apply matrix_iterate_monotone.
        unfold matrix_iterate at 1, matrix_plus.
        apply Bool.orb_true_iff.
        left; now apply finite_eqb_eq, substring_nil.
      + unfold matrix_star.
        rewrite <- mono_fixpoint_fixpoint
          by apply matrix_iterate_monotone.
        unfold matrix_iterate at 1, matrix_plus.
        apply Bool.orb_true_iff.
        apply substring_app in H0.
        destruct H0 as [p2 [? ?]]; right.
        apply matrix_product_characterise.
        exists p2; intuition.
  Qed.

  Lemma substring_nil'
    {A: Type}
    `{Finite A}
    (w: list A)
    (p: position (S (length w)))
  :
    substring w p p = inl nil
  .
  Proof.
    dependent induction p;
    autorewrite with substring.
    - reflexivity.
    - destruct w.
      + dependent destruction p.
      + autorewrite with substring.
        intuition.
  Qed.

  Lemma substring_single'
    {A: Type}
    `{Finite A}
    (a: A)
    (w: list A)
    (p0 p1: position (S (length w)))
  :
    embed_word w a p0 p1 = true ->
    substring w p0 p1 = inl (a :: nil)
  .
  Proof.
    dependent induction w.
    - dependent destruction p0;
      dependent destruction p1;
      intuition.
    - dependent destruction p0;
      dependent destruction p1;
      intuition.
      + dependent destruction p1.
        * autorewrite with embed_word in H0.
          apply finite_eqb_eq in H0; subst.
          now autorewrite with substring.
        * now autorewrite with embed_word in H0.
      + autorewrite with embed_word in H0.
        autorewrite with substring.
        intuition.
  Qed.

  Lemma substring_app'
    {A: Type}
    `{Finite A}
    (w w0 w1: list A)
    (p0 p1 p2: position (S (length w)))
  :
    substring w p0 p2 = inl w0 ->
    substring w p2 p1 = inl w1 ->
    substring w p0 p1 = inl (w0 ++ w1)
  .
  Proof.
    intros.
    dependent induction w.
    - dependent destruction p0; try now dependent destruction p0.
      dependent destruction p1; try now dependent destruction p1.
      dependent destruction p2; try now dependent destruction p2.
      autorewrite with substring in H0; inversion H0; subst.
      autorewrite with substring in H1; inversion H1; subst.
      now autorewrite with substring.
    - dependent destruction p0.
      + dependent destruction p1.
        * dependent destruction p2.
          -- autorewrite with substring in H0; inversion H0; subst.
             autorewrite with substring in H1; inversion H1; subst.
             now autorewrite with substring.
          -- autorewrite with substring in H1; inversion H1; subst.
        * dependent destruction p2.
          -- now autorewrite with substring in H0; inversion H0; subst.
          -- autorewrite with substring in H1.
             autorewrite with substring in H0.
             autorewrite with substring.
             destruct (substring w PHere p2) eqn:?; try discriminate.
             erewrite IHw; eauto.
             now inversion H0.
      + dependent destruction p1.
        * dependent destruction p2.
          -- now autorewrite with substring in H0.
          -- now autorewrite with substring in H1.
        * dependent destruction p2.
          -- now autorewrite with substring in H0.
          -- autorewrite with substring in H0.
             autorewrite with substring in H1.
             autorewrite with substring.
             eapply IHw; eauto.
  Qed.

  Lemma kleene_finite_recover
    {A: Type}
    `{Finite A}
    (w: list A)
    (p0 p1: position (S (length w)))
    (t: term A)
  :
    kleene_interp (kleene_finite_words w) (embed_word w) t p0 p1 = true ->
    exists x,
      substring w p0 p1 = inl x /\
      term_matches t x
  .
  Proof.
    revert w p0 p1; dependent induction t; intros;
    autorewrite with kleene_interp in H0; simpl in H0.
    - now (simpl in H0; unfold matrix_empty in H0).
    - unfold kleene_unit in H0; simpl in H0.
      apply finite_eqb_eq in H0; subst.
      exists nil; rewrite substring_nil'.
      intuition constructor.
    - exists (a :: nil).
      erewrite substring_single'; eauto.
      intuition constructor.
    - unfold matrix_plus in H0.
      apply Bool.orb_true_iff in H0.
      destruct H0.
      + apply IHt1 in H0.
        destruct H0 as [x [? ?]].
        exists x; intuition now constructor.
      + apply IHt2 in H0.
        destruct H0 as [x [? ?]].
        exists x; intuition now constructor.
    - unfold kleene_multiply in H0; simpl in H0.
      apply matrix_product_characterise in H0.
      destruct H0 as [q3 [? ?]].
      apply IHt1 in H0; destruct H0 as [x0 [? ?]].
      apply IHt2 in H1; destruct H1 as [x1 [? ?]].
      exists (x0 ++ x1).
      intuition.
      + eapply substring_app'; eauto.
      + now constructor.
    - unfold matrix_star in H0.
      unfold mono_fixpoint in H0.
      revert p0 p1 H0. match goal with
      | |- context [ length ?n ] => generalize (length n)
      end; intro; induction n; intros; simpl in H0.
      + now unfold matrix_empty in H0.
      + unfold matrix_iterate at 1, matrix_plus in H0.
        apply Bool.orb_true_iff in H0.
        destruct H0; intuition.
        * apply finite_eqb_eq in H0; subst.
          exists nil; intuition.
          -- apply substring_nil'.
          -- constructor.
        * apply matrix_product_characterise in H0.
          destruct H0 as [p2 [? ?]].
          apply IHt in H0; destruct H0 as [x0 [? ?]].
          apply IHn in H1; destruct H1 as [x1 [? ?]].
          exists (x0 ++ x1); intuition.
          -- eapply substring_app'; eauto.
          -- now constructor.
  Qed.

  Fixpoint position_max (n: nat) : position (S n) :=
    match n with
    | 0%nat => PHere
    | S n => PThere (position_max n)
    end
  .

  Lemma substring_whole
    {A: Type}
    (w: list A)
  :
    substring w PHere (position_max (length w)) = inl w
  .
  Proof.
    induction w; simpl;
    autorewrite with substring.
    - reflexivity.
    - now rewrite IHw.
  Qed.

  Lemma kleene_finite_equiv
    {A: Type}
    `{Finite A}
    (w: list A)
    (t: term A)
  :
    term_matches t w <->
    kleene_interp (kleene_finite_words w)
                  (embed_word w) t
                  PHere (position_max (length w)) = true
  .
  Proof.
    intuition.
    - eapply kleene_finite_embed with (w := w) (x := w); auto.
      apply substring_whole.
    - apply kleene_finite_recover in H0.
      destruct H0 as [x [? ?]].
      rewrite substring_whole in H0.
      inversion H0; now subst.
  Qed.

  Lemma kleene_preserve_equation_finite_relational_language
    {A: Type}
    `{Finite A}
    (t1 t2: term A)
    (w: list A)
  :
    kleene_satisfies_class (@kleene_finite_relational) t1 t2 ->
    term_matches t1 w <-> term_matches t2 w
  .
  Proof.
    intros; repeat rewrite kleene_finite_equiv.
    apply Bool.eq_iff_eq_true.
    now rewrite H0.
  Qed.
End FiniteEmbedding.

Section StarContinuousEmbedding.
  Equations kleene_interp_word
    {X A: Type}
    (K: kleene_algebra X)
    (h: A -> X)
    (w: list A)
  :
    X
  := {
    kleene_interp_word K h nil :=
      kleene_unit K;
    kleene_interp_word K h (a :: w) :=
      kleene_multiply K (h a) (kleene_interp_word K h w);
  }.

  Lemma kleene_interp_word_app
    {X A: Type}
    (K: kleene_algebra X)
    (h: A -> X)
    (w1 w2: list A)
  :
    kleene_multiply K (kleene_interp_word K h w1)
                      (kleene_interp_word K h w2) =
    kleene_interp_word K h (w1 ++ w2)
  .
  Proof.
    induction w1; simpl;
    autorewrite with kleene_interp_word.
    - unfold kleene_multiply, kleene_unit.
      now rewrite monoid_unit_right.
    - unfold kleene_multiply in *.
      rewrite monoid_compose_assoc.
      now rewrite IHw1.
  Qed.

  Lemma kleene_star_continuous_interp_lower_general
    {X A: Type}
    (K: kleene_algebra X)
    (t: term A)
    (h: A -> X)
    (u v x: X)
  :
    kleene_star_continuous K ->
    (forall (w: list A),
      term_matches t w ->
      let hwv := kleene_multiply K (kleene_interp_word K h w) v in
      let lhs := kleene_multiply K u hwv in
      kleene_plus K lhs x = x) ->
    let htv := kleene_multiply K (kleene_interp K h t) v in
    let lhs := kleene_multiply K u htv in
    kleene_plus K lhs x = x
  .
  Proof.
    simpl; revert u v; dependent induction t; intros;
    autorewrite with kleene_interp.
    - rewrite kleene_multiply_zero_left, kleene_multiply_zero_right.
      now rewrite kleene_plus_commute, kleene_plus_unit.
    - specialize (H0 nil).
      autorewrite with kleene_interp_word in H.
      apply H0; constructor.
    - specialize (H0 (a :: nil)).
      autorewrite with kleene_interp_word in H0.
      unfold kleene_multiply in H0 at 3.
      unfold kleene_unit in H0.
      rewrite monoid_unit_left in H0.
      apply H0; constructor.
    - rewrite kleene_distribute_right.
      rewrite kleene_distribute_left.
      rewrite kleene_plus_assoc.
      rewrite IHt2, IHt1; intuition.
      + now apply H0, MatchPlusLeft.
      + now apply H0, MatchPlusRight.
    - unfold kleene_multiply in *.
      rewrite monoid_compose_assoc.
      rewrite IHt1; auto; intros.
      rewrite <- monoid_compose_assoc.
      rewrite IHt2; auto; intros.
      rewrite monoid_compose_assoc.
      rewrite <- monoid_compose_assoc with (x1 := kleene_interp_word K h w).
      replace (monoid_compose _ (kleene_interp_word K h w)
                                (kleene_interp_word K h w0))
        with (kleene_interp_word K h (w ++ w0)).
      + apply H0; now constructor.
      + now rewrite <- kleene_interp_word_app.
    - apply H; intros.
    revert u v H0; induction n; simpl; intros.
      + specialize (H0 nil).
        autorewrite with kleene_interp_word in H0.
        apply H0; now constructor.
      + unfold kleene_multiply in *.
        rewrite monoid_compose_assoc with (x1 := kleene_interp K h t).
        rewrite <- monoid_compose_assoc with (x1 := u).
        rewrite IHn; intuition.
        rewrite monoid_compose_assoc.
        rewrite IHt; intuition.
        rewrite <- monoid_compose_assoc with (x1 := kleene_interp_word K h w0).
        replace (monoid_compose _ (kleene_interp_word K h w0)
                                  (kleene_interp_word K h w))
          with (kleene_interp_word K h (w0 ++ w)).
        * apply H0; now constructor.
        * now rewrite <- kleene_interp_word_app.
  Qed.

  Lemma kleene_star_continuous_interp_lower
    {X A: Type}
    (K: kleene_algebra X)
    (t: term A)
    (h: A -> X)
    (x: X)
  :
    kleene_star_continuous K ->
    (forall (w: list A),
      term_matches t w ->
      let lhs := kleene_interp_word K h w in
      kleene_plus K lhs x = x) ->
    let lhs := kleene_interp K h t in
    kleene_plus K lhs x = x
  .
  Proof.
    simpl; intros.
    rewrite <- kleene_multiply_unit_left
      with (k := K) (x := kleene_interp K h t).
    rewrite <- kleene_multiply_unit_right
      with (k := K) (x := monoid_compose _ _ _).
    apply kleene_star_continuous_interp_lower_general; intuition.
    unfold kleene_multiply.
    rewrite kleene_multiply_unit_right.
    rewrite kleene_multiply_unit_left.
    now apply H0.
  Qed.

  Lemma kleene_multiply_monotone
    {X: Type}
    (K: kleene_algebra X)
    (x x' y y': X)
  :
    kleene_plus K x y = y ->
    kleene_plus K x' y' = y' ->
    kleene_plus K (kleene_multiply K x x') (kleene_multiply K y y') =
    kleene_multiply K y y'
  .
  Proof.
    intros.
    rewrite <- H, <- H0.
    rewrite kleene_distribute_left.
    rewrite kleene_distribute_right.
    repeat rewrite kleene_plus_assoc.
    rewrite <- kleene_plus_assoc with (x1 := kleene_multiply K x x').
    now rewrite kleene_plus_idempotent.
  Qed.

  Lemma kleene_star_continuous_interp_upper
    {X A: Type}
    (K: kleene_algebra X)
    (t: term A)
    (h: A -> X)
    (w: list A)
  :
    term_matches t w ->
    let lhs := kleene_interp_word K h w in
    let rhs := kleene_interp K h t in
    kleene_plus K lhs rhs = rhs
  .
  Proof.
    simpl; revert w; induction t; intros;
    autorewrite with kleene_interp;
    autorewrite with kleene_interp_word.
    - dependent destruction H.
    - dependent destruction H.
      now rewrite kleene_plus_idempotent.
    - dependent destruction H.
      autorewrite with kleene_interp_word.
      unfold kleene_multiply, kleene_unit.
      rewrite monoid_unit_left.
      now rewrite kleene_plus_idempotent.
    - dependent destruction H.
      + rewrite <- kleene_plus_assoc.
        now rewrite IHt1.
      + rewrite kleene_plus_commute with (x1 := kleene_interp K h t1).
        rewrite <- kleene_plus_assoc.
        now rewrite IHt2.
    - dependent destruction H.
      rewrite <- kleene_interp_word_app.
      apply kleene_multiply_monotone; intuition.
    - dependent induction H.
      + autorewrite with kleene_interp_word.
        rewrite <- kleene_star_unroll at 1.
        rewrite <- kleene_plus_assoc.
        rewrite kleene_plus_idempotent.
        now rewrite kleene_star_unroll.
      + rewrite <- kleene_star_unroll.
        rewrite <- kleene_plus_assoc.
        rewrite kleene_plus_commute with (x2 := kleene_unit K).
        rewrite kleene_plus_assoc.
        f_equal; rewrite <- kleene_interp_word_app.
        apply kleene_multiply_monotone.
        * now apply IHt.
        * now apply IHterm_matches2.
  Qed.

  Lemma kleene_preserve_equation_language_star_continuous
    {A: Type}
    (t1 t2: term A)
  :
    term_matches t1 = term_matches t2 ->
    kleene_satisfies_class (@kleene_star_continuous) t1 t2
  .
  Proof.
    unfold kleene_satisfies_class, kleene_satisfies; intuition.
    apply kleene_mutual_containment with (K := K).
    - apply kleene_star_continuous_interp_lower; intuition.
      apply kleene_star_continuous_interp_upper.
      now rewrite <- H.
    - apply kleene_star_continuous_interp_lower; intuition.
      apply kleene_star_continuous_interp_upper.
      now rewrite H.
  Qed.
End StarContinuousEmbedding.
