Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.btauto.Btauto.
Require Import Coq.Program.Equality.
Local Open Scope bool_scope.

Require Import KA.Finite.
Require Import KA.Booleans.
Require Import KA.Terms.
Require Import KA.Vectors.
Require Import KA.Automata.
Require Import KA.Antimirov.
Require Import KA.Scope.
Local Open Scope ka_scope.

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
End StructureDefinitions.

Arguments monoid X : clear implicits.
Arguments kleene_algebra X : clear implicits.

Section StructurePowerset.
  Context {A: Type}.
  Notation term := (term A).

  Definition powerset_multiplication
    {X: Type}
    `{Finite X}
    (M: monoid X)
    (xs1 xs2: X -> bool)
    (x: X)
  :
    bool
  :=
    disj (
      map (fun '(x1, x2) =>
        finite_eqb x (monoid_compose M x1 x2) &&
        xs1 x1 && xs2 x2
      )
      (list_prod finite_enum finite_enum)
    )
  .

  Lemma powerset_multiplication_characterise
    {X: Type}
    `{Finite X}
    (M: monoid X)
    (x1 x2: X -> bool)
    (x: X)
  :
    powerset_multiplication M x1 x2 x = true <->
    exists (x1' x2': X),
      x1 x1' = true /\
      x2 x2' = true /\
      monoid_compose M x1' x2' = x
  .
  Proof.
    unfold powerset_multiplication.
    rewrite disj_true, in_map_iff.
    split; intros.
    - destruct H0 as [(x1', x2') [? ?]].
      repeat rewrite Bool.andb_true_iff in H0.
      destruct H0 as [[? ?] ?].
      apply finite_eqb_eq in H0.
      now exists x1', x2'.
    - destruct H0 as [x1' [x2' [? [? ?]]]].
      exists (x1', x2').
      repeat rewrite Bool.andb_true_iff; intuition.
      + now apply finite_eqb_eq.
      + replace (list_prod finite_enum finite_enum)
          with (finite_enum (X := (prod X X)))
          by reflexivity.
        apply finite_cover.
  Qed.

  Program Definition monoid_powerset
    {X: Type}
    `{Finite X}
    (M: monoid X)
  :
    monoid (X -> bool)
  := {|
    monoid_compose := powerset_multiplication M;
    monoid_unit x := finite_eqb x (monoid_unit M);
  |}.
  Next Obligation.
    extensionality x.
    apply ZMicromega.eq_true_iff_eq.
    repeat rewrite powerset_multiplication_characterise.
    split; intros.
    - destruct H0 as [x' [x3' [? [? ?]]]].
      apply powerset_multiplication_characterise in H0.
      destruct H0 as [x1' [x2' [? [? ?]]]]; subst.
      exists x1', (monoid_compose M x2' x3'); intuition.
      + apply powerset_multiplication_characterise.
        now exists x2', x3'.
      + now rewrite monoid_compose_assoc.
    - destruct H0 as [x1' [x' [? [? ?]]]].
      apply powerset_multiplication_characterise in H1.
      destruct H1 as [x2' [x3' [? [? ?]]]]; subst.
      exists (monoid_compose M x1' x2'), x3'; intuition.
      apply powerset_multiplication_characterise.
      now exists x1', x2'.
  Qed.
  Next Obligation.
    extensionality x'.
    apply ZMicromega.eq_true_iff_eq.
    rewrite powerset_multiplication_characterise.
    split; intros.
    - destruct H0 as [x1' [x2' [? [? ?]]]].
      apply finite_eqb_eq in H1; subst.
      now rewrite monoid_unit_left.
    - exists x', (monoid_unit M).
      intuition.
      now apply finite_eqb_eq.
  Qed.
  Next Obligation.
    extensionality x'.
    apply ZMicromega.eq_true_iff_eq.
    rewrite powerset_multiplication_characterise.
    split; intros.
    - destruct H0 as [x1' [x2' [? [? ?]]]].
      apply finite_eqb_eq in H0; subst.
      now rewrite monoid_unit_right.
    - exists (monoid_unit M), x'.
      intuition.
      now apply finite_eqb_eq.
  Qed.

  Program Instance subset_order
    (X: Type)
  :
    PartialOrderZero (X -> bool)
  := {|
    partial_order_rel xs1 xs2 := forall x, xs1 x = true -> xs2 x = true;
    partial_order_zero x := false;
  |}.
  Next Obligation.
    extensionality x.
    apply ZMicromega.eq_true_iff_eq.
    intuition.
  Qed.

  Definition powerset_union
    {X: Type}
    (xs1 xs2: X -> bool)
    (x: X)
  :=
    xs1 x || xs2 x
  .

  Definition powerset_bottom
    {X: Type}
    (x: X)
  :
    bool
  :=
    false
  .

  Definition kleene_star_step
    {X: Type}
    `{Finite X}
    (M: monoid X)
    (xs xs': X -> bool)
  :
    X -> bool
  :=
    powerset_union (monoid_compose (monoid_powerset M) xs xs')
                   (monoid_unit (monoid_powerset M))
  .

  Lemma powerset_union_characterise
    {X: Type}
    (xs1 xs2: X -> bool)
    (x: X)
  :
    powerset_union xs1 xs2 x = true <->
    xs1 x = true \/ xs2 x = true
  .
  Proof.
    unfold powerset_union.
    now rewrite Bool.orb_true_iff.
  Qed.

  Lemma powerset_union_order
    {X: Type}
    (xs1 xs2: X -> bool)
  :
    powerset_union xs1 xs2 = xs2 <->
    partial_order_rel xs1 xs2
  .
  Proof.
    unfold partial_order_rel, powerset_union.
    simpl; split; intros.
    - now rewrite <- H, H0.
    - extensionality x.
      apply ZMicromega.eq_true_iff_eq.
      rewrite Bool.orb_true_iff.
      firstorder.
  Qed.

  Definition kleene_star_step_offset
    {X: Type}
    `{Finite X}
    (M: monoid X)
    (xs1 xs2 xs3: X -> bool)
  :
    X -> bool
  :=
    powerset_union (powerset_multiplication M xs1 xs3) xs2
  .

  Lemma powerset_union_multiply_distribute_right
    {X: Type}
    `{Finite X}
    (M: monoid X)
    (xs1 xs2 xs3: X -> bool)
  :
    powerset_multiplication M (powerset_union xs1 xs2) xs3 =
    powerset_union (powerset_multiplication M xs1 xs3)
                   (powerset_multiplication M xs2 xs3)
  .
  Proof.
    extensionality x'.
    unfold powerset_union.
    apply ZMicromega.eq_true_iff_eq.
    rewrite Bool.orb_true_iff.
    repeat rewrite powerset_multiplication_characterise.
    setoid_rewrite Bool.orb_true_iff.
    firstorder.
  Qed.

  Lemma powerset_union_multiply_distribute_left
    {X: Type}
    `{Finite X}
    (M: monoid X)
    (xs1 xs2 xs3: X -> bool)
  :
    powerset_multiplication M xs1 (powerset_union xs2 xs3) =
    powerset_union (powerset_multiplication M xs1 xs2)
      (powerset_multiplication M xs1 xs3)
  .
  Proof.
    extensionality x'.
    unfold powerset_union.
    apply ZMicromega.eq_true_iff_eq.
    rewrite Bool.orb_true_iff.
    repeat rewrite powerset_multiplication_characterise.
    setoid_rewrite Bool.orb_true_iff.
    firstorder.
  Qed.

  Lemma powerset_union_commute
    {X: Type}
    (xs1 xs2: X -> bool)
  :
    powerset_union xs1 xs2 =
    powerset_union xs2 xs1
  .
  Proof.
    extensionality x.
    unfold powerset_union.
    btauto.
  Qed.

  Lemma kleene_star_step_offset_fixpoint
    {X: Type}
    `{Finite X}
    (M: monoid X)
    (xs1 xs2: X -> bool)
  :
    mono_fixpoint (kleene_star_step_offset M xs1 xs2) =
    powerset_multiplication M (mono_fixpoint (kleene_star_step M xs1)) xs2
  .
  Proof.
    unfold mono_fixpoint.
    generalize (@length (X -> bool) finite_enum); intros.
    induction n; simpl in *.
    - extensionality x.
      unfold powerset_multiplication.
      symmetry; apply disj_false; intros.
      apply in_map_iff in H0.
      destruct H0 as [(x1, x2) [? ?]]; subst.
      btauto.
    - rewrite IHn.
      unfold kleene_star_step at 2, kleene_star_step_offset at 1.
      rewrite powerset_union_multiply_distribute_right.
      replace (powerset_multiplication M)
        with (monoid_compose (monoid_powerset M))
        by reflexivity.
      rewrite monoid_compose_assoc.
      now rewrite monoid_unit_right.
  Qed.

  Lemma powerset_multiplication_mono
    {X: Type}
    `{Finite X}
    (M: monoid X)
    (xs1 xs2 xs1' xs2': X -> bool)
  :
    partial_order_rel xs1 xs1' ->
    partial_order_rel xs2 xs2' ->
    partial_order_rel (powerset_multiplication M xs1 xs2)
                      (powerset_multiplication M xs1' xs2')
  .
  Proof.
    simpl; setoid_rewrite powerset_multiplication_characterise; firstorder.
  Qed.

  Lemma powerset_union_mono
    {X: Type}
    `{Finite X}
    (xs1 xs2 xs1' xs2': X -> bool)
  :
    partial_order_rel xs1 xs1' ->
    partial_order_rel xs2 xs2' ->
    partial_order_rel (powerset_union xs1 xs2)
                      (powerset_union xs1' xs2')
  .
  Proof.
    simpl; unfold powerset_union; setoid_rewrite Bool.orb_true_iff; firstorder.
  Qed.

  Lemma kleene_star_step_mono
    {X: Type}
    `{Finite X}
    (M: monoid X)
    (xs: X -> bool)
  :
    monotone (kleene_star_step M xs)
  .
  Proof.
    constructor; intros.
    unfold kleene_star_step.
    apply powerset_union_mono.
    - apply powerset_multiplication_mono; auto.
      apply partial_order_refl.
    - apply partial_order_refl.
  Qed.

  Lemma kleene_star_step_offset_mono
    {X: Type}
    `{Finite X}
    (M: monoid X)
    (xs1 xs2: X -> bool)
  :
    monotone (kleene_star_step_offset M xs1 xs2)
  .
  Proof.
    constructor; intros.
    unfold kleene_star_step_offset.
    apply powerset_union_mono.
    - apply powerset_multiplication_mono; auto.
      apply partial_order_refl.
    - apply partial_order_refl.
  Qed.

  Program Definition monoid_to_kleene_algebra
    {X: Type}
    `{Finite X}
    (M: monoid X)
  :
    kleene_algebra (X -> bool)
  := {|
    kleene_monoid := monoid_powerset M;
    kleene_zero x := false;
    kleene_plus := powerset_union;
    kleene_star xs := mono_fixpoint (kleene_star_step M xs);
  |}.
  Next Obligation.
    extensionality x'.
    unfold powerset_union.
    btauto.
  Qed.
  Next Obligation.
    extensionality x'.
    unfold powerset_union.
    btauto.
  Qed.
  Next Obligation.
    extensionality x'.
    unfold powerset_union.
    btauto.
  Qed.
  Next Obligation.
    apply powerset_union_commute.
  Qed.
  Next Obligation.
    extensionality x'.
    unfold powerset_multiplication.
    apply disj_false; intros.
    apply in_map_iff in H0.
    destruct H0 as [(x1, x2') [? ?]]; subst.
    btauto.
  Qed.
  Next Obligation.
    extensionality x'.
    unfold powerset_multiplication.
    apply disj_false; intros.
    apply in_map_iff in H0.
    destruct H0 as [(x1, x2') [? ?]]; subst.
    btauto.
  Qed.
  Next Obligation.
    apply powerset_union_multiply_distribute_left.
  Qed.
  Next Obligation.
    apply powerset_union_multiply_distribute_right.
  Qed.
  Next Obligation.
    transitivity (kleene_star_step M x (mono_fixpoint (kleene_star_step M x))).
    - unfold kleene_star_step.
      now rewrite powerset_union_commute.
    - apply mono_fixpoint_fixpoint.
      apply kleene_star_step_mono.
  Qed.
  Next Obligation.
    apply powerset_union_order.
    apply powerset_union_order in H0.
    rewrite <- kleene_star_step_offset_fixpoint.
    apply mono_fixpoint_least.
    - apply kleene_star_step_offset_mono.
    - now unfold kleene_star_step_offset.
  Qed.

  Equations kleene_interp
    {X: Type}
    (K: kleene_algebra X)
    (f: A -> X)
    (t: term)
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
    {X: Type}
    (K: kleene_algebra X)
    (f: A -> X)
    (t1 t2: term)
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
    - unfold kleene_multiply, kleene_unit.
      now rewrite monoid_unit_left.
    - unfold kleene_multiply, kleene_unit.
      now rewrite monoid_unit_right.
    - rewrite kleene_plus_commute.
      now rewrite kleene_star_unroll.
    - now apply kleene_star_fixpoint.
  Qed.
End StructurePowerset.

Section StructureFromAutomaton.
  Context {A: Type}.
  Notation automaton := (automaton A).
  Notation term := (term A).

  Program Definition automaton_monoid
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
  :
    monoid (Q -> Q -> bool)
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

  Definition automaton_kleene_algebra
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
  :
    kleene_algebra ((Q -> Q -> bool) -> bool)
  :=
    monoid_to_kleene_algebra (automaton_monoid aut)
  .

  Definition automaton_kleene_algebra_embed
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (a: A)
  :
    (Q -> Q -> bool) -> bool
  :=
    finite_eqb (aut_transitions aut a)
  .

  Lemma kleene_interp_witness_construct
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (t: term)
    (m: Q -> Q -> bool)
  :
    kleene_interp (automaton_kleene_algebra aut)
                  (automaton_kleene_algebra_embed aut)
                  t m = true ->
    exists w,
      automaton_transition_matrix aut w = m /\
      term_matches t w
  .
  Proof.
    revert aut m; dependent induction t; intros;
    autorewrite with derivative_write in H0;
    autorewrite with kleene_interp in H0;
    simpl in H0.
    - discriminate.
    - unfold kleene_unit in H0; simpl in H0.
      apply finite_eqb_eq in H0; subst.
      exists nil; intuition.
      constructor.
    - unfold automaton_kleene_algebra_embed in H0.
      apply finite_eqb_eq in H0; subst.
      exists (a :: nil).
      autorewrite with automaton_transition_matrix.
      rewrite matrix_product_bool_unit_right; intuition.
      constructor.
    - apply powerset_union_characterise in H0; destruct H0.
      + apply IHt1 in H0.
        destruct H0 as [w [? ?]].
        exists w; intuition.
        now constructor.
      + apply IHt2 in H0.
        destruct H0 as [w [? ?]].
        exists w; intuition.
        now constructor.
    - unfold kleene_multiply in H0; simpl in H0.
      apply powerset_multiplication_characterise in H0.
      destruct H0 as [m1 [m2 [? [? ?]]]]; subst.
      apply IHt1 in H0; destruct H0 as [w1 [? ?]]; subst.
      apply IHt2 in H1; destruct H1 as [w2 [? ?]]; subst.
      exists (w1 ++ w2); simpl.
      rewrite automaton_transition_matrix_app; intuition.
      now constructor.
    - unfold mono_fixpoint in H0; revert H0.
      match goal with
      | |- context [ length ?l ] => generalize (length l)
      end.
      intros n; revert m.
      induction n; simpl; intros.
      + discriminate.
      + unfold kleene_star_step in H0 at 1.
        apply powerset_union_characterise in H0.
        simpl in H0; destruct H0.
        * apply powerset_multiplication_characterise in H0.
          destruct H0 as [m1 [m2 [? [? ?]]]].
          apply IHn in H1; destruct H1 as [w2 [? ?]]; subst.
          apply IHt in H0; destruct H0 as [w1 [? ?]]; subst.
          exists (w1 ++ w2).
          rewrite automaton_transition_matrix_app.
          intuition (now constructor).
        * exists nil.
          apply finite_eqb_eq in H0; subst.
          intuition constructor.
  Qed.

  Lemma kleene_interp_witness_apply
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (t: term)
    (w: list A)
  :
    term_matches t w ->
    kleene_interp (automaton_kleene_algebra aut)
                  (automaton_kleene_algebra_embed aut)
                  t
                  (automaton_transition_matrix aut w)
      = true
  .
  Proof.
    intros; revert aut.
    dependent induction H0; intros;
    autorewrite with kleene_interp;
    autorewrite with automaton_transition_matrix;
    simpl.
    - unfold kleene_unit; simpl.
      now apply finite_eqb_eq.
    - unfold automaton_kleene_algebra_embed.
      apply finite_eqb_eq.
      now rewrite matrix_product_bool_unit_right.
    - apply powerset_union_characterise.
      rewrite IHterm_matches; intuition btauto.
    - apply powerset_union_characterise.
      rewrite IHterm_matches; intuition btauto.
    - unfold kleene_multiply; simpl.
      apply powerset_multiplication_characterise.
      exists (automaton_transition_matrix aut w1).
      exists (automaton_transition_matrix aut w2).
      intuition; simpl.
      now rewrite automaton_transition_matrix_app.
    - rewrite <- mono_fixpoint_fixpoint.
      + unfold kleene_star_step.
        apply powerset_union_characterise; right.
        now apply finite_eqb_eq.
      + apply kleene_star_step_mono.
    - rewrite <- mono_fixpoint_fixpoint.
      + unfold kleene_star_step at 1.
        apply powerset_union_characterise; left.
        apply powerset_multiplication_characterise.
        exists (automaton_transition_matrix aut w1).
        exists (automaton_transition_matrix aut w2).
        intuition.
        * specialize (IHterm_matches2 aut).
          now autorewrite with kleene_interp in IHterm_matches2.
        * now rewrite automaton_transition_matrix_app.
      + apply kleene_star_step_mono.
  Qed.
End StructureFromAutomaton.

Section StructureNormalForm.
  Context {A: Type}.
  Context `{Finite A}.
  Notation automaton := (automaton A).
  Notation term := (term A).

  Definition kleene_interp_recombine
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (q: Q)
  :
    term
  :=
    sum (
       map (automaton_relation_solution aut)
           (filter (kleene_interp (automaton_kleene_algebra aut)
                                  (automaton_kleene_algebra_embed aut)
                                  (compute_automaton_solution aut q))
                   finite_enum)
    )
  .

  Lemma automaton_kleene_algebra_interp_upper
    (t: term)
    (m: derivative A t -> derivative A t -> bool)
  :
    kleene_interp (automaton_kleene_algebra (automaton_antimirov t))
                  (automaton_kleene_algebra_embed (automaton_antimirov t))
                  t m = true ->
    automaton_relation_solution (automaton_antimirov t) m <= t
  .
  Proof.
    intros.
    apply kleene_interp_witness_construct in H0.
    destruct H0 as [w [? ?]].
    apply automaton_antimirov_accepts in H1.
    destruct H1 as [t' [? ?]].
    apply automaton_accepts_transition_matrix in H2.
    unfold vector_inner_product_bool in H2.
    apply disj_true in H2.
    apply in_map_iff in H2.
    destruct H2 as [t'' [? ?]].
    apply andb_prop in H2.
    destruct H2 as [? ?].
    eapply term_lequiv_trans.
    eapply automaton_relation_solution_bound.
    rewrite H0 in H2.
    apply H2.
    apply H4.
    eapply term_lequiv_trans.
    - apply antimirov_solution_upper_bound.
    - now apply initial_cover.
  Qed.

  Lemma automaton_kleene_algebra_interp_lower
    (t t': term)
  :
    t' <=
    sum (map
      (automaton_relation_solution (automaton_antimirov t))
      (filter
        (kleene_interp
          (automaton_kleene_algebra (automaton_antimirov t))
          (automaton_kleene_algebra_embed (automaton_antimirov t)) t')
        finite_enum)
    )
  .
  Proof.
    dependent induction t'.
    - apply term_lequiv_zero.
    - autorewrite with kleene_interp.
      eapply term_lequiv_trans; swap 1 2.
      + apply sum_lequiv_member.
        apply in_map_iff.
        eexists; intuition.
        apply filter_In; intuition.
        * apply finite_cover.
        * now apply finite_eqb_eq.
      + rewrite automaton_relation_solution_characterise.
        unfold automaton_relation_solution'.
        eapply automaton_solution_halt.
        * apply automaton_solution_invariant.
          apply compute_automaton_solution_least_solution.
        * now apply finite_eqb_eq.
    - autorewrite with kleene_interp.
      eapply term_lequiv_trans; swap 1 2.
      + apply sum_lequiv_member.
        apply in_map_iff.
        eexists; intuition.
        apply filter_In; intuition.
        * apply finite_cover.
        * now apply finite_eqb_eq.
      + rewrite automaton_relation_solution_characterise.
        unfold automaton_relation_solution'.
        eapply term_lequiv_trans; swap 1 2.
        * eapply automaton_solution_move with (a := a).
          -- apply automaton_solution_invariant.
             apply compute_automaton_solution_least_solution.
          -- now apply finite_eqb_eq.
        * rewrite matrix_product_bool_unit_left.
          rewrite <- ETimesUnitRight with (t := $a) at 1.
          apply times_mor_mono.
          -- apply term_lequiv_refl.
          -- eapply automaton_solution_halt.
             ++ apply automaton_solution_invariant.
                apply compute_automaton_solution_least_solution.
             ++ now apply finite_eqb_eq.
    - apply term_lequiv_split.
      + eapply term_lequiv_trans; eauto.
        apply sum_lequiv_containment;
        unfold incl; intro t'; intros.
        apply in_map_iff in H0.
        destruct H0 as [m [? ?]].
        apply filter_In in H1.
        destruct H1 as [_ ?].
        apply in_map_iff.
        exists m; intuition.
        apply filter_In; intuition.
        * apply finite_cover.
        * autorewrite with kleene_interp; simpl.
          unfold powerset_union.
          now rewrite H1.
      + eapply term_lequiv_trans; eauto.
        apply sum_lequiv_containment;
        unfold incl; intro t'; intros.
        apply in_map_iff in H0.
        destruct H0 as [m [? ?]].
        apply filter_In in H1.
        destruct H1 as [_ ?].
        apply in_map_iff.
        exists m; intuition.
        apply filter_In; intuition.
        * apply finite_cover.
        * autorewrite with kleene_interp; simpl.
          unfold powerset_union.
          rewrite H1; btauto.
    - eapply term_lequiv_trans.
      + apply times_mor_mono; eauto.
      + rewrite <- sum_distribute_left.
        apply sum_lequiv_all; intros.
        apply in_map_iff in H0.
        destruct H0 as [t'' [? ?]]; subst.
        apply in_map_iff in H1.
        destruct H1 as [m [? ?]]; subst.
        apply filter_In in H1.
        destruct H1 as [_ ?].
        rewrite <- sum_distribute_right.
        apply sum_lequiv_all; intros.
        apply in_map_iff in H1.
        destruct H1 as [t'' [? ?]]; subst.
        apply in_map_iff in H2.
        destruct H2 as [m' [? ?]]; subst.
        apply filter_In in H2.
        destruct H2 as [_ ?].
        eapply term_lequiv_trans;
        [apply automaton_relation_solution_merge |].
        apply sum_lequiv_member.
        apply in_map_iff.
        eexists; intuition.
        apply filter_In.
        intuition; [apply finite_cover|].
        autorewrite with kleene_interp.
        unfold kleene_multiply; simpl.
        unfold powerset_multiplication.
        apply disj_true.
        apply in_map_iff.
        exists (m', m).
        repeat rewrite andb_true_intro; intuition.
        * apply in_prod; apply finite_cover.
        * now apply finite_eqb_eq.
    - rewrite <- ETimesUnitRight with (t := t' *) at 1.
      apply EFixLeft.
      apply term_lequiv_split.
      + eapply term_lequiv_trans; [ apply times_mor_mono; now eauto |].
        rewrite <- sum_distribute_left.
        apply sum_lequiv_all; intros t'''; intros.
        apply in_map_iff in H0.
        destruct H0 as [t'' [? ?]]; subst.
        apply in_map_iff in H1.
        destruct H1 as [m [? ?]]; subst.
        apply filter_In in H1.
        destruct H1 as [_ ?].
        eapply term_lequiv_trans.
        apply times_mor_mono; eauto; reflexivity.
        rewrite <- sum_distribute_right.
        apply sum_lequiv_all; intros.
        apply in_map_iff in H1.
        destruct H1 as [t'' [? ?]]; subst.
        apply in_map_iff in H2.
        destruct H2 as [m' [? ?]]; subst.
        apply filter_In in H2.
        destruct H2 as [_ ?].
        eapply term_lequiv_trans;
        [ apply automaton_relation_solution_merge |].
        apply sum_lequiv_member.
        apply in_map_iff.
        eexists; intuition.
        apply filter_In; intuition.
        * apply finite_cover.
        * rewrite kleene_interp_sound with (t2 := t' ;; t' * + 1)
            by (apply EStarLeft).
          autorewrite with kleene_interp; simpl.
          unfold powerset_union.
          apply Bool.orb_true_intro; left.
          unfold kleene_multiply; simpl.
          unfold powerset_multiplication.
          apply disj_true.
          apply in_map_iff.
          exists (m', m); simpl.
          repeat rewrite andb_true_intro; intuition.
          -- apply in_prod; apply in_map_iff.
             ++ exists (uncurry m'); intuition.
                apply Finite.finite_subsets_finite_obligation_2.
             ++ exists (uncurry m); intuition.
                apply Finite.finite_subsets_finite_obligation_2.
          -- now apply finite_eqb_eq.
      + eapply term_lequiv_trans; swap 1 2.
        * apply sum_lequiv_member.
          apply in_map_iff.
          eexists; intuition.
          apply filter_In; intuition.
          -- apply finite_cover.
          -- rewrite kleene_interp_sound with (t2 := t';; t' * + 1)
               by apply EStarLeft.
             autorewrite with kleene_interp; simpl.
             unfold powerset_union.
             repeat rewrite Bool.orb_true_intro; intuition; right.
             unfold kleene_unit, monoid_unit; simpl.
             apply finite_eqb_eq; reflexivity.
        * rewrite automaton_relation_solution_characterise.
          unfold automaton_relation_solution'.
          eapply automaton_solution_halt.
          -- apply automaton_solution_invariant.
            apply compute_automaton_solution_least_solution.
          -- now apply finite_eqb_eq.
  Qed.

  Lemma kleene_interp_recombine_characterise
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (q: Q)
  :
     kleene_interp_recombine aut q == compute_automaton_solution aut q
  .
  Proof.
    unfold kleene_interp_recombine.
    rewrite <- (automaton_sum_accepting_matrices_characterise aut q) at 2.
    unfold automaton_sum_accepting_matrices.
    apply term_lequiv_squeeze.
    - apply sum_lequiv_all; intros.
      apply in_map_iff in H1.
      destruct H1 as [m [? ?]]; subst.
      apply filter_In in H2.
      destruct H2 as [_ ?].
      apply kleene_interp_witness_construct in H1.
      destruct H1 as [w [? ?]].
      apply sum_lequiv_member.
      apply in_map_iff.
      exists m; subst; intuition.
      unfold automaton_accepting_matrices.
      apply filter_In.
      split; [ apply finite_cover |].
      apply automaton_accepts_transition_matrix.
      rewrite <- automaton_least_solution_match.
      + apply H2.
      + rewrite automaton_least_solution_invariant.
        apply compute_automaton_solution_least_solution.
    - apply sum_lequiv_all; intros.
      apply in_map_iff in H1.
      destruct H1 as [? [? ?]]; subst.
      destruct (term_empty (automaton_relation_solution aut x)) eqn:?.
      + apply term_empty_zero in Heqb.
        rewrite Heqb.
        apply term_lequiv_zero.
      + apply term_empty_dec in Heqb.
        destruct Heqb as [w ?].
        * rewrite term_equiv_sound
            with (t2 := automaton_relation_solution' aut x)
            in H1 by (apply automaton_relation_solution_characterise).
          unfold automaton_relation_solution' in H1.
          apply automaton_transition_monad_solution in H1.
          rewrite matrix_product_bool_unit_left in H1; subst.
          apply sum_lequiv_member.
          apply in_map_iff.
          eexists; intuition.
          apply filter_In.
          split; [apply finite_cover |].
          apply kleene_interp_witness_apply.
          unfold automaton_accepting_matrices in H2.
          apply filter_In in H2.
          destruct H2 as [_ ?].
          rewrite automaton_least_solution_match.
          -- apply automaton_accepts_transition_matrix, H1.
          -- rewrite automaton_least_solution_invariant.
             apply compute_automaton_solution_least_solution;
             apply automaton_relation_solution_characterise.
  Qed.

  Lemma term_normal_form_left_pre
    (t1 t2: term)
  :
    let aut1 := automaton_coalesce (automaton_antimirov t1) initial_b in
    let aut2 := automaton_coalesce (automaton_antimirov t2) initial_b in
    let aut := automaton_coproduct aut1 aut2 in
    t1 == compute_automaton_solution aut (inl (inr tt))
  .
  Proof.
    intros.
    rewrite term_roundtrip_invariant at 1.
    unfold term_roundtrip.
    unfold antimirov_solution.
    transitivity (compute_automaton_solution aut1 (inr tt)).
    - subst aut1.
      rewrite (automaton_coalesce_solution _ initial_b (inr tt)).
      unfold automaton_coalesce_import_solution.
      apply sum_equiv_containment; intros t ?.
      + apply in_map_iff in H0.
        destruct H0 as [? [? ?]]; subst.
        apply initial_list in H1.
        apply in_map_iff.
        exists x.
        split; auto.
        apply filter_In.
        split; [apply finite_cover|].
        now apply initial_dec.
      + apply in_map_iff in H0.
        destruct H0 as [? [? ?]]; subst.
        apply filter_In in H1.
        destruct H1 as [_ ?].
        apply in_map_iff.
        exists x.
        split; auto.
        apply initial_list.
        now apply initial_dec.
    - now rewrite (automaton_coproduct_solution_left aut1 aut2 (inr tt)).
  Qed.

  Lemma term_normal_form_left
    (t1 t2: term)
  :
    let aut1 := automaton_antimirov t1 in
    let aut2 := automaton_antimirov t2 in
    let aut := automaton_coproduct (automaton_coalesce aut1 initial_b)
                                   (automaton_coalesce aut2 initial_b) in
    let rels := kleene_interp (automaton_kleene_algebra aut)
                              (automaton_kleene_algebra_embed aut) t1 in
    t1 == sum (map (automaton_relation_solution aut)
                   (filter rels finite_enum))
  .
  Proof.
    intros.
    rewrite term_normal_form_left_pre at 1.
    rewrite <- kleene_interp_recombine_characterise.
    unfold kleene_interp_recombine.
    erewrite kleene_interp_sound.
    - now subst aut1 aut2 aut rels.
    - now rewrite <- term_normal_form_left_pre.
  Qed.

  Lemma term_normal_form_right_pre
    (t1 t2: term)
  :
    let aut1 := automaton_coalesce (automaton_antimirov t1) initial_b in
    let aut2 := automaton_coalesce (automaton_antimirov t2) initial_b in
    let aut := automaton_coproduct aut1 aut2 in
    t2 == compute_automaton_solution aut (inr (inr tt))
  .
  Proof.
    intros.
    rewrite term_roundtrip_invariant at 1.
    unfold term_roundtrip.
    unfold antimirov_solution.
    transitivity (compute_automaton_solution aut2 (inr tt)).
    - subst aut2.
      rewrite (automaton_coalesce_solution _ initial_b (inr tt)).
      unfold automaton_coalesce_import_solution.
      apply sum_equiv_containment; intros t ?.
      + apply in_map_iff in H0.
        destruct H0 as [? [? ?]]; subst.
        apply initial_list in H1.
        apply in_map_iff.
        exists x.
        split; auto.
        apply filter_In.
        split; [apply finite_cover|].
        now apply initial_dec.
      + apply in_map_iff in H0.
        destruct H0 as [? [? ?]]; subst.
        apply filter_In in H1.
        destruct H1 as [_ ?].
        apply in_map_iff.
        exists x.
        split; auto.
        apply initial_list.
        now apply initial_dec.
    - now rewrite (automaton_coproduct_solution_right aut1 aut2 (inr tt)).
  Qed.

  Lemma term_normal_form_right
    (t1 t2: term)
  :
    let aut1 := automaton_antimirov t1 in
    let aut2 := automaton_antimirov t2 in
    let aut := automaton_coproduct (automaton_coalesce aut1 initial_b)
                                   (automaton_coalesce aut2 initial_b) in
    let rels := kleene_interp (automaton_kleene_algebra aut)
                              (automaton_kleene_algebra_embed aut) t2 in
    t2 == sum (map (automaton_relation_solution aut)
                   (filter rels finite_enum))
  .
  Proof.
    intros.
    rewrite term_normal_form_right_pre at 1.
    rewrite <- kleene_interp_recombine_characterise.
    unfold kleene_interp_recombine.
    erewrite kleene_interp_sound.
    - now subst aut1 aut2 aut rels.
    - now rewrite <- term_normal_form_right_pre.
  Qed.
End StructureNormalForm.
