Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.btauto.Btauto.
Require Import Coq.Program.Equality.

Require Import KA.Antimirov.
Require Import KA.Automata.
Require Import KA.Booleans.
Require Import KA.Finite.
Require Import KA.Scope.
Require Import KA.Terms.
Require Import KA.Vectors.
Require Import KA.Transformation.
Require Import KA.Solve.
Require Import KA.ModelTheory.
Require Import KA.Utilities.

Local Open Scope ka_scope.
Local Open Scope bool_scope.

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
    propify; handle_lists; intuition.
    - destruct H0 as [[? ?] [? ?]].
      propify; intuition.
      apply finite_eqb_eq in H0.
      firstorder.
    - destruct H0 as [x1' [x2' ?]]; intuition.
      exists (x1', x2'); propify; intuition.
      + now apply finite_eqb_eq.
      + replace (list_prod finite_enum finite_enum)
          with (finite_enum (X := (prod X X)))
          by reflexivity.
        apply finite_cover.
  Qed.

  Opaque powerset_multiplication.

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
    extensionality x; propify.
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
    extensionality x'; propify.
    rewrite powerset_multiplication_characterise; intuition.
    - destruct H0 as [x1' [x2' [? [? ?]]]].
      apply finite_eqb_eq in H1; subst.
      now rewrite monoid_unit_left.
    - exists x', (monoid_unit M); intuition.
      now apply finite_eqb_eq.
  Qed.
  Next Obligation.
    extensionality x'; propify.
    rewrite powerset_multiplication_characterise; intuition.
    - destruct H0 as [x1' [x2' [? [? ?]]]].
      apply finite_eqb_eq in H0; subst.
      now rewrite monoid_unit_right.
    - exists (monoid_unit M), x'; intuition.
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
    extensionality x; propify; intuition.
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
    propify; intuition.
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
    - extensionality x; propify; intuition.
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
    extensionality x'; unfold powerset_union; propify.
    repeat rewrite powerset_multiplication_characterise; propify.
    firstorder; propify.
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
    extensionality x'; propify.
    unfold powerset_union; propify.
    repeat rewrite powerset_multiplication_characterise.
    propify; firstorder.
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
    - extensionality x; symmetry.
      propify; intuition.
      apply powerset_multiplication_characterise in H1.
      destruct H1 as [x1' [x2' ?]]; intuition.
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
    simpl; unfold powerset_union.
    propify; firstorder.
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
    extensionality x'; propify; intuition.
    apply powerset_multiplication_characterise in H0.
    destruct H0 as [? [? ?]]; intuition.
  Qed.
  Next Obligation.
    extensionality x'; propify; intuition.
    apply powerset_multiplication_characterise in H0.
    destruct H0 as [? [? ?]]; intuition.
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
    {X: Type}
    `{Finite X}
    (M: monoid X)
    (t: term)
    (h: A -> X)
    (x: X)
  :
    let h' a := finite_eqb (h a) in
    kleene_interp (monoid_to_kleene_algebra M) h' t x = true ->
    exists w, monoid_interp M h w = x /\ term_matches t w
  .
  Proof.
    revert x; dependent induction t; intros;
    autorewrite with kleene_interp in H0;
    simpl in H0.
    - discriminate.
    - unfold kleene_unit in H0; simpl in H0.
      apply finite_eqb_eq in H0; subst.
      exists nil; intuition.
      constructor.
    - apply finite_eqb_eq in H0; subst.
      exists (a :: nil); intuition.
      + autorewrite with monoid_interp.
        now rewrite monoid_unit_left.
      + constructor.
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
      exists (w1 ++ w2); intuition.
      + apply monoid_interp_app.
      + now constructor.
    - unfold mono_fixpoint in H0; revert H0.
      match goal with
      | |- context [ length ?l ] => generalize (length l)
      end.
      intros n; revert x.
      induction n; simpl; intros.
      + discriminate.
      + unfold kleene_star_step in H0 at 1.
        apply powerset_union_characterise in H0.
        simpl in H0; destruct H0.
        * apply powerset_multiplication_characterise in H0.
          destruct H0 as [m1 [m2 [? [? ?]]]].
          apply IHn in H1; destruct H1 as [w2 [? ?]]; subst.
          apply IHt in H0; destruct H0 as [w1 [? ?]]; subst.
          exists (w1 ++ w2); intuition.
          -- apply monoid_interp_app.
          -- now now constructor.
        * exists nil.
          apply finite_eqb_eq in H0; subst.
          intuition constructor.
  Qed.

  Lemma kleene_interp_witness_apply
    {X: Type}
    `{Finite X}
    (M: monoid X)
    (t: term)
    (h: A -> X)
    (w: list A)
  :
    let h' a := finite_eqb (h a) in
    term_matches t w ->
    kleene_interp (monoid_to_kleene_algebra M) h' t
                  (monoid_interp M h w) = true
  .
  Proof.
    simpl; intros.
    dependent induction H0; intros;
    autorewrite with kleene_interp;
    simpl.
    - unfold kleene_unit; simpl.
      now apply finite_eqb_eq.
    - apply finite_eqb_eq.
      autorewrite with monoid_interp.
      now rewrite monoid_unit_left.
    - apply powerset_union_characterise.
      rewrite IHterm_matches; intuition btauto.
    - apply powerset_union_characterise.
      rewrite IHterm_matches; intuition btauto.
    - unfold kleene_multiply; simpl.
      apply powerset_multiplication_characterise.
      exists (monoid_interp M h w1).
      exists (monoid_interp M h w2).
      intuition; simpl.
      now rewrite monoid_interp_app.
    - rewrite <- mono_fixpoint_fixpoint.
      + unfold kleene_star_step.
        apply powerset_union_characterise; right.
        now apply finite_eqb_eq.
      + apply kleene_star_step_mono.
    - rewrite <- mono_fixpoint_fixpoint.
      + unfold kleene_star_step at 1.
        apply powerset_union_characterise; left.
        apply powerset_multiplication_characterise.
        exists (monoid_interp M h w1).
        exists (monoid_interp M h w2).
        intuition.
        now rewrite monoid_interp_app.
      + apply kleene_star_step_mono.
  Qed.

  Lemma automaton_transition_matrix_monoid_interp
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (w: list A)
  :
    automaton_transition_matrix aut w =
    monoid_interp (automaton_monoid aut) (aut_transitions aut) w
  .
  Proof.
    induction w;
    autorewrite with monoid_interp;
    autorewrite with automaton_transition_matrix;
    simpl; congruence.
  Qed.

  Lemma automaton_kleene_algebra_interp_upper
    `{Finite A}
    (t: term)
    (m: derivative A t -> derivative A t -> bool)
  :
    kleene_interp (automaton_kleene_algebra (automaton_antimirov t))
                  (automaton_kleene_algebra_embed (automaton_antimirov t))
                  t m = true ->
    automaton_relation_solution (automaton_antimirov t) m finite_eqb <= t
  .
  Proof.
    intros.
    apply kleene_interp_witness_construct in H0.
    destruct H0 as [w [? ?]].
    apply automaton_antimirov_accepts in H1.
    destruct H1 as [t' [? ?]].
    apply automaton_accepts_transition_matrix in H2.
    unfold vector_inner_product_bool in H2.
    propify; handle_lists; propify; intuition.
    eapply term_lequiv_trans.
    - eapply automaton_relation_solution_bound; eauto.
      rewrite <- H0, <- automaton_transition_matrix_monoid_interp; eauto.
    - eapply term_lequiv_trans.
      + apply antimirov_solution_upper_bound.
      + now apply initial_cover.
  Qed.

  Lemma automaton_kleene_algebra_interp_lower_letter
    `{Finite A}
    (a: A)
    (t: term)
  :
    $ a <=
    sum (map
      (fun m => automaton_relation_solution (automaton_antimirov t) m finite_eqb)
      (filter (automaton_kleene_algebra_embed (automaton_antimirov t) a) finite_enum)
    )
  .
  Proof.
    eapply term_lequiv_trans; swap 1 2.
    - apply sum_lequiv_member.
      handle_lists; eexists; intuition.
      handle_lists; intuition.
      + apply finite_cover.
      + now apply finite_eqb_eq.
    - apply automaton_relation_solution_letter.
  Qed.

  Lemma automaton_kleene_algebra_interp_lower
    `{Finite A}
    (t t': term)
  :
    t' <=
    sum (map
      (fun m => automaton_relation_solution (automaton_antimirov t) m finite_eqb)
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
        handle_lists; eexists; intuition.
        handle_lists; intuition.
        * apply finite_cover.
        * now apply finite_eqb_eq.
      + unfold automaton_relation_solution.
        eapply automaton_solution_halt.
        * apply automaton_solution_invariant.
          apply compute_automaton_solution_least_solution.
        * now apply finite_eqb_eq.
    - autorewrite with kleene_interp.
      apply automaton_kleene_algebra_interp_lower_letter.
    - apply term_lequiv_split.
      + eapply term_lequiv_trans; eauto.
        apply sum_lequiv_containment;
        unfold incl; intro t'; intros.
        repeat handle_lists; eexists; intuition.
        handle_lists; intuition.
        autorewrite with kleene_interp; simpl.
        unfold powerset_union.
        now rewrite H3.
      + eapply term_lequiv_trans; eauto.
        apply sum_lequiv_containment;
        unfold incl; intro t'; intros.
        repeat handle_lists; eexists; intuition.
        handle_lists; intuition.
        autorewrite with kleene_interp; simpl.
        unfold powerset_union.
        rewrite H3; btauto.
    - eapply term_lequiv_trans.
      + apply times_mor_mono; eauto.
      + rewrite <- sum_distribute_left.
        apply sum_lequiv_all; intros.
        repeat handle_lists; intuition; subst.
        rewrite <- sum_distribute_right.
        apply sum_lequiv_all; intros.
        repeat handle_lists; intuition; subst.
        eapply term_lequiv_trans;
        [apply automaton_relation_solution_merge |].
        apply sum_lequiv_member.
        repeat handle_lists; eexists; intuition.
        handle_lists; intuition; try apply finite_cover.
        autorewrite with kleene_interp.
        unfold kleene_multiply; simpl.
        unfold powerset_multiplication.
        propify; intuition.
        handle_lists; exists (x0, x).
        propify; intuition.
        * now apply finite_eqb_eq.
        * apply in_prod; apply finite_cover.
    - rewrite <- ETimesUnitRight with (t := t' *) at 1.
      apply EFixLeft.
      apply term_lequiv_split.
      + eapply term_lequiv_trans; [ apply times_mor_mono; now eauto |].
        rewrite <- sum_distribute_left.
        apply sum_lequiv_all; intros t'''; intros.
        repeat handle_lists; intuition; subst.
        rewrite <- sum_distribute_right.
        apply sum_lequiv_all; intros.
        repeat handle_lists; intuition; subst.
        eapply term_lequiv_trans;
        [ apply automaton_relation_solution_merge |].
        apply sum_lequiv_member.
        handle_lists; eexists; intuition.
        handle_lists; intuition.
        * apply finite_cover.
        * rewrite kleene_interp_sound with (t2 := t' ;; t' * + 1)
            by (apply EStarLeft).
          autorewrite with kleene_interp; simpl.
          unfold powerset_union.
          propify; intuition; left.
          handle_lists; exists (x0, x).
          propify; intuition.
          -- now apply finite_eqb_eq.
          -- apply in_prod; intuition.
      + eapply term_lequiv_trans; swap 1 2.
        * apply sum_lequiv_member.
          handle_lists; eexists; intuition.
          handle_lists; intuition.
          -- apply finite_cover.
          -- rewrite kleene_interp_sound with (t2 := t';; t' * + 1)
               by apply EStarLeft.
             autorewrite with kleene_interp; simpl.
             unfold powerset_union.
             propify; intuition; right.
             unfold kleene_unit, monoid_unit; simpl.
             apply finite_eqb_eq; reflexivity.
        * unfold automaton_relation_solution.
          eapply automaton_solution_halt.
          -- apply automaton_solution_invariant.
            apply compute_automaton_solution_least_solution.
          -- now apply finite_eqb_eq.
  Qed.
End StructureFromAutomaton.
