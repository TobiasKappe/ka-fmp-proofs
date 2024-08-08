Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Require Import KA.Booleans.
Require Import KA.Finite.
Require Import KA.Automata.
Require Import KA.Solve.
Require Import KA.Terms.
Require Import KA.Vectors.
Require Import KA.Utilities.

Local Open Scope ka_scope.

Section AutomatonTransformationMonoid.
  Context {A: Type}.
  Context `{Finite A}.
  Notation automaton := (automaton A).
  Notation vector := (vector A).
  Notation term := (term A).

  Definition automaton_transition_monad
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (final: Q -> Q -> bool)
  :
    automaton (Q -> Q -> bool)
  := {|
    aut_transitions a m1 m2 :=
      finite_eqb (matrix_product_bool m1 (aut_transitions aut a)) m2;
    aut_accept m :=
      finite_eqb m final;
  |}.

  Equations automaton_transition_matrix
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (w: list A)
  :
    Q -> Q -> bool
  := {
    automaton_transition_matrix aut nil := finite_eqb;
    automaton_transition_matrix aut (a :: w) :=
      matrix_product_bool (aut_transitions aut a)
                          (automaton_transition_matrix aut w)
  }.

  Lemma automaton_transition_matrix_app
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (w1 w2: list A)
  :
    automaton_transition_matrix aut (w1 ++ w2) =
    matrix_product_bool (automaton_transition_matrix aut w1)
                        (automaton_transition_matrix aut w2)
  .
  Proof.
    induction w1; autorewrite with automaton_transition_matrix; simpl.
    - now rewrite matrix_product_bool_unit_left.
    - rewrite matrix_product_bool_associative.
      now rewrite <- IHw1.
  Qed.

  Lemma automaton_transition_monad_accepts
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (initial final: Q -> Q -> bool)
    (w: list A)
  :
    automaton_accepts (automaton_transition_monad aut final) initial w <->
    matrix_product_bool initial (automaton_transition_matrix aut w) = final
  .
  Proof.
    revert initial; induction w; intros initial;
    autorewrite with automaton_transition_matrix.
    - rewrite matrix_product_bool_unit_right.
      split; intros.
      + dependent destruction H1.
        simpl in H1.
        now rewrite finite_eqb_eq in H1.
      + constructor.
        simpl; subst.
        now apply finite_eqb_eq.
    - split; intros.
      + dependent destruction H1.
        simpl in H1.
        apply finite_eqb_eq in H1.
        subst.
        rewrite <- matrix_product_bool_associative.
        now apply IHw.
      + apply AcceptsStep
          with (q' := matrix_product_bool initial (aut_transitions aut a)).
        * now apply finite_eqb_eq.
        * apply IHw.
          now rewrite matrix_product_bool_associative.
  Qed.

  Definition automaton_relation_solution
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (m: Q -> Q -> bool)
  :=
    compute_automaton_solution (automaton_transition_monad aut m)
  .

  Lemma automaton_relation_solution_letter
    (a: A)
    (Q: Type)
    `{Finite Q}
    (aut: automaton Q)
  :
    $ a <= automaton_relation_solution aut (aut_transitions aut a) finite_eqb
  .
  Proof.
    eapply term_lequiv_trans; swap 1 2.
    - eapply automaton_solution_move with (a := a).
      + apply automaton_solution_invariant.
        apply compute_automaton_solution_least_solution.
      + now apply finite_eqb_eq.
    - rewrite matrix_product_bool_unit_left.
      rewrite <- ETimesUnitRight with (t := $a) at 1.
      apply times_mor_mono.
      + apply term_lequiv_refl.
      + eapply automaton_solution_halt.
        * apply automaton_solution_invariant.
          apply compute_automaton_solution_least_solution.
        * now apply finite_eqb_eq.
  Qed.

  Definition automaton_relation_solution_shifted
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (f g h: Q -> Q -> bool)
  :=
    automaton_relation_solution aut (matrix_product_bool g f) (matrix_product_bool g h)
  .

  Lemma automaton_relation_solution_shift
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (f g h: Q -> Q -> bool)
  :
    automaton_relation_solution aut f g <=
    automaton_relation_solution aut
      (matrix_product_bool h f)
      (matrix_product_bool h g)
  .
  Proof.
    unfold automaton_relation_solution at 1.
    rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
    replace (automaton_relation_solution aut _ _)
      with (automaton_relation_solution_shifted aut f h g)
      by reflexivity.
    apply compute_automaton_solution_least_solution; split; intros.
    - unfold automaton_relation_solution_shifted.
      unfold automaton_relation_solution.
      eapply automaton_solution_move.
      + apply automaton_solution_invariant.
        apply compute_automaton_solution_least_solution.
      + apply finite_eqb_eq.
        apply finite_eqb_eq in H1; subst.
        apply matrix_product_bool_associative.
    - apply finite_eqb_eq in H1; subst.
      unfold automaton_relation_solution_shifted.
      unfold automaton_relation_solution.
      eapply automaton_solution_halt.
      + apply automaton_solution_invariant.
        apply compute_automaton_solution_least_solution.
      + now apply finite_eqb_eq.
  Qed.

  Lemma automaton_relation_solution_merge
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (f g: Q -> Q -> bool)
  :
    automaton_relation_solution aut f finite_eqb ;;
    automaton_relation_solution aut g finite_eqb <=
    automaton_relation_solution aut (matrix_product_bool f g) finite_eqb
  .
  Proof.
    unfold automaton_relation_solution at 1.
    apply compute_automaton_solution_least_solution; split; intros.
    - unfold automaton_relation_solution at 2;
      unfold automaton_relation_solution at 2.
      eapply automaton_solution_move.
      + apply automaton_solution_invariant.
        apply compute_automaton_solution_least_solution.
      + auto.
    - apply finite_eqb_eq in H1; subst.
      replace f with (matrix_product_bool f finite_eqb) at 2
        by apply matrix_product_bool_unit_right.
      replace f with (matrix_product_bool f finite_eqb) at 4
        by apply matrix_product_bool_unit_right.
      apply automaton_relation_solution_shift.
  Qed.

  Definition automaton_sum_reached_paths
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (q: Q)
    (m: Q -> Q -> bool)
  :
    term
  :=
    sum (map (compute_automaton_solution aut) (filter (m q) finite_enum))
  .

  Lemma automaton_transition_monad_solution_upper
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (q q': Q)
    (m m': Q -> Q -> bool)
  :
    m q q' = true ->
    aut_accept aut q' = true ->
    compute_automaton_solution (automaton_transition_monad aut m) m' <=
    automaton_sum_reached_paths aut q m'
  .
  Proof.
    intros.
    rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
    apply compute_automaton_solution_least_solution.
    clear m'.
    split.
    - intros a m1 m2 ?; unfold automaton_sum_reached_paths.
      rewrite <- sum_distribute_left.
      rewrite map_map.
      apply sum_lequiv_all; intros.
      repeat (handle_lists; subst); intuition.
      apply finite_eqb_eq in H3; subst.
      apply matrix_product_characterise in H6.
      destruct H6 as [q3 [? ?]].
      apply term_lequiv_trans with (t2 := compute_automaton_solution aut q3).
      + rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut x).
        rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q3).
        now apply compute_automaton_solution_least_solution.
      + apply sum_lequiv_member.
        handle_lists; eexists; intuition.
        handle_lists; intuition.
    - intros m' ?; unfold automaton_sum_reached_paths.
      simpl in H3.
      apply finite_eqb_eq in H3; subst.
      apply term_lequiv_trans with (t2 := compute_automaton_solution aut q').
      + rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q').
        now apply compute_automaton_solution_least_solution.
      + apply sum_lequiv_member.
        handle_lists; eexists; intuition.
        handle_lists; intuition.
  Qed.

  Definition automaton_sum_accepting_matrices
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (q: Q)
    (m: Q -> Q -> bool)
  :=
    sum (map (compute_automaton_solution aut)
             (filter (m q) finite_enum))
  .

  Lemma automaton_relation_solution_bound
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (m: Q -> Q -> bool)
    (q q': Q)
  :
    m q q' = true ->
    aut_accept aut q' = true ->
    automaton_relation_solution aut m finite_eqb <= compute_automaton_solution aut q
  .
  Proof.
    intros.
    rewrite <- ETimesUnitRight with (t := automaton_relation_solution aut m finite_eqb).
    unfold automaton_relation_solution.
    eapply term_lequiv_trans with (t2 := automaton_sum_accepting_matrices aut q finite_eqb).
    - apply compute_automaton_solution_least_solution; split; intros.
      + unfold automaton_sum_accepting_matrices.
        rewrite <- sum_distribute_left.
        apply sum_lequiv_all; intros.
        repeat (handle_lists; subst); intuition.
        apply finite_eqb_eq in H3; subst.
        unfold matrix_product_bool in H6.
        unfold vector_inner_product_bool in H6.
        apply disj_true in H6.
        handle_lists.
        apply andb_prop in H3; destruct H3.
        eapply term_lequiv_trans; swap 1 2.
        * apply sum_lequiv_member.
          handle_lists; eexists; intuition.
          handle_lists; intuition.
        * eapply automaton_solution_move; eauto.
          apply automaton_solution_invariant.
          apply compute_automaton_solution_least_solution.
      + simpl in H3.
        apply finite_eqb_eq in H3; subst.
        unfold automaton_sum_accepting_matrices.
        eapply term_lequiv_trans; swap 1 2.
        * apply sum_lequiv_member.
          handle_lists; eexists; intuition.
          handle_lists; intuition.
        * eapply automaton_solution_halt; eauto.
          apply automaton_solution_invariant.
          apply compute_automaton_solution_least_solution.
    - unfold automaton_sum_accepting_matrices.
      apply sum_lequiv_all; intros.
      repeat handle_lists; intuition; subst.
      apply finite_eqb_eq in H6; subst.
      apply term_lequiv_refl.
  Qed.

  Lemma automaton_accepts_transition_matrix
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (q: Q)
    (w: list A)
  :
    automaton_accepts aut q w <->
    vector_inner_product_bool ((automaton_transition_matrix aut w) q)
                              (aut_accept aut) = true
  .
  Proof.
    unfold vector_inner_product_bool.
    rewrite disj_true.
    handle_lists.
    setoid_rewrite Bool.andb_true_iff.
    revert q; induction w; intros.
    - firstorder.
      + inversion H1; subst.
        exists q; intuition.
        autorewrite with automaton_transition_matrix.
        now apply finite_eqb_eq.
      + apply AcceptsEmpty.
        autorewrite with automaton_transition_matrix in H1.
        apply finite_eqb_eq in H1.
        congruence.
    - split; intros.
      + inversion H1; subst.
        apply IHw in H6.
        destruct H6 as [qf [[? ?] _]].
        exists qf; intuition.
        autorewrite with automaton_transition_matrix.
        apply matrix_product_characterise.
        now exists q'.
      + destruct H1 as [qf [[? ?] _]].
        autorewrite with automaton_transition_matrix in H1.
        apply matrix_product_characterise in H1.
        destruct H1 as [q' [? ?]].
        apply AcceptsStep with (q' := q'); auto.
        apply IHw.
        now exists qf; intuition.
  Qed.
End AutomatonTransformationMonoid.
