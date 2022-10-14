Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Local Open Scope program_scope.

Require Import KA.Finite.
Require Import KA.Terms.
Require Import KA.Vectors.
Require Import KA.Solve.
Local Open Scope ka_scope.

Section Automaton.
  Variable (A: Type).

  Record automaton (Q: Type) := {
    aut_transitions: A -> Q -> Q -> bool;
    aut_accept: Q -> bool;
  }.
End Automaton.

Arguments aut_transitions {A} {Q}.
Arguments aut_accept {A} {Q}.

Section AutomatonMorphism.
  Context {A: Type}.
  Notation automaton := (automaton A).

  Record automaton_homomorphism
    {Q1 Q2: Type}
    (aut1: automaton Q1)
    (aut2: automaton Q2)
  := {
    automaton_homomorphism_f :> Q1 -> Q2;
    automaton_homomorphism_compatible:
      forall (a: A) (q1 q1': Q1),
      aut_transitions aut1 a q1 q1' = true ->
      aut_transitions aut2 a (automaton_homomorphism_f q1)
                             (automaton_homomorphism_f q1') = true;
    automaton_homomorphism_preserve:
      forall (q1: Q1),
      aut_accept aut1 q1 = true ->
      aut_accept aut2 (automaton_homomorphism_f q1) = true;
  }.
End AutomatonMorphism.

Arguments automaton_homomorphism_f {A} {Q1} {Q2} {aut1} {aut2}.

Section AutomatonSolution.
  Context {A: Type}.
  Context `{Finite A}.
  Notation automaton := (automaton A).
  Notation term := (term A).
  Notation vector := (vector A).
  Notation system := (system A).

  Record automaton_solution
    {Q: Type}
    (aut: automaton Q)
    (scale: term)
    (sol: vector Q)
  := {
    automaton_solution_move:
      forall (a: A) (q1 q2: Q),
      aut_transitions aut a q1 q2 = true ->
      $a ;; sol q2 <= sol q1;
    automaton_solution_halt:
      forall (q: Q),
      aut_accept aut q = true ->
      scale <= sol q;
  }.

  Record automaton_least_solution
    {Q: Type}
    (aut: automaton Q)
    (scale: term)
    (sol: vector Q)
  := {
    automaton_least_solution_solution:
      automaton_solution aut scale sol;
    automaton_least_solution_least:
      forall (sol': vector Q),
      automaton_solution aut scale sol' ->
      sol <== sol'
  }.

  Lemma automaton_homomorphism_solution
    {Q1 Q2: Type}
    (aut1: automaton Q1)
    (aut2: automaton Q2)
    (scale: term)
    (sol: vector Q2)
    (h: automaton_homomorphism aut1 aut2)
  :
    automaton_solution aut2 scale sol ->
    automaton_solution aut1 scale (sol ∘ h)
  .
  Proof.
    split; intros.
    - unfold compose; simpl.
      apply H0 with (q1 := h q1).
      now apply h.
    - unfold compose; simpl.
      apply H0.
      now apply h.
  Qed.

  Lemma automaton_homomorphism_least_solution
    {Q1 Q2: Type}
    (aut1: automaton Q1)
    (aut2: automaton Q2)
    (scale: term)
    (sol1: vector Q1)
    (sol2: vector Q2)
    (h: automaton_homomorphism aut1 aut2)
  :
    automaton_least_solution aut1 scale sol1 ->
    automaton_least_solution aut2 scale sol2 ->
    sol1 <== sol2 ∘ h
  .
  Proof.
    intros.
    apply H0.
    apply automaton_homomorphism_solution.
    apply H1.
  Qed.

  Definition automaton_to_system
    {Q: Type}
    (aut: automaton Q)
    : system Q
  := {|
    smat q q' :=
      sum (map letter (filter (fun a => aut_transitions aut a q q') finite_enum));
    svec q :=
      if aut_accept aut q then 1 else 0;
  |}.

  Lemma system_solution_to_automaton_solution
    {Q: Type}
    (aut: automaton Q)
    (scale: term)
    (sol: vector Q)
  :
    solution (automaton_to_system aut) scale sol ->
    automaton_solution aut scale sol
  .
  Proof.
    intros.
    split; intros.
    - match goal with
      | |- ?lhs <= ?rhs => fold (term_lequiv lhs rhs)
      end.
      enough (term_lequiv ($ a) (smat (automaton_to_system aut) q1 q2)).
      + rewrite H2.
        unfold term_lequiv.
        apply H0.
      + unfold term_lequiv; simpl.
        apply sum_lequiv_member.
        apply in_map_iff.
        exists a.
        split; auto.
        apply filter_In.
        split; auto.
        apply finite_cover.
    - enough (svec (automaton_to_system aut) q == 1).
      + rewrite <- ETimesUnitLeft with (t := scale).
        rewrite <- H2.
        apply H0.
      + simpl.
        now rewrite H1.
  Qed.

  Lemma automaton_solution_to_system_solution
    {Q: Type}
    (aut: automaton Q)
    (scale: term)
    (sol: vector Q)
  :
    automaton_solution aut scale sol ->
    solution (automaton_to_system aut) scale sol
  .
  Proof.
    intros.
    split; intros.
    - simpl.
      rewrite <- sum_distribute_right.
      apply sum_lequiv_all; intros.
      rewrite map_map in H1.
      apply in_map_iff in H1.
      destruct H1 as [a [? ?]].
      subst.
      apply filter_In in H2.
      destruct H2 as [_ ?].
      apply H0.
      apply H1.
    - simpl.
      destruct (aut_accept aut q) eqn:?.
      + rewrite ETimesUnitLeft.
        now apply H0.
      + rewrite ETimesZeroRight.
        apply term_lequiv_zero.
  Qed.

  Definition compute_automaton_solution
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
  :
    vector Q
  :=
    compute_solution (automaton_to_system aut)
  .

  Lemma compute_automaton_solution_least_solution
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (scale: term)
  :
    automaton_least_solution aut scale (compute_automaton_solution aut ;;; scale)
  .
  Proof.
    split; intros.
    - unfold compute_automaton_solution.
      apply system_solution_to_automaton_solution.
      apply compute_solution_least_solution.
    - unfold compute_automaton_solution.
      apply compute_solution_least_solution.
      now apply automaton_solution_to_system_solution.
  Qed.

  Lemma automaton_solution_invariant
    {Q: Type}
    (aut: automaton Q)
    (scale: term)
    (sol: vector Q)
  :
    automaton_solution aut scale sol <->
    automaton_solution aut scale (sol ;;; 1)
  .
  Proof.
    split; intros.
    - split; intros.
      + unfold vector_scale_right.
        repeat rewrite ETimesUnitRight.
        now apply H0.
      + unfold vector_scale_right.
        rewrite ETimesUnitRight.
        now apply H0.
    - split; intros.
      + unfold vector_scale_right.
        rewrite <- ETimesUnitRight with (t := sol q2).
        rewrite <- ETimesUnitRight with (t := sol q1).
        now apply H0.
      + unfold vector_scale_right.
        rewrite <- ETimesUnitRight with (t := sol q).
        now apply H0.
  Qed.

  Lemma automaton_least_solution_invariant
    {Q: Type}
    (aut: automaton Q)
    (scale: term)
    (sol: vector Q)
  :
    automaton_least_solution aut scale sol <->
    automaton_least_solution aut scale (sol ;;; 1)
  .
  Proof.
    split; intros.
    - split; intros.
      + rewrite <- automaton_solution_invariant.
        apply H0.
      + intro q; unfold vector_scale_right.
        rewrite ETimesUnitRight.
        now apply H0.
    - split; intros.
      + rewrite automaton_solution_invariant.
        apply H0.
      + intro q.
        rewrite <- ETimesUnitRight with (t := sol q).
        now apply H0.
  Qed.

  Definition automaton_perturb
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (scale: term)
    (s: vector Q)
    (q: Q)
  :
    term
  :=
    (if aut_accept aut q then scale else 0) +
    sum (map (fun q' =>
        sum (map (fun a =>
            if aut_transitions aut a q q'
            then $a ;; s q' else 0
        ) finite_enum)
    ) finite_enum)
  .

  Lemma automaton_perturb_mono
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (scale: term)
    (s1 s2: vector Q)
  :
    s1 <== s2 ->
    automaton_perturb aut scale s1 <== automaton_perturb aut scale s2
  .
  Proof.
    intros; intro q.
    unfold automaton_perturb.
    apply term_lequiv_split.
    - apply term_lequiv_split_left.
      apply term_lequiv_refl.
    - apply term_lequiv_split_right.
      apply sum_lequiv_all; intros.
      apply in_map_iff in H2.
      destruct H2 as [q' [? ?]]; subst.
      eapply term_lequiv_trans; swap 1 2.
      + eapply sum_lequiv_member.
        apply in_map_iff.
        exists q'.
        split; auto.
      + apply sum_lequiv_all; intros.
        apply in_map_iff in H2.
        destruct H2 as [a [? ?]]; subst.
        destruct (aut_transitions aut a q q') eqn:?.
        * eapply term_lequiv_trans; swap 1 2.
          -- apply sum_lequiv_member.
             apply in_map_iff.
             exists a.
             split; auto.
          -- rewrite Heqb.
             apply times_mor_mono.
             ++ apply term_lequiv_refl.
             ++ apply H1.
        * apply term_lequiv_zero.
  Qed.

  Lemma automaton_solution_perturb
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (scale: term)
    (sol: vector Q)
  :
    automaton_solution aut scale sol <->
    automaton_perturb aut scale sol <== sol
  .
  Proof.
    split; intros.
    - intro q.
      unfold vector_scale_right.
      unfold automaton_perturb.
      apply term_lequiv_split.
      + destruct (aut_accept aut q) eqn:?.
        * now apply H1.
        * apply term_lequiv_zero.
      + apply sum_lequiv_all; intros.
        apply in_map_iff in H2.
        destruct H2 as [q' [? ?]]; subst.
        apply sum_lequiv_all; intros.
        apply in_map_iff in H2.
        destruct H2 as [a [? ?]]; subst.
        destruct (aut_transitions aut a q q') eqn:?.
        * now apply H1.
        * apply term_lequiv_zero.
    - split; intros.
      + apply term_lequiv_trans with (t2 := automaton_perturb aut scale sol q1).
        * unfold automaton_perturb.
          apply term_lequiv_split_right.
          eapply term_lequiv_trans; swap 1 2.
          -- apply sum_lequiv_member.
             apply in_map_iff.
             eexists; split; auto.
             apply finite_cover.
          -- apply sum_lequiv_member.
             apply in_map_iff.
             exists a.
             rewrite H2.
             split; auto.
             apply finite_cover.
        * apply H1.
      + eapply term_lequiv_trans with (t2 := automaton_perturb aut scale sol q).
        * unfold automaton_perturb.
          apply term_lequiv_split_left.
          rewrite H2.
          apply term_lequiv_refl.
        * apply H1.
  Qed.

  Lemma automaton_solution_iterate
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (scale: term)
    (sol: vector Q)
  :
    automaton_solution aut scale sol ->
    automaton_solution aut scale (automaton_perturb aut scale sol)
  .
  Proof.
    intros.
    apply automaton_solution_perturb.
    apply automaton_perturb_mono.
    now apply automaton_solution_perturb.
  Qed.

  Lemma automaton_solution_least_converse
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (scale: term)
    (sol: vector Q)
    (q: Q)
  :
    automaton_least_solution aut scale sol ->
    sol q == automaton_perturb aut scale sol q
  .
  Proof.
    intros.
    apply vector_lequiv_squeeze.
    - apply H1.
      apply automaton_solution_iterate.
      apply H1.
    - apply automaton_solution_perturb.
      apply H1.
  Qed.
End AutomatonSolution.
