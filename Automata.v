Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Local Open Scope program_scope.
Local Open Scope bool_scope.

Require Import KA.Finite.
Require Import KA.Booleans.
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
    automaton_solution aut1 scale (sol ??? h)
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
    sol1 <== sol2 ??? h
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

Section AutomatonLanguage.
  Context {A: Type}.
  Context `{Finite A}.
  Notation automaton := (automaton A).
  Notation vector := (vector A).
  Notation term := (vector A).

  Inductive automaton_accepts
    {Q: Type}
    (aut: automaton Q)
  :
    Q -> list A -> Prop
  :=
  | AcceptsEmpty:
    forall (q: Q),
    aut_accept aut q = true ->
    automaton_accepts aut q nil
  | AcceptsStep:
    forall (q q': Q) (a: A) (w: list A),
    aut_transitions aut a q q' = true ->
    automaton_accepts aut q' w ->
    automaton_accepts aut q (a :: w)
  .

  Lemma term_matches_automaton_perturb_nil
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (sol: vector Q)
    (q: Q)
  :
    term_matches (automaton_perturb aut 1 sol q) nil <->
    aut_accept aut q = true
  .
  Proof.
    split; intros.
    - unfold automaton_perturb in H1.
      dependent destruction H1.
      + destruct (aut_accept aut q); auto.
        dependent destruction H1.
      + apply term_matches_sum in H1.
        destruct H1 as [t [? ?]].
        apply in_map_iff in H1.
        destruct H1 as [q' [? ?]]; subst.
        apply term_matches_sum in H2.
        destruct H2 as [t [? ?]].
        apply in_map_iff in H1.
        destruct H1 as [a [? ?]]; subst.
        destruct (aut_transitions aut a q q');
        dependent destruction H2.
        apply app_eq_nil in x.
        destruct x; subst.
        dependent destruction H2_.
    - unfold automaton_perturb.
      apply MatchPlusLeft.
      rewrite H1.
      constructor.
  Qed.

  Lemma term_matches_automaton_perturb_cons
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (sol: vector Q)
    (q: Q)
    (a: A)
    (w: list A)
  :
    term_matches (automaton_perturb aut 1 sol q) (a :: w) <->
    exists (q': Q),
      aut_transitions aut a q q' = true /\
      term_matches (sol q') w
  .
  Proof.
    split; intros.
    - unfold automaton_perturb in H1.
      dependent destruction H1.
      + destruct (aut_accept aut q);
        dependent destruction H1.
      + apply term_matches_sum in H1.
        destruct H1 as [t [? ?]].
        apply in_map_iff in H1.
        destruct H1 as [q' [? ?]]; subst.
        exists q'.
        apply term_matches_sum in H2.
        destruct H2 as [t [? ?]].
        apply in_map_iff in H1.
        destruct H1 as [a' [? ?]]; subst.
        destruct (aut_transitions aut a' q q') eqn:?;
        dependent destruction H2.
        dependent destruction H2_.
        rewrite <- app_comm_cons in x.
        rewrite app_nil_l in x.
        inversion x; subst.
        intuition.
    - destruct H1 as [q' [? ?]].
      unfold automaton_perturb.
      apply MatchPlusRight.
      apply term_matches_sum.
      eexists; rewrite in_map_iff.
      repeat split.
      + exists q'; split; auto.
        apply finite_cover.
      + apply term_matches_sum.
        eexists; split.
        * apply in_map_iff.
          exists a; rewrite H1.
          intuition (apply finite_cover).
        * replace (a :: w) with ((a :: nil) ++ w) by reflexivity.
          apply MatchTimes; auto.
          constructor.
  Qed.

  Lemma automaton_least_solution_match
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (sol: vector Q)
    (q: Q)
    (w: list A)
  :
    automaton_least_solution aut 1 sol ->
    term_matches (sol q) w <->
    automaton_accepts aut q w
  .
  Proof.
    intro; revert q; induction w; intros;
    rewrite term_equiv_sound
      with (t2 := automaton_perturb aut 1 sol q)
      by (now apply automaton_solution_least_converse).
    - rewrite term_matches_automaton_perturb_nil.
      split; intros.
      + now constructor.
      + now dependent destruction H2.
    - rewrite term_matches_automaton_perturb_cons.
      split; intros.
      + destruct H2 as [q' [? ?]].
        apply AcceptsStep with (q' := q'); intuition.
      + dependent destruction H2.
        exists q'; split; auto.
        now apply IHw.
  Qed.
End AutomatonLanguage.

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

  Lemma automaton_transition_monad_solution
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (initial final: Q -> Q -> bool)
    (w: list A)
  :
    let aut' := automaton_transition_monad aut final in
    let sol' := compute_automaton_solution aut' in
    term_matches (sol' initial) w <->
    matrix_product_bool initial (automaton_transition_matrix aut w) = final
  .
  Proof.
    simpl.
    rewrite automaton_least_solution_match
      with (aut := automaton_transition_monad aut final)
      by (apply automaton_least_solution_invariant;
          apply compute_automaton_solution_least_solution).
    apply automaton_transition_monad_accepts.
  Qed.

  Definition automaton_lift
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
  :
    automaton (prod Q Q)
  := {|
    aut_accept '(q1, q2) := finite_eqb q1 q2;
    aut_transitions a '(q1, q2) '(q1', q2') :=
      aut_transitions aut a q1 q1' && finite_eqb q2 q2'
  |}.

  Lemma automaton_transition_monad_lift_shift_solution
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (scale: term)
    (sol: vector (prod (Q -> Q -> bool) (Q -> Q -> bool)))
    (h: Q -> Q -> bool)
  :
    automaton_solution (automaton_lift (automaton_transition_monad aut finite_eqb)) scale sol ->
    automaton_solution (automaton_lift (automaton_transition_monad aut finite_eqb)) scale (vector_shift_both sol h)
  .
  Proof.
    split; simpl; intros.
    - destruct q1, q2.
      apply Bool.andb_true_iff in H2; destruct H2.
      apply finite_eqb_eq in H2, H3; subst.
      unfold vector_shift_both; simpl.
      apply H1; simpl.
      apply Bool.andb_true_iff.
      repeat rewrite finite_eqb_eq.
      rewrite matrix_product_bool_associative.
      intuition.
    - destruct q.
      apply finite_eqb_eq in H2; subst.
      apply H1; simpl.
      now apply finite_eqb_eq.
  Qed.

  Definition automaton_relation_solution_path
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
  :=
    compute_automaton_solution (automaton_lift (automaton_transition_monad aut finite_eqb))
  .

  Definition automaton_relation_solution
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (m: Q -> Q -> bool)
  :=
    automaton_relation_solution_path aut (finite_eqb, m)
  .

  Lemma automaton_relation_solution_path_shift
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (h: Q -> Q -> bool)
  :
    automaton_relation_solution_path aut <==
    vector_shift_both (automaton_relation_solution_path aut) h
  .
  Proof.
    intro.
    unfold automaton_relation_solution_path.
    rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
    apply compute_automaton_solution_least_solution.
    apply automaton_transition_monad_lift_shift_solution.
    apply automaton_least_solution_invariant.
    apply compute_automaton_solution_least_solution.
  Qed.

  Lemma automaton_relation_solution_path_shift_single
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (h: Q -> Q -> bool)
  :
    automaton_relation_solution_path aut ;;;
    automaton_relation_solution aut h <==
    vector_shift_single (automaton_relation_solution_path aut) h
  .
  Proof.
    unfold automaton_relation_solution_path, automaton_relation_solution.
    apply compute_automaton_solution_least_solution.
    split; intros.
    - unfold vector_shift_single.
      destruct q1, q2; simpl in *.
      apply Bool.andb_true_iff in H1; destruct H1.
      rewrite finite_eqb_eq in H1, H2; subst.
      pose proof (vector_scale_right_unit (A := A) (Q := (prod (Q -> Q -> bool) (Q -> Q -> bool)))).
      specialize (H1 (compute_automaton_solution (automaton_lift (automaton_transition_monad aut finite_eqb)))).
      rewrite <- (H1 (matrix_product_bool b (aut_transitions aut a), matrix_product_bool b2 h)).
      rewrite <- (H1 (b, matrix_product_bool b2 h)).
      apply compute_automaton_solution_least_solution; simpl.
      apply Bool.andb_true_iff.
      now repeat rewrite finite_eqb_eq.
    - unfold vector_shift_single.
      destruct q; simpl in *.
      apply finite_eqb_eq in H1; subst.
      replace b0
        with (matrix_product_bool b0 finite_eqb) at 1
        by (apply matrix_product_bool_unit_right).
      replace b0
        with (matrix_product_bool b0 finite_eqb) at 3
        by (apply matrix_product_bool_unit_right).
      eapply term_lequiv_trans.
      apply automaton_relation_solution_path_shift.
      unfold vector_shift_both; simpl.
      repeat rewrite matrix_product_bool_unit_right.
      unfold automaton_relation_solution_path.
      apply term_lequiv_refl.
  Qed.

  Lemma automaton_relation_solution_merge
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (f g: Q -> Q -> bool)
  :
    automaton_relation_solution aut f ;;
    automaton_relation_solution aut g <=
    automaton_relation_solution aut (matrix_product_bool f g)
  .
  Proof.
    unfold automaton_relation_solution at 1.
    apply automaton_relation_solution_path_shift_single.
  Qed.

  Definition automaton_accepting_matrices
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (q: Q)
  :
    list (Q -> Q -> bool)
  :=
    filter (fun m => vector_inner_product_bool (m q) (aut_accept aut))
           finite_enum
  .

  Definition automaton_sum_accepting_matrices
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (q: Q)
  :
    term
  :=
    sum (map (automaton_relation_solution aut)
             (automaton_accepting_matrices aut q))
  .

  Lemma automaton_relation_solution_step
    {Q: Type}
    `{Finite Q}
    (a: A)
    (aut: automaton Q)
  :
    $ a <= automaton_relation_solution aut (automaton_transition_matrix aut (a :: nil))
  .
  Proof.
    unfold automaton_relation_solution.
    unfold automaton_relation_solution_path.
    apply term_lequiv_trans with (t2 := $a ;; compute_automaton_solution
    (automaton_lift (automaton_transition_monad aut finite_eqb))
    (automaton_transition_matrix aut (a :: nil), automaton_transition_matrix aut (a :: nil))).
    rewrite <- ETimesUnitRight with (t := $a) at 1.
    apply times_mor_mono.
    apply term_lequiv_refl.
    unfold term_lequiv.
    rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
    apply compute_automaton_solution_least_solution.
    simpl.
    now apply finite_eqb_eq.
    rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
    rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ (finite_eqb, _)).
    apply compute_automaton_solution_least_solution.
    simpl.
    apply Bool.andb_true_iff.
    repeat rewrite finite_eqb_eq.
    autorewrite with automaton_transition_matrix.
    rewrite matrix_product_bool_unit_left.
    rewrite matrix_product_bool_unit_right.
    intuition.
  Qed.

  Lemma automaton_sum_accepting_matrices_lower
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
  :
    compute_automaton_solution aut <== automaton_sum_accepting_matrices aut
  .
  Proof.
    intro.
    rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q).
    apply compute_automaton_solution_least_solution.
    split; intros.
    - unfold automaton_sum_accepting_matrices.
      rewrite <- sum_distribute_left.
      apply sum_lequiv_all; intros.
      apply in_map_iff in H2.
      destruct H2 as [? [? ?]]; subst.
      apply in_map_iff in H3.
      destruct H3 as [? [? ?]]; subst.
      unfold automaton_accepting_matrices in H3.
      apply filter_In in H3.
      destruct H3 as [_ ?].
      eapply term_lequiv_trans.
      + apply times_mor_mono; [| reflexivity ].
        apply automaton_relation_solution_step with (aut := aut).
      + eapply term_lequiv_trans.
        * apply automaton_relation_solution_merge.
        * apply sum_lequiv_member.
          apply in_map_iff.
          eexists; intuition.
          unfold automaton_accepting_matrices.
          apply filter_In.
          split; [apply finite_cover |].
          unfold vector_inner_product_bool.
          apply disj_true.
          apply in_map_iff.
          unfold vector_inner_product_bool in H2.
          apply disj_true in H2.
          apply in_map_iff in H2.
          destruct H2 as [? [? _]].
          apply Bool.andb_true_iff in H2; destruct H2.
          exists x; split; [| apply finite_cover ].
          apply Bool.andb_true_iff; intuition.
          apply matrix_product_characterise.
          exists q2; intuition.
          autorewrite with automaton_transition_matrix.
          now rewrite matrix_product_bool_unit_right.
    - unfold automaton_sum_accepting_matrices.
      eapply term_lequiv_trans
        with (t2 := automaton_relation_solution aut finite_eqb).
      + unfold automaton_relation_solution, automaton_relation_solution_path.
        rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
        apply compute_automaton_solution_least_solution; simpl.
        now apply finite_eqb_eq.
      + apply sum_lequiv_member.
        apply in_map_iff.
        eexists; split; auto.
        unfold automaton_accepting_matrices.
        apply filter_In; split; [ apply finite_cover |].
        unfold vector_inner_product_bool; apply disj_true.
        apply in_map_iff.
        exists q0; intuition.
        apply Bool.andb_true_iff; intuition.
        now apply finite_eqb_eq.
  Qed.

  Definition automaton_lift_sum_accepting_paths
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (q: Q)
  :=
      sum (
        map (curry (compute_automaton_solution (automaton_lift aut)) q)
            (filter (aut_accept aut) finite_enum)
      )
  .

  Lemma automaton_lift_solution_lower
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
  :
    compute_automaton_solution aut <==
    automaton_lift_sum_accepting_paths aut
  .
  Proof.
    intro.
    rewrite <- ETimesUnitRight
      with (t := compute_automaton_solution aut q).
    apply compute_automaton_solution_least_solution.
    split; intros.
    - unfold automaton_lift_sum_accepting_paths.
      rewrite <- sum_distribute_left.
      apply sum_lequiv_all; intros.
      apply in_map_iff in H2.
      destruct H2 as [q' [? ?]]; subst.
      apply in_map_iff in H3.
      destruct H3 as [q'' [? ?]]; subst.
      apply filter_In in H3.
      destruct H3 as [_ ?].
      unfold curry at 1; simpl.
      apply term_lequiv_trans
        with (t2 := compute_automaton_solution (automaton_lift aut) (q1, q'')).
      + rewrite <- ETimesUnitRight
          with (t := compute_automaton_solution _ (q2, q'')).
        rewrite <- ETimesUnitRight
          with (t := compute_automaton_solution _ (q1, q'')).
        apply compute_automaton_solution_least_solution; simpl.
        apply Bool.andb_true_iff.
        now rewrite finite_eqb_eq.
      + apply sum_lequiv_member.
        apply in_map_iff.
        exists q''; intuition.
        apply filter_In; intuition.
    - unfold automaton_lift_sum_accepting_paths.
      eapply term_lequiv_trans
        with (t2 := compute_automaton_solution (automaton_lift aut) (q0, q0)).
      + rewrite <- ETimesUnitRight
          with (t := compute_automaton_solution _ _).
        apply compute_automaton_solution_least_solution; simpl.
        now apply finite_eqb_eq.
      + apply sum_lequiv_member.
        apply in_map_iff.
        exists q0; intuition.
        apply filter_In; intuition.
  Qed.

  Definition automaton_fix_accepting_state
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (q: Q)
  :
    automaton Q
  := {|
    aut_transitions := aut_transitions aut;
    aut_accept q' := finite_eqb q q';
  |}.

  Definition automaton_reconstruct_path
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (q1 q2: Q)
  :
    term
  :=
    compute_automaton_solution (automaton_fix_accepting_state aut q2) q1
  .

  Lemma automaton_lift_solution_upper
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
  :
    compute_automaton_solution (automaton_lift aut) <==
    uncurry (automaton_reconstruct_path aut)
  .
  Proof.
    intro.
    rewrite <- ETimesUnitRight
      with (t := compute_automaton_solution _ q).
    apply compute_automaton_solution_least_solution.
    split; intros.
    - unfold automaton_reconstruct_path.
      destruct q1, q2; simpl.
      simpl in H1.
      apply Bool.andb_true_iff in H1; destruct H1.
      apply finite_eqb_eq in H2; subst.
      rewrite <- ETimesUnitRight
        with (t := compute_automaton_solution _ q2).
      rewrite <- ETimesUnitRight
        with (t := compute_automaton_solution _ q0).
      apply compute_automaton_solution_least_solution.
      now simpl.
    - destruct q0; simpl in *.
      apply finite_eqb_eq in H1; subst.
      unfold automaton_reconstruct_path.
      rewrite <- ETimesUnitRight
        with (t := compute_automaton_solution _ _).
      apply compute_automaton_solution_least_solution; simpl.
      now apply finite_eqb_eq.
  Qed.

  Lemma automaton_lift_solution_characterise
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (q: Q)
  :
    compute_automaton_solution aut q ==
    automaton_lift_sum_accepting_paths aut q
  .
  Proof.
    apply term_lequiv_squeeze.
    - apply automaton_lift_solution_lower.
    - unfold automaton_lift_sum_accepting_paths.
      apply sum_lequiv_all; intros.
      apply in_map_iff in H1.
      destruct H1 as [q' [? ?]]; subst.
      apply filter_In in H2.
      destruct H2 as [_ ?].
      unfold curry; simpl.
      eapply term_lequiv_trans.
      apply automaton_lift_solution_upper; simpl.
      unfold automaton_reconstruct_path; simpl.
      rewrite <- ETimesUnitRight
        with (t := compute_automaton_solution _ _).
      apply compute_automaton_solution_least_solution.
      split; intros.
      + rewrite <- ETimesUnitRight
          with (t := compute_automaton_solution _ q2).
        rewrite <- ETimesUnitRight
          with (t := compute_automaton_solution _ q1).
        now apply compute_automaton_solution_least_solution.
      + rewrite <- ETimesUnitRight
          with (t := compute_automaton_solution _ q0).
        apply compute_automaton_solution_least_solution.
        simpl in H2; rewrite finite_eqb_eq in H2.
        now subst.
  Qed.

  Lemma automaton_lift_transition_monad_discard_accept
   {Q: Type}
   `{Finite Q}
   (aut: automaton Q)
   (m1 m2: Q -> Q -> bool)
  :
    automaton_lift (automaton_transition_monad aut m1) =
    automaton_lift (automaton_transition_monad aut m2)
  .
  Proof.
    reflexivity.
  Qed.

  Lemma automaton_transition_monad_accepting
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (m: Q -> Q -> bool)
  :
    filter (aut_accept (automaton_transition_monad aut m)) finite_enum = m :: nil
  .
  Proof.
    rewrite filter_singleton with (x := m).
    - now rewrite finite_count_occ.
    - now setoid_rewrite finite_eqb_eq.
  Qed.

  Definition automaton_relation_solution'
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (m: Q -> Q -> bool)
  :
    term
  :=
      compute_automaton_solution (automaton_transition_monad aut m) finite_eqb
  .

  Lemma automaton_relation_solution_characterise
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (m: Q -> Q -> bool)
  :
    automaton_relation_solution aut m ==
    automaton_relation_solution' aut m
  .
  Proof.
    unfold automaton_relation_solution,
           automaton_relation_solution_path,
           automaton_relation_solution'.
    rewrite automaton_lift_solution_characterise
      with (aut := automaton_transition_monad aut m).
    unfold automaton_lift_sum_accepting_paths.
    rewrite automaton_transition_monad_accepting.
    simpl; autorewrite with sum.
    rewrite EPlusUnit.
    unfold curry; simpl.
    now rewrite automaton_lift_transition_monad_discard_accept with (m2 := m).
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
      apply in_map_iff in H4.
      destruct H4 as [q'' [? ?]]; subst.
      apply filter_In in H5.
      destruct H5 as [_ ?].
      apply finite_eqb_eq in H3; subst.
      apply matrix_product_characterise in H4.
      destruct H4 as [q3 [? ?]].
      apply term_lequiv_trans with (t2 := compute_automaton_solution aut q3).
      + rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q'').
        rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q3).
        now apply compute_automaton_solution_least_solution.
      + apply sum_lequiv_member.
        apply in_map_iff.
        exists q3; intuition.
        apply filter_In; intuition.
    - intros m' ?; unfold automaton_sum_reached_paths.
      simpl in H3.
      apply finite_eqb_eq in H3; subst.
      apply term_lequiv_trans with (t2 := compute_automaton_solution aut q').
      + rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q').
        now apply compute_automaton_solution_least_solution.
      + apply sum_lequiv_member.
        apply in_map_iff.
        exists q'; intuition.
        apply filter_In; intuition.
  Qed.

  Lemma automaton_sum_accepting_matrices_upper
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
  :
    automaton_sum_accepting_matrices aut <== compute_automaton_solution aut
  .
  Proof.
    intro q.
    unfold automaton_sum_accepting_matrices.
    apply sum_lequiv_all; intros.
    apply in_map_iff in H1.
    destruct H1 as [m [? ?]]; subst.
    unfold automaton_accepting_matrices in H2.
    apply filter_In in H2.
    destruct H2 as [_ ?].
    apply disj_true in H1.
    apply in_map_iff in H1.
    destruct H1 as [q' [? _]].
    apply Bool.andb_true_iff in H1.
    destruct H1 as [? ?].
    rewrite automaton_relation_solution_characterise.
    eapply term_lequiv_trans.
    apply automaton_transition_monad_solution_upper with (q := q) (q' := q'); auto.
    unfold automaton_sum_reached_paths.
    apply sum_lequiv_all; intros.
    apply in_map_iff in H3.
    destruct H3 as [q'' [? ?]]; subst.
    apply filter_In in H4.
    destruct H4 as [_ ?].
    apply finite_eqb_eq in H3; subst.
    apply term_lequiv_refl.
  Qed.

  Lemma automaton_sum_accepting_matrices_characterise
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
  :
    automaton_sum_accepting_matrices aut === compute_automaton_solution aut
  .
  Proof.
    apply vector_lequiv_squeeze.
    - apply automaton_sum_accepting_matrices_upper.
    - apply automaton_sum_accepting_matrices_lower.
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
    rewrite in_map_iff.
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

Section AutomatonCoproduct.
  Context {A: Type}.
  Context `{Finite A}.
  Notation term := (term A).
  Notation automaton := (automaton A).

  Definition automaton_coproduct
    {Q1 Q2: Type}
    (aut1: automaton Q1)
    (aut2: automaton Q2)
  :
    automaton (Q1 + Q2)
  := {|
    aut_accept q :=
      match q with
      | inl q1 => aut_accept aut1 q1
      | inr q2 => aut_accept aut2 q2
      end;
    aut_transitions a q q' :=
      match q, q' with
      | inl q1, inl q1' => aut_transitions aut1 a q1 q1'
      | inr q2, inr q2' => aut_transitions aut2 a q2 q2'
      | _, _ => false
      end;
  |}.

  Program Definition automaton_homomorphism_inl
    {Q1 Q2: Type}
    (aut1: automaton Q1)
    (aut2: automaton Q2)
  :
    automaton_homomorphism aut1 (automaton_coproduct aut1 aut2)
  := {|
    automaton_homomorphism_f := inl
  |}.

  Program Definition automaton_homomorphism_inr
    {Q1 Q2: Type}
    (aut1: automaton Q1)
    (aut2: automaton Q2)
  :
    automaton_homomorphism aut2 (automaton_coproduct aut1 aut2)
  := {|
    automaton_homomorphism_f := inr
  |}.

  Lemma automaton_coproduct_bound_upper
    {Q1 Q2: Type}
    `{Finite Q1}
    `{Finite Q2}
    (aut1: automaton Q1)
    (aut2: automaton Q2)
    (q: Q1 + Q2)
  :
    compute_automaton_solution (automaton_coproduct aut1 aut2) q
      <= match q with
         | inl q1 => compute_automaton_solution aut1 q1
         | inr q2 => compute_automaton_solution aut2 q2
         end
  .
  Proof.
    rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
    revert q.
    apply compute_automaton_solution_least_solution.
    split; intros.
    - destruct q1, q2; try discriminate.
      + rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut1 q).
        rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut1 q0).
        now apply compute_automaton_solution_least_solution.
      + rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut2 q).
        rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut2 q0).
        now apply compute_automaton_solution_least_solution.
    - destruct q.
      + rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut1 q).
        now apply compute_automaton_solution_least_solution.
      + rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut2 q).
        now apply compute_automaton_solution_least_solution.
  Qed.

  Lemma automaton_coproduct_solution_left
    {Q1 Q2: Type}
    `{Finite Q1}
    `{Finite Q2}
    (aut1: automaton Q1)
    (aut2: automaton Q2)
  :
    compute_automaton_solution aut1 ===
    compute_automaton_solution (automaton_coproduct aut1 aut2) ??? inl
  .
  Proof.
    intro q; apply term_lequiv_squeeze.
    - rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut1 q).
      apply compute_automaton_solution_least_solution.
      replace inl
        with (automaton_homomorphism_f (automaton_homomorphism_inl aut1 aut2))
        by reflexivity.
      apply automaton_homomorphism_solution.
      apply automaton_solution_invariant.
      apply compute_automaton_solution_least_solution.
    - unfold compose; simpl.
      now rewrite automaton_coproduct_bound_upper.
  Qed.

  Lemma automaton_coproduct_solution_right
    {Q1 Q2: Type}
    `{Finite Q1}
    `{Finite Q2}
    (aut1: automaton Q1)
    (aut2: automaton Q2)
  :
    compute_automaton_solution aut2 ===
    compute_automaton_solution (automaton_coproduct aut1 aut2) ??? inr
  .
  Proof.
    intro q; apply term_lequiv_squeeze.
    - rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut2 q).
      apply compute_automaton_solution_least_solution.
      replace inr
        with (automaton_homomorphism_f (automaton_homomorphism_inr aut1 aut2))
        by reflexivity.
      apply automaton_homomorphism_solution.
      apply automaton_solution_invariant.
      apply compute_automaton_solution_least_solution.
    - unfold compose; simpl.
      now rewrite automaton_coproduct_bound_upper.
  Qed.
End AutomatonCoproduct.

Section AutomatonCoalesce.
  Context {A: Type}.
  Context `{Finite A}.
  Notation automaton := (automaton A).
  Notation term := (term A).

  Definition automaton_coalesce_accept
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (targets: Q -> bool)
    (q: Q + unit)
  :
    bool
  :=
    match q with
    | inl q => aut_accept aut q
    | inr _ => disj (map (aut_accept aut) (filter targets finite_enum))
    end
  .

  Definition automaton_coalesce_transitions
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (targets: Q -> bool)
    (a: A)
    (q q': Q + unit)
  :
    bool
  :=
    match q, q' with
    | inl q, inl q' => aut_transitions aut a q q'
    | inr _, inl q' =>
      disj (
        map (fun q => aut_transitions aut a q q')
            (filter targets finite_enum)
      )
    | _, _ => false
    end
  .

  Definition automaton_coalesce
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (targets: Q -> bool)
  :
    automaton (Q + unit)
  := {|
    aut_accept := automaton_coalesce_accept aut targets;
    aut_transitions := automaton_coalesce_transitions aut targets;
  |}.


  Program Definition automaton_homomorphism_coalesce_embed
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (targets: Q -> bool)
  :
    automaton_homomorphism aut (automaton_coalesce aut targets)
  := {|
    automaton_homomorphism_f := inl
  |}.

  Definition automaton_coalesce_import_solution
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (targets: Q -> bool)
    (q: Q + unit)
  :
    term
  :=
    match q with
    | inl q => compute_automaton_solution aut q
    | inr _ =>
      sum (
        map (compute_automaton_solution aut)
            (filter targets finite_enum)
      )
    end
  .

  Lemma automaton_coalesce_solution_lower_embedded
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (targets: Q -> bool)
  :
    compute_automaton_solution aut <==
    compute_automaton_solution (automaton_coalesce aut targets) ??? inl
  .
  Proof.
    intro q.
    rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q).
    apply compute_automaton_solution_least_solution.
    replace inl
      with (automaton_homomorphism_f (automaton_homomorphism_coalesce_embed aut targets))
      by reflexivity.
    apply automaton_homomorphism_solution.
    apply automaton_solution_invariant.
    apply compute_automaton_solution_least_solution.
  Qed.

  Lemma automaton_coalesce_solution_lower
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (targets: Q -> bool)
  :
    automaton_coalesce_import_solution aut targets <==
    compute_automaton_solution (automaton_coalesce aut targets)
  .
  Proof.
    intro q; destruct q; simpl.
    - apply automaton_coalesce_solution_lower_embedded.
    - apply sum_lequiv_all; intros.
      apply in_map_iff in H1.
      destruct H1 as [q' [? ?]]; subst.
      apply filter_In in H2.
      destruct H2 as [_ ?].
      rewrite automaton_solution_least_converse
        with (aut := aut) (scale := 1)
        by (apply automaton_least_solution_invariant;
            apply compute_automaton_solution_least_solution).
      rewrite automaton_solution_least_converse
        with (aut := automaton_coalesce aut targets) (scale := 1)
        by (apply automaton_least_solution_invariant;
            apply compute_automaton_solution_least_solution).
      unfold automaton_perturb.
      apply term_lequiv_split.
      + apply term_lequiv_split_left; simpl.
        destruct (disj _) eqn:?.
        * destruct (aut_accept aut q').
          -- apply term_lequiv_refl.
          -- apply term_lequiv_zero.
        * rewrite disj_false in Heqb.
          rewrite (Heqb (aut_accept aut q')).
          -- apply term_lequiv_refl.
          -- apply in_map_iff.
             exists q'; intuition.
             apply filter_In; intuition.
      + apply term_lequiv_split_right.
        apply sum_lequiv_all; intros.
        apply in_map_iff in H2.
        destruct H2 as [q'' [? _]]; subst.
        apply sum_lequiv_all; intros.
        apply in_map_iff in H2.
        destruct H2 as [a [? _]]; subst.
        destruct (aut_transitions aut a q' q'') eqn:?; [| apply term_lequiv_zero].
        eapply term_lequiv_trans.
        2:{
          apply sum_lequiv_member.
          apply in_map_iff.
          exists (inl q''); intuition.
          apply finite_cover.
        }
        eapply term_lequiv_trans.
        2:{
          apply sum_lequiv_member.
          apply in_map_iff.
          exists a; intuition.
        }
        assert (aut_transitions (automaton_coalesce aut targets) a (inr u) (inl q'') = true).
        * apply disj_true.
          apply in_map_iff.
          exists q'; intuition.
          apply filter_In; intuition.
        * rewrite H2.
          apply times_mor_mono; [ apply term_lequiv_refl |].
          apply automaton_coalesce_solution_lower_embedded.
  Qed.

  Lemma automaton_coalesce_solution_upper
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (targets: Q -> bool)
  :
    compute_automaton_solution (automaton_coalesce aut targets)
      <== automaton_coalesce_import_solution aut targets
  .
  Proof.
    intro q.
    rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
    revert q.
    apply compute_automaton_solution_least_solution.
    split; intros.
    - destruct q1, q2; try discriminate; simpl.
      + rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q).
        rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q0).
        now apply compute_automaton_solution_least_solution.
      + simpl in H1.
        apply disj_true in H1.
        apply in_map_iff in H1.
        destruct H1 as [q' [? ?]].
        apply filter_In in H2.
        destruct H2 as [_ ?].
        apply term_lequiv_trans with (t2 := compute_automaton_solution aut q').
        * rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q).
          rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q').
          now apply compute_automaton_solution_least_solution.
        * apply sum_lequiv_member.
          apply in_map_iff.
          exists q'; intuition.
          apply filter_In; intuition.
    - destruct q; simpl.
      + simpl in H1.
        rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q).
        now apply compute_automaton_solution_least_solution.
      + simpl in H1.
        apply disj_true in H1.
        apply in_map_iff in H1.
        destruct H1 as [q' [? ?]].
        apply filter_In in H2.
        destruct H2 as [_ ?].
        eapply term_lequiv_trans with (t2 := compute_automaton_solution aut q').
        * rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q').
          now apply compute_automaton_solution_least_solution.
        * apply sum_lequiv_member.
          apply in_map_iff.
          exists q'; intuition.
          apply filter_In; intuition.
  Qed.

  Lemma automaton_coalesce_solution
    {Q: Type}
    `{Finite Q}
    (aut: automaton Q)
    (targets: Q -> bool)
  :
    compute_automaton_solution (automaton_coalesce aut targets)
      === automaton_coalesce_import_solution aut targets
  .
  Proof.
    apply vector_lequiv_squeeze.
    + apply automaton_coalesce_solution_upper.
    + apply automaton_coalesce_solution_lower.
  Qed.
End AutomatonCoalesce.
