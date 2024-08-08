Require Import Coq.Program.Equality.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Local Open Scope program_scope.

Require Import KA.Finite.
Require Import KA.Terms.
Require Import KA.Vectors.
Require Import KA.Scope.
Require Import KA.Automata.
Require Import KA.Utilities.
Local Open Scope ka_scope.

Section System.
  Variable (A: Type).
  Notation term := (term A).
  Notation matrix := (matrix A).
  Notation vector := (vector A).

  Record system (Q: Type) := {
    smat: matrix Q;
    svec: vector Q;
  }.
End System.

Arguments smat {A} {Q}.
Arguments svec {A} {Q}.

Section SystemOperations.
  Context {A: Type}.
  Notation term := (term A).
  Notation matrix := (matrix A).
  Notation vector := (vector A).
  Notation system := (system A).

  Definition system_index
    {X: Type}
    `{Finite X}
    (sys: system X)
  :
    system (position (length finite_enum))
  := {|
    smat := matrix_index (smat sys);
    svec := vector_index (svec sys);
  |}.

  Definition system_lookup
    {X: Type}
    `{Finite X}
    (sys: system (position (length finite_enum)))
  :
    system X
  := {|
    smat := matrix_lookup (smat sys);
    svec := vector_lookup (svec sys);
  |}.
End SystemOperations.

Section SolutionDefinition.
  Context {A: Type}.
  Notation term := (term A).
  Notation matrix := (matrix A).
  Notation vector := (vector A).
  Notation system := (system A).

  Record solution
    {Q: Type}
    (sys: system Q)
    (scale: term)
    (sol: vector Q)
  := {
    solution_move:
      forall (q q': Q),
      smat sys q q' ;; sol q' <= sol q;
    solution_bias:
      forall (q: Q),
      svec sys q ;; scale <= sol q;
  }.

  Record least_solution
    {Q: Type}
    (sys: system Q)
    (scale: term)
    (sol: vector Q)
  := {
    least_solution_solution:
      solution sys scale sol;
    least_solution_least:
      forall sol',
      solution sys scale sol' ->
      sol <== sol'
  }.

  Definition solution_nat
    {n: nat}
    (sys: system (position n))
    (scale: term)
    (sol: vector (position n))
  :=
    smat sys <*> sol <+> svec sys ;;; scale <== sol
  .
End SolutionDefinition.

Section SolutionAlgorithm.
  Context {A: Type}.
  Notation term := (term A).
  Notation matrix := (matrix A).
  Notation vector := (vector A).
  Notation system := (system A).

  Definition compress_system
    {n: nat}
    (sys: system (position (S n)))
    : system (position n)
  := {|
    smat p1 p2 :=
      smat sys (PThere p1) (PThere p2) +
      smat sys (PThere p1) PHere
        ;; (smat sys PHere PHere)*
        ;; smat sys PHere (PThere p2);
    svec p :=
      svec sys (PThere p) +
        smat sys (PThere p) PHere
          ;; (smat sys PHere PHere)*
          ;; svec sys PHere
  |}.

  Equations compute_solution_nat
    {n: nat}
    (sys: system (position n))
    (p: position n)
    : term
  := {
    @compute_solution_nat (S n) sys (PThere p) :=
      let smaller_solution := compute_solution_nat (compress_system sys) in
      smaller_solution p;
    @compute_solution_nat (S n) sys PHere :=
      let smaller_solution := compute_solution_nat (compress_system sys) in
      (smat sys PHere PHere)* ;;
        (svec sys PHere + (# (smat sys PHere)) ** smaller_solution);
  }.

  Definition compute_solution
    {X: Type}
    `{Finite X}
    (sys: system X)
  :
    vector X
  :=
    vector_lookup (compute_solution_nat (system_index sys))
  .
End SolutionAlgorithm.

Section SolutionCorrect.
  Context {A: Type}.
  Notation term := (term A).
  Notation matrix := (matrix A).
  Notation vector := (vector A).
  Notation system := (system A).

  Lemma compute_solution_nat_chomp
    {n: nat}
    (sys: system (position (S n)))
  :
    # compute_solution_nat sys === compute_solution_nat (compress_system sys)
  .
  Proof.
    intro.
    unfold vector_chomp.
    now autorewrite with compute_solution_nat; simpl.
  Qed.

  Lemma compress_system_mat
    (n: nat)
    (sys: system (position (S n)))
    (p: position n)
  :
    (smat sys (PThere p) PHere;; smat sys PHere PHere *) &
      (# smat sys PHere) <+> # smat sys (PThere p)
    === smat (compress_system sys) p
  .
  Proof.
    unfold compress_system; simpl.
    intro.
    unfold vector_sum, vector_scale_left, vector_chomp.
    now rewrite EPlusComm.
  Qed.

  Lemma compress_system_vec
    (n: nat)
    (sys: system (position (S n)))
    (p: position n)
  :
    svec sys (PThere p) +
      smat sys (PThere p) PHere ;; smat sys PHere PHere * ;; svec sys PHere
    == svec (compress_system sys) p
  .
  Proof.
    now unfold compress_system; simpl.
  Qed.

  Lemma solution_iff_solution_nat
    {n: nat}
    (sys: system (position n))
    (scale: term)
    (sol: vector (position n))
  :
    solution sys scale sol <-> solution_nat sys scale sol
  .
  Proof.
    split; intros.
    - unfold solution_nat.
      intro p.
      unfold vector_sum, matrix_vector_product.
      apply term_lequiv_split.
      + apply vector_inner_product_contained_split; intro.
        apply H.
      + apply H.
    - split; intros.
      + eapply term_lequiv_trans; [apply term_lequiv_split_left|].
        * apply vector_inner_product_contained.
        * apply H.
      + eapply term_lequiv_trans; [apply term_lequiv_split_right|].
        * apply term_lequiv_refl.
        * apply H.
  Qed.

  Lemma solution_one_solution_nat
    {Q: Type}
    (sys: system Q)
    (scale: term)
    (sol: vector Q)
  :
    solution sys 1 sol ->
    solution sys scale (sol ;;; scale)
  .
  Proof.
    split; intros.
    - unfold vector_scale_right.
      rewrite ETimesAssoc.
      apply times_mor_mono; try reflexivity.
      apply H.
    - unfold vector_scale_right.
      apply times_mor_mono; try reflexivity.
      unfold term_lequiv.
      rewrite <- ETimesUnitRight with (t := svec sys q).
      apply H.
  Qed.

  Lemma compute_solution_nat_solution_nat_one
    {n: nat}
    (sys: system (position n))
  :
    solution_nat sys 1 (compute_solution_nat sys)
  .
  Proof.
    unfold solution_nat; intro p.
    dependent induction p.
    + unfold vector_sum, matrix_vector_product.
      autorewrite with inner_product.
      autorewrite with compute_solution_nat; simpl.
      rewrite ETimesAssoc.
      unfold vector_scale_right; rewrite ETimesUnitRight.
      rewrite <- EPlusAssoc with (t3 := svec sys PHere).
      rewrite EPlusComm with (t2 := svec sys PHere).
      rewrite <- ETimesUnitLeft
        with (t := _ + # _ ** # compute_solution_nat sys).
      rewrite compute_solution_nat_chomp.
      rewrite <- EDistributeRight.
      rewrite <- EStarLeft.
      apply term_lequiv_refl.
    + unfold vector_sum, matrix_vector_product.
      autorewrite with inner_product.
      autorewrite with compute_solution_nat; simpl.
      rewrite ETimesAssoc.
      rewrite EDistributeLeft.
      rewrite compute_solution_nat_chomp.
      rewrite vector_inner_product_scale_left.
      rewrite <- EPlusAssoc with (t1 := _ ;; svec sys PHere).
      rewrite vector_inner_product_distribute_left.
      rewrite compress_system_mat.
      rewrite EPlusComm with (t1 := _ ;; svec sys PHere).
      unfold vector_scale_right; rewrite ETimesUnitRight.
      rewrite <- EPlusAssoc with (t3 := svec sys (PThere p)).
      rewrite EPlusComm with (t2 := svec sys (PThere p)) .
      rewrite compress_system_vec.
      unfold vector_scale_right, vector_sum in IHp;
      setoid_rewrite ETimesUnitRight in IHp.
      apply IHp.
  Qed.

  Lemma solution_bound_mat
    {Q: Type}
    (sys: system Q)
    (scale: term)
    (sol: vector Q)
    (q q': Q)
  :
    solution sys scale sol ->
    term_lequiv ((smat sys q q)* ;; smat sys q q' ;; sol q') (sol q)
  .
  Proof.
    intros.
    rewrite <- ETimesAssoc.
    apply EFixLeft.
    apply term_lequiv_split;
    apply H.
  Qed.

  Lemma solution_bound_vec
    {Q: Type}
    (sys: system Q)
    (scale: term)
    (sol: vector Q)
    (q: Q)
  :
    solution sys scale sol ->
    term_lequiv ((smat sys q q)* ;; svec sys q ;; scale) (sol q)
  .
  Proof.
    intros.
    rewrite <- ETimesAssoc.
    apply EFixLeft.
    apply term_lequiv_split;
    apply H.
  Qed.

  Lemma solution_bound
    {Q: Type}
    (sys: system Q)
    (scale: term)
    (sol: vector Q)
    (q q': Q)
  :
    solution sys scale sol ->
    term_lequiv ((smat sys q q)* ;; (smat sys q q' ;; sol q' + svec sys q ;; scale)) (sol q)
  .
  Proof.
    intros.
    rewrite EDistributeLeft.
    apply term_lequiv_split.
    + rewrite ETimesAssoc.
      eapply solution_bound_mat; eauto.
    + rewrite ETimesAssoc.
      now apply solution_bound_vec.
  Qed.

  Lemma solution_project
    {n: nat}
    (sys: system (position (S n)))
    (scale: term)
    (sol: vector (position (S n)))
  :
    solution sys scale sol ->
    solution (compress_system sys) scale (# sol)
  .
  Proof.
    split; intros; simpl;
    rewrite EDistributeRight;
    unfold vector_chomp.
    - apply term_lequiv_split.
      + apply H.
      + fold_term_lequiv.
        repeat rewrite <- ETimesAssoc.
        rewrite ETimesAssoc with (t3 := sol (PThere q')).
        erewrite solution_bound_mat; eauto.
        apply H.
    - apply term_lequiv_split.
      + apply H.
      + fold_term_lequiv.
        repeat rewrite <- ETimesAssoc.
        rewrite ETimesAssoc with (t3 := scale).
        erewrite solution_bound_vec; eauto.
        apply H.
  Qed.

  Lemma compute_solution_nat_least
    {n: nat}
    (sys: system (position n))
    (scale: term)
    (sol: vector (position n))
  :
    solution_nat sys scale sol ->
    compute_solution_nat sys ;;; scale <== sol
  .
  Proof.
    intros.
    dependent induction n; intro p; dependent destruction p.
    - unfold vector_scale_right.
      autorewrite with compute_solution_nat; simpl.
      rewrite EPlusComm with (t1 := svec sys PHere).
      fold_term_lequiv.
      rewrite <- ETimesAssoc.
      rewrite EDistributeRight.
      rewrite vector_inner_product_scale_right.
      rewrite IHn with (sol := # sol).
      + rewrite EDistributeLeft.
        apply term_lequiv_split.
        * rewrite vector_inner_product_scale_left.
          apply vector_inner_product_contained_split; intros.
          unfold vector_scale_left.
          unfold vector_chomp.
          eapply solution_bound_mat.
          now apply solution_iff_solution_nat.
        * rewrite ETimesAssoc.
          apply solution_bound_vec.
          now apply solution_iff_solution_nat.
      + apply solution_iff_solution_nat.
        apply solution_project.
        now apply solution_iff_solution_nat.
    - autorewrite with compute_solution_nat; simpl.
      eapply term_lequiv_trans; swap 1 2.
      apply (IHn (compress_system sys) scale (# sol)).
      + apply solution_iff_solution_nat.
        apply solution_project.
        now apply solution_iff_solution_nat.
      + unfold vector_scale_right.
        autorewrite with compute_solution_nat; simpl.
        apply term_lequiv_refl.
  Qed.

  Lemma compute_solution_nat_least_solution
    {n: nat}
    (sys: system (position n))
    (scale: term)
  :
    least_solution sys scale (compute_solution_nat sys ;;; scale)
  .
  Proof.
    split.
    - apply solution_one_solution_nat.
      apply solution_iff_solution_nat.
      apply compute_solution_nat_solution_nat_one.
    - setoid_rewrite solution_iff_solution_nat.
      apply compute_solution_nat_least.
  Qed.

  Lemma solution_finite_to_nat
    {X: Type}
    `{Finite X}
    (sys: system X)
    (scale: term)
    (v: vector X)
  :
    solution sys scale v ->
    solution (system_index sys) scale (vector_index v)
  .
  Proof.
    split; intros; simpl; apply H0.
  Qed.

  Lemma solution_nat_to_finite
    {X: Type}
    `{Finite X}
    (sys: system (position (length finite_enum)))
    (scale: term)
    (v: vector (position (length (finite_enum))))
  :
    solution sys scale v ->
    solution (system_lookup sys) scale (vector_lookup v)
  .
  Proof.
    split; intros; simpl; apply H0.
  Qed.

  Lemma compute_solution_solution
    {X: Type}
    `{Finite X}
    (sys: system X)
    (scale: term)
  :
    solution sys scale (compute_solution sys ;;; scale)
  .
  Proof.
    split; intros.
    - replace (smat sys q q') with (smat (system_index sys) (list_index q) (list_index q')).
      + apply compute_solution_nat_least_solution.
      + simpl; unfold matrix_index.
        now repeat rewrite list_lookup_index.
    - replace (svec sys q) with (svec (system_index sys) (list_index q)).
      + apply compute_solution_nat_least_solution.
      + simpl; unfold vector_index.
        now rewrite list_lookup_index.
  Qed.

  Lemma compute_solution_least
    {X: Type}
    `{Finite X}
    (sys: system X)
    (scale: term)
  :
    forall sol,
      solution sys scale sol ->
      compute_solution sys ;;; scale <== sol
  .
  Proof.
    intros; intro x.
    unfold compute_solution, vector_scale_right.
    replace (vector_lookup _ x ;; scale)
      with (vector_lookup (compute_solution_nat (system_index sys) ;;; scale) x)
      by reflexivity.
    apply vector_lequiv_adjunction.
    apply compute_solution_nat_least_solution.
    now apply solution_finite_to_nat.
  Qed.

  Lemma compute_solution_least_solution
    {X: Type}
    `{Finite X}
    (sys: system X)
    (scale: term)
  :
    least_solution sys scale (compute_solution sys ;;; scale)
  .
  Proof.
    split.
    - apply compute_solution_solution.
    - apply compute_solution_least.
  Qed.

  Lemma least_solution_unique
    {X: Type}
    (sys: system X)
    (scale: term)
    (v1 v2: vector X)
  :
    least_solution sys scale v1 ->
    least_solution sys scale v2 ->
    v1 === v2
  .
  Proof.
    intros.
    apply vector_lequiv_squeeze.
    - apply H.
      apply H0.
    - apply H0.
      apply H.
  Qed.
End SolutionCorrect.

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
        handle_lists; eexists; intuition.
        handle_lists; intuition.
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
      repeat handle_lists; subst; intuition.
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
      handle_lists; subst.
      eapply term_lequiv_trans; swap 1 2.
      + eapply sum_lequiv_member.
        handle_lists; exists x; intuition.
      + apply sum_lequiv_all; intros.
        handle_lists; subst.
        destruct (aut_transitions aut x0 q x) eqn:?.
        * eapply term_lequiv_trans; swap 1 2.
          -- apply sum_lequiv_member.
             handle_lists; eexists; intuition.
          -- rewrite Heqb.
             apply times_mor_mono; intuition.
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
        handle_lists; subst.
        apply sum_lequiv_all; intros.
        handle_lists; subst.
        destruct (aut_transitions aut x0 q x) eqn:?; intuition.
        apply term_lequiv_zero.
    - split; intros.
      + apply term_lequiv_trans with (t2 := automaton_perturb aut scale sol q1).
        * unfold automaton_perturb.
          apply term_lequiv_split_right.
          eapply term_lequiv_trans; swap 1 2.
          -- apply sum_lequiv_member.
             handle_lists; eexists; intuition.
          -- apply sum_lequiv_member.
             handle_lists; eexists; intuition.
             now rewrite H2.
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
