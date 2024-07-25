Require Import Coq.Lists.List.

Require Import KA.Finite.
Require Import KA.Terms.
Require Import KA.Structure.
Require Import KA.Scope.
Local Open Scope ka_scope.

Section Main.
  Variable (A: Type).
  Context `{Finite A}.

  Notation term := (term A).

  Definition term_interp_finite_equiv
    (t1 t2: term)
  :=
    forall (X: Type) (k: kleene_algebra X) (f: A -> X),
      Finite X ->
      kleene_interp k f t1 = kleene_interp k f t2
  .

  Lemma term_finite_equiv_symmetric
    (t1 t2: term)
  :
    term_interp_finite_equiv t1 t2 ->
    term_interp_finite_equiv t2 t1
  .
  Proof.
    unfold term_interp_finite_equiv.
    intros; now rewrite H0.
  Qed.

  Lemma finite_model_property_bound
    (t1 t2: term)
  :
    term_interp_finite_equiv t1 t2 ->
    t1 <= t2
  .
  Proof.
    intros.
    eapply term_lequiv_trans.
    + apply automaton_kleene_algebra_interp_lower.
    + apply sum_lequiv_all; intros.
      apply in_map_iff in H1.
      destruct H1 as [t'' [? ?]]; subst.
      apply filter_In in H2; destruct H2 as [_ ?].
      apply automaton_kleene_algebra_interp_upper.
      rewrite <- H0; intuition.
  Qed.

  Theorem finite_model_property
    (t1 t2: term)
  :
    term_interp_finite_equiv t1 t2 ->
    t1 == t2
  .
  Proof.
    intros.
    apply term_lequiv_squeeze.
    - now apply finite_model_property_bound.
    - now apply finite_model_property_bound, term_finite_equiv_symmetric.
  Qed.

  Definition term_language_equiv
    (t1 t2: term)
  :=
    forall w, term_matches t1 w <-> term_matches t2 w
  .

  Theorem completeness
    (t1 t2: term)
  :
    term_language_equiv t1 t2 ->
    t1 == t2
  .
  Proof.
  Admitted.
End Main.
