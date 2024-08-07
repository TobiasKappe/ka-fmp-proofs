Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import KA.Finite.
Require Import KA.ModelTheory.
Require Import KA.Scope.
Require Import KA.Terms.
Require Import KA.CanonicalModel.
Local Open Scope ka_scope.

Section Main.
  Variable (A: Type).
  Context `{Finite A}.

  Notation term := (term A).

  Lemma finite_model_property_bound
    (t1 t2: term)
  :
    kleene_satisfies_class (@kleene_finite) t1 t2 ->
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
      rewrite <- H0. intuition.
      constructor; intuition.
  Qed.

  Theorem finite_model_property
    (t1 t2: term)
  :
    kleene_satisfies_class (@kleene_finite) t1 t2 ->
    t1 == t2
  .
  Proof.
    intros.
    apply term_lequiv_squeeze.
    - now apply finite_model_property_bound.
    - now apply finite_model_property_bound,
                kleene_satisfies_class_symmetric.
  Qed.

  Theorem completeness
    (t1 t2: term)
  :
    term_matches t1 = term_matches t2 ->
    t1 == t2
  .
  Proof.
    intros.
    apply finite_model_property.
    unfold kleene_satisfies_class; intros.
    apply kleene_preserve_equation_language_star_continuous; auto.
    destruct H1; apply kleene_finite_star_continuous.
  Qed.

  Theorem relational_model_property
    (t1 t2: term)
  :
    kleene_satisfies_class (@kleene_relational) t1 t2 ->
    t1 == t2
  .
  Proof.
    intros.
    apply completeness.
    extensionality w; apply propositional_extensionality.
    apply kleene_preserve_equation_finite_relational_language.
    now apply kleene_preserve_equation_relational_finite_relational.
  Qed.
End Main.
