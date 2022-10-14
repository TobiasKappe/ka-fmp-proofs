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

  Theorem finite_model_property
    (t1 t2: term)
  :
    term_interp_finite_equiv t1 t2 ->
    t1 == t2
  .
  Proof.
    intros.
    rewrite term_normal_form_left with (t2 := t2) at 1; symmetry.
    rewrite term_normal_form_right with (t1 := t1) at 1; symmetry.
    rewrite H0.
    - reflexivity.
    - typeclasses eauto.
  Qed.

  Definition term_language_equiv
    (t1 t2: term)
  :=
    forall w, term_matches t1 w <-> term_matches t2 w
  .

  Theorem completeness
    (t1 t2: term)
  :
    term_language_equiv t1 t2 <->
    t1 == t2
  .
  Proof.
    split; intros.
    - intros.
      rewrite term_normal_form_left with (t2 := t2) at 1; symmetry.
      rewrite term_normal_form_right with (t1 := t1) at 1; symmetry.
      erewrite filter_ext.
      + reflexivity.
      + intros m.
        apply ZMicromega.eq_true_iff_eq.
        split; intros.
        * apply kleene_interp_witness_construct in H1.
          destruct H1 as [w [? ?]]; subst.
          apply kleene_interp_witness_apply.
          intuition.
        * apply kleene_interp_witness_construct in H1.
          destruct H1 as [w [? ?]]; subst.
          apply kleene_interp_witness_apply.
          intuition.
    - unfold term_language_equiv; intros.
      now apply term_equiv_sound.
  Qed.
End Main.
