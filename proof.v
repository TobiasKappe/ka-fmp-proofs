From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.btauto.Btauto.
Local Open Scope program_scope.
Local Open Scope bool_scope.

Require Import KA.Finite.
Require Import KA.Terms.
Require Import KA.Structure.
Require Import KA.Scope.
Local Open Scope ka_scope.

Variable (A: Type).
Context `{Finite A}.

Notation term := (term A).

Definition term_interp_finite_equiv
  (t1 t2: term)
:=
  forall {X: Type} `{Finite X} (k: kleene_algebra X) (f: A -> X),
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

Theorem completeness
  (t1 t2: term)
:
  (forall w, term_matches t1 w <-> term_matches t2 w) <->
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
  - now apply term_equiv_sound.
Qed.

Lemma starstar (a: A):
  ($ a) * * == ($ a)*
.
Proof.
  apply term_equiv_complete; split; intros.
  - apply term_matches_star_split in H0.
    apply term_matches_star_split.
    destruct H0 as [l [? ?]]; subst.
    induction l.
    + now exists nil.
    + destruct IHl as [l' [? ?]].
      * intros.
        apply H1.
        now right.
      * specialize (H1 a0 ltac:(now left)).
        apply term_matches_star_split in H1.
        destruct H1 as [l'' [? ?]]; subst.
        exists (l'' ++ l').
        rewrite concat_app, <- H0.
        intuition.
        apply in_app_iff in H1.
        destruct H1; intuition.
  - replace w with (w ++ nil) by (now rewrite app_nil_r).
    apply MatchStarStep; auto.
    apply MatchStarBase.
Qed.

Equations term_repeat
  (n: nat)
  (t: term)
:
  term
:= {
  term_repeat 0%nat t := 1;
  term_repeat (S n) t := t ;; term_repeat n t;
}.

Lemma term_matches_star_repeat
  (t: term)
  (w: list A)
:
  term_matches (t*) w <->
  exists n, term_matches (term_repeat n t) w
.
Proof.
  split; intros.
  - dependent induction H0.
    + exists 0%nat.
      autorewrite with term_repeat.
      apply MatchOne.
    + destruct (IHterm_matches2 t eq_refl) as [n ?].
      exists (S n).
      autorewrite with term_repeat.
      now apply MatchTimes.
  - destruct H0 as [n ?].
    revert w H0; induction n; intros;
    autorewrite with term_repeat in H0.
    + dependent destruction H0.
      apply MatchStarBase.
    + dependent destruction H0.
      apply MatchStarStep; auto.
Qed.

Lemma slide (a b: A):
  ($ a ;; $ b)* ;; $a == $a ;; ($ b ;; $ a)*
.
Proof.
  apply term_equiv_complete; split; intros.
  - dependent destruction H0.
    apply term_matches_star_repeat in H0_.
    destruct H0_ as [n ?].
    revert w1 w2 H0 H0_0; induction n;
    autorewrite with term_repeat; intros.
    + dependent destruction H0.
      rewrite app_nil_l, <- app_nil_r.
      apply MatchTimes; auto.
      apply MatchStarBase.
    + dependent destruction H0.
      dependent destruction H0_.
      repeat rewrite <- app_assoc.
      apply MatchTimes; auto.
      specialize (IHn _ _ H0_0 H0_3).
      dependent destruction IHn.
      rewrite <- x.
      rewrite app_assoc.
      * apply MatchStarStep; auto.
        now apply MatchTimes.
  - dependent destruction H0.
    apply term_matches_star_repeat in H0_0.
    destruct H0_0 as [n ?].
    revert w1 w2 H0 H0_; induction n;
    autorewrite with term_repeat; intros.
    + dependent destruction H0.
      rewrite app_nil_r,  <- app_nil_l.
      apply MatchTimes; auto.
      apply MatchStarBase.
    + dependent destruction H0.
      dependent destruction H0_.
      specialize (IHn _ _ H0_0 H0_2).
      dependent destruction IHn.
      repeat rewrite <- app_assoc.
      rewrite <- x.
      repeat rewrite app_assoc.
      apply MatchTimes; auto.
      apply MatchStarStep; auto.
      now apply MatchTimes.
Qed.

Lemma denest_pre (a b: A):
  ($ a)* ;; ($b ;; ($ a)*)* <= ($ a + $ b)*
.
Proof.
  apply EFixLeft.
  apply term_lequiv_split.
  - rewrite EStarLeft at 2.
    rewrite EStarLeft at 3.
    apply term_lequiv_split_left.
    fold_term_lequiv.
    apply times_mor_mono.
    + unfold term_lequiv.
      apply term_lequiv_split_left.
      apply term_lequiv_refl.
    + apply term_lequiv_refl.
  - rewrite <- ETimesUnitRight with (t := ($ b ;; ($ a)*)*).
    apply EFixLeft.
    apply term_lequiv_split.
    + rewrite EStarLeft with (t := $a + $b).
      apply term_lequiv_split_left.
      fold_term_lequiv.
      rewrite <- ETimesAssoc.
      apply times_mor_mono.
      * unfold term_lequiv.
        apply term_lequiv_split_right.
        apply term_lequiv_refl.
      * rewrite EDistributeLeft.
        apply term_lequiv_split.
        -- apply EFixLeft.
           apply term_lequiv_split.
           ++ rewrite EStarLeft with (t := $a + $b) at 2.
              rewrite EStarLeft with (t := $a + $b) at 3.
              apply term_lequiv_split_left.
              fold_term_lequiv.
              apply times_mor_mono.
              ** apply term_lequiv_split_left.
                 apply term_lequiv_refl.
              ** apply term_lequiv_refl.
           ++ rewrite EStarLeft with (t := $a + $b) at 2.
              rewrite EStarLeft with (t := $a + $b) at 3.
              apply term_lequiv_split_left.
              apply term_lequiv_refl.
        -- apply EFixLeft.
           apply term_lequiv_split.
           ++ rewrite EStarLeft with (t := $a + $b) at 2.
              rewrite EStarLeft with (t := $a + $b) at 3.
              apply term_lequiv_split_left.
              fold_term_lequiv.
              apply times_mor_mono.
              ** apply term_lequiv_split_left.
                 apply term_lequiv_refl.
              ** apply term_lequiv_refl.
           ++ rewrite EStarLeft with (t := $a + $b).
              apply term_lequiv_split_right.
              apply term_lequiv_refl.
    + rewrite EStarLeft with (t := $a + $b).
      apply term_lequiv_split_right.
      apply term_lequiv_refl.
Qed.

Lemma term_lequiv_sound
  (t1 t2: term)
  (w: list A)
:
  t1 <= t2 ->
  term_matches t1 w ->
  term_matches t2 w
.
Proof.
  intros.
  apply term_equiv_sound with (t2 := t1 + t2).
  + now symmetry.
  + now apply MatchPlusLeft.
Qed.

Lemma denest (a b: A):
  ($ a + $ b)* == ($ a)* ;; ($b ;; ($ a)*) *
.
Proof.
  apply term_equiv_complete; split; intros.
  - apply term_matches_star_repeat in H0.
    destruct H0 as [n ?].
    revert w H0; induction n;
    autorewrite with term_repeat; intros.
    + dependent destruction H0.
      rewrite <- app_nil_l.
      apply MatchTimes; apply MatchStarBase.
    + dependent destruction H0.
      dependent destruction H0_.
      * apply IHn in H0_0.
        dependent destruction H0_0.
        rewrite app_assoc.
        apply MatchTimes; auto.
        apply MatchStarStep; auto.
      * apply IHn in H0_0.
        dependent destruction H0_0.
        rewrite app_assoc.
        rewrite <- app_nil_l.
        apply MatchTimes; [apply MatchStarBase|].
        apply MatchStarStep; auto.
        apply MatchTimes; auto.
  - eapply term_lequiv_sound.
    + apply denest_pre.
    + auto.
Qed.

Equations term_subst (f: A -> term) (t: term) : term := {
  term_subst f 0 := 0;
  term_subst f 1 := 1;
  term_subst f ($ a) := f a;
  term_subst f (t1 + t2) := term_subst f t1 + term_subst f t2;
  term_subst f (t1 ;; t2) := term_subst f t1 ;; term_subst f t2;
  term_subst f (t*) := (term_subst f t)*
}.

Lemma term_subst_preserve (f: A -> term) (t1 t2: term):
  t1 == t2 ->
  term_subst f t1 == term_subst f t2
.
Proof.
  intros.
  dependent induction H0;
  autorewrite with term_subst.
  - reflexivity.
  - now symmetry.
  - now transitivity (term_subst f t2).
  - now rewrite IHterm_equiv1, IHterm_equiv2.
  - now rewrite IHterm_equiv1, IHterm_equiv2.
  - now rewrite IHterm_equiv.
  - apply EPlusIdemp.
  - apply EPlusComm.
  - apply EPlusAssoc.
  - apply EPlusUnit.
  - apply ETimesAssoc.
  - apply ETimesUnitRight.
  - apply ETimesUnitLeft.
  - apply ETimesZeroLeft.
  - apply ETimesZeroRight.
  - apply EDistributeLeft.
  - apply EDistributeRight.
  - apply EStarLeft.
  - autorewrite with term_subst in IHterm_equiv.
    now apply EFixLeft.
Qed.

Variable (a1 a2: A).
Hypotheses (HDiff: a1 <> a2).

Definition subst2 (t1 t2: term) (a: A) : term :=
  if finite_dec a1 a then t1
  else if finite_dec a2 a then t2
  else 0
.

Ltac force_subst_check :=
  autorewrite with term_subst; unfold subst2; simpl;
  pose proof HDiff;
  repeat destruct (finite_dec _ _); subst; try contradiction;
  reflexivity.

Lemma denest_general (t1 t2: term):
  (t1 + t2)* == t1* ;; (t2 ;; t1*) *
.
Proof.
  replace ((t1 + t2)*)
    with (term_subst (subst2 t1 t2) (($a1 + $a2)*))
    by force_subst_check.
  replace (t1 *;; (t2;; t1 *) *)
    with (term_subst (subst2 t1 t2) ($a1 *;; ($a2;; $a1 *) *))
    by force_subst_check.
  apply term_subst_preserve, denest.
Qed.

Lemma starstar_general (t: term):
  t * * == t*
.
Proof.
  replace (t * *)
    with (term_subst (subst2 t t) ($a1 * *))
    by force_subst_check.
  replace (t*)
    with (term_subst (subst2 t t) ($a1*))
    by force_subst_check.
  eapply term_subst_preserve, starstar.
Qed.

Lemma slide_general (t1 t2: term):
  (t1 ;; t2)* ;; t1 == t1 ;; (t2 ;; t1)*
.
Proof.
  replace ((t1 ;; t2)* ;; t1)
    with (term_subst (subst2 t1 t2) (($a1 ;; $a2)* ;; $a1))
    by force_subst_check.
  replace (t1 ;; (t2 ;; t1)*)
    with (term_subst (subst2 t1 t2) ($a1 ;; ($a2 ;; $a1)*))
    by force_subst_check.
  eapply term_subst_preserve, slide.
Qed.
