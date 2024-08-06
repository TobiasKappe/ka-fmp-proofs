Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.

Require Import KA.Terms.
Require Import KA.Finite.
Require Import KA.Main.
Require Import KA.Scope.
Local Open Scope ka_scope.

Section DerivedBase.
  Variable (A: Type).
  Context `{Finite A}.
  Notation term := (term A).

  Lemma starstar (a: A):
    ($ a) * * == ($ a)*
  .
  Proof.
    apply completeness; auto; extensionality w.
    apply propositional_extensionality; intuition.
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

  Lemma slide (a b: A):
    ($ a ;; $ b)* ;; $a == $a ;; ($ b ;; $ a)*
  .
  Proof.
    apply completeness; auto; extensionality w.
    apply propositional_extensionality; intuition.
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

  Lemma denest (a b: A):
    ($ a + $ b)* == ($ a)* ;; ($b ;; ($ a)*) *
  .
  Proof.
    apply completeness; auto; extensionality w.
    apply propositional_extensionality; intuition.
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
End DerivedBase.

Section DerivedProper.
  Variable (A: Type).
  Variable (a1 a2: A).
  Context `{Finite A}.
  Hypotheses (HDiff: a1 <> a2).
  Notation term := (term A).

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
    now apply term_subst_preserve, denest.
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
    now eapply term_subst_preserve, starstar.
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
    now eapply term_subst_preserve, slide.
  Qed.
End DerivedProper.
