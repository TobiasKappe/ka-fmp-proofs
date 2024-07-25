From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
Require Import Coq.btauto.Btauto.

Require Import KA.Finite.
Require Import KA.Scope.
Local Open Scope ka_scope.

Section TermSyntax.
  Context {A: Type}.

  Inductive term :=
  | zero: term
  | one: term
  | letter: A -> term
  | plus: term -> term -> term
  | times: term -> term -> term
  | star: term -> term
  .

  Derive NoConfusion for term.
End TermSyntax.

Arguments term A : clear implicits.

Notation "0" := zero : ka_scope.
Notation "1" := one : ka_scope.
Notation "$ a" :=
  (letter a)
  (at level 30)
  : ka_scope
.
Notation "t1 + t2" :=
  (plus t1 t2)
  (at level 50, left associativity)
  : ka_scope
.
Notation "t1 ;; t2" :=
  (times t1 t2)
  (at level 40, left associativity)
  : ka_scope
.
Notation "t *" :=
  (star t)
  (at level 30)
  : ka_scope
.

Section TermEquivalence.
  Context {A: Type}.
  Notation term := (term A).

  Reserved Notation "t1 == t2" (at level 70).
  Reserved Notation "t1 <= t2" (at level 70).

  Inductive term_equiv: term -> term -> Prop :=
  | ERefl: forall t, t == t
  | ESym: forall t1 t2, t1 == t2 -> t2 == t1
  | ETrans: forall t1 t2 t3, t1 == t2 -> t2 == t3 -> t1 == t3
  | ECongPlus: forall t1 t2 t3 t4, t1 == t2 -> t3 == t4 -> t1 + t3 == t2 + t4
  | ECongTimes: forall t1 t2 t3 t4, t1 == t2 -> t3 == t4 -> t1 ;; t3 == t2 ;; t4
  | ECongStar: forall t1 t2, t1 == t2 -> t1 * == t2 *
  | EPlusIdemp: forall t, t + t == t
  | EPlusComm: forall t1 t2, t1 + t2 == t2 + t1
  | EPlusAssoc: forall t1 t2 t3, t1 + (t2 + t3) == (t1 + t2) + t3
  | EPlusUnit: forall t, t + 0 == t
  | ETimesAssoc: forall t1 t2 t3, t1 ;; (t2 ;; t3) == (t1 ;; t2) ;; t3
  | ETimesUnitRight: forall t, t ;; 1 == t
  | ETimesUnitLeft: forall t, 1 ;; t == t
  | ETimesZeroLeft: forall t, t ;; 0 == 0
  | ETimesZeroRight: forall t, 0 ;; t == 0
  | EDistributeLeft: forall t1 t2 t3, t1 ;; (t2 + t3) == t1 ;; t2 + t1 ;; t3
  | EDistributeRight: forall t1 t2 t3, (t1 + t2) ;; t3 == t1 ;; t3 + t2 ;; t3
  | EStarLeft: forall t, t* == t ;; t* + 1
  | EFixLeft: forall t1 t2 t3, t2 ;; t1 + t3 <= t1 -> t2* ;; t3 <= t1
  where "t1 == t2" := (term_equiv t1 t2) : ka_scope
    and "t1 <= t2" := (t1 + t2 == t2) : ka_scope.

  Global Add Relation term term_equiv
    reflexivity proved by ERefl
    symmetry proved by ESym
    transitivity proved by ETrans
    as equiv_eq
  .

  Global Add Morphism plus
    with signature term_equiv ==> term_equiv ==> term_equiv
    as plus_mor
  .
  Proof.
    intros.
    now apply ECongPlus.
  Qed.

  Global Add Morphism times
    with signature term_equiv ==> term_equiv ==> term_equiv
    as times_mor
  .
  Proof.
    intros.
    now apply ECongTimes.
  Qed.

  Global Add Morphism star
    with signature term_equiv ==> term_equiv
    as star_mor
  .
  Proof.
    intros.
    now apply ECongStar.
  Qed.

  Definition term_lequiv (t1 t2: term) := t1 <= t2.
  (* Hint Unfold term_lequiv : core. *)

  Lemma term_lequiv_refl (t: term):
    t <= t
  .
  Proof.
    now rewrite EPlusIdemp.
  Qed.

  Lemma term_lequiv_trans (t1 t2 t3: term):
    t1 <= t2 -> t2 <= t3 -> t1 <= t3
  .
  Proof.
    intros.
    rewrite <- H0.
    rewrite <- H.
    repeat rewrite EPlusAssoc.
    rewrite EPlusIdemp.
    reflexivity.
  Qed.

  Lemma term_lequiv_zero (t: term):
    0 <= t
  .
  Proof.
    now rewrite EPlusComm, EPlusUnit.
  Qed.

  Global Add Relation term term_lequiv
    reflexivity proved by term_lequiv_refl
    transitivity proved by term_lequiv_trans
    as term_lequiv_po
  .

  Global Instance term_equiv_implies_lequiv: subrelation term_equiv term_lequiv.
  Proof.
    unfold subrelation, term_lequiv; intros.
    rewrite H.
    now rewrite EPlusIdemp.
  Qed.
End TermEquivalence.

Notation "t1 == t2" := (term_equiv t1 t2) (at level 70) : ka_scope.
Notation "t1 <= t2" := (t1 + t2 == t2) (at level 70) : ka_scope.

Ltac fold_term_lequiv :=
  match goal with
  | |- ?lhs <= ?rhs => fold (term_lequiv lhs rhs)
  end
.

Section TermProperties.
  Context {A: Type}.
  Notation term := (term A).

  Lemma term_lequiv_split_left
    (t1 t2 t3: term)
  :
    t1 <= t2 -> t1 <= t2 + t3
  .
  Proof.
    intros.
    rewrite <- H.
    repeat rewrite EPlusAssoc.
    now rewrite EPlusIdemp.
  Qed.

  Lemma term_lequiv_split_right
    (t1 t2 t3: term)
  :
    t1 <= t3 -> t1 <= t2 + t3
  .
  Proof.
    intros.
    rewrite <- H.
    rewrite EPlusAssoc with (t1 := t2).
    rewrite EPlusComm with (t1 := t2).
    repeat rewrite EPlusAssoc.
    now rewrite EPlusIdemp.
  Qed.

  Lemma term_lequiv_split
    (t1 t2 t3: term)
  :
    t1 <= t3 -> t2 <= t3 -> t1 + t2 <= t3
  .
  Proof.
    intros.
    rewrite <- H, <- H0.
    rewrite EPlusAssoc with (t1 := t1).
    rewrite EPlusAssoc with (t1 := (t1 + t2)).
    now rewrite EPlusIdemp.
  Qed.

  Global Add Morphism plus
    with signature term_lequiv ==> term_lequiv ==> (@term_lequiv A)
    as plus_mor_mono
  .
  Proof.
    unfold term_lequiv; intros.
    apply term_lequiv_split.
    - rewrite <- H.
      repeat apply term_lequiv_split_left.
      apply term_lequiv_refl.
    - rewrite <- H0.
      apply term_lequiv_split_right.
      apply term_lequiv_split_left.
      apply term_lequiv_refl.
  Qed.

  Global Add Morphism times
    with signature term_lequiv ==> term_lequiv ==> (@term_lequiv A)
    as times_mor_mono
  .
  Proof.
    unfold term_lequiv; intros.
    rewrite <- H, <- H0.
    rewrite EDistributeLeft.
    repeat rewrite EDistributeRight.
    repeat apply term_lequiv_split_left.
    apply term_lequiv_refl.
  Qed.

  Lemma term_lequiv_squeeze
    (t1 t2: term)
  :
    t1 <= t2 ->
    t2 <= t1 ->
    t1 == t2
  .
  Proof.
    intros.
    rewrite <- H.
    rewrite <- H0 at 1.
    rewrite EPlusComm.
    reflexivity.
  Qed.
End TermProperties.

Section TermSum.
  Context {A: Type}.
  Notation term := (term A).

  Equations sum (l: list term): term := {
    sum nil := 0;
    sum (t :: l) := t + sum l;
  }.

  Lemma sum_split (l1 l2: list term):
    sum (l1 ++ l2) == sum l1 + sum l2
  .
  Proof.
    revert l2; induction l1; intros.
    - autorewrite with sum.
      now rewrite EPlusComm, EPlusUnit, app_nil_l.
    - rewrite <- app_comm_cons.
      autorewrite with sum.
      rewrite <- EPlusAssoc.
      now rewrite IHl1.
  Qed.

  Lemma sum_distribute_right (l: list term) (t: term):
    sum (map (fun x => x ;; t) l) == sum l ;; t
  .
  Proof.
    induction l; simpl; autorewrite with sum.
    - now rewrite ETimesZeroRight.
    - rewrite IHl.
      now rewrite EDistributeRight.
  Qed.

  Lemma sum_distribute_left (l: list term) (t: term):
    sum (map (fun x => t ;; x) l) == t ;; sum l
  .
  Proof.
    induction l; simpl; autorewrite with sum.
    - now rewrite ETimesZeroLeft.
    - rewrite IHl.
      now rewrite EDistributeLeft.
  Qed.

  Lemma sum_lequiv_member
    (t: term)
    (l: list term)
  :
    In t l ->
    t <= sum l
  .
  Proof.
    intros; induction l; destruct H.
    - subst.
      autorewrite with sum.
      apply term_lequiv_split_left.
      apply term_lequiv_refl.
    - autorewrite with sum.
      apply term_lequiv_split_right.
      now apply IHl.
  Qed.

  Lemma sum_lequiv_all
    (l: list term)
    (t: term)
  :
    (forall (t': term), In t' l -> t' <= t) ->
    sum l <= t
  .
  Proof.
    intros.
    induction l.
    - autorewrite with sum.
      apply term_lequiv_zero.
    - autorewrite with sum.
      apply term_lequiv_split.
      + apply H.
        now left.
      + apply IHl; intros.
        apply H.
        now right.
  Qed.

  Lemma sum_lequiv_containment
    (l1 l2: list term)
  :
    incl l1 l2 ->
    sum l1 <= sum l2
  .
  Proof.
    intros.
    apply sum_lequiv_all; intros.
    apply sum_lequiv_member.
    now apply H.
  Qed.

  Lemma sum_equiv_containment
    (l1 l2: list term)
  :
    incl l1 l2 ->
    incl l2 l1 ->
    sum l1 == sum l2
  .
  Proof.
    intros.
    apply term_lequiv_squeeze;
    now apply sum_lequiv_containment.
  Qed.
End TermSum.

Section TermMatches.
  Context {A: Type}.
  Notation term := (term A).

  Inductive term_matches: term -> list A -> Prop :=
  | MatchOne:
      term_matches 1 nil
  | MatchLetter:
      forall (a: A),
      term_matches ($ a) (a :: nil)
  | MatchPlusLeft:
      forall (w: list A) (t1 t2: term),
      term_matches t1 w ->
      term_matches (t1 + t2) w
  | MatchPlusRight:
      forall (w: list A) (t1 t2: term),
      term_matches t2 w ->
      term_matches (t1 + t2) w
  | MatchTimes:
      forall (w1 w2: list A) (t1 t2: term),
      term_matches t1 w1 ->
      term_matches t2 w2 ->
      term_matches (t1 ;; t2) (w1 ++ w2)
  | MatchStarBase:
      forall (t: term),
      term_matches (t*) nil
  | MatchStarStep:
      forall (t: term) (w1 w2: list A),
      term_matches t w1 ->
      term_matches (t*) w2 ->
      term_matches (t*) (w1 ++ w2)
  .

  Lemma term_matches_star_split (t: term) (w: list A):
    term_matches (t*) w <->
    exists (l: list (list A)),
      w = concat l /\
      forall (w': list A), In w' l -> term_matches t w'
  .
  Proof.
    split; intros.
    - dependent induction H.
      + now exists nil.
      + specialize (IHterm_matches2 t eq_refl).
        destruct IHterm_matches2 as [l [? ?]]; subst.
        exists (w1 :: l).
        intuition.
        destruct H1.
        * now subst.
        * now apply H2.
    - destruct H as [l [? ?]]; subst.
      induction l; simpl.
      + apply MatchStarBase.
      + apply MatchStarStep.
        * apply H0.
          now left.
        * apply IHl; intros.
          apply H0.
          now right.
  Qed.

  Lemma term_equiv_sound (t1 t2: term) (w: list A):
    t1 == t2 ->
    term_matches t1 w <-> term_matches t2 w
  .
  Proof.
    intros.
    revert w; dependent induction H; intros.
    - reflexivity.
    - now symmetry.
    - now transitivity (term_matches t2 w).
    - split; intros.
      + dependent destruction H1.
        * apply MatchPlusLeft; intuition.
        * apply MatchPlusRight; intuition.
      + dependent destruction H1.
        * apply MatchPlusLeft; intuition.
        * apply MatchPlusRight; intuition.
    - split; intros.
      + dependent destruction H1.
        apply MatchTimes; intuition.
      + dependent destruction H1.
        apply MatchTimes; intuition.
    - split; intros.
      + dependent induction H0.
        * apply MatchStarBase.
        * apply MatchStarStep; intuition.
      + dependent induction H0.
        * apply MatchStarBase.
        * apply MatchStarStep; intuition.
    - split; intros.
      + now dependent destruction H.
      + now apply MatchPlusLeft.
    - split; intros.
      + dependent destruction H.
        * now apply MatchPlusRight.
        * now apply MatchPlusLeft.
      + dependent destruction H.
        * now apply MatchPlusRight.
        * now apply MatchPlusLeft.
    - split; intros.
      + dependent destruction H; [| dependent destruction H].
        * now apply MatchPlusLeft, MatchPlusLeft.
        * now apply MatchPlusLeft, MatchPlusRight.
        * now apply MatchPlusRight.
      + dependent destruction H; [dependent destruction H|].
        * now apply MatchPlusLeft.
        * now apply MatchPlusRight, MatchPlusLeft.
        * now apply MatchPlusRight, MatchPlusRight.
    - split; intros.
      + now dependent destruction H.
      + now apply MatchPlusLeft.
    - split; intros.
      + dependent destruction H.
        dependent destruction H0.
        rewrite app_assoc.
        apply MatchTimes; auto.
        now apply MatchTimes.
      + dependent destruction H.
        dependent destruction H.
        rewrite <- app_assoc.
        apply MatchTimes; auto.
        now apply MatchTimes.
    - split; intros.
      + dependent destruction H.
        dependent destruction H0.
        now rewrite app_nil_r.
      + rewrite <- app_nil_r.
        apply MatchTimes; auto.
        apply MatchOne.
    - split; intros.
      + dependent destruction H.
        dependent destruction H.
        now rewrite app_nil_l.
      + rewrite <- app_nil_l.
        apply MatchTimes; auto.
        apply MatchOne.
    - split; intros.
      + dependent destruction H.
        dependent destruction H0.
      + dependent destruction H.
    - split; intros.
      + dependent destruction H.
        dependent destruction H.
      + dependent destruction H.
    - split; intros.
      + dependent destruction H.
        dependent destruction H0.
        * apply MatchPlusLeft.
          now apply MatchTimes.
        * apply MatchPlusRight.
          now apply MatchTimes.
      + dependent destruction H.
        * dependent destruction H.
          apply MatchTimes; auto.
          now apply MatchPlusLeft.
        * dependent destruction H.
          apply MatchTimes; auto.
          now apply MatchPlusRight.
    - split; intros.
      + dependent destruction H.
        dependent destruction H.
        * apply MatchPlusLeft.
          now apply MatchTimes.
        * apply MatchPlusRight.
          now apply MatchTimes.
      + dependent destruction H.
        * dependent destruction H.
          apply MatchTimes; auto.
          now apply MatchPlusLeft.
        * dependent destruction H.
          apply MatchTimes; auto.
          now apply MatchPlusRight.
    - split; intros.
      + dependent destruction H.
        * now apply MatchPlusRight, MatchOne.
        * now apply MatchPlusLeft, MatchTimes.
      + dependent destruction H.
        * dependent destruction H.
          now apply MatchStarStep.
        * dependent destruction H.
          apply MatchStarBase.
    - split; intros.
      + dependent destruction H0; auto.
        dependent destruction H0.
        apply term_matches_star_split in H0_.
        destruct H0_ as [l [? ?]].
        subst; induction l; simpl.
        * apply IHterm_equiv.
          now apply MatchPlusLeft, MatchPlusRight.
        * apply IHterm_equiv.
          apply MatchPlusLeft, MatchPlusLeft.
          rewrite <- app_assoc.
          apply MatchTimes; intuition.
      + now apply MatchPlusRight.
  Qed.

  Lemma term_matches_sum (l: list term) (w: list A):
    term_matches (sum l) w <->
    exists (t: term),
      In t l /\ term_matches t w
  .
  Proof.
    induction l; autorewrite with sum.
    - split; intros.
      + dependent destruction H.
      + now destruct H as [t [? ?]].
    - split; intros.
      + dependent destruction H.
        * exists a; intuition.
        * apply IHl in H.
          destruct H as [t [? ?]].
          exists t; intuition.
      + destruct H as [t [[? | ?] ?]].
        * subst.
          now apply MatchPlusLeft.
        * apply MatchPlusRight.
          apply IHl.
          now exists t.
  Qed.

  Lemma term_matches_prepend_letter (t: term) (a: A):
    ~ term_matches ($a ;; t) nil
  .
  Proof.
    intro.
    dependent destruction H.
    dependent destruction H.
    rewrite <- app_comm_cons in x.
    inversion x.
  Qed.

  Lemma term_matches_star_progress
    (t: term)
    (w: list A)
    (a: A)
  :
    term_matches (t*) (a :: w) ->
    exists w1 w2,
      w = w1 ++ w2 /\
      term_matches t (a :: w1) /\
      term_matches (t*) w2
  .
  Proof.
    intros.
    dependent induction H.
    destruct w1; simpl in x; subst.
    - apply IHterm_matches2; eauto.
    - inversion x; subst; clear x.
      eexists; intuition eauto.
  Qed.
End TermMatches.

Section TermEmpty.
  Context {A: Type}.
  Context `{Finite A}.
  Notation term := (term A).

  Equations term_empty (t: term): bool := {
    term_empty 0 := true;
    term_empty 1 := false;
    term_empty ($ a) := false;
    term_empty (t1 + t2) := term_empty t1 && term_empty t2;
    term_empty (t1 ;; t2) := term_empty t1 || term_empty t2;
    term_empty (t*) := false
  }.

  Lemma term_empty_dec (t: term):
    term_empty t = false <-> exists w, term_matches t w
  .
  Proof.
    induction t;
    autorewrite with term_empty.
    - intuition.
      destruct H0 as [w ?].
      dependent destruction H0.
    - intuition.
      exists nil.
      apply MatchOne.
    - intuition.
      exists (a :: nil).
      apply MatchLetter.
    - rewrite Bool.andb_false_iff.
      rewrite IHt1, IHt2.
      split; intros.
      + destruct H0.
        * destruct H0 as [w ?].
          exists w.
          now apply MatchPlusLeft.
        * destruct H0 as [w ?].
          exists w.
          now apply MatchPlusRight.
      + destruct H0 as [w ?].
        dependent destruction H0.
        * left; now exists w.
        * right; now exists w.
    - rewrite Bool.orb_false_iff.
      rewrite IHt1, IHt2.
      split; intros.
      + destruct H0.
        destruct H0 as [w1 ?], H1 as [w2 ?].
        exists (w1 ++ w2).
        now apply MatchTimes.
      + destruct H0 as [w ?].
        dependent destruction H0.
        split.
        * now exists w1.
        * now exists w2.
    - intuition.
      exists nil.
      apply MatchStarBase.
  Qed.

  Lemma term_empty_zero (t: term):
    term_empty t = true ->
    t == 0
  .
  Proof.
    induction t;
    autorewrite with term_empty;
    intros.
    - reflexivity.
    - discriminate.
    - discriminate.
    - rewrite Bool.andb_true_iff in H0.
      destruct H0.
      rewrite IHt1, IHt2; auto.
      apply term_lequiv_refl.
    - rewrite Bool.orb_true_iff in H0.
      destruct H0.
      + rewrite IHt1 by auto.
        now rewrite ETimesZeroRight.
      + rewrite IHt2 by auto.
        now rewrite ETimesZeroLeft.
    - discriminate.
  Qed.

  Lemma term_empty_invariant (t1 t2: term):
    t1 == t2 ->
    term_empty t1 = term_empty t2
  .
  Proof.
    intros.
    dependent induction H0;
    autorewrite with term_empty in *;
    try congruence;
    try rewrite <- IHterm_equiv;
    btauto.
  Qed.

  Lemma term_zero_empty (t: term):
    t == 0 ->
    term_empty t = true
  .
  Proof.
    intros.
    now apply term_empty_invariant in H0.
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
      + destruct (IHterm_matches2 H t eq_refl) as [n ?].
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
End TermEmpty.

Section TermSubst.
  Context {A: Type}.
  Notation term := (term A).

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
    dependent induction H;
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
End TermSubst.
