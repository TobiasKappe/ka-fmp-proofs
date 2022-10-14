From Equations Require Import Equations.
Require Import Coq.Setoids.Setoid.

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
