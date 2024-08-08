Require Import Coq.Setoids.Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import KA.Finite.
Require Import KA.Booleans.
Require Import KA.Terms.
Require Import KA.Scope.
Require Import KA.Utilities.
Local Open Scope ka_scope.

Section Vectors.
  Variable (A: Type).
  Notation term := (term A).

  Definition vector (Q: Type) := Q -> term.

  Definition matrix (Q: Type) := Q -> Q -> term.
End Vectors.

Section VectorOperations.
  Context {A: Type}.
  Notation term := (term A).
  Notation vector := (vector A).
  Notation matrix := (matrix A).

  Definition vector_sum
    {Q: Type}
    (v1 v2: vector Q)
    (q: Q)
    : term
  :=
    (v1 q + v2 q)%ka
  .

  Definition vector_chomp
    {n: nat}
    (v: vector (position (S n)))
    (p: position n)
    : term
  :=
    v (PThere p)
  .

  Equations inner_product {n: nat} (v1 v2: vector (position n)): term := {
    @inner_product 0 _ _ :=
      zero;
    @inner_product (S _) v1 v2 :=
      v1 PHere ;; v2 PHere + inner_product (vector_chomp v1) (vector_chomp v2);
  }.

  Definition matrix_vector_product
    {n: nat}
    (m: matrix (position n))
    (v: vector (position n))
    (p: position n)
  :=
    inner_product (m p) v
  .

  Definition vector_scale_left
    {Q: Type}
    (t: term)
    (v: vector Q)
    (q: Q)
  :=
    t ;; v q
  .

  Definition vector_scale_right
    {Q: Type}
    (v: vector Q)
    (t: term)
    (q: Q)
  :=
    v q ;; t
  .

  Definition vector_index
    {X: Type}
    `{Finite X}
    (v: vector X)
    (p: position (length finite_enum))
  :
    term
  :=
    v (list_lookup p)
  .

  Definition vector_lookup
    {X: Type}
    `{Finite X}
    (v: vector (position (length finite_enum)))
    (x: X)
  :
    term
  :=
    v (list_index x)
  .

  Definition matrix_index
    {X: Type}
    `{Finite X}
    (m: matrix X)
    (p p': position (length finite_enum))
  :
    term
  :=
    m (list_lookup p) (list_lookup p')
  .

  Definition matrix_lookup
    {X: Type}
    `{Finite X}
    (m: matrix (position (length finite_enum)))
    (x x': X)
  :
    term
  :=
    m (list_index x) (list_index x')
  .
End VectorOperations.

Notation "v1 <+> v2" := (vector_sum v1 v2) (at level 40) : ka_scope.
Notation "# v" := (vector_chomp v) (at level 30) : ka_scope.
Notation "v1 ** v2" := (inner_product v1 v2) (at level 40) : ka_scope.
Notation "m <*> v" := (matrix_vector_product m v) (at level 40) : ka_scope.
Notation "t & v" := (vector_scale_left t v) (at level 30) : ka_scope.
Notation "v ;;; t" := (vector_scale_right v t) (at level 35) : ka_scope.

Section VectorEquiv.
  Context {A: Type}.
  Notation term := (term A).
  Notation vector := (vector A).

  Definition equiv_vec {Q: Type} (v1 v2: vector Q): Prop :=
    forall (q: Q), v1 q == v2 q
  .

  Notation "v1 === v2" := (equiv_vec v1 v2) (at level 70).

  Lemma equiv_vec_refl {Q: Type} (v: vector Q):
    v === v
  .
  Proof.
    now intro.
  Qed.

  Lemma equiv_vec_sym {Q: Type} (v1 v2: vector Q):
    v1 === v2 -> v2 === v1
  .
  Proof.
    intro; now intro.
  Qed.

  Lemma equiv_vec_trans {Q: Type} (v1 v2 v3: vector Q):
    v1 === v2 -> v2 === v3 -> v1 === v3
  .
  Proof.
    intros; intro.
    now transitivity (v2 q).
  Qed.

  Global Add Parametric Relation (Q: Type): (vector Q) equiv_vec
    reflexivity proved by equiv_vec_refl
    symmetry proved by equiv_vec_sym
    transitivity proved by equiv_vec_trans
    as equiv_equiv_vec
  .

  Global Add Parametric Morphism (Q: Type): vector_sum
    with signature (@equiv_vec Q) ==> equiv_vec ==> equiv_vec
    as vector_sum_mor
  .
  Proof.
    intros; intro.
    unfold vector_sum.
    now rewrite (H q), (H0 q).
  Qed.

  Global Add Parametric Morphism (n: nat): vector_chomp
    with signature (@equiv_vec (position (S n))) ==> equiv_vec
    as vector_comp_mor.
  Proof.
    intros.
    intro.
    unfold vector_chomp.
    now rewrite (H (PThere q)).
  Qed.

  Global Add Parametric Morphism (n: nat): inner_product
    with signature (@equiv_vec (position n)) ==> equiv_vec ==> term_equiv
    as inner_product_mor
  .
  Proof.
    intros.
    dependent induction n.
    - autorewrite with inner_product.
      reflexivity.
    - autorewrite with inner_product.
      rewrite (H PHere), (H0 PHere).
      apply ECongPlus; try reflexivity.
      apply IHn.
      + now rewrite H.
      + now rewrite H0.
  Qed.

  Definition lequiv_vec {Q: Type} (v1 v2: vector Q): Prop :=
    forall (q: Q), v1 q <= v2 q
  .
End VectorEquiv.

Notation "v1 === v2" := (equiv_vec v1 v2) (at level 70) : ka_scope.
Notation "v1 <== v2" := (lequiv_vec v1 v2) (at level 70) : ka_scope.

Section VectorProperties.
  Context {A: Type}.
  Notation term := (term A).
  Notation vector := (vector A).

  Lemma vector_scale_left_chomp
    {n: nat}
    (t: term)
    (v: vector (position (S n)))
  :
    t & (# v) === # (t & v)
  .
  Proof.
    now intro.
  Qed.

  Lemma vector_inner_product_scale_left
    {n: nat}
    (t: term)
    (v1 v2: vector (position n))
  :
    t ;; (v1 ** v2) == (t & v1) ** v2
  .
  Proof.
    dependent induction n.
    - autorewrite with inner_product.
      now rewrite ETimesZeroLeft.
    - autorewrite with inner_product.
      rewrite EDistributeLeft.
      rewrite IHn.
      unfold vector_scale_left at 2; simpl.
      rewrite vector_scale_left_chomp.
      rewrite ETimesAssoc.
      reflexivity.
  Qed.

  Lemma vector_chomp_sum
    {n: nat}
    (v1 v2: vector (position (S n)))
  :
    # (v1 <+> v2) === # v1 <+> # v2
  .
  Proof.
    now intro.
  Qed.

  Lemma vector_inner_product_distribute_left
    {n: nat}
    (v1 v2 v3: vector (position n))
  :
    v1 ** v3 + v2 ** v3 == (v1 <+> v2) ** v3
  .
  Proof.
    dependent induction n.
    - autorewrite with inner_product.
      now rewrite EPlusIdemp.
    - autorewrite with inner_product.
      rewrite EPlusAssoc.
      rewrite <- EPlusAssoc with (t3 := v2 PHere ;; v3 PHere).
      rewrite EPlusComm with (t1 := # v1 ** # v3).
      rewrite EPlusAssoc.
      rewrite <- EDistributeRight.
      rewrite <- EPlusAssoc.
      rewrite IHn.
      unfold vector_sum at 2.
      rewrite vector_chomp_sum.
      reflexivity.
  Qed.

  Lemma vector_inner_product_contained
    {n: nat}
    (v1 v2: vector (position n))
    (p: position n)
  :
    v1 p ;; v2 p <= v1 ** v2
  .
  Proof.
    dependent induction p.
    - autorewrite with inner_product.
      apply term_lequiv_split_left.
      apply term_lequiv_refl.
    - autorewrite with inner_product.
      apply term_lequiv_split_right.
      fold ((# v1) p).
      fold ((# v2) p).
      apply IHp.
  Qed.

  Global Add Parametric Morphism (n: nat): inner_product
    with signature eq ==> (@lequiv_vec A (position n)) ==> term_lequiv
    as inner_product_mor_mono
  .
  Proof.
    unfold term_lequiv; intros.
    dependent induction n.
    - autorewrite with inner_product.
      apply term_lequiv_refl.
    - autorewrite with inner_product.
      apply term_lequiv_split.
      + rewrite <- (H PHere).
        rewrite EDistributeLeft.
        repeat apply term_lequiv_split_left.
        apply term_lequiv_refl.
      + apply term_lequiv_split_right.
        apply IHn.
        intro p.
        apply H.
  Qed.

  Lemma vector_inner_product_contained_split
    {n: nat}
    (v1 v2: vector (position n))
    (t: term)
  :
    (forall p, v1 p ;; v2 p <= t) ->
    v1 ** v2 <= t
  .
  Proof.
    intros.
    dependent induction n.
    - autorewrite with inner_product.
      rewrite EPlusComm.
      now rewrite EPlusUnit.
    - autorewrite with inner_product.
      apply term_lequiv_split.
      + apply H.
      + apply IHn; intros.
        unfold vector_chomp.
        apply H.
  Qed.

  Lemma vector_scale_right_unit
    {Q: Type}
    (v: vector Q)
  :
    v ;;; 1 === v
  .
  Proof.
    intro q.
    unfold vector_scale_right.
    now rewrite ETimesUnitRight.
  Qed.

  Lemma vector_scale_right_chomp
    {n: nat}
    (v: vector (position (S n)))
    (t: term)
  :
    (# v) ;;; t === # (v ;;; t)
  .
  Proof.
    now intro.
  Qed.

  Lemma vector_inner_product_scale_right
    {n: nat}
    (v1 v2: vector (position n))
    (t: term)
  :
    (v1 ** v2) ;; t == v1 ** (v2 ;;; t)
  .
  Proof.
    dependent induction n.
    - autorewrite with inner_product.
      now rewrite ETimesZeroRight.
    - autorewrite with inner_product.
      rewrite EDistributeRight.
      rewrite IHn.
      unfold vector_scale_right at 2; simpl.
      rewrite vector_scale_right_chomp.
      rewrite ETimesAssoc.
      reflexivity.
  Qed.

  Lemma vector_lequiv_adjunction
    {X: Type}
    `{Finite X}
    (v1: vector (position (length finite_enum)))
    (v2: vector X)
  :
    v1 <== vector_index v2 <-> vector_lookup v1 <== v2
  .
  Proof.
    split; intros.
    - intro x.
      unfold vector_lookup.
      rewrite <- list_lookup_index with (x := x) at 2.
      rewrite <- list_lookup_index with (x := x) at 3.
      apply H0.
    - intro p.
      unfold vector_index.
      rewrite <- list_index_lookup at 1.
      apply H0.
  Qed.

  Lemma vector_lequiv_squeeze
    {X: Type}
    (v1 v2: vector X)
  :
    v1 <== v2 ->
    v2 <== v1 ->
    v1 === v2
  .
  Proof.
    intros; intro x.
    apply term_lequiv_squeeze.
    - apply H.
    - apply H0.
  Qed.
End VectorProperties.

Section VectorBool.
  Context {A: Type}.
  Notation vector := (vector A).
  Notation term := (term A).

  Global Program Instance matrix_finite
    (X Y: Type)
    `{Finite X}
    `{Finite Y}
  :
    Finite (X -> Y -> bool)
  := {|
    finite_enum := map curry finite_enum
  |}.
  Next Obligation.
    destruct (finite_dec (uncurry x1) (uncurry x2)).
    - left.
      extensionality x;
      extensionality y.
      replace x1 with (curry (uncurry x1)) by reflexivity.
      replace x2 with (curry (uncurry x2)) by reflexivity.
      now rewrite e.
    - right.
      contradict n.
      extensionality xy.
      destruct xy; simpl.
      now rewrite n.
  Defined.
  Next Obligation.
    replace x with (curry (uncurry x)) by reflexivity.
    handle_lists; eexists; intuition.
    replace finite_subsets
      with (@finite_enum (prod X Y -> bool) _)
      by reflexivity.
    apply finite_cover.
  Qed.
  Next Obligation.
    apply NoDup_map.
    - intros.
      extensionality xy.
      destruct xy.
      replace x with (uncurry (curry x)).
      replace y with (uncurry (curry y)).
      + simpl.
        now rewrite H1.
      + extensionality xy.
        now destruct xy.
      + extensionality xy.
        now destruct xy.
    - replace finite_subsets
        with (@finite_enum (prod X Y -> bool) _)
        by reflexivity.
      apply finite_nodup.
  Qed.

  Definition vector_inner_product_bool
    {X: Type}
    `{Finite X}
    (v1 v2: X -> bool)
  :
    bool
  :=
    disj (map (fun x => andb (v1 x) (v2 x)) finite_enum)
  .

  Definition matrix_product_bool
    {X: Type}
    `{Finite X}
    (m1 m2: X -> X -> bool)
    (x1 x2: X)
  :
    bool
  :=
    vector_inner_product_bool (m1 x1) (fun x => m2 x x2)
  .

  Lemma matrix_product_characterise
    {Q: Type}
    `{Finite Q}
    (m1 m2: Q -> Q -> bool)
    (q1 q2: Q)
  :
    matrix_product_bool m1 m2 q1 q2 = true <->
    exists (q3: Q), m1 q1 q3 = true /\ m2 q3 q2 = true
  .
  Proof.
    unfold matrix_product_bool.
    unfold vector_inner_product_bool.
    rewrite disj_true.
    handle_lists.
    setoid_rewrite Bool.andb_true_iff.
    split; intros.
    - destruct H0 as [q3 [? ?]].
      now exists q3.
    - destruct H0 as [q3 [? ?]].
      exists q3; intuition.
  Qed.

  Lemma matrix_product_bool_unit_left
    {Q: Type}
    `{Finite Q}
    (m: Q -> Q -> bool)
  :
    matrix_product_bool finite_eqb m = m
  .
  Proof.
    extensionality q1;
    extensionality q2.
    destruct (m _ _) eqn:?.
    - apply matrix_product_characterise.
      exists q1; intuition.
      unfold finite_eqb.
      now destruct (finite_dec _ _).
    - apply Bool.not_true_iff_false.
      apply Bool.not_true_iff_false in Heqb.
      contradict Heqb.
      apply matrix_product_characterise in Heqb.
      destruct Heqb as [q3 [? ?]].
      unfold finite_eqb in H0.
      destruct (finite_dec _ _).
      + now subst.
      + discriminate.
  Qed.

  Lemma matrix_product_bool_unit_right
    {Q: Type}
    `{Finite Q}
    (m: Q -> Q -> bool)
  :
    matrix_product_bool m finite_eqb = m
  .
  Proof.
    extensionality q1;
    extensionality q2.
    destruct (m _ _) eqn:?.
    - apply matrix_product_characterise.
      exists q2; intuition.
      unfold finite_eqb.
      now destruct (finite_dec _ _).
    - apply Bool.not_true_iff_false.
      apply Bool.not_true_iff_false in Heqb.
      contradict Heqb.
      apply matrix_product_characterise in Heqb.
      destruct Heqb as [q3 [? ?]].
      unfold finite_eqb in H1.
      destruct (finite_dec _ _).
      + now subst.
      + discriminate.
  Qed.

  Lemma matrix_product_bool_associative
    {Q: Type}
    `{Finite Q}
    (m1 m2 m3: Q -> Q -> bool)
  :
    matrix_product_bool (matrix_product_bool m1 m2) m3 =
    matrix_product_bool m1 (matrix_product_bool m2 m3)
  .
  Proof.
    extensionality q1;
    extensionality q2.
    destruct (matrix_product_bool _ _ _) eqn:?; symmetry.
    - apply matrix_product_characterise in Heqb.
      destruct Heqb as [q3 [? ?]].
      apply matrix_product_characterise in H0.
      destruct H0 as [q4 [? ?]].
      apply matrix_product_characterise.
      exists q4; intuition.
      apply matrix_product_characterise.
      exists q3; intuition.
    - apply Bool.not_true_iff_false.
      apply Bool.not_true_iff_false in Heqb.
      contradict Heqb.
      apply matrix_product_characterise in Heqb.
      destruct Heqb as [q3 [? ?]].
      apply matrix_product_characterise in H1.
      destruct H1 as [q4 [? ?]].
      apply matrix_product_characterise.
      exists q4; intuition.
      apply matrix_product_characterise.
      exists q3; intuition.
  Qed.

  Definition vector_shift_both
    {Q: Type}
    `{Finite Q}
    (v: vector (prod (Q -> Q -> bool) (Q -> Q -> bool)))
    (h: Q -> Q -> bool)
    (fg: prod (Q -> Q -> bool) (Q -> Q -> bool))
  :
    term
  :=
    v (matrix_product_bool h (fst fg), matrix_product_bool h (snd fg))
  .

  Definition vector_shift_single
    {Q: Type}
    `{Finite Q}
    (v: vector (prod (Q -> Q -> bool) (Q -> Q -> bool)))
    (h: Q -> Q -> bool)
    (fg: prod (Q -> Q -> bool) (Q -> Q -> bool))
  :
    term
  :=
    v (fst fg, matrix_product_bool (snd fg) h)
  .
End VectorBool.
