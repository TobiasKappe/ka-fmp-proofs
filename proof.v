From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.btauto.Btauto.
Local Open Scope program_scope.
Local Open Scope bool_scope.

Require Import KA.Finite.
Require Import KA.Booleans.
Require Import KA.Terms.
Require Import KA.Vectors.
Require Import KA.Solve.
Require Import KA.Antimirov.
Require Import KA.Automata.
Require Import KA.Scope.
Local Open Scope ka_scope.

Variable (A: Type).
Context `{Finite A}.

Notation term := (term A).
Notation matrix := (matrix A).
Notation vector := (vector A).
Notation system := (system A).
Notation derivative := (derivative A).
Notation initial := (initial A).
Notation nullable := (nullable A).
Notation automaton := (automaton A).

Record monoid {X: Type} := {
  monoid_compose: X -> X -> X;
  monoid_unit: X;

  monoid_compose_assoc:
    forall (x1 x2 x3: X),
      monoid_compose (monoid_compose x1 x2) x3 =
      monoid_compose x1 (monoid_compose x2 x3);
  monoid_unit_left:
    forall (x: X),
    monoid_compose x monoid_unit = x;
  monoid_unit_right:
    forall (x: X),
    monoid_compose monoid_unit x = x;
}.
Arguments monoid X : clear implicits.

Record kleene_algebra {X: Type} := {
  kleene_monoid: monoid X;
  kleene_plus: X -> X -> X;
  kleene_star: X -> X;
  kleene_zero: X;

  kleene_unit := monoid_unit kleene_monoid;
  kleene_multiply := monoid_compose kleene_monoid;

  kleene_plus_assoc:
    forall (x1 x2 x3: X),
      kleene_plus (kleene_plus x1 x2) x3 =
      kleene_plus x1 (kleene_plus x2 x3);
  kleene_plus_unit:
    forall (x: X),
      kleene_plus x kleene_zero = x;
  kleene_plus_idempotent:
    forall (x: X),
      kleene_plus x x = x;
  kleene_plus_commute:
    forall (x1 x2: X),
      kleene_plus x1 x2 = kleene_plus x2 x1;
  kleene_multiply_zero_left:
    forall (x: X),
      kleene_multiply kleene_zero x = kleene_zero;
  kleene_multiply_zero_right:
    forall (x: X),
      kleene_multiply x kleene_zero = kleene_zero;
  kleene_distribute_left:
    forall (x1 x2 x3: X),
      kleene_multiply x1 (kleene_plus x2 x3) =
      kleene_plus (kleene_multiply x1 x2) (kleene_multiply x1 x3);
  kleene_distribute_right:
    forall (x1 x2 x3: X),
      kleene_multiply (kleene_plus x1 x2) x3 =
      kleene_plus (kleene_multiply x1 x3) (kleene_multiply x2 x3);
  kleene_star_unroll:
    forall (x: X),
      kleene_plus kleene_unit (kleene_multiply x (kleene_star x)) =
      kleene_star x;
  kleene_star_fixpoint:
    forall (x1 x2 x3: X),
      kleene_plus (kleene_plus (kleene_multiply x1 x2) x3) x2 = x2 ->
      kleene_plus (kleene_multiply (kleene_star x1) x3) x2 = x2
}.
Arguments kleene_algebra X : clear implicits.

Definition powerset_multiplication
  {X: Type}
  `{Finite X}
  (M: monoid X)
  (xs1 xs2: X -> bool)
  (x: X)
:
  bool
:=
  disj (
    map (fun '(x1, x2) =>
      finite_eqb x (monoid_compose M x1 x2) &&
      xs1 x1 && xs2 x2
    )
    (list_prod finite_enum finite_enum)
  )
.

Lemma powerset_multiplication_characterise
  {X: Type}
  `{Finite X}
  (M: monoid X)
  (x1 x2: X -> bool)
  (x: X)
:
  powerset_multiplication M x1 x2 x = true <->
  exists (x1' x2': X),
    x1 x1' = true /\
    x2 x2' = true /\
    monoid_compose M x1' x2' = x
.
Proof.
  unfold powerset_multiplication.
  rewrite disj_true, in_map_iff.
  split; intros.
  - destruct H1 as [(x1', x2') [? ?]].
    repeat rewrite Bool.andb_true_iff in H1.
    destruct H1 as [[? ?] ?].
    apply finite_eqb_eq in H1.
    now exists x1', x2'.
  - destruct H1 as [x1' [x2' [? [? ?]]]].
    exists (x1', x2').
    repeat rewrite Bool.andb_true_iff; intuition.
    + now apply finite_eqb_eq.
    + replace (list_prod finite_enum finite_enum)
        with (finite_enum (X := (prod X X)))
        by reflexivity.
      apply finite_cover.
Qed.

Program Definition monoid_powerset
  {X: Type}
  `{Finite X}
  (M: monoid X)
:
  monoid (X -> bool)
:= {|
  monoid_compose := powerset_multiplication M;
  monoid_unit x := finite_eqb x (monoid_unit M);
|}.
Next Obligation.
  extensionality x.
  apply ZMicromega.eq_true_iff_eq.
  repeat rewrite powerset_multiplication_characterise.
  split; intros.
  - destruct H1 as [x' [x3' [? [? ?]]]].
    apply powerset_multiplication_characterise in H1.
    destruct H1 as [x1' [x2' [? [? ?]]]]; subst.
    exists x1', (monoid_compose M x2' x3'); intuition.
    + apply powerset_multiplication_characterise.
      now exists x2', x3'.
    + now rewrite monoid_compose_assoc.
  - destruct H1 as [x1' [x' [? [? ?]]]].
    apply powerset_multiplication_characterise in H2.
    destruct H2 as [x2' [x3' [? [? ?]]]]; subst.
    exists (monoid_compose M x1' x2'), x3'; intuition.
    apply powerset_multiplication_characterise.
    now exists x1', x2'.
Qed.
Next Obligation.
  extensionality x'.
  apply ZMicromega.eq_true_iff_eq.
  rewrite powerset_multiplication_characterise.
  split; intros.
  - destruct H1 as [x1' [x2' [? [? ?]]]].
    apply finite_eqb_eq in H2; subst.
    now rewrite monoid_unit_left.
  - exists x', (monoid_unit M).
    intuition.
    now apply finite_eqb_eq.
Qed.
Next Obligation.
  extensionality x'.
  apply ZMicromega.eq_true_iff_eq.
  rewrite powerset_multiplication_characterise.
  split; intros.
  - destruct H1 as [x1' [x2' [? [? ?]]]].
    apply finite_eqb_eq in H1; subst.
    now rewrite monoid_unit_right.
  - exists (monoid_unit M), x'.
    intuition.
    now apply finite_eqb_eq.
Qed.

Program Instance subset_order
  (X: Type)
:
  PartialOrderZero (X -> bool)
:= {|
  partial_order_rel xs1 xs2 := forall x, xs1 x = true -> xs2 x = true;
  partial_order_zero x := false;
|}.
Next Obligation.
  extensionality x.
  apply ZMicromega.eq_true_iff_eq.
  intuition.
Qed.

Definition powerset_union
  {X: Type}
  (xs1 xs2: X -> bool)
  (x: X)
:=
  xs1 x || xs2 x
.

Definition powerset_bottom
  {X: Type}
  (x: X)
:
  bool
:=
  false
.

Definition kleene_star_step
  {X: Type}
  `{Finite X}
  (M: monoid X)
  (xs xs': X -> bool)
:
  X -> bool
:=
  powerset_union (monoid_compose (monoid_powerset M) xs xs')
                 (monoid_unit (monoid_powerset M))
.

Lemma powerset_union_characterise
  {X: Type}
  (xs1 xs2: X -> bool)
  (x: X)
:
  powerset_union xs1 xs2 x = true <->
  xs1 x = true \/ xs2 x = true
.
Proof.
  unfold powerset_union.
  now rewrite Bool.orb_true_iff.
Qed.

Lemma powerset_union_order
  {X: Type}
  (xs1 xs2: X -> bool)
:
  powerset_union xs1 xs2 = xs2 <->
  partial_order_rel xs1 xs2
.
Proof.
  unfold partial_order_rel, powerset_union.
  simpl; split; intros.
  - now rewrite <- H0, H1.
  - extensionality x.
    apply ZMicromega.eq_true_iff_eq.
    rewrite Bool.orb_true_iff.
    firstorder.
Qed.

Definition kleene_star_step_offset
  {X: Type}
  `{Finite X}
  (M: monoid X)
  (xs1 xs2 xs3: X -> bool)
:
  X -> bool
:=
  powerset_union (powerset_multiplication M xs1 xs3) xs2
.

Lemma powerset_union_multiply_distribute_right
  {X: Type}
  `{Finite X}
  (M: monoid X)
  (xs1 xs2 xs3: X -> bool)
:
  powerset_multiplication M (powerset_union xs1 xs2) xs3 =
  powerset_union (powerset_multiplication M xs1 xs3)
                 (powerset_multiplication M xs2 xs3)
.
Proof.
  extensionality x'.
  unfold powerset_union.
  apply ZMicromega.eq_true_iff_eq.
  rewrite Bool.orb_true_iff.
  repeat rewrite powerset_multiplication_characterise.
  setoid_rewrite Bool.orb_true_iff.
  firstorder.
Qed.

Lemma powerset_union_multiply_distribute_left
  {X: Type}
  `{Finite X}
  (M: monoid X)
  (xs1 xs2 xs3: X -> bool)
:
  powerset_multiplication M xs1 (powerset_union xs2 xs3) =
  powerset_union (powerset_multiplication M xs1 xs2)
    (powerset_multiplication M xs1 xs3)
.
Proof.
  extensionality x'.
  unfold powerset_union.
  apply ZMicromega.eq_true_iff_eq.
  rewrite Bool.orb_true_iff.
  repeat rewrite powerset_multiplication_characterise.
  setoid_rewrite Bool.orb_true_iff.
  firstorder.
Qed.

Lemma powerset_union_commute
  {X: Type}
  (xs1 xs2: X -> bool)
:
  powerset_union xs1 xs2 =
  powerset_union xs2 xs1
.
Proof.
  extensionality x.
  unfold powerset_union.
  btauto.
Qed.

Lemma disj_false
  (l: list bool)
:
  disj l = false <->
  forall (x: bool), In x l -> x = false
.
Proof.
  split; intros.
  - induction l.
    + destruct H1.
    + autorewrite with disj in H0.
      apply Bool.orb_false_iff in H0.
      destruct H0, H1.
      * congruence.
      * now apply IHl.
  - induction l;
    autorewrite with disj.
    + reflexivity.
    + apply Bool.orb_false_iff.
      firstorder.
Qed.

Lemma kleene_star_step_offset_fixpoint
  {X: Type}
  `{Finite X}
  (M: monoid X)
  (xs1 xs2: X -> bool)
:
  mono_fixpoint (kleene_star_step_offset M xs1 xs2) =
  powerset_multiplication M (mono_fixpoint (kleene_star_step M xs1)) xs2
.
Proof.
  unfold mono_fixpoint.
  generalize (@length (X -> bool) finite_enum); intros.
  induction n; simpl in *.
  - extensionality x.
    unfold powerset_multiplication.
    symmetry; apply disj_false; intros.
    apply in_map_iff in H1.
    destruct H1 as [(x1, x2) [? ?]]; subst.
    btauto.
  - rewrite IHn.
    unfold kleene_star_step at 2, kleene_star_step_offset at 1.
    rewrite powerset_union_multiply_distribute_right.
    replace (powerset_multiplication M)
      with (monoid_compose (monoid_powerset M))
      by reflexivity.
    rewrite monoid_compose_assoc.
    now rewrite monoid_unit_right.
Qed.

Lemma powerset_multiplication_mono
  {X: Type}
  `{Finite X}
  (M: monoid X)
  (xs1 xs2 xs1' xs2': X -> bool)
:
  partial_order_rel xs1 xs1' ->
  partial_order_rel xs2 xs2' ->
  partial_order_rel (powerset_multiplication M xs1 xs2)
                    (powerset_multiplication M xs1' xs2')
.
Proof.
  simpl; setoid_rewrite powerset_multiplication_characterise; firstorder.
Qed.

Lemma powerset_union_mono
  {X: Type}
  `{Finite X}
  (xs1 xs2 xs1' xs2': X -> bool)
:
  partial_order_rel xs1 xs1' ->
  partial_order_rel xs2 xs2' ->
  partial_order_rel (powerset_union xs1 xs2)
                    (powerset_union xs1' xs2')
.
Proof.
  simpl; unfold powerset_union; setoid_rewrite Bool.orb_true_iff; firstorder.
Qed.

Lemma kleene_star_step_mono
  {X: Type}
  `{Finite X}
  (M: monoid X)
  (xs: X -> bool)
:
  monotone (kleene_star_step M xs)
.
Proof.
  constructor; intros.
  unfold kleene_star_step.
  apply powerset_union_mono.
  - apply powerset_multiplication_mono; auto.
    apply partial_order_refl.
  - apply partial_order_refl.
Qed.

Lemma kleene_star_step_offset_mono
  {X: Type}
  `{Finite X}
  (M: monoid X)
  (xs1 xs2: X -> bool)
:
  monotone (kleene_star_step_offset M xs1 xs2)
.
Proof.
  constructor; intros.
  unfold kleene_star_step_offset.
  apply powerset_union_mono.
  - apply powerset_multiplication_mono; auto.
    apply partial_order_refl.
  - apply partial_order_refl.
Qed.

Program Definition monoid_to_kleene_algebra
  {X: Type}
  `{Finite X}
  (M: monoid X)
:
  kleene_algebra (X -> bool)
:= {|
  kleene_monoid := monoid_powerset M;
  kleene_zero x := false;
  kleene_plus := powerset_union;
  kleene_star xs := mono_fixpoint (kleene_star_step M xs);
|}.
Next Obligation.
  extensionality x'.
  unfold powerset_union.
  btauto.
Qed.
Next Obligation.
  extensionality x'.
  unfold powerset_union.
  btauto.
Qed.
Next Obligation.
  extensionality x'.
  unfold powerset_union.
  btauto.
Qed.
Next Obligation.
  apply powerset_union_commute.
Qed.
Next Obligation.
  extensionality x'.
  unfold powerset_multiplication.
  apply disj_false; intros.
  apply in_map_iff in H1.
  destruct H1 as [(x1, x2') [? ?]]; subst.
  btauto.
Qed.
Next Obligation.
  extensionality x'.
  unfold powerset_multiplication.
  apply disj_false; intros.
  apply in_map_iff in H1.
  destruct H1 as [(x1, x2') [? ?]]; subst.
  btauto.
Qed.
Next Obligation.
  apply powerset_union_multiply_distribute_left.
Qed.
Next Obligation.
  apply powerset_union_multiply_distribute_right.
Qed.
Next Obligation.
  transitivity (kleene_star_step M x (mono_fixpoint (kleene_star_step M x))).
  - unfold kleene_star_step.
    now rewrite powerset_union_commute.
  - apply mono_fixpoint_fixpoint.
    apply kleene_star_step_mono.
Qed.
Next Obligation.
  apply powerset_union_order.
  apply powerset_union_order in H1.
  rewrite <- kleene_star_step_offset_fixpoint.
  apply mono_fixpoint_least.
  - apply kleene_star_step_offset_mono.
  - now unfold kleene_star_step_offset.
Qed.

Equations kleene_interp
  {X: Type}
  (K: kleene_algebra X)
  (f: A -> X)
  (t: term)
:
  X
:= {
  kleene_interp K f zero := kleene_zero K;
  kleene_interp K f one := kleene_unit K;
  kleene_interp K f (letter a) := f a;
  kleene_interp K f (t1 + t2) :=
    kleene_plus K (kleene_interp K f t1) (kleene_interp K f t2);
  kleene_interp K f (t1 ;; t2) :=
    kleene_multiply K (kleene_interp K f t1) (kleene_interp K f t2);
  kleene_interp K f (t*) :=
    kleene_star K (kleene_interp K f t)
}.

Lemma kleene_interp_sound
  {X: Type}
  (K: kleene_algebra X)
  (f: A -> X)
  (t1 t2: term)
:
  t1 == t2 ->
  kleene_interp K f t1 = kleene_interp K f t2
.
Proof.
  intros; dependent induction H0;
  autorewrite with kleene_interp in *;
  try congruence; try apply K.
  - now rewrite kleene_plus_assoc.
  - unfold kleene_multiply.
    now rewrite monoid_compose_assoc.
  - unfold kleene_multiply, kleene_unit.
    now rewrite monoid_unit_left.
  - unfold kleene_multiply, kleene_unit.
    now rewrite monoid_unit_right.
  - rewrite kleene_plus_commute.
    now rewrite kleene_star_unroll.
  - now apply kleene_star_fixpoint.
Qed.

Program Definition automaton_monoid
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
:
  monoid (Q -> Q -> bool)
:= {|
  monoid_compose := matrix_product_bool;
  monoid_unit := finite_eqb;
|}.
Next Obligation.
  apply matrix_product_bool_associative.
Qed.
Next Obligation.
  apply matrix_product_bool_unit_right.
Qed.
Next Obligation.
  apply matrix_product_bool_unit_left.
Qed.

Definition automaton_kleene_algebra
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
:
  kleene_algebra ((Q -> Q -> bool) -> bool)
:=
  monoid_to_kleene_algebra (automaton_monoid aut)
.

Definition automaton_kleene_algebra_embed
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (a: A)
:
  (Q -> Q -> bool) -> bool
:=
  finite_eqb (aut_transitions aut a)
.

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

Lemma kleene_interp_witness_construct
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (t: term)
  (m: Q -> Q -> bool)
:
  kleene_interp (automaton_kleene_algebra aut)
                (automaton_kleene_algebra_embed aut)
                t m = true ->
  exists w,
    automaton_transition_matrix aut w = m /\
    term_matches t w
.
Proof.
  revert aut m; dependent induction t; intros;
  autorewrite with derivative_write in H1;
  autorewrite with kleene_interp in H1;
  simpl in H1.
  - discriminate.
  - unfold kleene_unit in H1; simpl in H1.
    apply finite_eqb_eq in H1; subst.
    exists nil; intuition.
    constructor.
  - unfold automaton_kleene_algebra_embed in H1.
    apply finite_eqb_eq in H1; subst.
    exists (a :: nil).
    autorewrite with automaton_transition_matrix.
    rewrite matrix_product_bool_unit_right; intuition.
    constructor.
  - apply powerset_union_characterise in H1; destruct H1.
    + apply IHt1 in H1.
      destruct H1 as [w [? ?]].
      exists w; intuition.
      now constructor.
    + apply IHt2 in H1.
      destruct H1 as [w [? ?]].
      exists w; intuition.
      now constructor.
  - unfold kleene_multiply in H1; simpl in H1.
    apply powerset_multiplication_characterise in H1.
    destruct H1 as [m1 [m2 [? [? ?]]]]; subst.
    apply IHt1 in H1; destruct H1 as [w1 [? ?]]; subst.
    apply IHt2 in H2; destruct H2 as [w2 [? ?]]; subst.
    exists (w1 ++ w2); simpl.
    rewrite automaton_transition_matrix_app; intuition.
    now constructor.
  - unfold mono_fixpoint in H1; revert H1.
    match goal with
    | |- context [ length ?l ] => generalize (length l)
    end.
    intros n; revert m.
    induction n; simpl; intros.
    + discriminate.
    + unfold kleene_star_step in H1 at 1.
      apply powerset_union_characterise in H1.
      simpl in H1; destruct H1.
      * apply powerset_multiplication_characterise in H1.
        destruct H1 as [m1 [m2 [? [? ?]]]].
        apply IHn in H2; destruct H2 as [w2 [? ?]]; subst.
        apply IHt in H1; destruct H1 as [w1 [? ?]]; subst.
        exists (w1 ++ w2).
        rewrite automaton_transition_matrix_app.
        intuition (now constructor).
      * exists nil.
        apply finite_eqb_eq in H1; subst.
        intuition constructor.
Qed.

Lemma kleene_interp_witness_apply
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (t: term)
  (w: list A)
:
  term_matches t w ->
  kleene_interp (automaton_kleene_algebra aut)
                (automaton_kleene_algebra_embed aut)
                t
                (automaton_transition_matrix aut w)
    = true
.
Proof.
  intros; revert aut.
  dependent induction H1; intros;
  autorewrite with kleene_interp;
  autorewrite with automaton_transition_matrix;
  simpl.
  - unfold kleene_unit; simpl.
    now apply finite_eqb_eq.
  - unfold automaton_kleene_algebra_embed.
    apply finite_eqb_eq.
    now rewrite matrix_product_bool_unit_right.
  - apply powerset_union_characterise.
    rewrite IHterm_matches; intuition btauto.
  - apply powerset_union_characterise.
    rewrite IHterm_matches; intuition btauto.
  - unfold kleene_multiply; simpl.
    apply powerset_multiplication_characterise.
    exists (automaton_transition_matrix aut w1).
    exists (automaton_transition_matrix aut w2).
    intuition; simpl.
    now rewrite automaton_transition_matrix_app.
  - rewrite <- mono_fixpoint_fixpoint.
    + unfold kleene_star_step.
      apply powerset_union_characterise; right.
      now apply finite_eqb_eq.
    + apply kleene_star_step_mono.
  - rewrite <- mono_fixpoint_fixpoint.
    + unfold kleene_star_step at 1.
      apply powerset_union_characterise; left.
      apply powerset_multiplication_characterise.
      exists (automaton_transition_matrix aut w1).
      exists (automaton_transition_matrix aut w2).
      intuition.
      * specialize (IHterm_matches2 aut).
        now autorewrite with kleene_interp in IHterm_matches2.
      * now rewrite automaton_transition_matrix_app.
    + apply kleene_star_step_mono.
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

Definition kleene_interp_recombine
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (q: Q)
:
  term
:=
  sum (
     map (automaton_relation_solution aut)
         (filter (kleene_interp (automaton_kleene_algebra aut)
                                (automaton_kleene_algebra_embed aut)
                                (compute_automaton_solution aut q))
                 finite_enum)
  )
.

Lemma kleene_interp_recombine_characterise
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (q: Q)
:
   kleene_interp_recombine aut q == compute_automaton_solution aut q
.
Proof.
  unfold kleene_interp_recombine.
  rewrite <- (automaton_sum_accepting_matrices_characterise aut q) at 2.
  unfold automaton_sum_accepting_matrices.
  apply term_lequiv_squeeze.
  - apply sum_lequiv_all; intros.
    apply in_map_iff in H1.
    destruct H1 as [m [? ?]]; subst.
    apply filter_In in H2.
    destruct H2 as [_ ?].
    apply kleene_interp_witness_construct in H1.
    destruct H1 as [w [? ?]].
    apply sum_lequiv_member.
    apply in_map_iff.
    exists m; subst; intuition.
    unfold automaton_accepting_matrices.
    apply filter_In.
    split; [ apply finite_cover |].
    apply automaton_accepts_transition_matrix.
    rewrite <- automaton_least_solution_match.
    + apply H2.
    + rewrite automaton_least_solution_invariant.
      apply compute_automaton_solution_least_solution.
  - apply sum_lequiv_all; intros.
    apply in_map_iff in H1.
    destruct H1 as [? [? ?]]; subst.
    destruct (term_empty (automaton_relation_solution aut x)) eqn:?.
    + apply term_empty_zero in Heqb.
      rewrite Heqb.
      apply term_lequiv_zero.
    + apply term_empty_dec in Heqb.
      destruct Heqb as [w ?].
      * rewrite term_equiv_sound
          with (t2 := automaton_relation_solution' aut x)
          in H1 by (apply automaton_relation_solution_characterise).
        unfold automaton_relation_solution' in H1.
        apply automaton_transition_monad_solution in H1.
        rewrite matrix_product_bool_unit_left in H1; subst.
        apply sum_lequiv_member.
        apply in_map_iff.
        eexists; intuition.
        apply filter_In.
        split; [apply finite_cover |].
        apply kleene_interp_witness_apply.
        unfold automaton_accepting_matrices in H2.
        apply filter_In in H2.
        destruct H2 as [_ ?].
        rewrite automaton_least_solution_match.
        -- apply automaton_accepts_transition_matrix, H1.
        -- rewrite automaton_least_solution_invariant.
           apply compute_automaton_solution_least_solution;
           apply automaton_relation_solution_characterise.
Qed.

Program Instance finite_coproduct
  (X Y: Type)
  `{Finite X}
  `{Finite Y}
:
  Finite (X + Y)
:= {|
  finite_enum := map inl finite_enum ++ map inr finite_enum
|}.
Next Obligation.
  destruct x1, x2.
  - destruct (finite_dec x x0).
    + left; congruence.
    + right; congruence.
  - now right.
  - now right.
  - destruct (finite_dec y y0).
    + left; congruence.
    + right; congruence.
Qed.
Next Obligation.
  apply in_app_iff.
  repeat rewrite in_map_iff.
  destruct x.
  - left; exists x; intuition.
  - right; exists y; intuition.
Qed.
Next Obligation.
  apply NoDup_app.
  - apply NoDup_map.
    + intros; now inversion H2.
    + apply finite_nodup.
  - apply NoDup_map.
    + intros; now inversion H2.
    + apply finite_nodup.
  - intros; intro.
    rewrite in_map_iff in H2, H3.
    destruct H2 as [x' [? _]].
    destruct H3 as [x'' [? _]].
    now subst.
  - intros; intro.
    rewrite in_map_iff in H2, H3.
    destruct H2 as [x' [? _]].
    destruct H3 as [x'' [? _]].
    now subst.
Qed.

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
  compute_automaton_solution (automaton_coproduct aut1 aut2) ∘ inl
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
  compute_automaton_solution (automaton_coproduct aut1 aut2) ∘ inr
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

Program Instance finite_unit : Finite unit := {|
  finite_enum := tt :: nil;
|}.
Next Obligation.
  destruct x1, x2; now left.
Qed.
Next Obligation.
  destruct x; now left.
Qed.
Next Obligation.
  constructor; intuition constructor.
Qed.

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
  compute_automaton_solution (automaton_coalesce aut targets) ∘ inl
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
        apply finite_cover.
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

Definition term_interp_finite_equiv
  (t1 t2: term)
:=
  forall {X: Type} `{Finite X} (k: kleene_algebra X) (f: A -> X),
    kleene_interp k f t1 = kleene_interp k f t2
.

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
  now apply H0.
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

Lemma term_normal_form_left_pre
  (t1 t2: term)
:
  let aut1 := automaton_coalesce (automaton_antimirov t1) initial_b in
  let aut2 := automaton_coalesce (automaton_antimirov t2) initial_b in
  let aut := automaton_coproduct aut1 aut2 in
  t1 == compute_automaton_solution aut (inl (inr tt))
.
Proof.
  intros.
  rewrite term_roundtrip_invariant at 1.
  unfold term_roundtrip.
  unfold antimirov_solution.
  transitivity (compute_automaton_solution aut1 (inr tt)).
  - subst aut1.
    rewrite (automaton_coalesce_solution _ initial_b (inr tt)).
    unfold automaton_coalesce_import_solution.
    apply sum_equiv_containment; intros t ?.
    + apply in_map_iff in H0.
      destruct H0 as [? [? ?]]; subst.
      apply initial_list in H1.
      apply in_map_iff.
      exists x.
      split; auto.
      apply filter_In.
      split; [apply finite_cover|].
      now apply initial_dec.
    + apply in_map_iff in H0.
      destruct H0 as [? [? ?]]; subst.
      apply filter_In in H1.
      destruct H1 as [_ ?].
      apply in_map_iff.
      exists x.
      split; auto.
      apply initial_list.
      now apply initial_dec.
  - now rewrite (automaton_coproduct_solution_left aut1 aut2 (inr tt)).
Qed.

Lemma term_normal_form_left
  (t1 t2: term)
:
  let aut1 := automaton_antimirov t1 in
  let aut2 := automaton_antimirov t2 in
  let aut := automaton_coproduct (automaton_coalesce aut1 initial_b)
                                 (automaton_coalesce aut2 initial_b) in
  let rels := kleene_interp (automaton_kleene_algebra aut)
                            (automaton_kleene_algebra_embed aut) t1 in
  t1 == sum (map (automaton_relation_solution aut)
                 (filter rels finite_enum))
.
Proof.
  intros.
  rewrite term_normal_form_left_pre at 1.
  rewrite <- kleene_interp_recombine_characterise.
  unfold kleene_interp_recombine.
  erewrite kleene_interp_sound.
  - now subst aut1 aut2 aut rels.
  - now rewrite <- term_normal_form_left_pre.
Qed.

Lemma term_normal_form_right_pre
  (t1 t2: term)
:
  let aut1 := automaton_coalesce (automaton_antimirov t1) initial_b in
  let aut2 := automaton_coalesce (automaton_antimirov t2) initial_b in
  let aut := automaton_coproduct aut1 aut2 in
  t2 == compute_automaton_solution aut (inr (inr tt))
.
Proof.
  intros.
  rewrite term_roundtrip_invariant at 1.
  unfold term_roundtrip.
  unfold antimirov_solution.
  transitivity (compute_automaton_solution aut2 (inr tt)).
  - subst aut2.
    rewrite (automaton_coalesce_solution _ initial_b (inr tt)).
    unfold automaton_coalesce_import_solution.
    apply sum_equiv_containment; intros t ?.
    + apply in_map_iff in H0.
      destruct H0 as [? [? ?]]; subst.
      apply initial_list in H1.
      apply in_map_iff.
      exists x.
      split; auto.
      apply filter_In.
      split; [apply finite_cover|].
      now apply initial_dec.
    + apply in_map_iff in H0.
      destruct H0 as [? [? ?]]; subst.
      apply filter_In in H1.
      destruct H1 as [_ ?].
      apply in_map_iff.
      exists x.
      split; auto.
      apply initial_list.
      now apply initial_dec.
  - now rewrite (automaton_coproduct_solution_right aut1 aut2 (inr tt)).
Qed.

Lemma term_normal_form_right
  (t1 t2: term)
:
  let aut1 := automaton_antimirov t1 in
  let aut2 := automaton_antimirov t2 in
  let aut := automaton_coproduct (automaton_coalesce aut1 initial_b)
                                 (automaton_coalesce aut2 initial_b) in
  let rels := kleene_interp (automaton_kleene_algebra aut)
                            (automaton_kleene_algebra_embed aut) t2 in
  t2 == sum (map (automaton_relation_solution aut)
                 (filter rels finite_enum))
.
Proof.
  intros.
  rewrite term_normal_form_right_pre at 1.
  rewrite <- kleene_interp_recombine_characterise.
  unfold kleene_interp_recombine.
  erewrite kleene_interp_sound.
  - now subst aut1 aut2 aut rels.
  - now rewrite <- term_normal_form_right_pre.
Qed.

Lemma term_interp_finite_equiv_implies_equiv
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

Lemma term_equiv_complete
  (t1 t2: term)
:
  (forall w, term_matches t1 w <-> term_matches t2 w) ->
  t1 == t2
.
Proof.
  intros.
  rewrite term_normal_form_left with (t2 := t2) at 1; symmetry.
  rewrite term_normal_form_right with (t1 := t1) at 1; symmetry.
  erewrite filter_ext.
  - reflexivity.
  - intros m.
    apply ZMicromega.eq_true_iff_eq.
    split; intros.
    + apply kleene_interp_witness_construct in H1.
      destruct H1 as [w [? ?]]; subst.
      apply kleene_interp_witness_apply.
      intuition.
    + apply kleene_interp_witness_construct in H1.
      destruct H1 as [w [? ?]]; subst.
      apply kleene_interp_witness_apply.
      intuition.
Qed.

Lemma term_equiv_free
  (t1 t2: term)
:
  (forall w, term_matches t1 w <-> term_matches t2 w) <->
  t1 == t2
.
Proof.
  split; intros.
  - now apply term_equiv_complete.
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
