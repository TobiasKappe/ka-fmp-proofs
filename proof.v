From Equations Require Import Equations.
Require Import Coq.Program.Equality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Local Open Scope program_scope.

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

Equations position_subset_glue
  {n: nat}
  (b: bool)
  (f: position n -> bool)
  (p: position (S n))
:
  bool
:= {
  position_subset_glue b _ PHere := b;
  position_subset_glue _ f (PThere p) := f p;
}.

Definition empty_function {X: Type} (p: position 0): X :=
  match p with
  end
.

Equations position_subsets (n: nat): list (position n -> bool) := {
  position_subsets 0 := empty_function :: nil;
  position_subsets (S n) :=
    let subsets_n := position_subsets n in
    map (position_subset_glue false) subsets_n ++
    map (position_subset_glue true) subsets_n;
}.

Lemma position_subsets_full (n: nat) (f: position n -> bool):
  In f (position_subsets n)
.
Proof.
  induction n;
  autorewrite with position_subsets.
  - left.
    extensionality p.
    dependent destruction p.
  - simpl.
    apply in_app_iff.
    repeat rewrite in_map_iff.
    destruct (f PHere) eqn:?.
    + right.
      exists (fun p => f (PThere p)).
      split.
      * extensionality p.
        dependent destruction p;
        now autorewrite with position_subset_glue.
      * apply IHn.
    + left.
      exists (fun p => f (PThere p)).
      split.
      * extensionality p.
        dependent destruction p;
        now autorewrite with position_subset_glue.
      * apply IHn.
Qed.

Lemma position_subsets_nodup (n: nat):
  NoDup (position_subsets n)
.
Proof.
  induction n;
  autorewrite with position_subsets.
  - constructor.
    + now intro.
    + constructor.
  - simpl.
    apply NoDup_app.
    + apply NoDup_map; auto; intros.
      extensionality p.
      rewrite <- position_subset_glue_equation_2 with (f := x) (b := false) at 1.
      rewrite <- position_subset_glue_equation_2 with (f := y) (b := false).
      now rewrite H0.
    + apply NoDup_map; auto; intros.
      extensionality p.
      rewrite <- position_subset_glue_equation_2 with (f := x) (b := true) at 1.
      rewrite <- position_subset_glue_equation_2 with (f := y) (b := true).
      now rewrite H0.
    + intros; intro.
      rewrite in_map_iff in H0, H1.
      destruct H0 as [x0 [? ?]], H1 as [x1 [? ?]]; subst.
      apply Bool.diff_true_false.
      rewrite <- position_subset_glue_equation_1 with (f := x1) at 1.
      rewrite <- position_subset_glue_equation_1 with (f := x0).
      now rewrite H1.
    + intros; intro.
      rewrite in_map_iff in H0, H1.
      destruct H0 as [x0 [? ?]], H1 as [x1 [? ?]]; subst.
      apply Bool.diff_true_false.
      rewrite <- position_subset_glue_equation_1 with (f := x0) at 1.
      rewrite <- position_subset_glue_equation_1 with (f := x1).
      now rewrite H1.
Qed.

Definition finite_subsets {X: Type} `{Finite X}: list (X -> bool) :=
  map (fun f x => f (list_index x)) (position_subsets (length (finite_enum)))
.

Lemma conj_true (l: list bool):
  conj l = true <-> (forall x, In x l -> x = true)
.
Proof.
  split; intros.
  - induction l;
    autorewrite with conj in H0.
    + destruct H1.
    + apply andb_prop in H0.
      destruct H0, H1.
      * now subst.
      * now apply IHl.
  - induction l;
    autorewrite with conj;
    auto.
    apply andb_true_intro.
    split.
    + apply H0.
      now left.
    + apply IHl.
      intros.
      apply H0.
      now right.
Qed.

Lemma function_instantiation {X Y: Type} (f g: X -> Y) (x: X):
  f = g -> f x = g x
.
Proof.
  intros; now subst.
Qed.

Equations position_subsets_eqb {n: nat} (f g: position n -> bool) : bool := {
  @position_subsets_eqb 0 _ _ := true;
  @position_subsets_eqb (S n) f g :=
    Bool.eqb (f PHere) (g PHere) &&
    position_subsets_eqb (f ∘ PThere) (g ∘ PThere);
}.

Lemma position_subsets_eqb_correct (n: nat) (f g: position n -> bool):
  position_subsets_eqb f g = true <-> f = g
.
Proof.
  induction n;
  autorewrite with position_subsets_eqb.
  - split; intros; auto.
    extensionality p.
    dependent destruction p.
  - rewrite Bool.andb_true_iff.
    split; intros.
    + destruct H0.
      extensionality p.
      dependent destruction p.
      * now apply Bool.eqb_prop.
      * replace (f (PThere p)) with ((f ∘ PThere) p) by reflexivity.
        replace (g (PThere p)) with ((g ∘ PThere) p) by reflexivity.
        apply IHn in H1.
        now rewrite H1.
    + split; intros.
      * rewrite H0.
        apply Bool.eqb_reflx.
      * apply IHn.
        now rewrite H0.
Qed.

Program Instance finite_subsets_finite
  (X: Type)
  `{Finite X}
:
  Finite (X -> bool)
:= {|
  finite_enum := finite_subsets;
|}.
Next Obligation.
  destruct (position_subsets_eqb (x1 ∘ list_lookup) (x2 ∘ list_lookup)) eqn:?.
  - left.
    rewrite position_subsets_eqb_correct in Heqb.
    extensionality x.
    rewrite <- list_lookup_index with (x := x).
    replace (x1 (list_lookup (list_index x)))
      with ((x1 ∘ list_lookup) (list_index x))
      by reflexivity.
    replace (x2 (list_lookup (list_index x)))
      with ((x2 ∘ list_lookup) (list_index x))
      by reflexivity.
    now rewrite Heqb.
  - right.
    rewrite <- Bool.not_true_iff_false in Heqb.
    contradict Heqb.
    apply position_subsets_eqb_correct.
    now subst.
Defined.
Next Obligation.
  unfold finite_subsets.
  apply in_map_iff.
  exists (fun p => x (list_lookup p)); split.
  - extensionality x'.
    now rewrite list_lookup_index.
  - apply position_subsets_full.
Qed.
Next Obligation.
  unfold finite_subsets.
  apply NoDup_map.
  - intros.
    extensionality p.
    rewrite <- list_index_lookup with (p := p).
    replace (x (list_index (list_lookup p)))
      with ((x ∘ list_index) (list_lookup p))
      by reflexivity.
    replace (y (list_index (list_lookup p)))
      with ((y ∘ list_index) (list_lookup p))
      by reflexivity.
    apply function_instantiation.
    apply H1.
  - apply position_subsets_nodup.
Qed.

(* From Leapfrog *)
Lemma NoDup_prod:
  forall A B (l1: list A) (l2: list B),
    NoDup l1 ->
    NoDup l2 ->
    NoDup (list_prod l1 l2).
Proof.
  induction l1; intros.
  - constructor.
  - simpl.
    apply NoDup_app.
    + apply NoDup_map; auto.
      intros.
      now inversion H2.
    + apply IHl1; auto.
      now inversion H0.
    + intros.
      rewrite in_map_iff in H2.
      destruct x.
      destruct H2 as [? [? ?]].
      inversion H2; subst.
      inversion H0.
      contradict H6.
      apply in_prod_iff in H6.
      intuition.
    + intros.
      inversion_clear H0.
      contradict H3.
      apply in_map_iff in H3.
      destruct H3 as [? [? ?]].
      subst.
      apply in_prod_iff in H2.
      intuition.
Qed.

Program Instance product_finite
  (X Y: Type)
  `{Finite X}
  `{Finite Y}
:
  Finite (prod X Y)
:= {|
  finite_enum := list_prod finite_enum finite_enum;
|}.
Next Obligation.
  destruct (finite_dec x0 x).
  - destruct (finite_dec y0 y).
    + subst.
      now left.
    + right.
      contradict n.
      now inversion n.
  - right.
    contradict n.
    now inversion n.
Defined.
Next Obligation.
  apply in_prod;
  apply finite_cover.
Qed.
Next Obligation.
  apply NoDup_prod;
  apply finite_nodup.
Qed.

Program Instance matrix_finite
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
  apply in_map_iff.
  exists (uncurry x).
  intuition.
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
      now rewrite H2.
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

Definition automaton_transition_monad
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (final: Q -> Q -> bool)
:
  automaton (Q -> Q -> bool)
:= {|
  aut_transitions a m1 m2 :=
    finite_eqb (matrix_product_bool m1 (aut_transitions aut a)) m2;
  aut_accept m :=
    finite_eqb m final;
|}.

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
  - dependent induction H0.
    + now exists nil.
    + specialize (IHterm_matches2 t eq_refl).
      destruct IHterm_matches2 as [l [? ?]]; subst.
      exists (w1 :: l).
      intuition.
      destruct H0.
      * now subst.
      * now apply H1.
  - destruct H0 as [l [? ?]]; subst.
    induction l; simpl.
    + apply MatchStarBase.
    + apply MatchStarStep.
      * apply H1.
        now left.
      * apply IHl; intros.
        apply H1.
        now right.
Qed.

Lemma term_equiv_sound (t1 t2: term) (w: list A):
  t1 == t2 ->
  term_matches t1 w <-> term_matches t2 w
.
Proof.
  intros.
  revert w; dependent induction H0; intros.
  - reflexivity.
  - now symmetry.
  - now transitivity (term_matches t2 w).
  - split; intros.
    + dependent destruction H0.
      * apply MatchPlusLeft; intuition.
      * apply MatchPlusRight; intuition.
    + dependent destruction H0.
      * apply MatchPlusLeft; intuition.
      * apply MatchPlusRight; intuition.
  - split; intros.
    + dependent destruction H0.
      apply MatchTimes; intuition.
    + dependent destruction H0.
      apply MatchTimes; intuition.
  - split; intros.
    + dependent induction H1.
      * apply MatchStarBase.
      * apply MatchStarStep; intuition.
    + dependent induction H1.
      * apply MatchStarBase.
      * apply MatchStarStep; intuition.
  - split; intros.
    + now dependent destruction H0.
    + now apply MatchPlusLeft.
  - split; intros.
    + dependent destruction H0.
      * now apply MatchPlusRight.
      * now apply MatchPlusLeft.
    + dependent destruction H0.
      * now apply MatchPlusRight.
      * now apply MatchPlusLeft.
  - split; intros.
    + dependent destruction H0; [| dependent destruction H0].
      * now apply MatchPlusLeft, MatchPlusLeft.
      * now apply MatchPlusLeft, MatchPlusRight.
      * now apply MatchPlusRight.
    + dependent destruction H0; [dependent destruction H0|].
      * now apply MatchPlusLeft.
      * now apply MatchPlusRight, MatchPlusLeft.
      * now apply MatchPlusRight, MatchPlusRight.
  - split; intros.
    + now dependent destruction H0.
    + now apply MatchPlusLeft.
  - split; intros.
    + dependent destruction H0.
      dependent destruction H0_0.
      rewrite app_assoc.
      apply MatchTimes; auto.
      now apply MatchTimes.
    + dependent destruction H0.
      dependent destruction H0_.
      rewrite <- app_assoc.
      apply MatchTimes; auto.
      now apply MatchTimes.
  - split; intros.
    + dependent destruction H0.
      dependent destruction H0_0.
      now rewrite app_nil_r.
    + rewrite <- app_nil_r.
      apply MatchTimes; auto.
      apply MatchOne.
  - split; intros.
    + dependent destruction H0.
      dependent destruction H0_.
      now rewrite app_nil_l.
    + rewrite <- app_nil_l.
      apply MatchTimes; auto.
      apply MatchOne.
  - split; intros.
    + dependent destruction H0.
      dependent destruction H0_0.
    + dependent destruction H0.
  - split; intros.
    + dependent destruction H0.
      dependent destruction H0_.
    + dependent destruction H0.
  - split; intros.
    + dependent destruction H0.
      dependent destruction H0_0.
      * apply MatchPlusLeft.
        now apply MatchTimes.
      * apply MatchPlusRight.
        now apply MatchTimes.
    + dependent destruction H0.
      * dependent destruction H0.
        apply MatchTimes; auto.
        now apply MatchPlusLeft.
      * dependent destruction H0.
        apply MatchTimes; auto.
        now apply MatchPlusRight.
  - split; intros.
    + dependent destruction H0.
      dependent destruction H0_.
      * apply MatchPlusLeft.
        now apply MatchTimes.
      * apply MatchPlusRight.
        now apply MatchTimes.
    + dependent destruction H0.
      * dependent destruction H0.
        apply MatchTimes; auto.
        now apply MatchPlusLeft.
      * dependent destruction H0.
        apply MatchTimes; auto.
        now apply MatchPlusRight.
  - split; intros.
    + dependent destruction H0.
      * now apply MatchPlusRight, MatchOne.
      * now apply MatchPlusLeft, MatchTimes.
    + dependent destruction H0.
      * dependent destruction H0.
        now apply MatchStarStep.
      * dependent destruction H0.
        apply MatchStarBase.
  - split; intros.
    + dependent destruction H1; auto.
      dependent destruction H1.
      apply term_matches_star_split in H1_.
      destruct H1_ as [l [? ?]].
      subst; induction l; simpl.
      * apply IHterm_equiv.
        now apply MatchPlusLeft, MatchPlusRight.
      * apply IHterm_equiv.
        apply MatchPlusLeft, MatchPlusLeft.
        rewrite <- app_assoc.
        apply MatchTimes; intuition.
    + now apply MatchPlusRight.
Qed.

Equations automaton_transition_matrix
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (w: list A)
:
  Q -> Q -> bool
:= {
  automaton_transition_matrix aut nil := finite_eqb;
  automaton_transition_matrix aut (a :: w) :=
    matrix_product_bool (aut_transitions aut a)
                        (automaton_transition_matrix aut w)
}.

Lemma term_matches_sum (l: list term) (w: list A):
  term_matches (sum l) w <->
  exists (t: term),
    In t l /\ term_matches t w
.
Proof.
  induction l; autorewrite with sum.
  - split; intros.
    + dependent destruction H0.
    + now destruct H0 as [t [? ?]].
  - split; intros.
    + dependent destruction H0.
      * exists a; intuition.
      * apply IHl in H0.
        destruct H0 as [t [? ?]].
        exists t; intuition.
    + destruct H0 as [t [[? | ?] ?]].
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
  dependent destruction H0.
  dependent destruction H0_.
  rewrite <- app_comm_cons in x.
  inversion x.
Qed.

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
  rewrite in_map_iff.
  setoid_rewrite Bool.andb_true_iff.
  split; intros.
  - destruct H1 as [q3 [? ?]].
    now exists q3.
  - destruct H1 as [q3 [? ?]].
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
    unfold finite_eqb in H1.
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
    unfold finite_eqb in H2.
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
    apply matrix_product_characterise in H1.
    destruct H1 as [q4 [? ?]].
    apply matrix_product_characterise.
    exists q4; intuition.
    apply matrix_product_characterise.
    exists q3; intuition.
  - apply Bool.not_true_iff_false.
    apply Bool.not_true_iff_false in Heqb.
    contradict Heqb.
    apply matrix_product_characterise in Heqb.
    destruct Heqb as [q3 [? ?]].
    apply matrix_product_characterise in H2.
    destruct H2 as [q4 [? ?]].
    apply matrix_product_characterise.
    exists q4; intuition.
    apply matrix_product_characterise.
    exists q3; intuition.
Qed.

Inductive automaton_accepts
  {Q: Type}
  (aut: automaton Q)
:
  Q -> list A -> Prop
:=
| AcceptsEmpty:
  forall (q: Q),
  aut_accept aut q = true ->
  automaton_accepts aut q nil
| AcceptsStep:
  forall (q q': Q) (a: A) (w: list A),
  aut_transitions aut a q q' = true ->
  automaton_accepts aut q' w ->
  automaton_accepts aut q (a :: w)
.

Lemma term_matches_automaton_perturb_nil
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (sol: vector Q)
  (q: Q)
:
  term_matches (automaton_perturb aut 1 sol q) nil <->
  aut_accept aut q = true
.
Proof.
  split; intros.
  - unfold automaton_perturb in H1.
    dependent destruction H1.
    + destruct (aut_accept aut q); auto.
      dependent destruction H1.
    + apply term_matches_sum in H1.
      destruct H1 as [t [? ?]].
      apply in_map_iff in H1.
      destruct H1 as [q' [? ?]]; subst.
      apply term_matches_sum in H2.
      destruct H2 as [t [? ?]].
      apply in_map_iff in H1.
      destruct H1 as [a [? ?]]; subst.
      destruct (aut_transitions aut a q q');
      dependent destruction H2.
      apply app_eq_nil in x.
      destruct x; subst.
      dependent destruction H2_.
  - unfold automaton_perturb.
    apply MatchPlusLeft.
    rewrite H1.
    constructor.
Qed.

Lemma term_matches_automaton_perturb_cons
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (sol: vector Q)
  (q: Q)
  (a: A)
  (w: list A)
:
  term_matches (automaton_perturb aut 1 sol q) (a :: w) <->
  exists (q': Q),
    aut_transitions aut a q q' = true /\
    term_matches (sol q') w
.
Proof.
  split; intros.
  - unfold automaton_perturb in H1.
    dependent destruction H1.
    + destruct (aut_accept aut q);
      dependent destruction H1.
    + apply term_matches_sum in H1.
      destruct H1 as [t [? ?]].
      apply in_map_iff in H1.
      destruct H1 as [q' [? ?]]; subst.
      exists q'.
      apply term_matches_sum in H2.
      destruct H2 as [t [? ?]].
      apply in_map_iff in H1.
      destruct H1 as [a' [? ?]]; subst.
      destruct (aut_transitions aut a' q q') eqn:?;
      dependent destruction H2.
      dependent destruction H2_.
      rewrite <- app_comm_cons in x.
      rewrite app_nil_l in x.
      inversion x; subst.
      intuition.
  - destruct H1 as [q' [? ?]].
    unfold automaton_perturb.
    apply MatchPlusRight.
    apply term_matches_sum.
    eexists; rewrite in_map_iff.
    repeat split.
    + exists q'; split; auto.
      apply finite_cover.
    + apply term_matches_sum.
      eexists; split.
      * apply in_map_iff.
        exists a; rewrite H1.
        intuition (apply finite_cover).
      * replace (a :: w) with ((a :: nil) ++ w) by reflexivity.
        apply MatchTimes; auto.
        constructor.
Qed.

Lemma automaton_least_solution_match
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (sol: vector Q)
  (q: Q)
  (w: list A)
:
  automaton_least_solution aut 1 sol ->
  term_matches (sol q) w <->
  automaton_accepts aut q w
.
Proof.
  intro; revert q; induction w; intros;
  rewrite term_equiv_sound
    with (t2 := automaton_perturb aut 1 sol q)
    by (now apply automaton_solution_least_converse).
  - rewrite term_matches_automaton_perturb_nil.
    split; intros.
    + now constructor.
    + now dependent destruction H2.
  - rewrite term_matches_automaton_perturb_cons.
    split; intros.
    + destruct H2 as [q' [? ?]].
      apply AcceptsStep with (q' := q'); intuition.
    + dependent destruction H2.
      exists q'; split; auto.
      now apply IHw.
Qed.

Lemma finite_eqb_eq (X: Type) `{Finite X} (x1 x2: X):
  finite_eqb x1 x2 = true <-> x1 = x2
.
Proof.
  unfold finite_eqb.
  now destruct (finite_dec _ _).
Qed.

Lemma automaton_transition_monad_accepts
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (initial final: Q -> Q -> bool)
  (w: list A)
:
  automaton_accepts (automaton_transition_monad aut final) initial w <->
  matrix_product_bool initial (automaton_transition_matrix aut w) = final
.
Proof.
  revert initial; induction w; intros initial;
  autorewrite with automaton_transition_matrix.
  - rewrite matrix_product_bool_unit_right.
    split; intros.
    + dependent destruction H1.
      simpl in H1.
      now rewrite finite_eqb_eq in H1.
    + constructor.
      simpl; subst.
      now apply finite_eqb_eq.
  - split; intros.
    + dependent destruction H1.
      simpl in H1.
      apply finite_eqb_eq in H1.
      subst.
      rewrite <- matrix_product_bool_associative.
      now apply IHw.
    + apply AcceptsStep
        with (q' := matrix_product_bool initial (aut_transitions aut a)).
      * now apply finite_eqb_eq.
      * apply IHw.
        now rewrite matrix_product_bool_associative.
Qed.

Lemma automaton_transition_monad_solution
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (initial final: Q -> Q -> bool)
  (w: list A)
:
  let aut' := automaton_transition_monad aut final in
  let sol' := compute_automaton_solution aut' in
  term_matches (sol' initial) w <->
  matrix_product_bool initial (automaton_transition_matrix aut w) = final
.
Proof.
  simpl.
  rewrite automaton_least_solution_match
    with (aut := automaton_transition_monad aut final)
    by (apply automaton_least_solution_invariant;
        apply compute_automaton_solution_least_solution).
  apply automaton_transition_monad_accepts.
Qed.

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

Require Import Btauto.

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

Open Scope bool_scope.

Definition automaton_lift
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
:
  automaton (prod Q Q)
:= {|
  aut_accept '(q1, q2) := finite_eqb q1 q2;
  aut_transitions a '(q1, q2) '(q1', q2') :=
    aut_transitions aut a q1 q1' && finite_eqb q2 q2'
|}.

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

Lemma automaton_transition_monad_lift_shift_solution
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (scale: term)
  (sol: vector (prod (Q -> Q -> bool) (Q -> Q -> bool)))
  (h: Q -> Q -> bool)
:
  automaton_solution (automaton_lift (automaton_transition_monad aut finite_eqb)) scale sol ->
  automaton_solution (automaton_lift (automaton_transition_monad aut finite_eqb)) scale (vector_shift_both sol h)
.
Proof.
  split; simpl; intros.
  - destruct q1, q2.
    apply Bool.andb_true_iff in H2; destruct H2.
    apply finite_eqb_eq in H2, H3; subst.
    unfold vector_shift_both; simpl.
    apply H1; simpl.
    apply Bool.andb_true_iff.
    repeat rewrite finite_eqb_eq.
    rewrite matrix_product_bool_associative.
    intuition.
  - destruct q.
    apply finite_eqb_eq in H2; subst.
    apply H1; simpl.
    now apply finite_eqb_eq.
Qed.

Definition automaton_relation_solution_path
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
:=
  compute_automaton_solution (automaton_lift (automaton_transition_monad aut finite_eqb))
.

Definition automaton_relation_solution
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (m: Q -> Q -> bool)
:=
  automaton_relation_solution_path aut (finite_eqb, m)
.

Lemma automaton_relation_solution_path_shift
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (h: Q -> Q -> bool)
:
  automaton_relation_solution_path aut <==
  vector_shift_both (automaton_relation_solution_path aut) h
.
Proof.
  intro.
  unfold automaton_relation_solution_path.
  rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
  apply compute_automaton_solution_least_solution.
  apply automaton_transition_monad_lift_shift_solution.
  apply automaton_least_solution_invariant.
  apply compute_automaton_solution_least_solution.
Qed.

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

Lemma automaton_relation_solution_path_shift_single
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (h: Q -> Q -> bool)
:
  automaton_relation_solution_path aut ;;;
  automaton_relation_solution aut h <==
  vector_shift_single (automaton_relation_solution_path aut) h
.
Proof.
  unfold automaton_relation_solution_path, automaton_relation_solution.
  apply compute_automaton_solution_least_solution.
  split; intros.
  - unfold vector_shift_single.
    destruct q1, q2; simpl in *.
    apply Bool.andb_true_iff in H1; destruct H1.
    rewrite finite_eqb_eq in H1, H2; subst.
    pose proof (vector_scale_right_unit (A := A) (Q := (prod (Q -> Q -> bool) (Q -> Q -> bool)))).
    specialize (H1 (compute_automaton_solution (automaton_lift (automaton_transition_monad aut finite_eqb)))).
    rewrite <- (H1 (matrix_product_bool b (aut_transitions aut a), matrix_product_bool b2 h)).
    rewrite <- (H1 (b, matrix_product_bool b2 h)).
    apply compute_automaton_solution_least_solution; simpl.
    apply Bool.andb_true_iff.
    now repeat rewrite finite_eqb_eq.
  - unfold vector_shift_single.
    destruct q; simpl in *.
    apply finite_eqb_eq in H1; subst.
    replace b0
      with (matrix_product_bool b0 finite_eqb) at 1
      by (apply matrix_product_bool_unit_right).
    replace b0
      with (matrix_product_bool b0 finite_eqb) at 3
      by (apply matrix_product_bool_unit_right).
    eapply term_lequiv_trans.
    apply automaton_relation_solution_path_shift.
    unfold vector_shift_both; simpl.
    repeat rewrite matrix_product_bool_unit_right.
    unfold automaton_relation_solution_path.
    apply term_lequiv_refl.
Qed.

Lemma automaton_relation_solution_merge
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (f g: Q -> Q -> bool)
:
  automaton_relation_solution aut f ;;
  automaton_relation_solution aut g <=
  automaton_relation_solution aut (matrix_product_bool f g)
.
Proof.
  unfold automaton_relation_solution at 1.
  apply automaton_relation_solution_path_shift_single.
Qed.

Definition automaton_accepting_matrices
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (q: Q)
:
  list (Q -> Q -> bool)
:=
  filter (fun m => vector_inner_product_bool (m q) (aut_accept aut))
         finite_enum
.

Definition automaton_sum_accepting_matrices
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (q: Q)
:
  term
:=
  sum (map (automaton_relation_solution aut)
           (automaton_accepting_matrices aut q))
.

Lemma automaton_relation_solution_step
  {Q: Type}
  `{Finite Q}
  (a: A)
  (aut: automaton Q)
:
  $ a <= automaton_relation_solution aut (automaton_transition_matrix aut (a :: nil))
.
Proof.
  unfold automaton_relation_solution.
  unfold automaton_relation_solution_path.
  apply term_lequiv_trans with (t2 := $a ;; compute_automaton_solution
  (automaton_lift (automaton_transition_monad aut finite_eqb))
  (automaton_transition_matrix aut (a :: nil), automaton_transition_matrix aut (a :: nil))).
  rewrite <- ETimesUnitRight with (t := $a) at 1.
  apply times_mor_mono.
  apply term_lequiv_refl.
  unfold term_lequiv.
  rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
  apply compute_automaton_solution_least_solution.
  simpl.
  now apply finite_eqb_eq.
  rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
  rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ (finite_eqb, _)).
  apply compute_automaton_solution_least_solution.
  simpl.
  apply Bool.andb_true_iff.
  repeat rewrite finite_eqb_eq.
  autorewrite with automaton_transition_matrix.
  rewrite matrix_product_bool_unit_left.
  rewrite matrix_product_bool_unit_right.
  intuition.
Qed.

Lemma automaton_sum_accepting_matrices_lower
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
:
  compute_automaton_solution aut <== automaton_sum_accepting_matrices aut
.
Proof.
  intro.
  rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q).
  apply compute_automaton_solution_least_solution.
  split; intros.
  - unfold automaton_sum_accepting_matrices.
    rewrite <- sum_distribute_left.
    apply sum_lequiv_all; intros.
    apply in_map_iff in H2.
    destruct H2 as [? [? ?]]; subst.
    apply in_map_iff in H3.
    destruct H3 as [? [? ?]]; subst.
    unfold automaton_accepting_matrices in H3.
    apply filter_In in H3.
    destruct H3 as [_ ?].
    eapply term_lequiv_trans.
    + apply times_mor_mono; [| reflexivity ].
      apply automaton_relation_solution_step with (aut := aut).
    + eapply term_lequiv_trans.
      * apply automaton_relation_solution_merge.
      * apply sum_lequiv_member.
        apply in_map_iff.
        eexists; intuition.
        unfold automaton_accepting_matrices.
        apply filter_In.
        split; [apply finite_cover |].
        unfold vector_inner_product_bool.
        apply disj_true.
        apply in_map_iff.
        unfold vector_inner_product_bool in H2.
        apply disj_true in H2.
        apply in_map_iff in H2.
        destruct H2 as [? [? _]].
        apply Bool.andb_true_iff in H2; destruct H2.
        exists x; split; [| apply finite_cover ].
        apply Bool.andb_true_iff; intuition.
        apply matrix_product_characterise.
        exists q2; intuition.
        autorewrite with automaton_transition_matrix.
        now rewrite matrix_product_bool_unit_right.
  - unfold automaton_sum_accepting_matrices.
    eapply term_lequiv_trans
      with (t2 := automaton_relation_solution aut finite_eqb).
    + unfold automaton_relation_solution, automaton_relation_solution_path.
      rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
      apply compute_automaton_solution_least_solution; simpl.
      now apply finite_eqb_eq.
    + apply sum_lequiv_member.
      apply in_map_iff.
      eexists; split; auto.
      unfold automaton_accepting_matrices.
      apply filter_In; split; [ apply finite_cover |].
      unfold vector_inner_product_bool; apply disj_true.
      apply in_map_iff.
      exists q0; intuition.
      apply Bool.andb_true_iff; intuition.
      now apply finite_eqb_eq.
Qed.

Definition automaton_lift_sum_accepting_paths
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (q: Q)
:=
    sum (
      map (curry (compute_automaton_solution (automaton_lift aut)) q)
          (filter (aut_accept aut) finite_enum)
    )
.

Lemma automaton_lift_solution_lower
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
:
  compute_automaton_solution aut <==
  automaton_lift_sum_accepting_paths aut
.
Proof.
  intro.
  rewrite <- ETimesUnitRight
    with (t := compute_automaton_solution aut q).
  apply compute_automaton_solution_least_solution.
  split; intros.
  - unfold automaton_lift_sum_accepting_paths.
    rewrite <- sum_distribute_left.
    apply sum_lequiv_all; intros.
    apply in_map_iff in H2.
    destruct H2 as [q' [? ?]]; subst.
    apply in_map_iff in H3.
    destruct H3 as [q'' [? ?]]; subst.
    apply filter_In in H3.
    destruct H3 as [_ ?].
    unfold curry at 1; simpl.
    apply term_lequiv_trans
      with (t2 := compute_automaton_solution (automaton_lift aut) (q1, q'')).
    + rewrite <- ETimesUnitRight
        with (t := compute_automaton_solution _ (q2, q'')).
      rewrite <- ETimesUnitRight
        with (t := compute_automaton_solution _ (q1, q'')).
      apply compute_automaton_solution_least_solution; simpl.
      apply Bool.andb_true_iff.
      now rewrite finite_eqb_eq.
    + apply sum_lequiv_member.
      apply in_map_iff.
      exists q''; intuition.
      apply filter_In; intuition.
  - unfold automaton_lift_sum_accepting_paths.
    eapply term_lequiv_trans
      with (t2 := compute_automaton_solution (automaton_lift aut) (q0, q0)).
    + rewrite <- ETimesUnitRight
        with (t := compute_automaton_solution _ _).
      apply compute_automaton_solution_least_solution; simpl.
      now apply finite_eqb_eq.
    + apply sum_lequiv_member.
      apply in_map_iff.
      exists q0; intuition.
      apply filter_In; intuition.
Qed.

Definition automaton_fix_accepting_state
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (q: Q)
:
  automaton Q
:= {|
  aut_transitions := aut_transitions aut;
  aut_accept q' := finite_eqb q q';
|}.

Definition automaton_reconstruct_path
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (q1 q2: Q)
:
  term
:=
  compute_automaton_solution (automaton_fix_accepting_state aut q2) q1
.

Lemma automaton_lift_solution_upper
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
:
  compute_automaton_solution (automaton_lift aut) <==
  uncurry (automaton_reconstruct_path aut)
.
Proof.
  intro.
  rewrite <- ETimesUnitRight
    with (t := compute_automaton_solution _ q).
  apply compute_automaton_solution_least_solution.
  split; intros.
  - unfold automaton_reconstruct_path.
    destruct q1, q2; simpl.
    simpl in H1.
    apply Bool.andb_true_iff in H1; destruct H1.
    apply finite_eqb_eq in H2; subst.
    rewrite <- ETimesUnitRight
      with (t := compute_automaton_solution _ q2).
    rewrite <- ETimesUnitRight
      with (t := compute_automaton_solution _ q0).
    apply compute_automaton_solution_least_solution.
    now simpl.
  - destruct q0; simpl in *.
    apply finite_eqb_eq in H1; subst.
    unfold automaton_reconstruct_path.
    rewrite <- ETimesUnitRight
      with (t := compute_automaton_solution _ _).
    apply compute_automaton_solution_least_solution; simpl.
    now apply finite_eqb_eq.
Qed.

Lemma automaton_lift_solution_characterise
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (q: Q)
:
  compute_automaton_solution aut q ==
  automaton_lift_sum_accepting_paths aut q
.
Proof.
  apply term_lequiv_squeeze.
  - apply automaton_lift_solution_lower.
  - unfold automaton_lift_sum_accepting_paths.
    apply sum_lequiv_all; intros.
    apply in_map_iff in H1.
    destruct H1 as [q' [? ?]]; subst.
    apply filter_In in H2.
    destruct H2 as [_ ?].
    unfold curry; simpl.
    eapply term_lequiv_trans.
    apply automaton_lift_solution_upper; simpl.
    unfold automaton_reconstruct_path; simpl.
    rewrite <- ETimesUnitRight
      with (t := compute_automaton_solution _ _).
    apply compute_automaton_solution_least_solution.
    split; intros.
    + rewrite <- ETimesUnitRight
        with (t := compute_automaton_solution _ q2).
      rewrite <- ETimesUnitRight
        with (t := compute_automaton_solution _ q1).
      now apply compute_automaton_solution_least_solution.
    + rewrite <- ETimesUnitRight
        with (t := compute_automaton_solution _ q0).
      apply compute_automaton_solution_least_solution.
      simpl in H2; rewrite finite_eqb_eq in H2.
      now subst.
Qed.

Lemma automaton_lift_transition_monad_discard_accept
 {Q: Type}
 `{Finite Q}
 (aut: automaton Q)
 (m1 m2: Q -> Q -> bool)
:
  automaton_lift (automaton_transition_monad aut m1) =
  automaton_lift (automaton_transition_monad aut m2)
.
Proof.
  reflexivity.
Qed.

Lemma filter_singleton
  {X: Type}
  `{Finite X}
  (f: X -> bool)
  (l: list X)
  (x: X)
:
  (forall x', f x' = true <-> x = x') ->
  filter f l = repeat x (count_occ finite_dec l x)
.
Proof.
  intros.
  induction l.
  - reflexivity.
  - destruct (finite_dec a x).
    + subst; simpl.
      destruct (finite_dec x x); intuition.
      destruct (f x) eqn:?.
      * simpl; now f_equal.
      * specialize (H1 x).
        intuition congruence.
    + simpl.
      destruct (f a) eqn:?.
      * apply H1 in Heqb; congruence.
      * destruct (finite_dec a x); intuition.
Qed.

Lemma finite_count_occ
  {X: Type}
  `{Finite X}
  (x: X)
:
  count_occ finite_dec finite_enum x = 1%nat
.
Proof.
  apply PeanoNat.Nat.le_antisymm.
  - apply NoDup_count_occ.
    apply finite_nodup.
  - apply count_occ_In.
    apply finite_cover.
Qed.

Lemma automaton_transition_monad_accepting
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (m: Q -> Q -> bool)
:
  filter (aut_accept (automaton_transition_monad aut m)) finite_enum = m :: nil
.
Proof.
  rewrite filter_singleton with (x := m).
  - now rewrite finite_count_occ.
  - now setoid_rewrite finite_eqb_eq.
Qed.

Definition automaton_relation_solution'
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (m: Q -> Q -> bool)
:
  term
:=
    compute_automaton_solution (automaton_transition_monad aut m) finite_eqb
.

Lemma automaton_relation_solution_characterise
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (m: Q -> Q -> bool)
:
  automaton_relation_solution aut m ==
  automaton_relation_solution' aut m
.
Proof.
  unfold automaton_relation_solution,
         automaton_relation_solution_path,
         automaton_relation_solution'.
  rewrite automaton_lift_solution_characterise
    with (aut := automaton_transition_monad aut m).
  unfold automaton_lift_sum_accepting_paths.
  rewrite automaton_transition_monad_accepting.
  simpl; autorewrite with sum.
  rewrite EPlusUnit.
  unfold curry; simpl.
  now rewrite automaton_lift_transition_monad_discard_accept with (m2 := m).
Qed.

Definition automaton_sum_reached_paths
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (q: Q)
  (m: Q -> Q -> bool)
:
  term
:=
  sum (map (compute_automaton_solution aut) (filter (m q) finite_enum))
.

Lemma automaton_transition_monad_solution_upper
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (q q': Q)
  (m m': Q -> Q -> bool)
:
  m q q' = true ->
  aut_accept aut q' = true ->
  compute_automaton_solution (automaton_transition_monad aut m) m' <=
  automaton_sum_reached_paths aut q m'
.
Proof.
  intros.
  rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
  apply compute_automaton_solution_least_solution.
  clear m'.
  split.
  - intros a m1 m2 ?; unfold automaton_sum_reached_paths.
    rewrite <- sum_distribute_left.
    rewrite map_map.
    apply sum_lequiv_all; intros.
    apply in_map_iff in H4.
    destruct H4 as [q'' [? ?]]; subst.
    apply filter_In in H5.
    destruct H5 as [_ ?].
    apply finite_eqb_eq in H3; subst.
    apply matrix_product_characterise in H4.
    destruct H4 as [q3 [? ?]].
    apply term_lequiv_trans with (t2 := compute_automaton_solution aut q3).
    + rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q'').
      rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q3).
      now apply compute_automaton_solution_least_solution.
    + apply sum_lequiv_member.
      apply in_map_iff.
      exists q3; intuition.
      apply filter_In; intuition.
  - intros m' ?; unfold automaton_sum_reached_paths.
    simpl in H3.
    apply finite_eqb_eq in H3; subst.
    apply term_lequiv_trans with (t2 := compute_automaton_solution aut q').
    + rewrite <- ETimesUnitRight with (t := compute_automaton_solution aut q').
      now apply compute_automaton_solution_least_solution.
    + apply sum_lequiv_member.
      apply in_map_iff.
      exists q'; intuition.
      apply filter_In; intuition.
Qed.

Lemma automaton_sum_accepting_matrices_upper
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
:
  automaton_sum_accepting_matrices aut <== compute_automaton_solution aut
.
Proof.
  intro q.
  unfold automaton_sum_accepting_matrices.
  apply sum_lequiv_all; intros.
  apply in_map_iff in H1.
  destruct H1 as [m [? ?]]; subst.
  unfold automaton_accepting_matrices in H2.
  apply filter_In in H2.
  destruct H2 as [_ ?].
  apply disj_true in H1.
  apply in_map_iff in H1.
  destruct H1 as [q' [? _]].
  apply Bool.andb_true_iff in H1.
  destruct H1 as [? ?].
  rewrite automaton_relation_solution_characterise.
  eapply term_lequiv_trans.
  apply automaton_transition_monad_solution_upper with (q := q) (q' := q'); auto.
  unfold automaton_sum_reached_paths.
  apply sum_lequiv_all; intros.
  apply in_map_iff in H3.
  destruct H3 as [q'' [? ?]]; subst.
  apply filter_In in H4.
  destruct H4 as [_ ?].
  apply finite_eqb_eq in H3; subst.
  apply term_lequiv_refl.
Qed.

Lemma automaton_sum_accepting_matrices_characterise
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
:
  automaton_sum_accepting_matrices aut === compute_automaton_solution aut
.
Proof.
  apply vector_lequiv_squeeze.
  - apply automaton_sum_accepting_matrices_upper.
  - apply automaton_sum_accepting_matrices_lower.
Qed.

Inductive HasDup {X: Type}: list X -> Prop :=
| HasDupBase:
    forall (x: X) (l: list X),
    In x l ->
    HasDup (x :: l)
| HasDupStep:
    forall (x: X) (l: list X),
    HasDup l ->
    HasDup (x :: l)
.

Lemma NoDup_HasDup
  {X: Type}
  `{Finite X}
  (l: list X)
:
  NoDup l \/ HasDup l
.
Proof.
  induction l.
  - left; constructor.
  - destruct IHl.
    + destruct (In_dec finite_dec a l).
      * right; now constructor.
      * left; now constructor.
    + right; now constructor.
Qed.

Lemma HasDup_exists
  {X: Type}
  (l: list X)
:
  HasDup l ->
  exists (l1 l2 l3: list X) (x: X),
    l = l1 ++ (x :: nil) ++ l2 ++ (x :: nil) ++ l3
.
Proof.
  intros.
  induction H0.
  - apply in_split in H0.
    destruct H0 as [l2 [l3 ?]].
    exists nil, l2, l3, x.
    simpl; now f_equal.
  - destruct IHHasDup as [l1 [l2 [l3 [x' ?]]]].
    exists (x :: l1), l2, l3, x'.
    simpl; now f_equal.
Qed.

Require Import Coq.micromega.Lia.

Lemma pigeonhole_principle
  {X: Type}
  `{Finite X}
  (l: list X)
:
  length l > length finite_enum ->
  exists (l1 l2 l3: list X) (x: X),
    l = l1 ++ (x :: nil) ++ l2 ++ (x :: nil) ++ l3
.
Proof.
  intros.
  destruct (NoDup_HasDup l).
  - apply NoDup_incl_length with (l' := finite_enum) in H2.
    + lia.
    + intro x; intros.
      apply finite_cover.
  - now apply HasDup_exists.
Qed.

Fixpoint iterate
  {X: Type}
  (f: X -> X)
  (x: X)
  (n: nat)
:=
  match n with
  | 0%nat => x
  | S n => f (iterate f x n)
  end
.

Class PartialOrderZero (X: Type) := {
  partial_order_rel :> X -> X -> Prop;
  partial_order_refl:
    forall (x1: X),
    partial_order_rel x1 x1;
  partial_order_trans:
    forall (x1 x2 x3: X),
    partial_order_rel x1 x2 ->
    partial_order_rel x2 x3 ->
    partial_order_rel x1 x3;
  partial_order_antisym:
    forall (x1 x2: X),
    partial_order_rel x1 x2 ->
    partial_order_rel x2 x1 ->
    x1 = x2;
  partial_order_zero: X;
  partial_order_bottom:
    forall (x: X),
    partial_order_rel partial_order_zero x;
}.

Definition mono_fixpoint
  {X: Type}
  `{Finite X}
  `{PartialOrderZero X}
  (f: X -> X)
:
  X
:=
  iterate f partial_order_zero (length finite_enum)
.

Lemma map_app_lift {X Y: Type} (f: X -> Y) (lx: list X) (ly1 ly2: list Y):
  map f lx = ly1 ++ ly2 ->
  exists (lx1 lx2: list X),
    lx = lx1 ++ lx2 /\
    map f lx1 = ly1 /\
    map f lx2 = ly2
.
Proof.
  intros; revert lx H0; induction ly1; intros.
  - rewrite app_nil_l in H0.
    exists nil, lx.
    intuition.
  - destruct lx; simpl in H0.
    + discriminate.
    + inversion H0; subst.
      apply IHly1 in H3.
      destruct H3 as [lx1 [lx2 [? [? ?]]]].
      exists (x :: lx1), lx2; simpl.
      intuition congruence.
Qed.

Record monotone
  {X Y: Type}
  `{PartialOrderZero X}
  `{PartialOrderZero Y}
  (f: X -> Y)
:= {
  monotone_preserve:
    forall (x1 x2: X),
      partial_order_rel x1 x2 ->
      partial_order_rel (f x1) (f x2);
}.

Lemma iterate_order
  {X: Type}
  `{PartialOrderZero X}
  (f: X -> X)
  (n: nat)
:
  monotone f ->
  partial_order_rel (iterate f partial_order_zero n)
                    (f (iterate f partial_order_zero n))
.
Proof.
  intros.
  induction n; simpl.
  - apply partial_order_bottom.
  - now apply monotone_preserve.
Qed.

Lemma iterate_mono
  {X: Type}
  `{PartialOrderZero X}
  (f: X -> X)
  (n m: nat)
:
  monotone f ->
  (n <= m)%nat ->
  partial_order_rel (iterate f partial_order_zero n)
                    (iterate f partial_order_zero m)
.
Proof.
  intros.
  apply PeanoNat.Nat.le_exists_sub in H2.
  destruct H2 as [k [? _]]; subst.
  induction k; simpl.
  - apply partial_order_refl.
  - eapply partial_order_trans.
    + now apply iterate_order.
    + now apply monotone_preserve.
Qed.

Lemma iterate_repeat
  {X: Type}
  `{PartialOrderZero X}
  (f: X -> X)
  (n m: nat)
:
  n < m ->
  monotone f ->
  iterate f partial_order_zero n = iterate f partial_order_zero m ->
  f (iterate f partial_order_zero m) = iterate f partial_order_zero m
.
Proof.
  intros.
  rewrite <- H3.
  apply partial_order_antisym.
  - rewrite H3 at 2.
    replace (f (iterate f partial_order_zero n))
      with (iterate f partial_order_zero (S n))
      by reflexivity.
    now apply iterate_mono.
  - now apply iterate_order.
Qed.

Lemma iterate_beyond
  {X: Type}
  `{PartialOrderZero X}
  (f: X -> X)
  (n m: nat)
:
  (n <= m)%nat ->
  monotone f ->
  iterate f partial_order_zero n = f (iterate f partial_order_zero n) ->
  iterate f partial_order_zero m = iterate f partial_order_zero n
.
Proof.
  intros.
  apply PeanoNat.Nat.le_exists_sub in H1.
  destruct H1 as [k [? _]]; subst.
  induction k; simpl; congruence.
Qed.

Lemma iterate_fixed
  {X: Type}
  `{PartialOrderZero X}
  (f: X -> X)
  (n m: nat)
:
  (n <= m)%nat ->
  monotone f ->
  iterate f partial_order_zero n = f (iterate f partial_order_zero n) ->
  f (iterate f partial_order_zero m) = iterate f partial_order_zero m
.
Proof.
  intros.
  replace (f (iterate f partial_order_zero m))
    with (iterate f partial_order_zero (S m))
    by reflexivity.
  rewrite iterate_beyond with (n := n); auto.
  now rewrite iterate_beyond with (n := n) (m := m).
Qed.

Lemma app_match_left
  {X: Type}
  (l1 l2 l3 l4: list X)
:
  length l1 = length l3 ->
  l1 ++ l2 = l3 ++ l4 ->
  l1 = l3
.
Proof.
  intros.
  apply (f_equal (firstn (length l1))) in H1.
  repeat rewrite firstn_app in H1.
  replace (length l1 - length l1) with 0%nat in H1 by lia.
  replace (length l1 - length l3) with 0%nat in H1 by lia.
  repeat rewrite firstn_O in H1.
  repeat rewrite app_nil_r in H1.
  rewrite H0 in H1 at 2.
  now repeat rewrite firstn_all in H1.
Qed.

Lemma app_match_right
  {X: Type}
  (l1 l2 l3 l4: list X)
:
  length l1 = length l3 ->
  l1 ++ l2 = l3 ++ l4 ->
  l2 = l4
.
Proof.
  intros.
  apply (f_equal (skipn (length l1))) in H1.
  repeat rewrite skipn_app in H1.
  replace (length l1 - length l1) with 0%nat in H1 by lia.
  replace (length l1 - length l3) with 0%nat in H1 by lia.
  rewrite H0 in H1 at 2.
  repeat rewrite skipn_all in H1.
  repeat rewrite skipn_O in H1.
  now repeat rewrite app_nil_l in H1.
Qed.

Lemma seq_order
  (len: nat)
  (l1 l2: list nat)
  (n m: nat)
:
  seq 0 len = l1 ++ l2 ->
  In n l1 ->
  In m l2 ->
  n < m
.
Proof.
  intros; assert (len = length l1 + length l2)%nat.
  - rewrite <- app_length.
    erewrite <- seq_length at 1.
    now rewrite H0.
  - subst.
    rewrite seq_app in H0; simpl in H0.
    erewrite <- app_match_left
      with (l1 := seq 0 (length l1)) in H1.
    erewrite <- app_match_right
      with (l2 := seq (length l1) (length l2)) in H2.
    + apply in_seq in H1, H2; lia.
    + now rewrite seq_length.
    + apply H0.
    + now rewrite seq_length.
    + apply H0.
Qed.

Lemma mono_fixpoint_fixpoint
  {X: Type}
  `{Finite X}
  `{PartialOrderZero X}
  (f: X -> X)
:
  monotone f ->
  f (mono_fixpoint f) = mono_fixpoint f
.
Proof.
  pose (points := map (iterate f partial_order_zero)
                      (seq 0 (S (length finite_enum)))).
  destruct (pigeonhole_principle points) as [l1 [l2 [l3 [p ?]]]].
  - subst points.
    rewrite map_length, seq_length.
    lia.
  - intuition.
    apply map_app_lift in H2.
    destruct H2 as [ln1 [lnt1 [? [? ?]]]]; subst.
    apply map_app_lift in H5.
    destruct H5 as [ln2 [lnt2 [? [? ?]]]]; subst.
    apply map_app_lift in H6.
    destruct H6 as [ln3 [lnt3 [? [? ?]]]]; subst.
    apply map_app_lift in H7.
    destruct H7 as [ln4 [ln5 [? [? ?]]]]; subst.
    destruct ln2; simpl in H5; [ discriminate | inversion H5; clear H5 ].
    destruct ln4; simpl in H6; [ discriminate | inversion H6; clear H6 ].
    apply map_eq_nil in H8, H9; subst.
    intros; unfold mono_fixpoint.
    apply iterate_fixed with (n := n); auto.
    + assert (In n (seq 0 (S (length finite_enum)))).
      * rewrite H2.
        rewrite in_app_iff; right; now left.
      * apply in_seq in H4; now lia.
    + rewrite <- H5; symmetry.
      eapply iterate_repeat with (n := n); auto.
      eapply seq_order.
      * rewrite <- app_assoc.
        apply H2.
      * rewrite in_app_iff; right; now left.
      * rewrite in_app_iff; right; now left.
Qed.

Lemma mono_fixpoint_least
  {X: Type}
  `{Finite X}
  `{PartialOrderZero X}
  (f: X -> X)
  (x: X)
:
  monotone f ->
  partial_order_rel (f x) x ->
  partial_order_rel (mono_fixpoint f) x
.
Proof.
  intros.
  unfold mono_fixpoint.
  generalize (length (finite_enum)); intros.
  induction n; simpl.
  - apply partial_order_bottom.
  - eapply partial_order_trans.
    + apply monotone_preserve; auto.
      apply IHn.
    + apply H3.
Qed.

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
