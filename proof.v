From Equations Require Import Equations.
Require Import Coq.Program.Equality.

Inductive position: nat -> Type :=
| PHere:
    forall {n: nat},
    position (S n)
| PThere:
    forall {n: nat}
           (v: position n),
    position (S n)
.

Variable (A: Type).

Inductive term :=
| zero: term
| one: term
| letter: A -> term
| plus: term -> term -> term
| times: term -> term -> term
| star: term -> term
.

Notation "0" := zero.
Notation "1" := one.
Notation "$ a" := (letter a) (at level 30).
Notation "t1 + t2" := (plus t1 t2) (at level 50, left associativity).
Notation "t1 ;; t2" := (times t1 t2) (at level 40, left associativity).
Notation "t *" := (star t) (at level 30).

Definition vector (Q: Type) := Q -> term.

Definition vector_sum
  {Q: Type}
  (v1 v2: vector Q)
  (q: Q)
  : term
:=
  v1 q + v2 q
.

Notation "v1 <+> v2" := (vector_sum v1 v2) (at level 40).

Definition vector_chomp
  {n: nat}
  (v: vector (position (S n)))
  (p: position n)
  : term
:=
  v (PThere p)
.

Notation "# v" := (vector_chomp v) (at level 30).

Equations inner_product {n: nat} (v1 v2: vector (position n)): term := {
  @inner_product 0 _ _ :=
    zero;
  @inner_product (S _) v1 v2 :=
    v1 PHere ;; v2 PHere + inner_product (vector_chomp v1) (vector_chomp v2);
}.

Notation "v1 ** v2" := (inner_product v1 v2) (at level 40).

Definition matrix (Q: Type) := Q -> Q -> term.

Definition matrix_vector_product
  {n: nat}
  (m: matrix (position n))
  (v: vector (position n))
  (p: position n)
:=
  (m p) ** v
.

Notation "m <*> v" := (matrix_vector_product m v) (at level 40).

Reserved Notation "t1 == t2" (at level 70).
Reserved Notation "t1 <= t2" (at level 70).

Polymorphic Inductive term_equiv: term -> term -> Prop :=
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
| EStarRight: forall t, t* == t* ;; t + 1
| EFixLeft: forall t1 t2 t3, t2 ;; t1 + t3 <= t1 -> t2* ;; t3 <= t1
where "t1 == t2" := (term_equiv t1 t2)
  and "t1 <= t2" := (t1 + t2 == t2).

Require Import Coq.Setoids.Setoid.

Add Relation term term_equiv
  reflexivity proved by ERefl
  symmetry proved by ESym
  transitivity proved by ETrans
  as equiv_eq
.

Add Morphism plus
  with signature term_equiv ==> term_equiv ==> term_equiv
  as plus_mor
.
Proof.
  intros.
  now apply ECongPlus.
Qed.

Add Morphism times
  with signature term_equiv ==> term_equiv ==> term_equiv
  as times_mor
.
Proof.
  intros.
  now apply ECongTimes.
Qed.

Add Morphism star
  with signature term_equiv ==> term_equiv
  as star_mor
.
Proof.
  intros.
  now apply ECongStar.
Qed.

Definition term_lequiv (t1 t2: term) := t1 <= t2.
Global Hint Unfold term_lequiv : core.

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

Add Relation term term_lequiv
  reflexivity proved by term_lequiv_refl
  transitivity proved by term_lequiv_trans
  as term_lequiv_po
.

Instance term_equiv_implies_lequiv: subrelation term_equiv term_lequiv.
Proof.
  unfold subrelation, term_lequiv; intros.
  rewrite H.
  now rewrite EPlusIdemp.
Qed.

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

Add Parametric Relation (Q: Type): (vector Q) equiv_vec
  reflexivity proved by equiv_vec_refl
  symmetry proved by equiv_vec_sym
  transitivity proved by equiv_vec_trans
  as equiv_equiv_vec
.

Add Parametric Morphism (Q: Type): vector_sum
  with signature (@equiv_vec Q) ==> equiv_vec ==> equiv_vec
  as vector_sum_mor
.
Proof.
  intros; intro.
  unfold vector_sum.
  now rewrite (H q), (H0 q).
Qed.

Add Parametric Morphism (n: nat): vector_chomp
  with signature (@equiv_vec (position (S n))) ==> equiv_vec
  as vector_comp_mor.
Proof.
  intros.
  intro.
  unfold vector_chomp.
  now rewrite (H (PThere q)).
Qed.

Add Parametric Morphism (n: nat): inner_product
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
Notation "v1 <== v2" := (lequiv_vec v1 v2) (at level 70).

Record system (Q: Type) := {
  smat: matrix Q;
  svec: vector Q;
}.
Arguments smat {Q}.
Arguments svec {Q}.

Record solution
  {Q: Type}
  (sys: system Q)
  (scale: term)
  (sol: vector Q)
:= {
  solution_move:
    forall (q q': Q),
    smat sys q q' ;; sol q' <= sol q;
  solution_bias:
    forall (q: Q),
    svec sys q ;; scale <= sol q;
}.

Record least_solution
  {Q: Type}
  (sys: system Q)
  (scale: term)
  (sol: vector Q)
:= {
  least_solution_solution:
    solution sys scale sol;
  least_solution_least:
    forall sol',
    solution sys scale sol' ->
    sol <== sol'
}.

Definition compress_system
  {n: nat}
  (sys: system (position (S n)))
  : system (position n)
:= {|
  smat p1 p2 :=
    smat sys (PThere p1) (PThere p2) +
    smat sys (PThere p1) PHere
      ;; (smat sys PHere PHere)*
      ;; smat sys PHere (PThere p2);
  svec p :=
    svec sys (PThere p) +
      smat sys (PThere p) PHere
        ;; (smat sys PHere PHere)*
        ;; svec sys PHere
|}.

Equations compute_solution_nat
  {n: nat}
  (sys: system (position n))
  (p: position n)
  : term
:= {
  @compute_solution_nat (S n) sys (PThere p) :=
    let smaller_solution := compute_solution_nat (compress_system sys) in
    smaller_solution p;
  @compute_solution_nat (S n) sys PHere :=
    let smaller_solution := compute_solution_nat (compress_system sys) in
    (smat sys PHere PHere)* ;;
      (svec sys PHere + (# (smat sys PHere)) ** smaller_solution);
}.

Definition vector_scale_left
  {Q: Type}
  (t: term)
  (v: vector Q)
  (q: Q)
:=
  t ;; v q
.

Notation "t & v" := (vector_scale_left t v) (at level 30).

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

Lemma compute_solution_nat_chomp
  {n: nat}
  (sys: system (position (S n)))
:
  # compute_solution_nat sys === compute_solution_nat (compress_system sys)
.
Proof.
  intro.
  unfold vector_chomp.
  now autorewrite with compute_solution_nat; simpl.
Qed.

Lemma compress_system_mat
  (n: nat)
  (sys: system (position (S n)))
  (p: position n)
:
  (smat sys (PThere p) PHere;; smat sys PHere PHere *) &
    (# smat sys PHere) <+> # smat sys (PThere p)
  === smat (compress_system sys) p
.
Proof.
  unfold compress_system; simpl.
  intro.
  unfold vector_sum, vector_scale_left, vector_chomp.
  now rewrite EPlusComm.
Qed.

Lemma compress_system_vec
  (n: nat)
  (sys: system (position (S n)))
  (p: position n)
:
  svec sys (PThere p) +
    smat sys (PThere p) PHere ;; smat sys PHere PHere * ;; svec sys PHere
  == svec (compress_system sys) p
.
Proof.
  now unfold compress_system; simpl.
Qed.

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

Lemma term_lequiv_inner_product
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

Add Morphism plus
  with signature term_lequiv ==> term_lequiv ==> term_lequiv
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

Add Morphism times
  with signature term_lequiv ==> term_lequiv ==> term_lequiv
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

Add Parametric Morphism (n: nat): inner_product
  with signature eq ==> (@lequiv_vec (position n)) ==> term_lequiv
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

Lemma term_lequiv_inner_product_split
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

Definition vector_scale
  {Q: Type}
  (v: vector Q)
  (t: term)
  (q: Q)
:=
  v q ;; t
.

Notation "v ;;; t" := (vector_scale v t) (at level 35).

Lemma vector_scale_unit
  {Q: Type}
  (v: vector Q)
:
  v ;;; 1 === v
.
Proof.
  intro q.
  unfold vector_scale.
  now rewrite ETimesUnitRight.
Qed.

Definition solution_nat
  {n: nat}
  (sys: system (position n))
  (scale: term)
  (sol: vector (position n))
:=
  smat sys <*> sol <+> svec sys ;;; scale <== sol
.

Lemma solution_iff_solution_nat
  {n: nat}
  (sys: system (position n))
  (scale: term)
  (sol: vector (position n))
:
  solution sys scale sol <-> solution_nat sys scale sol
.
Proof.
  split; intros.
  - unfold solution_nat.
    intro p.
    unfold vector_sum, matrix_vector_product.
    apply term_lequiv_split.
    + apply term_lequiv_inner_product_split; intro.
      apply H.
    + apply H.
  - split; intros.
    + eapply term_lequiv_trans; [apply term_lequiv_split_left|].
      * apply term_lequiv_inner_product.
      * apply H.
    + eapply term_lequiv_trans; [apply term_lequiv_split_right|].
      * apply term_lequiv_refl.
      * apply H.
Qed.

Lemma solution_one_solution_nat
  {Q: Type}
  (sys: system Q)
  (scale: term)
  (sol: vector Q)
:
  solution sys 1 sol ->
  solution sys scale (sol ;;; scale)
.
Proof.
  split; intros.
  - unfold vector_scale.
    rewrite ETimesAssoc.
    apply times_mor_mono; try reflexivity.
    apply H.
  - unfold vector_scale.
    apply times_mor_mono; try reflexivity.
    unfold term_lequiv.
    rewrite <- ETimesUnitRight with (t := svec sys q).
    apply H.
Qed.

Lemma compute_solution_nat_solution_nat_one
  {n: nat}
  (sys: system (position n))
:
  solution_nat sys 1 (compute_solution_nat sys)
.
Proof.
  unfold solution_nat; intro p.
  dependent induction p.
  + unfold vector_sum, matrix_vector_product.
    autorewrite with inner_product.
    autorewrite with compute_solution_nat; simpl.
    rewrite ETimesAssoc.
    unfold vector_scale; rewrite ETimesUnitRight.
    rewrite <- EPlusAssoc with (t3 := svec sys PHere).
    rewrite EPlusComm with (t2 := svec sys PHere).
    rewrite <- ETimesUnitLeft
      with (t := _ + # _ ** # compute_solution_nat sys).
    rewrite compute_solution_nat_chomp.
    rewrite <- EDistributeRight.
    rewrite <- EStarLeft.
    apply term_lequiv_refl.
  + unfold vector_sum, matrix_vector_product.
    autorewrite with inner_product.
    autorewrite with compute_solution_nat; simpl.
    rewrite ETimesAssoc.
    rewrite EDistributeLeft.
    rewrite compute_solution_nat_chomp.
    rewrite vector_inner_product_scale_left.
    rewrite <- EPlusAssoc with (t1 := _ ;; svec sys PHere).
    rewrite vector_inner_product_distribute_left.
    rewrite compress_system_mat.
    rewrite EPlusComm with (t1 := _ ;; svec sys PHere).
    unfold vector_scale; rewrite ETimesUnitRight.
    rewrite <- EPlusAssoc with (t3 := svec sys (PThere p)).
    rewrite EPlusComm with (t2 := svec sys (PThere p)) .
    rewrite compress_system_vec.
    unfold vector_scale, vector_sum in IHp;
    setoid_rewrite ETimesUnitRight in IHp.
    apply IHp.
Qed.

Lemma solution_bound_mat
  {Q: Type}
  (sys: system Q)
  (scale: term)
  (sol: vector Q)
  (q q': Q)
:
  solution sys scale sol ->
  term_lequiv ((smat sys q q)* ;; smat sys q q' ;; sol q') (sol q)
.
Proof.
  intros.
  rewrite <- ETimesAssoc.
  apply EFixLeft.
  apply term_lequiv_split;
  apply H.
Qed.

Lemma solution_bound_vec
  {Q: Type}
  (sys: system Q)
  (scale: term)
  (sol: vector Q)
  (q: Q)
:
  solution sys scale sol ->
  term_lequiv ((smat sys q q)* ;; svec sys q ;; scale) (sol q)
.
Proof.
  intros.
  rewrite <- ETimesAssoc.
  apply EFixLeft.
  apply term_lequiv_split;
  apply H.
Qed.

Lemma solution_bound
  {Q: Type}
  (sys: system Q)
  (scale: term)
  (sol: vector Q)
  (q q': Q)
:
  solution sys scale sol ->
  term_lequiv ((smat sys q q)* ;; (smat sys q q' ;; sol q' + svec sys q ;; scale)) (sol q)
.
Proof.
  intros.
  rewrite EDistributeLeft.
  apply term_lequiv_split.
  + rewrite ETimesAssoc.
    eapply solution_bound_mat; eauto.
  + rewrite ETimesAssoc.
    now apply solution_bound_vec.
Qed.

Ltac fold_term_lequiv :=
  match goal with
  | |- ?lhs <= ?rhs => fold (term_lequiv lhs rhs)
  end
.

Lemma solution_project
  {n: nat}
  (sys: system (position (S n)))
  (scale: term)
  (sol: vector (position (S n)))
:
  solution sys scale sol ->
  solution (compress_system sys) scale (# sol)
.
Proof.
  split; intros; simpl;
  rewrite EDistributeRight;
  unfold vector_chomp.
  - apply term_lequiv_split.
    + apply H.
    + fold_term_lequiv.
      repeat rewrite <- ETimesAssoc.
      rewrite ETimesAssoc with (t3 := sol (PThere q')).
      erewrite solution_bound_mat; eauto.
      apply H.
  - apply term_lequiv_split.
    + apply H.
    + fold_term_lequiv.
      repeat rewrite <- ETimesAssoc.
      rewrite ETimesAssoc with (t3 := scale).
      erewrite solution_bound_vec; eauto.
      apply H.
Qed.

(*
Lemma solution_project'
  {n: nat}
  (sys: system (position (S n)))
  (scale: term)
  (sol: vector (position (S n)))
:
  solution_nat sys scale sol ->
  solution_nat (compress_system sys) scale (# sol)
.
Proof.
  intros; intro p.
  unfold vector_sum, matrix_vector_product, vector_scale.
  rewrite <- compress_system_mat.
  rewrite <- compress_system_vec.
  rewrite <- vector_inner_product_distribute_left.
  rewrite <- vector_inner_product_scale_left.
  rewrite EPlusComm with (t1 := svec sys (PThere p)).
  rewrite EDistributeRight.
  rewrite EPlusAssoc.
  rewrite <- EPlusAssoc with (t2 := # smat sys (PThere p) ** # sol).
  rewrite EPlusComm with (t1 := # smat sys (PThere p) ** # sol).
  rewrite EPlusAssoc.
  rewrite <- ETimesAssoc with (t3 := scale).
  rewrite <- EDistributeLeft.
  rewrite <- ETimesAssoc.
  match goal with
  | |- ?lhs <= ?rhs => fold (term_lequiv lhs rhs)
  end.
  rewrite solution_bound_; auto.
  rewrite <- inner_product_equation_2.
  apply H.
Qed.
*)

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
    unfold vector_scale at 2; simpl.
    rewrite vector_scale_right_chomp.
    rewrite ETimesAssoc.
    reflexivity.
Qed.

Lemma compute_solution_nat_least
  {n: nat}
  (sys: system (position n))
  (scale: term)
  (sol: vector (position n))
:
  solution_nat sys scale sol ->
  compute_solution_nat sys ;;; scale <== sol
.
Proof.
  intros.
  dependent induction n; intro p; dependent destruction p.
  - unfold vector_scale.
    autorewrite with compute_solution_nat; simpl.
    rewrite EPlusComm with (t1 := svec sys PHere).
    fold_term_lequiv.
    rewrite <- ETimesAssoc.
    rewrite EDistributeRight.
    rewrite vector_inner_product_scale_right.
    rewrite IHn with (sol := # sol).
    + rewrite EDistributeLeft.
      apply term_lequiv_split.
      * rewrite vector_inner_product_scale_left.
        apply term_lequiv_inner_product_split; intros.
        unfold vector_scale_left.
        unfold vector_chomp.
        eapply solution_bound_mat.
        now apply solution_iff_solution_nat.
      * rewrite ETimesAssoc.
        apply solution_bound_vec.
        now apply solution_iff_solution_nat.
    + apply solution_iff_solution_nat.
      apply solution_project.
      now apply solution_iff_solution_nat.
  - autorewrite with compute_solution_nat; simpl.
    eapply term_lequiv_trans; swap 1 2.
    apply (IHn (compress_system sys) scale (# sol)).
    + apply solution_iff_solution_nat.
      apply solution_project.
      now apply solution_iff_solution_nat.
    + unfold vector_scale.
      autorewrite with compute_solution_nat; simpl.
      apply term_lequiv_refl.
Qed.

Lemma compute_solution_nat_least_solution
  {n: nat}
  (sys: system (position n))
  (scale: term)
:
  least_solution sys scale (compute_solution_nat sys ;;; scale)
.
Proof.
  split.
  - apply solution_one_solution_nat.
    apply solution_iff_solution_nat.
    apply compute_solution_nat_solution_nat_one.
  - setoid_rewrite solution_iff_solution_nat.
    apply compute_solution_nat_least.
Qed.

Require Import Coq.Lists.List.

Class Finite (X: Type) := {
  finite_enum: list X;
  finite_dec: forall (x1 x2: X), {x1 = x2} + {x1 <> x2};
  finite_eqb x1 x2 := if finite_dec x1 x2 then true else false;
  finite_cover: forall x, In x finite_enum;
  finite_nodup: NoDup finite_enum;
}.

Equations list_lookup_helper
  {X: Type}
  (l: list X)
  (n: position (length l))
  : X
:= {
  list_lookup_helper (x :: _) PHere := x;
  list_lookup_helper (_ :: l) (PThere p) := list_lookup_helper l p;
}.

Definition list_lookup
  {X: Type}
  `{Finite X}
  (n: position (length finite_enum))
  : X
:=
  list_lookup_helper finite_enum n
.

Equations list_index_helper
  {X: Type}
  (l: list X)
  (x: X)
  (Hdec: forall (x1 x2: X), {x1 = x2} + {x1 <> x2})
  (Hin: In x l)
  : position (length l)
:=
  list_index_helper (x' :: l) x Hdec Hin :=
    if Hdec x' x then PHere
    else PThere (list_index_helper l x Hdec _)
.
Next Obligation.
  now destruct Hin.
Defined.

Definition list_index
  {X: Type}
  `{Finite X}
  (x: X)
  : position (length finite_enum)
:=
  list_index_helper finite_enum x finite_dec (finite_cover x)
.

Lemma list_lookup_helper_in
  {X: Type}
  (l: list X)
  (p: position (length l))
:
  In (list_lookup_helper l p) l
.
Proof.
  induction l.
  - dependent destruction p.
  - dependent destruction p.
    + autorewrite with list_lookup_helper.
      now left.
    + autorewrite with list_lookup_helper.
      right.
      apply IHl.
Qed.

Lemma list_lookup_helper_injective
  {X: Type}
  (l: list X)
  (p1 p2: position (length l))
:
  NoDup l ->
  list_lookup_helper l p1 = list_lookup_helper l p2 ->
  p1 = p2
.
Proof.
  induction l; intros.
  - dependent destruction p1.
  - dependent destruction p1;
    dependent destruction p2;
    autorewrite with list_lookup_helper in H0;
    auto.
    + exfalso.
      pose proof (list_lookup_helper_in l p2).
      rewrite <- H0 in H1.
      now inversion H.
    + exfalso.
      pose proof (list_lookup_helper_in l p1).
      rewrite H0 in H1.
      now inversion H.
    + autorewrite with list_lookup_helper in H0.
      f_equal.
      apply IHl; auto.
      now inversion H.
Qed.

Lemma list_lookup_injective
  {X: Type}
  `{Finite X}
  (p1 p2: position (length finite_enum))
:
  list_lookup p1 = list_lookup p2 ->
  p1 = p2
.
Proof.
  unfold list_lookup; intros.
  apply list_lookup_helper_injective; auto.
  apply finite_nodup.
Qed.

Lemma list_lookup_helper_list_index_helper
  {X: Type}
  (l: list X)
  (x: X)
  (Hdec: forall (x x': X), {x = x'} + {x <> x'})
  (Hin: In x l)
:
  list_lookup_helper l (list_index_helper l x Hdec Hin) = x
.
Proof.
  induction l.
  - destruct Hin.
  - autorewrite with list_index_helper.
    destruct (Hdec a x);
    autorewrite with list_lookup_helper.
    + assumption.
    + now rewrite IHl.
Qed.

Lemma list_lookup_index
  {X: Type}
  `{Finite X}
  (x: X)
:
  list_lookup (list_index x) = x
.
Proof.
  unfold list_lookup.
  unfold list_index.
  apply list_lookup_helper_list_index_helper.
Qed.

Lemma list_index_lookup
  {X: Type}
  `{Finite X}
  (p: position (length finite_enum))
:
  list_index (list_lookup p) = p
.
Proof.
  apply list_lookup_injective.
  now rewrite list_lookup_index.
Qed.

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

Definition system_index
  {X: Type}
  `{Finite X}
  (sys: system X)
:
  system (position (length finite_enum))
:= {|
  smat := matrix_index (smat sys);
  svec := vector_index (svec sys);
|}.

Definition system_lookup
  {X: Type}
  `{Finite X}
  (sys: system (position (length finite_enum)))
:
  system X
:= {|
  smat := matrix_lookup (smat sys);
  svec := vector_lookup (svec sys);
|}.

Lemma solution_finite_to_nat
  {X: Type}
  `{Finite X}
  (sys: system X)
  (scale: term)
  (v: vector X)
:
  solution sys scale v ->
  solution (system_index sys) scale (vector_index v)
.
Proof.
  split; intros; simpl; apply H0.
Qed.

Lemma solution_nat_to_finite
  {X: Type}
  `{Finite X}
  (sys: system (position (length finite_enum)))
  (scale: term)
  (v: vector (position (length (finite_enum))))
:
  solution sys scale v ->
  solution (system_lookup sys) scale (vector_lookup v)
.
Proof.
  split; intros; simpl; apply H0.
Qed.

Definition compute_solution
  {X: Type}
  `{Finite X}
  (sys: system X)
:
  vector X
:=
  vector_lookup (compute_solution_nat (system_index sys))
.

Lemma compute_solution_solution
  {X: Type}
  `{Finite X}
  (sys: system X)
  (scale: term)
:
  solution sys scale (compute_solution sys ;;; scale)
.
Proof.
  split; intros.
  - replace (smat sys q q') with (smat (system_index sys) (list_index q) (list_index q')).
    + apply compute_solution_nat_least_solution.
    + simpl; unfold matrix_index.
      now repeat rewrite list_lookup_index.
  - replace (svec sys q) with (svec (system_index sys) (list_index q)).
    + apply compute_solution_nat_least_solution.
    + simpl; unfold vector_index.
      now rewrite list_lookup_index.
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
    rewrite <- list_lookup_index at 2.
    rewrite <- list_lookup_index at 3.
    apply H0.
  - intro p.
    unfold vector_index.
    rewrite <- list_index_lookup at 1.
    apply H0.
Qed.

Lemma compute_solution_least
  {X: Type}
  `{Finite X}
  (sys: system X)
  (scale: term)
:
  forall sol,
    solution sys scale sol ->
    compute_solution sys ;;; scale <== sol
.
Proof.
  intros; intro x.
  unfold compute_solution, vector_scale.
  replace (vector_lookup _ x ;; scale)
    with (vector_lookup (compute_solution_nat (system_index sys) ;;; scale) x)
    by reflexivity.
  apply vector_lequiv_adjunction.
  apply compute_solution_nat_least_solution.
  now apply solution_finite_to_nat.
Qed.

Lemma compute_solution_least_solution
  {X: Type}
  `{Finite X}
  (sys: system X)
  (scale: term)
:
  least_solution sys scale (compute_solution sys ;;; scale)
.
Proof.
  split.
  - apply compute_solution_solution.
  - apply compute_solution_least.
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

Lemma least_solution_unique
  {X: Type}
  (sys: system X)
  (scale: term)
  (v1 v2: vector X)
:
  least_solution sys scale v1 ->
  least_solution sys scale v2 ->
  v1 === v2
.
Proof.
  intros.
  apply vector_lequiv_squeeze.
  - apply H.
    apply H0.
  - apply H0.
    apply H.
Qed.

Inductive derivative: term -> Type :=
| TOneOne:
    derivative 1
| TLetterLetter:
    forall (a: A),
    derivative ($ a)
| TLetterOne:
    forall {a: A},
    derivative ($ a)
| TPlusLeft:
    forall {t1: term} (t2: term),
    derivative t1 ->
    derivative (t1 + t2)
| TPlusRight:
    forall (t1: term) {t2: term},
    derivative t2 ->
    derivative (t1 + t2)
| TTimesPre:
    forall {t1: term} (t2: term),
    derivative t1 ->
    derivative (t1 ;; t2)
| TTimesPost:
    forall (t1: term) {t2: term},
    derivative t2 ->
    derivative (t1 ;; t2)
| TStarInner:
    forall (t: term),
    derivative t ->
    derivative (t *)
| TStarOne:
    forall (t: term),
    derivative (t *)
.

Derive NoConfusion for term.

Equations derivative_write {t: term} (d: derivative t): term := {
  derivative_write TOneOne := 1;
  derivative_write (TLetterLetter a) := $ a;
  derivative_write TLetterOne := 1;
  derivative_write (TPlusLeft _ d) := derivative_write d;
  derivative_write (TPlusRight _ d) := derivative_write d;
  derivative_write (TTimesPre t2 d) := derivative_write d ;; t2;
  derivative_write (TTimesPost _ d) := derivative_write d;
  derivative_write (TStarInner t d) := derivative_write d ;; t *;
  derivative_write (TStarOne t) := 1;
}.

Inductive initial:
  forall {t: term},
  derivative t ->
  Prop
:=
| InitialOneOne:
    initial TOneOne
| InitialLetterLetter:
    forall (a: A),
    initial (TLetterLetter a)
| InitialPlusLeft:
    forall (t1 t2: term) (d1: derivative t1),
    initial d1 ->
    initial (TPlusLeft t2 d1)
| InitialPlusRight:
    forall (t1 t2: term) (d2: derivative t2),
    initial d2 ->
    initial (TPlusRight t1 d2)
| InitialTimesPre:
    forall (t1 t2: term) (d1: derivative t1),
    initial d1 ->
    initial (TTimesPre t2 d1)
| InitialStarStep:
    forall (t: term) (d: derivative t),
    initial d ->
    initial (TStarInner t d)
| InitialStarOne:
    forall (t: term),
    initial (TStarOne t)
.

Equations initial_b (t: term) (d: derivative t): bool := {
  initial_b 1 TOneOne := true;
  initial_b ($ a) (TLetterLetter a) := true;
  initial_b (t1 + t2) (TPlusLeft _ d1) := initial_b t1 d1;
  initial_b (t1 + t2) (TPlusRight _ d2) := initial_b t2 d2;
  initial_b (t1 ;; t2) (TTimesPre _ d1) := initial_b t1 d1;
  initial_b (t*) (TStarInner _ d) := initial_b t d;
  initial_b (t*) (TStarOne _) := true;
  initial_b _ _ := false;
}.

Arguments initial_b {t}.

Lemma initial_dec (t: term) (d: derivative t):
  initial d <-> initial_b d = true
.
Proof.
  dependent induction d;
  autorewrite with initial_b;
  match goal with
  | |- _ <-> true = true =>
    split; intros; [reflexivity | constructor]
  | |- _ <-> false = true =>
    split; intros; [inversion H | discriminate]
  | |- _ <-> initial_b d = true =>
    split; intros; [
      dependent destruction H |
      constructor ];
    intuition
  end.
Qed.

Equations initial_l (t: term): list (derivative t) := {
  initial_l 0 := nil;
  initial_l 1 := TOneOne :: nil;
  initial_l ($ a) := TLetterLetter a :: nil;
  initial_l (t1 + t2) :=
    map (TPlusLeft _) (initial_l t1) ++
    map (TPlusRight _) (initial_l t2);
  initial_l (t1 ;; t2) := map (TTimesPre t2) (initial_l t1);
  initial_l (t*) := TStarOne t :: map (TStarInner t) (initial_l t);
}.

Search existT.

Ltac clean_exists :=
  repeat match goal with
  | H: existT ?P ?p _ = existT ?P ?p _ |- _ =>
    apply Eqdep.EqdepTheory.inj_pair2 in H
         end;
  subst.

Lemma initial_list (t: term) (d: derivative t):
  initial d <-> In d (initial_l t)
.
Proof.
  dependent induction d;
  autorewrite with initial_l;
  autorewrite with initial_b;
  try (split; intros; [now left | constructor]);
  try (split; intros; [inversion H | now destruct H]).
  - rewrite in_app_iff; repeat rewrite in_map_iff.
    split; intros.
    + dependent destruction H.
      left; eexists.
      intuition.
    + constructor.
      destruct H as [[d' [? ?]] | [d' [? ?]]].
      * apply IHd.
        inversion H.
        now clean_exists.
      * discriminate.
  - rewrite in_app_iff; repeat rewrite in_map_iff.
    split; intros.
    + dependent destruction H.
      right; eexists.
      intuition.
    + constructor.
      destruct H as [[d' [? ?]] | [d' [? ?]]].
      * discriminate.
      * apply IHd.
        inversion H.
        now clean_exists.
  - rewrite in_map_iff.
    split; intros.
    + dependent destruction H.
      eexists.
      intuition.
    + constructor.
      apply IHd.
      destruct H as [d' [? ?]].
      inversion H.
      now clean_exists.
  - rewrite in_map_iff.
    split; intros.
    + dependent destruction H.
    + now destruct H as [d' [? ?]].
  - simpl.
    rewrite in_map_iff.
    split; intros.
    + dependent destruction H.
      right.
      eexists.
      intuition.
    + destruct H as [? | [d' [? ?]]];
      try discriminate.
      inversion H.
      constructor.
      clean_exists.
      intuition.
Qed.

Inductive nullable:
  forall {t: term},
  derivative t ->
  Prop
:=
| NullableOneOne:
    nullable TOneOne
| NullableLetterOne:
    forall (a: A),
    nullable (TLetterOne (a := a))
| NullablePlusLeft:
    forall (t1 t2: term) (d: derivative t1),
    nullable d ->
    nullable (TPlusLeft t2 d)
| NullablePlusRight:
    forall (t1 t2: term) (d: derivative t2),
    nullable d ->
    nullable (TPlusRight t1 d)
| NullableTimesPre:
    forall (t1 t2: term) (d1: derivative t1) (d2: derivative t2),
    nullable d1 ->
    nullable d2 ->
    initial d2 ->
    nullable (TTimesPre t2 d1)
| NullableTimesPost:
    forall (t1 t2: term) (d2: derivative t2),
    nullable d2 ->
    nullable (TTimesPost t1 d2)
| NullableStarInner:
    forall (t: term) (d: derivative t),
    nullable d ->
    nullable (TStarInner t d)
| NullableStarOne:
    forall (t: term),
    nullable (TStarOne t)
.

Equations conj (l: list bool) : bool := {
  conj nil := true;
  conj (b :: l) := b && (conj l);
}.

Equations disj (l: list bool) : bool := {
  disj nil := false;
  disj (b :: l) := b || (disj l);
}.

Equations nullable_b (t: term) (d: derivative t) : bool := {
  nullable_b 1 TOneOne := true;
  nullable_b ($ _) TLetterOne := true;
  nullable_b (t1 + t2) (TPlusLeft _ d) := nullable_b _ d;
  nullable_b (t1 + t2) (TPlusRight _ d) := nullable_b _ d;
  nullable_b (t1 ;; t2) (TTimesPre _ d) :=
    nullable_b _ d && disj (map (nullable_b _) (initial_l t2));
  nullable_b (t1 ;; t2) (TTimesPost _ d) :=
    nullable_b _ d;
  nullable_b (t*) (TStarInner _ d) :=
    nullable_b _ d;
  nullable_b (t*) (TStarOne _) := true;
  nullable_b _ _ := false;
}.

Arguments nullable_b {t}.

Lemma disj_true (l: list bool):
  disj l = true <-> In true l
.
Proof.
  split; intros.
  - induction l; autorewrite with disj in H.
    + discriminate.
    + destruct a.
      * now left.
      * right.
        intuition.
  - induction l.
    + contradiction.
    + destruct a; simpl.
      * now autorewrite with disj.
      * apply IHl.
        now destruct H.
Qed.

Lemma nullable_dec (t: term) (d: derivative t):
  nullable d <-> nullable_b d = true
.
Proof.
  dependent induction t;
  dependent destruction d;
  autorewrite with nullable_b;
  match goal with
  | |- _ <-> true = true =>
    split; intros; [reflexivity | constructor]
  | |- _ <-> false = true =>
    split; intros; [inversion H | discriminate]
  | |- _ <-> nullable_b _ = true =>
    split; intros; [
      dependent destruction H; intuition |
      constructor ];
    intuition
  | _ => idtac
  end.
  split; intros.
  - dependent destruction H.
    apply andb_true_intro; split.
    + now apply IHt1.
    + apply disj_true.
      apply in_map_iff.
      exists d2.
      split.
      * now apply IHt2.
      * now apply initial_list.
  - apply andb_prop in H; destruct H.
    apply disj_true in H0.
    apply in_map_iff in H0.
    destruct H0 as [d' [? ?]].
    eapply NullableTimesPre.
    + now apply IHt1.
    + apply IHt2.
      apply H0.
    + now apply initial_list.
Qed.

Equations nullable_b' (t: term) : bool := {
  nullable_b' 0 := false;
  nullable_b' 1 := true;
  nullable_b' ($ _) := false;
  nullable_b' (t1 + t2) := nullable_b' t1 || nullable_b' t2;
  nullable_b' (t1 ;; t2) := nullable_b' t1 && nullable_b' t2;
  nullable_b' (t *) := true;
}.

Arguments nullable_b {t}.

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

Lemma initial_reconstruct (t: term):
  t == sum (map derivative_write (initial_l t))
.
Proof.
  induction t.
  - now vm_compute.
  - vm_compute.
    now rewrite EPlusUnit.
  - vm_compute.
    now rewrite EPlusUnit.
  - autorewrite with initial_l.
    rewrite map_app.
    rewrite sum_split.
    repeat rewrite map_map.
    rewrite map_ext
      with (f := (fun x => derivative_write (TPlusLeft t2 x)))
           (g := derivative_write)
      by easy.
    rewrite map_ext
      with (f := (fun x => derivative_write (TPlusRight t1 x)))
           (g := derivative_write)
      by easy.
    now rewrite <- IHt1, <- IHt2.
  - autorewrite with initial_l.
    rewrite map_map.
    rewrite map_ext with (g := (fun x => derivative_write x ;; t2)) by easy.
    rewrite <- map_map with (g := fun x => x ;; t2).
    rewrite sum_distribute_right.
    now rewrite <- IHt1.
  - autorewrite with initial_l.
    simpl; autorewrite with sum.
    autorewrite with derivative_write.
    rewrite map_map.
    rewrite map_ext with (g := (fun x => derivative_write x ;; t*)) by easy.
    rewrite <- map_map with (g := fun x => x ;; t*).
    rewrite sum_distribute_right.
    rewrite <- IHt.
    rewrite EStarLeft at 1.
    now rewrite EPlusComm.
Qed.

Context `{Finite A}.

Inductive derive (a: A):
  forall {t: term},
  derivative t ->
  derivative t ->
  Prop
:=
| DeriveLetterLetter: derive a (TLetterLetter a) TLetterOne
| DerivePlusLeft:
    forall (t1 t2: term) (d11 d12: derivative t1),
    derive a d11 d12 ->
    derive a (TPlusLeft t2 d11) (TPlusLeft t2 d12)
| DerivePlusRight:
    forall (t1 t2: term) (d21 d22: derivative t2),
    derive a d21 d22 ->
    derive a (TPlusRight t1 d21) (TPlusRight t1 d22)
| DeriveTimesPre:
    forall (t1 t2: term) (d11 d12: derivative t1),
    derive a d11 d12 ->
    derive a (TTimesPre t2 d11) (TTimesPre t2 d12)
| DeriveTimesJump:
    forall (t1 t2: term) (d1: derivative t1) (i d2: derivative t2),
    nullable d1 ->
    initial i ->
    derive a i d2 ->
    derive a (TTimesPre t2 d1) (TTimesPost t1 d2)
| DeriveTimesPost:
    forall (t1 t2: term) (d21 d22: derivative t2),
    derive a d21 d22 ->
    derive a (TTimesPost t1 d21) (TTimesPost t1 d22)
| DeriveStarInnerStep:
    forall (t: term) (d1 d2: derivative t),
    derive a d1 d2 ->
    derive a (TStarInner t d1) (TStarInner t d2)
| DeriveStarInnerJump:
    forall (t: term) (d1 i d2: derivative t),
    nullable d1 ->
    initial i ->
    derive a i d2 ->
    derive a (TStarInner t d1) (TStarInner t d2)
.

Equations derive_b (a: A) {t: term} (d1 d2: derivative t): bool := {
  derive_b a (TLetterLetter a') TLetterOne :=
    if finite_dec a a' then true else false;
  derive_b a (TPlusLeft _ d1) (TPlusLeft _ d2) := derive_b a d1 d2;
  derive_b a (TPlusRight _ d1) (TPlusRight _ d2) := derive_b a d1 d2;
  derive_b a (TTimesPre _ d1) (TTimesPre _ d2) := derive_b a d1 d2;
  derive_b a (TTimesPre t2 d1) (TTimesPost _ d2) :=
    nullable_b d1 && disj (map (fun i => derive_b a i d2) (initial_l t2));
  derive_b a (TTimesPost _ d1) (TTimesPost _ d2) := derive_b a d1 d2;
  derive_b a (TStarInner _ d1) (TStarInner _ d2) :=
    derive_b a d1 d2 || (
      nullable_b d1 &&
      disj (map (fun i => derive_b a i d2) (initial_l t))
    );
  derive_b _ _ _ := false;
}.

Lemma derive_dec (t: term) (d1 d2: derivative t) (a: A):
  derive a d1 d2 <-> derive_b a d1 d2 = true
.
Proof.
  dependent induction t;
  dependent destruction d1;
  dependent destruction d2;
  autorewrite with derive_b;
  match goal with
  | |- _ <-> true = true =>
    split; intros; [reflexivity | constructor]
  | |- _ <-> false = true =>
    split; intros; [now inversion H0 | discriminate]
  | |- _ <-> derive_b _ _ _ = true =>
    split; intros; [
      dependent destruction H0; intuition |
      constructor ];
    intuition
  | _ => idtac
  end.
  - destruct (finite_dec a0 a); split; intros.
    + reflexivity.
    + subst; constructor.
    + now inversion H0.
    + discriminate.
  - split; intros.
    + dependent destruction H0.
      apply andb_true_intro; split.
      * now apply nullable_dec.
      * apply disj_true.
        apply in_map_iff.
        eexists.
        intuition.
        now apply initial_list.
    + apply andb_prop in H0; destruct H0.
      apply disj_true in H1.
      apply in_map_iff in H1.
      destruct H1 as [i [? ?]].
      eapply DeriveTimesJump.
      * now apply nullable_dec.
      * apply initial_list, H2.
      * now apply IHt2.
  - split; intros.
    + apply Bool.orb_true_intro.
      dependent destruction H0.
      * left.
        now apply IHt.
      * right.
        apply andb_true_intro; split.
        -- now apply nullable_dec.
        -- apply disj_true.
           apply in_map_iff.
           exists i.
           intuition.
           now apply initial_list.
    + apply Bool.orb_true_elim in H0.
      destruct H0.
      * apply DeriveStarInnerStep.
        now apply IHt.
      * apply andb_prop in e; destruct e.
        apply disj_true in H1.
        apply in_map_iff in H1.
        destruct H1 as [i [? ?]].
        eapply DeriveStarInnerJump.
        -- now apply nullable_dec.
        -- apply initial_list, H2.
        -- now apply IHt.
Qed.

Record automaton (Q: Type) := {
  aut_transitions: A -> Q -> Q -> bool;
  aut_accept: Q -> bool;
}.
Arguments aut_transitions {Q}.
Arguments aut_accept {Q}.

Record automaton_homomorphism
  {Q1 Q2: Type}
  (aut1: automaton Q1)
  (aut2: automaton Q2)
:= {
  automaton_homomorphism_f :> Q1 -> Q2;
  automaton_homomorphism_compatible:
    forall (a: A) (q1 q1': Q1),
    aut_transitions aut1 a q1 q1' = true ->
    aut_transitions aut2 a (automaton_homomorphism_f q1)
                           (automaton_homomorphism_f q1') = true;
  automaton_homomorphism_preserve:
    forall (q1: Q1),
    aut_accept aut1 q1 = true ->
    aut_accept aut2 (automaton_homomorphism_f q1) = true;
}.

Equations derive_list (t: term) : list (derivative t) := {
  derive_list 0 := nil;
  derive_list 1 := TOneOne :: nil;
  derive_list ($ a) := TLetterLetter a :: TLetterOne :: nil;
  derive_list (t1 + t2) :=
    map (TPlusLeft _) (derive_list t1) ++
    map (TPlusRight _) (derive_list t2);
  derive_list (t1 ;; t2) :=
    map (TTimesPre _) (derive_list t1) ++
    map (TTimesPost _) (derive_list t2);
  derive_list (t*) :=
    TStarOne _ :: map (TStarInner _) (derive_list t);
}.

Equations derive_eqb {t: term} (d1 d2: derivative t) : bool := {
  derive_eqb TOneOne TOneOne := true;
  derive_eqb (TLetterLetter _) (TLetterLetter _) := true;
  derive_eqb TLetterOne TLetterOne := true;
  derive_eqb (TPlusLeft _ d1) (TPlusLeft _ d2) := derive_eqb d1 d2;
  derive_eqb (TPlusRight _ d1) (TPlusRight _ d2) := derive_eqb d1 d2;
  derive_eqb (TTimesPre _ d1) (TTimesPre _ d2) := derive_eqb d1 d2;
  derive_eqb (TTimesPost _ d1) (TTimesPost _ d2) := derive_eqb d1 d2;
  derive_eqb (TStarOne _) (TStarOne _) := true;
  derive_eqb (TStarInner _ d1) (TStarInner _ d2) := derive_eqb d1 d2;
  derive_eqb _ _ := false;
}.

Lemma derive_eqb_correct (t: term) (d1 d2: derivative t):
  derive_eqb d1 d2 = true <-> d1 = d2
.
Proof.
  dependent induction t;
  dependent destruction d1;
  dependent destruction d2;
  autorewrite with derive_eqb;
  try easy.
  - rewrite IHt1.
    split; intros.
    + now subst.
    + apply Eqdep.EqdepTheory.inj_pair2.
      now inversion H0.
  - rewrite IHt2.
    split; intros.
    + now subst.
    + apply Eqdep.EqdepTheory.inj_pair2.
      now inversion H0.
  - rewrite IHt1.
    split; intros.
    + now subst.
    + apply Eqdep.EqdepTheory.inj_pair2.
      now inversion H0.
  - rewrite IHt2.
    split; intros.
    + now subst.
    + apply Eqdep.EqdepTheory.inj_pair2.
      now inversion H0.
  - rewrite IHt.
    split; intros.
    + now subst.
    + apply Eqdep.EqdepTheory.inj_pair2.
      now inversion H0.
Qed.

(* From Leapfrog *)
Lemma NoDup_app :
  forall A (l l': list A),
    NoDup l ->
    NoDup l' ->
    (forall x, In x l -> ~ In x l') ->
    (forall x, In x l' -> ~ In x l) ->
    NoDup (l ++ l').
Proof.
  induction l; destruct l'; simpl; autorewrite with list; auto.
  intros.
  constructor.
  + intro.
    inversion H0; subst.
    apply in_app_or in H4.
    destruct H4; auto.
    eapply H3; eauto with datatypes.
  + eapply IHl; eauto with datatypes.
    * inversion H0; auto.
    * intuition eauto with datatypes.
Qed.

(* From Leapfrog *)
Lemma NoDup_map:
  forall A B (f: A -> B) l,
    (forall x y, f x = f y -> x = y) ->
    NoDup l ->
    NoDup (map f l).
Proof.
  intros.
  induction l; simpl; constructor.
  - intro Hin.
    apply in_map_iff in Hin.
    destruct Hin as [x [Heq Hin]].
    apply H0 in Heq.
    subst.
    inversion H1.
    congruence.
  - inversion H1.
    eauto.
Qed.

Program Instance: forall t, Finite (derivative t).
Next Obligation.
  apply derive_list.
Defined.
Next Obligation.
  destruct (derive_eqb x1 x2) eqn:?.
  - left; now apply derive_eqb_correct.
  - right.
    contradict Heqb.
    apply Bool.not_false_iff_true.
    now apply derive_eqb_correct.
Qed.
Next Obligation.
  unfold Finite_instance_0_obligation_1.
  dependent induction x;
  autorewrite with derive_list.
  - now left.
  - now left.
  - right; now left.
  - apply in_app_iff; left.
    apply in_map_iff; now exists x.
  - apply in_app_iff; right.
    apply in_map_iff; now exists x.
  - apply in_app_iff; left.
    apply in_map_iff; now exists x.
  - apply in_app_iff; right.
    apply in_map_iff; now exists x.
  - right.
    apply in_map_iff; now exists x.
  - now left.
Qed.
Next Obligation.
  unfold Finite_instance_0_obligation_1.
  dependent induction t;
  autorewrite with derive_list.
  - constructor.
  - constructor; auto.
    constructor.
  - constructor.
    + intro.
      destruct H0; auto.
      discriminate.
    + constructor; auto.
      constructor.
  - apply NoDup_app.
    + apply NoDup_map; auto; intros.
      apply Eqdep.EqdepTheory.inj_pair2.
      now inversion H0.
    + apply NoDup_map; auto; intros.
      apply Eqdep.EqdepTheory.inj_pair2.
      now inversion H0.
    + intros; intro.
      apply in_map_iff in H0, H1.
      destruct H0 as [d1 [? ?]].
      destruct H1 as [d2 [? ?]].
      subst.
      discriminate.
    + intros; intro.
      apply in_map_iff in H0, H1.
      destruct H0 as [d1 [? ?]].
      destruct H1 as [d2 [? ?]].
      subst.
      discriminate.
  - apply NoDup_app.
    + apply NoDup_map; auto; intros.
      apply Eqdep.EqdepTheory.inj_pair2.
      now inversion H0.
    + apply NoDup_map; auto; intros.
      apply Eqdep.EqdepTheory.inj_pair2.
      now inversion H0.
    + intros; intro.
      apply in_map_iff in H0, H1.
      destruct H0 as [d1 [? ?]].
      destruct H1 as [d2 [? ?]].
      subst.
      discriminate.
    + intros; intro.
      apply in_map_iff in H0, H1.
      destruct H0 as [d1 [? ?]].
      destruct H1 as [d2 [? ?]].
      subst.
      discriminate.
  - constructor.
    + intro.
      apply in_map_iff in H0.
      destruct H0 as [d [? ?]].
      discriminate.
    + apply NoDup_map; auto; intros.
      apply Eqdep.EqdepTheory.inj_pair2.
      now inversion H0.
Qed.

Definition automaton_antimirov (t: term) : automaton (derivative t) := {|
  aut_transitions a d1 d2 := derive_b a d1 d2;
  aut_accept := nullable_b;
|}.

Record term_homomorphism (t1 t2: term) := {
  term_homomorphism_automaton_homomorphism :>
    automaton_homomorphism (automaton_antimirov t1)
                           (automaton_antimirov t2);
  term_homomorphism_preserve_initial:
    forall (d1: derivative t1),
    initial d1 ->
    initial (term_homomorphism_automaton_homomorphism d1)
}.

Equations term_homomorphism_assoc_f
  {t1 t2 t3: term}
  (d: derivative (t1 ;; (t2 ;; t3)))
  : derivative ((t1 ;; t2) ;; t3)
:= {
  term_homomorphism_assoc_f (TTimesPre _ d) :=
    TTimesPre _ (TTimesPre _ d);
  term_homomorphism_assoc_f (TTimesPost _ (TTimesPre _ d)) :=
    TTimesPre _ (TTimesPost _ d);
  term_homomorphism_assoc_f (TTimesPost _ (TTimesPost _ d)) :=
    TTimesPost _ d;
}.

Program Definition term_homomorphism_assoc (t1 t2 t3: term):
  term_homomorphism (t1 ;; (t2 ;; t3)) ((t1 ;; t2) ;; t3)
:= {|
  term_homomorphism_automaton_homomorphism := {|
    automaton_homomorphism_f := term_homomorphism_assoc_f;
  |};
|}.
Next Obligation.
  apply derive_dec in H0.
  apply derive_dec.
  dependent destruction H0.
  - autorewrite with term_homomorphism_assoc_f.
    now repeat constructor.
  - dependent destruction H2;
    autorewrite with term_homomorphism_assoc_f.
    + dependent destruction H1.
      constructor.
      now apply DeriveTimesJump with (i := d11).
    + dependent destruction H1.
      apply DeriveTimesJump with (i := i0); auto.
      now apply NullableTimesPre with (d2 := d0).
    + dependent destruction H1.
  - dependent destruction H0;
    autorewrite with term_homomorphism_assoc_f.
    + now repeat constructor.
    + apply DeriveTimesJump with (i := i); auto.
      now constructor.
    + now constructor.
Qed.
Next Obligation.
  apply nullable_dec in H0.
  apply nullable_dec.
  dependent destruction q1.
  - dependent destruction H0.
    autorewrite with term_homomorphism_assoc_f.
    dependent destruction d2.
    dependent destruction H0_0.
    dependent destruction H1.
    + eapply NullableTimesPre with (d2 := d0); auto.
      now apply NullableTimesPre with (d2 := d2).
    + dependent destruction H0.
  - dependent destruction H0.
    dependent destruction q1.
    + autorewrite with term_homomorphism_assoc_f.
      dependent destruction H0.
      eapply NullableTimesPre with (d2 := d2); auto.
      now constructor.
    + autorewrite with term_homomorphism_assoc_f.
      dependent destruction H0.
      now constructor.
Qed.
Next Obligation.
  dependent destruction H0.
  autorewrite with term_homomorphism_assoc_f.
  now repeat constructor.
Qed.

Equations term_homomorphism_roll_f
  {t: term}
  (d: derivative (t ;; t* + 1))
  : derivative (t*)
:= {
  term_homomorphism_roll_f (TPlusRight _ TOneOne) := TStarOne _;
  term_homomorphism_roll_f (TPlusLeft _ (TTimesPre _ d)) := TStarInner _ d;
  term_homomorphism_roll_f (TPlusLeft _ (TTimesPost _ d)) := d;
}.

Program Definition term_homomorphism_roll (t: term):
  term_homomorphism (t ;; t* + 1) (t*)
:= {|
  term_homomorphism_automaton_homomorphism := {|
    automaton_homomorphism_f := term_homomorphism_roll_f;
  |};
|}.
Next Obligation.
  apply derive_dec in H0.
  apply derive_dec.
  dependent destruction H0.
  - dependent destruction H0;
    autorewrite with term_homomorphism_roll_f.
    + now constructor.
    + dependent destruction H2.
      * dependent destruction H1.
        now apply DeriveStarInnerJump with (i := d0).
      * dependent destruction H1.
        now apply DeriveStarInnerJump with (i := i0).
    + assumption.
  - dependent destruction H0.
Qed.
Next Obligation.
  apply nullable_dec in H0.
  apply nullable_dec.
  dependent destruction H0.
  - dependent destruction H0;
    autorewrite with term_homomorphism_roll_f.
    + now constructor.
    + assumption.
  - dependent destruction H0.
    autorewrite with term_homomorphism_roll_f.
    constructor.
Qed.
Next Obligation.
  dependent destruction H0.
  - dependent destruction H0.
    autorewrite with term_homomorphism_roll_f.
    now constructor.
  - dependent destruction H0.
    autorewrite with term_homomorphism_roll_f.
    now constructor.
Qed.

Record automaton_solution
  {Q: Type}
  (aut: automaton Q)
  (scale: term)
  (sol: vector Q)
:= {
  automaton_solution_move:
    forall (a: A) (q1 q2: Q),
    aut_transitions aut a q1 q2 = true ->
    $a ;; sol q2 <= sol q1;
  automaton_solution_halt:
    forall (q: Q),
    aut_accept aut q = true ->
    scale <= sol q;
}.

Record automaton_least_solution
  {Q: Type}
  (aut: automaton Q)
  (scale: term)
  (sol: vector Q)
:= {
  automaton_least_solution_solution:
    automaton_solution aut scale sol;
  automaton_least_solution_least:
    forall (sol': vector Q),
    automaton_solution aut scale sol' ->
    sol <== sol'
}.

Require Import Coq.Program.Basics.
Open Scope program_scope.

Lemma automaton_homomorphism_solution
  {Q1 Q2: Type}
  (aut1: automaton Q1)
  (aut2: automaton Q2)
  (scale: term)
  (sol: vector Q2)
  (h: automaton_homomorphism aut1 aut2)
:
  automaton_solution aut2 scale sol ->
  automaton_solution aut1 scale (sol ∘ h)
.
Proof.
  split; intros.
  - unfold compose; simpl.
    apply H0 with (q1 := h q1).
    now apply h.
  - unfold compose; simpl.
    apply H0.
    now apply h.
Qed.

Lemma automaton_homomorphism_least_solution
  {Q1 Q2: Type}
  (aut1: automaton Q1)
  (aut2: automaton Q2)
  (scale: term)
  (sol1: vector Q1)
  (sol2: vector Q2)
  (h: automaton_homomorphism aut1 aut2)
:
  automaton_least_solution aut1 scale sol1 ->
  automaton_least_solution aut2 scale sol2 ->
  sol1 <== sol2 ∘ h
.
Proof.
  intros.
  apply H0.
  apply automaton_homomorphism_solution.
  apply H1.
Qed.

Definition automaton_to_system
  {Q: Type}
  (aut: automaton Q)
:= {|
  smat q q' :=
    sum (map letter (filter (fun a => aut_transitions aut a q q') finite_enum));
  svec q :=
    if aut_accept aut q then 1 else 0;
|}.

Lemma sum_lequiv_member
  (t: term)
  (l: list term)
:
  In t l ->
  t <= sum l
.
Proof.
  intros; induction l; destruct H0.
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
    + apply H0.
      now left.
    + apply IHl; intros.
      apply H0.
      now right.
Qed.

Lemma system_solution_to_automaton_solution
  {Q: Type}
  (aut: automaton Q)
  (scale: term)
  (sol: vector Q)
:
  solution (automaton_to_system aut) scale sol ->
  automaton_solution aut scale sol
.
Proof.
  intros.
  split; intros.
  - match goal with
    | |- ?lhs <= ?rhs => fold (term_lequiv lhs rhs)
    end.
    enough (term_lequiv ($ a) (smat (automaton_to_system aut) q1 q2)).
    + rewrite H2.
      unfold term_lequiv.
      apply H0.
    + unfold term_lequiv; simpl.
      apply sum_lequiv_member.
      apply in_map_iff.
      exists a.
      split; auto.
      apply filter_In.
      split; auto.
      apply finite_cover.
  - enough (svec (automaton_to_system aut) q == 1).
    + rewrite <- ETimesUnitLeft with (t := scale).
      rewrite <- H2.
      apply H0.
    + simpl.
      now rewrite H1.
Qed.

Lemma automaton_solution_to_system_solution
  {Q: Type}
  (aut: automaton Q)
  (scale: term)
  (sol: vector Q)
:
  automaton_solution aut scale sol ->
  solution (automaton_to_system aut) scale sol
.
Proof.
  intros.
  split; intros.
  - simpl.
    rewrite <- sum_distribute_right.
    apply sum_lequiv_all; intros.
    rewrite map_map in H1.
    apply in_map_iff in H1.
    destruct H1 as [a [? ?]].
    subst.
    apply filter_In in H2.
    destruct H2 as [_ ?].
    apply H0.
    apply H1.
  - simpl.
    destruct (aut_accept aut q) eqn:?.
    + rewrite ETimesUnitLeft.
      now apply H0.
    + rewrite ETimesZeroRight.
      apply term_lequiv_zero.
Qed.

Definition compute_automaton_solution
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
:
  vector Q
:=
  compute_solution (automaton_to_system aut)
.

Lemma compute_automaton_solution_least_solution
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (scale: term)
:
  automaton_least_solution aut scale (compute_automaton_solution aut ;;; scale)
.
Proof.
  split; intros.
  - unfold compute_automaton_solution.
    apply system_solution_to_automaton_solution.
    apply compute_solution_least_solution.
  - unfold compute_automaton_solution.
    apply compute_solution_least_solution.
    now apply automaton_solution_to_system_solution.
Qed.

Definition antimirov_solution (t: term): vector (derivative t) :=
  compute_automaton_solution (automaton_antimirov t)
.

Definition term_roundtrip (t: term) : term :=
  sum (map (antimirov_solution t) (initial_l t))
.

Lemma initial_cover (t: term) (d: derivative t):
  initial d ->
  derivative_write d <= t
.
Proof.
  intros.
  eapply term_lequiv_trans.
  + apply sum_lequiv_member.
    apply in_map_iff.
    eexists; split; auto.
    now apply initial_list.
  + rewrite <- initial_reconstruct.
    apply term_lequiv_refl.
Qed.

Lemma nullable_one (t: term) (d: derivative t):
  nullable d ->
  1 <= derivative_write d
.
Proof.
  intros.
  dependent induction H0;
  autorewrite with derivative_write;
  auto.
  - apply term_lequiv_refl.
  - apply term_lequiv_refl.
  - rewrite <- ETimesUnitRight with (t := 1).
    apply times_mor_mono.
    + apply IHnullable1.
    + eapply term_lequiv_trans.
      * apply IHnullable2.
      * now apply initial_cover.
  - rewrite <- ETimesUnitRight with (t := 1).
    apply times_mor_mono.
    + apply IHnullable.
    + eapply term_lequiv_trans.
      * apply term_lequiv_split_right.
        apply term_lequiv_refl.
      * rewrite EStarLeft.
        apply term_lequiv_refl.
  - apply term_lequiv_refl.
Qed.

Lemma antimirov_solution_upper_bound (t: term):
  antimirov_solution t <== derivative_write
.
Proof.
  unfold antimirov_solution.
  intro d.
  rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
  apply compute_automaton_solution_least_solution.
  split; intros.
  - simpl in H0.
    apply derive_dec in H0.
    dependent induction t;
    dependent destruction q1;
    dependent destruction q2;
    dependent destruction H0;
    autorewrite with derivative_write.
    + rewrite ETimesUnitRight.
      apply term_lequiv_refl.
    + now apply IHt1.
    + now apply IHt2.
    + rewrite ETimesAssoc.
      apply times_mor_mono; auto.
      apply term_lequiv_refl.
    + eapply term_lequiv_trans.
      * now apply IHt2 with (q1 := i).
      * rewrite <- ETimesUnitLeft with (t := derivative_write i).
        apply times_mor_mono.
        -- now apply nullable_one.
        -- now apply initial_cover.
    + now apply IHt2.
    + rewrite ETimesAssoc.
      apply times_mor_mono; auto.
      apply term_lequiv_refl.
    + eapply term_lequiv_trans with (t2 := t*).
      * rewrite ETimesAssoc.
        rewrite EStarLeft at 2.
        rewrite EStarLeft at 3.
        apply term_lequiv_split_left.
        apply times_mor_mono.
        -- eapply term_lequiv_trans.
           ++ now apply IHt with (q1 := i).
           ++ now apply initial_cover.
        -- apply term_lequiv_refl.
      * rewrite <- ETimesUnitLeft with (t := t*).
        apply times_mor_mono.
        -- now apply nullable_one.
        -- now rewrite <- ETimesUnitLeft with (t := t*) at 1.
  - simpl in H0.
    apply nullable_one.
    now apply nullable_dec.
Qed.

 Lemma term_roundtrip_upper_bound (t: term):
   term_roundtrip t <= t
.
Proof.
  unfold term_roundtrip.
  apply sum_lequiv_all; intros.
  apply in_map_iff in H0.
  destruct H0 as [d [? ?]].
  subst.
  eapply term_lequiv_trans.
  - apply antimirov_solution_upper_bound.
  - apply initial_cover.
    now apply initial_list.
Qed.

Lemma automaton_solution_invariant
  {Q: Type}
  (aut: automaton Q)
  (scale: term)
  (sol: vector Q)
:
  automaton_solution aut scale sol <->
  automaton_solution aut scale (sol ;;; 1)
.
Proof.
  split; intros.
  - split; intros.
    + unfold vector_scale.
      repeat rewrite ETimesUnitRight.
      now apply H0.
    + unfold vector_scale.
      rewrite ETimesUnitRight.
      now apply H0.
  - split; intros.
    + unfold vector_scale.
      rewrite <- ETimesUnitRight with (t := sol q2).
      rewrite <- ETimesUnitRight with (t := sol q1).
      now apply H0.
    + unfold vector_scale.
      rewrite <- ETimesUnitRight with (t := sol q).
      now apply H0.
Qed.

Lemma automaton_least_solution_invariant
  {Q: Type}
  (aut: automaton Q)
  (scale: term)
  (sol: vector Q)
:
  automaton_least_solution aut scale sol <->
  automaton_least_solution aut scale (sol ;;; 1)
.
Proof.
  split; intros.
  - split; intros.
    + rewrite <- automaton_solution_invariant.
      apply H0.
    + intro q; unfold vector_scale.
      rewrite ETimesUnitRight.
      now apply H0.
  - split; intros.
    + rewrite automaton_solution_invariant.
      apply H0.
    + intro q.
      rewrite <- ETimesUnitRight with (t := sol q).
      now apply H0.
Qed.

Lemma antimirov_solution_homomorphism
  (t1 t2: term)
  (h: automaton_homomorphism (automaton_antimirov t1) (automaton_antimirov t2))
:
  antimirov_solution t1 <== antimirov_solution t2 ∘ h
.
Proof.
  unfold antimirov_solution.
  intro.
  rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
  apply compute_automaton_solution_least_solution.
  apply automaton_homomorphism_solution.
  apply automaton_solution_invariant.
  apply compute_automaton_solution_least_solution.
Qed.

Lemma term_roundtrip_homomorphism
  (t1 t2: term) (h: term_homomorphism t1 t2)
:
  term_roundtrip t1 <= term_roundtrip t2
.
Proof.
  unfold term_roundtrip.
  apply sum_lequiv_all; intros.
  apply in_map_iff in H0.
  destruct H0 as [d [? ?]]; subst.
  apply term_lequiv_trans with (t2 := antimirov_solution t2 (h d)).
  - apply antimirov_solution_homomorphism.
  - apply sum_lequiv_member.
    apply in_map_iff.
    eexists; split; auto.
    apply initial_list, h.
    now apply initial_list.
Qed.

Lemma term_roundtrip_assoc (t1 t2 t3: term):
  term_roundtrip (t1 ;; (t2 ;; t3)) <= term_roundtrip ((t1 ;; t2) ;; t3)
.
Proof.
  apply term_roundtrip_homomorphism.
  apply term_homomorphism_assoc.
Qed.

Lemma term_roundtrip_roll (t: term):
  term_roundtrip (t ;; t* + 1) <= term_roundtrip (t*)
.
Proof.
  apply term_roundtrip_homomorphism.
  apply term_homomorphism_roll.
Qed.

Equations translate_unit_right
  {t: term}
  (s: vector (derivative t))
  (d: derivative (t ;; 1))
:
  term
:= {
  translate_unit_right s (TTimesPre _ d) := s d;
  translate_unit_right s (TTimesPost _ TOneOne) := 1;
}.

Lemma term_roundtrip_unit_right (t: term):
  term_roundtrip (t ;; 1) <= term_roundtrip t
.
Proof.
  unfold term_roundtrip.
  apply sum_lequiv_all; intros.
  apply in_map_iff in H0.
  destruct H0 as [d [? ?]]; subst.
  dependent destruction d.
  - apply term_lequiv_trans with (t2 := antimirov_solution t d).
    + clear H1.
      replace (antimirov_solution t d)
        with (translate_unit_right (antimirov_solution t) (TTimesPre _ d))
        by reflexivity.
      rewrite <- ETimesUnitRight with (t := antimirov_solution _ _).
      apply compute_automaton_solution_least_solution.
      split; intros.
      * simpl in H0.
        apply derive_dec in H0.
        dependent destruction H0.
        -- autorewrite with translate_unit_right.
           rewrite <- ETimesUnitRight with (t := antimirov_solution t d12).
           rewrite <- ETimesUnitRight with (t := antimirov_solution t d11).
           apply compute_automaton_solution_least_solution; auto.
           simpl; now apply derive_dec.
        -- dependent destruction H2.
        -- dependent destruction H0.
      * simpl in H0.
        apply nullable_dec in H0.
        dependent destruction H0.
        -- autorewrite with translate_unit_right.
           rewrite <- ETimesUnitRight with (t := antimirov_solution t d1).
           apply compute_automaton_solution_least_solution; auto.
           simpl; now apply nullable_dec.
        -- dependent destruction d2.
           autorewrite with translate_unit_right.
           apply term_lequiv_refl.
    + apply sum_lequiv_member.
      apply in_map_iff.
      exists d; split; auto.
      apply initial_list in H1.
      apply initial_list.
      now dependent destruction H1.
  - apply initial_list in H1.
    dependent destruction H1.
Qed.

Program Definition term_homomorphism_inject_left
  (t1 t2: term)
:
  term_homomorphism t1 (t1 + t2)
:= {|
  term_homomorphism_automaton_homomorphism := {|
    automaton_homomorphism_f d := TPlusLeft _ d;
  |};
|}.
Next Obligation.
  now constructor.
Qed.

Lemma term_roundtrip_sum_split_left (t1 t2: term):
  term_roundtrip t1 <= term_roundtrip (t1 + t2)
.
Proof.
  apply term_roundtrip_homomorphism.
  apply term_homomorphism_inject_left.
Qed.

Program Definition term_homomorphism_inject_right
  (t1 t2: term)
:
  term_homomorphism t2 (t1 + t2)
:= {|
  term_homomorphism_automaton_homomorphism := {|
    automaton_homomorphism_f d := TPlusRight _ d;
  |};
|}.
Next Obligation.
  now constructor.
Qed.

Lemma term_roundtrip_sum_split_right (t1 t2: term):
  term_roundtrip t2 <= term_roundtrip (t1 + t2)
.
Proof.
  apply term_roundtrip_homomorphism.
  apply term_homomorphism_inject_right.
Qed.

Equations term_homomorphism_distribute_left_f
  {t1 t2 t3: term}
  (d: derivative (t1 ;; t3 + t2 ;; t3))
  : derivative ((t1 + t2) ;; t3)
:= {
  term_homomorphism_distribute_left_f (TPlusLeft _ (TTimesPre _ d)) :=
    TTimesPre _ (TPlusLeft _ d);
  term_homomorphism_distribute_left_f (TPlusLeft _ (TTimesPost _ d)) :=
    TTimesPost _ d;
  term_homomorphism_distribute_left_f (TPlusRight _ (TTimesPre _ d)) :=
    TTimesPre _ (TPlusRight _ d);
  term_homomorphism_distribute_left_f (TPlusRight _ (TTimesPost _ d)) :=
    TTimesPost _ d;
}.

Program Definition term_homomorphism_distribute_left
  (t1 t2 t3: term)
:
  term_homomorphism (t1 ;; t3 + t2 ;; t3) ((t1 + t2) ;; t3)
:= {|
  term_homomorphism_automaton_homomorphism := {|
    automaton_homomorphism_f := term_homomorphism_distribute_left_f;
  |};
|}.
Next Obligation.
  apply derive_dec in H0.
  apply derive_dec.
  dependent destruction H0.
  - dependent destruction H0;
    autorewrite with term_homomorphism_distribute_left_f.
    + now repeat constructor.
    + apply DeriveTimesJump with (i := i); auto.
      now constructor.
    + now constructor.
  - dependent destruction H0;
    autorewrite with term_homomorphism_distribute_left_f.
    + now repeat constructor.
    + apply DeriveTimesJump with (i := i); auto.
      now constructor.
    + now constructor.
Qed.
Next Obligation.
  apply nullable_dec.
  apply nullable_dec in H0.
  dependent destruction H0.
  - dependent destruction H0;
    autorewrite with term_homomorphism_distribute_left_f.
    + apply NullableTimesPre with (d2 := d2); auto.
      now constructor.
    + now constructor.
  - dependent destruction H0;
    autorewrite with term_homomorphism_distribute_left_f.
    + apply NullableTimesPre with (d2 := d2); auto.
      now constructor.
    + now constructor.
Qed.
Next Obligation.
  dependent destruction H0.
  - dependent destruction H0;
    autorewrite with term_homomorphism_distribute_left_f.
    now repeat constructor.
  - dependent destruction H0;
    autorewrite with term_homomorphism_distribute_left_f.
    now repeat constructor.
Qed.

Lemma term_roundtrip_distribute_left (t1 t2 t3: term):
  term_roundtrip (t1 ;; t3 + t2 ;; t3) <= term_roundtrip ((t1 + t2) ;; t3)
.
Proof.
  apply term_roundtrip_homomorphism.
  apply term_homomorphism_distribute_left.
Qed.

Definition automaton_perturb
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (scale: term)
  (s: vector Q)
  (q: Q)
:
  term
:=
  (if aut_accept aut q then scale else 0) +
  sum (map (fun q' =>
      sum (map (fun a =>
          if aut_transitions aut a q q'
          then $a ;; s q' else 0
      ) finite_enum)
  ) finite_enum)
.

Lemma automaton_perturb_mono
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (scale: term)
  (s1 s2: vector Q)
:
  s1 <== s2 ->
  automaton_perturb aut scale s1 <== automaton_perturb aut scale s2
.
Proof.
  intros; intro q.
  unfold automaton_perturb.
  apply term_lequiv_split.
  - apply term_lequiv_split_left.
    apply term_lequiv_refl.
  - apply term_lequiv_split_right.
    apply sum_lequiv_all; intros.
    apply in_map_iff in H2.
    destruct H2 as [q' [? ?]]; subst.
    eapply term_lequiv_trans; swap 1 2.
    + eapply sum_lequiv_member.
      apply in_map_iff.
      exists q'.
      split; auto.
    + apply sum_lequiv_all; intros.
      apply in_map_iff in H2.
      destruct H2 as [a [? ?]]; subst.
      destruct (aut_transitions aut a q q') eqn:?.
      * eapply term_lequiv_trans; swap 1 2.
        -- apply sum_lequiv_member.
           apply in_map_iff.
           exists a.
           split; auto.
        -- rewrite Heqb.
           apply times_mor_mono.
           ++ apply term_lequiv_refl.
           ++ apply H1.
      * apply term_lequiv_zero.
Qed.

Lemma automaton_solution_perturb
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (scale: term)
  (sol: vector Q)
:
  automaton_solution aut scale sol <->
  automaton_perturb aut scale sol <== sol
.
Proof.
  split; intros.
  - intro q.
    unfold vector_scale.
    unfold automaton_perturb.
    apply term_lequiv_split.
    + destruct (aut_accept aut q) eqn:?.
      * now apply H1.
      * apply term_lequiv_zero.
    + apply sum_lequiv_all; intros.
      apply in_map_iff in H2.
      destruct H2 as [q' [? ?]]; subst.
      apply sum_lequiv_all; intros.
      apply in_map_iff in H2.
      destruct H2 as [a [? ?]]; subst.
      destruct (aut_transitions aut a q q') eqn:?.
      * now apply H1.
      * apply term_lequiv_zero.
  - split; intros.
    + apply term_lequiv_trans with (t2 := automaton_perturb aut scale sol q1).
      * unfold automaton_perturb.
        apply term_lequiv_split_right.
        eapply term_lequiv_trans; swap 1 2.
        -- apply sum_lequiv_member.
           apply in_map_iff.
           eexists; split; auto.
           apply finite_cover.
        -- apply sum_lequiv_member.
           apply in_map_iff.
           exists a.
           rewrite H2.
           split; auto.
           apply finite_cover.
      * apply H1.
    + eapply term_lequiv_trans with (t2 := automaton_perturb aut scale sol q).
      * unfold automaton_perturb.
        apply term_lequiv_split_left.
        rewrite H2.
        apply term_lequiv_refl.
      * apply H1.
Qed.

Lemma automaton_solution_iterate
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (scale: term)
  (sol: vector Q)
:
  automaton_solution aut scale sol ->
  automaton_solution aut scale (automaton_perturb aut scale sol)
.
Proof.
  intros.
  apply automaton_solution_perturb.
  apply automaton_perturb_mono.
  now apply automaton_solution_perturb.
Qed.

Lemma automaton_solution_least_converse
  {Q: Type}
  `{Finite Q}
  (aut: automaton Q)
  (scale: term)
  (sol: vector Q)
  (q: Q)
:
  automaton_least_solution aut scale sol ->
  sol q == automaton_perturb aut scale sol q
.
Proof.
  intros.
  apply vector_lequiv_squeeze.
  - apply H1.
    apply automaton_solution_iterate.
    apply H1.
  - apply automaton_solution_perturb.
    apply H1.
Qed.

Lemma antimirov_solution_link
  (t1 t2: term)
  (d1: derivative t1)
  (d2: derivative t2)
:
  nullable d1 ->
  initial d2 ->
  antimirov_solution (t1 ;; t2) (TTimesPost _ d2) <=
  antimirov_solution (t1 ;; t2) (TTimesPre _ d1)
.
Proof.
  intros.
  rewrite automaton_solution_least_converse
    with (aut := automaton_antimirov (t1 ;; t2))
  by (apply automaton_least_solution_invariant;
      apply compute_automaton_solution_least_solution).
  rewrite automaton_solution_least_converse
    with (aut := automaton_antimirov (t1 ;; t2)) (q := (TTimesPre t2 d1))
    by (apply automaton_least_solution_invariant;
        apply compute_automaton_solution_least_solution).
  apply term_lequiv_split.
  - apply term_lequiv_split_left.
    simpl.
    destruct (nullable_b _) eqn:?.
    + simpl in Heqb.
      apply nullable_dec in Heqb.
      dependent destruction Heqb.
      assert (nullable_b (TTimesPre t2 d1) = true).
      * apply nullable_dec.
        now apply NullableTimesPre with (d2 := d2).
      * simpl.
        rewrite H2.
        apply term_lequiv_refl.
    + apply term_lequiv_zero.
  - apply sum_lequiv_all; intros.
    apply in_map_iff in H2.
    destruct H2 as [d3 [? ?]].
    subst.
    apply sum_lequiv_all; intros.
    apply in_map_iff in H2.
    destruct H2 as [a [? ?]].
    subst.
    apply term_lequiv_split_right.
    simpl.
    destruct (derive_b _ _ _) eqn:?.
    + apply derive_dec in Heqb.
      eapply term_lequiv_trans; swap 1 2.
      * apply sum_lequiv_member.
        apply in_map_iff.
        exists d3.
        split; auto.
      * apply sum_lequiv_member.
        apply in_map_iff.
        exists a.
        assert (derive_b a (TTimesPre t2 d1) d3 = true).
        -- apply derive_dec.
           dependent destruction Heqb.
           now apply DeriveTimesJump with (i := d2).
        -- now rewrite H2.
    + apply term_lequiv_zero.
Qed.

Program Definition automaton_homomorphism_prepend
  (t1 t2: term)
:
  automaton_homomorphism (automaton_antimirov t2)
                         (automaton_antimirov (t1 ;; t2))
:= {|
  automaton_homomorphism_f d := TTimesPost _ d;
|}.

Lemma antimirov_solution_prepend (t1 t2: term) (d: derivative t2):
  antimirov_solution t2 d <= antimirov_solution (t1 ;; t2) (TTimesPost _ d)
.
Proof.
  apply antimirov_solution_homomorphism
    with (h := automaton_homomorphism_prepend t1 t2).
Qed.

Lemma term_roundtrip_shift_unit (t: term):
  1 ;; term_roundtrip t <= term_roundtrip (1 ;; t)
.
Proof.
  rewrite ETimesUnitLeft.
  unfold term_roundtrip.
  apply sum_lequiv_all; intros.
  apply in_map_iff in H0.
  destruct H0 as [d [? ?]]; subst.
  autorewrite with initial_l.
  rewrite map_map; simpl.
  autorewrite with sum.
  repeat rewrite EPlusUnit.
  apply term_lequiv_trans
    with (t2 := antimirov_solution (1 ;; t) (TTimesPost _ d)).
  - apply antimirov_solution_prepend.
  - apply antimirov_solution_link.
    + constructor.
    + now apply initial_list.
Qed.

Lemma term_roundtrip_shift_letter (a: A) (t: term):
  $a ;; term_roundtrip t <= term_roundtrip ($a ;; t)
.
Proof.
  unfold term_roundtrip.
  rewrite <- sum_distribute_left.
  apply sum_lequiv_all; intros.
  rewrite map_map in H0.
  apply in_map_iff in H0.
  destruct H0 as [d [? ?]]; subst.
  autorewrite with initial_l.
  rewrite map_map; simpl.
  autorewrite with sum.
  repeat rewrite EPlusUnit.
  apply term_lequiv_trans
    with (t2 := $a ;; antimirov_solution ($a ;; t) (TTimesPre _ TLetterOne)).
  - apply times_mor_mono.
    + apply term_lequiv_refl.
    + unfold term_lequiv.
      apply term_lequiv_trans
        with (t2 := antimirov_solution ($a ;; t) (TTimesPost _ d)).
      * apply antimirov_solution_prepend.
      * apply antimirov_solution_link.
        -- constructor.
        -- now apply initial_list.
  - rewrite <- ETimesUnitRight
      with (t := antimirov_solution _ (TTimesPre _ TLetterOne)).
    rewrite <- ETimesUnitRight
      with (t := antimirov_solution _ (TTimesPre _ (TLetterLetter _))).
    apply compute_automaton_solution_least_solution; simpl.
    apply derive_dec.
    now repeat constructor.
Qed.

Equations term_homomorphism_fold_f
  {t: term}
  (d: derivative (t ;; t*))
  : derivative (t*)
:= {
  term_homomorphism_fold_f (TTimesPre _ d) := TStarInner _ d;
  term_homomorphism_fold_f (TTimesPost _ (TStarInner _ d)) := TStarInner _ d;
  term_homomorphism_fold_f (TTimesPost _ (TStarOne _)) := TStarOne _;
}.

Program Definition term_homomorphism_fold
  (t: term)
:
  term_homomorphism (t ;; t*) (t*)
:= {|
  term_homomorphism_automaton_homomorphism := {|
    automaton_homomorphism_f := term_homomorphism_fold_f;
  |};
|}.
Next Obligation.
  apply derive_dec.
  apply derive_dec in H0.
  dependent destruction H0.
  - autorewrite with term_homomorphism_fold_f.
    now constructor.
  - dependent destruction H2;
    autorewrite with term_homomorphism_fold_f.
    + dependent destruction H1.
      now apply DeriveStarInnerJump with (i := d0).
    + dependent destruction H1.
      now apply DeriveStarInnerJump with (i := i0).
  - dependent destruction H0;
    autorewrite with term_homomorphism_fold_f.
    + now constructor.
    + now apply DeriveStarInnerJump with (i := i).
Qed.
Next Obligation.
  apply nullable_dec.
  apply nullable_dec in H0.
  dependent destruction H0.
  - autorewrite with term_homomorphism_fold_f.
    now constructor.
  - dependent destruction H0;
    autorewrite with term_homomorphism_fold_f.
    + now constructor.
    + constructor.
Qed.
Next Obligation.
  dependent destruction H0.
  autorewrite with term_homomorphism_fold_f.
  now constructor.
Qed.

Lemma term_roundtrip_fold (t: term):
  term_roundtrip (t ;; t*) <= term_roundtrip (t*)
.
Proof.
  apply term_roundtrip_homomorphism.
  apply term_homomorphism_fold.
Qed.

Equations term_homomorphism_times_f
  {t1 t2 t3 t4: term}
  (h1: term_homomorphism t1 t2)
  (h2: term_homomorphism t3 t4)
  (d: derivative (t1 ;; t3))
:
  derivative (t2 ;; t4)
:= {
  term_homomorphism_times_f h1 h2 (TTimesPre _ d) := TTimesPre _ (h1 d);
  term_homomorphism_times_f h1 h2 (TTimesPost _ d) := TTimesPost _ (h2 d);
}.

Program Definition term_homomorphism_times
  {t1 t2 t3 t4: term}
  (h1: term_homomorphism t1 t2)
  (h2: term_homomorphism t3 t4)
:
  term_homomorphism (t1 ;; t3) (t2 ;; t4)
:= {|
  term_homomorphism_automaton_homomorphism := {|
    automaton_homomorphism_f := term_homomorphism_times_f h1 h2;
  |};
|}.
Next Obligation.
  destruct h1 as [h1a h1i].
  destruct h2 as [h2a h2i].
  apply derive_dec.
  apply derive_dec in H0.
  dependent destruction H0;
  autorewrite with term_homomorphism_times_f;
  simpl.
  - constructor.
    apply derive_dec.
    apply h1a; simpl.
    now apply derive_dec.
  - apply DeriveTimesJump with (i := h2a i); simpl.
    + apply nullable_dec.
      apply h1a; simpl.
      now apply nullable_dec.
    + now apply h2i.
    + apply derive_dec.
      apply h2a; simpl.
      now apply derive_dec.
  - constructor.
    apply derive_dec.
    apply h2a; simpl.
    now apply derive_dec.
Qed.
Next Obligation.
  destruct h1 as [h1a h1i].
  destruct h2 as [h2a h2i].
  apply nullable_dec.
  apply nullable_dec in H0.
  dependent destruction H0;
  autorewrite with term_homomorphism_times_f;
  simpl.
  - eapply NullableTimesPre with (d2 := h2a d2).
    + apply nullable_dec.
      apply h1a; simpl.
      now apply nullable_dec.
    + apply nullable_dec.
      apply h2a; simpl.
      now apply nullable_dec.
    + now apply h2i.
  - constructor.
    apply nullable_dec.
    apply h2a; simpl.
    now apply nullable_dec.
Qed.
Next Obligation.
  dependent destruction H0.
  autorewrite with term_homomorphism_times_f.
  constructor.
  now apply h1.
Qed.

Lemma term_roundtrip_times (t1 t2 t3 t4: term):
  term_homomorphism t1 t2 ->
  term_homomorphism t3 t4 ->
  term_roundtrip (t1 ;; t3) <= term_roundtrip (t2 ;; t4)
.
Proof.
  intros.
  apply term_roundtrip_homomorphism.
  now apply term_homomorphism_times.
Qed.

Program Definition term_homomorphism_identity
  (t: term)
:
  term_homomorphism t t
:= {|
  term_homomorphism_automaton_homomorphism := {|
    automaton_homomorphism_f := id;
  |};
|}.

Lemma term_roundtrip_nullable (t: term) (d: derivative t):
  initial d ->
  nullable d ->
  1 <= term_roundtrip t
.
Proof.
  intros.
  unfold term_roundtrip.
  apply term_lequiv_trans with (t2 := antimirov_solution t d).
  - rewrite <- ETimesUnitRight with (t := antimirov_solution t d).
    apply compute_automaton_solution_least_solution; auto.
    now apply nullable_dec.
  - apply sum_lequiv_member.
    apply in_map_iff.
    eexists; split; auto.
    now apply initial_list.
Qed.

Program Definition term_homomorphism_skip
  (t: term)
:
  term_homomorphism 1 (t*)
:= {|
  term_homomorphism_automaton_homomorphism := {|
    automaton_homomorphism_f _ := TStarOne _;
  |};
|}.
Next Obligation.
  apply derive_dec in H0.
  dependent destruction H0.
Qed.
Next Obligation.
  constructor.
Qed.

Lemma term_roundtrip_shift (t1 t2: term):
  t1 ;; term_roundtrip t2 <= term_roundtrip (t1 ;; t2)
.
Proof.
  revert t2; induction t1; intros.
  - rewrite ETimesZeroRight.
    apply term_lequiv_zero.
  - apply term_roundtrip_shift_unit.
  - apply term_roundtrip_shift_letter.
  - rewrite EDistributeRight.
    apply term_lequiv_trans
      with (t2 := term_roundtrip (t1_1 ;; t2 + t1_2 ;; t2)).
    + apply term_lequiv_split.
      * eapply term_lequiv_trans.
        -- apply IHt1_1.
        -- apply term_roundtrip_sum_split_left.
      * eapply term_lequiv_trans.
        -- apply IHt1_2.
        -- apply term_roundtrip_sum_split_right.
    + apply term_roundtrip_distribute_left.
  - eapply term_lequiv_trans.
    + rewrite <- ETimesAssoc.
      apply times_mor_mono.
      * apply term_lequiv_refl.
      * apply IHt1_2.
    + eapply term_lequiv_trans.
      * apply IHt1_1.
      * apply term_roundtrip_assoc.
  - apply EFixLeft.
    apply term_lequiv_split.
    + eapply term_lequiv_trans.
      * apply IHt1.
      * apply term_lequiv_trans
          with (t2 := term_roundtrip ((t1 ;; t1*) ;; t2)).
        -- apply term_roundtrip_assoc.
        -- apply term_roundtrip_times.
           ++ apply term_homomorphism_fold.
           ++ apply term_homomorphism_identity.
    + rewrite <- ETimesUnitLeft with (t := term_roundtrip t2).
      eapply term_lequiv_trans.
      apply term_roundtrip_shift_unit.
      apply term_roundtrip_times.
      * apply term_homomorphism_skip.
      * apply term_homomorphism_identity.
Qed.

Lemma term_roundtrip_one_lower:
  1 <= term_roundtrip 1
.
Proof.
  unfold term_roundtrip.
  eapply term_lequiv_trans with (t2 := antimirov_solution 1 TOneOne).
  - unfold antimirov_solution.
    rewrite <- ETimesUnitRight with (t := compute_automaton_solution _ _).
    apply compute_automaton_solution_least_solution.
    simpl.
    apply nullable_dec.
    constructor.
  - apply sum_lequiv_member.
    apply in_map_iff.
    eexists; split; auto.
    apply initial_list.
    constructor.
Qed.

Lemma term_roundtrip_lower_bound (t: term):
  t <= term_roundtrip t
.
Proof.
  rewrite <- ETimesUnitRight with (t := t) at 1.
  eapply term_lequiv_trans.
  - apply times_mor_mono.
    + apply term_lequiv_refl.
    + apply term_roundtrip_one_lower.
  - eapply term_lequiv_trans.
    + apply term_roundtrip_shift.
    + apply term_roundtrip_unit_right.
Qed.

Lemma term_roundtrip_invariant (t: term):
  t == term_roundtrip t
.
Proof.
  apply term_lequiv_squeeze.
  - apply term_roundtrip_lower_bound.
  - apply term_roundtrip_upper_bound.
Qed.

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
    + apply term_matches_star_split in H0.
      destruct H0 as [l [? ?]]; subst.
      induction l using rev_ind; simpl.
      * apply MatchPlusRight, MatchOne.
      * rewrite concat_app; simpl.
        rewrite app_nil_r.
        apply MatchPlusLeft, MatchTimes.
        apply term_matches_star_split.
        -- exists l; intuition.
        -- apply H1.
           apply in_app_iff.
           intuition.
    + dependent destruction H0.
      * dependent destruction H0.
        apply term_matches_star_split in H0_.
        destruct H0_ as [l [? ?]]; subst.
        apply term_matches_star_split.
        exists ((l ++ w2 :: nil)).
        split.
        -- rewrite concat_app.
           simpl.
           now rewrite app_nil_r.
        -- intros.
           apply in_app_iff in H0.
           destruct H0.
           ++ intuition.
           ++ destruct H0; intuition.
              now subst.
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
    pose proof (vector_scale_unit (Q := (prod (Q -> Q -> bool) (Q -> Q -> bool)))).
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
  monotone_bottom:
    f partial_order_zero = partial_order_zero;
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
  f x = x ->
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
    + rewrite H3.
      apply partial_order_refl.
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
  kleene_plus_commute:
    forall (x1 x2: X),
      kleene_plus x1 x2 = kleene_plus x2 x1;
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

Definition lift_multiplication
  {X: Type}
  `{Finite X}
  (M: monoid X)
  (xs1 xs2: X -> bool)
  (x: X)
:
  bool
:=
  disj (
    map (fun '(x1, x2) => finite_eqb x (monoid_compose M x1 x2)) (
      filter (fun '(x1, x2) => xs1 x1 && xs2 x2)
             (list_prod finite_enum finite_enum)
    )
  )
.

Lemma lift_multiplication_characterise
  {X: Type}
  `{Finite X}
  (M: monoid X)
  (x1 x2: X -> bool)
  (x: X)
:
  lift_multiplication M x1 x2 x = true <->
  exists (x1' x2': X),
    x1 x1' = true /\
    x2 x2' = true /\
    monoid_compose M x1' x2' = x
.
Proof.
  unfold lift_multiplication.
  rewrite disj_true, in_map_iff.
  split; intros.
  - destruct H1 as [(x1', x2') [? ?]].
    apply finite_eqb_eq in H1; subst.
    apply filter_In in H2.
    destruct H2 as [_ ?].
    apply Bool.andb_true_iff in H1.
    destruct H1 as [? ?].
    now exists x1', x2'.
  - destruct H1 as [x1' [x2' [? [? ?]]]].
    exists (x1', x2'); intuition.
    + now apply finite_eqb_eq.
    + apply filter_In; intuition.
      replace (list_prod finite_enum finite_enum)
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
  monoid_compose := lift_multiplication M;
  monoid_unit x := finite_eqb x (monoid_unit M);
|}.
Next Obligation.
  extensionality x.
  apply ZMicromega.eq_true_iff_eq.
  repeat rewrite lift_multiplication_characterise.
  split; intros.
  - destruct H1 as [x' [x3' [? [? ?]]]].
    apply lift_multiplication_characterise in H1.
    destruct H1 as [x1' [x2' [? [? ?]]]]; subst.
    exists x1', (monoid_compose M x2' x3'); intuition.
    + apply lift_multiplication_characterise.
      now exists x2', x3'.
    + now rewrite monoid_compose_assoc.
  - destruct H1 as [x1' [x' [? [? ?]]]].
    apply lift_multiplication_characterise in H2.
    destruct H2 as [x2' [x3' [? [? ?]]]]; subst.
    exists (monoid_compose M x1' x2'), x3'; intuition.
    apply lift_multiplication_characterise.
    now exists x1', x2'.
Qed.
