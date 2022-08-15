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

Record solution_at
  {Q: Type}
  (sys: system Q)
  (sol: vector Q)
  (q: Q)
:= {
  solution_move: forall (q': Q), smat sys q q' ;; sol q' <= sol q;
  solution_bias: svec sys q <= sol q;
}.

Definition solution
  {Q: Type}
  (sys: system Q)
  (sol: vector Q)
:=
  forall (q: Q), solution_at sys sol q
.

Record least_solution
  {Q: Type}
  (sys: system Q)
  (sol: vector Q)
:= {
  least_solution_solution: solution sys sol;
  least_solution_least: forall sol', solution sys sol' -> sol <== sol'
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

Equations compute_solution
  {n: nat}
  (sys: system (position n))
  (p: position n)
  : term
:= {
  @compute_solution (S n) sys (PThere p) :=
    let smaller_solution := compute_solution (compress_system sys) in
    smaller_solution p;
  @compute_solution (S n) sys PHere :=
    let smaller_solution := compute_solution (compress_system sys) in
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

Lemma compute_solution_chomp
  {n: nat}
  (sys: system (position (S n)))
:
  # compute_solution sys === compute_solution (compress_system sys)
.
Proof.
  intro.
  unfold vector_chomp.
  now autorewrite with compute_solution; simpl.
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

Definition solution_nat
  {n: nat}
  (sys: system (position n))
  (sol: vector (position n))
:=
  smat sys <*> sol <+> svec sys <== sol
.

Lemma compute_solution_solution
  {n: nat}
  (sys: system (position n))
:
  solution_nat sys (compute_solution sys)
.
Proof.
  unfold solution_nat; intro p.
  dependent induction p.
  - unfold vector_sum, matrix_vector_product.
    autorewrite with inner_product.
    autorewrite with compute_solution; simpl.
    rewrite ETimesAssoc.
    rewrite <- EPlusAssoc with (t3 := svec sys PHere).
    rewrite EPlusComm with (t2 := svec sys PHere).
    rewrite <- ETimesUnitLeft with (t := _ + # _ ** # compute_solution sys).
    rewrite compute_solution_chomp.
    rewrite <- EDistributeRight.
    rewrite <- EStarLeft.
    apply term_lequiv_refl.
  - unfold vector_sum, matrix_vector_product.
    autorewrite with inner_product.
    autorewrite with compute_solution; simpl.
    rewrite ETimesAssoc.
    rewrite EDistributeLeft.
    rewrite compute_solution_chomp.
    rewrite vector_inner_product_scale_left.
    rewrite <- EPlusAssoc with (t1 := _ ;; svec sys PHere).
    rewrite vector_inner_product_distribute_left.
    rewrite compress_system_mat.
    rewrite EPlusComm with (t1 := _ ;; svec sys PHere).
    rewrite <- EPlusAssoc with (t3 := svec sys (PThere p)).
    rewrite EPlusComm with (t2 := svec sys (PThere p)) .
    rewrite compress_system_vec.
    apply IHp.
Qed.

Lemma solution_bound
  {n: nat}
  (sys: system (position (S n)))
  (sol: vector (position (S n)))
:
  solution_nat sys sol ->
  term_lequiv ((smat sys PHere PHere)* ;; (# smat sys PHere ** # sol + svec sys PHere)) (sol PHere)
.
Proof.
  intros.
  apply EFixLeft.
  rewrite EPlusAssoc.
  rewrite <- inner_product_equation_2.
  apply H.
Qed.

Lemma solution_project
  {n: nat}
  (sys: system (position (S n)))
  (sol: vector (position (S n)))
:
  solution_nat sys sol ->
  solution_nat (compress_system sys) (# sol)
.
Proof.
  intros; intro p.
  unfold vector_sum, matrix_vector_product.
  rewrite <- compress_system_mat.
  rewrite <- compress_system_vec.
  rewrite <- vector_inner_product_distribute_left.
  rewrite <- vector_inner_product_scale_left.
  rewrite EPlusComm with (t1 := svec sys (PThere p)).
  rewrite EPlusAssoc.
  rewrite <- EPlusAssoc with (t2 := # smat sys (PThere p) ** # sol).
  rewrite EPlusComm with (t1 := # smat sys (PThere p) ** # sol).
  rewrite EPlusAssoc.
  rewrite <- EDistributeLeft.
  rewrite <- ETimesAssoc.
  match goal with
  | |- ?lhs <= ?rhs => fold (term_lequiv lhs rhs)
  end.
  rewrite solution_bound; auto.
  rewrite <- inner_product_equation_2.
  apply H.
Qed.

Lemma compute_solution_least
  {n: nat}
  (sys: system (position n))
  (sol: vector (position n))
:
  solution_nat sys sol ->
  compute_solution sys <== sol
.
Proof.
  intros.
  dependent induction n; intro p; dependent destruction p.
  - autorewrite with compute_solution; simpl.
    rewrite EPlusComm with (t1 := svec sys PHere).
    match goal with
    | |- ?lhs <= ?rhs => fold (term_lequiv lhs rhs)
    end.
    rewrite IHn with (sol := # sol).
    + now apply solution_bound.
    + now apply solution_project.
  - autorewrite with compute_solution; simpl.
    eapply term_lequiv_trans.
    apply IHn.
    + apply solution_project.
      apply H.
    + unfold vector_chomp.
      now rewrite EPlusIdemp.
Qed.

Lemma solution_iff_solution_nat
  {n: nat}
  (sys: system (position n))
  (sol: vector (position n))
:
  solution sys sol <-> solution_nat sys sol
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
  - intro p; split; intros.
    + eapply term_lequiv_trans; [apply term_lequiv_split_left|].
      * apply term_lequiv_inner_product.
      * apply H.
    + eapply term_lequiv_trans; [apply term_lequiv_split_right|].
      * apply term_lequiv_refl.
      * apply H.
Qed.

Lemma compute_solution_least_solution
  {n: nat}
  (sys: system (position n))
:
  least_solution sys (compute_solution sys)
.
Proof.
  split.
  - apply solution_iff_solution_nat.
    apply compute_solution_solution.
  - setoid_rewrite solution_iff_solution_nat.
    apply compute_solution_least.
Qed.

Require Import Coq.Lists.List.

Class Finite (X: Type) := {
  finite_enum: list X;
  finite_dec: forall (x1 x2: X), {x1 = x2} + {x1 <> x2};
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
  (p: position (length (@finite_enum X _)))
:
  list_index (list_lookup p) = p
.
Proof.
  apply list_lookup_injective.
  now rewrite list_lookup_index.
Qed.
