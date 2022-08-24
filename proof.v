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

Definition solution_nat
  {n: nat}
  (sys: system (position n))
  (sol: vector (position n))
:=
  smat sys <*> sol <+> svec sys <== sol
.

Lemma compute_solution_nat_solution_nat
  {n: nat}
  (sys: system (position n))
:
  solution_nat sys (compute_solution_nat sys)
.
Proof.
  unfold solution_nat; intro p.
  dependent induction p.
  - unfold vector_sum, matrix_vector_product.
    autorewrite with inner_product.
    autorewrite with compute_solution_nat; simpl.
    rewrite ETimesAssoc.
    rewrite <- EPlusAssoc with (t3 := svec sys PHere).
    rewrite EPlusComm with (t2 := svec sys PHere).
    rewrite <- ETimesUnitLeft with (t := _ + # _ ** # compute_solution_nat sys).
    rewrite compute_solution_nat_chomp.
    rewrite <- EDistributeRight.
    rewrite <- EStarLeft.
    apply term_lequiv_refl.
  - unfold vector_sum, matrix_vector_product.
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

Lemma compute_solution_nat_least
  {n: nat}
  (sys: system (position n))
  (sol: vector (position n))
:
  solution_nat sys sol ->
  compute_solution_nat sys <== sol
.
Proof.
  intros.
  dependent induction n; intro p; dependent destruction p.
  - autorewrite with compute_solution_nat; simpl.
    rewrite EPlusComm with (t1 := svec sys PHere).
    match goal with
    | |- ?lhs <= ?rhs => fold (term_lequiv lhs rhs)
    end.
    rewrite IHn with (sol := # sol).
    + now apply solution_bound.
    + now apply solution_project.
  - autorewrite with compute_solution_nat; simpl.
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

Lemma compute_solution_nat_least_solution
  {n: nat}
  (sys: system (position n))
:
  least_solution sys (compute_solution_nat sys)
.
Proof.
  split.
  - apply solution_iff_solution_nat.
    apply compute_solution_nat_solution_nat.
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
  (v: vector X)
:
  solution sys v ->
  solution (system_index sys) (vector_index v)
.
Proof.
  split; intros; simpl; apply H0.
Qed.

Lemma solution_nat_to_finite
  {X: Type}
  `{Finite X}
  (sys: system (position (length finite_enum)))
  (v: vector (position (length (finite_enum))))
:
  solution sys v ->
  solution (system_lookup sys) (vector_lookup v)
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
:
  solution sys (compute_solution sys)
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
:
  forall sol,
    solution sys sol ->
    compute_solution sys <== sol
.
Proof.
  intros.
  unfold compute_solution.
  apply vector_lequiv_adjunction.
  apply compute_solution_nat_least_solution.
  now apply solution_finite_to_nat.
Qed.

Lemma compute_solution_least_solution
  {X: Type}
  `{Finite X}
  (sys: system X)
:
  least_solution sys (compute_solution sys)
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
  (v1 v2: vector X)
:
  least_solution sys v1 ->
  least_solution sys v2 ->
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

Record automaton_solution_at
  {Q: Type}
  (aut: automaton Q)
  (sol: vector Q)
  (q: Q)
:= {
  automaton_solution_move:
    forall (a: A) (q1 q2: Q),
    aut_transitions aut a q1 q2 = true ->
    $a ;; sol q2 <= sol q1;
  automaton_solution_halt:
    forall (q: Q),
    aut_accept aut q = true ->
    1 <= sol q;
}.

Definition automaton_solution
  {Q: Type}
  (aut: automaton Q)
  (sol: vector Q)
:=
  forall (q: Q), automaton_solution_at aut sol q
.

Record automaton_least_solution
  {Q: Type}
  (aut: automaton Q)
  (sol: vector Q)
:= {
  automaton_least_solution_solution:
    automaton_solution aut sol;
  automaton_least_solution_least:
    forall (sol': vector Q),
    automaton_solution aut sol' ->
    sol <== sol'
}.

Require Import Coq.Program.Basics.
Open Scope program_scope.

Lemma automaton_homomorphism_solution
  {Q1 Q2: Type}
  (aut1: automaton Q1)
  (aut2: automaton Q2)
  (sol: vector Q2)
  (h: automaton_homomorphism aut1 aut2)
:
  automaton_solution aut2 sol ->
  automaton_solution aut1 (sol ∘ h)
.
Proof.
  split; intros.
  - unfold compose; simpl.
    apply (H0 (h q1)) with (q1 := h q1).
    now apply h.
  - unfold compose; simpl.
    apply (H0 (h q0)).
    now apply h.
Qed.

Lemma automaton_homomorphism_least_solution
  {Q1 Q2: Type}
  (aut1: automaton Q1)
  (aut2: automaton Q2)
  (sol1: vector Q1)
  (sol2: vector Q2)
  (h: automaton_homomorphism aut1 aut2)
:
  automaton_least_solution aut1 sol1 ->
  automaton_least_solution aut2 sol2 ->
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
  (sol: vector Q)
:
  solution (automaton_to_system aut) sol ->
  automaton_solution aut sol
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
  - enough (svec (automaton_to_system aut) q0 == 1).
    + rewrite <- H2.
      apply H0.
    + simpl.
      now rewrite H1.
Qed.

Lemma automaton_solution_to_system_solution
  {Q: Type}
  (aut: automaton Q)
  (sol: vector Q)
:
  automaton_solution aut sol ->
  solution (automaton_to_system aut) sol
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
    apply (H0 q).
    apply H1.
  - simpl.
    destruct (aut_accept aut q) eqn:?.
    + now apply (H0 q).
    + apply term_lequiv_zero.
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
:
  automaton_least_solution aut (compute_automaton_solution aut)
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
    apply nullable_dec in H0.
    dependent induction t;
    dependent destruction q0;
    dependent destruction H0;
    autorewrite with derivative_write.
    + apply term_lequiv_refl.
    + apply term_lequiv_refl.
    + now apply IHt1.
    + now apply IHt2.
    + rewrite <- ETimesUnitRight with (t := 1).
      apply times_mor_mono.
      * now apply IHt1.
      * eapply term_lequiv_trans.
        -- apply nullable_one.
           apply H0_0.
        -- now apply initial_cover.
    + now apply nullable_one.
    + rewrite <- ETimesUnitRight with (t := 1).
      apply times_mor_mono.
      * now apply nullable_one.
      * unfold term_lequiv.
        eapply term_lequiv_trans.
        -- apply term_lequiv_split_right.
           apply term_lequiv_refl.
        -- rewrite <- EStarLeft.
           apply term_lequiv_refl.
    + apply term_lequiv_refl.
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

Lemma antimirov_solution_homomorphism
  (t1 t2: term)
  (h: automaton_homomorphism (automaton_antimirov t1) (automaton_antimirov t2))
:
  antimirov_solution t1 <== antimirov_solution t2 ∘ h
.
Proof.
  unfold antimirov_solution.
  apply compute_automaton_solution_least_solution.
  apply automaton_homomorphism_solution.
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
      apply compute_automaton_solution_least_solution.
      split; intros.
      * simpl in H0.
        apply derive_dec in H0.
        dependent destruction H0.
        -- autorewrite with translate_unit_right.
           apply compute_automaton_solution_least_solution; auto.
           simpl; now apply derive_dec.
        -- dependent destruction H2.
        -- dependent destruction H0.
      * simpl in H0.
        apply nullable_dec in H0.
        dependent destruction H0.
        -- autorewrite with translate_unit_right.
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
  (s: vector Q)
  (q: Q)
:
  term
:=
  (if aut_accept aut q then 1 else 0) +
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
  (s1 s2: vector Q)
:
  s1 <== s2 ->
  automaton_perturb aut s1 <== automaton_perturb aut s2
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
  (sol: vector Q)
:
  automaton_solution aut sol <->
  automaton_perturb aut sol <== sol
.
Proof.
  split; intros.
  - intro q.
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
    + apply term_lequiv_trans with (t2 := automaton_perturb aut sol q1).
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
    + eapply term_lequiv_trans with (t2 := automaton_perturb aut sol q0).
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
  (sol: vector Q)
:
  automaton_solution aut sol ->
  automaton_solution aut (automaton_perturb aut sol)
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
  (sol: vector Q)
  (q: Q)
:
  automaton_least_solution aut sol ->
  sol q == automaton_perturb aut sol q
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
    by (apply compute_automaton_solution_least_solution).
  rewrite automaton_solution_least_converse
    with (aut := automaton_antimirov (t1 ;; t2)) (q := (TTimesPre t2 d1))
    by (apply compute_automaton_solution_least_solution).
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
  - apply compute_automaton_solution_least_solution.
    + exact (TTimesPost _ d).
    + simpl.
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
  - apply compute_automaton_solution_least_solution; auto.
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
    apply compute_automaton_solution_least_solution.
    + apply TOneOne.
    + simpl.
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
    finite_eqb (matrix_product_bool (aut_transitions aut a) m1) m2;
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

Lemma term_equiv_sound (t1 t2: term) (w: list A):
  t1 == t2 ->
  term_matches t1 w <-> term_matches t2 w
.
Proof.
Admitted.

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

Lemma matrix_product_bool_unit_left
  {Q: Type}
  `{Finite Q}
  (m: Q -> Q -> bool)
:
  matrix_product_bool finite_eqb m = m
.
Proof.
Admitted.

Lemma term_matches_sum (l: list term) (w: list A):
  term_matches (sum l) w ->
  exists (t: term),
    In t l /\ term_matches t w
.
Proof.
Admitted.

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
  matrix_product_bool (automaton_transition_matrix aut w) initial = final
.
Proof.
  intros.
  induction w.
  - split; intros.
    + rewrite term_equiv_sound
        with (t2 := automaton_perturb aut' sol' initial)
        in H1.
      * unfold automaton_perturb in H1.
        dependent destruction H1.
        -- unfold finite_eqb in H1.
           destruct (finite_dec initial final).
           ++ autorewrite with automaton_transition_matrix.
              subst.
              apply matrix_product_bool_unit_left.
           ++ dependent destruction H1.
        -- apply term_matches_sum in H1.
           destruct H1 as [t [? ?]].
           apply in_map_iff in H1.
           destruct H1 as [next [? ?]]; subst.
           apply term_matches_sum in H2.
           destruct H2 as [t [? ?]].
           apply in_map_iff in H1.
           destruct H1 as [a [? ?]]; subst.
           unfold finite_eqb in H2.
           destruct (finite_dec _ _).
           ++ now apply term_matches_prepend_letter in H2.
           ++ dependent destruction H2.
      * apply automaton_solution_least_converse.
        apply compute_automaton_solution_least_solution.
Admitted.

