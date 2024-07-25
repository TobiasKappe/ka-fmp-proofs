From Equations Require Import Equations.
Require Import Coq.Lists.List.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Coq.micromega.Lia.
Local Open Scope program_scope.

Require Import KA.Utilities.

Section FiniteDefinition.
  Class Finite (X: Type) := {
    finite_enum: list X;
    finite_dec: forall (x1 x2: X), {x1 = x2} + {x1 <> x2};
    finite_eqb x1 x2 := if finite_dec x1 x2 then true else false;
    finite_cover: forall x, In x finite_enum;
    finite_nodup: NoDup finite_enum;
  }.

  Lemma finite_eqb_eq (X: Type) `{Finite X} (x1 x2: X):
    finite_eqb x1 x2 = true <-> x1 = x2
  .
  Proof.
    unfold finite_eqb.
    now destruct (finite_dec _ _).
  Qed.
End FiniteDefinition.

Section FiniteIsomorphism.
  Inductive position: nat -> Type :=
  | PHere:
      forall {n: nat},
      position (S n)
  | PThere:
      forall {n: nat}
             (v: position n),
      position (S n)
  .

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
End FiniteIsomorphism.

Module FiniteBijection.
  Record bijection {X Y: Type} := {
    bijection_mapping :> X -> Y;
    bijection_inverse: Y -> X;
    bijection_injective:
      forall x1 x2,
        bijection_mapping x1 = bijection_mapping x2 ->
        x1 = x2;
    bijection_surjective:
      forall y, bijection_mapping (bijection_inverse y) = y
  }.
  Arguments bijection _ _ : clear implicits.

  Local Program Instance bijection_finite
    (X Y: Type)
    `{Finite X}
    (f: bijection X Y)
  :
    Finite Y
  := {|
    finite_enum := map f finite_enum
  |}.
  Next Obligation.
    destruct (finite_dec (bijection_inverse f x1) (bijection_inverse f x2)).
    - apply (f_equal (bijection_mapping f)) in e.
      repeat rewrite bijection_surjective in e.
      now left.
    - right; contradict n.
      now subst.
  Qed.
  Next Obligation.
    pose proof (bijection_surjective f).
    rewrite <- (H0 x).
    apply in_map_iff.
    eexists; intuition.
  Qed.
  Next Obligation.
    eapply NoDup_map_inv with (f := bijection_inverse f).
    rewrite map_map.
    rewrite map_ext with (g := id).
    - rewrite map_id.
      apply finite_nodup.
    - intros; unfold id; simpl.
      apply bijection_injective with (b := f).
      now rewrite bijection_surjective.
  Qed.
End FiniteBijection.

Section FiniteUtilities.
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
      inversion H; subst.
      apply in_app_or in H3.
      destruct H3; auto.
      eapply H2; eauto with datatypes.
    + eapply IHl; eauto with datatypes.
      * inversion H; auto.
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
      apply H in Heq.
      subst.
      inversion H0.
      congruence.
    - inversion H0.
      eauto.
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
        * specialize (H0 x).
          intuition congruence.
      + simpl.
        destruct (f a) eqn:?.
        * apply H0 in Heqb; congruence.
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
End FiniteUtilities.

Section FiniteSubset.
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
        now rewrite H.
      + apply NoDup_map; auto; intros.
        extensionality p.
        rewrite <- position_subset_glue_equation_2 with (f := x) (b := true) at 1.
        rewrite <- position_subset_glue_equation_2 with (f := y) (b := true).
        now rewrite H.
      + intros; intro.
        rewrite in_map_iff in H, H0.
        destruct H as [x0 [? ?]], H0 as [x1 [? ?]]; subst.
        apply Bool.diff_true_false.
        rewrite <- position_subset_glue_equation_1 with (f := x1) at 1.
        rewrite <- position_subset_glue_equation_1 with (f := x0).
        now rewrite H0.
      + intros; intro.
        rewrite in_map_iff in H, H0.
        destruct H as [x0 [? ?]], H0 as [x1 [? ?]]; subst.
        apply Bool.diff_true_false.
        rewrite <- position_subset_glue_equation_1 with (f := x0) at 1.
        rewrite <- position_subset_glue_equation_1 with (f := x1).
        now rewrite H0.
  Qed.

  Definition finite_subsets {X: Type} `{Finite X}: list (X -> bool) :=
    map (fun f x => f (list_index x)) (position_subsets (length (finite_enum)))
  .

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
      + destruct H.
        extensionality p.
        dependent destruction p.
        * now apply Bool.eqb_prop.
        * replace (f (PThere p)) with ((f ∘ PThere) p) by reflexivity.
          replace (g (PThere p)) with ((g ∘ PThere) p) by reflexivity.
          apply IHn in H0.
          now rewrite H0.
      + split; intros.
        * rewrite H.
          apply Bool.eqb_reflx.
        * apply IHn.
          now rewrite H.
  Qed.

  Global Program Instance finite_subsets_finite
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
      apply H0.
    - apply position_subsets_nodup.
  Qed.
End FiniteSubset.

Section FiniteCoproduct.
  Global Program Instance finite_coproduct
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
      + intros; now inversion H1.
      + apply finite_nodup.
    - apply NoDup_map.
      + intros; now inversion H1.
      + apply finite_nodup.
    - intros; intro.
      rewrite in_map_iff in H1, H2.
      destruct H1 as [x' [? _]].
      destruct H2 as [x'' [? _]].
      now subst.
    - intros; intro.
      rewrite in_map_iff in H1, H2.
      destruct H1 as [x' [? _]].
      destruct H2 as [x'' [? _]].
      now subst.
  Qed.
End FiniteCoproduct.

Section FiniteUnit.
  Global Program Instance finite_unit : Finite unit := {|
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
End FiniteUnit.

Section FiniteProduct.
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
        now inversion H1.
      + apply IHl1; auto.
        now inversion H.
      + intros.
        rewrite in_map_iff in H1.
        destruct x.
        destruct H1 as [? [? ?]].
        inversion H1; subst.
        inversion H.
        contradict H5.
        apply in_prod_iff in H5.
        intuition.
      + intros.
        inversion_clear H.
        contradict H2.
        apply in_map_iff in H2.
        destruct H2 as [? [? ?]].
        subst.
        apply in_prod_iff in H1.
        intuition.
  Qed.

  Global Program Instance product_finite
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
End FiniteProduct.

Module FinitePredicates.
  Import FiniteBijection.

  Axiom decidable_predicates:
    forall {X: Type} (P: X -> Prop) (x: X),
      {P x} + {~P x}
  .

  Definition predicate_to_bool_func
    {X: Type}
    (P: X -> Prop)
    (x: X)
  :=
    match decidable_predicates P x with
    | left _ => true
    | right  _ => false
    end
  .

  Definition bool_func_to_predicate
    {X: Type}
    (f: X -> bool)
    (x: X)
  :=
    f x = true
  .

  Global Instance finite_subsets_finite_prop
    (X: Type)
    `{Finite X}
  :
    Finite (X -> Prop)
  .
  Proof.
    apply bijection_finite with (X := X -> bool).
    - typeclasses eauto.
    - split with (bijection_inverse := predicate_to_bool_func)
                 (bijection_mapping := bool_func_to_predicate).
      + intros.
        extensionality x.
        assert (bool_func_to_predicate x1 x <-> bool_func_to_predicate x2 x).
        * now rewrite H0.
        * unfold bool_func_to_predicate in H1.
          apply Bool.eq_bool_prop_intro.
          unfold Bool.Is_true.
          destruct (x1 x) eqn:?;
          destruct (x2 x) eqn:?;
          intuition.
      + intros.
        extensionality x.
        apply propositional_extensionality.
        unfold bool_func_to_predicate.
        unfold predicate_to_bool_func.
        destruct (decidable_predicates y x);
        intuition.
  Qed.

  Global Instance finite_matrices_finite_prop
    (X: Type)
    `{Finite X}
  :
    Finite (X -> X -> Prop)
  .
  Proof.
    apply bijection_finite with (X := (X * X) -> Prop).
    - typeclasses eauto.
    - split with (bijection_inverse := uncurry)
                 (bijection_mapping := curry).
      + intros.
        extensionality x.
        destruct x as [x x'].
        assert (curry x1 x x' = curry x2 x x') by (now rewrite H0).
        apply H1.
      + intros.
        now extensionality x; extensionality x'.
  Qed.
End FinitePredicates.

Section FinitePigeonholePrinciple.
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
    induction H.
    - apply in_split in H.
      destruct H as [l2 [l3 ?]].
      exists nil, l2, l3, x.
      simpl; now f_equal.
    - destruct IHHasDup as [l1 [l2 [l3 [x' ?]]]].
      exists (x :: l1), l2, l3, x'.
      simpl; now f_equal.
  Qed.

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
    - apply NoDup_incl_length with (l' := finite_enum) in H1.
      + lia.
      + intro x; intros.
        apply finite_cover.
    - now apply HasDup_exists.
  Qed.
End FinitePigeonholePrinciple.

Section FiniteFixpoint.
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
    partial_order_rel : X -> X -> Prop;
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
    apply PeanoNat.Nat.le_exists_sub in H1.
    destruct H1 as [k [? _]]; subst.
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
    rewrite <- H2.
    apply partial_order_antisym.
    - rewrite H2 at 2.
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
    apply PeanoNat.Nat.le_exists_sub in H0.
    destruct H0 as [k [? _]]; subst.
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
      now rewrite H.
    - subst.
      rewrite seq_app in H; simpl in H.
      erewrite <- app_match_left
        with (l1 := seq 0 (length l1)) in H0.
      erewrite <- app_match_right
        with (l2 := seq (length l1) (length l2)) in H1.
      + apply in_seq in H0, H1; lia.
      + now rewrite seq_length.
      + apply H.
      + now rewrite seq_length.
      + apply H.
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
      apply map_app_lift in H1.
      destruct H1 as [ln1 [lnt1 [? [? ?]]]]; subst.
      apply map_app_lift in H4.
      destruct H4 as [ln2 [lnt2 [? [? ?]]]]; subst.
      apply map_app_lift in H5.
      destruct H5 as [ln3 [lnt3 [? [? ?]]]]; subst.
      apply map_app_lift in H6.
      destruct H6 as [ln4 [ln5 [? [? ?]]]]; subst.
      destruct ln2; simpl in H4; [ discriminate | inversion H4; clear H4 ].
      destruct ln4; simpl in H5; [ discriminate | inversion H5; clear H5 ].
      apply map_eq_nil in H7, H8; subst.
      intros; unfold mono_fixpoint.
      apply iterate_fixed with (n := n); auto.
      + assert (In n (seq 0 (S (length finite_enum)))).
        * rewrite H1.
          rewrite in_app_iff; right; now left.
        * apply in_seq in H3; now lia.
      + rewrite <- H4; symmetry.
        eapply iterate_repeat with (n := n); auto.
        eapply seq_order.
        * rewrite <- app_assoc.
          apply H1.
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
      + apply H2.
  Qed.
End FiniteFixpoint.
