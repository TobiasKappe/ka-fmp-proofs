Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.

Require Import KA.Automata.
Require Import KA.Booleans.
Require Import KA.Finite.
Require Import KA.Solve.
Require Import KA.Terms.
Require Import KA.Utilities.
Require Import KA.Vectors.

Local Open Scope ka_scope.
Local Open Scope program_scope.

Section AntimirovTypes.
  Variable (A: Type).
  Notation term := (term A).

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
  Derive Signature for derivative.

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
End AntimirovTypes.

Arguments TOneOne {A}.
Arguments TLetterLetter {A}.
Arguments TLetterOne {A} {a}.
Arguments TPlusLeft {A} {t1} t2.
Arguments TPlusRight {A} t1 {t2}.
Arguments TTimesPre {A} {t1} t2.
Arguments TTimesPost {A} t1 {t2}.
Arguments TStarInner {A}.
Arguments TStarOne {A}.
Arguments derivative_write {A} {t}.

Section AntimirovInitial.
  Context {A: Type}.
  Notation term := (term A).
  Notation derivative := (derivative A).
  Notation initial := (initial A).

  Equations initial_b {t: term} (d: derivative t): bool := {
    @initial_b 1 TOneOne := true;
    @initial_b ($ a) (TLetterLetter a) := true;
    @initial_b (t1 + t2) (TPlusLeft _ d1) := initial_b d1;
    @initial_b (t1 + t2) (TPlusRight _ d2) := initial_b d2;
    @initial_b (t1 ;; t2) (TTimesPre _ d1) := initial_b d1;
    @initial_b (t*) (TStarInner _ d) := initial_b d;
    @initial_b (t*) (TStarOne _) := true;
    @initial_b _ _ := false;
  }.

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

  Lemma initial_list (t: term) (d: derivative t):
    initial d <-> In d (initial_l t)
  .
  Proof.
    dependent induction d;
    autorewrite with initial_l;
    autorewrite with initial_b;
    try (split; intros; [now left | constructor]);
    try (split; intros; [inversion H | now destruct H]).
    - intuition; handle_lists.
      + dependent destruction H1.
        left; handle_lists.
        eexists; intuition.
      + constructor.
        intuition; handle_lists.
        * apply H0.
          inversion H1.
          now clean_exists.
        * discriminate.
    - intuition; handle_lists.
      + dependent destruction H1.
        right; handle_lists.
        eexists; intuition.
      + constructor.
        intuition; handle_lists.
        * discriminate.
        * apply H0.
          inversion H1.
          now clean_exists.
    - intuition; handle_lists.
      + dependent destruction H1.
        eexists; intuition.
      + constructor.
        apply H0.
        inversion H1.
        now clean_exists.
    - intuition.
      + dependent destruction H1.
      + handle_lists; discriminate.
    - simpl; intuition.
      + dependent destruction H1.
        right; handle_lists.
        eexists; intuition.
      + discriminate.
      + handle_lists.
        inversion H1.
        constructor.
        clean_exists.
        intuition.
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
      handle_lists.
      rewrite sum_split.
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
      handle_lists.
      rewrite map_ext with (g := (fun x => derivative_write x ;; t2)) by easy.
      rewrite <- map_map with (g := fun x => x ;; t2).
      rewrite sum_distribute_right.
      now rewrite <- IHt1.
    - autorewrite with initial_l.
      simpl; autorewrite with sum.
      autorewrite with derivative_write.
      handle_lists.
      rewrite map_ext with (g := (fun x => derivative_write x ;; t*)) by easy.
      rewrite <- map_map with (g := fun x => x ;; t*).
      rewrite sum_distribute_right.
      rewrite <- IHt.
      rewrite EStarLeft at 1.
      now rewrite EPlusComm.
  Qed.

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
End AntimirovInitial.

Section AntimirovNullable.
  Context {A: Type}.
  Notation term := (term A).
  Notation derivative := (derivative A).
  Notation nullable := (nullable A).

  Equations nullable_b {t: term} (d: derivative t) : bool := {
    @nullable_b 1 TOneOne := true;
    @nullable_b ($ _) TLetterOne := true;
    @nullable_b (t1 + t2) (TPlusLeft _ d) := nullable_b d;
    @nullable_b (t1 + t2) (TPlusRight _ d) := nullable_b d;
    @nullable_b (t1 ;; t2) (TTimesPre _ d) :=
      nullable_b d && disj (map nullable_b (initial_l t2));
    @nullable_b (t1 ;; t2) (TTimesPost _ d) :=
      nullable_b d;
    @nullable_b (t*) (TStarInner _ d) :=
      nullable_b d;
    @nullable_b (t*) (TStarOne _) := true;
    @nullable_b _ _ := false;
  }.

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
      propify; intuition.
      handle_lists; eexists; intuition.
      now apply initial_list.
    - propify; intuition.
      handle_lists.
      eapply NullableTimesPre; intuition.
      now apply initial_list.
  Qed.

  Lemma nullable_one (t: term) (d: derivative t):
    nullable d ->
    1 <= derivative_write d
  .
  Proof.
    intros.
    dependent induction H;
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

  Lemma nullable_term_matches
    (t: term)
    (t': derivative t)
  :
    term_matches (derivative_write t') nil ->
    nullable t'
  .
  Proof.
    dependent induction t;
    dependent destruction t';
    autorewrite with derivative_write; intros;
    try constructor; intuition;
    dependent destruction H;
    apply app_eq_nil in x; destruct x;
    subst; intuition.
    eapply term_equiv_sound in H0; swap 1 2.
    symmetry; apply initial_reconstruct.
    apply term_matches_sum in H0.
    destruct H0 as [t [? ?]].
    handle_lists; subst.
    apply initial_list in H2.
    eapply NullableTimesPre; intuition.
  Qed.
End AntimirovNullable.

Section AntimirovDerive.
  Context {A: Type}.
  Context `{Finite A}.
  Notation term := (term A).
  Notation derivative := (derivative A).
  Notation initial := (initial A).
  Notation nullable := (nullable A).

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
        propify; intuition.
        * now apply nullable_dec.
        * handle_lists; eexists; intuition.
          now apply initial_list.
      + propify; intuition.
        handle_lists.
        eapply DeriveTimesJump; intuition.
        * now apply nullable_dec.
        * apply initial_list, H2.
    - split; intros.
      + propify; intuition.
        dependent destruction H0.
        * left; now apply IHt.
        * right; intuition.
          -- now apply nullable_dec.
          -- handle_lists; eexists; intuition.
             now apply initial_list.
      + propify; intuition.
        * apply DeriveStarInnerStep.
          now apply IHt.
        * handle_lists.
          eapply DeriveStarInnerJump; intuition.
          -- now apply nullable_dec.
          -- apply initial_list, H2.
  Qed.

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
      + now inversion H0; clean_exists.
    - rewrite IHt2.
      split; intros.
      + now subst.
      + now inversion H0; clean_exists.
    - rewrite IHt1.
      split; intros.
      + now subst.
      + now inversion H0; clean_exists.
    - rewrite IHt2.
      split; intros.
      + now subst.
      + now inversion H0; clean_exists.
    - rewrite IHt.
      split; intros.
      + now subst.
      + now inversion H0; clean_exists.
  Qed.

  Global Program Instance derivative_finite: forall t, Finite (derivative t).
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
    unfold derivative_finite_obligation_1.
    dependent induction x;
    autorewrite with derive_list.
    - now left.
    - now left.
    - right; now left.
    - handle_lists; left.
      handle_lists; eexists; intuition.
    - handle_lists; right;
      handle_lists; eexists; intuition.
    - handle_lists; left.
      handle_lists; eexists; intuition.
    - handle_lists; right;
      handle_lists; eexists; intuition.
    - right; handle_lists; now eexists.
    - now left.
  Qed.
  Next Obligation.
    unfold derivative_finite_obligation_1.
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
        now inversion H0; clean_exists.
      + apply NoDup_map; auto; intros.
        now inversion H0; clean_exists.
      + intros; intro.
        now repeat (handle_lists; subst).
      + intros; intro.
        now repeat (handle_lists; subst).
    - apply NoDup_app.
      + apply NoDup_map; auto; intros.
        now inversion H0; clean_exists.
      + apply NoDup_map; auto; intros.
        now inversion H0; clean_exists.
      + intros; intro.
        now repeat (handle_lists; subst).
      + intros; intro.
        now repeat (handle_lists; subst).
    - constructor.
      + intro.
        now repeat (handle_lists; subst).
      + apply NoDup_map; auto; intros.
        now inversion H0; clean_exists.
  Qed.

  Lemma term_matches_step
    (t: term)
    (t': derivative t)
    (a: A)
    (w: list A)
  :
    term_matches (derivative_write t') (a :: w) ->
    exists t'',
      derive a t' t'' /\
      term_matches (derivative_write t'') w
  .
  Proof.
    dependent induction t;
    dependent destruction t';
    autorewrite with derivative_write; intros.
    - dependent destruction H0.
    - dependent destruction H0.
      eexists; intuition.
      + constructor.
      + simpl; constructor.
    - dependent destruction H0.
    - apply IHt1 in H0.
      destruct H0 as [t'' [? ?]].
      eexists; intuition.
      + constructor; eauto.
      + now simpl.
    - apply IHt2 in H0.
      destruct H0 as [t'' [? ?]].
      eexists; intuition.
      + constructor; eauto.
      + now simpl.
    - dependent destruction H0.
      destruct w1.
      + simpl in x; subst.
        eapply term_equiv_sound in H0_0; swap 1 2.
        symmetry; apply initial_reconstruct.
        apply term_matches_sum in H0_0.
        destruct H0_0 as [t'' [? ?]].
        handle_lists; subst.
        apply initial_list in H2.
        apply IHt2 in H1.
        destruct H1 as [t'' [? ?]].
        apply nullable_term_matches in H0_.
        eexists (TTimesPost t1 t''); intuition.
        econstructor; eauto.
      + simpl in x; inversion x; subst; clear x.
        apply IHt1 in H0_.
        destruct H0_ as [t'' [? ?]]; subst.
        eexists (TTimesPre t2 t'');
        autorewrite with derivative_write;
        intuition now constructor.
    - apply IHt2 in H0.
      destruct H0 as [t'' [? ?]].
      exists (TTimesPost t1 t'').
      intuition now constructor.
    - dependent destruction H0.
      destruct w1.
      + simpl in x; subst.
        apply term_matches_star_progress in H0_0.
        destruct H0_0 as [? [? [? [? ?]]]]; subst.
        eapply term_equiv_sound in H1; swap 1 2.
        symmetry; apply initial_reconstruct.
        apply term_matches_sum in H1.
        destruct H1 as [t'' [? ?]].
        handle_lists; subst.
        apply initial_list in H3.
        apply IHt in H1.
        destruct H1 as [t'' [? ?]].
        apply nullable_term_matches in H0_.
        eexists (TStarInner t t''); intuition.
        * eapply DeriveStarInnerJump; eauto.
        * autorewrite with derivative_write; now constructor.
      + simpl in x; inversion x; subst; clear x.
        apply IHt in H0_.
        destruct H0_ as [t'' [? ?]]; subst.
        eexists (TStarInner t t'');
        autorewrite with derivative_write;
        intuition now constructor.
    - dependent destruction H0.
  Qed.

  Lemma derive_step
    (t : term)
    (d : derivative t)
    (a : A)
    (t' t'' : derivative t)
  :
    derive a t' t'' ->
    $ a;; derivative_write t'' <= derivative_write t'
  .
  Proof.
    intros.
    dependent induction t;
    dependent destruction t';
    dependent destruction t'';
    dependent destruction H0;
    autorewrite with derivative_write.
    - rewrite ETimesUnitRight.
      apply term_lequiv_refl.
    - now apply IHt1.
    - now apply IHt2.
    - rewrite ETimesAssoc.
      apply times_mor_mono; intuition.
    - eapply term_lequiv_trans; intuition.
      rewrite <- ETimesUnitLeft with (t := derivative_write i).
      apply times_mor_mono.
      + now apply nullable_one.
      + now apply initial_cover.
    - now apply IHt2.
    - rewrite ETimesAssoc.
      apply times_mor_mono; intuition.
    - eapply term_lequiv_trans with (t2 := t*).
      + rewrite ETimesAssoc.
        rewrite EStarLeft at 2.
        rewrite EStarLeft at 3.
        apply term_lequiv_split_left.
        apply times_mor_mono; intuition.
        eapply term_lequiv_trans; intuition.
        now apply initial_cover.
      + rewrite <- ETimesUnitLeft with (t := t*).
        apply times_mor_mono.
        * now apply nullable_one.
        * now rewrite <- ETimesUnitLeft with (t := t*) at 1.
  Qed.
End AntimirovDerive.

Section AntimirovAutomaton.
  Context {A: Type}.
  Context `{Finite A}.
  Notation term := (term A).
  Notation derivative := (derivative A).
  Notation automaton := (automaton A).
  Notation nullable := (nullable A).
  Notation initial := (initial A).
  Notation vector := (vector A).

  Definition automaton_antimirov (t: term) : automaton (derivative t) := {|
    aut_transitions a d1 d2 := derive_b a d1 d2;
    aut_accept := nullable_b;
  |}.

  Lemma automaton_antimirov_accepts_local
    (t: term)
    (t': derivative t)
    (w: list A)
  :
    term_matches (derivative_write t') w ->
    automaton_accepts (automaton_antimirov t) t' w
  .
  Proof.
    revert t'; induction w; intros.
    - apply nullable_term_matches in H0.
      constructor; simpl.
      now apply nullable_dec.
    - apply term_matches_step in H0.
      destruct H0 as [? [? ?]].
      econstructor; simpl.
      + apply derive_dec; eauto.
      + now apply IHw.
  Qed.

  Lemma automaton_antimirov_accepts
    (t: term)
    (w: list A)
  :
    term_matches t w ->
    exists t',
        initial t' /\
        automaton_accepts (automaton_antimirov t) t' w
  .
  Proof.
    intros.
    eapply term_equiv_sound in H0; swap 1 2.
    symmetry; apply initial_reconstruct.
    apply term_matches_sum in H0.
    destruct H0 as [? [? ?]].
    handle_lists; subst.
    apply initial_list in H2.
    eexists; intuition.
    now apply automaton_antimirov_accepts_local.
  Qed.

  Definition antimirov_solution (t: term): vector (derivative t) :=
    compute_automaton_solution (automaton_antimirov t)
  .

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
      now apply derive_step.
    - simpl in H0.
      apply nullable_one.
      now apply nullable_dec.
  Qed.
End AntimirovAutomaton.
