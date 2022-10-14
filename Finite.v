From Equations Require Import Equations.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Class Finite (X: Type) := {
  finite_enum: list X;
  finite_dec: forall (x1 x2: X), {x1 = x2} + {x1 <> x2};
  finite_eqb x1 x2 := if finite_dec x1 x2 then true else false;
  finite_cover: forall x, In x finite_enum;
  finite_nodup: NoDup finite_enum;
}.

Inductive position: nat -> Type :=
| PHere:
    forall {n: nat},
    position (S n)
| PThere:
    forall {n: nat}
           (v: position n),
    position (S n)
.

Section FiniteIsomorphism.
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
