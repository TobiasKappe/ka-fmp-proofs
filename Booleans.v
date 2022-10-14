From Equations Require Import Equations.
Require Import Coq.Lists.List.

Section BooleanConjunction.
  Equations conj (l: list bool) : bool := {
    conj nil := true;
    conj (b :: l) := b && (conj l);
  }.

  Lemma conj_true (l: list bool):
    conj l = true <-> (forall x, In x l -> x = true)
  .
  Proof.
    split; intros.
    - induction l;
      autorewrite with conj in H.
      + destruct H0.
      + apply andb_prop in H.
        destruct H, H0.
        * now subst.
        * now apply IHl.
    - induction l;
      autorewrite with conj;
      auto.
      apply andb_true_intro.
      split.
      + apply H.
        now left.
      + apply IHl.
        intros.
        apply H.
        now right.
  Qed.
End BooleanConjunction.

Section BooleanDisjunction.
  Equations disj (l: list bool) : bool := {
    disj nil := false;
    disj (b :: l) := b || (disj l);
  }.

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
End BooleanDisjunction.
