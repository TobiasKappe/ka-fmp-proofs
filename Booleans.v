From Equations Require Import Equations.
Require Import Coq.Lists.List.

Equations conj (l: list bool) : bool := {
  conj nil := true;
  conj (b :: l) := b && (conj l);
}.

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
