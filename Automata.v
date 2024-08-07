Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Local Open Scope program_scope.
Local Open Scope bool_scope.

Require Import KA.Finite.
Require Import KA.Booleans.
Require Import KA.Terms.
Require Import KA.Vectors.
Local Open Scope ka_scope.

Section Automaton.
  Variable (A: Type).

  Record automaton (Q: Type) := {
    aut_transitions: A -> Q -> Q -> bool;
    aut_accept: Q -> bool;
  }.
End Automaton.

Arguments aut_transitions {A} {Q}.
Arguments aut_accept {A} {Q}.

Section AutomatonMorphism.
  Context {A: Type}.
  Notation automaton := (automaton A).

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
End AutomatonMorphism.

Arguments automaton_homomorphism_f {A} {Q1} {Q2} {aut1} {aut2}.

Section AutomatonLanguage.
  Context {A: Type}.
  Context `{Finite A}.
  Notation automaton := (automaton A).
  Notation vector := (vector A).
  Notation term := (vector A).

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
End AutomatonLanguage.
