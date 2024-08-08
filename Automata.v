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
