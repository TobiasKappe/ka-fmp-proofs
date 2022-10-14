Require Import KA.Terms.
Require Import KA.Vectors.
Require Import KA.Scope.
Local Open Scope ka_scope.

Section System.
  Variable (A: Type).
  Notation term := (term A).
  Notation matrix := (matrix A).
  Notation vector := (vector A).

  Record system (Q: Type) := {
    smat: matrix Q;
    svec: vector Q;
  }.
End System.

Arguments smat {A} {Q}.
Arguments svec {A} {Q}.

Section Solve.
  Context {A: Type}.
  Notation term := (term A).
  Notation matrix := (matrix A).
  Notation vector := (vector A).
  Notation system := (system A).

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
End Solve.
