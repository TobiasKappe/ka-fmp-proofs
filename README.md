[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.13293233.svg)](https://doi.org/10.5281/zenodo.13293233)

This is the Coq formalization accompanying the paper _An Elementary Proof of the FMP for Kleene Algebra_.

It includes the following files:
* Finite.v          : a typeclass for types with finitely many members.
* Utilities.v       : sundry utility lemmas used throughout the project.
* Booleans.v        : lemmas about Boolean disjunction and conjunction.
* Scope.v           : declaration of the Kleene Algebra scope.
* Terms.v           : Kleene algebra terms and equivalences between them.
* Vectors.v         : vectors and matrices of terms and their operators.
* Automata.v        : finite automata and constructions on those.
* Solve.v           : finite linear systems, their solutions and properties.
* Antimirov.v       : Antimirov automata and their solutions.
* Transformation.v  : Transformation automata and their solutions.
* ModelTheory.v     : Kleene algebras and correspondences between their classes.
* CanonicalModel.v  : how to construct a canonical Kleene algebra from an expression.
* Main.v            : the main theorems: completeness, the RMP, and the FMP.
* Derived.v         : some equations of KA derived by way of completeness.

To compile, make sure you have GNU Make and Coq >= 8.15, and run `make`.
