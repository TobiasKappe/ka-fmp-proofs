[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.7467245.svg)](https://doi.org/10.5281/zenodo.7467245)

This is the Coq formalization accompanying the paper _Completeness and the Finite Model Property for Kleene Algebra, Reconsidered_.

It includes the following files:
* Finite.v    : a typeclass for types with finitely many members.
* Utilities.v : sundry utility lemmas used throughout the project.
* Booleans.v  : lemmas about Boolean disjunction and conjunction.
* Scope.v     : declaration of the Kleene Algebra scope.
* Terms.v     : Kleene Algebra terms and equivalences between them.
* Vectors.v   : vectors and matrices of terms and their operators.
* Solve.v     : finite linear systems, their solutions and properties.
* Automata.v  : finite automata and constructions on those.
* Antimirov.v : Antimirov automata and the round-trip property.
* Structure.v : Kleene Algebras and how to obtain them from monoids.
* Main.v      : the main theorems: completeness and the FMP
* Derived.v   : some equations of KA derived by way of completeness.

To compile, make sure you have GNU Make and Coq >= 8.15, and run `make`.
