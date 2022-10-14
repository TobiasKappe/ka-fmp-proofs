Require Coq.Program.Equality.

Ltac clean_exists :=
  repeat match goal with
  | H: existT ?P ?p _ = existT ?P ?p _ |- _ =>
    apply Eqdep.EqdepTheory.inj_pair2 in H
         end;
  subst.
