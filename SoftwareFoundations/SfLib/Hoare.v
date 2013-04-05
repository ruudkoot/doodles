(**** Hoare: Hoare Logic ****)

Require Export Imp.

(*** Hoare Logic ***)

(** Assertions **)

Definition Assertion := state -> Prop.

(*

1) The variable X is equal to the integer 3.
2) The variable X is equal to the metavariable x.
3) The variable X is less than or equal to the variable Y.
4) The variable X is equal to 3 or it is less than or equal to the variable Y.
5) The variable Z squared is less than or equal ot the metavariable x and (Z + 1)^2 is
   greater than x.
6) Always holds.
7) Never holds.

*)

