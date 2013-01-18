(**** Types: Type Systems ****)

Require Export Smallstep.

(*** More Automation ***)

(** The 'auto' and 'eauto' Tactics **)

Example auto_example_1:
  forall P Q R S T U : Prop, (P -> Q) -> (P -> Q) -> (T -> R) ->
                             (S -> T -> U) -> ((P -> Q) -> (P -> S)) -> T -> P -> U.
Proof.
  auto.
Qed.

Lemma auto_example_2:
  forall P Q R : Prop, Q -> (Q -> R) -> P \/ (Q /\ R).
Proof.
  auto.
Qed.

Lemma auto_example_2a:
  forall P Q R : Prop, Q -> (Q -> R) -> P \/ (Q /\ R).
Proof.
  auto using conj, or_introl, or_intror.
Qed.

Hint Constructors multi.
Hint Resolve beq_id_eq beq_id_false_not_eq.

(** The 'Proof with' Tactic **)

(** The 'solve by inversion' Tactic **)

(** The 'try solve' Tactic **)

(** The 'f_equal' Tactic **)

Definition amultistep st := multi (astep st).

Notation " t '/' st '=>a*' t' " := (amultistep st t t') (at level 40, st at level 39).