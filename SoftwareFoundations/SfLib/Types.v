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

Example astep_example1:
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4)))  / empty_state =>a* (ANum 15).
Proof.
  apply multi_step with (APlus (ANum 3) (ANum 12)).
    apply AS_Plus2.
      apply av_num.
      apply AS_Mult.
  apply multi_step with (ANum 15).
    apply AS_Plus.
  apply multi_refl.
Qed.

Hint Constructors astep aval.

Example astep_example1':
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4)))  / empty_state =>a* (ANum 15).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize" := 
   repeat (print_goal; eapply multi_step ; 
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply multi_refl.

Example astep_example1'':
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4)))  / empty_state =>a* (ANum 15).
Proof.
  normalize.
Qed.

Example astep_example1''':
  exists e', (APlus (ANum 3) (AMult (ANum 3) (ANum 4)))  / empty_state =>a* e'.
Proof.
  eapply ex_intro. normalize.
Qed.

Theorem normalize_ex:
  exists e', (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state =>a* e'.
Proof.
  eapply ex_intro. normalize.
Qed.

Theorem normalize_ex':
  exists e', (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state =>a* e'.
Proof.
  apply ex_intro with (ANum 6).
  normalize.
Qed.

(*** Types Arithmetic Expressions ***)


