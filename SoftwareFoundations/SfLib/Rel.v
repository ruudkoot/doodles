(**** Properties of Relations ****)

Require Export SfLib.

Definition relation (X : Type) := X -> X -> Prop.

Print le.
Check le : nat -> nat -> Prop.
Check le : relation nat.

(*** Basic Properties of Relations ***)

Definition partial_function {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Print next_nat.
Check next_nat : relation nat.

Theorem next_nat_partial_function:
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.
Qed.

Theorem le_not_a_partial_function:
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense.
    apply Hc with (x := 0).
      apply le_n.
      apply le_S. apply le_n.
  inversion Nonsense.
Qed.

Theorem total_relation_not_a_partial_function:
  ~(partial_function total_relation).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense.
    apply Hc with (x := 0).
      apply tot.
      apply tot.
  inversion Nonsense.
Qed.

Theorem empty_relation_partial_function:
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1.
Qed.

Definition reflexive {X : Type} (R : relation X) :=
  forall a : X, R a a.

Theorem le_reflexive:
  reflexive le.
Proof.
  unfold reflexive. intros n. constructor.
Qed.

Definition transitive {X : Type} (R : relation X) :=
  forall a b c : X, R a b -> R b c -> R a c.

Theorem le_trans:
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
    assumption.
    constructor. apply IHHmo.
Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans.
Admitted. (* FIXME: error in the textbook? *)

