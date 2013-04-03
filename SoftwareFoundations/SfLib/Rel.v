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

Print le_trans.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo.
Qed.

Theorem lt_trans':
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    constructor. assumption.
    constructor. assumption.
Qed.

Theorem lt_trans'':
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
    inversion Hmo.
    assert (S n <= S m).
      constructor. assumption.
Admitted. (* FIXME (without using le_trans? *)

Theorem le_Sn_le:
  forall n m, S n <= m -> n <= m.
Proof.
  intros n m H.
  apply le_trans with (S n).
  apply le_S. apply le_n.
  apply H.
Qed.

Theorem le_S_n:
  forall n m, (S n <= S m) -> (n <= m).
Proof.
  intros n m H.
  inversion H.
    apply le_n.
    apply le_Sn_le. apply H1.
Qed.

Theorem le_Sn_n:
  forall n, ~(S n <= n).
Proof.
  intros n H.
  induction n.
    inversion H.
    apply IHn. inversion H. rewrite H1 in H. rewrite H1. apply H.
  apply le_S_n. apply le_S. apply H1.
Qed.

Definition symmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric:
  ~ (symmetric le).
Proof.
  unfold not. unfold symmetric.
  intros Hc.
  assert (1 <= 0) as Nonsense.
    apply Hc. apply le_S. apply le_n.
  inversion Nonsense.
Qed.

Definition antisymmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Lemma eq_S_n:
  forall n m, n = m -> S n = S m.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Theorem le_antisymmetric:
  antisymmetric le.
Proof.
  unfold antisymmetric.
  induction a.
    intros. inversion H0. reflexivity.
    induction b.
      intros. inversion H.
      intros. apply eq_S_n. apply IHa.
        apply le_S_n. apply H.
        apply le_S_n. apply H0.
Qed.

Theorem le_step:
  forall n m p, n < m -> m <= S p -> n <= p.
Proof.
  intros n m p Hnm Hmp.
  apply le_S_n.
  assert (S n <= m). auto.
  apply le_trans with m; assumption.
Qed.

Definition equivalence {X : Type} (R : relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X : Type} (R : relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X : Type} (R : relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order:
  order le.
Proof.
  unfold order. split.
    apply le_reflexive.
    split.
      apply le_antisymmetric.
      apply le_trans.
Qed.

(*** Reflexive, Transitive Closure ***)

Inductive clos_refl_trans {A : Type} (R : relation A) : relation A :=
  | rt_step : forall x y, R x y -> clos_refl_trans R x y
  | rt_refl : forall x, clos_refl_trans R x x
  | rt_trans : forall x y z, clos_refl_trans R x y -> clos_refl_trans R y z -> clos_refl_trans R x z.

Theorem next_nat_closure_is_le:
  forall n m, (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
    intro H. induction H.
      apply rt_refl.
      apply rt_trans with m. apply IHle. apply rt_step. apply nn.
    intro H. induction H.
      inversion H. apply le_S. apply le_n.
      apply le_n.
      apply le_trans with y.
        apply IHclos_refl_trans1.
        apply IHclos_refl_trans2.
Qed.

Inductive refl_step_closure {X : Type} (R : relation X) : relation X :=
  | rsc_refl : forall (x : X), refl_step_closure R x x
  | rsc_step : forall (x y z : X), R x y -> refl_step_closure R y z -> refl_step_closure R x z.

Theorem rsc_R:
  forall (X : Type) (R : relation X) (x y : X), R x y -> refl_step_closure R x y.
Proof.
  intros X R x y H.
  apply rsc_step with y.
    apply H.
    apply rsc_refl.
Qed.

Theorem rsc_trans:
  forall (X : Type) (R : relation X) (x y z : X),
    refl_step_closure R x y -> refl_step_closure R y z -> refl_step_closure R x z.
Proof.
  intros X R x y z Hxy Hyz.
Admitted. (* FIXME *)

Theorem rtc_rsc_coincide:
  forall (X : Type) (R : relation X) (x y : X),
    clos_refl_trans R x y <-> refl_step_closure R x y.
Proof.
  intros X R x y. split.
  intro H. induction H.
    apply rsc_step with y.
      apply H.
      apply rsc_refl.
      apply rsc_refl.
      admit.
  intro H. induction H.
    apply rt_refl.
    inversion H0.
      subst. apply rt_step. apply H.
      admit.
Admitted. (* FIXME *)