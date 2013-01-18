(**** Smallstep: Small-step Operational Semantics ****)

Require Export Imp.

(*** Relations ***)

Definition relation (X : Type) := X -> X -> Prop.

(*** A Toy Language ***)

Inductive tm : Type :=
| C : nat -> tm
| P : tm -> tm -> tm.

Module SimpleArith0.

  Fixpoint eval (t : tm) : nat :=
    match t with
      | C n => n
      | P a1 a2 => eval a1 + eval a2
    end.

End SimpleArith0.

Reserved Notation " t '||' n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
| E_Const : forall n, C n || n
| E_Plus : forall t1 t2 n1 n2, t1 || n1 -> t2 || n2 -> P t1 t2 || (n1 + n2)
where " t '||' n " := (eval t n).

Module SimpleArith1.

  Reserved Notation " t '=>' t' " (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2, P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2, t1 => t1' -> P t1 t2 => P t1' t2
  | ST_Plus2 : forall n1 t2 t2', t2 => t2' -> P (C n1) t2 => P (C n1) t2'
  where " t '=>' t' " := (step t t').

  Example test_step_1:
    P (P (C 0) (C 3)) (P (C 2) (C 4)) => P (C (0 + 3)) (P (C 2) (C 4)).
  Proof.
    repeat constructor.
  Qed.

  Example test_step_2:
    P (C 0) (P (C 2) (P (C 0) (C 3))) => P (C 0) (P (C 2) (C (0 + 3))).
  Proof.
    repeat constructor.
  Qed.

  Definition deterministic {X : Type} (R : relation X) :=
    forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

  Theorem step_deterministic:
    deterministic step.
  Proof.
    unfold deterministic.
    intros x y1 y2 Hy1. generalize dependent y2.
    induction Hy1; intros y2 Hy2.
      (* ST_PlusConstConst *)
      inversion Hy2.
        (* ST_PlusConstCOnst *) reflexivity.
        (* ST_Plus1          *) inversion H2.
        (* ST_Plus2          *) inversion H2.
      (* ST_Plus1 *)
      inversion Hy2; subst.
        (* ST_PlusConstConst *) inversion Hy1.
        (* ST_Plus1          *) rewrite <- (IHHy1 t1'0). reflexivity. assumption.
        (* ST_Plus2          *) inversion Hy1.
      inversion Hy2; subst.
        (* ST_PlusConstConst *) inversion Hy1.
        (* ST_Plus1          *) inversion H2.
        (* ST_Plus2          *) rewrite <- (IHHy1 t2'0). reflexivity. assumption.
  Qed.

End SimpleArith1.

(** Values **)

Inductive value : tm -> Prop :=
  v_const : forall n, value (C n).

Reserved Notation " t '=>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_PlusConstConst : forall n1 n2, P (C n1) (C n2) => C (n1 + n2)
| ST_Plus1 : forall t1 t1' t2, t1 => t1' -> P t1 t2 => P t1' t2
| ST_Plus2 : forall v1 t2 t2', value v1 -> t2 => t2' -> P v1 t2 => P v1 t2'
where " t '=>' t' " := (step t t').

Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1. generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  (* PCC *)
    inversion Hy2; subst.
    (* PCC *) reflexivity.
    (* P1  *) inversion H2.
    (* P2  *) inversion H3.
  (* P1  *)
    inversion Hy2; subst.
    (* PCC *) inversion Hy1.
    (* P1  *) rewrite <- (IHHy1 t1'0). reflexivity. assumption.
    (* P2  *) inversion H1. subst. inversion Hy1.
  (* P2  *)
    inversion Hy2; subst.
    (* PCC *) inversion Hy1.
    (* P1  *) inversion H. subst. inversion H3.
    (* P2  *) rewrite <- (IHHy1 t2'0). reflexivity. assumption.
Qed.

(** Strong Progress and Normal Forms **)

Theorem strong_progress:
  forall t, value t \/ (exists t', t => t').
Proof.
  intro t.
  induction t.
    (* t = C n *)
    left. constructor.
    (* t = P t1 t2 *)
    right. inversion IHt1.
      inversion IHt2.
        inversion H. inversion H0. exists (C (n + n0)). constructor.
        inversion H0 as [t' H1]. exists (P t1 t'). constructor.
          apply H.
          apply H1.
      inversion H as [t' H0].
        exists (P t' t2). constructor. apply H0.
Qed.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Lemma value_is_nf:
  forall t, value t -> normal_form step t.
Proof.
  intros t H.
  unfold normal_form. unfold not. intro G.
  inversion H. subst.
  inversion G.
  inversion H0.
Qed.

Lemma nf_is_value:
  forall t, normal_form step t -> value t.
Proof.
  unfold normal_form.
  intros t H.
  assert (G : value t \/ exists t', t => t').
    apply strong_progress.
  inversion G.
    apply H0.
    apply ex_falso_quodlibet. apply H. assumption.
Qed.

Corollary nf_same_as_value:
  forall t, normal_form step t <-> value t.
Proof.
  split.
    apply nf_is_value.
    apply value_is_nf.
Qed.

Module Temp1.

  Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n)
  | v_funny : forall t1 n2, value (P t1 (C n2)).

  Reserved Notation " t '=>' t' " (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2, P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2, t1 => t1' -> P t1 t2 => P t1' t2
  | ST_Plus2 : forall v1 t2 t2', value v1 -> t2 => t2' -> P v1 t2 => P v1 t2'
  where " t '=>' t' " := (step t t').

  Lemma value_not_same_as_normal_form:
    exists t, value t /\ ~normal_form step t.
  Proof.
    exists (P (C 1) (C 2)).
    split.
      repeat constructor.
      intro G. apply G. exists (C 3). constructor.
  Qed.

End Temp1.

Module Temp2.

  Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

  Reserved Notation " t '=>' t' " (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_Funny : forall n, C n => P (C n) (C 0)
  | ST_PlusConstConst : forall n1 n2, P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2, t1 => t1' -> P t1 t2 => P t1' t2
  | ST_Plus2 : forall v1 t2 t2', value v1 -> t2 => t2' -> P v1 t2 => P v1 t2'
  where " t '=>' t' " := (step t t').

  Lemma value_not_same_as_normal_form:
    exists t, value t /\ ~normal_form step t.
  Proof.
    exists (C 0).
    split.
      constructor.
      intro G. apply G. exists (P (C 0) (C 0)). constructor.
  Qed.

End Temp2.

Module Temp3.

  Inductive value : tm -> Prop :=
  | v_const : forall n, value (C n).

  Reserved Notation " t '=>' t' " (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2, P (C n1) (C n2) => C (n1 + n2)
  | ST_Plus1 : forall t1 t1' t2, t1 => t1' -> P t1 t2 => P t1' t2
  where " t '=>' t' " := (step t t').

  Lemma value_not_same_as_normal_form:
    exists t, ~value t /\ normal_form step t.
  Proof.
    exists (P (C 0) (P (C 0) (C 0))).
    split.
      intro G. inversion G.
      unfold normal_form. intro G. inversion G. inversion H. subst. inversion H3.
  Qed.

End Temp3.

(* Additional Exercises *)

Module Temp4.

  Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

  Inductive value : tm -> Prop :=
  | v_true : value ttrue
  | v_false : value tfalse.

  Reserved Notation " t '=>' t' " (at level 40).

  Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2, tif ttrue t1 t2 => t1
  | ST_IfFalse : forall t1 t2, tif tfalse t1 t2 => t2
  | ST_If : forall t1 t1' t2 t3, t1 => t1' -> tif t1 t2 t3 => tif t1' t2 t3
  where " t '=>' t' " := (step t t').

  Example bool_step_prop1:
    ~ (tfalse => tfalse).
  Proof.
    intro G. inversion G.
  Qed.

  Example bool_step_prop2:
    ~ (tif ttrue (tif ttrue ttrue ttrue) (tif tfalse tfalse tfalse) => ttrue).
  Proof.
    intro G. inversion G.
  Qed.

  Example bool_step_prop3:
    tif (tif ttrue ttrue ttrue) (tif ttrue ttrue ttrue) tfalse 
    =>
    tif ttrue (tif ttrue ttrue ttrue) tfalse.
  Proof.
    repeat constructor.
  Qed.

  Theorem strong_progress:
    forall t, value t \/ (exists t', t => t').
  Proof.
    intro t.
    induction t.
      left. constructor.
      left. constructor.
      right. inversion IHt1.
        inversion H.
          exists t2. constructor.
          exists t3. constructor.
        inversion H.
          exists (tif x t2 t3). apply ST_If. apply H0.
  Qed.

  Theorem step_deterministic:
    deterministic step.
  Proof.
    unfold deterministic.
    intros x y1 y2 Hy1.
    generalize dependent y2.
    induction Hy1; intros y2 Hy2.
      inversion Hy2; subst.
        reflexivity.
        inversion H3.
      inversion Hy2; subst.
        reflexivity.
        inversion H3.
      inversion Hy2; subst.
        inversion Hy1.
        inversion Hy1.
        assert (t1' = t1'0).
          apply IHHy1. apply H3.
        rewrite H. reflexivity.
  Qed.

  Module Temp5.

    Reserved Notation " t '=>' t' " (at level 40).

    Inductive step : tm -> tm -> Prop :=
    | ST_IfTrue : forall t1 t2, tif ttrue t1 t2 => t1
    | ST_IfFalse : forall t1 t2, tif tfalse t1 t2 => t2
    | ST_If : forall t1 t1' t2 t3, t1 => t1' -> tif t1 t2 t3 => tif t1' t2 t3
    | ST_Shortcut : forall t1 t2 t3,
                      value t2 -> value t3 -> t2 = t3 -> tif t1 t2 t3 => t2
    where " t '=>' t' " := (step t t').

    Theorem step_not_deterministic:
      ~deterministic step.
    Proof.
    Admitted. (* FIXME *)

    Theorem strong_progress:
      forall t, value t \/ (exists t', t => t').
    Proof.
    Admitted. (* FIXME *)

    (* Yes, any one of them. *)

  End Temp5.

End Temp4.

(*** Multi-Step Reduction ***)

(** Definitions **)

(* Already in SfLib!

  Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X), R x y -> multi R y z -> multi R x z.

*)

Theorem mutli_R:
  forall (X : Type) (R : relation X) (x y : X), R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y.
    apply H.
    apply multi_refl.
Qed.

Theorem multi_trans:
  forall (X : Type) (R : relation X) (x y z : X), multi R x y -> multi R y z -> multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    assumption.
    apply multi_step with y. assumption. apply IHG. assumption.
Qed.

Definition multistep := multi step.

Notation " t '=>*' t' " := (multistep t t') (at level 40).

(** Examples **)

Example test_multistep_1:
  P (P (C 0) (C 3)) (P (C 2) (C 4)) =>* C ((0 + 3) + (2 + 4)).
Proof.
  apply multi_step with (P (C (0 + 3)) (P (C 2) (C 4))).
    repeat constructor.
    apply multi_step with (P (C (0 + 3)) (C (2 + 4))).
      repeat constructor.
      apply multi_R.
        constructor.
Qed.

Example test_multistep_1':
  P (P (C 0) (C 3)) (P (C 2) (C 4)) =>* C ((0 + 3) + (2 + 4)).
Proof.
  eapply multi_step.
    repeat constructor.
    eapply multi_step.
      apply ST_Plus2. apply v_const.
      apply ST_PlusConstConst.
      eapply multi_step.
        apply ST_PlusConstConst.
        apply multi_refl.
Qed.

Example test_multistep_2:
  C 3 =>* C 3.
Proof.
  apply multi_refl.
Qed.

Example test_multistep_3:
  P (C 0) (C 3) =>* P (C 0) (C 3).
Proof.
  constructor.
Qed.

Example test_multistep_4:
  P (C 0) (P (C 2) (P (C 0) (C 3))) =>* P (C 0) (C (2 + (0 + 3))).
Proof.
  apply multi_step with (P (C 0) (P (C 2) (C (0 + 3)))).
  repeat constructor.
  apply multi_R.
  repeat constructor.
Qed.

(** Normal Forms Again **)

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) := t =>* t' /\ step_normal_form t'.

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1.
  inversion P2 as [P21 P22]; clear P2.
  generalize dependent y2.
  induction y1; intros.
    (* t = C n *)
    inversion P11; subst.
      inversion P21; subst.
        reflexivity.
        inversion H.
      admit.
    (* t = P t1 t2 *)
    inversion P21. inversion P11.
      subst. symmetry. apply H2.
Admitted. (* FIXME *)


      
  
                        