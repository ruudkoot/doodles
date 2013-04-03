(**** Equiv: Program Equivalence ****)

Require Export Imp.

(*** Behavioural Equivalence ***)

(** Definition **)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state), aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state), beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state), (c1 / st || st') <-> (c2 / st || st').

(* (a) no
   (b) yes
*)

(* {a} {b} {c,h} {d} {e} {f} {g} {i} *) (* FIXME *)

(** Examples **)

Theorem aequiv_example:
  aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
  intros st. simpl. apply minus_diag.
Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
  intros st.
  unfold beval.
  rewrite aequiv_example.
  reflexivity.
Qed.

Theorem skip_left:
  forall c, cequiv (SKIP; c) c.
Proof.
  intros c st st'.
  split; intros H.
    inversion H. subst. inversion H2. subst. assumption.
    apply E_Seq with st. apply E_Skip. assumption.
Qed.

Theorem skip_right:
  forall c, cequiv (c; SKIP) c.
Proof.
  intros c st st'.
  split; intros H.
    inversion H. subst. inversion H5. subst. assumption.
    apply E_Seq with st'. assumption. apply E_Skip.
Qed.

Theorem IFB_true_simple:
  forall c1 c2, cequiv (IFB BTrue THEN c1 ELSE c2 FI) c1.
Proof.
  intros c1 c2.
  split; intros H.
    inversion H. subst. assumption. inversion H5.
    apply E_IfTrue. reflexivity. assumption.
Qed.

Theorem IFB_true:
  forall b c1 c2, bequiv b BTrue -> cequiv (IFB b THEN c1 ELSE c2 FI) c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  inversion H; subst.
    assumption.
    rewrite Hb in H5. inversion H5.
  apply E_IfTrue; try assumption. rewrite Hb. reflexivity.
Qed.

Theorem IFB_false:
  forall b c1 c2, bequiv b BFalse -> cequiv (IFB b THEN c1 ELSE c2 FI) c2.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
    inversion H; subst.
      rewrite Hb in H5. inversion H5.
      assumption.
    apply E_IfFalse; try assumption. rewrite Hb. reflexivity.
Qed.

Theorem swap_if_branches:
  forall b e1 e2, cequiv (IFB b THEN e1 ELSE e2 FI) (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros b e1 e2 st st'.
  split; intros H.
    inversion H; subst.
      destruct b.