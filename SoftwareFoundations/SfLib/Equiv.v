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
      apply E_IfFalse.
        simpl. rewrite negb_false_iff. assumption.
        assumption.
      apply E_IfTrue.
        simpl. rewrite negb_true_iff. assumption.
        assumption.
    inversion H; subst.
      apply E_IfFalse.
        simpl in H5. rewrite negb_true_iff in H5. assumption.
        assumption.
      apply E_IfTrue.
        simpl in H5. rewrite negb_false_iff in H5. assumption.
        assumption.
Qed.

Theorem WHILE_false:
  forall b c, bequiv b BFalse -> cequiv (WHILE b DO c END) SKIP.
Proof.
  intros b c Hb.
  split; intros H.
    inversion H; subst.
      apply E_Skip.
      rewrite Hb in H2. inversion H2.
    inversion H; subst.
      apply E_WhileEnd. rewrite Hb. reflexivity.
Qed.

Lemma WHILE_true_nonterm:
  forall b c st st', bequiv b BTrue -> ~(WHILE b DO c END / st || st').
Proof.
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw.
  induction H; inversion Heqcw; subst; clear Heqcw.
    rewrite Hb in H. inversion H.
    apply IHceval2. reflexivity.
Qed.

Theorem WHILE_true:
  forall b c, bequiv b BTrue -> cequiv (WHILE b DO c END) (WHILE BTrue DO SKIP END).
Proof.
  intros b c Hb.
  split; intros H.
    inversion H; subst.
      rewrite Hb in H4. inversion H4.
      apply WHILE_true_nonterm in H6.
        inversion H6.
        assumption.
    inversion H; subst.
      inversion H4.
      apply WHILE_true_nonterm in H6.
        inversion H6.
        unfold bequiv. intros st0. reflexivity.
Qed.

Theorem loop_unrolling:
  forall b c, cequiv (WHILE b DO c END) (IFB b THEN (c; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros b c st st'.
  split; intros Hce.
    inversion Hce; subst.
      apply E_IfFalse. assumption. apply E_Skip.
      apply E_IfTrue. assumption. apply E_Seq with (st' := st'0). assumption. assumption.
    inversion Hce; subst.
      inversion H5; subst.
      apply E_WhileLoop with (st' := st'0).
        assumption.
        assumption.
        assumption.
      inversion H5; subst. apply E_WhileEnd. assumption.
Qed.

Theorem seq_assoc:
  forall c1 c2 c3, cequiv ((c1; c2); c3) (c1; (c2; c3)).
Proof.
  intros c1 c2 c3.
  split; intros H.
    