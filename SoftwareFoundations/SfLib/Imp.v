(**** Imp: Simple Imperative Programs ****)

Require Export SfLib.

(*** Arithmetic and Boolean Expressions ***)

(** Syntax **)

Module AExp.

Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

(** Evaluation **)

Fixpoint aeval (e : aexp) : nat :=
  match e with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof.
  reflexivity.
Qed.

Fixpoint beval (e : bexp) : bool :=
  match e with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
    | BLe a1 a2 => ble_nat (aeval a1) (aeval a2)
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

(** Optimization **)

Fixpoint optimize_0plus (e : aexp) : aexp :=
  match e with
    | ANum n => ANum n
    | APlus (ANum 0) e2 => optimize_0plus e2
    | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2) (APlus (ANum 0) (APlus (ANum 0) (ANum 1))))
  =
  APlus (ANum 2) (ANum 1).
Proof.
  reflexivity.
Qed.

Theorem optimize_0plus_sound:
  forall e, aeval (optimize_0plus e) = aeval e.
Proof.
  intro e. induction e.
    (* ANum *)
    simpl. reflexivity.
    (* APlus *)
    simpl. destruct e1.
      (* ANum*)
      simpl. destruct n.
        simpl. apply IHe2.
        simpl. rewrite IHe2. reflexivity.
      (* APlus *)
      simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
      (* AMinus *)
      simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
      (* AMult *)
      simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
    (* AMinus *)
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
    (* AMult *)
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

(*** Coq Automation ***)

(** Tacticals **)

(* The 'repeat' Tactical *)

Theorem ev100:
  ev 100.
Proof.
  repeat (apply ev_SS).
  apply ev_0.
Qed.

Theorem ev100':
  ev 100.
Proof.
  repeat (apply ev_0).
  repeat (apply ev_SS).
  apply ev_0.
Qed.

(* The 'try' Tactical *)

Theorem silly1:
  forall ae, aeval ae = aeval ae.
Proof.
  try reflexivity.
Qed.

Theorem silly2:
  forall (P: Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity.
  apply HP.
Qed.

(* The ';' Tactical (Simple Form) *)

Lemma foo:
  forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Lemma foo':
  forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n;
    simpl; reflexivity.
Qed.

Theorem optimize_0plus_sound':
  forall e, aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  induction e; try (simpl; rewrite IHe1; rewrite IHe2; reflexivity).
    (* ANum *)
    reflexivity.
    (* APlus *)
    destruct e1; try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
      (* ANum *)
      destruct n; simpl; rewrite IHe2; reflexivity.
Qed.

Theorem optimize_0plus_sound'':
  forall e, aeval (optimize_0plus e) = aeval e.
Proof.
  intros e.
  induction e;
    try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
    try reflexivity.
    (* APlus *)
    destruct e1;
      try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
      (* ANum *)
      destruct n; simpl; rewrite IHe2; reflexivity.
Qed.

(* The ';' Tactical (General Form) *)

(** Defining New Tactic Notations **)

Fixpoint optimize_0plus_b (e : bexp) : bexp :=
  match e with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
    | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
    | BNot b1 => BNot (optimize_0plus_b b1)
    | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound:
  forall e, beval (optimize_0plus_b e) = beval e.
Proof.
  intro e.
  induction e;
    try reflexivity;
    try (simpl; rewrite 2 optimize_0plus_sound; reflexivity).
    simpl. rewrite IHe. reflexivity.
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

(* 'aeval' and 'beval' form the most powerful optimizer and are trivally sound
    w.r.t themselves
 *)

(* The 'omega' Tactic *)

Example silly_presburger_example:
  forall m n o p, m + n <= n + o /\ o + 3 = p + 3 -> m <= p.
Proof.
  intros. omega.
Qed.

(* A Few More Handy Tactics *)

(*** Evaluation as a Relation ***)

Module aevalR_first_try.

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n : nat), aevalR (ANum n) n
  | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
                aevalR e1 n1 -> aevalR e2 n2 -> aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
                 aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
                aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMinus e1 e2) (n1 * n2).

  Notation "e '||' n" := (aevalR e n) : type_scope.

End aevalR_first_try.

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum : forall (n : nat), (ANum n) || n
| E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
              (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
| E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
               (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
| E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
              (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)
where "e '||' n" := (aevalR e n) : type_scope.

Theorem aeval_iff_aevalR:
  forall a n, (a || n) <-> aeval a = n.
Proof.
  split.
    intro H. induction H; simpl.
      reflexivity.
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    generalize dependent n.
    induction a; simpl; intros; subst.
      apply E_ANum.
      apply E_APlus.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
      apply E_AMinus.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
      apply E_AMult.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR':
  forall a n, (a || n) <-> aeval a = n.
Proof.
  split.
    intros H; induction H; subst; reflexivity.
    generalize dependent n. induction a; simpl; intros; subst; constructor;
                            try apply IHa1; try apply IHa2; reflexivity.
Qed.

Inductive bevalR : bexp -> bool -> Prop :=
| E_BTrue : BTrue || true
| E_BFalse : BFalse || false
| E_BEq : forall a1 a2 n1 n2, aevalR a1 n1 -> aevalR a2 n2 -> BEq a1 a2 || beq_nat n1 n2
| E_BLe : forall a1 a2 n1 n2, aevalR a1 n1 -> aevalR a2 n2 -> BLe a1 a2 || ble_nat n1 n2
| E_BNot : forall b p, b || p -> BNot b || negb p
| E_BAnd : forall b1 b2 p1 p2, b1 || p1 -> b2 || p2 -> BAnd b1 b2 || andb p1 p2
where "e '||' n" := (bevalR e n) : type_scope.

Theorem beval_iff_bevalR:
  forall b p, (b || p) <-> beval b = p.
Proof.
  split.
    intro H.
    induction H; simpl.

      reflexivity.

      reflexivity.

      assert (aeval a1 = n1).
        induction H;
          simpl; try (rewrite IHaevalR1); try (rewrite IHaevalR2); reflexivity.
      assert (aeval a2 = n2).
        induction H0; simpl;
          try (rewrite IHaevalR1); try (rewrite IHaevalR2); reflexivity.
      rewrite H1. rewrite H2. reflexivity.

      assert (aeval a1 = n1).
        induction H; simpl;
          try (rewrite IHaevalR1); try (rewrite IHaevalR2); reflexivity.
      assert (aeval a2 = n2).
        induction H0; simpl;
          try (rewrite IHaevalR1); try (rewrite IHaevalR2); reflexivity.
      rewrite H1. rewrite H2. reflexivity.

      rewrite IHbevalR. reflexivity.

      rewrite IHbevalR1. rewrite IHbevalR2. reflexivity.

    intro H. induction H; simpl.
      induction b; simpl.
        constructor.
        constructor.
        constructor; rewrite aeval_iff_aevalR; reflexivity.
        constructor; rewrite aeval_iff_aevalR; reflexivity.
        constructor. apply IHb.
        constructor. apply IHb1. apply IHb2.
Qed.

(** Inference Rule Notation **)

End AExp.

(*** Expression With Variables ***)

(** Identifiers **)

Module Id.

  Inductive id : Type :=
    Id : nat -> id.

  Definition beq_id X1 X2 :=
    match (X1, X2) with
        (Id n1, Id n2) => beq_nat n1 n2
    end.

  Theorem beq_id_refl:
    forall X, true = beq_id X X.
  Proof.
    intros.
    destruct X.
    apply beq_nat_refl.
  Qed.

  Theorem beq_id_false_not_eq:
    forall i1 i2, beq_id i1 i2 = false -> i1 <> i2.
  Proof.
    intros.
    destruct i1. destruct i2.
  Admitted. (* FIXME *)

  Theorem not_eq_beq_id_false:
    forall i1 i2, i1 <> i2 -> beq_id i1 i2 = false.
  Proof.
    intros.
    destruct i1. destruct i2. unfold not in H. unfold beq_id.
  Admitted. (* FIXME *)

  Theorem beq_id_sym:
    forall i1 i2, beq_id i1 i2 = beq_id i2 i1.
  Proof.
    intros. destruct i1. destruct i2. unfold beq_id. rewrite beq_nat_sym. reflexivity.
  Qed.

End Id.

(** States **)

Definition state := id -> nat.

Definition empty_state : state := fun _ => 0.

Definition update (st : state) (X : id) (n : nat) : state :=
  fun X' => if beq_id X X' then n else st X'.

Theorem update_eq:
  forall n X st, (update st X n) X = n.
Proof.
  intros n X st.
  unfold update.
  rewrite <- beq_id_refl.
  reflexivity.
Qed.

Theorem update_neq:
  forall V2 V1 n st, beq_id V2 V1 = false -> (update st V2 n) V1 = (st V1).
Proof.
  intros V2 V1 n st H.
  unfold update.
  rewrite H.
  reflexivity.
Qed.

Example update_example:
  forall (n : nat), (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  intros n.
  unfold update. simpl.
  unfold empty_state. reflexivity.
Qed.

Theorem update_shadow:
  forall x1 x2 k1 k2 (f : state),
    (update (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
  intros x1 x2 k1 k2 f.
  unfold update.
  destruct (beq_id k2 k1); reflexivity.
Qed.

Theorem update_same:
  forall x1 k1 k2 (f : state), f k1 = x1 -> (update f k1 x1) k2 = f k2.
Proof.
  intros x1 k1 k2 f H.
  unfold update.
Admitted. (* FIXME *)

Theorem update_permute:
  forall x1 x2 k1 k2 k3 f,
    beq_id k2 k1 = false ->
    (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
Proof.
  intros x1 x2 k1 k2 k3 f H.
  unfold update.
  remember (beq_id k1 k3) as Q1.
  remember (beq_id k2 k3) as Q2.
  destruct Q1. destruct Q2.
Admitted. (* FIXME *)

(** Syntax **)

Inductive aexp : Type :=
| ANum : nat -> aexp
| AId : id -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

(** Evaluation **)

Fixpoint aeval (st : state) (e : aexp) : nat :=
  match e with
    | ANum n => n
    | AId X => st X
    | APlus a1 a2 => (aeval st a1) + (aeval st a2)
    | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
    | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
    | BLe a1 a2 => ble_nat (aeval st a1) (aeval st a2)
    | BNot b1 => negb (beval st b1)
    | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Example aexp1:
  aeval (update empty_state X 5) (APlus (ANum 3) (AMult (AId X) (ANum 2))) = 13.
Proof.
  reflexivity.
Qed.

Example bexp1:
  beval (update empty_state X 5) (BAnd BTrue (BNot (BLe (AId X) (ANum 4)))) = true.
Proof.
  reflexivity.
Qed.

(*** Commands ***)

(** Syntax **)

Inductive com : Type :=
| CSkip : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com.

Notation "'SKIP'" := CSkip.
Notation "X '::=' a" := (CAss X a) (at level 60).
Notation "c1 ; c2" := (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := (CIf e1 e2 e3)
                                                  (at level 80, right associativity).

Definition fact_in_coq : com :=
  Z ::= AId X;
  Y ::= ANum 1;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
        Y ::= AMult (AId Y) (AId Z);
        Z ::= AMinus (AId Z) (ANum 1)
  END.

(** Exmaples **)

Definition plus2 : com := X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com := Z ::= (AMult (AId X) (AId Y)).

Definition substract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1);
  Z ::= AMinus (AId X) (ANum 1).

Definition substract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
        substract_slowly_body
  END.

Definition substract_3_from_5_slowly : com :=
  X ::= ANum 3;
  Z ::= ANum 5;
  substract_slowly.

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z);
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
        fact_body
  END.

Definition fact_com : com :=
  Z ::= AId X;
  Y ::= ANum 1;
  fact_loop.

(*** Evaluation ***)

(** Evaluation Function (Failed Attempt) **)

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
    | SKIP => st
    | l ::= a1 => update st l (aeval st a1)
    | c1 ; c2 => let st' := ceval_fun_no_while st c1 in ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI => if (beval st b)
                                  then ceval_fun_no_while st c1
                                  else ceval_fun_no_while st c2
    | WHILE b1 DO c1 END => if (beval st b1)
                            then (* ceval_fun_no_while st (c1; WHILE b1 DO c1 END *) admit
                            else st
  end.

(** Evaluation as a Relation **)

Reserved Notation "c1 '/' st || st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st, SKIP / st || st
| E_Ass : forall st a1 n X, aeval st a1 = n -> (X ::= a1) / st || (update st X n)
| E_Seq : forall c1 c2 st st' st'',
            c1 / st || st' -> c2 / st' || st'' -> (c1 ; c2) / st || st''
| E_IfTrue : forall st st' b1 c1 c2,
               beval st b1 = true -> c1 / st || st' ->
               (IFB b1 THEN c1 ELSE c2 FI) / st || st'
| E_IfFalse : forall st st' b1 c1 c2,
                beval st b1 = false -> c2 / st || st' ->
                (IFB b1 THEN c1 ELSE c2 FI) / st || st'
| E_WhileEnd : forall b1 st c1,
                 beval st b1 = false ->
                 (WHILE b1 DO c1 END) / st || st
| E_WhileLoop : forall st st' st'' b1 c1,
                  beval st b1 = true ->
                  c1 / st || st' ->
                  (WHILE b1 DO c1 END) / st' || st'' ->
                  (WHILE b1 DO c1 END) / st || st''
where "c1 '/' st '||' st'" := (ceval c1 st st').

Example ceval_example1:
  (X ::= ANum 2;
   IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
   FI)
  / empty_state
  || (update (update empty_state X 2) Z 4).
Proof.
  apply E_Seq with (update empty_state X 2).
    apply E_Ass. reflexivity.
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.
Qed.

Example ceval_example2:
  (X ::= ANum 0; Y ::= ANum 1; Z ::= ANum 2)
    / empty_state || (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (update empty_state X 0).
    apply E_Ass. reflexivity.
    apply E_Seq with (update (update empty_state X 0) Y 1).
      apply E_Ass. reflexivity.
      apply E_Ass. reflexivity.
Qed.

Definition pup_to_n : com :=
  Y ::= ANum 0;
  WHILE BLe (ANum 0) (AId X) DO
        Y ::= APlus (AId Y) (AId X);
        X ::= AMinus (AId X) (ANum 1)
  END.

Example pup_to_2_ceval:
  pup_to_n
    / (update empty_state X 2) ||
    update (update (update (update (update (update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  apply E_Seq with (update (update empty_state X 2) Y 0).
    apply E_Ass. reflexivity.
    apply E_WhileLoop with (update (update empty_state X 2) Y 0).
      reflexivity.
      apply E_Seq with (update (update (update empty_state X 2) Y 0) Y 2).
        apply E_Ass. reflexivity.
Admitted. (* FIXME *)


(** Determinist of Evaluation **)

Theorem ceval_deterministic:
  forall c st st1 st2, c / st || st1 -> c / st || st2 -> st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
    (* E_Skip *)
    reflexivity.
    (* E_Ass *)
    reflexivity.
    (* E_Seq *)
    assert (st' = st'0) as EQ1. apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2.
      assumption.
    (* E_IfTrue *)
    apply IHE1. assumption.
    rewrite H in H5. inversion H5.
    (* E_IfFalse *)
    rewrite H in H5. inversion H5.
    apply IHE1. assumption.
    (* E_WhileEnd *)
    reflexivity.
    rewrite H in H2. inversion H2.
    (* E_WhileLoop *)
    rewrite H in H4. inversion H4.
    assert (st' = st'0) as EQ1.
      apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption.
Qed.

(*** Reasoning About Programs ***)

(** Basic Examples **)

Theorem plus2_spec:
  forall st n st', st X = n -> plus2 / st || st' -> st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. simpl.
  apply update_eq.
Qed.

Theorem XtimesYinZ_spec:
  forall st x y st', st X = x -> st Y = y -> XtimesYinZ / st || st' -> st' Z = x * y.
Proof.
  intros st x y st' HX HY Heval.
  inversion Heval. subst. simpl.
  apply update_eq.
Qed.

Theorem loop_never_stops:
  forall st st', ~(loop / st || st').
Proof.
  intros st st' contra.
  unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef.
  induction loopdef; inversion Heqloopdef.
    subst. clear Heqloopdef.
    induction contra.
      apply IHloopdef.
        reflexivity.
        constructor.
      induction H.
Admitted. (* FIXME *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
    | SKIP => true
    | _ ::= _ => true
    | c1 ; c2 => andb (no_whiles c1) (no_whiles c2)
    | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
    | WHILE _ DO _ END => false
  end.

Inductive no_whilesR : com -> Prop :=
| NW_Skip : no_whilesR SKIP
| NW_Ass : forall X a, no_whilesR (X ::= a)
| NW_Seq : forall c1 c2, no_whilesR c1 -> no_whilesR c2 -> no_whilesR (c1 ; c2)
| NW_If : forall b c1 c2,
            no_whilesR c1 -> no_whilesR c2 -> no_whilesR (IFB b THEN c1 ELSE c2 FI).

Theorem no_whiles_eqv:
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  intro c.
  split.
    intro H. induction c.
      constructor.
      constructor.
      inversion H. apply andb_true_iff in H1. inversion H1. constructor.
        apply IHc1. apply H0.
        apply IHc2. apply H2.
      inversion H. apply andb_true_iff in H1. inversion H1. constructor.
        apply IHc1. apply H0.
        apply IHc2. apply H2.
      inversion H.
    intro H. induction c.
      reflexivity.
      reflexivity.
      simpl. inversion H. subst. apply andb_true_iff. split.
        apply IHc1. apply H2.
        apply IHc2. apply H3.
      simpl. inversion H. subst. apply andb_true_iff. split.
        apply IHc1. apply H2.
        apply IHc2. apply H4.
      inversion H.
Qed.

(* no_whiles_terminating *)

(** Proving a Program Correct (Optional) **)

Print fact_body.
Print fact_loop.
Print fact_com.

Fixpoint real_fact (n : nat) : nat :=
  match n with
    | O => 1
    | S n' => n * (real_fact n')
  end.

Definition fact_invariant (x : nat) (st : state) :=
  (st Y) * (real_fact (st Z)) = real_fact x.


      
