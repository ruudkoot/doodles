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
  5) The variable Z squared is less than or equal to the metavariable x
     and (Z + 1)^2 is greater than x.
  6) The property that always holds. The state can be anything.
  7) The property that never holds. There does not exists a state that satisfies it.
     (Note that non-terminating programs do not have a state either.)
*)

(** Hoare Triples **)

Definition hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st', c / st || st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(*
  1) After executing c in any state X will equal 5.
  2) After executing c in a state where X equals x, X will equal x + 5 in the
     resulting state.
  3) After executing c in a state where X <= Y, Y <= X in the resulting state.
  4) c never terminates (from any starting state).
  5) Y := X!
  6) ...
*)

(*
  1) valid
  2) valid
  3) valid
  4) valid (vacuously)
  5) invalid
  6) valid (vacuously)
  7) valid (non-termination)
  8) valid
  9) valid (non-terminiation)
*)

Theorem hoare_post_true:
  forall (P Q : Assertion) c, (forall st, Q st) -> {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.
Qed.

Theorem hoare_pre_false:
  forall (P Q : Assertion) c, (forall st, ~(P st)) -> {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.
Qed.

(** Weakest Preconditions **)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ~~> Q" := (assert_implies P Q) (at level 80).
Notation "P <~> Q" := (P ~~> Q /\ Q ~~> P) (at level 80).

(*
  1) X = 5
  2) Y = y /\ Z = z /\ y + z = 5
  3) True
  4) X = 0 => Z = 4 /\ X =/= 0 => W = 3
  5) False
  6) True
*)

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\ forall P', {{P'}} c {{Q}} -> (forall st, P' st -> P st).

Theorem is_wp_example:
  is_wp (fun st => st Y <= 4) (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
  unfold is_wp.
  split.
    (* => *)
      unfold hoare_triple. intros.
      inversion H. subst.
      unfold update. simpl.
      assert (forall x y, x <= y -> x + 1 <= S y) by (intros; omega).
      apply H1. assumption.
    (* <= *)
      unfold hoare_triple. intros.
Admitted. (* FIXME *)

(** Proof Rules **)

(* Assignment *)

Definition assn_sub X a Q : Assertion :=
  fun (st : state) => Q (update st X (aeval st a)).

Theorem hoare_asgn:
  forall Q X a, {{assn_sub X a Q}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.
Qed.

Example 