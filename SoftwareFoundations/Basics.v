(* Enumerated Types *)

(** Days of the Week **)

Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
  end.

Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday saturday)).

Example test_next_weekdat:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

(** Booleans **)

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Definition admit {T: Type} : T. Admitted.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | false => true
    | true => negb b2
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
    | true => match b2 with
                | true => b3
                | false => false
              end
    | false => false
  end.


Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(** Function Types **)

Check true.
Check (negb true).
Check negb.

(** Numbers **)

Module Playground1.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Definition pref (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. simpl. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Eval simpl in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
    | O , _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorail2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y)
                      (at level 40, left associativity) : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
    | O => match m with
             | O => true
             | S m' => false
           end
    | S n' => match m with 
                | O => false
                | S m' => beq_nat n' m'
              end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O => true
    | S n' =>
      match m with
        | O => false
        | S m' => ble_nat n' m'
      end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  ble_nat (S n) m.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* Proof By Simplification *)

Theorem plus_O_n : forall n:nat, 0 + n = n.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n' : forall n:nat, 0 + n = n.
Proof. reflexivity. Qed.

Eval simpl in (forall n:nat, n + 0 = n).
Eval simpl in (forall n:nat, 0 + n = n).

(* The 'intros' tactic *)

Theorem plus_O_n'' : forall n:nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof. intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof. intros n. reflexivity. Qed.

(* Proof by Rewriting *)

Theorem plus_id_example : forall n m:nat, n = m -> n + n = m + m.
Proof. intros n m. intros H. rewrite -> H. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat, n = m -> m = o -> n + m = m + o.
Proof. intros n m o. intros H1 H2. rewrite -> H1. rewrite -> H2. reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat, (0 + n) * m = n * m.
Proof. intros n m. rewrite -> plus_O_n. reflexivity. Qed.

Theorem mult_1_plus : forall n m : nat, (1 + n) * m = m + (n * m).
Proof. intros n m. rewrite -> plus_1_l. reflexivity. Qed.

(* Case Analysis *)

Theorem plus_1_neq_0_firsttry : forall n : nat, beq_nat (n + 1) 0 = false.
Proof. intros n. simpl. Abort.

Theorem plus_1_neq_0 : forall n : nat, beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.

Theorem negb_involutive : forall b : bool, negb (negb b) = b.
Proof.
  intros b. destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat, beq_nat 0 (n + 1) = false.
Proof.
  intros n. destruct n as [|n']; reflexivity.
Qed.

(* Naming Cases *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool, andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
  reflexivity.
  Case "b = false".
  rewrite <- H. reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool, andb b c = true -> c = true.
Proof.
  intros.
  destruct b.
  Case "b = true".
  rewrite <- H. reflexivity.
  Case "b = false".
  destruct c.
  SCase "c = true".
  reflexivity.
  SCase "c = false".
  rewrite <- H. reflexivity.
Qed.

(* Induction *)

Theorem plus_0_r_firsttry : forall n : nat, n + 0 = n.
Proof.
  intros. simpl.
Abort.

Theorem plus_0_r_secondtry : forall n : nat, n + 0 = n.
Proof.
  intros. destruct n.
  reflexivity.
  simpl.
Abort.

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [|n'].
  reflexivity.
  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n, minus n n = 0.
Proof.
  intros n. induction n as [|n'].
  simpl. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n:nat, n * 0 = 0.
Proof.
  intros. induction n.
  reflexivity.
  simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros. induction n.
  reflexivity.
  simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros. induction n.
  simpl. rewrite plus_0_r. reflexivity.
  simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
    | O => O
    | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros. induction n.
  reflexivity.
  simpl. rewrite IHn. rewrite -> plus_n_Sm. reflexivity.
Qed.

(* Formal vs. Informal Proof *)

Theorem plus_assoc' : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros. induction n.
  reflexivity.
  simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n'].
  Case "n = 0".
  reflexivity.
  Case "n = S n'".
  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem beq_nat_refl: forall n : nat, true = beq_nat n n. 
Proof.
  intros. induction n.
  reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

(* Proofs Within Proofs *)

Theorem mult_0_plus' : forall n m : nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). reflexivity.
  rewrite -> H. reflexivity.
Qed.

Theorem plus_rearrange_firsttry :
  forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros. rewrite -> plus_comm.
Abort.

Theorem plus_rearrange:
  forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros.
  assert (H: n + m = m + n). rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros.
  assert (H: m + p = p + m). rewrite plus_comm. reflexivity.
  rewrite H. rewrite plus_assoc. rewrite plus_comm. reflexivity.
Qed.

Lemma mult_m_Sn : forall m n : nat, m * S n = m * n + m.
Proof.
  intros. induction m.
  reflexivity.
  simpl. rewrite IHm. rewrite 2 plus_n_Sm. rewrite plus_assoc. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat, m * n = n * m.
Proof. (* FIXME: did not use plus_swap *)
  intros. induction n as [n|n'].
  rewrite mult_0_r. reflexivity.
  simpl. rewrite <- IHn'. rewrite mult_m_Sn. rewrite plus_comm. reflexivity.
Qed.

Theorem evenb_n__oddb_Sn : forall n : nat, evenb n = negb (evenb (S n)).
Proof.
  intros. induction n.
  reflexivity.
  assert (H: evenb (S (S n)) = evenb n). reflexivity.
  rewrite H. rewrite IHn. rewrite negb_involutive. reflexivity.
Qed.

(* More Exercises *)

Theorem ble_nat_refl : forall n:nat, true = ble_nat n n.
Proof.
  intros. induction n.
  reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n : nat, beq_nat 0 (S n) = false.
Proof.
  intros. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool, andb b false = false.
Proof.
  intros. destruct b; reflexivity.
Qed.

Theorem plus_ble_compat_l:
  forall n m p : nat, ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros. induction p; assumption.
Qed.

Theorem S_nbeq_0 : forall n:nat, beq_nat (S n) 0 = false.
Proof.
  reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros. simpl. rewrite plus_0_r. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool, orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  intros. destruct b, c; reflexivity.
Qed.

Lemma plus_nmp_npm : forall n m p : nat, n + m + p = n + p + m.
Proof.
  intros. rewrite <-2 plus_assoc.
  assert (H: p + m = m + p). rewrite plus_comm. reflexivity.
  rewrite H. reflexivity.
Qed.

Theorem mult_plus_distr_r :  forall n m p : nat, (n + m) * p = (n * p) + (m * p).
Proof. (* FIXME: ugly proof *)
  intros. induction p.
  rewrite -> mult_comm. simpl. rewrite mult_comm. simpl. rewrite mult_comm. reflexivity.
  rewrite mult_m_Sn. rewrite IHp. rewrite 2 mult_m_Sn. rewrite 2 plus_assoc.
  assert (H: n * p + m * p + n = n * p + n + m * p). rewrite plus_nmp_npm. reflexivity.
  rewrite H. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat, n * (m * p) = (n * m) * p.
Proof.
  intros. induction n.
  reflexivity.
  simpl. rewrite IHn. rewrite mult_plus_distr_r. reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros.
  replace (m + p) with (p + m). rewrite plus_assoc. rewrite plus_comm. reflexivity.
  rewrite plus_comm. reflexivity.
Qed.

Theorem bool_fn_applied_thrice : forall (f : bool -> bool) (b : bool), f (f (f b)) = f b.
Proof.
  intros. destruct b.
  remember (f true) as ftrue. destruct ftrue.
  rewrite <-2 Heqftrue. reflexivity.
  remember (f false) as ffalse. destruct ffalse.
  rewrite <- Heqftrue. reflexivity.
  rewrite <- Heqffalse. reflexivity.
  remember (f false) as ffalse. destruct ffalse.
  remember (f true) as ftrue. destruct ftrue.
  rewrite <- Heqftrue. reflexivity.
  rewrite <- Heqffalse. reflexivity.
  rewrite <-2 Heqffalse. reflexivity.
Qed.

Module Binary.

Inductive bin : Type :=
| zero : bin
| tw : bin -> bin
| tw_p1 : bin -> bin.

Fixpoint incr (b:bin) : bin :=
  match b with
    | zero => tw_p1 zero
    | tw b' => tw_p1 b'
    | tw_p1 b' => tw (incr b')
  end.

Fixpoint bin_to_nat (b:bin) : nat :=
  match b with
    | zero => O
    | tw b' => double (bin_to_nat b')
    | tw_p1 b' => S (double (bin_to_nat b'))
  end.

Theorem incr__bin_to_nat__comm : forall b : bin, bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros. induction b.
  reflexivity.
  reflexivity.
  simpl. rewrite IHb.
  assert (H: forall n : nat, double (S n) = S (S (double n))). reflexivity.
  rewrite H. reflexivity.
Qed.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
    | O => zero
    | S n' => incr (nat_to_bin n')
  end.

Theorem nat_to_bin_to_nat__id : forall n : nat, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros. induction n.
  reflexivity.
  simpl. rewrite incr__bin_to_nat__comm. rewrite IHn. reflexivity.
Qed.

Module BinaryInverse.

(* Representation of 0 is not unique. *)

Lemma nat_to_bin__double : forall n : nat, nat_to_bin (double n) = tw (nat_to_bin n).
Proof.
  intros. induction n.
  simpl. (* zero = tw zero *) admit.
  simpl.

Admitted.

Theorem bin_to_nat_to_bin__id : forall b : bin, nat_to_bin (bin_to_nat b) = b.
Proof.
  intros. induction b.
  reflexivity.
  simpl. rewrite nat_to_bin__double. rewrite IHb. reflexivity.
Abort.

End BinaryInverse.

Fixpoint normalize (b : bin) : bin :=
  match b with
    | zero => zero
    | tw zero => zero
    | tw b' => tw (normalize b')
    | tw_p1 b' => tw_p1 (normalize b')
  end.

Lemma tw_incr__incr_incr_tw:
  forall b : bin, tw (incr b) = incr (incr (tw b)).
Proof.
  intros. destruct b; reflexivity.
Qed.

Lemma twp1_incr__incr_incr_twp1:
  forall b : bin, tw_p1 (incr b) = incr (incr (tw_p1 b)).
Proof.
  intros. destruct b; reflexivity.
Qed.

Lemma incr_twp1__tw_incr:
  forall b : bin, incr (tw_p1 b) = tw (incr b).
Proof.
  intros. destruct b; reflexivity.
Qed.

Lemma normalize_incr__incr_normalize:
  forall b : bin, normalize (incr b) = incr (normalize b).
Proof.
  intros. induction b.
  reflexivity.
  destruct b; reflexivity.
  rewrite incr_twp1__tw_incr. destruct b.
  reflexivity.
  (* FIXME *)
Admitted.

Lemma nat_to_bin__double:
  forall (n : nat), nat_to_bin (double n) = normalize (tw (nat_to_bin n)).
Proof.
  intros. induction n.
  reflexivity.
  simpl (nat_to_bin (double (S n))). rewrite IHn.
  simpl (nat_to_bin (S n)).
  rewrite tw_incr__incr_incr_tw.
  rewrite 2 normalize_incr__incr_normalize.
  reflexivity.
Qed.

End Binary.

Module Decreasing.
(*
Fixpoint terminating_function_that_does_not_pass_termination_checker (n : nat) : bool :=
  match evenb n with
    | true => true
    | false => does_not_pass_termination_checker (S n)
  end.
*)
End Decreasing.