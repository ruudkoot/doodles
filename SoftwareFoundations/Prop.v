Require Export Poly.

(* Inductively Defined Propositions *)

(* varieties_of_beauty: an infinity number, due to the zero being neutral to sum *)

Inductive beautiful : nat -> Prop :=
  b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

Theorem three_is_beautiful: beautiful 3.
Proof.
  apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
  apply b_sum with (n := 3) (m := 5).
    apply b_3.
    apply b_5.
Qed.

(* Proof Objects *)

Check (b_sum 3 5 b_3 b_5).

Theorem eight_is_beautiful': beautiful 8.
Proof.
  apply (b_sum 3 5 b_3 b_5).
Qed.

(** Proof Scripts and Proof Objects **)

Theorem eight_is_beautiful'': beautiful 8.
Proof.
  apply b_sum with (n:=3) (m:=5).
  Show Proof.
  apply b_3.
  Show Proof.
  apply b_5.
  Show Proof.
Qed.

Definition eight_is_beautiful''' : beautiful 8 := b_sum 3 5 b_3 b_5.

Print eight_is_beautiful.
Print eight_is_beautiful'.
Print eight_is_beautiful''.
Print eight_is_beautiful'''.

Theorem six_is_beautiful: beautiful 6.
Proof.
  apply b_sum with (n:=3) (m:= 3).
    apply b_3.
    apply b_3.
Qed.

Definition six_is_beautiful' : beautiful 6 := b_sum 3 3 b_3 b_3.
Definition six_is_beautiful'': beautiful 6 := b_sum _ _ b_3 b_3.

Theorem nine_is_beautiful: beautiful 9.
Proof.
  apply b_sum with (n := 3) (m := 6).
    apply b_3.
    apply b_sum with (n := 3) (m := 3).
      apply b_3.
      apply b_3.
Qed.

Definition nine_is_beautiful' : beautiful 9 := b_sum 3 6 b_3 (b_sum 3 3 b_3 b_3).
Definition nine_is_beautiful'': beautiful 9 := b_sum _ _ (b_sum _ _ b_3 b_3) b_3.

(** Implications and Functions **)

Theorem b_plus3: forall n, beautiful n -> beautiful (3+n).
Proof.
  intros n H. apply b_sum. apply b_3. apply H.
Qed.

Print b_plus3.

Definition b_plus3' : forall n, beautiful n -> beautiful (3+n) :=
  fun n => fun H : beautiful n =>
             b_sum 3 n b_3 H.

Check b_plus3'.

Definition b_plus3'' (n : nat) (H: beautiful n) : beautiful (3+n) :=
  b_sum 3 n b_3 H.

Check b_plus3''.

Theorem test: forall n, n + 0 = n.
Proof.
  intros. rewrite plus_0_r. reflexivity.
Qed.

Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
  intros. simpl. rewrite plus_0_r. apply b_sum; apply H.
Defined.

Print b_times2.

Definition b_times2': forall n, beautiful n -> beautiful (2*n) :=
  fun n => fun H : beautiful n =>
             match eq_sym (plus_0_r n) in (_ = n') return (beautiful (n + n')) with
               | eq_refl => b_sum n n H H
             end.

Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  intros. induction m.
    simpl. apply b_0.
    simpl. apply b_sum.
      apply H.
      apply IHm.
Qed.

