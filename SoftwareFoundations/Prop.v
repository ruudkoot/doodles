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

