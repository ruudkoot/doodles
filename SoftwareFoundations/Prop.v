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

(** Induction Over Proof Objects **)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(*                   gorgeous n                gorgeous n
   ---------- [g_0]  -------------- [g_plus3]  -------------- [g_plus5]
   gorgeous 0        gorgeous (3+n)            gorgeous (5+n)           *)

Theorem gorgeous__beautiful : forall n, gorgeous n -> beautiful n.
Proof.
  intros. induction H.
    apply b_0.
    apply b_sum. apply b_3. apply IHgorgeous.
    apply b_sum. apply b_5. apply IHgorgeous.
Qed.

Theorem gorgeous__beautiful_FAILED : forall n, gorgeous n -> beautiful n.
Proof.
  intros. induction n.
    apply b_0.
Abort.

Theorem gorgeous_plus13: forall n, gorgeous n -> gorgeous (13+n).
Proof.
  intros. apply g_plus3. apply g_plus5. apply g_plus5. apply H.
Qed.

Definition gorgeous_plus13_po: forall n, gorgeous n -> gorgeous (13+n) :=
  fun n => fun H : gorgeous n => g_plus3 _ (g_plus5 _ (g_plus5 _ H)).

Theorem gorgeous_sum : forall n m, gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros. induction H.
    apply H0.
    rewrite <- plus_assoc. apply g_plus3. apply IHgorgeous.
    rewrite <- plus_assoc. apply g_plus5. apply IHgorgeous.
Qed.

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros. induction H.
    exact g_0.
    exact (g_plus3 _ g_0).
    exact (g_plus5 _ g_0).
    apply gorgeous_sum; assumption.
Qed.

Lemma helper_g_times : forall x y z, x + (z + y) = z + x + y.
Proof.
  intros x y z.
  rewrite plus_swap.
  rewrite plus_assoc.
  reflexivity.
Qed.

Theorem g_times2 : forall n, gorgeous n -> gorgeous (2*n).
Proof.
  intros n H. simpl.
  induction H.
    apply g_0.
    rewrite 2 helper_g_times. simpl. apply g_plus3. apply g_plus3.
      rewrite <- plus_assoc. apply IHgorgeous.
    rewrite 2 helper_g_times. simpl. apply g_plus5. apply g_plus5.
      rewrite <- plus_assoc. apply IHgorgeous.
Qed.

(** Evenness **)

Definition even (n:nat) : Prop :=
  evenb n = true.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem double_even : forall n, ev (double n).
Proof.
  intros. induction n.
    apply ev_0.
    simpl. apply ev_SS. apply IHn.
Qed.

Print double_even.

Definition double_even_pfobj : forall n, ev (double n) :=
  fun n => nat_ind (fun n' => ev (double n'))
                   ev_0
                   (fun _ IHn => ev_SS _ IHn)
                   n.

(** Inverting Evidence **)

Theorem ev_minus2: forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E.
    apply ev_0.
    apply E.
Qed.

Theorem ev_minus2_FAILED: forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct n.
    apply ev_0.
    destruct n.
      apply ev_0.
      simpl. (* FIXME: can we go further here? *)
Abort.