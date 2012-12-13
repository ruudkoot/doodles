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

Theorem ev__even : forall n, ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
    unfold even. reflexivity.
    unfold even. apply IHE'.
Qed.

Theorem ev__even_FAILED : forall n, ev n -> even n.
  intros n. induction n.
    intros E. unfold even. reflexivity.
    intros E. unfold even. (* FIXME: can we go further here? *)
Abort.

Theorem l : forall n, ev n.
Proof.
  intros n. induction n.
    apply ev_0.
    (* If n is even (induction hypothesis) then n + 1 (the goal) will not be. *)
Abort.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n+m).
Proof.
  intros n m H1 H2. induction H1.
    simpl. apply H2.
    simpl. apply ev_SS. apply IHev.
Qed.

Theorem SSev_ev_firsttry : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. destruct E.
  (* Stuck: destruct gives us an unprovable subgoal. *)
Abort.

Theorem SSev_ev_secondtry: forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. remember (S (S n)) as n2.
  destruct E.
    inversion Heqn2.
    inversion Heqn2. rewrite <- H0. apply E.
Qed.

Theorem SSev__even: forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. apply E'.
Qed.

Print SSev__even.

Theorem SSSSev__even: forall n, ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. inversion E' as [| n'' E'']. apply E''.
Qed.

Theorem even5_nonsense: ev 5 -> 2 + 2 = 9.
Proof.
  intros H. inversion H as [| n' H']. inversion H' as [| n'' H'']. inversion H''.
Qed.

Theorem ev_minus2': forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E. inversion E as [| n' E'].
    simpl. apply ev_0.
    simpl. apply E'.
Qed.

Theorem ev_ev__ev : forall n m, ev (n+m) -> ev n -> ev m.
Proof.
Abort. (* FIXME *)

Theorem ev_plus_plus: forall n m p, ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
Abort. (* FIXME *)

(* Programming with Propositions *)

Check (2 + 2 = 4).
Check (ble_nat 3 2 = false).
Check (beautiful 8).

Check (2 + 2 = 5).
Check (beautiful 4).

Theorem plus_2_2_is_4: 2 + 2 = 4.
Proof.
  reflexivity.
Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true: plus_fact.
Proof.
  reflexivity.
Qed.

Definition strange_prop1 : Prop := (2 + 2 = 5) -> (99 + 26 = 42).
Definition strange_prop2 : Prop :=
  forall n, (ble_nat n 17 = true) -> (ble_nat n 99 = true).

Check even.
Check (even 4).
Check (even 3).

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

Definition teen : nat->Prop := between 13 19.

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

Definition true_for_al_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(* Induction Principles *)

(** Induction Principles for Inductively Defined Types **)

Check nat_ind.

Theorem mult_0_r' : forall n:nat, n * 0 = 0.
Proof.
  apply nat_ind.
    reflexivity.
    simpl. intros n IHn. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_one_r' : forall n:nat, n + 1 = S n.
Proof.
  apply nat_ind.
    reflexivity.
    simpl. intros n H. apply eq_remove_S. apply H.
Qed.

Inductive yesno : Type :=
| yes : yesno
| no :yesno.

Check yesno_ind.

Inductive rgb : Type :=
| red : rgb
| green : rgb
| blue : rgb.

(* rgb_ind : forall P : rgb -> Prop, P red -> P green -> P blue -> forall c : rgb, P c *)

Check rgb_ind.

Inductive natlist : Type :=
| nnil : natlist
| ncons : nat -> natlist -> natlist.

Check natlist_ind.

Inductive natlist1 : Type :=
| nnil1 : natlist1
| nsnoc1 : natlist1 -> nat -> natlist1.

(* natlist1_ind : forall P : natlist1 -> Prop, P nnil1 -> (forall (n : nat) (n0 : natlist1), P n0 -> P (ncons n0 n)) -> forall n : natlist1, P n *)

Check natlist1_ind.