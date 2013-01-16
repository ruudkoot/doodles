(*** From the Coq Standard Library ***)

Require Omega.
Require Export Bool.
Require Export List.
Require Export Arith.
Require Export Arith.EqNat.

(*** From Basics.v ***)

Definition admit {T: Type} : T. Admitted.

Require String. Open Scope string_scope.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O => true
    | S n' =>
      match m with
        | O => false
        | S m' => ble_nat n' m'
      end
  end.

Theorem andb_true_elim1:
  forall b c, andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
    reflexivity.
    rewrite <- H. reflexivity.
Qed.

Theorem andb_true_elim2:
  forall b c, andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      reflexivity.
      rewrite <- H. reflexivity.
    destruct c.
      reflexivity.
      rewrite <- H. reflexivity.
Qed.

Theorem beq_nat_sym:
  forall (n m : nat), beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n.
    destruct m.
      reflexivity.
      reflexivity.
    destruct m.
      reflexivity.
      apply IHn.
Qed.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

(* From Props.v *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall (n : nat), ev n -> ev (S (S n)).

(*** From Logic.v ***)

Theorem andb_true:
  forall b c, andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      apply conj. reflexivity. reflexivity.
      inversion H.
    inversion H.
Qed.

Theorem not_eq_beq_false:
  forall (n n' : nat), n <> n' -> beq_nat n n' = false.
Proof.
  intros n. induction n.
    intros n' H. induction n'.
      unfold not in H.
        assert False.
          apply H. reflexivity.
        inversion H0.
      reflexivity.
    intros n' H. induction n'.
      reflexivity.
      apply IHn. unfold not in H.
        assert False.
          apply H.
Admitted. (*** FIXME ***)

Theorem ex_falso_quodlibet:
  forall (P : Prop), False -> P.
Proof.
  intros P contra. inversion contra.
Qed.

Theorem ev_not_ev_S:
  forall n, ev n -> ~ ev (S n).
Proof.
Admitted. (* FIXME *)

Theorem ble_nat_false:
  forall n m, ble_nat n m = false -> ~(n <= m).
Admitted.

Inductive appears_in (n : nat) : list nat -> Prop :=
| ai_here : forall l, appears_in n (n::l)
| ai_there : forall m l, appears_in n l -> appears_in n (m::l).

Inductive next_nat (n:nat) : nat -> Prop :=
| nn : next_nat n (S n).

Inductive total_relation : nat -> nat -> Prop :=
| tot : forall n m : nat, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .

(*** From Later Files ***)

Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive multi (X : Type) (R : relation X) : X -> X -> Prop :=
| multi_refl : forall (x : X), multi X R x x
| multi_step : forall (x y z : X), R x y -> multi X R y z -> multi X R x z.

Implicit Arguments multi [[X]].

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X), R x y -> multi R x y.
Proof.
  intros X R x y r.
  apply multi_step with y.
  apply r.
  apply multi_refl.
Qed.

Theorem mutli_trans:
  forall (X : Type) (R : relation X) (x y z : X),
    multi R x y -> multi R y z -> multi R x z.
Proof.
  intros X R x y z Hxy Hyz.
  inversion Hyz.
    rewrite H0 in Hxy. apply Hxy.
    inversion Hxy.
      apply Hyz.
Admitted. (* FIXME *)

(* Identifiers and polymorphic partial maps. *)

Inductive id : Type := Id : nat -> id.

Definition beq_id id1 id2 :=
  match (id1, id2) with
      (Id n1, Id n2) => beq_nat n1 n2
  end.

Theorem beq_id_refl:
  forall i, true = beq_id i i.
Proof.
  intro i. destruct i.
    apply beq_nat_refl.
Qed.

Theorem beq_id_eq:
  forall i1 i2, true = beq_id i1 i2 -> i1 = i2.
Proof.
  intros i1 i2 H.
  destruct i1.
    destruct i2.
      apply beq_nat_eq in H. subst. reflexivity.
Qed.

(* FIXME: Copied from here on. *)

Theorem beq_id_false_not_eq : forall i1 i2,
  beq_id i1 i2 = false -> i1 <> i2.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  apply beq_nat_false in H.
  intros C. apply H. inversion C. reflexivity. Qed.

Theorem not_eq_beq_id_false : forall i1 i2,
  i1 <> i2 -> beq_id i1 i2 = false.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  assert (n <> n0).
    intros C. subst. apply H. reflexivity.
  apply not_eq_beq_false. assumption. Qed.

Theorem beq_id_sym: forall i1 i2,
  beq_id i1 i2 = beq_id i2 i1.
Proof.
  intros i1 i2. destruct i1. destruct i2. apply beq_nat_sym. Qed.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None).

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if beq_id x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite <- beq_id_refl. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  beq_id x2 x1 = false ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite H. auto.
Qed.

Lemma extend_shadow : forall A (ctxt: partial_map A) t1 t2 x1 x2,
  extend (extend ctxt x2 t1) x2 t2 x1 = extend ctxt x2 t2 x1.
Proof with auto.
  intros. unfold extend. destruct (beq_id x2 x1). reflexivity. reflexivity.
Qed.

(*** Some useful tactis ***)

Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; t ]
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.