(**** Types: Type Systems ****)

(* 'auto' doens't seem to be as powerful as the book suggests.
   Did we forget to add some stuff to the hints database?      *)

Require Export Smallstep.

(*** More Automation ***)

(** The 'auto' and 'eauto' Tactics **)

Example auto_example_1:
  forall P Q R S T U : Prop,
    (P -> Q) ->
    (P -> Q) ->
    (T -> R) ->
    (S -> T -> U) ->
    ((P -> Q) -> (P -> S)) ->
    T ->
    P ->
    U.
Proof.
  auto.
Qed.

Lemma auto_example_2:
  forall P Q R : Prop, Q -> (Q -> R) -> P \/ (Q /\ R).
Proof.
  auto.
Qed.

Lemma auto_example_2a:
  forall P Q R : Prop, Q -> (Q -> R) -> P \/ (Q /\ R).
Proof.
  auto using conj, or_introl, or_intror.
Qed.

Hint Constructors multi.
Hint Resolve beq_id_eq beq_id_false_not_eq.

(** The 'Proof with' Tactic **)

(** The 'solve by inversion' Tactic **)

(** The 'try solve' Tactic **)

(** The 'f_equal' Tactic **)

(** The 'normalize' Tactic **)

Definition amultistep st := multi (astep st).
Notation " t '/' st '==>a*' t' " := (amultistep st t t') (at level 40, st at level 39).

Example astep_example1:
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4)))  / empty_state ==>a* (ANum 15).
Proof.
  apply multi_step with (APlus (ANum 3) (ANum 12)).
    apply AS_Plus2.
      apply av_num.
      apply AS_Mult.
  apply multi_step with (ANum 15).
    apply AS_Plus.
  apply multi_refl.
Qed.

Hint Constructors astep aval.

Example astep_example1':
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4)))  / empty_state ==>a* (ANum 15).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize" := 
   repeat (print_goal; eapply multi_step ; 
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply multi_refl.

Example astep_example1'':
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4)))  / empty_state ==>a* (ANum 15).
Proof.
  normalize.
Qed.

Example astep_example1''':
  exists e', (APlus (ANum 3) (AMult (ANum 3) (ANum 4)))  / empty_state ==>a* e'.
Proof.
  eapply ex_intro. normalize.
Qed.

Theorem normalize_ex:
  exists e', (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state ==>a* e'.
Proof.
  eapply ex_intro. normalize.
Qed.

Theorem normalize_ex':
  exists e', (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state ==>a* e'.
Proof.
  apply ex_intro with (ANum 6).
  normalize.
Qed.

(*** Types Arithmetic Expressions ***)

(** Syntax **)

Inductive tm : Type :=
| ttrue : tm
| tfalse : tm
| tif : tm -> tm -> tm -> tm
| tzero : tm
| tsucc : tm -> tm
| tpred : tm -> tm
| tiszero : tm -> tm.

Inductive bvalue : tm -> Prop :=
| bv_true : bvalue ttrue
| bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
| nv_zero : nvalue tzero
| nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t : tm) := bvalue t \/ nvalue t.

(** Operational Semantics **)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_IfTrue : forall t1 t2, (tif ttrue t1 t2) ==> t1
| ST_IfFalse : forall t1 t2, (tif tfalse t1 t2) ==> t2
| ST_If : forall t1 t1' t2 t3, t1 ==> t1' -> (tif t1 t2 t3) ==> (tif t1' t2 t3)
| ST_Succ : forall t1 t1', t1 ==> t1' -> (tsucc t1) ==> (tsucc t1')
| ST_PredZero : (tpred tzero) ==> tzero
| ST_PredSucc : forall t1, nvalue t1 -> (tpred (tsucc t1)) ==> t1
| ST_Pred : forall t1 t1', t1 ==> t1' -> (tpred t1) ==> (tpred t1')
| ST_IszeroZero : (tiszero tzero) ==> ttrue
| ST_IszeroSucc : forall t1, nvalue t1 -> (tiszero (tsucc t1)) ==> tfalse
| ST_Iszero : forall t1 t1', t1 ==> t1' -> (tiszero t1) ==> (tiszero t1')
where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

(** Normal Forms and Values **)

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

Example some_term_is_stuck:
  exists t, stuck t.
Proof.
  exists (tsucc ttrue). unfold stuck. split.
    unfold normal_form. unfold not. intro H.
      inversion H. inversion H0. subst. inversion H2.
    unfold not. intros H. inversion H. inversion H0. inversion H0. subst. inversion H2.
Qed.

Lemma value_is_nf:
  forall t, value t -> step_normal_form t.
Proof.
  intros t H.
  induction H.
    inversion H; subst.
      intros E. inversion E. inversion H0.
      intros E. inversion E. inversion H0.
      induction t; try solve by inversion.
        intros E. inversion E. inversion H0.
        intros E. inversion E. inversion H0. subst.
Admitted. (* FIXME *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
Admitted. (* FIXME *)

(** Typing **)

Inductive ty : Type :=
| TBool : ty
| TNat : ty.

Inductive has_type : tm -> ty -> Prop :=
| T_True : has_type ttrue TBool
| T_False : has_type tfalse TBool
| T_If : forall t1 t2 t3 T, has_type t1 TBool -> has_type t2 T -> has_type t3 T ->
                            has_type (tif t1 t2 t3) T
| T_Zero : has_type tzero TNat
| T_Succ : forall t1, has_type t1 TNat -> has_type (tsucc t1) TNat
| T_Pred : forall t1, has_type t1 TNat -> has_type (tpred t1) TNat
| T_Iszero : forall t1, has_type t1 TNat -> has_type (tiszero t1) TBool.

Hint Constructors has_type.

(* Examples *)

Example has_type_1:
  has_type (tif tfalse tzero (tsucc tzero)) TNat.
Proof.
  auto.
Qed.

Example has_type_not:
  ~ has_type (tif tfalse tzero ttrue) TBool.
Proof.
  intros Contra. solve by inversion 2.
Qed.

Example succ_hastype_nat__hastype_nat:
  forall t, has_type (tsucc t) TNat -> has_type t TNat.
Proof.
  intros t H.
  inversion H.
  assumption.
Qed.

(** Progress **)

Theorem progress:
  forall t T, has_type t T -> value t \/ exists t', t ==> t'.
Proof with auto.
  intros t T HT.
  induction HT.
    (* ttrue *)
      left. left. constructor.
    (* tfalse *)
      left. left. constructor.
    (* tif *)
      right. inversion IHHT1; clear IHHT1.
        (* value *)
          inversion H. clear H.
            (* bvalue *)
              inversion H0. clear H0.
                (* ttrue *)
                  exists t2...
                (* tfalse *)
                  exists t3...
            (* nvalue *)
              solve by inversion 2.
        (* can take a step *)
          inversion H as [t1' H1]. exists (tif t1' t2 t3)...
    (* tzero *)
       left. right. constructor.
    (* tsucc *)
       inversion IHHT; clear IHHT.
         (* t1 is value *)
           inversion H. clear H.
             (* bvalue *)
               solve by inversion 2.
             (* nvalue *)
               left. right. constructor. assumption.
         (* t1 can take a step *)
           right. inversion H. exists (tsucc x). constructor. assumption.
    (* tpred *)
       right. inversion IHHT; clear IHHT.
         (* t is a value *)
           inversion H; clear H.
             (* bvalue *)
               solve by inversion 2.
             (* nvalue *)
               inversion H0; clear H0.
                 (* t1 = tzero *)
                   exists tzero. constructor.
                 (* t1 = tsucc *)
                   exists t. constructor. assumption.
         (* t can take a step *)
           inversion H as [t' H1]. exists (tpred t')...
    (* tiszero *)
       right. inversion IHHT. clear IHHT.
         (* value *)
           inversion H; clear H.
             (* bvalue *)
                inversion H0. clear H0.
                (* ttrue *)
                  solve by inversion 2.
                (* tfalse *)
                  solve by inversion 2.
             (* nvalue *)
               inversion H0.
                 exists ttrue. constructor.
                 exists tfalse. constructor. assumption.
         (* can take a step *)
           inversion H as [t1' H1]. exists (tiszero t1')...
Qed.

(* Every well-typed normal form is a value?
     True
 * Every value is a normal form?
     True
 * The single-step evaluation relation is a partial function (i.e., it is deterministic).
     True
 * The single-step evaluation relation is a total function.
     False
 *)

(** Type Preservation **)

Theorem preservation:
  forall t t' T, has_type t T -> t ==> t' -> has_type t' T.
Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT; intros t' HE; try (solve by inversion).
    (* T_If *)
      