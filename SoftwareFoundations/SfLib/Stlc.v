(**** Stlc: The Simply Typed Lambda-Calculus ****)

Require Export Types.

(*** The Simply Typed Lambda-Calculus ***)

(** Overview **)

(** Syntax **)

Module STLC.

(* Types *)

Inductive ty : Type :=
| TBool : ty
| TArrow : ty -> ty -> ty.

(* Terms *)

Inductive tm : Type :=
| tvar : id -> tm
| tapp : tm -> tm -> tm
| tabs : id -> ty -> tm -> tm
| ttrue : tm
| tfalse : tm
| tif : tm -> tm -> tm -> tm.

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).

Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Notation idB :=
  (tabs x TBool (tvar x)).
Notation idBB :=
  (tabs x (TArrow TBool TBool) (tvar x)).
Notation idBBBB :=
  (tabs x (TArrow (TArrow TBool TBool) (TArrow TBool TBool)) (tvar x)).
Notation k :=
  (tabs x TBool (tabs y TBool (tvar x))).

(** Operational Semantics **)

(* Values *)

Inductive value : tm -> Prop :=
| v_abs : forall x T t, value (tabs x T t)
| t_true : value ttrue
| t_false : value tfalse.

Hint Constructors value.

(* Free Variables and Substitution *)

Fixpoint subst (x : id) (s : tm) (t : tm) : tm :=
  match t with
    | tvar x' =>
      if beq_id x x' then s else t
    | tabs x' T t1 =>
      tabs x' T (if beq_id x x' then t1 else (subst x s t1))
    | tapp t1 t2 =>
      tapp (subst x s t1) (subst x s t2)
    | ttrue =>
      ttrue
    | tfalse =>
      tfalse
    | tif t1 t2 t3 => 
      tif (subst x s t1) (subst x s t2) (subst x s t3)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(* Reduction *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall x T t12 v2, value v2 -> (tapp (tabs x T t12) v2) ==> [x:=v2]t12
| ST_App1 : forall t1 t1' t2, t1 ==> t1' -> tapp t1 t2 ==> tapp t1' t2
| ST_App2 : forall v1 t2 t2', value v1 -> t2 ==> t2' -> tapp v1 t2 ==> tapp v1 t2'
| ST_IfTrue : forall t1 t2, (tif ttrue t1 t2) ==> t1
| ST_IfFalse : forall t1 t2, (tif tfalse t1 t2) ==> t2
| ST_If : forall t1 t1' t2 t3, t1 ==> t1' -> (tif t1 t2 t3) ==> (tif t1' t2 t3)
where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

(* Examples *)

Lemma step_example1:
  (tapp idBB idB) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl.
Qed.

Lemma step_example1':
  (tapp idBB idB) ==>* idB.
Proof.
  normalize.
Qed.

Lemma step_example2:
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply multi_refl.
Qed.

Lemma step_example2':
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  normalize.
Qed.

Lemma step_example3:
  (tapp (tapp idBBBB idBB) idB) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_App1. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. apply v_abs. simpl.
  apply multi_refl.
Qed.

Lemma step_example3':
  (tapp (tapp idBBBB idBB) idB) ==>* idB.
Proof.
  normalize.
Qed.

(** Typing **)

(* Contexts *)

Module PartialMap.

  Definition partial_map (A : Type) := id -> option A.
    
  Definition empty {A : Type} : partial_map A := (fun _ => None).

  Definition extend {A : Type} (Gamma : partial_map A) (x : id) (T : A) :=
    fun x' => if beq_id x x' then Some T else Gamma x'.

  Lemma extend_eq:
    forall A (ctxt : partial_map A) x T, (extend ctxt x T) x = Some T.
  Proof.
    intros. unfold extend. rewrite <- beq_id_refl. reflexivity.
  Qed.

  Lemma extend_neq:
    forall A (ctxt : partial_map A) x1 T x2,
      beq_id x2 x1 = false -> (extend ctxt x2 T) x1 = ctxt x1.
  Proof.
    intros. unfold extend. rewrite H. reflexivity.
  Qed.

End PartialMap.

Definition context := partial_map ty.

(* Typing Relation *)

Inductive has_type : context -> tm -> ty -> Prop :=
| T_Var : forall Gamma x T, Gamma x = Some T -> has_type Gamma (tvar x) T
| T_Abs : forall Gamma x T11 T12 t12,
            has_type (extend Gamma x T11) t12 T12 ->
            has_type Gamma (tabs x T11 t12) (TArrow T11 T12)
| T_App : forall T11 T12 Gamma t1 t2,
            has_type Gamma t1 (TArrow T11 T12) ->
            has_type Gamma t2 T11 ->
            has_type Gamma (tapp t1 t2) T12
| T_True : forall Gamma, has_type Gamma ttrue TBool
| T_False : forall Gamma, has_type Gamma tfalse TBool
| T_If : forall t1 t2 t3 T Gamma,
           has_type Gamma t1 TBool ->
           has_type Gamma t2 T ->
           has_type Gamma t3 T ->
           has_type Gamma (tif t1 t2 t3) T.

Hint Constructors has_type.

(* Examples *)

Example typing_example_1:
  has_type empty (tabs x TBool (tvar x)) (TArrow TBool TBool).
Proof.
  apply T_Abs. apply T_Var. reflexivity.
Qed.

Example typing_example_1':
  has_type empty (tabs x TBool (tvar x)) (TArrow TBool TBool).
Proof.
  auto.
Qed.

Hint Unfold beq_id beq_nat extend.

Example typing_example_2_full:
  has_type empty
           (tabs x TBool (tabs y (TArrow TBool TBool)
                               (tapp (tvar y) (tapp (tvar y) (tvar x)))))
           (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof.
  apply T_Abs. apply T_Abs. apply T_App with (T11 := TBool).
    apply T_Var. unfold extend. rewrite <- beq_id_refl. reflexivity.
    apply T_App with (T11 := TBool).
      apply T_Var. unfold extend. rewrite <- beq_id_refl. reflexivity.
      apply T_Var. unfold extend. rewrite <- beq_id_refl. reflexivity.
Qed.

Example typing_example_3:
  has_type empty
           (tabs x (TArrow TBool TBool)
                 (tabs y (TArrow TBool TBool)
                       (tabs z TBool (tapp (tvar y) (tapp (tvar x) (tvar z))))))
           (TArrow (TArrow TBool TBool) (TArrow (TArrow TBool TBool)
                                                (TArrow TBool TBool))).
Proof.
  apply T_Abs. apply T_Abs. apply T_Abs.
  eapply T_App.
    apply T_Var. unfold extend, beq_id, beq_nat. reflexivity.
    eapply T_App.
      apply T_Var. unfold extend, beq_id, beq_nat. reflexivity.
      apply T_Var. unfold extend, beq_id, beq_nat. reflexivity.
Qed.

Example typing_nonexample_1:
  ~exists T, has_type empty (tabs x TBool (tabs y TBool (tapp (tvar x) (tvar y)))) T.
Proof.
  intros Hc. inversion Hc.
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  inversion H1.
Qed.

Lemma nonrecursive:
  forall x y, TArrow x y <> x.
Proof.
  induction x0.
    intros y0 H. inversion H.
    intros y0 H. inversion H. apply (IHx0_1 x0_2 H1).
Qed.
    
Example typing_nonexample_3:
  ~(exists S, exists T, has_type empty (tabs x S (tapp (tvar x) (tvar x))) T).
Proof.
  intros Hc. inversion Hc. clear Hc.
  inversion H. subst. clear H.
  inversion H0. subst. clear H0.
  inversion H5. subst. clear H5.
  inversion H2. inversion H4. subst. clear H2. clear H4.
  inversion H1. inversion H7. subst. clear H1. clear H7.
  apply (nonrecursive T11 T12). assumption.
Qed.

(** Properties **)

(* Progress *)

Theorem progress:
  forall t T, has_type empty t T -> value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t T Ht.
  remember (@empty ty) as Gamma.
  induction Ht; subst Gamma...
    (* T_Var *)
      inversion H.
    (* T_App: t = t1 t2 *)
      right. destruct IHHt1...
        (* t1 value *)
          destruct IHHt2...
            (* t2 value *)
              inversion H; subst. (* canonical forms lemma? *)
                exists ([x0:=t2]t)...
                solve by inversion.
                solve by inversion.
            (* t2 steps *)
              inversion H0 as [t2' Hstp]. exists (tapp t1 t2')...
        (* t1 steps *)
          inversion H as [t1' Hstp]. exists (tapp t1' t2)...
    (* T_If *)
      right. destruct IHHt1...
        (* t1 value *)
          inversion H; subst.
            solve by inversion.
            eauto.
            eauto.
        (* t2 steps *)
          inversion H as [t1' Hstp]. exists (tif t1' t2 t3)...
Qed.

Theorem progress':
  forall t T, has_type empty t T -> value t \/ exists t', t ==> t'.
Proof.
  induction t; intros T Ht; auto.
    (* tvar *)
      inversion Ht; subst.
        inversion H1.
    (* tapp *)
      right. inversion Ht; subst.
      remember (IHt1 (TArrow T11 T) H2) as R. inversion R as [R1|R2]; subst.
        inversion R1; subst.
          (*1*) exists ([x0:=t2]t). constructor. inversion H4; subst; admit.
          (*2*) inversion H2.
          (*3*) inversion H2.
        inversion R2. exists (tapp x0 t2). constructor. assumption.
    (* tif *)
      right. inversion Ht; subst.
      remember (IHt1 TBool H3) as R. inversion R as [R1|R2]; subst.
        inversion R1; subst; eauto. inversion H3.
        inversion R2. exists (tif x0 t2 t3). constructor. assumption.
Qed. (* FIXME: tapp *)

(* Free Occurrences *)

Inductive appears_free_in: id -> tm -> Prop :=
| afi_var : forall x, appears_free_in x (tvar x)
| afi_app1 : forall x t1 t2, appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
| afi_app2 : forall x t1 t2, appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
| afi_abs : forall x y T11 t12, y <> x -> appears_free_in x t12 -> appears_free_in x (tabs y T11 t12)
| afi_if1 : forall x t1 t2 t3, appears_free_in x t1 -> appears_free_in x (tif t1 t2 t3)
| afi_if2 : forall x t1 t2 t3, appears_free_in x t2 -> appears_free_in x (tif t1 t2 t3)
| afi_if3 : forall x t1 t2 t3, appears_free_in x t3 -> appears_free_in x (tif t1 t2 t3).

Hint Constructors appears_free_in.

Definition closed (t : tm) := forall x, ~appears_free_in x t.

(* Substitution *)

Lemma free_in_context:
  forall x t T Gamma,
    appears_free_in x t -> has_type Gamma t T -> exists T', Gamma x = Some T'.
Proof.
  