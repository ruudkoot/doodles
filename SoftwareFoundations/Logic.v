Require Export "Prop".

(* Quantification and Implication *)

Definition funny_prop1 :=
  forall n, forall (E : beautiful n), beautiful (n+3).

Definition funny_prop1' :=
  forall n, forall (_ : beautiful n), beautiful (n+3).

Definition funny_prop1'' :=
  forall n, beautiful n -> beautiful (n+3).

(* Conjunction *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.

Theorem and_example : (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj. apply b_0. apply b_3.
Qed.

Print and_example.

Theorem and_example' : (ev 0) /\ (ev 4).
Proof.
  split.
    apply ev_0.
    apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Theorem proj1 : forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP.
Qed.

Theorem proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  assumption.
Qed.

Print proj2.

Theorem and_commut : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  split; assumption.
Qed.

Print and_commut.

Theorem and_assoc : forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  repeat split; assumption.
Qed.

Theorem even__ev : forall n : nat, (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  induction n.
    split.
      constructor.
      intros. inversion H.
    inversion IHn.
      split.
        assumption.
        intros. apply ev_SS. unfold even in H1. simpl in H1. apply H. unfold even. assumption.
Qed.

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun P Q R PQ QR =>
    match PQ with
        conj P' _ => match QR with
                         conj _ R' => conj _ _ P' R'
                     end
    end.

(** Iff **)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) : type_scope.

Theorem iff_implies : forall P Q : Prop, (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H as [HAB HBA].
  apply HAB.
Qed.

Theorem iff_sym : forall P Q : Prop, (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H.
  inversion H as [HAB HBA].
  split; assumption.
Qed.

Theorem iff_refl : forall P : Prop, P <-> P.
Proof.
  intros P.
  split.
    intros H. assumption.
    intros H. assumption.
Qed.

Theorem iff_trans : forall P Q R : Prop, (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R PQ QR.
  split.
    intros H. inversion QR as [HQR HRQ]. apply HQR.
              inversion PQ as [HPQ HQP]. apply HPQ.
              apply H.
    intros H. inversion PQ as [HPQ HQP]. apply HQP.
              inversion QR as [HQR HRQ]. apply HRQ.
              apply H.
Qed.

Definition beautiful_iff_gorgeous : forall n, beautiful n <-> gorgeous n :=
  fun n => conj _ _ (beautiful__gorgeous n) (gorgeous__beautiful n).

(* Disjunction *)

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Check or_introl.
Check or_intror.

Theorem or_commut : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    apply or_intror. apply HP.
    apply or_introl. apply HQ.
Qed.

Theorem or_commut' : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    right. assumption.
    left. assumption.
Qed.

Definition or_commut'' : forall P Q : Prop, P \/ Q -> Q \/ P :=
  fun P Q H => match H with
                 | or_intror P' => or_introl Q P P'
                 | or_introl Q' => or_intror Q P Q'
               end.

Theorem or_distributes_over_and_1:
  forall P Q R : Prop, P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R H.
  inversion H as [HP | [HQ HR]].
    split.
      left. apply HP.
      left. apply HP.
    split.
      right. apply HQ.
      right. apply HR.
Qed.

Theorem or_distributes_over_and_2:
  forall P Q R : Prop, (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H.
  inversion H as [[HP1 | HQ] [HP2 | HR]].
    left. apply HP1.
    left. apply HP1.
    left. apply HP2.
    right. split; assumption.
Qed.

Theorem or_distributes_over_and:
  forall P Q R : Prop, P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split. apply or_distributes_over_and_1. apply or_distributes_over_and_2.
Qed.

(** Relating '/\' and '\/' with 'andb' and 'orb' **)

Theorem andb_true__and:
  forall b c, andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      apply conj; reflexivity.
      inversion H.
    inversion H.
Qed.

Theorem and__andb_true:
  forall b c, b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity.
Qed.

Theorem andb_false:
  forall b c, andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      inversion H.
      right. reflexivity.
    destruct c.
      left. reflexivity.
      left. reflexivity.
Qed.

Theorem orb_true:
  forall b c, orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H.
  destruct b.
    left. reflexivity.
    destruct c.
      right. reflexivity.
      inversion H.
Qed.

Theorem orb_false:
  forall b c, orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H.
  destruct b.
    destruct c.
      inversion H.
      inversion H.
      inversion H.
    destruct c.
      inversion H.
      inversion H.
      split; reflexivity.
Qed.

(* Falsehood *)

Inductive False : Prop := .

(* False_ind : forall P : Prop, False -> P *)

Check False_ind.

Theorem False_implies_nonsense:
  False -> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra.
Qed.

Theorem nonsense_implies_False:
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.
Qed.

Theorem ex_falso_quodlibet:
  forall (P:Prop), False -> P.
Proof.
  intros P contra.
  inversion contra.
Qed.

(** Truth **)

(* True_ind : forall P : True -> Prop, P truth -> forall t : True, P t. *)

Inductive True :=
| truth : True.

Check True_ind.

(* Negation *)

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

Theorem not_False:
  ~ False.
Proof.
   unfold not. intro H. inversion H.
Qed.

Theorem contadiction_implies_anything:
  forall P Q : Prop, (P /\ ~P) -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  inversion HP.
Qed.

Theorem double_neg:
  forall P : Prop, P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H.
Qed.

Theorem contrapositive:
  forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H. unfold not. intros G1 G2. apply G1. apply H. apply G2.
Qed.

Print contrapositive.

Theorem not_both_true_and_false:
  forall P : Prop, ~ (P /\ ~P).
Proof.
  intros P. unfold not. intros H. inversion H. apply H1. apply H0.
Qed.

Theorem five_not_even:
  ~ ev 5.
Proof.
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn].
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.
Qed.

Theorem ev_not_ev_S:
  forall n, ev n -> ~ ev (S n).
Proof.
  unfold not. intros n H. induction H.
    intros G. inversion G.
    intros G. apply IHev. inversion G. apply H1.
Qed.

Theorem classic_double_neg:
  forall P : Prop, ~~P -> P.
Proof.
  intros P H. unfold not in H.
Admitted.

Definition peirce :=
  forall P Q: Prop, ((P->Q)->P)->P.
Definition classic :=
  forall P:Prop, ~~P -> P.
Definition excluded_middle :=
  forall P:Prop, P \/ ~P.
Definition de_morgan_not_and_not :=
  forall P Q:Prop, ~(~P/\~Q) -> P\/Q.
Definition impies_to_or :=
  forall P Q:Prop, (P->Q) -> (~P\/Q).

Theorem pierce__classic:
  peirce -> classic.
Proof.
  unfold peirce. unfold classic. intros.
  unfold not in H0.
  apply H with (Q := False). intros. apply H0 in H1. inversion H1.
Qed.

Theorem classic__excluded_middle:
  classic -> excluded_middle.
Proof.
  unfold classic. unfold excluded_middle. intros.
  unfold not. unfold not in H.
Admitted. (* FIXME *)

Theorem excluded_middle__de_morgan_not_and_not :
  excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle. unfold de_morgan_not_and_not. unfold not. intros.
Admitted. (* FIXME *)

(** Inequiality **)

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true:
  forall b : bool, b <> false -> b = true.
Proof.
  intros b H.
  destruct b.
    reflexivity.
    unfold not in H. apply ex_falso_quodlibet. apply H. reflexivity.
Qed.

Theorem not_eq_beq_false:
  forall n n' : nat, n <> n' -> beq_nat n n' = false.
Proof.
  intros n n' H.
  unfold not in H.
Admitted. (* FIXME *)

Theorem beq_false_not_eq:
  forall n m, false = beq_nat n m -> n <> m.
Proof.
  intros n m H. unfold not. intro G.
  rewrite G in H. rewrite <- beq_nat_refl in H.
  inversion H.
Qed.

(* Existential Quantification *)

Inductive ex (X:Type) (P : X -> Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

Definition some_nat_is_even : Prop := ex nat ev.

Definition snie : some_nat_is_even :=
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Notation "'exists' x , p" :=
  (ex _ (fun x => p)) (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" :=
  (ex _ (fun x:X => p)) (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2).
  reflexivity.
Qed.

Example exists_example_1': exists n, n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2:
  forall n, (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

(* There exists a natural number such that n + 1 is beautiful. *)

Definition p : ex nat (fun n => beautiful (S n)) :=
  ex_intro nat (fun n => beautiful (S n)) 2 b_3.

Theorem dist_not_exists:
  forall (X : Type) (P : X -> Prop), (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros.
  unfold not. intro G. inversion G as [g Hg].
  apply Hg. apply H.
Qed.

Theorem not_exists_dist:
  excluded_middle -> forall (X:Type) (P:X->Prop), ~(exists x, ~P x) -> (forall x, P x).
Proof.
  intros.
Admitted. (* FIXME *)

Theorem dist_exists_or:
  forall (X:Type) (P Q : X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
    intros G. inversion G as [g Hg]. inversion Hg as [HgP | HgQ].
      left. exists g. apply HgP.
      right. exists g. apply HgQ.
    intros G. inversion G as [GP | GQ].
      inversion GP as [g gH]. assert (P g \/ Q g).
        left. apply gH.
        exists g. apply H.
      inversion GQ as [g gH]. assert (P g \/ Q g).
        right. apply gH.
        exists g. apply H.
Qed.

(* Equality *)

Module MyEquality.

  Inductive eq (X:Type) : X -> X -> Prop :=
    refl_equal : forall x, eq X x x.

  Notation "x = y" := (eq _ x y) (at level 70, no associativity) : type_scope.

  Inductive eq' (X:Type) (x:X) : X -> Prop :=
    refl_equal' : eq' X x x.
 
  Notation "x =' y" := (eq' _ x y) (at level 70, no associativity) : type_scope.

  Theorem two_defs_of_eq_coincide:
    forall (X : Type) (x y : X), x = y <-> x =' y.
  Proof.
    intros.
    split.
     intro G. inversion G. constructor.
     intro G. inversion G. constructor.
  Qed.

  Check eq_ind.
  Check eq'_ind.

  Definition four : 2 + 2 = 1 + 3 :=
    refl_equal nat 4.

  Definition singleton : forall (X:Set) (x:X), []++[x] = x::[] :=
    fun (X:Set) (x:X) => refl_equal (list X) [x].

End MyEquality.

(** Inversion, Again **)

(* Relations as Propositions *)

Module LeFirstTry.

  Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

  Check le_ind.

End LeFirstTry.

Inductive le (n:nat) : nat -> Prop :=
| le_n : le n n
| le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Check le_ind.

Theorem test_le1:
  3 <= 3.
Proof.
  constructor.
Qed.

Theorem test_le2:
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n.
Qed.

Theorem test_le3:
  ~ (2 <= 1).
Proof.
  intros H.
  inversion H.
  inversion H1.
Qed.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
| nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
| ne_1 : ev (S n) -> next_even n (S n)
| ne_2 : ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
| tr : forall (n m : nat), total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .

Module R.

  Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 : forall m n o, R m n o -> R (S m) n (S o)
  | c3 : forall m n o, R m n o -> R m (S n) (S o)
  | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
  | c5 : forall m n o, R m n o -> R n m o.

  Example ex1:
    R 1 1 2.
  Proof.
    repeat constructor.
  Qed.

  (* No, c1 and c4 are both symmetric in m and n and c2 and c3 are taken together. *)

  (* No, simply do not c2 and c3 earlier in your proof. *)

  Theorem R_fact:
    forall n m o, R m n o <-> m + n = o.
  Proof.
    split.
      intro H. induction H.
        reflexivity.
        rewrite plus_Sn_m. apply eq_remove_S. apply IHR.
        rewrite <- plus_n_Sm. apply eq_remove_S. apply IHR.
        apply eq_add_S. rewrite <- plus_Sn_m.
          apply eq_add_S. rewrite plus_n_Sm. apply IHR.
        rewrite plus_comm. apply IHR.
      intro H. inversion H.
        destruct m.
          destruct n.
            simpl. apply c1.
            simpl. apply c3.
              assert (forall i, R 0 i i).
                intro i. induction i.
                  apply c1.
                  apply c3. apply IHi.
              apply H1.
          destruct n.
            rewrite plus_0_r. apply c2.
              assert (forall i, R i 0 i).
                intro i. induction i.
                  apply c1.
                  apply c2. apply IHi.
              apply H1.
            rewrite <- plus_n_Sm. rewrite plus_Sn_m. apply c2. apply c3.
  Admitted. (* FIXME: stuck on the last step; induction on m and n missing quantifiers *)

End R.

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
| all_nil  : all X P []
| all_cons : forall x xs, P x -> all X P xs -> all X P (x::xs).

Theorem all_forallb:
  forall X P l test, (forall x:X, P x <-> test x = true) ->
                     (all X P l <-> forallb test l = true).
Proof.
  intros X P l test H.
  split.
    induction l.
      reflexivity.
      simpl. remember (test x) as Q. destruct Q.
        intro G. inversion G. apply IHl. apply H3.
      simpl. intro G. inversion G.
        assert (test x = true).
          apply H. apply H2.
        rewrite H4 in HeqQ. apply HeqQ.
    induction l.
      simpl. intro G. apply all_nil.
      simpl. remember (test x) as Q. destruct Q. intro G. apply all_cons.
        assert (test x = true -> P x).
          apply H.
        apply H0. symmetry in HeqQ. apply HeqQ.
      apply IHl. apply G.
      intro contra. inversion contra.
Qed.

Inductive InOrderMerge (X:Type) (test:X->bool) : list X -> list X -> list X -> Prop :=
| iom_nil : InOrderMerge X test [] [] []
| iom_left : forall x l1 l2 l3, InOrderMerge X test l1 l2 l3 -> test x = true ->
                                InOrderMerge X test (x::l1) l2 (x::l3)
| iom_right : forall x l1 l2 l3, InOrderMerge X test l1 l2 l3 -> test x = false ->
                                 InOrderMerge X test l1 (x::l2) (x::l3).

Lemma cons_remove:
  forall X (x:X) l1 l2, l1 = l2 -> x :: l1 = x :: l2.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Theorem filter_challenge:
  forall X test l l1 l2, InOrderMerge X test l1 l2 l -> filter test l = l1.
Proof.
  intros X test l. induction l.
    intros l1 l2 H. inversion H. reflexivity.
    intros l1 l2 H. simpl. remember (test x) as Q. destruct Q.
      inversion H.
        apply cons_remove. apply IHl with (l2 := l2). apply H4.
Admitted. (* FIXME *)

(* filter_challenge_2 *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
| ai_here : forall l, appears_in a (a::l)
| ai_later : forall b l, appears_in a l -> appears_in a (b::l).

Lemma appears_in_app:
  forall {X:Type} (xs ys : list X) (x:X),
    appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros X xs.
  induction xs.
    intros ys x H. simpl in H. right. apply H.
Admitted. (* FIXME *)

(* FIXME... *)
    
      
                         