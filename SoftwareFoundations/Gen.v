Require Export Poly.

Theorem double_injective_FAILED : forall n m, double n = double m -> n = m.
Proof.
  intros n m. induction n.
    simpl. intros eq. destruct m.
      reflexivity.
      inversion eq.
    intros eq. destruct m.
      inversion eq.
      assert (n = m) as H.
Abort.

Theorem double_injective' : forall n m, double n = double m -> n = m.
Proof.
  intros n. induction n.
    simpl. intros m eq. destruct m.
      reflexivity.
      inversion eq.
    intros m eq. destruct m.
      inversion eq.
      assert (n = m). apply IHn. inversion eq. reflexivity.
        rewrite -> H. reflexivity.
Qed.

Theorem double_injective_take2_FAILED:
  forall n m, double n = double m -> n = m.
Proof.
  intros n m. induction m.
    simpl. intros eq. destruct n.
      reflexivity.
      inversion eq.
    intros eq. destruct n.
      inversion eq.
      assert (n = m).
Abort.

Theorem double_injective_take2:
  forall n m, double n = double m -> n = m.
Proof.
  intros n m. generalize dependent n. induction m.
    simpl. intros n eq. destruct n.
      reflexivity.
      inversion eq.
    intros n eq. destruct n.
      inversion eq.
      assert (n = m). apply IHm. inversion eq. reflexivity.
        rewrite H. reflexivity.
Qed.

Theorem plus_n_n_injective_take2:
  forall n m, n + n = m + m -> n = m.
Proof.
  intros n m. generalize dependent n. induction m.
    intros n eq. destruct n.
      reflexivity.
      inversion eq.
    intros n eq. destruct n.
      inversion eq.
      assert (n = m).
        apply IHm. inversion eq. rewrite <-2 plus_n_Sm in H0. apply eq_add_S. apply H0.
        apply eq_remove_S. apply H.
Qed.

Theorem index_after_last:
  forall (n : nat) (X : Type) (l : list X), length l = n -> index (S n) l = None.
Proof.
  intros n X l. generalize dependent n. induction l.
    reflexivity.
    intros n eq. inversion eq. apply IHl. reflexivity.
Qed.

(* FIXME: infex_after_last_informal *)

Theorem length_snoc''': forall (n : nat) (X : Type) (v : X) (l : list X),
                          length l = n -> length (snoc l v) = S n.
Proof.
  intros n X v l. generalize dependent n. induction l.
    intros n eq. simpl. inversion eq. reflexivity.
    intros n eq. simpl.
Admitted. (* FIXME *)

Theorem app_length_cons:
  forall (X : Type) (l1 l2 : list X) (x : X) (n : nat),
    length (l1 ++ (x :: l2)) = n -> S (length (l1 ++ l2)) = n.
Proof.
  intros X. induction l1.
    intros l2 x n eq. simpl. inversion eq. reflexivity.
    intros l2 x' n eq. simpl. inversion eq. simpl. 
Admitted. (* FIXME *)