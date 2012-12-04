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

