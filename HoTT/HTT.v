Definition UU := Type.

Definition idfun ( A : UU ) : A -> A := fun x => x.

Section idfun_test.
Variable A : UU.
Variable a : A.
Check idfun A.
Check idfun _ a.
End idfun_test.

Definition funcomp_indirect ( A B C : UU ) ( f : A -> B ) ( g : B -> C ) : A -> C.
Proof.
  intros x. apply g. apply f. assumption.
Defined.

Definition funcomp { A B C : UU } ( f : A -> B ) ( g : B -> C )
  := fun x : A => g (f x).

Print funcomp.
Print funcomp_indirect.

(* 4. Some basic inductive types *)

(* Inductive nat := O | S : nat -> nat. *)

Definition predecessor ( n : nat ) : nat :=
  match n with
    | O => O
    | S m => m
  end.

Eval compute in predecessor 26.

Definition indirect_predecessor ( n : nat ) : nat.
Proof.
  destruct n. exact 0. exact n.
Defined.

Print predecessor.
Print indirect_predecessor.

Inductive total {B : UU} (E : B -> UU) : UU :=
  pair ( x : B ) ( y : E x ).

Definition dirprod ( A B : UU ) : UU :=
  total ( fun x : A => B ).

Definition pr1 { B : UU } { E : B -> UU } : total E -> B :=
  fun z => match z with pair x y => x end.

(* 5. The path space *)

Notation paths := identity.

Print identity.

Notation idpath := identity_refl.

Definition pathsinv { A : UU } { a b : A } ( f : paths a b ) : paths b a.
Proof.
  destruct f. apply idpath.
Defined.

Definition pathscomp { A : UU } { a b c : A } ( f : paths a b ) ( g : paths b c ) : paths a c.
Proof.
  destruct f. assumption.
Defined.

Lemma isrunitalpathscomp { A : UU } { a b : A } ( f : paths a b ) : paths ( pathscomp f ( idpath b ) ) f.
Proof.
  destruct f. apply idpath.
Defined.

Definition maponpaths { A B : UU } ( f : A -> B ) { a a' : A }
           ( p : paths a a' ) : paths ( f a ) ( f a' ).
Proof.
  destruct p. apply idpath.
Defined.

Print maponpaths.

Notation "f ' p" := ( maponpaths f p ) (at level 30).

(* Transport *)

Definition transportf { B : UU } ( E : B -> UU ) { b b' : B }
           ( f : paths b b' ) : E b -> E b'.
Proof.
  intros e. destruct f. assumption.
Defined.

Print transportf.

Definition transportb { B : UU } ( E : B -> UU ) { b b' : B }
           ( f : paths b b') : E b' -> E b.
Proof.
  intros e. destruct f. assumption.
Defined.

Definition homot { A B : UU } ( f g : A -> B ) := forall x : A, paths ( f x ) ( g x ).

Definition isheq { A B : UU } ( f : A -> B )
  := total (fun f' : B -> A => dirprod (homot (funcomp f' f) (idfun _))
                                       (homot (funcomp f f') (idfun _)) ).

Lemma backandforth { B : UU } { E : B -> UU } { b b' : B } ( f : paths b b' ) ( e : E b' ) : homot ( funcomp ( transportb E f ) ( transportf E f ) ) ( idfun _ ).
Proof.
  intros x. destruct f. apply idpath.
Defined.

Lemma forthandback { B : UU } { E : B -> UU } { b b' : B } ( f : paths b b') ( e : E b' ) : homot ( funcomp ( transportf E f ) ( transportb E f )  ) ( idfun _ ).
Proof.
  intros x. destruct f. apply idpath.
Defined.

(*
Lemma isheqtransportf { B : UU } ( E : B -> UU ) { b b' : B } ( f : paths b b' ) : isheq ( transportf E f ).
Proof. unfold isheq.
  split with ( transportb E f ). split.
  apply backandforth.
  (* apply forthandback. *)
*)

