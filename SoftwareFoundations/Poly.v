Require Export Lists.

(* Polymorphism *)

(** Polymorphic Lists **)

Inductive boollist : Type :=
| bool_nil : boollist
| bool_cons : bool -> boollist -> boollist.

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check nil.
Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length X t)
  end.

Example test_length1 : length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.
Example test_length2 : length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X : Type) (l1 l2 : list X) : (list X) :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
    | nil => cons X v (nil X)
    | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
    | nil => nil X
    | cons h t => snoc X (rev X t) h
  end.

Example test_rev1:
  rev nat (cons nat 1 (cons nat 2 (nil nat))) = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.
Example test_rev2:
 rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

(** Type Annotation Inference **)

Fixpoint app' X l1 l2 : list X :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app' X t l2)
  end.

Check app'.
Check app.

(** Type Argument Synthesis **)

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S(length' _ t)
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(** Implicit Arguments **)

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Definition list123'' :=
  cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length'' t)
  end.

(* Definition mynil := nil. *)

Definition mynil : list nat := nil.

Check @nil.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Definition list123''' := [1,2,3].

(** Exericises: Polymorphic Lists **)

Fixpoint repeat (X : Type) (n : X) (count : nat) : list X :=
  match count with
    | 0 => []
    | S count' => n :: repeat X n count'
  end.

Example test_repeat1: repeat bool true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app : forall X: Type, forall l:list X, app [] l = l.
Proof.
  destruct l; reflexivity.
Qed.

Theorem rev_snoc:
  forall X : Type, forall v : X, forall s : list X, rev (snoc s v) = v :: (rev s).
Proof.
  intros. induction s.
  reflexivity.
  simpl. rewrite IHs. reflexivity.
Qed.

Lemma rev_snoc__snoc_rev:
  forall (X:Type) (l:list X) (x:X), rev (snoc l x) = x :: rev l.
Proof.
  intros. induction l.
  reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed. 

Theorem rev_involutive : forall X : Type, forall l : list X, rev (rev l) = l.
Proof.
  intros. induction l.
  reflexivity.
  simpl. rewrite rev_snoc__snoc_rev. rewrite IHl. reflexivity.
Qed.

Theorem snoc_with_append:
  forall (X : Type) (l1 l2 : list X) (v : X), snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros. induction l1.
  reflexivity.
  simpl. rewrite IHl1. reflexivity.
Qed.

(** Polymorphic Pairs **)

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Implicit Arguments pair [[X] [Y]].

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match (lx,ly) with
    | ([],_) => []
    | (_,[]) => []
    | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

Fixpoint combine' {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx,ly with
    | [],_ => []
    | _,[] => []
    | x::tx, y::ty =>  (x,y) :: (combine' tx ty)
  end.

Check @combine.
Eval simpl in (combine [1,2] [false,false,true,true]).

Fixpoint split {X Y : Type} (l : list (X*Y)) : list X * list Y :=
  match l with
    | nil => (nil,nil)
    | (x,y) :: t => match split t with
                      | (tx,ty) => (x::tx,y::ty)
                    end
  end.

Example test_split: split [(1,false),(2,false)] = ([1,2],[false,false]).
Proof. reflexivity. Qed.

(** Polymorphic Options **)

Inductive option (X:Type) : Type :=
| Some : X -> option X
| None : option X.

Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].

Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' => if beq_nat n 0 then Some a else index (pred n) l'
  end.

Example test_index1 : index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1],[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.

Definition hd_opt {X : Type} (l : list X) : option X :=
  match l with
    | [] => None
    | h :: _ => Some h
  end.

Check @hd_opt.

Example test_hd_opt1 : hd_opt [1,2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [[1],[2]] = Some [1].
Proof. reflexivity. Qed.

(* Functions as Data *)

(** Higher-Order Functions **)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.
Example test_doit3times' : doit3times negb true = false.
Proof. reflexivity. Qed.

(** Partial Application **)

Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

(** Digression: Currying **)

