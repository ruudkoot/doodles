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

Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z :=
  f (x, y).

Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) : Z :=
  match p with (x,y) => f x y end.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry:
  forall (X Y Z : Type) (f : X -> Y -> Z) x y, prod_curry (prod_uncurry f) x y = f x y.
Proof.
  reflexivity.
Qed.

Theorem curry_uncurry:
  forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y), prod_uncurry (prod_curry f) p = f p.
Proof.
  destruct p. reflexivity.
Qed.

(** Filter **)

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : (list X) :=
  match l with
    | [] => []
    | h :: t => if test h
                then h :: (filter test t)
                else filter test t
  end.

Example test_filter1: filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2: filter length_is_1 [[1,2],[3],[4],[5,6,7],[],[8]] = [[3],[4],[8]].
Proof. reflexivity. Qed.

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0,2,4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

(** Anonymous Functions **)

Example test_anon_fun': doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':
  filter (fun l => beq_nat (length l) 1) [[1,2],[3],[4],[5,6,7],[],[8]] = [[3],[4],[8]].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun x => andb (evenb x) (ble_nat 7 x)) l.

Example test_filter_even_gt7_1 : filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 : filter_even_gt7 [5,2,6,19,129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type} (p : X -> bool) (l : list X) : list X * list X :=
  (filter p l, filter (fun x => negb (p x)) l).

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
Proof. reflexivity. Qed.

(** Map **)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity. Qed.
Example test_map2: map oddb [2,1,2,5] = [false,true,false,true].
Proof. reflexivity. Qed.
Example test_map3:
  map (fun n => [evenb n,oddb n]) [2,1,2,5] =
    [[true,false],[false,true],[true,false],[false,true]].
Proof. reflexivity. Qed.

Lemma map_snoc:
  forall (X Y : Type) (f : X -> Y) (l : list X) (x : X),
    map f (snoc l x) = snoc (map f l) (f x).
Proof.
  intros. induction l.
  reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Theorem map_rev:
  forall (X Y : Type) (f : X -> Y) (l : list X), map f (rev l) = rev (map f l).
Proof.
  intros. induction l.
  reflexivity.
  simpl. rewrite <- IHl. rewrite map_snoc. reflexivity.
Qed.

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => app (f h) (flat_map f t)
  end.

Example test_flat_map1: flat_map (fun n => [n,n,n]) [1,5,4] = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

Module implicit_args.
(* FIXME *)
End implicit_args.

(** Fold **)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
    | nil => b
    | h :: t => f h (fold f t b)
  end.

Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).

Example fold_example1 : fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.
Example fold_example2 : fold andb [true,true,false,true] true = false.
Proof. reflexivity. Qed.
Example fold_example3 : fold app [[1],[],[2,3],[4]] [] = [1,2,3,4].
Proof. reflexivity. Qed.

Definition fold_types_different (l : list nat) :=
  fold (fun x r => andb (negb (ble_nat 9 x)) r) l true.

Example fold_types_different1: fold_types_different [1,7,4,7] = true.
Proof. reflexivity. Qed.
Example fold_types_different2: fold_types_different [1,4,10,8] = false.
Proof. reflexivity. Qed.

(** Functions For Constructing Functions **)

Definition constfun {X:Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.
Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X:Type} (f: nat->X) (k:nat) (x:X) : nat->X :=
  fun (k':nat) => if beq_nat k k' then x else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.
Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.
Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.
Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

Theorem override_example : forall (b:bool), (override (constfun b) 3 true) 2 = b.
Proof.
  destruct b; reflexivity.
Qed.

(* Optional Material *)

(** Non-Uniform Inductive Families (GADTs) **)

Inductive boolllist : nat -> Type :=
  boollnil : boolllist 0
| boollcons : forall n, bool -> boolllist n -> boolllist (S n).

Implicit Arguments boollcons [[n]].

Check (boollcons true (boollcons false (boollcons true boollnil))).

Fixpoint blapp {n1} (l1: boolllist n1) {n2} (l2: boolllist n2) : boolllist (n1 + n2) :=
  match l1 with
    | boollnil => l2
    | boollcons _ h t => boollcons h (blapp t l2)
  end.

Inductive llist (X:Type) : nat -> Type :=
  lnil : llist X 0
| lcons : forall n, X -> llist X n -> llist X (S n).

Implicit Arguments lnil [[X]].
Implicit Arguments lcons [[X] [n]].

Check (lcons true (lcons false (lcons true lnil))).

Fixpoint lapp (X:Type) {n1} (l1: llist X n1) {n2} (l2: llist X n2) : llist X (n1 + n2) :=
  match l1 with
    | lnil => l2
    | lcons _ h t => lcons h (lapp X t l2)
  end.

(* More About Coq *)

(** The 'apply' Tactic **)

Theorem silly1 : forall (n m o p : nat), n = m -> [n,o] = [n,p] -> [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly2 :
  forall (n m o p : nat),
    n = m -> (forall (q r : nat), q = r -> [q,o] = [r,p]) -> [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.
Qed.

(* FIXME: try with rewrite instead of apply *)

Theorem silly2a:
  forall (n m : nat),
    (n,n) = (m,m) -> (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) -> [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.
Qed.

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) -> evenb 3 = true -> oddb 4 = true.
Proof.
  intros eq1 eq2.
  apply eq1, eq2.
Qed.

Theorem silly3_firsttry:
  forall (n : nat), true = beq_nat n 5 -> beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
Abort.

Theorem silly3:
  forall (n : nat), true = beq_nat n 5 -> beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H.
Qed.

Theorem rev_exercise1:
  forall (l l' : list nat), l = rev l' -> l' = rev l.
Proof.
  intros l l' H.
  rewrite H.
  symmetry.
  apply rev_involutive.
Qed.

Theorem rev_exercise1':
  forall (l l' : list nat), l = rev l' -> l' = rev l.
Proof.
  intros l l' H.
  rewrite H.
  rewrite rev_involutive.
  reflexivity.
Qed.

(* 'rewrite' operates on equalities, 'apply' operates on implications. As can be seen
   in rev_exercise1 and rev_exercise1' both can be applicable in the same situation.  *)

(** The 'unfold' Tactic **)

