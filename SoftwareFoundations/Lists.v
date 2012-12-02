Require Export Basics.

Module NatList.

(* Pairs of Numbers *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Eval simpl in (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
    | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
    | pair x y => y
  end.

Eval simpl in (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Eval simpl in (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
    | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
    | (x,y) => x
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
    | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat), (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing_stuck : forall (p : natprod), p = (fst p, snd p).
Proof.
  simpl.
Abort.

Theorem surjective_pairing : forall (p : natprod), p = (fst p, snd p).
Proof.
  intros p. destruct p as (n,m). simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod), (snd p, fst p) = swap_pair p.
Proof.
  intros. destruct p. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod), fst (swap_pair p) = snd p.
Proof.
  intros. destruct p. reflexivity.
Qed.

(* Lists of Numbers *)

Inductive natlist : Type :=
| nil : natlist
| cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1,2,3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
    | O => nil
    | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
    | nil => O
    | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Example test_app1: [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4,5] = [4,5].
Proof. reflexivity. Qed.
Example test_app3: [1,2,3] ++ nil = [1,2,3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
    | nil => default
    | h :: t => h
  end.

Definition tail (l:natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => t
  end.

Example test_hd1: hd 0 [1,2,3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tail: tail [1,2,3] = [2,3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
    | [] => []
    | h :: t => match h with
                  | 0 => nonzeros t
                  | _ => h :: nonzeros t
                end
  end.

Example test_nonzeros: nonzeros [0,1,0,2,3,0,0] = [1,2,3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
    | [] => []
    | h :: t => match oddb h with
                  | true => h :: oddmembers t
                  | false => oddmembers t
                end
  end.

Example test_oddmembers: oddmembers [0,1,0,2,3,0,0] = [1,3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
    | [] => 0
    | h :: t => match oddb h with
                  | true => S (countoddmembers t)
                  | false => countoddmembers t
                end
  end.

Example test_countoddmembers1: countoddmembers [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0,2,4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 , l2 with
     | [] , [] => []
     | l1' , [] => l1'
     | [] , l2' => l2
     | h1 :: t1 , h2 :: t2 => h1 :: h2 :: alternate t1 t2
  end.

Example test_alternate1: alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1,2,3] [4] = [1,4,2,3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [20,30] = [20,30].
Proof. reflexivity. Qed.

(** Bags via Lists **)

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
    | [] => 0
    | h :: t => match beq_nat h v with
                  | true => S (count v t)
                  | false => count v t
                end
  end.

Example test_count1: count 1 [1,2,3,1,4,1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1,2,3,1,4,1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := cons v s.

Example test_add1: count 1 (add 1 [1,4,1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1,4,1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool := negb (beq_nat 0 (count v s)).

Example test_member1: member 1 [1,4,1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1,4,1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) :=
  match s with
    | [] => []
    | h :: t => match beq_nat v h with
                 | true => t
                 | false => h :: remove_one v t
               end
  end.

Example test_remove_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4: count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
    | [] => []
    | h :: t => match beq_nat v h with
                  | true => remove_all v t
                  | false => h :: remove_all v t
                end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2,1,5,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2,1,4,1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
    | [] => true
    | h :: t => match member h s2 with
                  | true => subset t (remove_one h s2)
                  | false => false
                end
  end.

Example test_subset1: subset [1,2] [2,1,4,1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1,2,2] [2,1,4,1] = false.
Proof. reflexivity. Qed.

Theorem bag_theorem1:
  forall (n : nat) (s : bag), S (count n s) = count n (add n s).
Proof.
  intros. induction s; simpl; rewrite <- beq_nat_refl; reflexivity.
Qed.

Lemma ble_nat_Sn : forall n : nat, ble_nat n (S n) = true.
Proof.
  intros. induction n.
  reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Theorem bag_theorem2:
  forall (n m : nat) (s : bag), ble_nat (count m s) (count m (add n s)) = true.
Proof.
  intros. destruct s.
  reflexivity.
  simpl. remember (beq_nat n0 m). destruct b.
  simpl. remember (beq_nat n m). destruct b.
  rewrite ble_nat_Sn. reflexivity.
  rewrite <- ble_nat_refl. reflexivity.
  remember (beq_nat n m). destruct b.
  rewrite ble_nat_Sn. reflexivity.
  rewrite <- ble_nat_refl. reflexivity.
Qed.

(* Reasoning About Lists *)

Theorem nil_app : forall l:natlist, [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist, pred (length l) = length (tail l).
Proof.
  intros. destruct l; reflexivity.
Qed.

(** Induction on Lists **)

Theorem app_ass : forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros. induction l1.
  reflexivity.
  simpl. rewrite IHl1. reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist, length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros. induction l1.
  reflexivity.
  simpl. rewrite IHl1. reflexivity.
Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
  match l with
    | nil => [v]
    | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist :=
  match l with
    | [] => []
    | h :: t => snoc (rev t) h
  end.

Example test_rev1: rev [1,2,3] = [3,2,1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist, length (rev l) = length l.
Proof.
  intros. induction l.
  reflexivity.
  simpl. rewrite <- IHl.
Abort.

Theorem length_snoc : forall n : nat, forall l : natlist, length (snoc l n) = S (length l).
Proof.
  intros. induction l.
  reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_length : forall l : natlist, length (rev l) = length l.
Proof.
  intros. induction l.
  reflexivity.
  simpl. rewrite length_snoc. rewrite IHl. reflexivity.
Qed.

(** SearchAbout **)

SearchAbout rev.

(** List Exercises, Part 1 **)

Theorem app_nil_end : forall l : natlist, l ++ [] = l.
Proof.
  intros. induction l.
  reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Lemma rev_snoc__snoc_rev : forall (l : natlist) (n : nat), rev (snoc l n) = n :: rev l.
Proof.
  intros. induction l.
  reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist, rev (rev l) = l.
Proof.
  intros. induction l.
  reflexivity.
  simpl. rewrite rev_snoc__snoc_rev. rewrite IHl. reflexivity.
Qed.

Theorem app_ass4:
  forall l1 l2 l3 l4 : natlist, l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros. rewrite 2 app_ass. reflexivity.
Qed.

Theorem snoc_append : forall (l:natlist) (n:nat), snoc l n = l ++ [n].
Proof.
  intros. induction l.
  reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Lemma snoc_rev__rev_snoc : forall (l:natlist) (n:nat), snoc (rev l) n = rev l ++ [n].
Proof. (* FIXME *)
  intros. induction l.
  reflexivity.
  simpl. 
Admitted.

Theorem distr_rev : forall l1 l2 : natlist, rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof. (* FIXME *)
  intros. induction l1.
  simpl. rewrite app_nil_end. reflexivity.
  simpl. rewrite IHl1. rewrite snoc_append.
         rewrite snoc_rev__rev_snoc. rewrite app_ass. reflexivity.
Qed.

Lemma nonzerso_length:
  forall l1  l2 : natlist, nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros. induction l1.
  reflexivity.
  destruct n; simpl; rewrite IHl1; reflexivity.
Qed.

(** List Exercise, Part 2 **)

Lemma cons_app:
  forall (l:natlist) (n:nat), n :: l = [n] ++ l.
Proof.
  reflexivity.
Qed.

Theorem list_design1:
  forall (l1 l2 : natlist) (n1 n2 : nat), snoc l1 n1 ++ cons n2 l2 = l1 ++ [n1,n2] ++ l2.
Proof.
  intros. simpl. rewrite snoc_append. rewrite app_ass.
  replace (n2 :: l2) with ([n2] ++ l2).
  replace (n1 :: [n2] ++ l2) with ([n1] ++ [n2] ++ l2).
  reflexivity.
  rewrite cons_app. reflexivity.
  reflexivity.
Qed.

Theorem count_member_nonzero:
  forall (s : bag), ble_nat 1 (count 1 (1 :: s)) = true.
Proof. reflexivity. Qed.

Theorem ble_n_Sn : forall n, ble_nat n (S n) = true.
Proof.
  intros. induction n.
  reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.

Theorem remove_decreases_count:
  forall (s : bag), ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros. induction s.
  reflexivity.
  destruct n.
  simpl. rewrite ble_nat_Sn. reflexivity.
  simpl. rewrite IHs. reflexivity.
Qed.

Theorem bag_count_sum:
  forall (s1 s2 : bag) (n : nat), count n s1 + count n s2 = count n (sum s1 s2).
Proof.
  intros. induction s1.
  reflexivity.
  simpl. remember (beq_nat n0 n). destruct b.
  simpl. rewrite IHs1. reflexivity.
  rewrite IHs1. reflexivity.
Qed.

Theorem rev_injective : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof. (* FIXME *)
Abort.

(* Options *)

Inductive natoption : Type :=
| Some : nat -> natoption
| None : natoption.

Fixpoint index_bad (n:nat) (l:natlist) : nat :=
  match l with
    | nil => 42
    | a :: l' => match beq_nat n 0 with
                   | true => a
                   | false => index_bad (pred n) l'
                 end
  end.

Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
    | nil => None
    | a :: l' => match beq_nat n 0 with
                   | true => Some a 
                   | false => index (pred n) l'
                 end
  end.

Example test_index1 : index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 3 [4,5,6,7] = Some 7.
Proof. reflexivity. Qed.
Example test_index3 : index 10 [4,5,6,7] = None.
Proof. reflexivity. Qed.

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
    | [] => None
    | a :: l' => if beq_nat n 0 then Some a else index' (pred n) l'
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
    | Some n' => n'
    | None => d
  end.

Definition hd_opt (l : natlist) : natoption :=
  match l with
    | [] => None
    | h :: _ => Some h
  end.

Example test_hd_opt1 : hd_opt [] = None.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt3 : hd_opt [5,6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd:
  forall (l:natlist) (default:nat), hd default l = option_elim default (hd_opt l).
Proof.
  destruct l; reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
    | [], [] => true
    | h1 :: t1, h2 :: t2 => if beq_nat h1 h2 then beq_natlist t1 t2 else false
    | _, _ => false
  end.

Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.
Example test_beq_natlist2 : beq_natlist [1,2,3] [1,2,3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3 : beq_natlist [1,2,3] [3,2,1] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l:natlist, true = beq_natlist l l.
Proof.
  induction l.
  reflexivity.
  simpl. rewrite <- beq_nat_refl. rewrite IHl. reflexivity.
Qed.

(* Extended Exercise: Dectionaries *)

Module Dictionary.

Inductive dictionary : Type :=
| empty : dictionary
| record : nat -> nat -> dictionary -> dictionary.

Definition insert (key value : nat) (d : dictionary) : dictionary := record key value d.

Fixpoint find (key : nat) (d : dictionary) : natoption :=
  match d with
    | empty => None
    | record k v d' => if (beq_nat key k) then (Some v) else (find key d')
  end.

Theorem dictionary_invariant1:
  forall (d : dictionary) (k v :nat), (find k (insert k v d)) = Some v.
Proof.
  intros. simpl. rewrite <- beq_nat_refl. reflexivity.
Qed.

Theorem dictionary_invariant2:
  forall (d : dictionary) (m n o : nat),
    (beq_nat m n) = false -> (find m d) = (find m (insert n o d)).
Proof.
  intros. simpl. rewrite H. reflexivity.
Qed.

End Dictionary.

End NatList.