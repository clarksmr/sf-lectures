(** * Lists: Working with Structured Data *)

From LF Require Export Induction.
Module NatList.

(* ################################################################# *)
(** * Pairs of Numbers *)

(** An [Inductive] definition of pairs of numbers.  Note that
    it has just one constructor, (taking two arguments): *)

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

(** Functions for extracting the first and second components of a pair
    can then be defined by pattern matching. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(** A nicer notation for pairs: *)

Notation "( x , y )" := (pair x y).

(** The new notation can be used both in expressions and in pattern
    matches. *)

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(** Now let's try to prove a few simple facts about pairs.

    If we state properties of pairs in a slightly peculiar way, we can
    sometimes complete their proofs with just reflexivity (and its
    built-in simplification): *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof. reflexivity. Qed.

(** But just [reflexivity] is not enough if we state the lemma in the
    most natural way: *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

(** Solution: use [destruct]. *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl.
  reflexivity.
Qed.

(* ################################################################# *)
(** * Lists of Numbers *)

(** An inductive definition of _lists_ of numbers: *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** Some notation for lists to make our lives easier: *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** Now these all mean exactly the same thing: *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** Some useful list-manipulation functions... *)

(* ----------------------------------------------------------------- *)
(** *** Repeat *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(* ----------------------------------------------------------------- *)
(** *** Length *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* ----------------------------------------------------------------- *)
(** *** Append *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | [] => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2:             [] ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3:             [1;2;3] ++ [] = [1;2;3].
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** Head and Tail *)

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | [] => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | [] => []
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Reasoning About Lists *)

(** As with numbers, some proofs about list functions need only
    simplification... *)

Theorem nil_app : forall (lst : natlist),
  [] ++ lst = lst.
Proof. reflexivity. Qed.

(** ...and some need case analysis. *)

Theorem tl_length_pred : forall (lst : natlist),
  pred (length lst) = length (tl lst).
Proof.
  intros lst. destruct lst as [| h t].
  - reflexivity.
  - reflexivity.
Qed.

(** Usually, though, interesting theorems about lists require
    induction for their proofs.  We'll see how to do this next. *)

(* ================================================================= *)
(** ** Induction on Lists *)

(** Coq generates an induction principle for every [Inductive]
    definition, including lists.  We can use the [induction] tactic on
    lists to prove things like the associativity of list-append... *)

Theorem app_assoc : forall (lst1 lst2 lst3 : natlist),
  (lst1 ++ lst2) ++ lst3 = lst1 ++ (lst2 ++ lst3).
Proof.
  intros lst1 lst2 lst3. induction lst1 as [| h1 t1].
  - reflexivity.
  - simpl. rewrite -> IHt1. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Reversing a List *)

(** A more interesting example of induction over lists: *)

Fixpoint rev (lst : natlist) : natlist :=
  match lst with
  | [] => []
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev [] = [].
Proof. reflexivity.  Qed.

(** Let's try to prove [length (rev lst) = length lst]. *)

Theorem rev_length_firsttry : forall (lst : natlist),
  length (rev lst) = length lst.
Proof.
  intros lst. induction lst as [| h t].
  - reflexivity.
  - simpl. rewrite <- IHt.
Abort.

(** We can prove a lemma to bridge the gap. *)

Theorem app_length : forall (lst1 lst2 : natlist),
  length (lst1 ++ lst2) = (length lst1) + (length lst2).
Proof.
  intros lst1 lst2. induction lst1 as [| h1 t1].
  - reflexivity.
  - simpl. rewrite IHt1. reflexivity.
Qed.

(** Now we can complete the original proof. *)

Theorem rev_length : forall (lst : natlist),
  length (rev lst) = length lst.
Proof.
  intros lst. induction lst as [| h t].
  - reflexivity.
  - simpl. rewrite -> app_length.
    simpl. rewrite -> IHt. rewrite add_comm.
    reflexivity.
Qed.

(* ################################################################# *)
(** * Options *)

(** Suppose we'd like a function to retrieve the [n]th element
    of a list.  What to do if the list is too short? *)

Fixpoint nth_bad (lst : natlist) (n : nat) : nat :=
  match lst with
  | [] => 42 (* no good choice of what to return *)
  | h :: t =>
      match n with
      | 0 => h
      | S k => nth_bad t k
      end
  end.

(** The solution: [natoption]. *)

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (lst : natlist) (n : nat) : natoption :=
  match lst with
  | [] => None
  | h :: t =>
      match n with
      | 0 => Some h
      | S k => nth_error t k
      end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(* A simultaneous pattern match cleans up the code. *)

Fixpoint nth_error' (lst : natlist) (n : nat) : natoption :=
  match lst, n with
  | [], _ => None
  | h :: _, 0 => Some h
  | _ :: t, S k => nth_error' t k
  end.

Example test_nth_error'1 : nth_error' [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error'2 : nth_error' [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error'3 : nth_error' [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

End NatList.

(* ################################################################# *)
(** * Partial Maps *)

(** As a final illustration of how data structures can be defined in
    Coq, here is a simple _partial map_ data type, analogous to the
    map or dictionary data structures found in most programming
    languages. *)

Module PartialMap.
Export NatList.  (* make the definitions from NatList available here *)

Inductive partial_map : Type :=
  | Empty
  | Binding (k : nat) (v : nat) (m : partial_map).

(** The [update] function records a binding for a key. If the key
    was already present, that shadows the old binding. *)

Definition update (k : nat) (v : nat) (m : partial_map) : partial_map :=
  Binding k v m.

(** We can define functions on [partial_map]s by pattern matching. *)

Fixpoint find (k : nat) (m : partial_map) : natoption :=
  match m with
  | Empty => None
  | Binding k2 v m' =>
      if k =? k2 then Some v else find k m'
  end.

End PartialMap.

