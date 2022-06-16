(** * IndPrinciples: Induction Principles *)

(** Let's take a deeper look at induction. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export ProofObjects.

(* ################################################################# *)
(** * Basics *)

(** The automatically generated _induction principle_ for [nat]: *)

Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.

(** In English: Suppose [P] is a property of natural numbers (that is,
      [P n] is a [Prop] for every [n]). To show that [P n] holds of all
      [n], it suffices to show:

      - [P] holds of [0]
      - for any [n], if [P] holds of [n], then [P] holds of [S n]. *)

(** We can directly use the induction principle with [apply]: *)

Theorem mul_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity.  Qed.

(** Why the [induction] tactic is nicer than [apply]:
     - [apply] requires extra manual bookkeeping (the [intros] in the
       inductive case)
     - [apply] requires [n] to be left universally quantified
     - [apply] requires us to manually specify the name of the induction
       principle. *)

(** Coq generates induction principles for every datatype defined with
    [Inductive], including those that aren't recursive. *)

(** If we define type [t] with constructors [c1] ... [cn],
    Coq generates:

    t_ind : forall P : t -> Prop,
              ... case for c1 ... ->
              ... case for c2 ... -> ...
              ... case for cn ... ->
              forall n : t, P n

    The specific shape of each case depends on the arguments to the
    corresponding constructor. *)

(** An example with no constructor arguments: *)

Inductive time : Type :=
  | day
  | night.

Check time_ind :
  forall P : time -> Prop,
    P day ->
    P night ->
    forall t : time, P t.

(** An example with constructor arguments: *)

Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).

Check natlist_ind :
  forall P : natlist -> Prop,
    P nnil  ->
    (forall (n : nat) (l : natlist),
        P l -> P (ncons n l)) ->
    forall l : natlist, P l.

(** In general, the automatically generated induction principle for
    inductive type [t] is formed as follows:

    - Each constructor [c] generates one case of the principle.
    - If [c] takes no arguments, that case is:

      "P holds of c"

    - If [c] takes arguments [x1:a1] ... [xn:an], that case is:

      "For all x1:a1 ... xn:an,
          if [P] holds of each of the arguments of type [t],
          then [P] holds of [c x1 ... xn]"

      But that oversimplifies a little.  An assumption about [P]
      holding of an argument [x] of type [t] actually occurs
      immediately after the quantification of [x].
*)

(** For example, suppose we had written the definition of [natlist] a little
    differently: *)

Inductive natlist' : Type :=
  | nnil'
  | nsnoc (l : natlist') (n : nat).

(** Now the induction principle case for [nsnoc1] is a bit different
    than the earlier case for [ncons]: *)

Check natlist'_ind :
  forall P : natlist' -> Prop,
    P nnil' ->
    (forall l : natlist', P l -> forall n : nat, P (nsnoc l n)) ->
    forall n : natlist', P n.



(* ################################################################# *)
(** * Induction Principles for Propositions *)

(** Inductive definitions of propositions also cause Coq to generate
    induction priniciples.  For example, recall our proposition [ev]
    from [IndProp]: *)

Print ev.

(* ===>

  Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)))

*)

Check ev_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, ev n -> P n -> P (S (S n))) ->
    forall n : nat, ev n -> P n.

(** In English, [ev_ind] says: Suppose [P] is a property of natural
    numbers.  To show that [P n] holds whenever [n] is even, it suffices
    to show:

      - [P] holds for [0],

      - for any [n], if [n] is even and [P] holds for [n], then [P]
        holds for [S (S n)]. *)

(** The precise form of an [Inductive] definition can affect the
    induction principle Coq generates. *)

Inductive le1 : nat -> nat -> Prop :=
  | le1_n : forall n, le1 n n
  | le1_S : forall n m, (le1 n m) -> (le1 n (S m)).

Notation "m <=1 n" := (le1 m n) (at level 70).

(** [n] could instead be a parameter:  *)

Inductive le2 (n:nat) : nat -> Prop :=
  | le2_n : le2 n n
  | le2_S m (H : le2 n m) : le2 n (S m).

Notation "m <=2 n" := (le2 m n) (at level 70).

Check le1_ind :
  forall P : nat -> nat -> Prop,
    (forall n : nat, P n n) ->
    (forall n m : nat, n <=1 m -> P n m -> P n (S m)) ->
    forall n n0 : nat, n <=1 n0 -> P n n0.

Check le2_ind :
  forall (n : nat) (P : nat -> Prop),
    P n ->
    (forall m : nat, n <=2 m -> P m -> P (S m)) ->
    forall n0 : nat, n <=2 n0 -> P n0.

(** The latter is simpler, and corresponds to Coq's own
    definition. *)

(* ################################################################# *)
(** * Explicit Proof Objects for Induction (Optional) *)

(** Recall again the induction principle on naturals that Coq generates for
    us automatically from the Inductive declaration for [nat]. *)

Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.

(** There's nothing magic about this induction lemma: it's just
   another Coq lemma that requires a proof.  Coq generates the proof
   automatically too...  *)

Print nat_ind.

(** We can rewrite that more tidily as follows: *)
Fixpoint build_proof
         (P : nat -> Prop)
         (evPO : P 0)
         (evPS : forall n : nat, P n -> P (S n))
         (n : nat) : P n :=
  match n with
  | 0 => evPO
  | S k => evPS k (build_proof P evPO evPS k)
  end.

Definition nat_ind_tidy := build_proof.

(** Recursive function [build_proof] thus pattern matches against
    [n], recursing all the way down to 0, and building up a proof
    as it returns. *)

(** We can also define _non-standard_ induction principles
   in this style. Recall this troublesome thoerem: *)

Lemma even_ev : forall n: nat, even n = true -> ev n.
Proof.
  induction n; intros.
  - apply ev_0.
  - destruct n.
    + simpl in H. inversion H.
    + simpl in H.
      apply ev_SS.
Abort.

(** Attempts to prove this by standard induction on [n] fail in the case for
    [S (S n)], because the induction hypothesis only tells us something about
    [S n], which is useless. There are various ways to hack around this problem;
    for example, we _can_ use ordinary induction on [n] to prove this (try it!):

    [Lemma even_ev' : forall n : nat,
     (even n = true -> ev n) /\ (even (S n) = true -> ev (S n))].

    But we can make a much better proof by defining and proving a
    non-standard induction principle that goes "by twos":
 *)

Definition nat_ind2 :
  forall (P : nat -> Prop),
  P 0 ->
  P 1 ->
  (forall n : nat, P n -> P (S(S n))) ->
  forall n : nat , P n :=
    fun P => fun P0 => fun P1 => fun PSS =>
      fix f (n:nat) := match n with
                         0 => P0
                       | 1 => P1
                       | S (S n') => PSS n' (f n')
                       end.

 (** Once you get the hang of it, it is entirely straightforward to
     give an explicit proof term for induction principles like this.
     Proving this as a lemma using tactics is much less intuitive.

     The [induction ... using] tactic variant gives a convenient way to
     utilize a non-standard induction principle like this. *)

Lemma even_ev : forall n, even n = true -> ev n.
Proof.
  intros.
  induction n as [ | |n'] using nat_ind2.
  - apply ev_0.
  - simpl in H.
    inversion H.
  - simpl in H.
    apply ev_SS.
    apply IHn'.
    apply H.
Qed.



(** **** Exercise: 4 stars, standard, optional (t_tree)

    What if we wanted to define binary trees as follows, using a
    constructor that bundles the children and value at a node into a
    tuple? *)

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Inductive t_tree (X : Type) : Type :=
| t_leaf
| t_branch : (t_tree X * X * t_tree X) -> t_tree X.

Arguments t_leaf {X}.
Arguments t_branch {X}.

(** Unfortunately, the automatically-generated induction principle is
    not as strong as we need. It doesn't introduce induction hypotheses
    for the subtrees. *)

Check t_tree_ind.

(** That will get us in trouble if we want to prove something by
    induction, such as that [reflect] is an involution. *)

Fixpoint reflect {X : Type} (t : t_tree X) : t_tree X :=
  match t with
  | t_leaf => t_leaf
  | t_branch (l, v, r) => t_branch (reflect r, v, reflect l)
  end.

Theorem reflect_involution : forall (X : Type) (t : t_tree X),
    reflect (reflect t) = t.
Proof.
  intros X t. induction t.
  - reflexivity.
  - destruct p as [[l v] r]. simpl. Abort.

(** We get stuck, because we have no inductive hypothesis for [l] or
    [r]. So, we need to define our own custom induction principle, and
    use it to complete the proof.

    First, define the type of the induction principle that you want to
    use. There are many possible answers. Recall that you can use
    [match] as part of the definition. *)

Definition better_t_tree_ind_type : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Second, define the induction principle by giving a term of that
    type. Use the examples about [nat], above, as models. *)

Definition better_t_tree_ind : better_t_tree_ind_type
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Finally, prove the theorem. If [induction...using] gives you an
    error about "Cannot recognize an induction scheme", don't worry
    about it. The [induction] tactic is picky about the shape of the
    theorem you pass to it, but it doesn't give you much information
    to debug what is wrong about that shape.  You can use [apply]
    instead, as we saw at the beginning of this file. *)

Theorem reflect_involution : forall (X : Type) (t : t_tree X),
    reflect (reflect t) = t.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

