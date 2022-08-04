(** * Induction: Proof by Induction *)

(** Previous proof techniques:

    - reflexivity of equality [reflexivity]
    - substitution of equals for equals [rewrite]
    - case analysis [destruct]

    Next: _induction_ on data types. *)

(* ################################################################# *)
(** * Separate Compilation *)

(** Coq will first need to compile [Basics.v] into [Basics.vo]
    so it can be imported here -- detailed instructions are in the
    full version of this chapter. To create a Makefile, run
    [coq_makefile -f _CoqProject -o Makefile *.v]. *)

From LF Require Export Basics.

(* ################################################################# *)
(** * Proof by Induction *)

(** We can prove that [0] is a neutral
    element for [+] on the _left_
    using just [reflexivity]. *)

Example add_0_l : forall n : nat,
    0 + n = n.
Proof. reflexivity. Qed.

(** But the proof that it is also a neutral
    element on the _right_ ... *)

Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.
(** ... gets stuck. *)
Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(** And reasoning by cases using [destruct n] doesn't get us much
    further: the branch of the case analysis where we assume [n = 0]
    goes through fine, but in the branch where [n = S n'] for some [n'] we
    get stuck in exactly the same way. *)

Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.       (* ...but here we are stuck again *)
Abort.

(** We need a bigger hammer: the _principle of induction_ over
    natural numbers...

      - If [P(n)] is some proposition involving a natural number [n],
        and we want to show that [P] holds for _all_ numbers, we can
        reason like this:

         - show that [P(O)] holds

         - show that, if [P(n')] holds, then so does [P(S n')]

         - conclude that [P(n)] holds for all [n].

    For example... *)

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Let's try this one together: *)

Theorem minus_n_n : forall n,
  n - n = 0.
Proof.
  (* WORK IN CLASS *) Admitted.

(** Here's another related fact about addition, which we'll
    need later. *)

Theorem add_comm : forall n m : nat,
  n + m = m + n.
    (* FILL IN HERE *) Admitted.
(* ################################################################# *)
(** * Proofs Within Proofs *)

(** Here's a way to use an in-line assertion instead of a separate
    lemma.

    New tactic: [assert]. *)

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
  { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like add_comm should do the trick! *)
  rewrite add_comm.
  (* Doesn't work... Coq rewrites the wrong plus! :-( *)
Abort.

(** To use [add_comm] at the point where we need it, we can introduce
    a local lemma stating that [n + m = m + n] (for the _particular_ [m]
    and [n] that we are talking about here), prove this lemma using
    [add_comm], and then use it to do the desired rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.  Qed.

(* ################################################################# *)
(** * Formal vs. Informal Proof *)

(** "_Informal proofs are algorithms; formal proofs are code_." *)

(** An unreadable formal proof: *)

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite IHn'. reflexivity.  Qed.

(** Comments and bullets can make things clearer... *)

Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity.   Qed.

(** ... but it's still nowhere near as readable for a human as
    a careful informal proof: *)

(** - _Theorem_: For any [n], [m] and [p],

      n + (m + p) = (n + m) + p.

    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show that

        0 + (m + p) = (0 + m) + p.

      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where

        n' + (m + p) = (n' + m) + p.

      We must now show that

        (S n') + (m + p) = ((S n') + m) + p.

      By the definition of [+], this follows from

        S (n' + (m + p)) = S ((n' + m) + p),

      which is immediate from the induction hypothesis.  _Qed_. *)

(* ################################################################# *)
(** * More Exercises *)
(* These additional exercises will be used in later chapters.  We
   don't need to work them in class. *)

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.   (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (mul_comm)

    Use [assert] to help prove [add_shuffle3].  You don't need to
    use induction yet. *)

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.

(** Now prove commutativity of multiplication.  You will probably want
    to look for (or define and prove) a "helper" theorem to be used in
    the proof of this one. Hint: what is [n * (1 + k)]? *)

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (plus_leb_compat_l)

    If a hypothesis has the form [H: P -> a = b], then [rewrite H] will
    rewrite [a] to [b] in the goal, and add [P] as a new subgoal. Use
    that in the inductive step of this exercise. *)

Check leb.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (more_exercises)

    Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before you hack!) *)

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
