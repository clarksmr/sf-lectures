(** * Logic: Logic in Coq *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Tactics.

(** So far, we have seen...

       - _propositions_: factual claims
             - equality propositions ([e1 = e2])
             - implications ([P -> Q])
             - quantified propositions ([forall x, P])

       - _proofs_: ways of presenting evidence for the truth of a
          proposition

    In this chapter we will introduce several more flavors of both
    propositions and proofs. *)

(** Like everything in Coq, propositions have a _type_: *)

Check (3 = 3) : Prop.

Check (forall n m : nat, n + m = m + n) : Prop.

(** Note that _all_ syntactically well-formed propositions have type
    [Prop] in Coq, regardless of whether they are true.

    Simply _being_ a proposition is one thing; being _provable_ is
    a different thing! *)

Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.

(** So far, we've seen one primary place that propositions can appear:
    in [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** Propositions are first-class entities in Coq.  For example,
    we can name them: *)

Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.

Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity.  Qed.

(** We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.

(** In Coq, functions that return propositions are said to define
    _properties_ of their arguments.

    For instance, here's a (polymorphic) property defining the
    familiar notion of an _injective function_. *)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.

(** The equality operator [=] is a (binary) function that returns a
    [Prop].

    The expression [n = m] is syntactic sugar for [eq n m] (defined in
    Coq's standard library using the [Notation] mechanism). Because
    [eq] can be used with elements of any type, it is also
    polymorphic: *)

Check @eq : forall A : Type, A -> A -> Prop.

(* QUIZ

    What is the type of the following expression?

       pred (S O) = O

   (1) [Prop]

   (2) [nat->Prop]

   (3) [forall n:nat, Prop]

   (4) [nat->nat]

   (5) Not typeable

*)

(* QUIZ

    What is the type of the following expression?

      forall n:nat, pred (S n) = n

   (1) [Prop]

   (2) [nat->Prop]

   (3) [forall n:nat, Prop]

   (4) [nat->nat]

   (5) Not typeable

*)

(* QUIZ

    What is the type of the following expression?

      forall n:nat, S (pred n) = n

   (1) [Prop]

   (2) [nat->Prop]

   (3) [nat->nat]

   (4) Not typeable

*)

(* QUIZ

    What is the type of the following expression?

      forall n:nat, S (pred n)

   (1) [Prop]

   (2) [nat->Prop]

   (3) [nat->nat]

   (4) Not typeable
*)

(* QUIZ

    What is the type of the following expression?

      fun n:nat => S (pred n)

   (1) [Prop]

   (2) [nat->Prop]

   (3) [nat->nat]

   (4) Not typeable
*)

(* QUIZ

    What is the type of the following expression?

      fun n:nat => S (pred n) = n

   (1) [Prop]

   (2) [nat->Prop]

   (3) [nat->nat]

   (4) Not typeable

*)

(* QUIZ

    Which of the following is _not_ a proposition?

    (1) [3 + 2 = 4]

    (2) [3 + 2 = 5]

    (3) [3 + 2 =? 5]

    (4) [((3+2) =? 4) = false]

    (5) [forall n, (((3+2) =? n) = true) -> n = 5]

    (6) All of these are propositions
*)

(* ################################################################# *)
(** * Logical Connectives *)

(* ================================================================= *)
(** ** Conjunction *)

(** The _conjunction_, or _logical and_, of propositions [A] and [B]
    is written [A /\ B], representing the claim that both [A] and [B]
    are true. *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** To prove a conjunction, use the [split] tactic.  It will generate
    two subgoals, one for each part of the statement: *)

Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 * 2 = 4 *) reflexivity.
Qed.

(** For any propositions [A] and [B], if we assume that [A] is true
    and that [B] is true, we can conclude that [A /\ B] is also
    true. *)

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
    (* WORK IN CLASS *) Admitted.

(** So much for proving conjunctive statements.  To go in the other
    direction -- i.e., to _use_ a conjunctive hypothesis to help prove
    something else -- we employ the [destruct] tactic.

    When the current proof context contains a hypothesis [H] of the
    form [A /\ B], writing [destruct H as [HA HB]] will remove [H]
    from the context and replace it with two new hypotheses: [HA],
    stating that [A] is true, and [HB], stating that [B] is true.  *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORK IN CLASS *) Admitted.

(** As usual, we can also destruct [H] right when we introduce it,
    instead of introducing and then destructing it: *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** You may wonder why we bothered packing the two hypotheses [n = 0]
    and [m = 0] into a single conjunction, since we could have also
    stated the theorem with two separate premises: *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** For the present example, both ways work.  But in other
    situations we may wind up with a conjunctive hypothesis in the
    middle of a proof... *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORK IN CLASS *) Admitted.

(** By the way, the infix notation [/\] is actually just syntactic
    sugar for [and A B].  That is, [and] is a Coq operator that takes
    two propositions as arguments and yields a proposition. *)

Check and : Prop -> Prop -> Prop.

(* ================================================================= *)
(** ** Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_,
    of two propositions: [A \/ B] is true when either [A] or [B]
    is.  (This infix notation stands for [or A B], where [or : Prop ->
    Prop -> Prop].) *)

(** To use a disjunctive hypothesis in a proof, we proceed by case
    analysis -- which, as with other data types like [nat], can be done
    explicitly with [destruct] or implicitly with an [intros]
    pattern: *)

Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on
     [n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

(** We can see in this example that, when we perform case
    analysis on a disjunction [A \/ B], we must separately satisfy two
    proof obligations, each showing that the conclusion holds under a
    different assumption -- [A] in the first subgoal and [B] in the
    second.  Note that the case analysis pattern [[Hn | Hm]] allows
    us to name the hypotheses that are generated for the subgoals. *)

(** Conversely, to show that a disjunction holds, it suffices to show
    that one of its sides holds. This can be done via two tactics,
    [left] and [right].  As their names imply, the first one requires
    proving the left side of the disjunction, while the second
    requires proving its right side.  Here is a trivial use... *)

Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** ... and here is a slightly more interesting example requiring both
    [left] and [right]: *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORK IN CLASS *) Admitted.

(** **** Exercise: 1 star, standard (mult_is_O) *)
Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (or_commut) *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Falsehood and Negation

    So far, we have mostly been concerned with proving "positive"
    statements -- addition is commutative, appending lists is
    associative, etc.  Of course, we may also be interested in
    negative results, demonstrating that some given proposition is
    _not_ true. Such statements are expressed with the logical
    negation operator [~]. *)

(** To see how negation works, recall the _principle of explosion_
    from the [Tactics] chapter, which asserts that, if we assume a
    contradiction, then any other proposition can be derived.

    Following this intuition, we could define [~ P] ("not [P]") as
    [forall Q, P -> Q].

    Coq actually makes a slightly different (but equivalent) choice,
    defining [~ P] as [P -> False], where [False] is a specific
    contradictory proposition defined in the standard library. *)

Module NotPlayground.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not : Prop -> Prop.

End NotPlayground.

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we get [False] into the proof
    context, we can use [destruct] on it to complete any goal: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORK IN CLASS *) Admitted.

(** Inequality is a frequent enough form of negated statement
    that there is a special notation for it, [x <> y]:

      Notation "x <> y" := (~(x = y)).
*)

(** We can use [not] to state that [0] and [1] are different elements
    of [nat]: *)

Theorem zero_not_one : 0 <> 1.
Proof.
    unfold not.
    intros contra.
    discriminate contra.
Qed.

(** It takes a little practice to get used to working with negation in
    Coq.  Even though _you_ can see perfectly well why a statement
    involving negation is true, it can be a little tricky at first to
    make Coq understand it!  Here are proofs of a few familiar facts
    to get you warmed up. *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORK IN CLASS *) Admitted.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORK IN CLASS *) Admitted.

(** Since inequality involves a negation, it also requires a little
    practice to be able to work with it fluently.  Here is one useful
    trick:

    If you are trying to prove a goal that is nonsensical (e.g., the
    goal state is [false = true]), apply [ex_falso_quodlibet] to
    change the goal to [False].

    This makes it easier to use assumptions of the form [~P] that may
    be available in the context -- in particular, assumptions of the
    form [x<>y]. *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we need
    besides [intros] and [apply]?

        forall X, forall a b : X, (a=b) /\ (a<>b) -> False.

    (1) [destruct], [unfold], [left] and [right]

    (2) [destruct] and [unfold]

    (3) only [destruct]

    (4) [left] and/or [right]

    (5) only [unfold]

    (6) none of the above

*)
Lemma quiz1: forall X, forall a b : X, (a=b) /\ (a<>b) -> False.
Proof.
  intros X a b [H0 H1]. apply H1 in H0. apply H0.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we
    need besides [intros] and [apply]?

        forall P Q : Prop,  P \/ Q -> ~~(P \/ Q).

    (1) [destruct], [unfold], [left] and [right]

    (2) [destruct] and [unfold]

    (3) only [destruct]

    (4) [left] and/or [right]

    (5) only [unfold]

    (6) none of the above

*)
Lemma quiz2 : forall P Q : Prop,  P \/ Q -> ~~(P \/ Q).
Proof.
  intros P Q H H1. apply H1 in H. apply H.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we
    need besides [intros] and [apply]?

         forall A B: Prop, A -> (A \/ ~~B).

    (1) [destruct], [unfold], [left] and [right]

    (2) [destruct] and [unfold]

    (3) only [destruct]

    (4) [left] and/or [right]

    (5) only [unfold]

    (6) none of the above

*)
Lemma quiz3 : forall A B: Prop, A -> (A \/ ~~B).
Proof.
intros P Q H. left. apply H.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we need
    besides [intros] and [apply]?

         forall P Q: Prop,  P \/ Q -> ~~P \/ ~~Q.

    (1) [destruct], [unfold], [left] and [right]

    (2) [destruct] and [unfold]

    (3) only [destruct]

    (4) [left] and/or [right]

    (5) only [unfold]

    (6) none of the above

*)
Lemma quiz4 : forall P Q: Prop,  P \/ Q -> ~~P \/ ~~Q.
Proof.
  intros P Q [H0 | H0].
  - (* left *)
    left. intros H1. apply H1 in H0. apply H0.
  - (* right *)
    right. intros H1. apply H1 in H0. apply H0.
Qed.

(* QUIZ

    To prove the following proposition, which tactics will we need
    besides [intros] and [apply]?

         forall A : Prop, 1=0 -> (A \/ ~A).

    (1) [discriminate], [unfold], [left] and [right]

    (2) [discriminate] and [unfold]

    (3) only [discriminate]

    (4) [left] and/or [right]

    (5) only [unfold]

    (6) none of the above

*)
Lemma quiz5 : forall A : Prop, 1=0 -> (A \/ ~A).
Proof.
  intros P H. discriminate H.
Qed.

(* ================================================================= *)
(** ** Truth *)

(** Besides [False], Coq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    constant [I : True], which is also defined in the standard
    library: *)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** Unlike [False], which is used extensively, [True] is used
    relatively rarely, since it is trivial (and therefore
    uninteresting) to prove as a goal, and conversely it provides no
    interesting information when used as a hypothesis. *)

(* ================================================================= *)
(** ** Logical Equivalence *)

(** The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is simply the conjunction
    of two implications. *)

Module IffPlayground.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End IffPlayground.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORK IN CLASS *) Admitted.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORK IN CLASS *) Admitted.

(** Example: using [apply] with [<->]. *)

Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
  intros P Q R Hiff H HP. apply H.  apply Hiff. apply HP.
Qed.

Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
  intros P Q R Hiff H HQ. apply H.  apply Hiff. apply HQ.
Qed.

(** **** Exercise: 1 star, standard, optional (iff_properties)

    Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Setoids and Logical Equivalence *)

(** Some of Coq's tactics treat [iff] statements specially, avoiding
    the need for some low-level proof-state manipulation.  In
    particular, [rewrite] and [reflexivity] can be used with [iff]
    statements, not just equalities.  To enable this behavior, we have
    to import the Coq library that supports it: *)

From Coq Require Import Setoids.Setoid.

(** A "setoid" is a set equipped with an equivalence relation,
    such as [=] or [<->]. *)

(** Here is a simple example demonstrating how these tactics work with
    [iff].  First, let's prove a couple of basic iff equivalences. *)

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Existential Quantification *)

(** To prove a statement of the form [exists x, P], we must show that
    [P] holds for some specific choice of value for [x], known as the
    _witness_ of the existential.  This is done in two steps: First,
    we explicitly tell Coq which witness [t] we have in mind by
    invoking the tactic [exists t].  Then we prove that [P] holds after
    all occurrences of [x] are replaced by [t]. *)

Definition Even x := exists n : nat, x = double n.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORK IN CLASS *) Admitted.

(** **** Exercise: 3 stars, standard, optional (leb_plus_exists) *)
Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n+x.
Proof.
(* FILL IN HERE *) Admitted.

Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * Programming with Propositions *)

(** What does it mean to say that "an element [x] occurs in a
    list [l]"?

       - If [l] is the empty list, then [x] cannot occur in it, so the
         property "[x] appears in [l]" is simply false.

       - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
         occurs in [l] if it is equal to [x'] or if it occurs in
         [l']. *)

(** We can translate this directly into a straightforward recursive
    function taking an element and a list and returning a proposition (!): *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORK IN CLASS *) Admitted.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORK IN CLASS *) Admitted.

(** We can also prove more generic, higher-level lemmas about [In]. *)

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(* ################################################################# *)
(** * Applying Theorems to Arguments *)

(** Coq also treats _proofs_ as first-class objects! *)

(** We have seen that we can use [Check] to ask Coq to print the type
    of an expression.  We can also use it to ask what theorem a
    particular identifier refers to. *)

Check plus     : nat -> nat -> nat.
Check add_comm : forall n m : nat, n + m = m + n.

(** Coq checks the _statement_ of the [add_comm] theorem (or prints
    it for us, if we leave off the part beginning with the colon) in
    the same way that it checks the _type_ of any term (e.g., plus)
    that we ask it to [Check].

    Why? *)

(** The reason is that the identifier [add_comm] actually refers to a
    _proof object_, which represents a logical derivation establishing
    of the truth of the statement [forall n m : nat, n + m = m + n].  The
    type of this object is the proposition that it is a proof of. *)

(** The type of an ordinary function tells us what we can do
    with it.
       - e.g., if we have a term of type [nat -> nat -> nat], we can
         give it two [nat]s as arguments and get a [nat] back.

    Similarly, the statement of a theorem tells us what we can use
    that theorem for.
       - if we have a term of type [n = m -> n + n = m + m] and we
         provide it two numbers [n] and [m] plus an "argument" of type
         [n = m], we can derive [n + n = m + m]. *)

(** Coq actually allows us to _apply_ a theorem as if it were a
    function.

    This is often handy in proof scripts -- e.g., suppose we want too
    prove the following: *)

Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.

(** It appears at first sight that we ought to be able to prove this
    by rewriting with [add_comm] twice to make the two sides match.
    The problem, however, is that the second [rewrite] will undo the
    effect of the first. *)

Proof.
  intros x y z.
  rewrite add_comm.
  rewrite add_comm.
  (* We are back where we started... *)
Abort.

(** We can fix this by applying [add_comm] to the arguments we
    want it be to instantiated with.  Then the [rewrite] can only happen
    in one place. *)

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.

(** Let's see another example of using a theorem like a function.

    The following theorem says: any list [l] containing some element
    must be nonempty. *)

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

(** We should be able to use this theorem to prove the special case
    where [x] is [42]. However, naively, the tactic [apply in_not_nil]
    will fail because it cannot infer the value of [x]. *)

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

(** There are several ways to work around this: *)

(** Use [apply ... with ...] *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(** Use [apply ... in ...] *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(** Explicitly apply the lemma to the value for [x]. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(** Explicitly apply the lemma to a hypothesis. *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Lemma quiz : forall a b : nat,
  a = b -> b = 42 ->
  (forall (X : Type) (n m o : X),
          n = m -> m = o -> n = o) ->
  True.
Proof.
  intros a b H1 H2 trans_eq.

(* QUIZ

    Suppose we have

      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
          n = m -> m = o -> n = o

    What is the type of this proof object?

      trans_eq nat a b 42 H1 H2

    (1) [a = b]

    (2) [42 = a]

    (3) [a = 42]

    (4) Does not typecheck

 *)
Check trans_eq nat a b 42 H1 H2
  : a = 42.

(* QUIZ

    Suppose, again, that we have

      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
          n = m -> m = o -> n = o

    What is the type of this proof object?

      trans_eq nat b 42 a H2

    (1) [b = a]

    (2) [b = a -> 42 = a]

    (3) [42 = a -> b = a]

    (4) Does not typecheck

 *)
Check trans_eq nat b 42 a H2
    : 42 = a -> b = a.

(* QUIZ

    Suppose, again, that we have

      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
          n = m -> m = o -> n = o

    What is the type of this proof object?

      trans_eq _ 42 a b

    (1) [a = b -> b = 42 -> a = 42]

    (2) [42 = a -> a = b -> 42 = b]

    (3) [a = 42 -> 42 = b -> a = b]

    (4) Does not typecheck

 *)
Check trans_eq _ 42 a b
    : 42 = a -> a = b -> 42 = b.

(* QUIZ

    Suppose, again, that we have

      a, b : nat
      H1 : a = b
      H2 : b = 42
      trans_eq : forall (X : Type) (n m o : X),
          n = m -> m = o -> n = o

    What is the type of this proof object?

      trans_eq _ _ _ _ H2 H1

    (1) [b = a]

    (2) [42 = a]

    (3) [a = 42]

    (4) Does not typecheck

 *)
Fail Check trans_eq _ _ _ _ H2 H1.

Abort.

(* ################################################################# *)
(** * Coq vs. Set Theory *)

(** Coq's logical core, the _Calculus of Inductive
    Constructions_, is a "metalanguage for mathematics" in the same
    sense as familiar foundations for paper-and-pencil math, like
    Zermelo-Fraenkel Set Theory (ZFC).

    Mostly, the differences are not too important.  But there are a
    few points worth discussing... *)

(* ================================================================= *)
(** ** Functional Extensionality *)

(** Coq's logic is intentionally quite minimal.  This means that there
    are occasionally some cases where translating standard
    mathematical reasoning into Coq can be cumbersome or even
    impossible, unless we enrich the core logic with additional
    axioms. *)

(** For example, we can write an equality proposition stating
    that two _functions_ are equal to each other: *)

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

(** In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same output on every input:

    (forall x, f x = g x) -> f = g

    This is known as the principle of _functional extensionality_. *)

(** However, functional extensionality is not part of Coq's built-in
    logic.  This means that some apparently "obvious" propositions are
    not provable. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.

(** However, if we like, we can add functional extensionality to Coq's
    core using the [Axiom] command. *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** Defining something as an [Axiom] has the same effect as stating a
    theorem and skipping its proof using [Admitted], but it alerts the
    reader that this isn't just something we're going to come back and
    fill in later! *)

(** We can now invoke functional extensionality in proofs: *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.

(** Naturally, we must be careful when adding new axioms into Coq's
    logic, as this can render it _inconsistent_ -- that is, it may
    become possible to prove every proposition, including [False],
    [2+2=5], etc.!

    Unfortunately, there is no simple way of telling whether an axiom
    is safe to add: hard work by highly trained mathematicians is
    often required to establish the consistency of any particular
    combination of axioms.

    Fortunately, it is known that adding functional extensionality, in
    particular, _is_ consistent. *)

(** To check whether a particular proof relies on any additional
    axioms, use the [Print Assumptions] command:
    [Print Assumptions function_equality_ex2]. *)

(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g

    (If you try this yourself, you may also see [add_comm] listed as
    an assumption, depending on whether the copy of [Tactics.v] in the
    local directory has the proof of [add_comm] filled in.) *)

(* QUIZ

    Is this provable by just [reflexivity], without
    [functional_extensionality]?

      [(fun xs => 1 :: xs) = (fun xs => [1] ++ xs)]

    (1) Yes

    (2) No

 *)
Example cons_1_eq_ex : (fun xs => 1 :: xs) = (fun xs => [1] ++ xs).
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Propositions vs. Booleans

    We've seen two different ways of expressing logical claims in Coq:
    with _booleans_ (of type [bool]), and with _propositions_ (of type
    [Prop]).

    Here are the key differences between [bool] and [Prop]:

                                           bool     Prop
                                           ====     ====
           decidable?                       yes       no
           useable with match?             yes       no
           equalities rewritable?          no        yes
*)

(* ================================================================= *)
(** ** Working with Decidable Properties *)

(** Since every function terminates on all inputs in Coq, a
    function of type [nat -> bool] is a _decision procedure_ -- i.e.,
    it yields [true] or [false] on all inputs.

      - For example, [even : nat -> bool] is a decision procedure for
        the property "is even".

    It follows that there are some properties of numbers that we
    _cannot_ express as functions of type [nat -> bool].

      - For example, the property "is the code of a halting Turing
        machine" is undecidable, so there is no way to write it as a
        function of type [nat -> bool].

    On the other hand, [nat->Prop] is the type of _all_ properties of
    numbers that can be expressed in Coq's logic, including both
    decidable and undecidable ones.

      - For example, "being the code of a halting Turing machine" is a
        perfectly legitimate mathematical property, and we can
        absolutely represent it as a Coq expression of type [nat ->
        Prop].
*)

(** Since [Prop] includes _both_ decidable and undecidable properties,
    we have two choices when when we want to formalize a property that
    happens to be decidable: we can express it as a boolean
    computation or as a function into [Prop].

    For instance, to claim that a number [n] is even, we can say
    either... *)

(** ... that [even n] evaluates to [true]... *)
Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

(** ... or that there exists some [k] such that [n = double k]. *)
Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.

(** Of course, it would be pretty strange if these two
    characterizations of evenness did not describe the same set of
    natural numbers!  Fortunately, we can prove that they do... *)

(** We first need two helper lemmas. *)
Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  (* Hint: Use the [even_S] lemma from [Induction.v]. *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Now the main theorem: *)
Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

(** In view of this theorem, we say that the boolean computation
    [even n] is _reflected_ in the truth of the proposition
    [exists k, n = double k]. *)

(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say either
      - (1) that [n =? m] returns [true], or
      - (2) that [n = m].
    Again, these two notions are equivalent. *)

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite eqb_refl. reflexivity.
Qed.

(** Even when the boolean and propositional formulations of a claim
    are equivalent from a purely _logical_ perspective, they are often
    not equivalent from the point of view of convenience for some
    specific purpose. *)

(** For example, we cannot _test_ whether or not a [Prop] is
    true in a function definition; as a consequence, the following
    code fragment is rejected: *)

Fail
Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** An important side benefit of stating facts using booleans
    is enabling some proof automation through computation with Coq
    terms, a technique known as _proof by reflection_.

    Consider the following statement: *)

Example even_1000 : Even 1000.

(** The most direct way to prove this is to give the value of [k]
    explicitly. *)

Proof. unfold Even. exists 500. reflexivity. Qed.

(** The proof of the corresponding boolean statement is even
    simpler, because we don't have to invent the witness: Coq's
    computation mechanism does it for us! *)

Example even_1000' : even 1000 = true.
Proof. reflexivity. Qed.

(** What is interesting is that, since the two notions are equivalent,
    we can use the boolean formulation to prove the other one without
    mentioning the value 500 explicitly: *)

Example even_1000'' : Even 1000.
Proof. apply even_bool_prop. reflexivity. Qed.

(** Another notable difference is that the negation of a "boolean
    fact" is straightforward to state and prove: simply flip the
    expected boolean result. *)

Example not_even_1001 : even 1001 = false.
Proof.
  (* WORK IN CLASS *) Admitted.

(** In contrast, propositional negation can be more difficult
    to work with directly. *)

Example not_even_1001' : ~(Even 1001).
Proof.
  (* WORK IN CLASS *) Admitted.

(** Equality provides a complementary example, where it is sometimes
    easier to work in the propositional world.

    Knowing that [(n =? m) = true] is generally of little direct help in
    the middle of a proof involving [n] and [m]; however, if we
    convert the statement to the equivalent form [n = m], we can
    rewrite with it. *)

Lemma plus_eqb_example : forall n m p : nat,
  n =? m = true -> n + p =? m + p = true.
Proof.
  (* WORK IN CLASS *) Admitted.

(** We won't discuss reflection any further for the moment, but it
    serves as a good example showing the different strengths of
    booleans and general propositions; being able to cross back and
    forth between the boolean and propositional worlds will often be
    convenient in later chapters. *)

(* ================================================================= *)
(** ** Classical vs. Constructive Logic *)

(** The following reasoning principle is _not_ derivable in
    Coq (though, again, it can consistently be added): *)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

(** Logics like Coq's, which do not assume the excluded middle, are
    referred to as _constructive logics_.

    More conventional logical systems such as ZFC, in which the
    excluded middle does hold for arbitrary propositions, are referred
    to as _classical_. *)

