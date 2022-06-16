(** * Maps: Total and Partial Maps *)

(** _Maps_ (or _dictionaries_) are ubiquitous data structures both in
    ordinary programming and in the theory of programming languages;
    we're going to need them in many places in the coming chapters.

    They also make a nice case study using ideas we've seen in
    previous chapters, including building data structures out of
    higher-order functions (from [Basics] and [Poly]) and the use of
    reflection to streamline proofs (from [IndProp]).

    We'll define two flavors of maps: _total_ maps, which include a
    "default" element to be returned when a key being looked up
    doesn't exist, and _partial_ maps, which instead return an
    [option] to indicate success or failure.  The latter is defined in
    terms of the former, using [None] as the default element. *)

(* ################################################################# *)
(** * The Coq Standard Library *)

(** One small digression before we begin...

    Unlike the chapters we have seen so far, this one does not
    [Require Import] the chapter before it (nor, transitively, all the
    earlier chapters).  Instead, in this chapter and from now, on
    we're going to import the definitions and theorems we need
    directly from Coq's standard library stuff.  You should not notice
    much difference, though, because we've been careful to name our
    own definitions and theorems the same as their counterparts in the
    standard library, wherever they overlap. *)

From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

(** Documentation for the standard library can be found at
    https://coq.inria.fr/library/.

    The [Search] command is a good way to look for theorems involving
    objects of specific types. See [Lists] for a reminder of how
    to use it. *)

(** If you want to find out how or where a notation is defined, the
    [Locate] command is useful.  For example, where is the natural
    addition operation defined in the standard library? *)

Locate "+".

(** (There are several uses of the [+] notation, but only one for
    naturals.) *)

Print Init.Nat.add.

(** We'll see some more uses of [Locate] in the [Imp] chapter. *)

(* ################################################################# *)
(** * Identifiers *)

(** First, we need a type for the keys that we will use to index into
    our maps.  In [Lists.v] we introduced a fresh type [id] for a
    similar purpose; here and for the rest of _Software Foundations_
    we will use the [string] type from Coq's standard library. *)

(** To compare strings, we use the function [eqb] from the [String]
    module in the standard library. *)

Check String.eqb_refl :
  forall x : string, (x =? x)%string = true.

(** We will often use a few basic properties of string equality... *)
Check String.eqb_eq :
  forall n m : string, (n =? m)%string = true <-> n = m.
Check String.eqb_neq :
  forall n m : string, (n =? m)%string = false <-> n <> m.
Check String.eqb_spec :
  forall x y : string, reflect (x = y) (String.eqb x y).

(* ################################################################# *)
(** * Total Maps *)

(** Our main job in this chapter will be to build a definition of
    partial maps that is similar in behavior to the one we saw in the
    [Lists] chapter, plus accompanying lemmas about its behavior.

    This time around, though, we're going to use _functions_, rather
    than lists of key-value pairs, to build maps.  The advantage of
    this representation is that it offers a more "extensional" view of
    maps: two maps that respond to queries in the same way will be
    represented as exactly the same function, rather than just as
    "equivalent" list structures.  This, in turn, simplifies proofs
    that use maps. *)

(** We build up to partial maps in two steps.  First, we define a type
    of _total maps_ that return a default value when we look up a key
    that is not present in the map. *)

Definition total_map (A : Type) := string -> A.

(** Intuitively, a total map over an element type [A] is just a
    function that can be used to look up [string]s, yielding [A]s. *)

(** The function [t_empty] yields an empty total map, given a default
    element; this map always returns the default element when applied
    to any string. *)

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

(** More interesting is the map-updating function, which (as always)
    takes a map [m], a key [x], and a value [v] and returns a new map
    that takes [x] to [v] and takes every other key to whatever [m]
    does.  The novelty here is that we achieve this effect by wrapping
    a new function around the old one. *)

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

(** This definition is a nice example of higher-order programming:
    [t_update] takes a _function_ [m] and yields a new function
    [fun x' => ...] that behaves like the desired map. *)

(** For example, we can build a map taking [string]s to [bool]s, where
    ["foo"] and ["bar"] are mapped to [true] and every other key is
    mapped to [false], like this: *)

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

(** Next, let's introduce some notations to facilitate working with
    maps. *)

(** First, we use the following notation to represent an empty total
    map with a default value. *)
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

(** We next introduce a convenient notation for extending an existing
    map with a new binding. *)
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

(** The [examplemap] above can now be defined as follows: *)

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

(** This completes the definition of total maps.  Note that we
    don't need to define a [find] operation on this representation of
    maps because it is just function application! *)

Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.

Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.

(** When we use maps in later chapters, we'll need several fundamental
    facts about how they behave. *)

(** Even if you don't bother to work the following exercises,
    make sure you thoroughly understand the statements of the
    lemmas! *)

(** (Some of the proofs require the functional extensionality axiom,
    which was discussed in the [Logic] chapter.) *)

(** **** Exercise: 1 star, standard, optional (t_apply_empty)

    First, the empty map returns its default element for all keys: *)

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_eq)

    Next, if we update a map [m] at a key [x] with a new value [v]
    and then look up [x] in the map resulting from the [update], we
    get back [v]: *)

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_neq)

    On the other hand, if we update a map [m] at a key [x1] and then
    look up a _different_ key [x2] in the resulting map, we get the
    same result that [m] would have given: *)

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_shadow)

    If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: *)

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (t_update_same)

    Given [string]s [x1] and [x2], we can use the tactic
    [destruct (eqb_spec x1 x2)] to simultaneously perform case
    analysis on the result of [String.eqb x1 x2] and generate
    hypotheses about the equality (in the sense of [=]) of [x1] and
    [x2].  With the example in chapter [IndProp] as a template,
    use [String.eqb_spec] to prove the following theorem, which states
    that if we update a map to assign key [x] the same value as it
    already has in [m], then the result is equal to [m]: *)

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (t_update_permute)

    Similarly, use [String.eqb_spec] to prove one final property of
    the [update] function: If we update a map [m] at two distinct
    keys, it doesn't matter in which order we do the updates. *)

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Partial maps *)

(** Lastly, we define _partial maps_ on top of total maps.  A partial
    map with elements of type [A] is simply a total map with elements
    of type [option A] and default element [None]. *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

(** We introduce a similar notation for partial maps: *)
Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

(** We can also hide the last case when it is empty. *)
Notation "x '|->' v" := (update empty x v)
  (at level 100).

Definition examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).

(** We now straightforwardly lift all of the basic lemmas about total
    maps to partial maps.  *)

Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

(** One last thing: For partial maps, it's convenient to introduce a
    notion of map inclusion, stating that all the entries in one map
    are also present in another: *)

Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

(** We can then show that map update preserves map inclusion -- that is: *)

Lemma includedin_update : forall (A : Type) (m m' : partial_map A)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold includedin.
  intros A m m' x vx H.
  intros y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - rewrite update_neq. rewrite update_neq.
    + apply H.
    + apply Hxy.
    + apply Hxy.
Qed.

(** This property is quite useful for reasoning about languages with
    variable binding -- e.g., the Simply Typed Lambda Calculus, which
    we will see in _Programming Language Foundations_, where maps are
    used to keep track of which program variables are defined in a
    given scope. *)

(* 2022-06-16 11:18 *)
