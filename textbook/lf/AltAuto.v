(** * AltAuto: A Streamlined Treatment of Automation *)

(** So far, we've been doing all our proofs using just a small
    handful of Coq's tactics and completely ignoring its powerful
    facilities for constructing parts of proofs automatically. Getting
    used to them will take some work -- Coq's automation is a power
    tool -- but it will allow us to scale up our efforts to more
    complex definitions and more interesting properties without
    becoming overwhelmed by boring, repetitive, low-level details.

    In this chapter, we'll learn about

    - _tacticals_, which allow tactics to be combined;

    - new tactics that make dealing with hypothesis names less fussy
      and more maintainable;

    - _automatic solvers_ that can prove limited classes of theorems
      without any human assistance;

    - _proof search_ with the [auto] tactic; and

    - the _Ltac_ language for writing tactics.

    These features enable startlingly short proofs. Used properly,
    they can also make proofs more maintainable and robust to changes
    in underlying definitions.

    This chapter is an alternative to the combination of [Imp]
    and [Auto], which cover roughly the same material about
    automation, but in the context of programming language metatheory.
    A deeper treatment of [auto] can be found in the [UseAuto]
    chapter in _Programming Language Foundations_.  *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith List.
From LF Require Import IndProp.

(** As a simple illustration of the benefits of automation,
    let's consider another problem on regular expressions, which we
    formalized in [IndProp].  A given set of strings can be
    denoted by many different regular expressions.  For example, [App
    EmptyString re] matches exactly the same strings as [re].  We can
    write a function that "optimizes" any regular expression into a
    potentially simpler one by applying this fact throughout the r.e.
    (Note that, for simplicity, the function does not optimize
    expressions that arise as the result of other optimizations.) *)

Fixpoint re_opt_e {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App EmptyStr re2 => re_opt_e re2
  | App re1 re2 => App (re_opt_e re1) (re_opt_e re2)
  | Union re1 re2 => Union (re_opt_e re1) (re_opt_e re2)
  | Star re => Star (re_opt_e re)
  | _ => re
  end.

(** We would like to show the equivalence of re's with their
    "optimized" form.  One direction of this equivalence looks like
    this (the other is similar).  *)

Lemma re_opt_e_match : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) simpl. apply MEmpty.
  - (* MChar *) simpl. apply MChar.
  - (* MApp *) simpl.
    destruct re1.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + inversion Hmatch1. simpl. apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
  - (* MUnionL *) simpl. apply MUnionL. apply IH.
  - (* MUnionR *) simpl. apply MUnionR. apply IH.
  - (* MStar0 *) simpl. apply MStar0.
  - (* MStarApp *) simpl. apply MStarApp.
    * apply IH1.
    * apply IH2.
Qed.

(** The amount of repetition in that proof is annoying.  And if
    we wanted to extend the optimization function to handle other,
    similar, rewriting opportunities, it would start to be a real
    problem. We can streamline the proof with _tacticals_, which we
    turn to, next. *)

(* ################################################################# *)
(** * Tacticals *)

(** _Tacticals_ are tactics that take other tactics as arguments --
    "higher-order tactics," if you will.  *)

(* ================================================================= *)
(** ** The [try] Tactical *)

(** If [T] is a tactic, then [try T] is a tactic that is just like [T]
    except that, if [T] fails, [try T] _successfully_ does nothing at
    all instead of failing. *)

Theorem silly1 : forall n, 1 + n = S n.
Proof. try reflexivity. (* this just does [reflexivity] *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  Fail reflexivity.
  try reflexivity. (* proof state is unchanged *)
  apply HP.
Qed.

(** There is no real reason to use [try] in completely manual
    proofs like these, but it is very useful for doing automated
    proofs in conjunction with the [;] tactical, which we show
    next. *)

(* ================================================================= *)
(** ** The Sequence Tactical [;] (Simple Form) *)

(** In its most common form, the sequence tactical, written with
    semicolon [;], takes two tactics as arguments.  The compound
    tactic [T; T'] first performs [T] and then performs [T'] on _each
    subgoal_ generated by [T]. *)

(** For example, consider the following trivial lemma: *)

Lemma simple_semi : forall n, (n + 1 =? 0) = false.
Proof.
  intros n.
  destruct n eqn:E.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

(** We can simplify this proof using the [;] tactical: *)

Lemma simple_semi' : forall n, (n + 1 =? 0) = false.
Proof.
  intros n.
  (* [destruct] the current goal *)
  destruct n;
  (* then [simpl] each resulting subgoal *)
  simpl;
  (* and do [reflexivity] on each resulting subgoal *)
  reflexivity.
Qed.

(** Or even more tersely, [destruct] can do the [intro], and [simpl]
    can be omitted: *)

Lemma simple_semi'' : forall n, (n + 1 =? 0) = false.
Proof.
  destruct n; reflexivity.
Qed.

(** **** Exercise: 3 stars, standard (try_sequence) *)

(** Prove the following theorems using [try] and [;]. Like
    [simple_semi''] above, each proof script should be a sequence [t1;
    ...; tn.] of tactics, and there should be only one period in
    between [Proof.] and [Qed.]. Let's call that a "one shot"
    proof. *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof. (* FILL IN HERE *) Admitted.

Theorem add_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. (* FILL IN HERE *) Admitted.

Fixpoint nonzeros (lst : list nat) :=
  match lst with
  | [] => []
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.

Lemma nonzeros_app : forall lst1 lst2 : list nat,
  nonzeros (lst1 ++ lst2) = (nonzeros lst1) ++ (nonzeros lst2).
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(** Using [try] and [;] together, we can improve the proof about
    regular expression optimization. *)

Lemma re_opt_e_match' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2];
    (* Do the [simpl] for every case here: *)
    simpl.
  - (* MEmpty *) apply MEmpty.
  - (* MChar *) apply MChar.
  - (* MApp *)
    destruct re1;
    (* Most cases follow by the same formula.  Notice that [apply
       MApp] gives two subgoals: [try apply IH1] is run on _both_ of
       them and succeeds on the first but not the second; [apply IH2]
       is then run on this remaining goal. *)
    try (apply MApp; try apply IH1; apply IH2).
    (* The interesting case, on which [try...] does nothing, is when
       [re1 = EmptyStr]. In this case, we have to appeal to the fact
       that [re1] matches only the empty string: *)
    inversion Hmatch1. simpl. apply IH2.
  - (* MUnionL *) apply MUnionL. apply IH.
  - (* MUnionR *) apply MUnionR. apply IH.
  - (* MStar0 *) apply MStar0.
  - (* MStarApp *)  apply MStarApp. apply IH1.  apply IH2.
Qed.

(* ================================================================= *)
(** ** The Sequence Tactical [;] (Local Form) *)

(** The sequence tactical [;] also has a more general form than the
    simple [T; T'] we saw above.  If [T], [T1], ..., [Tn] are tactics,
    then

[[ T; [T1 | T2 | ... | Tn] ]]

    is a tactic that first performs [T] and then locally performs [T1]
    on the first subgoal generated by [T], locally performs [T2] on
    the second subgoal, etc.

    So [T; T'] is just special notation for the case when all of the
    [Ti]'s are the same tactic; i.e., [T; T'] is shorthand for:

      T; [T' | T' | ... | T']

    For example, the following proof makes it clear which tactics are
    used to solve the base case vs. the inductive case.
 *)

Theorem app_length : forall (X : Type) (lst1 lst2 : list X),
    length (lst1 ++ lst2) = (length lst1) + (length lst2).
Proof.
  intros; induction lst1;
    [reflexivity | simpl; rewrite IHlst1; reflexivity].
Qed.

(** The identity tactic [idtac] always succeeds without changing the
    proof state. We can use it to factor out [reflexivity] in the
    previous proof. *)

Theorem app_length' : forall (X : Type) (lst1 lst2 : list X),
    length (lst1 ++ lst2) = (length lst1) + (length lst2).
Proof.
  intros; induction lst1;
    [idtac | simpl; rewrite IHlst1];
    reflexivity.
Qed.

(** **** Exercise: 1 star, standard (notry_sequence) *)

(** Prove the following theorem with a one-shot proof, but this
    time, do not use [try]. *)

Theorem add_assoc' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(** We can use the local form of the sequence tactical to give a
    slightly neater version of our optimization proof. Two lines
    change, as shown below with [<===]. *)

Lemma re_opt_e_match'' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2];
    (* Do the [simpl] for every case here: *)
    simpl.
  - (* MEmpty *) apply MEmpty.
  - (* MChar *) apply MChar.
  - (* MApp *)
    destruct re1;
    try (apply MApp; [apply IH1 | apply IH2]).  (* <=== *)
    inversion Hmatch1. simpl. apply IH2.
  - (* MUnionL *) apply MUnionL. apply IH.
  - (* MUnionR *) apply MUnionR. apply IH.
  - (* MStar0 *) apply MStar0.
  - (* MStarApp *)  apply MStarApp; [apply IH1 | apply IH2].  (* <=== *)
Qed.

(* ================================================================= *)
(** ** The [repeat] Tactical *)

(** The [repeat] tactical takes another tactic and keeps
    applying this tactic until it fails or stops making progress. Here
    is an example showing that [10] is in a long list: *)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

(** The tactic [repeat T] never fails: if the tactic [T] doesn't apply
    to the original goal, then [repeat] still succeeds without
    changing the original goal (i.e., it repeats zero times). *)

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

(** The tactic [repeat T] also does not have any upper bound on the
    number of times it applies [T].  If [T] is a tactic that always
    succeeds, then repeat [T] will loop forever (e.g., [repeat simpl]
    loops, since [simpl] always succeeds). Evaluation in Coq's term
    language, Gallina, is guaranteed to terminate, but tactic
    evaluation is not. This does not affect Coq's logical consistency,
    however, since the job of [repeat] and other tactics is to guide
    Coq in constructing proofs. If the construction process diverges,
    it simply means that we have failed to construct a proof, not that
    we have constructed an incorrect proof. *)

(** **** Exercise: 1 star, standard (ev100)

    Prove that 100 is even. Your proof script should be quite short. *)

Theorem ev100: ev 100.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** An Optimization Exercise  *)
(** **** Exercise: 4 stars, standard (re_opt) *)

(** Consider this more powerful version of the regular expression
    optimizer. *)

Fixpoint re_opt {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App _ EmptySet => EmptySet
  | App EmptyStr re2 => re_opt re2
  | App re1 EmptyStr => re_opt re1
  | App re1 re2 => App (re_opt re1) (re_opt re2)
  | Union EmptySet re2 => re_opt re2
  | Union re1 EmptySet => re_opt re1
  | Union re1 re2 => Union (re_opt re1) (re_opt re2)
  | Star EmptySet => EmptyStr
  | Star EmptyStr => EmptyStr
  | Star re => Star (re_opt re)
  | EmptySet => EmptySet
  | EmptyStr => EmptyStr
  | Char x => Char x
  end.

(* Here is an incredibly tedious manual proof of (one direction of)
   its correctness: *)

Lemma re_opt_match : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) simpl. apply MEmpty.
  - (* MChar *) simpl. apply MChar.
  - (* MApp *) simpl.
    destruct re1.
    + inversion IH1.
    + inversion IH1. simpl. destruct re2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r.  apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
  - (* MUnionL *) simpl.
    destruct re1.
    + inversion IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
  - (* MUnionR *) simpl.
    destruct re1.
    + apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
 - (* MStar0 *) simpl.
    destruct re.
    + apply MEmpty.
    + apply MEmpty.
    + apply MStar0.
    + apply MStar0.
    + apply MStar0.
    + simpl.
      destruct re.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
 - (* MStarApp *) simpl.
   destruct re.
   + inversion IH1.
   + inversion IH1. inversion IH2. apply MEmpty.
   + apply star_app.
     * apply MStar1. apply IH1.
     * apply IH2.
   + apply star_app.
     * apply MStar1.  apply IH1.
     * apply IH2.
   + apply star_app.
     * apply MStar1.  apply IH1.
     * apply IH2.
   + apply star_app.
     * apply MStar1.  apply IH1.
     * apply IH2.
Qed.

(* Use the tacticals described so far to shorten the proof. The proof
   above is about 200 lines. Reduce it to 50 or fewer lines of similar
   density. Solve each of the seven top-level bullets with a one-shot
   proof.

   Hint: use a bottom-up approach. First copy-paste the entire proof
   below. Then automate the innermost bullets first, proceeding
   outwards. Frequently double-check that the entire proof still
   compiles. If it doesn't, undo the most recent changes you made
   until you get back to a compiling proof. *)

Lemma re_opt_match' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
(* FILL IN HERE *) Admitted.
(* Do not modify the following line: *)
Definition manual_grade_for_re_opt : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Tactics that Make Mentioning Names Unnecessary *)

(** So far we have been dependent on knowing the names of
    hypotheses.  For example, to prove the following simple theorem,
    we hardcode the name [HP]: *)

Theorem hyp_name : forall (P : Prop), P -> P.
Proof.
  intros P HP. apply HP.
Qed.

(** We took the trouble to invent a name for [HP], then we had
    to remember that name. If we later change the name in one place,
    we have to change it everywhere. Likewise, if we were to add new
    arguments to the theorem, we would have to adjust the [intros]
    list. That makes it challenging to maintain large proofs. So, Coq
    provides several tactics that make it possible to write proof
    scripts that do not hardcode names. *)

(* ================================================================= *)
(** ** The [assumption] tactic *)

(** The [assumption] tactic is useful to streamline the proof
    above. It looks through the hypotheses and, if it finds the goal
    as one them, it uses that to finish the proof. *)

Theorem no_hyp_name : forall (P : Prop), P -> P.
Proof.
  intros. assumption.
Qed.

(** Some might argue to the contrary that hypothesis names
    improve self-documention of proof scripts. Maybe they do,
    sometimes. But in the case of the two proofs above, the first
    mentions unnecessary detail, whereas the second could be
    paraphrased simply as "the conclusion follows from the
    assumptions."

    Anyway, unlike informal (good) mathematical proofs, Coq proof
    scripts are generally not that illuminating to readers. Worries
    about rich, self-documenting names for hypotheses might be
    misplaced. *)

(* ================================================================= *)
(** ** The [contradiction] tactic *)

(** The [contradiction] tactic handles some ad hoc situations where a
    hypothesis contains [False], or two hypotheses derive [False]. *)

Theorem false_assumed : False -> 0 = 1.
Proof.
  intros H. destruct H.
Qed.

Theorem false_assumed' : False -> 0 = 1.
Proof.
  intros. contradiction.
Qed.

Theorem contras : forall (P : Prop), P -> ~P -> 0 = 1.
Proof.
  intros P HP HNP. exfalso. apply HNP. apply HP.
Qed.

Theorem contras' : forall (P : Prop), P -> ~P -> 0 = 1.
Proof.
  intros. contradiction.
Qed.

(* ================================================================= *)
(** ** The [subst] tactic *)

(** The [subst] tactic substitutes away an identifier, replacing
    it everywhere and eliminating it from the context. That helps
    us to avoid naming hypotheses in [rewrite]s. *)

Theorem many_eq : forall (n m o p : nat),
  n = m ->
  o = p ->
  [n; o] = [m; p].
Proof.
  intros n m o p Hnm Hop. rewrite Hnm. rewrite Hop. reflexivity.
Qed.

Theorem many_eq' : forall (n m o p : nat),
  n = m ->
  o = p ->
  [n; o] = [m; p].
Proof.
  intros. subst. reflexivity.
Qed.

(** Actually there are two forms of this tactic.

     - [subst x] finds an assumption [x = e] or [e = x] in the
       context, replaces [x] with [e] throughout the context and
       current goal, and removes the assumption from the context.

     - [subst] substitutes away _all_ assumptions of the form [x = e]
       or [e = x]. *)

(* ================================================================= *)
(** ** The [constructor] tactic *)

(** The [constructor] tactic tries to find a constructor [c] (from the
    appropriate [Inductive] definition in the current environment)
    that can be applied to solve the current goal. *)

Check ev_0 : ev 0.
Check ev_SS : forall n : nat, ev n -> ev (S (S n)).

Example constructor_example: forall (n:nat),
    ev (n + n).
Proof.
  induction n; simpl.
  - constructor. (* applies ev_0 *)
  - rewrite add_comm. simpl. constructor. (* applies ev_SS *)
    assumption.
Qed.

(** Warning: if more than one constructor can apply,
    [constructor] picks the first one, in the order in which they were
    defined in the [Inductive] definition. That might not be the one
    you want. *)

(* ################################################################# *)
(** * Automatic Solvers *)

(** Coq has several special-purpose tactics that can solve
    certain kinds of goals in a completely automated way. These
    tactics are based on sophisticated algorithms developed for
    verification in specific mathematical or logical domains.

    Some automatic solvers are _decision procedures_, which are
    algorithms that always terminate, and always give a correct
    answer. Here, that means that they always find a correct proof, or
    correctly determine that the goal is invalid.  Other automatic
    solvers are _incomplete_: they might fail to find a proof of a
    valid goal. *)

(* ================================================================= *)
(** ** Linear Integer Arithmetic: The [lia] Tactic *)

(** The [lia] tactic implements a decision procedure for integer
    linear arithmetic, a subset of propositional logic and arithmetic.
    As input it accepts goals constructed as follows:

      - variables and constants of type [nat], [Z], and other integer
        types;

      - arithmetic operators [+], [-], [*], and [^];

      - equality [=] and ordering [<], [>], [<=], [>=]; and

      - the logical connectives [/\], [\/], [~], [->], and [<->]; and
        constants [True] and [False].

    _Linear_ goals involve (in)equalities over expressions of the form
    [c1 * x1 + ... + cn * xn], where [ci] are constants and [xi] are
    variables.

    - For linear goals, [lia] will either solve the goal or fail,
      meaning that the goal is actually invalid.

    - For non-linear goals, [lia] will also either solve the goal or
      fail. But in this case, the failure does not necessarily mean
      that the goal is invalid -- it might just be beyond [lia]'s
      reach to prove because of non-linearity.

    Also, [lia] will do [intros] as necessary. *)

From Coq Require Import Lia.

Theorem lia_succeed1 : forall (n : nat),
  n > 0 -> n * 2 > n.
Proof. lia. Qed.

Theorem lia_succeed2 : forall (n m : nat),
    n * m = m * n.
Proof.
  lia. (* solvable though non-linear *)
Qed.

Theorem lia_fail1 : 0 = 1.
Proof.
  Fail lia. (* goal is invalid *)
Abort.

Theorem lia_fail2 : forall (n : nat),
    n >= 1 -> 2 ^ n = 2 * 2 ^ (n - 1).
Proof.
  Fail lia. (*goal is non-linear, valid, but unsolvable by lia *)
Abort.

(** There are other tactics that can solve arithmetic goals.  The
    [ring] and [field] tactics, for example, can solve equations over
    the algebraic structures of _rings_ and _fields_, from which the
    tactics get their names. These tactics do not do [intros]. *)

Require Import Ring.

Theorem mult_comm : forall (n m : nat),
    n * m = m * n.
Proof.
  intros n m. ring.
Qed.

(* ================================================================= *)
(** ** Equalities: The [congruence] Tactic *)

(** The [lia] tactic makes use of facts about addition and
    multiplication to prove equalities. A more basic way of treating
    such formulas is to regard every function appearing in them as
    a black box: nothing is known about the function's behavior.
    Based on the properties of equality itself, it is still possible
    to prove some formulas. For example, [y = f x -> g y = g (f x)],
    even if we know nothing about [f] or [g]:
 *)

Theorem eq_example1 :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
    y = f x -> g y = g (f x).
Proof.
  intros. rewrite H. reflexivity.
Qed.

(** The essential properties of equality are that it is:

    - reflexive

    - symmetric

    - transitive

    - a _congruence_: it respects function and predicate
      application. *)

(** It is that congruence property that we're using when we
    [rewrite] in the proof above: if [a = b] then [f a = f b].  (The
    [ProofObjects] chapter explores this idea further under the
    name "Leibniz equality".) *)

(** The [congruence] tactic is a decision procedure for equality with
    uninterpreted functions and other symbols.  *)

Theorem eq_example1' :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
    y = f x -> g y = g (f x).
Proof.
  congruence.
Qed.

(** The [congruence] tactic is able to work with constructors,
    even taking advantage of their injectivity and distinctness. *)

Theorem eq_example2 : forall (n m o p : nat),
    n = m ->
    o = p ->
    (n, o) = (m, p).
Proof.
  congruence.
Qed.

Theorem eq_example3 : forall (X : Type) (h : X) (t : list X),
    [] <> h :: t.
Proof.
  congruence.
Qed.

(* ================================================================= *)
(** ** Propositions: The [intuition] Tactic *)

(** A _tautology_ is a logical formula that is always
    provable. A formula is _propositional_ if it does not use
    quantifiers -- or at least, if quantifiers do not have to be
    instantiated to carry out the proof. The [intuition] tactic
    implements a decision procedure for propositional tautologies in
    Coq's constructive (that is, intuitionistic) logic. Even if a goal
    is not a propositional tautology, [intuition] will still attempt
    to reduce it to simpler subgoals. *)

Theorem intuition_succeed1 : forall (P : Prop),
    P -> P.
Proof. intuition. Qed.

Theorem intuition_succeed2 : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof. intuition. Qed.

Theorem intuition_simplify1 : forall (P : Prop),
    ~~P -> P.
Proof.
  intuition. (* not a constructively valid formula *)
Abort.

Theorem intuition_simplify2 : forall (x y : nat) (P Q : nat -> Prop),
  x = y /\ (P x -> Q x) /\ P x -> Q y.
Proof.
  Fail congruence. (* the propositions stump it *)
  intuition. (* the [=] stumps it, but it simplifies the propositions *)
  congruence.
Qed.

(** In the previous example, neither [congruence] nor
    [intuition] alone can solve the goal. But after [intuition]
    simplifies the propositions involved in the goal, [congruence] can
    succeed. For situations like this, [intuition] takes an optional
    argument, which is a tactic to apply to all the unsolved goals
    that [intuition] generated. Using that we can offer a shorter
    proof: *)

Theorem intuition_simplify2' : forall (x y : nat) (P Q : nat -> Prop),
  x = y /\ (P x -> Q x) /\ P x -> Q y.
Proof.
  intuition congruence.
Qed.

(* ================================================================= *)
(** ** Exercises with Automatic Solvers *)

(** **** Exercise: 2 stars, standard (automatic_solvers)

    The exercises below are gleaned from previous chapters, where they
    were proved with (relatively) long proof scripts. Each should now
    be provable with just a single invocation of an automatic
    solver. *)

Theorem plus_id_exercise_from_basics : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. (* FILL IN HERE *) Admitted.

Theorem add_assoc_from_induction : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. (* FILL IN HERE *) Admitted.

Theorem S_injective_from_tactics : forall (n m : nat),
  S n = S m ->
  n = m.
Proof. (* FILL IN HERE *) Admitted.

Theorem or_distributes_over_and_from_logic : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * Search Tactics *)

(** The automated solvers we just discussed are capable of finding
    proofs in specific domains. Some of them might pay attention to
    local hypotheses, but overall they don't make use of any custom
    lemmas we've proved, or that are provided by libraries that we
    load.

    Another kind of automation that Coq provides does just that: the
    [auto] tactic and its variants search for proofs that can be
    assembled out of hypotheses and lemmas. *)

(* ================================================================= *)
(** ** The [auto] Tactic *)

(** Until this chapter, our proof scripts mostly applied relevant
    hypotheses or lemmas by name, and one at a time. *)

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. apply H3.
Qed.

(** The [auto] tactic frees us from this drudgery by _searching_ for a
    sequence of applications that will prove the goal: *)

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

(** The [auto] tactic solves goals that are solvable by any combination of
     - [intros] and
     - [apply] (of hypotheses from the local context, by default). *)

(** Using [auto] is always "safe" in the sense that it will
    never fail and will never change the proof state: either it
    completely solves the current goal, or it does nothing. *)

(** Here is a more interesting example showing [auto]'s power: *)

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

(** Proof search could, in principle, take an arbitrarily long time,
    so there are limits to how far [auto] will search by default. *)

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  (* When it cannot solve the goal, [auto] does nothing *)
  auto.
  (* Optional argument says how deep to search (default is 5) *)
  auto 6.
Qed.

(** The [auto] tactic considers the hypotheses in the current context
    together with a _hint database_ of other lemmas and constructors.
    Some common facts about equality and logical operators are
    installed in the hint database by default. *)

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. auto. Qed.

(** If we want to see which facts [auto] is using, we can use
    [info_auto] instead. *)

Example auto_example_5 : 2 = 2.
Proof.
  (* [auto] subsumes [reflexivity] because [eq_refl] is in the hint
     database. *)
  info_auto.
Qed.

(** We can extend the hint database with theorem [t] just for the
    purposes of one application of [auto] by writing [auto using
    t]. *)

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. lia. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto using le_antisym.
Qed.

(** Of course, in any given development there will probably be
    some specific constructors and lemmas that are used very often in
    proofs.  We can add these to a hint database named [db] by writing

      Create HintDb db.

    to create the database, then

      Hint Resolve T : db.

    to add [T] to the database, where [T] is a top-level theorem or a
    constructor of an inductively defined proposition (i.e., anything
    whose type is an implication). We tell [auto] to use that database
    by writing [auto with db]. Technically creation of the database
    is optional; Coq will create it automatically the first time
    we use [Hint]. *)

Create HintDb le_db.
Hint Resolve le_antisym : le_db.

Example auto_example_6' : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto with le_db.
Qed.

(** As a shorthand, we can write

      Hint Constructors c : db.

    to tell Coq to do a [Hint Resolve] for _all_ of the constructors
    from the inductive definition of [c].

    It is also sometimes necessary to add

      Hint Unfold d : db.

    where [d] is a defined symbol, so that [auto] knows to expand uses
    of [d], thus enabling further possibilities for applying lemmas that
    it knows about. *)

Definition is_fortytwo x := (x = 42).

Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.  (* does nothing *)
Abort.

Hint Unfold is_fortytwo : le_db.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof. info_auto with le_db. Qed.

(** The "global" database that [auto] always uses is named [core].
    You can add your own hints to it, but the Coq manual discourages
    that, preferring instead to have specialized databases for
    specific developments. Many of the important libraries have their
    own hint databases that you can tag in: [arith], [bool], [datatypes]
    (including lists), etc. *)

Example auto_example_8 : forall (n m : nat),
    n + m = m + n.
Proof.
  auto. (* no progress *)
  info_auto with arith. (* uses [Nat.add_comm] *)
Qed.

(** **** Exercise: 3 stars, standard (re_opt_match_auto) *)

(** Use [auto] to shorten your proof of [re_opt_match] even
    more. Eliminate all uses of [apply], thus removing the need to
    name specific constructors and lemmas about regular expressions.
    The number of lines of proof script won't decrease that much,
    because [auto] won't be able to find [induction], [destruct], or
    [inversion] opportunities by itself.

    Hint: again, use a bottom-up approach. Always keep the proof
    compiling. You might find it easier to return to the original,
    very long proof, and shorten it, rather than starting with
    [re_opt_match']; but, either way can work. *)

Lemma re_opt_match'' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
(* FILL IN HERE *) Admitted.
(* Do not modify the following line: *)
Definition manual_grade_for_re_opt_match'' : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (pumping_redux)

    Use [auto], [lia], and any other useful tactics from this chapter
    to shorten your proof (or the "official" solution proof) of the
    weak Pumping Lemma exercise from [IndProp]. *)

Import Pumping.

Lemma weak_pumping : forall T (re : reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists s1 s2 s3,
      s = s1 ++ s2 ++ s3 /\
        s2 <> [] /\
        forall m, s1 ++ napp m s2 ++ s3 =~ re.

Proof.
(* FILL IN HERE *) Admitted.
(* Do not modify the following line: *)
Definition manual_grade_for_pumping_redux : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (pumping_redux_strong)

    Use [auto], [lia], and any other useful tactics from this chapter
    to shorten your proof (or the "official" solution proof) of the
    stronger Pumping Lemma exercise from [IndProp]. *)

Lemma pumping : forall T (re : reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists s1 s2 s3,
      s = s1 ++ s2 ++ s3 /\
        s2 <> [] /\
        length s1 + length s2 <= pumping_constant re /\
        forall m, s1 ++ napp m s2 ++ s3 =~ re.

Proof.
(* FILL IN HERE *) Admitted.
(* Do not modify the following line: *)
Definition manual_grade_for_pumping_redux_strong : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** The [eauto] variant *)

(** There is a variant of [auto] (and other tactics, such as
    [apply]) that makes it possible to delay instantiation of
    quantifiers. To motivate this feature, consider again this simple
    example: *)

Example trans_example1:  forall a b c d,
    a <= b + b * c  ->
    (1 + c) * b <= d ->
    a <= d.
Proof.
  intros a b c d H1 H2.
  apply le_trans with (b + b * c).
    (* ^ We must supply the intermediate value *)
  - apply H1.
  - simpl in H2. rewrite mul_comm. apply H2.
Qed.

(** In the first step of the proof, we had to explicitly provide a
    longish expression to help Coq instantiate a "hidden" argument to
    the [le_trans] constructor. This was needed because the definition
    of [le_trans]...

    le_trans : forall m n o : nat, m <= n -> n <= o -> m <= o

    is quantified over a variable, [n], that does not appear in its
    conclusion, so unifying its conclusion with the goal state doesn't
    help Coq find a suitable value for this variable.  If we leave
    out the [with], this step fails ("Error: Unable to find an
    instance for the variable [n]").

    We already know one way to avoid an explicit [with] clause, namely
    to provide [H1] as the (first) explicit argument to [le_trans].
    But here's another way, using the [eapply tactic]: *)

Example trans_example1':  forall a b c d,
    a <= b + b * c  ->
    (1 + c) * b <= d ->
    a <= d.
Proof.
  intros a b c d H1 H2.
  eapply le_trans. (* 1 *)
  - apply H1. (* 2 *)
  - simpl in H2. rewrite mul_comm. apply H2.
Qed.

(** The [eapply H] tactic behaves just like [apply H] except
    that, after it finishes unifying the goal state with the
    conclusion of [H], it does not bother to check whether all the
    variables that were introduced in the process have been given
    concrete values during unification.

    If you step through the proof above, you'll see that the goal
    state at position [1] mentions the _existential variable_ [?n] in
    both of the generated subgoals.  The next step (which gets us to
    position [2]) replaces [?n] with a concrete value.  When we start
    working on the second subgoal (position [3]), we observe that the
    occurrence of [?n] in this subgoal has been replaced by the value
    that it was given during the first subgoal. *)

(** Several of the tactics that we've seen so far, including
    [exists], [constructor], and [auto], have [e...] variants.  For
    example, here's a proof using [eauto]: *)

Example trans_example2:  forall a b c d,
    a <= b + b * c  ->
    b + b * c <= d ->
    a <= d.
Proof.
  intros a b c d H1 H2.
  info_eauto using le_trans.
Qed.

(** The [eauto] tactic works just like [auto], except that it
    uses [eapply] instead of [apply].

    Pro tip: One might think that, since [eapply] and [eauto] are more
    powerful than [apply] and [auto], it would be a good idea to use
    them all the time.  Unfortunately, they are also significantly
    slower -- especially [eauto].  Coq experts tend to use [apply] and
    [auto] most of the time, only switching to the [e] variants when
    the ordinary variants don't do the job. *)

(* ################################################################# *)
(** * Ltac: The Tactic Language *)

(** Most of the tactics we have been using are implemented in
    OCaml, where they are able to use an API to access Coq's internal
    structures at a low level. But this is seldom worth the trouble
    for ordinary Coq users.

    Coq has a high-level language called Ltac for programming new
    tactics in Coq itself, without having to escape to OCaml.
    Actually we've been using Ltac all along -- anytime we are in
    proof mode, we've been writing Ltac programs. At their most basic,
    those programs are just invocations of built-in tactics.  The
    tactical constructs we learned at the beginning of this chapter
    are also part of Ltac.

    What we turn to, next, is ways to use Ltac to reduce the amount of
    proof script we have to write ourselves. *)

(* ================================================================= *)
(** ** Ltac Functions *)

(** Here is a simple [Ltac] example: *)

Ltac simpl_and_try tac := simpl; try tac.

(** This defines a new tactic called [simpl_and_try] that takes one
    tactic [tac] as an argument and is defined to be equivalent to
    [simpl; try tac]. Now writing "[simpl_and_try reflexivity.]" in a
    proof will be the same as writing "[simpl; try reflexivity.]" *)

Example sat_ex1 : 1 + 1 = 2.
Proof. simpl_and_try reflexivity. Qed.

Example sat_ex2 : forall (n : nat), 1 - 1 + n + 1 = 1 + n.
Proof. simpl_and_try reflexivity. lia. Qed.

(** Of course, that little tactic is not so useful. But it
    demonstrates that we can parameterize Ltac-defined tactics, and
    that their bodies are themselves tactics that will be run in the
    context of a proof. So Ltac can be used to create functions on
    tactics. *)

(** For a more useful tactic, consider these three proofs from
    [Basics], and how structurally similar they all are: *)

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

(** We can factor out the common structure:

    - Do a destruct.

    - For each branch, finish with [reflexivity] -- if possible. *)

Ltac destructpf x :=
  destruct x; try reflexivity.

Theorem plus_1_neq_0' : forall n : nat,
    (n + 1) =? 0 = false.
Proof. intros n; destructpf n. Qed.

Theorem negb_involutive' : forall b : bool,
  negb (negb b) = b.
Proof. intros b; destructpf b. Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c; destructpf b; destructpf c.
Qed.

(** **** Exercise: 1 star, standard (andb3_exchange)

    Re-prove the following theorem from [Basics], using only
    [intros] and [destructpf]. You should have a one-shot proof. *)

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (andb_true_elim2)

    The following theorem from [Basics] can't be proved with
    [destructpf]. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b eqn:Eb.
  - simpl. intros H. rewrite H. reflexivity.
  - simpl. intros H. destruct c eqn:Ec.
    + reflexivity.
    + rewrite H. reflexivity.
Qed.

(** Uncomment the definition of [destructpf'], below, and define your
    own, improved version of [destructpf]. Use it to prove the
    theorem. *)

(*
Ltac destructpf' x := ...
*)

(** Your one-shot proof should need only [intros] and
    [destructpf']. *)

Theorem andb_true_elim2' : forall b c : bool,
    andb b c = true -> c = true.
Proof. (* FILL IN HERE *) Admitted.

(** Double-check that [intros] and your new [destructpf'] still
    suffice to prove this earlier theorem -- i.e., that your improved
    tactic is general enough to still prove it in one shot: *)

Theorem andb3_exchange' :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof. (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Ltac Pattern Matching *)

(** Here is another common proof pattern that we have seen in
    many simple proofs by induction: *)

Theorem app_nil_r : forall (X : Type) (lst : list X),
    lst ++ [] = lst.
Proof.
  intros X lst. induction lst as [ | h t IHt].
  - reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

(** At the point we [rewrite], we can't substitute away [t]: it
    is present on both sides of the equality in the inductive
    hypothesis [IHt : t ++ [] = t]. How can we pick out which
    hypothesis to rewrite in an Ltac tactic?

    To solve this and other problems, Ltac contains a pattern-matching
    tactic [match goal].  It allows us to match against the _proof
    state_ rather than against a program. *)

Theorem match_ex1 : True.
Proof.
  match goal with
  | [ |- True ] => apply I
  end.
Qed.

(** The syntax is similar to a [match] in Gallina (Coq's term
    language), but has some new features:

    - The word [goal] here is a keyword, rather than an expression
      being matched. It means to match against the proof state, rather
      than a program term.

    - The square brackets around the pattern can often be omitted, but
      they do make it easier to visually distinguish which part of the
      code is the pattern.

    - The turnstile [|-] separates the hypothesis patterns (if any)
      from the conclusion pattern. It represents the big horizontal
      line shown by your IDE in the proof state: the hypotheses are to
      the left of it, the conclusion is to the right.

    - The hypotheses in the pattern need not completely describe all
      the hypotheses present in the proof state. It is fine for there
      to be additional hypotheses in the proof state that do not match
      any of the patterns. The point is for [match goal] to pick out
      particular hypotheses of interest, rather than fully specify the
      proof state.

    - The right-hand side of a branch is a tactic to run, rather than
      a program term.

    The single branch above therefore specifies to match a goal whose
    conclusion is the term [True] and whose hypotheses may be anything.
    If such a match occurs, it will run [apply I]. *)

(** There may be multiple branches, which are tried in order. *)

Theorem match_ex2 : True /\ True.
Proof.
  match goal with
  | [ |- True ] => apply I
  | [ |- True /\ True ] => split; apply I
  end.
Qed.

(** To see what branches are being tried, it can help to insert calls
    to the identity tactic [idtac]. It optionally accepts an argument
    to print out as debugging information. *)

Theorem match_ex2' : True /\ True.
Proof.
  match goal with
  | [ |- True ] => idtac "branch 1"; apply I
  | [ |- True /\ True ] => idtac "branch 2"; split; apply I
  end.
Qed.

(** Only the second branch was tried. The first one did not match the
    goal. *)

(** The semantics of the tactic [match goal] have a big
    difference with the semantics of the term [match].  With the
    latter, the first matching pattern is chosen, and later branches
    are never considered. In fact, an error is produced if later
    branches are known to be redundant. *)

Fail Definition redundant_match (n : nat) : nat :=
  match n with
  | x => x
  | 0 => 1
  end.

(** But with [match goal], if the tactic for the branch fails,
    pattern matching continues with the next branch, until a branch
    succeeds, or all branches have failed. *)

Theorem match_ex2'' : True /\ True.
Proof.
  match goal with
  | [ |- _ ] => idtac "branch 1"; apply I
  | [ |- True /\ True ] => idtac "branch 2"; split; apply I
  end.
Qed.

(** The first branch was tried but failed, then the second
    branch was tried and succeeded. If all the branches fail, the
    [match goal] fails. *)

Theorem match_ex2''' : True /\ True.
Proof.
  Fail match goal with
  | [ |- _ ] => idtac "branch 1"; apply I
  | [ |- _ ] => idtac "branch 2"; apply I
  end.
Abort.

(** Next, let's try matching against hypotheses. We can bind a
    hypothesis name, as with [H] below, and use that name on the
    right-hand side of the branch. *)

Theorem match_ex3 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  match goal with
  | [ H : _ |- _ ] => apply H
  end.
Qed.

(** The actual name of the hypothesis is of course [HP], but the
    pattern binds it as [H]. Using [idtac], we can even observe the
    actual name: stepping through the following proof causes "HP" to
    be printed. *)

Theorem match_ex3' : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  match goal with
  | [ H : _ |- _ ] => idtac H; apply H
  end.
Qed.

(** We'll keep using [idtac] for awhile to observe the behavior
    of [match goal], but, note that it isn't necessary for the
    successful proof of any of the following examples.

    If there are multiple hypotheses that match, which one does Ltac
    choose? Here is a big difference with regular [match] against
    terms: Ltac will try all possible matches until one succeeds (or
    all have failed). *)

Theorem match_ex4 : forall (P Q : Prop), P -> Q -> P.
Proof.
  intros P Q HP HQ.
  match goal with
  | [ H : _ |- _ ] => idtac H; apply H
  end.
Qed.

(** That example prints "HQ" followed by "HP". Ltac first
    matched against the most recently introduced hypothesis [HQ] and
    tried applying it. That did not solve the goal. So Ltac
    _backtracks_ and tries the next most-recent matching hypothesis,
    which is [HP]. Applying that does succeed. *)

(** But if there were no successful hypotheses, the entire match
    would fail: *)

Theorem match_ex5 : forall (P Q R : Prop), P -> Q -> R.
Proof.
  intros P Q R HP HQ.
  Fail match goal with
  | [ H : _ |- _ ] => idtac H; apply H
  end.
Abort.

(** So far we haven't been very demanding in how to match
    hypotheses. The _wildcard_ (aka _joker_) pattern we've used
    matches everything. We could be more specific by using
    _metavariables_: *)

Theorem match_ex5 : forall (P Q : Prop), P -> Q -> P.
Proof.
  intros P Q HP HQ.
  match goal with
  | [ H : ?X |- ?X ] => idtac H; apply H
  end.
Qed.

(** Note that this time, the only hypothesis printed by [idtac]
    is [HP]. The [HQ] hypothesis is ruled out, because it does not
    have the form [?X |- ?X].

    The occurrences of [?X] in that pattern are as _metavariables_
    that stand for the same term appearing both as the type of
    hypothesis [H] and as the conclusion of the goal.

    (The syntax of [match goal] requires that [?] to distinguish
    metavariables from other identifiers that might be in
    scope. However, the [?] is used only in the pattern. On the
    right-hand side of the branch, it's actually required to drop the
    [?].) *)

(** Now we have seen yet another difference between [match goal]
    and regular [match] against terms: [match goal] allows a
    metavariable to be used multiple times in a pattern, each time
    standing for the same term.  The regular [match] does not allow
    that: *)

Fail Definition dup_first_two_elts (lst : list nat) :=
  match lst with
  | x :: x :: _ => true
  | _ => false
  end.

(** The technical term for this is _linearity_: regular [match]
    requires pattern variables to be _linear_, meaning that they are
    used only once. Tactic [match goal] permits _non-linear_
    metavariables, meaning that they can be used multiple times in a
    pattern and must bind the same term each time. *)

(** Now that we've learned a bit about [match goal], let's return
    to the proof pattern of some simple inductions: *)

Theorem app_nil_r' : forall (X : Type) (lst : list X),
    lst ++ [] = lst.
Proof.
  intros X lst. induction lst as [ | h t IHt].
  - reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

(** With [match goal], we can automate that proof pattern: *)

Ltac simple_induction t :=
  induction t; simpl;
  try match goal with
      | [H : _ = _ |- _] => rewrite H
      end;
  reflexivity.

Theorem app_nil_r'' : forall (X : Type) (lst : list X),
    lst ++ [] = lst.
Proof.
  intros X lst. simple_induction lst.
Qed.

(** That works great! Here are two other proofs that follow the same
    pattern. *)

Theorem add_assoc'' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_assoc''' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p. simple_induction n.
Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  intros n m. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem plus_n_Sm' : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  intros n m. simple_induction n.
Qed.

(* ================================================================= *)
(** ** Using [match goal] to Prove Tautologies *)

(** The Ltac source code of [intuition] can be found in the GitHub
    repo for Coq in [theories/Init/Tauto.v]. At heart, it is a big
    loop that runs [match goal] to find propositions it can [apply]
    and [destruct].

    Let's build our own simplified "knock off" of [intuition]. Here's
    a start on implication: *)

Ltac imp_intuition :=
  repeat match goal with
         | [ H : ?P |- ?P ] => apply H
         | [ |- forall _, _ ] => intro
         | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => apply H1 in H2
         end.

(** That tactic repeatedly matches against the goal until the match
    fails to make progress. At each step, the [match goal] does one of
    three things:

    - Finds that the conclusion is already in the hypotheses, in which
      case the goal is finished.

    - Finds that the conclusion is a quantification, in which case it
      is introduced. Since implication [P -> Q] is itself a
      quantification [forall (_ : P), Q], this case handles introduction of
      implications, too.

    - Finds that two formulas of the form [?P -> ?Q] and [?P] are in
      the hypotheses. This is the first time we've seen an example of
      matching against two hypotheses simultaneously.  Note that the
      metavariable [?P] is once more non-linear: the same formula must
      occur in two different hypotheses.  In this case, the tactic
      uses forward reasoning to change hypothesis [H2] into [?Q].

    Already we can prove many theorems with this tactic: *)

Example imp1 : forall (P : Prop), P -> P.
Proof. imp_intuition. Qed.

Example imp2 : forall (P Q : Prop), P -> (P -> Q) -> Q.
Proof. imp_intuition. Qed.

Example imp3 : forall (P Q R : Prop), (P -> Q -> R) -> (Q -> P -> R).
Proof. imp_intuition. Qed.

(** Suppose we were to add a new logical connective: [nand], the "not
    and" connective, aka _Sheffer stroke_. *)

Inductive nand (P Q : Prop) :=
| stroke : ~P -> ~Q -> nand P Q.

(** Classically, [nand P Q] would be equivalent to [~(P /\ Q)].  But
    constructively, only one direction of that is provable. *)

Theorem nand_not_and : forall (P Q : Prop),
    nand P Q -> ~ (P /\ Q).
Proof.
  intros P Q Hnand [HP HQ]. destruct Hnand as [HNP HNQ]. auto.
Qed.

(** Some other usual theorems about [nand] are still provable,
    though. *)

Theorem nand_comm : forall (P Q : Prop),
    nand P Q <-> nand Q P.
Proof.
  intros P Q. split.
  - intros H. destruct H. apply stroke; assumption.
  - intros H. destruct H. apply stroke; assumption.
Qed.

Theorem nand_not : forall (P : Prop),
    nand P P <-> ~P.
Proof.
  intros P. split.
  - intros H. destruct H. assumption.
  - intros H. apply stroke; assumption.
Qed.

(** **** Exercise: 4 stars, advanced (nand_intuition) *)

(** Create your own tactic [nand_intuition]. It should be able to
    prove the three theorems above -- [nand_not_and], [nand_comm], and
    [nand_not] -- fully automatically. You may not use [intuition] or
    any other automated solvers in your solution.

    Begin by copying the code from [imp_intuition]. You will then need
    to expand it to handle conjunctions, negations, bi-implications,
    and [nand]. *)

(* Ltac nand_intuition := ... *)

(** Each of the three theorems below, and many others involving these
    logical connectives, should be provable with just
    [Proof. nand_intuition. Qed.] *)

Theorem nand_comm' : forall (P Q : Prop),
    nand P Q <-> nand Q P.
Proof. (* FILL IN HERE *) Admitted.

Theorem nand_not' : forall (P : Prop),
    nand P P <-> ~P.
Proof. (* FILL IN HERE *) Admitted.

Theorem nand_not_and' : forall (P Q : Prop),
    nand P Q -> ~ (P /\ Q).
Proof. (* FILL IN HERE *) Admitted.
(* Do not modify the following line: *)
Definition manual_grade_for_nand_intuition : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Review *)

(** We've learned a lot of new features and tactics in this chapter:

    - [try], [;], [repeat]

    - [assumption], [contradiction], [subst], [constructor]

    - [lia], [congruence], [intuition]

    - [auto], [eauto], [eapply]

    - Ltac functions and [match goal] *)

(* 2022-06-16 11:23 *)
