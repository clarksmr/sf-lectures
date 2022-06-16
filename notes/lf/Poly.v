(** * Poly: Polymorphism and Higher-Order Functions *)

(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Lists.

(* ================================================================= *)
(** ** Polymorphic Lists *)

(** Instead of defining new lists for each type, like
    this... *)

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

(** ...Coq lets us give a _polymorphic_ definition that allows
    list elements of any type: *)

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

(** [list] itself is a _function_ from types to types. *)

Check list : Type -> Type.

(** The [X] in the definition of [list] becomes a parameter to
    the list constructors [nil] and [cons]. *)

Check (nil nat) : list nat.

Check (cons nat 3 (nil nat)) : list nat.

Check nil : forall X : Type, list X.

Check cons : forall X : Type, X -> list X -> list X.

(** Side note: In .v files, the "forall" quantifier is spelled
    out in letters.  In the corresponding HTML files, it is usually
    typeset as the standard mathematical "upside down A." *)

Check (cons nat 2 (cons nat 1 (nil nat)))
      : list nat.

(** We can now define polymorphic versions of the functions
    we've already seen... *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

(* QUIZ

    Recall the types of [cons] and [nil]:

       nil : forall X : Type, list X
       cons : forall X : Type, X -> list X -> list X

    What is the type of [cons bool true (cons nat 3 (nil nat))]?

    (1) [nat -> list nat -> list nat]

    (2) [forall (X:Type), X -> list X -> list X]

    (3) [list nat]

    (4) [list bool]

    (5) Ill-typed
*)
(* QUIZ

    Recall the definition of [repeat]:

    Fixpoint repeat (X : Type) (x : X) (count : nat)
                  : list X :=
      match count with
      | 0 => nil X
      | S count' => cons X x (repeat X x count')
      end.

    What is the type of [repeat]?

    (1) [nat -> nat -> list nat]

    (2) [X -> nat -> list X]

    (3) [forall (X Y: Type), X -> nat -> list Y]

    (4) [forall (X:Type), X -> nat -> list X]

    (5) Ill-typed
*)
(* QUIZ

    What is the type of [repeat nat 1 2]?

    (1) [list nat]

    (2) [forall (X:Type), X -> nat -> list X]

    (3) [list bool]

    (4) Ill-typed
*)

(* ----------------------------------------------------------------- *)
(** *** Type Annotation Inference *)

(** Let's write the definition of [repeat] again, but this time we
    won't specify the types of any of the arguments.  Will Coq still
    accept it? *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(** Indeed it will.  Let's see what type Coq has assigned to [repeat']... *)

Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.

(** Coq has used _type inference_ to deduce the proper types
    for [X], [x], and [count]. *)

(* ----------------------------------------------------------------- *)
(** *** Type Argument Synthesis *)

(** Supplying every type _argument_ is also boring, but Coq
    can usually infer them: *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ----------------------------------------------------------------- *)
(** *** Implicit Arguments *)

(** In fact, we can go further and even avoid writing [_]'s in most
    cases by telling Coq _always_ to infer the type argument(s) of a
    given function.

    The [Arguments] directive specifies the name of the function (or
    constructor) and then lists the (leading) argument names to be
    treated as implicit, each surrounded by curly braces. *)

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

(** Now we don't have to supply any type arguments at all in the example: *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(** Alternatively, we can declare arguments implicit by
    surrounding them with curly braces instead of parens: *)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(** Here are polymorphic versions of a few more functions that
    we'll need later: *)

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** Supplying Type Arguments Explicitly *)

(** In general, it's fine to just let Coq infer all type
    arguments.  But occasionally this can lead to problems: *)

Fail Definition mynil := nil.

(** We can fix this with an explicit type declaration: *)

Definition mynil : list nat := nil.

(** Alternatively, we can force the implicit arguments to be explicit by
    prefixing the function name with [@]. *)

Check @nil : forall X : Type, list X.

Definition mynil' := @nil nat.

(** Using argument synthesis and implicit arguments, we can
    define concrete notations that work for lists of any type. *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

(* QUIZ

    Which type does Coq assign to the following expression?

    (The square brackets here and in the following quizzes are list
    brackets, not "this is a Coq expression inside a comment" brackets.)

       [1;2;3]

    (1) [list nat]

    (2) [list bool]

    (3) [bool]

    (4) No type can be assigned
*)
(* QUIZ

    What about this one?

       [3 + 4] ++ nil

    (1) [list nat]

    (2) [list bool]

    (3) [bool]

    (4) No type can be assigned
*)

(* QUIZ

    What about this one?

       andb true false ++ nil

    (1) [list nat]

    (2) [list bool]

    (3) [bool]

    (4) No type can be assigned
*)

(* QUIZ

    What about this one?

        [1; nil]

    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)

(* QUIZ

    What about this one?

        [[1]; nil]

    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)

(* QUIZ

    And what about this one?

         [1] :: [nil]

    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)

(* QUIZ

    This one?

        @nil bool

    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)

(* QUIZ

    This one?

        nil bool

    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)

(* QUIZ

    This one?

        @nil 3

    (1) [list nat]

    (2) [list (list nat)]

    (3) [list bool]

    (4) No type can be assigned
*)

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** **** Exercise: 2 stars, standard (poly_exercises)

    Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Complete the proofs
    below. *)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (more_poly_exercises)

    Here are some slightly more interesting ones... *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Polymorphic Pairs *)

(** Similarly... *)

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).

(** We can also use the [Notation] mechanism to define the standard
    notation for _product types_ (i.e., the types of pairs): *)

Notation "X * Y" := (prod X Y) : type_scope.

(** (The annotation [: type_scope] tells Coq that this abbreviation
    should only be used when parsing types, not when parsing
    expressions.  This avoids a clash with the multiplication
    symbol.) *)

(** Be careful not to get [(X,Y)] and [X*Y] confused! *)
Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(** What does this function do? *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* ================================================================= *)
(** ** Polymorphic Options *)

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X}.
Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Functions as Data *)

(* ================================================================= *)
(** ** Higher-Order Functions *)

(** Functions in Coq are _first class_. *)

Definition doit3times {X : Type} (f : X->X) (n : X) : X :=
  f (f (f n)).

Check @doit3times : forall X : Type, (X -> X) -> X -> X.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Filter *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(** The [filter] function (especially when combined with some
    other functions we'll see later) enables a powerful
    _collection-oriented_ programming style. *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter odd l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Anonymous Functions *)

(** Functions can be constructed "on the fly" without giving
    them names. *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

(** The expression [(fun n => n * n)] can be read as "the function
    that, given a number [n], yields [n * n]." *)

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Map *)

Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2:
  map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [even n;odd n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

(* QUIZ

    Recall the definition of [map]:

      Fixpoint map {X Y : Type} (f : X->Y) (l : list X)
                   : list Y :=
        match l with
        | []     => []
        | h :: t => (f h) :: (map f t)
        end.

    What is the type of [map]?

    (1) [forall X Y : Type, X -> Y -> list X -> list Y]

    (2) [X -> Y -> list X -> list Y]

    (3) [forall X Y : Type, (X -> Y) -> list X -> list Y]

    (4) [forall X : Type, (X -> X) -> list X -> list X]
*)

(** Lists are not the only inductive type for which [map] makes sense.
    Here is a [map] for the [option] type: *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

(* ================================================================= *)
(** ** Fold *)

Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** This is the "reduce" in map/reduce... *)

Check (fold andb) : list bool -> bool -> bool.

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* QUIZ

    Here is the definition of [fold] again:

     Fixpoint fold {X Y : Type}
                   (f : X->Y->Y) (l : list X) (b : Y)
                 : Y :=
       match l with
       | nil => b
       | h :: t => f h (fold f t b)
       end.

    What is the type of [fold]?

    (1) [forall X Y : Type, (X -> Y -> Y) -> list X -> Y -> Y]

    (2) [X -> Y -> (X -> Y -> Y) -> list X -> Y -> Y]

    (3) [forall X Y : Type, X -> Y -> Y -> list X -> Y -> Y]

    (4) [X -> Y ->  X -> Y -> Y -> list X -> Y -> Y]

*)

(* QUIZ

    What is the type of [fold plus]?

    (1) [forall X Y : Type, list X -> Y -> Y]

    (2) [nat -> nat -> list nat -> nat -> nat]

    (3) [forall Y : Type, list nat -> Y -> nat]

    (4) [list nat -> nat -> nat]

    (5) [forall X Y : Type, list nat -> nat -> nat]

*)

(* QUIZ

    What does [fold plus [1;2;3;4] 0] simplify to?

   (1) [[1;2;3;4]]

   (2) [0]

   (3) [10]

   (4) [[3;7;0]]

*)

(* ================================================================= *)
(** ** Functions That Construct Functions *)

(** Here are two more functions that _return_ functions
    as results. *)

Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** A two-argument function in Coq is actually a function that
    returns a function! *)

Check plus : nat -> nat -> nat.

Definition plus3 := plus 3.
Check plus3 : nat -> nat.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

