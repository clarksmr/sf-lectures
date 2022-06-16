Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import IndPrinciples.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From LF Require Import IndPrinciples.
Import Check.

Goal True.

idtac "-------------------  plus_one_r'  --------------------".
idtac " ".

idtac "#> plus_one_r'".
idtac "Possible points: 2".
check_type @plus_one_r' ((forall n : nat, n + 1 = S n)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_one_r'.
Goal True.
idtac " ".

idtac "-------------------  booltree_ind  --------------------".
idtac " ".

idtac "#> booltree_ind_type_correct".
idtac "Possible points: 2".
check_type @booltree_ind_type_correct (booltree_ind_type).
idtac "Assumptions:".
Abort.
Print Assumptions booltree_ind_type_correct.
Goal True.
idtac " ".

idtac "-------------------  toy_ind  --------------------".
idtac " ".

idtac "#> Toy_correct".
idtac "Possible points: 2".
check_type @Toy_correct (
(exists (f : bool -> Toy) (g : nat -> Toy -> Toy),
   forall P : Toy -> Prop,
   (forall b : bool, P (f b)) ->
   (forall (n : nat) (t : Toy), P t -> P (g n t)) -> forall t : Toy, P t)).
idtac "Assumptions:".
Abort.
Print Assumptions Toy_correct.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 6".
idtac "Max points - advanced: 6".
idtac "".
idtac "Allowed Axioms:".
idtac "functional_extensionality".
idtac "FunctionalExtensionality.functional_extensionality_dep".
idtac "plus_le".
idtac "le_trans".
idtac "le_plus_l".
idtac "add_le_cases".
idtac "Sn_le_Sm__n_le_m".
idtac "O_le_n".
idtac "".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "Below is a summary of the automatically graded exercises that are incomplete.".
idtac "".
idtac "The output for each exercise can be any of the following:".
idtac "  - 'Closed under the global context', if it is complete".
idtac "  - 'MANUAL', if it is manually graded".
idtac "  - A list of pending axioms, containing unproven assumptions. In this case".
idtac "    the exercise is considered complete, if the axioms are all allowed.".
idtac "".
idtac "********** Standard **********".
idtac "---------- plus_one_r' ---------".
Print Assumptions plus_one_r'.
idtac "---------- booltree_ind_type_correct ---------".
Print Assumptions booltree_ind_type_correct.
idtac "---------- Toy_correct ---------".
Print Assumptions Toy_correct.
idtac "".
idtac "********** Advanced **********".
Abort.

(* 2022-06-16 11:18 *)

(* 2022-06-16 11:18 *)
