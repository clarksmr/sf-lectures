Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import AltAuto.

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

From LF Require Import AltAuto.
Import Check.

Goal True.

idtac "-------------------  try_sequence  --------------------".
idtac " ".

idtac "#> andb_eq_orb".
idtac "Possible points: 1".
check_type @andb_eq_orb (
(forall b c : Basics.bool, Basics.andb b c = Basics.orb b c -> b = c)).
idtac "Assumptions:".
Abort.
Print Assumptions andb_eq_orb.
Goal True.
idtac " ".

idtac "#> add_assoc".
idtac "Possible points: 1".
check_type @add_assoc ((forall n m p : nat, n + (m + p) = n + m + p)).
idtac "Assumptions:".
Abort.
Print Assumptions add_assoc.
Goal True.
idtac " ".

idtac "#> nonzeros_app".
idtac "Possible points: 1".
check_type @nonzeros_app (
(forall lst1 lst2 : Poly.list nat,
 nonzeros (@Poly.app nat lst1 lst2) =
 @Poly.app nat (nonzeros lst1) (nonzeros lst2))).
idtac "Assumptions:".
Abort.
Print Assumptions nonzeros_app.
Goal True.
idtac " ".

idtac "-------------------  notry_sequence  --------------------".
idtac " ".

idtac "#> add_assoc'".
idtac "Possible points: 1".
check_type @add_assoc' ((forall n m p : nat, n + (m + p) = n + m + p)).
idtac "Assumptions:".
Abort.
Print Assumptions add_assoc'.
Goal True.
idtac " ".

idtac "-------------------  ev100  --------------------".
idtac " ".

idtac "#> ev100".
idtac "Possible points: 1".
check_type @ev100 ((IndProp.ev 100)).
idtac "Assumptions:".
Abort.
Print Assumptions ev100.
Goal True.
idtac " ".

idtac "-------------------  re_opt  --------------------".
idtac " ".

idtac "#> Manually graded: re_opt".
idtac "Possible points: 6".
print_manual_grade manual_grade_for_re_opt.
idtac " ".

idtac "-------------------  automatic_solvers  --------------------".
idtac " ".

idtac "#> plus_id_exercise_from_basics".
idtac "Possible points: 0.5".
check_type @plus_id_exercise_from_basics (
(forall n m o : nat, n = m -> m = o -> n + m = m + o)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_id_exercise_from_basics.
Goal True.
idtac " ".

idtac "#> add_assoc_from_induction".
idtac "Possible points: 0.5".
check_type @add_assoc_from_induction ((forall n m p : nat, n + (m + p) = n + m + p)).
idtac "Assumptions:".
Abort.
Print Assumptions add_assoc_from_induction.
Goal True.
idtac " ".

idtac "#> S_injective_from_tactics".
idtac "Possible points: 0.5".
check_type @S_injective_from_tactics ((forall n m : nat, S n = S m -> n = m)).
idtac "Assumptions:".
Abort.
Print Assumptions S_injective_from_tactics.
Goal True.
idtac " ".

idtac "#> or_distributes_over_and_from_logic".
idtac "Possible points: 0.5".
check_type @or_distributes_over_and_from_logic (
(forall P Q R : Prop, P \/ Q /\ R <-> (P \/ Q) /\ (P \/ R))).
idtac "Assumptions:".
Abort.
Print Assumptions or_distributes_over_and_from_logic.
Goal True.
idtac " ".

idtac "-------------------  re_opt_match_auto  --------------------".
idtac " ".

idtac "#> Manually graded: re_opt_match''".
idtac "Possible points: 3".
print_manual_grade manual_grade_for_re_opt_match''.
idtac " ".

idtac "-------------------  andb3_exchange  --------------------".
idtac " ".

idtac "#> andb3_exchange".
idtac "Possible points: 1".
check_type @andb3_exchange (
(forall b c d : Basics.bool,
 Basics.andb (Basics.andb b c) d = Basics.andb (Basics.andb b d) c)).
idtac "Assumptions:".
Abort.
Print Assumptions andb3_exchange.
Goal True.
idtac " ".

idtac "-------------------  andb_true_elim2  --------------------".
idtac " ".

idtac "#> andb_true_elim2'".
idtac "Possible points: 1.5".
check_type @andb_true_elim2' (
(forall b c : Basics.bool, Basics.andb b c = Basics.true -> c = Basics.true)).
idtac "Assumptions:".
Abort.
Print Assumptions andb_true_elim2'.
Goal True.
idtac " ".

idtac "#> andb3_exchange'".
idtac "Possible points: 0.5".
check_type @andb3_exchange' (
(forall b c d : Basics.bool,
 Basics.andb (Basics.andb b c) d = Basics.andb (Basics.andb b d) c)).
idtac "Assumptions:".
Abort.
Print Assumptions andb3_exchange'.
Goal True.
idtac " ".

idtac "-------------------  nand_intuition  --------------------".
idtac " ".

idtac "#> Manually graded: nand_intuition".
idtac "Advanced".
idtac "Possible points: 6".
print_manual_grade manual_grade_for_nand_intuition.
idtac " ".

idtac " ".

idtac "Max points - standard: 19".
idtac "Max points - advanced: 25".
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
idtac "---------- andb_eq_orb ---------".
Print Assumptions andb_eq_orb.
idtac "---------- add_assoc ---------".
Print Assumptions add_assoc.
idtac "---------- nonzeros_app ---------".
Print Assumptions nonzeros_app.
idtac "---------- add_assoc' ---------".
Print Assumptions add_assoc'.
idtac "---------- ev100 ---------".
Print Assumptions ev100.
idtac "---------- re_opt ---------".
idtac "MANUAL".
idtac "---------- plus_id_exercise_from_basics ---------".
Print Assumptions plus_id_exercise_from_basics.
idtac "---------- add_assoc_from_induction ---------".
Print Assumptions add_assoc_from_induction.
idtac "---------- S_injective_from_tactics ---------".
Print Assumptions S_injective_from_tactics.
idtac "---------- or_distributes_over_and_from_logic ---------".
Print Assumptions or_distributes_over_and_from_logic.
idtac "---------- re_opt_match'' ---------".
idtac "MANUAL".
idtac "---------- andb3_exchange ---------".
Print Assumptions andb3_exchange.
idtac "---------- andb_true_elim2' ---------".
Print Assumptions andb_true_elim2'.
idtac "---------- andb3_exchange' ---------".
Print Assumptions andb3_exchange'.
idtac "".
idtac "********** Advanced **********".
idtac "---------- nand_intuition ---------".
idtac "MANUAL".
Abort.

(* 2022-06-16 11:23 *)

(* 2022-06-16 11:23 *)
