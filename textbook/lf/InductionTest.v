Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import Induction.

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

From LF Require Import Induction.
Import Check.

Goal True.

idtac "-------------------  basic_induction  --------------------".
idtac " ".

idtac "#> mul_0_r".
idtac "Possible points: 0.5".
check_type @mul_0_r ((forall n : nat, n * 0 = 0)).
idtac "Assumptions:".
Abort.
Print Assumptions mul_0_r.
Goal True.
idtac " ".

idtac "#> plus_n_Sm".
idtac "Possible points: 0.5".
check_type @plus_n_Sm ((forall n m : nat, S (n + m) = n + S m)).
idtac "Assumptions:".
Abort.
Print Assumptions plus_n_Sm.
Goal True.
idtac " ".

idtac "#> add_comm".
idtac "Possible points: 0.5".
check_type @add_comm ((forall n m : nat, n + m = m + n)).
idtac "Assumptions:".
Abort.
Print Assumptions add_comm.
Goal True.
idtac " ".

idtac "#> add_assoc".
idtac "Possible points: 0.5".
check_type @add_assoc ((forall n m p : nat, n + (m + p) = n + m + p)).
idtac "Assumptions:".
Abort.
Print Assumptions add_assoc.
Goal True.
idtac " ".

idtac "-------------------  double_plus  --------------------".
idtac " ".

idtac "#> double_plus".
idtac "Possible points: 2".
check_type @double_plus ((forall n : nat, double n = n + n)).
idtac "Assumptions:".
Abort.
Print Assumptions double_plus.
Goal True.
idtac " ".

idtac "-------------------  eqb_refl  --------------------".
idtac " ".

idtac "#> eqb_refl".
idtac "Possible points: 2".
check_type @eqb_refl ((forall n : nat, (n =? n) = true)).
idtac "Assumptions:".
Abort.
Print Assumptions eqb_refl.
Goal True.
idtac " ".

idtac "-------------------  add_comm_informal  --------------------".
idtac " ".

idtac "#> Manually graded: add_comm_informal".
idtac "Advanced".
idtac "Possible points: 2".
print_manual_grade manual_grade_for_add_comm_informal.
idtac " ".

idtac "-------------------  mul_comm  --------------------".
idtac " ".

idtac "#> add_shuffle3".
idtac "Possible points: 1".
check_type @add_shuffle3 ((forall n m p : nat, n + (m + p) = m + (n + p))).
idtac "Assumptions:".
Abort.
Print Assumptions add_shuffle3.
Goal True.
idtac " ".

idtac "#> mul_comm".
idtac "Possible points: 2".
check_type @mul_comm ((forall m n : nat, m * n = n * m)).
idtac "Assumptions:".
Abort.
Print Assumptions mul_comm.
Goal True.
idtac " ".

idtac "-------------------  binary_commute  --------------------".
idtac " ".

idtac "#> bin_to_nat_pres_incr".
idtac "Possible points: 3".
check_type @bin_to_nat_pres_incr (
(forall b : bin, bin_to_nat (incr b) = 1 + bin_to_nat b)).
idtac "Assumptions:".
Abort.
Print Assumptions bin_to_nat_pres_incr.
Goal True.
idtac " ".

idtac "-------------------  nat_bin_nat  --------------------".
idtac " ".

idtac "#> nat_bin_nat".
idtac "Possible points: 3".
check_type @nat_bin_nat ((forall n : nat, bin_to_nat (nat_to_bin n) = n)).
idtac "Assumptions:".
Abort.
Print Assumptions nat_bin_nat.
Goal True.
idtac " ".

idtac "-------------------  double_bin  --------------------".
idtac " ".

idtac "#> double_incr".
idtac "Advanced".
idtac "Possible points: 0.5".
check_type @double_incr ((forall n : nat, double (S n) = S (S (double n)))).
idtac "Assumptions:".
Abort.
Print Assumptions double_incr.
Goal True.
idtac " ".

idtac "#> double_bin_zero".
idtac "Advanced".
idtac "Possible points: 0.5".
check_type @double_bin_zero ((double_bin Z = Z)).
idtac "Assumptions:".
Abort.
Print Assumptions double_bin_zero.
Goal True.
idtac " ".

idtac "#> double_incr_bin".
idtac "Advanced".
idtac "Possible points: 1".
check_type @double_incr_bin (
(forall b : bin, double_bin (incr b) = incr (incr (double_bin b)))).
idtac "Assumptions:".
Abort.
Print Assumptions double_incr_bin.
Goal True.
idtac " ".

idtac "-------------------  bin_nat_bin  --------------------".
idtac " ".

idtac "#> bin_nat_bin".
idtac "Advanced".
idtac "Possible points: 6".
check_type @bin_nat_bin ((forall b : bin, nat_to_bin (bin_to_nat b) = normalize b)).
idtac "Assumptions:".
Abort.
Print Assumptions bin_nat_bin.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
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
idtac "---------- mul_0_r ---------".
Print Assumptions mul_0_r.
idtac "---------- plus_n_Sm ---------".
Print Assumptions plus_n_Sm.
idtac "---------- add_comm ---------".
Print Assumptions add_comm.
idtac "---------- add_assoc ---------".
Print Assumptions add_assoc.
idtac "---------- double_plus ---------".
Print Assumptions double_plus.
idtac "---------- eqb_refl ---------".
Print Assumptions eqb_refl.
idtac "---------- add_shuffle3 ---------".
Print Assumptions add_shuffle3.
idtac "---------- mul_comm ---------".
Print Assumptions mul_comm.
idtac "---------- bin_to_nat_pres_incr ---------".
Print Assumptions bin_to_nat_pres_incr.
idtac "---------- nat_bin_nat ---------".
Print Assumptions nat_bin_nat.
idtac "".
idtac "********** Advanced **********".
idtac "---------- add_comm_informal ---------".
idtac "MANUAL".
idtac "---------- double_incr ---------".
Print Assumptions double_incr.
idtac "---------- double_bin_zero ---------".
Print Assumptions double_bin_zero.
idtac "---------- double_incr_bin ---------".
Print Assumptions double_incr_bin.
idtac "---------- bin_nat_bin ---------".
Print Assumptions bin_nat_bin.
Abort.

(* 2022-06-16 11:18 *)

(* 2022-06-16 11:18 *)
