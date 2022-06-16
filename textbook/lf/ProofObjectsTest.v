Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF Require Import ProofObjects.

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

From LF Require Import ProofObjects.
Import Check.

Goal True.

idtac "-------------------  eight_is_even  --------------------".
idtac " ".

idtac "#> ev_8".
idtac "Possible points: 1".
check_type @ev_8 ((ev 8)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_8.
Goal True.
idtac " ".

idtac "#> ev_8'".
idtac "Possible points: 1".
check_type @ev_8' ((ev 8)).
idtac "Assumptions:".
Abort.
Print Assumptions ev_8'.
Goal True.
idtac " ".

idtac "-------------------  conj_fact  --------------------".
idtac " ".

idtac "#> Props.conj_fact".
idtac "Possible points: 2".
check_type @Props.conj_fact ((forall P Q R : Prop, P /\ Q -> Q /\ R -> P /\ R)).
idtac "Assumptions:".
Abort.
Print Assumptions Props.conj_fact.
Goal True.
idtac " ".

idtac "-------------------  or_commut'  --------------------".
idtac " ".

idtac "#> Props.or_commut'".
idtac "Possible points: 2".
check_type @Props.or_commut' ((forall P Q : Prop, P \/ Q -> Q \/ P)).
idtac "Assumptions:".
Abort.
Print Assumptions Props.or_commut'.
Goal True.
idtac " ".

idtac "-------------------  ex_ev_Sn  --------------------".
idtac " ".

idtac "#> Props.ex_ev_Sn".
idtac "Possible points: 2".
check_type @Props.ex_ev_Sn ((exists n : nat, ev (S n))).
idtac "Assumptions:".
Abort.
Print Assumptions Props.ex_ev_Sn.
Goal True.
idtac " ".

idtac "-------------------  p_implies_true  --------------------".
idtac " ".

idtac "#> Props.p_implies_true".
idtac "Possible points: 1".
check_type @Props.p_implies_true ((forall P : Type, P -> Props.True)).
idtac "Assumptions:".
Abort.
Print Assumptions Props.p_implies_true.
Goal True.
idtac " ".

idtac "-------------------  ex_falso_quodlibet'  --------------------".
idtac " ".

idtac "#> Props.ex_falso_quodlibet'".
idtac "Possible points: 1".
check_type @Props.ex_falso_quodlibet' ((forall P : Type, Props.False -> P)).
idtac "Assumptions:".
Abort.
Print Assumptions Props.ex_falso_quodlibet'.
Goal True.
idtac " ".

idtac "-------------------  eq_cons  --------------------".
idtac " ".

idtac "#> EqualityPlayground.eq_cons".
idtac "Possible points: 2".
check_type @EqualityPlayground.eq_cons (
(forall (X : Type) (h1 h2 : X) (t1 t2 : list X),
 @EqualityPlayground.eq X h1 h2 ->
 @EqualityPlayground.eq (list X) t1 t2 ->
 @EqualityPlayground.eq (list X) (h1 :: t1) (h2 :: t2))).
idtac "Assumptions:".
Abort.
Print Assumptions EqualityPlayground.eq_cons.
Goal True.
idtac " ".

idtac "-------------------  equality__leibniz_equality  --------------------".
idtac " ".

idtac "#> EqualityPlayground.equality__leibniz_equality".
idtac "Possible points: 2".
check_type @EqualityPlayground.equality__leibniz_equality (
(forall (X : Type) (x y : X),
 @EqualityPlayground.eq X x y -> forall P : X -> Prop, P x -> P y)).
idtac "Assumptions:".
Abort.
Print Assumptions EqualityPlayground.equality__leibniz_equality.
Goal True.
idtac " ".

idtac "-------------------  equality__leibniz_equality_term  --------------------".
idtac " ".

idtac "#> EqualityPlayground.equality__leibniz_equality_term".
idtac "Possible points: 2".
check_type @EqualityPlayground.equality__leibniz_equality_term (
(forall (X : Type) (x y : X),
 @EqualityPlayground.eq X x y -> forall P : X -> Prop, P x -> P y)).
idtac "Assumptions:".
Abort.
Print Assumptions EqualityPlayground.equality__leibniz_equality_term.
Goal True.
idtac " ".

idtac "-------------------  and_assoc  --------------------".
idtac " ".

idtac "#> and_assoc".
idtac "Possible points: 2".
check_type @and_assoc ((forall P Q R : Prop, P /\ Q /\ R -> (P /\ Q) /\ R)).
idtac "Assumptions:".
Abort.
Print Assumptions and_assoc.
Goal True.
idtac " ".

idtac "-------------------  or_distributes_over_and  --------------------".
idtac " ".

idtac "#> or_distributes_over_and".
idtac "Possible points: 3".
check_type @or_distributes_over_and (
(forall P Q R : Prop, P \/ Q /\ R <-> (P \/ Q) /\ (P \/ R))).
idtac "Assumptions:".
Abort.
Print Assumptions or_distributes_over_and.
Goal True.
idtac " ".

idtac "-------------------  negations  --------------------".
idtac " ".

idtac "#> double_neg".
idtac "Possible points: 1".
check_type @double_neg ((forall P : Prop, P -> ~ ~ P)).
idtac "Assumptions:".
Abort.
Print Assumptions double_neg.
Goal True.
idtac " ".

idtac "#> contradiction_implies_anything".
idtac "Possible points: 1".
check_type @contradiction_implies_anything ((forall P Q : Prop, P /\ ~ P -> Q)).
idtac "Assumptions:".
Abort.
Print Assumptions contradiction_implies_anything.
Goal True.
idtac " ".

idtac "#> de_morgan_not_or".
idtac "Possible points: 1".
check_type @de_morgan_not_or ((forall P Q : Prop, ~ (P \/ Q) -> ~ P /\ ~ Q)).
idtac "Assumptions:".
Abort.
Print Assumptions de_morgan_not_or.
Goal True.
idtac " ".

idtac "-------------------  currying  --------------------".
idtac " ".

idtac "#> curry".
idtac "Possible points: 1".
check_type @curry ((forall P Q R : Prop, (P /\ Q -> R) -> P -> Q -> R)).
idtac "Assumptions:".
Abort.
Print Assumptions curry.
Goal True.
idtac " ".

idtac "#> uncurry".
idtac "Possible points: 1".
check_type @uncurry ((forall P Q R : Prop, (P -> Q -> R) -> P /\ Q -> R)).
idtac "Assumptions:".
Abort.
Print Assumptions uncurry.
Goal True.
idtac " ".

idtac "-------------------  pe_implies_or_eq  --------------------".
idtac " ".

idtac "#> pe_implies_or_eq".
idtac "Advanced".
idtac "Possible points: 1".
check_type @pe_implies_or_eq (
(propositional_extensionality -> forall P Q : Prop, (P \/ Q) = (Q \/ P))).
idtac "Assumptions:".
Abort.
Print Assumptions pe_implies_or_eq.
Goal True.
idtac " ".

idtac "-------------------  pe_implies_true_eq  --------------------".
idtac " ".

idtac "#> pe_implies_true_eq".
idtac "Advanced".
idtac "Possible points: 1".
check_type @pe_implies_true_eq (
(propositional_extensionality -> forall P : Prop, P -> True = P)).
idtac "Assumptions:".
Abort.
Print Assumptions pe_implies_true_eq.
Goal True.
idtac " ".

idtac "-------------------  pe_implies_pi  --------------------".
idtac " ".

idtac "#> pe_implies_pi".
idtac "Advanced".
idtac "Possible points: 3".
check_type @pe_implies_pi ((propositional_extensionality -> proof_irrelevance)).
idtac "Assumptions:".
Abort.
Print Assumptions pe_implies_pi.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 26".
idtac "Max points - advanced: 31".
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
idtac "---------- ev_8 ---------".
Print Assumptions ev_8.
idtac "---------- ev_8' ---------".
Print Assumptions ev_8'.
idtac "---------- Props.conj_fact ---------".
Print Assumptions Props.conj_fact.
idtac "---------- Props.or_commut' ---------".
Print Assumptions Props.or_commut'.
idtac "---------- Props.ex_ev_Sn ---------".
Print Assumptions Props.ex_ev_Sn.
idtac "---------- Props.p_implies_true ---------".
Print Assumptions Props.p_implies_true.
idtac "---------- Props.ex_falso_quodlibet' ---------".
Print Assumptions Props.ex_falso_quodlibet'.
idtac "---------- EqualityPlayground.eq_cons ---------".
Print Assumptions EqualityPlayground.eq_cons.
idtac "---------- EqualityPlayground.equality__leibniz_equality ---------".
Print Assumptions EqualityPlayground.equality__leibniz_equality.
idtac "---------- EqualityPlayground.equality__leibniz_equality_term ---------".
Print Assumptions EqualityPlayground.equality__leibniz_equality_term.
idtac "---------- and_assoc ---------".
Print Assumptions and_assoc.
idtac "---------- or_distributes_over_and ---------".
Print Assumptions or_distributes_over_and.
idtac "---------- double_neg ---------".
Print Assumptions double_neg.
idtac "---------- contradiction_implies_anything ---------".
Print Assumptions contradiction_implies_anything.
idtac "---------- de_morgan_not_or ---------".
Print Assumptions de_morgan_not_or.
idtac "---------- curry ---------".
Print Assumptions curry.
idtac "---------- uncurry ---------".
Print Assumptions uncurry.
idtac "".
idtac "********** Advanced **********".
idtac "---------- pe_implies_or_eq ---------".
Print Assumptions pe_implies_or_eq.
idtac "---------- pe_implies_true_eq ---------".
Print Assumptions pe_implies_true_eq.
idtac "---------- pe_implies_pi ---------".
Print Assumptions pe_implies_pi.
Abort.

(* 2022-06-16 11:18 *)

(* 2022-06-16 11:18 *)
