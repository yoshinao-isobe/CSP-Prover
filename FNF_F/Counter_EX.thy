           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Counter_EX
imports FNF_F
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*  The following simplification rules are deleted in this theory file *)
(*       P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))        *)
(* Isabelle 2017: split_if --> if_split *)

declare if_split  [split del]

(*****************************************************************

         1.
         2. 
         3. 

 *****************************************************************)

(* there is a process which is not contained in fsfF_proc *)

typedecl nopn
datatype event = event_a

primrec
  PAf   :: "nat => (nopn,event) proc"
where
  "PAf 0       = DIV"
 |"PAf (Suc n) = event_a -> (PAf n)"

definition
  PA    :: "(nopn,event) proc"
  where
  PA_def :
    "PA == !nat n .. PAf n"

lemma PA_eqF:
  "PA =F ((? a:{event_a} -> (if a = event_a then PA else DIV)) [+] DIV) |~| 
              (!set Y:{{event_a}} .. (? a:Y -> DIV))"
apply (simp add: PA_def)
apply (rule cspF_rw_left)
apply (subgoal_tac 
  "!nat :UNIV .. PAf =F !nat n:({0} Un {m. EX n. m = Suc n}) .. PAf n")
apply (assumption)
 apply (rule cspF_decompo)
 apply (rule equalityI)
 apply (rule)
 apply (simp add: nat_zero_or_Suc)
 apply (simp)
 apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_Rep_int_choice_union_Int)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_Rep_int_choice_singleton)
apply (rule cspF_reflex)

apply (rule cspF_rw_left)
apply (simp)
apply (rule cspF_unit)

apply (rule cspF_rw_left)
apply (subgoal_tac 
  "!nat :{m. EX n. m = Suc n} .. PAf =F !nat n .. PAf (Suc n)")
apply (simp)
 apply (rule cspF_Rep_int_choice_decompo_ALL_EX_eq)
 apply (simp)
 apply (intro allI impI)
 apply (elim exE)
 apply (simp)
 apply (rule_tac x="n" in exI)
 apply (simp)

 apply (rule ballI)
 apply (simp)
 apply (rule_tac x="Suc n2" in exI)
 apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_Act_prefix_Dist[THEN cspF_sym])
apply (simp)
apply (fold PA_def)

apply (rule cspF_rw_right)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (subgoal_tac 
  "? a:{event_a} -> (if a = event_a then PA else DIV) =F ? a:{event_a} -> PA")
apply (simp)
 apply (rule cspF_decompo)
 apply (simp)
 apply (simp)
apply (rule cspF_reflex)
apply (rule cspF_Rep_int_choice_singleton)
apply (rule cspF_rw_right)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (rule cspF_step[THEN cspF_sym])
apply (rule cspF_reflex)
apply (rule cspF_reflex)

apply (rule cspF_rw_right)
apply (rule cspF_decompo)
apply (rule cspF_reflex)
apply (rule cspF_step[THEN cspF_sym])

apply (rule cspF_rw_left)
apply (rule cspF_step)
apply (rule cspF_rw_left)
apply (rule cspF_input_DIV)

apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (rule cspF_rw_right)
apply (rule cspF_step)
apply (rule cspF_reflex)
apply (rule cspF_reflex)
apply (rule cspF_rw_right)
apply (rule cspF_step)
apply (rule cspF_reflex)
done

lemma NPA_fnfF_proc: 
  "NPA : fnfF_proc ==> 
   ((? a:{event_a} -> (if a = event_a then NPA else DIV)) [+] DIV) |~| 
              (!set Y:{{event_a}} .. (? a:Y -> DIV)) : fnfF_proc"
apply (rule fnfF_proc.intros)
apply (simp_all)
apply (simp split: if_split)
apply (simp add: fnfF_set_condition_def)
apply (auto)
done

lemma PA_not_fnfF_proc_lm:
  "[| PA =F NPA; NPA : fnfF_proc |]
   ==> PA =F ((? a:{event_a} -> (if a = event_a then NPA else DIV)) [+] DIV) |~| 
        (!set Y:{{event_a}} .. (? a:Y -> DIV))"
apply (rule cspF_rw_left)
apply (rule PA_eqF)
apply (rule cspF_decompo, simp?)+
apply (simp split: if_split)
apply (simp)
apply (rule cspF_decompo, simp?)+
apply (simp)
done

(* main *)

lemma PA_not_fnfF_proc: "PA =F NPA ==> NPA ~: fnfF_proc"
apply (case_tac "NPA ~: fnfF_proc", simp)
apply (simp)
apply (insert PA_not_fnfF_proc_lm[of NPA])
apply (simp)
apply (subgoal_tac 
 "NPA =F ? a:{event_a} -> (if a = event_a then NPA else DIV) [+] DIV 
        |~| !set Y:{{event_a}} .. ? a:Y -> DIV")
apply (subgoal_tac 
 "NPA = ? a:{event_a} -> (if a = event_a then NPA else DIV) [+] DIV 
        |~| !set Y:{{event_a}} .. ? a:Y -> DIV")
apply (simp)
defer
apply (rule fnfF_syntactical_equality_only_if)
apply (simp_all)
apply (simp add: NPA_fnfF_proc)
apply (erule cspF_symE)
apply (rule cspF_rw_left)
apply (simp)
apply (simp)
apply (rotate_tac -1)
apply (erule contrapos_pp)
apply (rule fnfF_proc.induct[of NPA])
apply (simp)
apply (simp)
apply (case_tac "A ~= {event_a}", simp)
apply (simp)
apply (case_tac "Q ~= DIV", simp)
apply (simp)

apply (case_tac "Ys ~= {{event_a}}")
apply (rule disjI2)
apply (simp add: Rep_int_choice_ss_def)
apply (simp)

apply (simp add: fun_eq_iff)
apply (rule_tac x="event_a" in exI)
apply (simp)
apply (subgoal_tac
  "(%a. (if a = event_a then Pf event_a else DIV)) = Pf")
apply (drule_tac x="event_a" in spec)
apply (simp)
(*
apply (fold fun_eq_iff)
apply (simp)
*)
apply (simp add: fun_eq_iff)
apply (rule allI)
apply (drule_tac x="x" in spec)
apply (simp split: if_split)
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
