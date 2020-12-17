           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory DIV_Example
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

fun
  Count :: "nat => (nat, nat) proc"
  where
  "Count  n = (n -> $(Suc n)) -- {n}"

declare Count.simps [simp del]

(*
defs (overloaded)
  Set_Count_PNfun[simp]: "PNfun == Count" 
*)

overloading Set_Count == 
  "PNfun :: (nat, nat) pnfun"
begin
  definition "PNfun == Count"
end
  
declare Set_Count_def [simp]

(*
defs
  FPmode_def[simp] : "FPmode == CPOmode"
*)

overloading FPmode == 
  "FPmode :: fpmode"
begin
  definition "FPmode == CPOmode"
end

declare FPmode_def [simp]

lemma ALL_Count_DIV:
  "ALL m. ((Count <<<)^^n) (%y. DIV) (m) =F DIV"
apply (induct_tac n)
apply (simp)
apply (simp)
apply (rule allI)
apply (rule cspF_rw_left)
apply (subgoal_tac 
  "Count <<< ((Count <<< ^^ n) (%y. DIV)) m =F Count <<< (%y. DIV) m")
apply (simp)
 apply (simp add: Subst_procfun_prod_def)
 apply (simp add: Count.simps)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_decompo)
 apply (simp)
 apply (drule_tac x="Suc m" in spec)
 apply (rule cspF_rw_left)
 apply (simp)
 apply (simp)

apply (simp add: Subst_procfun_prod_def)
apply (simp add: Count.simps)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_step)

apply (rule cspF_rw_left)
apply (rule cspF_step)
apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_IF_False)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (rule cspF_step[THEN cspF_sym])
apply (rule cspF_reflex)
apply (rule cspF_Rep_int_choice_singleton)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_idem)
apply (rule cspF_reflex)

apply (rule cspF_rw_left)
apply (rule cspF_unit)
apply (rule cspF_DIV_Hiding_Id)
done

lemma Count_DIV:
  "(Count <<< ^^n) (%y. DIV) (m) =F DIV"
apply (simp add: ALL_Count_DIV)
done

lemma CountFIX_DIV:
  "(FIX Count) 0 =F !nat n .. DIV"
apply (simp add: FIX_def)
apply (simp add: FIXn_def)

apply (rule cspF_decompo)
apply (simp)
apply (simp add: Count_DIV)
done

(*** full normalising ***)

lemma CountFIX_DIV_Xnorm:
  "(FIX Count) 0 =F !nat n .. NDIV"
apply (rule cspF_rw_left)
apply (rule CountFIX_DIV)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_NDIV_eqF)
done

(*** in extended full normal form ***)

lemma DIV_Xnorm_in:
  "!nat n .. NDIV : XfnfF_proc"
apply (simp add: XfnfF_proc_def)
apply (rule_tac x="(%n. NDIV)" in exI)
apply (simp)
apply (rule allI)
apply (rule cspF_rw_right)
apply (rule cspF_Dist)

apply (rule cspF_rw_right)
apply (rule cspF_Rep_int_choice_unit)
apply (simp)

apply (rule cspF_rw_right)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_NDIV_eqF[THEN cspF_sym])

apply (rule cspF_rw_right)
apply (rule cspF_DIV_Depth_rest)
apply (rule cspF_NDIV_eqF[THEN cspF_sym])
done

(*** unwinding test ***)

lemma Count_nat_eq:
  "$n =F (FIX Count) n"
apply (rule cspF_rw_left)
apply (rule cspF_FIX)
apply (rule disjI1)
apply (simp)+
done

lemma CountFIX_DIV_unwinding_test:
  "$n =F (n -> $(Suc n)) -- {n}"
apply (rule cspF_rw_left)
apply (rule cspF_unwind_cpo)
apply (simp add: Count.simps)+
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
