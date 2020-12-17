           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                  April 2006               |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_law_norm
imports CSP_F_law_basic CSP_T.CSP_T_law_norm
begin

(*********************************************************
                       ?-div
 *********************************************************)

lemma cspF_input_DIV:
  "? :A -> Pf =F[M,M] (? :A -> Pf [+] DIV) |~| ? a:A -> DIV"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_input_DIV)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_failures in_traces)
 apply (elim disjE conjE exE)
 apply (simp_all)

(* <= *)
 apply (rule)
 apply (simp add: in_failures in_traces)
 apply (elim disjE conjE exE)
 apply (simp_all)
done

(*********************************************************
                    !!-!set-div
 *********************************************************)

lemma cspF_Rep_int_choice_sum_set_Ext_pre_choice_DIV:
  "!! c:C .. (!set X:(Xsf c) .. (? a:X -> DIV))
   =F[M1,M2] !set X:(Union {(Xsf c) |c. c : sumset C}) .. (? a:X -> DIV)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_set_Ext_pre_choice_DIV)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE bexE exE)

  apply (rule_tac x="Xsf c" in exI)
  apply (rule conjI)
  apply (force)

  apply (rule_tac x="Xa" in bexI)
  apply (simp)
  apply (simp)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE bexE)
 apply (simp)
  apply (rule_tac x="c" in bexI)
  apply (rule_tac x="Xa" in bexI)
  apply (simp_all)
done


lemma cspF_Rep_int_choice_set_set_Ext_pre_choice_DIV:
  "!set Y:Ys .. (!set X:(Xsf Y) .. (? a:X -> DIV))
   =F[M1,M2] !set X:(Union {(Xsf Y) |Y. Y : Ys}) .. (? a:X -> DIV)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_set_Ext_pre_choice_DIV)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE bexE exE)

  apply (rule_tac x="Xsf Xa" in exI)
  apply (rule conjI)
  apply (force)

  apply (rule_tac x="Xb" in bexI)
  apply (simp)
  apply (simp)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE bexE)
 apply (simp)
  apply (rule_tac x="Y" in bexI)
  apply (rule_tac x="Xa" in bexI)
  apply (simp_all)
done

lemma cspF_Rep_int_choice_nat_set_Ext_pre_choice_DIV:
  "!nat n:N .. (!set X:(Xsf n) .. (? a:X -> DIV))
   =F[M1,M2] !set X:(Union {(Xsf n) |n. n : N}) .. (? a:X -> DIV)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_Rep_int_choice_set_Ext_pre_choice_DIV)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE bexE exE)

  apply (rule_tac x="Xsf n" in exI)
  apply (rule conjI)
  apply (force)

  apply (rule_tac x="Xa" in bexI)
  apply (simp)
  apply (simp)

(* => *)
 apply (rule)
 apply (simp add: in_failures)
 apply (elim disjE conjE exE bexE)
 apply (simp)
  apply (rule_tac x="n" in bexI)
  apply (rule_tac x="Xa" in bexI)
  apply (simp_all)
done

lemmas cspF_Rep_int_choice_set_Ext_pre_choice_DIV =
       cspF_Rep_int_choice_sum_set_Ext_pre_choice_DIV
       cspF_Rep_int_choice_set_set_Ext_pre_choice_DIV
       cspF_Rep_int_choice_nat_set_Ext_pre_choice_DIV

(*********************************************************
                      ?-!set-<=
 *********************************************************)

lemma cspF_input_Rep_int_choice_set_subset:
  "[| Xs <= Ys ; ALL Y:Ys. EX X:Xs. X <= Y & Y <= A |] ==>
   ((? :A -> Pf) [+] Q) 
   |~| (!set X : Xs .. ? a:X -> DIV)
   =F[M,M]
   ((? :A -> Pf) [+] Q)
   |~| (!set Y : Ys .. ? a:Y -> DIV)"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_input_Rep_int_choice_set_subset)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_failures)
 apply (elim disjE conjE bexE exE)
 apply (simp_all)
 apply (rule disjI2)
 apply (rule disjI2)
 apply (rule_tac x="Xa" in bexI)
 apply (simp)
 apply (force)

(* <= *)
 apply (rule, simp add: in_failures)
 apply (elim disjE conjE bexE exE)
 apply (simp_all)
 apply (rule disjI2)
 apply (rule disjI2)
 apply (drule_tac x="Xa" in bspec, simp)
 apply (elim conjE bexE)
 apply (rule_tac x="Xb" in bexI)
 apply (blast)
 apply (simp)
done

lemmas cspF_norm = cspF_input_DIV 
                   cspF_Rep_int_choice_set_Ext_pre_choice_DIV
                   cspF_input_Rep_int_choice_set_subset

end
