           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                  April 2006               |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law_norm 
imports CSP_T_law_basic
begin

(*********************************************************
                       ?-div
 *********************************************************)

lemma cspT_input_DIV:
  "? :A -> Pf =T[M,M] (? :A -> Pf [+] DIV) |~| ? a:A -> DIV"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule)
 apply (simp add: in_traces)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim disjE conjE exE)
 apply (simp_all)
done

(*********************************************************
                    !set-!set-div
 *********************************************************)

lemma cspT_Rep_int_choice_sum_set_Ext_pre_choice_DIV:
  "!! c:C .. (!set X:(Xsf c) .. (? a:X -> DIV))
   =T[M1,M2] !set X:(Union {(Xsf c) |c. c : sumset C}) .. (? a:X -> DIV)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)
 apply (rule_tac x="Xsf c" in exI)
 apply (force)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)
  apply (rule_tac x="c" in bexI)
  apply (force)
  apply (simp)
done

lemma cspT_Rep_int_choice_set_set_Ext_pre_choice_DIV:
  "!set Y:Ys .. (!set X:(Xsf Y) .. (? a:X -> DIV))
   =T[M1,M2] !set X:(Union {(Xsf Y) |Y. Y : Ys}) .. (? a:X -> DIV)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)
 apply (rule_tac x="Xsf X" in exI)
 apply (force)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)
  apply (rule_tac x="Y" in bexI)
  apply (force)
  apply (simp)
done

lemma cspT_Rep_int_choice_nat_set_Ext_pre_choice_DIV:
  "!nat n:N .. (!set X:(Xsf n) .. (? a:X -> DIV))
   =T[M1,M2] !set X:(Union {(Xsf n) |n. n : N}) .. (? a:X -> DIV)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)
 apply (rule_tac x="Xsf n" in exI)
 apply (force)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE bexE disjE)
 apply (simp_all)
  apply (rule_tac x="n" in bexI)
  apply (force)
  apply (simp)
done

lemmas cspT_Rep_int_choice_set_Ext_pre_choice_DIV =
       cspT_Rep_int_choice_sum_set_Ext_pre_choice_DIV
       cspT_Rep_int_choice_set_set_Ext_pre_choice_DIV
       cspT_Rep_int_choice_nat_set_Ext_pre_choice_DIV

(*********************************************************
                      ?-!set-<=
 *********************************************************)

lemma cspT_input_Rep_int_choice_set_subset:
  "[| Xs <= Ys ; ALL Y:Ys. EX X:Xs. X <= Y & Y <= A |] ==>
   ((? :A -> Pf) [+] Q) 
   |~| (!set X : Xs .. ? a:X -> DIV)
   =T[M,M]
   ((? :A -> Pf) [+] Q)
   |~| (!set Y : Ys .. ? a:Y -> DIV)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* => *)
 apply (rule, simp add: in_traces)
 apply (elim disjE conjE exE bexE)
 apply (simp_all)
 apply (force)

(* <= *)
 apply (rule, simp add: in_traces)
 apply (elim disjE conjE exE bexE)
 apply (simp_all)
 apply (drule_tac x="X" in bspec, simp)
 apply (force)
done

lemmas cspT_norm = cspT_input_DIV 
                   cspT_Rep_int_choice_set_Ext_pre_choice_DIV
                   cspT_input_Rep_int_choice_set_subset

end
