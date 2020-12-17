           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law
imports CSP_T_law_SKIP     CSP_T_law_ref
        CSP_T_law_dist     CSP_T_law_alpha_par
        CSP_T_law_step     CSP_T_law_rep_par
        CSP_T_law_fix
        CSP_T_law_DIV      CSP_T_law_SKIP_DIV
        CSP_T_law_step_ext CSP_T_law_norm
begin

(*-----------------------------------------------------------*
 |                                                           |
 |                 Ext_choice_Int_choice                     |
 |                                                           |
 |  These rules show the difference between models T and F.  |
 |                                                           |
 *-----------------------------------------------------------*)

lemma cspT_Ext_choice_Int_choice:
  "P1 [+] P2 =T[M,M] P1 |~| P2"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces)+
done

lemma cspT_Ext_pre_choice_Rep_int_choice:
  "? :X -> Pf =T[M,M] ! x:X .. x -> Pf x"
apply (simp add: cspT_semantics)
apply (rule order_antisym)
apply (rule, simp add: in_traces)
apply (force)
apply (rule, simp add: in_traces)
apply (force)
done

lemmas cspT_Ext_Int = cspT_Ext_choice_Int_choice
                      cspT_Ext_pre_choice_Rep_int_choice

(*********************************************************
            SKIP , DIV  and Internal choice
 *********************************************************)

(*** |~| ***)

lemma cspT_SKIP_DIV_Int_choice: 
  "[| P = SKIP | P = DIV ; Q = SKIP | Q = DIV |] ==>
   (P |~| Q) =T[M1,M2] (if (P = SKIP | Q = SKIP) then SKIP else DIV)"
apply (elim disjE)
apply (simp_all)
apply (rule cspT_rw_left)
apply (rule cspT_idem)
apply (rule cspT_reflex)
apply (rule cspT_rw_left)
apply (rule cspT_unit)
apply (rule cspT_reflex)
apply (rule cspT_rw_left)
apply (rule cspT_unit)
apply (rule cspT_reflex)
apply (rule cspT_rw_left)
apply (rule cspT_idem)
apply (rule cspT_reflex)
done

(*** !! ***)

lemma cspT_SKIP_DIV_Rep_int_choice_sum: 
  "[| ALL c: sumset C. (Qf c = SKIP | Qf c = DIV) |] ==>
   (!! c:C .. Qf c) =T[M1,M2] 
   (if (EX c: sumset C. Qf c = SKIP) then SKIP else DIV)"
apply (case_tac " sumset C={}")
apply (simp add: cspT_Rep_int_choice_empty)
apply (case_tac "ALL c: sumset C. Qf c = DIV")
 apply (simp)
 apply (rule cspT_rw_left)
 apply (rule cspT_Rep_int_choice_const)
 apply (simp)
 apply (force)
 apply (simp)

 apply (simp)
 apply (elim bexE)
 apply (frule_tac x="c" in bspec)
 apply (simp_all)
 apply (intro conjI impI)

  apply (rule cspT_rw_left)
  apply (subgoal_tac 
  "!! :C .. Qf =T[M1,M1]
   !! :({c:C. Qf c = SKIP}s Uns {c:C. Qf c ~= SKIP}s) .. Qf")
  apply (simp (no_asm))
  apply (rule cspT_decompo)
   apply (simp)
   apply (simp)

  apply (rule cspT_rw_left)
  apply (rule cspT_Rep_int_choice_union_Int)
  apply (simp)

  apply (rule cspT_rw_left)
  apply (rule cspT_decompo)
  apply (rule cspT_Rep_int_choice_const)
  apply (force)
  apply (rule ballI)
  apply (simp)
  apply (case_tac " sumset ({c:C. Qf c ~= SKIP}s) ={}")
   apply (rule cspT_Rep_int_choice_DIV)
   apply (simp)

   apply (rule cspT_rw_left)
   apply (rule cspT_Rep_int_choice_const)
   apply (simp_all)
   apply (intro allI impI)
   apply (subgoal_tac "Qf ca = DIV")
   apply (simp)
   apply (force)
   apply (simp)

  apply (rule cspT_rw_left)
  apply (rule cspT_unit)
  apply (simp)
done

lemma cspT_SKIP_DIV_Rep_int_choice_nat: 
  "[| ALL n:N. (Qf n = SKIP | Qf n = DIV) |] ==>
   (!nat n:N .. Qf n) =T[M1,M2] 
   (if (EX n:N. Qf n = SKIP) then SKIP else DIV)"
apply (unfold Rep_int_choice_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_SKIP_DIV_Rep_int_choice_sum)
apply (auto)
done

lemma cspT_SKIP_DIV_Rep_int_choice_set: 
  "[| ALL X:Xs. (Qf X = SKIP | Qf X = DIV) |] ==>
   (!set X:Xs .. Qf X) =T[M1,M2] 
   (if (EX X:Xs. Qf X = SKIP) then SKIP else DIV)"
apply (unfold Rep_int_choice_ss_def)
apply (rule cspT_rw_left)
apply (rule cspT_SKIP_DIV_Rep_int_choice_sum)
apply (auto)
done

lemmas cspT_SKIP_DIV_Rep_int_choice =
       cspT_SKIP_DIV_Rep_int_choice_sum
       cspT_SKIP_DIV_Rep_int_choice_nat
       cspT_SKIP_DIV_Rep_int_choice_set

end
