           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |               December 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_law
imports CSP_F_law_SKIP      CSP_F_law_ref
        CSP_F_law_dist      CSP_F_law_alpha_par 
        CSP_F_law_step      CSP_F_law_rep_par   
        CSP_F_law_fix
        CSP_F_law_DIV       CSP_F_law_SKIP_DIV  
        CSP_F_law_step_ext  CSP_F_law_norm
        CSP_F_law_rep_ext_choice
        CSP_F_law_rep_interleaving
        CSP_F_law_Subst_procfun
        CSP_F_law_CHAOS
        CSP_F_law_RUN
        CSP_T.CSP_T_law
begin

(*********************************************************
            SKIP , DIV  and Internal choice
 *********************************************************)

(*** |~| ***)

lemma cspF_SKIP_DIV_Int_choice: 
  "[| P = SKIP | P = DIV ; Q = SKIP | Q = DIV |] ==>
   (P |~| Q) =F[M1,M2] (if (P = SKIP | Q = SKIP) then SKIP else DIV)"
apply (elim disjE)
apply (simp_all)
apply (rule cspF_rw_left)
apply (rule cspF_idem)
apply (rule cspF_reflex)
apply (rule cspF_rw_left)
apply (rule cspF_unit)
apply (rule cspF_reflex)
apply (rule cspF_rw_left)
apply (rule cspF_unit)
apply (rule cspF_reflex)
apply (rule cspF_rw_left)
apply (rule cspF_idem)
apply (rule cspF_reflex)
done

(*** !! ***)

lemma cspF_SKIP_DIV_Rep_int_choice_sum: 
  "[| ALL c: sumset C. (Qf c = SKIP | Qf c = DIV) |] ==>
   (!! c:C .. Qf c) =F[M1,M2] 
   (if (EX c: sumset C. Qf c = SKIP) then SKIP else DIV)"
apply (case_tac " sumset C={}")
apply (simp add: cspF_Rep_int_choice_empty)
apply (case_tac "ALL c: sumset C. Qf c = DIV")
 apply (simp)
 apply (rule cspF_rw_left)
 apply (rule cspF_Rep_int_choice_const)
 apply (simp)
 apply (force)
 apply (simp)

 apply (simp)
 apply (elim bexE)
 apply (frule_tac x="c" in bspec)
 apply (simp_all)
 apply (intro conjI impI)

  apply (rule cspF_rw_left)
  apply (subgoal_tac 
  "!! :C .. Qf =F[M1,M1]
   !! :({c:C. Qf c = SKIP}s Uns {c:C. Qf c ~= SKIP}s) .. Qf")
  apply (simp (no_asm))
  apply (rule cspF_decompo)
   apply (simp)
   apply (simp)

  apply (rule cspF_rw_left)
  apply (rule cspF_Rep_int_choice_union_Int)
  apply (simp)

  apply (rule cspF_rw_left)
  apply (rule cspF_decompo)
  apply (rule cspF_Rep_int_choice_const)
  apply (force)
  apply (rule ballI)
  apply (simp)
  apply (case_tac " sumset ({c:C. Qf c ~= SKIP}s) ={}")
   apply (rule cspF_Rep_int_choice_DIV)
   apply (simp)

   apply (rule cspF_rw_left)
   apply (rule cspF_Rep_int_choice_const)
   apply (simp_all)
   apply (intro allI impI)
   apply (subgoal_tac "Qf ca = DIV")
   apply (simp)
   apply (force)
   apply (simp)

  apply (rule cspF_rw_left)
  apply (rule cspF_unit)
  apply (simp)
done

lemma cspF_SKIP_DIV_Rep_int_choice_nat: 
  "[| ALL n:N. (Qf n = SKIP | Qf n = DIV) |] ==>
   (!nat n:N .. Qf n) =F[M1,M2] 
   (if (EX n:N. Qf n = SKIP) then SKIP else DIV)"
apply (unfold Rep_int_choice_ss_def)
apply (rule cspF_rw_left)
apply (rule cspF_SKIP_DIV_Rep_int_choice_sum)
apply (auto)
done

lemma cspF_SKIP_DIV_Rep_int_choice_set: 
  "[| ALL X:Xs. (Qf X = SKIP | Qf X = DIV) |] ==>
   (!set X:Xs .. Qf X) =F[M1,M2] 
   (if (EX X:Xs. Qf X = SKIP) then SKIP else DIV)"
apply (unfold Rep_int_choice_ss_def)
apply (rule cspF_rw_left)
apply (rule cspF_SKIP_DIV_Rep_int_choice_sum)
apply (auto)
done

lemmas cspF_SKIP_DIV_Rep_int_choice =
       cspF_SKIP_DIV_Rep_int_choice_sum
       cspF_SKIP_DIV_Rep_int_choice_nat
       cspF_SKIP_DIV_Rep_int_choice_set


(*********************************************************
                      guard to IF
 *********************************************************)

lemma cspF_Ext_choice_guard_IF :
    "g &: P [+] \<not> g &: Q =F (IF g THEN P ELSE Q)"
  apply (case_tac g)
  apply (auto)
  apply (rule cspF_rw_left, rule cspF_Ext_choice_cong)
  apply (rule cspF_IF, rule cspF_IF)
  apply (rule cspF_rw_right, rule cspF_IF)
  apply (rule cspF_rw_left, rule cspF_Ext_choice_unit)
  apply (rule cspF_reflex)
  apply (rule cspF_rw_left, rule cspF_Ext_choice_cong)
  apply (rule cspF_IF, rule cspF_IF)
  apply (rule cspF_rw_right, rule cspF_IF)
  apply (rule cspF_rw_left, rule cspF_Ext_choice_unit)
  apply (rule cspF_reflex)
  done

end
