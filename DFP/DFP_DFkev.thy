           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_DFkev
imports DFP_DFnonTick
begin


datatype DFkevPN = DFkev nat nat


fun
  DFkevfun ::  "(DFkevPN, 'event) pnfun"
where
  "DFkevfun (DFkev 0 _) = DIV"
| "DFkevfun (DFkev k 0) = DIV"
| "DFkevfun (DFkev k i) = (if (i > k) then DIV else ! x -> (if (i - 1 = 0) then $DFkev k k else $DFkev k (i-1)))"


overloading Set_DFkevfun == 
  "CSP_syntax.PNfun :: (DFkevPN, 'event) pnfun"
begin
  definition "CSP_syntax.PNfun :: (DFkevPN, 'event) pnfun == DFkevfun"
end

declare Set_DFkevfun_def [simp]


lemma guardedfun_DFkevfun [simp]: "guardedfun DFkevfun"
  apply (simp add: guardedfun_def)
  apply (rule allI, induct_tac p)
  apply (case_tac x1a, simp_all)
    apply (case_tac x2a, simp_all)
  done



fun DF_induct_Hypotheses :: "DFkevPN \<Rightarrow> (DFnonTickPN, 'e) proc"
where
    "DF_induct_Hypotheses (DFkev k i) = $DFnonTick"

lemma Lemma_DFkevPN_To_DFtick :
    "DF_induct_Hypotheses p \<sqsubseteq>F (DFkevfun p) << DF_induct_Hypotheses"
  apply (induct_tac p, simp)
  apply (induct_tac x1a, simp)
    apply (case_tac x2a, simp_all)
    apply (case_tac x2a, simp_all)
      apply (rule, rule, cspF_unwind_left)
      apply (rule, rule, cspF_unwind_left)
  done



lemma DFnonTick_DFkev :
    "FPmode \<noteq> CMSmode \<Longrightarrow> $DFnonTick <=F $DFkev k i"
  apply (rule_tac Pf="DFkevfun" and f="DF_induct_Hypotheses" in cspF_fp_induct_ref_right)
  apply (simp, case_tac FPmode, simp_all)
  by (rule Lemma_DFkevPN_To_DFtick)


lemma DFtick_DFkev :
    "FPmode \<noteq> CMSmode \<Longrightarrow> $DFtick <=F $DFkev k i"
  apply (rule cspF_trans, rule DFtick_DFnonTick)
  by (rule DFnonTick_DFkev)


lemma DFkev_is_DeadlockFree:
    "FPmode \<noteq> CMSmode \<Longrightarrow> (($DFkev k i) :: (DFkevPN, 'e) proc) isDeadlockFree"
  by (simp only: DeadlockFree_DFtick_ref, rule DFtick_DFkev)



end