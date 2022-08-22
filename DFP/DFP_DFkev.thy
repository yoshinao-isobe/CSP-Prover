           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_DFkev
imports DFP_DFnonTick
begin


subsection \<open> kev \<close>
text \<open> The process that performs k events then SKIP \<close>

datatype kevPN = kev nat


fun
  kevfun ::  "(kevPN, 'event) pnfun"
where
  "kevfun (kev 0) = SKIP"
| "kevfun (kev k) = ! x -> $kev (k-1)"


overloading Set_kevfun == 
  "CSP_syntax.PNfun :: (kevPN, 'event) pnfun"
begin
  definition "CSP_syntax.PNfun :: (kevPN, 'event) pnfun == kevfun"
end

declare Set_kevfun_def [simp]


lemma guardedfun_kevfun [simp]: "guardedfun kevfun"
  apply (simp add: guardedfun_def)
  apply (rule allI, induct_tac p)
  apply (case_tac xa, simp_all)
  done



subsubsection \<open> dfp_kev \<close>

fun DF_induct_Hypotheses :: "kevPN \<Rightarrow> (DFtickName, 'e) proc"
where
    "DF_induct_Hypotheses (kev k) = $DFtick"


lemma Lemma_kevPN_To_DFtick :
    "DF_induct_Hypotheses p \<sqsubseteq>F (kevfun p) << DF_induct_Hypotheses"
  apply (induct_tac p, simp)
  apply (induct_tac xa)
  apply (simp, rule dfp)
  apply (simp, rule dfp)
  by (rule dfp)+


lemma dfp_kev :
    "$DFtick <=F $kev k"
  apply (rule_tac Pf="kevfun" and f="DF_induct_Hypotheses" in cspF_fp_induct_ref_right)
  apply (simp, case_tac FPmode, simp_all)
  by (rule Lemma_kevPN_To_DFtick)


lemma kev_is_DeadlockFree:
    "(($kev k) :: (kevPN, 'e) proc) isDeadlockFree"
  by (simp only: DeadlockFree_DFtick_ref, rule dfp_kev)




subsection \<open> DFkev \<close>
text \<open> The process that performs k events then RECURS \<close>

datatype DFkevPN = DFkev nat nat


fun
  DFkevfun ::  "(DFkevPN, 'event) pnfun"
where
  "DFkevfun (DFkev 0 _) = DIV"
| "DFkevfun (DFkev k 0) = DIV"
| "DFkevfun (DFkev k i) = (if (i > k) then DIV
                                      else ! x -> $DFkev k (if (i - 1 = 0) then k else i-1))"


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


subsubsection \<open> dfp_DFkev \<close>

fun DF_induct_Hypotheses2 :: "DFkevPN \<Rightarrow> (DFnonTickPN, 'e) proc"
where
    "DF_induct_Hypotheses2 (DFkev k i) = $DFnonTick"


lemma Lemma_DFkevPN_To_DFtick :
    "DF_induct_Hypotheses2 p \<sqsubseteq>F (DFkevfun p) << DF_induct_Hypotheses2"
  apply (induct_tac p, simp)
  apply (induct_tac x1a, simp)
    apply (case_tac x2a, simp_all)
      apply (rule, cspF_unwind_left)
  done


lemma dfnt_DFkev :
    "$DFnonTick <=F $DFkev k i"
  apply (rule_tac Pf="DFkevfun" and f="DF_induct_Hypotheses2" in cspF_fp_induct_ref_right)
  apply (simp, case_tac FPmode, simp_all)
  by (rule Lemma_DFkevPN_To_DFtick)


lemma dfp_DFkev :
    "$DFtick <=F $DFkev k i"
  apply (rule cspF_trans, rule dfp_DFnonTick)
  by (rule dfnt_DFkev)

lemma DFkev_is_DeadlockFree:
    "(($DFkev k i) :: (DFkevPN, 'e) proc) isDeadlockFree"
  by (simp only: DeadlockFree_DFtick_ref, rule dfp_DFkev)





subsection \<open> kevXPN = kevT | kevR \<close>
text \<open> The processes that performs k events then does X (SKIP (Tick) ou recur) \<close>

datatype kevXPN = kevT nat
                | kevR nat nat


fun
  kevXfun ::  "(kevXPN, 'event) pnfun"
where
  "kevXfun (kevT 0) = SKIP"
| "kevXfun (kevT k) = ! x -> $kevT (k-1)"
| "kevXfun (kevR 0 _) = DIV"
| "kevXfun (kevR _ 0) = DIV"
| "kevXfun (kevR k i) = (if (i > k) then DIV
                                    else ! x -> $kevR k (if (i - 1 = 0) then k else i-1))"


overloading Set_kevXfun == 
  "CSP_syntax.PNfun :: (kevXPN, 'event) pnfun"
begin
  definition "CSP_syntax.PNfun :: (kevXPN, 'event) pnfun == kevXfun"
end

declare Set_kevXfun_def [simp]


lemma guardedfun_kevXfun [simp]: "guardedfun kevXfun"
  apply (simp add: guardedfun_def)
  apply (rule allI, induct_tac p)
  apply (case_tac x, simp_all)
  apply (case_tac x1a, simp_all)
  apply (case_tac x2, simp_all)
  done



subsubsection \<open> dfp_kevT (kevT to kev) \<close>

fun DF_induct_Hypotheses3 :: "kevPN \<Rightarrow> (kevXPN, 'e) proc"
where
    "DF_induct_Hypotheses3 (kev k) = $kevT k"


lemma Lemma_kevPN_To_kevT :
    "DF_induct_Hypotheses3 p =F (kevfun p) << DF_induct_Hypotheses3"
  apply (induct_tac p, simp)
  apply (induct_tac xa, simp)
    apply (cspF_unwind_left)
    apply (cspF_unwind_left)
  done


lemma cspF_kevT_to_kev :
    "FPmode \<noteq> CPOmode \<Longrightarrow> $kevT k =F $kev k"
  apply (rule_tac Pf="kevfun" and f="DF_induct_Hypotheses3" in cspF_fp_induct_eq_right)
  apply (simp, case_tac FPmode, simp_all)
  by (rule Lemma_kevPN_To_kevT)

lemma cspF_kev_to_kevT :
    "FPmode \<noteq> CPOmode \<Longrightarrow> $kev k =F $kevT k"
  by (rule cspF_sym, rule cspF_kevT_to_kev)



lemma dfp_kevT :
    "FPmode \<noteq> CPOmode \<Longrightarrow> $DFtick <=F $kevT k"
  by (rule cspF_rw_right, rule cspF_kevT_to_kev, simp, rule dfp_kev)


lemma kevT_is_DeadlockFree:
    "FPmode \<noteq> CPOmode \<Longrightarrow> (($kevT k) :: (kevXPN, 'e) proc) isDeadlockFree"
  by (simp only: DeadlockFree_DFtick_ref, rule dfp_kevT, simp)



subsubsection \<open> dfp_kevR (kevR to DFkev) \<close>


fun DF_induct_Hypotheses4 :: "DFkevPN \<Rightarrow> (kevXPN, 'e) proc"
where
    "DF_induct_Hypotheses4 (DFkev k i) = $kevR k i"


lemma Lemma_DFkevPN_induct_right :
    "DF_induct_Hypotheses4 p =F (DFkevfun p) << DF_induct_Hypotheses4"
  apply (induct_tac p, simp)
  apply (induct_tac x1a, simp)
      apply (cspF_unwind_left)
    apply (case_tac x2a, simp_all)
      apply (cspF_unwind_left)
      apply (rule, rule, cspF_unwind_left)
      apply (rule)
      apply (rule, rule, cspF_unwind_left)
      apply (rule, cspF_unwind_left)
  done

lemma cspF_kevR_to_DFkev :
    "FPmode \<noteq> CPOmode \<Longrightarrow> $kevR k i =F $DFkev k i"
  apply (rule_tac Pf="DFkevfun" and f="DF_induct_Hypotheses4" in cspF_fp_induct_eq_right)
  apply (simp_all)
  by (rule Lemma_DFkevPN_induct_right)         

lemma cspF_DFkev_to_kevR :
    "FPmode \<noteq> CPOmode \<Longrightarrow> $DFkev k i =F $kevR k i"
  by (rule cspF_sym, rule cspF_kevR_to_DFkev)



lemma dfp_kevR :
    "FPmode \<noteq> CPOmode \<Longrightarrow> $DFtick <=F $kevR k i"
  by (rule cspF_rw_right, rule cspF_kevR_to_DFkev, simp, rule dfp_DFkev)


lemma kevR_is_DeadlockFree:
    "FPmode \<noteq> CPOmode \<Longrightarrow> (($kevR k i) :: (kevXPN, 'e) proc) isDeadlockFree"
  by (simp only: DeadlockFree_DFtick_ref, rule dfp_kevR, simp)






end