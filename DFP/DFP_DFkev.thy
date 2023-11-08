           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                  2022 / 2023 (modified)   |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_DFkev
imports DFP_law_DF
        DFP_law_DFtick
begin


subsection \<open> DFkEvTick \<close>
text \<open> The process that performs k events then SKIP \<close>


datatype DFkEvTickPN = DFkEvTick nat


fun DFkEvTickfun ::  "(DFkEvTickPN, 'event) pnfun"
where
  "DFkEvTickfun (DFkEvTick 0) = SKIP"
| "DFkEvTickfun (DFkEvTick k) = ! x -> $DFkEvTick (k-1)"


overloading Set_DFkEvTickfun == 
  "CSP_syntax.PNfun :: (DFkEvTickPN, 'event) pnfun"
begin
  definition "CSP_syntax.PNfun :: (DFkEvTickPN, 'event) pnfun == DFkEvTickfun"
end

declare Set_DFkEvTickfun_def [simp]


lemma guarded_DFkEvTickfun [simp]: "guarded (DFkEvTickfun p)"
  apply (induct_tac p)
  apply (case_tac xa, simp_all)
  done


lemma guardedfun_DFkEvTickfun [simp]: "guardedfun DFkEvTickfun"
  by (simp add: guardedfun_def)



subsubsection \<open> dfp_DFkEvTick \<close>

fun DF_induct_Hypotheses :: "DFkEvTickPN \<Rightarrow> (DFtickName, 'e) proc"
where
    "DF_induct_Hypotheses (DFkEvTick k) = $DFtick"


lemma Lemma_DFkEvTickPN_To_DFtick :
    "DF_induct_Hypotheses p \<sqsubseteq>F (DFkEvTickfun p) << DF_induct_Hypotheses"
  apply (induct_tac p, simp)
  apply (induct_tac xa)
  apply (simp, rule dfp)
  apply (simp, rule dfp)
  by (rule dfp)+


lemma dfp_DFkEvTick :
    "$DFtick <=F $DFkEvTick k"
  apply (rule_tac Pf="DFkEvTickfun" and f="DF_induct_Hypotheses" in cspF_fp_induct_ref_right)
  apply (simp, case_tac FPmode, simp_all)
  by (rule Lemma_DFkEvTickPN_To_DFtick)


lemma DFkEvTick_is_DeadlockFree:
    "(($DFkEvTick k) :: (DFkEvTickPN, 'e) proc) isDeadlockFree"
  by (simp only: DeadlockFree_DFtick_ref, rule dfp_DFkEvTick)




subsection \<open> DFkEv \<close>
text \<open> The process that performs k events then RECURS \<close>

datatype DFkEvPN = DFkEv nat nat


fun DFkEvfun ::  "(DFkEvPN, 'event) pnfun"
where
  "DFkEvfun (DFkEv 0 _) = DIV"
| "DFkEvfun (DFkEv k 0) = DIV"
| "DFkEvfun (DFkEv k i) = (if (i > k)
                           then DIV
                           else ! x -> $DFkEv k (if (i - 1 = 0) then k else i-1))"


overloading Set_DFkEvfun == 
  "CSP_syntax.PNfun :: (DFkEvPN, 'event) pnfun"
begin
  definition "CSP_syntax.PNfun :: (DFkEvPN, 'event) pnfun == DFkEvfun"
end

declare Set_DFkEvfun_def [simp]


lemma guarded_DFkEvfun [simp]: "guarded(DFkEvfun p)"
  apply (induct_tac p)
  apply (case_tac x1a, simp_all)
    apply (case_tac x2a, simp_all)
  done


lemma guardedfun_DFkEvfun [simp]: "guardedfun DFkEvfun"
  by (simp add: guardedfun_def)



subsubsection \<open> dfp_DFkEv \<close>

fun DF_induct_Hypotheses2 :: "DFkEvPN \<Rightarrow> (DFPN, 'e) proc"
where
    "DF_induct_Hypotheses2 (DFkEv k i) = DF"


lemma Lemma_DFkEvPN_To_DFtick :
    "DF_induct_Hypotheses2 p \<sqsubseteq>F (DFkEvfun p) << DF_induct_Hypotheses2"
  apply (induct_tac p, simp)
  apply (induct_tac x1a, simp)
    apply (case_tac x2a, simp_all add: DF_def)
      apply (rule, cspF_unwind_left)
  done


lemma dfnt_DFkEv :
    "DF <=F $DFkEv k i"
  apply (rule_tac Pf="DFkEvfun" and f="DF_induct_Hypotheses2" in cspF_fp_induct_ref_right)
  apply (simp, case_tac FPmode, simp_all)
  by (rule Lemma_DFkEvPN_To_DFtick)


lemma dfp_DFkEv :
    "$DFtick <=F $DFkEv k i"
  by (rule cspF_trans, rule dfp_DF, rule dfnt_DFkEv)

lemma DFkEv_is_DeadlockFree:
    "(($DFkEv k i) :: (DFkEvPN, 'e) proc) isDeadlockFree"
  by (simp only: DeadlockFree_DFtick_ref, rule dfp_DFkEv)





subsection \<open> kevPN = kEvTick | kEvRec \<close>
text \<open> The processes that performs k events then does X (SKIP (Tick) ou recur) \<close>

(*datatype kevPN = kEvTick nat
                | kEvRec nat nat*)
type_synonym kevPN = "(DFkEvTickPN, DFkEvPN) Sum_Type.sum"
abbreviation "kEvTick == \<lambda>x. (Inl (DFkEvTick x)::kevPN)"
abbreviation "kEvRec == \<lambda>x i. (Inr (DFkEv x i)::kevPN)"

(*fun kevfun ::  "(kevPN, 'event) pnfun"
where
  "kevfun(Inl x) = (DFkEvTickfun x) << (\<lambda>x. $Inl x)"
| "kevfun(Inr x) = (DFkEvfun x) << (\<lambda>x. $Inr x)"*)

fun kevfun ::  "(kevPN, 'event) pnfun"
where
  "kevfun (kEvTick 0) = SKIP"
| "kevfun (kEvTick k) = ! x -> $kEvTick (k-1)"
| "kevfun (kEvRec 0 _) = DIV"
| "kevfun (kEvRec _ 0) = DIV"
| "kevfun (kEvRec k i) = (if (i > k) then DIV
                           else ! x -> $kEvRec k (if (i - 1 = 0) then k else i-1))"



overloading Set_kevfun == 
  "CSP_syntax.PNfun :: (kevPN, 'event) pnfun"
begin
  definition "CSP_syntax.PNfun :: (kevPN, 'event) pnfun == kevfun"
end

declare Set_kevfun_def [simp]


lemma guardedfun_kevfun [simp]: "guardedfun kevfun"
  apply (simp add: guardedfun_def)
  apply (rule allI, induct_tac p)
  apply (case_tac a, simp_all)
  apply (case_tac x, simp_all)
  apply (case_tac b, simp_all)
  apply (case_tac x1, simp_all)
  apply (case_tac x2, simp_all)
  done



subsubsection \<open> dfp_kEvTick (kEvTick to DFkEvTick) \<close>

fun DF_induct_Hypotheses3 :: "DFkEvTickPN \<Rightarrow> (kevPN, 'e) proc"
where
    "DF_induct_Hypotheses3 (DFkEvTick k) = $kEvTick k"


lemma Lemma_DFkEvTickPN_To_kEvTick :
    "DF_induct_Hypotheses3 p =F (DFkEvTickfun p) << DF_induct_Hypotheses3"
  apply (induct_tac p, simp)
  apply (induct_tac xa, simp)
    apply (cspF_unwind_left)
    apply (cspF_unwind_left)
  done

lemma cspF_kEvTick_to_DFkEvTick :
    "FPmode \<noteq> CPOmode \<Longrightarrow> $kEvTick k =F $DFkEvTick k"
  apply (rule_tac Pf="DFkEvTickfun" and f="DF_induct_Hypotheses3" in cspF_fp_induct_eq_right)
  apply (simp, case_tac FPmode, simp_all)
  by (rule Lemma_DFkEvTickPN_To_kEvTick)

lemma cspF_kev_to_kEvTick :
    "FPmode \<noteq> CPOmode \<Longrightarrow> $DFkEvTick k =F $kEvTick k"
  by (rule cspF_sym, rule cspF_kEvTick_to_DFkEvTick)



lemma dfp_kEvTick :
    "FPmode \<noteq> CPOmode \<Longrightarrow> $DFtick <=F $kEvTick k"
  by (rule cspF_rw_right, rule cspF_kEvTick_to_DFkEvTick, simp, rule dfp_DFkEvTick)


lemma kEvTick_is_DeadlockFree:
    "FPmode \<noteq> CPOmode \<Longrightarrow> (($kEvTick k) :: (kevPN, 'e) proc) isDeadlockFree"
  by (simp only: DeadlockFree_DFtick_ref, rule dfp_kEvTick, simp)



subsubsection \<open> dfp_kEvRec (kEvRec to DFkEv) \<close>


fun DF_induct_Hypotheses4 :: "DFkEvPN \<Rightarrow> (kevPN, 'e) proc"
where
    "DF_induct_Hypotheses4 (DFkEv k i) = $kEvRec k i"


lemma Lemma_DFkEvPN_induct_right :
    "DF_induct_Hypotheses4 p =F (DFkEvfun p) << DF_induct_Hypotheses4"
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

lemma cspF_kEvRec_to_DFkEv :
    "FPmode \<noteq> CPOmode \<Longrightarrow> $kEvRec k i =F $DFkEv k i"
  apply (rule_tac Pf="DFkEvfun" and f="DF_induct_Hypotheses4" in cspF_fp_induct_eq_right)
  apply (simp_all)
  by (rule Lemma_DFkEvPN_induct_right)

lemma cspF_DFkEv_to_kEvRec :
    "FPmode \<noteq> CPOmode \<Longrightarrow> $DFkEv k i =F $kEvRec k i"
  by (rule cspF_sym, rule cspF_kEvRec_to_DFkEv)



lemma dfp_kEvRec :
    "FPmode \<noteq> CPOmode \<Longrightarrow> $DFtick <=F $kEvRec k i"
  by (rule cspF_rw_right, rule cspF_kEvRec_to_DFkEv, simp, rule dfp_DFkEv)


lemma kEvRec_is_DeadlockFree:
    "FPmode \<noteq> CPOmode \<Longrightarrow> (($kEvRec k i) :: (kevPN, 'e) proc) isDeadlockFree"
  by (simp only: DeadlockFree_DFtick_ref, rule dfp_kEvRec, simp)






end