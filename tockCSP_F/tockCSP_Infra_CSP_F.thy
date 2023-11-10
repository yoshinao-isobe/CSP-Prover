           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 2022 / 2023               |
            |                                           |
            |          Lemmas and Theorems from         |
            |    Jesus and Sampaio's SBMF 2022 paper    |
            |                     and                   |
            |    Jesus and Sampaio's SCP 2023 paper     |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory tockCSP_Infra_CSP_F
imports tockCSP_T.tockCSP_T_Main
        CSP_F.CSP_F
begin


subsection \<open> tockCSP_Infra_CSP_F - TODO: move to CSP_F \<close>


lemma S_UnF_T :
    "S UnF T = {u. u :f S \<or> u :f T}f"
by (simp add: UnionF_def CollectF_def Un_def memF_def)




lemma fstF_MF_iff_traces :
    "(Pf::('p,'e) pnfun) = PNfun \<Longrightarrow>
     FPmode = CMSmode \<longrightarrow> guardedfun Pf \<Longrightarrow>
     fstF (MF p) = traces (($p)::('p,'e) proc) MT"
  apply (subst fstF_MF_iff_MT, simp)
  apply (case_tac FPmode, simp_all)
  by (simp add: traces_iff)


lemma sndF_MF_iff_failures :
    "sndF (MF p) = failures ($p) MF"
  by (simp add: failures_iff)


lemma failures_Hiding_Hiding :
    "failures (P -- X -- X) M = failures (P -- X) M"
  apply (subst failures_iff)
  apply (rule sym)
  apply (subst failures_iff)
  apply (subst Abs_setF_inject, simp_all add: Hiding_setF)
  apply (subst in_failures_Hiding)
  apply (rule Collect_cong)
  apply (rule)
  apply (elim exE)
  apply (rule_tac x="s --tr X" in exI, simp add: hide_tr_of_hide_tr_subset1)
  apply (rule_tac x=s in exI, simp)

  apply (elim exE conjE)
  apply (rule_tac x=sa in exI, simp add: hide_tr_of_hide_tr_subset1)
  done



lemma in_failures_Inductive_parallel_map :
    "finite I ==> x ~= [] ==>
     (s, X) :f failures ([||] map PXf x) MF = 
     (sett s <= insert Tick (Ev ` (UN a:set x . snd (PXf a))) &
      (EX PXYs. map fst PXYs = map PXf x &
              X Int insert Tick (Ev ` (UN a:set x. snd (PXf a))) =
                  Union {Y Int insert Tick (Ev ` X) |X Y. EX P. ((P, X), Y) : set PXYs} &
              (ALL P X Y. ((P, X), Y) : set PXYs \<longrightarrow> (s rest-tr X, Y) :f failures P MF)))"
  by (subst in_failures_par, simp_all)

end