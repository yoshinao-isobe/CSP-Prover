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

theory TSF_Infra
imports tockCSP_DFP.tockCSP_Infra_DFP
        tockCSP.tockCSP_tock
begin



lemma insert_Tick_Evset_Un [simp]:
    "insert Tick (Evset Un X) = EvsetTick"
  apply (simp only: insert_def Un_left_commute)
  by (subst Evset_Un_eq_EvsetTick_if, simp_all)



lemma hide_tr_X_neq_sett :
    "~ (sett s <= (- Ev ` X)) ==> (t --tr (X) ~= s)"
  apply (erule contrapos_nn)
  by (simp add: hide_tr_X_sett)

lemma hide_tr_non_x_neq_sett :
    "~ (sett s <= {Tick,Ev x}) ==> (t --tr (- {x}) ~= s)"
  apply (erule contrapos_nn)
  by (simp add: hide_tr_non_x_sett)


lemma nilt_if_Tick_notin_hide_tr_x_and_non_x :
    "Tick ~: sett t ==> (s --tr {x} = t) ==> (s --tr (- {x}) = t) ==> t = <>"
  apply (induct t rule: induct_trace, simp, simp)
  by (drule hide_tr_singleton_only_if, simp)

lemma nilt_if_noTick_hide_tr_x_and_non_x :
    "noTick t ==> (s --tr {x} = t) ==> (s --tr (- {x}) = t) ==> t = <>"
  apply (simp add: noTick_def)
  by (rule nilt_if_Tick_notin_hide_tr_x_and_non_x)

lemma nilt_if_Tick_notin_src_hide_tr_x_and_non_x :
    "Tick ~: sett s ==> (s --tr {x} = t) ==> (s --tr (- {x}) = t) ==> t = <>"
  apply (frule Tick_notin_hide_tr_trans2, simp)
  by (rule nilt_if_Tick_notin_hide_tr_x_and_non_x, simp_all)

lemma nilt_if_noTick_src_hide_tr_x_and_non_x :
    "noTick s ==> (s --tr {x} = t) ==> (s --tr (- {x}) = t) ==> t = <>"
  apply (simp add: noTick_def)
  by (rule nilt_if_Tick_notin_src_hide_tr_x_and_non_x)


lemma tocks_only_if :
    "t =tocks(s) ==> t \<noteq>nontocks(s) \<or> t = <> \<or> t = <Tick>"
  by (frule hide_tr_Compl_singleton_only_if, simp_all)

lemma nontocks_only_if :
    "t =nontocks(s) ==> t \<noteq>tocks(s) \<or> t = <> \<or> t = <Tick>"
  by (frule hide_tr_singleton_only_if, simp_all)

lemma nilt_if_Tick_notin_tocks_nontocks :
    "Tick ~: sett t ==> t =nontocks(s) ==> t =tocks(s) ==> t = <>"
  by (rule nilt_if_Tick_notin_hide_tr_x_and_non_x)

lemma nilt_if_noTick_tocks_nontocks :
    "noTick t ==> t =nontocks(s) ==> t =tocks(s) ==> t = <>"
  by (rule nilt_if_noTick_hide_tr_x_and_non_x)

lemma nilt_if_Tick_notin_src_tocks_nontocks :
    "Tick ~: sett s ==> t =nontocks(s) ==> t =tocks(s) ==> t = <>"
  by (rule nilt_if_Tick_notin_src_hide_tr_x_and_non_x)

lemma nilt_if_noTick_src_tocks_nontocks :
    "noTick s ==> t =nontocks(s) ==> t =tocks(s) ==> t = <>"
  by (rule nilt_if_noTick_src_hide_tr_x_and_non_x)


lemma Tick_notin_src_tocks_nontocks_imp_eq_or_nilt :
    "Tick ~: sett s ==> t =nontocks(s) ==> nt =tocks(s) ==> t = nt \<or> s ~= <>"
  apply (induct s rule: induct_trace)
  apply (simp)
  apply (simp)
  by (drule sym, simp)



lemma nilt_tocks_nontocks :
    "Tick ~: sett s ==> <> =nontocks(s) ==> <> =tocks(s) ==> s = <>"
  apply (induct s rule: induct_trace, simp, simp)
  apply (simp)
  by (case_tac "a = tock", simp, simp)


lemma Tick_notin_src_tocks_nontocks_nilt_iff :
    "Tick ~: sett s ==> t =nontocks(s) ==> nt =tocks(s) ==> t = nt \<longleftrightarrow> s = <>"
  apply (rule)
  apply (frule Tick_notin_src_tocks_nontocks_imp_eq_or_nilt, simp_all)
  apply (case_tac "s = <>", simp)
  apply (frule_tac s=s in nilt_if_Tick_notin_src_tocks_nontocks, simp, simp, simp)
  by (frule_tac s=s in nilt_tocks_nontocks, simp_all)


end