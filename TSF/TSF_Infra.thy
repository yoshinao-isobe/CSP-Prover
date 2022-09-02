theory TSF_Infra
imports tockCSP_DFP.tockCSP_Infra_DFP
        tockCSP_DFP_Main
begin


lemma insert_Tick_Evset_Un [simp]:
    "insert Tick (Evset Un X) = EvsetTick"
  apply (simp only: insert_def Un_left_commute)
  by (subst Evset_Un_eq_EvsetTick_if, simp_all)



lemma hide_tr_X_neq_sett :
    "~ (sett s <= (- Ev ` X)) \<Longrightarrow> (t --tr (X) ~= s)"
  apply (erule contrapos_nn)
  by (simp add: hide_tr_X_sett)

lemma hide_tr_non_x_neq_sett :
    "~ (sett s <= {Tick,Ev x}) \<Longrightarrow> (t --tr (- {x}) ~= s)"
  apply (erule contrapos_nn)
  by (simp add: hide_tr_non_x_sett)


lemma nilt_if_Tick_notin_hide_tr_x_and_non_x :
    "Tick \<notin> sett t \<Longrightarrow> (s --tr {x} = t) \<Longrightarrow> (s --tr (- {x}) = t) \<Longrightarrow> t = <>"
  apply (induct t rule: induct_trace, simp, simp)
  by (drule hide_tr_singleton_only_if, simp)

lemma nilt_if_noTick_hide_tr_x_and_non_x :
    "noTick t \<Longrightarrow> (s --tr {x} = t) \<Longrightarrow> (s --tr (- {x}) = t) \<Longrightarrow> t = <>"
  apply (simp add: noTick_def)
  by (rule nilt_if_Tick_notin_hide_tr_x_and_non_x)

lemma nilt_if_Tick_notin_src_hide_tr_x_and_non_x :
    "Tick \<notin> sett s \<Longrightarrow> (s --tr {x} = t) \<Longrightarrow> (s --tr (- {x}) = t) \<Longrightarrow> t = <>"
  apply (frule Tick_notin_hide_tr_trans2, simp)
  by (rule nilt_if_Tick_notin_hide_tr_x_and_non_x, simp_all)

lemma nilt_if_noTick_src_hide_tr_x_and_non_x :
    "noTick s \<Longrightarrow> (s --tr {x} = t) \<Longrightarrow> (s --tr (- {x}) = t) \<Longrightarrow> t = <>"
  apply (simp add: noTick_def)
  by (rule nilt_if_Tick_notin_src_hide_tr_x_and_non_x)


lemma tocks_only_if :
    "t =tocks(s) \<Longrightarrow> t \<noteq>nontocks(s) \<or> t = <> \<or> t = <Tick>"
  by (frule hide_tr_Compl_singleton_only_if, simp_all)

lemma nontocks_only_if :
    "t =nontocks(s) \<Longrightarrow> t \<noteq>tocks(s) \<or> t = <> \<or> t = <Tick>"
  by (frule hide_tr_singleton_only_if, simp_all)

lemma nilt_if_Tick_notin_tocks_nontocks :
    "Tick \<notin> sett t \<Longrightarrow> t =nontocks(s) \<Longrightarrow> t =tocks(s) \<Longrightarrow> t = <>"
  by (rule nilt_if_Tick_notin_hide_tr_x_and_non_x)

lemma nilt_if_noTick_tocks_nontocks :
    "noTick t \<Longrightarrow> t =nontocks(s) \<Longrightarrow> t =tocks(s) \<Longrightarrow> t = <>"
  by (rule nilt_if_noTick_hide_tr_x_and_non_x)

lemma nilt_if_Tick_notin_src_tocks_nontocks :
    "Tick \<notin> sett s \<Longrightarrow> t =nontocks(s) \<Longrightarrow> t =tocks(s) \<Longrightarrow> t = <>"
  by (rule nilt_if_Tick_notin_src_hide_tr_x_and_non_x)

lemma nilt_if_noTick_src_tocks_nontocks :
    "noTick s \<Longrightarrow> t =nontocks(s) \<Longrightarrow> t =tocks(s) \<Longrightarrow> t = <>"
  by (rule nilt_if_noTick_src_hide_tr_x_and_non_x)


lemma Tick_notin_src_tocks_nontocks_imp_eq_or_nilt :
    "Tick \<notin> sett s \<Longrightarrow> t =nontocks(s) \<Longrightarrow> nt =tocks(s) \<Longrightarrow> t = nt \<or> s ~= <>"
  apply (induct s rule: induct_trace)
  apply (simp)
  apply (simp)
  by (drule sym, simp)



lemma nilt_tocks_nontocks :
    "Tick \<notin> sett s \<Longrightarrow> <> =nontocks(s) \<Longrightarrow> <> =tocks(s) \<Longrightarrow> s = <>"
  apply (induct s rule: induct_trace, simp, simp)
  apply (simp)
  by (case_tac "a = tock", simp, simp)


lemma Tick_notin_src_tocks_nontocks_nilt_iff :
    "Tick \<notin> sett s \<Longrightarrow> t =nontocks(s) \<Longrightarrow> nt =tocks(s) \<Longrightarrow> t = nt \<longleftrightarrow> s = <>"
  apply (rule)
  apply (frule Tick_notin_src_tocks_nontocks_imp_eq_or_nilt, simp_all)
  apply (case_tac "s = <>", simp)
  apply (frule_tac s=s in nilt_if_Tick_notin_src_tocks_nontocks, simp, simp, simp)
  by (frule_tac s=s in nilt_tocks_nontocks, simp_all)





end