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

theory tockCSP_Infra_CSP
imports tockCSP_Infra_HOL
        CSP
begin

(* TODO: tockCSP_Infra_CSP - move to CSP *)

subsection \<open> EvsetTick, Evset and Tick \<close>


lemma in_EvsetTick [simp]:
    "x \<in> EvsetTick"
  by (simp add: EvsetTick_def)


lemma insert_EvsetTick :
    "insert x EvsetTick = EvsetTick"
  by (auto)


lemma not_EvsetTick_eq_Evset [simp]:
    "\<not> EvsetTick = Evset"
  by (auto simp add: EvsetTick_def Evset_def)


lemma not_EvsetTick_subset_Evset [simp]:
    "\<not> EvsetTick \<subseteq> Evset"
  by (auto simp add: EvsetTick_def Evset_def)


lemma Un_EvsetTick [simp]:
    "X \<union> EvsetTick = EvsetTick"
  by (simp add: EvsetTick_def)


lemma EvsetTick_Un [simp]:
    "EvsetTick \<union> X = EvsetTick"
  by (simp add: EvsetTick_def)


lemma EvsetTick_Int [simp]:
    "EvsetTick \<inter> X = X"
  by (simp add: EvsetTick_def)


lemma EvsetTick_neq_Ev_image :
    "EvsetTick \<noteq> Ev ` X"
  by (auto simp add: EvsetTick_def)


lemma Evset_Ev_UNIV :
    "Evset = Ev ` UNIV"
  apply (auto simp add: Evset_def image_def)
  by (case_tac x, simp_all)


lemma Evset_Un_image [simp]:
    "Evset \<union> Ev ` X = Evset"
  by (auto simp add: Evset_def)


lemma Evset_Int_image [simp]:
    "Evset \<inter> Ev ` X = Ev ` X"
  by (auto simp add: Evset_def)


lemma not_subset_Evset :
    "\<not> X \<subseteq> Evset \<Longrightarrow> Tick : X"
  by (simp add: subset_eq Evset_def)



lemma Tick_notin_Evset [simp]:
    "Tick \<notin> Evset"
  by (simp add: Evset_def)


(* MOVE Tick_notin_Ev_image to CSP.Trace *)
lemma Tick_notin_Ev_image [simp]:
    "Tick \<notin> Ev ` X"
  by (simp add: image_def)


lemma ex_Tick_notin : "\<exists>Y. Tick \<notin> Y"
  by (auto)


lemma ex_Tick_in : "\<exists>Y. Tick \<in> Y"
  by (auto)


lemma Tick_notin_iff_noTick :
    "Tick \<notin> sett t \<longleftrightarrow> noTick t"
  by (simp add: noTick_def)

lemma Evset_Un_eq_EvsetTick_if :
    "Tick \<in> X \<Longrightarrow> Evset \<union> X = EvsetTick"
  by (auto simp add: Evset_def EvsetTick_def)


lemma insert_Tick_Evset [simp]:
    "insert Tick Evset = EvsetTick"
  apply (simp only: insert_def Un_commute)
  by (rule Evset_Un_eq_EvsetTick_if, simp)



subsection \<open> appt ^^^ \<close>


lemma Ev_appt_neq_event_right [simp]:
    "<Ev a> ^^^ s ~= s"
  apply (simp add: appt_def)
  apply (simp add: Abs_trace_inverse nilt_def)
  apply (rule Abs_trace_induct)
  apply (simp add: Abs_trace_inverse)
  apply (subgoal_tac "Ev a # y : trace")
  apply (simp add: Abs_trace_inject)
  apply (simp add: trace_def)
  done


lemma event_neq_Ev_appt_right [simp]:
    "s ~= <Ev a> ^^^ s"
  by (rule not_sym, simp)


lemma event_app_not_nil_right_sym[simp]:
    "noTick s ==> <> ~= s ^^^ <e>"
  by (rule not_sym, simp)


lemma event_app_not_nil_left_sym[simp]:
    "<> ~= <Ev a> ^^^ s"
  by (rule not_sym, simp)



subsection \<open> cases for traces \<close>


lemma cases_event_list:
    "s : trace \<Longrightarrow> \<lbrakk> s = [] \<longrightarrow> P <> ; s = [Tick] \<longrightarrow> P <Tick> ; \<forall> t a. s = [Ev a] @ t \<longrightarrow> P (<Ev a> ^^^ Abs_trace t) \<rbrakk> \<Longrightarrow>
    P (Abs_trace s)"
  apply (case_tac s)
  
  (* base case *)
  apply (simp add: nilt_def)
  
  (* step case *)
  apply (insert event_Tick_or_Ev)
  apply (drule_tac x="a" in spec)
  apply (elim disjE conjE exE)
  apply (simp_all)

  apply (case_tac list)
  apply (simp add: trace_def)
  apply (simp add: trace_def)
  
  apply (simp add: appt_head)
  apply (simp add: decompo_head_in_trace, elim disjE)
  apply (simp add: Abs_trace_inverse)
  apply (simp add: Abs_trace_inverse)
  done


lemma cases_trace:
    "\<lbrakk> s = <> \<longrightarrow> P <> ; s = <Tick> \<longrightarrow> P <Tick> ; \<forall> t a. s = <Ev a> ^^^ t \<longrightarrow> P (<Ev a> ^^^ t) \<rbrakk> \<Longrightarrow>
    P (s)"
  apply (insert cases_event_list[of "Rep_trace s" P])
  apply (simp add: Rep_trace_inverse)
  by (induct s rule: induct_trace, simp_all)




subsection \<open> sett \<close>


lemma sett_empty_iff : "sett s = {} \<longleftrightarrow> s = <>"
  apply (simp add: sett_def)
  apply (simp add: nilt_def Abs_trace_inverse)
  by (case_tac s, simp_all add: Abs_trace_inverse Abs_trace_inject)


lemma sett_Tick_iff : "sett s = {Tick} \<longleftrightarrow> s = <Tick>"
  apply (insert sett_subset_Tick[of s])
  apply (simp add: subset_eq)
  by (force)


lemma sett_one_iff : "sett s = {Ev e} \<longleftrightarrow> (\<exists> sa. sett sa \<subseteq> {Ev e} \<and> s = <Ev e> ^^^ sa)"
  apply (induct s rule: induct_trace)
  apply (simp_all)
  apply (rule, elim conjE, simp)
by (simp add: subset_eq)



lemma sett_doubleton :
    "sett s = {Tick, e} \<Longrightarrow> \<exists>sa. sett sa \<subseteq> {e} \<and> s = sa ^^^ <Tick>"
  apply (induct s rule: induct_trace)
    apply (simp)
    apply (rule_tac x="<>" in exI, simp)
    apply (case_tac "Ev a : sett s")
      apply (simp add: insert_absorb)
        apply (elim exE)
        apply (rule_tac x="<e> ^^^ sa" in exI, simp, rule, force, rule appt_assoc_sym)
        apply (drule sym, simp)
        apply (rotate_tac 1)
        apply (drule sym, simp)
        apply (simp add: noTick_def subset_singleton_iff, force)
      apply (simp)
        apply (case_tac "Ev a = e", auto)
        apply (insert event.simps)
        apply (drule insert_eq_doubleton, simp_all)
        apply (auto simp add: sett_Tick_iff)
        apply (rule_tac x="<Ev a>" in exI, simp)
  done



subsection \<open> hidex addidtional intro lemmas \<close>

lemma hidex_intro_one_left_iff :
    "((<Ev a>, t) : hidex X) = ((<Ev a> ^^^ <>, t) : hidex X)"
  by (simp)

lemma hidex_intro_one_right_iff :
    "((s, <Ev a>) : hidex X) = ((s, <Ev a> ^^^ <>) : hidex X)"
  by (simp)

lemma hidex_one_in: 
    "[| (<>, t) : hidex X ; a : X |]
     ==> (<Ev a>, t) : hidex X"
  apply (simp only: hidex_intro_one_left_iff)
  by (subst hidex_in, simp_all)

lemma hidex_one_notin: 
  "[| a ~: X |]
   ==> (<Ev a>, <Ev a>) : hidex X"
  apply (simp only: hidex_intro_one_left_iff)
  apply (simp only: hidex_intro_one_right_iff)
  apply (subst hidex_notin, simp_all)
  by (simp add: hidex.intros)


lemma "b : X \<Longrightarrow> a \<notin> X \<Longrightarrow> c \<notin> X \<Longrightarrow>
     (<Ev a> ^^^ <Ev b> ^^^ <Ev c>, <Ev a> ^^^ <Ev c>) \<in> hidex X"
  apply (subst hidex.hidex_notin, simp_all)
  apply (subst hidex.hidex_in, simp_all)
  apply (simp add: hidex_one_notin)
  done


inductive_cases hidex_appt_casesE [elim!]: "(t, <Ev a> ^^^ s) \<in> hidex X"


subsection \<open> nonmember hidex if \<close>


lemma notin_hidex_if_lm :
    "a \<notin> X \<longrightarrow> t \<noteq> <> \<and> t \<noteq> <Tick> \<and> (\<forall> a s. t \<noteq> <Ev a> ^^^ s) \<longrightarrow>
    (t, <Ev a> ^^^ s) \<notin> hidex X"
  apply (induct_tac t rule: induct_trace)
  by (simp_all)


lemma notin_hidex_if :
    "a \<notin> X \<Longrightarrow> t \<noteq> <> \<Longrightarrow> t \<noteq> <Tick> \<Longrightarrow> (\<forall> a s. t \<noteq> <Ev a> ^^^ s) \<Longrightarrow>
    (t, <Ev a> ^^^ s) \<notin> hidex X"
  by (simp add: notin_hidex_if_lm)



lemma hidex_idem_if:
    "sett u \<subseteq> - (Ev ` X) \<Longrightarrow> (u,u) \<in> hidex X"
  apply (induct u rule: induct_trace)
  apply (simp_all add: hidex.intros)
  apply (case_tac "a : X")
  apply (simp_all add: hidex.intros)
  done

lemma hidex_idem_only_if:
    "(u,u) \<in> hidex X \<Longrightarrow> sett u \<subseteq> - (Ev ` X)"
  apply (erule hidex.induct, simp_all)
  apply (simp_all add: image_def)
  done

lemma hidex_idem_iff :
    "(u,u) \<in> hidex X \<longleftrightarrow> sett u \<subseteq> - (Ev ` X)"
  apply (rule)
    apply (rule hidex_idem_only_if, simp)
    apply (rule hidex_idem_if, simp)
  done


subsection \<open> hide_tr addidtional lemmas \<close>

lemma hide_tr_one_left_iff :
    "(<Ev a> --tr X = t) = ((<Ev a> ^^^ <>) --tr X = t)"
  by (simp only: hide_tr_iff hidex_intro_one_left_iff)


lemma hide_tr_one_right_iff :
    "(s --tr X = <Ev a>) = (s --tr X = (<Ev a> ^^^ <>))"
  by (simp only: hide_tr_iff hidex_intro_one_right_iff)


(*lemma "b : X \<Longrightarrow> a \<notin> X \<Longrightarrow> c \<notin> X \<Longrightarrow>
     (<Ev a> ^^^ <Ev b> ^^^ <Ev c>) --tr X = <Ev a> ^^^ <Ev c>"
  apply (subst hide_tr_notin_appt, simp)
  apply (subst hide_tr_in, simp)
  apply (subst hide_tr_notin, simp)
  by (simp)

lemma "a \<notin> X \<Longrightarrow> b \<in> X \<Longrightarrow>
     (<Ev a> ^^^ <Ev b>) --tr X = <Ev a> ^^^ <Ev b>"
  apply (subst hide_tr_notin_appt, simp)
  apply (subst hide_tr_in_one, simp)
  oops*)

(*lemma hide_tr_exists: 
    "EX t. s --tr X = t"
  by (simp)*)



lemma hide_tr_sym:
    "(t = s --tr X) = (s --tr X = t)"
  by (rule eq_commute)



lemma noTick_hide_tr :
    "s --tr X = t \<Longrightarrow> noTick t \<Longrightarrow> noTick s"
  by (drule sym, simp)



lemma hide_tr_X_sett :
    "(t --tr (X) = s) \<Longrightarrow> (sett s <= (- Ev ` X))"
  apply (induct t arbitrary: X rule: induct_trace)
    apply (simp, drule sym, simp)
    apply (rule)
    apply (force)
  done

lemma hide_tr_non_x_sett :
    "(t --tr (- {x}) = s) \<Longrightarrow> (sett s <= {Tick,Ev x})"
  apply (induct t arbitrary: x rule: induct_trace)
    apply (simp, drule sym, simp)
    apply (rule)
    apply (case_tac "xa", simp_all)
    apply (case_tac "x1 = x", simp_all)
    apply (drule sym, simp)
  done



lemma sett_hide_tr_non_x :
    "sett (t --tr (- {x})) <= {Tick,Ev x}"
  apply (induct t arbitrary: x rule: induct_trace)
    apply (rule)
    apply (case_tac "xa", simp_all)
    apply (case_tac "a = x", simp_all)
  done


lemma sett_hide_tr_non_x_noTick :
    "noTick t \<Longrightarrow> sett (t --tr (- {x})) <= {Ev x}"
  apply (induct t arbitrary: x rule: induct_trace)
    apply (rule)
    apply (case_tac "xa", simp_all)
    apply (case_tac "a = x", simp_all)
  done

(*
lemma hide_tr_id:
    "sett u \<subseteq> insert Tick (Ev ` Y) & X Int Y = {} \<Longrightarrow>
     u --tr X = u"
  by (simp add: Trace_hide.hide_tr_id)
*)

lemma hide_tr_idem_if:
    "sett u \<subseteq> - (Ev ` X) \<Longrightarrow> u --tr X = u"
  apply (simp only: hide_tr_to_hidex)
  by (erule hidex_idem_if)

lemma hide_tr_idem_only_if:
    "u --tr X = u \<Longrightarrow> sett u \<subseteq> - (Ev ` X)"
  apply (simp only: hide_tr_to_hidex)
  by (erule hidex_idem_only_if)

lemma hide_tr_idem_iff :
    "u --tr X = u \<longleftrightarrow> sett u \<subseteq> - (Ev ` X)"
  apply (simp only: hide_tr_to_hidex)
  by (rule hidex_idem_iff)




lemma notin_hide_tr_appt_lm :
    "s --tr X = <Ev a> ^^^ t \<longrightarrow> a ~: X"
  apply (induct s rule: induct_trace)
  apply (simp)
  apply (simp)
  apply (simp)
  apply (safe)
  apply (case_tac "aa : X", simp)
  apply (subst (asm) hide_tr_notin, simp, simp)
done


lemma notin_hide_tr_appt:
    "s --tr X = <Ev a> ^^^ t ==> a ~: X"
  apply (insert notin_hide_tr_appt_lm[of s X a t])
by (drule mp, simp, simp)

lemma notin_hide_tr_one :
    "s --tr X = <Ev a> \<Longrightarrow> a ~: X"
  apply (insert notin_hide_tr_appt[of s X a <>])
by (simp)

lemma notin_appt_hide_tr_one :
    "(<Ev a> ^^^ s) --tr X = <Ev a> \<Longrightarrow> a ~: X"
  apply (insert notin_hide_tr_one[of "<Ev a> ^^^ s" X a])
by (assumption)

lemma notin_one_hide_tr_one :
    "<Ev a> --tr X = <Ev a> \<Longrightarrow> a ~: X"
by (rule notin_appt_hide_tr_one[of _ <>], simp)
(*by (erule hide_tr_elims, simp_all)*)




lemma in_hide_tr_appt_lm :
    "(<Ev a> ^^^ s) --tr X = <> \<longrightarrow> a : X"
  apply (induct s rule: induct_trace)
  apply (simp, intro impI)
  apply (subst (asm) hide_tr_nilt_sett, simp add: image_def)
  apply (simp, intro impI)
  apply (subst (asm) hide_tr_nilt_sett, simp add: image_def)
  apply (subst (asm) hide_tr_nilt_sett, simp add: image_def)
done


lemma in_hide_tr_one_if :
    "<Ev a> --tr X = <> \<Longrightarrow> a : X"
by (erule hide_tr_elims, simp_all)

(*lemma hide_tr_one_sett_in_iff:
  "a : X \<Longrightarrow> (s --tr X = <Ev a>) = (s = <>)"
apply (rule iffI)
apply (frule hide_tr_in_one)
apply (drule sym)
apply (frule hide_tr_notin)
done*)


lemma sett_subset_hide_tr_X :
    "(t --tr X = s) \<Longrightarrow> (sett t <= sett s \<union> Ev ` X)"
  apply (induct t arbitrary: X rule: induct_trace)
    apply (simp, drule sym, simp)
    apply (rule)
    apply (simp, drule sym, simp)
    apply (force)
  done

lemma notin_Ev_image : "a \<notin> X \<Longrightarrow> Ev a \<notin> Ev ` X"
by (auto)

lemma hide_tr_notin_only_if_not_subset :
     "sa --tr X = <Ev a> ^^^ s \<Longrightarrow>
      \<not> sett sa \<subseteq> Ev ` X"
  apply (induct sa rule: induct_trace)
  apply (simp_all)
  apply (rule impI)
  apply (case_tac "aa : X", simp)
  apply (simp)
  apply (simp add: image_def)
done


lemma hiding_all_sett : "{s --tr X |s. sett s \<subseteq> Ev ` X} = {<>}"
  apply (simp only: singleton_conv[THEN sym])
  apply (simp only: set_eq_iff)
  apply (rule)
    apply (induct_tac x rule: induct_trace)

    (* <> *)
    apply (simp add: subset_singleton_iff)
    apply (rule_tac x="<>" in exI, simp)

    (* <Tick> *)
    apply (simp)
    apply (intro allI impI)
    apply (simp add: hide_tr_sym)
    apply (simp add: hide_tr_Tick_sett)
    apply (elim exE conjE disjE, simp)

    (* <Ev a> ^^^ s *)
    apply (simp (no_asm))
    apply (intro allI impI)
    apply (simp add: hide_tr_sym)
    apply (simp add: hide_tr_notin_only_if_not_subset)
done




subsection \<open> hide_tr decompo \<close>


lemma hide_tr_decompo_appt_only_if :
  "t --tr X = <Ev a> ^^^ s \<Longrightarrow>
    (\<And>sa aa. t = <Ev aa> ^^^ sa \<Longrightarrow> sa --tr X = <Ev a> ^^^ s \<Longrightarrow> aa \<in> X \<Longrightarrow> P) \<Longrightarrow>
    (\<And>sa. t = <Ev a> ^^^ sa \<Longrightarrow> sa --tr X = s \<Longrightarrow> a \<notin> X \<Longrightarrow> P) \<Longrightarrow> P"
  apply (simp add: hide_tr_to_hidex)
  by (erule hidex_appt_casesE, simp_all)


lemma hide_tr_decompo_appt_if :
    "(EX sa aa. t = <Ev aa> ^^^ sa & sa --tr X = <Ev a> ^^^ s & aa \<in> X)
     | (EX sa. t = <Ev a> ^^^ sa & sa --tr X = s & a \<notin> X) \<Longrightarrow>
      t --tr X = <Ev a> ^^^ s"
  apply (elim disjE exE)
  by (simp add: hide_tr_to_hidex)+


lemma hide_tr_decompo_appt_iff :
    "(t --tr X = <Ev a> ^^^ s) =
       ((EX sa aa. t = <Ev aa> ^^^ sa & sa --tr X = <Ev a> ^^^ s & aa \<in> X)
       | (EX sa. t = <Ev a> ^^^ sa & sa --tr X = s & a \<notin> X))"
  apply (rule)
    apply (erule hide_tr_decompo_appt_only_if, simp_all)
    apply (rule hide_tr_decompo_appt_if, simp_all)
  done




lemma hide_tr_decompo_Ev_appt_only_if:
    "[| u --tr X = <Ev a> ^^^ t |]
     ==> (EX s' t'. (noTick s' | t' = <>) &
                    u = s' ^^^ t' &
                    s' --tr X = <Ev a> & t' --tr X = t)"
  apply (insert hide_tr_decompo_only_if_lm)
  apply (drule_tac x=X in spec)
  apply (drule_tac x=u in spec)
  apply (drule_tac x="<Ev a>" in spec)
  apply (drule_tac x=t in spec)
  apply (simp)
  apply (elim exE)
  apply (rule_tac x=s' in exI)
  apply (rule_tac x=t' in exI)
  apply (simp add: sym)
  done




subsection \<open> hide_tr decompo neq \<close>

subsubsection \<open> if ( --tr in conclusion ) \<close>

lemma hide_tr_decompo_neq_if_noTick:
    "[| noTick s ; 
        ~ (EX s' t'. (noTick s' | t' = <>) &
                      u = s' ^^^ t' &
                      s = s' --tr X & t = t' --tr X) |] ==>
    u --tr X \<noteq> s ^^^ t"
  apply (rule)
  apply (erule notE)
  by (rule hide_tr_decompo_only_if, simp_all)


lemma hide_tr_decompo_neq_Ev_appt_if :
    "~ (EX s' t'. (noTick s' | t' = <>) &
                      t = s' ^^^ t' &
                      <Ev a> = s' --tr X & rs = t' --tr X) \<Longrightarrow>
    t --tr X \<noteq> <Ev a> ^^^ rs"
  apply (rule hide_tr_decompo_neq_if_noTick)
  apply (simp)
  apply (simp)
  done


lemma hide_tr_decompo_neq_Ev_appt_if2 :
    "a \<notin> X  \<Longrightarrow> t \<noteq> <> \<Longrightarrow> t \<noteq> <Tick> \<Longrightarrow>
    (\<forall> a s. t \<noteq> <Ev a> ^^^ s) \<Longrightarrow>
    t --tr X \<noteq> <Ev a> ^^^ s"
  by (simp add: hide_tr_to_hidex notin_hidex_if)


lemma hide_tr_decompo_neq_Ev_appt_if_sett :
    "sett t \<subseteq> insert Tick (Ev ` X) \<Longrightarrow>
    t --tr X \<noteq> <Ev a> ^^^ rs"
  apply (induct t arbitrary: X rs rule: induct_trace)

  apply (simp add: hide_tr_nilt_sett)
  apply (simp add: hide_tr_Tick_sett)

  apply (simp)
  apply (case_tac "a \<in> X")
  apply (clarsimp)
  apply (clarsimp)
  done


subsubsection \<open> only_if ( --tr in assumption ) \<close>


lemma hide_tr_decompo_neq_only_if_noTick :
  "[| noTick s ; u --tr X ~= s ^^^ t |] ==>
   ~ (EX s' t'. (noTick s' | t' = <>) &
                u = s' ^^^ t' &
                s = s' --tr X & t = t' --tr X)"
  apply (rule)
  apply (erule notE)
  by (rule hide_tr_decompo_if, simp_all)


lemma hide_tr_decompo_neq_Ev_appt_only_if :
  "[| u --tr X ~= <Ev a> ^^^ t |] ==>
   ~ (EX s' t'. (noTick s' | t' = <>) &
                u = s' ^^^ t' &
                <Ev a> = s' --tr X & t = t' --tr X)"
  apply (insert noTick_Ev[of a])
  by (erule hide_tr_decompo_neq_only_if_noTick[of "<Ev a>" u X t], simp)



(*TODO hide_tr_decompo_neq_Ev_appt_only_if_sett *)
lemma hide_tr_decompo_neq_Ev_appt_only_if_sett :
    "[| u --tr X ~= <Ev a> ^^^ t |] ==>
     (sett u \<subseteq> insert Tick (Ev ` X)) \<or>  \<not> (\<exists> rs xs. rs ^^^ <Ev a> ^^^ xs --tr X = t)"
  apply (induct u rule: induct_trace)

  apply (simp add: hide_tr_nilt_sett)
  apply (simp add: hide_tr_Tick_sett)

  apply (simp)
  apply (case_tac "aa \<in> X")
  apply (clarsimp)
  apply (simp add: image_def)
  apply (case_tac "aa = a")
  apply (simp)
  apply (rule, rule)
  oops



subsection \<open> hide_tr iff \<close>


lemma nilt_eq_hide_tr_iff:
  "(<> = s --tr X) = (sett s <= Ev ` X)"
apply (rule iffI)
apply (simp add: hide_tr_nilt_sett_only_if)
apply (simp add: hide_tr_nilt_sett_if)
done


(* FIXME CSP-Prover lemma hide_tr_Tick_sett_if is incorrectly referring to <> instead of <Tick>! *)
lemma hide_tr_Tick_sett_if:
  "(EX s'. s = s' ^^^ <Tick> & sett s' <= Ev ` X & noTick s') ==> s --tr X = <Tick>"
apply (elim exE conjE, simp)
by (simp add: hide_tr_nilt_sett_if)


lemma Tick_eq_hide_tr_iff:
  "(<Tick> = s --tr X) = (EX s'. s = s' ^^^ <Tick> & sett s' <= Ev ` X & noTick s')"
apply (rule iffI)
apply (drule sym, simp add: hide_tr_Tick_sett_only_if)
apply (rule sym, simp add: hide_tr_Tick_sett_if)
done


lemma hide_tr_cases_iff :
    "(t --tr X = s) =
       ((s = <> \<longrightarrow> sett t <= Ev ` X)
       & (s = <Tick> \<longrightarrow> (EX s'. t = s' ^^^ <Tick> & sett s' <= Ev ` X & noTick s'))
       & (\<forall> a ss. s = <Ev a> ^^^ ss \<longrightarrow> 
                   (EX sa aa. t = <Ev aa> ^^^ sa & sa --tr X = <Ev a> ^^^ ss & aa \<in> X)
                   | (EX sa. t = <Ev a> ^^^ sa & sa --tr X = ss & a \<notin> X)))"
  apply (induct s rule: induct_trace)
    apply (simp_all)
    apply (simp add: hide_tr_nilt_sett)
    apply (simp add: hide_tr_Tick_sett)
    apply (rule hide_tr_decompo_appt_iff)
  done





lemma Tick_notin_hide_tr_iff:
    "(Tick ~: sett (s --tr X)) = (Tick ~: sett s)"
  by (simp)


lemma Tick_notin_hide_tr_trans1:
    "sa --tr X = s \<Longrightarrow>
    Tick ~: sett s \<Longrightarrow>
    Tick ~: sett sa"
  by (drule sym, simp)

lemma Tick_notin_hide_tr_trans2:
    "sa --tr X = s \<Longrightarrow>
    Tick ~: sett sa \<Longrightarrow>
    Tick ~: sett s"
  by (drule sym, simp)

lemmas Tick_notin_hide_tr_trans = Tick_notin_hide_tr_trans1
                                  Tick_notin_hide_tr_trans2

(*lemma hide_tr_disj :
    "s \<noteq> <> & t \<noteq> <> & s \<noteq> <Tick> & t \<noteq> <Tick> \<Longrightarrow>
     (s --tr {x} = t) \<Longrightarrow> (s --tr (- {x}) ~= t)"
  apply (frule hide_tr_X_sett)
  apply (simp add: image_def)
  apply (rule)
  apply (frule hide_tr_non_x_sett)
  apply (simp add: subset_doubleton_iff)
  apply (elim disjE, simp_all)
  apply (simp add: sett_empty_iff)
  apply (simp add: sett_Tick_iff)
  done*)


lemma hide_tr_singleton_only_if :
    "(s --tr {x} = t) \<Longrightarrow> (s --tr (- {x}) ~= t) \<or> t = <> \<or> t = <Tick>"
  apply (frule hide_tr_X_sett)
  apply (simp add: image_def)
  apply (rule)
  apply (frule hide_tr_non_x_sett)
  apply (simp add: subset_doubleton_iff)
  apply (elim disjE, simp_all)
  apply (simp add: sett_empty_iff)
  apply (simp add: sett_Tick_iff)
  done

lemma hide_tr_Compl_singleton_only_if :
    "(s --tr (- {x}) = t) \<Longrightarrow> (s --tr ({x}) ~= t) \<or> t = <> \<or> t = <Tick>"
  apply (drule hide_tr_non_x_sett)
  apply (simp add: subset_doubleton_iff)
  apply (rule)
  apply (drule hide_tr_X_sett)
  apply (elim disjE)
  apply (simp add: sett_empty_iff)
  apply (simp add: sett_Tick_iff)
  apply (simp)
  apply (simp)
  done


subsection \<open> rest_tr \<close>

lemma hide_tr_rest_tr_sett:
    "sett s <= insert Tick (Ev ` Y) ==>
    ((s --tr X) = (s rest-tr (Y-X)))"
  by (simp add: Trace_hide.hide_tr_rest_tr_sett)

lemma hide_tr_rest_tr_eq:
    "((s --tr X) = (s rest-tr (UNIV - X)))"
  apply (rule hide_tr_rest_tr_sett[of _ UNIV])
  by (simp add: insert_Tick_Ev)

lemma rest_tr_hide_tr_eq:
    "((s rest-tr X) = (s --tr (UNIV - X)))"
  apply (rule sym)
  apply (rule trans, rule Trace_hide.hide_tr_rest_tr_sett[of _ "UNIV"])
  apply (simp add: insert_Tick_Ev)
  by (simp add: Compl_eq_Diff_UNIV[THEN sym])









(*
lemma hide_tr_not_appt_self [simp]:
    "a \<notin> X \<Longrightarrow> \<exists>t. s --tr X = <Ev a> ^^^ t"
  apply (simp add: hide_tr_iff)
  
  apply (induction rule: hidex.induct)



lemma hide_tr_neq :
    "a \<in> X \<Longrightarrow> t --tr X ~= <Ev a> ^^^ s"
proof
  assume "t --tr X = <Ev a> ^^^ s"
  then have "<> --tr X ~= <Ev a> ^^^ s"
    by (simp)
  then have "<Tick> --tr X ~= <Ev a> ^^^ s"
    by (simp)
  then have "s --tr X = s \<longleftrightarrow> sett s \<inter> Ev ` X = {}"
    apply (induct s rule: induct_trace, simp_all)
  then have "(<Ev a> ^^^ s) --tr X ~= <Ev a> ^^^ s"
    by (simp)
  then show False
    using odd_one by blast 
qed
*)


end