theory CSP_T_law_RUN
imports CSP.CSP_RUN
        CSP_T_law_fix
        CSP_T_law_step
        CSP_T_law_ref
begin



section \<open> RUN traces semantics - code from CSPIO \<close>

definition traces_run :: "'a set => 'a domT"
where "traces_run A == Abs_domT (set_run A)"


definition RUNs :: "('a set => ('p,'a) proc) set"
where "RUNs == {Pf. ALL A. traces (Pf A) MT = traces_run A}"


(* ----------------------------------------------- *
                        alpha
 * ---------------------------------------------- *)

definition alphas :: "('p,'a) proc => ('a set) set"
where "alphas == (%P. {A. traces P MT <= traces_run A})"





lemma set_run_domT:
  "set_run A : domT"
apply (simp add: domT_def HC_T1_def)
apply (rule conjI)

(* non empty *)
apply (subgoal_tac "<> : set_run A")
apply (force)
apply (rule set_run.intros)

(* prefix closed *)
apply (simp add: prefix_closed_def)
apply (intro allI impI)
apply (elim conjE exE)
apply (erule set_run_prefixE)
apply (simp)
apply (simp)
apply (simp add: noTick_set_run)
apply (simp)
done




(* ------------------------------ *
        lemmas on traces_run
 * ------------------------------ *)

lemma in_traces_run: 
  "(t :t traces_run A) = (t : set_run A)"
apply (simp add: memT_def traces_run_def)
apply (simp add: Abs_domT_inverse set_run_domT)
done

lemma traces_run_subset:
  "[| A <= B ; t :t traces_run A |] ==> t :t traces_run B"
apply (simp add: in_traces_run)
apply (rule set_run_subset)
apply (rule conjI)
apply (simp)
apply (simp)
done

lemma traces_run_last:
  "[| noTick s ; s ^^^ <e> :t traces_run A |] ==> e : Ev ` A"
apply (simp add: in_traces_run)
apply (simp add: set_run_last)
done

lemma traces_run_ren:
  "[| s [[r]]* t ; s :t traces_run A |] ==> t :t traces_run (ren_set A r)"
apply (simp add: in_traces_run)
apply (rule set_run_ren)
apply (auto)
done

lemma traces_run_hide:
  "t :t traces_run A ==> t --tr X :t traces_run (A - X)"
apply (simp add: in_traces_run)
apply (simp add: set_run_hide)
done

lemma traces_run_par:
  "[| s :t traces_run A ; t :t traces_run B ; u : s |[X]|tr t |]
   ==> u :t traces_run (A Un B)"
apply (simp add: in_traces_run)
apply (rule set_run_par)
apply (auto)
done


lemma traces_run_app:
   "[| s :t traces_run A ; t :t traces_run A |] ==> s ^^^ t :t traces_run A" 
apply (simp add: in_traces_run)
apply (rule set_run_app)
apply (auto)
done


(* ------------------------------ *
        lemmas on RUNs
 * ------------------------------ *)

lemma in_traces_RUNs:
  "P : RUNs ==> (t :t traces (P A) MT) = (t : set_run A)"
apply (simp add: RUNs_def)
apply (simp add: in_traces_run)
done

lemma traces_run_RUNs:
  "P : RUNs ==> traces (P A) MT = traces_run A"
apply (rule order_antisym)
apply (rule)
apply (simp add: in_traces_RUNs)
apply (simp add: in_traces_run)
apply (rule)
apply (simp add: in_traces_RUNs)
apply (simp add: in_traces_run)
done

lemma traces_RUNs_subset:
  "[| P : RUNs ; A <= B ; t :t traces (P A) MT|] ==> t :t traces (P B) MT"
apply (simp add: RUNs_def)
apply (simp add: traces_run_subset)
done


lemma interleave_set_run:
  "u : set_run (X Un Y) 
   = (EX s t. u : s |[{}]|tr t & s : set_run X & t : set_run Y)"
apply (rule iffI)
apply (simp add: interleave_set_run_only_if)
apply (elim conjE exE)
apply (rule interleave_set_run_if)
apply (auto)
done


(* ---------------------------- *
          RUN and hiding
 * ---------------------------- *)

lemma traces_RUNs_hide_lm:
   "ALL t.
     (P : RUNs & t --tr X :t traces (P A) MT)
      --> t :t traces(P(A Un X)) MT"
apply (rule allI)
apply (induct_tac t rule: induct_trace)

(* <> *)
apply (simp)

(* <Tick> *)
apply (simp)
apply (intro impI)
apply (elim conjE exE)
apply (rule traces_RUNs_subset)
apply (simp_all)

(* <Ev a> ^^^ s *)
apply (intro impI)
apply (elim conjE exE)
apply (simp add: in_traces_RUNs)
apply (erule set_run.cases)

 apply (simp)
 apply (drule mp)
 apply (rule set_run.intros)
 apply (elim conjE exE)
 apply (simp add: hide_tr_nilt_sett)
 apply (rule set_run.intros)
 apply (simp)
 apply (simp add: image_iff)

 apply (case_tac "a:X")
  apply (simp)
  apply (drule mp)
  apply (rule set_run.intros)
  apply (simp)
  apply (simp add: image_iff)
  apply (rule set_run.intros)
  apply (simp)
  apply (simp add: image_iff)

 (* a~:X *)
  apply (simp)
  apply (rule set_run.intros)
  apply (simp)
  apply (simp add: image_iff)
done

(* ---------------------------------- *
       traces in RUN with hide
 * ---------------------------------- *)

lemma traces_RUNs_hide:
   "[| P : RUNs ;  t --tr X :t traces (P A) MT ; B = A Un X |]
    ==> t :t traces(P B) MT"
apply (simp add: traces_RUNs_hide_lm)
done



(* ----------------------------------------------- *
            input-completeness & alpha
                    lemmas
 * ----------------------------------------------- *)
(*
lemma complete_on_ref:
  "[| P : RUNs ; complete_on X P |]
   ==> P <=T P X"
apply (simp add: cspT_semantics)
apply (simp add: complete_on_def)
apply (simp add: traces_run_RUNs)
done
*)

lemma alphas_ref:
  "[| R : RUNs ; alpha : alphas P |]
   ==> R alpha <=T P"
apply (simp add: cspT_semantics)
apply (simp add: alphas_def)
apply (simp add: traces_run_RUNs)
done

lemma alpha_subset:
  "[| A <= B; A:alphas P |] ==> B:alphas P"
apply (simp add: alphas_def)
apply (auto)
apply (drule_tac x="t" in spec, simp)
apply (simp add: traces_run_subset)
done

lemma alphas_RUN:
  "[| P : RUNs ; B <= A |] ==> A : alphas (P B)"
apply (simp add: alphas_def)
apply (simp add: traces_run_RUNs)
apply (rule)
apply (simp add: traces_run_subset)
done

lemma alphas_sett_subset[rule_format]:
  "(A : alphas P & t :t traces P MT)
    --> sett t <= (Ev ` A)"
apply (induct_tac t rule: rev_induct_trace)

(* <> *)
apply (simp)

(* <Ev a> ^^^ s *)
apply (intro allI impI)
apply (simp)
apply (elim conjE exE)
apply (drule mp)
 apply (rule memT_prefix_closed)
 apply (simp)
 apply (simp add: prefix_def)
 apply (force)

apply (simp add: alphas_def)
apply (erule subdomTE_ALL)
apply (drule_tac x="s ^^^ <e>" in spec)
apply (simp add: traces_run_last)
done


lemma alphas_traces_sett:
  "[| A : alphas P; s :t traces P MT |]
    ==> sett s <= Ev ` A"
apply (simp add: alphas_def)
apply (rule set_run_sett)
apply (simp add: in_traces_run[THEN sym])
apply (auto)
done

lemma alphas_traces_noTick:
  "[| A : alphas P; s :t traces P MT |]
    ==> noTick s"
apply (rule noTick_set_run[of _ A])
apply (simp add: alphas_def)
apply (simp add: in_traces_run[THEN sym])
apply (auto)
done

(* -------------------- *
          par
 * -------------------- *)

lemma par_tr_all_sync_only_if[rule_format]:
  "ALL s t.
   sett s <= (Ev ` A) & sett t <= (Ev ` A) & u : s |[A]|tr t
   --> s = u & t = u"
apply (induct_tac u rule: induct_trace)

(* <> *)
apply (simp)

(* <Tick> *)
apply (simp)

(* <Ev a> *)
apply (intro allI impI)
apply (simp add: par_tr_head)
apply (elim disjE conjE exE)

(* sync *)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="t'" in spec)
 apply (simp)

apply (simp_all add: image_iff)
done

lemma par_tr_all_sync_if[rule_format]:
  "(sett s <= (Ev ` A) & sett t <= (Ev ` A))
   --> t : t |[A]|tr t"
apply (induct_tac t rule: rev_induct_trace)

(* <> *)
apply (simp)

(* <Ev a> *)
apply (intro allI impI)
apply (simp add: par_tr_last)
apply (elim disjE conjE exE)

apply (rule_tac x="sa" in exI)
apply (rule_tac x="sa" in exI)
apply (simp)
done

lemma par_tr_all_sync:
  "[| sett s <= (Ev ` A) ; sett t <= (Ev ` A) |]
  ==> u : s |[A]|tr t = (s = u & t = u)"
apply (rule iffI)
apply (rule par_tr_all_sync_only_if[of _ A])
apply (simp)
apply (simp add: par_tr_all_sync_if)
done

(* full sync para *)

lemma traces_parallel_all_sync_only_if:
  "[| A : alphas P ; A : alphas Q ; t :t traces(P |[A]| Q) MT |]
   ==> t :t traces P MT & t :t traces Q MT"
apply (simp add: in_traces)
apply (elim conjE exE)

apply (subgoal_tac "s = t & ta = t")
apply (simp)

apply (rule par_tr_all_sync_only_if)
apply (rule conjI)
apply (rule alphas_sett_subset)
apply (rule conjI)
apply (simp)
apply (simp)

apply (rule conjI)
apply (rule alphas_sett_subset)
apply (rule conjI)
apply (rotate_tac 1)
apply (simp)

apply (simp)
apply (simp)
done

lemma traces_parallel_all_sync_if:
  "[| A : alphas P ; A : alphas Q ; t :t traces P MT & t :t traces Q MT |]
   ==> t :t traces(P |[A]| Q) MT"
apply (simp add: in_traces)
apply (elim conjE exE)
apply (rule_tac x="t" in exI)
apply (rule_tac x="t" in exI)
apply (simp)

apply (rule par_tr_all_sync_if)
apply (rule conjI)
apply (rule alphas_sett_subset)
apply (rule conjI)
apply (simp)
apply (simp)

apply (rule alphas_sett_subset)
apply (rule conjI)
apply (simp)
apply (simp)
done

lemma traces_parallel_all_sync:
  "[| A : alphas P ; A : alphas Q |]
   ==> t :t traces(P |[A]| Q) MT = (t :t traces P MT & t :t traces Q MT)"
apply (rule iffI)
apply (simp add: traces_parallel_all_sync_only_if)
apply (simp add: traces_parallel_all_sync_if)
done

lemma traces_par_sync_decompo:
  "[| A1 : alphas P ; A2 : alphas Q ; A1 <= A ; A2 <= A |]
   ==> t :t traces(P |[A]| Q) MT = (t :t traces P MT & t :t traces Q MT)"
apply (rule traces_parallel_all_sync)
apply (simp_all add: alpha_subset)
done

(* -------------------------- *
 |          Lemma 3           |
 * -------------------------- *)

lemma parallel_refinement_all_sync:
  "[| X : alphas P ; X : alphas Q |] ==>
   P <=T Q |[X]| P"

apply (simp add: cspT_semantics)
apply (rule subdomTI)
apply (simp add: traces_parallel_all_sync)
done


(* ---------------------------- *)

lemma par_tr_all_sync_in[rule_format]:
  "sett s <= (Ev ` A) --> s : s |[A]|tr s"
apply (induct_tac s rule: induct_trace)

(* <> *)
apply (simp)

(* <Tick> *)
apply (simp)

(* <Ev a> *)
apply (intro allI impI)
apply (simp add: par_tr_head)
apply (elim disjE conjE exE)
apply (simp add: image_iff)
done


(* --- ren --- *)

lemma alphas_ren:
  "A : alphas P ==> ren_set A r : alphas (P[[r]])"
apply (simp add: alphas_def)
apply (rule)
apply (simp add: in_traces)
apply (elim conjE exE)
apply (erule subdomTE_ALL)
apply (drule_tac x="s" in spec)
apply (simp)
apply (simp add: traces_run_ren)
done

lemma alphas_ren_sub:
  "[| A : alphas P ; ren_set A r <= C |] ==> C : alphas (P[[r]])"
apply (insert alphas_ren[of A P r])
apply (rule alpha_subset)
apply (simp (no_asm_simp))
apply (simp)
done

(* --- hide --- *)

lemma alphas_hide:
  "A : alphas P ==> A - X : alphas (P -- X)"
apply (simp add: alphas_def)
apply (rule)
apply (simp add: in_traces)
apply (elim conjE exE)
apply (simp)
apply (erule subdomTE_ALL)
apply (drule_tac x="s" in spec)
apply (simp)
apply (simp add: traces_run_hide)
done

lemma alphas_hide_sub:
  "[| A : alphas P ; A - X <= C |] ==> C : alphas (P -- X)"
apply (insert alphas_hide[of A P X])
apply (rule alpha_subset)
apply (simp (no_asm_simp))
apply (simp)
done

(* --- par --- *)

lemma alphas_par:
  "[| A : alphas P ; B : alphas Q |] ==> A Un B : alphas (P |[X]| Q)"
apply (simp add: alphas_def)
apply (rule)
apply (simp add: in_traces)
apply (elim conjE exE)
apply (erule subdomTE_ALL)
apply (erule subdomTE_ALL)
apply (drule_tac x="s" in spec)
apply (drule_tac x="ta" in spec)
apply (simp)
apply (simp add: traces_run_par)
done

lemma alphas_par_sub:
  "[| A : alphas P ; B : alphas Q ; A Un B <= C|] ==> C : alphas (P |[X]| Q)"
apply (insert alphas_par[of A P B Q X])
apply (rule alpha_subset)
apply (simp (no_asm_simp))
apply (simp)
done


lemma cspT_interleave_RUN_Un:
  "P : RUNs ==> P X ||| P Y =T P (X Un Y)"
apply (simp add: cspT_semantics)
apply (rule order_antisym)

(* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE)
 apply (simp add: in_traces_RUNs)
 apply (simp add: interleave_set_run)
 apply (force)

(* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (simp add: in_traces_RUNs)
 apply (simp add: interleave_set_run)
done

(* --- stop --- *)

lemma alphas_STOP: "A : alphas STOP"
apply (simp add: alphas_def)
apply (auto)
apply (simp add: in_traces)
done

(* --- choice --- *)

lemma alphas_choice:
  "[| A : alphas P ; B : alphas Q |] ==> A Un B : alphas (P [+] Q)"
apply (simp add: alphas_def)
apply (rule)
apply (simp add: in_traces)
apply (erule subdomTE_ALL)
apply (erule subdomTE_ALL)
apply (drule_tac x="t" in spec)
apply (drule_tac x="t" in spec)
apply (erule disjE)
apply (simp_all)
apply (rule traces_run_subset)
apply (simp_all)
apply (rule traces_run_subset)
apply (simp_all)
done

lemma alphas_choice_sub:
  "[| A : alphas P ; B : alphas Q ; A Un B <= C|] ==> C : alphas (P [+] Q)"
apply (insert alphas_choice[of A P B Q])
apply (rule alpha_subset)
apply (simp (no_asm_simp))
apply (simp)
done


(* --------------------------------------------------------- *
                 preliminary for CSPIO
 * --------------------------------------------------------- *)

definition tr_after_set :: "'a domT => 'a trace => 'a trace set"
where "tr_after_set T s == {t. s ^^^ t :t T & (noTick s | t = <>)}"

definition tr_after :: "'a domT => 'a trace => 'a domT" ("_ afterTr _" [1000,1000] 1000)
where "T afterTr s == Abs_domT (tr_after_set T s)"

definition tr_initials :: "'a domT => 'a set"
where "tr_initials T == {a. EX t. t :t T & t~=<> & hdt(t) = Ev a}"

definition tr_initials_after :: "'a domT => 'a trace => 'a set"
where "tr_initials_after T s == if s :t T then (tr_initials (T afterTr s)) else {}"


(* --------------------------- *
            lemmas
 * --------------------------- *)

lemma tr_initials_Ev:
  "tr_initials T = {a. <Ev a> :t T}"
apply (simp add: tr_initials_def)
apply (auto)
apply (rule memT_prefix_closed)
apply (simp)
apply (simp add: prefix_def)
apply (rule_tac x="tlt t" in exI)
apply (rotate_tac -1)
apply (drule sym)
apply (simp)
done


lemma tr_after_set_in_domT:
  "[| noTick s ; s :t T |] ==> tr_after_set T s : domT"
apply (simp add: domT_def HC_T1_def)
apply (rule conjI)

(* non empty *)
 apply (simp add: tr_after_set_def)
 apply (rule_tac x="<>" in exI)
 apply (simp)

(* prefix closed *)
 apply (simp add: tr_after_set_def)
 apply (simp add: prefix_closed_def)
 apply (auto)
 apply (simp add: prefix_def)
 apply (auto)
 apply (simp add: appt_assoc[THEN sym])
 apply (rule memT_prefix_closed)
 apply (rotate_tac -2)
 apply (simp)
 apply (simp add: prefix_def)
 apply (auto)
done

lemma in_tr_after:
  "[| noTick s ; s :t T |] ==> (t :t T afterTr s) = (t : tr_after_set T s)"
apply (simp (no_asm_simp) add: memT_def tr_after_def)
apply (simp add: Abs_domT_inverse tr_after_set_in_domT)
done


(* a lemma for Theorem 1 *)

lemma tr_initials_after_set:
  "noTick s ==> (tr_initials_after T s) = {a. s^^^<Ev a> :t T}"
apply (rule equalityI)

(* <= *)
 apply (rule subsetI)
 apply (simp add: tr_initials_after_def)
 apply (case_tac "s :t T")
  apply (simp)
  apply (simp add: tr_initials_def)
  apply (simp add: in_tr_after)
  apply (simp add: tr_after_set_def)
  apply (elim conjE exE)
  apply (rule memT_prefix_closed)
  apply (rotate_tac 2)
  apply (simp)
  apply (simp add: prefix_def)
  apply (simp add: appt_assoc)
  apply (rule_tac x="tlt t" in exI)
  apply (rotate_tac -1)
  apply (drule sym)
  apply (simp)

 (* s ~:t T *)
 apply (simp)

(* => *)
 apply (rule subsetI)
 apply (simp add: tr_initials_after_def)
 apply (rule conjI)

  apply (intro allI impI)
  apply (simp add: tr_initials_def)
  apply (simp add: in_tr_after)
  apply (simp add: tr_after_set_def)
  apply (rule_tac x="<Ev x>" in exI)
  apply (simp)

  apply (rule memT_prefix_closed)
  apply (simp)
  apply (simp add: prefix_def)
  apply (force)
done


lemma tr_initials_after_RUN:
  "[| P : RUNs ; s : set_run A |]
   ==> tr_initials_after (traces (P A) MT) s = A"
apply (subgoal_tac "noTick s")
apply (rule equalityI)

 apply (rule subsetI)
 apply (simp add: tr_initials_after_set)
 apply (simp add: in_traces_RUNs)
 apply (subgoal_tac "sett (s ^^^ <Ev x>) <= (Ev ` A)")
 apply (force)
 apply (rule set_run_sett)
 apply (simp)

 apply (rule subsetI)
 apply (simp add: tr_initials_after_set)
 apply (simp add: in_traces_RUNs)
 apply (rule set_run_app)
 apply (simp)
 apply (rule set_run_one)
 apply (simp)

apply (simp add: noTick_set_run)
done

(* ----------------------------------------------- *
                   no Tick Proc 
      non-observationally terminating process
 * ----------------------------------------------- *)

definition noTickPr :: "('p,'a) proc => bool"
where "noTickPr == (%P. ALL t. t :t traces(P) MT --> noTick t)"

(* lemmas for non-observationally terminating process *)

lemma noTickPr_noTick:
  "[| noTickPr P ; t :t traces(P) MT |] ==> noTick t"
apply (simp add: noTickPr_def)
done

lemma alphas_noTickPr:
  "A:alphas P ==> noTickPr P"
apply (simp add: noTickPr_def)
apply (intro strip)
apply (simp add: noTick_def)
apply (subgoal_tac "sett t <= (Ev ` A)")
apply (force)

apply (rule alphas_sett_subset)
apply (auto)
done

lemma noTickPr_RUN:
  "P : RUNs ==> noTickPr (P A)"
apply (rule alphas_noTickPr[of A])
apply (simp add: alphas_RUN)
done





section \<open> RUN semantics \<close>

lemmas Run_domT = Ext_pre_choice_domT


subsubsection \<open> traces RUN \<close>


lemma cspT_Run :
    "(($Run A)::('e RunName, 'e) proc) =T (((Runfun (Run A)))::('e RunName, 'e) proc)"
by (rule cspT_unwind, simp_all)


lemma traces_Run :
    "traces ($Run A) MT = traces (? a:A -> $Run A) MT"
  apply (insert cspT_Run)
by (simp add: cspT_eqT_semantics)



subsection \<open> in traces Run S \<close>


lemma traces_included_in_Run_lm :
    "noTick t & sett t \<subseteq> Ev ` S -->
     t :t traces ((FIX Runfun) (Run S)) M"
  apply (induct_tac t rule: induct_trace)

  (* <> *)
    apply (intro impI conjI)
    apply (simp add: FIX_def in_traces)

  (* <Tick> *)
    apply (simp)

  (* <Ev a> ^^^ s *)
    apply (simp)
    apply (intro impI)
    apply (simp)
    apply (elim conjE)
    apply (simp add: FIX_def in_traces)

    apply (elim disjE exE)

    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_traces)
    apply (simp add: image_def)

    apply (rule_tac x="Suc n" in exI)
    apply (simp add: FIXn_def Subst_procfun_prod_def in_traces)
    apply (simp add: image_def)
done

lemma traces_included_in_Run :
    "[| noTick t ; sett t \<subseteq> Ev ` S |] ==>
     t :t traces ((FIX Runfun) (Run S)) M"
by (simp add: traces_included_in_Run_lm)



lemma Tickt_notin_traces_included_in_Run :
    "<Tick> ~:t traces ((FIX Runfun) (Run S)) M"
  apply (simp add: FIX_def in_traces)
  apply (intro allI)
  apply (case_tac n)
  apply (simp add: FIXn_def Subst_procfun_prod_def in_traces)
  apply (simp add: FIXn_def Subst_procfun_prod_def in_traces)
done



subsection \<open> $Run {} =T STOP \<close>


lemma cspT_Run_STOP : "(($Run {})::('a RunName,'a) proc) =T STOP"
  apply (rule cspT_rw_left, rule cspT_unwind)
  apply (simp, simp)
  apply (simp add: cspT_semantics)
  apply (simp add: traces_iff)
done



subsection \<open> RUN {} =T STOP \<close>


lemma cspT_RUN_STOP : "RUN {} =T STOP"
by (simp add: RUN_def, rule cspT_Run_STOP)



subsection \<open> $Run {} =T DIV \<close>


lemma cspT_Run_DIV : "(($Run {})::('a RunName,'a) proc) =T DIV"
  apply (rule cspT_rw_left, rule cspT_unwind)
  apply (simp, simp)
  apply (simp add: cspT_semantics)
  apply (simp add: traces_iff)
done


subsection \<open> RUN {} =T DIV \<close>


lemma cspT_RUN_DIV : "RUN {} =T DIV"
by (simp add: RUN_def, rule cspT_Run_DIV)




subsection \<open> $Run S <=T DIV \<close>


lemma cspT_Run_ref_DIV : "(($Run S)::('a RunName,'a) proc) <=T DIV"
by (rule cspT_top)



subsection \<open> $Run S <=T STOP \<close>


lemma cspT_Run_ref_STOP : "(($Run S)::('a RunName,'a) proc) <=T STOP"
by (rule cspT_top)



subsection \<open> ~ $Run S <=T SKIP \<close>


lemma not_cspT_Run_SKIP : "~ (($Run S)::('a RunName,'a) proc) <=T SKIP"
  apply (rule notI)

  apply (erule cspT_rw_leftE)
  apply (rule cspT_FIX[of Runfun], simp_all)
  apply (simp add: cspT_semantics)

  apply (simp add: subdomT_iff in_traces)
  apply (simp add: Tickt_notin_traces_included_in_Run)
done


end