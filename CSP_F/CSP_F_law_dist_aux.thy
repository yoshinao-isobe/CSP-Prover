           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory CSP_F_law_dist_aux
imports CSP_F
begin



lemma singleton_neq_butlast : "x \<notin> set (butlast y) \<and> x \<in> set y \<Longrightarrow> [x] \<noteq> butlast y"
  by (induct y, simp_all, force)

lemma neq_TickrmTick [simp]: "<Tick> \<noteq> rmTick (s)"
  apply (induct s)
  apply (simp add: rmTick_def sett_def Abs_trace_inverse trace_def butlastt_def)
  apply (rule)
   apply (simp add: noTick_def sett_def Abs_trace_inverse trace_def Abs_trace_inject)
   apply (case_tac y, simp, simp)
   apply (simp add: noTick_def sett_def Abs_trace_inverse trace_def)

   apply (simp add: Abs_trace_inject)
   apply (rule, rule singleton_neq_butlast, simp)
  done



lemma nilt_eq_appt : "noTick s \<or> t = <> \<Longrightarrow> <> = s ^^^ t \<longleftrightarrow> s = <> \<and> t = <>"
  apply (simp (no_asm) add: Abs_trace_inverse trace_def nilt_def)
  apply (simp add: Abs_trace_inject trace_def appt_def)
  apply (rule trans)
   apply (rule Abs_trace_inject trace_def, simp) 
   apply (rule Rep_compo_app_in_trace, simp)
   apply (rule, rule)
   apply (case_tac s, simp_all add: Abs_trace_inverse trace_def)
   apply (case_tac t, simp_all add: Abs_trace_inverse trace_def)
  done


lemma appt_decompo_Tick:
  "noTick s
   ==> (<Tick> = s ^^^ t) = (s = <> & t = <Tick>)"
  apply (induct s)
   apply (simp add: noTick_def sett_def nilt_def Abs_trace_inverse Abs_trace_inject)
   by (auto)

lemma noTick_Tick_eq_appt [simp]: "(noTick x \<and> <Tick> = x ^^^ xa) \<longleftrightarrow> (x = <> \<and> xa = <Tick>)"
  apply (rule trans, rule conj_cong, rule refl)
  apply (simp_all add: appt_decompo_Tick noTick_def sett_def)
  apply (induct_tac x)
  apply (simp add: Abs_trace_inverse nilt_def trace_def Abs_trace_inject appt_def noTick_def sett_def)
  apply (simp add: eq_commute)
  by (auto)


lemma Tick_eq_appt_and_and_noTick [simp]:
    "(<Tick> = s ^^^ t \<and> (P \<and> (Q \<and> noTick s))) \<longleftrightarrow> (s = <> \<and> t = <Tick> \<and> P \<and> Q)"
  apply (rule trans, rule conj_cong, rule refl)
  apply (rule trans, rule conj_assoc[THEN sym], rule conj_commute)
  apply (rule trans, rule conj_left_commute)
  apply (rule trans, rule conj_assoc[THEN sym])
  by (simp)


lemma noTick_nilt_appt [simp]:
    "(noTick s \<and> <> = s ^^^ t) \<longleftrightarrow> (<> = s \<and> <> = t)"
  apply (induct s)
  apply (induct t)
  apply (simp only: Abs_trace_inverse trace_def Abs_trace_inject appt_def noTick_def sett_def)
  apply (rule trans, simp only: nilt_def)
  apply (rule trans, rule conj_cong, rule refl, rule Abs_trace_inject)
    apply (simp add: trace_def)
    apply (rule decompo_app_in_trace_if, simp)
    apply (simp add: trace_def)
    apply (simp add: nilt_def Abs_trace_inject Abs_trace_inverse trace_def)
  apply (simp add: eq_commute)
  by (auto)


lemma nilt_appt_noTick :
    "(<> = s ^^^ t \<and> noTick s) \<longleftrightarrow> (<> = s \<and> <> = t)"
  by (simp only: conj_commute noTick_nilt_appt)


lemma nilt_appt_and_and_noTick2 [simp]:
    "(<> = s ^^^ t \<and> (P \<and> (Q \<and> noTick s))) \<longleftrightarrow> (<> = s \<and> <> = t \<and> P \<and> Q)"
  apply (rule trans, rule conj_cong, rule refl)
  apply (rule trans, rule conj_assoc[THEN sym], rule conj_commute)
  apply (rule trans, rule conj_left_commute)
  apply (rule trans, rule conj_assoc[THEN sym])
  by (simp)


lemma traces_Seq_compo_iff :
    "traces (P ;; Q) M =
     {u. (\<exists>s. u = rmTick s \<and> s :t traces P M) \<or> (\<exists>s t. u = s ^^^ t \<and> s ^^^ <Tick> :t traces P M \<and> t :t traces Q M \<and> noTick s)}t"
  by (simp add: traces.simps)



lemma failures_Ext_choice_iff :
    "failures (P [+] Q) M =
     {(f::'a trace \<times> 'a event set).
     (\<exists>X::'a event set. f = (<>, X)) \<and> f :f failures P M \<and> f :f failures Q M \<or>
     (\<exists>s::'a trace. (\<exists>X::'a event set. f = (s, X)) \<and> (f :f failures P M \<or> f :f failures Q M) \<and> s \<noteq> <>) \<or>
     (\<exists>X::'a event set. f = (<>, X) \<and> (<Tick> :t traces P (fstF \<circ> M) \<or> <Tick> :t traces Q (fstF \<circ> M)) \<and> X \<subseteq> Evset)}f"
  by (simp add: failures.simps)



lemma failures_Seq_compo_iff :
    "failures (P ;; Q) M =
         {f. (\<exists>(t::'b trace) X::'b event set. f = (t, X) \<and> (t, insert Tick X) :f failures P M \<and> noTick t) \<or>
             (\<exists>(s::'b trace) (t::'b trace) X::'b event set. f = (s ^^^ t, X) \<and> s ^^^ <Tick> :t traces P (fstF \<circ> M) \<and> (t, X) :f failures Q M \<and> noTick s)}f"
  by (simp add: failures.simps)




lemma temp : "(\<lambda>f. (\<exists>X. f = (<>, X)) \<and> f :f failures P1 M \<and> f :f failures P2 M \<or>
           (\<exists>s. (\<exists>X. f = (s, X)) \<and> (f :f failures P1 M \<or> f :f failures P2 M) \<and> s \<noteq> <>) \<or>
           (\<exists>X. f = (<>, X) \<and> (<Tick> :t traces P1 (fstF \<circ> M) \<or> <Tick> :t traces P2 (fstF \<circ> M)) \<and> X \<subseteq> Evset))
           = (\<lambda>f.
           (\<exists>X. ((f = (<>, X)) \<and> f :f failures P1 M \<and> f :f failures P2 M)
              \<or> (f = (<>, X) \<and> (<Tick> :t traces P1 (fstF \<circ> M) \<or> <Tick> :t traces P2 (fstF \<circ> M)) \<and> X \<subseteq> Evset))
           \<or> (\<exists>s. (\<exists>X. f = (s, X)) \<and> (f :f failures P1 M \<or> f :f failures P2 M) \<and> s \<noteq> <>))"
  by (auto)

lemma temp2 : "P = Q \<Longrightarrow> (a, b) :f {f. P f}f \<longleftrightarrow> (a, b) :f {f. Q f}f"
  by (auto)

lemma temp3 : "((\<exists>t X. f = (t, X) \<and> (t, insert Tick X) :f failures P M \<and> noTick t) \<or>
                         (\<exists>s t X. f = (s ^^^ t, X) \<and> s ^^^ <Tick> :t traces P (fstF \<circ> M) \<and> (t, X) :f failures Q M \<and> noTick s))
               = (\<exists>X s. (f = (s, X) \<and> noTick s \<and> (s, insert Tick X) :f failures P M) \<or>
                         (\<exists>t. noTick s \<and> f = (s ^^^ t, X) \<and> s ^^^ <Tick> :t traces P (fstF \<circ> M) \<and> (t, X) :f failures Q M))"
  by (auto)

lemma temp5 : "Collect P : setF \<Longrightarrow> Collect Q : setF \<Longrightarrow>
               (f :f {f. P f}f \<or>
                f :f {f. Q f}f)
               = (f :f {f. P f \<or> Q f }f)"
  apply (simp add: memF_def)
  apply (rule trans, rule Un_iff[THEN sym])
  apply (simp add: setF_UnF_Rep[THEN sym])
  apply (simp add: UnionF_def)
  by (simp add: Un_def Abs_setF_inverse setF_def)

lemma temp6 : "Collect P : setF \<Longrightarrow> Collect Q : setF \<Longrightarrow>
               (f :f {f. P f}f \<and>
                f :f {f. Q f}f)
               = (f :f {f. P f \<and> Q f }f)"
  apply (simp add: memF_def)
  apply (rule trans, rule Int_iff[THEN sym])
  apply (simp add: setF_IntF_Rep[THEN sym])
  apply (simp add: InterF_def)
  by (simp add: Int_def Abs_setF_inverse setF_def)


lemma setF_UnF_Or:
    "Collect P : setF \<Longrightarrow> Collect Q : setF \<Longrightarrow>
     ({f. P f}f UnF {f. Q f}f) = Abs_setF ({f. P f \<or> Q f})"
  by (simp add: UnionF_def Un_def Abs_setF_inverse)


lemma zzz : "\<And>f. ((\<exists>X. f = (<>, X)) \<and>
            f :f {f. (\<exists>t X. f = (t, X) \<and> (t, insert Tick X) :f failures P1 M \<and> noTick t) \<or> (\<exists>s t X. f = (s ^^^ t, X) \<and> s ^^^ <Tick> :t traces P1 (fstF \<circ> M) \<and> (t, X) :f failures Q M \<and> noTick s)}f \<and>
            f :f {f. (\<exists>t X. f = (t, X) \<and> (t, insert Tick X) :f failures P2 M \<and> noTick t) \<or> (\<exists>s t X. f = (s ^^^ t, X) \<and> s ^^^ <Tick> :t traces P2 (fstF \<circ> M) \<and> (t, X) :f failures Q M \<and> noTick s)}f)
           = (\<exists>X. f = (<>, X) \<and> (
            f :f {f. (\<exists>t X. f = (t, X) \<and> (t, insert Tick X) :f failures P1 M \<and> noTick t) \<or> (\<exists>s t X. f = (s ^^^ t, X) \<and> s ^^^ <Tick> :t traces P1 (fstF \<circ> M) \<and> (t, X) :f failures Q M \<and> noTick s)}f \<and>
            f :f {f. (\<exists>t X. f = (t, X) \<and> (t, insert Tick X) :f failures P2 M \<and> noTick t) \<or> (\<exists>s t X. f = (s ^^^ t, X) \<and> s ^^^ <Tick> :t traces P2 (fstF \<circ> M) \<and> (t, X) :f failures Q M \<and> noTick s)}f))"
  by (simp)



lemma nilt_X_in_failures : "X \<subseteq> Evset \<Longrightarrow> <Tick> :t traces P (fstF \<circ> M) \<Longrightarrow> ((<>, X) :f failures(P) M)"
 apply (rule proc_F2_F4)
 apply (simp_all)
  done



(*declare [[show_main_goal]]*)
lemma cspF_Seq_compo_Ext_dist:
  "(P1 [+] P2) ;; Q =F[M,M]
     (P1 ;; Q) [+] (P2 ;; Q)"
  apply (simp add: cspF_cspT_semantics)
  apply (simp add: cspT_Seq_compo_Ext_dist)
  apply (simp add: failures_iff in_traces)
  apply (rule set_CollectF_eq, rule Collect_cong)

  (* LEFT *)
  apply (rule trans)
   apply (rule trans, rule disj_cong, rule ex_comm, rule ex_rot_r)
   apply (rule trans, rule disj_cong)
     apply (rule ex_cong1)
     apply (rule trans, rule ex_cong1, rule conj_cong, rule refl)
     apply (rule trans, rule conj_cong)
      apply (rule CollectF_open_memF, rule failures_setF, rule refl)
     apply (rule trans, rule conj_cong)
      apply (rule disj_left_commute[THEN sym], rule refl)
      apply (rule trans, rule conj_commute)
      apply (rule conj_cong, rule refl)
       apply (rule disj_cong)
        apply (rule trans, rule ex_cong1, rule conj_cong)
        apply (rule trans, rule ex_cong1)
        apply (rule trans, simp)
        apply (rule conj_commute, rule trans, rule simp_thms, rule refl)
        apply (rule refl)
        apply (rule simp_thms)
        apply (rule trans, simp add: Evset_def)
     apply (rule refl)
     apply (rule refl)
     apply (rule refl)
     apply (rule ex_disj_distrib[THEN sym])
       apply (rule trans, rule ex_cong1, rule ex_disj_distrib[THEN sym])

   apply (simp only: in_failures_disj in_failures_conj)


  (* RIGHT *)
  apply (rule sym, rule trans)
  (* A f \<or> (B f) \<or> C f) *)
  apply (rule trans, rule disj_cong)
     (* A f *)
     apply (rule trans, rule ex_simps[THEN sym], rule ex_cong)
      apply (rule trans, rule conj_cong)
       apply (rule CollectF_open_memF, rule failures_setF)
       apply (rule CollectF_open_memF, rule failures_setF)
      apply (rule trans, rule conj_cong)
       apply (simp)
       apply (simp)
      apply (rule refl)
   (* (B f \<or> C f) *)
   apply (rule trans, rule disj_cong)
    (* B f *)
    apply (rule trans, rule ex_cong1)
     apply (rule trans, rule ex_simps[THEN sym], rule ex_cong)
     apply (rule trans, rule conj_cong)
      apply (rule trans, rule disj_cong)
       apply (rule CollectF_open_memF, rule failures_setF)
       apply (rule CollectF_open_memF, rule failures_setF)
      apply (rule trans, rule disj_cong)
       apply (simp)
       apply (simp)
        (* G f \<or> H f *)
      apply (rule trans, rule disj_left_commute[THEN sym])
       apply (rule trans, rule disj_assoc[THEN sym])
       apply (rule trans, rule disj_cong)
       apply (rule disj_assoc[THEN sym], rule refl)
       apply (rule trans, rule disj_assoc)
       apply (rule trans, rule disj_cong)
        apply (rule disj_commute)
        apply (rule trans, rule ex_disj_distrib[THEN sym])
         apply (rule trans, rule ex_cong1, rule ex_disj_distrib[THEN sym])
         apply (rule trans, rule ex_cong1, rule ex_cong1)
         apply (rule trans, rule conj_disj_distribL[THEN sym])
         apply (rule trans, rule conj_cong, rule refl)
        apply (rule trans, rule conj_disj_distribR[THEN sym])
       apply (rule refl)
       apply (rule refl)
       apply (rule refl)
       apply (rule refl)
       apply (rule refl)
       apply (rule refl)
      apply (rule ex_comm)
       apply (rule refl)
       apply (rule disj_commute)
       apply (rule disj_assoc[THEN sym])
       apply (rule trans, rule disj_cong)
        apply (rule ex_disj_distrib[THEN sym])
        apply (rule refl)
     apply (rule trans, rule ex_disj_distrib[THEN sym])
    apply (rule sym)

  (* CONGRUENCE *)
  apply (rule ex_cong1)

  oops


end