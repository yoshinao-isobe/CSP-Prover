           (*-------------------------------------------*
            |                  DFtickA X                |
            |                                           |
            |                 2022 / 2023               |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_DFtickA
imports DFP_Deadlock
begin


(*****************************************************************

         1. The most abstract deadlockfree process DFtick

 *****************************************************************)

declare csp_prefix_ss_def[simp]

(* TODO: move to CSP_F *)
lemma non_memF_F2:
    "[| (s,Y) ~:f F ; Y <= X |] ==> (s,X) ~:f F"
  apply (erule contrapos_nn)
  by (simp add: memF_F2)



section \<open> DFtickA specification \<close>

datatype ('e) DFtickName = DFtickA "'e set"


primrec
  DFtickfun ::  "('e DFtickName, 'e) pnfun"
where
  "DFtickfun (DFtickA A) = (! x:A ->  $(DFtickA A)) |~| SKIP "


overloading Set_DFtickfun == 
  "PNfun :: ('e DFtickName, 'e) pnfun"
begin
  definition "PNfun :: ('e DFtickName, 'e) pnfun == DFtickfun"
end
  
declare Set_DFtickfun_def [simp]



lemma guardedfun_DFtick[simp]:
      "guardedfun DFtickfun"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp_all)




subsection \<open> syntactical approach --> semantical approach \<close>


(*** sub ***)
lemma DFtickA_unwindT :
    "(($DFtickA A)::('e DFtickName, 'e) proc) =T
     ((DFtickfun (DFtickA A))::('e DFtickName, 'e) proc)"
by (cspT_unwind)

lemma traces_DFtickA :
    "traces (($DFtickA A)::('e DFtickName, 'e) proc) MT = 
     traces ((DFtickfun (DFtickA A))::('e DFtickName, 'e) proc) MT"
  apply (insert DFtickA_unwindT[of A])
by (simp add: cspT_semantics)

lemma MT_DFtickA :
    "MT (DFtickA A) = traces (($DFtickA A)::('e DFtickName, 'e) proc) MT"
  apply (insert DFtickA_unwindT[of A])
  apply (simp add: cspT_semantics)
  apply (simp add: traces_iff)
done

lemma fstF_MF_DFtickA :
    "fstF (MF (DFtickA A)) = traces (($DFtickA A)::('e DFtickName, 'e) proc) (fstF \<circ> MF)"
  apply (insert DFtickA_unwindT[of A])
  apply (simp add: cspF_eqF_semantics)
  apply (simp add: traces_iff)
done

lemma in_traces_DFtickA_prefix_closed :
    "(t = <> \<or> (\<exists>a\<in>A. t = <> \<or> (\<exists>s. t = <Ev a> ^^^ s \<and> s :t traces ($DFtickA A) MT)) \<or> t = <Tick>) =
     (t :t traces ($DFtickA A) MT)"
  apply (induct t rule: induct_trace)

  (* <> *)  
  apply (simp)
  
  (* <Tick> *)
  apply (simp add: traces_DFtickA)
  apply (simp add: in_traces)
  
  (* <Ev a> ^^^ s *)
  apply (simp add: traces_DFtickA)
  apply (rule sym, rule trans)
  apply (simp add: in_traces)
  apply (simp add: MT_DFtickA)
  apply (simp add: traces_DFtickA)
done


lemma in_traces_DFtickA_iff_sett :
    "t :t traces (($DFtickA A)::('e DFtickName, 'e) proc) MT = 
     (sett t \<subseteq> insert Tick (Ev ` A))"
  apply (induct t rule: induct_trace)

  (* <> *)  
  apply (simp)
  
  (* <Tick> *)
  apply (simp only: traces_DFtickA)
  apply (simp add: in_traces image_iff)
  
  (* <Ev a> ^^^ s *)
  apply (simp only: traces_DFtickA, simp)
  apply (simp add: in_traces_Int_choice image_iff)
  apply (simp add: in_traces_SKIP)
  apply (simp add: in_traces_Rep_int_choice in_traces_Act_prefix)

  apply (rule conj_cong, simp)

  apply (simp add: disj_left_commute)

  apply (simp add: in_traces_DFtickA_prefix_closed)
done


lemma DFtickA_unwindF :
    "(($DFtickA A)::('e DFtickName, 'e) proc) =F
     ((DFtickfun (DFtickA A))::('e DFtickName, 'e) proc)"
by (cspF_unwind)

lemma failures_DFtickA :
    "failures (($DFtickA A)::('e DFtickName, 'e) proc) MF = 
     failures ((DFtickfun (DFtickA A))::('e DFtickName, 'e) proc) MF"
  apply (insert DFtickA_unwindF[of A])
by (simp add: cspF_eqF_semantics)

lemma sndF_MF_DFtickA :
    "sndF (MF (DFtickA A)) = failures (($DFtickA A)::('e DFtickName, 'e) proc) MF"
  apply (insert DFtickA_unwindF[of A])
  apply (simp add: cspF_eqF_semantics)
  apply (simp add: failures_iff)
done



(*lemma in_failures_DFtickA_iff_sett :
    "(t,Y) :f failures (($DFtickA A)::('e DFtickName, 'e) proc) MF = 
     (sett t \<subseteq> insert Tick (Ev ` A) \<and>
      ((t = <> \<and> (\<exists>a\<in>A. Ev a \<notin> Y \<or> (Y \<subseteq> - (insert Tick (Ev ` A))))) \<or>
       (t = <> \<and> Y \<subseteq> Evset) \<or> (t = <Tick>)))"
  apply (induct t rule: induct_trace)

  (* <> *)
  apply (simp only: sett_nil empty_subsetI simp_thms)
  apply (simp only: failures_DFtickA DFtickfun.simps)
  apply (simp only: in_failures image_iff Int_pre_choice_def)
  apply (rule disj_cong)
  apply (rule bex_cong, simp)
  apply (rule disj_cong, simp)
defer
  apply (rule disj_cong, simp)
  apply (simp)
  
  (* <Tick> *)
  apply (simp add: failures_DFtickA)
  apply (simp only: in_failures image_iff)
  apply (simp)
  
  (* <Ev a> ^^^ s *)
  apply (simp (no_asm) add: failures_DFtickA)
  apply (simp (no_asm) add: in_failures image_iff)
  apply (simp add: sndF_MF_DFtickA, intro impI)
  apply (simp)

  apply (simp add: in_traces_DFtickA_prefix_closed)
done*)


lemma DFtickA_is_DeadlockFree:
    "Ev ` A \<subseteq> X \<Longrightarrow> Tick \<in> X \<Longrightarrow>
     [X]-DeadlockFree (($DFtickA A) :: ('e DFtickName, 'e) proc)"
  apply (simp add: DeadlockFree_def)
  apply (rule allI)
  apply (induct_tac s rule: induct_trace)
  
  apply (insert failures_DFtickA[of A])
  apply (simp)
  
  (* base case *)
  apply (simp)
  apply (subst in_failures)
  apply (simp (no_asm) add: in_failures)
  apply (simp add: Evset_def)
  apply (force)
  
  apply (simp)
  
  apply (simp (no_asm_simp))
  apply (intro impI)
  apply (simp (no_asm) add: in_failures)
  apply (intro impI)
  apply (simp add: sndF_MF_DFtickA)
done


(*** main ***)

lemma DFtickA_DeadlockFree:
    "Ev ` A \<subseteq> X \<Longrightarrow> Tick \<in> X \<Longrightarrow>
     ($DFtickA A :: ('e DFtickName, 'e) proc) <=F P ==> [X]-DeadlockFree P"
  apply (insert DFtickA_is_DeadlockFree[of A X])
  apply (simp add: DeadlockFree_def)
  apply (simp add: cspF_refF_semantics)
  apply (intro allI impI)
  apply (drule_tac x=s in spec, simp)
  apply (elim conjE subsetFE_ALL)
  apply (force)
done





subsection \<open> semantical approach --> syntactical approach \<close>


lemma traces_included_in_DFtickA_lm :
    "sett t \<subseteq> Ev ` A \<union> {Tick} \<longrightarrow>
     t :t traces ((FIX DFtickfun) (DFtickA A)) (fstF o MF)"
  apply (induct_tac t rule: induct_trace)
    
    (* <> *)
    apply (simp)
    
    (* <Tick> *)
    apply (simp add: FIX_def)
    apply (simp add: in_traces)
    apply (rule_tac x="Suc 0" in exI)
    apply (simp add: FIXn_def)
    apply (simp add: Subst_procfun_prod_def)
    apply (simp add: in_traces)
    
    (* <Ev a> ^^^ s *)
    apply (simp add: FIX_def)
    apply (simp add: in_traces)
    apply (intro impI)
    apply (elim conjE impE)

    apply (simp)
    apply (elim disjE exE)

      apply (rule_tac x="Suc 0" in exI)
      apply (simp add: FIXn_def)
      apply (simp add: Subst_procfun_prod_def)
      apply (simp add: in_traces)
      apply (force)
  
      apply (rule_tac x="Suc n" in exI)
      apply (simp add: FIXn_def)
      apply (simp add: Subst_procfun_prod_def)
      apply (simp add: in_traces)
      apply (force)
  done

lemma traces_included_in_DFtickA :
    "sett t \<subseteq> Ev ` A \<union> {Tick} \<Longrightarrow>
     t :t traces ((FIX DFtickfun) (DFtickA A)) (fstF o MF)"
by (simp add: traces_included_in_DFtickA_lm)




lemma failures_included_in_DFtickA_lm:
    "(\<exists>a\<in>A. Ev a \<notin> X) \<or> X \<subseteq> Evset \<Longrightarrow>
     sett t \<subseteq> Ev ` A \<union> {Tick} \<longrightarrow>
     (t,X) :f failures ((FIX DFtickfun) (DFtickA A)) MF"
  apply (induct_tac t rule: induct_trace)
  
  (* <> *)
  apply (simp add: FIX_def)
  apply (simp add: in_failures)
  apply (rule_tac x="Suc 0" in exI)
  apply (simp add: FIXn_def)
  apply (simp add: Subst_procfun_prod_def)
  apply (simp add: in_failures)
  
  (* <Tick> *)
  apply (simp add: FIX_def)
  apply (simp add: in_failures)
  apply (rule_tac x="Suc 0" in exI)
  apply (simp add: FIXn_def)
  apply (simp add: Subst_procfun_prod_def)
  apply (simp add: in_failures)
  
  (* <Ev a> ^^^ s *)
  apply (intro impI)

  apply (simp add: FIX_def)
  apply (simp add: in_failures)
  apply (elim exE conjE)
  apply (rule_tac x="Suc n" in exI)
  apply (simp add: FIXn_def)
  apply (simp (no_asm) add: Subst_procfun_prod_def)
  apply (simp add: in_failures)
  apply (simp add: Subst_procfun_prod_def)
  apply (force)
done


(*lemma alpha_not_subset_refusals : "(\<not> (Ev ` A \<subseteq> X)) = (\<exists>a\<in>A. Ev a \<notin> X)"
by (blast)*)


lemma failures_included_in_DFtickA:
  "[| sett t \<subseteq> Ev ` A \<union> {Tick} ; (\<exists>a\<in>A. Ev a \<notin> X) \<or> X \<subseteq> Evset |] ==>
   (t,X) :f failures ((FIX DFtickfun) (DFtickA A)) MF"
by (simp add: failures_included_in_DFtickA_lm)


lemma DeadlockFree_DFtickA:
    "\<forall>t. t :t traces P (fstF \<circ> MF) \<longrightarrow> sett t \<subseteq> Ev ` A \<union> {Tick} \<Longrightarrow>
     \<forall>t Y. (t,Y) :f failures P MF \<longrightarrow> (Y \<subseteq> Evset) \<Longrightarrow>
     [X]-DeadlockFree P \<Longrightarrow> ($DFtickA A :: ('e DFtickName, 'e) proc) <=F P"
  apply (rule cspF_rw_left)
  apply (rule cspF_FIX, simp_all)
  apply (simp add: cspF_refF_semantics)
  
  apply (rule conjI)
  
  (* trace *)
  apply (simp add: subdomT_iff)
  apply (simp add: traces_included_in_DFtickA)
  
  (* failures *)
  apply (simp add: subsetF_iff)
  apply (intro allI impI)
  apply (rule failures_included_in_DFtickA)
  apply (frule proc_T2, simp)
  apply (simp)
done



(*OLD
lemma failures_included_in_DFtickA_lm:
    "A \<noteq> {} \<Longrightarrow> (Tick : X \<longrightarrow> t = <Tick>) \<and>
     sett t \<subseteq> Ev ` A \<union> {Tick} \<longrightarrow>
     (t,X) :f failures ((FIX DFtickfun) (DFtickA A)) MF"
  apply (induct_tac t rule: induct_trace)
  
  (* <> *)
  apply (simp add: FIX_def)
  apply (simp add: in_failures)
  apply (intro impI)
  apply (rule_tac x="Suc 0" in exI)
  apply (simp add: FIXn_def)
  apply (simp add: Subst_procfun_prod_def)
  apply (simp add: in_failures)
  apply (simp add: Evset_def, force)
  
  (* <Tick> *)
  apply (simp add: FIX_def)
  apply (simp add: in_failures)
  apply (rule_tac x="Suc 0" in exI)
  apply (simp add: FIXn_def)
  apply (simp add: Subst_procfun_prod_def)
  apply (simp add: in_failures)
  
  (* <Ev a> ^^^ s *)
  apply (intro impI)

  apply (simp add: FIX_def)
  apply (simp add: in_failures)
  apply (elim exE conjE)
  apply (rule_tac x="Suc n" in exI)
  apply (simp add: FIXn_def)
  apply (simp (no_asm) add: Subst_procfun_prod_def)
  apply (simp add: in_failures)
  apply (simp add: Subst_procfun_prod_def)
  apply (force)
done


lemma failures_included_in_DFtickA:
  "[| sett t \<subseteq> Ev ` A \<union> {Tick} ; A \<noteq> {} ; Tick : X \<longrightarrow> t = <Tick> |] ==>
   (t,X) :f failures ((FIX DFtickfun) (DFtickA A)) MF"
by (simp add: failures_included_in_DFtickA_lm)

lemma DeadlockFree_DFtickA:
    "A \<noteq> {} \<Longrightarrow>
     \<forall>t. t :t traces P (fstF \<circ> MF) \<longrightarrow> sett t \<subseteq> Ev ` A \<union> {Tick} \<Longrightarrow>
     \<forall>t X. (t,X) :f failures P MF \<longrightarrow> (Tick : X \<longrightarrow> t = <Tick>) \<Longrightarrow>
     [X]-DeadlockFree P \<Longrightarrow> ($DFtickA A :: ('e DFtickName, 'e) proc) <=F P"
  apply (rule cspF_rw_left)
  apply (rule cspF_FIX, simp_all)
  apply (simp add: cspF_refF_semantics)
  
  apply (rule conjI)
  
  (* trace *)
  apply (simp add: subdomT_iff)
  apply (simp add: traces_included_in_DFtickA)
  
  (* failures *)
  apply (simp add: subsetF_iff)
  apply (intro allI impI)
  apply (rule failures_included_in_DFtickA)
  apply (frule proc_T2, simp)
  apply (simp, simp)
done*)



subsection \<open> syntactical approach <--> semantical approach \<close>


theorem DeadlockFree_DFtickA_ref:
    "\<forall>t. t :t traces P (fstF \<circ> MF) \<longrightarrow> sett t \<subseteq> Ev ` A \<union> {Tick} \<Longrightarrow>
     \<forall>t Y. (t,Y) :f failures P MF \<longrightarrow> (Y \<subseteq> Evset) \<Longrightarrow>
     Ev ` A \<subseteq> X \<Longrightarrow> Tick \<in> X \<Longrightarrow>
     [X]-DeadlockFree P = (($DFtickA A:: ('e DFtickName, 'e) proc) <=F P)"
  apply (rule)
  apply (simp add: DeadlockFree_DFtickA)
  apply (simp add: DFtickA_DeadlockFree)
done


end
