theory TSF_Theorem2
imports TSF_Theorem1
begin


lemma Theorem2_Jesus_Sampaio_2022_only_if :
    "( [X]-DeadlockFree P ) ==>
     ( ([X]-TimeStopFree P) & ([X - {Tock}]-DeadlockFree (P -- {tock})) )"

  apply (simp add: TimeStopFree_def)
  apply (simp add: DeadlockFree_def)
  apply (simp add: in_failures hide_tr_sym)
  apply (simp only: all_conj_distrib[THEN sym])
  apply (simp only: imp_conv_disj)
  apply (simp only: disj_conj_distribL[THEN sym])
  apply (simp only: all_conj_distrib[THEN sym])

    apply (rule)
    apply (subst disj_imp, rule)
    apply (rule)
    apply (simp add: disj_imp)
    apply (rule)
    apply (rule)
    apply (drule_tac x=sa in spec)
    apply (simp add: Tick_notin_hide_tr_trans1)
    apply (rule non_memF_F2[of _ X], simp, force)
    apply (rule)
    apply (drule_tac x=sa in spec)
    apply (simp add: Tick_notin_hide_tr_trans1)
    apply (rule non_memF_F2[of _ X], simp, force)
  done



lemma subset_NonTickTockEv_and_subset_Tock :
    "sett s \<subseteq> NonTickTockEv \<Longrightarrow>
       sett s \<subseteq> {Tock} \<Longrightarrow> s = <>"
  apply (simp add: subset_iff)
  by (simp add: sett_empty_iff)


lemma Theorem2_Jesus_Sampaio_2022_if :
    "( ([X]-TimeStopFree P) & ([X - {Tock}]-DeadlockFree (P -- {tock})) )
     \<Longrightarrow> ( [X]-DeadlockFree P )"
  apply (elim conjE)
  apply (simp only: TimeStopFree_def)
  apply (simp only: DeadlockFree_def)
  apply (simp add: in_failures hide_tr_sym)
  apply (intro allI impI)

  apply (case_tac "\<exists>t. t =tocks(s)", elim exE, simp_all)
  apply (drule_tac x=t in spec)
  apply (drule mp, simp add: Tick_notin_hide_tr_trans2)

  apply (case_tac "\<exists>nt. nt =nontocks(s)", elim exE, simp_all)
  apply (drule_tac x=nt in spec)
  apply (drule mp, simp add: Tick_notin_hide_tr_trans2)

  apply (drule_tac x=s in spec, simp)
  apply (drule_tac x=s in spec, simp)

  (* The pending goal requires the divergences to
     be included in the failures.*)
  (* NOTE: trying to use proc_F3 will discharge assumptions
           (s, insert Tock X) ~:f failures P MF \<Longrightarrow>
           (s, EvsetTick) ~:f failures P MF \<Longrightarrow>
           but maintain assumption
           (s, X) :f failures P MF \<Longrightarrow>
           so, when P diverges, refusals X can grows to insert Tock X
               then to UNIV (EvsetTick) *)
  (* CSP-Prover does not provides FD model, so we are implementing
     FD to provide a full mechanisation. *)

  (* case 1: Tock refused when P diverges *)
  apply (rotate_tac -1, erule contrapos_nn)

  (* case 2: - X refused when P diverges *)
  apply (rotate_tac -2, erule contrapos_np)
  sorry


theorem Theorem2_Jesus_Sampaio_2022 :
    "( [X]-DeadlockFree P ) =
     ( ([X]-TimeStopFree P) & ([X - {Tock}]-DeadlockFree (P -- {tock})) )"
  apply (rule)
    apply (simp only: Theorem2_Jesus_Sampaio_2022_only_if)
    apply (simp only: Theorem2_Jesus_Sampaio_2022_if)
  done

end