theory DFP_CHAOS
imports CSP_F.CSP_F_law_CHAOS
        DFP_law_DFtick
        DFP_law_DF
begin


lemma not_dfp_Chaos :
    "~ $DFtick <=F (($Chaos A)::('a ChaosName,'a) proc)"
  apply (rule notI)
  apply (erule cspF_rw_rightE)
  apply (cspF_unwind)
  apply (erule cspF_tr_rightE)
  apply (rule cspF_Int_choice_left2)
  apply (rule cspF_reflex)
  apply (erule contrapos_pp, simp)
  apply (rule not_dfp_STOP)
done


lemma not_dfpnt_Chaos :
    "~ $DF' <=F (($Chaos A)::('a ChaosName,'a) proc)"
  apply (rule notI)
  apply (erule cspF_tr_leftE)
  apply (rule dfp_DF')
  apply (erule contrapos_pp, simp)
  apply (rule not_dfp_Chaos)
done



lemma not_dfp_ChaosTick :
    "~ $DFtick <=F (($ChaosTick A)::('a ChaosName,'a) proc)"
  apply (rule notI)
  apply (erule cspF_rw_rightE)
  apply (cspF_unwind)
  apply (erule cspF_tr_rightE)
  apply (rule cspF_Int_choice_left1)
  apply (rule cspF_Int_choice_left2)
  apply (rule cspF_reflex)
  apply (erule contrapos_pp, simp)
  apply (rule not_dfp_STOP)
done


lemma not_dfpnt_ChaosTick :
    "~ $DF' <=F (($ChaosTick A)::('a ChaosName,'a) proc)"
  apply (rule notI)
  apply (erule cspF_tr_leftE)
  apply (rule dfp_DF')
  apply (erule contrapos_pp, simp)
  apply (rule not_dfp_ChaosTick)
done





lemma not_dfp_ChaosR :
    "~ $DFtick <=F (($ChaosR A)::('a ChaosName,'a) proc)"
  apply (rule notI)
  apply (erule cspF_rw_rightE)
  apply (cspF_unwind)
  apply (erule cspF_tr_rightE)
  apply (rule cspF_Int_choice_left2)
  apply (rule cspF_reflex)
  apply (erule contrapos_pp, simp)
  apply (rule not_dfp_STOP)
done


lemma not_dfpnt_ChaosR :
    "~ $DF' <=F (($ChaosR A)::('a ChaosName,'a) proc)"
  apply (rule notI)
  apply (erule cspF_tr_leftE)
  apply (rule dfp_DF')
  apply (erule contrapos_pp, simp)
  apply (rule not_dfp_ChaosR)
done



lemma not_dfp_ChaosRTick :
    "~ $DFtick <=F (($ChaosRTick A)::('a ChaosName,'a) proc)"
  apply (rule notI)
  apply (erule cspF_rw_rightE)
  apply (cspF_unwind)
  apply (erule cspF_tr_rightE)
  apply (rule cspF_Int_choice_left1)
  apply (rule cspF_Int_choice_left2)
  apply (rule cspF_reflex)
  apply (erule contrapos_pp, simp)
  apply (rule not_dfp_STOP)
done


lemma not_dfpnt_ChaosRTick :
    "~ $DF' <=F (($ChaosRTick A)::('a ChaosName,'a) proc)"
  apply (rule notI)
  apply (erule cspF_tr_leftE)
  apply (rule dfp_DF')
  apply (erule contrapos_pp, simp)
  apply (rule not_dfp_ChaosRTick)
done



end