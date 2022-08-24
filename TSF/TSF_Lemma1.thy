theory TSF_Lemma1
imports tockCSP_F.tockCSP_Proof_Rule1
        TSF_TOCKSTick
begin

(* Lemma1 is proved in
   tockCSP_F.tockCSP_Proof_Rule1.Rule_check_timestops_Roscoe_TOCKSTick
   and generalised in theorem
   TSF.TSF_TOCKSTick.TimeStopFree_TOCKSTick_ref_iff *)

lemmas pre_Lemma1_Jesus_Sampaio_2022 = Rule_check_timestops_Roscoe_TOCKSTick

lemmas Lemma1_Jesus_Sampaio_2022 = TimeStopFree_TOCKSTick_ref_iff

end