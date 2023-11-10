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

lemmas Lemma1_Jesus_Sampaio_2023 = Lemma1_Jesus_Sampaio_2022

end