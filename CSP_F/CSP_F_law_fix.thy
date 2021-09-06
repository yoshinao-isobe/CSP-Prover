           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                  March 2007               |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory CSP_F_law_fix
imports CSP_F_law_fp CSP_T.CSP_T_law_fix
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  Union (B ` A) = (UN x:A. B x)                      *)
(*                  Inter (B ` A) = (INT x:A. B x)                     *)

(*
declare Union_image_eq [simp del]
declare Inter_image_eq [simp del]
*)
(* no simp rules in Isabelle 2017 
declare Sup_image_eq [simp del]
declare Inf_image_eq [simp del]
*)

(*-----------*
 |    Bot    |
 *-----------*)

lemma failures_prod_Bot: "(%p. failures DIV M) = Bot"
apply (simp add: prod_Bot_def)
apply (simp add: fun_eq_iff)
apply (simp add: failures_iff)
apply (simp add: bottom_setF_def)
done

lemma traces_failures_prod_Bot: 
   "(%p. (traces DIV (fstF o M) ,, failures DIV M)) = Bot"
apply (simp add: prod_Bot_def)
apply (simp add: fun_eq_iff)
apply (simp add: bottom_domF_def)
apply (simp add: traces_iff failures_iff)
done

lemma semF_prod_Bot: "(%p. [[DIV]]F) = Bot"
apply (simp add: semF_def semFf_def)
apply (simp add: traces_failures_prod_Bot)
done

(*-----------*
 |   FIX P   |
 *-----------*)

(*** iteration lemmas ***)

lemma semTfun_iteration_semFfun_Bot:
  "ALL p. ([[Pf]]Tfun ^^ n) Bot p = fstF (([[Pf]]Ffun ^^ n) Bot p)"
apply (induct_tac n)
apply (simp_all)

(* base *)
apply (simp add: prod_Bot_def bottom_domF_def)
apply (simp add: bottom_domT_def)
apply (simp add: pairF_fstF)

(* step *)
apply (simp add: fun_eq_iff[THEN sym])
apply (simp add: fun_eq_iff)
apply (simp add: semFfun_def)
apply (fold comp_def)
apply (simp add: semTfun_fstF_semFf)
done

lemma semF_iteration_semFfun_Bot:
  "ALL p. [[(((Pf <<<) ^^ n) (%q. DIV) p)]]F = (([[Pf]]Ffun ^^ n) Bot p)"
apply (induct_tac n)
apply (simp_all)

(* base *)
apply (simp add: semF_def semFf_def)
apply (simp add: traces_iff failures_iff)
apply (simp add: prod_Bot_def bottom_domF_def)

(* step *)
apply (simp add: Subst_procfun_prod_def)
apply (simp add: semF_subst)
apply (simp add: fun_eq_iff[THEN sym])
apply (simp add: semFf_semFfun)
done

lemma semF_iteration_semFfun_Bot_sndF: 
  "failures (((Pf <<<) ^^ n) (%q. DIV) p) MF
   = sndF (([[Pf]]Ffun ^^ n) Bot p)"
apply (rule semF_decompo_sndF)
by (simp add: semF_iteration_semFfun_Bot)

(*** FIX ***)

lemma semF_FIX_LUB_domF_T:
   "fst ` Rep_domF ` 
   {y. EX x. (EX n. x = ([[P]]Ffun ^^ n) Bot) & y = x p}
 = {t. EX n. t = (fstF ((([[P]]Ffun ^^ n) Bot) p))}"
by (auto simp add: fstF_def)

lemma semF_FIX_LUB_domF_F:
   "Union (Rep_setF ` snd ` Rep_domF ` 
           {y. EX x. (EX n. x = ([[P]]Ffun ^^ n) Bot) & y = x p})
    = {f. EX n. f :f (sndF ((([[P]]Ffun ^^ n) Bot) p))}"
(* it is not necessary to add Union_image_eq in Isabelle 2017
by (auto simp add: Union_image_eq memF_def sndF_def)
*)
by (auto simp add: memF_def sndF_def)

lemma semF_FIX: 
    "[[(FIX Pf) p]]F
     = LUB_domF {y. EX x. (EX n. x = ([[Pf]]Ffun ^^ n) Bot) & y = x p}"
apply (simp add: semF_def semFf_def)
apply (simp add: pairF_def)
apply (simp add: LUB_domF_def)
apply (subgoal_tac "EX x n. x = ([[Pf]]Ffun ^^ n) Bot")
apply (subgoal_tac 
 "{y. EX x. (EX n. x = ([[Pf]]Ffun ^^ n) Bot) & y = x p} ~= {}")
apply (simp add: Abs_domF_inject LUB_TF_in_Rep)
apply (simp add: LUB_TF_def)
apply (simp add: semF_FIX_LUB_domF_T)
apply (simp add: UnionF_def)
(* for Isabelle 2018 *)
apply (simp add: semF_FIX_LUB_domF_F[simplified])
apply (rule) 

 (* T *)
 apply (simp add: traces_FIX)
 apply (simp add: semTfun_iteration_semFfun_Bot)

 (* F *)
 apply (simp add: FIX_def FIXn_def)
 apply (rule order_antisym)

  (* <= *)
  apply (rule)
  apply (simp add: in_failures)
  apply (elim conjE exE)
  apply (simp add: semF_iteration_semFfun_Bot_sndF)
  apply (force)

  (* => *)
  apply (rule)
  apply (simp add: in_failures)
  apply (elim conjE exE)
  apply (simp add: semF_iteration_semFfun_Bot_sndF)
  apply (force)

by (auto)

(*** FIX is LUB ***)

lemma semF_FIX_isLUB:
   "(%p. [[(FIX Pf) p]]F) isLUB {x. EX n. x = ([[Pf]]Ffun ^^ n) Bot}"
apply (simp add: prod_LUB_decompo)
apply (intro allI)
apply (simp add: proj_fun_def)
apply (simp add: image_def)
apply (simp add: semF_FIX)
apply (subgoal_tac 
     "{y. EX x. (EX n. x = ([[Pf]]Ffun ^^ n) Bot) & y = x i} =
      {u. EX n. u = ([[Pf]]Ffun ^^ n) Bot i}")
apply (simp)
apply (rule LUB_domF_isLUB)
apply (auto)
done


lemma semF_FIX_LUB:
   "(%p. [[(FIX Pf) p]]F) = LUB {x. EX n. x = ([[Pf]]Ffun ^^ n) Bot}"
apply (rule sym)
apply (rule isLUB_LUB)
apply (simp add: semF_FIX_isLUB)
done

lemma semF_FIX_LFP:
   "(%p. [[(FIX Pf) p]]F) = LFP ([[Pf]]Ffun)"
apply (simp add: semF_FIX_LUB)
apply (simp add: Tarski_thm_LFP_LUB continuous_semFfun)
done

lemma semF_FIX_LFP_p:
   "[[(FIX Pf) p]]F = LFP ([[Pf]]Ffun) p"
apply (insert semF_FIX_LFP[of Pf])
apply (simp add: fun_eq_iff)
done

lemma semF_FIX_isLFP:
   "(%p. [[(FIX Pf) p]]F) isLFP [[Pf]]Ffun"
apply (simp add: semF_FIX_LFP)
apply (simp add: LFP_is Tarski_thm_EX continuous_semFfun)
done

lemma semF_FIX_LFP_fixed_point:
   "[[Pf]]Ffun (%p. [[(FIX Pf) p]]F) = (%p. [[(FIX Pf) p]]F)"
apply (insert semF_FIX_isLFP[of Pf])
apply (simp add: isLFP_def)
done

lemma semF_FIX_LFP_least:
   "ALL M. [[Pf]]Ffun M = M --> (%p. [[(FIX Pf) p]]F) <= M"
apply (insert semF_FIX_isLFP[of Pf])
apply (simp add: isLFP_def)
done

(*=======================================================*
 |                                                       |
 |                        CPO                            |
 |                                                       |
 *=======================================================*)

lemma cspF_FIX_cpo:
  "[| FPmode = CPOmode |
      FPmode = MIXmode ;
      Pf = PNfun |]
  ==> $p =F (FIX Pf)(p)"
apply (simp add: eqF_def)
apply (fold semF_def)
apply (simp add: semF_FIX_LFP_p)
apply (simp add: semF_LFP_cpo)
done

lemma cspF_FIX_cms:
  "[| FPmode = CMSmode ;
      Pf = PNfun ;
      guardedfun (Pf) |]
  ==> $p =F (FIX Pf)(p)"
apply (simp add: eqF_def)
apply (fold semF_def)
apply (simp add: semF_FIX_LFP_p)
apply (simp add: semF_guarded_LFP_UFP)
apply (simp add: semF_UFP_cms)
done

lemma cspF_FIX:
  "[| FPmode = CPOmode | 
      FPmode = CMSmode & guardedfun (Pf) |
      FPmode = MIXmode ;
      Pf = PNfun |]
  ==> $p =F (FIX Pf)(p)"
apply (erule disjE)
apply (simp add: cspF_FIX_cpo)
apply (erule disjE)
apply (simp add: cspF_FIX_cms)
apply (simp add: cspF_FIX_cpo)
done

(*==============================================================*
 |                                                              |
 | replace process names by infinite repcicated internal choice |
 |                         rmPN   (FIX)                         |
 |                                                              |
 *==============================================================*)

lemma cspF_rmPN_eqF:
  "FPmode = CPOmode | 
   FPmode = CMSmode & guardedfun (PNfun::('p=>('p,'a) proc)) |
   FPmode = MIXmode 
   ==> (P::('p,'a) proc) =F rmPN(P)"
apply (induct_tac P)
apply (simp_all add: cspF_decompo)
apply (rule cspF_FIX)
apply (simp_all)
done

(*-------------------------------------------------------*
 |                                                       |
 |         FIX expansion (CSP-Prover intro rule)         |
 |                                                       |
 *-------------------------------------------------------*)

lemma failures_FIXn_plus_sub_lm:
 "ALL n m p. failures ((FIX[n] Pf) p) M <= failures ((FIX[n+m] Pf) p) M"
apply (rule)
apply (induct_tac n)
apply (simp add: FIXn_def)
apply (intro allI)
apply (rule)
apply (simp add: in_failures)

apply (rule allI)
apply (simp add: FIXn_def Subst_procfun_prod_def)
apply (drule_tac x="m" in spec)
apply (simp add: failures_subst)
apply (rule allI)
apply (subgoal_tac
  "(%q. [[((%Qf p. (Pf p) << Qf) ^^ na) (%q. DIV) q]]Ff M) <=
   (%q. [[((%Qf p. (Pf p) << Qf) ^^ (na + m)) (%q. DIV) q]]Ff M)")
apply (simp add: mono_failures[simplified mono_def])
apply (unfold order_prod_def)
apply (intro allI)
apply (simp add: subdomF_decompo)
apply (insert traces_FIXn_plus_sub_lm[of Pf "fstF o M"])
apply (simp add: FIXn_def Subst_procfun_prod_def)
done

lemma failures_FIXn_plus_sub: 
   "failures ((FIX[n] Pf) p) M <= failures ((FIX[n+m] Pf) p) M"
by (simp add: failures_FIXn_plus_sub_lm)

lemma semF_FIXn_plus_sub:
 "[[(FIX[n] Pf) p]]Ff M <= [[(FIX[n+m] Pf) p]]Ff M"
apply (simp add: subdomF_decompo)
apply (simp add: traces_FIXn_plus_sub)
apply (simp add: failures_FIXn_plus_sub)
done

lemma in_failures_FIXn_plus_sub: 
  "(s,X) :f failures ((FIX[n] Pf) p) M
   ==> (s,X) :f failures ((FIX[n+m] Pf) p) M"
apply (insert failures_FIXn_plus_sub[of n Pf p M m])
by (auto)

(*-----------------------------------------------------*
 |  sometimes FIX[n + f n] is useful more than FIX[n]  |
 *-----------------------------------------------------*)

lemma cspF_FIX_plus_eq: 
     "ALL f p. (FIX Pf) p =F (!nat n .. ((FIX[n + f n] Pf) p))"
apply (simp add: cspF_cspT_semantics)
apply (simp add: cspT_FIX_plus_eq)

apply (simp add: FIX_def)
apply (intro allI)
apply (rule order_antisym)

 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE exE)
 apply (rule_tac x="n" in exI)
 apply (simp add: in_failures_FIXn_plus_sub)

 apply (rule)
 apply (simp add: in_failures)
 apply (elim conjE exE)
 apply (rule_tac x="n + f n" in exI)
 apply (simp)
done

(****************** to add them again ******************)
(*
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
*)
(*
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
*)
end
