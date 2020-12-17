           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                  March 2007               |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_law_fix
imports CSP_T_law_fp
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

definition
 FIXn :: "nat => ('p => ('p,'a) proc) => ('p => ('p,'a) proc)"
                                                      ("FIX[_] _" [0,1000] 55)
  where
  FIXn_def :  "FIX[n] Pf == ((Pf <<< )^^n) (%q. DIV)"
  
definition
  FIX  :: "(('p) => ('p,'a) proc) => ('p => ('p,'a) proc)"
                                                      ("FIX _" [1000] 55)
  where
  FIX_def : "FIX Pf == (%p. (!nat n .. ((FIX[n] Pf) p)))"

(* ----- test ----- *
consts
 FIXnrec :: "nat => ('p => ('p,'a) proc) => ('p => ('p,'a) proc)"
                                                      ("FIXrec[_] _" [0,1000] 55)
primrec
     "FIXrec[0] Pf = (%p. DIV)"
 "FIXrec[Suc n] Pf = (%p. (Pf p)<<(FIXrec[n] Pf))"

lemma FIXn_FIXnrec: "FIX[n] Pf = FIXrec[n] Pf"
apply (induct_tac n)
apply (simp_all add: FIXn_def)
done

 * ----- test ----- *)

(*-----------*
 |   noPN    |
 *-----------*)

lemma noPNfun_FIXn: "noPNfun (%p. (FIX[n] Pf)(p))"
apply (simp add: FIXn_def)
apply (induct_tac n)
apply (simp add: noPNfun_def)
apply (simp (no_asm) add: noPNfun_def)
apply (intro allI)
apply (simp add: Subst_procfun_prod_def)
apply (simp add: noPN_Subst_Pf)
done

lemma noPN_FIXn: "noPN ((FIX[n] Pf)p)"
apply (insert noPNfun_FIXn[of _ Pf])
apply (simp add: noPNfun_def)
done

lemma noPN_FIX: "noPN ((FIX Pf) p)"
apply (simp add: FIX_def)
apply (simp add: noPN_FIXn)
done

(*-----------*
 |    Bot    |
 *-----------*)

lemma traces_prod_Bot: "(%p. traces DIV M) = Bot"
apply (simp add: prod_Bot_def)
apply (simp add: fun_eq_iff)
apply (simp add: traces_iff)
apply (simp add: bottom_domT_def)
done

lemma semT_prod_Bot: "(%p. [[DIV]]T) = Bot"
by (simp add: semT_def semTf_def traces_prod_Bot)

(*-----------*
 |   FIX P   |
 *-----------*)

lemma traces_subst_Bot: "traces (P<<(%q. DIV)) M = (traces P) Bot"
apply (induct_tac P)
apply (simp_all add: traces_iff)
apply (simp add: prod_Bot_def)
apply (simp add: bottom_domT_def)
done

lemma traces_iteration_semTfun_Bot:
  "ALL p. traces (((Pf <<<) ^^ n) (%q. DIV) p) M = ([[Pf]]Tfun ^^ n) Bot p"
apply (simp add: semTfun_def)
apply (simp add: semTf_def)
apply (induct_tac n)

(* base *)
apply (simp_all add: traces_iff)
apply (simp add: prod_Bot_def)
apply (simp add: bottom_domT_def)

(* step *)
apply (simp add: Subst_procfun_prod_def)
apply (simp add: traces_subst)
done

lemma traces_FIX:
    "traces ((FIX Pf) p) M
     = UnionT {u. EX n. u = ([[Pf]]Tfun ^^ n) Bot p}"
apply (simp add: FIX_def FIXn_def)
apply (subgoal_tac "{u. EX n. u = ([[Pf]]Tfun ^^ n) Bot p} ~= {}")
apply (rule order_antisym)

 (* <= *)
 apply (rule)
 apply (simp add: in_traces)
 apply (erule disjE, simp)
 apply (elim conjE exE)
 apply (rule_tac x="traces (((Pf <<<) ^^ n) (%q. DIV) p) M" in exI)
 apply (simp)
 apply (rule_tac x="n" in exI)
 apply (simp add: traces_iteration_semTfun_Bot)

 (* => *)
 apply (rule)
 apply (simp add: in_traces)
 apply (rule disjI2)
 apply (elim conjE exE)
 apply (simp)
 apply (rule_tac x="na" in exI)
 apply (simp add: traces_iteration_semTfun_Bot)

by (auto)

(*** [[ ]]T ***)

lemma semT_FIX:
    "[[(FIX Pf) p]]T
     = UnionT {u. EX n. u = ([[Pf]]Tfun ^^ n) Bot p}"
apply (simp add: semT_def semTf_def)
apply (simp add: traces_FIX)
done

(*** FIX is LUB ***)

lemma semT_FIX_isLUB:
   "(%p. [[(FIX Pf) p]]T) isLUB {x. EX n. x = ([[Pf]]Tfun ^^ n) Bot}"
apply (simp add: prod_LUB_decompo)
apply (intro allI)
apply (simp add: proj_fun_def)
apply (simp add: image_def)
apply (simp add: semT_FIX)
apply (subgoal_tac 
     "{y. EX x. (EX n. x = ([[Pf]]Tfun ^^ n) Bot) & y = x i} =
      {u. EX n. u = ([[Pf]]Tfun ^^ n) Bot i}")
apply (simp)
apply (rule UnionT_isLUB)
apply (auto)
done

lemma semT_FIX_LUB:
   "(%p. [[(FIX Pf) p]]T) = LUB {x. EX n. x = ([[Pf]]Tfun ^^ n) Bot}"
apply (rule sym)
apply (rule isLUB_LUB)
apply (simp add: semT_FIX_isLUB)
done

lemma semT_FIX_LFP:
   "(%p. [[(FIX Pf) p]]T) = LFP [[Pf]]Tfun"
apply (simp add: semT_FIX_LUB)
apply (simp add: Tarski_thm_LFP_LUB continuous_semTfun)
done

lemma semT_FIX_LFP_p:
   "[[(FIX Pf) p]]T = LFP [[Pf]]Tfun p"
apply (insert semT_FIX_LFP[of Pf])
apply (simp add: fun_eq_iff)
done

lemma semT_FIX_isLFP:
   "(%p. [[(FIX Pf) p]]T) isLFP [[Pf]]Tfun"
apply (simp add: semT_FIX_LFP)
apply (simp add: LFP_is Tarski_thm_EX continuous_semTfun)
done

lemma semT_FIX_LFP_fixed_point:
   "[[Pf]]Tfun (%p. [[(FIX Pf) p]]T) = (%p. [[(FIX Pf) p]]T)"
apply (insert semT_FIX_isLFP[of Pf])
apply (simp add: isLFP_def)
done

lemma semT_FIX_LFP_least:
   "ALL Tf. [[Pf]]Tfun Tf = Tf --> (%p. [[(FIX Pf) p]]T) <= Tf"
apply (insert semT_FIX_isLFP[of Pf])
apply (simp add: isLFP_def)
done

(*=======================================================*
 |                                                       |
 |                        CPO                            |
 |                                                       |
 *=======================================================*)

lemma cspT_FIX_cpo:
  "[| FPmode = CPOmode |
      FPmode = MIXmode ;
      Pf = PNfun |]
  ==> $p =T (FIX Pf)(p)"
apply (simp add: eqT_def)
apply (fold semT_def)
apply (simp add: semT_FIX_LFP_p)
apply (simp add: semT_LFP_cpo)
done

lemma cspT_FIX_cms:
  "[| FPmode = CMSmode ;
      Pf = PNfun ;
      guardedfun (Pf) |]
  ==> $p =T (FIX Pf)(p)"
apply (simp add: eqT_def)
apply (fold semT_def)
apply (simp add: semT_FIX_LFP_p)
apply (simp add: semT_guarded_LFP_UFP)
apply (simp add: semT_UFP_cms)
done

lemma cspT_FIX:
  "[| FPmode = CPOmode | 
      FPmode = CMSmode & guardedfun (Pf) |
      FPmode = MIXmode ;
      Pf = PNfun |]
  ==> $p =T (FIX Pf)(p)"
apply (erule disjE)
apply (simp add: cspT_FIX_cpo)
apply (erule disjE)
apply (simp add: cspT_FIX_cms)
apply (simp add: cspT_FIX_cpo)
done

(*==============================================================*
 |                                                              |
 | replace process names by infinite repcicated internal choice |
 |                         rmPN   (FIX)                         |
 |                                                              |
 *==============================================================*)

primrec 
   rmPN :: "('p,'a) proc => ('p,'a) proc"
where
  "rmPN(STOP)        = STOP"
 |"rmPN(SKIP)        = SKIP"
 |"rmPN(DIV)         = DIV"
 |"rmPN(a -> P)      = a -> (rmPN P)"
 |"rmPN(? :A -> Pf)  = ? a:A -> (rmPN (Pf a))"
 |"rmPN(P [+] Q)     = (rmPN P) [+] (rmPN Q)"
 |"rmPN(P |~| Q)     = (rmPN P) |~| (rmPN Q)"
 |"rmPN(!! :C .. Pf) = !! c:C .. rmPN (Pf c)"
 |"rmPN(IF b THEN P ELSE Q) = (IF b THEN rmPN(P) ELSE rmPN(Q))"
 |"rmPN(P |[X]| Q)   = (rmPN P) |[X]| (rmPN Q)"
 |"rmPN(P -- X)      = (rmPN P) -- X"
 |"rmPN(P [[r]])     = (rmPN P) [[r]]"
 |"rmPN(P ;; Q)      = (rmPN P) ;; (rmPN Q)"
 |"rmPN(P |. n)      = (rmPN P) |. n"
 |"rmPN($p)          = (FIX PNfun)(p)"

lemma noPN_rmPN: "noPN (rmPN P)"
apply (induct_tac P)
apply (simp_all)
apply (simp add: noPN_FIX)
done

lemma cspT_rmPN_eqT:
  "FPmode = CPOmode | 
   FPmode = CMSmode & guardedfun (PNfun::('p=>('p,'a) proc)) |
   FPmode = MIXmode 
   ==> (P::('p,'a) proc) =T rmPN(P)"
apply (induct_tac P)
apply (simp_all add: cspT_decompo)
apply (rule cspT_FIX)
apply (simp_all)
done

(*-------------------------------------------------------*
 |                                                       |
 |         FIX expansion (CSP-Prover intro rule)         |
 |                                                       |
 *-------------------------------------------------------*)

lemma traces_FIXn_plus_sub_lm:
 "ALL n m p. traces ((FIX[n] Pf) p) M <= traces ((FIX[n+m] Pf) p) M"
apply (rule)
apply (induct_tac n)
apply (simp add: FIXn_def Subst_procfun_prod_def)
apply (intro allI)
apply (rule)
apply (simp add: in_traces)

apply (rule allI)
apply (simp add: FIXn_def Subst_procfun_prod_def)
apply (drule_tac x="m" in spec)
apply (simp add: traces_subst)
apply (rule allI)
apply (fold order_prod_def)
apply (simp add: mono_traces[simplified mono_def])
done

lemma traces_FIXn_plus_sub: 
   "traces ((FIX[n] Pf) p) M <= traces ((FIX[n+m] Pf) p) M"
by (simp add: traces_FIXn_plus_sub_lm)

lemma semT_FIXn_plus_sub:
 "[[(FIX[n] Pf) p]]Tf M <= [[(FIX[n+m] Pf) p]]Tf M"
apply (simp add: semTf_def)
apply (simp add: traces_FIXn_plus_sub)
done

lemma in_traces_FIXn_plus_sub: 
  "t :t traces ((FIX[n] Pf) p) M ==> t :t traces ((FIX[n+m] Pf) p) M"
apply (insert traces_FIXn_plus_sub[of n Pf p M m])
by (auto)

(*-----------------------------------------------------*
 |  sometimes FIX[n + f n] is useful more than FIX[n]  |
 *-----------------------------------------------------*)

lemma cspT_FIX_plus_eq: 
     "ALL f p. (FIX Pf) p =T[M,M] (!nat n .. ((FIX[n + f n] Pf) p))"
apply (simp add: FIX_def)
apply (simp add: eqT_def)
apply (intro allI)
apply (simp add: semTf_def)
apply (rule order_antisym)

 apply (rule)
 apply (simp add: in_traces)
 apply (rule disjI2)
 apply (elim conjE exE disjE, simp)
 apply (rule_tac x="n" in exI)
 apply (simp add: in_traces_FIXn_plus_sub)

 apply (rule)
 apply (simp add: in_traces)
 apply (elim conjE exE disjE)
 apply (simp)
 apply (rule disjI2)
 apply (rule_tac x="n + f n" in exI)
 apply (simp)
done

(****************** to add them again ******************)
(*
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
*)
(* 2017
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
*)

end
