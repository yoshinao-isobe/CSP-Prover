           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                 August 2007               |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_MF_MT
imports CSP_F_law_fp
begin

(*********************************************************
            MT = fstF o MF if fixed points exist
 *********************************************************)

(*--------------*
 |      cms     |
 *--------------*)

(*** fixed point ***)

lemma fstF_MF_fixed_point_cms:
      "[| Pf = PNfun; guardedfun Pf ; FPmode = CMSmode|]
        ==> [[Pf]]Tfun (fstF o MF) = (fstF o MF)"
apply (simp (no_asm) add: fun_eq_iff)
apply (simp add: semTfun_def)
apply (rule)
apply (subgoal_tac "$x =F Pf x")
apply (simp add: cspF_cspT_semantics)
apply (simp add: eqT_def)
apply (simp add: semTf_def)
apply (simp add: traces.simps)
apply (simp add: cspF_unwind)
done

(*** fstF o MF = MT ***)

lemma fstF_MF_MT_cms:
      "[| (Pf::'p=>('p,'a) proc) = PNfun; guardedfun Pf ; FPmode = CMSmode|]
        ==> (fstF o MF) = (MT::'p => 'a domT)"
apply (rule hasUFP_unique_solution[of "[[Pf]]Tfun"])
apply (simp add: semT_hasUFP_cms)
apply (simp add: fstF_MF_fixed_point_cms)
apply (simp add: MT_fixed_point_cms)
done

(*--------------*
 |    least     |
 *--------------*)

(*** fixed point ***)

lemma fstF_MF_fixed_point_cpo:
      "[| Pf = PNfun; FPmode = CPOmode | FPmode = MIXmode |]
        ==> [[Pf]]Tfun (fstF o MF) = (fstF o MF)"
apply (simp (no_asm) add: fun_eq_iff)
apply (simp add: semTfun_def)
apply (rule)
apply (subgoal_tac "$x =F Pf x")
apply (simp add: cspF_cspT_semantics)
apply (simp add: eqT_def)
apply (simp add: semTf_def)
apply (simp add: traces.simps)
apply (rule cspF_unwind)
apply (auto)
done

(*** fstF o MF = MT ***)

lemma MT_LFP_UnionT_cpo_lm:
  "(EX x. (EX n. x = ([[PNfun]]Tfun ^^ n) Bot) & y = x p)
  = (EX n. y = ([[PNfun]]Tfun ^^ n) Bot p)"
by (auto)

lemma MT_LFP_UnionT_cpo:
  "Pf = PNfun 
   ==> LFP ([[Pf]]Tfun) p = UnionT {y. EX n. y = ([[Pf]]Tfun ^^ n) Bot p}"
apply (subgoal_tac 
  "LFP ([[Pf]]Tfun) isLUB {x. EX n. x = ([[Pf]]Tfun^^n) Bot}")
apply (simp add: prod_LUB_decompo)
apply (drule_tac x="p" in spec)
apply (simp add: proj_fun_def)
apply (subgoal_tac "(%x. x p) ` {x. EX n. x = ([[Pf]]Tfun ^^ n) Bot} ~= {}")
apply (simp add: isLUB_UnionT)
apply (simp add: image_def)
apply (simp add: MT_LFP_UnionT_cpo_lm)
apply (force)

apply (simp add: Tarski_thm continuous_semTfun)
done

lemma fstF_MF_LFP_UnionT_cpo_lm1:
  "(EX b x.
        (EX xa. (EX n. xa = ([[Pf]]Ffun ^^ n) Bot) & x = xa p) &
        (y, b) = Rep_domF x) =
    (EX n. y = fstF (([[Pf]]Ffun ^^ n) Bot p))"
apply (auto)

apply (rule_tac x="n" in exI)
apply (simp add: pair_eq_decompo)
apply (simp add: fstF_def)

apply (rule_tac x="(sndF (([[Pf]]Ffun ^^ n) Bot p))" in exI)
apply (rule_tac x="([[Pf]]Ffun ^^ n) Bot p" in exI)
apply (rule conjI)
apply (force)

apply (subgoal_tac 
 "Rep_domF(Abs_domF(fstF (([[Pf]]Ffun ^^ n) Bot p),
                    sndF (([[Pf]]Ffun ^^ n) Bot p)))
  = Rep_domF (([[Pf]]Ffun ^^ n) Bot p)")
apply (simp add: Abs_domF_inverse)
apply (simp add: Rep_domF_inject)
apply (fold pairF_def)
apply (simp)
done

lemma fstF_MF_LFP_UnionT_cpo_lm2:
  "LFP ([[Pf]]Ffun) p =
   LUB_domF ((%x. x p) ` {x. EX n. x = ([[Pf]]Ffun ^^ n) Bot})"
apply (subgoal_tac "LFP ([[Pf]]Ffun) isLUB {x. EX n. x = ([[Pf]]Ffun ^^n) Bot}")
apply (rule isLUB_LUB_domF_only_if)
apply (force)
apply (simp add: prod_LUB_decompo)
apply (drule_tac x="p" in spec)
apply (simp add: proj_fun_def)
apply (simp add: Tarski_thm continuous_semFfun)
done

lemma fstF_MF_LFP_UnionT_cpo:
  "Pf = PNfun 
   ==> fstF (LFP ([[Pf]]Ffun) p) =
       UnionT {y. EX n. y = fstF (([[Pf]]Ffun ^^ n) Bot p)}"
apply (subgoal_tac 
  "fstF (LFP ([[Pf]]Ffun) p) =
   fstF (LUB_domF ((%x. x p) ` {x. EX n. x = ([[Pf]]Ffun ^^ n) Bot}))")
apply (simp add: LUB_domF_def)
apply (simp add: fstF_def)
apply (subgoal_tac "(%x. x p) ` {x. EX n. x = ([[Pf]]Ffun ^^ n) Bot} ~= {}")
apply (simp add: LUB_TF_in_Rep Abs_domF_inverse)
apply (simp add: LUB_TF_def)
apply (simp add: image_def)
apply (simp add: fstF_MF_LFP_UnionT_cpo_lm1)
apply (simp add: fstF_def)
apply (force)
apply (simp add: fstF_MF_LFP_UnionT_cpo_lm2)
done

(* Tfun and fst Ffun *)

lemma iterative_fstF_semFfun_semFfun:
  "ALL p. (fstF (([[Pf]]Ffun ^^ n) Bot p)) = (([[Pf]]Tfun ^^ n) Bot p)"
apply (induct_tac n)

(* base *)
 apply (simp add: prod_Bot_def)
 apply (simp add: bottom_domF_def)
 apply (simp add: pairF)
 apply (simp add: bottom_domT_def)

(* step *)
 apply (simp add: semFfun_def)
 apply (simp add: comp_def)
 apply (simp add: semTfun_def)
 apply (simp add: semTf_def)
done

(*** fstF o MF = MT ***)

lemma fstF_MF_MT_cpo_lm:
  "Pf = PNfun 
   ==> fstF (LFP ([[Pf]]Ffun) p) = LFP ([[Pf]]Tfun) p"
apply (simp add: MT_LFP_UnionT_cpo)
apply (simp add: fstF_MF_LFP_UnionT_cpo)
apply (simp add: iterative_fstF_semFfun_semFfun)
done

lemma fstF_MF_MT_cpo:
 "[| (Pf::'p=>('p,'a) proc) = PNfun; FPmode = CPOmode | FPmode = MIXmode |]
  ==> (fstF o MF) = (MT::'p => 'a domT)"
apply (simp add: MF_def MT_def)
apply (simp add: semTfix_def semFfix_def)
apply (auto)
apply (simp_all add: fun_eq_iff)
apply (simp_all add: fstF_MF_MT_cpo_lm)
done

(*===================================*
              conclusion
 *===================================*)

lemma fstF_MF_MT:
 "[| (Pf::'p=>('p,'a) proc) = PNfun; 
       FPmode = CPOmode
     | FPmode = CMSmode & guardedfun Pf
     | FPmode = MIXmode |]
  ==> (fstF o MF) = (MT::'p => 'a domT)"
apply (elim conjE disjE)
apply (simp add: fstF_MF_MT_cpo)
apply (simp add: fstF_MF_MT_cms)
apply (simp add: fstF_MF_MT_cpo)
done

end
