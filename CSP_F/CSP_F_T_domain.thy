           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                 August 2007               |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_T_domain
imports CSP_F_domain
begin

(*=======================================================*
                 make 'a domF from 'a domT 
     (this theory is not important and can be removed)
 *=======================================================*)

definition
  traces_to_failures :: "'a domT => 'a setF"
  where
  traces_to_failures_def :
    "traces_to_failures T == 
        {f. (EX s. (EX X. f = (s ^^^ <Tick>, X)) & s ^^^ <Tick> :t T) |
            (EX s X. f = (s, X) & noTick s & s ^^^ <Tick> :t T & X <= Evset)}f"

(*********************************************************
                        setF
 *********************************************************)

(* F2 *)

lemma traces_to_failures_in_setF: 
  "{f. (EX s. (EX X. f = (s ^^^ <Tick>, X)) & s ^^^ <Tick> :t T) |
            (EX s X. f = (s, X) & noTick s & s ^^^ <Tick> :t T & X <= Evset)} : setF"
by (auto simp add: setF_def HC_F2_def)

(* in *)

lemma in_traces_to_failures: 
  "(s, X) :f traces_to_failures T =
            ((EX t. s = t ^^^ <Tick> & t ^^^ <Tick> :t T) |
             (noTick s & s ^^^ <Tick> :t T & X <= Evset))"
apply (simp add: memF_def)
apply (simp add: traces_to_failures_def)
apply (simp add: Abs_setF_inverse traces_to_failures_in_setF)
done

(*********************************************************
                        domF
 *********************************************************)

(* T2 *)

lemma traces_to_failures_T2 : 
   "HC_T2 (T, traces_to_failures T)"
apply (simp add: HC_T2_def)
apply (simp add: in_traces_to_failures)
apply (auto)
apply (rule memT_prefix_closed, simp)
apply (simp add: prefix_def)
apply (rule_tac x="<Tick>" in exI)
apply (simp)
done

(* F3 *)

lemma traces_to_failures_F3 : 
   "HC_F3 (T, traces_to_failures T)"
apply (simp add: HC_F3_def)
apply (simp add: in_traces_to_failures)
apply (auto)
apply (case_tac "x = Tick")
 apply (drule_tac x="Tick" in spec)
 apply (simp)
 apply (simp add: Evset_def)
done

(* T3_F4 *)

lemma traces_to_failures_T3_F4 : 
   "HC_T3_F4 (T, traces_to_failures T)"
apply (simp add: HC_T3_F4_def)
apply (simp add: in_traces_to_failures)
apply (auto)
done

(*** traces_to_failures_domF ***)

lemma traces_to_failures_domF[simp]: "(T, traces_to_failures T) : domF"
apply (simp add: domF_iff)
apply (simp add: traces_to_failures_T2)
apply (simp add: traces_to_failures_F3)
apply (simp add: traces_to_failures_T3_F4)
done

(*********************************************************
                        relation
 *********************************************************)

lemma traces_to_failures_EX: "ALL T. EX F. T = fstF F"
apply (rule)
apply (rule_tac x="(T ,, traces_to_failures T)" in exI)
apply (simp add: pairF_fstF)
done

lemma traces_to_failures_subset:
   "T1 <= T2 ==> traces_to_failures T1 <= traces_to_failures T2"
apply (rule)
apply (simp add: in_traces_to_failures)
apply (auto)
done

lemma traces_to_failures_refF:
   "T1 <= T2 ==> EX F1 F2. T1 = fstF F1 & T2 = fstF F2 & F1 <= F2"
apply (simp add: subdomF_decompo)
apply (rule_tac x="(T1 ,, traces_to_failures T1)" in exI)
apply (simp add: pairF_fstF)
apply (rule_tac x="(T2 ,, traces_to_failures T2)" in exI)
apply (simp add: pairF_fstF)
apply (simp add: pairF_sndF)
apply (simp add: traces_to_failures_subset)
done

(*** fun ***)

lemma traces_to_failures_fun_EX: "ALL Tf. EX Ff. Tf = fstF o Ff"
apply (simp add: fun_eq_iff)
apply (rule)
apply (rule_tac x="(%x. (Tf x ,, traces_to_failures (Tf x)))" in exI)
apply (simp add: pairF_fstF)
done

lemma traces_to_failures_fun_refF:
   "Tf1 <= Tf2 ==> EX Ff1 Ff2. Tf1 = fstF o Ff1 & Tf2 = fstF o Ff2 & Ff1 <= Ff2"
apply (rule_tac x="(%x. (Tf1 x ,, traces_to_failures (Tf1 x)))" in exI)
apply (rule_tac x="(%x. (Tf2 x ,, traces_to_failures (Tf2 x)))" in exI)
apply (simp add: fun_eq_iff)
apply (simp add: pairF_fstF)
apply (simp add: order_prod_def)
apply (rule)
apply (simp add: subdomF_decompo)
apply (simp add: pairF_fstF)
apply (simp add: pairF_sndF)
apply (simp add: traces_to_failures_subset)
done

end
