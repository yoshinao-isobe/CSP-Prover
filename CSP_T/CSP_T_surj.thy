           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                 August 2005               |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_surj
imports CSP_T_traces
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*********************************************************
            inverse function : DomT => proc
 *********************************************************)

definition
  head_traces :: "'a domT => 'a set"
  where
  head_traces_def :
  "head_traces T == {a. EX t. <Ev a> ^^^ t :t T}"

definition  
  tail_traces :: "'a domT => 'a => 'a domT"
  where
  tail_traces_def :
  "tail_traces T == (%a. {t. <Ev a> ^^^ t :t T}t)"

primrec
  Proc_T_rec  :: "nat => 'a domT => ('p,'a) proc"
where
  "Proc_T_rec 0 = (%T. DIV)"
 | "Proc_T_rec (Suc n)
     = (%T. ((! a:(head_traces T) .. a -> Proc_T_rec n (tail_traces T a)) [+] DIV)
            |~| (IF (<Tick> :t T) THEN SKIP ELSE DIV))"

definition
  Proc_T      :: "'a domT => ('p,'a) proc"
  where
  Proc_T_def :
   "Proc_T T == !nat n .. Proc_T_rec n T"

definition
  ALL_traces_Proc_T_rec :: "'a domT => 'a trace => nat => ('p => 'a domT) => bool"
  where
  ALL_traces_Proc_T_rec_def :
   "ALL_traces_Proc_T_rec T t n M == t :t traces (Proc_T_rec n T) M --> t :t T"

(*********************************************************
                     lemmas
 *********************************************************)

(* tail in domT *)

lemma tail_traces_domT:
   "a : head_traces T ==> {t. <Ev a> ^^^ t :t T} : domT"
apply (simp add: domT_def)
apply (simp add: HC_T1_def)
apply (rule)
apply (simp add: head_traces_def)

apply (simp add: prefix_closed_def)
apply (intro allI impI)
apply (elim conjE exE)
apply (rule memT_prefix_closed)
apply (simp)
apply (simp)
done

(* tail *)

lemma in_tail_traces: 
  "a : head_traces T ==> (s :t tail_traces T a) = (<Ev a> ^^^ s :t T)"
apply (simp add: tail_traces_def)
apply (simp add: tail_traces_domT CollectT_open_memT)
done

(* head & tail *)

lemma head_tail_traces_only_if:
   "<Ev a> ^^^ s :t T ==> a : head_traces T & s :t tail_traces T a"
apply (subgoal_tac "a : head_traces T", simp)
apply (simp add: in_tail_traces head_traces_def)
apply (auto simp add: head_traces_def)
done

lemma head_tail_traces_if:
   "[| a : head_traces T ;  s :t tail_traces T a |]
    ==> <Ev a> ^^^ s :t T"
by (simp add: in_tail_traces)

(* iff *)

lemma head_tail_traces:
   "<Ev a> ^^^ s :t T = (a : head_traces T & s :t tail_traces T a)"
apply (rule iffI)
apply (simp add: head_tail_traces_only_if)
apply (simp add: head_tail_traces_if)
done

(*----------------------------*
 |       Proc_T lemma         |
 *----------------------------*)

(* only if lemma *)

lemma semT_Proc_T_only_if_lm:
  "ALL n T t. t :t traces (Proc_T_rec n T) M --> t :t T"
apply (rule allI)
apply (induct_tac n)

 (* base *)
 apply (simp add: in_traces)

 (* step *)
 apply (fold ALL_traces_Proc_T_rec_def)    (* to prevent infinite simplification *)
 apply (simp (no_asm) add: ALL_traces_Proc_T_rec_def)
 apply (simp add: in_traces)
 apply (intro allI impI)
 apply (elim conjE exE bexE disjE)
 apply (simp)
 apply (simp)
 apply (unfold ALL_traces_Proc_T_rec_def)
 apply (drule_tac x="tail_traces T a" in spec)
 apply (drule_tac x="s" in spec)
 apply (simp add: head_tail_traces)
done

lemma semT_Proc_T_only_if:
  "EX n. t :t traces (Proc_T_rec n T) M ==> t :t T"
apply (erule exE)
apply (insert semT_Proc_T_only_if_lm[of M])
apply (drule_tac x="n" in spec)
apply (drule_tac x="T" in spec)
apply (drule_tac x="t" in spec)
by (simp)

(* if lemma *)

lemma semT_Proc_T_if_lm:
  "ALL t T. t :t T
   --> t :t traces (Proc_T_rec (lengtht t) T) M"
apply (rule allI)
apply (induct_tac t rule: induct_trace)

 (* <> *)
 apply (simp)

 (* <Tick> *)
 apply (intro allI impI)
 apply (simp add: in_traces)

 (* [Ev a] ^^^ s *)
 apply (intro allI impI)
 apply (simp add: in_traces)
 apply (drule_tac x="tail_traces T a" in spec)
 apply (simp add: head_tail_traces)
done

lemma semT_Proc_T_if:
  "t :t T
   ==> t :t traces (Proc_T_rec (lengtht t) T) M"
by (simp add: semT_Proc_T_if_lm)

(*----------------------------*
 |    Proc_T lemma (main)     |
 *----------------------------*)

lemma semT_Proc_T: "[[ Proc_T T ]]Tf M = T"
apply (simp add: Proc_T_def)
apply (rule order_antisym)

 (* <= *)
 apply (rule)
 apply (simp add: semT_def semTf_def)
 apply (simp add: in_traces)
 apply (erule disjE, simp)
 apply (elim conjE exE)
 apply (rule semT_Proc_T_only_if)
 apply (rule_tac x="n" in exI) 
 apply (simp)

 (* => *)
 apply (rule)
 apply (simp add: semT_def semTf_def)
 apply (simp add: in_traces)
 apply (rule disjI2)
 apply (rule_tac x="lengtht t" in exI) 
 apply (simp add: semT_Proc_T_if)
done

lemma traces_Proc_T: "traces (Proc_T T) M = T"
by (simp add: semT_Proc_T[simplified semT_def semTf_def])

(*----------------------------*
 |   [[ ]]T is surjective     |
 *----------------------------*)

theorem EX_proc_domT: "ALL T. EX P::('p,'a) proc. [[P]]T = T"
apply (rule allI)
apply (rule_tac x="Proc_T T" in exI)
apply (simp add: semT_def semT_Proc_T)
done

theorem surj_domT: "surj (%P::('p,'a) proc. [[P]]T)"
apply (simp add: surj_def)
apply (rule allI)
apply (rule_tac x=" Proc_T y" in exI)
apply (simp add: semT_def semT_Proc_T)
done

(****************** to add them again ******************)

declare disj_not1   [simp]

end
