           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                 August 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_surj
imports CSP_F_domain CSP_T.CSP_T_surj
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*********************************************************
            inverse function : DomT => proc
 *********************************************************)

definition
  head_failures :: "'a setF => 'a set"
  where
  head_failures_def :
  "head_failures F == {a. EX t X. (<Ev a> ^^^ t, X) :f F}"
  
definition  
  tail_failures :: "'a setF => 'a => 'a setF"
  where
  tail_failures_def :
  "tail_failures F == (%a. {(t,X). (<Ev a> ^^^ t, X) :f F}f)"

primrec
  Proc_F_rec   :: "nat => 'a domF => ('p,'a) proc"
where
  "Proc_F_rec 0 = (%SF. !set X:{X. EX Y. (<>,Y) :f sndF SF & 
                                  Ev ` X = Evset - Y & Tick : Y &
                                  (ALL a:X. <Ev a> :t fstF SF)} .. 
                        (? x:X -> DIV))"
 |"Proc_F_rec (Suc n)
     = (%SF. (! a:(head_failures (sndF SF)) .. a -> 
              Proc_F_rec n (tail_traces (fstF SF) a ,,
                           tail_failures (sndF SF) a)) [+] DIV)"
definition
  Proc_F    :: "'a domF => ('p,'a) proc"
  where
  Proc_F_def :
   "Proc_F SF == Proc_T (fstF SF) |~| (!nat n .. Proc_F_rec n SF)"

(*********************************************************
                     lemmas
 *********************************************************)

(* tail in setF *)

lemma tail_failures_setF: "{(t,X). (<Ev a> ^^^ t, X) :f F} : setF"
apply (simp add: setF_def)
apply (simp add: HC_F2_def)
apply (intro allI impI)
apply (rule memF_F2)
by (auto)

(* tail *)

lemma in_tail_failures: 
  "((s,X) :f tail_failures F a) = ((<Ev a> ^^^ s, X) :f F)"
apply (simp add: tail_failures_def)
apply (simp add: tail_failures_setF CollectF_open_memF)
done

(* head & tail *)

lemma head_tail_failures_only_if:
   "(<Ev a> ^^^ s, X) :f F ==> a : head_failures F & (s,X) :f tail_failures F a"
apply (simp add: in_tail_failures)
apply (auto simp add: head_failures_def)
done

(* iff *)

lemma head_tail_failures:
   "(<Ev a> ^^^ s, X) :f F = (a : head_failures F & (s,X) :f tail_failures F a)"
apply (rule iffI)
apply (simp add: head_tail_failures_only_if)
apply (simp add: in_tail_failures)
done

(*** domF ***)

(* head *)

lemma head_failures_traces: 
  "a : head_failures (sndF SF) ==> a : head_traces (fstF SF)"
apply (simp add: head_failures_def)
apply (simp add: head_traces_def)
apply (elim exE)
apply (rule_tac x="t" in exI)
apply (simp add: pairF_domF_T2)
done

(* T2 *)

lemma tail_traces_failures_T2: 
  "HC_T2 (tail_traces (fstF SF) a , tail_failures (sndF SF) a)"
apply (simp add: HC_T2_def in_traces in_failures)
apply (intro allI impI)
apply (elim exE)
apply (simp add: in_tail_failures)
apply (subgoal_tac "a : head_traces (fstF SF)")
apply (simp add: in_tail_traces)
apply (simp add: pairF_domF_T2)

apply (simp add: head_tail_failures)
apply (simp add: head_failures_traces)
done

(* F3 *)

lemma tail_traces_failures_F3: 
  "a : head_traces (fstF SF) ==>
   HC_F3 (tail_traces (fstF SF) a , tail_failures (sndF SF) a)"
apply (simp add: HC_F3_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE)

apply (simp add: in_tail_failures)
apply (simp add: in_tail_traces)
apply (rule pairF_domF_F3)
apply (simp)
apply (simp)
apply (simp add: appt_assoc_sym)
done

(* T3_F4 *)

lemma tail_traces_failures_T3_F4: 
  "a : head_traces (fstF SF) ==>
   HC_T3_F4 (tail_traces (fstF SF) a , tail_failures (sndF SF) a)"
apply (simp add: HC_T3_F4_def in_traces in_failures)
apply (intro allI impI)
apply (elim conjE)

apply (simp add: in_tail_failures)
apply (simp add: in_tail_traces)
apply (simp add: appt_assoc_sym)
apply (simp add: pairF_domF_F4)
apply (simp add: pairF_domF_T3)
done

lemma tail_traces_failures_domF: 
  "a : head_traces (fstF SF) | a : head_failures (sndF SF) 
   ==> (tail_traces (fstF SF) a , tail_failures (sndF SF) a) : domF"
apply (simp add: domF_iff)
apply (subgoal_tac "a : head_traces (fstF SF)")
apply (simp add: tail_traces_failures_T2)
apply (simp add: tail_traces_failures_F3)
apply (simp add: tail_traces_failures_T3_F4)
apply (auto simp add: head_failures_traces)
done

(*-------------------------------------*
 |   failures (Proc_T_rec n) --> Tick  |
 *-------------------------------------*)

lemma failures_Proc_T_rec_noTick_lm: 
  "ALL s T. ((s, X) :f failures (Proc_T_rec n T) M & noTick s)
   --> (EX t. s ^^^ t ^^^ <Tick> :t T & noTick t)"
apply (induct_tac n)

(* base *)
 apply (simp add: in_traces)
 apply (simp add: in_failures)

(* step *)
 apply (intro allI impI)
 apply (simp add: in_failures)
 apply (elim conjE exE disjE bexE)
 apply (simp_all)

  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="(tail_traces T a)" in spec)
  apply (simp)
  apply (elim conjE exE)
  apply (rule_tac x="t" in exI)
  apply (simp add: appt_assoc)
  apply (simp add: head_tail_traces)

  apply (simp add: in_traces)
  apply (simp add: in_traces)

  apply (case_tac "<Tick> :t T")

   apply (simp add: in_failures)
   apply (erule disjE)
    apply (rule_tac x="<>" in exI)
    apply (simp)
    apply (simp)

   apply (simp add: in_failures)
done

lemma failures_Proc_T_rec_noTick: 
  "[| (s, X) :f failures (Proc_T_rec n T) M ; noTick s|]
   ==> (EX t. s ^^^ t ^^^ <Tick> :t T & noTick t)"
by (simp add: failures_Proc_T_rec_noTick_lm)

lemma failures_Proc_T_rec_lm: 
  "ALL s T. ((s, X) :f failures (Proc_T_rec n T) M)
   --> s :t T"
apply (induct_tac n)

(* base *)
 apply (simp add: in_traces)
 apply (simp add: in_failures)

(* step *)
 apply (intro allI impI)
 apply (simp add: in_failures)
 apply (elim conjE exE disjE bexE)
 apply (simp_all)

  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="(tail_traces T a)" in spec)
  apply (simp add: head_tail_traces)

  apply (case_tac "<Tick> :t T")
  apply (auto simp add: in_failures)
done

lemma failures_Proc_T_rec: 
  "(s, X) :f failures (Proc_T_rec n T) M ==> s :t T"
by (simp add: failures_Proc_T_rec_lm)

lemma failures_Proc_T_rec_T3: 
  "[| (s, X) :f failures (Proc_T_rec n (fstF SF)) M ; noTick s |]
   ==> (EX t. (s ^^^ t ^^^ <Tick>,Y) :f (sndF SF) & noTick t)"
apply (insert failures_Proc_T_rec_noTick_lm[of X n M])
apply (drule_tac x="s" in spec)
apply (drule_tac x="fstF SF" in spec)
apply (simp)
apply (elim conjE exE)
apply (rule_tac x="t" in exI)
apply (simp)
apply (simp add: appt_assoc_sym)
apply (simp add: pairF_domF_T3)
done

(*** head T --> head F **)

lemma head_traces_failures_noTick:
  "[| a : head_traces (fstF SF);
     (s, X) :f failures (Proc_T_rec n (tail_traces (fstF SF) a)) M; noTick s|]
   ==> a : head_failures (sndF SF)"
apply (insert failures_Proc_T_rec_noTick_lm[of X n M])
apply (drule_tac x="s" in spec)
apply (drule_tac x="tail_traces (fstF SF) a" in spec)
apply (simp)
apply (elim conjE exE)
apply (simp add: in_tail_traces)

apply (simp add: head_failures_def)
apply (rule_tac x="s ^^^ t ^^^ <Tick>" in exI)
apply (rule_tac x="X" in exI)
apply (simp add: appt_assoc_sym)
apply (simp add: pairF_domF_T3)
done

(*** head_traces_failures ***)

lemma head_traces_failures:  (* not used *)
  "[| a : head_traces (fstF SF);
     (s, X) :f failures (Proc_T_rec n (tail_traces (fstF SF) a)) M |]
   ==> a : head_failures (sndF SF)"
apply (case_tac "noTick s")
apply (simp add: head_traces_failures_noTick)
apply (simp add: noTick_def)

apply (simp add: Tick_in_sett)
apply (elim conjE exE)

apply (insert failures_Proc_T_rec_lm[of X n M])
apply (drule_tac x="s" in spec)
apply (drule_tac x="tail_traces (fstF SF) a" in spec)

apply (simp add: in_tail_traces)
apply (simp add: appt_assoc_sym)

apply (simp add: head_failures_def)
apply (rule_tac x="t ^^^ <Tick>" in exI)
apply (rule_tac x="X" in exI)
apply (simp add: appt_assoc_sym)
apply (simp add: pairF_domF_T3)
done

(*----------------------------*
 |         Proc_T lemma       |
 *----------------------------*)

(* traces(Proc_F_rec) => fst SF (lm) *)

lemma Proc_F_to_T_lm:
   "ALL SF t. t :t traces (Proc_F_rec n SF) M --> t :t fstF SF"
apply (induct_tac n)

(* base *)
 apply (simp add: in_traces)
 apply (intro allI impI)
 apply (elim conjE exE)

 apply (erule disjE, simp)
 apply (elim conjE exE)
 apply (simp)

(* step *)
 apply (intro allI impI)
 apply (simp add: in_traces)
 apply (elim conjE exE disjE bexE)
 apply (simp_all)
 apply (drule_tac x="(tail_traces (fstF SF) a ,, tail_failures (sndF SF) a)" in spec)
 apply (drule_tac x="s" in spec)
 apply (simp)
 apply (simp add: tail_traces_failures_domF pairF_fstF)
 apply (simp add: in_tail_traces head_failures_traces)
done

(* traces(Proc_F_rec) => fst SF *)

lemma Proc_F_to_T:
   "t :t traces (Proc_F_rec n SF) M ==> t :t fstF SF"
by (simp add: Proc_F_to_T_lm)

(* traces(Proc_F_rec) => fst SF (lm) *)

lemma Proc_T_to_F_lm:
   "ALL SF s X.
    (s, X) :f failures (Proc_T_rec n (fstF SF)) M --> (s, X) :f sndF SF"
apply (induct_tac n)

(* base *)
 apply (simp add: in_failures)

(* step *)
 apply (intro allI impI)
 apply (simp add: in_failures)
 apply (elim conjE exE disjE bexE)
 apply (simp_all)

  apply (drule_tac x="(tail_traces (fstF SF) a ,, tail_failures (sndF SF) a)" in spec)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="X" in spec)
  apply (simp add: tail_traces_failures_domF pairF_fstF)
  apply (simp add: tail_traces_failures_domF pairF_sndF)
  apply (simp add: in_tail_failures)

  apply (simp add: in_traces)
  apply (simp add: in_traces)

  apply (case_tac "<Tick> :t fstF SF")
   apply (simp add: in_failures)
   apply (erule disjE)
    apply (simp add: pairF_domF_F2_F4)
    apply (simp add: pairF_domF_T3_Tick)

  apply (simp add: in_failures)
done

(* traces(Proc_F_rec) => fst SF *)

lemma Proc_T_to_F:
  "(s, X) :f failures (Proc_T_rec n (fstF SF)) M ==> (s, X) :f sndF SF"
by (simp add: Proc_T_to_F_lm)

(* failures(Proc_F_rec) => snd SF (lm) *)

lemma Proc_F_to_F_lm:
   "ALL SF s X. (s, X) :f failures (Proc_F_rec n SF) M --> (s, X) :f sndF SF"
apply (induct_tac n)

(* base *)
 apply (simp add: in_failures)
 apply (intro allI impI)
 apply (elim conjE exE)
 apply (rule memF_F2)
 apply (simp)
 apply (simp add: Evset_def)
 apply (blast)

(* step *)
 apply (intro allI impI)
 apply (simp add: in_failures)

 apply (elim conjE exE bexE disjE)
 apply (simp_all)

  apply (drule_tac x="(tail_traces (fstF SF) a ,, tail_failures (sndF SF) a)" in spec)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="X" in spec)
  apply (simp add: tail_traces_failures_domF pairF_fstF)
  apply (simp add: tail_traces_failures_domF pairF_sndF)
  apply (simp add: head_tail_failures)

  apply (simp add: in_traces)
  apply (simp add: in_traces)
done

lemma Proc_F_to_F:
   "(s, X) :f failures (Proc_F_rec n SF) M ==> (s, X) :f sndF SF"
by (simp add: Proc_F_to_F_lm)

(* sndF SF => failures (Proc_F_rec) lm *)

lemma F_Proc_F_lm:
   "ALL SF X. ((s, X) :f sndF SF & noTick s & (Tick : X | s ^^^ <Tick> ~:t fstF SF))
             --> (s, X) :f failures (Proc_F_rec (lengtht s) SF) M"
apply (induct_tac s rule: induct_trace)

 (* <> *)
 apply (intro allI impI)
 apply (simp add: in_failures)
 apply (rule_tac x="{a. Ev a ~: X & <Ev a> :t fstF SF}" in exI)
 apply (rule)

  apply (elim conjE)
  apply (erule disjE)

   (* Tick : X *)
   apply (rule_tac x="X Un {(Ev a)|a. <Ev a> ~:t fstF SF}" in exI)
   apply (simp)
   apply (rule)

    apply (rule pairF_domF_F3)
     apply (simp)
     apply (simp)
     apply (force)
    apply (simp add: Evset_def not_Tick_to_Ev)
    apply (force)

   (* <Tick> ~:t fstF SF *)
   apply (rule_tac x="X Un ({Tick} Un {(Ev a)|a. <Ev a> ~:t fstF SF})" in exI)
   apply (rule)

    apply (rule pairF_domF_F3)
     apply (simp)
     apply (simp)
     apply (force)

    apply (simp add: Evset_def not_Tick_to_Ev)
    apply (force)
    apply (force)

 (* <Tick> *)
 apply (simp)

 (* <Ev a> ^^^ s *)
 apply (intro allI impI)
 apply (simp add: in_failures)
 apply (simp add: head_tail_failures)

 apply (drule_tac x="(tail_traces (fstF SF) a ,, tail_failures (sndF SF) a)" in spec)
 apply (drule_tac x="X" in spec)
 apply (simp add: tail_traces_failures_domF pairF_fstF pairF_sndF)
 apply (elim conjE exE disjE)
 apply (simp)

 apply (simp add: appt_assoc)
 apply (simp add: head_failures_traces head_tail_traces)
done

(* sndF SF => failures (Proc_F_rec) *)

lemma F_Proc_F:
   "[| (s, X) :f sndF SF ; noTick s ; Tick : X | s ^^^ <Tick> ~:t fstF SF |]
    ==> (s, X) :f failures (Proc_F_rec (lengtht s) SF) M"
by (simp add: F_Proc_F_lm)

(* sndF SF => failures (Proc_T_rec) (noTick) lm *)

declare lengtht_app_event_Suc_head [simp del]
declare lengtht_app_decompo1       [simp del]
declare lengtht_app_decompo2       [simp del]
declare Proc_T_rec.simps            [simp del]

lemma F_Proc_T_noTick_lm:
   "ALL SF X. (s, X) :f sndF SF & noTick s & Tick ~: X & s ^^^ <Tick> :t fstF SF
    --> (s, X) :f failures (Proc_T_rec (Suc (lengtht s)) (fstF SF)) M"
apply (induct_tac s rule: induct_trace)

 (* <> *)
 apply (intro allI impI)
 apply (simp add: Proc_T_rec.simps in_failures)
 apply (simp add: Evset_def)
 apply (fast)

 (* <Tick> *)
 apply (intro allI impI)
 apply (simp add: Proc_T_rec.simps in_failures)

 (* <Ev a> ^^^ s *)
 apply (intro allI impI)
 apply (simp (no_asm) add: Proc_T_rec.simps)
 apply (simp add: in_failures)
 apply (elim conjE)
 apply (simp add: appt_assoc)
 apply (simp add: head_tail_traces)

 apply (drule_tac x="(tail_traces (fstF SF) a ,, tail_failures (sndF SF) a)" in spec)
 apply (drule_tac x="X" in spec)
 apply (simp)
 apply (elim conjE)
 apply (simp add: tail_traces_failures_domF pairF_fstF pairF_sndF)
 apply (simp add: head_tail_failures)
 apply (simp add: lengtht_app_event_Suc_head)
done

(* sndF SF => failures (Proc_T_rec) noTick *)

lemma F_Proc_T_noTick:
   "[| (s, X) :f sndF SF ; noTick s ; Tick ~: X ; s ^^^ <Tick> :t fstF SF |]
    ==> (s, X) :f failures (Proc_T_rec (Suc (lengtht s)) (fstF SF)) M"
by (simp add: F_Proc_T_noTick_lm)

declare lengtht_app_event_Suc_head [simp]
declare lengtht_app_decompo1       [simp]
declare lengtht_app_decompo2       [simp]
declare Proc_T_rec.simps            [simp]

(* sndF SF => failures (Proc_T_rec) (Tick) lm *)

lemma F_Proc_T_Tick_lm:
   "ALL SF X. ((s, X) :f sndF SF & ~ noTick s)
    --> (s, X) :f failures (Proc_T_rec (lengtht s) (fstF SF)) M"
apply (induct_tac s rule: induct_trace)

 (* <> *)
 apply (intro allI impI)
 apply (simp add: in_failures)

 (* <Tick> *)
 apply (intro allI impI)
 apply (simp add: in_failures)
 apply (simp add: pairF_domF_T2)

 (* <Ev a> ^^^ s *)
 apply (intro allI impI)
 apply (simp add: in_failures)
 apply (elim conjE)
 apply (simp add: head_tail_failures)

 apply (drule_tac x="(tail_traces (fstF SF) a ,, tail_failures (sndF SF) a)" in spec)
 apply (drule_tac x="X" in spec)
 apply (simp add: tail_traces_failures_domF pairF_fstF pairF_sndF)
 apply (elim conjE)
 apply (simp add: head_failures_traces)
done

(* sndF SF => failures (Proc_T_rec) noTick *)

lemma F_Proc_T_Tick:
   "[| (s, X) :f sndF SF; ~ noTick s |]
           ==> (s, X) :f failures (Proc_T_rec (lengtht s) (fstF SF)) M"
by (simp add: F_Proc_T_Tick_lm)

(*==================================================*
 |                Proc_F lemma (main)               |
 *==================================================*)

lemma semF_Proc_F: "[[ Proc_F SF ]]Ff M = SF"
apply (simp add: Proc_F_def)
apply (rule order_antisym)

 (* <= *)
 apply (simp add: subdomF_decompo)
 apply (rule conjI)

  (* Proc <= fstF SF *)
  apply (rule)
  apply (simp add: in_traces)
  apply (simp add: semT_Proc_T[simplified semTf_def])
  apply (erule disjE, simp)
  apply (erule disjE, simp)
  apply (elim conjE exE)
  apply (simp add: Proc_F_to_T)

  (* Proc <= sndF SF *)
  apply (rule)
  apply (simp add: in_failures)
  apply (erule disjE)

   (* Proc T <= sndF SF *)
   apply (simp add: Proc_T_def)
   apply (simp add: in_failures)
   apply (erule exE)
   apply (simp add: Proc_T_to_F)

   (* Proc F <= sndF SF *)
   apply (erule exE)
   apply (simp add: Proc_F_to_F)

 (* <= *)
 apply (simp add: subdomF_decompo)
 apply (rule conjI)

  (* fstF SF <= Proc *)
  apply (rule)
  apply (simp add: in_traces)
  apply (simp add: semT_Proc_T[simplified semTf_def])

  (* sndF SF <= Proc *)
  apply (rule)
  apply (simp add: in_failures)
  apply (case_tac "noTick s & (Tick : X | s ^^^ <Tick> ~:t fstF SF)")
   apply (rule disjI2)
   apply (rule_tac x="lengtht s" in exI)
   apply (simp add: F_Proc_F)

   apply (simp)
   apply (rule disjI1)
   apply (simp add: Proc_T_def)
   apply (simp add: in_failures)
   apply (case_tac "noTick s")

    (* noTick s & s ^^^ <Tick> :t fstF SF *)
    apply (simp)
    apply (rule_tac x="Suc (lengtht s)" in exI)
    apply (simp add: F_Proc_T_noTick del: Proc_T_rec.simps)

    (* ~ noTick s *)
    apply (rule_tac x="lengtht s" in exI)
    apply (simp add: F_Proc_T_Tick)
done

(*----------------------------*
 |   [[ ]]F is surjective     |
 *----------------------------*)

theorem EX_proc_domF: "ALL SF. EX P::('p,'a) proc. [[P]]F = SF"
apply (rule allI)
apply (rule_tac x="Proc_F SF" in exI)
apply (simp add: semF_def semF_Proc_F)
done

theorem surj_domF: "surj (%P::('p,'a) proc. [[P]]F)"
apply (simp add: surj_def)
apply (rule allI)
apply (rule_tac x="Proc_F y" in exI)
apply (simp add: semF_def semF_Proc_F)
done

(*----------------------------*
 |   failures and Proc_F SF   |
 *----------------------------*)

lemma failures_Proc_F: "failures (Proc_F SF) M = sndF SF"
apply (insert semF_Proc_F[of SF M])
apply (simp add: semFf_def)
apply (simp add: eqF_decompo)
done

(*----------------------------*
 |    traces and Proc_F SF    |
 *----------------------------*)

lemma make_failures_from_T:
  "(T , failures (Proc_T T) M) : domF"
apply (subgoal_tac
  "(traces (Proc_T T) (fstF o M) , failures (Proc_T T) M) : domF")
apply (simp only: traces_Proc_T)
apply (simp)
done

lemma traces_Proc_F: "traces ((Proc_F SF)::('p,'a) proc) M = fstF SF"
apply (insert semF_Proc_F[of SF 
  "(%p. (traces ((Proc_T (M p))::('p,'a) proc) (fstF o M'),,failures(Proc_T (M p)) M'))"])
apply (simp add: semFf_def)
apply (simp add: eqF_decompo)
apply (simp add: fstF_proc_domF_fun)
apply (simp add: traces_Proc_T)
done

lemma traces_Proc_T_F:
  "traces (Proc_T (fstF SF)) M = traces (Proc_F SF) M"
apply (simp add: traces_Proc_T)
apply (simp add: traces_Proc_F)
done

(*==========================================================*
 |                                                          |
 |              Generic Internal Choice                     |
 |                                                          |
 *==========================================================*)

definition
  Gen_int_choice_F_plus ::
    "('p,'a) proc set => ('p,'a) proc"    ("(1|~~|F _)" [900] 68) 
  where
  Gen_int_choice_F_plus_def:
        "|~~|F Ps == Proc_F( (UnionT {(traces(P) (fstF o MF))|P. P:Ps},,
                              UnionF {(failures(P) MF) |P. P:Ps}))"

(* lemmas *)

lemma traces_Gen_int_choice_F_plus:
   "Ps ~= {} ==> traces ( |~~|F Ps ) M = (UnionT {(traces(P) (fstF o MF)) |P. P:Ps})"
apply (simp add: Gen_int_choice_F_plus_def)
apply (simp add: traces_Proc_F)
apply (simp add: pairF non_empty_UnionT_UnionF_domF)
done

lemma failures_Gen_int_choice_F_plus:
   "Ps ~= {} ==> failures ( |~~|F Ps ) M = (UnionF {(failures(P) MF) |P. P:Ps})"
apply (simp add: Gen_int_choice_F_plus_def)
apply (simp add: failures_Proc_F)
apply (simp add: pairF non_empty_UnionT_UnionF_domF)
done

lemma semF_Gen_int_choice_F_plus:
   "Ps ~= {} ==> [[ |~~|F Ps ]]F = 
                 (UnionT {(traces(P) (fstF o MF)) |P. P:Ps}  ,, 
                 (UnionF {(failures(P) MF) |P. P:Ps}))"
apply (simp add: semF_def semFf_def)
apply (simp add: traces_Gen_int_choice_F_plus failures_Gen_int_choice_F_plus)
done

lemma in_traces_Gen_int_choice_F_plus:
   "Ps ~= {} ==> t :t traces ( |~~|F Ps ) M = (EX P:Ps. t :t traces(P) (fstF o MF))"
apply (simp add: traces_Gen_int_choice_F_plus)
apply (subgoal_tac "{(traces P) |P. P : Ps} ~= {}")
apply (auto)
done

lemma in_failures_Gen_int_choice_F_plus:
   "Ps ~= {} ==> f :f failures ( |~~|F Ps ) M = (EX P:Ps. f :f failures(P) MF)"
apply (simp add: failures_Gen_int_choice_F_plus)
apply (subgoal_tac "{(traces P) |P. P : Ps} ~= {}")
apply (auto)
done

(****************** to add them again ******************)

declare disj_not1   [simp]

end
