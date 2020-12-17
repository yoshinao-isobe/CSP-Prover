           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  April 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory FNF_F_nf_id
imports FNF_F_nf_def
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*  The following simplification rules are deleted in this theory file *)
(*       P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))        *)
(* Isabelle 2017 *)
declare if_split [split del]

(*****************************************************************

         1. =F --> =
         2. 
         3. 

 *****************************************************************)

(*---------------------------------------------------------*
 |              syntactically identical ?                  |
 *---------------------------------------------------------*)

(*===========================================================*
 |                      fnfF_nat_proc                        |
 *===========================================================*)

(*** Q ***)

lemma fnfF_syntactical_equality_Q_lm:
  "[| ? :A1 -> Pf1 [+] DIV |~| !set Y:Ys1 .. ? a:Y -> DIV <=F[M1,M2] 
      ? :A2 -> Pf2 [+] SKIP |~| !set Y:Ys2 .. ? a:Y -> DIV |]
   ==> False"
apply (simp add: cspF_semantics)
apply (elim conjE)
apply (simp add: subdomT_iff)
apply (drule_tac x="<Tick>" in spec)
apply (simp add: in_traces)
done

lemma fnfF_syntactical_equality_Q:
  "[| Q1 = SKIP | Q1 = DIV ; Q2 = SKIP | Q2 = DIV ;
      ? :A1 -> Pf1 [+] Q1 |~| !set Y:Ys1 .. ? a:Y -> DIV =F[M1,M2] 
      ? :A2 -> Pf2 [+] Q2 |~| !set Y:Ys2 .. ? a:Y -> DIV |]
   ==> Q1 = Q2"
apply (elim disjE)
apply (simp_all  add: cspF_eq_ref_iff)
apply (insert fnfF_syntactical_equality_Q_lm
       [of A2 Pf2 Ys2 M2 M1 A1 Pf1 Ys1])
apply (simp)
apply (insert fnfF_syntactical_equality_Q_lm
       [of A1 Pf1 Ys1 M1 M2 A2 Pf2 Ys2])
apply (simp)
done

(*** A ***)

lemma fnfF_syntactical_equality_Union_lm:
  "[| Union Ys1 <= A1 ; Union Ys2 <= A2 ; 
      Q = SKIP | Q = DIV ;
      ? :A1 -> Pf1 [+] Q |~| !set Y:Ys1 .. ? a:Y -> DIV <=F[M1,M2] 
      ? :A2 -> Pf2 [+] Q |~| !set Y:Ys2 .. ? a:Y -> DIV |]
   ==> A2 <= A1"
apply (simp add: cspF_semantics)
apply (elim conjE)
apply (simp add: subdomT_iff)
apply (rule subsetI)
apply (drule_tac x="<Ev x>" in spec)
apply (erule disjE)
apply (simp add: in_traces)
apply (elim disjE bexE)
apply (simp)
apply (force)
apply (simp add: in_traces)
apply (elim disjE bexE)
apply (simp)
apply (force)
done

lemma fnfF_syntactical_equality_Union:
  "[| Union Ys1 <= A1 ; Union Ys2 <= A2 ; 
      Q = SKIP | Q = DIV ;
      ? :A1 -> Pf1 [+] Q |~| !set Y:Ys1 .. ? a:Y -> DIV =F[M1,M2] 
      ? :A2 -> Pf2 [+] Q |~| !set Y:Ys2 .. ? a:Y -> DIV |]
   ==> A1 = A2"
apply (simp add: cspF_eq_ref_iff)
apply (rule equalityI)
apply (simp add: fnfF_syntactical_equality_Union_lm[of Ys2 A2 Ys1 A1 Q Pf2 M2 M1 Pf1])
apply (simp add: fnfF_syntactical_equality_Union_lm[of Ys1 A1 Ys2 A2 Q Pf1 M1 M2 Pf2])
done

(*** Yf ***)

lemma fnfF_syntactical_equality_Yf_DIV_lm:
  "[| Union Ys1 <= A ; Union Ys2 <= A ; 
      fnfF_set_condition A Ys1 ;
      ? :A -> Pf1 [+] DIV |~| !set Y:Ys1 .. ? a:Y -> DIV <=F[M1,M2]
      ? :A -> Pf2 [+] DIV |~| !set Y:Ys2 .. ? a:Y -> DIV |]
   ==> Ys2 <= Ys1"
apply (rule subsetI)
apply (simp add: cspF_semantics)
apply (elim conjE)
apply (simp add: subsetF_iff)
apply (simp add: in_failures)
apply (simp add: in_traces)
apply (drule_tac x="<>" in spec)
apply (simp)
apply (drule_tac x="UNIV - (Ev ` x)" in spec)
apply (drule mp)
apply (rule_tac x="x" in bexI)
apply (simp_all)
apply (elim conjE bexE)
apply (subgoal_tac "X <= x")
apply (unfold fnfF_set_condition_def)
apply (drule_tac x="x" in spec)
apply (drule mp)
apply (rule conjI)
apply (rule_tac x="X" in bexI)
apply (simp)
apply (simp)
apply (rule subsetI)
apply (simp)
apply (rule disjI1)
apply (subgoal_tac "xa : Union Ys2")
apply (force)
apply (force)
apply (simp)

apply (fold fnfF_set_condition_def)
apply (auto)
done

lemma fnfF_syntactical_equality_Yf_SKIP_lm:
  "[| Union Ys1 <= A ; Union Ys2 <= A ; 
      fnfF_set_condition A Ys1 ;
      ? :A -> Pf1 [+] SKIP |~| !set Y:Ys1 .. ? a:Y -> DIV <=F[M1,M2]
      ? :A -> Pf2 [+] SKIP |~| !set Y:Ys2 .. ? a:Y -> DIV |]
   ==> Ys2 <= Ys1"
apply (rule subsetI)
apply (simp add: cspF_semantics)
apply (elim conjE)
apply (simp add: subsetF_iff)
apply (simp add: in_failures)
apply (simp add: in_traces)
apply (drule_tac x="<>" in spec)
apply (simp)
apply (drule_tac x="UNIV - (Ev ` x)" in spec)
apply (drule mp)
apply (rule_tac x="x" in bexI)
apply (simp_all)

apply (case_tac "UNIV - Ev ` x <= Evset")
apply (simp add: Evset_def)
apply (force)

apply (simp)
apply (elim conjE bexE)
apply (subgoal_tac "X <= x")
apply (unfold fnfF_set_condition_def)
apply (drule_tac x="x" in spec)
apply (drule mp)
apply (rule conjI)
apply (rule_tac x="X" in bexI)
apply (simp)
apply (simp)

apply (rule subsetI)
apply (simp)
apply (rule disjI1)
apply (subgoal_tac "xa : Union Ys2")
apply (force)
apply (force)
apply (simp)

apply (fold fnfF_set_condition_def)
apply (auto)
done

lemma fnfF_syntactical_equality_Yf:
  "[| Union Ys1 <= A ; Union Ys2 <= A ; 
      fnfF_set_condition A Ys1 ; fnfF_set_condition A Ys2 ;
      Q = SKIP | Q = DIV ;
      ? :A -> Pf1 [+] Q |~| !set Y:Ys1 .. ? a:Y -> DIV =F[M1,M2]
      ? :A -> Pf2 [+] Q |~| !set Y:Ys2 .. ? a:Y -> DIV |]
   ==> Ys1 = Ys2"
apply (simp add: cspF_eq_ref_iff)
apply (erule disjE)
apply (rule equalityI)
apply (simp add: fnfF_syntactical_equality_Yf_SKIP_lm[of Ys2 A Ys1 Pf2 M2 M1 Pf1])
apply (simp add: fnfF_syntactical_equality_Yf_SKIP_lm[of Ys1 A Ys2 Pf1 M1 M2 Pf2])
apply (rule equalityI)
apply (simp add: fnfF_syntactical_equality_Yf_DIV_lm[of Ys2 A Ys1 Pf2 M2 M1 Pf1])
apply (simp add: fnfF_syntactical_equality_Yf_DIV_lm[of Ys1 A Ys2 Pf1 M1 M2 Pf2])
done

(*** Pf ***)

(* T DIV *)

lemma fnfF_syntactical_equality_Pf_T_DIV_lm:
  "[| a:A ;
      ? :A -> Pf1 [+] DIV |~| !set Y:Ys .. ? a:Y -> DIV <=T[M1,M2]
      ? :A -> Pf2 [+] DIV |~| !set Y:Ys .. ? a:Y -> DIV |]
   ==> Pf1 a <=T[M1,M2] Pf2 a"
apply (simp add: cspT_semantics)

apply (simp add: subdomT_iff)
apply (simp add: in_traces)
apply (intro allI impI)
apply (drule_tac x="<Ev a> ^^^ t" in spec)
apply (insert trace_nil_or_Tick_or_Ev)
apply (drule_tac x="t" in spec)
apply (elim disjE conjE exE)
apply (auto)
done

(* T SKIP *)

lemma fnfF_syntactical_equality_Pf_T_SKIP_lm:
  "[| a:A ;
      ? :A -> Pf1 [+] SKIP |~| !set Y:Ys .. ? a:Y -> DIV <=T[M1,M2]
      ? :A -> Pf2 [+] SKIP |~| !set Y:Ys .. ? a:Y -> DIV |]
   ==> Pf1 a <=T[M1,M2] Pf2 a"
apply (simp add: cspT_semantics)

apply (simp add: subdomT_iff)
apply (simp add: in_traces)
apply (intro allI impI)
apply (drule_tac x="<Ev a> ^^^ t" in spec)
apply (insert trace_nil_or_Tick_or_Ev)
apply (drule_tac x="t" in spec)
apply (elim disjE conjE exE)
apply (auto)
done

(* F DIV *)

lemma fnfF_syntactical_equality_Pf_F_DIV_lm:
  "[| a:A ;
      ? :A -> Pf1 [+] DIV |~| !set Y:Ys .. ? a:Y -> DIV <=F[M1,M2]
      ? :A -> Pf2 [+] DIV |~| !set Y:Ys .. ? a:Y -> DIV |]
   ==> Pf1 a <=F[M1,M2] Pf2 a"
apply (simp add: cspF_cspT_semantics)
apply (erule conjE)
apply (rule conjI)
apply (rule fnfF_syntactical_equality_Pf_T_DIV_lm)
apply (simp)
apply (simp add: comp_def)

apply (simp add: subsetF_iff)
apply (simp add: in_failures)
apply (intro allI impI)
apply (drule_tac x="<Ev a> ^^^ s" in spec)
apply (drule_tac x="X" in spec)
apply (insert trace_nil_or_Tick_or_Ev)
apply (drule_tac x="s" in spec)
apply (elim disjE conjE exE)

apply (force)
apply (force)
apply (force)
done

(* F SKIP *)

lemma fnfF_syntactical_equality_Pf_F_SKIP_lm:
  "[| a:A ;
      ? :A -> Pf1 [+] SKIP |~| !set Y:Ys .. ? a:Y -> DIV <=F[M1,M2]
      ? :A -> Pf2 [+] SKIP |~| !set Y:Ys .. ? a:Y -> DIV |]
   ==> Pf1 a <=F[M1,M2] Pf2 a"
apply (simp add: cspF_cspT_semantics)
apply (erule conjE)
apply (rule conjI)
apply (rule fnfF_syntactical_equality_Pf_T_SKIP_lm)
apply (simp)
apply (simp add: comp_def)

apply (simp add: subsetF_iff)
apply (simp add: in_failures)
apply (intro allI impI)
apply (drule_tac x="<Ev a> ^^^ s" in spec)
apply (drule_tac x="X" in spec)
apply (insert trace_nil_or_Tick_or_Ev)
apply (drule_tac x="s" in spec)
apply (elim disjE conjE exE)

apply (force)
apply (force)
apply (force)
done

lemma fnfF_syntactical_equality_Pf:
  "[| a:A ; Q = SKIP | Q = DIV ;
      ? :A -> Pf1 [+] Q |~| !set Y:Ys .. ? a:Y -> DIV =F[M1,M2]
      ? :A -> Pf2 [+] Q |~| !set Y:Ys .. ? a:Y -> DIV |]
   ==> Pf1 a =F[M1,M2] Pf2 a"
apply (simp add: cspF_eq_ref_iff)
apply (erule disjE)
apply (simp add: fnfF_syntactical_equality_Pf_F_SKIP_lm[of a A Pf1 Ys M1 M2 Pf2])
apply (simp add: fnfF_syntactical_equality_Pf_F_SKIP_lm[of a A Pf2 Ys M2 M1 Pf1])
apply (simp add: fnfF_syntactical_equality_Pf_F_DIV_lm[of a A Pf1 Ys M1 M2 Pf2])
apply (simp add: fnfF_syntactical_equality_Pf_F_DIV_lm[of a A Pf2 Ys M2 M1 Pf1])
done

(*------------------------------------------------------------------*
 |                fnfF_proc ---> syntactical equality               |
 *------------------------------------------------------------------*)

lemma fnfF_syntactical_equality_only_if_lm:
   "P1 : fnfF_proc ==> 
    ALL P2. (P2 : fnfF_proc & P1 =F[M1,M2] P2) --> P1 = P2"
apply (rule fnfF_proc.induct[of P1])
apply (simp)

apply (intro allI impI)
apply (elim conjE)
apply (rotate_tac -2)
apply (erule fnfF_proc.cases)
apply (simp)

apply (subgoal_tac "Q = Qa")
apply (subgoal_tac "A = Aa")
apply (subgoal_tac "Ys = Ysa")
apply (subgoal_tac "Pf = Pfa")
apply (simp)

(* Pf *)
apply (simp add: fun_eq_iff)
apply (rule allI)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in spec)
apply (case_tac "x:Aa")
 apply (simp)
 apply (elim bexE conjE)
 apply (drule_tac x="Pfa x" in spec)
 apply (drule mp)
  apply (rule conjI)
   apply (simp)
   apply (simp only: fnfF_syntactical_equality_Pf)
 apply (simp)
 apply (simp)

apply (simp add: fnfF_syntactical_equality_Yf)
apply (rule fnfF_syntactical_equality_Union)
apply (simp_all)
apply (rule fnfF_syntactical_equality_Q)
apply (simp_all)
done

lemma fnfF_syntactical_equality_only_if:
   "[| P1 : fnfF_proc ; 
       P2 : fnfF_proc ; 
        P1 =F[M1,M2] P2 |]
    ==> P1 = P2"
apply (simp add: fnfF_syntactical_equality_only_if_lm)
done

(*--------------------------*
 |         theorem          |
 *--------------------------*)

theorem fnfF_syntactical_equality:
   "[| P1 : fnfF_proc ; P2 : fnfF_proc |] ==>
    (P1 =F P2) = (P1 = P2)"
apply (rule iffI)
apply (simp only: fnfF_syntactical_equality_only_if)
apply (simp)
done

(*===========================================================*
 |                        XfnfF_proc                         |
 *===========================================================*)

theorem XfnfF_syntactical_equality:
   "[| P1 : XfnfF_proc ; P2 : XfnfF_proc |] ==>
    (P1 =F P2) = (P1 = P2)"
apply (rule iffI)
apply (simp add: XfnfF_proc_def)
apply (elim conjE exE)
apply (simp)
apply (subgoal_tac "Pf = Pfa")
apply (simp)
apply (simp add: fun_eq_iff)
apply (rule allI)
apply (drule_tac x="x" in spec)+
apply (subgoal_tac "Pf x =F Pfa x")
apply (simp add: fnfF_syntactical_equality)

apply (rule cspF_rw_left)
apply (simp)
apply (rule cspF_rw_right)
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (simp)
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
