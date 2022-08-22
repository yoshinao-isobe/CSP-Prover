           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  April 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory FNF_F_nf
imports FNF_F_nf_int FNF_F_sf
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*  The following simplification rules are deleted in this theory file *)
(*       P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))        *)
(* Isabelle 2017: split_if --> if_split *)

declare if_split  [split del]

(*****************************************************************

         1. full normalizing
         2. 
         3. 

 *****************************************************************)

(*==================================================================*
 |                          fsfF --> fnfF                           |
 *==================================================================*)

inductive_set
  fnfF_fsfF_rel :: "(nat * ('p,'a) proc * ('p,'a) proc) set"

where
fnfF_fsfF_rel_zero:
  "(0, P, NDIV) : fnfF_fsfF_rel"
|
fnfF_fsfF_rel_etc:
  "P ~: fsfF_proc
   ==> (Suc n, P, P |. Suc n) : fnfF_fsfF_rel"
|
fnfF_fsfF_rel_int:
  "[| ALL c. if (c: sumset C)
             then (Suc n, SPf c, NPf c) : fnfF_fsfF_rel
             else NPf c = DIV ;
      sumset C ~= {} ; ALL c: sumset C. SPf c : fsfF_proc |]
   ==>
   (Suc n, (!! :C .. SPf), !! c:C ..[Suc n] NPf c)
   : fnfF_fsfF_rel"
|
fnfF_fsfF_rel_step:
  "[| ALL a. if a:A
             then (n, SPf a, NPf a) : fnfF_fsfF_rel
             else NPf a = DIV ;
      ALL a:A. SPf a : fsfF_proc ;
      Q = SKIP | Q = DIV | Q = STOP |]
   ==> 
   (Suc n, (? :A -> SPf) [+] Q,
      ((? :A -> NPf) [+] (if (Q = SKIP) then SKIP else DIV))
      |~| (!set Y:(if Q = STOP then {A} else {}) .. (? a:Y -> DIV)))
    : fnfF_fsfF_rel"

(*** function ***)

definition
  fnfF_fsfF     :: "nat => ('p,'a) proc => ('p,'a) proc"
  where
  fnfF_fsfF_def:
    "fnfF_fsfF n SP == THE NP. (n, SP, NP) : fnfF_fsfF_rel"
  
definition
  fnfF          :: "nat => ('p,'a) proc => ('p,'a) proc"
  where
  fnfF_def :
    "fnfF == (%n P. fnfF_fsfF n (fsfF P))"
  
definition
  XfnfF         :: "('p,'a) proc => ('p,'a) proc"
  where
  XfnfF_def :
    "XfnfF == (%P. !nat n .. (fnfF n P))"

(****************************************************************
 |                      uniquness                               |
 ****************************************************************)

lemma fnfF_fsfF_rel_unique_in_lm:
   "(n, SP, NP1) : fnfF_fsfF_rel
    ==> (ALL NP2. ((n, SP, NP2) : fnfF_fsfF_rel
                   --> NP1 = NP2))"
apply (rule fnfF_fsfF_rel.induct[of n SP NP1])
apply (simp)

(* zero *)
apply (intro allI impI)
apply (rotate_tac -1)
apply (erule fnfF_fsfF_rel.cases)
apply (simp_all)

(* etc *)
apply (intro allI impI)
apply (rotate_tac -1)
apply (erule fnfF_fsfF_rel.cases)
apply (simp_all)
apply (simp add: fsfF_proc_int)
apply (simp add: fsfF_proc_ext)

(* int *)
apply (intro allI impI)
apply (rotate_tac -1)
apply (erule fnfF_fsfF_rel.cases, simp_all)

 apply (rotate_tac -3)
 apply (drule sym)
 apply (simp add: fsfF_proc_int)

 apply (subgoal_tac "NPf = NPfa", simp)
 apply (simp add: fun_eq_iff)
 apply (intro allI)
 apply (drule_tac x="x" in spec)+
 apply (case_tac "x : sumset Ca")
 apply (simp)
 apply (simp)

(* step *)
apply (intro allI impI)
apply (rotate_tac -1)
apply (erule fnfF_fsfF_rel.cases, simp_all)

 apply (rotate_tac -3)
 apply (drule sym)
 apply (simp add: fsfF_proc_ext)

 apply (rule conjI)
 apply (subgoal_tac "NPf = NPfa", simp)
 apply (simp add: fun_eq_iff)
 apply (intro allI)
 apply (drule_tac x="x" in spec)+
 apply (case_tac "x : Aa")
 apply (simp)
 apply (simp)

 apply (simp split: if_split)
done

(*-----------------------*
 |        unique         |
 *-----------------------*)

lemma fnfF_fsfF_rel_unique:
   "[| (n, SP, NP1) : fnfF_fsfF_rel;
       (n, SP, NP2) : fnfF_fsfF_rel |]
    ==> NP1 = NP2"
by (simp add: fnfF_fsfF_rel_unique_in_lm)

lemma fnfF_fsfF_rel_EX1:
   "(EX NP. (n, SP, NP) : fnfF_fsfF_rel)
 = (EX! NP. (n, SP, NP) : fnfF_fsfF_rel)"
apply (rule iffI)

 apply (erule exE)
 apply (rule_tac a="NP" in ex1I)
 apply (simp)
 apply (simp add: fnfF_fsfF_rel_unique)

 apply (elim ex1_implies_exE)
 apply (simp)
done

(*------------------------------------------------------------*
 |                      fnfF_fsfF_rel (iff)                   |
 *------------------------------------------------------------*)

(* zero *)

lemma fnfF_fsfF_rel_zero_iff:
  "(0, SP, NP) : fnfF_fsfF_rel = (NP = NDIV)"
apply (rule)
apply (erule fnfF_fsfF_rel.cases, simp_all)
apply (simp add: fnfF_fsfF_rel_zero)
done

(* etc *)

lemma fnfF_fsfF_rel_etc_iff:
  "P ~: fsfF_proc
   ==> (Suc n, P, NP) : fnfF_fsfF_rel
       = (NP = P |. Suc n)"
apply (rule)
apply (erule fnfF_fsfF_rel.cases, simp_all)
 apply (simp add: fsfF_proc_int)
 apply (simp add: fsfF_proc_ext)
apply (simp add: fnfF_fsfF_rel_etc)
done

(* int *)

lemma fnfF_fsfF_rel_int_iff:
  "[| ALL c. if (c: sumset C)
             then (Suc n, SPf c, NPf c) : fnfF_fsfF_rel
             else NPf c = DIV ;
      sumset C ~= {} ; ALL c: sumset C. SPf c : fsfF_proc |]
   ==>
   (Suc n, (!! :C .. SPf), NP) : fnfF_fsfF_rel
   = (NP = !! c:C ..[Suc n] NPf c)"
apply (rule)
apply (erule fnfF_fsfF_rel.cases, simp_all)

 apply (rotate_tac -3)
 apply (drule sym)
 apply (simp add: fsfF_proc_int)

 apply (subgoal_tac "NPfa = NPf", simp)
 apply (simp add: fun_eq_iff)
 apply (rule allI)
 apply (drule_tac x="x" in spec)+
 apply (case_tac "x : sumset Ca")
 apply (simp add: fnfF_fsfF_rel_unique)

 apply (simp)
apply (simp add: fnfF_fsfF_rel_int)
done

(* step *)

lemma fnfF_fsfF_rel_step_iff:
  "[| ALL a. if a:A
             then (n, SPf a, NPf a) : fnfF_fsfF_rel
             else NPf a = DIV ;
      ALL a:A. SPf a : fsfF_proc ;
      Q = SKIP | Q = DIV | Q = STOP |]
   ==> 
   (Suc n, (? :A -> SPf) [+] Q, NP) : fnfF_fsfF_rel
   = (NP = ((? :A -> NPf) [+] (if (Q = SKIP) then SKIP else DIV))
      |~| (!set Y:(if Q = STOP then {A} else {}) .. (? a:Y -> DIV)))"
apply (rule)
apply (erule fnfF_fsfF_rel.cases, simp_all)

 apply (rotate_tac -3)
 apply (drule sym)
 apply (simp add: fsfF_proc_ext)

 apply (rule conjI)
 apply (subgoal_tac "NPfa = NPf", simp)
 apply (simp add: fun_eq_iff)
 apply (intro allI conjI)

 apply (drule_tac x="x" in spec)+
 apply (case_tac "x : Aa")
 apply (simp add: fnfF_fsfF_rel_unique)
 apply (simp)
 apply (simp split: if_split)

apply (simp add: fnfF_fsfF_rel_step)
done

(****************************************************************
 |                      existency                               |
 ****************************************************************)

(*** exists ***)

lemma fnfF_fsfF_rel_exists_zero:
   "(EX NP. (0, SP, NP) : fnfF_fsfF_rel)"
apply (rule_tac x="NDIV" in exI)
apply (simp add: fnfF_fsfF_rel.intros)
done

lemma fnfF_fsfF_rel_exists_notin:
   "P ~: fsfF_proc
    ==> (EX NP. (n, P, NP) : fnfF_fsfF_rel)"
apply (insert nat_zero_or_Suc)
apply (drule_tac x="n" in spec)
apply (elim disjE exE)
apply (simp add: fnfF_fsfF_rel_exists_zero)
apply (rule_tac x="P |. n" in exI)
apply (simp add: fnfF_fsfF_rel.intros)
done

(*** in fsfF_proc ***)

lemma fnfF_fsfF_rel_exists_in:
   "SP : fsfF_proc
    ==> ALL n. (EX NP. (n, SP, NP) :  fnfF_fsfF_rel)"
apply (rule fsfF_proc.induct[of SP])
apply (simp)

(* int *)
apply (rule allI)
apply (insert nat_zero_or_Suc)
apply (drule_tac x="n" in spec)
apply (elim disjE exE)
apply (simp add: fnfF_fsfF_rel_exists_zero)

apply (erule dist_BALL_conjE)
apply (simp add: exchange_ALL_BALL)
apply (simp add: choice_BALL_EX)
apply (drule_tac x="n" in spec)
apply (elim exE)
apply (rule_tac x="!! c:C ..[Suc m] (if (c : sumset C) then f c else DIV)" in exI)
apply (rule fnfF_fsfF_rel.intros)
apply (simp split: if_split)
apply (simp_all)

(* ext *)
apply (rule allI)
apply (drule_tac x="n" in spec)
apply (rotate_tac -1)
apply (erule disjE)
apply (simp add: fnfF_fsfF_rel_exists_zero)

apply (elim exE)
apply (erule dist_BALL_conjE)

apply (simp add: exchange_ALL_BALL)
apply (simp add: choice_BALL_EX)
apply (drule_tac x="m" in spec)
apply (elim exE)
apply (rule_tac x=
"((? a:A -> (if (a : A) then f a else DIV)) [+] (if (Q = SKIP) then SKIP else DIV))
      |~| (!set Y:(if Q = STOP then {A} else {}) .. (? a:Y -> DIV))" in exI)
apply (rule fnfF_fsfF_rel.intros)
apply (simp split: if_split)
apply (simp_all)
done

(*-----------------------*
 |        exists         |
 *-----------------------*)

lemma fnfF_fsfF_rel_exists:
   "EX NP. (n, SP, NP) :  fnfF_fsfF_rel"
apply (case_tac "SP ~: fsfF_proc")
apply (simp add: fnfF_fsfF_rel_exists_notin)
apply (simp add: fnfF_fsfF_rel_exists_in)
done

(*-----------------------*
 |    uniquely exists    |
 *-----------------------*)

lemma fnfF_fsfF_rel_unique_exists:
   "EX! NP. (n, SP, NP) :  fnfF_fsfF_rel"
apply (simp add: fnfF_fsfF_rel_EX1[THEN sym])
apply (simp add: fnfF_fsfF_rel_exists)
done

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fnfF_fsfF_rel_zero_in:
  "(0, SP, NP) : fnfF_fsfF_rel ==> NP : fnfF_proc"
apply (simp add: fnfF_fsfF_rel_zero_iff)
done

lemma fnfF_fsfF_rel_in_lm:
  "SP : fsfF_proc ==> 
   ALL n NP. (n, SP, NP) : fnfF_fsfF_rel --> NP : fnfF_proc"
apply (rule fsfF_proc.induct[of SP])
apply (simp)

(* int *)
apply (intro allI)
apply (insert nat_zero_or_Suc)
apply (drule_tac x="n" in spec)
apply (elim disjE exE)
apply (simp add: fnfF_fsfF_rel_zero_in)

apply (intro impI)
apply (simp)
apply (rotate_tac -1)
apply (erule fnfF_fsfF_rel.cases, simp_all)

 apply (rotate_tac -3)
 apply (drule sym)
 apply (simp add: fsfF_proc.intros)

apply (rule fnfF_Rep_int_choice_in)
apply (rule ballI)
apply (drule_tac x="c" in spec, simp)

(* ext *)
apply (intro allI)
apply (drule_tac x="n" in spec)
apply (rotate_tac -1)
apply (erule disjE)
apply (simp add: fnfF_fsfF_rel_zero_in)

apply (intro impI)
apply (erule fnfF_fsfF_rel.cases, simp_all)

 apply (rotate_tac -3)
 apply (drule sym)
 apply (simp add: fsfF_proc.intros)

apply (rule fnfF_proc.intros)

 apply (simp split: if_split)
 apply (intro allI impI)
 apply (drule_tac x="a" in spec, simp)

 apply (simp add: fnfF_set_condition_def)
 apply (intro allI impI)
 apply (simp split: if_split)
 apply (elim conjE bexE) 
 apply (case_tac "Q = STOP")
 apply (simp)
 apply (simp)

 apply (force)
 apply (force)
done

(*------------------------------------*
 |                 in                 |
 *------------------------------------*)

lemma fnfF_fsfF_rel_in:
  "[| SP : fsfF_proc ; (n, SP, NP) : fnfF_fsfF_rel |]
   ==> NP : fnfF_proc"
apply (insert fnfF_fsfF_rel_in_lm[of SP])
apply (blast)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

(*** relation ***)

lemma cspF_fnfF_fsfF_rel_eqF_zero:
   "(0, P, NP) : fnfF_fsfF_rel
     ==> P |. 0 =F NP"
apply (simp add: fnfF_fsfF_rel_zero_iff)
apply (rule cspF_rw_left)
apply (rule cspF_Depth_rest_Zero)
apply (rule cspF_NDIV_eqF)
done

lemma cspF_fnfF_fsfF_rel_eqF_notin:
   "[| P ~: fsfF_proc ; (n, P, NP) : fnfF_fsfF_rel |]
    ==> P |. n =F NP"
apply (insert nat_zero_or_Suc)
apply (drule_tac x="n" in spec)
apply (elim disjE exE)
apply (simp add: cspF_fnfF_fsfF_rel_eqF_zero)
apply (simp add: fnfF_fsfF_rel_etc_iff)
done

lemma cspF_fnfF_fsfF_rel_eqF_in:
    "SP : fsfF_proc ==>
     ALL n NP. (n, SP, NP) : fnfF_fsfF_rel
                --> SP |. n =F NP"
apply (rule fsfF_proc.induct[of SP])
apply (simp)

(* int *)
apply (intro allI)
apply (insert nat_zero_or_Suc)
apply (drule_tac x="n" in spec)
apply (elim disjE exE)
apply (simp add: cspF_fnfF_fsfF_rel_eqF_zero)

apply (intro impI)
apply (simp)
apply (rotate_tac -1)
apply (erule fnfF_fsfF_rel.cases, simp_all)

apply (rule cspF_rw_right)
apply (rule cspF_fnfF_Rep_int_choice_eqF[THEN cspF_sym])

apply (rule cspF_rw_left)
apply (rule cspF_Dist)
apply (rule cspF_rw_right)
apply (rule cspF_Dist)
apply (rule cspF_decompo)
apply (simp)
apply (drule_tac x="c" in bspec, simp)
apply (drule_tac x="c" in spec)
apply (simp)
apply (drule_tac x="Suc na" in spec)
apply (drule_tac x="NPf c" in spec)
apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_Depth_rest_n[THEN cspF_sym])
apply (rule cspF_decompo)
apply (simp)
apply (simp)

(* ext *)
apply (intro allI)
apply (drule_tac x="n" in spec)
apply (rotate_tac -1)
apply (erule disjE)
apply (simp add: cspF_fnfF_fsfF_rel_eqF_zero)

apply (intro impI)
apply (erule fnfF_fsfF_rel.cases, simp_all)

apply (rule cspF_rw_left)
apply (rule cspF_Ext_dist)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_step)
apply (subgoal_tac "Q |. Suc na =F Q")
 apply (simp)
 apply (case_tac "Q = STOP")
 apply (simp add: cspF_STOP_Depth_rest)
 apply (simp add: cspF_SKIP_or_DIV_Depth_rest)

 apply (case_tac "Q = STOP")
 apply (simp)

 (* STOP *)
 apply (rule cspF_rw_left)
 apply (rule cspF_unit)
 apply (rule cspF_rw_left)
 apply (rule cspF_input_DIV)
 apply (rule cspF_decompo)
 apply (rule cspF_decompo)
 apply (rule cspF_decompo)
 apply (simp)
 apply (drule_tac x="a" in bspec, simp)
 apply (drule_tac x="na" in spec)
 apply (drule_tac x="NPf a" in spec)
 apply (simp)
 apply (simp)
 apply (rule cspF_rw_right)
 apply (rule cspF_Rep_int_choice_singleton)
 apply (rule cspF_reflex)

 (* SKIP | DIV *)
 apply (simp)
 apply (rule cspF_rw_right)
 apply (rule cspF_decompo)
 apply (rule cspF_reflex)
 apply (rule cspF_Rep_int_choice_DIV)
 apply (rule cspF_rw_right)
 apply (rule cspF_unit)
 apply (rule cspF_decompo)
 apply (rule cspF_decompo)
 apply (simp)
 apply (drule_tac x="a" in bspec, simp)
 apply (drule_tac x="na" in spec)
 apply (drule_tac x="NPf a" in spec)
 apply (simp)
 apply (force)
done

(*------------------------------------*
 |                 eqF                |
 *------------------------------------*)

lemma cspF_fnfF_fsfF_rel_eqF:
   "(n, SP, NP) : fnfF_fsfF_rel ==> SP |. n =F NP"
apply (case_tac "SP ~: fsfF_proc")
apply (simp add: cspF_fnfF_fsfF_rel_eqF_notin)
apply (simp add: cspF_fnfF_fsfF_rel_eqF_in)
done

(*************************************************************
                  relation --> function
 *************************************************************)

lemma fnfF_fsfF_in_rel:
    "(n, SP, fnfF_fsfF n SP) : fnfF_fsfF_rel"
apply (simp add: fnfF_fsfF_def)
apply (rule theI'
  [of "(%NP. (n, SP, NP) : fnfF_fsfF_rel)"])
apply (simp add: fnfF_fsfF_rel_unique_exists)
done

lemma fnfF_fsfF_from_rel:
    "((n, SP, NP) : fnfF_fsfF_rel)
   = (fnfF_fsfF n SP = NP)"
apply (rule iffI)
apply (simp add: fnfF_fsfF_def)
apply (simp add: fnfF_fsfF_rel_unique_exists the1_equality)

apply (drule sym)
apply (simp add: fnfF_fsfF_in_rel)
done

lemma fnfF_fsfF_to_rel:
    "(fnfF_fsfF n SP = NP)
   = ((n, SP, NP) : fnfF_fsfF_rel)"
by (simp add: fnfF_fsfF_from_rel)

(*************************************************************
                          function
 *************************************************************)

lemma fnfF_fsfF_zero:
  "fnfF_fsfF 0 SP = NDIV"
apply (simp add: fnfF_fsfF_to_rel)
apply (simp add: fnfF_fsfF_rel_zero_iff)
done

lemma fnfF_fsfF_etc:
  "P ~: fsfF_proc
   ==> fnfF_fsfF (Suc n) P = P |. (Suc n)"
apply (simp add: fnfF_fsfF_to_rel)
apply (simp add: fnfF_fsfF_rel_etc_iff)
done

lemma fnfF_fsfF_int:
  "[| sumset C ~= {} ; ALL c: sumset C. SPf c : fsfF_proc |]
   ==>
   fnfF_fsfF (Suc n) (!! :C .. SPf) =
    !! c:C ..[Suc n] (if c: sumset C then (fnfF_fsfF (Suc n) (SPf c)) else DIV)"
apply (simp add: fnfF_fsfF_to_rel)
apply (rule fnfF_fsfF_rel_int)
apply (simp_all)
apply (simp split: if_split)
apply (simp add: fnfF_fsfF_in_rel)
done

lemma fnfF_fsfF_step:
  "[| ALL a:A. SPf a : fsfF_proc ; Q = SKIP | Q = DIV | Q = STOP |]
   ==>
   fnfF_fsfF (Suc n) ((? :A -> SPf) [+] Q) =
      ((? a:A -> (if a:A then (fnfF_fsfF n (SPf a)) else DIV))
        [+] (if (Q = SKIP) then SKIP else DIV))
      |~| (!set Y:(if Q = STOP then {A} else {}) .. (? a:Y -> DIV))"
apply (simp add: fnfF_fsfF_to_rel)
apply (rule fnfF_fsfF_rel_step)
apply (simp_all)
apply (simp split: if_split)
apply (simp add: fnfF_fsfF_in_rel)
done

lemmas fnfF_fsfF =
       fnfF_fsfF_etc
       fnfF_fsfF_int
       fnfF_fsfF_step

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fnfF_fsfF_in:
  "SP : fsfF_proc
   ==> fnfF_fsfF n SP : fnfF_proc"
apply (rule fnfF_fsfF_rel_in[of SP n])
apply (simp_all add: fnfF_fsfF_in_rel)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

lemma cspF_fnfF_fsfF_eqF:
   "SP |. n =F fnfF_fsfF n SP"
apply (rule cspF_fnfF_fsfF_rel_eqF)
apply (simp add: fnfF_fsfF_in_rel)
done

(*===============================================================*
   theorem --- fnfF P is a (restricted) full normal form ---
 *===============================================================*)

theorem fnfF_in: "fnfF n P : fnfF_proc"
apply (simp add: fnfF_def)
apply (simp add: fnfF_fsfF_in fsfF_in)
done

(*===============================================================*
        theorem --- fnfF P is equal to P based on F ---
 *===============================================================*)

theorem cspF_fnfF_eqF: 
  "FPmode = CPOmode | FPmode = MIXmode ==> P |. n =F fnfF n P"
apply (simp add: fnfF_def)
apply (rule cspF_rw_right)
apply (rule cspF_fnfF_fsfF_eqF[THEN cspF_sym])
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_fsfF_eqF)
apply (simp)
apply (rule cspF_reflex)
done

(*------------------------*
 |     auxiliary laws     |
 *------------------------*)

lemma cspF_fnfF_eqF_Depth_rest:
  "FPmode = CPOmode | FPmode = MIXmode
   ==> (fnfF n P) |. n =F fnfF n P"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_fnfF_eqF[THEN cspF_sym])
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_Depth_rest_min)
apply (simp)
apply (rule cspF_fnfF_eqF)
apply (simp)
done

(*===============================================================*
          theorem --- XfnfF P is a full normal form ---
 *===============================================================*)

theorem XfnfF_in: 
  "FPmode = CPOmode | FPmode = MIXmode ==> XfnfF P : XfnfF_proc"
apply (simp add: XfnfF_def)
apply (simp add: XfnfF_proc_def)
apply (rule_tac x="(%n. fnfF n P)" in exI)
apply (simp)
apply (simp add: fnfF_in)
apply (rule allI)
apply (rule cspF_rw_right)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_fnfF_eqF[THEN cspF_sym])
apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_fnfF_eqF[THEN cspF_sym])
apply (simp)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_nat_Depth_rest)
done

(*===============================================================*
          theorem --- XfnfF P is equal to P based on F ---
 *===============================================================*)

theorem cspF_XfnfF_eqF:
   "FPmode = CPOmode | FPmode = MIXmode ==> P =F XfnfF P"
apply (simp add: XfnfF_def)
apply (rule cspF_rw_right)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_fnfF_eqF[THEN cspF_sym])
apply (simp)
apply (rule cspF_nat_Depth_rest)
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
