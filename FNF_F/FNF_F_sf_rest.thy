           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |              Februaru 2006                |
            |                 March 2007  (modified)    |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory FNF_F_sf_rest
imports FNF_F_sf_def
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

         1. full sequentialization for Depth-restriction (P |. n)
         2.
         3.

 *****************************************************************)

(*============================================================*
 |                                                            |
 |                       Depth_rest                           |
 |                                                            |
 *============================================================*)

(*============================================================*
 |                         Pfun P1 P2                         |
 *============================================================*)

(*** relation ***)

inductive_set
  fsfF_Depth_rest_rel ::
  "(('p,'a) proc * nat * ('p,'a) proc) set"

where
fsfF_Depth_rest_rel_zero:
  "(P1, 0, SDIV) : fsfF_Depth_rest_rel"
|
fsfF_Depth_rest_rel_etc:
  "P1 ~: fsfF_proc
   ==> (P1, Suc n, P1 |. (Suc n)) : fsfF_Depth_rest_rel"
|
fsfF_Depth_rest_rel_int:
  "[| ALL c. if (c: sumset C1)
             then (Rf1 c, Suc m, SRf c) : fsfF_Depth_rest_rel
             else SRf c = DIV ;
      sumset C1 ~= {} ; ALL c: sumset C1. Rf1 c : fsfF_proc |]
   ==>
   ((!! :C1 .. Rf1), Suc m, !! c:C1 .. SRf c)
   : fsfF_Depth_rest_rel"
|
fsfF_Depth_rest_rel_step:
  "[| ALL a. if a:A1
             then (Pf1 a, n, SPf a) : fsfF_Depth_rest_rel
             else SPf a = DIV ;
      ALL a:A1. Pf1 a : fsfF_proc ;
      Q1 = SKIP | Q1 = DIV | Q1 = STOP |]
   ==> 
   ((? :A1 -> Pf1) [+] Q1, Suc n, (? :A1 -> SPf) [+] Q1) : fsfF_Depth_rest_rel"

(*** function ***)

definition
  fsfF_Depth_rest ::
  "('p,'a) proc => nat => ('p,'a) proc"   ("(1_ /|.seq _)" [84,900] 84)
  where
  fsfF_Depth_rest_def:
    "P1 |.seq n == THE SP. (P1, n, SP) : fsfF_Depth_rest_rel"

(****************************************************************
 |                      uniquness                               |
 ****************************************************************)

lemma fsfF_Depth_rest_rel_unique_in_lm:
   "(P1, n, SP1) : fsfF_Depth_rest_rel
    ==> (ALL SP2. ((P1, n, SP2) : fsfF_Depth_rest_rel
                   --> SP1 = SP2))"
apply (rule fsfF_Depth_rest_rel.induct[of P1 n SP1])
apply (simp)

(* zero *)
apply (intro allI impI)
apply (rotate_tac -1)
apply (erule fsfF_Depth_rest_rel.cases)
apply (simp_all)

(* etc *)
apply (intro allI impI)
apply (rotate_tac -1)
apply (erule fsfF_Depth_rest_rel.cases)
apply (simp_all)
apply (simp add: fsfF_proc_int)
apply (simp add: fsfF_proc_ext)

(* step_int *)
apply (intro allI impI)
apply (rotate_tac -1)
apply (erule fsfF_Depth_rest_rel.cases, simp_all)

 apply (rotate_tac -4)
 apply (drule sym)
 apply (simp add: fsfF_proc_int)

 apply (simp add: fun_eq_iff)
 apply (intro allI)
 apply (drule_tac x="x" in spec)+
 apply (case_tac "x : sumset C1a")
 apply (simp)
 apply (simp)

(* step *)
apply (intro allI impI)
apply (rotate_tac -1)
apply (erule fsfF_Depth_rest_rel.cases, simp_all)

 apply (rotate_tac -4)
 apply (drule sym)
 apply (simp add: fsfF_proc_ext)

  apply (simp add: fun_eq_iff)
  apply (rule allI)
  apply (drule_tac x="x" in spec)+
  apply (case_tac "x : A1a")
  apply (simp_all)
done

(*-----------------------*
 |        unique         |
 *-----------------------*)

lemma fsfF_Depth_rest_rel_unique:
   "[| (P1, n, SP1) : fsfF_Depth_rest_rel;
       (P1, n, SP2) : fsfF_Depth_rest_rel |]
    ==> SP1 = SP2"
by (simp add: fsfF_Depth_rest_rel_unique_in_lm)

lemma fsfF_Depth_rest_rel_EX1:
   "(EX SP. (P1, n, SP) : fsfF_Depth_rest_rel)
 = (EX! SP. (P1, n, SP) : fsfF_Depth_rest_rel)"
apply (rule iffI)

 apply (erule exE)
 apply (rule_tac a="SP" in ex1I)
 apply (simp)
 apply (simp add: fsfF_Depth_rest_rel_unique)

 apply (elim ex1_implies_exE)
 apply (simp)
done

(*------------------------------------------------------------*
 |                   fsfF_Depth_rest_rel (iff)                |
 *------------------------------------------------------------*)

(* zero *)

lemma fsfF_Depth_rest_rel_zero_iff:
  "(P1, 0, SP) : fsfF_Depth_rest_rel
   = (SP = SDIV)"
apply (rule)
apply (erule fsfF_Depth_rest_rel.cases, simp_all)
apply (simp add: fsfF_Depth_rest_rel_zero)
done

(* etc *)

lemma fsfF_Depth_rest_rel_etc_iff:
  "P1 ~: fsfF_proc
   ==> (P1, Suc n, SP) : fsfF_Depth_rest_rel
       = (SP = P1 |. Suc n)"
apply (rule)
apply (erule fsfF_Depth_rest_rel.cases, simp_all)
 apply (simp add: fsfF_proc_int)
 apply (simp add: fsfF_proc_ext)
apply (simp add: fsfF_Depth_rest_rel_etc)
done

(* int nat *)

lemma fsfF_Depth_rest_rel_int_iff:
  "[| ALL c. if (c: sumset C1)
             then (Rf1 c, Suc m, SRf c) : fsfF_Depth_rest_rel
             else SRf c = DIV ;
      sumset C1 ~= {} ; ALL c: sumset C1. Rf1 c : fsfF_proc |]
   ==>
   ((!! :C1 .. Rf1), Suc m, SP) : fsfF_Depth_rest_rel
   = (SP = !! :C1 .. SRf)"
apply (rule)
apply (erule fsfF_Depth_rest_rel.cases, simp_all)

 apply (rotate_tac -4)
 apply (drule sym)
 apply (simp add: fsfF_proc_int)

 apply (simp add: fun_eq_iff)
 apply (rule allI)
 apply (drule_tac x="x" in spec)+
 apply (case_tac "x : sumset C1a")
 apply (simp add: fsfF_Depth_rest_rel_unique)

 apply (simp)
apply (simp add: fsfF_Depth_rest_rel_int)
done

(* step *)

lemma fsfF_Depth_rest_rel_step_iff:
  "[| ALL a. if a:A1
             then (Pf1 a, n, SPf a) : fsfF_Depth_rest_rel
             else SPf a = DIV ;
      ALL a:A1. Pf1 a : fsfF_proc ;
      Q1 = SKIP | Q1 = DIV | Q1 = STOP |]
   ==> 
   ((? :A1 -> Pf1) [+] Q1, Suc n, SP) : fsfF_Depth_rest_rel
   = (SP = (? :A1 -> SPf) [+] Q1)"
apply (rule)
apply (erule fsfF_Depth_rest_rel.cases, simp_all)

 apply (rotate_tac -4)
 apply (drule sym)
 apply (simp add: fsfF_proc_ext)

 apply (simp add: fun_eq_iff)
 apply (intro allI conjI)
 apply (elim conjE)
 apply (drule_tac x="x" in spec)+
 apply (case_tac "x : A1a")
 apply (simp add: fsfF_Depth_rest_rel_unique)
 apply (simp)
apply (simp add: fsfF_Depth_rest_rel_step)
done

(****************************************************************
 |                      existency                               |
 ****************************************************************)

(*** exists ***)

lemma fsfF_Depth_rest_rel_exists_zero:
   "(EX SP. (P1, 0, SP) : fsfF_Depth_rest_rel)"
apply (rule_tac x="SDIV" in exI)
apply (simp add: fsfF_Depth_rest_rel.intros)
done

lemma fsfF_Depth_rest_rel_exists_notin:
   "P1 ~: fsfF_proc
    ==> (EX SP. (P1, n, SP) : fsfF_Depth_rest_rel)"
apply (insert nat_zero_or_Suc)
apply (drule_tac x="n" in spec)
apply (elim disjE exE)
apply (simp add: fsfF_Depth_rest_rel_exists_zero)
apply (rule_tac x="P1 |. n" in exI)
apply (simp add: fsfF_Depth_rest_rel.intros)
done

(*** in fsfF_proc ***)

(********* P1 and P2 *********)

lemma fsfF_Depth_rest_rel_exists_in:
   "P1 : fsfF_proc
    ==> ALL n. (EX SP. (P1, n, SP) :  fsfF_Depth_rest_rel)"
apply (rule fsfF_proc.induct[of P1])
apply (simp)

(* int nat *)
apply (rule allI)
apply (insert nat_zero_or_Suc)
apply (drule_tac x="n" in spec)
apply (elim disjE exE)
apply (simp add: fsfF_Depth_rest_rel_exists_zero)

apply (erule dist_BALL_conjE)
apply (simp add: exchange_ALL_BALL)
apply (simp add: choice_BALL_EX)
apply (drule_tac x="n" in spec)
apply (elim exE)
apply (rule_tac x="!! c:C .. (if (c : sumset C) then f c else DIV)" in exI)
apply (rule fsfF_Depth_rest_rel.intros)
apply (simp split: if_split)
apply (simp_all)

(* ext *)
apply (rule allI)
apply (drule_tac x="n" in spec)
apply (rotate_tac -1)
apply (erule disjE)
apply (simp add: fsfF_Depth_rest_rel_exists_zero)

apply (elim exE)
apply (erule dist_BALL_conjE)

apply (simp add: exchange_ALL_BALL)
apply (simp add: choice_BALL_EX)
apply (drule_tac x="m" in spec)
apply (elim exE)
apply (rule_tac x="? a:A -> (if (a : A) then (f a) else DIV) [+] Q" in exI)
apply (rule fsfF_Depth_rest_rel.intros)
apply (simp split: if_split)
apply (simp_all)
done

(*-----------------------*
 |        exists         |
 *-----------------------*)

lemma fsfF_Depth_rest_rel_exists:
   "EX SP. (P1, n, SP) :  fsfF_Depth_rest_rel"
apply (case_tac "P1 ~: fsfF_proc")
apply (simp add: fsfF_Depth_rest_rel_exists_notin)
apply (simp add: fsfF_Depth_rest_rel_exists_in)
done

(*-----------------------*
 |    uniquely exists    |
 *-----------------------*)

lemma fsfF_Depth_rest_rel_unique_exists:
   "EX! SP. (P1, n, SP) :  fsfF_Depth_rest_rel"
apply (simp add: fsfF_Depth_rest_rel_EX1[THEN sym])
apply (simp add: fsfF_Depth_rest_rel_exists)
done

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fsfF_Depth_rest_rel_zero_in:
  "(P1, 0, SP) : fsfF_Depth_rest_rel ==> SP : fsfF_proc"
apply (simp add: fsfF_Depth_rest_rel_zero_iff)
done

lemma fsfF_Depth_rest_rel_in_lm:
  "P1 : fsfF_proc ==> 
   ALL n SP. (P1, n, SP) : fsfF_Depth_rest_rel --> SP : fsfF_proc"
apply (rule fsfF_proc.induct[of P1])
apply (simp)

(* int nat *)
apply (intro allI)
apply (insert nat_zero_or_Suc)
apply (drule_tac x="n" in spec)
apply (elim disjE exE)
apply (simp add: fsfF_Depth_rest_rel_zero_in)

apply (intro impI)
apply (simp)
apply (rotate_tac -1)
apply (erule fsfF_Depth_rest_rel.cases, simp_all)

 apply (rotate_tac -4)
 apply (drule sym)
 apply (simp add: fsfF_proc.intros)

apply (rule fsfF_proc.intros)
apply (simp_all)
apply (rule ballI)
apply (drule_tac x="c" in spec)
apply (drule_tac x="c" in bspec, simp)
apply (force)

(* ext *)
apply (intro allI)
apply (drule_tac x="n" in spec)
apply (rotate_tac -1)
apply (erule disjE)
apply (simp add: fsfF_Depth_rest_rel_zero_in)

apply (intro impI)
apply (erule fsfF_Depth_rest_rel.cases, simp_all)

 apply (rotate_tac -4)
 apply (drule sym)
 apply (simp add: fsfF_proc.intros)

apply (rule fsfF_proc.intros)
apply (simp_all)
apply (rule ballI)
apply (drule_tac x="a" in spec)
apply (drule_tac x="a" in bspec, simp)
apply (force)
done

(*------------------------------------*
 |                 in                 |
 *------------------------------------*)

lemma fsfF_Depth_rest_rel_in:
  "[| P1 : fsfF_proc ; (P1, n, SP) : fsfF_Depth_rest_rel |]
   ==> SP : fsfF_proc"
apply (insert fsfF_Depth_rest_rel_in_lm[of P1])
apply (blast)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

(*** relation ***)

lemma cspF_fsfF_Depth_rest_rel_eqF_zero:
   "(P1, 0, SP) : fsfF_Depth_rest_rel
     ==> P1 |. 0 =F SP"
apply (simp add: fsfF_Depth_rest_rel_zero_iff)
apply (rule cspF_rw_left)
apply (rule cspF_Depth_rest_Zero)
apply (rule cspF_SDIV_eqF)
done

lemma cspF_fsfF_Depth_rest_rel_eqF_notin:
   "[| P1 ~: fsfF_proc ; (P1, n, SP) : fsfF_Depth_rest_rel |]
    ==> P1 |. n =F SP"
apply (insert nat_zero_or_Suc)
apply (drule_tac x="n" in spec)
apply (elim disjE exE)
apply (simp add: cspF_fsfF_Depth_rest_rel_eqF_zero)
apply (simp add: fsfF_Depth_rest_rel_etc_iff)
done

lemma cspF_fsfF_Depth_rest_rel_eqF_in:
    "P1 : fsfF_proc ==>
     ALL n SP. (P1, n, SP) : fsfF_Depth_rest_rel
                --> P1 |. n =F SP"
apply (rule fsfF_proc.induct[of P1])
apply (simp)

(* int *)
apply (intro allI)
apply (insert nat_zero_or_Suc)
apply (drule_tac x="n" in spec)
apply (elim disjE exE)
apply (simp add: cspF_fsfF_Depth_rest_rel_eqF_zero)

apply (intro impI)
apply (simp)
apply (rotate_tac -1)
apply (erule fsfF_Depth_rest_rel.cases, simp_all)
apply (elim conjE)

apply (rule cspF_rw_left)
apply (rule cspF_Dist)
apply (rule cspF_decompo)
apply (simp)
apply (drule_tac x="c" in bspec, simp)
apply (drule_tac x="c" in spec)
apply (simp)

(* ext *)
apply (intro allI)
apply (drule_tac x="n" in spec)
apply (rotate_tac -1)
apply (erule disjE)
apply (simp add: cspF_fsfF_Depth_rest_rel_eqF_zero)

apply (intro impI)
apply (erule fsfF_Depth_rest_rel.cases, simp_all)

apply (rule cspF_rw_left)
apply (rule cspF_Ext_dist)
apply (rule cspF_decompo)

 apply (rule cspF_rw_left)
 apply (rule cspF_step)
 apply (rule cspF_decompo)
 apply (simp)
 apply (simp)
 apply (case_tac "Q = STOP")
 apply (simp add: cspF_STOP_Depth_rest)
 apply (simp add: cspF_SKIP_or_DIV_Depth_rest)
done

(*------------------------------------*
 |                 eqF                |
 *------------------------------------*)

lemma cspF_fsfF_Depth_rest_rel_eqF:
   "(P1, n, SP) : fsfF_Depth_rest_rel ==> P1 |. n =F SP"
apply (case_tac "P1 ~: fsfF_proc")
apply (simp add: cspF_fsfF_Depth_rest_rel_eqF_notin)
apply (simp add: cspF_fsfF_Depth_rest_rel_eqF_in)
done

(*************************************************************
                  relation --> function
 *************************************************************)

lemma fsfF_Depth_rest_in_rel:
    "(P1, n, P1 |.seq n) : fsfF_Depth_rest_rel"
apply (simp add: fsfF_Depth_rest_def)
apply (rule theI'
  [of "(%R. (P1, n, R) : fsfF_Depth_rest_rel)"])
apply (simp add: fsfF_Depth_rest_rel_unique_exists)
done

lemma fsfF_Depth_rest_from_rel:
    "((P1, n, SP) : fsfF_Depth_rest_rel)
   = (P1 |.seq n = SP)"
apply (rule iffI)
apply (simp add: fsfF_Depth_rest_def)
apply (simp add: fsfF_Depth_rest_rel_unique_exists the1_equality)

apply (drule sym)
apply (simp add: fsfF_Depth_rest_in_rel)
done

lemma fsfF_Depth_rest_to_rel:
    "(P1 |.seq n = SP)
   = ((P1, n, SP) : fsfF_Depth_rest_rel)"
by (simp add: fsfF_Depth_rest_from_rel)

(*************************************************************
                          function
 *************************************************************)

lemma fsfF_Depth_rest_zero:
  "P1 |.seq 0 = SDIV"
apply (simp add: fsfF_Depth_rest_to_rel)
apply (simp add: fsfF_Depth_rest_rel_zero_iff)
done

lemma fsfF_Depth_rest_etc:
  "P1 ~: fsfF_proc
   ==> P1 |.seq (Suc n) = P1 |. (Suc n)"
apply (simp add: fsfF_Depth_rest_to_rel)
apply (simp add: fsfF_Depth_rest_rel_etc_iff)
done

lemma fsfF_Depth_rest_int:
  "[| sumset C1 ~= {} ; ALL c: sumset C1. Rf1 c : fsfF_proc |]
   ==>
   (!! :C1 .. Rf1) |.seq (Suc m) = 
    !! c:C1 .. (if c: sumset C1 then (Rf1 c |.seq (Suc m)) else DIV)"
apply (simp add: fsfF_Depth_rest_to_rel)
apply (rule fsfF_Depth_rest_rel_int)
apply (simp_all)
apply (simp split: if_split)
apply (simp add: fsfF_Depth_rest_in_rel)
done

lemma fsfF_Depth_rest_step:
  "[| ALL a:A1. Pf1 a : fsfF_proc ; Q1 = SKIP | Q1 = DIV | Q1 = STOP |]
   ==>
    ((? :A1 -> Pf1) [+] Q1) |.seq (Suc n) = 
    ((? a:A1 -> (if (a:A1) then (Pf1 a |.seq n) else DIV)) [+] Q1)"
apply (simp add: fsfF_Depth_rest_to_rel)
apply (rule fsfF_Depth_rest_rel_step)
apply (simp_all)
apply (simp split: if_split)
apply (simp add: fsfF_Depth_rest_in_rel)
done

lemmas fsfF_Depth_rest =
       fsfF_Depth_rest_etc
       fsfF_Depth_rest_int
       fsfF_Depth_rest_step

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fsfF_Depth_rest_in:
  "P1 : fsfF_proc
   ==> P1 |.seq n : fsfF_proc"
apply (rule fsfF_Depth_rest_rel_in[of P1 n])
apply (simp_all add: fsfF_Depth_rest_in_rel)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

lemma cspF_fsfF_Depth_rest_eqF:
   "P1 |. n =F P1 |.seq n"
apply (rule cspF_fsfF_Depth_rest_rel_eqF)
apply (simp add: fsfF_Depth_rest_in_rel)
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
