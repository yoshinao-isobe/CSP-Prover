           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  April 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                  May 2016  (modified)     |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory FNF_F_nf_def
imports CSP_F_Main
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

         1. definition of full normalisation
         2. 
         3. 

 *****************************************************************)

(*----------------------------------------------------------------------*
 |                         full normal form                             |
 *----------------------------------------------------------------------*)

definition
  fnfF_set_condition  :: "'a set => 'a set set => bool"
  where
  fnfF_set_condition_def :
   "fnfF_set_condition A Ys == 
    (ALL Y. ((EX Y0:Ys. Y0 <= Y) & Y <= A Un Union Ys) --> Y:Ys)"
  
definition  
  fnfF_set_completion :: "'a set => 'a set set => 'a set set"
  where
  fnfF_set_completion_def :
   "fnfF_set_completion A Ys == {Y. (EX Y0:Ys. Y0 <= Y) & Y <= (A Un Union Ys)}"

   
(* Isabelle 2005
consts
  fnfF_proc      :: "('p,'a) proc set"

inductive "fnfF_proc"
intros
fnfF_proc_rule:
  "[| (ALL a. if a:A then Pf a : fnfF_proc else Pf a = DIV) ;
      fnfF_set_condition A Ys ; Union Ys <= A ;
      Q = SKIP | Q = DIV |]
   ==> ((? :A -> Pf) [+] Q) |~| (!set Y:Ys .. (? a:Y -> DIV))
        : fnfF_proc"
*)

inductive_set
  fnfF_proc      :: "('p,'a) proc set"
where
fnfF_proc_rule:
  "[| (ALL a. if a:A then Pf a : fnfF_proc else Pf a = DIV) ;
      fnfF_set_condition A Ys ; Union Ys <= A ;
      Q = SKIP | Q = DIV |]
   ==> ((? :A -> Pf) [+] Q) |~| (!set Y:Ys .. (? a:Y -> DIV))
        : fnfF_proc"

(* .elims ---> .cases *)


definition  
  XfnfF_proc           :: "('p,'a) proc set"
  where
  XfnfF_proc_def :
   "XfnfF_proc == {!nat n .. Pf n |Pf.
                  (ALL n. Pf n =F (!nat n .. Pf n) |. n) &
                  (ALL n. Pf n : fnfF_proc) }"

(*** convenient lemmas ***)

lemma fnfF_set_completion_sat_condition[simp]:
  "fnfF_set_condition A (fnfF_set_completion A Ys)"
apply (simp add: fnfF_set_condition_def)
apply (intro allI impI)
apply (elim conjE bexE)

apply (simp add: fnfF_set_completion_def)
apply (elim conjE bexE)
apply (rule conjI)
apply (rule_tac x="Y0a" in bexI)
apply (simp)
apply (simp)

apply (rule subsetI)
apply (erule subsetE)
apply (drule_tac x="x" in bspec, simp)
apply (simp)
apply (elim disjE conjE exE bexE)
apply (simp)

apply (rotate_tac 5)
apply (erule subsetE)
apply (simp)
done

lemma fnfF_set_completion_subset:
  "Ys <= fnfF_set_completion A Ys"
by (auto simp add: fnfF_set_completion_def)

lemma fnfF_set_completion_Union_subset:
  "Union Ys <= A ==>
   Union (fnfF_set_completion A Ys) <= A"
apply (auto simp add: fnfF_set_completion_def)
apply (subgoal_tac "x : A Un Union Ys")
apply (simp)
apply (erule disjE)
apply (auto)
done

(*----------------------------------------------------------*
 |                   intro, elim, simp                      |
 *----------------------------------------------------------*)

lemma fnfF_proc_iff:
  "(NP : fnfF_proc) = 
     (EX A Ys Pf Q.
      NP = ((? :A -> Pf) [+] Q) |~| (!set Y:Ys .. (? a:Y -> DIV)) &
      (ALL a. if a:A then Pf a : fnfF_proc else Pf a = DIV) &
       fnfF_set_condition A Ys & Union Ys <= A &
       (Q = SKIP | Q = DIV))"
apply (rule iffI)

(* => *)
(* apply (erule fnfF_proc.elims) *)
 apply (erule fnfF_proc.cases)
 apply (force)

(* <= *)
 apply (elim conjE exE)
 apply (simp add: fnfF_proc.intros)
done

lemma fnfF_proc_EX_I:
     "(EX A Ys Pf Q.
      NP = ((? :A -> Pf) [+] Q) |~| (!set Y:Ys .. (? a:Y -> DIV)) &
      (ALL a. if a:A then Pf a : fnfF_proc else Pf a = DIV) &
       fnfF_set_condition A Ys & Union Ys <= A &
       (Q = SKIP | Q = DIV))
    ==> NP : fnfF_proc"
apply (simp add: fnfF_proc_iff[of NP])
done

lemma fnfF_proc_EX_E:
  "[| NP : fnfF_proc ;
     (EX A Ys Pf Q.
      NP = ((? :A -> Pf) [+] Q) |~| (!set Y:Ys .. (? a:Y -> DIV)) &
      (ALL a. if a:A then Pf a : fnfF_proc else Pf a = DIV) &
       fnfF_set_condition A Ys & Union Ys <= A &
       (Q = SKIP | Q = DIV))
      ==> S |]
    ==> S"
apply (simp add: fnfF_proc_iff[of NP])
done

(*----------------------------------------------------------*
 |                 ALL fnfF_proc_iff                   |
 *----------------------------------------------------------*)

lemma ALL_fnfF_proc_only_if:
  "ALL x:X. NPf x : fnfF_proc
   ==>
     (EX Af Ysf Pff Qf.
      NPf = (%x. if x:X then (((? :(Af x) -> (Pff x)) [+] Qf x) |~| 
                             (!set Y:(Ysf x) .. (? a:Y -> DIV)))
                        else NPf x) &
      (ALL x:X. ALL a. if a:(Af x) then (Pff x a) : fnfF_proc 
                       else (Pff x a) = DIV) &
      (ALL x:X. fnfF_set_condition (Af x) (Ysf x)) &
      (ALL x:X. Union (Ysf x) <= Af x) &
      (ALL x:X. Qf x = SKIP | Qf x = DIV))"
apply (simp add: fnfF_proc_iff)
apply (simp add: choice_BALL_EX)
apply (elim exE)
apply (rule_tac x="f" in exI)
apply (rule_tac x="fa" in exI)
apply (rule_tac x="fb" in exI)
apply (rule_tac x="fc" in exI)

(* NPf *)
apply (rule conjI)
apply (simp add: fun_eq_iff)
apply (rule allI)
apply (case_tac "x:X")
apply (simp_all)

apply (intro allI ballI)
apply (drule_tac x="x" in bspec, simp)
apply (elim conjE)
apply (drule_tac x="a" in spec)
apply (simp)
done

lemma ALL_fnfF_proc_iff:
  "(ALL x:X. NPf x : fnfF_proc)
   =
     (EX Af Ysf Pff Qf.
      NPf = (%x. if x:X then (((? :(Af x) -> (Pff x)) [+] Qf x) |~| 
                             (!set Y:(Ysf x) .. (? a:Y -> DIV)))
                        else NPf x) &
      (ALL x:X. ALL a. if a:(Af x) then (Pff x a) : fnfF_proc 
                       else (Pff x a) = DIV) &
      (ALL x:X. fnfF_set_condition (Af x) (Ysf x)) &
      (ALL x:X. Union (Ysf x) <= Af x) &
      (ALL x:X. Qf x = SKIP | Qf x = DIV))"
apply (rule)
apply (simp add: ALL_fnfF_proc_only_if)

apply (elim conjE exE)
apply (intro ballI)
apply (simp add: fun_eq_iff)
apply (drule_tac x="x" in spec)
apply (drule_tac x="x" in bspec, simp)+
apply (simp)
apply (simp add: fnfF_proc.intros)
done

lemma ALL_fnfF_procI:
  "(EX Af Ysf Pff Qf.
      NPf = (%x. if x:X then (((? :(Af x) -> (Pff x)) [+] Qf x) |~| 
                             (!set Y:(Ysf x) .. (? a:Y -> DIV)))
                        else NPf x) &
      (ALL x:X. ALL a. if a:(Af x) then (Pff x a) : fnfF_proc 
                       else (Pff x a) = DIV) &
      (ALL x:X. fnfF_set_condition (Af x) (Ysf x)) &
      (ALL x:X. Union (Ysf x) <= Af x) &
      (ALL x:X. Qf x = SKIP | Qf x = DIV))
   ==> ALL x:X. NPf x : fnfF_proc"
apply (simp add: ALL_fnfF_proc_iff)
done

lemma ALL_fnfF_procE:
  "[| ALL x:X. NPf x : fnfF_proc ;
      (EX Af Ysf Pff Qf.
      NPf = (%x. if x:X then (((? :(Af x) -> (Pff x)) [+] Qf x) |~| 
                             (!set Y:(Ysf x) .. (? a:Y -> DIV)))
                        else NPf x) &
      (ALL x:X. ALL a. if a:(Af x) then (Pff x a) : fnfF_proc 
                       else (Pff x a) = DIV) &
      (ALL x:X. fnfF_set_condition (Af x) (Ysf x)) &
      (ALL x:X. Union (Ysf x) <= Af x) &
      (ALL x:X. Qf x = SKIP | Qf x = DIV))
   ==> S |] ==> S"
apply (simp add: ALL_fnfF_proc_iff)
done

(*======================================================*
 |         function to decompose : fnfF_decompo         |
 *======================================================*)
(* 
isabelle 2011

consts
  fnfF_A ::
     "('p,'a) proc => ('a set)"
  fnfF_Ys ::
     "('p,'a) proc => ('a set set)"
  fnfF_Pf ::
     "('p,'a) proc => ('a => ('p,'a) proc)"
  fnfF_Q ::
     "('p,'a) proc => ('p,'a) proc"

(* they are partial functions *)

recdef fnfF_A "{}"
  "fnfF_A (((? :A -> Pf) [+] Q) |~| R) = A"

recdef fnfF_Ys "{}"
  "fnfF_Ys (P |~| !! : type1 Ys .. Pf) = Ys"

recdef fnfF_Pf "{}"
  "fnfF_Pf (((? :A -> Pf) [+] Q) |~| R) = Pf"

recdef fnfF_Q "{}"
  "fnfF_Q (((? :A -> Pf) [+] Q) |~| R) = Q"
*)

(* they are partial functions *)

fun
  fnfF_A ::
     "('p,'a) proc => ('a set)"
where
  "fnfF_A (((? :A -> Pf) [+] Q) |~| R) = A"

fun
  fnfF_Ys ::
     "('p,'a) proc => ('a set set)"
where
  "fnfF_Ys (P |~| !! : type1 Ys .. Pf) = Ys"

fun
  fnfF_Pf ::
     "('p,'a) proc => ('a => ('p,'a) proc)"
where
  "fnfF_Pf (((? :A -> Pf) [+] Q) |~| R) = Pf"

fun
  fnfF_Q ::
     "('p,'a) proc => ('p,'a) proc"
where
  "fnfF_Q (((? :A -> Pf) [+] Q) |~| R) = Q"

lemma fnfF_Ys_get[simp]:
  "fnfF_Ys (P |~| !set :Ys .. Pf) = Ys"
by (simp add: Rep_int_choice_ss_def)

(*------------------------*
 |     decomposition      |
 *------------------------*)

lemma cspF_fnfF_nat_decompo:
   "P : fnfF_proc ==>
    P =F ((? : (fnfF_A P) -> (fnfF_Pf P)) [+] fnfF_Q P) 
         |~| (!set Y: fnfF_Ys P .. (? a:Y -> DIV))"
(* apply (erule fnfF_proc.elims) *)
apply (erule fnfF_proc.cases)
apply (simp)
done

(*--------------------------------------*
 |   properties of fnfF decomposition   |
 *--------------------------------------*)

lemma fnfF_Pf_A:
   "[| P : fnfF_proc ; a : (fnfF_A P) |]
    ==> (fnfF_Pf P) a : fnfF_proc"
apply (erule fnfF_proc.cases)
apply (simp)
done

lemma fnfF_Pf_DIV:
   "[| P : fnfF_proc ; a ~: (fnfF_A P) |]
    ==> (fnfF_Pf P) a = DIV"
apply (erule fnfF_proc.cases)
apply (simp)
done

lemma fnfF_Q_range:
   "P : fnfF_proc
    ==> (fnfF_Q P) = SKIP | (fnfF_Q P) = DIV"
apply (erule fnfF_proc.cases)
apply (simp)
done

lemma fnfF_condition_A_Ys:
   "P : fnfF_proc ==>
    fnfF_set_condition (fnfF_A P) (fnfF_Ys P)"
apply (erule fnfF_proc.cases)
apply (simp)
done

lemma fnfF_Union_Ys_A:
   "P : fnfF_proc ==>
    Union (fnfF_Ys P)  <= (fnfF_A P)"
apply (erule fnfF_proc.cases)
apply (simp)
done

(*-----------------------*
 |    DIV, SKIP, STOP    |
 *-----------------------*)

definition
  NSKIP     :: "('p,'a) proc"
  where
  NSKIP_def : "NSKIP == ((? a:{} -> DIV) [+] SKIP) |~| (!set Y:{} .. (? a:Y -> DIV))"
  
definition
  NDIV      :: "('p,'a) proc"
  where
  NDIV_def  : "NDIV  == ((? a:{} -> DIV) [+] DIV)  |~| (!set Y:{} .. (? a:Y -> DIV))"

definition  
  NSTOP     :: "('p,'a) proc"
  where
  NSTOP_def : "NSTOP == ((? a:{} -> DIV) [+] DIV)  |~| (!set Y:{{}} .. (? a:Y -> DIV))"

(*** in fnfF ***)

lemma fnfF_NSKIP[simp]: "NSKIP : fnfF_proc"
apply (simp add: NSKIP_def)
apply (rule fnfF_proc.intros)
apply (simp_all add: fnfF_set_condition_def)
done

lemma fnfF_NDIV[simp]: "NDIV : fnfF_proc"
apply (simp add: NDIV_def)
apply (rule fnfF_proc.intros)
apply (simp_all add: fnfF_set_condition_def)
done

lemma fnfF_NSTOP[simp]: "NSTOP : fnfF_proc"
apply (simp add: NSTOP_def)
apply (rule fnfF_proc.intros)
apply (simp_all add: fnfF_set_condition_def)
done

(*** eqF ***)

lemma cspF_NSKIP_eqF: "SKIP =F NSKIP"
apply (simp add: NSKIP_def)
apply (rule cspF_rw_right)
apply (rule cspF_decompo)
apply (rule cspF_choice_rule)
apply (rule cspF_Rep_int_choice_DIV)
apply (rule cspF_rw_right)
apply (rule cspF_unit)
apply (rule cspF_reflex)
done

lemma cspF_NDIV_eqF: "DIV =F NDIV"
apply (simp add: NDIV_def)
apply (rule cspF_rw_right)
apply (rule cspF_decompo)
apply (rule cspF_choice_rule)
apply (rule cspF_Rep_int_choice_DIV)
apply (rule cspF_rw_right)
apply (rule cspF_unit)
apply (rule cspF_reflex)
done

lemma cspF_NSTOP_eqF: "STOP =F NSTOP"
apply (simp add: NSTOP_def)
apply (rule cspF_rw_right)
apply (rule cspF_decompo)
apply (rule cspF_choice_rule)
apply (rule cspF_Rep_int_choice_singleton)
apply (rule cspF_rw_right)
apply (rule cspF_unit)
apply (rule cspF_step)
done

(*==============================================================*
 |               convenient rules for fnfF                      |
 *==============================================================*)

lemma cspF_fnfF_Depth_rest_dist:
  "Q = SKIP | Q = DIV ==>
   (? :A -> Pf [+] Q
   |~| !set Y:Ys .. ? a:Y -> DIV) |. Suc n
  =F 
   (? a:A -> (Pf a |. n) [+] Q
   |~| !set Y:Ys .. ? a:Y -> DIV)"
apply (rule cspF_rw_left)
apply (rule cspF_dist)
apply (rule cspF_decompo)
apply (rule cspF_rw_left)
apply (rule cspF_Ext_dist)
apply (rule cspF_decompo)
apply (rule cspF_rw_left)
apply (rule cspF_step)
apply (rule cspF_reflex)
apply (erule disjE)
apply (simp_all)

apply (rule cspF_rw_left)
apply (rule cspF_Dist)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_step)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_DIV_Depth_rest)
done

(* left DIV *)

lemma cspF_fsfF_left_DIV:
  "(? a:{} -> DIV [+] DIV) |~| P =F P"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_Ext_choice_rule)
apply (rule cspF_reflex)
apply (rule cspF_unit)
done

lemma cspF_fsfF_right_DIV:
  "P |~| (!set :{} .. Pf) =F P"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_reflex)
apply (rule cspF_Rep_int_choice_DIV)
apply (rule cspF_unit)
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
