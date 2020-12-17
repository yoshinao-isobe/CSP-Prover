           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                January 2006               |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory FNF_F_sf_def
imports CSP_F_Main
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*  The following simplification rules are deleted in this theory file *)
(*       P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))        *)


(* Isabelle 2017 *)
declare if_split  [split del]

(*****************************************************************

         1. definition of full sequential-formed process
         2. 
         3. 

 *****************************************************************)

(*==========================================================*
 |                                                          |
 |                    Definition of fsfF                    |
 |                                                          |
 *==========================================================*)

(* 
Isabelle 2005

consts
  fsfF_proc :: "('p,'a) proc set"

inductive "fsfF_proc"

intros
fsfF_proc_int:
  "[| sumset C ~= {} ; ALL c: sumset C. Rf c : fsfF_proc |]
   ==> (!! :C .. Rf) : fsfF_proc"

fsfF_proc_ext:
  "[| ALL a:A. Pf a : fsfF_proc ;
      Q = SKIP | Q = DIV | Q = STOP |]
   ==> ((? :A -> Pf) [+] Q) : fsfF_proc"
*)

inductive_set
  fsfF_proc :: "('p,'a) proc set"
where
fsfF_proc_int:
  "[| sumset C ~= {} ; ALL c: sumset C. Rf c : fsfF_proc |]
   ==> (!! :C .. Rf) : fsfF_proc" |

fsfF_proc_ext:
  "[| ALL a:A. Pf a : fsfF_proc ;
      Q = SKIP | Q = DIV | Q = STOP |]
   ==> ((? :A -> Pf) [+] Q) : fsfF_proc"

(*-------------------------------------------*
 |   sequential-formed SSKIP, SDIV, SSTOP    |
 *-------------------------------------------*)

definition
  SSKIP     :: "('p,'a) proc"
  where
  SSKIP_def : "SSKIP == (? y:{} -> DIV) [+] SKIP"
    
definition
  SDIV      :: "('p,'a) proc"
  where
  SDIV_def  : "SDIV  == (? y:{} -> DIV) [+] DIV"
  
definition
  SSTOP     :: "('p,'a) proc"
  where
  SSTOP_def : "SSTOP == (? y:{} -> DIV) [+] STOP"

(*** small lemmas ***)

(* in *)

lemma fsfF_SSKIP_in[simp]: "SSKIP : fsfF_proc"
apply (simp add: SSKIP_def)
apply (simp add: fsfF_proc.intros)
done

lemma fsfF_SDIV_in[simp]: "SDIV : fsfF_proc"
apply (simp add: SDIV_def)
apply (simp add: fsfF_proc.intros)
done

lemma fsfF_SSTOP_in[simp]: "SSTOP : fsfF_proc"
apply (simp add: SSTOP_def)
apply (simp add: fsfF_proc.intros)
done

(* eqF *)

lemma cspF_SSKIP_eqF: "SKIP =F SSKIP"
apply (simp add: SSKIP_def)
apply (rule cspF_rw_right)
apply (rule cspF_Ext_choice_rule)
apply (simp)
done

lemma cspF_SDIV_eqF: "DIV =F SDIV"
apply (simp add: SDIV_def)
apply (rule cspF_rw_right)
apply (rule cspF_Ext_choice_rule)
apply (simp)
done

lemma cspF_SSTOP_eqF: "STOP =F SSTOP"
apply (simp add: SSTOP_def)
apply (rule cspF_rw_right)
apply (rule cspF_Ext_choice_rule)
apply (simp)
done

(*----------------------------------------------------------*
 |                          iff                             |
 *----------------------------------------------------------*)

(* proc *)

lemma fsfF_proc_iff:
  "(SP : fsfF_proc) = 
    ((EX C Rf.
  sumset C ~= {} & SP = !! :C .. Rf & (ALL c: sumset C. Rf c : fsfF_proc)) |
     (EX A Pf Q.
        SP = (? :A -> Pf) [+] Q & (ALL a:A. Pf a : fsfF_proc) &
        (Q = SKIP | Q = DIV | Q = STOP)))"

apply (rule iffI)

(* => *)
 apply (erule fsfF_proc.cases)
 apply (simp_all)

(* <= *)
 apply (elim conjE exE disjE)
 apply (simp_all add: fsfF_proc.intros)
done

lemma fsfF_procI:
   "((EX C Rf.
  sumset C ~= {} & SP = !! :C .. Rf & (ALL c: sumset C. Rf c : fsfF_proc)) |
     (EX A Pf Q.
        SP = (? :A -> Pf) [+] Q & (ALL a:A. Pf a : fsfF_proc) &
        (Q = SKIP | Q = DIV | Q = STOP)))
    ==> SP : fsfF_proc"
apply (simp add: fsfF_proc_iff[of SP])
done

lemma fsfF_procE:
  "[| SP : fsfF_proc ;
     ((EX C Rf.
  sumset C ~= {} & SP = !! :C .. Rf & (ALL c: sumset C. Rf c : fsfF_proc)) |
     (EX A Pf Q.
        SP = (? :A -> Pf) [+] Q & (ALL a:A. Pf a : fsfF_proc) &
        (Q = SKIP | Q = DIV | Q = STOP)))
      ==> S |]
    ==> S"
apply (simp add: fsfF_proc_iff[of SP])
done

(*----------------------------------------------------------*
 |                    subexpression                         |
 *----------------------------------------------------------*)

(* proc *)

lemma Rf_fsfF_proc:
  "[| !! :C .. Rf : fsfF_proc ; c: sumset C |]
   ==> Rf c : fsfF_proc"
apply (erule fsfF_procE)
apply (elim disjE conjE exE)
apply (simp_all)
done

lemma Pf_fsfF_proc:
  "[| (? :A -> Pf) [+] Q : fsfF_proc ; a:A |]
   ==> Pf a : fsfF_proc"
apply (erule fsfF_procE)
apply (simp)
done

lemma Qf_range:
  "(? :A -> Pf) [+] Q : fsfF_proc 
   ==> Q = SKIP | Q = DIV | Q = STOP"
apply (erule fsfF_procE)
apply (simp)
done

(*======================================================*
 |                                                      |
 |    function to decompose : fsfF_decompo_int, ext     |
 |                                                      |
 *======================================================*)

(*
isabelle 2011

consts
  fsfF_C ::
     "('p,'a) proc => 'a sets_nats"
  fsfF_Rf ::
     "('p,'a) proc => ('a aset_anat => ('p,'a) proc)"

  fsfF_A ::
     "('p,'a) proc => 'a set"
  fsfF_Pf ::
     "('p,'a) proc => ('a => ('p,'a) proc)"
  fsfF_Q ::
     "('p,'a) proc => ('p,'a) proc"

(* they are partial functions *)

recdef fsfF_C "{}"
  "fsfF_C (!! :C .. Rf) = C"
recdef fsfF_Rf "{}"
  "fsfF_Rf (!! :C .. Rf) = Rf"
recdef fsfF_A "{}"
  "fsfF_A ((? :A -> Pf) [+] Q) = A"
recdef fsfF_Pf "{}"
  "fsfF_Pf ((? :A -> Pf) [+] Q) = Pf"
recdef fsfF_Q "{}"
  "fsfF_Q ((? :A -> Pf) [+] Q) = Q"
*)

fun
  fsfF_C ::
     "('p,'a) proc => 'a sets_nats"
where
  "fsfF_C (!! :C .. Rf) = C"

fun
  fsfF_Rf ::
     "('p,'a) proc => ('a aset_anat => ('p,'a) proc)"
where
  "fsfF_Rf (!! :C .. Rf) = Rf"

fun
  fsfF_A ::
     "('p,'a) proc => 'a set"
where
  "fsfF_A ((? :A -> Pf) [+] Q) = A"

fun
  fsfF_Pf ::
     "('p,'a) proc => ('a => ('p,'a) proc)"
where
  "fsfF_Pf ((? :A -> Pf) [+] Q) = Pf"

fun
  fsfF_Q ::
     "('p,'a) proc => ('p,'a) proc"
where
  "fsfF_Q ((? :A -> Pf) [+] Q) = Q"

(* they are partial functions *)


(*------------------------*
 |     decomposition      |
 *------------------------*)

lemma cspF_fsfF_proc_decompo:
   "P : fsfF_proc ==>
     ((P = (!! : fsfF_C P .. fsfF_Rf P)) |
      (P = (? : fsfF_A P -> fsfF_Pf P [+] fsfF_Q P)))"
apply (erule fsfF_proc.cases)
apply (simp_all)
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
