           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Trace_seq
imports Prefix
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite (notick | t = <>)                  *)
(*                                                                     *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*****************************************************************

         1. 
         2. 
         3. 
         4. 

 *****************************************************************)

definition
  rmTick:: "'a trace => 'a trace"
  where
  rmTick_def : 
    "rmTick s == if noTick s then s else butlastt s"

(***********************************************************
                  nil and Tick
 ***********************************************************)

(*** noTick s --> rmTick s ***)

lemma rmTick_nochange[simp]: "noTick s ==> rmTick s = s"
by (simp add: rmTick_def)

(*** rmTick <> ***)

lemma rmTick_nil[simp]: "rmTick <> = <>"
by (simp add: rmTick_def)

(*** rmTick <Tick> ***)

lemma rmTick_Tick[simp]: "rmTick <Tick> = <>"
by (simp add: rmTick_def)

(*** noTick rmTick s ***)

lemma noTick_rmTick[simp]: "noTick (rmTick s)"
apply (case_tac "noTick s")
apply (simp_all add: rmTick_def)
apply (simp add: noTick_butlast)
done

lemma noTick_rmTickE: "[| t = rmTick s ; noTick t ==> R |] ==> R"
by (simp)

(***********************************************************
                           appt
 ***********************************************************)

(*-------------------------*
 |       rmTick last       |
 *-------------------------*)

lemma rmTick_last_Tick[simp]:
  "noTick s ==> rmTick (s ^^^ <Tick>) = s"
by (simp add: rmTick_def)

(*** noTick butlast ***)

lemma rmTick_butlastt: 
  "~ noTick s ==> rmTick s = butlastt s"
by (simp add: rmTick_def)

(*-------------------------*
 |   rmTick distribution   |
 *-------------------------*)

lemma rmTick_appt_dist[simp]:
  "noTick s ==> rmTick (s ^^^ t) = s ^^^ (rmTick t)"
apply (insert trace_last_nil_or_unnil)
apply (drule_tac x="t" in spec, simp)
apply (erule disjE, simp)

apply (elim conjE exE, simp)
apply (insert event_Tick_or_Ev)
apply (drule_tac x="a" in spec)

apply (erule disjE)   (* Tick *)
apply (simp add: appt_assoc_sym)

apply (erule exE)     (* Ev *)
apply (simp add: appt_assoc_sym)
done

(***********************************************************
                        prefix
 ***********************************************************)

(*** rmTick prefix ***)

(* only if *)

lemma rmTick_prefix_only_if:
  "prefix s (rmTick t) ==> (EX u. prefix u t & s = rmTick u)"
apply (insert trace_last_nil_or_unnil)
apply (drule_tac x="t" in spec, simp)
apply (erule disjE, simp)

apply (elim conjE exE, simp)
apply (insert event_Tick_or_Ev)
apply (drule_tac x="a" in spec)

 apply (erule disjE)    (* Tick *)
 apply (rule_tac x="s" in exI)
 apply (simp add: prefix_noTick)

 apply (erule exE)      (* Ev *)
 apply (simp)

  apply (erule disjE)    (* same length *)
  apply (rule_tac x="sa ^^^ <Ev aa>" in exI, simp)

  apply (rule_tac x="s" in exI)
  apply (simp add: prefix_noTick)
done

(* if *)

lemma rmTick_prefix_if:
  "(EX u. prefix u t & s = rmTick u) ==> prefix s (rmTick t)"
apply (elim conjE exE)
apply (simp)

apply (insert trace_last_nil_or_unnil)
apply (drule_tac x="t" in spec, simp)
apply (erule disjE, simp)
apply (elim conjE exE)
apply (simp)

 apply (erule disjE, simp)
 apply (case_tac "~ noTick u")
 apply (simp add: prefix_noTick)

 apply (insert event_Tick_or_Ev)
 apply (drule_tac x="a" in spec)

  apply (erule disjE)    (* Tick *)
  apply (simp)

  apply (elim exE)       (* Ev *)
  apply (simp)
done

(* iff *)

lemma rmTick_prefix:
  "prefix s (rmTick t) = (EX u. prefix u t & s = rmTick u)"
apply (rule iffI)
apply (simp add: rmTick_prefix_only_if)
apply (simp add: rmTick_prefix_if)
done

(*--------------*
 |   reverse    |
 *--------------*)

lemma rmTick_prefix_rev: "prefix s t ==> prefix (rmTick s) t"
apply (simp add: rmTick_def)
apply (intro impI)
apply (simp add: prefix_def)

apply (rule_tac x="<Tick>" in exI)
apply (simp add: noTick_butlast)
apply (simp add: Tick_decompo)
done

lemma rmTick_prefix_rev_simp[simp]: "prefix (rmTick s) s"
by (simp add: rmTick_prefix_rev)

(****************** to add it again ******************)

declare disj_not1 [simp] 

end
