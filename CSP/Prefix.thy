           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Prefix
imports Trace
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite (noTick | t = <>)                  *)
(*                                                                     *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*********************************************************)

definition
  prefix         :: "'a trace => 'a trace => bool"
  where
  prefix_def        : "prefix s t == (EX u. t = s ^^^ u & (noTick s | u = <>))"
  
definition
  prefix_closed  :: "('a trace set) => bool"
  where
  prefix_closed_def : 
    "prefix_closed T == ALL s t. ((t : T & prefix s t) --> s : T)"

(***********************************************************
                       lemmas (prefix)
 ***********************************************************)

lemma prefix_closed_iff:
  "[| t : T ; prefix s t ; prefix_closed T |] ==> s : T"
apply (unfold prefix_closed_def[of T])
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
by (simp)

(*** Prefix itself ***)

lemma prefix_itself[simp]: "prefix s s"
apply (simp add: prefix_def)
apply (rule_tac x="<>" in exI)
by (simp)

(*** Prefix appt ***)

lemma prefix_appt_simp[simp]: "(noTick s | t = <>) ==> prefix s (s ^^^ t)"
apply (simp add: prefix_def)
apply (rule_tac x="t" in exI)
by (simp)

lemma prefix_appt: 
  "[| (noTick t | u = <>) ; prefix s t |] ==> prefix s (t ^^^ u)"
apply (simp add: prefix_def)
apply (erule exE)
apply (simp)
apply (rule_tac x="ua ^^^ u" in exI)
apply (elim conjE disjE)
apply (simp_all)
by (simp add: appt_assoc)

(*** <> is a prefix of any trace ***)

lemma nil_is_prefix[simp]: "prefix <> s"
by (simp add: prefix_def)

(*** the prefix of <> is <> ***)

lemma prefix_of_nil[simp]: "prefix s <> = (s = <>)"
by (auto simp add: prefix_def)

(*** prefix of [a]t ***)

lemma prefix_of_one[simp]: "prefix s <a> = (s = <> | s = <a>)"
apply (simp add: prefix_def)
apply (auto)
apply (rule_tac x="<>" in exI)
by (simp)

(*** length of prefix ***)

lemma length_of_prefix:
  "prefix s t ==> lengtht s <= lengtht t"
apply (simp add: prefix_def)
apply (erule exE)
by (simp)

(*** prefix closed & prefix ***)

lemma prefix_closed_prop:
  "[| prefix_closed T ; t : T ; prefix s t |] ==> s : T"
apply (unfold prefix_closed_def)
by (blast)

(***********************************************************
                   convenient lemmas
 ***********************************************************)

(*** prefix a#v u ***)

lemma prefix_same_head_only_if:
  "prefix (<Ev a> ^^^ v) u 
    ==> (EX u'. u = <Ev a> ^^^ u' & prefix v u')"
apply (simp add: prefix_def)
apply (erule exE)
apply (rule_tac x="v ^^^ ua" in exI)
apply (simp add: appt_assoc)
by (rule_tac x="ua" in exI, simp)

lemma prefix_same_head_if:
  "(EX u'. u = <Ev a> ^^^ u' & prefix v u')
   ==> prefix (<Ev a> ^^^ v) u"
apply (simp add: prefix_def)
apply (elim conjE exE)
apply (rule_tac x="ua" in exI)
by (simp add: appt_assoc)

lemma prefix_same_head[simp]:
  "prefix (<Ev a> ^^^ v) u 
    = (EX u'. u = <Ev a> ^^^ u' & prefix v u')"
apply (rule iffI)
apply (simp add: prefix_same_head_only_if)
apply (simp add: prefix_same_head_if)
done

(*** prefix v a#u ***)

lemma prefix_same_head_inv_only_if:
  "prefix v (<Ev a> ^^^ u)
      ==> v = <> | (EX v'. v = <Ev a> ^^^ v' & prefix v' u)"
apply (simp add: prefix_def)
apply (erule exE)

apply (insert trace_nil_or_Tick_or_Ev)
apply (drule_tac x="v" in spec)
apply (erule disjE, simp)
apply (erule disjE, erule conjE, simp)

apply (elim exE conjE)
apply (simp add: appt_assoc)
apply (rule_tac x="ua" in exI)
by (simp)

lemma prefix_same_head_inv_if:
  "[| v = <> | (EX v'. v = <Ev a> ^^^ v' & prefix v' u) |]
      ==> prefix v (<Ev a> ^^^ u)"
by (auto)

lemma prefix_same_head_inv[simp]:
  "prefix v (<Ev a> ^^^ u) =
   (v = <> | (EX v'. v = <Ev a> ^^^ v' & prefix v' u))"
apply (rule iffI)
apply (simp add: prefix_same_head_inv_only_if)
apply (simp add: prefix_same_head_inv_if)
done

(*** prefix v u#a ***)

(* only if *)

lemma prefix_last_inv_only_if:
  "[| noTick u ; prefix v (u ^^^ <e>) |] 
   ==> (v = u ^^^ <e> | prefix v u)"
apply (simp add: prefix_def)
apply (elim exE conjE)
apply (simp)
apply (insert trace_last_nil_or_unnil)
apply (drule_tac x="ua" in spec)
apply (elim disjE conjE exE)
apply (simp_all)
apply (simp add: appt_assoc_sym)
by (fast)

(* if *)

lemma prefix_last_inv_if:
  "[| noTick u ; v = u ^^^ <e> | prefix v u |] ==> prefix v (u ^^^ <e>)"
apply (erule disjE)
apply (simp)
apply (simp add: prefix_appt)
done

lemma prefix_last_inv[simp]:
  "noTick u ==> prefix v (u ^^^ <e>) = (v = u ^^^ <e> | prefix v u)"
apply (rule iffI)
apply (simp add: prefix_last_inv_only_if)
apply (simp add: prefix_last_inv_if)
done

(*-------------------------*
 |          sett           |
 *-------------------------*)

lemma prefix_subsett: "prefix s t ==> sett s <= sett t"
apply (simp add: prefix_def)
apply (erule exE)
by (auto)

lemma prefix_noTick: "[| prefix s t ; noTick t |] ==> noTick s"
apply (simp add: noTick_def)
apply (simp add: prefix_def)
apply (erule exE)
by (simp)

(*-------------------------*
 |         Tick            |
 *-------------------------*)

lemma prefix_Tick: "(prefix (<Tick>) t) = (t = <Tick>)"
by (simp add: prefix_def)

(****************** to add it again ******************)

declare disj_not1   [simp]

end
