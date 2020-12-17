           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Trace_op
imports Trace_hide Trace_par Trace_ren Trace_seq
begin

(*****************************************************************

         1. 

 *****************************************************************)

(* -------------- *
     hide & seq
 * -------------- *)

lemma rmTick_hide: "rmTick s --tr X = rmTick (s --tr X)"
apply (insert trace_last_noTick_or_Tick)
apply (drule_tac x="s" in spec)
apply (auto)
done

(* -------------- *
     hide & par
 * -------------- *)

lemma interleave_of_hide_tr_lm:
  "ALL s t. u : s |[{}]|tr t --> (u --tr X : s --tr X |[{}]|tr t --tr X)"
apply (induct_tac u rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (simp add: par_tr_head)
apply (elim exE disjE)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="t" in spec)
 apply (simp)
 apply (case_tac "a:X")
  apply (simp)
  apply (simp add: par_tr_head)

 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="t'" in spec)
 apply (simp)
 apply (case_tac "a:X")
  apply (simp)
  apply (simp add: par_tr_head)
done

(* interleave_of_hide_tr *)

lemma interleave_of_hide_tr:
  "u : s |[{}]|tr t ==> (u --tr X : s --tr X |[{}]|tr t --tr X)"
by (simp add: interleave_of_hide_tr_lm)


(* -------------------------------------------------------------- *)

lemma interleave_of_hide_tr_ex_only_if_lm:
  "ALL s t. u : s --tr X |[{}]|tr t --tr X -->
   (EX v. u = v --tr X & v : s |[{}]|tr t)"
apply (induct_tac u rule: induct_trace)

(* <> *)
apply (simp_all)
apply (intro allI impI)
apply (rule_tac x="s ^^^t" in exI)
apply (subgoal_tac "noTick s  & noTick t")
apply (simp)
apply (rule interleave_appt_left)
apply (rule interleave_appt_right)
apply (simp_all)
apply (subgoal_tac "noTick (s --tr X)  & noTick (t --tr X)")
apply (elim conjE)
apply (erule rem_asmE)
apply (erule rem_asmE)
apply (simp)
apply (simp)

(* <Tick> *)
apply (intro allI impI)
apply (simp add: hide_tr_Tick_sett)
apply (elim conjE exE)
apply (simp)
apply (rule_tac x="s' ^^^ s'a ^^^ <Tick>" in exI)
apply (simp)
apply (simp add: hide_tr_nilt_sett)
apply (rule interleave_appt_left)
apply (rule interleave_appt_right)
apply (simp_all)

(* step *)
 apply (intro allI impI)
 apply (simp add: par_tr_head)
 apply (elim disjE conjE exE)

 (* left *)
  apply (simp add: hide_tr_decompo)
  apply (elim conjE exE)
  apply (simp)
  apply (drule_tac x="t'" in spec)
  apply (drule_tac x="t" in spec)
  apply (simp)
  apply (elim conjE exE)
  apply (simp)
  apply (rule_tac x="s'a ^^^ v" in exI)
  apply (erule disjE)

   apply (simp)
   apply (rule interleave_appt_left)
   apply (simp)
   apply (simp)

   apply (simp)
   apply (subgoal_tac "noTick s'a")
   apply (simp)
   apply (rule interleave_appt_left)
   apply (simp)
   apply (simp)
   apply (subgoal_tac "noTick (s'a --tr X)")
   apply (simp)
   apply (rotate_tac 2)
   apply (drule sym)
   apply (simp)

 (* right *)
  apply (simp add: hide_tr_decompo)
  apply (elim conjE exE)
  apply (simp)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="t'a" in spec)
  apply (simp)
  apply (elim conjE exE)
  apply (simp)
  apply (rule_tac x="s' ^^^ v" in exI)
  apply (erule disjE)

   apply (simp)
   apply (rule interleave_appt_right)
   apply (simp)
   apply (simp)

   apply (simp)
   apply (subgoal_tac "noTick s'")
   apply (simp)
   apply (rule interleave_appt_right)
   apply (simp)
   apply (simp)
   apply (subgoal_tac "noTick (s' --tr X)")
   apply (simp)
   apply (rotate_tac 2)
   apply (drule sym)
   apply (simp)
done

lemma interleave_of_hide_tr_ex_only_if:
  "u : s --tr X |[{}]|tr t --tr X ==>
    EX v. u = v --tr X & v : s |[{}]|tr t"
by (simp add: interleave_of_hide_tr_ex_only_if_lm)

(* interleave_of_hide_tr_ex *)

lemma interleave_of_hide_tr_ex:
  "(u : s --tr X |[{}]|tr t --tr X) =
   (EX v. u = v --tr X & v : s |[{}]|tr t)"
apply (rule)
apply (simp add: interleave_of_hide_tr_ex_only_if)
apply (elim conjE exE)
apply (simp add: interleave_of_hide_tr)
done



(* --------------------------------------------------- *
        distribution renaming over Interleaving
 * --------------------------------------------------- *)

lemma interleave_of_ren_tr_only_if_all:
   "ALL u r v s t. (u : s |[{}]|tr t & u [[r]]* v)
       --> (EX s' t'.  v : s' |[{}]|tr t' & s [[r]]* s' & t [[r]]* t')"
apply (rule allI)
apply (rule allI)
apply (induct_tac u rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (elim conjE exE)
apply (simp add: ren_tr_decompo_left)
apply (elim conjE exE)
apply (simp)
apply (simp add: par_tr_head)
 apply (elim disjE conjE exE)
 apply (simp)
 apply (drule_tac x="ta" in spec)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="t" in spec)
 apply (simp)
 apply (elim conjE exE)

 apply (rule_tac x="<Ev b> ^^^ s'a" in exI)
 apply (simp)
 apply (rule_tac x="t'" in exI)
 apply (simp)

 apply (simp)
 apply (drule_tac x="ta" in spec)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="t'" in spec)
 apply (simp)
 apply (elim conjE exE)

 apply (rule_tac x="s'" in exI)
 apply (simp)
 apply (rule_tac x="<Ev b> ^^^ t'a" in exI)
 apply (simp)
done

lemma interleave_of_ren_tr_only_if:
   "[|u : s |[{}]|tr t ; u [[r]]* v |]
    ==> (EX s' t'.  v : s' |[{}]|tr t' & s [[r]]* s' & t [[r]]* t')"
apply (insert interleave_of_ren_tr_only_if_all)
apply (drule_tac x="u" in spec)
apply (drule_tac x="r" in spec)
apply (drule_tac x="v" in spec)
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
apply (simp)
done

lemma interleave_of_ren_tr_if_all:
   "ALL v r s t s' t'. (v : s' |[{}]|tr t' & s [[r]]* s' & t [[r]]* t')
       --> (EX u. u : s |[{}]|tr t & u [[r]]* v)"
apply (rule allI)
apply (rule allI)
apply (induct_tac v rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (elim conjE exE)
apply (simp add: par_tr_head)
apply (elim disjE conjE exE)

 apply (simp add: ren_tr_decompo_right)
 apply (elim disjE conjE exE)
 apply (simp)
 apply (drule_tac x="sb" in spec)
 apply (drule_tac x="t" in spec)
 apply (drule mp)
 apply (force)
 apply (elim disjE conjE exE)
 apply (rule_tac x="<Ev aa> ^^^ u" in exI)
 apply (simp)
 apply (simp add: par_tr_head)

 apply (simp add: ren_tr_decompo_right)
 apply (elim disjE conjE exE)
 apply (simp)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="sb" in spec)
 apply (drule mp)
 apply (force)
 apply (elim disjE conjE exE)
 apply (rule_tac x="<Ev aa> ^^^ u" in exI)
 apply (simp)
 apply (simp add: par_tr_head)
done

lemma interleave_of_ren_tr_if:
   "[| v : s' |[{}]|tr t' ; s [[r]]* s' ; t [[r]]* t' |]
    ==> (EX u. u : s |[{}]|tr t & u [[r]]* v)"
apply (insert interleave_of_ren_tr_if_all)
apply (drule_tac x="v" in spec)
apply (drule_tac x="r" in spec)
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
apply (drule_tac x="s'" in spec)
apply (drule_tac x="t'" in spec)
apply (simp)
done

(* ------------------------------- *
         Renaming channel
 * ------------------------------- *)

(* Renaming_channel & rest-tr *)

lemma ren_tr_rest_Renaming_channel[rule_format]:
  "ALL s1 s2. 
   (inj right & inj mid & inj left &
   (ALL x y. right x ~= mid y) &
   (ALL x y. left x ~= mid y) &
   (ALL x y. right x ~= left y) &
    s1 [[right<==>mid]]* (s rest-tr (range left Un range mid)) &
    s2 [[left<==>mid]]* (s rest-tr (range mid Un range right)))
    --> (s1 rest-tr range right) [[right<==>left]]* (s2 rest-tr range left)"
apply (induct_tac s rule: induct_trace)
apply (simp)
apply (simp)
apply (intro allI impI)
apply (simp)
 (* 1 *)
 apply (case_tac "a : range mid")
 apply (simp add: ren_tr_decompo_right)
 apply (elim conjE exE)
 apply (simp)

 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp)
 apply (simp add: pair_in_Renaming_channel)

 (* 2 *)
 apply (case_tac "a : range left")
 apply (subgoal_tac "a ~: range right")
 apply (simp)
 apply (simp add: ren_tr_decompo_right)
 apply (elim conjE exE)
 apply (simp)

 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp)
 apply (elim add_not_eq_symE)

 apply (simp add: pair_in_Renaming_channel)
 apply (subgoal_tac "(left x) ~: range right")
 apply (simp)
 apply (force)
 apply (elim conjE exE)
 apply (simp)
 apply (elim add_not_eq_symE)
 apply (force)

 (* 3 *)
 apply (case_tac "a : range right")
 apply (subgoal_tac "a ~: range left")
 apply (simp)
 apply (simp add: ren_tr_decompo_right)
 apply (elim conjE exE)
 apply (simp)

 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp)
 apply (elim add_not_eq_symE)

 apply (simp add: pair_in_Renaming_channel)
 apply (subgoal_tac "(right x) ~: range left")
 apply (simp)
 apply (force)

 apply (elim conjE exE)
 apply (elim add_not_eq_symE)
 apply (force)

apply (simp)
done

(* no renaming events *)

lemma Renaming_channel_tr_rest_eq[rule_format]:
  "ALL s t.
   (inj f & inj g & (ALL x y. f x ~= g y) &
    range f Int Y = {} & range g Int Y = {} & s [[f<==>g]]* t)
   --> s rest-tr Y = t rest-tr Y"
apply (rule)
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (elim conjE)
apply (simp add: ren_tr_decompo_left)
apply (elim conjE exE)
apply (simp)
 (* 1 *)
 apply (case_tac "(ALL x. a ~= f x) & (ALL x. a ~= g x)")
 apply (simp add: pair_in_Renaming_channel)
 (* 2 *)
 apply (simp)
 apply (elim disjE exE)
  apply (simp add: pair_in_Renaming_channel)
  apply (subgoal_tac "f x ~: Y & g x ~: Y")
  apply (simp)
  apply (blast)

  apply (simp)
  apply (elim add_not_eq_symE)
  apply (simp add: pair_in_Renaming_channel)
  apply (subgoal_tac "f x ~: Y & g x ~: Y")
  apply (simp)
  apply (blast)
done

lemma Renaming_channel_tr_rest_eq_range:
  "[| inj f ; inj g ; ALL x y. f x ~= g y ; 
      ALL x y. f x ~= h y ; ALL x y. g x ~= h y ;
      s [[f<==>g]]* t |]
   ==> s rest-tr range h = t rest-tr range h"
apply (rule Renaming_channel_tr_rest_eq[of f g "range h" s t])
apply (auto)
done


(* --- Renaming channel & sett 2 (no used) --- *)

lemma Renaming_channel_range_sett_lm[rule_format]:
  "ALL t s.
   (inj f & inj h & inj g &
   (ALL x y. f x ~= g y) &
   (ALL x y. f x ~= h y) &
   (ALL x y. g x ~= h y) &
   (s [[f<==>g]]* (t rest-tr (range f Un range h))))
   --> sett s <= insert Tick (Ev ` (range g Un range h))"
apply (rule)
apply (induct_tac t rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (elim exE conjE)
apply (simp)

 (* 1 *)
 apply (case_tac "a : range f")
 apply (simp)
 apply (simp add: ren_tr_decompo_right)
 apply (elim conjE exE)
 apply (simp)

 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp)
 apply (elim add_not_eq_symE)
 apply (simp add: pair_in_Renaming_channel)
 apply (fast)

 (* 2 *)
 apply (case_tac "a : range h")
 apply (simp)
 apply (simp add: ren_tr_decompo_right)
 apply (elim conjE exE)
 apply (simp)

 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp)
 apply (elim add_not_eq_symE)
 apply (simp add: pair_in_Renaming_channel)
 apply (fast)

 (* 3 *)
 apply (simp)
done

lemma Renaming_channel_range_sett1:
  "[| inj f ; inj h ; inj g ;
      (ALL x y. f x ~= g y) ;
      (ALL x y. f x ~= h y) ;
      (ALL x y. g x ~= h y) ;
      (s [[f<==>g]]* (t rest-tr (range f Un range h))) |]
   ==> sett s <= insert Tick (Ev ` (range g Un range h))"
apply (rule Renaming_channel_range_sett_lm)
apply (auto)
done

lemma Renaming_channel_range_sett2:
  "[| inj f ; inj h ; inj g ;
      (ALL x y. f x ~= g y) ;
      (ALL x y. f x ~= h y) ;
      (ALL x y. g x ~= h y) ;
      (s [[f<==>g]]* (t rest-tr (range h Un range f))) |]
   ==> sett s <= insert Tick (Ev ` (range h Un range g))"
apply (simp add: Un_sym)
apply (simp add: Renaming_channel_range_sett1)
done

lemma Renaming_channel_range_sett3:
  "[| inj f ; inj h ; inj g ;
      (ALL x y. f x ~= g y) ;
      (ALL x y. f x ~= h y) ;
      (ALL x y. g x ~= h y) ;
      (s [[g<==>f]]* (t rest-tr (range f Un range h))) |]
   ==> sett s <= insert Tick (Ev ` (range g Un range h))"
apply (simp add: Renaming_commut)
apply (simp add: Renaming_channel_range_sett1)
done

lemma Renaming_channel_range_sett4:
  "[| inj f ; inj h ; inj g ;
      (ALL x y. f x ~= g y) ;
      (ALL x y. f x ~= h y) ;
      (ALL x y. g x ~= h y) ;
      (s [[g<==>f]]* (t rest-tr (range h Un range f))) |]
   ==> sett s <= insert Tick (Ev ` (range h Un range g))"
apply (simp add: Renaming_commut)
apply (simp add: Renaming_channel_range_sett2)
done

lemmas Renaming_channel_range_sett =
       Renaming_channel_range_sett1
       Renaming_channel_range_sett2
       Renaming_channel_range_sett3
       Renaming_channel_range_sett4

(* --- compose restricted traces --- *) 

lemma Renaming_channel_tr_par_comp[rule_format]:
   "ALL n s t.
   (inj f & inj h & inj g &
   (ALL x y. f x ~= g y) &
   (ALL x y. f x ~= h y) &
   (ALL x y. g x ~= h y) &
    lengtht s + lengtht t <= n &
    sett(s) <= insert Tick (Ev ` (range f Un range g)) &
    sett(t) <= insert Tick (Ev ` (range f Un range g)) &
    (s rest-tr range f) [[f<==>g]]* (t rest-tr range g) &
   ((noTick s & noTick t & noTick u) | (~noTick s & ~noTick t & ~noTick u)))
   --> (EX sh th. 
         (EX v. v : sh |[range h]|tr th) &
          s [[f<==>h]]* sh &
          t [[g<==>h]]* th)"
apply (rule)
apply (induct_tac n)

(* n=0 *)
apply (intro allI impI)
apply (elim conjE exE)
apply (simp add: lengtht_zero)

(* Suc n *)
apply (intro allI impI)
apply (elim conjE exE)
apply (simp)
apply (insert trace_nil_or_Tick_or_Ev)
apply (rotate_tac -1)
apply (frule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
apply (rotate_tac -2)
apply (erule disjE)
apply (erule disjE)
apply (simp)

apply (rotate_tac -1)
apply (erule disjE)

 (* s=<>, t=<Tick> *)
 apply (simp)

 (* s=<>, t=<Ev a> ^^^ sa *)
 apply (elim conjE exE)
 apply (simp)
 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (erule disjE)

  (* EX x. a = f x *)
  apply (elim exE)
  apply (simp)
  apply (drule_tac x="<>" in spec)
  apply (drule_tac x="sa" in spec)
  apply (simp)
  apply (elim conjE exE)
  apply (rule_tac x="<Ev (f x)> ^^^ th" in exI)
  apply (simp add: pair_in_Renaming_channel)
  apply (rule_tac x="<Ev (f x)> ^^^ v" in exI)
  apply (simp add: par_tr_head)
  apply (fast)

  (* EX x. a = g x *)
  apply (elim exE)
  apply (simp)

apply (rotate_tac -1)
apply (erule disjE)

(* s=<Tick> *)
 apply (simp)
 apply (erule disjE)

 (* s=<Tick>, t=<Tick> *)
  apply (simp)

  (* s=<Tick>, t=<Ev a> ^^^ sa *)
  apply (elim conjE exE)
  apply (simp)
  apply (simp add: image_iff)
  apply (elim conjE exE)
  apply (erule disjE)

   (* EX x. a = f x *)
   apply (elim exE)
   apply (simp)
   apply (drule_tac x="<Tick>" in spec)
   apply (drule_tac x="sa" in spec)
   apply (simp)
   apply (elim conjE exE)
   apply (rule_tac x="<Ev (f x)> ^^^ th" in exI)
   apply (simp add: pair_in_Renaming_channel)
   apply (rule_tac x="<Ev (f x)> ^^^ v" in exI)
   apply (simp add: par_tr_head)
   apply (fast)

   (* EX x. a = g x *)
   apply (elim exE)
   apply (simp)

(* s = <Ev a> ^^^ sa *)
apply (elim conjE exE)
apply (simp)
apply (simp add: image_iff)
apply (elim conjE exE)

apply (rotate_tac -2)
apply (erule disjE)
apply (elim conjE exE)
apply (simp)

apply (simp add: ren_tr_decompo_left)
apply (elim conjE exE)
apply (simp add: pair_in_Renaming_channel)

apply (simp add: rest_tr_decompo)
apply (elim conjE exE)
apply (simp)

apply (drule_tac x="sa" in spec)
apply (drule_tac x="t'" in spec)
apply (drule mp)
apply (simp)
apply (case_tac "noTick s'")
apply (simp)
apply (simp)

apply (elim conjE exE)
apply (rule_tac x="<Ev (h x)> ^^^ sh" in exI)
apply (rotate_tac -7)
apply (drule sym)
apply (insert Ev_rest_tr_decompo)
apply (drule_tac x="s'" in spec)
apply (drule_tac x="range g" in spec)
apply (drule_tac x="g x" in spec)
apply (simp)
apply (elim conjE exE)
apply (simp)

apply (subgoal_tac 
  "sett s1 Int Ev ` range h = {} & sett s2 Int Ev ` range h = {}")
apply (rule_tac x="(s1 ^^^ <Ev (h x)> ^^^ s2) ^^^ th" in exI)
apply (rule conjI)
apply (rule_tac x="(s1 ^^^ <Ev (h x)> ^^^ s2) ^^^ v" in exI)
apply (simp add: appt_assoc)
apply (simp add: rest_tr_nilt_sett)
apply (fold noTick_def)
apply (rule par_tr_app_right)
apply (simp add: par_tr_head)
apply (rule par_tr_app_right)
apply (simp)

(* ren *)

apply (rule ren_tr_appt)
apply (rule ren_tr_appt)
apply (rule Renaming_channel_id)
apply (simp add: rest_tr_nilt_sett)
apply (rule ren_tr_Ev)
apply (rule Renaming_channel_id)
apply (simp add: rest_tr_nilt_sett)
apply (simp add: pair_in_Renaming_channel)
apply (simp_all)
apply (rule conjI)

apply (simp add: disjoint_eq_subset_Compl)
apply (rule)
apply (simp)
apply (elim conjE exE)
apply (elim add_not_eq_symE)
apply (rotate_tac -6)
apply (erule subsetE)
apply (drule_tac x="xa" in bspec, simp)
apply (force)

apply (simp add: disjoint_eq_subset_Compl)
apply (rule)
apply (simp)
apply (elim conjE exE)
apply (elim add_not_eq_symE)
apply (rotate_tac -5)
apply (erule subsetE)
apply (drule_tac x="xa" in bspec, simp)
apply (force)

apply (elim conjE exE)
apply (simp)
apply (subgoal_tac "g x ~: range f")
apply (simp)

apply (drule_tac x="sa" in spec)
apply (rotate_tac -1)
apply (drule_tac x="t" in spec)
apply (drule mp)
apply (simp)
apply (elim conjE exE)

apply (rule_tac x="<Ev (g x)> ^^^ sh" in exI)
apply (rule_tac x="th" in exI)
apply (simp)
apply (elim add_not_eq_symE)
apply (simp add: pair_in_Renaming_channel)
apply (rule_tac x="<Ev (g x)> ^^^ v" in exI)
apply (simp add: par_tr_head)
apply (rule disjI2)
apply (force)
apply (elim add_not_eq_symE)
apply (force)
done




(* -------------- distribution Renaming over restriction -------------- *)


lemma Renaming_channel_rest_tr_dist_only_if:
 "ALL n s t smid tmid. (inj left & inj mid & inj right &
      (ALL x y. right x ~= mid y)  &
      (ALL x y. left x ~= mid y)  &
      (ALL x y. right x ~= left y)  &
      lengtht s + lengtht t <= n &
      (s rest-tr range right) [[right<==>left]]* (t rest-tr range left) &
      s [[right<==>mid]]* smid &
      t [[left<==>mid]]* tmid)
    --> smid rest-tr range mid = tmid rest-tr range mid"
apply (rule)
apply (induct_tac n)
apply (simp add: lengtht_zero)

 (* Suc n *)
 apply (intro allI impI)
 apply (elim conjE exE)
 apply (elim add_not_eq_symE)
 apply (insert trace_nil_or_Tick_or_Ev)
 apply (rotate_tac -1)
 apply (frule_tac x="s" in spec)
 apply (drule_tac x="t" in spec)
 apply (elim disjE conjE exE)
 apply (simp_all)

 (* 1 *)
 apply (simp add: ren_tr_decompo_left)
 apply (elim conjE exE)
 apply (case_tac "a : range left Un range mid")
 apply (simp add: image_iff)
 apply (elim disjE conjE exE)
 apply (simp)
 apply (simp)
 apply (simp add: pair_in_Renaming_channel)
 apply (simp add: image_iff)
  apply (drule_tac x="<>" in spec)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="<>" in spec)
  apply (drule_tac x="ta" in spec)
  apply (simp)

 (* 2 *)
 apply (simp add: ren_tr_decompo_left)
 apply (simp add: image_iff)
 apply (elim conjE exE)
  apply (simp add: pair_in_Renaming_channel)
  apply (drule_tac x="<>" in spec)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="<>" in spec)
  apply (drule_tac x="ta" in spec)
  apply (simp)
  apply (simp add: image_iff)

 (* 3 *)
 apply (simp add: ren_tr_decompo_left)
 apply (elim disjE conjE exE)
 apply (case_tac "a : range right Un range mid")
 apply (simp add: image_iff)
 apply (elim disjE conjE exE)
 apply (simp)
 apply (simp)
 apply (simp add: pair_in_Renaming_channel)
 apply (simp add: image_iff)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="<>" in spec)
  apply (drule_tac x="ta" in spec)
  apply (drule_tac x="<>" in spec)
  apply (simp)

 (* 4 *)
 apply (simp add: ren_tr_decompo_left)
 apply (simp add: image_iff)
 apply (elim conjE exE)
  apply (simp add: pair_in_Renaming_channel)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="<>" in spec)
  apply (drule_tac x="ta" in spec)
  apply (drule_tac x="<>" in spec)
  apply (simp add: image_iff)

 (* 5 *)
 apply (simp add: ren_tr_decompo_left)
 apply (elim conjE exE)
 apply (case_tac "a : range left Un range mid")
  apply (simp add: image_iff)
  apply (elim disjE conjE exE)
  apply (simp)
  apply (simp add: image_iff)
  apply (simp add: pair_in_Renaming_channel)
  apply (simp add: pair_in_Renaming_channel)
  apply (simp add: image_iff)
  apply (drule_tac x="<Tick>" in spec)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="<Tick>" in spec)
  apply (drule_tac x="ta" in spec)
  apply (simp)

  apply (simp add: image_iff)
  apply (simp add: pair_in_Renaming_channel)
  apply (simp add: image_iff)
  apply (drule_tac x="<Tick>" in spec)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="<Tick>" in spec)
  apply (drule_tac x="ta" in spec)
  apply (simp)

 (* 6 *)
 apply (simp add: ren_tr_decompo_left)
 apply (elim conjE exE)
 apply (case_tac "a : range right Un range mid")
  apply (simp add: image_iff)
  apply (elim disjE conjE exE)
  apply (simp)
  apply (simp add: image_iff)
  apply (simp add: pair_in_Renaming_channel)
  apply (simp add: pair_in_Renaming_channel)
  apply (simp add: image_iff)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="<Tick>" in spec)
  apply (drule_tac x="ta" in spec)
  apply (drule_tac x="<Tick>" in spec)
  apply (simp)

  apply (simp add: image_iff)
  apply (simp add: pair_in_Renaming_channel)
  apply (simp add: image_iff)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="<Tick>" in spec)
  apply (drule_tac x="ta" in spec)
  apply (drule_tac x="<Tick>" in spec)
  apply (simp)

 (* 7 *)
 apply (simp add: ren_tr_decompo_left)
 apply (elim disjE conjE exE)
 apply (elim add_not_eq_symE)
 apply (case_tac "a : range right Un range mid")
  apply (case_tac "aa : range left Un range mid")

   (* 7.1 *)
   apply (simp add: image_iff)
   apply (elim disjE conjE exE)

    apply (simp add: pair_in_Renaming_channel)
    apply (drule_tac x="sa" in spec)
    apply (drule_tac x="sb" in spec)
    apply (drule_tac x="ta" in spec)
    apply (drule_tac x="tb" in spec)
    apply (simp add: pair_in_Renaming_channel)

    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="s" in spec)
    apply (drule_tac x="sb" in spec)
    apply (drule_tac x="smid" in spec)
    apply (drule_tac x="tb" in spec)
    apply (simp add: pair_in_Renaming_channel)

    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="sa" in spec)
    apply (drule_tac x="t" in spec)
    apply (drule_tac x="ta" in spec)
    apply (drule_tac x="tmid" in spec)
    apply (simp add: pair_in_Renaming_channel)

    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="sa" in spec)
    apply (drule_tac x="sb" in spec)
    apply (drule_tac x="ta" in spec)
    apply (drule_tac x="tb" in spec)
    apply (simp add: pair_in_Renaming_channel)

  (* 7.2 *)
  (* ~(aa : range left Un range mid) *)
   apply (simp add: image_iff)
   apply (elim disjE conjE exE)

    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="s" in spec)
    apply (drule_tac x="sb" in spec)
    apply (drule_tac x="smid" in spec)
    apply (drule_tac x="tb" in spec)
    apply (simp add: pair_in_Renaming_channel)

    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="sa" in spec)
    apply (drule_tac x="sb" in spec)
    apply (drule_tac x="ta" in spec)
    apply (drule_tac x="tb" in spec)
    apply (simp add: pair_in_Renaming_channel)

 (* ~(a : range right Un range mid) *)

  apply (case_tac "aa : range left Un range mid")

   (* 7.3 *)
   apply (simp add: image_iff)
   apply (elim disjE conjE exE)

    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="sa" in spec)
    apply (drule_tac x="t" in spec)
    apply (drule_tac x="ta" in spec)
    apply (drule_tac x="tmid" in spec)
    apply (simp add: pair_in_Renaming_channel)

    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="sa" in spec)
    apply (drule_tac x="sb" in spec)
    apply (drule_tac x="ta" in spec)
    apply (drule_tac x="tb" in spec)
    apply (simp add: pair_in_Renaming_channel)

  (* 7.4 *)
  (* ~(aa : range left Un range mid) *)
   apply (simp add: image_iff)
   apply (elim disjE conjE exE)

    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="sa" in spec)
    apply (drule_tac x="sb" in spec)
    apply (drule_tac x="ta" in spec)
    apply (drule_tac x="tb" in spec)
    apply (simp add: pair_in_Renaming_channel)
done


lemma Renaming_channel_rest_tr_dist_if:
 "ALL n s t smid tmid. (inj left & inj mid & inj right &
      (ALL x y. right x ~= mid y)  &
      (ALL x y. left x ~= mid y)  &
      (ALL x y. right x ~= left y)  &
      lengtht s + lengtht t <= n &
      sett s <= insert Tick (Ev ` (range left Un range right)) &
      sett t <= insert Tick (Ev ` (range left Un range right)) &
      smid rest-tr range mid = tmid rest-tr range mid &
      s [[right<==>mid]]* smid &
      t [[left<==>mid]]* tmid)
    --> (s rest-tr range right) [[right<==>left]]* (t rest-tr range left)"
apply (rule)
apply (induct_tac n)
apply (simp add: lengtht_zero)

 (* Suc n *)
 apply (intro allI impI)
 apply (elim conjE exE)
 apply (insert trace_nil_or_Tick_or_Ev)
 apply (rotate_tac -1)
 apply (frule_tac x="s" in spec)
 apply (drule_tac x="t" in spec)
 apply (elim disjE conjE exE)
 apply (simp_all)

 (* 1 *)
 apply (simp add: ren_tr_decompo_left)
 apply (simp add: image_iff)
 apply (elim disjE conjE exE)
  apply (simp add: pair_in_Renaming_channel)
  apply (simp)
  apply (drule_tac x="<>" in spec)
  apply (drule_tac x="sa" in spec)
  apply (simp)
  apply (drule mp)
  apply (rule_tac x="ta" in exI)
  apply (simp)
  apply (simp)
  apply (elim add_not_eq_symE)
  apply (subgoal_tac "right x ~: range left", simp)
  apply (force)

 (* 2 *)
 apply (simp add: ren_tr_decompo_left)
 apply (simp add: image_iff)
 apply (elim disjE conjE exE)
  apply (simp)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="<>" in spec)
  apply (simp)
  apply (drule mp)
  apply (rule_tac x="ta" in exI)
  apply (simp)
  apply (simp)
  apply (elim add_not_eq_symE)
  apply (subgoal_tac "left x ~: range right", simp)
  apply (force)
  apply (simp add: pair_in_Renaming_channel)

 (* 3 *)
 apply (simp add: ren_tr_decompo_left)
 apply (simp add: image_iff)
 apply (elim disjE conjE exE)
  apply (simp add: pair_in_Renaming_channel)
  apply (simp)
  apply (elim disjE conjE exE)
   apply (case_tac "b : range mid", simp, simp)
   apply (simp)
  apply (drule_tac x="<Tick>" in spec)
  apply (drule_tac x="sa" in spec)
  apply (simp)
  apply (drule mp)
  apply (rule_tac x="ta" in exI)
  apply (simp)
  apply (simp)
  apply (elim add_not_eq_symE)
  apply (subgoal_tac "right x ~: range left", simp)
  apply (force)

 (* 4 *)
 apply (simp add: ren_tr_decompo_left)
 apply (simp add: image_iff)
 apply (elim disjE conjE exE)
  apply (simp)
  apply (elim disjE conjE exE)
   apply (case_tac "b : range mid", simp, simp)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="<Tick>" in spec)
  apply (simp)
  apply (drule mp)
  apply (rule_tac x="ta" in exI)
  apply (simp)
  apply (simp)
  apply (elim add_not_eq_symE)
  apply (subgoal_tac "left x ~: range right", simp)
  apply (force)
 apply (simp add: pair_in_Renaming_channel)

 (* 5 *)
 apply (simp add: image_iff)
 apply (elim disjE conjE exE)
 apply (simp_all)

  (* 5.1 *)
  apply (simp add: ren_tr_decompo_left)
  apply (elim conjE exE)
  apply (elim add_not_eq_symE)
  apply (simp add: pair_in_Renaming_channel)
  apply (subgoal_tac "left x ~: range mid", simp)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="<Ev (left xa)> ^^^ sb" in spec)
  apply (simp)
  apply (drule mp)
  apply (rule_tac x="ta" in exI)
  apply (rule_tac x="<Ev (mid xa)> ^^^ tb" in exI)
  apply (simp)
  apply (simp add: pair_in_Renaming_channel)
  apply (subgoal_tac "left x ~: range right", simp)
  apply (force)
  apply (force)

  (* 5.2 *)
  apply (simp add: ren_tr_decompo_left)
  apply (elim conjE exE)
  apply (elim add_not_eq_symE)
  apply (simp add: pair_in_Renaming_channel)
  apply (rotate_tac -5)
  apply (drule sym)
  apply (rotate_tac -4)
  apply (drule sym)
  apply (simp)
  apply (subgoal_tac "left x ~: range mid", simp)
  apply (subgoal_tac "right xa ~: range mid", simp)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="sb" in spec)
  apply (simp)
  apply (drule mp)
  apply (rule_tac x="ta" in exI)
  apply (rule_tac x="tb" in exI)
  apply (simp)
  apply (subgoal_tac "left x ~: range right", simp)
  apply (subgoal_tac "right xa ~: range left", simp)
  apply (force)
  apply (force)
  apply (force)
  apply (force)

  (* 5.3 *)
  apply (simp add: ren_tr_decompo_left)
  apply (elim conjE exE)
  apply (elim add_not_eq_symE)
  apply (simp add: pair_in_Renaming_channel)
  apply (subgoal_tac "xa = x")
  apply (simp)
  apply (drule_tac x="sa" in spec)
  apply (drule_tac x="sb" in spec)
  apply (simp)
  apply (drule mp)
  apply (rule_tac x="ta" in exI)
  apply (rule_tac x="tb" in exI)
  apply (simp)
  apply (simp)
  apply (simp add: inj_on_def)

  (* 5.4 *)
  apply (subgoal_tac "right xa ~: range left", simp)
  apply (rule ren_tr_Renaming_channel_sym_rule, simp_all)
  apply (simp add: ren_tr_decompo_left)
  apply (rule ren_tr_Renaming_channel_sym_rule, simp_all)
  apply (elim conjE exE)
  apply (elim add_not_eq_symE)
  apply (simp add: pair_in_Renaming_channel)
  apply (rotate_tac -5)
  apply (drule sym)
  apply (subgoal_tac "right xa ~: range mid", simp)
  apply (drule_tac x="<Ev (right x)> ^^^ sa" in spec)
  apply (drule_tac x="sb" in spec)
  apply (simp)
  apply (drule mp)
   apply (rule_tac x="<Ev (mid x)> ^^^ ta" in exI)
   apply (rule_tac x="tb" in exI)
   apply (simp add: pair_in_Renaming_channel)
  apply (simp)
  apply (force)
  apply (force)
done

lemma Renaming_channel_rest_tr_dist:
 "[| inj left ; inj mid ; inj right ;
      (ALL x y. right x ~= mid y)  ;
      (ALL x y. left x ~= mid y)  ;
      (ALL x y. right x ~= left y)  ;
      sett s <= insert Tick (Ev ` (range left Un range right)) ;
      sett t <= insert Tick (Ev ` (range left Un range right)) ;
      s [[right<==>mid]]* smid ;
      t [[left<==>mid]]* tmid |]
  ==> ((s rest-tr range right) [[right<==>left]]* (t rest-tr range left)) =
      (smid rest-tr range mid = tmid rest-tr range mid)"
apply (rule)

(* => *)
apply (insert Renaming_channel_rest_tr_dist_only_if[of left mid right])
apply (drule_tac x="lengtht s + lengtht t" in spec)
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
apply (drule_tac x="smid" in spec)
apply (drule_tac x="tmid" in spec)
apply (simp)

(* <= *)

apply (rotate_tac -1)
apply (erule rem_asmE)
apply (insert Renaming_channel_rest_tr_dist_if[of left mid right])
apply (drule_tac x="lengtht s + lengtht t" in spec)
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
apply (drule_tac x="smid" in spec)
apply (drule_tac x="tmid" in spec)
apply (simp)
done

(* ----------------- Renaming, rest-tr, dist ------------------- *)

lemma Renaming_channel_rest_tr_dist_only_if_EX:
 "[| inj left & inj mid & inj right ;
      (ALL x y. right x ~= mid y)  ;
      (ALL x y. left x ~= mid y)  ;
      (ALL x y. right x ~= left y)  ;
      EX s t.
      (s rest-tr range right) [[right<==>left]]* (t rest-tr range left) &
      s [[right<==>mid]]* smid &
      t [[left<==>mid]]* tmid |]
  ==> smid rest-tr range mid = tmid rest-tr range mid"
apply (elim conjE exE)
apply (insert Renaming_channel_rest_tr_dist_only_if[of left mid right])
apply (drule_tac x="lengtht s + lengtht t" in spec)
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
apply (drule_tac x="smid" in spec)
apply (drule_tac x="tmid" in spec)
apply (simp)
done

(* ----------------- TRenaming and rest-tr ------------------- *)

lemma Renaming_channel_rest_tr_eq_n:
  "ALL n s t s' t'.
   (inj f & inj g & (ALL x y. f x ~= g y) &
    lengtht s + lengtht t <= n &
    s rest-tr range f = t rest-tr range f &
    s [[f<==>g]]* s' &
    t [[f<==>g]]* t')
    --> s' rest-tr range g = t' rest-tr range g"
apply (rule)
apply (induct_tac n)

(* n=0 *)
apply (simp add: lengtht_zero)

(* Suc n *)
apply (intro allI impI)
apply (elim conjE exE)
apply (simp)
apply (insert trace_nil_or_Tick_or_Ev)
apply (rotate_tac -1)
apply (frule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
apply (rotate_tac -2)
apply (erule disjE)
apply (erule disjE)
apply (simp)

apply (rotate_tac -1)
apply (erule disjE)

 (* s=<>, t=<Tick> *)
 apply (simp)

 (* s=<>, t=<Ev a> ^^^ sa *)
 apply (elim conjE exE)
 apply (simp)

 apply (simp add: ren_tr_decompo_left)
 apply (elim conjE exE)
 apply (simp add: pair_in_Renaming_channel)
 apply (drule_tac x="<>" in spec)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="<>" in spec)
 apply (drule_tac x="ta" in spec)
 apply (simp)
 apply (case_tac "b ~: range g")
 apply (simp)
 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp add: pair_in_Renaming_channel)

 (* s=<Tick>, t=<> *)
 apply (rotate_tac -1)
 apply (erule disjE)
 apply (erule disjE)
 apply (simp)

 (* s=<Tick>, t=<Tick> *)
 apply (rotate_tac -1)
 apply (erule disjE)
 apply (simp)

 (* s=<Tick>, t=<Ev a> ^^^ sa *)
 apply (elim conjE exE)
 apply (simp)

 apply (simp add: ren_tr_decompo_left)
 apply (elim conjE exE)
 apply (simp add: pair_in_Renaming_channel)
 apply (drule_tac x="s" in spec)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="s'" in spec)
 apply (drule_tac x="ta" in spec)
 apply (simp)
  apply (erule disjE)
  apply (case_tac "a : range f")
  apply (simp)
  apply (simp)
 apply (case_tac "b ~: range g")
 apply (simp)
 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp add: pair_in_Renaming_channel)

 (* s=..., t=<> *)
 apply (erule disjE)
 apply (elim conjE exE)
 apply (simp)

 apply (simp add: ren_tr_decompo_left)
 apply (elim conjE exE)
 apply (simp add: pair_in_Renaming_channel)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="<>" in spec)
 apply (drule_tac x="ta" in spec)
 apply (drule_tac x="<>" in spec)
 apply (simp)
 apply (case_tac "b ~: range g")
 apply (simp)
 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp add: pair_in_Renaming_channel)

 (* s=..., t=<Tick> *)
 apply (erule disjE)
 apply (elim conjE exE)
 apply (simp)

 apply (simp add: ren_tr_decompo_left)
 apply (elim conjE exE)
 apply (simp add: pair_in_Renaming_channel)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="t" in spec)
 apply (drule_tac x="ta" in spec)
 apply (drule_tac x="t'" in spec)
 apply (simp)
  apply (erule disjE)
  apply (case_tac "a : range f")
  apply (simp)
  apply (simp)
 apply (case_tac "b ~: range g")
 apply (simp)
 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp add: pair_in_Renaming_channel)

 (* s=..., t=... *)
 apply (elim conjE exE)
 apply (simp)

 apply (simp add: ren_tr_decompo_left)
 apply (elim conjE exE)
 apply (elim add_not_eq_symE)
 apply (simp)

  (* a : range f *)
  apply (case_tac "a : range f")

   (* aa : range f *)
   apply (case_tac "aa : range f")

    apply (simp add: image_iff)
    apply (elim conjE exE)
    apply (simp add: pair_in_Renaming_channel)
    apply (drule_tac x="sa" in spec)
    apply (drule_tac x="sb" in spec)
    apply (drule_tac x="ta" in spec)
    apply (drule_tac x="tb" in spec)
    apply (simp)

   (* aa : range g *)
   apply (case_tac "aa : range g")

    apply (simp add: image_iff)
    apply (elim conjE exE)
    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="s" in spec)
    apply (drule_tac x="sb" in spec)
    apply (drule_tac x="s'" in spec)
    apply (drule_tac x="tb" in spec)
    apply (simp add: pair_in_Renaming_channel)

   (* aa ~: range f & aa ~: range g *)
    apply (simp)
    apply (simp add: image_iff)
    apply (elim conjE exE)
    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="s" in spec)
    apply (drule_tac x="sb" in spec)
    apply (drule_tac x="s'" in spec)
    apply (drule_tac x="tb" in spec)
    apply (simp add: pair_in_Renaming_channel)

  (* a : range g *)
  apply (case_tac "a : range g")

   (* aa : range f *)
   apply (case_tac "aa : range f")

    apply (simp add: image_iff)
    apply (elim conjE exE)
    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="sa" in spec)
    apply (drule_tac x="t" in spec)
    apply (drule_tac x="ta" in spec)
    apply (drule_tac x="t'" in spec)
    apply (simp add: pair_in_Renaming_channel)

   (* aa : range g *)
   apply (case_tac "aa : range g")

    apply (simp add: image_iff)
    apply (elim conjE exE)
    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="s" in spec)
    apply (drule_tac x="sb" in spec)
    apply (drule_tac x="s'" in spec)
    apply (drule_tac x="tb" in spec)
    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)

   (* aa ~: range f & aa ~: range g *)
    apply (simp add: image_iff)
    apply (elim conjE exE)
    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="s" in spec)
    apply (drule_tac x="sb" in spec)
    apply (drule_tac x="s'" in spec)
    apply (drule_tac x="tb" in spec)
    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)

 (* a ~: range f & a ~: range g *)

   (* aa : range f *)
   apply (case_tac "aa : range f")

    apply (simp add: image_iff)
    apply (elim conjE exE)
    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="sa" in spec)
    apply (drule_tac x="t" in spec)
    apply (drule_tac x="ta" in spec)
    apply (drule_tac x="t'" in spec)
    apply (simp add: pair_in_Renaming_channel)

   (* aa : range g *)
   apply (case_tac "aa : range g")

    apply (simp add: image_iff)
    apply (elim conjE exE)
    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="s" in spec)
    apply (drule_tac x="sb" in spec)
    apply (drule_tac x="s'" in spec)
    apply (drule_tac x="tb" in spec)
    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)

   (* aa ~: range f & aa ~: range g *)
    apply (simp add: image_iff)
    apply (elim conjE exE)
    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
    apply (drule_tac x="s" in spec)
    apply (drule_tac x="sb" in spec)
    apply (drule_tac x="s'" in spec)
    apply (drule_tac x="tb" in spec)
    apply (simp add: pair_in_Renaming_channel)
    apply (simp add: image_iff)
done


lemma Renaming_channel_rest_tr_eq_EX:
  "[| inj f ; inj g ; ALL x y. f x ~= g y ;
      EX s t. s rest-tr range f = t rest-tr range f &
              s [[f<==>g]]* s' &
              t [[f<==>g]]* t' |]
   ==> s' rest-tr range g = t' rest-tr range g"
apply (elim conjE exE)
apply (insert Renaming_channel_rest_tr_eq_n[of f g])
apply (drule_tac x="lengtht s + lengtht t" in spec)
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
apply (drule_tac x="s'" in spec)
apply (drule_tac x="t'" in spec)
apply (simp)
done



end
