           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory Trace_ren
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

(*************************************************************
               functions used for defining [[ ]]
 *************************************************************)

(* Isabelle 2005

consts
  renx :: "('a * 'b) set => ('a trace * 'b trace) set"

inductive "renx r"
intros
renx_nil: 
  "(<>, <>) : renx r"

renx_Tick: 
  "(<Tick>, <Tick>) : renx r"

renx_Ev: 
  "[| (s, t) : renx r ; (a, b) : r |]
   ==> (<Ev a> ^^^ s, <Ev b> ^^^ t) : renx r"
*)

inductive_set
  renx :: "('a * 'b) set => ('a trace * 'b trace) set"
  for r :: "('a * 'b) set"
where
renx_nil: 
  "(<>, <>) : renx r" |

renx_Tick: 
  "(<Tick>, <Tick>) : renx r" |

renx_Ev: 
  "[| (s, t) : renx r ; (a, b) : r |]
   ==> (<Ev a> ^^^ s, <Ev b> ^^^ t) : renx r" 

definition
  ren_tr :: "'a trace => ('a * 'b) set => 'b trace => bool"
                                    ("(_ [[_]]* _)" [1000,90,1000] 1000)
  where
  ren_tr_def : "s [[r]]* t == (( s, t) : renx r)"
  
(*
                                    ("(_ [[_]]* _)" [1000,90,1000] 1000)
in Isabelle 2005
*)
  
definition
  ren_inv :: "('a * 'b) set => 'b event set => 'a event set"
                                    ("([[_]]inv _)" [90,1000] 1000)
  where
  ren_inv_def: 
   "[[r]]inv X == 
      {ea. EX eb : X. ea = Tick & eb = Tick |
                      (EX a b. (a,b):r & ea = Ev a & eb = Ev b)}"

(*************************************************************
                 ren_tr intros and elims
 *************************************************************)

(*-------------------*
 |      intros       |
 *-------------------*)

lemma ren_tr_nil[simp]:
  "<> [[r]]* <>"
apply (simp add: ren_tr_def)
by (simp add: renx.intros)

lemma ren_tr_Tick[simp]: 
  "<Tick> [[r]]* <Tick>"
apply (simp add: ren_tr_def)
by (simp add: renx.intros)

lemma ren_tr_Ev: 
  "[| s [[r]]* t ; (a, b) : r |]
   ==> (<Ev a> ^^^ s) [[r]]* (<Ev b> ^^^ t)"
apply (simp add: ren_tr_def)
by (simp add: renx.intros)

(*** intro rule ***)

lemmas ren_tr_intros = ren_tr_Ev

(*-------------------*
 |       elims       |
 *-------------------*)

lemma ren_tr_elims_lm:
 "[| s [[r]]* t ;
     (s = <> & t = <>) --> P ;
     (s = <Tick> & t = <Tick>) --> P ;
     ALL a b s' t'.
        (s' [[r]]* t' & s = <Ev a> ^^^ s' & t = <Ev b> ^^^ t' & 
         (a, b) : r )
        --> P |]
  ==> P"
apply (simp add: ren_tr_def)
apply (erule renx.cases)    (* renx.elim --2007--> renx.cases *)
apply (simp_all)
done

(*** elim rule ***)

lemma ren_tr_elims:
 "[| s [[r]]* t ;
     [| s = <>; t = <> |] ==> P ;
     [| s = <Tick>; t = <Tick> |] ==> P ;
     !!a b s' t'.
        [| s' [[r]]* t' ; s = <Ev a> ^^^ s' ; t = <Ev b> ^^^ t' ;
            (a, b) : r |]
        ==> P |]
  ==> P"
apply (rule ren_tr_elims_lm[of s r t])
by (auto)

(*************************************************************
                 ren_tr decomposition
 *************************************************************)

(*-------------------*
 |     ren nil       |
 *-------------------*)

lemma ren_tr_nil1[simp]: "(<> [[r]]* s) = (s = <>)"
apply (rule iffI)
by (erule ren_tr_elims, simp_all)

lemma ren_tr_nil2[simp]: "(s [[r]]* <>) = (s = <>)"
apply (rule iffI)
by (erule ren_tr_elims, simp_all)

(*-------------------*
 |     ren Tick      |
 *-------------------*)

lemma ren_tr_Tick1[simp]: "(<Tick> [[r]]* s) = (s = <Tick>)"
apply (rule iffI)
by (erule ren_tr_elims, simp_all)

lemma ren_tr_Tick2[simp]: "(s [[r]]* <Tick>) = (s = <Tick>)"
apply (rule iffI)
by (erule ren_tr_elims, simp_all)

(*-------------------*
 |     ren Ev        |
 *-------------------*)

(*** left ***)

(* only if *)

lemma ren_tr_decompo_left_only_if: 
  "(<Ev a> ^^^ s) [[r]]* u 
    ==> (EX b t. u = <Ev b> ^^^ t & (a, b) : r & s [[r]]* t)"
apply (insert trace_nil_or_Tick_or_Ev)
apply (drule_tac x="u" in spec)

apply (erule disjE, simp)   (* <> --> contradict *)
apply (erule disjE, simp)   (* <Tick> --> contradict *)

apply (erule ren_tr_elims)
by (simp_all)

(* if *)

lemma ren_tr_decompo_left_if: 
  "[| (a, b) : r ; s [[r]]* t |]
    ==> (<Ev a> ^^^ s) [[r]]* (<Ev b> ^^^ t)"
apply (rule ren_tr_intros)
by (simp_all)

(* iff *)

lemma ren_tr_decompo_left: 
  "(<Ev a> ^^^ s) [[r]]* u
      = (EX b t. u = <Ev b> ^^^ t & (a, b) : r & s [[r]]* t)"
apply (rule iffI)
apply (simp add: ren_tr_decompo_left_only_if)
apply (elim exE)
apply (simp add: ren_tr_decompo_left_if)
done

(*** right ***)

(* only if *)

lemma ren_tr_decompo_right_only_if: 
  "u [[r]]* (<Ev b> ^^^ t)
    ==> (EX a s. u = <Ev a> ^^^ s & (a, b) : r & s [[r]]* t)"
 apply (insert trace_nil_or_Tick_or_Ev)
 apply (drule_tac x="u" in spec)

 apply (erule disjE, simp)   (* <> --> contradict *)
 apply (erule disjE, simp)   (* <Tick> --> contradict *)

 apply (erule ren_tr_elims)
by (simp_all)

(* if *)

lemma ren_tr_decompo_right_if: 
  "[| (a, b) : r ; s [[r]]* t |]
    ==> (<Ev a> ^^^ s) [[r]]* (<Ev b> ^^^ t)"
apply (rule ren_tr_intros)
by (simp_all)

(* iff *)

lemma ren_tr_decompo_right: 
  "u [[r]]* (<Ev b> ^^^ t)
     = (EX a s. u = <Ev a> ^^^ s & (a, b) : r & s [[r]]* t)"
apply (rule iffI)
apply (simp add: ren_tr_decompo_right_only_if)
apply (elim exE)
apply (simp add: ren_tr_decompo_right_if)
done

lemmas ren_tr_decompo = ren_tr_decompo_left ren_tr_decompo_right

(*-------------------*
 |     ren one       |
 *-------------------*)

lemma ren_tr_one[simp]: 
  "(a, b) : r ==> <Ev a> [[r]]* <Ev b>"
apply (insert ren_tr_Ev[of "<>" r "<>" a b])
by (simp)

(*** left ***)

lemma ren_tr_one_decompo_left_only_if: 
  "<Ev a> [[r]]* t ==> (EX b. t = <Ev b> & (a, b) : r)"
apply (insert ren_tr_decompo_left[of a "<>" r t])
by (simp)

lemma ren_tr_one_decompo_left: 
  "<Ev a> [[r]]* t = (EX b. t = <Ev b> & (a, b) : r)"
apply (rule iffI)
apply (simp add: ren_tr_one_decompo_left_only_if)
by (auto)

(*** right ***)

lemma ren_tr_one_decompo_right_only_if: 
  "s [[r]]* <Ev b> ==> (EX a. s = <Ev a> & (a, b) : r)"
apply (insert ren_tr_decompo_right[of s r b "<>"])
by (simp)

lemma ren_tr_one_decompo_right: 
  "s [[r]]* <Ev b> = (EX a. s = <Ev a> & (a, b) : r)"
apply (rule iffI)
apply (simp add: ren_tr_one_decompo_right_only_if)
by (auto)

lemmas ren_tr_one_decompo = ren_tr_one_decompo_left ren_tr_one_decompo_right

(*************************************************************
                   ren_tr notick
 *************************************************************)

(*** left ***)

lemma ren_tr_noTick_left_lm: "ALL r s t. (s [[r]]* t & noTick s) --> noTick t"
apply (rule allI)
apply (rule allI)
apply (induct_tac s rule: induct_trace)
apply (simp_all)

apply (intro allI impI)
apply (simp add: ren_tr_decompo)
apply (elim conjE exE)
by (simp)

(*** rule ***)

lemma ren_tr_noTick_left: "[| s [[r]]* t ; noTick s |] ==> noTick t"
apply (insert ren_tr_noTick_left_lm)
apply (drule_tac x="r" in spec)
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
by (simp)

(*** right ***)

lemma ren_tr_noTick_right_lm: "ALL r s t. (s [[r]]* t & noTick t) --> noTick s"
apply (rule allI)
apply (rule allI)
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (simp add: disj_not1)

apply (intro allI impI)
apply (simp add: ren_tr_decompo)
apply (elim conjE exE)
apply (drule mp)
apply (rule_tac x="ta" in exI)
by (simp_all)

(*** rule ***)

lemma ren_tr_noTick_right: "[| s [[r]]* t ; noTick t |] ==> noTick s"
apply (insert ren_tr_noTick_right_lm)
apply (drule_tac x="r" in spec)
apply (drule_tac x="s" in spec)
apply (drule_tac x="t" in spec)
by (simp)

(*************************************************************
                 ren_tr appending
 *************************************************************)

(*** noTick not None ***)

lemma ren_tr_appt_noTick_lm:
  "ALL r s1 s2 t1 t2.
     (s1 [[r]]* t1 & s2 [[r]]* t2 & (noTick s1 & noTick t1))
       --> (s1 ^^^ s2) [[r]]* (t1 ^^^ t2)"
apply (rule allI)
apply (rule allI)
apply (induct_tac s1 rule: induct_trace)
 apply (simp_all)

 apply (intro allI impI)
 apply (elim conjE)
 apply (erule ren_tr_elims)
 apply (simp_all)

 apply (simp add: appt_assoc)
 apply (simp add: ren_tr_decompo)
done

(*** rule ***)

lemma ren_tr_appt:
  "[| s1 [[r]]* t1 ; s2 [[r]]* t2 ; noTick s1 | noTick t1 | s2 = <> | t2 = <> |]
     ==> (s1 ^^^ s2) [[r]]* (t1 ^^^ t2)"
apply (elim disjE)
apply (simp add: ren_tr_appt_noTick_lm ren_tr_noTick_left)
apply (simp add: ren_tr_appt_noTick_lm ren_tr_noTick_right)
by (simp_all)

(*--------------------*
 |   <Ev a> ^^^ ...   |
 *--------------------*)

lemma ren_tr_appt_Ev:
  "[| (a, b) : r ; s [[r]]* t |]
     ==> (<Ev a> ^^^ s) [[r]]* (<Ev b> ^^^ t)"
apply (insert ren_tr_appt[of "<Ev a>" r "<Ev b>" s t])
by (simp_all)

(*-------------------*
 |     decompo       |
 *-------------------*)

(*** left ***)

(* only if *)

lemma ren_tr_appt_decompo_left_only_if_lm: 
  "ALL r s1 s2 t. ((s1 ^^^ s2) [[r]]* t & (noTick s1 | s2 = <>))
    --> (EX t1 t2. t = t1 ^^^ t2 & s1 [[r]]* t1 & s2 [[r]]* t2 
                 & (noTick t1 | t2 = <>))"
apply (rule allI)
apply (rule allI)
apply (induct_tac s1 rule: induct_trace)
apply (simp_all)

(* [Ev a] ^^^ ... *)
apply (intro allI impI)
apply (elim conjE exE)
apply (simp add: appt_assoc)
apply (simp add: ren_tr_decompo_left)
apply (elim conjE exE)
apply (drule_tac x="s2" in spec)
apply (drule_tac x="ta" in spec)
apply (simp)
apply (elim conjE exE)
apply (rule_tac x="<Ev b> ^^^ t1" in exI)
apply (rule_tac x="t2" in exI)
apply (simp add: appt_assoc)
done

(* rule *)

lemma ren_tr_appt_decompo_left_only_if: 
  "[| (s1 ^^^ s2) [[r]]* t ; noTick s1 | s2 = <> |]
    ==> (EX t1 t2. t = t1 ^^^ t2 & s1 [[r]]* t1 & s2 [[r]]* t2 
                 & (noTick t1 | t2 = <>))"
by (simp add: ren_tr_appt_decompo_left_only_if_lm)

(* iff *)

lemma ren_tr_appt_decompo_left:
  "noTick s1 | s2 = <>
   ==> (s1 ^^^ s2) [[r]]* t
      = (EX t1 t2. t = t1 ^^^ t2 & s1 [[r]]* t1 & s2 [[r]]* t2 
                 & (noTick t1 | t2 = <>))"
apply (rule iffI)
apply (simp add: ren_tr_appt_decompo_left_only_if)
apply (elim conjE exE)
apply (auto simp add: ren_tr_appt)
done

(*** right ***)

(* only if *)

lemma ren_tr_appt_decompo_right_only_if_lm: 
  "ALL r t1 t2 s. (s [[r]]* (t1 ^^^ t2) & (noTick t1 | t2 = <>))
    --> (EX s1 s2. s = s1 ^^^ s2 & s1 [[r]]* t1 & s2 [[r]]* t2 
                 & (noTick s1 | s2 = <>))"
apply (rule allI)
apply (rule allI)
apply (induct_tac t1 rule: induct_trace)
apply (simp_all)

(* [Ev a] ^^^ ... *)
apply (intro allI impI)
apply (elim conjE exE)
apply (simp add: appt_assoc)
apply (simp add: ren_tr_decompo_right)
apply (elim conjE exE)
apply (drule_tac x="t2" in spec)
apply (drule_tac x="sb" in spec)
apply (simp)
apply (elim conjE exE)
apply (rule_tac x="<Ev aa> ^^^ s1" in exI)
apply (rule_tac x="s2" in exI)
apply (simp add: appt_assoc)
done

(* rule *)

lemma ren_tr_appt_decompo_right_only_if: 
  "[| s [[r]]* (t1 ^^^ t2) ; noTick t1 | t2 = <> |]
    ==> (EX s1 s2. s = s1 ^^^ s2 & s1 [[r]]* t1 & s2 [[r]]* t2
                 & (noTick s1 | s2 = <>))"
by (simp add: ren_tr_appt_decompo_right_only_if_lm)

(* iff *)

lemma ren_tr_appt_decompo_right:
  "noTick t1 | t2 = <>
    ==> s [[r]]* (t1 ^^^ t2)
      = (EX s1 s2. s = s1 ^^^ s2 & s1 [[r]]* t1 & s2 [[r]]* t2
                 & (noTick s1 | s2 = <>))"
apply (rule iffI)
apply (simp add: ren_tr_appt_decompo_right_only_if)
apply (elim conjE exE)
by (auto simp add: ren_tr_appt)

lemmas ren_tr_appt_decompo
     = ren_tr_appt_decompo_left ren_tr_appt_decompo_right

(*--------------------*
 |   <Ev a> ^^^ ...   |
 *--------------------*)

lemma ren_tr_head_decompo[simp]: 
  "(<Ev a> ^^^ s) [[r]]* (<Ev b> ^^^ t) = ((a, b) : r & s [[r]]* t)"
apply (insert ren_tr_appt_decompo_right[of  "<Ev b>" t "<Ev a> ^^^ s" r])
apply (rule iffI)

apply (simp add: ren_tr_one_decompo)
apply (elim conjE exE, simp)
by (simp add: ren_tr_appt_Ev)

(*--------------------*
 |    ... ^^^ [e]t     |
 *--------------------*)

lemma ren_tr_last_decompo_Ev[simp]: 
  "[| noTick s ; noTick t |]
    ==> (s ^^^ <Ev a>) [[r]]* (t ^^^ <Ev b>) = (s [[r]]* t & (a,b) : r)"
apply (insert ren_tr_appt_decompo_right[of t "<Ev b>" "(s ^^^ <Ev a>)" r])
 apply (rule iffI)

  (* => *)
  apply (simp add: ren_tr_one_decompo)
  apply (elim conjE exE)
  apply (simp)

  (* <= *)
  apply (simp)
  apply (rule_tac x="s" in exI)
  apply (rule_tac x="<Ev a>" in exI)
  apply (simp)
done

lemma ren_tr_last_decompo_Tick[simp]: 
  "[| noTick s ; noTick t |]
    ==> (s ^^^ <Tick>) [[r]]* (t ^^^ <Tick>) = (s [[r]]* t)"
apply (insert ren_tr_appt_decompo_right[of t "<Tick>" "(s ^^^ <Tick>)" r])
by (auto simp add: ren_tr_noTick_right)

(*************************************************************
                 ren_tr lengtht
 *************************************************************)

(*** ren same length ***)

lemma ren_tr_lengtht:
  "ALL r s t. s [[r]]* t --> lengtht s = lengtht t"
apply (rule allI)
apply (rule allI)
apply (induct_tac s rule: induct_trace)

 apply (simp_all)
 apply (intro allI impI)
 apply (erule ren_tr_elims)
 apply (simp_all)
done

(*************************************************************
                    ren_tr prefix
 *************************************************************)

lemma ren_tr_prefix_lm:
  "ALL r u v s. prefix v u & s [[r]]* u
     --> (EX t. prefix t s & t [[r]]* v)"
apply (rule allI)
apply (rule allI)
apply (induct_tac u rule: induct_trace)
apply (simp_all)

(* <Ev a> ^^^ ... *)
apply (intro allI impI)
apply (elim conjE)
apply (erule disjE, simp)

apply (simp add: ren_tr_decompo)
apply (elim conjE exE, simp)

apply (drule_tac x="v'" in spec)
apply (drule_tac x="sb" in spec, simp)
apply (elim conjE exE)

apply (rule_tac x="<Ev aa> ^^^ t" in exI, simp)
done

(*** rule ***)

lemma ren_tr_prefix:
  "[| prefix v u ; s [[r]]* u |] ==> (EX t. prefix t s & t [[r]]* v)"
apply (insert ren_tr_prefix_lm)
apply (drule_tac x="r" in spec)
apply (drule_tac x="u" in spec)
apply (drule_tac x="v" in spec)
apply (drule_tac x="s" in spec)
by (simp)

(*** erule ***)

lemma ren_tr_prefixE:
  "[| prefix v u ; s [[r]]* u ;
      !! t. [| prefix t s ; t [[r]]* v |] ==> R 
   |] ==> R"
apply (insert ren_tr_prefix[of v u s r])
by (auto)

(*************************************************************
                    inj --> unique
 *************************************************************)

lemma ren_tr_inj_unique_ALL:
  "ALL s1 s2. (inj f &
          s1 [[{b. EX a. b = (a, f a)}]]* t &
          s2 [[{b. EX a. b = (a, f a)}]]* t )
       --> s1 = s2"
apply (induct_tac t rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (elim conjE)
apply (simp add: ren_tr_decompo_right)
apply (elim conjE exE)
apply (simp)
apply (drule_tac x="sa" in spec)
apply (drule_tac x="sb" in spec)
apply (simp)
apply (simp add: inj_on_def)
done

lemma ren_tr_inj_unique:
  "[| inj f ;
          s1 [[{b. EX a. b = (a, f a)}]]* t ;
          s2 [[{b. EX a. b = (a, f a)}]]* t |]
   ==> s1 = s2"
apply (insert ren_tr_inj_unique_ALL[of f t])
apply (simp)
done

(*************************************************************
                       inverse R
 *************************************************************)

lemma ren_inv_sub_Evset[simp]: "[[r]]inv Evset <= Evset"
by (auto simp add: ren_inv_def Evset_def)

lemma ren_inv_sub:
  "X <= Y ==> [[r]]inv X <= [[r]]inv Y"
by (auto simp add: ren_inv_def)

lemma ren_inv_Un[simp]:
  "[[r]]inv(X Un Y) = [[r]]inv X Un [[r]]inv Y"
by (auto simp add: ren_inv_def)

(*** [[r]]inv preserves "no Tick" ***)

lemma ren_inv_no_Tick[simp]: "([[r]]inv X <= Evset) = (X <= Evset)"
by (auto simp add: ren_inv_def Evset_def)


(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)

(* -------------- *
         ren
 * -------------- *)

(* inverse set *)

lemma ren_inv_Int_Tick[simp]:
  "[[r]]inv(X Int {Tick}) = (X Int {Tick})"
by (auto simp add: ren_inv_def)

lemma ren_inv_diff_Tick[simp]:
  "[[r]]inv(X - {Tick}) = [[r]]inv X - (X Int {Tick})"
by (auto simp add: ren_inv_def)

(* insert *)

lemma ren_inv_insert_Tick:
  "[[r]]inv (insert Tick X) = insert Tick [[r]]inv X"
by (auto simp add: ren_inv_def)

(*  ren_tr -- noTick *)

lemma ren_tr_Tick_left: "[| s [[r]]* t ; ~ noTick s |] ==> ~ noTick t"
apply (rotate_tac -1)
apply (erule contrapos_nn)
apply (simp add: ren_tr_noTick_right)
done

lemma ren_tr_Tick_right: "[| s [[r]]* t ; ~ noTick t |] ==> ~ noTick s"
apply (rotate_tac -1)
apply (erule contrapos_nn)
apply (simp add: ren_tr_noTick_left)
done

(* --- Renaming channel & sett 1 --- *)

(* <==> *)

lemma Renaming1_channel_sett_lm[rule_format]:
  "ALL t s.
   (inj f & inj h & inj g &
   (disjoint_range f g) &
   (disjoint_range f h) &
   (disjoint_range g h) &
    sett t <= insert Tick (Ev ` (range f Un range h)) &
   (s [[f<==>g]]* t))
   --> sett s <= insert Tick (Ev ` (range g Un range h))"
apply (rule)
apply (induct_tac t rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (elim exE conjE)
apply (simp add: image_iff)
apply (elim add_not_eq_symE)
apply (elim disjE conjE exE)
apply (simp_all)
 apply (simp add: ren_tr_decompo_right)
 apply (elim conjE exE)
 apply (simp add: pair_in_Renaming_channel)
 apply (simp add: ren_tr_decompo_right)
 apply (elim conjE exE)
 apply (simp add: pair_in_Renaming_channel)
done

lemma Renaming1_channel_sett1:
  "[| inj f ; inj h ; inj g ;
       disjoint_range f g ;
       disjoint_range f h ;
       disjoint_range g h ;
       sett t <= insert Tick (Ev ` (range f Un range h)) ;
       s [[f<==>g]]* t |]
   ==> sett s <= insert Tick (Ev ` (range g Un range h))"
apply (rule Renaming1_channel_sett_lm)
apply (auto)
done

lemma Renaming1_channel_sett2:
  "[| inj f ; inj h ; inj g ;
       disjoint_range f g ;
       disjoint_range f h ;
       disjoint_range g h ;
       sett t <= insert Tick (Ev ` (range h Un range f)) ;
       s [[f<==>g]]* t |]
   ==> sett s <= insert Tick (Ev ` (range h Un range g))"
apply (simp add: Un_commute)
apply (simp add: Renaming1_channel_sett1)
done

lemma Renaming1_channel_sett3:
  "[| inj f ; inj h ; inj g ;
       disjoint_range f g ;
       disjoint_range f h ;
       disjoint_range g h ;
       sett t <= insert Tick (Ev ` (range f Un range h)) ;
       s [[g<==>f]]* t |]
   ==> sett s <= insert Tick (Ev ` (range g Un range h))"
apply (simp add: Renaming_commut)
apply (simp add: Renaming1_channel_sett1)
done

lemma Renaming1_channel_sett4:
  "[| inj f ; inj h ; inj g ;
       disjoint_range f g ;
       disjoint_range f h ;
       disjoint_range g h ;
       sett t <= insert Tick (Ev ` (range h Un range f)) ;
       s [[g<==>f]]* t |]
   ==> sett s <= insert Tick (Ev ` (range h Un range g))"
apply (simp add: Renaming_commut)
apply (simp add: Renaming1_channel_sett2)
done

lemmas Renaming1_channel_sett =
       Renaming1_channel_sett1
       Renaming1_channel_sett2
       Renaming1_channel_sett3
       Renaming1_channel_sett4

(* <== *)

lemma Renaming2_channel_sett_lm[rule_format]:
  "ALL t s.
   (inj f & inj h & inj g &
   (disjoint_range f g) &
   (disjoint_range f h) &
   (disjoint_range g h) &
    sett s <= insert Tick (Ev ` (range f Un range h)) &
   (s [[f<==g]]* t))
   --> sett t <= insert Tick (Ev ` (range g Un range h))"
apply (rule)
apply (induct_tac t rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (elim exE conjE)
apply (simp add: image_iff)
apply (elim add_not_eq_symE)
apply (elim disjE conjE exE)

apply (simp add: ren_tr_decompo_right)
apply (elim conjE exE)
apply (simp add: image_iff)
apply (elim disjE conjE exE)

 apply (drule mp)
  apply (rule_tac x="sb" in exI)
  apply (simp)
 apply (simp add: pair_in_Renaming_channel)
 apply (fast)

 apply (drule mp)
  apply (rule_tac x="sb" in exI)
  apply (simp)
 apply (simp add: pair_in_Renaming_channel)
 apply (fast)
done

lemma Renaming2_channel_sett:
  "[| inj f ; inj h ; inj g ;
       disjoint_range f g ;
       disjoint_range f h ;
       disjoint_range g h ;
       sett s <= insert Tick (Ev ` (range f Un range h)) ;
       s [[f<==g]]* t |]
   ==> sett t <= insert Tick (Ev ` (range g Un range h))"
apply (rule Renaming2_channel_sett_lm)
apply (auto)
done


lemmas Renaming_channel_sett =
       Renaming1_channel_sett
       Renaming2_channel_sett

(* ------ sym ------ *)


lemma ren_tr_Renaming_channel_sym_rule[rule_format]:
  "[| inj f ; inj g |] ==> ALL s t. (s [[f<==>g]]* t --> t [[f<==>g]]* s)"
apply (rule)
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (case_tac "~ (disjoint_range f g)")
 apply (subgoal_tac "(f<==>g) = <rel> (%c. c)")
 apply (simp)
 apply (simp add: ren_tr_decompo_left)
 apply (elim conjE exE)
 apply (drule_tac x="ta" in spec)
 apply (simp)
 apply (simp add: fun_to_rel_def)
apply (simp (no_asm_simp) add: Renaming_channel_def Renaming_channel_fun_def)

apply (simp add: ren_tr_decompo_left)
apply (elim conjE exE)
apply (drule_tac x="ta" in spec)
apply (simp)
apply (simp add: Renaming_channel_def Renaming_channel_fun_def)
apply (simp add: fun_to_rel_def)
apply (auto)
done

lemma ren_tr_Renaming_channel_sym:
  "[| inj f ; inj g |] ==> (s [[f<==>g]]* t) = (t [[f<==>g]]* s)"
apply (rule)
apply (rule ren_tr_Renaming_channel_sym_rule)
apply (simp_all)
apply (rule ren_tr_Renaming_channel_sym_rule)
apply (simp_all)
done



(* --- Renaming channel & exist --- *)

(* <==> *)

lemma Renaming1_channel_exist_left:
  "[| inj f ; inj g |] ==> ALL s. EX t. s [[f<==>g]]* t"
apply (rule)
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (elim conjE exE)
apply (case_tac "~ (disjoint_range f g)")
 apply (subgoal_tac "(f<==>g) = <rel> (%c. c)")
 apply (rule_tac x="<Ev a> ^^^ x" in exI)
 apply (simp add: fun_to_rel_def)
apply (simp (no_asm_simp) add: Renaming_channel_def Renaming_channel_fun_def)

apply (case_tac "a : range f")
 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp)
 apply (rule_tac x="<Ev (g xa)> ^^^ x" in exI)
 apply (simp add: pair_in_Renaming_channel)

apply (case_tac "a : range g")
 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp)
 apply (rule_tac x="<Ev (f xa)> ^^^ x" in exI)
 apply (elim add_not_eq_symE)
 apply (simp add: pair_in_Renaming_channel)

 apply (simp add: image_iff)
 apply (rule_tac x="<Ev a> ^^^ x" in exI)
 apply (elim add_not_eq_symE)
 apply (simp add: pair_in_Renaming_channel)
done

lemma Renaming1_channel_exist_right:
  "[| inj f ; inj g |] ==> ALL s. EX t. t [[f<==>g]]* s"
apply (simp add: ren_tr_Renaming_channel_sym)
apply (simp add: Renaming1_channel_exist_left)
done


(* --- Renaming channel & exist --- *)

(* <== *)

lemma Renaming2_channel_exist_left:
  "[| inj f ; inj g |] ==> ALL s. EX t. s [[f<==g]]* t"
apply (rule)
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (elim conjE exE)
apply (case_tac "~ (disjoint_range f g)")
 apply (subgoal_tac "(f<==g) = <rel> (%c. c)")
 apply (rule_tac x="<Ev a> ^^^ x" in exI)
 apply (simp add: fun_to_rel_def)
apply (simp (no_asm_simp) add: Renaming_channel_def Renaming_channel_fun_def)

apply (case_tac "a : range f")
 apply (simp add: image_iff)
 apply (elim conjE exE)
 apply (simp)
 apply (rule_tac x="<Ev (g xa)> ^^^ x" in exI)
 apply (simp add: pair_in_Renaming_channel)

 apply (simp add: image_iff)
 apply (rule_tac x="<Ev a> ^^^ x" in exI)
 apply (elim add_not_eq_symE)
 apply (simp add: pair_in_Renaming_channel)
done

(* Renaming exist 1 and 2 *)

lemmas Renaming_channel_exist_left =
       Renaming1_channel_exist_left
       Renaming2_channel_exist_left

lemmas Renaming_channel_exist_right =
       Renaming1_channel_exist_right

(* ------------- ren_inv -------------- *)

lemma Renaming_channel_ren_inv_Int_Tick_eq:
  "[[f<==>g]]inv X Int {Tick} = X Int {Tick}"
apply (case_tac "~ (disjoint_range f g)")
apply (subgoal_tac "f<==>g = <rel> (%c. c)")
 apply (simp)
 apply (simp add: ren_inv_def)
 apply (simp add: fun_to_rel_def)
 apply (force)
apply (simp (no_asm_simp) add: Renaming_channel_def Renaming_channel_fun_def)

apply (simp add: ren_inv_def)
apply (simp add: fun_to_rel_def Renaming_channel_def Renaming_channel_fun_def)
apply (elim add_not_eq_symE)
apply (rule equalityI)
apply (force)
apply (rule)
apply (simp add: image_iff)
apply (elim conjE exE)
apply (rule_tac x="Tick" in bexI)
apply (simp)
apply (simp)
done

lemma Renaming_channel_ren_inv_Int_eq:
  "[| disjoint_range f h ;
      disjoint_range g h |] ==>
     [[f<==>g]]inv X Int Ev ` range h = X Int Ev ` range h"
apply (case_tac "~ (disjoint_range f g)")
apply (subgoal_tac "f<==>g = <rel> (%c. c)")
 apply (simp)
 apply (simp add: ren_inv_def)
 apply (simp add: fun_to_rel_def)
 apply (force)
apply (simp (no_asm_simp) add: Renaming_channel_def Renaming_channel_fun_def)

apply (simp add: ren_inv_def)
apply (simp add: fun_to_rel_def Renaming_channel_def Renaming_channel_fun_def)
apply (elim add_not_eq_symE)
apply (rule equalityI)
apply (force)
apply (rule)
apply (simp add: image_iff)
apply (elim conjE exE)
apply (rule_tac x="Ev (h xa)" in bexI)
apply (simp)
apply (rule_tac x="h xa" in exI)
apply (simp)
apply (simp)
done

(* --- 2 ren_inv --- *)

lemma Renaming_channel_ren_inv_ren_inv_eq:
  "[| inj f; inj g |] ==> [[f<==>g]]inv [[f<==>g]]inv X = X"
apply (case_tac "~ (disjoint_range f g)")
apply (subgoal_tac "f<==>g = <rel> (%c. c)")
 apply (simp add: ren_inv_def)
 apply (simp add: fun_to_rel_def)
 apply (rule equalityI)
  apply (rule)
  apply (simp add: image_iff)
  apply (elim disjE conjE exE bexE)
  apply (simp)+
  apply (rule)
  apply (simp add: image_iff)
  apply (elim disjE conjE exE bexE)
  apply (rule_tac x="x" in exI)
  apply (simp)
  apply (insert event_Tick_or_Ev)
  apply (drule_tac x="x" in spec)
  apply (elim disjE conjE exE bexE)
  apply (force)
  apply (force)
 apply (simp (no_asm_simp) add: Renaming_channel_def Renaming_channel_fun_def)

(* (disjoint_range f g) *)
 (* <= *)
 apply (simp add: ren_inv_def)
 apply (rule equalityI)
  apply (rule)
  apply (simp add: image_iff)
  apply (elim disjE conjE exE bexE)
  apply (simp)+
  apply (insert Renaming_channel_unique[of f g])
apply (rotate_tac -1)
apply (erule rem_asmE)

  apply (drule_tac x="b" in spec)
  apply (drule_tac x="a" in spec)
  apply (drule_tac x="ba" in spec)
  apply (simp)
  apply (drule mp)
   apply (rule Renaming_channel_sym_rule)
   apply (simp)+

 (* => *)
 apply (rotate_tac -1)
 apply (erule rem_asmE)
 apply (rotate_tac -1)
 apply (erule rem_asmE)

 apply (rule)
 apply (simp)
 apply (drule_tac x="x" in spec)
 apply (elim disjE conjE exE)
 apply (simp)
 apply (simp)

 apply (case_tac "EX x. a = f x")
  apply (elim conjE exE)
  apply (simp)
  apply (rule_tac x="Ev (g xa)" in exI)
  apply (simp)
  apply (rule conjI)
   apply (rule_tac x="Ev (f xa)" in bexI)
   apply (simp add: pair_in_Renaming_channel)
   apply (rule Renaming_channel_sym_rule)
   apply (simp)
   apply (simp)
   apply (simp add: pair_in_Renaming_channel)
   apply (simp)
   apply (simp add: pair_in_Renaming_channel)

 apply (case_tac "EX x. a = g x")
  apply (elim conjE exE)
  apply (simp)
  apply (rule_tac x="Ev (f xa)" in exI)
  apply (simp add: pair_in_Renaming_channel)
  apply (rule Renaming_channel_sym_rule)
  apply (simp_all)
  apply (simp add: pair_in_Renaming_channel)

 apply (case_tac "(ALL x. a ~= f x) & (ALL x. a ~= g x)")
  apply (elim conjE exE)
  apply (simp)
  apply (rule_tac x="Ev a" in exI)
  apply (simp)
  apply (rule conjI)
   apply (rule_tac x="Ev a" in bexI)
   apply (rule_tac x="a" in exI)
   apply (simp add: pair_in_Renaming_channel)
   apply (simp)
   apply (simp add: pair_in_Renaming_channel)

apply (auto)
done

(* ----------------------------------- *)

(* ----------------- commut ------------------- *)

lemma Renaming_channel_ren_tr_commut:
   "ALL f1 f2 g1 g2 s1 s2 t1 t2 t2'.
   (inj f1 & inj f2 & inj g1 & inj g2 & 
   (ALL x y. f1 x ~= f2 y) &
   (ALL x y. f1 x ~= g1 y) &
   (ALL x y. f1 x ~= g2 y) &
   (ALL x y. f2 x ~= g1 y) &
   (ALL x y. f2 x ~= g2 y) &
   (ALL x y. g1 x ~= g2 y) &
    s1 [[f1<==>f2]]* s2 &
    s2 [[g1<==>g2]]* t2 &
    s1 [[g1<==>g2]]* t1 &
    t1 [[f1<==>f2]]* t2')
   --> t2 = t2'"
apply (rule)
apply (rule)
apply (rule)
apply (rule)
apply (rule)
apply (induct_tac s1 rule: induct_trace)

(* <> *)
 apply (intro allI impI)
 apply (elim conjE exE)
 apply (simp)

(* <Tick> *)
 apply (intro allI impI)
 apply (elim conjE exE)
 apply (simp)

(* ... *)
 apply (intro allI impI)
 apply (elim conjE exE)
 apply (simp (no_asm_use) add: ren_tr_decompo_left)
 apply (elim conjE exE)
 apply (drule_tac x="t" in spec)
 apply (drule_tac x="ta" in spec)
 apply (simp)
 apply (simp add: ren_tr_decompo_left)
 apply (elim conjE exE)
 apply (simp)
 apply (insert Renaming_channel_independ)
  apply (drule_tac x="f1" in spec)
  apply (drule_tac x="f2" in spec)
  apply (drule_tac x="g1" in spec)
  apply (drule_tac x="g2" in spec)
  apply (drule_tac x="a" in spec)
  apply (drule_tac x="b" in spec)
  apply (drule_tac x="ba" in spec)
  apply (drule_tac x="bb" in spec)
  apply (drule_tac x="bc" in spec)
 apply (simp)
done

lemma Renaming_channel_ren_tr_commut_rule:
   "EX f1 f2 g1 g2 s1 s2 t1.
   (inj f1 & inj f2 & inj g1 & inj g2 & 
   (ALL x y. f1 x ~= f2 y) &
   (ALL x y. f1 x ~= g1 y) &
   (ALL x y. f1 x ~= g2 y) &
   (ALL x y. f2 x ~= g1 y) &
   (ALL x y. f2 x ~= g2 y) &
   (ALL x y. g1 x ~= g2 y) &
    s1 [[f1<==>f2]]* s2 &
    s2 [[g1<==>g2]]* t2 &
    s1 [[g1<==>g2]]* t1 &
    t1 [[f1<==>f2]]* t2')
   ==> t2 = t2'"
apply (elim conjE exE)
apply (insert Renaming_channel_ren_tr_commut)
 apply (drule_tac x="f1" in spec)
 apply (drule_tac x="f2" in spec)
 apply (drule_tac x="g1" in spec)
 apply (drule_tac x="g2" in spec)
 apply (drule_tac x="s1" in spec)
 apply (drule_tac x="s2" in spec)
 apply (drule_tac x="t1" in spec)
 apply (drule_tac x="t2" in spec)
 apply (drule_tac x="t2'" in spec)
apply (simp)
done

(* not used ? *)

lemma Renaming1_channel_id[rule_format]:
  "(inj f & inj g & (disjoint_range f g) &
    sett s Int Ev ` range f = {} &
    sett s Int Ev ` range g = {}) 
    --> s [[f<==>g]]* s"
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (elim conjE disjE)
apply (simp)
 apply (elim add_not_eq_symE)
 apply (subgoal_tac "(ALL x. a ~= f x) & (ALL x. a ~= g x)")
 apply (simp add: pair_in_Renaming_channel)
apply (simp add: image_iff)
done

lemma Renaming2_channel_id[rule_format]:
  "(inj f & inj g & (disjoint_range f g) &
    sett s Int Ev ` range f = {})
    --> s [[f<==g]]* s"
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (elim conjE disjE)
apply (simp)
 apply (elim add_not_eq_symE)
 apply (subgoal_tac "(ALL x. a ~= f x)")
 apply (simp add: pair_in_Renaming_channel)
apply (simp add: image_iff)
done

lemmas Renaming_channel_id =
       Renaming1_channel_id
       Renaming2_channel_id

(* Un *)

lemma Renaming_channel_id_Un[rule_format]:
  "(inj f & inj g & (disjoint_range f g) &
    sett s Int Ev ` (range f Un range g) = {})
     --> s [[f<==>g]]* s"
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (intro allI impI)
apply (elim conjE disjE)
apply (simp)
 apply (elim add_not_eq_symE)
 apply (subgoal_tac "(ALL x. a ~= f x) & (ALL x. a ~= g x)")
 apply (simp add: pair_in_Renaming_channel)
apply (force)
done

(****************** to add it again ******************)

declare disj_not1 [simp] 

end
