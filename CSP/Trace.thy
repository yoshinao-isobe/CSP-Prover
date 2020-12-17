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
            |        CSP-Prover on Isabelle2013         |
            |                   June 2013  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Trace
imports Infra
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite (notick | t = <>)                  *)
(*                                                                     *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(***********************************************************

    Type Definitions
      'a event      : type of events      a,b,...
      'a trace      : type of traces      s,t,...

 ***********************************************************)

datatype 'a event = Ev 'a | Tick

definition
  Evset     :: "'a event set"
  where
  "Evset     == {a. a ~= Tick}"

definition  
  EvsetTick :: "'a event set"
  where
  "EvsetTick == UNIV"

(* EvsetTick seems to be useless, but it sometimes *)
(* makes proofs to be readable.                    *)

(*------------------------------------*
 |              X-Symbols             |
 *------------------------------------*)
(*
notation (xsymbols) Tick ("\<surd>")
*)

(*******************************
    Evset contains all (Ev a)
 *******************************)

lemma Un_Evset[simp] : "Ev ` X Un Evset = Evset"
by (auto simp add: Evset_def)

(*******************************
         Tick or Ev a
 *******************************)

lemma event_Tick_or_Ev: "ALL e. e = Tick | (EX a. e = Ev a)"
apply (intro allI)
by (induct_tac e, auto)

lemma not_Tick_to_Ev: "(e ~= Tick) = (EX a. e = Ev a)"
apply (auto)
apply (insert event_Tick_or_Ev)
apply (drule_tac x="e" in spec)
by (simp)

lemma in_Ev_set : "(e : Ev ` X) = (EX a. (e = Ev a & a : X))"
by (auto)

lemma notin_Ev_set : "(e ~: Ev ` X) = (e = Tick | (EX a. (e = Ev a & a ~: X)))"
apply (insert event_Tick_or_Ev)
apply (drule_tac x="e" in spec)
by (auto)

(*******************************
             inj
 *******************************)

lemma inj_Ev[simp]: "inj Ev"
apply (simp add: inj_on_def)
done

(***********************************************************
                    Definition of traces
 ***********************************************************)

(* "typedef" requires defined types are not empty as follows: *)

definition "trace  = {ss::('a event list). Tick ~: set (butlast ss)}"

typedef 'a trace = "trace :: 'a event list set"
(* typedef 'a trace = "{ss::('a event list). Tick ~: set (butlast ss)}"  *)
apply (rule_tac x ="[]" in exI)
apply (simp add: trace_def)
done

declare Rep_trace         [simp]

(*****************************************************************
            directly convert from list to trace
 *****************************************************************)

(***********************************************************)
(*                  operators over traces                  *)
(*                                                         *)
(*    memo    (infixr "@t" 65) = ("_ @t _" [66,65] 65)     *)
(*                                                         *)
(***********************************************************)

definition
  nilt    :: "'a trace"                                ("<>")
  where "<>       == Abs_trace []"
  
definition  
  sett    :: "'a trace => 'a event set"
  where  "sett s    == set (Rep_trace s)"

definition  
  lengtht :: "'a trace => nat"
  where
  "lengtht s == length (Rep_trace s)"
  
definition
  noTick  :: "'a trace => bool"
  where
  "noTick s  == (Tick ~: sett s)"

definition  
  hdt      :: "'a trace => 'a event"
  where
  hdt_def      : "hdt s      == hd (Rep_trace s)"
  
definition    
  tlt      :: "'a trace => 'a trace"
  where
  tlt_def      : "tlt s      == Abs_trace (tl (Rep_trace s))"
  
definition    
  lastt    :: "'a trace => 'a event"
  where
  lastt_def    : "lastt s    == last (Rep_trace s)"
  
definition    
  butlastt :: "'a trace => 'a trace"
  where
  butlastt_def : "butlastt s == Abs_trace (butlast (Rep_trace s))"

syntax
  "@trace"   :: "args => 'a trace"                       ("<_>" [900] 1000)

translations
  "<s>"      == "CONST Abs_trace [s]"   (* "CONST" for isabelle2009-2 *)

(*** appending ***)

datatype TraceChk = tr_nil | tr_noTick | tr_Tick | tr_error

definition
  appt    :: "'a trace => 'a trace => 'a trace"      (infixr "^^^" 65)
  where
  appt_def    : "s ^^^ t    == Abs_trace (Rep_trace s @ Rep_trace t)"

(******** X-symbols ********)
(*
notation (xsymbols) nilt ("\<langle>\<rangle>")
notation (xsymbols) appt (infixr "\<frown>" 65)

syntax (output)
  "_traceX"     :: "args => 'a trace"                       ("<(_)>")

syntax (xsymbols)
  "_traceX"     :: "args => 'a trace"       ("\<langle>(_)\<rangle>" [900] 1000)

translations
  "\<langle>s\<rangle>"  == "<s>"
*)

(***********************************************************
                          lemmas
 ***********************************************************)

(***************************************
         trace Rep and Abs lemmas
 ***************************************)

(*** Abs-Rep ***)

lemma Abs_trace_Rep_trace_inverse_left: 
  "t : trace ==> ((Abs_trace t = s) = (t = Rep_trace s))"
by (auto simp add: Abs_trace_inverse Rep_trace_inverse)

lemma Abs_trace_Rep_trace_inverse_right: 
  "t : trace ==> ((s = Abs_trace t) = (t = Rep_trace s))"
by (auto simp add: Abs_trace_inverse Rep_trace_inverse)

lemmas Abs_trace_Rep_trace_inverse =
       Abs_trace_Rep_trace_inverse_left Abs_trace_Rep_trace_inverse_right

(*** Rep-Abs ***)

lemma Rep_trace_Abs_trace_inverse_left_only_if: 
  "Rep_trace t = s ==> t = Abs_trace s"
by (auto simp add: Rep_trace_inverse)

lemma Rep_trace_Abs_trace_inverse_right_only_if: 
  "s = Rep_trace t ==> t = Abs_trace s"
by (auto simp add: Rep_trace_inverse)

lemmas Rep_trace_Abs_trace_inverse_only_if =
           Rep_trace_Abs_trace_inverse_left_only_if
           Rep_trace_Abs_trace_inverse_right_only_if

(*** Abs image ***)

lemma Abs_trace_inverse_in_only_if: 
  "[| ALL s:X. s : trace ; t : Abs_trace ` X |] ==> Rep_trace t : X"
apply (simp add: image_def, erule bexE)
apply (drule_tac x="x" in bspec, simp)
by (simp add: Abs_trace_inverse)

lemma Abs_trace_inverse_in_if: 
  "Rep_trace t : X ==> t : Abs_trace ` X"
apply (simp add: image_def)
apply (rule_tac x="Rep_trace t" in bexI)
by (simp_all add: Rep_trace_inverse)

lemma Abs_trace_inverse_in:
  "[| ALL s:X. s : trace |]
       ==> (t : Abs_trace ` X) = (Rep_trace t : X)"
apply (rule iffI)
apply (simp add: Abs_trace_inverse_in_only_if)
by (simp add: Abs_trace_inverse_in_if)

(*******************************
         check in trace
 *******************************)

lemma nil_in_trace[simp] : "[] : trace"
by (simp add: trace_def)

lemma event_in_trace[simp] : "[a] : trace"
by (simp add: trace_def)

lemma notic_in_trace[simp] : "Tick ~: set s ==> s : trace"
by (simp add: trace_def notin_set_butlast)

(*--------------------------*
 |        decompo app       |
 *--------------------------*)

(*** decompo traces only if ***)

lemma decompo_app_in_trace_only_if1 : "s @ t : trace ==> s : trace"
apply (simp add: trace_def)
apply (simp add: notin_butlast_decompo)
apply (erule disjE)
by (simp_all add: notin_set_butlast)

lemma decompo_app_in_trace_only_if2 : "s @ t : trace ==> t : trace"
apply (simp add: trace_def)
apply (simp add: notin_butlast_decompo)
by (auto)

lemma decompo_app_in_trace_only_if : 
  "s @ t : trace ==> (s : trace & t = []) | (Tick ~: set s & t : trace)"
apply (insert list_last_nil_or_unnil)
apply (drule_tac x="t" in spec)
apply (erule disjE)

 (* t = [] *)
 apply (simp)

 (* t = sa @ [a] *)
 apply (elim exE)
 apply (rule disjI2)
 apply (rule conjI)

 apply (simp add: trace_def)
 apply (simp add: notin_butlast_decompo)

 apply (rule decompo_app_in_trace_only_if2[of s])
 apply (simp)
done

(*** decompo traces if ***)

lemma decompo_app_in_trace_if : 
  "[| Tick ~: set s ; t : trace |] ==> s @ t : trace"
by (simp add: trace_def notin_butlast_decompo)

(****** decompo traces iff ******)

lemma decompo_app_in_trace : 
  "s @ t : trace = ((s : trace & t = []) | (Tick ~: set s & t : trace))"
apply (rule iffI)
apply (simp add: decompo_app_in_trace_only_if)
apply (erule disjE)
by (simp_all add: decompo_app_in_trace_if)

(*** erule for decomposing "s @ t : trace" in assumption ***)

lemma decompo_appt_in_traceE:
  "[| s @ t : trace ; [| s @ t : trace ; s : trace ; t : trace |] ==> R |]
    ==> R"
apply (simp add: decompo_app_in_trace)
by (auto)

(*--------------------------*
 |       decompo cons       |
 *--------------------------*)

(*** decompo traces if ***)

lemma decompo_head_in_trace_if:
  "[| a ~= Tick ; t : trace |] ==> a # t : trace"
apply (insert decompo_app_in_trace_if[of "[a]" t])
by (auto)

lemma decompo_head_in_trace : 
  "a # t : trace =  (t = [] | (a ~= Tick & t : trace))"
apply (insert decompo_app_in_trace[of "[a]"])
by (auto)

lemma decompo_last_in_trace_if : 
  "Tick ~: set s ==> s @ [a] : trace"
apply (insert decompo_app_in_trace_if[of s "[a]"])
by (auto)

lemma decompo_last_in_trace : 
  "s @ [a] : trace = (Tick ~: set s)"
apply (insert decompo_app_in_trace[of s "[a]"])
by (simp)

(*--------------------------*
 |        app not in        |
 *--------------------------*)

lemma app_notin_trace_left:
   "s ~: trace ==> t @ s ~: trace"
apply (auto simp add: trace_def)
apply (simp add: in_butlast_decompo)
apply (case_tac "s = []")
by (simp_all)

lemma app_notin_trace_right:
   "s ~: trace ==> s @ t ~: trace"
apply (auto simp add: trace_def)
apply (simp add: in_butlast_decompo)
apply (rule disjI1)
by (rule in_set_butlast, simp)

lemmas app_notin_trace = 
       app_notin_trace_left app_notin_trace_right

(*******************************
            Tick
 *******************************)

lemma Tick_is_last : "Tick#s : trace ==> s = []"
apply (case_tac "s = []")
by (auto simp add: trace_def)

(*******************************
             Nil
 *******************************)

lemma one_neq_nil[simp]: "<a> ~= <>"
by (simp add: nilt_def Abs_trace_inject)

lemma one_neq_nil_sym[simp]: "<> ~= <a>"
by (simp add: nilt_def Abs_trace_inject)

(*******************************
           noTick
 *******************************)

(*** noTick Ev ***)

lemma noTick_Ev[simp]: "noTick (<Ev a>)"
apply (simp add: noTick_def sett_def)
by (simp add: Abs_trace_inverse)

lemma noTick_EvI: "(EX a. e = Ev a) ==> noTick (<e>)"
apply (simp add: noTick_def sett_def)
by (auto simp add: Abs_trace_inverse)

(*** noTick nil ***)

lemma noTick_nil[simp]: "noTick <>"
apply (simp add: noTick_def nilt_def sett_def)
by (simp add: Abs_trace_inverse) 

(*** not noTick Tick ***)

lemma not_noTick_Tick[simp]: "~ noTick <Tick>"
apply (simp add: noTick_def sett_def)
by (simp add: Abs_trace_inverse)

(*******************************
            Event
 *******************************)

lemma Event_eq[simp] : "(<e1> = <e2>) = (e1 = e2)"
by (simp add: Abs_trace_inject)

(***********************************************************
                   @ in trace
 ***********************************************************)

(*---------------------------------------------*
 |         Rep_trace s @ Rep_trace t           |
 *---------------------------------------------*)

(*--------------------------*
 |       rep in_trace       |
 *--------------------------*)

lemma Rep_compo_head_in_trace[simp]: 
  "(Ev a) # Rep_trace t : trace"
by (simp add: decompo_head_in_trace)

lemma Rep_compo_last_in_trace[simp]: 
  "noTick t ==> Rep_trace t @ [e] : trace"
apply (simp add: decompo_last_in_trace)
apply (simp add: noTick_def sett_def)
done

lemma Rep_compo_app_in_trace[simp] : 
  "(noTick s | t = <>) ==> Rep_trace s @ Rep_trace t : trace"
apply (simp add: decompo_app_in_trace)
apply (simp add: noTick_def sett_def nilt_def)
apply (simp add: Abs_trace_Rep_trace_inverse)
by (auto)

(*** only if ***)

lemma decompo_apprep_in_traceI:
  "Rep_trace s @ Rep_trace t : trace ==> (noTick s | t = <>)"
apply (simp add: decompo_app_in_trace)
apply (simp add: nilt_def noTick_def sett_def)
by (auto simp add: Rep_trace_Abs_trace_inverse_only_if)

(*** iff ***)

lemma decompo_apprep_in_trace:
  "(Rep_trace s @ Rep_trace t : trace) = (noTick s | t = <>)"
apply (rule iffI)
apply (rule decompo_apprep_in_traceI, simp)
apply (simp)
done

(*** not ***)

lemma decompo_apprep_notin_traceI:
  "Rep_trace s @ Rep_trace t ~: trace ==> (~ noTick s & t ~= <>)"
by (erule contrapos_np, simp)

(*** erule ***)

lemma decompo_apprep_in_traceE:
  "[| Rep_trace s @ Rep_trace t : trace ; 
      noTick s | t = <> ==> R |] ==> R"
apply (simp add: decompo_apprep_in_trace)
done

lemma decompo_apprep_notin_traceE:
  "[| Rep_trace s @ Rep_trace t ~: trace ;
      [| ~ noTick s ; t ~= <> |] ==> R |] ==> R"
apply (simp add: decompo_apprep_in_trace)
done

(*-----------------------------*
 |     lemmas for in_traces    |
 *-----------------------------*)

lemmas in_trace = decompo_head_in_trace decompo_app_in_trace
lemmas Rep_in_trace = decompo_apprep_in_trace

(***********************************************************
                  lemmas for s @t t 
 ***********************************************************)

(*-----------------------------*
 | Abs_trace distribution on @ |
 *-----------------------------*)

lemma Abs_trace_app_dist:
  "s @ t : trace ==> Abs_trace s ^^^ Abs_trace t = Abs_trace (s @ t)"
apply (simp add: appt_def)
apply (erule decompo_appt_in_traceE)
apply (simp add: Abs_trace_inverse)
done

(***********************************************************
                    s ^^^ t <==> s @rep t
 ***********************************************************)

(*--------------------------*
 |       append head        |
 *--------------------------*)

lemma appt_head:
  "<a> ^^^ s = Abs_trace (a # Rep_trace s)"
apply (simp add: appt_def)
by (simp add: Abs_trace_inverse)

(*--------------------------*
 |       append last        |
 *--------------------------*)

lemma appt_last:
  "noTick t ==> t ^^^ <e> = Abs_trace (Rep_trace t @ [e])"
apply (simp add: appt_def)
by (simp add: Abs_trace_inverse)

(***********************************************************
                  lemmas for s ^^^ t 
 ***********************************************************)

lemma appt_nil_left[simp]: "<> ^^^ s = s"
apply (simp add: appt_def)
apply (simp add: nilt_def)
by (simp add: Abs_trace_inverse Rep_trace_inverse)

lemma appt_nil_right[simp]: "s ^^^ <> = s"
apply (simp add: appt_def)
apply (simp add: nilt_def)
by (simp add: Abs_trace_inverse Rep_trace_inverse)

lemma event_app_not_nil_left[simp]: "<Ev a> ^^^ s ~= <>"
apply (simp add: appt_def)
apply (simp add: Abs_trace_inverse nilt_def)
apply (subgoal_tac "Ev a # Rep_trace s : trace")
apply (simp add: Abs_trace_inject)
apply (simp add: in_trace)
done

lemma event_app_not_nil_right[simp]: "noTick s ==> s ^^^ <e> ~= <>"
apply (simp add: appt_def)
apply (simp add: Abs_trace_inverse nilt_def)
apply (subgoal_tac "Rep_trace s @ [e] : trace")
apply (simp add: Abs_trace_inject)
apply (simp add: in_trace)
apply (simp add: noTick_def sett_def)
done

(***********************************************************
                 induction for traces
 ***********************************************************)

(*** induction ***)

lemma induct_event_list:
  "s : trace &
   P <> & P <Tick> &
   (ALL s a. (P (Abs_trace s) --> P (<Ev a> ^^^ (Abs_trace s))))
    --> P (Abs_trace s)"
apply (induct_tac s)

(* base case *)
apply (simp add: nilt_def)

(* step case *)
apply (intro impI)
apply (simp add: in_trace)

apply (insert event_Tick_or_Ev)
apply (drule_tac x="a" in spec)
apply (elim disjE conjE exE)
apply (simp_all)

apply (drule_tac x="[]" in spec)
apply (fold nilt_def, simp)
apply (simp add: appt_head)
apply (drule_tac x="list" in spec)
apply (simp add: Abs_trace_inverse)
done

(*** rule ***)

lemma induct_trace:
  "[| P <> ; P <Tick> ; 
      !! (s::'a trace) a. P s ==> P (<Ev a> ^^^ s) |]
    ==> P (s)"
apply (insert induct_event_list[of "Rep_trace s" P])
by (simp add: Rep_trace_inverse)

(*------------------------------------------------------*
 |  use this induction rule "induct_trace" as follows:  |
 |                                                      |
 |      lemma test_induction: "test (s::'a trace)"      |
 |      apply (induct_tac s rule: induct_trace)         |
 |                                                      |
 *------------------------------------------------------*)

(*** reverse induction ***)

lemma rev_induct_event_list:
  "s : trace &
   P <> & 
   (ALL s e. (P (Abs_trace s) & noTick (Abs_trace s))
    --> P ((Abs_trace s) ^^^ <e>))
    --> P (Abs_trace s)"
apply (induct_tac s rule: rev_induct)

(* base case *)
apply (simp add: nilt_def)

(* step case *)
apply (intro allI impI)
apply (simp add: in_trace)
apply (elim conjE)
apply (drule_tac x="xs" in spec)
apply (simp add: noTick_def sett_def)
apply (simp add: Abs_trace_inverse)
apply (subgoal_tac "noTick (Abs_trace xs)")
apply (simp add: appt_last Abs_trace_inverse)
apply (simp add: noTick_def sett_def)
apply (simp add: Abs_trace_inverse)
done

(*** rule ***)

lemma rev_induct_trace:
  "[| P <> ; 
      !! (s::'a trace) e. [| P s ; noTick s |] ==> P (s ^^^ <e>) |]
    ==> P (s)"
apply (insert rev_induct_event_list[of "Rep_trace s" P])
by (simp add: Rep_trace_inverse)

(*----------------------------------------------------------*
 |  use this induction rule "rev_induct_trace" as follows:  |
 |                                                          |
 |      lemma test_induction: "test (s::'a trace)"          |
 |      apply (induct_tac s rule: rev_induct_trace)         |
 |                                                          |
 *----------------------------------------------------------*)

(***********************************************************
                   convenient lemmas
 ***********************************************************)

(*--------------------------*
 |   associativity of ^^^    |
 *--------------------------*)

lemma appt_assoc: 
  "[| (noTick s | t = <>) ; (noTick t | u = <>) |]
   ==> (s ^^^ t) ^^^ u = s ^^^ (t ^^^ u)"
apply (subgoal_tac "Rep_trace s @ Rep_trace t : trace")
apply (subgoal_tac "Rep_trace t @ Rep_trace u : trace")
apply (simp add: appt_def)
apply (simp add: Abs_trace_inverse)

apply (simp_all add: Rep_in_trace)
done

lemma appt_assoc_sym : 
  "[| (noTick s | t = <>) ; (noTick t | u = <>) |]
   ==> s ^^^ (t ^^^ u) = (s ^^^ t) ^^^ u"
by (simp add: appt_assoc)

(*** nil ***)

lemma appt_nil[simp]: "noTick s ==> (s ^^^ t = <>) = (s = <> & t = <>)"
apply (rule iffI)
apply (simp_all)

apply (simp add: appt_def)
apply (case_tac "(Rep_trace s @ Rep_trace t) : trace")
 apply (simp add: nilt_def)
 apply (simp add: Abs_trace_inject)
 apply (simp add: Rep_trace_Abs_trace_inverse_only_if)
 apply (simp add: Rep_in_trace)
done

lemma appt_nil_sym[simp]: "noTick s ==> (<> = s ^^^ t) = (s = <> & t = <>)"
apply (auto)
by (drule sym, simp)+

(*--------------------------*
 |         length           |
 *--------------------------*)

(*** 0 ***)
lemma lengtht_nil_zero[simp]: "lengtht (<>) = 0"
apply (simp add: nilt_def lengtht_def)
by (simp add: Abs_trace_inverse)

(*** 1 ***)
lemma lengtht_one_event[simp]: "lengtht (<e>) = Suc 0"
apply (simp add: lengtht_def)
by (simp add: Abs_trace_inverse)

(*** length + 1 ***)

lemma lengtht_app_event_Suc_last[simp]:
  "noTick s ==> lengtht (s ^^^ <a>) = Suc (lengtht s)"
apply (simp add: appt_def lengtht_def)
apply (simp add: Abs_trace_inverse)
done

lemma lengtht_app_event_Suc_head[simp]:
  "lengtht (<Ev a> ^^^ s) = Suc (lengtht s)"
apply (simp add: appt_def lengtht_def)
apply (simp add: Abs_trace_inverse)
done

(*** app length ***)

lemma lengtht_app_decompo1[simp]:
  "noTick s | t = <>
      ==> lengtht (s ^^^ t) = lengtht s + lengtht t"
apply (simp add: appt_def lengtht_def)
apply (simp add: Abs_trace_inverse)
done

lemma lengtht_app_decompo2[simp]:
  "Rep_trace s @ Rep_trace t : trace
      ==> lengtht (s ^^^ t) = lengtht s + lengtht t"
apply (simp add: Rep_in_trace)
done

(*---------------------------*
 |           sett            |
 *---------------------------*)

(*** nil ***)

lemma sett_nil[simp]: "sett <> = {}"
apply (simp add: sett_def)
by (simp add: nilt_def Abs_trace_inverse)

(*** one ***)

lemma sett_one[simp]: "sett <e> = {e}"
apply (simp add: sett_def)
by (simp add: Abs_trace_inverse)

(*** appt ***)

lemma sett_appt1[simp]:
  "noTick s | t = <> ==> sett (s ^^^ t) = sett s Un sett t"
apply (simp add: sett_def appt_def)
apply (simp add: Abs_trace_inverse)
done

lemma sett_appt2[simp]:
  "Rep_trace s @ Rep_trace t : trace
    ==> sett (s ^^^ t) = sett s Un sett t"
by (simp add: Rep_in_trace)

(*---------------------------*
 |     decompo appt Tick     |
 *---------------------------*)

(*** only if ***)

lemma decompo_appt_noTick_only_if:
  "[| noTick s | t = <> ; noTick (s ^^^ t) |] ==> (noTick s & noTick t)"
by (simp add: noTick_def)

(*** if ***)

lemma decompo_appt_noTick_if:
  "[| noTick s ; noTick t |] ==> noTick (s ^^^ t)"
by (simp add: noTick_def)

(*** iff ***)

lemma decompo_appt_noTick[simp]:
  "noTick s | t = <> ==> noTick (s ^^^ t) = (noTick s & noTick t)"
by (simp add: noTick_def)

(*---------------------------*
 |   a trace is ... or ...   |
 *---------------------------*)

(*** trace --> nil or Tick or etc ***)

lemma trace_nil_or_Tick_or_Ev: 
  "ALL t. ((t = <>) | (t = <Tick>) | (EX a s. t=<Ev a> ^^^ s))"
apply (intro allI)
apply (induct_tac t rule: induct_trace)
by (auto)

(*** trace --> nil or unnil ***)

lemma trace_nil_or_unnil: 
  "ALL t. ((t = <>) | (EX a s. t=<a> ^^^ s))"
apply (intro allI)
apply (insert trace_nil_or_Tick_or_Ev)
apply (drule_tac x="t" in spec)
apply (elim conjE disjE exE)
apply (simp_all)

apply (rule_tac x="Tick" in exI)
apply (rule_tac x="<>" in exI)
apply (simp)

apply (rule_tac x="Ev a" in exI)
apply (rule_tac x="s" in exI)
by (simp)

(*** trace --> nil or unnil (last) ***)

lemma trace_last_nil_or_unnil: 
  "ALL t. ((t = <>) | (EX s a. noTick s & t = s ^^^ <a>))"
apply (intro allI)
apply (induct_tac t rule: rev_induct_trace)
by (auto)

(*** trace --> noTick or Tick (last) ***)

lemma trace_last_noTick_or_Tick: 
  "ALL t. (noTick t | (EX s. noTick s & t = s ^^^ <Tick>))"
apply (intro allI impI)
apply (insert trace_last_nil_or_unnil)
apply (drule_tac x="t" in spec, simp)
apply (elim conjE disjE exE)
apply (simp_all)

 apply (insert event_Tick_or_Ev)
 apply (drule_tac x="a" in spec)
by (auto)

(*---------------------------*
 |    same head and last     |
 *---------------------------*)

(*** same head ***)

lemma appt_same_head_only_if: 
  "<Ev a> ^^^ s = <Ev b> ^^^ t  ==> a = b & s = t"
apply (simp add: appt_def)
apply (simp add: Abs_trace_inverse)
apply (simp add: Abs_trace_inject)
apply (simp add: Rep_trace_inject)
done

lemma appt_same_head[simp]: 
  "(<Ev a> ^^^ s = <Ev b> ^^^ t) = (a = b & s = t)"
apply (rule iffI)
apply (rule appt_same_head_only_if)
by (simp_all)

(*** same last ***)

lemma appt_same_last_only_if: 
  "[| noTick s ; noTick t ; s ^^^ <a> = t ^^^ <b> |]
      ==> s = t & a = b"
apply (simp add: appt_def)
apply (simp add: Abs_trace_inverse)
apply (simp add: Abs_trace_inject)
apply (simp add: Rep_trace_inject)
done

lemma appt_same_last[simp]: 
  "[| noTick s ; noTick t |] ==> (s ^^^ <a> = t ^^^ <b>) = (s = t & a = b)"
apply (rule iffI)
apply (rule appt_same_last_only_if)
by (simp_all)

(*---------------------------*
 |     appt decompo one      |
 *---------------------------*)

lemma appt_decompo_one_only_if:
  "[| noTick s | t = <> ; s ^^^ t = <a> |]
   ==> (s = <a> & t = <>) | (s = <> & t = <a>)"
apply (erule disjE)
apply (simp_all)
apply (simp add: appt_def)
apply (simp add: Abs_trace_inject)
apply (simp add: list_app_decompo_one)
apply (simp add: Abs_trace_Rep_trace_inverse nilt_def)
by (auto)

lemma appt_decompo_one[simp]:
  "noTick s | t = <> 
   ==> (s ^^^ t = <a>) = ((s = <a> & t = <>) | (s = <> & t = <a>))"
apply (rule iffI)
apply (simp add: appt_decompo_one_only_if)
by (auto)

lemma appt_decompo_one_sym[simp]:
  "noTick s | t = <> 
   ==> (<a> = s ^^^ t) = ((s = <a> & t = <>) | (s = <> & t = <a>))"
apply (rule iffI)
apply (drule sym, simp)
by (rule sym, simp)

(******************************************************************
                        head and tail
 ******************************************************************)

(*** tl : trace ***)

lemma tlt_trace:
  "[| s : trace ; s ~= [] |] ==> tl s : trace"
apply (simp add: trace_def)
apply (insert list_nil_or_unnil)
apply (drule_tac x="s" in spec)

apply (erule disjE, simp)
apply (elim exE, simp)
by (case_tac "sa = []", simp, simp)

(*** head !! ***)

lemma hdt_appt[simp]: "hdt (<Ev a> ^^^ s) = Ev a"
apply (simp add: appt_def)
apply (simp add: hdt_def)
apply (simp add: Abs_trace_inverse)
done

(* one *)

lemma hdt_one[simp]: "hdt <a> = a"
apply (simp add: hdt_def)
by (simp add: Abs_trace_inverse)

(*** tail !! ***)

lemma tlt_appt[simp]: "tlt (<Ev a> ^^^ s) = s"
apply (simp add: appt_def)
apply (simp add: tlt_def)
apply (simp add: Abs_trace_inverse)
apply (simp add: Rep_trace_inverse)
done

(* one *)

lemma tlt_one[simp]: "tlt <a> = <>"
apply (simp add: tlt_def)
by (simp add: Abs_trace_inverse nilt_def)

(*** head + tail ***)

lemma hdt_appt_tail[simp]: "s ~= <> ==> <hdt s> ^^^ (tlt s) = s"
apply (insert trace_nil_or_Tick_or_Ev)
apply (drule_tac x="s" in spec)
apply (simp)
apply (erule disjE, simp)
by (elim exE, simp)

(******************************************************************
                        butlast & last
 ******************************************************************)

(*** butlast : trace ***)

lemma butlast_trace:
  "[| s : trace ; s ~= [] |] ==> butlast s : trace"
by (simp add: trace_def notin_set_butlast)

lemma butlast_trace_Rep:
  "s ~= <> ==> butlast (Rep_trace s) : trace"
apply (insert Rep_trace[of s])
apply (case_tac "Rep_trace s ~= []")
apply (simp add: trace_def)
apply (simp add: notin_set_butlast)
by (simp)

(*** last !! ***)

lemma lastt_appt[simp]: "noTick s ==> lastt (s ^^^ <e>) = e"
apply (simp add: appt_def)
apply (simp add: lastt_def)
apply (simp add: Abs_trace_inverse)
done

(* one *)

lemma lastt_one[simp]: "lastt <a> = a"
apply (simp add: lastt_def)
by (simp add: Abs_trace_inverse)

(*** butlast !! ***)

lemma butlastt_appt[simp]: "noTick s ==> butlastt (s ^^^ <e>) = s"
apply (simp add: appt_def)
apply (simp add: butlastt_def)
apply (simp add: Abs_trace_inverse)
by (simp add: Rep_trace_inverse)

(* one *)

lemma butlastt_one[simp]: "butlastt <a> = <>"
apply (simp add: butlastt_def)
by (simp add: Abs_trace_inverse nilt_def)

(*** butlast + last ***)

lemma butlastt_appt_lastt[simp]: "s ~= <> ==> (butlastt s) ^^^ <lastt s> = s"
apply (insert trace_last_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (simp)
apply (elim conjE exE)
by (simp)

(******************************************************************
                        noTick + alpha
 ******************************************************************)

(* Tick in *)

lemma not_noTick_unnil[simp]: "~ noTick s ==> s ~= <>"
by (case_tac "s ~= <>", simp_all)

(* noTick butlastt *)

lemma noTick_butlast: "s ~= <> ==> noTick (butlastt s)"
apply (simp add: butlastt_def)
apply (simp add: noTick_def sett_def)
apply (simp add: butlast_trace_Rep Abs_trace_inverse)
apply (insert Rep_trace[of s])
by (simp add: trace_def)

(* Tick and butlastt *)

lemma Tick_decompo_lm: "ALL s. ~ noTick s --> s = ((butlastt s) ^^^ <Tick>)"
apply (intro allI impI)
apply (insert trace_last_nil_or_unnil)
apply (drule_tac x="s" in spec)
apply (simp)

apply (elim conjE exE)
by (simp add: noTick_def)

lemma Tick_decompo: "~ noTick s ==> s = ((butlastt s) ^^^ <Tick>)"
by (simp add: Tick_decompo_lm)

(******************************************************************
                         lengtht plus
 ******************************************************************)

(*** lengtht zero ***)

lemma lengtht_zero: "(lengtht s = 0) = (s = <>)"
apply (induct_tac s rule: induct_trace)
by (simp_all)

(*** lengtht one ***)

lemma lengtht_one: "(lengtht s = Suc 0) = (EX e. s = <e>)"
apply (induct_tac s rule: induct_trace)
apply (simp_all)
by (simp add: lengtht_zero)

(******************************************************************
                         convenient lemmas
 ******************************************************************)

(*-------------------*
 |  for Seq_compo T1 |
 *-------------------*)

lemma appt_decompo_lm: 
  "ALL s1 s2 t1 t2.
   (noTick s1 & s2 ~= <> & noTick t1 & t2 ~= <>)
       --> (s1 ^^^ s2 = t1 ^^^ t2) 
           = ((EX u. s1 ^^^ u = t1 & s2 = u ^^^ t2 & noTick u) |
              (EX u. s1 = t1 ^^^ u & u ^^^ s2 = t2 & noTick u))"
apply (rule allI)
apply (induct_tac s1 rule: induct_trace)
apply (force)
apply (force)
apply (intro allI impI)
apply (drule_tac x="s2" in spec, simp)

apply (rule iffI)
 (* => *)
 apply (insert trace_nil_or_Tick_or_Ev)
 apply (rotate_tac -1)

 apply (drule_tac x="t1" in spec)
 apply (erule disjE, simp)
 apply (erule disjE, simp)
 apply (elim exE, simp)     (* t1 = [Ev aa]t ^^^ sa *)
 apply (drule_tac x="sa" in spec)
 apply (drule_tac x="t2" in spec)
 apply (simp add: appt_assoc)

 (* <= *)
 apply (elim disjE conjE exE)
 apply (auto simp add: appt_assoc_sym)
done

lemma appt_decompo: 
  "[| noTick s1 | s2 = <> ; noTick t1 | t2 = <> |]
   ==> (s1 ^^^ s2 = t1 ^^^ t2) 
       = ((EX u. s1 ^^^ u = t1 & s2 = u ^^^ t2 & (noTick u | (noTick s1 & t2 = <>))) |
          (EX u. s1 = t1 ^^^ u & u ^^^ s2 = t2 & (noTick u | (noTick t1 & s2 = <>))))"
apply (case_tac "s2 ~= <>")
apply (case_tac "t2 ~= <>")
apply (auto simp add: appt_decompo_lm)
done

(*-------------------*
 |  for Seq_compo T2 |
 *-------------------*)

lemma noTick_or_last_Tick: 
  "ALL s. noTick s | (EX t. s = t ^^^ <Tick>)"
apply (rule allI)
apply (induct_tac s rule: rev_induct_trace)
apply (simp_all)
apply (insert event_Tick_or_Ev)
apply (drule_tac x="e" in spec)
by (auto)

(*--------------------------*
 |  used in Alpha_parallel  |
 *--------------------------*)

(*** Tick & sett ***)

lemma not_noTick_in_sett_imp:
  "~ (noTick s) --> (EX t. s = t ^^^ <Tick> & noTick t)"
apply (induct_tac s rule: induct_trace)
apply (simp_all)
apply (rule_tac x="<>" in exI)
apply (simp)

apply (intro allI impI)
apply (simp)
apply (elim exE)
apply (simp)
apply (rule_tac x="<Ev a> ^^^ t" in exI)
apply (simp add: appt_assoc)
done

lemma Tick_in_sett_imp:
  "Tick : sett(s) --> (EX t. s = t ^^^ <Tick> & noTick t)"
apply (insert not_noTick_in_sett_imp[of s])
by (simp add: noTick_def)

lemma Tick_in_sett: "(Tick : sett(s)) = (EX t. s = t ^^^ <Tick> & noTick t)"
apply (rule iffI)
apply (simp add: Tick_in_sett_imp)
apply (elim conjE exE)
by (simp)

(*--------------------------------*
 |   used in Inductive_parallel   |
 *--------------------------------*)

lemma sett_subset_Tick_if:
 "(u = <> | u = <Tick>) ==> (sett u <= {Tick})"
by (auto)

lemma sett_subset_Tick_only_if:
 "(sett u <= {Tick}) --> (u = <> | u = <Tick>)"
apply (induct_tac u rule: induct_trace)
by (simp_all)

lemma sett_subset_Tick:
 "(sett u <= {Tick}) = (u = <> | u = <Tick>)"
apply (rule iffI)
apply (simp add: sett_subset_Tick_only_if)
apply (simp add: sett_subset_Tick_if)
done

(*--------------------------*
 |    lengtht [a,b,c]t      |
 *--------------------------*)

lemma lengtht_Abs_trace: "s : trace ==> lengtht (Abs_trace s) = length s"
apply (simp add: lengtht_def)
apply (simp add: Abs_trace_inverse)
done

lemma lengtht_Abs_trace_noTick: 
  "Tick ~: set  (butlast s) ==> lengtht (Abs_trace s) = length s"
apply (simp add: lengtht_Abs_trace[simplified trace_def])
done

(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)

(* ~ noTick *)

lemma not_noTick_in_sett: "(~ (noTick s)) = (EX t. s = t ^^^ <Tick> & noTick t)"
apply (rule iffI)
apply (subgoal_tac "Tick : sett(s)")
apply (simp add: Tick_in_sett)
apply (simp add: noTick_def)
apply (simp (no_asm_simp) add: noTick_def)
apply (simp add: Tick_in_sett)
done

(*-------------------*
 |  for Seq_compo T2 |
 *-------------------*)

lemma noTick_or_last_Tick2: 
  "ALL s. noTick s | (EX t. s = t ^^^ <Tick> & noTick t)"
apply (rule allI)
apply (induct_tac s rule: rev_induct_trace)
apply (simp_all)
apply (insert event_Tick_or_Ev)
apply (drule_tac x="e" in spec)
apply (elim disjE exE)
apply (force)
apply (rule disjI1)
apply (force)
done


(****************** to add it again ******************)

declare disj_not1 [simp] 

end
