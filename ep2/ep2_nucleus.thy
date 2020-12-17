           (*-------------------------------------------------*
            |                 (a part of) ep2                 |
            |                  September 2004                 |
            |                   December 2004 (modified)      |
            |                   November 2005 (modified)      |
            |                      April 2006 (modified)      |
            |                      March 2007  (modified)     |
            |                                                 |
            |        CSP-Prover on Isabelle2009               |
            |                       June 2009  (modified)     |
            |                                                 |
            |        CSP-Prover on Isabelle2016               |
            |                        May 2016  (modified)     |
            |                                                 |
            |  Markus Roggenbach (Univ of Wales Swansea, UK)  |
            |  Yoshinao Isobe    (AIST, Japan)                |
            *-------------------------------------------------*)

theory ep2_nucleus
imports CSP_F
begin

(*** To automatically unfold syntactic sugar ***)

declare csp_prefix_ss_def [simp]
declare inj_on_def        [simp]

(*********************************************************
              data type passed on channels
 *********************************************************)

typedecl init_d typedecl request_d typedecl response_d typedecl exit_d

datatype Data = Init    init_d    | Exit     exit_d
              | Request request_d | Response response_d

(*********************************************************
                     event (channel)
 *********************************************************)

datatype Event = c Data

(*********************************************************
         abstract component description level
 *********************************************************)

datatype ACName = Acquirer | AcConfigManagement 
                | Terminal | TerminalConfigManagement

primrec
  ACfun :: "ACName => (ACName, Event) proc"
where
  "ACfun Acquirer
         = c ? x:(range Init) -> $AcConfigManagement"

 |"ACfun AcConfigManagement
         = c !? exit:(range Exit) -> SKIP
           |~| 
           c !? request:(range Request)
             -> c ? response:(range Response)
             -> $AcConfigManagement"

 |"ACfun Terminal
         = c !? init:(range Init) -> $TerminalConfigManagement"

 |"ACfun TerminalConfigManagement
         = c ? x -> IF (x:range Request) 
                    THEN (c !? response:(range Response)
                          -> $TerminalConfigManagement)
                    ELSE IF (x:range Exit)
                         THEN SKIP
                         ELSE STOP"
(*
defs (overloaded)
Set_ACfun_def [simp]: "PNfun == ACfun"
*)

overloading Set_ACfun == 
  "PNfun :: (ACName, Event) pnfun"
begin
  definition "PNfun == ACfun"
end

declare Set_ACfun_def [simp]

definition
  AC :: "(ACName, Event) proc"
  where
  AC_def: "AC == ($Acquirer |[range c]| $Terminal)"

(*---------------------------------------------------------------*
 |                          NOTE                                 |
 |                                                               |
 | c ! v -> P       : sends a value v to c, then behaves like P. |
 |                                                               |
 | c ? x:X -> P(x)  : receives a value v from c if c in X,       |
 |                    then behaves like P(v).                    |
 |                                                               |
 | c !? x:X -> P(x) : sends a value v selected from X to c,      |
 |                    then behaves like P(v).                    |
 |                                                               |
 *---------------------------------------------------------------*)

(*********************************************************
              equivalent sequential behavior
 *********************************************************)

datatype SeqName = SeqInit | Loop

primrec
  Seqfun :: "SeqName => (SeqName, Event) proc"
where
  "Seqfun SeqInit
          = c !? init:(range Init) -> $Loop"

 |"Seqfun Loop
          = c !? exit:(range Exit) -> SKIP
            |~| 
            c !? request:(range Request)
              -> c !? response:(range Response)
              -> $Loop"
(*
defs (overloaded)
Set_Seqfun_def [simp]: "PNfun == Seqfun"
*)

overloading Set_Seqfun == 
  "PNfun :: (SeqName, Event) pnfun"
begin
  definition "PNfun == Seqfun"
end
  
declare Set_Seqfun_def [simp]

definition
  Seq :: "(SeqName, Event) proc"
  where
  Seq_def: "Seq == $SeqInit"

(*********************************************************
        relating function between ACName and SeqName
 *********************************************************)

primrec
  Seq_to_AC :: "SeqName => (ACName, Event) proc"
where
  "Seq_to_AC (SeqInit)
          = ($Acquirer |[range c]| $Terminal)"

 |"Seq_to_AC (Loop)
          = ($AcConfigManagement |[range c]| $TerminalConfigManagement)"

(*********************************************************
               gProc lemmas (routine work)
 *********************************************************)

lemma guardedfun_AC_Seq[simp]:
      "guardedfun ACfun"
      "guardedfun Seqfun"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp_all)+

(*********************************************************
           a theorem for verifying Seq <=F AC
 *********************************************************)
(*
defs FPmode_def [simp]: "FPmode == CMSmode"
*)

overloading FPmode == 
  "FPmode :: fpmode"
begin
  definition "FPmode == CMSmode"
end

declare FPmode_def [simp]


theorem ep2: "Seq =F AC"
apply (unfold Seq_def AC_def)
apply (rule cspF_fp_induct_left[of _ "Seq_to_AC"])
apply (simp_all)
apply (simp)
apply (induct_tac p)
apply (simp_all)

(* 1st subgoal *)
apply (cspF_unwind)
apply (cspF_hsf)+
apply (rule cspF_decompo, auto)
apply (cspF_hsf)+
apply (rule cspF_decompo, auto)
apply (cspF_hsf)+

(* 2nd subgoal *)
apply (cspF_auto | rule cspF_decompo | rule cspF_decompo_ref | 
       auto simp add: image_iff)+
done

end
