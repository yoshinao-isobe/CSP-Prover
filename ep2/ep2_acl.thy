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
            |        CSP-Prover on Isabelle2012               |
            |                   November 2012  (modified)     |
            |                                                 |
            |        CSP-Prover on Isabelle2016               |
            |                        May 2016  (modified)     |
            |                                                 |
            |  Markus Roggenbach (Univ of Wales Swansea, UK)  |
            |  Yoshinao Isobe    (AIST, Japan)                |
            *-------------------------------------------------*)

theory ep2_acl
imports CSP_F
begin

(*********************************************************
          automatic unfolding syntactic-sugar
 *********************************************************)

declare csp_prefix_ss_def [simp]

(*********************************************************
              data type passed on channels
 *********************************************************)

typedecl D_SI_Init_SessionStart
typedecl D_SI_Init_SessionEnd
typedecl D_SI_Init_ConfigDataRequest
typedecl D_SI_Init_ConfigDataResponse
typedecl D_SI_Init_ConfigDataNotification
typedecl D_SI_Init_ConfigDataAcknowledge
typedecl D_SI_Init_RemoveConfigDataNotification
typedecl D_SI_Init_RemoveConfigDataAcknowledge
typedecl D_SI_Init_ActivateConfigDataNotification
typedecl D_SI_Init_ActivateConfigDataAcknowledge

datatype D_SI_Init = 
     SStart D_SI_Init_SessionStart
   | SEnd   D_SI_Init_SessionEnd
   | CDReq  D_SI_Init_ConfigDataRequest
   | CDRes  D_SI_Init_ConfigDataResponse
   | CDN    D_SI_Init_ConfigDataNotification
   | CDA    D_SI_Init_ConfigDataAcknowledge
   | RCDN   D_SI_Init_RemoveConfigDataNotification
   | RCDA   D_SI_Init_RemoveConfigDataAcknowledge
   | ACDN   D_SI_Init_ActivateConfigDataNotification
   | ACDA   D_SI_Init_ActivateConfigDataAcknowledge

typedecl TerminalState
typedecl Trigger
typedecl Message

(*********************************************************
                     event (channel)
 *********************************************************)

datatype Event = C_SI_Init D_SI_Init
               | C_TerminalDisplay Message
               | PairTT "TerminalState * Trigger"

(*********************************************************
         abstract component description level
 *********************************************************)

datatype ACName = TInit
                | TConfigurationManagement
                | AcquirerInit
                | ConfigurationManagement

primrec
  ACfun :: "ACName => (ACName, Event) proc"
where
  "ACfun (TInit) 
    = C_SI_Init !? x: (range SStart)
      -> $(TConfigurationManagement)"

 |"ACfun (TConfigurationManagement)
    = C_SI_Init ? x ->
       IF (x:range CDReq)
       THEN (C_SI_Init !? y: (range CDRes)
            -> $(TConfigurationManagement))

       ELSE IF (x:range CDN)
       THEN (C_SI_Init !? y: (range CDA)
            -> $(TConfigurationManagement))

       ELSE IF (x:range RCDN)
       THEN (C_SI_Init !? y: (range RCDA)
            -> $(TConfigurationManagement))

       ELSE IF (x:range ACDN)
       THEN (C_SI_Init !? y: (range ACDA)
            -> $(TConfigurationManagement))

       ELSE IF (x:range SEnd)
       THEN SKIP
       ELSE STOP"

 |"ACfun (AcquirerInit)
    = C_SI_Init ? sessionStart: (range SStart)
      -> $(ConfigurationManagement)"

 |"ACfun (ConfigurationManagement)
    =     C_SI_Init !? sessionEnd:(range SEnd) -> SKIP
      |~| C_SI_Init !? request:(range CDReq)
          -> C_SI_Init ? response:(range CDRes)
          -> $(ConfigurationManagement)
      |~| C_SI_Init !? notification:(range CDN)
          -> C_SI_Init ? acknowledge:(range CDA)
          -> $(ConfigurationManagement)
      |~| C_SI_Init !? notification:(range RCDN)
          -> C_SI_Init ? acknowledge:(range RCDA)
          -> $(ConfigurationManagement)
      |~| C_SI_Init !? notification:(range ACDN)
          -> C_SI_Init ? acknowledge:(range ACDA)
          -> $(ConfigurationManagement)"
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
  AC_def: "AC == ($TInit |[range C_SI_Init]| $AcquirerInit)"

(*********************************************************
              gProc lemmas (routine work)
 *********************************************************)

lemma guarded_AC[simp]:
      "guardedfun ACfun"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp_all)+

(*********************************************************
               abstract level (deadlock free)
 *********************************************************)


abbreviation REQs :: "D_SI_Init set"
where "REQs == (range CDReq) Un (range CDN) Un 
               (range RCDN)  Un (range ACDN)"

abbreviation RESs :: "D_SI_Init set"
where "RESs == (range CDRes) Un (range CDA) Un 
               (range RCDA)  Un (range ACDA)"

datatype AbsName = Abstract | Loop

fun
  Absfun :: "AbsName => (AbsName, Event) proc"
where
  "Absfun (Abstract)
          = C_SI_Init !? init:(range SStart) -> $(Loop)"

| "Absfun (Loop)
          = C_SI_Init !? exit:(range SEnd) -> SKIP
            |~| 
            C_SI_Init !? request:REQs
              -> C_SI_Init !? response:RESs
                -> $(Loop)"
(*
defs (overloaded)
  Set_Absfun_def [simp]: "PNfun == Absfun"
*)


overloading Set_Absfun == 
  "PNfun :: (AbsName, Event) pnfun"
begin
  definition "PNfun == Absfun"
end
  
declare Set_Absfun_def [simp]

definition
  Abs :: "(AbsName, Event) proc"
  where
  Abs_def: "Abs == $(Abstract)"

(*********************************************************
               gProc lemmas (routine work)
 *********************************************************)

lemma guarded_Abs[simp]:
      "guardedfun Absfun"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp_all)+

(*********************************************************
        relating function between AbsName and ACName
 *********************************************************)

primrec
  Abs_to_AC :: "AbsName => (ACName,Event) proc"
where
  "Abs_to_AC (Abstract)
          = ($TInit |[range C_SI_Init]| $AcquirerInit)"

 |"Abs_to_AC (Loop)
          = ($TConfigurationManagement |[range C_SI_Init]|
             $ConfigurationManagement)"

(*********************************************************
           a theorem for verifying Abs <=F AC
               (i.e. AC is deadlock-free)
 *********************************************************)

overloading FPmode == 
  "FPmode :: fpmode"
begin
  definition "FPmode == CMSmode"
end

declare FPmode_def [simp]
(*
defs FPmode_def [simp]: "FPmode == CMSmode"
*)

(*** CMS-based approach ***)

declare inj_on_def       [simp]


theorem ep2_abs: "Abs <=F AC"
apply (simp add: Abs_def AC_def)

  (***** by fixed point induction *****)
apply (rule cspF_fp_induct_left[of _ "Abs_to_AC"])

  (***** check guarded and no hiding operators *****)
apply (simp_all)
apply (simp)

   (*** recursion ***)
apply (induct_tac p)
apply (simp_all)

(*** initializing ***)

apply (cspF_unwind)
apply (cspF_dist)

apply (cspF_simp)
apply (auto)
apply (cspF_step)+
apply (rule cspF_decompo_subset)

apply (auto)
apply (cspF_simp)

(*** main loop ***)

apply (cspF_unwind)
apply (cspF_dist)+
apply (auto)

 (*** skip ***)
apply (cspF_step)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_decompo_subset)
apply (auto)
apply (simp add: image_iff)
apply (cspF_step)+

 (*** C_SI_Init ? ***)
apply (rule cspF_Int_choice_left2)
apply (rule cspF_decompo_subset)
apply (auto)
apply (simp add: image_iff)
apply (cspF_simp)+

apply (cspF_dist)
apply (cspF_simp)
apply (rule cspF_decompo_subset)
apply (auto)
apply (cspF_step)+
apply (auto)
apply (cspF_simp)

 (*** CD req res ***)
apply (rule cspF_Int_choice_left2)
apply (cspF_step)+
apply (rule cspF_decompo_subset)
apply (auto)
apply (simp add: image_iff)
apply (cspF_simp)+

apply (cspF_dist)
apply (cspF_simp)
apply (rule cspF_decompo_subset)
apply (auto)
apply (cspF_step)+
apply (auto)
apply (cspF_simp)

 (*** RCD ***)
apply (rule cspF_Int_choice_left2)
apply (cspF_step)+
apply (rule cspF_decompo_subset)
apply (auto)
apply (simp add: image_iff)
apply (cspF_simp)+

apply (cspF_dist)
apply (cspF_simp)
apply (rule cspF_decompo_subset)
apply (auto)
apply (cspF_step)+
apply (auto)
apply (cspF_simp)

 (*** ACD ***)
apply (rule cspF_Int_choice_left2)
apply (cspF_step)+
apply (rule cspF_decompo_subset)
apply (auto)
apply (simp add: image_iff)
apply (cspF_simp)+

apply (cspF_dist)
apply (cspF_simp)
apply (rule cspF_decompo_subset)
apply (auto)
apply (cspF_step)+
apply (auto)
apply (cspF_simp)
done

declare inj_on_def [simp del]

end
