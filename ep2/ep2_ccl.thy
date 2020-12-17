           (*-------------------------------------------------*
            |                 (a part of) ep2                 |
            |                  September 2004                 |
            |                   December 2004 (modified)      |
            |                   November 2005 (modified)      |
            |                      April 2006 (modified)      |
            |                      March 2007 (modified)      |
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

theory ep2_ccl
imports ep2_acl
begin

(*********************************************************
                    functions
 *********************************************************)

(* pair *)
definition
  state  :: "TerminalState * Trigger => TerminalState"
  where
  state_def  : "state p == fst p"
  
definition  
  trigger:: "TerminalState * Trigger => Trigger"
  where
  trigger_def: "trigger p == snd p"

(* Session start *)
consts
  sessionStart:: "Trigger => D_SI_Init_SessionStart"

(* ConfigDataRequest *)
consts
  configDataResponse:: 
    "D_SI_Init_ConfigDataRequest * TerminalState => 
     D_SI_Init_ConfigDataResponse"

(* ConfigDataNotification *)
consts
  configDataAcknowledge:: D_SI_Init_ConfigDataAcknowledge 
  configData::
    "D_SI_Init_ConfigDataNotification * TerminalState =>
     TerminalState"

(* ConfigDataRemove *)
consts
  removeDataAcknowledge:: D_SI_Init_RemoveConfigDataAcknowledge
  removeData:: "D_SI_Init_RemoveConfigDataNotification * TerminalState =>
                TerminalState"

(* ActivateConfigDataNotification *)
consts
  activateDataAcknowledge:: D_SI_Init_ActivateConfigDataAcknowledge
  activateData:: "D_SI_Init_ActivateConfigDataNotification * TerminalState =>
                  TerminalState"

(* Message *)
consts
  AcqConnectionFailed    :: Message
  InitialisationFinished :: Message
  InitialisationFailed   :: Message

(*********************************************************
         concrete component description level
 *********************************************************)

datatype CCName = CTInit "TerminalState * Trigger"
                | CTConfigurationManagement "TerminalState * Trigger"
                | CAcquirerInit
                | CConfigurationManagement

fun 
  CCfun :: "CCName => (CCName, Event) proc"
where 
  "CCfun (CTInit p) 
    = C_SI_Init ! (SStart (sessionStart (trigger p)))
      -> $(CTConfigurationManagement p)"

| "CCfun (CTConfigurationManagement p)
    = C_SI_Init ? x ->
       IF (x:range CDReq)
       THEN (C_SI_Init ! 
               (CDRes (configDataResponse 
               (((inv CDReq) x),(state p)))) 
            -> $(CTConfigurationManagement p))

       ELSE IF (x:range CDN)
       THEN (C_SI_Init ! (CDA configDataAcknowledge)
            -> $(CTConfigurationManagement 
                ((configData (((inv CDN) x),(state p))), (trigger p))))

       ELSE IF (x:range RCDN)
       THEN (C_SI_Init ! (RCDA removeDataAcknowledge)
            -> $(CTConfigurationManagement 
                (removeData((inv RCDN) x,(state p)), (trigger p))))

       ELSE IF (x:range ACDN)
       THEN (C_SI_Init ! (ACDA activateDataAcknowledge)
            -> $(CTConfigurationManagement 
                (activateData((inv ACDN) x,(state p)), (trigger p))))

       ELSE IF (x:range SEnd)
       THEN (C_TerminalDisplay ! InitialisationFinished -> SKIP)
       ELSE STOP"

| "CCfun (CAcquirerInit)
    = C_SI_Init ? sessionStart: (range SStart)
      -> $(CConfigurationManagement)"

| "CCfun (CConfigurationManagement)
    =     C_SI_Init !? sessionEnd:(range SEnd) -> SKIP
      |~| C_SI_Init !? request:(range CDReq)
          -> C_SI_Init ? response:(range CDRes)
          -> $(CConfigurationManagement)
      |~| C_SI_Init !? notification:(range CDN)
          -> C_SI_Init ? acknowledge:(range CDA)
          -> $(CConfigurationManagement)
      |~| C_SI_Init !? notification:(range RCDN)
          -> C_SI_Init ? acknowledge:(range RCDA)
          -> $(CConfigurationManagement)
      |~| C_SI_Init !? notification:(range ACDN)
          -> C_SI_Init ? acknowledge:(range ACDA)
          -> $(CConfigurationManagement)"

overloading Set_CCfun == 
  "PNfun :: (CCName, Event) pnfun"
begin
  definition "PNfun == CCfun"
end
  
declare Set_CCfun_def [simp]

(*
defs (overloaded)
  Set_CCfun_def [simp]: "PNfun == CCfun"
*)

definition
  CC :: "(TerminalState * Trigger) => (CCName, Event) proc"
  where
  CC_def: "CC p == $(CTInit p)-- (range C_TerminalDisplay)
                   |[range C_SI_Init]| $(CAcquirerInit)"

(*********************************************************
                gProc lemmas (routine work)
 *********************************************************)

lemma guarded_CC[simp]:
      "guardedfun CCfun"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp_all)+

(*********************************************************
        relating function between AbsName and ACName
 *********************************************************)

primrec
  AC_to_CC :: "ACName => (CCName, Event) proc"
where
  "AC_to_CC (TInit)                    =  
     !<PairTT> p .. ($(CTInit p))-- range C_TerminalDisplay"

 |"AC_to_CC (TConfigurationManagement) = 
     !<PairTT> p ..  ($(CTConfigurationManagement p)) -- range C_TerminalDisplay"

 |"AC_to_CC (AcquirerInit)             = $CAcquirerInit"
 |"AC_to_CC (ConfigurationManagement)  = $CConfigurationManagement"

(*********************************************************
           a theorem for verifying !!p. AC <=F CC p
 *********************************************************)

declare inj_on_def [simp]

lemma ep2_ccl_terminal_step1:
    "(ACfun TInit)<<AC_to_CC <=F AC_to_CC TInit"
apply (auto)
apply (cspF_unwind)+
apply (cspF_step)+
apply (simp add: image_iff)
apply (cspF_simp)+
apply (rule cspF_decompo_subset)
apply (auto)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="(a,b)" in exI)
apply (simp)
done

(*** loop (terminal) ***)

lemma ep2_ccl_terminal_step2:
    "(ACfun TConfigurationManagement)<<AC_to_CC <=F 
          AC_to_CC TConfigurationManagement"
apply (auto)
apply (cspF_unwind)
apply (cspF_step)+
apply (simp add: image_iff)
apply (subgoal_tac "range C_SI_Init Int range C_TerminalDisplay = {}")
apply (cspF_simp)
apply (auto)

apply (case_tac "x : range CDReq")
apply (subgoal_tac "(EX xa. x = CDReq xa)", erule exE)
apply (cspF_step)+
apply (subgoal_tac "(C_SI_Init (CDRes (configDataResponse (xa, state (a, b))))
                    ~: range C_TerminalDisplay)")
apply (cspF_simp)
apply (rule cspF_decompo_subset)
apply (auto)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="(a, b)" in exI)
apply (simp)

apply (case_tac "(EX xa. x = CDReq xa)")
apply (auto)
apply (cspF_step)+

apply (case_tac "(EX xa. x = CDN xa)")
apply (auto)
apply (cspF_step)+

apply (subgoal_tac "(C_SI_Init (CDA configDataAcknowledge) ~: range C_TerminalDisplay)")
apply (cspF_simp)
apply (auto)

apply (rule cspF_decompo_subset)
apply (auto)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="(configData (xa, state (a, b)), trigger (a, b))" in exI)
apply (simp)

apply (cspF_simp)
apply (case_tac "(EX xa. x = RCDN xa) ")
apply (auto)
apply (cspF_step)+
apply (subgoal_tac "(C_SI_Init (RCDA removeDataAcknowledge) ~: range C_TerminalDisplay)")
apply (auto)
apply (cspF_simp)

apply (rule cspF_decompo_subset)
apply (auto)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="(removeData (xa, state (a, b)), trigger (a, b))" in exI)
apply (simp)

apply (cspF_simp)
apply (case_tac "(EX xa. x = ACDN xa)")
apply (auto)
apply (cspF_step)+
apply (subgoal_tac "(C_SI_Init (ACDA activateDataAcknowledge) ~: range C_TerminalDisplay)")
apply (auto)
apply (cspF_simp)+

apply (rule cspF_decompo_subset)
apply (auto)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="(activateData (xa, state (a, b)), trigger (a, b))" in exI)
apply (simp)

 (*** C_TerminalDisplay ***)

apply (cspF_simp)
apply (case_tac "(EX xa. x = SEnd xa)")
apply (auto)
apply (cspF_step)+
done

lemma ACDef_AC_to_CC: "(ACfun p)<<AC_to_CC <=F AC_to_CC p"
apply (induct_tac p)
apply (simp add: ep2_ccl_terminal_step1 del: ACfun.simps AC_to_CC.simps)
apply (simp add: ep2_ccl_terminal_step2 del: ACfun.simps AC_to_CC.simps)
apply (cspF_unwind)+
done

(****************************
      !!p. AC p <=F CC p
 ****************************)

theorem ep2_acl_ccl: "!!p. AC <=F CC p"
apply (simp add: AC_def CC_def)
apply (rule cspF_decompo)
apply (simp)

(*** TInit ***)

 (* by fixed point induction *)

apply (rule cspF_fp_induct_left[of _ "AC_to_CC"])
apply (simp_all)
apply (simp)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="p" in exI)
apply (simp)

apply (simp add: ACDef_AC_to_CC)

(*** AcquirerInit ***)

 (* by fixed point induction *)

apply (rule cspF_fp_induct_left[of _ "AC_to_CC"])
apply (simp_all)
apply (simp)
apply (simp add: ACDef_AC_to_CC)
done

(****************************
      !!p. Abs <=F CC p
 ****************************)

theorem ep2_abs_ccl: "!!p. Abs <=F CC p"
apply (rule cspF_trans)
apply (rule ep2_abs)
apply (rule ep2_acl_ccl)
done

declare inj_on_def [simp del]

end
