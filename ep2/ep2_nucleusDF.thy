           (*-------------------------------------------------*
            |                 (a part of) ep2                 |
            |                  September 2004                 |
            |                   December 2004 (modified)      |
            |                   November 2005 (modified)      |
            |                      April 2006 (modified)      |
            |                      March 2007  (modified)     |
            |                     August 2007  (modified)     |
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

theory ep2_nucleusDF
imports DFP ep2_nucleus
begin

(*********************************************************
                     abstract level
 *********************************************************)

datatype AbsName = Abstract | Loop

primrec
  Absfun :: "AbsName => (AbsName, Event) proc"
where
  "Absfun Abstract
          = c !? x -> $Loop"

 |"Absfun Loop
          = c !? x -> (SKIP |~| c !? x -> $Loop)"
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
  Abs_def: "Abs == $Abstract"

(*********************************************************
               guard lemmas (routine work)
 *********************************************************)

lemma guardedfun_Abs[simp]:
      "guardedfun Absfun"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp_all)

(*********************************************************
        relating function between ACName and AbsName
 *********************************************************)

primrec
  Abs_to_AC :: "AbsName => (ACName, Event) proc"
where
  "Abs_to_AC (Abstract)
          = ($Acquirer |[range c]| $Terminal)"

 |"Abs_to_AC (Loop)
          = ($AcConfigManagement |[range c]| $TerminalConfigManagement)"

(*********************************************************
           a theorem for verifying Abs <=F AC
 *********************************************************)

declare simp_event_set [simp]

theorem ep2_Abs_AC: "Abs <=F AC"
apply (unfold Abs_def AC_def)
apply (rule cspF_fp_induct_left[of _ "Abs_to_AC"], auto)
  apply (induct_tac p, auto)
   apply (cspF_unwind)+
   apply (cspF_hsf)+
   apply (rule cspF_decompo_ref)
   apply (auto)
     apply (cspF_hsf)+
   apply (rule cspF_decompo_ref)
   apply (auto)
   apply (cspF_hsf)+

  (* 2 *)   (* modified for Isabelle2020
               Probably, this proof script can be more simplified *)

   apply (cspF_unwind)+
   apply (cspF_hsf+, auto)

   apply (rule cspF_Rep_int_choice_com_left, auto)
   apply (rule_tac x="Exit xa" in exI)
   apply (cspF_hsf)+
   apply (rule cspF_decompo_ref, auto)
   apply (cspF_hsf)+
   apply (rule cspF_Int_choice_left1, auto)

   apply (cspF_unwind)+
   apply (cspF_hsf+, auto)
   apply (rule cspF_Rep_int_choice_com_left, auto)
   apply (rule_tac x="Request xa" in exI)
   apply (cspF_hsf)+
   apply (rule cspF_decompo_ref, auto)
   apply (cspF_hsf)+
   apply (rule cspF_Int_choice_left2)
   apply (rule cspF_decompo_ref, auto)
   apply (cspF_hsf)+
   apply (rule cspF_decompo_ref, auto)
   apply (cspF_simp)+
done

(*********************************************************
        relating function between ACName and AbsName
 *********************************************************)

primrec
  Abs_to_DF :: "AbsName => (DFtickName, Event) proc"
where
  "Abs_to_DF (Abstract) = ($DFtick)"
 |"Abs_to_DF (Loop) = ($DFtick)"

(*********************************************************
           a theorem for verifying Abs <=F AC
 *********************************************************)
 
theorem ep2_DF_Abs: "$DFtick <=F Abs"
apply (unfold Abs_def)
apply (rule cspF_fp_induct_right[of _ _ "Abs_to_DF"], auto)
apply (induct_tac p, auto)
apply (cspF_auto)+
apply (rule cspF_Int_choice_left1)
apply (cspF_prefix_left)
apply (rule cspF_decompo_ref)
apply (auto)

apply (cspF_auto)+
apply (rule cspF_Int_choice_left1)
apply (cspF_prefix_left)
apply (rule cspF_decompo_ref)
apply (auto)
apply (cspF_auto)+
apply (rule cspF_Int_choice_left2)
apply (auto)
apply (cspF_auto)+
apply (rule cspF_Int_choice_left1)
apply (cspF_prefix_left)
apply (rule cspF_decompo_ref)
apply (auto)
done

(*-------------------------------------------------------*
 |                 AC is Deadlock-free.                  |
 *-------------------------------------------------------*)

theorem AC_isDeadlockFree: "AC isDeadlockFree"
apply (simp add: DeadlockFree_DFtick_ref)
apply (rule cspF_trans[of _ _ _ Abs])
apply (rule ep2_DF_Abs, rule ep2_Abs_AC)
done

end
