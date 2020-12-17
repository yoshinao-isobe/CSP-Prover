           (*-------------------------------------------*
            |                  DFtick                   |
            |                                           |
            |                   June 2007               |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory DFP_DFtick
imports DFP_Deadlock
begin

(*****************************************************************

         1. The most abstract deadlockfree process DFtick

 *****************************************************************)

declare csp_prefix_ss_def[simp]

(*********************************************************
                         event
 *********************************************************)

(* typedecl Event    any event *)

datatype DFtickName = DFtick

(*** Spc ***)

primrec
  DFtickfun ::  "(DFtickName, 'event) pnfun"
where
  "DFtickfun (DFtick) = (! x ->  $(DFtick)) |~| SKIP "
(*
defs (overloaded)
Set_DFtickfun_def [simp]: "PNfun == DFtickfun"
*)

overloading Set_DFtickfun == 
  "PNfun :: (DFtickName, 'event) pnfun"
begin
  definition "PNfun :: (DFtickName, 'event) pnfun == DFtickfun"
end
  
declare Set_DFtickfun_def [simp]

(*---------------------------------------------------*
 |                  n-replicted spec                 |
 *---------------------------------------------------*)

datatype RDFtickName = RDFtick

(*** Spc ***)

primrec
  NatDFtick :: 
     "nat => (RDFtickName, 'event) proc
          => (RDFtickName, 'event) proc"
where
    "NatDFtick 0 P = P"
  | "NatDFtick (Suc n) P = ((! x -> NatDFtick n P) |~| SKIP) |~| P"


primrec
  RDFtickfun :: 
    "RDFtickName
         => (RDFtickName, 'event) proc"
where
  "RDFtickfun (RDFtick)
     = (! x -> (!nat n .. NatDFtick n ($(RDFtick))) |~| SKIP)"
(*
defs (overloaded)
Set_RDFtickfun_def [simp]: "PNfun == RDFtickfun"
*)

overloading Set_RDFtickfun == 
  "PNfun :: (RDFtickName, 'event) pnfun"
begin
  definition "PNfun :: (RDFtickName, 'event) pnfun == RDFtickfun"
end
  
declare Set_RDFtickfun_def [simp]


(*********************************************************
              DFtick lemma
 *********************************************************)

lemma guardedfun_DFtick[simp]:
      "guardedfun DFtickfun"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp_all)

lemma guardedfun_RDFtick[simp]:
      "guardedfun RDFtickfun"
apply (simp add: guardedfun_def)
apply (rule allI)
apply (induct_tac p)
apply (simp)
apply (rule allI)
apply (induct_tac n)
apply (simp_all)
done

(* -------------------------------------------------*
 |                                                  |
 |  syntactical approach --> semantical approach    |
 |                                                  |
 * -------------------------------------------------*)

(*** sub ***)

lemma DFtick_is_DeadlockFree:
  "(($DFtick) :: (DFtickName, 'event) proc) isDeadlockFree"
apply (simp add: DeadlockFree_def)
apply (rule allI)
apply (induct_tac s rule: induct_trace)

(* base case *)
apply (simp)
apply (subgoal_tac 
  "((DFtickfun (DFtick))::(DFtickName, 'event) proc) =F 
   ($(DFtick)::(DFtickName, 'event) proc)")
apply (simp add: cspF_eqF_semantics)
apply (erule conjE)
apply (rotate_tac 1)
apply (drule sym)
apply (simp)
apply (rotate_tac 1)
apply (drule sym)
apply (simp (no_asm) add: in_failures)
apply (simp add: Evset_def)
apply (force)

apply (cspF_unwind)
apply (simp add: CPOmode_or_CMSmode_or_MIXmode)

apply (subgoal_tac 
  "failures (($DFtick)::(DFtickName, 'event) proc) MF = 
   failures ((DFtickfun DFtick)::(DFtickName, 'event) proc) MF")
apply (simp)
apply (rotate_tac -1)
apply (drule sym)
apply (simp (no_asm) add: in_failures)
apply (intro impI)
apply (simp add: in_failures)

apply (subgoal_tac 
  "(($DFtick)::(DFtickName, 'event) proc) =F
   ((DFtickfun DFtick)::(DFtickName, 'event) proc)")
apply (simp add: cspF_eqF_semantics)
apply (cspF_unwind)
apply (simp add: CPOmode_or_CMSmode_or_MIXmode)
done

(*** main ***)

lemma DFtick_DeadlockFree:
  "($DFtick :: (DFtickName, 'event) proc) <=F P ==> P isDeadlockFree"
apply (insert DFtick_is_DeadlockFree)
apply (simp add: DeadlockFree_def)
apply (simp add: cspF_refF_semantics)
apply (auto)
done

(* -------------------------------------------------*
 |                                                  |
 |  semantical approach --> syntactical approach    |
 |                                                  |
 * -------------------------------------------------*)

lemma traces_included_in_DFtick:
  "t :t traces ((FIX DFtickfun) (DFtick)) (fstF o MF)"
apply (induct_tac t rule: induct_trace)

 (* <> *)
 apply (simp)

 (* <Tick> *)
 apply (simp add: FIX_def)
 apply (simp add: in_traces)
 apply (rule_tac x="Suc 0" in exI)
 apply (simp add: FIXn_def)
 apply (simp add: Subst_procfun_prod_def)
 apply (simp add: in_traces)

 (* <Eva>^^^s *)
 apply (simp add: FIX_def)
 apply (simp add: in_traces)
 apply (erule disjE)

 apply (simp)
 apply (rule_tac x="Suc 0" in exI)
 apply (simp add: FIXn_def)
 apply (simp add: Subst_procfun_prod_def)
 apply (simp add: in_traces)

 apply (erule exE)
 apply (rule_tac x="Suc n" in exI)
 apply (simp add: FIXn_def)
 apply (simp add: Subst_procfun_prod_def)
 apply (simp add: in_traces)
done

lemma failures_included_in_DFtick_lm:
  "(X ~= UNIV | Tick : sett t) -->
   (t,X) :f failures ((FIX DFtickfun) (DFtick)) MF"
apply (induct_tac t rule: induct_trace)

 (* <> *)
apply (simp add: FIX_def)
apply (intro impI)
apply (simp add: in_failures)
apply (rule_tac x="Suc 0" in exI)
apply (simp add: FIXn_def)
apply (simp add: Subst_procfun_prod_def)
apply (simp add: in_failures)

apply (case_tac "EX x. x ~: X")
apply (elim exE)
apply (case_tac "x = Tick")
apply (simp)
apply (simp add: Evset_def)
apply (force)
apply (simp add: not_Tick_to_Ev)
apply (force)
apply (force)

 (* <Tick> *)
 apply (simp add: FIX_def)
apply (simp add: in_failures)
apply (rule_tac x="Suc 0" in exI)
apply (simp add: FIXn_def)
apply (simp add: Subst_procfun_prod_def)
apply (simp add: in_failures)

 (* <Eva>^^^s *)
apply (intro impI)
 apply (simp add: FIX_def)
apply (simp add: in_failures)
apply (erule exE)
apply (rule_tac x="Suc n" in exI)
apply (simp add: FIXn_def)
apply (simp add: Subst_procfun_prod_def)
apply (simp add: in_failures)
done

lemma failures_included_in_DFtick:
  "[| X ~= UNIV | Tick : sett t |] ==>
   (t,X) :f failures ((FIX DFtickfun) (DFtick)) MF"
by (simp add: failures_included_in_DFtick_lm)

lemma DeadlockFree_DFtick:
  "P isDeadlockFree ==> ($DFtick :: (DFtickName, 'event) proc) <=F P"
apply (rule cspF_rw_left)
apply (rule cspF_FIX)
prefer 2
apply (simp)
apply (simp add: CPOmode_or_CMSmode_or_MIXmode)
apply (simp add: cspF_refF_semantics)

apply (rule conjI)

(* trace *)
apply (simp add: subdomT_iff)
apply (simp add: traces_included_in_DFtick)

(* failures *)
apply (simp add: subsetF_iff)
apply (intro allI impI)
apply (rule failures_included_in_DFtick)
apply (simp add: DeadlockFree_def)
apply (drule_tac x="s" in spec)
apply (auto)
done


(* -------------------------------------------------*
 |                                                  |
 |  syntactical approach <--> semantical approach   |
 |                                                  |
 * -------------------------------------------------*)

theorem DeadlockFree_DFtick_ref:
  "P isDeadlockFree = (($DFtick:: (DFtickName, 'event) proc) <=F P)"
apply (rule)
apply (simp add: DeadlockFree_DFtick)
apply (simp add: DFtick_DeadlockFree)
done

(*================================================================*
 |                                                                |
 |                   n-replicted DF specification                 |
 |                                                                |
 *================================================================*)

(*******************************************************************
        relating function between DFtickName and Rep...
 *******************************************************************)

(*** ref1 ***)

primrec
  RepDF_to_DF :: "RDFtickName => 
                 (DFtickName, 'event) proc"
where
  "RepDF_to_DF (RDFtick) = ($DFtick)"

lemma RDFtick_DFtick_ref1_induct_lm:
  "(($DFtick)::(DFtickName, 'event) proc)
   <=F (NatDFtick n (($RDFtick)::(RDFtickName,'event)proc)) << RepDF_to_DF"
apply (induct_tac n)
apply (simp_all)
apply (rule cspF_Int_choice_right)
apply (rule cspF_rw_left)
apply (rule cspF_unwind)
apply (simp_all)
apply (simp add: CPOmode_or_CMSmode_or_MIXmode)
apply (simp)
done

lemma RDFtick_DFtick_ref1:
  "($DFtick :: (DFtickName, 'event) proc) <=F $RDFtick"
apply (rule cspF_fp_induct_right[of _ _ "RepDF_to_DF"])
apply (simp)
apply (simp add: CPOmode_or_CMSmode_or_MIXmode)
apply (simp)

apply (induct_tac p)
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_unwind)
apply (simp)
apply (simp add: CPOmode_or_CMSmode_or_MIXmode)
apply (simp)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_decompo)
apply (simp)

apply (rule cspF_Rep_int_choice_right)
apply (simp add: RDFtick_DFtick_ref1_induct_lm)
apply (simp)
done

(*** ref2 ***)

primrec
  DF_to_RepDF :: "DFtickName => 
                 (RDFtickName, 'event) proc"
where
  "DF_to_RepDF (DFtick) = ($RDFtick)"

lemma RDFtick_DFtick_ref2:
  "$RDFtick <=F ($DFtick :: (DFtickName, 'event) proc)"
apply (rule cspF_fp_induct_right[of _ _ "DF_to_RepDF"])
apply (simp)
apply (simp add: CPOmode_or_CMSmode_or_MIXmode)
apply (simp)

apply (induct_tac p)
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_unwind)
apply (simp)
apply (simp add: CPOmode_or_CMSmode_or_MIXmode)
apply (simp)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_decompo)
apply (simp)

apply (rule cspF_Rep_int_choice_left)
apply (rule_tac x="0" in exI)
apply (simp)
apply (simp)
done

(**************************** =F****************************)

lemma RDFtick_DFtick:
  "$RDFtick =F ($DFtick :: (DFtickName, 'event) proc)"
apply (simp add: cspF_eq_ref_iff)
apply (simp add: RDFtick_DFtick_ref1)
apply (simp add: RDFtick_DFtick_ref2)
done

(* ---------------------------------------------------*
 |                                                    |
 |  syntactical approach 2 <--> semantical approach   |
 |                                                    |
 * ---------------------------------------------------*)

theorem DeadlockFree_RDFtick_ref:
  "P isDeadlockFree = (($RDFtick :: (RDFtickName, 'event) proc) <=F P)"
apply (simp add: DeadlockFree_DFtick_ref)
apply (rule)
apply (rule cspF_rw_left)
apply (rule RDFtick_DFtick)
apply (simp)

apply (rule cspF_rw_left)
apply (rule RDFtick_DFtick[THEN cspF_sym])
apply (simp)
done

(* ------------------------------------------------------------------ *)

declare csp_prefix_ss_def[simp del]

end
