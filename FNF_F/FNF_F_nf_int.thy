           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  April 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory FNF_F_nf_int
imports FNF_F_nf_def
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*  The following simplification rules are deleted in this theory file *)
(*       P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))        *)
(* Isabelle 2017 *)
declare if_split  [split del]

(*****************************************************************

         1. full sequentialisation for Rep_int_choice
         2. 
         3. 

 *****************************************************************)

(*============================================================*
 |                                                            |
 |                    Rep_int_choice                          |
 |                                                            |
 *============================================================*)

definition
  fnfF_Rep_int_choice_step ::
  "'a sets_nats =>
   ('a aset_anat => 'a set) =>
   ('a aset_anat => 'a set set) =>
   ('a => ('p,'a) proc) =>
   ('a aset_anat => ('p,'a) proc) => ('p,'a) proc"

  where
  fnfF_Rep_int_choice_step_def:
    "fnfF_Rep_int_choice_step == (%X Af Ysf Pf Qf. 
  ((? :(Union {(Af x)|x. x: sumset X}) -> Pf)
    [+] (if (EX x: sumset X. Qf x = SKIP) then SKIP else DIV))
   |~| !set Y:(fnfF_set_completion (Union {(Af x)|x. x: sumset X})
                                   (Union {(Ysf x)|x. x : sumset X})) .. (? a:Y -> DIV))"

primrec
  fnfF_Rep_int_choice ::
  "nat => 'a sets_nats =>
     ('a aset_anat => ('p,'a) proc) => ('p,'a) proc"
where
  "fnfF_Rep_int_choice 0 = (%X SPf. NDIV)"

 |"fnfF_Rep_int_choice (Suc n) = (%C SPf. 
   if (ALL c: sumset C. SPf c : fnfF_proc) 
   then
   fnfF_Rep_int_choice_step C 
      (%c. (fnfF_A (SPf c)))
      (%c. (fnfF_Ys (SPf c)))
      (%a. (if a:Union {(fnfF_A (SPf c)) |c. c : sumset C}
            then fnfF_Rep_int_choice n {c:C. a : (fnfF_A (SPf c))}s
                                       (%c. (fnfF_Pf (SPf c) a))
            else DIV))
      (%c. (fnfF_Q (SPf c)))
   else 
      ((!! :C .. SPf) |. Suc n))"

syntax
  "_fnfF_Rep_int_choice" :: 
      "'a sets_nats => nat => ('a aset_anat => ('p,'a) proc) => ('p,'a) proc"
                                               ("(1!! :_ ..[_] /_)" [900,0,68] 68) 
  "@fnfF_Rep_int_choice":: 
      "pttrn => 'a sets_nats => nat => ('p,'a) proc => ('p,'a) proc"  
                               ("(1!! _:_ ..[_] /_)" [900,900,0,68] 68)

translations
  "!! :C ..[n] SPf"  == "CONST fnfF_Rep_int_choice n C SPf"
  "!! c:C ..[n] P"   == "!! :C ..[n] (%c. P)"

declare fnfF_Rep_int_choice.simps [simp del]

(*===========================================================*
 |                      in fnfF_rest                         |
 *===========================================================*)

lemma fnfF_Rep_int_choice_in_lm:
  "ALL C SPf.
   (ALL c: sumset C. SPf c : fnfF_proc) -->
    !! :C ..[n] SPf : fnfF_proc"
apply (induct_tac n)
apply (simp add: fnfF_Rep_int_choice.simps)

apply (intro impI allI)
apply (simp add: fnfF_Rep_int_choice.simps)
apply (simp add: fnfF_Rep_int_choice_step_def)
apply (rule fnfF_proc.intros)

(* set *)
apply (rule allI)
apply (simp)
apply (case_tac "EX x. (EX xa. x = fnfF_A (SPf xa) & xa : sumset C) & a : x")
apply (simp)
apply (drule_tac x="{c : C. a : fnfF_A (SPf c)}s" in spec)
apply (drule_tac x="(%c. fnfF_Pf (SPf c) a)" in spec)
apply (drule mp)
apply (rule ballI)
apply (simp)
apply (elim conjE exE bexE)
apply (simp)

apply (rule fnfF_Pf_A)
apply (simp)
apply (simp)
apply (simp)

apply (simp (no_asm_simp))
apply (simp)

 apply (rule fnfF_set_completion_Union_subset)
 apply (rule subsetI)
 apply (simp)
 apply (elim conjE exE bexE)
 apply (simp)
 apply (drule_tac x="xa" in bspec, simp)
 apply (erule fnfF_proc.cases)
 apply (simp)
 apply (rule_tac x="fnfF_A (SPf xa)" in exI)
 apply (simp)
 apply (rule conjI)
 apply (rule_tac x="xa" in exI)
 apply (simp)
 apply (auto)
  apply (case_tac "EX x: sumset C. fnfF_Q (SPf x) = SKIP")
  apply (simp_all)
done

(*------------------------------------*
 |                 in                 |
 *------------------------------------*)

lemma fnfF_Rep_int_choice_in:
  "(ALL c: sumset C. SPf c : fnfF_proc) ==>
    !! :C ..[n] SPf : fnfF_proc"
apply (simp add: fnfF_Rep_int_choice_in_lm)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)
(*-----------------------------------------*
 |    convenient lemma for subexpresions   |
 *-----------------------------------------*)

lemma fnfF_Rep_int_choice_step_subexp:
  "[| ALL a:(Union {(Af2 c)|c. c: sumset C}). Pf1 a =F Pf2 a ;
      ALL c: sumset C. Af1 c = Af2 c ; 
      ALL c: sumset C. Ysf1 c = Ysf2 c ; 
      ALL c: sumset C. Qf1 c = Qf2 c ;
      ALL c: sumset C. Union (Ysf2 c) <= (Af2 c) |]
   ==>
      fnfF_Rep_int_choice_step C Af1 Ysf1 Pf1 Qf1
   =F fnfF_Rep_int_choice_step C Af2 Ysf2 Pf2 Qf2"
apply (simp add: fnfF_Rep_int_choice_step_def)

apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (rule cspF_decompo)

(* 1 *)
apply (subgoal_tac
  "{(Af1 c)|c. c : sumset C} = {(Af2 c) |c. c : sumset C}", simp)
apply (blast)

(* 2 *)
 apply (simp)
 apply (elim conjE exE)
 apply (simp)
 apply (drule_tac x="Af2 xa" in spec)
 apply (drule mp)
 apply (rule_tac x="xa" in exI)
 apply (simp)
 apply (simp)

(* 3 *)
apply (simp)

(* 4 *)
apply (rule cspF_decompo)
apply (subgoal_tac
  "{(Af1 c)|c. c : sumset C} = {(Af2 c)|c. c : sumset C}")
apply (subgoal_tac
  "{(Ysf1 c)|c. c : sumset C} = {(Ysf2 c)|c. c : sumset C}")
apply (simp)
apply (erule rem_asmE)
apply (blast)
apply (erule rem_asmE)
apply (blast)
apply (simp)
done

(*------------------------------------*
 |         one step equality          |
 *------------------------------------*)

lemma cspF_fnfF_Rep_int_choice_one_step:
  "[| ALL c: sumset C. Union (Ysf c) <= (Af c) ;
      ALL c: sumset C. Qf c = SKIP | Qf c = DIV |] ==>
   !! c:C .. (? :(Af c) -> Pff c [+] Qf c 
             |~| !set Y:Ysf c .. ? a:Y -> DIV)
   =F
   fnfF_Rep_int_choice_step C Af Ysf 
          (%a. (!! c:{c : C. a : Af c}s .. Pff c a)) Qf"
apply (rule cspF_rw_left)
apply (rule cspF_dist)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_Rep_int_choice_Ext_Dist)
apply (simp)
apply (rule cspF_Rep_int_choice_set_Ext_pre_choice_DIV)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_decompo)
apply (rule cspF_Rep_int_choice_input_set)
apply (rule cspF_SKIP_DIV_Rep_int_choice)
apply (force)
apply (rule cspF_reflex)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (rule cspF_Rep_int_choice_input_Dist)
(* Isabelle 2017 *)
apply (simp split: if_split)
apply (rule cspF_reflex)

apply (simp add: fnfF_Rep_int_choice_step_def)
apply (rule cspF_input_Rep_int_choice_set_subset)

 apply (rule fnfF_set_completion_subset)

 apply (rule ballI)
 apply (simp add: fnfF_set_completion_def)
 apply (subgoal_tac 
   "Union (Union {(Ysf c)|c. c : sumset C}) <= Union {(Af c)|c. c : sumset C}")
 apply (blast)
 apply (auto)
done

(*------------------------------------*
 |              induction             |
 *------------------------------------*)

lemma cspF_fnfF_Rep_int_choice_eqF_lm:
  "ALL C SPf.
   (!! :C .. SPf) |. n =F !! :C ..[n] SPf"
apply (induct_tac n)

(* base *)
apply (intro allI)
apply (simp add: fnfF_Rep_int_choice.simps)
apply (rule cspF_rw_left)
apply (rule cspF_Depth_rest_Zero)
apply (rule cspF_NDIV_eqF)

(* step *)
apply (intro allI)
apply (case_tac "(ALL c: sumset C. SPf c : fnfF_proc)")
apply (subgoal_tac "(ALL c: sumset C. SPf c : fnfF_proc)")

apply (erule ALL_fnfF_procE)
apply (elim conjE exE)
apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (subgoal_tac
  "(!! u:C .. 
             (if u : sumset C
              then ? :Af u -> Pff u [+] Qf u 
                    |~| !set Y:Ysf u .. ? a:Y -> DIV
              else SPf u)) 
   =F (!! u:C .. (? :Af u -> Pff u [+] Qf u 
                    |~| !set Y:Ysf u .. ? a:Y -> DIV))")
apply (assumption)
 apply (rule cspF_decompo)
 apply (simp)
 apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_Dist_nonempty)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_fnfF_Depth_rest_dist)
apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_fnfF_Rep_int_choice_one_step)
apply (simp)
apply (simp)

apply (simp add: fnfF_Rep_int_choice.simps)
apply (rule fnfF_Rep_int_choice_step_subexp)

(* Pf *)
apply (rule ballI)
apply (drule_tac x=
   "{c : C.
             a : fnfF_A
                  (if c : sumset C
                   then ? :Af c -> Pff c [+] Qf c 
                         |~| !set Y:Ysf c .. ? a:Y -> DIV
                   else SPf c)}s" in spec)
apply (drule_tac x=
   "(%c. fnfF_Pf
                  (if c : sumset C
                   then ? :Af c -> Pff c [+] Qf c 
                         |~| !set Y:Ysf c .. ? a:Y -> DIV
                   else SPf c)
                  a)" in spec)

apply (rotate_tac -1)
apply (erule cspF_symE)
apply (rule cspF_rw_right)
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_Dist)

apply (rule cspF_decompo)
apply (simp)
apply (rule sub_sumset_eq)
apply (simp_all)
apply (subgoal_tac "~(ALL c: sumset C. SPf c : fnfF_proc)")
apply (simp (no_asm_simp) add: fnfF_Rep_int_choice.simps)
apply (simp)
done

(*------------------------------------*
 |                 eqF                |
 *------------------------------------*)

lemma cspF_fnfF_Rep_int_choice_eqF:
  "(!! :C .. SPf) |. n =F (!! :C ..[n] SPf)"
apply (simp add: cspF_fnfF_Rep_int_choice_eqF_lm)
done

(*------------------------*
 |     auxiliary laws     |
 *------------------------*)

lemma cspF_fnfF_Rep_int_choice_Depth_rest:
  "(!! :C ..[n] SPf) |. n =F (!! :C ..[n] SPf)"
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_fnfF_Rep_int_choice_eqF[THEN cspF_sym])
apply (rule cspF_rw_left)
apply (rule cspF_Depth_rest_min)
apply (simp)
apply (rule cspF_fnfF_Rep_int_choice_eqF)
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
