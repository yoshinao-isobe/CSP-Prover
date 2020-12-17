           (*-------------------------------------------*
            |  The Dining Mathematicians in CSP-Prover  |
            |               August 2004                 |
            |             December 2004 (modified)      |
            |             November 2005 (modified)      |
            |                March 2007 (modified)      |
            |                 July 2009 (modified)      |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory DM5_Spc_Imp
imports DM4_Spc_def
begin

(*****************************************************************

         1. proves lemma for Spc <=F Imp
         2.
         3. 
         4. 

 *****************************************************************)

(*** Back0_Back1 ***)

lemma Back0_Back1:
  "(Spcfun TH0_TH1)<<Spc_to_Imp <=F
   (Back0 -> ($TH0) |[CH0]| ($(VAR x)) |[CH1]| Back1 -> ($TH1))
   -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)
apply (cspF_step)+
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)

apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)
done

lemmas Back0_Back1_simp[simp] = Back0_Back1[simplified]

(*** Eat0_Back1 ***)

lemma Eat0_Back1: 
  "~ ODD x ==> 
   (Spcfun TH0_TH1)<<Spc_to_Imp <=F
   (Eat0 -> ($(EAT0 x)) |[CH0]| ($(VAR x)) |[CH1]| Back1 -> ($TH1)) 
      -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)
apply (cspF_step)+
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)

apply (cspF_simp)+
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)
done

lemmas Eat0_Back1_simp[simp] = Eat0_Back1[simplified]

(*** Back0_Eat1 ***)

lemma Back0_Eat1: 
  "ODD x
   ==> 
   (Spcfun TH0_TH1)<<Spc_to_Imp <=F    
   (Back0 -> ($TH0) |[CH0]| ($(VAR x)) |[CH1]| Eat1 -> ($(EAT1 x))) 
      -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)
apply (cspF_step)+
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)

apply (cspF_simp)+
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)
done

lemmas Back0_Eat1_simp[simp] = Back0_Eat1[simplified]

lemma EAT0_Back1: 
  "~ ODD x
   ==> 
   (Spcfun EAT0_TH1)<<Spc_to_Imp <=F
   (($(EAT0 x)) |[CH0]| ($(VAR x)) 
                      |[CH1]| Back1 -> ($TH1)) -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)
apply (cspF_step)+
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)

apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)
done

lemmas EAT0_Back1_simp[simp] = EAT0_Back1[simplified]

(*** Back0_EAT1 ***)

lemma Back0_EAT1:
  "ODD x
   ==> 
    (Spcfun TH0_EAT1)<<Spc_to_Imp <=F
   (Back0 -> ($TH0) |[CH0]| ($(VAR x)) |[CH1]| ($(EAT1 x)))
    -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)
apply (cspF_step)+
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)

apply (cspF_simp)+
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)
done

lemmas Back0_EAT1_simp[simp] = Back0_EAT1[simplified]

(*** Back0_TH1  ***)

(* declare SpcDef.simps [simp del] *)

lemma Back0_TH1:
  "(Spcfun TH0_TH1)<<Spc_to_Imp <=F
  (Back0 -> ($TH0) |[CH0]| ($(VAR x)) |[CH1]| ($TH1)) -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)
apply (rule cspF_Timeout_right)
apply (cspF_step)
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)+
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)

apply (case_tac "ODD x")
apply (cspF_simp)+
done

lemmas Back0_TH1_simp[simp] = Back0_TH1[simplified]

(*** TH0_Back1  ***)

lemma TH0_Back1:
  "(Spcfun TH0_TH1)<<Spc_to_Imp <=F
    (($TH0) |[CH0]| ($(VAR x)) |[CH1]| Back1 -> ($TH1)) -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)
apply (rule cspF_Timeout_right)
apply (cspF_step)
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)+
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)

apply (case_tac "ODD x")
apply (cspF_simp)+
done

lemmas TH0_Back1_simp[simp] = TH0_Back1[simplified]

(*** TH0_Eat1 ***)

lemma TH0_Eat1:
  "ODD x
   ==> 
   (Spcfun TH0_TH1)<<Spc_to_Imp <=F
   (($TH0) |[CH0]| ($(VAR x)) |[CH1]| Eat1 -> ($(EAT1 x))) 
    -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)+
apply (rule cspF_Timeout_right)
apply (cspF_step)
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)

apply (cspF_step_right)+
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)

apply (cspF_simp)+
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)
done

lemmas TH0_Eat1_simp[simp] = TH0_Eat1[simplified]

(*** Eat0_TH1 ***)

lemma Eat0_TH1:
  "~ ODD x
   ==> 
  (Spcfun TH0_TH1)<<Spc_to_Imp <=F
   (Eat0 -> ($(EAT0 x)) |[CH0]| ($(VAR x)) |[CH1]| ($TH1))
    -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)+
apply (rule cspF_Timeout_right)
apply (cspF_step)
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)

apply (cspF_step_right)+
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)

apply (cspF_simp)+
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)
done

lemmas Eat0_TH1_simp[simp] = Eat0_TH1[simplified]

(*** TH0_TH1 ***)

lemma TH0_TH1:
  "(Spcfun TH0_TH1)<<Spc_to_Imp <=F
    (($TH0) |[CH0]| ($(VAR x)) |[CH1]| ($TH1)) -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)
apply (rule)

apply (case_tac "ODD x")
apply (cspF_simp)+

apply (case_tac "ODD x")
apply (cspF_simp)+
done

lemmas TH0_TH1_simp[simp] = TH0_TH1[simplified]

(*** Back0_TH0_TH1 ***)

lemma Back0_TH0_WR1:
  "ODD x
    ==> 
        (Spcfun TH0_TH1)<<Spc_to_Imp <=F
        Back0 -> (($TH0) |[CH0]| ($(VAR (3 * x + 1))) |[CH1]| ($TH1))
         -- (CH0 Un CH1)"
apply (cspF_step)
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)+
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="(3 * x + 1)" in exI)
apply (simp)
done

lemmas Back0_TH0_WR1_simp[simp] = Back0_TH0_WR1[simplified]

(*** Back1_TH0_TH1 ***)

lemma Back1_TH0_WR1:
  "ODD x
    ==> 
        (Spcfun TH0_TH1)<<Spc_to_Imp <=F
        Back1 -> (($TH0) |[CH0]| ($(VAR (3 * x + 1))) |[CH1]| ($TH1))
         -- (CH0 Un CH1)"
apply (cspF_step)
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)+
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="(3 * x + 1)" in exI)
apply (simp)
done

lemmas Back1_TH0_WR1_simp[simp] = Back1_TH0_WR1[simplified]

(*** Back0_WR1 ***)

lemma Back0_WR1:
  "ODD x
   ==> 
    (Spcfun TH0_TH1)<<Spc_to_Imp <=F
   (Back0 -> ($TH0) |[CH0]| ($(VAR x)) 
                          |[CH1]| WR1 (3 * x + 1) -> ($TH1)) 
   -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)
apply (rule cspF_Timeout_right)
apply (cspF_step)
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)
done

lemmas Back0_WR1_simp[simp] = Back0_WR1[simplified]

(*** WR0_Back1 ***)

lemma WR0_Back1:
  "~ ODD x
   ==> 
    (Spcfun TH0_TH1)<<Spc_to_Imp <=F
   (WR0 (x div 2) -> ($TH0) |[CH0]| ($(VAR x)) |[CH1]| Back1 -> ($TH1)) 
       -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)
apply (rule cspF_Timeout_right)
apply (cspF_step)
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)
done

lemmas WR0_Back1_simp[simp] = WR0_Back1[simplified]

(*** TH0_WR1 ***)

lemma TH0_WR1:
  "ODD x
   ==> 
   (Spcfun TH0_TH1)<<Spc_to_Imp <=F
   (($TH0) |[CH0]| ($(VAR x)) |[CH1]| WR1 (3 * x + 1) -> ($TH1)) 
      -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)
apply (rule)
apply (cspF_simp fold_Imp_rules)+
done

lemmas TH0_WR1_simp[simp] = TH0_WR1[simplified]

(*** WR0_TH1 ***)

lemma WR0_TH1:
  "~ ODD x
   ==> 
   (Spcfun TH0_TH1)<<Spc_to_Imp <=F
   (WR0 (x div 2) -> ($TH0) |[CH0]| ($(VAR x)) |[CH1]| ($TH1))
     -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)
apply (rule)
apply (cspF_simp fold_Imp_rules)
done

lemmas WR0_TH1_simp[simp] = WR0_TH1[simplified]

(*** EAT0_TH1 ***)

lemma EAT0_TH1:
  "~ ODD x
   ==> 
   (Spcfun EAT0_TH1)<<Spc_to_Imp <=F
    (($(EAT0 x)) |[CH0]| ($(VAR x)) |[CH1]| ($TH1)) -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)
apply (rule cspF_Timeout_right)
apply (cspF_step)
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)
done

lemmas EAT0_TH1_simp[simp] = EAT0_TH1[simplified]

(*** TH0_EAT1 ***)

lemma TH0_EAT1:
  "ODD x
   ==> 
   (Spcfun TH0_EAT1)<<Spc_to_Imp <=F
    (($TH0) |[CH0]| ($(VAR x)) |[CH1]| ($(EAT1 x))) -- (CH0 Un CH1)"
apply (cspF_simp unfold_Imp_rules)
apply (rule cspF_Timeout_right)
apply (cspF_step)
apply (auto intro!: cspF_decompo_subset)
apply (cspF_simp)+
apply (rule cspF_Int_choice_left1)
apply (rule cspF_Int_choice_left2)
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="x" in exI)
apply (simp)
done

lemmas TH0_EAT1_simp[simp] = TH0_EAT1[simplified]

(*********************************************************
                  ALL n. Spc <=F Imp n
 *********************************************************)

lemma Spc_ref_Seq: "Spc <=F Imp n"
apply (simp add: Spc_def Imp_def)
apply (rule cspF_fp_induct_left[of _ Spc_to_Imp])
apply (simp)+

(*** body ***)
apply (rule cspF_Int_choice_left1)+
apply (rule cspF_Rep_int_choice_left)
apply (simp)
apply (rule_tac x="n" in exI)
apply (simp)

apply (induct_tac p)
apply (auto)
done

end
