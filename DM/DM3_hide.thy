           (*-------------------------------------------*
            |  The Dining Mathematicians in CSP-Prover  |
            |               August 2004                 |
            |             December 2004 (modified)      |
            |             November 2005 (modified)      |
            |                March 2007  (modified)     |
            |                April 2020  (modified)     |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory DM3_hide
imports DM2_para
begin

(*****************************************************************

         1. expands hiding operators in Imp
         2.
         3. 
         4. 

 *****************************************************************)

(******************** Hiding ********************)

(*** Back0 VAR Back1 HIDE ***)

lemma Back0_VAR_Back1_HIDE: 
  "(Back0 -> ($TH0) |[CH0]| ($(VAR n)) 
                                        |[CH1]| Back1 -> ($TH1))
                 -- (CH0 Un CH1)
   =F
   
        Back0 -> ((($TH0) |[CH0]| ($(VAR n)) |[CH1]| Back1 -> ($TH1))
                     -- (CH0 Un CH1))
        [+]
        Back1 -> ((Back0 -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
                     -- (CH0 Un CH1))"
apply (cspF_simp unfold_Imp_rules24)
apply (cspF_step)+
apply (auto)
apply (cspF_simp fold_Imp_rules24)+
done

lemmas Back0_VAR_Back1_HIDE_simp = Back0_VAR_Back1_HIDE[simplified]
lemmas unfold_Imp_rules25 = unfold_Imp_rules24 Back0_VAR_Back1_HIDE_simp
lemmas fold_Imp_rules25 = fold_Imp_rules24 Back0_VAR_Back1_HIDE_simp[THEN cspF_sym]

(*** Eat0 VAR Back1 HIDE ***)

lemma Eat0_VAR_Back1_HIDE: 
  "EVEN n ==>
   (Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| Back1 -> ($TH1))
                 -- (CH0 Un CH1)
   =F
   
        Eat0 -> ((($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| Back1 -> ($TH1))
                 -- (CH0 Un CH1))
        [+]
        Back1 -> ((Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
                 -- (CH0 Un CH1))"
apply (cspF_simp unfold_Imp_rules25)
apply (cspF_step)+
apply (auto)
apply (cspF_simp fold_Imp_rules25)+
done

lemmas Eat0_VAR_Back1_HIDE_simp = Eat0_VAR_Back1_HIDE[simplified]
lemmas unfold_Imp_rules26 = unfold_Imp_rules25 Eat0_VAR_Back1_HIDE_simp
lemmas fold_Imp_rules26 = fold_Imp_rules25 Eat0_VAR_Back1_HIDE_simp[THEN cspF_sym]

(*** Back0 VAR Eat1 HIDE ***)

lemma Back0_VAR_Eat1_HIDE: 
  "ODD n ==>
   (Back0 -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| Eat1 -> ($(EAT1 n)))
                 -- (CH0 Un CH1)
   =F
        Eat1 -> ((Back0 -> ($TH0) |[CH0]| ($(VAR n)) 
                                        |[CH1]| ($(EAT1 n)))
                 -- (CH0 Un CH1))
        [+]
        Back0 -> ((($TH0) |[CH0]| ($(VAR n)) 
                                |[CH1]| Eat1 -> ($(EAT1 n)))
                 -- (CH0 Un CH1))"
apply (cspF_simp unfold_Imp_rules26)
apply (cspF_step)+
apply (auto)
apply (cspF_simp fold_Imp_rules26)+
done

lemmas Back0_VAR_Eat1_HIDE_simp = Back0_VAR_Eat1_HIDE[simplified]
lemmas unfold_Imp_rules27 = unfold_Imp_rules26 Back0_VAR_Eat1_HIDE_simp
lemmas fold_Imp_rules27 = fold_Imp_rules26 Back0_VAR_Eat1_HIDE_simp[THEN cspF_sym]

(*** EAT0 VAR Back1 HIDE ***)

lemma EAT0_VAR_Back1_HIDE: 
  "EVEN n ==>
   (($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| Back1 -> ($TH1))
                 -- (CH0 Un CH1)
   =F
        End0 -> ((WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n)) 
                                                |[CH1]| Back1 -> ($TH1))
                 -- (CH0 Un CH1))
        [+]
        Back1 -> ((($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
                 -- (CH0 Un CH1))"
apply (cspF_simp unfold_Imp_rules27)
apply (cspF_step)+
apply (auto)
apply (cspF_simp fold_Imp_rules27)+
done

lemmas EAT0_VAR_Back1_HIDE_simp = EAT0_VAR_Back1_HIDE[simplified]
lemmas unfold_Imp_rules28 = unfold_Imp_rules27 EAT0_VAR_Back1_HIDE_simp
lemmas fold_Imp_rules28 = fold_Imp_rules27 EAT0_VAR_Back1_HIDE_simp[THEN cspF_sym]

(*** Back0 VAR EAT1 HIDE ***)

lemma Back0_VAR_EAT1_HIDE: 
  "ODD n ==>
   (Back0 -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($(EAT1 n)))
                 -- (CH0 Un CH1)
   =F
        End1 -> ((Back0 -> ($TH0) |[CH0]| ($(VAR n)) 
                                 |[CH1]| WR1 (3 * n + 1) -> ($TH1))
                  -- (CH0 Un CH1))
        [+]
        Back0 -> ((($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($(EAT1 n)))
                  -- (CH0 Un CH1))"
apply (cspF_simp unfold_Imp_rules28)
apply (cspF_step)+
apply (auto)
apply (cspF_simp fold_Imp_rules28)+
done

lemmas Back0_VAR_EAT1_HIDE_simp = Back0_VAR_EAT1_HIDE[simplified]
lemmas unfold_Imp_rules29 = unfold_Imp_rules28 Back0_VAR_EAT1_HIDE_simp
lemmas fold_Imp_rules29 = fold_Imp_rules28 Back0_VAR_EAT1_HIDE_simp[THEN cspF_sym]

(**************************)
(*** Back0 VAR TH1 HIDE ***)

lemma Back0_VAR_TH1_HIDE: 
  "(Back0 -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
                 -- (CH0 Un CH1)
   =F
        Back0 -> ((($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
                  -- (CH0 Un CH1))
        [>
        IF ODD n 
        THEN ((Back0 -> ($TH0) |[CH0]| ($(VAR n)) 
                                     |[CH1]| Eat1 -> ($(EAT1 n)))
              -- (CH0 Un CH1))
        ELSE ((Back0 -> ($TH0) |[CH0]| ($(VAR n))
                                     |[CH1]| Back1 -> ($TH1))
              -- (CH0 Un CH1))"
apply (cspF_simp unfold_Imp_rules29)
apply (cspF_step_left)+
apply (cspF_step_right)+
apply (rule cspF_decompo)+
apply (auto)

apply (subgoal_tac "{Back0, (RD1 n)} Int (CH0 Un CH1) = {(RD1 n)}")
apply (case_tac "ODD n")
apply (cspF_simp fold_Imp_rules29)+
done

lemmas Back0_VAR_TH1_HIDE_simp = Back0_VAR_TH1_HIDE[simplified]
lemmas unfold_Imp_rules30 = unfold_Imp_rules29 Back0_VAR_TH1_HIDE_simp
lemmas fold_Imp_rules30 = fold_Imp_rules29 Back0_VAR_TH1_HIDE_simp[THEN cspF_sym]

(**************************)
(*** TH0 VAR Back1 HIDE ***)

lemma TH0_VAR_Back1_HIDE: 
  "(($TH0) |[CH0]| ($(VAR n)) |[CH1]| Back1 -> ($TH1))
                 -- (CH0 Un CH1)
   =F
        Back1 -> ((($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
                  -- (CH0 Un CH1))
        [>
        IF EVEN n
        THEN ((Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n))
                                         |[CH1]| Back1 -> ($TH1))
              -- (CH0 Un CH1))
        ELSE ((Back0 -> ($TH0) |[CH0]| ($(VAR n))
                                     |[CH1]| Back1 -> ($TH1))
              -- (CH0 Un CH1))"
apply (cspF_simp unfold_Imp_rules30)
apply (cspF_step_left)+
apply (cspF_step_right)+
apply (rule cspF_decompo)+
apply (auto)
apply (subgoal_tac "{Back1, (RD0 n)} Int (CH0 Un CH1) = {(RD0 n)}")
apply (case_tac "ODD n")
apply (cspF_simp fold_Imp_rules30)+
done

lemmas TH0_VAR_Back1_HIDE_simp = TH0_VAR_Back1_HIDE[simplified]
lemmas unfold_Imp_rules31 = unfold_Imp_rules30 TH0_VAR_Back1_HIDE_simp
lemmas fold_Imp_rules31 = fold_Imp_rules30 TH0_VAR_Back1_HIDE_simp[THEN cspF_sym]

(*** Eat0 VAR TH1 HIDE ***)

lemma Eat0_VAR_TH1_HIDE: 
  "EVEN n ==>
   (Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
                  -- (CH0 Un CH1)
   =F
        Eat0 -> ((($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
                  -- (CH0 Un CH1))
        [>
        (Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| Back1 -> ($TH1))
         -- (CH0 Un CH1)"
apply (cspF_simp_left unfold_Imp_rules31)
apply (cspF_step_left)+
apply (cspF_step_right)+
apply (rule cspF_decompo)+
apply (auto)
done

lemmas Eat0_VAR_TH1_HIDE_simp = Eat0_VAR_TH1_HIDE[simplified]
lemmas unfold_Imp_rules32 = unfold_Imp_rules31 Eat0_VAR_TH1_HIDE_simp
lemmas fold_Imp_rules32 = fold_Imp_rules31 Eat0_VAR_TH1_HIDE_simp[THEN cspF_sym]

(*** TH0 VAR Eat1 HIDE ***)

lemma TH0_VAR_Eat1_HIDE: 
  "ODD n ==>
   (($TH0) |[CH0]| ($(VAR n)) |[CH1]| Eat1 -> ($(EAT1 n)))
                 -- (CH0 Un CH1)
   =F
        Eat1 -> ((($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($(EAT1 n)))
                 -- (CH0 Un CH1))
        [>
        (Back0 -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| Eat1 -> ($(EAT1 n)))
                 -- (CH0 Un CH1)"
apply (cspF_simp_left unfold_Imp_rules32)
apply (cspF_step_left)+
apply (cspF_step_right)+
apply (rule cspF_decompo)+
apply (auto)
done

lemmas TH0_VAR_Eat1_HIDE_simp = TH0_VAR_Eat1_HIDE[simplified]
lemmas unfold_Imp_rules33 = unfold_Imp_rules32 TH0_VAR_Eat1_HIDE_simp
lemmas fold_Imp_rules33 = fold_Imp_rules32 TH0_VAR_Eat1_HIDE_simp[THEN cspF_sym]

(*** EAT0 VAR TH1 HIDE ***)

lemma EAT0_VAR_TH1_HIDE: 
  "EVEN n ==>
   (($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
                 -- (CH0 Un CH1)
   =F
        End0 -> ((WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n)) 
                                                |[CH1]| ($TH1))
                 -- (CH0 Un CH1))
        [>
        (($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| Back1 -> ($TH1))
         -- (CH0 Un CH1)"
apply (cspF_simp_left unfold_Imp_rules33)
apply (cspF_step_left)+
apply (cspF_step_right)+
apply (rule cspF_decompo)+
apply (auto)
done

lemmas EAT0_VAR_TH1_HIDE_simp = EAT0_VAR_TH1_HIDE[simplified]
lemmas unfold_Imp_rules34 = unfold_Imp_rules33 EAT0_VAR_TH1_HIDE_simp
lemmas fold_Imp_rules34 = fold_Imp_rules33 EAT0_VAR_TH1_HIDE_simp[THEN cspF_sym]

(*** TH0 VAR EAT1 HIDE ***)

lemma TH0_VAR_EAT1_HIDE: 
  "ODD n ==>
   (($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($(EAT1 n)))
                 -- (CH0 Un CH1)
   =F
        End1 -> ((($TH0) |[CH0]| ($(VAR n)) 
                               |[CH1]| WR1 (3 * n + 1) -> ($TH1))
                 -- (CH0 Un CH1))
        [>
        (Back0 -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($(EAT1 n)))
         -- (CH0 Un CH1)"
apply (cspF_simp_left unfold_Imp_rules34)
apply (cspF_step_left)+
apply (cspF_step_right)+
apply (rule cspF_decompo)+
apply (auto)
done

lemmas TH0_VAR_EAT1_HIDE_simp = TH0_VAR_EAT1_HIDE[simplified]
lemmas unfold_Imp_rules35 = unfold_Imp_rules34 TH0_VAR_EAT1_HIDE_simp
lemmas fold_Imp_rules35 = fold_Imp_rules34 TH0_VAR_EAT1_HIDE_simp[THEN cspF_sym]

(*** TH0 VAR TH1 HIDE step 1 ***)

lemma TH0_VAR_TH1_HIDE:
  "(($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
         -- (CH0 Un CH1)
   =F 
       (IF EVEN n
        THEN ((Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
              -- (CH0 Un CH1))
        ELSE ((Back0 -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
              -- (CH0 Un CH1)))
        |~|
       (IF ODD n 
        THEN ((($TH0) |[CH0]| ($(VAR n)) |[CH1]| Eat1 -> ($(EAT1 n)))
              -- (CH0 Un CH1))
        ELSE ((($TH0) |[CH0]| ($(VAR n)) |[CH1]| Back1 -> ($TH1))
              -- (CH0 Un CH1)))"
apply (cspF_simp_left unfold_Imp_rules35)
apply (cspF_step_left)+
apply (rule cspF_ref_eq)

 (* <= *)
 apply (rule)
  apply (rule cspF_Rep_int_choice_left)
  apply (rule_tac x="RD0 n" in exI)
  apply (case_tac "ODD n")
  apply (simp)
  apply (cspF_simp)+

  apply (rule cspF_Rep_int_choice_left)
  apply (rule_tac x="RD1 n" in exI)
  apply (case_tac "ODD n")
  apply (simp)
  apply (cspF_simp)+

(* => *)
 apply (subgoal_tac "{(RD0 n), (RD1 n)} Int (CH0 Un CH1) = {(RD0 n), (RD1 n)}")
 apply (auto)

  apply (rule cspF_Int_choice_left1)
  apply (case_tac "ODD n")
  apply (simp)
  apply (cspF_simp)+

  apply (rule cspF_Int_choice_left2)
  apply (case_tac "ODD n")
  apply (simp)
  apply (cspF_simp)+
done

lemmas TH0_VAR_TH1_HIDE_simp = TH0_VAR_TH1_HIDE[simplified]
lemmas unfold_Imp_rules36 = unfold_Imp_rules35 TH0_VAR_TH1_HIDE_simp
lemmas fold_Imp_rules36 = fold_Imp_rules35 TH0_VAR_TH1_HIDE_simp[THEN cspF_sym]

(*** WR0 VAR Back1 HIDE ***)

lemma WR0_VAR_Back1_HIDE: 
  "EVEN n ==>
   (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| Back1 -> ($TH1))
                 -- (CH0 Un CH1)
   =F
        Back1 -> ((WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n))
                                                 |[CH1]| ($TH1))
                  -- (CH0 Un CH1))
        [>
        (($TH0) |[CH0]| ($(VAR (n div 2))) |[CH1]| Back1 -> ($TH1))
        -- (CH0 Un CH1)"
apply (cspF_simp_left unfold_Imp_rules36)
apply (cspF_step_left)+
apply (cspF_step_right)+
apply (rule cspF_decompo)+
apply (auto)
done

lemmas WR0_VAR_Back1_HIDE_simp = WR0_VAR_Back1_HIDE[simplified]
lemmas unfold_Imp_rules37 = unfold_Imp_rules36 WR0_VAR_Back1_HIDE_simp
lemmas fold_Imp_rules37 = fold_Imp_rules36 WR0_VAR_Back1_HIDE_simp[THEN cspF_sym]

(*** Back0 VAR WR1 HIDE ***)

lemma Back0_VAR_WR1_HIDE: 
  "ODD n ==>
   (Back0 -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| WR1 (3 * n + 1) -> ($TH1))
                 -- (CH0 Un CH1)
   =F
        Back0 -> ((($TH0) |[CH0]| ($(VAR n)) 
                                |[CH1]| WR1 (3 * n + 1) -> ($TH1))
                 -- (CH0 Un CH1))
        [>
        (Back0 -> ($TH0) |[CH0]| ($(VAR (3 * n + 1))) |[CH1]| ($TH1))
        -- (CH0 Un CH1)"
apply (cspF_simp_left unfold_Imp_rules37)
apply (cspF_step_left)+
apply (cspF_step_right)+
apply (rule cspF_decompo)+
apply (auto)
done

lemmas Back0_VAR_WR1_HIDE_simp = Back0_VAR_WR1_HIDE[simplified]
lemmas unfold_Imp_rules38 = unfold_Imp_rules37 Back0_VAR_WR1_HIDE_simp
lemmas fold_Imp_rules38 = fold_Imp_rules37 Back0_VAR_WR1_HIDE_simp[THEN cspF_sym]

(*** WR0 VAR TH1 HIDE ***)

lemma WR0_VAR_TH1_HIDE: 
  "EVEN n ==>
   (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
                -- (CH0 Un CH1)
   =F
        (($TH0)  |[CH0]| ($(VAR (n div 2))) |[CH1]| ($TH1))
         -- (CH0 Un CH1)
        |~|
        (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n))
                                       |[CH1]| Back1 -> ($TH1))
        -- (CH0 Un CH1)"
apply (cspF_simp_left unfold_Imp_rules38)
apply (cspF_step_left)+
apply (rule cspF_ref_eq)

 (* <= *)
 apply (rule)
  apply (rule cspF_Rep_int_choice_left)
  apply (rule_tac x="WR0 (n div 2)" in exI)
  apply (simp, cspF_simp)  (* modified for Isabelle2020 *)
                           (* "+" is removed *)

  apply (rule cspF_Rep_int_choice_left)
  apply (rule_tac x="RD1 n" in exI)
  apply (simp, cspF_simp)

(* => *)
 apply (subgoal_tac "{(WR0 (n div 2)), (RD1 n)} Int (CH0 Un CH1) =
                     {(WR0 (n div 2)), (RD1 n)}")
 apply (auto)

  apply (rule cspF_Int_choice_left1)
  apply (cspF_simp)+
  apply (rule cspF_Int_choice_left2)
  apply (cspF_simp)+
done

lemmas WR0_VAR_TH1_HIDE_simp = WR0_VAR_TH1_HIDE[simplified]
lemmas unfold_Imp_rules39 = unfold_Imp_rules38 WR0_VAR_TH1_HIDE_simp
lemmas fold_Imp_rules39 = fold_Imp_rules38 WR0_VAR_TH1_HIDE_simp[THEN cspF_sym]

(*** TH0 VAR WR1 HIDE ***)

lemma TH0_VAR_WR1_HIDE: 
  "ODD n ==>
   (($TH0) |[CH0]| ($(VAR n)) |[CH1]| WR1 (3 * n + 1) -> ($TH1))
                  -- (CH0 Un CH1)
   =F
        (($TH0) |[CH0]| ($(VAR (3 * n + 1))) |[CH1]| ($TH1))
        -- (CH0 Un CH1)
        |~|
        (Back0 -> ($TH0) |[CH0]| ($(VAR n))
                               |[CH1]| WR1 (3 * n + 1) -> ($TH1))
        -- (CH0 Un CH1)"
apply (cspF_simp_left unfold_Imp_rules39)
apply (cspF_step_left)+
apply (rule cspF_ref_eq)

 (* <= *)
 apply (rule)
  apply (rule cspF_Rep_int_choice_left)
  apply (rule_tac x="WR1 (3 * n + 1)" in exI)
  apply (simp, cspF_simp)
  apply (rule cspF_Rep_int_choice_left)
  apply (rule_tac x="RD0 n" in exI)
  apply (simp, cspF_simp)

(* => *)
 apply (subgoal_tac "{(WR1 (3 * n + 1)), (RD0 n)} Int (CH0 Un CH1) =
                     {(WR1 (3 * n + 1)), (RD0 n)}")
 apply (auto)

  apply (rule cspF_Int_choice_left1)
  apply (cspF_simp)+
  apply (rule cspF_Int_choice_left2)
  apply (cspF_simp)+
done

lemmas TH0_VAR_WR1_HIDE_simp = TH0_VAR_WR1_HIDE[simplified]
lemmas unfold_Imp_rules = unfold_Imp_rules39 TH0_VAR_WR1_HIDE_simp
lemmas fold_Imp_rules = fold_Imp_rules39 TH0_VAR_WR1_HIDE_simp[THEN cspF_sym]

end
