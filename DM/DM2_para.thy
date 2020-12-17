           (*-------------------------------------------*
            |  The Dining Mathematicians in CSP-Prover  |
            |               August 2004                 |
            |             December 2004 (modified)      |
            |             November 2005 (modified)      |
            |                March 2007  (modified)     |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory DM2_para
imports DM1_Imp_def
begin

(*****************************************************************

         1. expands parallel operators in Imp
         2.
         3. 
         4. 

 *****************************************************************)

(*** TH0 VAR step 1 ***)

lemma TH0_VAR: 
  "(($TH0) |[CH0]| ($(VAR n)))
   =F (? x:insert (RD0 n) (insert (RD1 n) (range WR1)) 
          -> IF (x : (range RD0) | x : (range WR0))
                THEN IF EVEN (getInt x) 
                     THEN (Eat0  -> ($(EAT0 n)) |[CH0]| ($(VAR n)))
                     ELSE (Back0 -> ($TH0) |[CH0]| ($(VAR n)))
                ELSE (($TH0) |[CH0]| ($(VAR (getInt x)))))"
apply (cspF_simp unfold_Imp_rules3)+
apply (cspF_step_left)+
apply (case_tac "EVEN n")
apply (auto)
apply (cspF_simp fold_Imp_rules3)+
done

lemmas TH0_VAR_simp = TH0_VAR[simplified]
lemmas unfold_Imp_rules4 = unfold_Imp_rules3 TH0_VAR_simp
lemmas fold_Imp_rules4 = fold_Imp_rules3 TH0_VAR_simp[THEN cspF_sym]

(*** TH0 VAR TH1 step 1 ***)

lemma TH0_VAR_TH1:
  "(($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
   =F
    ? x:{(RD0 n), (RD1 n)} 
      -> IF (x = RD0 n)
            THEN IF EVEN n
                 THEN (Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n)) 
                                                 |[CH1]| ($TH1))
                 ELSE (Back0 -> ($TH0)   |[CH0]| ($(VAR n)) 
                                               |[CH1]| ($TH1))
            ELSE IF ODD n
                 THEN (($TH0) |[CH0]| ($(VAR n)) 
                                    |[CH1]| Eat1 -> ($(EAT1 n)))
                 ELSE (($TH0) |[CH0]| ($(VAR n)) 
                                    |[CH1]| Back1 -> ($TH1))"
apply (cspF_simp unfold_Imp_rules4)
apply (cspF_step_left)
apply (case_tac "EVEN n")
apply (auto)
apply (cspF_simp fold_Imp_rules4)+
done

lemmas TH0_VAR_TH1_simp = TH0_VAR_TH1[simplified]
lemmas unfold_Imp_rules5 = unfold_Imp_rules4 TH0_VAR_TH1_simp
lemmas fold_Imp_rules5 = fold_Imp_rules4 TH0_VAR_TH1_simp[THEN cspF_sym]

(*** Eat0 VAR step 2 ***)

lemma Eat0_VAR: 
  " (Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n)))
   =F
    ? x:insert Eat0 (insert (RD1 n) (range WR1))
        -> IF (x = Eat0) 
              THEN (($(EAT0 n)) |[CH0]| ($(VAR n)))
              ELSE IF (x = RD1 n) 
                   THEN (Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n)))
                   ELSE (Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR (getInt x))))"
apply (cspF_simp unfold_Imp_rules5)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules5)+
done

lemmas Eat0_VAR_simp = Eat0_VAR[simplified]
lemmas unfold_Imp_rules6 = unfold_Imp_rules5 Eat0_VAR_simp
lemmas fold_Imp_rules6 = fold_Imp_rules5 Eat0_VAR_simp[THEN cspF_sym]

(*** Back0 VAR step 2 ***)

lemma Back0_VAR: 
  " (Back0 -> ($TH0) |[CH0]| ($(VAR n)))
   =F
    ? x:insert Back0 (insert (RD1 n) (range WR1))
        -> IF (x = Back0) 
              THEN (($TH0) |[CH0]| ($(VAR n)))
              ELSE IF (x = RD1 n)
                   THEN (Back0 -> ($TH0) |[CH0]| ($(VAR n)))
                   ELSE (Back0 -> ($TH0) |[CH0]| ($(VAR (getInt x))))"
apply (cspF_simp unfold_Imp_rules6)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules6)+
done

lemmas Back0_VAR_simp = Back0_VAR[simplified]
lemmas unfold_Imp_rules7 = unfold_Imp_rules6 Back0_VAR_simp
lemmas fold_Imp_rules7 = fold_Imp_rules6 Back0_VAR_simp[THEN cspF_sym]

(*** Eat0 VAR TH1 step 2 ***)

lemma Eat0_VAR_TH1: 
  "EVEN n ==>
    (Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
   =F
    ? x:{Eat0, (RD1 n)} 
      -> IF (x = Eat0)
            THEN (($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
            ELSE (Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n)) 
                                            |[CH1]| Back1 -> ($TH1))"
apply (cspF_simp unfold_Imp_rules7)
apply (cspF_step_left)
apply (auto)
apply (cspF_simp fold_Imp_rules7)+
done

lemmas Eat0_VAR_TH1_simp = Eat0_VAR_TH1[simplified]
lemmas unfold_Imp_rules8 = unfold_Imp_rules7 Eat0_VAR_TH1_simp
lemmas fold_Imp_rules8 = fold_Imp_rules7 Eat0_VAR_TH1_simp[THEN cspF_sym]

(****************************)
(*** Back0 VAR TH1 step 2 ***)

lemma Back0_VAR_TH1: 
  " (Back0 -> ($TH0) |[CH0]| ($(VAR n))
                           |[CH1]| ($TH1))
   =F
    ? x:{Back0, (RD1 n)} 
      -> IF (x = Back0)
            THEN (($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
            ELSE IF ODD n 
                 THEN (Back0 -> ($TH0) |[CH0]| ($(VAR n))
                                             |[CH1]| Eat1 -> ($(EAT1 n)))
                 ELSE (Back0 -> ($TH0) |[CH0]| ($(VAR n))
                                             |[CH1]| Back1 -> ($TH1))"
apply (cspF_simp unfold_Imp_rules8)
apply (cspF_step_left)
apply (case_tac "EVEN n")
apply (auto)
apply (cspF_simp fold_Imp_rules8)+
done

lemmas Back0_VAR_TH1_simp = Back0_VAR_TH1[simplified]
lemmas unfold_Imp_rules9 = unfold_Imp_rules8 Back0_VAR_TH1_simp
lemmas fold_Imp_rules9 = fold_Imp_rules8 Back0_VAR_TH1_simp[THEN cspF_sym]

(*** TH0 VAR Eat1 step 2 ***)

lemma TH0_VAR_Eat1: 
  "ODD n ==>
    (($TH0) |[CH0]| ($(VAR n)) 
                  |[CH1]| Eat1 -> ($(EAT1 n)))
   =F
    ? x:{Eat1, (RD0 n)} 
      -> IF (x = Eat1)
            THEN (($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($(EAT1 n))) 
            ELSE (Back0 -> ($TH0) |[CH0]| ($(VAR n)) 
                                        |[CH1]| Eat1 -> ($(EAT1 n)))"
apply (cspF_simp unfold_Imp_rules9)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules9)+
done

lemmas TH0_VAR_Eat1_simp = TH0_VAR_Eat1[simplified]
lemmas unfold_Imp_rules10 = unfold_Imp_rules9 TH0_VAR_Eat1_simp
lemmas fold_Imp_rules10 = fold_Imp_rules9 TH0_VAR_Eat1_simp[THEN cspF_sym]

(****************************)
(*** TH0 VAR Back1 step 2 ***)

lemma TH0_VAR_Back1: 
  " (($TH0) |[CH0]| ($(VAR n)) |[CH1]| Back1 -> ($TH1))
   =F
    ? x:{Back1, (RD0 n)}
      -> IF (x = Back1)
            THEN (($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
            ELSE IF EVEN n 
                 THEN (Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n)) 
                                                 |[CH1]| Back1 -> ($TH1)) 
                 ELSE (Back0 -> ($TH0) |[CH0]| ($(VAR n)) 
                                             |[CH1]| Back1 -> ($TH1))"
apply (cspF_simp unfold_Imp_rules10)
apply (cspF_step_left)+
apply (case_tac "EVEN n")
apply (auto)
apply (cspF_simp fold_Imp_rules10)+
done

lemmas TH0_VAR_Back1_simp = TH0_VAR_Back1[simplified]
lemmas unfold_Imp_rules11 = unfold_Imp_rules10 TH0_VAR_Back1_simp
lemmas fold_Imp_rules11 = fold_Imp_rules10 TH0_VAR_Back1_simp[THEN cspF_sym]

(*** EAT0 VAR step 3 ***)

lemma EAT0_VAR: 
  " (($(EAT0 n)) |[CH0]| ($(VAR n)))
   =F
    ? x:insert End0 (insert (RD1 n) (range WR1))
     -> IF (x = End0) 
           THEN (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n)))
           ELSE IF (x = RD1 n) 
                THEN (($(EAT0 n)) |[CH0]| ($(VAR n)))
                ELSE (($(EAT0 n)) |[CH0]| ($(VAR (getInt x))))"
apply (cspF_simp unfold_Imp_rules11)
apply (cspF_step_left)+
apply (case_tac "EVEN n")
apply (auto)
apply (cspF_simp fold_Imp_rules11)+
done

lemmas EAT0_VAR_simp = EAT0_VAR[simplified]
lemmas unfold_Imp_rules12 = unfold_Imp_rules11 EAT0_VAR_simp
lemmas fold_Imp_rules12 = fold_Imp_rules11 EAT0_VAR_simp[THEN cspF_sym]

(*** EAT0 VAR TH1 step 3 ***)

lemma EAT0_VAR_TH1: 
  "EVEN n ==>
    (($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
   =F
    ? x:{End0, (RD1 n)} 
      -> IF (x = End0)
            THEN (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n)) 
                                                |[CH1]| ($TH1))
            ELSE (($(EAT0 n)) |[CH0]| ($(VAR n)) 
                                    |[CH1]| Back1 -> ($TH1))"
apply (cspF_simp unfold_Imp_rules12)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules12)+
done

lemmas EAT0_VAR_TH1_simp = EAT0_VAR_TH1[simplified]
lemmas unfold_Imp_rules13 = unfold_Imp_rules12 EAT0_VAR_TH1_simp
lemmas fold_Imp_rules13 = fold_Imp_rules12 EAT0_VAR_TH1_simp[THEN cspF_sym]

(*** Eat0 VAR Back1 step 3 ***)

lemma Eat0_VAR_Back1:
  "EVEN n ==>
        (Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n)) 
                                   |[CH1]| Back1 -> ($TH1))
   =F
    ? x:{Eat0, Back1} 
      -> IF (x = Eat0)
            THEN (($(EAT0 n)) |[CH0]| ($(VAR n)) 
                                    |[CH1]| Back1 -> ($TH1))
            ELSE (Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n)) 
                                            |[CH1]| ($TH1))"
apply (cspF_simp unfold_Imp_rules13)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules13)+
done

lemmas Eat0_VAR_Back1_simp = Eat0_VAR_Back1[simplified]
lemmas unfold_Imp_rules14 = unfold_Imp_rules13 Eat0_VAR_Back1_simp
lemmas fold_Imp_rules14 = fold_Imp_rules13 Eat0_VAR_Back1_simp[THEN cspF_sym]

(*** TH0 VAR EAT1 step 3 ***)

lemma TH0_VAR_EAT1: 
  "ODD n ==>
    (($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($(EAT1 n)))
   =F
    ? x:{End1, (RD0 n)} 
   -> IF (x = End1)
         THEN (($TH0) |[CH0]| ($(VAR n)) 
                            |[CH1]| WR1 (3 * n + 1) -> ($TH1))
         ELSE (Back0 -> ($TH0) |[CH0]| ($(VAR n)) 
                                     |[CH1]| ($(EAT1 n)))"
apply (cspF_simp unfold_Imp_rules14)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules14)+
done

lemmas TH0_VAR_EAT1_simp = TH0_VAR_EAT1[simplified]
lemmas unfold_Imp_rules15 = unfold_Imp_rules14 TH0_VAR_EAT1_simp
lemmas fold_Imp_rules15 = fold_Imp_rules14 TH0_VAR_EAT1_simp[THEN cspF_sym]

(*** Back0 VAR Eat1 step 3 ***)

lemma Back0_VAR_Eat1: 
  "ODD n ==>
    (Back0 -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| Eat1 -> ($(EAT1 n)))
   =F
    ? x:{Eat1, Back0} 
   -> IF (x = Eat1)
         THEN (Back0 -> ($TH0) |[CH0]| ($(VAR n)) 
                                     |[CH1]| ($(EAT1 n)))
         ELSE (($TH0) |[CH0]| ($(VAR n)) 
                            |[CH1]| Eat1 -> ($(EAT1 n)))"
apply (cspF_simp unfold_Imp_rules15)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules15)+
done

lemmas Back0_VAR_Eat1_simp = Back0_VAR_Eat1[simplified]
lemmas unfold_Imp_rules16 = unfold_Imp_rules15 Back0_VAR_Eat1_simp
lemmas fold_Imp_rules16 = fold_Imp_rules15 Back0_VAR_Eat1_simp[THEN cspF_sym]

(*** Back0 VAR Back1 step 3 ***)

lemma Back0_VAR_Back1: 
  " (Back0 -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| Back1 -> ($TH1))
   =F
    ? x:{Back0, Back1} 
      -> IF (x = Back0)
            THEN (($TH0) |[CH0]| ($(VAR n)) |[CH1]| Back1 -> ($TH1))
            ELSE (Back0 -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))"
apply (cspF_simp unfold_Imp_rules16)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules16)+
done

lemmas Back0_VAR_Back1_simp = Back0_VAR_Back1[simplified]
lemmas unfold_Imp_rules17 = unfold_Imp_rules16 Back0_VAR_Back1_simp
lemmas fold_Imp_rules17 = fold_Imp_rules16 Back0_VAR_Back1_simp[THEN cspF_sym]

(*** WR0 VAR step 4 ***)

lemma WR0_VAR: 
  " (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n)))
   =F
    ? x:insert (WR0 (n div 2)) (insert (RD1 n) (range WR1))
     -> IF (x = WR0 (n div 2))
           THEN (($TH0) |[CH0]| ($(VAR (n div 2))))
           ELSE IF (x = RD1 n)
                THEN (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n)))
                ELSE (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR (getInt x))))"
apply (cspF_simp unfold_Imp_rules17)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules17)+
done

lemmas WR0_VAR_simp = WR0_VAR[simplified]
lemmas unfold_Imp_rules18 = unfold_Imp_rules17 WR0_VAR_simp
lemmas fold_Imp_rules18 = fold_Imp_rules17 WR0_VAR_simp[THEN cspF_sym]

(*** WR0 VAR TH1 step 4 ***)

lemma WR0_VAR_TH1: 
  "EVEN n ==>
    (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))
   =F
    ? x:{(WR0 (n div 2)), (RD1 n)}
      -> IF (x = WR0 (n div 2))
            THEN (($TH0)  |[CH0]| ($(VAR (n div 2))) |[CH1]| ($TH1))
            ELSE (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n)) 
                                                |[CH1]| Back1 -> ($TH1))"
apply (cspF_simp unfold_Imp_rules18)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules18)+
done

lemmas WR0_VAR_TH1_simp = WR0_VAR_TH1[simplified]
lemmas unfold_Imp_rules19 = unfold_Imp_rules18 WR0_VAR_TH1_simp
lemmas fold_Imp_rules19 = fold_Imp_rules18 WR0_VAR_TH1_simp[THEN cspF_sym]

(*** EAT0 VAR Back1 step 4 ***)

lemma EAT0_VAR_Back1: 
  "EVEN n ==>
    (($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| Back1 -> ($TH1))
   =F
    ? x:{End0, Back1} 
      -> IF (x = End0)
            THEN (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n)) 
                                                |[CH1]| Back1 -> ($TH1))
            ELSE (($(EAT0 n)) |[CH0]| ($(VAR n)) |[CH1]| ($TH1))"
apply (cspF_simp unfold_Imp_rules19)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules19)+
done

lemmas EAT0_VAR_Back1_simp = EAT0_VAR_Back1[simplified]
lemmas unfold_Imp_rules20 = unfold_Imp_rules19 EAT0_VAR_Back1_simp
lemmas fold_Imp_rules20 = fold_Imp_rules19 EAT0_VAR_Back1_simp[THEN cspF_sym]

(*** TH0 VAR EAT1 step 4 ***)

lemma TH0_VAR_WR1: 
  "ODD n ==>
    (($TH0) |[CH0]| ($(VAR n)) |[CH1]| WR1 (3 * n + 1) -> ($TH1))
   =F
    ? x:{(WR1 (3 * n + 1)), (RD0 n)} 
   -> IF (x = WR1 (3 * n + 1))
         THEN (($TH0) |[CH0]| ($(VAR (3 * n + 1))) |[CH1]| ($TH1))
         ELSE (Back0 -> ($TH0) |[CH0]| ($(VAR n)) 
                                     |[CH1]| WR1 (3 * n + 1) -> ($TH1))"
apply (cspF_simp unfold_Imp_rules20)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules20)+
done

lemmas TH0_VAR_WR1_simp = TH0_VAR_WR1[simplified]
lemmas unfold_Imp_rules21 = unfold_Imp_rules20 TH0_VAR_WR1_simp
lemmas fold_Imp_rules21 = fold_Imp_rules20 TH0_VAR_WR1_simp[THEN cspF_sym]

(*** Back0 VAR EAT1 step 4 ***)

lemma Back0_VAR_EAT1: 
  "ODD n ==>
    (Back0 -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($(EAT1 n)))
   =F
    ? x:{End1, Back0} 
   -> IF (x = End1)
         THEN (Back0 -> ($TH0) |[CH0]| ($(VAR n)) 
                                     |[CH1]| WR1 (3 * n + 1) -> ($TH1))
         ELSE (($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($(EAT1 n)))"
apply (cspF_simp unfold_Imp_rules21)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules21)+
done

lemmas Back0_VAR_EAT1_simp = Back0_VAR_EAT1[simplified]
lemmas unfold_Imp_rules22 = unfold_Imp_rules21 Back0_VAR_EAT1_simp
lemmas fold_Imp_rules22 = fold_Imp_rules21 Back0_VAR_EAT1_simp[THEN cspF_sym]

(*** WR0 VAR Back1 step 5 ***)

lemma WR0_VAR_Back1: 
  "EVEN n ==>
    (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n)) |[CH1]| Back1 -> ($TH1))
   =F
    ? x:{(WR0 (n div 2)), Back1}
      -> IF (x = WR0 (n div 2))
            THEN (($TH0)  |[CH0]| ($(VAR (n div 2))) 
                                |[CH1]| Back1 -> ($TH1))
            ELSE (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n)) 
                                                |[CH1]| ($TH1))"
apply (cspF_simp unfold_Imp_rules22)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules22)+
done

lemmas WR0_VAR_Back1_simp = WR0_VAR_Back1[simplified]
lemmas unfold_Imp_rules23 = unfold_Imp_rules22 WR0_VAR_Back1_simp
lemmas fold_Imp_rules23 = fold_Imp_rules22 WR0_VAR_Back1_simp[THEN cspF_sym]

(*** Back0 VAR WR1 step 5 ***)

lemma Back0_VAR_WR1: 
  "ODD n ==>
    (Back0 -> ($TH0) |[CH0]| ($(VAR n)) 
                                 |[CH1]| WR1 (3 * n + 1) -> ($TH1))
   =F
    ? x:{(WR1 (3 * n + 1)), Back0} 
   -> IF (x = WR1 (3 * n + 1))
         THEN (Back0 -> ($TH0) |[CH0]| ($(VAR (3 * n + 1))) 
                                     |[CH1]| ($TH1))
         ELSE (($TH0) |[CH0]| ($(VAR n)) 
                            |[CH1]| WR1 (3 * n + 1) -> ($TH1))"
apply (cspF_simp unfold_Imp_rules23)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp fold_Imp_rules23)+
done

lemmas Back0_VAR_WR1_simp = Back0_VAR_WR1[simplified]
lemmas unfold_Imp_rules24 = unfold_Imp_rules23 Back0_VAR_WR1_simp
lemmas fold_Imp_rules24 = fold_Imp_rules23 Back0_VAR_WR1_simp[THEN cspF_sym]

end
