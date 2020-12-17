           (*-------------------------------------------*
            |  The Dining Mathematicians in CSP-Prover  |
            |               August 2004                 |
            |             December 2004 (modified)      |
            |             November 2005 (modified)      |
            |                April 2006 (modified)      |
            |                  May 2016  (modified)     |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory DM1_Imp_def
imports CSP_F
begin

(*****************************************************************

         1. defines Imp
         2.
         3. 
         4. 

 *****************************************************************)

(*********************************************************
                    ODD and EVEN
 *********************************************************)

definition
  EVEN :: "int => bool"
  where
  EVEN_def : "EVEN n == (n mod 2 = 0)"
  
definition  
  ODD  :: "int => bool"
  where
  ODD_def  : "ODD n  == (n mod 2 = 1)"

abbreviation 
  EVENs :: "int set" ("EVENs")
where
  "EVENs == Collect EVEN"

abbreviation 
  ODDs  :: "int set" ("ODDs")
where
  "ODDs == Collect ODD"

(*********************************************************
                         event
 *********************************************************)

datatype Event = Eat0 | Back0 | End0 | RD0 int | WR0 int
               | Eat1 | Back1 | End1 | RD1 int | WR1 int 
               | NUM int

lemma expand_Event_fun[simp]:
  "ALL Ef Eg. ((Ef::int => Event) = Eg) = (ALL n. Ef n = Eg n)"
apply (simp add: fun_eq_iff)
done


abbreviation CH0 :: "Event set"
where "CH0 == (range RD0) Un (range WR0)"

abbreviation CH1 :: "Event set"
where "CH1 == (range RD1) Un (range WR1)"

abbreviation OBS :: "Event set"
where "OBS == {Eat0, Back0, End0, Eat1, Back1, End1}"

(*********************************************************
                     function
 *********************************************************)

primrec
  getInt :: "Event => int"
where
  "getInt (Eat0)   = 0"
 |"getInt (Eat1)   = 0"
 |"getInt (Back0)  = 0"
 |"getInt (Back1)  = 0"
 |"getInt (End0)   = 0"
 |"getInt (End1)   = 0"
 |"getInt (RD0 n)  = n"
 |"getInt (RD1 n)  = n"
 |"getInt (WR0 n)  = n"
 |"getInt (WR1 n)  = n"
 |"getInt (NUM n)  = n"

(*********************************************************
                Parallel system definition
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


datatype ImpName = VAR int | TH0 | EAT0 int | TH1 | EAT1 int

primrec
  Impfun :: "ImpName => (ImpName, Event) proc"
where
  "Impfun   (TH0) = RD0 ? n -> IF (EVEN n)
                                  THEN (Eat0  -> $(EAT0 n))
                                  ELSE (Back0 -> $(TH0))"

 |"Impfun   (TH1) = RD1 ? n -> IF (ODD n)
                                  THEN (Eat1  -> $(EAT1 n))
                                  ELSE (Back1 -> $(TH1))"

 |"Impfun (EAT0 n) = End0 -> WR0 ! (n div 2) -> $(TH0)"

 |"Impfun (EAT1 n) = End1 -> WR1 ! (3 * n + 1) -> $(TH1)"

 |"Impfun (VAR n) = WR0 ? n -> $(VAR n)
                   [+] WR1 ? n -> $(VAR n)
                   [+] RD0 ! n -> $(VAR n)
                   [+] RD1 ! n -> $(VAR n)"
(*
defs (overloaded)
Set_Impfun_def [simp]: "PNfun == Impfun"
*)

overloading Set_Impfun == 
  "PNfun :: (ImpName, Event) pnfun"
begin
  definition "PNfun == Impfun"
end
  
declare Set_Impfun_def [simp]

definition
  Imp :: "int => (ImpName, Event) proc"
  where
  Imp_def: "Imp == (%n. ($TH0 |[CH0]| $(VAR n) |[CH1]| $TH1) -- (CH0 Un CH1))"

(*********************************************************
         To unfold "range" and "syntactic sugar", ...
 *********************************************************)

declare image_iff         [simp]
declare inj_on_def        [simp]
declare csp_prefix_ss_def [simp]


(*********************************************************
                gProc lemmas (routine work)
 *********************************************************)

lemma guarded_Imp[simp]:
      "guardedfun Impfun"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp_all)+

(*********************************************************
                        Lemmas
 *********************************************************)

(*** int lemmas ***)

lemma int_le_inc: "ALL (n::int) m. n <= m --> n = m | n+1 <= m"
by (auto)

lemma mod_2_not_le: "ALL (n::int). ~(2 <= n mod 2)"
by (simp add: linorder_not_le)

lemma mod_2_or: "ALL (n::int). n mod 2 = 0 | n mod 2 =1"
apply (intro allI)
apply (insert int_le_inc)
apply (drule_tac x="0" in spec)
apply (drule_tac x="n mod 2" in spec)
apply (simp)
apply (erule disjE)
apply (simp)

apply (insert int_le_inc)
apply (drule_tac x="1" in spec)
apply (drule_tac x="n mod 2" in spec)
apply (simp)
done

(*** ODD and EVEN lemmas ***)

lemma EVEN_not_ODD[simp]: "ALL n. EVEN n = (~ ODD n)"
apply (auto simp add: EVEN_def ODD_def )
done

lemma ODD_add_1: "ALL n. (n mod 2 = 1) --> ((n + 1) mod 2 = (0::int))"
apply (simp add: mod_add_eq[THEN sym])
(*
apply (simp add: mod_add_eq)          (in Isabelle 2016)
*)
(*
apply (simp add: zmod_zadd_left_eq)   (in Isabelle 2008)
*)
done

lemma ODD_EX: "ALL m. ODD m --> (EX n. m = 2 * n + 1)"
apply (intro allI impI)
apply (simp add: ODD_def)
apply (insert ODD_add_1)
apply (drule_tac x="m" in spec)
apply (simp)
apply (simp add: zmod_eq_0_iff)
apply (erule exE)
apply (rule_tac x="q - 1" in exI)
apply (simp)
done

lemma ODD_to_EVEN[simp]: "ODD n ==> EVEN (3 * n + 1)"
apply (insert ODD_EX)
apply (drule_tac x="n" in spec)
apply (simp add: ODD_def EVEN_def)
apply (erule exE)
(*
apply (simp add: zmod_zadd_left_eq)
apply (simp add: zmod_zmult1_eq')
*)
apply (simp add: mod_add_eq)
(* apply (simp add: mod_mult_eq) *)
done

lemma ODD_to_notODD[simp]: "ODD n ==> ~ ODD (3 * n + 1)"
apply (insert ODD_to_EVEN[of n])
apply (simp)
done

(*** range ***)

lemma fold_range: "(EX a. x = f a) = (x : range f)"
apply (auto)
done

(*********************************************************
           unfolding & folding process names
 *********************************************************)

(*** unfold VAR ***)

lemma VAR:
     "$(VAR n)
    =F ? x:insert (RD1 n) (insert (RD0 n) ((range WR0) Un (range WR1)))
         -> IF (x : (range WR0) | x : (range WR1)) 
            THEN $(VAR (getInt x)) ELSE $(VAR n)"
apply (cspF_unwind_left)
apply (cspF_step_left)+
apply (auto)
apply (cspF_simp)+
done

lemmas VAR_simp = VAR[simplified]
(*
lemmas unfold_Imp_rules = VAR_simp
lemmas fold_Imp_rules = VAR_simp[THEN cspF_sym]
*)

(*** unfold TH0 ***)

lemma TH0:
     "($TH0)
   =F RD0 ? n -> IF (EVEN n) THEN (Eat0  -> ($(EAT0 n)))
                             ELSE (Back0 -> ($TH0))"
apply (cspF_unwind_left)
done

lemmas TH0_simp = TH0[simplified]
lemmas unfold_Imp_rules0 = VAR_simp TH0_simp
lemmas fold_Imp_rules0 = VAR_simp[THEN cspF_sym] TH0_simp[THEN cspF_sym]

(*** unfold TH1 ***)

lemma TH1:
     "($TH1)
   =F RD1 ? n -> IF (ODD n) THEN (Eat1  ->  ($(EAT1 n)))
                            ELSE (Back1 -> ($TH1))"
by (cspF_unwind_left)

lemmas TH1_simp = TH1[simplified]
lemmas unfold_Imp_rules1 = unfold_Imp_rules0 TH1_simp
lemmas fold_Imp_rules1 = fold_Imp_rules0 TH1_simp[THEN cspF_sym]

(*** unfold EAT0 ***)

lemma EAT0:
     "($(EAT0 n))
   =F ? x:{End0} -> WR0 (n div 2) -> ($TH0)"
by (cspF_unwind_left)

lemmas EAT0_simp = EAT0[simplified]
lemmas unfold_Imp_rules2 = unfold_Imp_rules1 EAT0_simp
lemmas fold_Imp_rules2 = fold_Imp_rules1 EAT0_simp[THEN cspF_sym]

(*** unfold EAT1 ***)

lemma EAT1:
     "($(EAT1 n))
   =F ? x:{End1} -> WR1 ! (3 * n + 1) -> ($TH1)"
by (cspF_unwind_left)

lemmas EAT1_simp = EAT1[simplified]
lemmas unfold_Imp_rules3 = unfold_Imp_rules2 EAT1_simp
lemmas fold_Imp_rules3 = fold_Imp_rules2 EAT1_simp[THEN cspF_sym]

end
