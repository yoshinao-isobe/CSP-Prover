           (*-------------------------------------------*
            |  The Dining Mathematicians in CSP-Prover  |
            |               August 2004                 |
            |             December 2004 (modified)      |
            |             November 2005 (modified)      |
            |                March 2007  (modified)     |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory DM4_Spc_def
imports DM3_hide
begin

(*****************************************************************

         1. defines Spc 
         2.
         3. 
         4. 

 *****************************************************************)

(*********************************************************
                     specification 
 *********************************************************)

datatype SpcName = TH0_TH1 | EAT0_TH1 | TH0_EAT1

primrec
  Spcfun :: "SpcName => (SpcName, Event) proc"
where
   "Spcfun
      (TH0_TH1)  = ! x:OBS -> IF (x = Eat0) THEN ($EAT0_TH1)
                                 ELSE IF (x = Eat1) THEN ($TH0_EAT1)
                                                    ELSE ($TH0_TH1)"

  |"Spcfun
      (EAT0_TH1) = ! x:(OBS - {Eat1}) -> IF (x = End0) 
                                            THEN ($TH0_TH1)
                                            ELSE ($EAT0_TH1)"

  |"Spcfun
      (TH0_EAT1) = ! x:(OBS - {Eat0}) -> IF (x = End1) 
                                            THEN ($TH0_TH1)
                                            ELSE ($TH0_EAT1)"
(*
defs (overloaded)
Set_Spcfun_def [simp]: "PNfun == Spcfun"
*)
overloading Set_Spcfun == 
  "PNfun :: (SpcName, Event) pnfun"
begin
  definition "PNfun == Spcfun"
end
  
declare Set_Spcfun_def [simp]

definition
  Spc :: "(SpcName,Event) proc"
  where
  Spc_def: "Spc == $TH0_TH1"

(*********************************************************
        Lemmas for   ALL n.  verify Spc <=sf Imp n
 *********************************************************)

(*** relation between Spcfun and ImpDef ***)

primrec
  Spc_to_Imp :: "SpcName => (ImpName,Event) proc"
where
  "Spc_to_Imp
     TH0_TH1 = 
       !<NUM> n .. (($TH0) |[CH0]| ($(VAR n))
                                 |[CH1]| ($TH1)) -- (CH0 Un CH1)
       |~|
       !<NUM> n .. (Back0 -> ($TH0) |[CH0]| ($(VAR n))
                                          |[CH1]| ($TH1)) -- (CH0 Un CH1)
       |~|
       !<NUM> n .. (($TH0) |[CH0]| ($(VAR n)) 
                                 |[CH1]| Back1 -> ($TH1)) -- (CH0 Un CH1)
       |~|
       !<NUM> n .. (Back0 -> ($TH0) |[CH0]| ($(VAR n))
                                          |[CH1]| Back1 -> ($TH1)) 
                  -- (CH0 Un CH1)
       |~|
       !<NUM> n:EVENs .. (Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n))
                                           |[CH1]| Back1 -> ($TH1))
                        -- (CH0 Un CH1)
       |~|
       !<NUM> n:ODDs  .. (Back0 -> ($TH0) |[CH0]| ($(VAR n))
                                                |[CH1]| Eat1 -> ($(EAT1 n)))
                        -- (CH0 Un CH1)
       |~|
       !<NUM> n:EVENs .. (Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n))
                                           |[CH1]| ($TH1))
                        -- (CH0 Un CH1)
       |~|
       !<NUM> n:ODDs  .. (($TH0) |[CH0]| ($(VAR n))
                                       |[CH1]| Eat1 -> ($(EAT1 n)))
                        -- (CH0 Un CH1)
       |~|
       !<NUM> n:EVENs .. (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n))
                                                        |[CH1]| ($TH1))
                       -- (CH0 Un CH1)
       |~|
       !<NUM> n:EVENs .. (WR0 (n div 2) -> ($TH0) |[CH0]| ($(VAR n))
                                                        |[CH1]| Back1 -> ($TH1))
                       -- (CH0 Un CH1)
       |~|
       !<NUM> n:ODDs  .. (($TH0) |[CH0]| ($(VAR n))
                                       |[CH1]| WR1 ! (3 * n + 1) -> ($TH1))
                       -- (CH0 Un CH1)
       |~|
       !<NUM> n:ODDs  .. (Back0 -> ($TH0) |[CH0]| ($(VAR n))
                                                |[CH1]| WR1 ! (3 * n + 1) -> ($TH1))
                       -- (CH0 Un CH1)"

 |"Spc_to_Imp
     EAT0_TH1 = 
       !<NUM> n:EVENs .. (($(EAT0 n)) |[CH0]| ($(VAR n)) 
                                            |[CH1]| ($TH1)) 
                       -- (CH0 Un CH1)
       |~|
       !<NUM> n:EVENs .. (($(EAT0 n)) |[CH0]| ($(VAR n))
                                            |[CH1]| Back1 -> ($TH1))
                       -- (CH0 Un CH1)"

 |"Spc_to_Imp
     TH0_EAT1 = 
       !<NUM> n:ODDs .. (($TH0) |[CH0]| ($(VAR n)) |[CH1]| ($(EAT1 n)))
                       -- (CH0 Un CH1)
       |~|
       !<NUM> n:ODDs .. (Back0 -> ($TH0) |[CH0]| ($(VAR n))
                                               |[CH1]| ($(EAT1 n)))
                       -- (CH0 Un CH1)"

(*********************************************************
                gProc lemmas (routine work)
 *********************************************************)

lemma guarded_Spc[simp]:
      "guardedfun Spcfun"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp_all)+

end
