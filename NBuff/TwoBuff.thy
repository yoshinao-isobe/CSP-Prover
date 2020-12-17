           (*-------------------------------------------*
            |                2 Buffers                  |
            |                                           |
            |                June 2009                  |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory TwoBuff
imports CSP_F
begin

(*=============================================================*
 |                                                             |
 |                           Process                           |
 |                                                             |
 *=============================================================*)

(*********************************************************
               process names and events
 *********************************************************)

datatype Event = inC | outC | midC
datatype PN = Buff1 | Buff1' | Buff2 | Buff2' | Buff2''

(*********************************************************
                  Recursivey Process
 *********************************************************)

primrec	
  PNdef :: "PN => (PN, Event) proc"
where
 "PNdef   (Buff1) = inC -> $Buff1'"
|"PNdef  (Buff1') = outC -> $Buff1"

|"PNdef   (Buff2) = inC -> $Buff2'"
|"PNdef  (Buff2') = inC -> $Buff2'' [+] outC -> $Buff2"
|"PNdef (Buff2'') = outC -> $Buff2'"

(*
defs (overloaded) Set_PNfun_def [simp]: "PNfun == PNdef"
*)


overloading Set_PNdef == 
  "PNfun :: (PN, Event) pnfun"
begin
  definition "PNfun == PNdef"
end
  
declare Set_PNdef_def [simp]

(* ------------------ *
      guardedness
 * ------------------ *)

lemma guardedfun_PN[simp]:
      "guardedfun PNdef"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp_all)
(*
defs FPmode_def [simp]: "FPmode == CMSmode"
*)

overloading FPmode == 
  "FPmode :: fpmode"
begin
  definition "FPmode == CMSmode"
end

declare FPmode_def [simp]

(*********************************************************
                     Composition
 *********************************************************)

abbreviation
 Link :: "(PN, Event) proc => (PN, Event) proc => (PN, Event) proc"
        ("(1_ /<---> _)" [76,77] 76)
where "P <---> Q == (P[[outC<-->midC]] |[{midC}]| 
                     Q[[inC<-->midC]]) -- {midC}"

abbreviation
 LinkBuff2 :: "(PN, Event) proc"
where "LinkBuff2 == $Buff1 <---> $Buff1"

(*********************************************************
                  for automatising
 *********************************************************)

declare simp_event_set [simp]

lemma Link_cong: "Q =F R ==> P <---> Q =F P <---> R"
by (simp)

(*********************************************************
                    verification
 *********************************************************)

primrec
  Buff2_to_LinkBuff2 :: "PN => (PN, Event) proc"
where
  "Buff2_to_LinkBuff2 (Buff1) = $Buff1"
 |"Buff2_to_LinkBuff2 (Buff1') = $Buff1'"
 |"Buff2_to_LinkBuff2 (Buff2) = LinkBuff2"
 |"Buff2_to_LinkBuff2 (Buff2') = $Buff1' <---> $Buff1"
 |"Buff2_to_LinkBuff2 (Buff2'') = $Buff1' <---> $Buff1'"

theorem Buff2_eq_LinkBuff2:
   "$Buff2 =F LinkBuff2"

(* by finxed point induction *)
apply (rule cspF_fp_induct_left[of _ "Buff2_to_LinkBuff2"])
apply (simp+, induct_tac p, auto, cspF_unwind+)

(* by sequentialising *)
apply (cspF_auto | auto)+
done

end
