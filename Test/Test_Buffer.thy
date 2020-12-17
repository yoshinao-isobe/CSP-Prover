           (*-------------------------------------------*
            |                   Test                    |
            |        CSP-Prover on Isabelle2005         |
            |                  April 2006               |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory Test_Buffer
imports CSP_F
begin

(*****************************************************************

         1. test Buffer
         2. verification of deadlock-free.
         3.
         4. 

 *****************************************************************)

datatype Event = left real | right "real * nat"
datatype Name = Empty nat | Full real nat
datatype DFName = DF

primrec
  Bufferfun :: "Name => (Name, Event) proc"
where
  "Bufferfun  (Empty n)  = left ? r -> $(Full r n)"
 |"Bufferfun  (Full r n) = right (r,n) -> $(Empty (Suc n))"

 (*
defs (overloaded)
Set_Bufferfun_def [simp]: "PNfun == Bufferfun"
*)

overloading Set_Bufferfun == 
  "PNfun :: (Name, Event) pnfun"
begin
  definition "PNfun == Bufferfun"
end

declare Set_Bufferfun_def [simp]

definition
  Buffer :: "(Name, Event) proc"
  where
  Buffer_def: "Buffer == $(Empty 0)"

(*** Spc ***)

primrec
  DFfun :: "DFName => (DFName, Event) proc"
where
  "DFfun  DF = (! x -> $DF)"
(*
defs (overloaded)
Set_DFfun_def [simp]: "PNfun == DFfun"
*)

overloading Set_DFfun == 
  "PNfun :: (DFName, Event) pnfun"
begin
  definition "PNfun == DFfun"
end

declare Set_DFfun_def [simp]

(*** To automatically unfold syntactic sugar ***)
declare csp_prefix_ss_def[simp]
declare inj_on_def[simp]

(*********************************************************
               guardedfun (rutine work)
 *********************************************************)

lemma guardedfun_Bufferfun[simp]:
     "guardedfun Bufferfun"
apply (simp add: guardedfun_def, rule)
apply (induct_tac p)
apply (simp_all)+
done

lemma guardedfun_DFfun[simp]:
     "guardedfun DFfun"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp_all)

(*********************************************************
            relation between Buffer and DF
 *********************************************************)

primrec
  Buffer_to_DF :: "Name => (DFName, Event) proc"
where
  "Buffer_to_DF (Empty n)  = $DF"
 |"Buffer_to_DF (Full r n) = $DF"

(*********************************************************
               Buffer is deadlock free.
 *********************************************************)

(*** manual proof ***)

(*
defs FPmode_def [simp]: "FPmode == CMSmode"
*)
(* use the CMS approach in this example *)

overloading FPmode == 
  "FPmode :: fpmode"
begin
  definition "FPmode == CMSmode"
end

declare FPmode_def [simp]

lemma manual_proof_Buffer: 
  "$DF <=F Buffer"
apply (simp add: Buffer_def)
apply (rule cspF_fp_induct_right[of _ _ "Buffer_to_DF"])
apply (simp)
apply (simp)
apply (simp)

apply (induct_tac p)
apply (simp_all)

(* Empty *)
apply (rule cspF_rw_left)
apply (rule cspF_unwind)
apply (simp)
apply (simp)
apply (simp)
apply (rule cspF_decompo_subset)
apply (simp_all)

(* Full *)
apply (rule cspF_rw_left)
apply (rule cspF_unwind)
apply (simp)
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_step)

apply (simp)
apply (rule cspF_decompo_subset)
apply (simp)
apply (simp)
apply (rule cspF_reflex)
done

(*** semi-automatic proof ***)

lemma semi_auto_proof_Buffer: "$DF <=F Buffer"
apply (simp add: Buffer_def)
apply (rule cspF_fp_induct_right[of _ _ "Buffer_to_DF"])
apply (simp)+

apply (induct_tac p)
apply (cspF_auto, rule cspF_decompo_subset, simp_all)+
done

end
