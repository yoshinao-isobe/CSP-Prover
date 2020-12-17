           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                  May 2016  (modified)     |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory FNF_F_sf
imports FNF_F_sf_hide FNF_F_sf_par
        FNF_F_sf_ren  FNF_F_sf_seq
        FNF_F_sf_rest 
begin

(*****************************************************************

         1. full sequentialisation
         2. 
         3. 

 *****************************************************************)

(*****************************************************************
                      small transformation
 *****************************************************************)

definition
  fsfF_Act_prefix ::
  "'a => ('p,'a) proc => ('p,'a) proc"        ("(1_ /->seq _)" [150,80] 80)
  where
  fsfF_Act_prefix_def :
    "a ->seq P == (? y:{a} -> P) [+] STOP"
  
definition
  fsfF_Ext_pre_choice ::
  "'a set => ('a => ('p,'a) proc) => ('p,'a) proc"   ("(1? :_ /->seq _)" [900,80] 80)
  where
  fsfF_Ext_pre_choice_def :
    "? :A ->seq Pf == (? :A -> Pf) [+] STOP"

syntax
  "@fsfF_Ext_pre_choice"  :: "pttrn => 'a set => ('p,'a) proc 
                => ('p,'a) proc"  ("(1? _:_ /->seq _)" [900,900,80] 80)
translations
  "? a:A ->seq P"  == "? :A ->seq (%a. P)"

(* a -> P *)

lemma fsfF_Act_prefix_in:
  "P : fsfF_proc ==> a ->seq P : fsfF_proc"
by (simp add: fsfF_Act_prefix_def fsfF_proc.intros)

lemma cspF_fsfF_Act_prefix_eqF:
  "a -> P =F a ->seq P"
apply (simp add: fsfF_Act_prefix_def)
apply (rule cspF_rw_right)
apply (rule cspF_Ext_choice_unit)
apply (rule cspF_Act_prefix_step)
done

(* ? :A -> Pf *)

lemma fsfF_Ext_pre_choice_in:
  "ALL a. Pf a : fsfF_proc ==> ? :A ->seq Pf : fsfF_proc"
by (simp add: fsfF_Ext_pre_choice_def fsfF_proc.intros)

lemma cspF_fsfF_Ext_pre_choice_eqF:
  "? :A -> Pf =F ? :A ->seq Pf"
apply (simp add: fsfF_Ext_pre_choice_def)
apply (rule cspF_rw_right)
apply (rule cspF_Ext_choice_unit)
apply (rule cspF_reflex)
done

(* IF b THEN P ELSE Q *)

lemma fsfF_IF_in:
  "[| P : fsfF_proc ; Q : fsfF_proc |]
   ==> (if b then P else Q) : fsfF_proc"
by (auto)

lemmas cspF_fsfF_IF_eqF = cspF_IF_split

(*===============================================================*
 |                                                               |
 |      definition of a function for full sequentialization      |
 |                     (no process name)                         |
 |                                                               |
 *===============================================================*)

primrec 
   prefsfF :: "('p,'a) proc => ('p,'a) proc"
where
  "prefsfF(STOP)        = SSTOP"
 |"prefsfF(SKIP)        = SSKIP"
 |"prefsfF(DIV)         = SDIV"
 |"prefsfF(a -> P)      = a ->seq (prefsfF P)"
 |"prefsfF(? :A -> Pf)  = ? a:A ->seq (prefsfF (Pf a))"
 |"prefsfF(P [+] Q)     = (prefsfF P) [+]seq (prefsfF Q)"
 |"prefsfF(P |~| Q)     = (prefsfF P) |~|seq (prefsfF Q)"
 |"prefsfF(!! :C .. Pf) = !! c:C ..seq prefsfF (Pf c)"
 |"prefsfF(IF b THEN P ELSE Q) = (if b then prefsfF(P) else prefsfF(Q))"
 |"prefsfF(P |[X]| Q)   = (prefsfF P) |[X]|seq (prefsfF Q)"
 |"prefsfF(P -- X)      = (prefsfF P) --seq X"
 |"prefsfF(P [[r]])     = (prefsfF P) [[r]]seq"
 |"prefsfF(P ;; Q)      = (prefsfF P) ;;seq (prefsfF Q)"
 |"prefsfF(P |. n)      = (prefsfF P) |.seq n"
 |"prefsfF($p)          = $p"



(*===============================================================*
            --- prefsfF P is fullly sequentialized ---
 *===============================================================*)

lemma prefsfF_in_lm: 
  "noPN P --> prefsfF P : fsfF_proc"
apply (induct_tac P)
apply (simp_all)
apply (simp add: fsfF_Act_prefix_in)
apply (simp add: fsfF_Ext_pre_choice_in)
apply (simp add: fsfF_Ext_choice_in)
apply (simp add: fsfF_Int_choice_in)
apply (simp add: fsfF_Rep_int_choice_in)
apply (simp add: fsfF_Parallel_in)
apply (simp add: fsfF_Hiding_in)
apply (simp add: fsfF_Renaming_in)
apply (simp add: fsfF_Seq_compo_in)
apply (simp add: fsfF_Depth_rest_in)
done

lemma prefsfF_in: 
  "noPN P ==> prefsfF P : fsfF_proc"
by (simp add: prefsfF_in_lm)

(*===============================================================*
           --- prefsfF P is equal to P based on F ---
 *===============================================================*)

lemma cspF_prefsfF_eqF_lm:
  "noPN P --> P =F prefsfF P"
apply (induct_tac P)
apply (simp add: cspF_SSTOP_eqF)
apply (simp add: cspF_SSKIP_eqF)
apply (simp add: cspF_SDIV_eqF)

(* Act_prefix *)
apply (intro impI)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp_all)
apply (simp add: cspF_fsfF_Act_prefix_eqF)

(* Ext_pre_choice *)
apply (intro impI)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule rev_all1E)    (* modified for Isabelle 2016 *)
apply (simp)
apply (drule_tac x="a" in spec)+
apply (simp_all)
apply (force)
apply (simp add: cspF_fsfF_Ext_pre_choice_eqF)

(* Ext_choice *)
apply (intro impI)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp_all)
apply (simp add: cspF_fsfF_Ext_choice_eqF)

(* Int_choice *)
apply (intro impI)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp_all)
apply (simp add: cspF_fsfF_Int_choice_eqF)

(* Rep_int_choice *)
apply (intro impI)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
(* isabelle 2013
apply (erule rev_all1E)
apply (drule_tac x="c" in spec)+
apply (simp_all)
*)
apply (rule rev_all1E)
apply (simp)
apply (drule_tac x="c" in spec)+
apply (simp_all)
apply (force)

apply (simp add: cspF_fsfF_Rep_int_choice_eqF)

(* IF *)
apply (intro conjI impI)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp_all)
apply (rule cspF_IF)
apply (rule cspF_rw_left)
apply (rule cspF_IF)
apply (simp_all)

(* Parallel *)
apply (intro impI)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp_all)

apply (simp add: cspF_fsfF_Parallel_eqF)

(* Hiding *)
apply (intro impI)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp_all)
apply (simp add: cspF_fsfF_Hiding_eqF)

(* Renaming *)
apply (intro impI)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp_all)
apply (simp add: cspF_fsfF_Renaming_eqF)

(* Seq_compo *)
apply (intro impI)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp_all)
apply (simp add: cspF_fsfF_Seq_compo_eqF)

(* Depth_rest *)
apply (intro impI)
apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp_all)
apply (simp add: cspF_fsfF_Depth_rest_eqF)
done

lemma cspF_prefsfF_eqF:
  "noPN P ==> P =F prefsfF P"
by (simp add: cspF_prefsfF_eqF_lm)

(*===============================================================*
 |                                                               |
 |      definition of a function for full sequentialization      |
 |                                                               |
 *===============================================================*)

definition
   fsfF :: "('p,'a) proc => ('p,'a) proc"
   where
   fsfF_def : "fsfF == (%P. prefsfF(rmPN(P)))"

(*===============================================================*
           theorem --- fsfF P is fullly sequentialized ---
 *===============================================================*)

theorem fsfF_in: 
  "fsfF P : fsfF_proc"
apply (simp add: fsfF_def)
apply (rule prefsfF_in)
apply (simp add: noPN_rmPN)
done

(*===============================================================*
           theorem --- fsfF P is equal to P based on F ---
 *===============================================================*)

lemma cspF_fsfF_eqF:
  "FPmode = CPOmode | FPmode = MIXmode ==>  P =F fsfF P"
apply (simp add: fsfF_def)
apply (rule cspF_rw_right)
apply (rule cspF_prefsfF_eqF[THEN cspF_sym])
apply (simp add: noPN_rmPN)
apply (rule cspF_rmPN_eqF)
apply (force)
done

end
