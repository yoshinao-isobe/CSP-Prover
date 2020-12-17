           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |              Februaru 2006                |
            |                 March 2007  (modified)    |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory FNF_F_sf_par
imports FNF_F_sf_induct FNF_F_sf_ext
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite UnionT and InterT.                 *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*  The following simplification rules are deleted in this theory file *)
(*       P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))        *)
(* Isabelle 2017: split_if --> if_split *)

declare if_split  [split del]

(*****************************************************************

         1. full sequentialization for Parallel (P1 |[X]| DIV)
         2. full sequentialization for Parallel (P1 |[X]| SKIP)
         3. full sequentialization for Parallel (P1 |[X]| P2)

 *****************************************************************)

(*============================================================*
 |                                                            |
 |                Parallel (P |[X]| DIV)                      |
 |                                                            |
 *============================================================*)

definition
  Pfun_Parallel_DIV :: "'a set => (('p,'a) proc => ('p,'a) proc)"
  where
  Pfun_Parallel_DIV_def :
    "Pfun_Parallel_DIV X == (%P1. P1 |[X]| DIV)"
  
definition
  SP_step_Parallel_DIV :: 
   "'a set => ('a set => ('a => ('p,'a) proc) => ('p,'a) proc => ('a => ('p,'a) proc) => ('p,'a) proc)"
  where
  SP_step_Parallel_DIV_def :
    "SP_step_Parallel_DIV X == (%A1 Pf1 Q1 SPf. 
                               (? :(A1-X) -> SPf) [+] DIV)"

definition
  fsfF_Parallel_DIV :: "'a set => ('p,'a) proc => ('p,'a) proc"
  where
  fsfF_Parallel_DIV_def :
    "fsfF_Parallel_DIV X == (%P1. 
       (fsfF_induct1 (Pfun_Parallel_DIV X)
                     (SP_step_Parallel_DIV X) P1))"

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fsfF_Parallel_DIV_in:
    "P1 : fsfF_proc
     ==> fsfF_Parallel_DIV X P1 : fsfF_proc"
apply (simp add: fsfF_Parallel_DIV_def)
apply (rule fsfF_induct1_in)
apply (simp_all add: SP_step_Parallel_DIV_def
                     fsfF_proc.intros)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

lemma cspF_fsfF_Parallel_DIV_eqF:
    "P1 |[X]| DIV =F fsfF_Parallel_DIV X P1"
apply (simp add: fsfF_Parallel_DIV_def)
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_induct1_eqF[THEN cspF_sym])
apply (simp_all add: Pfun_Parallel_DIV_def
                     SP_step_Parallel_DIV_def)
apply (rule cspF_Dist_nonempty, simp)

apply (rule cspF_rw_left)
apply (rule cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice)
apply (simp)
apply (rule cspF_rw_left)
apply (rule cspF_SKIP_DIV)
apply (simp)
apply (rule cspF_decompo | rule cspF_reflex | simp)+
done

(*============================================================*
 |                                                            |
 |                Parallel (P |[X]| SKIP)                     |
 |                                                            |
 *============================================================*)

definition
  Pfun_Parallel_SKIP :: "'a set => (('p,'a) proc => ('p,'a) proc)"
  where
  Pfun_Parallel_SKIP_def :
    "Pfun_Parallel_SKIP X == (%P1. P1 |[X]| SKIP)"
  
definition
  SP_step_Parallel_SKIP :: 
   "'a set => ('a set => ('a => ('p,'a) proc) => ('p,'a) proc => 
     ('a => ('p,'a) proc) => ('p,'a) proc)"
  where
  SP_step_Parallel_SKIP_def :
    "SP_step_Parallel_SKIP X == (%A1 Pf1 Q1 SPf.
                                (? :(A1-X) -> SPf) [+] Q1)"

definition
  fsfF_Parallel_SKIP  :: "'a set => ('p,'a) proc => ('p,'a) proc"
  where
  fsfF_Parallel_SKIP_def :
    "fsfF_Parallel_SKIP X == (%P1. 
       (fsfF_induct1 (Pfun_Parallel_SKIP X)
                     (SP_step_Parallel_SKIP X) P1))"

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fsfF_Parallel_SKIP_in:
    "P1 : fsfF_proc
     ==> fsfF_Parallel_SKIP X P1 : fsfF_proc"
apply (simp add: fsfF_Parallel_SKIP_def)
apply (rule fsfF_induct1_in)
apply (simp_all add: SP_step_Parallel_SKIP_def
                     fsfF_proc.intros)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

lemma cspF_fsfF_Parallel_SKIP_eqF:
    "P1 |[X]| SKIP =F fsfF_Parallel_SKIP X P1"
apply (simp add: fsfF_Parallel_SKIP_def)
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_induct1_eqF[THEN cspF_sym])
apply (simp_all add: Pfun_Parallel_SKIP_def
                     SP_step_Parallel_SKIP_def)

apply (rule cspF_Dist_nonempty, simp)

apply (rule cspF_rw_left)
apply (rule cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice)
apply (simp)
apply (simp)
apply (rule cspF_decompo | rule cspF_reflex | simp)+
done

(*============================================================*
 |                                                            |
 |              Parallel (P |[X]| SKIP or DIV)                |
 |                                                            |
 *============================================================*)

definition
  fsfF_Parallel_SKIP_DIV  :: "'a set => ('p,'a) proc => ('p,'a) proc => ('p,'a) proc"

where
  fsfF_Parallel_SKIP_DIV_def :
    "fsfF_Parallel_SKIP_DIV X P1 P2 ==
        if (P2 = SKIP) then fsfF_Parallel_SKIP X P1
        else if (P2 = DIV) then fsfF_Parallel_DIV X P1
        else (P1 |[X]| P2)"

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fsfF_Parallel_SKIP_DIV_in:
    "[| P1 : fsfF_proc ; P2 = SKIP | P2 = DIV |]
     ==> fsfF_Parallel_SKIP_DIV X P1 P2 : fsfF_proc"
apply (simp add: fsfF_Parallel_SKIP_DIV_def)
apply (erule disjE)
apply (simp add: fsfF_Parallel_SKIP_in)
apply (simp add: fsfF_Parallel_DIV_in)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

lemma cspF_fsfF_Parallel_SKIP_DIV_eqF:
    "P1 |[X]| P2 =F fsfF_Parallel_SKIP_DIV X P1 P2"
apply (simp add: fsfF_Parallel_SKIP_DIV_def)
apply (simp split: if_split)
apply (intro conjI impI)
apply (simp add: cspF_fsfF_Parallel_DIV_eqF)
apply (simp add: cspF_fsfF_Parallel_SKIP_eqF)
done

lemmas cspF_fsfF_Parallel_SKIP_DIV_eqF_sym =
       cspF_fsfF_Parallel_SKIP_DIV_eqF[THEN cspF_sym]

(*============================================================*
 |                                                            |
 |            Genaralized Parallel (P |[X]| Q)                |
 |                                                            |
 *============================================================*)

definition
  Pfun_Parallel :: "'a set => (('p,'a) proc => ('p,'a) proc => ('p,'a) proc)"
  where
  Pfun_Parallel_def :
    "Pfun_Parallel X == (%P1 P2. P1 |[X]| P2)"
  
definition
  SP_step_Parallel :: 
   "'a set => 
    ('a set => ('a => ('p,'a) proc) => ('p,'a) proc => 
     'a set => ('a => ('p,'a) proc) => ('p,'a) proc => 
    ('a => ('p,'a) proc) => ('a => ('p,'a) proc) => ('a => ('p,'a) proc) => ('p,'a) proc)"
  where
  SP_step_Parallel_def :
    "SP_step_Parallel X == (%A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2. 
    (if (Q1 = STOP & Q2 = STOP) then
     ((? a:((X Int A1 Int A2) Un (A1 - X) Un (A2 - X))
          -> (if (a : X) then (SPf a)
                 else if (a : A1 & a : A2)
                      then ((SPf1 a) |~|seq (SPf2 a))
                 else if (a : A1) then (SPf1 a)
                 else (SPf2 a))) [+] STOP)
    else if (Q1 = STOP) then
    (((? a:((X Int A1 Int A2) Un (A1 - X) Un (A2 - X))
        -> (if (a : X) then (SPf a)
               else if (a : A1 & a : A2)
                    then ((SPf1 a) |~|seq (SPf2 a))
               else if (a : A1) then (SPf1 a)
               else (SPf2 a))) [+] STOP)
     [>seq
     (fsfF_Parallel_SKIP_DIV X (((? :A1 -> Pf1) [+] Q1)) Q2))

    else if (Q2 = STOP) then
    (((? a:((X Int A1 Int A2) Un (A1 - X) Un (A2 - X))
        -> (if (a : X) then (SPf a)
               else if (a : A1 & a : A2)
                    then ((SPf1 a) |~|seq (SPf2 a))
               else if (a : A1) then (SPf1 a)
               else (SPf2 a))) [+] STOP)
     [>seq
     (fsfF_Parallel_SKIP_DIV X (((? :A2 -> Pf2) [+] Q2)) Q1))

   else
    (((? a:((X Int A1 Int A2) Un (A1 - X) Un (A2 - X))
        -> (if (a : X) then (SPf a)
               else if (a : A1 & a : A2)
                    then ((SPf1 a) |~|seq (SPf2 a))
               else if (a : A1) then (SPf1 a)
               else (SPf2 a))) [+] STOP)
     [>seq
     ((fsfF_Parallel_SKIP_DIV X 
             (((? :A2 -> Pf2) [+] Q2)) Q1) |~|seq
      (fsfF_Parallel_SKIP_DIV X 
             (((? :A1 -> Pf1) [+] Q1)) Q2)))))"

definition
  fsfF_Parallel  :: "('p,'a) proc => 'a set => ('p,'a) proc => ('p,'a) proc"
                          ("(1_ /|[_]|seq _)" [76,0,77] 76)
  where
  fsfF_Parallel_def :
    "P1 |[X]|seq P2 == 
       (fsfF_induct2 (Pfun_Parallel X) (SP_step_Parallel X) P1 P2)"

(*------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------*)

lemma fsfF_Parallel_in_lm:
  "[| ALL a:A1. Pf1 a : fsfF_proc; 
      ALL a:A2. Pf2 a : fsfF_proc; 
      ALL a:A1 Int A2. SPf a : fsfF_proc;
      ALL a:A1. SPf1 a : fsfF_proc; 
      ALL a:A2. SPf2 a : fsfF_proc;
      Q1 = SKIP | Q1 = DIV | Q1 = STOP; Q2 = SKIP | Q2 = DIV | Q2 = STOP |]
   ==> SP_step_Parallel X A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2 : fsfF_proc"
apply (simp_all add: SP_step_Parallel_def)

(* Q1 = STOP & Q2 = STOP *)
apply (case_tac "Q1 = STOP & Q2 = STOP")
apply (simp)
apply (rule fsfF_proc.intros)
apply (rule ballI)
apply (simp split: if_split)
apply (intro conjI ballI impI)
apply (simp_all)
apply (simp add: fsfF_Int_choice_in)

(* Q1 = STOP *)
apply (subgoal_tac "~ (Q1 = STOP & Q2 = STOP)")
apply (simp (no_asm_simp))
apply (case_tac "Q1 = STOP")
apply (simp)
apply (rule fsfF_Timeout_in)

apply (rule fsfF_proc.intros)
apply (rule ballI)
apply (simp split: if_split)
apply (intro conjI ballI impI)
apply (simp_all)
apply (simp add: fsfF_Int_choice_in)
apply (rule fsfF_Parallel_SKIP_DIV_in)

apply (simp add: fsfF_proc.intros)
apply (simp)

(* Q2 = STOP *)
apply (case_tac "Q2 = STOP")
apply (simp)
apply (rule fsfF_Timeout_in)

apply (rule fsfF_proc.intros)
apply (rule ballI)
apply (simp split: if_split)
apply (intro conjI ballI impI)
apply (simp_all)
apply (simp add: fsfF_Int_choice_in)
apply (rule fsfF_Parallel_SKIP_DIV_in)
apply (simp add: fsfF_proc.intros)
apply (simp)

(* Q1 = SKIP | DIV , Q2 = SKIP | DIV *)
apply (rule fsfF_Timeout_in)

apply (rule fsfF_proc.intros)
apply (rule ballI)
apply (simp split: if_split)
apply (intro conjI ballI impI)
apply (simp_all)
apply (simp add: fsfF_Int_choice_in)

apply (rule fsfF_Int_choice_in)
apply (rule fsfF_Parallel_SKIP_DIV_in)
apply (simp add: fsfF_proc.intros)
apply (simp)

apply (rule fsfF_Parallel_SKIP_DIV_in)
apply (simp add: fsfF_proc.intros)
apply (simp)
done

(*------------------------------------*
 |                 in                 |
 *------------------------------------*)

lemma fsfF_Parallel_in:
    "[| P1 : fsfF_proc ; P2 : fsfF_proc |]
     ==> P1 |[X]|seq P2 : fsfF_proc"
apply (simp add: fsfF_Parallel_def)
apply (rule fsfF_induct2_in)
apply (simp_all)
apply (simp add: fsfF_Parallel_in_lm)
done

(*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*)

lemma cspF_fsfF_Parallel_eqF:
    "P1 |[X]| P2 =F P1 |[X]|seq P2"
apply (simp add: fsfF_Parallel_def)
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_induct2_eqF[THEN cspF_sym])
apply (simp_all add: Pfun_Parallel_def)
apply (rule cspF_Dist_nonempty, simp)
apply (rule cspF_Dist_nonempty, simp)

apply (simp add: SP_step_Parallel_def)

(* Q1 = STOP & Q2 = STOP *)
apply (case_tac "Q1 = STOP & Q2 = STOP")
apply (simp)

apply (rule cspF_rw_right)
apply (rule cspF_unit)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_unit)
apply (rule cspF_unit)

apply (rule cspF_rw_left)
apply (rule cspF_step)
apply (rule cspF_decompo)
apply (simp)

apply (simp split: if_split)
apply (intro conjI impI)
apply (simp)

apply (rule cspF_rw_left, rule cspF_IF)+

apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])

 apply (rule cspF_decompo)
 apply (rule cspF_decompo)
 apply (simp)
 apply (simp)
 apply (rule cspF_rw_right)
 apply (rule cspF_unit)
 apply (rule cspF_reflex)

 apply (rule cspF_decompo)
 apply (simp)
 apply (simp)
 apply (rule cspF_rw_right)
 apply (rule cspF_unit)
 apply (rule cspF_reflex)
 apply (rule cspF_reflex)

apply (rule cspF_rw_left, rule cspF_IF)+
apply (rule cspF_rw_right)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_reflex)
 apply (rule cspF_unit)
 apply (rule cspF_reflex)

apply (rule cspF_rw_left, rule cspF_IF)+
apply (rule cspF_rw_right)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_unit)
 apply (rule cspF_reflex)
 apply (rule cspF_reflex)

apply (rule cspF_rw_left, rule cspF_IF)+
apply (rule cspF_rw_right)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_unit)
 apply (rule cspF_reflex)
 apply (rule cspF_reflex)

(* Q1 = STOP *)
apply (simp (no_asm_simp))
apply (case_tac "Q1 = STOP")
apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_Ext_choice_unit)
apply (rule cspF_reflex)

apply (rule cspF_rw_left)
apply (rule cspF_SKIP_or_DIV_resolve)
apply (fast)

apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Timeout_eqF[THEN cspF_sym])
apply (rule cspF_decompo)
apply (rule cspF_decompo)

apply (rule cspF_rw_right)
apply (rule cspF_unit)
apply (rule cspF_decompo)
apply (simp)

(* IF --> if *)
apply (simp split: if_split)
apply (intro conjI impI)
apply (simp)

apply (rule cspF_rw_left, rule cspF_IF)+
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])

 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_rw_right)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_unit)
 apply (rule cspF_reflex)
 apply (rule cspF_reflex)

apply (rule cspF_rw_left, rule cspF_IF)+
 apply (rule cspF_reflex)

apply (rule cspF_rw_left, rule cspF_IF)+
apply (rule cspF_rw_right)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_unit)
 apply (rule cspF_reflex)
 apply (rule cspF_reflex)

apply (rule cspF_rw_left, rule cspF_IF)+
apply (rule cspF_rw_right)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_unit)
 apply (rule cspF_reflex)
 apply (rule cspF_reflex)

apply (rule cspF_reflex)

apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Parallel_SKIP_DIV_eqF[THEN cspF_sym])
apply (rule cspF_rw_right)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_unit)
 apply (rule cspF_reflex)
 apply (rule cspF_reflex)

(* Q2 = STOP *)
apply (case_tac "Q2 = STOP")
apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_decompo)
apply (simp)
apply (rule cspF_reflex)
apply (rule cspF_unit)

apply (rule cspF_rw_left)
apply (rule cspF_SKIP_or_DIV_resolve)
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Timeout_eqF[THEN cspF_sym])
apply (rule cspF_decompo)
apply (rule cspF_decompo)

apply (rule cspF_rw_right)
apply (rule cspF_unit)
apply (rule cspF_decompo)
apply (simp)

(* IF --> if *)
apply (simp split: if_split)
apply (intro conjI impI)
apply (simp)

apply (rule cspF_rw_left, rule cspF_IF)+
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])

 apply (rule cspF_decompo)
 apply (rule cspF_rw_right)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_reflex)
 apply (rule cspF_unit)
 apply (rule cspF_reflex)
 apply (rule cspF_reflex)

apply (rule cspF_rw_left, rule cspF_IF)+
apply (rule cspF_rw_right)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_reflex)
 apply (rule cspF_unit)
 apply (rule cspF_reflex)

apply (rule cspF_rw_left, rule cspF_IF)+
 apply (rule cspF_reflex)

apply (rule cspF_rw_left, rule cspF_IF)+
 apply (rule cspF_reflex)

apply (rule cspF_reflex)

apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Parallel_SKIP_DIV_eqF[THEN cspF_sym])
apply (rule cspF_rw_right)
 apply (rule cspF_decompo)
 apply (simp)
 apply (rule cspF_unit)
 apply (rule cspF_reflex)
 apply (rule cspF_commut)

(* DIV or SKIP *)
apply (simp)

apply (rule cspF_rw_left)
apply (rule cspF_SKIP_or_DIV_resolve)
apply (simp)
apply (simp)
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Timeout_eqF[THEN cspF_sym])
apply (rule cspF_decompo)
apply (rule cspF_decompo)

apply (rule cspF_rw_right)
apply (rule cspF_unit)
apply (rule cspF_decompo)
apply (simp)

(* IF --> if *)
apply (simp split: if_split)
apply (intro conjI impI)
apply (simp)

apply (rule cspF_rw_left, rule cspF_IF)+
apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])
apply (rule cspF_reflex)

apply (rule cspF_rw_left, rule cspF_IF)+
apply (rule cspF_reflex)

apply (rule cspF_rw_left, rule cspF_IF)+
apply (rule cspF_reflex)

apply (rule cspF_rw_left, rule cspF_IF)+
apply (rule cspF_reflex)

apply (rule cspF_reflex)

apply (rule cspF_rw_right)
apply (rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])
apply (rule cspF_decompo)

 apply (rule cspF_rw_right)
 apply (rule cspF_fsfF_Parallel_SKIP_DIV_eqF[THEN cspF_sym])
 apply (rule cspF_commut)
 apply (rule cspF_rw_right)
 apply (rule cspF_fsfF_Parallel_SKIP_DIV_eqF[THEN cspF_sym])
 apply (rule cspF_reflex)

(* congruence *)

apply (simp add: SP_step_Parallel_def)

apply (simp split: if_split)
apply (intro conjI impI)

apply (rule cspF_decompo, simp)
apply (rule cspF_decompo, simp)
apply (simp split: if_split)
apply (intro conjI impI)
apply (simp_all)
apply (rule cspF_rw_left, rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])
apply (rule cspF_rw_right, rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])
apply (rule cspF_decompo)
apply (simp_all)

apply (rule cspF_rw_left,  rule cspF_fsfF_Timeout_eqF[THEN cspF_sym])
apply (rule cspF_rw_right, rule cspF_fsfF_Timeout_eqF[THEN cspF_sym])
apply (rule cspF_Timeout_cong)
apply (rule cspF_decompo, simp)
apply (rule cspF_decompo, simp)
apply (simp split: if_split)
apply (intro conjI impI)
apply (simp_all)
apply (rule cspF_rw_left, rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])
apply (rule cspF_rw_right, rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])
apply (rule cspF_decompo)
apply (simp_all)

apply (rule cspF_rw_left,  rule cspF_fsfF_Timeout_eqF[THEN cspF_sym])
apply (rule cspF_rw_right, rule cspF_fsfF_Timeout_eqF[THEN cspF_sym])
apply (rule cspF_Timeout_cong)
apply (rule cspF_decompo, simp)
apply (rule cspF_decompo, simp)
apply (simp split: if_split)
apply (intro conjI impI)
apply (simp_all)
apply (rule cspF_rw_left, rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])
apply (rule cspF_rw_right, rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])
apply (rule cspF_decompo)
apply (simp_all)

apply (rule cspF_rw_left,  rule cspF_fsfF_Timeout_eqF[THEN cspF_sym])
apply (rule cspF_rw_right, rule cspF_fsfF_Timeout_eqF[THEN cspF_sym])
apply (rule cspF_Timeout_cong)
apply (rule cspF_decompo, simp)
apply (rule cspF_decompo, simp)
apply (simp split: if_split)
apply (intro conjI impI)
apply (simp_all)
apply (rule cspF_rw_left, rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])
apply (rule cspF_rw_right, rule cspF_fsfF_Int_choice_eqF[THEN cspF_sym])
apply (rule cspF_decompo)
apply (simp_all)
done

(****************** to add them again ******************)

declare if_split    [split]
declare disj_not1   [simp]

end
