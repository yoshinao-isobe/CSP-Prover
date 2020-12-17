           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                  April 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_op_alpha_par
imports CSP_F_domain CSP_T.CSP_T_op_alpha_par
begin

(*  The following simplification rules are deleted in this theory file *)
(*  because they unexpectly rewrite (notick | t = <>)                  *)
(*                                                                     *)
(*                  disj_not1: (~ P | Q) = (P --> Q)                   *)

declare disj_not1 [simp del]

(*********************************************************
             Alphabetized Parallel eval
 *********************************************************)

lemma in_failures_Parallel_SKIP_lm1: 
  "[| Y - insert Tick (Ev ` X) = Z - insert Tick (Ev ` X) ; 
     (Tick ~: Z | Z <= Evset) |]
   ==> Z - Y <= Ev ` X"
by (auto simp add: Evset_def)

lemma in_failures_Parallel_SKIP_lm2: 
  "Y - insert Tick (Ev ` X) = Z - insert Tick (Ev ` X)  
   ==> Z - insert Tick Y <= Ev ` X"
by (auto)

(* Para SKIP *)

lemma in_failures_Parallel_SKIP:
  "(f :f failures(P |[X]| SKIP) M) = 
   (EX u Y Z. f = (u, Y Un Z) & (u, Y) :f failures(P) M & 
              sett(u) Int (Ev ` X) = {} & Z <= Ev ` X)"
apply (simp add: in_failures)
apply (rule iffI)

(* => *)
 apply (elim conjE exE)
 apply (erule disjE)

 (* t = <> *)
  apply (simp add: par_tr_nil)
  apply (elim conjE, simp)
  apply (rule_tac x="Y" in exI)
  apply (rule_tac x="Z - Y" in exI)
  apply (simp add: in_failures_Parallel_SKIP_lm1)

 (* t = <Tick> *)
  apply (simp add: par_tr_Tick)
  apply (elim conjE, simp)
  apply (case_tac "Tick ~: Z")

   apply (rule_tac x="Y" in exI)
   apply (rule_tac x="Z - Y" in exI)
   apply (simp add: in_failures_Parallel_SKIP_lm1)

   (* Tick : Z *)
   apply (rule_tac x="insert Tick Y" in exI)
   apply (rule_tac x="(Z - insert Tick Y)" in exI)
   apply (rule conjI, force)
   apply (simp add: Tick_in_sett)
   apply (erule exE)
   apply (rule conjI)
   apply (simp)
   apply (rule proc_T2_T3)
   apply (simp)
   apply (simp)
   apply (simp add: in_failures_Parallel_SKIP_lm2)

(* <= *)
 apply (elim conjE exE)
 apply (case_tac "Tick ~: sett u")

 (* t = <> *)
  apply (rule_tac x="u" in exI)
  apply (rule_tac x="Y" in exI)
  apply (rule_tac x="Z Un (Y - {Tick})" in exI)
  apply (simp)
  apply (rule conjI)
  apply (fast)
  apply (rule conjI)
  apply (fast)
  apply (rule_tac x="u" in exI)
  apply (rule_tac x="<>" in exI)
  apply (simp add: par_tr_nil)
  apply (simp add: Evset_def)
  apply (force)

 (* t = <Tick> *)
  apply (rule_tac x="u" in exI)
  apply (rule_tac x="Y" in exI)
  apply (rule_tac x="Z Un Y" in exI)
  apply (simp)
  apply (rule conjI)
  apply (fast)
  apply (rule conjI)
  apply (fast)
  apply (rule_tac x="u" in exI)
  apply (rule_tac x="<Tick>" in exI)
  apply (simp add: par_tr_Tick)
done

(*** complement ***)

lemma in_failures_Parallel_SKIP_comp:
  "(f :f failures(P |[- X]| SKIP) M) =
   (EX u Y Z. f = (u, Y Un Z) & (u, Y) :f failures(P) M & 
              sett(u) <= insert Tick (Ev ` X) & Z Int insert Tick (Ev ` X) = {})"
apply (simp add: in_failures_Parallel_SKIP)
apply (auto)
apply (rule_tac x="Y" in exI)
apply (rule_tac x="Z" in exI)
apply (simp)
apply (rule conjI)
 apply (rule subsetI)
 apply (case_tac "x : Ev ` (- X)")
 apply (fast)
 apply (simp add: notin_Ev_set)
 apply (erule disjE, simp)
 apply (force)
apply (force)

apply (rule_tac x="Y" in exI)
apply (rule_tac x="Z" in exI)
apply (auto)
apply (case_tac "x = Tick", simp)
apply (simp add: not_Tick_to_Ev)
apply (auto)
done

(*** Alpha_parallel_evalF ***)

lemma in_failures_Alpha_parallel_lm1:
  "[| Tick ~: Za ; Za Int Ev ` X1 = {}; 
      Tick ~: Zb ; Zb Int Ev ` X2 = {};
      Ya Un Za - insert Tick (Ev ` (X1 Int X2)) =
      Yb Un Zb - insert Tick (Ev ` (X1 Int X2)) |]
       ==>
       (Ya Un Za Un (Yb Un Zb)) Int insert Tick (Ev ` (X1 Un X2)) =
         (Ya Int insert Tick (Ev ` X1)) Un
         (Yb Int insert Tick (Ev ` X2))"
by (auto)

lemma in_failures_Alpha_parallel_lm2:
  "X Int insert Tick (Ev ` (X1 Un X2)) <= Y Un Z
   ==> X = X Int Ev ` (X1 - X2) Un X Int Y Int insert Tick (Ev ` (X1 Int X2)) Un
               (X - insert Tick (Ev ` X1)) Un
               (X Int Ev ` (X2 - X1) Un X Int Z Int insert Tick (Ev ` (X1 Int X2)) Un
                (X - insert Tick (Ev ` X2)))"
by (auto)

lemma in_failures_Alpha_parallel_lm3:
  "X Int Ev ` (X1 - X2) Un X Int Y Int insert Tick (Ev ` (X1 Int X2)) Un
           (X - insert Tick (Ev ` X1)) -
           insert Tick (Ev ` (X1 Int X2)) =
           X Int Ev ` (X2 - X1) Un X Int Z Int insert Tick (Ev ` (X1 Int X2)) Un
           (X - insert Tick (Ev ` X2)) -
           insert Tick (Ev ` (X1 Int X2))"
by (auto)

(* F *)

lemma in_failures_Alpha_parallel:
  "(f :f failures(P |[X1,X2]| Q) M) =
   (EX u X.
     f = (u, X) &
     (EX Y Z.
         X Int insert Tick (Ev ` (X1 Un X2)) =
         Y Int insert Tick (Ev ` X1) Un Z Int insert Tick (Ev ` X2) &
         (u rest-tr X1, Y) :f failures(P) M &
         (u rest-tr X2, Z) :f failures(Q) M & 
          sett u <= insert Tick (Ev ` (X1 Un X2))))"
apply (simp add: Alpha_parallel_def)
apply (simp add: in_failures_Parallel[of _ _ "X1 Int X2"])
apply (simp add: in_failures_Parallel_SKIP_comp)
apply (rule iffI)

(* => *)
 apply (elim conjE exE)
 apply (simp add: par_tr_rest_tr)
 apply (rule_tac x="Ya" in exI, simp)
 apply (rule_tac x="Yb" in exI, simp)
 apply (simp add: in_failures_Alpha_parallel_lm1)

(* <= *)
 apply (elim conjE exE)
 apply (simp)
 apply (rule_tac x=
   "(X Int (Ev ` (X1 - X2))) Un 
    (X Int Y Int insert Tick (Ev ` (X1 Int X2))) Un
    (X - insert Tick (Ev ` X1))" in exI)
 apply (rule_tac x=
   "(X Int (Ev ` (X2 - X1))) Un 
    (X Int Z Int insert Tick (Ev ` (X1 Int X2))) Un
    (X - insert Tick (Ev ` X2))" in exI)

(* X = Y' Un Z' *)
  apply (rule conjI)
  apply (rule in_failures_Alpha_parallel_lm2)
  apply (fast)

(* Parallel condition *)
  apply (rule conjI)
  apply (simp add: in_failures_Alpha_parallel_lm3)

(* failures *)
  apply (rule_tac x="u rest-tr X1" in exI)
  apply (rule_tac x="u rest-tr X2" in exI)
  apply (simp add: par_tr_rest_tr_if)

  apply (rule conjI)
   apply (rule_tac x=
     "(X Int (Ev ` (X1 - X2))) Un 
      (X Int Y Int insert Tick (Ev ` (X1 Int X2)))" in exI)
   apply (rule_tac x= "(X - insert Tick (Ev ` X1))" in exI)
   apply (simp)
   apply (rule conjI)
   apply (rule memF_F2)
   apply (simp)
   apply (force)
   apply (force)

   apply (rule_tac x=
     "(X Int (Ev ` (X2 - X1))) Un 
      (X Int Z Int insert Tick (Ev ` (X1 Int X2)))" in exI)
   apply (rule_tac x= "(X - insert Tick (Ev ` X2))" in exI)
   apply (simp)
   apply (rule conjI)
   apply (rule memF_F2)
   apply (simp)
   apply (force)
   apply (force)
done

(*** Semantics for alphabetized parallel on F ***)

lemma failures_Alpha_parallel:
  "failures(P |[X1,X2]| Q) = (%M.
   {f. (EX u X. f = (u, X) &
     (EX Y Z.
         X Int insert Tick (Ev ` (X1 Un X2)) =
         Y Int insert Tick (Ev ` X1) Un Z Int insert Tick (Ev ` X2) &
         (u rest-tr X1, Y) :f failures(P) M &
         (u rest-tr X2, Z) :f failures(Q) M &
          sett u <= insert Tick (Ev ` (X1 Un X2))))}f)"
apply (simp only: in_failures_Alpha_parallel[THEN sym])
apply (simp)
done

(****************** to add it again ******************)

declare disj_not1   [simp]

end
