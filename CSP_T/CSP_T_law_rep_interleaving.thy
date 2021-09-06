           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2020         |
            |                  March 2021               |
            |                                           |
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021  (modified)   |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory CSP_T_law_rep_interleaving
imports CSP_T_law_decompo CSP_T_law_basic
begin

subsection \<open> Inductive interleave \<close>

(*
lemma cspT_Interleave_Act_prefix_Alpha_Par :
    "a \<noteq> b \<Longrightarrow>
     (a -> SKIP ||| b -> SKIP)
     =T [||] [ (a -> SKIP, {a}), (b -> SKIP, {b}) ]"
  apply (cspT_auto)
  apply (rule cspT_rw_right, simp add: Alpha_parallel_def)

  apply (cspT_auto)
  apply (rule cspT_rw_right)
    apply (rule cspT_decompo, simp)
    apply (rule cspT_decompo, simp)
    apply (rule cspT_Parallel_term)
    apply (rule cspT_decompo, simp)
    apply (rule cspT_decompo, simp)
    apply (rule cspT_Parallel_term)
    apply (rule cspT_reflex)
  apply (rule cspT_rw_right)
    apply (rule cspT_decompo, simp)
    apply (rule cspT_reflex)
    apply (rule cspT_decompo, simp)
    apply (rule cspT_reflex)
    apply (rule cspT_reflex)
    apply (cspT_auto)
    apply (cspT_auto)
done
*)

(*
lemma cspT_Inductive_interleave_map_cong2 :
    "\<forall>a. PXf a = PXg a \<Longrightarrow> ( ||| map PXf x) =T ( ||| map PXg x)"
  apply (induct x)
  apply (simp add: Inductive_interleave_def)
  apply (simp (no_asm) add: map_unwind)
  apply (rule cspT_decompo, simp, clarsimp)
  apply (force)
done
*)

lemma cspT_Inductive_interleave_cong :
    "x = y \<Longrightarrow> ||| x =T ||| y"
by (simp)


lemma cspT_Inductive_interleaving_Cons_cong :
    "\<lbrakk> P =T Q; ||| Ps =T ||| Qs \<rbrakk> \<Longrightarrow> ||| (P#Ps) =T ||| (Q#Qs)"
by (simp, rule cspT_decompo, simp)

lemma cspT_Inductive_interleave_map_cong :
    "\<forall>a \<in> set x. PXf a =T PXg a \<Longrightarrow> ( ||| map PXf x) =T ( ||| map PXg x)"
  apply (induct x, simp_all)
by (rule cspT_decompo, simp_all)+

lemma cspT_Inductive_interleave_map_to_List :
    "map PXf x = l \<Longrightarrow> ( ||| map PXf x) =T ( ||| l)"
by (simp)

lemma cspT_Inductive_interleave_map_to_List_Cons :
    "l \<noteq> [] \<Longrightarrow> ||| map PXf l =T ||| ( (PXf (hd l)) # map PXf (tl l) )"
  apply (rule cspT_Inductive_interleave_map_to_List)

by (induct l, simp, simp add: map_def)


lemma cspT_Subst_procfun_Inductive_interleave_map :
   "\<forall> i \<in> set l. (PXf i) << Pf =T PXf i
    \<Longrightarrow> ( ||| map PXf l) << Pf =T ( ||| map PXf l)"
  apply (induct l, simp_all)
by (rule cspT_decompo, simp_all)+


subsection \<open> Replicated interleaving \<close>

lemma cspT_Rep_interleaving_to_Inductive_interleave :
    "finite X \<Longrightarrow> l = (SOME y. y isListOf X)
     \<Longrightarrow> ||| x:X .. PXf x =T[M,M] ||| (map PXf l)"
by (simp add: Rep_interleaving_def)


lemma cspT_Rep_interleaving_cong :
    "X = Y \<Longrightarrow> ||| x:X .. PfX =T ||| y:Y .. PfX"
by (simp)

lemma cspT_Rep_interleaving_pair_cong :
    "X = Y \<Longrightarrow> ||| (a,b):X .. PfX =T ||| (c,d):Y .. PfX"
by (simp)


end