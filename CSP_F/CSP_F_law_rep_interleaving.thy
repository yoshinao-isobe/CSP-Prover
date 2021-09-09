           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory CSP_F_law_rep_interleaving
imports CSP_F_law_decompo CSP_F_law_basic
begin

subsection \<open> Inductive interleave \<close>

lemma cspF_Inductive_interleave_cong :
    "x = y \<Longrightarrow> ||| x =F ||| y"
by (simp)


lemma cspF_Inductive_interleaving_Cons_cong :
    "\<lbrakk> P =F Q; ||| Ps =F ||| Qs \<rbrakk> \<Longrightarrow> ||| (P#Ps) =F ||| (Q#Qs)"
by (simp, rule cspF_decompo, simp)

lemma cspF_Inductive_interleave_map_cong :
    "\<forall>a \<in> set x. PXf a =F PXg a \<Longrightarrow> ( ||| map PXf x) =F ( ||| map PXg x)"
  apply (induct x, simp_all)
by (rule cspF_decompo, simp_all)+

lemma cspF_Inductive_interleave_map_to_List :
    "map PXf x = l \<Longrightarrow> ( ||| map PXf x) =F ( ||| l)"
by (simp)

lemma cspF_Inductive_interleave_map_to_List_Cons :
    "l \<noteq> [] \<Longrightarrow> ||| map PXf l =F ||| ( (PXf (hd l)) # map PXf (tl l) )"
  apply (rule cspF_Inductive_interleave_map_to_List)

by (induct l, simp, simp add: map_def)


lemma cspF_Subst_procfun_Inductive_interleave_map :
   "\<forall> i \<in> set l. (PXf i) << Pf =F PXf i
    \<Longrightarrow> ( ||| map PXf l) << Pf =F ( ||| map PXf l)"
  apply (induct l, simp_all)
by (rule cspF_decompo, simp_all)+




subsection \<open> Replicated interleaving \<close>

lemma cspF_Rep_interleaving_to_Inductive_interleave :
    "finite X \<Longrightarrow> l = (SOME y. y isListOf X)
     \<Longrightarrow> ||| x:X .. PXf x =F[M,M] ||| (map PXf l)"
by (simp add: Rep_interleaving_def)


lemma cspF_Rep_interleaving_cong :
    "X = Y \<Longrightarrow> ||| x:X .. PfX =F ||| y:Y .. PfX"
by (simp)

lemma cspF_Rep_interleaving_pair_cong :
    "X = Y \<Longrightarrow> ||| (a,b):X .. PfX =F ||| (c,d):Y .. PfX"
by (simp)


end