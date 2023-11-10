           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2021         |
            |                 August 2021               |
            |                  2022 / 2023 (modified)   |
            |                                           |
            | Joabe Jesus (eComp POLI UPE and CIn UFPE) |
            *-------------------------------------------*)

theory DFP_DFrep
imports DFP_law_DFkev
begin



subsection \<open> Rep_interleave_Int_pre_choice \<close>
text \<open> The process that performs k events in INTERLEAVE \<close>

definition Rep_interleave_Int_pre_choice ::
    "(nat \<Rightarrow> 'a \<Rightarrow> 'e) \<Rightarrow> nat \<Rightarrow> ('e \<Rightarrow> ('p,'e) proc) \<Rightarrow> ('p,'e) proc" ("(1|||!<_>_ .. _)" [80,80,80] 80)
where
    "|||!<f> k .. P = ||| :[1..k] .. (\<lambda>i. ! :(f (nat i) ` UNIV) -> P)"



definition Rep_interleave_Int_pre_choice_SKIP ::
    "(nat \<Rightarrow> 'a \<Rightarrow> 'e) \<Rightarrow> nat \<Rightarrow> ('p,'e) proc" ("(1|||!<_> _)" [80,80] 80)
where
    "|||!<f> k = |||!<f> k .. (\<lambda>x. SKIP)"



subsubsection \<open> DFP Rep_interleave_Int_pre_choice \<close>

lemma dfp_Rep_interleave_Int_pre_choice :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    \<forall>i \<in> {1..n}. \<forall>x \<in> (f (nat i) ` UNIV). $DFtick <=F P x \<Longrightarrow>
    $DFtick <=F |||!<f> n .. P"
  apply (simp add: Rep_interleave_Int_pre_choice_def)
  apply (rule dfp, simp)
  apply (rule dfp)+
  apply (simp only: set_upto)
  by (force)


lemma dfp_Rep_interleave_Int_pre_choice_SKIP :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    $DFtick <=F |||!<f> n"
  apply (simp add: Rep_interleave_Int_pre_choice_SKIP_def)
  apply (rule dfp_Rep_interleave_Int_pre_choice, simp)
  by (rule dfp)+





subsection \<open> Rep_ext_choice_Int_pre_choice \<close>
text \<open> The process that chooses between k events \<close>

definition Rep_ext_choice_Int_pre_choice ::
    "(nat \<Rightarrow> 'a \<Rightarrow> 'e) \<Rightarrow> nat \<Rightarrow> ('e \<Rightarrow> ('p,'e) proc) \<Rightarrow> ('p,'e) proc" ("(1[+]!<_> _ .. _)" [80,80,80] 80)
where
    "[+]!<f> n .. P = [+] :[1..n] .. (\<lambda>i. ! :(f (nat i) ` UNIV) -> P)"

definition Rep_ext_choice_Int_pre_choice_SKIP ::
    "(nat \<Rightarrow> 'a \<Rightarrow> 'e) \<Rightarrow> nat \<Rightarrow> ('p,'e) proc" ("(1[+]!<_> _)" [80,80] 80)
where
    "[+]!<f> n = [+]!<f> n .. (\<lambda>x. SKIP)"







subsubsection \<open> DFP Rep_ext_choice_Int_pre_choice \<close>

lemma dfp_Rep_ext_choice_Int_pre_choice :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    n > 0 \<Longrightarrow>
    \<forall>i \<in> {1..n}. \<forall>x \<in> (f (nat i) ` UNIV). $DFtick <=F P x \<Longrightarrow>
    $DFtick <=F [+]!<f> n .. P"
  apply (simp add: Rep_ext_choice_Int_pre_choice_def)
  apply (rule dfp, simp, simp)
  apply (rule dfp)+
  apply (simp only: set_upto)
  by (force)


lemma dfp_Rep_ext_choice_Int_pre_choice_SKIP :
    "FPmode \<noteq> CPOmode \<Longrightarrow>
    n > 0 \<Longrightarrow>
    $DFtick <=F [+]!<f> n"
  apply (simp add: Rep_ext_choice_Int_pre_choice_SKIP_def)
  apply (rule dfp_Rep_ext_choice_Int_pre_choice, simp, simp)
  by (rule dfp)+

end