theory CSP_CHAOS
imports CSP_syntax
begin


subsection \<open> Guardedness \<close>

lemma guarded_Chaosfun [simp]: "\<forall>p. guarded (Chaosfun p)"
  by (rule, case_tac p, simp)

lemma guardedfun_Chaosfun [simp]: "guardedfun Chaosfun"
  by (simp add: guardedfun_def)

declare Set_Chaosfun_def [simp]


end