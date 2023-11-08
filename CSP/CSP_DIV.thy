theory CSP_DIV
imports CSP_syntax
begin



section \<open> Div \<close>

datatype DivPN = Div

primrec DivPNfun :: "(DivPN, 'a) pnfun"
where
    "DivPNfun (Div) = ? x:{} -> $Div"


overloading Set_DivPNfun == 
  "CSP_syntax.PNfun :: (DivPN, 'a) pnfun"
begin                                           
  definition "(CSP_syntax.PNfun::(DivPN, 'a) pnfun) == DivPNfun"
end

declare Set_DivPNfun_def [simp]




subsection \<open> Guardedness \<close>

(*FIXME?: Is Ext pre choice: ? x:{} -> Pf really guarded? *)
lemma guarded_DivPNfun [simp]: "\<forall>p. guarded (DivPNfun p)"
by (rule, case_tac p, simp)

lemma guardedfun_DivPNfun [simp]: "guardedfun DivPNfun"
by (simp add: guardedfun_def)






section \<open> DIV according to Hoare \<close>


datatype DivHPN = DivH

primrec DivHPNfun :: "(DivHPN, 'a) pnfun"
where
    "DivHPNfun (DivH) = (SKIP ;; $DivH)"


overloading Set_DivHPNfun == 
  "CSP_syntax.PNfun :: (DivHPN, 'a) pnfun"
begin                                           
  definition "(CSP_syntax.PNfun::(DivHPN, 'a) pnfun) == DivHPNfun"
end

declare Set_DivHPNfun_def [simp]


(*
class tauCSP =
    fixes tau :: "'a" ("\<tau>")
      and nontau :: "'a"
  assumes Diff_tau_nontau : "tau \<noteq> nontau"

primrec DivPNfun :: "(DivPN, 'a::tauCSP) pnfun"
where
    "DivPNfun (Div) = (nontau -> $Div) -- {nontau}"


overloading Set_DivPNfun == 
  "PNfun :: (DivPN, 'a::tauCSP) pnfun"
begin                                           
  definition "(PNfun::(DivPN, 'a::tauCSP) pnfun) == DivPNfun"
end

declare Set_DivPNfun_def [simp]
*)


subsection \<open> Guardedness \<close>

lemma not_guarded_DivHPNfun [simp]: "\<forall>p. \<not> guarded (DivHPNfun p)"
by (rule, case_tac p, simp)

lemma not_guardedfun_DivHPNfun [simp]: "\<not> guardedfun DivHPNfun"
by (simp add: guardedfun_def)



end