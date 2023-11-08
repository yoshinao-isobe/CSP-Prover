theory tockCSP_RUNT
imports tockCSP_tock
        CSP.CSP_RUN
begin

definition
  RUNT :: "'a set => ('a RunName, 'a::tockCSP) proc" ("RUN\<^sub>T")
where
  "RUN\<^sub>T S == RUN(S \<union> {tock})"

end