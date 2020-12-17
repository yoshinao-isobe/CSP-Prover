           (*-------------------------------------------*
            |        X symbols for CSP-Prover           |
            |                   June 2008  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_F_xsymbols
imports Set_F CSP_F_semantics
begin

(*------------------------------------*
 |                                    |
 |               Set_F                |
 |                                    |
 *------------------------------------*)

notation (xsymbols) memF ("(_/ \<in>f _)" [50, 51] 50)
notation (xsymbols) UnionF ("\<Union>f _" [90] 90)
notation (xsymbols) InterF ("\<Inter>f _" [90] 90)

notation (xsymbols) nonmemF  ("(_/ \<notin>f _)" [50, 51] 50)
notation (xsymbols) UnF      ("_ \<union>f _" [65,66] 65)
notation (xsymbols) IntF     ("_ \<inter>f _" [70,71] 70)

(*------------------------------------*
 |                                    |
 |        CSP_F_semantics             |
 |                                    |
 *------------------------------------*)

notation (xsymbols) semFf   ("\<lbrakk>_\<rbrakk>Ff")
notation (xsymbols) semFfun ("\<lbrakk>_\<rbrakk>Ffun")

notation (xsymbols) semFfix ("\<lbrakk>_\<rbrakk>Ffix")
notation (xsymbols) semF ("\<lbrakk>_\<rbrakk>F")

notation (xsymbols) refF ("(0_ /\<sqsubseteq>F[_,_] /_)" [51,100,100,50] 50)
notation (xsymbols) refFfix ("(0_ /\<sqsubseteq>F /_)" [51,50] 50)

end
