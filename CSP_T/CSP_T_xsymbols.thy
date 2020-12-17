           (*-------------------------------------------*
            |        X symbols for CSP-Prover           |
            |                   June 2008  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_T_xsymbols
imports Domain_T CSP_T_semantics
begin

(*------------------------------------*
 |                                    |
 |             Domain_T               |
 |                                    |
 *------------------------------------*)

notation (xsymbols) memT ("(_/ \<in>t _)" [50, 51] 50)
notation (xsymbols) UnionT ("\<Union>t _" [90] 90)
notation (xsymbols) InterT ("\<Inter>t _" [90] 90)

notation (xsymbols) nonmemT ("(_/ \<notin>t _)" [50, 51] 50)
notation (xsymbols) UnT  ("_ \<union>t _" [65,66] 65)
notation (xsymbols) IntT ("_ \<inter>t _" [70,71] 70)

(*------------------------------------*
 |                                    |
 |           CSP_T_semantics          |
 |                                    |
 *------------------------------------*)

notation (xsymbols) semTf   ("\<lbrakk>_\<rbrakk>Tf")
notation (xsymbols) semTfun ("\<lbrakk>_\<rbrakk>Tfun")

notation (xsymbols) semTfix ("\<lbrakk>_\<rbrakk>Tfix")
notation (xsymbols) semT ("\<lbrakk>_\<rbrakk>T")

notation (xsymbols) refT ("(0_ /\<sqsubseteq>T[_,_] /_)" [51,0,0,50] 50)
notation (xsymbols) refTfix ("(0_ /\<sqsubseteq>T /_)" [51,50] 50)

end
