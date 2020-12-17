           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                   July 2005               |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2011         |
            |                  April 2011  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2012         |
            |               November 2012  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2013         |
            |                   June 2013  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2018         |
            |               February 2019  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2020         |
            |                  April 2020  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

chapter CSP

session CSP in CSP = HOL +
  description "
    CSP Logic.
  "
  theories
    CSP (global)
    CSP_Main (global)

session CSP_T in CSP_T = CSP +
  description "
    CSP_T Logic.
  "
  theories
    CSP_T (global)
    CSP_T_Main (global)

session CSP_F in CSP_F = CSP_T +
  description "
    CSP_F Logic.
  "
  theories
    CSP_F (global)
    CSP_F_Main (global)
    
session DFP in DFP = CSP_F +
  description "
    DFP Logic.
  "
  theories
    DFP (global)
    DFP_Main (global)

session FNF_F in FNF_F = CSP_F +
  description "
    FNF_F Logic.
  "
  theories
    FNF_F (global)
    FNF_F_Main (global)
    