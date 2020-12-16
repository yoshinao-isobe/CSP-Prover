# CSP-Prover

an interactive theorem prover on the process algebra CSP based on the theorem prover Isabelle (see [the CSP-Prover's web-site](http://staff.aist.go.jp/y-isobe/CSP-Prover/CSP-Prover.html))

# Introduction

CSP-Prover[1,2,3,4] is an interactive theorem prover dedicated to refinement proofs within the process algebra CSP[5]. It aims specifically at proofs on infinite state systems, which may also involve infinite non-determinism.

# Directory

* CSP    : the reusable part of CSP-Prover
* CSP_T  : the instantiated part for T
* CSP_F  : the instantiated part for F
* FNF_F  : full normalising for F
* DFP    : (Deadlock Freedom Proof) on CSP_F, theorems given in [6]
* ep2    : an example (electronic payment system) on CSP_F
* DM     : an example (Dining Mathematicians) on CSP_F
* Test   : small examples on CSP_F
* SA_Kung: an example on DFP (Kung's Systolic array [4])
* NBuff  : an example (Linked n one-buffers)
* UCD    : an example (Uniform Candy Distribution Puzzle [3])

# Installation

This CSP-Prover needs Isabelle2020. At first, the environment-variable "CSP_PROVER_HOME" is set to the directory containing CSP, CSP_T,..., and ROOT of CSP-Prover. Then, to make heap-files of CSP, CSP_T, CSP_F, and FNF_F once, execute the command
$ `make_heap`
in this directory (CSP_PROVER_HOME). Please read ["User Guide CSP-Prover"](https://staff.aist.go.jp/y-isobe/CSP-Prover/CSP-Prover-5-0-2009/User-Guide-5-0.pdf) in [the CSP-Prover's web-site](http://staff.aist.go.jp/y-isobe/CSP-Prover/CSP-Prover.html).

# User interface

To start Iasbelle/jEdit with the logic of CSP_F, execute the following command:
$ `isabelle jedit -d '$CSP_PROVER_HOME' -l CSP_F`

# Licence agreement

Following the ideas of open source software, we allow anyone to use CSP-Prover without fee, under the CSP-Prover licence, which is similar to the Lesser Gnu Public License (LGPL). The details are given in [licence.txt](licence.txt). You have to agree with the licence before using CSP-Prover.

# X-symbols

X-symbols are used for expressing conventional CSP operators in CSP-Prover, but X-symbols may causes some warnings on syntax. Therefore, we separated the definitions of X-symbols from the main definitions and theorems, and collected them into new files `CSP_*_xsymbols`. If you do not use X-symbols of CSP-Processes, it is recommended to use the theories
  `CSP_Main, CSP_T_Main, and CSP_F_Main,`
instead of
  `CSP, CSP_T, and CSP_F`.
`CSP_*_Main` contains all the definitions and theorems of previous CSP-Prover except the definitions on X-symbols, and `CSP_*` imports `CSP_*_Main` and `CSP_*_xsymbols`.

# References

1. Y.Isobe and M.Roggenbach: A generic theorem prover of CSP refinement, TACAS 2005 (11th Inter\national Conference on Tools and Algorithms for the Construction and Analysis of Systems), LNCS 3440, Springer, pp.108-123, April 2005.

2. Y.Isobe and M.Roggenbach: A complete axiomatic semantics for the CSP stable-failures model, CONCUR 2006 (17th International Conference on Concurrency Theory), LNCS 4137, Springer, pp.158-172, August 2006.

3. Y.Isobe and M.Roggenbach: CSP-Prover -- a Proof Tool for the Verification of Scalable Concurrent Systems, Journal of Computer Software, Japan Society for Software Science and Technology (JSSST), Vol.25, No.4, pp.85--92, 2008.

4. Y.Isobe, M.Roggenbach, and S.Gruner, Extending CSP-Prover by deadlock-analysis: Towards the verification of systolic arrays, FOSE 2005 (12th Workshop on Foundation of Software Engineering), Japanese Lecture Notes Series 31, pp.257-266, Kindai-kagaku-sha, November 2005.

5. A.W.Roscoe, "The Theory and Practice of Concurrency", Prentice Hall, 1998.

6. A.W.Roscoe and N.Dathi, "The pursuit of deadlock freedom", Information and Computation, Vol.75, No.3, pp.289-327, 1987.
