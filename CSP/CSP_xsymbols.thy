           (*-------------------------------------------*
            |        CSP-Prover on Isabelle2008         |
            |                   June 2008  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory CSP_xsymbols
imports Infra_type CSP_syntax Trace RS
begin

(*------------------------------------*
 |                                    |
 |              X-Symbols             |
 |                                    |
 *------------------------------------*)

(*------------------------------------*
 |                                    |
 |             Infra_type             |
 |                                    |
 *------------------------------------*)

notation (xsymbols) sum_cup_mix ("_ \<union>s _" [65,66] 65)
notation (xsymbols) sum_cap_mix ("_ \<inter>s _" [70,71] 70)

notation (xsymbols) nilt ("\<langle>\<rangle>")
notation (xsymbols) appt (infixr "\<frown>" 65)

syntax (output)
  "_traceX"     :: "args => 'a trace"                       ("<(_)>")

syntax (xsymbols)
  "_traceX"     :: "args => 'a trace"       ("\<langle>(_)\<rangle>" [900] 1000)

translations
  "\<langle>s\<rangle>"  == "<s>"

(*------------------------------------*
 |                                    |
 |                Trace               |
 |                                    |
 *------------------------------------*)

notation (xsymbols) Tick ("\<surd>")

(*------------------------------------*
 |                                    |
 |                  RS                |
 |                                    |
 *------------------------------------*)

notation (xsymbols) restriction ("_ \<down> _" [84,900] 84)

(*------------------------------------*
 |                                    |
 |             CSP_syntax             |
 |                                    |
 *------------------------------------*)

syntax (output)
  "_PrefixX"         :: "'a => ('p,'a) proc => ('p,'a) proc"
                                   ("(1_ /-> _)" [150,80] 80)
  "_Ext_pre_choiceX" :: "pttrn => 'a set => ('p,'a) proc => ('p,'a) proc"  
                                   ("(1? _:_ /-> _)" [900,900,80] 80)
  "_Ext_choiceX"     :: "('p,'a) proc => ('p,'a) proc => ('p,'a) proc"
                                   ("(1_ /[+] _)" [72,73] 72)
  "_Int_choiceX"     :: "('p,'a) proc => ('p,'a) proc => ('p,'a) proc"
                                   ("(1_ /|~| _)" [64,65] 64)
  "_Int_pre_choiceX" :: "pttrn => 'a set => ('p,'a) proc => ('p,'a) proc"  
                                   ("(1! _:_ /-> _)" [900,900,80] 80)

syntax (xsymbols)
  "_PrefixX"         :: "'a => ('p,'a) proc => ('p,'a) proc"
                          ("(1_ /\<rightarrow> _)" [150,80] 80)
  "_Ext_pre_choiceX" :: "pttrn => 'a set => ('p,'a) proc => ('p,'a) proc"  
                          ("(1? _:_ /\<rightarrow> _)" [900,900,80] 80)
  "_Ext_choiceX"     :: "('p,'a) proc => ('p,'a) proc => ('p,'a) proc"
                          ("(1_ /\<box> _)" [72,73] 72)
  "_Int_choiceX"     :: "('p,'a) proc => ('p,'a) proc => ('p,'a) proc"
                          ("(1_ /\<sqinter> _)" [64,65] 64)

  "_Int_pre_choiceX" :: "pttrn => 'a set => ('p,'a) proc => ('p,'a) proc"  
                          ("(1! _:_ /\<rightarrow> _)" [900,900,80] 80)

translations
  "a \<rightarrow> P"     == "a -> P"
  "? x:X \<rightarrow> P" == "? x:X -> P"
  "P \<box> Q"            == "P [+] Q"
  "P \<sqinter> Q"        == "P |~| Q"
  "! x:X \<rightarrow> P" == "! x:X -> P"

syntax (output)
  "_Nondet_send_prefixX"      :: "('x => 'a) => pttrn => 'x set => 
                                  ('p,'a) proc => ('p,'a) proc"
                                  ("(1_ !? _:_ /-> _)" [900,900,1000,80] 80)
  "_Nondet_send_prefix_UNIVX" :: "('x => 'a) => pttrn => ('p,'a) proc => ('p,'a) proc"
                               ("(1_ !? _ /-> _)" [900,900,80] 80)

  "_Send_prefixX"     :: "('x => 'a) => 'x => ('p,'a) proc => ('p,'a) proc" 
                          ("(1_ ! _ /-> _)" [900,1000,80] 80)

  "_Rec_prefixX"      :: "('x => 'a) => pttrn => 'x set => 
                          ('p,'a) proc => ('p,'a) proc"
                          ("(1_ ? _:_ /-> _)" [900,900,1000,80] 80)
  "_Rec_prefix_UNIVX" :: "('x => 'a) => pttrn =>
                          ('p,'a) proc => ('p,'a) proc"
                          ("(1_ ? _ /-> _)" [900,900,80] 80)

syntax (xsymbols)
  "_Nondet_send_prefixX"      :: "('x => 'a) => pttrn => 'x set => 
                                  ('p,'a) proc => ('p,'a) proc"
                               ("(1_ !? _:_ /\<rightarrow> _)" [900,900,1000,80] 80)
  "_Nondet_send_prefix_UNIVX" :: "('x => 'a) => pttrn => ('p,'a) proc => ('p,'a) proc"
                               ("(1_ !? _ /\<rightarrow> _)" [900,900,80] 80)

  "_Send_prefixX"     :: "('x => 'a) => 'x => ('p,'a) proc => ('p,'a) proc" 
                          ("(1_ ! _ /\<rightarrow> _)" [900,1000,80] 80)

  "_Rec_prefixX"      :: "('x => 'a) => pttrn => 'x set => 
                          ('p,'a) proc => ('p,'a) proc"
                          ("(1_ ? _:_ /\<rightarrow> _)" [900,900,1000,80] 80)
  "_Rec_prefix_UNIVX" :: "('x => 'a) => pttrn =>
                          ('p,'a) proc => ('p,'a) proc"
                          ("(1_ ? _ /\<rightarrow> _)" [900,900,80] 80)

translations
  "a !? x:X \<rightarrow> P" == "a !? x:X -> P"
  "a !? x \<rightarrow> P"   == "a !? x:(CONST UNIV) \<rightarrow> P"

  "a ! x \<rightarrow> P"    == "a ! x -> P"
  "a ? x:X \<rightarrow> P"  == "a ? x:X -> P"
  "a ? x \<rightarrow> P"    == "a ? x:(CONST UNIV) \<rightarrow> P"

syntax (output)
  "_TimeoutX"   :: "('p,'a) proc => ('p,'a) proc 
                 => ('p,'a) proc"  ("(1_ /[> _)" [73,74] 73)
  "_TimeoutdefX" :: "('p,'a) proc => ('p,'a) proc 
                 => ('p,'a) proc"  ("(1_ /[>def _)" [73,74] 73)
  "_InterruptX":: "('p,'a) proc => 'a => ('p,'a) proc 
                 => ('p,'a) proc"  ("(1_ /'/>_ _)" [68,150,69] 68)
  "_HidingX"    :: "('p,'a) proc => 'a set => ('p,'a) proc"  
                                        ("(1_ /-- _)" [84,85] 84)
  "_RenamingX"  :: "('p,'a) proc => ('a * 'a) set => ('p,'a) proc"  
                                        ("(1_ /[[_]])" [84,0] 84)
  "_Depth_rest" :: "('p,'a) proc => ('p,'a) proc 
                 => ('p,'a) proc"   ("(1_ /|. _)" [84,900] 84)

syntax (xsymbols)
  "_TimeoutX"   :: "('p,'a) proc => ('p,'a) proc 
                 => ('p,'a) proc"  ("(1_ /\<rhd> _)" [73,74] 73)
  "_TimeoutdefX":: "('p,'a) proc => ('p,'a) proc 
                 => ('p,'a) proc"  ("(1_ /\<unrhd> _)" [73,74] 73)
  "_InterruptX":: "('p,'a) proc => 'a => ('p,'a) proc 
                 => ('p,'a) proc"  ("(1_ /\<triangle>_ _)" [68,150,69] 68)
  "_HidingX"    :: "('p,'a) proc => 'a set => ('p,'a) proc"  
                                   ("(1_ /\<midarrow> _)" [84,85] 84)
  "_RenamingX"  :: "('p,'a) proc => ('a * 'a) set => ('p,'a) proc"  
                                        ("(1_ /\<lbrakk>_\<rbrakk>)" [84,0] 84)
  "_Depth_rest" :: "('p,'a) proc => ('p,'a) proc 
                 => ('p,'a) proc"   ("(1_ /\<lfloor> _)" [84,900] 84)

translations
(*"P \<rhd> Q"            == "(P |~| STOP) [+] Q"*)
  "P \<rhd> Q"            == "P [> Q"
  "P \<unrhd> Q"            == "P [>def Q"
  "P \<triangle>i Q"           == "P />i Q"
  "P \<midarrow> X"            == "P -- X"
  "P \<lbrakk>r\<rbrakk>"             == "P [[r]]"
  "P \<lfloor> n"             == "P |. n"


end
