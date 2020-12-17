           (*-------------------------------------------*
            |    Example 1 [Roscoe_Dathi_1987 P.10]     |
            |  Self-timed version of a systolic array   |
            |                   June 2005               |
            |               December 2005  (modified)   |
            |                                           |
            |   on DFP on CSP-Prover ver.3.0            |
            |              September 2006  (modified)   |
            |                                           |
            |   on DFP on CSP-Prover ver.4.0            |
            |                  April 2007  (modified)   |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory SA_expanding
imports SA_definition
begin

declare inj_on_def [simp]

(* this is automatically used in simplifying (inv (vert (i, j)) (vert (i,j))) *)

(*********************************************************
              Element process expanding
 *********************************************************)

(* in *)

lemma pe_expand_in:
   "(FIX[Suc (Suc (n + n))] SAfun) (pe (i,j) r)
  =F ? a:(range (vert (i, j)) Un range (hori (i, j)))
   -> IF (a:range (vert (i, j)))
      THEN (? b:range (hori (i, j)) ->
     (FIX[Suc (n + n)] SAfun) (pe' (i, j) r (inv (vert (i, j)) a) (inv (hori (i, j)) b)))
      ELSE (? b:range (vert (i, j)) -> 
     (FIX[Suc (n + n)] SAfun) (pe' (i, j) r (inv (vert (i, j)) b) (inv (hori (i, j)) a)))" 
apply (simp add: FIXn_def)
apply (simp add: Subst_procfun_prod_def)

apply (simp add: csp_prefix_ss_def)
apply (cspF_hsf_left)+
apply (rule cspF_decompo)
apply (simp)
apply (simp)
apply (erule disjE)
apply (simp add: image_iff, elim exE)
apply (cspF_simp)+
apply (simp add: image_iff, elim exE)
apply (cspF_simp)+
done

(* out *)

lemma pe_expand_out:
   "(FIX[Suc (n + n)] SAfun) (pe' (i, j) r x y)
    =F 
    ? a:{vert (Suc i, j) x, hori (i, Suc j) y}
      -> (IF (a = vert (Suc i, j) x) 
          THEN (? z:{hori (i, Suc j) y} -> (FIX[n + n] SAfun) (pe (i,j) (r + x * y)))
          ELSE (? z:{vert (Suc i, j) x} -> (FIX[n + n] SAfun) (pe (i,j) (r + x * y))))"
apply (simp add: FIXn_def Subst_procfun_prod_def)
apply (simp add: csp_prefix_ss_def)
apply (cspF_hsf_left)+
apply (rule cspF_decompo)
apply (fast)
apply (cspF_simp)+
apply (erule disjE)
apply (cspF_simp)+
apply (cspF_hsf_left)+

apply (cspF_simp)
done

(*********************************************************
                  alphabet lemma
 *********************************************************)

lemma EX1_isFailureOf_in_alpha1:
"(<>, Ev ` Alpha_pe (i, j) - Ev ` (range (vert (i, j)) Un range (hori (i, j))))
= (<>, {Ev a |a. EX x. a = vert (Suc i, j) x | a = hori (i, Suc j) x})"
by (auto simp add: Alpha_pe.simps)

lemma EX1_isFailureOf_in_alpha2:
"({(<Ev (vert (i, j) x)> ^^^ s, Y) |x s Y.
           (s, Y) : Faiures_in_hori x (i, j) F} Un
          {(<Ev (hori (i, j) y)> ^^^ s, Y) |y s Y.
           (s, Y) : Faiures_in_vert y (i, j) F}) =
{(<Ev a> ^^^ s, Y) |a s Y.
          (s, Y)
          : (if a : range (vert (i, j))
             then Faiures_in_hori (inv (vert (i, j)) a) (i, j) F
             else Faiures_in_vert (inv (hori (i, j)) a) (i, j) F) &
          a : range (vert (i, j)) Un range (hori (i, j))}"
apply (auto)
apply (rule_tac x="vert (i, j) x" in exI)
apply (simp)
done

lemma EX1_isFailureOf_in_hori_alpha1:
  "(<>, {Ev a |a.
                 EX x. a = vert (i, j) x |
                       a = hori (i, Suc j) x | a = vert (Suc i, j) x})
 = (<>, Ev ` Alpha_pe (i, j) - Ev ` range (hori (i, j)))"
by (auto simp add: Alpha_pe.simps)

lemma EX1_isFailureOf_in_hori_alpha2:
  "{(<Ev (hori (i, j) y)> ^^^ s, Y) |y s Y.
          (s, Y) : Faiures_out (inv (vert (i, j)) a) y (i, j) F} =
  {(<Ev aa> ^^^ s, Y) |aa s Y.
          (s, Y) : Faiures_out (inv (vert (i, j)) a) (inv (hori (i, j)) aa) (i, j) F &
          aa : range (hori (i, j))}"
apply (auto)
done

lemma EX1_isFailureOf_in_vert_alpha1:
  "(<>, {Ev a |a.
          EX x. a = hori (i, j) x | a = vert (Suc i, j) x | a = hori (i, Suc j) x})
   = (<>, Ev ` Alpha_pe (i, j) - Ev ` range (vert (i, j)))"
by (auto simp add: Alpha_pe.simps)

lemma EX1_isFailureOf_in_vert_alpha2:
  "{(<Ev (vert (i, j) x)> ^^^ s, Y) |x s Y.
          (s, Y) : Faiures_out x (inv (hori (i, j)) a) (i, j) F} =
   {(<Ev aa> ^^^ s, Y) |aa s Y.
          (s, Y) : Faiures_out (inv (vert (i, j)) aa) (inv (hori (i, j)) a) (i, j) F &
          aa : range (vert (i, j))}"
apply (auto)
done

lemma EX1_isFailureOf_out_alpha1:
   "(<>, {Ev a |a.
           EX z. a = hori (i, j) z |
                 a = vert (i, j) z |
                 a = hori (i, Suc j) z & z ~= y | a = vert (Suc i, j) z & z ~= x})
  = (<>, Ev ` Alpha_pe (i, j) - Ev ` {vert (Suc i, j) x, hori (i, Suc j) y})"
by (auto simp add: Alpha_pe.simps)

lemma EX1_isFailureOf_out_alpha2:
"({(<Ev (vert (Suc i, j) x)> ^^^ s, Y) |s Y.
           (s, Y) : Faiures_out_hori y (i, j) F} Un
          {(<Ev (hori (i, Suc j) y)> ^^^ s, Y) |s Y.
           (s, Y) : Faiures_out_vert x (i, j) F}) =
{(<Ev a> ^^^ s, Y) |a s Y.
          (s, Y)
          : (if a : range (vert (Suc i, j)) then Faiures_out_hori y (i, j) F
             else Faiures_out_vert x (i, j) F) &
          a : {vert (Suc i, j) x, hori (i, Suc j) y}}"
by (auto simp add: image_iff)

(*********************************************************
                  isFailureOf
 *********************************************************)

(*** out ***)

lemma EX1_isFailureOf_out_hori:
   "ALL (r::'r::ring). peF_rec n (i, j) <=EX
           failures((FIX[n + n] SAfun) (pe (i, j) r)) MF
           restRefusal (Ev ` Alpha_pe (i, j))
         ==> Faiures_out_hori y (i, j) (peF_rec n (i, j))
             <=EX
             failures (
               IF True 
               THEN (? z:{hori (i, Suc j) y} 
                     -> (FIX[n + n] SAfun) (pe (i, j) ((r::'r::ring) + x * y)))
               ELSE (? z:{vert (Suc i, j) x} 
                     -> (FIX[n + n] SAfun) (pe (i, j) (r + x * y)))) MF
             restRefusal (Ev ` Alpha_pe (i, j))"
apply (rule cspF_subseteqEX_Ext_pre_choice [of _ _ _ _ _  "(%b. peF_rec n (i, j))"])
apply (cspF_simp_left)
apply (simp add: Faiures_out_hori_def)
apply (auto simp add: Alpha_pe.simps)
done


lemma EX1_isFailureOf_out_vert:
    "ALL (r::'r::ring). peF_rec n (i, j) <=EX
             failures((FIX[n + n] SAfun) (pe (i, j) r)) MF
             restRefusal (Ev ` Alpha_pe (i, j))
         ==> Faiures_out_vert x (i, j) (peF_rec n (i, j))
             <=EX
             failures (
               IF False 
               THEN (? z:{hori (i, Suc j) y} 
                     -> (FIX[n + n] SAfun) (pe (i, j) ((r::'r::ring) + x * y)))
               ELSE (? z:{vert (Suc i, j) x} 
                     -> (FIX[n + n] SAfun) (pe (i, j) (r + x * y)))) MF
             restRefusal (Ev ` Alpha_pe (i, j))"
apply (rule cspF_subseteqEX_Ext_pre_choice [of _ _ _ _ _  "(%b. peF_rec n (i, j))"])
apply (cspF_simp_left)
apply (simp add: Faiures_out_vert_def)
apply (auto simp add: Alpha_pe.simps)
done

lemma EX1_isFailureOf_out:
      "ALL (r::'r::ring).
          peF_rec n (i, j) <=EX
          failures((FIX[n + n] SAfun) (pe (i, j) r)) MF
          restRefusal (Ev ` Alpha_pe (i, j))
       ==> Faiures_out x y (i, j) (peF_rec n (i, j))
           <=EX
           failures((FIX[Suc (n + n)] SAfun) (pe' (i, j) (r::'r::ring) x y)) MF
           restRefusal (Ev ` Alpha_pe (i, j))"
apply (simp add: Faiures_out_def)
apply (rule cspF_subseteqEX_Ext_pre_choice [of _ _ _ _ _ 
 "(%a. if (a : range (vert (Suc i, j)))
       then Faiures_out_hori y (i, j) (peF_rec n (i, j))
       else Faiures_out_vert x (i, j) (peF_rec n (i, j)))"])
apply (rule pe_expand_out)
apply (simp only: EX1_isFailureOf_out_alpha1 EX1_isFailureOf_out_alpha2)

apply (rule ballI)
apply (simp)
apply (erule disjE)
apply (simp)
apply (simp add: EX1_isFailureOf_out_hori)
apply (subgoal_tac "a ~: range (vert (Suc i, j))")
apply (simp add: EX1_isFailureOf_out_vert)
by (auto)

(*** in ***)

lemma EX1_isFailureOf_in_hori:
   "[| ALL (r::'r::ring). 
         peF_rec n (i, j) <=EX
         failures((FIX[n + n] SAfun) (pe (i, j) r)) MF
         restRefusal (Ev ` Alpha_pe (i, j)) ;
          a : range (vert (i, j)) |]
       ==> Faiures_in_hori (inv (vert (i, j)) a) (i, j) (peF_rec n (i, j))
           <=EX
           failures(
             IF True 
             THEN (? b:range (hori (i, j)) 
                   -> (FIX[Suc (n + n)] SAfun)
                       (pe' (i, j) (r::'r::ring) (inv (vert (i, j)) a)
                         (inv (hori (i, j)) b))) 
             ELSE (? b:range (vert (i, j)) 
                   -> (FIX[Suc (n + n)] SAfun)
                       (pe' (i, j) r (inv (vert (i, j)) b)
                         (inv (hori (i, j)) a)))) MF
           restRefusal (Ev ` Alpha_pe (i, j))"
apply (rule cspF_subseteqEX_Ext_pre_choice [of _ _ _ _ _ 
 "(%b. Faiures_out (inv (vert (i, j)) a) (inv (hori (i, j)) b) (i, j) 
       (peF_rec n (i, j)))"])
apply (cspF_simp_left)
apply (simp add: Faiures_in_hori_def)
apply (simp only: EX1_isFailureOf_in_hori_alpha1)
apply (auto)
apply (simp add: EX1_isFailureOf_out)
done

lemma EX1_isFailureOf_in_vert:
   "[| ALL (r::'r::ring). 
             peF_rec n (i, j) <=EX
             failures((FIX[n + n] SAfun) (pe (i, j) r)) MF
             restRefusal (Ev ` Alpha_pe (i, j)) ;
            a : range (hori (i, j)); a ~: range (vert (i, j)) |]
         ==> Faiures_in_vert (inv (hori (i, j)) a) (i, j) (peF_rec n (i, j))
             <=EX
             failures(
               IF False 
               THEN (? b:range (hori (i, j)) 
                     -> (FIX[Suc (n + n)] SAfun)
                         (pe' (i, j) (r::'r::ring) (inv (vert (i, j)) a)
                           (inv (hori (i, j)) b))) 
               ELSE (? b:range (vert (i, j)) 
                     -> (FIX[Suc (n + n)] SAfun)
                         (pe' (i, j) r (inv (vert (i, j)) b)
                           (inv (hori (i, j)) a)))) MF
             restRefusal(Ev ` Alpha_pe (i, j))"
apply (rule cspF_subseteqEX_Ext_pre_choice [of _ _ _ _ _ 
 "(%b. Faiures_out (inv (vert (i, j)) b) (inv (hori (i, j)) a) (i, j) 
       (peF_rec n (i, j)))"])
apply (cspF_simp_left)
apply (simp add: Faiures_in_vert_def)
apply (simp only: EX1_isFailureOf_in_vert_alpha1 EX1_isFailureOf_in_vert_alpha2)
apply (auto)
apply (simp add: EX1_isFailureOf_out)
done

lemma EX1_isFailureOf_in:
      "ALL (r::'r::ring). peF_rec n (i, j)
              <=EX failures((FIX[n + n] SAfun) (pe (i,j) r)) MF
                   restRefusal (Ev ` Alpha_pe (i, j))
       ==> Faiures_in (i, j) (peF_rec n (i, j))
           <=EX failures((FIX[Suc (Suc (n + n))] SAfun) (pe (i,j) (r::'r::ring))) MF
                restRefusal(Ev ` Alpha_pe (i, j))"
apply (simp add: Faiures_in_def)
apply (rule cspF_subseteqEX_Ext_pre_choice [of _ _ _ _ _ 
 "(%a. if (a : range (vert (i, j)))
       then Faiures_in_hori (inv (vert (i, j)) a) (i, j) (peF_rec n (i, j))
       else Faiures_in_vert (inv (hori (i, j)) a) (i, j) (peF_rec n (i, j)))"])
apply (rule pe_expand_in)
apply (simp only: EX1_isFailureOf_in_alpha1 EX1_isFailureOf_in_alpha2)

apply (intro ballI)
apply (simp)
apply (erule disjE)
apply (simp)
apply (simp add: EX1_isFailureOf_in_hori)
apply (subgoal_tac "a ~: range (vert (i, j))")
apply (simp)
apply (simp add:  EX1_isFailureOf_in_vert)
by (auto)

lemma EX1_isFailureOf_in_ALL:
      "ALL (r::'r::ring). peF_rec n (i, j)
              <=EX failures((FIX[n + n] SAfun) (pe (i,j) r)) MF
                   restRefusal (Ev ` Alpha_pe (i, j))"
apply (induct_tac n)
apply (simp add: FIXn_def)
apply (rule allI)
apply (simp)
apply (simp add: EX1_isFailureOf_in[simplified])
done

(*** main ***)

lemma EX1_isFailureOf:
   "(Systolic_ArrayF N) isFailureOf (Systolic_Array N)"
apply (simp add: isFailureOf_def)
apply (simp add: Systolic_Array_def Systolic_ArrayF_def)
apply (rule ballI)
apply (subgoal_tac "$(pe i 0) =F 
      (!nat n .. ((FIX[n + n] SAfun) (pe i 0)))")
apply (rule cspF_subseteqEX_eqF)
apply (simp)
apply (rule cspF_subseteqEX_Rep_int_choice_nat_UNIV)
apply (rule cspF_decompo)
apply (simp_all)
apply (rule cspF_reflex)
apply (subgoal_tac "peF i = Union {peF_rec n i |n. True}")
apply (simp)
apply (simp add: peF_def)

apply (rule allI)
apply (simp add: Example1_index_mem)
apply (elim conjE exE)
apply (simp add: EX1_isFailureOf_in_ALL)

apply (rule cspF_rw_left)
apply (rule pe_FIX)
apply (simp add: cspF_FIX_plus_eq)
done

declare inj_on_def [simp del]

end
