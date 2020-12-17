           (*-------------------------------------------*
            |    Example 1 [Roscoe_Dathi_1987 P.10]     |
            |             WITH computation              |
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

theory SA_local
imports SA_definition
begin

(*----------------------*
 |     small lemma      |
 *----------------------*)

lemma possible_pairs:
    "{ (peF ij, Alpha_pe ij) | ij:{(i1, j1), (i2, j2)} }Fnet >> 
       (i1, j1) --[(t, Yf), Lambda]-->o (i2, j2)
     ==> (i1 = i2 & j1 = Suc j2)
       | (i1 = i2 & j2 = Suc j1)
       | (i1 = Suc i2 & j1 = j2)
       | (i2 = Suc i1 & j1 = j2)"
apply (simp add: isUngrantedRequestOfwrt_def)
apply (simp add: isUngrantedRequestOf_def)
apply (simp add: isRequestOf_def)
apply (simp add: isStateOf_def)
apply (simp add: Alpha_pe.simps)
apply (auto)
done

(*--------------------------------*
 |       local calculation        |
 *--------------------------------*)

(*** i j hori ***)

lemma local_i_j_hori_ALL:
   "ALL s. ((s, Yf (i, j)) : peF_rec n (i, j) & 
            (EX x. Ev (hori (i,Suc j) x) ~: Yf (i,j)))
    --> Suc (Suc (4 * lengtht (s rest-tr (range(hori (i, Suc j)))))) <= lengtht s"
apply (induct_tac n)
apply (simp)

apply (intro allI impI)
apply (simp add: Faiures_in_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_in_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_in_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
done

lemma local_i_j_hori:
   "[| (s, Yf (i, j)) : peF (i, j) ; 
       EX x. Ev (hori (i, Suc j) x) ~: Yf (i, j) |]
    ==> Suc (Suc (4 * lengtht (s rest-tr (range (hori (i, Suc j)))))) <= lengtht s"
apply (simp add: peF_def)
apply (elim conjE exE, simp)
apply (insert local_i_j_hori_ALL[of Yf i j])
by (auto)

(*** i (Suc j) hori ***)

lemma local_i_Suc_j_hori_ALL:
   "ALL s. ((s, Yf (i, Suc j)) : peF_rec n (i, Suc j) & 
       (ALL x. Ev (hori (i,Suc j) x) : Yf (i,Suc j)))
    --> Suc (lengtht s) <= 4 * lengtht (s rest-tr (range (hori (i, Suc j))))"
apply (induct_tac n)
apply (simp)

apply (intro allI impI)
apply (simp add: Faiures_in_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_in_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_in_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
done

lemma local_i_Suc_j_hori:
   "[| (s, Yf (i, Suc j)) : peF (i, Suc j) ;
       ALL x. Ev (hori (i,Suc j) x) : Yf (i,Suc j) |]
    ==> Suc (lengtht s) <= 4 * lengtht (s rest-tr (range (hori (i, Suc j))))"
apply (simp add: peF_def)
apply (elim conjE exE, simp)
apply (insert local_i_Suc_j_hori_ALL[of Yf i j])
by (simp)

(*** i j vert ***)

lemma local_i_j_vert_ALL:
   "ALL s. ((s, Yf (i, j)) : peF_rec n (i, j) & 
            (EX x. Ev (vert (Suc i, j) x) ~: Yf (i,j)))
    --> Suc (Suc (4 * lengtht (s rest-tr (range(vert (Suc i, j)))))) <= lengtht s"
apply (induct_tac n)
apply (simp)

apply (intro allI impI)
apply (simp add: Faiures_in_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_in_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_in_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
done

lemma local_i_j_vert:
   "[| (s, Yf (i, j)) : peF (i, j) ; EX x. Ev (vert (Suc i, j) x) ~: Yf (i,j) |]
    ==> Suc (Suc (4 * lengtht (s rest-tr (range (vert (Suc i, j)))))) <= lengtht s"
apply (simp add: peF_def)
apply (elim conjE exE, simp)
apply (insert local_i_j_vert_ALL[of Yf i j])
by (auto)

(*** (Suc i) j vert ***)

lemma local_Suc_i_j_vert_ALL:
   "ALL s. ((s, Yf (Suc i, j)) : peF_rec n (Suc i, j) & 
            (ALL x. Ev (vert (Suc i, j) x) : Yf (Suc i, j)))
    --> Suc (lengtht s) <= 4 * lengtht (s rest-tr (range (vert (Suc i, j))))"
apply (induct_tac n)
apply (simp)

apply (intro allI impI)
apply (simp add: Faiures_in_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_in_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_in_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
done

lemma local_Suc_i_j_vert:
   "[| (s, Yf (Suc i, j)) : peF (Suc i, j) ;
       ALL x. Ev (vert (Suc i, j) x) : Yf (Suc i, j) |]
    ==> Suc (lengtht s) <= 4 * lengtht (s rest-tr (range (vert (Suc i, j))))"
apply (simp add: peF_def)
apply (elim conjE exE, simp)
apply (insert local_Suc_i_j_vert_ALL[of Yf i j])
by (simp)

(****** reverse ******)

(*** i j hori ***)

lemma local_i_j_hori_rev_ALL:
   "ALL s. ((s, Yf (i, j)) : peF_rec n (i, j) & 
            (ALL x. Ev (hori (i,Suc j) x) : Yf (i,j)))
    -->  lengtht s <= (Suc (4 * lengtht (s rest-tr (range (hori (i, Suc j))))))"
apply (induct_tac n)
apply (simp)

apply (intro allI impI)
apply (simp add: Faiures_in_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_in_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE)
apply (force)
apply (simp add: Faiures_out_hori_def)
apply (force)
apply (simp add: Faiures_out_vert_def)
apply (force)

apply (simp add: Faiures_in_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE)
apply (force)
apply (simp add: Faiures_out_hori_def)
apply (force)
apply (simp add: Faiures_out_vert_def)
apply (force)
done

lemma local_i_j_hori_rev:
   "[| (s, Yf (i, j)) : peF (i, j) ; 
       ALL x. Ev (hori (i,Suc j) x) : Yf (i,j) |]
    ==> lengtht s <= (Suc (4 * lengtht (s rest-tr (range (hori (i, Suc j))))))"
apply (simp add: peF_def)
apply (elim conjE exE, simp)
apply (insert local_i_j_hori_rev_ALL[of Yf i j])
by (simp)

(*** i (Suc j) hori ***)

lemma local_i_Suc_j_hori_rev_ALL:
   "ALL s. ((s, Yf (i, Suc j)) : peF_rec n (i, Suc j) & 
            (EX x. Ev (hori (i,Suc j) x) ~: Yf (i,Suc j)))
    --> 4 * lengtht (s rest-tr (range (hori (i, Suc j)))) <= lengtht s"
apply (induct_tac n)
apply (simp)

apply (intro allI impI)
apply (simp add: Faiures_in_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_in_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_in_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
done

lemma local_i_Suc_j_hori_rev:
   "[| (s, Yf (i, Suc j)) : peF (i, Suc j) ;
       EX x. Ev (hori (i,Suc j) x) ~: Yf (i,Suc j) |]
    ==> 4 * lengtht (s rest-tr (range (hori (i, Suc j)))) <= lengtht s"
apply (simp add: peF_def)
apply (elim conjE exE, simp)
apply (insert local_i_Suc_j_hori_rev_ALL[of Yf i j])
by (auto)

(*** i j vert ***)

lemma local_i_j_vert_rev_ALL:
   "ALL s. ((s, Yf (i, j)) : peF_rec n (i, j) & 
           (ALL x. Ev (vert (Suc i, j) x) : Yf (i,j)))
    -->  lengtht s <= (Suc (4 * lengtht (s rest-tr (range (vert (Suc i, j))))))"
apply (induct_tac n)
apply (simp)

apply (intro allI impI)
apply (simp add: Faiures_in_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_in_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE)
apply (force)
apply (simp add: Faiures_out_hori_def)
apply (force)
apply (simp add: Faiures_out_vert_def)
apply (force)

apply (simp add: Faiures_in_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE)
apply (force)
apply (simp add: Faiures_out_hori_def)
apply (force)
apply (simp add: Faiures_out_vert_def)
apply (force)
done

lemma local_i_j_vert_rev:
   "[| (s, Yf (i, j)) : peF (i, j) ; ALL x. Ev (vert (Suc i, j) x) : Yf (i,j) |]
    ==> lengtht s <= (Suc (4 * lengtht (s rest-tr (range (vert (Suc i, j))))))"
apply (simp add: peF_def)
apply (elim conjE exE, simp)
apply (insert local_i_j_vert_rev_ALL[of Yf i j])
by (simp)

(*** (Suc i) j vert ***)

lemma local_Suc_i_j_vert_rev_ALL:
   "ALL s. ((s, Yf (Suc i, j)) : peF_rec n (Suc i, j) & 
            (EX x. Ev (vert (Suc i, j) x) ~: Yf (Suc i, j)))
    --> 4 * lengtht (s rest-tr (range (vert (Suc i, j)))) <= lengtht s"
apply (induct_tac n)
apply (simp)

apply (intro allI impI)
apply (simp add: Faiures_in_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_in_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_in_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)

apply (simp add: Faiures_out_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_hori_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
apply (simp add: Faiures_out_vert_def)
apply (elim disjE conjE exE, simp_all add: image_iff)
done

lemma local_Suc_i_j_vert_rev:
   "[| (s, Yf (Suc i, j)) : peF (Suc i, j) ;
       EX x. Ev (vert (Suc i, j) x) ~: Yf (Suc i, j) |]
    ==> 4 * lengtht (s rest-tr (range (vert (Suc i, j)))) <= lengtht s"
apply (simp add: peF_def)
apply (elim conjE exE, simp)
apply (insert local_Suc_i_j_vert_rev_ALL[of Yf i j])
by (auto)

(*---------------------------------------*
 |  ungranted request --> Yf properties  |
 *---------------------------------------*)

(* hori *)

lemma EX1_request_hori:
  "(Ev ` Alpha_pe (i, j) - Yf (i, j)) Int Ev ` Alpha_pe (i, Suc j) ~= {}
   ==> EX x. Ev (hori (i, Suc j) x) ~: Yf (i, j)"
by (auto simp add: Alpha_pe.simps)

lemma EX1_ungranted_hori_lm1:
  "[| (Ev ` Alpha_pe (i, j) - Yf (i, j)) Int Ev ` Alpha_pe (i, Suc j) ~= {} ;
       Ev ` Alpha_pe (i, j) Int Ev ` Alpha_pe (i, Suc j) <= Yf (i, j) Un Yf (i, Suc j) |]
   ==> EX x. Ev (hori (i, Suc j) x) : Yf (i, Suc j)"
by (auto simp add: Alpha_pe.simps)

lemma EX1_ungranted_hori_lm2:
  "ALL n x. (Ev (hori (i, Suc j) x) : Yf (i, Suc j) &
    (EX t. (t , Yf (i, Suc j)) : peF_rec n (i, Suc j)))
   --> (ALL x. Ev (hori (i, Suc j) x) : Yf (i, Suc j))"
apply (intro allI)
apply (induct_tac n)
apply (simp)
apply (intro allI impI)

apply (simp)
apply (simp add: Faiures_in_def)
apply (elim conjE exE disjE)
apply (force)                            (* contra *)

 (* hori *)
 apply (simp add: Faiures_in_hori_def)
 apply (elim conjE exE disjE)
 apply (force)                            (* contra *)
 apply (simp add: Faiures_out_def)
 apply (elim conjE exE disjE)
 apply (force)                            (* okay *)

  apply (simp add: Faiures_out_hori_def)
  apply (elim conjE exE disjE)
  apply (force)                            (* okay *)
  apply (force)                            (* induction *)

  apply (simp add: Faiures_out_vert_def)
  apply (elim conjE exE disjE)
  apply (force)                            (* okay *)
  apply (force)                            (* induction *)

 (* vert *)
 apply (simp add: Faiures_in_vert_def)
 apply (elim conjE exE disjE)
 apply (force)                            (* contra *)
 apply (simp add: Faiures_out_def)
 apply (elim conjE exE disjE)
 apply (force)                            (* okay *)

  apply (simp add: Faiures_out_hori_def)
  apply (elim conjE exE disjE)
  apply (force)                            (* okay *)
  apply (force)                            (* induction *)

  apply (simp add: Faiures_out_vert_def)
  apply (elim conjE exE disjE)
  apply (force)                            (* okay *)
  apply (force)                            (* induction *)
done

lemma EX1_ungranted_hori:
  "[| (Ev ` Alpha_pe (i, j) - Yf (i, j)) Int Ev ` Alpha_pe (i, Suc j) ~= {} ;
       Ev ` Alpha_pe (i, j) Int Ev ` Alpha_pe (i, Suc j) <= Yf (i, j) Un Yf (i, Suc j) ;
       (t , Yf (i, Suc j)) : peF (i, Suc j) |]
   ==> (ALL x. Ev (hori (i, Suc j) x) : Yf (i, Suc j))"
apply (insert EX1_ungranted_hori_lm1[of i j Yf])
apply (simp add: peF_def)
apply (elim conjE exE)
apply (simp)
apply (insert EX1_ungranted_hori_lm2[of i j Yf])
apply (drule_tac x="n" in spec)
apply (drule_tac x="xa" in spec)
apply (drule mp)
by (auto)

(* vert *)

lemma EX1_request_vert:
  "(Ev ` Alpha_pe (i, j) - Yf (i, j)) Int Ev ` Alpha_pe (Suc i, j) ~= {}
   ==> EX x. Ev (vert (Suc i, j) x) ~: Yf (i, j)"
by (auto simp add: Alpha_pe.simps)

lemma EX1_ungranted_vert_lm1:
  "[| (Ev ` Alpha_pe (i, j) - Yf (i, j)) Int Ev ` Alpha_pe (Suc i, j) ~= {} ;
       Ev ` Alpha_pe (i, j) Int Ev ` Alpha_pe (Suc i, j) <= Yf (i, j) Un Yf (Suc i, j) |]
   ==> EX x. Ev (vert (Suc i, j) x) : Yf (Suc i, j)"
by (auto simp add: Alpha_pe.simps)

lemma EX1_ungranted_vert_lm2:
  "ALL n x. (Ev (vert (Suc i, j) x) : Yf (Suc i, j) &
    (EX t. (t , Yf (Suc i, j)) : peF_rec n (Suc i, j)))
   --> (ALL x. Ev (vert (Suc i, j) x) : Yf (Suc i, j))"
apply (intro allI)
apply (induct_tac n)
apply (simp)
apply (intro allI impI)

apply (simp)
apply (simp add: Faiures_in_def)
apply (elim conjE exE disjE)
apply (force)                            (* contra *)

 (* hori *)
 apply (simp add: Faiures_in_hori_def)
 apply (elim conjE exE disjE)
 apply (force)                            (* okay *)
 apply (simp add: Faiures_out_def)
 apply (elim conjE exE disjE)
 apply (force)                            (* okay *)

  apply (simp add: Faiures_out_hori_def)
  apply (elim conjE exE disjE)
  apply (force)                            (* okay *)
  apply (force)                            (* induction *)

  apply (simp add: Faiures_out_vert_def)
  apply (elim conjE exE disjE)
  apply (force)                            (* okay *)
  apply (force)                            (* induction *)

 (* vert *)
 apply (simp add: Faiures_in_vert_def)
 apply (elim conjE exE disjE)
 apply (force)                            (* contra *)
 apply (simp add: Faiures_out_def)
 apply (elim conjE exE disjE)
 apply (force)                            (* okay *)

  apply (simp add: Faiures_out_hori_def)
  apply (elim conjE exE disjE)
  apply (force)                            (* okay *)
  apply (force)                            (* induction *)

  apply (simp add: Faiures_out_vert_def)
  apply (elim conjE exE disjE)
  apply (force)                            (* okay *)
  apply (force)                            (* induction *)
done

lemma EX1_ungranted_vert:
  "[| (Ev ` Alpha_pe (i, j) - Yf (i, j)) Int Ev ` Alpha_pe (Suc i, j) ~= {} ;
       Ev ` Alpha_pe (i, j) Int Ev ` Alpha_pe (Suc i, j) <= Yf (i, j) Un Yf (Suc i, j) ;
       (t , Yf (Suc i, j)) : peF (Suc i, j) |]
   ==> (ALL x. Ev (vert (Suc i, j) x) : Yf (Suc i, j))"
apply (insert EX1_ungranted_vert_lm1[of i j Yf])
apply (simp add: peF_def)
apply (elim conjE exE)
apply (simp)
apply (insert EX1_ungranted_vert_lm2[of i j Yf])
apply (drule_tac x="n" in spec)
apply (drule_tac x="xa" in spec)
apply (drule mp)
by (auto)

(* hori rev *)

lemma EX1_request_hori_rev:
  "(Ev ` Alpha_pe (i, Suc j) - Yf (i, Suc j)) Int Ev ` Alpha_pe (i, j) ~= {}
   ==> EX x. Ev (hori (i, Suc j) x) ~: Yf (i, Suc j)"
by (auto simp add: Alpha_pe.simps)

lemma EX1_request_hori_rev_ALL:
  "[| (Ev ` Alpha_pe (i, Suc j) - Yf (i, Suc j)) Int Ev ` Alpha_pe (i, j) ~= {} ;
      (t , Yf (i, Suc j)) : peF (i, Suc j) |]
   ==> ALL x. Ev (hori (i, Suc j) x) ~: Yf (i, Suc j)"
apply (case_tac "ALL x. Ev (hori (i, Suc j) x) ~: Yf (i, Suc j)", simp_all)
apply (simp add: peF_def)
apply (elim conjE exE)
apply (insert EX1_ungranted_hori_lm2[of i j Yf])
apply (drule_tac x="n" in spec)
apply (drule_tac x="xa" in spec)
apply (drule mp, fast)
apply (insert EX1_request_hori_rev[of i j Yf])
apply (simp)
done

lemma EX1_ungranted_hori_rev:
  "[| (Ev ` Alpha_pe (i, Suc j) - Yf (i, Suc j)) Int Ev ` Alpha_pe (i, j) ~= {} ;
       Ev ` Alpha_pe (i, Suc j) Int Ev ` Alpha_pe (i, j) <= Yf (i, Suc j) Un Yf (i, j) ;
       (t , Yf (i, Suc j)) : peF (i, Suc j) |]
   ==> ALL x. Ev (hori (i, Suc j) x) : Yf (i, j)"
apply (insert EX1_request_hori_rev_ALL[of i j Yf t])
by (auto simp add: Alpha_pe.simps)

(* vert rev *)

lemma EX1_request_vert_rev:
  "(Ev ` Alpha_pe (Suc i, j) - Yf (Suc i, j)) Int Ev ` Alpha_pe (i, j) ~= {}
   ==> EX x. Ev (vert (Suc i, j) x) ~: Yf (Suc i, j)"
by (auto simp add: Alpha_pe.simps)

lemma EX1_request_vert_rev_ALL:
  "[| (Ev ` Alpha_pe (Suc i, j) - Yf (Suc i, j)) Int Ev ` Alpha_pe (i, j) ~= {} ;
      (t , Yf (Suc i, j)) : peF (Suc i, j) |]
   ==> ALL x. Ev (vert (Suc i, j) x) ~: Yf (Suc i, j)"
apply (case_tac "ALL x. Ev (vert (Suc i, j) x) ~: Yf (Suc i, j)", simp_all)
apply (simp add: peF_def)
apply (elim conjE exE)
apply (insert EX1_ungranted_vert_lm2[of i j Yf])
apply (drule_tac x="n" in spec)
apply (drule_tac x="xa" in spec)
apply (drule mp, fast)
apply (insert EX1_request_vert_rev[of i j Yf])
apply (simp)
done

lemma EX1_ungranted_vert_rev:
  "[| (Ev ` Alpha_pe (Suc i, j) - Yf (Suc i, j)) Int Ev ` Alpha_pe (i, j) ~= {} ;
       Ev ` Alpha_pe (Suc i, j) Int Ev ` Alpha_pe (i, j) <= Yf (Suc i, j) Un Yf (i, j) ;
      (t , Yf (Suc i, j)) : peF (Suc i, j) |]
   ==> ALL x. Ev (vert (Suc i, j) x) : Yf (i, j)"
apply (insert EX1_request_vert_rev_ALL[of i j Yf t])
by (auto simp add: Alpha_pe.simps)

(*--------------------------------*
 |        making function         |
 *--------------------------------*)

(* small calculation *)

lemma EX1_cal1:
  "[| Suc (Suc (4 * x)) <= y0 ; Suc y1 <= 4 * x |]
   ==> Suc (Suc y1) < y0"
by (auto)

lemma EX1_cal1_rev:
  "[| 4 * x <= y1 ; y0 <= Suc (4 * x) |]
   ==> y0 < Suc (Suc y1)"
by (auto)

(****** hori ******)

lemma local_hori_lm:
  "[| { (peF ij, Alpha_pe ij) | ij:{(i, j), (i, Suc j)} }Fnet >>
      (i, j) --[(t, Yf),
                VocabularyOf({ (peF ij, Alpha_pe ij) | ij:Array_Index N }Fnet)]-->o 
      (i, Suc j) |]
   ==> Suc (Suc (4 * lengtht (t rest-tr (range (hori (i, Suc j))))))
       <= lengtht (t rest-tr (Alpha_pe (i, j))) &
       Suc (lengtht (t rest-tr (Alpha_pe (i, Suc j))))
       <= 4 * lengtht (t rest-tr (range (hori (i, Suc j))))"
apply (simp add: isUngrantedRequestOfwrt_def)
apply (simp add: isUngrantedRequestOf_def)
apply (simp add: isRequestOf_def)
apply (simp add: isStateOf_def)
apply (elim conjE)

apply (insert local_i_j_hori[of "t rest-tr (Alpha_pe (i, j))" Yf i j])
apply (insert local_i_Suc_j_hori[of "t rest-tr (Alpha_pe (i, Suc j))" Yf i j])
apply (simp add: EX1_ungranted_hori EX1_request_hori)

apply (subgoal_tac 
   "t rest-tr (Alpha_pe (i, j)) rest-tr (range (hori (i, Suc j)))
  = t rest-tr (range (hori (i, Suc j)))")
apply (subgoal_tac 
  "t rest-tr (Alpha_pe (i, Suc j)) rest-tr (range (hori (i, Suc j)))
 = t rest-tr (range (hori (i, Suc j)))")
apply (simp)
apply (rule rest_tr_of_rest_tr_subset)
apply (simp add: Alpha_pe.simps image_iff, force)
apply (rule rest_tr_of_rest_tr_subset)
apply (simp add: Alpha_pe.simps image_iff, force)
done

(* local_hori *)

lemma local_hori:
  "[| { (peF ij, Alpha_pe ij) | ij:{(i, j), (i, Suc j)} }Fnet >>
      (i, j) --[(t, Yf),
                VocabularyOf({ (peF ij, Alpha_pe ij) | ij:Array_Index N }Fnet)]-->o 
      (i, Suc j) |]
   ==> Suc (Suc (lengtht (t rest-tr (Alpha_pe (i, Suc j)))))
       < lengtht (t rest-tr (Alpha_pe (i, j)))"
apply (rule EX1_cal1[of "lengtht (t rest-tr (range (hori (i, Suc j))))"])
apply (simp_all add: local_hori_lm)
done

(****** vert ******)

lemma local_vert_lm:
  "[| { (peF ij, Alpha_pe ij) | ij:{(i, j), (Suc i, j)} }Fnet >>
      (i, j) --[(t, Yf),
                VocabularyOf({ (peF ij, Alpha_pe ij) | ij:Array_Index N }Fnet)]-->o 
      (Suc i, j) |]
   ==> Suc (Suc (4 * lengtht (t rest-tr (range (vert (Suc i, j))))))
       <= lengtht (t rest-tr (Alpha_pe (i, j))) &
       Suc (lengtht (t rest-tr (Alpha_pe (Suc i, j))))
       <= 4 * lengtht (t rest-tr (range (vert (Suc i, j))))"
apply (simp add: isUngrantedRequestOfwrt_def)
apply (simp add: isUngrantedRequestOf_def)
apply (simp add: isRequestOf_def)
apply (simp add: isStateOf_def)
apply (elim conjE)

apply (insert local_i_j_vert[of "t rest-tr (Alpha_pe (i, j))" Yf i j])
apply (insert local_Suc_i_j_vert[of "t rest-tr (Alpha_pe (Suc i, j))" Yf i j])
apply (simp add: EX1_ungranted_vert EX1_request_vert)

apply (subgoal_tac 
   "t rest-tr (Alpha_pe (i, j)) rest-tr (range (vert (Suc i, j)))
  = t rest-tr (range (vert (Suc i, j)))")
apply (subgoal_tac 
  "t rest-tr (Alpha_pe (Suc i, j)) rest-tr (range (vert (Suc i, j)))
 = t rest-tr (range (vert (Suc i, j)))")
apply (simp)
apply (rule rest_tr_of_rest_tr_subset)
apply (simp add: Alpha_pe.simps image_iff, force)
apply (rule rest_tr_of_rest_tr_subset)
apply (simp add: Alpha_pe.simps image_iff, force)
done

(* local_vert *)

lemma local_vert:
  "[| { (peF ij, Alpha_pe ij) | ij:{(i, j), (Suc i, j)} }Fnet >>
      (i, j) --[(t, Yf),
                VocabularyOf({ (peF ij, Alpha_pe ij) | ij:Array_Index N }Fnet)]-->o 
      (Suc i, j) |]
   ==> Suc (Suc (lengtht (t rest-tr (Alpha_pe (Suc i, j)))))
       < lengtht (t rest-tr (Alpha_pe (i, j)))"
apply (rule EX1_cal1[of "lengtht (t rest-tr (range (vert (Suc i, j))))"])
apply (simp_all add: local_vert_lm)
done

(****** hori rev ******)

lemma local_hori_rev_lm:
  "[| { (peF ij, Alpha_pe ij) | ij:{(i, Suc j), (i, j)} }Fnet >>
      (i, Suc j) --[(t, Yf),
                VocabularyOf({ (peF ij, Alpha_pe ij) | ij:Array_Index N }Fnet)]-->o 
      (i, j) |]
   ==> lengtht (t rest-tr (Alpha_pe (i, j)))
       <= (Suc (4 * lengtht (t rest-tr (range (hori (i, Suc j)))))) &
       4 * lengtht (t rest-tr (range (hori (i, Suc j)))) 
       <= lengtht (t rest-tr (Alpha_pe (i, Suc j)))"
apply (simp add: isUngrantedRequestOfwrt_def)
apply (simp add: isUngrantedRequestOf_def)
apply (simp add: isRequestOf_def)
apply (simp add: isStateOf_def)
apply (elim conjE)

apply (insert local_i_j_hori_rev[of "t rest-tr (Alpha_pe (i, j))" Yf i j])
apply (insert local_i_Suc_j_hori_rev[of "t rest-tr (Alpha_pe (i, Suc j))" Yf i j])
apply (simp add: EX1_ungranted_hori_rev EX1_request_hori_rev)

apply (subgoal_tac 
   "t rest-tr (Alpha_pe (i, j)) rest-tr (range (hori (i, Suc j)))
  = t rest-tr (range (hori (i, Suc j)))")
apply (subgoal_tac 
  "t rest-tr (Alpha_pe (i, Suc j)) rest-tr (range (hori (i, Suc j)))
 = t rest-tr (range (hori (i, Suc j)))")
apply (simp)
apply (rule rest_tr_of_rest_tr_subset)
apply (simp add: Alpha_pe.simps image_iff, force)
apply (rule rest_tr_of_rest_tr_subset)
apply (simp add: Alpha_pe.simps image_iff, force)
done

(* local_hori_rev *)

lemma local_hori_rev:
  "[| { (peF ij, Alpha_pe ij) | ij:{(i, Suc j), (i, j)} }Fnet >>
      (i, Suc j) --[(t, Yf),
                VocabularyOf({ (peF ij, Alpha_pe ij) | ij:Array_Index N }Fnet)]-->o 
      (i, j) |]
   ==> lengtht (t rest-tr (Alpha_pe (i, j)))
       < Suc (Suc (lengtht (t rest-tr (Alpha_pe (i, Suc j)))))"
apply (rule EX1_cal1_rev[of "lengtht (t rest-tr (range (hori (i, Suc j))))"])
apply (simp_all add: local_hori_rev_lm)
done

(****** vert rev ******)

lemma local_vert_rev_lm:
  "[| { (peF ij, Alpha_pe ij) | ij:{(Suc i, j),(i, j)} }Fnet >>
      (Suc i, j) --[(t, Yf),
                VocabularyOf({ (peF ij, Alpha_pe ij) | ij:Array_Index N }Fnet)]-->o 
      (i, j) |]
   ==> lengtht (t rest-tr (Alpha_pe (i, j)))
       <= (Suc (4 * lengtht (t rest-tr (range (vert (Suc i, j)))))) &
       4 * lengtht (t rest-tr (range (vert (Suc i, j))))
       <= lengtht (t rest-tr (Alpha_pe (Suc i, j)))"
apply (simp add: isUngrantedRequestOfwrt_def)
apply (simp add: isUngrantedRequestOf_def)
apply (simp add: isRequestOf_def)
apply (simp add: isStateOf_def)
apply (elim conjE)

apply (insert local_i_j_vert_rev[of "t rest-tr (Alpha_pe (i, j))" Yf i j])
apply (insert local_Suc_i_j_vert_rev[of "t rest-tr (Alpha_pe (Suc i, j))" Yf i j])
apply (simp add: EX1_ungranted_vert_rev EX1_request_vert_rev)

apply (subgoal_tac 
   "t rest-tr (Alpha_pe (i, j)) rest-tr (range (vert (Suc i, j)))
  = t rest-tr (range (vert (Suc i, j)))")
apply (subgoal_tac 
  "t rest-tr (Alpha_pe (Suc i, j)) rest-tr (range (vert (Suc i, j)))
 = t rest-tr (range (vert (Suc i, j)))")
apply (simp)
apply (rule rest_tr_of_rest_tr_subset)
apply (simp add: Alpha_pe.simps image_iff, force)
apply (rule rest_tr_of_rest_tr_subset)
apply (simp add: Alpha_pe.simps image_iff, force)
done

(* local_vert_rev *)

lemma local_vert_rev:
  "[| { (peF ij, Alpha_pe ij) | ij:{(Suc i, j),(i, j)} }Fnet >>
      (Suc i, j) --[(t, Yf),
                VocabularyOf({ (peF ij, Alpha_pe ij) | ij:Array_Index N }Fnet)]-->o 
      (i, j) |]
   ==> lengtht (t rest-tr (Alpha_pe (i, j)))
       < Suc (Suc (lengtht (t rest-tr (Alpha_pe (Suc i, j)))))"
apply (rule EX1_cal1_rev[of "lengtht (t rest-tr (range (vert (Suc i, j))))"])
apply (simp_all add: local_vert_rev_lm)
done

(****************** to add it again ******************)

end
