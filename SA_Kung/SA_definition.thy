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
            |                   June 2008  (modified)   |
            |                                           |
            |   on DFP on CSP-Prover ver.5.0            |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *-------------------------------------------*)

theory SA_definition
imports DFP_Main HOL.Rings
begin

(*********************************************************
                         event
 *********************************************************)

datatype 'r Event = vert "nat * nat" 'r | hori "nat * nat" 'r

(*********************************************************
                  element process
 *********************************************************)

type_synonym index_type = "nat * nat"

datatype 'r ProcName = pe "index_type" 'r | pe' "index_type" 'r 'r 'r

fun
  SAfun  :: "('r::ring) ProcName => ('r ProcName, 'r Event) proc"

where
  "SAfun (pe (i,j) r) = (vert (i,j) ? x -> hori (i,j) ? y -> $(pe' (i,j) r x y)) [+]
                        (hori (i,j) ? y -> vert (i,j) ? x -> $(pe' (i,j) r x y))"

 | "SAfun (pe' (i,j) r x y) = ((vert (i+1,j) ! x -> SKIP) ||| 
                                 (hori (i,j+1) ! y -> SKIP)) ;;
                                 $(pe (i,j) (r + x * y))"
(*
defs (overloaded)
 set_SAfun_Pnfun_def [simp]: "PNfun == SAfun"
*)

overloading Set_SAfun == 
  "PNfun :: (('r::ring) ProcName, 'r Event) pnfun"
begin
  definition "PNfun :: (('r::ring) ProcName, 'r Event) pnfun == SAfun"
end

declare Set_SAfun_def [simp]

(*
defs 
 set_FPmode_def [simp]: "FPmode == CPOmode"
*)

overloading FPmode == 
  "FPmode :: fpmode"
begin
  definition "FPmode == CPOmode"
end
declare FPmode_def [simp]

(*** fixed point ***)

lemma pe_FIX:
  "$(pe ij r) =F (FIX SAfun) (pe ij r)"
apply (rule cspF_rw_left)
apply (rule cspF_FIX)
apply (simp)+
done

(*** network ***)

fun
  Alpha_pe :: "index_type => ('r::ring) Event set"

where
  "Alpha_pe (i,j) = {a. EX x. a = vert (i  ,j) x | a = hori (i,j  ) x |
                              a = vert (i+1,j) x | a = hori (i,j+1) x }"

declare Alpha_pe.simps [simp del]

definition
  Array_Index :: "nat => index_type set"
  where
  Array_Index_def : "Array_Index N == {(i,j)|i j. i < N & j < N}"

definition
  Systolic_Array :: "nat => (index_type,('r::ring) ProcName,'r Event) Network"
  where
  Systolic_Array_def: 
  "Systolic_Array N == 
   { ($(pe (i,j) 0), Alpha_pe (i,j)) | (i,j) : (Array_Index N)}net"


(*---------------------------------*
 | Failures sets of Systolic_Array |
 *---------------------------------*)

(*** out term ***)

definition
  Faiures_out_hori :: "('r::ring) => index_type
                         => 'r Event failure set => 'r Event failure set"
  where
  Faiures_out_hori_def :
  "Faiures_out_hori y ==
   (%(i,j). (%F.
      {(<>, {Ev a |a. EX z. (a = vert (i,j) z | a = hori (i,j) z | a = vert (i+1,j) z |
                              (a = hori (i,j+1) z & z ~= y))})} Un
      {(<Ev (hori (i,j+1) y)> ^^^ s, Y) |s Y. (s, Y) : F}))"
                         
definition
  Faiures_out_vert :: "('r::ring) => index_type
                         => 'r Event failure set => 'r Event failure set"
  where
  Faiures_out_vert_def :
  "Faiures_out_vert x ==
   (%(i,j). (%F.
      {(<>, {Ev a |a. EX z. (a = hori (i,j) z | a = vert (i,j) z | a = hori (i,j+1) z |
                              (a = vert (i+1,j) z & z ~= x))})} Un
      {(<Ev (vert (i+1,j) x)> ^^^ s, Y) |s Y. (s, Y) : F}))"

definition
  Faiures_out:: "('r::ring) => 'r => index_type 
                         => 'r Event failure set => 'r Event failure set"
  where
  Faiures_out_def :
  "Faiures_out x y ==
   (%(i,j). (%F.
      {(<>, {Ev a |a. EX z. (a = hori (i,j) z | a = vert (i,j) z |
                              (a = hori (i,j+1) z & z ~= y) |
                              (a = vert (i+1,j) z & z ~= x))})} Un
      {(<Ev (vert (i+1,j) x)> ^^^ s, Y) |s Y. (s, Y) : Faiures_out_hori y (i,j) F} Un
      {(<Ev (hori (i,j+1) y)> ^^^ s, Y) |s Y. (s, Y) : Faiures_out_vert x (i,j) F}))"

(*** in term ***)

definition
  Faiures_in_hori :: "('r::ring) => index_type
                       => 'r Event failure set => 'r Event failure set"
  where
  Faiures_in_hori_def :
  "Faiures_in_hori x ==
   (%(i,j) F.
      {(<>, {Ev a |a. EX x. (a = vert (i,j) x | a = hori (i,j+1) x | 
                              a = vert (i+1,j) x)})} Un
      {(<Ev (hori (i,j) y)> ^^^ s, Y) |y s Y. (s, Y) : Faiures_out x y (i,j) F})"

definition
  Faiures_in_vert :: "('r::ring) => index_type
                       => 'r Event failure set => 'r Event failure set"
  where
  Faiures_in_vert_def :
  "Faiures_in_vert y ==
   (%(i,j) F.
      {(<>, {Ev a |a. EX x. (a = hori (i,j) x | a = vert (i+1,j) x | 
                              a = hori (i,j+1) x)})} Un
      {(<Ev (vert (i,j) x)> ^^^ s, Y) |x s Y. (s, Y) : Faiures_out x y (i,j) F})"

definition
  Faiures_in      :: "index_type => ('r::ring) Event failure set => 'r Event failure set"
  where
  Faiures_in_def :
  "Faiures_in ==
   (%(i,j) F.
      {(<>, {Ev a |a. EX x. (a = vert (i+1,j) x | a = hori (i,j+1) x)})} Un
      {(<Ev (vert (i,j) x)> ^^^ s, Y) |x s Y. (s, Y) : Faiures_in_hori x (i,j) F} Un
      {(<Ev (hori (i,j) y)> ^^^ s, Y) |y s Y. (s, Y) : Faiures_in_vert y (i,j) F})"

(*** induction ***)

primrec
  peF_rec :: "nat => index_type => ('r::ring) Event failure set"
where
  "peF_rec 0       = (%ij. {})"
 |"peF_rec (Suc n) = (%ij. Faiures_in ij (peF_rec n ij))"

definition
  peF     :: "index_type => ('r::ring) Event failure set"
  where
   peF_def : "peF ij == Union {peF_rec n ij |n. True}"

(*** NetworkF ***)

definition
  Systolic_ArrayF :: "nat => (index_type, ('r::ring) Event) NetworkF"
  where
  Systolic_ArrayF_def: 
  "Systolic_ArrayF == 
   (%N. { (peF ij, Alpha_pe ij) | ij : (Array_Index N)}Fnet)"

(******************************************************************
                        small lemmas 
 ******************************************************************)

(* index *)

lemma Example1_index_mem:
  "ij : Array_Index N = (EX i j. ij = (i,j) & i < N & j < N)"
apply (simp add: Array_Index_def)
by (auto)

(****************** to add it again ******************)

end
