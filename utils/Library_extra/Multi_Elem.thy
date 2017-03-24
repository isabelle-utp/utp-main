(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: Multi_Elem.thy                                                       *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Axiomatising Types with multiple elements *}

theory Multi_Elem
imports Main
begin

class one_elem =
  fixes elem1 :: 'a

class one_elem_uniq = one_elem +
  assumes "x = elem1"

class two_elem = one_elem +
  fixes elem2 :: 'a
  assumes elem1_neq_elem2: "elem1 \<noteq> elem2"
begin

lemma elem1_new_elem2_dest [dest]:
  "elem1 = elem2 \<Longrightarrow> False"
  "elem2 = elem1 \<Longrightarrow> False"
  by (metis elem1_neq_elem2)+

end

class three_elem = two_elem +
  fixes elem3 :: 'a
  assumes "elem1 \<noteq> elem3"
  and     "elem2 \<noteq> elem3"

text {* Relational identity can be distinguished from UNIV only
        for types with at least two distinct elements *}

lemma Id_neq_UNIV [simp]:
  "(Id :: ('a::two_elem rel)) \<noteq> UNIV"
  "UNIV \<noteq> (Id :: ('a::two_elem rel))"
  by (auto simp add:Id_def set_eq_iff)
end