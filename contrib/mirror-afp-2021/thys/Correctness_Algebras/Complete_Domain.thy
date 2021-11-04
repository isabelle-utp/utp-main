(* Title:      Complete Domain
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Complete Domain\<close>

theory Complete_Domain

imports Relative_Domain Complete_Tests

begin

class complete_antidomain_semiring = relative_antidomain_semiring + complete_tests +
  assumes a_dist_Sum: "ascending_chain f \<longrightarrow> -(Sum f) = Prod (\<lambda>n . -f n)"
  assumes a_dist_Prod: "descending_chain f \<longrightarrow> -(Prod f) = Sum (\<lambda>n . -f n)"
begin

lemma a_ascending_chain:
  "ascending_chain f \<Longrightarrow> descending_chain (\<lambda>n . -f n)"
  by (simp add: a_antitone ascending_chain_def descending_chain_def)

lemma a_descending_chain:
  "descending_chain f \<Longrightarrow> ascending_chain (\<lambda>n . -f n)"
  by (simp add: a_antitone ord.ascending_chain_def ord.descending_chain_def)

lemma d_dist_Sum:
  "ascending_chain f \<Longrightarrow> d(Sum f) = Sum (\<lambda>n . d(f n))"
  by (simp add: d_def a_ascending_chain a_dist_Prod a_dist_Sum)

lemma d_dist_Prod:
  "descending_chain f \<Longrightarrow> d(Prod f) = Prod (\<lambda>n . d(f n))"
  by (simp add: d_def a_dist_Sum a_dist_Prod a_descending_chain)

end

end

