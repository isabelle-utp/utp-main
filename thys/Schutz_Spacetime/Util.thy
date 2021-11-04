(*  Title:      Schutz_Spacetime/Util.thy
    Authors:    Richard Schmoetten, Jake Palmer and Jacques D. Fleuriot
                University of Edinburgh, 2021          
*)
theory Util
  imports Main

(* Some "utility" proofs -- little proofs that come in handy every now and then. *)

begin

text \<open>
  We need this in order to obtain a natural number which can be passed to the ordering function,
  distinct from two others, in the case of a finite set of events with cardinality a least 3.
\<close>

lemma is_free_nat:
  assumes "(m::nat) < n"
      and "n < c"
      and "c \<ge> 3"
  shows "\<exists>k::nat. k < m \<or> (m < k \<and> k < n) \<or> (n < k \<and> k < c)"
using assms by presburger

text \<open>Helpful proofs on sets.\<close>

lemma set_le_two [simp]: "card {a, b} \<le> 2"
  by (simp add: card_insert_if)

lemma set_le_three [simp]: "card {a, b, c} \<le> 3"
  by (simp add: card_insert_if)

lemma card_subset: "\<lbrakk>card Y = n; Y \<subseteq> X\<rbrakk> \<Longrightarrow> card X \<ge> n \<or> infinite X"
  using card_mono by blast

lemma card_subset_finite: "\<lbrakk>finite X; card Y = n; Y \<subseteq> X\<rbrakk> \<Longrightarrow> card X \<ge> n"
  using card_subset by auto

lemma three_subset: "\<lbrakk>x \<noteq> y; x \<noteq> z; y \<noteq> z; {x,y,z} \<subseteq> X\<rbrakk> \<Longrightarrow> card X \<ge> 3 \<or> infinite X"
  apply (case_tac "finite X")
   apply (auto simp : card_mono)
  apply (erule_tac Y = "{x,y,z}" in card_subset_finite)
  by auto

lemma card_Collect_nat:
  assumes "(j::nat)>i"
  shows "card {i..j} = j-i+1"
  using card_atLeastAtMost
  using Suc_diff_le assms le_eq_less_or_eq by presburger


text \<open>These lemmas make life easier with some of the ordering proofs.\<close>

lemma less_3_cases: "n < 3 \<Longrightarrow> n = 0 \<or> n = Suc 0 \<or> n = Suc (Suc 0)"
by auto

end