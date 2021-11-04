(* Author: Andreas Lochbihler, ETH Zurich & Digital Asset *)

theory Max_Flow_Min_Cut_Countable imports
  MFMC_Bounded
  MFMC_Unbounded
begin

section \<open>The Max-Flow Min-Cut theorem\<close>

theorem max_flow_min_cut_countable:
  fixes \<Delta> (structure)
  assumes countable_E [simp]: "countable \<^bold>E"
  and source_neq_sink [simp]: "source \<Delta> \<noteq> sink \<Delta>"
  and capacity_outside: "\<forall>e. e \<notin> \<^bold>E \<longrightarrow> capacity \<Delta> e = 0"
  and capacity_finite [simp]: "\<forall>e. capacity \<Delta> e \<noteq> \<top>"
  shows "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
proof -
  interpret countable_network \<Delta> using assms by(unfold_locales) auto
  show ?thesis by(rule max_flow_min_cut)
qed

hide_const (open) A B weight

end
