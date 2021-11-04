(* Title: Examples/TTS_Foundations/Foundations/FNDS_Lifting_Set_Ext.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Extension of the theory \<^text>\<open>Lifting_Set\<close>\<close>
theory FNDS_Lifting_Set_Ext
  imports Main
begin

context
  includes lifting_syntax
begin

lemma set_pred_eq_transfer[transfer_rule]:
  assumes [transfer_rule]: "right_total A" 
  shows
    "((rel_set A ===> (=)) ===> (rel_set A ===> (=)) ===> (=)) 
      (\<lambda>X Y. \<forall>s\<subseteq>Collect (Domainp A). X s = Y s) 
      ((=)::['b set \<Rightarrow> bool, 'b set \<Rightarrow> bool] \<Rightarrow> bool)"
proof(intro rel_funI)
  let ?sA = "Collect (Domainp A)"
  fix X Y :: "'a set \<Rightarrow> bool" 
  fix X' Y' :: "'b set \<Rightarrow> bool"
  assume rs: "(rel_set A ===> (=)) X X'" "(rel_set A ===> (=)) Y Y'"
  show "(\<forall>s\<subseteq>?sA. X s = Y s) = (X' = Y')"
  proof
    assume X_eq_Y: "\<forall>s\<subseteq>?sA. X s = Y s"
    {
      fix s' assume "X' s'" 
      then obtain s where "rel_set A s s'" 
        by (meson assms right_total_def right_total_rel_set)
      then have "X s" using rs(1) unfolding rel_fun_def by (simp add: \<open>X' s'\<close>)
      moreover from \<open>rel_set A s s'\<close> have "s \<subseteq> ?sA" 
        unfolding Ball_Collect[symmetric] by (auto dest: rel_setD1)
      ultimately have "Y' s'" 
        using rs(2)[unfolded rel_fun_def] \<open>rel_set A s s'\<close> by (simp add: X_eq_Y)
    }
    note XY = this
    {
      fix s' assume "Y' s'" 
      then obtain s where "rel_set A s s'" 
        by (meson assms right_total_def right_total_rel_set)
      then have "Y s" using rs(2)[unfolded rel_fun_def] by (simp add: \<open>Y' s'\<close>)
      moreover from \<open>rel_set A s s'\<close> have "s \<subseteq> ?sA" 
        unfolding Ball_Collect[symmetric] by (auto dest: rel_setD1)
      ultimately have "X' s'" 
        using X_eq_Y rs(1)[unfolded rel_fun_def] \<open>rel_set A s s'\<close> by auto
    }
    with XY show "X' = Y'" by auto
  next
    assume "X' = Y'" show "\<forall>s\<subseteq>?sA. X s = Y s"
      unfolding Ball_Collect[symmetric]
      using rs[unfolded rel_fun_def] \<open>X' = Y'\<close> by (metis DomainpE Domainp_set)+
  qed
qed

private lemma vimage_fst_transfer_h:
  "
  pred_prod (Domainp A) (Domainp B) x = 
    (x \<in> Collect (Domainp A) \<times> Collect (Domainp B))
  "
  unfolding pred_prod_beta mem_Times_iff by simp

lemma vimage_fst_transfer[transfer_rule]: 
  assumes [transfer_rule]: "bi_unique A" "right_total A" "right_total B" 
  shows 
    "((rel_prod A B ===> A) ===> rel_set A ===> rel_set (rel_prod A B)) 
      (\<lambda>f S. (f -` S) \<inter> ((Collect (Domainp A)) \<times> (Collect (Domainp B)))) 
      vimage"
  unfolding vimage_def
  apply transfer_prover_start
  apply transfer_step+
  unfolding vimage_fst_transfer_h by auto

lemma vimage_snd_transfer[transfer_rule]: 
  assumes [transfer_rule]: "right_total A" "bi_unique B" "right_total B" 
  shows 
    "((rel_prod A B ===> B) ===> rel_set B ===> rel_set (rel_prod A B)) 
      (\<lambda>f S. (f -` S) \<inter> ((Collect (Domainp A)) \<times> (Collect (Domainp B)))) 
      vimage"
  unfolding vimage_def
  apply transfer_prover_start
  apply transfer_step+
  unfolding vimage_fst_transfer_h by auto

lemma vimage_transfer[transfer_rule]: 
  assumes [transfer_rule]: "bi_unique B" "right_total A" 
  shows 
    "((A ===> B) ===> (rel_set B) ===> rel_set A) 
      (\<lambda>f s. (vimage f s) \<inter> (Collect (Domainp A))) (-`)"
  by transfer_prover

lemma pairwise_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "((A ===> A ===> (=)) ===> rel_set A  ===> (=)) pairwise pairwise"
  unfolding pairwise_def by transfer_prover

lemma disjnt_transfer[transfer_rule]: 
  assumes [transfer_rule]: "bi_unique A"
  shows "(rel_set A ===> rel_set A  ===> (=)) disjnt disjnt"
  unfolding disjnt_def by transfer_prover

lemma bij_betw_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "bi_unique B"
  shows "((A ===> B) ===> rel_set A ===> rel_set B ===> (=)) bij_betw bij_betw"
  unfolding bij_betw_def
  apply transfer_prover_start
  apply transfer_step+
  by simp

end

text\<open>\newpage\<close>

end