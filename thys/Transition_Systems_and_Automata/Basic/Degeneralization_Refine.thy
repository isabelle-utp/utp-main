theory Degeneralization_Refine
imports Degeneralization Refine
begin

  lemma degen_param[param]: "(degen, degen) \<in> \<langle>S \<rightarrow> bool_rel\<rangle> list_rel \<rightarrow> S \<times>\<^sub>r nat_rel \<rightarrow> bool_rel"
  proof (intro fun_relI)
    fix cs ds ak bl
    assume "(cs, ds) \<in> \<langle>S \<rightarrow> bool_rel\<rangle> list_rel" "(ak, bl) \<in>  S \<times>\<^sub>r nat_rel"
    then show "(degen cs ak, degen ds bl) \<in> bool_rel"
      unfolding degen_def list_rel_def fun_rel_def list_all2_conv_all_nth
      by (cases "snd ak < length cs") (auto 0 3)
  qed

  lemma count_param[param]: "(Degeneralization.count, Degeneralization.count) \<in>
    \<langle>A \<rightarrow> bool_rel\<rangle> list_rel \<rightarrow> A \<rightarrow> nat_rel \<rightarrow> nat_rel"
    unfolding count_def null_def[symmetric] by parametricity

end