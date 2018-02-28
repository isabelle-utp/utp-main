section \<open> Expectations \<close>

theory utp_expectation
  imports "UTP.utp"
begin

subsection \<open> Probabilities \<close>

typedef prob = "{0..1} :: real set"
  by auto

setup_lifting type_definition_prob

instantiation prob :: "{ord,zero,one,times,uminus}"
begin
  lift_definition less_eq_prob :: "prob \<Rightarrow> prob \<Rightarrow> bool" is "op \<le>" .
  lift_definition less_prob :: "prob \<Rightarrow> prob \<Rightarrow> bool" is "op <" .
  lift_definition zero_prob :: prob is 0 by auto
  lift_definition one_prob :: prob is 1 by auto
  lift_definition times_prob :: "prob \<Rightarrow> prob \<Rightarrow> prob" is "op *"
    by (auto, simp add: mult_le_one)
  lift_definition uminus_prob :: "prob \<Rightarrow> prob" is "\<lambda> p. 1 - p"
    by (auto)  
instance ..
end

instance prob :: order
  by (intro_classes, (transfer, auto)+)

instance prob :: comm_monoid_mult
  by (intro_classes, (transfer, auto)+)

lemma "- (- (p :: prob)) = p"
  by (transfer, simp)

subsection \<open> Expectation Type \<close>

type_synonym '\<alpha> uexpt = "(prob, '\<alpha>) uexpr"

definition upred_expt :: "'\<alpha> upred \<Rightarrow> '\<alpha> uexpt" ("[_]\<^sub>P") where
[upred_defs]: "[P]\<^sub>P = 1 \<triangleleft> P \<triangleright> 0"

lemma upred_expt_false: "[false]\<^sub>P = 0"
  by pred_auto

lemma upred_expt_true: "[true]\<^sub>P = 1"
  by pred_auto

end