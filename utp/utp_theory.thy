section {* UTP Theories *}

theory utp_theory
imports utp_rel
begin

type_synonym '\<alpha> Healthiness_condition = "'\<alpha> upred \<Rightarrow> '\<alpha> upred"

definition 
Healthy::"'\<alpha> upred \<Rightarrow> '\<alpha> Healthiness_condition \<Rightarrow> bool" (infix "is" 30)
where "P is H \<equiv> (P = H P)"

lemma Healthy_def': "P is H \<longleftrightarrow> (H P = P)"
  unfolding Healthy_def by auto

declare Healthy_def' [upred_defs]

end