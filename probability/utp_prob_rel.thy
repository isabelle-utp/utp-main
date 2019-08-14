section \<open> Probabilistic Relations \<close>

theory utp_prob_rel
  imports "UTP-Calculi.utp_wprespec" "UTP-Designs.utp_designs" "HOL-Probability.Probability_Mass_Function"
begin recall_syntax

purge_notation inner (infix "\<bullet>" 70)
declare [[coercion pmf]]

alphabet 's prss = 
  prob :: "'s pmf"

text \<open> If the probabilities of two disjoint sample sets sums up to 1, then the probability of the
  first set is equal to 1 minus the probability of the second set. \<close>

lemma prob_lemma1:
  assumes "X \<inter> Y = {}"
  shows "((\<Sum>\<^sub>a i\<in>(X \<union> Y). pmf M i) = 1) = ((\<Sum>\<^sub>a i\<in>X. pmf M i) = 1 - (\<Sum>\<^sub>a i\<in>Y. pmf M i))"
  by (metis assms diff_eq_eq infsetsum_Un_disjoint pmf_abs_summable)

no_utp_lift ndesign wprespec uwp

type_synonym ('a, 'b) rel_pdes = "('a, 'b prss) rel_des"

translations
  (type) "('a, 'b) rel_pdes" <= (type) "('a, 'b prss) rel_des"

definition forget_prob :: "('s prss, 's) rel_des" ("\<^bold>f\<^bold>p") where
[upred_defs]: "forget_prob = UTP\<open>true \<turnstile>\<^sub>n ($prob($\<^bold>v\<acute>) > 0)\<close>"

definition pemb :: "('a, 'b) rel_des \<Rightarrow> ('a, 'b) rel_pdes" ("\<K>")
  where [upred_defs]: "pemb D = \<^bold>f\<^bold>p \\ D"

lemma pemb_mono: "P \<sqsubseteq> Q \<Longrightarrow> \<K>(P) \<sqsubseteq> \<K>(Q)"
  by (metis (mono_tags, lifting) dual_order.trans order_refl pemb_def wprespec)

text \<open> Can this law be generalised for normal or arbitrary designs? \<close>

lemma wdprespec: "(true \<turnstile>\<^sub>n R) \\ (p \<turnstile>\<^sub>n Q) = (p \<turnstile>\<^sub>n (R \\ Q))"
  by (rel_auto)

lemma "R wp (&\<^bold>v =\<^sub>u \<guillemotleft>s'\<guillemotright>) = Pre(R\<lbrakk>\<guillemotleft>s'\<guillemotright>/$\<^bold>v\<acute>\<rbrakk>)"
  by (rel_auto)

lemma pemb_form:
  fixes R :: "('a, 'b) urel"
  shows "\<^U>\<open>($prob($\<^bold>v\<acute>) > 0) \\ R\<close> = \<^U>\<open>(\<Sum>\<^sub>a i\<in>{s'.(R wp (&\<^bold>v = s'))\<^sup><}. $prob\<acute> i) = 1\<close>" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<^U>\<open>(\<not> (\<not> R) ;; (0 < $prob\<acute>$\<^bold>v))\<close>"
    by (rel_auto)
  also have "... = \<^U>\<open>(\<Sum>\<^sub>a i\<in>{s'.(R wp (&\<^bold>v = s'))\<^sup><}. $prob\<acute> i) = 1\<close>"
    apply (rel_auto)
    apply (metis (no_types, lifting) infsetsum_pmf_eq_1 mem_Collect_eq pmf_positive subset_eq)
    apply (metis AE_measure_pmf_iff UNIV_I measure_pmf.prob_eq_1 measure_pmf_conv_infsetsum mem_Collect_eq set_pmf_eq' sets_measure_pmf)
    done
  finally show ?thesis .
qed

lemma prob_lift:
  fixes R :: "('a, 'b) urel" and p :: "'a upred"
  shows "\<K>(p \<turnstile>\<^sub>n R) = \<^U>\<open>p \<turnstile>\<^sub>n ((\<Sum>\<^sub>a i\<in>{s'.(R wp (&\<^bold>v = s'))\<^sup><}. $prob\<acute> i) = 1)\<close>"
proof -
  have 1:"\<K>(p \<turnstile>\<^sub>n R) = p \<turnstile>\<^sub>n \<^U>\<open>($prob($\<^bold>v\<acute>) > 0) \\ R\<close>"
    by (rel_auto)
  have 2:"\<^U>\<open>($prob($\<^bold>v\<acute>) > 0) \\ R\<close> = \<^U>\<open>(\<Sum>\<^sub>a i\<in>{s'.(R wp (&\<^bold>v = s'))\<^sup><}. $prob\<acute> i) = 1\<close>"
    by (simp add: pemb_form)
  show ?thesis
    by (simp add: "1" "2")
qed

no_utp_lift usubst subst

lemma assign_prob:
  fixes e :: "(_, _) uexpr" 
  shows "\<K>(x :=\<^sub>D e) = \<^U>\<open>true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>e\<^sup></$x\<rbrakk>) = 1)\<close>"
  unfolding assigns_d_ndes_def
  apply (simp add: prob_lift wp usubst)
  apply (rel_auto)
  done
  
end
