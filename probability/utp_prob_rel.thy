section \<open> Probabilistic Relations \<close>

theory utp_prob_rel
  imports "UTP-Calculi.utp_wprespec" "UTP-Designs.utp_designs" "HOL-Probability.Probability_Mass_Function"
begin recall_syntax

no_notation inner (infix "\<bullet>" 70)
declare [[coercion pmf]]


alphabet 's prss = 
  prob :: "'s pmf"

text \<open> If the probabilities of two disjoint sample sets sums up to 1, then the probability of the
  first set is equal to 1 minus the probability of the second set. \<close>

lemma prob_lemma1:
  assumes "X \<inter> Y = {}"
  shows "((\<Sum>\<^sub>a i\<in>(X \<union> Y). pmf M i) = 1) = ((\<Sum>\<^sub>a i\<in>X. pmf M i) = 1 - (\<Sum>\<^sub>a i\<in>Y. pmf M i))"
  by (metis assms diff_eq_eq infsetsum_Un_disjoint pmf_abs_summable)

no_utp_lift ndesign

definition fprb :: "('s prss, 's) rel_des" ("\<rho>") where
[upred_defs]: "fprb = UTP\<open>true \<turnstile>\<^sub>n ($prob($\<^bold>v\<acute>) > 0)\<close>"

definition pemb ("\<K>") where [upred_defs]: "pemb D = \<rho> \\ D"

lemma wdprespec: "(true \<turnstile>\<^sub>n R) \\ (p \<turnstile>\<^sub>n Q) = (p \<turnstile>\<^sub>n (R \\ Q))"
  by (rel_auto)

lemma seqr_unfold_heterogeneous:
  "(P ;; Q) = (\<^bold>\<exists> v \<bullet> \<lparr>$\<^bold>v\<acute> \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>, $\<^bold>v \<mapsto>\<^sub>s $\<^bold>v\<rparr> \<dagger> P \<and> \<lparr>$\<^bold>v \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>, $\<^bold>v\<acute> \<mapsto>\<^sub>s $\<^bold>v\<acute>\<rparr> \<dagger> Q)"
  by (rel_auto)

syntax
  "_uinfsetsum" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("infsetsum\<^sub>u")

term shEx

lift_definition uexpr_bind :: "(('a \<Rightarrow> 'c) \<Rightarrow> 'b, 's) uexpr \<Rightarrow> ('a \<Rightarrow> ('c, 's) uexpr) \<Rightarrow> ('b, 's) uexpr" (infixl ":>" 85)
is "\<lambda> f x s. f s (\<lambda> v. x v s)" .

update_uexpr_rep_eq_thms

lemma "shEx F = (\<guillemotleft>Ex\<guillemotright> :> F)"
  by (pred_simp)

lemma "(\<Sqinter> i\<in>A \<bullet> P(i)) = \<guillemotleft>SUPREMUM\<guillemotright> |> \<guillemotleft>A\<guillemotright> :> P"
  by (pred_simp, simp add: Setcompr_eq_image)

translations
  "_uinfsetsum x y" == "CONST bop CONST infsetsum x y"

abbreviation "uinfsetsum x y \<equiv> \<guillemotleft>infsetsum\<guillemotright> :> x |> y"

syntax
  "_UInfSetsum" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Sum>\<^sub>a _ \<in> _ \<bullet> _" [0, 10] 10)

translations
  "_UInfSetsum x A P" => "CONST uinfsetsum (\<lambda> x. P) A"

no_utp_lift uwp lift_pre uinfsetsum

term "UTP\<open>$prob\<acute> i\<close>"

term "UTP\<open>\<Sum>\<^sub>a i\<in>{s' | (R wp (&\<^bold>v = s'))\<^sup><} \<bullet> $prob\<acute> i\<close>"


lemma prob_lift:
  fixes R :: "'s hrel"
  shows "\<K>(p \<turnstile>\<^sub>n R) = p \<turnstile>\<^sub>n UTP\<open>infsetsum $prob\<acute> {s' | (R wp (&\<^bold>v = s'))\<^sup><} = 1\<close>"
proof -
  have 1:"\<K>(p \<turnstile>\<^sub>n R) = p \<turnstile>\<^sub>n ((($prob |> $\<^bold>v\<acute>) >\<^sub>u 0) \\ R)"
    by (rel_auto)

  have 2:"(($prob |> $\<^bold>v\<acute>) >\<^sub>u 0) \\ R  = UTP\<open>infsetsum $prob\<acute> {s' | \<lceil>R wp (&\<^bold>v = s')\<rceil>\<^sub><} = 1\<close>"
  proof -
    have "((($prob |> $\<^bold>v\<acute>) >\<^sub>u 0) \\ R) = (\<not> (\<not> R) ;; (0 <\<^sub>u $prob\<acute> |> $\<^bold>v))"
      by rel_auto
    also have "... = (\<not> (\<^bold>\<exists> v \<bullet> \<not> \<lparr>$\<^bold>v \<mapsto>\<^sub>s $\<^bold>v, $\<^bold>v\<acute> \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>\<rparr> \<dagger> R \<and> 0 <\<^sub>u $prob\<acute> |> (\<guillemotleft>v\<guillemotright>)))"
      by (simp add: seqr_unfold_heterogeneous usubst, rel_auto)
    also have "... = (\<not> (\<^bold>\<exists> v \<bullet> \<not> \<lceil>R wp (&\<^bold>v =\<^sub>u \<guillemotleft>v\<guillemotright>)\<rceil>\<^sub>< \<and> 0 <\<^sub>u $prob\<acute> |> (\<guillemotleft>v\<guillemotright>)))"
      by (rel_auto)
    also have "... = UTP\<open>infsetsum $prob\<acute> {s' | \<lceil>R wp (&\<^bold>v = s')\<rceil>\<^sub><} = 1\<close>"
      apply (rel_auto)
      apply (metis (no_types, lifting) infsetsum_pmf_eq_1 mem_Collect_eq pmf_positive subset_eq)
      apply (metis AE_measure_pmf_iff UNIV_I measure_pmf.prob_eq_1 measure_pmf_conv_infsetsum mem_Collect_eq set_pmf_eq' sets_measure_pmf)
      done
    finally show ?thesis .
  qed
  show ?thesis
    by (simp add: "1" "2")
qed

lemma "vwb_lens x \<Longrightarrow> \<K>(x :=\<^sub>D e) = (true \<turnstile>\<^sub>n ($prob\<acute> |> ($\<^bold>v\<lbrakk>\<lceil>e\<rceil>\<^sub></$x\<rbrakk>) =\<^sub>u 1))"
  unfolding assigns_d_ndes_def
  apply (simp add: prob_lift wp usubst)
  apply (rel_auto)
  done

end
