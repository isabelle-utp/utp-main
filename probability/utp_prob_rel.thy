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
type_synonym 's hrel_pdes = "('s, 's) rel_pdes"

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

no_utp_lift usubst (0) subst (1)

lemma prob_assigns: "\<K>(\<langle>\<sigma>\<rangle>\<^sub>D) = \<^U>\<open>true \<turnstile>\<^sub>n ($prob\<acute>((\<sigma> \<dagger> &\<^bold>v)\<^sup><) = 1)\<close>"
  by (simp add: assigns_d_ndes_def prob_lift wp usubst, rel_auto)

lemma prob_skip: "\<K>(II\<^sub>D) = \<^U>\<open>true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v) = 1)\<close>"
  by (simp only: assigns_d_id[THEN sym] prob_assigns usubst, rel_auto)

lemma prob_assign:
  fixes e :: "(_, _) uexpr" 
  shows "\<K>(x :=\<^sub>D e) = \<^U>\<open>true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>e\<^sup></$x\<rbrakk>) = 1)\<close>"
  by (simp add: prob_assigns wp usubst, rel_auto)

definition wplus :: "'a pmf \<Rightarrow> real \<Rightarrow> 'a pmf \<Rightarrow> 'a pmf" ("(_ +\<^bsub>_\<^esub> _)" [64, 0, 65] 64) where
"wplus P w Q = join_pmf (pmf_of_list [(P, w), (Q, 1 - w)])"

lemma pmf_wplus: 
  assumes "w \<in> {0..1}"
  shows "pmf (P +\<^bsub>w\<^esub> Q) i = pmf P i * w + pmf Q i * (1 - w)"
proof -
  from assms have pmf_wf_list: "pmf_of_list_wf [(P, w), (Q, 1 - w)]"
    by (auto intro!: pmf_of_list_wfI) 
  show ?thesis
  proof (cases "w \<in> {0<..<1}")
    case True
    hence set_pmf:"set_pmf (pmf_of_list [(P, w), (Q, 1 - w)]) = {P, Q}"
      by (subst set_pmf_of_list_eq, auto simp add: pmf_wf_list)
    thus ?thesis
    proof (cases "P = Q")
      case True
      from assms show ?thesis
        apply (auto simp add: wplus_def join_pmf_def pmf_bind)
        apply (subst integral_measure_pmf[of "{P, Q}"])
          apply (auto simp add: set_pmf_of_list pmf_wf_list set_pmf pmf_pmf_of_list)
        apply (simp add: True)
        apply (metis distrib_right eq_iff_diff_eq_0 le_add_diff_inverse mult.commute mult_cancel_left1)
        done
    next
      case False
      then show ?thesis
        apply (auto simp add: wplus_def join_pmf_def pmf_bind)
        apply (subst integral_measure_pmf[of "{P, Q}"])
          apply (auto simp add: set_pmf_of_list pmf_wf_list set_pmf pmf_pmf_of_list)
        done
    qed
  next
    case False
    thm disjE
    with assms have "w = 0 \<or> w = 1"
      by (auto)
    with assms show ?thesis 
    proof (erule_tac disjE, simp_all)
      assume w: "w = 0"
      with pmf_wf_list have "set_pmf (pmf_of_list [(P, w), (Q, 1 - w)]) = {Q}"
        apply (simp add: pmf_of_list_remove_zeros(2)[THEN sym])
        apply (subst set_pmf_of_list_eq, auto simp add: pmf_of_list_wf_def)
        done
      with w show "pmf (P +\<^bsub>0\<^esub> Q) i = pmf Q i"
        apply (auto simp add: wplus_def join_pmf_def pmf_bind pmf_wf_list pmf_of_list_remove_zeros(2)[THEN sym])
        apply (subst integral_measure_pmf[of "{Q}"])
          apply (simp_all add: set_pmf_of_list_eq pmf_pmf_of_list pmf_of_list_wf_def)
        done
    next
      assume w: "w = 1"
      with pmf_wf_list have "set_pmf (pmf_of_list [(P, w), (Q, 1 - w)]) = {P}"
        apply (simp add: pmf_of_list_remove_zeros(2)[THEN sym])
        apply (subst set_pmf_of_list_eq, auto simp add: pmf_of_list_wf_def)
        done
      with w show "pmf (P +\<^bsub>1\<^esub> Q) i = pmf P i"
        apply (auto simp add: wplus_def join_pmf_def pmf_bind pmf_wf_list pmf_of_list_remove_zeros(2)[THEN sym])
        apply (subst integral_measure_pmf[of "{P}"])
          apply (simp_all add: set_pmf_of_list_eq pmf_pmf_of_list pmf_of_list_wf_def)
        done
    qed
  qed
qed

lemma wplus_commute: 
  assumes "w \<in>{0..1}"
  shows "P +\<^bsub>w\<^esub> Q = Q +\<^bsub>(1 - w)\<^esub> P"
  using assms by (auto intro: pmf_eqI simp add: pmf_wplus)

lemma wplus_zero: "P +\<^bsub>0\<^esub> Q = Q"
  by (auto intro: pmf_eqI simp add: pmf_wplus)

lemma wplus_assoc:
  assumes "w\<^sub>1 \<in> {0..1}" "w\<^sub>2 \<in> {0..1}"
  defines "w\<^sub>2' \<equiv> w\<^sub>1+w\<^sub>2 - w\<^sub>1\<cdot>w\<^sub>2" and "w\<^sub>1' \<equiv> w\<^sub>1 / w\<^sub>1+w\<^sub>2 - w\<^sub>1\<cdot>w\<^sub>2"
  shows "P +\<^bsub>w\<^sub>1\<^esub> (Q +\<^bsub>w\<^sub>2\<^esub> R) = (P +\<^bsub>w\<^sub>1'\<^esub> Q) +\<^bsub>w\<^sub>2'\<^esub> R"
proof (rule pmf_eqI)
  fix i
  from assms(1-2) have "w\<^sub>1+w\<^sub>2 - w\<^sub>1\<cdot>w\<^sub>2 \<in> {0..1}"
    using mult_right_le_one_le sum_le_prod1 by fastforce
  with assms show "pmf (P +\<^bsub>w\<^sub>1\<^esub> (Q +\<^bsub>w\<^sub>2\<^esub> R)) i = pmf (P +\<^bsub>w\<^sub>1'\<^esub> Q +\<^bsub>w\<^sub>2'\<^esub> R) i"
    apply (simp add: pmf_wplus add.assoc)
    apply (subst pmf_wplus)
    apply (auto)
    oops

    term "\<lparr>$0-\<^bold>v \<mapsto>\<^sub>s $0-\<^bold>v\<^sub>D, $1-\<^bold>v \<mapsto>\<^sub>s $1-\<^bold>v\<^sub>D, $\<^bold>v\<acute> \<mapsto>\<^sub>s $\<^bold>v\<^sub>D\<acute>\<rparr>"

(*
definition des_merge :: "(('\<alpha>, '\<beta>, '\<gamma>) mrg, '\<delta>) urel \<Rightarrow> (('\<alpha> des, '\<beta> des, '\<gamma> des) mrg, '\<delta> des) urel" ("\<^bold>D\<^bold>M'(_')") where
[upred_defs]: "\<^bold>D\<^bold>M(M) \<equiv> ((($0-ok \<and> $1-ok) \<Rightarrow> $ok\<acute> \<and> \<lparr>$\<^bold>v\<^sub>< \<mapsto>\<^sub>s $\<^bold>v\<^sub>D\<^sub><, $0-\<^bold>v \<mapsto>\<^sub>s $0-\<^bold>v\<^sub>D, $1-\<^bold>v \<mapsto>\<^sub>s $1-\<^bold>v\<^sub>D, $\<^bold>v\<acute> \<mapsto>\<^sub>s $\<^bold>v\<^sub>D\<acute>\<rparr> \<dagger> M))"

consts IM :: "(('\<alpha>, '\<beta>, '\<gamma>) mrg, '\<delta>) urel"
*)


definition prob_merge :: "real \<Rightarrow> (('s, 's prss, 's prss) mrg, 's prss) urel" ("\<^bold>P\<^bold>M\<^bsub>_\<^esub>") where
[upred_defs]: "prob_merge r = \<^U>\<open>$prob\<acute> = $0-prob +\<^bsub>r\<^esub> $1-prob\<close>"

lemma swap_prob_merge:
  assumes "r \<in> {0..1}"
  shows "swap\<^sub>m ;; \<^bold>P\<^bold>M\<^bsub>r\<^esub> = \<^bold>P\<^bold>M\<^bsub>1 - r\<^esub>"
  by (rel_auto, (metis assms wplus_commute)+)


abbreviation prob_des_merge :: "real \<Rightarrow> (('s des, 's prss des, 's prss des) mrg, 's prss des) urel" ("\<^bold>P\<^bold>D\<^bold>M\<^bsub>_\<^esub>") where
"\<^bold>P\<^bold>D\<^bold>M\<^bsub>r\<^esub> \<equiv> \<^bold>D\<^bold>M(\<^bold>P\<^bold>M\<^bsub>r\<^esub>)"

lemma swap_prob_des_merge:
  assumes "r \<in> {0..1}"
  shows "swap\<^sub>m ;; \<^bold>P\<^bold>D\<^bold>M\<^bsub>r\<^esub> = \<^bold>P\<^bold>D\<^bold>M\<^bsub>1 - r\<^esub>"
  by (metis assms swap_des_merge swap_prob_merge)

definition prob_choice :: "'s hrel_pdes \<Rightarrow> real \<Rightarrow> 's hrel_pdes \<Rightarrow> 's hrel_pdes" ("(_ \<oplus>\<^bsub>_\<^esub> _)" [164, 0, 165] 164) where
[upred_defs]: "prob_choice P r Q = P \<parallel>\<^bsub>\<^bold>P\<^bold>D\<^bold>M\<^bsub>r\<^esub>\<^esub> Q"

lemma prob_choice: "r \<in> {0..1} \<Longrightarrow> (p\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2) \<oplus>\<^bsub>r\<^esub> (q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2) = (p\<^sub>1 \<and> q\<^sub>1) \<turnstile>\<^sub>n (P\<^sub>2 \<parallel>\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> Q\<^sub>2)"
  apply (rel_auto)

lemma prob_choice_commute: "r \<in> {0..1} \<Longrightarrow> P \<oplus>\<^bsub>r\<^esub> Q = Q \<oplus>\<^bsub>1 - r\<^esub> P"
  by (simp add: prob_choice_def swap_prob_des_merge[THEN sym], metis par_by_merge_commute_swap)



end
