section \<open> Linking to the Failures-Divergences Model \<close>

theory utp_circus_fdsem
  imports utp_circus_parallel utp_circus_recursion
begin

subsection \<open> Failures-Divergences Semantics \<close>

text \<open> The following functions play a similar role to those in Roscoe's CSP semantics, and are
  calculated from the Circus reactive design semantics. A major difference is that these three
  functions account for state. Each divergence, trace, and failure is subject to an initial
  state. Moreover, the traces are terminating traces, and therefore also provide a final state
  following the given interaction. A more subtle difference from the Roscoe semantics is that
  the set of traces do not include the divergences. The same semantic information is present,
  but we construct a direct analogy with the pre-, peri- and postconditions of our reactive 
  designs. \<close>

definition divergences :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> '\<phi> list set" ("dv\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "divergences P s = {t | t. `(\<not>\<^sub>r pre\<^sub>R(P))\<lbrakk>\<guillemotleft>s\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>`}"
  
definition traces :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> ('\<phi> list \<times> '\<sigma>) set" ("tr\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "traces P s = {(t,s') | t s'. `(pre\<^sub>R(P) \<and> post\<^sub>R(P))\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>/$st,$st\<acute>,$tr,$tr\<acute>\<rbrakk>`}"

definition failures :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> ('\<phi> list \<times> '\<phi> set) set" ("fl\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "failures P s = {(t,r) | t r. `(pre\<^sub>R(P) \<and> peri\<^sub>R(P))\<lbrakk>\<guillemotleft>r\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>/$ref\<acute>,$st,$tr,$tr\<acute>\<rbrakk>`}"

lemma preR_refine_divergences:
  assumes "P is NCSP" "Q is NCSP" "\<And> s. dv\<lbrakk>P\<rbrakk>s \<subseteq> dv\<lbrakk>Q\<rbrakk>s"
  shows "pre\<^sub>R(P) \<sqsubseteq> pre\<^sub>R(Q)"
proof (rule CRR_refine_impl_prop, simp_all add: assms closure usubst unrest)
  fix t s
  assume a: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> pre\<^sub>R Q`"
  with a show "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> pre\<^sub>R P`"
  proof (rule_tac ccontr)
    from assms(3)[of s] have b: "t \<in> dv\<lbrakk>P\<rbrakk>s \<Longrightarrow> t \<in> dv\<lbrakk>Q\<rbrakk>s"
      by (auto)
    assume "\<not> `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> pre\<^sub>R P`"
    hence "\<not> `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> CRC(pre\<^sub>R P)`"
      by (simp add: assms closure Healthy_if)
    hence "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (\<not>\<^sub>r CRC(pre\<^sub>R P))`"
      by (rel_auto)
    hence "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (\<not>\<^sub>r pre\<^sub>R P)`"
      by (simp add: assms closure Healthy_if)
    with a b show False
      by (rel_auto)
  qed
qed

lemma preR_eq_divergences:
  assumes "P is NCSP" "Q is NCSP" "\<And> s. dv\<lbrakk>P\<rbrakk>s = dv\<lbrakk>Q\<rbrakk>s"
  shows "pre\<^sub>R(P) = pre\<^sub>R(Q)"
  by (metis assms dual_order.antisym order_refl preR_refine_divergences)

lemma periR_refine_failures:
  assumes "P is NCSP" "Q is NCSP" "\<And> s. fl\<lbrakk>Q\<rbrakk>s \<subseteq> fl\<lbrakk>P\<rbrakk>s"
  shows "(pre\<^sub>R(P) \<and> peri\<^sub>R(P)) \<sqsubseteq> (pre\<^sub>R(Q) \<and> peri\<^sub>R(Q))"
proof (rule CRR_refine_impl_prop, simp_all add: assms closure unrest subst_unrest_3)
  fix t s r'
  assume a: "`[$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r'\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (pre\<^sub>R Q \<and> peri\<^sub>R Q)`"
  from assms(3)[of s] have b: "(t, r') \<in> fl\<lbrakk>Q\<rbrakk>s \<Longrightarrow> (t, r') \<in> fl\<lbrakk>P\<rbrakk>s"
    by (auto)
  with a show "`[$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r'\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (pre\<^sub>R P \<and> peri\<^sub>R P)`"
    by (simp add: failures_def)
qed

lemma periR_eq_failures:
  assumes "P is NCSP" "Q is NCSP" "\<And> s. fl\<lbrakk>P\<rbrakk>s = fl\<lbrakk>Q\<rbrakk>s"
  shows "(pre\<^sub>R(P) \<and> peri\<^sub>R(P)) = (pre\<^sub>R(Q) \<and> peri\<^sub>R(Q))"
  by (metis (full_types) assms dual_order.antisym order_refl periR_refine_failures)

lemma postR_refine_traces:
  assumes "P is NCSP" "Q is NCSP" "\<And> s. tr\<lbrakk>Q\<rbrakk>s \<subseteq> tr\<lbrakk>P\<rbrakk>s"
  shows "(pre\<^sub>R(P) \<and> post\<^sub>R(P)) \<sqsubseteq> (pre\<^sub>R(Q) \<and> post\<^sub>R(Q))"
proof (rule CRR_refine_impl_prop, simp_all add: assms closure unrest subst_unrest_5)
  fix t s s'
  assume a: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (pre\<^sub>R Q \<and> post\<^sub>R Q)`"
  from assms(3)[of s] have b: "(t, s') \<in> tr\<lbrakk>Q\<rbrakk>s \<Longrightarrow> (t, s') \<in> tr\<lbrakk>P\<rbrakk>s"
    by (auto)
  with a show "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (pre\<^sub>R P \<and> post\<^sub>R P)`"
    by (simp add: traces_def)
qed

lemma postR_eq_traces:
  assumes "P is NCSP" "Q is NCSP" "\<And> s. tr\<lbrakk>P\<rbrakk>s = tr\<lbrakk>Q\<rbrakk>s"
  shows "(pre\<^sub>R(P) \<and> post\<^sub>R(P)) = (pre\<^sub>R(Q) \<and> post\<^sub>R(Q))"
  by (metis assms dual_order.antisym order_refl postR_refine_traces)

lemma circus_fd_refine_intro:
  assumes "P is NCSP" "Q is NCSP" "\<And> s. dv\<lbrakk>Q\<rbrakk>s \<subseteq> dv\<lbrakk>P\<rbrakk>s" "\<And> s. fl\<lbrakk>Q\<rbrakk>s \<subseteq> fl\<lbrakk>P\<rbrakk>s" "\<And> s. tr\<lbrakk>Q\<rbrakk>s \<subseteq> tr\<lbrakk>P\<rbrakk>s"
  shows "P \<sqsubseteq> Q"
proof (rule SRD_refine_intro', simp_all add: closure assms)
  show a: "`pre\<^sub>R P \<Rightarrow> pre\<^sub>R Q`"
    using assms(1) assms(2) assms(3) preR_refine_divergences refBy_order by blast
  show "peri\<^sub>R P \<sqsubseteq> (pre\<^sub>R P \<and> peri\<^sub>R Q)"
  proof -
    have "peri\<^sub>R P \<sqsubseteq> (pre\<^sub>R Q \<and> peri\<^sub>R Q)"
      by (metis (no_types) assms(1) assms(2) assms(4) periR_refine_failures utp_pred_laws.le_inf_iff)
    then show ?thesis
      by (metis a refBy_order utp_pred_laws.inf.order_iff utp_pred_laws.inf_assoc)
  qed
  show "post\<^sub>R P \<sqsubseteq> (pre\<^sub>R P \<and> post\<^sub>R Q)"
  proof -
    have "post\<^sub>R P \<sqsubseteq> (pre\<^sub>R Q \<and> post\<^sub>R Q)"
      by (meson assms(1) assms(2) assms(5) postR_refine_traces utp_pred_laws.le_inf_iff)
    then show ?thesis
      by (metis a refBy_order utp_pred_laws.inf.absorb_iff1 utp_pred_laws.inf_assoc)
  qed
qed

subsection \<open> Circus Operators \<close>

lemma traces_Skip:
  "tr\<lbrakk>Skip\<rbrakk>s = {([], s)}"
  by (simp add: traces_def rdes alpha closure, rel_simp)

lemma failures_Skip:
  "fl\<lbrakk>Skip\<rbrakk>s = {}"
  by (simp add: failures_def, rdes_calc)

lemma divergences_Skip:
  "dv\<lbrakk>Skip\<rbrakk>s = {}"
  by (simp add: divergences_def, rdes_calc)

lemma traces_Stop:
  "tr\<lbrakk>Stop\<rbrakk>s = {}"
  by (simp add: traces_def, rdes_calc)

lemma failures_Stop:
  "fl\<lbrakk>Stop\<rbrakk>s = {([], E) | E. True}"
  by (simp add: failures_def, rdes_calc, rel_auto)

lemma divergences_Stop:
  "dv\<lbrakk>Stop\<rbrakk>s = {}"
  by (simp add: divergences_def, rdes_calc)

lemma traces_AssignsCSP:
  "tr\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>C\<rbrakk>s = {([], \<sigma>(s))}"
  by (simp add: traces_def rdes closure usubst alpha, rel_auto)

lemma failures_AssignsCSP:
  "fl\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>C\<rbrakk>s = {}"
  by (simp add: failures_def, rdes_calc)

lemma divergences_AssignsCSP:
  "dv\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>C\<rbrakk>s = {}"
  by (simp add: divergences_def, rdes_calc)

lemma failures_Miracle: "fl\<lbrakk>Miracle\<rbrakk>s = {}"
  by (simp add: failures_def rdes closure usubst)

lemma divergences_Miracle: "dv\<lbrakk>Miracle\<rbrakk>s = {}"
  by (simp add: divergences_def rdes closure usubst)

lemma failures_Chaos: "fl\<lbrakk>Chaos\<rbrakk>s = {}"
  by (simp add: failures_def rdes, rel_auto)

lemma divergences_Chaos: "dv\<lbrakk>Chaos\<rbrakk>s = UNIV"
  by (simp add: divergences_def rdes, rel_auto)

lemma traces_Chaos: "tr\<lbrakk>Chaos\<rbrakk>s = {}"
  by (simp add: traces_def rdes closure usubst)
  
lemma traces_do: "tr\<lbrakk>do\<^sub>C(e)\<rbrakk>s = {([\<lbrakk>e\<rbrakk>\<^sub>es], s)}"
  by (rdes_simp, simp add: traces_def rdes closure rpred, rel_auto)

lemma failures_do: "fl\<lbrakk>do\<^sub>C(e)\<rbrakk>s = {([], E) | E. \<lbrakk>e\<rbrakk>\<^sub>es \<notin> E}"
  by (rdes_simp, simp add: failures_def rdes closure rpred usubst, rel_auto)

lemma divergences_do: "dv\<lbrakk>do\<^sub>C(e)\<rbrakk>s = {}"
  by (rel_auto)

lemma nil_least [simp]:
  "\<langle>\<rangle> \<le>\<^sub>u x = true" by rel_auto

lemma wp_rea_circus_lemma_1:
  assumes "P is CRR" "$ref\<acute> \<sharp> P"
  shows "out\<alpha> \<sharp> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk>"
proof -
  have "out\<alpha> \<sharp> (CRR (\<exists> $ref\<acute> \<bullet> P))\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk>"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms(1) assms(2) ex_unrest)
qed

lemma wp_rea_circus_lemma_2:
  assumes "P is CRR"
  shows "in\<alpha> \<sharp> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>"
proof -
  have "in\<alpha> \<sharp> (CRR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms ex_unrest)
qed

text \<open> The meaning of reactive weakest precondition for Circus. @{term "P wp\<^sub>r Q"} means that,
  whenever $P$ terminates in a state @{term s\<^sub>0} having done the interaction trace @{term t\<^sub>0}, which 
  is a prefix of the overall trace, then $Q$ must be satisfied. This in particular means that
  the remainder of the trace after @{term t\<^sub>0} must not be a divergent behaviour of $Q$. \<close>

lemma wp_rea_circus_form:
  assumes "P is CRR" "$ref\<acute> \<sharp> P" "Q is CRC"
  shows "(P wp\<^sub>r Q) = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<Rightarrow>\<^sub>r Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>)"
proof -
  have "(P wp\<^sub>r Q) = (\<not>\<^sub>r (\<^bold>\<exists> t\<^sub>0 \<bullet> P\<lbrakk>\<guillemotleft>t\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>t\<^sub>0\<guillemotright>/$tr\<rbrakk> \<and> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>))"
    by (simp_all add: wp_rea_def R2_tr_middle closure RR_implies_R2 assms)
  also have "... = (\<not>\<^sub>r (\<^bold>\<exists> (s\<^sub>0,t\<^sub>0) \<bullet> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> ;; (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk> \<and> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>))"
    by (rel_blast)
  also have "... = (\<not>\<^sub>r (\<^bold>\<exists> (s\<^sub>0,t\<^sub>0) \<bullet> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<and> (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk> \<and> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>))"
    by (simp add: seqr_to_conj add: wp_rea_circus_lemma_1 wp_rea_circus_lemma_2 assms closure conj_assoc)
  also have "... = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> \<not>\<^sub>r P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<or> \<not>\<^sub>r (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk> \<or> \<not>\<^sub>r \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>)"
    by (rel_auto)
  also have "... = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> \<not>\<^sub>r P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<or> \<not>\<^sub>r (\<not>\<^sub>r RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk> \<or> \<not>\<^sub>r \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>)"
    by (simp add: Healthy_if assms closure)
  also have "... = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> \<not>\<^sub>r P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<or> (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk> \<or> \<not>\<^sub>r \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>)"
    by (rel_auto)
  also have "... = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>)"
    by (rel_auto)
  also have "... = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<Rightarrow>\<^sub>r Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>)"
    by (simp add: Healthy_if assms closure)
  finally show ?thesis .
qed

lemma subst_case_prod [usubst]:
  fixes P :: "'i \<Rightarrow> 'j \<Rightarrow> ('a, '\<alpha>) uexpr"  
  shows "\<sigma> \<dagger> case_prod (\<lambda> x y. P x y) v = case_prod (\<lambda> x y. \<sigma> \<dagger> P x y) v"
  by (simp add: case_prod_beta')

lemma wp_rea_circus_form_alt:
  assumes "P is CRR" "$ref\<acute> \<sharp> P" "Q is CRC"
  shows "(P wp\<^sub>r Q) = R1(\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> $tr ^\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                               \<Rightarrow>\<^sub>r Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,&tt-\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>)"
proof -
  have "(P wp\<^sub>r Q) = R2(P wp\<^sub>r Q)"
    by (simp add: CRC_implies_RR CRR_implies_RR Healthy_if RR_implies_R2 assms wp_rea_R2_closed)
  also have "... = R2(\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>)"
    by (simp add: wp_rea_circus_form assms closure Healthy_if)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                                        \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>) 
                                         \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>)"
    by (simp add: R2_form, rel_auto)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                                        \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0-tr\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>) 
                                         \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>)"
    by (rel_auto)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> $tr ^\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                                        \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,&tt-\<guillemotleft>tr\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>) 
                                         \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>)"
    by (rel_auto, (metis list_concat_minus_list_concat)+)
  also have "... = R1(\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> $tr ^\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                                        \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,&tt-\<guillemotleft>tr\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>)"
    by (rel_auto)
  also have "... = R1(\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> $tr ^\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                               \<Rightarrow>\<^sub>r Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,&tt-\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>)"
    by (simp add: Healthy_if assms closure)
  finally show ?thesis .
qed

(*
lemma traces_seq:
  fixes P :: "('s, 'e) action"
  assumes "P is NCSP" "Q is NCSP"
  shows "tr\<lbrakk>P ;; Q\<rbrakk>s = 
          {(t\<^sub>1 @ t\<^sub>2, s') | t\<^sub>1 t\<^sub>2 s\<^sub>0 s'. (t\<^sub>1, s\<^sub>0) \<in> tr\<lbrakk>P\<rbrakk>s \<and> (t\<^sub>2, s') \<in> tr\<lbrakk>Q\<rbrakk>s\<^sub>0 
                                     \<and> (t\<^sub>1@t\<^sub>2) \<notin> dv\<lbrakk>P\<rbrakk>s 
                                     \<and> (\<forall> (t, s\<^sub>1) \<in> tr\<lbrakk>P\<rbrakk>s. t \<le> t\<^sub>1@t\<^sub>2 \<longrightarrow> (t\<^sub>1@t\<^sub>2)-t \<notin> dv\<lbrakk>Q\<rbrakk>s\<^sub>1) }"
  (is "?lhs = ?rhs")
proof 
  show "?lhs \<subseteq> ?rhs"
  proof (rdes_expand cls: assms, simp add: traces_def divergences_def rdes closure assms rdes_def unrest rpred usubst, auto)
    fix t :: "'e list" and s' :: "'s"
    let ?\<sigma> = "[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>]"
    assume 
      a1: "`?\<sigma> \<dagger> (post\<^sub>R P ;; post\<^sub>R Q)`" and
      a2: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> pre\<^sub>R P`" and
      a3: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (post\<^sub>R P wp\<^sub>r pre\<^sub>R Q)`"
    from a1 have "`?\<sigma> \<dagger> (\<^bold>\<exists> tr\<^sub>0 \<bullet> ((post\<^sub>R P)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; (post\<^sub>R Q)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>) \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>)`"
      by (simp add: R2_tr_middle assms closure)
    then obtain tr\<^sub>0 where p1:"`?\<sigma> \<dagger> ((post\<^sub>R P)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; (post\<^sub>R Q)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>)`" and tr0: "tr\<^sub>0 \<le> t"
      apply (simp add: usubst)
      apply (erule taut_shEx_elim)
       apply (simp add: unrest_all_circus_vars_st_st' closure unrest assms)
      apply (rel_auto)
      done
    from p1 have "`?\<sigma> \<dagger> (\<^bold>\<exists> st\<^sub>0 \<bullet> (post\<^sub>R P)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk>\<lbrakk>\<guillemotleft>st\<^sub>0\<guillemotright>/$st\<acute>\<rbrakk> ;; (post\<^sub>R Q)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>st\<^sub>0\<guillemotright>/$st\<rbrakk>)`"
      by (simp add: seqr_middle[of st, THEN sym])
    then obtain s\<^sub>0 where "`?\<sigma> \<dagger> ((post\<^sub>R P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> ;; (post\<^sub>R Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>)`"
      apply (simp add: usubst)
      apply (erule taut_shEx_elim)
       apply (simp add: unrest_all_circus_vars_st_st' closure unrest assms)
      apply (rel_auto)
      done
    hence "`(([$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tr\<^sub>0\<guillemotright>] \<dagger> post\<^sub>R P) ;;
             ([$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<guillemotleft>tr\<^sub>0\<guillemotright>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> post\<^sub>R Q))`"
      by (rel_auto)
    hence "`(([$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tr\<^sub>0\<guillemotright>] \<dagger> post\<^sub>R P) \<and>
             ([$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<guillemotleft>tr\<^sub>0\<guillemotright>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> post\<^sub>R Q))`"
      by (simp add: seqr_to_conj unrest_any_circus_var assms closure unrest)
    hence postP: "`([$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tr\<^sub>0\<guillemotright>] \<dagger> post\<^sub>R P)`" and
          postQ': "`([$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<guillemotleft>tr\<^sub>0\<guillemotright>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> post\<^sub>R Q)`"
      by (rel_auto)+
    from postQ' have "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>] \<dagger> [$tr \<mapsto>\<^sub>s \<guillemotleft>tr\<^sub>0\<guillemotright>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tr\<^sub>0\<guillemotright> + (\<guillemotleft>t\<guillemotright> - \<guillemotleft>tr\<^sub>0\<guillemotright>)] \<dagger> post\<^sub>R Q`"
      using tr0 by (rel_auto)
    hence "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>] \<dagger> [$tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright> - \<guillemotleft>tr\<^sub>0\<guillemotright>] \<dagger> post\<^sub>R Q`"
      by (simp add: R2_subst_tr closure assms)
    hence postQ: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t - tr\<^sub>0\<guillemotright>] \<dagger> post\<^sub>R Q`"
      by (rel_auto)
    have preP: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tr\<^sub>0\<guillemotright>] \<dagger> pre\<^sub>R P`"
    proof -
      have "(pre\<^sub>R P)\<lbrakk>0,\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<sqsubseteq> (pre\<^sub>R P)\<lbrakk>0,\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk>"
        by (simp add: RC_prefix_refine closure assms tr0)
      hence "[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tr\<^sub>0\<guillemotright>] \<dagger> pre\<^sub>R P \<sqsubseteq> [$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> pre\<^sub>R P"
        by (rel_auto)
      thus ?thesis
        by (simp add: taut_refine_impl a2)
    qed

    have preQ: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t - tr\<^sub>0\<guillemotright>] \<dagger> pre\<^sub>R Q`"
    proof -
      from postP a3 have "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<guillemotleft>tr\<^sub>0\<guillemotright>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> pre\<^sub>R Q`"
        apply (simp add: wp_rea_def)
        apply (rel_auto)
        using tr0 apply blast+
        done
      hence "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>] \<dagger> [$tr \<mapsto>\<^sub>s \<guillemotleft>tr\<^sub>0\<guillemotright>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tr\<^sub>0\<guillemotright> + (\<guillemotleft>t\<guillemotright> - \<guillemotleft>tr\<^sub>0\<guillemotright>)] \<dagger> pre\<^sub>R Q`"
        by (rel_auto)

      hence "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>] \<dagger> [$tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright> - \<guillemotleft>tr\<^sub>0\<guillemotright>] \<dagger> pre\<^sub>R Q`"
        by (simp add: R2_subst_tr closure assms)
      thus ?thesis
        by (rel_auto)
    qed

    from a2 have ndiv: "\<not> `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tr\<^sub>0 @ (t - tr\<^sub>0)\<guillemotright>] \<dagger> (\<not>\<^sub>r pre\<^sub>R P)`"
      using tr0 by (rel_auto)

    from a3
    have "\<And>t\<^sub>0 s\<^sub>1.
           `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> pre\<^sub>R P` \<Longrightarrow>
           `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> post\<^sub>R P` \<Longrightarrow>
            t\<^sub>0 \<le> t \<Longrightarrow> `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t - t\<^sub>0\<guillemotright>] \<dagger> (\<not>\<^sub>r pre\<^sub>R Q)` \<Longrightarrow> False"
    proof -
      fix t\<^sub>0 s\<^sub>1
      assume b:
        "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> pre\<^sub>R P`"
        "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> post\<^sub>R P`"
        "t\<^sub>0 \<le> t" 
        "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t - t\<^sub>0\<guillemotright>] \<dagger> (\<not>\<^sub>r pre\<^sub>R Q)`"

      from b(2) have c1: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> RR(post\<^sub>R P)`"
        by (simp add: Healthy_if assms closure)

      from b(4) have c2: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t - t\<^sub>0\<guillemotright>] \<dagger> (\<not>\<^sub>r RC(pre\<^sub>R Q))`"
        by (simp add: Healthy_if assms closure)

      from a3 have "`\<^bold>\<forall> (s\<^sub>0, t\<^sub>0) \<bullet> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> [$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> post\<^sub>R P 
                               \<Rightarrow>\<^sub>r [$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> pre\<^sub>R Q`"
        using wp_rea_circus_form[of "post\<^sub>R P" "pre\<^sub>R Q"]
        apply (simp_all add: closure assms unrest usubst)

      from a3 have

      from a3 have c3: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (RR(post\<^sub>R P) wp\<^sub>r RC(pre\<^sub>R Q))`"
        by (simp add: Healthy_if assms closure)

      from a3 have "`\<^bold>\<forall> (s\<^sub>0, t\<^sub>0) \<bullet> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>t\<guillemotright> \<Rightarrow> P\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> \<not>\<^sub>r Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t - t\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>`"
        using wp_rea_circus[of "post\<^sub>R P" "pre\<^sub>R Q" s t]  apply (simp_all add: closure unrest assms)

(*
      have "\<And> s\<^sub>0 t\<^sub>0. t\<^sub>0 \<le> t \<Longrightarrow> `[$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> post\<^sub>R P \<and>
                                 \<not>\<^sub>r [$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t - t\<^sub>0\<guillemotright>] \<dagger> pre\<^sub>R Q`"

        using wp_rea_circus[of "post\<^sub>R P" "pre\<^sub>R Q" s t]
        apply (simp_all add: closure unrest assms)
*)

      from c1 c2 c3 b(3) show False
        apply (simp add: wp_rea_def)
        apply (rel_auto)

      
    show "\<exists>t\<^sub>1 t\<^sub>2.
            t = t\<^sub>1 @ t\<^sub>2 \<and>
            (\<exists>s\<^sub>0. `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>] \<dagger> pre\<^sub>R P \<and>
                    [$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>] \<dagger> post\<^sub>R P` \<and>
                   `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> pre\<^sub>R Q \<and>
                    [$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> post\<^sub>R Q` \<and>
                    \<not> `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>] \<dagger> (\<not>\<^sub>r pre\<^sub>R P)` \<and>
                    (\<forall>t\<^sub>0 s\<^sub>1. `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> pre\<^sub>R P \<and>
                             [$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> post\<^sub>R P` \<longrightarrow>
                            t\<^sub>0 \<le> t\<^sub>1 @ t\<^sub>2 \<longrightarrow> \<not> `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>(t\<^sub>1 @ t\<^sub>2) - t\<^sub>0\<guillemotright>] \<dagger> (\<not>\<^sub>r pre\<^sub>R Q)`))"
      apply (rule_tac x="tr\<^sub>0" in exI)
      apply (rule_tac x="(t - tr\<^sub>0)" in exI)
      apply (auto)
      using tr0 apply auto[1]
      apply (rule_tac x="s\<^sub>0" in exI)
      apply (auto simp add: taut_conj preP preQ postP postQ ndiv)
      done
  qed

  show "?rhs \<subseteq> ?lhs"
  proof (rdes_expand cls: assms, simp add: traces_def divergences_def rdes closure assms rdes_def unrest rpred usubst, auto)
    fix t\<^sub>1 t\<^sub>2 :: "'e list" and s\<^sub>0 s' :: "'s"
    assume
      a1: "\<not> `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>] \<dagger> (\<not>\<^sub>r pre\<^sub>R P)`" and 
      a2: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>] \<dagger> pre\<^sub>R P`" and
      a3: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>] \<dagger> post\<^sub>R P`" and
      a4: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> pre\<^sub>R Q`" and
      a5: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> post\<^sub>R Q`"

    from a1 have preP: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>] \<dagger> (pre\<^sub>R P)`"
      by (simp add: taut_not unrest_all_circus_vars_st assms closure unrest, rel_auto)

    have "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>+\<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> post\<^sub>R Q`"
    proof -
      have "[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> post\<^sub>R Q =
            [$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>] \<dagger> [$tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> post\<^sub>R Q"
        by rel_auto
      also have "... = [$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>] \<dagger> [$tr \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>+\<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> post\<^sub>R Q"
        by (simp add: R2_subst_tr assms closure, rel_auto)
      finally show ?thesis using a5
        by (rel_auto)
    qed
    with a3
    have postPQ: " `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>] \<dagger> (post\<^sub>R P ;; post\<^sub>R Q)`"
      by (rel_blast)

    have "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>+\<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> pre\<^sub>R Q`"
    proof -
      have "[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>+\<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> pre\<^sub>R Q = 
            [$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>] \<dagger> [$tr \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>+\<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> pre\<^sub>R Q"
        by rel_auto
      also have "... = [$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>] \<dagger> [$tr \<mapsto>\<^sub>s 0, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> pre\<^sub>R Q"
        by (simp add: R2_subst_tr assms closure)
      finally show ?thesis using a4
        by (rel_auto)
    qed

    with a3
    have wpR: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>] \<dagger> (post\<^sub>R P wp\<^sub>r pre\<^sub>R Q)`"
      apply (simp add: wp_rea_def usubst rea_not_def R1_def)
      apply (rel_simp) sorry

    show "`([$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>] \<dagger> pre\<^sub>R P \<and>
         [$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>] \<dagger> (post\<^sub>R P wp\<^sub>r pre\<^sub>R Q)) \<and>
        [$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>] \<dagger> (post\<^sub>R P ;; post\<^sub>R Q)`"
      by (auto simp add: taut_conj preP postPQ wpR)
  qed
qed

lemma traces_prefix: 
  assumes "P is NCSP"
  shows "tr\<lbrakk>a \<^bold>\<rightarrow> P\<rbrakk>s = {(a # t, s') | t s'. (t, s') \<in> tr\<lbrakk>P\<rbrakk>s}"
  by (auto simp add: PrefixCSP_def traces_seq traces_do divergences_do lit.rep_eq assms closure Healthy_if)
*)

subsection {* Deadlock Freedom *}
  
definition DF :: "'e set \<Rightarrow> ('s, 'e) action" where
"DF(A) = (\<mu>\<^sub>C X \<bullet> (\<Sqinter> a\<in>A \<bullet> a \<^bold>\<rightarrow> Skip) ;; X)"
 
lemma DF_CSP [closure]: "A \<noteq> {} \<Longrightarrow> DF(A) is CSP"
  by (simp add: DF_def closure unrest)

end