section \<open> Linking to the Failures-Divergences Model \<close>

theory utp_sfrd_fdsem
  imports utp_sfrd_recursion
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

lemma trace_divergence_disj:
  assumes "P is NCSP" "(t, s') \<in> tr\<lbrakk>P\<rbrakk>s" "t \<in> dv\<lbrakk>P\<rbrakk>s"
  shows False
  using assms(2,3)
  by (simp add: traces_def divergences_def, rdes_simp cls:assms, rel_auto)

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
  "tr\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>C\<rbrakk>s = {([], \<lbrakk>\<sigma>\<rbrakk>\<^sub>e s)}"
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

lemma divergences_cond:
  assumes "P is NCSP" "Q is NCSP"
  shows "dv\<lbrakk>P \<triangleleft> b \<triangleright>\<^sub>R Q\<rbrakk>s = (if (\<lbrakk>b\<rbrakk>\<^sub>es) then dv\<lbrakk>P\<rbrakk>s else dv\<lbrakk>Q\<rbrakk>s)"
  by (rdes_simp cls: assms, simp add: divergences_def traces_def rdes closure rpred assms, rel_auto)

lemma traces_cond:
  assumes "P is NCSP" "Q is NCSP"
  shows "tr\<lbrakk>P \<triangleleft> b \<triangleright>\<^sub>R Q\<rbrakk>s = (if (\<lbrakk>b\<rbrakk>\<^sub>es) then tr\<lbrakk>P\<rbrakk>s else tr\<lbrakk>Q\<rbrakk>s)"
  by (rdes_simp cls: assms, simp add: divergences_def traces_def rdes closure rpred assms, rel_auto)

lemma failures_cond:
  assumes "P is NCSP" "Q is NCSP"
  shows "fl\<lbrakk>P \<triangleleft> b \<triangleright>\<^sub>R Q\<rbrakk>s = (if (\<lbrakk>b\<rbrakk>\<^sub>es) then fl\<lbrakk>P\<rbrakk>s else fl\<lbrakk>Q\<rbrakk>s)"
  by (rdes_simp cls: assms, simp add: divergences_def failures_def rdes closure rpred assms, rel_auto)

lemma divergences_guard: 
  assumes "P is NCSP"
  shows "dv\<lbrakk>g &\<^sub>C P\<rbrakk>s = (if (\<lbrakk>g\<rbrakk>\<^sub>es) then dv\<lbrakk>g &\<^sub>C P\<rbrakk>s else {})"
  by (rdes_simp cls: assms, simp add: divergences_def traces_def rdes closure rpred assms, rel_auto)

lemma traces_do: "tr\<lbrakk>do\<^sub>C(e)\<rbrakk>s = {([\<lbrakk>e\<rbrakk>\<^sub>es], s)}"
  by (rdes_simp, simp add: traces_def rdes closure rpred, rel_auto)

lemma failures_do: "fl\<lbrakk>do\<^sub>C(e)\<rbrakk>s = {([], E) | E. \<lbrakk>e\<rbrakk>\<^sub>es \<notin> E}"
  by (rdes_simp, simp add: failures_def rdes closure rpred usubst, rel_auto)

lemma divergences_do: "dv\<lbrakk>do\<^sub>C(e)\<rbrakk>s = {}"
  by (rel_auto)

lemma divergences_seq:
  fixes P :: "('s, 'e) action"
  assumes "P is NCSP" "Q is NCSP"
  shows "dv\<lbrakk>P ;; Q\<rbrakk>s = dv\<lbrakk>P\<rbrakk>s \<union> {t\<^sub>1 @ t\<^sub>2 | t\<^sub>1 t\<^sub>2 s\<^sub>0. (t\<^sub>1, s\<^sub>0) \<in> tr\<lbrakk>P\<rbrakk>s \<and> t\<^sub>2 \<in> dv\<lbrakk>Q\<rbrakk>s\<^sub>0}"
  (is "?lhs = ?rhs")
  oops

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

    from a2 have ndiv: "\<not> `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> (\<not>\<^sub>r pre\<^sub>R P)`"
      by (rel_auto)

    have t_minus_tr0: "tr\<^sub>0 @ (t - tr\<^sub>0) = t"
      using append_minus tr0 by blast

    from a3
    have wpr: "\<And>t\<^sub>0 s\<^sub>1.
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

      from a3 have c: "`\<^bold>\<forall> (s\<^sub>0, t\<^sub>0) \<bullet> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>t\<guillemotright> 
                                \<and> [$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> post\<^sub>R P 
                                \<Rightarrow> [$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright> - \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> pre\<^sub>R Q`"
        by (simp add: wp_rea_circus_form_alt[of "post\<^sub>R P" "pre\<^sub>R Q"] closure assms unrest usubst)
           (rel_simp)

      from c b(2-4) show False
        by (rel_auto)
    qed
      
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
      apply (auto intro:wpr simp add: taut_conj preP preQ postP postQ ndiv wpr t_minus_tr0)
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
      a5: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> post\<^sub>R Q`" and
      a6: "\<forall>t s\<^sub>1. `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> pre\<^sub>R P \<and>
                  [$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> post\<^sub>R P` \<longrightarrow>
                  t \<le> t\<^sub>1 @ t\<^sub>2 \<longrightarrow> \<not> `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>(t\<^sub>1 @ t\<^sub>2) - t\<guillemotright>] \<dagger> (\<not>\<^sub>r pre\<^sub>R Q)`"
    
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
      by (rel_auto, meson Prefix_Order.prefixI)

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

    from a6 
    have a6': "\<And> t s\<^sub>1. \<lbrakk> t \<le> t\<^sub>1 @ t\<^sub>2; `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> pre\<^sub>R P`; `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>] \<dagger> post\<^sub>R P` \<rbrakk> \<Longrightarrow>
                         `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>(t\<^sub>1 @ t\<^sub>2) - t\<guillemotright>] \<dagger> pre\<^sub>R Q`"
      apply (subst (asm) taut_not)
      apply (simp add: unrest_all_circus_vars_st assms closure unrest)
      apply (rel_auto)
      done

    have wpR: "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>] \<dagger> (post\<^sub>R P wp\<^sub>r pre\<^sub>R Q)`"
    proof -
      have "\<And> s\<^sub>1 t\<^sub>0. \<lbrakk> t\<^sub>0 \<le> t\<^sub>1 @ t\<^sub>2; `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> post\<^sub>R P` \<rbrakk>
                     \<Longrightarrow> `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>(t\<^sub>1 @ t\<^sub>2) - t\<^sub>0\<guillemotright>] \<dagger> pre\<^sub>R Q`"
      proof -
        fix s\<^sub>1 t\<^sub>0
        assume c:"t\<^sub>0 \<le> t\<^sub>1 @ t\<^sub>2" "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> post\<^sub>R P`"

        have preP': "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> pre\<^sub>R P`"
        proof -
          have "(pre\<^sub>R P)\<lbrakk>0,\<guillemotleft>t\<^sub>0\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<sqsubseteq> (pre\<^sub>R P)\<lbrakk>0,\<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>/$tr,$tr\<acute>\<rbrakk>"
            by (simp add: RC_prefix_refine closure assms c)
          hence "[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> pre\<^sub>R P \<sqsubseteq> [$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>] \<dagger> pre\<^sub>R P"
            by (rel_auto)
          thus ?thesis
            by (simp add: taut_refine_impl preP)
        qed


        with c a3 preP a6'[of t\<^sub>0 s\<^sub>1] show "`[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>(t\<^sub>1 @ t\<^sub>2) - t\<^sub>0\<guillemotright>] \<dagger> pre\<^sub>R Q`"
          by (simp)
      qed

      thus ?thesis
        apply (simp_all add: wp_rea_circus_form_alt assms closure unrest usubst rea_impl_alt_def)
        apply (simp add: R1_def usubst tcontr_alt_def)
        apply (auto intro!: taut_shAll_intro_2)
        apply (rule taut_impl_intro)
        apply (simp add: unrest_all_circus_vars_st_st' unrest closure assms)
        apply (rel_simp)
      done
    qed
    show "`([$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>] \<dagger> pre\<^sub>R P \<and>
         [$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>] \<dagger> (post\<^sub>R P wp\<^sub>r pre\<^sub>R Q)) \<and>
        [$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>] \<dagger> (post\<^sub>R P ;; post\<^sub>R Q)`"
      by (auto simp add: taut_conj preP postPQ wpR)
  qed
qed

lemma Cons_minus [simp]: "(a # t) - [a] = t"
  by (metis append_Cons append_Nil append_minus)
  
lemma traces_prefix: 
  assumes "P is NCSP"
  shows "tr\<lbrakk>\<guillemotleft>a\<guillemotright> \<rightarrow>\<^sub>C P\<rbrakk>s = {(a # t, s') | t s'. (t, s') \<in> tr\<lbrakk>P\<rbrakk>s}"
  apply (auto simp add: PrefixCSP_def traces_seq traces_do divergences_do lit.rep_eq assms closure Healthy_if trace_divergence_disj)
  apply (meson assms trace_divergence_disj)
  done

subsection \<open> Deadlock Freedom \<close>

text \<open> The following is a specification for deadlock free actions. In any intermediate observation,
  there must be at least one enabled event. \<close>

definition CDF :: "('s, 'e) action" where
[rdes_def]: "CDF = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> (\<Sqinter> (s, t, E, e) \<bullet> \<E>(\<guillemotleft>s\<guillemotright>, \<guillemotleft>t\<guillemotright>, \<guillemotleft>insert e E\<guillemotright>)) \<diamondop> true\<^sub>r)"

lemma CDF_NCSP [closure]: "CDF is NCSP"
  apply (simp add: CDF_def) 
  apply (rule NCSP_rdes_intro)
  apply (simp_all add: closure unrest)
  done

lemma CDF_seq_idem: "CDF ;; CDF = CDF"
  by (rdes_eq)

lemma CDF_refine_intro: "CDF \<sqsubseteq> P \<Longrightarrow> CDF \<sqsubseteq> (CDF ;; P)"
  by (metis CDF_seq_idem urel_dioid.mult_isol)

lemma Skip_deadlock_free: "CDF \<sqsubseteq> Skip"
  by (rdes_refine)

lemma CDF_ext_st [alpha]: "CDF \<oplus>\<^sub>p abs_st\<^sub>L = CDF"
  by (rdes_eq) 

end