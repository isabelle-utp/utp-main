section \<open> Linking to the Failures-Divergences Model \<close>

theory utp_circus_fdsem
  imports utp_circus_parallel utp_circus_recursion
begin

subsection {* Failures-Divergences Semantics *}

definition divergences :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> '\<phi> list set" ("dv\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "divergences P s = {t | t. `(\<not>\<^sub>r pre\<^sub>R(P))\<lbrakk>\<guillemotleft>s\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>`}"
  
definition traces :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> ('\<phi> list \<times> '\<sigma>) set" ("tr\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "traces P s = {(t,s') | t s'. `(pre\<^sub>R(P) \<and> post\<^sub>R(P))\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>/$st,$st\<acute>,$tr,$tr\<acute>\<rbrakk>`}"

definition failures :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> ('\<phi> list \<times> '\<phi> set) set" ("fl\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "failures P s = {(t,r) | t r. `(pre\<^sub>R(P) \<and> peri\<^sub>R(P))\<lbrakk>\<guillemotleft>r\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>/$ref\<acute>,$st,$tr,$tr\<acute>\<rbrakk>`}"
   
lemma traces_Skip:
  "tr\<lbrakk>Skip\<rbrakk>s = {([], s)}"
  by (simp add: traces_def rdes alpha closure, rel_simp)

lemma failures_Skip:
  "fl\<lbrakk>Skip\<rbrakk>s = {}"
  by (simp add: failures_def, rdes_calc)

lemma divergences_Skip:
  "dv\<lbrakk>Skip\<rbrakk>s = {}"
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

lemma traces_seq:
  fixes P :: "('s, 'e) action"
  assumes "P is NCSP" "Q is NCSP"
  shows "tr\<lbrakk>P ;; Q\<rbrakk>s = 
          {(t\<^sub>1 @ t\<^sub>2, s') | t\<^sub>1 t\<^sub>2 s\<^sub>0 s'. (t\<^sub>1, s\<^sub>0) \<in> tr\<lbrakk>P\<rbrakk>s \<and> (t\<^sub>2, s') \<in> tr\<lbrakk>Q\<rbrakk>s\<^sub>0 \<and> (t\<^sub>1 @ t\<^sub>2) \<notin> dv\<lbrakk>P\<rbrakk>s }"
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
       apply (simp add: unrest_all_circus_vars closure unrest assms)
      apply (rel_auto)
      done
    from p1 have "`?\<sigma> \<dagger> (\<^bold>\<exists> st\<^sub>0 \<bullet> (post\<^sub>R P)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk>\<lbrakk>\<guillemotleft>st\<^sub>0\<guillemotright>/$st\<acute>\<rbrakk> ;; (post\<^sub>R Q)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>st\<^sub>0\<guillemotright>/$st\<rbrakk>)`"
      by (simp add: seqr_middle[of st, THEN sym])
    then obtain s\<^sub>0 where "`?\<sigma> \<dagger> ((post\<^sub>R P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> ;; (post\<^sub>R Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>)`"
      apply (simp add: usubst)
      apply (erule taut_shEx_elim)
       apply (simp add: unrest_all_circus_vars closure unrest assms)
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

    show "\<exists>t\<^sub>1 t\<^sub>2.
            t = t\<^sub>1 @ t\<^sub>2 \<and>
            (\<exists>s\<^sub>0. `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>] \<dagger> pre\<^sub>R P \<and>
                    [$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>] \<dagger> post\<^sub>R P` \<and>
                   `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> pre\<^sub>R Q \<and>
                    [$st \<mapsto>\<^sub>s \<guillemotleft>s\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>2\<guillemotright>] \<dagger> post\<^sub>R Q` \<and>
                    \<not> `[$st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1 @ t\<^sub>2\<guillemotright>] \<dagger> (\<not>\<^sub>r pre\<^sub>R P)`)"
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

subsection {* Deadlock Freedom *}
  
definition DF :: "'e set \<Rightarrow> ('s, 'e) action" where
"DF(A) = (\<mu>\<^sub>C X \<bullet> (\<Sqinter> a\<in>A \<bullet> a \<^bold>\<rightarrow> Skip) ;; X)"
 
lemma DF_CSP [closure]: "A \<noteq> {} \<Longrightarrow> DF(A) is CSP"
  by (simp add: DF_def closure unrest)

end