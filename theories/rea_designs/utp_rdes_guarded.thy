section \<open> Guarded Recursion \<close>

theory utp_rdes_guarded
  imports utp_rdes_productive
begin

subsection \<open> Traces with a size measure \<close>

text \<open> Guarded recursion relies on our ability to measure the trace's size, in order to see if it
  is decreasing on each iteration. Thus, we here equip the trace algebra with the @{term size}
  function that provides this. \<close>

class size_trace = trace + size +
  assumes
    size_zero: "size 0 = 0" and
    size_nzero: "s > 0 \<Longrightarrow> size(s) > 0" and
    size_plus: "size (s + t) = size(s) + size(t)"
  \<comment> \<open> These axioms may be stronger than necessary. In particular, @{thm size_nzero} requires that
       a non-empty trace have a positive size. But this may not be the case with all trace models
       and is possibly more restrictive than necessary. In future we will explore weakening. \<close>
begin

lemma size_mono: "s \<le> t \<Longrightarrow> size(s) \<le> size(t)"
  by (metis le_add1 local.diff_add_cancel_left' local.size_plus)

lemma size_strict_mono: "s < t \<Longrightarrow> size(s) < size(t)"
  by (metis cancel_ab_semigroup_add_class.add_diff_cancel_left' local.diff_add_cancel_left' local.less_iff local.minus_gr_zero_iff local.size_nzero local.size_plus zero_less_diff)

lemma trace_strict_prefixE: "xs < ys \<Longrightarrow> (\<And>zs. \<lbrakk> ys = xs + zs; size(zs) > 0 \<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (metis local.diff_add_cancel_left' local.less_iff local.minus_gr_zero_iff local.size_nzero)

lemma size_minus_trace: "y \<le> x \<Longrightarrow> size(x - y) = size(x) - size(y)"
  by (metis diff_add_inverse local.diff_add_cancel_left' local.size_plus)

end

text \<open> Both natural numbers and lists are measurable trace algebras. \<close>

instance nat :: size_trace
  by (intro_classes, simp_all)

instance list :: (type) size_trace
  by (intro_classes, simp_all add: less_list_def' plus_list_def prefix_length_less)

syntax
  "_usize"      :: "logic \<Rightarrow> logic" ("size\<^sub>u'(_')")

translations
  "size\<^sub>u(t)" == "CONST uop CONST size t"

subsection \<open> Guardedness \<close>

definition gvrt :: "(('t::size_trace,'\<alpha>) rp \<times> ('t,'\<alpha>) rp) chain" where
[upred_defs]: "gvrt(n) \<equiv> ($tr \<le>\<^sub>u $tr\<acute> \<and> size\<^sub>u(&tt) <\<^sub>u \<guillemotleft>n\<guillemotright>)"

lemma gvrt_chain: "chain gvrt"
  apply (simp add: chain_def, safe)
  apply (rel_simp)
  apply (rel_simp)+
done

lemma gvrt_limit: "\<Sqinter> (range gvrt) = ($tr \<le>\<^sub>u $tr\<acute>)"
  by (rel_auto)

definition Guarded :: "(('t::size_trace,'\<alpha>) hrel_rp \<Rightarrow> ('t,'\<alpha>) hrel_rp) \<Rightarrow> bool" where
[upred_defs]: "Guarded(F) = (\<forall> X n. (F(X) \<and> gvrt(n+1)) = (F(X \<and> gvrt(n)) \<and> gvrt(n+1)))"

lemma GuardedI: "\<lbrakk> \<And> X n. (F(X) \<and> gvrt(n+1)) = (F(X \<and> gvrt(n)) \<and> gvrt(n+1)) \<rbrakk> \<Longrightarrow> Guarded F"
  by (simp add: Guarded_def)

text \<open> Guarded reactive designs yield unique fixed-points. \<close>

theorem guarded_fp_uniq:
  assumes "mono F" "F \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H" "Guarded F"
  shows "\<mu> F = \<nu> F"
proof -
  have "constr F gvrt"
    using assms    
    by (auto simp add: constr_def gvrt_chain Guarded_def tcontr_alt_def')
  hence "($tr \<le>\<^sub>u $tr\<acute> \<and> \<mu> F) = ($tr \<le>\<^sub>u $tr\<acute> \<and> \<nu> F)"
    apply (rule constr_fp_uniq)
     apply (simp add: assms)
    using gvrt_limit apply blast
    done
  moreover have "($tr \<le>\<^sub>u $tr\<acute> \<and> \<mu> F) = \<mu> F"
  proof -
    have "\<mu> F is R1"
      by (rule SRD_healths(1), rule Healthy_mu, simp_all add: assms)
    thus ?thesis
      by (metis Healthy_def R1_def conj_comm)
  qed
  moreover have "($tr \<le>\<^sub>u $tr\<acute> \<and> \<nu> F) = \<nu> F"
  proof -
    have "\<nu> F is R1"
      by (rule SRD_healths(1), rule Healthy_nu, simp_all add: assms)
    thus ?thesis
      by (metis Healthy_def R1_def conj_comm)
  qed
  ultimately show ?thesis
    by (simp)
qed

lemma Guarded_const [closure]: "Guarded (\<lambda> X. P)"
  by (simp add: Guarded_def)

lemma UINF_Guarded [closure]:
  assumes  "\<And> P. P \<in> A \<Longrightarrow> Guarded P"
  shows "Guarded (\<lambda> X. \<Sqinter>P\<in>A \<bullet> P(X))"
proof (rule GuardedI)
  fix X n
  have "\<And> Y. ((\<Sqinter>P\<in>A \<bullet> P Y) \<and> gvrt(n+1)) = ((\<Sqinter>P\<in>A \<bullet> (P Y \<and> gvrt(n+1))) \<and> gvrt(n+1))"
  proof -
    fix Y
    let ?lhs = "((\<Sqinter>P\<in>A \<bullet> P Y) \<and> gvrt(n+1))" and ?rhs = "((\<Sqinter>P\<in>A \<bullet> (P Y \<and> gvrt(n+1))) \<and> gvrt(n+1))"
    have a:"?lhs\<lbrakk>false/$ok\<rbrakk> = ?rhs\<lbrakk>false/$ok\<rbrakk>"
      by (rel_auto)
    have b:"?lhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>true/$wait\<rbrakk> = ?rhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>true/$wait\<rbrakk>"
      by (rel_auto)
    have c:"?lhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>false/$wait\<rbrakk> = ?rhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>false/$wait\<rbrakk>"
      by (rel_auto)
    show "?lhs = ?rhs"
      using a b c
      by (rule_tac bool_eq_splitI[of "in_var ok"], simp, rule_tac bool_eq_splitI[of "in_var wait"], simp_all)
  qed
  moreover have "((\<Sqinter>P\<in>A \<bullet> (P X \<and> gvrt(n+1))) \<and> gvrt(n+1)) =  ((\<Sqinter>P\<in>A \<bullet> (P (X \<and> gvrt(n)) \<and> gvrt(n+1))) \<and> gvrt(n+1))"
  proof -
    have "(\<Sqinter>P\<in>A \<bullet> (P X \<and> gvrt(n+1))) = (\<Sqinter>P\<in>A \<bullet> (P (X \<and> gvrt(n)) \<and> gvrt(n+1)))"
    proof (rule UINF_cong)
      fix P assume "P \<in> A"
      thus "(P X \<and> gvrt(n+1)) = (P (X \<and> gvrt(n)) \<and> gvrt(n+1))"
        using Guarded_def assms by blast
    qed
    thus ?thesis by simp
  qed
  ultimately show "((\<Sqinter>P\<in>A \<bullet> P X) \<and> gvrt(n+1)) = ((\<Sqinter>P\<in>A \<bullet> (P (X \<and> gvrt(n)))) \<and> gvrt(n+1))"
    by simp
qed

lemma intChoice_Guarded [closure]:
  assumes "Guarded P" "Guarded Q"
  shows "Guarded (\<lambda> X. P(X) \<sqinter> Q(X))"
proof -
  have "Guarded (\<lambda> X. \<Sqinter>F\<in>{P,Q} \<bullet> F(X))"
    by (rule UINF_Guarded, auto simp add: assms)
  thus ?thesis
    by (simp)
qed

lemma cond_srea_Guarded [closure]:
  assumes "Guarded P" "Guarded Q"
  shows "Guarded (\<lambda> X. P(X) \<triangleleft> b \<triangleright>\<^sub>R Q(X))"
  using assms by (rel_auto)

text \<open> A tail recursive reactive design with a productive body is guarded. \<close>

lemma Guarded_if_Productive [closure]:
  fixes P :: "('s, 't::size_trace,'\<alpha>) hrel_rsp"
  assumes "P is NSRD" "P is Productive"
  shows "Guarded (\<lambda> X. P ;; SRD(X))"
proof (clarsimp simp add: Guarded_def)
  \<comment> \<open> We split the proof into three cases corresponding to valuations for ok, wait, and wait'
        respectively. \<close>
  fix X n
  have a:"(P ;; SRD(X) \<and> gvrt (Suc n))\<lbrakk>false/$ok\<rbrakk> =
        (P ;; SRD(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>false/$ok\<rbrakk>"
    by (simp add: usubst closure SRD_left_zero_1 assms)
  have b:"((P ;; SRD(X) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk> =
          ((P ;; SRD(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk>"
    by (simp add: usubst closure SRD_left_zero_2 assms)
  have c:"((P ;; SRD(X) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>false/$wait\<rbrakk> =
          ((P ;; SRD(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>false/$wait\<rbrakk>"
  proof -
    have 1:"(P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (SRD X)\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
          (P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (SRD (X \<and> gvrt n))\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
      by (metis (no_types, lifting) Healthy_def R3h_wait_true SRD_healths(3) SRD_idem)
    have 2:"(P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (SRD X)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
          (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (SRD (X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
    proof -
      have exp:"\<And> Y::('s, 't,'\<alpha>) hrel_rsp. (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (SRD Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
                  ((((\<not>\<^sub>r pre\<^sub>R P) ;; (SRD(Y))\<lbrakk>false/$wait\<rbrakk> \<or> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (SRD Y)\<lbrakk>true,false/$ok,$wait\<rbrakk>))
                     \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
      proof -
        fix Y :: "('s, 't,'\<alpha>) hrel_rsp"

        have "(P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (SRD Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
              ((\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (SRD Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (metis (no_types) Healthy_def Productive_form assms(1) assms(2) NSRD_is_SRD)
        also have "... =
             ((R1(R2c(pre\<^sub>R(P) \<Rightarrow> ($ok\<acute> \<and> post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (SRD Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def RD1_def RD2_def usubst unrest assms closure design_def)
        also have "... =
             (((\<not>\<^sub>r pre\<^sub>R(P) \<or> ($ok\<acute> \<and> post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (SRD Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (simp add: impl_alt_def R2c_disj R1_disj R2c_not  assms closure R2c_and
              R2c_preR rea_not_def R1_extend_conj' R2c_ok' R2c_post_SRD R1_tr_less_tr' R2c_tr_less_tr')
        also have "... =
             ((((\<not>\<^sub>r pre\<^sub>R P) ;; (SRD(Y))\<lbrakk>false/$wait\<rbrakk> \<or> ($ok\<acute> \<and> post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (SRD Y)\<lbrakk>false/$wait\<rbrakk>)) \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (simp add: usubst unrest assms closure seqr_or_distl NSRD_neg_pre_left_zero)
        also have "... =
             ((((\<not>\<^sub>r pre\<^sub>R P) ;; (SRD(Y))\<lbrakk>false/$wait\<rbrakk> \<or> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (SRD Y)\<lbrakk>true,false/$ok,$wait\<rbrakk>)) \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
        proof -
          have "($ok\<acute> \<and> post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (SRD Y)\<lbrakk>false/$wait\<rbrakk> =
                ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) \<and> $ok\<acute> =\<^sub>u true) ;; (SRD Y)\<lbrakk>false/$wait\<rbrakk>"
            by (rel_blast)
          also have "... = (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)\<lbrakk>true/$ok\<acute>\<rbrakk> ;; (SRD Y)\<lbrakk>false/$wait\<rbrakk>\<lbrakk>true/$ok\<rbrakk>"
            using seqr_left_one_point[of ok "(post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)" True "(SRD Y)\<lbrakk>false/$wait\<rbrakk>"]
            by (simp add: true_alt_def[THEN sym])
          finally show ?thesis by (simp add: usubst unrest)
        qed
        finally
        show "(P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (SRD Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
                 ((((\<not>\<^sub>r pre\<^sub>R P) ;; (SRD(Y))\<lbrakk>false/$wait\<rbrakk> \<or> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (SRD Y)\<lbrakk>true,false/$ok,$wait\<rbrakk>))
                 \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>" .
      qed

      have 1:"((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (SRD X)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<and> gvrt (Suc n)) =
              ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (SRD (X \<and> gvrt n))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<and> gvrt (Suc n))"
        apply (rel_auto)
         apply (rename_tac tr st more ok wait tr' st' more' tr\<^sub>0 st\<^sub>0 more\<^sub>0 ok')
         apply (rule_tac x="tr\<^sub>0" in exI, rule_tac x="st\<^sub>0" in exI, rule_tac x="more\<^sub>0" in exI)
         apply (simp)
         apply (erule trace_strict_prefixE)
         apply (rename_tac tr st ref ok wait tr' st' ref' tr\<^sub>0 st\<^sub>0 ref\<^sub>0 ok' zs)
         apply (rule_tac x="False" in exI)
         apply (simp add: size_minus_trace)
         apply (subgoal_tac "size(tr) < size(tr\<^sub>0)")
          apply (simp add: less_diff_conv2 size_mono)
        using size_strict_mono apply blast
        apply (rename_tac tr st more ok wait tr' st' more' tr\<^sub>0 st\<^sub>0 more\<^sub>0 ok')
        apply (rule_tac x="tr\<^sub>0" in exI, rule_tac x="st\<^sub>0" in exI, rule_tac x="more\<^sub>0" in exI)
        apply (simp)
        apply (erule trace_strict_prefixE)
        apply (rename_tac tr st more ok wait tr' st' more' tr\<^sub>0 st\<^sub>0 more\<^sub>0 ok' zs)
        apply (auto simp add: size_minus_trace)
        apply (subgoal_tac "size(tr) < size(tr\<^sub>0)")
         apply (simp add: less_diff_conv2 size_mono)
        using size_strict_mono apply blast
        done
      have 2:"(\<not>\<^sub>r pre\<^sub>R P) ;; (SRD X)\<lbrakk>false/$wait\<rbrakk> = (\<not>\<^sub>r pre\<^sub>R P) ;; (SRD(X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk>"
        by (simp add: NSRD_neg_pre_left_zero closure assms SRD_healths)
      show ?thesis
        by (simp add: exp 1 2 utp_pred_laws.inf_sup_distrib2)
    qed

    show ?thesis
    proof -
      have "(P ;; (SRD X) \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
          ((P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (SRD X)\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<or>
          (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (SRD X)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
        by (subst seqr_bool_split[of wait], simp_all add: usubst utp_pred_laws.distrib(4))

      also
      have "... = ((P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (SRD (X \<and> gvrt n))\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<or>
                 (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (SRD (X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
        by (simp add: 1 2)

      also
      have "... = ((P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (SRD (X \<and> gvrt n))\<lbrakk>true/$wait\<rbrakk> \<or>
                    P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (SRD (X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk>) \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
        by (simp add: usubst utp_pred_laws.distrib(4))

      also have "... = (P ;; (SRD (X \<and> gvrt n)) \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
        by (subst seqr_bool_split[of wait], simp_all add: usubst)
      finally show ?thesis by (simp add: usubst)
    qed

  qed
  show "(P ;; SRD(X) \<and> gvrt (Suc n)) = (P ;; SRD(X \<and> gvrt n) \<and> gvrt (Suc n))"
    apply (rule_tac bool_eq_splitI[of "in_var ok"])
      apply (simp_all add: a)
    apply (rule_tac bool_eq_splitI[of "in_var wait"])
      apply (simp_all add: b c)
  done
qed

subsection \<open> Tail recursive fixed-point calculations \<close>

declare upred_semiring.power_Suc [simp]

lemma mu_csp_form_1 [rdes]:
  fixes P :: "('s, 't::size_trace,'\<alpha>) hrel_rsp"
  assumes "P is NSRD" "P is Productive"
  shows "(\<mu> X \<bullet> P ;; SRD(X)) = (\<Sqinter>i \<bullet> P \<^bold>^ (i+1)) ;; Miracle"
proof -
  have 1:"Continuous (\<lambda>X. P ;; SRD X)"
    using SRD_Continuous
    by (clarsimp simp add: Continuous_def seq_SUP_distl[THEN sym], drule_tac x="A" in spec, simp)
  have 2: "(\<lambda>X. P ;; SRD X) \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
    by (blast intro: funcsetI closure assms)
  with 1 2 have "(\<mu> X \<bullet> P ;; SRD(X)) = (\<nu> X \<bullet> P ;; SRD(X))"
    by (simp add: guarded_fp_uniq Guarded_if_Productive[OF assms] funcsetI closure)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P ;; SRD X) ^^ i) false)"
    by (simp add: sup_continuous_lfp 1 sup_continuous_Continuous false_upred_def)
  also have "... = ((\<lambda>X. P ;; SRD X) ^^ 0) false \<sqinter> (\<Sqinter>i. ((\<lambda>X. P ;; SRD X) ^^ (i+1)) false)"
    by (subst Sup_power_expand, simp)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P ;; SRD X) ^^ (i+1)) false)"
    by (simp)
  also have "... = (\<Sqinter>i. P \<^bold>^ (i+1) ;; Miracle)"
  proof (rule SUP_cong, simp_all) 
    fix i
    show "P ;; SRD (((\<lambda>X. P ;; SRD X) ^^ i) false) = (P ;; P \<^bold>^ i) ;; Miracle"
    proof (induct i)
      case 0
      then show ?case
        by (simp, metis srdes_theory.healthy_top)
    next
      case (Suc i)
      then show ?case
        by (simp add: Healthy_if NSRD_is_SRD SRD_power_comp SRD_seqr_closure assms(1) seqr_assoc[THEN sym] srdes_theory.top_closed)
    qed
  qed
  also have "... = (\<Sqinter>i. P \<^bold>^ (i+1)) ;; Miracle"
    by (simp add: seq_Sup_distr)
  finally show ?thesis
    by (simp add: UINF_as_Sup_collect)
qed

lemma mu_csp_form_NSRD [closure]:
  fixes P :: "('s, 't::size_trace,'\<alpha>) hrel_rsp"
  assumes "P is NSRD" "P is Productive"
  shows "(\<mu> X \<bullet> P ;; SRD(X)) is NSRD"
  by (simp add: mu_csp_form_1 assms closure)

lemma mu_csp_form_1':
  fixes P :: "('s, 't::size_trace,'\<alpha>) hrel_rsp"
  assumes "P is NSRD" "P is Productive"
  shows "(\<mu> X \<bullet> P ;; SRD(X)) = (P ;; P\<^sup>\<star>) ;; Miracle"
proof -
  have "(\<mu> X \<bullet> P ;; SRD(X)) = (\<Sqinter> i\<in>UNIV \<bullet> P ;; P \<^bold>^ i) ;; Miracle"
    by (simp add: mu_csp_form_1 assms closure ustar_def)
  also have "... = (P ;; P\<^sup>\<star>) ;; Miracle"
    by (simp only: seq_UINF_distl[THEN sym], simp add: ustar_def)
  finally show ?thesis .
qed

declare upred_semiring.power_Suc [simp del]

end