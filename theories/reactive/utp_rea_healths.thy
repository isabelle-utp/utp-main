section \<open> Reactive Healthiness Conditions \<close>

theory utp_rea_healths
  imports utp_rea_core
begin

lemma typi: 
  "a A + (b A) = a A + (d A) \<Longrightarrow> \<exists>d. (\<lambda>ba. a ba + b ba) = (\<lambda>b. a b + d b)"
  by auto

lemma typi2:
  "(\<exists>d. (\<lambda>ba. a ba + b ba) = (\<lambda>b. a b + d b) \<and> (\<forall>A. prefix_rel (a A) (d A)))
   =
   (\<exists>d. \<forall>A. a A + b A = a A + d A \<and> prefix_rel (a A) (d A))"
  apply auto
  by metis

lemma
  "(\<not> (\<forall>A. prefix_rel (a A) (b A)) \<longrightarrow> (\<exists>d. (\<lambda>ba. a ba + b ba) = (\<lambda>b. a b + d b) \<and> (\<forall>A. prefix_rel (a A) (d A))))
   =
   ((\<forall>A. prefix_rel (a A) (b A)) \<or> (\<exists>d. \<forall>A. a A + b A = a A + d A \<and> prefix_rel (a A) (d A)))"
  using typi2 
  apply blast
  done



(*
instance uexpr :: (fzero_sum_zero, type) fzero_sum_zero
  apply (intro_classes) 
  apply (simp add: fzero_uexpr_def plus_uexpr_def, transfer, auto)
  sledgehammer[debug=true]*)

(*
lemma
  "(\<forall>A. prefix_rel (a A) (b A))
    \<longrightarrow>
   (\<exists>d. \<forall>A. a A + b A = a A + d A \<and> prefix_rel (a A) (d A))"
  apply auto
  sledgehammer[debug=true]
*)
(*
lemma "(\<not> (\<forall>A. (a A) \<inter> (b A) = {}) \<longrightarrow> (\<exists>d. (\<lambda>ba. a ba \<union> b ba) = (\<lambda>b. a b \<union> d b) \<and> (\<forall>A. (a A) \<inter> (d A) = {})))
        =
        ((\<forall>A. (a A) \<inter> (b A) = {}) \<or> (\<exists>d. \<forall>A. a A \<union> b A = a A \<union> d A \<and> (a A) \<inter> (d A) = {}))"
  apply simp
  also have "... = ((\<forall>A. prefix_rel (a A) (b A)) \<or> (\<forall>A. \<exists>d. a A + b A = a A + d A \<and> prefix_rel (a A) (d A)))"
*)
(*
lemma opo: "\<not>prefix_rel a b \<longrightarrow> (\<exists>d. (a + b) = (a + d) \<and> (prefix_rel (a) (d)))"
  using prefix_sum by blast

lemma
  assumes "\<forall>a b. \<exists>d. a + d = b \<and> R d b"
  shows "\<exists>f d. a + (f d) = b \<and> R (f d) b"
proof -
  have "(\<exists>f d. a + (f d) = b \<and> R (f d) b)
        =
        (\<exists>x. a + x = b \<and> R x b)"
    by auto
  then show ?thesis
  using assms 
  by auto
qed

lemma
  shows "(\<exists>d. \<exists>A. a A + b A = a A + d A)
          =
         (\<exists>d. \<exists>A. a A + b A = a A + d)"
  apply auto
  nitpick

lemma 
  fixes a :: "'b::{plus}"
  assumes "\<forall>a b. (\<exists>d. ((a::'b) + b) = (a + d) \<longrightarrow> b = d \<and> R d b)" 
  shows "(\<exists>d x. (a + b) = (a + d x) \<longrightarrow> b = d x \<and> R (d x) b)"
  using assms 


lemma 
  fixes a :: "'b::{plus,prefix_rel}"
  assumes "\<forall>a b. (\<exists>d. ((a::'b) + b) = (a + d) \<and> (prefix_rel (a) (d)))" "\<not>prefix_rel a b"
  shows "\<exists>d x. (a + b) = (a + d x) \<and> (prefix_rel (a) (d x))"
  apply (rule exI)
  using assms apply auto

lemma opo: "\<exists>f. (a A) + (b A) = (a A) + (f A) \<and> (prefix_rel (a A) (f A))"
  using prefix_sum apply (simp only:Ex_def)
  apply auto

lemma "\<exists>d. \<forall>A. (a A) + (b A) = (a A) + (d A) \<and> (prefix_rel (a A) (d A))"
  using opo 

instantiation uexpr :: (prefix_rel, type) prefix_rel
begin

definition prefix_rel_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> (bool, 'b) uexpr" where
"prefix_rel_uexpr a b = true"

lift_definition prefix_rel_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> bool"
  is "\<lambda> P Q. \<exists>A. prefix_rel (P A) (Q A)" .
(*  is "\<lambda> P Q A. (prefix_rel (P A) (Q A))" . *)
 
instance apply intro_classes
        apply (simp_all add:fzero_uexpr_def  )
     apply (simp add: prefix_rel_sym utp_rea_healths.prefix_rel_uexpr.rep_eq)
    apply (simp add: prefix_rel_zero uop_ueval utp_rea_healths.prefix_rel_uexpr.rep_eq)
  
   apply (simp add: plus_uexpr_def)
   apply (transfer)
  sledgehammer[debug=true]
proof -
  have "(\<not> (\<forall>A. prefix_rel (a A) (b A)) \<longrightarrow> (\<exists>d. (\<lambda>ba. a ba + b ba) = (\<lambda>b. a b + d b) \<and> (\<forall>A. prefix_rel (a A) (d A))))
        =
        ((\<forall>A. prefix_rel (a A) (b A)) \<or> (\<exists>d. \<forall>A. a A + b A = a A + d A \<and> prefix_rel (a A) (d A)))"
    using typi2 by blast
  also have "... = (((\<forall>A. prefix_rel (a A) (b A)) \<and> (\<exists>d. \<forall>A. a A + b A = a A + d A \<and> prefix_rel (a A) (d A))) 
                    \<or> (\<exists>d. \<forall>A. a A + b A = a A + d A \<and> prefix_rel (a A) (d A)))"
    by auto
  also have "... = (\<exists>d. \<forall>A. a A + b A = a A + d A \<and> prefix_rel (a A) (d A))"
    by auto
  also have "... = True"
    apply auto
  proof -
    have "(\<forall>A. \<exists>d.  a A + b A = a A + d A \<and> prefix_rel (a A) (d A))
          =
          True"
    apply auto
  
  apply (rule typi2)
  
       apply (simp add: bop_ueval plus_uexpr_def uop_ueval)
      
      
      
  apply (simp add: plus_uexpr_def uop_ueval )
  
      apply auto
end*)

subsection \<open> R1: Events cannot be undone \<close> 

definition R1 :: "('t::fzero_weak_trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
R1_def [upred_defs]: "R1 (P) = (P \<and> ($tr \<le>\<^sub>u $tr\<acute>))"

lemma R1_idem: "R1(R1(P)) = R1(P)"
  by pred_auto

lemma R1_Idempotent [closure]: "Idempotent R1"
  by (simp add: Idempotent_def R1_idem)

lemma R1_mono: "P \<sqsubseteq> Q \<Longrightarrow> R1(P) \<sqsubseteq> R1(Q)"
  by pred_auto

lemma R1_Monotonic: "Monotonic R1"
  by (simp add: mono_def R1_mono)

lemma R1_Continuous: "Continuous R1"
  by (auto simp add: Continuous_def, rel_auto)

lemma R1_unrest [unrest]: "\<lbrakk> x \<bowtie> in_var tr; x \<bowtie> out_var tr; x \<sharp> P \<rbrakk> \<Longrightarrow> x \<sharp> R1(P)"
  by (simp add: R1_def unrest lens_indep_sym)

lemma R1_false: "R1(false) = false"
  by pred_auto

lemma R1_conj: "R1(P \<and> Q) = (R1(P) \<and> R1(Q))"
  by pred_auto

lemma conj_R1_closed_1 [closure]: "P is R1 \<Longrightarrow> (P \<and> Q) is R1"
  by (rel_blast)

lemma conj_R1_closed_2 [closure]: "Q is R1 \<Longrightarrow> (P \<and> Q) is R1"
  by (rel_blast)

lemma R1_disj: "R1(P \<or> Q) = (R1(P) \<or> R1(Q))"
  by pred_auto

lemma disj_R1_closed [closure]: "\<lbrakk> P is R1; Q is R1 \<rbrakk> \<Longrightarrow> (P \<or> Q) is R1"
  by (simp add: Healthy_def R1_def utp_pred_laws.inf_sup_distrib2)

lemma R1_impl: "R1(P \<Rightarrow> Q) = ((\<not> R1(\<not> P)) \<Rightarrow> R1(Q))"
  by (rel_auto)

lemma R1_inf: "R1(P \<sqinter> Q) = (R1(P) \<sqinter> R1(Q))"
  by pred_auto

lemma R1_USUP:
  "R1(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> R1(P(i)))"
  by (rel_auto)

lemma R1_Sup [closure]: "\<lbrakk> \<And> P. P \<in> A \<Longrightarrow> P is R1; A \<noteq> {} \<rbrakk> \<Longrightarrow> \<Sqinter> A is R1"
  using R1_Continuous by (auto simp add: Continuous_def Healthy_def)

lemma R1_UINF:
  assumes "A \<noteq> {}"
  shows "R1(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> R1(P(i)))"
  using assms by (rel_auto)

lemma R1_UINF_ind:
  "R1(\<Squnion> i \<bullet> P(i)) = (\<Squnion> i \<bullet> R1(P(i)))"
  by (rel_auto)

lemma UINF_ind_R1_closed [closure]:
  "\<lbrakk> \<And> i. P(i) is R1 \<rbrakk> \<Longrightarrow> (\<Sqinter> i \<bullet> P(i)) is R1"
  by (rel_blast)

lemma UINF_R1_closed [closure]:
  "\<lbrakk> \<And> i. P i is R1 \<rbrakk> \<Longrightarrow> (\<Sqinter> i \<in> A \<bullet> P i) is R1"
  by (rel_blast)

(* TODO: Why use a list here?
lemma tr_ext_conj_R1 [closure]: 
  "$tr\<acute> =\<^sub>u $tr ^\<^sub>u e \<and> P is R1"
  by (rel_auto, simp add: Prefix_Order.prefixI) *)

lemma tr_id_conj_R1 [closure]: 
  "$tr\<acute> =\<^sub>u $tr \<and> P is R1"
  by (rel_auto)

lemma R1_extend_conj: "R1(P \<and> Q) = (R1(P) \<and> Q)"
  by pred_auto

lemma R1_extend_conj': "R1(P \<and> Q) = (P \<and> R1(Q))"
  by pred_auto

lemma R1_cond: "R1(P \<triangleleft> b \<triangleright> Q) = (R1(P) \<triangleleft> b \<triangleright> R1(Q))"
  by (rel_auto)

lemma R1_cond': "R1(P \<triangleleft> b \<triangleright> Q) = (R1(P) \<triangleleft> R1(b) \<triangleright> R1(Q))"
  by (rel_auto)

lemma R1_negate_R1: "R1(\<not> R1(P)) = R1(\<not> P)"
  by pred_auto

lemma R1_wait_true [usubst]: "(R1 P)\<^sub>t = R1(P)\<^sub>t"
  by pred_auto

lemma R1_wait_false [usubst]: "(R1 P) \<^sub>f = R1(P) \<^sub>f"
  by pred_auto

lemma R1_wait'_true [usubst]: "(R1 P)\<lbrakk>true/$wait\<acute>\<rbrakk> = R1(P\<lbrakk>true/$wait\<acute>\<rbrakk>)"
  by (rel_auto)

lemma R1_wait'_false [usubst]: "(R1 P)\<lbrakk>false/$wait\<acute>\<rbrakk> = R1(P\<lbrakk>false/$wait\<acute>\<rbrakk>)"
  by (rel_auto)

lemma R1_wait_false_closed [closure]: "P is R1 \<Longrightarrow> P\<lbrakk>false/$wait\<rbrakk> is R1"
  by (rel_auto)

lemma R1_wait'_false_closed [closure]: "P is R1 \<Longrightarrow> P\<lbrakk>false/$wait\<acute>\<rbrakk> is R1"
  by (rel_auto)

lemma R1_skip: "R1(II) = II"
  by (rel_auto)

lemma skip_is_R1 [closure]: "II is R1"
  by (rel_auto)

lemma subst_R1: "\<lbrakk> $tr \<sharp> \<sigma>; $tr\<acute> \<sharp> \<sigma>  \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> (R1 P) = R1(\<sigma> \<dagger> P)"
  by (simp add: R1_def usubst)
  
lemma subst_R1_closed [closure]: "\<lbrakk> $tr \<sharp> \<sigma>; $tr\<acute> \<sharp> \<sigma>; P is R1 \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> P is R1"
  by (metis Healthy_def subst_R1)

lemma R1_by_refinement:
  "P is R1 \<longleftrightarrow> (($tr \<le>\<^sub>u $tr\<acute>) \<sqsubseteq> P)"
  by (rel_blast)

(* TODO: Why use a list here? 
lemma R1_trace_extension [closure]:
  "$tr\<acute> \<ge>\<^sub>u $tr ^\<^sub>u e is R1"
  by (rel_auto) *)
    
lemma tr_le_trans:
  "(($tr \<le>\<^sub>u $tr\<acute>) ;; ($tr \<le>\<^sub>u $tr\<acute>)) = ($tr \<le>\<^sub>u $tr\<acute>)"
  apply (rel_simp)
  using order_trans by auto
    
lemma R1_seqr:
  "R1(R1(P) ;; R1(Q)) = (R1(P) ;; R1(Q))"
  apply (rel_simp)
  using order_trans by blast

lemma R1_seqr_closure [closure]:
  assumes "P is R1" "Q is R1"
  shows "(P ;; Q) is R1"
  using assms unfolding R1_by_refinement
  by (metis seqr_mono tr_le_trans)

lemma R1_power [closure]: "P is R1 \<Longrightarrow> P\<^bold>^n is R1"
  by (induct n, simp_all add: upred_semiring.power_Suc closure)

lemma R1_true_comp [simp]: "(R1(true) ;; R1(true)) = R1(true)"
  apply (rel_simp)
  using order_trans by auto

lemma R1_ok'_true: "(R1(P))\<^sup>t = R1(P\<^sup>t)"
  by pred_auto

lemma R1_ok'_false: "(R1(P))\<^sup>f = R1(P\<^sup>f)"
  by pred_auto

lemma R1_ok_true: "(R1(P))\<lbrakk>true/$ok\<rbrakk> = R1(P\<lbrakk>true/$ok\<rbrakk>)"
  by pred_auto

lemma R1_ok_false: "(R1(P))\<lbrakk>false/$ok\<rbrakk> = R1(P\<lbrakk>false/$ok\<rbrakk>)"
  by pred_auto

lemma seqr_R1_true_right: "((P ;; R1(true)) \<or> P) = (P ;; ($tr \<le>\<^sub>u $tr\<acute>))"
  by (rel_auto)

lemma conj_R1_true_right: "(P;;R1(true) \<and> Q;;R1(true)) ;; R1(true) = (P;;R1(true) \<and> Q;;R1(true))"
  apply (rel_auto) using dual_order.trans
  using order_trans by blast+

lemma R1_extend_conj_unrest: "\<lbrakk> $tr \<sharp> Q; $tr\<acute> \<sharp> Q \<rbrakk> \<Longrightarrow> R1(P \<and> Q) = (R1(P) \<and> Q)"
  by pred_auto

lemma R1_extend_conj_unrest': "\<lbrakk> $tr \<sharp> P; $tr\<acute> \<sharp> P \<rbrakk> \<Longrightarrow> R1(P \<and> Q) = (P \<and> R1(Q))"
  by pred_auto

lemma R1_tr'_eq_tr: "R1($tr\<acute> =\<^sub>u $tr) = ($tr\<acute> =\<^sub>u $tr)"
  by (rel_auto)

lemma R1_tr_less_tr': "R1($tr <\<^sub>u $tr\<acute>) = ($tr <\<^sub>u $tr\<acute>)"
  apply (rel_simp)
  using less_le_not_le by blast

lemma tr_strict_prefix_R1_closed [closure]: "$tr <\<^sub>u $tr\<acute> is R1"
  apply (rel_simp)
  using less_imp_le by blast

    
lemma R1_H2_commute: "R1(H2(P)) = H2(R1(P))"
  by (simp add: H2_split R1_def usubst, rel_auto)

subsection \<open> R2: No dependence upon trace history \<close>

text \<open> There are various ways of expressing $R2$, which are enumerated below. \<close>

definition R2a :: "('t::fzero_weak_trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" where
[upred_defs]: "R2a (P) = (\<Sqinter> s \<bullet> P\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s\<guillemotright>+($tr\<acute>-$tr)/$tr,$tr\<acute>\<rbrakk> \<and> (fzero $tr) =\<^sub>u (fzero \<guillemotleft>s\<guillemotright>) \<and> \<guillemotleft>s\<guillemotright> \<bar>\<^sub>u ($tr\<acute>-$tr))"

definition R2a' :: "('t::fzero_weak_trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" where
[upred_defs]: "R2a' P = (R2a(P) \<triangleleft> R1(true) \<triangleright> P)"

definition R2s :: "('t::fzero_weak_trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" where
[upred_defs]: "R2s (P) = (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>($tr\<acute>-$tr)/$tr\<acute>\<rbrakk>)"

definition R2 :: "('t::fzero_weak_trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
[upred_defs]: "R2(P) = R1(R2s(P))"

definition R2c :: "('t::fzero_weak_trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
[upred_defs]: "R2c(P) = (R2s(P) \<triangleleft> R1(true) \<triangleright> P)"

text \<open> @{term R2a} and @{term R2s} are the standard definitions from the UTP book~\cite{Hoare&98}.
  An issue with these forms is that their definition depends upon @{term R1} also being 
  satisfied~\cite{Foster17b}, since otherwise the trace minus operator is not well defined. 
  We overcome this with our own version, @{term R2c}, which applies @{term R2s} if @{term R1} holds,
  and otherwise has no effect. This latter healthiness condition can therefore be reasoned about
  independently of @{term R1}, which is useful in some circumstances. \<close>

lemma fzero_unrest [unrest]:
  assumes "y \<sharp> x"
  shows "y \<sharp> (fzero x)"
  using assms
  by pred_auto
  
lemma unrest_ok_R2s [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R2s(P)"
  by (simp add: R2s_def unrest)

lemma unrest_ok'_R2s [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R2s(P)"
  by (simp add: R2s_def unrest)

lemma unrest_ok_R2c [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma unrest_ok'_R2c [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma R2s_unrest [unrest]: "\<lbrakk> vwb_lens x; x \<bowtie> in_var tr; x \<bowtie> out_var tr; x \<sharp> P \<rbrakk> \<Longrightarrow> x \<sharp> R2s(P)"
  by (simp add: R2s_def unrest usubst lens_indep_sym)

lemma R2s_subst_wait_true [usubst]:
  "(R2s(P))\<lbrakk>true/$wait\<rbrakk> = R2s(P\<lbrakk>true/$wait\<rbrakk>)"
  by (simp add: R2s_def usubst unrest)

lemma R2s_subst_wait'_true [usubst]:
  "(R2s(P))\<lbrakk>true/$wait\<acute>\<rbrakk> = R2s(P\<lbrakk>true/$wait\<acute>\<rbrakk>)"
  by (simp add: R2s_def usubst unrest)

lemma R2_subst_wait_true [usubst]:
  "(R2(P))\<lbrakk>true/$wait\<rbrakk> = R2(P\<lbrakk>true/$wait\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2_subst_wait'_true [usubst]:
  "(R2(P))\<lbrakk>true/$wait\<acute>\<rbrakk> = R2(P\<lbrakk>true/$wait\<acute>\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2_subst_wait_false [usubst]:
  "(R2(P))\<lbrakk>false/$wait\<rbrakk> = R2(P\<lbrakk>false/$wait\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2_subst_wait'_false [usubst]:
  "(R2(P))\<lbrakk>false/$wait\<acute>\<rbrakk> = R2(P\<lbrakk>false/$wait\<acute>\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2c_R2s_absorb: "R2c(R2s(P)) = R2s(P)"
  by rel_auto
  
lemma R2a_R2s: "R2a(R2s(P)) = R2s(P)"
  apply rel_auto
  by (metis disjoint_rel_zero(1) fzero_weak_left_cancel_minus_ord_class.add_diff_cancel_left fzero_weak_left_cancel_minus_ord_class.le_iff_add fzero_weak_left_cancel_minus_ord_class.not_le_minus)
  
lemma R2s_R2a: "R2s(R2a(P)) = R2a(P)"
  by rel_auto
  
lemma R2a_equiv_R2s: "P is R2a \<longleftrightarrow> P is R2s"
  by (metis Healthy_def' R2a_R2s R2s_R2a)

lemma R2a_idem: "R2a(R2a(P)) = R2a(P)"
  apply pred_auto
  by force

lemma R2a'_idem: "R2a'(R2a'(P)) = R2a'(P)"
  apply rel_auto
  by force

lemma R2a_mono: "P \<sqsubseteq> Q \<Longrightarrow> R2a(P) \<sqsubseteq> R2a(Q)"
  by (rel_blast)

lemma R2a'_mono: "P \<sqsubseteq> Q \<Longrightarrow> R2a'(P) \<sqsubseteq> R2a'(Q)"
  by (rel_blast)

lemma R2a'_weakening: "R2a'(P) \<sqsubseteq> P"
  apply (rel_simp)
  apply (rename_tac ok wait tr more ok' wait' tr' more')
  apply (rule_tac x="tr" in exI)
  apply (simp add: diff_add_cancel_left' fzero_uexpr_def uop_ueval var.rep_eq)
  using fzero_weak_left_cancel_minus_ord_class.le_iff_add by force

lemma fzero_fzero_tr: "fzero (fzero $tr) = fzero $tr"
  by (pred_auto)
    
lemma fzero_fzero_tr_subst:
  "(fzero $tr)\<lbrakk>(fzero $tr)/$tr\<rbrakk> = fzero $tr"
  by pred_simp
  
lemma fzero_subst:
  "(fzero $tr)\<lbrakk>e/$tr\<rbrakk> = fzero e"
  by pred_simp
  
lemma R2s_idem: "R2s(R2s(P)) = R2s(P)"
  by pred_auto
  
lemma R2_idem: "R2(R2(P)) = R2(P)"
  apply (pred_auto)
  using fzero_weak_left_cancel_minus_ord_class.not_le_minus by fastforce

lemma R2_mono: "P \<sqsubseteq> Q \<Longrightarrow> R2(P) \<sqsubseteq> R2(Q)"
  by (pred_auto)

lemma R2_implies_R1 [closure]: "P is R2 \<Longrightarrow> P is R1"
  by (rel_blast)
    
lemma R2c_Continuous: "Continuous R2c"
  by (rel_simp)

lemma R2c_lit: "R2c(\<guillemotleft>x\<guillemotright>) = \<guillemotleft>x\<guillemotright>"
  by (rel_auto)

lemma tr_strict_prefix_R2c_closed [closure]: "$tr <\<^sub>u $tr\<acute> is R2c"
  apply rel_auto
   apply (simp add: fzero_uexpr_def fzero_weak_left_cancel_minus_ord_class.zero_le_minus_imp_le uop_ueval var.rep_eq)
  by (simp add: fzero_uexpr_def le_imp_zero_le_minus uop_ueval var.rep_eq)

lemma R2s_conj: "R2s(P \<and> Q) = (R2s(P) \<and> R2s(Q))"
  by (pred_auto)

lemma R2_conj: "R2(P \<and> Q) = (R2(P) \<and> R2(Q))"
  by (pred_auto)

lemma R2s_disj: "R2s(P \<or> Q) = (R2s(P) \<or> R2s(Q))"
  by pred_auto

lemma R2s_USUP:
  "R2s(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> R2s(P(i)))"
  by (simp add: R2s_def usubst)

lemma R2c_USUP:
  "R2c(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> R2c(P(i)))"
  by (rel_auto)

lemma R2s_UINF:
  "R2s(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> R2s(P(i)))"
  by (simp add: R2s_def usubst)

lemma R2c_UINF:
  "R2c(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> R2c(P(i)))"
  by (rel_auto)

lemma R2_disj: "R2(P \<or> Q) = (R2(P) \<or> R2(Q))"
  by (pred_auto)

lemma R2s_not: "R2s(\<not> P) = (\<not> R2s(P))"
  by pred_auto

lemma R2s_condr: "R2s(P \<triangleleft> b \<triangleright> Q) = (R2s(P) \<triangleleft> R2s(b) \<triangleright> R2s(Q))"
  by (rel_auto)

lemma R2_condr: "R2(P \<triangleleft> b \<triangleright> Q) = (R2(P) \<triangleleft> R2(b) \<triangleright> R2(Q))"
  unfolding R2_def R2s_def
  apply subst_tac
  by (rel_auto)

lemma R2_condr': "R2(P \<triangleleft> b \<triangleright> Q) = (R2(P) \<triangleleft> R2s(b) \<triangleright> R2(Q))"
  by (rel_auto)

lemma R2s_ok: "R2s($ok) = $ok"
  by (rel_auto)

lemma R2s_ok': "R2s($ok\<acute>) = $ok\<acute>"
  by (rel_auto)

lemma R2s_wait: "R2s($wait) = $wait"
  by (rel_auto)

lemma R2s_wait': "R2s($wait\<acute>) = $wait\<acute>"
  by (rel_auto)

lemma R2s_true: "R2s(true) = true"
  by pred_auto

lemma R2s_false: "R2s(false) = false"
  by pred_auto

lemma true_is_R2s:
  "true is R2s"
  by (simp add: Healthy_def R2s_true)

lemma R2s_lift_rea: "R2s(\<lceil>P\<rceil>\<^sub>R) = \<lceil>P\<rceil>\<^sub>R"
  by (simp add: R2s_def usubst unrest)

lemma R2c_lift_rea: "R2c(\<lceil>P\<rceil>\<^sub>R) = \<lceil>P\<rceil>\<^sub>R"
  by (simp add: R2c_def R2s_lift_rea cond_idem usubst unrest)

lemma R2c_true: "R2c(true) = true"
  by (rel_auto)

lemma R2c_false: "R2c(false) = false"
  by (rel_auto)

lemma R2c_and: "R2c(P \<and> Q) = (R2c(P) \<and> R2c(Q))"
  by (rel_auto)

lemma conj_R2c_closed [closure]: "\<lbrakk> P is R2c; Q is R2c \<rbrakk> \<Longrightarrow> (P \<and> Q) is R2c"
  by (simp add: Healthy_def R2c_and)

lemma R2c_disj: "R2c(P \<or> Q) = (R2c(P) \<or> R2c(Q))"
  by (rel_auto)

lemma R2c_inf: "R2c(P \<sqinter> Q) = (R2c(P) \<sqinter> R2c(Q))"
  by (rel_auto)

lemma R2c_not: "R2c(\<not> P) = (\<not> R2c(P))"
  by (rel_auto)

lemma R2c_ok: "R2c($ok) = ($ok)"
  by (rel_auto)

lemma R2c_ok': "R2c($ok\<acute>) = ($ok\<acute>)"
  by (rel_auto)

lemma R2c_wait: "R2c($wait) = $wait"
  by (rel_auto)

lemma R2c_wait': "R2c($wait\<acute>) = $wait\<acute>"
  by (rel_auto)

lemma R2c_wait'_true [usubst]: "(R2c P)\<lbrakk>true/$wait\<acute>\<rbrakk> = R2c(P\<lbrakk>true/$wait\<acute>\<rbrakk>)"
  by rel_auto
  
lemma R2c_wait'_false [usubst]: "(R2c P)\<lbrakk>false/$wait\<acute>\<rbrakk> = R2c(P\<lbrakk>false/$wait\<acute>\<rbrakk>)"
  by (rel_auto)
  
lemma R2c_tr'_minus_tr: "R2c($tr\<acute> =\<^sub>u $tr) = ($tr\<acute> =\<^sub>u $tr)"
  apply (rel_auto) using minus_zero_eq 
  by (simp add: fzero_weak_left_cancel_minus_ord_class.minus_zero_eq comp_def fzero_uexpr_def uop_ueval var.rep_eq)+
  

lemma R2c_tr'_ge_tr: "R2c($tr\<acute> \<ge>\<^sub>u $tr) = ($tr\<acute> \<ge>\<^sub>u $tr)"
  apply (rel_simp)
  by (metis (no_types, lifting) comp_apply des_vars.select_convs(2) fst_conv fzero_idem fzero_uexpr_def fzero_weak_left_cancel_minus_ord_class.not_le_minus lens.simps(1) minus_minus_fzero order_refl rp_vars.select_convs(2) uop.rep_eq var.rep_eq)

lemma R2c_tr_less_tr': "R2c($tr <\<^sub>u $tr\<acute>) = ($tr <\<^sub>u $tr\<acute>)"
  apply (rel_simp)
  using le_iff_zero_leq_minus by blast

lemma R2c_condr: "R2c(P \<triangleleft> b \<triangleright> Q) = (R2c(P) \<triangleleft> R2c(b) \<triangleright> R2c(Q))"
  by (rel_auto)

lemma R2c_shAll: "R2c (\<^bold>\<forall> x \<bullet> P x) = (\<^bold>\<forall> x \<bullet> R2c(P x))"
  by (rel_auto)

lemma R2c_impl: "R2c(P \<Rightarrow> Q) = (R2c(P) \<Rightarrow> R2c(Q))"
  by (metis (no_types, lifting) R2c_and R2c_not double_negation impl_alt_def not_conj_deMorgans)

lemma R2c_skip_r: "R2c(II) = II"
proof -
  have "R2c(II) = R2c($tr\<acute> =\<^sub>u $tr \<and> II\<restriction>\<^sub>\<alpha>tr)"
    by (subst skip_r_unfold[of tr], simp_all)
  also have "... = (R2c($tr\<acute> =\<^sub>u $tr) \<and> II\<restriction>\<^sub>\<alpha>tr)"
    by (simp add: R2c_and, simp add: R2c_def R2s_def usubst unrest cond_idem)
  also have "... = ($tr\<acute> =\<^sub>u $tr \<and> II\<restriction>\<^sub>\<alpha>tr)"
    by (simp add: R2c_tr'_minus_tr)
  finally show ?thesis
    by (subst skip_r_unfold[of tr], simp_all)
qed

lemma R1_R2c_commute: "R1(R2c(P)) = R2c(R1(P))"
  apply rel_auto
  by (metis (no_types, lifting) comp_apply des_vars.select_convs(2) fst_conv fzero_idem fzero_uexpr_def fzero_weak_left_cancel_minus_ord_class.not_le_minus lens.simps(1) minus_minus_fzero order_refl rp_vars.select_convs(2) uop.rep_eq var.rep_eq)
  
lemma R1_R2c_is_R2: "R1(R2c(P)) = R2(P)"
  by (rel_auto)

lemma R1_R2s_R2c: "R1(R2s(P)) = R1(R2c(P))"
  by (rel_auto)

lemma R1_R2s_tr_wait:
  "R1 (R2s ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)) = ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)"
  apply rel_auto using minus_zero_eq
  by (simp add: fzero_weak_left_cancel_minus_ord_class.minus_zero_eq fzero_uexpr_def uop.rep_eq var.rep_eq)+

lemma R1_R2s_tr'_eq_tr:
  "R1 (R2s ($tr\<acute> =\<^sub>u $tr)) = ($tr\<acute> =\<^sub>u $tr)"
  apply (rel_auto) using minus_zero_eq
  by (simp add: fzero_weak_left_cancel_minus_ord_class.minus_zero_eq fzero_uexpr_def uop.rep_eq var.rep_eq)+

(* TODO: 
lemma R1_R2s_tr'_extend_tr:
  "\<lbrakk> $tr \<sharp> v; $tr\<acute> \<sharp> v \<rbrakk> \<Longrightarrow> R1 (R2s ($tr\<acute> =\<^sub>u $tr ^\<^sub>u v)) = ($tr\<acute> =\<^sub>u $tr  ^\<^sub>u v)"
  apply (rel_auto)
   apply (metis append_minus)
  apply (simp add: Prefix_Order.prefixI)
  done *)

lemma R2_tr_prefix: "R2($tr \<le>\<^sub>u $tr\<acute>) = ($tr \<le>\<^sub>u $tr\<acute>)"
  apply (rel_simp)
  by (metis (no_types, lifting) comp_apply des_vars.select_convs(2) fst_conv fzero_idem fzero_uexpr_def fzero_weak_left_cancel_minus_ord_class.not_le_minus lens.simps(1) minus_minus_fzero order_refl rp_vars.select_convs(2) uop.rep_eq var.rep_eq)
  
lemma R2_form:
  "R2(P) = (\<^bold>\<exists> tt\<^sub>0 \<bullet> P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>)"
  apply rel_auto
  using fzero_weak_left_cancel_minus_ord_class.le_iff_add by force

lemma R2_subst_tr: 
  assumes "P is R2" "`tr\<^sub>0 \<bar>\<^sub>u t`"
  shows "[$tr \<mapsto>\<^sub>s tr\<^sub>0, $tr\<acute> \<mapsto>\<^sub>s tr\<^sub>0 + t] \<dagger> P = [$tr \<mapsto>\<^sub>s fzero tr\<^sub>0, $tr\<acute> \<mapsto>\<^sub>s t] \<dagger> P"
proof -
  have "[$tr \<mapsto>\<^sub>s tr\<^sub>0, $tr\<acute> \<mapsto>\<^sub>s tr\<^sub>0 + t] \<dagger> R2 P = [$tr \<mapsto>\<^sub>s fzero tr\<^sub>0, $tr\<acute> \<mapsto>\<^sub>s t] \<dagger> R2 P"
    unfolding R2_def R1_def R2s_def
    apply subst_tac
    apply rel_simp
  thus ?thesis
    by (simp add: Healthy_if assms)
qed
  oops

lemma R2_seqr_form:
  shows "(R2(P) ;; R2(Q)) =
         (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
                        \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> ($tr + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
proof -
  have "(R2(P) ;; R2(Q)) = (\<^bold>\<exists> tr\<^sub>0 \<bullet> (R2(P))\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; (R2(Q))\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>)"
    by (subst seqr_middle[of tr], simp_all)
  also have "... = (\<^bold>\<exists> tr\<^sub>0 \<bullet> ((\<^bold>\<exists> tt\<^sub>1 \<bullet> P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk>) ;; 
                            ((\<^bold>\<exists> tt\<^sub>2 \<bullet> Q\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>)) "
    by (simp add: R2_form)
  also have "... = (\<^bold>\<exists> tr\<^sub>0 \<bullet> ((\<^bold>\<exists> tt\<^sub>1 \<bullet> P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>)) ;; 
                            (\<^bold>\<exists> tt\<^sub>2 \<bullet> Q\<lbrakk>(fzero($tr)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>))"
    by (rel_auto)
  also have "... = (\<^bold>\<exists> tr\<^sub>0 \<bullet> ((\<^bold>\<exists> tt\<^sub>1 \<bullet> P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>)) ;; 
                            (\<^bold>\<exists> tt\<^sub>2 \<bullet> Q\<lbrakk>fzero(\<guillemotleft>tr\<^sub>0\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>))"
    by (simp add:fzero_subst)
  also have "... = (\<^bold>\<exists> tr\<^sub>0 \<bullet> ((\<^bold>\<exists> tt\<^sub>1 \<bullet> P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>)) ;; 
                            (\<^bold>\<exists> tt\<^sub>2 \<bullet> Q\<lbrakk>fzero(\<guillemotleft>tr\<^sub>0\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> ($tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)))"
    by rel_auto
  also have "... =
       (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>) ;;
                                (Q\<lbrakk>fzero(\<guillemotleft>tr\<^sub>0\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)))"
    apply (simp add: R2_form usubst unrest uquant_lift)
    by pred_auto
  also have "... =
       (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((\<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>) ;;
                                (Q\<lbrakk>fzero(\<guillemotleft>tr\<^sub>0\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)))"
    by pred_auto
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tr\<^sub>0 \<bullet> ((P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>) ;; (Q\<lbrakk>fzero(\<guillemotleft>tr\<^sub>0\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
                                \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    by (rel_blast)
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tr\<^sub>0 \<bullet> ((P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>fzero(\<guillemotleft>tr\<^sub>0\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
                                \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>  \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    by rel_blast
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tr\<^sub>0 \<bullet> ((P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>fzero(\<guillemotleft>tr\<^sub>0\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
                                \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> fzero(\<guillemotleft>tr\<^sub>0\<guillemotright>) =\<^sub>u fzero($tr + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    apply (simp add:usubst unrest fzero_uexpr_def) (* TODO: Really need to incorporate fzero_uexpr_def in the tactic simp *)
    by (rel_auto)
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tr\<^sub>0 \<bullet> ((P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>fzero(\<guillemotleft>tr\<^sub>0\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
                                \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> fzero(\<guillemotleft>tr\<^sub>0\<guillemotright>) =\<^sub>u fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>) \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    apply (simp add:usubst unrest fzero_uexpr_def) (* TODO: Really need to incorporate fzero_uexpr_def in the tactic simp *)
    apply (rel_simp robust)
    using fzero_plus_right
    by blast
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tr\<^sub>0 \<bullet> ((P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
                                \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    apply (simp add:usubst unrest fzero_uexpr_def) (* TODO: Really need to incorporate fzero_uexpr_def in the tactic simp *)
    apply (rel_auto)
     apply blast
    using fzero_plus_right by fastforce
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
                        \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>))"
    by rel_simp
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
                        \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> ($tr + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    by pred_auto
  finally show ?thesis .
qed

lemma R2_seqr_form':
  assumes "P is R2" "Q is R2"
  shows "P ;; Q =
         (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>))
                        \<and> ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> ($tr + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>))"
  using R2_seqr_form[of P Q] by (simp add: Healthy_if assms)

lemma R2_seqr_form'':
  assumes "P is R2" "Q is R2"
  shows "P ;; Q =
         (\<^bold>\<exists> (tt\<^sub>1, tt\<^sub>2) \<bullet> ((P\<lbrakk>fzero($tr),\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr,$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>),\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr,$tr\<acute>\<rbrakk>))
                         \<and> ($tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> ($tr + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>))"
  by (subst R2_seqr_form', simp_all add: assms fzero_uexpr_def, rel_auto)

lemma R2_tr_middle:
  assumes "P is R2" "Q is R2"
  shows "(\<^bold>\<exists> tr\<^sub>0 \<bullet> (P\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>) \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>) = (P ;; Q)"
proof -
  have "(P ;; Q) = (\<^bold>\<exists> tr\<^sub>0 \<bullet> (P\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>))"
    by (simp add: seqr_middle)
  also have "... = (\<^bold>\<exists> tr\<^sub>0 \<bullet> ((R2 P)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; (R2 Q)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>))"
    by (simp add: assms Healthy_if)
  also have "... = (\<^bold>\<exists> tr\<^sub>0 \<bullet> ((R2 P)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; (R2 Q)\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>) \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>)"
    by (rel_auto)
  also have "... = (\<^bold>\<exists> tr\<^sub>0 \<bullet> (P\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>) \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>)"
    by (simp add: assms Healthy_if)
  finally show ?thesis ..
qed

lemma subst_prefix_rel: "($tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>)\<lbrakk>e/$tr\<rbrakk> = (e \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>)"
  by subst_tac

lemma R2_seqr_distribute:
  fixes P :: "('t::fzero_weak_trace,'\<alpha>,'\<beta>) rel_rp" and Q :: "('t,'\<beta>,'\<gamma>) rel_rp"
  shows "R2(R2(P) ;; R2(Q)) = (R2(P) ;; R2(Q))"
proof -
   have "R2(R2(P) ;; R2(Q)) =
    (R2s(\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> ($tr + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
     apply (simp add: R2_seqr_form) 
     by (simp add: R1_def R2_def)
   also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> ($tr + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>($tr\<acute> - $tr)/$tr\<acute>\<rbrakk> \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
     by (simp add:R2s_def)
   also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> =\<^sub>u fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> fzero($tr) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> (fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)\<lbrakk>($tr\<acute> - $tr)/$tr\<acute>\<rbrakk> \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
     apply (simp add:usubst unrest fzero_uexpr_def)
     by (rel_simp)
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)\<lbrakk>($tr\<acute> - $tr)/$tr\<acute>\<rbrakk>
      \<and> $tr\<acute> - $tr =\<^sub>u fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> fzero($tr) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> (fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
    by (simp add:usubst unrest)
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)\<lbrakk>(fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)/$tr\<acute>\<rbrakk>
      \<and> $tr\<acute> - $tr =\<^sub>u fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> fzero($tr) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> (fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
    by rel_simp
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> - $tr =\<^sub>u fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> fzero($tr) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> (fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
      by (rel_auto)
  also have "... =
    (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> ($tr\<acute> - $tr =\<^sub>u fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> fzero($tr) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> (fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr\<acute> \<ge>\<^sub>u $tr))"
    by pred_auto (* goal: ($tr + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) *)
  also have "... =
    (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> =\<^sub>u $tr + fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> fzero($tr) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> (fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u (fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
  proof -
    have "\<And> tt\<^sub>1 tt\<^sub>2. ((($tr\<acute> - $tr =\<^sub>u fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> fzero($tr) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> (fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr) :: ('t,'\<alpha>,'\<gamma>) rel_rp)
           = ($tr\<acute> =\<^sub>u $tr + fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> fzero($tr) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> (fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u (fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
      apply (rel_simp)
      apply (auto simp add:minus_prefix_disjoint)
         apply (metis add.assoc add_fzero_right fzero_weak_left_cancel_minus_ord_class.diff_add_cancel_left')
      using minus_prefix_disjoint apply blast
     apply (metis fzero_weak_left_cancel_minus_ord_class.add_diff_cancel_left fzero_weak_left_cancel_minus_ord_class.diff_zero fzero_weak_left_cancel_minus_ord_class.le_add fzero_weak_left_cancel_minus_ord_class.sum_minus_left plus_fzeros)
    by (simp add: add.assoc fzero_le_add)
    thus ?thesis by rel_auto
  qed
  also have "... =
    (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> fzero($tr) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> (fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u (fzero($tr) + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
  proof -
    have "$tr + fzero($tr) = $tr"
    apply (simp add:fzero_uexpr_def)
      by (rel_auto)
    thus ?thesis by auto
  qed
  also have "... =
    (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>fzero(\<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> ($tr + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    apply (simp add:fzero_uexpr_def)
    apply rel_simp    
    using plus_fzeros by blast
  (*also have "... =
    (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>fzero($tr + \<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> fzero($tr) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> (fzero($tr) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> \<guillemotleft>tt\<^sub>1\<guillemotright> \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    apply (simp add:fzero_uexpr_def)
    apply rel_auto
    using prefix_rel_dist prefix_rel_sym by blast+
  also have "... =
    (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>fzero($tr + \<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> (fzero($tr) + $tr) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> (fzero($tr) + $tr) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> \<guillemotleft>tt\<^sub>1\<guillemotright> \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    apply (simp add:fzero_uexpr_def)
    apply rel_auto
    using prefix_rel_dist prefix_rel_sym 
     apply blast
    using prefix_rel_dist by force
  also have "... =
    (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>fzero($tr + \<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> \<guillemotleft>tt\<^sub>1\<guillemotright> \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    apply (simp add:fzero_uexpr_def)
    by rel_auto
  also have "... =
    (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>fzero($tr)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>fzero($tr + \<guillemotleft>tt\<^sub>1\<guillemotright>)/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr \<bar>\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> ($tr + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<bar>\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    apply (simp add:fzero_uexpr_def)
    apply rel_auto
    using prefix_rel_dist prefix_rel_sym 
    by blast+*)
  also have "... = (R2(P) ;; R2(Q))"
    by (simp add: R2_seqr_form)
  finally show ?thesis .
qed

lemma R2_seqr_closure [closure]:
  assumes "P is R2" "Q is R2"
  shows "(P ;; Q) is R2"
  by (metis Healthy_def' R2_seqr_distribute assms(1) assms(2))

lemma false_R2 [closure]: "false is R2"
  by (rel_auto)
    
lemma R1_R2_commute:
  "R1(R2(P)) = R2(R1(P))"
  apply rel_auto
  by (metis comp_apply des_vars.select_convs(2) fst_conv fzero_idem fzero_weak_left_cancel_minus_ord_class.not_le_minus lens.simps(1) minus_minus_fzero order_refl rp_vars.select_convs(2) uop.rep_eq var.rep_eq)

lemma R2_R1_form: "R2(R1(P)) = R1(R2s(P))"
  apply rel_auto
  by (metis comp_apply des_vars.select_convs(2) fst_conv fzero_idem fzero_weak_left_cancel_minus_ord_class.not_le_minus lens.simps(1) minus_minus_fzero order_refl rp_vars.select_convs(2) uop.rep_eq var.rep_eq)
  
lemma R2s_H1_commute:
  "R2s(H1(P)) = H1(R2s(P))"
  by (rel_auto)

lemma R2s_H2_commute:
  "R2s(H2(P)) = H2(R2s(P))"
  by (simp add: H2_split R2s_def usubst fzero_uexpr_def)

(* TODO: sadly no longer holds but it isn't used anywhere else either 
lemma R2_R1_seq_drop_left:
  "R2(R1(P) ;; R1(Q)) = R2(P ;; R1(Q))"
  apply rel_auto
  apply (simp add:fzero_uexpr_def)
    sledgehammer[debug=true]
    nitpick
  by (rel_auto) *)

lemma R2c_idem: "R2c(R2c(P)) = R2c(P)"
  by rel_auto
  
lemma R2c_Idempotent [closure]: "Idempotent R2c"
  by (simp add: Idempotent_def R2c_idem)

lemma R2c_Monotonic [closure]: "Monotonic R2c"
  by (rel_auto)

lemma R2c_H2_commute: "R2c(H2(P)) = H2(R2c(P))"
  by (simp add: H2_split R2c_disj R2c_def R2s_def usubst fzero_uexpr_def, rel_auto)

lemma R2c_seq: "R2c(R2(P) ;; R2(Q)) = (R2(P) ;; R2(Q))"
  by (metis (no_types, lifting) R1_R2c_commute R1_R2c_is_R2 R2_seqr_distribute R2c_idem)

lemma R2_R2c_def: "R2(P) = R1(R2c(P))"
  by (rel_auto)

lemma R2_comp_def: "R2 = R1 \<circ> R2c"
  by (auto simp add: R2_R2c_def)
    
lemma R2c_R1_seq: "R2c(R1(R2c(P)) ;; R1(R2c(Q))) = (R1(R2c(P)) ;; R1(R2c(Q)))"
  using R2c_seq[of P Q] by (simp add: R2_R2c_def)

lemma R1_R2c_seqr_distribute:
  fixes P :: "('t::fzero_weak_trace,'\<alpha>,'\<beta>) rel_rp" and Q :: "('t,'\<beta>,'\<gamma>) rel_rp"
  assumes "P is R1" "P is R2c" "Q is R1" "Q is R2c"
  shows "R1(R2c(P ;; Q)) = P ;; Q"
  by (metis Healthy_if R1_seqr R2c_R1_seq assms)

lemma R2_R1_true:
  "R2(R1(true)) = R1(true)"
  by (simp add: R2_R1_form R2s_true)
    
lemma R1_true_R2 [closure]: "R1(true) is R2"
  apply (rel_auto)
  by (metis (no_types, lifting) comp_apply des_vars.select_convs(2) fst_conv fzero_idem fzero_uexpr_def fzero_weak_left_cancel_minus_ord_class.not_le_minus lens.simps(1) minus_minus_fzero order_refl rp_vars.select_convs(2) uop.rep_eq var.rep_eq)
  
(* TODO: fix this 
lemma R1_R2s_R1_true_lemma:
  "R1(R2s(R1 (\<not> R2s P) ;; R1 true)) = R1(R2s((\<not> P) ;; R1 true))"
  apply (rel_auto)
  apply (simp add:fzero_uexpr_def)
  apply (smt comp_apply comp_eq_dest_lhs des_vars.select_convs(2) fst_conv fzero_almost_trace_class.diff_cancel fzero_almost_trace_class.diff_zero fzero_uexpr_def fzero_uexpr_def lens.simps(1) rp_vars.select_convs(2) uop.rep_eq uop.rep_eq uop_ueval uop_ueval var.rep_eq)
  sledgehammer[debug=true]
  nitpick
  by (simp add: fzero_uexpr_def uop.rep_eq var.rep_eq)+*)

lemma R2c_healthy_R2s: "P is R2c \<Longrightarrow> R1(R2s(P)) = R1(P)"
  by (simp add: Healthy_def R1_R2s_R2c) 

subsection \<open> R3: No activity while predecessor is waiting \<close>

definition R3 :: "('t::fzero_weak_trace, '\<alpha>) hrel_rp \<Rightarrow> ('t, '\<alpha>) hrel_rp" where
[upred_defs]: "R3(P) = (II \<triangleleft> $wait \<triangleright> P)"

lemma R3_idem: "R3(R3(P)) = R3(P)"
  by (rel_auto)

lemma R3_Idempotent [closure]: "Idempotent R3"
  by (simp add: Idempotent_def R3_idem)

lemma R3_mono: "P \<sqsubseteq> Q \<Longrightarrow> R3(P) \<sqsubseteq> R3(Q)"
  by (rel_auto)

lemma R3_Monotonic: "Monotonic R3"
  by (simp add: mono_def R3_mono)

lemma R3_Continuous: "Continuous R3"
  by (rel_auto)

lemma R3_conj: "R3(P \<and> Q) = (R3(P) \<and> R3(Q))"
  by (rel_auto)

lemma R3_disj: "R3(P \<or> Q) = (R3(P) \<or> R3(Q))"
  by (rel_auto)

lemma R3_USUP:
  assumes "A \<noteq> {}"
  shows "R3(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> R3(P(i)))"
  using assms by (rel_auto)

lemma R3_UINF:
  assumes "A \<noteq> {}"
  shows "R3(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> R3(P(i)))"
  using assms by (rel_auto)

lemma R3_condr: "R3(P \<triangleleft> b \<triangleright> Q) = (R3(P) \<triangleleft> b \<triangleright> R3(Q))"
  by (rel_auto)

lemma R3_skipr: "R3(II) = II"
  by (rel_auto)

lemma R3_form: "R3(P) = (($wait \<and> II) \<or> (\<not> $wait \<and> P))"
  by (rel_auto)

lemma wait_R3:
  "($wait \<and> R3(P)) = (II \<and> $wait\<acute>)"
  by (rel_auto)

lemma nwait_R3:
  "(\<not>$wait \<and> R3(P)) = (\<not>$wait \<and> P)"
  by (rel_auto)

lemma R3_semir_form:
  "(R3(P) ;; R3(Q)) = R3(P ;; R3(Q))"
  by (rel_auto)

lemma R3_semir_closure:
  assumes "P is R3" "Q is R3"
  shows "(P ;; Q) is R3"
  using assms
  by (metis Healthy_def' R3_semir_form)

lemma R1_R3_commute: "R1(R3(P)) = R3(R1(P))"
  by (rel_auto)

lemma R2_R3_commute: "R2(R3(P)) = R3(R2(P))"
  apply (rel_auto)
  by (simp add: fzero_uexpr_def fzero_weak_left_cancel_minus_ord_class.minus_zero_eq uop.rep_eq var.rep_eq)+

subsection \<open> R4: The trace strictly increases \<close>

definition R4 :: "('t::fzero_weak_trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
[upred_defs]: "R4(P) = (P \<and> $tr <\<^sub>u $tr\<acute>)"

lemma R4_implies_R1 [closure]: "P is R4 \<Longrightarrow> P is R1"
  using less_iff by rel_blast

lemma R4_iff_refine:
  "P is R4 \<longleftrightarrow> ($tr <\<^sub>u $tr\<acute>) \<sqsubseteq> P"
  by (rel_blast)

lemma R4_idem: "R4 (R4 P) = R4 P"
  by (rel_auto)

lemma R4_false: "R4(false) = false"
  by (rel_auto)

lemma R4_conj: "R4(P \<and> Q) = (R4(P) \<and> R4(Q))"
  by (rel_auto)

lemma R4_disj: "R4(P \<or> Q) = (R4(P) \<or> R4(Q))"
  by (rel_auto)

lemma R4_is_R4 [closure]: "R4(P) is R4"
  by (rel_auto)

lemma false_R4 [closure]: "false is R4"
  by (rel_auto)

lemma UINF_R4_closed [closure]: 
  "\<lbrakk> \<And> i. P i is R4 \<rbrakk> \<Longrightarrow> (\<Sqinter> i \<bullet> P i) is R4"
  by (rel_blast)

lemma conj_R4_closed [closure]:
  "\<lbrakk> P is R4; Q is R4 \<rbrakk> \<Longrightarrow> (P \<and> Q) is R4"
  by (simp add: Healthy_def R4_conj)

lemma disj_R4_closed [closure]:
  "\<lbrakk> P is R4; Q is R4 \<rbrakk> \<Longrightarrow> (P \<or> Q) is R4"
  by (simp add: Healthy_def R4_disj)

lemma seq_R4_closed_1 [closure]:
  "\<lbrakk> P is R4; Q is R1 \<rbrakk> \<Longrightarrow> (P ;; Q) is R4"
  using less_le_trans by rel_blast

lemma seq_R4_closed_2 [closure]:
  "\<lbrakk> P is R1; Q is R4 \<rbrakk> \<Longrightarrow> (P ;; Q) is R4"
  using le_less_trans by rel_blast

subsection \<open> R5: The trace does not increase \<close>

definition R5 :: "('t::fzero_weak_trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp" where
[upred_defs]: "R5(P) = (P \<and> $tr =\<^sub>u $tr\<acute>)"

lemma R5_implies_R1 [closure]: "P is R5 \<Longrightarrow> P is R1"
  using eq_iff 
  apply rel_auto using eq_refl by smt

lemma R5_iff_refine:
  "P is R5 \<longleftrightarrow> ($tr =\<^sub>u $tr\<acute>) \<sqsubseteq> P"
  by (rel_blast)

lemma R5_conj: "R5(P \<and> Q) = (R5(P) \<and> R5(Q))"
  by (rel_auto)

lemma R5_disj: "R5(P \<or> Q) = (R5(P) \<or> R5(Q))"
  by (rel_auto)

lemma R4_R5: "R4 (R5 P) = false"
  by (rel_auto)

lemma R5_R4: "R5 (R4 P) = false"
  by (rel_auto)

lemma UINF_R5_closed [closure]: 
  "\<lbrakk> \<And> i. P i is R5 \<rbrakk> \<Longrightarrow> (\<Sqinter> i \<bullet> P i) is R5"
  by (rel_blast)

lemma conj_R5_closed [closure]:
  "\<lbrakk> P is R5; Q is R5 \<rbrakk> \<Longrightarrow> (P \<and> Q) is R5"
  by (simp add: Healthy_def R5_conj)

lemma disj_R5_closed [closure]:
  "\<lbrakk> P is R5; Q is R5 \<rbrakk> \<Longrightarrow> (P \<or> Q) is R5"
  by (simp add: Healthy_def R5_disj)

lemma seq_R5_closed [closure]:
  "\<lbrakk> P is R5; Q is R5 \<rbrakk> \<Longrightarrow> (P ;; Q) is R5"
  by (rel_auto, metis)

subsection {* RP laws *}

definition RP_def [upred_defs]: "RP(P) = R1(R2c(R3(P)))"

lemma RP_comp_def: "RP = R1 \<circ> R2c \<circ> R3"
  by (auto simp add: RP_def)

lemma RP_alt_def: "RP(P) = R1(R2(R3(P)))"
  by (metis R1_R2c_is_R2 R1_idem RP_def)

lemma RP_intro: "\<lbrakk> P is R1; P is R2; P is R3 \<rbrakk> \<Longrightarrow> P is RP"
  by (simp add: Healthy_def' RP_alt_def)

lemma RP_idem: "RP(RP(P)) = RP(P)"
  by (simp add: R1_R2c_is_R2 R2_R3_commute R2_idem R3_idem RP_def)

lemma RP_Idempotent [closure]: "Idempotent RP"
  by (simp add: Idempotent_def RP_idem)

lemma RP_mono: "P \<sqsubseteq> Q \<Longrightarrow> RP(P) \<sqsubseteq> RP(Q)"
  by (simp add: R1_R2c_is_R2 R2_mono R3_mono RP_def)

lemma RP_Monotonic: "Monotonic RP"
  by (simp add: mono_def RP_mono)

lemma RP_Continuous: "Continuous RP"
  by (simp add: Continuous_comp R1_Continuous R2c_Continuous R3_Continuous RP_comp_def)

lemma RP_skip:
  "RP(II) = II"
  by (simp add: R1_skip R2c_skip_r R3_skipr RP_def)

lemma RP_skip_closure:
  "II is RP"
  by (simp add: Healthy_def' RP_skip)

lemma RP_seq_closure:
  assumes "P is RP" "Q is RP"
  shows "(P ;; Q) is RP"
proof (rule RP_intro)
  show "(P ;; Q) is R1"
    by (metis Healthy_def R1_seqr RP_def assms)
  thus "(P ;; Q) is R2"
    by (metis Healthy_def' R2_R2c_def R2c_R1_seq RP_def  assms)
  show "(P ;; Q) is R3"
    by (metis (no_types, lifting) Healthy_def' R1_R2c_is_R2 R2_R3_commute R3_idem R3_semir_form RP_def assms)
qed

subsection \<open> UTP theories \<close>

typedecl REA
abbreviation "REA \<equiv> UTHY(REA, ('t::fzero_weak_trace,'\<alpha>) rp)"

overloading
  rea_hcond == "utp_hcond :: (REA, ('t::fzero_weak_trace,'\<alpha>) rp) uthy \<Rightarrow> (('t,'\<alpha>) rp \<times> ('t,'\<alpha>) rp) health"
  rea_unit == "utp_unit :: (REA, ('t::fzero_weak_trace,'\<alpha>) rp) uthy \<Rightarrow> ('t,'\<alpha>) hrel_rp"
begin
  definition rea_hcond :: "(REA, ('t::fzero_weak_trace,'\<alpha>) rp) uthy \<Rightarrow> (('t,'\<alpha>) rp \<times> ('t,'\<alpha>) rp) health"
  where [upred_defs]: "rea_hcond T = RP"
  definition rea_unit :: "(REA, ('t::fzero_weak_trace,'\<alpha>) rp) uthy \<Rightarrow> ('t,'\<alpha>) hrel_rp"
  where [upred_defs]: "rea_unit T = II"
end

interpretation rea_utp_theory: utp_theory "UTHY(REA, ('t::fzero_weak_trace,'\<alpha>) rp)"
  rewrites "carrier (uthy_order REA) = \<lbrakk>RP\<rbrakk>\<^sub>H"
  by (simp_all add: rea_hcond_def utp_theory_def RP_idem)

interpretation rea_utp_theory_mono: utp_theory_continuous "UTHY(REA, ('t::fzero_weak_trace,'\<alpha>) rp)"
  rewrites "carrier (uthy_order REA) = \<lbrakk>RP\<rbrakk>\<^sub>H"
  by (unfold_locales, simp_all add: RP_Continuous rea_hcond_def)

interpretation rea_utp_theory_rel: utp_theory_unital "UTHY(REA, ('t::fzero_weak_trace,'\<alpha>) rp)"
  rewrites "carrier (uthy_order REA) = \<lbrakk>RP\<rbrakk>\<^sub>H"
  by (unfold_locales, simp_all add: rea_hcond_def rea_unit_def RP_seq_closure RP_skip_closure)

lemma rea_top: "\<^bold>\<top>\<^bsub>REA\<^esub> = ($wait \<and> II)"
proof -
  have "\<^bold>\<top>\<^bsub>REA\<^esub> = RP(false)"
    by (simp add: rea_utp_theory_mono.healthy_top, simp add: rea_hcond_def)
  also have "... = ($wait \<and> II)"
    apply rel_auto
    by (simp add: fzero_uexpr_def fzero_weak_left_cancel_minus_ord_class.minus_zero_eq uop.rep_eq var.rep_eq)+
  finally show ?thesis .
qed

lemma rea_top_left_zero:
  assumes "P is RP"
  shows "(\<^bold>\<top>\<^bsub>REA\<^esub> ;; P) = \<^bold>\<top>\<^bsub>REA\<^esub>"
proof -
  have "(\<^bold>\<top>\<^bsub>REA\<^esub> ;; P) = (($wait \<and> II) ;; R3(P))"
    by (metis (no_types, lifting) Healthy_def R1_R2c_is_R2 R2_R3_commute R3_idem RP_def assms rea_top)
  also have "... = ($wait \<and> R3(P))"
    by (rel_auto)
  also have "... = ($wait \<and> II)"
    by (metis R3_skipr wait_R3)
  also have "... = \<^bold>\<top>\<^bsub>REA\<^esub>"
    by (simp add: rea_top)
  finally show ?thesis .
qed

lemma rea_bottom: "\<^bold>\<bottom>\<^bsub>REA\<^esub> = R1($wait \<Rightarrow> II)"
proof -
  have "\<^bold>\<bottom>\<^bsub>REA\<^esub> = RP(true)"
    by (simp add: rea_utp_theory_mono.healthy_bottom, simp add: rea_hcond_def)
  also have "... = R1($wait \<Rightarrow> II)"
    apply rel_auto
    by (simp add: fzero_uexpr_def fzero_weak_left_cancel_minus_ord_class.minus_zero_eq uop.rep_eq var.rep_eq)+
  finally show ?thesis .
qed

end