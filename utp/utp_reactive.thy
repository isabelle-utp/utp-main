section {* Reactive processes *}

theory utp_reactive
imports 
  utp_concurrency 
  utp_event
begin

subsection {* Preliminaries *}

type_synonym '\<alpha> trace = "'\<alpha> list"

fun list_diff::"'\<alpha> list \<Rightarrow> '\<alpha> list \<Rightarrow> '\<alpha> list option" where
   "list_diff l [] = Some l"
  | "list_diff [] l = None"
  | "list_diff (x#xs) (y#ys) = (if (x = y) then (list_diff xs ys) else None)"

lemma list_diff_empty [simp]: "the (list_diff l []) = l"
by (cases l) auto

lemma prefix_subst [simp]: "l @ t = m \<Longrightarrow> m - l = t"
by (auto)

lemma prefix_subst1 [simp]: "m = l @ t \<Longrightarrow> m - l = t"
by (auto)

text {* The definitions of reactive process alphabets and healthiness conditions are given
in the following. The healthiness conditions of reactive processes are defined by 
$R1$, $R2$, $R3$ and their composition $R$.*}

type_synonym '\<theta> refusal = "'\<theta> set"
  
record '\<theta> alpha_rp'  = rp_wait :: bool
                       rp_tr   :: "'\<theta> trace"
                       rp_ref  :: "'\<theta> refusal"

type_synonym ('\<theta>, '\<alpha>) alpha_rp_scheme = "('\<theta>, '\<alpha>) alpha_rp'_scheme alpha_d_scheme"

type_synonym ('\<theta>,'\<alpha>) alphabet_rp  = "('\<theta>,'\<alpha>) alpha_rp_scheme alphabet"
type_synonym ('\<theta>,'\<alpha>,'\<beta>) relation_rp  = "(('\<theta>,'\<alpha>) alphabet_rp, ('\<theta>,'\<beta>) alphabet_rp) relation"
type_synonym ('\<theta>,'\<alpha>) hrelation_rp  = "(('\<theta>,'\<alpha>) alphabet_rp, ('\<theta>,'\<alpha>) alphabet_rp) relation"
type_synonym ('\<theta>,'\<sigma>) predicate_rp  = "('\<theta>,'\<sigma>) alphabet_rp upred"

definition "wait\<^sub>r = VAR rp_wait"
definition "tr\<^sub>r   = VAR rp_tr"
definition "ref\<^sub>r  = VAR rp_ref"
definition [upred_defs]: "\<Sigma>\<^sub>r    = VAR more"

declare wait\<^sub>r_def [upred_defs]
declare tr\<^sub>r_def [upred_defs]
declare ref\<^sub>r_def [upred_defs]
declare \<Sigma>\<^sub>r_def [upred_defs]

lemma wait\<^sub>r_uvar [simp]: "uvar wait\<^sub>r"
  by (unfold_locales, simp_all add: wait\<^sub>r_def)

lemma tr\<^sub>r_uvar [simp]: "uvar tr\<^sub>r"
  by (unfold_locales, simp_all add: tr\<^sub>r_def)

lemma ref\<^sub>r_uvar [simp]: "uvar ref\<^sub>r"
  by (unfold_locales, simp_all add: ref\<^sub>r_def)

lemma rea_lens_uvar [simp]: "uvar \<Sigma>\<^sub>r"
  by (unfold_locales, simp_all add: \<Sigma>\<^sub>r_def)
  
definition "wait = (wait\<^sub>r ;\<^sub>L \<Sigma>\<^sub>D)"
definition "tr   = (tr\<^sub>r ;\<^sub>L \<Sigma>\<^sub>D)"
definition "ref  = (ref\<^sub>r ;\<^sub>L \<Sigma>\<^sub>D)"
definition [upred_defs]: "\<Sigma>\<^sub>R   = (\<Sigma>\<^sub>r ;\<^sub>L \<Sigma>\<^sub>D)"

lemma wait_uvar [simp]: "uvar wait"
  by (simp add: comp_vwb_lens wait_def)

lemma tr_uvar [simp]: "uvar tr"
  by (simp add: comp_vwb_lens tr_def)

lemma ref_uvar [simp]: "uvar ref"
  by (simp add: comp_vwb_lens ref_def)

lemma rea_lens_under_des_lens: "\<Sigma>\<^sub>R \<subseteq>\<^sub>L \<Sigma>\<^sub>D"
  by (simp add: \<Sigma>\<^sub>R_def lens_comp_lb)

declare wait_def [upred_defs]
declare tr_def [upred_defs]
declare ref_def [upred_defs]

lemma tr_ok_indep [simp]: "tr \<bowtie> ok" "ok \<bowtie> tr"
  by (simp_all add: lens_indep_left_ext lens_indep_sym tr_def)

lemma wait_ok_indep [simp]: "wait \<bowtie> ok" "ok \<bowtie> wait"
  by (simp_all add: lens_indep_left_ext lens_indep_sym wait_def)

lemma ref_ok_indep [simp]: "ref \<bowtie> ok" "ok \<bowtie> ref"
  by (simp_all add: lens_indep_left_ext lens_indep_sym ref_def)

lemma tr\<^sub>r_wait\<^sub>r_indep [simp]: "tr\<^sub>r \<bowtie> wait\<^sub>r" "wait\<^sub>r \<bowtie> tr\<^sub>r"
  by (auto intro!:lens_indepI simp add: tr\<^sub>r_def wait\<^sub>r_def)  
  
lemma tr_wait_indep [simp]: "tr \<bowtie> wait" "wait \<bowtie> tr"
  by (auto intro: lens_indep_left_comp simp add: tr_def wait_def)

lemma ref\<^sub>r_wait\<^sub>r_indep [simp]: "ref\<^sub>r \<bowtie> wait\<^sub>r" "wait\<^sub>r \<bowtie> ref\<^sub>r"
  by (auto intro!:lens_indepI simp add: ref\<^sub>r_def wait\<^sub>r_def)

lemma ref_wait_indep [simp]: "ref \<bowtie> wait" "wait \<bowtie> ref"
  by (auto intro: lens_indep_left_comp simp add: ref_def wait_def)

lemma tr\<^sub>r_ref\<^sub>r_indep [simp]: "ref\<^sub>r \<bowtie> tr\<^sub>r" "tr\<^sub>r \<bowtie> ref\<^sub>r"
  by (auto intro!:lens_indepI simp add: ref\<^sub>r_def tr\<^sub>r_def)

lemma tr_ref_indep [simp]: "ref \<bowtie> tr" "tr \<bowtie> ref"
  by (auto intro: lens_indep_left_comp simp add: ref_def tr_def)

instantiation alpha_rp'_ext :: (type, vst) vst
begin
  definition vstore_lens_alpha_rp'_ext :: "vstore \<Longrightarrow> ('a, 'b) alpha_rp'_scheme"
  where "vstore_lens_alpha_rp'_ext = \<V> ;\<^sub>L \<Sigma>\<^sub>r"
instance
  by (intro_classes, simp add: vstore_lens_alpha_rp'_ext_def comp_vwb_lens)
end

abbreviation wait_f::"('\<theta>, '\<alpha>, '\<beta>) relation_rp \<Rightarrow> ('\<theta>, '\<alpha>, '\<beta>) relation_rp" ("_\<^sub>f" [1000] 1000)
where "wait_f R \<equiv> R\<lbrakk>false/$wait\<rbrakk>"

abbreviation wait_t::"('\<theta>, '\<alpha>, '\<beta>) relation_rp \<Rightarrow> ('\<theta>, '\<alpha>, '\<beta>) relation_rp" ("_\<^sub>t" [1000] 1000)
where "wait_t R \<equiv> R\<lbrakk>true/$wait\<rbrakk>"

definition lift_rea :: "('\<alpha>, '\<beta>) relation \<Rightarrow> ('\<theta>, '\<alpha>, '\<beta>) relation_rp" ("\<lceil>_\<rceil>\<^sub>R") where
[upred_defs]: "\<lceil>P\<rceil>\<^sub>R = P \<oplus>\<^sub>p (\<Sigma>\<^sub>R \<times>\<^sub>L \<Sigma>\<^sub>R)"

definition drop_rea :: "('\<theta>, '\<alpha>, '\<beta>) relation_rp \<Rightarrow> ('\<alpha>, '\<beta>) relation" ("\<lfloor>_\<rfloor>\<^sub>R") where
[upred_defs]: "\<lfloor>P\<rfloor>\<^sub>R = P \<restriction>\<^sub>p (\<Sigma>\<^sub>R \<times>\<^sub>L \<Sigma>\<^sub>R)"

definition skip_rea_def [urel_defs]: "II\<^sub>r = (II \<or> (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>))"

lemma unrest_tr_lift_rea [unrest]:
  "$tr \<sharp> \<lceil>P\<rceil>\<^sub>R" "$tr\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>R"
  by (pred_tac)+

subsection {* R1: Events cannot be undone *}

definition R1_def [upred_defs]: "R1 (P) =  (P \<and> ($tr \<le>\<^sub>u $tr\<acute>))"

lemma R1_idem: "R1(R1(P)) = R1(P)"
  by pred_tac

lemma R1_mono: "P \<sqsubseteq> Q \<Longrightarrow> R1(P) \<sqsubseteq> R1(Q)"
  by pred_tac

lemma R1_conj: "R1(P \<and> Q) = (R1(P) \<and> R1(Q))"
  by pred_tac

lemma R1_disj: "R1(P \<or> Q) = (R1(P) \<or> R1(Q))"
  by pred_tac

lemma R1_extend_conj: "R1(P \<and> Q) = (R1(P) \<and> Q)"
  by pred_tac

lemma R1_cond: "R1(P \<triangleleft> b \<triangleright> Q) = (R1(P) \<triangleleft> b \<triangleright> R1(Q))"
  by rel_tac

lemma R1_negate_R1: "R1(\<not> R1(P)) = R1(\<not> P)"
  by pred_tac

lemma R1_wait_true: "(R1 P)\<^sub>t = R1(P)\<^sub>t"
  by pred_tac

lemma R1_wait_false: "(R1 P) \<^sub>f = R1(P) \<^sub>f"
  by pred_tac

lemma R1_skip: "R1(II) = II"
  by rel_tac

lemma R1_skip_rea: "R1(II\<^sub>r) = II\<^sub>r"
  by rel_tac

lemma R1_by_refinement:
  "P is R1 \<longleftrightarrow> (($tr \<le>\<^sub>u $tr\<acute>) \<sqsubseteq> P)"
  by rel_tac

lemma tr_le_trans:
  "($tr \<le>\<^sub>u $tr\<acute> ;; $tr \<le>\<^sub>u $tr\<acute>) = ($tr \<le>\<^sub>u $tr\<acute>)"
  by (rel_tac, metis alpha_d.select_convs(2) alpha_rp'.select_convs(2) eq_refl)

lemma R1_seqr_closure:
  assumes "P is R1" "Q is R1"
  shows "(P ;; Q) is R1"
  using assms unfolding R1_by_refinement
  by (metis seqr_mono tr_le_trans)

lemma R1_ok'_true: "(R1(P))\<^sup>t = R1(P\<^sup>t)"
  by pred_tac

lemma R1_ok'_false: "(R1(P))\<^sup>f = R1(P\<^sup>f)"
  by pred_tac

lemma R1_ok_true: "(R1(P))\<lbrakk>true/$ok\<rbrakk> = R1(P\<lbrakk>true/$ok\<rbrakk>)"
  by pred_tac

lemma R1_ok_false: "(R1(P))\<lbrakk>false/$ok\<rbrakk> = R1(P\<lbrakk>false/$ok\<rbrakk>)"
  by pred_tac

lemma seqr_R1_true_right: "((P ;; R1(true)) \<or> P) = (P ;; ($tr \<le>\<^sub>u $tr\<acute>))"
  by rel_tac

lemma R1_H2_commute: "R1(H2(P)) = H2(R1(P))"
  by (simp add: H2_split R1_def usubst, rel_tac)

subsection {* R2 *}

definition R2a_def [upred_defs]: "R2a (P) = (\<Sqinter> s \<bullet> P\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s\<guillemotright>^\<^sub>u($tr\<acute>-$tr)/$tr,$tr\<acute>\<rbrakk>)"
definition R2s_def [upred_defs]: "R2s (P) = (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>($tr\<acute>-$tr)/$tr\<acute>\<rbrakk>)"
definition R2_def [upred_defs]: "R2(P) = R1(R2s(P))"

lemma R2a_R2s: "R2a(R2s(P)) = R2s(P)"
  by rel_tac

lemma R2s_R2a: "R2s(R2a(P)) = R2a(P)"
  by rel_tac

lemma R2a_equiv_R2s: "P is R2a \<longleftrightarrow> P is R2s"
  by (metis Healthy_def' R2a_R2s R2s_R2a)

lemma R2s_idem: "R2s(R2s(P)) = R2s(P)"
  by (pred_tac)

lemma R2_idem: "R2(R2(P)) = R2(P)"
  by (pred_tac)

lemma R2_mono: "P \<sqsubseteq> Q \<Longrightarrow> R2(P) \<sqsubseteq> R2(Q)"
  by (pred_tac)

lemma R2s_conj: "R2s(P \<and> Q) = (R2s(P) \<and> R2s(Q))"
  by (pred_tac)

lemma R2_conj: "R2(P \<and> Q) = (R2(P) \<and> R2(Q))"
  by (pred_tac)

lemma R2s_disj: "R2s(P \<or> Q) = (R2s(P) \<or> R2s(Q))"
  by pred_tac

lemma R2_disj: "R2(P \<or> Q) = (R2(P) \<or> R2(Q))"
  by (pred_tac)

lemma R2s_not: "R2s(\<not> P) = (\<not> R2s(P))"
  by pred_tac

lemma R2s_condr: "R2s(P \<triangleleft> b \<triangleright> Q) = (R2s(P) \<triangleleft> R2s(b) \<triangleright> R2s(Q))"
  by rel_tac

lemma R2_condr: "R2(P \<triangleleft> b \<triangleright> Q) = (R2(P) \<triangleleft> R2(b) \<triangleright> R2(Q))"
  by rel_tac

lemma R2_condr': "R2(P \<triangleleft> b \<triangleright> Q) = (R2(P) \<triangleleft> R2s(b) \<triangleright> R2(Q))"
  by rel_tac

lemma R2s_wait: "R2s($wait) = $wait"
  by rel_tac

lemma R2s_wait': "R2s($wait\<acute>) = $wait\<acute>"
  by rel_tac

lemma R2s_tr'_eq_tr: "R2s($tr\<acute> =\<^sub>u $tr) = ($tr\<acute> =\<^sub>u $tr)"
  apply (pred_tac)
  using list_minus_anhil apply blast
done

lemma R2s_true: "R2s(true) = true"
  by pred_tac

lemma true_is_R2s:
  "true is R2s"
  by (simp add: Healthy_def R2s_true)

lemma R2s_lift_rea: "R2s(\<lceil>P\<rceil>\<^sub>R) = \<lceil>P\<rceil>\<^sub>R"
  by (simp add: R2s_def usubst unrest)

lemma R2_skip_rea: "R2(II\<^sub>r) = II\<^sub>r"
proof (rel_tac)
  fix a :: "('a, 'b) alpha_rp'_scheme alpha_d_ext" and b :: "('a, 'b) alpha_rp'_scheme alpha_d_ext"
  assume a1: "\<not> b = a"
  assume a2: "rp_tr (alpha_d.more a) \<le> rp_tr (alpha_d.more b)"
  assume a3: "b\<lparr>alpha_d.more := alpha_d.more b \<lparr>rp_tr := rp_tr (alpha_d.more b) - rp_tr (alpha_d.more a)\<rparr>\<rparr> = a\<lparr>alpha_d.more := alpha_d.more a \<lparr>rp_tr := uempty\<rparr>\<rparr>"
  assume a4: "des_ok a"
  obtain aas :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "\<forall>x0 x1. (\<exists>v2. x0 = x1 @ v2) = (x0 = x1 @ aas x0 x1)"
    by moura
  then have f5: "\<forall>as asa. \<not> as \<le> asa \<or> asa = as @ aas asa as"
    by (meson strict_prefixE)
  have "\<lparr>des_ok = True, rp_wait = rp_wait (alpha_d.more a), rp_tr = rp_tr (alpha_d.more a), rp_ref = rp_ref (alpha_d.more a), \<dots> = alpha_rp'.more (alpha_d.more a)\<rparr> = \<lparr>des_ok = des_ok a, \<dots> = alpha_d.more a\<rparr>"
    by (simp add: a4)
  then have "\<lparr>des_ok = True, rp_wait = rp_wait (alpha_d.more a), rp_tr = rp_tr (alpha_d.more a), rp_ref = rp_ref (alpha_d.more a), \<dots> = alpha_rp'.more (alpha_d.more a)\<rparr> = a"
    by (metis alpha_d.surjective)
  then have f6: "\<lparr>des_ok = True, \<dots> = alpha_d.more a\<lparr>rp_tr := uempty\<rparr>\<rparr> = b\<lparr>alpha_d.more := alpha_d.more b \<lparr>rp_tr := rp_tr (alpha_d.more b) - rp_tr (alpha_d.more a)\<rparr>\<rparr>"
    using a3 by (metis (no_types) alpha_d.update_convs(2))
  have f7: "\<lparr>des_ok = des_ok b, rp_wait = rp_wait (alpha_d.more b), rp_tr = rp_tr (alpha_d.more b), rp_ref = rp_ref (alpha_d.more b), \<dots> = alpha_rp'.more (alpha_d.more b)\<rparr> = b"
    by (metis (full_types) alpha_d.surjective alpha_rp'.surjective)
  have f8: "aas (rp_tr (alpha_d.more b)) (rp_tr (alpha_d.more a)) = rp_tr (alpha_d.more b) - rp_tr (alpha_d.more a)"
    using f5 a2 by (metis (no_types) append_minus)
  have "\<lparr>rp_wait = rp_wait (alpha_d.more b), rp_tr = rp_tr (alpha_d.more a) @ aas (rp_tr (alpha_d.more b)) (rp_tr (alpha_d.more a)), rp_ref = rp_ref (alpha_d.more b), \<dots> = alpha_rp'.more (alpha_d.more b)\<rparr> = alpha_d.more b"
    using f5 a2 by simp
  then have "b = \<lparr>des_ok = True, \<dots> = rp_tr_update (op @ (rp_tr (alpha_d.more a))) (alpha_d.more a\<lparr>rp_tr := uempty\<rparr>)\<rparr>"
    using f8 f7 f6 by (metis (no_types) alpha_d.surjective alpha_d.update_convs(2) alpha_rp'.update_convs(2))
  then have "b = \<lparr>des_ok = des_ok a, \<dots> = alpha_d.more a\<rparr>"
    using a4 by simp
  then show False
    using a1 by (metis (no_types) alpha_d.surjective)
qed

lemma tr_prefix_as_concat: "(xs \<le>\<^sub>u ys) = (\<^bold>\<exists> zs \<bullet> ys =\<^sub>u xs ^\<^sub>u \<guillemotleft>zs\<guillemotright>)"
  by (rel_tac, simp add: less_eq_list_def prefixeq_def)

lemma R2_form:
  "R2(P) = (\<^bold>\<exists> tt \<bullet> P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<guillemotright>)"
  by (rel_tac, metis prefix_subst strict_prefixE)

lemma uconc_left_unit [simp]: "\<langle>\<rangle> ^\<^sub>u e = e"
  by pred_tac

lemma uconc_right_unit [simp]: "e ^\<^sub>u \<langle>\<rangle> = e"
  by pred_tac

lemma R2_seqr_form: 
  shows "(R2(P) ;; R2(Q)) = 
         (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)) 
                        \<and> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>))"
proof -
  have "(R2(P) ;; R2(Q)) = (\<^bold>\<exists> tr\<^sub>0 \<bullet> (R2(P))\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; (R2(Q))\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>)"
    by (subst seqr_middle[of tr], simp_all)
  also have "... =
       (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>) ;; 
                                (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)))"
    by (simp add: R2_form usubst unrest uquant_lift, rel_tac)
  also have "... =
       (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((\<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; 
                                (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)))"
    by (simp add: conj_comm)
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tr\<^sub>0 \<bullet> ((P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)) 
                                \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    by rel_tac
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)) 
                        \<and> (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>))"
    by rel_tac
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)) 
                        \<and> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>))"
    by rel_tac
  finally show ?thesis .
qed

lemma R2_seqr_distribute: 
  fixes P :: "('\<theta>,'\<alpha>,'\<beta>) relation_rp" and Q :: "('\<theta>,'\<beta>,'\<gamma>) relation_rp"
  shows "R2(R2(P) ;; R2(Q)) = (R2(P) ;; R2(Q))"
proof -
  have "R2(R2(P) ;; R2(Q)) = 
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)\<lbrakk>($tr\<acute> - $tr)/$tr\<acute>\<rbrakk>
      \<and> $tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
    by (simp add: R2_seqr_form, simp add: R2s_def usubst unrest, rel_tac)
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)\<lbrakk>(\<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)/$tr\<acute>\<rbrakk>
      \<and> $tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
      by (subst subst_eq_replace, simp)
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
      by (rel_tac)
  also have "... =
    (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> ($tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr\<acute> \<ge>\<^sub>u $tr))"
    by pred_tac
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>))"
  proof -
    have "\<And> tt\<^sub>1 tt\<^sub>2. ((($tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr) :: ('\<theta>,'\<alpha>,'\<gamma>) relation_rp)
           = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (rel_tac, metis prefix_subst strict_prefixE)
    thus ?thesis by simp
  qed
  also have "... = (R2(P) ;; R2(Q))"
    by (simp add: R2_seqr_form)
  finally show ?thesis .
qed

lemma R2_seqr_closure:
  assumes "P is R2" "Q is R2"
  shows "(P ;; Q) is R2"
  by (metis Healthy_def' R2_seqr_distribute assms(1) assms(2))

lemma R1_R2_commute:
  "R1(R2(P)) = R2(R1(P))"
  by pred_tac

lemma R2s_H1_commute:
  "R2s(H1(P)) = H1(R2s(P))"
  by rel_tac

lemma R2s_H2_commute:
  "R2s(H2(P)) = H2(R2s(P))"
  by (simp add: H2_split R2s_def usubst, smt out_in_indep out_var_indep tr_ok_indep(1) usubst_upd_comm)

subsection {* R3 *}

definition R3_def [upred_defs]: "R3 (P) = (II \<triangleleft> $wait \<triangleright> P)"

definition R3c_def [upred_defs]: "R3c (P) = (II\<^sub>r \<triangleleft> $wait \<triangleright> P)"

lemma R3_idem: "R3(R3(P)) = R3(P)"
  by rel_tac

lemma R3_mono: "P \<sqsubseteq> Q \<Longrightarrow> R3(P) \<sqsubseteq> R3(Q)"
  by rel_tac

lemma R3_conj: "R3(P \<and> Q) = (R3(P) \<and> R3(Q))"
  by rel_tac

lemma R3_disj: "R3(P \<or> Q) = (R3(P) \<or> R3(Q))"
  by rel_tac

lemma R3_condr: "R3(P \<triangleleft> b \<triangleright> Q) = (R3(P) \<triangleleft> b \<triangleright> R3(Q))"
  by rel_tac

lemma R3_skipr: "R3(II) = II"
  by rel_tac

lemma R3_form: "R3(P) = (($wait \<and> II) \<or> (\<not> $wait \<and> P))"
  by rel_tac

lemma R3_semir_form:
  "(R3(P) ;; R3(Q)) = R3(P ;; R3(Q))"
  by rel_tac

lemma R3_semir_closure:
  assumes "P is R3" "Q is R3"
  shows "(P ;; Q) is R3"
  using assms
  by (metis Healthy_def' R3_semir_form)

lemma R3c_semir_form:
  "(R3c(P) ;; R3c(R1(Q))) = R3c(P ;; R3c(R1(Q)))"
  by rel_tac

lemma R3c_seq_closure:
  assumes "P is R3c" "Q is R3c" "Q is R1"
  shows "(P ;; Q) is R3c"
  by (metis Healthy_def' R3c_semir_form assms)

lemma R3c_subst_wait: "R3c(P) = R3c(P \<^sub>f)"
  by (metis R3c_def cond_var_subst_right wait_uvar)

lemma R1_R3_commute: "R1(R3(P)) = R3(R1(P))"
  by rel_tac

lemma R2_R3_commute: "R2(R3(P)) = R3(R2(P))"
  by (rel_tac, (smt alpha_d.surjective alpha_d.update_convs(2) alpha_rp'.surjective alpha_rp'.update_convs(2) append_Nil2 append_minus strict_prefixE)+)

lemma R2_R3c_commute: "R2(R3c(P)) = R3c(R2(P))"
  by (rel_tac, (smt alpha_d.surjective alpha_d.update_convs(2) alpha_rp'.surjective alpha_rp'.update_convs(2) append_minus append_self_conv strict_prefixE)+)

lemma R1_H1_R3c_commute:
  "R1(H1(R3c(P))) = R3c(R1(H1(P)))"
  by rel_tac

lemma R3c_H2_commute: "R3c(H2(P)) = H2(R3c(P))"
  apply (simp add: H2_split R3c_def usubst, rel_tac)
  apply (metis (mono_tags, lifting) alpha_d.surjective alpha_d.update_convs(1))+
done

lemma R3c_idem: "R3c(R3c(P)) = R3c(P)"
  by rel_tac
  
subsection {* RH laws *}

definition RH_def [upred_defs]: "RH(P) = R1(R2s(R3c(P)))"

lemma RH_alt_def:
  "RH(P) = R1(R2(R3c(P)))"
  by (simp add: R1_idem R2_def RH_def)

lemma RH_alt_def':
  "RH(P) = R2(R3c(P))"
  by (simp add: R2_def RH_def)

lemma RH_idem:
  "RH(RH(P)) = RH(P)"
  by (metis R2_R3c_commute R2_def R2_idem R3c_idem RH_def)

lemma RH_monotone:
  "P \<sqsubseteq> Q \<Longrightarrow> RH(P) \<sqsubseteq> RH(Q)"
  by rel_tac

lemma RH_intro:
  "\<lbrakk> P is R1; P is R2; P is R3c \<rbrakk> \<Longrightarrow> P is RH"
  by (simp add: Healthy_def' R2_def RH_def)
  
lemma RH_seq_closure:
  assumes "P is RH" "Q is RH"
  shows "(P ;; Q) is RH"
proof (rule RH_intro)
  show "(P ;; Q) is R1"
    by (metis Healthy_def' R1_seqr_closure R2_def RH_alt_def RH_def assms(1) assms(2))
  show "(P ;; Q) is R2"
    by (metis Healthy_def' R2_def R2_idem R2_seqr_closure RH_def assms(1) assms(2))
  show "(P ;; Q) is R3c"
    by (metis Healthy_def' R2_R3c_commute R2_def R3c_idem R3c_seq_closure RH_alt_def RH_def assms(1) assms(2))
qed

end