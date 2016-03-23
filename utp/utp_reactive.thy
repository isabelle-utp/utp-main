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
  
record '\<theta> alpha_rp  = alpha_d + 
                         rp_wait :: bool
                         rp_tr   :: "'\<theta> trace"
                         rp_ref  :: "'\<theta> refusal"

definition "wait = VAR rp_wait"
definition "tr   = VAR rp_tr"
definition "ref  = VAR rp_ref"

declare wait_def [upred_defs]
declare tr_def [upred_defs]
declare ref_def [upred_defs]

lemma tr_ok_indep [simp]: "tr \<bowtie> ok" "ok \<bowtie> tr"
  by (auto intro!: lens_indepI, pred_tac+)

lemma wait_ok_indep [simp]: "wait \<bowtie> ok" "ok \<bowtie> wait"
  by (auto intro!: lens_indepI, pred_tac+)

lemma ref_ok_indep [simp]: "ref \<bowtie> ok" "ok \<bowtie> ref"
  by (auto intro!: lens_indepI, pred_tac+)

lemma tr_wait_indep [simp]: "tr \<bowtie> wait" "wait \<bowtie> tr"
  by (auto intro!: lens_indepI, pred_tac+)

lemma ref_wait_indep [simp]: "ref \<bowtie> wait" "wait \<bowtie> ref"
  by (auto intro!: lens_indepI, pred_tac+)

lemma tr_ref_indep [simp]: "ref \<bowtie> tr" "tr \<bowtie> ref"
  by (auto intro!: lens_indepI, pred_tac+)

instantiation alpha_rp_ext :: (type, vst) vst
begin
  definition get_vstore_alpha_rp_ext :: "('a, 'b) alpha_rp_ext \<Rightarrow> vstore"
  where [simp]: "get_vstore_alpha_rp_ext x = get_vstore (alpha_rp.more (alpha_d.extend undefined x))"
  definition put_vstore_alpha_rp_ext :: "('a, 'b) alpha_rp_ext \<Rightarrow> vstore \<Rightarrow> ('a, 'b) alpha_rp_ext"
  where [simp]: "put_vstore_alpha_rp_ext s x = alpha_d.more (alpha_rp.more_update (\<lambda>v. put_vstore v x) (alpha_d.extend undefined s))"
instance
  apply (intro_classes, auto simp add: alpha_rp.defs alpha_d.defs)
  apply (metis alpha_d.select_convs(2) alpha_rp.select_convs(4) alpha_rp.surjective alpha_rp.update_convs(4) put_get_vstore)
  apply (metis (no_types, lifting) alpha_d.select_convs(2) alpha_rp.surjective alpha_rp.update_convs(4) get_put_vstore)
  apply (metis (no_types, lifting) alpha_d.select_convs(2) alpha_rp.surjective alpha_rp.update_convs(4) put_put_vstore)
done
end

lemma uvar_wait [simp]: "uvar wait"
  by (unfold_locales, simp_all add: wait_def)

lemma uvar_tr [simp]: "uvar tr"
  by (unfold_locales, simp_all add: tr_def)

lemma uvar_ref [simp]: "uvar ref"
  by (unfold_locales, simp_all add: ref_def)

text{* Note that we define here the class of UTP alphabets that contain
$wait$, $tr$ and $ref$, or, in other words, we define here the class of reactive process
alphabets. *}

type_synonym ('\<theta>,'\<alpha>) alphabet_rp  = "('\<theta>,'\<alpha>) alpha_rp_scheme alphabet"
type_synonym ('\<theta>,'\<alpha>,'\<beta>) relation_rp  = "(('\<theta>,'\<alpha>) alphabet_rp, ('\<theta>,'\<beta>) alphabet_rp) relation"
type_synonym ('\<theta>,'\<alpha>) hrelation_rp  = "(('\<theta>,'\<alpha>) alphabet_rp, ('\<theta>,'\<alpha>) alphabet_rp) relation"
type_synonym ('\<theta>,'\<sigma>) predicate_rp  = "('\<theta>,'\<sigma>) alphabet_rp upred"

abbreviation wait_f::"('\<theta>, '\<alpha>, '\<beta>) relation_rp \<Rightarrow> ('\<theta>, '\<alpha>, '\<beta>) relation_rp" ("_\<^sub>f" [1000] 1000)
where "wait_f R \<equiv> R\<lbrakk>false/$wait\<rbrakk>"

abbreviation wait_t::"('\<theta>, '\<alpha>, '\<beta>) relation_rp \<Rightarrow> ('\<theta>, '\<alpha>, '\<beta>) relation_rp" ("_\<^sub>t" [1000] 1000)
where "wait_t R \<equiv> R\<lbrakk>true/$wait\<rbrakk>"

lift_definition lift_rea :: "('\<alpha>, '\<beta>) relation \<Rightarrow> ('\<theta>, '\<alpha>, '\<beta>) relation_rp" ("\<lceil>_\<rceil>\<^sub>R") is
"\<lambda> P (A, A'). P (more A, more A')" .

lift_definition drop_rea :: "('\<theta>, '\<alpha>, '\<beta>) relation_rp \<Rightarrow> ('\<alpha>, '\<beta>) relation" ("\<lfloor>_\<rfloor>\<^sub>R") is
"\<lambda> P (A, A'). P (\<lparr> des_ok = True, rp_wait = True, rp_tr = [], rp_ref = {}, \<dots> = A \<rparr>, 
                 \<lparr> des_ok = True, rp_wait = True, rp_tr = [], rp_ref = {}, \<dots> = A' \<rparr>)" .

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

lemma R1_wait_false: "(R1 P)\<^sub>f = R1(P)\<^sub>f"
  by pred_tac

lemma R1_skip: "R1(II) = II"
  by rel_tac

lemma R1_by_refinement:
  "P is R1 \<longleftrightarrow> (($tr \<le>\<^sub>u $tr\<acute>) \<sqsubseteq> P)"
  by rel_tac

lemma tr_le_trans:
  "($tr \<le>\<^sub>u $tr\<acute> ;; $tr \<le>\<^sub>u $tr\<acute>) = ($tr \<le>\<^sub>u $tr\<acute>)"
  by (rel_tac, metis alpha_rp.select_convs(2) order_refl)

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

subsection {* R2 *}

definition R2s_def [upred_defs]: "R2s (P) = (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>($tr\<acute>-$tr)/$tr\<acute>\<rbrakk>)"
definition R2_def [upred_defs]: "R2(P) = R1(R2s(P))"

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

lemma R2s_condr: "R2s(P \<triangleleft> b \<triangleright> Q) = (R2s(P) \<triangleleft> R2s(b) \<triangleright> R2s(Q))"
  by rel_tac

lemma R2_condr: "R2(P \<triangleleft> b \<triangleright> Q) = (R2(P) \<triangleleft> R2(b) \<triangleright> R2(Q))"
  by rel_tac

lemma tr_prefix_as_concat: "(xs \<le>\<^sub>u ys) = (\<^bold>\<exists> zs \<bullet> ys =\<^sub>u xs ^\<^sub>u \<guillemotleft>zs\<guillemotright>)"
  by (rel_tac, simp add: less_eq_list_def prefixeq_def)

lemma R2_form:
  "R2(P) = (\<^bold>\<exists> tt \<bullet> P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<guillemotright>)"
  by (rel_tac, metis prefix_subst strict_prefixE)

lemma uconc_left_unit [simp]: "\<langle>\<rangle> ^\<^sub>u e = e"
  by pred_tac

lemma uconc_right_unit [simp]: "e ^\<^sub>u \<langle>\<rangle> = e"
  by pred_tac

text {* This laws is proven only for homogeneous relations, can it be generalised? *}

lemma R2_seqr_form: 
  fixes P Q :: "('\<theta>,'\<alpha>,'\<alpha>) relation_rp"
  shows "(R2(P) ;; R2(Q)) = 
         (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)) 
                        \<and> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>))"
proof -
  have "(R2(P) ;; R2(Q)) = (\<^bold>\<exists> tr\<^sub>0 \<bullet> (R2(P))\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; (R2(Q))\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>)"
    by (subst seqr_middle[of tr], simp_all)
  also have "... =
       (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>) ;; 
                                (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)))"
    by (simp add: R2_form usubst unrest uquant_lift var_in_var var_out_var, rel_tac)
  also have "... =
       (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((\<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; 
                                (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)))"
    by (simp add: conj_comm)
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tr\<^sub>0 \<bullet> ((P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)) 
                                \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    by (simp add: seqr_pre_out seqr_post_out unrest, rel_tac)
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
  fixes P Q :: "('\<theta>,'\<alpha>,'\<alpha>) relation_rp"
  shows "R2(R2(P) ;; R2(Q)) = (R2(P) ;; R2(Q))"
proof -
  have "R2(R2(P) ;; R2(Q)) = 
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)\<lbrakk>($tr\<acute> - $tr)/$tr\<acute>\<rbrakk>
      \<and> $tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
    by (simp add: R2_seqr_form, simp add: R2s_def usubst unrest, rel_tac, blast+)
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)\<lbrakk>(\<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)/$tr\<acute>\<rbrakk>
      \<and> $tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
      by (subst subst_eq_replace, simp)
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
      by (simp add: usubst unrest)
  also have "... =
    (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> ($tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr\<acute> \<ge>\<^sub>u $tr))"
    by pred_tac
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>))"
  proof -
    have "\<And> tt\<^sub>1 tt\<^sub>2. ((($tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr) :: ('\<theta>,'\<alpha>,'\<alpha>) relation_rp)
           = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (rel_tac, metis prefix_subst strict_prefixE)
    thus ?thesis by simp
  qed
  also have "... = (R2(P) ;; R2(Q))"
    by (simp add: R2_seqr_form)
  finally show ?thesis .
qed

lemma R1_R2_commute:
  "R1(R2(P)) = R2(R1(P))"
  by pred_tac

subsection {* R3 *}

definition skip_rea_def [urel_defs]: "II\<^sub>r = (II \<or> (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>))"

definition R3_def [upred_defs]: "R3 (P) = (II \<triangleleft> $wait \<triangleright> P)"

definition R3c_def [upred_defs]: "R3c (P) = (II\<^sub>r \<triangleleft> $wait \<triangleright> P)"

definition RH_def [upred_defs]: "RH(P) = R1(R2(R3c(P)))"

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

lemma R1_R3_commute: "R1(R3(P)) = R3(R1(P))"
  by rel_tac

lemma R2_R3_commute: "R2(R3(P)) = R3(R2(P))"
  by (rel_tac, (metis (no_types, lifting) alpha_rp.surjective alpha_rp.update_convs(2) append_Nil2 prefix_subst strict_prefixE)+)

lemma R2_R3c_commute: "R2(R3c(P)) = R3c(R2(P))"
  by (rel_tac, (metis (no_types, lifting) alpha_rp.surjective alpha_rp.update_convs(2) append_Nil2 append_minus strict_prefixE)+)

lemma R3c_idem: "R3c(R3c(P)) = R3c(P)"
  by rel_tac

lemma R1_skip_rea: "R1(II\<^sub>r) = II\<^sub>r"
  by rel_tac

lemma R2_skip_rea: "R2(II\<^sub>r) = II\<^sub>r"
  apply (rel_tac)
  apply (metis (no_types, lifting) alpha_rp.surjective alpha_rp.update_convs(2) append_Nil2 prefix_subst strict_prefixE)
done

end