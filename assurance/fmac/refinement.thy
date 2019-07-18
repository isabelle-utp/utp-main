section \<open> Refinement of Abstract Machines \<close>

theory refinement
    imports "UTP.utp_full"
begin

subsection \<open> Abstract Machines \<close>

record 's machine =
  init    :: "'s usubst"    ("Init\<index>")
  invs    :: "'s upred"     ("Invs\<index>")
  body    :: "'s hrel"      ("Body\<index>")

definition semantics :: "'s machine \<Rightarrow> 's hrel" ("Sem\<index>") where
[upred_defs]: "semantics M = (\<langle>init M\<rangle>\<^sub>a ;; ?[invs M]) ;; (body M)\<^sup>\<star>"

locale machine =
  fixes M :: "'s machine" (structure)
  \<comment> \<open> The invariant under initial constraints admits at least one observation (i.e. it is not @{term false}) \<close>
  assumes feasible_init_invs: "`\<exists> &\<^bold>v \<bullet> Init \<dagger> Invs`"
  \<comment> \<open> The body preserves the invariant \<close>
  and body_invs: "`Invs \<Rightarrow> Body wlp Invs`"
  \<comment> \<open> The body does not abort -- deadlock freedom \<close>
  and body_progress: "`Invs \<Rightarrow> Body wp true`"
begin

  lemma body_invs' [hoare_safe]: "\<lbrace>Invs\<rbrace>Body\<lbrace>Invs\<rbrace>\<^sub>u"
    by (simp add: body_invs wlp_hoare_link)

  lemma semantics_invs [hoare_safe]: "\<lbrace>true\<rbrace>Sem\<lbrace>Invs\<rbrace>\<^sub>u"
    apply (simp add: semantics_def)
    apply (rule seq_hoare_inv_r_2)
     apply (hoare_auto)
    apply (hoare_auto)
    done

  lemma body_reachable_invs: "`Invs \<Rightarrow> Body wp Invs`"
    using body_invs body_progress by (rel_blast)

end

subsection \<open> Refinements \<close>

record ('s\<^sub>1, 's\<^sub>2) refinement =
  abs_m     :: "'s\<^sub>1 machine" ("\<M>\<^sub>A\<index>")    \<comment> \<open> Abstract Machine \<close>
  con_m     :: "'s\<^sub>2 machine" ("\<M>\<^sub>C\<index>")    \<comment> \<open> Concrete Machine \<close>
  retrieve  :: "('s\<^sub>1 , 's\<^sub>2) urel" ("\<R>\<index>") \<comment> \<open> Retrieve Relation \<close>

abbreviation abs_invs ("Inv\<^sub>A\<index>") where "abs_invs R \<equiv> invs (abs_m R)"
abbreviation con_invs ("Inv\<^sub>C\<index>") where "con_invs R \<equiv> invs (con_m R)"

abbreviation abs_body ("Body\<^sub>A\<index>") where "abs_body R \<equiv> body (abs_m R)"
abbreviation con_body ("Body\<^sub>C\<index>") where "con_body R \<equiv> body (con_m R)"

locale refinement =
  fixes R :: "('s\<^sub>1, 's\<^sub>2) refinement" (structure)
  \<comment> \<open> Both machines are valid \<close>
  assumes abs_machine: "machine \<M>\<^sub>A" and con_machine: "machine \<M>\<^sub>C"

locale rel_refinement = refinement +
  \<comment> \<open> The retrieve relation is surjective: any supported abstract element is ``round-tripped'' \<close>
  assumes retrieve_surj: "II \<sqsubseteq> \<R> ;; \<R>\<^sup>-"

subsection \<open> Forward Refinements \<close>

locale fwd_refinement = rel_refinement +
  assumes fwd_sim: "body (abs_m R) ;; retrieve R \<sqsubseteq> retrieve R ;; body (con_m R)"

subsection \<open> Backward Refinements \<close>

locale bwd_refinement = rel_refinement +
  \<comment> \<open> The concrete invariant through the retrieve relation strengthens the abstract invariant \<close>
  assumes bwd_invs: "`\<R> wp Inv\<^sub>C \<Rightarrow> Inv\<^sub>A`"
  \<comment> \<open> The abstract operations are refined by the concrete ones \<close>
  and bwd_sim: "?[Inv\<^sub>C] ;; \<R>\<^sup>- ;; Body\<^sub>A \<sqsubseteq> ?[Inv\<^sub>C] ;; Body\<^sub>C ;; \<R>\<^sup>-"
begin

  lemma bwd_invs_wp: "`Inv\<^sub>C \<Rightarrow> \<R>\<^sup>- wlp Inv\<^sub>A`"
    using bwd_invs by (rel_auto, metis (mono_tags) assigns_r.rep_eq case_prodI)

  lemma conv_retrieve_invs: "\<lbrace>Inv\<^sub>C\<rbrace>\<R>\<^sup>-\<lbrace>Inv\<^sub>A\<rbrace>\<^sub>u"
    by (simp add: sp_hoare_link sp bwd_invs)

  lemma retrieve_assm_prop: "?[Inv\<^sub>A] ;; \<R> ;; ?[Inv\<^sub>C] = \<R> ;; ?[Inv\<^sub>C]"
  proof -
    have f1: "`Dom (\<R> ;; ?[Inv\<^sub>C]::('a, 'b) urel) \<Rightarrow> Inv\<^sub>A`"
      by (metis (full_types) bwd_invs wp_upred_def)
    have f2: "\<forall>u. u = Dom (II::'a hrel) \<or> \<not> `u`"
      by (metis (no_types) Dom_assume RA1 assume_Dom assume_seq eq_split impl_mp2 taut_conj upred_semiring.mult.left_neutral)
    have "\<forall>u. (II::'a hrel) ;; (u::('a, 'b) urel) = u"
      by simp
    then show ?thesis
      using f2 f1 by (metis (no_types) RA1 assume_Dom assume_seq impl_mp2)
  qed

  lemma refine_lemma: "?[Inv\<^sub>A] ;; Body\<^sub>A \<sqsubseteq> \<R> ;; ?[Inv\<^sub>C] ;; Body\<^sub>C ;; \<R>\<^sup>-"
  proof -
    have 1:"?[Inv\<^sub>A] ;; Body\<^sub>A \<sqsubseteq> ?[Inv\<^sub>A] ;; \<R> ;; \<R>\<^sup>- ;; Body\<^sub>A"
      by (metis (no_types, hide_lams) RA1 order_refl retrieve_surj seqr_mono upred_semiring.mult.left_neutral)
    have 2:"?[Inv\<^sub>A] ;; \<R> ;; \<R>\<^sup>- ;; Body\<^sub>A \<sqsubseteq> (?[Inv\<^sub>A] ;; \<R> ;; ?[Inv\<^sub>C]) ;; \<R>\<^sup>- ;; Body\<^sub>A"
      by (rel_auto)
    have 3: "(?[Inv\<^sub>A] ;; \<R> ;; ?[Inv\<^sub>C]) ;; \<R>\<^sup>- ;; Body\<^sub>A = \<R> ;; ?[Inv\<^sub>C] ;; \<R>\<^sup>- ;; Body\<^sub>A"
      by (metis (no_types, lifting) RA1 retrieve_assm_prop)
    from 1 2 3 have 4: "?[Inv\<^sub>A] ;; Body\<^sub>A \<sqsubseteq> \<R> ;; ?[Inv\<^sub>C] ;; \<R>\<^sup>- ;; Body\<^sub>A"
      by (simp)
    have 5:"\<R> ;; ?[Inv\<^sub>C] ;; \<R>\<^sup>- ;; Body\<^sub>A \<sqsubseteq> \<R> ;; ?[Inv\<^sub>C] ;; Body\<^sub>C ;; \<R>\<^sup>-"
      by (simp add: bwd_sim seqr_mono)
    from 4 5 show ?thesis
      using order.trans by blast
  qed

  text \<open> Crucial theorem: all safety properties are preserved by data refinement \<close>

  theorem refinement_preserves_safety:
    assumes "\<lbrace>Inv\<^sub>A \<and> p\<rbrace> Body\<^sub>A \<lbrace>q\<rbrace>\<^sub>u"
    shows  "\<lbrace>Inv\<^sub>C \<and> p sp \<R>\<rbrace> Body\<^sub>C \<lbrace>\<R>\<^sup>- wlp q\<rbrace>\<^sub>u"
  proof -
    have "(\<lceil>p\<rceil>\<^sub>< \<Rightarrow> \<lceil>q\<rceil>\<^sub>>) \<sqsubseteq> \<R> ;; ?[Inv\<^sub>C] ;; Body\<^sub>C ;; \<R>\<^sup>-"
      by (meson assms dual_order.trans hoare_pre_assume_1 hoare_r_def refine_lemma)
    hence 1:"\<lbrace>p\<rbrace>\<R> ;; ?[Inv\<^sub>C] ;; Body\<^sub>C ;; \<R>\<^sup>-\<lbrace>q\<rbrace>\<^sub>u"
      by (simp add: hoare_r_def)
    have 2: "\<lbrace>p\<rbrace>\<R> ;; ?[Inv\<^sub>C] ;; Body\<^sub>C ;; \<R>\<^sup>-\<lbrace>q\<rbrace>\<^sub>u = \<lbrace>Inv\<^sub>C \<and> p sp \<R>\<rbrace> Body\<^sub>C \<lbrace>\<R>\<^sup>- wlp q\<rbrace>\<^sub>u"
      by (rel_blast)
    also have "... = \<lbrace>Inv\<^sub>C \<and> p sp \<R>\<rbrace> Body\<^sub>C \<lbrace>Inv\<^sub>C \<and> \<R>\<^sup>- wlp q\<rbrace>\<^sub>u"
      by (metis "1" calculation con_machine hoare_r_conj hoare_r_weaken_pre(2) machine.body_invs' utp_pred_laws.inf_commute)
    finally show ?thesis
      using "1" "2" by blast 
  qed

  theorem refinement_preserves_safety_wlp:
    assumes "`(Inv\<^sub>A \<and> p) \<Rightarrow> Body\<^sub>A wlp q`"
    shows "`(Inv\<^sub>C \<and> p sp \<R>) \<Rightarrow> Body\<^sub>C wlp (\<R>\<^sup>- wlp q)`"
    by (meson assms refinement_preserves_safety wlp_hoare_link)

end

lemma bwd_refineI: 
  assumes 
    "machine \<M>\<^sub>A\<^bsub>R\<^esub>" "machine \<M>\<^sub>C\<^bsub>R\<^esub>" "II \<sqsubseteq> \<R>\<^bsub>R\<^esub> ;; \<R>\<^bsub>R\<^esub>\<^sup>-"
    "`\<R>\<^bsub>R\<^esub> wp Inv\<^sub>C\<^bsub>R\<^esub> \<Rightarrow> Inv\<^sub>A\<^bsub>R\<^esub>`" "?[Inv\<^sub>C\<^bsub>R\<^esub>] ;; \<R>\<^bsub>R\<^esub>\<^sup>- ;; Body\<^sub>A\<^bsub>R\<^esub> \<sqsubseteq> ?[Inv\<^sub>C\<^bsub>R\<^esub>] ;; Body\<^sub>C\<^bsub>R\<^esub> ;; \<R>\<^bsub>R\<^esub>\<^sup>-" 
  shows "bwd_refinement R"
  by (simp add: assms bwd_refinement_axioms.intro bwd_refinement_def refinement.intro rel_refinement_axioms.intro rel_refinement_def)

subsection \<open> Functional refinement \<close>

locale func_refinement = refinement +
  fixes \<sigma> :: "'s\<^sub>2 \<Rightarrow> 's\<^sub>1"
  assumes retrieve_func: "\<R> = \<langle>\<sigma>\<rangle>\<^sub>a\<^sup>-"
  and func_invs: "`Inv\<^sub>C \<Rightarrow> (\<sigma> \<dagger> Inv\<^sub>A)`"
  and func_sim: "?[Inv\<^sub>C] ;; \<langle>\<sigma>\<rangle>\<^sub>a ;; Body\<^sub>A \<sqsubseteq> ?[Inv\<^sub>C] ;; Body\<^sub>C ;; \<langle>\<sigma>\<rangle>\<^sub>a"
begin

sublocale rel_refinement
proof
  show "II \<sqsubseteq> \<R> ;; \<R>\<^sup>-"
    by (simp add: retrieve_func, rel_auto)
qed

sublocale bwd_refinement
proof
  show "`\<R> wp Inv\<^sub>C \<Rightarrow> Inv\<^sub>A`"
    by (simp add: retrieve_func wp sp, rel_simp, metis func_invs refBy_order subst.rep_eq upred_ref_iff)
  show "?[Inv\<^sub>C] ;; \<R>\<^sup>- ;; Body\<^sub>A \<sqsubseteq> ?[Inv\<^sub>C] ;; Body\<^sub>C ;; \<R>\<^sup>-"
    by (simp add: retrieve_func func_sim)
qed

  theorem refinement_preserves_safety_func:
    assumes "\<lbrace>Inv\<^sub>A \<and> p\<rbrace> Body\<^sub>A \<lbrace>q\<rbrace>\<^sub>u"
    shows  "\<lbrace>Inv\<^sub>C \<and> \<sigma> \<dagger> p\<rbrace> Body\<^sub>C \<lbrace>\<sigma> \<dagger> q\<rbrace>\<^sub>u"
    by (metis assms bwd_refinement.refinement_preserves_safety bwd_refinement_axioms convr_invol retrieve_func wlp_assigns_r wp_assigns wp_convr)

  theorem refinement_preserves_safety_wlp_func:
    assumes "`(Inv\<^sub>A \<and> p) \<Rightarrow> Body\<^sub>A wlp q`"
    shows "`Inv\<^sub>C \<and> \<sigma> \<dagger> p \<Rightarrow> Body\<^sub>C wlp \<sigma> \<dagger> q`"
    using assms
    by (metis convr_invol refinement_preserves_safety_wlp retrieve_func wlp_assigns_r wp_assigns wp_convr)

end

lemma func_refinementI:
  assumes 
    "machine \<M>\<^sub>A\<^bsub>R\<^esub>" "machine \<M>\<^sub>C\<^bsub>R\<^esub>" "\<R>\<^bsub>R\<^esub> = \<langle>\<sigma>\<rangle>\<^sub>a\<^sup>-"
    "`Inv\<^sub>C\<^bsub>R\<^esub> \<Rightarrow> (\<sigma> \<dagger> Inv\<^sub>A\<^bsub>R\<^esub>)`" "?[Inv\<^sub>C\<^bsub>R\<^esub>] ;; \<langle>\<sigma>\<rangle>\<^sub>a ;; Body\<^sub>A\<^bsub>R\<^esub> \<sqsubseteq> ?[Inv\<^sub>C\<^bsub>R\<^esub>] ;; Body\<^sub>C\<^bsub>R\<^esub> ;; \<langle>\<sigma>\<rangle>\<^sub>a" 
  shows "func_refinement R \<sigma>"
  by (simp add: assms func_refinement.intro func_refinement_axioms.intro refinement.intro) 

definition func_refine :: "'s\<^sub>1 machine \<Rightarrow> 's\<^sub>2 machine \<Rightarrow> ('s\<^sub>2 \<Rightarrow> 's\<^sub>1) \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) refinement" where
"func_refine M\<^sub>1 M\<^sub>2 \<sigma> = \<lparr> abs_m = M\<^sub>1, con_m = M\<^sub>2, retrieve = \<langle>\<sigma>\<rangle>\<^sub>a\<^sup>- \<rparr>"

lemma func_refineI: 
  assumes "machine M\<^sub>1" "machine M\<^sub>2" "`Invs\<^bsub>M\<^sub>2\<^esub> \<Rightarrow> (\<sigma> \<dagger> Invs\<^bsub>M\<^sub>1\<^esub>)`"
    "?[Invs\<^bsub>M\<^sub>2\<^esub>] ;; \<langle>\<sigma>\<rangle>\<^sub>a ;; Body\<^bsub>M\<^sub>1\<^esub> \<sqsubseteq> ?[Invs\<^bsub>M\<^sub>2\<^esub>] ;; Body\<^bsub>M\<^sub>2\<^esub> ;; \<langle>\<sigma>\<rangle>\<^sub>a"
  shows "bwd_refinement (func_refine M\<^sub>1 M\<^sub>2 \<sigma>)"
  apply (rule bwd_refineI, simp_all add: func_refine_def assms wp sp)
    apply (rel_simp)
    apply (rel_simp)
  apply (metis assms(3) refBy_order subst.rep_eq upred_ref_iff)
  done

lemma func_refineI':
  assumes "machine M\<^sub>1" "machine M\<^sub>2" "`Invs\<^bsub>M\<^sub>2\<^esub> \<Rightarrow> (\<sigma> \<dagger> Invs\<^bsub>M\<^sub>1\<^esub>)`"
    "?[Invs\<^bsub>M\<^sub>2\<^esub>] ;; \<langle>\<sigma>\<rangle>\<^sub>a ;; Body\<^bsub>M\<^sub>1\<^esub> \<sqsubseteq> ?[Invs\<^bsub>M\<^sub>2\<^esub>] ;; Body\<^bsub>M\<^sub>2\<^esub> ;; \<langle>\<sigma>\<rangle>\<^sub>a"
  shows "func_refinement (func_refine M\<^sub>1 M\<^sub>2 \<sigma>) \<sigma>"
  by (rule func_refinementI, simp_all add: func_refine_def assms wp sp)

end