section \<open> Reactive Parallel-by-Merge \<close>

theory utp_rea_parallel
  imports utp_rea_healths
begin

text \<open> We show closure of parallel by merge under the reactive healthiness conditions by means
  of suitable restrictions on the merge predicate~\cite{Foster17b}. We first define healthiness 
  conditions for $R1$ and $R2$ merge predicates. \<close>

definition R1m :: "('t :: trace, '\<alpha>) rp merge \<Rightarrow> ('t, '\<alpha>) rp merge"
  where [upred_defs]: "R1m(M) = (M \<and> $tr\<^sub>< \<le>\<^sub>u $tr\<acute>)"

definition R1m' :: "('t :: trace, '\<alpha>) rp merge \<Rightarrow> ('t, '\<alpha>) rp merge"
  where [upred_defs]: "R1m'(M) = (M \<and> $tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<and> $tr\<^sub>< \<le>\<^sub>u $0-tr \<and> $tr\<^sub>< \<le>\<^sub>u $1-tr)"

text \<open> A merge predicate can access the history through $tr$, as usual, but also through $0.tr$ and
  $1.tr$. Thus we have to remove the latter two histories as well to satisfy R2 for the overall
  construction. \<close>
  
definition R2m :: "('t :: trace, '\<alpha>) rp merge \<Rightarrow> ('t, '\<alpha>) rp merge"
  where [upred_defs]: "R2m(M) = R1m(M\<lbrakk>0,($tr\<acute>-$tr\<^sub><),($0-tr-$tr\<^sub><),($1-tr-$tr\<^sub><)/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>)"

definition R2m' :: "('t :: trace, '\<alpha>) rp merge \<Rightarrow> ('t, '\<alpha>) rp merge"
  where [upred_defs]: "R2m'(M) = R1m'(M\<lbrakk>0,($tr\<acute>-$tr\<^sub><),($0-tr-$tr\<^sub><),($1-tr-$tr\<^sub><)/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>)"

definition R2cm :: "('t :: trace, '\<alpha>) rp merge \<Rightarrow> ('t, '\<alpha>) rp merge"
  where [upred_defs]: "R2cm(M) = M\<lbrakk>0,($tr\<acute>-$tr\<^sub><),($0-tr-$tr\<^sub><),($1-tr-$tr\<^sub><)/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk> \<triangleleft> $tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<triangleright> M"

lemma R2m'_form:
  "R2m'(M) =
  (\<^bold>\<exists> (tt\<^sub>p, tt\<^sub>0, tt\<^sub>1) \<bullet> M\<lbrakk>0,\<guillemotleft>tt\<^sub>p\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>
                    \<and> $tr\<acute> =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>p\<guillemotright>
                    \<and> $0-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>0\<guillemotright>
                    \<and> $1-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>1\<guillemotright>)"
  by (rel_auto, metis diff_add_cancel_left')

lemma R1m_idem: "R1m(R1m(P)) = R1m(P)"
  by (rel_auto)

lemma R1m_seq_lemma: "R1m(R1m(M) ;; R1(P)) = R1m(M) ;; R1(P)"
  by (rel_auto)

lemma R1m_seq [closure]:
  assumes "M is R1m" "P is R1"
  shows "M ;; P is R1m"
proof -
  from assms have "R1m(M ;; P) = R1m(R1m(M) ;; R1(P))"
    by (simp add: Healthy_if)
  also have "... = R1m(M) ;; R1(P)"
    by (simp add: R1m_seq_lemma)
  also have "... = M ;; P"
    by (simp add: Healthy_if assms)
  finally show ?thesis
    by (simp add: Healthy_def)
qed

lemma R2m_idem: "R2m(R2m(P)) = R2m(P)"
  by (rel_auto)

lemma R2m_seq_lemma: "R2m'(R2m'(M) ;; R2(P)) = R2m'(M) ;; R2(P)"
  apply (simp add: R2m'_form R2_form)
  apply (rel_auto)
   apply (metis (no_types, lifting) add.assoc)+
  done

lemma R2m'_seq [closure]:
  assumes "M is R2m'" "P is R2"
  shows "M ;; P is R2m'"
  by (metis Healthy_def' R2m_seq_lemma assms(1) assms(2))

lemma R1_par_by_merge [closure]:
  "M is R1m \<Longrightarrow> (P \<parallel>\<^bsub>M\<^esub> Q) is R1"
  by (rel_blast)
    
lemma R2_R2m'_pbm: "R2(P \<parallel>\<^bsub>M\<^esub> Q) = (R2(P) \<parallel>\<^bsub>R2m'(M)\<^esub> R2(Q))"
proof -
  have "(R2(P) \<parallel>\<^bsub>R2m'(M)\<^esub> R2(Q)) = ((R2(P) \<parallel>\<^sub>s R2(Q)) ;;
                   (\<^bold>\<exists> (tt\<^sub>p, tt\<^sub>0, tt\<^sub>1) \<bullet> M\<lbrakk>0,\<guillemotleft>tt\<^sub>p\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>
                                     \<and> $tr\<acute> =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>p\<guillemotright>
                                     \<and> $0-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>0\<guillemotright>
                                     \<and> $1-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>1\<guillemotright>))"
    by (simp add: par_by_merge_def R2m'_form)
  also have "... = (\<^bold>\<exists> (tt\<^sub>p, tt\<^sub>0, tt\<^sub>1) \<bullet> ((R2(P) \<parallel>\<^sub>s R2(Q)) ;; (M\<lbrakk>0,\<guillemotleft>tt\<^sub>p\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>
                                                  \<and> $tr\<acute> =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>p\<guillemotright>
                                                  \<and> $0-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>0\<guillemotright>
                                                  \<and> $1-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>1\<guillemotright>)))"
    by (rel_blast)
  also have "... = (\<^bold>\<exists> (tt\<^sub>p, tt\<^sub>0, tt\<^sub>1) \<bullet> (((R2(P) \<parallel>\<^sub>s R2(Q)) \<and> $0-tr\<acute> =\<^sub>u $tr\<^sub><\<acute> + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> $1-tr\<acute> =\<^sub>u $tr\<^sub><\<acute> + \<guillemotleft>tt\<^sub>1\<guillemotright>) ;;
                                      (M\<lbrakk>0,\<guillemotleft>tt\<^sub>p\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>p\<guillemotright>)))"
    by (rel_blast)
  also have "... = (\<^bold>\<exists> (tt\<^sub>p, tt\<^sub>0, tt\<^sub>1) \<bullet> (((R2(P) \<parallel>\<^sub>s R2(Q)) \<and> $0-tr\<acute> =\<^sub>u $tr\<^sub><\<acute> + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> $1-tr\<acute> =\<^sub>u $tr\<^sub><\<acute> + \<guillemotleft>tt\<^sub>1\<guillemotright>) ;;
                                      (M\<lbrakk>0,\<guillemotleft>tt\<^sub>p\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>)) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>p\<guillemotright>)"
    by (rel_blast)
  also have "... = (\<^bold>\<exists> (tt\<^sub>p, tt\<^sub>0, tt\<^sub>1) \<bullet> (((R2(P) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>) \<parallel>\<^sub>s (R2(Q) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright>)) ;;
                                      (M\<lbrakk>0,\<guillemotleft>tt\<^sub>p\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>)) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>p\<guillemotright>)"
    by (rel_auto, blast, metis le_add trace_class.add_diff_cancel_left)
  also have "... = (\<^bold>\<exists> (tt\<^sub>p, tt\<^sub>0, tt\<^sub>1) \<bullet> ((   ((\<^bold>\<exists> tt\<^sub>0' \<bullet> P\<lbrakk>0,\<guillemotleft>tt\<^sub>0'\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0'\<guillemotright>) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>)
                                       \<parallel>\<^sub>s ((\<^bold>\<exists> tt\<^sub>1' \<bullet> Q\<lbrakk>0,\<guillemotleft>tt\<^sub>1'\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1'\<guillemotright>) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright>)) ;;
                                      (M\<lbrakk>0,\<guillemotleft>tt\<^sub>p\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>)) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>p\<guillemotright>)"
    by (simp add: R2_form usubst)
  also have "... = (\<^bold>\<exists> (tt\<^sub>p, tt\<^sub>0, tt\<^sub>1) \<bullet> ((   (P\<lbrakk>0,\<guillemotleft>tt\<^sub>0\<guillemotright>/$tr,$tr\<acute>\<rbrakk>  \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>)
                                       \<parallel>\<^sub>s (Q\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright>)) ;;
                                      (M\<lbrakk>0,\<guillemotleft>tt\<^sub>p\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>)) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>p\<guillemotright>)"
    by (rel_auto, metis left_cancel_monoid_class.add_left_imp_eq, blast)
  also have "... = R2(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (rel_auto, blast, metis diff_add_cancel_left')
  finally show ?thesis ..
qed

lemma R2m_R2m'_pbm: "(R2(P) \<parallel>\<^bsub>R2m(M)\<^esub> R2(Q)) = (R2(P) \<parallel>\<^bsub>R2m'(M)\<^esub> R2(Q))"
  by (rel_blast)

lemma R2_par_by_merge [closure]:
  assumes "P is R2" "Q is R2" "M is R2m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R2"
  by (metis Healthy_def' R2_R2m'_pbm R2m_R2m'_pbm assms(1) assms(2) assms(3))

lemma R2_par_by_merge' [closure]:
  assumes "P is R2" "Q is R2" "M is R2m'"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R2"
  by (metis Healthy_def' R2_R2m'_pbm assms(1) assms(2) assms(3))
  
lemma R1m_skip_merge: "R1m(skip\<^sub>m) = skip\<^sub>m"
  by (rel_auto)

lemma R1m_disj: "R1m(P \<or> Q) = (R1m(P) \<or> R1m(Q))"
  by (rel_auto)

lemma R1m_conj: "R1m(P \<and> Q) = (R1m(P) \<and> R1m(Q))"
  by (rel_auto)

lemma R2m_skip_merge: "R2m(skip\<^sub>m) = skip\<^sub>m"
  apply (rel_auto) using minus_zero_eq by blast

lemma R2m_disj: "R2m(P \<or> Q) = (R2m(P) \<or> R2m(Q))"
  by (rel_auto)

lemma R2m_conj: "R2m(P \<and> Q) = (R2m(P) \<and> R2m(Q))"
  by (rel_auto)

definition R3m :: "('t :: trace, '\<alpha>) rp merge \<Rightarrow> ('t, '\<alpha>) rp merge" where
  [upred_defs]: "R3m(M) = skip\<^sub>m \<triangleleft> $wait\<^sub>< \<triangleright> M"

lemma R3_par_by_merge:
  assumes
    "P is R3" "Q is R3" "M is R3m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R3"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = ((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (metis cond_L6 cond_var_split in_var_uvar wait_vwb_lens)
  also have "... = (((R3 P)\<lbrakk>true/$wait\<rbrakk> \<parallel>\<^bsub>(R3m M)\<lbrakk>true/$wait\<^sub><\<rbrakk>\<^esub> (R3 Q)\<lbrakk>true/$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (subst_tac, simp add: Healthy_if assms)
  also have "... = ((II\<lbrakk>true/$wait\<rbrakk> \<parallel>\<^bsub>skip\<^sub>m\<lbrakk>true/$wait\<^sub><\<rbrakk>\<^esub> II\<lbrakk>true/$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (simp add: R3_def R3m_def usubst)
  also have "... = ((II \<parallel>\<^bsub>skip\<^sub>m\<^esub> II)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (subst_tac)
  also have "... = (II \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (simp add: cond_var_subst_left par_by_merge_skip)
  also have "... = R3(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: R3_def)
  finally show ?thesis
    by (simp add: Healthy_def)
qed

lemma SymMerge_R1_true [closure]:
  "M is SymMerge \<Longrightarrow> M ;; R1(true) is SymMerge"
  by (rel_auto)

end