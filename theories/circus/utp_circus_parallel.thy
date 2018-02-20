section \<open> Circus Parallel Composition \<close>

theory utp_circus_parallel
  imports 
    utp_circus_prefix
    utp_circus_traces
begin

subsection \<open> Merge predicates \<close>

definition CSPInnerMerge :: "('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> '\<psi> set \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> (('\<sigma>,'\<psi>) st_csp) merge" ("N\<^sub>C") where
  [upred_defs]:
  "CSPInnerMerge ns1 cs ns2 = (
    $ref\<acute> \<subseteq>\<^sub>u (($0-ref \<union>\<^sub>u $1-ref) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u (($0-ref \<inter>\<^sub>u $1-ref) - \<guillemotleft>cs\<guillemotright>) \<and>
    $tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<and>
    ($tr\<acute> - $tr\<^sub><) \<in>\<^sub>u ($0-tr - $tr\<^sub><) \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> ($1-tr - $tr\<^sub><) \<and>
    ($0-tr - $tr\<^sub><) \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u ($1-tr - $tr\<^sub><) \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and>
    $st\<acute> =\<^sub>u ($st\<^sub>< \<oplus> $0-st on &ns1) \<oplus> $1-st on &ns2)"

definition CSPInnerInterleave :: "('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> (('\<sigma>,'\<psi>) st_csp) merge" ("N\<^sub>I") where
  [upred_defs]:
  "N\<^sub>I ns1 ns2 = (
    $ref\<acute> \<subseteq>\<^sub>u ($0-ref \<inter>\<^sub>u $1-ref) \<and>
    $tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<and>
    ($tr\<acute> - $tr\<^sub><) \<in>\<^sub>u ($0-tr - $tr\<^sub><) \<star>\<^bsub>{}\<^sub>u\<^esub> ($1-tr - $tr\<^sub><) \<and>
    $st\<acute> =\<^sub>u ($st\<^sub>< \<oplus> $0-st on &ns1) \<oplus> $1-st on &ns2)"
  
text \<open> An intermediate merge hides the state, whilst a final merge hides the refusals. \<close>
  
definition CSPInterMerge where
[upred_defs]: "CSPInterMerge P ns1 cs ns2 Q = (P \<parallel>\<^bsub>(\<exists> $st\<acute> \<bullet> N\<^sub>C ns1 cs ns2)\<^esub> Q)"
  
definition CSPFinalMerge where
[upred_defs]: "CSPFinalMerge P ns1 cs ns2 Q = (P \<parallel>\<^bsub>(\<exists> $ref\<acute> \<bullet> N\<^sub>C ns1 cs ns2)\<^esub> Q)"
  
syntax
  "_cinter_merge" :: "logic \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> logic" ("_ \<lbrakk>_|_|_\<rbrakk>\<^sup>I _" [85,0,0,0,86] 86)
  "_cfinal_merge" :: "logic \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> logic" ("_ \<lbrakk>_|_|_\<rbrakk>\<^sup>F _" [85,0,0,0,86] 86)
  "_wrC" :: "logic \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> logic" ("_ wr[_|_|_]\<^sub>C _" [85,0,0,0,86] 86)

translations
  "_cinter_merge P ns1 cs ns2 Q" == "CONST CSPInterMerge P ns1 cs ns2 Q"
  "_cfinal_merge P ns1 cs ns2 Q" == "CONST CSPFinalMerge P ns1 cs ns2 Q"
  "_wrC P ns1 cs ns2 Q" == "P wr\<^sub>R(N\<^sub>C ns1 cs ns2) Q"

lemma CSPInnerMerge_R2m [closure]: "N\<^sub>C ns1 cs ns2 is R2m"
  by (rel_auto)

lemma CSPInnerMerge_RDM [closure]: "N\<^sub>C ns1 cs ns2 is RDM"
  by (rule RDM_intro, simp add: closure, simp_all add: CSPInnerMerge_def unrest)
    
lemma ex_ref'_R2m_closed [closure]: 
  assumes "P is R2m"
  shows "(\<exists> $ref\<acute> \<bullet> P) is R2m"
proof -
  have "R2m(\<exists> $ref\<acute> \<bullet> R2m P) = (\<exists> $ref\<acute> \<bullet> R2m P)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def' assms) 
qed
  
lemma CSPInnerMerge_unrests [unrest]: 
  "$ok\<^sub>< \<sharp> N\<^sub>C ns1 cs ns2"
  "$wait\<^sub>< \<sharp> N\<^sub>C ns1 cs ns2"
  by (rel_auto)+
    
lemma CSPInterMerge_RR_closed [closure]: 
  assumes "P is RR" "Q is RR"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I Q is RR"
  by (simp add: CSPInterMerge_def parallel_RR_closed assms closure unrest)

lemma CSPInterMerge_unrest_st' [unrest]:
  "$st\<acute> \<sharp> P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I Q"
  by (rel_auto)
    
lemma CSPFinalMerge_RR_closed [closure]: 
  assumes "P is RR" "Q is RR"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q is RR"
  by (simp add: CSPFinalMerge_def parallel_RR_closed assms closure unrest)
    
lemma CSPInnerMerge_empty_Interleave:
  "N\<^sub>C ns1 {} ns2 = N\<^sub>I ns1 ns2"
  by (rel_auto)

definition CSPMerge :: "('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> '\<psi> set \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> (('\<sigma>,'\<psi>) st_csp) merge" ("M\<^sub>C") where
[upred_defs]: "M\<^sub>C ns1 cs ns2 = M\<^sub>R(N\<^sub>C ns1 cs ns2) ;; Skip"

definition CSPInterleave :: "('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> (('\<sigma>,'\<psi>) st_csp) merge" ("M\<^sub>I") where
[upred_defs]: "M\<^sub>I ns1 ns2 = M\<^sub>R(N\<^sub>I ns1 ns2) ;; Skip"

lemma swap_CSPInnerMerge:
  "ns1 \<bowtie> ns2 \<Longrightarrow> swap\<^sub>m ;; (N\<^sub>C ns1 cs ns2) = (N\<^sub>C ns2 cs ns1)"
  apply (rel_auto)
  using tr_par_sym apply blast
  apply (simp add: lens_indep_comm)
  using tr_par_sym apply blast
  apply (simp add: lens_indep_comm)
done
    
lemma SymMerge_CSPInnerMerge_NS [closure]: "N\<^sub>C 0\<^sub>L cs 0\<^sub>L is SymMerge"
  by (simp add: Healthy_def swap_CSPInnerMerge)
                             
lemma SymMerge_CSPInnerInterleave [closure]:
  "N\<^sub>I 0\<^sub>L 0\<^sub>L is SymMerge"
  by (metis CSPInnerMerge_empty_Interleave SymMerge_CSPInnerMerge_NS)  
    
lemma SymMerge_CSPInnerInterleave [closure]:
  "AssocMerge (N\<^sub>I 0\<^sub>L 0\<^sub>L)"
  apply (rel_auto)
  apply (rename_tac tr tr\<^sub>2' ref\<^sub>0 tr\<^sub>0' ref\<^sub>0' tr\<^sub>1' ref\<^sub>1' tr' ref\<^sub>2' tr\<^sub>i' ref\<^sub>3')
oops
    
    
lemma CSPInterMerge_false [rpred]: "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I false = false"
  by (simp add: CSPInterMerge_def)

lemma CSPFinalMerge_false [rpred]: "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F false = false"
  by (simp add: CSPFinalMerge_def)
    
lemma CSPInterMerge_commute:
  assumes "ns1 \<bowtie> ns2"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I Q = Q \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>I P"
proof -
  have "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I Q = P \<parallel>\<^bsub>\<exists> $st\<acute> \<bullet> N\<^sub>C ns1 cs ns2\<^esub> Q"
    by (simp add: CSPInterMerge_def)
  also have "... = P \<parallel>\<^bsub>\<exists> $st\<acute> \<bullet> (swap\<^sub>m ;; N\<^sub>C ns2 cs ns1)\<^esub> Q"
    by (simp add: swap_CSPInnerMerge lens_indep_sym assms)
  also have "... = P \<parallel>\<^bsub>swap\<^sub>m ;; (\<exists> $st\<acute> \<bullet> N\<^sub>C ns2 cs ns1)\<^esub> Q"
    by (simp add: seqr_exists_right)
  also have "... = Q \<parallel>\<^bsub>(\<exists> $st\<acute> \<bullet> N\<^sub>C ns2 cs ns1)\<^esub> P"
    by (simp add: par_by_merge_commute_swap[THEN sym])
  also have "... = Q \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>I P"
    by (simp add: CSPInterMerge_def)
  finally show ?thesis .
qed

lemma CSPFinalMerge_commute:
  assumes "ns1 \<bowtie> ns2"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q = Q \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>F P"
proof -
  have "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q = P \<parallel>\<^bsub>\<exists> $ref\<acute> \<bullet> N\<^sub>C ns1 cs ns2\<^esub> Q"
    by (simp add: CSPFinalMerge_def)
  also have "... = P \<parallel>\<^bsub>\<exists> $ref\<acute> \<bullet> (swap\<^sub>m ;; N\<^sub>C ns2 cs ns1)\<^esub> Q"
    by (simp add: swap_CSPInnerMerge lens_indep_sym assms)
  also have "... = P \<parallel>\<^bsub>swap\<^sub>m ;; (\<exists> $ref\<acute> \<bullet> N\<^sub>C ns2 cs ns1)\<^esub> Q"
    by (simp add: seqr_exists_right)
  also have "... = Q \<parallel>\<^bsub>(\<exists> $ref\<acute> \<bullet> N\<^sub>C ns2 cs ns1)\<^esub> P"
    by (simp add: par_by_merge_commute_swap[THEN sym])
  also have "... = Q \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>F P"
    by (simp add: CSPFinalMerge_def)
  finally show ?thesis .
qed
  
text \<open> Important theorem that shows the form of a parallel process \<close>

lemma CSPInnerMerge_form:
  fixes P Q :: "('\<sigma>,'\<phi>) action"
  assumes "vwb_lens ns1" "vwb_lens ns2" "P is RR" "Q is RR" 
  shows
  "P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $ref\<acute> \<subseteq>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
  (is "?lhs = ?rhs")
proof -
  have P:"(\<exists> {$ok\<acute>,$wait\<acute>} \<bullet> R2(P)) = P" (is "?P' = _")
    by (simp add: ex_unrest ex_plus Healthy_if assms RR_implies_R2 unrest closure)
  have Q:"(\<exists> {$ok\<acute>,$wait\<acute>} \<bullet> R2(Q)) = Q" (is "?Q' = _")
    by (simp add: ex_unrest ex_plus Healthy_if assms RR_implies_R2 unrest closure)
  from assms(1,2)
  have "?P' \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> ?Q' = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             ?P'\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> ?Q'\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $ref\<acute> \<subseteq>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    apply (simp add: par_by_merge_alt_def, rel_auto, blast)
    apply (rename_tac ok wait tr st ref tr' ref' ref\<^sub>0 ref\<^sub>1 st\<^sub>0 st\<^sub>1 tr\<^sub>0 ok\<^sub>0 tr\<^sub>1 wait\<^sub>0 ok\<^sub>1 wait\<^sub>1)
    apply (rule_tac x="ok" in exI)
    apply (rule_tac x="wait" in exI)
    apply (rule_tac x="tr" in exI)      
    apply (rule_tac x="st" in exI)
    apply (rule_tac x="ref" in exI)
    apply (rule_tac x="tr @ tr\<^sub>0" in exI)      
    apply (rule_tac x="st\<^sub>0" in exI)
    apply (rule_tac x="ref\<^sub>0" in exI)      
    apply (auto)
    apply (metis Prefix_Order.prefixI append_minus)
  done      
  thus ?thesis
    by (simp add: P Q)
qed

lemma CSPInterMerge_form:
  fixes P Q :: "('\<sigma>,'\<phi>) action"
  assumes "vwb_lens ns1" "vwb_lens ns2" "P is RR" "Q is RR" 
  shows
  "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I Q = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $ref\<acute> \<subseteq>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<exists> $st\<acute> \<bullet> P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q)"
    by (simp add: CSPInterMerge_def par_by_merge_def seqr_exists_right)
  also have "... = 
      (\<exists> $st\<acute> \<bullet>
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $ref\<acute> \<subseteq>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2))"
    by (simp add: CSPInnerMerge_form assms)
  also have "... = ?rhs"
    by (rel_blast)
  finally show ?thesis .
qed
  
lemma CSPFinalMerge_form:
  fixes P Q :: "('\<sigma>,'\<phi>) action"
  assumes "vwb_lens ns1" "vwb_lens ns2" "P is RR" "Q is RR" "$ref\<acute> \<sharp> P" "$ref\<acute> \<sharp> Q"
  shows
  "(P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q) = 
        (\<^bold>\<exists> (st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             P\<lbrakk>\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
  (is "?lhs = ?rhs")  
proof -
  have "?lhs = (\<exists> $ref\<acute> \<bullet> P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q)"
    by (simp add: CSPFinalMerge_def par_by_merge_def seqr_exists_right)
  also have "... = 
      (\<exists> $ref\<acute> \<bullet>
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $ref\<acute> \<subseteq>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2))"
    by (simp add: CSPInnerMerge_form assms)
  also have "... = 
      (\<exists> $ref\<acute> \<bullet>
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             (\<exists> $ref\<acute> \<bullet> P)\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> (\<exists> $ref\<acute> \<bullet> Q)\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $ref\<acute> \<subseteq>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2))"
    by (simp add: ex_unrest assms)
  also have "... = 
        (\<^bold>\<exists> (st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             (\<exists> $ref\<acute> \<bullet> P)\<lbrakk>\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> (\<exists> $ref\<acute> \<bullet> Q)\<lbrakk>\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (rel_blast)
  also have "... = ?rhs"
    by (simp add: ex_unrest assms)
  finally show ?thesis .
qed

lemma merge_csp_do_left:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR"
  shows "\<Phi>(s\<^sub>0,\<sigma>\<^sub>0,t\<^sub>0) \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> P = 
     (\<^bold>\<exists> (ref\<^sub>1, st\<^sub>1, tt\<^sub>1) \<bullet> 
        [s\<^sub>0]\<^sub>S\<^sub>< \<and>
        [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> P \<and>
        $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
        [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>0 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> t\<^sub>0 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
        $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>\<sigma>\<^sub>0\<guillemotright>($st)\<^sub>a on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
     (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
        [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<Phi>(s\<^sub>0,\<sigma>\<^sub>0,t\<^sub>0) \<and>
        [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> P \<and>
        $ref\<acute> \<subseteq>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
        $tr \<le>\<^sub>u $tr\<acute> \<and>
        &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and> $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (simp add: CSPInnerMerge_form assms closure)
  also have "... =
     (\<^bold>\<exists> (ref\<^sub>1, st\<^sub>1, tt\<^sub>1) \<bullet> 
        [s\<^sub>0]\<^sub>S\<^sub>< \<and>
        [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> P \<and>
        $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
        [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>0 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> t\<^sub>0 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
        $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>\<sigma>\<^sub>0\<guillemotright>($st)\<^sub>a on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (rel_blast)
  finally show ?thesis .
qed

lemma merge_csp_do_right:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR"
  shows "P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) = 
     (\<^bold>\<exists> (ref\<^sub>0, st\<^sub>0, tt\<^sub>0) \<bullet> 
        [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> P \<and>
        [s\<^sub>1]\<^sub>S\<^sub>< \<and>
        $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
        [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>1 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
        $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>\<sigma>\<^sub>1\<guillemotright>($st)\<^sub>a on &ns2 )"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
    (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> P \<and>
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<and>
             $ref\<acute> \<subseteq>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             $tr \<le>\<^sub>u $tr\<acute> \<and>
             &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and> $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (simp add: CSPInnerMerge_form assms closure)
  also have "... = ?rhs"
    by (rel_blast)
  finally show ?thesis .
qed 
  
text \<open> The result of merge two terminated stateful traces is to (1) require both state preconditions
  hold, (2) merge the traces using, and (3) merge the state using a parallel assignment. \<close>

lemma FinalMerge_csp_do_left:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR" "$ref\<acute> \<sharp> P"
  shows "\<Phi>(s\<^sub>0,\<sigma>\<^sub>0,t\<^sub>0) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F P =         
         (\<^bold>\<exists> (st\<^sub>1, t\<^sub>1) \<bullet> 
             [s\<^sub>0]\<^sub>S\<^sub>< \<and>
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>] \<dagger> P \<and>
             [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>0 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>t\<^sub>1\<guillemotright> \<and> t\<^sub>0 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>t\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
             $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>\<sigma>\<^sub>0\<guillemotright>($st)\<^sub>a on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<^bold>\<exists> (st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<Phi>(s\<^sub>0,\<sigma>\<^sub>0,t\<^sub>0) \<and>
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> RR(\<exists> $ref\<acute> \<bullet> P) \<and>
             $tr \<le>\<^sub>u $tr\<acute> \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and> 
             $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (simp add: CSPFinalMerge_form ex_unrest Healthy_if unrest closure assms)
  also have "... = 
        (\<^bold>\<exists> (st\<^sub>1, tt\<^sub>1) \<bullet> 
             [s\<^sub>0]\<^sub>S\<^sub>< \<and>
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> RR(\<exists> $ref\<acute> \<bullet> P) \<and>
             [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>0 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> t\<^sub>0 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
             $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>\<sigma>\<^sub>0\<guillemotright>($st)\<^sub>a on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (rel_blast)
  also have "... = 
        (\<^bold>\<exists> (st\<^sub>1, t\<^sub>1) \<bullet> 
             [s\<^sub>0]\<^sub>S\<^sub>< \<and>
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>1\<guillemotright>] \<dagger> P \<and>
             [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>0 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>t\<^sub>1\<guillemotright> \<and> t\<^sub>0 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>t\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
             $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>\<sigma>\<^sub>0\<guillemotright>($st)\<^sub>a on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (simp add: ex_unrest Healthy_if unrest closure assms)
  finally show ?thesis .
qed
      
lemma FinalMerge_csp_do_right:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR" "$ref\<acute> \<sharp> P"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) =         
         (\<^bold>\<exists> (st\<^sub>0, t\<^sub>0) \<bullet> 
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> P \<and>
             [s\<^sub>1]\<^sub>S\<^sub>< \<and>
             [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>1 \<and> \<guillemotleft>t\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
             $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>\<sigma>\<^sub>1\<guillemotright>($st)\<^sub>a on &ns2)"
  (is "?lhs = ?rhs")
proof -
  have "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) = \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>F P"
    by (simp add: assms CSPFinalMerge_commute)
  also have "... = ?rhs"
    apply (simp add: FinalMerge_csp_do_left assms lens_indep_sym conj_comm)
    apply (rel_auto)
    using assms(3) lens_indep.lens_put_comm tr_par_sym apply fastforce+
  done
  finally show ?thesis .
qed
  
lemma FinalMerge_csp_do:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) = 
         ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and> [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> [\<langle>\<sigma>\<^sub>1 [&ns1|&ns2]\<^sub>s \<sigma>\<^sub>2\<rangle>\<^sub>a]\<^sub>S')" 
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<^bold>\<exists> (st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<and>
             [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) \<and>
             $tr \<le>\<^sub>u $tr\<acute> \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and> 
             $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (simp add: CSPFinalMerge_form unrest closure assms)
  also have "... = 
        ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and> [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> [\<langle>\<sigma>\<^sub>1 [&ns1|&ns2]\<^sub>s \<sigma>\<^sub>2\<rangle>\<^sub>a]\<^sub>S')"
    by (rel_auto)
  finally show ?thesis .
qed

lemma FinalMerge_csp_do' [rpred]:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) = 
         (\<Sqinter> trace | \<guillemotleft>trace\<guillemotright> \<in>\<^sub>u \<lceil>t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2\<rceil>\<^sub>S\<^sub>< \<bullet>
                    \<Phi>(s\<^sub>1 \<and> s\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>, \<sigma>\<^sub>1 [&ns1|&ns2]\<^sub>s \<sigma>\<^sub>2, \<guillemotleft>trace\<guillemotright>))"
  by (simp add: FinalMerge_csp_do assms, rel_auto)

lemma InterMerge_csp_enable:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) = 
          ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and>
           (\<^bold>\<forall> e\<in>\<lceil>(E\<^sub>1 \<inter>\<^sub>u E\<^sub>2 \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((E\<^sub>1 \<union>\<^sub>u E\<^sub>2) - \<guillemotleft>cs\<guillemotright>)\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<and>
           [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t)" 
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<and>
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) \<and>
             $ref\<acute> \<subseteq>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             $tr \<le>\<^sub>u $tr\<acute> \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>)"
    by (simp add: CSPInterMerge_form unrest closure assms)
  also have "... = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<and>
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) \<and>
             $ref\<acute> \<subseteq>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             $tr \<le>\<^sub>u $tr\<acute> \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>)"
    by (rel_auto)
  also have "... = 
        ( [s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and>
          (\<^bold>\<forall> e\<in>\<lceil>(E\<^sub>1 \<inter>\<^sub>u E\<^sub>2 \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((E\<^sub>1 \<union>\<^sub>u E\<^sub>2) - \<guillemotleft>cs\<guillemotright>)\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<and>
          [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t
         )"  
    apply (rel_auto)
    apply (rename_tac tr st tr' ref')
    apply (rule_tac x="- \<lbrakk>E\<^sub>1\<rbrakk>\<^sub>e st" in exI)
    apply (simp)
    apply (rule_tac x="- \<lbrakk>E\<^sub>2\<rbrakk>\<^sub>e st" in exI)
    apply (auto)
  done
  finally show ?thesis .
qed

lemma InterMerge_csp_enable':
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) = 
          (\<Sqinter> trace | \<guillemotleft>trace\<guillemotright> \<in>\<^sub>u \<lceil>t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2\<rceil>\<^sub>S\<^sub>< \<bullet>
                     \<E>( s\<^sub>1 \<and> s\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
                      , \<guillemotleft>trace\<guillemotright>
                      , (E\<^sub>1 \<inter>\<^sub>u E\<^sub>2 \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((E\<^sub>1 \<union>\<^sub>u E\<^sub>2) - \<guillemotleft>cs\<guillemotright>)))"
  by (simp add: InterMerge_csp_enable assms, rel_auto)

lemma InterMerge_csp_enable_csp_do:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) = 
           ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and> (\<^bold>\<forall> e\<in>\<lceil>(E\<^sub>1 - \<guillemotleft>cs\<guillemotright>)\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<and>
           [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t)" 
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<and>
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) \<and>
             $ref\<acute> \<subseteq>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             $tr \<le>\<^sub>u $tr\<acute> \<and> &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>)"
    by (simp add: CSPInterMerge_form unrest closure assms)
  also have "... = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, tt\<^sub>0) \<bullet> 
             [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<and>
             [s\<^sub>2]\<^sub>S\<^sub>< \<and>
             $ref\<acute> \<subseteq>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t)"
    by (rel_auto) 
  also have "... = ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and> (\<^bold>\<forall> e\<in>\<lceil>(E\<^sub>1 - \<guillemotleft>cs\<guillemotright>)\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<and>
                    [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t)"
    by (rel_auto) 
  finally show ?thesis .
qed

lemma InterMerge_csp_enable_csp_do' [rpred]:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) =
         (\<Sqinter> trace | \<guillemotleft>trace\<guillemotright> \<in>\<^sub>u \<lceil>t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2\<rceil>\<^sub>S\<^sub>< \<bullet>
                     \<E>(s\<^sub>1 \<and> s\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>, \<guillemotleft>trace\<guillemotright>, E\<^sub>1 - \<guillemotleft>cs\<guillemotright>))"
  by (simp add: InterMerge_csp_enable_csp_do assms, rel_auto)

lemma InterMerge_csp_do_csp_enable:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) = 
           ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and> (\<^bold>\<forall> e\<in>\<lceil>(E\<^sub>2 - \<guillemotleft>cs\<guillemotright>)\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<acute>) \<and>
           [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t)" 
  (is "?lhs = ?rhs")
proof -
  have "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) = \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>I \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1)"
    by (simp add: CSPInterMerge_commute assms)
  also have "... = ?rhs"
    by (simp add: InterMerge_csp_enable_csp_do assms lens_indep_sym trace_merge_commute conj_comm eq_upred_sym)
  finally show ?thesis .
qed

lemma InterMerge_csp_do_csp_enable' [rpred]:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) =
         (\<Sqinter> trace | \<guillemotleft>trace\<guillemotright> \<in>\<^sub>u \<lceil>t\<^sub>1 \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>2\<rceil>\<^sub>S\<^sub>< \<bullet> 
                     \<E>(s\<^sub>1 \<and> s\<^sub>2 \<and> t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>2 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>, \<guillemotleft>trace\<guillemotright>, E\<^sub>2 - \<guillemotleft>cs\<guillemotright>))" 
  by (simp add: InterMerge_csp_do_csp_enable assms, rel_auto)

lemma CSPInterMerge_or_left [rpred]: 
  "(P \<or> Q) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I R = (P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I R \<or> Q \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I R)"
  by (simp add: CSPInterMerge_def par_by_merge_or_left)

lemma CSPInterMerge_or_right [rpred]:
  "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q \<or> R) = (P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I Q \<or> P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I R)"
  by (simp add: CSPInterMerge_def par_by_merge_or_right)

lemma par_by_merge_seq_remove: "(P \<parallel>\<^bsub>M ;; R\<^esub> Q) = (P \<parallel>\<^bsub>M\<^esub> Q) ;; R"
  by (simp add: par_by_merge_seq_add[THEN sym])
  
lemma merge_csp_do_right:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RC"
  shows "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) wr[ns1|cs|ns2]\<^sub>C P = undefined"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<not>\<^sub>r (\<^bold>\<exists> (ref\<^sub>0, st\<^sub>0, tt\<^sub>0) \<bullet> 
              [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> (\<not>\<^sub>r RC(P)) \<and>
              [s\<^sub>1]\<^sub>S\<^sub>< \<and>
              $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
              [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>1 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
              $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>\<sigma>\<^sub>1\<guillemotright>($st)\<^sub>a on &ns2) ;; R1 true)"
    by (simp add: wrR_def par_by_merge_seq_remove merge_csp_do_right closure assms Healthy_if rpred)
 also have "... =
        (\<not>\<^sub>r (\<^bold>\<exists> (ref\<^sub>0, st\<^sub>0, tt\<^sub>0) \<bullet> 
              [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> (\<not>\<^sub>r RC(P)) \<and>
              [s\<^sub>1]\<^sub>S\<^sub>< \<and>
              $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
              [\<guillemotleft>trace\<guillemotright> \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> t\<^sub>1 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u t\<^sub>1 \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>]\<^sub>t ;; true\<^sub>r \<and> 
              $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>\<sigma>\<^sub>1\<guillemotright>($st)\<^sub>a on &ns2))"
   apply (rel_auto)


oops

subsection \<open> Parallel operator \<close>

syntax
  "_par_circus"   :: "logic \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> logic"  ("_ \<lbrakk>_\<parallel>_\<parallel>_\<rbrakk> _" [75,0,0,0,76] 76)
  "_par_csp"      :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<lbrakk>_\<rbrakk>\<^sub>C _" [75,0,76] 76)
  "_inter_circus" :: "logic \<Rightarrow> salpha \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> logic"  ("_ \<lbrakk>_\<parallel>_\<rbrakk> _" [75,0,0,76] 76)
  "_inter_csp"    :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr "|||" 75)
    
translations
  "_par_circus P ns1 cs ns2 Q" == "P \<parallel>\<^bsub>M\<^sub>C ns1 cs ns2\<^esub> Q"
  "_par_csp P cs Q" == "_par_circus P 0\<^sub>L cs 0\<^sub>L Q"
  "_inter_circus P ns1 ns2 Q" == "_par_circus P ns1 {} ns2 Q"
  "_inter_csp P Q" == "_par_csp P {} Q"
  
definition CSP5 :: "('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "CSP5(P) = (P ||| Skip)"

definition C2 :: "('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "C2(P) = (P \<lbrakk>\<Sigma>\<parallel>{}\<parallel>\<emptyset>\<rbrakk> Skip)"

lemma Skip_right_form:
  assumes "P\<^sub>1 is RC" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "$st\<acute> \<sharp> P\<^sub>2"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) ;; Skip = \<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> (\<exists> $ref\<acute> \<bullet> P\<^sub>3))"
proof -
  have 1:"RR(P\<^sub>3) ;; \<Phi>(true,id,\<langle>\<rangle>) = (\<exists> $ref\<acute> \<bullet> RR(P\<^sub>3))"
    by (rel_auto)
  show ?thesis
    by (rdes_simp cls: assms, metis "1" Healthy_if assms(3))
qed
  
lemma ParCSP_rdes_def [rdes_def]:
  fixes P\<^sub>1 :: "('s,'e) action"
  assumes "P\<^sub>1 is CRC" "Q\<^sub>1 is CRC" "P\<^sub>2 is CRR" "Q\<^sub>2 is CRR" "P\<^sub>3 is CRR" "Q\<^sub>3 is CRR" 
          "$st\<acute> \<sharp> P\<^sub>2" "$st\<acute> \<sharp> Q\<^sub>2" 
          "ns1 \<bowtie> ns2"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) = 
         \<^bold>R\<^sub>s (((Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and>
              (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and> 
              (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1 \<and> 
              (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1) \<turnstile>
             ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or>
              (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or> 
              (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)) \<diamondop>
             ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)))"
  (is "?P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> ?Q = ?rhs")
proof -
  have "?P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> ?Q = (?P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> ?Q) ;;\<^sub>h Skip"
    by (simp add: CSPMerge_def par_by_merge_seq_add)
  also 
  have "... =  \<^bold>R\<^sub>s (((Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and>
                    (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1) \<turnstile>
                    ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or>
                     (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or> 
                     (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)) \<diamondop>
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)) ;;\<^sub>h Skip"
    by (simp add: parallel_rdes_def swap_CSPInnerMerge CSPInterMerge_def closure assms)
  also 
  have "... =  \<^bold>R\<^sub>s (((Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and>
                    (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1) \<turnstile>
                    ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or>
                     (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or> 
                     (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)) \<diamondop>
                    (\<exists> $ref\<acute> \<bullet> ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3))))"
     by (simp add: Skip_right_form  closure parallel_RR_closed assms unrest)
  also
  have "... =  \<^bold>R\<^sub>s (((Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and>
                    (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3) wr[ns1|cs|ns2]\<^sub>C P\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) wr[ns2|cs|ns1]\<^sub>C Q\<^sub>1) \<turnstile>
                    ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or>
                     (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) \<or> 
                     (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>I (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)) \<diamondop>
                    ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)))"
  proof -
    have "(\<exists> $ref\<acute> \<bullet> ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3))) = ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3))"
      by (rel_blast)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed
       
subsection {* Parallel Laws *}

lemma ParCSP_expand:
  "P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q = (P \<parallel>\<^sub>R\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q) ;; Skip"
  by (simp add: CSPMerge_def par_by_merge_seq_add)
    
lemma parallel_is_CSP [closure]:
  assumes "P is CSP" "Q is CSP"
  shows "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) is CSP"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> Q) is CSP"
    by (simp add: closure assms)
  hence "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> Q) ;; Skip is CSP"
    by (simp add: closure)
  thus ?thesis
    by (simp add: CSPMerge_def par_by_merge_seq_add)
qed  
      
lemma parallel_is_CSP3 [closure]:
  assumes "P is CSP" "P is CSP3" "Q is CSP" "Q is CSP3"
  shows "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) is CSP3"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> Q) is CSP"
    by (simp add: closure assms)
  hence "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> Q) ;; Skip is CSP"
    by (simp add: closure)
  thus ?thesis
    oops

theorem parallel_commutative:
  assumes "ns1 \<bowtie> ns2"
  shows "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) = (Q \<lbrakk>ns2\<parallel>cs\<parallel>ns1\<rbrakk> P)"
proof -
  have "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) = P \<parallel>\<^bsub>swap\<^sub>m ;; (M\<^sub>C ns2 cs ns1)\<^esub> Q"
    by (simp add: CSPMerge_def seqr_assoc[THEN sym] swap_merge_rd swap_CSPInnerMerge lens_indep_sym assms)
  also have "... = Q \<lbrakk>ns2\<parallel>cs\<parallel>ns1\<rbrakk> P"
    by (metis par_by_merge_commute_swap)
  finally show ?thesis .
qed

lemma interleave_commute:
  "P ||| Q = Q ||| P"
  using parallel_commutative zero_lens_indep by blast

text {* The form of C2 tells us that a normal CSP process has a downward closed set of refusals *}
  
lemma C2_form:
  assumes "P is NCSP"
  shows "C2(P) = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> (\<^bold>\<exists> ref\<^sub>0 \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) \<diamondop> post\<^sub>R P)"
proof -
  have 1:"\<Phi>(true,id,\<langle>\<rangle>) wr[\<Sigma>|{}|\<emptyset>]\<^sub>C pre\<^sub>R P = pre\<^sub>R P" (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<not>\<^sub>r (\<^bold>\<exists> (ref\<^sub>0, st\<^sub>0, tt\<^sub>0) \<bullet> 
                   [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> (\<exists> $ref\<acute>;$st\<acute> \<bullet> RR(\<not>\<^sub>r pre\<^sub>R P)) \<and>
                    $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright> \<and> [\<guillemotleft>trace\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>]\<^sub>t \<and> 
                    $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on \<Sigma> \<oplus> \<guillemotleft>id\<guillemotright>($st)\<^sub>a on \<emptyset>) ;; R1 true)"
      by (simp add: wrR_def par_by_merge_seq_remove rpred merge_csp_do_right ex_unrest Healthy_if pr_var_def closure assms unrest usubst)
    also have "... = (\<not>\<^sub>r (\<exists> $ref\<acute>;$st\<acute> \<bullet> RR(\<not>\<^sub>r pre\<^sub>R P)) ;; R1 true)"
      by (rel_auto)
    also have "... = (\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P) ;; R1 true)"
      by (simp add: Healthy_if closure ex_unrest unrest assms)
    also have "... = pre\<^sub>R P"
      by (simp add: NCSP_implies_NSRD NSRD_neg_pre_unit R1_preR assms rea_not_not)
    finally show ?thesis .
  qed
  have 2: "(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<lbrakk>\<Sigma>|{}|\<emptyset>\<rbrakk>\<^sup>I \<Phi>(true,id,\<langle>\<rangle>) = 
           (\<^bold>\<exists> ref\<^sub>0 \<bullet> (peri\<^sub>R P)\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = peri\<^sub>R P \<lbrakk>\<Sigma>|{}|\<emptyset>\<rbrakk>\<^sup>I \<Phi>(true,id,\<langle>\<rangle>)"
      by (simp add: SRD_peri_under_pre closure assms unrest)
    also have "... = (\<exists> $st\<acute> \<bullet> (peri\<^sub>R P \<parallel>\<^bsub> N\<^sub>C 1\<^sub>L {} 0\<^sub>L\<^esub> \<Phi>(true,id,\<langle>\<rangle>)))"
      by (simp add: CSPInterMerge_def par_by_merge_def seqr_exists_right)
    also have "... = 
         (\<exists> $st\<acute> \<bullet> \<^bold>\<exists> (ref\<^sub>0, st\<^sub>0, tt\<^sub>0) \<bullet> 
            [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> (\<exists> $st\<acute> \<bullet> RR(peri\<^sub>R P)) \<and>
             $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright> \<and> [\<guillemotleft>trace\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>]\<^sub>t \<and> $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on \<Sigma> \<oplus> \<guillemotleft>id\<guillemotright>($st)\<^sub>a on \<emptyset>)"
      by (simp add: merge_csp_do_right pr_var_def assms Healthy_if assms closure rpred unrest ex_unrest)
    also have "... = 
         (\<^bold>\<exists> ref\<^sub>0 \<bullet> (\<exists> $st\<acute> \<bullet> RR(peri\<^sub>R P))\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>)"
      by (rel_auto)
    also have "... = ?rhs"
      by (simp add: closure ex_unrest Healthy_if unrest assms)
    finally show ?thesis .
  qed
  have 3: "(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) \<lbrakk>\<Sigma>|{}|\<emptyset>\<rbrakk>\<^sup>F \<Phi>(true,id,\<langle>\<rangle>) = post\<^sub>R(P)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = post\<^sub>R P \<lbrakk>\<Sigma>|{}|\<emptyset>\<rbrakk>\<^sup>F \<Phi>(true,id,\<langle>\<rangle>)"
      by (simp add: SRD_post_under_pre closure assms unrest)
    also have "... = (\<^bold>\<exists> (st\<^sub>0, t\<^sub>0) \<bullet> 
                        [$st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> RR(post\<^sub>R P) \<and>
                        [\<guillemotleft>trace\<guillemotright> =\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright>]\<^sub>t \<and> $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on \<Sigma> \<oplus> \<guillemotleft>id\<guillemotright>($st)\<^sub>a on \<emptyset>)"
      by (simp add: FinalMerge_csp_do_right pr_var_def assms closure unrest rpred Healthy_if)
    also have "... = RR(post\<^sub>R(P))"
      by (rel_auto)
    finally show ?thesis
      by (simp add: Healthy_if assms closure)
  qed
  show ?thesis
  proof -
    have "C2(P) = \<^bold>R\<^sub>s (\<Phi>(true,id,\<langle>\<rangle>) wr[\<Sigma>|{}|\<emptyset>]\<^sub>C pre\<^sub>R P \<turnstile>
          (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<lbrakk>\<Sigma>|{}|\<emptyset>\<rbrakk>\<^sup>I \<Phi>(true,id,\<langle>\<rangle>) \<diamondop> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) \<lbrakk>\<Sigma>|{}|\<emptyset>\<rbrakk>\<^sup>F \<Phi>(true,id,\<langle>\<rangle>))"
      by (simp add: C2_def, rdes_simp cls: assms, simp add: id_def pr_var_def)
    also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> (\<^bold>\<exists> ref\<^sub>0 \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) \<diamondop> post\<^sub>R P)"
      by (simp add: 1 2 3)
    finally show ?thesis .
  qed
qed

lemma Skip_C2_closed [closure]: 
  "Skip is C2"
  apply (simp add: Healthy_def C2_form)
  apply (simp add: C2_form closure rdes usubst)
  apply (simp add: rdes_def)
done
  
lemma ref_down_CRR [closure]:
  assumes "P is NCSP"
  shows "(\<^bold>\<exists> ref\<^sub>0 \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) is CRR"
proof -
  have "(\<^bold>\<exists> ref\<^sub>0 \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) = 
        (\<^bold>\<exists> ref\<^sub>0 \<bullet> (CRR(peri\<^sub>R P))\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>)"
    by (simp add: Healthy_if assms closure)
  also have "... = CRR(\<^bold>\<exists> ref\<^sub>0 \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>)"
    by (rel_auto)
  finally show ?thesis
    by (simp add: Healthy_def')
qed
  
lemma C2_idem: 
  assumes "P is NCSP"
  shows "C2(C2(P)) = C2(P)" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> (\<^bold>\<exists> ref\<^sub>0 \<bullet> (pre\<^sub>R P \<Rightarrow>\<^sub>r (\<^bold>\<exists> ref\<^sub>0' \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0'\<guillemotright>/$ref\<acute>\<rbrakk> \<and> \<guillemotleft>ref\<^sub>0\<guillemotright> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0'\<guillemotright>)) \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) \<diamondop> post\<^sub>R P)"
    by (simp add: C2_form closure unrest rdes SRD_post_under_pre SRD_peri_under_pre usubst NCSP_rdes_intro assms)
  also have 
    "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> (\<^bold>\<exists> ref\<^sub>0 \<bullet> (\<^bold>\<exists> ref\<^sub>0' \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0'\<guillemotright>/$ref\<acute>\<rbrakk> \<and> \<guillemotleft>ref\<^sub>0\<guillemotright> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0'\<guillemotright>) \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) \<diamondop> post\<^sub>R P)"
     by (rel_auto)
  also have 
    "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> (\<^bold>\<exists> ref\<^sub>0 \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) \<diamondop> post\<^sub>R P)"
    by (rel_auto)
  also have "... = C2(P)"
    by (simp add: C2_form closure unrest assms)
  finally show ?thesis .
qed  
  
lemma Stop_C2_closed [closure]: 
  "Stop is C2"
  apply (simp add: Healthy_def C2_form)
  apply (simp add: C2_form closure rdes usubst)
  apply (rel_auto)
done

lemma Miracle_C2_closed [closure]: 
  "Miracle is C2"
  apply (simp add: Healthy_def C2_form)
  apply (simp add: C2_form closure rdes usubst)
  apply (simp add: rdes_def)
done

lemma Chaos_C2_closed [closure]: 
  "Chaos is C2"
  apply (simp add: Healthy_def C2_form)
  apply (simp add: C2_form closure rdes usubst unrest)
  apply (simp add: rdes_def)
  apply (rel_auto)
done
  
(* An attempt at proving that the precondition of Chaos is false *)
  
lemma 
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR"
  shows "P wr[ns1|cs|ns2]\<^sub>C false = undefined" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<not>\<^sub>r (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
                   [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>0\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>0\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> R1 true \<and>
                   [$ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>ref\<^sub>1\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>st\<^sub>1\<guillemotright>, $tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> P \<and>
                   $ref\<acute> \<subseteq>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright> \<union>\<^sub>u (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
                   $tr \<le>\<^sub>u $tr\<acute> \<and>
                   &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and> 
                   $st\<acute> =\<^sub>u $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2) ;;
                    R1 true)"
    by (simp add: wrR_def par_by_merge_seq_remove CSPInnerMerge_form assms closure usubst unrest)
  also have "... = (\<not>\<^sub>r (\<^bold>\<exists> (tt\<^sub>0, tt\<^sub>1) \<bullet>                    
                   [$tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> P \<and>
                   $tr \<le>\<^sub>u $tr\<acute> \<and>
                   &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>) ;;
                    R1 true)"
    by (rel_blast)  
  also have "... = (\<not>\<^sub>r (\<^bold>\<exists> (tt\<^sub>0, tt\<^sub>1) \<bullet>                    
                   [$tr \<mapsto>\<^sub>s \<langle>\<rangle>, $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> RR(P) \<and>
                   $tr \<le>\<^sub>u $tr\<acute> \<and>
                   &tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>) ;;
                    R1 true)"
    by (simp add: Healthy_if assms)
  oops

end