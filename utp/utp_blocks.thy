section \<open> Blocks \<close>

theory utp_blocks
  imports utp_rel_laws
begin

subsection \<open> Extending and Contracting Substitutions \<close>

definition subst_ext :: "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<alpha>, '\<beta>) psubst" ("ext\<^sub>s") where
[upred_defs]: "ext\<^sub>s a = \<lparr>\<^bold>v \<mapsto>\<^sub>s &\<^bold>v \<restriction>\<^sub>e a\<rparr>"

definition subst_con :: "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<beta>, '\<alpha>) psubst" ("con\<^sub>s") where
[upred_defs]: "con\<^sub>s a = \<lparr>\<^bold>v \<mapsto>\<^sub>s &\<^bold>v \<oplus>\<^sub>p a\<rparr>"

lemma subst_res_ext_con: "\<sigma> \<restriction>\<^sub>s a = con\<^sub>s a \<circ> \<sigma> \<circ> ext\<^sub>s a"
  by (rel_simp)

lemma subst_ext_con [usubst]: "mwb_lens a \<Longrightarrow> con\<^sub>s a \<circ> ext\<^sub>s a = id"
  by (rel_simp)

lemma subst_con_update_sublens [usubst]: 
  "\<lbrakk> mwb_lens a; x \<subseteq>\<^sub>L a \<rbrakk> \<Longrightarrow> con\<^sub>s a \<circ> subst_upd \<sigma> x v = subst_upd (con\<^sub>s a \<circ> \<sigma>) (x /\<^sub>L a) v"
  by (simp add: subst_con_def usubst alpha, rel_simp)

lemma subst_con_update_indep [usubst]: 
  "\<lbrakk> mwb_lens x; mwb_lens a; a \<bowtie> x \<rbrakk> \<Longrightarrow> con\<^sub>s a \<circ> subst_upd \<sigma> x v = (con\<^sub>s a \<circ> \<sigma>)"
  by (simp add: subst_con_def usubst alpha)

lemma subst_ext_apply [usubst]: "\<langle>ext\<^sub>s a\<rangle>\<^sub>s x = &x \<restriction>\<^sub>e a"
  by (rel_simp)

subsection \<open> Generic Blocks \<close>

definition block_open :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('a, 'b) urel" ("open\<^bsub>_\<^esub>") where
[upred_defs]: "block_open a = \<langle>ext\<^sub>s a\<rangle>\<^sub>a ;; ($a\<acute> =\<^sub>u $a)"

definition block_close :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('b, 'a) urel" ("close\<^bsub>_\<^esub>") where
[upred_defs]: "block_close a = \<langle>con\<^sub>s a\<rangle>\<^sub>a"

lemma block_open_conv: 
  "mwb_lens a \<Longrightarrow> open\<^bsub>a\<^esub>\<^sup>- = close\<^bsub>a\<^esub>"
  by (rel_auto)

lemma block_open_close:
  "mwb_lens a \<Longrightarrow> open\<^bsub>a\<^esub> ;; close\<^bsub>a\<^esub> = II"
  by (rel_auto, metis mwb_lens_def weak_lens.create_get)

lemma block_open_open:
  "\<lbrakk> mwb_lens a; mwb_lens b\<rbrakk> \<Longrightarrow> open\<^bsub>a\<^esub> ;; open\<^bsub>b\<^esub> = open\<^bsub>a ;\<^sub>L b\<^esub>"
  by (rel_auto)

lemma block_close_close:
  "\<lbrakk> mwb_lens a; mwb_lens b\<rbrakk> \<Longrightarrow> close\<^bsub>a\<^esub> ;; close\<^bsub>b\<^esub> = close\<^bsub>b ;\<^sub>L a\<^esub>"
  by (rel_auto)

lemma block_assigns_open:
  "vwb_lens a \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>a ;; open\<^bsub>a\<^esub> = open\<^bsub>a\<^esub> ;; \<langle>\<sigma> \<oplus>\<^sub>s a\<rangle>\<^sub>a"
  by (rel_auto, metis lens_override_def lens_override_idem mwb_lens_axioms_def mwb_lens_def vwb_lens_def weak_lens.put_get)

lemma block_assign_local_close:
  "a \<bowtie> x \<Longrightarrow> x := v ;; close\<^bsub>a\<^esub> = close\<^bsub>a\<^esub>"
  by (rel_auto)

end