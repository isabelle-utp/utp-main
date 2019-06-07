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
[upred_defs]: "block_open a = \<langle>ext\<^sub>s a\<rangle>\<^sub>a"

definition block_close :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('b, 'a) urel" ("close\<^bsub>_\<^esub>") where
[upred_defs]: "block_close a = \<langle>con\<^sub>s a\<rangle>\<^sub>a"

lemma block_open_close:
  "mwb_lens a \<Longrightarrow> open\<^bsub>a\<^esub> ;; close\<^bsub>a\<^esub> = II"
  by (rel_simp)

lemma block_assigns_open:
  "mwb_lens a \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>a ;; open\<^bsub>a\<^esub> = open\<^bsub>a\<^esub> ;; \<langle>\<sigma> \<oplus>\<^sub>s a\<rangle>\<^sub>a"
  by (rel_simp)

end