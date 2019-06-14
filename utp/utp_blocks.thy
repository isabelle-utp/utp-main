section \<open> Blocks (Abstract Local Variables) \<close>

theory utp_blocks
  imports utp_rel_laws
begin

syntax
  "_slens_view" :: "logic \<Rightarrow> svid" ("\<V>[_]")

translations
  "_slens_view a" => "\<V>\<^bsub>a\<^esub>"

subsection \<open> Extending and Contracting Substitutions \<close>

definition subst_ext :: "(<'\<alpha>, '\<beta>> \<Longleftrightarrow> '\<gamma>) \<Rightarrow> ('\<alpha>, '\<gamma>) psubst" ("ext\<^sub>s") where
"ext\<^sub>s a = (\<lambda> s. create\<^bsub>\<V>\<^bsub>a\<^esub>\<^esub> s)" \<comment> \<open> Extend state space by execution of create \<close>

lemma subst_ext_alt_def [upred_defs]: "ext\<^sub>s a = \<lparr>\<^bold>v \<mapsto>\<^sub>s &\<^bold>v \<restriction>\<^sub>e \<V>\<^bsub>a\<^esub>\<rparr>"
  unfolding subst_ext_def by (rel_auto)

definition subst_con :: "(<'\<alpha>, '\<beta>> \<Longleftrightarrow> '\<gamma>) \<Rightarrow> ('\<gamma>, '\<alpha>) psubst" ("con\<^sub>s") where
"con\<^sub>s a = (\<lambda> s. get\<^bsub>\<V>\<^bsub>a\<^esub>\<^esub> s)" \<comment> \<open> Contract the state space with get \<close>

lemma subst_con_alt_def [upred_defs]: "con\<^sub>s a = \<lparr>\<^bold>v \<mapsto>\<^sub>s &\<^bold>v \<oplus>\<^sub>p \<V>\<^bsub>a\<^esub>\<rparr>"
  unfolding subst_con_def by (rel_auto)

lemma subst_res_ext_con: "\<sigma> \<restriction>\<^sub>s (\<V>\<^bsub>a\<^esub>) = con\<^sub>s a \<circ> \<sigma> \<circ> ext\<^sub>s a"
  by (rel_simp)

lemma subst_ext_con [usubst]: "psym_lens a \<Longrightarrow> con\<^sub>s a \<circ> ext\<^sub>s a = id"
  by (rel_simp)

text \<open> Variables in the "global" state space will be retained after a state is contracted \<close>

lemma subst_con_update_sublens [usubst]: 
  "\<lbrakk> psym_lens a; x \<subseteq>\<^sub>L \<V>\<^bsub>a\<^esub> \<rbrakk> \<Longrightarrow> con\<^sub>s a \<circ> subst_upd \<sigma> x v = subst_upd (con\<^sub>s a \<circ> \<sigma>) (x /\<^sub>L \<V>\<^bsub>a\<^esub>) v"
  by (simp add: subst_con_def usubst alpha, rel_simp)

text \<open> Variables in the "local" state space will be lost after a state is contracted \<close>

lemma subst_con_update_indep [usubst]: 
  "\<lbrakk> mwb_lens x; psym_lens a; \<V>\<^bsub>a\<^esub> \<bowtie> x \<rbrakk> \<Longrightarrow> con\<^sub>s a \<circ> subst_upd \<sigma> x v = (con\<^sub>s a \<circ> \<sigma>)"
  by (simp add: subst_con_alt_def usubst alpha)

lemma subst_ext_apply [usubst]: "\<langle>ext\<^sub>s a\<rangle>\<^sub>s x = &x \<restriction>\<^sub>e \<V>\<^bsub>a\<^esub>"
  by (rel_simp)

subsection \<open> Generic Blocks \<close>

text \<open> We ensure that the initial values of local are arbitrarily chosen \<close>

definition block_open :: "(<'a, 'c> \<Longleftrightarrow> 'b) \<Rightarrow> ('a, 'b) urel" ("open\<^bsub>_\<^esub>") where
[upred_defs]: "block_open a = \<langle>ext\<^sub>s a\<rangle>\<^sub>a ;; ($\<V>[a]\<acute> =\<^sub>u $\<V>[a])"

definition block_close :: "(<'a, 'c> \<Longleftrightarrow> 'b) \<Rightarrow> ('b, 'a) urel" ("close\<^bsub>_\<^esub>") where
[upred_defs]: "block_close a = \<langle>con\<^sub>s a\<rangle>\<^sub>a"

lemma block_open_conv: 
  "psym_lens a \<Longrightarrow> open\<^bsub>a\<^esub>\<^sup>- = close\<^bsub>a\<^esub>"
  by (rel_auto)

lemma block_open_close:
  "psym_lens a \<Longrightarrow> open\<^bsub>a\<^esub> ;; close\<^bsub>a\<^esub> = II"
  by (rel_auto, metis mwb_lens_def psym_lens.mwb_region weak_lens.create_get)

lemma block_assigns_open:
  "sym_lens a \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>a ;; open\<^bsub>a\<^esub> = open\<^bsub>a\<^esub> ;; \<langle>\<sigma> \<oplus>\<^sub>s \<V>\<^bsub>a\<^esub>\<rangle>\<^sub>a"
  by (rel_auto, metis mwb_lens_axioms_def mwb_lens_def sym_lens_def vwb_lens_def wb_lens_axioms_def wb_lens_def weak_lens.put_get)

lemma block_assign_local_close:
  "\<V>\<^bsub>a\<^esub> \<bowtie> x \<Longrightarrow> x := v ;; close\<^bsub>a\<^esub> = close\<^bsub>a\<^esub>"
  by (rel_auto)

end