section \<open> Blocks (Abstract Local Variables) \<close>

theory utp_blocks
  imports utp_rel_laws utp_wp
begin

subsection \<open> Extending and Contracting Substitutions \<close>

definition subst_ext :: "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<alpha>, '\<beta>) psubst" ("ext\<^sub>s") where
\<comment> \<open> Extend state space, setting local state to an arbitrary value \<close>
[upred_defs]: "ext\<^sub>s a = \<lparr>&a \<mapsto>\<^sub>s &\<^bold>v\<rparr>" 

definition subst_con :: "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<beta>, '\<alpha>) psubst" ("con\<^sub>s") where
\<comment> \<open> Contract the state space with get \<close>
[upred_defs]: "con\<^sub>s a = &a"

lemma subst_con_alt_def: "con\<^sub>s a = \<lparr>\<^bold>v \<mapsto>\<^sub>s &a\<rparr>"
  unfolding subst_con_def by (rel_auto)

lemma subst_ext_con [usubst]: "mwb_lens a \<Longrightarrow> con\<^sub>s a \<circ>\<^sub>s ext\<^sub>s a = id\<^sub>s"
  by (rel_simp)

lemma subst_apply_con [usubst]: "\<langle>con\<^sub>s a\<rangle>\<^sub>s x = &a:x"
  by (rel_simp)

text \<open> Variables in the global state space will be retained after a state is contracted \<close>

lemma subst_con_update_sublens [usubst]: 
  "\<lbrakk> mwb_lens a; x \<subseteq>\<^sub>L a \<rbrakk> \<Longrightarrow> con\<^sub>s a \<circ>\<^sub>s subst_upd \<sigma> x v = subst_upd (con\<^sub>s a \<circ>\<^sub>s \<sigma>) (x /\<^sub>L a) v"
  by (simp add: subst_con_def usubst alpha, rel_simp)

text \<open> Variables in the local state space will be lost after a state is contracted \<close>

lemma subst_con_update_indep [usubst]: 
  "\<lbrakk> mwb_lens x; mwb_lens a; a \<bowtie> x \<rbrakk> \<Longrightarrow> con\<^sub>s a \<circ>\<^sub>s subst_upd \<sigma> x v = (con\<^sub>s a \<circ>\<^sub>s \<sigma>)"
  by (simp add: subst_con_alt_def usubst alpha)

lemma subst_ext_apply [usubst]: "\<langle>ext\<^sub>s a\<rangle>\<^sub>s x = &x \<restriction>\<^sub>e a"
  apply (rel_simp)
  oops

subsection \<open> Generic Blocks \<close>

text \<open> We ensure that the initial values of local are arbitrarily chosen using the non-deterministic
  choice operator. \<close>

definition block_open :: "(<'a, 'c> \<Longleftrightarrow> 'b) \<Rightarrow> ('a, 'b) urel" ("open\<^bsub>_\<^esub>") where
[upred_defs]: "block_open a = \<langle>ext\<^sub>s \<V>\<^bsub>a\<^esub>\<rangle>\<^sub>a ;; \<C>[a] := *"

lemma block_open_alt_def:
  "sym_lens a \<Longrightarrow> block_open a = \<langle>ext\<^sub>s \<V>\<^bsub>a\<^esub>\<rangle>\<^sub>a ;; ($\<V>[a]\<acute> =\<^sub>u $\<V>[a])"
  by (rel_auto, metis lens_indep_vwb_iff sym_lens.put_region_coregion_cover sym_lens_def)

definition block_close :: "(<'a, 'c> \<Longleftrightarrow> 'b) \<Rightarrow> ('b, 'a) urel" ("close\<^bsub>_\<^esub>") where
[upred_defs]: "block_close a = \<langle>con\<^sub>s \<V>\<^bsub>a\<^esub>\<rangle>\<^sub>a"

lemma wp_open_block [wp]: "psym_lens a \<Longrightarrow> open\<^bsub>a\<^esub> wp b = (\<^bold>\<exists> v \<bullet> \<lparr>&\<V>[a] \<mapsto>\<^sub>s &\<^bold>v, &\<C>[a] \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>\<rparr> \<dagger> b)"
  by (simp add: block_open_def subst_ext_def wp usubst unrest)

lemma wp_close_block [wp]: "psym_lens a \<Longrightarrow> close\<^bsub>a\<^esub> wp b = con\<^sub>s \<V>\<^bsub>a\<^esub> \<dagger> b"
  by (simp add: block_close_def subst_ext_def wp usubst unrest)

lemma block_open_conv:
  "sym_lens a \<Longrightarrow> open\<^bsub>a\<^esub>\<^sup>- = close\<^bsub>a\<^esub>"
  by (rel_auto, metis lens_indep_def sym_lens.put_region_coregion_cover sym_lens_def)

lemma block_open_close:
  "psym_lens a \<Longrightarrow> open\<^bsub>a\<^esub> ;; close\<^bsub>a\<^esub> = II"
  by (rel_auto)

text \<open> I needed this property for the assignment open law below. \<close>

lemma usubst_prop: "\<sigma> \<oplus>\<^sub>s a = [a \<mapsto>\<^sub>s &a \<dagger> \<sigma>]"
  by (rel_simp)

lemma block_assigns_open:
  "psym_lens a \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>a ;; open\<^bsub>a\<^esub> = open\<^bsub>a\<^esub> ;; \<langle>\<sigma> \<oplus>\<^sub>s \<V>\<^bsub>a\<^esub>\<rangle>\<^sub>a"
  apply (wp_calc)
  apply (simp add: usubst_prop usubst)
  apply (rel_auto)
  done

lemma block_assign_open:
  "psym_lens a \<Longrightarrow> x := v ;; open\<^bsub>a\<^esub> = open\<^bsub>a\<^esub> ;; \<V>[a]:x := (v \<oplus>\<^sub>p \<V>\<^bsub>a\<^esub>)"
  by (simp add: block_assigns_open, rel_auto)

lemma block_assign_local_close:
  "\<V>\<^bsub>a\<^esub> \<bowtie> x \<Longrightarrow> x := v ;; close\<^bsub>a\<^esub> = close\<^bsub>a\<^esub>"
  by (rel_auto)
  
lemma block_assign_global_close:
  "\<lbrakk> psym_lens a; x \<subseteq>\<^sub>L \<V>\<^bsub>a\<^esub> ; \<V>[a] \<natural> v \<rbrakk> \<Longrightarrow> (x := v) ;; close\<^bsub>a\<^esub> = close\<^bsub>a\<^esub> ;; (x\<restriction>\<V>[a] := (v \<restriction>\<^sub>e \<V>\<^bsub>a\<^esub>))"
  by (rel_simp)

lemma block_assign_global_close':
  "\<lbrakk> sym_lens a; x \<subseteq>\<^sub>L \<V>\<^bsub>a\<^esub> ; \<C>[a] \<sharp> v \<rbrakk> \<Longrightarrow> (x := v) ;; close\<^bsub>a\<^esub> = close\<^bsub>a\<^esub> ;; (x\<restriction>\<V>[a] := (v \<restriction>\<^sub>e \<V>\<^bsub>a\<^esub>))"
  by (rule block_assign_global_close, simp_all add: sym_lens_unrest')

lemma hoare_block [hoare_safe]: 
  assumes "psym_lens a"
  shows "\<lbrace>p \<oplus>\<^sub>p \<V>\<^bsub>a\<^esub>\<rbrace>P\<lbrace>q \<oplus>\<^sub>p \<V>\<^bsub>a\<^esub>\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>p\<rbrace>open\<^bsub>a\<^esub> ;; P ;; close\<^bsub>a\<^esub>\<lbrace>q\<rbrace>\<^sub>u"
  using assms by (rel_simp)

lemma "vwb_lens a \<Longrightarrow> a:[P]\<^sup>+ = a:[\<langle>con\<^sub>s a\<rangle>\<^sub>a ;; P ;; \<langle>ext\<^sub>s a\<rangle>\<^sub>a ;; ($a\<acute> =\<^sub>u $a)]"
  by (rel_auto)

end