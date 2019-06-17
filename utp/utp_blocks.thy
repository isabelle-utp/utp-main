section \<open> Blocks (Abstract Local Variables) \<close>

theory utp_blocks
  imports utp_rel_laws utp_wp
begin

syntax
  "_slens_view" :: "logic \<Rightarrow> svid" ("\<V>[_]")
  "_slens_coview" :: "logic \<Rightarrow> svid" ("\<C>[_]")

translations
  "_slens_view a" => "\<V>\<^bsub>a\<^esub>"
  "_slens_coview a" => "\<C>\<^bsub>a\<^esub>"

subsection \<open> Extending and Contracting Substitutions \<close>

definition subst_ext :: "(<'\<alpha>, '\<beta>> \<Longleftrightarrow> '\<gamma>) \<Rightarrow> ('\<alpha>, '\<gamma>) psubst" ("ext\<^sub>s") where
\<comment> \<open> Extend state space, setting local state to an arbitrary value \<close>
[upred_defs]: "ext\<^sub>s a = \<lparr>&\<V>[a] \<mapsto>\<^sub>s &\<^bold>v, &\<C>[a] \<mapsto>\<^sub>s \<guillemotleft>undefined\<guillemotright>\<rparr>" 

definition subst_con :: "(<'\<alpha>, '\<beta>> \<Longleftrightarrow> '\<gamma>) \<Rightarrow> ('\<gamma>, '\<alpha>) psubst" ("con\<^sub>s") where
\<comment> \<open> Contract the state space with get \<close>
"con\<^sub>s a = (\<lambda> s. get\<^bsub>\<V>\<^bsub>a\<^esub>\<^esub> s)"

lemma subst_con_alt_def [upred_defs]: "con\<^sub>s a = \<lparr>\<^bold>v \<mapsto>\<^sub>s &\<V>[a]\<rparr>"
  unfolding subst_con_def by (rel_auto)

lemma subst_ext_con [usubst]: "psym_lens a \<Longrightarrow> con\<^sub>s a \<circ> ext\<^sub>s a = id"
  by (rel_simp)

text \<open> Variables in the global state space will be retained after a state is contracted \<close>

lemma subst_con_update_sublens [usubst]: 
  "\<lbrakk> psym_lens a; x \<subseteq>\<^sub>L \<V>\<^bsub>a\<^esub> \<rbrakk> \<Longrightarrow> con\<^sub>s a \<circ> subst_upd \<sigma> x v = subst_upd (con\<^sub>s a \<circ> \<sigma>) (x /\<^sub>L \<V>\<^bsub>a\<^esub>) v"
  by (simp add: subst_con_def usubst alpha, rel_simp)

text \<open> Variables in the local state space will be lost after a state is contracted \<close>

lemma subst_con_update_indep [usubst]: 
  "\<lbrakk> mwb_lens x; psym_lens a; \<V>\<^bsub>a\<^esub> \<bowtie> x \<rbrakk> \<Longrightarrow> con\<^sub>s a \<circ> subst_upd \<sigma> x v = (con\<^sub>s a \<circ> \<sigma>)"
  by (simp add: subst_con_alt_def usubst alpha)

lemma subst_ext_apply [usubst]: "\<langle>ext\<^sub>s a\<rangle>\<^sub>s x = &x \<restriction>\<^sub>e \<V>\<^bsub>a\<^esub>"
  apply (rel_simp)
  oops

subsection \<open> Generic Blocks \<close>

text \<open> We ensure that the initial values of local are arbitrarily chosen using the non-deterministic
  choice operator. \<close>

definition block_open :: "(<'a, 'c> \<Longleftrightarrow> 'b) \<Rightarrow> ('a, 'b) urel" ("open\<^bsub>_\<^esub>") where
[upred_defs]: "block_open a = \<langle>ext\<^sub>s a\<rangle>\<^sub>a ;; \<C>[a] := *"

lemma block_open_alt_def:
  "sym_lens a \<Longrightarrow> block_open a = \<langle>ext\<^sub>s a\<rangle>\<^sub>a ;; ($\<V>[a]\<acute> =\<^sub>u $\<V>[a])"
  by (rel_auto, metis lens_indep_vwb_iff sym_lens.put_region_coregion_cover sym_lens_def)

definition block_close :: "(<'a, 'c> \<Longleftrightarrow> 'b) \<Rightarrow> ('b, 'a) urel" ("close\<^bsub>_\<^esub>") where
[upred_defs]: "block_close a = \<langle>con\<^sub>s a\<rangle>\<^sub>a"

lemma wp_open_block [wp]: "psym_lens a \<Longrightarrow> open\<^bsub>a\<^esub> wp b = (\<^bold>\<exists> v \<bullet> \<lparr>&\<V>[a] \<mapsto>\<^sub>s &\<^bold>v, &\<C>[a] \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>\<rparr> \<dagger> b)"
  by (simp add: block_open_def subst_ext_def wp usubst unrest)

lemma wp_close_block [wp]: "psym_lens a \<Longrightarrow> close\<^bsub>a\<^esub> wp b = con\<^sub>s a \<dagger> b"
  by (simp add: block_close_def subst_ext_def wp usubst unrest)

lemma block_open_conv:
  "sym_lens a \<Longrightarrow> open\<^bsub>a\<^esub>\<^sup>- = close\<^bsub>a\<^esub>"
  by (rel_auto, metis lens_indep_def sym_lens.put_region_coregion_cover sym_lens_def)

lemma block_open_close:
  "psym_lens a \<Longrightarrow> open\<^bsub>a\<^esub> ;; close\<^bsub>a\<^esub> = II"
  by (rel_auto)

text \<open> I needed this property for the assignment open law below. \<close>

lemma usubst_prop: "\<sigma> \<oplus>\<^sub>s a = [a \<mapsto>\<^sub>s uop \<sigma> &a]"
  by (rel_simp)

lemma block_assigns_open:
  "psym_lens a \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>a ;; open\<^bsub>a\<^esub> = open\<^bsub>a\<^esub> ;; \<langle>\<sigma> \<oplus>\<^sub>s \<V>\<^bsub>a\<^esub>\<rangle>\<^sub>a"
  apply (wp_calc)
  apply (simp add: usubst_prop usubst)
  apply (rel_auto)
  done

lemma block_assign_local_close:
  "\<V>\<^bsub>a\<^esub> \<bowtie> x \<Longrightarrow> x := v ;; close\<^bsub>a\<^esub> = close\<^bsub>a\<^esub>"
  by (rel_auto)

end