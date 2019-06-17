section \<open> Symmetric Lenses \<close>

theory Lens_Symmetric
  imports Lens_Order
begin

text \<open> A characterisation of Hofmann's ``Symmetric Lenses''~\cite{Hofmann2011}, where
  a lens is accompanied by its complement. \<close>

record ('a, 'b, 's) slens = 
  view   :: "'a \<Longrightarrow> 's" ("\<V>\<index>") \<comment> \<open> The region characterised \<close>
  coview :: "'b \<Longrightarrow> 's" ("\<C>\<index>") \<comment> \<open> The complement of the region \<close>

type_notation
  slens ("<_, _> \<Longleftrightarrow> _")

subsection \<open> Partial Symmetric Lenses \<close>

locale psym_lens =
  fixes S :: "<'a, 'b> \<Longleftrightarrow> 's" (structure)
  assumes 
    mwb_region [simp]: "mwb_lens \<V>" and
    mwb_coregion [simp]: "mwb_lens \<C>" and
    indep_region_coregion [simp]: "\<V> \<bowtie> \<C>" and
    pbij_region_coregion [simp]: "pbij_lens (\<V> +\<^sub>L \<C>)"

declare psym_lens.mwb_region [simp]
declare psym_lens.mwb_coregion [simp]
declare psym_lens.indep_region_coregion [simp]

subsection \<open> Symmetric Lenses \<close>

locale sym_lens =
  fixes S :: "<'a, 'b> \<Longleftrightarrow> 's" (structure)
  assumes 
    vwb_region: "vwb_lens \<V>" and
    vwb_coregion: "vwb_lens \<C>" and
    indep_region_coregion: "\<V> \<bowtie> \<C>" and
    bij_region_coregion: "bij_lens (\<V> +\<^sub>L \<C>)"
begin

sublocale psym_lens
proof (rule psym_lens.intro)
  show "mwb_lens \<V>"
    by (simp add: vwb_region)
  show "mwb_lens \<C>"
    by (simp add: vwb_coregion)
  show "\<V> \<bowtie> \<C>"
    using indep_region_coregion by blast
  show "pbij_lens (\<V> +\<^sub>L \<C>)"
    by (simp add: bij_region_coregion)
qed

lemma put_region_coregion_cover:
  "put\<^bsub>\<V>\<^esub> (put\<^bsub>\<C>\<^esub> s\<^sub>1 (get\<^bsub>\<C>\<^esub> s\<^sub>2)) (get\<^bsub>\<V>\<^esub> s\<^sub>2) = s\<^sub>2"
proof -
  have "put\<^bsub>\<V>\<^esub> (put\<^bsub>\<C>\<^esub> s\<^sub>1 (get\<^bsub>\<C>\<^esub> s\<^sub>2)) (get\<^bsub>\<V>\<^esub> s\<^sub>2) = put\<^bsub>\<V> +\<^sub>L \<C>\<^esub> s\<^sub>1 (get\<^bsub>\<V> +\<^sub>L \<C>\<^esub> s\<^sub>2)"
    by (simp add: lens_defs)
  also have "... = s\<^sub>2"
    by (simp add: bij_region_coregion)
  finally show ?thesis .
qed

end

declare sym_lens.vwb_region [simp]
declare sym_lens.vwb_coregion [simp]
declare sym_lens.indep_region_coregion [simp]

end