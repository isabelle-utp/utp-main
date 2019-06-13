section \<open> Symmetric Lenses \<close>

theory Lens_Symmetric
  imports Lens_Order
begin

record ('a, 'b, 's) slens = 
  view   :: "'a \<Longrightarrow> 's" ("\<V>\<index>")
  coview :: "'b \<Longrightarrow> 's" ("\<C>\<index>")

type_notation
  slens ("<_, _> \<Longleftrightarrow> _")

locale psym_lens =
  fixes S :: "<'a, 'b> \<Longleftrightarrow> 's" (structure)
  assumes 
    mwb_region: "mwb_lens \<V>" and
    mwb_coregion: "mwb_lens \<C>" and
    indep_region_coregion: "\<V> \<bowtie> \<C>" and
    pbij_region_coregion: "pbij_lens (\<V> +\<^sub>L \<C>)"

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
end

end