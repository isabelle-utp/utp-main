theory Lens_Symmetric
  imports Lens_Order
begin

record ('a, 'b, 's) slens = 
  view   :: "'a \<Longrightarrow> 's" ("\<V>\<index>")
  coview :: "'b \<Longrightarrow> 's" ("\<C>\<index>")

type_notation
  slens ("<_, _> \<Longleftrightarrow> _")

locale sym_lens =
  fixes S :: "<'a, 'b> \<Longleftrightarrow> 's" (structure)
  assumes 
    vwb_region: "vwb_lens \<V>" and
    vwb_coregion: "vwb_lens \<C>" and
    indep_region_coregion: "\<V> \<bowtie> \<C>" and
    bij_region_coregion: "bij_lens (\<V> +\<^sub>L \<C>)"

end