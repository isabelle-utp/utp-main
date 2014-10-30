theory bmap
imports bset
begin

subsection {* Type Definition *}

definition bmap :: "('a \<rightharpoonup> 'b) set" where
"bmap \<equiv> {f :: ('a \<rightharpoonup> 'b). dom(f) \<preceq>\<^sub>c c\<^sub>b\<^sub>s\<^sub>e\<^sub>t}"

theorem bmap_member (* [iff] *) :
"f \<in> bmap \<longleftrightarrow> dom(f) \<preceq>\<^sub>c c\<^sub>b\<^sub>s\<^sub>e\<^sub>t"
  by (simp add: bmap_def)
  
typedef ('a, 'b) bmap = "bmap :: ('a \<rightharpoonup> 'b) set"
morphisms DestBMap MkBMap
apply (rule_tac x = "Map.empty" in exI)
apply (simp add: bmap_def)
apply (unfold leq_card_def)
apply (simp only: inj_on_empty image_empty empty_subsetI)
apply (simp)
done

end
