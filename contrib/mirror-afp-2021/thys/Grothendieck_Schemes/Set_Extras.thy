
text \<open>Authors: Anthony Bordg and Lawrence Paulson\<close>

theory Set_Extras
  imports "Jacobson_Basic_Algebra.Set_Theory"

begin

text \<open>Some new notation for built-in primitives\<close>

section \<open>Sets\<close>

abbreviation complement_in_of:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" ("_\<setminus>_" [65,65]65)
  where "A \<setminus> B \<equiv> A-B"

section \<open>Functions\<close>

abbreviation preimage:: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> 'a set" ("_ \<^sup>\<inverse> _ _" [90,90,1000]90)
  where "f\<^sup>\<inverse> X V \<equiv> (vimage f V) \<inter> X"

lemma preimage_of_inter:
  fixes f::"'a \<Rightarrow> 'b" and X::"'a set" and V::"'b set" and V'::"'b set"
  shows "f\<^sup>\<inverse> X (V \<inter> V') = (f\<^sup>\<inverse> X V) \<inter> (f\<^sup>\<inverse> X V')"
  by blast

lemma preimage_identity_self: "identity A \<^sup>\<inverse> A B = B \<inter> A"
  by (simp add: vimage_inter_cong)

text \<open>Simplification actually replaces the RHS by the LHS\<close>
lemma preimage_vimage_eq: "(f \<^sup>\<inverse> (f -` U') U) \<inter> X = f\<^sup>\<inverse> X (U \<inter> U')"
  by simp

definition inverse_map:: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'a)"
  where "inverse_map f S T \<equiv> restrict (inv_into S f) T"

lemma bijective_map_preimage:
  assumes "bijective_map f S T"
  shows "bijective_map (inverse_map f S T) T S"
proof
  show "inverse_map f S T \<in> T \<rightarrow>\<^sub>E S"
    by (simp add: assms bij_betw_imp_funcset bij_betw_inv_into bijective.bijective bijective_map.axioms(2) inverse_map_def)
  show "bij_betw (inverse_map f S T) T S"
    using assms by (simp add: bij_betw_inv_into bijective_def bijective_map_def inverse_map_def)
qed

lemma inverse_map_identity [simp]:
  "inverse_map (identity S) S S = identity S"
  by (metis Id_compose compose_id_inv_into image_ident image_restrict_eq inv_into_funcset inverse_map_def restrict_extensional)

abbreviation composing ("_ \<circ> _ \<down> _" [60,0,60]59)
  where "g \<circ> f \<down> D \<equiv> compose D g f"

lemma comp_maps:
  assumes "Set_Theory.map \<eta> A B" and "Set_Theory.map \<theta> B C"
  shows "Set_Theory.map (\<theta> \<circ> \<eta> \<down> A) A C"
proof-
  have "(\<theta> \<circ> \<eta> \<down> A) \<in> A \<rightarrow>\<^sub>E C"
    using assms by (metis Int_iff PiE_def compose_def funcset_compose map.graph restrict_extensional)
  thus ?thesis by (simp add: Set_Theory.map_def)
qed

lemma undefined_is_map_on_empty:
  fixes f:: "'a set \<Rightarrow> 'b set"
  assumes "f = (\<lambda>x. undefined)"
  shows "map f {} {}"
  using assms by (simp add: map.intro)

lemma restrict_on_source:
  assumes "map f S T"
  shows "restrict f S = f"
  using assms by (meson PiE_restrict map.graph)

lemma restrict_further:
  assumes "map f S T" and "U \<subseteq> S" and "V \<subseteq> U"
  shows "restrict (restrict f U) V = restrict f V"
  using assms by (simp add: inf.absorb_iff2)

lemma map_eq:
  assumes "map f S T" and "map g S T" and "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  shows "f = g"
  using assms by (metis restrict_ext restrict_on_source)

lemma image_subset_of_target:
  assumes "map f S T"
  shows "f ` S \<subseteq> T"
  using assms by (meson image_subsetI map.map_closed)

end
