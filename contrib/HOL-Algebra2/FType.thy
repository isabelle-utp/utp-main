theory FType
imports Main
begin

text {* To talk about functions between structures with carrier sets,
we need some notion of a function's \emph {type}. *}

definition ftype :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" (infixr "\<rightarrow>" 60) where
  "ftype A B \<equiv> {f. \<forall>x. x \<in> A \<longrightarrow> f x \<in> B}"

text {* We could also define \emph{ftype} as a predicate rather than
as a set. *}

lemma ftype_pred: "(f \<in> A \<rightarrow> B) = (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B)"
  by (simp add: ftype_def)

text {* Typing rules for composition and application can then be
derived, as well as the type of the identity function. *}

lemma typed_composition: "\<lbrakk>f \<in> A \<rightarrow> B; g \<in> B \<rightarrow> C\<rbrakk> \<Longrightarrow> g \<circ> f \<in> A \<rightarrow> C"
  by (simp add: ftype_def)

lemma typed_application: "\<lbrakk>x \<in> A; f \<in> A \<rightarrow> B\<rbrakk> \<Longrightarrow> f x \<in> B"
  by (simp add: ftype_def)

lemma typed_abstraction: "\<forall>x. f x \<in> A \<Longrightarrow> f \<in> UNIV \<rightarrow> A"
  by (simp add: ftype_def)

lemma typed_mapping: "\<lbrakk>f \<in> A \<rightarrow> B; X \<subseteq> A\<rbrakk> \<Longrightarrow> f ` X \<subseteq> B"
  by (metis ftype_pred image_subsetI set_mp)

lemma id_type: "id \<in> A \<rightarrow> A"
  by (simp add: ftype_def)

end