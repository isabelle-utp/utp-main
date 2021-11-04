theory Dynamic
  imports Main
begin

locale dynval =
  fixes
    is_true :: "'dyn \<Rightarrow> bool" and
    is_false :: "'dyn \<Rightarrow> bool"
  assumes
    not_true_and_false: "\<not> (is_true d \<and> is_false d)"
begin

lemma false_not_true: "is_false d \<Longrightarrow> \<not> is_true d"
  using not_true_and_false by blast

lemma true_not_false: "is_true d \<Longrightarrow> \<not> is_false d"
  using not_true_and_false by blast

lemma is_true_and_is_false_implies_False: "is_true d \<Longrightarrow> is_false d \<Longrightarrow> False"
  using true_not_false false_not_true by simp

end

end