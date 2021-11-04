section \<open>Fresh identifier generation for infinite types\<close>

theory Fresh_Infinite
  imports Fresh
begin

text \<open>This is a default fresh operator for infinite types
for which more specific (smarter) alternatives are not (yet) available. \<close>


definition (in infinite) fresh :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a" where
"fresh xs x \<equiv> if x \<notin> xs \<or> infinite xs then x else (SOME y. y \<notin> xs)"

sublocale infinite < fresh where fresh = fresh
apply standard
  subgoal unfolding fresh_def
  by (metis ex_new_if_finite local.infinite_UNIV someI_ex)
  subgoal unfolding fresh_def by simp .

end
