section \<open>Fresh identifier generation for natural numbers\<close>

theory Fresh_Nat
  imports Fresh
begin

text \<open>Assuming \<open>x \<le> y\<close>, \<open>fresh2 xs x y\<close> returns an element
outside the interval \<open>(x,y)\<close> that is fresh for \<open>xs\<close> and closest to this interval,
favoring smaller elements: \<close>

function fresh2 :: "nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"fresh2 xs x y =
 (if x \<notin> xs \<or> infinite xs then x else
  if y \<notin> xs then y else
  fresh2 xs (x-1) (y+1))"
by auto
termination
  apply(relation "measure (\<lambda>(xs,x,y). (Max xs) + 1 - y)")
  by (simp_all add: Suc_diff_le)

lemma fresh2_notIn: "finite xs \<Longrightarrow> fresh2 xs x y \<notin> xs"
  by (induct xs x y rule: fresh2.induct) auto

lemma fresh2_eq: "x \<notin> xs \<Longrightarrow> fresh2 xs x y = x"
  by auto

declare fresh2.simps[simp del]

instantiation nat :: fresh
begin

text \<open>\<open>fresh xs x y\<close> returns an element
that is fresh for \<open>xs\<close> and closest to \<open>x\<close>, favoring smaller elements: \<close>

definition fresh_nat :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
"fresh_nat xs x \<equiv> fresh2 xs x x"

instance by standard (use fresh2_notIn fresh2_eq in \<open>auto simp add: fresh_nat_def\<close>)

end (* instantiation *)

text \<open>Code generation\<close>

lemma fresh2_list[code]:
  "fresh2 (set xs) x y =
     (if x \<notin> set xs then x else
      if y \<notin> set xs then y else
      fresh2 (set xs) (x-1) (y+1))"
  by (auto simp: fresh2.simps)

text \<open>Some tests: \<close>

value "[fresh {} (1::nat),
        fresh {3,5,2,4} 3]"

end
