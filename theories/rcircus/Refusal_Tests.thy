section \<open> Refusal Tests \<close>

theory Refusal_Tests
  imports Main
begin

subsection \<open> Refusal Sets \<close>

datatype 'e refusal = rfnil ("\<^bold>\<bullet>") | rfset "'e set" ("[_]\<^sub>\<R>")

abbreviation empty_refusal :: "'e refusal" ("{}\<^sub>\<R>") where
"empty_refusal \<equiv> [{}]\<^sub>\<R>"

instantiation refusal :: (type) order
begin
  fun less_eq_refusal :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> bool" where
  "\<^bold>\<bullet> \<le> S = True" |
  "R \<le> \<^bold>\<bullet> = (R = \<^bold>\<bullet>)" |
  "[X]\<^sub>\<R> \<le> [Y]\<^sub>\<R> = (X \<subseteq> Y)"
  definition less_refusal :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> bool" where
  "less_refusal S R = (S \<le> R \<and> \<not> R \<le> S)"
instance proof
  fix x y z :: "'a refusal"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_refusal_def)
  show "x \<le> x"
    by (cases x, simp_all)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x, simp_all, cases y, simp_all, cases z, simp_all)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (metis Refusal_Tests.less_eq_refusal.elims(2) dual_order.antisym less_eq_refusal.simps(2) refusal.inject)
qed

end

abbreviation rsubseteq :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> bool" ("(_/ \<subseteq>\<^sub>\<R> _)" [51, 51] 50) where 
"S \<subseteq>\<^sub>\<R> R \<equiv> S \<le> R"

fun rmember :: "'a \<Rightarrow> 'a refusal \<Rightarrow> bool" ("(_/ \<in>\<^sub>\<R> _)" [51, 51] 50) where
"x \<in>\<^sub>\<R> \<^bold>\<bullet> = False" | "x \<in>\<^sub>\<R> [R]\<^sub>\<R> = (x \<in> R)"

abbreviation rnot_member ("(_/ \<notin>\<^sub>\<R> _)" [51, 51] 50)
  where "rnot_member x A \<equiv> \<not> (x \<in>\<^sub>\<R>  A)"

lemma rfnil_mem_dest [dest]: "x \<in>\<^sub>\<R> \<^bold>\<bullet> \<Longrightarrow> P"
  by (metis rmember.simps(1))

instantiation refusal :: (type) lattice
begin
  fun sup_refusal :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> 'a refusal"  where
  "sup \<^bold>\<bullet> R = R" |
  "sup S \<^bold>\<bullet> = S" |
  "sup [S]\<^sub>\<R> [R]\<^sub>\<R> = [S \<union> R]\<^sub>\<R>"

  fun inf_refusal :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> 'a refusal"  where
  "inf \<^bold>\<bullet> R = \<^bold>\<bullet>" |
  "inf S \<^bold>\<bullet> = \<^bold>\<bullet>" |
  "inf [S]\<^sub>\<R> [R]\<^sub>\<R> = [S \<inter> R]\<^sub>\<R>"
instance proof
  fix x y z :: "'a refusal"
  show "inf x y \<subseteq>\<^sub>\<R> x"
    by (cases x, simp_all, cases y, simp_all)
  show "inf x y \<subseteq>\<^sub>\<R> y"
    by (cases x, simp_all, cases y, simp_all)
  show "x \<subseteq>\<^sub>\<R> y \<Longrightarrow> x \<subseteq>\<^sub>\<R> z \<Longrightarrow> x \<subseteq>\<^sub>\<R> inf y z"
    by (cases x, simp_all, cases y, simp_all, cases z, simp_all)
  show "x \<subseteq>\<^sub>\<R> sup x y"
    by (cases x, simp_all, cases y, simp_all)
  show "y \<subseteq>\<^sub>\<R> sup x y"
    by (cases x, simp_all, cases y, simp_all)
  show "y \<subseteq>\<^sub>\<R> x \<Longrightarrow> z \<subseteq>\<^sub>\<R> x \<Longrightarrow> sup y z \<subseteq>\<^sub>\<R> x"
    by (cases x, simp_all, cases y, simp_all, cases z, simp_all, cases y, simp_all, cases y, simp_all)
qed
end

abbreviation runion :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> 'a refusal"  (infixl "\<union>\<^sub>\<R>" 65)
  where "runion \<equiv> Lattices.sup"

abbreviation rinter :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> 'a refusal"  (infixl "\<inter>\<^sub>\<R>" 70)
  where "rinter \<equiv> Lattices.inf"

lemma refusal_mp: "\<lbrakk> A \<subseteq>\<^sub>\<R> B; x \<in>\<^sub>\<R> A \<rbrakk> \<Longrightarrow> x \<in>\<^sub>\<R> B"
  by (cases A, simp_all, metis (full_types) less_eq_refusal.elims(2) refusal.distinct(1) rmember.simps(2) subsetD)

subsection \<open> Refusal Events \<close>

typedef 'e revent = "{(X :: 'e refusal, a :: 'e). a \<notin>\<^sub>\<R> X}"
  by (rule_tac x="(\<^bold>\<bullet>, undefined)" in exI, simp)

setup_lifting type_definition_revent

lift_definition rrefusal :: "'e revent \<Rightarrow> 'e refusal" is fst .
lift_definition revent   :: "'e revent \<Rightarrow> 'e" is snd .

lemma revent_notin_refusal [simp]:
  "revent a \<notin>\<^sub>\<R> rrefusal a"
  by (metis Rep_revent mem_Collect_eq prod.case_eq_if revent.rep_eq rrefusal.rep_eq)

end