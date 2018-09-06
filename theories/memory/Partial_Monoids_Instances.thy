subsection \<open> Instances for Partial Monoids \<close>

theory Partial_Monoids_Instances
  imports Partial_Monoids "UTP-Toolkit.utp_toolkit"
begin

subsection \<open> Partial Functions \<close>

instantiation pfun :: (type, type) pas
begin
  definition compat_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" where
  "f ## g = (pdom(f) \<inter> pdom(g) = {})"
instance proof
  fix x y z :: "('a, 'b) pfun"
  assume "x ## y"
  thus "y ## x"
    by (auto simp add: compat_pfun_def)
  assume a: "x ## y" "x + y ## z"
  thus "x ## y + z"
    by (auto simp add: compat_pfun_def)
  from a show "y ## z"
    by (auto simp add: compat_pfun_def)
  from a show "x + y + z = x + (y + z)"
    by (simp add: add.assoc)
next
  fix x y :: "('a, 'b) pfun"
  assume "x ## y"
  thus "x + y = y + x"
    by (meson compat_pfun_def pfun_plus_commute)
qed
end

instance pfun :: (type, type) pam
proof
  fix x :: "('a, 'b) pfun"
  show "{}\<^sub>p ## x"
    by (simp add: compat_pfun_def)
  show "{}\<^sub>p + x = x"
    by (simp)
  show "x + {}\<^sub>p = x"
    by (simp)
qed

instance pfun :: (type, type) pam_cancel_pos
proof
  fix x y z :: "('a, 'b) pfun"
  assume "z ## x" "z ## y" "z + x = z + y"
  thus "x = y"
    by (auto simp add: compat_pfun_def, metis Int_commute pfun_minus_plus pfun_plus_commute)
next
  fix x y :: "('a, 'b) pfun"
  show "x + y = {}\<^sub>p \<Longrightarrow> x = {}\<^sub>p"
    using pfun_plus_pos by blast
qed

lemma pfun_compat_minus:
  fixes x y :: "('a, 'b) pfun"
  assumes "y \<subseteq>\<^sub>p x"
  shows "y ## x - y"
  using assms by (simp add: compat_pfun_def)

instance pfun :: (type, type) sep_alg
proof
  show 1: "\<And> x y :: ('a, 'b) pfun. (x \<subseteq>\<^sub>p y) = (x \<preceq>\<^sub>G y)"
    by (simp add: green_preorder_def compat_pfun_def)
       (metis compat_pfun_def pfun_compat_minus pfun_le_plus pfun_plus_commute pfun_plus_minus)
  show "\<And>x y :: ('a, 'b) pfun. (x \<subset>\<^sub>p y) = (x \<prec>\<^sub>G y)"
    by (simp add: "1" green_strict_def less_le_not_le)
  show "\<And>x y :: ('a, 'b) pfun. y \<subseteq>\<^sub>p x \<Longrightarrow> x - y = x -\<^sub>G y"
    apply (rule sym)
    apply (auto simp add: green_subtract_def 1[THEN sym])
     apply (rule the_equality)
      apply (auto simp add: pfun_compat_minus)
    using pfun_compat_minus pfun_plus_minus plus_pcomm apply fastforce
    apply (metis Int_commute compat_pfun_def pfun_minus_plus plus_pcomm)
    done
qed

instance pfun :: (type, type) sep_alg_cancel_pos .. 

subsection \<open> Finite Functions \<close>

instantiation ffun :: (type, type) pas
begin
  definition compat_ffun :: "('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun \<Rightarrow> bool" where
  "f ## g = (fdom(f) \<inter> fdom(g) = {})"

instance proof
  fix x y z :: "('a, 'b) ffun"
  assume "x ## y"
  thus "y ## x"
    by (simp add: compat_ffun_def inf_commute)
  assume a:"x ## y" "x + y ## z"
  thus "x ## y + z"
    by (metis (mono_tags, lifting) Partial_Monoids_Instances.compat_ffun_def compat_pfun_def compat_property fdom.rep_eq fdom_plus pdom_plus) 
  from a show "y ## z"
    by (metis Partial_Monoids_Instances.compat_ffun_def compat_pfun_def compat_property fdom.rep_eq plus_ffun.rep_eq)
  from a show "x + y + z = x + (y + z)"
    by (simp add: add.assoc)
next
  fix x y :: "('a, 'b) ffun"
  assume "x ## y"
  thus "x + y = y + x"
    by (meson compat_ffun_def ffun_plus_commute)
qed
end

instance ffun :: (type, type) pam
proof
  fix x :: "('a, 'b) ffun"
  show "{}\<^sub>f ## x"
    by (simp add: compat_ffun_def)
  show "{}\<^sub>f + x = x"
    by (simp)
  show "x + {}\<^sub>f = x"
    by (simp)
qed

instance ffun :: (type, type) pam_cancel_pos
proof
  fix x y z :: "('a, 'b) ffun"
  assume "z ## x" "z ## y" "z + x = z + y"
  thus "x = y"
    by (metis compat_comm compat_ffun_def ffun_minus_plus plus_pcomm)
next
  fix x y :: "('a, 'b) ffun"
  show "x + y = {}\<^sub>f \<Longrightarrow> x = {}\<^sub>f"
    using ffun_plus_pos by auto
qed

lemma ffun_compat_minus:
  fixes x y :: "('a, 'b) ffun"
  assumes "y \<subseteq>\<^sub>f x"
  shows "y ## x - y"
  by (metis assms compat_ffun_def compat_pfun_def fdom.rep_eq less_eq_ffun.rep_eq minus_ffun.rep_eq pfun_compat_minus)

instance ffun :: (type, type) sep_alg
proof
  show 1: "\<And> x y :: ('a, 'b) ffun. (x \<subseteq>\<^sub>f y) = (x \<preceq>\<^sub>G y)"
    using compat_ffun_def ffun_compat_minus ffun_le_plus ffun_plus_minus green_preorder_def plus_pcomm by fastforce
  show "\<And>x y :: ('a, 'b) ffun. (x \<subset>\<^sub>f y) = (x \<prec>\<^sub>G y)"
    by (simp add: "1" green_strict_def less_le_not_le)
  show "\<And>x y :: ('a, 'b) ffun. y \<subseteq>\<^sub>f x \<Longrightarrow> x - y = x -\<^sub>G y"
    apply (rule sym)
    apply (auto simp add: green_subtract_def 1[THEN sym])
     apply (rule the_equality)
      apply (auto simp add: ffun_compat_minus)
    using ffun_compat_minus ffun_plus_minus plus_pcomm apply fastforce
    apply (metis compat_comm compat_ffun_def ffun_minus_plus plus_pcomm)
    done
qed

instance ffun :: (type, type) sep_alg_cancel_pos .. 

end