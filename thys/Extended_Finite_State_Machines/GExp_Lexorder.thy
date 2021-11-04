subsection\<open>GExp Lexorder\<close>

text\<open>This theory defines a lexicographical ordering on guard expressions such that we can build
orderings for transitions. We make use of the previously established orderings on arithmetic
expressions.\<close>

theory
GExp_Lexorder
imports
  "GExp"
  "AExp_Lexorder"
  "HOL-Library.List_Lexorder"
begin

fun height :: "'a gexp \<Rightarrow> nat" where
  "height (Bc _) = 1" |
  "height (Eq a1 a2) = 1 + max (AExp_Lexorder.height a1) (AExp_Lexorder.height a2)" |
  "height (Gt a1 a2) = 1 + max (AExp_Lexorder.height a1) (AExp_Lexorder.height a2)" |
  "height (In v l) = 2 + size l" |
  "height (Nor g1 g2) = 1 + max (height g1) (height g2)"

instantiation gexp :: (linorder) linorder begin
fun less_gexp_aux :: "'a gexp \<Rightarrow> 'a gexp \<Rightarrow> bool"  where
  "less_gexp_aux (Bc b1) (Bc b2) = (b1 < b2)" |
  "less_gexp_aux (Bc b1) _ = True" |

  "less_gexp_aux (Eq e1 e2) (Bc b2) = False" |
  "less_gexp_aux (Eq e1 e2) (Eq e1' e2') = ((e1 < e1') \<or> ((e1 = e1') \<and> (e2 < e2')))" |
  "less_gexp_aux (Eq e1 e2) _ = True" |

  "less_gexp_aux (Gt e1 e2) (Bc b2) = False" |
  "less_gexp_aux (Gt e1 e2) (Eq e1' e2') = False" |
  "less_gexp_aux (Gt e1 e2) (Gt e1' e2') = ((e1 < e1') \<or> ((e1 = e1') \<and> (e2 < e2')))" |
  "less_gexp_aux (Gt e1 e2) _ = True" |

  "less_gexp_aux (In vb vc) (Nor v va) = True" |
  "less_gexp_aux (In vb vc) (In v va) = (vb < v \<or> (vb = v \<and> vc < va))" |
  "less_gexp_aux (In vb vc) _ = False" |

  "less_gexp_aux (Nor g1 g2) (Nor g1' g2') = ((less_gexp_aux g1 g1') \<or> ((g1 = g1') \<and> (less_gexp_aux g2 g2')))" |
  "less_gexp_aux (Nor g1 g2) _ = False"

definition less_gexp :: "'a gexp \<Rightarrow> 'a gexp \<Rightarrow> bool" where
  "less_gexp a1 a2 = (
    let
      h1 = height a1;
      h2 = height a2
    in
    if h1 = h2 then
      less_gexp_aux a1 a2
    else
      h1 < h2
  )"

declare less_gexp_def [simp]

definition less_eq_gexp :: "'a gexp \<Rightarrow> 'a gexp \<Rightarrow> bool" where
  "less_eq_gexp e1 e2 \<equiv> (e1 < e2) \<or> (e1 = e2)"

lemma less_gexp_aux_antisym: "less_gexp_aux x y = (\<not>(less_gexp_aux y x) \<and> (x \<noteq> y))"
proof (induct x y rule: less_gexp_aux.induct)
  case (1 b1 b2)
  then show ?case by auto
next
  case ("2_1" b1 v va)
  then show ?case by auto
next
  case ("2_2" b1 v va)
  then show ?case by auto
next
  case ("2_3" b1 v va)
  then show ?case by auto
next
  case ("2_4" b1 v va)
  then show ?case by auto
next
  case (3 e1 e2 b2)
  then show ?case by auto
next
  case (4 e1 e2 e1' e2')
  then show ?case
    by (metis less_gexp_aux.simps(7) less_imp_not_less less_linear)
next
  case ("5_1" e1 e2 v va)
  then show ?case by auto
next
  case ("5_2" e1 e2 v va)
  then show ?case by auto
next
  case ("5_3" e1 e2 v va)
  then show ?case by auto
next
  case (6 e1 e2 b2)
  then show ?case by auto
next
  case (7 e1 e2 e1' e2')
  then show ?case by auto
next
  case (8 e1 e2 e1' e2')
  then show ?case
    by (metis less_gexp_aux.simps(13) less_imp_not_less less_linear)
next
  case ("9_1" e1 e2 v va)
  then show ?case by auto
next
  case ("9_2" e1 e2 v va)
  then show ?case by auto
next
  case (10 vb vc v va)
  then show ?case by auto
next
  case (11 vb vc v va)
  then show ?case by auto
next
  case ("12_1" vb vc v)
  then show ?case by auto
next
  case ("12_2" vb vc v va)
  then show ?case by auto
next
  case ("12_3" vb vc v va)
  then show ?case by auto
next
  case (13 g1 g2 g1' g2')
  then show ?case by auto
next
  case ("14_1" g1 g2 v)
  then show ?case by auto
next
  case ("14_2" g1 g2 v va)
  then show ?case by auto
next
  case ("14_3" g1 g2 v va)
  then show ?case by auto
next
  case ("14_4" g1 g2 v va)
  then show ?case by auto
qed

lemma less_gexp_antisym: "(x::'a gexp) < y = (\<not>(y < x) \<and> (x \<noteq> y))"
  apply (simp add: Let_def)
  apply standard
  using less_gexp_aux_antisym apply blast
  apply clarsimp
  by (induct x, auto)

lemma less_gexp_aux_trans: "less_gexp_aux x y \<Longrightarrow> less_gexp_aux y z \<Longrightarrow> less_gexp_aux x z"
proof(induct x y arbitrary: z rule: less_gexp_aux.induct)
case (1 b1 b2)
  then show ?case by (cases z, auto)
next
  case ("2_1" b1 v va)
  then show ?case by (cases z, auto)
next
  case ("2_2" b1 v va)
  then show ?case by (cases z, auto)
next
  case ("2_3" b1 v va)
  then show ?case by (cases z, auto)
next
  case ("2_4" b1 v va)
  then show ?case by (cases z, auto)
next
  case (3 e1 e2 b2)
  then show ?case by (cases z, auto)
next
  case (4 e1 e2 e1' e2')
  then show ?case
    apply (cases z)
        apply simp
       apply (metis dual_order.strict_trans less_gexp_aux.simps(7))
    by auto
next
  case ("5_1" e1 e2 v va)
  then show ?case by (cases z, auto)
next
  case ("5_2" e1 e2 v va)
  then show ?case by (cases z, auto)
next
  case ("5_3" e1 e2 v va)
  then show ?case by (cases z, auto)
next
  case (6 e1 e2 b2)
  then show ?case by (cases z, auto)
next
  case (7 e1 e2 e1' e2')
  then show ?case by (cases z, auto)
next
  case (8 e1 e2 e1' e2')
  then show ?case
    apply (cases z)
        apply simp
       apply simp
      apply (metis dual_order.strict_trans less_gexp_aux.simps(13))
    by auto
next
  case ("9_1" e1 e2 v va)
  then show ?case by (cases z, auto)
next
  case ("9_2" e1 e2 v va)
  then show ?case by (cases z, auto)
next
  case (10 vb vc v va)
  then show ?case by (cases z, auto)
next
  case (11 vb vc v va)
  then show ?case by (cases z, auto)
next
  case ("12_1" vb vc v)
  then show ?case by (cases z, auto)
next
  case ("12_2" vb vc v va)
  then show ?case by (cases z, auto)
next
  case ("12_3" vb vc v va)
  then show ?case by (cases z, auto)
next
  case (13 g1 g2 g1' g2')
  then show ?case by (cases z, auto)
next
  case ("14_1" g1 g2 v)
  then show ?case by (cases z, auto)
next
  case ("14_2" g1 g2 v va)
  then show ?case by (cases z, auto)
next
  case ("14_3" g1 g2 v va)
  then show ?case by (cases z, auto)
next
  case ("14_4" g1 g2 v va)
  then show ?case by (cases z, auto)
qed

lemma less_gexp_trans: "(x::'a gexp) < y \<Longrightarrow> y < z \<Longrightarrow> x < z"
  apply (simp add: Let_def)
  by (metis (no_types, lifting) dual_order.strict_trans less_gexp_aux_trans less_imp_not_less)

instance proof
  fix x y z :: "'a gexp"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (metis less_gexp_antisym less_eq_gexp_def)
  show "(x \<le> x)"
    by (simp add: less_eq_gexp_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (metis less_eq_gexp_def less_gexp_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding less_eq_gexp_def using less_gexp_antisym by blast
  show "x \<le> y \<or> y \<le> x"
    unfolding less_eq_gexp_def using less_gexp_antisym by blast
qed
end

end
