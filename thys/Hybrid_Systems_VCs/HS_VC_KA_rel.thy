(*  Title:       Verification components with relational MKA 
    Author:      Jonathan Julián Huerta y Munive, 2020
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

subsection \<open> Relational model \<close> (* by Victor Gomes, Georg Struth *)

text \<open> In this subsection, we follow Gomes and Struth~\cite{afp:vericomp} and show that relations 
form Kleene algebras.  \<close>

theory HS_VC_KA_rel
  imports Kleene_Algebra.Kleene_Algebra

begin

context dioid_one_zero
begin

lemma power_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> (x ^ n) \<cdot> z \<le> y"
  by(induct n, auto, metis mult.assoc mult_isol order_trans)

lemma power_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> (x ^ n) \<le> y"
proof (induct n)
  case 0 show ?case
    using "0.prems" by auto
  case Suc
  {fix n
    assume "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x ^ n \<le> y"
      and "z + y \<cdot> x \<le> y"
    hence "z \<cdot> x ^ n \<le> y"
      by auto
    also have "z \<cdot> x ^ Suc n = z \<cdot> x \<cdot> x ^ n"
      by (metis mult.assoc power_Suc)
    moreover have "... = (z \<cdot> x ^ n) \<cdot> x"
      by (metis mult.assoc power_commutes)
    moreover have "... \<le> y \<cdot> x"
      by (metis calculation(1) mult_isor)
    moreover have "... \<le> y"
      using \<open>z + y \<cdot> x \<le> y\<close> by auto
    ultimately have "z \<cdot> x ^ Suc n \<le> y" by auto}
  thus ?case
    by (metis Suc)
qed

end

interpretation rel_dioid: dioid_one_zero "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)"
  by (unfold_locales, auto)

lemma power_is_relpow: "rel_dioid.power X n = X ^^ n"
proof (induct n)
  case 0 show ?case
    by (metis rel_dioid.power_0 relpow.simps(1))
  case Suc thus ?case
    by (metis rel_dioid.power_Suc2 relpow.simps(2))
qed

lemma rel_star_def: "X^* = (\<Union>n. rel_dioid.power X n)"
  by (simp add: power_is_relpow rtrancl_is_UN_relpow)

lemma rel_star_contl: "X O Y^* = (\<Union>n. X O rel_dioid.power Y n)"
  by (metis rel_star_def relcomp_UNION_distrib)

lemma rel_star_contr: "X^* O Y = (\<Union>n. (rel_dioid.power X n) O Y)"
  by (metis rel_star_def relcomp_UNION_distrib2)

interpretation rel_ka: kleene_algebra "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl
proof
  fix x y z :: "'a rel"
  show "Id \<union> x O x\<^sup>* \<subseteq> x\<^sup>*"
    by (metis order_refl r_comp_rtrancl_eq rtrancl_unfold)
next
  fix x y z :: "'a rel"
  assume "z \<union> x O y \<subseteq> y"
  thus "x\<^sup>* O z \<subseteq> y"
    by (simp only: rel_star_contr, metis (lifting) SUP_le_iff rel_dioid.power_inductl)
next
  fix x y z :: "'a rel"
  assume "z \<union> y O x \<subseteq> y"
  thus "z O x\<^sup>* \<subseteq> y"
    by (simp only: rel_star_contl, metis (lifting) SUP_le_iff rel_dioid.power_inductr)
qed

end