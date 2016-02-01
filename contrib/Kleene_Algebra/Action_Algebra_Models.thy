(* Title:      Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

header {* Models of Action Algebras *}

theory Action_Algebra_Models
imports Action_Algebra Kleene_Algebra_Models
begin

subsection {* The Powerset Action Algebra over a Monoid *}

text {* Here we show that various models of Kleene algebras are also
residuated; hence they form action algebras. In each case the main
work is to establish the residuated lattice structure. *}

text {* The interpretation proofs for some of the following models are
quite similar. One could, perhaps, abstract out common reasoning. *}


subsection {* The Powerset Action Algebra over a Monoid *}

instantiation set :: (monoid_mult) residuated_join_semilattice
begin

  definition residual_r_set where
    "X \<rightarrow> Z = \<Union> {Y. X \<cdot> Y \<subseteq> Z}"

  definition residual_l_set where
    "Z \<leftarrow> Y = \<Union> {X. X \<cdot> Y \<subseteq> Z}"

  instance
  proof
    fix X Y Z :: "'a set"
    show "X \<subseteq> (Z \<leftarrow> Y) \<longleftrightarrow> X \<cdot> Y \<subseteq> Z"
    proof
      assume "X \<subseteq> Z \<leftarrow> Y"
      hence "X \<cdot> Y \<subseteq> (Z \<leftarrow> Y) \<cdot> Y"
        by (metis near_dioid_class.mult_isor)
      also have "\<dots> \<subseteq> \<Union> {X. X \<cdot> Y \<subseteq> Z} \<cdot> Y"
        by (simp add: residual_l_set_def)
      also have "\<dots> = \<Union> {X \<cdot> Y | X. X \<cdot> Y \<subseteq> Z}"
        by (auto simp only: c_prod_def)
      finally show "X \<cdot> Y \<subseteq> Z"
        by auto
    next
      assume "X \<cdot> Y \<subseteq> Z"
      hence "X \<subseteq> \<Union> {X. X \<cdot> Y \<subseteq> Z}"
        by (metis Sup_upper mem_Collect_eq)
      thus "X \<subseteq> Z \<leftarrow> Y"
        by (simp add: residual_l_set_def)
    qed
    show "X \<cdot> Y \<subseteq> Z \<longleftrightarrow> Y \<subseteq> (X \<rightarrow> Z)"
    proof
      assume "Y \<subseteq> X \<rightarrow> Z"
      hence "X \<cdot> Y \<subseteq> X \<cdot> (X \<rightarrow> Z)"
        by (metis pre_dioid_class.mult_isol)
      also have "\<dots> \<subseteq> X \<cdot> \<Union> {Y. X \<cdot> Y \<subseteq> Z}"
        by (simp add: residual_r_set_def)
      also have "\<dots> = \<Union> {X \<cdot> Y | Y. X \<cdot> Y \<subseteq> Z}"
        by (auto simp only: c_prod_def)
      finally show "X \<cdot> Y \<subseteq> Z"
        by auto
    next
      assume "X \<cdot> Y \<subseteq> Z"
      hence "Y \<subseteq> \<Union> {Y. X \<cdot> Y \<subseteq> Z}"
        by (metis Sup_upper mem_Collect_eq)
      thus "Y \<subseteq> X \<rightarrow> Z"
        by (simp add: residual_r_set_def)
    qed
qed

end (* instantiation *)

instantiation set :: (monoid_mult) action_algebra
begin

  instance
  proof
    fix x y :: "'a set"
    show "1 + x\<^sup>\<star> \<cdot> x\<^sup>\<star> + x \<subseteq> x\<^sup>\<star>"
      by (metis join_semilattice_class.add_lub left_near_kleene_algebra_class.star_plus_one left_near_kleene_algebra_class.star_trans_eq left_pre_kleene_algebra_class.star_ext subset_refl)
    show  "1 + y \<cdot> y + x \<subseteq> y \<longrightarrow> x\<^sup>\<star> \<subseteq> y"
      by (metis ab_semigroup_add_class.add_ac(1) join_semilattice_class.add_comm left_pre_kleene_algebra_class.star_rtc_least)
  qed

end (* instantiation *)


subsection {* Language Action Algebras *}

definition limp_lan :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" where
  "limp_lan Z Y = {x. \<forall>y \<in> Y. x @ y \<in> Z}"

definition rimp_lan :: "'a lan \<Rightarrow> 'a lan \<Rightarrow> 'a lan" where
  "rimp_lan X Z = {y. \<forall>x \<in> X. x @ y \<in> Z}"

interpretation lan_residuated_join_semilattice: residuated_join_semilattice "op +" "op \<subseteq>" "op \<subset>" "op \<cdot>" limp_lan rimp_lan
proof
  fix x y z :: "'a lan"
  show "x \<subseteq> limp_lan z y \<longleftrightarrow> x \<cdot> y \<subseteq> z"
    by (auto simp add: c_prod_def limp_lan_def times_list_def)
  show "x \<cdot> y \<subseteq> z \<longleftrightarrow> y \<subseteq> rimp_lan x z"
    by (auto simp add: c_prod_def rimp_lan_def times_list_def)
qed

interpretation lan_action_algebra: action_algebra "op +" "op \<subseteq>" "op \<subset>" "op \<cdot>" limp_lan rimp_lan 1 0 star
proof
  fix x y :: "'a lan"
  show "1 + x\<^sup>\<star> \<cdot> x\<^sup>\<star> + x \<subseteq> x\<^sup>\<star>"
    by (metis left_near_kleene_algebra_class.star_plus_one left_near_kleene_algebra_class.star_trans left_near_kleene_algebra_class.star_trans_eq left_near_kleene_algebra_class.sum_star_closure left_pre_kleene_algebra_class.star_ext)
  show "1 + y \<cdot> y + x \<subseteq> y \<longrightarrow> x\<^sup>\<star> \<subseteq> y"
    by (metis ab_semigroup_add_class.add_ac(1) join_semilattice_class.add_comm left_pre_kleene_algebra_class.star_rtc_least)
qed


subsection {* Relation Action Algebras *}

definition limp_rel :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "limp_rel T S = {(y,x) | y x. \<forall>z. (x,z) \<in> S \<longrightarrow> (y,z) \<in> T}"

definition rimp_rel :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where
  "rimp_rel R T = {(y,z) | y z. \<forall>x. (x,y) \<in> R \<longrightarrow> (x,z) \<in> T}"

interpretation rel_residuated_join_semilattice: residuated_join_semilattice "op \<union>" "op \<subseteq>" "op \<subset>" "op O" limp_rel rimp_rel
proof
  fix x y z :: "'a rel"
  show "x \<subseteq> limp_rel z y \<longleftrightarrow> x O y \<subseteq> z"
    by (auto simp add: limp_rel_def)
  show "x O y \<subseteq> z \<longleftrightarrow> y \<subseteq> rimp_rel x z"
    by (auto simp add: rimp_rel_def)
qed

interpretation rel_action_algebra: action_algebra "op \<union>" "op \<subseteq>" "op \<subset>" "op O" limp_rel rimp_rel Id "{}" rtrancl
proof
  fix x y :: "'a rel"
  show "Id \<union> x\<^sup>* O x\<^sup>* \<union> x \<subseteq> x\<^sup>*"
    by auto
  show "Id \<union> y O y \<union> x \<subseteq> y \<longrightarrow> x\<^sup>* \<subseteq> y"
    by (metis le_supE rel_kleene_algebra.star_rtc2 rtrancl_mono)
qed


subsection {* Trace Action Algebras *}

definition limp_trace :: "('p, 'a) trace set \<Rightarrow> ('p, 'a) trace set \<Rightarrow> ('p, 'a) trace set" where
  "limp_trace Z Y = \<Union> {X. t_prod X Y \<subseteq> Z}"

definition rimp_trace :: "('p, 'a) trace set \<Rightarrow> ('p, 'a) trace set \<Rightarrow> ('p, 'a) trace set" where
  "rimp_trace X Z = \<Union> {Y. t_prod X Y \<subseteq> Z}"

interpretation trace_residuated_join_semilattice: residuated_join_semilattice "op \<union>" "op \<subseteq>" "op \<subset>" t_prod limp_trace rimp_trace
proof
  fix X Y Z :: "('a,'b) trace set"
  show "X \<subseteq> limp_trace Z Y \<longleftrightarrow> t_prod X Y \<subseteq> Z"
    proof
      assume "X \<subseteq> limp_trace Z Y"
      hence "t_prod X Y \<subseteq> t_prod (limp_trace Z Y) Y"
        by (metis trace_dioid.mult_isor)
      also have "\<dots> \<subseteq> t_prod (\<Union> {X. t_prod X Y \<subseteq> Z}) Y"
        by (simp add: limp_trace_def)
      also have "\<dots> = \<Union> {t_prod X Y | X. t_prod X Y \<subseteq> Z}"
        by (auto simp only: t_prod_def)
      finally show "t_prod X Y \<subseteq> Z"
        by auto
    next
      assume "t_prod X Y \<subseteq> Z"
      hence "X \<subseteq> \<Union> {X. t_prod X Y \<subseteq> Z}"
        by (metis Sup_upper mem_Collect_eq)
      thus "X \<subseteq> limp_trace Z Y"
        by (simp add: limp_trace_def)
    qed
  show "t_prod X Y \<subseteq> Z \<longleftrightarrow> Y \<subseteq> rimp_trace X Z"
    proof
      assume "t_prod X Y \<subseteq> Z"
      hence "Y \<subseteq> \<Union> {Y. t_prod X Y \<subseteq> Z}"
        by (metis Sup_upper mem_Collect_eq)
      thus "Y \<subseteq> rimp_trace X Z"
        by (simp add: rimp_trace_def)
    next
      assume "Y \<subseteq> rimp_trace X Z"
      hence "t_prod X Y \<subseteq> t_prod X (rimp_trace X Z)"
        by (metis trace_dioid.mult_isol)
      also have "\<dots> \<subseteq> t_prod X (\<Union> {Y. t_prod X Y \<subseteq> Z})"
        by (simp add: rimp_trace_def)
      also have "\<dots> = \<Union> {t_prod X Y | Y. t_prod X Y \<subseteq> Z}"
        by (auto simp only: t_prod_def)
      finally show "t_prod X Y \<subseteq> Z"
        by auto
    qed
qed

interpretation trace_action_algebra: action_algebra "op \<union>" "op \<subseteq>" "op \<subset>" t_prod limp_trace rimp_trace t_one t_zero t_star
proof
  fix X Y :: "('a,'b) trace set"
  show "t_one \<union> t_prod (t_star X) (t_star X) \<union> X \<subseteq> t_star X"
    by (metis Un_least order_refl trace_kleene_algebra.star_ext trace_kleene_algebra.star_plus_one trace_kleene_algebra.star_trans_eq)
  show "t_one \<union> t_prod Y Y \<union> X \<subseteq> Y \<longrightarrow> t_star X \<subseteq> Y"
    by (metis Un_commute le_iff_sup trace_dioid.add_lub trace_kleene_algebra.boffa_var trace_kleene_algebra.star_subdist)
qed


subsection {* Path Action Algebras *}

text {* We start with paths that include the empty path. *}

definition limp_path :: "'a path set \<Rightarrow> 'a path set \<Rightarrow> 'a path set" where
  "limp_path Z Y = \<Union> {X. p_prod X Y \<subseteq> Z}"

definition rimp_path :: "'a path set \<Rightarrow> 'a path set \<Rightarrow> 'a path set" where
  "rimp_path X Z = \<Union> {Y. p_prod X Y \<subseteq> Z}"

interpretation path_residuated_join_semilattice: residuated_join_semilattice "op \<union>" "op \<subseteq>" "op \<subset>" p_prod limp_path rimp_path
proof
  fix X Y Z :: "'a path set"
  show "X \<subseteq> limp_path Z Y \<longleftrightarrow> p_prod X Y \<subseteq> Z"
    proof
      assume "X \<subseteq> limp_path Z Y"
      hence "p_prod X Y \<subseteq> p_prod (limp_path Z Y) Y"
        by (metis path_dioid.mult_isor)
      also have "\<dots> \<subseteq> p_prod (\<Union> {X. p_prod X Y \<subseteq> Z}) Y"
        by (simp add: limp_path_def)
      also have "\<dots> = \<Union> {p_prod X Y | X. p_prod X Y \<subseteq> Z}"
        by (auto simp only: p_prod_def)
      finally show "p_prod X Y \<subseteq> Z"
        by auto
    next
      assume "p_prod X Y \<subseteq> Z"
      hence "X \<subseteq> \<Union> {X. p_prod X Y \<subseteq> Z}"
        by (metis Sup_upper mem_Collect_eq)
      thus "X \<subseteq> limp_path Z Y"
        by (simp add: limp_path_def)
    qed
  show "p_prod X Y \<subseteq> Z \<longleftrightarrow> Y \<subseteq> rimp_path X Z"
    proof
      assume "p_prod X Y \<subseteq> Z"
      hence "Y \<subseteq> \<Union> {Y. p_prod X Y \<subseteq> Z}"
        by (metis Sup_upper mem_Collect_eq)
      thus "Y \<subseteq> rimp_path X Z"
        by (simp add: rimp_path_def)
    next
      assume "Y \<subseteq> rimp_path X Z"
      hence "p_prod X Y \<subseteq> p_prod X (rimp_path X Z)"
        by (metis path_dioid.mult_isol)
      also have "\<dots> \<subseteq> p_prod X (\<Union> {Y. p_prod X Y \<subseteq> Z})"
        by (simp add: rimp_path_def)
      also have "\<dots> = \<Union> {p_prod X Y | Y. p_prod X Y \<subseteq> Z}"
        by (auto simp only: p_prod_def)
      finally show "p_prod X Y \<subseteq> Z"
        by auto
    qed
qed

interpretation path_action_algebra: action_algebra "op \<union>" "op \<subseteq>" "op \<subset>" p_prod limp_path rimp_path p_one "{}" p_star
proof
  fix X Y :: "'a path set"
  show "p_one \<union> p_prod (p_star X) (p_star X) \<union> X \<subseteq> p_star X"
    by (metis Un_least order_refl path_kleene_algebra.star_ext path_kleene_algebra.star_plus_one path_kleene_algebra.star_trans_eq)
  show "p_one \<union> p_prod Y Y \<union> X \<subseteq> Y \<longrightarrow> p_star X \<subseteq> Y"
    by (metis Un_commute le_iff_sup path_dioid.add_lub path_kleene_algebra.boffa_var path_kleene_algebra.star_subdist)
qed

text {* We now consider a notion of paths that does not include the
empty path. *}

definition limp_ppath :: "'a ppath set \<Rightarrow> 'a ppath set \<Rightarrow> 'a ppath set" where
  "limp_ppath Z Y = \<Union> {X. pp_prod X Y \<subseteq> Z}"

definition rimp_ppath :: "'a ppath set \<Rightarrow> 'a ppath set \<Rightarrow> 'a ppath set" where
  "rimp_ppath X Z = \<Union> {Y. pp_prod X Y \<subseteq> Z}"

interpretation ppath_residuated_join_semilattice: residuated_join_semilattice "op \<union>" "op \<subseteq>" "op \<subset>" pp_prod limp_ppath rimp_ppath
proof
  fix X Y Z :: "'a ppath set"
  show "X \<subseteq> limp_ppath Z Y \<longleftrightarrow> pp_prod X Y \<subseteq> Z"
    proof
      assume "X \<subseteq> limp_ppath Z Y"
      hence "pp_prod X Y \<subseteq> pp_prod (limp_ppath Z Y) Y"
        by (metis ppath_dioid.mult_isor)
      also have "\<dots> \<subseteq> pp_prod (\<Union> {X. pp_prod X Y \<subseteq> Z}) Y"
        by (simp add: limp_ppath_def)
      also have "\<dots> = \<Union> {pp_prod X Y | X. pp_prod X Y \<subseteq> Z}"
        by (auto simp only: pp_prod_def)
      finally show "pp_prod X Y \<subseteq> Z"
        by auto
    next
      assume "pp_prod X Y \<subseteq> Z"
      hence "X \<subseteq> \<Union> {X. pp_prod X Y \<subseteq> Z}"
        by (metis Sup_upper mem_Collect_eq)
      thus "X \<subseteq> limp_ppath Z Y"
        by (simp add: limp_ppath_def)
    qed
  show "pp_prod X Y \<subseteq> Z \<longleftrightarrow> Y \<subseteq> rimp_ppath X Z"
    proof
      assume "pp_prod X Y \<subseteq> Z"
      hence "Y \<subseteq> \<Union> {Y. pp_prod X Y \<subseteq> Z}"
        by (metis Sup_upper mem_Collect_eq)
      thus "Y \<subseteq> rimp_ppath X Z"
        by (simp add: rimp_ppath_def)
    next
      assume "Y \<subseteq> rimp_ppath X Z"
      hence "pp_prod X Y \<subseteq> pp_prod X (rimp_ppath X Z)"
        by (metis ppath_dioid.mult_isol)
      also have "\<dots> \<subseteq> pp_prod X (\<Union> {Y. pp_prod X Y \<subseteq> Z})"
        by (simp add: rimp_ppath_def)
      also have "\<dots> = \<Union> {pp_prod X Y | Y. pp_prod X Y \<subseteq> Z}"
        by (auto simp only: pp_prod_def)
      finally show "pp_prod X Y \<subseteq> Z"
        by auto
    qed
qed

interpretation ppath_action_algebra: action_algebra "op \<union>" "op \<subseteq>" "op \<subset>" pp_prod limp_ppath rimp_ppath pp_one "{}" pp_star
proof
  fix X Y :: "'a ppath set"
  show "pp_one \<union> pp_prod (pp_star X) (pp_star X) \<union> X \<subseteq> pp_star X"
    by (metis Un_least order_refl ppath_kleene_algebra.star_ext ppath_kleene_algebra.star_plus_one ppath_kleene_algebra.star_trans_eq)
  show "pp_one \<union> pp_prod Y Y \<union> X \<subseteq> Y \<longrightarrow> pp_star X \<subseteq> Y"
    by (metis Un_commute le_iff_sup ppath_dioid.add_lub ppath_kleene_algebra.boffa_var ppath_kleene_algebra.star_subdist)
qed


subsection {* The Min-Plus Action Algebra *}

instantiation pnat :: minus
begin

  fun minus_pnat where
    "(pnat x) - (pnat y) = pnat (x - y)"
  | "x - PInfty = 1"
  | "PInfty - (pnat x) = 0"

  instance ..

end

instantiation pnat :: residuated_join_semilattice
begin

  definition residual_r_pnat where
    "(x::pnat) \<rightarrow> y \<equiv> y - x"

  definition residual_l_pnat where
    "(y::pnat) \<leftarrow> x \<equiv> y - x"

  instance
  proof
    fix x y z :: pnat
    show "x \<le> (z \<leftarrow> y) \<longleftrightarrow> x \<cdot> y \<le> z"
      by (cases x, cases y, cases z) (auto simp add: plus_pnat_def times_pnat_def residual_l_pnat_def less_eq_pnat_def zero_pnat_def one_pnat_def)
    show "x \<cdot> y \<le> z \<longleftrightarrow> y \<le> (x \<rightarrow> z)"
      by (cases y, cases x, cases z) (auto simp add: plus_pnat_def times_pnat_def residual_r_pnat_def less_eq_pnat_def zero_pnat_def one_pnat_def)
  qed

end (* instantiation *)

instantiation pnat :: action_algebra
begin

text {* The Kleene star for type~@{typ pnat} has already been defined in theory
@{theory Kleene_Algebra_Models}. *}

  instance
  proof
    fix x y :: pnat
    show "1 + x\<^sup>\<star> \<cdot> x\<^sup>\<star> + x \<le> x\<^sup>\<star>"
      by (metis star_pnat_def zero_pnat_top)
    show "1 + y \<cdot> y + x \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y"
      by (metis join_semilattice_class.add_lub star_pnat_def)
  qed

end (* instantiation *)

end
