(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: Finite_Fun.thy                                                       *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section \<open> Finite Functions \<close>

theory Finite_Fun
imports Map_Extra Partial_Fun FSet_Extra
begin

subsection \<open> Finite function type and operations \<close>

typedef ('a, 'b) ffun = "{f :: ('a, 'b) pfun. finite(pdom(f))}"
  morphisms pfun_of Abs_pfun
  by (rule_tac x="{}\<^sub>p" in exI, auto)

setup_lifting type_definition_ffun

lift_definition ffun_app :: "('a, 'b) ffun \<Rightarrow> 'a \<Rightarrow> 'b" ("_'(_')\<^sub>f" [999,0] 999) is "pfun_app" .

lift_definition ffun_upd :: "('a, 'b) ffun \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) ffun" is "pfun_upd" by simp

lift_definition fdom :: "('a, 'b) ffun \<Rightarrow> 'a set" is pdom .

lift_definition fran :: "('a, 'b) ffun \<Rightarrow> 'b set" is pran .

lift_definition ffun_comp :: "('b, 'c) ffun \<Rightarrow> ('a, 'b) ffun \<Rightarrow> ('a, 'c) ffun" (infixl "\<circ>\<^sub>f" 55) is pfun_comp by auto

lift_definition ffun_member :: "'a \<times> 'b \<Rightarrow> ('a, 'b) ffun \<Rightarrow> bool" (infix "\<in>\<^sub>f" 50) is "(\<in>\<^sub>p)" .

lift_definition fdom_res :: "'a set \<Rightarrow> ('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun" (infixl "\<lhd>\<^sub>f" 85)
is "pdom_res" by simp

lift_definition fran_res :: "('a, 'b) ffun \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) ffun" (infixl "\<rhd>\<^sub>f" 85)
is pran_res by simp

lift_definition ffun_graph :: "('a, 'b) ffun \<Rightarrow> ('a \<times> 'b) set" is pfun_graph .

lift_definition graph_ffun :: "('a \<times> 'b) set \<Rightarrow> ('a, 'b) ffun" is
  "\<lambda> R. if (finite (Domain R)) then graph_pfun R else pempty"
  by (simp add: finite_Domain)

instantiation ffun :: (type, type) zero
begin
lift_definition zero_ffun :: "('a, 'b) ffun" is "0" by simp
instance ..
end

abbreviation fempty :: "('a, 'b) ffun" ("{}\<^sub>f")
where "fempty \<equiv> 0"

instantiation ffun :: (type, type) plus
begin
lift_definition plus_ffun :: "('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun" is "(+)" by simp
instance ..
end

instantiation ffun :: (type, type) minus
begin
lift_definition minus_ffun :: "('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun" is "(-)"
  by (metis finite_Diff finite_Domain pdom_graph_pfun pdom_pfun_graph_finite pfun_graph_inv pfun_graph_minus)
instance ..
end

instance ffun :: (type, type) monoid_add
  by (intro_classes, (transfer, simp add: add.assoc)+)

instantiation ffun :: (type, type) inf
begin
lift_definition inf_ffun :: "('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun" is inf
  by (meson finite_Int infinite_super pdom_inter)
instance ..
end

abbreviation ffun_inter :: "('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun" (infixl "\<inter>\<^sub>f" 80)
where "ffun_inter \<equiv> inf"

instantiation ffun :: (type, type) order
begin
  lift_definition less_eq_ffun :: "('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun \<Rightarrow> bool" is
  "\<lambda> f g. f \<subseteq>\<^sub>p g" .
  lift_definition less_ffun :: "('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun \<Rightarrow> bool" is
  "\<lambda> f g. f < g" .
instance
  by (intro_classes, (transfer, auto)+)
end

abbreviation ffun_subset :: "('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun \<Rightarrow> bool" (infix "\<subset>\<^sub>f" 50)
where "ffun_subset \<equiv> less"

abbreviation ffun_subset_eq :: "('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun \<Rightarrow> bool" (infix "\<subseteq>\<^sub>f" 50)
where "ffun_subset_eq \<equiv> less_eq"

instance ffun :: (type, type) semilattice_inf
  by (intro_classes, (transfer, auto)+)

lemma ffun_subset_eq_least [simp]:
  "{}\<^sub>f \<subseteq>\<^sub>f f"
  by (transfer, auto)

syntax
  "_FfunUpd"  :: "[('a, 'b) ffun, maplets] => ('a, 'b) ffun" ("_'(_')\<^sub>f" [900,0]900)
  "_Ffun"     :: "maplets => ('a, 'b) ffun"            ("(1{_}\<^sub>f)")

translations
  "_FfunUpd m (_Maplets xy ms)"  == "_FfunUpd (_FfunUpd m xy) ms"
  "_FfunUpd m (_maplet  x y)"    == "CONST ffun_upd m x y"
  "_Ffun ms"                     => "_FfunUpd (CONST fempty) ms"
  "_Ffun (_Maplets ms1 ms2)"     <= "_FfunUpd (_Ffun ms1) ms2"
  "_Ffun ms"                     <= "_FfunUpd (CONST fempty) ms"

subsection \<open> Algebraic laws \<close>

lemma ffun_comp_assoc: "f \<circ>\<^sub>f (g \<circ>\<^sub>f h) = (f \<circ>\<^sub>f g) \<circ>\<^sub>f h"
  by (transfer, simp add: pfun_comp_assoc)

lemma pfun_override_dist_comp:
  "(f + g) \<circ>\<^sub>f h = (f \<circ>\<^sub>f h) + (g \<circ>\<^sub>f h)"
  by (transfer, simp add: pfun_override_dist_comp)

lemma ffun_minus_unit [simp]:
  fixes f :: "('a, 'b) ffun"
  shows "f - 0 = f"
  by (transfer, simp)

lemma ffun_minus_zero [simp]:
  fixes f :: "('a, 'b) ffun"
  shows "0 - f = 0"
  by (transfer, simp)

lemma ffun_minus_self [simp]:
  fixes f :: "('a, 'b) ffun"
  shows "f - f = 0"
  by (transfer, simp)

lemma ffun_plus_commute:
  "fdom(f) \<inter> fdom(g) = {} \<Longrightarrow> f + g = g + f"
  by (transfer, metis pfun_plus_commute)

lemma ffun_minus_plus_commute:
  "fdom(g) \<inter> fdom(h) = {} \<Longrightarrow> (f - g) + h = (f + h) - g"
  by (transfer, simp add: pfun_minus_plus_commute)

lemma ffun_plus_minus:
  "f \<subseteq>\<^sub>f g \<Longrightarrow> (g - f) + f = g"
  by (transfer, simp add: pfun_plus_minus)

lemma ffun_minus_common_subset:
  "\<lbrakk> h \<subseteq>\<^sub>f f; h \<subseteq>\<^sub>f g \<rbrakk> \<Longrightarrow> (f - h = g - h) = (f = g)"
  by (transfer, simp add: pfun_minus_common_subset)

lemma ffun_minus_plus:
  "fdom(f) \<inter> fdom(g) = {} \<Longrightarrow> (f + g) - g = f"
  by (transfer, simp add: pfun_minus_plus)

instantiation ffun :: (type, type) pas
begin
  lift_definition compat_ffun :: "('a, 'b) ffun \<Rightarrow> ('a, 'b) ffun \<Rightarrow> bool" is
  "\<lambda> f g. f ## g" .
instance proof
  fix x y z :: "('a, 'b) ffun"
  assume "x ## y"
  thus "y ## x"
    by (transfer, simp add: compat_comm)
  assume a:"x ## y" "x + y ## z"
  thus "x ## y + z"
    by (transfer, simp add: compat_assoc) 
  from a show "y ## z"
    by (transfer, metis compat_property)
  from a show "x + y + z = x + (y + z)"
    by (simp add: add.assoc)
next
  fix x y :: "('a, 'b) ffun"
  assume "x ## y"
  thus "x + y = y + x"
    by (transfer, meson compat_pfun_def pfun_plus_commute)
qed
end

lemma compat_ffun_alt_def: "f ## g = (fdom(f) \<inter> fdom(g) = {})"
  by (transfer, simp add: compat_pfun_def)

instance ffun :: (type, type) pam
proof
  fix x :: "('a, 'b) ffun"
  show "{}\<^sub>f ## x"
    by (transfer, simp)
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
    by (transfer, metis gr_minus_cancel)
next
  fix x y :: "('a, 'b) ffun"
  show "x + y = {}\<^sub>f \<Longrightarrow> x = {}\<^sub>f"
    by (transfer) (simp add: positive_left)
qed

lemma ffun_compat_minus:
  fixes x y :: "('a, 'b) ffun"
  assumes "y \<subseteq>\<^sub>f x"
  shows "y ## x - y"
  by (metis assms compat_ffun.rep_eq less_eq_ffun.rep_eq minus_ffun.rep_eq pfun_compat_minus)

instance ffun :: (type, type) sep_alg
proof
  show 1: "\<And> x y :: ('a, 'b) ffun. (x \<subseteq>\<^sub>f y) = (x \<preceq>\<^sub>G y)"
    by (simp add: green_preorder_def compat_ffun_def)
       (metis ffun_compat_minus compat_ffun.rep_eq ffun_plus_minus green_preorder_def less_eq_def less_eq_ffun.rep_eq plus_ffun.rep_eq plus_pcomm)
  show "\<And>x y :: ('a, 'b) ffun. (x \<subset>\<^sub>f y) = (x \<prec>\<^sub>G y)"
    by (simp add: "1" green_strict_def less_le_not_le)
  show "\<And>x y :: ('a, 'b) ffun. y \<subseteq>\<^sub>f x \<Longrightarrow> x - y = x -\<^sub>G y"
    apply (rule sym)
    thm 1[THEN sym]
    apply (auto simp add: green_subtract_def 1[THEN sym])
     apply (rule the_equality)
      apply (auto simp add: ffun_compat_minus)
    using ffun_compat_minus ffun_plus_minus plus_pcomm apply fastforce
    apply (metis compat_comm compat_ffun_alt_def ffun_minus_plus plus_pcomm)
    done
qed

instance ffun :: (type, type) sep_alg_cancel_pos .. 

subsection \<open> Membership, application, and update \<close>

lemma ffun_ext: "\<lbrakk> \<And> x y. (x, y) \<in>\<^sub>f f \<longleftrightarrow> (x, y) \<in>\<^sub>f g \<rbrakk> \<Longrightarrow> f = g"
  by (transfer, simp add: pfun_ext)

lemma ffun_member_alt_def:
  "(x, y) \<in>\<^sub>f f \<longleftrightarrow> (x \<in> fdom f \<and> f(x)\<^sub>f = y)"
  by (transfer, simp add: pfun_member_alt_def)

lemma ffun_member_plus:
  "(x, y) \<in>\<^sub>f f + g \<longleftrightarrow> ((x \<notin> fdom(g) \<and> (x, y) \<in>\<^sub>f f) \<or> (x, y) \<in>\<^sub>f g)"
  by (transfer, simp add: pfun_member_plus)

lemma ffun_member_minus:
  "(x, y) \<in>\<^sub>f f - g \<longleftrightarrow> (x, y) \<in>\<^sub>f f \<and> (\<not> (x, y) \<in>\<^sub>f g)"
  by (transfer, simp add: pfun_member_minus)

lemma ffun_app_upd_1 [simp]: "x = y \<Longrightarrow> (f(x \<mapsto> v)\<^sub>f)(y)\<^sub>f = v"
  by (transfer, simp)

lemma ffun_app_upd_2 [simp]: "x \<noteq> y \<Longrightarrow> (f(x \<mapsto> v)\<^sub>f)(y)\<^sub>f = f(y)\<^sub>f"
  by (transfer, simp)

lemma ffun_app_add [simp]: "x \<in> fdom(g) \<Longrightarrow> (f + g)(x)\<^sub>f = g(x)\<^sub>f"
  by (transfer, simp)

lemma ffun_upd_add [simp]: "f + g(x \<mapsto> v)\<^sub>f = (f + g)(x \<mapsto> v)\<^sub>f"
  by (transfer, simp)

lemma ffun_upd_twice [simp]: "f(x \<mapsto> u, x \<mapsto> v)\<^sub>f = f(x \<mapsto> v)\<^sub>f"
  by (transfer, simp)

lemma ffun_upd_comm:
  assumes "x \<noteq> y"
  shows "f(y \<mapsto> u, x \<mapsto> v)\<^sub>f = f(x \<mapsto> v, y \<mapsto> u)\<^sub>f"
  using assms by (transfer, simp add: pfun_upd_comm)

lemma ffun_upd_comm_linorder [simp]:
  fixes x y :: "'a :: linorder"
  assumes "x < y"
  shows "f(y \<mapsto> u, x \<mapsto> v)\<^sub>f = f(x \<mapsto> v, y \<mapsto> u)\<^sub>f"
  using assms by (transfer, auto)

lemma ffun_app_minus [simp]: "x \<notin> fdom g \<Longrightarrow> (f - g)(x)\<^sub>f = f(x)\<^sub>f"
  by (transfer, auto)

lemma ffun_upd_minus [simp]:
  "x \<notin> fdom g \<Longrightarrow> (f - g)(x \<mapsto> v)\<^sub>f = (f(x \<mapsto> v)\<^sub>f - g)"
  by (transfer, auto)

lemma fdom_member_minus_iff [simp]:
  "x \<notin> fdom g \<Longrightarrow> x \<in> fdom(f - g) \<longleftrightarrow> x \<in> fdom(f)"
  by (transfer, simp)

lemma fsubseteq_ffun_upd1 [intro]:
  "\<lbrakk> f \<subseteq>\<^sub>f g; x \<notin> fdom(g) \<rbrakk> \<Longrightarrow> f \<subseteq>\<^sub>f g(x \<mapsto> v)\<^sub>f"
  by (transfer, auto)

lemma fsubseteq_ffun_upd2 [intro]:
  "\<lbrakk> f \<subseteq>\<^sub>f g; x \<notin> fdom(f) \<rbrakk> \<Longrightarrow> f \<subseteq>\<^sub>f g(x \<mapsto> v)\<^sub>f"
  by (transfer, auto)

lemma psubseteq_pfun_upd3 [intro]:
  "\<lbrakk> f \<subseteq>\<^sub>f g; g(x)\<^sub>f = v \<rbrakk> \<Longrightarrow> f \<subseteq>\<^sub>f g(x \<mapsto> v)\<^sub>f"
  by (transfer, auto)

lemma fsubseteq_dom_subset:
  "f \<subseteq>\<^sub>f g \<Longrightarrow> fdom(f) \<subseteq> fdom(g)"
  by (transfer, auto simp add: psubseteq_dom_subset)

lemma fsubseteq_ran_subset:
  "f \<subseteq>\<^sub>f g \<Longrightarrow> fran(f) \<subseteq> fran(g)"
  by (transfer, simp add: psubseteq_ran_subset)

subsection \<open> Domain laws \<close>

lemma fdom_finite [simp]: "finite(fdom(f))"
  by (transfer, simp)

lemma fdom_zero [simp]: "fdom 0 = {}"
  by (transfer, simp)

lemma fdom_plus [simp]: "fdom (f + g) = fdom f \<union> fdom g"
  by (transfer, auto)

lemma fdom_inter: "fdom (f \<inter>\<^sub>f g) \<subseteq> fdom f \<inter> fdom g"
  by (transfer, meson pdom_inter)

lemma fdom_comp [simp]: "fdom (g \<circ>\<^sub>f f) = fdom (f \<rhd>\<^sub>f fdom g)"
  by (transfer, auto)

lemma fdom_upd [simp]: "fdom (f(k \<mapsto> v)\<^sub>f) = insert k (fdom f)"
  by (transfer, simp)

lemma fdom_fdom_res [simp]: "fdom (A \<lhd>\<^sub>f f) = A \<inter> fdom(f)"
  by (transfer, auto)

lemma fdom_graph_ffun [simp]:
  "finite (Domain R) \<Longrightarrow> fdom (graph_ffun R) = Domain R"
  by (transfer, simp add: Domain_fst graph_map_dom)

subsection \<open> Range laws \<close>

lemma fran_zero [simp]: "fran 0 = {}"
  by (transfer, simp)

lemma fran_upd [simp]: "fran (f(k \<mapsto> v)\<^sub>f) = insert v (fran ((- {k}) \<lhd>\<^sub>f f))"
  by (transfer, auto)

lemma fran_fran_res [simp]: "fran (f \<rhd>\<^sub>f A) = fran(f) \<inter> A"
  by (transfer, auto)

lemma fran_comp [simp]: "fran (g \<circ>\<^sub>f f) = fran (fran f \<lhd>\<^sub>f g)"
  by (transfer, auto)

subsection \<open> Domain restriction laws \<close>

lemma fdom_res_zero [simp]: "A \<lhd>\<^sub>f {}\<^sub>f = {}\<^sub>f"
  by (transfer, auto)

lemma fdom_res_empty [simp]:
  "({} \<lhd>\<^sub>f f) = {}\<^sub>f"
  by (transfer, auto)

lemma fdom_res_fdom [simp]:
  "fdom(f) \<lhd>\<^sub>f f = f"
  by (transfer, auto)

lemma pdom_res_upd_in [simp]:
  "k \<in> A \<Longrightarrow> A \<lhd>\<^sub>f f(k \<mapsto> v)\<^sub>f = (A \<lhd>\<^sub>f f)(k \<mapsto> v)\<^sub>f"
  by (transfer, auto)

lemma pdom_res_upd_out [simp]:
  "k \<notin> A \<Longrightarrow> A \<lhd>\<^sub>f f(k \<mapsto> v)\<^sub>f = A \<lhd>\<^sub>f f"
  by (transfer, auto)

lemma fdom_res_override [simp]: "A \<lhd>\<^sub>f (f + g) = (A \<lhd>\<^sub>f f) + (A \<lhd>\<^sub>f g)"
  by (metis fdom_res.rep_eq pdom_res_override pfun_of_inject plus_ffun.rep_eq)

lemma fdom_res_minus [simp]: "A \<lhd>\<^sub>f (f - g) = (A \<lhd>\<^sub>f f) - g"
  by (transfer, auto)

lemma fdom_res_swap: "(A \<lhd>\<^sub>f f) \<rhd>\<^sub>f B = A \<lhd>\<^sub>f (f \<rhd>\<^sub>f B)"
  by (transfer, simp add: pdom_res_swap)

lemma fdom_res_twice [simp]: "A \<lhd>\<^sub>f (B \<lhd>\<^sub>f f) = (A \<inter> B) \<lhd>\<^sub>f f"
  by (transfer, auto)

lemma fdom_res_comp [simp]: "A \<lhd>\<^sub>f (g \<circ>\<^sub>f f) =  g \<circ>\<^sub>f (A \<lhd>\<^sub>f f)"
  by (transfer, simp)

subsection \<open> Range restriction laws \<close>

lemma fran_res_zero [simp]: "{}\<^sub>f \<rhd>\<^sub>f A = {}\<^sub>f"
  by (transfer, auto)

lemma fran_res_upd_1 [simp]: "v \<in> A \<Longrightarrow> f(x \<mapsto> v)\<^sub>f \<rhd>\<^sub>f A = (f \<rhd>\<^sub>f A)(x \<mapsto> v)\<^sub>f"
  by (transfer, auto)

lemma fran_res_upd_2 [simp]: "v \<notin> A \<Longrightarrow> f(x \<mapsto> v)\<^sub>f \<rhd>\<^sub>f A = ((- {x}) \<lhd>\<^sub>f f) \<rhd>\<^sub>f A"
  by (transfer, auto)

lemma fran_res_override: "(f + g) \<rhd>\<^sub>f A \<subseteq>\<^sub>f (f \<rhd>\<^sub>f A) + (g \<rhd>\<^sub>f A)"
  by (transfer, simp add: pran_res_override)

subsection \<open> Graph laws \<close>

lemma ffun_graph_inv: "graph_ffun (ffun_graph f) = f"
  by (transfer, auto simp add: pfun_graph_inv finite_Domain)

lemma ffun_graph_zero: "ffun_graph 0 = {}"
  by (transfer, simp add: pfun_graph_zero)

lemma ffun_graph_minus: "ffun_graph (f - g) = ffun_graph f - ffun_graph g"
  by (transfer, simp add: pfun_graph_minus)

lemma ffun_graph_inter: "ffun_graph (f \<inter>\<^sub>f g) = ffun_graph f \<inter> ffun_graph g"
  by (transfer, simp add: pfun_graph_inter)

text \<open> Hide implementation details for finite functions \<close>

lifting_update ffun.lifting
lifting_forget ffun.lifting

end