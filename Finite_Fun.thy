(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: Finite_Fun.thy                                                       *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section \<open> Finite Functions \<close>

theory Finite_Fun
imports Map_Extra Partial_Fun
begin

subsection \<open> Finite function type and operations \<close>

typedef ('a, 'b) ffun = "{f :: ('a, 'b) pfun. finite(pdom(f))}"
  morphisms pfun_of Abs_pfun
  by (rule_tac x="{}\<^sub>p" in exI, auto)

type_notation ffun (infixr "\<Zffun>" 1)

setup_lifting type_definition_ffun

lift_definition ffun_app :: "'a \<Zffun> 'b \<Rightarrow> 'a \<Rightarrow> 'b" ("_'(_')\<^sub>f" [999,0] 999) is "pfun_app" .

lift_definition ffun_upd :: "'a \<Zffun> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Zffun> 'b" is "pfun_upd" by simp

lift_definition fdom :: "'a \<Zffun> 'b \<Rightarrow> 'a set" is pdom .

lift_definition fran :: "'a \<Zffun> 'b \<Rightarrow> 'b set" is pran .

lift_definition ffun_comp :: "('b, 'c) ffun \<Rightarrow> 'a \<Zffun> 'b \<Rightarrow> ('a, 'c) ffun" (infixl "\<circ>\<^sub>f" 55) is pfun_comp by auto

lift_definition ffun_member :: "'a \<times> 'b \<Rightarrow> 'a \<Zffun> 'b \<Rightarrow> bool" (infix "\<in>\<^sub>f" 50) is "(\<in>\<^sub>p)" .

lift_definition fdom_res :: "'a set \<Rightarrow> 'a \<Zffun> 'b \<Rightarrow> 'a \<Zffun> 'b" (infixr "\<lhd>\<^sub>f" 85)
is pdom_res by simp

lift_definition fran_res :: "'a \<Zffun> 'b \<Rightarrow> 'b set \<Rightarrow> 'a \<Zffun> 'b" (infixl "\<rhd>\<^sub>f" 85)
is pran_res by simp

lift_definition ffun_graph :: "'a \<Zffun> 'b \<Rightarrow> ('a \<times> 'b) set" is pfun_graph .

lift_definition graph_ffun :: "('a \<times> 'b) set \<Rightarrow> 'a \<Zffun> 'b" is
  "\<lambda> R. if (finite (Domain R)) then graph_pfun R else pempty"
  by (simp add: finite_Domain) (meson pdom_graph_pfun rev_finite_subset)

instantiation ffun :: (type, type) zero
begin
lift_definition zero_ffun :: "'a \<Zffun> 'b" is "0" by simp
instance ..
end

abbreviation fempty :: "'a \<Zffun> 'b" ("{}\<^sub>f")
where "fempty \<equiv> 0"

instantiation ffun :: (type, type) oplus
begin
lift_definition oplus_ffun :: "'a \<Zffun> 'b \<Rightarrow> 'a \<Zffun> 'b \<Rightarrow> 'a \<Zffun> 'b" is "(\<oplus>)" by simp
instance ..
end

instantiation ffun :: (type, type) minus
begin
lift_definition minus_ffun :: "'a \<Zffun> 'b \<Rightarrow> 'a \<Zffun> 'b \<Rightarrow> 'a \<Zffun> 'b" is "(-)"
  by (metis Dom_pfun_graph finite_Diff finite_Domain pdom_pfun_graph_finite pfun_graph_minus)
instance ..
end

instantiation ffun :: (type, type) inf
begin
lift_definition inf_ffun :: "'a \<Zffun> 'b \<Rightarrow> 'a \<Zffun> 'b \<Rightarrow> 'a \<Zffun> 'b" is inf
  by (meson finite_Int infinite_super pdom_inter)
instance ..
end

abbreviation ffun_inter :: "'a \<Zffun> 'b \<Rightarrow> 'a \<Zffun> 'b \<Rightarrow> 'a \<Zffun> 'b" (infixl "\<inter>\<^sub>f" 80)
where "ffun_inter \<equiv> inf"

instantiation ffun :: (type, type) order
begin
  lift_definition less_eq_ffun :: "'a \<Zffun> 'b \<Rightarrow> 'a \<Zffun> 'b \<Rightarrow> bool" is
  "\<lambda> f g. f \<subseteq>\<^sub>p g" .
  lift_definition less_ffun :: "'a \<Zffun> 'b \<Rightarrow> 'a \<Zffun> 'b \<Rightarrow> bool" is
  "\<lambda> f g. f < g" .
instance
  by (intro_classes, (transfer, auto)+)
end

abbreviation ffun_subset :: "'a \<Zffun> 'b \<Rightarrow> 'a \<Zffun> 'b \<Rightarrow> bool" (infix "\<subset>\<^sub>f" 50)
where "ffun_subset \<equiv> less"

abbreviation ffun_subset_eq :: "'a \<Zffun> 'b \<Rightarrow> 'a \<Zffun> 'b \<Rightarrow> bool" (infix "\<subseteq>\<^sub>f" 50)
where "ffun_subset_eq \<equiv> less_eq"

instance ffun :: (type, type) semilattice_inf
  by (intro_classes, (transfer, auto)+)

lemma ffun_subset_eq_least [simp]:
  "{}\<^sub>f \<subseteq>\<^sub>f f"
  by (transfer, auto)

instantiation ffun :: (type, type) size
begin

definition size_ffun :: "'a \<Zffun> 'b \<Rightarrow> nat" where
[simp]: "size_ffun f = card (fdom f)"

instance ..

end

syntax
  "_FfunUpd"  :: "['a \<Zffun> 'b, maplets] => 'a \<Zffun> 'b" ("_'(_')\<^sub>f" [900,0]900)
  "_Ffun"     :: "maplets => 'a \<Zffun> 'b"            ("(1{_}\<^sub>f)")

translations
  "_FfunUpd m (_Maplets xy ms)"  == "_FfunUpd (_FfunUpd m xy) ms"
  "_FfunUpd m (_maplet  x y)"    == "CONST ffun_upd m x y"
  "_Ffun ms"                     => "_FfunUpd (CONST fempty) ms"
  "_Ffun (_Maplets ms1 ms2)"     <= "_FfunUpd (_Ffun ms1) ms2"
  "_Ffun ms"                     <= "_FfunUpd (CONST fempty) ms"

subsection \<open> Algebraic laws \<close>

lemma ffun_comp_assoc: "f \<circ>\<^sub>f (g \<circ>\<^sub>f h) = (f \<circ>\<^sub>f g) \<circ>\<^sub>f h"
  by (transfer, simp add: pfun_comp_assoc)

lemma ffun_override_dist_comp:
  "(f \<oplus> g) \<circ>\<^sub>f h = (f \<circ>\<^sub>f h) \<oplus> (g \<circ>\<^sub>f h)"
  by (transfer, simp add: pfun_override_dist_comp)

lemma ffun_minus_unit [simp]:
  fixes f :: "'a \<Zffun> 'b"
  shows "f - 0 = f"
  by (transfer, simp)

lemma ffun_minus_zero [simp]:
  fixes f :: "'a \<Zffun> 'b"
  shows "0 - f = 0"
  by (transfer, simp)

lemma ffun_minus_self [simp]:
  fixes f :: "'a \<Zffun> 'b"
  shows "f - f = 0"
  by (transfer, simp)

instantiation ffun :: (type, type) override
begin
  lift_definition compatible_ffun :: "'a \<Zffun> 'b \<Rightarrow> 'a \<Zffun> 'b \<Rightarrow> bool" is compatible .


instance
  by (intro_classes; transfer, simp_all add: compatible_sym override_assoc override_comm)
     (transfer, simp add: override_compat_iff)+
end
  
lemma compatible_ffun_alt_def: "R ## S = ((fdom R) \<lhd>\<^sub>f S = (fdom S) \<lhd>\<^sub>f R)"
  by (transfer, simp add: compatible_pfun_def)

lemma ffun_indep_compat: "fdom(f) \<inter> fdom(g) = {} \<Longrightarrow> f ## g"
  by (transfer, simp add: pfun_indep_compat)

lemma ffun_override_commute:
  "fdom(f) \<inter> fdom(g) = {} \<Longrightarrow> f \<oplus> g = g \<oplus> f"
  by (meson ffun_indep_compat override_comm)

lemma ffun_minus_override_commute:
  "fdom(g) \<inter> fdom(h) = {} \<Longrightarrow> (f - g) \<oplus> h = (f \<oplus> h) - g"
  by (transfer, simp add: pfun_minus_override_commute)

lemma ffun_override_minus:
  "f \<subseteq>\<^sub>f g \<Longrightarrow> (g - f) \<oplus> f = g"
  by (transfer, simp add: pfun_override_minus)

lemma ffun_minus_common_subset:
  "\<lbrakk> h \<subseteq>\<^sub>f f; h \<subseteq>\<^sub>f g \<rbrakk> \<Longrightarrow> (f - h = g - h) = (f = g)"
  by (transfer, simp add: pfun_minus_common_subset)

lemma ffun_minus_override:
  "fdom(f) \<inter> fdom(g) = {} \<Longrightarrow> (f \<oplus> g) - g = f"
  by (transfer, simp add: pfun_minus_override)

lemma ffun_override_pos: "x \<oplus> y = {}\<^sub>f \<Longrightarrow> x = {}\<^sub>f"
  by (transfer, simp add: pfun_override_pos)

lemma ffun_le_override: "fdom x \<inter> fdom y = {} \<Longrightarrow> x \<le> x \<oplus> y"
  by (transfer, simp add: pfun_le_override)

subsection \<open> Membership, application, and update \<close>

lemma ffun_ext: "\<lbrakk> \<And> x y. (x, y) \<in>\<^sub>f f \<longleftrightarrow> (x, y) \<in>\<^sub>f g \<rbrakk> \<Longrightarrow> f = g"
  by (transfer, simp add: pfun_ext)

lemma ffun_member_alt_def:
  "(x, y) \<in>\<^sub>f f \<longleftrightarrow> (x \<in> fdom f \<and> f(x)\<^sub>f = y)"
  by (transfer, simp add: pfun_member_alt_def)

lemma ffun_member_override:
  "(x, y) \<in>\<^sub>f f \<oplus> g \<longleftrightarrow> ((x \<notin> fdom(g) \<and> (x, y) \<in>\<^sub>f f) \<or> (x, y) \<in>\<^sub>f g)"
  by (transfer, simp add: pfun_member_override)

lemma ffun_member_minus:
  "(x, y) \<in>\<^sub>f f - g \<longleftrightarrow> (x, y) \<in>\<^sub>f f \<and> (\<not> (x, y) \<in>\<^sub>f g)"
  by (transfer, simp add: pfun_member_minus)

lemma ffun_app_upd_1 [simp]: "x = y \<Longrightarrow> (f(x \<mapsto> v)\<^sub>f)(y)\<^sub>f = v"
  by (transfer, simp)

lemma ffun_app_upd_2 [simp]: "x \<noteq> y \<Longrightarrow> (f(x \<mapsto> v)\<^sub>f)(y)\<^sub>f = f(y)\<^sub>f"
  by (transfer, simp)

lemma ffun_upd_ext [simp]: "x \<in> fdom(f) \<Longrightarrow> f(x \<mapsto> f(x)\<^sub>f)\<^sub>f = f"
  by (transfer, simp)

lemma ffun_app_add [simp]: "x \<in> fdom(g) \<Longrightarrow> (f \<oplus> g)(x)\<^sub>f = g(x)\<^sub>f"
  by (transfer, simp)

lemma ffun_upd_add [simp]: "f \<oplus> g(x \<mapsto> v)\<^sub>f = (f \<oplus> g)(x \<mapsto> v)\<^sub>f"
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

lemma fdom_plus [simp]: "fdom (f \<oplus> g) = fdom f \<union> fdom g"
  by (transfer, auto)

lemma fdom_inter: "fdom (f \<inter>\<^sub>f g) \<subseteq> fdom f \<inter> fdom g"
  by (transfer, meson pdom_inter)

lemma fdom_comp [simp]: "fdom (g \<circ>\<^sub>f f) = fdom (f \<rhd>\<^sub>f fdom g)"
  by (transfer, auto)

lemma fdom_upd [simp]: "fdom (f(k \<mapsto> v)\<^sub>f) = insert k (fdom f)"
  by (transfer, simp)

lemma fdom_fdom_res [simp]: "fdom (A \<lhd>\<^sub>f f) = A \<inter> fdom(f)"
  by (transfer, auto)

lemma ffun_fdom_antires_upd [simp]:
  "k \<in> A \<Longrightarrow> ((- A) \<lhd>\<^sub>f m)(k \<mapsto> v)\<^sub>f = ((- (A - {k})) \<lhd>\<^sub>f m)(k \<mapsto> v)\<^sub>f"
  by (transfer, simp)

lemma fdom_res_UNIV [simp]: "UNIV \<lhd>\<^sub>f f = f"
  by (transfer, simp)

lemma fdom_graph_ffun [simp]:
  "\<lbrakk> functional R; finite (Domain R) \<rbrakk> \<Longrightarrow> fdom (graph_ffun R) = Domain R"
  by (transfer, simp add: Domain_fst graph_map_dom)

lemma pdom_pfun_of [simp]: "pdom (pfun_of f) = fdom f"
  by (transfer, simp)

lemma finite_pdom_ffun [simp]: "finite (pdom (pfun_of f))"
  by (transfer, simp)

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

lemma fdom_res_upd_in [simp]:
  "k \<in> A \<Longrightarrow> A \<lhd>\<^sub>f f(k \<mapsto> v)\<^sub>f = (A \<lhd>\<^sub>f f)(k \<mapsto> v)\<^sub>f"
  by (transfer, auto)

lemma fdom_res_upd_out [simp]:
  "k \<notin> A \<Longrightarrow> A \<lhd>\<^sub>f f(k \<mapsto> v)\<^sub>f = A \<lhd>\<^sub>f f"
  by (transfer, auto)

lemma fdom_res_override [simp]: "A \<lhd>\<^sub>f (f \<oplus> g) = (A \<lhd>\<^sub>f f) \<oplus> (A \<lhd>\<^sub>f g)"
  by (metis fdom_res.rep_eq pdom_res_override pfun_of_inject oplus_ffun.rep_eq)

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

lemma fran_res_override: "(f \<oplus> g) \<rhd>\<^sub>f A \<subseteq>\<^sub>f (f \<rhd>\<^sub>f A) \<oplus> (g \<rhd>\<^sub>f A)"
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

subsection \<open> Conversions \<close>

lift_definition list_ffun :: "'a list \<Rightarrow> nat \<Zffun> 'a" is
list_pfun by simp

lemma fdom_list_ffun [simp]: "fdom (list_ffun xs) = {1..length xs}"
  by (transfer, auto)

lemma fran_list_ffun [simp]: "fran (list_ffun xs) = set xs"
  by (transfer, simp)

lemma ffun_app_list_ffun: "\<lbrakk> 0 < i; i < length xs \<rbrakk> \<Longrightarrow> (list_ffun xs)(i)\<^sub>f = xs ! (i - 1)"
  by (transfer, simp add: pfun_app_list_pfun)

lemma range_list_ffun: "range list_ffun = {f. \<exists> i. fdom(f) = {1..i}}"
  by (transfer, auto simp add: range_list_pfun)

subsection \<open> Finite Function Lens \<close>

definition ffun_lens :: "'a \<Rightarrow> ('b \<Longrightarrow> 'a \<Zffun> 'b)" where
[lens_defs]: "ffun_lens i = \<lparr> lens_get = \<lambda> s. s(i)\<^sub>f, lens_put = \<lambda> s v. s(i \<mapsto> v)\<^sub>f \<rparr>"

lemma ffun_lens_mwb [simp]: "mwb_lens (ffun_lens i)"
  by (unfold_locales, simp_all add: ffun_lens_def)

lemma ffun_lens_src: "\<S>\<^bsub>ffun_lens i\<^esub> = {f. i \<in> fdom(f)}"
  by (auto simp add: lens_defs lens_source_def, metis ffun_upd_ext)

text \<open> Hide implementation details for finite functions \<close>

lifting_update ffun.lifting
lifting_forget ffun.lifting

end