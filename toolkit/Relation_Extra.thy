section \<open> Extra Relational Definitions and Theorems \<close>

theory Relation_Extra
  imports "HOL-Library.FuncSet"
begin

text \<open> We set up some nice syntax for heterogeneous relations at the type level \<close>

syntax
  "_rel_type" :: "type \<Rightarrow> type \<Rightarrow> type" (infixr "\<leftrightarrow>" 0)

translations
  (type) "'a \<leftrightarrow> 'b" == (type) "('a \<times> 'b) set"

subsection \<open> Relational Function Operations \<close>

definition rel_apply :: "('a \<leftrightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("_'(_')\<^sub>r" [999,0] 999) where
"rel_apply R x = (if x \<in> Domain(R) then THE y. (x, y) \<in> R else undefined)"

definition rel_domres :: "'a set \<Rightarrow> ('a \<leftrightarrow> 'b) \<Rightarrow> 'a \<leftrightarrow> 'b" (infixr "\<lhd>\<^sub>r" 85) where
"rel_domres A R = {(k, v) \<in> R. k \<in> A}"

definition rel_override :: "('a \<leftrightarrow> 'b) \<Rightarrow> ('a \<leftrightarrow> 'b) \<Rightarrow> 'a \<leftrightarrow> 'b" (infixl "+\<^sub>r" 65) where
"rel_override R S = (- Domain S) \<lhd>\<^sub>r R \<union> S"

definition rel_update :: "('a \<leftrightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<leftrightarrow> 'b" where
"rel_update R k v = rel_override R {(k, v)}"

subsection \<open> Domain Restriction \<close>

lemma Domain_rel_domres [simp]: "Domain (A \<lhd>\<^sub>r R) = A \<inter> Domain(R)"
  by (auto simp add: rel_domres_def)

lemma rel_domres_empty [simp]: "{} \<lhd>\<^sub>r R = {}"
  by (simp add: rel_domres_def)

lemma rel_domres_UNIV [simp]: "UNIV \<lhd>\<^sub>r R = R"
  by (simp add: rel_domres_def)

lemma rel_domres_nil [simp]: "A \<lhd>\<^sub>r {} = {}"
  by (simp add: rel_domres_def)

lemma rel_domres_inter [simp]: "A \<lhd>\<^sub>r B \<lhd>\<^sub>r R = (A \<inter> B) \<lhd>\<^sub>r R"
  by (auto simp add: rel_domres_def)

subsection \<open> Relational Override \<close>

interpretation rel_override_monoid: monoid_add "(+\<^sub>r)" "{}"
  by (unfold_locales, simp_all add: rel_override_def, auto simp add: rel_domres_def)

lemma Domain_rel_override [simp]: "Domain (R +\<^sub>r S) = Domain(R) \<union> Domain(S)"
  by (auto simp add: rel_override_def Domain_Un_eq)

lemma Range_rel_override: "Range(R +\<^sub>r S) \<subseteq> Range(R) \<union> Range(S)"
  by (auto simp add: rel_override_def rel_domres_def)

subsection \<open> Functional Relations \<close>

definition functional :: "('a \<leftrightarrow> 'b) \<Rightarrow> bool" where
"functional g = inj_on fst g"

lemma functional_algebraic: "functional R \<longleftrightarrow> R\<inverse> O R \<subseteq> Id"
  apply (auto simp add: functional_def subset_iff relcomp_unfold)
  using inj_on_eq_iff apply fastforce
  apply (metis inj_onI surjective_pairing)
  done

lemma functional_determine: "\<lbrakk> functional R; (x, y) \<in> R; (x, z) \<in> R \<rbrakk> \<Longrightarrow> y = z"
  by (auto simp add: functional_algebraic subset_iff relcomp_unfold)

lemma functional_apply: 
  assumes "functional R" "(x, y) \<in> R"
  shows "R(x)\<^sub>r = y"
  by (metis (no_types, lifting) Domain.intros DomainE assms(1) assms(2) functional_determine rel_apply_def theI_unique)  

lemma functional_elem:
  assumes "functional R" "x \<in> Domain(R)"
  shows "(x, R(x)\<^sub>r) \<in> R"
  using assms(1) assms(2) functional_apply by fastforce

lemma functional_empty [simp]: "functional {}"
  by (simp add: functional_def)

lemma functional_override [intro]: "\<lbrakk> functional R; functional S \<rbrakk> \<Longrightarrow> functional (R +\<^sub>r S)"
  by (auto simp add: functional_algebraic rel_override_def rel_domres_def)

definition functional_list :: "('a \<times> 'b) list \<Rightarrow> bool" where
"functional_list xs = (\<forall> x y z. ListMem (x,y) xs \<and> ListMem (x,z) xs \<longrightarrow> y = z)"

lemma functional_insert [simp]: "functional (insert (x,y) g) \<longleftrightarrow> (g``{x} \<subseteq> {y} \<and> functional g)"
  by (auto simp add:functional_def inj_on_def image_def)

lemma functional_list_nil[simp]: "functional_list []"
  by (simp add:functional_list_def ListMem_iff)

lemma functional_list: "functional_list xs \<longleftrightarrow> functional (set xs)"
  apply (induct xs)
   apply (simp add:functional_def)
  apply (simp add:functional_def functional_list_def ListMem_iff)
  apply (safe)
         apply (force)
        apply (force)
       apply (force)
      apply (force)
     apply (force)
    apply (force)
   apply (force)
  apply (force)
  done

definition fun_rel :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<leftrightarrow> 'b)" where
"fun_rel f = {(x, y). y = f x}"

lemma functional_fun_rel: "functional (fun_rel f)"
  by (simp add: fun_rel_def functional_def)
     (metis (mono_tags, lifting) Product_Type.Collect_case_prodD inj_onI prod.expand)

lemma rel_apply_fun [simp]: "(fun_rel f)(x)\<^sub>r = f x"
  by (simp add: fun_rel_def rel_apply_def)

subsection \<open> Left-Total Relations\<close>

definition left_totalr_on :: "'a set \<Rightarrow> ('a \<leftrightarrow> 'b) \<Rightarrow> bool" where
"left_totalr_on A R \<longleftrightarrow> (\<forall>x\<in>A. \<exists>y. (x, y) \<in> R)"

abbreviation "left_totalr R \<equiv> left_totalr_on UNIV R"

lemma left_totalr_algebraic: "left_totalr R \<longleftrightarrow> Id \<subseteq> R O R\<inverse>"
  by (auto simp add: left_totalr_on_def)

lemma left_totalr_fun_rel: "left_totalr (fun_rel f)"
  by (simp add: left_totalr_on_def fun_rel_def)

subsection \<open> Relation Sets \<close>

definition rel_typed :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<leftrightarrow> 'b) set" (infixr "\<leftrightarrow>\<^sub>r" 55) where
"rel_typed A B = {R. Domain(R) \<subseteq> A \<and> Range(R) \<subseteq> B}"

lemma rel_typed_intro: "\<lbrakk> Domain(R) \<subseteq> A; Range(R) \<subseteq> B \<rbrakk> \<Longrightarrow> R \<in> A \<leftrightarrow>\<^sub>r B"
  by (simp add: rel_typed_def)

definition rel_pfun :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<leftrightarrow> 'b) set" (infixr "\<rightharpoonup>\<^sub>r" 55) where
"rel_pfun A B = {R. R \<in> A \<leftrightarrow>\<^sub>r B \<and> functional R}"

lemma rel_pfun_intro: "\<lbrakk> R \<in> A \<leftrightarrow>\<^sub>r B; functional R \<rbrakk> \<Longrightarrow> R \<in> A \<rightharpoonup>\<^sub>r B"
  by (simp add: rel_pfun_def)

definition rel_tfun :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<leftrightarrow> 'b) set" (infixr "\<rightarrow>\<^sub>r" 55) where
"rel_tfun A B = {R. R \<in> A \<rightharpoonup>\<^sub>r B \<and> left_totalr R}"

definition rel_ffun :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<leftrightarrow> 'b) set" where
"rel_ffun A B = {R. R \<in> A \<rightharpoonup>\<^sub>r B \<and> finite(Domain R)}"

subsection \<open> Closure Properties \<close>

text \<open> These can be seen as typing rules for relational functions \<close>

named_theorems rclos

lemma rel_ffun_is_pfun [rclos]: "R \<in> rel_ffun A B \<Longrightarrow> R \<in> A \<rightharpoonup>\<^sub>r B"
  by (simp add: rel_ffun_def)

lemma rel_tfun_is_pfun [rclos]: "R \<in> A \<rightarrow>\<^sub>r B \<Longrightarrow> R \<in> A \<rightharpoonup>\<^sub>r B"
  by (simp add: rel_tfun_def)

lemma rel_pfun_is_typed [rclos]: "R \<in> A \<rightharpoonup>\<^sub>r B \<Longrightarrow> R \<in> A \<leftrightarrow>\<^sub>r B"
  by (simp add: rel_pfun_def)

lemma rel_ffun_empty [rclos]: "{} \<in> rel_ffun A B"
  by (simp add: rel_ffun_def rel_pfun_def rel_typed_def)

lemma rel_pfun_apply [rclos]: "\<lbrakk> x \<in> Domain(R); R \<in> A \<rightharpoonup>\<^sub>r B \<rbrakk> \<Longrightarrow> R(x)\<^sub>r \<in> B"
  using functional_apply by (fastforce simp add: rel_pfun_def rel_typed_def)

lemma rel_tfun_apply [rclos]: "\<lbrakk> x \<in> A; R \<in> A \<rightarrow>\<^sub>r B \<rbrakk> \<Longrightarrow> R(x)\<^sub>r \<in> B"
  by (metis (no_types, lifting) Domain_iff iso_tuple_UNIV_I left_totalr_on_def mem_Collect_eq rel_pfun_apply rel_tfun_def)

lemma rel_typed_insert [rclos]: "\<lbrakk> R \<in> A \<leftrightarrow>\<^sub>r B; x \<in> A; y \<in> B \<rbrakk> \<Longrightarrow> insert (x, y) R \<in> A \<leftrightarrow>\<^sub>r B"
  by (simp add: rel_typed_def)

lemma rel_pfun_insert [rclos]: "\<lbrakk> R \<in> A \<rightharpoonup>\<^sub>r B; x \<in> A; y \<in> B; x \<notin> Domain(R) \<rbrakk> \<Longrightarrow> insert (x, y) R \<in> A \<rightharpoonup>\<^sub>r B"
  by (auto intro: rclos simp add: rel_pfun_def)

lemma rel_pfun_override [rclos]: "\<lbrakk> R \<in> A \<rightharpoonup>\<^sub>r B; S \<in> A \<rightharpoonup>\<^sub>r B \<rbrakk> \<Longrightarrow> (R +\<^sub>r S) \<in> A \<rightharpoonup>\<^sub>r B"
  apply (rule rel_pfun_intro)
   apply (rule rel_typed_intro)
  apply (auto simp add: rel_pfun_def rel_typed_def)
  apply (metis (no_types, hide_lams) Range.simps Range_Un_eq Range_rel_override Un_iff rev_subsetD)
  done

end