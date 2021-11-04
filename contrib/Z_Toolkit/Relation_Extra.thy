section \<open> Relational Universe \<close>

theory Relation_Extra
  imports "HOL-Library.FuncSet" "HOL-Library.AList" List_Extra Overriding
begin

text \<open> This theory develops a universe for a Z-like relational language, including the core 
  operators of the ISO Z metalanguage. Much of this already exists in @{theory HOL.Relation},
  but we need to add some additional functions and sets. It characterises relations, partial
  functions, total functions, and finite functions. \<close>

subsection \<open> Type Syntax\<close>

text \<open> We set up some nice syntax for heterogeneous relations at the type level \<close>

syntax
  "_rel_type" :: "type \<Rightarrow> type \<Rightarrow> type" (infixr "\<leftrightarrow>" 0)

translations
  (type) "'a \<leftrightarrow> 'b" == (type) "('a \<times> 'b) set"

text \<open> Setup pretty printing for homogeneous relations. \<close>

print_translation \<open>
let fun tr' ctx [ Const (@{type_syntax "prod"},_) $ a $ b ] = 
      if a = b then Syntax.const @{type_syntax "rel"} $ a else raise Match;
in [(@{type_syntax "set"},tr')]
end
\<close>

subsection \<open> Notation for types as sets \<close>

definition "TUNIV (a::'a itself) = (UNIV :: 'a set)"

syntax "_tvar" :: "type \<Rightarrow> logic" ("[_]\<^sub>T")
translations "['a]\<^sub>T" == "CONST TUNIV TYPE('a)"

lemma TUNIV_mem [simp]: "x \<in> ['a]\<^sub>T"
  by (simp add: TUNIV_def)

subsection \<open> Relational Function Operations \<close>

text \<open> These functions are all adapted from their ISO Z counterparts. \<close>

definition rel_apply :: "('a \<leftrightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("_'(_')\<^sub>r" [999,0] 999) where
"rel_apply R x = (if (\<exists>! y. (x, y) \<in> R) then THE y. (x, y) \<in> R else undefined)"

text \<open> If there exists a unique @{term "e\<^sub>3"} such that @{term "(e\<^sub>2, e\<^sub>3)"} is in @{term "e\<^sub>1"}, then 
  the value of @{term "e\<^sub>1(e\<^sub>2)\<^sub>r"} is @{term e\<^sub>3}, otherwise each @{term "e\<^sub>1(e\<^sub>2)\<^sub>r"} has a fixed but 
  unknown value (i.e. @{const undefined}). \<close>

definition rel_domres :: "'a set \<Rightarrow> ('a \<leftrightarrow> 'b) \<Rightarrow> 'a \<leftrightarrow> 'b" (infixr "\<lhd>\<^sub>r" 85) where
"rel_domres A R = {p \<in> R. fst p \<in> A}"

lemma rel_domres_math_def: "A \<lhd>\<^sub>r R = {(k, v) \<in> R. k \<in> A}"
  by (auto simp add: rel_domres_def)

text \<open> Domain restriction (@{term "A \<lhd>\<^sub>r R"} contains the set of pairs in @{term R}, such that the
  first element of every such pair in in @{term A}. \<close>

definition rel_ranres :: "('a \<leftrightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a \<leftrightarrow> 'b" (infixl "\<rhd>\<^sub>r" 85) where
"rel_ranres R A = {p \<in> R. snd p \<in> A}"

text \<open> We employ some type class trickery to enable a polymorphic operator for override that can
  instantiate @{typ "'a set"}, which is needed for relational overriding. The following class's
  sole purpose is to allow pairs to be the only valid instantiation element for the set type. \<close>

class pre_restrict =
  fixes cmpt :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  and res :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"

instantiation prod :: (type, type) pre_restrict
begin

text \<open> Relations are compatible is they agree on the values for maplets they both possess. \<close>

definition cmpt_prod :: "('a \<leftrightarrow> 'b) \<Rightarrow> ('a \<leftrightarrow> 'b) \<Rightarrow> bool"
  where [simp]: "cmpt_prod R S = ((Domain R) \<lhd>\<^sub>r S = (Domain S) \<lhd>\<^sub>r R)"
definition res_prod :: "('a \<leftrightarrow> 'b) \<Rightarrow> ('a \<leftrightarrow> 'b) \<Rightarrow> 'a \<leftrightarrow> 'b" 
  where [simp]: "res_prod R S = ((- Domain S) \<lhd>\<^sub>r R) \<union> S"
instance ..
end

instantiation set :: (type) zero
begin

definition zero_set :: "'a set" where
[simp]: "zero_set = {}"

instance ..
end

instantiation set :: (pre_restrict) oplus
begin

definition oplus_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"oplus_set = res"

instance ..

end

definition rel_update :: "('a \<leftrightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<leftrightarrow> 'b" where
"rel_update R k v = R \<oplus> {(k, v)}"

text \<open> Relational update adds a new pair to a relation. \<close>

definition rel_disjoint :: "('a \<leftrightarrow> 'b set) \<Rightarrow> bool" where
"rel_disjoint f = (\<forall> p \<in> f. \<forall> q \<in> f. p \<noteq> q \<longrightarrow> snd p \<inter> snd q = {})"

definition rel_partitions :: "('a \<leftrightarrow> 'b set) \<Rightarrow> 'b set \<Rightarrow> bool" where
"rel_partitions f a = (rel_disjoint f \<and> \<Union> (Range f) = a)"

subsection \<open> Domain laws \<close>

declare Domain_Un_eq [simp]

lemma Domain_Preimage: "Domain P = P\<inverse> `` UNIV"
  by (simp add: Image_def Domain_unfold)

lemma Domain_relcomp [simp]: "Domain (P O Q) = Domain (P \<rhd>\<^sub>r Domain Q)"
  by (force simp add: Domain_iff rel_ranres_def)

lemma Domain_relcomp_conv: "Domain (P O Q) = (P\<inverse> `` Domain(Q))"
  by (simp add: Domain_Preimage converse_relcomp relcomp_Image)

lemma Domain_set: "Domain (set xs) = set (map fst xs)"
  by (simp add: Domain_fst)

subsection \<open> Range laws \<close>

lemma Range_Image: "Range P = P `` UNIV"
  by (simp add: Image_def Range_iff set_eq_iff)

lemma Range_relcomp: "Range (P O Q) = (Q `` Range(P))"
  by (simp add: Range_Image relcomp_Image)

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

lemma rel_domres_compl_disj: "A \<inter> Domain P = {} \<Longrightarrow> (- A) \<lhd>\<^sub>r P = P"
  by (auto simp add: rel_domres_def)

lemma rel_domres_notin_Dom: "k \<notin> Domain(f) \<Longrightarrow> (- {k}) \<lhd>\<^sub>r f = f"
  by (simp add: rel_domres_compl_disj)

lemma rel_domres_Id_on: "A \<lhd>\<^sub>r R = Id_on A O R"
  by (auto simp add: rel_domres_def Id_on_def relcomp_unfold)

lemma rel_domres_insert [simp]:
 "A \<lhd>\<^sub>r insert (k, v) R = (if (k \<in> A) then insert (k, v) (A \<lhd>\<^sub>r R) else A \<lhd>\<^sub>r R)"
  by (auto simp add: rel_domres_def)

lemma rel_domres_insert_set [simp]: "x \<notin> Domain P \<Longrightarrow> (insert x A) \<lhd>\<^sub>r P = A \<lhd>\<^sub>r P"
  by (auto simp add: rel_domres_def)

lemma Image_as_rel_domres: "R `` A = Range (A \<lhd>\<^sub>r R)"
  by (auto simp add: rel_domres_def)

lemma rel_domres_Un [simp]: "A \<lhd>\<^sub>r (S \<union> R) = (A \<lhd>\<^sub>r S) \<union> (A \<lhd>\<^sub>r R)"
  by (auto simp add: rel_domres_def)

subsection \<open> Range Restriction \<close>

lemma rel_ranres_UNIV [simp]: "P \<rhd>\<^sub>r UNIV = P"
  by (auto simp add: rel_ranres_def)

lemma rel_ranres_Un [simp]: "(P \<union> Q) \<rhd>\<^sub>r A = (P \<rhd>\<^sub>r A \<union> Q \<rhd>\<^sub>r A)"
  by (auto simp add: rel_ranres_def)

lemma rel_ranres_relcomp [simp]: "(P O Q) \<rhd>\<^sub>r A = P O (Q \<rhd>\<^sub>r A)"
  by (auto simp add: rel_ranres_def relcomp_unfold prod.case_eq_if)

lemma conv_rel_domres [simp]: "(P \<rhd>\<^sub>r A)\<inverse> = A \<lhd>\<^sub>r P\<inverse>"
  by (auto simp add: rel_domres_def rel_ranres_def)

lemma rel_ranres_le: "A \<subseteq> B \<Longrightarrow> f \<rhd>\<^sub>r A \<le> f \<rhd>\<^sub>r B"
  by (simp add: Collect_mono_iff in_mono rel_ranres_def)

subsection \<open> Relational Override \<close>

class restrict = pre_restrict +
  assumes cmpt_sym: "cmpt P Q \<Longrightarrow> cmpt Q P"
  and cmpt_empty: "cmpt {} P"
  assumes res_idem: "res P P = P"
  and res_assoc: "res P (res Q R) = res (res P Q) R"
  and res_lzero: "res {} P = P"
  and res_comm: "cmpt P Q \<Longrightarrow> res P Q = res Q P"
  and res_cmpt: "\<lbrakk> cmpt P Q; cmpt (res P Q) R \<rbrakk> \<Longrightarrow> cmpt P R"
  and res_cmptI: "\<lbrakk> cmpt P Q; cmpt P R; cmpt Q R \<rbrakk> \<Longrightarrow> cmpt (res P Q) R"

lemma res_cmpt_rel: "cmpt (P :: 'a \<leftrightarrow> 'b) Q \<Longrightarrow> cmpt (res P Q) R \<Longrightarrow> cmpt P R"
  by (fastforce simp add: rel_domres_def Domain_iff)

instance prod :: (type, type) restrict
  by (intro_classes, simp_all only: res_cmpt_rel, auto simp add: rel_domres_def Domain_unfold)
  
instantiation set :: (restrict) override
begin
definition compatible_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"compatible_set = cmpt"

instance 
  apply (intro_classes, simp_all add: oplus_set_def compatible_set_def res_idem res_assoc res_lzero cmpt_sym cmpt_empty res_comm res_cmptI)
  using res_cmpt apply blast
  done
end

lemma override_eq: "R \<oplus> S = ((- Domain S) \<lhd>\<^sub>r R) \<union> S"
  by (simp add: oplus_set_def)

lemma Domain_rel_override [simp]: "Domain (R \<oplus> S) = Domain(R) \<union> Domain(S)"
  by (auto simp add: oplus_set_def Domain_Un_eq)

lemma Range_rel_override: "Range(R \<oplus> S) \<subseteq> Range(R) \<union> Range(S)"
  by (auto simp add: oplus_set_def rel_domres_def)

lemma compatible_rel: "R ## S = (Domain R \<lhd>\<^sub>r S = Domain S \<lhd>\<^sub>r R)"
  by (simp add: compatible_set_def)

lemma compatible_relI: "Domain R \<lhd>\<^sub>r S = Domain S \<lhd>\<^sub>r R \<Longrightarrow> R ## S"
  by (simp add: compatible_rel)

subsection \<open> Functional Relations \<close>

abbreviation functional :: "('a \<leftrightarrow> 'b) \<Rightarrow> bool" where
"functional R \<equiv> single_valued R"

lemma functional_def: "functional R \<longleftrightarrow> inj_on fst R"
  by (force simp add: single_valued_def inj_on_def)

lemma functional_algebraic: "functional R \<longleftrightarrow> R\<inverse> O R \<subseteq> Id"
  apply (auto simp add: functional_def subset_iff relcomp_unfold)
  using inj_on_eq_iff apply fastforce
  apply (metis inj_onI surjective_pairing)
  done

lemma functional_apply: 
  assumes "functional R" "(x, y) \<in> R"
  shows "R(x)\<^sub>r = y"
  by (metis (no_types, lifting) Domain.intros DomainE assms(1) assms(2) single_valuedD rel_apply_def theI_unique)  

lemma functional_apply_iff: "functional R \<Longrightarrow> (x, y) \<in> R \<longleftrightarrow> (x \<in> Domain R \<and> R(x)\<^sub>r = y)"
  by (auto simp add: functional_apply)

lemma functional_elem:
  assumes "functional R" "x \<in> Domain(R)"
  shows "(x, R(x)\<^sub>r) \<in> R"
  using assms(1) assms(2) functional_apply by fastforce

lemma functional_override [intro!]: "\<lbrakk> functional R; functional S \<rbrakk> \<Longrightarrow> functional (R \<oplus> S)"
  by (auto simp add: functional_algebraic oplus_set_def rel_domres_def)

lemma functional_union [intro!]: "\<lbrakk> functional R; functional S; R ## S \<rbrakk> \<Longrightarrow> functional (R \<union> S)"
  by (metis functional_override le_sup_iff override_comm override_eq single_valued_subset subsetI)
  
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

text \<open> Make a relation functional by removing any pairs that have duplicate distinct values. \<close>

definition mk_functional :: "('a \<leftrightarrow> 'b) \<Rightarrow> ('a \<leftrightarrow> 'b)" where
"mk_functional R = {(x, y) \<in> R. \<forall> y'. (x, y') \<in> R \<longrightarrow> y = y'}"

lemma mk_functional [simp]: "functional (mk_functional R)"
  by (auto simp add: mk_functional_def single_valued_def)

lemma mk_functional_fp: "functional R \<Longrightarrow> mk_functional R = R"
  by (auto simp add: mk_functional_def single_valued_def)

lemma mk_functional_idem: "mk_functional (mk_functional R) = mk_functional R"
  using mk_functional mk_functional_fp by blast

lemma mk_functional_subset [simp]: "mk_functional R \<subseteq> R"
  by (auto simp add: mk_functional_def)

lemma Domain_mk_functional: "Domain (mk_functional R) \<subseteq> Domain R"
  by (auto simp add: mk_functional_def)

definition single_valued_dom :: "('a \<times> 'b) set \<Rightarrow> 'a set" where
"single_valued_dom R = {x \<in> Domain(R). \<exists> y. R `` {x} = {y}}"

lemma mk_functional_single_valued_dom: "mk_functional R = single_valued_dom R \<lhd>\<^sub>r R"
  by (auto simp add: mk_functional_def single_valued_dom_def rel_domres_math_def Domain_unfold)
     (metis Image_singleton_iff singletonD)
  
subsection \<open> Left-Total Relations\<close>

definition left_totalr_on :: "'a set \<Rightarrow> ('a \<leftrightarrow> 'b) \<Rightarrow> bool" where
"left_totalr_on A R \<longleftrightarrow> (\<forall>x\<in>A. \<exists>y. (x, y) \<in> R)"

abbreviation "left_totalr R \<equiv> left_totalr_on UNIV R"

lemma left_totalr_algebraic: "left_totalr R \<longleftrightarrow> Id \<subseteq> R O R\<inverse>"
  by (auto simp add: left_totalr_on_def)

lemma left_totalr_fun_rel: "left_totalr (fun_rel f)"
  by (simp add: left_totalr_on_def fun_rel_def)

subsection \<open> Injective Relations \<close>

definition injective :: "('a \<leftrightarrow> 'b) \<Rightarrow> bool" where
"injective R = (functional R \<and> R O R\<inverse> \<subseteq> Id)"

lemma injectiveI: 
  assumes "functional R" "\<And> x y. \<lbrakk> x \<in> Domain R; y \<in> Domain R; R(x)\<^sub>r = R(y)\<^sub>r \<rbrakk> \<Longrightarrow> x = y"
  shows "injective R"
  using assms by (auto simp add: injective_def functional_apply_iff)

subsection \<open> Relation Sets \<close>

definition rel_typed :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<leftrightarrow> 'b) set" (infixr "\<leftrightarrow>" 55) where
"rel_typed A B = {R. Domain(R) \<subseteq> A \<and> Range(R) \<subseteq> B}" \<comment> \<open> Relations \<close>

lemma rel_typed_intro: "\<lbrakk> Domain(R) \<subseteq> A; Range(R) \<subseteq> B \<rbrakk> \<Longrightarrow> R \<in> A \<leftrightarrow> B"
  by (simp add: rel_typed_def)

definition rel_pfun :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<leftrightarrow> 'b) set" (infixr "\<rightarrow>\<^sub>p" 55) where
"rel_pfun A B = {R. R \<in> A \<leftrightarrow> B \<and> functional R}" \<comment> \<open> Partial Functions \<close>

lemma rel_pfun_intro: "\<lbrakk> R \<in> A \<leftrightarrow> B; functional R \<rbrakk> \<Longrightarrow> R \<in> A \<rightarrow>\<^sub>p B"
  by (simp add: rel_pfun_def)

definition rel_tfun :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<leftrightarrow> 'b) set" (infixr "\<rightarrow>\<^sub>t" 55) where
"rel_tfun A B = {R. R \<in> A \<rightarrow>\<^sub>p B \<and> left_totalr R}" \<comment> \<open> Total Functions \<close>

definition rel_ffun :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<leftrightarrow> 'b) set" (infixr "\<rightarrow>\<^sub>f" 55) where
"rel_ffun A B = {R. R \<in> A \<rightarrow>\<^sub>p B \<and> finite(Domain R)}" \<comment> \<open> Finite Functions \<close>

subsection \<open> Closure Properties \<close>

text \<open> These can be seen as typing rules for relational functions \<close>

named_theorems rclos

lemma rel_ffun_is_pfun [rclos]: "R \<in> rel_ffun A B \<Longrightarrow> R \<in> A \<rightarrow>\<^sub>p B"
  by (simp add: rel_ffun_def)

lemma rel_tfun_is_pfun [rclos]: "R \<in> A \<rightarrow>\<^sub>t B \<Longrightarrow> R \<in> A \<rightarrow>\<^sub>p B"
  by (simp add: rel_tfun_def)

lemma rel_pfun_is_typed [rclos]: "R \<in> A \<rightarrow>\<^sub>p B \<Longrightarrow> R \<in> A \<leftrightarrow> B"
  by (simp add: rel_pfun_def)

lemma rel_ffun_empty [rclos]: "{} \<in> rel_ffun A B"
  by (simp add: rel_ffun_def rel_pfun_def rel_typed_def)

lemma rel_pfun_apply [rclos]: "\<lbrakk> x \<in> Domain(R); R \<in> A \<rightarrow>\<^sub>p B \<rbrakk> \<Longrightarrow> R(x)\<^sub>r \<in> B"
  using functional_apply by (fastforce simp add: rel_pfun_def rel_typed_def)

lemma rel_tfun_apply [rclos]: "\<lbrakk> x \<in> A; R \<in> A \<rightarrow>\<^sub>t B \<rbrakk> \<Longrightarrow> R(x)\<^sub>r \<in> B"
  by (metis (no_types, lifting) Domain_iff iso_tuple_UNIV_I left_totalr_on_def mem_Collect_eq rel_pfun_apply rel_tfun_def)

lemma rel_typed_insert [rclos]: "\<lbrakk> R \<in> A \<leftrightarrow> B; x \<in> A; y \<in> B \<rbrakk> \<Longrightarrow> insert (x, y) R \<in> A \<leftrightarrow> B"
  by (simp add: rel_typed_def)

lemma rel_pfun_insert [rclos]: "\<lbrakk> R \<in> A \<rightarrow>\<^sub>p B; x \<in> A; y \<in> B; x \<notin> Domain(R) \<rbrakk> \<Longrightarrow> insert (x, y) R \<in> A \<rightarrow>\<^sub>p B"
  by (auto intro: rclos simp add: rel_pfun_def)

lemma rel_pfun_override [rclos]: "\<lbrakk> R \<in> A \<rightarrow>\<^sub>p B; S \<in> A \<rightarrow>\<^sub>p B \<rbrakk> \<Longrightarrow> (R \<oplus> S) \<in> A \<rightarrow>\<^sub>p B"
  apply (rule rel_pfun_intro)
   apply (rule rel_typed_intro)
  apply (auto simp add: rel_pfun_def rel_typed_def)
  apply (metis (no_types, hide_lams) Range.simps Range_Un_eq Range_rel_override Un_iff rev_subsetD)
  done

subsection \<open> Code Generation \<close>

lemma rel_conv_alist [code]: "(set xs)\<inverse> = set (map (\<lambda>(x, y). (y, x)) xs)"
  by (induct xs, auto)

lemma rel_domres_alist [code]: "A \<lhd>\<^sub>r set xs = set (AList.restrict A xs)"
  by (induct xs, simp_all, safe, simp_all)

lemma Image_alist [code]: "set xs `` A = set (map snd (AList.restrict A xs))"
  by (simp add: Image_as_rel_domres rel_domres_alist Range_snd)

lemma Collect_set: "{x \<in> set xs. P x} = set (filter P xs)"
  by auto

lemma single_valued_dom_alist [code]:
  "single_valued_dom (set xs) = set (filter (\<lambda>x. length (remdups (map snd (AList.restrict {x} xs))) = 1) (map fst xs))"
  by (simp only: single_valued_dom_def set_map[THEN sym] Image_alist Domain_set set_singleton_iff list_singleton_iff Collect_set)

lemma AList_restrict_in_dom: "AList.restrict (set (filter P (map fst xs))) xs = filter (\<lambda> (x, y). P x) xs"
  by (auto intro: filter_cong simp add: Domain.intros fst_eq_Domain AList.restrict_eq)

lemma mk_functional_alist [code]:
  "mk_functional (set xs) = set (filter (\<lambda> (x,y). length (remdups (map snd (AList.restrict {x} xs))) = 1) xs)"
  by (simp only: mk_functional_single_valued_dom rel_domres_alist single_valued_dom_alist AList_restrict_in_dom)
  
lemma rel_apply_set [code]:
  "rel_apply (set xs) k = 
  (let ys = filter (\<lambda> (k', v). k = k') xs in
   if (length ys > 0 \<and> ys = replicate (length ys) (hd ys)) then snd (hd ys) else undefined)"
proof (simp add: Let_unfold, safe)
  let ?ys = "filter (\<lambda>(k', v). k = k') xs"
  assume ys: "?ys \<noteq> []" "?ys = replicate (length ?ys) (hd ?ys)"
  have kmem: "\<And> y. (k, y) \<in> set xs \<longleftrightarrow> (k, y) \<in> set ?ys"
    by simp
  from ys obtain v where v: "(k, v) \<in> set xs"
    using hd_in_set by fastforce
  hence ys':"?ys = replicate (length ?ys) (k, v)"
    by (metis (mono_tags) case_prodI filter_set in_set_replicate member_filter ys(2))
  hence "snd (hd ?ys) = v"
    by (metis hd_replicate replicate_0 snd_conv ys(1))
  moreover have "(THE y. (k, y) \<in> set xs) = v"
    by (metis (no_types, lifting) v in_set_replicate kmem snd_conv the_equality ys')
  moreover have "(\<exists>!y. (k, y) \<in> set xs)"
    by (metis Pair_inject v in_set_replicate kmem ys')
  ultimately show "set xs(k)\<^sub>r = snd (hd ?ys)"
    by (simp add: rel_apply_def)
next
  assume "filter (\<lambda>(k', v). k = k') xs = []" 
  hence "\<nexists>v. (k, v) \<in> set xs"
    by (metis (mono_tags, lifting) case_prodI filter_empty_conv)
  thus "set xs(k)\<^sub>r = undefined"
    by (auto simp add: rel_apply_def)
next
  let ?ys = "filter (\<lambda>(k', v). k = k') xs"
  assume ys: "?ys \<noteq> replicate (length ?ys) (hd ?ys)"
  have keys: "\<forall> (k', v') \<in> set ?ys. k' = k"
    by auto
  show "set xs(k)\<^sub>r = undefined"
  proof (cases "length ?ys = 0")
    case True
    then show ?thesis
      using ys by fastforce
  next
    case False
    hence "length ?ys > 1"
      by (metis hd_in_set in_set_conv_nth length_0_conv less_one linorder_neqE_nat replicate_length_same ys)
    have "fst (hd ?ys) = k"
      using False hd_in_set by force
    have "\<not>(\<forall> (k, v) \<in> set ?ys. v = snd (hd ?ys))"
    proof 
      assume "(\<forall> (k, v) \<in> set ?ys. v = snd (hd ?ys))"
      hence "(\<forall> p \<in> set ?ys. p = (k, snd (hd ?ys)))"
        by fastforce
      hence "?ys = replicate (length ?ys) (hd ?ys)"
        by (metis False length_0_conv list.set_sel(1) replicate_length_same)
      thus False
        using ys by blast
    qed
    then obtain v where "(k, v) \<in> set ?ys" "v \<noteq> snd (hd ?ys)"
      by fastforce
    hence "(\<not> (\<exists>!y. (k, y) \<in> set xs))"
      using False list.set_sel(1) by fastforce
    then show ?thesis
      by (simp add: rel_apply_def)
  qed
qed

end