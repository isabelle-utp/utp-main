section \<open> Relation Toolkit \<close>

theory Relation_Toolkit
  imports Set_Toolkit Overriding
begin

subsection \<open> Conversions \<close>

text \<open> The majority of the relation toolkit is also part of HOL. We just need to generalise
  some of the syntax. \<close>

declare [[coercion rel_apply]]
declare [[coercion pfun_app]]
declare [[coercion pfun_of]]


text \<open> The following definition is semantically identical to @{const pfun_graph}, but is used to 
  represent coercions with associated reasoning. \<close>

definition rel_of_pfun :: "'a \<Zpfun> 'b \<Rightarrow> 'a \<leftrightarrow> 'b" ("[_]\<^sub>\<Zpfun>") where
[code_unfold]: "rel_of_pfun = pfun_graph"

declare [[coercion rel_of_pfun]]
declare [[coercion pfun_of_pinj]]

notation pfun_of_pinj ("[_]\<^sub>\<Zpinj>")

subsection \<open> First component projection \<close>

text \<open> Z supports n-ary Cartesian products. We cannot support such structures directly in 
  Isabelle/HOL, but instead add the projection notations for the first and second components.
  A homogeneous finite Cartesian product type also exists in the Multivariate Analysis package. \<close>

abbreviation (input) "first \<equiv> fst"
notation first ("_.1" [999] 999)

subsection \<open> Second component projection \<close>

abbreviation (input) "second \<equiv> snd"
notation second ("_.2" [999] 999)

subsection \<open> Maplet \<close>

subsection \<open> Domain \<close>

hide_const (open) dom

consts dom :: "'f \<Rightarrow> 'a set"

adhoc_overloading
  dom Map.dom and
  dom Relation.Domain and
  dom Partial_Fun.pdom and
  dom Finite_Fun.fdom and
  dom Partial_Inj.pidom

subsection \<open> Range \<close>

hide_const (open) ran

consts ran :: "'f \<Rightarrow> 'a set"

adhoc_overloading
  ran Map.ran and
  ran Relation.Range and
  ran Partial_Fun.pran and
  ran Finite_Fun.fran and
  ran Partial_Inj.piran

subsection \<open> Identity relation \<close>

notation Id_on ("id[_]")

subsection \<open> Relational composition \<close>

notation relcomp (infixr "\<^bold>;" 75)

subsection \<open> Functional composition \<close>

text \<open> Composition is probably the most difficult of the Z functions to implement correctly. Firstly,
  the notation @{term "(\<circ>)"} is already defined for HOL functions, and we need to respect that
  in order to use the HOL library functions. Secondly, Z composition can be used to compose 
  heterogeneous relations and functions, which is not easy to type infer. Consequently, we opt
  to use adhoc overloading here. \<close>

hide_const (open) comp

consts comp :: "'f \<Rightarrow> 'g \<Rightarrow> 'h" 

adhoc_overloading
  comp Fun.comp and
  comp pfun_comp and
  comp ffun_comp

bundle Z_Relation_Syntax
begin

no_notation Fun.comp (infixl "\<circ>" 55)
notation comp (infixl "\<circ>" 55)

end

subsection \<open> Domain restriction and subtraction \<close>

consts dom_res :: "'a set \<Rightarrow> 'r \<Rightarrow> 'r" (infixr "\<Zdres>" 85)

abbreviation ndres (infixr "\<Zndres>" 85) where "ndres A P \<equiv> CONST dom_res (- A) P" 

adhoc_overloading 
  dom_res rel_domres
  and dom_res pdom_res
  and dom_res fdom_res
  and dom_res pinj_dres

syntax "_ndres" :: "logic \<Rightarrow> logic \<Rightarrow> logic" 
translations "_ndres A P" == "CONST dom_res (- A) P"

subsection \<open> Range restriction and subtraction \<close>

consts ran_res :: "'r \<Rightarrow> 'a set \<Rightarrow> 'r" (infixl "\<Zrres>" 86)

abbreviation nrres (infixl "\<Znrres>" 86) where "nrres P A \<equiv> CONST ran_res P (- A)"

adhoc_overloading 
  ran_res rel_ranres
  and ran_res pran_res
  and ran_res fran_res
  and ran_res pinj_rres

subsection \<open> Relational inversion \<close>

notation converse ("(_\<^sup>\<sim>)" [1000] 999)

lemma relational_inverse: "r\<^sup>\<sim> = {(p.2, p.1) | p. p \<in> r}"
  by auto

subsection \<open> Relational image \<close>

notation Image ("_\<lparr>_\<rparr>" [990] 990)

lemma Image_eq: "Image r a = {p.2 | p. p \<in> r \<and> p.1 \<in> a}"
  by (auto simp add: Image_def)

subsection \<open> Overriding \<close>

lemma dom_override: "dom ((Q :: 'a \<leftrightarrow> 'b) \<oplus> R) = (dom Q) \<union> (dom R)"
  by (simp add: Un_Int_distrib2)

lemma override_Un: "dom Q \<inter> dom R = {} \<Longrightarrow> Q \<oplus> R = Q \<union> R"
  by (simp add: override_eq Int_commute rel_domres_compl_disj)

subsection \<open> Proof Support \<close>

text \<open> The objective of these laws is to, as much as possible, convert relational constructions
  into functional ones. The benefit is better proof automation in the more type constrained setting. \<close>

lemma rel_of_pfun_eq_iff [simp]: "[f]\<^sub>\<Zpfun> = [g]\<^sub>\<Zpfun> \<longleftrightarrow> f = g"
  by (simp add: pfun_eq_graph rel_of_pfun_def)

lemma rel_of_pfun_le_iff [simp]: "[f]\<^sub>\<Zpfun> \<subseteq> [g]\<^sub>\<Zpfun> \<longleftrightarrow> f \<le> g"
  by (simp add: pfun_graph_le_iff rel_of_pfun_def)

lemma rel_of_pfun_pabs: "[pabs A P f]\<^sub>\<Zpfun> = {(k, v). k \<in> A \<and> P k \<and> v = f k}"
  by (simp add: rel_of_pfun_def pfun_graph_pabs)

lemma rel_of_pfun_apply [simp]: "[f]\<^sub>\<Zpfun> x = f x"
  by (simp add: rel_of_pfun_def)

lemma rel_of_pfun_functional [simp]: "functional [f]\<^sub>\<Zpfun>"
  by (simp add: rel_of_pfun_def)

lemma rel_of_pfun_override [simp]: "[f]\<^sub>\<Zpfun> \<oplus> [g]\<^sub>\<Zpfun> = [f \<oplus> g]\<^sub>\<Zpfun>"
  by (simp add: pfun_graph_override rel_of_pfun_def)

lemma rel_of_pfun_comp [simp]: "[f]\<^sub>\<Zpfun> O [g]\<^sub>\<Zpfun> = [g \<circ>\<^sub>p f]\<^sub>\<Zpfun>"
  by (simp add: pfun_graph_comp rel_of_pfun_def)

lemma pfun_comp_inv: "[f \<circ>\<^sub>p g]\<^sub>\<Zpfun>\<^sup>\<sim> = [f]\<^sub>\<Zpfun>\<^sup>\<sim> O [g]\<^sub>\<Zpfun>\<^sup>\<sim>"
  by (metis converse_relcomp rel_of_pfun_comp)

lemma rel_of_pfun_dom [simp]: "Domain [f]\<^sub>\<Zpfun> = pdom f"
  by (simp add: Dom_pfun_graph rel_of_pfun_def)

lemma rel_of_pfun_ran [simp]: "Range [f]\<^sub>\<Zpfun> = pran f"
  by (simp add: Range_pfun_graph rel_of_pfun_def)

lemma rel_of_pfun_domres [simp]: "A \<Zdres> [f]\<^sub>\<Zpfun> = [A \<Zdres> f]\<^sub>\<Zpfun>"
  by (simp add: pfun_graph_domres rel_of_pfun_def)

lemma rel_of_pfun_ranres [simp]: "[f]\<^sub>\<Zpfun> \<Zrres> A = [f \<Zrres> A]\<^sub>\<Zpfun>"
  by (simp add: rel_of_pfun_def pfun_graph_rres)

lemma rel_of_pfun_image [simp]: "[f]\<^sub>\<Zpfun> \<lparr> A \<rparr> = pfun_image f A"
  by (simp add: Image_as_rel_domres)

lemma rel_of_pfun_member_iff [simp]:
  "(k, v) \<in> [f]\<^sub>\<Zpfun> \<longleftrightarrow> (k \<in> dom f \<and> f k = v)"
  by (simp add: rel_of_pfun_def)

lemma rel_of_pinj_conv [simp]: "[[f]\<^sub>\<Zpinj>]\<^sub>\<Zpfun>\<inverse> = [[pinv f]\<^sub>\<Zpinj>]\<^sub>\<Zpfun>"
  by (simp add: pfun_graph_pfun_inv pinv.rep_eq rel_of_pfun_def)

lemma dom_pinv [simp]: "dom [pinv f]\<^sub>\<Zpinj> = ran [f]\<^sub>\<Zpinj>"
  by (simp add: pinv.rep_eq)

lemma ran_pinv [simp]: "ran [pinv f]\<^sub>\<Zpinj> = dom [f]\<^sub>\<Zpinj>"
  by (metis dom_pinv pinv_pinv)

lemma pfun_inj_rel_conv [simp]: "pfun_inj f \<Longrightarrow> [f]\<^sub>\<Zpfun>\<^sup>\<sim> = [pfun_inv f]\<^sub>\<Zpfun>"
  by (simp add: pfun_graph_pfun_inv rel_of_pfun_def)

end