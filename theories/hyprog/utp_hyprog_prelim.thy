section \<open> Hybrid Programs Preliminaries \<close>

theory utp_hyprog_prelim
  imports 
    "UTP.utp"
    "Ordinary_Differential_Equations.ODE_Analysis"
    "HOL-Analysis.Analysis"
    "HOL-Library.Function_Algebras"
    "Dynamics.Derivative_extra"
    "Dynamics.ODE_Cert"
    "Dynamics.Matrix_Syntax"
begin recall_syntax

subsection \<open> Basic Lens Results \<close>

utp_lift_notation utp_pred.taut utp_pred.closure

lemma bounded_linear_fst_lens [simp]: "bounded_linear (get\<^bsub>fst\<^sub>L\<^esub>)"
  by (simp add: lens_defs bounded_linear_fst)

lemma bounded_linear_snd_lens [simp]: "bounded_linear (get\<^bsub>snd\<^sub>L\<^esub>)"
  by (simp add: lens_defs bounded_linear_snd)

lemma bounded_linear_lens_comp [simp]: 
  "\<lbrakk> bounded_linear (get\<^bsub>x\<^esub>); bounded_linear (get\<^bsub>y\<^esub>) \<rbrakk> \<Longrightarrow> bounded_linear (get\<^bsub>x;\<^sub>Ly\<^esub>)"
  by (simp add: lens_defs comp_def bounded_linear_compose)

subsection \<open> Continuous Variable Lenses \<close>

text \<open> We begin by defining some lenses that will be useful in characterising continuous variables \<close>

subsubsection \<open> Finite Cartesian Product Lens \<close>

declare [[coercion vec_nth]]

definition vec_upd :: "'a^'i \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> 'a^'i" where
"vec_upd s k v = (\<chi> x. fun_upd (vec_nth s) k v x)"

lemma vec_nth_upd [simp]: "vec_nth (vec_upd f k v) k = v"
  by (simp add: vec_upd_def)

lemma vec_upd_nth [simp]: "vec_upd f k (vec_nth f k) = f"
  by (simp add: vec_upd_def)

lemma vec_upd_upd [simp]: "vec_upd (vec_upd f k v) k u = vec_upd f k u"
  by (simp add: vec_upd_def fun_eq_iff)

definition vec_lens :: "'i \<Rightarrow> ('a \<Longrightarrow> 'a^'i)" where
[lens_defs]: "vec_lens k = \<lparr> lens_get = (\<lambda> s. vec_nth s k), lens_put = (\<lambda> s. vec_upd s k) \<rparr>"

lemma vec_vwb_lens [simp]: "vwb_lens (vec_lens k)"
  by (unfold_locales, simp_all add: vec_lens_def)

lemma vec_lens_indep [simp]: "i \<noteq> j \<Longrightarrow> vec_lens i \<bowtie> vec_lens j"
  by (unfold_locales, simp_all add: vec_lens_def vec_upd_def fun_eq_iff)

lemma bounded_linear_vec_lens [simp]: "bounded_linear (get\<^bsub>vec_lens i\<^esub>)"
  by (simp add: vec_lens_def bounded_linear_vec_nth)

subsubsection \<open> Matrix Lens \<close>

definition mat_lens :: "'i \<Rightarrow> 'j \<Rightarrow> ('a \<Longrightarrow> 'a mat['i, 'j])" where
[lens_defs]: "mat_lens i j = vec_lens j ;\<^sub>L vec_lens i"

lemma mat_vwb_lens [simp]: "vwb_lens (mat_lens i j)"
  by (simp add: mat_lens_def)

lemma mat_lens_indep [simp]: "\<lbrakk> i\<^sub>1 \<noteq> i\<^sub>2 \<or> j\<^sub>1 \<noteq> j\<^sub>2 \<rbrakk> \<Longrightarrow> mat_lens i\<^sub>1 j\<^sub>1 \<bowtie> mat_lens i\<^sub>2 j\<^sub>2"
  by (simp add: mat_lens_def
     ,metis lens_indep_left_comp lens_indep_left_ext lens_indep_right_ext vec_lens_indep vec_vwb_lens vwb_lens_mwb)

lemma bounded_linear_mat_lens [simp]: "bounded_linear (get\<^bsub>mat_lens i k\<^esub>)"
  by (simp add: mat_lens_def) 

subsubsection \<open> Executable Euclidean Space Lens \<close>

definition "eucl_nth k \<equiv> (\<lambda> x. list_of_eucl x ! k)"

lemma bounded_linear_eucl_nth [simp]: 
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> bounded_linear (eucl_nth k :: 'a \<Rightarrow> real)"
  by (simp add: eucl_nth_def bounded_linear_inner_left)

lemmas has_derivative_eucl_nth = bounded_linear.has_derivative[OF bounded_linear_eucl_nth]

lemma has_derivative_eucl_nth_triv:
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> ((eucl_nth k :: 'a \<Rightarrow> real) has_derivative eucl_nth k) F"
  using bounded_linear_eucl_nth bounded_linear_imp_has_derivative by blast

lemma frechet_derivative_eucl_nth:
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> \<partial>(eucl_nth k :: 'a \<Rightarrow> real) (at t) = eucl_nth k"
  by (metis (full_types) frechet_derivative_at has_derivative_eucl_nth_triv)

lemma differentiable_eucl_nth:
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> (eucl_nth k :: 'a \<Rightarrow> real) differentiable (at t)"
  using differentiableI has_derivative_eucl_nth_triv by blast

lemma differentiable_eucl_nth':
  fixes f :: "_ \<Rightarrow> 'a::executable_euclidean_space"
  assumes "f differentiable (at t)" "k < DIM('a)"
  shows "(\<lambda> x. eucl_nth k (f x)) differentiable (at t)"
  by (simp add: assms(1) assms(2) differentiable_compose differentiable_eucl_nth)

lemma frechet_derivative_eucl_nth':
  fixes f :: "_ \<Rightarrow> 'a::executable_euclidean_space"
  assumes "f differentiable (at t)" "k < DIM('a)"
  shows "\<partial> (\<lambda> x. eucl_nth k (f x)) (at t) = (\<lambda> x. eucl_nth k (\<partial> f (at t) x))"
  by (metis (full_types) assms(1) assms(2) frechet_derivative_at frechet_derivative_works has_derivative_eucl_nth)

text \<open> The Euclidean lens extracts the nth component of a Euclidean space \<close>

definition eucl_lens :: "nat \<Rightarrow> (real \<Longrightarrow> 'a::executable_euclidean_space)" ("\<Pi>[_]") where
[lens_defs]: "eucl_lens k = \<lparr> lens_get = eucl_nth k
                            , lens_put = (\<lambda> s v. eucl_of_list(list_update (list_of_eucl s) k v)) \<rparr>"

lemma eucl_vwb_lens [simp]: 
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> vwb_lens (\<Pi>[k] :: real \<Longrightarrow> 'a)"
  apply (unfold_locales)
  apply (simp_all add: lens_defs eucl_of_list_inner eucl_nth_def)
  apply (metis eucl_of_list_list_of_eucl list_of_eucl_nth list_update_id)
  done

lemma eucl_lens_indep [simp]:
  "\<lbrakk> i < DIM('a); j < DIM('a); i \<noteq> j \<rbrakk> \<Longrightarrow> (eucl_lens i :: real \<Longrightarrow> 'a::executable_euclidean_space) \<bowtie> eucl_lens j"
  by (unfold_locales, simp_all add: lens_defs list_update_swap eucl_of_list_inner eucl_nth_def)

lemma bounded_linear_eucl_get [simp]:
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> bounded_linear (get\<^bsub>\<Pi>[k] :: real \<Longrightarrow> 'a\<^esub>)"
  by (metis bounded_linear_eucl_nth eucl_lens_def lens.simps(1))

text \<open> Characterising lenses that are equivalent to Euclidean lenses \<close>

definition is_eucl_lens :: "(real \<Longrightarrow> 'a::executable_euclidean_space) \<Rightarrow> bool" where
"is_eucl_lens x = (\<exists> k. k < DIM('a) \<and> x \<approx>\<^sub>L \<Pi>[k])"

lemma eucl_lens_is_eucl:
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> is_eucl_lens (\<Pi>[k] :: real \<Longrightarrow> 'a)"
  by (force simp add: is_eucl_lens_def)

lemma eucl_lens_is_vwb [simp]: "is_eucl_lens x \<Longrightarrow> vwb_lens x"
  using eucl_vwb_lens is_eucl_lens_def lens_equiv_def sublens_pres_vwb by blast

lemma bounded_linear_eucl_lens: "is_eucl_lens x \<Longrightarrow> bounded_linear (get\<^bsub>x\<^esub>)"
  oops

subsection \<open> Hybrid state space \<close>

text \<open> A hybrid state-space consists, minimally, of a suitable topological space that occupies
  the continuous variables. Usually, @{typ 'c} will be a Euclidean space or real vector. \<close>

alphabet 'c::t2_space hybs =
  cvec :: "'c"
(*  cghost :: "'c" *)

text \<open> The remainder of the state-space is discrete and we make no requirements of it \<close>

abbreviation "dst \<equiv> hybs.more\<^sub>L"

notation cvec ("\<^bold>c")
notation dst ("\<^bold>d")

text \<open> We define hybrid expressions, predicates, and relations (i.e. programs) by utilising
  the hybrid state-space type. \<close>

type_synonym ('a, 'c, 's) hyexpr = "('a, ('c, 's) hybs_scheme) uexpr"
type_synonym ('c, 's) hypred = "('c, 's) hybs_scheme upred"
type_synonym ('c, 's) hyrel = "('c, 's) hybs_scheme hrel"

subsection \<open> Syntax \<close>

syntax
  "_vec_lens"  :: "logic \<Rightarrow> svid" ("\<pi>[_]")
  "_eucl_lens" :: "logic \<Rightarrow> svid" ("\<Pi>[_]")
  "_cvec_lens" :: "svid" ("\<^bold>c")
  "_dst_lens"  :: "svid" ("\<^bold>d")

translations
  "_vec_lens x" == "CONST vec_lens x"
  "_eucl_lens x" == "CONST eucl_lens x"
  "_cvec_lens" == "CONST cvec"
  "_dst_lens" == "CONST dst"

end