section \<open> Hybrid Programs Preliminaries \<close>

theory utp_hyprog_prelim
  imports 
    "UTP.utp"
    "Ordinary_Differential_Equations.ODE_Analysis"
    "HOL-Analysis.Analysis"
    "HOL-Library.Function_Algebras"
    "Dynamics.Derivative_extra"
begin recall_syntax

subsection \<open> Continuous Variable Lenses \<close>

text \<open> We begin by defining some lenses that will be useful in characterising continuous variables \<close>

subsubsection \<open> Finite Cartesian Product Lens \<close>

definition vec_lens :: "'i \<Rightarrow> ('a \<Longrightarrow> 'a^'i)" where
[lens_defs]: "vec_lens k = \<lparr> lens_get = (\<lambda> s. vec_nth s k), lens_put = (\<lambda> s v. (\<chi> x. fun_upd (vec_nth s) k v x)) \<rparr>"

lemma vec_vwb_lens [simp]: "vwb_lens (vec_lens k)"
  apply (unfold_locales)
  apply (simp_all add: vec_lens_def fun_eq_iff)
  using vec_lambda_unique apply force
  done

subsubsection \<open> Executable Euclidean Space Lens \<close>

abbreviation "eucl_nth k \<equiv> (\<lambda> x. list_of_eucl x ! k)"

lemma bounded_linear_eucl_nth: 
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> bounded_linear (eucl_nth k :: 'a \<Rightarrow> real)"
  by (simp add: bounded_linear_inner_left)

lemmas has_derivative_eucl_nth = bounded_linear.has_derivative[OF bounded_linear_eucl_nth]

lemma has_derivative_eucl_nth_triv:
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> ((eucl_nth k :: 'a \<Rightarrow> real) has_derivative eucl_nth k) F"
  using bounded_linear_eucl_nth bounded_linear_imp_has_derivative by blast

lemma frechet_derivative_eucl_nth:
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> \<partial>(eucl_nth k :: 'a \<Rightarrow> real) (at t) = eucl_nth k"
  by (metis (full_types) frechet_derivative_at has_derivative_eucl_nth_triv)

text \<open> The Euclidean lens extracts the nth component of a Euclidean space \<close>

definition eucl_lens :: "nat \<Rightarrow> (real \<Longrightarrow> 'a::executable_euclidean_space)" ("\<Pi>[_]") where
[lens_defs]: "eucl_lens k = \<lparr> lens_get = eucl_nth k
                            , lens_put = (\<lambda> s v. eucl_of_list(list_update (list_of_eucl s) k v)) \<rparr>"

lemma eucl_vwb_lens [simp]: 
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> vwb_lens (\<Pi>[k] :: real \<Longrightarrow> 'a)"
  apply (unfold_locales)
  apply (simp_all add: lens_defs eucl_of_list_inner)
  apply (metis eucl_of_list_list_of_eucl list_of_eucl_nth list_update_id)
  done

lemma eucl_lens_indep [simp]:
  "\<lbrakk> i < DIM('a); j < DIM('a); i \<noteq> j \<rbrakk> \<Longrightarrow> (eucl_lens i :: real \<Longrightarrow> 'a::executable_euclidean_space) \<bowtie> eucl_lens j"
  by (unfold_locales, simp_all add: lens_defs list_update_swap eucl_of_list_inner)

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
  "_eucl_lens" :: "logic \<Rightarrow> svid" ("\<Pi>[_]")
  "_cvec_lens" :: "svid" ("\<^bold>c")
  "_dst_lens"  :: "svid" ("\<^bold>d")

translations
  "_eucl_lens x" == "CONST eucl_lens x"
  "_cvec_lens" == "CONST cvec"
  "_dst_lens" == "CONST dst"

end