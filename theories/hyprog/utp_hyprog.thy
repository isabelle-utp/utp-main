section \<open> Hybrid Programs \<close>

theory utp_hyprog
  imports 
    "UTP.utp"
    "Ordinary_Differential_Equations.ODE_Analysis"
    "HOL-Analysis.Analysis"
    "HOL-Library.Function_Algebras"
    "Dynamics.Derivative_extra"
begin recall_syntax

subsection \<open> Continuous Variable Lenses \<close>

text \<open> Finite Cartesian Product Lens \<close>

definition vec_lens :: "'i \<Rightarrow> ('a \<Longrightarrow> 'a^'i)" where
[lens_defs]: "vec_lens k = \<lparr> lens_get = (\<lambda> s. vec_nth s k), lens_put = (\<lambda> s v. (\<chi> x. fun_upd (vec_nth s) k v x)) \<rparr>"

lemma vec_vwb_lens [simp]: "vwb_lens (vec_lens k)"
  apply (unfold_locales)
  apply (simp_all add: vec_lens_def fun_eq_iff)
  using vec_lambda_unique apply force
  done

text \<open> Executable Euclidean Space Lens \<close>

notation frechet_derivative ("\<partial>")

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

definition eucl_lens :: "nat \<Rightarrow> (real \<Longrightarrow> 'a::executable_euclidean_space)" where
[lens_defs]: "eucl_lens k = \<lparr> lens_get = eucl_nth k
                            , lens_put = (\<lambda> s v. eucl_of_list(list_update (list_of_eucl s) k v)) \<rparr>"

lemma eucl_vwb_lens [simp]: 
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> vwb_lens (eucl_lens k :: real \<Longrightarrow> 'a)"
  apply (unfold_locales)
  apply (simp_all add: lens_defs eucl_of_list_inner)
  apply (metis eucl_of_list_list_of_eucl list_of_eucl_nth list_update_id)
  done

lemma bounded_linear_eucl_get [simp]:
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> bounded_linear (get\<^bsub>eucl_lens k :: real \<Longrightarrow> 'a\<^esub>)"
  by (metis bounded_linear_eucl_nth eucl_lens_def lens.simps(1))

text \<open> Characterising lenses that are equivalent to Euclidean lenses \<close>

definition is_eucl_lens :: "(real \<Longrightarrow> 'a::executable_euclidean_space) \<Rightarrow> bool" where
"is_eucl_lens x = (\<exists> k. k < DIM('a) \<and> x \<approx>\<^sub>L eucl_lens k)"

lemma eucl_lens_is_eucl:
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> is_eucl_lens (eucl_lens k :: real \<Longrightarrow> 'a)"
  by (force simp add: is_eucl_lens_def)

lemma eucl_lens_is_vwb [simp]: "is_eucl_lens x \<Longrightarrow> vwb_lens x"
  using eucl_vwb_lens is_eucl_lens_def lens_equiv_def sublens_pres_vwb by blast

lemma bounded_linear_eucl_lens: "is_eucl_lens x \<Longrightarrow> bounded_linear (get\<^bsub>x\<^esub>)"
  oops

alphabet 'i::finite hybs =
  cvec :: "real^'i"

abbreviation "dst \<equiv> hybs_child_lens"

type_synonym ('a, 'i, 's) hyexpr = "('a, ('i, 's) hybs_scheme) uexpr"
type_synonym ('i, 's) hypred = "('i, 's) hybs_scheme upred"
type_synonym ('i, 's) hyrel = "('i, 's) hybs_scheme hrel"

subsection \<open> Relational ODEs \<close>

text \<open> An ODE consists of equations @{term \<F>'} and a boundary condition @{term B}. It states that
  there exists a solution function @{term \<F>} and non-zero duration @{term l}, such that for 
  every @{term \<tau>} in the interval $[0, l]$ @{term \<F>'} is the derivative of @{term \<F>}, @{term B}
  holds on at each instant, and the before and after value of variable $x$ is equal to 
  @{term "\<F>(0)"} and @{term "\<F>(l)"}, respectively. \<close>

definition ode :: "('a::executable_euclidean_space \<Longrightarrow> real^'i::enum) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('i, 's) hypred \<Rightarrow> ('i, 's) hyrel" where
[upred_defs]: "ode x \<F>' B = 
  cvec:x:[\<^bold>\<exists> (\<F>, l) \<bullet> 
        \<guillemotleft>l\<guillemotright> >\<^sub>u 0 \<and> (\<^bold>\<forall> \<tau> \<in> {0..\<guillemotleft>l\<guillemotright>}\<^sub>u \<bullet> \<guillemotleft>(\<F> has_vector_derivative (\<lambda> _. \<F>') \<tau> (\<F> \<tau>)) (at \<tau> within {0..l}) 
                    \<and> `B\<lbrakk>\<guillemotleft>\<F>(\<tau>)\<guillemotright>/&cvec:x\<rbrakk>`\<guillemotright>)
      \<and> $cvec:x =\<^sub>u \<guillemotleft>\<F>(0)\<guillemotright> \<and> $cvec:x\<acute> =\<^sub>u \<guillemotleft>\<F>(l)\<guillemotright>]"

text \<open> We set up a parser and pretty printer so that an ODE relation can be written using the
  familiar $\dot{x} = f(x)$ style syntax. \<close>

nonterminal sode and sodes

syntax
  "_ode"        :: "id \<Rightarrow> logic \<Rightarrow> sode" ("der'(_') = _")
  "_ode"        :: "id \<Rightarrow> logic \<Rightarrow> sode" ("_\<^sup>\<bullet> = _")
  "_ode_last"   :: "sode \<Rightarrow> sodes" ("_")
  "_ode_cons"   :: "sode \<Rightarrow> sodes \<Rightarrow> sodes" ("_,/ _")
  "_sys_ode"    :: "sodes \<Rightarrow> uexp \<Rightarrow> logic" ("\<langle>_ | _\<rangle>")
  "_sys_ode_s"  :: "sodes \<Rightarrow> logic" ("\<langle>_\<rangle>")
  "_ode_lens"   :: "sodes \<Rightarrow> logic"
  "_ode_tuple"  :: "sodes \<Rightarrow> logic"
  "_ode_expr"   :: "sodes \<Rightarrow> logic"

translations
  "_ode_lens (_ode_cons (_ode x f) fs)" => "x +\<^sub>L (_ode_lens fs)"
  "_ode_lens (_ode_last (_ode x f))" => "x"
  "_ode_tuple (_ode_cons (_ode x f) fs)" => "(x, (_ode_tuple fs))"
  "_ode_tuple (_ode_last (_ode x f))" => "x"
  "_ode_expr (_ode_cons (_ode x f) fs)" => "(f, (_ode_expr fs))"
  "_ode_expr (_ode_last (_ode x f))" => "f"
  "_sys_ode fs B" => "CONST ode (_ode_lens fs /\<^sub>L CONST cvec) (_abs (_ode_tuple fs) (_ode_expr fs)) B"
  "_sys_ode_s fs" == "_sys_ode fs true"
  "_sys_ode (_ode y f) B" <= "CONST ode x (_abs y f) B"
  "_ode_cons (_ode x f) (_ode y g)" <= "_ode (_pattern x y) (f, g)"

term "\<langle>der(h) = v, der(v) = -9.81 | (&h \<ge>\<^sub>u 0)\<rangle>"
term "\<langle>x\<^sup>\<bullet> = f(x)\<rangle>"

subsection \<open> dL Rules \<close>

lemma differential_weakening: 
  "\<lbrakk> vwb_lens x; `B \<Rightarrow> C` \<rbrakk> \<Longrightarrow> \<^bold>[\<langle>x\<^sup>\<bullet> = f(x) | B\<rangle>\<^bold>]C = true"
  by (rel_simp, simp add: bop_ueval lit.rep_eq)

end