section \<open> Ordinary Differential Equation Systems \<close>

theory utp_hyprog_ode
  imports utp_hyprog_prelim
begin

subsection \<open> Relational ODEs \<close>

text \<open> An ODE consists of equations @{term \<F>'} and a boundary condition @{term B}. It states that
  there exists a solution function @{term \<F>} and non-zero duration @{term l}, such that for 
  every @{term \<tau>} in the interval $[0, l]$ @{term \<F>'} is the derivative of @{term \<F>}, @{term B}
  holds on at each instant, and the before and after value of variable $x$ is equal to 
  @{term "\<F>(0)"} and @{term "\<F>(l)"}, respectively. \<close>

abbreviation solves :: 
  "(real \<Rightarrow> 'a::executable_euclidean_space) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a, 's) hybs_scheme upred \<Rightarrow> 's \<Rightarrow> real \<Rightarrow> bool" where
  "solves F F' B s l \<equiv>  (\<forall>x. 0 \<le> x \<and> x \<le> l \<longrightarrow> (F has_vector_derivative F' (F x)) (at x within {0..l}) \<and> (\<lbrakk>B\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F x, \<dots> = s\<rparr>)))"

abbreviation solves\<^sub>u :: "(real \<Rightarrow> 'c::executable_euclidean_space) \<Rightarrow> 'c usubst \<Rightarrow> ('c, 's) hypred \<Rightarrow>  real \<Rightarrow> _" where
"solves\<^sub>u \<F> \<F>' B l \<equiv> (\<^bold>\<forall> \<tau> \<in> {0..\<guillemotleft>l\<guillemotright>}\<^sub>u \<bullet> \<guillemotleft>(\<F> has_vector_derivative (\<lambda> _. \<lbrakk>\<F>'\<rbrakk>\<^sub>e) \<tau> (\<F> \<tau>)) (at \<tau> within {0..l}) 
                      \<guillemotright> \<and> \<lceil>B\<lbrakk>\<guillemotleft>\<F>(\<tau>)\<guillemotright>/&cvec\<rbrakk>\<rceil>\<^sub><)"

definition ode :: "'c::executable_euclidean_space usubst \<Rightarrow> ('c, 's) hypred \<Rightarrow> ('c, 's) hyrel" where
[upred_defs]: "ode \<F>' B = cvec:[\<^bold>\<exists> (\<F>, l) \<bullet> \<guillemotleft>l\<guillemotright> \<ge>\<^sub>u 0 \<and> solves\<^sub>u \<F> \<F>' B l \<and> $cvec =\<^sub>u \<guillemotleft>\<F>(0)\<guillemotright> \<and> $cvec\<acute> =\<^sub>u \<guillemotleft>\<F>(l)\<guillemotright>]"

text \<open> A framed ODE allows us to explicitly specify only certain continuous variables using a
  suitable lens that selects those variables we are interested in. The remainder are held constant
  by assigning them deriative 0. \<close>

definition fode :: 
  "('a::executable_euclidean_space \<Longrightarrow> 'b::executable_euclidean_space) \<Rightarrow> 'b usubst \<Rightarrow> 'b usubst" where
[upred_defs]: "fode x F = F \<circ>\<^sub>s [&\<^bold>v \<mapsto>\<^sub>s 0]"

subsection \<open> ODE Parser \<close>

text \<open> We set up a parser and pretty printer so that an ODE relation can be written using the
  familiar $\dot{x} = f(x)$ style syntax. \<close>

nonterminal sode and sodes

syntax
  "_ode"        :: "id \<Rightarrow> logic \<Rightarrow> sode" ("der'(_') = _")
  "_ode"        :: "id \<Rightarrow> logic \<Rightarrow> sode" ("_\<^sup>\<bullet> = _")
  "_ode_last"   :: "sode \<Rightarrow> sodes" ("_")
  "_ode_cons"   :: "sode \<Rightarrow> sodes \<Rightarrow> sodes" ("_,/ _")
  "_sys_ode"    :: "sodes \<Rightarrow> logic \<Rightarrow> logic" ("\<langle>_ | _\<rangle>")
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
  "_sys_ode fs B" => "CONST ode (CONST fode (_ode_lens fs /\<^sub>L CONST cvec) (_abs (_ode_tuple fs) (_ode_expr fs))) B"
  "_sys_ode_s fs" == "_sys_ode fs true"
  "_sys_ode (_ode y f) B" <= "CONST ode (CONST fode x (_abs y f)) B"
  "_ode_cons (_ode x f) (_ode y g)" <= "_ode (_pattern x y) (f, g)"

(*
term "\<langle>der(h) = v, der(v) = -9.81 | (&h \<ge>\<^sub>u 0)\<rangle>"
term "\<langle>x\<^sup>\<bullet> = f(x)\<rangle>"
*)

subsection \<open> ODE laws \<close>

lemma solves_le: "\<lbrakk> solves F F' B s l; l' \<le> l \<rbrakk> \<Longrightarrow> solves F F' B s l'"
  by (meson atLeastatMost_subset_iff has_vector_derivative_within_subset order_refl order_trans)

lemma ode_post: "ode F' B ;; ?[B] = ode F' B"
  by (rel_auto', metis (no_types), metis hybs.select_convs(1) order_refl)

lemma ode_mono:
  "`(C \<Rightarrow> B)` \<Longrightarrow> ode F' B \<sqsubseteq> ode F' C"
  by (rel_blast)

end