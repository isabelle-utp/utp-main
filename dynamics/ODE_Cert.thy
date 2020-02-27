section \<open> ODE Certification Tactic \<close>

theory ODE_Cert
  imports 
    Derivative_extra
    "Ordinary_Differential_Equations.ODE_Analysis"
begin

text \<open> \emph{ode\_cert} is a simple tactic for certifying solutions to systems of differential equations \<close>
                               
method ode_cert = 
  \<comment> \<open> Apply the introduction rule \<close>
  (rule_tac solves_odeI,
  \<comment> \<open> Simplify away the set-wise vector derivative definition \<close>
    simp_all add: has_vderiv_on_def, 
  \<comment> \<open> Split apart individual ODEs composed pair-wise \<close>
    safe intro!: has_vector_derivative_Pair, 
  \<comment> \<open> Raise two goals, with a linking meta-variable: (1) the derivative goal, (2) a goal that
      the resulting derivative is equal to the target \<close>
    (rule has_vector_derivative_eq_rhs,
  \<comment> \<open> Recursively apply derivative introduction laws to (1) \<close>
      (rule derivative_intros; (simp)?)+, 
  \<comment> \<open> Simplify away (2) using field laws \<close>
      simp add: field_simps)+)

type_synonym 'c ODE = "real \<Rightarrow> 'c \<Rightarrow> 'c"

text \<open> A simple example is the following system of ODEs for an objecting accelerating according to gravity. \<close>

abbreviation "grav \<equiv> 9.81"

abbreviation grav_ode :: "(real \<times> real) ODE" where
"grav_ode \<equiv> (\<lambda> t (v, h). (- grav, v))"

text \<open> We also present the following solution to the system of ODEs, which is a function from 
  initial values of the continuous variables to a continuous function that shows how the variables 
  change with time. \<close>

abbreviation grav_sol :: "real \<times> real \<Rightarrow> real \<Rightarrow>  real \<times> real" where
"grav_sol \<equiv> \<lambda> (v\<^sub>0, h\<^sub>0)  \<tau>. (v\<^sub>0 - grav * \<tau>, v\<^sub>0 * \<tau> - grav * (\<tau> * \<tau>) / 2 + h\<^sub>0)"

text \<open> Finally, we show how this solution to the ODEs can be certified. \<close>

lemma 
  "(grav_sol (v\<^sub>0, h\<^sub>0) solves_ode grav_ode) T UNIV"
  by ode_cert

text \<open> More examples \<close>

lemma "((\<lambda> t. exp t) solves_ode (\<lambda> t y. y)) T UNIV"
  by ode_cert

lemma "((\<lambda> t. (cos t, sin t)) solves_ode (\<lambda> t (x, y). (-y, x))) T UNIV"
  by ode_cert

end