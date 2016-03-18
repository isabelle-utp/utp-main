section {* Unrestriction *}

theory utp_unrest
  imports utp_expr
begin

text {* Unrestriction is an encoding of semantic freshness, that allows us to reason about the
        presence of variables in predicates without being concerned with abstract syntax trees.
        An expression $p$ is unrestricted by variable $x$, written $x \mathop{\sharp} p$, if
        altering the value of $x$ has no effect on the valuation of $p$. This is a sufficient
        notion to prove many laws that would ordinarily rely on an \emph{fv} function. *}

consts
  unrest :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

syntax
  "_unrest" :: "svar \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<sharp>" 20)

translations
  "_unrest x p" == "CONST unrest x p" 

named_theorems unrest

term "var_update"

lift_definition unrest_upred :: "('a, '\<alpha>) uvar \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> bool"
is "\<lambda> x e. \<forall> b v. e (var_assign x v b) = e b" .

definition unrest_dvar_upred :: "'a::continuum dvar \<Rightarrow> ('b, '\<alpha>::vst) uexpr \<Rightarrow> bool" where
"unrest_dvar_upred x P = unrest_upred (x\<up>) P"

adhoc_overloading
  unrest unrest_upred

lemma unrest_lit [unrest]: "x \<sharp> \<guillemotleft>v\<guillemotright>"
  by (transfer, simp)

text {* The following law demonstrates why we need variable independence: a variable 
        expression is unrestricted by another variable only when the two variables are independent. *}

lemma unrest_var [unrest]: "\<lbrakk> uvar x; x \<bowtie> y \<rbrakk> \<Longrightarrow> y \<sharp> var x"
  by (transfer, auto)

lemma unrest_iuvar [unrest]: "\<lbrakk> uvar x; x \<bowtie> y \<rbrakk> \<Longrightarrow> $y \<sharp> $x"
  by (metis in_var_indep in_var_uvar unrest_var var_in_var)

lemma unrest_ouvar [unrest]: "\<lbrakk> uvar x; x \<bowtie> y \<rbrakk> \<Longrightarrow> $y\<acute> \<sharp> $x\<acute>"
  by (metis out_var_indep out_var_uvar unrest_var var_out_var)

lemma unrest_iuvar_ouvar [unrest]: 
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "uvar y"
  shows "$x \<sharp> $y\<acute>"
  by (metis prod.collapse unrest_upred.rep_eq var.rep_eq var_lookup_out var_out_var var_update_in)

lemma unrest_ouvar_iuvar [unrest]:
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "uvar y"
  shows "$x\<acute> \<sharp> $y"
  by (metis prod.collapse unrest_upred.rep_eq var.rep_eq var_in_var var_lookup_in var_update_out)

lemma unrest_uop [unrest]: "x \<sharp> e \<Longrightarrow> x \<sharp> uop f e"
  by (transfer, simp)

lemma unrest_bop [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> bop f u v"
  by (transfer, simp)

lemma unrest_trop [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v; x \<sharp> w \<rbrakk> \<Longrightarrow> x \<sharp> trop f u v w"
  by (transfer, simp)

lemma unrest_eq [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u =\<^sub>u v"
  by (simp add: eq_upred_def, transfer, simp)

lemma unrest_zero [unrest]: "x \<sharp> 0"
  by (simp add: unrest_lit zero_uexpr_def)

lemma unrest_one [unrest]: "x \<sharp> 1"
  by (simp add: one_uexpr_def unrest_lit)

lemma unrest_numeral [unrest]: "x \<sharp> (numeral n)"
  by (simp add: numeral_uexpr_simp unrest_lit)

lemma unrest_plus [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u + v"
  by (simp add: plus_uexpr_def unrest)

lemma unrest_uminus [unrest]: "x \<sharp> u \<Longrightarrow> x \<sharp> - u"
  by (simp add: uminus_uexpr_def unrest)

lemma unrest_minus [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u - v"
  by (simp add: minus_uexpr_def unrest)

lemma unrest_times [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u * v"
  by (simp add: times_uexpr_def unrest)

lemma unrest_divide [unrest]: "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> u / v"
  by (simp add: divide_uexpr_def unrest)

end
