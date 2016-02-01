section {* Substitution *}

theory utp_subst
imports 
  utp_expr
  utp_lift
  utp_unrest
begin

subsection {* Substitution definitions *}

text {* We introduce a polymorphic constant that will be used to represent application of
        a substitution, and also a set of theorems to represent laws. *}

consts
  usubst :: "'s \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<dagger>" 80)

named_theorems usubst

text {* A substitution is simply a transformation on the alphabet; it shows how variables
        should be mapped to different values. *}

type_synonym '\<alpha> usubst = "'\<alpha> alphabet \<Rightarrow> '\<alpha> alphabet"

lift_definition subst :: "'\<alpha> usubst \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" is
"\<lambda> \<sigma> e b. e (\<sigma> b)" .

adhoc_overloading
  usubst subst

text {* Update the value of a variable to an expression in a substitution *}

consts subst_upd :: "'\<alpha> usubst \<Rightarrow> 'v \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> '\<alpha> usubst"

definition subst_upd_uvar :: "'\<alpha> usubst \<Rightarrow> ('a, '\<alpha>) uvar \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> '\<alpha> usubst" where
"subst_upd_uvar \<sigma> x v = (\<lambda> b. var_assign x (\<lbrakk>v\<rbrakk>\<^sub>eb) (\<sigma> b))"

definition subst_upd_dvar :: "'\<alpha> usubst \<Rightarrow> 'a::continuum dvar \<Rightarrow> ('a, '\<alpha>::vst) uexpr \<Rightarrow> '\<alpha> usubst" where
"subst_upd_dvar \<sigma> x v = (\<lambda> b. var_assign (dvar_lift x) (\<lbrakk>v\<rbrakk>\<^sub>eb) (\<sigma> b))"

adhoc_overloading
  subst_upd subst_upd_uvar and subst_upd subst_upd_dvar

text {* Lookup the expression associated with a variable in a substitution *}

lift_definition usubst_lookup :: "'\<alpha> usubst \<Rightarrow> ('a, '\<alpha>) uvar \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<langle>_\<rangle>\<^sub>s")
is "\<lambda> \<sigma> x b. var_lookup x (\<sigma> b)" .

text {* Relational lifting of a substitution to the first element of the state space *}

definition usubst_rel_lift :: "'\<alpha> usubst \<Rightarrow> ('\<alpha> \<times> '\<beta>) usubst" ("\<lceil>_\<rceil>\<^sub>s") where
"\<lceil>\<sigma>\<rceil>\<^sub>s = (\<lambda> (A, A'). (\<sigma> A, A'))"

definition usubst_rel_drop :: "('\<alpha> \<times> '\<alpha>) usubst \<Rightarrow> '\<alpha> usubst" ("\<lfloor>_\<rfloor>\<^sub>s") where
"\<lfloor>\<sigma>\<rfloor>\<^sub>s = (\<lambda> A. fst (\<sigma> (A, A)))"

nonterminal smaplet and smaplets

syntax
  "_smaplet"  :: "[svar, 'a] => smaplet"             ("_ /\<mapsto>\<^sub>s/ _")
  ""          :: "smaplet => smaplets"            ("_")
  "_SMaplets" :: "[smaplet, smaplets] => smaplets" ("_,/ _")
  "_SubstUpd" :: "['m usubst, smaplets] => 'm usubst" ("_/'(_')" [900,0] 900)
  "_Subst"    :: "smaplets => 'a ~=> 'b"            ("(1[_])")

translations
  "_SubstUpd m (_SMaplets xy ms)"     == "_SubstUpd (_SubstUpd m xy) ms"
  "_SubstUpd m (_smaplet  x y)"       == "CONST subst_upd m x y"
  "_Subst ms"                         == "_SubstUpd (CONST id) ms"
  "_Subst (_SMaplets ms1 ms2)"        <= "_SubstUpd (_Subst ms1) ms2"
  "_SMaplets ms1 (_SMaplets ms2 ms3)" <= "_SMaplets (_SMaplets ms1 ms2) ms3"

subsection {* Substitution laws *}

text {* We set up a simple substitution tactic that applies substitution and unrestriction laws *}

method subst_tac = (simp add: usubst unrest)?

lemma usubst_lookup_id [usubst]: "\<langle>id\<rangle>\<^sub>s x = var x"
  by (transfer, simp)

lemma usubst_lookup_upd [usubst]:
  assumes "uvar x"
  shows "\<langle>\<sigma>(x \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x = v"
  using assms
  by (simp add: subst_upd_uvar_def, transfer) (simp)

lemma usubst_upd_idem [usubst]:
  assumes "uvar x"
  shows " \<sigma>(x \<mapsto>\<^sub>s u, x \<mapsto>\<^sub>s v) = \<sigma>(x \<mapsto>\<^sub>s v)"
  by (simp add: subst_upd_uvar_def assms comp_def)

lemma usubst_lookup_upd_indep [usubst]:
  assumes "uvar x" "x \<bowtie> y"
  shows "\<langle>\<sigma>(y \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, simp)

lemma subst_unrest [usubst] : "x \<sharp> P \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) \<dagger> P = \<sigma> \<dagger> P"
  by (simp add: subst_upd_uvar_def, transfer, auto)

lemma id_subst [usubst]: "id \<dagger> v = v"
  by (transfer, simp)

lemma subst_lit [usubst]: "\<sigma> \<dagger> \<guillemotleft>v\<guillemotright> = \<guillemotleft>v\<guillemotright>"
  by (transfer, simp)

lemma subst_var [usubst]: "\<sigma> \<dagger> var x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  by (transfer, simp)

lemma subst_ivar [usubst]: "\<sigma> \<dagger> $x = \<langle>\<sigma>\<rangle>\<^sub>s (in_var x)"
  by (simp add: iuvar_def, transfer, simp)

lemma subst_ovar [usubst]: "\<sigma> \<dagger> $x\<acute> = \<langle>\<sigma>\<rangle>\<^sub>s (out_var x)"
  by (simp add: ouvar_def, transfer, simp)

lemma subst_uop [usubst]: "\<sigma> \<dagger> uop f v = uop f (\<sigma> \<dagger> v)"
  by (transfer, simp)

lemma subst_bop [usubst]: "\<sigma> \<dagger> bop f u v = bop f (\<sigma> \<dagger> u) (\<sigma> \<dagger> v)"
  by (transfer, simp)

lemma subst_plus [usubst]: "\<sigma> \<dagger> (x + y) = \<sigma> \<dagger> x + \<sigma> \<dagger> y"
  by (simp add: plus_uexpr_def subst_bop)

lemma subst_times [usubst]: "\<sigma> \<dagger> (x * y) = \<sigma> \<dagger> x * \<sigma> \<dagger> y"
  by (simp add: times_uexpr_def subst_bop)

lemma subst_minus [usubst]: "\<sigma> \<dagger> (x - y) = \<sigma> \<dagger> x - \<sigma> \<dagger> y"
  by (simp add: minus_uexpr_def subst_bop)

lemma subst_zero [usubst]: "\<sigma> \<dagger> 0 = 0"
  by (simp add: zero_uexpr_def subst_lit)

lemma subst_one [usubst]: "\<sigma> \<dagger> 1 = 1"
  by (simp add: one_uexpr_def subst_lit)

lemma subst_eq_upred [usubst]: "\<sigma> \<dagger> (x =\<^sub>u y) = (\<sigma> \<dagger> x =\<^sub>u \<sigma> \<dagger> y)"
  by (simp add: eq_upred_def usubst)

lemma subst_subst [usubst]: "\<sigma> \<dagger> \<rho> \<dagger> e = (\<rho> \<circ> \<sigma>) \<dagger> e"
  by (transfer, simp)

lemma subst_upd_comp [usubst]: 
  fixes x :: "('a, '\<alpha>) uvar"
  shows "\<rho>(x \<mapsto>\<^sub>s v) \<circ> \<sigma> = (\<rho> \<circ> \<sigma>)(x \<mapsto>\<^sub>s \<sigma> \<dagger> v)"
  by (rule ext, simp add:uexpr_defs subst_upd_uvar_def, transfer, simp)

lemma subst_lift_id [usubst]: "\<lceil>id\<rceil>\<^sub>s = id"
  by (simp add: usubst_rel_lift_def)

lemma subst_drop_id [usubst]: "\<lfloor>id\<rfloor>\<^sub>s = id"
  by (auto simp add: usubst_rel_drop_def)

lemma subst_lift_drop [usubst]: "\<lfloor>\<lceil>\<sigma>\<rceil>\<^sub>s\<rfloor>\<^sub>s = \<sigma>"
  by (simp add: usubst_rel_lift_def usubst_rel_drop_def)

lemma subst_lift_upd [usubst]: "\<lceil>\<sigma>(x \<mapsto>\<^sub>s v)\<rceil>\<^sub>s = \<lceil>\<sigma>\<rceil>\<^sub>s($x \<mapsto>\<^sub>s \<lceil>v\<rceil>\<^sub><)"
  by (simp add: usubst_rel_lift_def subst_upd_uvar_def, transfer, auto)

lemma subst_drop_upd [usubst]: "\<lfloor>\<sigma>($x \<mapsto>\<^sub>s v)\<rfloor>\<^sub>s = \<lfloor>\<sigma>\<rfloor>\<^sub>s(x \<mapsto>\<^sub>s \<lfloor>v\<rfloor>\<^sub><)"
  apply (simp add: usubst_rel_drop_def subst_upd_uvar_def, transfer, rule ext, auto simp add:in_var_def)
  apply (rename_tac x v \<sigma> A)
  apply (case_tac "\<sigma> (A, A)", simp)
done

nonterminal uexprs and svars

syntax
  "_psubst"  :: "['\<alpha> usubst, svars, uexprs] \<Rightarrow> logic"
  "_subst"   :: "('a, '\<alpha>) uexpr \<Rightarrow> uexprs \<Rightarrow> svars \<Rightarrow> ('a, '\<alpha>) uexpr" ("(_\<lbrakk>_'/_\<rbrakk>)" [999,999] 1000)
  "_uexprs"  :: "[('a, '\<alpha>) uexpr, uexprs] => uexprs" ("_,/ _")
  ""         :: "('a, '\<alpha>) uexpr => uexprs" ("_")
  "_svars"   :: "[svar, svars] => svars" ("_,/ _")
  ""         :: "svar => svars" ("_")

translations
  "_subst P es vs"            => "CONST subst (_psubst (CONST id) vs es) P"
  "_psubst m (_svar x) v"     => "CONST subst_upd m x v"
  "_psubst m (_spvar x) v"    => "CONST subst_upd m x v"
  "_psubst m (_sinvar x) v"   => "CONST subst_upd m (CONST in_var x) v"
  "_psubst m (_soutvar x) v"  => "CONST subst_upd m (CONST out_var x) v"
  "_psubst m (_svars x xs) (_uexprs v vs)" => "_psubst (_psubst m x v) xs vs"

end