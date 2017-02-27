section {* Substitution *}

theory utp_subst
imports 
  utp_expr
  utp_unrest
begin

subsection {* Substitution definitions *}

text {* We introduce a polymorphic constant that will be used to represent application of
        a substitution, and also a set of theorems to represent laws. *}

consts
  usubst :: "'s \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "\<dagger>" 80)

named_theorems usubst

text {* A substitution is simply a transformation on the alphabet; it shows how variables
        should be mapped to different values. *}

type_synonym ('\<alpha>,'\<beta>) psubst = "'\<alpha> alphabet \<Rightarrow> '\<beta> alphabet"
type_synonym '\<alpha> usubst = "'\<alpha> alphabet \<Rightarrow> '\<alpha> alphabet"

lift_definition subst :: "('\<alpha>, '\<beta>) psubst \<Rightarrow> ('a, '\<beta>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" is
"\<lambda> \<sigma> e b. e (\<sigma> b)" .

adhoc_overloading
  usubst subst

text {* Update the value of a variable to an expression in a substitution *}

consts subst_upd :: "('\<alpha>,'\<beta>) psubst \<Rightarrow> 'v \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('\<alpha>,'\<beta>) psubst"

definition subst_upd_uvar :: "('\<alpha>,'\<beta>) psubst \<Rightarrow> ('a, '\<beta>) uvar \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('\<alpha>,'\<beta>) psubst" where
"subst_upd_uvar \<sigma> x v = (\<lambda> b. put\<^bsub>x\<^esub> (\<sigma> b) (\<lbrakk>v\<rbrakk>\<^sub>eb))"

adhoc_overloading
  subst_upd subst_upd_uvar

text {* Lookup the expression associated with a variable in a substitution *}

lift_definition usubst_lookup :: "('\<alpha>,'\<beta>) psubst \<Rightarrow> ('a, '\<beta>) uvar \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<langle>_\<rangle>\<^sub>s")
is "\<lambda> \<sigma> x b. get\<^bsub>x\<^esub> (\<sigma> b)" .

text {* Relational lifting of a substitution to the first element of the state space *}

definition unrest_usubst :: "('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> usubst \<Rightarrow> bool"
where "unrest_usubst x \<sigma> = (\<forall> \<rho> v. \<sigma> (put\<^bsub>x\<^esub> \<rho> v) = put\<^bsub>x\<^esub> (\<sigma> \<rho>) v)"

adhoc_overloading
  unrest unrest_usubst

nonterminal smaplet and smaplets

syntax
  "_smaplet"  :: "[salpha, 'a] => smaplet"             ("_ /\<mapsto>\<^sub>s/ _")
  ""          :: "smaplet => smaplets"            ("_")
  "_SMaplets" :: "[smaplet, smaplets] => smaplets" ("_,/ _")
  "_SubstUpd" :: "['m usubst, smaplets] => 'm usubst" ("_/'(_')" [900,0] 900)
  "_Subst"    :: "smaplets => 'a \<rightharpoonup> 'b"            ("(1[_])")

translations
  "_SubstUpd m (_SMaplets xy ms)"     == "_SubstUpd (_SubstUpd m xy) ms"
  "_SubstUpd m (_smaplet x y)"        == "CONST subst_upd m x y"
  "_Subst ms"                         == "_SubstUpd (CONST id) ms"
  "_Subst (_SMaplets ms1 ms2)"        <= "_SubstUpd (_Subst ms1) ms2"
  "_SMaplets ms1 (_SMaplets ms2 ms3)" <= "_SMaplets (_SMaplets ms1 ms2) ms3"

text {* Deletion of a substitution maplet *}

definition subst_del :: "'\<alpha> usubst \<Rightarrow> ('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> usubst" (infix "-\<^sub>s" 85) where
"subst_del \<sigma> x = \<sigma>(x \<mapsto>\<^sub>s &x)"

subsection {* Substitution laws *}

text {* We set up a simple substitution tactic that applies substitution and unrestriction laws *}

method subst_tac = (simp add: usubst unrest)?

lemma usubst_lookup_id [usubst]: "\<langle>id\<rangle>\<^sub>s x = var x"
  by (transfer, simp)

lemma usubst_lookup_upd [usubst]:
  assumes "mwb_lens x"
  shows "\<langle>\<sigma>(x \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x = v"
  using assms
  by (simp add: subst_upd_uvar_def, transfer) (simp)
  
lemma usubst_upd_idem [usubst]:
  assumes "mwb_lens x"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, x \<mapsto>\<^sub>s v) = \<sigma>(x \<mapsto>\<^sub>s v)"
  by (simp add: subst_upd_uvar_def assms comp_def)

lemma usubst_upd_comm:
  assumes "x \<bowtie> y"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v) = \<sigma>(y \<mapsto>\<^sub>s v, x \<mapsto>\<^sub>s u)"
  using assms
  by (rule_tac ext, auto simp add: subst_upd_uvar_def assms comp_def lens_indep_comm)

lemma usubst_upd_comm2:
  assumes "z \<bowtie> y" and "mwb_lens x"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v, z \<mapsto>\<^sub>s s) = \<sigma>(x \<mapsto>\<^sub>s u, z \<mapsto>\<^sub>s s, y \<mapsto>\<^sub>s v)"
  using assms
  by (rule_tac ext, auto simp add: subst_upd_uvar_def assms comp_def lens_indep_comm)

lemma swap_usubst_inj:
  fixes x y :: "('a, '\<alpha>) uvar"
  assumes "vwb_lens x" "vwb_lens y" "x \<bowtie> y"
  shows "inj [x \<mapsto>\<^sub>s &y, y \<mapsto>\<^sub>s &x]"
  using assms
  apply (auto simp add: inj_on_def subst_upd_uvar_def)
  apply (smt lens_indep_get lens_indep_sym var.rep_eq vwb_lens.put_eq vwb_lens_wb wb_lens_weak weak_lens.put_get)
done

lemma usubst_upd_var_id [usubst]: 
  "vwb_lens x \<Longrightarrow> [x \<mapsto>\<^sub>s var x] = id"
  apply (simp add: subst_upd_uvar_def)
  apply (transfer)
  apply (rule ext)
  apply (auto)
done

lemma usubst_upd_comm_dash [usubst]: 
  fixes x :: "('a, '\<alpha>) uvar"
  shows "\<sigma>($x\<acute> \<mapsto>\<^sub>s v, $x \<mapsto>\<^sub>s u) = \<sigma>($x \<mapsto>\<^sub>s u, $x\<acute> \<mapsto>\<^sub>s v)"
  using out_in_indep usubst_upd_comm by blast  

lemma usubst_lookup_upd_indep [usubst]:
  assumes "mwb_lens x" "x \<bowtie> y"
  shows "\<langle>\<sigma>(y \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, simp)

lemma usubst_apply_unrest [usubst]:
  "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>s x = var x"
  by (simp add: unrest_usubst_def, transfer, auto simp add: fun_eq_iff, metis vwb_lens_wb wb_lens.get_put wb_lens_weak weak_lens.put_get)

lemma subst_del_id [usubst]: 
  "vwb_lens x \<Longrightarrow> id -\<^sub>s x = id"
  by (simp add: subst_del_def subst_upd_uvar_def, transfer, auto)

lemma subst_del_upd_same [usubst]: 
  "mwb_lens x \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) -\<^sub>s x = \<sigma> -\<^sub>s x"
  by (simp add: subst_del_def subst_upd_uvar_def)

lemma subst_del_upd_diff [usubst]: 
  "x \<bowtie> y \<Longrightarrow> \<sigma>(y \<mapsto>\<^sub>s v) -\<^sub>s x = (\<sigma> -\<^sub>s x)(y \<mapsto>\<^sub>s v)"
  by (simp add: subst_del_def subst_upd_uvar_def lens_indep_comm)

lemma subst_unrest [usubst]: "x \<sharp> P \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) \<dagger> P = \<sigma> \<dagger> P"
  by (simp add: subst_upd_uvar_def, transfer, auto)

lemma subst_compose_upd [usubst]: "x \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<circ> \<rho>(x \<mapsto>\<^sub>s v) = (\<sigma> \<circ> \<rho>)(x \<mapsto>\<^sub>s v) "
  by (simp add: subst_upd_uvar_def, transfer, auto simp add: unrest_usubst_def)

lemma id_subst [usubst]: "id \<dagger> v = v"
  by (transfer, simp)

lemma subst_lit [usubst]: "\<sigma> \<dagger> \<guillemotleft>v\<guillemotright> = \<guillemotleft>v\<guillemotright>"
  by (transfer, simp)

lemma subst_var [usubst]: "\<sigma> \<dagger> var x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  by (transfer, simp)

lemma usubst_ulambda [usubst]: "\<sigma> \<dagger> (\<lambda> x \<bullet> P(x)) = (\<lambda> x \<bullet> \<sigma> \<dagger> P(x))"
  by (transfer, simp)
    
lemma unrest_usubst_del [unrest]: "\<lbrakk> vwb_lens x; x \<sharp> (\<langle>\<sigma>\<rangle>\<^sub>s x); x \<sharp> \<sigma> -\<^sub>s x \<rbrakk> \<Longrightarrow>  x \<sharp> (\<sigma> \<dagger> P)"
  by (simp add: subst_del_def subst_upd_uvar_def unrest_upred_def unrest_usubst_def subst.rep_eq usubst_lookup.rep_eq)
     (metis vwb_lens.put_eq)

text {* We set up a purely syntactic order on variable lenses which is useful for the substitution
        normal form. *}

definition var_name_ord :: "('a, '\<alpha>) uvar \<Rightarrow> ('b, '\<alpha>) uvar \<Rightarrow> bool" where
[no_atp]: "var_name_ord x y = True"

syntax
  "_var_name_ord" :: "salpha \<Rightarrow> salpha \<Rightarrow> bool" (infix "\<prec>\<^sub>v" 65)

translations
  "_var_name_ord x y" == "CONST var_name_ord x y"

lemma usubst_upd_comm_ord [usubst]:
  assumes "x \<bowtie> y" "y \<prec>\<^sub>v x"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v) = \<sigma>(y \<mapsto>\<^sub>s v, x \<mapsto>\<^sub>s u)"
  by (simp add: assms(1) usubst_upd_comm)

text {* We add the symmetric definition of input and output variables to substitution laws
        so that the variables are correctly normalised after substitution. *}

lemma subst_uop [usubst]: "\<sigma> \<dagger> uop f v = uop f (\<sigma> \<dagger> v)"
  by (transfer, simp)

lemma subst_bop [usubst]: "\<sigma> \<dagger> bop f u v = bop f (\<sigma> \<dagger> u) (\<sigma> \<dagger> v)"
  by (transfer, simp)

lemma subst_trop [usubst]: "\<sigma> \<dagger> trop f u v w = trop f (\<sigma> \<dagger> u) (\<sigma> \<dagger> v) (\<sigma> \<dagger> w)"
  by (transfer, simp)

lemma subst_qtop [usubst]: "\<sigma> \<dagger> qtop f u v w x = qtop f (\<sigma> \<dagger> u) (\<sigma> \<dagger> v) (\<sigma> \<dagger> w) (\<sigma> \<dagger> x)"
  by (transfer, simp)

lemma subst_plus [usubst]: "\<sigma> \<dagger> (x + y) = \<sigma> \<dagger> x + \<sigma> \<dagger> y"
  by (simp add: plus_uexpr_def subst_bop)

lemma subst_times [usubst]: "\<sigma> \<dagger> (x * y) = \<sigma> \<dagger> x * \<sigma> \<dagger> y"
  by (simp add: times_uexpr_def subst_bop)

lemma subst_mod [usubst]: "\<sigma> \<dagger> (x mod y) = \<sigma> \<dagger> x mod \<sigma> \<dagger> y"
  by (simp add: mod_uexpr_def usubst)

lemma subst_div [usubst]: "\<sigma> \<dagger> (x div y) = \<sigma> \<dagger> x div \<sigma> \<dagger> y"
  by (simp add: divide_uexpr_def usubst)

lemma subst_minus [usubst]: "\<sigma> \<dagger> (x - y) = \<sigma> \<dagger> x - \<sigma> \<dagger> y"
  by (simp add: minus_uexpr_def subst_bop)

lemma subst_uminus [usubst]: "\<sigma> \<dagger> (- x) = - (\<sigma> \<dagger> x)"
  by (simp add: uminus_uexpr_def subst_uop)

lemma usubst_sgn [usubst]: "\<sigma> \<dagger> sgn x = sgn (\<sigma> \<dagger> x)"
  by (simp add: sgn_uexpr_def subst_uop)

lemma usubst_abs [usubst]: "\<sigma> \<dagger> abs x = abs (\<sigma> \<dagger> x)"
  by (simp add: abs_uexpr_def subst_uop)

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

nonterminal uexprs and svars and salphas

syntax
  "_psubst"  :: "[logic, svars, uexprs] \<Rightarrow> logic"
  "_subst"   :: "logic \<Rightarrow> uexprs \<Rightarrow> salphas \<Rightarrow> logic" ("(_\<lbrakk>_'/_\<rbrakk>)" [999,0,0] 1000)
  "_uexprs"  :: "[logic, uexprs] => uexprs" ("_,/ _")
  ""         :: "logic => uexprs" ("_")
  "_svars"   :: "[svar, svars] => svars" ("_,/ _")
  ""         :: "svar => svars" ("_")
  "_salphas" :: "[salpha, salphas] => salphas" ("_,/ _")
  ""         :: "salpha => salphas" ("_")

translations
  "_subst P es vs" => "CONST subst (_psubst (CONST id) vs es) P"
  "_psubst m (_salphas x xs) (_uexprs v vs)" => "_psubst (_psubst m x v) xs vs"
  "_psubst m x v"  => "CONST subst_upd m x v"
  "P\<lbrakk>v/$x\<rbrakk>" <= "CONST usubst (CONST subst_upd (CONST id) (CONST ivar x) v) P"
  "P\<lbrakk>v/$x\<acute>\<rbrakk>" <= "CONST usubst (CONST subst_upd (CONST id) (CONST ovar x) v) P"
  "P\<lbrakk>v/x\<rbrakk>" <= "CONST usubst (CONST subst_upd (CONST id) x v) P"

lemma subst_singleton: 
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "x \<sharp> \<sigma>"
  shows "\<sigma>(x \<mapsto>\<^sub>s v) \<dagger> P = (\<sigma> \<dagger> P)\<lbrakk>v/x\<rbrakk>"
  using assms
  by (simp add: usubst)

lemmas subst_to_singleton = subst_singleton id_subst

subsection {* Unrestriction laws *}

lemma unrest_usubst_single [unrest]:
  "\<lbrakk> mwb_lens x; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> P\<lbrakk>v/x\<rbrakk>"
  by (transfer, auto simp add: subst_upd_uvar_def unrest_upred_def)

lemma unrest_usubst_id [unrest]:
  "mwb_lens x \<Longrightarrow> x \<sharp> id"
  by (simp add: unrest_usubst_def)

lemma unrest_usubst_upd [unrest]:
  "\<lbrakk> x \<bowtie> y; x \<sharp> \<sigma>; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> \<sigma>(y \<mapsto>\<^sub>s v)"
  by (simp add: subst_upd_uvar_def unrest_usubst_def unrest_upred.rep_eq lens_indep_comm)

lemma unrest_subst [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> x \<sharp> (\<sigma> \<dagger> P)"
  by (transfer, simp add: unrest_usubst_def)

end