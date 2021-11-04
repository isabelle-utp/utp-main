chapter \<open>Löb  Formulas\<close>

(*<*)
theory Loeb_Formula imports Diagonalization Derivability_Conditions
begin
(*>*)

text \<open>The Löb formula, parameterized by a sentence @{term \<phi>}, is defined by diagonalizing @{term "imp P \<phi>"}.\<close>


locale Loeb_Form =
Deduct2
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv bprv
+
Repr_SelfSubst
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv bprv
  enc
  S
+
HBL1
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv bprv
  enc
  P
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var num FvarsT substT Fvars subst
and eql cnj imp all exi
and prv bprv
and enc ("\<langle>_\<rangle>")
and S
and P
begin

text \<open>The Löb formula associated to a formula @{term \<phi>}:\<close>
definition \<phi>L :: "'fmla \<Rightarrow> 'fmla" where "\<phi>L \<phi> \<equiv> diag (imp P \<phi>)"

lemma \<phi>L[simp,intro]: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> \<phi>L \<phi> \<in> fmla"
and
Fvars_\<phi>L[simp]: "\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> Fvars (\<phi>L \<phi>) = {}"
  unfolding \<phi>L_def PP_def by auto

lemma bprv_\<phi>L_eqv:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi>  = {} \<Longrightarrow> bprv (eqv (\<phi>L \<phi>) (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>))"
  unfolding \<phi>L_def PP_def using bprv_diag_eqv[of "imp P \<phi>"] by auto

lemma prv_\<phi>L_eqv:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi>  = {} \<Longrightarrow> prv (eqv (\<phi>L \<phi>) (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>))"
  using bprv_prv[OF _ _ bprv_\<phi>L_eqv, simplified] by auto

end \<comment> \<open>context @{locale Loeb_Form}\<close>

(*<*)
end
(*>*)
