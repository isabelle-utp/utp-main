section \<open>A Formalization of Jeroslow's Original Argument\<close>

(*<*)
theory Jeroslow_Original imports
"Syntax_Independent_Logic.Pseudo_Term"
Abstract_Jeroslow_Encoding
begin
(*>*)

subsection \<open>Preliminaries\<close>

text \<open>The First Derivability Condition was stated using a formula
with free variable @{term xx}, whereas the pseudo-term theory employs a different variable,
inp. The distinction is of course immaterial, because we can perform
a change of variable in the instantiation:\<close>

context HBL1
begin

text \<open>Changing the variable (from @{term xx} to @{term inp}) in the provability predicate:\<close>
definition "Pinp \<equiv> subst P (Var inp) xx"
lemma PP_Pinp: "t \<in> trm \<Longrightarrow> PP t = instInp Pinp t"
unfolding PP_def Pinp_def instInp_def by auto

text \<open>A version of HBL1 that uses the @{term inp} variable:\<close>
lemma HBL1_inp:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> \<Longrightarrow> prv (instInp Pinp \<langle>\<phi>\<rangle>)"
unfolding Pinp_def instInp_def by (auto intro: HBL1)

end \<comment> \<open>context @{locale HBL1 }\<close>


subsection \<open>Jeroslow-style diagonalization\<close>

locale Jeroslow_Diagonalization =
Deduct_with_False_Disj_Rename
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv
+
Encode
  var trm fmla Var FvarsT substT Fvars subst
  num
  enc
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
and prv
and enc ("\<langle>_\<rangle>")
+
fixes F :: "('trm \<Rightarrow> 'trm) set"
  and encF :: "('trm \<Rightarrow> 'trm) \<Rightarrow> 'fmla"
  and N :: "'trm \<Rightarrow> 'trm"
  and ssap :: "'fmla \<Rightarrow> 'trm \<Rightarrow> 'trm"
assumes
\<comment> \<open>For the members @{term f} of @{term F}, we will only care about their action on numerals,
and we assume that they send numerals to numerals.\<close>
F[simp,intro!]: "\<And> f n. f \<in> F \<Longrightarrow> n \<in> num \<Longrightarrow> f n \<in> num"
and
encF[simp,intro!]: "\<And> f. f \<in> F \<Longrightarrow> encF f \<in> ptrm (Suc 0)"
and
N[simp,intro!]: "N \<in> F"
and
ssap[simp]: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {inp} \<Longrightarrow> ssap \<phi> \<in> F"
and
ReprF: "\<And>f n. f \<in> F \<Longrightarrow> n \<in> num \<Longrightarrow> prveqlPT (instInp (encF f) n) (f n)"
and
CapN: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> N \<langle>\<phi>\<rangle> = \<langle>neg \<phi>\<rangle>"
and
CapSS: \<comment> \<open>We consider formulas @{term \<psi>} of one variable, called @{term inp}:\<close>
"\<And> \<psi> f. \<psi> \<in> fmla \<Longrightarrow> Fvars \<psi> = {inp} \<Longrightarrow> f \<in> F \<Longrightarrow>
    ssap \<psi> \<langle>encF f\<rangle> = \<langle>instInpP \<psi> 0 (instInp (encF f) \<langle>encF f\<rangle>)\<rangle>"
begin

lemma encF_fmla[simp,intro!]: "\<And> f. f \<in> F \<Longrightarrow> encF f \<in> fmla"
by auto

lemma enc_trm: "\<phi> \<in> fmla \<Longrightarrow> \<langle>\<phi>\<rangle> \<in> trm"
by auto

definition \<tau>J :: "'fmla \<Rightarrow> 'fmla" where
"\<tau>J \<psi> \<equiv> instInp (encF (ssap \<psi>)) (\<langle>encF (ssap \<psi>)\<rangle>)"

definition \<phi>J :: "'fmla \<Rightarrow> 'fmla" where
"\<phi>J \<psi> \<equiv> instInpP \<psi> 0 (\<tau>J \<psi>)"

lemma \<tau>J[simp]:
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {inp}"
shows "\<tau>J \<psi> \<in> ptrm 0"
unfolding \<tau>J_def apply(rule instInp)
using assms by auto

lemma \<tau>J_fmla[simp]:
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {inp}"
shows "\<tau>J \<psi> \<in> fmla"
using \<tau>J[OF assms] unfolding ptrm_def by auto

lemma FvarsT_\<tau>J[simp]:
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {inp}"
shows "Fvars (\<tau>J \<psi>) = {out}"
using \<tau>J[OF assms] unfolding ptrm_def by auto

lemma \<phi>J[simp]:
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {inp}"
shows "\<phi>J \<psi> \<in> fmla"
unfolding \<phi>J_def using assms by (intro instInpP_fmla) auto

lemma Fvars_\<phi>J[simp]:
assumes "\<psi> \<in> fmla" and "Fvars \<psi> = {inp}"
shows "Fvars (\<phi>J \<psi>) = {}"
using assms unfolding \<phi>J_def by auto

lemma diagonalization:
assumes \<psi>[simp]: "\<psi> \<in> fmla" and [simp]: "Fvars \<psi> = {inp}"
shows "prveqlPT (\<tau>J \<psi>) \<langle>instInpP \<psi> 0 (\<tau>J \<psi>)\<rangle> \<and>
       prv (eqv (\<phi>J \<psi>) (instInp \<psi> \<langle>\<phi>J \<psi>\<rangle>))"
proof
  define f where "f \<equiv> ssap \<psi>"
  have f[simp]: "f \<in> F" unfolding f_def using assms by auto
  have ff: "f \<langle>encF f\<rangle> = \<langle>instInpP \<psi> 0 (\<tau>J \<psi>)\<rangle>"
  using assms unfolding f_def \<tau>J_def by (intro CapSS) auto

  show "prveqlPT (\<tau>J \<psi>) \<langle>instInpP \<psi> 0 (\<tau>J \<psi>)\<rangle>"
  using ReprF[OF f, of "\<langle>encF f\<rangle>"]
  unfolding \<tau>J_def[of \<psi>, unfolded f_def[symmetric],symmetric] ff[symmetric]
  by auto
  from prveqlPT_prv_instInp_eqv_instInpP[OF \<psi>, of "\<tau>J \<psi>", OF _ _ _ _ this,
           unfolded \<phi>J_def[symmetric]]
  show "prv (eqv (\<phi>J \<psi>) (instInp \<psi> \<langle>\<phi>J \<psi>\<rangle>))"
  by auto
qed

end \<comment> \<open>context @{locale Jeroslow_Diagonalization}\<close>


subsection \<open>Jeroslow's Second Incompleteness Theorem\<close>

text \<open>We follow Jeroslow's pseudo-term-based development of the
Second Incompleteness Theorem and point out the location in the proof that
implicitly uses an unstated assumption: the fact that, for certain two provably
equivalent formulas @{term \<phi>} and @{term \<phi>'}, it is provable that
the provability of the encoding of @{term \<phi>'} implies
the provability of the encoding of @{term \<phi>}. \<close>

locale Jeroslow_Godel_Second =
Jeroslow_Diagonalization
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv
  enc
  F encF N ssap
+
HBL1
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv prv
  enc
  P
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
and prv
and enc ("\<langle>_\<rangle>")
and P
and F encF N ssap
+
assumes
SHBL3: "\<And>\<tau>. \<tau> \<in> ptrm 0 \<Longrightarrow> prv (imp (instInpP Pinp 0 \<tau>) (instInp Pinp \<langle>instInpP Pinp 0 \<tau>\<rangle>))"
begin


text \<open>Consistency formula a la Jeroslow:\<close>
definition jcons :: "'fmla" where
"jcons \<equiv> all xx (neg (cnj (instInp Pinp (Var xx))
                           (instInpP Pinp 0 (instInp (encF N) (Var (xx))))))"

lemma prv_eql_subst_trm3:
"x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow>
prv (eql t1 t2) \<Longrightarrow> prv (subst \<phi> t1 x) \<Longrightarrow> prv (subst \<phi> t2 x)"
using prv_eql_subst_trm2
  by (meson subst prv_imp_mp)

lemma Pinp[simp,intro!]: "Pinp \<in> fmla"
and Fvars_Pinp[simp]: "Fvars Pinp = {inp}"
unfolding Pinp_def by auto

lemma ReprF_combineWith_CapN:
assumes "\<phi> \<in> fmla" and "Fvars \<phi> = {}"
shows "prveqlPT (instInp (encF N) \<langle>\<phi>\<rangle>) \<langle>neg \<phi>\<rangle>"
using assms unfolding CapN[symmetric, OF assms] by (intro ReprF) auto

theorem jeroslow_godel_second:
assumes consistent
\<comment> \<open>Assumption that is not stated by Jeroslow, but seems to be needed:\<close>
assumes unstated:
        "let \<psi> = instInpP Pinp (Suc 0) (encF N);
             \<tau> = \<tau>J \<psi>;
             \<phi> = instInpP (instInpP Pinp (Suc 0) (encF N)) 0 \<tau>;
             \<phi>' = instInpP Pinp 0 (instInpP (encF N) 0 \<tau>)
         in prv (imp (instInp Pinp \<langle>\<phi>'\<rangle>) (instInp Pinp \<langle>\<phi>\<rangle>))"
shows "\<not> prv jcons"
proof
  assume *: "prv jcons"

  define \<psi> where "\<psi> \<equiv> instInpP Pinp (Suc 0) (encF N)"
  define \<tau> where "\<tau> \<equiv> \<tau>J \<psi>"
  define \<phi> where "\<phi> \<equiv> \<phi>J \<psi>"
  have \<psi>[simp,intro]: "\<psi> \<in> fmla" "Fvars \<psi> = {inp}"
  unfolding \<psi>_def by auto
  have \<tau>[simp,intro]: "\<tau> \<in> ptrm 0" "\<tau> \<in> fmla" "Fvars \<tau> = {out}"
    unfolding \<tau>_def by auto
  have [simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" unfolding \<phi>_def by auto

  define eN\<tau> where "eN\<tau> \<equiv> instInpP (encF N) 0 \<tau>"
  have eN\<tau>[simp]: "eN\<tau> \<in> ptrm 0" "eN\<tau> \<in> fmla" "Fvars eN\<tau> = {out}"
   unfolding eN\<tau>_def by auto
  define \<phi>' where "\<phi>' \<equiv> instInpP Pinp 0 eN\<tau>"
  have [simp]: "\<phi>' \<in> fmla" "Fvars \<phi>' = {}" unfolding \<phi>'_def by auto

  have \<phi>\<phi>': "prv (imp \<phi> \<phi>')" and \<phi>'\<phi>: "prv (imp \<phi>' \<phi>)" and \<phi>e\<phi>': "prv (eqv \<phi> \<phi>')"
   unfolding \<phi>_def \<phi>J_def \<phi>'_def eN\<tau>_def \<tau>_def[symmetric] unfolding \<psi>_def
   using prv_instInpP_compose[of Pinp "encF N" \<tau>] by auto

  from diagonalization[OF \<psi>]
  have "prveqlPT \<tau> \<langle>instInpP \<psi> 0 \<tau>\<rangle>" and **: "prv (eqv \<phi> (instInp \<psi> \<langle>\<phi>\<rangle>))"
  unfolding \<tau>_def[symmetric] \<phi>_def[symmetric] by auto
  have "**1": "prv (imp \<phi> (instInp \<psi> \<langle>\<phi>\<rangle>))" "prv (imp (instInp \<psi> \<langle>\<phi>\<rangle>) \<phi>)"
   using prv_imp_eqvEL[OF _ _ **] prv_imp_eqvER[OF _ _ **] by auto

  from SHBL3[OF eN\<tau>(1)]
  have "prv (imp (instInpP Pinp 0 eN\<tau>) (instInp Pinp \<langle>instInpP Pinp 0 eN\<tau>\<rangle>))" .
  hence "prv (imp \<phi>' (instInp Pinp \<langle>\<phi>'\<rangle>))" unfolding \<phi>'_def .
  from prv_prv_imp_trans[OF _ _ _ \<phi>\<phi>' this]
  have 0: "prv (imp \<phi> (instInp Pinp \<langle>\<phi>'\<rangle>))" by auto

  note unr = unstated[unfolded Let_def
    \<phi>_def[unfolded \<phi>J_def \<tau>_def[symmetric], symmetric] \<psi>_def[symmetric]
      \<tau>_def[symmetric] eN\<tau>_def[symmetric] \<phi>'_def[symmetric] \<phi>J_def]

  have 1: "prv (imp \<phi> (instInp Pinp \<langle>\<phi>\<rangle>))"
  apply(nrule r: nprv_prvI)
  apply(nrule r: nprv_impI)
  apply(nrule r: nprv_addLemmaE[OF unr])
  apply(nrule r: nprv_addImpLemmaE[OF 0])
  apply(nrule r: nprv_clear3_3)
  by (simp add: nprv_clear2_2 prv_nprv1I unr)

  have 2: "prv (imp \<phi> (cnj (instInp Pinp \<langle>\<phi>\<rangle>)
                           (instInp \<psi> \<langle>\<phi>\<rangle>)))"
  apply(nrule r: nprv_prvI)
  apply(nrule r: nprv_impI)
  apply(nrule r: nprv_cnjI)
  subgoal apply(nrule r: nprv_addImpLemmaE[OF 1]) .
  subgoal apply(nrule r: nprv_addImpLemmaE[OF "**1"(1)]) . .

  define z where "z \<equiv> Variable (Suc (Suc 0))"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<notin> Fvars Pinp"
    "out \<noteq> z \<and> z \<noteq> out" "inp \<noteq> z \<and> z \<noteq> inp"
   unfolding z_def by auto

  have 30: "subst (instInpP Pinp 0 (instInp (encF N) (Var xx))) \<langle>\<phi>\<rangle> xx =
            instInpP Pinp 0 (instInp (encF N) \<langle>\<phi>\<rangle>)"
  unfolding z_def[symmetric] instInp_def instInpP_def Let_def
  by (variousSubsts4 auto
        s1: subst_compose_diff s2: subst_subst
        s3: subst_notIn[of _ _ xx] s4: subst_compose_diff)
  have 31: "subst (instInp Pinp (Var xx)) \<langle>\<phi>\<rangle> xx =
            instInp Pinp \<langle>\<phi>\<rangle>" unfolding instInp_def by auto
  have [simp]: "instInp (instInpP Pinp (Suc 0) (encF N)) \<langle>\<phi>\<rangle> =
           instInpP Pinp 0 (instInp (encF N) \<langle>\<phi>\<rangle>)"
  by (auto simp: instInp_instInpP \<psi>_def)

  have 3: "prv (neg (cnj (instInp Pinp \<langle>\<phi>\<rangle>)
                         (instInp \<psi> \<langle>\<phi>\<rangle>)))"
  apply(nrule r: nprv_prvI)
  apply(nrule r: nprv_addLemmaE[OF *, unfolded jcons_def])
  apply(rule nprv_allE0[of _ _ _ "\<langle>\<phi>\<rangle>"], auto)
  unfolding 30 31
  apply(nrule r: nprv_clear2_2)
  apply(nrule r: nprv_negI)
  apply(nrule r: nprv_negE0)
  apply(nrule r: nprv_clear2_2)
  apply(nrule r: nprv_cnjE0)
  apply(nrule r: nprv_clear3_3)
  apply(nrule r: nprv_cnjI)
  apply(nrule r: nprv_clear2_1)
  unfolding \<psi>_def
  apply(nrule r: nprv_hyp) .

  have ***: "prv (neg \<phi>)"
  apply(nrule r: nprv_prvI)
  apply(nrule r: nprv_negI)
  apply(nrule r: nprv_addImpLemmaE[OF 2])
  apply(nrule r: nprv_addLemmaE[OF 3])
  apply(nrule r: nprv_negE0) .

  have 4: "prv (instInp Pinp \<langle>neg \<phi>\<rangle>)" using HBL1_inp[OF _ _ ***] by auto

  have 5: "prveqlPT (instInp (encF N) \<langle>\<phi>\<rangle>) \<langle>neg \<phi>\<rangle>"
    using ReprF_combineWith_CapN[of \<phi>] by auto

  have [simp]: "instInp (encF N) \<langle>\<phi>\<rangle> \<in> ptrm 0" using instInp by auto

  have 6: "prv (instInpP Pinp 0 (instInp (encF N) \<langle>\<phi>\<rangle>))"
  apply(nrule r: nprv_prvI)
  apply(nrule r: nprv_addLemmaE[OF 4])
  apply(nrule r: prveqlPT_nprv_instInpP_instInp[OF _ _ _ _ _ 5]) .

  note lem = "**1"(2)[unfolded \<psi>_def]
  have "prv \<phi>"
  apply(nrule r: nprv_prvI)
  apply(nrule r: nprv_addLemmaE[OF 6])
  apply(nrule r: nprv_addImpLemmaE[OF lem]) .

  from this *** \<open>consistent\<close> show False unfolding consistent_def3 by auto
qed

end \<comment> \<open>context @{locale Jeroslow_Godel_Second}\<close>

(*<*)
end
(*>*)
