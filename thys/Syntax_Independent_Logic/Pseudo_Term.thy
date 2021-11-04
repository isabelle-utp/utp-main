chapter \<open>Pseudo-Terms\<close>

(*<*)
theory Pseudo_Term
  imports Natural_Deduction
begin
(*>*)

text \<open>Pseudo-terms are formulas that satisfy the exists-unique property
on one of their variables.\<close>

section \<open>Basic Setting\<close>

context Generic_Syntax
begin

text \<open>We choose a specific variable, out, that will represent the
"output" of pseudo-terms, i.e., the variable on which the exists-unique property holds:\<close>
abbreviation "out \<equiv> Variable 0"
text \<open>Many facts will involve pseudo-terms with only one additional "input" variable, inp:\<close>
abbreviation "inp \<equiv> Variable (Suc 0)"

(* These facts can speed up simplification: *)
lemma out_inp_distinct[simp]:
"out \<noteq> inp" "inp \<noteq> out"
"out \<noteq> xx" "out \<noteq> yy" "yy \<noteq> out" "out \<noteq> zz" "zz \<noteq> out" "out \<noteq> xx'" "xx' \<noteq> out"
   "out \<noteq> yy'" "yy' \<noteq> out" "out \<noteq> zz'" "zz' \<noteq> out"
"inp \<noteq> xx" "inp \<noteq> yy" "yy \<noteq> inp" "inp \<noteq> zz" "zz \<noteq> inp" "inp \<noteq> xx'" "xx' \<noteq> inp"
   "inp \<noteq> yy'" "yy' \<noteq> inp" "inp \<noteq> zz'" "zz' \<noteq> inp"
by auto

end (* context Generic_Syntax *)


context Deduct_with_False_Disj_Rename
begin

text \<open>Pseudo-terms over the first $n+1$ variables, i.e.,
having $n$ input variables (Variable $1$ to Variable $n$), and an output variable, out (which is
an abbreviation for Variable $0$).\<close>
definition ptrm :: "nat \<Rightarrow> 'fmla set" where
"ptrm n \<equiv> {\<sigma> \<in> fmla . Fvars \<sigma> = Variable ` {0..n} \<and> prv (exu out \<sigma>)}"

lemma ptrm[intro,simp]: "\<sigma> \<in> ptrm n \<Longrightarrow> \<sigma> \<in> fmla"
  unfolding ptrm_def by auto

lemma ptrm_1_Fvars[simp]: "\<sigma> \<in> ptrm (Suc 0) \<Longrightarrow> Fvars \<sigma> = {out,inp}"
	unfolding ptrm_def by auto

lemma ptrm_prv_exu: "\<sigma> \<in> ptrm n \<Longrightarrow> prv (exu out \<sigma>)"
  unfolding ptrm_def by auto

lemma ptrm_prv_exi: "\<sigma> \<in> ptrm n \<Longrightarrow> prv (exi out \<sigma>)"
  by (simp add: ptrm_prv_exu prv_exu_exi)

lemma nprv_ptrmE_exi:
"\<sigma> \<in> ptrm n \<Longrightarrow> nprv (insert \<sigma> F) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow>
 \<psi> \<in> fmla \<Longrightarrow> out \<notin> Fvars \<psi> \<Longrightarrow> out \<notin> \<Union> (Fvars ` F) \<Longrightarrow> nprv F \<psi>"
  apply (frule ptrm_prv_exu, drule ptrm)
  apply(rule nprv_exuE_exi[of _ out \<sigma>])
  by (auto intro!: prv_nprvI)

lemma nprv_ptrmE_uni:
"\<sigma> \<in> ptrm n \<Longrightarrow> nprv F (subst \<sigma> t1 out) \<Longrightarrow> nprv F (subst \<sigma> t2 out) \<Longrightarrow>
 nprv (insert (eql t1 t2) F) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> t1 \<in> trm \<Longrightarrow> t2 \<in> trm
 \<Longrightarrow> nprv F \<psi>"
  apply (frule ptrm_prv_exu, drule ptrm)
  apply(rule nprv_exuE_uni[of _ out \<sigma> t1 t2])
  by (auto intro!: prv_nprvI)

lemma nprv_ptrmE_uni0:
"\<sigma> \<in> ptrm n \<Longrightarrow> nprv F \<sigma> \<Longrightarrow> nprv F (subst \<sigma> t out) \<Longrightarrow>
 nprv (insert (eql (Var out) t) F) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> t \<in> trm
 \<Longrightarrow> nprv F \<psi>"
   by (rule nprv_ptrmE_uni[of \<sigma> _ _ "Var out" t]) auto

lemma nprv_ptrmE0_uni0:
"\<sigma> \<in> ptrm n \<Longrightarrow> \<sigma> \<in> F \<Longrightarrow> nprv F (subst \<sigma> t out) \<Longrightarrow>
 nprv (insert (eql (Var out) t) F) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> t \<in> trm
 \<Longrightarrow> nprv F \<psi>"
by (rule nprv_ptrmE_uni0[of \<sigma> n _ t]) auto


section \<open>The $\forall$-$\exists$ Equivalence\<close>

text \<open>There are two natural ways to state that (unique) "output" of a pseudo-term @{term \<sigma>}
satisfies a property @{term \<phi>}:
(1) using $\exists$: there exists an "out" such that @{term \<sigma>} and @{term \<phi>} hold for it;
(2) using $\forall$: for all "out" such that @{term \<sigma>} holds for it, @{term \<phi>} holds for it as well.

We prove the well-known fact that these two ways are equivalent. (Intuitionistic
logic suffice to prove that.)\<close>

lemma ptrm_nprv_exi:
assumes \<sigma>: "\<sigma> \<in> ptrm n" and [simp]: "\<phi> \<in> fmla"
shows "nprv {\<sigma>, exi out (cnj \<sigma> \<phi>)} \<phi>"
proof-
  have [simp]: "\<sigma> \<in> fmla" using \<sigma> by simp
  define z where "z \<equiv> getFr [out] [] [\<sigma>,\<phi>]"
  have z_facts[simp]: "z \<in> var" "z \<noteq> out" "z \<notin> Fvars \<sigma>" "z \<notin> Fvars \<phi>"
  using getFr_FvarsT_Fvars[of "[out]" "[]" "[\<sigma>,\<phi>]"] unfolding z_def[symmetric] by auto
  have 0: "exi out (cnj \<sigma> \<phi>) = exi z (subst (cnj \<sigma> \<phi>) (Var z) out)"
    by(rule exi_rename, auto)
  show ?thesis
    unfolding 0
    apply(nrule r: nprv_exiE0[of z "subst (cnj \<sigma> \<phi>) (Var z) out"])
    apply(nrule2 r: nprv_ptrmE0_uni0[OF \<sigma>, of _ "Var z"])
      subgoal by (nrule r: nprv_cnjE0)
      subgoal
        apply(nrule r: nprv_clear4_4)
        apply(nrule r: nprv_clear3_3)
        apply (nrule r: nprv_cnjE0)
        apply(nrule r: nprv_clear4_4)
        apply(nrule r: nprv_clear3_1)
        apply(nrule r: nprv_eql_substE012[of "Var out" "Var z" _ \<phi> out \<phi>]) . .
qed

lemma ptrm_nprv_exi_all:
  assumes \<sigma>: "\<sigma> \<in> ptrm n" and [simp]: "\<phi> \<in> fmla"
  shows "nprv {exi out (cnj \<sigma> \<phi>)} (all out (imp \<sigma> \<phi>))"
proof-
  have [simp]: "\<sigma> \<in> fmla" using \<sigma> by simp
  show ?thesis
  apply(nrule r: nprv_allI)
  apply(nrule r: nprv_impI)
  apply(nrule r: ptrm_nprv_exi[OF \<sigma>]) .
qed

lemma ptrm_prv_exi_imp_all:
  assumes \<sigma>: "\<sigma> \<in> ptrm n" and [simp]: "\<phi> \<in> fmla"
  shows "prv (imp (exi out (cnj \<sigma> \<phi>)) (all out (imp \<sigma> \<phi>)))"
proof-
  have [simp]: "\<sigma> \<in> fmla" using \<sigma> by simp
  show ?thesis
  apply(nrule r: nprv_prvI)
  apply(nrule r: nprv_impI)
  apply(nrule r: ptrm_nprv_exi_all[OF \<sigma>]) .
qed

lemma ptrm_nprv_all_imp_exi:
  assumes \<sigma>: "\<sigma> \<in> ptrm n" and [simp]: "\<phi> \<in> fmla"
  shows "nprv {all out (imp \<sigma> \<phi>)} (exi out (cnj \<sigma> \<phi>))"
proof-
  have [simp]: "\<sigma> \<in> fmla" using \<sigma> by simp
  define z where "z \<equiv> getFr [out] [] [\<sigma>,\<phi>]"
  have z_facts[simp]: "z \<in> var" "z \<noteq> out" "z \<notin> Fvars \<sigma>" "z \<notin> Fvars \<phi>"
  using getFr_FvarsT_Fvars[of "[out]" "[]" "[\<sigma>,\<phi>]"] unfolding z_def[symmetric] by auto
  show ?thesis
    apply(nrule r: nprv_ptrmE_exi[OF \<sigma>])
    apply(nrule r: nprv_exiI[of _ "cnj \<sigma> \<phi>" "Var out" out])
    apply(nrule r: nprv_allE0[of out "imp \<sigma> \<phi>" _ "Var out"])
    apply(nrule r: nprv_clear3_3)
    apply(nrule r: nprv_cnjI)
    apply(nrule r: nprv_impE01) .
qed

lemma ptrm_prv_all_imp_exi:
  assumes \<sigma>: "\<sigma> \<in> ptrm n" and [simp]: "\<phi> \<in> fmla"
  shows "prv (imp (all out (imp \<sigma> \<phi>)) (exi out (cnj \<sigma> \<phi>)))"
proof-
  have [simp]: "\<sigma> \<in> fmla" using \<sigma> by simp
  define z where "z \<equiv> getFr [out] [] [\<sigma>,\<phi>]"
  have z_facts[simp]: "z \<in> var" "z \<noteq> out" "z \<notin> Fvars \<sigma>" "z \<notin> Fvars \<phi>"
  using getFr_FvarsT_Fvars[of "[out]" "[]" "[\<sigma>,\<phi>]"] unfolding z_def[symmetric] by auto
  show ?thesis
  apply(nrule r: nprv_prvI)
  apply(nrule r: nprv_impI)
  apply(nrule r: ptrm_nprv_all_imp_exi[OF \<sigma>]) .
qed

end \<comment> \<open>context @{locale Deduct_with_False_Disj_Rename }\<close>

section \<open>Instantiation\<close>

text \<open>We define the notion of instantiating the "inp" variable of a formula
(in particular, of a pseudo-term):
-- first with a term);
-- then with a pseudo-term.
\<close>

subsection \<open>Instantiation with terms\<close>

text \<open>Instantiation with terms is straightforward using substitution.
In the name of the operator, the suffix "Inp" is a reminder that we instantiate @{term \<phi>}
on its variable "inp".\<close>


context Generic_Syntax
begin

definition instInp :: "'fmla \<Rightarrow> 'trm \<Rightarrow> 'fmla" where
"instInp \<phi> t \<equiv> subst \<phi> t inp"

lemma instInp_fmla[simp,intro]:
assumes "\<phi> \<in> fmla" and "t \<in> trm"
shows "instInp \<phi> t \<in> fmla"
using assms instInp_def by auto

lemma Fvars_instInp[simp,intro]:
assumes "\<phi> \<in> fmla" and "t \<in> trm" "Fvars \<phi> = {inp}"
shows "Fvars (instInp \<phi> t) = FvarsT t"
using assms instInp_def by auto

end \<comment> \<open>context @{locale Generic_Syntax }\<close>


context Deduct_with_False_Disj_Rename
begin

lemma Fvars_instInp_ptrm_1[simp,intro]:
assumes \<tau>: "\<tau> \<in> ptrm (Suc 0)" and "t \<in> trm"
shows "Fvars (instInp \<tau> t) = insert out (FvarsT t)"
using assms instInp_def by auto

lemma instInp:
assumes \<tau>: "\<tau> \<in> ptrm (Suc 0)" and [simp]: "t \<in> trm"
and [simp]: "FvarsT t = Variable ` {(Suc 0)..n}"
shows "instInp \<tau> t \<in> ptrm n"
proof-
  note Let_def[simp]
  have [simp]: "\<tau> \<in> fmla" "Fvars \<tau> = {out,inp}"
    using assms unfolding ptrm_def by auto
  have [simp]: "Fvars (instInp \<tau> t) = insert out (FvarsT t)"
     using \<tau> by (subst Fvars_instInp_ptrm_1) auto
  have 0: "exu out (instInp \<tau> t) = subst (exu out \<tau>) t inp"
    unfolding instInp_def by (subst subst_exu) auto
  have 1: "prv (exu out \<tau>)" using \<tau> unfolding ptrm_def by auto
  have "prv (exu out (instInp \<tau> t))"
  unfolding 0 by (rule prv_subst[OF _ _ _ 1], auto)
  thus ?thesis using assms unfolding ptrm_def[of n] by auto
qed

lemma instInp_0:
assumes \<tau>: "\<tau> \<in> ptrm (Suc 0)" and "t \<in> trm" and "FvarsT t = {}"
shows "instInp \<tau> t \<in> ptrm 0"
using assms by (intro instInp) auto

lemma instInp_1:
assumes \<tau>: "\<tau> \<in> ptrm (Suc 0)" and "t \<in> trm" and "FvarsT t = {inp}"
shows "instInp \<tau> t \<in> ptrm (Suc 0)"
using assms by (intro instInp) auto


subsection \<open>Instantiation with pseudo-terms\<close>

text \<open>Instantiation of a formula @{term \<phi>} with a pseudo-term @{term \<tau>} yields a formula that
could be casually written @{term [source] "\<phi>(\<tau>)"}. It states the existence of an output @{term zz} of @{term \<tau>} on which @{term \<phi>} holds.
Instead of @{term [source] "\<phi>(\<tau>)"}, we write @{term "instInpP \<phi> n \<tau>"} where @{term n} is the number of input variables of @{term \<tau>}.
In the name @{term "instInpP"}, @{term "Inp"} is as before a reminder that we instantiate @{term \<phi>} on its variable
"inp" and the suffix "P" stands for "Pseudo".\<close>

definition instInpP :: "'fmla \<Rightarrow> nat \<Rightarrow> 'fmla \<Rightarrow> 'fmla" where
"instInpP \<phi> n \<tau> \<equiv> let zz = Variable (Suc (Suc n)) in
   exi zz (cnj (subst \<tau> (Var zz) out) (subst \<phi> (Var zz) inp))"

lemma instInpP_fmla[simp, intro]:
	assumes "\<phi> \<in> fmla" and "\<tau> \<in> fmla"
	shows "instInpP \<phi> n \<tau> \<in> fmla"
	using assms unfolding instInpP_def by (auto simp: Let_def)

lemma Fvars_instInpP[simp]:
assumes "\<phi> \<in> fmla" and \<tau>: "\<tau> \<in> ptrm n"  "Variable (Suc (Suc n)) \<notin> Fvars \<phi>"
shows "Fvars (instInpP \<phi> n \<tau>) = Fvars \<phi> - {inp} \<union> Variable ` {(Suc 0)..n}"
using assms unfolding instInpP_def Let_def ptrm_def by auto

lemma Fvars_instInpP2[simp]:
assumes "\<phi> \<in> fmla" and \<tau>: "\<tau> \<in> ptrm n" and "Fvars \<phi> \<subseteq> {inp}"
shows "Fvars (instInpP \<phi> n \<tau>) = Fvars \<phi> - {inp} \<union> Variable ` {(Suc 0)..n}"
using assms by (subst Fvars_instInpP) auto


subsection \<open>Closure and compositionality properties of instantiation\<close>

text \<open>Instantiating a 1-pseudo-term with an n-pseudo-term yields an n pseudo-term:\<close>
(* This could be generalized, of course. *)
lemma instInpP1[simp,intro]:
assumes \<sigma>: "\<sigma> \<in> ptrm (Suc 0)" and \<tau>: "\<tau> \<in> ptrm n"
shows "instInpP \<sigma> n \<tau> \<in> ptrm n"
proof-
  note Let_def[simp]
  have [simp]: "\<sigma> \<in> fmla" "\<tau> \<in> fmla" "Fvars \<sigma> = {out,inp}"
   "Fvars \<tau> = Variable ` {0..n}"
    using assms unfolding ptrm_def by auto
  define zz where "zz \<equiv> Variable (Suc (Suc n))"
  have zz_facts[simp]: "zz \<in> var" "\<And>i. i \<le> n \<Longrightarrow> Variable i \<noteq> zz \<and> zz \<noteq> Variable i"
    "out \<noteq> zz" "zz \<noteq> out" "inp \<noteq> zz" "zz \<noteq> inp"
   unfolding zz_def by auto

  define x where "x \<equiv> getFr [out,inp,zz] [] [\<sigma>,\<tau>]"
  have x_facts[simp]: "x \<in> var" "x \<noteq> out" "x \<noteq> inp"
  "x \<noteq> zz" "zz \<noteq> x" "x \<notin> Fvars \<sigma>" "x \<notin> Fvars \<tau>"
  using getFr_FvarsT_Fvars[of "[out,inp,zz]" "[]" "[\<sigma>,\<tau>]"] unfolding x_def[symmetric] by auto
  have [simp]: "x \<noteq> Variable (Suc (Suc n))"
  	using x_facts(4) zz_def by auto
  define z where "z \<equiv> getFr [out,inp,zz,x] [] [\<sigma>,\<tau>]"
  have z_facts[simp]: "z \<in> var" "z \<noteq> out" "z \<noteq> inp" "z \<noteq> x" "z \<noteq> zz" "z \<notin> Fvars \<sigma>" "z \<notin> Fvars \<tau>"
  using getFr_FvarsT_Fvars[of "[out,inp,zz,x]" "[]" "[\<sigma>,\<tau>]"] unfolding z_def[symmetric] by auto

  have [simp]: "\<And>i. z = Variable i \<Longrightarrow> \<not> i \<le> n"
   and [simp]: "\<And>i. x = Variable i \<Longrightarrow> \<not> i \<le> n"
   using \<open>Fvars \<tau> = Variable ` {0..n}\<close> atLeastAtMost_iff z_facts(7) x_facts(7)
  by blast+

  have [simp]: "Fvars (instInpP \<sigma> n \<tau>) = Variable ` {0..n}"
    unfolding instInpP_def by auto
  have tt: "exi out \<tau> = exi zz (subst \<tau> (Var zz) out)"
    by (rule exi_rename) auto

  have exi_\<sigma>: "prv (exi out \<sigma>)" and exi_\<tau>: "prv (exi zz (subst \<tau> (Var zz) out))"
  	using \<sigma> \<tau> ptrm_prv_exi tt by fastforce+ 	
  have exi_\<sigma>: "prv (exi out (subst \<sigma> (Var zz) inp))"
    using prv_subst[OF _ _ _ exi_\<sigma>, of inp "Var zz"] by auto

  have exu_\<sigma>: "prv (exu out \<sigma>)"
  	using \<sigma> ptrm_prv_exu by blast
  have exu_\<sigma>: "prv (exu out (subst \<sigma> (Var zz) inp))"
    using prv_subst[OF _ _ _ exu_\<sigma>, of inp "Var zz"] by auto

  have zz_z: "exi zz (cnj (subst \<tau> (Var zz) out) (subst \<sigma> (Var zz) inp)) =
              exi z (cnj (subst \<tau> (Var z) out) (subst \<sigma> (Var z) inp))"
  by (variousSubsts2 auto s1: exi_rename[of _ zz z] s2: subst_subst)

  have 0: "prv (exu out (instInpP \<sigma> n \<tau>))"
  apply(nrule r: nprv_prvI)
  apply(nrule2 r: nprv_exuI_exi[of _ _ _ x])
  subgoal unfolding instInpP_def Let_def
    apply(nrule r: nprv_addImpLemmaI[OF prv_exi_commute])
    apply(nrule r: nprv_addLemmaE[OF exi_\<tau>])
    apply(nrule r: nprv_exiE[of _ zz "subst \<tau> (Var zz) out"])
    apply(nrule r: nprv_clear2_2)
    apply(nrule r: nprv_exiI[of _ _ "Var zz"])
    apply(nrule r: nprv_addLemmaE[OF exi_\<sigma>])
    apply(nrule r: nprv_exiE[of _ out "subst \<sigma> (Var zz) inp"])
    apply(nrule r: nprv_clear3_2)
    apply(nrule r: nprv_exiI[of _ _ "Var out"])
      apply(variousSubsts1 auto s1: subst_subst)
    apply(nrule r: nprv_cnjI) .
  subgoal
    unfolding instInpP_def Let_def zz_def[symmetric]
    apply(nrule r: nprv_exiE0[of zz])
    apply(nrule r: nprv_clear3_2)
    apply(nrule r: nprv_cnjE0)
    apply(nrule r: nprv_clear4_3)
    unfolding zz_z
    apply(nrule r: nprv_exiE0[of z])
    apply(nrule r: nprv_clear4_4)
    apply(nrule r: nprv_cnjE0)
    apply(nrule r: nprv_clear5_3)
    apply(nrule r: nprv_cut[of _ "eql (Var z) (Var zz)"])
    subgoal by (nprover3 r1: nprv_clear4_2 r2: nprv_clear3_3
                  r3: nprv_ptrmE_uni[OF \<tau>, of _ "Var z" "Var zz"])
    subgoal
      apply(nrule r: nprv_clear5_2)
      apply(nrule r: nprv_clear4_3)
      apply(nrule2 r: nprv_eql_substE[of _ "Var zz" "Var z" \<sigma> inp])
      subgoal by (nrule r: nprv_eql_symE01)
      subgoal
        apply(nrule r: nprv_clear4_2)
        apply(nrule r: nprv_clear3_2)
        apply(nrule r: nprv_addLemmaE[OF exu_\<sigma>])
        apply(nrule r: nprv_exuE_uni[of _ out "subst \<sigma> (Var zz) inp" "Var out" "Var x"])
        apply(nrule r: nprv_eql_symE01) . . . .
	show ?thesis using 0 unfolding ptrm_def instInpP_def Let_def by auto
qed		

text \<open>Term and pseudo-term instantiation compose smoothly:\<close>
lemma instInp_instInpP:
assumes \<phi>: "\<phi> \<in> fmla" "Fvars \<phi> \<subseteq> {inp}" and \<tau>: "\<tau> \<in> ptrm (Suc 0)"
and "t \<in> trm" and "FvarsT t = {}"
shows "instInp (instInpP \<phi> (Suc 0) \<tau>) t = instInpP \<phi> 0 (instInp \<tau> t)"
proof-
  define x1 and x2 where
   x12: "x1 \<equiv> Variable (Suc (Suc 0))"
        "x2 \<equiv> Variable (Suc (Suc (Suc 0)))"
  have x_facts[simp]: "x1 \<in> var" "x2 \<in> var" "x1 \<noteq> inp" "x2 \<noteq> inp"
   "x1 \<noteq> out" "out \<noteq> x1" "x2 \<noteq> out" "out \<noteq> x2" "x1 \<noteq> x2" "x2 \<noteq> x1"
   unfolding x12 by auto
  show ?thesis
  using assms unfolding instInp_def instInpP_def Let_def x12[symmetric]

  apply(subst subst_exi)
  apply(TUF simp)

  apply(variousSubsts5 auto
   s1: subst_compose_same
   s2: subst_compose_diff
   s3: exi_rename[of _ x1 x2]
   s4: subst_comp
   s5: subst_notIn[of \<phi> _ x1]
  ) .
qed

text \<open>Pseudo-term instantiation also composes smoothly with itself:\<close>
lemma nprv_instInpP_compose:
assumes [simp]: "\<chi> \<in> fmla" "Fvars \<chi> = {inp}"
and \<sigma>[simp]: "\<sigma> \<in> ptrm (Suc 0)" and \<tau>[simp]: "\<tau> \<in> ptrm 0"
shows "nprv {instInpP (instInpP \<chi> (Suc 0) \<sigma>) 0 \<tau>}
            (instInpP \<chi> 0 (instInpP \<sigma> 0 \<tau>))" (is ?A)
and
      "nprv {instInpP \<chi> 0 (instInpP \<sigma> 0 \<tau>)}
            (instInpP (instInpP \<chi> (Suc 0) \<sigma>) 0 \<tau>)" (is ?B)
proof-
  define \<chi>\<sigma> and \<sigma>\<tau> where \<chi>\<sigma>_def: "\<chi>\<sigma> \<equiv> instInpP \<chi> (Suc 0) \<sigma>" and \<sigma>\<tau>_def: "\<sigma>\<tau> \<equiv> instInpP \<sigma> 0 \<tau>"

  have [simp]: "\<sigma> \<in> fmla" "Fvars \<sigma> = {out,inp}" "\<tau> \<in> fmla" "Fvars \<tau> = {out}"
    using \<sigma> \<tau> unfolding ptrm_def by auto
  have \<chi>\<sigma>[simp]: "\<chi>\<sigma> \<in> fmla" "Fvars \<chi>\<sigma> = {inp}"
    unfolding \<chi>\<sigma>_def by auto
  have \<sigma>\<tau>[simp]:  "\<sigma>\<tau> \<in> ptrm 0" "\<sigma>\<tau> \<in> fmla" "Fvars \<sigma>\<tau> = {out}" unfolding \<sigma>\<tau>_def
    by auto
  define z where "z \<equiv> Variable (Suc (Suc 0))"
  have z_facts[simp]: "z \<in> var"
    "out \<noteq> z \<and> z \<noteq> out" "inp \<noteq> z \<and> z \<noteq> inp" "z \<notin> Fvars \<chi>" "z \<notin> Fvars \<sigma>" "z \<notin> Fvars \<tau>"
   unfolding z_def by auto
  define zz where "zz \<equiv> Variable (Suc (Suc (Suc 0)))"
  have zz_facts[simp]: "zz \<in> var"
    "out \<noteq> zz \<and> zz \<noteq> out" "inp \<noteq> zz \<and> zz \<noteq> inp" "z \<noteq> zz \<and> zz \<noteq> z"
    "zz \<notin> Fvars \<chi>" "zz \<notin> Fvars \<sigma>" "zz \<notin> Fvars \<tau>"
   unfolding zz_def z_def by auto
  define z' where "z' \<equiv> getFr [out,inp,z,zz] [] [\<chi>,\<sigma>,\<tau>]"
  have z'_facts[simp]: "z' \<in> var" "z' \<noteq> out" "z' \<noteq> inp" "z' \<noteq> z" "z \<noteq> z'" "z' \<noteq> zz" "zz \<noteq> z'"
   "z' \<notin> Fvars \<chi>""z' \<notin> Fvars \<sigma>" "z' \<notin> Fvars \<tau>"
  using getFr_FvarsT_Fvars[of "[out,inp,z,zz]" "[]" "[\<chi>,\<sigma>,\<tau>]"] unfolding z'_def[symmetric] by auto

  have \<chi>\<sigma>': "instInpP \<chi>\<sigma> 0 \<tau> = exi z' (cnj (subst \<tau> (Var z') out) (subst \<chi>\<sigma> (Var z') inp))"
    unfolding instInpP_def Let_def z_def[symmetric]
    by (auto simp: exi_rename[of _ z z'])
  have \<chi>\<sigma>z': "subst \<chi>\<sigma> (Var z') inp =
    exi zz (cnj (subst (subst \<sigma> (Var zz) out) (Var z') inp) (subst \<chi> (Var zz) inp))"
  unfolding \<chi>\<sigma>_def instInpP_def Let_def zz_def[symmetric]
  by (auto simp: subst_compose_same)
  have \<sigma>\<tau>zz: "subst \<sigma>\<tau> (Var zz) out =
     exi z (cnj (subst \<tau> (Var z) out) (subst (subst \<sigma> (Var zz) out) (Var z) inp))"
  unfolding \<sigma>\<tau>_def instInpP_def Let_def z_def[symmetric]
  by (variousSubsts2 auto s1: subst_compose_same s2: subst_compose_diff)

  have "nprv {instInpP \<chi>\<sigma> 0 \<tau>} (instInpP \<chi> 0 \<sigma>\<tau>)"
  unfolding \<chi>\<sigma>'
  apply(nrule r: nprv_exiE0)
  apply(nrule r: nprv_clear2_2)
  apply(nrule r: nprv_cnjE0)
  apply(nrule r: nprv_clear3_3)
  unfolding \<chi>\<sigma>z'
  apply(nrule r: nprv_exiE0)
  apply(nrule r: nprv_clear3_3)
  apply(nrule r: nprv_cnjE0)
  apply(nrule r: nprv_clear4_3)
  unfolding instInpP_def Let_def z_def[symmetric]
  apply(nrule r: nprv_exiI[of _ _ "Var zz"])
  apply(nrule r: nprv_cnjI)
  apply(nrule r: nprv_clear3_2)
  unfolding \<sigma>\<tau>zz
  apply(nrule r: nprv_exiI[of _ _ "Var z'"])
  apply(nrule r: nprv_cnjI) .
  thus ?A unfolding \<chi>\<sigma>_def \<sigma>\<tau>_def .

  have \<chi>\<sigma>\<tau>: "instInpP \<chi> 0 \<sigma>\<tau> = exi z' (cnj (subst \<sigma>\<tau> (Var z') out) (subst \<chi> (Var z') inp))"
  unfolding instInpP_def Let_def z_def[symmetric]
  by (auto simp: exi_rename[of _ z z'])

  have \<sigma>\<tau>z': "subst \<sigma>\<tau> (Var z') out =
   exi z (cnj (subst \<tau> (Var z) out) (subst (subst \<sigma> (Var z) inp) (Var z') out))"
  unfolding \<sigma>\<tau>_def instInpP_def Let_def z_def[symmetric]
  by (auto simp: subst_compose_same)

  have \<chi>\<sigma>z: "subst \<chi>\<sigma> (Var z) inp =
    exi zz (cnj (subst (subst \<sigma> (Var z) inp) (Var zz) out) (subst \<chi> (Var zz) inp))"
  unfolding \<chi>\<sigma>_def instInpP_def Let_def zz_def[symmetric]
  by (variousSubsts2 auto s1: subst_compose_same s2: subst_compose_diff)

  have "nprv {instInpP \<chi> 0 \<sigma>\<tau>} (instInpP \<chi>\<sigma> 0 \<tau>)"
  unfolding \<chi>\<sigma>\<tau>
  apply(nrule r: nprv_exiE0)
  apply(nrule r: nprv_clear2_2)
  apply(nrule r: nprv_cnjE0)
  apply(nrule r: nprv_clear3_3)
  unfolding \<sigma>\<tau>z'
  apply(nrule r: nprv_exiE0)
  apply(nrule r: nprv_clear3_2)
  apply(nrule r: nprv_cnjE0)
  apply(nrule r: nprv_clear4_3)
  unfolding instInpP_def Let_def z_def[symmetric]
  apply(nrule r: nprv_exiI[of _ _ "Var z"])
  apply(nrule r: nprv_cnjI)
  unfolding \<chi>\<sigma>z
  apply(nrule r: nprv_exiI[of _ _ "Var z'"])
  apply(nrule r: nprv_cnjI) .
  thus ?B unfolding \<chi>\<sigma>_def \<sigma>\<tau>_def .
qed

lemma prv_instInpP_compose:
assumes [simp]: "\<chi> \<in> fmla" "Fvars \<chi> = {inp}"
and \<sigma>[simp]: "\<sigma> \<in> ptrm (Suc 0)" and \<tau>[simp]: "\<tau> \<in> ptrm 0"
shows "prv (imp (instInpP (instInpP \<chi> (Suc 0) \<sigma>) 0 \<tau>)
                (instInpP \<chi> 0 (instInpP \<sigma> 0 \<tau>)))" (is ?A)
and
      "prv (imp (instInpP \<chi> 0 (instInpP \<sigma> 0 \<tau>))
                (instInpP (instInpP \<chi> (Suc 0) \<sigma>) 0 \<tau>))" (is ?B)
and
      "prv (eqv (instInpP (instInpP \<chi> (Suc 0) \<sigma>) 0 \<tau>)
                (instInpP \<chi> 0 (instInpP \<sigma> 0 \<tau>)))" (is ?C)
proof-
  have [simp]: "\<sigma> \<in> fmla" "Fvars \<sigma> = {out,inp}" "\<tau> \<in> fmla" "Fvars \<tau> = {out}"
  using \<sigma> \<tau> unfolding ptrm_def by auto
  show ?A ?B by (intro nprv_prvI nprv_impI nprv_instInpP_compose, auto)+
  thus ?C by (intro prv_eqvI) auto
qed


section \<open>Equality between Pseudo-Terms and Terms\<close>

text \<open>Casually, the equality between a pseudo-term @{term \<tau>} and a term @{term t} can
be written as $\vdash\tau = t$. This is in fact the (provability of)
the instantiation of @{term \<tau>} with @{term t} on @{term \<tau>}'s output variable out. Indeed, this
formula says that the unique entity denoted by @{term \<tau>} is exactly @{term t}.\<close>

definition prveqlPT :: "'fmla \<Rightarrow> 'trm \<Rightarrow> bool" where
"prveqlPT \<tau> t \<equiv> prv (subst \<tau> t out)"


text \<open>We prove that term--pseudo-term equality indeed acts like an equality,
in that it satisfies the substitutivity principle (shown only in the
particular case of formula-input instantiation).\<close>

lemma prveqlPT_nprv_instInp_instInpP:
assumes[simp]: "\<phi> \<in> fmla" and f: "Fvars \<phi> \<subseteq> {inp}" and \<tau>: "\<tau> \<in> ptrm 0"
and [simp]: "t \<in> trm" "FvarsT t = {}"
and \<tau>t: "prveqlPT \<tau> t"
shows "nprv {instInpP \<phi> 0 \<tau>} (instInp \<phi> t)"
proof-
  have [simp]: "\<tau> \<in> fmla" "Fvars \<tau> = {out}" using \<tau> unfolding ptrm_def by auto
  define zz where "zz \<equiv> Variable (Suc (Suc 0))"
  have zz_facts[simp]: "zz \<in> var"
    "out \<noteq> zz \<and> zz \<noteq> out" "inp \<noteq> zz \<and> zz \<noteq> inp" "zz \<notin> Fvars \<tau>" "zz \<notin> Fvars \<phi>"
   unfolding zz_def using f by auto

  note lemma1 = nprv_addLemmaE[OF \<tau>t[unfolded prveqlPT_def]]

  show ?thesis unfolding instInpP_def Let_def zz_def[symmetric] instInp_def
  apply(nrule r: lemma1)
  apply(nrule r: nprv_exiE0[of zz])
  apply(nrule r: nprv_clear3_3)
  apply(nrule r: nprv_cnjE0)
  apply(nrule r: nprv_clear4_3)
  apply(nrule r: nprv_ptrmE_uni[OF \<tau>, of _ t "Var zz"])
  apply(nrule r: nprv_clear4_2)
  apply(nrule r: nprv_clear3_3)
  apply(nrule r: nprv_eql_substE012[of t "Var zz" _ \<phi> inp]) .
qed

lemma prveqlPT_prv_instInp_instInpP:
assumes"\<phi> \<in> fmla" and f: "Fvars \<phi> \<subseteq> {inp}" and \<tau>: "\<tau> \<in> ptrm 0"
and "t \<in> trm" "FvarsT t = {}"
and \<tau>t: "prveqlPT \<tau> t"
shows "prv (imp (instInpP \<phi> 0 \<tau>) (instInp \<phi> t))"
using assms by (intro nprv_prvI nprv_impI prveqlPT_nprv_instInp_instInpP) auto

lemma prveqlPT_nprv_instInpP_instInp:
assumes[simp]: "\<phi> \<in> fmla" and f: "Fvars \<phi> \<subseteq> {inp}" and \<tau>: "\<tau> \<in> ptrm 0"
and [simp]: "t \<in> trm" "FvarsT t = {}"
and \<tau>t: "prveqlPT \<tau> t"
shows "nprv {instInp \<phi> t} (instInpP \<phi> 0 \<tau>)"
proof-
  have [simp]: "\<tau> \<in> fmla" "Fvars \<tau> = {out}" using \<tau> unfolding ptrm_def by auto
  define zz where "zz \<equiv> Variable (Suc (Suc 0))"
  have zz_facts[simp]: "zz \<in> var"
    "out \<noteq> zz \<and> zz \<noteq> out" "inp \<noteq> zz \<and> zz \<noteq> inp" "zz \<notin> Fvars \<tau>" "zz \<notin> Fvars \<phi>"
   unfolding zz_def using f by auto

  note lemma1 = nprv_addLemmaE[OF \<tau>t[unfolded prveqlPT_def]]

  show ?thesis unfolding instInpP_def Let_def zz_def[symmetric] instInp_def
  by (nprover3 r1: lemma1 r2: nprv_exiI[of _ _ t] r3: nprv_cnjI)
qed

lemma prveqlPT_prv_instInpP_instInp:
assumes"\<phi> \<in> fmla" and f: "Fvars \<phi> \<subseteq> {inp}" and \<tau>: "\<tau> \<in> ptrm 0"
and "t \<in> trm" "FvarsT t = {}"
and \<tau>t: "prveqlPT \<tau> t"
shows "prv (imp (instInp \<phi> t) (instInpP \<phi> 0 \<tau>))"
using assms by (intro nprv_prvI nprv_impI prveqlPT_nprv_instInpP_instInp) auto

lemma prveqlPT_prv_instInp_eqv_instInpP:
assumes"\<phi> \<in> fmla" and f: "Fvars \<phi> \<subseteq> {inp}" and \<tau>: "\<tau> \<in> ptrm 0"
and "t \<in> trm" "FvarsT t = {}"
and \<tau>t: "prveqlPT \<tau> t"
shows "prv (eqv (instInpP \<phi> 0 \<tau>) (instInp \<phi> t))"
using assms prveqlPT_prv_instInp_instInpP prveqlPT_prv_instInpP_instInp
by (intro prv_eqvI) auto


end \<comment> \<open>context @{locale Deduct_with_False_Disj_Rename}\<close>

(*<*)
end
(*>*)