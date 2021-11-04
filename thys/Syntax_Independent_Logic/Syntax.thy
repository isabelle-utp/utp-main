chapter \<open>Syntax\<close>

(*<*)
theory Syntax
  imports Prelim
begin
(*>*)


section \<open>Generic Syntax\<close>

text \<open>We develop some generic (meta-)axioms for syntax and substitution.
We only assume that the syntax of our logic has notions of variable, term and formula,
which \emph{include} subsets of "numeric" variables, terms and formulas,
the latter being endowed with notions of free variables and substitution subject to
some natural properties.\<close>

locale Generic_Syntax =
  fixes
    var :: "'var set" \<comment> \<open>numeric variables (i.e., variables ranging over numbers)\<close>
    and trm :: "'trm set" \<comment> \<open>numeric trms, which include the numeric variables\<close>
    and fmla :: "'fmla set" \<comment> \<open>numeric formulas\<close>
    and Var :: "'var \<Rightarrow> 'trm" \<comment> \<open>trms include at least the variables\<close>
    and FvarsT :: "'trm \<Rightarrow> 'var set" \<comment> \<open>free variables for trms\<close>
    and substT :: "'trm \<Rightarrow> 'trm \<Rightarrow> 'var \<Rightarrow> 'trm" \<comment> \<open>substitution for trms\<close>
    and Fvars :: "'fmla \<Rightarrow> 'var set" \<comment> \<open>free variables for formulas\<close>
    and subst :: "'fmla \<Rightarrow> 'trm \<Rightarrow> 'var \<Rightarrow> 'fmla" \<comment> \<open>substitution for formulas\<close>
  assumes
    infinite_var: "infinite var" \<comment> \<open>the variables are assumed infinite\<close>
    and \<comment> \<open>Assumptions about the infrastructure (free vars, substitution and the embedding of variables into trms.
      NB: We need fewer assumptions for trm substitution than for formula substitution!\<close>
    Var[simp,intro!]: "\<And>x. x \<in> var \<Longrightarrow> Var x \<in> trm"
    and
    inj_Var[simp]: "\<And> x y. x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow> (Var x = Var y \<longleftrightarrow> x = y)"
    and
    finite_FvarsT: "\<And> t. t \<in> trm \<Longrightarrow> finite (FvarsT t)"
    and
    FvarsT: "\<And>t. t \<in> trm \<Longrightarrow> FvarsT t \<subseteq> var"
    and
    substT[simp,intro]: "\<And>t1 t x. t1 \<in> trm \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> substT t1 t x \<in> trm"
    and
    FvarsT_Var[simp]: "\<And> x. x \<in> var \<Longrightarrow> FvarsT (Var x) = {x}"
    and
    substT_Var[simp]: "\<And> x t y. x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow> t \<in> trm \<Longrightarrow>
      substT (Var x) t y = (if x  = y then t else Var x)"
    and
    substT_notIn[simp]:
    "\<And>t1 t2 x. x \<in> var \<Longrightarrow> t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> x \<notin> FvarsT t1 \<Longrightarrow> substT t1 t2 x = t1"
    and
    \<comment> \<open>Assumptions about the infrastructure (free vars and substitution) on formulas\<close>
    finite_Fvars: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> finite (Fvars \<phi>)"
    and
    Fvars: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> \<subseteq> var"
    and
    subst[simp,intro]: "\<And>\<phi> t x. \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> subst \<phi> t x \<in> fmla"
    and
    Fvars_subst_in:
    "\<And> \<phi> t x. \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> x \<in> Fvars \<phi> \<Longrightarrow>
      Fvars (subst \<phi> t x) = Fvars \<phi> - {x} \<union> FvarsT t"
    and
    subst_compose_eq_or:
    "\<And> \<phi> t1 t2 x1 x2. \<phi> \<in> fmla \<Longrightarrow> t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> x1 \<in> var \<Longrightarrow> x2 \<in> var \<Longrightarrow>
      x1 = x2 \<or> x2 \<notin> Fvars \<phi> \<Longrightarrow> subst (subst \<phi> t1 x1) t2 x2 = subst \<phi> (substT t1 t2 x2) x1"
    and
    subst_compose_diff:
    "\<And> \<phi> t1 t2 x1 x2. \<phi> \<in> fmla \<Longrightarrow> t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> x1 \<in> var \<Longrightarrow> x2 \<in> var \<Longrightarrow>
      x1 \<noteq> x2 \<Longrightarrow> x1 \<notin> FvarsT t2 \<Longrightarrow>
      subst (subst \<phi> t1 x1) t2 x2 = subst (subst \<phi> t2 x2) (substT t1 t2 x2) x1"
    and
    subst_same_Var[simp]:
    "\<And> \<phi> x. \<phi> \<in> fmla \<Longrightarrow> x \<in> var \<Longrightarrow> subst \<phi> (Var x) x = \<phi>"
    and
    subst_notIn[simp]:
    "\<And> x \<phi> t. \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> x \<notin> Fvars \<phi> \<Longrightarrow> subst \<phi> t x = \<phi>"
begin

lemma var_NE: "var \<noteq> {}"
using infinite_var by auto

lemma Var_injD: "Var x = Var y \<Longrightarrow> x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow> x = y"
by auto

lemma FvarsT_VarD: "x \<in> FvarsT (Var y) \<Longrightarrow> y \<in> var \<Longrightarrow> x = y"
by auto

lemma FvarsT': "t \<in> trm \<Longrightarrow> x \<in> FvarsT t \<Longrightarrow> x \<in> var"
using FvarsT by auto

lemma Fvars': "\<phi> \<in> fmla \<Longrightarrow> x \<in> Fvars \<phi> \<Longrightarrow> x \<in> var"
using Fvars by auto

lemma Fvars_subst[simp]:
  "\<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
  Fvars (subst \<phi> t x) = (Fvars \<phi> - {x}) \<union> (if x \<in> Fvars \<phi> then FvarsT t else {})"
  by (simp add: Fvars_subst_in)

lemma in_Fvars_substD:
  "y \<in> Fvars (subst \<phi> t x) \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var
   \<Longrightarrow> y \<in> (Fvars \<phi> - {x}) \<union> (if x \<in> Fvars \<phi> then FvarsT t else {})"
  using Fvars_subst by auto

lemma inj_on_Var: "inj_on Var var"
  using inj_Var unfolding inj_on_def by auto

lemma subst_compose_same:
  "\<And> \<phi> t1 t2 x. \<phi> \<in> fmla \<Longrightarrow> t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
  subst (subst \<phi> t1 x) t2 x = subst \<phi> (substT t1 t2 x) x"
  using subst_compose_eq_or by blast

lemma subst_subst[simp]:
  assumes \<phi>[simp]: "\<phi> \<in> fmla" and t[simp]:"t \<in> trm" and x[simp]:"x \<in> var" and y[simp]:"y \<in> var"
  assumes yy: "x \<noteq> y" "y \<notin> Fvars \<phi>"
  shows "subst (subst \<phi> (Var y) x) t y = subst \<phi> t x"
  using subst_compose_eq_or[OF \<phi> _ t x y, of "Var y"] using subst_notIn yy by simp

lemma subst_comp:
  "\<And> x y \<phi> t. \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow>
  x \<noteq> y \<Longrightarrow> y \<notin> FvarsT t \<Longrightarrow>
  subst (subst \<phi> (Var x) y) t x = subst (subst \<phi> t x) t y"
  by (simp add: subst_compose_diff)

lemma exists_nat_var:
  "\<exists> f::nat\<Rightarrow>'var. inj f \<and> range f \<subseteq> var"
  by (simp add: infinite_countable_subset infinite_var)

definition Variable :: "nat \<Rightarrow> 'var" where
  "Variable = (SOME f. inj f \<and> range f \<subseteq> var)"

lemma Variable_inj_var:
  "inj Variable \<and> range Variable \<subseteq> var"
  unfolding Variable_def using someI_ex[OF exists_nat_var] .

lemma inj_Variable[simp]: "\<And> i j. Variable i = Variable j \<longleftrightarrow> i = j"
  and Variable[simp,intro!]: "\<And>i. Variable i \<in> var"
  using Variable_inj_var image_def unfolding inj_def by auto

text \<open>Convenient notations for some variables
We reserve the first 10 indexes for any special variables we
may wish to consider later.\<close>
abbreviation xx where "xx \<equiv> Variable 10"
abbreviation yy where "yy \<equiv> Variable 11"
abbreviation zz where "zz \<equiv> Variable 12"

abbreviation xx' where "xx' \<equiv> Variable 13"
abbreviation yy' where "yy' \<equiv> Variable 14"
abbreviation zz' where "zz' \<equiv> Variable 15"

lemma xx: "xx \<in> var"
  and yy: "yy \<in> var"
  and zz: "zz \<in> var"
  and xx': "xx' \<in> var"
  and yy': "yy' \<in> var"
  and zz': "zz' \<in> var"
  by auto

lemma vars_distinct[simp]:
  "xx \<noteq> yy" "yy \<noteq> xx" "xx \<noteq> zz" "zz \<noteq> xx" "xx \<noteq> xx'" "xx' \<noteq> xx" "xx \<noteq> yy'" "yy' \<noteq> xx" "xx \<noteq> zz'" "zz' \<noteq> xx"
  "yy \<noteq> zz" "zz \<noteq> yy" "yy \<noteq> xx'" "xx' \<noteq> yy" "yy \<noteq> yy'" "yy' \<noteq> yy" "yy \<noteq> zz'" "zz' \<noteq> yy"
  "zz \<noteq> xx'" "xx' \<noteq> zz" "zz \<noteq> yy'" "yy' \<noteq> zz" "zz \<noteq> zz'" "zz' \<noteq> zz"
  "xx' \<noteq> yy'" "yy' \<noteq> xx'" "xx' \<noteq> zz'" "zz' \<noteq> xx'"
  "yy' \<noteq> zz'" "zz' \<noteq> yy'"
  by auto


subsection \<open>Instance Operator\<close>

definition inst :: "'fmla \<Rightarrow> 'trm \<Rightarrow> 'fmla" where
  "inst \<phi> t = subst \<phi> t xx"

lemma inst[simp]: "\<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> inst \<phi> t \<in> fmla"
  unfolding inst_def by auto

definition getFresh :: "'var set \<Rightarrow> 'var" where
  "getFresh V = (SOME x. x \<in> var \<and> x \<notin> V)"

lemma getFresh: "finite V \<Longrightarrow>  getFresh V \<in> var \<and> getFresh V \<notin> V"
  by (metis (no_types, lifting) finite_subset getFresh_def infinite_var someI_ex subsetI)

definition getFr :: "'var list \<Rightarrow> 'trm list \<Rightarrow> 'fmla list \<Rightarrow> 'var" where
  "getFr xs ts \<phi>s =
 getFresh (set xs \<union> (\<Union>(FvarsT ` set ts)) \<union> (\<Union>(Fvars ` set \<phi>s)))"

lemma getFr_FvarsT_Fvars:
  assumes "set xs \<subseteq> var" "set ts \<subseteq> trm" and "set \<phi>s \<subseteq> fmla"
  shows "getFr xs ts \<phi>s \<in> var \<and>
       getFr xs ts \<phi>s \<notin> set xs \<and>
       (t \<in> set ts \<longrightarrow> getFr xs ts \<phi>s \<notin> FvarsT t) \<and>
       (\<phi> \<in> set \<phi>s \<longrightarrow> getFr xs ts \<phi>s \<notin> Fvars \<phi>)"
proof-
  have "finite (set xs \<union> (\<Union>(FvarsT ` set ts)) \<union> (\<Union>(Fvars ` set \<phi>s)))"
    using assms finite_FvarsT finite_Fvars by auto
  from getFresh[OF this] show ?thesis using assms unfolding getFr_def by auto
qed

lemma getFr[simp,intro]:
  assumes "set xs \<subseteq> var" "set ts \<subseteq> trm" and "set \<phi>s \<subseteq> fmla"
  shows "getFr xs ts \<phi>s \<in> var"
  using assms getFr_FvarsT_Fvars by auto

lemma getFr_var:
  assumes "set xs \<subseteq> var" "set ts \<subseteq> trm" and "set \<phi>s \<subseteq> fmla" and "t \<in> set ts"
  shows "getFr xs ts \<phi>s \<notin> set xs"
  using assms getFr_FvarsT_Fvars by auto

lemma getFr_FvarsT:
  assumes "set xs \<subseteq> var" "set ts \<subseteq> trm" and "set \<phi>s \<subseteq> fmla" and "t \<in> set ts"
  shows "getFr xs ts \<phi>s \<notin> FvarsT t"
  using assms getFr_FvarsT_Fvars by auto

lemma getFr_Fvars:
  assumes "set xs \<subseteq> var" "set ts \<subseteq> trm" and "set \<phi>s \<subseteq> fmla" and "\<phi> \<in> set \<phi>s"
  shows "getFr xs ts \<phi>s \<notin> Fvars \<phi>"
  using assms getFr_FvarsT_Fvars by auto


subsection \<open>Fresh Variables\<close>

fun getFreshN :: "'var set \<Rightarrow> nat \<Rightarrow> 'var list" where
  "getFreshN V 0 = []"
| "getFreshN V (Suc n) = (let u = getFresh V in u # getFreshN (insert u V) n)"

lemma getFreshN: "finite V \<Longrightarrow>
  set (getFreshN V n) \<subseteq> var \<and> set (getFreshN V n) \<inter> V = {} \<and> length (getFreshN V n) = n \<and> distinct (getFreshN V n)"
  by (induct n arbitrary: V) (auto simp: getFresh Let_def)

definition getFrN :: "'var list \<Rightarrow> 'trm list \<Rightarrow> 'fmla list \<Rightarrow> nat \<Rightarrow> 'var list" where
  "getFrN xs ts \<phi>s n =
 getFreshN (set xs \<union> (\<Union>(FvarsT ` set ts)) \<union> (\<Union>(Fvars ` set \<phi>s))) n"

lemma getFrN_FvarsT_Fvars:
  assumes "set xs \<subseteq> var" "set ts \<subseteq> trm" and "set \<phi>s \<subseteq> fmla"
  shows "set (getFrN xs ts \<phi>s n) \<subseteq> var \<and>
       set (getFrN xs ts \<phi>s n) \<inter> set xs = {} \<and>
       (t \<in> set ts \<longrightarrow> set (getFrN xs ts \<phi>s n) \<inter> FvarsT t = {}) \<and>
       (\<phi> \<in> set \<phi>s \<longrightarrow> set (getFrN xs ts \<phi>s n) \<inter> Fvars \<phi> = {}) \<and>
       length (getFrN xs ts \<phi>s n) = n \<and>
       distinct (getFrN xs ts \<phi>s n)"
proof-
  have "finite (set xs \<union> (\<Union>(FvarsT ` set ts)) \<union> (\<Union>(Fvars ` set \<phi>s)))"
    using assms finite_FvarsT finite_Fvars by auto
  from getFreshN[OF this] show ?thesis using assms unfolding getFrN_def by auto
qed

lemma getFrN[simp,intro]:
  assumes "set xs \<subseteq> var" "set ts \<subseteq> trm" and "set \<phi>s \<subseteq> fmla"
  shows "set (getFrN xs ts \<phi>s n) \<subseteq> var"
  using assms getFrN_FvarsT_Fvars by auto

lemma getFrN_var:
  assumes "set xs \<subseteq> var" "set ts \<subseteq> trm" and "set \<phi>s \<subseteq> fmla" and "t \<in> set ts"
  shows "set (getFrN xs ts \<phi>s n) \<inter> set xs = {}"
  using assms getFrN_FvarsT_Fvars by auto

lemma getFrN_FvarsT:
  assumes "set xs \<subseteq> var" "set ts \<subseteq> trm" and "set \<phi>s \<subseteq> fmla" and "t \<in> set ts"
  shows "set (getFrN xs ts \<phi>s n) \<inter> FvarsT t = {}"
  using assms getFrN_FvarsT_Fvars by auto

lemma getFrN_Fvars:
  assumes "set xs \<subseteq> var" "set ts \<subseteq> trm" and "set \<phi>s \<subseteq> fmla" and "\<phi> \<in> set \<phi>s"
  shows "set (getFrN xs ts \<phi>s n) \<inter> Fvars \<phi> = {}"
  using assms getFrN_FvarsT_Fvars by auto

lemma getFrN_length:
  assumes "set xs \<subseteq> var" "set ts \<subseteq> trm" and "set \<phi>s \<subseteq> fmla"
  shows "length (getFrN xs ts \<phi>s n) = n"
  using assms getFrN_FvarsT_Fvars by auto

lemma getFrN_distinct[simp,intro]:
  assumes "set xs \<subseteq> var" "set ts \<subseteq> trm" and "set \<phi>s \<subseteq> fmla"
  shows "distinct (getFrN xs ts \<phi>s n)"
  using assms getFrN_FvarsT_Fvars by auto


subsection \<open>Parallel Term Substitution\<close>

fun rawpsubstT :: "'trm \<Rightarrow> ('trm \<times> 'var) list \<Rightarrow> 'trm" where
  "rawpsubstT t [] = t"
| "rawpsubstT t ((t1,x1) # txs) = rawpsubstT (substT t t1 x1) txs"

lemma rawpsubstT[simp]:
  assumes "t \<in> trm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
  shows "rawpsubstT t txs \<in> trm"
  using assms by (induct txs arbitrary: t) fastforce+

definition psubstT :: "'trm \<Rightarrow> ('trm \<times> 'var) list \<Rightarrow> 'trm" where
  "psubstT t txs =
    (let xs = map snd txs; ts = map fst txs; us = getFrN xs (t # ts) [] (length xs) in
      rawpsubstT (rawpsubstT t (zip (map Var us) xs)) (zip ts us))"

text \<open>The psubstT versions of the subst axioms.\<close>

lemma psubstT[simp,intro]:
  assumes "t \<in> trm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
  shows "psubstT t txs \<in> trm"
proof-
  define us where us: "us = getFrN (map snd txs) (t # map fst txs) [] (length txs)"
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> FvarsT t = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    "distinct us"
    using assms unfolding us
    using getFrN_FvarsT[of "map snd txs" "t # map fst txs" "[]" _ "length txs"]
      getFrN_var[of "map snd txs" "t # map fst txs" "[]" _ "length txs"]
      getFrN_length[of "map snd txs" "t # map fst txs" "[]" "length txs"]
      getFrN_distinct[of "map snd txs" "t # map fst txs" "[]" "length txs"]
    by auto (metis (no_types, hide_lams) IntI empty_iff image_iff old.prod.inject surjective_pairing)
  show ?thesis using assms us_facts unfolding psubstT_def
    by (force simp: Let_def us[symmetric] dest: set_zip_leftD set_zip_rightD intro!: rawpsubstT)
qed

lemma rawpsubstT_Var_not[simp]:
  assumes "x \<in> var" "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
    and "x \<notin> snd ` (set txs)"
  shows "rawpsubstT (Var x) txs = Var x"
  using assms by (induct txs) auto

lemma psubstT_Var_not[simp]:
  assumes "x \<in> var" "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
    and "x \<notin> snd ` (set txs)"
  shows "psubstT (Var x) txs = Var x"
proof-
  define us where us: "us = getFrN (map snd txs) (Var x # map fst txs) [] (length txs)"
  have us_facts: "set us \<subseteq> var"
    "x \<notin> set us"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    using assms unfolding us
    using getFrN_FvarsT[of "map snd txs" "Var x # map fst txs" "[]" "Var x" "length txs"]
      getFrN_FvarsT[of "map snd txs" "Var x # map fst txs" "[]" _ "length txs"]
      getFrN_var[of "map snd txs" "Var x # map fst txs" "[]" "Var x" "length txs"]
      getFrN_length[of "map snd txs" "Var x # map fst txs" "[]" "length txs"]
    by (auto simp: set_eq_iff)
  have [simp]: "rawpsubstT (Var x) (zip (map Var us) (map snd txs)) = Var x"
    using assms us_facts
    by(intro rawpsubstT_Var_not) (force dest: set_zip_rightD set_zip_leftD)+
  have [simp]: "rawpsubstT (Var x) (zip (map fst txs) us) = Var x"
    using assms us_facts
    by(intro rawpsubstT_Var_not) (force dest: set_zip_rightD set_zip_leftD)+
  show ?thesis using assms us_facts unfolding psubstT_def
    by (auto simp: Let_def us[symmetric])
qed

lemma rawpsubstT_notIn[simp]:
  assumes "x \<in> var" "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm" "t \<in> trm"
    and "FvarsT t \<inter> snd ` (set txs) = {}"
  shows "rawpsubstT t txs = t"
  using assms by (induct txs) auto

lemma psubstT_notIn[simp]:
  assumes "x \<in> var" "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm" "t \<in> trm"
    and "FvarsT t \<inter> snd ` (set txs) = {}"
  shows "psubstT t txs = t"
proof-
  define us where us: "us = getFrN (map snd txs) (t # map fst txs) [] (length txs)"
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> FvarsT t = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    using assms unfolding us
    using getFrN_FvarsT[of "map snd txs" "t # map fst txs" "[]" _ "length txs"]
      getFrN_var[of "map snd txs" "t # map fst txs" "[]" t "length txs"]
      getFrN_length[of "map snd txs" "t # map fst txs" "[]" "length txs"]
    by (auto simp: set_eq_iff)
  have [simp]: "rawpsubstT t (zip (map Var us) (map snd txs)) = t"
    using assms us_facts
    by(intro rawpsubstT_notIn) (auto 0 3 dest: set_zip_rightD set_zip_leftD)
  have [simp]: "rawpsubstT t (zip (map fst txs) us) = t"
    using assms us_facts
    by(intro rawpsubstT_notIn) (auto 0 3 dest: set_zip_rightD set_zip_leftD)
  show ?thesis using assms us_facts unfolding psubstT_def
    by (auto simp: Let_def us[symmetric])
qed


subsection \<open>Parallel Formula Substitution\<close>

fun rawpsubst :: "'fmla \<Rightarrow> ('trm \<times> 'var) list \<Rightarrow> 'fmla" where
  "rawpsubst \<phi> [] = \<phi>"
| "rawpsubst \<phi> ((t1,x1) # txs) = rawpsubst (subst \<phi> t1 x1) txs"

lemma rawpsubst[simp]:
  assumes "\<phi> \<in> fmla" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
  shows "rawpsubst \<phi> txs \<in> fmla"
  using assms by (induct txs arbitrary: \<phi>) fastforce+

definition psubst :: "'fmla \<Rightarrow> ('trm \<times> 'var) list \<Rightarrow> 'fmla" where
  "psubst \<phi> txs =
    (let xs = map snd txs; ts = map fst txs; us = getFrN xs ts [\<phi>] (length xs) in
      rawpsubst (rawpsubst \<phi> (zip (map Var us) xs)) (zip ts us))"

text \<open>The psubst versions of the subst axioms.\<close>

lemma psubst[simp,intro]:
  assumes "\<phi> \<in> fmla" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
  shows "psubst \<phi> txs \<in> fmla"
proof-
  define us where us: "us = getFrN (map snd txs) (map fst txs) [\<phi>] (length txs)"
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> Fvars \<phi> = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    "distinct us"
    using assms unfolding us
    using getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>]" \<phi> "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[\<phi>]" "length txs"]
      getFrN_distinct[of "map snd txs" "map fst txs" "[\<phi>]" "length txs"]
    by (auto 8 0 simp: set_eq_iff image_iff Bex_def Ball_def)
  show ?thesis using assms us_facts unfolding psubst_def
    by (auto 0 3 simp: Let_def us[symmetric] dest: set_zip_rightD set_zip_leftD intro!: rawpsubst)
qed

lemma Fvars_rawpsubst_su:
  assumes "\<phi> \<in> fmla" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
  shows "Fvars (rawpsubst \<phi> txs) \<subseteq>
       (Fvars \<phi> - snd ` (set txs)) \<union> (\<Union> {FvarsT t | t x . (t,x) \<in> set txs})"
  using assms proof(induction txs arbitrary: \<phi>)
  case (Cons tx txs \<phi>)
  then obtain t x where tx: "tx = (t,x)" by force
  have t: "t \<in> trm" and x: "x \<in> var" using Cons.prems unfolding tx by auto
  define \<chi> where "\<chi> = subst \<phi> t x"
  have 0: "Fvars \<chi> =  Fvars \<phi> - {x} \<union> (if x \<in> Fvars \<phi> then FvarsT t else {})"
    using Cons.prems unfolding \<chi>_def by (auto simp: tx t)
  have \<chi>: "\<chi> \<in> fmla" unfolding \<chi>_def using Cons.prems t x by auto
  have "Fvars (rawpsubst \<chi> txs) \<subseteq>
       (Fvars \<chi> - snd ` (set txs)) \<union>
       (\<Union> {FvarsT t | t x . (t,x) \<in> set txs})"
     using Cons.prems \<chi> by (intro Cons.IH) auto
  also have "\<dots> \<subseteq> Fvars \<phi> - insert x (snd ` set txs) \<union> \<Union>{FvarsT ta |ta. \<exists>xa. ta = t \<and> xa = x \<or> (ta, xa) \<in> set txs}"
    (is "_ \<subseteq> ?R") by(auto simp: 0 tx Cons.prems)
  finally have 1: "Fvars (rawpsubst \<chi> txs) \<subseteq> ?R" .
  have 2: "Fvars \<chi> = Fvars \<phi> - {x} \<union> (if x \<in> Fvars \<phi> then FvarsT t else {})"
    using Cons.prems t x unfolding \<chi>_def using Fvars_subst by auto
  show ?case using 1 by (simp add: tx \<chi>_def[symmetric] 2)
qed auto

lemma in_Fvars_rawpsubst_imp:
  assumes "y \<in> Fvars (rawpsubst \<phi> txs)"
    and "\<phi> \<in> fmla" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
  shows "(y \<in> Fvars \<phi> - snd ` (set txs)) \<or>
     (y \<in> \<Union> { FvarsT t | t x . (t,x) \<in> set txs})"
  using Fvars_rawpsubst_su[OF assms(2-4)]
  using assms(1) by blast

lemma Fvars_rawpsubst:
  assumes "\<phi> \<in> fmla" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
    and "distinct (map snd txs)" and "\<forall> x \<in> snd ` (set txs). \<forall> t \<in> fst ` (set txs). x \<notin> FvarsT t"
  shows "Fvars (rawpsubst \<phi> txs) =
       (Fvars \<phi> - snd ` (set txs)) \<union>
       (\<Union> {if x \<in> Fvars \<phi> then FvarsT t else {} | t x . (t,x) \<in> set txs})"
  using assms proof(induction txs arbitrary: \<phi>)
  case (Cons a txs \<phi>)
  then obtain t x where a: "a = (t,x)" by force
  have t: "t \<in> trm" and x: "x \<in> var" using Cons.prems unfolding a by auto
  have x_txs: "\<And>ta xa. (ta, xa) \<in> set txs \<Longrightarrow> x \<noteq> xa" using \<open>distinct (map snd (a # txs))\<close>
   unfolding a by (auto simp: rev_image_eqI)
  have xt: "x \<notin> FvarsT t \<and> snd ` set txs \<inter> FvarsT t = {}" using Cons.prems unfolding a by auto
  hence 0: "Fvars \<phi> - {x} \<union> FvarsT t - snd ` set txs =
            Fvars \<phi> - insert x (snd ` set txs) \<union> FvarsT t"
    by auto
  define \<chi> where \<chi>_def: "\<chi> = subst \<phi> t x"
  have \<chi>: "\<chi> \<in> fmla" unfolding \<chi>_def using Cons.prems t x by auto
  have 1: "Fvars (rawpsubst \<chi> txs) =
       (Fvars \<chi> - snd ` (set txs)) \<union>
       (\<Union> {if x \<in> Fvars \<chi> then FvarsT t else {} | t x . (t,x) \<in> set txs})"
     using Cons.prems \<chi> by (intro Cons.IH) auto
  have 2: "Fvars \<chi> = Fvars \<phi> - {x} \<union> (if x \<in> Fvars \<phi> then FvarsT t else {})"
    using Cons.prems t x unfolding \<chi>_def using Fvars_subst by auto

  define f where "f \<equiv> \<lambda>ta xa. if xa \<in> Fvars \<phi> then FvarsT ta else {}"

  have 3: "\<Union> {f ta xa  |ta xa. (ta, xa) \<in> set ((t, x) # txs)} =
        f t x \<union> (\<Union> {f ta xa  |ta xa. (ta, xa) \<in> set txs})" by auto
  have 4: "snd ` set ((t, x) # txs) = {x} \<union> snd ` set txs" by auto
  have 5: "f t x \<inter> snd ` set txs = {}" unfolding f_def using xt by auto
  have 6: "\<Union> {if xa \<in> Fvars \<phi> - {x} \<union> f t x then FvarsT ta else {} | ta xa. (ta, xa) \<in> set txs}
     = (\<Union> {f ta xa | ta xa. (ta, xa) \<in> set txs})"
  unfolding f_def using xt x_txs by (fastforce split: if_splits)

  have "Fvars \<phi> - {x} \<union> f t x  - snd ` set txs \<union>
    \<Union> {if xa \<in> Fvars \<phi> - {x} \<union> f t x then FvarsT ta else {}
         | ta xa. (ta, xa) \<in> set txs} =
        Fvars \<phi> - snd ` set ((t, x) # txs) \<union>
    \<Union> {f ta xa  |ta xa. (ta, xa) \<in> set ((t, x) # txs)}"
  unfolding 3 4 6 unfolding Un_Diff2[OF 5] Un_assoc unfolding Diff_Diff_Un ..

  thus ?case unfolding a rawpsubst.simps 1 2 \<chi>_def[symmetric] f_def by simp
qed auto

lemma in_Fvars_rawpsubstD:
  assumes "y \<in> Fvars (rawpsubst \<phi> txs)"
    and "\<phi> \<in> fmla" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
    and "distinct (map snd txs)" and "\<forall> x \<in> snd ` (set txs). \<forall> t \<in> fst ` (set txs). x \<notin> FvarsT t"
  shows "(y \<in> Fvars \<phi> - snd ` (set txs)) \<or>
     (y \<in> \<Union> {if x \<in> Fvars \<phi> then FvarsT t else {} | t x . (t,x) \<in> set txs})"
  using Fvars_rawpsubst assms by auto

lemma Fvars_psubst:
  assumes "\<phi> \<in> fmla" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
    and "distinct (map snd txs)"
  shows "Fvars (psubst \<phi> txs) =
       (Fvars \<phi> - snd ` (set txs)) \<union>
       (\<Union> {if x \<in> Fvars \<phi> then FvarsT t else {} | t x . (t,x) \<in> set txs})"
proof-
  define us where us: "us = getFrN (map snd txs) (map fst txs) [\<phi>] (length txs)"
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> Fvars \<phi> = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    "distinct us"
    using assms unfolding us
    using getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[\<phi>]" "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[\<phi>]" "length txs"]
    by (auto 9 0 simp: set_eq_iff image_iff)
  define \<chi> where \<chi>_def: "\<chi> = rawpsubst \<phi> (zip (map Var us) (map snd txs))"
  have \<chi>: "\<chi> \<in> fmla" unfolding \<chi>_def using assms us_facts
    by (intro rawpsubst) (auto dest!: set_zip_D)
  have set_us: "set us = snd ` (set (zip (map fst txs) us))"
     using us_facts by (intro snd_set_zip[symmetric]) auto
  have set_txs: "snd ` set txs = snd ` (set (zip (map Var us) (map snd txs)))"
     using us_facts by (intro snd_set_zip_map_snd[symmetric]) auto
  have "\<And> t x. (t, x) \<in> set (zip (map Var us) (map snd txs)) \<Longrightarrow> \<exists> u. t = Var u"
    using us_facts set_zip_leftD by fastforce
  hence 00: "\<And> t x. (t, x) \<in> set (zip (map Var us) (map snd txs))
     \<longleftrightarrow>  (\<exists> u \<in> var. t = Var u \<and> (Var u, x) \<in> set (zip (map Var us) (map snd txs)))"
    using us_facts set_zip_leftD by fastforce
  have "Fvars \<chi> =
        Fvars \<phi> - snd ` set txs \<union>
        \<Union>{if x \<in> Fvars \<phi> then FvarsT t else {} |t x.
             (t, x) \<in> set (zip (map Var us) (map snd txs))}"
    unfolding \<chi>_def set_txs using assms us_facts
    apply(intro Fvars_rawpsubst)
    subgoal by auto
    subgoal by (auto dest!: set_zip_rightD)
    subgoal by (auto dest!: set_zip_leftD)
    subgoal by auto
    subgoal  by (auto 0 6 simp: set_txs[symmetric] set_eq_iff subset_eq image_iff in_set_zip
      dest: spec[where P="\<lambda>x. x \<in> set us \<longrightarrow> (\<forall>y \<in> set txs. x \<noteq> snd y)", THEN mp[OF _ nth_mem]]) .
  also have "\<dots> =
    Fvars \<phi> - snd ` set txs \<union>
    \<Union>{if x \<in> Fvars \<phi> then {u} else {} |u x. u \<in> var \<and> (Var u, x) \<in> set (zip (map Var us) (map snd txs))}"
    (is "\<dots> = ?R")
    using FvarsT_Var by (metis (no_types, hide_lams) 00)
  finally have 0: "Fvars \<chi> = ?R" .
  have 1: "Fvars (rawpsubst \<chi> (zip (map fst txs) us)) =
        (Fvars \<chi> - set us) \<union>
        (\<Union> {if u \<in> Fvars \<chi> then FvarsT t else {} | t u . (t,u) \<in> set (zip (map fst txs) us)})"
    unfolding set_us using us_facts assms \<chi>
    apply (intro Fvars_rawpsubst)
    subgoal by (auto dest: set_zip_rightD)
    subgoal by (auto dest: set_zip_rightD)
    subgoal by (auto dest!: set_zip_leftD)
    subgoal by (auto dest!: set_zip_leftD)
    subgoal by (metis IntI Union_iff empty_iff fst_set_zip_map_fst image_eqI set_us) .
  have 2: "Fvars \<chi> - set us = Fvars \<phi> - snd ` set txs"
    unfolding 0 using us_facts(1,2)
    by (fastforce dest!: set_zip_leftD split: if_splits)
  have 3:
    "(\<Union> {if u \<in> Fvars \<chi> then FvarsT t else {} | t u . (t,u) \<in> set (zip (map fst txs) us)}) =
   (\<Union> {if x \<in> Fvars \<phi> then FvarsT t else {} | t x . (t,x) \<in> set txs})"
  proof safe
    fix xx tt y
    assume xx: "xx \<in> (if y \<in> Fvars \<chi> then FvarsT tt else {})"
      and ty: "(tt, y) \<in> set (zip (map fst txs) us)"
    have ttin: "tt \<in> fst ` set txs" using ty using set_zip_leftD by fastforce
    have yin: "y \<in> set us" using ty by (meson set_zip_D)
    have yvar: "y \<in> var" using us_facts yin by auto
    have ynotin: "y \<notin> snd ` set txs" "y \<notin> Fvars \<phi>" using yin us_facts by auto
    show "xx \<in> \<Union>{if x \<in> Fvars \<phi> then FvarsT t else {} |t x. (t, x) \<in> set txs}"
    proof(cases "y \<in> Fvars \<chi>")
      case True note y = True
      hence xx: "xx \<in> FvarsT tt" using xx by simp
      obtain x where x\<phi>: "x \<in> Fvars \<phi>"
        and yx: "(Var y, x) \<in> set (zip (map Var us) (map snd txs))"
        using y ynotin unfolding 0 by auto (metis empty_iff insert_iff)
      have yx: "(y, x) \<in> set (zip us (map snd txs))"
      using yvar us_facts by (intro inj_on_set_zip_map[OF inj_on_Var yx]) auto
      have "(tt, x) \<in> set txs" apply(rule set_zip_map_fst_snd[OF yx ty])
        using  \<open>distinct (map snd txs)\<close> us_facts by auto
      thus ?thesis using xx x\<phi> by auto
    qed(insert xx, auto)
  next
    fix y tt xx
    assume y: "y \<in> (if xx \<in> Fvars \<phi> then FvarsT tt else {})"
      and tx: "(tt, xx) \<in> set txs"
    hence xxsnd: "xx \<in> snd ` set txs" by force
    obtain u where uin: "u \<in> set us" and uxx: "(u, xx) \<in> set (zip us (map snd txs))"
      by (metis xxsnd in_set_impl_in_set_zip2 length_map set_map set_zip_leftD us_facts(5))
    hence uvar: "u \<in> var" using us_facts by auto
    show "y \<in> \<Union>{if u \<in> Fvars \<chi> then FvarsT t else {} |t u. (t, u) \<in> set (zip (map fst txs) us)}"
    proof(cases "xx \<in> Fvars \<phi>")
      case True note xx = True
      hence y: "y \<in> FvarsT tt" using y by auto
      have "(Var u, xx) \<in> set (zip (map Var us) (map snd txs))"
      using us_facts by (intro set_zip_length_map[OF uxx]) auto
      hence u\<chi>: "u \<in> Fvars \<chi>" using uin xx uvar unfolding 0 by auto
      have ttu: "(tt, u) \<in> set (zip (map fst txs) us)"
      using assms us_facts by (intro set_zip_map_fst_snd2[OF uxx tx]) auto
      show ?thesis using u\<chi> ttu y by auto
    qed(insert y, auto)
  qed
  show ?thesis
  by (simp add: psubst_def Let_def us[symmetric] \<chi>_def[symmetric] 1 2 3)
qed

lemma in_Fvars_psubstD:
  assumes "y \<in> Fvars (psubst \<phi> txs)"
    and "\<phi> \<in> fmla" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
    and "distinct (map snd txs)"
  shows "y \<in> (Fvars \<phi> - snd ` (set txs)) \<union>
           (\<Union> {if x \<in> Fvars \<phi> then FvarsT t else {} | t x . (t,x) \<in> set txs})"
  using assms Fvars_psubst by auto

lemma subst2_fresh_switch:
  assumes "\<phi> \<in> fmla" "t \<in> trm" "s \<in> trm" "x \<in> var" "y \<in> var"
    and "x \<noteq> y" "x \<notin> FvarsT s" "y \<notin> FvarsT t"
  shows "subst (subst \<phi> s y) t x = subst (subst \<phi> t x) s y"   (is "?L = ?R")
  using assms by (simp add: subst_compose_diff[of \<phi> s t y x])

lemma rawpsubst2_fresh_switch:
  assumes "\<phi> \<in> fmla" "t \<in> trm" "s \<in> trm" "x \<in> var" "y \<in> var"
    and "x \<noteq> y" "x \<notin> FvarsT s" "y \<notin> FvarsT t"
  shows "rawpsubst \<phi> ([(s,y),(t,x)]) = rawpsubst \<phi> ([(t,x),(s,y)])"
  using assms by (simp add: subst2_fresh_switch)

lemma rawpsubst_compose:
  assumes "\<phi> \<in> fmla" and "snd ` (set txs1) \<subseteq> var" and "fst ` (set txs1) \<subseteq> trm"
    and "snd ` (set txs2) \<subseteq> var" and "fst ` (set txs2) \<subseteq> trm"
  shows "rawpsubst (rawpsubst \<phi> txs1) txs2 = rawpsubst \<phi> (txs1 @ txs2)"
  using assms by (induct txs1 arbitrary: txs2 \<phi>) auto

lemma rawpsubst_subst_fresh_switch:
  assumes "\<phi> \<in> fmla" "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
    and "\<forall> x \<in> snd ` (set txs). x \<notin> FvarsT s"
    and "\<forall> t \<in> fst ` (set txs). y \<notin> FvarsT t"
    and "distinct (map snd txs)"
    and "s \<in> trm" and "y \<in> var" "y \<notin> snd ` (set txs)"
  shows "rawpsubst (subst \<phi> s y) txs = rawpsubst \<phi> (txs @ [(s,y)])"
  using assms proof(induction txs arbitrary: \<phi> s y)
  case (Cons tx txs)
  obtain t x where tx[simp]: "tx = (t,x)" by force
  have x: "x \<in> var" and t: "t \<in> trm" using Cons unfolding tx by auto
  have "rawpsubst \<phi> ((s, y) # (t, x) # txs) = rawpsubst \<phi> ([(s, y),(t, x)] @ txs)" by simp
  also have "\<dots> = rawpsubst (rawpsubst \<phi> [(s, y),(t, x)]) txs"
    using Cons by auto
  also have "rawpsubst \<phi> [(s, y),(t, x)] = rawpsubst \<phi> [(t, x),(s, y)]"
    using Cons by (intro rawpsubst2_fresh_switch) auto
  also have "rawpsubst (rawpsubst \<phi> [(t, x),(s, y)]) txs = rawpsubst \<phi> ([(t, x),(s, y)] @ txs)"
    using Cons by auto
  also have "\<dots> = rawpsubst (subst \<phi> t x) (txs @ [(s,y)])" using Cons by auto
  also have "\<dots> = rawpsubst \<phi> (((t, x) # txs) @ [(s, y)])" by simp
  finally show ?case unfolding tx by auto
qed auto

lemma subst_rawpsubst_fresh_switch:
  assumes "\<phi> \<in> fmla" "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
    and "\<forall> x \<in> snd ` (set txs). x \<notin> FvarsT s"
    and "\<forall> t \<in> fst ` (set txs). y \<notin> FvarsT t"
    and "distinct (map snd txs)"
    and "s \<in> trm" and "y \<in> var" "y \<notin> snd ` (set txs)"
  shows "subst (rawpsubst \<phi> txs) s y = rawpsubst \<phi> ((s,y) # txs)"
  using assms proof(induction txs arbitrary: \<phi> s y)
  case (Cons tx txs)
  obtain t x where tx[simp]: "tx = (t,x)" by force
  have x: "x \<in> var" and t: "t \<in> trm" using Cons unfolding tx by auto
  have "subst (rawpsubst (subst \<phi> t x) txs) s y = rawpsubst (subst \<phi> t x) ((s,y) # txs)"
   using Cons.prems by (intro Cons.IH) auto
  also have "\<dots> = rawpsubst (rawpsubst \<phi> [(t,x)]) ((s,y) # txs)" by simp
  also have "\<dots> = rawpsubst \<phi> ([(t,x)] @ ((s,y) # txs))"
    using Cons.prems by auto
  also have "\<dots> = rawpsubst \<phi> ([(t,x),(s,y)] @ txs)" by simp
  also have "\<dots> = rawpsubst (rawpsubst \<phi> [(t,x),(s,y)]) txs"
    using Cons.prems by auto
  also have "rawpsubst \<phi> [(t,x),(s,y)] = rawpsubst \<phi> [(s,y),(t,x)]"
    using Cons.prems by (intro rawpsubst2_fresh_switch) auto
  also have "rawpsubst (rawpsubst \<phi> [(s,y),(t,x)]) txs = rawpsubst \<phi> ([(s,y),(t,x)] @ txs)"
    using Cons.prems by auto
  finally show ?case by simp
qed auto

lemma rawpsubst_compose_freshVar:
  assumes "\<phi> \<in> fmla" "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
    and "distinct (map snd txs)"
    and "\<And> i j. i < j \<Longrightarrow> j < length txs \<Longrightarrow> snd (txs!j) \<notin> FvarsT (fst (txs!i))"
    and us_facts: "set us \<subseteq> var"
    "set us \<inter> Fvars \<phi> = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    "distinct us"
  shows "rawpsubst (rawpsubst \<phi> (zip (map Var us) (map snd txs))) (zip (map fst txs) us) = rawpsubst \<phi> txs"
  using assms proof(induction txs arbitrary: us \<phi>)
  case (Cons tx txs uus \<phi>)
  obtain t x where tx[simp]: "tx = (t,x)" by force
  obtain u us where uus[simp]: "uus = u # us" using Cons by (cases uus) auto
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> Fvars \<phi> = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    "distinct us" and u_facts: "u \<in> var" "u \<notin> Fvars \<phi>"
    "u \<notin> \<Union> (FvarsT ` (fst ` (set txs)))"
    "u \<notin> snd ` (set txs)" "u \<notin> set us"
    using Cons by auto
  let ?uxs = "zip (map Var us) (map snd txs)"
  have 1: "rawpsubst (subst \<phi> (Var u) x) ?uxs = rawpsubst \<phi> (?uxs @ [(Var u,x)])"
    using u_facts Cons.prems
    by (intro rawpsubst_subst_fresh_switch) (auto simp: subsetD dest!: set_zip_D)
  let ?uuxs = "zip (map Var uus) (map snd (tx # txs))"
  let ?tus = "zip (map fst txs) us"  let ?ttxs = "zip (map fst (tx # txs)) uus"
  have 2: "u \<in> Fvars (rawpsubst \<phi> (zip (map Var us) (map snd txs))) \<Longrightarrow> False"
  using Cons.prems apply- apply(drule in_Fvars_rawpsubstD)
  subgoal by auto
  subgoal by (auto dest!: set_zip_D)
  subgoal by (auto dest!: set_zip_D)
  subgoal by auto
  subgoal premises prems using us_facts(1,4,5)
    by (auto 0 3 simp: in_set_zip subset_eq set_eq_iff image_iff
      dest: spec[where P="\<lambda>x. x \<in> set us \<longrightarrow> (\<forall>y \<in> set txs. x \<noteq> snd y)",
        THEN mp[OF _ nth_mem], THEN bspec[OF _ nth_mem]])
  subgoal
    by (auto simp: in_set_zip subset_eq split: if_splits) .

  have 3: "\<And> xx tt. xx \<in> FvarsT t \<Longrightarrow> (tt, xx) \<notin> set txs"
  using Cons.prems(4,5) tx unfolding set_conv_nth
  by simp (metis One_nat_def Suc_leI diff_Suc_1 fst_conv le_imp_less_Suc
            nth_Cons_0 snd_conv zero_less_Suc)

  have 00: "rawpsubst (rawpsubst \<phi> ?uuxs) ?ttxs = rawpsubst (subst (rawpsubst \<phi> (?uxs @ [(Var u, x)])) t u) ?tus"
    by (simp add: 1)

  have "rawpsubst \<phi> (?uxs @ [(Var u, x)]) = rawpsubst (rawpsubst \<phi> ?uxs) [(Var u, x)]"
  using Cons.prems by (intro rawpsubst_compose[symmetric]) (auto intro!: rawpsubst dest!: set_zip_D)
  also have "rawpsubst (rawpsubst \<phi> ?uxs) [(Var u, x)] = subst (rawpsubst \<phi> ?uxs) (Var u) x" by simp
  finally have "subst (rawpsubst \<phi> (?uxs @ [(Var u, x)])) t u =
                subst (subst (rawpsubst \<phi> ?uxs) (Var u) x) t u" by simp
  also have "\<dots> = subst (rawpsubst \<phi> ?uxs) t x"
    using Cons 2 by (intro subst_subst) (auto intro!: rawpsubst dest!: set_zip_D)
  also have "\<dots> = rawpsubst \<phi> ((t,x) # ?uxs)"
  using Cons.prems 3 apply(intro subst_rawpsubst_fresh_switch)
    subgoal by (auto dest!: set_zip_D)
    subgoal by (auto dest!: set_zip_D)
    subgoal by (auto dest!: set_zip_D)
    subgoal by (auto dest!: set_zip_D)
    subgoal by (fastforce dest!: set_zip_D)
    by (auto dest!: set_zip_D)
  also have "\<dots> =  rawpsubst \<phi> ([(t,x)] @ ?uxs)" by simp
  also have "\<dots> = rawpsubst (rawpsubst \<phi> [(t,x)]) ?uxs"
    using Cons.prems by (intro rawpsubst_compose[symmetric]) (auto dest!: set_zip_D)
  finally have "rawpsubst (subst (rawpsubst \<phi> (?uxs @ [(Var u, x)])) t u) ?tus =
                rawpsubst (rawpsubst (rawpsubst \<phi> [(t,x)]) ?uxs) ?tus" by auto
  hence "rawpsubst (rawpsubst \<phi> ?uuxs) ?ttxs = rawpsubst (rawpsubst (rawpsubst \<phi> [(t,x)]) ?uxs) ?tus"
    using 00 by auto
  also have "\<dots> = rawpsubst (rawpsubst \<phi> [(t,x)]) txs"
    using Cons.prems apply (intro Cons.IH rawpsubst)
    subgoal by (auto dest!: set_zip_D in_Fvars_substD)
    subgoal by (auto dest!: set_zip_D in_Fvars_substD)
    subgoal by (auto dest!: set_zip_D in_Fvars_substD)
    subgoal by (auto dest!: set_zip_D in_Fvars_substD)
    subgoal by (auto dest!: set_zip_D in_Fvars_substD)
    subgoal by (auto dest!: set_zip_D in_Fvars_substD)
    subgoal by (metis Suc_mono diff_Suc_1 length_Cons nat.simps(3) nth_Cons')
    by (auto dest!: set_zip_D in_Fvars_substD)
  also have "\<dots> = rawpsubst \<phi> ([(t,x)] @ txs)"
    using Cons.prems by (intro rawpsubst_compose) (auto dest!: set_zip_D)
  finally show ?case by simp
qed auto

lemma rawpsubst_compose_freshVar2_aux:
  assumes \<phi>[simp]: "\<phi> \<in> fmla"
    and ts: "set ts \<subseteq> trm"
    and xs: "set xs \<subseteq> var"  "distinct xs"
    and us_facts: "set us \<subseteq> var"  "distinct us"
    "set us \<inter> Fvars \<phi> = {}"
    "set us \<inter> \<Union> (FvarsT ` (set ts)) = {}"
    "set us \<inter> set xs = {}"
    and vs_facts: "set vs \<subseteq> var"  "distinct vs"
    "set vs \<inter> Fvars \<phi> = {}"
    "set vs \<inter> \<Union> (FvarsT ` (set ts)) = {}"
    "set vs \<inter> set xs = {}"
    and l: "length us = length xs" "length vs = length xs" "length ts = length xs"
    and (* Extra hypothesis, only to get induction through: *) d: "set us \<inter> set vs = {}"
  shows "rawpsubst (rawpsubst \<phi> (zip (map Var us) xs)) (zip ts us) =
       rawpsubst (rawpsubst \<phi> (zip (map Var vs) xs)) (zip ts vs)"
  using assms proof(induction xs arbitrary: \<phi> ts us vs)
  case (Cons x xs \<phi> tts uus vvs)
  obtain t ts u us v vs where tts[simp]: "tts = t # ts" and lts[simp]: "length ts = length xs"
    and uus[simp]: "uus = u # us" and lus[simp]: "length us = length xs"
    and vvs[simp]: "vvs = v # vs" and lvs[simp]: "length vs = length xs"
    using \<open>length uus = length (x # xs)\<close> \<open>length vvs = length (x # xs)\<close> \<open>length tts = length (x # xs)\<close>
    apply(cases tts)
    subgoal by auto
    subgoal apply(cases uus)
      subgoal by auto
      subgoal by (cases vvs) auto . .

  let ?\<phi>ux = "subst \<phi> (Var u) x"   let ?\<phi>vx = "subst \<phi> (Var v) x"

  have 0: "rawpsubst (rawpsubst ?\<phi>ux (zip (map Var us) xs)) (zip ts us) =
           rawpsubst (rawpsubst ?\<phi>ux (zip (map Var vs) xs)) (zip ts vs)"
    apply(rule Cons.IH) using Cons.prems by (auto intro!: rawpsubst dest!: set_zip_D)

  have 1: "rawpsubst ?\<phi>ux (zip (map Var vs) xs) =
           subst (rawpsubst \<phi> (zip (map Var vs) xs)) (Var u) x"
    using Cons.prems
    by (intro subst_rawpsubst_fresh_switch[simplified,symmetric])
       (force intro!: rawpsubst dest!: set_zip_D simp: subset_eq)+

  have 11: "rawpsubst ?\<phi>vx (zip (map Var vs) xs) =
           subst (rawpsubst \<phi> (zip (map Var vs) xs)) (Var v) x"
    using Cons.prems
    by (intro subst_rawpsubst_fresh_switch[simplified,symmetric])
       (auto intro!: rawpsubst dest!: set_zip_D simp: subset_eq)

  have "subst (subst (rawpsubst \<phi> (zip (map Var vs) xs)) (Var u) x) t u =
        subst (rawpsubst \<phi> (zip (map Var vs) xs)) t x"
  using Cons.prems
  by (intro subst_subst) (force intro!: rawpsubst dest!: set_zip_D in_Fvars_rawpsubst_imp simp: Fvars_rawpsubst)+
  also have "\<dots> = subst (subst (rawpsubst \<phi> (zip (map Var vs) xs)) (Var v) x) t v"
  using Cons.prems
  by (intro subst_subst[symmetric])
     (force intro!: rawpsubst dest!: set_zip_D in_Fvars_rawpsubst_imp simp: Fvars_rawpsubst)+

  finally have
    2: "subst (subst (rawpsubst \<phi> (zip (map Var vs) xs)) (Var u) x) t u =
      subst (subst (rawpsubst \<phi> (zip (map Var vs) xs)) (Var v) x) t v"  .

  have "rawpsubst (subst (rawpsubst ?\<phi>ux (zip (map Var us) xs)) t u) (zip ts us) =
        subst (rawpsubst (rawpsubst ?\<phi>ux (zip (map Var us) xs)) (zip ts us)) t u"
    using Cons.prems
    by (intro subst_rawpsubst_fresh_switch[simplified,symmetric]) (auto intro!: rawpsubst dest!: set_zip_D)
  also have "\<dots> = subst (rawpsubst (rawpsubst ?\<phi>ux (zip (map Var vs) xs)) (zip ts vs)) t u"
    unfolding 0 ..
  also have "\<dots> = rawpsubst (subst (rawpsubst ?\<phi>ux (zip (map Var vs) xs)) t u) (zip ts vs)"
    using Cons.prems
    by (intro subst_rawpsubst_fresh_switch[simplified]) (auto intro!: rawpsubst dest!: set_zip_D)
  also have "\<dots> = rawpsubst (subst (subst (rawpsubst \<phi> (zip (map Var vs) xs)) (Var u) x) t u) (zip ts vs)"
    unfolding 1 ..
  also have "\<dots> = rawpsubst (subst (subst (rawpsubst \<phi> (zip (map Var vs) xs)) (Var v) x) t v) (zip ts vs)"
    unfolding 2 ..
  also have "\<dots> = rawpsubst (subst (rawpsubst ?\<phi>vx (zip (map Var vs) xs)) t v) (zip ts vs)"
    unfolding 11 ..
  finally have "rawpsubst (subst (rawpsubst ?\<phi>ux (zip (map Var us) xs)) t u) (zip ts us) =
        rawpsubst (subst (rawpsubst ?\<phi>vx (zip (map Var vs) xs)) t v) (zip ts vs)" .
  thus ?case by simp
qed auto

text \<open>... now getting rid of the disjointness hypothesis:\<close>

lemma rawpsubst_compose_freshVar2:
  assumes \<phi>[simp]: "\<phi> \<in> fmla"
    and ts: "set ts \<subseteq> trm"
    and xs: "set xs \<subseteq> var"  "distinct xs"
    and us_facts: "set us \<subseteq> var"  "distinct us"
    "set us \<inter> Fvars \<phi> = {}"
    "set us \<inter> \<Union> (FvarsT ` (set ts)) = {}"
    "set us \<inter> set xs = {}"
    and vs_facts: "set vs \<subseteq> var"  "distinct vs"
    "set vs \<inter> Fvars \<phi> = {}"
    "set vs \<inter> \<Union> (FvarsT ` (set ts)) = {}"
    "set vs \<inter> set xs = {}"
    and l: "length us = length xs" "length vs = length xs" "length ts = length xs"
  shows "rawpsubst (rawpsubst \<phi> (zip (map Var us) xs)) (zip ts us) =
       rawpsubst (rawpsubst \<phi> (zip (map Var vs) xs)) (zip ts vs)"  (is "?L = ?R")
proof-
  define ws where "ws = getFrN (xs @ us @ vs) ts [\<phi>] (length xs)"
  note fv = getFrN_Fvars[of "xs @ us @ vs" "ts" "[\<phi>]" _ "length xs"]
  and fvt = getFrN_FvarsT[of "xs @ us @ vs" "ts" "[\<phi>]" _ "length xs"]
  and var = getFrN_var[of "xs @ us @ vs" "ts" "[\<phi>]" _ "length xs"]
  and l = getFrN_length[of "xs @ us @ vs" "ts" "[\<phi>]" "length xs"]
  have ws_facts: "set ws \<subseteq> var"  "distinct ws"
    "set ws \<inter> Fvars \<phi> = {}"
    "set ws \<inter> \<Union> (FvarsT ` (set ts)) = {}"
    "set ws \<inter> set xs = {}" "set ws \<inter> set us = {}" "set ws \<inter> set vs = {}"
    "length ws = length xs" using assms unfolding ws_def
    apply -
    subgoal by auto
    subgoal by auto
    subgoal using fv by auto
    subgoal using fvt IntI empty_iff by fastforce
    subgoal using var IntI empty_iff by fastforce
    subgoal using var IntI empty_iff by fastforce
    subgoal using var IntI empty_iff by fastforce
    subgoal using l by auto  .
  have "?L = rawpsubst (rawpsubst \<phi> (zip (map Var ws) xs)) (zip ts ws)"
    apply(rule rawpsubst_compose_freshVar2_aux) using assms ws_facts by auto
  also have "\<dots> = ?R"
    apply(rule rawpsubst_compose_freshVar2_aux) using assms ws_facts by auto
  finally show ?thesis .
qed

lemma psubst_subst_fresh_switch:
  assumes "\<phi> \<in> fmla" "snd ` set txs \<subseteq> var" "fst ` set txs \<subseteq> trm"
    and "\<forall>x\<in>snd ` set txs. x \<notin> FvarsT s" "\<forall>t\<in>fst ` set txs. y \<notin> FvarsT t"
    and "distinct (map snd txs)"
    and "s \<in> trm" "y \<in> var" "y \<notin> snd ` set txs"
  shows "psubst (subst \<phi> s y) txs = subst (psubst \<phi> txs) s y"
proof-
  define us where us: "us = getFrN (map snd txs) (map fst txs) [\<phi>] (length txs)"
  note fvt = getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
  and fv = getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
  and var = getFrN_var[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
  and l = getFrN_length[of "map snd txs" "map fst txs" "[\<phi>]" "length txs"]

  have us_facts: "set us \<subseteq> var"
    "set us \<inter> Fvars \<phi> = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    "distinct us"
  using assms unfolding us apply -
  subgoal by auto
  subgoal using fv by (cases txs, auto)
  subgoal using fvt by (cases txs, auto)
  subgoal using var by (cases txs, auto)
  subgoal using l by auto
  subgoal by auto .

  define vs where vs: "vs = getFrN (map snd txs) (map fst txs) [subst \<phi> s y] (length txs)"
  note fvt = getFrN_FvarsT[of "map snd txs" "map fst txs" "[subst \<phi> s y]" _ "length txs"]
  and fv = getFrN_Fvars[of "map snd txs" "map fst txs" "[subst \<phi> s y]" _ "length txs"]
  and var = getFrN_var[of "map snd txs" "map fst txs" "[subst \<phi> s y]" _ "length txs"]
  and l = getFrN_length[of "map snd txs" "map fst txs" "[subst \<phi> s y]" "length txs"]

  have vs_facts: "set vs \<subseteq> var"
    "set vs \<inter> Fvars (subst \<phi> s y) = {}"
    "set vs \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set vs \<inter> snd ` (set txs) = {}"
    "length vs = length txs"
    "distinct vs"
  using assms unfolding vs apply -
  subgoal by auto
  subgoal using fv by (cases txs, auto)
  subgoal using fvt by (cases txs, auto)
  subgoal using var by (cases txs, auto)
  subgoal using l by auto
  subgoal by auto .

  define ws where ws: "ws = getFrN (y # map snd txs) (s # map fst txs) [\<phi>] (length txs)"
  note fvt = getFrN_FvarsT[of "y # map snd txs" "s # map fst txs" "[\<phi>]" _ "length txs"]
  and fv = getFrN_Fvars[of "y # map snd txs" "s # map fst txs" "[\<phi>]" _ "length txs"]
  and var = getFrN_var[of "y # map snd txs" "s # map fst txs" "[\<phi>]" _ "length txs"]
  and l = getFrN_length[of "y # map snd txs" "s # map fst txs" "[\<phi>]" "length txs"]

  have ws_facts: "set ws \<subseteq> var"
    "set ws \<inter> Fvars \<phi> = {}" "y \<notin> set ws" "set ws \<inter> FvarsT s = {}"
    "set ws \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set ws \<inter> snd ` (set txs) = {}"
    "length ws = length txs"
    "distinct ws"
  using assms unfolding ws apply -
  subgoal by auto
  subgoal using fv by (cases txs, auto)
  subgoal using var by (cases txs, auto)
  subgoal using fvt  by (cases txs, auto)
  subgoal using fvt by (cases txs, auto)
  subgoal using var by (cases txs, auto)
  subgoal using l by (cases txs, auto)
  by auto

  let ?vxs = "zip (map Var vs) (map snd txs)"
  let ?tvs = "(zip (map fst txs) vs)"
  let ?uxs = "zip (map Var us) (map snd txs)"
  let ?tus = "(zip (map fst txs) us)"
  let ?wxs = "zip (map Var ws) (map snd txs)"
  let ?tws = "(zip (map fst txs) ws)"

  have 0: "rawpsubst (subst \<phi> s y) ?wxs = subst (rawpsubst \<phi> ?wxs) s y"
  apply(subst rawpsubst_compose[of \<phi> ?wxs  "[(s,y)]",simplified])
  using assms ws_facts apply -
  subgoal by auto
  subgoal by (auto dest!: set_zip_D)
  subgoal by (auto dest!: set_zip_D)
  subgoal by auto
  subgoal by auto
  subgoal apply(subst rawpsubst_subst_fresh_switch)
    by (auto dest!: set_zip_D simp: subset_eq rawpsubst_subst_fresh_switch) .

  have 1: "rawpsubst (rawpsubst \<phi> ?wxs) ?tws = rawpsubst (rawpsubst \<phi> ?uxs) ?tus"
    using assms ws_facts us_facts by (intro rawpsubst_compose_freshVar2) (auto simp: subset_eq)

  have "rawpsubst (rawpsubst (subst \<phi> s y) ?vxs) ?tvs =
        rawpsubst (rawpsubst (subst \<phi> s y) ?wxs) ?tws"
    using assms ws_facts vs_facts
    by (intro rawpsubst_compose_freshVar2)  (auto simp: subset_eq)
  also have "\<dots> = rawpsubst (subst (rawpsubst \<phi> ?wxs) s y) ?tws" unfolding 0 ..
  also have "\<dots> = subst (rawpsubst (rawpsubst \<phi> ?wxs) ?tws) s y"
  apply(subst rawpsubst_compose[of "rawpsubst \<phi> ?wxs" ?tws  "[(s,y)]",simplified])
  using assms ws_facts apply -
  subgoal by (auto dest!: set_zip_D simp: subset_eq intro!: rawpsubst)
  subgoal by (auto dest!: set_zip_D)
  subgoal by (auto dest!: set_zip_D)
  subgoal by auto
  subgoal by auto
  subgoal by (subst rawpsubst_subst_fresh_switch)
    (auto dest!: set_zip_D simp: subset_eq rawpsubst_subst_fresh_switch
          intro!: rawpsubst) .
  also have "\<dots> = subst (rawpsubst (rawpsubst \<phi> ?uxs) ?tus) s y" unfolding 1 ..
  finally show  ?thesis unfolding psubst_def by (simp add: Let_def vs[symmetric] us[symmetric])
qed

text \<open>For many cases, the simpler rawpsubst can replace psubst:\<close>

lemma psubst_eq_rawpsubst:
  assumes "\<phi> \<in> fmla" "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
    and "distinct (map snd txs)"
    (* ... namely, when the substituted variables do not belong to trms substituted for previous variables: *)
    and "\<And> i j. i < j \<Longrightarrow> j < length txs \<Longrightarrow> snd (txs!j) \<notin> FvarsT (fst (txs!i))"
  shows "psubst \<phi> txs = rawpsubst \<phi> txs"
proof-
  define us where us: "us = getFrN (map snd txs) (map fst txs) [\<phi>] (length txs)"
  note fvt = getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
  and fv = getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
  and var = getFrN_var[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
  and l = getFrN_length[of "map snd txs" "map fst txs" "[\<phi>]" "length txs"]
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> Fvars \<phi> = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    "distinct us"
    using assms unfolding us
    apply -
    subgoal by auto
    subgoal using fv by auto
    subgoal using fvt by force
    subgoal using var by (force simp: image_iff)
    using l by auto
  show ?thesis
    using rawpsubst_compose_freshVar assms us_facts
    by (simp add: psubst_def Let_def us[symmetric])
qed

text \<open>Some particular cases:\<close>

lemma psubst_eq_subst:
  assumes "\<phi> \<in> fmla" "x \<in> var" and "t \<in> trm"
  shows "psubst \<phi> [(t,x)] = subst \<phi> t x"
proof-
  have "psubst \<phi> [(t,x)] = rawpsubst \<phi> [(t,x)]" apply(rule psubst_eq_rawpsubst)
    using assms by auto
  thus ?thesis by auto
qed

lemma psubst_eq_rawpsubst2:
  assumes "\<phi> \<in> fmla" "x1 \<in> var" "x2 \<in> var" "t1 \<in> trm" "t2 \<in> trm"
    and "x1 \<noteq> x2" "x2 \<notin> FvarsT t1"
  shows "psubst \<phi> [(t1,x1),(t2,x2)] = rawpsubst \<phi> [(t1,x1),(t2,x2)]"
  apply(rule psubst_eq_rawpsubst)
  using assms using less_SucE by force+

lemma psubst_eq_rawpsubst3:
  assumes "\<phi> \<in> fmla" "x1 \<in> var" "x2 \<in> var" "x3 \<in> var" "t1 \<in> trm" "t2 \<in> trm" "t3 \<in> trm"
    and "x1 \<noteq> x2" "x1 \<noteq> x3" "x2 \<noteq> x3"
    "x2 \<notin> FvarsT t1" "x3 \<notin> FvarsT t1" "x3 \<notin> FvarsT t2"
  shows "psubst \<phi> [(t1,x1),(t2,x2),(t3,x3)] = rawpsubst \<phi> [(t1,x1),(t2,x2),(t3,x3)]"
  using assms using less_SucE apply(intro psubst_eq_rawpsubst)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for i j
    apply(cases j)
    subgoal by auto
    subgoal by (simp add: nth_Cons') . .

lemma psubst_eq_rawpsubst4:
  assumes "\<phi> \<in> fmla" "x1 \<in> var" "x2 \<in> var" "x3 \<in> var" "x4 \<in> var"
    "t1 \<in> trm" "t2 \<in> trm" "t3 \<in> trm" "t4 \<in> trm"
    and "x1 \<noteq> x2" "x1 \<noteq> x3" "x2 \<noteq> x3" "x1 \<noteq> x4" "x2 \<noteq> x4" "x3 \<noteq> x4"
    "x2 \<notin> FvarsT t1" "x3 \<notin> FvarsT t1" "x3 \<notin> FvarsT t2" "x4 \<notin> FvarsT t1" "x4 \<notin> FvarsT t2" "x4 \<notin> FvarsT t3"
  shows "psubst \<phi> [(t1,x1),(t2,x2),(t3,x3),(t4,x4)] = rawpsubst \<phi> [(t1,x1),(t2,x2),(t3,x3),(t4,x4)]"
  using assms using less_SucE apply(intro psubst_eq_rawpsubst)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal for i j
    apply(cases j)
    subgoal by auto
    subgoal by (simp add: nth_Cons') . .

lemma rawpsubst_same_Var[simp]:
  assumes "\<phi> \<in> fmla" "set xs \<subseteq> var"
  shows "rawpsubst \<phi> (map (\<lambda>x. (Var x,x)) xs) = \<phi>"
  using assms by (induct xs) auto

lemma psubst_same_Var[simp]:
  assumes "\<phi> \<in> fmla" "set xs \<subseteq> var" and "distinct xs"
  shows "psubst \<phi> (map (\<lambda>x. (Var x,x)) xs) = \<phi>"
proof-
  have "psubst \<phi> (map (\<lambda>x. (Var x,x)) xs) = rawpsubst \<phi> (map (\<lambda>x. (Var x,x)) xs)"
  using assms by (intro psubst_eq_rawpsubst) (auto simp: nth_eq_iff_index_eq subsetD)
  thus ?thesis using assms by auto
qed

lemma rawpsubst_notIn[simp]:
  assumes "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm" "\<phi> \<in> fmla"
    and "Fvars \<phi> \<inter> snd ` (set txs) = {}"
  shows "rawpsubst \<phi> txs = \<phi>"
  using assms by (induct txs) auto

lemma psubst_notIn[simp]:
  assumes "x \<in> var" "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm" "\<phi> \<in> fmla"
    and  "Fvars \<phi> \<inter> snd ` (set txs) = {}"
  shows "psubst \<phi> txs = \<phi>"
proof-
  define us where us: "us = getFrN (map snd txs) (map fst txs) [\<phi>] (length txs)"
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> Fvars \<phi> = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[\<phi>]" "length txs"]
    using assms unfolding us apply -
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (fastforce simp: image_iff)
    subgoal by auto .
    (* *)
  have [simp]: "rawpsubst \<phi> (zip (map Var us) (map snd txs)) = \<phi>"
  using assms us_facts apply(intro rawpsubst_notIn)
  subgoal by (auto dest!: set_zip_rightD)
  subgoal by (auto dest!: set_zip_leftD)
  subgoal by auto
  subgoal by (auto dest!: set_zip_rightD) .
  have [simp]: "rawpsubst \<phi> (zip (map fst txs) us) = \<phi>"
    using assms us_facts apply(intro rawpsubst_notIn)
  subgoal by (auto dest!: set_zip_rightD)
  subgoal by (auto dest!: set_zip_leftD)
  subgoal by auto
  subgoal by (auto dest!: set_zip_rightD) .
  show ?thesis using assms us_facts unfolding psubst_def
    by(auto simp: Let_def us[symmetric])
qed

end \<comment> \<open>context @{locale Generic_Syntax}\<close>


section \<open>Adding Numerals to the Generic Syntax\<close>

locale Syntax_with_Numerals =
  Generic_Syntax var trm fmla Var FvarsT substT Fvars subst
  for var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
    and Var FvarsT substT Fvars subst
    +
  fixes
    \<comment> \<open>Abstract notion of numerals, as a subset of the ground terms:\<close>
    num :: "'trm set"
  assumes
    numNE: "num \<noteq> {}"
    and
    num: "num \<subseteq> trm"
    and
    FvarsT_num[simp, intro!]: "\<And>n. n \<in> num \<Longrightarrow> FvarsT n = {}"
begin

lemma substT_num1[simp]: "t \<in> trm \<Longrightarrow> y \<in> var \<Longrightarrow> n \<in> num \<Longrightarrow> substT n t y = n"
  using num by auto

lemma in_num[simp]: "n \<in> num \<Longrightarrow> n \<in> trm" using num by auto

lemma subst_comp_num:
  assumes "\<phi> \<in> fmla" "x \<in> var" "y \<in> var" "n \<in> num"
  shows "x \<noteq> y \<Longrightarrow> subst (subst \<phi> (Var x) y) n x = subst (subst \<phi> n x) n y"
  using assms by (simp add: subst_comp)

lemma rawpsubstT_num:
  assumes "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm" "n \<in> num"
  shows "rawpsubstT n txs = n"
  using assms by (induct txs) auto

lemma psubstT_num[simp]:
  assumes "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm" "n \<in> num"
  shows "psubstT n txs = n"
proof-
  define us where us: "us = getFrN (map snd txs) (n # map fst txs) [] (length txs)"
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> FvarsT n = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    using assms unfolding us
    using getFrN_Fvars[of "map snd txs" "n # map fst txs" "[]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "n # map fst txs" "[]" _ "length txs"]
      getFrN_var[of "map snd txs" "n # map fst txs" "[]" _ "length txs"]
      getFrN_length[of "map snd txs" "n # map fst txs" "[]" "length txs"]
    by (auto 7 0 simp: set_eq_iff image_iff)
  let ?t = "rawpsubstT n (zip (map Var us) (map snd txs))"
  have t: "?t = n"
  using assms us_facts apply(intro rawpsubstT_num)
  subgoal by (auto dest!: set_zip_rightD)
  subgoal by (auto dest!: set_zip_leftD)
  subgoal by auto .
  have "rawpsubstT ?t (zip (map fst txs) us) = n"
  unfolding t using assms us_facts apply(intro rawpsubstT_num)
  subgoal by (auto dest!: set_zip_rightD)
  subgoal by (auto dest!: set_zip_leftD)
  subgoal by auto .
  thus ?thesis unfolding psubstT_def by(simp add: Let_def us[symmetric])
qed

end \<comment> \<open>context @{locale Syntax_with_Numerals}\<close>


section \<open>Adding Connectives and Quantifiers\<close>

locale Syntax_with_Connectives =
  Generic_Syntax var trm fmla Var FvarsT substT Fvars subst
  for
    var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
    and Var FvarsT substT Fvars subst
    +
  fixes
    \<comment> \<open>Logical connectives\<close>
    eql :: "'trm \<Rightarrow> 'trm \<Rightarrow> 'fmla"
    and
    cnj :: "'fmla \<Rightarrow> 'fmla \<Rightarrow> 'fmla"
    and
    imp :: "'fmla \<Rightarrow> 'fmla \<Rightarrow> 'fmla"
    and
    all :: "'var \<Rightarrow> 'fmla \<Rightarrow> 'fmla"
    and
    exi :: "'var \<Rightarrow> 'fmla \<Rightarrow> 'fmla"
  assumes
    eql[simp,intro]: "\<And> t1 t2. t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> eql t1 t2 \<in> fmla"
    and
    cnj[simp,intro]: "\<And> \<phi>1 \<phi>2. \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> cnj \<phi>1 \<phi>2 \<in> fmla"
    and
    imp[simp,intro]: "\<And> \<phi>1 \<phi>2. \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> imp \<phi>1 \<phi>2 \<in> fmla"
    and
    all[simp,intro]: "\<And> x \<phi>. x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> all x \<phi> \<in> fmla"
    and
    exi[simp,intro]: "\<And> x \<phi>. x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> exi x \<phi> \<in> fmla"
    and
    Fvars_eql[simp]:
    "\<And> t1 t2. t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> Fvars (eql t1 t2) = FvarsT t1 \<union> FvarsT t2"
    and
    Fvars_cnj[simp]:
    "\<And> \<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> Fvars (cnj \<phi> \<chi>) = Fvars \<phi> \<union> Fvars \<chi>"
    and
    Fvars_imp[simp]:
    "\<And> \<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> Fvars (imp \<phi> \<chi>) = Fvars \<phi> \<union> Fvars \<chi>"
    and
    Fvars_all[simp]:
    "\<And> x \<phi>. x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars (all x \<phi>) = Fvars \<phi> - {x}"
    and
    Fvars_exi[simp]:
    "\<And> x \<phi>. x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars (exi x \<phi>) = Fvars \<phi> - {x}"
    and
    \<comment> \<open>Assumed properties of substitution\<close>
    subst_cnj[simp]:
    "\<And> x \<phi> \<chi> t. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
      subst (cnj \<phi> \<chi>) t x = cnj (subst \<phi> t x) (subst \<chi> t x)"
    and
    subst_imp[simp]:
    "\<And> x \<phi> \<chi> t. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
      subst (imp \<phi> \<chi>) t x = imp (subst \<phi> t x) (subst \<chi> t x)"
    and
    subst_all[simp]:
    "\<And> x y \<phi> t. \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow>
      x \<noteq> y \<Longrightarrow> x \<notin> FvarsT t \<Longrightarrow> subst (all x \<phi>) t y = all x (subst \<phi> t y)"
    and
    subst_exi[simp]:
    "\<And> x y \<phi> t. \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow>
      x \<noteq> y \<Longrightarrow> x \<notin> FvarsT t \<Longrightarrow> subst (exi x \<phi>) t y = exi x (subst \<phi> t y)"
    and
    subst_eql[simp]:
    "\<And> t1 t2 t x. t \<in> trm \<Longrightarrow> t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
      subst (eql t1 t2) t x = eql (substT t1 t x) (substT t2 t x)"
begin

(*
(* "is the unique": isTU t x \<phi> is the formula "t is the unique x such that phi(x)"
 *)
definition isTU :: "'trm \<Rightarrow> 'var \<Rightarrow> 'fmla  \<Rightarrow> 'fmla" where
"isTU t x \<phi> \<equiv>
 cnj (subst \<phi> t x)
     (all x (imp \<phi> (subst \<phi> t x)))"

(* TODO: properties: works well when x is not free in t,
in particular, when t is num n *)
*)

text \<open>Formula equivalence, $\longleftrightarrow$, a derived connective\<close>

definition eqv :: "'fmla \<Rightarrow> 'fmla \<Rightarrow> 'fmla" where
  "eqv \<phi> \<chi> = cnj (imp \<phi> \<chi>) (imp \<chi> \<phi>)"

lemma
  eqv[simp]: "\<And>\<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> eqv \<phi> \<chi> \<in> fmla"
  and
  Fvars_eqv[simp]: "\<And>\<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow>
  Fvars (eqv \<phi> \<chi>)  = Fvars \<phi> \<union> Fvars \<chi>"
  and
  subst_eqv[simp]:
  "\<And>\<phi> \<chi> t x. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
  subst (eqv \<phi> \<chi>) t x = eqv (subst \<phi> t x) (subst \<chi> t x)"
  unfolding eqv_def by auto

lemma subst_all_idle[simp]:
assumes [simp]: "x \<in> var" "\<phi> \<in> fmla" "t \<in> trm"
shows "subst (all x \<phi>) t x = all x \<phi>"
by (intro subst_notIn) auto

lemma subst_exi_idle[simp]:
assumes [simp]: "x \<in> var" "\<phi> \<in> fmla" "t \<in> trm"
shows "subst (exi x \<phi>) t x = exi x \<phi>"
by (rule subst_notIn) auto


text \<open>Parallel substitution versus connectives and quantifiers.\<close>

lemma rawpsubst_cnj:
  assumes "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla"
    and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
  shows "rawpsubst (cnj \<phi>1 \<phi>2) txs = cnj (rawpsubst \<phi>1 txs) (rawpsubst \<phi>2 txs)"
  using assms by (induct txs arbitrary: \<phi>1 \<phi>2) auto

lemma psubst_cnj[simp]:
  assumes "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla"
    and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
    and "distinct (map snd txs)"
  shows "psubst (cnj \<phi>1 \<phi>2) txs = cnj (psubst \<phi>1 txs) (psubst \<phi>2 txs)"
proof-
  define us where us: "us = getFrN (map snd txs) (map fst txs) [cnj \<phi>1 \<phi>2] (length txs)"
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> Fvars \<phi>1 = {}"
    "set us \<inter> Fvars \<phi>2 = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    "distinct us"
    using assms unfolding us
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[cnj \<phi>1 \<phi>2]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[cnj \<phi>1 \<phi>2]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[cnj \<phi>1 \<phi>2]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[cnj \<phi>1 \<phi>2]" "length txs"]
    apply -
    subgoal by auto
    subgoal by fastforce
    subgoal by fastforce
    subgoal by fastforce
    subgoal by (fastforce simp: image_iff)
    subgoal by auto
    subgoal by auto .
  define vs1 where vs1: "vs1 = getFrN (map snd txs) (map fst txs) [\<phi>1] (length txs)"
  have vs1_facts: "set vs1  \<subseteq> var"
    "set vs1 \<inter> Fvars \<phi>1 = {}"
    "set vs1 \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set vs1 \<inter> snd ` (set txs) = {}"
    "length vs1 = length txs"
    "distinct vs1"
    using assms unfolding vs1
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>1]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>1]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[\<phi>1]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[\<phi>1]" "length txs"]
    apply -
    subgoal by auto
    subgoal by auto
    subgoal by fastforce
    subgoal by force
    subgoal by auto
    subgoal by auto .

  define vs2 where vs2: "vs2 = getFrN (map snd txs) (map fst txs) [\<phi>2] (length txs)"
  have vs2_facts: "set vs2  \<subseteq> var"
    "set vs2 \<inter> Fvars \<phi>2 = {}"
    "set vs2 \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set vs2 \<inter> snd ` (set txs) = {}"
    "length vs2 = length txs"
    "distinct vs2"
    using assms unfolding vs2
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>2]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>2]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[\<phi>2]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[\<phi>2]" "length txs"]
    apply -
    subgoal by auto
    subgoal by auto
    subgoal by fastforce
    subgoal by force
    subgoal by auto
    subgoal by auto .

  let ?tus = "zip (map fst txs) us"
  let ?uxs = "zip (map Var us) (map snd txs)"
  let ?tvs1 = "zip (map fst txs) vs1"
  let ?vxs1 = "zip (map Var vs1) (map snd txs)"
  let ?tvs2 = "zip (map fst txs) vs2"
  let ?vxs2 = "zip (map Var vs2) (map snd txs)"

  let ?c = "rawpsubst (cnj \<phi>1 \<phi>2) ?uxs"
  have c: "?c = cnj (rawpsubst \<phi>1 ?uxs) (rawpsubst \<phi>2 ?uxs)"
    using assms us_facts
    by (intro rawpsubst_cnj) (auto intro!: rawpsubstT dest!: set_zip_D)
  have 0: "rawpsubst ?c ?tus =
    cnj (rawpsubst (rawpsubst \<phi>1 ?uxs) ?tus) (rawpsubst (rawpsubst \<phi>2 ?uxs) ?tus)"
    unfolding c using assms us_facts
    by (intro rawpsubst_cnj) (auto dest!: set_zip_D intro!: rawpsubst)

  have 1: "rawpsubst (rawpsubst \<phi>1 ?uxs) ?tus = rawpsubst (rawpsubst \<phi>1 ?vxs1) ?tvs1"
    using assms vs1_facts us_facts
    by (intro rawpsubst_compose_freshVar2) (auto intro!: rawpsubst)
  have 2: "rawpsubst (rawpsubst \<phi>2 ?uxs) ?tus = rawpsubst (rawpsubst \<phi>2 ?vxs2) ?tvs2"
    using assms vs2_facts us_facts
    by (intro rawpsubst_compose_freshVar2)(auto intro!: rawpsubst)
  show ?thesis unfolding psubst_def by (simp add: Let_def us[symmetric] vs1[symmetric] vs2[symmetric] 0 1 2)
qed

lemma rawpsubst_imp:
  assumes "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla"
    and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
  shows "rawpsubst (imp \<phi>1 \<phi>2) txs = imp (rawpsubst \<phi>1 txs) (rawpsubst \<phi>2 txs)"
  using assms apply (induct txs arbitrary: \<phi>1 \<phi>2)
  subgoal by auto
  subgoal for tx txs \<phi>1 \<phi>2 by (cases tx) auto .

lemma psubst_imp[simp]:
  assumes "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla"
    and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
    and "distinct (map snd txs)"
  shows "psubst (imp \<phi>1 \<phi>2) txs = imp (psubst \<phi>1 txs) (psubst \<phi>2 txs)"
proof-
  define us where us: "us = getFrN (map snd txs) (map fst txs) [imp \<phi>1 \<phi>2] (length txs)"
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> Fvars \<phi>1 = {}"
    "set us \<inter> Fvars \<phi>2 = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    "distinct us"
    using assms unfolding us
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[imp \<phi>1 \<phi>2]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[imp \<phi>1 \<phi>2]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[imp \<phi>1 \<phi>2]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[imp \<phi>1 \<phi>2]" "length txs"]
    apply -
    subgoal by auto
    subgoal by fastforce
    subgoal by fastforce
    subgoal by fastforce
    subgoal by (fastforce simp: image_iff)
    by auto

  define vs1 where vs1: "vs1 = getFrN (map snd txs) (map fst txs) [\<phi>1] (length txs)"
  have vs1_facts: "set vs1  \<subseteq> var"
    "set vs1 \<inter> Fvars \<phi>1 = {}"
    "set vs1 \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set vs1 \<inter> snd ` (set txs) = {}"
    "length vs1 = length txs"
    "distinct vs1"
    using assms unfolding vs1
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>1]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>1]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[\<phi>1]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[\<phi>1]" "length txs"]
    apply -
    subgoal by auto
    subgoal by auto
    subgoal by fastforce
    subgoal by force
    by auto

  define vs2 where vs2: "vs2 = getFrN (map snd txs) (map fst txs) [\<phi>2] (length txs)"
  have vs2_facts: "set vs2  \<subseteq> var"
    "set vs2 \<inter> Fvars \<phi>2 = {}"
    "set vs2 \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set vs2 \<inter> snd ` (set txs) = {}"
    "length vs2 = length txs"
    "distinct vs2"
    using assms unfolding vs2
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>2]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>2]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[\<phi>2]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[\<phi>2]" "length txs"]
    apply -
    subgoal by auto
    subgoal by auto
    subgoal by fastforce
    subgoal by force
    by auto

  let ?tus = "zip (map fst txs) us"
  let ?uxs = "zip (map Var us) (map snd txs)"
  let ?tvs1 = "zip (map fst txs) vs1"
  let ?vxs1 = "zip (map Var vs1) (map snd txs)"
  let ?tvs2 = "zip (map fst txs) vs2"
  let ?vxs2 = "zip (map Var vs2) (map snd txs)"

  let ?c = "rawpsubst (imp \<phi>1 \<phi>2) ?uxs"
  have c: "?c = imp (rawpsubst \<phi>1 ?uxs) (rawpsubst \<phi>2 ?uxs)"
    apply(rule rawpsubst_imp) using assms us_facts apply (auto intro!: rawpsubstT)
    apply(drule set_zip_rightD) apply simp apply blast
    apply(drule set_zip_leftD) apply simp apply blast .
  have 0: "rawpsubst ?c ?tus =
    imp (rawpsubst (rawpsubst \<phi>1 ?uxs) ?tus) (rawpsubst (rawpsubst \<phi>2 ?uxs) ?tus)"
    unfolding c
    using assms us_facts
    by (intro rawpsubst_imp) (auto intro!: rawpsubst dest!: set_zip_D)
  have 1: "rawpsubst (rawpsubst \<phi>1 ?uxs) ?tus = rawpsubst (rawpsubst \<phi>1 ?vxs1) ?tvs1"
    using assms vs1_facts us_facts
    by (intro rawpsubst_compose_freshVar2) (auto intro!: rawpsubst)
  have 2: "rawpsubst (rawpsubst \<phi>2 ?uxs) ?tus = rawpsubst (rawpsubst \<phi>2 ?vxs2) ?tvs2"
    using assms vs2_facts us_facts
    by (intro rawpsubst_compose_freshVar2) (auto intro!: rawpsubst)
  show ?thesis unfolding psubst_def by (simp add: Let_def us[symmetric] vs1[symmetric] vs2[symmetric] 0 1 2)
qed

lemma rawpsubst_eqv:
  assumes "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla"
    and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
  shows "rawpsubst (eqv \<phi>1 \<phi>2) txs = eqv (rawpsubst \<phi>1 txs) (rawpsubst \<phi>2 txs)"
  using assms apply (induct txs arbitrary: \<phi>1 \<phi>2)
  subgoal by auto
  subgoal for tx txs \<phi>1 \<phi>2 by (cases tx) auto .

lemma psubst_eqv[simp]:
  assumes "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla"
    and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
    and "distinct (map snd txs)"
  shows "psubst (eqv \<phi>1 \<phi>2) txs = eqv (psubst \<phi>1 txs) (psubst \<phi>2 txs)"
proof-
  define us where us: "us = getFrN (map snd txs) (map fst txs) [eqv \<phi>1 \<phi>2] (length txs)"
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> Fvars \<phi>1 = {}"
    "set us \<inter> Fvars \<phi>2 = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    "distinct us"
    using assms unfolding us
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[eqv \<phi>1 \<phi>2]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[eqv \<phi>1 \<phi>2]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[eqv \<phi>1 \<phi>2]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[eqv \<phi>1 \<phi>2]" "length txs"]
    apply -
    subgoal by auto
    subgoal by fastforce
    subgoal by fastforce
    subgoal by fastforce
    subgoal by (fastforce simp: image_iff)
    by auto

  define vs1 where vs1: "vs1 = getFrN (map snd txs) (map fst txs) [\<phi>1] (length txs)"
  have vs1_facts: "set vs1  \<subseteq> var"
    "set vs1 \<inter> Fvars \<phi>1 = {}"
    "set vs1 \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set vs1 \<inter> snd ` (set txs) = {}"
    "length vs1 = length txs"
    "distinct vs1"
    using assms unfolding vs1
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>1]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>1]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[\<phi>1]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[\<phi>1]" "length txs"]
    apply -
    subgoal by auto
    subgoal by auto
    subgoal by fastforce
    subgoal by force
    by auto

  define vs2 where vs2: "vs2 = getFrN (map snd txs) (map fst txs) [\<phi>2] (length txs)"
  have vs2_facts: "set vs2  \<subseteq> var"
    "set vs2 \<inter> Fvars \<phi>2 = {}"
    "set vs2 \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set vs2 \<inter> snd ` (set txs) = {}"
    "length vs2 = length txs"
    "distinct vs2"
    using assms unfolding vs2
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>2]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>2]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[\<phi>2]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[\<phi>2]" "length txs"]
    apply -
    subgoal by auto
    subgoal by auto
    subgoal by fastforce
    subgoal by force
    by auto

  let ?tus = "zip (map fst txs) us"
  let ?uxs = "zip (map Var us) (map snd txs)"
  let ?tvs1 = "zip (map fst txs) vs1"
  let ?vxs1 = "zip (map Var vs1) (map snd txs)"
  let ?tvs2 = "zip (map fst txs) vs2"
  let ?vxs2 = "zip (map Var vs2) (map snd txs)"

  let ?c = "rawpsubst (eqv \<phi>1 \<phi>2) ?uxs"
  have c: "?c = eqv (rawpsubst \<phi>1 ?uxs) (rawpsubst \<phi>2 ?uxs)"
    using assms us_facts
    by (intro rawpsubst_eqv) (auto intro!: rawpsubstT dest!: set_zip_D)
  have 0: "rawpsubst ?c ?tus =
    eqv (rawpsubst (rawpsubst \<phi>1 ?uxs) ?tus) (rawpsubst (rawpsubst \<phi>2 ?uxs) ?tus)"
    unfolding c using assms us_facts
    by (intro rawpsubst_eqv) (auto intro!: rawpsubst dest!: set_zip_D)
  have 1: "rawpsubst (rawpsubst \<phi>1 ?uxs) ?tus = rawpsubst (rawpsubst \<phi>1 ?vxs1) ?tvs1"
    using assms vs1_facts us_facts
    by (intro rawpsubst_compose_freshVar2) (auto intro!: rawpsubst)
  have 2: "rawpsubst (rawpsubst \<phi>2 ?uxs) ?tus = rawpsubst (rawpsubst \<phi>2 ?vxs2) ?tvs2"
    using assms vs2_facts us_facts
    by (intro rawpsubst_compose_freshVar2) (auto intro!: rawpsubst)
  show ?thesis unfolding psubst_def by (simp add: Let_def us[symmetric] vs1[symmetric] vs2[symmetric] 0 1 2)
qed

lemma rawpsubst_all:
  assumes "\<phi> \<in> fmla" "y \<in> var"
    and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
    and "y \<notin> snd ` (set txs)" "y \<notin> \<Union> (FvarsT ` fst ` (set txs))"
  shows "rawpsubst (all y \<phi>) txs = all y (rawpsubst \<phi> txs)"
  using assms apply (induct txs arbitrary: \<phi>)
  subgoal by auto
  subgoal for tx txs \<phi> by (cases tx) auto .

lemma psubst_all[simp]:
  assumes "\<phi> \<in> fmla" "y \<in> var"
    and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
    and "y \<notin> snd ` (set txs)" "y \<notin> \<Union> (FvarsT ` fst ` (set txs))"
    and "distinct (map snd txs)"
  shows "psubst (all y \<phi>) txs = all y (psubst \<phi> txs)"
proof-
  define us where us: "us = getFrN (map snd txs) (map fst txs) [all y \<phi>] (length txs)"
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> (Fvars \<phi> - {y}) = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    "distinct us"
    using assms unfolding us
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[all y \<phi>]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[all y \<phi>]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[all y \<phi>]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[all y \<phi>]" "length txs"]
    apply -
    subgoal by auto
    subgoal by fastforce
    subgoal by fastforce
    subgoal by (fastforce simp: image_iff)
    by auto

  define vs where vs: "vs = getFrN (map snd txs) (map fst txs) [\<phi>] (length txs)"
  have vs_facts: "set vs  \<subseteq> var"
    "set vs \<inter> Fvars \<phi> = {}"
    "set vs \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set vs \<inter> snd ` (set txs) = {}"
    "length vs = length txs"
    "distinct vs"
    using assms unfolding vs
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[\<phi>]" "length txs"]
    apply -
    subgoal by auto
    subgoal by fastforce
    subgoal by fastforce
    subgoal by (fastforce simp: image_iff)
    by auto

  define ws where ws: "ws = getFrN (y # map snd txs) (map fst txs) [\<phi>] (length txs)"
  have ws_facts: "set ws  \<subseteq> var"
    "set ws \<inter> Fvars \<phi> = {}"  "y \<notin> set ws"
    "set ws \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set ws \<inter> snd ` (set txs) = {}"
    "length ws = length txs"
    "distinct ws"
    using assms unfolding ws
    using getFrN_Fvars[of "y # map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_FvarsT[of "y # map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_var[of "y # map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_length[of "y # map snd txs" "map fst txs" "[\<phi>]" "length txs"]
    apply -
    subgoal by auto
    subgoal by fastforce
    subgoal by fastforce
    subgoal by (fastforce simp: image_iff)
    subgoal by (fastforce simp: image_iff)
    by auto

  have 0: "rawpsubst (all y \<phi>) (zip (map Var ws) (map snd txs)) =
           all y (rawpsubst \<phi> (zip (map Var ws) (map snd txs)))"
    using assms ws_facts  apply(intro rawpsubst_all)
    subgoal by auto
    subgoal by auto
    subgoal by (auto dest!: set_zip_D)
    subgoal by (auto dest!: set_zip_D)
    subgoal by (auto dest!: set_zip_D)
    subgoal by (fastforce dest: set_zip_D) .

  have 1: "rawpsubst ((rawpsubst \<phi> (zip (map Var ws) (map snd txs)))) (zip (map fst txs) ws) =
           rawpsubst ((rawpsubst \<phi> (zip (map Var vs) (map snd txs)))) (zip (map fst txs) vs)"
    apply(rule rawpsubst_compose_freshVar2)
    using assms ws_facts vs_facts by (auto intro!: rawpsubst)
  have "rawpsubst (rawpsubst (all y \<phi>) (zip (map Var us) (map snd txs))) (zip (map fst txs) us) =
        rawpsubst (rawpsubst (all y \<phi>) (zip (map Var ws) (map snd txs))) (zip (map fst txs) ws)"
    using assms ws_facts us_facts
    by (intro rawpsubst_compose_freshVar2) (auto intro!: rawpsubst)
  also have
    "\<dots> = all y (rawpsubst ((rawpsubst \<phi> (zip (map Var ws) (map snd txs)))) (zip (map fst txs) ws))"
    unfolding 0 using assms ws_facts
    by (intro rawpsubst_all) (auto dest!: set_zip_D intro!: rawpsubst)
  also have
    "\<dots> = all y (rawpsubst (rawpsubst \<phi> (zip (map Var vs) (map snd txs))) (zip (map fst txs) vs))"
    unfolding 1 ..
  finally show ?thesis unfolding psubst_def by (simp add: Let_def us[symmetric] vs[symmetric])
qed

lemma rawpsubst_exi:
  assumes "\<phi> \<in> fmla" "y \<in> var"
    and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
    and "y \<notin> snd ` (set txs)" "y \<notin> \<Union> (FvarsT ` fst ` (set txs))"
  shows "rawpsubst (exi y \<phi>) txs = exi y (rawpsubst \<phi> txs)"
  using assms apply (induct txs arbitrary: \<phi>)
  subgoal by auto
  subgoal for tx txs \<phi> by (cases tx) auto .

lemma psubst_exi[simp]:
  assumes "\<phi> \<in> fmla" "y \<in> var"
    and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
    and "y \<notin> snd ` (set txs)" "y \<notin> \<Union> (FvarsT ` fst ` (set txs))"
    and "distinct (map snd txs)"
  shows "psubst (exi y \<phi>) txs = exi y (psubst \<phi> txs)"
proof-
  define us where us: "us = getFrN (map snd txs) (map fst txs) [exi y \<phi>] (length txs)"
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> (Fvars \<phi> - {y}) = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    "distinct us"
    using assms unfolding us
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[exi y \<phi>]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[exi y \<phi>]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[exi y \<phi>]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[exi y \<phi>]" "length txs"]
    apply -
    subgoal by auto
    subgoal by fastforce
    subgoal by fastforce
    subgoal by (fastforce simp: image_iff)
    subgoal by (fastforce simp: image_iff)
    by auto

  define vs where vs: "vs = getFrN (map snd txs) (map fst txs) [\<phi>] (length txs)"
  have vs_facts: "set vs  \<subseteq> var"
    "set vs \<inter> Fvars \<phi> = {}"
    "set vs \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set vs \<inter> snd ` (set txs) = {}"
    "length vs = length txs"
    "distinct vs"
    using assms unfolding vs
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[\<phi>]" "length txs"]
    apply -
    subgoal by auto
    subgoal by fastforce
    subgoal by fastforce
    subgoal by (fastforce simp: image_iff)
    subgoal by (fastforce simp: image_iff)
    by auto

  define ws where ws: "ws = getFrN (y # map snd txs) (map fst txs) [\<phi>] (length txs)"
  have ws_facts: "set ws  \<subseteq> var"
    "set ws \<inter> Fvars \<phi> = {}"  "y \<notin> set ws"
    "set ws \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set ws \<inter> snd ` (set txs) = {}"
    "length ws = length txs"
    "distinct ws"
    using assms unfolding ws
    using getFrN_Fvars[of "y # map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_FvarsT[of "y # map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_var[of "y # map snd txs" "map fst txs" "[\<phi>]" _ "length txs"]
      getFrN_length[of "y # map snd txs" "map fst txs" "[\<phi>]" "length txs"]
    apply -
    subgoal by auto
    subgoal by fastforce
    subgoal by fastforce
    subgoal by (fastforce simp: image_iff)
    subgoal by (fastforce simp: image_iff)
    by auto

  have 0: "rawpsubst (exi y \<phi>) (zip (map Var ws) (map snd txs)) =
           exi y (rawpsubst \<phi> (zip (map Var ws) (map snd txs)))"
    using assms ws_facts apply(intro rawpsubst_exi)
    subgoal by auto
    subgoal by auto
    subgoal by (auto dest!: set_zip_D)
    subgoal by (auto dest!: set_zip_D)
    subgoal by (auto dest!: set_zip_D)
    subgoal by (fastforce dest: set_zip_D) .

  have 1: "rawpsubst ((rawpsubst \<phi> (zip (map Var ws) (map snd txs)))) (zip (map fst txs) ws) =
           rawpsubst ((rawpsubst \<phi> (zip (map Var vs) (map snd txs)))) (zip (map fst txs) vs)"
    using assms ws_facts vs_facts
    by (intro rawpsubst_compose_freshVar2) (auto intro!: rawpsubst)
  have "rawpsubst (rawpsubst (exi y \<phi>) (zip (map Var us) (map snd txs))) (zip (map fst txs) us) =
        rawpsubst (rawpsubst (exi y \<phi>) (zip (map Var ws) (map snd txs))) (zip (map fst txs) ws)"
    using assms ws_facts us_facts
    by (intro rawpsubst_compose_freshVar2) (auto intro!: rawpsubst)
  also have
    "\<dots> = exi y (rawpsubst ((rawpsubst \<phi> (zip (map Var ws) (map snd txs)))) (zip (map fst txs) ws))"
    using assms ws_facts unfolding 0
    by (intro rawpsubst_exi) (auto dest!: set_zip_D intro!: rawpsubst)
  also have
    "\<dots> = exi y (rawpsubst (rawpsubst \<phi> (zip (map Var vs) (map snd txs))) (zip (map fst txs) vs))"
    unfolding 1 ..
  finally show ?thesis unfolding psubst_def by (simp add: Let_def us[symmetric] vs[symmetric])
qed

end \<comment> \<open>context @{locale Syntax_with_Connectives}\<close>


locale Syntax_with_Numerals_and_Connectives =
  Syntax_with_Numerals
  var trm fmla Var FvarsT substT Fvars subst
  num
  +
  Syntax_with_Connectives
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  for
    var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
    and Var FvarsT substT Fvars subst
    and num
    and eql cnj imp all exi
begin

lemma subst_all_num[simp]:
  assumes "\<phi> \<in> fmla" "x \<in> var" "y \<in> var" "n \<in> num"
  shows "x \<noteq> y \<Longrightarrow> subst (all x \<phi>) n y = all x (subst \<phi> n y)"
  using assms by simp

lemma subst_exi_num[simp]:
  assumes "\<phi> \<in> fmla" "x \<in> var" "y \<in> var" "n \<in> num"
  shows "x \<noteq> y \<Longrightarrow> subst (exi x \<phi>) n y = exi x (subst \<phi> n y)"
  using assms by simp


text \<open>The "soft substitution" function:\<close>
definition softSubst :: "'fmla \<Rightarrow> 'trm \<Rightarrow> 'var \<Rightarrow> 'fmla" where
  "softSubst \<phi> t x = exi x (cnj (eql (Var x) t) \<phi>)"

lemma softSubst[simp,intro]: "\<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> softSubst \<phi> t x \<in> fmla"
  unfolding softSubst_def by auto

lemma Fvars_softSubst[simp]:
  "\<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
 Fvars (softSubst \<phi> t x) = (Fvars \<phi> \<union> FvarsT t - {x})"
  unfolding softSubst_def by auto

lemma Fvars_softSubst_subst_in:
  "\<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> x \<notin> FvarsT t \<Longrightarrow> x \<in> Fvars \<phi> \<Longrightarrow>
 Fvars (softSubst \<phi> t x) = Fvars (subst \<phi> t x)"
  by auto

lemma Fvars_softSubst_subst_notIn:
  "\<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> x \<notin> FvarsT t \<Longrightarrow> x \<notin> Fvars \<phi> \<Longrightarrow>
 Fvars (softSubst \<phi> t x) = Fvars (subst \<phi> t x) \<union> FvarsT t"
  by auto

end \<comment> \<open>context @{locale Syntax_with_Connectives}\<close>

text \<open>The addition of False among logical connectives\<close>

locale Syntax_with_Connectives_False =
  Syntax_with_Connectives
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  for
    var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
    and Var FvarsT substT Fvars subst
    and eql cnj imp all exi
    +
  fixes fls::'fmla
  assumes
    fls[simp,intro!]: "fls \<in> fmla"
    and
    Fvars_fls[simp,intro!]: "Fvars fls = {}"
    and
    subst_fls[simp]:
    "\<And>t x. t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> subst fls t x = fls"
begin

text \<open>Negation as a derrived connective:\<close>
definition neg :: "'fmla \<Rightarrow> 'fmla" where
  "neg \<phi> = imp \<phi> fls"

lemma
  neg[simp]: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> neg \<phi> \<in> fmla"
  and
  Fvars_neg[simp]: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars (neg \<phi>) = Fvars \<phi>"
  and
  subst_neg[simp]:
  "\<And>\<phi> t x. \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
  subst (neg \<phi>) t x = neg (subst \<phi> t x)"
  unfolding neg_def by auto

text \<open>True as a derived connective:\<close>
definition tru where "tru = neg fls"

lemma
  tru[simp,intro!]: "tru \<in> fmla"
  and
  Fvars_tru[simp]: "Fvars tru = {}"
  and
  subst_tru[simp]: "\<And> t x. t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> subst tru t x = tru"
  unfolding tru_def by auto


subsection \<open>Iterated conjunction\<close>

text \<open>First we define list-based conjunction:\<close>
fun lcnj :: "'fmla list \<Rightarrow> 'fmla" where
  "lcnj [] = tru"
| "lcnj (\<phi> # \<phi>s) = cnj \<phi> (lcnj \<phi>s)"

lemma lcnj[simp,intro!]: "set \<phi>s \<subseteq> fmla \<Longrightarrow> lcnj \<phi>s \<in> fmla"
  by (induct \<phi>s) auto

lemma Fvars_lcnj[simp]:
  "set \<phi>s \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> Fvars (lcnj \<phi>s) = \<Union> (set (map Fvars \<phi>s))"
  by(induct \<phi>s) auto

lemma subst_lcnj[simp]:
  "set \<phi>s \<subseteq> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
 subst (lcnj \<phi>s) t x = lcnj (map (\<lambda>\<phi>. subst \<phi> t x) \<phi>s)"
  by(induct \<phi>s) auto

text \<open>Then we define (finite-)set-based conjunction:\<close>
definition scnj :: "'fmla set \<Rightarrow> 'fmla" where
  "scnj F = lcnj (asList F)"

lemma scnj[simp,intro!]: "F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> scnj F \<in> fmla"
  unfolding scnj_def by auto

lemma Fvars_scnj[simp]:
  "F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow>Fvars (scnj F) = \<Union> (Fvars ` F)"
  unfolding scnj_def by auto

subsection \<open>Parallel substitution versus the new connectives\<close>

lemma rawpsubst_fls:
  "snd ` (set txs) \<subseteq> var \<Longrightarrow> fst ` (set txs) \<subseteq> trm \<Longrightarrow> rawpsubst fls txs = fls"
  by (induct txs) auto

lemma psubst_fls[simp]:
  assumes "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
  shows "psubst fls txs = fls"
proof-
  define us where us: "us = getFrN (map snd txs) (map fst txs) [fls] (length txs)"
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    "distinct us"
    using assms unfolding us
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[fls]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[fls]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[fls]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[fls]" "length txs"]
    apply -
    subgoal by auto
    subgoal by fastforce
    subgoal by (fastforce simp: image_iff)
    subgoal by (fastforce simp: image_iff)
    by auto
  have [simp]: "rawpsubst fls (zip (map Var us) (map snd txs)) = fls"
    using us_facts assms by (intro rawpsubst_fls) (auto dest!: set_zip_D)
  show ?thesis using assms us_facts
    unfolding psubst_def by (auto simp add: Let_def us[symmetric] intro!: rawpsubst_fls dest!: set_zip_D)
qed

lemma psubst_neg[simp]:
  assumes "\<phi> \<in> fmla"
    and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
    and "distinct (map snd txs)"
  shows "psubst (neg \<phi>) txs = neg (psubst \<phi> txs)"
  unfolding neg_def using assms psubst_imp psubst_fls by auto

lemma psubst_tru[simp]:
  assumes "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
    and "distinct (map snd txs)"
  shows "psubst tru txs = tru"
  unfolding tru_def using assms psubst_neg[of fls txs] psubst_fls by auto

lemma psubst_lcnj[simp]:
  "set \<phi>s \<subseteq> fmla \<Longrightarrow> snd ` (set txs) \<subseteq> var \<Longrightarrow> fst ` (set txs) \<subseteq> trm \<Longrightarrow>
 distinct (map snd txs) \<Longrightarrow>
 psubst (lcnj \<phi>s) txs = lcnj (map (\<lambda>\<phi>. psubst \<phi> txs) \<phi>s)"
  by (induct  \<phi>s) auto

end \<comment> \<open>context @{locale Syntax_with_Connectives_False}\<close>


section \<open>Adding Disjunction\<close>

text \<open>NB: In intuitionistic logic, disjunction is not definable from the other connectives.\<close>

locale Syntax_with_Connectives_False_Disj =
  Syntax_with_Connectives_False
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  for
    var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
    and Var FvarsT substT Fvars subst
    and eql cnj imp all exi
    and fls
    +
  fixes dsj :: "'fmla \<Rightarrow> 'fmla \<Rightarrow> 'fmla"
  assumes
    dsj[simp]: "\<And>\<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> dsj \<phi> \<chi> \<in> fmla"
    and
    Fvars_dsj[simp]: "\<And>\<phi> \<chi>. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow>
  Fvars (dsj \<phi> \<chi>) = Fvars \<phi> \<union> Fvars \<chi>"
    and
    subst_dsj[simp]:
    "\<And> x \<phi> \<chi> t. \<phi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
   subst (dsj \<phi> \<chi>) t x = dsj (subst \<phi> t x) (subst \<chi> t x)"
begin

subsection \<open>Iterated disjunction\<close>

text \<open>First we define list-based disjunction:\<close>
fun ldsj :: "'fmla list \<Rightarrow> 'fmla" where
  "ldsj [] = fls"
| "ldsj (\<phi> # \<phi>s) = dsj \<phi> (ldsj \<phi>s)"

lemma ldsj[simp,intro!]: "set \<phi>s \<subseteq> fmla \<Longrightarrow> ldsj \<phi>s \<in> fmla"
  by (induct \<phi>s) auto

lemma Fvars_ldsj[simp]:
  "set \<phi>s \<subseteq> fmla \<Longrightarrow> Fvars (ldsj \<phi>s) = \<Union> (set (map Fvars \<phi>s))"
  by(induct \<phi>s) auto

lemma subst_ldsj[simp]:
  "set \<phi>s \<subseteq> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
 subst (ldsj \<phi>s) t x = ldsj (map (\<lambda>\<phi>. subst \<phi> t x) \<phi>s)"
  by(induct \<phi>s) auto

text \<open>Then we define (finite-)set-based disjunction:\<close>
definition sdsj :: "'fmla set \<Rightarrow> 'fmla" where
  "sdsj F = ldsj (asList F)"

lemma sdsj[simp,intro!]: "F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> sdsj F \<in> fmla"
  unfolding sdsj_def by auto

lemma Fvars_sdsj[simp]:
  "F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> Fvars (sdsj F) = \<Union> (Fvars ` F)"
  unfolding sdsj_def by auto


subsection \<open>Parallel substitution versus the new connectives\<close>

lemma rawpsubst_dsj:
  assumes "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla"
    and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
  shows "rawpsubst (dsj \<phi>1 \<phi>2) txs = dsj (rawpsubst \<phi>1 txs) (rawpsubst \<phi>2 txs)"
  using assms apply (induct txs arbitrary: \<phi>1 \<phi>2)
  subgoal by auto
  subgoal for tx txs \<phi>1 \<phi>2 apply (cases tx) by auto .

lemma psubst_dsj[simp]:
  assumes "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla"
    and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
    and "distinct (map snd txs)"
  shows "psubst (dsj \<phi>1 \<phi>2) txs = dsj (psubst \<phi>1 txs) (psubst \<phi>2 txs)"
proof-
  define us where us: "us = getFrN (map snd txs) (map fst txs) [dsj \<phi>1 \<phi>2] (length txs)"
  have us_facts: "set us \<subseteq> var"
    "set us \<inter> Fvars \<phi>1 = {}"
    "set us \<inter> Fvars \<phi>2 = {}"
    "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set us \<inter> snd ` (set txs) = {}"
    "length us = length txs"
    "distinct us"
    using assms unfolding us
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[dsj \<phi>1 \<phi>2]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[dsj \<phi>1 \<phi>2]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[dsj \<phi>1 \<phi>2]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[dsj \<phi>1 \<phi>2]" "length txs"]
    apply -
    subgoal by auto
    subgoal by fastforce
    subgoal by (fastforce simp: image_iff)
    subgoal by (fastforce simp: image_iff)
    subgoal by (fastforce simp: image_iff)
    by auto

  define vs1 where vs1: "vs1 = getFrN (map snd txs) (map fst txs) [\<phi>1] (length txs)"
  have vs1_facts: "set vs1  \<subseteq> var"
    "set vs1 \<inter> Fvars \<phi>1 = {}"
    "set vs1 \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set vs1 \<inter> snd ` (set txs) = {}"
    "length vs1 = length txs"
    "distinct vs1"
    using assms unfolding vs1
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>1]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>1]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[\<phi>1]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[\<phi>1]" "length txs"]
    apply -
    subgoal by auto
    subgoal by fastforce
    subgoal by fastforce
    subgoal by (fastforce simp: image_iff)
    by auto

  define vs2 where vs2: "vs2 = getFrN (map snd txs) (map fst txs) [\<phi>2] (length txs)"
  have vs2_facts: "set vs2  \<subseteq> var"
    "set vs2 \<inter> Fvars \<phi>2 = {}"
    "set vs2 \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
    "set vs2 \<inter> snd ` (set txs) = {}"
    "length vs2 = length txs"
    "distinct vs2"
    using assms unfolding vs2
    using getFrN_Fvars[of "map snd txs" "map fst txs" "[\<phi>2]" _ "length txs"]
      getFrN_FvarsT[of "map snd txs" "map fst txs" "[\<phi>2]" _ "length txs"]
      getFrN_var[of "map snd txs" "map fst txs" "[\<phi>2]" _ "length txs"]
      getFrN_length[of "map snd txs" "map fst txs" "[\<phi>2]" "length txs"]
    apply -
    apply -
    subgoal by auto
    subgoal by fastforce
    subgoal by fastforce
    subgoal by (fastforce simp: image_iff)
    by auto

  let ?tus = "zip (map fst txs) us"
  let ?uxs = "zip (map Var us) (map snd txs)"
  let ?tvs1 = "zip (map fst txs) vs1"
  let ?vxs1 = "zip (map Var vs1) (map snd txs)"
  let ?tvs2 = "zip (map fst txs) vs2"
  let ?vxs2 = "zip (map Var vs2) (map snd txs)"

  let ?c = "rawpsubst (dsj \<phi>1 \<phi>2) ?uxs"
  have c: "?c = dsj (rawpsubst \<phi>1 ?uxs) (rawpsubst \<phi>2 ?uxs)"
    apply(rule rawpsubst_dsj) using assms us_facts apply (auto intro!: rawpsubstT)
    apply(drule set_zip_rightD) apply simp apply blast
    apply(drule set_zip_leftD) apply simp apply blast .
  have 0: "rawpsubst ?c ?tus =
    dsj (rawpsubst (rawpsubst \<phi>1 ?uxs) ?tus) (rawpsubst (rawpsubst \<phi>2 ?uxs) ?tus)"
    unfolding c using assms us_facts
    by (intro rawpsubst_dsj) (auto intro!: rawpsubst dest!: set_zip_D)
  have 1: "rawpsubst (rawpsubst \<phi>1 ?uxs) ?tus = rawpsubst (rawpsubst \<phi>1 ?vxs1) ?tvs1"
    using assms vs1_facts us_facts
    by (intro rawpsubst_compose_freshVar2) (auto intro!: rawpsubst)
  have 2: "rawpsubst (rawpsubst \<phi>2 ?uxs) ?tus = rawpsubst (rawpsubst \<phi>2 ?vxs2) ?tvs2"
    using assms vs2_facts us_facts
    by (intro rawpsubst_compose_freshVar2) (auto intro!: rawpsubst)
  show ?thesis unfolding psubst_def by (simp add: Let_def us[symmetric] vs1[symmetric] vs2[symmetric] 0 1 2)
qed

lemma psubst_ldsj[simp]:
  "set \<phi>s \<subseteq> fmla \<Longrightarrow> snd ` (set txs) \<subseteq> var \<Longrightarrow> fst ` (set txs) \<subseteq> trm \<Longrightarrow>
 distinct (map snd txs) \<Longrightarrow>
 psubst (ldsj \<phi>s) txs = ldsj (map (\<lambda>\<phi>. psubst \<phi> txs) \<phi>s)"
  by (induct  \<phi>s) auto

end \<comment> \<open>context @{locale Syntax_with_Connectives_False_Disj}\<close>


section \<open>Adding an Ordering-Like Formula\<close>

locale Syntax_with_Numerals_and_Connectives_False_Disj =
  Syntax_with_Connectives_False_Disj
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  +
  Syntax_with_Numerals_and_Connectives
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  for
    var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
    and Var FvarsT substT Fvars subst
    and eql cnj imp all exi
    and fls
    and dsj
    and num

text \<open>... and in addition a formula expressing order (think: less than or equal to)\<close>
locale Syntax_PseudoOrder =
  Syntax_with_Numerals_and_Connectives_False_Disj
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  for
    var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
    and Var FvarsT substT Fvars subst
    and eql cnj imp all exi
    and fls
    and dsj
    and num
    +
  fixes
    \<comment> \<open>Lq is a formula with free variables xx yy:\<close>
    Lq :: 'fmla
  assumes
    Lq[simp,intro!]: "Lq \<in> fmla"
    and
    Fvars_Lq[simp]: "Fvars Lq = {zz,yy}"
begin

definition LLq where "LLq t1 t2 = psubst Lq [(t1,zz), (t2,yy)]"

lemma LLq_def2: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> yy \<notin> FvarsT t1 \<Longrightarrow>
 LLq t1 t2 = subst (subst Lq t1 zz) t2 yy"
  unfolding LLq_def by (rule psubst_eq_rawpsubst2[simplified]) auto

lemma LLq[simp,intro]:
  assumes "t1 \<in> trm" "t2 \<in> trm"
  shows "LLq t1 t2 \<in> fmla"
  using assms unfolding LLq_def by auto

lemma LLq2[simp,intro!]:
  "n \<in> num \<Longrightarrow> LLq n (Var yy') \<in> fmla"
  by auto

lemma Fvars_LLq[simp]: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> yy \<notin> FvarsT t1 \<Longrightarrow>
Fvars (LLq t1 t2) = FvarsT t1 \<union> FvarsT t2"
  by (auto simp add: LLq_def2 subst2_fresh_switch)

lemma LLq_simps[simp]:
  "m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (LLq m (Var yy)) n yy = LLq m n"
  "m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (LLq m (Var yy')) n yy = LLq m (Var yy')"
  "m \<in> num \<Longrightarrow> subst (LLq m (Var yy')) (Var yy) yy' = LLq m (Var yy)"
  "n \<in> num \<Longrightarrow> subst (LLq (Var xx) (Var yy)) n xx = LLq n (Var yy)"
  "n \<in> num \<Longrightarrow> subst (LLq (Var zz) (Var yy)) n yy = LLq (Var zz) n"
  "m \<in> num \<Longrightarrow> subst (LLq (Var zz) (Var yy)) m zz = LLq m (Var yy)"
  "m \<in> num \<Longrightarrow> n \<in> num \<Longrightarrow> subst (LLq (Var zz) n) m xx = LLq (Var zz) n"
  by (auto simp: LLq_def2 subst2_fresh_switch)

end \<comment> \<open>context @{locale Syntax_PseudoOrder}\<close>


section \<open>Allowing the Renaming of Quantified Variables\<close>

text \<open>So far, we did not need any renaming axiom for the quantifiers. However,
our axioms for substitution implicitly assume the irrelevance of the bound names;
in other words, their usual instances would have this property; and since this assumption
greatly simplifies the formal development, we make it at this point.\<close>

locale Syntax_with_Connectives_Rename =
Syntax_with_Connectives
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
+
assumes all_rename:
"\<And>\<phi> x y. \<phi> \<in> fmla \<Longrightarrow> x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow> y \<notin> Fvars \<phi> \<Longrightarrow>
  all x \<phi> = all y (subst \<phi> (Var y) x)"
and exi_rename:
"\<And>\<phi> x y. \<phi> \<in> fmla \<Longrightarrow> x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow> y \<notin> Fvars \<phi> \<Longrightarrow>
  exi x \<phi> = exi y (subst \<phi> (Var y) x)"
begin

lemma all_rename2:
"\<phi> \<in> fmla \<Longrightarrow> x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow> (y = x \<or> y \<notin> Fvars \<phi>) \<Longrightarrow>
  all x \<phi> = all y (subst \<phi> (Var y) x)"
using all_rename by (cases "y = x") (auto simp del: Fvars_subst)

lemma exi_rename2:
"\<phi> \<in> fmla \<Longrightarrow> x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow> (y = x \<or> y \<notin> Fvars \<phi>) \<Longrightarrow>
  exi x \<phi> = exi y (subst \<phi> (Var y) x)"
using exi_rename by (cases "y = x") (auto simp del: Fvars_subst)


section \<open>The Exists-Unique Quantifier\<close>

text \<open>It is phrased in such a way as to avoid substitution:\<close>

definition exu :: "'var \<Rightarrow> 'fmla \<Rightarrow> 'fmla" where
"exu x \<phi> \<equiv> let y = getFr [x] [] [\<phi>] in
 cnj (exi x \<phi>) (exi y (all x (imp \<phi> (eql (Var x) (Var y)))))"

lemma exu[simp,intro]:
"x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> exu x \<phi> \<in> fmla"
unfolding exu_def by (simp add: Let_def)

lemma Fvars_exu[simp]:
"x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> Fvars (exu x \<phi>) = Fvars \<phi> - {x}"
unfolding exu_def by (auto simp: Let_def getFr_Fvars)

lemma exu_def_var:
assumes [simp]: "x \<in> var" "y \<in> var" "y \<noteq> x" "y \<notin> Fvars \<phi>" "\<phi> \<in> fmla"
shows
"exu x \<phi> = cnj (exi x \<phi>) (exi y (all x (imp \<phi> (eql (Var x) (Var y)))))"
proof-
  have [simp]: "x \<noteq> y" using assms by blast
  define z where z: "z \<equiv> getFr [x] [] [\<phi>]"
  have z_facts[simp]:  "z \<in> var" "z \<noteq> x" "x \<noteq> z" "z \<notin> Fvars \<phi>"
  unfolding z using getFr_FvarsT_Fvars[of "[x]" "[]" "[\<phi>]"] by auto
  define u where u: "u \<equiv> getFr [x,y,z] [] [\<phi>]"
  have u_facts[simp]:  "u \<in> var" "u \<noteq> x" "u \<noteq> z" "y \<noteq> u" "u \<noteq> y" "x \<noteq> u" "z \<noteq> u" "u \<notin> Fvars \<phi>"
  unfolding u using getFr_FvarsT_Fvars[of "[x,y,z]" "[]" "[\<phi>]"] by auto

  have "exu x \<phi> =  cnj (exi x \<phi>) (exi u (all x (imp \<phi> (eql (Var x) (Var u)))))"
  by (auto simp: exu_def Let_def z[symmetric] exi_rename[of "all x (imp \<phi> (eql (Var x) (Var z)))" z u])
  also have "\<dots> = cnj (exi x \<phi>) (exi y (all x (imp \<phi> (eql (Var x) (Var y)))))"
  by (auto simp: exi_rename[of "all x (imp \<phi> (eql (Var x) (Var u)))" u y]
     split: if_splits)
  finally show ?thesis .
qed

lemma subst_exu[simp]:
assumes [simp]: "\<phi> \<in> fmla" "t \<in> trm" "x \<in> var" "y \<in> var" "x \<noteq> y" "x \<notin> FvarsT t"
shows "subst (exu x \<phi>) t y = exu x (subst \<phi> t y)"
proof-
  define u where u: "u \<equiv> getFr [x,y] [t] [\<phi>]"
  have u_facts[simp]:  "u \<in> var" "u \<noteq> x" "u \<noteq> y" "y \<noteq> u" "x \<noteq> u"
    "u \<notin> FvarsT t" "u \<notin> Fvars \<phi>"
  unfolding u using getFr_FvarsT_Fvars[of "[x,y]" "[t]" "[\<phi>]"] by auto
  show ?thesis
  by (auto simp: Let_def exu_def_var[of _ u] subst_compose_diff)
qed

lemma subst_exu_idle[simp]:
assumes [simp]: "x \<in> var" "\<phi> \<in> fmla" "t \<in> trm"
shows "subst (exu x \<phi>) t x = exu x \<phi>"
by (intro subst_notIn) auto

lemma exu_rename:
assumes [simp]: "\<phi> \<in> fmla" "x \<in> var" "y \<in> var" "y \<notin> Fvars \<phi>"
shows "exu x \<phi> = exu y (subst \<phi> (Var y) x)"
proof(cases "y = x")
  case [simp]: False
  define z where z: "z = getFr [x] [] [\<phi>]"
  have z_facts[simp]:  "z \<in> var" "z \<noteq> x" "x \<noteq> z" "z \<notin> Fvars \<phi>"
  unfolding z using getFr_FvarsT_Fvars[of "[x]" "[]" "[\<phi>]"] by auto
  define u where u: "u \<equiv> getFr [x,y,z] [] [\<phi>]"
  have u_facts[simp]: "u \<in> var" "u \<noteq> x" "x \<noteq> u" "u \<noteq> y" "y \<noteq> u" "u \<noteq> z" "z \<noteq> u"
     "u \<notin> Fvars \<phi>"
  unfolding u using getFr_FvarsT_Fvars[of "[x,y,z]" "[]" "[\<phi>]"] by auto
  show ?thesis
  by (auto simp: exu_def_var[of _ u] exi_rename[of _ _ y] all_rename[of _ _ y])
qed auto

lemma exu_rename2:
"\<phi> \<in> fmla \<Longrightarrow> x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow> (y = x \<or> y \<notin> Fvars \<phi>) \<Longrightarrow>
  exu x \<phi> = exu y (subst \<phi> (Var y) x)"
using exu_rename by (cases "y = x") (auto simp del: Fvars_subst)

end \<comment> \<open>context @{locale Syntax_with_Connectives_Rename}\<close>

(*<*)
end
(*>*)