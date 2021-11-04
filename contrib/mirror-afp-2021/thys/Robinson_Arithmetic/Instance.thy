section \<open>Instantiation of Syntax-Independent Logic Infrastructure\<close>

(*<*)
theory Instance
imports "Syntax_Independent_Logic.Standard_Model" "Syntax_Independent_Logic.Deduction_Q" Robinson_Arithmetic
begin
(*>*)

subsection \<open>Preliminaries\<close>

inductive_set num :: "trm set" where
 zer[intro!,simp]: "zer \<in> num"
|suc[simp]: "t \<in> num \<Longrightarrow> suc t \<in> num"

definition ground_aux :: "trm \<Rightarrow> atom set \<Rightarrow> bool"
  where "ground_aux t S \<equiv> (supp t \<subseteq> S)"

abbreviation ground :: "trm \<Rightarrow> bool"
  where "ground t \<equiv> ground_aux t {}"

definition ground_fmla_aux :: "fmla \<Rightarrow> atom set \<Rightarrow> bool"
  where "ground_fmla_aux A S \<equiv> (supp A \<subseteq> S)"

abbreviation ground_fmla :: "fmla \<Rightarrow> bool"
  where "ground_fmla A \<equiv> ground_fmla_aux A {}"

lemma ground_aux_simps[simp]:
  "ground_aux zer S = True"
  "ground_aux (Var k) S = (if atom k \<in> S then True else False)"
  "ground_aux (suc t) S = (ground_aux t S)"
  "ground_aux (pls t u) S = (ground_aux t S \<and> ground_aux u S)"
  "ground_aux (tms t u) S = (ground_aux t S \<and> ground_aux u S)"
unfolding ground_aux_def
by (simp_all add: supp_at_base)

lemma ground_fmla_aux_simps[simp]:
  "ground_fmla_aux fls S = True"
  "ground_fmla_aux (t EQ u) S = (ground_aux t S \<and> ground_aux u S)"
  "ground_fmla_aux (A OR B) S = (ground_fmla_aux A S \<and> ground_fmla_aux B S)"
  "ground_fmla_aux (A AND B) S = (ground_fmla_aux A S \<and> ground_fmla_aux B S)"
  "ground_fmla_aux (A IFF B) S = (ground_fmla_aux A S \<and> ground_fmla_aux B S)"
  "ground_fmla_aux (neg A) S =  (ground_fmla_aux A S)"
  "ground_fmla_aux (exi x A) S = (ground_fmla_aux A (S \<union> {atom x}))"
by (auto simp: ground_fmla_aux_def ground_aux_def supp_conv_fresh)

lemma ground_fresh[simp]:
  "ground t \<Longrightarrow> atom i \<sharp> t"
  "ground_fmla A \<Longrightarrow> atom i \<sharp> A"
unfolding ground_aux_def ground_fmla_aux_def fresh_def
by simp_all

(* This applies to all nominal types, including terms and formulas: *)
definition "Fvars t = {a :: name. \<not> atom a \<sharp> t}"

lemma Fvars_trm_simps[simp]:
  "Fvars zer = {}"
  "Fvars (Var a) = {a}"
  "Fvars (suc x ) = Fvars x"
  "Fvars (pls x y) = Fvars x \<union> Fvars y"
  "Fvars (tms x y) = Fvars x \<union> Fvars y"
  by (auto simp: Fvars_def fresh_at_base(2))

lemma finite_Fvars_trm[simp]:
  fixes t :: trm
  shows "finite (Fvars t)"
  by (induct t rule: trm.induct) auto

lemma Fvars_fmla_simps[simp]:
  "Fvars (x EQ y) = Fvars x \<union> Fvars y"
  "Fvars (A OR B) = Fvars A \<union> Fvars B"
  "Fvars (A AND B) = Fvars A \<union> Fvars B"
  "Fvars (A IMP B) = Fvars A \<union> Fvars B"
  "Fvars fls = {}"
  "Fvars (neg A) = Fvars A"
  "Fvars (exi a A) = Fvars A - {a}"
  "Fvars (all a A) = Fvars A - {a}"
  by (auto simp: Fvars_def fresh_at_base(2))

lemma finite_Fvars_fmla[simp]:
  fixes A :: fmla
  shows "finite (Fvars A)"
  by (induct A rule: fmla.induct) auto

lemma subst_trm_subst_trm[simp]:
  "x \<noteq> y \<Longrightarrow> atom x \<sharp> u \<Longrightarrow> subst y u (subst x t v) = subst x (subst y u t) (subst y u v)"
  by (induct v rule: trm.induct) auto

lemma subst_fmla_subst_fmla[simp]:
  "x \<noteq> y \<Longrightarrow> atom x \<sharp> u \<Longrightarrow> (A(x::=t))(y::=u) = (A(y::=u))(x::=subst y u t)"
  by (nominal_induct A avoiding: x t y u rule: fmla.strong_induct) auto

lemma Fvars_empty_ground[simp]: "Fvars t = {} \<Longrightarrow> ground t"
  by (induct t rule: trm.induct) auto

lemma Fvars_ground_aux: "Fvars t \<subseteq> B \<Longrightarrow> ground_aux t (atom ` B)"
  by (induct t rule: trm.induct) auto

lemma ground_Fvars: "ground t \<longleftrightarrow> Fvars t = {}"
  apply (rule iffI)
  subgoal by (auto simp only: Fvars_def ground_fresh) []
  by auto

lemma Fvars_ground_fmla_aux: "Fvars A \<subseteq> B \<Longrightarrow> ground_fmla_aux A (atom ` B)"
  apply (induct A arbitrary: B rule: fmla.induct)
  subgoal by (auto simp: Diff_subset_conv Fvars_ground_aux)
  subgoal by (auto simp: Diff_subset_conv Fvars_ground_aux)
  subgoal by (auto simp: Diff_subset_conv Fvars_ground_aux)
  subgoal by (metis Diff_subset_conv Fvars_fmla_simps(7) Un_insert_left
              Un_insert_right ground_fmla_aux_simps(7)
              image_insert sup_bot.left_neutral sup_bot.right_neutral) .

lemma ground_fmla_Fvars: "ground_fmla A \<longleftrightarrow> Fvars A = {}"
  apply (rule iffI)
  subgoal by (auto simp only: Fvars_def ground_fresh)
  by (auto intro: Fvars_ground_fmla_aux[of A "{}", simplified])

lemma obtain_const_trm:
obtains t where "eval_trm e t = x" "t \<in> num"
apply (induct x)
using eval_trm.simps(1) eval_trm.simps(3) num.suc by blast+

lemma ex_eval_fmla_iff_exists_num:
  "eval_fmla e (exi k A) \<longleftrightarrow> (\<exists>t. eval_fmla e (A(k::=t)) \<and> t \<in> num)"
by (auto simp: eval_subst_fmla) (metis obtain_const_trm)

lemma exi_ren: "y \<notin> Fvars \<phi> \<Longrightarrow> exi x \<phi> = exi y (\<phi>(x::=Var y))"
using exi_ren_subst_fresh Fvars_def by blast

lemma all_ren: "y \<notin> Fvars \<phi> \<Longrightarrow> all x \<phi> = all y (\<phi>(x::=Var y))"
by (simp add: exi_ren)

lemma Fvars_num[simp]: "t \<in> num \<Longrightarrow> Fvars t = {}"
by (induct t rule: trm.induct) (auto elim: num.cases)

subsection \<open>Instantiation of the generic syntax and deduction relation\<close>

interpretation Generic_Syntax where
      var = "UNIV :: name set"
  and trm = "UNIV :: trm set"
  and fmla = "UNIV :: fmla set"
  and Var = Var
  and FvarsT = Fvars
  and substT = "\<lambda>t u x. subst x u t"
  and Fvars = Fvars
  and subst = "\<lambda>A u x. subst_fmla A x u"
  apply unfold_locales
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal for t by (induct t rule: trm.induct) auto
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal unfolding Fvars_def fresh_subst_fmla_if by auto
  subgoal unfolding Fvars_def by auto
  subgoal unfolding Fvars_def by simp
  subgoal by simp
  subgoal unfolding Fvars_def by simp .

interpretation Syntax_with_Numerals where
      var = "UNIV :: name set"
  and trm = "UNIV :: trm set"
  and fmla = "UNIV :: fmla set"
  and num = num
  and Var = Var
  and FvarsT = Fvars
  and substT = "\<lambda>t u x. subst x u t"
  and Fvars = Fvars
  and subst = "\<lambda>A u x. subst_fmla A x u"
  apply unfold_locales
  subgoal by (auto intro!: exI[of _ zer])
  subgoal by simp
  subgoal by (simp add: ground_Fvars) .

interpretation Deduct_with_False where
      var = "UNIV :: name set"
  and trm = "UNIV :: trm set"
  and fmla = "UNIV :: fmla set"
  and num = num
  and Var = Var
  and FvarsT = Fvars
  and substT = "\<lambda>t u x. subst x u t"
  and Fvars = Fvars
  and subst = "\<lambda>A u x. subst_fmla A x u"
  and eql = eql and cnj = cnj and imp = imp and all = all
  and exi = exi and fls = fls
  and prv = "(\<turnstile>) {}"
  apply unfold_locales
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal unfolding Fvars_def by simp
  subgoal unfolding Fvars_def by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal using MP_null by blast
  subgoal by blast
  subgoal for A B C
    apply (rule imp_I)+
    apply (rule MP_same[of _ B])
     apply (rule MP_same[of _ C])
      apply (auto intro: neg_D) .
  subgoal by blast
  subgoal by blast
  subgoal by blast
  subgoal unfolding Fvars_def by (auto intro: MP_null)
  subgoal unfolding Fvars_def by (auto intro: MP_null)
  subgoal by (auto intro: all_D)
  subgoal by (auto intro: exi_I)
  subgoal by simp
  subgoal by (metis cnj_E2 Iff_def imp_I Var_eql_subst_Iff)
  subgoal by blast .

interpretation Deduct_with_False_Disj where
      var = "UNIV :: name set"
  and trm = "UNIV :: trm set"
  and fmla = "UNIV :: fmla set"
  and num = num
  and Var = Var
  and FvarsT = Fvars
  and substT = "\<lambda>t u x. subst x u t"
  and Fvars = Fvars
  and subst = "\<lambda>A u x. subst_fmla A x u"
  and eql = eql and cnj = cnj and dsj = dsj and imp = imp
  and all = all and exi = exi and fls = fls
  and prv = "(\<turnstile>) {}"
  apply unfold_locales
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (auto intro: dsj_I1)
  subgoal by (auto intro: dsj_I2)
  subgoal by (auto intro: ContraAssume) .


subsection \<open>Instantiation of the arithmetic-enriched generic syntax and deduction relation\<close>

interpretation Syntax_Arith_aux where
      var = "UNIV :: name set"
  and trm = "UNIV :: trm set"
  and fmla = "UNIV :: fmla set"
  and num = num
  and Var = Var
  and FvarsT = Fvars
  and substT = "\<lambda>t u x. subst x u t"
  and Fvars = Fvars
  and subst = "\<lambda>A u x. subst_fmla A x u"
  and eql = eql and cnj = cnj and imp = imp and all = all
  and exi = exi and dsj = dsj and fls = fls
  and zer = zer and suc = suc and pls = pls and tms = tms
  by unfold_locales (auto simp: exi_ren all_ren)

lemma num_range_Num: "num = range Num"
proof-
  {fix t assume "t \<in> num"
   then have "\<exists>n. t = Num n"
   apply(induct t rule: trm.induct)
   subgoal by (auto intro: exI[of _ 0])
   subgoal by (auto elim: num.cases)
   subgoal by (metis Num.simps(2) num.cases trm.distinct(3) trm.eq_iff(3))
   by (auto elim: num.cases)
  }
  moreover
  {fix n have "Num n \<in> num"
   by (induct n) auto
  }
  ultimately show ?thesis by auto
qed

lemma [simp]: "{} \<turnstile> neg (zer EQ suc (Var xx))"
proof-
  have 0: "{} \<turnstile> Robinson_Arithmetic.neg (zer EQ suc (Var xx))"
  by (intro nprv.Q) (auto intro!: exI[of _ zz] simp: Q_axioms_def)
  show ?thesis unfolding neg_def
  by (simp add: 0 dsj_I1)
qed

lemma [simp]: "{} \<turnstile> Var yy EQ zer OR exi xx (Var yy EQ suc (Var xx))"
by (intro nprv.Q) (auto intro!: exI[of _ zz] simp: Q_axioms_def)

lemma [simp]: "{} \<turnstile> pls (Var xx) zer EQ Var xx"
by (intro nprv.Q) (auto intro!: exI[of _ zz] simp: Q_axioms_def)

lemma [simp]: "{} \<turnstile> tms (Var xx) zer EQ zer"
by (intro nprv.Q) (auto intro!: exI[of _ zz] simp: Q_axioms_def)

interpretation S: Syntax_Arith where
      var = "UNIV :: name set"
  and trm = "UNIV :: trm set"
  and fmla = "UNIV :: fmla set"
  and num = num
  and Var = Var
  and FvarsT = Fvars
  and substT = "\<lambda>t u x. subst x u t"
  and Fvars = Fvars
  and subst = "\<lambda>A u x. subst_fmla A x u"
  and eql = eql and cnj = cnj and imp = imp and all = all
  and exi = exi and dsj = dsj and fls = fls and zer = zer
  and suc = suc and pls = pls and tms = tms
  using num_range_Num by unfold_locales auto

interpretation Deduct_Q where
      var = "UNIV :: name set"
  and trm = "UNIV :: trm set"
  and fmla = "UNIV :: fmla set"
  and num = num
  and Var = Var
  and FvarsT = Fvars
  and substT = "\<lambda>t u x. subst x u t"
  and Fvars = Fvars
  and subst = "\<lambda>A u x. subst_fmla A x u"
  and eql = eql and cnj = cnj and imp = imp and all = all
  and exi = exi and dsj = dsj and fls = fls and zer = zer
  and suc = suc and pls = pls and tms = tms
  and prv = "(\<turnstile>) {}"
  by unfold_locales (auto simp add: Q Q_axioms_def)

subsection \<open>Instantiation of the abstract notion of standard model and truth\<close>

interpretation Minimal_Truth_Soundness where
      var = "UNIV :: name set"
  and trm = "UNIV :: trm set"
  and fmla = "UNIV :: fmla set"
  and num = num
  and Var = Var
  and FvarsT = Fvars
  and substT = "\<lambda>t u x. subst x u t"
  and Fvars = Fvars
  and subst = "\<lambda>A u x. subst_fmla A x u"
  and eql = eql and cnj = cnj and dsj = dsj and imp = imp
  and all = all and exi = exi and fls = fls
  and prv = "(\<turnstile>) {}"
  and isTrue = "eval_fmla e0"
  apply unfold_locales
  subgoal by (auto simp: fls_def)
  subgoal by simp
  subgoal by (auto simp only: ex_eval_fmla_iff_exists_num eval_fmla.simps  subst_fmla.simps)
  subgoal by (auto simp only: ex_eval_fmla_iff_exists_num)
  subgoal by (simp add: neg_def)
  subgoal by (auto dest: nprv_sound) .

(*<*)
end
(*>*)
