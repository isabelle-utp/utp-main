(*<*)
theory Robinson_Arithmetic
imports Nominal2.Nominal2
begin
(*>*)

section \<open>Terms and Formulas\<close>

text \<open>nat is a pure permutation type\<close>

instance nat :: pure by standard

atom_decl name

declare fresh_set_empty [simp]

lemma supp_name [simp]: fixes i::name shows "supp i = {atom i}"
  by (rule supp_at_base)

subsection \<open>The datatypes\<close>

nominal_datatype trm = zer | Var name | suc trm | pls trm trm | tms trm trm

nominal_datatype fmla =
    eql trm trm     (infixr "EQ" 150)
  | dsj fmla fmla   (infixr "OR" 130)
  | neg fmla
  | exi x::name f::fmla binds x in f

text \<open>eql are atomic formulas; dsj, neg, exi are non-atomic\<close>

declare trm.supp [simp] fmla.supp [simp]

subsection \<open>Substitution\<close>

nominal_function subst :: "name \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm"
  where
   "subst i x zer       = zer"
 | "subst i x (Var k)    = (if i=k then x else Var k)"
 | "subst i x (suc t) = suc (subst i x t)"
 | "subst i x (pls t u) = pls (subst i x t) (subst i x u)"
 | "subst i x (tms t u) = tms (subst i x t) (subst i x u)"
by (auto simp: eqvt_def subst_graph_aux_def) (metis trm.strong_exhaust)

nominal_termination (eqvt)
  by lexicographic_order

lemma fresh_subst_if [simp]:
  "j \<sharp> subst i x t \<longleftrightarrow> (atom i \<sharp> t \<and> j \<sharp> t) \<or> (j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))"
  by (induct t rule: trm.induct) (auto simp: fresh_at_base)

lemma forget_subst_trm [simp]: "atom a \<sharp> trm \<Longrightarrow> subst a x trm = trm"
  by (induct trm rule: trm.induct) (simp_all add: fresh_at_base)

lemma subst_trm_id [simp]: "subst a (Var a) trm = trm"
  by (induct trm rule: trm.induct) simp_all

lemma subst_trm_commute [simp]:
  "atom j \<sharp> trm \<Longrightarrow> subst j u (subst i t trm) = subst i (subst j u t) trm"
  by (induct trm rule: trm.induct) (auto simp: fresh_Pair)

lemma subst_trm_commute2 [simp]:
  "atom j \<sharp> t \<Longrightarrow> atom i \<sharp> u \<Longrightarrow> i \<noteq> j \<Longrightarrow> subst j u (subst i t trm) = subst i t (subst j u trm)"
  by (induct trm rule: trm.induct) auto

lemma repeat_subst_trm [simp]: "subst i u (subst i t trm) = subst i (subst i u t) trm"
  by (induct trm rule: trm.induct) auto

nominal_function  subst_fmla :: "fmla \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> fmla" ("_'(_::=_')" [1000, 0, 0] 200)
  where
    eql:   "(eql t u)(i::=x)   = eql  (subst i x t) (subst i x u)"
  | dsj: "(dsj A B)(i::=x) = dsj (A(i::=x)) (B(i::=x))"
  | neg:  "(neg A)(i::=x)    = neg  (A(i::=x))"
  | exi:   "atom j \<sharp> (i, x) \<Longrightarrow> (exi j A)(i::=x) = exi j (A(i::=x))"
subgoal by (simp add: eqvt_def subst_fmla_graph_aux_def)
subgoal by auto
subgoal by (metis fmla.strong_exhaust fresh_star_insert old.prod.exhaust)
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal
  by (simp add: eqvt_at_def fresh_star_def fresh_Pair fresh_at_base)
     (metis flip_at_base_simps(3) flip_fresh_fresh) .

nominal_termination (eqvt)
  by lexicographic_order

lemma size_subst_fmla [simp]: "size (A(i::=x)) = size A"
  by (nominal_induct A avoiding: i x rule: fmla.strong_induct) auto

lemma forget_subst_fmla [simp]: "atom a \<sharp> A \<Longrightarrow> A(a::=x) = A"
  by (nominal_induct A avoiding: a x rule: fmla.strong_induct) (auto simp: fresh_at_base)

lemma subst_fmla_id [simp]: "A(a::=Var a) = A"
  by (nominal_induct A avoiding: a rule: fmla.strong_induct) (auto simp: fresh_at_base)

lemma fresh_subst_fmla_if [simp]:
  "j \<sharp> (A(i::=x)) \<longleftrightarrow> (atom i \<sharp> A \<and> j \<sharp> A) \<or> (j \<sharp> x \<and> (j \<sharp> A \<or> j = atom i))"
  by (nominal_induct A avoiding: i x rule: fmla.strong_induct) (auto simp: fresh_at_base)

lemma subst_fmla_commute [simp]:
  "atom j \<sharp> A \<Longrightarrow> (A(i::=t))(j::=u) = A(i ::= subst j u t)"
  by (nominal_induct A avoiding: i j t u rule: fmla.strong_induct) (auto simp: fresh_at_base)

lemma repeat_subst_fmla [simp]: "(A(i::=t))(i::=u) = A(i ::= subst i u t)"
  by (nominal_induct A avoiding: i t u rule: fmla.strong_induct) auto

lemma subst_fmla_exi_with_renaming:
  "atom i' \<sharp> (A, i, j, t) \<Longrightarrow> (exi i A)(j ::= t) = exi i' (((i \<leftrightarrow> i') \<bullet> A)(j ::= t))"
  by (rule subst [of "exi i' ((i \<leftrightarrow> i') \<bullet> A)" "exi i A"])
     (auto simp: Abs1_eq_iff flip_def swap_commute)

text \<open>the simplifier cannot apply the rule above, because
it introduces a new variable at the right hand side.\<close>

lemma flip_subst_trm: "atom y \<sharp> t \<Longrightarrow> (x \<leftrightarrow> y) \<bullet> t = subst x (Var y) t"
apply(nominal_induct t avoiding: x y rule: trm.strong_induct)
by auto

lemma flip_subst_fmla: "atom y \<sharp> \<phi> \<Longrightarrow> (x \<leftrightarrow> y) \<bullet> \<phi> = \<phi>(x::=Var y)"
apply(nominal_induct \<phi> avoiding: x y rule: fmla.strong_induct)
apply (auto simp: flip_subst_trm)
using fresh_at_base(2) by blast

lemma exi_ren_subst_fresh: "atom y \<sharp> \<phi> \<Longrightarrow> exi x \<phi> = exi y (\<phi>(x::=Var y))"
  using flip_subst_fmla by auto


subsection\<open>Semantics\<close>

definition e0 :: "(name, nat) finfun"    \<comment> \<open>the null environment\<close>
  where "e0 \<equiv> finfun_const 0"

nominal_function eval_trm :: "(name, nat) finfun \<Rightarrow> trm \<Rightarrow> nat"
  where
   "eval_trm e zer = 0"
 | "eval_trm e (Var k) = finfun_apply e k"
 | "eval_trm e (suc t) = Suc (eval_trm e t)"
 | "eval_trm e (pls t u) = eval_trm e t + eval_trm e u"
 | "eval_trm e (tms t u) = eval_trm e t * eval_trm e u"
by (auto simp: eqvt_def eval_trm_graph_aux_def) (metis trm.strong_exhaust)

nominal_termination (eqvt)
  by lexicographic_order

nominal_function eval_fmla :: "(name, nat) finfun \<Rightarrow> fmla \<Rightarrow> bool"
  where
   "eval_fmla e (t EQ u) \<longleftrightarrow> eval_trm e t = eval_trm e u"
 | "eval_fmla e (A OR B) \<longleftrightarrow> eval_fmla e A \<or> eval_fmla e B"
 | "eval_fmla e (neg A) \<longleftrightarrow> (~ eval_fmla e A)"
 | "atom k \<sharp> e \<Longrightarrow> eval_fmla e (exi k A) \<longleftrightarrow> (\<exists>x. eval_fmla (finfun_update e k x) A)"
supply [[simproc del: defined_all]]
apply(simp add: eqvt_def eval_fmla_graph_aux_def)
apply(auto del: iffI) [11]
apply(rule_tac y=b and c="(a)" in fmla.strong_exhaust)
apply(auto simp: fresh_star_def)[4]
using [[simproc del: alpha_lst]] apply clarsimp
apply(erule_tac c="(ea)" in Abs_lst1_fcb2')
apply(rule pure_fresh)
apply(simp add: fresh_star_def)
apply (simp_all add: eqvt_at_def)
apply (simp_all add: perm_supp_eq)
done

nominal_termination (eqvt)
  by lexicographic_order

lemma eval_trm_rename:
  assumes "atom k' \<sharp> t"
  shows "eval_trm (finfun_update e k x) t =
         eval_trm (finfun_update e k' x) ((k' \<leftrightarrow> k) \<bullet> t)"
using assms
by (induct t rule: trm.induct) (auto simp: permute_flip_at)

lemma eval_fmla_rename:
  assumes "atom k' \<sharp> A"
  shows "eval_fmla (finfun_update e k x) A = eval_fmla (finfun_update e k' x) ((k' \<leftrightarrow> k) \<bullet> A)"
using assms
apply (nominal_induct A avoiding: e k k' x rule: fmla.strong_induct)
apply (simp_all add: eval_trm_rename[symmetric], metis)
apply (simp add: fresh_finfun_update fresh_at_base finfun_update_twist)
done

lemma better_ex_eval_fmla[simp]:
  "eval_fmla e (exi k A) \<longleftrightarrow> (\<exists>x. eval_fmla (finfun_update e k x) A)"
proof -
  obtain k'::name where k': "atom k' \<sharp> (k, e, A)"
    by (rule obtain_fresh)
  then have eq: "exi k' ((k' \<leftrightarrow> k) \<bullet> A) = exi k A"
    by (simp add: Abs1_eq_iff flip_def)
  have "eval_fmla e (exi k' ((k' \<leftrightarrow> k) \<bullet> A)) = (\<exists>x. eval_fmla (finfun_update e k' x) ((k' \<leftrightarrow> k) \<bullet> A))"
    using k' by simp
  also have "... = (\<exists>x. eval_fmla (finfun_update e k x) A)"
    by (metis eval_fmla_rename k' fresh_Pair)
  finally show ?thesis
    by (metis eq)
qed

lemma forget_eval_trm [simp]: "atom i \<sharp> t \<Longrightarrow>
    eval_trm (finfun_update e i x) t = eval_trm e t"
  by (induct t rule: trm.induct) (simp_all add: fresh_at_base)

lemma forget_eval_fmla [simp]:
   "atom k \<sharp> A \<Longrightarrow> eval_fmla (finfun_update e k x) A = eval_fmla e A"
  by (nominal_induct A avoiding: k e rule: fmla.strong_induct)
     (simp_all add: fresh_at_base finfun_update_twist)

lemma eval_subst_trm: "eval_trm e (subst i t u) =
   eval_trm (finfun_update e i (eval_trm e t)) u"
  by (induct u rule: trm.induct) (auto)

lemma eval_subst_fmla: "eval_fmla e (fmla(i::= t)) =
   eval_fmla (finfun_update e i (eval_trm e t)) fmla"
  by (nominal_induct fmla avoiding: i t e rule: fmla.strong_induct)
     (simp_all add: eval_subst_trm finfun_update_twist fresh_at_base)

subsection \<open>Derived logical connectives\<close>

abbreviation imp :: "fmla \<Rightarrow> fmla \<Rightarrow> fmla"   (infixr "IMP" 125)
  where "imp A B \<equiv> dsj (neg A) B"

abbreviation all :: "name \<Rightarrow> fmla \<Rightarrow> fmla"
  where "all i A \<equiv> neg (exi i (neg A))"

subsubsection \<open>Conjunction\<close>

definition cnj :: "fmla \<Rightarrow> fmla \<Rightarrow> fmla"   (infixr "AND" 135)
  where "cnj A B \<equiv> neg (dsj (neg A) (neg B))"

lemma cnj_eqvt [eqvt]: "p \<bullet> (A AND B) = (p \<bullet> A) AND (p \<bullet> B)"
  by (simp add: cnj_def)

lemma fresh_cnj [simp]: "a \<sharp> A AND B \<longleftrightarrow> (a \<sharp> A \<and> a \<sharp> B)"
  by (auto simp: cnj_def)

lemma supp_cnj [simp]: "supp (A AND B) = supp A \<union> supp B"
  by (auto simp: cnj_def)

lemma size_cnj [simp]: "size (A AND B) = size A + size B + 4"
  by (simp add: cnj_def)

lemma cnj_injective_iff [iff]: "(A AND B) = (A' AND B') \<longleftrightarrow> (A = A' \<and> B = B')"
  by (auto simp: cnj_def)

lemma subst_fmla_cnj [simp]: "(A AND B)(i::=x) = (A(i::=x)) AND (B(i::=x))"
  by (auto simp: cnj_def)

lemma eval_fmla_cnj [simp]: "eval_fmla e (cnj A B) \<longleftrightarrow> (eval_fmla e A \<and> eval_fmla e B)"
  by (auto simp: cnj_def)

subsubsection \<open>If and only if\<close>

definition Iff :: "fmla \<Rightarrow> fmla \<Rightarrow> fmla"   (infixr "IFF" 125)
  where "Iff A B = cnj (imp A B) (imp B A)"

lemma Iff_eqvt [eqvt]: "p \<bullet> (A IFF B) = (p \<bullet> A) IFF (p \<bullet> B)"
  by (simp add: Iff_def)

lemma fresh_Iff [simp]: "a \<sharp> A IFF B \<longleftrightarrow> (a \<sharp> A \<and> a \<sharp> B)"
  by (auto simp: cnj_def Iff_def)

lemma size_Iff [simp]: "size (A IFF B) = 2*(size A + size B) + 8"
  by (simp add: Iff_def)

lemma Iff_injective_iff [iff]: "(A IFF B) = (A' IFF B') \<longleftrightarrow> (A = A' \<and> B = B')"
  by (auto simp: Iff_def)

lemma subst_fmla_Iff [simp]: "(A IFF B)(i::=x) = (A(i::=x)) IFF (B(i::=x))"
  by (auto simp: Iff_def)

lemma eval_fmla_Iff [simp]: "eval_fmla e (Iff A B) \<longleftrightarrow> (eval_fmla e A  \<longleftrightarrow>  eval_fmla e B)"
  by (auto simp: Iff_def)

subsubsection \<open>False\<close>

definition fls  where "fls \<equiv> neg (zer EQ zer)"

lemma fls_eqvt [eqvt]: "(p \<bullet> fls) = fls"
  by (simp add: fls_def)

lemma fls_fresh [simp]: "a \<sharp> fls"
  by (simp add: fls_def)

section \<open>Axioms and Theorems\<close>

subsection \<open>Logical axioms\<close>

inductive_set boolean_axioms :: "fmla set"
  where
    Ident:     "A IMP A \<in> boolean_axioms"
  | dsjI1:    "A IMP (A OR B) \<in> boolean_axioms"
  | dsjCont:  "(A OR A) IMP A \<in> boolean_axioms"
  | dsjAssoc: "(A OR (B OR C)) IMP ((A OR B) OR C) \<in> boolean_axioms"
  | dsjcnj:  "(C OR A) IMP (((neg C) OR B) IMP (A OR B)) \<in> boolean_axioms"

lemma boolean_axioms_hold: "A \<in> boolean_axioms \<Longrightarrow> eval_fmla e A"
  by (induct rule: boolean_axioms.induct, auto)

inductive_set special_axioms :: "fmla set" where
  I: "A(i::=x) IMP (exi i A) \<in> special_axioms"

lemma special_axioms_hold: "A \<in> special_axioms \<Longrightarrow> eval_fmla e A"
  by (induct rule: special_axioms.induct, auto) (metis eval_subst_fmla)

lemma twist_forget_eval_fmla [simp]:
   "atom j \<sharp> (i, A)
    \<Longrightarrow> eval_fmla (finfun_update (finfun_update (finfun_update e i x) j y) i z) A =
        eval_fmla (finfun_update e i z) A"
  by (metis finfun_update_twice finfun_update_twist forget_eval_fmla fresh_Pair)

subsection \<open>Concrete variables\<close>

declare Abs_name_inject[simp]

abbreviation
  "X0 \<equiv> Abs_name (Atom (Sort ''Theory_Syntax_Q.name'' []) 0)"

abbreviation
  "X1 \<equiv> Abs_name (Atom (Sort ''Robinson_Arithmetic.name'' []) (Suc 0))"
   \<comment> \<open>We prefer @{term "Suc 0"} because simplification will transform 1 to that form anyway.\<close>

abbreviation
  "X2 \<equiv> Abs_name (Atom (Sort ''Robinson_Arithmetic.name'' []) 2)"

abbreviation
  "X3 \<equiv> Abs_name (Atom (Sort ''Robinson_Arithmetic.name'' []) 3)"

abbreviation
  "X4 \<equiv> Abs_name (Atom (Sort ''Robinson_Arithmetic.name'' []) 4)"

subsection \<open>Equality axioms\<close>

definition refl_ax :: fmla where
  "refl_ax = Var X1 EQ Var X1"

lemma refl_ax_holds: "eval_fmla e refl_ax"
  by (auto simp: refl_ax_def)

definition eq_cong_ax :: fmla where
  "eq_cong_ax = ((Var X1 EQ Var X2) AND (Var X3 EQ Var X4)) IMP
                ((Var X1 EQ Var X3) IMP (Var X2 EQ Var X4))"

lemma eq_cong_ax_holds: "eval_fmla e eq_cong_ax"
  by (auto simp: cnj_def eq_cong_ax_def)

definition syc_cong_ax :: fmla where
  "syc_cong_ax = ((Var X1 EQ Var X2)) IMP
                ((suc (Var X1)) EQ (suc (Var X2)))"

lemma syc_cong_ax_holds: "eval_fmla e syc_cong_ax"
  by (auto simp: cnj_def syc_cong_ax_def)

definition pls_cong_ax :: fmla where
  "pls_cong_ax = ((Var X1 EQ Var X2) AND (Var X3 EQ Var X4)) IMP
                  ((pls (Var X1) (Var X3)) EQ (pls (Var X2) (Var X4)))"

lemma pls_cong_ax_holds: "eval_fmla e pls_cong_ax"
  by (auto simp: cnj_def pls_cong_ax_def)

definition tms_cong_ax :: fmla where
  "tms_cong_ax = ((Var X1 EQ Var X2) AND (Var X3 EQ Var X4)) IMP
                  ((tms (Var X1) (Var X3)) EQ (tms (Var X2) (Var X4)))"

lemma tms_cong_ax_holds: "eval_fmla e tms_cong_ax"
  by (auto simp: cnj_def tms_cong_ax_def)

definition equality_axioms :: "fmla set" where
  "equality_axioms = {refl_ax, eq_cong_ax, syc_cong_ax, pls_cong_ax, tms_cong_ax}"

lemma equality_axioms_hold: "A \<in> equality_axioms \<Longrightarrow> eval_fmla e A"
  by (auto simp: equality_axioms_def refl_ax_holds eq_cong_ax_holds
       syc_cong_ax_holds pls_cong_ax_holds tms_cong_ax_holds)

subsection \<open>The Q (Robinson-arithmetic-specific) axioms\<close>

definition "Q_axioms \<equiv>
 {A | A X1 X2.
   X1 \<noteq> X2 \<and>
   (A = neg (zer EQ suc (Var X1)) \<or>
    A = suc (Var X1) EQ suc (Var X2) IMP Var X1 EQ Var X2 \<or>
    A = Var X2 EQ zer OR exi X1 (Var X2 EQ suc (Var X1)) \<or>
    A = pls (Var X1) zer EQ Var X1 \<or>
    A = pls (Var X1) (suc (Var X2)) EQ suc (pls (Var X1) (Var X2)) \<or>
    A = tms (Var X1) zer EQ zer \<or>
    A = tms (Var X1) (suc (Var X2)) EQ pls (tms (Var X1) (Var X2)) (Var X1))}"


subsection \<open>The proof system\<close>

inductive nprv :: "fmla set \<Rightarrow> fmla \<Rightarrow> bool" (infixl "\<turnstile>" 55)
  where
    Hyp:    "A \<in> H \<Longrightarrow> H \<turnstile> A"
  | Q:  "A \<in> Q_axioms \<Longrightarrow> H \<turnstile> A"
  | Bool:   "A \<in> boolean_axioms \<Longrightarrow> H \<turnstile> A"
  | eql:     "A \<in> equality_axioms \<Longrightarrow> H \<turnstile> A"
  | Spec:   "A \<in> special_axioms \<Longrightarrow> H \<turnstile> A"
  | MP:     "H \<turnstile> A IMP B \<Longrightarrow> H' \<turnstile> A \<Longrightarrow> H \<union> H' \<turnstile> B"
  | exiists: "H \<turnstile> A IMP B \<Longrightarrow> atom i \<sharp> B \<Longrightarrow> \<forall>C \<in> H. atom i \<sharp> C \<Longrightarrow> H \<turnstile> (exi i A) IMP B"


subsection\<open>Derived rules of inference\<close>

lemma contraction: "insert A (insert A H) \<turnstile> B \<Longrightarrow> insert A H \<turnstile> B"
  by (metis insert_absorb2)

lemma thin_Un: "H \<turnstile> A \<Longrightarrow> H \<union> H' \<turnstile> A"
  by (metis Bool MP boolean_axioms.Ident sup_commute)

lemma thin: "H \<turnstile> A \<Longrightarrow> H \<subseteq> H' \<Longrightarrow> H' \<turnstile> A"
  by (metis Un_absorb1 thin_Un)

lemma thin0: "{} \<turnstile> A \<Longrightarrow> H \<turnstile> A"
  by (metis sup_bot_left thin_Un)

lemma thin1: "H \<turnstile> B \<Longrightarrow> insert A H \<turnstile> B"
  by (metis subset_insertI thin)

lemma thin2: "insert A1 H \<turnstile> B \<Longrightarrow> insert A1 (insert A2 H) \<turnstile> B"
  by (blast intro: thin)

lemma thin3: "insert A1 (insert A2 H) \<turnstile> B \<Longrightarrow> insert A1 (insert A2 (insert A3 H)) \<turnstile> B"
  by (blast intro: thin)

lemma thin4:
  "insert A1 (insert A2 (insert A3 H)) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 H))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate2: "insert A2 (insert A1 H) \<turnstile> B \<Longrightarrow> insert A1 (insert A2 H) \<turnstile> B"
  by (blast intro: thin)

lemma rotate3: "insert A3 (insert A1 (insert A2 H)) \<turnstile> B \<Longrightarrow> insert A1 (insert A2 (insert A3 H)) \<turnstile> B"
  by (blast intro: thin)

lemma rotate4:
  "insert A4 (insert A1 (insert A2 (insert A3 H))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 H))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate5:
  "insert A5 (insert A1 (insert A2 (insert A3 (insert A4 H)))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 H)))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate6:
  "insert A6 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 H))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 H))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate7:
  "insert A7 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 H)))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 H)))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate8:
  "insert A8 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 H))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 H))))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate9:
  "insert A9 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 H)))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 H)))))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate10:
  "insert A10 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 H))))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 H))))))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate11:
  "insert A11 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 H)))))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 H)))))))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate12:
  "insert A12 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 H))))))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 (insert A12 H))))))))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate13:
  "insert A13 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 (insert A12 H)))))))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 (insert A12 (insert A13 H)))))))))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate14:
  "insert A14 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 (insert A12 (insert A13 H))))))))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 (insert A12 (insert A13 (insert A14 H))))))))))))) \<turnstile> B"
  by (blast intro: thin)

lemma rotate15:
  "insert A15 (insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 (insert A12 (insert A13 (insert A14 H)))))))))))))) \<turnstile> B
   \<Longrightarrow> insert A1 (insert A2 (insert A3 (insert A4 (insert A5 (insert A6 (insert A7 (insert A8 (insert A9 (insert A10 (insert A11 (insert A12 (insert A13 (insert A14 (insert A15 H)))))))))))))) \<turnstile> B"
  by (blast intro: thin)

lemma MP_same: "H \<turnstile> A IMP B \<Longrightarrow> H \<turnstile> A \<Longrightarrow> H \<turnstile> B"
  by (metis MP Un_absorb)

lemma MP_thin: "HA \<turnstile> A IMP B \<Longrightarrow> HB \<turnstile> A \<Longrightarrow> HA \<union> HB \<subseteq> H \<Longrightarrow> H \<turnstile> B"
  by (metis MP_same le_sup_iff thin)

lemma MP_null: "{} \<turnstile> A IMP B \<Longrightarrow> H \<turnstile> A \<Longrightarrow> H \<turnstile> B"
  by (metis MP_same thin0)

lemma dsj_commute: "H \<turnstile> B OR A \<Longrightarrow> H \<turnstile> A OR B"
  using dsjcnj [of B A B] Ident [of B]
by (metis Bool MP_same)

lemma S: assumes  "H \<turnstile> A IMP (B IMP C)" "H' \<turnstile> A IMP B" shows "H \<union> H' \<turnstile> A IMP C"
proof -
  have "H' \<union> H \<turnstile> (neg A) OR (C OR (neg A))"
    by (metis Bool MP MP_same boolean_axioms.dsjcnj dsj_commute dsjAssoc assms)
  thus ?thesis
    by (metis Bool dsj_commute Un_commute MP_same dsjAssoc dsjCont dsjI1)
qed

lemma Assume: "insert A H \<turnstile> A"
  by (metis Hyp insertI1)

lemmas AssumeH = Assume Assume [THEN rotate2] Assume [THEN rotate3] Assume [THEN rotate4] Assume [THEN rotate5]
                 Assume [THEN rotate6] Assume [THEN rotate7] Assume [THEN rotate8] Assume [THEN rotate9] Assume [THEN rotate10]
                 Assume [THEN rotate11] Assume [THEN rotate12]
declare AssumeH [intro!]

lemma imp_triv_I: "H \<turnstile> B \<Longrightarrow> H \<turnstile> A IMP B"
  by (metis Bool dsj_commute MP_same boolean_axioms.dsjI1)

lemma dsjAssoc1: "H \<turnstile> A OR (B OR C) \<Longrightarrow> H \<turnstile> (A OR B) OR C"
  by (metis Bool MP_same boolean_axioms.dsjAssoc)

lemma dsjAssoc2: "H \<turnstile> (A OR B) OR C \<Longrightarrow> H \<turnstile> A OR (B OR C)"
  by (metis dsjAssoc1 dsj_commute)

lemma dsj_commute_imp: "H \<turnstile> (B OR A) IMP (A OR B)"
  using dsjcnj [of B A B] Ident [of B]
  by (metis Bool dsjAssoc2 dsj_commute MP_same)

lemma dsj_Semicong_1: "H \<turnstile> A OR C \<Longrightarrow> H \<turnstile> A IMP B \<Longrightarrow> H \<turnstile> B OR C"
  using dsjcnj [of A C B]
  by (metis Bool dsj_commute MP_same)

lemma imp_imp_commute: "H \<turnstile> B IMP (A IMP C) \<Longrightarrow> H \<turnstile> A IMP (B IMP C)"
  by (metis dsjAssoc1 dsjAssoc2 dsj_Semicong_1 dsj_commute_imp)


subsection\<open>The deduction theorem\<close>

lemma deduction_Diff: assumes "H \<turnstile> B" shows "H - {C} \<turnstile> C IMP B"
using assms
proof (induct)
  case (Hyp A H) thus ?case
    by (metis Bool imp_triv_I boolean_axioms.Ident nprv.Hyp member_remove remove_def)
next
  case (Q H) thus ?case
    by (metis imp_triv_I nprv.Q)
next
  case (Bool A H) thus ?case
    by (metis imp_triv_I nprv.Bool)
next
  case (eql A H) thus ?case
    by (metis imp_triv_I nprv.eql)
next
  case (Spec A H) thus ?case
    by (metis imp_triv_I nprv.Spec)
next
  case (MP H A B H')
  hence "(H-{C}) \<union> (H'-{C}) \<turnstile> imp C B"
    by (simp add: S)
  thus ?case
    by (metis Un_Diff)
next
  case (exiists H A B i) show ?case
  proof (cases "C \<in> H")
    case True
    hence "atom i \<sharp> C" using exiists by auto
    moreover have "H - {C} \<turnstile> A IMP C IMP B" using exiists
      by (metis imp_imp_commute)
    ultimately have "H - {C} \<turnstile> (exi i A) IMP C IMP B" using exiists
      using nprv.eql
      by (simp add: nprv.exiists)
    thus ?thesis
      by (metis imp_imp_commute)
  next
    case False
    hence "H - {C} = H" by auto
    thus ?thesis using exiists
      by (metis imp_triv_I nprv.exiists)
  qed
qed

theorem imp_I [intro!]: "insert A H \<turnstile> B \<Longrightarrow> H \<turnstile> A IMP B"
  by (metis Diff_insert_absorb imp_triv_I deduction_Diff insert_absorb)

lemma anti_deduction: "H \<turnstile> A IMP B \<Longrightarrow> insert A H \<turnstile> B"
   by (metis Assume MP_same thin1)

subsection\<open>Cut rules\<close>

lemma cut:  "H \<turnstile> A \<Longrightarrow> insert A H' \<turnstile> B \<Longrightarrow> H \<union> H' \<turnstile> B"
  by (metis MP Un_commute imp_I)

lemma cut_same: "H \<turnstile> A \<Longrightarrow> insert A H \<turnstile> B \<Longrightarrow> H \<turnstile> B"
  by (metis Un_absorb cut)

lemma cut_thin: "HA \<turnstile> A \<Longrightarrow> insert A HB \<turnstile> B \<Longrightarrow> HA \<union> HB \<subseteq> H \<Longrightarrow> H \<turnstile> B"
  by (metis thin cut)

lemma cut0: "{} \<turnstile> A \<Longrightarrow> insert A H \<turnstile> B \<Longrightarrow> H \<turnstile> B"
  by (metis cut_same thin0)

lemma cut1: "{A} \<turnstile> B \<Longrightarrow> H \<turnstile> A \<Longrightarrow> H \<turnstile> B"
  by (metis cut sup_bot_right)

lemma rcut1: "{A} \<turnstile> B \<Longrightarrow> insert B H \<turnstile> C \<Longrightarrow> insert A H \<turnstile> C"
  by (metis Assume cut1 cut_same rotate2 thin1)

lemma cut2: "\<lbrakk>{A,B} \<turnstile> C; H \<turnstile> A; H \<turnstile> B\<rbrakk> \<Longrightarrow> H \<turnstile> C"
  by (metis Un_empty_right Un_insert_right cut cut_same)

lemma rcut2: "{A,B} \<turnstile> C \<Longrightarrow> insert C H \<turnstile> D \<Longrightarrow> H \<turnstile> B \<Longrightarrow> insert A H \<turnstile> D"
  by (metis Assume cut2 cut_same insert_commute thin1)

lemma cut3: "\<lbrakk>{A,B,C} \<turnstile> D; H \<turnstile> A; H \<turnstile> B; H \<turnstile> C\<rbrakk> \<Longrightarrow> H \<turnstile> D"
  by (metis MP_same cut2 imp_I)

lemma cut4: "\<lbrakk>{A,B,C,D} \<turnstile> E; H \<turnstile> A; H \<turnstile> B; H \<turnstile> C; H \<turnstile> D\<rbrakk> \<Longrightarrow> H \<turnstile> E"
  by (metis MP_same cut3 [of B C D] imp_I)


section\<open>Miscellaneous Logical Rules\<close>

lemma dsj_I1: "H \<turnstile> A \<Longrightarrow> H \<turnstile> A OR B"
  by (metis Bool MP_same boolean_axioms.dsjI1)

lemma dsj_I2: "H \<turnstile> B \<Longrightarrow> H \<turnstile> A OR B"
  by (metis dsj_commute dsj_I1)

lemma Peirce: "H \<turnstile> (neg A) IMP A \<Longrightarrow> H \<turnstile> A"
  using dsjcnj [of "neg A" A A]  dsjCont [of A]
  by (metis Bool MP_same boolean_axioms.Ident)

lemma Contra: "insert (neg A) H \<turnstile> A \<Longrightarrow> H \<turnstile> A"
  by (metis Peirce imp_I)

lemma imp_neg_I: "H \<turnstile> A IMP B \<Longrightarrow> H \<turnstile> A IMP (neg B) \<Longrightarrow> H \<turnstile> neg A"
  by (metis dsjcnj [of B "neg A" "neg A"] dsjCont Bool dsj_commute MP_same)

lemma negneg_I: "H \<turnstile> A \<Longrightarrow> H \<turnstile> neg (neg A)"
  using dsjcnj [of "neg (neg A)" "neg A" "neg (neg A)"]
  by (metis Bool Ident MP_same)

lemma negneg_D: "H \<turnstile> neg (neg A) \<Longrightarrow> H \<turnstile> A"
  by (metis dsj_I1 Peirce)

lemma neg_D: "H \<turnstile> neg A \<Longrightarrow> H \<turnstile> A \<Longrightarrow> H \<turnstile> B"
  by (metis imp_neg_I imp_triv_I negneg_D)

lemma dsj_neg_1: "H \<turnstile> A OR B \<Longrightarrow> H \<turnstile> neg B \<Longrightarrow> H \<turnstile> A"
  by (metis dsj_I1 dsj_Semicong_1 dsj_commute Peirce)

lemma dsj_neg_2: "H \<turnstile> A OR B \<Longrightarrow> H \<turnstile> neg A \<Longrightarrow> H \<turnstile> B"
  by (metis dsj_neg_1 dsj_commute)

lemma neg_dsj_I: "H \<turnstile> neg A \<Longrightarrow> H \<turnstile> neg B \<Longrightarrow> H \<turnstile> neg (A OR B)"
by (metis Bool dsj_neg_1 MP_same boolean_axioms.Ident dsjAssoc)

lemma cnj_I [intro!]: "H \<turnstile> A \<Longrightarrow> H \<turnstile> B \<Longrightarrow> H \<turnstile> A AND B"
  by (metis cnj_def negneg_I neg_dsj_I)

lemma cnj_E1: "H \<turnstile> A AND B \<Longrightarrow> H \<turnstile> A"
  by (metis cnj_def Bool dsj_neg_1 negneg_D boolean_axioms.dsjI1)

lemma cnj_E2: "H \<turnstile> A AND B \<Longrightarrow> H \<turnstile> B"
  by (metis cnj_def Bool dsj_I2 dsj_neg_2 MP_same dsjAssoc Ident)

lemma cnj_commute: "H \<turnstile> B AND A \<Longrightarrow> H \<turnstile> A AND B"
  by (metis cnj_E1 cnj_E2 cnj_I)

lemma cnj_E: assumes "insert A (insert B H) \<turnstile> C" shows "insert (A AND B) H \<turnstile> C"
apply (rule cut_same [where A=A], metis cnj_E1 Hyp insertI1)
by (metis (full_types) AssumeH(2) cnj_E2 assms cut_same [where A=B] insert_commute thin2)

lemmas cnj_EH = cnj_E cnj_E [THEN rotate2] cnj_E [THEN rotate3] cnj_E [THEN rotate4] cnj_E [THEN rotate5]
                 cnj_E [THEN rotate6] cnj_E [THEN rotate7] cnj_E [THEN rotate8] cnj_E [THEN rotate9] cnj_E [THEN rotate10]
declare cnj_EH [intro!]

lemma neg_I0: assumes "(\<And>B. atom i \<sharp> B \<Longrightarrow> insert A H \<turnstile> B)" shows "H \<turnstile> neg A"
  by (meson fls_fresh imp_I imp_neg_I assms fmla.fresh(3))

lemma neg_mono: "insert A H \<turnstile> B \<Longrightarrow> insert (neg B) H \<turnstile> neg A"
  by (rule neg_I0) (metis Hyp neg_D insert_commute insertI1 thin1)

lemma cnj_mono: "insert A H \<turnstile> B \<Longrightarrow> insert C H \<turnstile> D \<Longrightarrow> insert (A AND C) H \<turnstile> B AND D"
  by (metis cnj_E1 cnj_E2 cnj_I Hyp Un_absorb2 cut insertI1 subset_insertI)

lemma dsj_mono:
  assumes "insert A H \<turnstile> B" "insert C H \<turnstile> D" shows "insert (A OR C) H \<turnstile> B OR D"
proof -
  { fix A B C H
    have "insert (A OR C) H \<turnstile> (A IMP B) IMP C OR B"
      by (metis Bool Hyp MP_same boolean_axioms.dsjcnj insertI1)
    hence "insert A H \<turnstile> B \<Longrightarrow> insert (A OR C) H \<turnstile> C OR B"
      by (metis MP_same Un_absorb Un_insert_right imp_I thin_Un)
  }
  thus ?thesis
    by (metis cut_same assms thin2)
qed

lemma dsj_E:
  assumes A: "insert A H \<turnstile> C" and B: "insert B H \<turnstile> C" shows "insert (A OR B) H \<turnstile> C"
  by (metis A B dsj_mono negneg_I Peirce)

lemmas dsj_EH = dsj_E dsj_E [THEN rotate2] dsj_E [THEN rotate3] dsj_E [THEN rotate4] dsj_E [THEN rotate5]
                 dsj_E [THEN rotate6] dsj_E [THEN rotate7] dsj_E [THEN rotate8] dsj_E [THEN rotate9] dsj_E [THEN rotate10]
declare dsj_EH [intro!]

lemma Contra': "insert A H \<turnstile> neg A \<Longrightarrow> H \<turnstile> neg A"
  by (metis Contra neg_mono)

lemma negneg_E [intro!]: "insert A H \<turnstile> B \<Longrightarrow> insert (neg (neg A)) H \<turnstile> B"
  by (metis negneg_D neg_mono)

declare negneg_E [THEN rotate2, intro!]
declare negneg_E [THEN rotate3, intro!]
declare negneg_E [THEN rotate4, intro!]
declare negneg_E [THEN rotate5, intro!]
declare negneg_E [THEN rotate6, intro!]
declare negneg_E [THEN rotate7, intro!]
declare negneg_E [THEN rotate8, intro!]

lemma imp_E:
  assumes A: "H \<turnstile> A" and B: "insert B H \<turnstile> C" shows "insert (A IMP B) H \<turnstile> C"
proof -
  have "insert (A IMP B) H \<turnstile> B"
    by (metis Hyp A thin1 MP_same insertI1)
  thus ?thesis
    by (metis cut [where B=C] Un_insert_right sup_commute sup_idem B)
qed

lemma imp_cut:
  assumes "insert C H \<turnstile> A IMP B" "{A} \<turnstile> C"
    shows "H \<turnstile> A IMP B"
  by (metis Contra dsj_I1 neg_mono assms rcut1)

lemma Iff_I [intro!]: "insert A H \<turnstile> B \<Longrightarrow> insert B H \<turnstile> A \<Longrightarrow> H \<turnstile> A IFF B"
  by (metis Iff_def cnj_I imp_I)

lemma Iff_MP_same: "H \<turnstile> A IFF B \<Longrightarrow> H \<turnstile> A \<Longrightarrow> H \<turnstile> B"
  by (metis Iff_def cnj_E1 MP_same)

lemma Iff_MP2_same: "H \<turnstile> A IFF B \<Longrightarrow> H \<turnstile> B \<Longrightarrow> H \<turnstile> A"
  by (metis Iff_def cnj_E2 MP_same)

lemma Iff_refl [intro!]: "H \<turnstile> A IFF A"
  by (metis Hyp Iff_I insertI1)

lemma Iff_sym: "H \<turnstile> A IFF B \<Longrightarrow> H \<turnstile> B IFF A"
  by (metis Iff_def cnj_commute)

lemma Iff_trans: "H \<turnstile> A IFF B \<Longrightarrow> H \<turnstile> B IFF C \<Longrightarrow> H \<turnstile> A IFF C"
  unfolding Iff_def
  by (metis cnj_E1 cnj_E2 cnj_I dsj_Semicong_1 dsj_commute)

lemma Iff_E:
  "insert A (insert B H) \<turnstile> C \<Longrightarrow> insert (neg A) (insert (neg B) H) \<turnstile> C \<Longrightarrow> insert (A IFF B) H \<turnstile> C"
  by (simp add: Assume Iff_def anti_deduction cnj_E dsj_EH(2) dsj_I1 insert_commute)

lemma Iff_E1:
  assumes A: "H \<turnstile> A" and B: "insert B H \<turnstile> C" shows "insert (A IFF B) H \<turnstile> C"
  by (metis Iff_def A B cnj_E imp_E insert_commute thin1)

lemma Iff_E2:
  assumes A: "H \<turnstile> A" and B: "insert B H \<turnstile> C" shows "insert (B IFF A) H \<turnstile> C"
  by (metis Iff_def A B Bool cnj_E2 cnj_mono imp_E boolean_axioms.Ident)

lemma Iff_MP_left: "H \<turnstile> A IFF B \<Longrightarrow> insert A H \<turnstile> C \<Longrightarrow> insert B H \<turnstile> C"
  by (metis Hyp Iff_E2 cut_same insertI1 insert_commute thin1)

lemma Iff_MP_left': "H \<turnstile> A IFF B \<Longrightarrow> insert B H \<turnstile> C \<Longrightarrow> insert A H \<turnstile> C"
  by (metis Iff_MP_left Iff_sym)

lemma Swap: "insert (neg B) H \<turnstile> A \<Longrightarrow> insert (neg A) H \<turnstile> B"
  by (metis negneg_D neg_mono)

lemma Cases: "insert A H \<turnstile> B \<Longrightarrow> insert (neg A) H \<turnstile> B \<Longrightarrow> H \<turnstile> B"
  by (metis Contra neg_D neg_mono)

lemma neg_cnj_E: "H \<turnstile> B \<Longrightarrow> insert (neg A) H \<turnstile> C \<Longrightarrow> insert (neg (A AND B)) H \<turnstile> C"
  by (metis cnj_I Swap thin1)

lemma dsj_CI: "insert (neg B) H \<turnstile> A \<Longrightarrow> H \<turnstile> A OR B"
  by (metis Contra dsj_I1 dsj_I2 Swap)

lemma dsj_3I: "insert (neg A) (insert (neg C) H) \<turnstile> B \<Longrightarrow> H \<turnstile> A OR B OR C"
  by (metis dsj_CI dsj_commute insert_commute)

lemma Contrapos1: "H \<turnstile> A IMP B \<Longrightarrow> H \<turnstile> neg B IMP neg A"
  by (metis Bool MP_same boolean_axioms.dsjcnj boolean_axioms.Ident)

lemma Contrapos2: "H \<turnstile> (neg B) IMP (neg A) \<Longrightarrow> H \<turnstile> A IMP B"
  by (metis Bool MP_same boolean_axioms.dsjcnj boolean_axioms.Ident)

lemma ContraAssumeN [intro]: "B \<in> H \<Longrightarrow> insert (neg B) H \<turnstile> A"
  by (metis Hyp Swap thin1)

lemma ContraAssume: "neg B \<in> H \<Longrightarrow> insert B H \<turnstile> A"
  by (metis dsj_I1 Hyp anti_deduction)

lemma ContraProve: "H \<turnstile> B \<Longrightarrow> insert (neg B) H \<turnstile> A"
  by (metis Swap thin1)

lemma dsj_IE1: "insert B H \<turnstile> C \<Longrightarrow> insert (A OR B) H \<turnstile> A OR C"
  by (metis Assume dsj_mono)

lemmas dsj_IE1H = dsj_IE1 dsj_IE1 [THEN rotate2] dsj_IE1 [THEN rotate3] dsj_IE1 [THEN rotate4] dsj_IE1 [THEN rotate5]
                 dsj_IE1 [THEN rotate6] dsj_IE1 [THEN rotate7] dsj_IE1 [THEN rotate8]
declare dsj_IE1H [intro!]

subsection\<open>Quantifier reasoning\<close>

lemma exi_I: "H \<turnstile> A(i::=x) \<Longrightarrow> H \<turnstile> exi i A"
  by (metis MP_same Spec special_axioms.intros)

lemma exi_E:
  assumes "insert A H \<turnstile> B" "atom i \<sharp> B" "\<forall>C \<in> H. atom i \<sharp> C"
  shows "insert (exi i A) H \<turnstile> B"
  by (metis exiists imp_I anti_deduction assms)

lemma exi_E_with_renaming:
  assumes "insert ((i \<leftrightarrow> i') \<bullet> A) H \<turnstile> B" "atom i' \<sharp> (A,i,B)" "\<forall>C \<in> H. atom i' \<sharp> C"
  shows "insert (exi i A) H \<turnstile> B"
proof -
  have "exi i A = exi i' ((i \<leftrightarrow> i') \<bullet> A)"
    using assms using flip_subst_fmla by auto
  thus ?thesis
    by (metis exi_E assms fresh_Pair)
qed

lemmas exi_EH = exi_E exi_E [THEN rotate2] exi_E [THEN rotate3] exi_E [THEN rotate4] exi_E [THEN rotate5]
                 exi_E [THEN rotate6] exi_E [THEN rotate7] exi_E [THEN rotate8] exi_E [THEN rotate9] exi_E [THEN rotate10]
declare exi_EH [intro!]

lemma exi_mono: "insert A H \<turnstile> B \<Longrightarrow> \<forall>C \<in> H. atom i \<sharp> C \<Longrightarrow> insert (exi i A) H \<turnstile> (exi i B)"
  by (auto simp add: intro: exi_I [where x="Var i"])

lemma all_I [intro!]: "H \<turnstile> A \<Longrightarrow> \<forall>C \<in> H. atom i \<sharp> C \<Longrightarrow> H \<turnstile> all i A"
  by (auto intro: ContraProve neg_I0)

lemma all_D: "H \<turnstile> all i A \<Longrightarrow> H \<turnstile> A(i::=x)"
  by (metis Assume exi_I negneg_D neg_mono neg cut_same)

lemma all_E: "insert (A(i::=x)) H \<turnstile> B \<Longrightarrow> insert (all i A) H \<turnstile> B"
  by (metis exi_I negneg_D neg_mono neg)

lemma all_E': "H \<turnstile> all i A \<Longrightarrow> insert (A(i::=x)) H \<turnstile> B \<Longrightarrow> H \<turnstile> B"
  by (metis all_D cut_same)

subsection\<open>Congruence rules\<close>

lemma neg_cong: "H \<turnstile> A IFF A' \<Longrightarrow> H \<turnstile> neg A IFF neg A'"
  by (metis Iff_def cnj_E1 cnj_E2 cnj_I Contrapos1)

lemma dsj_cong: "H \<turnstile> A IFF A' \<Longrightarrow> H \<turnstile> B IFF B' \<Longrightarrow> H \<turnstile> A OR B IFF A' OR B'"
  by (metis cnj_E1 cnj_E2 dsj_mono Iff_I Iff_def anti_deduction)

lemma cnj_cong: "H \<turnstile> A IFF A' \<Longrightarrow> H \<turnstile> B IFF B' \<Longrightarrow> H \<turnstile> A AND B IFF A' AND B'"
  by (metis cnj_def dsj_cong neg_cong)

lemma imp_cong: "H \<turnstile> A IFF A' \<Longrightarrow> H \<turnstile> B IFF B' \<Longrightarrow> H \<turnstile> (A IMP B) IFF (A' IMP B')"
  by (metis dsj_cong neg_cong)

lemma Iff_cong: "H \<turnstile> A IFF A' \<Longrightarrow> H \<turnstile> B IFF B' \<Longrightarrow> H \<turnstile> (A IFF B) IFF (A' IFF B')"
  by (metis Iff_def cnj_cong imp_cong)

lemma exi_cong: "H \<turnstile> A IFF A' \<Longrightarrow> \<forall>C \<in> H. atom i \<sharp> C \<Longrightarrow> H \<turnstile> (exi i A) IFF (exi i A')"
  apply (rule Iff_I)
   apply (metis exi_mono Hyp Iff_MP_same Un_absorb Un_insert_right insertI1 thin_Un)
  apply (metis exi_mono Hyp Iff_MP2_same Un_absorb Un_insert_right insertI1 thin_Un)
  done

lemma all_cong: "H \<turnstile> A IFF A' \<Longrightarrow> \<forall>C \<in> H. atom i \<sharp> C \<Longrightarrow> H \<turnstile> (all i A) IFF (all i A')"
  by (metis exi_cong neg_cong)

lemma Subst: "H \<turnstile> A \<Longrightarrow> \<forall>B \<in> H. atom i \<sharp> B \<Longrightarrow> H \<turnstile> A (i::=x)"
  by (metis all_D all_I)


section\<open>Eqluality Reasoning\<close>

subsection\<open>The congruence property for @{term eql}, and other basic properties of equality\<close>

lemma eql_cong1: "{} \<turnstile> (t EQ t' AND u EQ u') IMP (t EQ u IMP t' EQ u')"
proof -
  obtain v2::name and v3::name and v4::name
    where v2: "atom v2 \<sharp> (t,X1,X3,X4)"
      and v3: "atom v3 \<sharp> (t,t',X1,v2,X4)"
      and v4: "atom v4 \<sharp> (t,t',u,X1,v2,v3)"
    by (metis obtain_fresh)
  have "{} \<turnstile> (Var X1 EQ Var X2 AND Var X3 EQ Var X4) IMP (Var X1 EQ Var X3 IMP Var X2 EQ Var X4)"
    by (rule eql) (simp add: eq_cong_ax_def equality_axioms_def)
  hence "{} \<turnstile> (Var X1 EQ Var X2 AND Var X3 EQ Var X4) IMP (Var X1 EQ Var X3 IMP Var X2 EQ Var X4)"
    by (drule_tac i=X1 and x="Var X1" in Subst) simp_all
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var X3 EQ Var X4) IMP (Var X1 EQ Var X3 IMP Var v2 EQ Var X4)"
    by (drule_tac i=X2 and x="Var v2" in Subst) simp_all
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var v3 EQ Var X4) IMP (Var X1 EQ Var v3 IMP Var v2 EQ Var X4)"
    using v2
    by (drule_tac i=X3 and x="Var v3" in Subst) simp_all
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var v3 EQ Var v4) IMP (Var X1 EQ Var v3 IMP Var v2 EQ Var v4)"
    using v2 v3
    by (drule_tac i=X4 and x="Var v4" in Subst) simp_all
  hence "{} \<turnstile> (t EQ Var v2 AND Var v3 EQ Var v4) IMP (t EQ Var v3 IMP Var v2 EQ Var v4)"
    using v2 v3 v4
    by (drule_tac i=X1 and x=t in Subst) simp_all
  hence "{} \<turnstile> (t EQ t' AND Var v3 EQ Var v4) IMP (t EQ Var v3 IMP t' EQ Var v4)"
    using v2 v3 v4
    by (drule_tac i=v2 and x="t'" in Subst) simp_all
  hence "{} \<turnstile> (t EQ t' AND u EQ Var v4) IMP (t EQ u IMP t' EQ Var v4)"
    using v3 v4
    by (drule_tac i=v3 and x=u in Subst) simp_all
  thus ?thesis
    using v4
    by (drule_tac i=v4 and x="u'" in Subst) simp_all
qed

lemma Refl [iff]: "H \<turnstile> t EQ t"
proof -
  have "{} \<turnstile> Var X1 EQ Var X1"
    by (rule eql) (simp add: equality_axioms_def refl_ax_def)
  hence "{} \<turnstile> t EQ t"
    by (drule_tac i=X1 and x=t in Subst) simp_all
  thus ?thesis
    by (metis empty_subsetI thin)
qed

text\<open>Apparently necessary in order to prove the congruence property.\<close>
lemma Sym: assumes "H \<turnstile> t EQ u" shows "H \<turnstile> u EQ t"
proof -
  have "{} \<turnstile>  (t EQ u AND t EQ t) IMP (t EQ t IMP u EQ t)"
    by (rule eql_cong1)
   moreover have "{t EQ u} \<turnstile> t EQ u AND t EQ t"
    by (metis Assume cnj_I Refl)
  ultimately have "{t EQ u} \<turnstile> u EQ t"
    by (metis MP_same MP Refl sup_bot_left)
  thus "H \<turnstile> u EQ t" by (metis assms cut1)
qed

lemma Sym_L: "insert (t EQ u) H \<turnstile> A \<Longrightarrow> insert (u EQ t) H \<turnstile> A"
  by (metis Assume Sym Un_empty_left Un_insert_left cut)

lemma Trans: assumes "H \<turnstile> x EQ y" "H \<turnstile> y EQ z" shows "H \<turnstile> x EQ z"
proof -
  have "\<And>H. H \<turnstile> (x EQ x AND y EQ z) IMP (x EQ y IMP x EQ z)"
    by (metis eql_cong1 bot_least thin)
  moreover have "{x EQ y, y EQ z} \<turnstile> x EQ x AND y EQ z"
    by (metis Assume cnj_I Refl thin1)
  ultimately have "{x EQ y, y EQ z} \<turnstile> x EQ z"
    by (metis Hyp MP_same insertI1)
  thus ?thesis
    by (metis assms cut2)
qed

lemma eql_cong:
  assumes "H \<turnstile> t EQ t'" "H \<turnstile> u EQ u'" shows "H \<turnstile> t EQ u IFF t' EQ u'"
proof -
  { fix t t' u u'
    assume  "H \<turnstile> t EQ t'" "H \<turnstile> u EQ u'"
    moreover have "{t EQ t', u EQ u'} \<turnstile> t EQ u IMP t' EQ u'" using eql_cong1
      by (metis Assume cnj_I MP_null insert_commute)
    ultimately have "H \<turnstile> t EQ u IMP t' EQ u'"
      by (metis cut2)
  }
  thus ?thesis
    by (metis Iff_def cnj_I assms Sym)
qed

lemma eql_Trans_E: "H \<turnstile> x EQ u \<Longrightarrow> insert (t EQ u) H \<turnstile> A \<Longrightarrow> insert (x EQ t) H \<turnstile> A"
  by (metis Assume Sym_L Trans cut_same thin1 thin2)

subsection\<open>The congruence properties for @{term suc}, @{term pls} and @{term tms}\<close>

lemma suc_cong1: "{} \<turnstile> (t EQ t') IMP (suc t EQ suc t')"
proof -
  obtain v2::name and v3::name and v4::name
    where v2: "atom v2 \<sharp> (t,X1,X3,X4)"
      and v3: "atom v3 \<sharp> (t,t',X1,v2,X4)"
      and v4: "atom v4 \<sharp> (t,t',X1,v2,v3)"
    by (metis obtain_fresh)
  have "{} \<turnstile> (Var X1 EQ Var X2) IMP (suc (Var X1) EQ suc (Var X2))"
    by (metis syc_cong_ax_def equality_axioms_def insert_iff eql)
  hence "{} \<turnstile> (Var X1 EQ Var v2) IMP (suc (Var X1) EQ suc (Var v2))"
    by (drule_tac i=X2 and x="Var v2" in Subst) simp_all
  hence "{} \<turnstile> (t EQ Var v2) IMP (suc t EQ suc (Var v2))"
    using v2 v3 v4
    by (drule_tac i=X1 and x=t in Subst) simp_all
  hence "{} \<turnstile> (t EQ t') IMP (suc t EQ suc t')"
    using v2 v3 v4
    by (drule_tac i=v2 and x=t' in Subst) simp_all
  thus ?thesis
    using v4
    by (drule_tac i=v4 in Subst) simp_all
qed

lemma suc_cong: "\<lbrakk>H \<turnstile> t EQ t'\<rbrakk> \<Longrightarrow> H \<turnstile> suc t EQ suc t'"
  by (metis anti_deduction suc_cong1 cut1)

lemma pls_cong1: "{} \<turnstile> (t EQ t' AND u EQ u') IMP (pls t u EQ pls t' u')"
proof -
  obtain v2::name and v3::name and v4::name
    where v2: "atom v2 \<sharp> (t,X1,X3,X4)"
      and v3: "atom v3 \<sharp> (t,t',X1,v2,X4)"
      and v4: "atom v4 \<sharp> (t,t',u,X1,v2,v3)"
    by (metis obtain_fresh)
  have "{} \<turnstile> (Var X1 EQ Var X2 AND Var X3 EQ Var X4) IMP (pls (Var X1) (Var X3) EQ pls (Var X2) (Var X4))"
    by (metis pls_cong_ax_def equality_axioms_def insert_iff eql)
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var X3 EQ Var X4) IMP (pls (Var X1) (Var X3) EQ pls (Var v2) (Var X4))"
    by (drule_tac i=X2 and x="Var v2" in Subst) simp_all
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var v3 EQ Var X4) IMP (pls (Var X1) (Var v3) EQ pls (Var v2) (Var X4))"
    using v2
    by (drule_tac i=X3 and x="Var v3" in Subst) simp_all
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var v3 EQ Var v4) IMP (pls (Var X1) (Var v3) EQ pls (Var v2) (Var v4))"
    using v2 v3
    by (drule_tac i=X4 and x="Var v4" in Subst) simp_all
  hence "{} \<turnstile> (t EQ Var v2 AND Var v3 EQ Var v4) IMP (pls t (Var v3) EQ pls (Var v2) (Var v4))"
    using v2 v3 v4
    by (drule_tac i=X1 and x=t in Subst) simp_all
  hence "{} \<turnstile> (t EQ t' AND Var v3 EQ Var v4) IMP (pls t (Var v3) EQ pls t' (Var v4))"
    using v2 v3 v4
    by (drule_tac i=v2 and x=t' in Subst) simp_all
  hence "{} \<turnstile> (t EQ t' AND u EQ Var v4) IMP (pls t u EQ pls t' (Var v4))"
    using v3 v4
    by (drule_tac i=v3 and x=u in Subst) simp_all
  thus ?thesis
    using v4
    by (drule_tac i=v4 and x=u' in Subst) simp_all
qed

lemma pls_cong: "\<lbrakk>H \<turnstile> t EQ t'; H \<turnstile> u EQ u'\<rbrakk> \<Longrightarrow> H \<turnstile> pls t u EQ pls t' u'"
  by (metis cnj_I anti_deduction pls_cong1 cut1)

lemma tms_cong1: "{} \<turnstile> (t EQ t' AND u EQ u') IMP (tms t u EQ tms t' u')"
proof -
  obtain v2::name and v3::name and v4::name
    where v2: "atom v2 \<sharp> (t,X1,X3,X4)"
      and v3: "atom v3 \<sharp> (t,t',X1,v2,X4)"
      and v4: "atom v4 \<sharp> (t,t',u,X1,v2,v3)"
    by (metis obtain_fresh)
  have "{} \<turnstile> (Var X1 EQ Var X2 AND Var X3 EQ Var X4) IMP (tms (Var X1) (Var X3) EQ tms (Var X2) (Var X4))"
    by (metis tms_cong_ax_def equality_axioms_def insert_iff eql)
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var X3 EQ Var X4) IMP (tms (Var X1) (Var X3) EQ tms (Var v2) (Var X4))"
    by (drule_tac i=X2 and x="Var v2" in Subst) simp_all
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var v3 EQ Var X4) IMP (tms (Var X1) (Var v3) EQ tms (Var v2) (Var X4))"
    using v2
    by (drule_tac i=X3 and x="Var v3" in Subst) simp_all
  hence "{} \<turnstile> (Var X1 EQ Var v2 AND Var v3 EQ Var v4) IMP (tms (Var X1) (Var v3) EQ tms (Var v2) (Var v4))"
    using v2 v3
    by (drule_tac i=X4 and x="Var v4" in Subst) simp_all
  hence "{} \<turnstile> (t EQ Var v2 AND Var v3 EQ Var v4) IMP (tms t (Var v3) EQ tms (Var v2) (Var v4))"
    using v2 v3 v4
    by (drule_tac i=X1 and x=t in Subst) simp_all
  hence "{} \<turnstile> (t EQ t' AND Var v3 EQ Var v4) IMP (tms t (Var v3) EQ tms t' (Var v4))"
    using v2 v3 v4
    by (drule_tac i=v2 and x=t' in Subst) simp_all
  hence "{} \<turnstile> (t EQ t' AND u EQ Var v4) IMP (tms t u EQ tms t' (Var v4))"
    using v3 v4
    by (drule_tac i=v3 and x=u in Subst) simp_all
  thus ?thesis
    using v4
    by (drule_tac i=v4 and x=u' in Subst) simp_all
qed

lemma tms_cong: "\<lbrakk>H \<turnstile> t EQ t'; H \<turnstile> u EQ u'\<rbrakk> \<Longrightarrow> H \<turnstile> tms t u EQ tms t' u'"
  by (metis cnj_I anti_deduction tms_cong1 cut1)


subsection\<open>Substitution for eqlualities\<close>

lemma eql_subst_trm_Iff: "{t EQ u} \<turnstile> subst i t trm EQ subst i u trm"
  by (induct trm rule: trm.induct) (auto simp: suc_cong pls_cong tms_cong)

lemma eql_subst_fmla_Iff: "insert (t EQ u) H \<turnstile> A(i::=t) IFF A(i::=u)"
proof -
  have "{ t EQ u } \<turnstile> A(i::=t) IFF A(i::=u)"
    by (nominal_induct A avoiding: i t u rule: fmla.strong_induct)
       (auto simp: dsj_cong neg_cong exi_cong eql_cong eql_subst_trm_Iff)
  thus ?thesis
    by (metis Assume cut1)
qed

lemma Var_eql_subst_Iff: "insert (Var i EQ t) H \<turnstile> A(i::=t) IFF A"
  by (metis eql_subst_fmla_Iff Iff_sym subst_fmla_id)

lemma Var_eql_imp_subst_Iff: "H \<turnstile> Var i EQ t \<Longrightarrow> H \<turnstile> A(i::=t) IFF A"
  by (metis Var_eql_subst_Iff cut_same)

subsection\<open>Congruence rules for predicates\<close>

lemma P1_cong:
  fixes tms :: "trm list"
  assumes "\<And>i t x. atom i \<sharp> tms \<Longrightarrow> (P t)(i::=x) = P (subst i x t)" and "H \<turnstile> x EQ x'"
  shows "H \<turnstile> P x IFF P x'"
proof -
  obtain i::name where i: "atom i \<sharp> tms"
    by (metis obtain_fresh)
  have "insert (x EQ x') H  \<turnstile> (P (Var i))(i::=x) IFF (P(Var i))(i::=x')"
    by (rule eql_subst_fmla_Iff)
  thus ?thesis using assms i
    by (metis cut_same subst.simps(2))
qed

lemma P2_cong:
  fixes tms :: "trm list"
  assumes sub: "\<And>i t u x. atom i \<sharp> tms \<Longrightarrow> (P t u)(i::=x) = P (subst i x t) (subst i x u)"
      and eq:  "H \<turnstile> x EQ x'" "H \<turnstile> y EQ y'"
  shows "H \<turnstile> P x y IFF P x' y'"
proof -
  have yy': "{ y EQ y' } \<turnstile> P x' y IFF P x' y'"
    by (rule P1_cong [where tms="[y,x']@tms"]) (auto simp: fresh_Cons sub)
  have "{ x EQ x' } \<turnstile> P x y IFF P x' y"
    by (rule P1_cong [where tms="[y,x']@tms"]) (auto simp: fresh_Cons sub)
  hence "{x EQ x', y EQ y'} \<turnstile> P x y IFF P x' y'"
    by (metis Assume Iff_trans cut1 rotate2 yy')
  thus ?thesis
    by (metis cut2 eq)
 qed

lemma P3_cong:
  fixes tms :: "trm list"
  assumes sub: "\<And>i t u v x. atom i \<sharp> tms \<Longrightarrow>
                   (P t u v)(i::=x) = P (subst i x t) (subst i x u) (subst i x v)"
      and eq:  "H \<turnstile> x EQ x'" "H \<turnstile> y EQ y'" "H \<turnstile> z EQ z'"
  shows "H \<turnstile> P x y z IFF P x' y' z'"
proof -
  obtain i::name where i: "atom i \<sharp> (z,z',y,y',x,x')"
    by (metis obtain_fresh)
  have tl: "{ y EQ y', z EQ z' } \<turnstile> P x' y z IFF P x' y' z'"
    by (rule P2_cong [where tms="[z,z',y,y',x,x']@tms"]) (auto simp: fresh_Cons sub)
  have hd: "{ x EQ x' } \<turnstile> P x y z IFF P x' y z"
    by (rule P1_cong [where tms="[z,y,x']@tms"]) (auto simp: fresh_Cons sub)
  have "{x EQ x', y EQ y', z EQ z'} \<turnstile> P x y z IFF P x' y' z'"
    by (metis Assume thin1 hd [THEN cut1] tl Iff_trans)
  thus ?thesis
    by (rule cut3) (rule eq)+
qed

lemma P4_cong:
  fixes tms :: "trm list"
  assumes sub: "\<And>i t1 t2 t3 t4 x. atom i \<sharp> tms \<Longrightarrow>
                 (P t1 t2 t3 t4)(i::=x) = P (subst i x t1) (subst i x t2) (subst i x t3) (subst i x t4)"
      and eq:  "H \<turnstile> x1 EQ x1'" "H \<turnstile> x2 EQ x2'" "H \<turnstile> x3 EQ x3'" "H \<turnstile> x4 EQ x4'"
  shows "H \<turnstile> P x1 x2 x3 x4 IFF P x1' x2' x3' x4'"
proof -
  obtain i::name where i: "atom i \<sharp> (x4,x4',x3,x3',x2,x2',x1,x1')"
    by (metis obtain_fresh)
  have tl: "{ x2 EQ x2', x3 EQ x3', x4 EQ x4' } \<turnstile> P x1' x2 x3 x4 IFF P x1' x2' x3' x4'"
    by (rule P3_cong [where tms="[x4,x4',x3,x3',x2,x2',x1,x1']@tms"]) (auto simp: fresh_Cons sub)
  have hd: "{ x1 EQ x1' } \<turnstile> P x1 x2 x3 x4 IFF P x1' x2 x3 x4"
    by (auto simp: fresh_Cons sub intro!: P1_cong [where tms="[x4,x3,x2,x1']@tms"])
  have "{x1 EQ x1', x2 EQ x2', x3 EQ x3', x4 EQ x4'} \<turnstile> P x1 x2 x3 x4 IFF P x1' x2' x3' x4'"
    by (metis Assume thin1 hd [THEN cut1] tl Iff_trans)
  thus ?thesis
    by (rule cut4) (rule eq)+
qed



subsection\<open>The formula @{term fls}\<close>

lemma neg_I [intro!]: "insert A H \<turnstile> fls \<Longrightarrow> H \<turnstile> neg A"
  unfolding fls_def
  by (meson neg_D neg_I0 Refl)

lemma neg_E [intro!]: "H \<turnstile> A \<Longrightarrow> insert (neg A) H \<turnstile> fls"
  by (rule ContraProve)

declare neg_E [THEN rotate2, intro!]
declare neg_E [THEN rotate3, intro!]
declare neg_E [THEN rotate4, intro!]
declare neg_E [THEN rotate5, intro!]
declare neg_E [THEN rotate6, intro!]
declare neg_E [THEN rotate7, intro!]
declare neg_E [THEN rotate8, intro!]

lemma neg_imp_I [intro!]: "H \<turnstile> A \<Longrightarrow> insert B H \<turnstile> fls \<Longrightarrow> H \<turnstile> neg (A IMP B)"
  by (metis negneg_I neg_dsj_I neg_I)

lemma neg_imp_E [intro!]: "insert (neg B) (insert A H) \<turnstile> C \<Longrightarrow> insert (neg (A IMP B)) H \<turnstile> C"
apply (rule cut_same [where A=A])
 apply (metis Assume dsj_I1 negneg_D neg_mono)
apply (metis Swap imp_I rotate2 thin1)
done

declare neg_imp_E [THEN rotate2, intro!]
declare neg_imp_E [THEN rotate3, intro!]
declare neg_imp_E [THEN rotate4, intro!]
declare neg_imp_E [THEN rotate5, intro!]
declare neg_imp_E [THEN rotate6, intro!]
declare neg_imp_E [THEN rotate7, intro!]
declare neg_imp_E [THEN rotate8, intro!]

lemma fls_E [intro!]: "insert fls H \<turnstile> A"
  by (simp add: ContraProve fls_def)

declare fls_E [THEN rotate2, intro!]
declare fls_E [THEN rotate3, intro!]
declare fls_E [THEN rotate4, intro!]
declare fls_E [THEN rotate5, intro!]
declare fls_E [THEN rotate6, intro!]
declare fls_E [THEN rotate7, intro!]
declare fls_E [THEN rotate8, intro!]

lemma truth_provable: "H \<turnstile> (neg fls)"
  by (metis fls_E neg_I)

lemma exFalso: "H \<turnstile> fls \<Longrightarrow> H \<turnstile> A"
  by (metis neg_D truth_provable)


text\<open>Soundness of the provability relation\<close>

theorem nprv_sound: assumes "H \<turnstile> A" shows "(\<forall>B\<in>H. eval_fmla e B) \<Longrightarrow> eval_fmla e A"
using assms
proof (induct arbitrary: e)
  case (Hyp A H) thus ?case
    by auto
next
  case (Q H) thus ?case
     unfolding Q_axioms_def
     using not0_implies_Suc by fastforce
next
  case (Bool A H) thus ?case
    by (metis boolean_axioms_hold)
next
  case (eql A H) thus ?case
    by (metis equality_axioms_hold)
next
  case (Spec A H) thus ?case
    by (metis special_axioms_hold)
next
  case (MP H A B H') thus ?case
    by auto
next
  case (exiists H A B i e) thus ?case
    by auto (metis forget_eval_fmla)
qed

(*<*)
end
(*>*)
