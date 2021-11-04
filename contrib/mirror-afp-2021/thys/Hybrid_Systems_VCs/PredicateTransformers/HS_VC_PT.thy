(*  Title:       Verification components with predicate transformers
    Author:      Jonathan Julián Huerta y Munive, 2020
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

section \<open> Verification components with Predicate Transformers \<close>

text \<open> We use the categorical forward box operator @{text fb\<^sub>\<F>} to compute weakest liberal 
preconditions (wlps) of hybrid programs. Then we repeat the three methods for verifying 
correctness specifications of the continuous dynamics of a HS. \<close>

theory HS_VC_PT
  imports 
    "Transformer_Semantics.Kleisli_Quantaloid"
    "../HS_ODEs" 
                        
begin

no_notation bres (infixr "\<rightarrow>" 60)
        and dagger ("_\<^sup>\<dagger>" [101] 100)
        and "Relation.relcomp" (infixl ";" 75) 
        and eta ("\<eta>")
        and kcomp (infixl "\<circ>\<^sub>K" 75)

type_synonym 'a pred = "'a \<Rightarrow> bool"

notation eta ("skip")
     and kcomp (infixl ";" 75)
     and g_orbital ("(1x\<acute>=_ & _ on _ _ @ _)")


subsection \<open>Verification of regular programs\<close>

text \<open>Properties of the forward box operator. \<close>

lemma "fb\<^sub>\<F> F S = (\<Inter> \<circ> \<P> (- op\<^sub>K F)) (- S)"
  unfolding ffb_def map_dual_def dual_set_def klift_def by simp

lemma "fb\<^sub>\<F> F S = {s. F s \<subseteq> S}"
  by (auto simp: ffb_def kop_def klift_def map_dual_def dual_set_def f2r_def r2f_def)

lemma ffb_eq: "fb\<^sub>\<F> F S = {s. \<forall>s'. s' \<in> F s \<longrightarrow> s' \<in> S}"
  by (auto simp: ffb_def kop_def klift_def map_dual_def dual_set_def f2r_def r2f_def)

lemma ffb_iso: "P \<le> Q \<Longrightarrow> fb\<^sub>\<F> F P \<le> fb\<^sub>\<F> F Q"
  unfolding ffb_eq by auto

lemma ffb_invariants: 
  assumes "{s. I s} \<le> fb\<^sub>\<F> F {s. I s}" and "{s. J s} \<le> fb\<^sub>\<F> F {s. J s}"
  shows "{s. I s \<and> J s} \<le> fb\<^sub>\<F> F {s. I s \<and> J s}"
    and "{s. I s \<or> J s} \<le> fb\<^sub>\<F> F {s. I s \<or> J s}"
  using assms unfolding ffb_eq by auto

\<comment> \<open> Skip \<close>

lemma ffb_skip[simp]: "fb\<^sub>\<F> skip S = S"
  unfolding ffb_def by(simp add: kop_def klift_def map_dual_def)

\<comment> \<open> Tests \<close>

definition test :: "'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" ("(1\<questiondown>_?)")
  where "\<questiondown>P? = (\<lambda>s. {x. x = s \<and> P x})"

lemma ffb_test[simp]: "fb\<^sub>\<F> \<questiondown>P? Q = {s. P s \<longrightarrow> s \<in> Q}"
  unfolding ffb_eq test_def by simp

\<comment> \<open> Assignments \<close>

definition assign :: "'n \<Rightarrow> ('a^'n \<Rightarrow> 'a) \<Rightarrow> ('a^'n) \<Rightarrow> ('a^'n) set" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) = (\<lambda>s. {vec_upd s x (e s)})" 

lemma ffb_assign[simp]: "fb\<^sub>\<F> (x ::= e) Q = {s. (\<chi> j. ((($) s)(x := (e s))) j) \<in> Q}"
  unfolding vec_upd_def assign_def by (subst ffb_eq) simp

\<comment> \<open> Nondeterministic assignments \<close>

definition nondet_assign :: "'n \<Rightarrow> 'a^'n \<Rightarrow> ('a^'n) set" ("(2_ ::= ? )" [70] 61)
  where "(x ::= ?) = (\<lambda>s. {(vec_upd s x k)|k. True})"

lemma fbox_nondet_assign[simp]: "fb\<^sub>\<F> (x ::= ?) P = {s. \<forall>k. (\<chi> j. if j = x then k else s$j) \<in> P}"
  unfolding ffb_eq nondet_assign_def vec_upd_eq apply(simp add: fun_eq_iff, safe)
  by (erule_tac x="(\<chi> j. if j = x then k else _ $ j)" in allE, auto)

\<comment> \<open> Nondeterministic choice \<close>

lemma ffb_choice: "fb\<^sub>\<F> (\<lambda>s. F s \<union> G s) P = fb\<^sub>\<F> F P \<inter> fb\<^sub>\<F> G P"
  unfolding ffb_eq by auto

lemma le_ffb_choice_iff: "P \<subseteq> fb\<^sub>\<F> (\<lambda>s. F s \<union> G s) Q \<longleftrightarrow> P \<subseteq> fb\<^sub>\<F> F Q \<and> P \<subseteq> fb\<^sub>\<F> G Q"
  unfolding ffb_eq by auto

\<comment> \<open> Sequential composition \<close>

lemma ffb_kcomp[simp]: "fb\<^sub>\<F> (G ; F) P = fb\<^sub>\<F> G (fb\<^sub>\<F> F P)"
  unfolding ffb_eq by (auto simp: kcomp_def)

lemma hoare_kcomp:
  assumes "P \<le> fb\<^sub>\<F> F R" "R \<le> fb\<^sub>\<F> G Q"
  shows "P \<le> fb\<^sub>\<F> (F ; G) Q"
  apply(subst ffb_kcomp) 
  by (rule order.trans[OF assms(1)]) (rule ffb_iso[OF assms(2)])

\<comment> \<open> Conditional statement \<close>

definition ifthenelse :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set)"
  ("IF _ THEN _ ELSE _" [64,64,64] 63) where 
  "IF P THEN X ELSE Y = (\<lambda> x. if P x then X x else Y x)"

lemma ffb_if_then_else[simp]:
  "fb\<^sub>\<F> (IF T THEN X ELSE Y) Q = {s. T s \<longrightarrow> s \<in> fb\<^sub>\<F> X Q} \<inter> {s. \<not> T s \<longrightarrow> s \<in> fb\<^sub>\<F> Y Q}"
  unfolding ffb_eq ifthenelse_def by auto

lemma hoare_if_then_else:
  assumes "P \<inter> {s. T s} \<le> fb\<^sub>\<F> X Q"
    and "P \<inter> {s. \<not> T s} \<le> fb\<^sub>\<F> Y Q"
  shows "P \<le> fb\<^sub>\<F> (IF T THEN X ELSE Y) Q"
  using assms 
  apply(subst ffb_eq)
  apply(subst (asm) ffb_eq)+
  unfolding ifthenelse_def by auto

\<comment> \<open> Finite iteration \<close>

lemma kpower_inv: "I \<le> {s. \<forall>y. y \<in> F s \<longrightarrow> y \<in> I} \<Longrightarrow> I \<le> {s. \<forall>y. y \<in> (kpower F n s) \<longrightarrow> y \<in> I}"
  apply(induct n, simp)
  apply simp
  by(auto simp: kcomp_prop) 

lemma kstar_inv: "I \<le> fb\<^sub>\<F> F I \<Longrightarrow> I \<subseteq> fb\<^sub>\<F> (kstar F) I"
  unfolding kstar_def ffb_eq apply clarsimp
  using kpower_inv by blast

lemma ffb_kstarI:
  assumes "P \<le> I" and "I \<le> Q" and "I \<le> fb\<^sub>\<F> F I"
  shows "P \<le> fb\<^sub>\<F> (kstar F) Q"
proof-
  have "I \<subseteq> fb\<^sub>\<F> (kstar F) I"
    using assms(3) kstar_inv by blast
  hence "P \<le> fb\<^sub>\<F> (kstar F) I"
    using assms(1) by auto
  also have "fb\<^sub>\<F> (kstar F) I \<le> fb\<^sub>\<F> (kstar F) Q"
    by (rule ffb_iso[OF assms(2)])
  finally show ?thesis .
qed

definition loopi :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> 'a set)" ("LOOP _ INV _ " [64,64] 63)
  where "LOOP F INV I \<equiv> (kstar F)"

lemma change_loopI: "LOOP X INV G = LOOP X INV I"
  unfolding loopi_def by simp

lemma ffb_loopI: "P \<le> {s. I s}  \<Longrightarrow> {s. I s} \<le> Q \<Longrightarrow> {s. I s} \<le> fb\<^sub>\<F> F {s. I s} \<Longrightarrow> P \<le> fb\<^sub>\<F> (LOOP F INV I) Q"
  unfolding loopi_def using ffb_kstarI[of "P"] by simp

lemma ffb_loopI_break: 
  "P \<le> fb\<^sub>\<F> Y {s. I s} \<Longrightarrow> {s. I s} \<le> fb\<^sub>\<F> X {s. I s} \<Longrightarrow> {s. I s} \<le> Q \<Longrightarrow> P \<le> fb\<^sub>\<F> (Y ; (LOOP X INV I)) Q"
  by (rule hoare_kcomp, force) (rule ffb_loopI, auto)


subsection \<open>Verification of hybrid programs\<close>

text \<open>Verification by providing evolution\<close>

definition g_evol :: "(('a::ord) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b pred \<Rightarrow> ('b \<Rightarrow> 'a set) \<Rightarrow> ('b \<Rightarrow> 'b set)" ("EVOL")
  where "EVOL \<phi> G U = (\<lambda>s. g_orbit (\<lambda>t. \<phi> t s) G (U s))"

lemma fbox_g_evol[simp]: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "fb\<^sub>\<F> (EVOL \<phi> G U) Q = {s. (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> (\<phi> t s) \<in> Q)}"
  unfolding g_evol_def g_orbit_eq ffb_eq by auto

text \<open>Verification by providing solutions\<close>

lemma ffb_g_orbital: "fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) Q = 
  {s. \<forall>X\<in>Sols f U S t\<^sub>0 s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (X \<tau>)) \<longrightarrow> (X t) \<in> Q}"
  unfolding ffb_eq g_orbital_eq by (auto simp: fun_eq_iff)

context local_flow
begin

lemma ffb_g_ode_subset:
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "fb\<^sub>\<F> (x\<acute>= (\<lambda>t. f) & G on U S @ 0) Q = 
  {s. s \<in> S \<longrightarrow> (\<forall>t\<in>(U s). (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> (\<phi> t s) \<in> Q)}"
  apply(unfold ffb_g_orbital set_eq_iff)
  apply(clarify, rule iffI; clarify)
   apply(force simp: in_ivp_sols assms)
  apply(frule ivp_solsD(2), frule ivp_solsD(3), frule ivp_solsD(4))
  apply(subgoal_tac "\<forall>\<tau>\<in>down (U x) t. X \<tau> = \<phi> \<tau> x")
   apply(clarsimp, fastforce, rule ballI)
  apply(rule ivp_unique_solution[OF _ _ _ _ _ in_ivp_sols])
  using assms by auto

lemma ffb_g_ode: "fb\<^sub>\<F> (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. T) S @ 0) Q = 
  {s. s \<in> S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> (\<phi> t s) \<in> Q)}" (is "_ = ?wlp")
  by (subst ffb_g_ode_subset, simp_all add: init_time interval_time)

lemma ffb_g_ode_ivl: "t \<ge> 0 \<Longrightarrow> t \<in> T \<Longrightarrow> fb\<^sub>\<F> (x\<acute>=(\<lambda>t. f) & G on (\<lambda>s. {0..t}) S @ 0) Q = 
  {s. s \<in> S \<longrightarrow> (\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> (\<phi> t s) \<in> Q)}"
  apply(subst ffb_g_ode_subset, simp_all add: subintervalI init_time real_Icc_closed_segment)
  by (auto simp: closed_segment_eq_real_ivl)

lemma ffb_orbit: "fb\<^sub>\<F> \<gamma>\<^sup>\<phi> Q = {s. s \<in> S \<longrightarrow> (\<forall> t \<in> T. \<phi> t s \<in> Q)}"
  unfolding orbit_def ffb_g_ode by simp

end

text \<open> Verification with differential invariants \<close>

definition g_ode_inv :: "(real \<Rightarrow> ('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> real set) \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> 'a set)" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on U S @ t\<^sub>0 DINV I) = (x\<acute>= f & G on U S @ t\<^sub>0)"

lemma ffb_g_orbital_guard: 
  assumes "H = (\<lambda>s. G s \<and> Q s)"
  shows "fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) {s. Q s} = fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) {s. H s}"
  unfolding ffb_g_orbital using assms by auto

lemma ffb_g_orbital_inv:
  assumes "P \<le> I" and "I \<le> fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) I" and "I \<le> Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) Q"
  using assms(1) 
  apply(rule order.trans)
  using assms(2) 
  apply(rule order.trans)
  by (rule ffb_iso[OF assms(3)])

lemma ffb_diff_inv[simp]: 
  "({s. I s} \<le> fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) {s. I s}) = diff_invariant I f U S t\<^sub>0 G"
  by (auto simp: diff_invariant_def ivp_sols_def ffb_eq g_orbital_eq)

lemma bdf_diff_inv:
  "diff_invariant I f U S t\<^sub>0 G = (bd\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) {s. I s} \<le> {s. I s})"
  unfolding ffb_fbd_galois_var by (auto simp: diff_invariant_def ivp_sols_def ffb_eq g_orbital_eq)

lemma diff_inv_guard_ignore:
  assumes "{s. I s} \<le> fb\<^sub>\<F> (x\<acute>= f & (\<lambda>s. True) on U S @ t\<^sub>0) {s. I s}"
  shows "{s. I s} \<le> fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) {s. I s}"
  using assms unfolding ffb_diff_inv diff_invariant_eq image_le_pred by auto

context local_flow
begin

lemma ffb_diff_inv_eq: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "diff_invariant I (\<lambda>t. f) U S 0 (\<lambda>s. True) = 
  ({s. s \<in> S \<longrightarrow> I s} = fb\<^sub>\<F> (x\<acute>= (\<lambda>t. f) & (\<lambda>s. True) on U S @ 0) {s. s \<in> S \<longrightarrow> I s})"
 unfolding ffb_diff_inv[symmetric] 
  apply(subst ffb_g_ode_subset[OF assms], simp)+
  apply(clarsimp simp: set_eq_iff, safe, force)
   apply(erule_tac x=0 in ballE)
  using init_time in_domain ivp(2) assms apply(force, force)
  apply(erule_tac x=x in allE, clarsimp, erule_tac x=t in ballE)
  using in_domain ivp(2) assms by force+

lemma diff_inv_eq_inv_set:
  "diff_invariant I (\<lambda>t. f) (\<lambda>s. T) S 0 (\<lambda>s. True) = (\<forall>s. I s \<longrightarrow> \<gamma>\<^sup>\<phi> s \<subseteq> {s. I s})"
  unfolding diff_inv_eq_inv_set orbit_def by simp

end

lemma ffb_g_odei: "P \<le> {s. I s} \<Longrightarrow> {s. I s} \<le> fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) {s. I s} \<Longrightarrow> 
  {s. I s \<and> G s} \<le> Q \<Longrightarrow> P \<le> fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0 DINV I) Q"
  unfolding g_ode_inv_def 
  apply(rule_tac b="fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) {s. I s}" in order.trans)
   apply(rule_tac I="{s. I s}" in ffb_g_orbital_inv, simp_all)
  apply(subst ffb_g_orbital_guard, simp)
  by (rule ffb_iso, force)

subsection \<open> Derivation of the rules of dL \<close>

text\<open> We derive domain specific rules of differential dynamic logic (dL). First we present a 
generalised version, then we show the rules as instances of the general ones.\<close>

abbreviation g_dl_orbit ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" ("(1x\<acute>=_ & _)") 
  where "(x\<acute>=f & G) \<equiv> (x\<acute>=(\<lambda>t. f) & G on (\<lambda>s. {t. t \<ge> 0}) UNIV @ 0)"

abbreviation g_dl_ode_inv ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" ("(1x\<acute>=_ & _ DINV _)") 
  where "(x\<acute>=f & G DINV I) \<equiv> (x\<acute>=(\<lambda>t. f) & G on (\<lambda>s. {t. t \<ge> 0}) UNIV @ 0 DINV I)"

lemma diff_solve_axiom1: 
  assumes "local_flow f UNIV UNIV \<phi>"
  shows "fb\<^sub>\<F> (x\<acute>= f & G) Q = 
  {s. \<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> (\<phi> t s) \<in> Q}"
  by (subst local_flow.ffb_g_ode_subset[OF assms], auto)

lemma diff_solve_axiom2: 
  fixes c::"'a::{heine_borel, banach}"
  shows "fb\<^sub>\<F> (x\<acute>=(\<lambda>s. c) & G) Q = 
  {s. \<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (s + \<tau> *\<^sub>R c)) \<longrightarrow> (s + t *\<^sub>R c) \<in> Q}"
  apply(subst local_flow.ffb_g_ode_subset[where \<phi>="(\<lambda>t s. s + t *\<^sub>R c)" and T=UNIV])
  by (rule line_is_local_flow, auto)

lemma diff_solve_rule:
  assumes "local_flow f UNIV UNIV \<phi>"
    and "\<forall>s. s \<in> P \<longrightarrow> (\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> (\<phi> t s) \<in> Q)"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>= f & G) Q"
  using assms by(subst local_flow.ffb_g_ode_subset[OF assms(1)]) auto

lemma diff_weak_axiom1: "s \<in> (fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) {s. G s})"
  unfolding ffb_eq g_orbital_eq by auto

lemma diff_weak_axiom2: "fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) Q = fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) {s. G s \<longrightarrow> s \<in> Q}"
  unfolding ffb_g_orbital image_def by force
    
lemma diff_weak_rule: "{s. G s} \<le> Q \<Longrightarrow> P \<le> fb\<^sub>\<F> (x\<acute>= f & G on T S @ t\<^sub>0) Q"
  by(auto intro: g_orbitalD simp: le_fun_def g_orbital_eq ffb_eq)

lemma ffb_g_orbital_eq_univD:
  assumes "fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) {s. C s} = UNIV" 
    and "\<forall>\<tau>\<in>(down (U s) t). x \<tau> \<in> (x\<acute>= f & G on U S @ t\<^sub>0) s"
  shows "\<forall>\<tau>\<in>(down (U s) t). C (x \<tau>)"
proof
  fix \<tau> assume "\<tau> \<in> (down (U s) t)"
  hence "x \<tau> \<in> (x\<acute>= f & G on U S @ t\<^sub>0) s" 
    using assms(2) by blast
  also have "\<forall>y. y \<in> (x\<acute>= f & G on U S @ t\<^sub>0) s \<longrightarrow> C y" 
    using assms(1) unfolding ffb_eq by fastforce
  ultimately show "C (x \<tau>)" by blast
qed

lemma diff_cut_axiom:
  assumes "fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) {s. C s} = UNIV"
  shows "fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) Q = fb\<^sub>\<F> (x\<acute>= f & (\<lambda>s. G s \<and> C s) on U S @ t\<^sub>0) Q"
proof(rule_tac f="\<lambda> x. fb\<^sub>\<F> x Q" in HOL.arg_cong, rule ext, rule subset_antisym)
  fix s 
  {fix s' assume "s' \<in> (x\<acute>= f & G on U S @ t\<^sub>0) s"
    then obtain \<tau>::real and X where x_ivp: "X \<in> Sols f U S t\<^sub>0 s" 
      and "X \<tau> = s'" and "\<tau> \<in> (U s)" and guard_x:"\<P> X (down (U s) \<tau>) \<subseteq> {s. G s}"
      using g_orbitalD[of s' "f" G _ S t\<^sub>0 s]  by blast
    have "\<forall>t\<in>(down (U s) \<tau>). \<P> X (down (U s) t) \<subseteq> {s. G s}"
      using guard_x by (force simp: image_def)
    also have "\<forall>t\<in>(down (U s) \<tau>). t \<in> (U s)"
      using \<open>\<tau> \<in> (U s)\<close> closed_segment_subset_interval by auto
    ultimately have "\<forall>t\<in>(down (U s) \<tau>). X t \<in> (x\<acute>= f & G on U S @ t\<^sub>0) s"
      using g_orbitalI[OF x_ivp] by (metis (mono_tags, lifting))
    hence "\<forall>t\<in>(down (U s) \<tau>). C (X t)" 
      using assms unfolding ffb_eq by fastforce
    hence "s' \<in> (x\<acute>= f & (\<lambda>s. G s \<and> C s) on U S @ t\<^sub>0) s"
      using g_orbitalI[OF x_ivp \<open>\<tau> \<in> (U s)\<close>] guard_x \<open>X \<tau> = s'\<close> 
      unfolding image_le_pred by fastforce}
  thus "(x\<acute>= f & G on U S @ t\<^sub>0) s \<subseteq> (x\<acute>= f & (\<lambda>s. G s \<and> C s) on U S @ t\<^sub>0) s"
    by blast
next show "\<And>s. (x\<acute>= f & (\<lambda>s. G s \<and> C s) on U S @ t\<^sub>0) s \<subseteq> (x\<acute>= f & G on U S @ t\<^sub>0) s" 
    by (auto simp: g_orbital_eq)
qed

lemma diff_cut_rule:
  assumes ffb_C: "P \<le> fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) {s. C s}"
    and ffb_Q: "P \<le> fb\<^sub>\<F> (x\<acute>= f & (\<lambda>s. G s \<and> C s) on U S @ t\<^sub>0) Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) Q"
proof(subst ffb_eq, subst g_orbital_eq, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s assume "s \<in> P" and "t \<in> (U s)"
    and x_ivp:"X \<in> Sols f U S t\<^sub>0 s" 
    and guard_x:"\<forall>\<tau>. \<tau> \<in> (U s) \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)"
  have "\<forall>\<tau>\<in>(down (U s) t). X \<tau> \<in> (x\<acute>= f & G on U S @ t\<^sub>0) s"
    using g_orbitalI[OF x_ivp] guard_x unfolding image_le_pred by auto
  hence "\<forall>\<tau>\<in>(down (U s) t). C (X \<tau>)" 
    using ffb_C \<open>s \<in> P\<close> by (subst (asm) ffb_eq, auto)
  hence "X t \<in> (x\<acute>= f & (\<lambda>s. G s \<and> C s) on U S @ t\<^sub>0) s"
    using guard_x \<open>t \<in> (U s)\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "(X t) \<in> Q"
    using \<open>s \<in> P\<close> ffb_Q by (subst (asm) ffb_eq) auto
qed

lemma diff_inv_axiom1:
  assumes "G s \<longrightarrow> I s" and "diff_invariant I (\<lambda>t. f) (\<lambda>s. {t. t \<ge> 0}) UNIV 0 G"
  shows "s \<in> (fb\<^sub>\<F> (x\<acute>= f & G) {s. I s})"
  using assms unfolding ffb_g_orbital diff_invariant_eq apply clarsimp
  by (erule_tac x=s in allE, frule ivp_solsD(2), clarsimp)

lemma diff_inv_axiom2:
  assumes "picard_lindeloef (\<lambda>t. f) UNIV UNIV 0"
    and "\<And>s. {t::real. t \<ge> 0} \<subseteq> picard_lindeloef.ex_ivl (\<lambda>t. f) UNIV UNIV 0 s"
    and "diff_invariant I (\<lambda>t. f) (\<lambda>s. {t::real. t \<ge> 0}) UNIV 0 G"
  shows "fb\<^sub>\<F> (x\<acute>= f & G) {s. I s} = fb\<^sub>\<F> (\<lambda>s. {x. s = x \<and> G s}) {s. I s}"
proof(unfold ffb_g_orbital, subst ffb_eq, clarsimp simp: set_eq_iff)
  fix s
  let "?ex_ivl s" = "picard_lindeloef.ex_ivl (\<lambda>t. f) UNIV UNIV 0 s"
  let "?lhs s" = 
    "\<forall>X\<in>Sols (\<lambda>t. f) (\<lambda>s. {t. t \<ge> 0}) UNIV 0 s. \<forall>t\<ge>0. (\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)) \<longrightarrow> I (X t)"
  obtain X where xivp1: "X \<in> Sols (\<lambda>t. f) (\<lambda>s. ?ex_ivl s) UNIV 0 s"
    using picard_lindeloef.flow_in_ivp_sols_ex_ivl[OF assms(1)] by auto
  have xivp2: "X \<in> Sols (\<lambda>t. f) (\<lambda>s. Collect ((\<le>) 0)) UNIV 0 s"
    by (rule in_ivp_sols_subset[OF _ _ xivp1], simp_all add: assms(2))
  hence shyp: "X 0 = s"
    using ivp_solsD by auto
  have dinv: "\<forall>s. I s \<longrightarrow> ?lhs s"
    using assms(3) unfolding diff_invariant_eq by auto
  {assume "?lhs s" and "G s"
    hence "I s"
      by (erule_tac x=X in ballE, erule_tac x=0 in allE, auto simp: shyp xivp2)}
  hence "?lhs s \<longrightarrow> (G s \<longrightarrow> I s)" 
    by blast
  moreover
  {assume "G s \<longrightarrow> I s"
    hence "?lhs s"
      apply(clarify, subgoal_tac "\<forall>\<tau>. 0 \<le> \<tau> \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)")
       apply(erule_tac x=0 in allE, frule ivp_solsD(2), simp)
      using dinv by blast+}
  ultimately show "?lhs s = (G s \<longrightarrow> I s)"
    by blast
qed

lemma diff_inv_rule:
  assumes "P \<le> {s. I s}" and "diff_invariant I f U S t\<^sub>0 G" and "{s. I s} \<le> Q"
  shows "P \<le> fb\<^sub>\<F> (x\<acute>= f & G on U S @ t\<^sub>0) Q"
  apply(rule ffb_g_orbital_inv[OF assms(1) _ assms(3)])
  unfolding ffb_diff_inv using assms(2) .

end