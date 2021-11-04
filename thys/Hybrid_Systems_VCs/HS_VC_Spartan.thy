(*  Title:       Verification components for hybrid systems 
    Author:      Jonathan Julián Huerta y Munive, 2020
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

section \<open> Verification components for hybrid systems \<close>

text \<open> A light-weight version of the verification components. We define the forward box 
operator to compute weakest liberal preconditions (wlps) of hybrid programs. Then we 
introduce three methods for verifying correctness specifications of the continuous 
dynamics of a HS. \<close>

theory HS_VC_Spartan
  imports HS_ODEs
                        
begin

type_synonym 'a pred = "'a \<Rightarrow> bool"

no_notation Transitive_Closure.rtrancl ("(_\<^sup>*)" [1000] 999)

notation Union ("\<mu>")
     and g_orbital ("(1x\<acute>=_ & _ on _ _ @ _)")


subsection \<open>Verification of regular programs\<close>

text \<open> Lemmas for verification condition generation \<close>

definition fbox :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'b pred \<Rightarrow> 'a pred" ("|_] _" [61,81] 82)
  where "|F] P = (\<lambda>s. (\<forall>s'. s' \<in> F s \<longrightarrow> P s'))"

lemma fbox_iso: "P \<le> Q \<Longrightarrow> |F] P \<le> |F] Q"
  unfolding fbox_def by auto

lemma fbox_anti: "\<forall>s. F\<^sub>1 s \<subseteq> F\<^sub>2 s \<Longrightarrow> |F\<^sub>2] P \<le> |F\<^sub>1] P"
  unfolding fbox_def by auto

lemma fbox_invariants: 
  assumes "I \<le> |F] I" and "J \<le> |F] J"
  shows "(\<lambda>s. I s \<and> J s) \<le> |F] (\<lambda>s. I s \<and> J s)"
    and "(\<lambda>s. I s \<or> J s) \<le> |F] (\<lambda>s. I s \<or> J s)"
  using assms unfolding fbox_def by auto

\<comment> \<open> Skip \<close>

abbreviation "skip \<equiv> (\<lambda>s. {s})"

lemma fbox_eta[simp]: "fbox skip P = P"
  unfolding fbox_def by simp

\<comment> \<open> Tests \<close>

definition test :: "'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" ("(1\<questiondown>_?)")
  where "\<questiondown>P? = (\<lambda>s. {x. x = s \<and> P x})"

lemma fbox_test[simp]: "(\<lambda>s. ( |\<questiondown>P?] Q) s) = (\<lambda>s. P s \<longrightarrow> Q s)"
  unfolding fbox_def test_def by simp

\<comment> \<open> Assignments \<close>

definition vec_upd :: "'a^'n \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> 'a^'n"
  where "vec_upd s i a = (\<chi> j. ((($) s)(i := a)) j)"

lemma vec_upd_eq: "vec_upd s i a = (\<chi> j. if j = i then a else s$j)"
  by (simp add: vec_upd_def)

definition assign :: "'n \<Rightarrow> ('a^'n \<Rightarrow> 'a) \<Rightarrow> 'a^'n \<Rightarrow> ('a^'n) set" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) = (\<lambda>s. {vec_upd s x (e s)})" 

lemma fbox_assign[simp]: "|x ::= e] Q = (\<lambda>s. Q (\<chi> j. ((($) s)(x := (e s))) j))"
  unfolding vec_upd_def assign_def by (subst fbox_def) simp

\<comment> \<open> Nondeterministic assignments \<close>

definition nondet_assign :: "'n \<Rightarrow> 'a^'n \<Rightarrow> ('a^'n) set" ("(2_ ::= ? )" [70] 61)
  where "(x ::= ?) = (\<lambda>s. {(vec_upd s x k)|k. True})"

lemma fbox_nondet_assign[simp]: "|x ::= ?] P = (\<lambda>s. \<forall>k. P (\<chi> j. if j = x then k else s$j))"
  unfolding fbox_def nondet_assign_def vec_upd_eq apply(simp add: fun_eq_iff, safe)
  by (erule_tac x="(\<chi> j. if j = x then k else _ $ j)" in allE, auto)

\<comment> \<open> Nondeterministic choice \<close>

lemma fbox_choice: "|(\<lambda>s. F s \<union> G s)] P = (\<lambda>s. ( |F] P) s \<and> ( |G] P) s)"
  unfolding fbox_def by auto

lemma le_fbox_choice_iff: "P \<le> |(\<lambda>s. F s \<union> G s)] Q \<longleftrightarrow> P \<le> |F] Q \<and> P \<le> |G] Q"
  unfolding fbox_def by auto

\<comment> \<open> Sequential composition \<close>

definition kcomp :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('b \<Rightarrow> 'c set) \<Rightarrow> ('a  \<Rightarrow> 'c set)" (infixl ";" 75) where
  "F ; G = \<mu> \<circ> \<P> G \<circ> F"

lemma kcomp_eq: "(f ; g) x = \<Union> {g y |y. y \<in> f x}"
  unfolding kcomp_def image_def by auto

lemma fbox_kcomp[simp]: "|G ; F] P = |G] |F] P"
  unfolding fbox_def kcomp_def by auto

lemma hoare_kcomp:
  assumes "P \<le> |G] R" "R \<le> |F] Q"
  shows "P \<le> |G ; F] Q"
  apply(subst fbox_kcomp) 
  by (rule order.trans[OF assms(1)]) (rule fbox_iso[OF assms(2)])

\<comment> \<open> Conditional statement \<close>

definition ifthenelse :: "'a pred \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set)"
  ("IF _ THEN _ ELSE _" [64,64,64] 63) where 
  "IF P THEN X ELSE Y \<equiv> (\<lambda>s. if P s then X s else Y s)"

lemma fbox_if_then_else[simp]:
  "|IF T THEN X ELSE Y] Q = (\<lambda>s. (T s \<longrightarrow> ( |X] Q) s) \<and> (\<not> T s \<longrightarrow> ( |Y] Q) s))"
  unfolding fbox_def ifthenelse_def by auto

lemma hoare_if_then_else:
  assumes "(\<lambda>s. P s \<and> T s) \<le> |X] Q"
    and "(\<lambda>s. P s \<and> \<not> T s) \<le> |Y] Q"
  shows "P \<le> |IF T THEN X ELSE Y] Q"
  using assms unfolding fbox_def ifthenelse_def by auto

\<comment> \<open> Finite iteration \<close>

definition kpower :: "('a \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a set)" 
  where "kpower f n = (\<lambda>s. ((;) f ^^ n) skip s)"

lemma kpower_base:
  shows "kpower f 0 s = {s}" and "kpower f (Suc 0) s = f s"
  unfolding kpower_def by(auto simp: kcomp_eq)

lemma kpower_simp: "kpower f (Suc n) s = (f ; kpower f n) s"
  unfolding kcomp_eq 
  apply(induct n)
  unfolding kpower_base 
   apply(force simp: subset_antisym)
  unfolding kpower_def kcomp_eq by simp

definition kleene_star :: "('a \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> 'a set)" ("(_\<^sup>*)" [1000] 999)
  where "(f\<^sup>*) s = \<Union> {kpower f n s |n. n \<in> UNIV}"

lemma kpower_inv: 
  fixes F :: "'a \<Rightarrow> 'a set"
  assumes "\<forall>s. I s \<longrightarrow> (\<forall>s'. s' \<in> F s \<longrightarrow> I s')" 
  shows "\<forall>s. I s \<longrightarrow> (\<forall>s'. s' \<in> (kpower F n s) \<longrightarrow> I s')"
  apply(clarsimp, induct n)
  unfolding kpower_base kpower_simp 
   apply(simp_all add: kcomp_eq, clarsimp) 
  apply(subgoal_tac "I y", simp)
  using assms by blast

lemma kstar_inv: "I \<le> |F] I \<Longrightarrow> I \<le> |F\<^sup>*] I"
  unfolding kleene_star_def fbox_def 
  apply clarsimp
  apply(unfold le_fun_def, subgoal_tac "\<forall>x. I x \<longrightarrow> (\<forall>s'. s' \<in> F x \<longrightarrow> I s')")
  using kpower_inv[of I F] by blast simp

lemma fbox_kstarI:
  assumes "P \<le> I" and "I \<le> Q" and "I \<le> |F] I" 
  shows "P \<le> |F\<^sup>*] Q"
proof-
  have "I \<le> |F\<^sup>*] I"
    using assms(3) kstar_inv by blast
  hence "P \<le> |F\<^sup>*] I"
    using assms(1) by auto
  also have "|F\<^sup>*] I \<le> |F\<^sup>*] Q"
    by (rule fbox_iso[OF assms(2)])
  finally show ?thesis .
qed

definition loopi :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> 'a set)" ("LOOP _ INV _ " [64,64] 63)
  where "LOOP F INV I \<equiv> (F\<^sup>*)"

lemma change_loopI: "LOOP X INV G = LOOP X INV I"
  unfolding loopi_def by simp

lemma fbox_loopI: "P \<le> I \<Longrightarrow> I \<le> Q \<Longrightarrow> I \<le> |F] I \<Longrightarrow> P \<le> |LOOP F INV I] Q"
  unfolding loopi_def using fbox_kstarI[of "P"] by simp

lemma wp_loopI_break: 
  "P \<le> |Y] I \<Longrightarrow> I \<le> |X] I \<Longrightarrow> I \<le> Q \<Longrightarrow> P \<le> |Y ; (LOOP X INV I)] Q"
  by (rule hoare_kcomp, force) (rule fbox_loopI, auto)


subsection \<open> Verification of hybrid programs \<close>

text \<open> Verification by providing evolution \<close>

definition g_evol :: "(('a::ord) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b pred \<Rightarrow> ('b \<Rightarrow> 'a set) \<Rightarrow> ('b \<Rightarrow> 'b set)" ("EVOL")
  where "EVOL \<phi> G U = (\<lambda>s. g_orbit (\<lambda>t. \<phi> t s) G (U s))"

lemma fbox_g_evol[simp]: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "|EVOL \<phi> G U] Q = (\<lambda>s. (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  unfolding g_evol_def g_orbit_eq fbox_def by auto

text \<open> Verification by providing solutions \<close>

lemma fbox_g_orbital: "|x\<acute>=f & G on U S @ t\<^sub>0] Q = 
  (\<lambda>s. \<forall>X\<in>Sols f U S t\<^sub>0 s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (X \<tau>)) \<longrightarrow> Q (X t))"
  unfolding fbox_def g_orbital_eq by (auto simp: fun_eq_iff)

context local_flow
begin

lemma fbox_g_ode_subset:
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "|x\<acute>= (\<lambda>t. f) & G on U S @ 0] Q = 
  (\<lambda> s. s \<in> S \<longrightarrow> (\<forall>t\<in>(U s). (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  apply(unfold fbox_g_orbital fun_eq_iff)
  apply(clarify, rule iffI; clarify)
   apply(force simp: in_ivp_sols assms)
  apply(frule ivp_solsD(2), frule ivp_solsD(3), frule ivp_solsD(4))
  apply(subgoal_tac "\<forall>\<tau>\<in>down (U x) t. X \<tau> = \<phi> \<tau> x")
   apply(clarsimp, fastforce, rule ballI)
  apply(rule ivp_unique_solution[OF _ _ _ _ _ in_ivp_sols])
  using assms by auto
                         
lemma fbox_g_ode: "|x\<acute>=(\<lambda>t. f) & G on (\<lambda>s. T) S @ 0] Q = 
  (\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  by (subst fbox_g_ode_subset, simp_all add: init_time interval_time)

lemma fbox_g_ode_ivl: "t \<ge> 0 \<Longrightarrow> t \<in> T \<Longrightarrow> |x\<acute>=(\<lambda>t. f) & G on (\<lambda>s. {0..t}) S @ 0] Q = 
  (\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  apply(subst fbox_g_ode_subset, simp_all add: subintervalI init_time real_Icc_closed_segment)
  by (auto simp: closed_segment_eq_real_ivl)

lemma fbox_orbit: "|\<gamma>\<^sup>\<phi>] Q = (\<lambda>s. s \<in> S \<longrightarrow> (\<forall> t \<in> T. Q (\<phi> t s)))"
  unfolding orbit_def fbox_g_ode by simp

end

text \<open> Verification with differential invariants \<close>

definition g_ode_inv :: "(real \<Rightarrow> ('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> real set) \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> 'a set)" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on U S @ t\<^sub>0 DINV I) = (x\<acute>= f & G on U S @ t\<^sub>0)"

lemma fbox_g_orbital_guard: 
  assumes "H = (\<lambda>s. G s \<and> Q s)"
  shows "|x\<acute>=f & G on U S @ t\<^sub>0] Q = |x\<acute>=f & G on U S @ t\<^sub>0] H "
  unfolding fbox_g_orbital using assms by auto

lemma fbox_g_orbital_inv:
  assumes "P \<le> I" and "I \<le> |x\<acute>=f & G on U S @ t\<^sub>0] I" and "I \<le> Q"
  shows "P \<le> |x\<acute>=f & G on U S @ t\<^sub>0] Q"
  using assms(1) 
  apply(rule order.trans)
  using assms(2) 
  apply(rule order.trans)
  by (rule fbox_iso[OF assms(3)])

lemma fbox_diff_inv[simp]: 
  "(I \<le> |x\<acute>=f & G on U S @ t\<^sub>0] I) = diff_invariant I f U S t\<^sub>0 G"
  by (auto simp: diff_invariant_def ivp_sols_def fbox_def g_orbital_eq)

lemma diff_inv_guard_ignore:
  assumes "I \<le> |x\<acute>= f & (\<lambda>s. True) on U S @ t\<^sub>0] I"
  shows "I \<le> |x\<acute>= f & G on U S @ t\<^sub>0] I"
  using assms unfolding fbox_diff_inv diff_invariant_eq image_le_pred by auto

context local_flow
begin

lemma fbox_diff_inv_eq: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "diff_invariant I (\<lambda>t. f) U S 0 (\<lambda>s. True) = 
  ((\<lambda>s. s \<in> S \<longrightarrow> I s) = |x\<acute>= (\<lambda>t. f) & (\<lambda>s. True) on U S @ 0] (\<lambda>s. s \<in> S \<longrightarrow> I s))"
  unfolding fbox_diff_inv[symmetric] 
  apply(subst fbox_g_ode_subset[OF assms], simp)+
  apply(clarsimp simp: le_fun_def fun_eq_iff, safe, force)
   apply(erule_tac x=0 in ballE)
  using init_time in_domain ivp(2) assms apply(force, force)
  apply(erule_tac x=x in allE, clarsimp, erule_tac x=t in ballE)
  using in_domain ivp(2) assms by force+

lemma diff_inv_eq_inv_set: 
  "diff_invariant I (\<lambda>t. f) (\<lambda>s. T) S 0 (\<lambda>s. True) = (\<forall>s. I s \<longrightarrow> \<gamma>\<^sup>\<phi> s \<subseteq> {s. I s})"
  unfolding diff_inv_eq_inv_set orbit_def by simp

end

lemma fbox_g_odei: "P \<le> I \<Longrightarrow> I \<le> |x\<acute>= f & G on U S @ t\<^sub>0] I \<Longrightarrow> (\<lambda>s. I s \<and> G s) \<le> Q \<Longrightarrow> 
  P \<le> |x\<acute>= f & G on U S @ t\<^sub>0 DINV I] Q"
  unfolding g_ode_inv_def 
  apply(rule_tac b="|x\<acute>= f & G on U S @ t\<^sub>0] I" in order.trans)
   apply(rule_tac I="I" in fbox_g_orbital_inv, simp_all)
  apply(subst fbox_g_orbital_guard, simp)
  by (rule fbox_iso, force)


subsection \<open> Derivation of the rules of dL \<close>

text \<open> We derive rules of differential dynamic logic (dL). This allows the components to reason 
in the style of that logic. \<close>

abbreviation g_dl_ode ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" 
  ("(1x\<acute>=_ & _)") where "(x\<acute>=f & G) \<equiv> (x\<acute>=(\<lambda>t. f) & G on (\<lambda>s. {t. t \<ge> 0}) UNIV @ 0)"

abbreviation g_dl_ode_inv ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a \<Rightarrow> 'a set" ("(1x\<acute>=_ & _ DINV _)") 
  where "(x\<acute>=f & G DINV I) \<equiv> (x\<acute>=(\<lambda>t. f) & G on (\<lambda>s. {t. t \<ge> 0}) UNIV @ 0 DINV I)"

lemma diff_solve_axiom1: 
  assumes "local_flow f UNIV UNIV \<phi>"
  shows "|x\<acute>= f & G] Q = 
  (\<lambda>s. \<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  by (subst local_flow.fbox_g_ode_subset[OF assms], auto)

lemma diff_solve_axiom2: 
  fixes c::"'a::{heine_borel, banach}"
  shows "|x\<acute>=(\<lambda>s. c) & G] Q = 
  (\<lambda>s. \<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (s + \<tau> *\<^sub>R c)) \<longrightarrow> Q (s + t *\<^sub>R c))"
  by (subst local_flow.fbox_g_ode_subset[OF line_is_local_flow, of UNIV], auto)

lemma diff_solve_rule:
  assumes "local_flow f UNIV UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  shows "P \<le> |x\<acute>= f & G] Q"
  using assms by(subst local_flow.fbox_g_ode_subset[OF assms(1)]) auto

lemma diff_weak_axiom1: "( |x\<acute>= f & G on U S @ t\<^sub>0] G) s"
  unfolding fbox_def g_orbital_eq by auto

lemma diff_weak_axiom2: "|x\<acute>= f & G on T S @ t\<^sub>0] Q = |x\<acute>= f & G on T S @ t\<^sub>0] (\<lambda>s. G s \<longrightarrow> Q s)"
  unfolding fbox_g_orbital image_def by force
  
lemma diff_weak_rule: "G \<le> Q \<Longrightarrow> P \<le> |x\<acute>= f & G on T S @ t\<^sub>0] Q"
  by(auto intro: g_orbitalD simp: le_fun_def g_orbital_eq fbox_def)

lemma fbox_g_orbital_eq_univD:
  assumes "|x\<acute>= f & G on U S @ t\<^sub>0] C = (\<lambda>s. True)" 
    and "\<forall>\<tau>\<in>(down (U s) t). x \<tau> \<in> (x\<acute>= f & G on U S @ t\<^sub>0) s"
  shows "\<forall>\<tau>\<in>(down (U s) t). C (x \<tau>)"
proof
  fix \<tau> assume "\<tau> \<in> (down (U s) t)"
  hence "x \<tau> \<in> (x\<acute>= f & G on U S @ t\<^sub>0) s" 
    using assms(2) by blast
  also have "\<forall>s'. s' \<in> (x\<acute>= f & G on U S @ t\<^sub>0) s \<longrightarrow> C s'"
    using assms(1) unfolding fbox_def by meson 
  ultimately show "C (x \<tau>)" 
    by blast
qed

lemma diff_cut_axiom:
  assumes "|x\<acute>= f & G on U S @ t\<^sub>0] C = (\<lambda>s. True)"
  shows "|x\<acute>= f & G on U S @ t\<^sub>0] Q = |x\<acute>= f & (\<lambda>s. G s \<and> C s) on U S @ t\<^sub>0] Q"
proof(rule_tac f="\<lambda> x. |x] Q" in HOL.arg_cong, rule ext, rule subset_antisym)
  fix s 
  {fix s' assume "s' \<in> (x\<acute>= f & G on U S @ t\<^sub>0) s"
    then obtain \<tau>::real and X where x_ivp: "X \<in> Sols f U S t\<^sub>0 s" 
      and "X \<tau> = s'" and "\<tau> \<in> U s" and guard_x:"\<P> X (down (U s) \<tau>) \<subseteq> {s. G s}"
      using g_orbitalD[of s' "f" G U S t\<^sub>0 s]  by blast
    have "\<forall>t\<in>(down (U s) \<tau>). \<P> X (down (U s) t) \<subseteq> {s. G s}"
      using guard_x by (force simp: image_def)
    also have "\<forall>t\<in>(down (U s) \<tau>). t \<in> U s"
      using \<open>\<tau> \<in> U s\<close> closed_segment_subset_interval by auto
    ultimately have "\<forall>t\<in>(down (U s) \<tau>). X t \<in> (x\<acute>= f & G on U S @ t\<^sub>0) s"
      using g_orbitalI[OF x_ivp] by (metis (mono_tags, lifting))
    hence "\<forall>t\<in>(down (U s) \<tau>). C (X t)" 
      using assms unfolding fbox_def by meson
    hence "s' \<in> (x\<acute>= f & (\<lambda>s. G s \<and> C s) on U S @ t\<^sub>0) s"
      using g_orbitalI[OF x_ivp \<open>\<tau> \<in> U s\<close>] guard_x \<open>X \<tau> = s'\<close> by fastforce}
  thus "(x\<acute>= f & G on U S @ t\<^sub>0) s \<subseteq> (x\<acute>= f & (\<lambda>s. G s \<and> C s) on U S @ t\<^sub>0) s"
    by blast
next show "\<And>s. (x\<acute>= f & (\<lambda>s. G s \<and> C s) on U S @ t\<^sub>0) s \<subseteq> (x\<acute>= f & G on U S @ t\<^sub>0) s" 
    by (auto simp: g_orbital_eq)
qed

lemma diff_cut_rule:
  assumes fbox_C: "P \<le> |x\<acute>= f & G on U S @ t\<^sub>0] C"
    and fbox_Q: "P \<le> |x\<acute>= f & (\<lambda>s. G s \<and> C s) on U S @ t\<^sub>0] Q"
  shows "P \<le> |x\<acute>= f & G on U S @ t\<^sub>0] Q"
proof(subst fbox_def, subst g_orbital_eq, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s assume "P s" and "t \<in> U s"
    and x_ivp:"X \<in> Sols f U S t\<^sub>0 s" 
    and guard_x:"\<forall>\<tau>. \<tau> \<in> U s \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)"
  have "\<forall>\<tau>\<in>(down (U s) t). X \<tau> \<in> (x\<acute>= f & G on U S @ t\<^sub>0) s"
    using g_orbitalI[OF x_ivp] guard_x unfolding image_le_pred by auto
  hence "\<forall>\<tau>\<in>(down (U s) t). C (X \<tau>)" 
    using fbox_C \<open>P s\<close> by (subst (asm) fbox_def, auto)
  hence "X t \<in> (x\<acute>= f & (\<lambda>s. G s \<and> C s) on U S @ t\<^sub>0) s"
    using guard_x \<open>t \<in> U s\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "Q (X t)"
    using \<open>P s\<close> fbox_Q by (subst (asm) fbox_def) auto
qed

lemma diff_inv_axiom1:
  assumes "G s \<longrightarrow> I s" and "diff_invariant I (\<lambda>t. f) (\<lambda>s. {t. t \<ge> 0}) UNIV 0 G"
  shows "( |x\<acute>= f & G] I) s"
  using assms unfolding fbox_g_orbital diff_invariant_eq apply clarsimp
  by (erule_tac x=s in allE, frule ivp_solsD(2), clarsimp)

lemma diff_inv_axiom2:
  assumes "picard_lindeloef (\<lambda>t. f) UNIV UNIV 0"
    and "\<And>s. {t::real. t \<ge> 0} \<subseteq> picard_lindeloef.ex_ivl (\<lambda>t. f) UNIV UNIV 0 s"
    and "diff_invariant I (\<lambda>t. f) (\<lambda>s. {t::real. t \<ge> 0}) UNIV 0 G"
  shows "|x\<acute>= f & G] I = |(\<lambda>s. {x. s = x \<and> G s})] I"
proof(unfold fbox_g_orbital, subst fbox_def, clarsimp simp: fun_eq_iff)
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
  assumes "P \<le> I" and "diff_invariant I f U S t\<^sub>0 G" and "I \<le> Q"
  shows "P \<le> |x\<acute>= f & G on U S @ t\<^sub>0] Q"
  apply(rule fbox_g_orbital_inv[OF assms(1) _ assms(3)])
  unfolding fbox_diff_inv using assms(2) .

end