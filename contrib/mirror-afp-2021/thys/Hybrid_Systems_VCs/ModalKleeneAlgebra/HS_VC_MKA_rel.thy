(*  Title:       Verification components with relational MKA 
    Author:      Jonathan Julián Huerta y Munive, 2020
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

subsection \<open>Verification of hybrid programs\<close>

text \<open> We show that relations form an antidomain Kleene algebra. This allows us to inherit 
the rules of the wlp calculus for regular programs. Finally, we derive three methods for 
verifying correctness specifications for the continuous dynamics of hybrid systems in this 
setting. \<close>

theory HS_VC_MKA_rel
  imports 
    "../HS_ODEs" 
    "HS_VC_MKA"
    "../HS_VC_KA_rel"

begin

definition rel_ad :: "'a rel \<Rightarrow> 'a rel" where
  "rel_ad R = {(x,x) | x. \<not> (\<exists>y. (x,y) \<in> R)}"

interpretation rel_aka: antidomain_kleene_algebra rel_ad "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl
  by  unfold_locales (auto simp: rel_ad_def)


subsubsection \<open> Regular programs\<close>

text \<open> Lemmas for manipulation of predicates in the relational model \<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and antidomain_semiringl.ads_d ("d")

notation Id ("skip")
     and relcomp (infixl ";" 70)
     and zero_class.zero ("0")
     and rel_aka.fbox ("wp")

definition p2r :: "'a pred \<Rightarrow> 'a rel" ("(1\<lceil>_\<rceil>)") where
  "\<lceil>P\<rceil> = {(s,s) |s. P s}"

lemma p2r_simps[simp]: 
  "\<lceil>P\<rceil> \<le> \<lceil>Q\<rceil> = (\<forall>s. P s \<longrightarrow> Q s)"
  "(\<lceil>P\<rceil> = \<lceil>Q\<rceil>) = (\<forall>s. P s = Q s)"
  "(\<lceil>P\<rceil> ; \<lceil>Q\<rceil>) = \<lceil>\<lambda> s. P s \<and> Q s\<rceil>"
  "(\<lceil>P\<rceil> \<union> \<lceil>Q\<rceil>) = \<lceil>\<lambda> s. P s \<or> Q s\<rceil>"
  "rel_ad \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<not> P s\<rceil>"
  "rel_aka.ads_d \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  unfolding p2r_def rel_ad_def rel_aka.ads_d_def by auto

lemma in_p2r [simp]: "(a,b) \<in> \<lceil>P\<rceil> = (P a \<and> a = b)"
  by (auto simp: p2r_def)

text \<open> Lemmas for verification condition generation \<close>

lemma wp_rel: "wp R \<lceil>P\<rceil> = \<lceil>\<lambda> x. \<forall> y. (x,y) \<in> R \<longrightarrow> P y\<rceil>"
  unfolding rel_aka.fbox_def p2r_def rel_ad_def by auto

\<comment> \<open> Tests \<close>

lemma wp_test[simp]: "wp \<lceil>P\<rceil> \<lceil>Q\<rceil> = \<lceil>\<lambda>s. P s \<longrightarrow> Q s\<rceil>"
  by (subst wp_rel, simp add: p2r_def)

\<comment> \<open> Assignments \<close>

definition assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) rel" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) = {(s, vec_upd s x (e s))| s. True}" 

lemma wp_assign [simp]: "wp (x ::= e) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. Q (\<chi> j. ((($) s)(x := (e s))) j)\<rceil>"
  unfolding wp_rel vec_upd_def assign_def by (auto simp: fun_upd_def)

\<comment> \<open> Nondeterministic assignments \<close>

definition nondet_assign :: "'b \<Rightarrow> ('a^'b) rel" ("(2_ ::= ? )" [70] 61)
  where "(x ::= ?) = {(s,vec_upd s x k)|s k. True}"

lemma wp_nondet_assign[simp]: "wp (x ::= ?) \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<forall>k. P (\<chi> j. ((($) s)(x := k)) j)\<rceil>"
  unfolding wp_rel nondet_assign_def vec_upd_eq apply(clarsimp, safe)
  by (erule_tac x="(\<chi> j. if j = x then k else s $ j)" in allE, auto)

\<comment> \<open> Nondeterministic choice \<close>

lemma le_wp_choice_iff: "\<lceil>P\<rceil> \<le> wp (X \<union> Y) \<lceil>Q\<rceil> \<longleftrightarrow> \<lceil>P\<rceil> \<le> wp X \<lceil>Q\<rceil> \<and> \<lceil>P\<rceil> \<le> wp Y \<lceil>Q\<rceil>"
  using rel_aka.le_fbox_choice_iff[of "\<lceil>P\<rceil>"] by simp

\<comment> \<open> Conditional statement \<close>

abbreviation cond_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("IF _ THEN _ ELSE _" [64,64] 63) 
  where "IF P THEN X ELSE Y \<equiv> rel_aka.aka_cond \<lceil>P\<rceil> X Y"

\<comment> \<open> Finite iteration \<close>

abbreviation loopi_sugar :: "'a rel \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("LOOP _ INV _ " [64,64] 63)
  where "LOOP R INV I \<equiv> rel_aka.aka_loopi R \<lceil>I\<rceil>"

lemma change_loopI: "LOOP X INV G = LOOP X INV I"
  by (unfold rel_aka.aka_loopi_def, simp)

lemma wp_loopI: 
  "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> wp R \<lceil>I\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> wp (LOOP R INV I) \<lceil>Q\<rceil>"
  using rel_aka.fbox_loopi[of "\<lceil>P\<rceil>"] by auto

lemma wp_loopI_break: 
  "\<lceil>P\<rceil> \<le> wp Y \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> wp X \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>  \<Longrightarrow> \<lceil>P\<rceil> \<le> wp (Y ; (LOOP X INV I)) \<lceil>Q\<rceil>"
  using rel_aka.fbox_loopi_break[of "\<lceil>P\<rceil>"] by auto


subsubsection \<open> Evolution commands \<close>

text \<open>Verification by providing evolution\<close>

definition g_evol :: "(('a::ord) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b pred \<Rightarrow> ('b \<Rightarrow> 'a set) \<Rightarrow> 'b rel" ("EVOL")
  where "EVOL \<phi> G U = {(s,s') |s s'. s' \<in> g_orbit (\<lambda>t. \<phi> t s) G (U s)}"

lemma wp_g_dyn[simp]:  
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "wp (EVOL \<phi> G U) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  unfolding wp_rel g_evol_def g_orbit_eq by auto

text \<open>Verification by providing solutions\<close>

definition g_ode :: "(real \<Rightarrow> ('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> real set) \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 
  'a rel" ("(1x\<acute>=_ & _ on _ _ @ _)") 
  where "(x\<acute>= f & G on U S @ t\<^sub>0) = {(s,s') |s s'. s' \<in> g_orbital f G U S t\<^sub>0 s}"

lemma wp_g_orbital: "wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda>s. \<forall>X\<in>Sols f U S t\<^sub>0 s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (X \<tau>)) \<longrightarrow> Q (X t)\<rceil>"
  unfolding g_orbital_eq wp_rel ivp_sols_def g_ode_def by auto

context local_flow
begin

lemma wp_g_ode_subset:
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "wp (x\<acute>= (\<lambda>t. f) & G on U S @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>(U s). (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))\<rceil>"
  apply(unfold wp_g_orbital, clarsimp, rule iffI; clarify)
   apply(force simp: in_ivp_sols assms)
  apply(frule ivp_solsD(2), frule ivp_solsD(3), frule ivp_solsD(4))
  apply(subgoal_tac "\<forall>\<tau>\<in>down (U s) t. X \<tau> = \<phi> \<tau> s")
   apply(clarsimp, fastforce, rule ballI)
  apply(rule ivp_unique_solution[OF _ _ _ _ _ in_ivp_sols])
  using assms by auto

lemma wp_g_ode: "wp (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. T) S @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))\<rceil>"
  by (subst wp_g_ode_subset, simp_all add: init_time interval_time)

lemma wp_g_ode_ivl: "t \<ge> 0 \<Longrightarrow> t \<in> T \<Longrightarrow> wp (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. {0..t}) S @ 0) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))\<rceil>"
  apply(subst wp_g_ode_subset, simp_all add: subintervalI init_time real_Icc_closed_segment)
  by (auto simp: closed_segment_eq_real_ivl)

lemma wp_orbit: "wp ({(s,s') | s s'. s' \<in> \<gamma>\<^sup>\<phi> s}) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>T. Q (\<phi> t s))\<rceil>"
  unfolding orbit_def wp_g_ode g_ode_def[symmetric] by auto

end

text \<open> Verification with differential invariants \<close>

definition g_ode_inv :: "(real \<Rightarrow> ('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> real set) \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on U S @ t\<^sub>0 DINV I) = (x\<acute>= f & G on U S @ t\<^sub>0)"

lemma wp_g_orbital_guard: 
  assumes "H = (\<lambda>s. G s \<and> Q s)"
  shows "wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>H\<rceil>"
  unfolding wp_g_orbital using assms by auto

lemma wp_g_orbital_inv:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>I\<rceil>" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms(1) 
  apply(rule order.trans)
  using assms(2) 
  apply(rule order.trans)
  apply(rule rel_aka.fbox_iso)
  using assms(3) by auto

lemma wp_diff_inv[simp]: "(\<lceil>I\<rceil> \<le> wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>I\<rceil>) = diff_invariant I f U S t\<^sub>0 G"
  unfolding diff_invariant_eq wp_g_orbital by(auto simp: p2r_def)

lemma diff_inv_guard_ignore:
  assumes "\<lceil>I\<rceil> \<le> wp (x\<acute>= f & (\<lambda>s. True) on U S @ t\<^sub>0) \<lceil>I\<rceil>"
  shows "\<lceil>I\<rceil> \<le> wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>I\<rceil>"
  using assms unfolding wp_diff_inv diff_invariant_eq by auto

context local_flow
begin

lemma wp_diff_inv_eq: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "diff_invariant I (\<lambda>t. f) U S 0 (\<lambda>s. True) = 
  (\<lceil>\<lambda>s. s \<in> S \<longrightarrow> I s\<rceil> = wp (x\<acute>= (\<lambda>t. f) & (\<lambda>s. True) on U S @ 0) \<lceil>\<lambda>s. s \<in> S \<longrightarrow> I s\<rceil>)"
  unfolding wp_diff_inv[symmetric] 
  apply(subst wp_g_ode_subset[OF assms], simp)+
  apply(clarsimp, safe, force)
   apply(erule_tac x=0 in ballE)
  using init_time in_domain ivp(2) assms apply(force, force)
  apply(erule_tac x=s in allE, clarsimp, erule_tac x=t in ballE)
  using in_domain ivp(2) assms by force+

lemma diff_inv_eq_inv_set:
  "diff_invariant I (\<lambda>t. f) (\<lambda>s. T) S 0 (\<lambda>s. True) = (\<forall>s. I s \<longrightarrow> \<gamma>\<^sup>\<phi> s \<subseteq> {s. I s})"
  unfolding diff_inv_eq_inv_set orbit_def by (auto simp: p2r_def)

end

lemma wp_g_odei: "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>I\<rceil> \<Longrightarrow> \<lceil>\<lambda>s. I s \<and> G s\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> 
  \<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on U S @ t\<^sub>0 DINV I) \<lceil>Q\<rceil>"
  unfolding g_ode_inv_def 
  apply(rule_tac b="wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>I\<rceil>" in order.trans)
   apply(rule_tac I="I" in wp_g_orbital_inv, simp_all)
  apply(subst wp_g_orbital_guard, simp)
  by (rule rel_aka.fbox_iso, simp)


subsubsection \<open> Derivation of the rules of dL \<close>

text \<open> We derive rules of differential dynamic logic (dL). This allows the components to reason 
in the style of that logic. \<close>

abbreviation g_dl_ode ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _)") 
  where "(x\<acute>=f & G) \<equiv> (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. {t. t \<ge> 0}) UNIV @ 0)"

abbreviation g_dl_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _ DINV _)") 
  where "(x\<acute>= f & G DINV I) \<equiv> (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. {t. t \<ge> 0}) UNIV @ 0 DINV I)"

lemma diff_solve_axiom1: 
  assumes "local_flow f UNIV UNIV \<phi>"
  shows "wp (x\<acute>= f & G) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda>s. \<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)\<rceil>"
  by (subst local_flow.wp_g_ode_subset[OF assms], auto)

lemma diff_solve_axiom2: 
  fixes c::"'a::{heine_borel, banach}"
  shows "wp (x\<acute>=(\<lambda>s. c) & G) \<lceil>Q\<rceil> = 
  \<lceil>\<lambda>s. \<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (s + \<tau> *\<^sub>R c)) \<longrightarrow> Q (s + t *\<^sub>R c)\<rceil>"
  apply(subst local_flow.wp_g_ode_subset[where \<phi>="(\<lambda>t s. s + t *\<^sub>R c)" and T=UNIV])
  by (rule line_is_local_flow, auto)

lemma diff_solve_rule:
  assumes "local_flow f UNIV UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G) \<lceil>Q\<rceil>"
  using assms by (subst local_flow.wp_g_ode_subset[OF assms(1)], auto)

lemma diff_weak_axiom1: "Id \<subseteq> wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>G\<rceil>"
  unfolding wp_rel g_ode_def g_orbital_eq by auto

lemma diff_weak_axiom2: 
  "wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>= f & G on T S @ t\<^sub>0) \<lceil>\<lambda> s. G s \<longrightarrow> Q s\<rceil>"
  unfolding wp_g_orbital image_def by force

lemma diff_weak_rule: 
  assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>Q\<rceil>"
  using assms by (auto simp: wp_g_orbital)

lemma wp_g_evol_IdD:
  assumes "wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>C\<rceil> = Id"
    and "\<forall>\<tau>\<in>(down (U s) t). (s, x \<tau>) \<in> (x\<acute>= f & G on U S @ t\<^sub>0)"
  shows "\<forall>\<tau>\<in>(down (U s) t). C (x \<tau>)"
proof
  fix \<tau> assume "\<tau> \<in> (down (U s) t)"
  hence "x \<tau> \<in> g_orbital f G U S t\<^sub>0 s" 
    using assms(2) unfolding g_ode_def by blast
  also have "\<forall>y. y \<in> (g_orbital f G U S t\<^sub>0 s) \<longrightarrow> C y" 
    using assms(1) unfolding wp_rel g_ode_def by(auto simp: p2r_def)
  ultimately show "C (x \<tau>)" 
    by blast
qed

lemma diff_cut_axiom:
  assumes "wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>C\<rceil> = Id"
  shows "wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>Q\<rceil> = wp (x\<acute>= f & (\<lambda>s. G s \<and> C s) on U S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(rule_tac f="\<lambda> x. wp x \<lceil>Q\<rceil>" in HOL.arg_cong, rule subset_antisym)
  show "(x\<acute>=f & G on U S @ t\<^sub>0) \<subseteq> (x\<acute>=f & \<lambda>s. G s \<and> C s on U S @ t\<^sub>0)"
  proof(clarsimp simp: g_ode_def)
    fix s and s' assume "s' \<in> g_orbital f G U S t\<^sub>0 s"
    then obtain \<tau>::real and X where x_ivp: "X \<in> Sols f U S t\<^sub>0 s" 
      and "X \<tau> = s'" and "\<tau> \<in> U s" and guard_x:"(\<P> X (down (U s) \<tau>) \<subseteq> {s. G s})"
      using g_orbitalD[of s' "f" G _ S t\<^sub>0 s] by blast
    have "\<forall>t\<in>(down (U s) \<tau>). \<P> X (down (U s) t) \<subseteq> {s. G s}"
      using guard_x by (force simp: image_def)
    also have "\<forall>t\<in>(down (U s) \<tau>). t \<in> U s"
      using \<open>\<tau> \<in> U s\<close> by auto
    ultimately have "\<forall>t\<in>(down (U s) \<tau>). X t \<in> g_orbital f G U S t\<^sub>0 s"
      using g_orbitalI[OF x_ivp] by (metis (mono_tags, lifting))
    hence "\<forall>t\<in>(down (U s) \<tau>). C (X t)" 
      using wp_g_evol_IdD[OF assms(1)] unfolding g_ode_def by blast
    thus "s' \<in> g_orbital f (\<lambda>s. G s \<and> C s) U S t\<^sub>0 s"
      using g_orbitalI[OF x_ivp \<open>\<tau> \<in> U s\<close>] guard_x \<open>X \<tau> = s'\<close> by fastforce
  qed
next show "(x\<acute>=f & \<lambda>s. G s \<and> C s on U S @ t\<^sub>0) \<subseteq> (x\<acute>=f & G on U S @ t\<^sub>0)"  
    by (auto simp: g_orbital_eq g_ode_def)
qed

lemma diff_cut_rule:
  assumes wp_C: "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>C\<rceil>"
    and wp_Q: "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & (\<lambda>s. G s \<and> C s) on U S @ t\<^sub>0) \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>Q\<rceil>"
proof(subst wp_rel, simp add: g_orbital_eq p2r_def g_ode_def, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s assume "P s" and "t \<in> U s"
    and x_ivp:"X \<in> Sols f U S t\<^sub>0 s" 
    and guard_x:"\<forall>x. x \<in> U s \<and> x \<le> t \<longrightarrow> G (X x)"
  have "\<forall>t\<in>(down (U s) t). X t \<in> g_orbital f G U S t\<^sub>0 s"
    using g_orbitalI[OF x_ivp] guard_x by auto
  hence "\<forall>t\<in>(down (U s) t). C (X t)" 
    using wp_C \<open>P s\<close> by (subst (asm) wp_rel, auto simp: g_ode_def)
  hence "X t \<in> g_orbital f (\<lambda>s. G s \<and> C s) U S t\<^sub>0 s"
    using guard_x \<open>t \<in> U s\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "Q (X t)"
    using \<open>P s\<close> wp_Q by (subst (asm) wp_rel) (auto simp: g_ode_def)
qed

lemma diff_inv_axiom1:
  assumes "G s \<longrightarrow> I s" and "diff_invariant I (\<lambda>t. f) (\<lambda>s. {t. t \<ge> 0}) UNIV 0 G"
  shows "(s,s) \<in> wp (x\<acute>= f & G) \<lceil>I\<rceil>"
  using assms unfolding wp_g_orbital diff_invariant_eq apply clarsimp
  by (erule_tac x=s in allE, frule ivp_solsD(2), clarsimp)

lemma diff_inv_axiom2:
  assumes "picard_lindeloef (\<lambda>t. f) UNIV UNIV 0"
    and "\<And>s. {t::real. t \<ge> 0} \<subseteq> picard_lindeloef.ex_ivl (\<lambda>t. f) UNIV UNIV 0 s"
    and "diff_invariant I (\<lambda>t. f) (\<lambda>s. {t::real. t \<ge> 0}) UNIV 0 G"
  shows "wp (x\<acute>= f & G) \<lceil>I\<rceil> = wp \<lceil>G\<rceil> \<lceil>I\<rceil>"
proof(unfold wp_g_orbital, subst wp_rel, clarsimp simp: fun_eq_iff)
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
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "diff_invariant I f U S t\<^sub>0 G" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<lceil>P\<rceil> \<le> wp (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>Q\<rceil>"
  apply(rule wp_g_orbital_inv[OF assms(1) _ assms(3)])
  unfolding wp_diff_inv using assms(2) .

end