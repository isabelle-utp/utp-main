(*  Title:       Verification and refinement of hybrid systems in the relational KAT
    Author:      Jonathan Julián Huerta y Munive, 2020
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

subsection \<open>Verification of hybrid programs\<close>

text \<open> We use our relational model to obtain verification and refinement components for hybrid 
programs. We devise three methods for reasoning with evolution commands and their continuous 
dynamics: providing flows, solutions or invariants. \<close>

theory HS_VC_KAT_rel
  imports 
    "../HS_ODEs"
    "HS_VC_KAT"
    "../HS_VC_KA_rel"

begin

interpretation rel_tests: test_semiring "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" "\<lambda>x. Id \<inter> ( - x)"
  by (standard, auto)

interpretation rel_kat: kat "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl "\<lambda>x. Id \<inter> ( - x)"
  by (unfold_locales)

definition rel_R :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where 
  "rel_R P Q = \<Union>{X. rel_kat.Hoare P X Q}"

interpretation rel_rkat: rkat "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl "(\<lambda>X. Id \<inter> - X)" rel_R
  by (standard, auto simp: rel_R_def rel_kat.Hoare_def)


subsubsection \<open> Regular programs\<close>

text \<open> Lemmas for manipulation of predicates in the relational model \<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

notation Id ("skip")
     and empty ("abort")
     and relcomp (infixr ";" 75)

no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")
        and Archimedean_Field.floor_ceiling_class.floor ("\<lfloor>_\<rfloor>")
        and tau ("\<tau>")
        and n_op ("n _" [90] 91)

definition p2r :: "'a pred \<Rightarrow> 'a rel" ("\<lceil>_\<rceil>") where
  "\<lceil>P\<rceil> = {(s,s) |s. P s}"

lemma p2r_simps[simp]: 
  "\<lceil>P\<rceil> \<le> \<lceil>Q\<rceil> = (\<forall>s. P s \<longrightarrow> Q s)"
  "(\<lceil>P\<rceil> = \<lceil>Q\<rceil>) = (\<forall>s. P s = Q s)"
  "(\<lceil>P\<rceil> ; \<lceil>Q\<rceil>) = \<lceil>\<lambda> s. P s \<and> Q s\<rceil>"
  "(\<lceil>P\<rceil> \<union> \<lceil>Q\<rceil>) = \<lceil>\<lambda> s. P s \<or> Q s\<rceil>"
  "rel_tests.t \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  "(- Id) \<union> \<lceil>P\<rceil> = - \<lceil>\<lambda>s. \<not> P s\<rceil>"
  "Id \<inter> (- \<lceil>P\<rceil>) = \<lceil>\<lambda>s. \<not> P s\<rceil>"
  unfolding p2r_def by auto

text \<open> Lemmas for verification condition generation \<close>

lemma RdL_is_rRKAT: "(\<forall>x. {(x,x)}; R1 \<subseteq> {(x,x)}; R2) = (R1 \<subseteq> R2)"
  by auto (* Refinement in dL is that of rKAT *)

\<comment> \<open> Hoare Triples \<close>

abbreviation relHoare ("\<^bold>{_\<^bold>}_\<^bold>{_\<^bold>}") 
  where "\<^bold>{P\<^bold>}X\<^bold>{Q\<^bold>} \<equiv> rel_kat.Hoare \<lceil>P\<rceil> X \<lceil>Q\<rceil>"

lemma rel_kat_H: "\<^bold>{P\<^bold>} X \<^bold>{Q\<^bold>} \<longleftrightarrow> (\<forall>s s'. P s \<longrightarrow> (s,s') \<in> X \<longrightarrow> Q s')"
  by (simp add: rel_kat.Hoare_def, auto simp add: p2r_def)

\<comment> \<open> Skip \<close>

lemma sH_skip[simp]: "\<^bold>{P\<^bold>} skip \<^bold>{Q\<^bold>} \<longleftrightarrow> \<lceil>P\<rceil> \<le> \<lceil>Q\<rceil>"
  unfolding rel_kat_H by simp

lemma H_skip: "\<^bold>{P\<^bold>} skip \<^bold>{P\<^bold>}"
  by simp

\<comment> \<open> Tests \<close>

lemma sH_test[simp]: "\<^bold>{P\<^bold>} \<lceil>R\<rceil> \<^bold>{Q\<^bold>} = (\<forall>s. P s \<longrightarrow> R s \<longrightarrow> Q s)"
  by (subst rel_kat_H, simp add: p2r_def)

\<comment> \<open> Abort \<close>

lemma sH_abort[simp]: "\<^bold>{P\<^bold>} abort \<^bold>{Q\<^bold>} \<longleftrightarrow> True"
  unfolding rel_kat_H by simp

lemma H_abort: "\<^bold>{P\<^bold>} abort \<^bold>{Q\<^bold>}"
  by simp

\<comment> \<open> Assignments \<close>

definition assign :: "'b \<Rightarrow> ('a^'b \<Rightarrow> 'a) \<Rightarrow> ('a^'b) rel" ("(2_ ::= _)" [70, 65] 61) 
  where "(x ::= e) \<equiv> {(s, vec_upd s x (e s))| s. True}" 

lemma sH_assign[simp]: "\<^bold>{P\<^bold>} (x ::= e) \<^bold>{Q\<^bold>} \<longleftrightarrow> (\<forall>s. P s \<longrightarrow> Q (\<chi> j. ((($) s)(x := (e s))) j))"
  unfolding rel_kat_H vec_upd_def assign_def by (auto simp: fun_upd_def)

lemma H_assign: "P = (\<lambda>s. Q (\<chi> j. ((($) s)(x := (e s))) j)) \<Longrightarrow> \<^bold>{P\<^bold>} (x ::= e) \<^bold>{Q\<^bold>}"
  by simp

\<comment> \<open> Nondeterministic assignments \<close>

definition nondet_assign :: "'b \<Rightarrow> ('a^'b) rel" ("(2_ ::= ? )" [70] 61)
  where "(x ::= ?) = {(s,vec_upd s x k)|s k. True}"

lemma sH_nondet_assign[simp]: 
  "\<^bold>{P\<^bold>} (x ::= ?) \<^bold>{Q\<^bold>} \<longleftrightarrow> (\<forall>s. P s \<longrightarrow> (\<forall>k. Q (\<chi> j. ((($) s)(x := k)) j)))"
  unfolding rel_kat_H vec_upd_def nondet_assign_def by (auto simp: fun_upd_def)

lemma H_nondet_assign: "\<^bold>{\<lambda>s. \<forall>k. P (\<chi> j. ((($) s)(x := k)) j)\<^bold>} (x ::= ?) \<^bold>{P\<^bold>}"
  by simp

\<comment> \<open> Sequential Composition \<close>

lemma H_seq: "\<^bold>{P\<^bold>} X \<^bold>{R\<^bold>} \<Longrightarrow> \<^bold>{R\<^bold>} Y \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} X;Y \<^bold>{Q\<^bold>}"
  using rel_kat.H_seq .

lemma sH_seq: "\<^bold>{P\<^bold>} X;Y \<^bold>{Q\<^bold>} = \<^bold>{P\<^bold>} X \<^bold>{\<lambda>s. \<forall>s'. (s, s') \<in> Y \<longrightarrow> Q s'\<^bold>}"
  unfolding rel_kat_H by auto

lemma H_assignl: 
  assumes "\<^bold>{K\<^bold>} X \<^bold>{Q\<^bold>}" 
    and "\<forall>s. P s \<longrightarrow> K (vec_lambda ((($) s)(x := e s)))"
  shows "\<^bold>{P\<^bold>} (x ::= e);X \<^bold>{Q\<^bold>}"
  apply(rule H_seq, subst sH_assign)
  using assms by auto

\<comment> \<open> Nondeterministic Choice \<close>

lemma sH_choice: "\<^bold>{P\<^bold>} X \<union> Y \<^bold>{Q\<^bold>} \<longleftrightarrow> (\<^bold>{P\<^bold>} X \<^bold>{Q\<^bold>} \<and> \<^bold>{P\<^bold>} Y \<^bold>{Q\<^bold>})"
  unfolding rel_kat_H by auto

lemma H_choice: "\<^bold>{P\<^bold>} X \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} Y \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} X \<union> Y \<^bold>{Q\<^bold>}"
  using rel_kat.H_choice .

\<comment> \<open> Conditional Statement \<close>

abbreviation cond_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" 
  ("IF _ THEN _ ELSE _" [64,64] 63) 
  where "IF B THEN X ELSE Y \<equiv> rel_kat.kat_cond \<lceil>B\<rceil> X Y"

lemma sH_cond[simp]: 
  "\<^bold>{P\<^bold>} (IF B THEN X ELSE Y) \<^bold>{Q\<^bold>} \<longleftrightarrow> (\<^bold>{\<lambda>s. P s \<and> B s\<^bold>} X \<^bold>{Q\<^bold>} \<and> \<^bold>{\<lambda>s. P s \<and> \<not> B s\<^bold>} Y \<^bold>{Q\<^bold>})"
  by (auto simp: rel_kat.H_cond_iff rel_kat_H)

lemma H_cond: 
  "\<^bold>{\<lambda>s. P s \<and> B s\<^bold>} X \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{\<lambda>s. P s \<and> \<not> B s\<^bold>} Y \<^bold>{Q\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} (IF B THEN X ELSE Y) \<^bold>{Q\<^bold>}"
  by simp

\<comment> \<open> While Loop \<close>

abbreviation while_inv_sugar :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" 
  ("WHILE _ INV _ DO _" [64,64,64] 63) 
  where "WHILE B INV I DO X \<equiv> rel_kat.kat_while_inv \<lceil>B\<rceil> \<lceil>I\<rceil> X"

lemma sH_whileI: "\<forall>s. P s \<longrightarrow> I s \<Longrightarrow> \<forall>s. I s \<and> \<not> B s \<longrightarrow> Q s \<Longrightarrow> \<^bold>{\<lambda>s. I s \<and> B s\<^bold>} X \<^bold>{I\<^bold>} 
  \<Longrightarrow> \<^bold>{P\<^bold>} (WHILE B INV I DO X) \<^bold>{Q\<^bold>}"
  by (rule rel_kat.H_while_inv, auto simp: p2r_def rel_kat.Hoare_def, fastforce)

lemma "\<^bold>{\<lambda>s. P s \<and> B s\<^bold>} X \<^bold>{\<lambda>s. P s\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} (WHILE B INV I DO X) \<^bold>{\<lambda>s. P s \<and> \<not> B s\<^bold>}"
  using rel_kat.H_while[of "\<lceil>P\<rceil>" "\<lceil>B\<rceil>" X]
  unfolding rel_kat.kat_while_inv_def by auto

\<comment> \<open> Finite Iteration \<close>

abbreviation loopi_sugar :: "'a rel \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("LOOP _ INV _ " [64,64] 63)
  where "LOOP X INV I \<equiv> rel_kat.kat_loop_inv X \<lceil>I\<rceil>"

lemma H_loop: "\<^bold>{P\<^bold>} X \<^bold>{P\<^bold>} \<Longrightarrow> \<^bold>{P\<^bold>} (LOOP X INV I) \<^bold>{P\<^bold>}"
  by (auto intro: rel_kat.H_loop)

lemma H_loopI: "\<^bold>{I\<^bold>} X \<^bold>{I\<^bold>} \<Longrightarrow> \<lceil>P\<rceil> \<subseteq> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<subseteq> \<lceil>Q\<rceil> \<Longrightarrow> \<^bold>{P\<^bold>} (LOOP X INV I) \<^bold>{Q\<^bold>}"
  using rel_kat.H_loop_inv[of "\<lceil>P\<rceil>" "\<lceil>I\<rceil>" X "\<lceil>Q\<rceil>"] by auto


subsubsection \<open> Evolution commands \<close>

\<comment> \<open>Verification by providing evolution\<close>

definition g_evol :: "(('a::ord) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b pred \<Rightarrow> ('b \<Rightarrow> 'a set) \<Rightarrow> 'b rel" ("EVOL")
  where "EVOL \<phi> G U = {(s,s') |s s'. s' \<in> g_orbit (\<lambda>t. \<phi> t s) G (U s)}"

lemma sH_g_evol[simp]:  
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "\<^bold>{P\<^bold>} (EVOL \<phi> G U) \<^bold>{Q\<^bold>} = (\<forall>s. P s \<longrightarrow> (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  unfolding rel_kat_H g_evol_def g_orbit_eq by auto

lemma H_g_evol: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes "P = (\<lambda>s. (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  shows "\<^bold>{P\<^bold>} (EVOL \<phi> G U) \<^bold>{Q\<^bold>}"
  by (simp add: assms)

\<comment> \<open>Verification by providing solutions\<close>

definition g_ode :: "(real \<Rightarrow> ('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> real set) \<Rightarrow> 'a set \<Rightarrow> real \<Rightarrow> 
  'a rel" ("(1x\<acute>=_ & _ on _ _ @ _)") 
  where "(x\<acute>= f & G on T S @ t\<^sub>0) = {(s,s') |s s'. s' \<in> g_orbital f G T S t\<^sub>0 s}"

lemma H_g_orbital: 
  "P = (\<lambda>s. (\<forall>X\<in>ivp_sols f U S t\<^sub>0 s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (X \<tau>)) \<longrightarrow> Q (X t))) \<Longrightarrow> 
  \<^bold>{P\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0) \<^bold>{Q\<^bold>}"
  unfolding rel_kat_H g_ode_def g_orbital_eq by clarsimp

lemma sH_g_orbital: "\<^bold>{P\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0) \<^bold>{Q\<^bold>} = 
  (\<forall>s. P s \<longrightarrow> (\<forall>X\<in>ivp_sols f U S t\<^sub>0 s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (X \<tau>)) \<longrightarrow> Q (X t)))"
  unfolding g_orbital_eq g_ode_def rel_kat_H by auto

context local_flow
begin

lemma sH_g_ode_subset: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "\<^bold>{P\<^bold>} (x\<acute>= (\<lambda>t. f) & G on U S @ 0) \<^bold>{Q\<^bold>} = 
  (\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
proof(unfold sH_g_orbital, clarsimp, safe)
  fix s t
  assume hyps: "s \<in> S" "P s" "t \<in> U s" "\<forall>\<tau>. \<tau> \<in> U s \<and> \<tau> \<le> t \<longrightarrow> G (\<phi> \<tau> s)"
    and main: "\<forall>s. P s \<longrightarrow> (\<forall>X\<in>Sols (\<lambda>t. f) U S 0 s. \<forall>t\<in>U s. (\<forall>\<tau>. \<tau> \<in> U s \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)) \<longrightarrow> Q (X t))"
  hence "(\<lambda>t. \<phi> t s) \<in> Sols (\<lambda>t. f) U S 0 s"
    using in_ivp_sols assms by blast
  thus "Q (\<phi> t s)"
    using main hyps by fastforce
next
  fix s X t
  assume hyps: "P s" "X \<in> Sols (\<lambda>t. f) U S 0 s" "t \<in> U s"  "\<forall>\<tau>. \<tau> \<in> U s \<and> \<tau> \<le> t \<longrightarrow> G (X \<tau>)"
    and main: "\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>U s. (\<forall>\<tau>. \<tau> \<in> U s \<and> \<tau> \<le> t \<longrightarrow> G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  hence obs: "s \<in> S"
    using ivp_sols_def[of "\<lambda>t. f"] init_time by auto
  hence "\<forall>\<tau>\<in>down (U s) t. X \<tau> = \<phi> \<tau> s"
    using eq_solution hyps assms by blast
  thus "Q (X t)"
    using hyps main obs by auto
qed

lemma H_g_ode_subset:
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
    and "P = (\<lambda>s. s \<in> S \<longrightarrow> (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))" 
  shows "\<^bold>{P\<^bold>} (x\<acute>= (\<lambda>t. f) & G on U S @ 0) \<^bold>{Q\<^bold>}"
  using assms apply(subst sH_g_ode_subset[OF assms(1)])
  unfolding assms by auto

lemma sH_g_ode: "\<^bold>{P\<^bold>} (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. T) S @ 0) \<^bold>{Q\<^bold>} = 
  (\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  by (subst sH_g_ode_subset, auto simp: init_time interval_time)

lemma sH_g_ode_ivl: "t \<ge> 0 \<Longrightarrow> t \<in> T \<Longrightarrow> \<^bold>{P\<^bold>} (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. {0..t}) S @ 0) \<^bold>{Q\<^bold>} = 
  (\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)))"
  apply(subst sH_g_ode_subset; clarsimp, (force)?)
  using init_time interval_time mem_is_interval_1_I by blast

lemma sH_orbit: "\<^bold>{P\<^bold>} ({(s,s') | s s'. s' \<in> \<gamma>\<^sup>\<phi> s}) \<^bold>{Q\<^bold>} = (\<forall>s \<in> S. P s \<longrightarrow> (\<forall> t \<in> T. Q (\<phi> t s)))"
  using sH_g_ode unfolding orbit_def g_ode_def by auto

end

\<comment> \<open> Verification with differential invariants \<close>

definition g_ode_inv :: "(real \<Rightarrow> ('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> ('a \<Rightarrow> real set) \<Rightarrow> 'a set \<Rightarrow> 
  real \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _ on _ _ @ _ DINV _ )") 
  where "(x\<acute>= f & G on U S @ t\<^sub>0 DINV I) = (x\<acute>= f & G on U S @ t\<^sub>0)"

lemma sH_g_orbital_guard: 
  assumes "R = (\<lambda>s. G s \<and> Q s)"
  shows "\<^bold>{P\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0) \<^bold>{Q\<^bold>} = \<^bold>{P\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0) \<^bold>{R\<^bold>}" 
  using assms unfolding g_orbital_eq rel_kat_H ivp_sols_def g_ode_def by auto

lemma sH_g_orbital_inv:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "\<^bold>{I\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0) \<^bold>{I\<^bold>}" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows " \<^bold>{P\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0) \<^bold>{Q\<^bold>}"
  using assms(1) apply(rule_tac p'="\<lceil>I\<rceil>" in rel_kat.H_consl, simp)
  using assms(3) apply(rule_tac q'="\<lceil>I\<rceil>" in rel_kat.H_consr, simp)
  using assms(2) by simp

lemma sH_diff_inv[simp]: "\<^bold>{I\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0) \<^bold>{I\<^bold>} = diff_invariant I f U S t\<^sub>0 G"
  unfolding diff_invariant_eq rel_kat_H g_orbital_eq g_ode_def by auto

lemma H_g_ode_inv: "\<^bold>{I\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0) \<^bold>{I\<^bold>} \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> 
  \<lceil>\<lambda>s. I s \<and> G s\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> \<^bold>{P\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0 DINV I) \<^bold>{Q\<^bold>}"
  unfolding g_ode_inv_def apply(rule_tac q'="\<lceil>\<lambda>s. I s \<and> G s\<rceil>" in rel_kat.H_consr, simp)
  apply(subst sH_g_orbital_guard[symmetric], force)
  by (rule_tac I="I" in sH_g_orbital_inv, simp_all)


subsection \<open> Refinement Components \<close>

\<comment> \<open> Skip \<close>

lemma R_skip: "(\<forall>s. P s \<longrightarrow> Q s) \<Longrightarrow> skip \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (rule rel_rkat.R2, simp)

\<comment> \<open> Abort \<close>

lemma R_abort: "abort \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (rule rel_rkat.R2, simp)

\<comment> \<open> Sequential Composition \<close>

lemma R_seq: "(rel_R \<lceil>P\<rceil> \<lceil>R\<rceil>) ; (rel_R \<lceil>R\<rceil> \<lceil>Q\<rceil>) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  using rel_rkat.R_seq by blast

lemma R_seq_law: "X \<le> rel_R \<lceil>P\<rceil> \<lceil>R\<rceil> \<Longrightarrow> Y \<le> rel_R \<lceil>R\<rceil> \<lceil>Q\<rceil> \<Longrightarrow> X; Y \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding rel_rkat.spec_def by (rule H_seq)

lemmas R_seq_mono = relcomp_mono

\<comment> \<open> Nondeterministic Choice \<close>

lemma R_choice: "(rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>) \<union> (rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  using rel_rkat.R_choice[of "\<lceil>P\<rceil>" "\<lceil>Q\<rceil>"] .

lemma R_choice_law: "X \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil> \<Longrightarrow> Y \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil> \<Longrightarrow> X \<union> Y \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  using le_supI .

lemma R_choice_mono: "P' \<subseteq> P \<Longrightarrow> Q' \<subseteq> Q \<Longrightarrow> P' \<union> Q' \<subseteq> P \<union> Q"
  using Un_mono .

\<comment> \<open> Assignment \<close>

lemma R_assign: "(x ::= e) \<le> rel_R \<lceil>\<lambda>s. P (\<chi> j. ((($) s)(x := e s)) j)\<rceil> \<lceil>P\<rceil>"
  unfolding rel_rkat.spec_def by (rule H_assign, clarsimp simp: fun_upd_def)

lemma R_assign_law: 
  "(\<forall>s. P s \<longrightarrow> Q (\<chi> j. ((($) s)(x := (e s))) j)) \<Longrightarrow> (x ::= e) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_assign[symmetric] by (rule rel_rkat.R2)

lemma R_assignl: "P = (\<lambda>s. R (\<chi> j. ((($) s)(x := e s)) j)) \<Longrightarrow> 
  (x ::= e) ; rel_R \<lceil>R\<rceil> \<lceil>Q\<rceil> \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply(rule_tac R=R in R_seq_law)
  by (rule_tac R_assign_law, simp_all)

lemma R_assignr: "R = (\<lambda>s. Q (\<chi> j. ((($) s)(x := e s)) j)) \<Longrightarrow> 
  rel_R \<lceil>P\<rceil> \<lceil>R\<rceil>; (x ::= e) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply(rule_tac R=R in R_seq_law, simp)
  by (rule_tac R_assign_law, simp)

lemma "(x ::= e) ; rel_R \<lceil>Q\<rceil> \<lceil>Q\<rceil> \<le> rel_R \<lceil>(\<lambda>s. Q (\<chi> j. ((($) s)(x := e s)) j))\<rceil> \<lceil>Q\<rceil>"
  by (rule R_assignl) simp

lemma "rel_R \<lceil>Q\<rceil> \<lceil>(\<lambda>s. Q (\<chi> j. ((($) s)(x := e s)) j))\<rceil>; (x ::= e) \<le> rel_R \<lceil>Q\<rceil> \<lceil>Q\<rceil>"
  by (rule R_assignr) simp

\<comment> \<open> Nondeterministic Assignment \<close>

lemma R_nondet_assign: "(x ::= ?) \<le> rel_R \<lceil>\<lambda>s. \<forall>k. P (\<chi> j. ((($) s)(x := k)) j)\<rceil> \<lceil>P\<rceil>"
  unfolding rel_rkat.spec_def by (rule H_nondet_assign)

lemma R_nondet_assign_law: 
  "(\<forall>s. P s \<longrightarrow> (\<forall>k. Q (\<chi> j. ((($) s)(x := k)) j))) \<Longrightarrow> (x ::= ?) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_nondet_assign[symmetric] by (rule rel_rkat.R2)

\<comment> \<open> Conditional Statement \<close>

lemma R_cond: 
  "(IF B THEN rel_R \<lceil>\<lambda>s. B s \<and> P s\<rceil> \<lceil>Q\<rceil> ELSE rel_R \<lceil>\<lambda>s. \<not> B s \<and> P s\<rceil> \<lceil>Q\<rceil>) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  using rel_rkat.R_cond[of "\<lceil>B\<rceil>" "\<lceil>P\<rceil>" "\<lceil>Q\<rceil>"] by simp

lemma R_cond_mono: "X \<le> X' \<Longrightarrow> Y \<le> Y' \<Longrightarrow> (IF P THEN X ELSE Y) \<le> IF P THEN X' ELSE Y'"
  by (auto simp: rel_kat.kat_cond_def)

lemma R_cond_law: "X \<le> rel_R \<lceil>\<lambda>s. B s \<and> P s\<rceil> \<lceil>Q\<rceil> \<Longrightarrow> Y \<le> rel_R \<lceil>\<lambda>s. \<not> B s \<and> P s\<rceil> \<lceil>Q\<rceil> \<Longrightarrow> 
  (IF B THEN X ELSE Y) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (rule order_trans; (rule R_cond_mono)?, (rule R_cond)?) auto

\<comment> \<open> While Loop \<close>

lemma R_while: "K = (\<lambda>s. P s \<and> \<not> B s) \<Longrightarrow> 
  WHILE B INV I DO (rel_R \<lceil>\<lambda>s. P s \<and> B s\<rceil> \<lceil>P\<rceil>) \<le> rel_R \<lceil>P\<rceil> \<lceil>K\<rceil>"
  unfolding rel_kat.kat_while_inv_def using rel_rkat.R_while[of "\<lceil>B\<rceil>" "\<lceil>P\<rceil>"] by simp

lemma R_whileI:
  "X \<le> rel_R \<lceil>I\<rceil> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>\<lambda>s. I s \<and> B s\<rceil> \<Longrightarrow> \<lceil>\<lambda>s. I s \<and> \<not> B s\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> 
  WHILE B INV I DO X \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (rule rel_rkat.R2, rule rel_kat.H_while_inv, auto simp: rel_kat_H rel_rkat.spec_def)

lemma R_while_mono: "X \<le> X' \<Longrightarrow> (WHILE P INV I DO X) \<subseteq> WHILE P INV I DO X'"
  by (simp add: rel_dioid.mult_isol rel_dioid.mult_isor rel_ka.conway.dagger_iso 
      rel_kat.kat_while_def rel_kat.kat_while_inv_def)

lemma R_while_law: "X \<le> rel_R \<lceil>\<lambda>s. P s \<and> B s\<rceil> \<lceil>P\<rceil> \<Longrightarrow> Q = (\<lambda>s. P s \<and> \<not> B s) \<Longrightarrow> 
  (WHILE B INV I DO X) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (rule order_trans; (rule R_while_mono)?, (rule R_while)?)

\<comment> \<open> Finite Iteration \<close>

lemma R_loop:"LOOP rel_R \<lceil>P\<rceil> \<lceil>P\<rceil> INV I \<le> rel_R \<lceil>P\<rceil> \<lceil>P\<rceil>"
  using rel_rkat.R_loop .

lemma R_loopI: 
  "X \<le> rel_R \<lceil>I\<rceil> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>I\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> LOOP X INV I \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding rel_rkat.spec_def using H_loopI by blast

lemma R_loop_mono: "X \<le> X' \<Longrightarrow> LOOP X INV I \<subseteq> LOOP X' INV I"
  unfolding rel_kat.kat_loop_inv_def by (simp add: rel_ka.star_iso)

\<comment> \<open> Evolution command (flow) \<close>

lemma R_g_evol: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "(EVOL \<phi> G U) \<le> rel_R \<lceil>\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> P (\<phi> t s)\<rceil> \<lceil>P\<rceil>"
  unfolding rel_rkat.spec_def by (rule H_g_evol, simp)

lemma R_g_evol_law: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "(\<forall>s. P s \<longrightarrow> (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))) \<Longrightarrow> (EVOL \<phi> G U) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_g_evol[symmetric] rel_rkat.spec_def .

lemma R_g_evoll: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "P = (\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> R (\<phi> t s)) \<Longrightarrow> 
  (EVOL \<phi> G U) ; rel_R \<lceil>R\<rceil> \<lceil>Q\<rceil> \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply(rule_tac R=R in R_seq_law)
  by (rule_tac R_g_evol_law, simp_all)

lemma R_g_evolr: 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "R = (\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)) \<Longrightarrow> 
  rel_R \<lceil>P\<rceil> \<lceil>R\<rceil>; (EVOL \<phi> G U) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply(rule_tac R=R in R_seq_law, simp)
  by (rule_tac R_g_evol_law, simp)

lemma 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "EVOL \<phi> G U ; rel_R \<lceil>Q\<rceil> \<lceil>Q\<rceil> \<le> rel_R \<lceil>\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)\<rceil> \<lceil>Q\<rceil>"
  by (rule R_g_evoll) simp

lemma 
  fixes \<phi> :: "('a::preorder) \<Rightarrow> 'b \<Rightarrow> 'b"
  shows "rel_R \<lceil>Q\<rceil> \<lceil>\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)\<rceil>; EVOL \<phi> G U \<le> rel_R \<lceil>Q\<rceil> \<lceil>Q\<rceil>"
  by (rule R_g_evolr) simp

\<comment> \<open> Evolution command (ode) \<close>

context local_flow
begin

lemma R_g_ode_subset: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "(x\<acute>= (\<lambda>t. f) & G on U S @ 0) \<le> 
  rel_R \<lceil>\<lambda>s. s\<in>S \<longrightarrow> (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> P (\<phi> t s))\<rceil> \<lceil>P\<rceil>"
  unfolding rel_rkat.spec_def by (rule H_g_ode_subset[OF assms], simp_all)

lemma R_g_ode_rule_subset: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
  shows "(\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))) \<Longrightarrow> 
  (x\<acute>= (\<lambda>t. f) & G on U S @ 0) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (rule rel_rkat.R2, subst sH_g_ode_subset[OF assms], auto)

lemma R_g_odel_subset: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
    and "P = (\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> R (\<phi> t s))"
  shows "(x\<acute>= (\<lambda>t. f) & G on U S @ 0) ; rel_R \<lceil>R\<rceil> \<lceil>Q\<rceil> \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply (rule_tac R=R in R_seq_law, rule_tac R_g_ode_rule_subset)
  by (simp_all add: assms)

lemma R_g_oder_subset: 
  assumes "\<And>s. s \<in> S \<Longrightarrow> 0 \<in> U s \<and> is_interval (U s) \<and> U s \<subseteq> T"
    and "R = (\<lambda>s. \<forall>t\<in>U s. (\<forall>\<tau>\<in>down (U s) t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  shows "rel_R \<lceil>P\<rceil> \<lceil>R\<rceil>; (x\<acute>= (\<lambda>t. f) & G on U S @ 0) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply (rule_tac R=R in R_seq_law, simp)
  by (rule_tac R_g_ode_rule_subset, simp_all add: assms)

lemma R_g_ode: "(x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. T) S @ 0) \<le> 
  rel_R \<lceil>\<lambda>s. s\<in>S \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> P (\<phi> t s))\<rceil> \<lceil>P\<rceil>"
  by (rule R_g_ode_subset, auto simp: init_time interval_time)

lemma R_g_ode_law: "(\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))) \<Longrightarrow> 
  (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. T) S @ 0) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_g_ode[symmetric] by (rule rel_rkat.R2)

lemma R_g_odel: "P = (\<lambda>s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> R (\<phi> t s)) \<Longrightarrow> 
  (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. T) S @ 0) ; rel_R \<lceil>R\<rceil> \<lceil>Q\<rceil> \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (rule R_g_odel_subset, auto simp: init_time interval_time)

lemma R_g_oder: "R = (\<lambda>s. \<forall>t\<in>T. (\<forall>\<tau>\<in>down T t. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s)) \<Longrightarrow> 
  rel_R \<lceil>P\<rceil> \<lceil>R\<rceil>; (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. T) S @ 0) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (rule R_g_oder_subset, auto simp: init_time interval_time)

lemma R_g_ode_ivl: 
  "t \<ge> 0 \<Longrightarrow> t \<in> T \<Longrightarrow> (\<forall>s\<in>S. P s \<longrightarrow> (\<forall>t\<in>{0..t}. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))) \<Longrightarrow> 
  (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. {0..t}) S @ 0) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding sH_g_ode_ivl[symmetric] by (rule rel_rkat.R2)

end

\<comment> \<open> Evolution command (invariants) \<close>

lemma R_g_ode_inv: "diff_invariant I f T S t\<^sub>0 G \<Longrightarrow> \<lceil>P\<rceil> \<le> \<lceil>I\<rceil> \<Longrightarrow> \<lceil>\<lambda>s. I s \<and> G s\<rceil> \<le> \<lceil>Q\<rceil> \<Longrightarrow> 
  (x\<acute>=f & G on T S @ t\<^sub>0 DINV I) \<le> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  unfolding rel_rkat.spec_def by (auto simp: H_g_ode_inv)


subsection \<open> Derivation of the rules of dL \<close>

text \<open> We derive rules of differential dynamic logic (dL). This allows the components to reason 
in the style of that logic. \<close>

abbreviation g_dl_ode ::"(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _)") 
  where "(x\<acute>=f & G) \<equiv> (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. {t. t \<ge> 0}) UNIV @ 0)"

abbreviation g_dl_ode_inv :: "(('a::banach)\<Rightarrow>'a) \<Rightarrow> 'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel" ("(1x\<acute>=_ & _ DINV _)") 
  where "(x\<acute>= f & G DINV I) \<equiv> (x\<acute>= (\<lambda>t. f) & G on (\<lambda>s. {t. t \<ge> 0}) UNIV @ 0 DINV I)"

lemma diff_solve_rule1:
  assumes "local_flow f UNIV UNIV \<phi>"
    and "\<forall>s. P s \<longrightarrow> (\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (\<phi> \<tau> s)) \<longrightarrow> Q (\<phi> t s))"
  shows "\<^bold>{P\<^bold>} (x\<acute>= f & G) \<^bold>{Q\<^bold>}"
  using assms by(subst local_flow.sH_g_ode_subset, auto)

lemma diff_solve_rule2: 
  fixes c::"'a::{heine_borel, banach}"
  assumes "\<forall>s. P s \<longrightarrow> (\<forall>t\<ge>0. (\<forall>\<tau>\<in>{0..t}. G (s + \<tau> *\<^sub>R c)) \<longrightarrow> Q (s + t *\<^sub>R c))"
  shows "\<^bold>{P\<^bold>} (x\<acute>=(\<lambda>s. c) & G) \<^bold>{Q\<^bold>}"
  apply(subst local_flow.sH_g_ode_subset[where T=UNIV and \<phi>="(\<lambda> t x. x + t *\<^sub>R c)"])
  using line_is_local_flow assms by auto

lemma diff_weak_rule: 
  assumes "\<lceil>G\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<^bold>{P\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0) \<^bold>{Q\<^bold>}"
  using assms unfolding g_orbital_eq rel_kat_H ivp_sols_def g_ode_def by auto

lemma diff_cut_rule:
  assumes wp_C:"rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & G on U S @ t\<^sub>0) \<lceil>C\<rceil>"
    and wp_Q:"rel_kat.Hoare \<lceil>P\<rceil> (x\<acute>= f & (\<lambda> s. G s \<and> C s) on U S @ t\<^sub>0) \<lceil>Q\<rceil>"
  shows "\<^bold>{P\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0) \<^bold>{Q\<^bold>}"
proof(subst rel_kat_H, simp add: g_orbital_eq p2r_def g_ode_def, clarsimp)
  fix t::real and X::"real \<Rightarrow> 'a" and s 
  assume "P s" and "t \<in> U s"
    and x_ivp:"X \<in> ivp_sols f U S t\<^sub>0 s" 
    and guard_x:"\<forall>x. x \<in> U s \<and> x \<le> t \<longrightarrow> G (X x)"
  have "\<forall>t\<in>(down (U s) t). X t \<in> g_orbital f G U S t\<^sub>0 s"
    using g_orbitalI[OF x_ivp] guard_x by auto
  hence "\<forall>t\<in>(down (U s) t). C (X t)" 
    using wp_C \<open>P s\<close> by (subst (asm) rel_kat_H, auto simp: g_ode_def)
  hence "X t \<in> g_orbital f (\<lambda>s. G s \<and> C s) U S t\<^sub>0 s"
    using guard_x \<open>t \<in> U s\<close> by (auto intro!: g_orbitalI x_ivp)
  thus "Q (X t)"
    using \<open>P s\<close> wp_Q by (subst (asm) rel_kat_H) (auto simp: g_ode_def)
qed

lemma diff_inv_rule:
  assumes "\<lceil>P\<rceil> \<le> \<lceil>I\<rceil>" and "diff_invariant I f U S t\<^sub>0 G" and "\<lceil>I\<rceil> \<le> \<lceil>Q\<rceil>"
  shows "\<^bold>{P\<^bold>} (x\<acute>= f & G on U S @ t\<^sub>0) \<^bold>{Q\<^bold>}"
  apply(subst g_ode_inv_def[symmetric, where I=I], rule H_g_ode_inv)
  unfolding sH_diff_inv using assms by auto

end