(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Further properties of natural numbers\<close>
theory CZH_Sets_Nat
  imports CZH_Sets_Sets
begin



subsection\<open>Background\<close>


text\<open>
The section exposes certain fundamental properties of natural numbers and
provides convenience utilities for doing arithmetic within the type \<^typ>\<open>V\<close>. 

Many of the results that are presented in this sections were carried over
(with amendments) from the theory \<open>Nat\<close> that can be found in the main 
library of Isabelle/HOL. 
\<close>

notation ord_of_nat (\<open>_\<^sub>\<nat>\<close> [999] 999)

named_theorems nat_omega_simps

declare One_nat_def[simp del]

abbreviation (input) vpfst where "vpfst a \<equiv> a\<lparr>0\<rparr>"
abbreviation (input) vpsnd where "vpsnd a \<equiv> a\<lparr>1\<^sub>\<nat>\<rparr>"
abbreviation (input) vpthrd where "vpthrd a \<equiv> a\<lparr>2\<^sub>\<nat>\<rparr>"



subsection\<open>Conversion between \<^typ>\<open>V\<close> and \<open>nat\<close>\<close>


subsubsection\<open>Primitive arithmetic\<close>

lemma ord_of_nat_plus[nat_omega_simps]: "a\<^sub>\<nat> + b\<^sub>\<nat> = (a + b)\<^sub>\<nat>"
  by (induct b) (simp_all add: plus_V_succ_right)

lemma ord_of_nat_times[nat_omega_simps]: "a\<^sub>\<nat> * b\<^sub>\<nat> = (a * b)\<^sub>\<nat>"
  by (induct b) (simp_all add: mult_succ nat_omega_simps)

lemma ord_of_nat_succ[nat_omega_simps]: "succ (a\<^sub>\<nat>) = (Suc a)\<^sub>\<nat>" by auto

lemmas [nat_omega_simps] = nat_cadd_eq_add

lemma ord_of_nat_csucc[nat_omega_simps]: "csucc (a\<^sub>\<nat>) = succ (a\<^sub>\<nat>)" 
  using finite_csucc by blast

lemma ord_of_nat_succ_vempty[nat_omega_simps]: "succ 0 = 1\<^sub>\<nat>" by auto

lemma ord_of_nat_vone[nat_omega_simps]: "1 = 1\<^sub>\<nat>" by auto


subsubsection\<open>Transfer\<close>

definition cr_omega :: "V \<Rightarrow> nat \<Rightarrow> bool"
  where "cr_omega a b \<longleftrightarrow> (a = ord_of_nat b)"


text\<open>Transfer setup.\<close>

lemma cr_omega_right_total[transfer_rule]: "right_total cr_omega"
  unfolding cr_omega_def right_total_def by simp

lemma cr_omega_bi_unqie[transfer_rule]: "bi_unique cr_omega"
  unfolding cr_omega_def bi_unique_def
  by (simp add: inj_eq inj_ord_of_nat)

lemma omega_transfer_domain_rule[transfer_domain_rule]: 
  "Domainp cr_omega = (\<lambda>x. x \<in>\<^sub>\<circ> \<omega>)"
  unfolding cr_omega_def by (auto simp: elts_\<omega>)

lemma omega_transfer[transfer_rule]: 
  "(rel_set cr_omega) (elts \<omega>) (UNIV::nat set)"
  unfolding cr_omega_def rel_set_def by (simp add: elts_\<omega>)

lemma omega_of_real_transfer[transfer_rule]: "cr_omega (ord_of_nat a) a"
  unfolding cr_omega_def by auto


text\<open>Operations.\<close>

lemma omega_succ_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_omega ===> cr_omega) succ Suc"
proof(intro rel_funI, unfold cr_omega_def)
  fix x y assume prems: "x = y\<^sub>\<nat>"
  show "succ x = Suc y\<^sub>\<nat>" unfolding prems ord_of_nat_succ[symmetric] ..
qed

lemma omega_plus_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_omega ===> cr_omega ===> cr_omega) (+) (+)"
  by (intro rel_funI, unfold cr_omega_def) (simp add: nat_omega_simps)

lemma omega_mult_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_omega ===> cr_omega ===> cr_omega) (*) (*)"
  by (intro rel_funI, unfold cr_omega_def) (simp add: nat_omega_simps)

lemma ord_of_nat_card_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(rel_set (=) ===> cr_omega) (\<lambda>x. ord_of_nat (card x)) card"
  by (intro rel_funI) (simp add: cr_omega_def rel_set_eq)



subsection\<open>Elementary results\<close>

lemma ord_of_nat_vempty: "0 = 0\<^sub>\<nat>" by auto

lemma set_vzero_eq_ord_of_nat_vone: "set {0} = 1\<^sub>\<nat>"
  by (metis elts_1 set_of_elts ord_of_nat_vone)

lemma vone_in_omega[simp]: "1 \<in>\<^sub>\<circ> \<omega>" unfolding \<omega>_def by force

lemma nat_of_omega:
  assumes "n \<in>\<^sub>\<circ> \<omega>" 
  obtains m where "n = m\<^sub>\<nat>"
  using assms unfolding \<omega>_def by clarsimp

lemma omega_prev:
  assumes "n \<in>\<^sub>\<circ> \<omega>" and "0 \<in>\<^sub>\<circ> n"
  obtains k where "n = succ k"
proof-
  from assms nat_of_omega obtain m where "n = m\<^sub>\<nat>" by auto
  with assms(2) obtain m' where "m = Suc m'"
    unfolding less_V_def by (auto dest: gr0_implies_Suc)
  with that show ?thesis unfolding \<open>n = m\<^sub>\<nat>\<close> using ord_of_nat.simps(2) by blast  
qed

lemma omega_vplus_commutative:
  assumes "a \<in>\<^sub>\<circ> \<omega>" and "b \<in>\<^sub>\<circ> \<omega>" 
  shows "a + b = b + a" 
  using assms by (metis Groups.add_ac(2) nat_of_omega ord_of_nat_plus)

lemma omega_vinetrsection[intro]:
  assumes "m \<in>\<^sub>\<circ> \<omega>" and "n \<in>\<^sub>\<circ> \<omega>"
  shows "m \<inter>\<^sub>\<circ> n \<in>\<^sub>\<circ> \<omega>"
proof-
  from nat_into_Ord[OF assms(1)] nat_into_Ord[OF assms(2)] Ord_linear_le 
  consider "m \<subseteq>\<^sub>\<circ> n" | "n \<subseteq>\<^sub>\<circ> m" 
    by auto
  then show ?thesis by cases (simp_all add: assms inf.absorb1 inf.absorb2)
qed



subsection\<open>Induction\<close>

lemma omega_induct_all[consumes 1, case_names step]:
  assumes "n \<in>\<^sub>\<circ> \<omega>" and "\<And>x. \<lbrakk>x \<in>\<^sub>\<circ> \<omega>; \<And>y. y \<in>\<^sub>\<circ> x \<Longrightarrow> P y\<rbrakk> \<Longrightarrow> P x" 
  shows "P n"
  using assms by (metis Ord_\<omega> Ord_induct Ord_linear Ord_trans nat_into_Ord)

lemma omega_induct[consumes 1, case_names 0 succ]:
  assumes "n \<in>\<^sub>\<circ> \<omega>" and "P 0" and "\<And>n. \<lbrakk> n \<in>\<^sub>\<circ> \<omega>; P n \<rbrakk> \<Longrightarrow> P (succ n)" 
  shows "P n"
  using assms(1,3)
proof(induct rule: omega_induct_all)
  case (step x) show ?case
  proof(cases \<open>x = 0\<close>)
    case True with assms(2) show ?thesis by simp
  next
    case False
    with step(1) have "0 \<in>\<^sub>\<circ> x" by (simp add: mem_0_Ord)
    with \<open>x \<in>\<^sub>\<circ> \<omega>\<close> obtain y where x_def: "x = succ y" by (elim omega_prev)
    with elts_succ step.hyps(1) have "y \<in>\<^sub>\<circ> \<omega>" by (blast intro: Ord_trans)
    have "y \<in>\<^sub>\<circ> x" by (simp add: \<open>x = succ y\<close>) 
    have "P y" by (auto intro: step.prems step.hyps(2)[OF \<open>y \<in>\<^sub>\<circ> x\<close>])
    from step.prems[OF \<open>y \<in>\<^sub>\<circ> \<omega>\<close> \<open>P y\<close>, folded x_def] show "P x" . 
  qed
qed



subsection\<open>Methods\<close>


text\<open>
The following methods provide an infrastructure for working with goals of the 
form \<open>a \<in>\<^sub>\<circ> n\<^sub>\<nat> \<Longrightarrow> P a\<close>.
\<close>

lemma in_succE:
  assumes "a \<in>\<^sub>\<circ> succ n" and "\<And>a. a \<in>\<^sub>\<circ> n \<Longrightarrow> P a" and "P n"
  shows "P a"
  using assms by auto

method Suc_of_numeral =
  (
    unfold numeral.simps add.assoc,
    use nothing in \<open>unfold Suc_eq_plus1_left[symmetric], unfold One_nat_def\<close>
  )

method succ_of_numeral = 
  (
    Suc_of_numeral, 
    use nothing in \<open>unfold ord_of_nat_succ[symmetric] ord_of_nat_zero\<close>
  )

method numeral_of_succ =
  (
    unfold nat_omega_simps, 
    use nothing in 
      \<open>
        unfold numeral.simps[symmetric] Suc_numeral add_num_simps,
        (unfold numerals(1))?
      \<close>
  )

method elim_in_succ =
  (
    (
      elim in_succE; 
      use nothing in \<open>(unfold triv_forall_equality)?; (numeral_of_succ)?\<close>
    ), 
    simp
  )

method elim_in_numeral = (succ_of_numeral, use nothing in \<open>elim_in_succ\<close>)



subsection\<open>Auxiliary\<close>

lemma two: "2\<^sub>\<nat> = set {0, 1\<^sub>\<nat>}" by force

lemma three: "3\<^sub>\<nat> = set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}" by force

lemma four: "4\<^sub>\<nat> = set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>, 3\<^sub>\<nat>}" by force

lemma two_vdiff_zero[simp]: "set {0, 1\<^sub>\<nat>} -\<^sub>\<circ> set {0} = set {1\<^sub>\<nat>}" by auto
lemma two_vdiff_one[simp]: "set {0, 1\<^sub>\<nat>} -\<^sub>\<circ> set {1\<^sub>\<nat>} = set {0}" by auto


text\<open>\newpage\<close>

end