(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Example I: absence of replacement in \<open>V\<^sub>\<omega>\<^sub>+\<^sub>\<omega>\<close>\<close>
theory CZH_EX_Replacement
  imports CZH_Sets_ZQR
begin


text\<open>
The statement of the main result presented in this subsection
can be found in \cite{noauthor_wikipedia_2001}\footnote{
\url{https://en.wikipedia.org/wiki/Zermelo_set_theory}
}
\<close>

definition repl_ex_fun :: V
  where "repl_ex_fun = (\<lambda>i\<in>\<^sub>\<circ>\<omega>. Vfrom \<omega> i)"

mk_VLambda repl_ex_fun_def
  |vsv repl_ex_fun_vsv|
  |vdomain repl_ex_fun_vdomain|
  |app repl_ex_fun_app|

lemma repl_ex_fun_vrange: "\<R>\<^sub>\<circ> repl_ex_fun \<subseteq>\<^sub>\<circ> Vset (\<omega> + \<omega>)"
proof(intro vsv.vsv_vrange_vsubset, unfold repl_ex_fun_vdomain)
  fix x assume prems: "x \<in>\<^sub>\<circ> \<omega>"
  then show "repl_ex_fun\<lparr>x\<rparr> \<in>\<^sub>\<circ> Vset (\<omega> + \<omega>)"
  proof(induction rule: omega_induct)
    case 0 then show ?case 
      by 
        (
          auto 
            simp: repl_ex_fun_app intro!: vreal_in_Vset_\<omega>2 omega_vsubset_vreal
        )
  next
    case (succ n)
    then have Ord_n: "Ord n" by auto
    have Limit_\<omega>\<omega>: "Limit (\<omega> + \<omega>)" by auto
    from succ show ?case 
      by
        (
          auto 
            simp: Vfrom_succ_Ord[OF Ord_n, of \<omega>] repl_ex_fun_app 
            intro: Limit_\<omega>\<omega> 
            intro!: omega_vsubset_vreal vreal_in_Vset_\<omega>2
        )
  qed
qed (unfold repl_ex_fun_def, auto)

lemma Limit_vsv_not_in_Vset_if_vrange_not_in_Vset:
  assumes "Limit \<alpha>" and "\<R>\<^sub>\<circ> f \<notin>\<^sub>\<circ> Vset \<alpha>"
  shows "f \<notin>\<^sub>\<circ> Vset \<alpha>"
proof(rule ccontr, unfold not_not)
  assume "f \<in>\<^sub>\<circ> Vset \<alpha>"
  with assms(1) have "\<R>\<^sub>\<circ> f \<in>\<^sub>\<circ> Vset \<alpha>" by (simp add: vrange_in_VsetI)
  with assms(2) show False by simp
qed

lemma Ord_not_in_Vset:
  assumes "Ord \<alpha>"
  shows "\<alpha> \<notin>\<^sub>\<circ> Vset \<alpha>"
  using assms
proof(induction rule: Ord_induct3')
  case (succ \<alpha>)
  then have succ\<alpha>: "Vset (succ \<alpha>) = VPow (Vset \<alpha>)" by (simp add: Vset_succ)
  show ?case 
  proof(rule ccontr, unfold not_not)
    assume "succ \<alpha> \<in>\<^sub>\<circ> Vset (succ \<alpha>)"
    then have "vinsert \<alpha> \<alpha> \<in>\<^sub>\<circ> VPow (Vset \<alpha>)" 
      unfolding succ\<alpha> by (simp add: succ_def)
    with succ(2) show False by auto
  qed
next
  case (Limit \<alpha>) show ?case 
  proof(rule ccontr, unfold not_not)
    assume "(\<Union>\<^sub>\<circ>\<xi>\<in>\<^sub>\<circ>\<alpha>. \<xi>) \<in>\<^sub>\<circ> Vset (\<Union>\<^sub>\<circ>\<xi>\<in>\<^sub>\<circ>\<alpha>. \<xi>)"
    with Limit(1) have "\<alpha> \<in>\<^sub>\<circ> Vset \<alpha>" by auto
    with Limit(1) obtain i where i: "i \<in>\<^sub>\<circ> \<alpha>" and "(\<Union>\<^sub>\<circ>\<xi>\<in>\<^sub>\<circ>\<alpha>. \<xi>) \<in>\<^sub>\<circ> Vset i" 
      by (metis Limit_Vfrom_eq Limit_vifunion_def vifunion_iff)
    moreover with Limit(1) have "\<alpha> \<in>\<^sub>\<circ> Vset i" by auto
    ultimately have "i \<in>\<^sub>\<circ> Vset i" by auto
    with Limit(2)[OF i] show False by auto
  qed
qed simp

lemma Ord_succ_vsusbset_Vfrom_succ: 
  assumes "Transset A" and "Ord a" and "a \<in>\<^sub>\<circ> Vfrom A i" 
  shows "succ a \<subseteq>\<^sub>\<circ> Vfrom A (succ i)"
proof(intro vsubsetI)
  from Vfrom_in_mono[OF vsubset_reflexive] have i_succi: 
    "Vfrom A i \<in>\<^sub>\<circ> Vfrom A (succ i)"
    by simp
  fix x assume prems: "x \<in>\<^sub>\<circ> succ a"
  then consider \<open>x \<in>\<^sub>\<circ> a\<close> | \<open>x = a\<close> unfolding succ_def by auto
  then show "x \<in>\<^sub>\<circ> Vfrom A (succ i)"
  proof cases
    case 1
    have "x \<in>\<^sub>\<circ> Vfrom A i" by (rule Vfrom_trans[OF assms(1) 1 assms(3)])
    then show "x \<in>\<^sub>\<circ> Vfrom A (succ i)" by (rule Vfrom_trans[OF assms(1) _ i_succi])
  next
    case 2 from assms(3) show ?thesis
      unfolding 2 by (intro Vfrom_trans[OF assms(1) _ i_succi])
  qed
qed

lemma Ord_succ_in_Vfrom_succ: 
  assumes "Transset A" and "Ord a" and "a \<in>\<^sub>\<circ> Vfrom A i" 
  shows "succ a \<in>\<^sub>\<circ> Vfrom A (succ (succ i))"
  using Ord_succ_vsusbset_Vfrom_succ[OF assms] by (simp add: Vfrom_succ)

lemma \<omega>_vplus_in_Vfrom_\<omega>:
  assumes "j \<in>\<^sub>\<circ> \<omega>"
  shows "\<omega> + j \<in>\<^sub>\<circ> Vfrom \<omega> (succ (2\<^sub>\<nat> * j))"
  using assms
proof(induction rule: omega_induct)
  case 0
  have "\<omega> \<in>\<^sub>\<circ> Vfrom \<omega> (succ 0)" 
    unfolding Vfrom_succ_Ord[where i=0, simplified] by auto
  then show ?case by simp
next
  case (succ n)
  from succ(1) obtain m where n_def: "n = m\<^sub>\<nat>" by (auto elim: nat_of_omega)
  from succ(1) have \<omega>_succn: "\<omega> + succ n = succ (\<omega> + n)" by (simp add: plus_V_succ_right)
  from succ(1) have succ_2succn: "succ (2\<^sub>\<nat> * succ n) = succ (succ (succ (2\<^sub>\<nat> * n)))" 
    unfolding n_def by (cs_concl_step nat_omega_simps)+ auto    
  show ?case 
    unfolding \<omega>_succn succ_2succn
    by (intro Ord_succ_in_Vfrom_succ succ) 
      (auto simp: succ(1) intro: Ord_is_Transset)
qed

lemma repl_ex_fun_vrange_not_in_Vset: "\<R>\<^sub>\<circ> repl_ex_fun \<notin>\<^sub>\<circ> Vset (\<omega> + \<omega>)"
proof(rule ccontr, unfold not_not)
  assume prems: "\<R>\<^sub>\<circ> repl_ex_fun \<in>\<^sub>\<circ> Vset (\<omega> + \<omega>)"
  then have "\<Union>\<^sub>\<circ>(\<R>\<^sub>\<circ> repl_ex_fun) \<in>\<^sub>\<circ> Vset (\<omega> + \<omega>)" by (simp add: VUnion_in_VsetI)
  moreover have "\<omega> + \<omega> \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<R>\<^sub>\<circ> repl_ex_fun)"
  proof(intro vsubsetI)
    fix x assume prems: "x \<in>\<^sub>\<circ> \<omega> + \<omega>"
    from prems consider \<open>x \<in>\<^sub>\<circ> \<omega>\<close> | \<open>x \<notin>\<^sub>\<circ> \<omega>\<close> by auto
    then show "x \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<R>\<^sub>\<circ> repl_ex_fun)"
    proof cases
      case 1 
      show ?thesis 
      proof(rule VUnionI)
        show "Vfrom \<omega> 0 \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> repl_ex_fun"
          unfolding repl_ex_fun_def by blast
        from 1 show "x \<in>\<^sub>\<circ> Vfrom \<omega> 0" by auto
      qed
    next
      case 2
      with prems obtain j where x_def: "x = \<omega> + j" and j: "j \<in>\<^sub>\<circ> \<omega>" 
        by (auto elim: mem_plus_V_E)
      show ?thesis
      proof(rule VUnionI)
        from j show "Vfrom \<omega> (succ (2\<^sub>\<nat> * j)) \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> repl_ex_fun"
          unfolding repl_ex_fun_def by blast
        show "x \<in>\<^sub>\<circ> Vfrom \<omega> (succ (2\<^sub>\<nat> * j))"
          by (rule \<omega>_vplus_in_Vfrom_\<omega>[OF j, folded x_def])
      qed
    qed
  qed
  ultimately have "\<omega> + \<omega> \<in>\<^sub>\<circ> Vset (\<omega> + \<omega>)" by auto
  with Ord_not_in_Vset show False by auto
qed

lemma repl_ex_fun_not_in_Vset: "repl_ex_fun \<notin>\<^sub>\<circ> Vset (\<omega> + \<omega>)"
  by (rule Limit_vsv_not_in_Vset_if_vrange_not_in_Vset) 
    (auto simp: repl_ex_fun_vrange_not_in_Vset)

text\<open>\newpage\<close>

end