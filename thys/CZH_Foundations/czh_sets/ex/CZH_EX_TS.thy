(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Example II: topological spaces\<close>
theory CZH_EX_TS
  imports CZH_Sets_ZQR
begin



subsection\<open>Background\<close>


text\<open>
The section presents elements of the foundations of the theory of topological
spaces formalized in \<open>ZFC in HOL\<close>. The definitions were adopted 
(with amendments) from the main library of Isabelle/HOL and 
\cite{kelley_general_1955}.
\<close>

named_theorems ts_struct_field_simps



subsection\<open>\<open>\<Z>\<close>-sequence\<close>

locale \<Z>_vfsequence = \<Z> \<alpha> + vfsequence \<SS> for \<alpha> \<SS> +
  assumes vrange_vsubset_Vset: "\<R>\<^sub>\<circ> \<SS> \<subseteq>\<^sub>\<circ> Vset \<alpha>"


text\<open>Rules.\<close>

lemma \<Z>_vfsequenceI[intro]:
  assumes "\<Z> \<alpha>" and "vfsequence \<SS>" and "\<R>\<^sub>\<circ> \<SS> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  shows "\<Z>_vfsequence \<alpha> \<SS>"
  using assms unfolding \<Z>_vfsequence_def \<Z>_vfsequence_axioms_def by simp

lemmas \<Z>_vfsequenceD[dest] = \<Z>_vfsequence.axioms

lemma \<Z>_vfsequenceE[elim]:
  assumes "\<Z>_vfsequence \<alpha> \<SS>"
  obtains "\<Z> \<alpha>" and "vfsequence \<SS>" and "\<R>\<^sub>\<circ> \<SS> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  using assms by (simp add: \<Z>_vfsequence.axioms(1,2) \<Z>_vfsequence.vrange_vsubset_Vset)
  

text\<open>Elementary properties.\<close>

context \<Z>_vfsequence
begin

lemma (in \<Z>_vfsequence) \<Z>_vfsequence_vdomain_in_Vset[intro, simp]: 
  "\<D>\<^sub>\<circ> \<SS> \<in>\<^sub>\<circ> Vset \<alpha>"
  using Axiom_of_Infinity vfsequence_vdomain_in_omega by auto

lemma (in \<Z>_vfsequence) \<Z>_vfsequence_vrange_in_Vset[intro, simp]: 
  "\<R>\<^sub>\<circ> \<SS> \<in>\<^sub>\<circ> Vset \<alpha>"
  using vrange_vsubset_Vset vfsequence_vdomain_in_omega by auto

lemma (in \<Z>_vfsequence) \<Z>_vfsequence_struct_in_Vset: "\<SS> \<in>\<^sub>\<circ> Vset \<alpha>"
  by (auto simp: vrange_vsubset_Vset vsv_Limit_vsv_in_VsetI)

end


subsection\<open>Topological space\<close>

definition \<A> where [ts_struct_field_simps]: "\<A> = 0"
definition \<T> where [ts_struct_field_simps]: "\<T> = 1\<^sub>\<nat>"

locale \<Z>_ts = \<Z>_vfsequence \<alpha> \<SS> for \<alpha> \<SS> +
  assumes \<Z>_ts_length: "2\<^sub>\<nat> \<le> vcard \<SS>" 
    and \<Z>_ts_closed[intro]: "A \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> A \<subseteq>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>"
    and \<Z>_ts_domain[intro, simp]: "\<SS>\<lparr>\<A>\<rparr> \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr>"
    and \<Z>_ts_vintersection[intro]: 
      "A \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> B \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> A \<inter>\<^sub>\<circ> B \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr>"
    and \<Z>_ts_VUnion[intro]: "X \<subseteq>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> \<Union>\<^sub>\<circ>X \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr>"


text\<open>Rules.\<close>

lemma \<Z>_tsI[intro]:
  assumes "\<Z>_vfsequence \<alpha> \<SS>"
    and "2\<^sub>\<nat> \<le> vcard \<SS>"
    and "\<And>A. A \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> A \<subseteq>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>"
    and "\<SS>\<lparr>\<A>\<rparr> \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr>"
    and "\<And>A B. A \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> B \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> A \<inter>\<^sub>\<circ> B \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr>"
    and "\<And>X. X \<subseteq>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> \<Union>\<^sub>\<circ>X \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr>"
  shows "\<Z>_ts \<alpha> \<SS>"
  using assms unfolding \<Z>_ts_def \<Z>_ts_axioms_def by simp

lemma \<Z>_tsD[dest]:
  assumes "\<Z>_ts \<alpha> \<SS>"
  shows "\<Z>_vfsequence \<alpha> \<SS>"
    and "2\<^sub>\<nat> \<le> vcard \<SS>"
    and "\<And>A. A \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> A \<subseteq>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>"
    and "\<SS>\<lparr>\<A>\<rparr> \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr>"
    and "\<And>A B. A \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> B \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> A \<inter>\<^sub>\<circ> B \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr>"
    and "\<And>X. X \<subseteq>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> \<Union>\<^sub>\<circ>X \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr>"
  using assms unfolding \<Z>_ts_def \<Z>_ts_axioms_def by auto

lemma \<Z>_tsE[elim]:
  assumes "\<Z>_ts \<alpha> \<SS>"
  obtains "\<Z>_vfsequence \<alpha> \<SS>"
    and "2\<^sub>\<nat> \<le> vcard \<SS>"
    and "\<And>A. A \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> A \<subseteq>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>"
    and "\<SS>\<lparr>\<A>\<rparr> \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr>"
    and "\<And>A B. A \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> B \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> A \<inter>\<^sub>\<circ> B \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr>"
    and "\<And>X. X \<subseteq>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr> \<Longrightarrow> \<Union>\<^sub>\<circ>X \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr>"
  using assms by auto


text\<open>Elementary properties.\<close>

lemma (in \<Z>_ts) \<Z>_ts_vempty_in_ts: "0 \<in>\<^sub>\<circ> \<SS>\<lparr>\<T>\<rparr>" 
  using \<Z>_ts_VUnion[of 0] by simp



subsection\<open>Indiscrete topology\<close>

definition ts_indiscrete :: "V \<Rightarrow> V"
  where "ts_indiscrete A = [A, set {0, A}]\<^sub>\<circ>"

named_theorems ts_indiscrete_simps

lemma ts_indiscrete_\<A>[ts_indiscrete_simps]: "ts_indiscrete A\<lparr>\<A>\<rparr> = A"
  unfolding ts_indiscrete_def by (auto simp: ts_struct_field_simps)

lemma ts_indiscrete_\<T>[ts_indiscrete_simps]: "ts_indiscrete A\<lparr>\<T>\<rparr> = set {0, A}"
  unfolding ts_indiscrete_def 
  by (simp add: ts_struct_field_simps nat_omega_simps)

lemma (in \<Z>) \<Z>_ts_ts_indiscrete:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "\<Z>_ts \<alpha> (ts_indiscrete A)"
proof(intro \<Z>_tsI)

  show struct: "\<Z>_vfsequence \<alpha> (ts_indiscrete A)"
  proof(intro \<Z>_vfsequenceI)
    show "vfsequence (ts_indiscrete A)" unfolding ts_indiscrete_def by auto
    show "\<R>\<^sub>\<circ> (ts_indiscrete A) \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    proof(intro vsubsetI)
      fix x assume "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (ts_indiscrete A)" 
      then consider \<open>x = A\<close> | \<open>x = set {0, A}\<close>
        unfolding ts_indiscrete_def by auto
      then show "x \<in>\<^sub>\<circ> Vset \<alpha>" by cases (simp_all add: Axiom_of_Pairing assms)
    qed
  qed (simp_all add: \<Z>_axioms)
  
  interpret struct: \<Z>_vfsequence \<alpha> \<open>ts_indiscrete A\<close> by (rule struct)

  show "X \<subseteq>\<^sub>\<circ> ts_indiscrete A\<lparr>\<T>\<rparr> \<Longrightarrow> \<Union>\<^sub>\<circ>X \<in>\<^sub>\<circ> ts_indiscrete A\<lparr>\<T>\<rparr>" for X
    unfolding ts_indiscrete_simps
  proof-
    assume "X \<subseteq>\<^sub>\<circ> set {0, A}"
    then have "X \<in>\<^sub>\<circ> VPow (set {0, A})" by force
    then consider \<open>X = 0\<close> | \<open>X = set {0}\<close> | \<open>X = set {A}\<close> | \<open>X = set {0, A}\<close>
      by auto
    then show "\<Union>\<^sub>\<circ>X \<in>\<^sub>\<circ> set {0, A}" by cases auto
  qed

  show "2\<^sub>\<nat> \<subseteq>\<^sub>\<circ> vcard (ts_indiscrete A)" unfolding ts_indiscrete_def by fastforce

qed (auto simp: ts_indiscrete_simps)

text\<open>\newpage\<close>

end