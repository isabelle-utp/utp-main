(* Author: Nan Jiang *)

section \<open>Soundness and completeness\<close>

theory Dom_Kildall_Correct
imports Dom_Kildall_Property
begin

context dom_sl
begin

lemma entry_dominate_dom: 
  assumes "i \<in> set (g_V G)"
      and "dominate i 0"
    shows "dom i 0" 
  using assms
proof-
  from assms(1) entry0_dominates_all have "dominate 0 i" by auto
  with assms(2) reachable have "i = 0" using reachable_dom_acyclic by (auto simp add:reachable_def)
  then show ?thesis using dom_refl by auto
qed

lemma path_entry_dom: 
  fixes pa i d
  assumes "path_entry (g_E G) pa i"
      and "dom d i"
    shows "d \<in> set pa \<or> d = i" 
  using assms
proof(induct rule:path_entry.induct)
  case path_entry0
  then show ?case using zero_dom_zero by auto
next
  case (path_entry_prepend u v l)
  note u_v = path_entry_prepend.hyps(1)
  note ind = path_entry_prepend.hyps(3)
  note d_v = path_entry_prepend.prems
  show ?case 
  proof(cases "d \<noteq> v")
    case True note d_n_v = this
    from u_v have "v \<in> succs u" by (simp add:succs_def)
    with d_v d_n_v have "dom d u" by (auto intro:adom_succs)
    with ind have "d \<in> set l \<or> d = u" by auto 
    then show ?thesis by auto
  next
    case False 
    then show ?thesis by auto
  qed
qed

\<comment>\<open>soundenss\<close>

lemma dom_sound: "dom i j \<Longrightarrow> dominate i j"
  by (fastforce simp add: dominate_def dest:path_entry_dom)

lemma sdom_sound: "strict_dom i j \<Longrightarrow> j \<in> set (g_V G) \<Longrightarrow> strict_dominate i j"
proof -
  assume sdom: "strict_dom i j" and "j \<in> set (g_V G)" 
  then have i_n_j: "i \<noteq> j" by (rule sdom_asyc)
  from sdom have "dom i j" using sdom_dom by auto
  then have domi: "dominate i j" by (rule dom_sound)  
  with i_n_j show ?thesis by (fastforce dest: dominate_sdominate)
qed


\<comment>\<open>completeness\<close>
 
lemma dom_complete_auxi: "i < length start \<Longrightarrow> (dom_kildall start)!i = ss' \<and> k \<notin> set ss' \<Longrightarrow> non_strict_dominate k i"
proof-
  assume i_lt: "i < length start" and dom_kil: "(dom_kildall start)!i = ss'\<and> k \<notin> set ss'" 
  then have dom_iter: "(fst (iter f step start (unstables r step start)))!i = ss'" and k_nin: "k \<notin> set ss'" 
    using nodes_semi_def r_def f_def step_def dom_kildall_def kildall_def  by auto
  then obtain s w where iter: " iter f step start (unstables r step start) = (s, w)" by fastforce
  with dom_iter have "s!i = ss'" by auto
  with iter_dom_invariant_complete iter k_nin i_lt len_start_is_n
  show ?thesis by auto
qed

lemma notsdom_notsdominate: "\<not> strict_dom i j \<Longrightarrow> j < length start \<Longrightarrow> non_strict_dominate i j"
proof-
  assume i_not_sdom_j: "\<not> strict_dom i j" and j_lt: "j < length start"
  then obtain res where j_res: "dom_kildall start ! j = res" by (auto simp add:strict_dom_def)
  then have "strict_dom i j = (i \<in> set res)" by (auto simp add:strict_dom_def start_def n_def nodes_def)
  with i_not_sdom_j have i_nin: "i \<notin> set res" by auto
  with j_res j_lt show "non_strict_dominate i j" using dom_complete_auxi by fastforce
qed

lemma notsdom_notsdominate': "\<not> strict_dom i j \<Longrightarrow> j < length start \<Longrightarrow> \<not> strict_dominate i j"
  using notsdom_notsdominate nonstrict_eq by auto

lemma dom_complete: "strict_dominate i j \<Longrightarrow> j < size start \<Longrightarrow> strict_dom i j" 
  by (insert notsdom_notsdominate') (auto intro: contrapos_nn nonstrict_eq)

end

end

