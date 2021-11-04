(* Author: Nan Jiang *)

section \<open>The specification of computing dominators\<close>

theory Cfg
imports Main 
begin

text \<open>The specification of computing dominators is defined.
      For fast data flow analysis presented by CHK \cite{Dominance_Algorithm}, 
      a directed graph with explicit node list and sets of initial nodes is defined.
      Each node refers to its rPO (reverse PostOrder) number w.r.t a DFST, and 
      related properties as assumptions are handled using a locale.\<close>

type_synonym 'a digraph = "('a \<times>'a) set"

record 'a graph_rec =
  g_V  :: "'a list"
  g_V0 :: "'a set" 
  g_E  :: "'a digraph"  
 
  tail :: "'a \<times> 'a \<Rightarrow> 'a"
  head :: "'a \<times> 'a \<Rightarrow> 'a"

definition wf_cfg :: "'a graph_rec \<Rightarrow> bool" where
  "wf_cfg G \<equiv> g_V0 G \<subseteq> set( g_V G)"

type_synonym node = nat

locale cfg_doms =
  \<comment>\<open>Nodes are rPO numbers\<close>
  fixes G :: "nat graph_rec" (structure) 

  \<comment>\<open>General properties\<close>
  assumes wf_cfg: "wf_cfg G"
  assumes tail[simp]: "e = (u,v) \<Longrightarrow> tail G e = u"
  assumes head[simp]: "e = (u,v) \<Longrightarrow> head G e = v"
  assumes tail_in_verts[simp]: "e \<in> g_E G \<Longrightarrow> tail G e \<in> set (g_V G)"
  assumes head_in_verts[simp]: "e \<in> g_E G \<Longrightarrow> head G e \<in> set (g_V G)"

  \<comment>\<open>Properties of a cfg where nodes are rPO numbers\<close>
  assumes entry0:    "g_V0 G = {0}"
  assumes dfst:      "\<forall>v \<in> set (g_V G) - {0}. \<exists>prev. (prev, v) \<in> g_E G \<and> prev < v" 
  assumes reachable: "\<forall>v \<in> set (g_V G). v \<in> (g_E G)\<^sup>* `` {0}"    
  assumes verts:     "g_V G = [0 ..< (length (g_V G))]"

 \<comment>\<open>It is required that the entry node has an immediate successor which is not itself;
    Otherwise, no need to compute dominators
    It is required for proving the lemma: "wf\_dom start (unstables r step start)".\<close>
  assumes succ_of_entry0: "\<exists>s. (0,s) \<in> g_E G \<and> s \<noteq> 0"

begin

inductive path_entry :: "nat digraph \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" for E where
  path_entry0: "path_entry E [] 0"
| path_entry_prepend: "\<lbrakk> (u,v)\<in> E; path_entry E l u \<rbrakk> \<Longrightarrow> path_entry E (u#l) v"

lemma path_entry0_empty_conv: "path_entry E [] v \<longleftrightarrow> v = 0" 
 by (auto intro: path_entry0 elim: path_entry.cases)

inductive_cases path_entry_uncons: "path_entry E (u'#l) w"
inductive_simps path_entry_cons_conv: "path_entry E (u'#l) w"

lemma single_path_entry: "path_entry E [p] w \<Longrightarrow> p = 0" 
  by (simp add: path_entry_cons_conv path_entry0_empty_conv)

lemma path_entry_append: 
  "\<lbrakk> path_entry E l v; (v,w)\<in>E \<rbrakk> \<Longrightarrow> path_entry E (v#l) w"
  by (rule path_entry_prepend)

lemma entry_rtrancl_is_path:
  assumes "(0,v) \<in> E\<^sup>*"
  obtains p where "path_entry E p v" 
    using assms 
    by induct (auto intro:path_entry0 path_entry_prepend)

lemma path_entry_is_trancl: 
  assumes "path_entry E l v"
  and "l \<noteq> []"
  shows "(0,v)\<in>E\<^sup>+"
  using assms 
  apply induct
  apply auto []
  apply (case_tac l)
  apply (auto simp add:path_entry0_empty_conv)
  done

lemma tail_is_vert: "(u,v) \<in> g_E G  \<Longrightarrow> u \<in> set (g_V G)"
  by (auto dest: tail_in_verts[of "(u,v)"])

lemma head_is_vert: "(u,v) \<in> g_E G  \<Longrightarrow> v \<in> set (g_V G)"
  by (auto dest: head_in_verts[of "(u,v)"])

lemma tail_is_vert2: "(u,v) \<in> (g_E G)\<^sup>+ \<Longrightarrow> u \<in> set (g_V G)"
  by (induct rule:trancl.induct)(auto dest: tail_in_verts)

lemma head_is_vert2: "(u,v) \<in> (g_E G)\<^sup>+  \<Longrightarrow> v \<in> set (g_V G)"
  by (induct rule:trancl.induct)(auto dest: head_in_verts)

lemma verts_set: "set (g_V G) = {0 ..< length (g_V G)}"   
proof-
  from verts have "set (g_V G) = set [0 ..< (length (g_V G))]" by simp
  also have "set [0 ..< (length (g_V G))] = {0 ..< (length (g_V G))}" by simp
  ultimately show ?thesis by auto
qed

lemma fin_verts: "finite (set (g_V G))" 
  by (auto)

lemma zero_in_verts: "0 \<in> set (g_V G)"
  using wf_cfg entry0 by (unfold wf_cfg_def)  auto

lemma verts_not_empty: "g_V G \<noteq> []"
  using zero_in_verts by auto

lemma len_verts_gt0: "length (g_V G) > 0" 
  by (simp add:verts_not_empty)

lemma len_verts_gt1: "length (g_V G) > 1"
proof-
  from succ_of_entry0 obtain s where "s \<in> set (g_V G)" and "s \<noteq> 0" using head_is_vert by auto
  with zero_in_verts have "{0,s} \<subseteq> set (g_V G)" and c: "card {0, s} > 1" by auto
  then have "card {0, s} \<le> card (set (g_V G))" by (auto simp add:card_mono)
  with c have "card (set (g_V G)) > 1" by simp
  then show ?thesis using card_length[of "g_V G"] by auto
qed

lemma verts_ge_Suc0 : "\<not> [0..<length (g_V G)] = [0]"
proof
  assume "[0..<length (g_V G)] = [0]"
  then have "length [0..<length (g_V G)] = 1" by simp
  with len_verts_gt1 show False by auto
qed

lemma distinct_verts1: "distinct [0..<length (g_V G)] " 
  by simp

lemma distinct_verts2: "distinct (g_V G)" 
  by (insert distinct_verts1 verts)  simp

lemma single_entry: "is_singleton (g_V0 G)" 
  by (simp add:entry0)

lemma entry_is_0: "the_elem (g_V0 G) = 0" 
  by (simp add: entry0)

lemma wf_digraph: "cfg_doms G" by intro_locales

lemma path_entry_prepend_conv: "path_entry (g_E G) p n \<Longrightarrow> p \<noteq> [] \<Longrightarrow> \<exists>v. path_entry (g_E G) (tl p) v \<and> (v, n) \<in> (g_E G)" 
proof (induct rule:path_entry.induct)
  case path_entry0 then show ?case by auto
next
  case (path_entry_prepend u v l) 
  then show ?case by auto
qed

lemma path_verts: "path_entry (g_E G) p n \<Longrightarrow> n \<in> set (g_V G)" 
proof (cases "p = []")
  case True
  assume "path_entry (g_E G) p n" and "p = []"
  then show ?thesis by (simp add:path_entry0_empty_conv zero_in_verts)
next
  case False
  assume "path_entry (g_E G) p n" and "p \<noteq> []"
  then have "(0,n)\<in>(g_E G)\<^sup>+" by (auto simp add:path_entry_is_trancl)
  then show ?thesis using head_is_vert2 by simp
qed

lemma path_in_verts: 
  assumes "path_entry (g_E G) l v"
    shows "set l \<subseteq> set (g_V G)"
  using assms 
proof (induct rule:path_entry.induct)
  case path_entry0 then show ?case by auto
next
  case (path_entry_prepend u v l) 
  then show ?case using path_verts by auto
qed

lemma any_node_exits_path: 
  assumes "v \<in> set (g_V G) "
    shows "\<exists>p. path_entry (g_E G) p v" 
  using assms
proof (cases "v = 0")
  assume "v \<in> set (g_V G)" and "v = 0" 
  have "path_entry (g_E G) [] 0" by (auto simp add:path_entry0)
  then show ?thesis using `v = 0` by auto
next
  assume "v \<in> set (g_V G)" and "v \<noteq> 0" 
  with reachable have "v \<in> (g_E G)\<^sup>* `` {0}" by auto
  then have "(0,v) \<in> (g_E G)\<^sup>*"  by (simp add:Image_iff)
  then show ?thesis by (auto intro:entry_rtrancl_is_path)
qed

lemma entry0_path: "path_entry (g_E G) [] 0"
  by (auto simp add:path_entry.path_entry0)

definition reachable :: "node \<Rightarrow> bool" 
  where "reachable v \<equiv> v \<in> (g_E G)\<^sup>* `` {0}"

lemma path_entry_reachable: 
  assumes "path_entry (g_E G) p n"
    shows "reachable n" 
  using assms reachable 
  by (fastforce intro:path_verts simp add:reachable_def)

lemma nin_nodes_reachable: "n \<notin> set (g_V G) \<Longrightarrow> \<not> reachable n"
proof(rule ccontr)
  assume "n \<notin> set (g_V G)" and nn: " \<not> \<not> reachable n"
  from `n \<notin> set (g_V G)` have "n \<noteq> 0" using verts_set len_verts_gt0 entry0  by auto
  from nn have "reachable n" by auto
  then have "n \<in> (g_E G)\<^sup>* `` {0}" by (simp add: reachable_def)
  then have " (0, n) \<in> (g_E G)\<^sup>* " by (auto simp add:Image_def)  
  with `n \<noteq> 0` have "\<exists>n'. (0,n') \<in> (g_E G)\<^sup>* \<and> (n', n) \<in> (g_E G)" by (auto intro:rtranclE)
  then obtain n' where "(0,n') \<in> (g_E G)\<^sup>* " and " (n', n) \<in> (g_E G)"by auto
  then have "n \<in> set (g_V G)" using head_is_vert by auto
  with `n \<notin> set (g_V G)` show False
    by auto
qed

lemma reachable_path_entry: "reachable n \<Longrightarrow> \<exists>p. path_entry (g_E G) p n" 
proof-
  assume "reachable n"
  then have "(0,n) \<in> (g_E G)\<^sup>*" by (auto simp add:reachable_def Image_iff)
  then have "0 = n \<or> 0 \<noteq> n \<and> (0,n) \<in> (g_E G)\<^sup>+" by (auto simp add: rtrancl_eq_or_trancl)
  then show ?thesis 
  proof
    assume "0 = n" 
    have "path_entry (g_E G) [] 0" by (simp add:path_entry0)
    with `0 = n` show ?thesis by auto
  next
    assume "0 \<noteq> n \<and> (0,n) \<in> (g_E G)\<^sup>+"
    then have "(0,n) \<in> (g_E G)\<^sup>+"  by (auto simp add:rtranclpD)
    then have "n \<in> set (g_V G)" by (simp add:head_is_vert2)
    then show ?thesis by (rule any_node_exits_path)
  qed
qed

lemma path_entry_unconc:
  assumes "path_entry (g_E G) (la@lb) w"
  obtains v where "path_entry (g_E G) lb v"
  using assms 
  apply (induct "la@lb" w arbitrary:la lb rule: path_entry.induct)
   apply (fastforce intro:path_entry.intros)
  by (auto intro:path_entry.intros iff add: Cons_eq_append_conv)

lemma path_entry_append_conv:
  "path_entry (g_E G) (v#l) w \<longleftrightarrow> (path_entry (g_E G) l v \<and> (v,w) \<in> (g_E G))"
proof
  assume "path_entry (g_E G) (v # l) w " 
  then show "path_entry (g_E G) l v \<and> (v, w) \<in> g_E G" 
    by (auto simp add:path_entry_cons_conv)   
next
  assume "path_entry (g_E G) l v \<and> (v, w) \<in> g_E G"
  then show "path_entry (g_E G) (v # l) w " by (fastforce intro: path_entry_append)
qed

lemma takeWhileNot_path_entry:
  assumes "path_entry E p x"
      and "v \<in> set p"
      and "takeWhile ((\<noteq>) v) (rev p) = c"
    shows "path_entry E (rev c) v"
  using assms
proof (induct rule: path_entry.induct)
  case path_entry0 
  then show ?case by auto
next
  case (path_entry_prepend u va l)
  then show ?case
  proof(cases "v \<in> set l")
    case True note v_in = this
    then have "takeWhile ((\<noteq>) v) (rev (u # l)) = takeWhile ((\<noteq>) v) (rev l)" by auto
    with path_entry_prepend.prems(2) have "takeWhile ((\<noteq>) v) (rev l) = c" by simp
    with v_in show ?thesis using path_entry_prepend.hyps(3) by auto
  next
    case False note v_nin = this    
    with path_entry_prepend.prems(1) have v_u: "v = u" by auto
    then have take_eq: "takeWhile ((\<noteq>) v) (rev (u # l)) = takeWhile ((\<noteq>) v) ((rev l) @ [u])"  by auto 
    from v_nin have "\<And>x. x \<in> set (rev l) \<Longrightarrow> ((\<noteq>) v) x" by auto
    then have "takeWhile ((\<noteq>) v) ((rev l) @ [u]) = (rev l) @ takeWhile ((\<noteq>) v) [u]" 
      by (rule takeWhile_append2) simp
    with v_u take_eq have "takeWhile ((\<noteq>) v) (rev (u # l)) = (rev l)" by simp
    then show ?thesis using path_entry_prepend.prems(2) path_entry_prepend.hyps(2) v_u by auto
  qed
qed

lemma path_entry_last: "path_entry (g_E G) p n \<Longrightarrow> p \<noteq> [] \<Longrightarrow> last p = 0" 
  apply (induct rule: path_entry.induct)
   apply simp  
  apply (simp add: path_entry_cons_conv neq_Nil_conv)
  apply (auto simp add:path_entry0_empty_conv)
  done

lemma path_entry_loop: 
  assumes n_path: "path_entry (g_E G) p n"
      and n:      "n \<in> set p "
    shows "\<exists>p'.   path_entry (g_E G) p' n \<and> n \<notin> set p'" 
  using assms
proof -
  let ?c = "takeWhile ((\<noteq>) n) (rev ( p))"
  have "\<forall>z \<in> set ?c. z \<noteq> n" by (auto dest: set_takeWhileD)
  then have n_nin: "n \<notin> set (rev ?c)" by auto
 
  from n_path  obtain v where "path_entry (g_E G) ( p) v" using path_entry_prepend_conv by auto  
  with n have "path_entry (g_E G) (rev ?c) n" by (auto intro:takeWhileNot_path_entry)  
  with n_nin show ?thesis by fastforce
qed

lemma path_entry_hd_edge: 
  assumes "path_entry (g_E G) pa p "   
      and "pa \<noteq> []"
    shows "(hd pa, p) \<in> (g_E G)" 
  using assms
  by (induct rule: path_entry.induct) auto

lemma path_entry_edge: 
  assumes "pa \<noteq> [] "
      and "path_entry (g_E G) pa p "
    shows "\<exists>u\<in>set pa. (path_entry (g_E G) (rev (takeWhile ((\<noteq>) u) (rev pa))) u) \<and> (u,p) \<in> (g_E G)"
  using assms
proof-
  from assms have 1: "path_entry (g_E G) (rev (takeWhile ((\<noteq>) (hd pa)) (rev pa))) (hd pa)" by (auto intro:takeWhileNot_path_entry)
  from assms have 2: "(hd pa, p)\<in> (g_E G)" by (auto intro: path_entry_hd_edge)
  have "hd pa \<in> set pa" using assms(1) by auto
  with 1 2 show ?thesis by auto
qed

definition is_tail :: "node \<Rightarrow> node \<times> node \<Rightarrow> bool"
  where "is_tail v e = (v = tail G e)"

definition is_head :: "node \<Rightarrow> node \<times> node \<Rightarrow> bool"
  where "is_head v e = (v = head G e)"

definition succs:: "node \<Rightarrow> node set"
  where "succs v = (g_E G) `` {v}"

lemma succ_in_verts: "s \<in> succs n \<Longrightarrow> {s,n} \<subseteq> set (g_V G)"
  by( simp add:succs_def tail_is_vert head_is_vert)

lemma succ0_not_nil: "succs 0 \<noteq> {}"
  using succ_of_entry0 by (auto simp add:succs_def)

definition prevs:: "node \<Rightarrow> node set" where
  "prevs v = (converse (g_E G))`` {v}"

lemma "v \<in> succs u \<longleftrightarrow> u \<in> prevs v"
  by (auto simp add:succs_def prevs_def)

lemma succ_edge: "\<forall>v \<in> succs n. (n,v) \<in> g_E G"
  by (auto simp add:succs_def)

lemma prev_edge: "u \<in> set (g_V G) \<Longrightarrow> \<forall>v \<in> prevs u. (v, u) \<in> g_E G"
  by (auto simp add:prevs_def)

lemma succ_in_G: "\<forall>v \<in> succs n. v \<in> set (g_V G)"  
  by (auto simp add: succs_def dest:head_in_verts)

lemma succ_is_subset_of_verts: "\<forall>v \<in> set (g_V G). succs v \<subseteq> set(g_V G)"
  by (insert succ_in_G) auto

lemma fin_succs: "\<forall>v \<in> set (g_V G). finite (succs v)"
  by (insert succ_is_subset_of_verts) (auto intro:rev_finite_subset)

lemma fin_succs': "v < length (g_V G) \<Longrightarrow> finite (succs v)" 
  by (subgoal_tac "v \<in> set (g_V G)")
   (auto simp add: fin_succs verts_set)

lemma succ_range: "\<forall>v \<in> succs n. v < length (g_V G)" 
  by (insert succ_in_G verts_set) auto

lemma path_entry_gt: 
  assumes "\<forall>p. path_entry E p n \<longrightarrow> d \<in> set p"
      and "\<forall>p. path_entry E p n' \<longrightarrow> n \<in> set p"
    shows "\<forall>p. path_entry E p n' \<longrightarrow> d \<in> set p" 
  using assms
proof (intro strip)
  fix p
  let ?npath = "takeWhile ((\<noteq>) n) (rev p)" 
  have sub: "set ?npath \<subseteq> set p" apply (induct p) by (auto dest:set_takeWhileD)

  assume ass: "path_entry E p n' "
  with assms(2) have n_in_p: "n \<in> set p" by auto
  then have "n \<in> set (rev p)" by auto
  with ass have "path_entry E (rev ?npath) n" 
    using takeWhileNot_path_entry by auto
  with assms(1) have "d \<in> set ?npath" by fastforce   
  with sub show "d \<in> set p" by auto
qed

definition dominate :: "nat \<Rightarrow> nat \<Rightarrow> bool" 
  where "dominate n1 n2 \<equiv>
         \<forall>pa. path_entry (g_E G) pa n2 \<longrightarrow> 
         (n1 \<in> set pa \<or> n1 = n2)"

definition strict_dominate:: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "strict_dominate n1 n2 \<equiv> 
   \<forall>pa. path_entry (g_E G) pa n2 \<longrightarrow> 
   (n1 \<in> set pa \<and> n1 \<noteq> n2)"

lemma any_dominate_unreachable: "\<not> reachable n \<Longrightarrow> dominate d n"
proof(unfold reachable_def dominate_def)
  assume ass: "n \<notin> (g_E G)\<^sup>* `` {0}"

  have "\<not> (\<exists>p. path_entry (g_E G) p n)" 
  proof (rule ccontr)
    assume " \<not> (\<not> (\<exists>p. path_entry (g_E G) p n))"
    then obtain p where p: "path_entry (g_E G) p n" by auto
    then have "n = 0 \<or> reachable n" by (auto intro:path_entry_reachable)
    then show False
    proof
      assume "n = 0" 
      then show False using ass by auto
    next
      assume "reachable n" 
      then show False using ass by (auto simp add:reachable_def)
    qed
  qed
  then show "\<forall>pa. path_entry (g_E G) pa n \<longrightarrow> d \<in> set pa \<or> d = n" by auto
qed

lemma any_sdominate_unreachable: "\<not> reachable n \<Longrightarrow> strict_dominate d n"
proof(unfold reachable_def strict_dominate_def)
  assume ass:"n \<notin> (g_E G)\<^sup>* `` {0} "

  have "\<not> (\<exists>p. path_entry (g_E G)  p n)" 
  proof (rule ccontr)
    assume " \<not> (\<not> (\<exists>p. path_entry (g_E G) p n))"
    then obtain p where p: "path_entry (g_E G) p n" by auto
    then have "n = 0 \<or> reachable n" by (auto intro:path_entry_reachable)
    then show False    
    proof 
      assume "n = 0" 
      then show False using ass by auto
    next
      assume "reachable n" 
      then show False using ass by (auto simp add:reachable_def)
    qed
  qed
  then show "\<forall>pa. path_entry (g_E G)  pa n \<longrightarrow> d \<in> set pa \<and> d \<noteq> n" by auto
qed

lemma dom_reachable: "reachable n \<Longrightarrow> dominate d n \<Longrightarrow> reachable d"
proof -
  assume reach_n: "reachable n"
     and dom_n: "dominate d n" 
  from reach_n have "\<exists>p. path_entry (g_E G)  p n" by (rule reachable_path_entry)
  then obtain p where p: "path_entry (g_E G) p n" by auto

  show "reachable d"
  proof (cases "d \<noteq> n")
    case True     
    with dom_n p have d_in: "d \<in> set p" by (auto simp add:dominate_def)
    let ?pa = "takeWhile ((\<noteq>) d) (rev p)"
    from d_in p have "path_entry (g_E G) (rev ?pa) d" using takeWhileNot_path_entry by auto
    then show ?thesis using path_entry_reachable by auto
  next
    case False
    with reach_n show ?thesis by auto
  qed
qed

lemma dominate_refl: "dominate n n" 
  by (simp add:dominate_def)

lemma entry0_dominates_all: "\<forall>p \<in> set (g_V G). dominate 0 p"  
proof(intro strip)  
  fix p 
  assume "p \<in> set (g_V G)"
  show "dominate 0 p" 
  proof (cases "p = 0")
    case True
    then show ?thesis by (auto simp add:dominate_def)
  next
    case False
    assume p_neq0: "p \<noteq> 0"
    have "\<forall>pa. path_entry (g_E G) pa p \<longrightarrow> 0 \<in> set pa"
    proof (intro strip)
      fix pa
      assume path_p: "path_entry (g_E G) pa p"
      show "0 \<in> set pa"
      proof (cases "pa \<noteq> []")
        case True note pa_n_nil = this
        with path_p have last_pa: "last pa = 0" using path_entry_last by auto
        from pa_n_nil have "last pa \<in> set pa" by simp
        with last_pa show ?thesis by simp
      next
        case False 
        with path_p have "p = 0" by (simp add:path_entry0_empty_conv)
        with p_neq0 show ?thesis by auto
      qed
    qed
    then show ?thesis by (auto simp add:dominate_def)
  qed
qed

lemma "strict_dominate i j \<Longrightarrow> j \<in> set (g_V G) \<Longrightarrow> i \<noteq> j" 
  using  any_node_exits_path
  by (auto simp add:strict_dominate_def)

definition non_strict_dominate:: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "non_strict_dominate n1 n2 \<equiv> \<exists>pa. path_entry (g_E G) pa n2 \<and> (n1 \<notin> set pa)"

lemma any_sdominate_0: "n \<in> set (g_V G) \<Longrightarrow> non_strict_dominate n 0"
  apply (simp add:non_strict_dominate_def)
  by (auto intro:path_entry0)

(*
lemma non_strict_dominate_refl: "n \<in> set (g_V G) \<Longrightarrow> non_strict_dominate n n"
proof(unfold non_strict_dominate_def)
  assume n_in: "n \<in> set (g_V G)"
  then obtain p where p_n: "path_entry (g_E G) p n" using any_node_exits_path by auto

  have pa0: "path_entry (g_E G) [] 0" by (rule path_entry0)

  show "\<exists>pa. path_entry (g_E G) pa n \<and> n \<notin> set pa"
  proof(cases "n = 0")
    case True 
    then show ?thesis using pa0 by (auto simp add:non_strict_dominate_def)
  next 
    case False note n_neq_0 = this 
    with p_n have "p \<noteq> []" using path_entry0_empty_conv by auto 
    then show ?thesis using p_n by (auto intro: path_entry_loop)    
  qed
qed
*)
lemma non_sdominate_succ: "(i,j ) \<in> g_E G \<Longrightarrow> k \<noteq> i \<Longrightarrow> non_strict_dominate k i \<Longrightarrow> non_strict_dominate k j" 
proof -
  assume i_j: "(i,j ) \<in> g_E G" and k_neq_i: "k \<noteq> i" and "non_strict_dominate k i"
  then obtain pa where "path_entry (g_E G) pa i" and k_nin_pa: "k \<notin> set pa" by (auto simp add:non_strict_dominate_def)
  with i_j have "path_entry (g_E G) (i#pa) j" by (auto simp add:path_entry_prepend)
  with k_neq_i k_nin_pa show ?thesis by (auto simp add:non_strict_dominate_def)
qed

lemma any_node_non_sdom0: "non_strict_dominate k 0"
  by (auto intro:entry0_path simp add:non_strict_dominate_def)

lemma nonstrict_eq: "non_strict_dominate i j \<Longrightarrow> \<not> strict_dominate i j" 
  by (auto simp add:non_strict_dominate_def strict_dominate_def)

lemma dominate_trans: 
  assumes "dominate n1 n2"
      and "dominate n2 n3"
    shows "dominate n1 n3"
  using assms
proof(cases "n1 = n2")
  case True
  then show ?thesis using assms(2) by auto
next
  case False
  then show "dominate n1 n3"
  proof (cases "n1 = n3")
    case True
    then show ?thesis by (auto simp add:dominate_def)
  next
    case False
    show "dominate n1 n3" 
    proof (cases "n2 = n3")
      case True
      then show ?thesis using assms(1) by auto
    next
      case False
      with `n1 \<noteq> n2` `n1 \<noteq> n3` show ?thesis
      proof (auto simp add: dominate_def)
        fix pa
        assume "n1 \<noteq> n2" and "n1 \<noteq> n3" and "n2 \<noteq> n3"
        from `n1 \<noteq> n2` assms(1) have n1_n2_pa: "\<forall>pa. path_entry (g_E G) pa n2 \<longrightarrow> n1 \<in> set pa" 
          by (auto simp add:dominate_def)
        from `n2 \<noteq> n3` assms(2) have "\<forall>pa. path_entry (g_E G) pa n3 \<longrightarrow> n2 \<in> set pa" 
          by (auto simp add:dominate_def)
        with n1_n2_pa have "\<forall>pa. path_entry (g_E G) pa n3 \<longrightarrow> n1 \<in> set pa" 
          by (rule path_entry_gt)
        then show "\<And>pa. path_entry (g_E G) pa n3 \<Longrightarrow> n1 \<in> set pa" by auto
      qed
    qed
  qed
qed

lemma len_takeWhile_lt: "x \<in> set xs \<Longrightarrow> length (takeWhile ((\<noteq>) x) xs) < length xs"
  by (induct xs) auto

lemma len_takeWhile_comp: 
  assumes "n1 \<in> set xs"
      and "n2 \<in> set xs"
      and "n1 \<noteq> n2"
    shows "length (takeWhile ((\<noteq>) n1) xs) \<noteq> length (takeWhile ((\<noteq>) n2) xs)"
  using assms
  by (induct xs) auto

lemma len_takeWhile_comp1: 
  assumes "n1 \<in> set xs"
      and "n2 \<in> set xs"
      and "n1 \<noteq> n2"
    shows "length (takeWhile ((\<noteq>) n1) (rev (x # xs))) \<noteq> length (takeWhile ((\<noteq>) n2) (rev (x # xs)))"
  using assms len_takeWhile_comp[of "n1" "rev xs" "n2"] by fastforce

lemma len_takeWhile_comp2: 
  assumes "n1 \<in> set xs"
      and "n2 \<notin> set xs"
    shows "length (takeWhile ((\<noteq>) n1) (rev (x # xs))) \<noteq> length (takeWhile ((\<noteq>) n2) (rev (x # xs)))"
  using assms
proof-
  let ?xs1 = "takeWhile ((\<noteq>) n1) (rev (x # xs))"
  let ?xs2 = "takeWhile ((\<noteq>) n2) (rev (x # xs))"
  from assms have len1: "length (takeWhile ((\<noteq>) n1) (rev xs)) < length (rev xs)" 
    using len_takeWhile_lt[of _"rev xs"] by auto

  from assms(1) have "?xs1 = takeWhile ((\<noteq>) n1) (rev xs)" by auto
  then have len2: "length ?xs1 < length (rev xs)" using len1 by auto
  
  from assms(2) have "takeWhile ((\<noteq>) n2) (rev xs @ [x]) = (rev xs) @ takeWhile ((\<noteq>) n2) [x]" 
    by (fastforce intro:takeWhile_append2)
  then have "?xs2 = (rev xs) @ takeWhile ((\<noteq>) n2) [x]" by simp
  then show ?thesis using len2 by auto 
qed

lemma len_compare1: 
  assumes "n1 = x" and "n2 \<noteq> x"
    shows "length (takeWhile ((\<noteq>) n1) (rev (x # xs))) \<noteq> length (takeWhile ((\<noteq>) n2) (rev (x # xs)))"
  using assms
proof(cases "n1 \<in> set xs \<and> n2 \<in> set xs")
  case True
  with assms show ?thesis using len_takeWhile_comp1 by fastforce
next
  let ?xs1 = "takeWhile ((\<noteq>) n1) (rev (x # xs))"
  let ?xs2 = "takeWhile ((\<noteq>) n2) (rev (x # xs))"

  case False
  then have "n1 \<in> set xs \<and> n2 \<notin> set xs \<or> n1 \<notin> set xs \<and> n2 \<in> set xs \<or> n1 \<notin> set xs \<and> n2 \<notin>  set xs" by auto
  then show ?thesis
  proof
    assume "n1 \<in> set xs \<and> n2 \<notin> set xs"
    then show ?thesis by (fastforce dest: len_takeWhile_comp2)
  next
    assume "n1 \<notin> set xs \<and> n2 \<in> set xs \<or> n1 \<notin> set xs \<and> n2 \<notin> set xs"
    then show ?thesis 
    proof
      assume "n1 \<notin> set xs \<and> n2 \<in> set xs"
      then have n1: "n1 \<notin> set xs" and n2: "n2 \<in> set xs" by auto
      have "length ?xs2 \<noteq> length ?xs1" using len_takeWhile_comp2[OF n2 n1] by auto
      then show ?thesis by simp
    next
      assume "n1 \<notin> set xs \<and> n2 \<notin> set xs"
      then have n1_nin: "n1 \<notin> set xs" and n2_nin: "n2 \<notin> set xs" by auto
      then  have t1: "takeWhile ((\<noteq>) n1) (rev xs @ [x]) = (rev xs) @ takeWhile  ((\<noteq>) n1) [x]" 
             and     "takeWhile ((\<noteq>) n2) (rev xs @ [x]) = (rev xs) @ takeWhile  ((\<noteq>) n2) [x]" 
        by (fastforce intro:takeWhile_append2)+
      with `n1 = x` `n2 \<noteq> x`  have t1': "takeWhile ((\<noteq>) n1) (rev xs @ [x]) = rev xs" 
                               and      "takeWhile ((\<noteq>) n2) (rev xs @ [x]) = (rev xs) @ [x]" by auto      
      then have "length (takeWhile ((\<noteq>) n2) (rev xs @ [x])) = length ((rev xs) @ [x])" 
        using arg_cong[of "takeWhile ((\<noteq>) n2) (rev xs @ [x])" "rev xs @ [x]" "length"] by fastforce       
      with t1' show ?thesis by auto
    qed
  qed
qed

lemma len_compare2: 
  assumes "n1 \<in> set xs"
      and "n1 \<noteq> n2"
    shows "length (takeWhile ((\<noteq>) n1) (rev (x # xs))) \<noteq> length (takeWhile ((\<noteq>) n2) (rev (x # xs)))"
  using assms 
  apply(case_tac "n2 \<in> set xs") 
   apply (fastforce dest: len_takeWhile_comp1 ) 
  apply (fastforce dest:len_takeWhile_comp2)
  done

lemma len_takeWhile_set: 
  assumes "length (takeWhile ((\<noteq>) n1) xs) > length (takeWhile ((\<noteq>) n2) xs)"
      and "n1 \<noteq> n2"
      and "n1 \<in> set xs" 
      and "n2 \<in> set xs"
    shows "set (takeWhile ((\<noteq>) n2) xs)  \<subseteq> set (takeWhile ((\<noteq>) n1) xs)"
  using assms
proof (induct xs)
  case Nil then show ?case by auto
next
  case (Cons y ys)
  note ind_hyp = Cons(1)
  note len_n2_lt_n1_y_ys = Cons(2)
  note n1_n_n2 = Cons(3)
  note n1_in_y_ys = Cons(4)
  note n2_in_y_ys = Cons(5)
 
  let ?ys1_take = "takeWhile ((\<noteq>) n1) ys"
  let ?ys2_take = "takeWhile ((\<noteq>) n2) ys"

  show ?case
  proof(cases "n1 \<in> set ys")
    case True note n1_in_ys = this
    show ?thesis 
    proof(cases "n2 \<in> set ys")
      case True note n2_in_ys = this
      show ?thesis 
      proof (cases "n1 \<noteq> y")
        case True note n1_neq_y = this
        show ?thesis 
        proof (cases "n2 \<noteq> y")
          case True note n2_neq_y = this
          from len_n2_lt_n1_y_ys have "length ?ys2_take < length ?ys1_take" 
            using n1_n_n2 n1_in_ys n2_in_ys n1_neq_y n2_neq_y by (induct ys) auto
          from ind_hyp[OF this n1_n_n2 n1_in_ys n2_in_ys]
          have "set (takeWhile ((\<noteq>) n2) ys) \<subseteq> set (takeWhile ((\<noteq>) n1) ys)" by auto
          then show ?thesis using n1_neq_y n2_neq_y by (induct ys) auto
        next
          case False
          with n1_n_n2 show ?thesis by auto
        qed
      next
        case False 
        with n1_n_n2 show ?thesis using len_n2_lt_n1_y_ys by auto
      qed
    next
      case False
      with n2_in_y_ys have "n2 = y" by auto
      then show ?thesis by auto
    qed
  next
    case False
    with n1_in_y_ys have "n1 = y" by auto
    with n1_n_n2 show ?thesis using len_n2_lt_n1_y_ys by auto
  qed
qed
    
lemma reachable_dom_acyclic:
  assumes "reachable n2"
      and "dominate n1 n2"
      and "dominate n2 n1"
    shows "n1 = n2" 
  using assms 
proof -
  from assms(1) assms(2) have "reachable n1" by (auto intro: dom_reachable)
  then have "\<exists>pa. path_entry (g_E G) pa n1" by (auto intro: reachable_path_entry)
  then obtain pa where pa: "path_entry (g_E G) pa n1" by auto

  let ?n_take_n1 = "takeWhile ((\<noteq>) n1) (rev pa)"
  let ?n_take_n2 = "takeWhile ((\<noteq>) n2) (rev pa)"

  show "n1 = n2" 
  proof(rule ccontr)
    assume n1_neq_n2:  "n1 \<noteq> n2" 
    then have pa_n1_n2: "\<forall>pa. path_entry (g_E G) pa n2 \<longrightarrow> n1 \<in> set pa" 
          and pa_n2_n1: "\<forall>pa. path_entry (g_E G)  pa n1 \<longrightarrow> n2 \<in> set pa" using assms(2) assms(3)
      by (auto simp add:dominate_def)
    then have n1_n1_pa: "\<forall>pa. path_entry (g_E G)  pa n1 \<longrightarrow> n1 \<in> set pa" by (rule path_entry_gt)
    with pa pa_n2_n1 have n1_in_pa: "n1 \<in> set pa" 
                      and n2_in_pa: "n2 \<in> set pa" by auto
    with n1_neq_n2 have len_neq: "length ?n_take_n1 \<noteq> length ?n_take_n2" 
      by (auto simp add: len_takeWhile_comp)
    
    from pa n1_in_pa n2_in_pa have path1: "path_entry (g_E G) (rev ?n_take_n1) n1"  
                               and path2: "path_entry (g_E G) (rev ?n_take_n2) n2"  
      using takeWhileNot_path_entry by auto

    have n1_not_in: "n1 \<notin> set ?n_take_n1" by (auto dest: set_takeWhileD[of _ _ "rev pa"])
    have n2_not_in: "n2 \<notin> set ?n_take_n2" by (auto dest: set_takeWhileD[of _ _ "rev pa"])

    show False
    proof(cases "length ?n_take_n1 > length ?n_take_n2")
      case True
      then have "set ?n_take_n2 \<subseteq> set ?n_take_n1" 
        using n1_in_pa n2_in_pa by (auto dest: len_takeWhile_set[of _ "rev pa"])       
      then have "n1 \<notin> set ?n_take_n2 " using n1_not_in by auto
      with path2 show False using pa_n1_n2 by auto
    next
      case False
      with len_neq have "length ?n_take_n2 > length ?n_take_n1" by auto
      then have "set ?n_take_n1 \<subseteq> set ?n_take_n2" 
        using n1_neq_n2 n2_in_pa n1_in_pa  by (auto dest: len_takeWhile_set)  
      then have "n2 \<notin> set ?n_take_n1 " using n2_not_in by auto
      with path1 show False using pa_n2_n1 by auto
    qed
  qed
qed

lemma sdom_dom: "strict_dominate n1 n2 \<Longrightarrow> dominate n1 n2" 
  by (auto simp add:strict_dominate_def dominate_def)

lemma dominate_sdominate: "dominate n1 n2 \<Longrightarrow> n1 \<noteq> n2 \<Longrightarrow> strict_dominate n1 n2" 
  by (auto simp add:strict_dominate_def dominate_def)

lemma sdom_neq: 
  assumes "reachable n2"
      and "strict_dominate n1 n2"
    shows "n1 \<noteq> n2" 
  using assms
proof -
  from assms(1) have "\<exists>p. path_entry (g_E G)  p n2" by (rule reachable_path_entry) 
  then obtain p where "path_entry (g_E G)  p n2" by auto
  with assms(2) show ?thesis by (auto simp add:strict_dominate_def)
qed
  
lemma reachable_dom_acyclic2:
  assumes "reachable n2 "
      and "strict_dominate n1 n2"
    shows "\<not> dominate n2 n1" 
  using assms
proof -
  from assms have n1_dom_n2: "dominate n1 n2" and n1_neq_n2: "n1 \<noteq> n2" 
    by (auto simp add:sdom_dom sdom_neq)
  with assms(1) have "dominate n2 n1 \<Longrightarrow> n1 = n2" using reachable_dom_acyclic by auto
  with n1_neq_n2 show ?thesis by auto
qed

lemma not_dom_eq_not_sdom: "\<not> dominate n1 n2 \<Longrightarrow> \<not> strict_dominate n1 n2" 
  by (auto simp add:strict_dominate_def dominate_def)

lemma reachable_sdom_acyclic:
  assumes "reachable n2"
      and "strict_dominate n1 n2"
    shows "\<not> strict_dominate n2 n1" 
  using assms 
  apply (insert reachable_dom_acyclic2[OF assms(1) assms(2)])
  by (auto simp add:not_dom_eq_not_sdom) 

lemma strict_dominate_trans1: 
  assumes "strict_dominate n1 n2" 
      and "dominate n2 n3" 
    shows "strict_dominate n1 n3" 
  using assms
proof (cases "reachable n2")
  case True note reach_n2 = this
  with assms(1) have n1_dom_n2: "dominate n1 n2" and n1_neq_n2: "n1 \<noteq> n2"
    by (auto simp add:sdom_dom sdom_neq)
  with assms(2) have n1_dom_n3: "dominate n1 n3" by (auto intro: dominate_trans)
  have n1_neq_n3: "n1 \<noteq> n3"
  proof (rule ccontr)
    assume "\<not> n1 \<noteq> n3" then have "n1 = n3" by simp
    with assms(2) have n2_dom_n1: "dominate n2 n1" by simp
    with reach_n2 n1_dom_n2 have "n1 = n2" by (auto dest:reachable_dom_acyclic)
    with n1_neq_n2 show False by auto
  qed
  with n1_dom_n3 show ?thesis by (simp add:strict_dominate_def dominate_def)
next
  case False note not_reach_n2 = this
  have "\<not> reachable n3" 
  proof (rule ccontr)
    assume "\<not> \<not> reachable n3 " 
    with assms(2) have "reachable n2" by (auto intro: dom_reachable)
    with not_reach_n2 show False by auto
  qed
  then show ?thesis by (auto intro:any_sdominate_unreachable)
qed

lemma strict_dominate_trans2: 
  assumes "dominate n1 n2" 
      and "strict_dominate n2 n3" 
    shows "strict_dominate n1 n3" 
  using assms
proof (cases "reachable n3")
  case True
  with assms(2) have n2_dom_n3: "dominate n2 n3" and n1_neq_n2: "n2 \<noteq> n3"
    by (auto simp add:sdom_dom sdom_neq)
  with assms(1) have n1_dom_n3: "dominate n1 n3" by (auto intro: dominate_trans)
  have n1_neq_n3: "n1 \<noteq> n3"
  proof (rule ccontr)
    assume "\<not> n1 \<noteq> n3" then have "n1 = n3" by simp
    with assms(1) have "dominate n3 n2" by simp
    with `reachable n3` n2_dom_n3 have "n2 = n3" by (auto dest:reachable_dom_acyclic)
    with n1_neq_n2 show False by auto
  qed
  with n1_dom_n3 show ?thesis by (simp add:strict_dominate_def dominate_def)
next
  case False
  then have "\<not> reachable n3" by simp
  then show ?thesis by (auto intro:any_sdominate_unreachable)
qed

lemma strict_dominate_trans: 
  assumes "strict_dominate n1 n2"
      and "strict_dominate n2 n3"
    shows "strict_dominate n1 n3"
  using assms
  apply(subgoal_tac "dominate n2 n3")
   apply(rule strict_dominate_trans1)
  apply (auto simp add: strict_dominate_def dominate_def)
  done

lemma sdominate_dominate_succs: 
  assumes i_sdom_j:    "strict_dominate i j"
      and j_in_succ_k: "j \<in> succs k"
    shows              "dominate i k"
proof (rule ccontr)
  assume ass:"\<not> dominate i k" 
  then obtain p where path_k: "path_entry (g_E G)  p k" and i_nin_p: "i \<notin> set p" by (auto simp add:dominate_def)
  with j_in_succ_k i_sdom_j have i: "i = k \<or> i = j" by (auto intro:path_entry_append simp add:succs_def strict_dominate_def)

  from j_in_succ_k have "reachable j" using succ_in_verts reachable by (auto simp add:reachable_def)
  with i_sdom_j have "i \<noteq> j" by (auto simp add: sdom_neq)
  with i have "i = k" by auto
  then have "dominate i k" by (auto simp add:dominate_refl)
  with ass show False by auto
qed

end

end