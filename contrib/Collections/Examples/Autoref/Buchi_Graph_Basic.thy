theory Buchi_Graph_Basic
imports Main "../../../Automatic_Refinement/Lib/Misc"
begin

text {* Specification of a reachable accepting cycle: *}
definition "has_acc_cycle E A v0 \<equiv> \<exists>v\<in>A. (v0,v)\<in>E\<^sup>* \<and> (v,v)\<in>E\<^sup>+"

subsubsection {* Paths *}
inductive path :: "('v\<times>'v) set \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" for E where
  path0: "path E u [] u"
| path_prepend: "\<lbrakk> (u,v)\<in>E; path E v l w \<rbrakk> \<Longrightarrow> path E u (u#l) w"

lemma path1: "(u,v)\<in>E \<Longrightarrow> path E u [u] v"
  by (auto intro: path.intros)

lemma path_simps[simp]:
  "path E u [] v \<longleftrightarrow> u=v"
  by (auto intro: path0 elim: path.cases)

lemma path_conc: 
  assumes P1: "path E u la v" 
  assumes P2: "path E v lb w"
  shows "path E u (la@lb) w"
  using P1 P2 apply induct 
  by (auto intro: path.intros)
  
lemma path_append:
  "\<lbrakk> path E u l v; (v,w)\<in>E \<rbrakk> \<Longrightarrow> path E u (l@[v]) w"
  using path_conc[OF _ path1] .

lemma path_unconc:
  assumes "path E u (la@lb) w"
  obtains v where "path E u la v" and "path E v lb w"
  using assms 
  thm path.induct
  apply (induct u "la@lb" w arbitrary: la lb rule: path.induct)
  apply (auto intro: path.intros elim!: list_Cons_eq_append_cases)
  done

lemma path_uncons:
  assumes "path E u (u'#l) w"
  obtains v where "u'=u" and "(u,v)\<in>E" and "path E v l w"
  apply (rule path_unconc[of E u "[u']" l w, simplified, OF assms])
  apply (auto elim: path.cases)
  done

lemma path_is_rtrancl: 
  assumes "path E u l v"
  shows "(u,v)\<in>E\<^sup>*"
  using assms 
  by induct auto

lemma rtrancl_is_path:
  assumes "(u,v)\<in>E\<^sup>*"
  obtains l where "path E u l v"
  using assms 
  by induct (auto intro: path0 path_append)

lemma path_is_trancl: 
  assumes "path E u l v"
  and "l\<noteq>[]"
  shows "(u,v)\<in>E\<^sup>+"
  using assms 
  apply induct
  apply auto []
  apply (case_tac l)
  apply auto
  done

lemma trancl_is_path:
  assumes "(u,v)\<in>E\<^sup>+"
  obtains l where "l\<noteq>[]" and "path E u l v"
  using assms 
  by induct (auto intro: path0 path_append)
  

text {* Specification of witness for accepting cycle *}
definition "is_acc_cycle E A v0 v r c 
  \<equiv> v\<in>A \<and> path E v0 r v \<and> path E v c v \<and> c\<noteq>[]"

text {* Specification is compatible with existence of accepting cycle *}
lemma is_acc_cycle_eq:
  "has_acc_cycle E A v0 \<longleftrightarrow> (\<exists>v r c. is_acc_cycle E A v0 v r c)"
  unfolding has_acc_cycle_def is_acc_cycle_def
  by (auto elim!: rtrancl_is_path trancl_is_path
    intro: path_is_rtrancl path_is_trancl)

end
