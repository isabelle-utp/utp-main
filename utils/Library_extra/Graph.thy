header {* Graphs and Paths *}

theory Graph
imports Main
begin

type_synonym vertex = int

type_synonym 'a table = "'a list" 
type_synonym graph = "(int list) table"
type_synonym edge = "vertex * vertex"

definition indices :: "'a table \<Rightarrow> int list" where
"indices x = [0..int(length x - 1)]"

definition vertices :: "graph \<Rightarrow> vertex list" where
"vertices = indices"

lemma vetices_distinct: "distinct(vertices G)"
  by (simp add: vertices_def indices_def)

lemma vetices_sorted: "sorted(vertices G)"
  by (simp add: vertices_def indices_def)

definition edges :: "graph \<Rightarrow> edge list" where
"edges g = [ (v, w). v <- vertices g, w <- g!nat(v) ]"

definition graph_rel :: "graph \<Rightarrow> vertex rel" where
"graph_rel G = set(edges G)"

definition before :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
"before x y xs = (\<exists> i j. i < j \<and> j < length(xs) \<and> xs!i = x \<and> xs!j = y)"

lemma before_trans: "\<lbrakk> distinct xs; before x y xs; before y z xs \<rbrakk> \<Longrightarrow> before x z xs"
  apply (auto simp add: before_def)
  apply (rule_tac x="i" in exI)
  apply (rule_tac x="ja" in exI)
  apply (auto)
  apply (metis less_trans nth_eq_iff_index_eq)
done

lemma distinct_not_before_self:
  "distinct(xs) \<Longrightarrow> before x x xs \<Longrightarrow> False"
  by (auto simp add: before_def distinct_conv_nth)

lemma distinct_no_cycle:
  "distinct(xs) \<Longrightarrow> before x y xs \<Longrightarrow> before y x xs \<Longrightarrow> False"
  apply (auto simp add: before_def distinct_conv_nth)
  apply (metis less_trans not_less_iff_gr_or_eq)
done

lemma hd_before_last: "length(xs) \<ge> 2 \<Longrightarrow> before (hd xs) (last xs) xs"
  apply (auto simp add:before_def)
  apply (rule_tac x="0" in exI)
  apply (rule_tac x="length xs - 1" in exI)
  apply (auto)
  apply (metis hd_conv_nth list.size(3) not_numeral_le_zero)
  apply (metis One_nat_def last_conv_nth list.size(3) not_numeral_le_zero)
done

definition is_topological_order :: "int list \<Rightarrow> graph \<Rightarrow> bool" where
"is_topological_order xs G = (distinct(xs) \<and> set(xs) = set(vertices(G)) \<and> (\<forall> (x, y) \<in> set(edges(G)). before x y xs))" 

inductive path :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<turnstile> _ -<_>\<rightarrow> _" [100, 0, 0, 101] 101) where 
unit_path [intro]: "(a, b) \<in> R \<Longrightarrow> R \<turnstile> a -<[a, b]>\<rightarrow> b" | 
step_path [intro]: "\<lbrakk> (a, b) \<in> R; R \<turnstile> b -<p>\<rightarrow> c \<rbrakk> \<Longrightarrow> R \<turnstile> a -<a # p>\<rightarrow> c"

lemma path_concat_list: "\<lbrakk> R \<turnstile> a -<p>\<rightarrow> b; (b, c) \<in> R \<rbrakk> \<Longrightarrow> R \<turnstile> a -<p @ [c]>\<rightarrow> c"
  by (induct rule: path.induct, auto)

lemma trancl_implies_path:
  assumes "(a, b) \<in> R\<^sup>+"
  obtains p where "R \<turnstile> a -<p>\<rightarrow> b"
using assms proof (induct rule: trancl_induct)
  case base thus ?case
    by (auto)
next
  case (step b c) thus ?case
    by (meson path_concat_list)
qed

lemma path_implies_trancl:
  assumes "R \<turnstile> a -<p>\<rightarrow> b"
  shows "(a, b) \<in> R\<^sup>+"
  using assms by (induct rule: path.induct, auto)

lemma trancl_iff_path:
  "(a, b) \<in> R\<^sup>+ \<longleftrightarrow> (\<exists> p. R \<turnstile> a -<p>\<rightarrow> b)"
  by (meson path_implies_trancl trancl_implies_path)
  


(*
lemma path_chop: "\<lbrakk> R \<turnstile> a -<p>\<rightarrow> b; length p > 2 \<rbrakk>

finpath p R; length p > 2 \<rbrakk> \<Longrightarrow> finpath (tl p) R"
  apply (induct rule: finpath.induct)
  apply (simp_all)
done
*)

lemma finpath_init_pair: "R \<turnstile> a -<p>\<rightarrow> b \<Longrightarrow> (a, p!1) \<in> R"
  by (induct rule: path.induct, auto)
  
lemma finpath_pairs: 
  assumes "finpath p R" "i \<le> length p - 2"
  shows "(p!i, p!(Suc i)) \<in> R"
proof -
  from assms(1) have "\<forall> i \<le> length p - 2. (p!i, p!(Suc i)) \<in> R"
    apply (induct rule: finpath.induct)
    apply (auto)
    apply (case_tac "i > 0")
    apply (auto)
  done
  with assms(2) show ?thesis by auto
qed


lemma finpath_elems: "\<lbrakk> finpath p R; i < j; j \<le> length p - 2 \<rbrakk> \<Longrightarrow> (p!i, p!j) \<in> R\<^sup>+"
  apply (induct j)
  apply (auto)
  apply (metis Suc_leD finpath_pairs less_Suc_eq trancl.r_into_trancl trancl.trancl_into_trancl)
done

lemma trancl_finpath:
  assumes "(x, y) \<in> R\<^sup>+"
  shows "\<exists> xs. finpath xs R \<and> hd(xs) = x \<and> last(xs) = y"
  using assms
  apply (erule_tac trancl_induct)
  apply (force)
  apply (auto)
  apply (rule_tac x="xs @ [z]" in exI)
  apply (auto)
  apply (rule finpath_concat_last)
  apply (auto)
  apply (metis finpath.cases hd_append2 list.distinct(2))
done

lemma trancl_finpathE:
  "\<lbrakk> (x, y) \<in> R\<^sup>+; \<And> xs. \<lbrakk> finpath xs R; hd(xs) = x; last(xs) = y \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis trancl_finpath)
  
lemma before_topological_order: "\<lbrakk> is_topological_order xs G; (x, y) \<in> (graph_rel(G))\<^sup>+ \<rbrakk> \<Longrightarrow> before x y xs"
  apply (auto simp add: is_topological_order_def graph_rel_def)
  apply (induct rule: trancl_induct)
  apply (auto)
  apply (metis before_trans old.prod.case)
done

theorem topological_order_acyclic:
  assumes "is_topological_order xs G"
  shows "acyclic(graph_rel(G))"
proof (rule acyclicI, clarify)
  fix x
  assume "(x, x) \<in> (graph_rel G)\<^sup>+"
  moreover then obtain p where finp: "finpath p (graph_rel(G))" "hd(p) = x" "last(p) = x"
    by (metis trancl_finpathE)
  moreover have "\<forall> j \<le> length p - 2. \<forall> i < j. before (p!i) (p!j) xs"
  proof -
    have "\<forall> j \<le> length p - 2. \<forall> i < j. (p!i, p!j) \<in> (graph_rel(G))\<^sup>+"
      by (metis finp(1) finpath_elems)
    with assms show ?thesis
      by (metis before_topological_order)
  qed
  ultimately have "before x x xs"
    by (metis assms before_topological_order)
  with assms show False
    by (metis is_topological_order_def distinct_not_before_self)
qed

end
