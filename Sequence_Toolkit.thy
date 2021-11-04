section \<open> Sequence Toolkit \<close>

theory Sequence_Toolkit
  imports Number_Toolkit
begin

subsection \<open> Conversion \<close>

text \<open> We define a number of coercions for mapping a list to finite function. \<close>

abbreviation rel_of_list :: "'a list \<Rightarrow> nat \<leftrightarrow> 'a" ("[_]\<^sub>s") where
"rel_of_list xs \<equiv> [list_pfun xs]\<^sub>\<Zpfun>"

abbreviation seq_nth ("_'(_')\<^sub>s" [999,0] 999) where
"seq_nth xs i \<equiv> xs ! (i - 1)"

declare [[coercion list_ffun]]
declare [[coercion list_pfun]]
declare [[coercion rel_of_list]]
declare [[coercion seq_nth]]

subsection \<open> Number range\<close>

lemma number_range: "{i..j} = {k :: \<int>. i \<le> k \<and> k \<le> j}"
  by (auto)

text \<open> The number range from $i$ to $j$ is the set of all integers greater than or equal to $i$, 
  which are also less than or equal to $j$.\<close>

subsection \<open> Iteration \<close>

definition iter :: "\<int> \<Rightarrow> ('X \<leftrightarrow> 'X) \<Rightarrow> ('X \<leftrightarrow> 'X)" where
"iter n R = (if (n \<ge> 0) then R ^^ (nat n) else (R\<^sup>\<sim>) ^^ (nat n))"

lemma iter_eqs:
  "iter 0 r = Id"
  "n \<ge> 0 \<Longrightarrow> iter (n + 1) r = r \<^bold>; (iter n r)"
  "n < 0 \<Longrightarrow> iter (n + 1) r = iter n (r\<^sup>\<sim>)"
  by (simp_all add: iter_def, metis Suc_nat_eq_nat_zadd1 add.commute relpow.simps(2) relpow_commute)

subsection \<open> Number of members of a set \<close>

lemma size_rel_of_list: 
  "#xs = length xs" 
  by simp

subsection \<open> Minimum \<close>

text \<open> Implemented by the function @{const Min}. \<close>

subsection \<open> Maximum \<close>

text \<open> Implemented by the function @{const Max}. \<close>

subsection \<open> Finite sequences \<close>

definition "seq A = lists A"

lemma seq_iff [simp]: "xs \<in> seq A \<longleftrightarrow> set xs \<subseteq> A"
  by (simp add: in_lists_conv_set seq_def subset_code(1))
  
lemma seq_ffun_set: "range list_ffun = {f :: \<nat> \<Zffun> 'X. dom(f) = {1..#f}}"
  by (simp add: range_list_ffun, force)

subsection \<open> Non-empty finite sequences \<close>

definition "seq\<^sub>1 A = seq A - {[]}"

lemma seq\<^sub>1_iff [simp]: "xs \<in> seq\<^sub>1(A) \<longleftrightarrow> (xs \<in> seq A \<and> #xs > 0)"
  by (simp add: seq\<^sub>1_def)

subsection \<open> Injective sequences \<close>

definition "iseq A = seq A \<inter> Collect distinct"

lemma iseq_iff [simp]: "xs \<in> iseq(A) \<longleftrightarrow> (xs \<in> seq A \<and> distinct xs)"
  by (simp add: iseq_def)

subsection \<open> Bounded sequences \<close>

definition bseq :: "\<nat> \<Rightarrow> 'a set \<Rightarrow> 'a list set" ("bseq[_]") where
"bseq n A = blists n A"

(* Proof that this corresponds to the Z definition required *)

subsection \<open> Sequence brackets \<close>

text \<open> Provided by the HOL list notation @{term "[x, y, z]"}. \<close>

subsection \<open> Concatenation \<close>

text \<open> Provided by the HOL concatenation operator @{term "(@)"}. \<close>

subsection \<open> Reverse \<close>

text \<open> Provided by the HOL function @{const rev}. \<close>

subsection \<open> Head of a sequence \<close>

definition head :: "'a list \<Zpfun> 'a" where
"head = (\<lambda> xs :: 'a list | #xs > 0 \<bullet> hd xs)"

lemma dom_head: "dom head = {xs. #xs > 0}"
  by (simp add: head_def)

lemma head_app: "#xs > 0 \<Longrightarrow> head xs = hd xs"
  by (simp add: head_def)

lemma head_z_def: "xs \<in> seq\<^sub>1(A) \<Longrightarrow> head xs = xs 1"
  by (simp add: hd_conv_nth head_app seq\<^sub>1_def)

subsection \<open> Last of a sequence \<close>

hide_const (open) last

definition last :: "'a list \<Zpfun> 'a" where
"last = (\<lambda> xs :: 'a list | #xs > 0 \<bullet> List.last xs)"

lemma dom_last: "dom last = {xs. #xs > 0}"
  by (simp add: last_def)

lemma last_app: "#xs > 0 \<Longrightarrow> last xs = List.last xs"
  by (simp add: last_def)

lemma last_eq: "#s > 0 \<Longrightarrow> last s = s (#s)"
  by (simp add: last_app last_conv_nth)

subsection \<open> Tail of a sequence \<close>

definition tail :: "'a list \<Zpfun> 'a list" where
"tail = (\<lambda> xs :: 'a list | #xs > 0 \<bullet> tl xs)"

lemma dom_tail: "dom tail = {xs. #xs > 0}"
  by (simp add: tail_def)

lemma tail_app: "#xs > 0 \<Longrightarrow> tail xs = tl xs"
  by (simp add: tail_def)

subsection \<open> Domain \<close>

definition dom_seq :: "'a list \<Rightarrow> \<nat> set" where
[simp]: "dom_seq xs = {0..<#xs}"

adhoc_overloading dom dom_seq

subsection \<open> Range \<close>

definition ran_seq :: "'a list \<Rightarrow> 'a set" where
[simp]: "ran_seq xs = set xs"

adhoc_overloading ran ran_seq

subsection \<open> Filter \<close>

notation seq_filter (infix "\<restriction>" 80)

lemma seq_filter_Nil: "[] \<restriction> V = []" by simp

lemma seq_filter_append: "(s @ t) \<restriction> V = (s \<restriction> V) @ (t \<restriction> V)" 
  by (simp add: seq_filter_append)

lemma seq_filter_subset_iff: "ran s \<subseteq> V \<longleftrightarrow> (s \<restriction> V = s)"
  by (auto simp add: seq_filter_def subsetD, meson filter_id_conv)

lemma seq_filter_empty: "s \<restriction> {} = []" by simp

lemma seq_filter_size: "#(s \<restriction> V) \<le> #s"
  by (simp add: seq_filter_def)

lemma seq_filter_twice: "(s \<restriction> V) \<restriction> W = s \<restriction> (V \<inter> W)" by simp

subsection \<open> Examples \<close>

lemma "([1,2,3] \<^bold>; (\<lambda> x \<bullet> x + 1)) 1 = 2"
  by (simp add: pfun_graph_comp[THEN sym] list_pfun_def pcomp_pabs)

end