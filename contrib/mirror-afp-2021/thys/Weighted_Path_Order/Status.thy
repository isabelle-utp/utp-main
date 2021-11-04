section \<open>Preliminaries\<close>

subsection \<open>Status functions\<close>

text \<open>A status function assigns to each n-ary symbol a list of indices between 0 and n-1.
These functions are encapsulated into a separate type, so that recursion on the i-th subterm
does not have to perform out-of-bounds checks (e.g., to ensure termination).\<close>

theory Status
  imports 
    First_Order_Terms.Term
begin

typedef 'f status = "{ (\<sigma> :: 'f \<times> nat \<Rightarrow> nat list). (\<forall> f k. set (\<sigma> (f, k)) \<subseteq> {0 ..< k})}" 
  morphisms status Abs_status
  by (rule exI[of _ "\<lambda> _. []"]) auto

setup_lifting type_definition_status

lemma status: "set (status \<sigma> (f, n)) \<subseteq> {0 ..< n}"
  by (transfer) auto

lemma status_aux[termination_simp]: "i \<in> set (status \<sigma> (f, length ss)) \<Longrightarrow> ss ! i \<in> set ss"
  using status[of \<sigma> f "length ss"] unfolding set_conv_nth by force

lemma status_termination_simps[termination_simp]:
  assumes i1: "i < length (status \<sigma> (f, length xs))"
  shows "size (xs ! (status \<sigma> (f, length xs) ! i)) < Suc (size_list size xs)" (is "?a < ?c")
proof -
  from i1 have "status \<sigma> (f, length xs) ! i \<in> set (status \<sigma> (f, length xs))" by auto
  from status_aux[OF this] have "?a \<le> size_list size xs" by (auto simp: termination_simp)
  then show ?thesis by auto
qed

lemma status_ne:
  "status \<sigma> (f, n) \<noteq> [] \<Longrightarrow> \<exists>i < n. i \<in> set (status \<sigma> (f, n))"
  using status [of \<sigma> f n]
  by (meson atLeastLessThan_iff set_empty subsetCE subsetI subset_empty)

lemma set_status_nth:
  "length xs = n \<Longrightarrow> i \<in> set (status \<sigma> (f, n)) \<Longrightarrow> i < length xs \<and> xs ! i \<in> set xs"
  using status [of \<sigma> f n] by force

lift_definition full_status :: "'f status" is "\<lambda> (f, n). [0 ..< n]" by auto

lemma full_status[simp]: "status full_status (f, n) = [0 ..< n]" 
  by transfer auto

text \<open>An argument position i is simple wrt. some term relation, if the i-th subterm is in relation to the
  full term.\<close>

definition simple_arg_pos :: "('f, 'v) term rel \<Rightarrow> 'f \<times> nat \<Rightarrow> nat \<Rightarrow> bool" where 
  "simple_arg_pos rel f i \<equiv> \<forall> ts. i < snd f \<longrightarrow> length ts = snd f \<longrightarrow> (Fun (fst f) ts, ts ! i) \<in> rel"

lemma simple_arg_posI: "\<lbrakk>\<And> ts. length ts = n \<Longrightarrow> i < n \<Longrightarrow> (Fun f ts, ts ! i) \<in> rel\<rbrakk> \<Longrightarrow> simple_arg_pos rel (f, n) i"
  unfolding simple_arg_pos_def by auto

end
