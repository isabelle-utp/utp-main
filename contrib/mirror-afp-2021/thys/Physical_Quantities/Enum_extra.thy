section \<open> Enumeration Extras \<close>

theory Enum_extra
  imports "HOL-Library.Cardinality"
begin

subsection \<open> First Index Function \<close>

text \<open> The following function extracts the index of the first occurrence of an element in a list, 
  assuming it is indeed an element. \<close>

fun first_ind :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat" where
"first_ind [] y i = undefined" |
"first_ind (x # xs) y i = (if (x = y) then i else first_ind xs y (Suc i))"

lemma first_ind_length:
  "x \<in> set(xs) \<Longrightarrow> first_ind xs x i < length(xs) + i"
  by (induct xs arbitrary: i, auto, metis add_Suc_right)

lemma nth_first_ind:
  "\<lbrakk> distinct xs; x \<in> set(xs) \<rbrakk> \<Longrightarrow> xs ! (first_ind xs x i - i) = x"
  apply (induct xs arbitrary: i)
   apply (auto)
  apply (metis One_nat_def add.right_neutral add_Suc_right add_diff_cancel_left' diff_diff_left empty_iff first_ind.simps(2) list.set(1) nat.simps(3) neq_Nil_conv nth_Cons' zero_diff)
  done

lemma first_ind_nth:
  "\<lbrakk> distinct xs; i < length xs \<rbrakk> \<Longrightarrow> first_ind xs (xs ! i) j = i + j"
  apply (induct xs arbitrary: i j)
   apply (auto)
   apply (metis less_Suc_eq_le nth_equal_first_eq)
  using less_Suc_eq_0_disj apply auto
  done

subsection \<open> Enumeration Indices \<close>

syntax
  "_ENUM" :: "type \<Rightarrow> logic" ("ENUM'(_')")

translations
  "ENUM('a)" => "CONST Enum.enum :: ('a::enum) list"

text \<open> Extract a unique natural number associated with an enumerated value by using its index
  in the characteristic list \<^term>\<open>ENUM('a)\<close>. \<close>

definition enum_ind :: "'a::enum \<Rightarrow> nat" where
"enum_ind (x :: 'a::enum) = first_ind ENUM('a) x 0"

lemma length_enum_CARD: "length ENUM('a) = CARD('a)"
  by (simp add: UNIV_enum distinct_card enum_distinct)

lemma CARD_length_enum: "CARD('a) = length ENUM('a)"
  by (simp add: length_enum_CARD)

lemma enum_ind_less_CARD [simp]: "enum_ind (x :: 'a::enum) < CARD('a)"
  using first_ind_length[of x, OF in_enum, of 0] by (simp add: enum_ind_def CARD_length_enum)
  
lemma enum_nth_ind [simp]: "Enum.enum ! (enum_ind x) = x"
  using nth_first_ind[of Enum.enum x 0, OF enum_distinct in_enum] by (simp add: enum_ind_def)

lemma enum_distinct_conv_nth:
  assumes "i < CARD('a)" "j < CARD('a)" "ENUM('a) ! i = ENUM('a) ! j"
  shows "i = j"
proof -
  have "(\<forall>i<length ENUM('a). \<forall>j<length ENUM('a). i \<noteq> j \<longrightarrow> ENUM('a) ! i \<noteq> ENUM('a) ! j)"
    using distinct_conv_nth[of "ENUM('a)", THEN sym] by (simp add: enum_distinct)
  with assms show ?thesis
    by (auto simp add: CARD_length_enum)
qed

lemma enum_ind_nth [simp]:
  assumes "i < CARD('a::enum)"
  shows "enum_ind (ENUM('a) ! i) = i"
  using assms first_ind_nth[of "ENUM('a)" i 0, OF enum_distinct]
  by (simp add: enum_ind_def CARD_length_enum)

lemma enum_ind_spec:
  "enum_ind (x :: 'a::enum) = (THE i. i < CARD('a) \<and> Enum.enum ! i = x)"
proof (rule sym, rule the_equality, safe)
  show "enum_ind x < CARD('a)"
    by (simp add: enum_ind_less_CARD[of x])
  show "enum_class.enum ! enum_ind x = x"
    by simp
  show "\<And>i. i < CARD('a) \<Longrightarrow> x = ENUM('a) ! i \<Longrightarrow> i = enum_ind (ENUM('a) ! i)"
    by (simp add: enum_ind_nth)
qed

lemma enum_ind_inj: "inj (enum_ind :: 'a::enum \<Rightarrow> nat)"
  by (rule inj_on_inverseI[of _ "\<lambda> i. ENUM('a) ! i"], simp)

lemma enum_ind_neq [simp]: "x \<noteq> y \<Longrightarrow> enum_ind x \<noteq> enum_ind y"
  by (simp add: enum_ind_inj inj_eq)

end