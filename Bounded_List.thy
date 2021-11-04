section \<open> Bounded Lists \<close>

theory Bounded_List
  imports "List_Extra" "HOL-Library.Numeral_Type"
begin

text \<open> The term @{term "CARD('n)"} retrieves the cardinality of a finite type @{typ 'n}. Examples
  include the types @{typ 1}, @{typ 2} and @{typ 3}.\<close>

typedef ('a, 'n::finite) blist = "{xs :: 'a list. length xs \<le> CARD('n)}"
  morphisms list_of_blist blist_of_list
  by (rule_tac x="[]" in exI, auto)

declare list_of_blist_inverse [simp]

syntax "_blist" :: "type \<Rightarrow> type \<Rightarrow> type" ("_ blist[_]" [100, 0] 100)
translations (type) "'a blist['n]" == (type) "('a, 'n) blist"

text \<open> We construct various functions using the lifting package to lift corresponding list functions. \<close>

setup_lifting type_definition_blist

lift_definition blength :: "'a blist['n::finite] \<Rightarrow> nat" is length .

lift_definition bappend :: "'a blist['m::finite] \<Rightarrow> 'a blist['n::finite] \<Rightarrow> 'a blist['m + 'n]" (infixr "@\<^sub>s" 65) is append
  by auto

lift_definition bmake :: "'n itself \<Rightarrow> 'a list \<Rightarrow> 'a blist['n::finite]" is "\<lambda> _. take CARD('n)"
  by auto

code_datatype bmake

lemma bmake_length_card:
  "blength (bmake TYPE('n::finite) xs) = (if length xs \<le> CARD('n) then length xs else CARD('n))"
  apply (simp add: blength_def bmake_def, auto)
  by (simp add: blist_of_list_inverse)+

lemma blist_always_bounded:
  "length (list_of_blist (bl::'a blist['n::finite])) \<le> CARD('n)"
  using list_of_blist by blast

lemma blist_remove_head:
  fixes bl :: "'a blist['n::finite]"
  assumes "blength bl > 0"
  shows "blength (bmake TYPE('n::finite) (tl (list_of_blist (bl::'a blist['n::finite])))) < blength bl"
  by (metis One_nat_def Suc_pred assms blength.rep_eq bmake_length_card length_tl less_Suc_eq_le linear)

text \<open> This proof is performed by transfer \<close>

lemma bappend_bmake [code]: 
  "bmake TYPE('a::finite) xs @\<^sub>s bmake TYPE('b::finite) ys 
    = bmake TYPE('a + 'b) (take CARD('a) xs @ take CARD('b) ys)"
  by (transfer, simp add: min.absorb2)

instantiation blist :: (type, finite) equal
begin

definition equal_blist :: "'a blist['b] \<Rightarrow> 'a blist['b] \<Rightarrow> bool" where
"equal_blist m1 m2 \<longleftrightarrow> (list_of_blist m1 = list_of_blist m2)"

instance by (intro_classes, auto simp add: equal_blist_def, transfer, auto)
end

lemma list_of_blist_code [code]:
  "list_of_blist (bmake TYPE('n::finite) xs) = take CARD('n) xs"
  by (transfer, simp)+

definition blists :: "'n::finite itself \<Rightarrow> 'a list \<Rightarrow> ('a blist['n]) list" where
"blists n xs = map blist_of_list (b_lists CARD('n) xs)"

lemma n_blists_as_b_lists:
  fixes n::"'n::finite itself"
  shows "map list_of_blist (blists n xs) = b_lists CARD('n) xs" (is "?lhs = ?rhs")
proof -
  have "?lhs = map (list_of_blist \<circ> (blist_of_list :: _ \<Rightarrow> _ blist['n])) (b_lists CARD('n) xs)"
    by (simp add: blists_def)
  also have "... = map id (b_lists CARD('n) xs)"
    by (rule map_cong, auto simp add: blist_of_list_inverse length_b_lists_elem)
  also have "... = b_lists CARD('n) xs"
    by simp
  finally show ?thesis .
qed

lemma set_blists_enum_UNIV: "set (blists TYPE('n::finite) enum_class.enum) = UNIV"
  apply (auto simp add: blists_def image_iff)
  apply (rule_tac x="list_of_blist x" in bexI, auto)
  apply (rule in_blistsI)
   apply (simp add: blist_always_bounded)
  apply (auto simp add: lists_eq_set enum_UNIV)
  done

lemma distinct_blists: "distinct xs \<Longrightarrow> distinct (blists n xs)"
  by (metis distinct_b_lists distinct_map n_blists_as_b_lists)

definition all_blists :: "(('a::enum) blist['n::finite] \<Rightarrow> bool) \<Rightarrow> bool"
where
  "all_blists P \<longleftrightarrow> (\<forall>xs \<in> set (blists TYPE('n) Enum.enum). P xs)"

definition ex_blists :: "(('a :: enum) blist['n::finite] \<Rightarrow> bool) \<Rightarrow> bool"
where
  "ex_blists P \<longleftrightarrow> (\<exists>xs \<in> set (blists TYPE('n) Enum.enum). P xs)"

instantiation blist :: (enum, finite) enum
begin

definition enum_blist :: "('a blist['b]) list" where
"enum_blist = blists TYPE('b) Enum.enum"

definition enum_all_blist :: "('a blist['b] \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_all_blist P = all_blists P"

definition enum_ex_blist :: "('a blist['b] \<Rightarrow> bool) \<Rightarrow> bool" where
"enum_ex_blist P = ex_blists P"

instance 
  by (intro_classes)
     (simp_all add: enum_blist_def set_blists_enum_UNIV distinct_blists enum_distinct enum_all_blist_def enum_ex_blist_def all_blists_def ex_blists_def)

end
  
end