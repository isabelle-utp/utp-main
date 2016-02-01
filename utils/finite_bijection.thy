section {* Finite bijections *}

theory finite_bijection
  imports "~~/src/HOL/Library/Countable_Set"
begin

text {* This theory shows that there exists a bijection between any finite type and the set
        of natural numbers bounded by the cardinality of the finite type. *}

definition is_to_nat_ind :: "'a \<Rightarrow> nat \<Rightarrow> bool" where
"is_to_nat_ind x i \<longleftrightarrow> (finite (UNIV :: 'a set) \<and>
                        i < card (UNIV :: 'a set) \<and> 
                        sorted_list_of_set (to_nat_on (UNIV :: 'a set) ` (UNIV :: 'a set)) ! i = to_nat_on (UNIV :: 'a set) x)"

text {* The function @{const to_nat} from the countable class makes no guarantees about
        which natural numbers will be picked for each element. Nevertheless is guaranatees
        a unique natural for each element. We use this to map each of these elements to
        a number in the range 0..|A| by creating a sorted list of the corresponding naturals
        from @{const to_nat} and then assigning each element its index in this list. Thus
        we end up with a more predictable set of numbers. *}

definition to_nat_fin :: "'a \<Rightarrow> nat" where
"to_nat_fin x = (THE i. is_to_nat_ind x i)"

lemma sorted_list_of_set_index_ex:
  assumes "finite A"
  shows "(\<exists> i<card A. sorted_list_of_set A ! i = x) \<longleftrightarrow> x \<in> A"
  by (metis assms distinct_card in_set_conv_nth sorted_list_of_set)

lemma nat_ind_exists:
  assumes "finite (UNIV :: 'a set)"
  shows "\<exists> i. is_to_nat_ind (x :: 'a) i"
proof -
  have "to_nat_on (UNIV :: 'a set) x \<in> range (to_nat_on (UNIV :: 'a set)) \<longleftrightarrow> 
          (\<exists> i<card (UNIV :: 'a set). sorted_list_of_set (range (to_nat_on (UNIV :: 'a set))) ! i = to_nat_on (UNIV :: 'a set) x)"     
    by (meson assms card_image_le dual_order.strict_trans1 finite_imageI range_eqI sorted_list_of_set_index_ex)

  then obtain a 
    where a_card: "a < card (UNIV :: 'a set)" 
    and a_ind: "sorted_list_of_set (range (to_nat_on (UNIV :: 'a set))) ! a = to_nat_on (UNIV :: 'a set) x"
    by auto
  
  thus ?thesis
    by (auto simp add: is_to_nat_ind_def assms)
qed

lemma length_sorted_list_of_set [simp]: "finite A \<Longrightarrow> length (sorted_list_of_set A) = card A"
  using distinct_card sorted_list_of_set by force

lemma to_nat_on_inj_on: "countable A \<Longrightarrow> inj_on (to_nat_on A) A"
  by (auto simp add: inj_on_def)

thm card_image

lemma finite_card_to_nat_on [simp]:
  "finite (UNIV :: 'a set) \<Longrightarrow> card (range (to_nat_on (UNIV :: 'a set))) = card (UNIV :: 'a set)"
  by (simp add: card_image countable_finite to_nat_on_inj_on)

lemma nat_ind_unique:
  assumes "is_to_nat_ind (x :: 'a) i"
  shows "to_nat_fin x = i"
proof -
  let ?A = "range (to_nat_on (UNIV :: 'a set))"
  from assms have finA: "finite ?A"
    by (simp add: is_to_nat_ind_def)
  hence "distinct (sorted_list_of_set ?A)"
    using sorted_list_of_set by blast
  with assms have "\<And> i j. \<lbrakk> i < card(UNIV :: 'a set); j < card (UNIV :: 'a set) 
                 ; sorted_list_of_set ?A ! i = sorted_list_of_set ?A ! j \<rbrakk> \<Longrightarrow> i = j"
    using finite_card_to_nat_on is_to_nat_ind_def by (fastforce simp add: distinct_conv_nth finA)
  with assms show ?thesis
    apply (simp add: the_equality to_nat_fin_def)
    apply (rule the_equality)
    apply (auto simp add: is_to_nat_ind_def)
  done
qed

lemma nat_ind_val_exists:
  assumes "finite (UNIV :: 'a set)" "i < card (UNIV :: 'a set)"
  shows "\<exists>x :: 'a. is_to_nat_ind x i"
  using assms
  apply (auto simp add: is_to_nat_ind_def)
  apply (metis finite_card_to_nat_on finite_imageI imageE sorted_list_of_set_index_ex)
done

lemma to_nat_fin_ex:
  fixes x :: "'a"
  assumes "finite (UNIV :: 'a set)" "i < card (UNIV :: 'a set)"
  shows "\<exists>x :: 'a. i = to_nat_fin x"
proof -
  obtain y :: 'a where "is_to_nat_ind y i"
    using assms nat_ind_val_exists by blast
  thus ?thesis
    using nat_ind_unique by fastforce
qed

lemma to_nat_fin_bounded: 
  fixes x :: "'a"
  assumes "finite (UNIV :: 'a set)"
  shows "to_nat_fin x < card (UNIV :: 'a set)"
proof -
  obtain i where "is_to_nat_ind x i"
    by (meson assms nat_ind_exists)
  thus ?thesis
    using is_to_nat_ind_def nat_ind_unique by fastforce
qed

lemma range_to_nat_fin: 
  "finite (UNIV :: 'a set) \<Longrightarrow> range (to_nat_fin :: 'a \<Rightarrow> nat) = {n. n < card(UNIV :: 'a set)}"
  using to_nat_fin_ex by (auto simp add: to_nat_fin_bounded)

lemma is_to_nat_ind:
  "\<lbrakk> finite (UNIV :: 'a set); is_to_nat_ind (x :: 'a) i; is_to_nat_ind x j \<rbrakk> \<Longrightarrow> i = j"
  apply (auto simp add: is_to_nat_ind_def)
  apply (metis distinct_card finite_card_to_nat_on finite_imageI nth_eq_iff_index_eq sorted_list_of_set)
done

lemma is_to_nat_ind_elem:
  "\<lbrakk> is_to_nat_ind x i; is_to_nat_ind y i \<rbrakk> \<Longrightarrow> x = y"
  by (auto simp add: is_to_nat_ind_def countable_finite)

lemma to_nat_fin_inj:
  assumes "finite (UNIV :: 'a set)"
  shows "inj (to_nat_fin :: 'a \<Rightarrow> nat)"
proof (rule injI)
  fix x y :: 'a
  assume "to_nat_fin x = to_nat_fin y"
  moreover obtain i where "is_to_nat_ind x i"
    by (meson assms nat_ind_exists)
  moreover obtain j where "is_to_nat_ind y j"
    by (meson assms nat_ind_exists)
 ultimately show "x = y"
    by (metis is_to_nat_ind_elem nat_ind_unique)
qed

lemma to_nat_fin_bij:
  "finite (UNIV :: 'a set) \<Longrightarrow> bij_betw to_nat_fin (UNIV :: 'a set) {n. n < card (UNIV :: 'a set)}"
  by (auto simp add: bij_betw_def to_nat_fin_inj to_nat_fin_bounded range_to_nat_fin)

end