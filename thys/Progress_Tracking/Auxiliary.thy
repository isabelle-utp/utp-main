section \<open>Auxiliary Lemmas\<close>

(*<*)
theory Auxiliary
  imports
    "HOL-Library.Multiset"
    "Nested_Multisets_Ordinals.Signed_Multiset"
    "HOL-Library.Linear_Temporal_Logic_on_Streams"
begin
(*>*)

subsection\<open>General\<close>

lemma sum_list_hd_tl:
  fixes xs :: "(_ :: group_add) list"
  shows "xs \<noteq> [] \<Longrightarrow> sum_list (tl xs) = (- hd xs) + sum_list xs"
  by (cases xs) simp_all

lemma finite_distinct_bounded: "finite A \<Longrightarrow> finite {xs. distinct xs \<and> set xs \<subseteq> A}"
  apply (rule finite_subset[of _ "\<Union>n \<in> {0 .. card A}. {xs.  length xs = n \<and> distinct xs \<and> set xs \<subseteq> A}"])
  subgoal by clarsimp (metis card_mono distinct_card)
  subgoal by auto
  done


subsection\<open>Sums\<close>

lemma Sum_eq_pick_changed_elem:
  assumes "finite M"
    and "m \<in> M" "f m = g m + \<Delta>"
    and "\<And>n. n \<noteq> m \<and> n \<in> M \<Longrightarrow> f n = g n"
  shows "(\<Sum>x\<in>M. f x) = (\<Sum>x\<in>M. g x) + \<Delta>"
  using assms
proof (induct M arbitrary: m rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case
  proof (cases "x=m")
    case True
    with insert have "sum f F = sum g F"
      by (intro sum.cong[OF refl]) force
    with insert True show ?thesis
      by (auto simp: add.commute add.left_commute)
  next
    case False
    with insert show ?thesis
      by (auto simp: add.assoc)
  qed
qed

lemma sum_pos_ex_elem_pos: "(0::int) < (\<Sum>m\<in>M. f m) \<Longrightarrow> \<exists>m\<in>M. 0 < f m"
  by (meson not_le sum_nonpos)

lemma sum_if_distrib_add: "finite A \<Longrightarrow> b \<in> A \<Longrightarrow> (\<Sum>a\<in>A. if a=b then X b + Y a else X a) = (\<Sum>a\<in>A. X a) + Y b"
  by (simp add: Sum_eq_pick_changed_elem)

subsection\<open>Partial Orders\<close>

lemma (in order) order_finite_set_exists_foundation:
  fixes   t :: 'a
  assumes "finite M"
    and   "t \<in> M"
  shows   "\<exists>s\<in>M. s \<le> t \<and> (\<forall>u\<in>M. \<not> u < s)"
  using assms
  by (simp add: dual_order.strict_iff_order finite_has_minimal2)

lemma order_finite_set_obtain_foundation:
  fixes   t :: "_ :: order"
  assumes "finite M"
    and   "t \<in> M"
  obtains s where "s \<in> M" "s \<le> t" "\<forall>u\<in>M. \<not> u < s"
  using assms order_finite_set_exists_foundation by blast

subsection\<open>Multisets\<close>

lemma finite_nonzero_count: "finite {t. count M t > 0}"
  using count unfolding multiset_def by auto

lemma finite_count[simp]: "finite {t. count M t > i}"
  by (rule finite_subset[OF _ finite_nonzero_count[of M]]) (auto simp only: set_mset_def)

subsection\<open>Signed Multisets\<close>

lemma zcount_zmset_of_nonneg[simp]: "0 \<le> zcount (zmset_of M) t"
  by simp

lemma finite_zcount_pos[simp]: "finite {t. zcount M t > 0}"
  apply transfer
  subgoal for M
    apply (rule finite_subset[OF _ finite_Un[THEN iffD2, OF conjI[OF finite_nonzero_count finite_nonzero_count]], of _ "fst M" "snd M"])
    apply (auto simp only: set_mset_def fst_conv snd_conv split: prod.splits)
    done
  done

lemma finite_zcount_neg[simp]: "finite {t. zcount M t < 0}"
  apply transfer
  subgoal for M
    apply (rule finite_subset[OF _ finite_Un[THEN iffD2, OF conjI[OF finite_nonzero_count finite_nonzero_count]], of _ "fst M" "snd M"])
    apply (auto simp only: set_mset_def fst_conv snd_conv split: prod.splits)
    done
  done

lemma pos_zcount_in_zmset: "0 < zcount M x \<Longrightarrow> x \<in>#\<^sub>z M"
  by (simp add: zcount_inI)

lemma zmset_elem_nonneg: "x \<in>#\<^sub>z M \<Longrightarrow> (\<And>x. x \<in>#\<^sub>z M \<Longrightarrow> 0 \<le> zcount M x) \<Longrightarrow> 0 < zcount M x"
  by (simp add: order.order_iff_strict zcount_eq_zero_iff)

lemma zero_le_sum_single: "0 \<le> zcount (\<Sum>x\<in>M. {#f x#}\<^sub>z) t"
  by (induct M rule: infinite_finite_induct) auto

lemma mem_zmset_of[simp]: "x \<in>#\<^sub>z zmset_of M \<longleftrightarrow> x \<in># M"
  by (simp add: set_zmset_def)

lemma mset_neg_minus: "mset_neg (abs_zmultiset (Mp,Mn)) = Mn-Mp"
  by (simp add: mset_neg.abs_eq)

lemma mset_pos_minus: "mset_pos (abs_zmultiset (Mp,Mn)) = Mp-Mn"
  by (simp add: mset_pos.abs_eq)

lemma mset_neg_sum_set: "(\<And>m. m \<in> M \<Longrightarrow> mset_neg (f m) = {#}) \<Longrightarrow> mset_neg (\<Sum>m\<in>M. f m) = {#}"
  by (induct M rule: infinite_finite_induct) auto

lemma mset_neg_empty_iff: "mset_neg M = {#} \<longleftrightarrow> (\<forall>t. 0 \<le> zcount M t)"
  apply rule
  subgoal
    by (metis add.commute add.right_neutral mset_pos_as_neg zcount_zmset_of_nonneg zmset_of_empty)
  subgoal
    apply (induct rule: zmultiset.abs_induct)
    subgoal for y
      apply (induct y)
      apply (subst mset_neg_minus)
      apply transfer
      apply (simp add: Diff_eq_empty_iff_mset mset_subset_eqI)
      done
    done
  done

lemma mset_neg_zcount_nonneg: "mset_neg M = {#} \<Longrightarrow> 0 \<le> zcount M t"
  by (subst (asm) mset_neg_empty_iff) simp

lemma in_zmset_conv_pos_neg_disj: "x \<in>#\<^sub>z M \<longleftrightarrow> x \<in># mset_pos M \<or> x \<in># mset_neg M"
  by (metis count_mset_pos in_diff_zcount mem_zmset_of mset_pos_neg_partition nat_code(2) not_in_iff zcount_ne_zero_iff)

lemma in_zmset_notin_mset_pos[simp]: "x \<in>#\<^sub>z M \<Longrightarrow> x \<notin># mset_pos M \<Longrightarrow> x \<in># mset_neg M"
  by (auto simp: in_zmset_conv_pos_neg_disj)

lemma in_zmset_notin_mset_neg[simp]: "x \<in>#\<^sub>z M \<Longrightarrow> x \<notin># mset_neg M \<Longrightarrow> x \<in># mset_pos M"
  by (auto simp: in_zmset_conv_pos_neg_disj)

lemma in_mset_pos_in_zmset: "x \<in># mset_pos M \<Longrightarrow> x \<in>#\<^sub>z M"
  by (auto intro: iffD2[OF in_zmset_conv_pos_neg_disj])

lemma in_mset_neg_in_zmset: "x \<in># mset_neg M \<Longrightarrow> x \<in>#\<^sub>z M"
  by (auto intro: iffD2[OF in_zmset_conv_pos_neg_disj])

lemma set_zmset_eq_set_mset_union: "set_zmset M = set_mset (mset_pos M) \<union> set_mset (mset_neg M)"
  by (auto dest: in_mset_pos_in_zmset in_mset_neg_in_zmset)

lemma member_mset_pos_iff_zcount: "x \<in># mset_pos M \<longleftrightarrow> 0 < zcount M x"
  using not_in_iff pos_zcount_in_zmset by force

lemma member_mset_neg_iff_zcount: "x \<in># mset_neg M \<longleftrightarrow> zcount M x < 0"
  by (metis member_mset_pos_iff_zcount mset_pos_uminus neg_le_0_iff_le not_le zcount_uminus)

lemma mset_pos_mset_neg_disjoint[simp]: "set_mset (mset_pos \<Delta>) \<inter> set_mset (mset_neg \<Delta>) = {}"
  by (auto simp: member_mset_pos_iff_zcount member_mset_neg_iff_zcount)

lemma zcount_sum: "zcount (\<Sum>M\<in>MM. f M) t = (\<Sum>M\<in>MM. zcount (f M) t)"
  by (induct MM rule: infinite_finite_induct) auto

lemma zcount_filter_invariant: "zcount {# t'\<in>#\<^sub>zM. t'=t #} t = zcount M t"
  by auto

lemma in_filter_zmset_in_zmset[simp]: "x \<in>#\<^sub>z filter_zmset P M \<Longrightarrow> x \<in>#\<^sub>z M"
  by (metis count_filter_zmset zcount_ne_zero_iff)

lemma pos_filter_zmset_pos_zmset[simp]: "0 < zcount (filter_zmset P M) x \<Longrightarrow> 0 < zcount M x"
  by (metis (full_types) count_filter_zmset less_irrefl)

lemma neg_filter_zmset_neg_zmset[simp]: "0 > zcount (filter_zmset P M) x \<Longrightarrow> 0 > zcount M x"
  by (metis (full_types) count_filter_zmset less_irrefl)


lift_definition update_zmultiset :: "'t zmultiset \<Rightarrow> 't \<Rightarrow> int \<Rightarrow> 't zmultiset" is
  "\<lambda>(A,B) T D.(if D>0 then (A + replicate_mset (nat D) T, B)
                    else (A,B + replicate_mset (nat (-D)) T))"
  by (auto simp: equiv_zmset_def if_split)

lemma zcount_update_zmultiset: "zcount (update_zmultiset M t n) t' = zcount M t' + (if t = t' then n else 0)"
  by transfer auto

lemma (in order) order_zmset_exists_foundation:
  fixes   t :: 'a
  assumes "0 < zcount M t"
  shows   "\<exists>s. s \<le> t \<and> 0 < zcount M s \<and> (\<forall>u. 0 < zcount M u \<longrightarrow> \<not> u < s)"
  using assms
proof -
  let ?M = "{t. 0 < zcount M t}"
  from assms have "t \<in> ?M"
    by simp
  then have "\<exists>s\<in>?M. s \<le> t \<and> (\<forall>u\<in>?M. \<not> u < s)"
    by - (drule order_finite_set_exists_foundation[rotated 1], auto)
  then show ?thesis by auto
qed

lemma (in order) order_zmset_exists_foundation':
  fixes   t :: 'a
  assumes "0 < zcount M t"
  shows   "\<exists>s. s \<le> t \<and> 0 < zcount M s \<and> (\<forall>u<s. zcount M u \<le> 0)"
  using assms order_zmset_exists_foundation
  by (meson le_less_linear)

lemma (in order) order_zmset_exists_foundation_neg:
  fixes   t :: 'a
  assumes "zcount M t < 0"
  shows   "\<exists>s. s \<le> t \<and> zcount M s < 0 \<and> (\<forall>u. zcount M u < 0 \<longrightarrow> \<not> u < s)"
  using assms
proof -
  let ?M = "{t. zcount M t < 0}"
  from assms have "t \<in> ?M"
    by simp
  then have "\<exists>s\<in>?M. s \<le> t \<and> (\<forall>u\<in>?M. \<not> u < s)"
    by - (drule order_finite_set_exists_foundation[rotated 1], auto)
  then show ?thesis by auto
qed

lemma (in order) order_zmset_exists_foundation_neg':
  fixes   t :: 'a
  assumes "zcount M t < 0"
  shows   "\<exists>s. s \<le> t \<and> zcount M s < 0 \<and> (\<forall>u<s. 0 \<le> zcount M u)"
  using assms order_zmset_exists_foundation_neg
  by (meson le_less_linear)

lemma (in order) elem_order_zmset_exists_foundation:
  fixes x :: 'a
  assumes "x \<in>#\<^sub>z M"
  shows   "\<exists>s\<in>#\<^sub>zM. s \<le> x \<and> (\<forall>u\<in>#\<^sub>zM. \<not> u < s)"
  by (rule order_finite_set_exists_foundation[OF finite_set_zmset, OF assms(1)])

subsubsection\<open>Image of a Signed Multiset\<close>

lift_definition image_zmset :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a zmultiset \<Rightarrow> 'b zmultiset" is
  "\<lambda>f (M, N). (image_mset f M, image_mset f N)"
  by (auto simp: equiv_zmset_def simp flip: image_mset_union)

syntax (ASCII)
  "_comprehension_zmset" :: "'a \<Rightarrow> 'b \<Rightarrow> 'b zmultiset \<Rightarrow> 'a zmultiset"  ("({#_/. _ :#z _#})")
syntax
  "_comprehension_zmset" :: "'a \<Rightarrow> 'b \<Rightarrow> 'b zmultiset \<Rightarrow> 'a zmultiset"  ("({#_/. _ \<in>#\<^sub>z _#})")
translations
  "{#e. x \<in>#\<^sub>z M#}" \<rightleftharpoons> "CONST image_zmset (\<lambda>x. e) M"

lemma image_zmset_empty[simp]: "image_zmset f {#}\<^sub>z = {#}\<^sub>z"
  by transfer (auto simp: equiv_zmset_def)

lemma image_zmset_single[simp]: "image_zmset f {#x#}\<^sub>z = {#f x#}\<^sub>z"
  by transfer (simp add: equiv_zmset_def)

lemma image_zmset_union[simp]: "image_zmset f (M + N) = image_zmset f M + image_zmset f N"
  by transfer (auto simp: equiv_zmset_def)

lemma image_zmset_Diff[simp]: "image_zmset f (A - B) = image_zmset f A - image_zmset f B"
proof -
  have "image_zmset f (A - B + B) = image_zmset f (A - B) + image_zmset f B"
    using image_zmset_union by blast
  then show ?thesis by simp
qed

lemma mset_neg_image_zmset: "mset_neg M = {#} \<Longrightarrow> mset_neg (image_zmset f M) = {#}"
  unfolding multiset_eq_iff count_empty
  by transfer (auto simp add: image_mset_subseteq_mono mset_subset_eqI mset_subset_eq_count)

lemma nonneg_zcount_image_zmset[simp]: "(\<And>t. 0 \<le> zcount M t) \<Longrightarrow> 0 \<le> zcount (image_zmset f M) t"
  by (meson mset_neg_empty_iff mset_neg_image_zmset)

lemma image_zmset_add_zmset[simp]: "image_zmset f (add_zmset t M) = add_zmset (f t) (image_zmset f M)"
  by transfer (auto simp: equiv_zmset_def)

lemma pos_zcount_image_zmset[simp]: "(\<And>t. 0 \<le> zcount M t) \<Longrightarrow> 0 < zcount M t \<Longrightarrow> 0 < zcount (image_zmset f M) (f t)"
  apply transfer
  subgoal for M t f
    apply (induct M)
    subgoal for Mp Mn
      apply simp
      apply (metis count_diff count_image_mset_ge_count image_mset_Diff less_le_trans subseteq_mset_def zero_less_diff)
      done
    done
  done

lemma set_zmset_transfer[transfer_rule]:
  "(rel_fun (pcr_zmultiset (=)) (rel_set (=)))
   (\<lambda>(Mp, Mn). set_mset Mp \<union> set_mset Mn - {x. count Mp x = count Mn x}) set_zmset"
  by (auto simp: rel_fun_def pcr_zmultiset_def cr_zmultiset_def
      rel_set_eq multiset.rel_eq set_zmset_def zcount.abs_eq count_eq_zero_iff[symmetric]
      simp del: zcount_ne_zero_iff)

lemma zcount_image_zmset:
  "zcount (image_zmset f M) x = (\<Sum>y \<in> f -` {x} \<inter> set_zmset M. zcount M y)"
  apply (transfer fixing: f x)
  subgoal for M
    apply (cases M; clarify)
    subgoal for Mp Mn
      unfolding count_image_mset int_sum
    proof -
      have "(\<Sum>x\<in>f -` {x} \<inter> set_mset Mp. int (count Mp x)) =
        (\<Sum>x\<in>f -` {x} \<inter> (set_mset Mp \<union> set_mset Mn). int (count Mp x))" (is "?S1 = _")
        by (subst sum.same_carrier[where C="f -` {x} \<inter> (set_mset Mp \<union> set_mset Mn)"])
          (auto simp: count_eq_zero_iff)
      moreover
      have "(\<Sum>x\<in>f -` {x} \<inter> set_mset Mn. int (count Mn x)) =
        (\<Sum>x\<in>f -` {x} \<inter> (set_mset Mp \<union> set_mset Mn). int (count Mn x))"(is "?S2 = _")
        by (subst sum.same_carrier[where C="f -` {x} \<inter> (set_mset Mp \<union> set_mset Mn)"])
          (auto simp: count_eq_zero_iff)
      moreover
      have "(\<Sum>x\<in>f -` {x} \<inter> (set_mset Mp \<union> set_mset Mn - {x. count Mp x = count Mn x}). int (count Mp x) - int (count Mn x))
        = (\<Sum>x\<in>f -` {x} \<inter> (set_mset Mp \<union> set_mset Mn). int (count Mp x) - int (count Mn x))"
        (is "?S = _")
        by (subst sum.same_carrier[where C="f -` {x} \<inter> (set_mset Mp \<union> set_mset Mn)"]) auto
      ultimately show "?S1 - ?S2 = ?S"
        by (auto simp: sum_subtractf)
    qed
    done
  done

lemma zmset_empty_image_zmset_empty: "(\<And>t. zcount M t = 0) \<Longrightarrow> zcount (image_zmset f M) t = 0"
  by (auto simp: zcount_image_zmset)

lemma in_image_zmset_in_zmset: "t \<in>#\<^sub>z image_zmset f M \<Longrightarrow> \<exists>t. t \<in>#\<^sub>z M"
  by (rule ccontr) simp

lemma zcount_image_zmset_zero: "(\<And>m. m \<in>#\<^sub>z M \<Longrightarrow> f m \<noteq> x) \<Longrightarrow> x \<notin>#\<^sub>z image_zmset f M"
  unfolding set_zmset_def
  by (simp add: zcount_image_zmset) (metis Int_emptyI sum.empty vimage_singleton_eq)

lemma image_zmset_pre: "t \<in>#\<^sub>z image_zmset f M \<Longrightarrow> \<exists>m. m \<in>#\<^sub>z M \<and> f m = t"
proof (rule ccontr)
  assume t: "t \<in>#\<^sub>z image_zmset f M"
  assume "\<nexists>m. m \<in>#\<^sub>z M \<and> f m = t"
  then have "m \<in>#\<^sub>z M \<Longrightarrow> \<not> f m = t" for m
    by blast
  then have "zcount (image_zmset f M) t = 0"
    by (meson t zcount_image_zmset_zero)
  with t show False
    by (meson zcount_ne_zero_iff)
qed

lemma pos_image_zmset_obtain_pre:
  "(\<And>t. 0 \<le> zcount M t) \<Longrightarrow> 0 < zcount (image_zmset f M) t \<Longrightarrow> \<exists>m. 0 < zcount M m \<and> f m = t"
proof -
  assume nonneg: "0 \<le> zcount M t" for t
  assume "0 < zcount (image_zmset f M) t"
  then have "t \<in>#\<^sub>z image_zmset f M"
    by (simp add: pos_zcount_in_zmset)
  then obtain x where x: "x \<in>#\<^sub>z M" "f x = t"
    by (auto dest: image_zmset_pre)
  with nonneg have "0 < zcount M x"
    by (meson zmset_elem_nonneg)
  with x show ?thesis
    by auto
qed

subsection\<open>Streams\<close>

definition relates :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> bool" where
  "relates \<phi> s = \<phi> (shd s) (shd (stl s))"

lemma relatesD[dest]: "relates P s \<Longrightarrow> P (shd s) (shd (stl s))"
  unfolding relates_def by simp

lemma alw_relatesD[dest]: "alw (relates P) s \<Longrightarrow> P (shd s) (shd (stl s))"
  by auto

lemma relatesI[intro]: "P (shd s) (shd (stl s)) \<Longrightarrow> relates P s"
  by (auto simp: relates_def)

lemma alw_holds_smap_conv_comp: "alw (holds P) (smap f s) = alw (\<lambda>s. (P o f) (shd s)) s"
  apply (rule iffI)
   apply (coinduction arbitrary: s)
   apply auto []
  apply (coinduction arbitrary: s)
  apply auto
  done

lemma alw_relates: "alw (relates P) s \<longleftrightarrow> P (shd s) (shd (stl s)) \<and> alw (relates P) (stl s)"
  apply (rule iffI)
   apply (auto simp: relates_def dest: alwD) []
  apply (coinduction arbitrary: s)
  apply (auto simp: relates_def)
  done

subsection\<open>Notation\<close>

no_notation AND  (infix "aand" 60)
no_notation OR   (infix "or" 60)
no_notation IMPL (infix "imp" 60)

notation AND  (infixr "aand" 70)
notation OR   (infixr "or" 65)
notation IMPL (infixr "imp" 60)

(*<*)
end
(*>*)