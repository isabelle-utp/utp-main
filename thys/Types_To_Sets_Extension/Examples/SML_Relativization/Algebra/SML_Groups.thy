(* Title: Examples/SML_Relativization/Algebra/SML_Groups.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Relativization of the results about groups\<close>
theory SML_Groups
  imports SML_Monoids
begin



subsection\<open>Simple groups\<close>


subsubsection\<open>Definitions and common properties\<close>

locale group_ow = semigroup_ow U f for U :: "'ag set" and f +
  fixes z (\<open>\<^bold>1\<^sub>o\<^sub>w\<close>)
    and inverse :: "'ag \<Rightarrow> 'ag"
  assumes z_closed[simp]: "\<^bold>1\<^sub>o\<^sub>w \<in> U"
    and inverse_closed[simp]: "a \<in> U \<Longrightarrow> inverse a \<in> U" 
    and group_left_neutral: "a \<in> U \<Longrightarrow> \<^bold>1\<^sub>o\<^sub>w \<^bold>*\<^sub>o\<^sub>w a = a"
    and left_inverse[simp]: "a \<in> U \<Longrightarrow> inverse a \<^bold>*\<^sub>o\<^sub>w a = \<^bold>1\<^sub>o\<^sub>w"
begin

notation z (\<open>\<^bold>1\<^sub>o\<^sub>w\<close>)

lemma inverse_closed': "inverse ` U \<subseteq> U" by auto
lemma inverse_closed'': "\<forall>x\<in>U. inverse x \<in> U" by auto

lemma left_cancel: 
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" 
  shows "a \<^bold>*\<^sub>o\<^sub>w b = a \<^bold>*\<^sub>o\<^sub>w c \<longleftrightarrow> b = c"
proof
  assume "a \<^bold>*\<^sub>o\<^sub>w b = a \<^bold>*\<^sub>o\<^sub>w c"
  then have "inverse a \<^bold>*\<^sub>o\<^sub>w (a \<^bold>*\<^sub>o\<^sub>w b) = inverse a \<^bold>*\<^sub>o\<^sub>w (a \<^bold>*\<^sub>o\<^sub>w c)" by simp
  with assms have "(inverse a \<^bold>*\<^sub>o\<^sub>w a) \<^bold>*\<^sub>o\<^sub>w b = (inverse a \<^bold>*\<^sub>o\<^sub>w a) \<^bold>*\<^sub>o\<^sub>w c"
    by (metis assoc inverse_closed) 
  with assms show "b = c" 
    using group_ow_axioms by (fastforce simp: group_ow.group_left_neutral)
qed simp

sublocale monoid_ow U \<open>(\<^bold>*\<^sub>o\<^sub>w)\<close> \<open>\<^bold>1\<^sub>o\<^sub>w\<close>
proof
  show "a \<in> U \<Longrightarrow> a \<^bold>*\<^sub>o\<^sub>w \<^bold>1\<^sub>o\<^sub>w = a" for a
  proof-
    assume "a \<in> U" 
    with left_inverse[OF this] have "inverse a \<^bold>*\<^sub>o\<^sub>w (a \<^bold>*\<^sub>o\<^sub>w \<^bold>1\<^sub>o\<^sub>w) = inverse a \<^bold>*\<^sub>o\<^sub>w a"
      by (metis assoc group_left_neutral inverse_closed z_closed)
    with \<open>a \<in> U\<close> z_closed show "a \<^bold>*\<^sub>o\<^sub>w \<^bold>1\<^sub>o\<^sub>w = a"
      by (meson left_cancel f_closed inverse_closed)
  qed
qed (simp add: group_left_neutral)+

lemma inverse_image[simp]: "inverse ` U \<subseteq> U" by (simp add: image_subsetI)

end

lemma group_ow: "group = group_ow UNIV"
  unfolding 
    group_def group_ow_def  group_axioms_def group_ow_axioms_def semigroup_ow
  by simp

locale uminus_ow =
  fixes U :: "'ag set" and uminus :: "'ag \<Rightarrow> 'ag" (\<open>-\<^sub>o\<^sub>w _\<close> [81] 80) 
  assumes uminus_closed: "a \<in> U \<Longrightarrow> -\<^sub>o\<^sub>w a \<in> U"
begin

notation uminus (\<open>-\<^sub>o\<^sub>w _\<close> [81] 80)

lemma uminus_closed': "uminus ` U \<subseteq> U" by (auto simp: uminus_closed)
lemma uminus_closed'': "\<forall>a\<in>U. -\<^sub>o\<^sub>w a \<in> U" by (simp add: uminus_closed)

tts_register_sbts uminus | U by (rule tts_AB_transfer[OF uminus_closed'])

end

locale group_add_ow =
  minus_ow U minus + uminus_ow U uminus + monoid_add_ow U plus zero
  for U :: "'ag set" and minus plus zero uminus +
  assumes left_inverse: "a \<in> U \<Longrightarrow> (-\<^sub>o\<^sub>w a) +\<^sub>o\<^sub>w a = 0\<^sub>o\<^sub>w"
    and add_inv_conv_diff: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a +\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w b) = a -\<^sub>o\<^sub>w b"
begin

sublocale add: group_ow U \<open>(+\<^sub>o\<^sub>w)\<close> \<open>0\<^sub>o\<^sub>w\<close> uminus
  by unfold_locales (auto simp: uminus_closed left_inverse)

lemma inverse_unique:
  assumes "a \<in> U" and "b \<in> U" and "a +\<^sub>o\<^sub>w b = 0\<^sub>o\<^sub>w"
  shows "-\<^sub>o\<^sub>w a = b"
proof-
  from assms have "(-\<^sub>o\<^sub>w a +\<^sub>o\<^sub>w a) +\<^sub>o\<^sub>w b = -\<^sub>o\<^sub>w a"
    by (metis add.assoc uminus_closed add.right_neutral_mow) 
  thus ?thesis 
    unfolding left_inverse[OF \<open>a \<in> U\<close>] add.left_neutral_mow[OF \<open>b \<in> U\<close>] by simp
qed

lemma inverse_neutral[simp]: "-\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w = 0\<^sub>o\<^sub>w"
  by 
    (
      rule inverse_unique[
        OF zero_closed zero_closed add.left_neutral_mow[OF zero_closed]
        ]                                     
    )

lemma inverse_inverse: 
  assumes "a \<in> U"
  shows "-\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w a) = a"
  by 
    (
      rule inverse_unique[
        OF uminus_closed[OF assms] assms left_inverse[OF assms]
      ]
    )

lemma right_inverse: 
  assumes "a \<in> U"
  shows "a +\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w a) = 0\<^sub>o\<^sub>w"
proof -
  from assms have "a +\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w a) = -\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w a) +\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w a)"
    by (simp add: inverse_inverse)
  moreover have "\<dots> = 0\<^sub>o\<^sub>w" by (rule left_inverse[OF uminus_closed[OF assms]])
  ultimately show ?thesis by simp
qed

sublocale cancel_semigroup_add_ow U \<open>(+\<^sub>o\<^sub>w)\<close>
proof
  fix a b c assume "a \<in> U" and "b \<in> U" and "c \<in> U" and "a +\<^sub>o\<^sub>w b = a +\<^sub>o\<^sub>w c"
  from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> this have 
    "((-\<^sub>o\<^sub>w a) +\<^sub>o\<^sub>w a) +\<^sub>o\<^sub>w b = ((-\<^sub>o\<^sub>w a) +\<^sub>o\<^sub>w a) +\<^sub>o\<^sub>w c"
    by (auto simp: add.left_cancel)
  thus "b = c" 
    unfolding
      left_inverse[OF \<open>a \<in> U\<close>]
      add.left_neutral_mow[OF \<open>b \<in> U\<close>] 
      add.left_neutral_mow[OF \<open>c \<in> U\<close>]
    by simp
next
  fix a b c assume "a \<in> U" and "b \<in> U" and "c \<in> U" and "b +\<^sub>o\<^sub>w a = c +\<^sub>o\<^sub>w a"
  then have "b +\<^sub>o\<^sub>w (a +\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w a)) = c +\<^sub>o\<^sub>w (a +\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w a))" 
    by (metis add.assoc uminus_closed)
  thus "b = c"
    unfolding 
      right_inverse[OF \<open>a \<in> U\<close>]
      add.left_neutral_mow[OF \<open>b \<in> U\<close>] 
      add.right_neutral_mow[OF \<open>c \<in> U\<close>]
    by (simp add: \<open>b \<in> U\<close>)
qed

end

lemma group_add_ow: "class.group_add = group_add_ow UNIV"
  unfolding 
    class.group_add_def group_add_ow_def
    class.group_add_axioms_def group_add_ow_axioms_def
    minus_ow_def uminus_ow_def
    monoid_add_ow 
  by simp


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma group_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows "((A ===> A ===> A) ===> A ===> (A ===> A) ===> (=)) 
    (group_ow (Collect (Domainp A))) group"
proof -
  let ?P = "((A ===> A ===> A) ===> A ===> (A ===> A) ===> (=))"
  let ?group_ow = "group_ow (Collect (Domainp A))"
  have 
    "?P 
      (\<lambda>f z inv. ?group_ow f z inv) 
      (\<lambda>f z inv. z \<in> UNIV \<and> (\<forall>x\<in>UNIV. inv x \<in> UNIV) \<and> group f z inv)"
    unfolding group_ow_def group_def group_ow_axioms_def group_axioms_def
    apply transfer_prover_start
    apply transfer_step+
    by blast
  thus ?thesis by simp
qed

lemma group_add_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows 
    "((A ===> A ===> A) ===> (A ===> A ===> A) ===> A ===> (A ===> A) ===> (=)) 
      (group_add_ow (Collect (Domainp A))) class.group_add"
proof -
  let ?P = 
    "((A ===> A ===> A) ===> (A ===> A ===> A) ===> A ===> (A ===> A) ===> (=))"
  let ?group_add_ow = "group_add_ow (Collect (Domainp A))"
  have 
    "?P 
      (\<lambda>minus plus zero uminus. ?group_add_ow minus plus zero uminus) 
      (
        \<lambda>fi f z inv_f. 
          (\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. fi x y \<in> UNIV) \<and>
          (\<forall>x\<in>UNIV. inv_f x \<in> UNIV) \<and>  
          class.group_add fi f z inv_f
      )"
    unfolding 
      group_add_ow_def class.group_add_def
      group_add_ow_axioms_def class.group_add_axioms_def
      minus_ow_def uminus_ow_def
    apply transfer_prover_start
    apply transfer_step+
    by simp
  thus ?thesis by simp
qed

end


subsubsection\<open>Relativization\<close>

context group_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting group_ow_axioms and not_empty
  applying [OF f_closed' z_closed inverse_closed'']
begin

tts_lemma inverse_neutral: "inverse \<^bold>1\<^sub>o\<^sub>w = \<^bold>1\<^sub>o\<^sub>w"
  is group.inverse_neutral.
    
tts_lemma inverse_inverse:
  assumes "a \<in> U"
  shows "inverse (inverse a) = a"
    is group.inverse_inverse.

tts_lemma right_inverse:
  assumes "a \<in> U"
  shows "a \<^bold>*\<^sub>o\<^sub>w inverse a = \<^bold>1\<^sub>o\<^sub>w"
    is group.right_inverse.

tts_lemma inverse_distrib_swap:
  assumes "a \<in> U" and "b \<in> U"
  shows "inverse (a \<^bold>*\<^sub>o\<^sub>w b) = inverse b \<^bold>*\<^sub>o\<^sub>w inverse a"
    is group.inverse_distrib_swap.

tts_lemma right_cancel:
  assumes "b \<in> U" and "a \<in> U" and "c \<in> U"
  shows "(b \<^bold>*\<^sub>o\<^sub>w a = c \<^bold>*\<^sub>o\<^sub>w a) = (b = c)"
    is group.right_cancel.

tts_lemma inverse_unique:
  assumes "a \<in> U" and "b \<in> U" and "a \<^bold>*\<^sub>o\<^sub>w b = \<^bold>1\<^sub>o\<^sub>w"
  shows "inverse a = b"
    is group.inverse_unique.
end

end

context group_add_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting group_add_ow_axioms and zero.not_empty
  applying [OF minus_closed' plus_closed' zero_closed add.inverse_closed'']
begin

tts_lemma diff_0:
  assumes "a \<in> U"
  shows "0\<^sub>o\<^sub>w -\<^sub>o\<^sub>w a = -\<^sub>o\<^sub>w a"
    is group_add_class.diff_0.

tts_lemma diff_0_right:
  assumes "a \<in> U"
  shows "a -\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w = a"
    is group_add_class.diff_0_right.
    
tts_lemma diff_self:
  assumes "a \<in> U"
  shows "a -\<^sub>o\<^sub>w a = 0\<^sub>o\<^sub>w"
    is group_add_class.diff_self.
    
tts_lemma group_left_neutral:
  assumes "a \<in> U"
  shows "0\<^sub>o\<^sub>w +\<^sub>o\<^sub>w a = a"
    is group_add_class.add.group_left_neutral.
    
tts_lemma minus_minus:
  assumes "a \<in> U"
  shows "-\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w a) = a"
  is group_add_class.minus_minus.
    
tts_lemma right_minus:
  assumes "a \<in> U"
  shows "a +\<^sub>o\<^sub>w -\<^sub>o\<^sub>w a = 0\<^sub>o\<^sub>w"
  is group_add_class.right_minus.

tts_lemma left_minus:
  assumes "a \<in> U"
  shows "-\<^sub>o\<^sub>w a +\<^sub>o\<^sub>w a = 0\<^sub>o\<^sub>w"
    is group_add_class.left_minus.
    
tts_lemma add_diff_cancel:
  assumes "a \<in> U" and "b \<in> U"
  shows "a +\<^sub>o\<^sub>w b -\<^sub>o\<^sub>w b = a"
  is group_add_class.add_diff_cancel.
    
tts_lemma diff_add_cancel:
  assumes "a \<in> U" and "b \<in> U"
  shows "a -\<^sub>o\<^sub>w b +\<^sub>o\<^sub>w b = a"
    is group_add_class.diff_add_cancel.
    
tts_lemma diff_conv_add_uminus:
  assumes "a \<in> U" and "b \<in> U"
  shows "a -\<^sub>o\<^sub>w b = a +\<^sub>o\<^sub>w -\<^sub>o\<^sub>w b"
    is group_add_class.diff_conv_add_uminus.
    
tts_lemma diff_minus_eq_add:
  assumes "a \<in> U" and "b \<in> U"
  shows "a -\<^sub>o\<^sub>w -\<^sub>o\<^sub>w b = a +\<^sub>o\<^sub>w b"
    is group_add_class.diff_minus_eq_add.
  
tts_lemma add_uminus_conv_diff:
  assumes "a \<in> U" and "b \<in> U"
  shows "a +\<^sub>o\<^sub>w -\<^sub>o\<^sub>w b = a -\<^sub>o\<^sub>w b"
    is group_add_class.add_uminus_conv_diff.

tts_lemma minus_diff_eq:
  assumes "a \<in> U" and "b \<in> U"
  shows "-\<^sub>o\<^sub>w (a -\<^sub>o\<^sub>w b) = b -\<^sub>o\<^sub>w a"
    is group_add_class.minus_diff_eq.

tts_lemma add_minus_cancel:
  assumes "a \<in> U" and "b \<in> U"
  shows "a +\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w a +\<^sub>o\<^sub>w b) = b"
    is group_add_class.add_minus_cancel.
    
tts_lemma minus_add_cancel:
  assumes "a \<in> U" and "b \<in> U"
  shows "-\<^sub>o\<^sub>w a +\<^sub>o\<^sub>w (a +\<^sub>o\<^sub>w b) = b"
    is group_add_class.minus_add_cancel.

tts_lemma neg_0_equal_iff_equal:
  assumes "a \<in> U"
  shows "(0\<^sub>o\<^sub>w = -\<^sub>o\<^sub>w a) = (0\<^sub>o\<^sub>w = a)"
    is group_add_class.neg_0_equal_iff_equal.
    
tts_lemma neg_equal_0_iff_equal:
  assumes "a \<in> U"
  shows "(-\<^sub>o\<^sub>w a = 0\<^sub>o\<^sub>w) = (a = 0\<^sub>o\<^sub>w)"
    is group_add_class.neg_equal_0_iff_equal.
    
tts_lemma eq_iff_diff_eq_0:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a = b) = (a -\<^sub>o\<^sub>w b = 0\<^sub>o\<^sub>w)"
    is group_add_class.eq_iff_diff_eq_0.

tts_lemma equation_minus_iff:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a = -\<^sub>o\<^sub>w b) = (b = -\<^sub>o\<^sub>w a)"
    is group_add_class.equation_minus_iff.

tts_lemma minus_equation_iff:
  assumes "a \<in> U" and "b \<in> U"
  shows "(-\<^sub>o\<^sub>w a = b) = (-\<^sub>o\<^sub>w b = a)"
    is group_add_class.minus_equation_iff.

tts_lemma neg_equal_iff_equal:
  assumes "a \<in> U" and "b \<in> U"
  shows "(-\<^sub>o\<^sub>w a = -\<^sub>o\<^sub>w b) = (a = b)"
    is group_add_class.neg_equal_iff_equal.

tts_lemma right_minus_eq:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a -\<^sub>o\<^sub>w b = 0\<^sub>o\<^sub>w) = (a = b)"
    is group_add_class.right_minus_eq.

tts_lemma minus_add:
  assumes "a \<in> U" and "b \<in> U"
  shows "-\<^sub>o\<^sub>w (a +\<^sub>o\<^sub>w b) = -\<^sub>o\<^sub>w b +\<^sub>o\<^sub>w -\<^sub>o\<^sub>w a"
    is group_add_class.minus_add.

tts_lemma eq_neg_iff_add_eq_0:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a = -\<^sub>o\<^sub>w b) = (a +\<^sub>o\<^sub>w b = 0\<^sub>o\<^sub>w)"
    is group_add_class.eq_neg_iff_add_eq_0.

tts_lemma neg_eq_iff_add_eq_0:
  assumes "a \<in> U" and "b \<in> U"
  shows "(-\<^sub>o\<^sub>w a = b) = (a +\<^sub>o\<^sub>w b = 0\<^sub>o\<^sub>w)"
    is group_add_class.neg_eq_iff_add_eq_0.

tts_lemma add_eq_0_iff2:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a +\<^sub>o\<^sub>w b = 0\<^sub>o\<^sub>w) = (a = -\<^sub>o\<^sub>w b)"
    is group_add_class.add_eq_0_iff2.

tts_lemma add_eq_0_iff:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a +\<^sub>o\<^sub>w b = 0\<^sub>o\<^sub>w) = (b = -\<^sub>o\<^sub>w a)"
    is group_add_class.add_eq_0_iff.

tts_lemma diff_diff_eq2:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "a -\<^sub>o\<^sub>w (b -\<^sub>o\<^sub>w c) = a +\<^sub>o\<^sub>w c -\<^sub>o\<^sub>w b"
    is group_add_class.diff_diff_eq2.

tts_lemma diff_add_eq_diff_diff_swap:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "a -\<^sub>o\<^sub>w (b +\<^sub>o\<^sub>w c) = a -\<^sub>o\<^sub>w c -\<^sub>o\<^sub>w b"
    is group_add_class.diff_add_eq_diff_diff_swap.

tts_lemma add_diff_eq:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "a +\<^sub>o\<^sub>w (b -\<^sub>o\<^sub>w c) = a +\<^sub>o\<^sub>w b -\<^sub>o\<^sub>w c"
    is group_add_class.add_diff_eq.

tts_lemma eq_diff_eq:
  assumes "a \<in> U" and "c \<in> U" and "b \<in> U"
  shows "(a = c -\<^sub>o\<^sub>w b) = (a +\<^sub>o\<^sub>w b = c)"
    is group_add_class.eq_diff_eq.

tts_lemma diff_eq_eq:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "(a -\<^sub>o\<^sub>w b = c) = (a = c +\<^sub>o\<^sub>w b)"
    is group_add_class.diff_eq_eq.

tts_lemma left_cancel:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "(a +\<^sub>o\<^sub>w b = a +\<^sub>o\<^sub>w c) = (b = c)"
    is group_add_class.add.left_cancel.

tts_lemma right_cancel:
  assumes "b \<in> U" and "a \<in> U" and "c \<in> U"
  shows "(b +\<^sub>o\<^sub>w a = c +\<^sub>o\<^sub>w a) = (b = c)"
    is group_add_class.add.right_cancel.

tts_lemma minus_unique:
  assumes "a \<in> U" and "b \<in> U" and "a +\<^sub>o\<^sub>w b = 0\<^sub>o\<^sub>w"
  shows "-\<^sub>o\<^sub>w a = b"
    is group_add_class.minus_unique.

tts_lemma diff_eq_diff_eq:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U" and "a -\<^sub>o\<^sub>w b = c -\<^sub>o\<^sub>w d"
  shows "(a = b) = (c = d)"
    is group_add_class.diff_eq_diff_eq.

end

end



subsection\<open>Abelian groups\<close>


subsubsection\<open>Definitions and common properties\<close>

locale ab_group_add_ow =
  minus_ow U minus + uminus_ow U uminus + comm_monoid_add_ow U plus zero
  for U :: "'ag set" and plus zero minus uminus +
  assumes ab_left_minus: "a \<in> U \<Longrightarrow> -\<^sub>o\<^sub>w a +\<^sub>o\<^sub>w a = 0\<^sub>o\<^sub>w"
  assumes ab_diff_conv_add_uminus: 
    "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a -\<^sub>o\<^sub>w b = a +\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w b)"
begin

sublocale group_add_ow 
  by unfold_locales (simp_all add: ab_left_minus ab_diff_conv_add_uminus)

sublocale cancel_comm_monoid_add_ow 
  apply unfold_locales
  subgoal using add.commute by (fastforce simp: add_diff_cancel)
  subgoal by (metis add.commute diff_add_eq_diff_diff_swap)
  done

end

lemma ab_group_add_ow: "class.ab_group_add = ab_group_add_ow UNIV"
  unfolding 
  class.ab_group_add_def ab_group_add_ow_def
  class.ab_group_add_axioms_def ab_group_add_ow_axioms_def
  minus_ow_def uminus_ow_def
  comm_monoid_add_ow
  by simp

lemma ab_group_add_ow_UNIV_axioms: 
  "ab_group_add_ow (UNIV::'a::ab_group_add set) (+) 0 (-) uminus"
  by (fold ab_group_add_ow) (rule ab_group_add_class.ab_group_add_axioms)


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma ab_group_add_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> A ===> (A ===> A ===> A) ===> (A ===> A) ===> (=))
      (ab_group_add_ow (Collect (Domainp A))) class.ab_group_add"
proof -
  let ?P = 
    "((A ===> A ===> A) ===> A ===> (A ===> A ===> A) ===> (A ===> A) ===> (=))"
  let ?ab_group_add_ow = "ab_group_add_ow (Collect (Domainp A))"
  have 
    "?P 
      ?ab_group_add_ow 
      (
        \<lambda>plus zero minus uminus. 
          (\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. minus x y \<in> UNIV) \<and>
          (\<forall>x\<in>UNIV. uminus x \<in> UNIV) \<and>  
          class.ab_group_add plus zero minus uminus
      )"
    unfolding 
      ab_group_add_ow_def class.ab_group_add_def
      ab_group_add_ow_axioms_def class.ab_group_add_axioms_def
      minus_ow_def uminus_ow_def
    apply transfer_prover_start
    apply transfer_step+
    by simp
  thus ?thesis by simp
qed

end


subsubsection\<open>Relativization\<close>

context ab_group_add_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting ab_group_add_ow_axioms and zero.not_empty
  applying [OF plus_closed' zero_closed minus_closed' add.inverse_closed'']
begin

tts_lemma uminus_add_conv_diff:
  assumes "a \<in> U" and "b \<in> U"
  shows "-\<^sub>o\<^sub>w a +\<^sub>o\<^sub>w b = b -\<^sub>o\<^sub>w a"
    is ab_group_add_class.uminus_add_conv_diff.
    
tts_lemma diff_add_eq:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "a -\<^sub>o\<^sub>w b +\<^sub>o\<^sub>w c = a +\<^sub>o\<^sub>w c -\<^sub>o\<^sub>w b"
    is ab_group_add_class.diff_add_eq.

end

end

text\<open>\newpage\<close>

end