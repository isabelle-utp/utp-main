(* Title: Examples/SML_Relativization/Algebra/SML_Semigroups.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Relativization of the results about semigroups\<close>
theory SML_Semigroups
  imports 
    "../SML_Introduction"
    "../Foundations/Lifting_Set_Ext"
begin



subsection\<open>Simple semigroups\<close>


subsubsection\<open>Definitions and common properties\<close>

locale semigroup_ow = 
  fixes U :: "'ag set" and f :: "['ag, 'ag] \<Rightarrow> 'ag" (infixl \<open>\<^bold>*\<^sub>o\<^sub>w\<close> 70)
  assumes f_closed: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a \<^bold>*\<^sub>o\<^sub>w b \<in> U"
  assumes assoc: "\<lbrakk> a \<in> U; b \<in> U; c \<in> U \<rbrakk> \<Longrightarrow> a \<^bold>*\<^sub>o\<^sub>w b \<^bold>*\<^sub>o\<^sub>w c = a \<^bold>*\<^sub>o\<^sub>w (b \<^bold>*\<^sub>o\<^sub>w c)"
begin

notation f (infixl \<open>\<^bold>*\<^sub>o\<^sub>w\<close> 70)

lemma f_closed'[simp]: "\<forall>x\<in>U. \<forall>y\<in>U. x \<^bold>*\<^sub>o\<^sub>w y \<in> U" by (simp add: f_closed)

tts_register_sbts \<open>(\<^bold>*\<^sub>o\<^sub>w)\<close> | U by (rule tts_AA_A_transfer[OF f_closed])

end

lemma semigroup_ow: "semigroup = semigroup_ow UNIV"
  unfolding semigroup_def semigroup_ow_def by simp

locale plus_ow =
  fixes U :: "'ag set" and plus :: "['ag, 'ag] \<Rightarrow> 'ag" (infixl \<open>+\<^sub>o\<^sub>w\<close> 65)
  assumes plus_closed[simp, intro]: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a +\<^sub>o\<^sub>w b \<in> U"
begin

notation plus (infixl \<open>+\<^sub>o\<^sub>w\<close> 65)

lemma plus_closed'[simp]: "\<forall>x\<in>U. \<forall>y\<in>U. x +\<^sub>o\<^sub>w y \<in> U" by simp

tts_register_sbts \<open>(+\<^sub>o\<^sub>w)\<close> | U  by (rule tts_AA_A_transfer[OF plus_closed])

end

locale times_ow =
  fixes U :: "'ag set" and times :: "['ag, 'ag] \<Rightarrow> 'ag" (infixl \<open>*\<^sub>o\<^sub>w\<close> 70)
  assumes times_closed[simp, intro]: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a *\<^sub>o\<^sub>w b \<in> U"
begin

notation times (infixl \<open>*\<^sub>o\<^sub>w\<close> 70)

lemma times_closed'[simp]: "\<forall>x\<in>U. \<forall>y\<in>U. x *\<^sub>o\<^sub>w y \<in> U" by simp

tts_register_sbts \<open>(*\<^sub>o\<^sub>w)\<close> | U  by (rule tts_AA_A_transfer[OF times_closed])

end

locale semigroup_add_ow = plus_ow U plus 
  for U :: "'ag set" and plus +
  assumes plus_assoc: 
    "\<lbrakk> a \<in> U; b \<in> U; c \<in> U \<rbrakk> \<Longrightarrow> a +\<^sub>o\<^sub>w b +\<^sub>o\<^sub>w c = a +\<^sub>o\<^sub>w (b +\<^sub>o\<^sub>w c)"
begin

sublocale add: semigroup_ow U \<open>(+\<^sub>o\<^sub>w)\<close> 
  by unfold_locales (auto simp: plus_assoc)

end

lemma semigroup_add_ow: "class.semigroup_add = semigroup_add_ow UNIV"
  unfolding 
    class.semigroup_add_def semigroup_add_ow_def
    semigroup_add_ow_axioms_def plus_ow_def
  by simp

locale semigroup_mult_ow = times_ow U times 
  for U :: "'ag set" and times +
  assumes mult_assoc: 
    "\<lbrakk> a \<in> U; b \<in> U; c \<in> U \<rbrakk> \<Longrightarrow> a *\<^sub>o\<^sub>w b *\<^sub>o\<^sub>w c = a *\<^sub>o\<^sub>w (b *\<^sub>o\<^sub>w c)"
begin

sublocale mult: semigroup_ow U \<open>(*\<^sub>o\<^sub>w)\<close> 
  by unfold_locales (auto simp: times_closed' mult_assoc)

end

lemma semigroup_mult_ow: "class.semigroup_mult = semigroup_mult_ow UNIV"
  unfolding 
    class.semigroup_mult_def semigroup_mult_ow_def
    semigroup_mult_ow_axioms_def times_ow_def
  by simp


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma semigroup_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> (=)) 
      (semigroup_ow (Collect (Domainp A))) semigroup"
proof -
  let ?P = "((A ===> A ===> A) ===> (=))"
  let ?semigroup_ow = "semigroup_ow (Collect (Domainp A))"
  let ?rf_UNIV = 
    "(\<lambda>f::['b, 'b] \<Rightarrow> 'b. (\<forall>x y. x \<in> UNIV \<longrightarrow> y \<in> UNIV \<longrightarrow> f x y \<in> UNIV))"
  have "?P ?semigroup_ow (\<lambda>f. ?rf_UNIV f \<and> semigroup f)"
    unfolding semigroup_ow_def semigroup_def
    apply transfer_prover_start
    apply transfer_step+
    by simp
  thus ?thesis by simp
qed

lemma semigroup_add_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> (=)) 
      (semigroup_add_ow (Collect (Domainp A))) class.semigroup_add"
proof -
  let ?P = "((A ===> A ===> A) ===> (=))"
  let ?semigroup_add_ow = "(\<lambda>f. semigroup_add_ow (Collect (Domainp A)) f)"
  let ?rf_UNIV = 
    "(\<lambda>f::['b, 'b] \<Rightarrow> 'b. (\<forall>x y. x \<in> UNIV \<longrightarrow> y \<in> UNIV \<longrightarrow> f x y \<in> UNIV))"
  have "?P ?semigroup_add_ow (\<lambda>f. ?rf_UNIV f \<and> class.semigroup_add f)"
    unfolding 
      semigroup_add_ow_def class.semigroup_add_def
      semigroup_add_ow_axioms_def plus_ow_def
    apply transfer_prover_start
    apply transfer_step+    
    by simp
  thus ?thesis by simp
qed

lemma semigroup_mult_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> (=)) 
      (semigroup_mult_ow (Collect (Domainp A))) class.semigroup_mult"
proof -
  let ?P = "((A ===> A ===> A) ===> (=))"
  let ?semigroup_mult_ow = "(\<lambda>f. semigroup_mult_ow (Collect (Domainp A)) f)"
  let ?rf_UNIV = 
    "(\<lambda>f::['b, 'b] \<Rightarrow> 'b. (\<forall>x y. x \<in> UNIV \<longrightarrow> y \<in> UNIV \<longrightarrow> f x y \<in> UNIV))"
  have "?P ?semigroup_mult_ow (\<lambda>f. ?rf_UNIV f \<and> class.semigroup_mult f)"
    unfolding 
      semigroup_mult_ow_def class.semigroup_mult_def
      semigroup_mult_ow_axioms_def times_ow_def
    apply transfer_prover_start
    apply transfer_step+
    by simp
  thus ?thesis by simp
qed

end



subsection\<open>Cancellative semigroups\<close>


subsubsection\<open>Definitions and common properties\<close>
 
locale cancel_semigroup_add_ow = semigroup_add_ow U plus
  for U :: "'ag set" and plus +
  assumes add_left_imp_eq: 
    "\<lbrakk> a \<in> U; b \<in> U; c \<in> U; a +\<^sub>o\<^sub>w b = a +\<^sub>o\<^sub>w c \<rbrakk> \<Longrightarrow> b = c"
  assumes add_right_imp_eq: 
    "\<lbrakk> b \<in> U; a \<in> U; c \<in> U; b +\<^sub>o\<^sub>w a = c +\<^sub>o\<^sub>w a \<rbrakk> \<Longrightarrow> b = c"

lemma cancel_semigroup_add_ow: 
  "class.cancel_semigroup_add = cancel_semigroup_add_ow UNIV"
  unfolding 
    class.cancel_semigroup_add_def cancel_semigroup_add_ow_def
    cancel_semigroup_add_ow_axioms_def class.cancel_semigroup_add_axioms_def
    semigroup_add_ow
  by simp


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma cancel_semigroup_add_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> (=)) 
      (cancel_semigroup_add_ow (Collect (Domainp A)))  
      class.cancel_semigroup_add"
  unfolding cancel_semigroup_add_ow_def class.cancel_semigroup_add_def
  unfolding 
    cancel_semigroup_add_ow_axioms_def class.cancel_semigroup_add_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  by simp

end


subsubsection\<open>Relativization\<close>

context cancel_semigroup_add_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting cancel_semigroup_add_ow_axioms
  eliminating through simp
begin

tts_lemma add_right_cancel:
  assumes "b \<in> U" and "a \<in> U" and "c \<in> U"
  shows "(b +\<^sub>o\<^sub>w a = c +\<^sub>o\<^sub>w a) = (b = c)"
  is cancel_semigroup_add_class.add_right_cancel.

tts_lemma add_left_cancel:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "(a +\<^sub>o\<^sub>w b = a +\<^sub>o\<^sub>w c) = (b = c)"
  is cancel_semigroup_add_class.add_left_cancel.
    
tts_lemma bij_betw_add:
  assumes "a \<in> U" and "A \<subseteq> U" and "B \<subseteq> U"
  shows "bij_betw ((+\<^sub>o\<^sub>w) a) A B = ((+\<^sub>o\<^sub>w) a ` A = B)"
    is cancel_semigroup_add_class.bij_betw_add.

tts_lemma inj_on_add:
  assumes "a \<in> U" and "A \<subseteq> U"
  shows "inj_on ((+\<^sub>o\<^sub>w) a) A"
    is cancel_semigroup_add_class.inj_on_add.

tts_lemma inj_add_left:
  assumes "a \<in> U"
  shows "inj_on ((+\<^sub>o\<^sub>w) a) U"
    is cancel_semigroup_add_class.inj_add_left.

tts_lemma inj_on_add':
  assumes "a \<in> U" and "A \<subseteq> U"
  shows "inj_on (\<lambda>b. b +\<^sub>o\<^sub>w a) A"
    is cancel_semigroup_add_class.inj_on_add'.

end

end



subsection\<open>Commutative semigroups\<close>


subsubsection\<open>Definitions and common properties\<close>

locale abel_semigroup_ow =
  semigroup_ow U f for U :: "'ag set" and f +
  assumes commute: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a \<^bold>*\<^sub>o\<^sub>w b = b \<^bold>*\<^sub>o\<^sub>w a"
begin

lemma fun_left_comm: 
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U" 
  shows "y \<^bold>*\<^sub>o\<^sub>w (x \<^bold>*\<^sub>o\<^sub>w z) = x \<^bold>*\<^sub>o\<^sub>w (y \<^bold>*\<^sub>o\<^sub>w z)"
  using assms by (metis assoc commute)

end

lemma abel_semigroup_ow: "abel_semigroup = abel_semigroup_ow UNIV"
  unfolding 
    abel_semigroup_def abel_semigroup_ow_def
    abel_semigroup_axioms_def abel_semigroup_ow_axioms_def
    semigroup_ow
  by simp

locale ab_semigroup_add_ow =
  semigroup_add_ow U plus for U :: "'ag set" and plus +
  assumes add_commute: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a +\<^sub>o\<^sub>w b = b +\<^sub>o\<^sub>w a"
begin

sublocale add: abel_semigroup_ow U \<open>(+\<^sub>o\<^sub>w)\<close> 
  by unfold_locales (rule add_commute)
  
end

lemma ab_semigroup_add_ow: "class.ab_semigroup_add = ab_semigroup_add_ow UNIV"
  unfolding 
    class.ab_semigroup_add_def ab_semigroup_add_ow_def
    class.ab_semigroup_add_axioms_def ab_semigroup_add_ow_axioms_def
    semigroup_add_ow
  by simp

locale ab_semigroup_mult_ow = 
  semigroup_mult_ow U times for U :: "'ag set" and times+
  assumes mult_commute: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a *\<^sub>o\<^sub>w b = b *\<^sub>o\<^sub>w a"
begin

sublocale mult: abel_semigroup_ow U \<open>(*\<^sub>o\<^sub>w)\<close> 
  by unfold_locales (rule mult_commute)
  
end

lemma ab_semigroup_mult_ow: 
  "class.ab_semigroup_mult = ab_semigroup_mult_ow UNIV"
  unfolding 
    class.ab_semigroup_mult_def ab_semigroup_mult_ow_def
    class.ab_semigroup_mult_axioms_def ab_semigroup_mult_ow_axioms_def
    semigroup_mult_ow
  by simp


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma abel_semigroup_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> (=)) 
      (abel_semigroup_ow (Collect (Domainp A))) abel_semigroup"
  unfolding 
    abel_semigroup_ow_def abel_semigroup_def
    abel_semigroup_ow_axioms_def abel_semigroup_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  unfolding Ball_def by simp

lemma ab_semigroup_add_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> (=)) 
      (ab_semigroup_add_ow (Collect (Domainp A))) class.ab_semigroup_add"
  unfolding 
    ab_semigroup_add_ow_def class.ab_semigroup_add_def
    ab_semigroup_add_ow_axioms_def class.ab_semigroup_add_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  by simp

lemma ab_semigroup_mult_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> (=)) 
      (ab_semigroup_mult_ow (Collect (Domainp A))) class.ab_semigroup_mult"
  unfolding ab_semigroup_mult_ow_def class.ab_semigroup_mult_def
  unfolding ab_semigroup_mult_ow_axioms_def class.ab_semigroup_mult_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  by simp

end


subsubsection\<open>Relativization\<close>

context abel_semigroup_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting abel_semigroup_ow_axioms
  eliminating through simp
begin

tts_lemma left_commute:
  assumes "b \<in> U" and "a \<in> U" and "c \<in> U"
  shows "b \<^bold>*\<^sub>o\<^sub>w (a \<^bold>*\<^sub>o\<^sub>w c) = a \<^bold>*\<^sub>o\<^sub>w (b \<^bold>*\<^sub>o\<^sub>w c)"
    is abel_semigroup.left_commute.

end

end

context ab_semigroup_add_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting ab_semigroup_add_ow_axioms
  eliminating through simp
begin

tts_lemma add_ac:
  shows "\<lbrakk>a \<in> U; b \<in> U; c \<in> U\<rbrakk> \<Longrightarrow> a +\<^sub>o\<^sub>w b +\<^sub>o\<^sub>w c = a +\<^sub>o\<^sub>w (b +\<^sub>o\<^sub>w c)"
    is ab_semigroup_add_class.add_ac(1)
    and "\<lbrakk>a \<in> U; b \<in> U\<rbrakk> \<Longrightarrow> a +\<^sub>o\<^sub>w b = b +\<^sub>o\<^sub>w a"
    is ab_semigroup_add_class.add_ac(2)
    and "\<lbrakk>b \<in> U; a \<in> U; c \<in> U\<rbrakk> \<Longrightarrow> b +\<^sub>o\<^sub>w (a +\<^sub>o\<^sub>w c) = a +\<^sub>o\<^sub>w (b +\<^sub>o\<^sub>w c)"
    is ab_semigroup_add_class.add_ac(3).

end

end

context ab_semigroup_mult_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting ab_semigroup_mult_ow_axioms
  eliminating through simp
begin

tts_lemma mult_ac:
  shows "\<lbrakk>a \<in> U; b \<in> U; c \<in> U\<rbrakk> \<Longrightarrow> a *\<^sub>o\<^sub>w b *\<^sub>o\<^sub>w c = a *\<^sub>o\<^sub>w (b *\<^sub>o\<^sub>w c)"
    is ab_semigroup_mult_class.mult_ac(1)
    and "\<lbrakk>a \<in> U; b \<in> U\<rbrakk> \<Longrightarrow> a *\<^sub>o\<^sub>w b = b *\<^sub>o\<^sub>w a"
    is ab_semigroup_mult_class.mult_ac(2)
    and "\<lbrakk>b \<in> U; a \<in> U; c \<in> U\<rbrakk> \<Longrightarrow> b *\<^sub>o\<^sub>w (a *\<^sub>o\<^sub>w c) = a *\<^sub>o\<^sub>w (b *\<^sub>o\<^sub>w c)"
    is ab_semigroup_mult_class.mult_ac(3).

end

end



subsection\<open>Cancellative commutative semigroups\<close>


subsubsection\<open>Definitions and common properties\<close>

locale minus_ow =
  fixes U :: "'ag set" and minus :: "['ag, 'ag] \<Rightarrow> 'ag" (infixl \<open>-\<^sub>o\<^sub>w\<close> 65)
  assumes minus_closed[simp,intro]: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a -\<^sub>o\<^sub>w b \<in> U"
begin

notation minus (infixl \<open>-\<^sub>o\<^sub>w\<close> 65)

lemma minus_closed'[simp]: "\<forall>x\<in>U. \<forall>y\<in>U. x -\<^sub>o\<^sub>w y \<in> U" by simp

tts_register_sbts \<open>(-\<^sub>o\<^sub>w)\<close> | U by (rule tts_AA_A_transfer[OF minus_closed])

end

locale cancel_ab_semigroup_add_ow = 
  ab_semigroup_add_ow U plus + minus_ow U minus
  for U :: "'ag set" and plus minus +
  assumes add_diff_cancel_left'[simp]: 
    "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> (a +\<^sub>o\<^sub>w b) -\<^sub>o\<^sub>w a = b"
  assumes diff_diff_add: 
    "\<lbrakk> a \<in> U; b \<in> U; c \<in> U \<rbrakk> \<Longrightarrow> a -\<^sub>o\<^sub>w b -\<^sub>o\<^sub>w c = a -\<^sub>o\<^sub>w (b +\<^sub>o\<^sub>w c)"
begin

sublocale cancel_semigroup_add_ow U \<open>(+\<^sub>o\<^sub>w)\<close>
  apply unfold_locales
  subgoal by (metis add_diff_cancel_left')
  subgoal by (metis add.commute add_diff_cancel_left')
  done

end

lemma cancel_ab_semigroup_add_ow: 
  "class.cancel_ab_semigroup_add = cancel_ab_semigroup_add_ow UNIV"
  unfolding 
    class.cancel_ab_semigroup_add_def 
    cancel_ab_semigroup_add_ow_def
    class.cancel_ab_semigroup_add_axioms_def
    cancel_ab_semigroup_add_ow_axioms_def
    minus_ow_def
    ab_semigroup_add_ow
  by simp


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma cancel_ab_semigroup_add_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> (A ===> A ===> A) ===> (=)) 
      (cancel_ab_semigroup_add_ow (Collect (Domainp A))) 
      class.cancel_ab_semigroup_add"
proof -
  let ?P = "((A ===> A ===> A) ===> (A ===> A ===> A) ===> (=))"
  let ?cancel_ab_semigroup_add_ow = 
    "cancel_ab_semigroup_add_ow (Collect (Domainp A))"
  let ?rf_UNIV = 
    "(\<lambda>f::['b, 'b] \<Rightarrow> 'b. (\<forall>x y. x \<in> UNIV \<longrightarrow> y \<in> UNIV \<longrightarrow> f x y \<in> UNIV))"
  have 
    "?P 
      ?cancel_ab_semigroup_add_ow 
      (\<lambda>f fi. ?rf_UNIV fi \<and> class.cancel_ab_semigroup_add f fi)"
    unfolding 
      class.cancel_ab_semigroup_add_def 
      cancel_ab_semigroup_add_ow_def
      class.cancel_ab_semigroup_add_axioms_def 
      cancel_ab_semigroup_add_ow_axioms_def
      minus_ow_def
    apply transfer_prover_start
    apply transfer_step+
    unfolding Ball_def by auto
  thus ?thesis by simp
qed

end


subsubsection\<open>Relativization\<close>

context cancel_ab_semigroup_add_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting cancel_ab_semigroup_add_ow_axioms
  eliminating through simp
begin

tts_lemma add_diff_cancel_right':
  assumes "a \<in> U" and "b \<in> U"
  shows "a +\<^sub>o\<^sub>w b -\<^sub>o\<^sub>w b = a"
    is cancel_ab_semigroup_add_class.add_diff_cancel_right'.

tts_lemma add_diff_cancel_right:
  assumes "a \<in> U" and "c \<in> U" and "b \<in> U"
  shows "a +\<^sub>o\<^sub>w c -\<^sub>o\<^sub>w (b +\<^sub>o\<^sub>w c) = a -\<^sub>o\<^sub>w b"
    is cancel_ab_semigroup_add_class.add_diff_cancel_right.

tts_lemma add_diff_cancel_left:
  assumes "c \<in> U" and "a \<in> U" and "b \<in> U"
  shows "c +\<^sub>o\<^sub>w a -\<^sub>o\<^sub>w (c +\<^sub>o\<^sub>w b) = a -\<^sub>o\<^sub>w b"
    is cancel_ab_semigroup_add_class.add_diff_cancel_left.

tts_lemma diff_right_commute:
  assumes "a \<in> U" and "c \<in> U" and "b \<in> U"
  shows "a -\<^sub>o\<^sub>w c -\<^sub>o\<^sub>w b = a -\<^sub>o\<^sub>w b -\<^sub>o\<^sub>w c"
    is cancel_ab_semigroup_add_class.diff_right_commute.

tts_lemma diff_diff_eq:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "a -\<^sub>o\<^sub>w b -\<^sub>o\<^sub>w c = a -\<^sub>o\<^sub>w (b +\<^sub>o\<^sub>w c)"
    is diff_diff_eq.

end

end

text\<open>\newpage\<close>

end