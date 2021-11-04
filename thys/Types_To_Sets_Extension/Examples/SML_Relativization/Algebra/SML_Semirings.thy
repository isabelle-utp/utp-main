(* Title: Examples/SML_Relativization/Algebra/SML_Semirings.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Relativization of the results about semirings\<close>
theory SML_Semirings
  imports SML_Groups
begin



subsection\<open>Semirings\<close>


subsubsection\<open>Definitions and common properties\<close>

locale semiring_ow =
  ab_semigroup_add_ow U plus + semigroup_mult_ow U times 
  for U :: "'ag set" and plus times +
  assumes distrib_right[simp]: 
    "\<lbrakk> a \<in> U; b \<in> U; c \<in> U \<rbrakk> \<Longrightarrow> (a +\<^sub>o\<^sub>w b) *\<^sub>o\<^sub>w c = a *\<^sub>o\<^sub>w c +\<^sub>o\<^sub>w b *\<^sub>o\<^sub>w c"
  assumes distrib_left[simp]: 
    "\<lbrakk> a \<in> U; b \<in> U; c \<in> U \<rbrakk> \<Longrightarrow> a *\<^sub>o\<^sub>w (b +\<^sub>o\<^sub>w c) = a *\<^sub>o\<^sub>w b +\<^sub>o\<^sub>w a *\<^sub>o\<^sub>w c"

lemma semiring_ow: "class.semiring = semiring_ow UNIV"
  unfolding 
    class.semiring_def semiring_ow_def
    class.semiring_axioms_def semiring_ow_axioms_def
    ab_semigroup_add_ow semigroup_mult_ow
  by simp


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma semiring_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> (A ===> A ===> A) ===> (=)) 
      (semiring_ow (Collect (Domainp A))) class.semiring"
  unfolding 
    semiring_ow_def class.semiring_def
    semiring_ow_axioms_def class.semiring_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  by simp

end


subsubsection\<open>Relativization\<close>

context semiring_ow
begin

tts_context
  tts: (?'a to U)
  substituting semiring_ow_axioms
  eliminating through simp
begin

tts_lemma combine_common_factor:
  assumes "a \<in> U" and "e \<in> U" and "b \<in> U" and "c \<in> U"
  shows "a *\<^sub>o\<^sub>w e +\<^sub>o\<^sub>w (b *\<^sub>o\<^sub>w e +\<^sub>o\<^sub>w c) = (a +\<^sub>o\<^sub>w b) *\<^sub>o\<^sub>w e +\<^sub>o\<^sub>w c"
    is semiring_class.combine_common_factor.

end

end



subsection\<open>Commutative semirings\<close>


subsubsection\<open>Definitions and common properties\<close>

locale comm_semiring_ow = 
  ab_semigroup_add_ow U plus + ab_semigroup_mult_ow U times
  for U :: "'ag set" and plus times +
  assumes distrib: 
    "\<lbrakk>a \<in> U; b \<in> U; c \<in> U\<rbrakk> \<Longrightarrow> (a +\<^sub>o\<^sub>w b) *\<^sub>o\<^sub>w c = a *\<^sub>o\<^sub>w c +\<^sub>o\<^sub>w b *\<^sub>o\<^sub>w c"
begin

sublocale semiring_ow
proof
  fix a b c :: 'ag
  assume "a \<in> U" and "b \<in> U" and "c \<in> U"
  then show "(a +\<^sub>o\<^sub>w b) *\<^sub>o\<^sub>w c = a *\<^sub>o\<^sub>w c +\<^sub>o\<^sub>w b *\<^sub>o\<^sub>w c" by (simp only: distrib)
  show "a *\<^sub>o\<^sub>w (b +\<^sub>o\<^sub>w c) = a *\<^sub>o\<^sub>w b +\<^sub>o\<^sub>w a *\<^sub>o\<^sub>w c"
  proof-
    from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have "a *\<^sub>o\<^sub>w (b +\<^sub>o\<^sub>w c) = (b +\<^sub>o\<^sub>w c) *\<^sub>o\<^sub>w a" 
      by (simp add: mult_commute)
    with \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have "a *\<^sub>o\<^sub>w (b +\<^sub>o\<^sub>w c) = b *\<^sub>o\<^sub>w a +\<^sub>o\<^sub>w c *\<^sub>o\<^sub>w a" 
      by (simp only: distrib)
    with \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> show ?thesis  by (simp only: mult_commute)
  qed
qed

end

lemma comm_semiring_ow: "class.comm_semiring = comm_semiring_ow UNIV"
  unfolding 
    class.comm_semiring_def comm_semiring_ow_def
    class.comm_semiring_axioms_def comm_semiring_ow_axioms_def
    ab_semigroup_add_ow ab_semigroup_mult_ow
  by simp


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma comm_semiring_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> (A ===> A ===> A) ===> (=)) 
      (comm_semiring_ow (Collect (Domainp A))) class.comm_semiring"
    (is "?PR (comm_semiring_ow (Collect (Domainp A))) class.comm_semiring")
  unfolding 
    comm_semiring_ow_def class.comm_semiring_def
    comm_semiring_ow_axioms_def class.comm_semiring_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  by simp

end



subsection\<open>Semirings with zero\<close>


subsubsection\<open>Definitions and further results\<close>

locale mult_zero_ow = times_ow U times + zero_ow U zero
  for U :: "'ag set" and times zero +
  assumes mult_zero_left[simp]: "a \<in> U \<Longrightarrow> 0\<^sub>o\<^sub>w *\<^sub>o\<^sub>w a = 0\<^sub>o\<^sub>w"
  assumes mult_zero_right[simp]: "a \<in> U \<Longrightarrow> a *\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w = 0\<^sub>o\<^sub>w"

lemma mult_zero_ow: "class.mult_zero = mult_zero_ow UNIV"
  unfolding 
    class.mult_zero_def mult_zero_ow_def mult_zero_ow_axioms_def
    times_ow_def zero_ow_def neutral_ow_def
  by simp

locale semiring_0_ow = 
  semiring_ow U plus times + 
  comm_monoid_add_ow U plus zero + 
  mult_zero_ow U times zero
  for U :: "'ag set" and plus zero times 

lemma semiring_0_ow: "class.semiring_0 = semiring_0_ow UNIV"
  unfolding 
    class.semiring_0_def semiring_0_ow_def  
    mult_zero_ow comm_monoid_add_ow semiring_ow
  by (auto simp: conj_commute)


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma semiring_0_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> A ===> (A ===> A ===> A) ===> (=)) 
      (semiring_0_ow (Collect (Domainp A))) class.semiring_0"
    (is "?PR (semiring_0_ow (Collect (Domainp A))) class.semiring_0")
proof-
  let ?semiring_0 =
    "(
      \<lambda>plus zero times. 
        class.semiring_0 plus zero times \<and>
        (\<forall>a b. a \<in> UNIV \<longrightarrow> b \<in> UNIV \<longrightarrow> times a b \<in> UNIV) \<and> zero \<in> UNIV
    )" 
  have "?PR (semiring_0_ow (Collect (Domainp A))) ?semiring_0" 
    unfolding
      semiring_0_ow_def  class.semiring_0_def
      mult_zero_ow_def class.mult_zero_def
      mult_zero_ow_axioms_def
      times_ow_def zero_ow_def neutral_ow_def 
    apply transfer_prover_start
    apply transfer_step+
    by blast
  thus ?thesis by simp
qed

end



subsection\<open>Commutative semirings with zero\<close>


subsubsection\<open>Definitions and common properties\<close>

locale comm_semiring_0_ow = 
  comm_semiring_ow U plus times +  
  comm_monoid_add_ow U plus zero + 
  mult_zero_ow U times zero
  for U :: "'ag set" and plus zero times 
begin

sublocale semiring_0_ow by unfold_locales

end

lemma comm_semiring_0_ow: "class.comm_semiring_0 = comm_semiring_0_ow UNIV"
  unfolding 
    class.comm_semiring_0_def comm_semiring_0_ow_def
    comm_monoid_add_ow comm_semiring_ow mult_zero_ow
  by (auto simp: conj_commute)


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma comm_semiring_0_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> A ===> (A ===> A ===> A) ===> (=)) 
      (comm_semiring_0_ow (Collect (Domainp A))) class.comm_semiring_0"
    (is "?PR (comm_semiring_0_ow (Collect (Domainp A))) class.comm_semiring_0")
proof-
  let ?comm_semiring_0 =
    "(
      \<lambda>plus zero times. 
        class.comm_semiring_0 plus zero times \<and>
        (\<forall>a b. a \<in> UNIV \<longrightarrow> b \<in> UNIV \<longrightarrow> times a b \<in> UNIV) \<and> zero \<in> UNIV
    )" 
  have "?PR (comm_semiring_0_ow (Collect (Domainp A))) ?comm_semiring_0" 
    unfolding
      comm_semiring_0_ow_def class.comm_semiring_0_def
      mult_zero_ow_def class.mult_zero_def
      mult_zero_ow_axioms_def
      times_ow_def zero_ow_def neutral_ow_def 
    apply transfer_prover_start
    apply transfer_step+
    by blast
  thus ?thesis by simp
qed

end



subsection\<open>Cancellative semirings with zero\<close>


subsubsection\<open>Definitions and common properties\<close>

locale semiring_0_cancel_ow =
  semiring_ow U plus times + cancel_comm_monoid_add_ow U plus minus zero
  for U :: "'ag set" and plus minus zero times
begin

sublocale semiring_0_ow 
proof
  fix a
  show "a \<in> U \<Longrightarrow> 0\<^sub>o\<^sub>w *\<^sub>o\<^sub>w a = 0\<^sub>o\<^sub>w"
  proof-
    assume "a \<in> U"
    have "0\<^sub>o\<^sub>w *\<^sub>o\<^sub>w a \<in> U" by (simp add: \<open>a \<in> U\<close> times_closed') 
    have "0\<^sub>o\<^sub>w *\<^sub>o\<^sub>w a +\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w *\<^sub>o\<^sub>w a = 0\<^sub>o\<^sub>w *\<^sub>o\<^sub>w a +\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w" 
      by (simp add: \<open>a \<in> U\<close> \<open>0\<^sub>o\<^sub>w *\<^sub>o\<^sub>w a \<in> U\<close> distrib_right[symmetric])
    then show ?thesis 
      unfolding add_left_cancel[OF \<open>0\<^sub>o\<^sub>w *\<^sub>o\<^sub>w a \<in> U\<close> \<open>0\<^sub>o\<^sub>w *\<^sub>o\<^sub>w a \<in> U\<close> zero_closed]
      by assumption
  qed
  show "a \<in> U \<Longrightarrow> a *\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w = 0\<^sub>o\<^sub>w"
  proof-
    assume "a \<in> U"
    have "a *\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w \<in> U" by (simp add: \<open>a \<in> U\<close> times_closed')
    have "a *\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w +\<^sub>o\<^sub>w a *\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w = a *\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w +\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w"
      by (simp add: \<open>a \<in> U\<close> \<open>a *\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w \<in> U\<close> distrib_left[symmetric])
    then show ?thesis
      unfolding add_left_cancel[OF \<open>a *\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w \<in> U\<close> \<open>a *\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w \<in> U\<close> zero_closed]
      by assumption
  qed
qed

end

lemma semiring_0_cancel_ow: 
  "class.semiring_0_cancel = semiring_0_cancel_ow UNIV"
  unfolding 
    class.semiring_0_cancel_def 
    semiring_0_cancel_ow_def
    cancel_comm_monoid_add_ow semiring_ow
  by (simp add: conj_commute)


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma semiring_0_cancel_transfer[transfer_rule]: 
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> A) ===> 
      A ===> 
      (A ===> A ===> A) ===> 
      (=)
    ) (semiring_0_cancel_ow (Collect (Domainp A))) class.semiring_0_cancel"
  unfolding semiring_0_cancel_ow_def class.semiring_0_cancel_def
  apply transfer_prover_start
  apply transfer_step+
  by auto

end



subsection\<open>Commutative cancellative semirings with zero\<close>


subsubsection\<open>Definitions and common properties\<close>

locale comm_semiring_0_cancel_ow = 
  comm_semiring_ow U plus times + 
  cancel_comm_monoid_add_ow U plus minus zero
  for U :: "'ag set" and plus  minus zero times 
begin

sublocale semiring_0_cancel_ow by unfold_locales

sublocale comm_semiring_0_ow by unfold_locales

end

lemma comm_semiring_0_cancel_ow: 
  "class.comm_semiring_0_cancel = comm_semiring_0_cancel_ow UNIV"
  unfolding 
    class.comm_semiring_0_cancel_def comm_semiring_0_cancel_ow_def
    cancel_comm_monoid_add_ow comm_semiring_ow
  by (simp add: conj_commute)


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma comm_semiring_0_cancel_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> A) ===> 
      A ===> 
      (A ===> A ===> A) ===> 
      (=)
    ) 
    (comm_semiring_0_cancel_ow (Collect (Domainp A))) 
    class.comm_semiring_0_cancel"
  unfolding comm_semiring_0_cancel_ow_def class.comm_semiring_0_cancel_def
  apply transfer_prover_start
  apply transfer_step+
  by auto

end



subsection\<open>Class \<^class>\<open>zero_neq_one\<close>\<close>


subsubsection\<open>Definitions and common properties\<close>

locale zero_neq_one_ow = 
  zero_ow U zero + one_ow U one
  for U :: "'ag set" and one (\<open>1\<^sub>o\<^sub>w\<close>) and zero (\<open>0\<^sub>o\<^sub>w\<close>)  +
  assumes zero_neq_one[simp]: "0\<^sub>o\<^sub>w \<noteq> 1\<^sub>o\<^sub>w"

lemma zero_neq_one_ow: "class.zero_neq_one = zero_neq_one_ow UNIV"
  unfolding 
    class.zero_neq_one_def zero_neq_one_ow_def
    zero_neq_one_ow_axioms_def
    one_ow_def zero_ow_def neutral_ow_def
  by simp

ud \<open>zero_neq_one.of_bool\<close> (\<open>(with _ _ : \<guillemotleft>of'_bool\<guillemotright> _)\<close> [1000, 999, 1000] 10)
ud of_bool' \<open>of_bool\<close>

ctr parametricity
  in of_bool.with_def

context zero_neq_one_ow
begin

abbreviation of_bool where "of_bool \<equiv> of_bool.with 1\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w"

end


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma zero_neq_one_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"  
  shows 
    "(A ===> A ===> (=)) 
      (zero_neq_one_ow (Collect (Domainp A))) class.zero_neq_one" 
    (is "?PR (zero_neq_one_ow (Collect (Domainp A))) class.zero_neq_one")
proof-
  let ?zero_neq_one = 
    "(\<lambda>one zero. class.zero_neq_one one zero \<and> one \<in> UNIV \<and> zero \<in> UNIV)"
  have "?PR (zero_neq_one_ow (Collect (Domainp A))) ?zero_neq_one"
    unfolding 
      zero_neq_one_ow_def class.zero_neq_one_def
      zero_neq_one_ow_axioms_def
      zero_ow_def one_ow_def neutral_ow_def
    apply transfer_prover_start
    apply transfer_step+
    by auto
  thus ?thesis by simp
qed

end


subsubsection\<open>Relativization\<close>

context zero_neq_one_ow
begin

tts_context
  tts: (?'a to U) 
  rewriting ctr_simps
  substituting zero_neq_one_ow_axioms
  eliminating through simp
begin

tts_lemma split_of_bool_asm:
  shows "P (of_bool p) = (\<not> (p \<and> \<not> P 1\<^sub>o\<^sub>w \<or> \<not> p \<and> \<not> P 0\<^sub>o\<^sub>w))"
    is zero_neq_one_class.split_of_bool_asm.
    
tts_lemma of_bool_eq_iff:
  shows "(of_bool p = local.of_bool q) = (p = q)"
    is zero_neq_one_class.of_bool_eq_iff.
    
tts_lemma split_of_bool:
  shows "P (of_bool p) = ((p \<longrightarrow> P 1\<^sub>o\<^sub>w) \<and> (\<not> p \<longrightarrow> P 0\<^sub>o\<^sub>w))"
    is zero_neq_one_class.split_of_bool.

tts_lemma one_neq_zero: "1\<^sub>o\<^sub>w \<noteq> 0\<^sub>o\<^sub>w"
  is zero_neq_one_class.one_neq_zero.
    
tts_lemma of_bool_eq:
  shows "of_bool False = 0\<^sub>o\<^sub>w" 
    is zero_neq_one_class.of_bool_eq(1)
    and "of_bool True = 1\<^sub>o\<^sub>w"
    is zero_neq_one_class.of_bool_eq(2).

end

end



subsection\<open>Semirings with zero and one (rigs)\<close>


subsubsection\<open>Definitions and commmon properties\<close>

locale semiring_1_ow =
  zero_neq_one_ow U one zero +
  semiring_0_ow U plus zero times + 
  monoid_mult_ow U one times
  for U :: "'ag set" and one times plus zero

lemma semiring_1_ow: "class.semiring_1 = semiring_1_ow UNIV"
  unfolding 
    class.semiring_1_def semiring_1_ow_def
    monoid_mult_ow semiring_0_ow zero_neq_one_ow
  by (auto simp: conj_commute)

ud \<open>semiring_1.of_nat\<close> (\<open>(with _ _ _ : \<guillemotleft>of'_nat\<guillemotright> _)\<close> [1000, 999, 998, 1000] 10)
ud of_nat' \<open>of_nat\<close>

ud \<open>semiring_1.Nats\<close> (\<open>(with _ _ _ : \<nat>)\<close> [1000, 999, 998] 10)
ud Nats' \<open>Nats\<close>

ctr parametricity
  in of_nat_ow: of_nat.with_def
    and Nats_ow: Nats.with_def

context semiring_1_ow
begin

abbreviation of_nat where "of_nat \<equiv> of_nat.with 1\<^sub>o\<^sub>w (+\<^sub>o\<^sub>w) 0\<^sub>o\<^sub>w"
abbreviation Nats (\<open>\<guillemotleft>\<nat>\<guillemotright>\<close>) where "\<guillemotleft>\<nat>\<guillemotright> \<equiv> Nats.with 1\<^sub>o\<^sub>w (+\<^sub>o\<^sub>w) 0\<^sub>o\<^sub>w"
notation Nats (\<open>\<guillemotleft>\<nat>\<guillemotright>\<close>)

end

context semiring_1
begin

lemma Nat_ss_UNIV: "\<nat> \<subseteq> UNIV" by simp

end


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma semiring_1_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(A ===> (A ===> A ===> A) ===> (A ===> A ===> A) ===> A ===> (=)) 
      (semiring_1_ow (Collect (Domainp A))) class.semiring_1"
  unfolding semiring_1_ow_def class.semiring_1_def
  apply transfer_prover_start
  apply transfer_step+
  by auto

end


subsubsection\<open>Relativization\<close>

context semiring_1_ow
begin

tts_context
  tts: (?'a to U) 
  rewriting ctr_simps
  substituting semiring_1_ow_axioms and zero.not_empty 
  eliminating through simp
begin

tts_lemma Nat_ss_UNIV[simp]:
  shows "\<guillemotleft>\<nat>\<guillemotright> \<subseteq> U"
    is Nat_ss_UNIV.

end

lemma Nat_closed[simp, intro]: "a \<in> \<guillemotleft>\<nat>\<guillemotright> \<Longrightarrow> a \<in> U" using Nat_ss_UNIV by blast

tts_context
  tts: (?'a to U) 
  rewriting ctr_simps
  substituting semiring_1_ow_axioms and zero.not_empty
  eliminating through auto
begin

tts_lemma mult_of_nat_commute:
  assumes "y \<in> U"
  shows "of_nat x *\<^sub>o\<^sub>w y = y *\<^sub>o\<^sub>w of_nat x"
    is semiring_1_class.mult_of_nat_commute.

tts_lemma of_bool_conj: "of_bool (P \<and> Q) = of_bool P *\<^sub>o\<^sub>w of_bool Q"
  is semiring_1_class.of_bool_conj.

tts_lemma power_0_left: "0\<^sub>o\<^sub>w ^\<^sub>o\<^sub>w n = (if n = 0 then 1\<^sub>o\<^sub>w else 0\<^sub>o\<^sub>w)"
  is semiring_1_class.power_0_left.

tts_lemma of_nat_power: "of_nat ((with 1 (*) : m ^\<^sub>o\<^sub>w n)) = of_nat m ^\<^sub>o\<^sub>w n"
  is semiring_1_class.of_nat_power.

tts_lemma of_nat_of_bool: "of_nat (with 1 0 : \<guillemotleft>of_bool\<guillemotright> P) = of_bool P"
  is semiring_1_class.of_nat_of_bool.

tts_lemma of_nat_in_Nats: "of_nat n \<in> \<guillemotleft>\<nat>\<guillemotright>"
  is semiring_1_class.of_nat_in_Nats.

tts_lemma zero_power2: "0\<^sub>o\<^sub>w ^\<^sub>o\<^sub>w 2 = 0\<^sub>o\<^sub>w"
  is semiring_1_class.zero_power2.

tts_lemma power_0_Suc: "0\<^sub>o\<^sub>w ^\<^sub>o\<^sub>w Suc n = 0\<^sub>o\<^sub>w"
  is semiring_1_class.power_0_Suc.

tts_lemma zero_power:
  assumes "0 < n"
  shows "0\<^sub>o\<^sub>w ^\<^sub>o\<^sub>w n = 0\<^sub>o\<^sub>w"
    is semiring_1_class.zero_power.

tts_lemma one_power2: "1\<^sub>o\<^sub>w ^\<^sub>o\<^sub>w 2 = 1\<^sub>o\<^sub>w"
  is semiring_1_class.one_power2.

tts_lemma of_nat_simps:
  shows "of_nat 0 = 0\<^sub>o\<^sub>w" 
    is semiring_1_class.of_nat_simps(1)
    and "of_nat (Suc m) = 1\<^sub>o\<^sub>w +\<^sub>o\<^sub>w of_nat m"
    is semiring_1_class.of_nat_simps(2).

tts_lemma of_nat_mult: "of_nat (m * n) = of_nat m *\<^sub>o\<^sub>w of_nat n"
  is semiring_1_class.of_nat_mult.

tts_lemma Nats_induct:
  assumes "x \<in> \<guillemotleft>\<nat>\<guillemotright>" and "\<And>n. P (of_nat n)"
  shows "P x"
    is semiring_1_class.Nats_induct.

tts_lemma of_nat_add: "of_nat (m + n) = of_nat m +\<^sub>o\<^sub>w of_nat n"
  is semiring_1_class.of_nat_add.

tts_lemma of_nat_Suc: "of_nat (Suc m) = 1\<^sub>o\<^sub>w +\<^sub>o\<^sub>w of_nat m"
  is semiring_1_class.of_nat_Suc.

tts_lemma Nats_cases:
  assumes "x \<in> \<guillemotleft>\<nat>\<guillemotright>" 
  obtains (of_nat) n where "x = of_nat n"
    given semiring_1_class.Nats_cases by auto

tts_lemma Nats_mult:
  assumes "a \<in> \<guillemotleft>\<nat>\<guillemotright>" and "b \<in> \<guillemotleft>\<nat>\<guillemotright>"
  shows "a *\<^sub>o\<^sub>w b \<in> \<guillemotleft>\<nat>\<guillemotright>"
    is semiring_1_class.Nats_mult.

tts_lemma of_nat_1: "of_nat 1 = 1\<^sub>o\<^sub>w"
  is semiring_1_class.of_nat_1.

tts_lemma of_nat_0: "of_nat 0 = 0\<^sub>o\<^sub>w"
  is semiring_1_class.of_nat_0.

tts_lemma Nats_add:
  assumes "a \<in> \<guillemotleft>\<nat>\<guillemotright>" and "b \<in> \<guillemotleft>\<nat>\<guillemotright>"
  shows "a +\<^sub>o\<^sub>w b \<in> \<guillemotleft>\<nat>\<guillemotright>"
    is semiring_1_class.Nats_add.

tts_lemma Nats_1: "1\<^sub>o\<^sub>w \<in> \<guillemotleft>\<nat>\<guillemotright>"
  is semiring_1_class.Nats_1.

tts_lemma Nats_0: "0\<^sub>o\<^sub>w \<in> \<guillemotleft>\<nat>\<guillemotright>"
  is semiring_1_class.Nats_0.

end

end



subsection\<open>Commutative rigs\<close>


subsubsection\<open>Definitions and common properties\<close>

locale comm_semiring_1_ow = 
  zero_neq_one_ow U one zero +
  comm_semiring_0_ow U plus zero times +
  comm_monoid_mult_ow U times one
  for U :: "'ag set" and times one plus zero  
begin

sublocale semiring_1_ow by unfold_locales

end

lemma comm_semiring_1_ow: "class.comm_semiring_1 = comm_semiring_1_ow UNIV"
  unfolding 
    class.comm_semiring_1_def comm_semiring_1_ow_def
    comm_monoid_mult_ow comm_semiring_0_ow zero_neq_one_ow
  by (auto simp: conj_commute)


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma comm_semiring_1_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> A ===> (A ===> A ===> A) ===> A ===> (=)) 
      (comm_semiring_1_ow (Collect (Domainp A))) class.comm_semiring_1"
  unfolding comm_semiring_1_ow_def class.comm_semiring_1_def
  apply transfer_prover_start
  apply transfer_step+
  by auto

end


subsubsection\<open>Relativization\<close>

context comm_semiring_1_ow
begin

tts_context
  tts: (?'a to U) 
  rewriting ctr_simps
  substituting comm_semiring_1_ow_axioms and zero.not_empty
  applying [OF times_closed' one_closed plus_closed' zero_closed]
begin

tts_lemma semiring_normalization_rules:
  shows 
    "\<lbrakk>a \<in> U; m \<in> U; b \<in> U\<rbrakk> \<Longrightarrow> a *\<^sub>o\<^sub>w m +\<^sub>o\<^sub>w b *\<^sub>o\<^sub>w m = (a +\<^sub>o\<^sub>w b) *\<^sub>o\<^sub>w m"
    "\<lbrakk>a \<in> U; m \<in> U\<rbrakk> \<Longrightarrow> a *\<^sub>o\<^sub>w m +\<^sub>o\<^sub>w m = (a +\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) *\<^sub>o\<^sub>w m"
    "\<lbrakk>m \<in> U; a \<in> U\<rbrakk> \<Longrightarrow> m +\<^sub>o\<^sub>w a *\<^sub>o\<^sub>w m = (a +\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) *\<^sub>o\<^sub>w m"
    "m \<in> U \<Longrightarrow> m +\<^sub>o\<^sub>w m = (1\<^sub>o\<^sub>w +\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) *\<^sub>o\<^sub>w m"
    "a \<in> U \<Longrightarrow> 0\<^sub>o\<^sub>w +\<^sub>o\<^sub>w a = a"
    "a \<in> U \<Longrightarrow> a +\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w = a"
    "\<lbrakk>a \<in> U; b \<in> U\<rbrakk> \<Longrightarrow> a *\<^sub>o\<^sub>w b = b *\<^sub>o\<^sub>w a"
    "\<lbrakk>a \<in> U; b \<in> U; c \<in> U\<rbrakk> \<Longrightarrow> (a +\<^sub>o\<^sub>w b) *\<^sub>o\<^sub>w c = a *\<^sub>o\<^sub>w c +\<^sub>o\<^sub>w b *\<^sub>o\<^sub>w c"
    "a \<in> U \<Longrightarrow> 0\<^sub>o\<^sub>w *\<^sub>o\<^sub>w a = 0\<^sub>o\<^sub>w"
    "a \<in> U \<Longrightarrow> a *\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w = 0\<^sub>o\<^sub>w"
    "a \<in> U \<Longrightarrow> 1\<^sub>o\<^sub>w *\<^sub>o\<^sub>w a = a"
    "a \<in> U \<Longrightarrow> a *\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w = a"
    "\<lbrakk>lx \<in> U; ly \<in> U; rx \<in> U; ry \<in> U\<rbrakk> \<Longrightarrow> 
      lx *\<^sub>o\<^sub>w ly *\<^sub>o\<^sub>w (rx *\<^sub>o\<^sub>w ry) = lx *\<^sub>o\<^sub>w rx *\<^sub>o\<^sub>w (ly *\<^sub>o\<^sub>w ry)"
    "\<lbrakk>lx \<in> U; ly \<in> U; rx \<in> U; ry \<in> U\<rbrakk> \<Longrightarrow> 
      lx *\<^sub>o\<^sub>w ly *\<^sub>o\<^sub>w (rx *\<^sub>o\<^sub>w ry) = lx *\<^sub>o\<^sub>w (ly *\<^sub>o\<^sub>w (rx *\<^sub>o\<^sub>w ry))"
    "\<lbrakk>lx \<in> U; ly \<in> U; rx \<in> U; ry \<in> U\<rbrakk> \<Longrightarrow> 
      lx *\<^sub>o\<^sub>w ly *\<^sub>o\<^sub>w (rx *\<^sub>o\<^sub>w ry) = rx *\<^sub>o\<^sub>w (lx *\<^sub>o\<^sub>w ly *\<^sub>o\<^sub>w ry)"
    "\<lbrakk>lx \<in> U; ly \<in> U; rx \<in> U\<rbrakk> \<Longrightarrow> lx *\<^sub>o\<^sub>w ly *\<^sub>o\<^sub>w rx = lx *\<^sub>o\<^sub>w rx *\<^sub>o\<^sub>w ly"
    "\<lbrakk>lx \<in> U; ly \<in> U; rx \<in> U\<rbrakk> \<Longrightarrow> lx *\<^sub>o\<^sub>w ly *\<^sub>o\<^sub>w rx = lx *\<^sub>o\<^sub>w (ly *\<^sub>o\<^sub>w rx)"
    "\<lbrakk>lx \<in> U; rx \<in> U; ry \<in> U\<rbrakk> \<Longrightarrow> lx *\<^sub>o\<^sub>w (rx *\<^sub>o\<^sub>w ry) = lx *\<^sub>o\<^sub>w rx *\<^sub>o\<^sub>w ry"
    "\<lbrakk>lx \<in> U; rx \<in> U; ry \<in> U\<rbrakk> \<Longrightarrow> lx *\<^sub>o\<^sub>w (rx *\<^sub>o\<^sub>w ry) = rx *\<^sub>o\<^sub>w (lx *\<^sub>o\<^sub>w ry)"
    "\<lbrakk>a \<in> U; b \<in> U; c \<in> U; d \<in> U\<rbrakk> \<Longrightarrow> 
      a +\<^sub>o\<^sub>w b +\<^sub>o\<^sub>w (c +\<^sub>o\<^sub>w d) = a +\<^sub>o\<^sub>w c +\<^sub>o\<^sub>w (b +\<^sub>o\<^sub>w d)"
    "\<lbrakk>a \<in> U; b \<in> U; c \<in> U\<rbrakk> \<Longrightarrow> a +\<^sub>o\<^sub>w b +\<^sub>o\<^sub>w c = a +\<^sub>o\<^sub>w (b +\<^sub>o\<^sub>w c)"
    "\<lbrakk>a \<in> U; c \<in> U; d \<in> U\<rbrakk> \<Longrightarrow> a +\<^sub>o\<^sub>w (c +\<^sub>o\<^sub>w d) = c +\<^sub>o\<^sub>w (a +\<^sub>o\<^sub>w d)"
    "\<lbrakk>a \<in> U; b \<in> U; c \<in> U\<rbrakk> \<Longrightarrow> a +\<^sub>o\<^sub>w b +\<^sub>o\<^sub>w c = a +\<^sub>o\<^sub>w c +\<^sub>o\<^sub>w b"
    "\<lbrakk>a \<in> U; c \<in> U\<rbrakk> \<Longrightarrow> a +\<^sub>o\<^sub>w c = c +\<^sub>o\<^sub>w a"
    "\<lbrakk>a \<in> U; c \<in> U; d \<in> U\<rbrakk> \<Longrightarrow> a +\<^sub>o\<^sub>w (c +\<^sub>o\<^sub>w d) = a +\<^sub>o\<^sub>w c +\<^sub>o\<^sub>w d"
    "x \<in> U \<Longrightarrow> x ^\<^sub>o\<^sub>w p *\<^sub>o\<^sub>w x ^\<^sub>o\<^sub>w q = x ^\<^sub>o\<^sub>w (p + q)"
    "x \<in> U \<Longrightarrow> x *\<^sub>o\<^sub>w x ^\<^sub>o\<^sub>w q = x ^\<^sub>o\<^sub>w Suc q"
    "x \<in> U \<Longrightarrow> x ^\<^sub>o\<^sub>w q *\<^sub>o\<^sub>w x = x ^\<^sub>o\<^sub>w Suc q"
    "x \<in> U \<Longrightarrow> x *\<^sub>o\<^sub>w x = x ^\<^sub>o\<^sub>w 2"
    "\<lbrakk>x \<in> U; y \<in> U\<rbrakk> \<Longrightarrow> (x *\<^sub>o\<^sub>w y) ^\<^sub>o\<^sub>w q = x ^\<^sub>o\<^sub>w q *\<^sub>o\<^sub>w y ^\<^sub>o\<^sub>w q"
    "x \<in> U \<Longrightarrow> (x ^\<^sub>o\<^sub>w p) ^\<^sub>o\<^sub>w q = x ^\<^sub>o\<^sub>w (p * q)"
    "x \<in> U \<Longrightarrow> x ^\<^sub>o\<^sub>w 0 = 1\<^sub>o\<^sub>w"
    "x \<in> U \<Longrightarrow> x ^\<^sub>o\<^sub>w 1 = x"
    "\<lbrakk>x \<in> U; y \<in> U; z \<in> U\<rbrakk> \<Longrightarrow> x *\<^sub>o\<^sub>w (y +\<^sub>o\<^sub>w z) = x *\<^sub>o\<^sub>w y +\<^sub>o\<^sub>w x *\<^sub>o\<^sub>w z"
    "x \<in> U \<Longrightarrow> x ^\<^sub>o\<^sub>w Suc q = x *\<^sub>o\<^sub>w x ^\<^sub>o\<^sub>w q"
    "x \<in> U \<Longrightarrow> x ^\<^sub>o\<^sub>w (2 * n) = x ^\<^sub>o\<^sub>w n *\<^sub>o\<^sub>w x ^\<^sub>o\<^sub>w n"
    is comm_semiring_1_class.semiring_normalization_rules.

tts_lemma le_imp_power_dvd:
  assumes "a \<in> U" and "m \<le> n"
  shows "a ^\<^sub>o\<^sub>w m \<guillemotleft>dvd\<guillemotright> a ^\<^sub>o\<^sub>w n"
    is comm_semiring_1_class.le_imp_power_dvd.

tts_lemma dvd_0_left_iff:
  assumes "a \<in> U"
  shows "(0\<^sub>o\<^sub>w \<guillemotleft>dvd\<guillemotright> a) = (a = 0\<^sub>o\<^sub>w)"
    is comm_semiring_1_class.dvd_0_left_iff.

tts_lemma dvd_power_same:
  assumes "x \<in> U" and "y \<in> U" and "x \<guillemotleft>dvd\<guillemotright> y"
  shows "x ^\<^sub>o\<^sub>w n \<guillemotleft>dvd\<guillemotright> y ^\<^sub>o\<^sub>w n"
    is comm_semiring_1_class.dvd_power_same.

tts_lemma power_le_dvd:
  assumes "a \<in> U" and "b \<in> U" and "a ^\<^sub>o\<^sub>w n \<guillemotleft>dvd\<guillemotright> b" and "m \<le> n"
  shows "a ^\<^sub>o\<^sub>w m \<guillemotleft>dvd\<guillemotright> b"
    is comm_semiring_1_class.power_le_dvd.

tts_lemma dvd_0_right:
  assumes "a \<in> U"
  shows "a \<guillemotleft>dvd\<guillemotright> 0\<^sub>o\<^sub>w"
    is comm_semiring_1_class.dvd_0_right.

tts_lemma dvd_0_left:
  assumes "a \<in> U" and "0\<^sub>o\<^sub>w \<guillemotleft>dvd\<guillemotright> a"
  shows "a = 0\<^sub>o\<^sub>w"
    is comm_semiring_1_class.dvd_0_left.

tts_lemma dvd_power:
  assumes "x \<in> U" and "0 < n \<or> x = 1\<^sub>o\<^sub>w"
  shows "x \<guillemotleft>dvd\<guillemotright> x ^\<^sub>o\<^sub>w n"
    is comm_semiring_1_class.dvd_power.

tts_lemma dvd_add:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "a \<guillemotleft>dvd\<guillemotright> b" and "a \<guillemotleft>dvd\<guillemotright> c"
  shows "a \<guillemotleft>dvd\<guillemotright> b +\<^sub>o\<^sub>w c"
    is comm_semiring_1_class.dvd_add.

end

end



subsection\<open>Cancellative rigs\<close>


subsubsection\<open>Definitions and common properties\<close>

locale semiring_1_cancel_ow =
  semiring_ow U plus times +
  cancel_comm_monoid_add_ow U plus minus zero +
  zero_neq_one_ow U one zero +
  monoid_mult_ow U one times
  for U :: "'ag set" and plus minus zero one times
begin

sublocale semiring_0_cancel_ow ..
sublocale semiring_1_ow ..

end

lemma semiring_1_cancel_ow: 
  "class.semiring_1_cancel = semiring_1_cancel_ow UNIV"
  unfolding 
    class.semiring_1_cancel_def semiring_1_cancel_ow_def
    cancel_comm_monoid_add_ow monoid_mult_ow semiring_ow zero_neq_one_ow
  by (force simp: conj_commute)


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma semiring_1_cancel_transfer[transfer_rule]:
  includes lifting_syntax
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> A) ===> 
      A ===> 
      A ===> 
      (A ===> A ===> A) ===> 
      (=)
    ) (semiring_1_cancel_ow (Collect (Domainp A))) class.semiring_1_cancel"
  unfolding semiring_1_cancel_ow_def class.semiring_1_cancel_def
  apply transfer_prover_start
  apply transfer_step+
  by blast

end



subsection\<open>Commutative cancellative rigs\<close>


subsubsection\<open>Definitions and common properties\<close>

locale comm_semiring_1_cancel_ow =
  comm_semiring_ow U plus times + 
  cancel_comm_monoid_add_ow U plus minus zero + 
  zero_neq_one_ow U one zero +  
  comm_monoid_mult_ow U times one 
  for U :: "'ag set" and plus minus zero times one + 
  assumes right_diff_distrib'[algebra_simps]: 
    "\<lbrakk> a \<in> U; b \<in> U; c \<in> U \<rbrakk> \<Longrightarrow> a *\<^sub>o\<^sub>w (b -\<^sub>o\<^sub>w c) = a *\<^sub>o\<^sub>w b -\<^sub>o\<^sub>w a *\<^sub>o\<^sub>w c" 
begin

sublocale semiring_1_cancel_ow ..
sublocale comm_semiring_0_cancel_ow ..
sublocale comm_semiring_1_ow ..

end


subsubsection\<open>Transfer rules\<close>

context 
  includes lifting_syntax
begin

lemma comm_semiring_1_cancel_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> A) ===> 
      A ===> 
      (A ===> A ===> A) ===> 
      A ===> 
      (=)
    ) 
    (comm_semiring_1_cancel_ow (Collect (Domainp A))) 
    class.comm_semiring_1_cancel"
  unfolding 
    comm_semiring_1_cancel_ow_def class.comm_semiring_1_cancel_def
    comm_semiring_1_cancel_ow_axioms_def 
    class.comm_semiring_1_cancel_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  by blast

end


subsubsection\<open>Relativization\<close>

context comm_semiring_1_cancel_ow
begin

tts_context
  tts: (?'a to U) 
  rewriting ctr_simps
  substituting comm_semiring_1_cancel_ow_axioms and zero.not_empty
  applying [OF plus_closed' minus_closed' zero_closed times_closed' one_closed]
begin

tts_lemma dvd_add_times_triv_right_iff:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "(a \<guillemotleft>dvd\<guillemotright> b +\<^sub>o\<^sub>w c *\<^sub>o\<^sub>w a) = (a \<guillemotleft>dvd\<guillemotright> b)"
  is comm_semiring_1_cancel_class.dvd_add_times_triv_right_iff.

tts_lemma dvd_add_times_triv_left_iff:
  assumes "a \<in> U" and "c \<in> U" and "b \<in> U"
  shows "(a \<guillemotleft>dvd\<guillemotright> c *\<^sub>o\<^sub>w a +\<^sub>o\<^sub>w b) = (a \<guillemotleft>dvd\<guillemotright> b)"
    is comm_semiring_1_cancel_class.dvd_add_times_triv_left_iff.

tts_lemma dvd_add_triv_right_iff:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a \<guillemotleft>dvd\<guillemotright> b +\<^sub>o\<^sub>w a) = (a \<guillemotleft>dvd\<guillemotright> b)"
    is comm_semiring_1_cancel_class.dvd_add_triv_right_iff.

tts_lemma dvd_add_triv_left_iff:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a \<guillemotleft>dvd\<guillemotright> a +\<^sub>o\<^sub>w b) = (a \<guillemotleft>dvd\<guillemotright> b)"
    is comm_semiring_1_cancel_class.dvd_add_triv_left_iff.

tts_lemma left_diff_distrib':
  assumes "b \<in> U" and "c \<in> U" and "a \<in> U"
  shows "(b -\<^sub>o\<^sub>w c) *\<^sub>o\<^sub>w a = b *\<^sub>o\<^sub>w a -\<^sub>o\<^sub>w c *\<^sub>o\<^sub>w a"
    is comm_semiring_1_cancel_class.left_diff_distrib'.

tts_lemma dvd_add_right_iff:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "a \<guillemotleft>dvd\<guillemotright> b"
  shows "(a \<guillemotleft>dvd\<guillemotright> b +\<^sub>o\<^sub>w c) = (a \<guillemotleft>dvd\<guillemotright> c)"
    is comm_semiring_1_cancel_class.dvd_add_right_iff.

tts_lemma dvd_add_left_iff:
  assumes "a \<in> U" and "c \<in> U" and "b \<in> U" and "a \<guillemotleft>dvd\<guillemotright> c"
  shows "(a \<guillemotleft>dvd\<guillemotright> b +\<^sub>o\<^sub>w c) = (a \<guillemotleft>dvd\<guillemotright> b)"
    is comm_semiring_1_cancel_class.dvd_add_left_iff.

end

end

text\<open>\newpage\<close>

end