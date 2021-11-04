(* Title: Examples/SML_Relativization/Algebra/SML_Rings.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Relativization of the results about rings\<close>
theory SML_Rings
  imports 
    SML_Semirings
    Complex_Main
begin



subsection\<open>Rings\<close>


subsubsection\<open>Definitions and common properties\<close>

locale ring_ow =
  semiring_ow U plus times + ab_group_add_ow U plus zero minus uminus
  for U :: "'ag set" and plus zero minus uminus times
begin

sublocale semiring_0_cancel_ow ..

end

lemma ring_ow: "class.ring = ring_ow UNIV"
  unfolding class.ring_def ring_ow_def ab_group_add_ow semiring_ow
  by (simp add: conj_commute)

lemma ring_ow_UNIV_axioms: "ring_ow (UNIV::'a::ring set) (+) 0 (-) uminus (*)"
  by (fold ring_ow) (rule ring_class.ring_axioms)


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma ring_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      A ===> 
      (A ===> A ===> A) ===> 
      (A ===> A) ===> 
      (A ===> A ===> A) ===> 
      (=)
    ) 
    (ring_ow (Collect (Domainp A))) class.ring"
  unfolding ring_ow_def class.ring_def
  apply transfer_prover_start
  apply transfer_step+
  by blast

end


subsubsection\<open>Relativization\<close>

context ring_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting ring_ow_axioms and zero.not_empty
  applying 
    [
      OF 
        plus_closed' 
        zero_closed 
        minus_closed' 
        add.inverse_closed'' 
        times_closed'
    ] 
begin

tts_lemma right_diff_distrib:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "a *\<^sub>o\<^sub>w (b -\<^sub>o\<^sub>w c) = a *\<^sub>o\<^sub>w b -\<^sub>o\<^sub>w a *\<^sub>o\<^sub>w c"
    is Rings.ring_class.right_diff_distrib.

tts_lemma minus_mult_commute:
  assumes "a \<in> U" and "b \<in> U"
  shows "-\<^sub>o\<^sub>w a *\<^sub>o\<^sub>w b = a *\<^sub>o\<^sub>w -\<^sub>o\<^sub>w b"
    is Rings.ring_class.minus_mult_commute.

tts_lemma left_diff_distrib:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "(a -\<^sub>o\<^sub>w b) *\<^sub>o\<^sub>w c = a *\<^sub>o\<^sub>w c -\<^sub>o\<^sub>w b *\<^sub>o\<^sub>w c"
    is Rings.ring_class.left_diff_distrib.

tts_lemma mult_minus_right:
  assumes "a \<in> U" and "b \<in> U"
  shows "a *\<^sub>o\<^sub>w -\<^sub>o\<^sub>w b = -\<^sub>o\<^sub>w (a *\<^sub>o\<^sub>w b)"
    is Rings.ring_class.mult_minus_right.

tts_lemma minus_mult_right:
  assumes "a \<in> U" and "b \<in> U"
  shows "-\<^sub>o\<^sub>w (a *\<^sub>o\<^sub>w b) = a *\<^sub>o\<^sub>w -\<^sub>o\<^sub>w b"
    is Rings.ring_class.minus_mult_right.

tts_lemma minus_mult_minus:
  assumes "a \<in> U" and "b \<in> U"
  shows "-\<^sub>o\<^sub>w a *\<^sub>o\<^sub>w -\<^sub>o\<^sub>w b = a *\<^sub>o\<^sub>w b"
    is Rings.ring_class.minus_mult_minus.

tts_lemma mult_minus_left:
  assumes "a \<in> U" and "b \<in> U"
  shows "-\<^sub>o\<^sub>w a *\<^sub>o\<^sub>w b = -\<^sub>o\<^sub>w (a *\<^sub>o\<^sub>w b)"
    is Rings.ring_class.mult_minus_left.

tts_lemma minus_mult_left:
  assumes "a \<in> U" and "b \<in> U"
  shows "-\<^sub>o\<^sub>w (a *\<^sub>o\<^sub>w b) = -\<^sub>o\<^sub>w a *\<^sub>o\<^sub>w b"
    is Rings.ring_class.minus_mult_left.

tts_lemma ring_distribs:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows 
    "a *\<^sub>o\<^sub>w (b +\<^sub>o\<^sub>w c) = a *\<^sub>o\<^sub>w b +\<^sub>o\<^sub>w a *\<^sub>o\<^sub>w c"
    "(a +\<^sub>o\<^sub>w b) *\<^sub>o\<^sub>w c = a *\<^sub>o\<^sub>w c +\<^sub>o\<^sub>w b *\<^sub>o\<^sub>w c"
    "(a -\<^sub>o\<^sub>w b) *\<^sub>o\<^sub>w c = a *\<^sub>o\<^sub>w c -\<^sub>o\<^sub>w b *\<^sub>o\<^sub>w c"
    "a *\<^sub>o\<^sub>w (b -\<^sub>o\<^sub>w c) = a *\<^sub>o\<^sub>w b -\<^sub>o\<^sub>w a *\<^sub>o\<^sub>w c"
    is Rings.ring_class.ring_distribs.

tts_lemma eq_add_iff2:
  assumes "a \<in> U" and "e \<in> U" and "c \<in> U" and "b \<in> U" and "d \<in> U"
  shows "(a *\<^sub>o\<^sub>w e +\<^sub>o\<^sub>w c = b *\<^sub>o\<^sub>w e +\<^sub>o\<^sub>w d) = (c = (b -\<^sub>o\<^sub>w a) *\<^sub>o\<^sub>w e +\<^sub>o\<^sub>w d)"
    is Rings.ring_class.eq_add_iff2.

tts_lemma eq_add_iff1:
  assumes "a \<in> U" and "e \<in> U" and "c \<in> U" and "b \<in> U" and "d \<in> U"
  shows "(a *\<^sub>o\<^sub>w e +\<^sub>o\<^sub>w c = b *\<^sub>o\<^sub>w e +\<^sub>o\<^sub>w d) = ((a -\<^sub>o\<^sub>w b) *\<^sub>o\<^sub>w e +\<^sub>o\<^sub>w c = d)"
    is Rings.ring_class.eq_add_iff1.

tts_lemma mult_diff_mult:
  assumes "x \<in> U" and "y \<in> U" and "a \<in> U" and "b \<in> U"
  shows "x *\<^sub>o\<^sub>w y -\<^sub>o\<^sub>w a *\<^sub>o\<^sub>w b = x *\<^sub>o\<^sub>w (y -\<^sub>o\<^sub>w b) +\<^sub>o\<^sub>w (x -\<^sub>o\<^sub>w a) *\<^sub>o\<^sub>w b"
    is Real.mult_diff_mult.

end

end



subsection\<open>Commutative rings\<close>


subsubsection\<open>Definitions and common properties\<close>

locale comm_ring_ow =
  comm_semiring_ow U plus times + ab_group_add_ow U plus zero minus uminus
  for U :: "'ag set" and plus zero minus uminus times
begin

sublocale ring_ow ..
sublocale comm_semiring_0_cancel_ow ..

end

lemma comm_ring_ow: "class.comm_ring = comm_ring_ow UNIV"
  unfolding 
    class.comm_ring_def comm_ring_ow_def 
    ab_group_add_ow comm_semiring_ow
  by (simp add: conj_commute)


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma comm_ring_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      A ===> 
      (A ===> A ===> A) ===> 
      (A ===> A) ===>
      (A ===> A ===> A) ===>
      (=)
    ) 
    (comm_ring_ow (Collect (Domainp A))) class.comm_ring"
  unfolding comm_ring_ow_def class.comm_ring_def
  apply transfer_prover_start
  apply transfer_step+
  by blast

end


subsubsection\<open>Relativization\<close>

context comm_ring_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting comm_ring_ow_axioms and zero.not_empty
  applying 
    [
      OF 
        plus_closed' 
        zero_closed 
        minus_closed' 
        add.inverse_closed'' 
        times_closed'
    ] 
begin

tts_lemma square_diff_square_factored:
  assumes "x \<in> U" and "y \<in> U"
  shows "x *\<^sub>o\<^sub>w x -\<^sub>o\<^sub>w y *\<^sub>o\<^sub>w y = (x +\<^sub>o\<^sub>w y) *\<^sub>o\<^sub>w (x -\<^sub>o\<^sub>w y)"
    is comm_ring_class.square_diff_square_factored.

end

end



subsection\<open>Rings with identity\<close>


subsubsection\<open>Definitions and common properties\<close>

locale ring_1_ow =
  ring_ow U plus zero minus uminus times + 
  zero_neq_one_ow U one zero + 
  monoid_mult_ow U one times 
  for U :: "'ag set" and one times plus zero minus uminus
begin

sublocale semiring_1_cancel_ow ..

end

lemma ring_1_ow: "class.ring_1 = ring_1_ow UNIV"
  unfolding 
    class.ring_1_def ring_1_ow_def monoid_mult_ow ring_ow zero_neq_one_ow
  by (force simp: conj_commute)

lemma ring_1_ow_UNIV_axioms: 
  "ring_1_ow (UNIV::'a::ring_1 set) 1 (*) (+) 0 (-) uminus"
  by (fold ring_1_ow) (rule ring_1_class.ring_1_axioms)

ud \<open>ring_1.iszero\<close> (\<open>(with _ : \<guillemotleft>iszero\<guillemotright> _)\<close> [1000, 1000] 10)
ud iszero' \<open>iszero\<close> 
ud \<open>ring_1.of_int\<close>
  (\<open>(with _ _ _ _ : \<guillemotleft>of'_int\<guillemotright> _)\<close> [1000, 999, 998, 997, 1000] 10)
ud of_int' \<open>of_int\<close>
ud \<open>ring_1.Ints\<close> (\<open>(with _ _ _ _ : \<int>)\<close> [1000, 999, 998, 997] 10)
ud Ints' \<open>Ints\<close>
ud \<open>diffs\<close> (\<open>(with _ _ _ _ : \<guillemotleft>diffs\<guillemotright> _)\<close> [1000, 999, 998, 997, 1000] 10)

ctr parametricity  
  in iszero_ow: iszero.with_def 
    and of_int_ow: of_int.with_def
    and Ints_ow: Ints.with_def
    and diffs_ow: diffs.with_def

context ring_1_ow
begin

abbreviation iszero where "iszero \<equiv> iszero.with 0\<^sub>o\<^sub>w"
abbreviation of_int where "of_int \<equiv> of_int.with 1\<^sub>o\<^sub>w (+\<^sub>o\<^sub>w) 0\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w)"
abbreviation Ints (\<open>\<guillemotleft>\<int>\<guillemotright>\<close>) where "\<guillemotleft>\<int>\<guillemotright> \<equiv> Ints.with 1\<^sub>o\<^sub>w (+\<^sub>o\<^sub>w) 0\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w)"
notation Ints (\<open>\<guillemotleft>\<int>\<guillemotright>\<close>)

end

context ring_1
begin

lemma Int_ss_UNIV: "\<int> \<subseteq> UNIV" by simp 

end


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma ring_1_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      A ===> 
      (A ===> A ===> A) ===>
      (A ===> A ===> A) ===>
      A ===>
      (A ===> A ===> A) ===> 
      (A ===> A) ===>
      (=)
    ) 
      (ring_1_ow (Collect (Domainp A))) class.ring_1"
  unfolding ring_1_ow_def class.ring_1_def
  apply transfer_prover_start
  apply transfer_step+
  by blast

end


subsubsection\<open>Relativization\<close>

declare dvd.with[ud_with del]
declare dvd'.with[ud_with del]

context ring_1_ow
begin

tts_context
  tts: (?'a to U)
  substituting ring_1_ow_axioms and zero.not_empty
  eliminating through simp
begin

tts_lemma Int_ss_UNIV[simp]: "\<guillemotleft>\<int>\<guillemotright> \<subseteq> U"
  is Int_ss_UNIV.

end

lemma Int_closed[simp,intro]: "a \<in> \<guillemotleft>\<int>\<guillemotright> \<Longrightarrow> a \<in> U" using Int_ss_UNIV by blast

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting ring_1_ow_axioms and zero.not_empty
  eliminating through auto
begin

tts_lemma iszero_0: "iszero 0\<^sub>o\<^sub>w"
  is ring_1_class.iszero_0.
    
tts_lemma not_iszero_1: "\<not> iszero 1\<^sub>o\<^sub>w"
  is ring_1_class.not_iszero_1.

tts_lemma Nats_subset_Ints: "\<guillemotleft>\<nat>\<guillemotright> \<subseteq> \<guillemotleft>\<int>\<guillemotright>"
  is Int.ring_1_class.Nats_subset_Ints.

tts_lemma Ints_1: "1\<^sub>o\<^sub>w \<in> \<guillemotleft>\<int>\<guillemotright>"
  is Int.ring_1_class.Ints_1.

tts_lemma Ints_0: "0\<^sub>o\<^sub>w \<in> \<guillemotleft>\<int>\<guillemotright>"
  is Int.ring_1_class.Ints_0.

tts_lemma not_iszero_neg_1: "\<not> iszero (-\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w)"
  is Num.ring_1_class.not_iszero_neg_1.

tts_lemma of_int_1: "of_int 1 = 1\<^sub>o\<^sub>w"
  is Int.ring_1_class.of_int_1.

tts_lemma of_int_0: "of_int 0 = 0\<^sub>o\<^sub>w"
  is Int.ring_1_class.of_int_0.

tts_lemma Ints_of_int: "of_int z \<in> \<guillemotleft>\<int>\<guillemotright>"
  is Int.ring_1_class.Ints_of_int.

tts_lemma Ints_of_nat: "of_nat n \<in> \<guillemotleft>\<int>\<guillemotright>"
  is Int.ring_1_class.Ints_of_nat.

tts_lemma of_int_of_nat_eq:
  shows "local.of_int (with 1 (+) 0 : \<guillemotleft>of_nat\<guillemotright> n) = local.of_nat n"
    is Int.ring_1_class.of_int_of_nat_eq.

tts_lemma of_int_of_bool:
  "of_int (with 1 0 : \<guillemotleft>of_bool\<guillemotright> P) = of_bool P"
  is Int.ring_1_class.of_int_of_bool.

tts_lemma of_int_minus: "of_int (- z) = -\<^sub>o\<^sub>w of_int z"
  is Int.ring_1_class.of_int_minus.

tts_lemma mult_minus1_right:
  assumes "z \<in> U"
  shows "z *\<^sub>o\<^sub>w -\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w = -\<^sub>o\<^sub>w z"
    is Num.ring_1_class.mult_minus1_right.

tts_lemma mult_minus1:
  assumes "z \<in> U"
  shows "-\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w *\<^sub>o\<^sub>w z = -\<^sub>o\<^sub>w z"
    is Num.ring_1_class.mult_minus1.

tts_lemma eq_iff_iszero_diff:
  assumes "x \<in> U" and "y \<in> U"
  shows "(x = y) = iszero (x -\<^sub>o\<^sub>w y)"
    is Num.ring_1_class.eq_iff_iszero_diff.

tts_lemma minus_in_Ints_iff:
  assumes "x \<in> U"
  shows "(-\<^sub>o\<^sub>w x \<in> \<guillemotleft>\<int>\<guillemotright>) = (x \<in> \<guillemotleft>\<int>\<guillemotright>)"
    is Int.ring_1_class.minus_in_Ints_iff.

tts_lemma mult_of_int_commute:
  assumes "y \<in> U"
  shows "of_int x *\<^sub>o\<^sub>w y = y *\<^sub>o\<^sub>w of_int x"
    is Int.ring_1_class.mult_of_int_commute.

tts_lemma of_int_power:
  "of_int ((with 1 (*) : z ^\<^sub>o\<^sub>w n)) = of_int z ^\<^sub>o\<^sub>w n"
    is Int.ring_1_class.of_int_power.

tts_lemma Ints_minus:
  assumes "a \<in> \<guillemotleft>\<int>\<guillemotright>"
  shows "-\<^sub>o\<^sub>w a \<in> \<guillemotleft>\<int>\<guillemotright>"
    is Int.ring_1_class.Ints_minus.

tts_lemma of_int_diff: "of_int (w - z) = of_int w -\<^sub>o\<^sub>w of_int z"
  is Int.ring_1_class.of_int_diff.

tts_lemma of_int_add: "of_int (w + z) = of_int w +\<^sub>o\<^sub>w of_int z"
  is Int.ring_1_class.of_int_add.

tts_lemma of_int_mult: "of_int (w * z) = of_int w *\<^sub>o\<^sub>w of_int z"
  is Int.ring_1_class.of_int_mult.

tts_lemma power_minus1_even: "(-\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) ^\<^sub>o\<^sub>w (2 * n) = 1\<^sub>o\<^sub>w"
  is Power.ring_1_class.power_minus1_even.

tts_lemma Ints_power:
  assumes "a \<in> \<guillemotleft>\<int>\<guillemotright>"
  shows "a ^\<^sub>o\<^sub>w n \<in> \<guillemotleft>\<int>\<guillemotright>"
    is Int.ring_1_class.Ints_power.

tts_lemma of_nat_nat:
  assumes "0 \<le> z"
  shows "of_nat (nat z) = of_int z"
    is Int.ring_1_class.of_nat_nat.

tts_lemma power2_minus:
  assumes "a \<in> U"
  shows "(-\<^sub>o\<^sub>w a) ^\<^sub>o\<^sub>w 2 = a ^\<^sub>o\<^sub>w 2"
    is Power.ring_1_class.power2_minus.

tts_lemma power_minus1_odd:
  shows "(-\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) ^\<^sub>o\<^sub>w Suc (2 * n) = -\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w"
    is Power.ring_1_class.power_minus1_odd.

tts_lemma power_minus:
  assumes "a \<in> U"
  shows "(-\<^sub>o\<^sub>w a) ^\<^sub>o\<^sub>w n = (-\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) ^\<^sub>o\<^sub>w n *\<^sub>o\<^sub>w a ^\<^sub>o\<^sub>w n"
    is Power.ring_1_class.power_minus.

tts_lemma square_diff_one_factored:
  assumes "x \<in> U"
  shows "x *\<^sub>o\<^sub>w x -\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w = (x +\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) *\<^sub>o\<^sub>w (x -\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w)"
    is Rings.ring_1_class.square_diff_one_factored.

tts_lemma neg_one_even_power:
  assumes "even n"
  shows "(-\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) ^\<^sub>o\<^sub>w n = 1\<^sub>o\<^sub>w"
    is Parity.ring_1_class.neg_one_even_power.

tts_lemma minus_one_power_iff:
  "(-\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) ^\<^sub>o\<^sub>w n = (if even n then 1\<^sub>o\<^sub>w else -\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w)"
    is Parity.ring_1_class.minus_one_power_iff.

tts_lemma Nats_altdef1: "\<guillemotleft>\<nat>\<guillemotright> = {x \<in> U. \<exists>y\<ge>0. x = of_int y}"
    is Int.ring_1_class.Nats_altdef1.

tts_lemma Ints_induct:
  assumes "q \<in> \<guillemotleft>\<int>\<guillemotright>" and "\<And>z. P (of_int z)"
  shows "P q"
    is Int.ring_1_class.Ints_induct.

tts_lemma of_int_of_nat:
  shows 
    "of_int k = (if k < 0 then -\<^sub>o\<^sub>w of_nat (nat (- k)) else of_nat (nat k))"
    is Int.ring_1_class.of_int_of_nat.

tts_lemma Ints_diff:
  assumes "a \<in> \<guillemotleft>\<int>\<guillemotright>" and "b \<in> \<guillemotleft>\<int>\<guillemotright>"
  shows "a -\<^sub>o\<^sub>w b \<in> \<guillemotleft>\<int>\<guillemotright>"
    is Int.ring_1_class.Ints_diff.

tts_lemma Ints_add:
  assumes "a \<in> \<guillemotleft>\<int>\<guillemotright>" and "b \<in> \<guillemotleft>\<int>\<guillemotright>"
  shows "a +\<^sub>o\<^sub>w b \<in> \<guillemotleft>\<int>\<guillemotright>"
    is Int.ring_1_class.Ints_add.

tts_lemma Ints_mult:
  assumes "a \<in> \<guillemotleft>\<int>\<guillemotright>" and "b \<in> \<guillemotleft>\<int>\<guillemotright>"
  shows "a *\<^sub>o\<^sub>w b \<in> \<guillemotleft>\<int>\<guillemotright>"
    is Int.ring_1_class.Ints_mult.

tts_lemma power_minus_even':
  assumes "a \<in> U" and "even n"
  shows "(-\<^sub>o\<^sub>w a) ^\<^sub>o\<^sub>w n = a ^\<^sub>o\<^sub>w n"
    is Parity.ring_1_class.power_minus_even.

tts_lemma power_minus_even:
  assumes "a \<in> U"
  shows "(-\<^sub>o\<^sub>w a) ^\<^sub>o\<^sub>w (2 * n) = a ^\<^sub>o\<^sub>w (2 * n)"
    is Power.ring_1_class.power_minus_even.

tts_lemma power_minus_odd:
  assumes "a \<in> U" and "odd n"
  shows "(-\<^sub>o\<^sub>w a) ^\<^sub>o\<^sub>w n = -\<^sub>o\<^sub>w (a ^\<^sub>o\<^sub>w n)"
    is Parity.ring_1_class.power_minus_odd.

tts_lemma uminus_power_if:
  assumes "a \<in> U"
  shows "(-\<^sub>o\<^sub>w a) ^\<^sub>o\<^sub>w n = (if even n then a ^\<^sub>o\<^sub>w n else -\<^sub>o\<^sub>w (a ^\<^sub>o\<^sub>w n))"
    is Parity.ring_1_class.uminus_power_if.

tts_lemma neg_one_power_add_eq_neg_one_power_diff:
  assumes "k \<le> n"
  shows "(-\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) ^\<^sub>o\<^sub>w (n + k) = (-\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) ^\<^sub>o\<^sub>w (n - k)"
    is Parity.ring_1_class.neg_one_power_add_eq_neg_one_power_diff.

tts_lemma neg_one_odd_power:
  assumes "odd n"
  shows "(-\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) ^\<^sub>o\<^sub>w n = -\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w"
    is Parity.ring_1_class.neg_one_odd_power.

tts_lemma Ints_cases:
  assumes "q \<in> \<guillemotleft>\<int>\<guillemotright>" and "\<And>z. q = of_int z \<Longrightarrow> thesis"
  shows thesis
    is Int.ring_1_class.Ints_cases.

end

end

lemmas [ud_with] = dvd.with dvd'.with



subsection\<open>Commutative rings with identity\<close>


subsubsection\<open>Definitions and common properties\<close>

locale comm_ring_1_ow =
  comm_ring_ow U plus zero minus uminus times + 
  zero_neq_one_ow U one zero + 
  comm_monoid_mult_ow U times one 
  for U :: "'ag set" and times one plus zero minus uminus
begin

sublocale ring_1_ow ..
sublocale comm_semiring_1_cancel_ow 
  by unfold_locales (blast intro: right_diff_distrib)

end

lemma comm_ring_1_ow: "class.comm_ring_1 = comm_ring_1_ow UNIV"
  unfolding 
    class.comm_ring_1_def comm_ring_1_ow_def
    comm_monoid_mult_ow comm_ring_ow zero_neq_one_ow
  by (force simp: conj_commute)

lemma comm_ring_1_ow_UNIV_axioms:
  "comm_ring_1_ow (UNIV::'a::comm_ring_1 set) (*) 1 (+) 0 (-) uminus"
  by (fold comm_ring_1_ow) (rule comm_ring_1_class.comm_ring_1_axioms)


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma comm_ring_1_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===>
      A ===> 
      (A ===> A ===> A) ===>
      A ===>
      (A ===> A ===> A) ===> 
      (A ===> A) ===>
      (=)
    ) (comm_ring_1_ow (Collect (Domainp A))) class.comm_ring_1"
  unfolding comm_ring_1_ow_def class.comm_ring_1_def
  apply transfer_prover_start
  apply transfer_step+
  by blast

end


subsubsection\<open>Relativization\<close>

context comm_ring_1_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting comm_ring_1_ow_axioms and zero.not_empty
  applying 
    [
      OF 
        times_closed' 
        one_closed 
        plus_closed'
        zero_closed 
        minus_closed'
        add.inverse_closed''
    ]
begin

tts_lemma ring_normalization_rules:
  assumes "x \<in> U"
  shows "-\<^sub>o\<^sub>w x = -\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w *\<^sub>o\<^sub>w x" "y \<in> U \<Longrightarrow> x -\<^sub>o\<^sub>w y = x +\<^sub>o\<^sub>w -\<^sub>o\<^sub>w y"
    is comm_ring_1_class.ring_normalization_rules.
    
tts_lemma left_minus_one_mult_self:
  assumes "a \<in> U"
  shows "(-\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) ^\<^sub>o\<^sub>w n *\<^sub>o\<^sub>w ((-\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) ^\<^sub>o\<^sub>w n *\<^sub>o\<^sub>w a) = a"
    is Power.comm_ring_1_class.left_minus_one_mult_self.

tts_lemma minus_power_mult_self:
  assumes "a \<in> U"
  shows "(-\<^sub>o\<^sub>w a) ^\<^sub>o\<^sub>w n *\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w a) ^\<^sub>o\<^sub>w n = a ^\<^sub>o\<^sub>w (2 * n)"
    is Power.comm_ring_1_class.minus_power_mult_self.

tts_lemma minus_one_mult_self: "(-\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) ^\<^sub>o\<^sub>w n *\<^sub>o\<^sub>w (-\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) ^\<^sub>o\<^sub>w n = 1\<^sub>o\<^sub>w"
  is comm_ring_1_class.minus_one_mult_self.

tts_lemma power2_commute:
  assumes "x \<in> U" and "y \<in> U"
  shows "(x -\<^sub>o\<^sub>w y) ^\<^sub>o\<^sub>w 2 = (y -\<^sub>o\<^sub>w x) ^\<^sub>o\<^sub>w 2"
    is comm_ring_1_class.power2_commute.

tts_lemma minus_dvd_iff:
  assumes "x \<in> U" and "y \<in> U"
  shows "(-\<^sub>o\<^sub>w x \<guillemotleft>dvd\<guillemotright> y) = (x \<guillemotleft>dvd\<guillemotright> y)"
    is comm_ring_1_class.minus_dvd_iff.

tts_lemma dvd_minus_iff:
  assumes "x \<in> U" and "y \<in> U"
  shows "(x \<guillemotleft>dvd\<guillemotright> -\<^sub>o\<^sub>w y) = (x \<guillemotleft>dvd\<guillemotright> y)"
    is comm_ring_1_class.dvd_minus_iff.

tts_lemma dvd_diff:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U" and "x \<guillemotleft>dvd\<guillemotright> y" and "x \<guillemotleft>dvd\<guillemotright> z"
  shows "x \<guillemotleft>dvd\<guillemotright> y -\<^sub>o\<^sub>w z"
    is comm_ring_1_class.dvd_diff.

end

end

text\<open>\newpage\<close>

end