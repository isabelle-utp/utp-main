(* Title: Examples/SML_Relativization/Algebra/SML_Monoids.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Relativization of the results about monoids\<close>
theory SML_Monoids
  imports 
    SML_Semigroups
    "../Foundations/Product_Type_Ext"
    "../Foundations/Transfer_Ext"
begin



subsection\<open>Simple monoids\<close>


subsubsection\<open>Definitions and common properties\<close>

locale neutral_ow =
  fixes U :: "'ag set" and z :: "'ag" (\<open>\<^bold>1\<^sub>o\<^sub>w\<close>)
  assumes z_closed[simp]: "\<^bold>1\<^sub>o\<^sub>w \<in> U" 
begin

notation z (\<open>\<^bold>1\<^sub>o\<^sub>w\<close>)

tts_register_sbts \<open>\<^bold>1\<^sub>o\<^sub>w\<close> | U by (meson Domainp.cases z_closed)

lemma not_empty[simp]: "U \<noteq> {}" using z_closed by blast

lemma neutral_map: "(\<lambda>y. \<^bold>1\<^sub>o\<^sub>w) ` A \<subseteq> U" using z_closed by auto

end

locale monoid_ow = semigroup_ow U f + neutral_ow U z
  for U :: "'ag set" and f z +
  assumes left_neutral_mow[simp]: "a \<in> U \<Longrightarrow> (\<^bold>1\<^sub>o\<^sub>w \<^bold>*\<^sub>o\<^sub>w a) = a"
    and right_neutral_mow[simp]: "a \<in> U \<Longrightarrow> (a \<^bold>*\<^sub>o\<^sub>w \<^bold>1\<^sub>o\<^sub>w) = a"

locale zero_ow = zero: neutral_ow U zero
  for U :: "'ag set" and zero :: "'ag" (\<open>0\<^sub>o\<^sub>w\<close>)
begin

notation zero (\<open>0\<^sub>o\<^sub>w\<close>)

lemma zero_closed: "0\<^sub>o\<^sub>w \<in> U" by (rule zero.z_closed)

end

lemma monoid_ow: "monoid = monoid_ow UNIV"
  unfolding 
    monoid_def monoid_ow_def monoid_axioms_def monoid_ow_axioms_def
    neutral_ow_def
    semigroup_ow
  by simp

locale one_ow = one: neutral_ow U one
  for U :: "'ag set" and one :: "'ag" (\<open>1\<^sub>o\<^sub>w\<close>)
begin

notation one (\<open>1\<^sub>o\<^sub>w\<close>)

lemma one_closed: "1\<^sub>o\<^sub>w \<in> U" by (rule one.z_closed)

end

locale power_ow = one_ow U one + times_ow U times
  for U :: "'ag set" and one :: "'ag" (\<open>1\<^sub>o\<^sub>w\<close>) and times (infixl \<open>*\<^sub>o\<^sub>w\<close> 70)

primrec power_with :: "['a, ['a, 'a] \<Rightarrow> 'a, 'a, nat] \<Rightarrow> 'a"
  (\<open>'(/with _ _ : _ ^\<^sub>o\<^sub>w _/')\<close> [1000, 999, 1000, 1000] 10)
  where
    power_0: "power_with one times a 0 = one" for one times
  | power_Suc: "power_with one times a (Suc n) = 
      times a (power_with one times a n)" for one times

lemma power_with[ud_with]: "power = power_with 1 (*)"
  apply(intro ext)
  subgoal for x n by (induction n) auto
  done

context power_ow
begin

abbreviation power (\<open>(_ ^\<^sub>o\<^sub>w _)\<close> [81, 80] 80) where 
  "power \<equiv> power_with 1\<^sub>o\<^sub>w (*\<^sub>o\<^sub>w)"

end

locale monoid_add_ow =
  semigroup_add_ow U plus + zero_ow U zero for U :: "'ag set" and plus zero +
  assumes add_0_left: "a \<in> U \<Longrightarrow> (0\<^sub>o\<^sub>w +\<^sub>o\<^sub>w a) = a"
  assumes add_0_right: "a \<in> U \<Longrightarrow> (a +\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w) = a"
begin

sublocale add: monoid_ow U \<open>(+\<^sub>o\<^sub>w)\<close> \<open>0\<^sub>o\<^sub>w\<close> 
  by unfold_locales (simp add: add_0_left add_0_right)+

end

lemma monoid_add_ow: "class.monoid_add = monoid_add_ow UNIV"
  unfolding 
    class.monoid_add_def monoid_add_ow_def
    class.monoid_add_axioms_def monoid_add_ow_axioms_def
    zero_ow_def neutral_ow_def
    semigroup_add_ow
  by simp

locale monoid_mult_ow = semigroup_mult_ow U times + one_ow U one 
  for U :: "'ag set" and one times  +
  assumes mult_1_left: "a \<in> U \<Longrightarrow> (1\<^sub>o\<^sub>w *\<^sub>o\<^sub>w a) = a"
  assumes mult_1_right: "a \<in> U \<Longrightarrow> (a *\<^sub>o\<^sub>w 1\<^sub>o\<^sub>w) = a"
begin

sublocale mult: monoid_ow U \<open>(*\<^sub>o\<^sub>w)\<close> \<open>1\<^sub>o\<^sub>w\<close> 
  by unfold_locales (simp add: mult_1_left mult_1_right)+

sublocale power_ow ..

end

lemma monoid_mult_ow: "class.monoid_mult = monoid_mult_ow UNIV"
  unfolding 
    class.monoid_mult_def monoid_mult_ow_def
    class.monoid_mult_axioms_def monoid_mult_ow_axioms_def
    one_ow_def neutral_ow_def
    semigroup_mult_ow
  by simp


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma monoid_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> A ===> (=)) 
      (monoid_ow (Collect (Domainp A))) monoid"
proof-
  let ?P = "((A ===> A ===> A) ===> A ===> (=))"
  let ?monoid_ow = "monoid_ow (Collect (Domainp A))"
  have "?P ?monoid_ow (\<lambda>f z. z \<in> UNIV \<and> monoid f z)"
    unfolding 
      monoid_def monoid_ow_def 
      monoid_axioms_def monoid_ow_axioms_def 
      neutral_ow_def
    apply transfer_prover_start
    apply transfer_step+
    unfolding Ball_def by blast
  thus ?thesis by simp
qed

lemma monoid_add_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> A ===> (=)) 
      (monoid_add_ow (Collect (Domainp A))) class.monoid_add"
proof-
  let ?P = "((A ===> A ===> A) ===> A ===> (=))"
  let ?monoid_add_ow = "monoid_add_ow (Collect (Domainp A))"
  have "?P ?monoid_add_ow (\<lambda>f z. z \<in> UNIV \<and> class.monoid_add f z)"
    unfolding 
      class.monoid_add_def monoid_add_ow_def 
      class.monoid_add_axioms_def monoid_add_ow_axioms_def
      zero_ow_def neutral_ow_def
    apply transfer_prover_start
    apply transfer_step+
    unfolding Ball_def by blast
  thus ?thesis by simp
qed


lemma monoid_mult_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(A ===> (A ===> A ===> A) ===> (=)) 
      (monoid_mult_ow (Collect (Domainp A))) class.monoid_mult"
proof-
  let ?P = "(A ===> (A ===> A ===> A) ===> (=))"
  let ?monoid_mult_ow = "monoid_mult_ow (Collect (Domainp A))"
  have "?P ?monoid_mult_ow (\<lambda>z f. z \<in> UNIV \<and> class.monoid_mult z f)"
    unfolding 
      class.monoid_mult_def monoid_mult_ow_def 
      class.monoid_mult_axioms_def monoid_mult_ow_axioms_def
      one_ow_def neutral_ow_def
    apply transfer_prover_start
    apply transfer_step+
    unfolding Ball_def by blast
  thus ?thesis by simp
qed

lemma power_with_transfer[transfer_rule]:  
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(A ===> (A ===> A ===> A) ===> A ===> (=) ===> A) power_with power_with"
proof(intro rel_funI, elim subst)
  fix i i' m m' a a' n
  assume ii': "A i i'" and mm': "(A ===> A ===> A) m m'" and aa': "A a a'"
  show "A (power_with i m a n) (power_with i' m' a' n)"
    apply(induction n)
    subgoal by (simp add: ii')
    subgoal using mm' aa' by (auto elim: rel_funE)
    done
qed

end


subsubsection\<open>Relativization\<close>

context power_ow
begin

tts_context
  tts: (?'a to U)
  sbterms: (\<open>(*)::[?'a::power,?'a::power] \<Rightarrow> ?'a::power\<close> to \<open>(*\<^sub>o\<^sub>w)\<close>) 
    and (\<open>1::?'a::power\<close> to \<open>1\<^sub>o\<^sub>w\<close>)
  rewriting ctr_simps
  substituting power_ow_axioms and one.not_empty
begin

tts_lemma power_Suc:
  assumes "a \<in> U"
  shows "a ^\<^sub>o\<^sub>w Suc n = a *\<^sub>o\<^sub>w a ^\<^sub>o\<^sub>w n"
    is power_class.power.power_Suc.

tts_lemma power_0:
  assumes "a \<in> U"
  shows "a ^\<^sub>o\<^sub>w 0 = 1\<^sub>o\<^sub>w"
  is power_class.power.power_0.
    
tts_lemma power_eq_if:
  assumes "p \<in> U"
  shows "p ^\<^sub>o\<^sub>w m = (if m = 0 then 1\<^sub>o\<^sub>w else p *\<^sub>o\<^sub>w p ^\<^sub>o\<^sub>w (m - 1))"
    is power_class.power_eq_if.
    
tts_lemma simps:
  assumes "a \<in> U"
  shows "a ^\<^sub>o\<^sub>w 0 = 1\<^sub>o\<^sub>w" 
    is power_class.power.simps(1)
    and "a ^\<^sub>o\<^sub>w Suc n = a *\<^sub>o\<^sub>w a ^\<^sub>o\<^sub>w n" 
    is power_class.power.simps(2).

end

end

context monoid_mult_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting monoid_mult_ow_axioms and one.not_empty
  applying [OF one_closed mult.f_closed']
begin

tts_lemma power_commuting_commutes:
  assumes "x \<in> U" and "y \<in> U" and "x *\<^sub>o\<^sub>w y = y *\<^sub>o\<^sub>w x"
  shows "x ^\<^sub>o\<^sub>w n *\<^sub>o\<^sub>w y = y *\<^sub>o\<^sub>w x ^\<^sub>o\<^sub>w n"
    is monoid_mult_class.power_commuting_commutes.

tts_lemma left_right_inverse_power:
  assumes "x \<in> U" and "y \<in> U" and "x *\<^sub>o\<^sub>w y = 1\<^sub>o\<^sub>w"
  shows "x ^\<^sub>o\<^sub>w n *\<^sub>o\<^sub>w y ^\<^sub>o\<^sub>w n = 1\<^sub>o\<^sub>w"
    is monoid_mult_class.left_right_inverse_power.

tts_lemma power_numeral_even:
  assumes "z \<in> U"
  shows "z ^\<^sub>o\<^sub>w numeral (num.Bit0 w) = (let w = z ^\<^sub>o\<^sub>w numeral w in w *\<^sub>o\<^sub>w w)"
    is monoid_mult_class.power_numeral_even.

tts_lemma power_numeral_odd:
  assumes "z \<in> U"
  shows "z ^\<^sub>o\<^sub>w numeral (num.Bit1 w) = (let w = z ^\<^sub>o\<^sub>w numeral w in z *\<^sub>o\<^sub>w w *\<^sub>o\<^sub>w w)"
    is monoid_mult_class.power_numeral_odd.

tts_lemma power_minus_mult:
  assumes "a \<in> U" and "0 < n"
  shows "a ^\<^sub>o\<^sub>w (n - 1) *\<^sub>o\<^sub>w a = a ^\<^sub>o\<^sub>w n"
    is monoid_mult_class.power_minus_mult.

tts_lemma power_Suc0_right:
  assumes "a \<in> U" 
  shows "a ^\<^sub>o\<^sub>w Suc 0 = a"
    is monoid_mult_class.power_Suc0_right.

tts_lemma power2_eq_square:
  assumes "a \<in> U"
  shows "a ^\<^sub>o\<^sub>w 2 = a *\<^sub>o\<^sub>w a"
    is monoid_mult_class.power2_eq_square.

tts_lemma power_one_right:
  assumes "a \<in> U"
  shows "a ^\<^sub>o\<^sub>w 1 = a"
    is monoid_mult_class.power_one_right.

tts_lemma power_commutes:
  assumes "a \<in> U"
  shows "a ^\<^sub>o\<^sub>w n *\<^sub>o\<^sub>w a = a *\<^sub>o\<^sub>w a ^\<^sub>o\<^sub>w n"
    is monoid_mult_class.power_commutes.

tts_lemma power3_eq_cube:
  assumes "a \<in> U"
  shows "a ^\<^sub>o\<^sub>w 3 = a *\<^sub>o\<^sub>w a *\<^sub>o\<^sub>w a"
    is monoid_mult_class.power3_eq_cube.

tts_lemma power_even_eq:
  assumes "a \<in> U"
  shows "a ^\<^sub>o\<^sub>w (2 * n) = (a ^\<^sub>o\<^sub>w n) ^\<^sub>o\<^sub>w 2"
    is monoid_mult_class.power_even_eq.

tts_lemma power_odd_eq:
  assumes "a \<in> U"
  shows "a ^\<^sub>o\<^sub>w Suc (2 * n) = a *\<^sub>o\<^sub>w (a ^\<^sub>o\<^sub>w n) ^\<^sub>o\<^sub>w 2"
    is monoid_mult_class.power_odd_eq.

tts_lemma power_mult:
  assumes "a \<in> U"
  shows "a ^\<^sub>o\<^sub>w (m * n) = (a ^\<^sub>o\<^sub>w m) ^\<^sub>o\<^sub>w n"
    is monoid_mult_class.power_mult.

tts_lemma power_Suc2:
  assumes "a \<in> U"
  shows "a ^\<^sub>o\<^sub>w Suc n = a ^\<^sub>o\<^sub>w n *\<^sub>o\<^sub>w a"
    is monoid_mult_class.power_Suc2.

tts_lemma power_one: "1\<^sub>o\<^sub>w ^\<^sub>o\<^sub>w n = 1\<^sub>o\<^sub>w"
  is monoid_mult_class.power_one.

tts_lemma power_add:
  assumes "a \<in> U"
  shows "a ^\<^sub>o\<^sub>w (m + n) = a ^\<^sub>o\<^sub>w m *\<^sub>o\<^sub>w a ^\<^sub>o\<^sub>w n"
    is monoid_mult_class.power_add.

tts_lemma power_mult_numeral:
  assumes "a \<in> U"
  shows "(a ^\<^sub>o\<^sub>w numeral m) ^\<^sub>o\<^sub>w numeral n = a ^\<^sub>o\<^sub>w numeral (m * n)"
    is Power.power_mult_numeral.

tts_lemma power_add_numeral2:
  assumes "a \<in> U" and "b \<in> U"
  shows 
    "a ^\<^sub>o\<^sub>w numeral m *\<^sub>o\<^sub>w (a ^\<^sub>o\<^sub>w numeral n *\<^sub>o\<^sub>w b) = a ^\<^sub>o\<^sub>w numeral (m + n) *\<^sub>o\<^sub>w b"
    is Power.power_add_numeral2.

tts_lemma power_add_numeral:
  assumes "a \<in> U"
  shows "a ^\<^sub>o\<^sub>w numeral m *\<^sub>o\<^sub>w a ^\<^sub>o\<^sub>w numeral n = a ^\<^sub>o\<^sub>w numeral (m + n)"
    is Power.power_add_numeral.

end

end



subsection\<open>Commutative monoids\<close>


subsubsection\<open>Definitions and common properties\<close>

locale comm_monoid_ow = 
  abel_semigroup_ow U f + neutral_ow U z for U :: "'ag set" and f z +
  assumes comm_neutral: "a \<in> U \<Longrightarrow> (a \<^bold>*\<^sub>o\<^sub>w \<^bold>1\<^sub>o\<^sub>w) = a"
begin

sublocale monoid_ow U \<open>(\<^bold>*\<^sub>o\<^sub>w)\<close> \<open>\<^bold>1\<^sub>o\<^sub>w\<close>
  apply unfold_locales
  subgoal by (simp add: comm_neutral commute)
  subgoal using commute by (simp add: comm_neutral)
  done

end

lemma comm_monoid_ow: "comm_monoid = comm_monoid_ow UNIV"
  unfolding 
    comm_monoid_def comm_monoid_ow_def
    comm_monoid_axioms_def comm_monoid_ow_axioms_def
    neutral_ow_def
    abel_semigroup_ow
  by simp

locale comm_monoid_set_ow = comm_monoid_ow U f z for U :: "'ag set" and f z
begin

tts_register_sbts \<open>(\<^bold>*\<^sub>o\<^sub>w)\<close> | U by (rule tts_AA_A_transfer[OF f_closed])
                        
end

lemma comm_monoid_set_ow: "comm_monoid_set = comm_monoid_set_ow UNIV"
  unfolding comm_monoid_set_def comm_monoid_set_ow_def comm_monoid_ow by simp

locale comm_monoid_add_ow =
  ab_semigroup_add_ow U plus + zero_ow U zero   
  for U :: "'ag set" and plus zero +
  assumes add_0[simp]: "a \<in> U \<Longrightarrow> 0\<^sub>o\<^sub>w +\<^sub>o\<^sub>w a = a"
begin

sublocale add: comm_monoid_ow U \<open>(+\<^sub>o\<^sub>w)\<close> \<open>0\<^sub>o\<^sub>w\<close>
  by unfold_locales (use add.commute in force)

sublocale monoid_add_ow U \<open>(+\<^sub>o\<^sub>w)\<close> \<open>0\<^sub>o\<^sub>w\<close> by unfold_locales simp+ 

sublocale sum: comm_monoid_set_ow U \<open>(+\<^sub>o\<^sub>w)\<close> \<open>0\<^sub>o\<^sub>w\<close> ..

notation sum.F (\<open>\<guillemotleft>sum\<guillemotright>\<close>)

abbreviation Sum (\<open>\<Sum>\<^sub>o\<^sub>w/ _\<close> [1000] 1000)
  where "\<Sum>\<^sub>o\<^sub>w A \<equiv> (\<guillemotleft>sum\<guillemotright> (\<lambda>x. x) A)"

notation Sum (\<open>\<Sum>\<^sub>o\<^sub>w/ _\<close> [1000] 1000)

end

lemma comm_monoid_add_ow: "class.comm_monoid_add = comm_monoid_add_ow UNIV"
  unfolding 
    class.comm_monoid_add_def comm_monoid_add_ow_def
    class.comm_monoid_add_axioms_def comm_monoid_add_ow_axioms_def
    zero_ow_def neutral_ow_def
    ab_semigroup_add_ow
  by simp

locale dvd_ow = times_ow U times 
  for U :: "'ag set" and times

ud \<open>dvd.dvd\<close>
ud dvd' \<open>dvd_class.dvd\<close>

ctr relativization
  synthesis ctr_simps
  assumes [transfer_domain_rule, transfer_rule]: "Domainp A = (\<lambda>x. x \<in> U)"
    and [transfer_rule]: "bi_unique A" "right_total A"
  trp (?'a A)
  in dvd_ow': dvd.with_def 
    (\<open>(on _ with _: _ \<guillemotleft>dvd\<guillemotright> _)\<close> [1000, 1000, 1000, 1000] 50)

ctr parametricity
  in dvd_ow'': dvd_ow'_def 

context dvd_ow
begin

abbreviation dvd (infixr \<open>\<guillemotleft>dvd\<guillemotright>\<close> 50) where "a \<guillemotleft>dvd\<guillemotright> b \<equiv> dvd_ow' U (*\<^sub>o\<^sub>w) a b"
notation dvd (infixr \<open>\<guillemotleft>dvd\<guillemotright>\<close> 50)

end

locale comm_monoid_mult_ow =
  ab_semigroup_mult_ow U times + one_ow U one 
  for U :: "'ag set" and times one +
  assumes mult_1[simp]: "a \<in> U \<Longrightarrow> 1\<^sub>o\<^sub>w *\<^sub>o\<^sub>w a = a"
begin

sublocale dvd_ow ..

sublocale mult: comm_monoid_ow U \<open>(*\<^sub>o\<^sub>w)\<close> \<open>1\<^sub>o\<^sub>w\<close>
  by unfold_locales (use mult.commute in force)

sublocale monoid_mult_ow U \<open>1\<^sub>o\<^sub>w\<close> \<open>(*\<^sub>o\<^sub>w)\<close> by unfold_locales simp+ 

sublocale prod: comm_monoid_set_ow U \<open>(*\<^sub>o\<^sub>w)\<close> \<open>1\<^sub>o\<^sub>w\<close> ..

notation prod.F (\<open>\<guillemotleft>prod\<guillemotright>\<close>)

abbreviation Prod (\<open>\<Prod>\<^sub>o\<^sub>w _\<close> [1000] 1000)
  where "\<Prod>\<^sub>o\<^sub>w A \<equiv> (\<guillemotleft>prod\<guillemotright> (\<lambda>x. x) A)"

notation Prod (\<open>\<Prod>\<^sub>o\<^sub>w _\<close> [1000] 1000)

end

lemma comm_monoid_mult_ow: "class.comm_monoid_mult = comm_monoid_mult_ow UNIV"
  unfolding 
    class.comm_monoid_mult_def comm_monoid_mult_ow_def
    class.comm_monoid_mult_axioms_def comm_monoid_mult_ow_axioms_def  
    one_ow_def neutral_ow_def
    ab_semigroup_mult_ow
  by simp


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma bij_betw_transfer[transfer_rule]:
  assumes [transfer_rule]:
    "bi_unique A" "right_total A" "bi_unique B" "right_total B" 
  shows 
    "((A ===> B) ===> rel_set A ===> rel_set B ===> (=)) bij_betw bij_betw"
  unfolding bij_betw_def inj_on_def
  apply transfer_prover_start
  apply transfer_step+
  by simp

lemma comm_monoid_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows 
    "((A ===> A ===> A) ===> A ===> (=)) 
      (comm_monoid_ow (Collect (Domainp A))) comm_monoid"
proof -
  let ?P = "((A ===> A ===> A) ===> A ===> (=))"
  let ?comm_monoid_ow = "comm_monoid_ow (Collect (Domainp A))"
  have "?P ?comm_monoid_ow 
    (\<lambda>f z. z \<in> UNIV \<and> comm_monoid f z)"
    unfolding 
      comm_monoid_ow_def comm_monoid_def  
      comm_monoid_ow_axioms_def comm_monoid_axioms_def 
      neutral_ow_def
    apply transfer_prover_start
    apply transfer_step+
    by auto
  thus ?thesis by simp
qed

lemma comm_monoid_set_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> A ===> (=)) 
      (comm_monoid_set_ow (Collect (Domainp A))) comm_monoid_set"
  unfolding comm_monoid_set_ow_def comm_monoid_set_def
  apply transfer_prover_start
  apply transfer_step+
  by simp

lemma comm_monoid_add_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> A ===> (=)) 
      (comm_monoid_add_ow (Collect (Domainp A))) class.comm_monoid_add"
proof -
  let ?P = "((A ===> A ===> A) ===> A ===> (=))"
  let ?comm_monoid_add_ow = "comm_monoid_add_ow (Collect (Domainp A))"
  have "?P ?comm_monoid_add_ow (\<lambda>f z. z \<in> UNIV \<and> class.comm_monoid_add f z)"
    unfolding 
      comm_monoid_add_ow_def class.comm_monoid_add_def 
      zero_ow_def neutral_ow_def 
      comm_monoid_add_ow_axioms_def class.comm_monoid_add_axioms_def
    apply transfer_prover_start
    apply transfer_step+
    by auto
  thus ?thesis by simp
qed

lemma comm_monoid_mult_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> A ===> (=)) 
      (comm_monoid_mult_ow (Collect (Domainp A))) class.comm_monoid_mult"
proof -
  let ?P = "((A ===> A ===> A) ===> A ===> (=))"
  let ?comm_monoid_mult_ow = "comm_monoid_mult_ow (Collect (Domainp A))"
  have "?P ?comm_monoid_mult_ow (\<lambda>f z. z \<in> UNIV \<and> class.comm_monoid_mult f z)"
    unfolding 
      comm_monoid_mult_ow_def class.comm_monoid_mult_def 
      one_ow_def neutral_ow_def 
      comm_monoid_mult_ow_axioms_def class.comm_monoid_mult_axioms_def
    apply transfer_prover_start
    apply transfer_step+
    by auto
  thus ?thesis by simp
qed

lemma dvd_with_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> A ===> A ===> (=)) 
      (dvd_ow' (Collect (Domainp A))) dvd.with"
  unfolding dvd_ow'_def dvd.with_def by transfer_prover

end


subsubsection\<open>Relativization\<close>

context dvd_ow
begin

tts_context
  tts: (?'a to U)
  sbterms: (\<open>(*)::[?'a::times, ?'a::times] \<Rightarrow> ?'a::times\<close> to \<open>(*\<^sub>o\<^sub>w)\<close>)
  rewriting ctr_simps
  substituting dvd_ow_axioms 
  eliminating through simp
begin

tts_lemma dvdI:
  assumes "b \<in> U" and "k \<in> U" and "a = b *\<^sub>o\<^sub>w k"
  shows "b \<guillemotleft>dvd\<guillemotright> a"
    is dvd_class.dvdI.

tts_lemma dvdE:
  assumes "b \<in> U" 
    and "a \<in> U" 
    and "b \<guillemotleft>dvd\<guillemotright> a" 
    and "\<And>k. \<lbrakk>k \<in> U; a = b *\<^sub>o\<^sub>w k\<rbrakk> \<Longrightarrow> P"
  shows P
    is dvd_class.dvdE.

end

end

context comm_monoid_mult_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting comm_monoid_mult_ow_axioms and one.not_empty
  applying [OF mult.f_closed' one_closed]
begin

tts_lemma strict_subset_divisors_dvd:
  assumes "a \<in> U" and "b \<in> U"
  shows 
    "({x \<in> U. x \<guillemotleft>dvd\<guillemotright> a} \<subset> {x \<in> U. x \<guillemotleft>dvd\<guillemotright> b}) = (a \<guillemotleft>dvd\<guillemotright> b \<and> \<not> b \<guillemotleft>dvd\<guillemotright> a)"
    is comm_monoid_mult_class.strict_subset_divisors_dvd.

tts_lemma subset_divisors_dvd:
  assumes "a \<in> U" and "b \<in> U"
  shows "({x \<in> U. x \<guillemotleft>dvd\<guillemotright> a} \<subseteq> {x \<in> U. x \<guillemotleft>dvd\<guillemotright> b}) = (a \<guillemotleft>dvd\<guillemotright> b)"
    is comm_monoid_mult_class.subset_divisors_dvd.

tts_lemma power_mult_distrib:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a *\<^sub>o\<^sub>w b) ^\<^sub>o\<^sub>w n = a ^\<^sub>o\<^sub>w n *\<^sub>o\<^sub>w b ^\<^sub>o\<^sub>w n"
    is Power.comm_monoid_mult_class.power_mult_distrib.

tts_lemma dvd_triv_right:
  assumes "a \<in> U" and "b \<in> U"
  shows "a \<guillemotleft>dvd\<guillemotright> b *\<^sub>o\<^sub>w a"
    is comm_monoid_mult_class.dvd_triv_right.

tts_lemma dvd_mult_right:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "a *\<^sub>o\<^sub>w b \<guillemotleft>dvd\<guillemotright> c"
  shows "b \<guillemotleft>dvd\<guillemotright> c"
    is comm_monoid_mult_class.dvd_mult_right.

tts_lemma mult_dvd_mono:
  assumes "a \<in> U" 
    and "b \<in> U" 
    and "c \<in> U" 
    and "d \<in> U"
    and "a \<guillemotleft>dvd\<guillemotright> b"
    and "c \<guillemotleft>dvd\<guillemotright> d"
  shows "a *\<^sub>o\<^sub>w c \<guillemotleft>dvd\<guillemotright> b *\<^sub>o\<^sub>w d"
    is comm_monoid_mult_class.mult_dvd_mono.

tts_lemma dvd_triv_left:
  assumes "a \<in> U" and "b \<in> U"
  shows "a \<guillemotleft>dvd\<guillemotright> a *\<^sub>o\<^sub>w b"
    is comm_monoid_mult_class.dvd_triv_left.

tts_lemma dvd_mult_left:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "a *\<^sub>o\<^sub>w b \<guillemotleft>dvd\<guillemotright> c"
  shows "a \<guillemotleft>dvd\<guillemotright> c"
    is comm_monoid_mult_class.dvd_mult_left.

tts_lemma dvd_trans:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "a \<guillemotleft>dvd\<guillemotright> b" and "b \<guillemotleft>dvd\<guillemotright> c"
  shows "a \<guillemotleft>dvd\<guillemotright> c"
    is comm_monoid_mult_class.dvd_trans.

tts_lemma dvd_mult2:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "a \<guillemotleft>dvd\<guillemotright> b"
  shows "a \<guillemotleft>dvd\<guillemotright> b *\<^sub>o\<^sub>w c"
    is comm_monoid_mult_class.dvd_mult2.

tts_lemma dvd_refl:
  assumes "a \<in> U"
  shows "a \<guillemotleft>dvd\<guillemotright> a"
    is comm_monoid_mult_class.dvd_refl.

tts_lemma dvd_mult:
  assumes "a \<in> U" and "c \<in> U" and "b \<in> U" and "a \<guillemotleft>dvd\<guillemotright> c"
  shows "a \<guillemotleft>dvd\<guillemotright> b *\<^sub>o\<^sub>w c"
    is comm_monoid_mult_class.dvd_mult.

tts_lemma one_dvd:
  assumes "a \<in> U"
  shows "1\<^sub>o\<^sub>w \<guillemotleft>dvd\<guillemotright> a"
    is comm_monoid_mult_class.one_dvd.

end

end



subsection\<open>Cancellative commutative monoids\<close>


subsubsection\<open>Definitions and common properties\<close>

locale cancel_comm_monoid_add_ow =
  cancel_ab_semigroup_add_ow U plus minus +
  comm_monoid_add_ow U plus zero
  for U :: "'ag set" and plus minus zero

lemma cancel_comm_monoid_add_ow: 
  "class.cancel_comm_monoid_add = cancel_comm_monoid_add_ow UNIV"
  unfolding 
    class.cancel_comm_monoid_add_def cancel_comm_monoid_add_ow_def
    cancel_ab_semigroup_add_ow comm_monoid_add_ow
  by simp


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma cancel_comm_monoid_add_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> (A ===> A ===> A) ===> A ===> (=)) 
      (cancel_comm_monoid_add_ow (Collect (Domainp A))) 
      class.cancel_comm_monoid_add"
  unfolding cancel_comm_monoid_add_ow_def class.cancel_comm_monoid_add_def
  by transfer_prover

end


subsubsection\<open>Relativization\<close>

context cancel_comm_monoid_add_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting cancel_comm_monoid_add_ow_axioms and zero.not_empty
  applying [OF add.f_closed' minus_closed' zero_closed]
begin

tts_lemma add_cancel_right_right:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a = a +\<^sub>o\<^sub>w b) = (b = 0\<^sub>o\<^sub>w)"
    is cancel_comm_monoid_add_class.add_cancel_right_right.
    
tts_lemma add_cancel_right_left:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a = b +\<^sub>o\<^sub>w a) = (b = 0\<^sub>o\<^sub>w)"
    is cancel_comm_monoid_add_class.add_cancel_right_left.

tts_lemma add_cancel_left_right:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a +\<^sub>o\<^sub>w b = a) = (b = 0\<^sub>o\<^sub>w)"
    is cancel_comm_monoid_add_class.add_cancel_left_right.

tts_lemma add_cancel_left_left:
  assumes "b \<in> U" and "a \<in> U"
  shows "(b +\<^sub>o\<^sub>w a = a) = (b = 0\<^sub>o\<^sub>w)"
    is cancel_comm_monoid_add_class.add_cancel_left_left.

tts_lemma add_implies_diff:
  assumes "c \<in> U" and "b \<in> U" and "a \<in> U" and "c +\<^sub>o\<^sub>w b = a"
  shows "c = a -\<^sub>o\<^sub>w b"
    is cancel_comm_monoid_add_class.add_implies_diff.

tts_lemma diff_cancel:
  assumes "a \<in> U"
  shows "a -\<^sub>o\<^sub>w a = 0\<^sub>o\<^sub>w"
    is cancel_comm_monoid_add_class.diff_cancel.

tts_lemma diff_zero:
  assumes "a \<in> U"
  shows "a -\<^sub>o\<^sub>w 0\<^sub>o\<^sub>w = a"
    is cancel_comm_monoid_add_class.diff_zero.

end

end

text\<open>\newpage\<close>

end