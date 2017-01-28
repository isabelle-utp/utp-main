section {* Dyadic rational numbers *}

theory Dyadic
imports Real Transcendental cardinals 
begin

text {* A dyadic rational is a rational whose denominator is a power of 2. They are precisely the
  rational numbers that can be encoded in binary. *}

definition dyadic :: "'a::field_char_0 \<Rightarrow> bool" where
"dyadic x = (\<exists> a \<in> \<int>. \<exists> b. x = a / 2^b)"

abbreviation Dyadics :: "'a::field_char_0 set" ("\<rat>\<^sub>D")
where "\<rat>\<^sub>D \<equiv> {x. dyadic x}"

lemma dyadic_zero: "dyadic 0"
  by (auto simp add: dyadic_def)

lemma dyadic_one: "dyadic 1"
  by (auto simp add: dyadic_def)

lemma dyadic_plus: 
  assumes "dyadic x" "dyadic y"
  shows "dyadic (x + y)"
using assms
proof (clarsimp simp add: dyadic_def)
  fix a1 a2 :: "'a :: field_char_0" and b1 b2 :: nat
  assume as: "a1 \<in> \<int>" "a2 \<in> \<int>"
  have "a1 / 2 ^ b1 + a2 / 2 ^ b2 = (2 ^ (b2 - b1) * a1 + 2 ^ (b1 - b2) * a2) / 2 ^ max b1 b2"
    by (cases "b1 \<ge> b2")
       (simp_all add: max_absorb1 max_absorb2 divide_add_eq_iff power_diff add_divide_eq_iff mult.commute)
  moreover from as have "2 ^ (b2 - b1) * a1 + 2 ^ (b1 - b2) * a2 \<in> \<int>"
    by (metis Ints_add Ints_mult Ints_of_int Ints_power of_int_numeral)
  ultimately show "\<exists>a\<in>\<int>. \<exists>b. a1 / 2 ^ b1 + a2 / 2 ^ b2 = a / 2 ^ b"
    by auto
qed

lemma dyadic_uminus: "dyadic x \<Longrightarrow> dyadic (- x)"
  using Ints_minus minus_divide_left by (force simp add: dyadic_def)

lemma dyadic_minus: 
  assumes "dyadic x" "dyadic y"
  shows "dyadic (x - y)"
proof -
  have xy: "x - y = (x + (- y))"
    using diff_conv_add_uminus by blast
  from assms show ?thesis
    unfolding xy by (blast intro: dyadic_plus dyadic_uminus)
qed

lemma dyadic_times: 
  assumes "dyadic x" "dyadic y"
  shows "dyadic (x * y)"
  using assms
  by (auto simp add: dyadic_def, metis Ints_mult power_add)

lemma dyadic_rational: "dyadic x \<Longrightarrow> x \<in> \<rat>"
  by (auto simp add: dyadic_def, metis Ints_def Rats_divide Rats_number_of Rats_of_int Rats_power imageE)
  
lemma dyadic_setsum: "\<lbrakk> finite A; \<forall> i \<in> A. dyadic (f i) \<rbrakk> \<Longrightarrow> dyadic (setsum f A)"
  by (induct rule: finite_induct, auto intro: dyadic_plus dyadic_zero)

lemma dyadic_div_pow_2: "x \<in> \<int> \<Longrightarrow> dyadic (x / 2^n)"
  by (auto simp add: dyadic_def)

lemma Dyadics_Rats: "\<rat>\<^sub>D \<subseteq> \<rat>"
  using dyadic_rational by blast

lemma Ints_dyadic: "\<int> \<subseteq> \<rat>\<^sub>D"
  apply (auto)
  apply (rename_tac x)
  apply (simp add: dyadic_def)
  apply (rule_tac x="x" in bexI)
  apply (rule_tac x="0" in exI)
  apply (auto) 
done

lemma Nats_dyadic: "\<nat> \<subseteq> \<rat>\<^sub>D"
  by (metis Ints_dyadic Ints_of_nat Nats_cases subset_eq)

lemma Dyadics_countable:
  "countable \<rat>\<^sub>D"
  using Dyadics_Rats countable_rat countable_subset by blast
lemma coprime_power_two: "b > 0 \<Longrightarrow> coprime (a::int) (2^b) \<longleftrightarrow> odd a"
  apply (induct b arbitrary: a)
  apply (auto)
  apply (metis dvd_triv_left gcd_greatest_iff_int odd_one)
  apply (metis coprime_exp_int even_iff_mod_2_eq_zero gcd_1_int gcd_red_int not_mod_2_eq_0_eq_1 power_Suc)
done

typedef drat = "{x :: rat. dyadic x}"
  by (rule_tac x="0" in exI, auto simp add: dyadic_def)

setup_lifting type_definition_drat

lift_definition DFract :: "int \<Rightarrow> nat \<Rightarrow> drat"
is "\<lambda> a b. Fract a (2 ^ b)"
  apply (auto simp add: dyadic_def)
  apply (rename_tac a b)
  apply (rule_tac x="of_int a" in bexI)
  apply (rule_tac x="b" in exI)
  apply (auto simp add: Fract_of_int_quotient of_int_power)
done

lift_definition dfrac_of :: "drat \<Rightarrow> int \<times> nat" is
"\<lambda> x. (fst (quotient_of x), nat \<lfloor>log 2 (snd (quotient_of x))\<rfloor>)" .

lemma powr_as_power: "x > 0 \<Longrightarrow> x powr (real n) = x ^ n"
  by (induct n, simp_all, auto simp add: powr_add)

lemma dfrac_of_DFract:
  assumes "coprime a (2^b)"
  shows "dfrac_of (DFract a b) = (a, b)"
proof (cases "b = 0")
  case True
  thus ?thesis
    by (transfer, simp add: quotient_of_Fract)
next
  case False with assms show ?thesis
    by (transfer, auto simp add: quotient_of_Fract powr_as_power[THEN sym])
qed

lemma dyadic_Fract: "dyadic x \<Longrightarrow> \<exists> a b. x = Fract a (2^b)"
  apply (auto simp add: dyadic_def)
  apply (erule Ints_cases)
  apply (rename_tac a b z)
  apply (rule_tac x="z" in exI)
  apply (rule_tac x="b" in exI)
  apply (simp add: Fract_of_int_quotient of_int_power)
done
   
lemma dyadic_FractE: "\<lbrakk> dyadic x; \<And> a b. x = Fract a (2^b) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using dyadic_Fract by blast

thm parity_induct

(*
inductive 

lemma even_induct: 
  fixes a :: nat
  assumes "even a" "P 0" "\<And> n. \<lbrakk> even n; P n \<rbrakk> \<Longrightarrow> P (Suc (Suc n))"
  shows "P a"
using assms(1) proof (induct a)
  case 0 from assms show ?case by simp
next
  case (Suc n) thus ?case
  proof (induct n)
    case 0 thus ?case by auto
  next
    case (Suc m) thus ?case
      apply (auto)
*)

inductive ieven :: "nat \<Rightarrow> bool" and iodd :: "nat \<Rightarrow> bool" where
ieven_0 [intro]: "ieven 0" | 
ieven_Suc [intro]: "iodd n \<Longrightarrow> ieven (Suc n)" |
iodd_Suc [intro]: "ieven n \<Longrightarrow> iodd (Suc n)"

print_theorems

inductive_cases
  ieven_0E [elim]: "ieven 0" and
  iodd_0E [elim]: "iodd 0" and
  ieven_SucE [elim]: "ieven (Suc n)" and
  iodd_SucE [elim]: "iodd (Suc n)"

lemma ieven_induct: "\<lbrakk> ieven x; P 0; \<And> n. \<lbrakk> ieven n; P n \<rbrakk> \<Longrightarrow> P (Suc (Suc n)) \<rbrakk> \<Longrightarrow> P x"
  by (simp add: ieven_iodd.inducts(1))

lemma iodd_induct: "\<lbrakk> iodd x; P 1; \<And> n. \<lbrakk> iodd n; P n \<rbrakk> \<Longrightarrow> P (Suc (Suc n)) \<rbrakk> \<Longrightarrow> P x"
  by (simp add: ieven_iodd.inducts(2))

lemma iodd_odd: "iodd x \<Longrightarrow> odd x" and ieven_even: "ieven x \<Longrightarrow> even x"
  by (induct x, auto)

lemma odd_iodd: "odd x \<Longrightarrow> iodd x" and even_ieven: "even x \<Longrightarrow> ieven x"
  by (induct x, auto)

lemma ieven_iff_even: "ieven x = even x"
  using even_ieven ieven_even by blast

lemma iodd_iff_odd: "iodd x = odd x"
  using odd_iodd iodd_odd by blast

lemma [simp]: "iodd 0 = False"
  by (auto)

fun tdiv2 :: "nat \<Rightarrow> nat" where
"tdiv2 x = (if (odd x \<or> x = 0) then 0 else Suc (tdiv2 (x div 2)))"

declare tdiv2.simps [simp del]

lemma odd_div_tdiv2:
  fixes x :: nat
  assumes "x > 0"
  shows "odd (x div (2^(tdiv2 x)))"
  using assms
  apply (case_tac "odd x")
  apply (simp add: tdiv2.simps)
  apply (induct x rule: tdiv2.induct)
  apply (simp)
  apply (rename_tac x)
  apply (case_tac "even (x div 2)")
  apply (simp_all)
  apply (metis Divides.div_mult2_eq Divides.div_positive dvd_imp_le neq0_conv pos2 power.simps(2) tdiv2.simps)
  apply (simp add: tdiv2.simps)
done

lemma tdiv2_mod: "x mod (2^(tdiv2 x)) = 0"
  apply (induct x rule: tdiv2.induct)
  apply (auto)
  apply (metis Divides.mod_mult2_eq add.right_neutral even_iff_mod_2_eq_zero mod_by_1 mult_zero_right neq0_conv power_0 power_Suc tdiv2.simps)
done

text {* Every number greater than 0 can be expressed as the multiple of a perfect square
        and an odd number *}

lemma evenE_nat [elim?]:
  fixes a :: nat
  assumes "a > 0"
  obtains b n where "odd b" "a = 2^n * b"
proof -
  have "odd (a div (2^(tdiv2 a)))"
    using assms odd_div_tdiv2 by blast
  moreover have "a div (2^(tdiv2 a)) * (2^(tdiv2 a)) = a"
    using mod_div_equality[of a "2^(tdiv2 a)"] by (simp add: tdiv2_mod)
  ultimately show ?thesis
    by (metis mult.commute that)
qed

lemma evenE_int [elim?]:
  fixes a :: int
  assumes "a \<noteq> 0"
  obtains b n where "odd b" "a = 2^n * b"
proof (cases "a \<ge> 0")
  case True
  then obtain a' :: nat where "a = int a'"
    using nonneg_eq_int by blast
  moreover obtain b' n' where "odd b'" "a' = 2^n' * b'"
    using assms calculation evenE_nat by auto
  ultimately show ?thesis using that
    by (metis even_int_iff of_nat_mult of_nat_power transfer_int_nat_numerals(3))
next
  case False
  then obtain a' :: nat where "a = - (int a')"
    by (metis Nat_Transfer.transfer_nat_int_function_closures(9) int_cases)
  moreover obtain b' n' where "odd b'" "a' = 2^n' * b'"
    using assms calculation evenE_nat by auto
  ultimately show ?thesis using that
    by (metis even_int_iff even_minus mult_minus_right of_nat_mult of_nat_numeral of_nat_power)
qed

lemma rat_of_int_div: "\<lbrakk> y dvd x \<rbrakk> \<Longrightarrow> rat_of_int x / rat_of_int y = rat_of_int (x div y)"
  by (metis Fract_of_int_quotient div_by_1 divide_eq_0_iff dvd_div_mult_self eq_rat(1) gcd_1_int gcd_dvd1 of_int_eq_0_iff of_int_rat zdiv_eq_0_iff)

(* FIXME: This proof can be tidied and shortened *)

lemma dyadic_Fract_0_1_coprime: 
  assumes "dyadic x" "x \<in> {0<..<1}"
  obtains a b where "x = Fract a (2^b)" "coprime a (2^b)"
proof -
  obtain a' b' where x_def: "x = Fract a' (2 ^ b')"
    using assms dyadic_Fract by blast
  with assms have a'_nz: "a' > 0"
    by (simp add: zero_less_Fract_iff)
  with assms(2) have "a' \<noteq> 0"
    by (auto simp add: rat_number_collapse(1))
  then obtain k n where kn: "odd k" "a' = 2^n * k" "k > 0"
    by (metis a'_nz evenE_int not_numeral_less_zero power_less_zero_eq zero_less_mult_iff) 
  then have "x = Fract k (2 ^ (b' - n))"
  proof -
    from kn have tn_dv1: "(2^n) dvd a'"
      by (auto)
    from assms x_def have "a' < 2 ^ b'"
      by (simp add: Fract_less_one_iff)
    moreover from kn have "2 ^ n \<le> 2 ^ n * k"
      by auto
    ultimately have "(2^n :: int) < 2^b'"
      using kn(2) by (simp only:)
    hence nb': "n < b'"
      by auto
    hence tn_dv2: "(2^n :: int) dvd (2^b')"
      by (simp add: le_imp_power_dvd less_imp_le_nat)
    have "rat_of_int a' / rat_of_int (2 ^ b') = (rat_of_int a' / rat_of_int (2^n)) / (rat_of_int (2^b') / rat_of_int (2^n))"
      by simp
    also have "... = rat_of_int (a' div 2^n) / (rat_of_int ((2^b') div (2^n)))"
      using rat_of_int_div tn_dv1 tn_dv2 by presburger
    also from kn have "... = rat_of_int k / (rat_of_int ((2^b') div (2^n)))"
      by simp
    also have "... = rat_of_int k / rat_of_int (2 ^ (b' - n))"
      by (metis (mono_tags, lifting) dbl_simps(3) eq_numeral_simps(4) less_imp_le_nat nb' of_int_numeral of_int_power power_diff rat_of_int_div tn_dv2)
    finally show ?thesis
      by (simp add: Fract_of_int_quotient x_def)
  qed
  moreover have "coprime k (2 ^ (b' - n))"
    by (metis coprime_exp_int even_iff_mod_2_eq_zero gcd_1_int gcd_red_int kn(1) not_mod_2_eq_1_eq_0)
  ultimately show ?thesis
    using that by blast
qed

context field_char_0
begin

lift_definition of_drat :: "drat \<Rightarrow> 'a"
  is "\<lambda>x. of_int (fst (quotient_of x)) / of_int (snd (quotient_of x))" .

end

lemma of_drat_exists:
  assumes "x \<in> \<rat>\<^sub>D" 
  shows "\<exists> n. x = of_drat n"
proof -
  from assms obtain a :: int and b :: nat where "x = (of_int a) / 2^b"
    by (auto simp add: dyadic_def, metis Ints_def imageE)
  thus ?thesis
    apply (rule_tac x="DFract a b" in exI)
    apply (transfer)  
    apply (auto simp add: dyadic_def quotient_of_Fract)
    apply (smt normalize_denom_pos normalize_eq numeral_One numeral_plus_numeral of_int_1 of_int_add of_int_power of_rat_rat power_not_zero semiring_norm(2) surjective_pairing)
  done
qed

lemma drat_cases:
  "\<lbrakk> x \<in> \<rat>\<^sub>D; \<And> n. x = of_drat n \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  using of_drat_exists by blast

lemma gcd_power_two: "gcd a (2^Suc b) = (if ((a::int) mod 2 = 0) then (2 * gcd (a div 2) (2^b)) else 1)"
  apply (auto)
  apply (subst gcd_mult_distrib_int[THEN sym])
  apply (simp)
  apply (metis abs_gcd_int coprime_exp_int gcd_dvd1 gcd_red_int power.simps(2) zdvd1_eq)
done

instantiation drat :: "{plus,minus,uminus,times,one,zero}"
begin
  lift_definition zero_drat :: drat is 0
    by (fact dyadic_zero)
  lift_definition one_drat :: drat is 1
    by (fact dyadic_one)
  lift_definition plus_drat :: "drat \<Rightarrow> drat \<Rightarrow> drat" is "op +"
    by (fact dyadic_plus)
  lift_definition minus_drat :: "drat \<Rightarrow> drat \<Rightarrow> drat" is "op -"
    by (fact dyadic_minus)
  lift_definition uminus_drat :: "drat \<Rightarrow> drat" is "uminus"
    by (fact dyadic_uminus)
  lift_definition times_drat :: "drat \<Rightarrow> drat \<Rightarrow> drat" is "op *"
    by (fact dyadic_times)
instance ..
end

instance drat :: idom
  by (intro_classes, (transfer, auto simp add: distrib_left distrib_right)+)

instantiation drat :: linorder
begin
  lift_definition less_eq_drat :: "drat \<Rightarrow> drat \<Rightarrow> bool" is "op \<le>" .
  lift_definition less_drat :: "drat \<Rightarrow> drat \<Rightarrow> bool" is "op <" .
instance 
  by (intro_classes, (transfer, auto)+)
end

instantiation drat :: linordered_idom
begin
  lift_definition sgn_drat :: "drat \<Rightarrow> drat" is sgn
    apply (transfer, auto simp add: dyadic_def sgn_rat_def)
    apply (rule_tac x="-1" in bexI, rule_tac x="0" in exI, auto)
  done
  lift_definition abs_drat :: "drat \<Rightarrow> drat" is abs
    apply (transfer, auto simp add: dyadic_def abs_rat_def)
    using Ints_minus minus_divide_left apply blast
  done

instance
  by (intro_classes, (transfer, auto)+)
end

lemma of_drat_0: "of_drat 0 = 0"
  by (transfer, simp)

lemma of_drat_1: "of_drat 1 = 1"
  by (transfer, simp)


lemma quotient_of_div_simp:
  "of_int (fst (quotient_of x)) / of_int (snd (quotient_of x)) = of_rat x"
  by (metis (mono_tags, lifting) of_rat_divide of_rat_of_int_eq prod.collapse quotient_of_div)

lemma dyadic_of_rat: "dyadic x \<Longrightarrow> dyadic (of_rat x)"
  apply (auto simp add: dyadic_def)
  apply (rename_tac a b)
  apply (rule_tac x="of_rat a" in bexI)
  apply (rule_tac x="b" in exI)
  apply (simp add: of_rat_divide of_rat_power)
  apply (metis Ints_cases Ints_of_int of_rat_of_int_eq)
done

lemma dyadic_of_drat: "dyadic (of_drat x)"
  by (transfer, simp add: quotient_of_div_simp dyadic_of_rat)

lemma of_drat_less_eq:
  "(of_drat x :: 'a::{linordered_field}) \<le> of_drat y \<longleftrightarrow> x \<le> y"
  by (transfer, auto simp add: of_rat_less_eq quotient_of_div_simp)

lemma of_drat_less:
  "(of_drat x :: 'a::{linordered_field}) < of_drat y \<longleftrightarrow> x < y"
  by (transfer, auto simp add: of_rat_less quotient_of_div_simp)

lemma of_drat_0_1:
  "(of_drat x :: 'a::{linordered_field}) \<in> {0<..<1} \<longleftrightarrow> x \<in> {0<..<1}"
  by (auto) (metis of_drat_0 of_drat_less, metis of_drat_1 of_drat_less)+

lemma drat_0_1_induct: 
  assumes "x \<in> {0<..<1}" "\<And> a b. coprime a (2^b) \<Longrightarrow> P (DFract a b)"
  shows "P x"
proof -
  from assms(1) have "(of_drat x :: rat) \<in> {0<..<1}"
    by (auto, metis of_drat_0 of_drat_less, metis of_drat_1 of_drat_less)
  then obtain a b where "of_drat x = Fract a (2^b)" "coprime a (2^b)"
    using dyadic_Fract_0_1_coprime dyadic_of_drat by blast
  moreover hence "x = DFract a b"
    by (transfer, simp add: quotient_of_div_simp)
  ultimately show ?thesis
    using assms(2) by blast
qed

end