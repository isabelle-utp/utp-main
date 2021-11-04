
section \<open>Extended integers (i.e. with infinity)\<close>

text\<open>
  This section formalizes the extended integers, which serve as the codomain for the $p$-adic 
  valuation. The element $\infty$ is added to the integers to serve as a maximxal element in the 
  order, which is the valuation of $0$.
\<close>

theory Extended_Int
imports Main "HOL-Library.Countable" "HOL-Library.Order_Continuity" "HOL-Library.Extended_Nat"
begin

text\<open>
  The following is based very closely on the theory \<^theory>\<open>HOL-Library.Extended_Nat\<close> from the 
  standard Isabelle distribution, with adaptations made to formalize the integers extended with
  an element for infinity. This is the standard range for the valuation function on a discretely
  valued ring such as the field of $p$-adic numbers, such as in \cite{engler2005valued}.
\<close>

context
  fixes f :: "nat \<Rightarrow> 'a::{canonically_ordered_monoid_add, linorder_topology, complete_linorder}"
begin

lemma sums_SUP[simp, intro]: "f sums (SUP n. \<Sum>i<n. f i)"
  unfolding sums_def by (intro LIMSEQ_SUP monoI sum_mono2 zero_le) auto

lemma suminf_eq_SUP: "suminf f = (SUP n. \<Sum>i<n. f i)"
  using sums_SUP by (rule sums_unique[symmetric])

end

subsection \<open>Type definition\<close>

text \<open>
  We extend the standard natural numbers by a special value indicating
  infinity.
\<close>

typedef eint = "UNIV :: int option set" ..


definition eint :: "int \<Rightarrow> eint" where
  "eint n = Abs_eint (Some n)"

instantiation eint :: infinity
begin

definition "\<infinity> = Abs_eint None"
instance ..

end

fun int_option_enumeration :: "int option \<Rightarrow> nat" where
"int_option_enumeration (Some n) = (if n \<ge> 0 then nat (2*(n + 1)) else  nat (2*(-n) + 1))"|
"int_option_enumeration None = (0::nat)"

lemma int_option_enumeration_inj:
"inj int_option_enumeration"
proof 
  have pos_even: "\<And>n::int. n \<ge> 0 \<Longrightarrow> even (int_option_enumeration (Some n)) \<and> (int_option_enumeration (Some n))> 0"
  proof-
    fix n::int assume "n \<ge>0" then have "(int_option_enumeration (Some n)) = nat (2*(n + 1))"
      by simp
    then show "even (int_option_enumeration (Some n)) \<and> 0 < int_option_enumeration (Some n)"
      by (smt \<open>0 \<le> n\<close> even_of_nat int_nat_eq oddE zero_less_nat_eq)  
  qed
  have neg_odd: "\<And>n::int. n < 0 \<Longrightarrow> odd (int_option_enumeration (Some n))"
    by (smt evenE even_of_nat int_nat_eq int_option_enumeration.simps(1))
  fix x y assume A: "x \<in> UNIV" "y \<in> UNIV" "int_option_enumeration x = int_option_enumeration y"
  show "x = y"
    apply(cases "x = None")
      using A pos_even neg_odd 
      apply (metis dvd_0_right int_option_enumeration.elims int_option_enumeration.simps(2) not_gr0 not_le)
    proof-
      assume "x \<noteq>None"
      then obtain n where n_def: "x = Some n"
        by auto 
      then have y_not_None: "y \<noteq> None"
        using A 
        by (metis \<open>\<And>thesis. (\<And>n. x = Some n \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
              add_cancel_right_right even_add int_option_enumeration.simps(2) 
              linorder_not_less neg_odd neq0_conv pos_even) 
      then obtain m where m_def: "y = Some m"
        by blast
      show ?thesis 
      proof(cases "n \<ge>0")
        case True
        then show ?thesis 
          using n_def A neg_odd pos_even m_def int_option_enumeration.simps(1)
          by (smt int_nat_eq)
      next
        case False
        then show ?thesis 
          using n_def A neg_odd pos_even m_def int_option_enumeration.simps(1)
          by (smt int_nat_eq)
      qed
  qed
qed

definition eint_enumeration where
"eint_enumeration = int_option_enumeration \<circ> Rep_eint"

lemma eint_enumeration_inj:
"inj eint_enumeration"
  unfolding eint_enumeration_def 
  using int_option_enumeration_inj Rep_eint_inject
  by (metis (mono_tags, lifting) comp_apply injD inj_on_def)
    
instance eint :: countable
proof
  show "\<exists>to_int::eint \<Rightarrow> nat. inj to_int"
    using eint_enumeration_inj by blast 
qed

old_rep_datatype eint "\<infinity> :: eint"
proof -
  fix P i assume "\<And>j. P (eint j)" "P \<infinity>"
  then show "P i"
  proof induct
    case (Abs_eint y) then show ?case
      by (cases y rule: option.exhaust)
         (auto simp: eint_def infinity_eint_def)
  qed
qed (auto simp add: eint_def infinity_eint_def Abs_eint_inject)

declare [[coercion "eint::int\<Rightarrow>eint"]]

lemmas eint2_cases = eint.exhaust[case_product eint.exhaust]
lemmas eint3_cases = eint.exhaust[case_product eint.exhaust eint.exhaust]

lemma not_infinity_eq [iff]: "(x \<noteq> \<infinity>) = (\<exists>i. x = eint i)"
  by (cases x) auto

lemma not_eint_eq [iff]: "(\<forall>y. x \<noteq> eint y) = (x = \<infinity>)"
  by (cases x) auto

lemma eint_ex_split: "(\<exists>c::eint. P c) \<longleftrightarrow> P \<infinity> \<or> (\<exists>c::int. P c)"
  by (metis eint.exhaust)

primrec the_eint :: "eint \<Rightarrow> int"
  where "the_eint (eint n) = n"


subsection \<open>Constructors and numbers\<close>

instantiation eint :: zero_neq_one
begin

definition
  "0 = eint 0"

definition
  "1 = eint 1"

instance
  proof qed (simp add: zero_eint_def one_eint_def)

end


lemma eint_0 [code_post]: "eint 0 = 0"
  by (simp add: zero_eint_def)

lemma eint_1 [code_post]: "eint 1 = 1"
  by (simp add: one_eint_def)

lemma eint_0_iff: "eint x = 0 \<longleftrightarrow> x = 0" "0 = eint x \<longleftrightarrow> x = 0"
  by (auto simp add: zero_eint_def)

lemma eint_1_iff: "eint x = 1 \<longleftrightarrow> x = 1" "1 = eint x \<longleftrightarrow> x = 1"
  by (auto simp add: one_eint_def)

lemma infinity_ne_i0 [simp]: "(\<infinity>::eint) \<noteq> 0"
  by (simp add: zero_eint_def)

lemma i0_ne_infinity [simp]: "0 \<noteq> (\<infinity>::eint)"
  by (simp add: zero_eint_def)

lemma zero_one_eint_neq:
  "\<not> 0 = (1::eint)"
  "\<not> 1 = (0::eint)"
  unfolding zero_eint_def one_eint_def by simp_all

lemma infinity_ne_i1 [simp]: "(\<infinity>::eint) \<noteq> 1"
  by (simp add: one_eint_def)

lemma i1_ne_infinity [simp]: "1 \<noteq> (\<infinity>::eint)"
  by (simp add: one_eint_def)
 
subsection \<open>Addition\<close>

instantiation eint :: comm_monoid_add
begin

definition [nitpick_simp]:
  "m + n = (case m of \<infinity> \<Rightarrow> \<infinity> | eint m \<Rightarrow> (case n of \<infinity> \<Rightarrow> \<infinity> | eint n \<Rightarrow> eint (m + n)))"

lemma plus_eint_simps [simp, code]:
  fixes q :: eint
  shows "eint m + eint n = eint (m + n)"
    and "\<infinity> + q = \<infinity>"
    and "q + \<infinity> = \<infinity>"
  by (simp_all add: plus_eint_def split: eint.splits)

instance
proof
  fix n m q :: eint
  show "n + m + q = n + (m + q)"
    by (cases n m q rule: eint3_cases) auto
  show "n + m = m + n"
    by (cases n m rule: eint2_cases) auto
  show "0 + n = n"
    by (cases n) (simp_all add: zero_eint_def)
qed

end

lemma eSuc_eint: "(eint n) + 1 = eint (n + 1)"
  by (simp add: one_eint_def)

lemma eSuc_infinity [simp]: " \<infinity> + (1::eint) = \<infinity>"
  unfolding plus_eint_def 
  by auto 

lemma eSuc_inject [simp]: " m + (1::eint)=  n + 1 \<longleftrightarrow> m = n"
  unfolding plus_eint_def 
  apply(cases "m = \<infinity>")
  apply (metis (no_types, lifting) eSuc_eint 
    eint.distinct(2) eint.exhaust eint.simps(4) eint.simps(5) plus_eint_def)
  apply(cases "n = \<infinity>")
  using eSuc_eint plus_eint_def apply auto[1]
  unfolding one_eint_def 
  using add.commute eSuc_eint 
  by auto
     
lemma eSuc_eint_iff: "x + 1 = eint y \<longleftrightarrow> (\<exists>n. y = n + 1 \<and> x = eint n)"
  apply(cases "x = \<infinity>")
  apply simp
  unfolding plus_eint_def one_eint_def 
  using eSuc_eint 
  by auto

lemma enat_eSuc_iff: "eint y = x + 1 \<longleftrightarrow> (\<exists>n. y = n + 1 \<and> eint n = x)"
  using eSuc_eint_iff 
  by metis

lemma iadd_Suc: "((m::eint) + 1) + n = (m + n) + 1"
  by (metis ab_semigroup_add_class.add_ac(1) add.assoc add.commute)
  

lemma iadd_Suc_right: "(m::eint) + (n + 1) = (m + n) + 1"
  using add.assoc[of m n 1] by auto 

subsection \<open>Multiplication\<close>

instantiation eint :: "{comm_semiring}"
begin

definition times_eint_def [nitpick_simp]:
  "m * n = (case m of \<infinity> \<Rightarrow>  \<infinity> | eint m \<Rightarrow>
    (case n of \<infinity> \<Rightarrow> \<infinity> | eint n \<Rightarrow> eint (m * n)))"

lemma times_eint_simps [simp, code]:
  "eint m * eint n = eint (m * n)"
  "\<infinity> * \<infinity> = (\<infinity>::eint)"
  "\<infinity> * eint n = \<infinity>"
  "eint m * \<infinity> = \<infinity>"
  unfolding times_eint_def zero_eint_def
  by (simp_all split: eint.split)

lemma sum_infinity_imp_summand_infinity:
  assumes "a + b = (\<infinity>::eint)"
  shows "a = \<infinity> \<or> b = \<infinity>"
  using assms 
  by (metis  not_eint_eq plus_eint_simps(1))

lemma sum_finite_imp_summands_finite:
  assumes "a + b \<noteq> (\<infinity>::eint)"
  shows "a \<noteq> \<infinity>" "b \<noteq> \<infinity>"
  using assms eint.simps(5) apply fastforce
  using assms eint.simps(5) by fastforce


instance
proof
  fix a b c :: eint
  show "(a * b) * c = a * (b * c)"
    unfolding times_eint_def zero_eint_def
    by (simp split: eint.split)
  show comm: "a * b = b * a"
    unfolding times_eint_def zero_eint_def
    by (simp split: eint.split)
  show distr: "(a + b) * c = a * c + b * c"
    unfolding times_eint_def plus_eint_def 
    apply(cases "a + b = \<infinity>")
    apply(cases "a = \<infinity>")
    apply simp
    using sum_infinity_imp_summand_infinity[of a b] 
    apply (metis eint.simps(5) plus_eint_def plus_eint_simps(3))
    apply(cases "c = \<infinity>")
     apply (metis eint.exhaust plus_eint_def plus_eint_simps(3) times_eint_def times_eint_simps(4))
    using sum_finite_imp_summands_finite[of a b] 
    apply auto 
    by (simp add: semiring_normalization_rules(1))
qed    


end

lemma mult_one_right[simp]:
"(n::eint)*1 = n"
  apply(cases "n = \<infinity>")
  apply (simp add: one_eint_def)
  by (metis eint2_cases mult_cancel_left2 one_eint_def times_eint_simps(1))

lemma mult_one_left[simp]:
"1*(n::eint) = n"
  by (metis mult.commute mult_one_right)

lemma mult_eSuc: "((m::eint) + 1) * n = m * n + n"
  by (simp add: distrib_right)
 
lemma mult_eSuc': "((m::eint) + 1) * n = n + m * n"
  using mult_eSuc add.commute by simp 

lemma mult_eSuc_right: "(m::eint) * (n + 1) =  m * n +  m "
  by(simp add: distrib_left)

lemma mult_eSuc_right': "(m::eint) * (n + 1) =  m + m * n  "
  using mult_eSuc_right add.commute by simp 


subsection \<open>Numerals\<close>

lemma numeral_eq_eint:
  "numeral k = eint (numeral k)"
  by simp

lemma eint_numeral [code_abbrev]:
  "eint (numeral k) = numeral k"
  using numeral_eq_eint ..

lemma infinity_ne_numeral [simp]: "(\<infinity>::eint) \<noteq> numeral k"
  by auto

lemma numeral_ne_infinity [simp]: "numeral k \<noteq> (\<infinity>::eint)"
  by simp
  
subsection \<open>Subtraction\<close>

instantiation eint :: minus
begin

definition diff_eint_def:
"a - b = (case a of (eint x) \<Rightarrow> (case b of (eint y) \<Rightarrow> eint (x - y) | \<infinity> \<Rightarrow> \<infinity>)
          | \<infinity> \<Rightarrow> \<infinity>)"

instance ..

end




lemma idiff_eint_eint [simp, code]: "eint a - eint b = eint (a - b)"
  by (simp add: diff_eint_def)

lemma idiff_infinity [simp, code]: "\<infinity> - n = (\<infinity>::eint)"
  by (simp add: diff_eint_def)

lemma idiff_infinity_right [simp, code]: "eint a - \<infinity> = \<infinity>"
  by (simp add: diff_eint_def)

lemma idiff_0 [simp]: "(0::eint) - n = -n"
  by (cases n, simp_all add: zero_eint_def)

lemmas idiff_eint_0 [simp] = idiff_0 [unfolded zero_eint_def]

lemma idiff_0_right [simp]: "(n::eint) - 0 = n"
  by (cases n) (simp_all add: zero_eint_def)

lemmas idiff_eint_0_right [simp] = idiff_0_right [unfolded zero_eint_def]

lemma idiff_self [simp]: "n \<noteq> \<infinity> \<Longrightarrow> (n::eint) - n = 0"
  by (auto simp: zero_eint_def)


lemma eSuc_minus_eSuc [simp]: "((n::eint) + 1) - (m + 1) = n - m"
  apply(cases "n = \<infinity>")
  apply simp 
  apply(cases "m = \<infinity>")
  apply (metis eSuc_infinity eint.exhaust idiff_infinity_right infinity_ne_i1 sum_infinity_imp_summand_infinity)
proof-
  assume A: "n \<noteq>\<infinity>" "m \<noteq> \<infinity>"
  obtain a where a_def: "n = eint a"
    using A 
    by auto
  obtain b where b_def: "m = eint b"
    using A 
    by auto 
  show ?thesis 
    using  idiff_eint_eint[of "a + 1" "b + 1"]
           idiff_eint_eint[of a b]
  by (simp add: a_def b_def eSuc_eint)
qed
  
lemma eSuc_minus_1 [simp]: "((n::eint)+ 1) - 1 = n"
  using eSuc_minus_eSuc[of n 0]
  by auto 


(*lemmas idiff_self_eq_0_eint = idiff_self_eq_0[unfolded zero_eint_def]*)

subsection \<open>Ordering\<close>

instantiation eint :: linordered_ab_semigroup_add
begin

definition [nitpick_simp]:
  "m \<le> n = (case n of eint n1 \<Rightarrow> (case m of eint m1 \<Rightarrow> m1 \<le> n1 | \<infinity> \<Rightarrow> False)
    | \<infinity> \<Rightarrow> True)"

definition [nitpick_simp]:
  "m < n = (case m of eint m1 \<Rightarrow> (case n of eint n1 \<Rightarrow> m1 < n1 | \<infinity> \<Rightarrow> True)
    | \<infinity> \<Rightarrow> False)"

lemma eint_ord_simps [simp]:
  "eint m \<le> eint n \<longleftrightarrow> m \<le> n"
  "eint m < eint n \<longleftrightarrow> m < n"
  "q \<le> (\<infinity>::eint)"
  "q < (\<infinity>::eint) \<longleftrightarrow> q \<noteq> \<infinity>"
  "(\<infinity>::eint) \<le> q \<longleftrightarrow> q = \<infinity>"
  "(\<infinity>::eint) < q \<longleftrightarrow> False"
  by (simp_all add: less_eq_eint_def less_eint_def split: eint.splits)

lemma numeral_le_eint_iff[simp]:
  shows "numeral m \<le> eint n \<longleftrightarrow> numeral m \<le> n"
  by auto

lemma numeral_less_eint_iff[simp]:
  shows "numeral m < eint n \<longleftrightarrow> numeral m < n"
  by simp

lemma eint_ord_code [code]:
  "eint m \<le> eint n \<longleftrightarrow> m \<le> n"
  "eint m < eint n \<longleftrightarrow> m < n"
  "q \<le> (\<infinity>::eint) \<longleftrightarrow> True"
  "eint m < \<infinity> \<longleftrightarrow> True"
  "\<infinity> \<le> eint n \<longleftrightarrow> False"
  "(\<infinity>::eint) < q \<longleftrightarrow> False"
  by simp_all

lemma eint_ord_plus_one[simp]:
  assumes "eint n \<le> x"
  assumes "x < y"
  shows "eint (n + 1) \<le> y"
proof-
  obtain m where "x = eint m"
    using assms(2) 
    by fastforce
  show ?thesis apply(cases "y = \<infinity>")
  apply simp
    using \<open>x = eint m\<close> assms(1) assms(2) 
    by force
qed

instance
  by standard (auto simp add: less_eq_eint_def less_eint_def plus_eint_def split: eint.splits)

end

instance eint :: "{strict_ordered_comm_monoid_add}"
proof
  show "a < b \<Longrightarrow> c < d \<Longrightarrow> a + c < b + d" for a b c d :: eint
    by (cases a b c d rule: eint2_cases[case_product eint2_cases]) auto
qed 

(* BH: These equations are already proven generally for any type in
class linordered_semidom. However, eint is not in that class because
it does not have the cancellation property. Would it be worthwhile to
a generalize linordered_semidom to a new class that includes eint? *)

lemma add_diff_assoc_eint: "z \<le> y \<Longrightarrow> x + (y - z) = x + y - (z::eint)"
by(cases x)(auto simp add: diff_eint_def split: eint.split)

lemma eint_ord_number [simp]:
  "(numeral m :: eint) \<le> numeral n \<longleftrightarrow> (numeral m :: nat) \<le> numeral n"
  "(numeral m :: eint) < numeral n \<longleftrightarrow> (numeral m :: nat) < numeral n"
  apply simp 
  by simp

lemma infinity_ileE [elim!]: "\<infinity> \<le> eint m \<Longrightarrow> R"
  by simp  

lemma infinity_ilessE [elim!]: "\<infinity> < eint m \<Longrightarrow> R"
  by simp

lemma imult_infinity: "(0::eint) < n \<Longrightarrow> \<infinity> * n = \<infinity>"
  by (simp add: zero_eint_def less_eint_def split: eint.splits)

lemma imult_infinity_right: "(0::eint) < n \<Longrightarrow> n * \<infinity> = \<infinity>"
  by (simp add: zero_eint_def less_eint_def split: eint.splits)

lemma min_eint_simps [simp]:
  "min (eint m) (eint n) = eint (min m n)"
  "min q (\<infinity>::eint) = q"
  "min (\<infinity>::eint) q = q"
  by (auto simp add: min_def)

lemma max_eint_simps [simp]:
  "max (eint m) (eint n) = eint (max m n)"
  "max q \<infinity> = (\<infinity>::eint)"
  "max \<infinity> q = (\<infinity>::eint)"
  by (simp_all add: max_def)

lemma eint_ile: "n \<le> eint m \<Longrightarrow> \<exists>k. n = eint k"
  by (cases n) simp_all

lemma eint_iless: "n < eint m \<Longrightarrow> \<exists>k. n = eint k"
  by (cases n) simp_all

lemma iadd_le_eint_iff:
  "x + y \<le> eint n \<longleftrightarrow> (\<exists>y' x'. x = eint x' \<and> y = eint y' \<and> x' + y' \<le> n)"
by(cases x y rule: eint.exhaust[case_product eint.exhaust]) simp_all

lemma chain_incr: "\<forall>i. \<exists>j. Y i < Y j \<Longrightarrow> \<exists>j. eint k < Y j"
proof-
  assume A: "\<forall>i. \<exists>j. Y i < Y j"
  then have "\<forall>i. \<exists>n::int. Y i = eint n"
    by (metis eint.exhaust eint_ord_simps(6))
  then obtain i n where in_def: "Y (i::'a) = eint n"
    by blast 
  show "\<exists>j. eint k < Y j"
  proof(rule ccontr)
    assume C: "\<not>(\<exists>j. eint k < Y j)"
    then have C':"\<forall>j. Y j \<le> eint k"
      using le_less_linear 
      by blast
    then have "Y (i::'a) \<le> eint k"
      by simp     
    have "\<And>m::nat. \<exists>j::'a. Y j \<ge> eint (n + int m)"
    proof- fix m
      show "\<exists>j::'a. Y j \<ge> eint (n + int m)"
        apply(induction m)
         apply (metis in_def int_ops(1) order_refl plus_int_code(1))
      proof- fix m
        assume "\<exists>j. eint (n + int m) \<le> Y j"
        then obtain j where j_def: "eint (n + int m) \<le> Y j"
          by blast 
        obtain j' where j'_def: "Y j < Y j'"
          using A by blast 
        have "eint (n + int (Suc m)) = eint (n + m + 1)"
          by auto
        then have "eint (n + int (Suc m)) \<le> Y j'"
          using j_def j'_def  eint_ord_plus_one[of "n + m" "Y j" "Y j'"]
          by presburger
        then show "\<exists>j. eint (n + int (Suc m)) \<le> Y j" 
          by blast 
      qed
    qed
    then show False 
      by (metis A C \<open>Y i \<le> eint k\<close>   eint_ord_simps(1) in_def 
          order.not_eq_order_implies_strict zle_iff_zadd)
  qed
qed

lemma eint_ord_Suc:
  assumes "(x::eint) < y"
  shows "x + 1 < y + 1"
  apply(cases "y = \<infinity>")
  using assms i1_ne_infinity sum_infinity_imp_summand_infinity 
   apply fastforce
  by (metis add_mono_thms_linordered_semiring(3) assms eSuc_inject order_less_le)

lemma eSuc_ile_mono [simp]: "(n::eint) + 1 \<le> m+ 1 \<longleftrightarrow> n \<le> m"
  by (meson add_mono_thms_linordered_semiring(3) eint_ord_Suc linorder_not_le)

lemma eSuc_mono [simp]: "(n::eint) + 1 < m+ 1 \<longleftrightarrow> n < m"
  by (meson add_mono_thms_linordered_semiring(3) eint_ord_Suc linorder_not_le)

lemma ile_eSuc [simp]: "(n::eint) \<le> n + 1"
  by (metis add.right_neutral add_left_mono eint_1_iff(2) eint_ord_code(1) linear not_one_le_zero zero_eint_def)

lemma ileI1: "(m::eint) < n \<Longrightarrow> m + 1 \<le> n"
  by (metis eSuc_eint eint.exhaust eint_ex_split eint_iless eint_ord_Suc eint_ord_code(6) 
      eint_ord_plus_one eint_ord_simps(3) less_le_trans linear )
 
lemma Suc_ile_eq: "eint (m +1) \<le> n \<longleftrightarrow> eint m < n"
  by (cases n) auto

lemma iless_Suc_eq [simp]: "eint m < n + 1 \<longleftrightarrow> eint m \<le> n"
  by (metis Suc_ile_eq eSuc_eint eSuc_ile_mono)

lemma eSuc_max: "(max (x::eint) y) + 1 = max (x+1) (y+1)"
  by (simp add: max_def)

lemma eSuc_Max:
  assumes "finite A" "A \<noteq> ({}::eint set)"
  shows " (Max A) + 1 = Max ((+)1 ` A)"
using assms proof induction
  case (insert x A)
  thus ?case 
    using Max_insert[of A x] Max_singleton[of x] add.commute[of 1] eSuc_max finite_imageI 
          image_insert image_is_empty
  by (simp add: add.commute hom_Max_commute)
qed simp

instantiation eint :: "{order_top}"
begin

definition top_eint :: eint where "top_eint = \<infinity>"

instance
  by standard (simp add: top_eint_def)

end

lemma finite_eint_bounded:
  assumes le_fin: "\<And>y. y \<in> A \<Longrightarrow> eint m \<le> y \<and> y \<le> eint n"
  shows "finite A"
proof (rule finite_subset)
  show "finite (eint ` {m..n})" by blast
  have "A \<subseteq> {eint m..eint n}" using le_fin by fastforce
  also have "\<dots> \<subseteq> eint ` {m..n}"
    apply (rule subsetI)
    subgoal for x by (cases x) auto
    done
  finally show "A \<subseteq> eint ` {m..n}" .
qed


subsection \<open>Cancellation simprocs\<close>

lemma add_diff_cancel_eint[simp]: "x \<noteq> \<infinity> \<Longrightarrow> x + y - x = (y::eint)"
by (metis add.commute add.right_neutral add_diff_assoc_eint idiff_self order_refl)

lemma eint_add_left_cancel: "a + b = a + c \<longleftrightarrow> a = (\<infinity>::eint) \<or> b = c"
  unfolding plus_eint_def by (simp split: eint.split)

lemma eint_add_left_cancel_le: "a + b \<le> a + c \<longleftrightarrow> a = (\<infinity>::eint) \<or> b \<le> c"
  unfolding plus_eint_def by (simp split: eint.split)

lemma eint_add_left_cancel_less: "a + b < a + c \<longleftrightarrow> a \<noteq> (\<infinity>::eint) \<and> b < c"
  unfolding plus_eint_def by (simp split: eint.split)

lemma plus_eq_infty_iff_eint: "(m::eint) + n = \<infinity> \<longleftrightarrow> m=\<infinity> \<or> n=\<infinity>"
using eint_add_left_cancel by fastforce

ML \<open>
structure Cancel_Enat_Common =
struct
  (* copied from src/HOL/Tools/nat_numeral_simprocs.ML *)
  fun find_first_t _    _ []         = raise TERM("find_first_t", [])
    | find_first_t past u (t::terms) =
          if u aconv t then (rev past @ terms)
          else find_first_t (t::past) u terms

  fun dest_summing (Const (\<^const_name>\<open>Groups.plus\<close>, _) $ t $ u, ts) =
        dest_summing (t, dest_summing (u, ts))
    | dest_summing (t, ts) = t :: ts

  val mk_sum = Arith_Data.long_mk_sum
  fun dest_sum t = dest_summing (t, [])
  val find_first = find_first_t []
  val trans_tac = Numeral_Simprocs.trans_tac
  val norm_ss =
    simpset_of (put_simpset HOL_basic_ss \<^context>
      addsimps @{thms ac_simps add_0_left add_0_right})
  fun norm_tac ctxt = ALLGOALS (simp_tac (put_simpset norm_ss ctxt))
  fun simplify_meta_eq ctxt cancel_th th =
    Arith_Data.simplify_meta_eq [] ctxt
      ([th, cancel_th] MRS trans)
  fun mk_eq (a, b) = HOLogic.mk_Trueprop (HOLogic.mk_eq (a, b))
end

structure Eq_Enat_Cancel = ExtractCommonTermFun
(open Cancel_Enat_Common
  val mk_bal = HOLogic.mk_eq
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>HOL.eq\<close> \<^typ>\<open>eint\<close>
  fun simp_conv _ _ = SOME @{thm eint_add_left_cancel}
)

structure Le_Enat_Cancel = ExtractCommonTermFun
(open Cancel_Enat_Common
  val mk_bal = HOLogic.mk_binrel \<^const_name>\<open>Orderings.less_eq\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Orderings.less_eq\<close> \<^typ>\<open>eint\<close>
  fun simp_conv _ _ = SOME @{thm eint_add_left_cancel_le}
)

structure Less_Enat_Cancel = ExtractCommonTermFun
(open Cancel_Enat_Common
  val mk_bal = HOLogic.mk_binrel \<^const_name>\<open>Orderings.less\<close>
  val dest_bal = HOLogic.dest_bin \<^const_name>\<open>Orderings.less\<close> \<^typ>\<open>eint\<close>
  fun simp_conv _ _ = SOME @{thm eint_add_left_cancel_less}
)
\<close>

simproc_setup eint_eq_cancel
  ("(l::eint) + m = n" | "(l::eint) = m + n") =
  \<open>fn phi => fn ctxt => fn ct => Eq_Enat_Cancel.proc ctxt (Thm.term_of ct)\<close>

simproc_setup eint_le_cancel
  ("(l::eint) + m \<le> n" | "(l::eint) \<le> m + n") =
  \<open>fn phi => fn ctxt => fn ct => Le_Enat_Cancel.proc ctxt (Thm.term_of ct)\<close>

simproc_setup eint_less_cancel
  ("(l::eint) + m < n" | "(l::eint) < m + n") =
  \<open>fn phi => fn ctxt => fn ct => Less_Enat_Cancel.proc ctxt (Thm.term_of ct)\<close>

text \<open>TODO: add regression tests for these simprocs\<close>

text \<open>TODO: add simprocs for combining and cancelling numerals\<close>

subsection \<open>Well-ordering\<close>

lemma less_eintE:
  "[| n < eint m; !!k. n = eint k ==> k < m ==> P |] ==> P"
by (induct n) auto

lemma less_infinityE:
  "[| n < \<infinity>; !!k. n = eint k ==> P |] ==> P"
by (induct n) auto


subsection \<open>Traditional theorem names\<close>

lemmas eint_defs = zero_eint_def one_eint_def 
  plus_eint_def less_eq_eint_def less_eint_def

instantiation eint :: uminus
begin

definition 
"- b = (case b of \<infinity> \<Rightarrow> \<infinity> | eint m \<Rightarrow> eint (-m))"

lemma eint_uminus_eq:
"(a::eint) + (-a) = a - a"
  apply(induction a)
  apply (simp add: uminus_eint_def)
  by simp




instance..
end

section\<open>Additional Lemmas (Useful for the Proof of Hensel's Lemma)\<close>

lemma eint_mult_mono:
  assumes "(c::eint) > 0 \<and> c \<noteq> \<infinity>"
  assumes "k > n"
  shows "k*c > n*c"  
  using assms apply(induction k, induction n, induction c)
  by(auto simp add: zero_eint_def)

lemma eint_mult_mono':
  assumes "(c::eint) \<ge> 0 \<and> c \<noteq> \<infinity>"
  assumes "k > n"
  shows "k*c \<ge> n*c"  
  apply(cases "c = 0")
   apply (metis add.right_neutral assms(2) eint_add_left_cancel eint_ord_code(3) 
         eint_ord_simps(4) eq_iff less_le_trans mult.commute mult_eSuc_right' 
         mult_one_right not_less times_eint_simps(4) zero_eint_def)
    using assms eint_mult_mono 
    by (simp add: le_less)

lemma eint_minus_le:
  assumes "(b::eint) < c"
  shows "c - b > 0"
  using assms apply(induction b, induction c) 
  by (auto simp add: zero_eint_def)  

lemma eint_nat_times:
  assumes "(c::eint) > 0"
  shows "(Suc n)*(c::eint) > 0"
  using assms  apply(induction c)
  apply (simp add: zero_eint_def)
  by simp

lemma eint_pos_times_is_pos:
  assumes "(c::eint) > 0"
  assumes "b > 0"
  shows "b*c > 0"
  using assms apply(induction c, induction b)
  by(auto simp add: zero_eint_def imult_infinity_right)

lemma eint_nat_is_pos:
"eint (Suc n) > 0"
  by (simp add: zero_eint_def)

lemma eint_pow_int_is_pos:
  assumes "n > 0"
  shows "eint n > 0"
  using assms by (simp add: zero_eint_def)

lemma eint_nat_times':
  assumes "(c::eint) \<ge> 0"
  shows "(Suc n)*c \<ge> 0"  
  using assms zero_eint_def by fastforce

lemma eint_pos_int_times_ge:
  assumes "(c::eint) \<ge> 0"
  assumes "n > 0"
  shows "eint n * c \<ge> c"
  using assms apply(induction c)
  apply (smt eSuc_eint eint.distinct(2) eint_mult_mono' eint_pow_int_is_pos eq_iff ileI1 less_le mult.commute mult_one_right one_eint_def zero_eint_def)
  by simp

lemma eint_pos_int_times_gt:
  assumes "(c::eint) > 0"
  assumes "c \<noteq>\<infinity>"
  assumes "n > 1"
  shows "eint n * c > c"
  using assms eint_mult_mono[of c 1 "eint n"]
  by (metis eint_ord_simps(2) mult_one_left one_eint_def)

lemma eint_add_cancel_fact[simp]:
  assumes "(c::eint) \<noteq> \<infinity>"
  shows "c + (b - c) = b"
  using assms apply(induction c, induction b)
  by auto 

lemma nat_mult_not_infty[simp]:
  assumes "c \<noteq> \<infinity>"
  shows "(eint n) * c \<noteq> \<infinity>"
  using assms by auto

lemma eint_minus_distl:
  assumes "(b::eint) \<noteq> d"
  shows "b*c - d*c = (b-d)*c"
  using assms apply(induction c, induction b, induction d)
  apply (metis add_diff_cancel_eint distrib_right eint.distinct(2) eint_add_cancel_fact nat_mult_not_infty)
    apply simp
      apply simp
        by (simp add: mult.commute times_eint_def)    

lemma eint_minus_distr:
  assumes "(b::eint) \<noteq> d"
  shows "c*(b - d) = c*b - c*d"
  by (metis assms eint_minus_distl mult.commute)  

lemma eint_int_minus_distr:
"(eint n)*c - (eint m)*c = eint (n - m) * c"
  by (metis add.right_neutral distrib_right eint_add_left_cancel eint_minus_distl idiff_eint_eint
      idiff_infinity idiff_self infinity_ne_i0 nat_mult_not_infty not_eint_eq times_eint_simps(4))

lemma eint_2_minus_1_mult[simp]:
"2*(b::eint) - b = b"
proof -
  have "\<forall>e. (\<infinity>::eint) * e = \<infinity>"
  by (simp add: times_eint_def)
  then show ?thesis
    by (metis add_diff_cancel_eint idiff_infinity mult.commute mult_eSuc_right' mult_one_right one_add_one one_eint_def plus_eint_simps(1))
qed

lemma eint_minus_comm:
"(d::eint) + b - c = d - c + b"
apply(induction c )
  apply (metis add.assoc add_diff_cancel_eint eint.distinct(2) eint_add_cancel_fact)
    apply(induction d)
    apply (metis distrib_left eint2_cases eint_minus_distl i1_ne_infinity idiff_infinity_right 
           mult_one_left plus_eq_infty_iff_eint sum_infinity_imp_summand_infinity times_eint_simps(3))
      apply(induction b)
        apply simp
          by simp

lemma ge_plus_pos_imp_gt:
  assumes "(c::eint) \<noteq>\<infinity>"
  assumes "(b::eint) > 0"
  assumes "d \<ge> c + b"
  shows "d > c"
  using assms apply(induction d, induction c)
  apply (metis add.comm_neutral assms(2) eint_add_left_cancel_less less_le_trans)
   apply blast
    by simp

lemma eint_minus_ineq:
  assumes "(c::eint) \<noteq>\<infinity>"
  assumes "b \<ge> d"
  shows "b - c \<ge> d - c"
  by (metis add_left_mono antisym assms(1) assms(2) eint_add_cancel_fact linear)

lemma eint_minus_ineq':
  assumes "(c::eint) \<noteq>\<infinity>"
  assumes "b \<ge> d"
  assumes "(e::eint) > 0"
  assumes "e \<noteq> \<infinity>"
  shows "e*(b - c) \<ge> e*(d - c)"
  using assms eint_minus_ineq 
  by (metis eint_mult_mono' eq_iff less_le mult.commute)

lemma eint_minus_ineq'':
  assumes "(c::eint) \<noteq>\<infinity>"
  assumes "b \<ge> d"
  assumes "(e::eint) > 0"
  assumes "e \<noteq> \<infinity>"
  shows "e*(b - c) \<ge> e*d - e*c"
  using assms eint_minus_ineq' 
  proof -
    have "\<forall>e. (0::eint) + e = e"
      by simp
    then have f1: "e * 0 = 0"
      by (metis add_diff_cancel_eint assms(4) idiff_self mult_eSuc_right' mult_one_right)
    have "\<infinity> \<noteq> c * e"
      using assms(1) assms(4) eint_pos_times_is_pos by auto
    then show ?thesis
      using f1 by (metis assms(1) assms(2) assms(3) assms(4) eint_minus_distl eint_minus_ineq' idiff_self mult.commute)
  qed

lemma eint_min_ineq:
  assumes "(b::eint) \<ge> min c d"
  assumes "c > e"
  assumes "d > e"
  shows "b > e"
  by (meson assms(1) assms(2) assms(3) less_le_trans min_le_iff_disj)

lemma eint_plus_times:
  assumes "(d::eint) \<ge> 0"
  assumes "(b::eint) \<ge> c + (eint k)*d"
  assumes "k \<ge> l"
  shows "b \<ge> c + l*d" 
proof-
  have "k*d \<ge> l*d"
    by (smt assms(1) assms(3) eint_mult_mono' eint_ord_simps(2) eq_iff times_eint_simps(4))
  thus ?thesis 
    by (meson add_mono_thms_linordered_semiring(2) assms(2) order_subst2)
qed
end

