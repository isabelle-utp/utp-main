(*Author: Angeliki Koutsoukou-Argyraki, University of Cambridge.
Date: 3 August 2020.

text\<open>This is a formalisation of Amicable Numbers, involving some relevant material including
Euler's sigma function, some relevant definitions, results and examples as well as rules such as
Th\={a}bit ibn Qurra's Rule, Euler's Rule, te Riele's Rule and Borho's Rule with breeders.\<close>*)

theory "Amicable_Numbers"
  imports "HOL-Number_Theory.Number_Theory"
   "HOL-Computational_Algebra.Computational_Algebra"
   Pratt_Certificate.Pratt_Certificate_Code
   Polynomial_Factorization.Prime_Factorization

begin

section\<open>Miscellaneous\<close>

lemma mult_minus_eq_nat: 
  fixes  x::nat and y ::nat and z::nat
  assumes " x+y = z"
  shows " -x-y = -z "
  using assms by linarith

lemma minus_eq_nat_subst: fixes A::nat and B::nat and  C::nat and  D::nat and  E::nat
  assumes "A = B-C-D" and " -E = -C-D"
  shows " A = B-E"
  using assms by linarith

lemma minus_eq_nat_subst_order:  fixes  A::nat and  B::nat  and  C::nat  and  D::nat  and   E::nat
  assumes "B-C-D > 0" and "A = B-C-D+B"  shows "A = 2*B-C-D"
   using assms by auto

lemma auxiliary_ineq: fixes x::nat assumes "x \<ge> (2::nat)"
  shows " x+1 < (2::nat)*x"
  using assms by linarith

(* TODO The following three auxiliary lemmas are by Lawrence Paulson. To be added to the library. *)

lemma sum_strict_mono:
  fixes A :: "nat set"
  assumes "finite B" "A \<subset> B" "0 \<notin> B"
  shows "\<Sum> A < \<Sum> B"
proof -
  have "B - A \<noteq> {}"
    using assms(2) by blast
  with assms DiffE have "\<Sum> (B-A) > 0"
    by fastforce
  moreover have "\<Sum> B = \<Sum> A + \<Sum> (B-A)"
    by (metis add.commute assms(1) assms(2) psubsetE sum.subset_diff)
  ultimately show ?thesis
    by linarith
qed

lemma sum_image_eq:
  assumes "inj_on f A"
  shows "\<Sum> (f ` A) = (\<Sum> i \<in> A. f i)"
  using assms sum.reindex_cong by fastforce

lemma coprime_dvd_aux:
  assumes "gcd m n = Suc 0" "na dvd n" "ma dvd m" "mb dvd m" "nb dvd n" and eq: "ma * na = mb * nb"
  shows "ma = mb"
proof -
  have "gcd na mb = 1"
    using assms by (metis One_nat_def gcd.commute gcd_nat.mono is_unit_gcd_iff)
  moreover have "gcd nb ma = 1"
    using assms by (metis One_nat_def gcd.commute gcd_nat.mono is_unit_gcd_iff)
  ultimately show "ma = mb"
    by (metis eq gcd_mult_distrib_nat mult.commute nat_mult_1_right)
qed

section\<open>Amicable Numbers\<close>

subsection\<open>Preliminaries\<close>

definition divisor :: "nat \<Rightarrow>nat \<Rightarrow> bool"  (infixr "divisor" 80)
  where "n divisor m \<equiv>(n \<ge> 1 \<and> n \<le> m \<and> n dvd m)"

definition divisor_set: "divisor_set m = {n. n divisor m}"

lemma def_equiv_divisor_set: "divisor_set (n::nat) = set(divisors_nat n)"
  using  divisors_nat_def divisors_nat divisor_set divisor_def by auto

definition proper_divisor :: "nat \<Rightarrow>nat \<Rightarrow> bool"  (infixr "properdiv" 80)
  where "n properdiv m \<equiv>(n \<ge> 1 \<and> n < m \<and> n dvd m)"

definition properdiv_set: "properdiv_set m = {n. n properdiv m}"

lemma example1_divisor: shows "(2::nat) \<in> divisor_set (4::nat)"
 using  divisor_set divisor_def by force

lemma example2_properdiv_set: "properdiv_set (Suc (Suc (Suc 0))) = {(1::nat)}"
   by (auto simp: properdiv_set proper_divisor_def less_Suc_eq dvd_def; presburger)

lemma divisor_set_not_empty: fixes m::nat assumes "m \<ge>1"
  shows "m \<in> divisor_set m"
using assms divisor_set divisor_def by force

lemma finite_divisor_set [simp]: "finite(divisor_set n)"
  using divisor_def divisor_set by simp

lemma finite_properdiv_set[simp]: shows "finite(properdiv_set m)"
  using  properdiv_set proper_divisor_def by simp

lemma divisor_set_mult:
  "divisor_set  (m*n) = {i*j| i j. (i \<in> divisor_set m)\<and>(j \<in> divisor_set n)}"
  using divisor_set divisor_def
  by (fastforce simp add: divisor_set divisor_def dest: division_decomp)

lemma divisor_set_1 [simp]: "divisor_set (Suc 0) = {Suc 0}"
  by (simp add: divisor_set divisor_def cong: conj_cong)

lemma divisor_set_one: shows "divisor_set 1 ={1}"
  using divisor_set  divisor_def by auto

lemma union_properdiv_set: assumes "n\<ge>1" shows "divisor_set n =(properdiv_set n)\<union>{n}"
 using divisor_set properdiv_set  proper_divisor_def assms  divisor_def by auto

lemma prime_div_set: assumes "prime n" shows "divisor_set n = {n, 1}"
  using divisor_def assms divisor_set  prime_nat_iff by auto

lemma div_set_prime:
  assumes "prime n"
  shows "properdiv_set n = {1}"
   using assms properdiv_set prime_nat_iff proper_divisor_def
  by (metis (no_types, lifting) Collect_cong One_nat_def divisor_def divisor_set divisor_set_one
 dvd_1_left empty_iff insert_iff mem_Collect_eq order_less_irrefl)

lemma prime_gcd: fixes m::nat and n::nat assumes "prime m" and "prime n"
and "m \<noteq> n" shows "gcd m n =1 " using prime_def
  by (simp add: assms primes_coprime)

text\<open>We refer to definitions from \cite{aliquotwiki}:\<close>

definition aliquot_sum :: "nat \<Rightarrow> nat"
  where "aliquot_sum n \<equiv> \<Sum>(properdiv_set n)"

definition deficient_number :: "nat \<Rightarrow> bool"
  where "deficient_number n \<equiv> (n > aliquot_sum n)"

definition abundant_number :: "nat \<Rightarrow> bool"
  where "abundant_number n \<equiv> (n < aliquot_sum n)"

definition perfect_number :: "nat \<Rightarrow> bool"
  where "perfect_number n \<equiv> (n = aliquot_sum n)"

lemma example_perfect_6: shows "perfect_number 6"

proof-
  have a: "set(divisors_nat 6) = {1, 2, 3, 6}" by eval
  have b: "divisor_set (6) = {1, 2, 3, 6}"
    using a  def_equiv_divisor_set by simp
  have  c: "properdiv_set (6) = {1, 2, 3}"
    using b union_properdiv_set properdiv_set proper_divisor_def by auto
  show ?thesis using aliquot_sum_def c
    by (simp add: numeral_3_eq_3 perfect_number_def)
qed


subsection\<open>Euler's sigma function and properties\<close>

text\<open>The sources of the following useful material on Euler's sigma function are \cite{garciaetal1},
\cite{garciaetal2}, \cite{sandifer} and \cite{escott}.\<close>

definition Esigma :: "nat \<Rightarrow> nat"
  where "Esigma n \<equiv> \<Sum>(divisor_set n)"

lemma Esigma_properdiv_set:
  assumes "m \<ge> 1"
  shows "Esigma m = (aliquot_sum m) + m"
  using assms divisor_set properdiv_set proper_divisor_def union_properdiv_set  Esigma_def
        aliquot_sum_def by fastforce

lemma Esigmanotzero:
  assumes "n \<ge> 1"
  shows "Esigma n \<ge> 1"
  using Esigma_def assms Esigma_properdiv_set by auto

lemma prime_sum_div:
  assumes "prime n"
  shows " Esigma n = n +(1::nat)"
proof -
  have "1 \<le> n"
    using assms prime_ge_1_nat by blast
  then show ?thesis using Esigma_properdiv_set assms div_set_prime
    by (simp add: Esigma_properdiv_set aliquot_sum_def assms div_set_prime)
qed

lemma sum_div_is_prime:
  assumes "Esigma n = n +(1::nat)" and "n \<ge>1"
  shows "prime n"
 
proof (rule ccontr)
  assume F: " \<not> (prime n)"
  have " n divisor n" using assms divisor_def by simp
  have " (1::nat) divisor n"using assms divisor_def by simp

  have "n \<noteq> Suc 0"
    using Esigma_def assms(1) by auto
  then have r: " \<exists>( m::nat). m \<in> divisor_set n \<and> m\<noteq> (1::nat) \<and> m \<noteq> n"
    using assms F
    apply (clarsimp simp add: Esigma_def divisor_set divisor_def prime_nat_iff)
    by (meson Suc_le_eq dvd_imp_le dvd_pos_nat)

  have "Suc n = \<Sum>{n,1}"
    by (simp add: \<open>n \<noteq> Suc 0\<close>)
  moreover
  have "divisor_set n \<supset> {n,1}"
    using assms divisor_set r \<open>1 divisor n\<close> divisor_set_not_empty by auto
  then have "\<Sum>(divisor_set n) > \<Sum>{n,1}"
     apply (rule sum_strict_mono [OF finite_divisor_set])
    by (simp add: divisor_def divisor_set)
  ultimately
  show False
    using Esigma_def assms(1) by presburger
qed

lemma Esigma_prime_sum:
  fixes k:: nat assumes "prime m" "k \<ge>1"
  shows "Esigma (m^k) =( m^(k+(1::nat)) -(1::nat)) /(m-1)"

proof-
  have "m > 1"
    using \<open>prime m\<close> prime_gt_1_nat by blast

  have A: " Esigma (m^k) =( \<Sum> j= 0..k.( m^j)) "
  proof-
    have AA: "divisor_set (m^k) = (\<lambda>j. m ^ j) ` {0..k}"
      using assms prime_ge_1_nat
      by (auto simp add: power_increasing prime_ge_Suc_0_nat divisor_set divisor_def image_iff
 divides_primepow_nat)

    have \<section>: "\<Sum> ((\<lambda>j. m ^ j) ` {..k}) = sum (\<lambda>j. m ^ j) {0..k}"  for k
    proof (induction k)
      case (Suc k)
      then show ?case
        apply (clarsimp simp: atMost_Suc)
        by (smt add.commute add_le_same_cancel1 assms(1) atMost_iff finite_atMost finite_imageI
image_iff le_zero_eq power_add power_one_right prime_power_inj sum.insert zero_neq_one)
    qed auto
    show ?thesis
      by (metis "\<section>" AA Esigma_def atMost_atLeast0)
  qed
  have B: "(\<Sum> i\<le>k.( m^i)) = ( m^Suc k -(1::nat)) /(m-(1::nat))"

    using assms \<open>m > 1\<close> Set_Interval.geometric_sum  [of m "Suc k"]
    apply (simp add: )
    by (metis One_nat_def lessThan_Suc_atMost nat_one_le_power of_nat_1 of_nat_diff of_nat_mult
of_nat_power one_le_mult_iff prime_ge_Suc_0_nat sum.lessThan_Suc)
  show ?thesis using A B assms
    by (metis Suc_eq_plus1 atMost_atLeast0 of_nat_1 of_nat_diff prime_ge_1_nat)
qed

lemma prime_Esigma_mult: assumes "prime m" and "prime n" and "m \<noteq> n"
  shows "Esigma (m*n) = (Esigma n)*(Esigma m)"

proof-
  have "m divisor (m*n)" using divisor_def assms
    by (simp add: dvd_imp_le prime_gt_0_nat)
  moreover have "\<not>(\<exists> k::nat. k divisor (m*n) \<and> k\<noteq>(1::nat)\<and> k \<noteq> m \<and> k \<noteq> n \<and> k\<noteq> m*n)"
    using assms unfolding divisor_def
    by (metis One_nat_def division_decomp nat_mult_1 nat_mult_1_right prime_nat_iff)
  ultimately have c: "divisor_set (m*n) = {m, n, m*n, 1}"
    using divisor_set assms  divisor_def by auto
  obtain "m\<noteq>1" "n\<noteq>1"
    using assms not_prime_1 by blast
  then have dd: "Esigma (m*n) = m + n +m *n +1"
    using assms by (simp add: Esigma_def c)
  then show ?thesis
    using prime_sum_div assms by simp
qed

lemma gcd_Esigma_mult:
  assumes "gcd m n = 1"
  shows "Esigma (m*n) = (Esigma m)*(Esigma n)"

proof-
  have "Esigma (m*n) = \<Sum> {i*j| i j. i \<in> divisor_set m \<and> j \<in> divisor_set n}"
    by (simp add: divisor_set_mult Esigma_def)
  also have "... = (\<Sum>i \<in> divisor_set m. \<Sum>j \<in> divisor_set n. i*j)"
  proof-
    have "inj_on (\<lambda>(i,j). i*j) (divisor_set m \<times> divisor_set n)"
      using assms
      apply (simp add: inj_on_def divisor_set divisor_def)
   by (metis assms coprime_dvd_aux mult_left_cancel not_one_le_zero)
  moreover have
"{i*j| i j. i \<in> divisor_set m \<and> j \<in> divisor_set n}= (\<lambda>(i,j). i*j)`(divisor_set m \<times> divisor_set n)"
      by auto
    ultimately show ?thesis
      by (simp add: sum.cartesian_product sum_image_eq)
  qed
  also have "... = \<Sum>( divisor_set m)* \<Sum>( divisor_set n)"
    by (simp add: sum_product)
  also have "... = Esigma m * Esigma n"
    by (simp add: Esigma_def)
  finally show ?thesis .
qed

lemma deficient_Esigma:
  assumes "Esigma m < 2*m" and "m \<ge>1"
  shows "deficient_number m"
  using Esigma_properdiv_set assms deficient_number_def by auto

lemma abundant_Esigma:
  assumes "Esigma m > 2*m" and "m \<ge>1" 
  shows "abundant_number m" 
  using Esigma_properdiv_set assms abundant_number_def by auto

lemma perfect_Esigma:
  assumes "Esigma m = 2*m" and "m \<ge>1" 
  shows "perfect_number m" 
 using Esigma_properdiv_set assms perfect_number_def by auto

subsection\<open>Amicable Numbers; definitions, some lemmas and examples\<close>

definition Amicable_pair :: "nat \<Rightarrow>nat \<Rightarrow> bool"  (infixr "Amic" 80)
  where "m Amic n \<equiv> ((m = aliquot_sum n) \<and> (n = aliquot_sum m)) "

lemma Amicable_pair_sym: fixes m::nat and n ::nat
  assumes "m Amic n " shows "n Amic m "
  using  Amicable_pair_def assms by blast

lemma Amicable_pair_equiv_def:
  assumes "(m Amic n)" and "m \<ge>1" and "n \<ge>1"
  shows   "(Esigma m = Esigma n)\<and>(Esigma m = m+n)"
  using assms Amicable_pair_def
  by (metis Esigma_properdiv_set add.commute)

lemma Amicable_pair_equiv_def_conv:
  assumes "m\<ge>1" and "n\<ge>1" and "(Esigma m = Esigma n)\<and>(Esigma m = m+n)"
  shows  "(m Amic n)"
  using assms Amicable_pair_def Esigma_properdiv_set
  by (metis add_right_imp_eq add.commute )

definition typeAmic :: "nat \<Rightarrow> nat \<Rightarrow> nat list"
  where "typeAmic n m =
    [(card {i. \<exists> N. n = N*(gcd n m) \<and> prime i \<and> i dvd N \<and> \<not> i dvd (gcd n m)}),
     (card {j. \<exists> M. m = M*(gcd n m) \<and> prime j \<and> j dvd M \<and> \<not> j dvd (gcd n m)})]"

lemma Amicable_pair_deficient: assumes "m > n" and  "m Amic n"
  shows "deficient_number m"
  using assms deficient_number_def Amicable_pair_def by metis

lemma Amicable_pair_abundant: assumes "m > n" and  "m Amic n"
  shows "abundant_number n"
  using assms abundant_number_def Amicable_pair_def by metis

lemma even_even_amicable: assumes  "m Amic n" and "m \<ge>1" and "n \<ge>1" and "even m" and "even n"
  shows "(2*m \<noteq> n)"

proof( rule ccontr )
  have a: "Esigma m  = Esigma n" using \<open>m Amic n\<close> Amicable_pair_equiv_def Amicable_pair_def
     assms by blast

  assume "\<not> (2*m \<noteq> n)"
  have "(2*m = n)" using \<open>\<not> (2*m \<noteq> n)\<close> by simp
  have d:"Esigma n = Esigma (2*m)"  using  \<open>\<not> (2*m \<noteq> n)\<close> by simp

  then show False

  proof-
    have w: "2*m \<in> divisor_set (2*m)" using divisor_set assms divisor_set_not_empty
      by auto
    have w1: "2*m \<notin> divisor_set (m)" using divisor_set assms
      by (simp add: divisor_def)
    have w2: "\<forall> n::nat. n divisor m \<longrightarrow> n divisor (2*m)"
      using assms divisor_def by auto
    have w3: "divisor_set (2*m) \<supset> divisor_set m" using divisor_set divisor_def assms w w1 w2
      by blast
    have v: "( \<Sum> i \<in> ( divisor_set (2*m)).i)> ( \<Sum> i \<in> ( divisor_set m).i)"
      using w3  sum_strict_mono by (simp add: divisor_def divisor_set)
    show ?thesis using v d Esigma_def a by auto
  qed
qed


subsubsection\<open>Regular Amicable Pairs\<close>

definition regularAmicPair :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "regularAmicPair n m \<longleftrightarrow> (n Amic m \<and>
     (\<exists>M N g. g = gcd m n \<and> m = M*g \<and> n = N*g \<and> squarefree M \<and>
              squarefree N \<and> gcd g M = 1 \<and> gcd g N = 1))"

lemma regularAmicPair_sym:
  assumes "regularAmicPair n m" shows "regularAmicPair m n"

proof-
  have "gcd m n = gcd n m"
    by (metis (no_types) gcd.commute)
  then show ?thesis
    using Amicable_pair_sym assms regularAmicPair_def by auto
qed

definition irregularAmicPair :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "irregularAmicPair n m \<longleftrightarrow> (( n Amic m) \<and> \<not> regularAmicPair n m)"

lemma irregularAmicPair_sym:
  assumes "irregularAmicPair n m"
  shows "irregularAmicPair m n"
  using  irregularAmicPair_def regularAmicPair_sym Amicable_pair_sym assms by blast


subsubsection\<open>Twin Amicable Pairs\<close>

text \<open>We refer to the definition in \cite{amicwiki}:\<close>

definition twinAmicPair :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "twinAmicPair n m \<longleftrightarrow>
     (n Amic m) \<and> (\<not>(\<exists>k l. k > Min {n, m} \<and> k < Max {n, m}\<and> k Amic l))"

lemma twinAmicPair_sym:
  assumes "twinAmicPair n m"
  shows "twinAmicPair m n"
  using assms twinAmicPair_def Amicable_pair_sym assms by auto

subsubsection\<open>Isotopic Amicable Pairs\<close>

text\<open>A way of generating an amicable pair from a given amicable pair under certain conditions is 
given below. Such amicable pairs are called Isotopic \cite{garciaetal1}.\<close>

lemma isotopic_amicable_pair:
  fixes m n g h M N :: nat
  assumes "m Amic n" and "m \<ge> 1" and "n \<ge> 1"and "m= g*M" and "n = g*N"
      and "Esigma h = (h/g) * Esigma g" and "h \<noteq> g" and "h > 1" and "g > 1"
      and "gcd g M = 1" and "gcd g N = 1" and "gcd h M = 1" and "gcd h N = 1"
    shows "(h*M) Amic (h*N)"

proof-
  have a: "Esigma m = Esigma n" using \<open> m Amic n\<close>  Amicable_pair_equiv_def assms
    by blast
  have b: "Esigma m = m + n" using \<open> m Amic n\<close> Amicable_pair_equiv_def assms
    by blast
  have c: "Esigma (h*M) = (Esigma h)*(Esigma M)"

  proof-
    have  "h \<noteq> M"
      using assms Esigmanotzero gcd_Esigma_mult gcd_nat.idem b mult_eq_self_implies_10
    by (metis less_irrefl)

    show ?thesis using  \<open>h \<noteq> M\<close>  gcd_Esigma_mult assms
     by auto
  qed

  have d: "Esigma (g*M) = (Esigma g)*(Esigma M)"

  proof-
       have  "g\<noteq>M"  using assms gcd_nat.idem by (metis less_irrefl)
     show ?thesis using  \<open>g\<noteq>M\<close>  gcd_Esigma_mult assms by auto
  qed

  have e: "Esigma (g*N) = (Esigma g)*(Esigma N)"

    proof-
    have  "g\<noteq>N"  using assms by auto
    show ?thesis using  \<open>g\<noteq>N\<close>  gcd_Esigma_mult assms by auto
    qed

  have p1: "Esigma m = (Esigma g)*(Esigma M)" using assms d by simp
  have p2: "Esigma n = (Esigma g)*(Esigma N)" using assms e by simp
  have p3: "Esigma (h*N) = (Esigma h)*(Esigma N)"

  proof-
    have  "h\<noteq>N"  using assms \<open> gcd h N =1\<close>  a b p2 by fastforce
    show ?thesis using  \<open>h \<noteq> N\<close>  gcd_Esigma_mult  assms by auto
  qed

  have A: "Esigma (h*M) = Esigma (h*N)"
    using c p3 d e p1 p2 a assms Esigmanotzero by fastforce

  have B:  "Esigma (h*M)=(h*M)+(h*N)"
  proof-
     have s: "Esigma (h*M) = (h/g)*(m+n)" using b c p1 Esigmanotzero assms by simp
     have s1: "Esigma (h*M) = h*(m/g+n/g)" using  s assms
       by (metis add_divide_distrib b of_nat_add semiring_normalization_rules(7)
 times_divide_eq_left times_divide_eq_right)
     have s2: " Esigma (h*M) = h*(M+N)"
     proof-
       have v: "m/g = M" using assms by simp
       have v1:"n/g = N" using assms by simp
       show ?thesis using s1 v v1 assms
         using of_nat_eq_iff by fastforce
     qed
     show ?thesis using s2 assms
       by (simp add: add_mult_distrib2)
   qed
  show ?thesis using Amicable_pair_equiv_def_conv A B assms one_le_mult_iff  One_nat_def Suc_leI
    by (metis (no_types, hide_lams)  nat_less_le)
qed


lemma isotopic_pair_example1:
  assumes "(3^3*5*11*17*227) Amic (3^3*5*23*37*53)"
  shows  "(3^2*7*13*11*17*227) Amic (3^2*7*13*23*37*53)"

proof-
  obtain m where o1: "m = (3::nat)^3*5*11*17*227" by simp
  obtain n where o2: "n = (3::nat)^3*5*23*37*53" by simp
  obtain g where o3: "g = (3::nat)^3*5" by simp
  obtain h where o4: "h = (3::nat)^2*7*13" by simp
  obtain M where o5: "M = (11::nat)*17*227" by simp
  obtain N where o6: "N = (23::nat)*37*53" by simp
  have "prime(3::nat)" by simp
  have "prime(5::nat)" by simp
  have "prime(7::nat)" by simp
  have "prime(13::nat)" by simp

  have v: "m Amic n" using o1 o2 assms by simp
  have v1: "m = g*M" using o1 o3 o5  by simp
  have v2: "n = g*N"  using o2 o3 o6 by simp
  have v3: "h >0" using o4 by simp
  have w: "g >0" using o3 by simp
  have w1: "h \<noteq> g" using o4 o3 by simp
  have "h = 819" using o4 by simp
  have "g = 135" using o3 by simp

    have w2: "Esigma h = (h/g)*Esigma g"

  proof-
  have B: "Esigma h = 1456"
    proof-
      have R: "set(divisors_nat 819) ={1, 3, 7, 9, 13, 21, 39, 63, 91, 117, 273, 819}"
        by eval
      have RR: "set( divisors_nat(819)) = divisor_set (819)"
        using def_equiv_divisor_set by simp

      show?thesis using Esigma_def RR R \<open> h = 819\<close> divisor_def divisors_nat divisors_nat_def by auto
     qed

    have C: "Esigma g = 240"
    proof-
      have G: "set(divisors_nat 135) = {1, 3, 5, 9, 15, 27, 45, 135}"
        by eval
      have GG:  "set(divisors_nat 135) = divisor_set 135"
        using  def_equiv_divisor_set by simp

   show ?thesis using G GG Esigma_def  \<open> g = 135\<close>
      properdiv_set proper_divisor_def
     by simp
 qed
  have D: "(Esigma h) * g = (Esigma g) * h"

    proof-
    have A: "(Esigma h) * g = 196560"
        using B o3 by simp
      have AA: "(Esigma g) * h = 196560" using C o4  by simp
      show ?thesis using A AA by simp
    qed
    show ?thesis using D
      by (metis mult.commute nat_neq_iff nonzero_mult_div_cancel_right
of_nat_eq_0_iff of_nat_mult times_divide_eq_left w)

 qed

  have w4: "gcd g M =1"

  proof-
    have "coprime g M"

    proof-
      have "\<not> g dvd M"  using o3 o5 by auto
      moreover have  "\<not> 3 dvd M" using o5 by auto
      moreover have  "\<not> 5 dvd M"  using o5 by auto
      ultimately show ?thesis using o5 o3
     gcd_nat.absorb_iff2 prime_nat_iff \<open> prime(3::nat)\<close> \<open> prime(5::nat)\<close>
    by (metis coprime_commute
coprime_mult_left_iff prime_imp_coprime_nat prime_imp_power_coprime_nat)
qed
 show ?thesis using \<open>coprime g M\<close> by simp
  qed

  have s: " gcd g N =1"

  proof-
    have "coprime g N"

 proof-
      have "\<not> g dvd N"
        using o3 o6  by auto
      moreover have "\<not> 3 dvd N" using o6 by auto
      moreover have "\<not> 5 dvd N" using o6 by auto
      ultimately show ?thesis using o3 gcd_nat.absorb_iff2 prime_nat_iff \<open> prime(3::nat)\<close>
 \<open> prime(5::nat)\<close>
    by (metis coprime_commute
coprime_mult_left_iff prime_imp_coprime_nat prime_imp_power_coprime_nat)
qed
 show ?thesis using \<open>coprime g N\<close> by simp
  qed

  have s1: "gcd h M =1"

 proof-
   have "coprime h M"

 proof-
      have "\<not> h dvd M"  using o4 o5  by auto
      moreover have "\<not> 3 dvd M" using o5  by auto
      moreover have "\<not> 7 dvd M" using o5  by auto
      moreover have "\<not> 13 dvd M" using o5 by auto
      ultimately  show ?thesis using o4  gcd_nat.absorb_iff2 prime_nat_iff \<open> prime(3::nat)\<close>
\<open> prime(13::nat)\<close> \<open> prime(7::nat)\<close>

    by (metis coprime_commute
coprime_mult_left_iff prime_imp_coprime_nat prime_imp_power_coprime_nat)
qed

  show ?thesis using \<open>coprime h M\<close>  by simp
  qed

  have s2: "gcd h N =1"

  proof-
    have "coprime h N"

    proof-
  have "\<not> h dvd N" using o4 o6  by auto
  moreover have "\<not> 3 dvd N" using o6  by auto
  moreover have "\<not> 7 dvd N" using o6  by auto
  moreover have "\<not> 13 dvd N" using o6 by auto
  ultimately show ?thesis using o4
     gcd_nat.absorb_iff2 prime_nat_iff \<open> prime(3::nat)\<close>\<open> prime(13::nat)\<close> \<open> prime(7::nat)\<close>

    by (metis coprime_commute
coprime_mult_left_iff prime_imp_coprime_nat prime_imp_power_coprime_nat)
qed

 show ?thesis using \<open>coprime h N\<close>  by simp
  qed

  have s4: "(h*M) Amic (h*N)" using isotopic_amicable_pair v v1 v2 v3 w4 s s1 s2 w w1 w2
   by (metis One_nat_def Suc_leI le_eq_less_or_eq nat_1_eq_mult_iff
num.distinct(3) numeral_eq_one_iff one_le_mult_iff one_le_numeral o3 o4 o5 o6)

  show ?thesis using s4 o4 o5 o6 by simp
qed


subsubsection\<open>Betrothed (Quasi-Amicable) Pairs\<close>

text\<open>We refer to the definition in \cite{betrothedwiki}:\<close>

definition QuasiAmicable_pair :: "nat \<Rightarrow> nat \<Rightarrow> bool"  (infixr "QAmic" 80)
  where "m QAmic n \<longleftrightarrow> (m + 1 = aliquot_sum n) \<and> (n + 1 = aliquot_sum m)"

lemma QuasiAmicable_pair_sym :
  assumes "m QAmic n " shows "n QAmic m "
  using  QuasiAmicable_pair_def assms by blast

lemma QuasiAmicable_example:
  shows "48 QAmic 75"

proof-
  have a: "set(divisors_nat 48) = {1, 2, 3, 4, 6, 8, 12, 16, 24, 48}" by eval
  have b: "divisor_set (48) = {1, 2, 3, 4, 6, 8, 12, 16, 24, 48}"
    using a  def_equiv_divisor_set by simp
  have c: "properdiv_set (48) = {1, 2, 3, 4, 6, 8, 12, 16, 24}"
    using b union_properdiv_set properdiv_set proper_divisor_def by auto
  have e: "aliquot_sum (48) = 75+1" using aliquot_sum_def c
    by simp
  have i: "set(divisors_nat 75) = {1, 3, 5, 15, 25, 75}" by eval
  have ii: "divisor_set (75) = {1, 3, 5, 15, 25, 75}"
    using i  def_equiv_divisor_set by simp
  have iii: "properdiv_set (75) = {1, 3, 5, 15, 25}"
    using ii union_properdiv_set properdiv_set proper_divisor_def by auto
  have iv: "aliquot_sum (75) = 48+1" using aliquot_sum_def iii
    by simp
  show ?thesis using e iv QuasiAmicable_pair_def by simp
qed


subsubsection\<open>Breeders\<close>

definition breeder_pair :: "nat \<Rightarrow>nat \<Rightarrow> bool"  (infixr "breeder" 80)
  where "m breeder n \<equiv> (\<exists>x\<in>\<nat>. x > 0 \<and> Esigma m = m + n*x \<and> Esigma m = (Esigma n)*(x+1))"

lemma breederAmic:
  fixes x :: nat
  assumes "x > 0" and "Esigma n = n + m*x" and "Esigma n = Esigma m * (x+1)" 
      and "prime x" and "\<not>( x dvd m)"
  shows " n Amic (m*x)"

proof-
  have A: "Esigma n = Esigma (m*x)"
  proof-
    have "gcd m x =1" using assms  gcd_nat.absorb_iff2 prime_nat_iff by blast

    have A1: "Esigma (m*x) = (Esigma m)*(Esigma x)"
      using \<open>gcd m x =1\<close> gcd_Esigma_mult by simp
    have A2: "Esigma (m*x) = (Esigma m)*(x+1)"
      using \<open>prime x\<close>  prime_Esigma_mult A1
      by (simp add: prime_sum_div)
    show ?thesis using A2 assms by simp
  qed

  have B: "Esigma n = n+m*x" using assms by simp
  show ?thesis using A B Amicable_pair_equiv_def
     by (smt Amicable_pair_equiv_def_conv Esigma_properdiv_set
One_nat_def Suc_leI add_cancel_left_left add_le_same_cancel1 add_mult_distrib2 assms
 dvd_triv_right le_add2 nat_0_less_mult_iff not_gr_zero not_le semiring_normalization_rules(1))
 qed


subsubsection\<open>More examples\<close>

text\<open>The first odd-odd amicable pair was discovered by Euler \cite{garciaetal1}. In the following 
proof, amicability is shown using the properties of Euler's sigma function.\<close>

lemma odd_odd_amicable_Euler: "69615 Amic 87633"
proof-
  have "prime(5::nat)" by simp
  have "prime(17::nat)" by simp
  have "\<not> (5*17)dvd((3::nat)^2*7*13)" by auto
  have "\<not> 5 dvd((3::nat)^2*7*13)" by auto
  have "\<not> 17 dvd((3::nat)^2*7*13)"  by auto
  have A1: "Esigma(69615) = Esigma(3^2*7*13*5*17)" by simp
  have A2: "Esigma(3^2*7*13*5*17) =  Esigma(3^2*7*13)*Esigma(5*17)"
  
  proof-
    have A111: "coprime  ((3::nat)^2*7*13) ((5::nat)*17)"
      using \<open>\<not> 17 dvd((3::nat)^2*7*13)\<close> \<open>\<not> 5 dvd((3::nat)^2*7*13)\<close> \<open>prime (17::nat)\<close>
        \<open>prime (5::nat)\<close> coprime_commute coprime_mult_left_iff prime_imp_coprime_nat by blast

    have "gcd (3^2*7*13)((5::nat)*17) =1"
      using A111  coprime_imp_gcd_eq_1 by blast
    show ?thesis using \<open>gcd (3^2*7*13)((5::nat)*17) =1 \<close>
        gcd_Esigma_mult
      by (smt semiring_normalization_rules(18) semiring_normalization_rules(7))
  qed
  have "prime (7::nat)" by simp
  have "\<not> 7 dvd ((3::nat)^2)"  by simp
  have "prime (13::nat)" by simp
  have " \<not> 13 dvd ((3::nat)^2*7)"  by simp
  have  "gcd ((3::nat)^2*7) 13 =1"
    using \<open>prime (13::nat)\<close> \<open>\<not> 13 dvd ((3::nat)^2*7)\<close> gcd_nat.absorb_iff2 prime_nat_iff
    by blast
  have A3: " Esigma(3^2 * 7*13) = Esigma(3^2*7)*Esigma(13)"
    using  \<open>gcd  (3^2 *7) 13 =1\<close>  gcd_Esigma_mult
    by (smt semiring_normalization_rules(18) semiring_normalization_rules(7))
  have  "gcd ((3::nat)^2) 7 = 1"
    using \<open>prime (7::nat)\<close> \<open> \<not> 7 dvd ((3::nat)^2 )\<close> gcd_nat.absorb_iff2 prime_nat_iff
    by blast
  have A4: " Esigma(3^2*7) = Esigma(3^2)* Esigma (7)"
    using  \<open>gcd ((3::nat)^2) 7 =1\<close>  gcd_Esigma_mult
    by (smt semiring_normalization_rules(18) semiring_normalization_rules(7))
  have A5: "Esigma(3^2) = 13"
  proof-
    have  "(3::nat)^2 =9" by auto
    have A55:"divisor_set 9 = {1, 3, 9}"
    proof-
      have A555: "set(divisors_nat (9)) = {1, 3, 9}" by eval
      show ?thesis using def_equiv_divisor_set A555 by simp
    qed
    show ?thesis using A55 \<open>(3::nat)^2 =9\<close> Esigma_def by simp
  qed
  have "prime( 13::nat)" by simp
  have A6: "Esigma (13) = 14"
    using prime_sum_div \<open>prime( 13::nat)\<close> by auto
  have "prime( 7::nat)" by simp
  have A7: "Esigma (7) = 8"
    using prime_sum_div \<open>prime( 7::nat)\<close> by auto
  have "prime (5::nat)" by simp
  have "prime (17::nat)" by simp
  have A8: "Esigma(5*17) = Esigma(5) * Esigma (17)" 
    using prime_Esigma_mult \<open>prime (5::nat)\<close> \<open>prime (17::nat)\<close>
    by (metis arith_simps(2) mult.commute num.inject(2) numeral_eq_iff semiring_norm(83))
  have A9: "Esigma(69615) = Esigma(3^2)*Esigma (7) *Esigma (13) * Esigma(5) * Esigma (17)"
    using A1 A2 A3 A4 A5 A6 A7 A8 by (metis mult.assoc)
  have A10: "Esigma (5)=6"
    using prime_sum_div \<open>prime(5::nat)\<close> by auto
  have A11: "Esigma (17)=18"
    using prime_sum_div \<open>prime(17::nat)\<close> by auto
  have AA:  "Esigma(69615)=13*8*14*6*18" using A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11
    by simp
  have AAA: "Esigma(69615) =157248" using AA by simp

  have AA1: "Esigma(87633) = Esigma (3^2*7*13*107)" by simp
  have "prime (107::nat)" by simp
  have AA2: "Esigma (3^2*7*13*107) = Esigma (3^2*7*13)*Esigma(107)"

  proof-
    have "\<not> (107::nat) dvd  (3^2*7*13)" by auto
    have "gcd  ((3::nat)^2*7*13) 107 =1" using \<open>prime (107::nat)\<close>
        \<open> \<not> (107::nat) dvd  (3^2*7*13)\<close>

      using gcd_nat.absorb_iff2 prime_nat_iff by blast

    show ?thesis using \<open>gcd  (3^2 *7*13) 107 =1\<close> gcd_Esigma_mult by (smt mult.commute)
  qed
  have AA3:  "Esigma (107) =108"
    using prime_sum_div \<open>prime(107::nat)\<close> by auto
  have AA4: "Esigma(3^2*7*13) = 13*8*14"
    using A3 A4 A5 A6 A7 by auto
  have AA5 : "Esigma (3^2*7*13*107) = 13*8*14*108"
    using AA2 AA3 AA4 by auto
  have AA6: "Esigma (3^2*7*13*107) = 157248" using AA5 by simp
  have A:"Esigma(69615) = Esigma(87633)"
    using  AAA AA6 AA5 AA1 by linarith
  have B: " Esigma(87633) = 69615 + 87633"
    using AAA \<open>Esigma 69615 = Esigma 87633\<close> by linarith
  show ?thesis using A B Amicable_pair_def Amicable_pair_equiv_def_conv by auto
qed

text\<open>The following is the smallest odd-odd amicable pair \cite{garciaetal1}. In the following proof, 
amicability is shown directly by evaluating the sets of divisors.\<close>

lemma Amicable_pair_example_smallest_odd_odd: "12285 Amic 14595"
proof-
  have A: "set(divisors_nat (12285)) = {1, 3, 5, 7, 9, 13, 15, 21, 27, 35, 39, 45, 63, 65, 91,
105, 117, 135, 189, 195, 273, 315, 351, 455, 585, 819, 945, 1365, 1755, 2457, 4095, 12285}"
    by eval
  have A1: "set(divisors_nat (12285)) = divisor_set 12285"
    using def_equiv_divisor_set by simp
  have A2: "\<Sum>{1, 3, 5, 7, 9, 13, 15, 21, 27, 35, 39, 45, 63, 65, 91, 105, 117, 135, 189, 195, 273, 
315, 351, 455, 585, 819, 945, 1365, 1755, 2457, 4095, 12285} = (26880::nat)" by eval
  have  A3: "Esigma 12285 = 26880" using A A1 A2 Esigma_def by simp
  have Q:"Esigma 12285 = Esigma 14595"
  proof-
    have N: "set(divisors_nat (14595)) =
               { 1, 3, 5, 7, 15, 21, 35, 105, 139, 417, 695, 973, 2085, 2919, 4865, 14595}"
      by eval
    have N1: "set(divisors_nat (14595)) = divisor_set 14595"
      using def_equiv_divisor_set by simp
    have N2:
      "\<Sum>{ 1, 3, 5, 7, 15, 21, 35, 105, 139, 417, 695, 973, 2085, 2919, 4865, 14595} = (26880::nat)"
      by eval
    show ?thesis using A3 N N1 N2 Esigma_def by simp
  qed
  have B:"Esigma (12285) = 12285 + 14595" using A3 by auto
  show ?thesis using B Q Amicable_pair_def
    using Amicable_pair_equiv_def_conv one_le_numeral by blast
qed


section\<open>Euler's Rule\<close>

text\<open>We present Euler's Rule as in \cite{garciaetal1}. The proof has been reconstructed.\<close>

theorem Euler_Rule_Amicable:
  fixes k l f p q r m n :: nat
  assumes "k > l" and "l \<ge> 1" and "f = 2^l+1" 
      and "prime p" and "prime q" and "prime r"
      and "p = 2^(k-l) * f - 1" and "q = 2^k * f - 1" and "r = 2^(2*k-l) * f^2 - 1" 
      and "m = 2^k * p * q" and "n = 2^k * r"
  shows "m Amic n"

proof-
  note [[linarith_split_limit = 50]]
  have A1: "(p+1)*(q+1) = (r+1)"
  proof-
    have a: "p+1 = (2^(k-l))*f" using assms by simp
    have b: "q+1 = (2^(k))*f" using assms by simp
    have c: "r+1 = (2^(2*k-l))*(f^2)" using assms by simp
    have d: "(p+1)*(q+1) = (2^(k-l))*(2^(k))*f^2"
      using a b by (simp add: power2_eq_square)
    show ?thesis using d c
      by (metis Nat.add_diff_assoc add.commute assms(1) less_imp_le_nat mult_2 power_add)
  qed
  have aa: "Esigma p = p+1" using assms \<open>prime p\<close> prime_sum_div by simp
  have bb: "Esigma q = q+1" using \<open>prime q\<close> prime_sum_div assms by simp
  have cc: "Esigma r = r+1" using \<open>prime r\<close> prime_sum_div assms by simp
  have A2: "(Esigma p)*(Esigma q) = Esigma r"
    using aa bb cc A1 by simp
  have A3: "Esigma (2^k)*(Esigma p)*(Esigma q) = Esigma(2^k)*(Esigma r)"
    using A2 by simp
  have A4: "Esigma(( 2^k)*r) = (Esigma(2^k))*(Esigma r)"
  proof-
    have Z0: "gcd ((2::nat)^k)r =1" using assms \<open>prime r\<close>  by simp
    have A: "(2::nat)^k \<ge> 1" using assms by simp
    have Ab: "(2::nat)^k \<noteq> r" using assms
      by (metis gcd_nat.idem numeral_le_one_iff prime_ge_2_nat semiring_norm(69) Z0)
   show ?thesis using Z0 gcd_Esigma_mult assms A Ab by metis
  qed

  have A5: "Esigma((2^k)*p*q) =(Esigma(2^k))*(Esigma p)*(Esigma q)"
  proof-
    have "(2::nat)^k \<ge>1" using assms by simp
    have A:  "gcd (2^k) p =1" using assms \<open>prime p\<close> by simp
    have B:  "gcd (2^k) q =1" using assms \<open>prime q\<close> by simp
    have BB: "gcd (2^k) (p*q) =1" using assms A B by fastforce
    have C:  "p*q \<ge>1" using assms One_nat_def one_le_mult_iff prime_ge_1_nat by metis
    have A6: " Esigma((2^k)*(p*q))=( Esigma(2^k))*(Esigma(p*q))"
    proof-
      have "(( 2::nat)^k) \<noteq> (p*q)" using assms
        by (metis BB Nat.add_0_right gcd_idem_nat less_add_eq_less
            not_add_less1 power_inject_exp prime_gt_1_nat semiring_normalization_rules(32)
            two_is_prime_nat )
      show ?thesis using \<open>(( 2::nat)^k) \<noteq> (p*q)\<close>
          \<open>( 2::nat)^k \<ge>1\<close>  gcd_Esigma_mult assms C BB
        by metis
    qed
    have A7:"Esigma(p*q) = (Esigma p)*(Esigma q)"
    proof-
      have "p \<noteq> q" using assms One_nat_def Suc_pred add_gr_0 add_is_0 diff_commute diff_diff_cancel
          diff_is_0_eq nat_0_less_mult_iff nat_mult_eq_cancel_disj
          numeral_One prime_gt_1_nat power_inject_exp
          semiring_normalization_rules(7) two_is_prime_nat zero_less_numeral zero_less_power
zero_neq_numeral  by (smt less_imp_le_nat)

      show ?thesis using \<open>p \<noteq> q\<close>
          \<open>prime p\<close>  \<open>prime q\<close> C  prime_Esigma_mult assms
        by (metis mult.commute)
    qed

    have A8: "Esigma((2^k)*( p*q))=(Esigma(2^k))*(Esigma p)*(Esigma q)" by (simp add: A6 A7)
    show ?thesis using A8 by (simp add: mult.assoc)
  qed

  have Z: "Esigma((2^k)*p*q) = Esigma ((2^k)*r)" using A1 A2 A3 A4 A5 by simp

  have Z1: "Esigma ((2^k)*p*q) = 2^k *p*q + 2^k*r"

  proof-
    have "prime (2::nat)" by simp
    have s: "Esigma (2^k) =((2::nat)^(k+1)-1)/(2-1)"
      using  \<open>prime (2::nat)\<close> assms Esigma_prime_sum  by auto
    have ss: "Esigma (2^k) =(2^(k+1)-1)" using s by simp
    have J: "(k+1+k-l+k)= 3*k +1-l" using assms by linarith
    have JJ: "(2^(k-l))*(2^k) = (2::nat)^(2*k-l)"
      apply (simp add: algebra_simps)
      by (metis Nat.add_diff_assoc assms(1) less_imp_le_nat mult_2_right power_add)
    have "Esigma((2^k)*p*q)= (Esigma(2^k))*(Esigma p)*(Esigma q)" using A5 by simp
    also have "\<dots> = (2^(k+1)-1)*(p+1)*(q+1)" using assms ss aa bb by metis
   also have "\<dots> = (2^(k+1)-1)*((2^(k-l))*f)*((2^k)*f)" using assms by simp
   also have "\<dots> = (2^(k+1)-1)*(2^(k-l))*(2^k)*f^2"
      by (simp add: power2_eq_square)
    also have "\<dots> = (2^(k+1))*(2^(k-l))*(2^k)*f^2-(2^(k-l))*(2^k)*f^2"
      by (smt left_diff_distrib' mult.commute mult_numeral_1_right numeral_One)
   also have "\<dots> = (2^(k+1+k-l+k))*f^2-(2^(k-l))*(2^k)*f^2"
      by (metis Nat.add_diff_assoc assms(1) less_imp_le_nat power_add)
   also have "\<dots> = (2^(3*k+1-l))*f^2-(2^(k-l))*(2^k)*f^2"
     using J by auto
   also have "\<dots> = (2^(3*k+1-l))*f^2-(2^(2*k-l))*f^2"
    using JJ by simp
  finally
  have YY:" Esigma((2^k)*p*q)= (2^(3*k+1-l))*f^2-(2^(2*k-l))*f^2" .

    have auxicalc: "(2^(2*k-l))*(f^2)=(2^(2*k-l))*f +(2^(2*k))*f"

    proof-
      have i: "(2^(2*k-l))*f = (2^(2*k-l))*(2^l+1)"
        using assms \<open>f = 2^l+1\<close> by simp
       have ii: "( 2^(2*k-l))*f = (2^(2*k-l))*( 2^l)+(2^(2*k-l))"
         using i by simp
       have iii: "(2^(2*k-l))*f = (2^(2*k-l+l))+(2^(2*k-l))"
        using ii  by (simp add: power_add)
       have iv: "( 2^(2*k-l))*f*f =(((2^(2*k))+(2^(2*k-l))))*f"
        using iii assms by simp
       have v:  "(2^(2*k-l))*f *f =((2^(2*k)))*f+((2^(2*k-l)))*f"
        using iv assms comm_monoid_mult_axioms  power2_eq_square semiring_normalization_rules(18)
          semiring_normalization_rules by (simp add: add_mult_distrib assms) (*slow*)
      show ?thesis using v by (simp add: power2_eq_square semiring_normalization_rules(18))
    qed

    have W1: "2^k*p*q + 2^k*r = 2^k *(p*q +r) "
      by (simp add: add_mult_distrib2)

    have W2: "2^k*(p*q +r)= 2^k *((2^(k-l)*f-1)*((2^k)*f-1)+(2^(2*k-l))*f^2-1)"
      using assms by simp

    have W3: "2^k*((2^(k-l)*f-1)*((2^k)*f-1)+(2^(2*k-l))*f^2-1)=
2^k*((2^(k-l)*f-1)*((2^k)*f)-(2^(k-l)*f-1)+(2^(2*k-l))*f^2-1)"
      by (simp add: right_diff_distrib')

    have W4: "2^k*((2^(k-l)*f-1)*((2^k)*f)-(2^(k-l)*f-1)+(2^(2*k-l))*f^2-1) =
2^k*((2^(k-l)*f)*((2^k)*f)-((2^k)*f)-(2^(k-l)*f-1)+(2^(2*k-l))*f^2-1)"
      using assms  by (simp add: diff_mult_distrib)

    have W5: " 2^k*((2^(k-l)*f)*((2^k)*f)-((2^k)*f)-(2^(k-l)*f-1)+(2^(2*k-l))*f^2-1) =
2^k *(( 2^(k-l)*f)*((2^k)*f)-((2^k)*f)-(2^(k-l)*f)+1 +(2^(2*k-l))*f^2-1)"
      using assms  less_imp_le_nat less_imp_le_nat  prime_ge_1_nat
      by (smt Nat.add_diff_assoc2 Nat.diff_diff_right One_nat_def Suc_leI Suc_pred W3 W4
          add_diff_cancel_right' add_gr_0 le_Suc_ex less_numeral_extra(1) mult_cancel1
          nat_0_less_mult_iff zero_less_diff zero_less_numeral zero_less_power)

    have W6: "2^k*((2^(k-l)* f)*((2^k)*f)-((2^k)*f)-(2^(k-l)*f)+1+(2^(2*k-l))*f^2-1 ) =
 2^k*((2^(k-l)*f)*((2^k)*f)-((2^k )*f)-(2^(k-l)*f)+(2^(2*k-l))*f^2)"
          by simp

    have W7: "2^k*((2^(k-l)*f)*((2^k)*f)-((2^k)*f)-(2^(k-l)*f)+(2^(2*k-l))*f^2) =
   2^k *((2^(2*k-l+1)*(f^2))-((2^k)*f)-(2^(k-l)* f))"

    proof-
      have a: "(2^(k-l)*f)*(2^k * f) = (2^(k-l)*f*(f*(2^k))) "
        using assms by simp
      have b: "(2^(k-l)*f)*(f*(2^k)) = 2^(k-l)*(f*f)*(2^k)"
        using assms by linarith
      have c: "2^(k-l)*(f*f)*(2^k) = 2^(k-l+k)*(f^2)"
        using Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(16)
          Semiring_Normalization.comm_semiring_1_class.semiring_normalization_rules(29)
        by  (simp add:  power_add)

      have d: "2^(k-l+k) *(f^2) = 2^(2*k-l) *(f^2)"
        by (simp add: JJ power_add)

      have e: "(2^(2*k-l))*f^2 + (2^(2*k-l))*f^2 =  2^(2*k-l +1)*(f^2)"
         by simp

       have f1: "((2^(k-l)*f)*((2^k)*f)-((2^k)*f)-(2^(k-l)*f)+(2^(2*k-l))*f^2) =
    (2^(2*k-l)*(f^2)-((2^k)*f)-(2^(k-l)*f)+(2^(2*k-l))*f^2)"
        using a b c d e by simp

      have f2:"((2^(k-l)*f)*((2^k)*f)-((2^k)*f)-(2^(k-l)*f))+(2^(2*k-l))*f^2
       = ((2^(2*k-l+1)*(f^2))-((2^k)*f)-(2^(k-l)*f))"

        proof-
        have aa: "f > 1" using assms by simp
        have a: "((2::nat)^(2*k-l))*f^2-((2::nat)^(k-l)*f)>0"
        proof-
          have b: "(2::nat)^(2*k-l) > 2^(k-l)" using assms by simp
          have c: "(2::nat)^(2*k-l)*f > 2^(k-l)*f" using a assms
            by (metis One_nat_def add_gr_0 b lessI mult_less_mono1)
          show ?thesis
            using c auxicalc by linarith
        qed

        have aaa: "(2^(2*k-l))*f^2 -(2^(k-l)*f)-((2^k)*f) >0"

        proof-
          have A: "(2^(2*k-l))*f-(2^(k-l))-(( 2^k)) >0"

          proof-
              have A_1 : "(2^(2*k-l))*f  > (2^(k-l))+((2^k))"

            proof-
              have A_2: "(2^(2*k-l))*f = 2^(k)*2^(k-l)*f"
                  by (metis JJ semiring_normalization_rules(7))

              have df1: "(2^(k-l))+((2^k))< ((2::nat)^(2*k-l))+((2^k))"
                using \<open>l < k\<close> by (simp add: algebra_simps)

              have df2: "((2::nat)^(2*k-l))+((2^k)) < ((2::nat)^(2*k-l))*f"
              proof-
                have "k >1" using assms by simp
                have df: "((2::nat)^(k-l))+(1::nat) < ((2::nat)^(k-l))*f"
                proof-
                  obtain x::nat where xx: "x=(2::nat)^(k-l)" by simp
                  have xxx: "x \<ge>( 2::nat)" using assms xx
                    by (metis One_nat_def Suc_leI one_le_numeral power_increasing
                        semiring_normalization_rules(33) zero_less_diff)

                  have c: "x*f \<ge> x*(2::nat)" using aa by simp

                  have c1: "x+(1::nat) < x*(2::nat)"
                    using auxiliary_ineq  xxx by linarith
                  have c2: "((2::nat)^(k-l))+(1::nat) < ((2::nat)^(k-l))*(2::nat)"
                    using c1 xx by blast
                  show ?thesis using c2 c xx
                    by (metis diff_is_0_eq' le_trans nat_less_le zero_less_diff)
                qed

                show ?thesis using df aa assms
                  by (smt JJ add.commute mult_less_cancel2 semiring_normalization_rules
                      zero_less_numeral zero_less_power)
              qed
              show ?thesis using A_2 df1 df2 by linarith
            qed

            show ?thesis using assms A_1
              using diff_diff_left zero_less_diff by presburger
          qed

           show ?thesis using A aa assms
            by (metis (no_types, hide_lams)  a nat_0_less_mult_iff right_diff_distrib'
                semiring_normalization_rules(18) semiring_normalization_rules(29)
               semiring_normalization_rules(7))
        qed

        have b3: "((2^(2*k-l)*(f^2))-((2^k)*f)-(2^(k-l)*f)+(2^(2*k-l))*f^2) =
                  (2*(2^(2*k-l)*(f^2))-((2^k)*f)-(2^(k-l)*f))"
          using a aa assms  minus_eq_nat_subst_order  by (smt aaa diff_commute)

        show ?thesis using f1 by (metis b3 e mult_2)

      qed
      show ?thesis using f2 by simp
    qed

    have W8: "2^k*((2^(2*k-l+1)*(f^2))-((2^k)*f)-(2^(k-l)*f)) = (2^(3*k+1-l))*f^2-(2^(2*k-l))*f^2"

    proof-
   have a: "2^k*(2^(2*k-l+1)*f^2-2^k*f-2^(k-l)*f) = 2^k*(2^(2*k-l+1)*f^2)-2^k*(2^k*f)-2^k*(2^(k-l)*f)"
        by (simp add: algebra_simps)

      have b: "2^k*(2^(2*k-l+1)*f^2)-2^k*(2^k*f)-2^k*(2^(k-l)*f) =
2^k*(2^(2*k-l+1)*f^2)-2^k*(2^k*f)-2^k*(2^(k-l)*f)"
        by (simp add: algebra_simps)

      have c: "2^k*(2^(2*k-l+1)*f^2)-2^k*(2^k*f)-2^k*(2^(k-l)*f) =
2^(2*k+1-l+k)*f^2-2^k*(2^k*f)-2^k*(2^(k-l)*f)"
        apply (simp add: algebra_simps power_add)
        by (smt Groups.mult_ac(1) Groups.mult_ac(2) Nat.diff_add_assoc assms(1) le_simps(1)
mult_2_right plus_nat.simps(2) power.simps(2))

      have d: "2^k*(2^(2*k-l+1)*(f^2))= (2^(3*k+1-l))*f^2"

        using power_add   Nat.add_diff_assoc assms(1) less_imp_le_nat mult_2
          semiring_normalization_rules(18) semiring_normalization_rules(23)
        by (smt J)

      have e: "2^k*((2^(2*k-l+1)*(f^2))-((2^k)*f)-(2^(k-l)*f)) =
(2^(3*k+1-l))*f^2-(2^k)*((2^k)*f)-(2^k)*(2^(k-l)*f)"

        using a b c d  One_nat_def  one_le_mult_iff
          Nat.add_diff_assoc assms(1) less_imp_le_nat by metis

      have ee: "2^k*((2^(2*k-l+1)*(f^2))-((2^k)*f)-((2::nat)^(k-l)*f))
= (2^(3*k+1-l))*f^2-( 2^k)*((2^k)*f)-(2^(2*k-l)*f)"

        using e  power_add  Nat.add_diff_assoc assms(1) less_imp_le_nat mult_2
          semiring_normalization_rules
     by (smt J)

      have eee :
        "-(( 2::nat)^(2*k-l))*(f^(2::nat)) =(-(( 2::nat)^(2*k))*f-(( 2::nat)^(2*k-l))*f)"
      using auxicalc mult_minus_eq_nat mult_minus_left of_nat_mult by smt

      have e4: "2^k*((2^(2*k-l+1)*(f^2))-((2^k)*f)-(2^(k-l)*f))=(2^(3*k+1-l))*f^2-(2^(2*k-l))*(f^2)"

      proof-
        define A where A: "A = 2^k*((2^(2*k-l+1)*(f^2))-((2^k)*f)-(2^(k-l)*f))"
        define B where B: "B = (2^(3*k+(1::nat)-l))*f^2"
        define C where C: "C = (2^k)*((2^k)*f)"
        define D where D: "D = (2^(2*k-l)*f)"
        define E where E: "E = (2^(2*k-l))*(f^2)"
        have wq: "A = B-C-D" using ee A B C D  by simp
        have wq1: "-E = -C-D" using eee C D E
          by (simp add: semiring_normalization_rules(36))
        have wq2: "A = B-E" using wq wq1  minus_eq_nat_subst by blast
        show ?thesis using wq2 A B E
          by metis
      qed
     show ?thesis using e4 by simp
    qed

    have Y: "2^k*p*q+2^k*r = (2^(3*k+1-l))*f^2-(2^(2*k-l))*f^2"
      using W1 W2 W3 W4 W5 W6 W7 W8  by linarith
    show ?thesis using Y YY  auxicalc by simp
  qed

  show ?thesis using Z Z1 Amicable_pair_equiv_def_conv assms One_nat_def  one_le_mult_iff
         one_le_numeral less_imp_le_nat one_le_power
    by (metis prime_ge_1_nat)
qed

text\<open>Another approach by Euler \cite{garciaetal1}:\<close>

theorem Euler_Rule_Amicable_1:
  fixes m n a :: nat
  assumes "m \<ge> 1" and "n \<ge> 1" and "a \<ge> 1" 
      and "Esigma m = Esigma n" and "Esigma a * Esigma m = a*(m+n)" 
      and "gcd a m =1" and "gcd a n =1"
      shows "(a*m) Amic (a*n)"

proof-
  have a: "Esigma (a*m) =(Esigma a)*(Esigma m)"
    using assms  gcd_Esigma_mult by (simp add: mult.commute)

  have b: "Esigma (a*m) = Esigma (a*n)"

  proof-
    have c: "Esigma (a*n) = (Esigma a)*(Esigma n)"
      using gcd_Esigma_mult \<open>gcd a n =1\<close>
      by (metis assms(4) a )
    show ?thesis using c a assms by simp
     qed

     have d: " Esigma (a*m) = a*m + a*n "
    using a assms  by (simp add: add_mult_distrib2)
  show ?thesis using a b d Amicable_pair_equiv_def_conv assms by (simp add: Suc_leI)
qed


section\<open>Th\={a}bit ibn Qurra's Rule and more examples\<close>

text\<open>Euler's Rule (theorem Euler\_Rule\_Amicable) is actually a generalisation of the following 
rule by Th\={a}bit ibn Qurra from the 9th century \cite{garciaetal1}. Th\={a}bit ibn Qurra's Rule is 
the special case for $l=1$ thus $f=3$.\<close>

corollary Thabit_ibn_Qurra_Rule_Amicable:
  fixes k l f p q r :: nat
  assumes "k > 1" and "prime p" and "prime q"  and "prime r"
  and "p = 2^(k-1) * 3 - 1" and "q = 2^k * 3 - 1" and "r = 2^(2*k-1) * 9 - 1"
  shows "((2^k)*p*q) Amic ((2^k)*r)"

proof-
   obtain l where l:"l = (1::nat)" by simp
   obtain f where f:"f = (3::nat)" by simp
   have "k >l" using l assms by simp
have  "f =2^1+1" using f by simp
have " r =(2^(2*k-1))*(3^2)-1"  using assms by simp
  show ?thesis  using assms Euler_Rule_Amicable  \<open>f =2^1 +1\<close>
     \<open> r =(2^(2*k -1))*(3^2) -1\<close> l f
    by (metis le_numeral_extra(4))
qed

text\<open>In the following three example of amicable pairs, instead of evaluating the sum of the divisors 
or using the properties of Euler's sigma function as it was done in the previous examples, we 
prove amicability more directly as we can apply Th\={a}bit ibn Qurra's Rule.\<close>

text\<open>The following is the first example of an amicable pair known to the Pythagoreans and can be
derived from Th\={a}bit ibn Qurra's Rule with $k=2$ \cite{garciaetal1}.\<close>

lemma Amicable_Example_Pythagoras:
  shows "220 Amic 284"

proof-
  have a: "(2::nat)>1" by simp
  have b: "prime((3::nat)*(2^(2-1))-1)" by simp
  have c: "prime((3::nat)*(2^2)-1)" by simp
  have d: "prime((9::nat)*(2^(2*2-1))-1)" by simp
  have e: "((2^2)*(3*(2^(2-1))-1)*(3*(2^2)-1))Amic((2^2)*(9*(2^(2*2-1))-1))"
    using Thabit_ibn_Qurra_Rule_Amicable a b c d
    by (metis mult.commute)

  have f: "((2::nat)^2)*5*11 = 220" by simp
  have g: "((2::nat)^2)*71 = 284" by simp
    show ?thesis using  e f g by simp
qed

text\<open>The following example of an amicable pair was (re)discovered by Fermat and can be derived from
Th\={a}bit ibn Qurra's Rule with $k=4$ \cite{garciaetal1}.\<close>

lemma Amicable_Example_Fermat:
  shows  "17296 Amic 18416"

proof-
 have a: "(4::nat)>1" by simp
 have b: "prime((3::nat)*(2^(4-1))-1)" by simp
 have c: "prime((3::nat)*(2^4)-1)" by simp
 have d: "prime (1151::nat)" by (pratt (code))
 have e: "(1151::nat) = 9*(2^(2*4-1))-1" by simp
 have f: "prime((9::nat)*(2^(2*4-1))-1)" using d e by metis
 have g: "((2^4)*(3*(2^(4-1))-1)*(3*(2^4)-1)) Amic((2^4)*(9*(2^(2*4-1))-1))"
   using  Thabit_ibn_Qurra_Rule_Amicable a b c f by (metis mult.commute)
 have h: "((2::nat)^4)*23*47 = 17296" by simp
 have i: "(((2::nat)^4)*1151) = 18416" by simp

  show ?thesis using g h i by simp
qed

text\<open>The following example of an amicable pair was (re)discovered by Descartes and can be derived 
from Th\={a}bit ibn Qurra's Rule with $k=7$ \cite{garciaetal1}.\<close>

lemma Amicable_Example_Descartes:
  shows "9363584 Amic 9437056"

proof-
 have a: "(7::nat)>1" by simp
 have b: "prime (191::nat)"  by (pratt (code))
 have c: "((3::nat)* (2^(7-1))-1) =191" by simp
 have d: "prime((3::nat)* (2^(7-1))-1)" using b c by metis
 have e: "prime (383::nat)"  by (pratt (code))
 have f: "(3::nat)*(2^7)-1 = 383" by simp
 have g: "prime ((3::nat)*(2^7)-1)" using e f by metis
 have h: "prime (73727::nat)"  by (pratt (code))
 have i: "(9::nat)*(2^(2*7-1))-1 = 73727" by simp
 have j: "prime ((9::nat)*(2^(2*7-1))-1)" using i h by metis
 have k: "((2^7)*(3*(2^(7-1))-1)*(3*(2^7)-1))Amic((2^7)*(9*(2^(2*7-1))-1))"
   using  Thabit_ibn_Qurra_Rule_Amicable a d g j by (metis mult.commute)
 have l: "((2::nat)^7)* 191* 383 = 9363584" by simp
 have m: "(((2::nat)^7)* 73727) = 9437056"  by simp

    show ?thesis using a k l by simp
qed


text\<open>In fact, the Amicable Pair (220, 284) is Regular and of type (2,1):\<close>

lemma regularAmicPairExample: "regularAmicPair 220 284 \<and> typeAmic 220 284 = [2, 1]"
proof-
  have a: "220 Amic 284" using Amicable_Example_Pythagoras by simp
  have b: "gcd (220::nat) (284::nat) = 4"  by eval
  have c: "(220::nat) = 55*4"  by simp
  have d: "(284::nat) = 71*4"  by simp
  have e: "squarefree (55::nat)" using squarefree_def by eval
  have f: "squarefree (71::nat)" using squarefree_def by eval
  have g: "gcd (4::nat) (55::nat) =1" by eval
  have h: "gcd (4::nat) (71::nat) =1" by eval

  have A: "regularAmicPair 220 284"
    by (simp add: a b e g f h gcd.commute regularAmicPair_def)
  have B: "(card {i.\<exists> N. ( 220::nat) = N*(4::nat) \<and> prime i \<and> i dvd N \<and> \<not> i dvd 4}) = 2"

  proof-
    obtain N::nat where N: "(220::nat) = N* 4"
      by (metis  c)
    have NN:"N=55" using N by simp
    have K1: "prime(5::nat)" by simp
    have K2: "prime(11::nat)" by simp
    have KK2: " \<not> prime (55::nat)" by simp
    have KK3: " \<not> prime (1::nat)" by simp
    have K: "set(divisors_nat 55 ) = {1, 5, 11, 55}" by eval
    have KK: "{i. i dvd (55::nat)} = {1, 5, 11, 55}"
      using K divisors_nat  divisors_nat_def by auto
    have K3 : "\<not> (5::nat) dvd 4" by simp
    have K4 : "\<not> (11::nat) dvd 4" by simp
    have K55: "(1::nat) \<notin> {i. prime i \<and> i dvd 55}" using KK3 by simp
    have K56: "(55::nat) \<notin> {i. prime i \<and> i dvd 55}" using KK2 by simp
    have K57: "(5::nat) \<in> {i. prime i \<and> i dvd 55}" using K1 by simp
    have K58: "(11::nat) \<in> {i. prime i \<and> i dvd 55}" using K2 by simp
    have K5:  "{i.( prime i \<and> i dvd (55::nat) \<and> \<not> i dvd 4)} = {5, 11}"

    proof-
      have K66: "{i.(prime i \<and> i dvd (55::nat) \<and> \<not> i dvd 4)}=
{i. prime i} \<inter> {i. i dvd 55} \<inter> { i. \<not> i dvd 4}"
        by blast
      show ?thesis using K66  K K1 K2 KK2 KK3  K3 K4 KK K55 K56 K57 K58 divisors_nat_def
          divisors_nat by auto (*slow*)
    qed
    have K6:  "card ({(5::nat), (11::nat)}) = 2"  by simp
    show ?thesis using K5 K6 by simp
  qed

  have C: "(card {i. \<exists>N. (284::nat) = N*4 \<and> prime i \<and> i dvd N \<and> \<not> i dvd 4} ) = 1"
  proof-
    obtain N::nat where N: "284 = N*4"
      by (metis d)
    have NN: "N= 71" using N by simp
    have K: "set(divisors_nat 71 ) = {1, 71 }" by eval
    have KK: "{i. i dvd (71::nat)} = {1, 71}"
      using K divisors_nat  divisors_nat_def by auto

    have K55:"(1::nat) \<notin> {i. prime i \<and> i dvd 71}" by simp
    have K58: "(71::nat) \<in> {i. prime i \<and> i dvd 71}" by simp
    have K5: "{i. prime i \<and> i dvd 71 \<and> \<not> i dvd 4} = {(71::nat)}"
    proof-
      have K66: "{i. prime i \<and> i dvd 71 \<and> \<not> i dvd 4}= 
{i. prime i} \<inter> {i. i dvd 71} \<inter> { i. \<not> i dvd 4}"
        by blast
      show ?thesis using  K KK K55 K58 
        by (auto simp add: divisors_nat_def K66 divisors_nat)
    qed
    have K6: "card ({(71::nat)}) = 1"  by simp
    show ?thesis using K5 K6 by simp
  qed

  show ?thesis using A B C
    by (simp add: typeAmic_def b)
qed

lemma abundant220ex: "abundant_number 220"
proof-
  have "220 Amic 284" using Amicable_Example_Pythagoras by simp
  moreover have "(220::nat) < 284" by simp
  ultimately show ?thesis using Amicable_pair_abundant Amicable_pair_sym
    by blast
qed   

lemma deficient284ex: "deficient_number 284"
proof-
  have "220 Amic 284" using Amicable_Example_Pythagoras by simp
  moreover have "(220::nat) < 284" by simp
  ultimately show ?thesis using Amicable_pair_deficient Amicable_pair_sym
    by blast
qed


section\<open>Te Riele's Rule and Borho's Rule with breeders\<close>

text\<open>With the following rule \cite{garciaetal1} we can get an amicable pair from a known amicable 
pair under certain conditions.\<close>

theorem teRiele_Rule_Amicable: 
  fixes a u p r c q :: nat
  assumes "a \<ge> 1" and "u \<ge> 1"
      and "prime p" and "prime r" and "prime c" and "prime q" and "r \<noteq> c" 
      and "\<not>(p dvd a)" and "(a*u) Amic (a*p)" and "gcd a (r*c)=1"
      and "q = r+c+u" and "gcd (a*u) q =1" and "r*c = p*(r +c+ u) + p+u"
  shows "(a*u*q) Amic (a*r*c)"

proof-
  have "p+1 >0" using assms by simp
  have Z1: " r*c = p*q+p+u" using assms by auto
  have Z2: "(r+1)*(c+1) = (q+1)*(p+1)"
  proof-
    have y: "(q+1)*(p+1) = q*p + q+ p+1 " by simp
    have yy: "(r+1)*(c+1) = r*c + r+ c+1" by simp
    show ?thesis using assms y Z1 yy  by simp
  qed

  have "Esigma(a) = (a*(u+p)/(p+1))"
  proof-
    have d: "Esigma (a*p) = (Esigma a)*(Esigma p)"
      using assms gcd_Esigma_mult \<open>prime p\<close> \<open>\<not> (p dvd a)\<close>
      by (metis gcd_unique_nat prime_nat_iff)
    have dd : "Esigma (a*p) =(Esigma a)*(p+1)"
      using d assms  prime_sum_div by simp
    have ddd: "Esigma (a*p) = a*(u+p)" using assms Amicable_pair_def
        Amicable_pair_equiv_def
      by (smt One_nat_def add_mult_distrib2 one_le_mult_iff prime_ge_1_nat)

    show ?thesis using d dd ddd Esigmanotzero assms(3) dvd_triv_right
        nonzero_mult_div_cancel_right prime_nat_iff prime_sum_div real_of_nat_div
      by (metis \<open>0 < p + 1\<close> neq0_conv)
  qed

  have "Esigma(r) = (r+1)" using assms prime_sum_div by blast
  have "Esigma(c) = (c+1)" using assms prime_sum_div by blast
  have "Esigma (a*r*c) = (Esigma a)*(Esigma r)*(Esigma c)"
  proof-
    have h: "Esigma (a*r*c) = (Esigma a)*(Esigma (r*c))"
      using assms gcd_Esigma_mult
      by (metis mult.assoc mult.commute)
    have hh: " Esigma (r*c) = (Esigma r)*(Esigma c)" using assms prime_Esigma_mult
      by (metis semiring_normalization_rules(7))

    show ?thesis using h hh by auto
  qed

  have A: "Esigma (a*u*q) = Esigma (a*r*c)"
  proof-
    have wk: "Esigma (a*u*q) = Esigma (a*u)*(q+1)"
      using assms gcd_Esigma_mult  by (simp add: prime_sum_div)
    have wk1: "Esigma (a*u) = a*(u+p)" using assms Amicable_pair_equiv_def
      by (smt One_nat_def add_mult_distrib2 one_le_mult_iff prime_ge_1_nat)

    have w3: "Esigma (a*u*q) = a*(u+p)*(q+1)" using wk wk1 by simp
    have w4: "Esigma (a*r*c) =(Esigma a)*(r+1) * (c+1)" using assms
      by (simp add: \<open>Esigma (a*r*c) = Esigma a * Esigma r * Esigma c\<close> \<open>Esigma c = c + 1\<close> 
           \<open>Esigma r = r+1\<close>)

    have we: "a*(u+p)*(q+1) = (Esigma a)*(r+1)*(c+1)"
    proof-
      have we1: "(Esigma a)*(r+1)*(c+1) = (a*(u+p)/(p+1))*(r+1)*(c+1)"
        by (metis \<open>real (Esigma a) = real (a*(u+p))/real(p+1)\<close> of_nat_mult)
      have we12: " (Esigma a)*(r+1)*(c+1) = (a*(u+p)/(p+1))*(q+1)*(p+1)" using we1 Z2
        by (metis of_nat_mult semiring_normalization_rules(18))
      show ?thesis using we12 assms
        by (smt  nonzero_mult_div_cancel_right of_nat_1  of_nat_add of_nat_eq_iff of_nat_le_iff
            of_nat_mult prime_ge_1_nat times_divide_eq_left)
    qed

    show ?thesis using we w3 w4 by simp
  qed

  have B : "Esigma (a*r*c) = (a*u*q)+(a*r*c)"
  proof-
    have a1: "(u+p)*(q+1) = (u*q+p*q+p+u)" using assms add_mult_distrib by auto
    have a2: "(u+p)*(q+1)*(p+1) = (u*q+p*q+p+u)*(p+1)" using a1 assms by metis
    have a3: "(u+p)*(r+1)*(c+1) = (u*q+p*q+p+u)*(p+1)" using assms a2 Z2
      by (metis semiring_normalization_rules(18))
    have a4: "a*(u+p)* (r+1)*(c+1) = a*(u*q+ p*q+p+u)*(p+1)" using assms a3
      by (metis semiring_normalization_rules(18))
    have a5: "a*(u+p)*(r+1)*(c+1) = a*(u*q+r*c)*(p+1)" using assms a4 Z1
      by (simp add: semiring_normalization_rules(21))
    have a6: "(a*(u+p)*(r+1)*(c+1))/(p+1) =(a*(u*q+ r*c)* (p+1))/(p+1)" using assms a5
        semiring_normalization_rules(21) \<open>p+1 >0\<close>  by auto
    have a7: "(a*(u+p)*(r+1)*(c+1))/(p+1) =(a*(u*q+ r*c))" using assms a6 \<open>p+1 >0\<close>
      by (metis neq0_conv nonzero_mult_div_cancel_right of_nat_eq_0_iff of_nat_mult)
    have a8:"(a*(u+p)/(p+1))*(r+1)*(c+1) = a*(u*q+r*c)" using assms a7  \<open>p+1 >0\<close>
      by (metis of_nat_mult times_divide_eq_left)
    have a9: "(Esigma a)* Esigma(r)* Esigma(c) = a*(u*q+ r*c)" using a8 assms
        \<open> Esigma(r) = (r+1)\<close> \<open> Esigma(c) = (c+1)\<close>
      by (metis \<open>real (Esigma a) = real (a*(u + p))/real(p + 1)\<close> of_nat_eq_iff of_nat_mult)
    have a10: " Esigma(a*r*c) = a*(u*q+ r*c)" using a9 assms
        \<open>Esigma (a*r*c) = (Esigma a)*(Esigma r)*(Esigma c)\<close> by simp

    show ?thesis using a10 assms
      by (simp add: add_mult_distrib2 mult.assoc)
  qed

  show ?thesis using A B  Amicable_pair_equiv_def_conv assms One_nat_def  one_le_mult_iff
    by (smt prime_ge_1_nat)
 qed

 text \<open>By replacing the assumption that \<open>(a*u) Amic (a*p)\<close> in the above rule by te Riele with the 
 assumption that \<open>(a*u) breeder u\<close>, we obtain Borho's Rule with breeders \cite{garciaetal1}.\<close>

theorem Borho_Rule_breeders_Amicable: 
  fixes a u r c q x :: nat 
  assumes "x \<ge> 1" and "a \<ge> 1" and "u \<ge> 1"
      and "prime r" and "prime c" and  "prime q" and "r \<noteq> c" 
      and "Esigma (a*u) = a*u + a*x" "Esigma (a*u) = (Esigma a)*(x+1)" and "gcd a (r * c) =1"
      and "gcd (a*u) q = 1" and "r * c = x+u + x*u +r*x +x*c" and "q = r+c+u"
  shows "(a*u*q) Amic (a*r*c)"

proof-
  have a: "Esigma(a*u*q) = Esigma(a*u)*Esigma(q)"
    using assms gcd_Esigma_mult by simp
  have a1: "Esigma(a*r*c) = (Esigma a)*Esigma(r*c)"
    using assms gcd_Esigma_mult by (metis mult.assoc mult.commute)
  have a2: "Esigma(a*r*c) = (Esigma a)*(r+1)*(c+1)"
    using a1 assms
    by (metis mult.commute mult.left_commute prime_Esigma_mult prime_sum_div)

  have A: "Esigma (a*u*q) = Esigma(a*r*c)"
  proof-
    have d: "Esigma(a)*(r+1)*(c+1) = Esigma(a*u)*(q+1)"
    proof-
      have d1: "(r+1)*(c+1) =(x+1)*(q+1)"
      proof-
        have ce: "(r+1)*(c+1) = r*c+r+c+1" by simp
        have ce1: "(r+1)*(c+1) = x+u+x*u+r*x+x*c+r+c+1"
          using ce assms by simp
        have de: "(x+1)*(q+1) = x*q +1+x+q" by simp
        have de1: "(x+1)*(q+1) = x*(r+c+u)+1+x+ r+c+u"
          using assms de by simp
        show ?thesis using de1 ce1 add_mult_distrib2 by auto
      qed

      show ?thesis using d1 assms
        by (metis semiring_normalization_rules(18))
    qed

    show ?thesis using d a2
      by (simp add: a assms(6) prime_sum_div)
  qed

  have B: "Esigma (a*u*q) = a*u*q + a*r*c"
  proof-
    have i: "Esigma (a*u*q) = Esigma(a*u)*(q+1)"
      using a assms
      by (simp add: prime_sum_div)

    have ii:"Esigma (a*u*q) = (a*u+ a*x)*(q+1)"
      using assms i by auto

     have iii:"Esigma (a*u*q) = a*u*q +a*u+ a*x*q+ a*x"
      using assms ii add_mult_distrib by simp
    show ?thesis using iii assms
      by (smt distrib_left semiring_normalization_rules)
  qed

  show ?thesis using A B assms Amicable_pair_equiv_def_conv assms  One_nat_def one_le_mult_iff
    by (smt prime_ge_1_nat)
qed

no_notation divisor (infixr "divisor" 80)


section\<open>Acknowledgements\<close>

text
\<open>The author was supported by the ERC Advanced Grant ALEXANDRIA (Project 742178) funded by the
European Research Council and led by Professor Lawrence Paulson at the University of Cambridge, UK.
Many thanks to Lawrence Paulson for his help and suggestions. Number divisors were initially looked
up on \<^url>\<open>https://onlinemathtools.com/find-all-divisors\<close>.\<close>

end
