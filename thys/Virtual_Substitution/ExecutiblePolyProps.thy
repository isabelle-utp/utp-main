text "Executable Polynomial Properties"
theory ExecutiblePolyProps
  imports
    Polynomials.MPoly_Type_Univariate
    MPolyExtension
begin

text \<open>(Univariate) Polynomial hiding\<close>

lifting_update poly.lifting
lifting_forget poly.lifting

text \<open>\<close>

no_notation MPoly_Type.div (infixl "div" 70)
no_notation MPoly_Type.mod (infixl "mod" 70)

subsection "Lemmas with Monomial and Monomials"

lemma of_nat_monomial: "of_nat p = monomial p 0"
  by (auto simp: poly_mapping_eq_iff lookup_of_nat fun_eq_iff lookup_single)

lemma of_nat_times_monomial: "of_nat p * monomial c i = monomial (p*c) i"
  by (auto simp: poly_mapping_eq_iff prod_fun_def fun_eq_iff of_nat_monomial
      lookup_single mult_single)

lemma monomial_adds_nat_iff: "monomial p i adds c \<longleftrightarrow> lookup c i \<ge> p" for p::"nat"
  apply (auto simp: adds_def lookup_add)
  by (metis add.left_commute nat_le_iff_add remove_key_sum single_add)

lemma update_minus_monomial: "Poly_Mapping.update k i (m - monomial i k) = Poly_Mapping.update k i m"
  by (auto simp: poly_mapping_eq_iff lookup_update update.rep_eq fun_eq_iff lookup_minus
      lookup_single)

lemma monomials_Var: "monomials (Var x::'a::zero_neq_one mpoly) = {Poly_Mapping.single x 1}"
  by transfer (auto simp: Var\<^sub>0_def)

lemma monomials_Const: "monomials (Const x) = (if x = 0 then {} else {0})"
  by transfer' (auto simp: Const\<^sub>0_def)

lemma coeff_eq_zero_iff: "MPoly_Type.coeff c p = 0 \<longleftrightarrow> p \<notin> monomials c"
  by transfer (simp add: not_in_keys_iff_lookup_eq_zero)

lemma monomials_1[simp]: "monomials 1 = {0}"
  by transfer auto

lemma monomials_and_monoms: 
  shows "(k \<in> monomials m) = (\<exists> (a::nat). a \<noteq> 0 \<and> (monomials (MPoly_Type.monom k a)) \<subseteq> monomials m)"
proof - 
  show ?thesis using monomials_monom by auto
qed

lemma mult_monomials_dir_one:
  shows "monomials (p*q) \<subseteq> {a+b | a b . a \<in> monomials p \<and> b \<in> monomials q}"
  using monomials_and_monoms mult_monom
  by (simp add: keys_mult monomials.rep_eq times_mpoly.rep_eq) 

lemma monom_eq_zero_iff[simp]: "MPoly_Type.monom a b = 0 \<longleftrightarrow> b = 0"
  by (metis MPolyExtension.coeff_monom MPolyExtension.monom_zero)

lemma update_eq_plus_monomial:
  "v \<ge> lookup m k \<Longrightarrow> Poly_Mapping.update k v m = m + monomial (v - lookup m k) k"
  for v n::nat
  by transfer auto

lemma coeff_monom_mult':
  "MPoly_Type.coeff ((MPoly_Type.monom m' a) * q) (m'm)  = a * MPoly_Type.coeff q (m'm - m')"
  if *: "m'm = m' + (m'm - m')"
  by (subst *) (rule More_MPoly_Type.coeff_monom_mult)

lemma monomials_zero[simp]: "monomials 0 = {}"
  by transfer auto

lemma in_monomials_iff: "x \<in> monomials m \<longleftrightarrow> MPoly_Type.coeff m x \<noteq> 0"
  using coeff_eq_zero_iff[of m x] by auto

lemma monomials_monom_mult: "monomials (MPoly_Type.monom mon a * q) = (if a = 0 then {} else (+) mon ` monomials q)"
  for q::"'a::semiring_no_zero_divisors mpoly"
  apply auto
  subgoal by transfer' (auto elim!: in_keys_timesE)
  subgoal by (simp add: in_monomials_iff More_MPoly_Type.coeff_monom_mult)
  done

subsection "Simplification Lemmas for Const 0 and Const 1"
lemma add_zero : "P + Const 0 = P"
proof -
  have h:"P + 0 = P" using add_0_right by auto
  show ?thesis unfolding Const_def using h by (simp add: Const\<^sub>0_zero zero_mpoly.abs_eq)
qed

(* example *)
lemma add_zero_example : "((Var 0)^2 - (Const 1)) + Const 0 = ((Var 0)^2 - (Const 1))"
proof -
  show ?thesis by (simp add : add_zero)
qed

lemma mult_zero_left : "Const 0 * P = Const 0"
proof -
  have h:"0*P = 0" by simp
  show ?thesis unfolding Const_def using h by (simp add: Const\<^sub>0_zero zero_mpoly_def)
qed

lemma mult_zero_right : "P * Const 0 = Const 0"
  by (metis mult_zero_left mult_zero_right)

lemma mult_one_left : "Const 1 * (P :: real mpoly) = P"
  by (simp add: Const.abs_eq Const\<^sub>0_one one_mpoly_def)

lemma mult_one_right : "(P::real mpoly) * Const 1 = P"
  by (simp add: Const.abs_eq Const\<^sub>0_one one_mpoly_def)


subsection "Coefficient Lemmas"
lemma coeff_zero[simp]: "MPoly_Type.coeff 0 x = 0"
  by transfer auto

lemma coeff_sum: "MPoly_Type.coeff (sum f S) x = sum (\<lambda>i. MPoly_Type.coeff (f i) x) S"
  apply (induction S rule: infinite_finite_induct) 
    apply (auto)
  by (metis More_MPoly_Type.coeff_add)

lemma coeff_mult_Var: "MPoly_Type.coeff (x * Var i ^ p) c = (MPoly_Type.coeff x (c - monomial p i) when lookup c i \<ge> p)"
  by transfer'
    (auto simp: Var\<^sub>0_def pprod.monomial_power lookup_times_monomial_right
      of_nat_times_monomial monomial_adds_nat_iff)

lemma lookup_update_self[simp]: "Poly_Mapping.update i (lookup m i) m = m"
  by (auto simp: lookup_update intro!: poly_mapping_eqI)

lemma coeff_Const: "MPoly_Type.coeff (Const p) m = (p when m = 0)"
  by transfer' (auto simp: Const\<^sub>0_def lookup_single)

lemma coeff_Var: "MPoly_Type.coeff (Var p) m = (1 when m = monomial 1 p)"
  by transfer' (auto simp: Var\<^sub>0_def lookup_single when_def)

subsection "Miscellaneous"
lemma update_0_0[simp]: "Poly_Mapping.update x 0 0 = 0"
  by (metis lookup_update_self lookup_zero)

lemma mpoly_eq_iff: "p = q \<longleftrightarrow> (\<forall>m. MPoly_Type.coeff p m = MPoly_Type.coeff q m)"
  by transfer (auto simp: poly_mapping_eqI)

lemma power_both_sides :
  assumes Ah : "(A::real) \<ge>0"
  assumes Bh : "(B::real) \<ge>0"
  shows "(A\<le>B) = (A^2\<le>B^2)"
  using Ah Bh by (meson power2_le_imp_le power_mono)

lemma in_list_induct_helper: 
  assumes "set(xs)\<subseteq>X"
  assumes  "P []"
  assumes "(\<And>x. x\<in>X \<Longrightarrow> ( \<And>xs. P xs \<Longrightarrow> P (x # xs)))"
  shows "P xs" using assms(1)
proof(induction xs)
  case Nil
  then show ?case using assms by auto
next
  case (Cons a xs)
  then show ?case using assms(3) by auto
qed

theorem in_list_induct [case_names Nil Cons]: 
  assumes  "P []"
  assumes "(\<And>x. x\<in>set(xs) \<Longrightarrow> ( \<And>xs. P xs \<Longrightarrow> P (x # xs)))"
  shows "P xs"
  using in_list_induct_helper[of xs "set(xs)" P] using assms by auto

subsubsection "Keys and vars"

lemma inKeys_inVars : "a\<noteq>0 \<Longrightarrow> x \<in> keys m \<Longrightarrow> x \<in> vars(MPoly_Type.monom m a)"
  by(simp add: vars_def)

lemma notInKeys_notInVars : "x \<notin> keys m \<Longrightarrow> x \<notin> vars(MPoly_Type.monom m a)"
  by(simp add: vars_def)

lemma lookupNotIn : "x \<notin> keys m \<Longrightarrow> lookup m x = 0"
  by (simp add: in_keys_iff)

subsection "Degree Lemmas"

lemma degree_le_iff: "MPoly_Type.degree p x \<le> k \<longleftrightarrow> (\<forall>m\<in>monomials p. lookup m x \<le> k)"
  by transfer simp

lemma degree_less_iff: "MPoly_Type.degree p x < k \<longleftrightarrow> (k>0 \<and> (\<forall>m\<in>monomials p. lookup m x < k))"
  by (transfer fixing: k) (cases "k = 0"; simp)  

lemma degree_ge_iff: "k > 0 \<Longrightarrow> MPoly_Type.degree p x \<ge> k \<longleftrightarrow> (\<exists>m\<in>monomials p. lookup m x \<ge> k)"
  using Max_ge_iff by (meson degree_less_iff not_less) 

lemma degree_greater_iff: "MPoly_Type.degree p x > k \<longleftrightarrow> (\<exists>m\<in>monomials p. lookup m x > k)"
  by transfer' (auto simp: Max_gr_iff)

lemma degree_eq_iff:
  "MPoly_Type.degree p x = k \<longleftrightarrow> (if k = 0
    then (\<forall>m\<in>monomials p. lookup m x = 0)
    else (\<exists>m\<in>monomials p. lookup m x = k) \<and> (\<forall>m\<in>monomials p. lookup m x \<le> k))"
  by (subst eq_iff) (force simp: degree_le_iff degree_ge_iff intro!: antisym)

declare poly_mapping.lookup_inject[simp del]

lemma lookup_eq_and_update_lemma: "lookup m var = deg \<and> Poly_Mapping.update var 0 m = x \<longleftrightarrow>
  m = Poly_Mapping.update var deg x \<and> lookup x var = 0"
  unfolding poly_mapping_eq_iff
  by (force simp: update.rep_eq fun_eq_iff)


lemma degree_const : "MPoly_Type.degree (Const (z::real)) (x::nat) = 0"
  by (simp add: degree_eq_iff monomials_Const)

lemma degree_one : "MPoly_Type.degree (Var x :: real mpoly) x = 1"
  by(simp add: degree_eq_iff monomials_Var)

subsection "Lemmas on treating a multivariate polynomial as univariate "
lemma coeff_isolate_variable_sparse:
  "MPoly_Type.coeff (isolate_variable_sparse p var deg) x =
  (if lookup x var = 0
  then MPoly_Type.coeff p (Poly_Mapping.update var deg x)
  else 0)"
  apply (transfer fixing: x var deg p)
  unfolding lookup_sum
  unfolding lookup_single
  apply (auto simp: when_def)
   apply (subst sum.inter_filter[symmetric])
  subgoal by simp
  subgoal by (simp add: lookup_eq_and_update_lemma Collect_conv_if)
  by (auto intro!: sum.neutral simp add: lookup_update)

lemma isovarspar_sum: 
  "isolate_variable_sparse (p+q) var deg = 
  isolate_variable_sparse (p) var deg
  + isolate_variable_sparse (q) var deg"
  apply (auto simp add: mpoly_eq_iff coeff_isolate_variable_sparse )
   apply (metis More_MPoly_Type.coeff_add coeff_isolate_variable_sparse)
  by (metis More_MPoly_Type.coeff_add add.comm_neutral coeff_isolate_variable_sparse less_numeral_extra(3))

lemma isolate_zero[simp]: "isolate_variable_sparse 0 var n = 0"
  by transfer' (auto simp: mpoly_eq_iff)

lemma coeff_isolate_variable_sparse_minus_monomial:
  "MPoly_Type.coeff (isolate_variable_sparse mp var i) (m - monomial i var) =
  (if lookup m var \<le> i then MPoly_Type.coeff mp (Poly_Mapping.update var i m) else 0)"
  by (simp add: coeff_isolate_variable_sparse lookup_minus update_minus_monomial)

lemma sum_over_zero: "(mp::real mpoly) = (\<Sum>i::nat \<le>MPoly_Type.degree mp x. isolate_variable_sparse mp x i * Var x^i)"
  by (auto simp add: mpoly_eq_iff coeff_sum coeff_mult_Var if_if_eq_conj not_le
      coeff_isolate_variable_sparse_minus_monomial when_def lookup_update degree_less_iff
      simp flip: eq_iff
      intro!: coeff_not_in_monomials)

lemma const_lookup_zero : "isolate_variable_sparse (Const p ::real mpoly) (x::nat) (0::nat) = Const p"
  by (auto simp: mpoly_eq_iff coeff_isolate_variable_sparse coeff_Const when_def)
    (metis lookup_update_self)

lemma const_lookup_suc : "isolate_variable_sparse (Const p :: real mpoly) x (Suc i) = 0"
  apply(auto simp add: mpoly_eq_iff coeff_isolate_variable_sparse coeff_Const when_def)
  by (metis lookup_update lookup_zero nat.distinct(1))

lemma isovar_greater_degree : "\<forall>i > MPoly_Type.degree p var. isolate_variable_sparse p var i = 0"
  apply(auto simp add: mpoly_eq_iff coeff_isolate_variable_sparse degree_less_iff)
  by (metis coeff_not_in_monomials less_irrefl_nat lookup_update)

lemma isolate_var_0 : "isolate_variable_sparse (Var x::real mpoly) x 0 = 0"
  apply(auto simp add: mpoly_eq_iff coeff_isolate_variable_sparse coeff_Var when_def)
  by (metis gr0I lookup_single_eq lookup_update_self n_not_Suc_n)

lemma isolate_var_one : "isolate_variable_sparse (Var x :: real mpoly) x 1 = 1"
  by (auto simp add: mpoly_eq_iff coeff_isolate_variable_sparse coeff_Var coeff_eq_zero_iff)
    (smt More_MPoly_Type.coeff_monom One_nat_def add_diff_cancel_left' lookup_eq_and_update_lemma
      lookup_single_eq lookup_update_self monom_one plus_1_eq_Suc single_diff single_zero update_minus_monomial)

lemma isovarspase_monom :
  assumes notInKeys : "x \<notin> keys m"
  assumes notZero : "a \<noteq> 0"
  shows "isolate_variable_sparse (MPoly_Type.monom m a) x 0 = (MPoly_Type.monom m a :: real mpoly)"
  using assms
  by (auto simp add: mpoly_eq_iff coeff_isolate_variable_sparse coeff_eq_zero_iff in_keys_iff)
    (metis lookup_update_self)

lemma isolate_variable_spase_zero : "lookup m x = 0 \<Longrightarrow>
    insertion (nth L) ((MPoly_Type.monom m a)::real mpoly) = 0 \<Longrightarrow>
    a \<noteq> 0 \<Longrightarrow> insertion (nth L) (isolate_variable_sparse (MPoly_Type.monom m a) x 0) = 0"
  by (simp add: isovarspase_monom lookup_eq_zero_in_keys_contradict notInKeys_notInVars)

lemma isovarsparNotIn : "x \<notin> vars (p::real mpoly) \<Longrightarrow> isolate_variable_sparse p x 0 = p"
proof(induction p rule: mpoly_induct)
  case (monom m a)
  then show ?case
    apply(cases "a=0")
    by (simp_all add: isovarspase_monom vars_monom_keys)
next
  case (sum p1 p2 m a)
  then show ?case 
    by (simp add: monomials.rep_eq vars_add_monom isovarspar_sum)
qed


lemma degree0isovarspar :
  assumes deg0 : "MPoly_Type.degree (p::real mpoly) x = 0"
  shows "isolate_variable_sparse p x 0 = p"
proof -
  have h1 : "p = (\<Sum>i::nat \<le>MPoly_Type.degree p x. isolate_variable_sparse p x i * Var x ^ i)"
    using sum_over_zero by auto
  have h2a : "\<forall>f. (\<Sum>i::nat \<le>0. f i) = f 0"
    apply(simp add: sum_def)
    by (metis add.right_neutral comm_monoid_add_class.sum_def finite.emptyI insert_absorb insert_not_empty sum.empty sum.insert)
  have h2 : "p = isolate_variable_sparse p x 0 * Var x ^ 0"
    using deg0 h1 h2a by auto
  show ?thesis using h2
    by auto 
qed


subsection "Summation Lemmas"

lemma summation_normalized :
  assumes nonzero : "(B ::real) \<noteq>0"
  shows "(\<Sum>i = 0..<((n::nat)+1). (f i :: real) * B ^ (n - i)) = (\<Sum>i = 0..<(n+1). (f i) / (B ^ i)) * (B^n)"
proof -
  have h1a : "\<forall>x::real. ((\<Sum>i = 0..<(n+1). (f i) / (B ^ i)) * x = (\<Sum>i = 0..<(n+1). ((f i) / (B ^ i)) * x))"  
    apply(induction n )
     apply(auto)
    by (simp add: distrib_right)
  have h1 : "(\<Sum>i = 0..<(n+1). (f i) / (B ^ i)) * (B^n) = (\<Sum>i = 0..<(n+1). ((f i) / (B ^ i)) * (B^n))"
    using h1a by auto
  have h2 : "(\<Sum>i = 0..<(n+1). ((f i) / (B ^ i)) * (B^n)) = (\<Sum>i = 0..<(n+1). (f i) * ((B^n) / (B ^ i)))"
    by auto
  have h3 : "(\<Sum>i = 0..<(n+1). (f i) * ((B^n) / (B ^ i))) = (\<Sum>i = 0..<(n+1). (f i) * B ^ (n - i))"
    using add.right_neutral nonzero power_diff by fastforce
  show ?thesis using h1 h2 h3 by auto
qed

lemma normalize_summation :
  assumes nonzero : "(B::real)\<noteq>0"
  shows "(\<Sum>i = 0..<n+1. f i * B ^ (n - i))= 0
          \<longleftrightarrow>
  (\<Sum>i = 0..<(n::nat)+1. (f i::real) / (B ^ i)) = 0"
proof - 
  have pow_zero : "\<forall>i. B^(i :: nat)\<noteq>0" using nonzero by(auto)
  have single_division_zero : "\<forall>X. B*(X::real)=0 \<longleftrightarrow> X=0" using nonzero by(auto)
  have h1: "(\<Sum>i = 0..<n+1. (f i) / (B ^ i)) = 0 \<longleftrightarrow> ((\<Sum>i = 0..<n+1. (f i) / (B ^ i)))*B^n = 0"
    using nonzero single_division_zero by(auto)
  have h2: "((\<Sum>i = 0..<n+1. (f i) / (B ^ i))*(B^n)) = ((\<Sum>i = 0..<n+1. (f i) * (B ^ (n- i))))"
    using summation_normalized nonzero by auto
  show ?thesis using h1 h2 by auto
qed


lemma normalize_summation_less :
  assumes nonzero : "(B::real)\<noteq>0"
  shows "(\<Sum>i = 0..<(n+1). (f i) * B ^ (n - i)) * B ^ (n mod 2) < 0
          \<longleftrightarrow>
  (\<Sum>i = 0..<((n::nat)+1). (f i::real) / (B ^ i)) < 0"
proof - 
  have h1 : "(\<Sum>i = 0..<(n+1). (f i) * B ^ (n - i)) * B ^ (n mod 2) < 0
        \<longleftrightarrow>  (\<Sum>i = 0..<(n+1). (f i) / (B ^ i)) * (B^n) * B ^ (n mod 2) < 0"
    using summation_normalized nonzero by auto
  have h2a : "n mod 2 = 0 \<or> n mod 2 = 1" by auto
  have h2b : "n mod 2 = 1 \<Longrightarrow> odd n" by auto
  have h2c : "(B^n) * B ^ (n mod 2) > 0"
    using h2a h2b apply auto
    using nonzero apply presburger
    by (metis even_Suc mult.commute nonzero power_Suc zero_less_power_eq)    
  have h2 : "\<forall>x. ((x * (B^n) * B ^ (n mod 2) < 0) = (x<0))"
    using h2c using mult.assoc by (metis mult_less_0_iff not_square_less_zero) 
  show ?thesis using h1 h2 by auto
qed

subsection "Additional Lemmas with Vars"

lemma not_in_isovarspar : "isolate_variable_sparse (p::real mpoly) var x = (q::real mpoly) \<Longrightarrow> var\<notin>(vars q)"
  apply(simp add: isolate_variable_sparse_def vars_def)
proof -
  assume a1: "MPoly (\<Sum>m | m \<in> monomials p \<and> lookup m var = x. monomial (MPoly_Type.coeff p m) (Poly_Mapping.update var 0 m)) = q"
  { fix pp :: "nat \<Rightarrow>\<^sub>0 nat"
    have "isolate_variable_sparse p var x = q"
      using a1 isolate_variable_sparse.abs_eq by blast
    then have "var \<notin> keys pp \<or> pp \<notin> keys (mapping_of q)"
      by (metis (no_types) coeff_def coeff_isolate_variable_sparse in_keys_iff) }
  then show "\<forall>p\<in>keys (mapping_of q). var \<notin> keys p"
    by meson
qed 

lemma not_in_add : "var\<notin>(vars (p::real mpoly)) \<Longrightarrow> var\<notin>(vars (q::real mpoly)) \<Longrightarrow> var\<notin>(vars (p+q))"
  by (meson UnE in_mono vars_add)

lemma not_in_mult : "var\<notin>(vars (p::real mpoly)) \<Longrightarrow> var\<notin>(vars (q::real mpoly)) \<Longrightarrow> var\<notin>(vars (p*q))"
  by (meson UnE in_mono vars_mult)

lemma not_in_neg : "var\<notin>(vars(p::real mpoly)) \<longleftrightarrow> var\<notin>(vars(-p))"
proof -
  have h: "var \<notin> (vars (-1::real mpoly))" by (metis add_diff_cancel_right' add_neg_numeral_special(8) isolate_var_one isolate_zero isovarsparNotIn isovarspar_sum not_in_isovarspar)
  show ?thesis using not_in_mult using h by fastforce
qed

lemma not_in_sub : "var\<notin>(vars (p::real mpoly)) \<Longrightarrow> var\<notin>(vars (q::real mpoly)) \<Longrightarrow> var\<notin>(vars (p-q))"
  using not_in_add not_in_neg by fastforce


lemma not_in_pow : "var\<notin>(vars(p::real mpoly)) \<Longrightarrow> var\<notin>(vars(p^i))"
proof (induction i)
  case 0
  then show ?case using isolate_var_one not_in_isovarspar
    by (metis power_0) 
next 
  case (Suc i)
  then show ?case using not_in_mult by simp
qed

lemma not_in_sum_var: "(\<forall>i. var\<notin>(vars(f(i)::real mpoly))) \<Longrightarrow> var\<notin>(vars(\<Sum>i\<in>{0..<(n::nat)}.f(i)))"
proof (induction n)
  case 0
  then show ?case using isolate_zero not_in_isovarspar by fastforce
next
  case (Suc n)
  have h1: "(sum f {0..<Suc n}) = (sum f {0..< n}) + (f n)" using sum.atLeast0_lessThan_Suc by blast
  have h2: "var \<notin> vars (f n)" by (simp add: Suc.prems)
  then show ?case using h1 vars_add by (simp add: Suc.IH Suc.prems not_in_add)
qed

lemma not_in_sum : "(\<forall>i. var\<notin>(vars(f(i)::real mpoly))) \<Longrightarrow> \<forall>(n::nat). var\<notin>(vars(\<Sum>i\<in>{0..<n}.f(i)))"
  using not_in_sum_var by blast

lemma not_contains_insertion_helper : 
  "\<forall>x\<in>keys (mapping_of p). var \<notin> keys x \<Longrightarrow>
         (\<And>k f. (k \<notin> keys f) = (lookup f k = 0)) \<Longrightarrow>
         lookup (mapping_of p) a = 0 \<or>
         (\<Prod>aa. (if aa < length L then L[var := y] ! aa else 0) ^ lookup a aa) =
         (\<Prod>aa. (if aa < length L then L[var := x] ! aa else 0) ^ lookup a aa)"
  apply(cases "lookup (mapping_of p) a = 0") 
   apply auto
  apply(rule Prod_any.cong) 
  apply auto
  using lookupNotIn nth_list_update_neq power_0 by smt

lemma not_contains_insertion : 
  assumes notIn : "var \<notin> vars (p:: real mpoly)"
  assumes exists : "insertion (nth_default 0 (list_update L var x)) p = val"
  shows "insertion (nth_default 0 (list_update L var y)) p = val"
  using notIn exists
  apply(simp add: insertion_def insertion_aux_def insertion_fun_def)
  unfolding vars_def nth_default_def
  using not_in_keys_iff_lookup_eq_zero  
  apply auto
  apply(rule Sum_any.cong) 
  apply simp
  using not_contains_insertion_helper[of p var _ L y x]
proof -
  fix a :: "nat \<Rightarrow>\<^sub>0 nat"
  assume a1: "\<forall>x\<in>keys (mapping_of p). var \<notin> keys x"
  assume "\<And>k f. ((k::'a) \<notin> keys f) = (lookup f k = 0)"
  then show "lookup (mapping_of p) a = 0 \<or> (\<Prod>n. (if n < length L then L[var := y] ! n else 0) ^ lookup a n) = (\<Prod>n. (if n < length L then L[var := x] ! n else 0) ^ lookup a n)"
    using a1 \<open>\<And>a. \<lbrakk>\<forall>x\<in>keys (mapping_of p). var \<notin> keys x; \<And>k f. (k \<notin> keys f) = (lookup f k = 0)\<rbrakk> \<Longrightarrow> lookup (mapping_of p) a = 0 \<or> (\<Prod>aa. (if aa < length L then L[var := y] ! aa else 0) ^ lookup a aa) = (\<Prod>aa. (if aa < length L then L[var := x] ! aa else 0) ^ lookup a aa)\<close> by blast
qed


subsection "Insertion Lemmas"
lemma insertion_sum_var : "((insertion f (\<Sum>i\<in>{0..<(n::nat)}.g(i))) = (\<Sum>i\<in>{0..<n}. insertion f (g i)))"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case by (simp add: insertion_add)
qed

(* changed to explicitly typecast n as a nat *)
lemma insertion_sum : "\<forall>(n::nat). ((insertion f (\<Sum>i\<in>{0..<n}.g(i))) = (\<Sum>i\<in>{0..<n}. insertion f (g i)))"
  using insertion_sum_var by blast


lemma insertion_sum' : "\<And>(n::nat). ((insertion f (\<Sum>i\<le>n. g(i))) = (\<Sum>i\<le>n. insertion f (g i)))"
  by (metis (no_types, lifting) fun_sum_commute insertion_add insertion_zero sum.cong) 

lemma insertion_pow : "insertion f (p^i) = (insertion f p)^i"
proof (induction i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case by (simp add: insertion_mult)
qed

lemma insertion_neg : "insertion f (-p) = -insertion f p"
  by (metis add.inverse_inverse insertionNegative)

lemma insertion_var : 
  "length L > var \<Longrightarrow> insertion (nth_default 0 (list_update L var x)) (Var var) = x"
  by (auto simp: monomials_Var coeff_Var insertion_code nth_default_def)

lemma insertion_var_zero : "insertion (nth_default 0 (x#xs)) (Var 0) = x" using insertion_var
  by fastforce

lemma notIn_insertion_sub : "x\<notin>vars(p::real mpoly) \<Longrightarrow> x\<notin>vars(q::real mpoly)
                             \<Longrightarrow> insertion f (p-q) = insertion f p - insertion f q"
  by (metis ab_group_add_class.ab_diff_conv_add_uminus insertion_add insertion_neg)

lemma insertion_sub : "insertion f (A-B :: real mpoly) = insertion f A - insertion f B"
  using insertion_neg insertion_add
  by (metis uminus_add_conv_diff)

lemma insertion_four : "insertion ((nth_default 0) xs) 4 = 4"
  by (metis (no_types, lifting) insertion_add insertion_one numeral_plus_numeral one_add_one semiring_norm(2) semiring_norm(6))

lemma insertion_add_ind_basecase:
  "insertion (nth (list_update L var x)) ((\<Sum>i::nat \<le> 0. isolate_variable_sparse p var i * (Var var)^i))
  = (\<Sum>i = 0..<(0+1).  insertion (nth (list_update L var x)) (isolate_variable_sparse p var i * (Var var)^i))"
proof - 
  have h1: "((\<Sum>i::nat \<le> 0. isolate_variable_sparse p var i * (Var var)^i))
   = (isolate_variable_sparse p var 0 * (Var var)^0)"
    by auto
  show ?thesis using h1
    by auto 
qed

lemma insertion_add_ind:
  "insertion (nth_default 0 (list_update L var x)) ((\<Sum>i::nat \<le> d. isolate_variable_sparse p var i * (Var var)^i))
  = (\<Sum>i = 0..<(d+1).  insertion (nth_default 0 (list_update L var x)) (isolate_variable_sparse p var i * (Var var)^i))"
proof (induction d)
  case 0
  then show ?case using insertion_add_ind_basecase nth_default_def
    by auto
next
  case (Suc n)
  then show ?case using insertion_add apply auto
    by (simp add: insertion_add)
qed

lemma sum_over_degree_insertion :
  assumes lLength : "length L > var"
  assumes deg : "MPoly_Type.degree (p::real mpoly) var = d"
  shows "(\<Sum>i = 0..<(d+1). insertion (nth_default 0 (list_update L var x)) (isolate_variable_sparse p var i) * (x^i))
          = insertion (nth_default 0 (list_update L var x)) p"
proof -
  have h1: "(p::real mpoly) = (\<Sum>i::nat \<le>(MPoly_Type.degree p var). isolate_variable_sparse p var i * (Var var)^i)" using sum_over_zero by auto
  have h2: "insertion (nth_default 0 (list_update L var x)) p = 
    insertion (nth_default 0 (list_update L var x)) ((\<Sum>i::nat \<le> d. isolate_variable_sparse p var i * (Var var)^i))" using h1 deg by auto
  have h3:  "insertion (nth_default 0 (list_update L var x)) p = (\<Sum>i = 0..<(d+1).  insertion (nth_default 0 (list_update L var x)) (isolate_variable_sparse p var i * (Var var)^i))"
    using h2 insertion_add_ind nth_default_def
    by (simp add: )
  show ?thesis using h3 insertion_var insertion_pow
    by (metis (no_types, lifting) insertion_mult lLength sum.cong)
qed



lemma insertion_isovarspars_free :
  "insertion (nth_default 0 (list_update L var x)) (isolate_variable_sparse (p::real mpoly) var (i::nat))
  =insertion (nth_default 0 (list_update L var y)) (isolate_variable_sparse (p::real mpoly) var (i::nat))"
proof -
  have h : "var \<notin> vars(isolate_variable_sparse (p::real mpoly) var (i::nat))"
    by (simp add: not_in_isovarspar)
  then show ?thesis using not_contains_insertion
    by blast 
qed
lemma insertion_zero : "insertion f (Const 0 ::real mpoly) = 0"
  by (metis add_cancel_right_right add_zero insertion_zero)

lemma insertion_one : "insertion f (Const 1 ::real mpoly) = 1"
  by (metis insertion_one mult.right_neutral mult_one_left)

lemma insertion_const : "insertion f (Const c::real mpoly) = (c::real)"
  by (auto simp: monomials_Const coeff_Const insertion_code)


subsection "Putting Things Together"
subsubsection "More Degree Lemmas"
lemma degree_add_leq : 
  assumes h1 : "MPoly_Type.degree a var \<le> x"
  assumes h2 : "MPoly_Type.degree b var \<le> x"
  shows "MPoly_Type.degree (a+b) var \<le> x"
  using degree_eq_iff coeff_add coeff_not_in_monomials
  by (smt (z3) More_MPoly_Type.coeff_add add.left_neutral coeff_eq_zero_iff degree_le_iff h1 h2)

lemma degree_add_less : 
  assumes h1 : "MPoly_Type.degree a var < x"
  assumes h2 : "MPoly_Type.degree b var < x"
  shows "MPoly_Type.degree (a+b) var < x"
proof -
  obtain pp :: "nat \<Rightarrow> nat \<Rightarrow> 'a mpoly \<Rightarrow> nat \<Rightarrow>\<^sub>0 nat" where
    "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> monomials x2 \<and> \<not> lookup v3 x1 < x0) = (pp x0 x1 x2 \<in> monomials x2 \<and> \<not> lookup (pp x0 x1 x2) x1 < x0)"
    by moura
  then have f1: "\<forall>m n na. (\<not> MPoly_Type.degree m n < na \<or> 0 < na \<and> (\<forall>p. p \<notin> monomials m \<or> lookup p n < na)) \<and> (MPoly_Type.degree m n < na \<or> \<not> 0 < na \<or> pp na n m \<in> monomials m \<and> \<not> lookup (pp na n m) n < na)"
    by (metis (no_types) degree_less_iff)
  then have "0 < x \<and> (\<forall>p. p \<notin> monomials a \<or> lookup p var < x)"
    using assms(1) by presburger
  then show ?thesis
    using f1 by (metis MPolyExtension.coeff_add add.left_neutral assms(2) coeff_eq_zero_iff)
qed

lemma degree_sum : "(\<forall>i\<in>{0..n::nat}. MPoly_Type.degree (f i :: real mpoly) var \<le> x) \<Longrightarrow> (MPoly_Type.degree (\<Sum>x\<in>{0..n}. f x) var) \<le> x"
proof(induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case by(simp add: degree_add_leq)
qed

lemma degree_sum_less : "(\<forall>i\<in>{0..n::nat}. MPoly_Type.degree (f i :: real mpoly) var < x) \<Longrightarrow> (MPoly_Type.degree (\<Sum>x\<in>{0..n}. f x) var) < x"
proof(induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case by(simp add: degree_add_less)
qed


lemma varNotIn_degree : 
  assumes "var \<notin> vars p"
  shows "MPoly_Type.degree p var = 0"
proof-
  have "\<forall>m\<in>monomials p. lookup m var = 0"
    using assms unfolding vars_def keys_def
    using monomials.rep_eq by fastforce
  then show ?thesis
    using degree_less_iff by blast
qed

lemma degree_mult_leq : 
  assumes pnonzero: "(p::real mpoly)\<noteq>0"
  assumes qnonzero: "(q::real mpoly)\<noteq>0"
  shows "MPoly_Type.degree ((p::real mpoly) * (q::real mpoly)) var \<le> (MPoly_Type.degree p var) + (MPoly_Type.degree q var)"
proof(cases "MPoly_Type.degree (p*q) var =0")
  case True
  then show ?thesis by simp
next
  case False
  have hp: "\<forall>m\<in>monomials p. lookup m var \<le> MPoly_Type.degree p var" using degree_eq_iff
    by (metis zero_le) 
  have hq: "\<forall>m\<in>monomials q. lookup m var \<le> MPoly_Type.degree q var" using degree_eq_iff
    by (metis zero_le) 
  have hpq: "\<forall>m\<in>{a+b | a b . a \<in> monomials p \<and> b \<in> monomials q}.
      lookup m var \<le> (MPoly_Type.degree p var) + (MPoly_Type.degree q var)"
    by (smt add_le_mono hp hq mem_Collect_eq plus_poly_mapping.rep_eq)
  have h1: "(\<forall>m\<in>monomials (p*q). lookup m var \<le> (MPoly_Type.degree p var) + (MPoly_Type.degree q var))" 
    using mult_monomials_dir_one hpq
    by blast 
  then show ?thesis using h1 degree_eq_iff False
    by (simp add: degree_le_iff)
qed

lemma degree_exists_monom: 
  assumes "p\<noteq>0"
  shows  "\<exists>m\<in>monomials p. lookup m var = MPoly_Type.degree p var"
proof(cases "MPoly_Type.degree p var =0")
  case True
  have h1: "\<exists>m\<in>monomials p. lookup m var = 0" unfolding monomials_def
    by (metis True assms(1) aux degree_eq_iff in_keys_iff mapping_of_inject monomials.rep_eq monomials_def zero_mpoly.rep_eq)
  then show ?thesis using h1
    using True by simp
next
  case False
  then show ?thesis using degree_eq_iff assms(1) apply(auto)
    by (metis degree_eq_iff dual_order.strict_iff_order) 
qed

lemma degree_not_exists_monom: 
  assumes "p\<noteq>0"
  shows  "\<not> (\<exists> m\<in>monomials p. lookup m var > MPoly_Type.degree p var)"
proof - 
  show ?thesis using degree_less_iff by blast 
qed

lemma degree_monom: "MPoly_Type.degree (MPoly_Type.monom x y) v = (if y = 0 then 0 else lookup x v)"
  by (auto simp: degree_eq_iff)

lemma degree_plus_disjoint:
  "MPoly_Type.degree (p + MPoly_Type.monom m c) v = max (MPoly_Type.degree p v) (MPoly_Type.degree (MPoly_Type.monom m c) v)"
  if "m \<notin> monomials p"
  for p::"real mpoly"
  using that
  apply (subst degree_eq_iff)
  apply (auto simp: monomials_add_disjoint)
            apply (auto simp: degree_eq_iff degree_monom)
       apply (metis MPoly_Type.degree_zero degree_exists_monom less_numeral_extra(3))
  using degree_le_iff apply blast
  using degree_eq_iff
     apply (metis max_def neq0_conv)
    apply (metis degree_eq_iff max.coboundedI1 neq0_conv)
   apply (metis MPoly_Type.degree_zero degree_exists_monom max_def zero_le)
  using degree_le_iff max.cobounded1 by blast

subsubsection "More isolate\\_variable\\_sparse lemmas"

lemma isolate_variable_sparse_ne_zeroD:
  "isolate_variable_sparse mp v x \<noteq> 0 \<Longrightarrow> x \<le> MPoly_Type.degree mp v"
  using isovar_greater_degree leI by blast

context includes poly.lifting begin
lift_definition mpoly_to_nested_poly::"'a::comm_monoid_add mpoly \<Rightarrow> nat \<Rightarrow> 'a mpoly Polynomial.poly" is
  "\<lambda>(mp::'a mpoly) (v::nat) (p::nat). isolate_variable_sparse mp v p"
  \<comment> \<open>note \<^const>\<open>extract_var\<close> nests the other way around\<close>
  unfolding MOST_iff_cofinite
proof -
  fix mp::"'a mpoly" and v::nat
  have "{p. isolate_variable_sparse mp v p \<noteq> 0} \<subseteq> {0..MPoly_Type.degree mp v}"
    (is "?s \<subseteq> _")
    by (auto dest!: isolate_variable_sparse_ne_zeroD)
  also have "finite \<dots>" by simp
  finally (finite_subset) show "finite ?s" .
qed

lemma degree_eq_0_mpoly_to_nested_polyI:
  "mpoly_to_nested_poly mp v = 0 \<Longrightarrow> MPoly_Type.degree mp v = 0"
  apply transfer'
  apply (simp add: degree_eq_iff)
  apply transfer'
  apply (auto simp: fun_eq_iff)
proof -
  fix mpa :: "'a mpoly" and va :: nat and m :: "nat \<Rightarrow>\<^sub>0 nat"
  assume a1: "\<forall>x. (\<Sum>m | m \<in> monomials mpa \<and> lookup m va = x. monomial (MPoly_Type.coeff mpa m) (Poly_Mapping.update va 0 m)) = 0"
  assume a2: "m \<in> monomials mpa"
  have f3: "\<forall>m p. lookup (mapping_of m) p \<noteq> (0::'a) \<or> p \<notin> monomials m"
    by (metis (full_types) coeff_def coeff_eq_zero_iff)
  have f4: "\<forall>n. mapping_of (isolate_variable_sparse mpa va n) = 0"
    using a1 by (simp add: isolate_variable_sparse.rep_eq)
  have "\<forall>p n. lookup 0 (p::nat \<Rightarrow>\<^sub>0 nat) = (0::'a) \<or> (0::nat) = n"
    by simp
  then show "lookup m va = 0"
    using f4 f3 a2 by (metis coeff_def coeff_isolate_variable_sparse lookup_eq_and_update_lemma)
qed

lemma coeff_eq_zero_mpoly_to_nested_polyD: "mpoly_to_nested_poly mp v = 0 \<Longrightarrow> MPoly_Type.coeff mp 0 = 0"
  apply transfer'
  apply transfer'
  by (metis (no_types) coeff_def coeff_isolate_variable_sparse isolate_variable_sparse.rep_eq lookup_zero update_0_0)

lemma mpoly_to_nested_poly_eq_zero_iff[simp]:
  "mpoly_to_nested_poly mp v = 0 \<longleftrightarrow> mp = 0"
  apply (auto simp: coeff_eq_zero_mpoly_to_nested_polyD degree_eq_0_mpoly_to_nested_polyI)
proof -
  show "mpoly_to_nested_poly mp v = 0 \<Longrightarrow> mp = 0" 
    apply (frule degree_eq_0_mpoly_to_nested_polyI)
    apply (frule coeff_eq_zero_mpoly_to_nested_polyD)
    apply (transfer' fixing: mp v)
    apply (transfer' fixing: mp v)
    apply (auto simp: fun_eq_iff mpoly_eq_iff intro!: sum.neutral)
  proof -
    fix m :: "nat \<Rightarrow>\<^sub>0 nat"
    assume a1: "\<forall>x. (\<Sum>m | m \<in> monomials mp \<and> lookup m v = x. monomial (MPoly_Type.coeff mp m) (Poly_Mapping.update v 0 m)) = 0"
    assume a2: "MPoly_Type.degree mp v = 0"
    have "\<forall>n. isolate_variable_sparse mp v n = 0"
      using a1 by (simp add: isolate_variable_sparse.abs_eq zero_mpoly.abs_eq)
    then have f3: "\<forall>p. MPoly_Type.coeff mp p = MPoly_Type.coeff 0 p \<or> lookup p v \<noteq> 0"
      by (metis (no_types) coeff_isolate_variable_sparse lookup_update_self)
    then show "MPoly_Type.coeff mp m = 0"
      using a2 coeff_zero
      by (metis coeff_not_in_monomials degree_eq_iff)
  qed
  show "mp = 0 \<Longrightarrow> mpoly_to_nested_poly 0 v = 0" 
    subgoal
      apply transfer'
      apply transfer'
      by (auto simp: fun_eq_iff intro!: sum.neutral)
    done
qed

lemma isolate_variable_sparse_degree_eq_zero_iff: "isolate_variable_sparse p v (MPoly_Type.degree p v) = 0 \<longleftrightarrow> p = 0"
  apply (transfer')
  apply auto
proof -
  fix pa :: "'a mpoly" and va :: nat
  assume "(\<Sum>m | m \<in> monomials pa \<and> lookup m va = MPoly_Type.degree pa va. monomial (MPoly_Type.coeff pa m) (Poly_Mapping.update va 0 m)) = 0"
  then have "mapping_of (isolate_variable_sparse pa va (MPoly_Type.degree pa va)) = 0"
    by (simp add: isolate_variable_sparse.rep_eq)
  then show "pa = 0"
    by (metis (no_types) coeff_def coeff_eq_zero_iff coeff_isolate_variable_sparse degree_exists_monom lookup_eq_and_update_lemma lookup_zero)
qed

lemma degree_eq_univariate_degree: "MPoly_Type.degree p v =
    (if p = 0 then 0 else Polynomial.degree (mpoly_to_nested_poly p v))"
  apply auto
  apply (rule antisym)
  subgoal
    apply (rule Polynomial.le_degree)
    apply (auto simp: )
    apply transfer'
    by (simp add: isolate_variable_sparse_degree_eq_zero_iff)
  subgoal apply (rule Polynomial.degree_le)
    apply (auto simp: elim!: degree_eq_zeroE)
    apply transfer'
    by (simp add: isovar_greater_degree)
  done

lemma compute_mpoly_to_nested_poly[code]:
  "coeffs (mpoly_to_nested_poly mp v) =
    (if mp = 0 then []
    else map (isolate_variable_sparse mp v) [0..<Suc(MPoly_Type.degree mp v)])"
  unfolding coeffs_def unfolding mpoly_to_nested_poly_eq_zero_iff degree_eq_univariate_degree apply auto
  subgoal by transfer' (rule refl)
  by transfer' (rule refl)

end

lemma isolate_variable_sparse_monom: "isolate_variable_sparse (MPoly_Type.monom m a) v i =
  (if a = 0 \<or> lookup m v \<noteq> i then 0 else MPoly_Type.monom (Poly_Mapping.update v 0 m) a)"
proof -
  have *: "{x. x = m \<and> lookup x v = i} = (if lookup m v = i then {m} else {})"
    by auto
  show ?thesis
    by (transfer' fixing: m a v i) (simp add:*)
qed



lemma isolate_variable_sparse_monom_mult:
  "isolate_variable_sparse (MPoly_Type.monom m a * q) v n =
    (if n \<ge> lookup m v
    then MPoly_Type.monom (Poly_Mapping.update v 0 m) a * isolate_variable_sparse q v (n - lookup m v)
    else 0)"
  for q::"'a::semiring_no_zero_divisors mpoly"
  apply (auto simp: MPoly_Type.mult_monom)
  subgoal
    apply transfer'
    subgoal for mon v i a q
      apply (auto simp add: monomials_monom_mult sum_distrib_left)
      apply (rule sum.reindex_bij_witness_not_neutral[where
            j="\<lambda>a. a - mon"
            and i="\<lambda>a. mon + a"
            and S'="{}"
            and T'="{}"
            ])
              apply (auto simp: lookup_add)
      apply (auto simp: poly_mapping_eq_iff fun_eq_iff single.rep_eq Poly_Mapping.mult_single)
      apply (auto simp: when_def More_MPoly_Type.coeff_monom_mult)
      by (auto simp: lookup_update lookup_add split: if_splits)
    done
  subgoal
    apply transfer'
    apply (auto intro!: sum.neutral simp: monomials_monom_mult )
    apply (rule poly_mapping_eqI)
    apply (auto simp: lookup_single when_def)
    by (simp add: lookup_add)
  done

lemma isolate_variable_sparse_mult:
  "isolate_variable_sparse (p * q) v n = (\<Sum>i\<le>n. isolate_variable_sparse p v i * isolate_variable_sparse q v (n - i))"
  for p q::"'a::semiring_no_zero_divisors mpoly"
proof (induction p rule: mpoly_induct)
  case (monom m a)
  then show ?case
    by (cases "a = 0")
      (auto simp add: mpoly_eq_iff coeff_sum coeff_mult if_conn if_distrib if_distribR
        isolate_variable_sparse_monom isolate_variable_sparse_monom_mult
        cong: if_cong)
next
  case (sum p1 p2 m a)
  then show ?case
    by (simp add: distrib_right isovarspar_sum sum.distrib)
qed

subsubsection "More Miscellaneous"
lemma var_not_in_Const : "var\<notin>vars (Const x :: real mpoly)"
  unfolding vars_def keys_def
  by (smt UN_iff coeff_def coeff_isolate_variable_sparse const_lookup_zero keys_def lookup_eq_zero_in_keys_contradict) 

lemma mpoly_to_nested_poly_mult:
  "mpoly_to_nested_poly (p * q) v = mpoly_to_nested_poly p v * mpoly_to_nested_poly q v"
  for p q::"'a::{comm_semiring_0, semiring_no_zero_divisors} mpoly"
  by (auto simp: poly_eq_iff coeff_mult mpoly_to_nested_poly.rep_eq isolate_variable_sparse_mult)

lemma get_if_const_insertion : 
  assumes "get_if_const (p::real mpoly) = Some r"
  shows "insertion f p = r"
proof-
  have "Set.is_empty (vars p)"
    apply(cases "Set.is_empty (vars p)")
     apply(simp) using assms by(simp)
  then have "(MPoly_Type.coeff p 0) = r"
    using assms by simp
  then show ?thesis
    by (metis Set.is_empty_def \<open>Set.is_empty (vars p)\<close> empty_iff insertion_irrelevant_vars insertion_trivial)
qed

subsubsection "Yet more Degree Lemmas"
lemma degree_mult:
  fixes p q::"'a::{comm_semiring_0, ring_1_no_zero_divisors} mpoly"
  assumes "p \<noteq> 0"
  assumes "q \<noteq> 0"
  shows "MPoly_Type.degree (p * q) v = MPoly_Type.degree p v + MPoly_Type.degree q v"
  using assms
  by (auto simp add: degree_eq_univariate_degree mpoly_to_nested_poly_mult Polynomial.degree_mult_eq)

lemma degree_eq:
  assumes "(p::real mpoly) = (q:: real mpoly)"
  shows "MPoly_Type.degree p x = MPoly_Type.degree q x"
  by (simp add: assms)

lemma degree_var_i : "MPoly_Type.degree (((Var x)^i:: real mpoly)) x = i"
proof (induct i)
  case 0
  then show ?case using degree_const
    by simp
next
  case (Suc i)
  have multh: "(Var x)^(Suc i) = ((Var x)^i::real mpoly) * (Var x:: real mpoly)"
    using power_Suc2 by blast
  have deg0h: "MPoly_Type.degree 0 x = 0"
    by simp
  have deg1h: "MPoly_Type.degree (Var x::real mpoly) x = 1"
    using degree_one
    by blast 
  have nonzeroh1: "(Var x:: real mpoly) \<noteq> 0" 
    using degree_eq deg0h deg1h by auto 
  have nonzeroh2: "((Var x)^i:: real mpoly) \<noteq> 0" 
    using degree_eq deg0h Suc.hyps
    by (metis one_neq_zero power_0) 
  have sumh: "(MPoly_Type.degree (((Var x)^i:: real mpoly) * (Var x:: real mpoly)) x) = (MPoly_Type.degree ((Var x)^i::real mpoly) x) + (MPoly_Type.degree (Var x::real mpoly) x)"
    using degree_mult[where p = "(Var x)^i::real mpoly", where q = "Var x::real mpoly"]  nonzeroh1 nonzeroh2
    by blast 
  then show ?case using sumh deg1h
    by (metis Suc.hyps Suc_eq_plus1 multh) 
qed


lemma degree_less_sum: 
  assumes "MPoly_Type.degree (p::real mpoly) var = n"
  assumes "MPoly_Type.degree (q::real mpoly) var = m"
  assumes "m < n"
  shows "MPoly_Type.degree (p + q) var = n"
proof - 
  have h1: "n > 0"
    using assms(3) neq0_conv by blast
  have h2: "(\<exists>m\<in>monomials p. lookup m var = n) \<and> (\<forall>m\<in>monomials p. lookup m var \<le> n)"
    using degree_eq_iff assms(1)
    by (metis degree_ge_iff h1 order_refl)
  have h3: "(\<exists>m\<in>monomials (p + q). lookup m var = n)"
    using h2
    by (metis MPolyExtension.coeff_add add.right_neutral assms(2) assms(3) coeff_eq_zero_iff degree_not_exists_monom) 
  have h4: "(\<forall>m\<in>monomials (p + q). lookup m var \<le> n)"
    using h2 assms(3) assms(2)
    using degree_add_leq degree_le_iff dual_order.strict_iff_order by blast
  show ?thesis using degree_eq_iff h3 h4
    by (metis assms(3) gr_implies_not0) 
qed

lemma degree_less_sum': 
  assumes "MPoly_Type.degree (p::real mpoly) var = n"
  assumes "MPoly_Type.degree (q::real mpoly) var = m"
  assumes "n < m"
  shows "MPoly_Type.degree (p + q) var = m" using degree_less_sum[OF assms(2) assms(1) assms(3)]
  by (simp add: add.commute) 

(* Result on the degree of the derivative  *)

lemma nonzero_const_is_nonzero: 
  assumes "(k::real) \<noteq> 0"
  shows "((Const k)::real mpoly) \<noteq> 0"
  by (metis MPoly_Type.insertion_zero assms insertion_const)

lemma degree_derivative : 
  assumes "MPoly_Type.degree p x > 0"
  shows "MPoly_Type.degree p x = MPoly_Type.degree (derivative x p) x + 1"
proof -
  define f where "f i = (isolate_variable_sparse p x (i+1) * (Var x)^(i) * (Const (i+1)))" for i
  define n where "n = MPoly_Type.degree p x-1"
  have d : "\<exists>m\<in>monomials p. lookup m x = n+1"
    using n_def degree_eq_iff assms
    by (metis add.commute less_not_refl2 less_one linordered_semidom_class.add_diff_inverse)    
  have h1a : "\<forall>i. MPoly_Type.degree (isolate_variable_sparse p x i) x = 0"
    by (simp add: not_in_isovarspar varNotIn_degree)
  have h1b : "\<forall>i::nat. MPoly_Type.degree ((Var x)^i:: real mpoly) x = i"
    using degree_var_i by auto
  have h1c1 : "\<forall>i. (Var(x)^(i)::real mpoly)\<noteq>0"
    by (metis MPoly_Type.degree_zero h1b power_0 zero_neq_one)
  have h1c1var: "((Var x)^i:: real mpoly) \<noteq> 0" using h1c1 by blast
  have h1c2 : "((Const ((i::nat) + 1))::real mpoly)\<noteq>0"
    using nonzero_const_is_nonzero
    by auto 
  have h1c3: "(isolate_variable_sparse p x (n + 1)) \<noteq> 0" using d
    by (metis One_nat_def Suc_pred add.commute assms isolate_variable_sparse_degree_eq_zero_iff n_def not_gr_zero not_in_isovarspar plus_1_eq_Suc varNotIn_degree)
  have h3: "(isolate_variable_sparse p x (i+1) = 0) \<longrightarrow> (MPoly_Type.degree (f i) x) = 0"
    by (simp add: f_def)
  have degh1: "(MPoly_Type.degree (((Const ((i::nat)+1))::real mpoly)*(Var x)^i) x) = 
    ((MPoly_Type.degree ((Const (i+1))::real mpoly) x) + (MPoly_Type.degree ((Var x)^i:: real mpoly) x))"
    using h1c2 h1c1var degree_mult[where p="((Const ((i::nat)+1))::real mpoly)", where q="((Var x)^i:: real mpoly)"]
    by blast
  then have degh2: "(MPoly_Type.degree (((Const ((i::nat)+1))::real mpoly)*(Var x)^i) x) = i" 
    using degree_var_i degree_const
    by simp 
  have nonzerohyp: "(((Const ((i::nat)+1))::real mpoly)*(Var x)^i) \<noteq> 0"
  proof (induct i)
    case 0
    then show ?case
      by (simp add: nonzero_const_is_nonzero) 
  next
    case (Suc i)
    then show ?case using degree_eq degh2
      by (metis Suc_eq_plus1 h1c1 mult_eq_0_iff nat.simps(3) nonzero_const_is_nonzero of_nat_eq_0_iff)
  qed
  have h4a1: "(isolate_variable_sparse p x (i+1) \<noteq> 0) \<longrightarrow> (MPoly_Type.degree (isolate_variable_sparse p x (i+1) * ((Var x)^(i) * (Const (i+1)))::real mpoly) x = 
      (MPoly_Type.degree (isolate_variable_sparse p x (i+1):: real mpoly) x) + (MPoly_Type.degree (((Const (i+1)) *  (Var x)^(i))::real mpoly) x))"
    using nonzerohyp degree_mult[where p = "(isolate_variable_sparse p x (i+1))::real mpoly", where q = "((Const (i+1)) *  (Var x)^(i)):: real mpoly", where v = "x"]
    by (simp add: mult.commute)
  have h4: "(isolate_variable_sparse p x (i+1) \<noteq> 0) \<longrightarrow> (MPoly_Type.degree (f i) x) = i"
    using h4a1 f_def degh2 h1a
    by (metis (no_types, hide_lams) add.left_neutral mult.commute mult.left_commute of_nat_1 of_nat_add) 
  have h5: "(MPoly_Type.degree (f i) x) \<le> i" using h3 h4 by auto
  have h6: "(MPoly_Type.degree (f n) x) = n" using h1c3 h4
    by (smt One_nat_def add.right_neutral add_Suc_right degree_const degree_mult divisors_zero f_def h1a h1b h1c1 mult.commute nonzero_const_is_nonzero of_nat_1 of_nat_add of_nat_neq_0) 
  have h7a: "derivative x p = (\<Sum>i\<in>{0..MPoly_Type.degree p x-1}. isolate_variable_sparse p x (i+1) * (Var x)^i * (Const (i+1)))" using derivative_def by auto
  have h7b: "(\<Sum>i\<in>{0..MPoly_Type.degree p x-1}. isolate_variable_sparse p x (i+1) * (Var x)^i * (Const (i+1))) = (\<Sum>i\<in>{0..MPoly_Type.degree p x-1}. (f i))" using f_def
    by (metis Suc_eq_plus1 add.commute semiring_1_class.of_nat_simps(2)) 
  have h7c: "derivative x p = (\<Sum>i\<in>{0..MPoly_Type.degree p x-1}. (f i))" using h7a h7b by auto
  have h7: "derivative x p = (\<Sum>i\<in>{0..n}. (f i))" using n_def h7c
    by blast 
  have h8: "n > 0 \<longrightarrow> ((MPoly_Type.degree (\<Sum>i\<in>{0..(n-1)}. (f i)) x) < n)"
  proof (induct n)
    case 0
    then show ?case
      by blast 
  next
    case (Suc n)
    then show ?case using h5 degree_less_sum
      by (smt add_cancel_right_right atLeastAtMost_iff degree_const degree_mult degree_sum_less degree_var_i diff_Suc_1 f_def h1a le_imp_less_Suc mult.commute mult_eq_0_iff)
  qed 
  have h9a: "n = 0 \<longrightarrow> MPoly_Type.degree (\<Sum>i\<in>{0..n}. (f i)) x = n" using h6
    by auto   
  have h9b: "n > 0 \<longrightarrow> MPoly_Type.degree (\<Sum>i\<in>{0..n}. (f i)) x = n" 
  proof - 
    have h9bhyp: "n > 0 \<longrightarrow> (MPoly_Type.degree (\<Sum>i\<in>{0..n}. (f i)) x = MPoly_Type.degree ((\<Sum>i\<in>{0..(n-1)}. (f i)) + (f n)) x)"
      by (metis Suc_diff_1 sum.atLeast0_atMost_Suc)
    have h9bhyp2: "n > 0 \<longrightarrow> ((MPoly_Type.degree ((\<Sum>i\<in>{0..(n-1)}. (f i)) + (f n)) x) = n)" 
      using h6 h8 degree_less_sum
      by (simp add: add.commute) 
    then show ?thesis using h9bhyp2 h9bhyp
      by linarith
  qed
  have h9:  "MPoly_Type.degree (\<Sum>i\<in>{0..n}. (f i)) x = n" using h9a h9b
    by blast 
  have h10: "MPoly_Type.degree (derivative x p) x = n" using h9 h7
    by simp
  show ?thesis using h10 n_def
    using assms by linarith
qed


lemma express_poly :
  assumes h : "MPoly_Type.degree (p::real mpoly) var = 1 \<or> MPoly_Type.degree p var = 2"
  shows "p =
     (isolate_variable_sparse p var 2)*(Var var)^2
    +(isolate_variable_sparse p var 1)*(Var var)
    +(isolate_variable_sparse p var 0)"
proof-
  have h1a: "MPoly_Type.degree p var = 1 \<longrightarrow> p =
    isolate_variable_sparse p var 0 + 
    isolate_variable_sparse p var 1 * Var var"
    using sum_over_zero[where mp="p",where x="var"]
    by auto
  have h1b: "MPoly_Type.degree p var = 1 \<longrightarrow> isolate_variable_sparse p var 2 = 0"
    using isovar_greater_degree
    by (simp add: isovar_greater_degree)
  have h1: "MPoly_Type.degree p var = 1 \<longrightarrow> p =
    isolate_variable_sparse p var 0 + 
    isolate_variable_sparse p var 1 * Var var
    + isolate_variable_sparse p var 2 * (Var var)^2" using h1a h1b by auto
  have h2a: "MPoly_Type.degree p var = 2 \<longrightarrow> p = (\<Sum>i::nat \<le> 2. isolate_variable_sparse p var i * Var var^i)"
    using sum_over_zero[where mp="p", where x="var"] by auto
  have h2b: "(\<Sum>i::nat \<le> 2. isolate_variable_sparse p var i * Var var^i) =
   (\<Sum>i::nat \<le> 1. isolate_variable_sparse p var i * Var var^i) +
   isolate_variable_sparse p var 2 * (Var var)^2" apply auto
    by (simp add: numerals(2))
  have h2:  "MPoly_Type.degree p var = 2 \<longrightarrow> p =
    isolate_variable_sparse p var 0 + 
    isolate_variable_sparse p var 1 * Var var + 
    isolate_variable_sparse p var 2 * (Var var)^2"
    using h2a h2b by auto
  have h3: "isolate_variable_sparse p var 0 + 
    isolate_variable_sparse p var 1 * Var var + 
    isolate_variable_sparse p var 2 * (Var var)^2 = 
    isolate_variable_sparse p var 2 * (Var var)^2 +
    isolate_variable_sparse p var 1 * Var var + 
    isolate_variable_sparse p var 0" by (simp add: add.commute)

  show ?thesis using h h1 h2 h3 by presburger
qed

lemma degree_isovarspar : "MPoly_Type.degree (isolate_variable_sparse (p::real mpoly) x i) x = 0"
  using not_in_isovarspar varNotIn_degree by blast 


end                           
