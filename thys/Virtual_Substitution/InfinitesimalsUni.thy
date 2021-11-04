theory InfinitesimalsUni
  imports Infinitesimals UniAtoms NegInfinityUni QE

begin



fun convertDerivativeUni ::  "real * real * real \<Rightarrow> atomUni fmUni" where
  "convertDerivativeUni (a,b,c) = 
  OrUni(AtomUni(LessUni(a,b,c)))(AndUni(AtomUni(EqUni(a,b,c)))(
    OrUni(AtomUni(LessUni(0,2*a,b)))(AndUni(AtomUni(EqUni(0,2*a,b)))(
      (AtomUni(LessUni(0,0,2*a)))
    ))
  ))
"



lemma convert_convertDerivative : 
  assumes "convert_poly var p (xs'@x#xs) = Some(a,b,c)"
  assumes "length xs' = var"
  shows "eval (convertDerivative var p) (xs'@x#xs) = evalUni (convertDerivativeUni (a,b,c)) x"
proof(cases "MPoly_Type.degree p var = 0")
  case True
  then show ?thesis using assms apply (simp add: isovar_greater_degree eval_or eval_and insertion_mult insertion_const)
    using sum_over_zero[of p var] by auto
next
  case False
  then have nonzero: "MPoly_Type.degree p var \<noteq> 0" by auto
  then show ?thesis proof(cases "MPoly_Type.degree p var = 1")
    case True
    have h1 : "MPoly_Type.degree p var < 3" using True by auto
    have h2 : "get_coeffs var p = (isolate_variable_sparse p var 2, isolate_variable_sparse p var 1, isolate_variable_sparse p var 0)" by auto
    have h : "insertion (nth_default 0 (xs' @ x # xs)) p = b * x + c"
      using poly_to_univar[OF h1 h2 _ _ _ assms(2), of  a x xs b c x] using assms(1) apply(cases "MPoly_Type.degree p var < 3") apply simp_all
      using isovar_greater_degree[of p var] unfolding True by simp
    have h3: "MPoly_Type.degree (isolate_variable_sparse p var (Suc 0) * Const 1) var = 0"
      using degree_mult[of "isolate_variable_sparse p var (Suc 0)" "Const 1" var]
      using degree_isovarspar mult_one_right by presburger
    show ?thesis
      using assms True
      unfolding convertDerivative.simps[of _ p] convertDerivative.simps[of _ "(derivative var p)"]
      apply (simp add: derivative_def isovar_greater_degree eval_or eval_and insertion_add insertion_mult insertion_const HOL.arg_cong[OF sum_over_zero[of p var], of "insertion (nth_default var (xs'@x#xs))"] insertion_var_zero del:convertDerivative.simps)    
      unfolding h     h3 by(simp del:convertDerivative.simps)
  next
    case False
    then have deg2 :  "MPoly_Type.degree p var = 2"
      by (metis One_nat_def assms(1) convert_poly.simps le_SucE less_Suc0 less_Suc_eq_le nonzero numeral_2_eq_2 numeral_3_eq_3 option.distinct(1)) 
    then have first : "isolate_variable_sparse p var (Suc (Suc 0)) \<noteq> 0"
      by (metis MPoly_Type.degree_zero isolate_variable_sparse_degree_eq_zero_iff nat.distinct(1) numeral_2_eq_2)
    have second : "(isolate_variable_sparse p var (Suc (Suc 0)) * Var var)\<noteq>0"
      by (metis MPoly_Type.degree_zero One_nat_def ExecutiblePolyProps.degree_one Zero_not_Suc first mult_eq_0_iff)
    have other : "Const (2::real)\<noteq>0"
      by (simp add: nonzero_const_is_nonzero)
    have thing: "(Var var::real mpoly) \<noteq> 0"
      using second by auto 
    have degree: "MPoly_Type.degree
                  (isolate_variable_sparse p var (Suc 0) * Const 1 +
                   isolate_variable_sparse p var (Suc (Suc 0)) * Var var * Const 2)
                  var -
                 Suc 0 = 0"
      apply simp apply(rule Nat.eq_imp_le) apply(rule degree_less_sum'[of _ _ 0])
      apply (simp add: degree_isovarspar mult_one_right)  apply auto
      unfolding degree_mult[OF second other, of var] degree_const apply simp
      unfolding degree_mult[OF first thing] degree_one
      using degree_isovarspar by force
    have insertion: "insertion (nth_default 0 (xs'@x#xs)) (\<Sum>(i::nat)\<le>2. isolate_variable_sparse p var i * Var var ^ i) = a * x^2 + b * x + c"
    proof(cases "MPoly_Type.degree p var = 1")
      case True
      then show ?thesis
        using False by blast
    next
      case False
      then have deg2 :  "MPoly_Type.degree p var = 2"
        by (metis One_nat_def assms(1) convert_poly.simps le_SucE less_Suc0 less_Suc_eq_le nonzero numeral_2_eq_2 numeral_3_eq_3 option.distinct(1)) 
      then have degless3 : "MPoly_Type.degree p var < 3" by auto
      have thing : "var<length(xs'@x # xs)" using assms by auto
      have h : "(\<Sum>i\<le>2. isolate_variable_sparse p var i * Var var ^ i) = p"
        using deg2
        by (metis sum_over_zero)
      have three: "(3::nat) = Suc(Suc(Suc(0)))" by auto
      have "(\<Sum>i = 0..<3. insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var i) * x ^ i) =
          (insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 0) * x ^ 0) + 
          (insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var (1::nat)) * x ^ (1::nat)) + 
          (insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var (2::nat)) * x ^ (2::nat))"
        unfolding Set_Interval.comm_monoid_add_class.sum.atLeast0_lessThan_Suc three
      proof -
        have "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var (MPoly_Type.degree p var)) * x ^ MPoly_Type.degree p var + (x * insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 1) + (insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 0) + (\<Sum>n = 0..<0. insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var n) * x ^ n))) = insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 0) + x * insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 1) + insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var (MPoly_Type.degree p var)) * x ^ MPoly_Type.degree p var"
          by auto
        then show "(\<Sum>n = 0..<0. insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var n) * x ^ n) + insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 0) * x ^ 0 + insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var (Suc 0)) * x ^ Suc 0 + insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var (Suc (Suc 0))) * x ^ Suc (Suc 0) = insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 0) * x ^ 0 + insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 1) * x ^ 1 + insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 2) * x\<^sup>2"
          by (metis (no_types) One_nat_def Suc_1 add.commute deg2 mult.commute mult.left_neutral power_0 power_one_right)
      qed
      also have "... =  a * x\<^sup>2 + b * x + c"
        unfolding Power.power_class.power.power_0 Power.monoid_mult_class.power_one_right Groups.monoid_mult_class.mult_1_right
        using assms unfolding convert_poly.simps using degless3 by simp
      finally have h2  :"(\<Sum>i = 0..<3. insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var i) * x ^ i) =  a * x\<^sup>2 + b * x + c "
        .
      show ?thesis using sum_over_degree_insertion[OF thing deg2, of x] apply auto  using h h2 using assms(2) by auto
    qed
    have insertionb: "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var (Suc 0)) = b"
      using assms apply(cases "MPoly_Type.degree p var < 3") by simp_all
    have insertiona : "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var (Suc (Suc 0))) = a" 
      using assms apply(cases "MPoly_Type.degree p var < 3")  apply simp_all
      by (simp add: numeral_2_eq_2)
    have x :  "insertion (nth_default 0 (xs' @ x # xs)) (Var var) = x" using insertion_var[of var "(xs' @ x # xs)" x] using assms(2) by auto
    have zero1 : "insertion (nth_default 0 (xs' @ x # xs))
     (isolate_variable_sparse (isolate_variable_sparse p var (Suc 0)) var (Suc 0)) = 0"
      by (simp add: degree_isovarspar isovar_greater_degree)
    have zero2 : "insertion (nth_default 0 (xs' @ x # xs))
      (isolate_variable_sparse (isolate_variable_sparse p var (Suc (Suc 0))) var 0) = a"
      using degree0isovarspar degree_isovarspar insertiona by presburger
    have zero3 : "insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse (Var var) var (Suc 0)) = 1" using isolate_var_one
      using MPoly_Type.insertion_one by fastforce
    have zero4 : "insertion (nth_default 0 (xs' @ x # xs))
      (isolate_variable_sparse (isolate_variable_sparse p var (Suc (Suc 0))) var (Suc 0)) = 0"
      by (simp add: degree_isovarspar isovar_greater_degree)
    have insertion_deriv : "insertion (nth_default 0 (xs'@x#xs))
       (isolate_variable_sparse
         (isolate_variable_sparse p var (Suc 0) * Const 1 +
          isolate_variable_sparse p var (Suc (Suc 0)) * Var var * Const 2)
         var (Suc 0)) = 2*a" 
      unfolding isovarspar_sum isolate_variable_sparse_mult apply auto
      unfolding const_lookup_suc const_lookup_zero Rings.mult_zero_class.mult_zero_right
        Groups.group_add_class.add.group_left_neutral
      unfolding insertion_add insertion_mult insertion_const apply auto
      unfolding zero1 zero2 zero3 zero4 by simp
    have deg2 : "MPoly_Type.degree p var = 2" using degree_convert_eq[OF assms(1)] False nonzero by auto
    then show ?thesis
      using assms 
      unfolding convertDerivative.simps[of _ p] convertDerivative.simps[of _ "(derivative var p)"] convertDerivative.simps[of _ "(derivative var (derivative var p))"]
      apply (simp add: x insertionb insertiona insertion_deriv insertion degree derivative_def isovar_greater_degree eval_or eval_and insertion_add insertion_mult insertion_const HOL.arg_cong[OF sum_over_zero[of p var], of "insertion (nth_default 0 (xs'@x#xs))"] insertion_var_zero del:convertDerivative.simps)
      by (smt (z3) One_nat_def degree_isovarspar distrib_right insertion_deriv isolate_variable_sparse_ne_zeroD mult_one_right neq0_conv not_one_le_zero zero1)
  qed
qed

fun linearSubstitutionUni :: "real \<Rightarrow> real \<Rightarrow> atomUni \<Rightarrow> atomUni fmUni" where
  "linearSubstitutionUni b c a = (if aEvalUni a (-c/b) then TrueFUni else FalseFUni)"

lemma convert_linearSubstitutionUni: 
  assumes "convert_atom var a (xs'@x#xs) = Some(a')"
  assumes "insertion (nth_default 0 (xs'@x#xs)) b = B"
  assumes "insertion (nth_default 0 (xs'@x#xs)) c = C"
  assumes "B \<noteq> 0"
  assumes "var\<notin>(vars b)"
  assumes "var\<notin>(vars c)"
  assumes "length xs' = var"
  shows "aEval (linear_substitution var (-c) b a) (xs'@x#xs) = evalUni (linearSubstitutionUni B C a') x"
  using assms
proof -
  have "aEval a (xs'@(-C/B)#xs) = evalUni (linearSubstitutionUni B C a') x"
    using assms(1) proof(cases "a")
    case (Less p)
    then have "MPoly_Type.degree p var < 3" using assms(1)apply(cases "MPoly_Type.degree p var < 3") by auto
    then show ?thesis
      using Less assms apply simp
      using poly_to_univar by force
  next
    case (Eq p)
    then have "MPoly_Type.degree p var < 3" using assms(1)apply(cases "MPoly_Type.degree p var < 3") by auto
    then show ?thesis
      using Eq assms apply simp
      using poly_to_univar by force
  next
    case (Leq p)
    then have "MPoly_Type.degree p var < 3" using assms(1)apply(cases "MPoly_Type.degree p var < 3") by auto
    then show ?thesis
      using Leq assms apply simp
      using poly_to_univar by force
  next
    case (Neq p)
    then have "MPoly_Type.degree p var < 3" using assms(1)apply(cases "MPoly_Type.degree p var < 3") by auto
    then show ?thesis
      using Neq assms apply simp
      using poly_to_univar by force
  qed
  then have subst : "aEval a ((xs'@x#xs)[var := - C / B]) = evalUni (linearSubstitutionUni B C a') x" using assms by auto
  have hlength : "var< length (xs'@x#xs)" using assms by auto
  have inB : "insertion (nth_default 0 ((xs'@x#xs)[var := - C / B])) b = B" using assms apply auto apply(cases a) apply auto
    by (simp add: insertion_lowerPoly1)+ 
  have inC : "insertion (nth_default 0 ((xs'@x#xs)[var := - C / B])) (-c) = -C" using assms apply auto apply(cases a) apply auto
    by (simp add: insertion_lowerPoly1 insertion_neg)+
  have freenegc : "var\<notin>vars(-c)" using assms not_in_neg by auto
  show ?thesis using linear[OF hlength assms(4)  freenegc assms(5) inC inB, of a ] subst
    using  var_not_in_eval3[OF var_not_in_linear[OF freenegc assms(5)] assms(7)]
    by (metis assms(7) list_update_length)
qed
  (*
  substInfinitesimalLinear var b c A
  substitutes -c/b+epsilon for variable var in atom A
  assumes b is nonzero
  defined in page 615
*)
fun substInfinitesimalLinearUni :: "real \<Rightarrow> real \<Rightarrow> atomUni \<Rightarrow> atomUni fmUni" where
  "substInfinitesimalLinearUni b c (EqUni p) = allZero' p"|
  "substInfinitesimalLinearUni b c (LessUni p) = 
  map_atomUni (linearSubstitutionUni b c) (convertDerivativeUni p)"|
  "substInfinitesimalLinearUni b c (LeqUni p) = 
OrUni
  (allZero' p)
  (map_atomUni (linearSubstitutionUni b c) (convertDerivativeUni p))"|
  "substInfinitesimalLinearUni b c (NeqUni p) = negUni (allZero' p)"


lemma convert_linear_subst_fm :
  assumes "convert_atom var a (xs'@x#xs) = Some a'"
  assumes "insertion (nth_default 0 (xs'@x#xs)) b = B"
  assumes "insertion (nth_default 0 (xs'@x#xs)) c = C"
  assumes "B \<noteq> 0"
  assumes "var\<notin>(vars b)"
  assumes "var\<notin>(vars c)"
  assumes "length xs' = var"
  shows "aEval (linear_substitution (var + 0) (liftPoly 0 0 (-c)) (liftPoly 0 0 b) a) (xs'@x#xs) =
     evalUni (linearSubstitutionUni B C a') x"
proof-
  have lb : "insertion (nth_default 0 (xs'@x#xs)) (liftPoly 0 0 b) = B" unfolding lift00 using assms(2) by auto
  have lc : "insertion (nth_default 0 (xs'@x#xs)) (liftPoly 0 0 c) = C" unfolding lift00 using assms(3) insertion_neg by auto
  have nb : "var \<notin> vars (liftPoly 0 0 b)" using not_in_lift[OF assms(5), of 0] by auto
  have nc : "var \<notin> vars (liftPoly 0 0 c)" using not_in_lift[OF assms(6)] not_in_neg
    using assms(6) lift00 by auto
  then show ?thesis using assms using lb lc convert_linearSubstitutionUni[OF assms(1)  lb lc assms(4) nb nc]
    by (simp add: lift00)
qed

lemma evalUni_if : "evalUni (if cond then TrueFUni else FalseFUni) x = cond"
  by(cases cond)(auto)

lemma degree_less_sum' : "MPoly_Type.degree (p::real mpoly) var = n \<Longrightarrow> MPoly_Type.degree (q::real mpoly) var = m \<Longrightarrow> n < m \<Longrightarrow> MPoly_Type.degree (p + q) var = m"
  using degree_less_sum[of q var m p n]
  by (simp add: add.commute) 

lemma convert_substInfinitesimalLinear_less : 
  assumes "convert_poly var p (xs'@x#xs) = Some(p')"
  assumes "insertion (nth_default 0 (xs'@x#xs)) b = B"
  assumes "insertion (nth_default 0 (xs'@x#xs)) c = C"
  assumes "B \<noteq> 0"
  assumes "var\<notin>(vars b)"
  assumes "var\<notin>(vars c)"
  assumes "length xs' = var"
  shows "
eval (liftmap
    (\<lambda>x. \<lambda>A. Atom(linear_substitution (var+x) (liftPoly 0 x (-c)) (liftPoly 0 x b) A)) 
    (convertDerivative var p)
    0) (xs'@x#xs) =
evalUni (map_atomUni (linearSubstitutionUni B C) (convertDerivativeUni p')) x"
proof(cases p')
  case (fields a' b' c')
  have h : "convert_poly var p (xs'@x#xs) = Some (a', b', c')"
    using assms fields by auto
  have h2 : "\<exists>F'. convert_fm var (convertDerivative var p) xs = Some F'"
    unfolding convertDerivative.simps[of _ p] convertDerivative.simps[of _ "derivative var p"] convertDerivative.simps[of _ "derivative var (derivative var p)"]
    apply( auto simp del: convertDerivative.simps)
    using degree_convert_eq h apply blast
    using assms(1) degree_convert_eq apply blast
    apply (metis Suc_eq_plus1 degree_derivative gr_implies_not0 less_trans_Suc nat_neq_iff)
    using assms(1) degree_convert_eq apply blast
    apply (meson assms(1) degree_convert_eq)
    apply (metis One_nat_def Suc_eq_plus1 degree_derivative less_2_cases less_Suc_eq nat_neq_iff numeral_3_eq_3 one_add_one)
    using assms(1) degree_convert_eq apply blast
    using degree_derivative apply force
    using assms(1) degree_convert_eq apply blast
    apply (meson assms(1) degree_convert_eq)
    apply (metis degree_derivative eq_numeral_Suc less_add_one less_trans_Suc not_less_eq numeral_2_eq_2 pred_numeral_simps(3))
    apply (meson assms(1) degree_convert_eq)
    using degree_derivative apply fastforce
    by (meson assms(1) degree_convert_eq)
  have c'_insertion : "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 0) = c'"
    using assms fields unfolding convert_poly.simps apply(cases "MPoly_Type.degree p var < 3") by auto
  have b'_insertion : "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var (Suc 0)) = b'"
    using assms fields unfolding convert_poly.simps apply(cases "MPoly_Type.degree p var < 3") by auto
  then have b'_insertion2 : "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 1) = b'"
    by auto
  have a'_insertion : "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 2) = a'"
    using assms fields unfolding convert_poly.simps apply(cases "MPoly_Type.degree p var < 3") by auto
  have liftb : "liftPoly 0 0 b = b" using lift00 by auto
  have liftc : "liftPoly 0 0 c = c" using lift00 by auto
  have b'_insertion' : "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse (isolate_variable_sparse p var (Suc 0)) var 0) = b'"
    using assms fields unfolding convert_poly.simps apply(cases "MPoly_Type.degree p var < 3") apply auto
    by (simp add: degree0isovarspar degree_isovarspar)
  have insertion_into_1 : "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse (Const 1) var 0) = 1"
    by (simp add: const_lookup_zero insertion_const)
  have twominusone : "((2-1)::nat) = 1" by auto
  show ?thesis
  proof(cases "MPoly_Type.degree p var = 0")
    case True
    have simp: "(convertDerivative var p)=Atom(Less p)"
      using True
      by auto
    have azero : "a'=0"
      by (metis MPoly_Type.insertion_zero True a'_insertion isolate_variable_sparse_ne_zeroD nat.simps(3) not_less numeral_2_eq_2 zero_less_iff_neq_zero)
    have bzero : "b'=0"
      using True b'_insertion isovar_greater_degree by fastforce
    show ?thesis unfolding fields substInfinitesimalLinearUni.simps
        convertDerivativeUni.simps linearSubstitutionUni.simps map_atomUni.simps evalUni.simps evalUni_if aEvalUni.simps
        Rings.mult_zero_class.mult_zero_left Rings.mult_zero_class.mult_zero_right Groups.add_0 azero bzero
        substInfinitesimalLinear.simps convertDerivative.simps[of _ p] True simp liftmap.simps 
        linear_substitution.simps
      apply (auto simp add:True) 
      unfolding c'_insertion by auto
  next
    case False
    then have degnot0 : "MPoly_Type.degree p var \<noteq> 0" by auto
    then show ?thesis
    proof(cases "MPoly_Type.degree p var = 1")
      case True
      then have simp : "convertDerivative var p = Or (fm.Atom (Less p)) (And (fm.Atom (Eq p)) (fm.Atom (Less (derivative var p))))"
        by (metis One_nat_def Suc_eq_plus1 add_right_imp_eq convertDerivative.simps degnot0 degree_derivative zero_less_one)
      have azero : "a'=0"
        by (metis MPoly_Type.insertion_zero One_nat_def True a'_insertion isovar_greater_degree lessI numeral_2_eq_2)
      have degderiv : "MPoly_Type.degree (isolate_variable_sparse p var (Suc 0) * Const 1) var = 0"
        using degree_mult
        by (simp add: degree_isovarspar mult_one_right) 
      show ?thesis
        unfolding fields substInfinitesimalLinearUni.simps
          convertDerivativeUni.simps linearSubstitutionUni.simps map_atomUni.simps evalUni.simps evalUni_if aEvalUni.simps
          Rings.mult_zero_class.mult_zero_left Rings.mult_zero_class.mult_zero_right Groups.add_0 azero
          substInfinitesimalLinear.simps True simp liftmap.simps 
          linear_substitution.simps eval_Or eval_And liftb liftc 
        apply auto
        unfolding derivative_def True insertion_sub insertion_mult c'_insertion b'_insertion assms lift00 apply auto
        unfolding insertion_sub insertion_mult c'_insertion b'_insertion assms lift00
        apply (smt diff_divide_eq_iff divide_less_0_iff mult_less_0_iff)
        apply (smt mult_imp_less_div_pos neg_less_divide_eq zero_le_mult_iff)
        using assms(4) mult.commute nonzero_mult_div_cancel_left
        apply smt
        unfolding degderiv apply auto
        unfolding isolate_variable_sparse_mult apply auto
        unfolding insertion_mult defer
        apply (smt assms(4) diff_divide_eq_iff divide_less_0_iff mult_less_0_iff)
        defer
        using assms(4) apply blast
        unfolding b'_insertion' insertion_into_1 apply auto
        by (smt assms(4) less_divide_eq mult_pos_neg2 no_zero_divisors zero_less_mult_pos)
    next
      case False
      then have degreetwo : "MPoly_Type.degree p var = 2" using degnot0
        by (metis One_nat_def degree_convert_eq h less_2_cases less_Suc_eq numeral_2_eq_2 numeral_3_eq_3) 
      have two : "(2::nat) = Suc(Suc 0)" by auto
      have sum : "(\<Sum>i = 0..<2. isolate_variable_sparse p var i * (- c) ^ i * b ^ (2 - i)) =
                  isolate_variable_sparse p var 0 * (- c) ^ 0 * b ^ (2 - 0) + isolate_variable_sparse p var 1 * (- c) ^ 1 * b ^ (2 - 1) "
        unfolding Set_Interval.comm_monoid_add_class.sum.atLeast0_lessThan_Suc two by auto
      have a : "isolate_variable_sparse p var (Suc (Suc 0)) \<noteq> 0"
        by (metis degnot0 degree_isovarspar degreetwo isolate_variable_sparse_degree_eq_zero_iff numeral_2_eq_2) 
      have b : "((Var var * Const 2) :: real mpoly) \<noteq> (0::real mpoly)"
        by (metis MPoly_Type.degree_zero ExecutiblePolyProps.degree_one mult_eq_0_iff nonzero_const_is_nonzero zero_neq_numeral zero_neq_one)
      have degreedeg1 : "MPoly_Type.degree
               (isolate_variable_sparse p var (Suc 0) * Const 1 +
                isolate_variable_sparse p var (Suc (Suc 0)) * Var var * Const 2)
               var  = 1"
        apply(rule degree_less_sum'[where n ="0"])
        apply (simp add: degree_isovarspar mult_one_right) defer
        apply simp
        using degree_mult[OF a b, of var]
        by (metis (no_types, hide_lams) ExecutiblePolyProps.degree_one add.left_neutral b degree_const degree_isovarspar degree_mult mult.commute mult_zero_class.mult_zero_right)
      have simp : "(convertDerivative var p) = Or (fm.Atom (Less p))
     (And (fm.Atom (Eq p))
       (Or (fm.Atom (Less (derivative var p)))
         (And (fm.Atom (Eq (derivative var p))) (fm.Atom (Less (derivative var (derivative var p)))))))"
        using degreetwo
        by (metis One_nat_def Suc_1 Suc_eq_plus1 add_diff_cancel_right' convertDerivative.simps degree_derivative neq0_conv zero_less_Suc)
      have a : "insertion (nth_default 0 (xs'@x#xs))
     (isolate_variable_sparse
       (isolate_variable_sparse p var (Suc 0) * Const 1 +
        isolate_variable_sparse p var (Suc (Suc 0)) * Var var * Const 2)
       var 0) = b'" unfolding isovarspar_sum isolate_variable_sparse_mult apply auto
        unfolding const_lookup_suc const_lookup_zero Rings.mult_zero_class.mult_zero_right
          Groups.group_add_class.add.group_left_neutral
        by (simp add: b'_insertion' isolate_var_0 mult_one_right)
      have b : "insertion (nth_default 0 (xs'@x#xs))
     (isolate_variable_sparse
       (isolate_variable_sparse p var (Suc 0) * Const 1 +
        isolate_variable_sparse p var (Suc (Suc 0)) * Var var * Const 2)
       var (Suc 0)) = 2 * a'"
        unfolding isovarspar_sum isolate_variable_sparse_mult apply auto
        unfolding const_lookup_suc const_lookup_zero Rings.mult_zero_class.mult_zero_right
          Groups.group_add_class.add.group_left_neutral
        unfolding insertion_add insertion_mult insertion_const
        by (metis MPoly_Type.insertion_one MPoly_Type.insertion_zero One_nat_def a'_insertion add.commute add.right_neutral degree0isovarspar degree_isovarspar isolate_var_one isovar_greater_degree mult.commute mult.right_neutral mult_zero_class.mult_zero_right numeral_2_eq_2 zero_less_one)
      have simp_insertion_blob : "insertion (nth_default 0 (xs'@x#xs))
     (isolate_variable_sparse
        (isolate_variable_sparse p var (Suc 0) * Const 1 +
         isolate_variable_sparse p var (Suc (Suc 0)) * Var var * Const 2)
        var 0 *
       b -
       isolate_variable_sparse
        (isolate_variable_sparse p var (Suc 0) * Const 1 +
         isolate_variable_sparse p var (Suc (Suc 0)) * Var var * Const 2)
        var (Suc 0) *
       c) = b' * B - 2 * a' * C"
        unfolding insertion_sub insertion_mult assms a b by auto
      have a : "isolate_variable_sparse
       (isolate_variable_sparse p var (Suc 0) * Const 1 +
        isolate_variable_sparse p var (Suc (Suc 0)) * Var var * Const 2)
       var (Suc 0) \<noteq> 0"
        by (metis MPoly_Type.degree_zero One_nat_def degreedeg1 isolate_variable_sparse_degree_eq_zero_iff zero_neq_one) 
      have b' : "(Const 1::real mpoly) \<noteq> 0"
        by (simp add: nonzero_const_is_nonzero)
      have degreeblob : "MPoly_Type.degree
               (isolate_variable_sparse
                 (isolate_variable_sparse p var (Suc 0) * Const 1 +
                  isolate_variable_sparse p var (Suc (Suc 0)) * Var var * Const 2)
                 var (Suc 0) *
                Const 1)
               var = 0" 
        unfolding degree_mult[OF a b', of var]
        by (simp add: degree_isovarspar degree_eq_iff monomials_Const)
      have otherblob : "insertion (nth_default 0 (xs'@x#xs))
      (isolate_variable_sparse
        (isolate_variable_sparse
          (isolate_variable_sparse p var (Suc 0) * Const 1 +
           isolate_variable_sparse p var (Suc (Suc 0)) * Var var * Const 2)
          var (Suc 0) *
         Const 1)
        var 0) = 2 * a'" using b
        by (simp add: degree0isovarspar degree_isovarspar mult_one_right)

      have "(c' * B\<^sup>2 - b' * C * B + a' * C\<^sup>2 < 0) = ((c' * B\<^sup>2 - b' * C * B + a' * C\<^sup>2)/(B\<^sup>2) < 0)"
        by (simp add: assms(4) divide_less_0_iff)
      also have "... = (((c' * B\<^sup>2)/(B\<^sup>2) - (b' * C * B)/(B\<^sup>2) + (a' * C\<^sup>2)/(B\<^sup>2)) < 0)"
        by (metis (no_types, lifting) add_divide_distrib diff_divide_distrib )
      also have "... = (a' * (C / B)\<^sup>2 - b' * C / B + c' < 0)"
      proof -
        { assume "c' + a' * (C / B)\<^sup>2 - b' * (C / B) < 0"
          then have ?thesis
            by (simp add: assms(4) power2_eq_square) }
        moreover
        { assume "\<not> c' + a' * (C / B)\<^sup>2 - b' * (C / B) < 0"
          then have ?thesis
            by (simp add: power2_eq_square) }
        ultimately show ?thesis
          by fastforce
      qed
      finally have h1: "(c' * B\<^sup>2 - b' * C * B + a' * C\<^sup>2 < 0) = (a' * (C / B)\<^sup>2 - b' * C / B + c' < 0)"
        .
      have "(c' * B\<^sup>2 - b' * C * B + a' * C\<^sup>2 = 0) = ((c' * B\<^sup>2 - b' * C * B + a' * C\<^sup>2)/(B\<^sup>2) = 0)"
        by (simp add: assms(4))
      also have "... = (((c' * B\<^sup>2)/(B\<^sup>2) - (b' * C * B)/(B\<^sup>2) + (a' * C\<^sup>2)/(B\<^sup>2)) = 0)"
        by (metis (no_types, lifting) add_divide_distrib diff_divide_distrib )
      also have "... = (a' * (C / B)\<^sup>2 - b' * C / B + c' = 0)"
      proof -
        { assume "c' + a' * (C * (C / (B * B))) - b' * (C / B) \<noteq> 0"
          then have ?thesis
            by (simp add: assms(4) power2_eq_square) }
        moreover
        { assume "c' + a' * (C * (C / (B * B))) - b' * (C / B) = 0"
          then have ?thesis
            by (simp add: power2_eq_square) }
        ultimately show ?thesis
          by fastforce
      qed
      finally have h2 : "(c' * B\<^sup>2 - b' * C * B + a' * C\<^sup>2 = 0) = (a' * (C / B)\<^sup>2 - b' * C / B + c' = 0)"
        .
      have h3 : "((b' * B - 2 * a' * C) * B < 0) = (b' < 2 * a' * C / B)"
        by (smt assms(4) less_divide_eq zero_le_mult_iff)
      have h4 : "(b' * B = 2 * a' * C) = (b' = 2 * a' * C / B)"
        by (simp add: assms(4) nonzero_eq_divide_eq)
      show ?thesis unfolding fields substInfinitesimalLinearUni.simps
          convertDerivativeUni.simps linearSubstitutionUni.simps map_atomUni.simps evalUni.simps evalUni_if aEvalUni.simps
          Rings.mult_zero_class.mult_zero_left Rings.mult_zero_class.mult_zero_right Groups.add_0
          substInfinitesimalLinear.simps degreetwo simp liftmap.simps 
          linear_substitution.simps eval_Or eval_And liftb liftc 
        apply simp 
        unfolding derivative_def degreetwo insertion_sub insertion_mult c'_insertion b'_insertion assms  apply simp
        unfolding sum insertion_add insertion_mult insertion_pow insertion_neg assms
        unfolding b'_insertion2 c'_insertion a'_insertion
        unfolding Power.power_class.power.power_0  Groups.monoid_mult_class.mult_1_right
          Groups.cancel_comm_monoid_add_class.diff_zero Power.monoid_mult_class.power_one_right
          twominusone degreedeg1 apply simp
        unfolding insertion_mult assms simp_insertion_blob degreeblob 
        unfolding insertion_mult insertion_sub assms otherblob apply simp
        unfolding otherblob h1 h2 h3 h4 unfolding lift00 insertion_neg assms insertion_isovarspars_free insertion_sum insertion_mult insertion_sub degree0isovarspar degree_isovarspar mult_one_right insertion_sum_var insertion_pow insertion_neg sum
        unfolding assms b'_insertion c'_insertion a'_insertion insertion_neg insertion_mult insertion_add insertion_pow apply simp
        by (smt assms(2) assms(3) b'_insertion h1 h2 h3 h4 insertion_mult insertion_sub mult_one_right simp_insertion_blob)
    qed
  qed
qed
lemma convert_substInfinitesimalLinear: 
  assumes "convert_atom var a (xs'@x#xs) = Some(a')"
  assumes "insertion (nth_default 0 (xs'@x#xs)) b = B"
  assumes "insertion (nth_default 0 (xs'@x#xs)) c = C"
  assumes "B \<noteq> 0"
  assumes "var\<notin>(vars b)"
  assumes "var\<notin>(vars c)"
  assumes "length xs' = var"
  shows "eval (substInfinitesimalLinear var (-c) b a) (xs'@x#xs) = evalUni (substInfinitesimalLinearUni B C a') x"
  using assms
proof(cases a)
  case (Less p)
  have "\<exists>p'. convert_poly var p (xs'@x#xs) = Some p'"
    using Less assms(1) apply(cases "MPoly_Type.degree p var < 3") by auto
  then obtain p' where p'_def : "convert_poly var p (xs'@x#xs) = Some p'" by auto
  have A'_simp :  "a' = LessUni p'"
    using assms Less
    using p'_def by auto 
  have h1 : "eval (convertDerivative var p) (xs'@x#xs) = evalUni (convertDerivativeUni p') x" using convert_convertDerivative
    apply ( cases p')
    using A'_simp Less assms by auto 
  show ?thesis unfolding A'_simp using convert_substInfinitesimalLinear_less[OF p'_def assms(2-7)] unfolding Less by auto
next
  case (Eq p)
  define p' where "p' = (case convert_poly var p (xs'@x#xs) of Some p' \<Rightarrow> p')"
  have A'_simp :  "a' = EqUni p'"
    using assms Eq
    using p'_def by auto 
  show ?thesis
    unfolding Eq A'_simp substInfinitesimalLinear.simps substInfinitesimalLinearUni.simps
    using convert_allZero A'_simp Eq assms by auto
next
  case (Leq p)
  have "\<exists>p'. convert_poly var p (xs' @ x # xs) = Some p'"
    using assms(1) unfolding Leq apply auto apply(cases "MPoly_Type.degree p var < 3") by auto
  then obtain p' where p'_def : "convert_poly var p (xs' @ x # xs) = Some p'" by metis
  have A'_simp :  "a' = LeqUni p'"
    using assms Leq
    using p'_def by auto 
  have h1 : "eval (convertDerivative var p) (xs'@x#xs) = evalUni (convertDerivativeUni p') x" using convert_convertDerivative
    apply(cases p')
    using A'_simp Leq assms by auto
  show ?thesis unfolding A'_simp Leq substInfinitesimalLinear.simps eval_Or substInfinitesimalLinearUni.simps evalUni.simps
    using convert_substInfinitesimalLinear_less[OF p'_def assms(2-7)]
      convert_allZero[OF p'_def assms(7)] by simp
next
  case (Neq p)
  have "\<exists>p'. convert_poly var p (xs' @ x # xs) = Some p'"
    using assms(1) unfolding Neq apply auto apply(cases "MPoly_Type.degree p var < 3") by auto
  then obtain p' where p'_def : "convert_poly var p (xs' @ x # xs) = Some p'" by metis
  have A'_simp :  "a' = NeqUni p'"
    using assms Neq
    using p'_def by auto 
  show ?thesis
    unfolding Neq A'_simp substInfinitesimalLinear.simps substInfinitesimalLinearUni.simps
    using convert_allZero[OF p'_def assms(7)]
    by (metis A'_simp Neq assms(1) assms(7) convert_substNegInfinity eval.simps(6) eval_neg substNegInfinityUni.simps(4) substNegInfinity.simps(4))  
qed


lemma either_or:
  fixes r :: "real"
  assumes a: "(\<exists>y'>r. \<forall>x\<in>{r<..y'}.  (aEvalUni (EqUni (a, b, c)) x) \<or> (aEvalUni (LessUni (a, b, c)) x))"
  shows "(\<exists>y'>r. \<forall>x\<in>{r<..y'}.  (aEvalUni (EqUni (a, b, c)) x)) \<or> 
  (\<exists>y'>r. \<forall>x\<in>{r<..y'}.  (aEvalUni (LessUni (a, b, c)) x))"
proof  (cases "a = 0 \<and> b = 0 \<and> c= 0")
  case True
  then have "(\<exists>y'>r. \<forall>x\<in>{r<..y'}.  (aEvalUni (EqUni (a, b, c)) x))"
    using assms by auto
  then show ?thesis
    by blast 
next
  case False 
  then have noz: "a\<noteq>0 \<or> b\<noteq>0 \<or> c\<noteq>0" by auto
  obtain y1' where y1prop: "y1' > r \<and> (\<forall>x\<in>{r<..y1'}. (aEvalUni (EqUni (a, b, c)) x) \<or> (aEvalUni (LessUni (a, b, c)) x))"
    using a by auto
  obtain y2' where y2prop: "y2' > r \<and> (\<forall>x\<in>{r<..y2'}. a * x\<^sup>2 + b * x + c \<noteq> 0)"
    using noz nonzcoeffs[of a b c] by auto
  let ?y = "min y1' y2'"
  have ygt: "?y > r" using y1prop y2prop by auto
  have "\<forall>x\<in>{r<..?y}. (aEvalUni (LessUni (a, b, c)) x)"
    using y1prop y2prop greaterThanAtMost_iff
    by force 
  then show ?thesis using ygt
    by blast 
qed

lemma infinitesimal_linear'_helper :
  assumes at_is: "At = LessUni p \<or> At = EqUni p"
  assumes "B \<noteq> 0"
  shows "((\<exists>y'::real>-C/B. \<forall>x::real \<in>{-C/B<..y'}. aEvalUni At x)
      = evalUni (substInfinitesimalLinearUni B C At) x)"
proof (cases "At = LessUni p")
  case True
  then have LessUni: "At = LessUni p" by auto
  then show ?thesis proof(cases p)
    case (fields a b c) 
    then show ?thesis 
      unfolding LessUni fields 
      using one_root_a_lt0[where r="C/B", where a= "a", where b="b",where c= "c"] apply(auto) 
      using continuity_lem_lt0_expanded[where a= "a", where b = "2 * a * C / B ", where c = "c"]  apply (auto) 
      using continuity_lem_gt0_expanded[where a = "a", where b = "2 * a * C / B",where c = "c", where r = "- (C / B)"] apply (auto) 
      apply (meson less_eq_real_def linorder_not_less) 
      using one_root_a_gt0[where r = "C/B", where a = "a", where b="b", where c="c"] apply (auto) 
      using continuity_lem_lt0_expanded[where a= "a", where b = "2 * a * C / B", where c= "c"]
      apply (auto)
      using continuity_lem_gt0_expanded[where a = "a", where b = "2 * a * C / B",where c = "c", where r = "- (C / B)"]
      apply (auto) apply (meson less_eq_real_def linorder_not_less) 
      using case_d1 apply (auto)
      using continuity_lem_lt0_expanded[where a= "a", where b = "b", where c= "c"]
      apply (auto)
      using continuity_lem_gt0_expanded[where a = "a", where b = "b",where c = "c", where r = "- (C / B)"]
      apply (auto) apply (meson less_eq_real_def linorder_not_less) 
      using case_d4 apply (auto) 
      using continuity_lem_lt0_expanded[where a= "a", where b = "b", where c= "c"]
      apply (auto)
      using continuity_lem_gt0_expanded[where a = "a", where b = "b",where c = "c", where r = "- (C / B)"]
      apply (auto)
      by (meson less_eq_real_def linorder_not_le) 
  qed    
next
  case False
  then have EqUni: "At = EqUni p" using at_is by auto
  then show ?thesis proof(cases p)
    case (fields a b c)
    show ?thesis
      apply(auto simp add:EqUni fields) 
      using continuity_lem_eq0[where r= "-(C/B)"] apply blast
      using continuity_lem_eq0[where r= "-(C/B)"] apply blast
      using continuity_lem_eq0[where r= "-(C/B)"] apply blast
      using linordered_field_no_ub by blast
  qed
qed 

(* I assume substInfinitesimalLinearUni' was supposed to be substInfinitesimalLinearUni?*)
lemma infinitesimal_linear' :
  assumes "B \<noteq> 0"
  shows "(\<exists>y'::real>-C/B. \<forall>x::real \<in>{-C/B<..y'}. aEvalUni At x)
      = evalUni (substInfinitesimalLinearUni B C At) x"
proof(cases At)
  case (LessUni p) 
  then show ?thesis using infinitesimal_linear'_helper[of At p B C] assms by auto
next
  case (EqUni p)
  then show ?thesis  using infinitesimal_linear'_helper[of At p B C] assms by (auto) 
next
  case (LeqUni p)
  then show ?thesis proof(cases p)
    case (fields a b c) 
    have same: "\<forall>x. aEvalUni (LeqUni p) x = (aEvalUni (EqUni p) x) \<or> (aEvalUni (LessUni p) x)" 
      apply (simp add: fields)
      by force 
    have "\<And>a b c.
       At = LeqUni p \<Longrightarrow>
       p = (a, b, c) \<Longrightarrow>
       (\<exists>y'>- C / B. \<forall>x\<in>{- C / B<..y'}. aEvalUni At x) =
       evalUni (substInfinitesimalLinearUni B C At) x "
    proof - 
      fix a b c
      assume atis: "At = LeqUni p"
      assume p_is: " p = (a, b, c)"
      have s1: "(\<exists>y'>- C / B. \<forall>x\<in>{- C / B<..y'}. aEvalUni At x) = (\<exists>y'>- C / B. \<forall>x\<in>{- C / B<..y'}.  (aEvalUni (EqUni p) x) \<or> (aEvalUni (LessUni p) x))"
        using atis same aEvalUni.simps(2) aEvalUni.simps(3) fields less_eq_real_def
        by blast
      have s2: "... = (\<exists>y'>- C / B. \<forall>x\<in>{- C / B<..y'}.  (aEvalUni (EqUni p) x)) \<or> (\<exists>y'>- C / B. \<forall>x\<in>{- C / B<..y'}. (aEvalUni (LessUni p) x))"
        using either_or[where r = "-C/B"] p_is 
        by blast 
      have eq1: "(\<exists>y'>- C / B. \<forall>x\<in>{- C / B<..y'}.  (aEvalUni (EqUni p) x)) =  (evalUni (substInfinitesimalLinearUni B C (EqUni p)) x)"
        using infinitesimal_linear'_helper[where At = "EqUni p", where p = "p", where B = "B", where C= "C"] 
          assms by auto
      have eq2: "(\<exists>y'>- C / B. \<forall>x\<in>{- C / B<..y'}. (aEvalUni (LessUni p) x)) = (evalUni (substInfinitesimalLinearUni B C (LessUni p)) x)"
        using infinitesimal_linear'_helper[where At = "LessUni p", where p = "p", where B = "B", where C= "C"] 
          assms by auto
      have z1: "(\<exists>y'>- C / B. \<forall>x\<in>{- C / B<..y'}. aEvalUni At x) = ((evalUni (substInfinitesimalLinearUni B C (EqUni p)) x) \<or> (evalUni (substInfinitesimalLinearUni B C (LessUni p)) x))"
        using s1 s2 eq1 eq2  by auto
      have z2: "(evalUni (substInfinitesimalLinearUni B C (EqUni p)) x) \<or> (evalUni (substInfinitesimalLinearUni B C (LessUni p)) x) = evalUni (substInfinitesimalLinearUni B C (LeqUni p)) x" 
        by auto
      have z3: "(evalUni (substInfinitesimalLinearUni B C At) x) = evalUni (substInfinitesimalLinearUni B C (LeqUni p)) x"
        using LeqUni by auto
      then have z4: "(evalUni (substInfinitesimalLinearUni B C (EqUni p)) x) \<or> (evalUni (substInfinitesimalLinearUni B C (LessUni p)) x) = (evalUni (substInfinitesimalLinearUni B C At) x) "
        using z2 z3 by auto
      let ?a = "(evalUni (substInfinitesimalLinearUni B C (EqUni p)) x) \<or> (evalUni (substInfinitesimalLinearUni B C (LessUni p)) x)"
      let ?b = "(\<exists>y'>- C / B. \<forall>x\<in>{- C / B<..y'}. aEvalUni At x)"
      let ?c = "(evalUni (substInfinitesimalLinearUni B C At) x)"
      have t1: "?b = ?a" using z1 by auto
      have t2: "?a = ?c" using z4
        by (simp add: atis)
      then have "?b = ?c" using t1 t2 by auto
      then show "(\<exists>y'>- C / B. \<forall>x\<in>{- C / B<..y'}. aEvalUni At x) = evalUni (substInfinitesimalLinearUni B C At) x"
        by auto
    qed
    then show ?thesis
      using LeqUni fields by blast 
  qed
next
  case (NeqUni p)
  then show ?thesis proof(cases p)
    case (fields a b c)
    then show ?thesis unfolding NeqUni fields using nonzcoeffs  by (auto) 
  qed
qed

fun quadraticSubUni :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> atomUni \<Rightarrow> atomUni fmUni" where
  "quadraticSubUni a b c d A = (if aEvalUni A ((a+b*sqrt(c))/d) then TrueFUni else FalseFUni)"

fun substInfinitesimalQuadraticUni :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> atomUni \<Rightarrow> atomUni fmUni" where
  "substInfinitesimalQuadraticUni a b c d (EqUni p) = allZero' p"|
  "substInfinitesimalQuadraticUni a b c d (LessUni p) = map_atomUni (quadraticSubUni a b c d) (convertDerivativeUni p)"|
  "substInfinitesimalQuadraticUni a b c d (LeqUni p) = OrUni(map_atomUni (quadraticSubUni a b c d) (convertDerivativeUni p)) (allZero' p)"|
  "substInfinitesimalQuadraticUni a b c d (NeqUni p) = negUni (allZero' p)"


lemma weird :
  fixes D::"real"
  assumes dneq: "D \<noteq> (0::real)"
  shows 
    "((a'::real) * (((A::real) + (B::real) * sqrt (C::real)) / (D::real))\<^sup>2 + (b'::real) * (A + B * sqrt C) / D + c' < 0 \<or>
     a' * ((A + B * sqrt C) / D)\<^sup>2 + b' * (A + B * sqrt C) / D + (c'::real) = 0 \<and>
     (b' + a' * (A + B * sqrt C) * 2 / D < 0 \<or>
      b' + a' * (A + B * sqrt C) * 2 / D = 0 \<and> 2 * a' < 0)) =
    (a' * ((A + B * sqrt C) / D)\<^sup>2 + b' * (A + B * sqrt C) / D + c' < 0 \<or>
     a' * ((A + B * sqrt C) / D)\<^sup>2 + b' * (A + B * sqrt C) / D + c' = 0 \<and>
     (2 * a' * (A + B * sqrt C) / D + b' < 0 \<or>
      2 * a' * (A + B * sqrt C) / D + b' = 0 \<and> a' < 0))"
proof (cases "(a' * ((A + B * sqrt C) / D)\<^sup>2 + b' * (A + B * sqrt C) / D + c' < 0)")
  case True
  then show ?thesis
    by auto
next
  case False
  have "a' * (A + B * sqrt C) * 2 = 2 * a' * (A + B * sqrt C)" by auto
  then have "a' * (A + B * sqrt C) * 2 / D =2 * a' * (A + B * sqrt C) / D "
    using dneq by simp 
  then have "b' + a' * (A + B * sqrt C) * 2 / D = 2 * a' * (A + B * sqrt C) / D + b'"
    using add.commute by simp
  then have "(b' + a' * (A + B * sqrt C) * 2 / D < 0 \<or> b' + a' * (A + B * sqrt C) * 2 / D = 0 \<and> a' < 0)
   = (2 * a' * (A + B * sqrt C) / D + b' < 0 \<or> 2 * a' * (A + B * sqrt C) / D + b' = 0 \<and> a' < 0)"
    by (simp add: \<open>b' + a' * (A + B * sqrt C) * 2 / D = 2 * a' * (A + B * sqrt C) / D + b'\<close>)
  then have "(a' * ((A + B * sqrt C) / D)\<^sup>2 + b' * (A + B * sqrt C) / D + c' = 0 \<and>
     (b' + a' * (A + B * sqrt C) * 2 / D < 0 \<or> b' + a' * (A + B * sqrt C) * 2 / D = 0 \<and> a' < 0)) =
    (a' * ((A + B * sqrt C) / D)\<^sup>2 + b' * (A + B * sqrt C) / D + c' = 0 \<and>
     (2 * a' * (A + B * sqrt C) / D + b' < 0 \<or> 2 * a' * (A + B * sqrt C) / D + b' = 0 \<and> a' < 0))"
    by blast
  then show ?thesis using False by simp
qed 

lemma convert_substInfinitesimalQuadratic_less :
  assumes "convert_poly var p (xs'@x#xs) = Some p'"
  assumes "insertion (nth_default 0 (xs'@x#xs)) a = A"
  assumes "insertion (nth_default 0 (xs'@x#xs)) b = B"
  assumes "insertion (nth_default 0 (xs'@x#xs)) c = C"
  assumes "insertion (nth_default 0 (xs'@x#xs)) d = D"
  assumes "D \<noteq> 0"
  assumes "0 \<le> C"
  assumes "var\<notin>(vars a)"
  assumes "var\<notin>(vars b)"
  assumes "var\<notin>(vars c)"
  assumes "var\<notin>(vars d)"
  assumes "length xs' = var"
  shows "eval (quadratic_sub_fm var a b c d (convertDerivative var p)) (xs'@x#xs) = evalUni (map_atomUni (quadraticSubUni A B C D) (convertDerivativeUni p')) x"
proof(cases p')
  case (fields a' b' c')
  have h : "convert_poly var p (xs'@x#xs) = Some (a', b', c')"
    using assms fields by auto
  have h2 : "\<exists>F'. convert_fm var (convertDerivative var p) (xs'@x#xs) = Some F'"
    unfolding convertDerivative.simps[of _ p] convertDerivative.simps[of _ "derivative var p"] convertDerivative.simps[of _ "derivative var (derivative var p)"]
    apply (auto simp del: convertDerivative.simps)
    using degree_convert_eq h apply blast
    using assms(1) degree_convert_eq apply blast
    using degree_derivative apply fastforce
    apply (metis degree_convert_eq h   numeral_3_eq_3 )
    apply (metis (no_types, lifting) One_nat_def add.right_neutral add_Suc_right degree_derivative less_Suc_eq_0_disj less_Suc_eq_le neq0_conv numeral_3_eq_3)
    apply (metis One_nat_def Suc_eq_plus1 degree_derivative less_2_cases less_Suc_eq nat_neq_iff numeral_3_eq_3 one_add_one)
    apply (meson assms(1) degree_convert_eq)
    using degree_derivative apply fastforce
    using assms(1) degree_convert_eq apply blast
    apply (meson assms(1) degree_convert_eq)
    apply (metis degree_derivative less_Suc_eq less_add_one not_less_eq numeral_3_eq_3)
    apply (meson assms(1) degree_convert_eq)
    apply (metis (no_types, hide_lams) Suc_1 Suc_eq_plus1 degree_derivative less_2_cases less_Suc_eq numeral_3_eq_3)
    using assms(1) degree_convert_eq by blast
  have c'_insertion : "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 0) = c'"
    using assms fields unfolding convert_poly.simps apply(cases "MPoly_Type.degree p var < 3") by auto
  then have c'_insertion'' : "\<And>x. insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 0) = c'"
    using assms(12) not_in_isovarspar[of p var 0 "isolate_variable_sparse p var 0", OF HOL.refl]
    by (metis list_update_length not_contains_insertion)
  have b'_insertion : "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var (Suc 0)) = b'"
    using assms fields unfolding convert_poly.simps apply(cases "MPoly_Type.degree p var < 3") by auto
  then have b'_insertion'' : "\<And>x. insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var (Suc 0)) = b'"
    using assms(12) not_in_isovarspar[of p var "Suc 0" "isolate_variable_sparse p var (Suc 0)", OF HOL.refl]
    by (metis list_update_length not_contains_insertion)
  then have b'_insertion2 : "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 1) = b'"
    by auto
  have a'_insertion : "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse p var 2) = a'"
    using assms fields unfolding convert_poly.simps apply(cases "MPoly_Type.degree p var < 3") by auto
  then have a'_insertion'' : "\<And>x. insertion (nth_default 0 (xs' @ x # xs)) (isolate_variable_sparse p var 2) = a'"
    using assms(12) not_in_isovarspar[of p var 2 "isolate_variable_sparse p var 2", OF HOL.refl]
    by (metis list_update_length not_contains_insertion)
  have liftb : "liftPoly 0 0 b = b" using lift00 by auto
  have liftc : "liftPoly 0 0 c = c" using lift00 by auto
  have b'_insertion' : "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse (isolate_variable_sparse p var (Suc 0)) var 0) = b'"
    using assms fields unfolding convert_poly.simps apply(cases "MPoly_Type.degree p var < 3") apply auto
    using degree0isovarspar degree_isovarspar by auto
  have insertion_into_1 : "insertion (nth_default 0 (xs'@x#xs)) (isolate_variable_sparse (Const 1) var 0) = 1"
    by (simp add: const_lookup_zero insertion_const)
  have twominusone : "((2-1)::nat) = 1" by auto
  have length0 : "var < length (xs'@x#xs)" using assms by auto
  have altinserta : "\<forall>xa. insertion (nth_default 0 ((xs'@x#xs)[var := xa])) a = A"
    using assms by (metis list_update_length not_contains_insertion)
  have altinserta' : "\<And>xa. insertion (nth_default 0 ((xs'@x#xs)[var := xa])) a = A"
    using assms by (metis list_update_length not_contains_insertion)
  have altinsertb : "\<forall>xa. insertion (nth_default 0 ((xs'@x#xs)[var := xa])) b = B"
    using assms by (metis list_update_length not_contains_insertion)
  have altinsertb' : "\<And>xa. insertion (nth_default 0 ((xs'@x#xs)[var := xa])) b = B"
    using assms by (metis list_update_length not_contains_insertion)
  have altinsertc : "\<forall>xa. insertion (nth_default 0 ((xs'@x#xs)[var := xa])) c = C"
    using assms by (metis list_update_length not_contains_insertion)
  have altinsertc' : "\<And>xa. insertion (nth_default 0 ((xs'@x#xs)[var := xa])) c = C"
    using assms by (metis list_update_length not_contains_insertion)
  have altinsertd : "\<forall>xa. insertion (nth_default 0 ((xs'@x#xs)[var := xa])) d = D" 
    using assms by (metis list_update_length not_contains_insertion)
  have altinsertd' : "\<And>xa. insertion (nth_default 0 ((xs'@x#xs)[var := xa])) d = D" 
    using assms by (metis list_update_length not_contains_insertion)
  have freeInQuadraticSub : "\<forall>At. eval (quadratic_sub var a b c d At) ((xs'@x#xs)[var := sqrt C]) = eval (quadratic_sub var a b c d At) ((xs'@x#xs))"
    by (metis assms(10) assms(11) assms(8) assms(9) free_in_quad list_update_id var_not_in_eval)
  have quad : "\<And>At. (eval (quadratic_sub var a b c d At) (xs'@x#xs) =
  aEval At ((xs'@x#xs)[var := (A + B * sqrt C) / D]))"
    using quadratic_sub[OF length0 assms(6-7) assms(10) altinserta altinsertb altinsertc altinsertd, symmetric]
    using freeInQuadraticSub  by auto 
  show ?thesis
  proof(cases "MPoly_Type.degree p var = 0")
    case True
    then have simp: "(convertDerivative var p)=Atom(Less p)"
      by auto
    have azero : "a'=0"
      by (metis MPoly_Type.insertion_zero True a'_insertion isolate_variable_sparse_ne_zeroD nat.simps(3) not_less numeral_2_eq_2 zero_less_iff_neq_zero)
    have bzero : "b'=0"
      using True b'_insertion isovar_greater_degree by fastforce
    define p1 where "p1 = isolate_variable_sparse p var 0"
    have degree_p1: "MPoly_Type.degree p1 var = 0" unfolding p1_def
      by (simp add: degree_isovarspar)
    define p2 where "p2 = isolate_variable_sparse p1 var 0 * Const 0 * Var var + isolate_variable_sparse p1 var 0 * Const 1"
    define A where "A = isolate_variable_sparse p2 var 0"
    define B where "B = isolate_variable_sparse p2 var (Suc 0)"
    show ?thesis
      unfolding substInfinitesimalQuadratic.simps substInfinitesimalQuadraticUni.simps
        fields
        convertDerivativeUni.simps map_atomUni.simps quadraticSubUni.simps aEvalUni.simps evalUni.simps evalUni_if
        Rings.mult_zero_class.mult_zero_left Groups.add_0 Rings.mult_zero_class.mult_zero_right
        True simp azero bzero 
        quadratic_sub_fm.simps quadratic_sub_fm_helper.simps liftmap.simps lift00  
        quad aEval.simps
      apply (simp add:True c'_insertion p1_def[symmetric] degree_p1 p2_def[symmetric] A_def[symmetric] B_def[symmetric]) 
      unfolding A_def B_def p2_def p1_def  degree0isovarspar[OF True] isovarspar_sum mult_one_right mult_zero_right mult_zero_left const_lookup_zero const_lookup_suc
      apply simp
      unfolding insertion_add insertion_sub insertion_mult insertion_pow insertion_const c'_insertion apply simp
      using \<open>isolate_variable_sparse p var 0 = p\<close> b'_insertion2 bzero c'_insertion by force
  next
    case False
    then have degreenonzero : "MPoly_Type.degree p var \<noteq>0" by auto
    show ?thesis
    proof(cases "MPoly_Type.degree p var = 1")
      case True
      then have simp : "convertDerivative var p = Or (fm.Atom (Less p)) (And (fm.Atom (Eq p)) (fm.Atom (Less (derivative var p))))"
        by (metis One_nat_def Suc_eq_plus1 add_right_imp_eq convertDerivative.simps degree_derivative degreenonzero less_numeral_extra(1))
      have azero : "a'=0"
        by (metis MPoly_Type.insertion_zero One_nat_def True a'_insertion isovar_greater_degree lessI numeral_2_eq_2)
      have degderiv : "MPoly_Type.degree (isolate_variable_sparse p var (Suc 0) * Const 1) var = 0"
        using degree_mult
        by (simp add: degree_isovarspar mult_one_right)
      have thing : "var<length (xs'@((A + B * sqrt C) / D # xs))" using assms by auto
      have insertp : "insertion (nth_default 0 (xs'@((A + B * sqrt C) / D # xs))) p = b' * (A + B * sqrt C) / D + c'"
        using sum_over_degree_insertion[OF thing True, of "(A + B * sqrt C) / D", symmetric] unfolding list_update_length  assms(12)[symmetric] apply simp
        unfolding assms(12) unfolding c'_insertion'' b'_insertion''  by auto
      have insertb : "insertion (nth_default 0 (xs'@(A + B * sqrt C) / D # xs))
      (isolate_variable_sparse p var (Suc 0) * Const 1) = b'"
        unfolding insertion_mult insertion_const b'_insertion'' by simp
      show ?thesis
        unfolding substInfinitesimalQuadratic.simps substInfinitesimalQuadraticUni.simps
          fields
          convertDerivativeUni.simps map_atomUni.simps quadraticSubUni.simps aEvalUni.simps evalUni.simps evalUni_if
          Rings.mult_zero_class.mult_zero_left Groups.add_0 Rings.mult_zero_class.mult_zero_right
          True simp azero 
          quadratic_sub_fm.simps quadratic_sub_fm_helper.simps liftmap.simps lift00  
          quad aEval.simps eval.simps derivative_def Groups.monoid_add_class.add_0_right
        apply simp
        unfolding insertp insertb insertion_mult insertion_const
        using assms(12) b'_insertion'' insertp by force
    next
      case False
      then have degree2 : "MPoly_Type.degree p var = 2" using degreenonzero
        using h less_Suc_eq by fastforce 
      have simp : "(convertDerivative var p) = Or (fm.Atom (Less p))
     (And (fm.Atom (Eq p))
       (Or (fm.Atom (Less (derivative var p)))
         (And (fm.Atom (Eq (derivative var p))) (fm.Atom (Less (derivative var (derivative var p)))))))"
        by (metis One_nat_def Suc_eq_plus1 add_diff_cancel_right' convertDerivative.simps degree2 degree_derivative degreenonzero neq0_conv one_add_one)
      have insertionp : "var < length (xs'@(A + B * sqrt C) / D # xs)" using assms by auto
      have three : "3 = Suc(Suc(Suc(0)))" by auto
      have two : "2 = Suc(Suc(0))" by auto
      have insertionp : "insertion (nth_default 0 ((xs'@x # xs)[var := (A + B * sqrt C) / D])) p = a' * ((A + B * sqrt C) / D)\<^sup>2 + b' * (A + B * sqrt C) / D + c'"
        using sum_over_degree_insertion[OF insertionp degree2, of "(A + B * sqrt C) / D", symmetric] unfolding  
          a'_insertion[symmetric] b'_insertion[symmetric] c'_insertion[symmetric] 
          insertion_isovarspars_free[of _ _ "(A + B * sqrt C) / D" _ _ x]
        unfolding two apply simp
        using assms(12) by force
      have insertion_simp : "insertion (nth_default 0 ((xs' @ x # xs)[var := (A + B * sqrt C) / D])) = insertion (nth_default 0 ((xs' @ ((A + B * sqrt C) / D) # xs)))"
        using assms
        by (metis list_update_length) 
      have degreeone : "MPoly_Type.degree
                  (isolate_variable_sparse p var (Suc 0) * Const 1 +
                   isolate_variable_sparse p var (Suc (Suc 0)) * Var var * Const 2)
                  var = 1"
        apply(rule degree_less_sum'[where n=0])
        apply (simp add: degree_isovarspar mult_one_right)
        apply (smt One_nat_def ExecutiblePolyProps.degree_one degree2 degree_const degree_isovarspar degree_mult degreenonzero isolate_variable_sparse_degree_eq_zero_iff mult.commute nonzero_const_is_nonzero numeral_2_eq_2 plus_1_eq_Suc)
        by simp
      have zero1 : " insertion (nth_default 0 (xs' @ (A + B * sqrt C) / D # xs))
     (isolate_variable_sparse (isolate_variable_sparse p var (Suc 0)) var (Suc 0)) = 0"
        by (simp add: degree_isovarspar isovar_greater_degree) 
      have zero2 : "insertion (nth_default 0 (xs' @ (A + B * sqrt C) / D # xs))
      (isolate_variable_sparse (isolate_variable_sparse p var (Suc (Suc 0))) var 0) = a'"
        using a'_insertion'' degree0isovarspar degree_isovarspar numeral_2_eq_2 by force
      have zero3 : "insertion (nth_default 0 (xs' @ (A + B * sqrt C) / D # xs)) (isolate_variable_sparse (Var var) var (Suc 0)) = 1"
        using isolate_var_one by fastforce
      have zero4 : "insertion (nth_default 0 (xs' @ (A + B * sqrt C) / D # xs))
      (isolate_variable_sparse (isolate_variable_sparse p var (Suc (Suc 0))) var (Suc 0)) = 0"
        by (simp add: degree_isovarspar isovar_greater_degree)
      have insertiona' : " insertion (nth_default 0 (xs' @ (A + B * sqrt C) / D # xs))
       (isolate_variable_sparse
         (isolate_variable_sparse p var (Suc 0) * Const 1 +
          isolate_variable_sparse p var (Suc (Suc 0)) * Var var * Const 2)
         var (Suc 0) *
        Const 1) = 2 * a'"
        unfolding isovarspar_sum isolate_variable_sparse_mult apply auto
        unfolding const_lookup_suc const_lookup_zero Rings.mult_zero_class.mult_zero_right
          Groups.group_add_class.add.group_left_neutral
        unfolding insertion_add insertion_mult insertion_const b'_insertion' apply auto
        unfolding zero1 zero2 zero3 zero4 by auto
      have a' :  "insertion (nth_default 0 (xs' @ (A + B * sqrt C) / D # xs)) (isolate_variable_sparse p var (Suc (Suc 0))) = a'"
        unfolding two[symmetric] unfolding a'_insertion'' by auto
      have var: "insertion (nth_default 0 (xs' @ (A + B * sqrt C) / D # xs)) (Var var) = (A + B * sqrt C) / D" using assms
        by (metis insertion_simp insertion_var length0)
      show ?thesis
        unfolding substInfinitesimalQuadratic.simps substInfinitesimalQuadraticUni.simps
          fields
          convertDerivativeUni.simps map_atomUni.simps quadraticSubUni.simps aEvalUni.simps evalUni.simps evalUni_if
          Rings.mult_zero_class.mult_zero_left Groups.add_0 Rings.mult_zero_class.mult_zero_right
          degree2 simp
          quadratic_sub_fm.simps quadratic_sub_fm_helper.simps liftmap.simps lift00   Groups.monoid_add_class.add_0_right
          quad aEval.simps eval.simps derivative_def apply (simp add:insertion_sum insertion_add insertion_mult insertion_const insertion_var_zero)
        unfolding insertionp 
        unfolding insertion_simp
        unfolding b'_insertion'' a'_insertion'' 
        unfolding 
          degreeone apply simp
        unfolding a' var
        unfolding insertiona'
        using weird[OF assms(6)] by auto
    qed
  qed
qed

lemma convert_substInfinitesimalQuadratic: 
  assumes "convert_atom var At (xs'@ x#xs) = Some(At')"
  assumes "insertion (nth_default 0 (xs'@ x#xs)) a = A"
  assumes "insertion (nth_default 0 (xs'@ x#xs)) b = B"
  assumes "insertion (nth_default 0 (xs'@ x#xs)) c = C"
  assumes "insertion (nth_default 0 (xs'@ x#xs)) d = D"
  assumes "D \<noteq> 0"
  assumes "0 \<le> C"
  assumes "var\<notin>(vars a)"
  assumes "var\<notin>(vars b)"
  assumes "var\<notin>(vars c)"
  assumes "var\<notin>(vars d)"
  assumes "length xs' = var"
  shows "eval (substInfinitesimalQuadratic var a b c d At) (xs'@ x#xs) = evalUni (substInfinitesimalQuadraticUni A B C D At') x"
  using assms
proof(cases At)
  case (Less p)
  define p' where "p' = (case convert_poly var p (xs'@ x#xs) of Some p' \<Rightarrow> p')"
  have At'_simp :  "At' = LessUni p'"
    using assms Less
    using p'_def by auto 
  show ?thesis 
    using convert_substInfinitesimalQuadratic_less[OF _ assms(2-12)]
    by (metis At'_simp Less None_eq_map_option_iff assms(1) convert_atom.simps(1) option.distinct(1) option.exhaust_sel option.the_def p'_def substInfinitesimalQuadraticUni.simps(2) substInfinitesimalQuadratic.simps(2))
next
  case (Eq p)
  define p' where "p' = (case convert_poly var p (xs'@ x#xs) of Some p' \<Rightarrow> p')"
  have At'_simp :  "At' = EqUni p'"
    using assms Eq
    using p'_def by auto 
  show ?thesis 
    unfolding At'_simp Eq  substInfinitesimalQuadraticUni.simps substInfinitesimalQuadratic.simps
    using At'_simp Eq assms(1) convert_substNegInfinity assms(12) by fastforce
next
  case (Leq p)
  define p' where "p' = (case convert_poly var p (xs'@ x#xs) of Some p' \<Rightarrow> p')"
  have At'_simp :  "At' = LeqUni p'"
    using assms Leq
    using p'_def by auto 
  have allzero : "eval (allZero p var) (xs'@ x#xs) = evalUni (allZero' p') x"
    using Leq assms(1) convert_allZero p'_def assms(12) by force
  have less : "eval (quadratic_sub_fm var a b c d (convertDerivative var p)) (xs'@ x#xs) = evalUni (map_atomUni (quadraticSubUni A B C D) (convertDerivativeUni p')) x"
    using convert_substInfinitesimalQuadratic_less[OF _ assms(2-12)]
    by (metis Leq assms(1) convert_atom.simps(3) option.distinct(1) option.exhaust_sel option.map(1) option.the_def p'_def)
  show ?thesis 
    unfolding At'_simp Leq substInfinitesimalQuadraticUni.simps substInfinitesimalQuadratic.simps
      eval.simps evalUni.simps
    using allzero less by auto
next
  case (Neq p)
  define p' where "p' = (case convert_poly var p (xs'@ x#xs) of Some p' \<Rightarrow> p')"
  have At'_simp :  "At' = NeqUni p'"
    using assms Neq
    using p'_def by auto 
  show ?thesis 
    unfolding At'_simp Neq substInfinitesimalQuadraticUni.simps substInfinitesimalQuadratic.simps
    by (metis assms(12) At'_simp Neq assms(1) convert_substNegInfinity eval.simps(6) eval_neg substNegInfinityUni.simps(4) substNegInfinity.simps(4))
qed

lemma infinitesimal_quad_helper:
  fixes A B C D:: "real"
  assumes at_is: "At = LessUni p \<or> At = EqUni p"
  assumes "D\<noteq>0"
  assumes "C\<ge>0"
  shows "(\<exists>y'::real>((A+B * sqrt(C))/(D)). \<forall>x::real \<in>{((A+B * sqrt(C))/(D))<..y'}. aEvalUni At x)
      = (evalUni (substInfinitesimalQuadraticUni A B C D At) x)"
proof(cases "At = LessUni p")
  case True
  then have LessUni: "At = LessUni p" by auto
  then show ?thesis proof(cases p)
    case (fields a b c)
    show ?thesis 
    proof(cases "2 * (a::real) * (A + B * sqrt C) / D + b = 0")
      case True
      then have True1 : "2 * a * (A + B * sqrt C) / D + b = 0" by auto
      show ?thesis proof(cases "a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c = 0")
        case True
        then have True2 : "a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c = 0" by auto
        then show ?thesis proof(cases "a<0")
          case True
          then show ?thesis unfolding LessUni fields apply (simp add:True1 True2 True)
            using True1 True2 True  
          proof - 
            assume beq: "2 * a * (A + B * sqrt C) / D + b = 0"
            assume root: "a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c = 0"
            assume alt: "a < 0 "
            let ?r = "-((A + B * sqrt C) / D)"
            have beq_var: "b = 2 * a * ?r" using beq
              by auto 
            have root_var: " a * ?r^2 - 2*a*?r*?r + c = 0" using root
              by (simp add: beq_var)
            have "\<exists>y'>- ?r. \<forall>x\<in>{- ?r<..y'}. a * x\<^sup>2 + 2 * a *?r * x + c < 0" 
              using beq_var root_var alt one_root_a_lt0[where a = "a", where b="b", where c="c", where r="?r"]
              by auto
            then show "\<exists>y'>(A + B * sqrt C) / D. \<forall>x\<in>{(A + B * sqrt C) / D<..y'}. a * x\<^sup>2 + b * x + c < 0"
              using beq_var by auto
          qed
        next
          case False
          then show ?thesis unfolding LessUni fields apply (simp add:True1 True2 False)
            using True1 True2 False 
          proof clarsimp 
            fix y'
            assume beq: " 2 * a * (A + B * sqrt C) / D + b = 0"
            assume root: " a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c = 0"
            assume agteq: "\<not> a < 0 "
            assume y_prop: "(A + B * sqrt C) / D < y'"
            have beq_var: "b = 2 * a * (- A - B * sqrt C) / D" using beq
              by (metis (no_types, hide_lams) ab_group_add_class.ab_diff_conv_add_uminus add.left_neutral add_diff_cancel_left' divide_inverse mult.commute mult_minus_right)             
            have root_var: " a * ((- A - B * sqrt C) / D)\<^sup>2 - 2 * a * (- A - B * sqrt C) * (- A - B * sqrt C) / (D * D) + c =  0"
              using root
            proof -
              have f1: "\<And>r ra. - ((r::real) + ra) = - r - ra"
                by auto
              have f2: "\<And>r ra. r * (a * 2 * (- A - B * sqrt C)) / (ra * D) = r / (ra / b)"
                by (simp add: beq_var)
              have f3: "c - 0 + a * ((A + B * sqrt C) / D)\<^sup>2 = - (b * (A + B * sqrt C) / D)"
                using root by force
              have f4: "\<And>r ra rb. ((- (r::real) - ra) / rb)\<^sup>2 = ((r + ra) / rb)\<^sup>2"
                using f1 by (metis (no_types) divide_minus_left power2_minus)
              have "\<And>r ra rb rc. - ((r::real) * (ra + rb) / rc) = r * (- ra - rb) / rc"
                using f1 by (metis divide_divide_eq_right divide_minus_left mult.commute)
              then show ?thesis
                using f4 f3 f2 by (simp add: mult.commute)
            qed 
            have y_prop_var: "- ((- A - B * sqrt C) / D) < y'" using y_prop
              by (metis add.commute diff_minus_eq_add divide_minus_left minus_diff_eq)
            have "\<exists>x\<in>{- (- (A + B * sqrt C) / D)<..y'}. \<not> a * x\<^sup>2 + 2 * a * (- (A + B * sqrt C) / D) * x + c < 0"
              using y_prop_var beq_var root_var agteq one_root_a_gt0[where a = "a", where b ="b", where c = "c", where r= "-(A + B * sqrt C) / D"]
              by auto
            then show " \<exists>x\<in>{(A + B * sqrt C) / D<..y'}. \<not> a * x\<^sup>2 + b * x + c < 0"
            proof -
              have f1: "2 * a * (A + B * sqrt C) * inverse D + b = 0"
                by (metis True1 divide_inverse)
              obtain rr :: real where
                f2: "rr \<in> {- (- (A + B * sqrt C) / D)<..y'} \<and> \<not> a * rr\<^sup>2 + 2 * a * (- (A + B * sqrt C) / D) * rr + c < 0"
                using \<open>\<exists>x\<in>{- (- (A + B * sqrt C) / D)<..y'}. \<not> a * x\<^sup>2 + 2 * a * (- (A + B * sqrt C) / D) * x + c < 0\<close> by blast
              have f3: "a * ((A + B * sqrt C) * (inverse D * 2)) = - b"
                using f1 by linarith
              have f4: "\<forall>r. - (- (r::real)) = r"
                by simp
              have f5: "\<forall>r ra. (ra::real) * - r = r * - ra"
                by simp
              have f6: "a * ((A + B * sqrt C) * (inverse D * - 2)) = b"
                using f3 by simp
              have f7: "\<forall>r ra rb. (rb::real) * (ra * r) = r * (rb * ra)"
                by auto
              have f8: "\<forall>r ra. - (ra::real) * r = ra * - r"
                by linarith
              then have f9: "a * (inverse D * ((A + B * sqrt C) * - 2)) = b"
                using f7 f6 f5 by presburger
              have f10: "rr \<in> {inverse D * (A + B * sqrt C)<..y'}"
                using f4 f2 by (metis (no_types) divide_inverse mult.commute mult_minus_right)
              have "\<not> c + (rr * b + a * rr\<^sup>2) < 0"
                using f9 f8 f7 f2 by (metis (no_types) add.commute divide_inverse mult.commute mult_minus_right)
              then show ?thesis
                using f10 by (metis (no_types) add.commute divide_inverse mult.commute)
            qed
          qed
        qed
      next
        case False
        then have False1 : "a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c \<noteq> 0" by auto 
        show ?thesis proof(cases "a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c < 0")
          case True
          show ?thesis unfolding LessUni fields apply (simp add: True1 True)
            using True1 True   
          proof -
            let ?r = "(A + B * sqrt C) / D"
            assume " 2 * a * (A + B * sqrt C) / D + b = 0"
            assume "a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c < 0 "
            then have " \<exists>y'>(A + B * sqrt C) / D. \<forall>x\<in>{(A + B * sqrt C) / D<..y'}. poly [:c, b, a:] x < 0"  using continuity_lem_lt0[where r= "(A + B * sqrt C) / D", where c = "c", where b = "b", where a="a"]
                quadratic_poly_eval[of c b a ?r]  by auto
            then show "\<exists>y'>(A + B * sqrt C) / D. \<forall>x\<in>{(A + B * sqrt C) / D<..y'}. a * x\<^sup>2 + b * x + c < 0"
              using quadratic_poly_eval[of c b a]
              by fastforce 
          qed
        next
          case False
          then have False' : "a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c > 0" using False1 by auto
          show ?thesis unfolding LessUni fields apply(simp add: True1 False False1) 
            using True1 False' continuity_lem_gt0_expanded[where a = "a", where b = "b",where c = "c", where r = "((A + B * sqrt C) / D)"]
            by (metis mult_less_0_iff not_square_less_zero times_divide_eq_right)
        qed
      qed
    next
      case False
      then have False1 : "2 * a * (A + B * sqrt C) / D + b \<noteq> 0" by auto
      have c1: "a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c = 0 \<Longrightarrow>
    2 * a * (A + B * sqrt C) / D + b < 0 \<Longrightarrow>
    \<exists>y'>(A + B * sqrt C) / D. \<forall>x\<in>{(A + B * sqrt C) / D<..y'}. a * x\<^sup>2 + b * x + c < 0"
      proof -
        assume root: "a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c = 0"
        assume blt: " 2 * a * (A + B * sqrt C) / D + b < 0"
        let ?r = "-(A + B * sqrt C) / D"
        have bltvar: "b < 2 * a * ?r" using blt divide_minus_left mult_2 mult_minus_right real_add_less_0_iff
          by (metis times_divide_eq_right)
        have rootvar: "a * ?r^2 - b * ?r + c = 0" using root
        proof -
          have f1: "\<forall>r ra. - (ra::real) * r = ra * - r"
            by simp
          have f2: "\<forall>r ra. ((ra::real) * - r)\<^sup>2 = (ra * r)\<^sup>2"
            by simp
          have f3: "a * (inverse D * (A - B * - sqrt C))\<^sup>2 - inverse D * (b * - (A - B * - sqrt C)) - - c = 0"
            by (metis (no_types) diff_minus_eq_add divide_inverse mult.commute mult_minus_left root)
          have f4: "\<forall>r ra rb. (rb::real) * (ra * r) = ra * (r * rb)"
            by simp
          have "\<forall>r ra. (ra::real) * - r = r * - ra"
            by simp
          then have "a * (inverse D * (A - B * - sqrt C))\<^sup>2 - b * (inverse D * - (A - B * - sqrt C)) - - c = 0"
            using f4 f3 f1 by (metis (no_types))
          then have "a * (inverse D * - (A - B * - sqrt C))\<^sup>2 - b * (inverse D * - (A - B * - sqrt C)) - - c = 0"
            using f2 by presburger
          then show ?thesis
            by (simp add: divide_inverse mult.commute)
        qed
        have "\<exists>y'> ((A + B * sqrt C) / D). \<forall>x\<in>{((A + B * sqrt C) / D)<..y'}. a * x\<^sup>2 + b * x + c < 0"
          using rootvar bltvar case_d1[where a= "a", where b = "b", where c = "c", where r = ?r]
          by (metis add.inverse_inverse divide_inverse mult_minus_left)
        then show ?thesis
          by blast 
      qed
      have c2: " \<And>y'. a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c = 0 \<Longrightarrow>
          \<not> 2 * a * (A + B * sqrt C) / D + b < 0 \<Longrightarrow>
          (A + B * sqrt C) / D < y' \<Longrightarrow>
          \<exists>x\<in>{(A + B * sqrt C) / D<..y'}. \<not> a * x\<^sup>2 + b * x + c < 0"
      proof - 
        let ?r = "(A + B * sqrt C) / D"
        fix y'
        assume h1: "a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c = 0"
        assume h2: "\<not> 2 * a * (A + B * sqrt C) / D + b < 0"
        assume h3: " (A + B * sqrt C) / D < y'"
        have eq: "2 * a * (A + B * sqrt C) / D + b = 0 \<Longrightarrow> \<exists>x\<in>{(A + B * sqrt C) / D..y'}. \<not> a * x\<^sup>2 + b * x + c < 0"
          using False1 by blast
        have "2 * a * (A + B * sqrt C) / D + b > 0 \<Longrightarrow> \<exists>x\<in>{?r<..y'}. \<not> a * x\<^sup>2 + b * x + c < 0" 
          using case_d4[where a = "a", where b = "b", where c= "c", where r = "-?r"] h1 h2 h3 by auto
        then show "\<exists>x\<in>{(A + B * sqrt C) / D<..y'}. \<not> a * x\<^sup>2 + b * x + c < 0" using h2 eq
          using False1 by linarith
      qed
      have c3: "((a::real) * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c < 0) \<longrightarrow>
    (\<exists>y'>((A + B * sqrt C) / D). \<forall>x\<in>{(A + B * sqrt C) / D<..y'}. a * x\<^sup>2 + b * x + c < 0)"
      proof clarsimp 
        assume assump: "a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c < 0 "
        have "a * ((A + B * sqrt C) / D)\<^sup>2 + b * ((A + B * sqrt C) / D) + c < 0 \<Longrightarrow>
  \<exists>y'>(A + B * sqrt C) / D. \<forall>x\<in>{(A + B * sqrt C) / D<..y'}. a * x\<^sup>2 + b * x + c < 0" 
          using continuity_lem_lt0_expanded[where a= "a", where b = "b", where c = "c", where r = "((A + B * sqrt C) / D)::real"]
          by auto
        then have "\<exists>y'>(A + B * sqrt C) / D. \<forall>x\<in>{(A + B * sqrt C) / D<..y'}. a * x\<^sup>2 + b * x + c < 0" using assump by auto
        then obtain y where y_prop: "y >(A + B * sqrt C) / D \<and> (\<forall>x\<in>{(A + B * sqrt C) / D<..y}. a * x\<^sup>2 + b * x + c < 0)" by auto
        then have h: "\<exists> k. k >(A + B * sqrt C) / D \<and> k < y" using dense
          by blast 
        then obtain k where k_prop: "k >(A + B * sqrt C) / D  \<and> k < y" by auto
        then have "\<forall>x\<in>{(A + B * sqrt C) / D..k}. a * x\<^sup>2 + b * x + c < 0" using y_prop
          using assump by force 
        then show "\<exists>y'>((A + B * sqrt C) / D::real). \<forall>x\<in>{(A + B * sqrt C) / D<..y'}. a * x\<^sup>2 + b * x + c < 0"
          using k_prop by auto
      qed
      have c4: "\<And>y'. a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c \<noteq> 0 \<Longrightarrow>
          \<not> a * ((A + B * sqrt C) / D)\<^sup>2 + b * (A + B * sqrt C) / D + c < 0 \<Longrightarrow>
          (A + B * sqrt C) / D < y' \<Longrightarrow>
          \<exists>x\<in>{(A + B * sqrt C) / D<..y'}. \<not> a * x\<^sup>2 + b * x + c < 0"
        using continuity_lem_gt0_expanded[where a= "a", where b = "b", where c = "c", where r= "(A + B * sqrt C) / D"]
        by (metis Groups.mult_ac(1) divide_inverse less_eq_real_def linorder_not_le)
      show ?thesis unfolding LessUni fields apply(simp add: False1) 
        using c1 c2 c3 c4 by auto
    qed
  qed
next
  case False
  then have EqUni: "At = EqUni p" using at_is by auto
  then show ?thesis proof(cases p) 
    case (fields a b c) 
    have " \<And>y'. (A + B * sqrt C) / D < y' \<Longrightarrow>
          \<forall>x\<in>{(A + B * sqrt C) / D<..y'}. a * x\<^sup>2 + b * x + c = 0 \<Longrightarrow> (a = 0 \<and> b = 0 \<and> c = 0)"
    proof -
      fix y'
      assume "(A + B * sqrt C) / D < y'"
      then show " \<forall>x\<in>{(A + B * sqrt C) / D<..y'}. a * x\<^sup>2 + b * x + c = 0 \<Longrightarrow> (a = 0 \<and> b = 0 \<and> c = 0)" using assms continuity_lem_eq0[where r = "(A + B * sqrt C) / D", where p = "y'", where a= "a", where b ="b", where c="c"]
        by auto
    qed
    then show ?thesis
      apply (auto simp add:EqUni fields )
      using linordered_field_no_ub by blast
  qed
qed

lemma infinitesimal_quad:
  fixes A B C D:: "real"
  assumes "D\<noteq>0"
  assumes "C\<ge>0"
  shows "(\<exists>y'::real>((A+B * sqrt(C))/(D)). \<forall>x::real \<in>{((A+B * sqrt(C))/(D))<..y'}. aEvalUni At x)
      = (evalUni (substInfinitesimalQuadraticUni A B C D At) x)"
proof(cases At)
  case (LessUni p)
  then show ?thesis using infinitesimal_quad_helper assms
    by blast 
next
  case (EqUni p)
  then show ?thesis
    using infinitesimal_quad_helper assms
    by blast 
next
  case (LeqUni p)
  then show ?thesis 
  proof (cases p)
    case (fields a b c) 
    have same: "\<forall>x. aEvalUni (LeqUni p) x = (aEvalUni (EqUni p) x) \<or> (aEvalUni (LessUni p) x)" 
      apply (simp add: fields)
      by force 
    let ?r = "(A + B * sqrt C) / D"
    have "\<And>a b c.
       At = LeqUni p \<Longrightarrow>
       p = (a, b, c) \<Longrightarrow>
       (\<exists>y'>(A + B * sqrt C) / D. \<forall>x\<in>{(A + B * sqrt C) / D<..y'}. aEvalUni At x) =
       evalUni (substInfinitesimalQuadraticUni A B C D At) x"
    proof - 
      fix a b c
      assume atis: "At = LeqUni p"
      assume p_is: " p = (a, b, c)"
      have s1: "(\<exists>y'>?r. \<forall>x\<in>{?r<..y'}. aEvalUni At x) = (\<exists>y'>?r. \<forall>x\<in>{?r<..y'}.  (aEvalUni (EqUni p) x) \<or> (aEvalUni (LessUni p) x))"
        using atis same aEvalUni.simps(2) aEvalUni.simps(3) fields less_eq_real_def 
        by blast
      have s2: "... = (\<exists>y'>?r. \<forall>x\<in>{?r<..y'}.  (aEvalUni (EqUni p) x)) \<or> (\<exists>y'>?r. \<forall>x\<in>{?r<..y'}. (aEvalUni (LessUni p) x))"
        using either_or[where r = "?r"] p_is 
        by blast 
      have eq1: "(\<exists>y'>?r. \<forall>x\<in>{?r<..y'}.  (aEvalUni (EqUni p) x)) =  (evalUni (substInfinitesimalQuadraticUni A B C D (EqUni p)) x)"
        using infinitesimal_quad_helper[where At = "EqUni p", where p = "p", where B = "B", where C= "C", where A= "A", where D="D"] 
          assms  by auto
      have eq2: "(\<exists>y'>?r. \<forall>x\<in>{?r<..y'}.  (aEvalUni (LessUni p) x)) =  (evalUni (substInfinitesimalQuadraticUni A B C D (LessUni p)) x)"
        using infinitesimal_quad_helper[where At = "LessUni p", where p = "p", where B = "B", where C= "C", where A= "A", where D="D"] 
          assms by auto
      have z1: "(\<exists>y'>?r. \<forall>x\<in>{?r<..y'}. aEvalUni At x) = ((evalUni (substInfinitesimalQuadraticUni A B C D (EqUni p)) x) \<or> (evalUni (substInfinitesimalQuadraticUni A B C D (LessUni p)) x))"
        using s1 s2 eq1 eq2 by auto
      have z2: "(evalUni (substInfinitesimalQuadraticUni A B C D (EqUni p)) x) \<or> (evalUni (substInfinitesimalQuadraticUni A B C D (LessUni p)) x) = evalUni (substInfinitesimalQuadraticUni A B C D (LeqUni p)) x" 
        by auto
      have z3: "(evalUni (substInfinitesimalQuadraticUni A B C D At) x) = evalUni (substInfinitesimalQuadraticUni A B C D (LeqUni p)) x"
        using LeqUni by auto
      then have z4: "(evalUni (substInfinitesimalQuadraticUni A B C D (EqUni p)) x) \<or> (evalUni (substInfinitesimalQuadraticUni A B C D (LessUni p)) x) = (evalUni (substInfinitesimalQuadraticUni A B C D At) x) "
        using z2 z3 by auto
      let ?a = "(evalUni (substInfinitesimalQuadraticUni A B C D (EqUni p)) x) \<or> (evalUni (substInfinitesimalQuadraticUni A B C D (LessUni p)) x)"
      let ?b = "(\<exists>y'>?r. \<forall>x\<in>{?r<..y'}. aEvalUni At x)"
      let ?c = "(evalUni (substInfinitesimalQuadraticUni A B C D At) x)"
      have t1: "?b = ?a" using z1 by auto
      have t2: "?a = ?c" using z4
        using atis by auto
      then have "?b = ?c" using t1 t2 by auto
      then show "(\<exists>y'>?r. \<forall>x\<in>{?r<..y'}. aEvalUni At x) = evalUni (substInfinitesimalQuadraticUni A B C D At) x"
        by auto
    qed
    then show ?thesis
      using LeqUni fields by blast 
  qed
next
  case (NeqUni p)
  then show ?thesis
  proof (cases p)
    case (fields a b c) 
    then show ?thesis unfolding NeqUni fields using nonzcoeffs by auto
  qed
qed


end