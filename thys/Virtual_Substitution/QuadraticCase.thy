subsection "Quadratic Case"
theory QuadraticCase
  imports VSAlgos
begin

(*-------------------------------------------------------------------------------------------------------------*)
lemma quad_part_1_eq :
  assumes lLength : "length L > var"
  assumes hdeg : "MPoly_Type.degree (p::real mpoly) var = (deg::nat)"
  assumes nonzero : "D \<noteq> 0"
  assumes ha : "\<forall>x. insertion (nth_default 0 (list_update L var x)) a = (A::real)"
  assumes hb : "\<forall>x. insertion (nth_default 0 (list_update L var x)) b = (B::real)"
  assumes hd : "\<forall>x. insertion (nth_default 0 (list_update L var x)) d = (D::real)"
  shows "aEval (Eq p) (list_update L var ((A+B*C)/D)) = aEval (Eq(quadratic_part_1 var a b d (Eq p))) (list_update L var C)"
proof - 
  define f where "f i = insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C) ^ i)" for i
  have h1 : "\<forall>i. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i)) = (insertion (nth_default 0 (list_update L var ((A+B*C)/D))) (isolate_variable_sparse p var i))"
    by(simp add: insertion_isovarspars_free)
  have h2 : "((\<Sum>i = 0..<deg+1. f i / D ^ i) = 0) =((\<Sum>i = 0..<deg+1. (f i) * D ^ (deg - i)) = 0)"
    using normalize_summation nonzero by(auto)
  have "aEval (Eq(quadratic_part_1 var a b d (Eq p))) (list_update L var C) = 
      ((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C) ^ i)) * D ^ (deg - i)) = 0)"
    by(simp add: hdeg insertion_sum insertion_add insertion_mult insertion_var insertion_pow ha hb hd lLength)
  also have "... =((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C) ^ i)) / D ^ i) = 0)"
    using f_def h2 by auto
  also have "... =((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C)^i / (D ^ i)))) = 0)"
    by auto
  also have "... =((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C)/D) ^ i)) = 0)"
    by (metis (no_types, lifting) power_divide sum.cong)
  also have "... =((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var ((A+B*C)/D))) (isolate_variable_sparse p var i) * ((A + B * C)/D) ^ i))=0)"
    using h1 by auto 
  also have "... = (insertion (nth_default 0 (list_update L var ((A+B*C)/D))) p =0)"
    using sum_over_degree_insertion hdeg lLength by auto
  also have "... = aEval (Eq p) (list_update L var ((A+B*C)/D))"
    using aEval.simps(1) by blast
  finally show ?thesis using assms by auto
qed


(*------------------------------------------------------------------------------------------------*)
lemma quad_part_1_less :
  assumes lLength : "length L > var"
  assumes hdeg : "MPoly_Type.degree (p::real mpoly) var = (deg::nat)"
  assumes nonzero : "D \<noteq> 0"
  assumes ha : "\<forall>x. insertion (nth_default 0 (list_update L var x)) a = (A::real)"
  assumes hb : "\<forall>x. insertion (nth_default 0 (list_update L var x)) b = (B::real)"
  assumes hd : "\<forall>x. insertion (nth_default 0 (list_update L var x)) d = (D::real)"
  shows "aEval (Less p) (list_update L var ((A+B*C)/D)) = aEval (Less(quadratic_part_1 var a b d (Less p))) (list_update L var C)"
proof - 
  define f where "f i = insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C) ^ i)" for i
  have h1a : "((\<Sum>i = 0..<deg+1. f i / D ^ i) < 0) =((\<Sum>i = 0..<deg+1. (f i) * D ^ (deg - i))  * D ^ (deg mod 2) < 0)"
    using normalize_summation_less nonzero by(auto)
  have h4a : "\<forall>i. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i)) = (insertion (nth_default 0 (list_update L var ((A+B*C)/D))) (isolate_variable_sparse p var i))"
    by(simp add: insertion_isovarspars_free)
  have "((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C) ^ i)) * D ^ (deg - i)) * D ^ (deg mod 2) < 0)
        =((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C) ^ i)) / D ^ i) < 0)"
    using h1a f_def by auto
  also have "...=((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C)^i / (D ^ i)))) < 0)"
    by auto
  also have "...=((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C)/D) ^ i)) < 0)"
    by (metis (no_types, lifting) power_divide sum.cong)
  also have "... =((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var ((A+B*C)/D)))  (isolate_variable_sparse p var i) * ((A + B * C)/D) ^ i))<0)"
    using h4a
    by auto 
  also have "... = (insertion (nth_default 0 (list_update L var ((A+B*C)/D))) p <0)"
    using sum_over_degree_insertion hdeg lLength by auto
  finally show ?thesis
    by(simp add: hdeg lLength insertion_add insertion_mult ha hb hd insertion_sum insertion_pow insertion_var)
qed

(*------------------------------------------------------------------------------------------------*)
lemma quad_part_1_leq :
  assumes lLength : "length L > var"
  assumes hdeg : "MPoly_Type.degree (p::real mpoly) var = (deg::nat)"
  assumes nonzero : "D \<noteq> 0"
  assumes ha : "\<forall>x. insertion (nth_default 0 (list_update L var x)) a = (A::real)"
  assumes hb : "\<forall>x. insertion (nth_default 0 (list_update L var x)) b = (B::real)"
  assumes hd : "\<forall>x. insertion (nth_default 0 (list_update L var x)) d = (D::real)"
  shows "aEval (Leq p) (list_update L var ((A+B*C)/D)) = aEval (Leq(quadratic_part_1 var a b d (Leq p))) (list_update L var C)"
proof - 
  define f where "f i = insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C) ^ i)" for i
  have h1a : "((\<Sum>i = 0..<deg+1. f i / D ^ i) < 0) =((\<Sum>i = 0..<deg+1. (f i) * D ^ (deg - i))  * D ^ (deg mod 2) < 0)"
    using normalize_summation_less nonzero by(auto)
  have h1b : "((\<Sum>i = 0..<deg+1. f i / D ^ i) = 0) =((\<Sum>i = 0..<deg+1. (f i) * D ^ (deg - i)) = 0)"
    using normalize_summation nonzero by(auto)
  have h1c : "((\<Sum>i = 0..<deg+1. f i / D ^ i) \<le> 0) =((\<Sum>i = 0..<deg+1. (f i) * D ^ (deg - i))  * D ^ (deg mod 2) \<le> 0)"
    using h1a h1b nonzero by auto 
  have h4a : "\<forall>i. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i)) = (insertion (nth_default 0 (list_update L var ((A+B*C)/D))) (isolate_variable_sparse p var i))"
    by(simp add: insertion_isovarspars_free)
  have "((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C) ^ i)) * D ^ (deg - i)) * D ^ (deg mod 2) \<le> 0)=
    ((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C) ^ i)) / D ^ i) \<le> 0)"
    using h1c f_def by auto
  also have "...=((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C)^i / (D ^ i)))) \<le> 0)"
    by auto
  also have "...=((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var C)) (isolate_variable_sparse p var i) * ((A + B * C)/D) ^ i)) \<le> 0)"
    by (metis (no_types, lifting) power_divide sum.cong)
  also have "...=((\<Sum>i = 0..<deg+1. (insertion (nth_default 0 (list_update L var ((A+B*C)/D))) (isolate_variable_sparse p var i) * ((A + B * C)/D) ^ i))\<le>0)"
    using h4a by auto 
  also have "... = (insertion (nth_default 0 (list_update L var ((A+B*C)/D))) p\<le>0)"
    using sum_over_degree_insertion hdeg lLength by auto
  finally show ?thesis
    by(simp add: hdeg lLength insertion_add insertion_mult ha hb hd insertion_sum insertion_pow insertion_var)
qed

(*------------------------------------------------------------------------------------------------*)
lemma quad_part_1_neq :
  assumes lLength : "length L > var"
  assumes hdeg : "MPoly_Type.degree (p::real mpoly) var = (deg::nat)"
  assumes nonzero : "D \<noteq> 0"
  assumes ha : "\<forall>x. insertion (nth_default 0 (list_update L var x)) a = (A::real)"
  assumes hb : "\<forall>x. insertion (nth_default 0 (list_update L var x)) b = (B::real)"
  assumes hd : "\<forall>x. insertion (nth_default 0 (list_update L var x)) d = (D::real)"
  shows "aEval (Neq p) (list_update L var ((A+B*C)/D)) = aEval (Neq(quadratic_part_1 var a b d (Neq p))) (list_update L var C)"
proof -
  have "aEval (Eq(quadratic_part_1 var a b d (Eq p))) (list_update L var C) = aEval (Eq p) (list_update L var ((A+B*C)/D))"
    using quad_part_1_eq assms by blast
  then show ?thesis by auto
qed

(*------------------------------------------------------------------------------------------------*)


lemma sqrt_case : 
  assumes detGreater0 : "SQ \<ge> 0"
  shows "((SQ^(i div 2)) * real (i mod 2) * sqrt SQ + SQ ^ (i div 2) * (1 - real (i mod 2))) = (sqrt SQ) ^ i"
proof -
  have h1 : "i mod 2 = 0 \<or> (odd i \<and> (i mod 2 = 1))"
    by auto
  have h2 : "i mod 2 = 0 \<Longrightarrow> ((SQ^(i div 2)) * real (i mod 2) * sqrt SQ + SQ ^ (i div 2) * (1 - real (i mod 2))) = (sqrt SQ) ^ i"
    using detGreater0 apply auto
    by (simp add: real_sqrt_power_even)
  have h3 : "(odd i \<and> (i mod 2 = 1)) \<Longrightarrow> ((SQ^(i div 2)) * real (i mod 2) * sqrt SQ + SQ ^ (i div 2) * (1 - real (i mod 2))) = (sqrt SQ) ^ i"
    using detGreater0 apply auto
    by (smt One_nat_def add_Suc_right mult.commute nat_arith.rule0 odd_two_times_div_two_succ power.simps(2) power_mult real_sqrt_pow2)
  show ?thesis
    using h1 h2 h3
    by linarith 
qed

lemma sum_over_sqrt :
  assumes detGreater0 : "SQ \<ge> 0"
  shows "(\<Sum>i\<in>{0..<n+1}. ((f i::real) * (SQ^(i div 2)) * real (i mod 2) * sqrt SQ +f i * SQ ^ (i div 2) * (1 - real (i mod 2))))
        =(\<Sum>i\<in>{0..<n+1}. ((f i::real) * ((sqrt SQ)^i)))"
  using sqrt_case detGreater0
  by (metis (no_types, hide_lams) distrib_left mult.assoc) 

lemma quad_part_2_eq :
  assumes lLength : "length L > var"
  assumes detGreater0 : "SQ\<ge>0"
  assumes hdeg : "MPoly_Type.degree (p::real mpoly) var = (deg ::nat)"
  assumes hsq : "\<forall>x. insertion (nth_default 0 (list_update L var x)) sq = (SQ::real)"
  shows "aEval (Eq p) (list_update L var (sqrt SQ)) = aEval (Eq(quadratic_part_2 var sq p)) (list_update L var (sqrt SQ))"
proof -
  define f where "f i = insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i)" for i
  have h1a : "(\<Sum>i\<in>{0..<deg+1}. (f i * (SQ^(i div 2)) * real (i mod 2) * sqrt SQ +f i * SQ ^ (i div 2) * (1 - real (i mod 2))))
             =(\<Sum>i\<in>{0..<deg+1}. (f i * ((sqrt SQ)^i)))"
    using sum_over_sqrt detGreater0 by auto
  have "(\<Sum>i\<in>{0..<deg+1}. (insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i) * (SQ^(i div 2)) * real (i mod 2) * sqrt SQ + (insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i)) * SQ ^ (i div 2) * (1 - real (i mod 2))))
             =(\<Sum>i\<in>{0..<deg+1}. (insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i) * ((sqrt SQ)^i)))"
    using h1a f_def by auto
  also have "... = insertion (nth_default 0 (list_update L var (sqrt SQ))) p"
    using sum_over_degree_insertion hdeg lLength by auto
  finally show ?thesis
    by(simp add:hdeg hsq insertion_add insertion_sum insertion_mult insertion_pow insertion_var insertion_const lLength)
qed

lemma quad_part_2_less :
  assumes lLength : "length L > var"
  assumes detGreater0 : "SQ\<ge>0"
  assumes hdeg : "MPoly_Type.degree (p::real mpoly) var = (deg ::nat)"
  assumes hsq : "\<forall>x. insertion (nth_default 0 (list_update L var x)) sq = (SQ::real)"
  shows "aEval (Less p) (list_update L var (sqrt SQ)) = aEval (Less(quadratic_part_2 var sq p)) (list_update L var (sqrt SQ))"
proof -
  define f where "f i = insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i)" for i
  have h1a : "(\<Sum>i\<in>{0..<deg+1}. (f i * (SQ^(i div 2)) * real (i mod 2) * sqrt SQ +f i * SQ ^ (i div 2) * (1 - real (i mod 2))))
             =(\<Sum>i\<in>{0..<deg+1}. (f i * ((sqrt SQ)^i)))"
    using sum_over_sqrt detGreater0 by auto
  have "(\<Sum>i\<in>{0..<deg+1}. (insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i) * (SQ^(i div 2)) * real (i mod 2) * sqrt SQ + (insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i)) * SQ ^ (i div 2) * (1 - real (i mod 2))))
             =(\<Sum>i\<in>{0..<deg+1}. (insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i) * ((sqrt SQ)^i)))"
    using h1a f_def by auto
  also have "... = insertion (nth_default 0 (list_update L var (sqrt SQ))) p"
    using sum_over_degree_insertion hdeg lLength by auto
  finally show ?thesis
    by(simp add:hdeg hsq insertion_add insertion_sum insertion_mult insertion_pow insertion_var insertion_const lLength)
qed

lemma quad_part_2_neq :
  assumes lLength : "length L > var"
  assumes detGreater0 : "SQ\<ge>0"
  assumes hdeg : "MPoly_Type.degree (p::real mpoly) var = (deg ::nat)"
  assumes hsq : "\<forall>x. insertion (nth_default 0 (list_update L var x)) sq = (SQ::real)"
  shows "aEval (Neq p) (list_update L var (sqrt SQ)) = aEval (Neq(quadratic_part_2 var sq p)) (list_update L var (sqrt SQ))"
proof -
  define f where "f i = insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i)" for i
  have h1a : "(\<Sum>i\<in>{0..<deg+1}. (f i * (SQ^(i div 2)) * real (i mod 2) * sqrt SQ +f i * SQ ^ (i div 2) * (1 - real (i mod 2))))
             =(\<Sum>i\<in>{0..<deg+1}. (f i * ((sqrt SQ)^i)))"
    using sum_over_sqrt detGreater0 by auto
  have "(\<Sum>i\<in>{0..<deg+1}. (insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i) * (SQ^(i div 2)) * real (i mod 2) * sqrt SQ + (insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i)) * SQ ^ (i div 2) * (1 - real (i mod 2))))
             =(\<Sum>i\<in>{0..<deg+1}. (insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i) * ((sqrt SQ)^i)))"
    using h1a f_def by auto
  also have "... = insertion (nth_default 0 (list_update L var (sqrt SQ))) p"
    using sum_over_degree_insertion hdeg lLength by auto
  finally show ?thesis
    by(simp add:hdeg hsq insertion_add insertion_sum insertion_mult insertion_pow insertion_var insertion_const lLength)
qed

lemma quad_part_2_leq :
  assumes lLength : "length L > var"
  assumes detGreater0 : "SQ\<ge>0"
  assumes hdeg : "MPoly_Type.degree (p::real mpoly) var = (deg ::nat)"
  assumes hsq : "\<forall>x. insertion (nth_default 0 (list_update L var x)) sq = (SQ::real)"
  shows "aEval (Leq p) (list_update L var (sqrt SQ)) = aEval (Leq(quadratic_part_2 var sq p)) (list_update L var (sqrt SQ))"
proof -
  define f where "f i = insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i)" for i
  have h1a : "(\<Sum>i\<in>{0..<deg+1}. (f i * (SQ^(i div 2)) * real (i mod 2) * sqrt SQ +f i * SQ ^ (i div 2) * (1 - real (i mod 2))))
             =(\<Sum>i\<in>{0..<deg+1}. (f i * ((sqrt SQ)^i)))"
    using sum_over_sqrt detGreater0 by auto
  have "(\<Sum>i\<in>{0..<deg+1}. (insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i) * (SQ^(i div 2)) * real (i mod 2) * sqrt SQ + (insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i)) * SQ ^ (i div 2) * (1 - real (i mod 2))))
             =(\<Sum>i\<in>{0..<deg+1}. (insertion (nth_default 0 (list_update L var (sqrt SQ))) (isolate_variable_sparse p var i) * ((sqrt SQ)^i)))"
    using h1a f_def by auto
  also have "... = insertion (nth_default 0 (list_update L var (sqrt SQ))) p"
    using sum_over_degree_insertion hdeg lLength by auto
  finally show ?thesis
    by(simp add:hdeg hsq insertion_add insertion_sum insertion_mult insertion_pow insertion_var insertion_const lLength)
qed

lemma quad_part_2_deg :
  assumes sqfree : "(var::nat)\<notin>vars(sq::real mpoly)"
  shows "MPoly_Type.degree (quadratic_part_2 var sq p) var \<le> 1"
proof -
  define deg where "deg = MPoly_Type.degree (p::real mpoly) var"
  define f where "f i = isolate_variable_sparse p var i * sq ^ (i div 2) * Const (real (i mod 2)) * Var var" for i
  define g where "g i = isolate_variable_sparse p var i * sq ^ (i div 2) * Const (1 - real (i mod 2))" for i
  have h1a : "\<forall>i. MPoly_Type.degree (isolate_variable_sparse p var i) var = 0"
    by (simp add: varNotIn_degree not_in_isovarspar) 
  have h1b : "\<forall>i. MPoly_Type.degree (sq ^ (i div 2)) var = 0"
    by (simp add: sqfree varNotIn_degree not_in_pow)
  have h1c : "\<forall>i. MPoly_Type.degree (Const (real (i mod 2))) var = 0"
    using degree_const by blast
  have h1d : "MPoly_Type.degree (Var var :: real mpoly) var = 1"
    using degree_one by auto
  have h1 : "\<forall>i<deg+1. MPoly_Type.degree (f i) var \<le> 1"
    using f_def degree_mult h1a h1b h1c h1d
    by (smt ExecutiblePolyProps.degree_one add.right_neutral mult.commute mult_eq_0_iff nat_le_linear not_one_le_zero)
  have h2a : "\<forall>i. MPoly_Type.degree (Const (1 - real (i mod 2))) var = 0"
    using degree_const by blast
  have h2 : "\<forall>i<deg+1. MPoly_Type.degree (g i) var = 0"
    using g_def degree_mult h1a h1b h2a
    by (metis (no_types, lifting) add.right_neutral mult_eq_0_iff)
  have h3 : "\<forall>i<deg+1. MPoly_Type.degree (f i + g i) var \<le> 1"
    using h1 h2 by (simp add: degree_add_leq)
  show ?thesis using atLeastLessThanSuc_atLeastAtMost degree_sum f_def g_def h3 deg_def by auto 
qed



(*------------------------------------------------------------------------------------------------*)

lemma quad_equality_helper :
  assumes lLength : "length L > var"
  assumes detGreat0 : "Cv\<ge>0"
  assumes hC : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (C::real mpoly) = (Cv::real)"
  assumes hA : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (A::real mpoly) = (Av::real)"
  assumes hB : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (B::real mpoly) = (Bv::real)"
  shows "aEval (Eq (A + B * Var var)) (list_update L var (sqrt Cv)) = eval (And (Atom(Leq (A*B))) (Atom (Eq (A^2-B^2*C)))) (list_update L var (sqrt Cv))"
proof-
  have h1 : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (A^2-(B^2)*C) = Av^2-(Bv^2)*Cv"
    by(simp add: hA hB hC insertion_add insertion_mult insertion_sub insertion_pow)
  have h2a : "(Av + Bv * sqrt Cv = 0) = (Av = - Bv * sqrt Cv)"
    by auto
  have h2b : "(Av = - Bv * sqrt Cv) \<Longrightarrow> (Av^2 = (- Bv * sqrt Cv)^2)"
    by simp
  have h2c : "(Av^2 = (- Bv * sqrt Cv)^2) = (Av^2 = Bv^2 * (sqrt Cv)^2)"
    by (simp add: power_mult_distrib)
  have h2d : "(Av^2 = Bv^2 * (sqrt Cv)^2) = (Av^2 = Bv^2 * Cv)"
    by (simp add: detGreat0)
  have h2 : "(Av + Bv * sqrt Cv = 0) \<Longrightarrow> (Av^2 = Bv^2 * Cv)"
    using h2a h2b h2c h2d by blast
  have h3a : "(Av*Bv > 0) \<Longrightarrow> (Av + Bv * sqrt Cv \<noteq> 0)"
    by (smt detGreat0 mult_nonneg_nonneg real_sqrt_ge_zero zero_less_mult_iff)
  have h3 : "(Av + Bv * sqrt Cv = 0) \<Longrightarrow> (Av*Bv\<le> 0)"
    using h3a by linarith
  have h4 : "(Av * Bv \<le> 0 \<and> Av\<^sup>2 = Bv\<^sup>2 * Cv) \<Longrightarrow> (Av + Bv * sqrt Cv = 0)"
    apply(cases "Av>0")
     apply (metis detGreat0 h2a h2c h2d mult_minus_left not_le power2_eq_iff real_sqrt_lt_0_iff zero_less_mult_iff)
    by (smt h2a real_sqrt_abs real_sqrt_mult zero_less_mult_iff)
  show ?thesis
    apply(simp add: hA hB h1 insertion_add insertion_mult insertion_var lLength)
    using h2 h3 h4 by blast
qed

lemma quadratic_sub_eq :
  assumes lLength : "length L > var"
  assumes nonzero : "Dv \<noteq> 0"
  assumes detGreater0 : "Cv \<ge> 0"
  assumes freeC : "var \<notin> vars c"
  assumes ha : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (a::real mpoly) = (Av :: real)"
  assumes hb : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (b::real mpoly) = (Bv :: real)"
  assumes hc : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (c::real mpoly) = (Cv :: real)"
  assumes hd : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (d::real mpoly) = (Dv :: real)"
  shows "aEval (Eq p) (list_update L var ((Av+Bv*sqrt(Cv))/Dv)) = eval (quadratic_sub var a b c d (Eq p)) (list_update L var (sqrt Cv))"
proof -
  define p1 where "(p1::real mpoly) = quadratic_part_1 var a b d (Eq p)"
  define p2 where "(p2::real mpoly) = quadratic_part_2 var c p1"
  define A where "A = isolate_variable_sparse p2 var 0"
  define B where "B = isolate_variable_sparse p2 var 1"
  have h3c : "MPoly_Type.degree p2 var = 0 \<or> MPoly_Type.degree p2 var = 1"
    using freeC quad_part_2_deg p2_def by (meson le_neq_implies_less less_one)
  have h3d : "MPoly_Type.degree p2 var = 0 \<Longrightarrow> B = 0"
    by(simp add: B_def isovar_greater_degree)
  then have h3f : "MPoly_Type.degree p2 var = 0 \<Longrightarrow> p2 = A + B * Var var"
    by(simp add: h3d A_def degree0isovarspar)
  have h3g1 : "MPoly_Type.degree p2 var = 1 \<Longrightarrow> p2 = (\<Sum>i\<le>1. isolate_variable_sparse p2 var i * Var var ^ i)"
    using sum_over_zero by metis 
  have h3g2a : "\<forall>f. (\<Sum>i::nat\<le>1. f i) = f 0 + f 1" by simp
  have h3g2 : "(\<Sum>i::nat\<le>1. isolate_variable_sparse p2 var i * Var var ^ i) = 
                isolate_variable_sparse p2 var 0 * Var var ^ 0 + isolate_variable_sparse p2 var 1 * Var var ^ 1"
    using h3g2a by blast 
  have h3g : "MPoly_Type.degree p2 var = 1 \<Longrightarrow> p2 = A + B * Var var"
    apply(simp add: sum_over_zero A_def B_def)
    using h3g1 h3g2
    by (metis (no_types, lifting) One_nat_def mult_cancel_left2 power_0 power_one_right)
  have h3h : "p2 = A + B * Var var"
    using h3c h3f h3g by auto

  have h4a : "\<exists>x::real. \<forall>y::real. insertion (nth_default 0 (list_update L var y)) A = x"
    using not_contains_insertion not_in_isovarspar A_def by blast
  have h4b : "\<exists>x::real. \<forall>y::real. insertion (nth_default 0 (list_update L var y)) B = x"
    using not_contains_insertion not_in_isovarspar B_def by blast


  have "aEval (Eq p) (list_update L var ((Av+Bv*sqrt(Cv))/Dv)) =  aEval (Eq p1) (list_update L var (sqrt Cv))"
    using p1_def quad_part_1_eq nonzero ha hb hd lLength by blast
  also have h2 : "... = aEval (Eq p2) (list_update L var (sqrt Cv))"
    using p2_def quad_part_2_eq lLength detGreater0 hc by metis
  also have "... = aEval (Eq (A + B * Var var)) (list_update L var (sqrt Cv))"
    using h3h by auto
  also have "... = eval (And (Atom(Leq (A*B))) (Atom (Eq (A^2-B^2*c)))) (list_update L var (sqrt Cv))"
    using quad_equality_helper hc detGreater0 h4a h4b lLength by blast
  also have "... = eval (quadratic_sub var a b c d (Eq p)) (list_update L var (sqrt Cv))"
    using p2_def A_def B_def p1_def quadratic_sub.simps(1) by metis
  finally show ?thesis by blast
qed
  (*------------------------------------------------------------------------------------------------*)
lemma quadratic_sub_less_helper :
  assumes lLength : "length L > var"
  assumes detGreat0 : "Cv\<ge>0"
  assumes hC : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (C::real mpoly) = (Cv::real)"
  assumes hA : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (A::real mpoly) = (Av::real)"
  assumes hB : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (B::real mpoly) = (Bv::real)"
  shows "aEval (Less (A + B * Var var)) (list_update L var (sqrt Cv)) = eval
     (Or (And (fm.Atom (Less A)) (fm.Atom (Less (B\<^sup>2 * C - A\<^sup>2))))
       (And (fm.Atom (Leq B)) (Or (fm.Atom (Less A)) (fm.Atom (Less (A\<^sup>2 - B\<^sup>2 * C))))))
     (list_update L var (sqrt Cv)) "
proof-
  have h1 : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (A^2-(B^2)*C) = Av^2-(Bv^2)*Cv"
    by(simp add: hA hB hC insertion_add insertion_mult insertion_sub insertion_pow)
  have h2 : "\<forall>x. insertion (nth_default 0 (list_update L var x)) ((B^2)*C-A^2) = (Bv^2)*Cv-Av^2"
    by(simp add: hA hB hC insertion_add insertion_mult insertion_sub insertion_pow)
  have h3 : "Av=0 \<Longrightarrow> Bv=0 \<Longrightarrow> (Av + Bv * sqrt Cv < 0) =
    (Av < 0 \<and> Bv\<^sup>2 * Cv < Av\<^sup>2 \<or> Bv \<le> 0 \<and> (Av < 0 \<or> Av\<^sup>2 < Bv\<^sup>2 * Cv))"
    by simp
  have h4 : "Av<0 \<Longrightarrow> Bv\<le>0 \<Longrightarrow> (Av + Bv * sqrt Cv < 0) =
    (Av < 0 \<and> Bv\<^sup>2 * Cv < Av\<^sup>2 \<or> Bv \<le> 0 \<and> (Av < 0 \<or> Av\<^sup>2 < Bv\<^sup>2 * Cv))"
    by (metis add.right_neutral add_mono_thms_linordered_field(5) detGreat0 less_eq_real_def mult_less_0_iff mult_zero_class.mult_zero_left mult_zero_class.mult_zero_right real_sqrt_eq_zero_cancel_iff real_sqrt_gt_0_iff)
  have h5a : "Av\<ge>0 \<Longrightarrow> Bv\<le>0 \<Longrightarrow> (Av < -Bv * sqrt Cv) \<Longrightarrow> (Av\<^sup>2 < Bv\<^sup>2 * Cv)"
  proof -
    assume a1: "0 \<le> Av"
    assume a2: "Av < - Bv * sqrt Cv"
    assume "Bv \<le> 0"
    then have "Av < sqrt (Cv * (Bv * Bv))"
      using a2 by (simp add: mult.commute real_sqrt_mult)
    then show ?thesis
      using a1 by (metis (no_types) mult.commute power2_eq_square real_sqrt_less_iff real_sqrt_mult real_sqrt_pow2_iff)
  qed
  have h5b : "Av\<ge>0 \<Longrightarrow> Bv\<le>0 \<Longrightarrow> (Av\<^sup>2 < Bv\<^sup>2 * Cv) \<Longrightarrow> (Av < -Bv * sqrt Cv)"
    using real_less_rsqrt real_sqrt_mult by fastforce
  have h5 : "Av\<ge>0 \<Longrightarrow> Bv\<le>0 \<Longrightarrow> (Av + Bv * sqrt Cv < 0) =
    (Av < 0 \<and> Bv\<^sup>2 * Cv < Av\<^sup>2 \<or> Bv \<le> 0 \<and> (Av < 0 \<or> Av\<^sup>2 < Bv\<^sup>2 * Cv))"
    using h5a h5b by linarith
  have h6 : "Av\<ge>0 \<Longrightarrow> Bv>0 \<Longrightarrow> (Av + Bv * sqrt Cv < 0) =
    (Av < 0 \<and> Bv\<^sup>2 * Cv < Av\<^sup>2 \<or> Bv \<le> 0 \<and> (Av < 0 \<or> Av\<^sup>2 < Bv\<^sup>2 * Cv))"
    by (smt detGreat0 mult_nonneg_nonneg real_sqrt_ge_zero)
  have h7a : "Av<0 \<Longrightarrow> Bv>0 \<Longrightarrow> (Av < -Bv * sqrt Cv) \<Longrightarrow> (Bv\<^sup>2 * Cv < Av\<^sup>2)"
    by (smt mult_minus_left real_sqrt_abs real_sqrt_le_mono real_sqrt_mult)
  have h7b : "Av<0 \<Longrightarrow> Bv>0 \<Longrightarrow> (Bv\<^sup>2 * Cv < Av\<^sup>2) \<Longrightarrow> (Av < -Bv * sqrt Cv)"
    by (metis abs_of_nonneg abs_real_def add.commute less_eq_real_def mult.assoc mult_minus_left power2_eq_square real_add_less_0_iff real_sqrt_less_iff real_sqrt_mult real_sqrt_mult_self)
  have h7 : "Av<0 \<Longrightarrow> Bv>0 \<Longrightarrow> (Av + Bv * sqrt Cv < 0) =
    (Av < 0 \<and> Bv\<^sup>2 * Cv < Av\<^sup>2 \<or> Bv \<le> 0 \<and> (Av < 0 \<or> Av\<^sup>2 < Bv\<^sup>2 * Cv))"
    using h7a h7b by linarith
  show ?thesis
    apply(simp add: hA hB h1 h2 insertion_add insertion_mult insertion_var lLength)
    using h3 h4 h5 h6 h7 by smt 
qed

lemma quadratic_sub_less :
  assumes lLength : "length L > var"
  assumes nonzero : "Dv \<noteq> 0"
  assumes detGreater0 : "Cv \<ge> 0"
  assumes freeC : "var \<notin> vars c"
  assumes ha : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (a::real mpoly) = (Av :: real)"
  assumes hb : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (b::real mpoly) = (Bv :: real)"
  assumes hc : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (c::real mpoly) = (Cv :: real)"
  assumes hd : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (d::real mpoly) = (Dv :: real)"
  shows "aEval (Less p) (list_update L var ((Av+Bv*sqrt(Cv))/Dv)) = eval (quadratic_sub var a b c d (Less p)) (list_update L var (sqrt Cv))"
proof -
  define p1 where "(p1::real mpoly) = quadratic_part_1 var a b d (Less p)"
  define p2 where "(p2::real mpoly) = quadratic_part_2 var c p1"
  define A where "A = isolate_variable_sparse p2 var 0"
  define B where "B = isolate_variable_sparse p2 var 1"

  have h3b : "MPoly_Type.degree p2 var \<le> 1"
    using freeC quad_part_2_deg p2_def by blast
  then have h3c : "MPoly_Type.degree p2 var = 0 \<or> MPoly_Type.degree p2 var = 1"
    by auto
  have h3d : "MPoly_Type.degree p2 var = 0 \<Longrightarrow> B = 0"
    by(simp add: B_def isovar_greater_degree)
  then have h3f : "MPoly_Type.degree p2 var = 0 \<Longrightarrow> p2 = A + B * Var var"
    by(simp add: h3d A_def degree0isovarspar)
  have h3g1 : "MPoly_Type.degree p2 var = 1 \<Longrightarrow> p2 = (\<Sum>i\<le>1. isolate_variable_sparse p2 var i * Var var ^ i)"
    using sum_over_zero by metis 
  have h3g2a : "\<forall>f. (\<Sum>i::nat\<le>1. f i) = f 0 + f 1" by simp
  have h3g2 : "(\<Sum>i::nat\<le>1. isolate_variable_sparse p2 var i * Var var ^ i) = 
                isolate_variable_sparse p2 var 0 * Var var ^ 0 + isolate_variable_sparse p2 var 1 * Var var ^ 1"
    using h3g2a by blast 
  have h3g : "MPoly_Type.degree p2 var = 1 \<Longrightarrow> p2 = A + B * Var var"
    apply(simp add: sum_over_zero A_def B_def)
    using h3g1 h3g2
    by (metis (no_types, lifting) One_nat_def mult_cancel_left2 power_0 power_one_right)
  have h3h : "p2 = A + B * Var var"
    using h3c h3f h3g by auto

  have h4a : "\<exists>x::real. \<forall>y::real. insertion (nth_default 0(list_update L var y)) A = x"
    using not_contains_insertion not_in_isovarspar A_def by blast
  have h4b : "\<exists>x::real. \<forall>y::real. insertion (nth_default 0(list_update L var y)) B = x"
    using not_contains_insertion not_in_isovarspar B_def by blast

  have h1 : "aEval (Less p) (list_update L var ((Av+Bv*sqrt(Cv))/Dv)) = aEval (Less (quadratic_part_1 var a b d (Less p))) (list_update L var (sqrt Cv))"
    using quad_part_1_less assms by blast
  also have "... = aEval (Less p1) (list_update L var (sqrt Cv))"
    using p1_def by auto
  also have "... = aEval (Less (quadratic_part_2 var c p1)) (list_update L var (sqrt Cv))"
    using quad_part_2_less assms by blast
  also have "... = aEval (Less p2) (list_update L var (sqrt Cv))"
    using p2_def by auto
  also have "... = aEval (Less (A + B * Var var)) (list_update L var (sqrt Cv))"
    using h3h by auto
  also have "... = eval
     (Or (And (fm.Atom (Less A)) (fm.Atom (Less (B\<^sup>2 * c - A\<^sup>2))))
       (And (fm.Atom (Leq B)) (Or (fm.Atom (Less A)) (fm.Atom (Less (A\<^sup>2 - B\<^sup>2 * c))))))
     (list_update L var (sqrt Cv))"
    using quadratic_sub_less_helper hc detGreater0 h4a h4b lLength by blast
  also have  "... = eval (quadratic_sub var a b c d (Less p)) (list_update L var (sqrt Cv))"
    using p2_def A_def B_def p1_def quadratic_sub.simps(2) by metis
  finally show ?thesis by blast
qed

(*------------------------------------------------------------------------------------------------*) 
lemma quadratic_sub_leq_helper :
  assumes lLength : "length L > var"
  assumes detGreat0 : "Cv\<ge>0"
  assumes hC : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (C::real mpoly) = (Cv::real)"
  assumes hA : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (A::real mpoly) = (Av::real)"
  assumes hB : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (B::real mpoly) = (Bv::real)"
  shows "aEval (Leq (A + B * Var var)) (list_update L var (sqrt Cv)) = 
  eval (Or(And(Atom(Leq(A)))(Atom (Leq(B^2*C-A^2))))(And (Atom(Leq B)) (Atom(Leq (A^2-B^2*C))))) (list_update L var (sqrt Cv))"
proof-
  have h1 : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (A^2-(B^2)*C) = Av^2-(Bv^2)*Cv"
    by(simp add: hA hB hC insertion_add insertion_mult insertion_sub insertion_pow)
  have h2 : "\<forall>x. insertion (nth_default 0 (list_update L var x)) ((B^2)*C-A^2) = (Bv^2)*Cv-Av^2"
    by(simp add: hA hB hC insertion_add insertion_mult insertion_sub insertion_pow)
  have h3 : "Av=0 \<Longrightarrow> Bv=0 \<Longrightarrow> (Av + Bv * sqrt Cv \<le> 0) = (Av \<le> 0 \<and> Bv\<^sup>2 * Cv \<le> Av\<^sup>2 \<or> Bv \<le> 0 \<and> Av\<^sup>2 \<le> Bv\<^sup>2 * Cv)"
    by simp
  have h4 : "Av<0 \<Longrightarrow> Bv\<le>0 \<Longrightarrow> (Av + Bv * sqrt Cv \<le> 0) = (Av \<le> 0 \<and> Bv\<^sup>2 * Cv \<le> Av\<^sup>2 \<or> Bv \<le> 0 \<and> Av\<^sup>2 \<le> Bv\<^sup>2 * Cv)"
    by (smt detGreat0 real_sqrt_ge_zero zero_less_mult_iff)
  have h5 : "Av=0 \<Longrightarrow> Bv\<le>0 \<Longrightarrow> (Av + Bv * sqrt Cv \<le> 0) = (Av \<le> 0 \<and> Bv\<^sup>2 * Cv \<le> Av\<^sup>2 \<or> Bv \<le> 0 \<and> Av\<^sup>2 \<le> Bv\<^sup>2 * Cv)"
    by (smt detGreat0 real_sqrt_ge_zero zero_less_mult_iff)
  have h6 : "Av\<ge>0 \<Longrightarrow> Bv>0 \<Longrightarrow> (Av + Bv * sqrt Cv \<le> 0) = (Av \<le> 0 \<and> Bv\<^sup>2 * Cv \<le> Av\<^sup>2 \<or> Bv \<le> 0 \<and> Av\<^sup>2 \<le> Bv\<^sup>2 * Cv)"
    by (smt detGreat0 mult_nonneg_nonneg mult_pos_pos real_sqrt_gt_0_iff real_sqrt_zero zero_le_power2 zero_less_mult_pos zero_less_power2)
  have h7a : "Av<0 \<Longrightarrow> Bv>0 \<Longrightarrow> (Av + Bv * sqrt Cv \<le> 0) \<Longrightarrow> Bv\<^sup>2 * Cv \<le> Av\<^sup>2"
    by (smt real_sqrt_abs real_sqrt_less_mono real_sqrt_mult)
  have h7b : "Av<0 \<Longrightarrow> Bv>0 \<Longrightarrow>  Bv\<^sup>2 * Cv \<le> Av\<^sup>2 \<Longrightarrow> (Av + Bv * sqrt Cv \<le> 0) "
    by (smt real_sqrt_abs real_sqrt_less_mono real_sqrt_mult)
  have h7 : "Av<0 \<Longrightarrow> Bv>0 \<Longrightarrow> (Av + Bv * sqrt Cv \<le> 0) = (Av \<le> 0 \<and> Bv\<^sup>2 * Cv \<le> Av\<^sup>2 \<or> Bv \<le> 0 \<and> Av\<^sup>2 \<le> Bv\<^sup>2 * Cv)"
    using h7a h7b by linarith
  have h8c : "(-Bv * sqrt Cv)^2 = Bv\<^sup>2 * Cv"
    by (simp add: detGreat0 power_mult_distrib)
  have h8a : "Av>0 \<Longrightarrow> Bv\<le>0  \<Longrightarrow> (Av \<le> -Bv * sqrt Cv) \<Longrightarrow>  Av\<^sup>2 \<le> Bv\<^sup>2 * Cv"
    using detGreat0 h8c power_both_sides by smt 
  have h8b : "Av>0 \<Longrightarrow> Bv\<le>0  \<Longrightarrow>   Av\<^sup>2 \<le> Bv\<^sup>2 * Cv \<Longrightarrow> (Av + Bv * sqrt Cv \<le> 0) "
    using detGreat0 h8c power_both_sides
    by (smt mult_minus_left real_sqrt_ge_zero zero_less_mult_iff) 
  have h8 : "Av>0 \<Longrightarrow> Bv\<le>0 \<Longrightarrow> (Av + Bv * sqrt Cv \<le> 0) = (Av \<le> 0 \<and> Bv\<^sup>2 * Cv \<le> Av\<^sup>2 \<or> Bv \<le> 0 \<and> Av\<^sup>2 \<le> Bv\<^sup>2 * Cv)"
    using h8a h8b by linarith
  show ?thesis
    apply(simp add: hA hB h1 h2 insertion_add insertion_mult insertion_var lLength)
    using h3 h4 h5 h6 h7 h8 by smt
qed

lemma quadratic_sub_leq :
  assumes lLength : "length L > var"
  assumes nonzero : "Dv \<noteq> 0"
  assumes detGreater0 : "Cv \<ge> 0"
  assumes freeC : "var \<notin> vars c"
  assumes ha : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (a::real mpoly) = (Av :: real)"
  assumes hb : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (b::real mpoly) = (Bv :: real)"
  assumes hc : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (c::real mpoly) = (Cv :: real)"
  assumes hd : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (d::real mpoly) = (Dv :: real)"
  shows "aEval (Leq p) (list_update L var ((Av+Bv*sqrt(Cv))/Dv)) = eval (quadratic_sub var a b c d (Leq p)) (list_update L var (sqrt Cv))"
proof -
  define p1 where "(p1::real mpoly) = quadratic_part_1 var a b d (Leq p)"
  define p2 where "(p2::real mpoly) = quadratic_part_2 var c p1"
  define A where "A = isolate_variable_sparse p2 var 0"
  define B where "B = isolate_variable_sparse p2 var 1"

  have h3b : "MPoly_Type.degree p2 var \<le> 1"
    using freeC quad_part_2_deg p2_def lLength by metis
  then have h3c : "MPoly_Type.degree p2 var = 0 \<or> MPoly_Type.degree p2 var = 1"
    by auto
  have h3d : "MPoly_Type.degree p2 var = 0 \<Longrightarrow> B = 0"
    by(simp add: B_def isovar_greater_degree)
  then have h3f : "MPoly_Type.degree p2 var = 0 \<Longrightarrow> p2 = A + B * Var var"
    by(simp add: h3d A_def degree0isovarspar)
  have h3g1 : "MPoly_Type.degree p2 var = 1 \<Longrightarrow> p2 = (\<Sum>i\<le>1. isolate_variable_sparse p2 var i * Var var ^ i)"
    using sum_over_zero by metis 
  have h3g2a : "\<forall>f. (\<Sum>i::nat\<le>1. f i) = f 0 + f 1" by simp
  have h3g2 : "(\<Sum>i::nat\<le>1. isolate_variable_sparse p2 var i * Var var ^ i) = 
                isolate_variable_sparse p2 var 0 * Var var ^ 0 + isolate_variable_sparse p2 var 1 * Var var ^ 1"
    using h3g2a by blast 
  have h3g : "MPoly_Type.degree p2 var = 1 \<Longrightarrow> p2 = A + B * Var var"
    apply(simp add: sum_over_zero A_def B_def)
    using h3g1 h3g2
    by (metis (no_types, lifting) One_nat_def mult_cancel_left2 power_0 power_one_right)
  have h3h : "p2 = A + B * Var var"
    using h3c h3f h3g by auto

  have h4a : "\<exists>x::real. \<forall>y::real. insertion (nth_default 0 (list_update L var y)) A = x"
    using not_contains_insertion not_in_isovarspar A_def by blast
  have h4b : "\<exists>x::real. \<forall>y::real. insertion (nth_default 0 (list_update L var y)) B = x"
    using not_contains_insertion not_in_isovarspar B_def by blast

  have "aEval (Leq p) (list_update L var ((Av+Bv*sqrt(Cv))/Dv)) = aEval (Leq p1) (list_update L var (sqrt Cv))"
    using quad_part_1_leq nonzero ha hb hd p1_def lLength by metis
  also have "... = aEval (Leq p2) (list_update L var (sqrt Cv))"
    using p2_def quad_part_2_leq hc detGreater0 lLength by metis
  also have "... = aEval (Leq (A + B * Var var)) (list_update L var (sqrt Cv))"
    using h3h by auto
  also have h4 : "... = eval
     (Or
      (And
        (Atom(Leq(A)))
        (Atom (Leq(B^2*c-A^2))))
      (And
        (Atom(Leq B))
        (Atom(Leq (A^2-B^2*c)))))
     (list_update L var (sqrt Cv))"
    using quadratic_sub_leq_helper hc detGreater0 h4a h4b lLength by blast
  also have "... = eval (quadratic_sub var a b c d (Leq p)) (list_update L var (sqrt Cv))"
    using p1_def quadratic_sub.simps(3) p2_def A_def B_def by metis
  finally show ?thesis by blast
qed
  (*------------------------------------------------------------------------------------------------*)
lemma quadratic_sub_neq :
  assumes lLength : "length L > var"
  assumes nonzero : "Dv \<noteq> 0"
  assumes detGreater0 : "Cv \<ge> 0"
  assumes freeC : "var \<notin> vars c"
  assumes ha : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (a::real mpoly) = (Av :: real)"
  assumes hb : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (b::real mpoly) = (Bv :: real)"
  assumes hc : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (c::real mpoly) = (Cv :: real)"
  assumes hd : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (d::real mpoly) = (Dv :: real)"
  shows "aEval (Neq p) (list_update L var ((Av+Bv*sqrt(Cv))/Dv)) = eval (quadratic_sub var a b c d (Neq p)) (list_update L var (sqrt Cv))"
proof -
  define p1 where "(p1::real mpoly) = quadratic_part_1 var a b d (Neq p)"
  define p2 where "(p2::real mpoly) = quadratic_part_2 var c p1"
  define A where "A = isolate_variable_sparse p2 var 0"
  define B where "B = isolate_variable_sparse p2 var 1"

  have h3b : "MPoly_Type.degree p2 var \<le> 1"
    using freeC quad_part_2_deg p2_def lLength by metis
  then have h3c : "MPoly_Type.degree p2 var = 0 \<or> MPoly_Type.degree p2 var = 1"
    by auto
  have h3d : "MPoly_Type.degree p2 var = 0 \<Longrightarrow> B = 0"
    by(simp add: B_def isovar_greater_degree)
  then have h3f : "MPoly_Type.degree p2 var = 0 \<Longrightarrow> p2 = A + B * Var var"
    by(simp add: h3d A_def degree0isovarspar)
  have h3g1 : "MPoly_Type.degree p2 var = 1 \<Longrightarrow> p2 = (\<Sum>i\<le>1. isolate_variable_sparse p2 var i * Var var ^ i)"
    using sum_over_zero by metis 
  have h3g2a : "\<forall>f. (\<Sum>i::nat\<le>1. f i) = f 0 + f 1" by simp
  have h3g2 : "(\<Sum>i::nat\<le>1. isolate_variable_sparse p2 var i * Var var ^ i) = 
                isolate_variable_sparse p2 var 0 * Var var ^ 0 + isolate_variable_sparse p2 var 1 * Var var ^ 1"
    using h3g2a by blast 
  have h3g : "MPoly_Type.degree p2 var = 1 \<Longrightarrow> p2 = A + B * Var var"
    apply(simp add: sum_over_zero A_def B_def)
    using h3g1 h3g2
    by (metis (no_types, lifting) One_nat_def mult_cancel_left2 power_0 power_one_right)
  have h3h : "p2 = A + B * Var var"
    using h3c h3f h3g by auto

  have h4a : "\<exists>x::real. \<forall>y::real. insertion (nth_default 0 (list_update L var y)) A = x"
    using not_contains_insertion not_in_isovarspar A_def by blast
  have h4b : "\<exists>x::real. \<forall>y::real. insertion (nth_default 0 (list_update L var y)) B = x"
    using not_contains_insertion not_in_isovarspar B_def by blast
  have h4c : "aEval (Eq (A + B * Var var)) (list_update L var (sqrt Cv))
           = eval (And (Atom(Leq (A*B))) (Atom (Eq (A^2-B^2*c)))) (list_update L var (sqrt Cv))"
    using quad_equality_helper hc detGreater0 h4a h4b lLength by blast
  have h4d : "aEval (Neq (A + B * Var var)) (list_update L var (sqrt Cv))
           = (\<not> (eval (And (Atom(Leq (A*B))) (Atom (Eq (A^2-B^2*c)))) (list_update L var (sqrt Cv))))"
    using aEval.simps(1) aEval.simps(4) h4c by blast
  have h4e : "(\<not> (eval (And (Atom(Leq (A*B))) (Atom (Eq (A^2-B^2*c)))) (list_update L var (sqrt Cv))))
                = eval (Or (Atom(Less(-A*B))) (Atom (Neq(A^2-B^2*c)))) (list_update L var (sqrt Cv))"
    by (metis aNeg.simps(2) aNeg.simps(3) aNeg_aEval eval.simps(1) eval.simps(4) eval.simps(5) mult_minus_left)

  have "aEval (Neq p) (list_update L var ((Av+Bv*sqrt(Cv))/Dv)) = aEval (Neq p1) (list_update L var (sqrt Cv))"
    using quad_part_1_neq nonzero ha hb hd p1_def lLength by blast
  also have "... = aEval (Neq p2) (list_update L var (sqrt Cv))"
    using p2_def quad_part_2_neq hc detGreater0 lLength by metis
  also have "... = aEval (Neq (A + B * Var var)) (list_update L var (sqrt Cv))"
    using h3h by auto
  also have "... = eval (Or
      (Atom(Less(-A*B)))
      (Atom (Neq(A^2-B^2*c)))) (list_update L var (sqrt Cv))"
    using h4c h4d h4e by auto
  also have "... = eval (quadratic_sub var a b c d (Neq p)) (list_update L var (sqrt Cv))"
    using p2_def A_def B_def p1_def quadratic_sub.simps(4) quadratic_part_1.simps(1) quadratic_part_1.simps(4)
    by (metis (no_types, lifting))
  finally show ?thesis by blast
qed
  (*-----------------------------------------------------------------------------------------------*)
theorem free_in_quad :
  assumes freeA : "var\<notin> vars a"
  assumes freeB : "var\<notin> vars b"
  assumes freeC : "var\<notin> vars c"
  assumes freeD : "var\<notin> vars d"
  shows "freeIn var (quadratic_sub var a b c d A)"
proof(cases A)
  case (Less p)
  define p1 where "(p1::real mpoly) = quadratic_part_1 var a b d (Less p)"
  define p2 where "(p2::real mpoly) = quadratic_part_2 var c p1"
  define A where "A = isolate_variable_sparse p2 var 0"
  define B where "B = isolate_variable_sparse p2 var 1"
  have h1 : "freeIn var (quadratic_sub var a b c d (Less p)) = freeIn var (Or (And (fm.Atom (Less A)) (fm.Atom (Less (B\<^sup>2 * c - A\<^sup>2))))
       (And (fm.Atom (Leq B)) (Or (fm.Atom (Less A)) (fm.Atom (Less (A\<^sup>2 - B\<^sup>2 * c))))))"
    using p2_def A_def B_def p1_def quadratic_sub.simps(2) by metis
  have h2d : "var\<notin>vars(4::real mpoly)"
    by (metis freeB not_in_add not_in_pow numeral_Bit0 one_add_one power_0)
  have h2 : "freeIn var ((Or (And (fm.Atom (Less A)) (fm.Atom (Less (B\<^sup>2 * c - A\<^sup>2))))
       (And (fm.Atom (Leq B)) (Or (fm.Atom (Less A)) (fm.Atom (Less (A\<^sup>2 - B\<^sup>2 * c)))))))"
    using vars_mult not_in_isovarspar A_def B_def not_in_sub not_in_mult not_in_neg not_in_pow not_in_isovarspar h2d freeC
    by (simp)
  show ?thesis using h1 h2 Less by blast
next
  case (Eq p)
  define p1 where "(p1::real mpoly) = quadratic_part_1 var a b d (Eq p)"
  define p2 where "(p2::real mpoly) = quadratic_part_2 var c p1"
  define A where "A = isolate_variable_sparse p2 var 0"
  define B where "B = isolate_variable_sparse p2 var 1"
  have h1 : "freeIn var (quadratic_sub var a b c d (Eq p)) = freeIn var (And (Atom(Leq (A*B))) (Atom (Eq (A\<^sup>2 - B\<^sup>2 * c))))"
    using p2_def A_def B_def p1_def quadratic_sub.simps(1) by metis
  have h2d : "var\<notin>vars(4::real mpoly)"
    by (metis freeB not_in_add not_in_pow numeral_Bit0 one_add_one power_0)
  have h2 : "freeIn var (And (Atom(Leq (A*B))) (Atom (Eq (A\<^sup>2 - B\<^sup>2 * c))))"
    using vars_mult not_in_isovarspar A_def B_def not_in_sub not_in_mult not_in_neg not_in_pow not_in_isovarspar h2d freeC
    by (simp)
  show ?thesis using h1 h2 Eq by blast
next
  case (Leq p)
  define p1 where "(p1::real mpoly) = quadratic_part_1 var a b d (Leq p)"
  define p2 where "(p2::real mpoly) = quadratic_part_2 var c p1"
  define A where "A = isolate_variable_sparse p2 var 0"
  define B where "B = isolate_variable_sparse p2 var 1"
  have h1 : "freeIn var (quadratic_sub var a b c d (Leq p)) = freeIn var (Or(And(Atom(Leq(A)))(Atom (Leq(B^2*c-A^2))))(And(Atom(Leq B))(Atom(Leq (A^2-B^2*c)))))"
    using p2_def A_def B_def p1_def quadratic_sub.simps(3) by metis
  have h2d : "var\<notin>vars(4::real mpoly)"
    by (metis freeB not_in_add not_in_pow numeral_Bit0 one_add_one power_0)
  have h2 : "freeIn var (Or(And(Atom(Leq(A)))(Atom (Leq(B^2*c-A^2))))(And(Atom(Leq B))(Atom(Leq (A^2-B^2*c)))))"
    using vars_mult not_in_isovarspar A_def B_def not_in_sub not_in_mult not_in_neg not_in_pow not_in_isovarspar h2d freeC
    by (simp)
  show ?thesis using h1 h2 Leq by blast
next
  case (Neq p)
  define p1 where "(p1::real mpoly) = quadratic_part_1 var a b d (Neq p)"
  define p2 where "(p2::real mpoly) = quadratic_part_2 var c p1"
  define A where "A = isolate_variable_sparse p2 var 0"
  define B where "B = isolate_variable_sparse p2 var 1"
  have h1 : "freeIn var (quadratic_sub var a b c d (Neq p)) = freeIn var (Or (Atom(Less(-A*B))) (Atom (Neq(A^2-B^2*c))))"
    using p2_def A_def B_def p1_def quadratic_sub.simps(4) by metis
  have h2d : "var\<notin>vars(4::real mpoly)"
    by (metis freeB not_in_add not_in_pow numeral_Bit0 one_add_one power_0)
  have h2 : "freeIn var (Or (Atom(Less(-A*B))) (Atom (Neq(A^2-B^2*c))))"
    using vars_mult not_in_isovarspar A_def B_def not_in_sub not_in_mult not_in_neg not_in_pow not_in_isovarspar h2d freeC
    by (simp)
  show ?thesis using h1 h2 Neq by blast
qed

theorem quadratic_sub :
  assumes lLength : "length L > var"
  assumes nonzero : "Dv \<noteq> 0"
  assumes detGreater0 : "Cv \<ge> 0"
  assumes freeC : "var \<notin> vars c"
  assumes ha : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (a::real mpoly) = (Av :: real)"
  assumes hb : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (b::real mpoly) = (Bv :: real)"
  assumes hc : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (c::real mpoly) = (Cv :: real)"
  assumes hd : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (d::real mpoly) = (Dv :: real)"
  shows "aEval A (list_update L var ((Av+Bv*sqrt(Cv))/Dv)) = eval (quadratic_sub var a b c d A) (list_update L var (sqrt Cv))"
proof(cases A)
  case (Less x1)
  then show ?thesis using quadratic_sub_less assms by blast
next
  case (Eq x2)
  then show ?thesis using quadratic_sub_eq assms by blast
next
  case (Leq x3)
  then show ?thesis using quadratic_sub_leq assms by blast
next
  case (Neq x4)
  then show ?thesis using quadratic_sub_neq assms by blast
qed




lemma free_in_quad_fm_helper :
  assumes freeA : "var\<notin> vars a"
  assumes freeB : "var\<notin> vars b"
  assumes freeC : "var\<notin> vars c"
  assumes freeD : "var\<notin> vars d"
  shows "freeIn (var+z) (quadratic_sub_fm_helper var a b c d F z)"
proof(induction F arbitrary: z)
  case TrueF
  then show ?case by auto
next
  case FalseF
  then show ?case by auto
next
  case (Atom x)
  then show ?case using free_in_quad[OF not_in_lift[OF assms(1)] not_in_lift[OF assms(2)] not_in_lift[OF assms(3)] not_in_lift[OF assms(4)], of z] by auto
next
  case (And F1 F2)
  then show ?case by auto
next
  case (Or F1 F2)
  then show ?case by auto
next
  case (Neg F)
  then show ?case by auto
next
  case (ExQ F)
  show ?case using ExQ[of "z+1"] by simp
next
  case (AllQ F)
  show ?case using AllQ[of "z+1"] by simp
next
  case (ExN x1 F)
  then show ?case
    by (metis (no_types, lifting) add.assoc freeIn.simps(13) liftmap.simps(10) quadratic_sub_fm_helper.simps)
next
  case (AllN x1 F)
  then show ?case
    by (metis (no_types, lifting) freeIn.simps(12) group_cancel.add1 liftmap.simps(9) quadratic_sub_fm_helper.simps)
qed

theorem free_in_quad_fm :
  assumes freeA : "var\<notin> vars a"
  assumes freeB : "var\<notin> vars b"
  assumes freeC : "var\<notin> vars c"
  assumes freeD : "var\<notin> vars d"
  shows "freeIn var (quadratic_sub_fm var a b c d A)"
  using free_in_quad_fm_helper[OF assms, of 0] by auto



lemma quadratic_sub_fm_helper :
  assumes nonzero : "Dv \<noteq> 0"
  assumes detGreater0 : "Cv \<ge> 0"
  assumes freeC : "var \<notin> vars c"
  assumes lLength : "length L > var+z"
  assumes ha : "\<forall>x. insertion (nth_default 0 (list_update (drop z L) var x)) (a::real mpoly) = (Av :: real)"
  assumes hb : "\<forall>x. insertion (nth_default 0 (list_update (drop z L) var x)) (b::real mpoly) = (Bv :: real)"
  assumes hc : "\<forall>x. insertion (nth_default 0 (list_update (drop z L) var x)) (c::real mpoly) = (Cv :: real)"
  assumes hd : "\<forall>x. insertion (nth_default 0 (list_update (drop z L) var x)) (d::real mpoly) = (Dv :: real)"
  shows "eval F (list_update L (var+z) ((Av+Bv*sqrt(Cv))/Dv)) = eval (quadratic_sub_fm_helper var a b c d F z) (list_update L (var+z) (sqrt Cv))"
  using assms proof(induction F arbitrary: z L)
  case TrueF
  then show ?case by auto
next
  case FalseF
  then show ?case by auto
next
  case (Atom x)
  define L1 where "L1 = drop z L"
  define L2 where "L2 = take z L"
  have L_def : "L = L2 @ L1" using L1_def L2_def by auto
  have lengthl2 : "length L2 = z" using L2_def
    using Atom.prems(4) by auto
  have "eval (Atom(Eq (a-Const Av))) ([] @ L1) = eval (liftFm 0 z (Atom(Eq (a- Const Av)))) ([] @ L2 @ L1)"
    by (metis eval_liftFm_helper lengthl2 list.size(3))
  then have "(insertion (nth_default 0 (L2 @ L1)) (liftPoly 0 z (a - Const Av)) = 0)"
    apply(simp add: insertion_sub insertion_const)
    using Atom(5) unfolding L1_def
    by (metis list_update_id) 
  then have "insertion (nth_default 0 (L2 @ L1)) (liftPoly 0 z a) = Av"
    using lift_minus by blast
  then have a1 : "\<forall>x. insertion (nth_default 0 (L[var + z := x])) (liftPoly 0 z a) = Av"
    unfolding L_def 
    by (metis (no_types, lifting) Atom.prems(5) L1_def add.right_neutral add_diff_cancel_right' append_eq_append_conv append_eq_append_conv2 length_append lengthl2 lift_insertion list.size(3) list_update_append not_add_less2) 
  have "eval (Atom(Eq (b-Const Bv))) ([] @ L1) = eval (liftFm 0 z (Atom(Eq (b- Const Bv)))) ([] @ L2 @ L1)"
    by (metis eval_liftFm_helper lengthl2 list.size(3))
  then have "(insertion (nth_default 0 (L2 @ L1)) (liftPoly 0 z (b - Const Bv)) = 0)"
    apply(simp add: insertion_sub insertion_const)
    using Atom(6) unfolding L1_def
    by (metis list_update_id) 
  then have "insertion (nth_default 0 (L2 @ L1)) (liftPoly 0 z b) = Bv"
    using lift_minus by blast
  then have a2 : "\<forall>x. insertion (nth_default 0 (L[var + z := x])) (liftPoly 0 z b) = Bv"
    unfolding L_def using Atom(6) L1_def
    by (metis L_def add_diff_cancel_right' append.simps(1) lengthl2 lift_insertion list.size(3) list_update_append not_add_less2)    
  have "eval (Atom(Eq (c-Const Cv))) ([] @ L1) = eval (liftFm 0 z (Atom(Eq (c- Const Cv)))) ([] @ L2 @ L1)"
    by (metis eval_liftFm_helper lengthl2 list.size(3))
  then have "(insertion (nth_default 0 (L2 @ L1)) (liftPoly 0 z (c - Const Cv)) = 0)"
    apply(simp add: insertion_sub insertion_const)
    using Atom(7) unfolding L1_def
    by (metis list_update_id) 
  then have "insertion (nth_default 0 (L2 @ L1)) (liftPoly 0 z c) = Cv"
    using lift_minus by blast
  then have a3 : "\<forall>x. insertion (nth_default 0 (L[var + z := x])) (liftPoly 0 z c) = Cv"
    unfolding L_def
  proof -
    obtain nn :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> real mpoly \<Rightarrow> nat" where
      "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> vars x2 \<and> x1 v3 \<noteq> x0 v3) = (nn x0 x1 x2 \<in> vars x2 \<and> x1 (nn x0 x1 x2) \<noteq> x0 (nn x0 x1 x2))"
      by moura
    then have f1: "\<forall>m f fa. nn fa f m \<in> vars m \<and> f (nn fa f m) \<noteq> fa (nn fa f m) \<or> insertion f m = insertion fa m"
      by (meson insertion_irrelevant_vars)
    obtain rr :: real where
      "(\<exists>v0. insertion (nth_default 0 ((L2 @ L1)[var + z := v0])) (liftPoly 0 z c) \<noteq> Cv) = (insertion (nth_default 0 ((L2 @ L1)[var + z := rr])) (liftPoly 0 z c) \<noteq> Cv)"
      by blast
    moreover
    { assume "var + z \<noteq> nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c)"
      moreover
      { assume "(nth_default 0 (L2 @ L1) (nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c)) = nth_default 0 ((L2 @ L1)[var + z := rr]) (nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c))) \<noteq> ((L2 @ L1) ! nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c) = (L2 @ L1)[var + z := rr] ! nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c))"
        then have "nth_default 0 ((L2 @ L1)[var + z := rr]) (nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c)) \<noteq> (L2 @ L1)[var + z := rr] ! nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c) \<or> nth_default 0 (L2 @ L1) (nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c)) \<noteq> (L2 @ L1) ! nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c)"
          by linarith
        then have "nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c) \<notin> vars (liftPoly 0 z c) \<or> nth_default 0 (L2 @ L1) (nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c)) = nth_default 0 ((L2 @ L1)[var + z := rr]) (nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c))"
          by (metis (no_types) append_Nil2 length_list_update nth_default_append) }
      ultimately have "nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c) \<notin> vars (liftPoly 0 z c) \<or> nth_default 0 (L2 @ L1) (nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c)) = nth_default 0 ((L2 @ L1)[var + z := rr]) (nn (nth_default 0 ((L2 @ L1)[var + z := rr])) (nth_default 0 (L2 @ L1)) (liftPoly 0 z c))"
        by force }
    ultimately show "\<forall>r. insertion (nth_default 0 ((L2 @ L1)[var + z := r])) (liftPoly 0 z c) = Cv"
      using f1 by (metis (full_types) Atom.prems(3) \<open>insertion (nth_default 0 (L2 @ L1)) (liftPoly 0 z c) = Cv\<close> not_in_lift)
  qed
  have "eval (Atom(Eq (d-Const Dv))) ([] @ L1) = eval (liftFm 0 z (Atom(Eq (d- Const Dv)))) ([] @ L2 @ L1)"
    by (metis eval_liftFm_helper lengthl2 list.size(3))
  then have "(insertion (nth_default 0 (L2 @ L1)) (liftPoly 0 z (d - Const Dv)) = 0)"
    apply(simp add: insertion_sub insertion_const)
    using Atom(8) unfolding L1_def
    by (metis list_update_id) 
  then have "insertion (nth_default 0 (L2 @ L1)) (liftPoly 0 z d) = Dv"
    using lift_minus by blast
  then have a4 : "\<forall>x. insertion (nth_default 0 (L[var + z := x])) (liftPoly 0 z d) = Dv"
    unfolding L_def
    by (metis Atom(8) L1_def L_def add_diff_cancel_right' append.simps(1) lengthl2 lift_insertion list.size(3) list_update_append not_add_less2)
  then show ?case  apply(simp)
    using quadratic_sub[OF Atom(4) Atom(1) Atom(2) not_in_lift[OF Atom(3)], of "(liftPoly 0 z a)" Av "(liftPoly 0 z b)" Bv "(liftPoly 0 z d)" x
        , OF a1 a2 a3 a4] .
next
  case (And F1 F2)
  then show ?case by auto
next
  case (Or F1 F2)
  then show ?case by auto
next
  case (Neg F)
  then show ?case by auto
next
  case (ExQ F)
  have lengthG : "var + (z + 1) < length (x#L)" for x using ExQ(5) by auto
  have forall : "\<forall>x. insertion (nth_default 0 ((drop z L)[var := x])) a = Av \<Longrightarrow> 
      \<forall>x. insertion (nth_default 0 ((drop (z + 1) (x1 # L))[var := x])) a = Av" for x1 a Av
    by auto
  have l : "x # L[var + z := v] = ((x#L)[var+(z+1):=v])" for x v
    by auto
  have "eval (ExQ F) (L[var + z := (Av + Bv * sqrt Cv) / Dv]) =
    (\<exists>x. eval F (x # L[var + z := (Av + Bv * sqrt Cv) / Dv]))"
    by(simp)
  also have "... = (\<exists>x. eval
          (liftmap
            (\<lambda>x. quadratic_sub (var + x) (liftPoly 0 x a) (liftPoly 0 x b) (liftPoly 0 x c) (liftPoly 0 x d))
            F (z + 1))
          (x # L[var + z := sqrt Cv]))"
    apply(rule ex_cong1)
    unfolding l
    using ExQ(1)[OF ExQ(2) ExQ(3) ExQ(4) lengthG forall[OF ExQ(6)] forall[OF ExQ(7)] forall[OF ExQ(8)] forall[OF ExQ(9)]]
    unfolding quadratic_sub_fm_helper.simps liftmap.simps
    by simp
  also have "... = eval (quadratic_sub_fm_helper var a b c d (ExQ F) z) (L[var + z := sqrt Cv])"
    unfolding quadratic_sub_fm_helper.simps liftmap.simps eval.simps by auto
  finally show ?case by simp
next
  case (AllQ F)
  have lengthG : "var + (z + 1) < length (x#L)" for x using AllQ(5) by auto
  have forall : "\<forall>x. insertion (nth_default 0 ((drop z L)[var := x])) a = Av \<Longrightarrow> 
      \<forall>x. insertion (nth_default 0 ((drop (z + 1) (x1 # L))[var := x])) a = Av" for x1 a Av
    by auto
  have l : "x # L[var + z := v] = ((x#L)[var+(z+1):=v])" for x v
    by auto
  have "eval (AllQ F) (L[var + z := (Av + Bv * sqrt Cv) / Dv]) =
    (\<forall>x. eval F (x # L[var + z := (Av + Bv * sqrt Cv) / Dv]))"
    by(simp)
  also have "... = (\<forall>x. eval
          (liftmap
            (\<lambda>x. quadratic_sub (var + x) (liftPoly 0 x a) (liftPoly 0 x b) (liftPoly 0 x c) (liftPoly 0 x d))
            F (z + 1))
          (x # L[var + z := sqrt Cv]))"
    apply(rule all_cong1)
    unfolding l
    using AllQ(1)[OF AllQ(2) AllQ(3) AllQ(4) lengthG forall[OF AllQ(6)] forall[OF AllQ(7)] forall[OF AllQ(8)] forall[OF AllQ(9)]]
    unfolding quadratic_sub_fm_helper.simps liftmap.simps
    by simp
  also have "... = eval (quadratic_sub_fm_helper var a b c d (AllQ F) z) (L[var + z := sqrt Cv])"
    unfolding quadratic_sub_fm_helper.simps liftmap.simps eval.simps by auto
  finally show ?case by simp
next
  case (ExN x1 F)
  have list : "\<And>l. length l=x1 \<Longrightarrow> ((drop (z + x1) l @ drop (z + x1 - length l) L)) = ((drop z L))"
    by auto
  have map : "\<And> z L. eval (liftmap (\<lambda>x A. (quadratic_sub (var + x) (liftPoly 0 x a) (liftPoly 0 x b) (liftPoly 0 x c) (liftPoly 0 x d) A)) F (z + x1))
      L = eval (liftmap (\<lambda>x A. (quadratic_sub (var + x1 + x) (liftPoly 0 (x+x1) a) (liftPoly 0 (x+x1) b) (liftPoly 0 (x+x1) c) (liftPoly 0 (x+x1) d) A)) F z)
      L"
    apply(induction F) apply(simp_all add:add.commute add.left_commute)
    apply force
    apply force
    by (metis (mono_tags, lifting) ab_semigroup_add_class.add_ac(1))+
  show ?case apply simp apply(rule ex_cong1)
    subgoal for l
      using map[of z] list[of l] ExN(1)[OF ExN(2-4), of "z+x1" "l@L"] ExN(5-9) list_update_append
      apply auto
      by (simp add: list_update_append) +
    done
next
  case (AllN x1 F)
  have list : "\<And>l. length l=x1 \<Longrightarrow> ((drop (z + x1) l @ drop (z + x1 - length l) L)) = ((drop z L))"
    by auto
  have map : "\<And> z L. eval (liftmap (\<lambda>x A. (quadratic_sub (var + x) (liftPoly 0 x a) (liftPoly 0 x b) (liftPoly 0 x c) (liftPoly 0 x d) A)) F (z + x1))
      L = eval (liftmap (\<lambda>x A. (quadratic_sub (var + x1 + x) (liftPoly 0 (x+x1) a) (liftPoly 0 (x+x1) b) (liftPoly 0 (x+x1) c) (liftPoly 0 (x+x1) d) A)) F z)
      L"
    apply(induction F) apply(simp_all add:add.commute add.left_commute)
    apply force
    apply force
    by (metis (mono_tags, lifting) ab_semigroup_add_class.add_ac(1))+
  show ?case apply simp apply(rule all_cong1)
    subgoal for l
      using map[of z] list[of l] AllN(1)[OF AllN(2-4), of "z+x1" "l@L"] AllN(5-9)
      apply auto
      by (simp add: list_update_append) +
    done
qed

theorem quadratic_sub_fm :
  assumes lLength : "length L > var"
  assumes nonzero : "Dv \<noteq> 0"
  assumes detGreater0 : "Cv \<ge> 0"
  assumes freeC : "var \<notin> vars c"
  assumes ha : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (a::real mpoly) = (Av :: real)"
  assumes hb : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (b::real mpoly) = (Bv :: real)"
  assumes hc : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (c::real mpoly) = (Cv :: real)"
  assumes hd : "\<forall>x. insertion (nth_default 0 (list_update L var x)) (d::real mpoly) = (Dv :: real)"
  shows "eval F (list_update L var ((Av+Bv*sqrt(Cv))/Dv)) = eval (quadratic_sub_fm var a b c d F) (list_update L var (sqrt Cv))"
  unfolding quadratic_sub_fm.simps using quadratic_sub_fm_helper[OF assms(2) assms(3) assms(4), of 0 L a Av b Bv d F] assms(1) assms(5) assms(6) assms(7) assms(8)
  by (simp add: lLength)
end