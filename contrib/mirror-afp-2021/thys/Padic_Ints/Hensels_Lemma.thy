theory Hensels_Lemma
  imports Padic_Int_Polynomials
begin


text\<open>
  The following proof of Hensel's Lemma is directly adapted from Keith Conrad's proof which is
  given in an online note \cite{keithconrad}. The same note was used as the basis for a 
  formalization of Hensel's Lemma by Robert Lewis in the Lean proof assistant
  \cite{10.1145/3293880.3294089}.  \<close>
(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Auxiliary Lemmas for Hensel's Lemma\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma(in ring) minus_sum:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "\<ominus> (a \<oplus> b) = \<ominus> a \<oplus> \<ominus> b"
  by (simp add: assms(1) assms(2) local.minus_add)

context padic_integers
begin


lemma poly_diff_val:
  assumes "f \<in> carrier Zp_x"
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  shows "val_Zp (f\<bullet>a \<ominus> f\<bullet>b) \<ge> val_Zp (a \<ominus> b)"
proof-
  obtain c where c_def: "c \<in> carrier Zp \<and> (f\<bullet>a \<ominus> f\<bullet>b) = (a \<ominus> b) \<otimes> c"
    using assms 
    by (meson to_fun_diff_factor)
  have 1: "val_Zp c \<ge> 0"
    using c_def val_pos by blast 
  have 2: "val_Zp (f\<bullet>a \<ominus> f\<bullet>b) = val_Zp (a \<ominus> b) + (val_Zp c)"
    using c_def val_Zp_mult 
    by (simp add: assms(2) assms(3))        
  then show ?thesis 
    using "1" by auto 
qed

text\<open>Restricted p-adic division\<close>

definition divide where
"divide x y = (if x = \<zero> then \<zero> else 
              (\<p>[^](nat (ord_Zp x - ord_Zp y)) \<otimes> ac_Zp x \<otimes> (inv ac_Zp y)))"

lemma divide_closed:
  assumes "x \<in> carrier Zp"
  assumes "y \<in> carrier Zp"
  assumes "y \<noteq> \<zero>"
  shows "divide x y \<in> carrier Zp"
  unfolding divide_def
  apply(cases "x = \<zero>")
  apply auto[1]
  using assms ac_Zp_is_Unit 
  by (simp add: ac_Zp_in_Zp)
   
lemma divide_formula:
  assumes "x \<in> carrier Zp"
  assumes "y \<in> carrier Zp"
  assumes "y \<noteq> \<zero>"
  assumes "val_Zp x \<ge> val_Zp y"
  shows "y \<otimes> divide x y = x"
  apply(cases "x = \<zero>")
   apply (simp add: divide_def mult_zero_l)
proof- assume A: "x \<noteq> \<zero>"
  have 0: "y \<otimes> divide x y = \<p>[^] nat (ord_Zp y) \<otimes> ac_Zp y \<otimes> (\<p>[^](nat (ord_Zp x - ord_Zp y)) \<otimes> ac_Zp x \<otimes> (inv ac_Zp y))"
    using assms ac_Zp_factors_x[of x] ac_Zp_factors_x[of y] A divide_def 
    by auto
  hence  1: "y \<otimes> divide x y = \<p>[^] nat (ord_Zp  y) \<otimes> (\<p>[^](nat (ord_Zp  x - ord_Zp  y)) \<otimes>  ac_Zp x \<otimes> ac_Zp y \<otimes>  (inv ac_Zp y))"
    using mult_assoc mult_comm by auto
  have 2: "(nat (ord_Zp  y) + nat (ord_Zp  x - ord_Zp  y)) = nat (ord_Zp  x)"
    using assms ord_pos[of x] ord_pos[of y] A val_ord_Zp by auto
  have "y \<otimes> divide x y = \<p>[^] nat (ord_Zp  y) \<otimes> \<p>[^](nat (ord_Zp  x - ord_Zp  y)) \<otimes>  ac_Zp x"
    using 1 A assms 
    by (simp add: ac_Zp_in_Zp ac_Zp_is_Unit mult_assoc)
  thus "y \<otimes> divide x y = x"
    using "2" A ac_Zp_factors_x(1) assms(1) p_natpow_prod by auto
qed

lemma divide_nonzero:
  assumes "x \<in> nonzero Zp"
  assumes "y \<in> nonzero Zp"
  assumes "val_Zp x \<ge> val_Zp y"
  shows "divide x y \<in> nonzero Zp"
  by (metis assms(1) assms(2) assms(3) divide_closed divide_formula mult_zero_l nonzero_closed nonzero_memE(2) nonzero_memI)

lemma val_of_divide:
  assumes "x \<in> carrier Zp"
  assumes "y \<in> nonzero Zp"
  assumes "val_Zp x \<ge> val_Zp y"
  shows "val_Zp (divide x y) = val_Zp x - val_Zp y"
proof-
  have 0: "y \<otimes> divide x y = x"
    by (simp add: assms(1) assms(2) assms(3) divide_formula nonzero_closed nonzero_memE(2))
  hence "val_Zp y + val_Zp (divide x y) = val_Zp x"
    using assms(1) assms(2) divide_closed nonzero_closed not_nonzero_memI val_Zp_mult by fastforce
  thus ?thesis 
    by (smt Zp_def add.commute add.left_neutral add.right_neutral add_diff_assoc_eint assms(1) 
        assms(2) divide_nonzero eSuc_minus_eSuc iadd_Suc idiff_0_right mult_zero(1) mult_zero_l
        nonzero_closed ord_pos order_refl padic_integers.Zp_int_inc_closed padic_integers.mult_comm 
        padic_integers.ord_of_nonzero(2) padic_integers_axioms val_Zp_eq_frac_0 val_Zp_mult val_Zp_p)
qed

lemma val_of_divide':
  assumes "x \<in> carrier Zp"
  assumes "y \<in> carrier  Zp"
  assumes "y \<noteq> \<zero>"
  assumes "val_Zp x \<ge> val_Zp y"
  shows "val_Zp (divide x y) = val_Zp x - val_Zp y"
  using Zp_def assms(1) assms(2) assms(3) assms(4) padic_integers.not_nonzero_Zp 
    padic_integers.val_of_divide padic_integers_axioms by blast
end

lemma(in UP_cring) taylor_deg_1_eval''':
  assumes "f \<in> carrier P"
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "c = to_fun (shift (2::nat) (T\<^bsub>a\<^esub> f)) (\<ominus>b)"
  assumes "b \<otimes> (deriv f a) = (to_fun f a)"
  shows "to_fun f (a \<ominus> b) =  (c \<otimes> b[^](2::nat))"
proof-
  have 0: "to_fun f (a \<ominus> b) = (to_fun f a) \<ominus> (deriv f a \<otimes> b) \<oplus> (c \<otimes> b[^](2::nat))"
    using assms taylor_deg_1_eval'' 
    by blast
  have 1: "(to_fun f a) \<ominus> (deriv f a \<otimes> b) = \<zero>"
    using assms
  proof -
    have "\<forall>f a. f \<notin> carrier P \<or> a \<notin> carrier R \<or> to_fun f a \<in> carrier R"
      using to_fun_closed by presburger
    then show ?thesis
      using R.m_comm R.r_right_minus_eq assms(1) assms(2) assms(3) assms(5) 
      by (simp add: deriv_closed)
  qed     
  have 2: "to_fun f (a \<ominus> b) = \<zero> \<oplus> (c \<otimes> b[^](2::nat))"
    using 0 1 
    by simp
  then show ?thesis using assms
    by (simp add: taylor_closed to_fun_closed shift_closed)    
qed

lemma(in padic_integers) res_diff_zero_fact:
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "(a \<ominus> b) k = 0"
  shows "a k = b k" "a k \<ominus>\<^bsub>Zp_res_ring k\<^esub> b k = 0"
   apply(cases "k = 0")
  apply (metis assms(1) assms(2) p_res_ring_0 p_res_ring_0' p_res_ring_car p_residue_padic_int p_residue_range' zero_le)
   apply (metis R.add.inv_closed R.add.m_lcomm R.minus_eq R.r_neg R.r_zero Zp_residue_add_zero(2) assms(1) assms(2) assms(3))
    using assms(2) assms(3) residue_of_diff by auto

lemma(in padic_integers) res_diff_zero_fact':
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "a k = b k"
  shows "a k \<ominus>\<^bsub>Zp_res_ring k\<^esub> b k = 0"
  by (simp add: assms(3) residue_minus)

lemma(in padic_integers) res_diff_zero_fact'':
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "a k = b k"
  shows "(a \<ominus> b) k = 0"
  by (simp add: assms(2) assms(3) res_diff_zero_fact' residue_of_diff)

lemma(in padic_integers) is_Zp_cauchyI': 
assumes "s \<in> closed_seqs Zp"
assumes "\<forall>n::nat. \<exists> k::int.\<forall>m.  m \<ge>  k \<longrightarrow> val_Zp (s (Suc m) \<ominus> s m) \<ge> n"
shows "is_Zp_cauchy s"
proof(rule is_Zp_cauchyI)
  show A0: "s \<in> closed_seqs Zp" 
    by (simp add: assms(1))  
  show "\<And>n. \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 n = s n1 n"
  proof-
    fix n
    show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 n = s n1 n"
    proof(induction n)
      case 0
      then show ?case 
      proof-
        have "\<forall>n0 n1. 0 < n0 \<and> 0 < n1 \<longrightarrow> s n0 0 = s n1 0"
          apply auto 
        proof-
          fix n0 n1::nat
          assume A: "n0 > 0" "n1 > 0"
          have 0: "s n0 \<in> carrier Zp"
            using A0 
            by (simp add: closed_seqs_memE)                       
          have 1: "s n1 \<in> carrier Zp"
            using A0            
            by (simp add: closed_seqs_memE)                       
          show " s n0 (0::nat) = s n1 (0::nat)"
            using A0 Zp_def 0 1 residues_closed 
            by (metis p_res_ring_0')           
        qed
        then show ?thesis 
          by blast 
      qed
    next
      case (Suc n)
      fix n
      assume IH: "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 n = s n1 n"
      show " \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 (Suc n) = s n1 (Suc n)"
      proof-
        obtain N where N_def: "\<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 n = s n1 n"
          using IH 
          by blast  
        obtain k where k_def: "\<forall>m.  (Suc m) \<ge> k \<longrightarrow> val_Zp (s (Suc (Suc m)) \<ominus> s (Suc m)) \<ge> Suc (Suc n)"
          using assms  Suc_n_not_le_n 
          by (meson nat_le_iff)
        have "\<forall>n0 n1.  Suc (max N (max n k)) < n0 \<and>  Suc (max N (max n k))< n1 \<longrightarrow> s n0 (Suc n) = s n1 (Suc n)"
          apply auto
        proof-
          fix n0 n1
          assume A: "Suc (max N (max n k)) < n0" " Suc (max N (max n k)) < n1"
          show "s n0 (Suc n) = s n1 (Suc n) "
          proof-
            obtain K where K_def: "K = Suc (max N (max n k))"
              by simp
            have P0: "\<And>m. s ((Suc m)+ K) (Suc n) = s (Suc K) (Suc n)"
              apply auto  
            proof-
              fix m
              show "s (Suc (m + K)) (Suc n) = s (Suc K) (Suc n)"
              apply(induction m)
                 apply auto 
              proof-
                fix m
                assume A0: " s (Suc (m + K)) (Suc n) = s (Suc K) (Suc n)"
                show " s (Suc (Suc (m + K))) (Suc n) = s (Suc K) (Suc n)"
                proof-
                  have I: "k < m + K"
                    using K_def 
                    by linarith
                  have "val_Zp (s (Suc (Suc (m + K))) \<ominus> s (Suc (m + K))) \<ge>  Suc (Suc n)"
                  proof-
                    have "(Suc (m + K)) > k"
                      by (simp add: I less_Suc_eq)
                    then show ?thesis 
                      using k_def less_imp_le_nat 
                      by blast
                  qed
                  hence D: "val_Zp (s (Suc (Suc (m + K))) \<ominus> s (Suc (m + K))) > (Suc n)"
                    using Suc_ile_eq by fastforce
                  have "s (Suc (Suc (m + K))) (Suc n) =  s (Suc (m + K)) (Suc n)"
                  proof-
                    have "(s (Suc (Suc (m + K))) \<ominus> s (Suc (m + K)))  (Suc n) = 0"
                      using D assms(1) res_diff_zero_fact''[of "s (Suc (Suc (m + K)))" "s (Suc (m + K)) " "Suc n"]
                      val_Zp_dist_res_eq[of "s (Suc (Suc (m + K)))" "s (Suc (m + K)) "  "Suc n"] unfolding val_Zp_dist_def 
                      by (simp add: closed_seqs_memE)                                                                                  
                    hence 0: "(s (Suc (Suc (m + K)))  (Suc n) \<ominus>\<^bsub>Zp_res_ring (Suc n)\<^esub> (s (Suc (m + K)))  (Suc n)) = 0"
                      using res_diff_zero_fact(2)[of "s (Suc (Suc (m + K)))" "s (Suc (m + K))" "Suc n" ]
                            assms(1) 
                      by (simp add: closed_seqs_memE)                       
 
                    show ?thesis 
                    proof-
                      have 00: "cring (Zp_res_ring (Suc n))"
                        using R_cring by blast
                      have 01: " s (Suc (Suc (m + K))) (Suc n) \<in> carrier (Zp_res_ring (Suc n))"
                        using assms(1) closed_seqs_memE residues_closed by blast
                      have 02: "(\<ominus>\<^bsub>Zp_res_ring (Suc n)\<^esub> (s (Suc (m + K)) (Suc n))) \<in> carrier (Zp_res_ring (Suc n)) "
                        by (meson "00" assms(1) cring.cring_simprules(3) closed_seqs_memE residues_closed)
                      show ?thesis 
                        unfolding a_minus_def
                        using  00 01 02  
                              cring.sum_zero_eq_neg[of "Zp_res_ring (Suc n)" "s (Suc (Suc (m + K))) (Suc n)"
                                            "\<ominus>\<^bsub>Zp_res_ring (Suc n)\<^esub>s (Suc (m + K)) (Suc n)"]  
                        by (metis 0  a_minus_def assms(1) cring.cring_simprules(21) closed_seqs_memE 
                            p_res_ring_zero residues_closed)                        
                    qed
                  qed
                  then show ?thesis using A0 assms(1)
                    by simp   
                qed
              qed
            qed
            have "\<exists>m0. n0 = (Suc m0) + K"
            proof-
              have "n0 > K"
                by (simp add: A(1) K_def)
              then have "n0 = (Suc (n0 - K - 1)) + K"
                by auto
              then show ?thesis by blast 
            qed
            then obtain m0 where m0_def: "n0 = (Suc m0) + K"
              by blast 
            have "\<exists>m0. n1 = (Suc m0) + K"
            proof-
              have "n1 > K"
                by (simp add: A(2) K_def)
              then have "n1 = (Suc (n1 - K - 1)) + K"
                by auto
              then show ?thesis by blast 
            qed
            then obtain m1 where m1_def: "n1 = (Suc m1) + K"
              by blast
            have 0: "s n0 (Suc n) = s (Suc K) (Suc n)" 
              using m0_def P0[of "m0"] by auto  
            have 1: "s n1 (Suc n) = s (Suc K) (Suc n)" 
              using m1_def P0[of "m1"] by auto  
            show ?thesis using 0 1 
              by auto
          qed
        qed
        then show ?thesis 
          by blast
      qed
    qed
  qed
qed

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>The Proof of Hensel's Lemma\<close>
(**************************************************************************************************)
(**************************************************************************************************)

subsection\<open>Building a Locale for the Proof of Hensel's Lemma\<close>

locale hensel = padic_integers+ 
  fixes f::padic_int_poly
  fixes a::padic_int
  assumes f_closed[simp]: "f \<in> carrier Zp_x"
  assumes a_closed[simp]: "a \<in> carrier Zp"
  assumes fa_nonzero[simp]: "f\<bullet>a \<noteq>\<zero>"
  assumes hensel_hypothesis[simp]: "(val_Zp (f\<bullet>a) > 2* val_Zp ((pderiv f)\<bullet>a))"

sublocale hensel < cring Zp
  by (simp add: R.is_cring)

context hensel
begin

abbreviation f' where
"f' \<equiv> pderiv f"

lemma f'_closed:
"f' \<in> carrier Zp_x"
  using f_closed pderiv_closed by blast 
  
lemma f'_vals_closed:
  assumes "a \<in> carrier Zp"
  shows "f'\<bullet>a \<in> carrier Zp"
  by (simp add: UP_cring.to_fun_closed Zp_x_is_UP_cring f'_closed)
  
lemma fa_closed:
"(f\<bullet>a) \<in> carrier Zp"
  by (simp add: UP_cring.to_fun_closed Zp_x_is_UP_cring)

lemma f'a_closed:
"(f'\<bullet>a) \<in> carrier Zp"
proof-
  have "f' \<in> carrier Zp_x"
    by (simp add: f'_closed)  
  then show ?thesis 
    by (simp add: f'_vals_closed)
qed

lemma fa_nonzero':
"(f\<bullet>a) \<in> nonzero Zp"
  using fa_closed fa_nonzero not_nonzero_Zp by blast

lemma f'a_nonzero[simp]:
"(f'\<bullet>a) \<noteq> \<zero>"
proof(rule ccontr)
  assume "\<not> (f'\<bullet>a) \<noteq> \<zero>"
  then have "(f'\<bullet>a) = \<zero>"
    by blast 
  then have "\<infinity> < val_Zp (f\<bullet>a)" using hensel_hypothesis 
    by (simp add: val_Zp_def)
  thus False 
    using eint_ord_simps(6) by blast
qed      

lemma f'a_nonzero':
"(f'\<bullet>a) \<in> nonzero Zp"
  using f'a_closed f'a_nonzero not_nonzero_Zp by blast

lemma f'a_not_infinite[simp]: 
"val_Zp (f'\<bullet>a) \<noteq> \<infinity>"
  by (metis eint_ord_code(3) hensel_hypothesis linorder_not_less times_eint_simps(4))

lemma f'a_nonneg_val[simp]: 
"val_Zp ((f'\<bullet>a)) \<ge> 0"
  using f'a_closed val_pos by blast

lemma hensel_hypothesis_weakened:
"val_Zp (f\<bullet>a) > val_Zp (f'\<bullet>a)"
proof-
  have 0: "0 \<le> val_Zp (f'\<bullet>a) \<and> val_Zp (f'\<bullet>a) \<noteq> \<infinity>"
    using f'a_closed val_ord_Zp val_pos by force
  have 1: "1 < eint 2 "
    by (simp add: one_eint_def)
  thus ?thesis   using 0 eint_mult_mono'[of "val_Zp (f'\<bullet>a)" 1 2] hensel_hypothesis 
    by (metis linorder_not_less mult_one_left order_trans)
qed

subsection\<open>Constructing the Newton Sequence\<close>

definition newton_step :: "padic_int \<Rightarrow> padic_int" where
"newton_step x = x \<ominus> (divide (f\<bullet>x) (f'\<bullet>x))"

lemma newton_step_closed:
  "newton_step a \<in> carrier Zp"
  using  divide_closed unfolding newton_step_def 
  using f'a_closed f'a_nonzero fa_closed local.a_closed by blast
  
fun newton_seq :: "padic_int_seq" ("ns") where
"newton_seq 0 = a"|
"newton_seq (Suc n) = newton_step (newton_seq n)"

subsection\<open>Key Properties of the Newton Sequence\<close>

lemma hensel_factor_id:
"(divide (f\<bullet>a) (f'\<bullet>a)) \<otimes> ((f'\<bullet>a)) = (f\<bullet>a)"
  using hensel_hypothesis hensel_axioms divide_formula f'a_closed 
        fa_closed hensel_hypothesis_weakened mult_comm 
  by auto

definition hensel_factor ("t") where
"hensel_factor = val_Zp (f\<bullet>a) - 2*(val_Zp (f'\<bullet>a))"

lemma t_pos[simp]:
"t > 0"
  using hensel_factor_def hensel_hypothesis 
  by (simp add: eint_minus_le)

lemma t_neq_infty[simp]:
"t \<noteq> \<infinity>"
  by (simp add: hensel_factor_def val_Zp_def)

lemma t_times_pow_pos[simp]:
"(2^(n::nat))*t > 0"
  apply(cases "n = 0")
  using one_eint_def apply auto[1]
    using eint_mult_mono'[of t 1 "2^n"] t_pos
  by (smt eint_ord_simps(2) linorder_not_less mult_one_left neq0_conv one_eint_def order_less_le order_trans self_le_power t_neq_infty)

lemma newton_seq_props_induct:
shows "\<And>k. k \<le> n \<Longrightarrow> (ns k) \<in> carrier Zp
              \<and> val_Zp (f'\<bullet>(ns k)) = val_Zp ((f'\<bullet>a))
              \<and> val_Zp (f\<bullet>(ns k)) \<ge> 2*(val_Zp (f'\<bullet>a)) + (2^k)*t"
proof(induction n)
  case 0
  then have kz: "k = 0"
    by simp
  have B0: "( ns k) \<in> carrier Zp"
    using kz 
    by simp
  have B1: "val_Zp (f' \<bullet> ns k) = (val_Zp (f'\<bullet>a))"
    using kz newton_seq.simps(1) 
    by presburger 
  have B2: "val_Zp (f \<bullet> (ns k)) \<ge> (2 * (val_Zp (f'\<bullet>a))) + 2 ^ k * t"
  proof-
    have B20: "(2 * (val_Zp (f'\<bullet>a))) + 2 ^ k * t = (2 * (val_Zp (f'\<bullet>a))) +  t"
    proof-
      have "(2 * (val_Zp (f'\<bullet>a))) + 2 ^ k * t = (2 * (val_Zp (f'\<bullet>a))) +  t"
        using kz  one_eint_def by auto        
      then show ?thesis 
        by blast
    qed
    then have "(2 * (val_Zp (f'\<bullet>a))) + 2 ^ k * t = (2 * (val_Zp (f'\<bullet>a))) + val_Zp (f\<bullet>a) - 2*(val_Zp (f'\<bullet>a))"
      unfolding hensel_factor_def 
      by (simp add: val_Zp_def)
    then have "(2 * (val_Zp (f'\<bullet>a))) + 2 ^ k * t =  val_Zp (f\<bullet>a)"
      by (metis add_diff_cancel_eint eint_ord_simps(6) hensel_hypothesis)     
    thus ?thesis       by (simp add: kz)      
  qed
  thus ?case 
    using B0 B1 by blast    
next
  case (Suc n)
  show ?case
  proof(cases "k \<le> n")
    case True
    then show ?thesis using  Suc.IH 
      by blast
    next
      case False
      have F1: "(ns n) \<in> carrier Zp"
        using  Suc.IH   by blast      
      have F2: "val_Zp (f'\<bullet>(ns n)) = val_Zp ((f'\<bullet>a))"
        using  Suc.IH  by blast      
      have F3: "val_Zp (f\<bullet>(ns n)) \<ge> 2*(val_Zp (f'\<bullet>a)) + (2^n)*t"
        using  Suc.IH  by blast 
      have kval: "k = Suc n"
        using False Suc.prems le_Suc_eq by blast        
      have F6: "val_Zp (f\<bullet>(ns n)) \<ge> val_Zp (f'\<bullet>(ns n))"
      proof-
        have "2*(val_Zp (f'\<bullet>a))  \<ge> val_Zp (f'\<bullet>a)"
          using f'a_closed val_pos eint_mult_mono'[of "val_Zp (f'\<bullet>a)" 1 2]  
          by (metis Groups.add_ac(2) add.right_neutral eSuc_eint eint_0_iff(2) eint_add_left_cancel_le
              eint_ord_simps(2) f'a_nonneg_val f'a_not_infinite infinity_ne_i1 linorder_not_less 
              mult_one_left not_one_less_zero one_add_one one_eint_def order_less_le order_trans zero_one_eint_neq(1))
        hence  "2*(val_Zp (f'\<bullet>a)) + (2^n)*t  \<ge> val_Zp (f'\<bullet>a)"
          using t_times_pow_pos[of n] 
          by (metis (no_types, lifting) add.right_neutral eint_add_left_cancel_le order_less_le order_trans)    
        then show ?thesis 
          using F2 F3 by auto                            
      qed
      have F5: " divide (f\<bullet>(ns n))(f'\<bullet>(ns n)) \<in> carrier Zp"
      proof-
        have 00: "f \<bullet> ns n \<in> carrier Zp"
          by (simp add: F1 to_fun_closed)                     
        have "val_Zp ((f'\<bullet>a)) \<noteq> val_Zp \<zero>"
          by (simp add:  val_Zp_def)
        then have 01: "f' \<bullet> ns n \<in> nonzero Zp"
          using F2 F1 Zp_x_is_UP_cring f'_closed nonzero_def
        proof -
          have "f' \<bullet> ns n \<in> carrier Zp"
            using F1 Zp_continuous_is_Zp_closed f'_closed  polynomial_is_Zp_continuous
            by (simp add: to_fun_closed) 
          then show ?thesis
            using F2 \<open>val_Zp (f'\<bullet>a) \<noteq> val_Zp \<zero>\<close> not_nonzero_Zp by fastforce
        qed           
        then show ?thesis 
          using F6 
          by (metis "00" F2 \<open>val_Zp (f'\<bullet>a) \<noteq> val_Zp \<zero>\<close> divide_closed nonzero_closed)          
      qed
      have F4:  "(ns k) \<ominus> (ns n) = (\<ominus> divide (f\<bullet>(ns n))(f'\<bullet>(ns n)))"
        using F1 F5 newton_seq.simps(2)[of n] kval
        unfolding newton_step_def 
        by (metis R.l_neg R.minus_closed R.minus_zero R.plus_diff_simp R.r_neg2 R.r_right_minus_eq 
            a_minus_def local.a_closed minus_a_inv)
      have F7: "val_Zp (divide (f\<bullet>(ns n))(f'\<bullet>(ns n))) = val_Zp (f\<bullet>(ns n)) - val_Zp (f'\<bullet>(ns n))"
        apply(rule val_of_divide)
           apply (simp add: F1 to_fun_closed)
            using F1 f'_closed to_fun_closed F2 not_nonzero_Zp val_Zp_def apply fastforce
              by (simp add: F6)
      show ?thesis
      proof
        show P0:"ns k \<in> carrier Zp"
        proof- 
          have A0: "ns k = ns n \<ominus> (divide (f\<bullet> (ns n)) (f'\<bullet>(ns n)))"
            by (simp add: kval newton_step_def)          
          have A1: "val_Zp (f'\<bullet>(ns n)) = val_Zp (f'\<bullet>a)"
            using  Suc.IH  
            by blast
          have A2: "val_Zp (f\<bullet>(ns n)) \<ge>val_Zp (f'\<bullet>a)"
          proof-
            have A20: "(2 * val_Zp (f'\<bullet>a)) + 2 ^ n * (val_Zp (f\<bullet>a) - 2 * val_Zp (f'\<bullet>a)) \<ge>val_Zp (f'\<bullet>a)"
            proof-
              have "val_Zp (f\<bullet>a) - 2 * val_Zp (f'\<bullet>a) > 0"
                using hensel_hypothesis eint_minus_le by blast                
              then have "  (2 ^ n) * (val_Zp (f\<bullet>a) - 2 * val_Zp (f'\<bullet>a))
                        \<ge> (val_Zp (f\<bullet>a) - 2 * val_Zp (f'\<bullet>a))"
                using eint_pos_int_times_ge by auto
              then have  "  ((2 * val_Zp (f'\<bullet>a)) + 2 ^ n * (val_Zp (f\<bullet>a) - 2 * val_Zp (f'\<bullet>a)))
                        \<ge> (2 * val_Zp (f'\<bullet>a)) + (val_Zp (f\<bullet>a) - 2 * val_Zp (f'\<bullet>a))"
                by (simp add: val_Zp_def)
              then have  "  ((2 * val_Zp (f'\<bullet>a)) + 2 ^ n * (val_Zp (f\<bullet>a) - 2 * val_Zp (f'\<bullet>a)))
                        \<ge> (val_Zp (f\<bullet>a) )"
                by simp 
              then show  "  ((2 * val_Zp (f'\<bullet>a)) + 2 ^ n * (val_Zp (f\<bullet>a) - 2 * val_Zp (f'\<bullet>a)))
                        \<ge> (val_Zp (f'\<bullet>a) )"
                using hensel_hypothesis_weakened by auto                 
            qed
            have A21:"val_Zp (f\<bullet>(ns n)) \<ge> (2 * val_Zp (f'\<bullet>a)) + 2 ^ n * (val_Zp (f\<bullet>a) - 2 * val_Zp (f'\<bullet>a))"
              using  Suc.IH unfolding hensel_factor_def 
              by blast              
            show ?thesis using A21 A20 
              by auto              
          qed
          have A3: "ns n \<in> carrier Zp"
            using  Suc.IH by blast 
          have A4: "val_Zp (f\<bullet>(ns n)) \<ge>val_Zp (f'\<bullet>(ns n))"
            using A1 A2 
            by presburger
          have A5: "f\<bullet>(ns n) \<in> carrier Zp"
            by (simp add: F1 UP_cring.to_fun_closed Zp_x_is_UP_cring)                      
          have A6: "(f'\<bullet>(ns n)) \<in> nonzero Zp"
          proof-
            have "(f'\<bullet>(ns n)) \<in> carrier  Zp"
              by (simp add: F1 UP_cring.to_fun_closed Zp_x_is_UP_cring f'_closed)                 
            have "val_Zp (f'\<bullet>(ns n)) \<noteq> \<infinity>"
              using A1 
              by (simp add:  val_Zp_def)              
            then show ?thesis 
              using \<open>f' \<bullet> ns n \<in> carrier Zp\<close> not_nonzero_Zp val_Zp_def 
              by meson
          qed
          have A7: " (divide (f\<bullet> (ns n)) (f'\<bullet>(ns n))) \<in> carrier Zp"
            using A5 A6 A4 A3 F5 by linarith            
          then show ?thesis 
            using A0 A3 cring.cring_simprules(4) 
            by (simp add: F1 F5 cring.cring_simprules(4))
        qed
        have P1: "val_Zp (f' \<bullet> ns k) = val_Zp (f'\<bullet>a) "
        proof(cases "(f' \<bullet> ns k) = (f' \<bullet> ns n)")
          case True
          then show ?thesis using  Suc.IH
            by (metis order_refl)
        next
          case False
          have "val_Zp ((f' \<bullet> ns k) \<ominus> (f' \<bullet> ns n)) \<ge> val_Zp ((ns k) \<ominus> (ns n))"
            using False P0 f'_closed  poly_diff_val  Suc.IH 
            by blast
          then have "val_Zp ((f' \<bullet> ns k) \<ominus> (f' \<bullet> ns n)) \<ge> val_Zp (\<ominus> divide (f\<bullet>(ns n))(f'\<bullet>(ns n)))"
            using  F4 by metis  
          then have "val_Zp ((f' \<bullet> ns k) \<ominus> (f' \<bullet> ns n)) \<ge> val_Zp (divide (f\<bullet>(ns n))(f'\<bullet>(ns n)))"
            using F5 val_Zp_of_minus 
            by presburger                        
          then have P10: "val_Zp ((f' \<bullet> ns k) \<ominus> (f' \<bullet> ns n)) \<ge> val_Zp (f\<bullet>(ns n)) - val_Zp (f'\<bullet>(ns n))"
            using F7 by metis 
          have P11: "val_Zp (f'\<bullet>(ns n)) \<noteq> \<infinity>"
            by (simp add: F2)           
          then have "val_Zp ((f' \<bullet> ns k) \<ominus> (f' \<bullet> ns n)) \<ge> (2 * val_Zp (f'\<bullet>a)) + 2 ^ n * t -  val_Zp (f'\<bullet>(ns n))"
            using F3 P10  
            by (smt eint_add_cancel_fact eint_add_left_cancel_le order_trans)                
          then have P12: "val_Zp ((f' \<bullet> ns k) \<ominus> (f' \<bullet> ns n)) \<ge> (2 *(val_Zp (f'\<bullet>a))) + 2 ^ n * t - (val_Zp (f'\<bullet>a))"
            by (simp add: F2)            
          have P13:"val_Zp ((f' \<bullet> ns k) \<ominus> (f' \<bullet> ns n)) \<ge> (val_Zp (f'\<bullet>a)) + 2 ^ n * t "
          proof-
            have "(2 *(val_Zp (f'\<bullet>a))) + (2 ^ n * t) - (val_Zp (f'\<bullet>a)) =  (2 *(val_Zp (f'\<bullet>a))) - (val_Zp (f'\<bullet>a)) + (2 ^ n * t) "
              using eint_minus_comm by blast            
            then show ?thesis using P12 
              using f'a_not_infinite by force
          qed
          then have P14: "val_Zp ((f' \<bullet> ns k) \<ominus> (f' \<bullet> ns n)) > (val_Zp (f'\<bullet>a))"
            using f'a_not_infinite ge_plus_pos_imp_gt t_times_pow_pos by blast
          show ?thesis 
            by (meson F1 F2 P0 P14 equal_val_Zp f'_closed f'a_closed to_fun_closed)
        qed
        have P2: "val_Zp (f\<bullet>(ns k)) \<ge> 2*(val_Zp (f'\<bullet>a)) + (2^k)*t"
        proof- 
          have P23: "2 * (val_Zp (f'\<bullet>a)) + ((2 ^ k) * t) \<le> val_Zp (f \<bullet> ns k)"
          proof-
            have 0: "ns n \<in> carrier Zp"
              by (simp add: F1)
            have 1: "local.divide (f \<bullet> ns n) (f' \<bullet> ns n) \<in> carrier Zp"
              using F5 by blast
            have 2: "(poly_shift_iter 2 (taylor (ns n) f)) \<bullet> \<ominus> local.divide (f \<bullet> ns n) (f' \<bullet> ns n) \<in> carrier Zp"
              using F1 F5 shift_closed 1  
              by (simp add: taylor_closed to_fun_closed)
            have 3: "divide (f \<bullet> ns n) (f' \<bullet> ns n) \<otimes> deriv f (ns n) = f \<bullet> ns n"
              by (metis F1 F2 F6 divide_formula f'_closed f'a_not_infinite f_closed mult_comm pderiv_eval_deriv to_fun_closed val_Zp_def)                  
            have 4: "f \<in> carrier Zp_x"
              by simp
            obtain c where c_def: "c = poly_shift_iter (2::nat) (taylor (ns n) f) \<bullet> \<ominus> local.divide (f \<bullet> ns n) (f' \<bullet> ns n)"
              by blast
            then have c_def': "c \<in> carrier Zp \<and> f \<bullet> (ns n \<ominus> local.divide (f \<bullet> ns n) (f' \<bullet> ns n)) = c \<otimes> local.divide (f \<bullet> ns n) (f' \<bullet> ns n) [^] (2::nat)"
              using 0 1 2 3 4 UP_cring.taylor_deg_1_eval'''[of Zp f "ns n" "(divide (f\<bullet>(ns n)) (f'\<bullet>(ns n)))" c]
                Zp_x_is_UP_cring
              by blast
            have P230: "f\<bullet>(ns k) =  (c \<otimes> (divide (f\<bullet>(ns n)) (f'\<bullet>(ns n)))[^](2::nat))"
              using c_def' 
              by (simp add: kval newton_step_def)                
            have P231: "val_Zp (f\<bullet>(ns k)) = val_Zp c + 2*(val_Zp (f\<bullet>(ns n)) - val_Zp(f'\<bullet>(ns n)))"
                proof-
                  have P2310: "val_Zp (f\<bullet>(ns k)) =  val_Zp c + val_Zp ((divide (f\<bullet>(ns n)) (f'\<bullet>(ns n)))[^](2::nat))"
                    by (simp add: F5 P230 c_def' val_Zp_mult)                
                  have P2311: "val_Zp ((divide (f\<bullet>(ns n)) (f'\<bullet>(ns n)))[^](2::nat)) 
                                                    =  2*(val_Zp (f\<bullet>(ns n)) - val_Zp(f'\<bullet>(ns n)))"
                    by (metis  F5 F7 R.pow_zero mult.commute not_nonzero_Zp of_nat_numeral times_eint_simps(3) val_Zp_def val_Zp_pow' zero_less_numeral)
                  thus ?thesis 
                    by (simp add: P2310)                
                qed
                have P232: "val_Zp (f\<bullet>(ns k)) \<ge> 2*(val_Zp (f\<bullet>(ns n)) - val_Zp(f'\<bullet>(ns n)))"
                  by (simp add: P231 c_def' val_pos)                
                have P236:  "val_Zp (f\<bullet>(ns k)) \<ge> 2*(2 *val_Zp (f'\<bullet>a) + 2 ^ n * t)  - 2* val_Zp(f'\<bullet>(ns n))"
                  using P232 F3 eint_minus_ineq''[of "val_Zp(f'\<bullet>(ns n))" "(2 *val_Zp (f'\<bullet>a)) + 2 ^ n * t" "val_Zp (f\<bullet>(ns n))" 2 ]
                       F2 eint_pow_int_is_pos by auto
                hence  P237:  "val_Zp (f\<bullet>(ns k)) \<ge>(4*val_Zp (f'\<bullet>a)) + (2*((2 ^ n)* t)) - 2* val_Zp(f'\<bullet>(ns n))"
                proof-
                  have "2*(2*val_Zp (f'\<bullet>a) + 2 ^ n * t)  = (4*val_Zp (f'\<bullet>a)) + 2*(2 ^ n)* t "
                    using distrib_left[of 2 "2*val_Zp (f'\<bullet>a)" "2 ^ n * t"] mult.assoc mult_one_right one_eint_def plus_eint_simps(1)
                          hensel_factor_def val_Zp_def by auto
                  then show ?thesis 
                    using P236 
                    by (metis mult.assoc)                  
                qed
                hence P237:  "val_Zp (f\<bullet>(ns k)) \<ge> 4*val_Zp (f'\<bullet>a) + 2*(2 ^ n)* t - 2* val_Zp((f'\<bullet>a))"
                  by (metis F2 mult.assoc)                                  
                hence P238: "val_Zp (f\<bullet>(ns k)) \<ge> 2*val_Zp (f'\<bullet>a) + 2*(2 ^ n)* t"
                  using eint_minus_comm[of "4*val_Zp (f'\<bullet>a) " "2*(2 ^ n)* t" "2* val_Zp((f'\<bullet>a))"]
                  by (simp add: eint_int_minus_distr)
                thus ?thesis 
                  by (simp add: kval)               
          qed
          thus ?thesis 
            by blast   
        qed
        show "val_Zp (to_fun f' (ns k)) = val_Zp (f'\<bullet>a) \<and> 
                2 * val_Zp (f'\<bullet>a) + eint (2 ^ k) * t \<le> val_Zp (to_fun f (ns k))"
          using P1 P2 by blast
      qed
    qed
qed

lemma newton_seq_closed:
shows "ns m \<in> carrier Zp"
  using newton_seq_props_induct 
  by blast

lemma f_of_newton_seq_closed:
shows "f \<bullet> ns m \<in> carrier Zp"
  by (simp add: to_fun_closed newton_seq_closed)

lemma newton_seq_fact1[simp]:
" val_Zp (f'\<bullet>(ns k)) = val_Zp ((f'\<bullet>a))"
using newton_seq_props_induct by blast

lemma newton_seq_fact2:
"\<And>k.  val_Zp (f\<bullet>(ns k)) \<ge> 2*(val_Zp (f'\<bullet>a)) + (2^k)*t"
  by (meson le_iff_add newton_seq_props_induct)

lemma newton_seq_fact3:
"val_Zp (f\<bullet>(ns l)) \<ge> val_Zp (f'\<bullet>(ns l))"
proof-
  have "2*(val_Zp (f'\<bullet>a)) + (2^l)*t \<ge> (val_Zp (f'\<bullet>a))"
    using f'a_closed ord_pos t_pos 
    by (smt eint_pos_int_times_ge f'a_nonneg_val f'a_not_infinite ge_plus_pos_imp_gt linorder_not_less nat_mult_not_infty order_less_le t_times_pow_pos)    
  then show "val_Zp (f \<bullet> ns l) \<ge> val_Zp (f' \<bullet> ns l) "
    using  f'a_closed f'a_nonzero newton_seq_fact1[of l] newton_seq_fact2[of l]  val_Zp_def 
    proof -
    show ?thesis
      using \<open>eint 2 * val_Zp (f'\<bullet>a) + eint (2 ^ l) * t \<le> val_Zp (to_fun f (ns l))\<close> \<open>val_Zp (f'\<bullet>a) \<le> eint 2 * val_Zp (f'\<bullet>a) + eint (2 ^ l) * t\<close> by force
    qed  
qed

lemma newton_seq_fact4[simp]:
  assumes "f\<bullet>(ns l) \<noteq>\<zero>"
  shows "val_Zp (f\<bullet>(ns l)) \<ge> val_Zp (f'\<bullet>(ns l))"
  using newton_seq_fact3 by blast

lemma newton_seq_fact5:
"divide (f \<bullet> ns l) (f' \<bullet> ns l) \<in> carrier Zp"
  apply(rule divide_closed) 
  apply (simp add: to_fun_closed newton_seq_closed)
  apply (simp add: f'_closed to_fun_closed newton_seq_closed)
  by (metis f'a_not_infinite newton_seq_fact1 val_Zp_def)
   
lemma newton_seq_fact6:
"(f'\<bullet>(ns l)) \<in> nonzero Zp"
  apply(rule ccontr)
  using  nonzero_memI nonzero_memE  
        f'a_nonzero newton_seq_fact1  val_Zp_def
  by (metis (no_types, lifting) divide_closed f'_closed f'a_closed fa_closed hensel_factor_id 
      hensel_hypothesis_weakened mult_zero_l newton_seq_closed order_less_le to_fun_closed val_Zp_mult)

lemma newton_seq_fact7:
 "(ns (Suc n)) \<ominus> (ns n) = \<ominus>divide (f\<bullet>(ns n)) (f'\<bullet>(ns n))"
  using newton_seq.simps(2)[of n]  newton_seq_fact5[of n] 
        newton_seq_closed[of "Suc n"]  newton_seq_closed[of n] 
        R.ring_simprules
  unfolding newton_step_def a_minus_def 
  by smt 

lemma newton_seq_fact8:
  assumes "f\<bullet>(ns l) \<noteq>\<zero>"
  shows "divide (f \<bullet> ns l) (f' \<bullet> ns l) \<in> nonzero Zp"
  using assms divide_nonzero[of "f \<bullet> ns l" "f' \<bullet> ns l"]
        nonzero_memI 
  using f_of_newton_seq_closed newton_seq_fact3 newton_seq_fact6 by blast

lemma newton_seq_fact9:
  assumes "f\<bullet>(ns n) \<noteq>\<zero>"
  shows "val_Zp((ns (Suc n)) \<ominus> (ns n)) = val_Zp (f\<bullet>(ns n)) - val_Zp (f'\<bullet>(ns n))"
  using newton_seq_fact7 val_of_divide newton_seq_fact6 assms nonzero_memI
        f_of_newton_seq_closed newton_seq_fact4 newton_seq_fact5 
  by (metis val_Zp_of_minus)

text\<open>Assuming no element of the Newton sequence is a root of f, the Newton sequence is Cauchy.\<close>

lemma newton_seq_is_Zp_cauchy_0:
assumes "\<And>k. f\<bullet>(ns k) \<noteq>\<zero>"
shows "is_Zp_cauchy ns"
proof(rule is_Zp_cauchyI')
  show P0: "ns \<in> closed_seqs Zp"
  proof(rule closed_seqs_memI)
    show "\<And>k. ns k \<in> carrier Zp "
     by (simp add: newton_seq_closed)
 qed
  show "\<forall>n. \<exists>k. \<forall>m. k \<le> int m \<longrightarrow> int n \<le> val_Zp (ns (Suc m) \<ominus> ns m)"
  proof
    fix n
    show "\<exists>k. \<forall>m. k \<le> int m \<longrightarrow> int n \<le> val_Zp (ns (Suc m) \<ominus> ns m)"
    proof(induction "n")
      case 0
      have B0: "\<forall>n0 n1. 0 < n0 \<and> 0 < n1 \<longrightarrow> ns n0 0 = ns n1 0"
        apply auto 
      proof-
        fix n0 n1::nat 
        assume A: "0 < n0" "0 < n1"
        show "ns n0 0 = ns n1 0"
        proof-
          have 0: "ns n0 \<in> carrier Zp"
            using P0 
            by (simp add: newton_seq_closed)           
          have 1: "ns n1 \<in> carrier Zp"
            using P0 
            by (simp add: newton_seq_closed)      
          show ?thesis
            using 0 1 Zp_defs(3) prime  
            by (metis p_res_ring_0' residue_closed)                                
        qed
      qed
      have "\<forall>m. 1 \<le> int m \<longrightarrow> int 0 \<le> val_Zp_dist (newton_step (ns m)) (ns m)"
      proof
        fix m
        show "1 \<le> int m \<longrightarrow> int 0 \<le> val_Zp_dist (newton_step (ns m)) (ns m)"
        proof
        assume "1 \<le> int m "
        then have C0:"ns (Suc m) 0 = ns m 0"
          using B0 
          by (metis int_one_le_iff_zero_less int_ops(1) less_Suc_eq_0_disj of_nat_less_iff)
        then show "int 0 \<le> val_Zp_dist (newton_step (ns m)) (ns m)"
        proof-
          have "(newton_step (ns m)) \<noteq>(ns m)"
          proof-
            have A0: "divide (f\<bullet>(ns m)) (f'\<bullet>(ns m)) \<noteq>\<zero>"
            proof-
              have 0: "(f\<bullet>(ns m)) \<noteq> \<zero>"
                using assms by auto 
              have 1: " (f'\<bullet>(ns m)) \<in> carrier Zp"
                by (simp add: UP_cring.to_fun_closed Zp_x_is_UP_cring f'_closed newton_seq_closed)                
              have 2:  "(f'\<bullet>(ns m)) \<noteq> \<zero>" 
                using newton_seq_fact6 not_nonzero_memI by blast                                              
              show ?thesis using 0 1 2 
                by (metis R.r_null divide_formula f_closed to_fun_closed newton_seq_closed newton_seq_fact4)                
            qed
            have A2: "local.divide (f \<bullet> ns m) (f' \<bullet> ns m) \<in> carrier Zp"
              using newton_seq_fact5 by blast   
            have A3: "ns m \<in> carrier Zp"
              by (simp add: newton_seq_closed)
            have A4: "newton_step (ns m) \<in> carrier Zp"
              by (metis newton_seq.simps(2) newton_seq_closed)
            show ?thesis 
              apply(rule ccontr) 
              using A4 A3 A2 A0 newton_step_def[of "(ns m)"] 
              by (simp add: a_minus_def)
          qed
          then show ?thesis using C0 
            by (metis newton_seq.simps(2) newton_seq_closed val_Zp_dist_res_eq2)
        qed
      qed
      qed
      then show ?case 
        using val_Zp_def val_Zp_dist_def 
        by (metis int_ops(1) newton_seq.simps(2) zero_eint_def)                
    next
      case (Suc n)
      show "\<exists>k. \<forall>m. k \<le> int m \<longrightarrow> int (Suc n) \<le> val_Zp (ns (Suc m) \<ominus> ns m)"
      proof-
        obtain k0 where k0_def: "k0 \<ge>0 \<and> (\<forall>m. k0 \<le> int m \<longrightarrow> int n \<le> val_Zp (ns (Suc m) \<ominus> ns m))"
          using Suc.IH 
          by (metis int_nat_eq le0 nat_le_iff of_nat_0_eq_iff )
        have I0: "\<And>l. val_Zp (ns (Suc l) \<ominus> ns l) = val_Zp (f\<bullet> (ns l)) - val_Zp (f'\<bullet>(ns l))"
        proof-
          fix l
          have I00:"(ns (Suc l) \<ominus> ns l) = (\<ominus> divide (f\<bullet>(ns l)) (f'\<bullet>(ns l)))"
          proof-
            have "local.divide (f \<bullet> ns l) (f' \<bullet> ns l) \<in> carrier Zp"
              by (simp add: newton_seq_fact5) 
            then show ?thesis 
              using newton_seq.simps(2)[of l] newton_seq_closed R.ring_simprules 
              unfolding newton_step_def a_minus_def  
              by (metis add_comm)                 
          qed
          have I01: "val_Zp (ns (Suc l) \<ominus> ns l) = val_Zp (divide (f\<bullet>(ns l)) (f'\<bullet>(ns l)))"   
          proof-
            have I010: "(divide (f\<bullet>(ns l)) (f'\<bullet>(ns l))) \<in>carrier Zp"
             by (simp add: newton_seq_fact5)
           have I011: "(divide (f\<bullet>(ns l)) (f'\<bullet>(ns l))) \<noteq> \<zero>"
           proof-
             have A: "(f\<bullet>(ns l)) \<noteq>\<zero>"
               by (simp add: assms) 
             have B: " (f'\<bullet>(ns l))  \<in>carrier Zp"
               using nonzero_memE newton_seq_fact6 by auto                 
             then have C: " (f'\<bullet>(ns l))  \<in>nonzero  Zp"
               using  f'a_closed fa_closed fa_nonzero hensel_factor_id hensel_hypothesis_weakened
                     newton_seq_fact1[of l]   not_nonzero_Zp val_Zp_def 
               by fastforce
             then show ?thesis using I010 A 
               by (metis B R.r_null divide_formula f_closed to_fun_closed newton_seq_closed newton_seq_fact4 nonzero_memE(2))               
           qed
           then have "val_Zp (divide (f\<bullet>(ns l)) (f'\<bullet>(ns l)))
                    = val_Zp (\<ominus> divide (f\<bullet>(ns l)) (f'\<bullet>(ns l)))"
             using I010 not_nonzero_Zp val_Zp_of_minus by blast
           then show ?thesis using I00 by metis  
          qed
          have I02: "val_Zp (f\<bullet>(ns l)) \<ge> val_Zp (f'\<bullet>(ns l))"
            using assms  newton_seq_fact4
            by blast  
          have I03: "(f\<bullet>(ns l)) \<in> nonzero Zp"
            by (meson UP_cring.to_fun_closed Zp_x_is_UP_cring assms f_closed newton_seq_closed not_nonzero_Zp)           
          have I04: "f'\<bullet>(ns l) \<in> nonzero Zp"
            by (simp add: newton_seq_fact6)            
          have I05 :" val_Zp (divide (f\<bullet>(ns l)) (f'\<bullet>(ns l))) = val_Zp (f\<bullet> (ns l)) - val_Zp (f'\<bullet>(ns l))"
            using I02 I03 I04 I01 assms newton_seq_fact9 by auto                
          then show " val_Zp (ns (Suc l) \<ominus> ns l) = val_Zp (f\<bullet> (ns l)) - val_Zp (f'\<bullet>(ns l))"
            using I01  by simp            
        qed
        have "\<forall>m. int(Suc n) + k0 + 1 \<le> int m \<longrightarrow> int (Suc n) \<le> val_Zp_dist (newton_step (ns m)) (ns m)"
        proof
          fix m
          show "int (Suc n) + k0 + 1 \<le> int m \<longrightarrow> int (Suc n) \<le> val_Zp_dist (newton_step (ns m)) (ns m)"
          proof
          assume A: "int (Suc n) + k0 + 1 \<le> int m "
            show " int (Suc n) \<le> val_Zp_dist (newton_step (ns m)) (ns m)"
            proof-
              have 0: " val_Zp_dist (newton_step (ns m)) (ns m) =  val_Zp (f\<bullet> (ns m)) - val_Zp (f'\<bullet>(ns m))"
                using I0 val_Zp_dist_def by auto         
              have 1: "val_Zp (f\<bullet> (ns m)) - val_Zp (f'\<bullet>(ns m)) > int n"
              proof-
              have "val_Zp (f\<bullet> (ns m)) \<ge> 2*(val_Zp (f'\<bullet>a)) + (2^m)*t"
                by (simp add: newton_seq_fact2)                
              then have 10:"val_Zp (f\<bullet> (ns m)) - val_Zp (f'\<bullet>(ns m)) \<ge> 2*(val_Zp (f'\<bullet>a)) + (2^m)*t -  val_Zp (f'\<bullet>(ns m))"
                by (simp add: eint_minus_ineq)                
              have "2^m * t > m"
                apply(induction m)
                 using one_eint_def zero_eint_def apply auto[1]                 
              proof- fix m 
                assume IH : "int m < 2 ^ m * t " 
                then have "((2 ^ (Suc m)) * t) = 2* ((2 ^ m) * t)"
                  by (metis mult.assoc power_Suc times_eint_simps(1))  
                then show "int (Suc m) < 2 ^ Suc m * t"
                  using IH t_neq_infty by force
              qed
              then have 100: "2^m * t > int m"
                by blast
              have "int m \<ge>2 + (int n + k0)"
                using A by simp
              hence 1000: "2^m * t > 2 + (int n + k0)"
                using 100 
                by (meson eint_ord_simps(2) less_le_trans linorder_not_less)
              have "2 + (int n + k0) > 1 + int n"
                using k0_def by linarith
              then have "2^m * t > 1 + int n"
                using 1000  eint_ord_simps(2) k0_def less_le_trans linorder_not_less
              proof -
                have "eint (2 + (int n + k0)) < t * eint (int (2 ^ m))"
                  by (metis "1000" mult.commute numeral_power_eq_of_nat_cancel_iff)
                then have "eint (int (Suc n)) < t * eint (int (2 ^ m))"
                  by (metis \<open>1 + int n < 2 + (int n + k0)\<close> eint_ord_simps(2) less_trans of_nat_Suc)
                then show ?thesis
                  by (simp add: mult.commute)
              qed
              hence "2*val_Zp (f'\<bullet>a) + eint (2 ^ m) * t \<ge> 2*(val_Zp (f'\<bullet>a)) + 1 + int n"
                by (smt eSuc_eint eint_add_left_cancel_le iadd_Suc iadd_Suc_right order_less_le)
              then have 11: "val_Zp (f\<bullet> (ns m)) - val_Zp (f'\<bullet>(ns m)) 
                                \<ge> 2*(val_Zp (f'\<bullet>a)) + 1 + int n -  val_Zp (f'\<bullet>(ns m))"
                using "10" 
                by (smt \<open>eint 2 * val_Zp (f'\<bullet>a) + eint (2 ^ m) * t \<le> val_Zp (to_fun f (ns m))\<close> 
                    f'a_not_infinite eint_minus_ineq hensel_axioms newton_seq_fact1 order_trans)
              have 12: "val_Zp (f'\<bullet>(ns m))  = val_Zp (f'\<bullet>a) "
                using nonzero_memE  newton_seq_fact1 newton_seq_fact6 val_Zp_def val_Zp_def 
                by auto               
              then have 13: "val_Zp (f\<bullet> (ns m)) - val_Zp (f'\<bullet>(ns m)) 
                                \<ge> 2*(val_Zp (f'\<bullet>a)) + (1 + int n) -  val_Zp ((f'\<bullet>a))"
                using 11 
                by (smt eSuc_eint iadd_Suc iadd_Suc_right)
              then have 14:"val_Zp (f\<bullet> (ns m)) - val_Zp (f'\<bullet>(ns m)) 
                                \<ge> 1 + int n +  val_Zp ((f'\<bullet>a))"
                using eint_minus_comm[of "2*(val_Zp (f'\<bullet>a))" "1 + int n" "val_Zp ((f'\<bullet>a))"] 
                by (simp add: Groups.add_ac(2))
              then show ?thesis 
                by (smt Suc_ile_eq add.right_neutral eint.distinct(2) f'a_nonneg_val ge_plus_pos_imp_gt order_less_le)                
              qed
              then show ?thesis 
               by (smt "0" Suc_ile_eq of_nat_Suc)              
            qed
          qed
        qed
        then show ?thesis 
          using val_Zp_def val_Zp_dist_def 
          by (metis newton_seq.simps(2))          
       qed
    qed
  qed
qed

lemma eventually_zero:
"f \<bullet> ns (k + m) = \<zero> \<Longrightarrow> f \<bullet> ns (k + Suc m) = \<zero>"
proof-
  assume A: "f \<bullet> ns (k + m) = \<zero>"
  have 0: "ns (k + Suc m) = ns (k + m) \<ominus> (divide (f \<bullet> ns (k + m)) (f' \<bullet> ns (k + m)))"
    by (simp add: newton_step_def)
  have 1: "(divide (f \<bullet> ns (k + m)) (f' \<bullet> ns (k + m))) = \<zero>"
    by (simp add: A divide_def)
  show "f \<bullet> ns (k + Suc m) = \<zero>"
    using A 0 1 
    by (simp add: a_minus_def newton_seq_closed)    
qed

text\<open>The Newton Sequence is Cauchy:\<close>

lemma newton_seq_is_Zp_cauchy:
"is_Zp_cauchy ns"
proof(cases "\<forall>k. f\<bullet>(ns k) \<noteq>\<zero>")
  case True
  then show ?thesis using newton_seq_is_Zp_cauchy_0 
    by blast
next
  case False
  obtain k where k_def:"f\<bullet>(ns k) = \<zero>"
    using False by blast
  have 0: "\<And>m. (ns (m + k)) = (ns k)"
  proof-
    fix m
    show "(ns (m + k)) = (ns k)"
    proof(induction m)
      case 0
      then show ?case 
        by simp      
    next
      case (Suc m)
      show "(ns (Suc m + k)) = (ns k)" 
      proof-
        have "f \<bullet> ns (m + k) = \<zero>"
          by (simp add: Suc.IH k_def)
        then have "divide ( f \<bullet> ns (m + k)) (f' \<bullet> ns (m + k)) = \<zero>"
          by (simp add: divide_def)
        then show ?thesis using newton_step_def 
          by (simp add: Suc.IH a_minus_def newton_seq_closed)
      qed
    qed
  qed
  show "is_Zp_cauchy ns"
    apply(rule is_Zp_cauchyI)
    apply (simp add: closed_seqs_memI newton_seq_closed)                  
  proof-
    show "\<And>n.\<And>n. \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> ns n0 n = ns n1 n"
    proof-
      fix n
      show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> ns n0 n = ns n1 n"
      proof-
        have "\<forall>n0 n1. k < n0 \<and> k < n1 \<longrightarrow> ns n0 n = ns n1 n"
          apply auto 
        proof-
          fix n0 n1
          assume A0: "k < n0"
          assume A1: "k < n1"
          obtain m0 where m0_def: "n0 = k + m0"
            using A0 less_imp_add_positive by blast
          obtain m1 where m1_def: "n1 = k + m1"
            using A1 less_imp_add_positive by auto
          show "ns n0 n = ns n1 n"
            using 0 m0_def m1_def 
            by (metis add.commute)
        qed
        then show ?thesis by blast 
      qed
    qed
  qed
qed

subsection\<open>The Proof of Hensel's Lemma\<close>
lemma pre_hensel:
"val_Zp (a \<ominus> (ns n)) >  val_Zp (f'\<bullet>a)"
"\<exists>N. \<forall>n. n> N \<longrightarrow> (val_Zp (a \<ominus> (ns n)) = val_Zp (divide (f\<bullet>a) (f'\<bullet>a)))"
"val_Zp (f'\<bullet>(ns n)) = val_Zp (f'\<bullet>a)"
proof-
  show "val_Zp (a \<ominus> (ns n)) >  val_Zp (f'\<bullet>a)"
  proof(induction n)
    case 0
    then show ?case 
      by (simp add: val_Zp_def)                
  next
    case (Suc n)
    show "val_Zp (a \<ominus> (ns (Suc n))) > val_Zp (f'\<bullet>a)"
    proof-
      have I0: "val_Zp ((ns (Suc n)) \<ominus> (ns n)) >  val_Zp (f'\<bullet>a)"
      proof(cases "(ns (Suc n)) = (ns n)")
        case True
        then show ?thesis 
          by (simp add: newton_seq_closed val_Zp_def)              
      next
        case False         
        have 00:"(ns (Suc n)) \<ominus> (ns n) = \<ominus>divide (f\<bullet>(ns n)) (f'\<bullet>(ns n))"
          using  newton_seq_fact7 by blast                 
        then have 0: "val_Zp((ns (Suc n)) \<ominus> (ns n)) = val_Zp (divide (f\<bullet>(ns n)) (f'\<bullet>(ns n)))"
          using newton_seq_fact5 val_Zp_of_minus by presburger                                                    
        have 1: "(f\<bullet>(ns n)) \<in> nonzero Zp"
          by (metis False R.minus_zero R.r_right_minus_eq 00 divide_def f_closed to_fun_closed 
              newton_seq_closed not_nonzero_Zp)         
        have 2: "f'\<bullet>(ns n) \<in> nonzero Zp"
          by (simp add: newton_seq_fact6)
        have "val_Zp (f\<bullet>(ns n))  \<ge> val_Zp (f'\<bullet>(ns n))"
          using nonzero_memE  \<open>f \<bullet> ns n \<in> nonzero Zp\<close> newton_seq_fact4 by blast
        then have 3:"val_Zp((ns (Suc n)) \<ominus> (ns n)) = val_Zp (f\<bullet>(ns n)) - val_Zp (f'\<bullet>(ns n))"
          using 0 1 2 newton_seq_fact9 nonzero_memE(2) by blast      
        have 4: "val_Zp (f \<bullet> ns n) \<ge> (2 * val_Zp (f'\<bullet>a)) + 2 ^ n * t"
          using newton_seq_fact2[of n] by metis  
        then have 5: "val_Zp((ns (Suc n)) \<ominus> (ns n)) \<ge> ((2 * val_Zp (f'\<bullet>a)) + 2 ^ n * t) - val_Zp (f'\<bullet>(ns n))"
          using "3" eint_minus_ineq f'a_not_infinite newton_seq_fact1 by presburger
        have 6: "((ns (Suc n)) \<ominus> (ns n)) \<in> nonzero Zp"
          using False not_eq_diff_nonzero newton_seq_closed by blast
        then have "val_Zp((ns (Suc n)) \<ominus> (ns n)) \<ge> (2 * val_Zp (f'\<bullet>a)) + 2 ^ n * t - val_Zp ((f'\<bullet>a))"
          using "5" by auto         
        then have 7: "val_Zp((ns (Suc n)) \<ominus> (ns n)) \<ge> (val_Zp (f'\<bullet>a)) + 2 ^ n * t"
          by (simp add: eint_minus_comm)         
        then show  "val_Zp((ns (Suc n)) \<ominus> (ns n)) > (val_Zp (f'\<bullet>a))"
          using f'a_not_infinite ge_plus_pos_imp_gt t_times_pow_pos by blast
      qed      
      have "val_Zp ((ns (Suc n)) \<ominus> (ns n)) = val_Zp ((ns n) \<ominus> (ns (Suc n)))"
        using  newton_seq_closed[of "n"]  newton_seq_closed[of "Suc n"]
                 val_Zp_def val_Zp_dist_def val_Zp_dist_sym val_Zp_def 
        by auto
      then have I1: "val_Zp ((ns n) \<ominus> (ns (Suc n))) > val_Zp (f'\<bullet>a)"
        using I0 
        by presburger
      have I2: " (a \<ominus> (ns n)) \<oplus> ((ns n) \<ominus> (ns (Suc n))) = (a \<ominus> (ns (Suc n)))"
          by (metis R.plus_diff_simp add_comm local.a_closed newton_seq_closed)                    
      then have "val_Zp (a \<ominus> (ns (Suc n))) \<ge> min (val_Zp (a \<ominus> ns n)) (val_Zp (ns n \<ominus> ns (Suc n)))"
          by (metis R.minus_closed local.a_closed newton_seq_closed val_Zp_ultrametric)               
      thus ?thesis 
        using I1 Suc.IH eint_min_ineq by blast
    qed
  qed
  show "val_Zp (f'\<bullet>(ns n)) = val_Zp (f'\<bullet>a)"
    using newton_seq_fact1 by blast
  show "\<exists>N.\<forall>n. n> N \<longrightarrow> (val_Zp (a \<ominus> (ns n)) = val_Zp (divide (f\<bullet>a) (f'\<bullet>a)))"
  proof-
    have P: "\<And>m. m > 1 \<Longrightarrow> (val_Zp (a \<ominus> (ns m)) = val_Zp (divide (f\<bullet>a) (f'\<bullet>a)))"
    proof-
      fix n::nat
      assume AA: "n >1"
      show " (val_Zp (a \<ominus> (ns n)) = val_Zp (divide (f\<bullet>a) (f'\<bullet>a)))" 
      proof(cases "(ns 1) = a")
        case True
        have T0: "\<And>k. \<forall>n. n \<le> k \<longrightarrow>  ns n = a"
        proof-
          fix k
          show " \<forall>n. n \<le> k \<longrightarrow>  ns n = a"
          proof(induction k)
            case 0
            then show ?case 
              by simp 
          next
            case (Suc k)
            show "\<forall>n\<le>Suc k. ns n = a" apply auto 
            proof-
              fix n
              assume A: "n \<le>Suc k"
              show "ns n = a"
              proof(cases "n < Suc k")
                case True
                then show ?thesis using Suc.IH by auto 
              next
                case False thus ?thesis 
                  using A Suc.IH True by auto
              qed
            qed
          qed
        qed
        show "val_Zp (a \<ominus> ns n) = val_Zp (local.divide (f\<bullet>a) (f'\<bullet>a))"
          by (metis T0  Zp_def Zp_defs(3) f'a_closed f'a_nonzero fa_nonzero 
              hensel.fa_closed hensel_axioms hensel_hypothesis_weakened le_eq_less_or_eq 
              newton_seq_fact9 not_nonzero_Qp order_less_le val_of_divide)
      next
        case False  
        have F0: "(1::nat) \<le> n"
          using AA by simp 
        have "(f\<bullet>a) \<noteq> \<zero>"
          by simp
        have "\<And>k. val_Zp (a \<ominus> ns (Suc k)) = val_Zp (local.divide (f\<bullet>a) (f'\<bullet>a))"
        proof-
          fix k
          show " val_Zp (a \<ominus> ns (Suc k)) = val_Zp (local.divide (f\<bullet>a) (f'\<bullet>a))"
          proof(induction k)
            case 0             
            have "(a \<ominus> ns (Suc 0)) = (local.divide (f\<bullet>a) (f'\<bullet>a))" 
              by (metis R.minus_minus Zp_def hensel.newton_seq_fact7 hensel_axioms 
                  local.a_closed minus_a_inv newton_seq.simps(1) newton_seq.simps(2) newton_seq_fact5 newton_step_closed)
            then show ?case by simp
          next
            case (Suc k)
            have I0: "ns (Suc (Suc k)) = ns (Suc k) \<ominus> (divide (f\<bullet>(ns (Suc k))) (f'\<bullet>(ns (Suc k))))"
              by (simp add: newton_step_def)
            have I1: "val_Zp (f\<bullet>(ns (Suc k))) \<ge> val_Zp(f'\<bullet>(ns (Suc k)))"
              using newton_seq_fact3 by blast
            have I2: "(divide (f\<bullet>(ns (Suc k))) (f'\<bullet>(ns (Suc k)))) \<in> carrier Zp"
              using newton_seq_fact5 by blast
            have I3: "ns (Suc (Suc k)) \<ominus> ns (Suc k) = \<ominus>(divide (f\<bullet>(ns (Suc k))) (f'\<bullet>(ns (Suc k))))"
              using I0 I2 newton_seq_fact7 by blast                                     
            then have "val_Zp (ns (Suc (Suc k)) \<ominus> ns (Suc k)) = val_Zp (divide (f\<bullet>(ns (Suc k))) (f'\<bullet>(ns (Suc k))))"
              using I2 val_Zp_of_minus 
              by presburger   
            then have "val_Zp (ns (Suc (Suc k)) \<ominus> ns (Suc k)) = val_Zp (f\<bullet>(ns (Suc k))) - val_Zp (f'\<bullet>(ns (Suc k)))"
              by (metis I1 R.zero_closed Zp_def newton_seq_fact6 newton_seq_fact9 padic_integers.val_of_divide padic_integers_axioms)    
            then have I4: "val_Zp (ns (Suc (Suc k)) \<ominus> ns (Suc k)) = val_Zp (f\<bullet>(ns (Suc k))) - val_Zp ((f'\<bullet>a))"
              using newton_seq_fact1 by presburger                  
            have F3: "val_Zp (a \<ominus> ns (Suc k)) = val_Zp (local.divide (f\<bullet>a) (f'\<bullet>a))"
              using Suc.IH by blast
            have F4: "a \<ominus>  ns (Suc (Suc k)) = (a \<ominus> ( ns (Suc k))) \<oplus> (ns  (Suc k)) \<ominus> ns (Suc (Suc k))"
              by (metis R.ring_simprules(17) a_minus_def add_comm local.a_closed newton_seq_closed)                                          
            have F5: "val_Zp ((ns  (Suc k)) \<ominus> ns (Suc (Suc k))) > val_Zp (a \<ominus> ( ns (Suc k)))"
            proof-
              have F50:  "val_Zp ((ns  (Suc k)) \<ominus> ns (Suc (Suc k))) = val_Zp (f\<bullet>(ns (Suc k))) - val_Zp ((f'\<bullet>a))"
                by (metis I4 R.minus_closed minus_a_inv newton_seq_closed val_Zp_of_minus)
                                                          
              have F51: "val_Zp (f\<bullet>(ns (Suc k))) > val_Zp ((f\<bullet>a))"                 
              proof-
                have F510: "val_Zp (f\<bullet>(ns (Suc k))) \<ge>  2*val_Zp (f'\<bullet>a) + 2^(Suc k)*t "
                  using newton_seq_fact2 by blast                    
                hence F511: "val_Zp (f\<bullet>(ns (Suc k))) \<ge>  2*val_Zp (f'\<bullet>a) + 2*t "
                  using eint_plus_times[of t "2*val_Zp (f'\<bullet>a)" "2^(Suc k)" "val_Zp (f\<bullet>(ns (Suc k)))" 2] t_pos
                  by (simp add: order_less_le)
                have F512: "2*val_Zp (f'\<bullet>a) + 2*t  = 2 *val_Zp (f\<bullet>a) - 2* val_Zp (f'\<bullet>a)"               
                  unfolding hensel_factor_def
                  using eint_minus_distr[of "val_Zp (f\<bullet>a)" "2 * val_Zp (f'\<bullet>a)" 2] 
                        eint_minus_comm[of _ _ "eint 2 * (eint 2 * val_Zp (f'\<bullet>a))"]   
                  by (smt eint_2_minus_1_mult eint_add_cancel_fact eint_minus_comm f'a_not_infinite hensel_hypothesis nat_mult_not_infty order_less_le)
                hence "2*val_Zp (f'\<bullet>a) + 2*t  > val_Zp (f\<bullet>a)"
                  using hensel_hypothesis 
                  by (smt add_diff_cancel_eint eint_add_cancel_fact eint_add_left_cancel_le 
                      eint_pos_int_times_gt f'a_not_infinite hensel_factor_def nat_mult_not_infty order_less_le t_neq_infty t_pos)
                thus ?thesis using F512 
                  using F511 less_le_trans by blast
              qed
              thus ?thesis 
                by (metis F3 F50 Zp_def divide_closed eint_add_cancel_fact eint_minus_ineq 
                    f'a_closed f'a_nonzero f'a_not_infinite fa_closed fa_nonzero hensel.newton_seq_fact7 
                    hensel_axioms newton_seq.simps(1) newton_seq_fact9 order_less_le val_Zp_of_minus)
            qed
            have "a \<ominus> ns (Suc k) \<oplus> (ns (Suc k) \<ominus> ns (Suc (Suc k))) = a  \<ominus> ns (Suc (Suc k))"
              by (metis F4 a_minus_def add_assoc)
            then show F6: "val_Zp (a \<ominus> ns (Suc (Suc k))) = val_Zp (local.divide (f\<bullet>a) (f'\<bullet>a))"
              using F5 F4 F3  
              by (metis R.minus_closed local.a_closed newton_seq_closed order_less_le val_Zp_not_equal_ord_plus_minus val_Zp_ultrametric_eq'')                 
          qed
        qed
        thus ?thesis 
          by (metis AA less_imp_add_positive plus_1_eq_Suc)        
      qed
    qed
    thus ?thesis 
      by blast
  qed
qed

lemma hensel_seq_comp_f:
 "res_lim ((to_fun f) \<circ> ns) = \<zero>"
proof-
  have A: "is_Zp_cauchy ((to_fun f) \<circ> ns)"
    using f_closed is_Zp_continuous_def newton_seq_is_Zp_cauchy polynomial_is_Zp_continuous 
    by blast
  have "Zp_converges_to ((to_fun f) \<circ> ns) \<zero>"
    apply(rule Zp_converges_toI)
    using A is_Zp_cauchy_def apply blast
     apply simp     
  proof-
    fix n
    show " \<exists>N. \<forall>k>N. (((to_fun f) \<circ> ns) k) n = \<zero> n"
    proof-
      have 0: "\<And>k. (k::nat)>3 \<longrightarrow>  val_Zp (f\<bullet>(ns k)) > k"
      proof
        fix k::nat
        assume A: "k >3"
        show "val_Zp (f\<bullet>(ns k)) > k "
        proof-
          have 0: " val_Zp (f\<bullet>(ns k)) \<ge>  2*(val_Zp (f'\<bullet>a)) + (2^k)*t"
            using newton_seq_fact2 by blast   
          have 1: "2*(val_Zp (f'\<bullet>a)) + (2^k)*t > k "
          proof-
            have "(2^k)*t \<ge> (2^k) "
              apply(cases "t = \<infinity>")
               apply simp
            using t_pos eint_mult_mono' 
            proof -
              obtain ii :: "eint \<Rightarrow> int" where
                f1: "\<forall>e. (\<infinity> \<noteq> e \<or> (\<forall>i. eint i \<noteq> e)) \<and> (eint (ii e) = e \<or> \<infinity> = e)"
                by (metis not_infinity_eq)
              then have "0 < ii t"
                by (metis (no_types) eint_ord_simps(2) t_neq_infty t_pos zero_eint_def)
              then show ?thesis
                using f1 by (metis eint_pos_int_times_ge eint_mult_mono linorder_not_less 
                            mult.commute order_less_le t_neq_infty t_pos t_times_pow_pos)
            qed
            hence " 2*(val_Zp (f'\<bullet>a)) + (2^k)*t \<ge> (2^k) "
              by (smt Groups.add_ac(2) add.right_neutral eint_2_minus_1_mult eint_pos_times_is_pos
                  eint_pow_int_is_pos f'a_nonneg_val ge_plus_pos_imp_gt idiff_0_right linorder_not_less 
                  nat_mult_not_infty order_less_le t_neq_infty) 
            then have  " 2*(val_Zp (f'\<bullet>a)) + (2^k)*t > k"
              using A  of_nat_1 of_nat_add of_nat_less_two_power 
              by (smt eint_ord_simps(1) linorder_not_less order_trans)              
            then show ?thesis 
              by metis
          qed
          thus ?thesis 
            using 0 less_le_trans by blast          
        qed
      qed
      have 1: "\<And>k. (k::nat)>3 \<longrightarrow>  (f\<bullet>(ns k)) k = 0"
      proof
        fix k::nat
        assume B: "3<k"
        show " (f\<bullet>(ns k)) k = 0"
        proof-
          have B0: " val_Zp (f\<bullet>(ns k)) > k"
            using 0 B 
            by blast
          then show ?thesis 
            by (simp add: f_of_newton_seq_closed zero_below_val_Zp)
        qed
      qed
      have "\<forall>k>(max 3 n). (((to_fun f) \<circ> ns) k) n = \<zero> n"
        apply auto
      proof-
        fix k::nat
        assume A: "3< k"
        assume A': "n < k"
        have A0: "(f\<bullet>(ns k)) k = 0"
          using 1[of k] A by auto 
        then have "(f\<bullet>(ns k)) n = 0"
          using A A'
          using above_ord_nonzero[of "(f\<bullet>(ns k))"]
          by (smt UP_cring.to_fun_closed Zp_x_is_UP_cring f_closed le_eq_less_or_eq 
              newton_seq_closed of_nat_mono residue_of_zero(2) zero_below_ord)
        then show A1:  "to_fun f (ns k) n = \<zero> n"
          by (simp add: residue_of_zero(2))          
      qed
      then show ?thesis by blast 
    qed
  qed
  then show ?thesis 
    by (metis Zp_converges_to_def unique_limit') 
qed

lemma full_hensels_lemma:
  obtains \<alpha> where
       "f\<bullet>\<alpha> = \<zero>" and "\<alpha> \<in> carrier Zp"
       "val_Zp (a \<ominus> \<alpha>) > val_Zp (f'\<bullet>a)"
       "(val_Zp (a \<ominus> \<alpha>) = val_Zp (divide (f\<bullet>a) (f'\<bullet>a)))"
       "val_Zp (f'\<bullet>\<alpha>) = val_Zp (f'\<bullet>a)"
proof(cases "\<exists>k. f\<bullet>(ns k) =\<zero>")
  case True
  obtain k where k_def: "f\<bullet>(ns k) =\<zero>"
    using True by blast
  obtain N where N_def: "\<forall>n. n> N \<longrightarrow> (val_Zp (a \<ominus> (ns n)) = val_Zp (divide (f\<bullet>a) (f'\<bullet>a)))"
    using pre_hensel(2) by blast
  have Z: "\<And>n. n \<ge>k \<Longrightarrow> f\<bullet>(ns n) =\<zero>"
  proof-
    fix n
    assume A: "n \<ge>k"
    obtain l where l_def:"n = k + l"
      using A le_Suc_ex 
      by blast
    have "\<And>m. f\<bullet>(ns (k+m)) =\<zero>"
    proof-
      fix m
      show "f\<bullet>(ns (k+m)) =\<zero>"
        apply(induction m)
         apply (simp add: k_def)
        using  eventually_zero 
        by simp
    qed
    then show "f\<bullet>(ns n) =\<zero>"
      by (simp add: l_def)
  qed
  obtain M where M_def: "M = N + k"
    by simp 
  then have M_root: "f\<bullet>(ns M) =\<zero>"
    by (simp add: Z)
  obtain \<alpha> where alpha_def: "\<alpha>= ns M"
    by simp 
  have T0: "f\<bullet>\<alpha> = \<zero>"
    using alpha_def M_root 
    by auto
  have T1:    "val_Zp (a \<ominus> \<alpha>) > val_Zp (f'\<bullet>a)"
    using alpha_def pre_hensel(1) by blast
  have T2: "(val_Zp (a \<ominus> \<alpha>) = val_Zp (divide (f\<bullet>a) (f'\<bullet>a)))"
    by (metis M_def N_def alpha_def fa_nonzero k_def 
        less_add_same_cancel1 newton_seq.elims zero_less_Suc)
  have T3:  "val_Zp (f'\<bullet>\<alpha>) = val_Zp (f'\<bullet>a)"
    using alpha_def newton_seq_fact1 by blast
  show ?thesis using T0 T1 T2 T3 
    using that alpha_def newton_seq_closed 
    by blast   
next 
  case False
  then have Nz: "\<And>k. f\<bullet>(ns k) \<noteq>\<zero>"
    by blast
  have ns_cauchy: "is_Zp_cauchy ns"
    by (simp add: newton_seq_is_Zp_cauchy)
  have fns_cauchy: "is_Zp_cauchy ((to_fun f) \<circ> ns)"
    using f_closed is_Zp_continuous_def ns_cauchy polynomial_is_Zp_continuous by blast
  have F0: "res_lim ((to_fun f) \<circ> ns) = \<zero>"
  proof-
    show ?thesis 
      using hensel_seq_comp_f by auto 
  qed
  obtain \<alpha> where alpha_def: "\<alpha> = res_lim ns"
    by simp
  have F1: "(f\<bullet>\<alpha>)= \<zero>"
    using F0 alpha_def alt_seq_limit
      ns_cauchy polynomial_is_Zp_continuous res_lim_pushforward 
      res_lim_pushforward' by auto
  have F2: "val_Zp (a \<ominus> \<alpha>) > val_Zp (f'\<bullet>a) \<and>  val_Zp (a \<ominus> \<alpha>) = val_Zp (local.divide (f\<bullet>a) (f'\<bullet>a))"
  proof-
    have 0: "Zp_converges_to ns \<alpha>"
      by (simp add: alpha_def is_Zp_cauchy_imp_has_limit ns_cauchy)
    have "val_Zp (a \<ominus> \<alpha>) < \<infinity>"
      using "0" F1 R.r_right_minus_eq Zp_converges_to_def Zp_def hensel.fa_nonzero hensel_axioms local.a_closed val_Zp_def 
      by auto
    hence "1 + max (eint 2 + val_Zp (f'\<bullet>a)) (val_Zp (\<alpha> \<ominus> a)) < \<infinity>"
      by (metis "0" R.minus_closed Zp_converges_to_def eint.distinct(2) eint_ord_simps(4) 
          f'a_not_infinite infinity_ne_i1 local.a_closed max_def minus_a_inv 
          sum_infinity_imp_summand_infinity val_Zp_of_minus)
    then obtain l where l_def: "eint l = 1 + max (eint 2 + val_Zp (f'\<bullet>a)) (val_Zp (\<alpha> \<ominus> a))"
      by auto
    then obtain N where N_def: "(\<forall>m>N. 1 + max (2 + val_Zp (f'\<bullet>a)) (val_Zp (\<alpha> \<ominus> a)) < val_Zp_dist (ns m) \<alpha>)"
      using 0 l_def Zp_converges_to_def[of ns \<alpha>] unfolding val_Zp_dist_def 
      by metis        
    obtain N' where N'_def: "\<forall>n>N'. val_Zp (a \<ominus> ns n) = val_Zp (local.divide (f\<bullet>a) (f'\<bullet>a))"
      using pre_hensel(2) by blast 
    obtain K where K_def: "K = Suc (max N N')"
      by simp 
    then have F21: "(1+ (max (2 + val_Zp (f'\<bullet>a)) (val_Zp (\<alpha> \<ominus> a)))) < val_Zp_dist (ns K) \<alpha>"
      by (metis N_def lessI linorder_not_less max_def order_trans)         
    have F22: "a \<noteq> ns K"
      by (smt False K_def N'_def Zp_def cring_def eint.distinct(2) hensel_factor_id lessI 
          less_le_trans linorder_not_less max_def mult_comm mult_zero_l newton_seq_closed 
          order_less_le padic_int_is_cring padic_integers.prime padic_integers_axioms ring.r_right_minus_eq 
          val_Zp_def)
    show ?thesis
    proof(cases "ns K = \<alpha>")
      case True
      then show ?thesis 
        using pre_hensel F1 False by blast
    next
      case False
      assume "ns K \<noteq> \<alpha>"
      show ?thesis
      proof-
        have P0: " (a \<ominus> \<alpha>) \<in> nonzero Zp"
          by (metis (mono_tags, hide_lams) F1 not_eq_diff_nonzero 
              \<open>Zp_converges_to ns \<alpha>\<close> a_closed Zp_converges_to_def fa_nonzero)
        have P1: "(\<alpha> \<ominus> (ns K)) \<in> nonzero Zp"
          using False not_eq_diff_nonzero \<open>Zp_converges_to ns \<alpha>\<close> 
            Zp_converges_to_def newton_seq_closed
          by (metis (mono_tags, hide_lams))
        have P2: "a \<ominus> (ns K) \<in> nonzero Zp"
          using F22 not_eq_diff_nonzero 
                a_closed newton_seq_closed 
          by blast
        have P3: "(a \<ominus> \<alpha>) = a \<ominus> (ns K) \<oplus> ((ns K) \<ominus> \<alpha>)"
          by (metis R.plus_diff_simp \<open>Zp_converges_to ns \<alpha>\<close> add_comm Zp_converges_to_def local.a_closed newton_seq_closed)                           
        have P4: "val_Zp (a \<ominus> \<alpha>) \<ge> min (val_Zp (a \<ominus> (ns K))) (val_Zp ((ns K) \<ominus> \<alpha>))"
          using "0" P3 Zp_converges_to_def newton_seq_closed val_Zp_ultrametric 
          by auto          
        have P5: "val_Zp (a \<ominus> (ns K)) >  val_Zp (f'\<bullet>a)"
          using pre_hensel(1)[of "K"] 
          by metis                
        have "1 + max (eint 2 + val_Zp (f'\<bullet>a)) (val_Zp (\<alpha> \<ominus> a)) > val_Zp (f'\<bullet>a)"
        proof-
          have "1 + max (eint 2 + val_Zp (f'\<bullet>a)) (val_Zp (\<alpha> \<ominus> a)) > (eint 2 + val_Zp (f'\<bullet>a))"
          proof -
            obtain ii :: int where
              f1: "eint ii = 1 + max (eint 2 + val_Zp (f'\<bullet>a)) (val_Zp (\<alpha> \<ominus> a))"
              by (meson l_def)
            then have "1 + (eint 2 + val_Zp (f'\<bullet>a)) \<le> eint ii"
              by simp
            then show ?thesis
              using f1 by (metis Groups.add_ac(2) iless_Suc_eq linorder_not_less)
          qed
          thus ?thesis 
            by (smt Groups.add_ac(2) eint_pow_int_is_pos f'a_not_infinite ge_plus_pos_imp_gt order_less_le)
        qed
        hence P6: "val_Zp ((ns K) \<ominus> \<alpha>) >  val_Zp (f'\<bullet>a)"
          using F21 unfolding val_Zp_dist_def 
          by auto     
        have P7: "val_Zp (a \<ominus> \<alpha>) >  val_Zp (f'\<bullet>a)"
          using P4 P5 P6 eint_min_ineq by blast
        have P8:  "val_Zp (a \<ominus> \<alpha>) = val_Zp (local.divide (f\<bullet>a) (f'\<bullet>a))"
        proof-
          have " 1 + max (2 + val_Zp (f'\<bullet>a)) (val_Zp_dist \<alpha> a) \<le> val_Zp_dist (ns K) \<alpha>"
            using False F21 
            by (simp add: val_Zp_dist_def)           
          then have "val_Zp(\<alpha> \<ominus> (ns K)) >   max (2 + val_Zp (f'\<bullet>a)) (val_Zp_dist \<alpha> a)"
            by (metis "0" Groups.add_ac(2) P1 Zp_converges_to_def eSuc_mono iless_Suc_eq l_def 
                minus_a_inv newton_seq_closed nonzero_closed val_Zp_dist_def val_Zp_of_minus)                                          
          then have "val_Zp(\<alpha> \<ominus> (ns K)) > val_Zp (a \<ominus> \<alpha>) "
            using \<open>Zp_converges_to ns \<alpha>\<close> Zp_converges_to_def val_Zp_dist_def val_Zp_dist_sym 
            by auto
          then have P80: "val_Zp (a \<ominus> \<alpha>) = val_Zp (a \<ominus> (ns K))"
            using P0 P1 Zp_def val_Zp_ultrametric_eq[of "\<alpha> \<ominus> ns K" "a \<ominus> \<alpha>"] 0 R.plus_diff_simp 
              Zp_converges_to_def local.a_closed newton_seq_closed nonzero_closed by auto
          have P81: "val_Zp (a \<ominus> ns K) = val_Zp (local.divide (f\<bullet>a) (f'\<bullet>a))"
            using K_def N'_def 
            by (metis (no_types, lifting) lessI linorder_not_less max_def order_less_le order_trans)
          then show ?thesis       
            by (simp add: P80)            
        qed
        thus ?thesis 
          using P7 by blast        
      qed          
    qed
  qed
  have F3: "val_Zp (f' \<bullet> \<alpha>) = val_Zp (f'\<bullet>a)"
  proof-
    have F31: " (f' \<bullet> \<alpha>) = res_lim ((to_fun f') \<circ> ns)"
      using alpha_def alt_seq_limit ns_cauchy polynomial_is_Zp_continuous res_lim_pushforward
          res_lim_pushforward' f'_closed 
      by auto
    obtain N where N_def: "val_Zp (f'\<bullet>\<alpha> \<ominus> f'\<bullet>(ns N)) > val_Zp ((f'\<bullet>a))"
      by (smt F2 False R.minus_closed Suc_ile_eq Zp_def alpha_def f'_closed f'a_nonzero 
          local.a_closed minus_a_inv newton_seq.simps(1) newton_seq_is_Zp_cauchy_0 order_trans
          padic_integers.poly_diff_val padic_integers_axioms res_lim_in_Zp val_Zp_def val_Zp_of_minus)      
    show ?thesis
      by (metis False N_def alpha_def equal_val_Zp f'_closed newton_seq_closed newton_seq_is_Zp_cauchy_0 newton_seq_fact1 res_lim_in_Zp to_fun_closed)
  qed
  show ?thesis 
    using F1 F2 F3 that alpha_def ns_cauchy res_lim_in_Zp 
    by blast
qed


end

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Removing Hensel's Lemma from the Hensel Locale\<close>
(**************************************************************************************************)
(**************************************************************************************************)

context padic_integers
begin


lemma hensels_lemma:
  assumes "f \<in> carrier Zp_x"
  assumes "a \<in> carrier Zp"
  assumes "(pderiv f)\<bullet>a \<noteq> \<zero>"
  assumes "f\<bullet>a \<noteq>\<zero>"
  assumes "val_Zp (f\<bullet>a) > 2* val_Zp ((pderiv f)\<bullet>a)"
  obtains \<alpha> where
       "f\<bullet>\<alpha> = \<zero>" and "\<alpha> \<in> carrier Zp" 
       "val_Zp (a \<ominus> \<alpha>) > val_Zp ((pderiv f)\<bullet>a)"
       "val_Zp (a \<ominus> \<alpha>) = val_Zp (divide (f\<bullet>a) ((pderiv f)\<bullet>a))"
       "val_Zp ((pderiv f)\<bullet>\<alpha>) = val_Zp ((pderiv f)\<bullet>a)"
proof-
  have "hensel p f a"
    using assms 
    by (simp add: Zp_def hensel.intro hensel_axioms.intro padic_integers_axioms)
  then show ?thesis 
    using hensel.full_hensels_lemma  Zp_def that    
    by blast     
qed

text\<open>Uniqueness of the root found in Hensel's lemma \<close>

lemma hensels_lemma_unique_root:
  assumes "f \<in> carrier Zp_x"
  assumes "a \<in> carrier Zp"
  assumes "(pderiv f)\<bullet>a \<noteq> \<zero>"
  assumes "f\<bullet>a \<noteq>\<zero>"
  assumes "(val_Zp (f\<bullet>a) > 2* val_Zp ((pderiv f)\<bullet>a))"
  assumes "f\<bullet>\<alpha> = \<zero>" 
  assumes "\<alpha> \<in> carrier Zp" 
  assumes "val_Zp (a \<ominus> \<alpha>) > val_Zp ((pderiv f)\<bullet>a)"
  assumes "f\<bullet>\<beta> = \<zero>" 
  assumes "\<beta> \<in> carrier Zp" 
  assumes "val_Zp (a \<ominus> \<beta>) > val_Zp ((pderiv f)\<bullet>a)"
  assumes "val_Zp ((pderiv f)\<bullet>\<alpha>) = val_Zp ((pderiv f)\<bullet>a)"
  shows "\<alpha> = \<beta>"
proof-
  have "\<alpha> \<noteq> a"
    using assms(4) assms(6) by auto
  have "\<beta> \<noteq> a"
    using assms(4) assms(9) by auto
  have 0: "val_Zp (\<beta> \<ominus> \<alpha>) >  val_Zp ((pderiv f)\<bullet>a)"
  proof-
    have "\<beta> \<ominus> \<alpha> = \<ominus> ((a \<ominus> \<beta>) \<ominus> (a \<ominus> \<alpha>))"
      by (metis R.minus_eq R.plus_diff_simp assms(10) assms(2) assms(7) minus_a_inv)   
    hence "val_Zp (\<beta> \<ominus> \<alpha>) = val_Zp ((a \<ominus> \<beta>) \<ominus> (a \<ominus> \<alpha>))"
      using R.minus_closed assms(10) assms(2) assms(7) val_Zp_of_minus by presburger
    thus ?thesis using val_Zp_ultrametric_diff[of "a \<ominus> \<beta>" "a \<ominus> \<alpha>"]
      by (smt R.minus_closed assms(10) assms(11) assms(2) assms(7) assms(8) min.absorb2 min_less_iff_conj)      
  qed
  obtain h where h_def: "h = \<beta> \<ominus> \<alpha>"
    by blast 
  then have h_fact: "h \<in> carrier Zp \<and> \<beta> = \<alpha> \<oplus> h"
    by (metis R.l_neg R.minus_closed R.minus_eq R.r_zero add_assoc add_comm assms(10) assms(7))    
  then have 1: "f\<bullet>(\<alpha> \<oplus> h) = \<zero>"
    using assms 
    by blast
  obtain c where c_def: "c \<in> carrier Zp \<and> f\<bullet>(\<alpha> \<oplus> h) = (f \<bullet> \<alpha>) \<oplus> (deriv f \<alpha>)\<otimes>h \<oplus> c \<otimes>(h[^](2::nat))"
    using taylor_deg_1_eval'[of  f \<alpha> h _ "f \<bullet> \<alpha>" "deriv f \<alpha>" ]
    by (meson taylor_closed assms(1) assms(7) to_fun_closed h_fact shift_closed)    
  then have  "(f \<bullet> \<alpha>) \<oplus> (deriv f \<alpha>)\<otimes>h \<oplus> c \<otimes>(h[^](2::nat)) = \<zero>"
    by (simp add: "1")
  then have 2:  "(deriv f \<alpha>)\<otimes>h \<oplus> c \<otimes>(h[^](2::nat)) = \<zero>"
   by (simp add: assms(1) assms(6) assms(7) deriv_closed h_fact)   
  have 3: "((deriv f \<alpha>) \<oplus> c \<otimes>h)\<otimes>h = \<zero>"
  proof-
    have "((deriv f \<alpha>) \<oplus> c \<otimes>h)\<otimes>h = ((deriv f \<alpha>)\<otimes>h \<oplus> (c \<otimes>h)\<otimes>h)"
      by (simp add: R.r_distr UP_cring.deriv_closed Zp_x_is_UP_cring assms(1) assms(7) c_def h_fact mult_comm)      
    then have "((deriv f \<alpha>) \<oplus> c \<otimes>h)\<otimes>h = (deriv f \<alpha>)\<otimes>h \<oplus> (c \<otimes>(h\<otimes>h))"
      by (simp add: mult_assoc)      
    then have "((deriv f \<alpha>) \<oplus> c \<otimes>h)\<otimes>h = (deriv f \<alpha>)\<otimes>h \<oplus> (c \<otimes>(h[^](2::nat)))"
      using nat_pow_def[of Zp h "2"]
      by (simp add: h_fact)
    then show ?thesis
      using 2 
      by simp
  qed
  have "h = \<zero>"
  proof(rule ccontr)
    assume "h \<noteq> \<zero>"
    then have "(deriv f \<alpha>) \<oplus> c \<otimes>h = \<zero>"
      using 2 3 
      by (meson R.m_closed assms(1) assms(7) c_def deriv_closed h_fact local.integral sum_closed)      
    then have "(deriv f \<alpha>) = \<ominus> c \<otimes>h"
      by (simp add: R.l_minus R.sum_zero_eq_neg UP_cring.deriv_closed Zp_x_is_UP_cring assms(1) assms(7) c_def h_fact)      
    then have "val_Zp (deriv f \<alpha>) = val_Zp (c \<otimes> h)"
      by (meson R.m_closed \<open>deriv f \<alpha> \<oplus> c \<otimes> h = \<zero>\<close> assms(1) assms(7) c_def deriv_closed h_fact val_Zp_not_equal_imp_notequal(3))      
    then have P: "val_Zp (deriv f \<alpha>) = val_Zp h + val_Zp c"
      using val_Zp_mult c_def h_fact by force
    hence "val_Zp (deriv f \<alpha>) \<ge> val_Zp h "
      using val_pos[of c] 
      by (simp add: c_def)
    then have "val_Zp (deriv f \<alpha>) \<ge> val_Zp (\<beta> \<ominus> \<alpha>) "
      using h_def by blast
    then have "val_Zp (deriv f \<alpha>) > val_Zp ((pderiv f)\<bullet>a)"
      using "0" by auto     
    then show False using pderiv_eval_deriv[of f \<alpha>]  
      using assms(1) assms(12) assms(7) by auto
  qed
  then show "\<alpha> = \<beta>"
    using assms(10) assms(7) h_def 
    by auto
qed

lemma hensels_lemma':
  assumes "f \<in> carrier Zp_x"
  assumes "a \<in> carrier Zp"
  assumes "val_Zp (f\<bullet>a) > 2*val_Zp ((pderiv f)\<bullet>a)"
  shows "\<exists>!\<alpha> \<in> carrier Zp. f\<bullet>\<alpha> = \<zero> \<and> val_Zp (a \<ominus> \<alpha>) > val_Zp ((pderiv f)\<bullet>a)"
proof(cases "f\<bullet>a = \<zero>")
  case True
  have T0: "pderiv f \<bullet> a \<noteq> \<zero>"
    apply(rule ccontr) using assms(3) 
    unfolding val_Zp_def by simp                  
  then have T1: "a \<in> carrier Zp \<and> f\<bullet>a = \<zero> \<and> val_Zp (a \<ominus> a) > val_Zp ((pderiv f)\<bullet>a)"
    using assms True  
    by(simp add: val_Zp_def)  
  have T2: "\<And>b. b \<in> carrier Zp \<and> f\<bullet>b = \<zero> \<and> val_Zp (a \<ominus> b) > val_Zp ((pderiv f)\<bullet>a) \<Longrightarrow> a = b"
  proof- fix b assume A: "b \<in> carrier Zp \<and> f\<bullet>b = \<zero> \<and> val_Zp (a \<ominus> b) > val_Zp ((pderiv f)\<bullet>a)"
    obtain h where h_def: "h = b \<ominus> a"
      by blast 
    then have h_fact: "h \<in> carrier Zp \<and> b = a \<oplus> h"
      by (metis A R.l_neg R.minus_closed R.minus_eq R.r_zero add_assoc add_comm assms(2))        
    then have 1: "f\<bullet>(a \<oplus> h) = \<zero>"
      using assms A by blast   
    obtain c where c_def: "c \<in> carrier Zp \<and> f\<bullet>(a \<oplus> h) = (f \<bullet> a) \<oplus> (deriv f a)\<otimes>h \<oplus> c \<otimes>(h[^](2::nat))"
      using taylor_deg_1_eval'[of  f a h _ "f \<bullet> a" "deriv f a" ]
      by (meson taylor_closed assms(1) assms(2) to_fun_closed h_fact shift_closed)       
    then have  "(f \<bullet> a) \<oplus> (deriv f a)\<otimes>h \<oplus> c \<otimes>(h[^](2::nat)) = \<zero>"
      by (simp add: "1")
    then have 2:  "(deriv f a)\<otimes>h \<oplus> c \<otimes>(h[^](2::nat)) = \<zero>"
      by (simp add: True assms(1) assms(2) deriv_closed h_fact)   
    hence 3: "((deriv f a) \<oplus> c \<otimes>h)\<otimes>h = \<zero>"      
    proof-
      have "((deriv f a) \<oplus> c \<otimes>h)\<otimes>h = ((deriv f a)\<otimes>h \<oplus> (c \<otimes>h)\<otimes>h)"
        by (simp add: R.l_distr assms(1) assms(2) c_def deriv_closed h_fact)        
      then have "((deriv f a) \<oplus> c \<otimes>h)\<otimes>h = (deriv f a)\<otimes>h \<oplus> (c \<otimes>(h\<otimes>h))"
        by (simp add: mult_assoc)      
      then have "((deriv f a) \<oplus> c \<otimes>h)\<otimes>h = (deriv f a)\<otimes>h \<oplus> (c \<otimes>(h[^](2::nat)))"
        using nat_pow_def[of Zp h "2"]
        by (simp add: h_fact)
      then show ?thesis
        using 2 
        by simp
    qed
    have "h = \<zero>"
    proof(rule ccontr)
      assume "h \<noteq> \<zero>"
      then have "(deriv f a) \<oplus> c \<otimes>h = \<zero>"
        using 2 3 
        by (meson R.m_closed UP_cring.deriv_closed Zp_x_is_UP_cring assms(1) assms(2) c_def h_fact local.integral sum_closed)              
      then have "(deriv f a) = \<ominus> c \<otimes>h"
        using R.l_minus R.minus_equality assms(1) assms(2) c_def deriv_closed h_fact by auto               
      then have "val_Zp (deriv f a) = val_Zp (c \<otimes> h)"
        by (meson R.m_closed \<open>deriv f a \<oplus> c \<otimes> h = \<zero>\<close> assms(1) assms(2) c_def deriv_closed h_fact val_Zp_not_equal_imp_notequal(3))            
      then have P: "val_Zp (deriv f a) = val_Zp h +  val_Zp c"
        by (simp add: c_def h_fact val_Zp_mult)
      have "val_Zp (deriv f a) \<ge> val_Zp h "
        using P val_pos[of c] c_def  
        by simp
      then have "val_Zp (deriv f a) \<ge> val_Zp (b \<ominus> a) "
        using h_def by blast
      then have "val_Zp (deriv f a) > val_Zp ((pderiv f)\<bullet>a)"
        by (metis (no_types, lifting) A assms(2) h_def h_fact minus_a_inv not_less order_trans val_Zp_of_minus)
      then have P0:"val_Zp (deriv f a) > val_Zp (deriv f a)"
        by (metis UP_cring.pderiv_eval_deriv Zp_x_is_UP_cring assms(1) assms(2))     
      thus False by auto 
    qed
    then show "a = b"
      by (simp add: assms(2) h_fact)
  qed
  show ?thesis 
    using T1 T2 
    by blast  
next
  case False
  have F0: "pderiv f \<bullet> a \<noteq> \<zero>"
    apply(rule ccontr) using assms(3) 
    unfolding val_Zp_def by simp
  obtain \<alpha> where alpha_def:
       "f\<bullet>\<alpha> = \<zero>"  "\<alpha> \<in> carrier Zp" 
       "val_Zp (a \<ominus> \<alpha>) > val_Zp ((pderiv f)\<bullet>a)"
       "(val_Zp (a \<ominus> \<alpha>) = val_Zp (divide (f\<bullet>a) ((pderiv f)\<bullet>a)))"
       "val_Zp ((pderiv f)\<bullet>\<alpha>) = val_Zp ((pderiv f)\<bullet>a)"
    using assms hensels_lemma F0 False by blast    
  have 0: "\<And>x. x \<in> carrier Zp \<and> f \<bullet> x = \<zero> \<and> val_Zp (a \<ominus> x) > val_Zp (pderiv f \<bullet> a) \<and> val_Zp (pderiv f \<bullet> a) \<noteq> val_Zp (a \<ominus> x) \<Longrightarrow> x= \<alpha>"
    using alpha_def assms hensels_lemma_unique_root[of f a \<alpha>] F0 False by blast     
  have 1: "\<alpha> \<in> carrier Zp \<and> f \<bullet> \<alpha> = \<zero> \<and> val_Zp (a \<ominus> \<alpha>) > val_Zp (pderiv f \<bullet> a) \<and> val_Zp (pderiv f \<bullet> a) \<noteq> val_Zp (a \<ominus> \<alpha>)"
    using alpha_def order_less_le by blast    
  thus ?thesis 
    using 0  
    by (metis (no_types, hide_lams) R.minus_closed alpha_def(1-3) assms(2) equal_val_Zp val_Zp_ultrametric_eq')
qed

(**************************************************************************************************)
(**************************************************************************************************)
section\<open>Some Applications of Hensel's Lemma to Root Finding for Polynomials over $\mathbb{Z}_p$\<close>
(**************************************************************************************************)
(**************************************************************************************************)

lemma Zp_square_root_criterion:
  assumes "p \<noteq> 2"
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "val_Zp b \<ge> val_Zp a"
  assumes "a \<noteq> \<zero>"
  assumes "b \<noteq> \<zero>"
  shows "\<exists>y \<in> carrier Zp. a[^](2::nat) \<oplus> \<p>\<otimes>b[^](2::nat) = (y [^]\<^bsub>Zp\<^esub> (2::nat))"
proof-
  have bounds: "val_Zp a < \<infinity>" "val_Zp a \<ge> 0" "val_Zp b < \<infinity>" "val_Zp b \<ge> 0"
    using assms(2) assms(3) assms(6) assms(5) val_Zp_def val_pos[of b]  val_pos[of a] 
    by auto     
  obtain f where f_def: "f = monom Zp_x \<one> 2  \<oplus>\<^bsub>Zp_x\<^esub> to_polynomial Zp (\<ominus> (a[^](2::nat)\<oplus> \<p>\<otimes>b[^](2::nat)))"
    by simp
  have "\<exists> \<alpha>. f\<bullet>\<alpha> = \<zero> \<and> \<alpha> \<in> carrier Zp"
  proof-
    have 0: "f \<in> carrier Zp_x"
      using f_def 
      by (simp add: X_closed assms(2) assms(3) to_poly_closed)       
    have 1: "(pderiv f)\<bullet>a = [(2::nat)] \<cdot> \<one> \<otimes> a"
    proof-
      have "pderiv f = pderiv (monom Zp_x \<one> 2)"
        using assms f_def pderiv_add[of "monom Zp_x \<one> 2"] to_poly_closed R.nat_pow_closed 
              pderiv_deg_0
        unfolding to_polynomial_def 
        using P.nat_pow_closed P.r_zero R.add.inv_closed X_closed Zp_int_inc_closed deg_const monom_term_car pderiv_closed sum_closed
        by (metis (no_types, lifting) R.one_closed monom_closed)                                                                                                            
      then have 20: "pderiv f = monom (Zp_x) ([(2::nat) ] \<cdot> \<one>) (1::nat)"
        using pderiv_monom[of \<one> 2] 
        by simp
      have 21: "[(2::nat)] \<cdot> \<one> \<noteq> \<zero>"
        using Zp_char_0'[of 2] by simp 
      have 22: "(pderiv f)\<bullet>a = [(2::nat)] \<cdot> \<one> \<otimes> (a[^]((1::nat)))"
        using 20 
        by (simp add: Zp_nat_inc_closed assms(2) to_fun_monom)        
      then show ?thesis
        using assms(2) 
        by (simp add: cring.cring_simprules(12))       
    qed
    have 2: "(pderiv f)\<bullet>a \<noteq> \<zero>"
      using 1 assms 
      by (metis Zp_char_0' Zp_nat_inc_closed local.integral zero_less_numeral)
    have 3: "f\<bullet>a = \<ominus> (\<p>\<otimes>b[^](2::nat))"
    proof-
      have 3: "f\<bullet>a =
    monom (UP Zp) \<one> 2 \<bullet> a \<oplus>
    to_polynomial Zp (\<ominus> (a [^] (2::nat) \<oplus> [p] \<cdot> \<one> \<otimes> b [^] (2::nat)))\<bullet>a"
        unfolding f_def apply(rule to_fun_plus)
          apply (simp add: assms(2) assms(3) to_poly_closed)
         apply simp
        by (simp add: assms(2))
      have 30: "f\<bullet>a = a[^](2::nat)  \<ominus> (a[^](2::nat) \<oplus> \<p>\<otimes>b[^](2::nat))"
        unfolding 3  by (simp add: R.minus_eq assms(2) assms(3) to_fun_monic_monom to_fun_to_poly)
      have 31: "f\<bullet>a = a[^](2::nat)  \<ominus> a[^](2::nat) \<ominus> (\<p>\<otimes>b[^](2::nat))"
      proof-
        have 310: "a[^](2::nat) \<in> carrier Zp"
          using assms(2) pow_closed 
          by blast
        have 311: "\<p>\<otimes>(b[^](2::nat)) \<in> carrier Zp"
          by (simp add: assms(3) monom_term_car)
        have   "\<ominus> (a [^] (2::nat)\<oplus>(\<p> \<otimes> b [^] (2::nat))) = \<ominus> (a [^] (2::nat)) \<oplus> \<ominus> (\<p> \<otimes> (b [^] (2::nat)))"
          using 310 311 R.minus_add by blast                  
        then show ?thesis  
          by (simp add: "30" R.minus_eq add_assoc)                                                  
      qed
      have 32: "f\<bullet>a = (a[^](2::nat)  \<ominus> a[^](2::nat)) \<ominus> (\<p>\<otimes>b[^](2::nat))"
        using 31 unfolding a_minus_def 
        by blast
      have 33: "\<p>\<otimes>b[^](2::nat) \<in> carrier Zp"
        by (simp add: Zp_nat_inc_closed assms(3) monom_term_car)
      have 34: "a[^](2::nat) \<in> carrier Zp"
        using assms(2) pow_closed by blast
      then have 34: "(a[^](2::nat)  \<ominus> a[^](2::nat)) = \<zero> "
        by simp        
      have 35: "f\<bullet>a = \<zero> \<ominus> (\<p>\<otimes>b[^](2::nat))"
        by (simp add: "32" "34")                
      then show ?thesis 
        using 33 unfolding a_minus_def   
        by (simp add: cring.cring_simprules(3))
    qed
    have 4: "f\<bullet>a \<noteq>\<zero>"
      using 3 assms  
      by (metis R.add.inv_eq_1_iff R.m_closed R.nat_pow_closed Zp.integral Zp_int_inc_closed
          mult_zero_r nonzero_pow_nonzero p_natpow_prod_Suc(1) p_pow_nonzero(2))                                                
    have 5: "val_Zp (f\<bullet>a) = 1 + 2*val_Zp b"
    proof-
      have "val_Zp (f\<bullet>a) = val_Zp (\<p>\<otimes>b[^](2::nat))"
        using 3 Zp_int_inc_closed assms(3) monom_term_car val_Zp_of_minus by presburger               
      then have "val_Zp (\<p>\<otimes>b[^](2::nat)) = 1 + val_Zp (b[^](2::nat))"
        by (simp add: assms(3) val_Zp_mult val_Zp_p)                
      then show ?thesis 
        using assms(3) assms(6) 
        using Zp_def \<open>val_Zp (to_fun f a) = val_Zp ([p] \<cdot> \<one> \<otimes> b [^] 2)\<close> not_nonzero_Zp
          padic_integers_axioms val_Zp_pow' by fastforce                           
    qed
    have 6: "val_Zp ((pderiv f)\<bullet>a) = val_Zp a"
    proof-
      have 60: "val_Zp ([(2::nat)] \<cdot> \<one> \<otimes> a) = val_Zp ([(2::nat)] \<cdot> \<one>) + val_Zp a"
        by (simp add: Zp_char_0' assms(2) assms(5) val_Zp_mult ord_of_nonzero(2) ord_pos)
      have "val_Zp ([(2::nat)] \<cdot> \<one>) = 0"
      proof-
        have "(2::nat) < p"
          using prime assms prime_ge_2_int by auto          
        then have "(2::nat) mod p = (2::nat)"
          by simp
        then show ?thesis 
          by (simp add: val_Zp_p_nat_unit)          
      qed
      then show ?thesis 
        by (simp add: "1" "60")        
    qed
    then have 7: "val_Zp (f\<bullet>a) > 2* val_Zp ((pderiv f)\<bullet>a)"
      using bounds 5 assms(4) 
      by (simp add: assms(5) assms(6) one_eint_def val_Zp_def)
    obtain \<alpha> where
       A0: "f\<bullet>\<alpha> = \<zero>"  "\<alpha> \<in> carrier Zp"       
      using hensels_lemma[of f a] "0" "2" "4" "7" assms(2) 
      by blast
    show ?thesis 
      using A0  by blast   
  qed
  then obtain \<alpha> where \<alpha>_def: "f\<bullet>\<alpha> = \<zero> \<and> \<alpha> \<in> carrier Zp"
    by blast 
  have "f\<bullet>\<alpha> = \<alpha> [^](2::nat)  \<ominus> (a[^](2::nat)\<oplus> \<p>\<otimes>b[^](2::nat))" 
  proof- 
    have 0: "f\<bullet>\<alpha> =
    monom (UP Zp) \<one> 2 \<bullet> \<alpha> \<oplus>
    to_polynomial Zp (\<ominus> (a [^] (2::nat) \<oplus> [p] \<cdot> \<one> \<otimes> b [^] (2::nat)))\<bullet>\<alpha>"
        unfolding f_def apply(rule to_fun_plus)
          apply (simp add: assms(2) assms(3) to_poly_closed)
         apply simp
        by (simp add: \<alpha>_def)
    thus ?thesis 
      by (simp add: R.minus_eq \<alpha>_def assms(2) assms(3) to_fun_monic_monom to_fun_to_poly)
  qed
  then show ?thesis 
    by (metis R.r_right_minus_eq Zp_int_inc_closed \<alpha>_def assms(2) assms(3) monom_term_car pow_closed sum_closed)        
qed

lemma Zp_semialg_eq:
  assumes "a \<in> nonzero Zp"
  shows "\<exists>y \<in> carrier Zp. \<one> \<oplus> (\<p> [^] (3::nat))\<otimes> (a [^] (4::nat)) = (y [^] (2::nat))"
proof-
  obtain f where f_def: "f = monom Zp_x \<one> 2 \<oplus>\<^bsub>Zp_x\<^esub> to_poly (\<ominus> (\<one> \<oplus> (\<p> [^] (3::nat))\<otimes> (a [^] (4::nat))))"
    by simp
  have a_car: "a \<in> carrier Zp"
    by (simp add: nonzero_memE assms)
  have "f \<in> carrier Zp_x"
    using f_def 
    by (simp add: a_car to_poly_closed)             
  hence 0:"f\<bullet>\<one> = \<one> \<ominus> (\<one> \<oplus> (\<p> [^] (3::nat))\<otimes> (a [^] (4::nat)))"
    using f_def 
    by (simp add: R.minus_eq assms nat_pow_nonzero nonzero_mult_in_car p_pow_nonzero' to_fun_monom_plus to_fun_to_poly to_poly_closed)
  then have 1: "f\<bullet>\<one> = \<ominus> (\<p> [^] (3::nat))\<otimes> (a [^] (4::nat))"
    unfolding a_minus_def 
    by (smt R.add.inv_closed R.l_minus R.minus_add R.minus_minus R.nat_pow_closed R.one_closed R.r_neg1 a_car monom_term_car p_pow_nonzero(1))
  then have "val_Zp (f\<bullet>\<one>) = 3 + val_Zp (a [^] (4::nat))"
    using  assms val_Zp_mult[of "\<p> [^] (3::nat)" "(a [^] (4::nat))" ] 
      val_Zp_p_pow p_pow_nonzero[of "3::nat"] val_Zp_of_minus  
    by (metis R.l_minus R.nat_pow_closed a_car monom_term_car of_nat_numeral)
  then have 2: "val_Zp (f\<bullet>\<one>) = 3 + 4* val_Zp a"
    using assms val_Zp_pow' by auto
  have "pderiv f = pderiv (monom Zp_x \<one> 2)"
    using assms f_def pderiv_add[of "monom Zp_x \<one> 2"] to_poly_closed R.nat_pow_closed  pderiv_deg_0
    unfolding to_polynomial_def 
    by (metis (no_types, lifting) P.r_zero R.add.inv_closed R.add.m_closed R.one_closed 
        UP_zero_closed a_car deg_const deg_nzero_nzero monom_closed monom_term_car p_pow_nonzero(1))
  then have 3: "pderiv f = [(2::nat)] \<cdot> \<one> \<odot>\<^bsub>Zp_x\<^esub> X "
    by (metis P.nat_pow_eone R.one_closed Suc_1 X_closed diff_Suc_1 monom_rep_X_pow pderiv_monom')
  hence 4: "val_Zp ((pderiv f)\<bullet>\<one>) = val_Zp ([(2::nat)] \<cdot> \<one> )"
    by (metis R.add.nat_pow_eone R.nat_inc_prod R.nat_inc_prod' R.nat_pow_one R.one_closed 
        Zp_nat_inc_closed \<open>pderiv f = pderiv (monom Zp_x \<one> 2)\<close> pderiv_monom to_fun_monom)
  have "(2::int) = (int (2::nat))"
    by simp
  then  have 5: "[(2::nat)] \<cdot> \<one> = ([(int (2::nat))] \<cdot> \<one> )"
     using add_pow_def int_pow_int 
     by metis     
  have 6: "val_Zp ((pderiv f)\<bullet>\<one>) \<le> 1" 
    apply(cases "p = 2") 
    using "4" "5" val_Zp_p apply auto[1]
  proof-
    assume "p \<noteq> 2"
    then have 60: "coprime 2 p"
      using prime prime_int_numeral_eq primes_coprime two_is_prime_nat by blast    
    have 61: "2 < p"
      using 60 prime 
      by (smt \<open>p \<noteq> 2\<close> prime_gt_1_int)
    then show ?thesis 
      by (smt "4" "5" \<open>2 = int 2\<close> mod_pos_pos_trivial nonzero_closed p_nonzero val_Zp_p val_Zp_p_int_unit val_pos)
  qed
  have 7: "val_Zp (f\<bullet>\<one>) \<ge> 3"
  proof-
    have "eint 4 * val_Zp a \<ge> 0"
      using 2 val_pos[of a] 
      by (metis R.nat_pow_closed a_car assms of_nat_numeral val_Zp_pow' val_pos)
    thus ?thesis 
      using "2" by auto
  qed
  have "2*val_Zp ((pderiv f)\<bullet>\<one>) \<le> 2*1"
    using 6 one_eint_def eint_mult_mono' 
    by (smt \<open>2 = int 2\<close> eint.distinct(2) eint_ile eint_ord_simps(1) eint_ord_simps(2) mult.commute 
        ord_Zp_p ord_Zp_p_pow ord_Zp_pow p_nonzero p_pow_nonzero(1) times_eint_simps(1) val_Zp_p val_Zp_pow' val_pos)
  hence 8: "2 * val_Zp ((pderiv f)\<bullet> \<one>) < val_Zp (f\<bullet>\<one>)"
    using 7 le_less_trans[of "2 * val_Zp ((pderiv f)\<bullet> \<one>)" "2::eint" 3] 
            less_le_trans[of "2 * val_Zp ((pderiv f)\<bullet> \<one>)" 3 "val_Zp (f\<bullet>\<one>)"] one_eint_def
    by auto
  obtain \<alpha> where  \<alpha>_def: "f\<bullet>\<alpha> = \<zero>" and  \<alpha>_def' :"\<alpha> \<in> carrier Zp"
    using 2 6 7 hensels_lemma' 8 \<open>f \<in> carrier Zp_x\<close>  by blast
  have 0: "(monom Zp_x \<one> 2) \<bullet> \<alpha> = \<alpha> [^] (2::nat)"
    by (simp add: \<alpha>_def' to_fun_monic_monom)          
  have 1: "to_poly (\<ominus> (\<one> \<oplus> (\<p> [^] (3::nat))\<otimes> (a [^] (4::nat)))) \<bullet> \<alpha> =\<ominus>( \<one> \<oplus> (\<p> [^] (3::nat))\<otimes> (a [^] (4::nat)))"
    by (simp add: \<alpha>_def' a_car to_fun_to_poly)  
  then have "\<alpha> [^] (2::nat) \<ominus> (\<one> \<oplus> (\<p> [^] (3::nat))\<otimes> (a [^] (4::nat))) = \<zero>"
    using \<alpha>_def \<alpha>_def' 
    by (simp add: R.minus_eq a_car f_def to_fun_monom_plus to_poly_closed)    
  then show ?thesis 
    by (metis R.add.m_closed R.nat_pow_closed R.one_closed R.r_right_minus_eq \<alpha>_def' a_car monom_term_car p_pow_nonzero(1))   
qed

lemma Zp_nth_root_lemma:
  assumes "a \<in> carrier Zp"
  assumes "a \<noteq> \<one>"
  assumes "n > 1"
  assumes "val_Zp (\<one> \<ominus> a) > 2*val_Zp ([(n::nat)]\<cdot> \<one>)"
  shows "\<exists> b \<in> carrier Zp. b[^]n = a"
proof-
  obtain f where f_def: "f = monom Zp_x \<one> n \<oplus>\<^bsub>Zp_x\<^esub> monom Zp_x (\<ominus>a) 0"
    by simp
  have "f \<in> carrier Zp_x"
    using f_def monom_closed assms 
    by simp
  have 0: "pderiv f = monom Zp_x ([n]\<cdot> \<one>) (n-1)"
    by (simp add: assms(1) f_def pderiv_add pderiv_monom)    
  have 1: "f \<bullet> \<one> = \<one> \<ominus> a"
    using f_def 
    by (metis R.add.inv_closed R.minus_eq R.nat_pow_one R.one_closed assms(1) to_fun_const to_fun_monom to_fun_monom_plus monom_closed)
  have 2: "(pderiv f) \<bullet> \<one> = ([n]\<cdot> \<one>)"
    using 0 to_fun_monom assms 
    by simp
  have 3: "val_Zp (f \<bullet> \<one>) > 2* val_Zp ((pderiv f) \<bullet> \<one>)"
    using 1 2 assms 
    by (simp add: val_Zp_def)
  have 4: "f \<bullet> \<one> \<noteq> \<zero>"
    using 1 assms(1) assms(2) by auto
  have 5: "(pderiv f) \<bullet> \<one> \<noteq> \<zero>"
    using "2" Zp_char_0' assms(3) by auto
  obtain \<beta> where beta_def: "\<beta> \<in> carrier Zp \<and> f \<bullet> \<beta> = \<zero>"
    using hensels_lemma[of f \<one>]
    by (metis "3" "5" R.one_closed \<open>f \<in> carrier Zp_x\<close>)
  then have "(\<beta> [^] n) \<ominus> a = \<zero>"
    using f_def R.add.inv_closed  assms(1) to_fun_const[of "\<ominus> a"] to_fun_monic_monom[of \<beta> n] to_fun_plus monom_closed
    unfolding a_minus_def 
    by (simp add: beta_def)
  then have "\<beta> \<in> carrier Zp \<and> \<beta> [^] n = a"
    using beta_def nonzero_memE  not_eq_diff_nonzero assms(1) pow_closed 
    by blast
  then show ?thesis by blast 
qed
    
end
end 
