theory Padic_Int_Topology
imports Padic_Integers Function_Ring
begin

type_synonym padic_int_seq = "nat \<Rightarrow> padic_int"

type_synonym padic_int_fun = "padic_int \<Rightarrow> padic_int"

sublocale padic_integers < FunZp?: U_function_ring "Zp"
  unfolding U_function_ring_def 
  by (simp add: R.ring_axioms)

context padic_integers
begin

(**************************************************************************************************)
(**************************************************************************************************)
(***********************************)section\<open>Sequences over Zp\<close>(***********************************)
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  The $p$-adic valuation can be thought of as equivalent to the $p$-adic absolute value, but with
  the notion of size inverted so that small numbers have large valuation, and zero has maximally 
  large valuation. The $p$-adic distance between two points is just the valuation of the difference
  of those points, and is thus equivalent to the metric induced by the $p$-adic absolute value. 
  For background on valuations and absolute values for $p$-adic rings see \cite{engler2005valued}.
  In what follows, we develop the topology of the $p$-adic from a valuative perspective rather than 
  a metric perspective. Though equivalent to the metric approach in the $p$-adic case, this
  approach is more general in that there exist valued rings whose valuations take values in
  non-Archimedean ordered ablelian groups which do not embed into the real numbers.
\<close>

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>The Valuative Distance Function on $\mathbb{Z}_p$\<close>
  (**********************************************************************)
  (**********************************************************************)

text\<open>
  The following lemmas establish that the $p$-adic distance function satifies the standard
  properties of an ultrametric. It is symmetric, obeys the ultrametric inequality, and only
  identical elements are infinitely close.
\<close>

definition val_Zp_dist :: "padic_int \<Rightarrow> padic_int \<Rightarrow> eint" where
"val_Zp_dist a b \<equiv> val_Zp (a \<ominus> b)"

lemma val_Zp_dist_sym:
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  shows "val_Zp_dist a b = val_Zp_dist b a"
proof-   
  have 1: "a \<ominus> b = \<ominus> (b \<ominus> a)" using assms(1) assms(2)  
    using minus_a_inv by blast      
  then show ?thesis 
    using R.minus_closed Zp_def assms(1) assms(2) padic_integers.val_Zp_of_minus 
      padic_integers_axioms val_Zp_dist_def by auto   
qed

lemma val_Zp_dist_ultrametric:
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "c \<in> carrier Zp"
  shows "val_Zp_dist b c \<ge> min (val_Zp_dist a c) (val_Zp_dist a b)" 
proof-
  let ?X = "b \<ominus> a"
  let ?Y = "a \<ominus> c"
  let ?Z = "b \<ominus> c"
  have 0: "?Z = ?X \<oplus> ?Y" 
    using R.add.m_comm assms(1) assms(2) assms(3) R.plus_diff_simp by auto
  have 4: "val_Zp ?Z \<ge> min (val_Zp ?X) (val_Zp ?Y)" 
    using "0" assms(1) assms(2) assms(3) val_Zp_ultrametric by auto
  then show ?thesis 
    using  assms val_Zp_dist_sym 
    unfolding  val_Zp_dist_def
    by (simp add: min.commute)    
qed

lemma val_Zp_dist_infty:
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "val_Zp_dist a b = \<infinity>"
  shows "a = b"
  using assms unfolding val_Zp_dist_def 
  by (metis R.r_right_minus_eq not_eint_eq val_ord_Zp) 

lemma val_Zp_dist_infty':
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "a = b"
  shows "val_Zp_dist a b = \<infinity>"
  using assms unfolding val_Zp_dist_def 
  by (simp add: val_Zp_def) 

text\<open>
  The following property will be useful in the proof of Hensel's Lemma: two $p$-adic integers are
  close together if and only if their residues are equal at high orders.
\<close>

lemma val_Zp_dist_res_eq:
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "val_Zp_dist a b > k"
  shows "(a k) = (b k)" 
  using  assms(1) assms(2) assms(3) val_Zp_dist_def
  by (simp add: Zp_residue_eq)  

lemma val_Zp_dist_res_eq2:
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "(a k) = (b k)" 
  shows "val_Zp_dist a b \<ge> k"
  using assms(1) assms(2) assms(3) Zp_residue_eq2
  unfolding val_Zp_dist_def
  by (simp add: val_Zp_def)

lemma val_Zp_dist_triangle_eqs:
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "c \<in> carrier Zp"
  assumes "val_Zp_dist a b > n"
  assumes "val_Zp_dist a c > n"
  assumes "(k::nat) < n"
  shows "a k = b k"
        "a k = c k"
        "b k = c k" 
  unfolding val_Zp_dist_def 
proof-
  show 0: "a k = b k"
    using assms(1) assms(2) assms(4) assms(6) val_Zp_dist_res_eq
    by (metis less_imp_le_nat p_residue_padic_int)   
  show 1: "a k = c k"
    using assms(1) assms(3) assms(5) assms(6) val_Zp_dist_res_eq 
    by (meson eint_ord_simps(1) le_less_trans less_imp_triv not_less of_nat_le_iff)   
  show "b k = c k"
    using 0 1 by auto 
qed

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>Cauchy Sequences\<close>
  (**********************************************************************)
  (**********************************************************************)

text\<open>
  The definition of Cauchy sequence here is equivalent to standard the metric notion, and is
  identical to the one found on page 50 of \cite{engler2005valued}.
\<close>

lemma closed_seqs_diff_closed:
  assumes "s \<in> closed_seqs Zp"
  assumes "a \<in> carrier Zp"
  shows "s m \<ominus> a \<in> carrier Zp"
  using assms 
  by (simp add: closed_seqs_memE)  

definition is_Zp_cauchy :: "padic_int_seq \<Rightarrow> bool" where
"is_Zp_cauchy s = ((s \<in> closed_seqs Zp) \<and> (\<forall> (n::int). \<exists> (N::nat). \<forall> m k::nat. 

                  (m>N \<and> k>N \<longrightarrow> (val_Zp_dist (s m) (s k)) > eint n)))"

text\<open>Relation for a sequence which converges to a point:\<close>

definition Zp_converges_to :: "padic_int_seq \<Rightarrow> padic_int \<Rightarrow> bool" where
          "Zp_converges_to s a = ((a \<in> carrier Zp \<and> s \<in> closed_seqs Zp)  
                              \<and> (\<forall>(n::int). (\<exists>(k:: nat). (\<forall>( m::nat).
                                (m > k \<longrightarrow> (val_Zp ((s m) \<ominus> a)) > eint n) ))))"

lemma is_Zp_cauchy_imp_closed:
  assumes "is_Zp_cauchy s"
  shows "s \<in> closed_seqs Zp"
  using assms unfolding is_Zp_cauchy_def by blast 

text\<open>
  Analogous to the lemmas about residues and $p$-adic distances, we can characterize Cauchy 
  sequences without reference to a distance function: a sequence is Cauchy if and only if for 
  every natural number $k$, the $k^{th}$ residues of the elements in the sequence are eventually
  all equal.
\<close>

lemma is_Zp_cauchy_imp_res_eventually_const_0:
  assumes "is_Zp_cauchy s"
  fixes n::nat
  obtains N where "\<And> n0 n1. n0 > N \<and> n1 > N \<Longrightarrow> (s n0) n = (s n1) n"
proof-
  have "\<exists> (N::nat). \<forall> m k::nat. (m>N \<and> k>N \<longrightarrow> (val_Zp_dist (s m) (s k)) > (int n))"
    using assms is_Zp_cauchy_def by blast 
  then obtain N where P0: " \<forall> m k::nat. (m>N \<and> k>N \<longrightarrow> (val_Zp_dist (s m) (s k)) > (int n))"
    by blast 
  have P1: "\<And> n0 n1. n0 > N \<and> n1 > N \<Longrightarrow> (s n0) n = (s n1) n"
  proof-
    fix n0 n1
    assume A: "n0 > N \<and> n1 > N"
    have "(n0>N \<and> n1>N \<longrightarrow> (val_Zp_dist (s n0) (s n1)) > (int n))" 
      using P0 by blast
    then have C0: "(val_Zp_dist (s n0) (s n1)) > (int n)" 
      using A  by blast
    show "(s n0) n = (s n1) n"
    proof-
      have A0: "(val_Zp_dist (s n0) (s n1)) > (int n)" 
        using C0 by blast
      have A1: "s n0 \<in> carrier Zp" 
        using is_Zp_cauchy_imp_closed[of s] assms 
        by (simp add: closed_seqs_memE)                      
      have A2: "s n1 \<in> carrier Zp" 
        using is_Zp_cauchy_def assms closed_seqs_memE[of _ Zp] 
        by blast
      show ?thesis 
        using A0 val_Zp_dist_res_eq  A1 A2 by metis 
    qed
  qed
  then show ?thesis 
    using that by blast
qed

lemma is_Zp_cauchyI:
  assumes "s \<in> closed_seqs Zp"
  assumes "\<And> n.  (\<exists>N. (\<forall> n0 n1. n0 > N \<and> n1 > N \<longrightarrow> (s n0) n = (s n1) n))"
  shows "is_Zp_cauchy s"
proof-
  have "(\<forall> (n::int). \<exists> (N::nat). \<forall> m k::nat. (m>N \<and> k>N \<longrightarrow> (val_Zp_dist (s m) (s k)) > n))"
  proof
    fix n
    show "\<exists> (N::nat). \<forall> m k::nat. (m>N \<and> k>N \<longrightarrow> (val_Zp_dist (s m) (s k)) > eint n)"
    proof-
      have "(\<exists>N. (\<forall> n0 n1. n0 > N \<and> n1 > N \<longrightarrow> (s n0) (Suc (nat n)) = (s n1) (Suc (nat n))))" 
        using assms(2) by blast
      then obtain N where N_def: "(\<forall> n0 n1. n0 > N \<and> n1 > N \<longrightarrow> (s n0) (Suc (nat n)) = (s n1) (Suc (nat n)))"
        by blast 
      have 0: "n \<le> eint (int (nat n))"
        by simp
      have "\<forall>m k. N < m \<and> N < k \<longrightarrow> (nat n) < val_Zp_dist (s m) (s k)"
      proof
      fix m
      show "\<forall>k. N < m \<and> N < k \<longrightarrow> int (nat n) < val_Zp_dist (s m) (s k)"
      proof
        fix k
        show "N < m \<and> N < k \<longrightarrow> int(nat n) < val_Zp_dist (s m) (s k)"
        proof
          assume A: "N < m \<and> N < k"
          then have E: "(s m) (Suc(nat n)) = (s k) (Suc(nat n))" 
            using N_def by blast 
          then show " int (nat n) < val_Zp_dist (s m) (s k)"
          proof-
            have 0: "(s m) \<in> carrier Zp"
              by (simp add: assms(1) closed_seqs_memE)           
            have 1: "(s k) \<in> carrier Zp" 
              using Zp_def assms(1) closed_seqs_memE[of _ Zp] padic_integers_axioms by blast
            have "int (Suc (nat n)) \<le> val_Zp_dist (s m) (s k)" 
              using   E 0 1 val_Zp_dist_res_eq[of "(s m)" "(s k)" "Suc (nat n)"] val_Zp_dist_res_eq2
              by blast
            then have "int (nat n) < val_Zp_dist (s m) (s k)" 
              by (metis Suc_ile_eq add.commute of_nat_Suc)            
            then show ?thesis 
              by blast
          qed
        qed
      qed
      qed
      hence "\<forall>m k. N < m \<and> N < k \<longrightarrow> n < val_Zp_dist (s m) (s k)"
      using 0 
      by (simp add: order_le_less_subst2)
      thus ?thesis by blast
    qed
  qed
  then show ?thesis 
    using is_Zp_cauchy_def assms  by blast
qed

lemma is_Zp_cauchy_imp_res_eventually_const:
  assumes "is_Zp_cauchy s"
  fixes n::nat
  obtains N r where "r \<in> carrier (Zp_res_ring n)" and "\<And> m. m > N \<Longrightarrow> (s m) n = r"
proof-
  obtain N where A0: "\<And> n0 n1. n0 > N \<and> n1 > N \<Longrightarrow> (s n0) n = (s n1) n"
    using assms is_Zp_cauchy_imp_res_eventually_const_0 padic_integers_axioms by blast
  obtain r where A1: "s (Suc N) n = r" 
    by simp
  have 0: "r \<in> carrier (Zp_res_ring n)" 
    using  Zp_def \<open>s (Suc N) n = r\<close> assms closed_seqs_memE[of _ Zp] 
      is_Zp_cauchy_def padic_integers_axioms residues_closed 
    by blast  
  have 1: "\<And> m. m > N \<Longrightarrow> (s m) n = r"
  proof-
    fix m 
    assume " m > N"
    then show "(s m) n = r" 
      using A0 A1  by blast
  qed
  then show ?thesis 
    using 0 1  that by blast
qed

text\<open>
  This function identifies the eventual residues of the elements of a cauchy sequence. 
  Since a $p$-adic integer is defined to be the map which identifies its residues, this map 
  will turn out to be precisely the limit of a cauchy sequence.
\<close>
definition res_lim :: "padic_int_seq \<Rightarrow> padic_int" where
"res_lim s = (\<lambda> k. (THE r. (\<exists>N.  (\<forall> m. m > N \<longrightarrow> (s m) k = r))))"

lemma res_lim_Zp_cauchy_0:
  assumes "is_Zp_cauchy s"
  assumes "f = (res_lim s) k"
  shows "(\<exists>N.  (\<forall> m. (m > N \<longrightarrow> (s m) k = f)))"
        "f \<in> carrier (Zp_res_ring k)"
proof-
  obtain N r where P0: "r \<in> carrier (Zp_res_ring k)" and P1: "\<And> m. m > N \<Longrightarrow> (s m) k = r"
    by (meson assms(1) is_Zp_cauchy_imp_res_eventually_const)
  obtain P where  P_def: "P = (\<lambda> x. (\<exists>N.  (\<forall> m. m > N \<longrightarrow> (s m) k = x)))"
    by simp
  have 0: "P r"
    using P1 P_def by auto
  have 1: "(\<And>x. P x \<Longrightarrow> x = r)"
  proof-
    fix x
    assume A_x: "P x"
    obtain N0 where "(\<forall> m. m > N0 \<longrightarrow> (s m) k = x)" 
      using A_x P_def by blast
    let ?M = "max N0 N" 
    have C0: "s (Suc ?M) k = x" 
      by (simp add: \<open>\<forall>m>N0. s m k = x\<close>)
    have C1: "s (Suc ?M) k = r" 
      by (simp add: P1)
    show "x = r" 
      using C0 C1 by auto 
  qed
  have R: "r = (THE x. P x)" 
    using the_equality 0 1 by metis
  have "(res_lim s) k = (THE r. \<exists>N. \<forall>m>N. s m k = r)" 
    using res_lim_def by simp
  then have "f = (THE r. \<exists>N. \<forall>m>N. s m k = r)" 
    using assms by auto 
  then have "f = (THE r. P r)" 
    using P_def by auto 
  then have "r = f"
    using R by auto  
  then show "(\<exists>N.  (\<forall> m. (m > N \<longrightarrow> (s m) k = f)))" using 0 P_def 
    by blast
  show "f \<in> carrier (Zp_res_ring k)" 
    using P0 \<open>r = f\<close> by auto
qed

lemma res_lim_Zp_cauchy:
  assumes "is_Zp_cauchy s"
  obtains N where "\<And> m.  (m > N \<longrightarrow> (s m) k = (res_lim s) k)"
  using res_lim_Zp_cauchy_0 assms by presburger

lemma res_lim_in_Zp:
  assumes "is_Zp_cauchy s"
  shows "res_lim s \<in> carrier Zp"
proof-
  have "res_lim s \<in> padic_set p"
  proof(rule padic_set_memI)
    show "\<And>m. res_lim s m \<in> carrier (residue_ring (p^ m))" 
      using res_lim_Zp_cauchy_0     by (simp add:  assms)
    show "\<And>m n. m < n \<Longrightarrow> residue (p^ m) (res_lim s n) = res_lim s m"
    proof-
      fix m n
      obtain N where  N0: "\<And> l.  (l > N \<longrightarrow> (s l) m = (res_lim s) m)"
        using assms res_lim_Zp_cauchy by blast
      obtain M where M0: "\<And> l.  (l > M \<longrightarrow> (s l) n = (res_lim s) n)"
        using assms prod.simps(2) res_lim_Zp_cauchy by auto
      obtain K where K_def: "K = max M N" 
        by simp
      have Km: "\<And> l.  (l > K \<longrightarrow> (s l) m = (res_lim s) m)" 
        using K_def N0  by simp
      have Kn: "\<And> l.  (l > K \<longrightarrow> (s l) n = (res_lim s) n)" 
        using K_def M0  by simp
      assume "m < n"
      show "residue (p^ m) (res_lim s n) = res_lim s m"
      proof-
        obtain l where l_def: "l = Suc K"
          by simp
        have ln: "(res_lim s n) = (s l) n" 
          by (simp add: Kn l_def)
        have lm: "(res_lim s m) = (s l) m"
          by (simp add: Km l_def)
        have s_car: "s l \<in> carrier Zp" 
          using assms is_Zp_cauchy_def closed_seqs_memE[of _ Zp] by blast
        then show ?thesis 
          using s_car lm ln \<open>m < n\<close> p_residue_def p_residue_padic_int by auto     
      qed
    qed
  qed
  then show ?thesis 
    by (simp add: Zp_def padic_int_simps(5))    
qed

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>Completeness of $\mathbb{Z}_p$\<close>
  (**********************************************************************)
  (**********************************************************************)

text\<open>
  We can use the developments above to show that a sequence of $p$-adic integers is convergent 
  if and only if it is cauchy, and that limits of convergent sequences are always unique.
\<close>

lemma is_Zp_cauchy_imp_has_limit:
  assumes "is_Zp_cauchy s"
  assumes "a = res_lim s"
  shows "Zp_converges_to s a"
proof-
  have 0: "(a \<in> carrier Zp \<and> s \<in> closed_seqs Zp)" 
    using assms(1) assms(2) is_Zp_cauchy_def res_lim_in_Zp by blast
  have 1: "(\<forall>(n::int). (\<exists>(k:: nat). (\<forall>( m::nat). 
            (m > k \<longrightarrow> (val_Zp ((s m) \<ominus> a)) \<ge> n))))"
  proof
    fix n
    show "\<exists>k. \<forall>m>k.  eint n \<le> val_Zp (s m \<ominus> a)"
    proof-
      obtain K where K_def: "\<And>m. (m > K \<longrightarrow> (s m) (nat n) = (res_lim s) (nat n))"
        using assms(1) res_lim_Zp_cauchy 
        by blast        
      have "\<forall>m>K.  n \<le> val_Zp_dist (s m) a"
      proof
        fix m
        show "K < m \<longrightarrow>  n \<le> val_Zp_dist (s m) a"
        proof
          assume A: "K < m"
          show " n \<le> val_Zp_dist (s m) a"
          proof-
            have X: "(s m) \<in> carrier Zp" 
              using "0" closed_seqs_memE[of _ Zp] 
              by blast
            have "(s m) (nat n) = (res_lim s) (nat n)"
              using A K_def  by blast
            then have "(s m) (nat n) = a (nat n)" 
              using assms(2) by blast
            then have "int (nat n) \<le> val_Zp_dist (s m) a"
              using  X val_Zp_dist_res_eq2 "0" by blast
            then show ?thesis
              by (metis eint_ord_simps(1) int_ops(1) less_not_sym nat_eq_iff2 not_le order_trans zero_eint_def)              
          qed
        qed
      qed
      then show ?thesis 
        using val_Zp_dist_def by auto 
    qed
  qed
  then show ?thesis using
    "0" Zp_converges_to_def 
    by (metis Suc_ile_eq val_Zp_dist_def)
qed

lemma convergent_imp_Zp_cauchy: 
  assumes "s \<in> closed_seqs Zp"
  assumes "a \<in> carrier Zp"
  assumes "Zp_converges_to s a"
  shows "is_Zp_cauchy s"
  apply(rule is_Zp_cauchyI)
  using assms apply simp 
proof-
  fix n
  show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 n = s n1 n "
  proof-
    obtain k where k_def:"\<forall>m>k.  n < val_Zp_dist (s m) a"
      using assms val_Zp_dist_def 
      unfolding Zp_converges_to_def 
      by presburger    
    have A0:  "\<forall>n0 n1. k < n0 \<and> k < n1 \<longrightarrow> s n0 n = s n1 n "     
    proof- have "\<And>n0 n1. k < n0 \<and> k < n1 \<longrightarrow> s n0 n = s n1 n"
      proof
      fix n0 n1
      assume A: " k < n0 \<and> k < n1"
      show " s n0 n = s n1 n "
      proof-
        have 0: "n < val_Zp_dist (s n0) a"
          using k_def using  A 
          by blast  
        have 1: "n < val_Zp_dist (s n1) a"
          using k_def using  A 
          by blast
        hence 2: "(s n0) n = a n"
          using 0 assms val_Zp_dist_res_eq[of "s n0" a n] closed_seqs_memE 
          by blast          
        hence 3: "(s n1) n = a n"
          using 1 assms val_Zp_dist_res_eq[of "s n1" a n] closed_seqs_memE 
          by blast                              
        show ?thesis 
          using 2 3 
          by auto 
      qed
       qed
       thus ?thesis by blast       
    qed
    show ?thesis 
      using A0 
      by blast 
  qed
qed

lemma unique_limit:
  assumes "s \<in> closed_seqs Zp"
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "Zp_converges_to s a"
  assumes "Zp_converges_to s b"
  shows "a = b"
proof-
  have "\<And>k. a k = b k"
  proof-
    fix k::nat
    obtain k0 where k0_def:"\<forall>m>k0.  k < val_Zp_dist (s m) a"
      using assms  unfolding val_Zp_dist_def Zp_converges_to_def 
      by blast 
    obtain k1 where k1_def:"\<forall>m>k1. k <  val_Zp_dist (s m) b"
      using assms unfolding val_Zp_dist_def Zp_converges_to_def 
      by blast
    have k0_prop: "\<And>m. m> k0 \<Longrightarrow> (s m) k = a k" proof- fix m assume A: "m > k0" 
      then show "(s m) k = a k"
      using k0_def assms closed_seqs_memE[of s Zp] val_Zp_dist_res_eq[of _ a k] of_nat_Suc
       by blast
    qed
    have k1_prop: "\<And>m. m> k1 \<Longrightarrow> (s m) k = b k"
      using k1_def assms closed_seqs_memE[of s Zp] 
      by (simp add: val_Zp_dist_res_eq)      
    have "\<And> m. m > (max k0 k1) \<Longrightarrow> a k = b k"
      using k0_prop k1_prop 
      by force
    then show "a k = b k"
      by blast
  qed
  then show ?thesis 
    by blast
qed

lemma unique_limit':
  assumes "s \<in> closed_seqs Zp"
  assumes "a \<in> carrier Zp"
  assumes "Zp_converges_to s a"
  shows "a = res_lim s"
  using unique_limit[of s a "res_lim s"] assms 
        convergent_imp_Zp_cauchy is_Zp_cauchy_imp_has_limit res_lim_in_Zp 
  by blast

lemma Zp_converges_toE:
  assumes "s \<in> closed_seqs Zp"
  assumes "a \<in> carrier Zp"
  assumes "Zp_converges_to s a"
  shows "\<exists>N. \<forall>k > N. s k n = a n"
  by (metis assms(1) assms(2) assms(3) 
      convergent_imp_Zp_cauchy 
      res_lim_Zp_cauchy unique_limit')

lemma Zp_converges_toI:
  assumes "s \<in> closed_seqs Zp"
  assumes "a \<in> carrier Zp"
  assumes "\<And>n. \<exists>N. \<forall>k > N. s k n = a n"
  shows "Zp_converges_to s a"
proof-
  have 0: "(a \<in> carrier Zp \<and> s \<in> closed_seqs Zp)" 
    using assms
    by auto 
  have 1: "(\<forall>n::int. \<exists>k. \<forall>m>k.  n < val_Zp_dist (s m) a) "
  proof
    fix n::int 
    show "\<exists>k. \<forall>m>k.  n < val_Zp_dist (s m) a "
    proof(cases "n < 0")
      case True
      have "\<forall>m>0.  n < val_Zp_dist (s m) a "
      proof
        fix m ::nat
        show "0 < m \<longrightarrow>  n < val_Zp_dist (s m) a"
        proof
          have 0: "eint n < 0"
            by (simp add: True zero_eint_def)
          have 1: " s m \<ominus> a \<in> carrier Zp"
            using assms 
            by (simp add: closed_seqs_diff_closed)            
          thus " n < val_Zp_dist (s m) a"
            using 0  True val_pos[of "s m \<ominus> a"]
            unfolding val_Zp_dist_def 
            by auto                 
        qed 
      qed
      then show ?thesis 
        by blast
    next
      case False
      then have P0: "n \<ge> 0"
        by auto 
      obtain N where N_def: "\<forall>k > N. s k (Suc (nat n)) = a (Suc (nat n))"
        using assms by blast      
      have "\<forall>m>N.  n < val_Zp_dist (s m) a "
      proof
        fix m
        show " N < m \<longrightarrow>  n < val_Zp_dist (s m) a"
        proof
          assume A: "N < m"
          then have A0: "s m (Suc (nat n)) = a (Suc (nat n))"
            using N_def by blast 
          have "(Suc (nat n)) \<le> val_Zp_dist (s m) a"
            using assms A0 val_Zp_dist_res_eq2[of "s m" a "Suc (nat n)"] closed_seqs_memE 
            by blast          
          thus "n < val_Zp_dist (s m) a"
            using False 
            by (meson P0 eint_ord_simps(2) less_Suc_eq less_le_trans nat_less_iff)          
        qed
      qed
      then show ?thesis 
        by blast
    qed
  qed
  show ?thesis 
    unfolding Zp_converges_to_def 
    using 0 1 
    by (simp add: val_Zp_dist_def) 
qed

text\<open>Sums and products of cauchy sequences are cauchy:\<close>

lemma sum_of_Zp_cauchy_is_Zp_cauchy:
  assumes "is_Zp_cauchy s"
  assumes "is_Zp_cauchy t"
  shows "is_Zp_cauchy (s \<oplus>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t)"
proof(rule is_Zp_cauchyI)
  show "(s \<oplus>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) \<in> closed_seqs Zp" 
    using assms seq_plus_closed is_Zp_cauchy_def by blast
  show "\<And>n. \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> (s \<oplus>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n0 n = (s \<oplus>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n1 n"
  proof-
    fix n
    show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> (s \<oplus>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n0 n = (s \<oplus>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n1 n"
    proof-
      obtain N1 where N1_def: "\<forall>n0 n1. N1 < n0 \<and> N1 < n1 \<longrightarrow> s n0 n = s n1 n" 
        using assms(1) is_Zp_cauchy_imp_res_eventually_const_0 padic_integers_axioms  by blast
      obtain N2 where N2_def: "\<forall>n0 n1. N2 < n0 \<and> N2 < n1 \<longrightarrow> t n0 n = t n1 n" 
        using assms(2) is_Zp_cauchy_imp_res_eventually_const_0 padic_integers_axioms by blast
      obtain M where M_def: "M = max N1 N2"
        by simp
      have "\<forall>n0 n1. M < n0 \<and> M < n1 \<longrightarrow> (s \<oplus>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n0 n = (s \<oplus>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n1 n"
      proof
        fix n0
        show "\<forall>n1. M < n0 \<and> M < n1 \<longrightarrow> (s \<oplus>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n0 n = (s \<oplus>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n1 n"
        proof
          fix n1 
          show " M < n0 \<and> M < n1 \<longrightarrow> (s \<oplus>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n0 n = (s \<oplus>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n1 n"
          proof
            assume A: "M < n0 \<and> M < n1 "
            have Fs: " s n0 n = s n1 n" using A M_def N1_def by auto
            have Ft: " t n0 n = t n1 n" using A M_def N2_def by auto
            then show "(s \<oplus>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n0 n = (s \<oplus>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n1 n" 
              using seq_plus_simp[of s t] assms  
              by (simp add: Fs is_Zp_cauchy_imp_closed residue_of_sum)                                               
          qed
        qed
      qed
      then show ?thesis 
        by blast
    qed
  qed
qed
   
lemma prod_of_Zp_cauchy_is_Zp_cauchy:
  assumes "is_Zp_cauchy s"
  assumes "is_Zp_cauchy t"
  shows "is_Zp_cauchy (s \<otimes>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t)"
proof(rule is_Zp_cauchyI)
  show "(s \<otimes>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) \<in> closed_seqs Zp" 
    using assms(1) assms(2) is_Zp_cauchy_def seq_mult_closed by auto  
  show "\<And>n. \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> (s \<otimes>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n0 n = (s \<otimes>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n1 n"
  proof-
    fix n
    show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> (s \<otimes>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n0 n = (s \<otimes>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n1 n"
    proof-
      obtain N1 where N1_def: "\<forall>n0 n1. N1 < n0 \<and> N1 < n1 \<longrightarrow> s n0 n = s n1 n" 
        using assms(1) is_Zp_cauchy_imp_res_eventually_const_0 padic_integers_axioms by blast
      obtain N2 where N2_def: "\<forall>n0 n1. N2 < n0 \<and> N2 < n1 \<longrightarrow> t n0 n = t n1 n" 
        using assms(2) is_Zp_cauchy_imp_res_eventually_const_0 padic_integers_axioms by blast
      obtain M where M_def: "M = max N1 N2"
        by simp
      have "\<forall>n0 n1. M < n0 \<and> M < n1 \<longrightarrow> (s \<otimes>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n0 n = (s \<otimes>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n1 n"
      proof
        fix n0
        show "\<forall>n1. M < n0 \<and> M < n1 \<longrightarrow> (s \<otimes>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n0 n = (s \<otimes>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n1 n"
        proof
          fix n1 
          show " M < n0 \<and> M < n1 \<longrightarrow> (s \<otimes>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n0 n = (s \<otimes>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n1 n"
          proof
            assume A: "M < n0 \<and> M < n1 "
            have Fs: " s n0 n = s n1 n" using A M_def N1_def by auto
            have Ft: " t n0 n = t n1 n" using A M_def N2_def by auto
            then show "(s \<otimes>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n0 n = (s \<otimes>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> t) n1 n" 
              using seq_mult_simp[of s t] is_Zp_cauchy_imp_closed assms 
              by (simp add: Fs residue_of_prod) 
          qed
        qed
      qed
      then show ?thesis 
        by blast
    qed
  qed
qed

text\<open>Constant sequences are cauchy:\<close>

lemma constant_is_Zp_cauchy:
  assumes "is_constant_seq Zp s"
  shows "is_Zp_cauchy s"
proof(rule is_Zp_cauchyI)
  show "s \<in> closed_seqs Zp"
  proof(rule closed_seqs_memI)
    fix k 
    show "s k \<in> carrier Zp" 
      using assms is_constant_seq_imp_closed
      by (simp add: is_constant_seq_imp_closed closed_seqs_memE)            
  qed
  obtain x where "\<And> k. s k = x" 
    using assms 
    by (meson is_constant_seqE)   
  then show "\<And>n. \<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 n = s n1 n" 
    by simp
qed

text\<open>Scalar multiplies of cauchy sequences are cauchy:\<close>

lemma smult_is_Zp_cauchy:
  assumes "is_Zp_cauchy s"
  assumes "a \<in> carrier Zp"
  shows "is_Zp_cauchy (a \<odot>\<^bsub>Zp\<^bsup>\<omega>\<^esup>\<^esub> s)"
  apply(rule is_Zp_cauchyI)
  apply (meson U_function_ring.ring_seq_smult_closed U_function_ring_axioms assms(1) assms(2) is_Zp_cauchy_def)
  using assms ring_seq_smult_eval[of s a] is_Zp_cauchy_imp_closed[of s]
  by (metis res_lim_Zp_cauchy residue_of_prod)

lemma Zp_cauchy_imp_approaches_res_lim:
  assumes "is_Zp_cauchy s"
  assumes "a = res_lim s"
  obtains N where "\<And>n. n> N \<Longrightarrow> val_Zp (a \<ominus> (s n)) > eint k"
proof-
  have " (\<forall>n::int. \<exists>k. \<forall>m>k.  n < val_Zp_dist (s m) a)"
    using Zp_converges_to_def[of s a] assms is_Zp_cauchy_imp_has_limit[of s a] val_Zp_dist_def 
    by simp    
  then have "\<exists>N. \<forall>m>N.  k < val_Zp_dist (s m) a"
    by blast    
  then obtain N where N_def: "\<forall>m>N.  k < val_Zp_dist (s m) a"
    by blast
  have "\<And>n. n> N \<Longrightarrow> val_Zp (a \<ominus> (s n)) > k"
  proof-
    fix m
    assume "m > N"
    then have 0: "k < val_Zp_dist (s m) a"
      using N_def   
      by (simp add: val_Zp_def)
    show "k < val_Zp (a \<ominus> s m)"
      using "0" assms(1) assms(2) is_Zp_cauchy_def closed_seqs_memE[of _ Zp] val_Zp_dist_def val_Zp_dist_sym res_lim_in_Zp by auto     
  qed
  then show ?thesis 
    using that 
    by blast
qed

(**************************************************************************************************)
(**************************************************************************************************)
(****************************)  section\<open>Continuous Functions\<close>  (***********************************)
(**************************************************************************************************)
(**************************************************************************************************)

text\<open>
  For convenience, we will use a slightly unorthodox definition of continuity here.
  Since $\mathbb{Z}_p$ is complete, a function is continuous if and only if its compositions
  with cauchy sequences are cauchy sequences. Thus we can define a continuous function on
  $\mathbb{Z}_p$ as a function which carries cauchy sequences to cauchy sequences under
  composition. Note that this does not generalize to a definition of continuity for functions
  defined on incomplete subsets of $\mathbb{Z}_p$. For example, the function $1/x$ defined on
  $\mathbb{Z}_p - \{0\}$ clearly does not have this property but is continuous. However, towards
  a proof of Hensel's Lemma we will only need to consider polynomial functions and so this 
  definition suffices for our purposes.
\<close>

subsection\<open>Defining Continuous Functions and Basic Examples\<close>
abbreviation Zp_constant_function ("\<cc>\<^bsub>Zp\<^esub>") where
"\<cc>\<^bsub>Zp\<^esub> a \<equiv> constant_function (carrier Zp) a"

definition is_Zp_continuous ::"padic_int_fun \<Rightarrow> bool" where
"is_Zp_continuous f = (f \<in> carrier (Fun Zp) \<and>(\<forall> s. is_Zp_cauchy s \<longrightarrow> is_Zp_cauchy(f \<circ> s)))"

lemma Zp_continuous_is_Zp_closed:
  assumes "is_Zp_continuous f"
  shows "f \<in> carrier (Fun Zp)" 
  using assms is_Zp_continuous_def by blast

lemma is_Zp_continuousI:
  assumes "f \<in> carrier (Fun Zp)"
  assumes "\<And>s. is_Zp_cauchy s \<Longrightarrow> is_Zp_cauchy (f \<circ> s)"
  shows "is_Zp_continuous f"
proof-
  have "(\<forall> s. is_Zp_cauchy s \<longrightarrow> is_Zp_cauchy(f \<circ> s))"
  proof
    fix s
    show "is_Zp_cauchy s \<longrightarrow> is_Zp_cauchy (f \<circ> s) " 
      by (simp add: assms(2))
  qed
  then show ?thesis 
    using assms(1) is_Zp_continuous_def by blast
qed

lemma Zp_continuous_is_closed:
  assumes "is_Zp_continuous f"
  shows "f \<in> carrier (Fun Zp)"
  using assms unfolding is_Zp_continuous_def by blast

lemma constant_is_Zp_continuous:
  assumes "a \<in> carrier Zp"
  shows "is_Zp_continuous (const a)"
proof(rule is_Zp_continuousI)
  show "\<cc>\<^bsub>Zp\<^esub> a \<in> carrier (function_ring (carrier Zp) Zp)" 
    by (simp add: assms constant_function_closed)          
  show "\<And>s. is_Zp_cauchy s \<Longrightarrow> is_Zp_cauchy (\<cc>\<^bsub>Zp\<^esub> a \<circ> s) "
  proof-
    fix s
    assume A: "is_Zp_cauchy s"
    have "is_constant_seq Zp (\<cc>\<^bsub>Zp\<^esub> a \<circ> s)" 
      using constant_function_comp_is_constant_seq[of a s] A assms 
        is_Zp_cauchy_imp_closed by blast
    then show "is_Zp_cauchy (\<cc>\<^bsub>Zp\<^esub> a \<circ> s)"
      using A assms  constant_is_Zp_cauchy 
      by blast
  qed
qed

lemma sum_of_cont_is_cont:
  assumes "is_Zp_continuous f"
  assumes "is_Zp_continuous g"
  shows "is_Zp_continuous (f \<oplus>\<^bsub>Fun Zp\<^esub> g)"
  apply(rule is_Zp_continuousI)
  using assms Zp_continuous_is_closed assms function_sum_comp_is_seq_sum[of _ f g] 
  apply (simp add: fun_add_closed)
  using assms(1) assms(2) function_sum_comp_is_seq_sum is_Zp_cauchy_def is_Zp_continuous_def sum_of_Zp_cauchy_is_Zp_cauchy by auto
  
lemma prod_of_cont_is_cont:
  assumes "is_Zp_continuous f"
  assumes "is_Zp_continuous g"
  shows "is_Zp_continuous (f \<otimes>\<^bsub>Fun Zp\<^esub> g)"
  apply(rule is_Zp_continuousI)
  using assms Zp_continuous_is_closed assms
  apply (simp add: fun_mult_closed)
  using  function_mult_comp_is_seq_mult[of _ f g] assms(1) assms(2) is_Zp_cauchy_imp_closed 
    is_Zp_continuous_def prod_of_Zp_cauchy_is_Zp_cauchy by auto

lemma smult_is_continuous:
  assumes "is_Zp_continuous f"
  assumes "a \<in> carrier Zp"
  shows "is_Zp_continuous (a \<odot>\<^bsub>Fun Zp\<^esub> f)"
  apply(rule is_Zp_continuousI)
  using assms  apply (simp add: assms function_smult_closed is_Zp_continuous_def)
  using ring_seq_smult_comp_assoc assms 
  by (simp add: is_Zp_cauchy_imp_closed is_Zp_continuous_def smult_is_Zp_cauchy)

lemma id_Zp_is_Zp_continuous:
"is_Zp_continuous ring_id"
  apply(rule is_Zp_continuousI)
  by (auto simp add: is_Zp_cauchy_imp_closed ring_id_seq_comp)
   
lemma nat_pow_is_Zp_continuous:
  assumes "is_Zp_continuous f"
  shows "is_Zp_continuous (f[^]\<^bsub>Fun Zp\<^esub>(n::nat))"
  apply(induction n)
  using constant_is_Zp_continuous function_one_is_constant apply force
  by (simp add: assms prod_of_cont_is_cont)

lemma ring_id_pow_closed:
"(ring_id)[^]\<^bsub>Fun Zp\<^esub> (n::nat) \<in> carrier (Fun Zp)"
  by (simp add: function_ring_is_monoid monoid.nat_pow_closed)

lemma monomial_equation:
  assumes "c \<in> carrier Zp"
  shows "monomial c n = c \<odot>\<^bsub>Fun Zp\<^esub> (ring_id)[^]\<^bsub>Fun Zp\<^esub>n"
  apply(rule function_ring_car_eqI)
    apply (simp add: assms monomial_functions)
  using assms function_smult_closed[of c "ring_id [^]\<^bsub>Fun Zp\<^esub> n"] ring_id_pow_closed apply blast
  unfolding monomial_function_def 
  using assms function_smult_eval[of c "(ring_id)[^]\<^bsub>Fun Zp\<^esub> (n::nat)"] 
        function_nat_pow_eval[of ring_id _ n]
  by (simp add: ring_id_eval ring_id_pow_closed)
  
lemma monomial_is_Zp_continuous:
  assumes "c \<in> carrier Zp"
  shows "is_Zp_continuous (monomial c n)" 
  using monomial_equation[of c n] nat_pow_is_Zp_continuous 
  by (simp add: assms id_Zp_is_Zp_continuous smult_is_continuous)

subsection\<open>Composition by a Continuous Function Commutes with Taking Limits of Sequences\<close>

text \<open>
  Due to our choice of definition for continuity, a little bit of care is required to show that
  taking the limit of a cauchy sequence commutes with composition by a continuous function.
  For a sequence $(s_n)_{n \in \mathbb{N}}$ converging to a point $t$, we can consider the 
  alternating sequence $(s_0, t, s_1, t, s_2, t, \dots)$ which is also cauchy. Clearly 
  composition with $f$ yields $(f(s_0), f(t), f(s_1), f(t), f(s_2), f(t), \dots)$ from which
  we can see that the limit must be $f(t)$.
\<close>
definition alt_seq where
"alt_seq s = (\<lambda>k. (if (even k) then (s k) else (res_lim s)))"

lemma alt_seq_Zp_cauchy:
  assumes "is_Zp_cauchy s"
  shows "is_Zp_cauchy (alt_seq s)"
proof(rule is_Zp_cauchyI)
  show "(alt_seq s) \<in> closed_seqs Zp"
    unfolding alt_seq_def using assms is_Zp_cauchy_imp_closed
    by (simp add: closed_seqs_memE closed_seqs_memI res_lim_in_Zp)          
  fix n
  show "\<exists>N. \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> alt_seq s n0 n = alt_seq s n1 n "
  proof-
    obtain N where N_def: " \<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> s n0 n =  s n1 n "
      using assms is_Zp_cauchy_imp_res_eventually_const_0
            padic_integers_axioms 
      by blast
    have "\<forall>n0 n1. N < n0 \<and> N < n1 \<longrightarrow> alt_seq s n0 n = alt_seq s n1 n "
      apply auto 
    proof-
      fix n0 n1
      assume A: "N < n0" "N < n1"
      show "alt_seq s n0 n = alt_seq s n1 n"
        using N_def 
        unfolding alt_seq_def 
        by (smt A(1) A(2) assms lessI max_less_iff_conj 
            res_lim_Zp_cauchy padic_integers_axioms)
    qed
    then show ?thesis 
      by blast
  qed
qed

lemma alt_seq_limit:
  assumes "is_Zp_cauchy s"
  shows "res_lim(alt_seq s) = res_lim s"
proof-
  have "\<And>k. res_lim(alt_seq s) k = res_lim s k"
  proof-
    fix k
    obtain N where N_def: "\<forall> m. m> N \<longrightarrow>  s m k = res_lim s k"
      using assms res_lim_Zp_cauchy 
      by blast
    obtain N' where N'_def: "\<forall> m. m> N' \<longrightarrow>  (alt_seq s) m k = res_lim (alt_seq s) k"
      using assms res_lim_Zp_cauchy 
            alt_seq_Zp_cauchy 
      by blast
    have "\<And>m. m > (max N N') \<Longrightarrow> s m k = res_lim (alt_seq s) k"
    proof-
      fix m 
      assume A0: "m > (max N N')"
      have A1: "s m k = res_lim s k"
        using A0 N_def 
        by simp
      have A2: "(alt_seq s) m k = res_lim (alt_seq s) k"
        using A0 N'_def 
        by simp
      have A3: "(alt_seq s) m k = res_lim s k"
        using alt_seq_def A1 A2 
        by presburger
      show "s m k = res_lim (alt_seq s) k" 
        using A1 A2 A3 
        by auto 
    qed
    then have P:"\<And>m. m > (max N N') \<Longrightarrow> (res_lim s k) = res_lim (alt_seq s) k" 
      using N_def 
      by auto
    show "res_lim(alt_seq s) k = res_lim s k" 
      using P[of "Suc (max N N')"] 
      by auto 
  qed
  then show ?thesis 
    by (simp add: ext)
qed

lemma res_lim_pushforward: 
  assumes "is_Zp_continuous f"
  assumes "is_Zp_cauchy s"
  assumes "t = alt_seq s"
  shows "res_lim (f \<circ> t) = f (res_lim t)"
proof-
  have 0: "Zp_converges_to (f \<circ> t) (res_lim (f \<circ> t))"
    using assms alt_seq_Zp_cauchy is_Zp_cauchy_imp_has_limit 
          is_Zp_continuous_def 
    by blast
  have  "\<And>k. res_lim (f \<circ> t) k = f (res_lim t) k"
  proof-
    fix k
    show "res_lim (f \<circ> t) k = f (res_lim t) k"
    proof-
      obtain N where N_def: "\<And>m. m> N \<Longrightarrow> (f \<circ> t) m k = (res_lim (f \<circ> t)) k"
        using 0  
        by (meson convergent_imp_Zp_cauchy Zp_converges_to_def res_lim_Zp_cauchy)
      obtain M where M_def: "M = 2*(Suc N) + 1"
        by simp
      have 0: "t M = res_lim s"
        using assms 
        unfolding alt_seq_def
        by (simp add: M_def)
      have 1: "(f \<circ> t) M k = (res_lim (f \<circ> t)) k"
        using N_def M_def 
        by auto 
      have 2: "(f \<circ> t) M k = f (t M) k"
        by simp      
      have 3: "(f \<circ> t) M k = f (res_lim s) k"
        using 0 2 by simp
      have 4: "(f \<circ> t) M k = f (res_lim t) k"
        using 3 assms alt_seq_limit[of s] 
        by auto
      show ?thesis 
        using 4 1 by auto 
    qed
  qed
  then show ?thesis by(simp add: ext)
qed

lemma res_lim_pushforward': 
  assumes "is_Zp_continuous f"
  assumes "is_Zp_cauchy s"
  assumes "t = alt_seq s"
  shows "res_lim (f \<circ> s) = res_lim (f \<circ> t)"
proof-
  obtain a where a_def: "a = res_lim (f \<circ> s)"
    by simp
  obtain b where b_def: "b = res_lim (f \<circ> t)"
    by simp 
  have "\<And>k. a k = b k"
  proof-
    fix k
    obtain Na where Na_def: "\<And>m. m > Na \<Longrightarrow> (f \<circ> s) m k = a k"
      using a_def assms  is_Zp_continuous_def 
            padic_integers_axioms res_lim_Zp_cauchy
      by blast
    obtain Nb where Nb_def: "\<And>m. m > Nb \<Longrightarrow> (f \<circ> t) m k = b k"
      using b_def assms is_Zp_continuous_def 
            padic_integers_axioms res_lim_Zp_cauchy
            alt_seq_Zp_cauchy 
      by blast
    obtain M where M_def: "M = 2*(max Na Nb) + 1"
      by simp
    have M0: "odd M"
      by (simp add: M_def)
    have M1: "M > Na" 
      using M_def 
      by auto 
    have M2: "M > Nb" 
      using M_def 
      by auto 
    have M3: "t M = res_lim s"
      using assms alt_seq_def M0 
      by auto 
    have M4: "((f \<circ> t) M) = f (res_lim s)"
      using M3 
      by auto 
    have M5: "((f \<circ> t) M) k = b k"
      using M2 Nb_def by auto 
    have M6: "f (res_lim s) = f (res_lim t)" 
      using assms alt_seq_limit[of s] 
      by auto 
    have M7: "f (res_lim t) k = b k"
      using M4 M5 M6 by auto
    have M8: "(f \<circ> s) M k = (f \<circ> s) (Suc M) k"
      using M1 Na_def by auto
    have M9: "(f \<circ> s) (Suc M) = (f \<circ> t) (Suc M)"
      using assms unfolding alt_seq_def
      using M_def 
      by auto 
    have M10: "(f \<circ> t) M k = (f \<circ> t) (Suc M) k"
      using M2 Nb_def by auto     
    have M11: "(f \<circ> t) M k = (f \<circ> s) M k"
      using M10 M8 M9 by auto    
    show "a k = b k" 
      using M1 M11 M5 Na_def by auto
  qed
  then show ?thesis using a_def b_def ext[of a b] by auto 
qed

lemma continuous_limit:
  assumes "is_Zp_continuous f"
  assumes "is_Zp_cauchy s"
  shows "Zp_converges_to (f \<circ> s) (f (res_lim s))"
proof-
  obtain t where t_def: "t = alt_seq s"
    by simp
  have 0: "Zp_converges_to (f \<circ> s) (res_lim (f \<circ> s))"
    using assms(1) assms(2) is_Zp_continuous_def 
      is_Zp_cauchy_imp_has_limit padic_integers_axioms by blast
  have 1: "Zp_converges_to (f \<circ> s) (res_lim (f \<circ> t))"
    using "0" assms(1) assms(2) res_lim_pushforward' t_def by auto
  have 2: "Zp_converges_to (f \<circ> s) (f (res_lim t))"
    using "1" assms(1) assms(2) res_lim_pushforward padic_integers_axioms t_def by auto
  then show  "Zp_converges_to (f \<circ> s) (f (res_lim s))"
    by (simp add: alt_seq_limit assms(2) t_def)
qed


end
end 
