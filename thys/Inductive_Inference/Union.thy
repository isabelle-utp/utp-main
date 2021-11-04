section \<open>The union of classes\label{s:union}\<close>

theory Union
  imports R1_BC TOTAL_CONS
begin

text \<open>None of the inference types introduced in this chapter are closed
under union of classes. For all inference types except FIN this follows from
@{thm[source] "U0_V0_not_in_BC"}.\<close>

lemma not_closed_under_union:
  "\<forall>\<I>\<in>{CP, TOTAL, CONS, LIM, BC}. U\<^sub>0 \<in> \<I> \<and> V\<^sub>0 \<in> \<I> \<and> U\<^sub>0 \<union> V\<^sub>0 \<notin> \<I>"
  using U0_in_CP U0_in_NUM V0_in_FIN
    FIN_subseteq_CP
    NUM_subseteq_TOTAL
    CP_subseteq_TOTAL
    TOTAL_subseteq_CONS
    CONS_subseteq_Lim
    Lim_subseteq_BC
    U0_V0_not_in_BC
  by blast

text \<open>In order to show the analogous result for FIN consider the
classes $\{0^\infty\}$ and $\{0^n10^\infty \mid n \in \mathbb{N}\}$. The
former can be learned finitely by a strategy that hypothesizes $0^\infty$ for
every input. The latter can be learned finitely by a strategy that waits for
the 1 and hypothesizes the only function in the class with a 1 at that
position. However, the union of both classes is not in FIN. This is because
any FIN strategy has to hypothesize $0^\infty$ on some prefix of the form
$0^n$. But the strategy then fails for the function $0^n10^\infty$.\<close>

lemma singleton_in_FIN: "f \<in> \<R> \<Longrightarrow> {f} \<in> FIN"
proof -
  assume "f \<in> \<R>"
  then obtain i where i: "\<phi> i = f"
    using phi_universal by blast
  define s :: partial1 where "s = (\<lambda>_. Some (Suc i))"
  then have "s \<in> \<R>"
    using const_in_Prim1[of "Suc i"] by simp
  have "learn_fin \<phi> {f} s"
  proof (intro learn_finI)
    show "environment \<phi> {f} s"
      using \<open>s \<in> \<R>\<close> \<open>f \<in> \<R>\<close> by (simp add: phi_in_P2)
    show "\<exists>i n\<^sub>0. \<phi> i = g \<and> (\<forall>n<n\<^sub>0. s (g \<triangleright> n) \<down>= 0) \<and> (\<forall>n\<ge>n\<^sub>0. s (g \<triangleright> n) \<down>= Suc i)"
      if "g \<in> {f}" for g
    proof -
      from that have "g = f" by simp
      then have "\<phi> i = g"
        using i by simp
      moreover have "\<forall>n<0. s (g \<triangleright> n) \<down>= 0" by simp
      moreover have "\<forall>n\<ge>0. s (g \<triangleright> n) \<down>= Suc i"
        using s_def by simp
      ultimately show ?thesis by auto
    qed
  qed
  then show "{f} \<in> FIN" using FIN_def by auto
qed

definition U_single :: "partial1 set" where
  "U_single \<equiv> {(\<lambda>x. if x = n then Some 1 else Some 0)| n. n \<in> UNIV}"

lemma U_single_in_FIN: "U_single \<in> FIN"
proof -
  define psi :: partial2 where "psi \<equiv> \<lambda>n x. if x = n then Some 1 else Some 0"
  have "psi \<in> \<R>\<^sup>2"
    using psi_def by (intro R2I[of "Cn 2 r_not [r_eq]"]) auto
  define s :: partial1 where
    "s \<equiv> \<lambda>b. if findr b \<down>= e_length b then Some 0 else Some (Suc (the (findr b)))"
  have "s \<in> \<R>"
  proof (rule R1I)
    let ?r = "Cn 1 r_ifeq [r_findr, r_length, Z, Cn 1 S [r_findr]]"
    show "recfn 1 ?r" by simp
    show "total ?r" by auto
    show "eval ?r [b] = s b" for b
    proof -
      let ?b = "the (findr b)"
      have "eval ?r [b] = (if ?b = e_length b then Some 0 else Some (Suc (?b)))"
        using findr_total by simp
      then show "eval ?r [b] = s b"
        by (metis findr_total option.collapse option.inject s_def)
    qed
  qed
  have "U_single \<subseteq> \<R>"
  proof
    fix f
    assume "f \<in> U_single"
    then obtain n where "f = (\<lambda>x. if x = n then Some 1 else Some 0)"
      using U_single_def by auto
    then have "f = psi n"
      using psi_def by simp
    then show "f \<in> \<R>"
      using \<open>psi \<in> \<R>\<^sup>2\<close> by simp
  qed
  have "learn_fin psi U_single s"
  proof (rule learn_finI)
    show "environment psi U_single s"
      using \<open>psi \<in> \<R>\<^sup>2\<close> \<open>s \<in> \<R>\<close> \<open>U_single \<subseteq> \<R>\<close> by simp
    show "\<exists>i n\<^sub>0. psi i = f \<and> (\<forall>n<n\<^sub>0. s (f \<triangleright> n) \<down>= 0) \<and> (\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= Suc i)"
      if "f \<in> U_single" for f
    proof -
      from that obtain i where i: "f = (\<lambda>x. if x = i then Some 1 else Some 0)"
        using U_single_def by auto
      then have "psi i = f"
        using psi_def by simp
      moreover have "\<forall>n<i. s (f \<triangleright> n) \<down>= 0"
        using i s_def findr_def by simp
      moreover have "\<forall>n\<ge>i. s (f \<triangleright> n) \<down>= Suc i"
      proof (rule allI, rule impI)
        fix n
        assume "n \<ge> i"
        let ?e = "init f n"
        have "\<exists>i<e_length ?e. e_nth ?e i \<noteq> 0"
          using \<open>n \<ge> i\<close> i by simp
        then have less: "the (findr ?e) < e_length ?e"
          and nth_e: "e_nth ?e (the (findr ?e)) \<noteq> 0"
          using findr_ex by blast+
        then have "s ?e \<down>= Suc (the (findr ?e))"
          using s_def by auto
        moreover have "the (findr ?e) = i"
          using nth_e less i by (metis length_init nth_init option.sel)
        ultimately show "s ?e \<down>= Suc i" by simp
      qed
      ultimately show ?thesis by auto
    qed
  qed
  then show "U_single \<in> FIN" using FIN_def by blast
qed

lemma zero_U_single_not_in_FIN: "{0\<^sup>\<infinity>} \<union> U_single \<notin> FIN"
proof
  assume "{0\<^sup>\<infinity>} \<union> U_single \<in> FIN"
  then obtain psi s where learn: "learn_fin psi ({0\<^sup>\<infinity>} \<union> U_single) s"
    using FIN_def by blast
  then have "learn_fin psi {0\<^sup>\<infinity>} s"
    using learn_fin_closed_subseteq by auto
  then obtain i n\<^sub>0 where i:
    "psi i = 0\<^sup>\<infinity>"
    "\<forall>n<n\<^sub>0. s (0\<^sup>\<infinity> \<triangleright> n) \<down>= 0"
    "\<forall>n\<ge>n\<^sub>0. s (0\<^sup>\<infinity> \<triangleright> n) \<down>= Suc i"
    using learn_finE(2) by blast
  let ?f = "\<lambda>x. if x = Suc n\<^sub>0 then Some 1 else Some 0"
  have "?f \<noteq> 0\<^sup>\<infinity>" by (metis option.inject zero_neq_one)
  have "?f \<in> U_single"
    using U_single_def by auto
  then have "learn_fin psi {?f} s"
    using learn learn_fin_closed_subseteq by simp
  then obtain j m\<^sub>0 where j:
    "psi j = ?f"
    "\<forall>n<m\<^sub>0. s (?f \<triangleright> n) \<down>= 0"
    "\<forall>n\<ge>m\<^sub>0. s (?f \<triangleright> n) \<down>= Suc j"
    using learn_finE(2) by blast
  consider
    (less) "m\<^sub>0 < n\<^sub>0" | (eq) "m\<^sub>0 = n\<^sub>0" | (gr) "m\<^sub>0 > n\<^sub>0"
    by linarith
  then show False
  proof (cases)
    case less
    then have "s (0\<^sup>\<infinity>\<triangleright> m\<^sub>0) \<down>= 0"
      using i by simp
    moreover have "0\<^sup>\<infinity> \<triangleright> m\<^sub>0 = ?f \<triangleright> m\<^sub>0"
      using less init_eqI[of m\<^sub>0 ?f "0\<^sup>\<infinity>"] by simp
    ultimately have "s (?f \<triangleright> m\<^sub>0) \<down>= 0" by simp
    then show False using j by simp
  next
    case eq
    then have "0\<^sup>\<infinity> \<triangleright> m\<^sub>0 = ?f \<triangleright> m\<^sub>0"
      using init_eqI[of m\<^sub>0 ?f "0\<^sup>\<infinity>"] by simp
    then have "s (0\<^sup>\<infinity> \<triangleright> m\<^sub>0) = s (?f \<triangleright> m\<^sub>0)" by simp
    then have "i = j"
      using i j eq by simp
    then have "psi i = psi j" by simp
    then show False using \<open>?f \<noteq> 0\<^sup>\<infinity>\<close> i j by simp
  next
    case gr
    have "0\<^sup>\<infinity> \<triangleright> n\<^sub>0 = ?f \<triangleright> n\<^sub>0"
      using init_eqI[of n\<^sub>0 ?f "0\<^sup>\<infinity>"] by simp
    moreover have "s (0\<^sup>\<infinity> \<triangleright> n\<^sub>0) \<down>= Suc i"
      using i by simp
    moreover have "s (?f \<triangleright> n\<^sub>0) \<down>= 0"
      using j gr by simp
    ultimately show False by simp
  qed
qed

lemma FIN_not_closed_under_union: "\<exists>U V. U \<in> FIN \<and> V \<in> FIN \<and> U \<union> V \<notin> FIN"
proof -
  have "{0\<^sup>\<infinity>} \<in> FIN"
    using singleton_in_FIN const_in_Prim1 by simp
  moreover have "U_single \<in> FIN"
    using U_single_in_FIN by simp
  ultimately show ?thesis
    using zero_U_single_not_in_FIN by blast
qed

text \<open>In contrast to the inference types, NUM is closed under the union
of classes. The total numberings that exist for each NUM class can be
interleaved to produce a total numbering encompassing the union of the
classes. To define the interleaving, modulo and division by two will be
helpful.\<close>

definition "r_div2 \<equiv>
  r_shrink
   (Pr 1 Z
     (Cn 3 r_ifle
       [Cn 3 r_mul [r_constn 2 2, Cn 3 S [Id 3 0]], Id 3 2, Cn 3 S [Id 3 1], Id 3 1]))"

lemma r_div2_prim [simp]: "prim_recfn 1 r_div2"
  unfolding r_div2_def by simp

lemma r_div2 [simp]: "eval r_div2 [n] \<down>= n div 2"
proof -
  let ?p = "Pr 1 Z
    (Cn 3 r_ifle
      [Cn 3 r_mul [r_constn 2 2, Cn 3 S [Id 3 0]], Id 3 2, Cn 3 S [Id 3 1], Id 3 1])"
  have "eval ?p [i, n] \<down>= min (n div 2) i" for i
    by (induction i) auto
  then have "eval ?p [n, n] \<down>= n div 2" by simp
  then show ?thesis unfolding r_div2_def by simp
qed

definition "r_mod2 \<equiv> Cn 1 r_sub [Id 1 0, Cn 1 r_mul [r_const 2, r_div2]]"

lemma r_mod2_prim [simp]: "prim_recfn 1 r_mod2"
  unfolding r_mod2_def by simp

lemma r_mod2 [simp]: "eval r_mod2 [n] \<down>= n mod 2"
  unfolding r_mod2_def using Rings.semiring_modulo_class.minus_mult_div_eq_mod
  by auto

lemma NUM_closed_under_union:
  assumes "U \<in> NUM" and "V \<in> NUM"
  shows "U \<union> V \<in> NUM"
proof -
  from assms obtain psi_u psi_v where
    psi_u: "psi_u \<in> \<R>\<^sup>2" "\<And>f. f \<in> U \<Longrightarrow> \<exists>i. psi_u i = f" and
    psi_v: "psi_v \<in> \<R>\<^sup>2" "\<And>f. f \<in> V \<Longrightarrow> \<exists>i. psi_v i = f"
    by fastforce
  define psi where "psi \<equiv> \<lambda>i. if i mod 2 = 0 then psi_u (i div 2) else psi_v (i div 2)"
  from psi_u(1) obtain u where u: "recfn 2 u" "total u" "\<And>x y. eval u [x, y] = psi_u x y"
    by auto
  from psi_v(1) obtain v where v: "recfn 2 v" "total v" "\<And>x y. eval v [x, y] = psi_v x y"
    by auto
  let ?r_psi = "Cn 2 r_ifz
    [Cn 2 r_mod2 [Id 2 0],
     Cn 2 u [Cn 2 r_div2 [Id 2 0], Id 2 1],
     Cn 2 v [Cn 2 r_div2 [Id 2 0], Id 2 1]]"
  show ?thesis
  proof (rule NUM_I[of psi])
    show "psi \<in> \<R>\<^sup>2"
    proof (rule R2I)
      show "recfn 2 ?r_psi"
        using u(1) v(1) by simp
      show "eval ?r_psi [x, y] = psi x y" for x y
        using u v psi_def prim_recfn_total R2_imp_total2[OF psi_u(1)]
          R2_imp_total2[OF psi_v(1)]
        by simp
      moreover have "psi x y \<down>" for x y
        using psi_def psi_u(1) psi_v(1) by simp
      ultimately show "total ?r_psi"
        using \<open>recfn 2 ?r_psi\<close> totalI2 by simp
    qed
    show "\<exists>i. psi i = f" if "f \<in> U \<union> V" for f
    proof (cases "f \<in> U")
      case True
      then obtain j where "psi_u j = f"
        using psi_u(2) by auto
      then have "psi (2 * j) = f"
        using psi_def by simp
      then show ?thesis by auto
    next
      case False
      then have "f \<in> V"
        using that by simp
      then obtain j where "psi_v j = f"
        using psi_v(2) by auto
      then have "psi (Suc (2 * j)) = f"
        using psi_def by simp
      then show ?thesis by auto
    qed
  qed
qed

end