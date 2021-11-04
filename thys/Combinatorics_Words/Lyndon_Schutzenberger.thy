(*  Title:      CoW/Lyndon_Schutzenberger.thy
    Author:     Štěpán Holub, Charles University
*)

theory Lyndon_Schutzenberger
  imports CoWBasic 
begin

chapter \<open>Lyndon-Schützenberger Equation\<close>

text\<open>The Lyndon-Schützenberger equation is the following equation on words:
\[
x^ay^b = z^c,
\]
in this formalization denoted as @{term "x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c"}, with $2 \leq a,b,c$.
We formalize here a proof that the equation has periodic solutions only in free monoids, that is, that any three words 
$x$, $y$ and $z$ satisfying the equality pairwise commute.
The result was first proved in @{cite LySch62} in a more general setting of free groups.
There are several proofs to be found in the literature (for instance @{cite Lo83 and Dmsi2006}).
The presented proof is the author's proof.
\<close>

text\<open>We set up a locale representing the Lyndon-Schützenberger Equation.\<close>

locale LS =
  fixes x a y b z c
  assumes a:  "2 \<le> a" and b: "2 \<le> b" and c: "2 \<le> c"   and eq: "x\<^sup>@a \<cdot> y\<^sup>@b = z\<^sup>@c" 
begin

lemma a0: "a \<noteq> 0" and b0: "b \<noteq> 0"  
      using a b by auto

text\<open>If $x^a$ or $y^b$ is sufficiently long, then the calim follows from the Periodicity Lemma.\<close>

lemma per_lemma_case:
  assumes "\<^bold>|z\<^bold>| + \<^bold>|x\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|"
  shows "x\<cdot>y=y\<cdot>x"
proof (cases "x = \<epsilon>")
  assume "x = \<epsilon>"
  thus "x\<cdot>y=y\<cdot>x" by simp 
next 
  assume "x \<noteq> \<epsilon>"
  hence "z\<^sup>@c \<noteq> \<epsilon>" 
    using eq assms emp_pow[of c] by auto
  hence "x\<^sup>@a \<le>p (z\<^sup>@c)\<^sup>\<omega>"
    unfolding period_root_def using 
    pref_ext[OF triv_pref[of "x\<^sup>@a" "y\<^sup>@b", unfolded eq], of "x\<^sup>@a"] by blast 
  have "x \<^sup>@ a \<le>p x\<^sup>\<omega>"
    using \<open>x \<noteq> \<epsilon>\<close> a0 root_self[THEN per_drop_exp] by blast
  from two_pers[OF per_drop_exp[OF \<open>x\<^sup>@a \<le>p (z\<^sup>@c)\<^sup>\<omega>\<close>] this assms]
  have "z \<cdot> x = x \<cdot> z".
  hence "z\<^sup>@c\<cdot>x\<^sup>@a = x\<^sup>@a\<cdot>z\<^sup>@c"
    by (simp add: comm_add_exps)
  from this[folded eq, unfolded rassoc cancel, symmetric]
  have "x\<^sup>@a \<cdot> y\<^sup>@b = y\<^sup>@b \<cdot> x\<^sup>@a".
  from this[unfolded comm_pow_roots[OF a0 b0]]
  show "x \<cdot> y = y \<cdot> x".
qed

text\<open>The most challenging case is when $c = 3$.\<close>

lemma core_case:
  assumes 
    "c = 3" and 
    "b*\<^bold>|y\<^bold>| \<le> a*\<^bold>|x\<^bold>|" and "x \<noteq> \<epsilon>" and "y \<noteq> \<epsilon>" and 
    lenx: "a*\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|x\<^bold>|" and
    leny: "b*\<^bold>|y\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|y\<^bold>|"
  shows "x\<cdot>y = y\<cdot>x" 
proof- 
  have "a \<noteq> 0" and "b \<noteq> 0"  
      using a b by auto

  \<comment>\<open>We first show that a = 2\<close>
  have "a*\<^bold>|x\<^bold>|+b*\<^bold>|y\<^bold>| = 3*\<^bold>|z\<^bold>|"
    using \<open>c = 3\<close> eq length_append[of "x\<^sup>@a" "y\<^sup>@b"]
    by (simp add: pow_len)
  hence "3*\<^bold>|z\<^bold>| \<le> a*\<^bold>|x\<^bold>| + a*\<^bold>|x\<^bold>|"
    using \<open>b*\<^bold>|y\<^bold>| \<le> a*\<^bold>|x\<^bold>|\<close>  by simp
  hence "3*\<^bold>|z\<^bold>| < 2*\<^bold>|z\<^bold>| + 2*\<^bold>|x\<^bold>|"
    using lenx by linarith
  hence "\<^bold>|z\<^bold>| + \<^bold>|x\<^bold>| < 3 * \<^bold>|x\<^bold>|" by simp
  from less_trans[OF lenx this, unfolded mult_less_cancel2]
  have "a = 2" using a by force

  hence "\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|" using \<open>b*\<^bold>|y\<^bold>| \<le> a*\<^bold>|x\<^bold>|\<close> b 
      pow_len[of x 2]  pow_len[of y b] mult_le_less_imp_less[of a b "\<^bold>|x\<^bold>|" "\<^bold>|y\<^bold>|"] not_le
    by auto
  have "x\<cdot>x\<cdot>y\<^sup>@b = z\<cdot>z\<cdot>z" using a eq \<open>c=3\<close> \<open>a=2\<close>
    by (simp add: numeral_2_eq_2 numeral_3_eq_3) 

\<comment> \<open>Find words u, v, w\<close>
  have "\<^bold>|z\<^bold>| < \<^bold>|x\<cdot>x\<^bold>|"
    using \<open>\<^bold>|z\<^bold>| + \<^bold>|x\<^bold>| < 3 * \<^bold>|x\<^bold>|\<close> add.commute by auto 
  from ruler_le[THEN prefD, OF triv_pref[of z "z\<cdot>z"] _ less_imp_le[OF this]]
  obtain w  where "z\<cdot>w = x\<cdot>x" 
    using prefI[of "x\<cdot>x" "y\<^sup>@b" "z\<cdot>z\<cdot>z", unfolded rassoc, OF \<open>x\<cdot>x\<cdot>y\<^sup>@b = z\<cdot>z\<cdot>z\<close>] by fastforce  

  have "\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|"
    using \<open>a = 2\<close> lenx by auto
  from ruler_le[THEN prefD, OF _ _ less_imp_le[OF this], of "x\<cdot>x\<cdot>y\<^sup>@b", OF triv_pref, unfolded \<open>x\<cdot>x\<cdot>y\<^sup>@b = z\<cdot>z\<cdot>z\<close>, OF triv_pref]
  obtain u :: "'a list" where "x\<cdot>u=z" 
    by blast
  have "u \<noteq> \<epsilon>"
    using \<open>\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|\<close> \<open>x\<cdot>u = z\<close> by auto 
  have "x = u\<cdot>w" using  \<open>z\<cdot>w = x\<cdot>x\<close> \<open>x\<cdot>u = z\<close> by auto

  have "\<^bold>|x\<cdot>x\<^bold>| < \<^bold>|z\<cdot>z\<^bold>|"  by (simp add: \<open>\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|\<close> add_less_mono)
  from ruler_le[OF triv_pref[of "x\<cdot>x" "y\<^sup>@b", unfolded  rassoc \<open>x\<cdot>x\<cdot>y\<^sup>@b = z\<cdot>z\<cdot>z\<close>, unfolded lassoc] triv_pref, OF less_imp_le[OF this]]
  have "z\<cdot>w \<le>p z\<cdot>z"
    unfolding \<open>z\<cdot>w = x\<cdot>x\<close>.
  obtain v :: "'a list" where "w \<cdot> v = x"
    using lq_pref[of w x] 
   pref_prod_pref'[OF pref_cancel[OF \<open>z\<cdot>w \<le>p z\<cdot>z\<close>, folded \<open>x \<cdot> u = z\<close>, unfolded \<open>x = u \<cdot> w\<close> rassoc], folded  \<open>x = u \<cdot> w\<close>] by blast  
  have "u\<cdot>w\<cdot>v \<noteq> \<epsilon>"
    by (simp add: \<open>u \<noteq> \<epsilon>\<close>)

\<comment> \<open>Express x, y and z in terms of  u, v and w\<close>
  hence "z = w\<cdot>v\<cdot>u"
    using \<open>w \<cdot> v = x\<close> \<open>x \<cdot> u = z\<close> by auto
  from \<open>x \<cdot> x \<cdot> y\<^sup>@b = z \<cdot> z \<cdot> z\<close>[unfolded this lassoc, folded \<open>z \<cdot> w = x \<cdot> x\<close>, unfolded this rassoc]
  have "w\<cdot>v \<cdot> u\<cdot>w \<cdot> y\<^sup>@b = w\<cdot>v\<cdot>u\<cdot>w\<cdot>v\<cdot>u\<cdot>w\<cdot>v\<cdot>u".
  hence "y\<^sup>@b = v\<cdot>u\<cdot>w\<cdot>v\<cdot>u"
    using pref_cancel by auto

\<comment> \<open>Double period of uwv\<close>
  from periodN_fac[OF _ \<open>u\<cdot>w\<cdot>v \<noteq> \<epsilon>\<close>, of v u "\<^bold>|y\<^bold>|", unfolded rassoc, folded this]
  have "periodN (u\<cdot>w\<cdot>v) \<^bold>|y\<^bold>|"
    using pow_per[OF \<open>y \<noteq> \<epsilon>\<close> b0] by blast
  have "u\<cdot>w\<cdot>v = x \<cdot>v"
    by (simp add: \<open>x = u \<cdot> w\<close>) 
  have "u\<cdot>w\<cdot>v = u\<cdot> x"
    by (simp add: \<open>w \<cdot> v = x\<close>)
  have "u\<cdot>w\<cdot>v \<le>p u\<^sup>\<omega>"
    unfolding period_root_def
    using \<open>u \<cdot> w \<cdot> v = u \<cdot> x\<close>[unfolded \<open>x = u \<cdot> w\<close>] \<open>u \<noteq> \<epsilon>\<close> triv_pref[of "u \<cdot> u \<cdot> w" v]
    by force
  have "periodN (u\<cdot>w\<cdot>v) \<^bold>|u\<^bold>|"
    using \<open>u \<cdot> w \<cdot> v \<le>p u \<^sup>\<omega>\<close> by auto

\<comment> \<open>Common period d\<close>
  obtain d::nat where "d=gcd \<^bold>|y\<^bold>| \<^bold>|u\<^bold>|"
    by simp
  have "\<^bold>|y\<^bold>| + \<^bold>|u\<^bold>| \<le> \<^bold>|u\<cdot>w\<cdot>v\<^bold>|" using \<open>\<^bold>|y\<^bold>| \<le> \<^bold>|x\<^bold>|\<close> length_append \<open>u\<cdot>w\<cdot>v = u\<cdot> x\<close>
    by simp
  hence "periodN (u\<cdot>w\<cdot>v) d" 
    using \<open>periodN (u \<cdot> w \<cdot> v) \<^bold>|u\<^bold>|\<close> \<open>periodN (u \<cdot> w \<cdot> v) \<^bold>|y\<^bold>|\<close> \<open>d = gcd \<^bold>|y\<^bold>| \<^bold>|u\<^bold>|\<close> two_periodsN
    by blast

\<comment> \<open>Divisibility\<close>
  have "v\<cdot>u\<cdot>z=y\<^sup>@b"
    by (simp add: \<open>y\<^sup>@b = v \<cdot> u \<cdot> w \<cdot> v \<cdot> u\<close> \<open>z = w \<cdot> v \<cdot> u\<close>)
  have "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|"
    using \<open>x = u \<cdot> w\<close> \<open>w \<cdot> v = x\<close> length_append[of u w] length_append[of w v] add.commute[of "\<^bold>|u\<^bold>|" "\<^bold>|w\<^bold>|"] add_left_cancel
    by simp
  hence "d dvd \<^bold>|v\<^bold>|" using gcd_nat.cobounded1[of "\<^bold>|v\<^bold>|" "\<^bold>|y\<^bold>|"] gcd.commute[of "\<^bold>|y\<^bold>|" "\<^bold>|u\<^bold>|"]
    by (simp add: \<open>d = gcd \<^bold>|y\<^bold>| \<^bold>|u\<^bold>|\<close>)
  have "d dvd \<^bold>|u\<^bold>|"
    by (simp add: \<open>d = gcd  \<^bold>|y\<^bold>| \<^bold>|u\<^bold>|\<close>)
  have "\<^bold>|z\<^bold>| + \<^bold>|u\<^bold>| + \<^bold>|v\<^bold>| = b*\<^bold>|y\<^bold>|"
    using  lenarg[OF \<open>v\<cdot>u\<cdot>z=y\<^sup>@b\<close>, unfolded length_append pow_len] by auto
  from dvd_add_left_iff[OF \<open>d dvd \<^bold>|v\<^bold>|\<close>, of "\<^bold>|z\<^bold>|+\<^bold>|u\<^bold>|", unfolded this dvd_add_left_iff[OF \<open>d dvd \<^bold>|u\<^bold>|\<close>, of "\<^bold>|z\<^bold>|"]]
  have "d dvd \<^bold>|z\<^bold>|" 
    using \<open>d = gcd  \<^bold>|y\<^bold>| \<^bold>|u\<^bold>|\<close> dvd_mult by blast 
  from lenarg[OF \<open>z = w \<cdot> v \<cdot> u\<close>, unfolded length_append pow_len]
  have "d dvd \<^bold>|w\<^bold>|"
    using \<open>d dvd \<^bold>|z\<^bold>|\<close>  \<open>d dvd \<^bold>|u\<^bold>|\<close> \<open>d dvd \<^bold>|v\<^bold>|\<close>  by (simp add: dvd_add_left_iff)
  hence "d dvd \<^bold>|x\<^bold>|"
    using \<open>d dvd \<^bold>|v\<^bold>|\<close> \<open>w \<cdot> v = x\<close> by force

\<comment> \<open>x and y commute\<close>
  have "x \<le>p u\<cdot>w\<cdot>v"
    by (simp add: \<open>x = u \<cdot> w\<close>)   
  have "periodN x d" using per_pref'[OF \<open>x\<noteq>\<epsilon>\<close>  \<open>periodN (u\<cdot>w\<cdot>v) d \<close> \<open>x \<le>p u \<cdot>w\<cdot>v\<close>].
  hence "x \<in> (take d x)*"
    using \<open>d dvd \<^bold>|x\<^bold>|\<close>
    using root_divisor by blast 

  hence "periodN u d " using \<open>x = u \<cdot> w\<close> per_pref'
    using \<open>periodN x d\<close> \<open>u \<noteq> \<epsilon>\<close> by blast
  have " take d x = take d u" using \<open>u\<noteq>\<epsilon>\<close>  \<open>x = u \<cdot> w\<close> pref_share_take
    by (simp add: \<open>d = gcd  \<^bold>|y\<^bold>| \<^bold>|u\<^bold>|\<close>)
  from root_divisor[OF \<open>periodN u d\<close> \<open>d dvd \<^bold>|u\<^bold>|\<close>, folded this]
  have "u \<in> (take d x)*".


  hence "z \<in> (take d x)*" 
    using \<open>x\<cdot>u=z\<close> \<open>x \<in> (take d x)*\<close> add_roots by blast
  from root_pref_cancel'[OF _ root_pow_root[OF  \<open>x \<in> take d x*\<close>, of a],of "y\<^sup>@b", unfolded eq, OF root_pow_root[OF  this, of c]]
  have "y\<^sup>@b \<in> (take d x)*". 
  from  commD[OF root_pow_root[OF  \<open>x \<in> take d x*\<close>, of a] this] 
  show "x \<cdot> y = y \<cdot> x" 
    unfolding comm_pow_roots[OF \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close>, of x y].
qed

end \<comment> \<open>locale LS\<close>

text\<open>The main proof is by induction on the length of $z$. It also uses the reverse symmetry of the equation which is 
exploited by two interpretations of the locale @{term LS}. Note also that the case $|x^a| < |y^b|$ is solved by 
using induction on $|z| + |y^b|$ instead of just on $|z|$.
\<close>

lemma Lyndon_Schutzenberger':
  "\<lbrakk> x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c;  2 \<le> a;  2 \<le> b; 2 \<le> c \<rbrakk>
  \<Longrightarrow> x\<cdot>y = y\<cdot>x"
proof (induction "\<^bold>|z\<^bold>| + b* \<^bold>|y\<^bold>|" arbitrary: x y z a b c  rule: less_induct)
  case less

  interpret LS x a y b z c using \<open> x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c\<close> \<open> 2 \<le>a \<close> \<open> 2 \<le> b\<close> \<open> 2 \<le> c\<close>
    by (simp add: LS.intro)
  interpret LSrev: LS "rev y" b "rev x" a "rev z" c 
        using  LS.intro[OF b a c, of "rev y" "rev x" "rev z", folded rev_append rev_pow, unfolded rev_is_rev_conv, OF \<open>x\<^sup>@a \<cdot> y\<^sup>@b = z\<^sup>@c\<close>].

  have leneq: "a * \<^bold>|x\<^bold>| + b*\<^bold>|y\<^bold>| = c * \<^bold>|z\<^bold>|" 
    using  eq unfolding pow_len[symmetric] length_append[symmetric] by simp
  have "a \<noteq> 0" and "b \<noteq> 0"  
    using a b by auto

  show "x \<cdot> y = y \<cdot> x"
  proof (cases "x = \<epsilon> \<or> y = \<epsilon>") 
    show "x = \<epsilon> \<or> y = \<epsilon> \<Longrightarrow> x \<cdot> y = y \<cdot> x"
      by auto
  next
    assume "\<not> (x = \<epsilon> \<or> y = \<epsilon>)" hence "x \<noteq> \<epsilon>" and "y \<noteq> \<epsilon>" by blast+
    show "x \<cdot> y = y \<cdot> x"
    proof (cases "\<^bold>|x \<^sup>@ a\<^bold>| < \<^bold>|y \<^sup>@ b\<^bold>|")

\<comment> \<open>WLOG assumption\<close>
      assume "\<^bold>|x\<^sup>@a\<^bold>| < \<^bold>|y\<^sup>@b\<^bold>|"
      have "\<^bold>|rev z\<^bold>| + a* \<^bold>|rev x\<^bold>| < \<^bold>|z\<^bold>| + b* \<^bold>|y\<^bold>|" using \<open>\<^bold>|x\<^sup>@a\<^bold>| < \<^bold>|y\<^sup>@b\<^bold>|\<close>
        by (simp add: pow_len)
      from "less.hyps"[OF this LSrev.eq b a c, symmetric]
      show "x \<cdot> y = y \<cdot> x"
        unfolding  rev_append[symmetric] rev_is_rev_conv by simp 
    next
      assume " \<not> \<^bold>|x\<^sup>@a\<^bold>| < \<^bold>|y\<^sup>@b\<^bold>|" hence "\<^bold>|y\<^sup>@b\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|" by force
          \<comment> \<open>case solved by the Periodicity lemma\<close>
      consider (with_Periodicity_lemma)
        "\<^bold>|z\<^bold>| + \<^bold>|x\<^bold>| \<le> \<^bold>|x \<^sup>@ a\<^bold>| \<or> \<^bold>|z\<^bold>| + \<^bold>|y\<^bold>| \<le> \<^bold>|y \<^sup>@ b\<^bold>|" |
        (without_Periodicity_lemma)    
        "\<^bold>|x\<^sup>@a\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|x\<^bold>|" and "\<^bold>|y\<^sup>@b\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|y\<^bold>|"
        using not_le_imp_less by blast 
      thus "x \<cdot> y = y \<cdot> x"
      proof (cases)
        case with_Periodicity_lemma
        assume short: "\<^bold>|z\<^bold>| + \<^bold>|x\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>| \<or> \<^bold>|z\<^bold>| + \<^bold>|y\<^bold>| \<le> \<^bold>|y\<^sup>@b\<^bold>|"
        have "x = \<epsilon> \<or> rev y = \<epsilon> \<Longrightarrow> x \<cdot> y = y \<cdot> x"
          by auto
        thus "x \<cdot> y = y \<cdot> x"
          using per_lemma_case LSrev.per_lemma_case short
          unfolding length_rev rev_append[symmetric] rev_is_rev_conv rev_pow[symmetric] by blast
      next
        case without_Periodicity_lemma
        assume lenx: "\<^bold>|x\<^sup>@a\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|x\<^bold>|" and leny: "\<^bold>|y\<^sup>@b\<^bold>| < \<^bold>|z\<^bold>| + \<^bold>|y\<^bold>|"
        have ex: "\<exists> k. d = Suc (Suc k)" if "2 \<le> d" for d
          using nat_le_iff_add that by auto 
        have "a * \<^bold>|x\<^bold>| + b*\<^bold>|y\<^bold>| < 4 * \<^bold>|z\<^bold>|" 
          using ex[OF \<open>2 \<le> a\<close>] ex[OF \<open>2 \<le> b\<close>] lenx leny unfolding pow_len by auto
        hence "c < 4" using leneq by auto
        consider (c_is_3) "c = 3" | (c_is_2) "c = 2"
          using \<open>c < 4\<close> c by linarith
        then show "x \<cdot> y = y \<cdot> x"
        proof(cases)
          case c_is_3 
          show "x \<cdot> y = y \<cdot> x" 
            using  
              core_case[OF \<open>c = 3\<close> \<open>\<^bold>|y\<^sup>@b\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|\<close>[unfolded pow_len] _ _ lenx[unfolded pow_len] leny[unfolded pow_len]] 
              \<open>x \<noteq> \<epsilon>\<close> \<open>y \<noteq> \<epsilon>\<close> 
            by blast
        next  
          assume "c = 2"  
          hence eq2: "x\<^sup>@a \<cdot> y\<^sup>@b = z \<cdot> z"
            by (simp add: eq pow2_list)
          from   dual_order.trans  le_cases[of "\<^bold>|x\<^sup>@a\<^bold>|" "\<^bold>|z\<^bold>|" "\<^bold>|z\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|", unfolded eq_len_iff[OF this]] 
          have "\<^bold>|z\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|" 
            using \<open>\<^bold>|y\<^sup>@b\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|\<close> by blast 
          obtain a' where "Suc a' = a" and "1 \<le> a'"
            using \<open>2 \<le> a\<close> ex by auto
          from eq2[folded \<open>Suc a' = a\<close>, unfolded pow_Suc2_list rassoc]  pow_Suc2_list[of x a', unfolded this, symmetric]
          have eq3: "x \<^sup>@ a' \<cdot> x \<cdot> y \<^sup>@ b = z \<cdot> z" and aa':"x \<^sup>@ a' \<cdot> x = x \<^sup>@ a ".
          hence "\<^bold>|x\<^sup>@a'\<^bold>| < \<^bold>|z\<^bold>|" 
            using \<open>Suc a' = a\<close> lenx pow_len by auto
          hence "\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|"  
            using  mult_le_mono[of 1 a' "\<^bold>|z\<^bold>|" "\<^bold>|x\<^bold>|", OF \<open>1 \<le> a'\<close>, THEN leD] unfolding pow_len  
            by linarith
          obtain u w where "x\<^sup>@a'\<cdot>u = z" and "w \<cdot> y\<^sup>@b = z"
            using eqd_prefE[OF eq3[unfolded rassoc] less_imp_le[OF \<open>\<^bold>|x\<^sup>@a'\<^bold>| < \<^bold>|z\<^bold>|\<close>], of thesis]
              eqd_prefE[OF eq2[symmetric]  \<open>\<^bold>|z\<^bold>| \<le> \<^bold>|x\<^sup>@a\<^bold>|\<close>, of thesis] by fast

          have "x\<^sup>@a'\<cdot>x\<cdot>y\<^sup>@b = x\<^sup>@a'\<cdot>u\<cdot>w\<cdot>y\<^sup>@b"
           unfolding lassoc  \<open>x \<^sup>@ a' \<cdot> u = z\<close> \<open>w \<cdot> y\<^sup>@b = z\<close> aa' cancel eq2 by simp 
          hence "u\<cdot>w=x"
            by auto
          hence "\<^bold>|w\<cdot>u\<^bold>| = \<^bold>|x\<^bold>|"
            using swap_len by blast

\<comment> \<open>Induction step: new equation with shorter z\<close>
          have "w\<^sup>@2\<cdot>y\<^sup>@b = (w\<cdot>u)\<^sup>@a"
            unfolding pow2_list using \<open>w \<cdot> y \<^sup>@ b = z\<close> \<open>x \<^sup>@ a' \<cdot> u = z\<close> \<open>u\<cdot>w=x\<close> pow_slide[of w u a', unfolded \<open>Suc a' = a\<close>] by simp
          from "less.hyps"[OF _ this _ b a, unfolded \<open>\<^bold>|w\<cdot>u\<^bold>| = \<^bold>|x\<^bold>|\<close>]
          have "y\<cdot>w = w\<cdot>y" 
            using  \<open>\<^bold>|x\<^bold>| < \<^bold>|z\<^bold>|\<close>  by force

          have "y \<cdot> z = z \<cdot> y"
            unfolding \<open>w \<cdot> y\<^sup>@b = z\<close>[symmetric] lassoc \<open>y\<cdot>w = w\<cdot>y\<close>
            by (simp add: pow_commutes_list)   
          hence "z\<^sup>@c\<cdot>y\<^sup>@b = y\<^sup>@b\<cdot>z\<^sup>@c"
            by (simp add: comm_add_exps) 
          from this[folded eq, unfolded lassoc]
          have "x\<^sup>@a\<cdot>y\<^sup>@b = y\<^sup>@b\<cdot>x\<^sup>@a"
            using cancel_right by blast
          from this[unfolded comm_pow_roots[OF \<open>a\<noteq>0\<close> \<open>b \<noteq> 0\<close>]]
          show "x \<cdot> y = y \<cdot> x".
        qed
      qed
    qed
  qed
qed

theorem Lyndon_Schutzenberger:
  assumes "x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c" and  "2 \<le> a"  and "2 \<le> b" and "2 \<le> c"
  shows  "x\<cdot>y = y\<cdot>x" and "x\<cdot>z = z\<cdot>x" and "y\<cdot>z = z\<cdot>y"
proof-
  show "x \<cdot> y = y \<cdot> x"
    using Lyndon_Schutzenberger'[OF assms].
  have "c \<noteq> 0" and  "b \<noteq> 0" using  \<open>2 \<le> c\<close> \<open>2 \<le> b\<close> by auto
  have "x \<cdot> x\<^sup>@a \<cdot> y\<^sup>@b = x\<^sup>@a \<cdot> y\<^sup>@b \<cdot> x" and "y \<cdot> x\<^sup>@a \<cdot> y\<^sup>@b = x\<^sup>@a \<cdot> y\<^sup>@b \<cdot> y"
    unfolding comm_add_exp[OF \<open>x \<cdot> y = y \<cdot> x\<close>[symmetric], of b] comm_add_exp[OF \<open>x \<cdot> y = y \<cdot> x\<close>, symmetric, of a]
    lassoc power_commutes by blast+ 
  thus "x\<cdot>z = z\<cdot>x" and "y\<cdot>z = z\<cdot>y"
    using comm_drop_exp[OF \<open>c \<noteq> 0\<close>] unfolding lassoc \<open>x\<^sup>@a\<cdot>y\<^sup>@b = z\<^sup>@c\<close> by force+
qed

end