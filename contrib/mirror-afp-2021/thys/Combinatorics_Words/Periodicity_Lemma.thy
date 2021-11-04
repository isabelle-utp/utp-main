(*  Title:      CoW/Periodicity_Lemma.thy
    Author:     Štěpán Holub, Charles University
*)

theory Periodicity_Lemma
  imports CoWBasic
begin

chapter "The Periodicity Lemma"

text\<open>The Periodicity Lemma says that if a sufficiently long word has two periods p and q, 
then the period can be refined to @{term "gcd p q"}. 
The consequence is equivalent to the fact that the corresponding periodic roots commute. 
``Sufficiently long'' here means at least @{term "p + q - gcd p q"}.
It is also known as the Fine and Wilf theorem due to its authors @{cite FineWilf}.\<close>

text\<open>
If we relax the requirement to @{term "p + q"}, then the claim becomes easy, and it is proved in theory @{theory Combinatorics_Words.CoWBasic} as @{term two_pers}: @{thm[names_long] two_pers[no_vars]}.
\<close>

theorem per_lemma_relaxed:
  assumes "periodN w p" and  "periodN w q" and  "p + q \<le> \<^bold>|w\<^bold>|"
  shows "(take p w)\<cdot>(take q w) = (take q w)\<cdot>(take p w)"
  using   two_pers[OF
      \<open>periodN w p\<close>[unfolded periodN_def[of w p]]
      \<open>periodN w q\<close>[unfolded periodN_def[of w q]], unfolded    
      take_len[OF add_leD1[OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]] 
      take_len[OF add_leD2[OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]], OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]. 

text\<open>Also in terms of the numeric period:\<close>

thm two_periodsN

section \<open>Main claim\<close>

text\<open>We first formulate the claim of the Periodicity lemma in terms of commutation of two periodic roots.
For trivial reasons we can also drop the requirement that the roots are nonempty.
\<close>
lemma per_lemma_comm:
  assumes "w \<le>p r \<cdot> w" and "w \<le>p s \<cdot> w" 
    and len: "\<^bold>|s\<^bold>| + \<^bold>|r\<^bold>| - (gcd \<^bold>|s\<^bold>| \<^bold>|r\<^bold>|) \<le> \<^bold>|w\<^bold>|"
  shows "s \<cdot> r = r \<cdot> s"
  using assms
proof (induction "\<^bold>|s\<^bold>| + \<^bold>|s\<^bold>| + \<^bold>|r\<^bold>|" arbitrary: w r s rule: less_induct)
  case less
  consider (empty) "s = \<epsilon>" | (short)  "\<^bold>|r\<^bold>| < \<^bold>|s\<^bold>|" | (step) "s \<noteq> \<epsilon> \<and> \<^bold>|s\<^bold>| \<le> \<^bold>|r\<^bold>|" by force
  then show ?case 
  proof (cases)
    case (empty) 
    thus "s \<cdot> r = r \<cdot> s" by fastforce
  next
    case (short)
    thus "s \<cdot> r = r \<cdot> s"
      using  "less.hyps"[OF  _ \<open> w \<le>p s \<cdot> w\<close> \<open> w \<le>p r \<cdot> w\<close> 
      \<open>\<^bold>|s\<^bold>| + \<^bold>|r\<^bold>| - (gcd \<^bold>|s\<^bold>| \<^bold>|r\<^bold>|) \<le> \<^bold>|w\<^bold>|\<close>[unfolded gcd.commute[of "\<^bold>|s\<^bold>|"] add.commute[of "\<^bold>|s\<^bold>|"]]] by fastforce
   next
     case (step)
    hence  "s \<noteq> \<epsilon>" and "\<^bold>|s\<^bold>| \<le> \<^bold>|r\<^bold>|" by blast+
    from le_add_diff[OF gcd_le2_nat[OF \<open>s \<noteq> \<epsilon>\<close>[folded length_0_conv], of "\<^bold>|r\<^bold>|"], unfolded gcd.commute[of "\<^bold>|r\<^bold>|"]]
    have "\<^bold>|r\<^bold>| \<le> \<^bold>|w\<^bold>|" 
      using  \<open>\<^bold>|s\<^bold>| + \<^bold>|r\<^bold>| - (gcd \<^bold>|s\<^bold>| \<^bold>|r\<^bold>|) \<le> \<^bold>|w\<^bold>|\<close> order.trans by fast
    hence "\<^bold>|s\<^bold>| \<le> \<^bold>|w\<^bold>|"
      using \<open>\<^bold>|s\<^bold>| \<le> \<^bold>|r\<^bold>|\<close> order.trans by blast
    from pref_prod_long[OF  \<open>w \<le>p s \<cdot> w\<close> this] 
    have "s \<le>p w".
    
    obtain w' where "s \<cdot> w' = w" and "\<^bold>|w'\<^bold>| < \<^bold>|w\<^bold>|" using \<open>s \<noteq> \<epsilon>\<close> \<open>s \<le>p w\<close> by auto
    have "w' \<le>p w"
      using \<open>w \<le>p s \<cdot> w\<close> unfolding \<open>s \<cdot> w' = w\<close>[symmetric] pref_cancel_conv.
    from this[folded \<open>s \<cdot> w' = w\<close>]
    have "w' \<le>p s\<cdot>w'".

    have "s \<le>p r"
      using pref_prod_short[OF prefix_order.order.trans[OF \<open>s \<le>p w\<close> \<open>w \<le>p r \<cdot> w\<close>] \<open>\<^bold>|s\<^bold>| \<le> \<^bold>|r\<^bold>|\<close>].
    hence  "w' \<le>p (s\<inverse>\<^sup>>r) \<cdot> w'"
      using \<open>w \<le>p r \<cdot> w\<close> \<open>s \<cdot> w' = w\<close> pref_prod_pref[OF _ \<open>w' \<le>p w\<close>, of "s\<inverse>\<^sup>>r"]  by fastforce

    have ind_len: "\<^bold>|s\<^bold>| + \<^bold>|s\<inverse>\<^sup>>r\<^bold>| - (gcd \<^bold>|s\<^bold>| \<^bold>|s\<inverse>\<^sup>>r\<^bold>|) \<le> \<^bold>|w'\<^bold>|"
      using \<open>\<^bold>|s\<^bold>| + \<^bold>|r\<^bold>| - (gcd \<^bold>|s\<^bold>| \<^bold>|r\<^bold>|) \<le> \<^bold>|w\<^bold>|\<close> \<open>s \<cdot> w' = w\<close> \<open>s \<le>p r\<close> by auto

    have "s \<cdot> s\<inverse>\<^sup>>r = s\<inverse>\<^sup>>r \<cdot> s" 
      using "less.hyps"[OF  _ \<open>w' \<le>p (s\<inverse>\<^sup>>r) \<cdot> w'\<close>  \<open>w' \<le>p s \<cdot> w'\<close> ind_len] \<open>s \<le>p r\<close> \<open>\<^bold>|w'\<^bold>| < \<^bold>|w\<^bold>|\<close>  by force 

    thus "s \<cdot> r = r \<cdot> s"
       using \<open>s \<le>p r\<close> by auto
  qed 
qed

text\<open>We can now prove the numeric version.\<close>

theorem per_lemma: assumes "periodN w p" and "periodN w q" and len: "p + q - gcd p q \<le> \<^bold>|w\<^bold>|"
  shows  "periodN w (gcd p q)"
proof-
  have takep: "w \<le>p (take p w) \<cdot> w" and takeq: "w \<le>p (take q w) \<cdot> w"
    using \<open>periodN w p\<close> \<open>periodN w q\<close> periodN_D3 by blast+
  have lenp: "\<^bold>|take p w\<^bold>| = p"
    using gcd_le2_nat[OF per_positive[OF \<open>periodN w q\<close>], of p] len take_len
    by auto
  have lenq: "\<^bold>|take q w\<^bold>| = q"
    using gcd_le1_nat[OF per_positive[OF \<open>periodN w p\<close>], of q] len take_len
    by simp
  obtain t where "take p w \<in> t*" and "take q w \<in> t*" 
    using comm_rootE[OF per_lemma_comm[OF takeq takep, unfolded lenp lenq, OF len], of thesis] by blast
  hence "w \<le>p t\<^sup>\<omega>"
    using \<open>periodN w p\<close> periodN_def per_root_trans by blast
  have "periodN w \<^bold>|t\<^bold>|"
    using  root_periodN[OF  per_nemp[OF \<open>periodN w p\<close>] \<open>w \<le>p t\<^sup>\<omega>\<close>]. 
  have "\<^bold>|t\<^bold>| dvd (gcd p q)"
    using  common_root_len_gcd[OF \<open>take p w \<in> t*\<close> \<open>take q w \<in> t*\<close>] unfolding  lenp lenq.
  from dvd_div_mult_self[OF this]
  have "gcd p q div \<^bold>|t\<^bold>| * \<^bold>|t\<^bold>| = gcd p q".
  have "gcd p q \<noteq> 0"
    using \<open>periodN w p\<close> by auto 
  from this[folded dvd_div_eq_0_iff[OF \<open>\<^bold>|t\<^bold>| dvd (gcd p q)\<close>]]
  show "periodN w (gcd p q)"
    using  per_mult[OF \<open>periodN w \<^bold>|t\<^bold>|\<close>, of "gcd p q div \<^bold>|t\<^bold>|", unfolded dvd_div_mult_self[OF \<open>\<^bold>|t\<^bold>| dvd (gcd p q)\<close>]] by blast
qed

section \<open>Optimality\<close>

text\<open>@{term "FW_word"} (where FW stands for  Fine and Wilf) yields a word which show the optimality of the bound in the Periodicity lemma. 
    Moreover, the obtained word has maximum possible letters (each equality of letters is forced by periods). The latter is not proved here.\<close>

term "butlast ([0..<(gcd p q)]\<^sup>@(p div (gcd p q)))\<cdot>[gcd p q]\<cdot>(butlast ([0..<(gcd p q)]\<^sup>@(p div (gcd p q))))"

\<comment> \<open>an auxiliary claim\<close>
lemma ext_per_sum: assumes "periodN w p" and "periodN w q" and  "p \<le> \<^bold>|w\<^bold>|" 
  shows "periodN ((take p w) \<cdot> w) (p+q)"
proof-
  have nemp: "take p w \<cdot> take q w \<noteq> \<epsilon>"
    using \<open>periodN w p\<close> by auto
  have "take (p + q) (take p w \<cdot> w) = take p (take p w \<cdot> w) \<cdot> take q (drop p (take p w \<cdot> w))"
    using take_add by blast
  also have "... = take p w \<cdot> take q w"
    by (simp add: \<open>p \<le> \<^bold>|w\<^bold>|\<close>)
  ultimately have sum: "take (p + q) (take p w \<cdot> w) = take p w \<cdot> take q w"
    by simp
  show ?thesis
    using assms(1) assms(2) nemp
    unfolding periodN_def period_root_def sum rassoc same_prefix_prefix
    using pref_prolong  by blast
qed

abbreviation "fw_p_per p q \<equiv> butlast ([0..<(gcd p q)]\<^sup>@(p div (gcd p q)))"
abbreviation "fw_base p q \<equiv> fw_p_per p q \<cdot> [gcd p q]\<cdot> fw_p_per p q"

fun FW_word :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  FW_word_def: "FW_word p q =  
\<comment>\<open>symmetry\<close>           (if q < p then  FW_word q p else 
\<comment>\<open>artificial value\<close>   if p = 0 \<or> p = q then \<epsilon> else 
\<comment>\<open>base case\<close>          if gcd p q = q - p then fw_base p q
\<comment>\<open>step\<close>               else (take p (FW_word p (q-p))) \<cdot> FW_word p (q-p)    )"

lemma FW_sym: "FW_word p q = FW_word q p"
  by (cases rule: linorder_cases[of p q], simp+)

theorem fw_word': "\<not> p dvd q \<Longrightarrow> \<not> q dvd p \<Longrightarrow>
 \<^bold>|FW_word p q\<^bold>| = p + q - gcd p q - 1 \<and> periodN (FW_word p q) p \<and> periodN (FW_word p q) q \<and> \<not> periodN (FW_word p q) (gcd p q)"
proof (induction "p + p + q" arbitrary: p q rule: less_induct)
  case less
  have "p \<noteq> 0"
    using  \<open>\<not> q dvd p\<close> dvd_0_right[of q] by meson 
  have "p \<noteq> q"
    using \<open>\<not> p dvd q\<close> by auto
  then consider "q < p" | "p < q" 
    by linarith
  then show ?case 
  proof (cases)
    assume "q < p"
    have less: "q + q + p < p + p + q"
      by (simp add: \<open>q < p\<close>)
    thus ?case
      using "less.hyps"[OF _ \<open>\<not> q dvd p\<close> \<open>\<not> p dvd q\<close>] 
      unfolding FW_sym[of p q] gcd.commute[of p q] add.commute[of p q] by blast             
  next
    let ?d = "gcd p q"
    let ?dw = "[0..<(gcd p q)]"
    let ?pd = "p div (gcd p q)"
    assume "p < q" 
    thus ?thesis
    proof (cases "?d = q - p")
      assume "?d = q - p" hence "p + ?d = q" using \<open>p < q\<close> by auto
      have fw: "FW_word p q = fw_base p q"
        using FW_word_def \<open>p \<noteq> 0\<close> \<open>gcd p q = q - p\<close> \<open>p < q\<close> by auto 

      have ppref: "\<^bold>|butlast (?dw\<^sup>@?pd)\<cdot>[?d]\<^bold>| = p"
        using length_append \<open>p \<noteq> 0\<close> pow_len[of "?dw" "?pd"]
        by auto
      note ppref' = this[unfolded length_append]
      have qpref: "\<^bold>|butlast (?dw\<^sup>@?pd)\<cdot>[?d]\<cdot>?dw\<^bold>| = q"
        unfolding lassoc length_append ppref' using  \<open>p + gcd p q = q\<close> by simp   
      have "butlast (?dw\<^sup>@?pd)\<cdot>[?d] \<le>p FW_word p q"
        unfolding fw by force
      from pref_take[OF this]
      have takep: "take p (FW_word p q) = butlast (?dw\<^sup>@?pd)\<cdot>[?d]"
        unfolding ppref.

      have "?dw \<noteq> \<epsilon>" and "\<^bold>|?dw\<^bold>| = ?d"
        using \<open>p \<noteq> 0\<close> by auto
      have "?pd \<noteq> 0"
        by (simp add: \<open>p \<noteq> 0\<close> dvd_div_eq_0_iff) 
      from not0_implies_Suc[OF this]
      obtain e where "?pd = Suc e"  by blast
      have "gcd p q \<noteq> p"
        using \<open>\<not> p dvd q\<close> gcd_dvd2[of p q] by force     
      hence "Suc e \<noteq> 1"
        using dvd_mult_div_cancel[OF gcd_dvd1[of p q], unfolded \<open>?pd = Suc e\<close>] by force
      hence "e \<noteq> 0" by simp

      have "[0..<gcd p q] \<^sup>@ e \<noteq> \<epsilon>"
        using \<open>[0..<gcd p q] \<noteq> \<epsilon>\<close> \<open>e \<noteq> 0\<close> nonzero_pow_emp by blast
      hence but_dec: "butlast (?dw\<^sup>@?pd) = ?dw \<cdot> butlast (?dw\<^sup>@e)"
        unfolding \<open>?pd = Suc e\<close> pow_Suc_list butlast_append  if_not_P[OF \<open>[0..<gcd p q] \<^sup>@ e \<noteq> \<epsilon>\<close>] by blast
      have but_dec_b: "butlast (?dw\<^sup>@?pd) = ?dw\<^sup>@e \<cdot> butlast ?dw" 
        unfolding \<open>?pd = Suc e\<close> pow_Suc2_list butlast_append if_not_P[OF \<open>?dw \<noteq> \<epsilon>\<close>] by blast
      have "butlast (?dw\<^sup>@?pd)\<cdot>[?d]\<cdot>?dw \<le>p FW_word p q"
        using fw but_dec by auto
      note takeq = pref_take[OF this, unfolded qpref]

      have "\<^bold>|FW_word p q\<^bold>| = p + q - gcd p q - 1"
      proof-
        have "\<^bold>|?dw\<^bold>| = ?d"
          by auto
        have "gcd p q dvd p"
          by auto
        hence "\<^bold>|?dw\<^sup>@?pd\<^bold>| = p"
          using pow_len[of "?dw" "?pd"]
          by auto
        hence "\<^bold>|butlast (?dw\<^sup>@?pd)\<^bold>| = p - 1"
          by simp
        hence "\<^bold>|FW_word p q\<^bold>| = (p - 1) + 1 +  (p - 1)"
          using fw unfolding length_append
          by auto
        thus "\<^bold>|FW_word p q\<^bold>| = p + q - gcd p q - 1"
          unfolding \<open>gcd p q = q - p\<close> using \<open>p + gcd p q = q\<close> \<open>p \<noteq> 0\<close> add.assoc by auto
      qed    

      have "periodN (FW_word p q) p"
      proof-
        have "take p (FW_word p q) \<noteq> \<epsilon>"
          using \<open>p \<noteq> 0\<close>  unfolding length_0_conv[symmetric] ppref[folded takep].
        thus "periodN (FW_word p q) p"
          unfolding periodN_def period_root_def  takep unfolding fw lassoc by auto
      qed

      have "periodN (FW_word p q) q"
        unfolding periodN_def period_root_def 
      proof
        show "take q (FW_word p q) \<noteq> \<epsilon>"
          unfolding length_0_conv[symmetric] qpref[folded takeq] using \<open>p \<noteq> 0\<close> \<open>p < q\<close> by linarith
      next
        show "FW_word p q \<le>p take q (FW_word p q) \<cdot> FW_word p q"
          unfolding takeq 
          unfolding fw rassoc pref_cancel_conv but_dec but_dec_b \<open>?pd = Suc e\<close> pow_Suc2_list butlast_append pow_Suc_list if_not_P[OF \<open>?dw \<noteq> \<epsilon>\<close>]
          unfolding lassoc power_commutes[symmetric] unfolding rassoc pref_cancel_conv
          using pref_ext[OF prefixeq_butlast, of "?dw"] by blast 
      qed

      have "\<not> periodN (FW_word p q) ?d"
      proof-
        have last_a: "last (take p (FW_word p q)) = ?d"
          unfolding takep nth_append_length[of "butlast (?dw \<^sup>@ ?pd)" "?d" \<epsilon>]
            last_snoc by blast
        have "?dw \<le>p FW_word p q"
          using fw but_dec  by simp
        from pref_take[OF this, unfolded \<open>\<^bold>|?dw\<^bold>| = ?d\<close>]
        have takegcd:  "take (gcd p q) (FW_word p q) = [0..<gcd p q]".
        have fw_dec_b: "FW_word p q = [0..<gcd p q]\<^sup>@e \<cdot> butlast ([0..<gcd p q]) \<cdot> [?d] \<cdot> (butlast ([0..<gcd p q]\<^sup>@(p div gcd p q)))"
          using fw but_dec_b  by simp
        hence gcdepref:  "[0..<gcd p q]\<^sup>@ Suc e \<le>p take (gcd p q) (FW_word p q) \<cdot> FW_word p q"
          using takegcd  by simp
        have "\<^bold>|[0..<gcd p q]\<^sup>@ Suc e\<^bold>| = p"
          unfolding pow_len \<open>\<^bold>|?dw\<^bold>| = ?d\<close> \<open>?pd = Suc e\<close>[symmetric] using  
            dvd_div_mult_self[OF gcd_dvd1].
        from pref_take[OF gcdepref, unfolded this] 
        have takegcdp:  "take p (take (gcd p q) (FW_word p q) \<cdot> (FW_word p q)) = [0..<gcd p q]\<^sup>@e \<cdot> [0..<gcd p q]"
          unfolding pow_Suc2_list.  
        have "0 < gcd p q" by (simp add: \<open>p \<noteq> 0\<close>)
        from last_upt[OF this]
        have last_b: "last (take p (take (gcd p q) (FW_word p q) \<cdot> (FW_word p q))) = gcd p q - 1"
          unfolding takegcdp  last_appendR[of "[0..<gcd p q]" "[0..<gcd p q]\<^sup>@e", OF \<open>[0..<gcd p q] \<noteq> \<epsilon>\<close>].
        have "p \<le> \<^bold>|FW_word p q\<^bold>|"
          using \<open>\<^bold>|FW_word p q\<^bold>| = p + q - gcd p q - 1\<close> \<open>gcd p q = q - p\<close> \<open>p < q\<close> by linarith 
        have "gcd p q \<noteq> gcd p q - 1"
          using \<open>gcd p q = q - p\<close> \<open>p < q\<close> by linarith
        hence "take p (FW_word p q) \<noteq> take p (take (gcd p q) (FW_word p q) \<cdot> (FW_word p q))"
          unfolding last_b[symmetric] unfolding last_a[symmetric] using arg_cong[of _ _ last] by blast
        hence "\<not> FW_word p q \<le>p take (gcd p q) (FW_word p q) \<cdot> FW_word p q " 
          using pref_share_take[OF _ \<open>p \<le> \<^bold>|FW_word p q\<^bold>|\<close>, of "take (gcd p q) (FW_word p q) \<cdot> FW_word p q"] by blast
        thus "\<not> periodN (FW_word p q) (gcd p q)" 
          unfolding periodN_def period_root_def by blast
      qed          

      show ?thesis
        using \<open>periodN (FW_word p q) p\<close> \<open>periodN (FW_word p q) q\<close>
          \<open>\<^bold>|FW_word p q\<^bold>| = p + q - gcd p q - 1\<close> \<open>\<not> periodN (FW_word p q) (gcd p q)\<close> by blast
    next
      let ?d' = "gcd p (q-p)" 
      assume "gcd p q \<noteq> q - p"
      hence fw: "FW_word p q = (take p (FW_word p (q-p))) \<cdot> FW_word p (q-p)" 
        using FW_word_def \<open>p \<noteq> 0\<close> \<open>p \<noteq> q\<close> \<open>p < q\<close> by (meson less_Suc_eq not_less_eq)

      have divhyp1: "\<not> p dvd q - p"
        using \<open>\<not> p dvd q\<close> \<open>p < q\<close> dvd_minus_self by auto

      have divhyp2: "\<not> q - p dvd p"
      proof (rule notI)
        assume "q - p dvd p"
        have "q = p + (q - p)"
          by (simp add: \<open>p < q\<close> less_or_eq_imp_le)
        from gcd_add2[of p "q - p", folded  this, unfolded gcd_nat.absorb2[of "q - p" p, OF \<open>q - p dvd p\<close>]] 
        show "False"
          using \<open>gcd p q \<noteq> q - p\<close> by blast
      qed

      have lenhyp: "p + p + (q - p) < p + p + q"
        using \<open>p < q\<close> \<open>p \<noteq> 0\<close> by linarith 

\<comment> \<open>induction assumption\<close>      
      have "\<^bold>|FW_word p (q - p)\<^bold>| = p + (q - p) - ?d' - 1" and "periodN (FW_word p (q-p)) p" and "periodN (FW_word p (q-p)) (q-p)" and
        "\<not> periodN (FW_word p (q-p)) (gcd p (q-p))" 
        using "less.hyps"[OF _ divhyp1 divhyp2] lenhyp
        by blast+ 

\<comment> \<open>auxiliary facts\<close>
      have "p + (q - p) = q"
         using divhyp1 dvd_minus_self by auto
      have "?d = ?d'"
        using  gcd_add2[of p "q-p", unfolded le_add_diff_inverse[OF less_imp_le[OF \<open>p < q\<close>]]].
      have "?d \<noteq> q"
        using  \<open>\<not> q dvd p\<close>  gcd_dvd2[of q p, unfolded gcd.commute[of q]] by force
      from this[unfolded nat_neq_iff]
      have "?d < q"
        using  gr_implies_not0 \<open>p < q\<close> nat_dvd_not_less by blast
      hence "1 \<le> q - ?d"
        by linarith
      have "?d' < q - p"
        using  gcd_le2_nat[OF per_positive[OF \<open>periodN (FW_word p (q - p)) (q - p)\<close>], of p]  divhyp2[unfolded  gcd_nat.absorb_iff2] nat_less_le by blast
      hence "p \<le> \<^bold>|(FW_word p (q - p))\<^bold>|"
        unfolding  \<open>\<^bold>|FW_word p (q - p)\<^bold>| = p + (q - p) - ?d' - 1\<close>  diff_diff_left discrete by linarith
      have "FW_word p (q - p) \<noteq> \<epsilon>" 
        unfolding length_0_conv[symmetric] using  \<open>p \<le> \<^bold>|FW_word p (q - p)\<^bold>|\<close> \<open>p \<noteq> 0\<close>[folded le_zero_eq] 
        by linarith

\<comment> \<open>claim 1\<close>
      have "\<^bold>|FW_word p q\<^bold>| = p + q - ?d - 1" 
      proof-
        have "\<^bold>|FW_word p q\<^bold>| = \<^bold>|take p (FW_word p (q - p))\<^bold>| + \<^bold>|FW_word p (q - p)\<^bold>|"
          using fw length_append[of "take p (FW_word p (q - p))" "FW_word p (q - p)"]
          by presburger
        also have "... = p + (p + (q - p) - ?d' - 1)"
          unfolding \<open>\<^bold>|FW_word p (q - p)\<^bold>| = p + (q - p) - ?d' - 1\<close> 
            take_len[OF \<open>p \<le> \<^bold>|FW_word p (q - p)\<^bold>|\<close>] by blast
        also have "... = p + (q - ?d  - 1)"
          unfolding \<open>?d = ?d'\<close> using  \<open>p < q\<close> by auto
        also have "... = p + (q - ?d) - 1"
          using Nat.add_diff_assoc[OF \<open>1 \<le> q - ?d\<close>].
        also have "... = p + q - ?d - 1"
          by (simp add: \<open>?d < q\<close> less_or_eq_imp_le)
        finally show "\<^bold>|FW_word p q\<^bold>| = p + q - ?d - 1" 
          by presburger
      qed

\<comment> \<open>claim 2\<close>
      have "periodN (FW_word p q) p"
        using fw  ext_per_left[OF \<open>periodN (FW_word p (q-p)) p\<close> \<open>p \<le> \<^bold>|FW_word p (q - p)\<^bold>|\<close>]
        by presburger

\<comment> \<open>claim 3\<close>
      have "periodN (FW_word p q) q"
        using ext_per_sum[OF \<open>periodN (FW_word p (q - p)) p\<close> \<open>periodN (FW_word p (q - p)) (q - p)\<close> \<open>p \<le> \<^bold>|FW_word p (q - p)\<^bold>|\<close>, folded fw, unfolded \<open>p + (q-p) = q\<close>].

\<comment> \<open>claim 4\<close>
      have "\<not> periodN (FW_word p q) ?d"                   
        using \<open>\<not> periodN (FW_word p (q -p)) (gcd p (q-p))\<close> 
        unfolding \<open>?d = ?d'\<close>[symmetric]  
        using periodN_fac[of "take p (FW_word p (q - p))" "FW_word p (q - p)" \<epsilon> "?d", unfolded append_Nil2, 
                          OF _ \<open>FW_word p (q - p) \<noteq> \<epsilon>\<close>, folded fw] by blast
      thus ?thesis
        using \<open>periodN (FW_word p q) p\<close> \<open>periodN (FW_word p q) q\<close> \<open>\<^bold>|FW_word p q\<^bold>| = p + q - ?d - 1\<close> by blast 
    qed
  qed
qed

theorem fw_word: assumes "\<not> p dvd q" "\<not> q dvd p"
  shows "\<^bold>|FW_word p q\<^bold>| = p + q - gcd p q - 1" and "periodN (FW_word p q) p" and  "periodN (FW_word p q) q" and "\<not> periodN (FW_word p q) (gcd p q)"
  using fw_word'[OF assms] by blast+

text\<open>Calculation examples\<close>

value "FW_word 3 7"
value "FW_word 5 7"
value "FW_word 5 13"
value "FW_word 4 6"
value "FW_word 12 18"

section "Other variants of the periodicity lemma"

text \<open>Periodicity lemma is one of the most frequent tools in Combinatorics on words.
   Here are some useful variants.\<close>

lemma fac_two_conjug_prim_root:
  assumes facs: "u \<le>f r\<^sup>@k" "u \<le>f s\<^sup>@l" and nemps: "r \<noteq> \<epsilon>" "s \<noteq> \<epsilon>" and len: "\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| - gcd (\<^bold>|r\<^bold>|) (\<^bold>|s\<^bold>|) \<le> \<^bold>|u\<^bold>|"
  shows "\<rho> r \<sim> \<rho> s"
proof -
  obtain r' s' where prefr': "u \<le>p r'\<^sup>@k" and prefs': "u \<le>p s'\<^sup>@l"
               and   conjugs: "r \<sim> r'" "s \<sim> s'"
    using facs by (elim fac_pow_pref_conjug)
  have rootr': "u \<le>p r' \<cdot> u" and roots': "u \<le>p s' \<cdot> u"
    using pref_prod_root[OF prefr'] pref_prod_root[OF prefs']. 
  have nemps': "r' \<noteq> \<epsilon>" "s'\<noteq> \<epsilon>" using nemps conjugs conjug_nemp_iff by blast+
  have "\<^bold>|r'\<^bold>| + \<^bold>|s'\<^bold>| - gcd (\<^bold>|r'\<^bold>|) (\<^bold>|s'\<^bold>|) \<le> \<^bold>|u\<^bold>|" using len
    unfolding conjug_len[OF \<open>r \<sim> r'\<close>] conjug_len[OF \<open>s \<sim> s'\<close>].
  from per_lemma_comm[OF roots' rootr' this]  have "r' \<cdot> s' = s' \<cdot> r'".
  then have "\<rho> r' = \<rho> s'" using comm_primroots[OF nemps'] by force 
  also have "\<rho> s \<sim> \<rho> s'" using conjug_prim_root[OF \<open>s \<sim> s'\<close> \<open>s \<noteq> \<epsilon>\<close>].
  also have [symmetric]: "\<rho> r \<sim> \<rho> r'" using conjug_prim_root[OF \<open>r \<sim> r'\<close> \<open>r \<noteq> \<epsilon>\<close>].
  finally show "\<rho> r \<sim> \<rho> s"..
qed

lemma fac_two_conjug_prim_root':
  assumes facs: "u \<le>f r\<^sup>@k" "u \<le>f s\<^sup>@l" and "u \<noteq> \<epsilon>" and len: "\<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| - gcd (\<^bold>|r\<^bold>|) (\<^bold>|s\<^bold>|) \<le> \<^bold>|u\<^bold>|"
  shows "\<rho> r \<sim> \<rho> s"
proof -
  have nemps: "r \<noteq> \<epsilon>" "s \<noteq> \<epsilon>" using facs \<open>u \<noteq> \<epsilon>\<close> by auto
  show "conjugate (\<rho> r) (\<rho> s)" using fac_two_conjug_prim_root[OF facs nemps len].
qed

lemma fac_two_nconj_prim_pow:
  assumes prims: "primitive r" "primitive s" and "\<not> r \<sim> s"
      and facs: "u \<le>f r\<^sup>@k" "u \<le>f s\<^sup>@l"
  shows "\<^bold>|u\<^bold>| < \<^bold>|r\<^bold>| + \<^bold>|s\<^bold>| - gcd (\<^bold>|r\<^bold>|) (\<^bold>|s\<^bold>|)"
  using \<open>\<not> r \<sim> s\<close> fac_two_conjug_prim_root[OF facs prim_nemp prim_nemp leI, OF prims]
  unfolding prim_self_root[OF \<open>primitive r\<close>] prim_self_root[OF \<open>primitive s\<close>]
  by (rule contrapos_np)

end
