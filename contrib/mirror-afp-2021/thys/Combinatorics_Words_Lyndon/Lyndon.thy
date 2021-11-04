(*  Title:      CoW_Lyndon.Lyndon
    Author:     Štěpán Holub, Charles University
    Author:     Štěpán Starosta, CTU in Prague
*)
theory Lyndon
  imports Combinatorics_Words.CoWBasic
begin

chapter "Lyndon words"

text\<open>A Lyndon word is a non-empty word that is lexicographically 
strictly smaller than any other word in its conjugacy class, i.e., than any its rotations.
They are named after R. Lyndon who introduced them in @{cite Lyndon54} as ``standard'' sequences.

We present elementary results on Lyndon words, mostly covered by results in @{cite \<open>Chapter 5\<close> Lo83
} and @{cite Duval80 and Duval83}.

This definition assumes a linear order on letters given by the context.
\<close>


section "Definition and elementary properties"

subsection "Underlying order"

lemma (in linorder) lexordp_mid_pref: "ord_class.lexordp u v \<Longrightarrow> ord_class.lexordp v (u\<cdot>s) \<Longrightarrow>
   u \<le>p v"
  by (induct rule: lexordp_induct, simp_all)

lemma (in linorder) lexordp_ext: "ord_class.lexordp u v \<Longrightarrow>  \<not> u \<le>p v \<Longrightarrow> 
  ord_class.lexordp (u\<cdot>w) (v\<cdot>z)"
  by (induct rule: lexordp_induct, simp_all)                         

lemmas [code] = lexordp_simps

context linorder
begin

abbreviation Lyndon_less :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infixl "<lex" 50)
  where "Lyndon_less xs ys \<equiv> ord_class.lexordp xs ys"

abbreviation Lyndon_le :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infixl "\<le>lex" 50)
  where "Lyndon_le xs ys \<equiv> ord_class.lexordp_eq xs ys"

interpretation rlex: linorder "(\<le>lex)" "(<lex)" 
  using lexordp_linorder.

interpretation dual_rlex: linorder "\<lambda> x y. y \<le>lex x" "\<lambda> x y. y <lex x" 
  using rlex.dual_linorder.

lemma sorted_dual_rev_iff: "dual_rlex.sorted ws \<longleftrightarrow> rlex.sorted (rev ws)"
  unfolding rlex.sorted_rev_iff_nth_mono dual_rlex.sorted_iff_nth_mono by blast 

text \<open>Several useful lemmas that are formulated for relations, interpreted for the default linear order.\<close>

lemmas lexord_suf_linorder = lexord_sufE[of _ _ _ _ "{(x, y). x < y}", folded lexordp_conv_lexord]
  and lexord_append_leftI_linorder = lexord_append_leftI[of  _ _  "{(x, y). x < y}" _, folded lexordp_conv_lexord]
  and lexord_app_right_linorder = lexord_sufI[of  _ _  "{(x, y). x < y}" _, folded lexordp_conv_lexord]
  and lexord_take_index_conv_linorder = lexord_take_index_conv[of  _ _  "{(x, y). x < y}", folded lexordp_conv_lexord]
  and mismatch_lexord_linorder = mismatch_lexord[of  _ _  "{(x, y). x < y}", folded lexordp_conv_lexord]
  and lexord_cancel_right_linorder = lexord_cancel_right[of _ _ _ _ "{(a,b). a < b}", folded lexordp_conv_lexord]

subsection "Lyndon word definition"

fun Lyndon :: "'a list \<Rightarrow> bool"
  where "Lyndon w = (w \<noteq> \<epsilon> \<and> (\<forall>n. 0 < n \<and> n < \<^bold>|w\<^bold>| \<longrightarrow> w <lex rotate n w))"

lemma LyndonD: "Lyndon w \<Longrightarrow> 0 < n \<Longrightarrow> n < \<^bold>|w\<^bold>| \<Longrightarrow> w <lex rotate n w"
  unfolding Lyndon.simps by blast

lemma LyndonD_nemp: "Lyndon w \<Longrightarrow> w \<noteq> \<epsilon>"
  unfolding Lyndon.simps by blast

lemma LyndonI: "w \<noteq> \<epsilon> \<Longrightarrow> \<forall> n. 0 < n \<and> n < \<^bold>|w\<^bold>| \<longrightarrow> w <lex rotate n w \<Longrightarrow>  Lyndon w"
  unfolding  Lyndon.simps by blast

lemma Lyndon_sing: "Lyndon [a]" 
  unfolding Lyndon.simps by auto

lemma Lyndon_prim: assumes "Lyndon w"
  shows "primitive w"
proof-
  have "0 < n \<Longrightarrow> n < \<^bold>|w\<^bold>| \<Longrightarrow> rotate n w \<noteq> w" for n
    using LyndonD[OF \<open>Lyndon w\<close>, of n] rlex.less_irrefl[of w] by argo
  from no_rotate_prim[OF LyndonD_nemp[OF \<open>Lyndon w\<close>]] this
  show ?thesis by blast
qed

lemma Lyndon_conj_greater: "Lyndon (u\<cdot>v) \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> v \<noteq> \<epsilon> \<Longrightarrow> u\<cdot>v <lex v\<cdot>u"
  using LyndonD[of "u\<cdot>v" "\<^bold>|u\<^bold>|", unfolded rotate_append[of u v]] 
  by force

subsection "Code equations for Lyndon words"

primrec Lyndon_rec :: "'a list \<Rightarrow> nat \<Rightarrow> bool" where
    "Lyndon_rec w 0 = True" |
    "Lyndon_rec w (Suc n) = (if w <lex rotate (Suc n) w then Lyndon_rec w n else False)"

lemma Lyndon_rec_all: assumes "Lyndon_rec (a # w) (\<^bold>|w\<^bold>|)"
  shows "n < \<^bold>|a#w\<^bold>| \<Longrightarrow> 0 < n \<Longrightarrow> Lyndon_rec (a#w) n"
proof(induction n rule: strict_inc_induct)
  case (base i)
  then show ?case
    using assms by auto
next
  case (step i)
  then show ?case
    by (meson Lyndon_rec.simps(2) zero_less_Suc)
qed

lemma Lyndon_Lyndon_rec: assumes "Lyndon w"
  shows "0 < n \<Longrightarrow> n < \<^bold>|w\<^bold>| \<Longrightarrow> Lyndon_rec w n"
proof(induction n, simp)
  case (Suc n)
  have "w <lex rotate (Suc n) w"
    using LyndonD Suc.prems(2) assms by blast
  then show ?case
    using Suc.IH[OF _ Suc_lessD[OF \<open>Suc n < \<^bold>|w\<^bold>|\<close>], folded neq0_conv] Lyndon_rec.simps(1)[of w] 
    unfolding Lyndon_rec.simps(2)
    by metis
qed

lemma Lyndon_code [code]:
    "Lyndon Nil = False" 
    "Lyndon (a # w) = Lyndon_rec (a # w) (\<^bold>|w\<^bold>|)"
proof-
  show "Lyndon Nil = False" by simp
  have "a # w \<noteq> \<epsilon>"
    by simp
  have ax: "0 < n \<Longrightarrow> Lyndon_rec (a#w) n \<Longrightarrow> (a#w) <lex rotate n (a#w)" for n
    using Lyndon_rec.simps(2)[of "a#w"] gr0_implies_Suc[of n] by metis
  have bx: "Lyndon_rec (a # w) (\<^bold>|w\<^bold>|) = (\<forall>n. n < \<^bold>|a#w\<^bold>| \<and> 0 < n \<longrightarrow> Lyndon_rec (a#w) n)"
  proof(cases "w = \<epsilon>", simp)
    assume "w \<noteq> \<epsilon>"
    from this[folded length_greater_0_conv]
    show ?thesis
      using Lyndon_rec_all[of a w] length_Cons[of a w] lessI[of "\<^bold>|w\<^bold>|"]
      by fastforce
  qed
  show "Lyndon (a # w) = Lyndon_rec (a # w) \<^bold>|w\<^bold>|"
    unfolding bx Lyndon.simps
    using ax  LyndonI[OF \<open>a # w \<noteq> \<epsilon>\<close>]Lyndon_Lyndon_rec by blast
qed

subsection "Properties of Lyndon words"

subsubsection "Lyndon words are unbordered"

theorem Lyndon_unbordered: assumes "Lyndon w" shows "\<not> bordered w"
proof
  assume "bordered w"
  from bordered_dec[OF this]
  obtain u v where "u\<cdot>v\<cdot>u = w" and "u \<noteq> \<epsilon>". 
  hence "v \<cdot> u \<noteq> \<epsilon>" and "u \<cdot> v \<noteq> \<epsilon>" by blast+
  note lyn = \<open>Lyndon w\<close>[folded  \<open>u\<cdot>v\<cdot>u = w\<close>] 
  have "u\<cdot>v\<cdot>u <lex v\<cdot>u\<cdot>u"
    using Lyndon_conj_greater[of u "v\<cdot>u", OF lyn \<open>u \<noteq> \<epsilon>\<close> \<open>v \<cdot> u \<noteq> \<epsilon>\<close>, unfolded rassoc].
  from this[unfolded lassoc]
  have "u \<cdot> v \<noteq> v \<cdot> u" 
    by force
  from lexord_suf_linorder[OF _ this, of u u]
  have "u\<cdot>v <lex v\<cdot>u" 
    using  \<open>u\<cdot>v\<cdot>u <lex v\<cdot>u\<cdot>u\<close>  by simp
  from lexord_append_leftI_linorder[of  "u\<cdot>v" "v\<cdot>u", unfolded lassoc, OF this, unfolded rassoc]
  have "u\<cdot>u\<cdot>v <lex u\<cdot>v\<cdot>u".
  from this Lyndon_conj_greater[of "u\<cdot>v" u, unfolded rassoc, OF lyn \<open>u \<cdot> v \<noteq> \<epsilon>\<close>  \<open>u \<noteq> \<epsilon>\<close>]
  show False 
    by simp
qed

subsubsection "Each conjugacy class contains a Lyndon word"

lemma conjug_Lyndon_ex: assumes "primitive w"
  obtains n where "Lyndon (rotate n w)"
proof-
  have "w \<noteq> \<epsilon>"
    using  prim_nemp[OF \<open>primitive w\<close>].

  let ?ConClass = "{rotate n w | n. 0 \<le> n \<and> n < \<^bold>|w\<^bold>|}"

  have "?ConClass \<noteq> {}"
    using \<open>w \<noteq> \<epsilon>\<close> by blast 
  have "w \<in> ?ConClass"
    using \<open>w \<noteq> \<epsilon>\<close> id_apply[of w, folded rotate0]
    by force
  have "finite ?ConClass"
    by simp
  have all_rot: "rotate m w \<in> ?ConClass" for m
    using rotate_conv_mod[of _ w] mod_less_divisor[of "\<^bold>|w\<^bold>|"] \<open>w \<noteq> \<epsilon>\<close>
    by blast

  obtain w' n where "w' \<in> ?ConClass" and all_b: "\<forall> b \<in> ?ConClass. b \<le>lex w' \<longrightarrow> w' = b" and w': "w' = rotate n w"
    using rlex.finite_has_minimal[OF \<open>finite ?ConClass\<close> \<open>?ConClass \<noteq> {}\<close>] by auto 

  have "rotate n w <lex rotate na (rotate n w)" if  "0 < na" and "na < \<^bold>|w\<^bold>|" for na
  proof-
    from prim_no_rotate[OF assms[unfolded prim_rotate_conv[of w n]], of na] \<open>na < \<^bold>|w\<^bold>|\<close> \<open>0 < na\<close>
    have "rotate na (rotate n w) \<noteq> rotate n w" by force
    hence "\<not> rotate na (rotate n w) \<le>lex rotate n w"
      using all_b[rule_format, OF all_rot[of "na + n", folded rotate_rotate[of na n w]]] unfolding w'
      by auto
    from rlex.not_le_imp_less[OF this]
    show "rotate n w <lex rotate na (rotate n w)". 
  qed
  hence "Lyndon (rotate n w)"
    using \<open>w \<noteq> \<epsilon>\<close> by auto 
  from that[OF this] show thesis.
qed

lemma conjug_Lyndon_ex': assumes "primitive w"
  obtains v where "w \<sim> v" and "Lyndon v"
  unfolding conjug_rotate_iff
  using conjug_Lyndon_ex[OF \<open>primitive w\<close>]
  by metis
  
section "Characterization by suffixes"

lemma Lyndon_suf_less: assumes "Lyndon w" "s \<le>ns w" "s \<noteq> w"
  shows "w <lex s"
proof-
  define p where "p = take \<^bold>|s\<^bold>| w" 
  have "\<^bold>|s\<^bold>| \<le> \<^bold>|w\<^bold>|" 
    using nsD[OF \<open>s \<le>ns w\<close>] by force 
  have "p \<le>p w" and "\<^bold>|p\<^bold>|  = \<^bold>|s\<^bold>|"
    unfolding p_def
    using take_is_prefix \<open>\<^bold>|s\<^bold>| \<le> \<^bold>|w\<^bold>|\<close> take_len by blast+ 
  hence "p \<noteq> s" 
    using Lyndon_unbordered[OF \<open>Lyndon w\<close>] \<open>s \<le>ns w\<close> \<open>s \<noteq> w\<close> assms 
    by auto
  define p' s' where "p' = drop \<^bold>|s\<^bold>| w" and "s' = take \<^bold>|p'\<^bold>| w"
  have "p\<cdot>p' = w" and "s'\<cdot>s = w"
    unfolding p'_def p_def s'_def
    using \<open>s \<le>ns w\<close> by auto
  have "\<^bold>|p'\<^bold>| = \<^bold>|s'\<^bold>|"
    using s'_def \<open>p\<cdot>p' = w\<close> by auto 
  have "w <lex s\<cdot>s'"
    using Lyndon_conj_greater[of s' s, unfolded \<open>s' \<cdot> s = w\<close>, OF \<open>Lyndon w\<close>] \<open>p \<noteq> s\<close> 
    unfolding \<open>s' \<cdot> s = w\<close> p_def using \<open>s' \<cdot> s = w\<close> assms(3) by fastforce
  from lexord_suf_linorder[OF _ \<open>p \<noteq> s\<close> \<open>\<^bold>|p\<^bold>| = \<^bold>|s\<^bold>|\<close> \<open>\<^bold>|p'\<^bold>| = \<^bold>|s'\<^bold>|\<close>, OF this[folded \<open>p \<cdot> p' = w\<close>]]
  have "p <lex s".
  from lexord_app_right_linorder[OF this, of p' \<epsilon>, unfolded \<open>p \<cdot> p' = w\<close>]  \<open>\<^bold>|p\<^bold>| = \<^bold>|s\<^bold>|\<close>
  show "w <lex s"
    by simp
qed

(* TODO zkusit pouzit jinde *)
lemma Lyndon_pref_suf_less:  assumes "Lyndon w" "p \<le>p w" "s \<le>ns w" "s \<noteq> w"
  shows "p <lex s"
proof(cases "p = w", simp add: Lyndon_suf_less[OF assms(1) assms(3) assms(4)])
  assume "p \<noteq> w"
  show "p <lex s"
  proof(rule rlex.less_trans)
    show "p <lex w"
      using \<open>p \<noteq> w\<close> assms(2) lexordp_append_rightI by fastforce 
    show "w <lex s"
      using Lyndon_suf_less assms(1) assms(3) assms(4) by blast
  qed
qed

lemma suf_less_Lyndon: assumes "w \<noteq> \<epsilon>" and "\<forall>s. (s \<le>ns w \<longrightarrow> s \<noteq> w \<longrightarrow> w <lex s)"
  shows "Lyndon w"
proof (cases "primitive w") 
  assume "\<not> primitive w"
  obtain q k where "q \<noteq> \<epsilon>" "1 < k" "q\<^sup>@k=w" "w\<noteq>q" \<comment> \<open>the exact match of @{thm non_prim} fastens the proof considerably\<close>
    using non_prim[OF \<open>\<not> primitive w\<close> \<open>w \<noteq> \<epsilon>\<close>] by blast
  hence "q \<le>ns w"
    unfolding nonempty_suffix_def pow_eq_if_list[of q k] pow_commutes_list[symmetric]
    using sufI[of "q \<^sup>@ (k - 1)" q w]
    by presburger

  have "q <p w"
    using \<open>1 < k\<close>  \<open>q \<^sup>@ k = w\<close> 
    unfolding pow_eq_if_list[of q k] pow_eq_if_list[of q "k-1"]
    using \<open>w \<noteq> \<epsilon>\<close>  by auto
  from lexordp_append_rightI[of "q\<inverse>\<^sup>>w" q, 
      unfolded lq_pref[OF sprefD1[OF this]], OF lq_spref[OF this]]
  have "q <lex w".
  thus  "Lyndon w"
    unfolding Lyndon.simps using \<open>q \<le>ns w\<close> \<open>w \<noteq> \<epsilon>\<close> assms(2) rlex.order.strict_trans by blast
next 
  assume "primitive w"
  have "w <lex rotate l w" if assms_l: "0 < l" "l < \<^bold>|w\<^bold>|" for l  
  proof-
    have "take l w \<le>np w" and "\<^bold>|take l w\<^bold>| = l"
      using assms_l take_is_prefix  \<open>l < \<^bold>|w\<^bold>|\<close> by auto
    have "drop l w \<le>ns w" 
      using \<open>l < \<^bold>|w\<^bold>|\<close> suffix_drop by auto
    have "drop l w \<noteq> w"
      using append_take_drop_id[of l w] npD'[OF \<open>take l w \<le>np w\<close>] by force
    have "drop l w \<cdot> take l w = rotate l w"
      using rotate_append[of "take l w" "drop l w", symmetric, unfolded \<open>\<^bold>|take l w\<^bold>| = l\<close>, 
          unfolded append_take_drop_id].

    have "w <lex drop l w"
      using \<open>drop l w \<le>ns w\<close> \<open>drop l w \<noteq> w\<close> assms(2) by blast
    from lexord_app_right_linorder[OF this suffix_length_le[OF conjunct2[OF \<open>drop l w \<le>ns w\<close>[unfolded nonempty_suffix_def]]], of \<epsilon> "take l w", unfolded  append.right_neutral]
    have "w <lex drop l w \<cdot> take l w".
    thus "w <lex rotate l w"
      by (simp add: \<open>drop l w \<cdot> take l w = rotate l w\<close>)
  qed
  thus "Lyndon w"
    by (simp add: \<open>w \<noteq> \<epsilon>\<close> local.LyndonI)
qed

corollary Lyndon_suf_char: "w \<noteq> \<epsilon> \<Longrightarrow> Lyndon w \<longleftrightarrow> (\<forall>s. s \<le>ns w \<longrightarrow> s \<noteq> w \<longrightarrow> w <lex s)"
  using Lyndon_suf_less suf_less_Lyndon by blast

lemma Lyndon_suf_le: "Lyndon w \<Longrightarrow> s \<le>ns w \<Longrightarrow> w \<le>lex s"
  using Lyndon_suf_less rlex.not_less rlex.order.asym by blast

section "Unbordered prefix of a Lyndon word is Lyndon"

lemma unbordered_pref_Lyndon: "Lyndon (u\<cdot>v) \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> \<not> bordered u \<Longrightarrow> Lyndon u"
  unfolding Lyndon_suf_char
proof(standard+)
  fix s
  assume "Lyndon (u \<cdot> v)" and  "u \<noteq> \<epsilon>" and "\<not> bordered u" and "s \<le>ns u" and "s \<noteq> u"
    hence "u \<cdot> v <lex s \<cdot> v"
      using  Lyndon_suf_less[OF \<open>Lyndon (u \<cdot> v)\<close>, of "s \<cdot> v"] by auto
    have "\<not> s \<le>p u"
      using \<open>\<not> bordered u\<close> \<open>s \<le>ns u\<close> \<open>s \<noteq> u\<close> by auto 
    moreover have "\<not> u \<le>p s"
      using suf_pref_eq[OF nsD[OF\<open>s \<le>ns u\<close>]] \<open>s \<noteq> u\<close> by blast
    ultimately show "u <lex s"
      using lexord_cancel_right_linorder[OF \<open>u \<cdot> v <lex s \<cdot> v\<close>] by blast
qed

section "Concatenation of Lyndon words"

theorem Lyndon_concat: assumes  "Lyndon u" and "Lyndon v" and "u <lex v"
  shows "Lyndon (u\<cdot>v)"
proof-
  have "u\<cdot>v <lex v"
  proof(cases "u \<le>p v")
    assume "u \<le>p v"
    then obtain z where "u\<cdot>z = v" and "z \<le>ns v"
      using assms(3) dual_rlex.less_imp_neq by auto
    from Lyndon_suf_less[OF \<open>Lyndon v\<close> this(2), THEN lexord_append_leftI_linorder, of u]
      LyndonD_nemp[OF \<open>Lyndon u\<close>] this(1)
    show ?thesis
      by blast
  next
    assume "\<not> u \<le>p v"
    then show ?thesis
      using local.lexordp_linear[of v "u\<cdot>v"] 
        local.lexordp_mid_pref[OF \<open>u <lex v\<close>,of v]
        prefixI[of v u v]
      by argo
  qed

  { fix z
    assume "z \<le>ns (u\<cdot>v)" "z \<noteq> u\<cdot>v"
    have "u\<cdot>v <lex z"
    proof(cases "z \<le>ns v")
      assume "z \<le>ns v"
      from Lyndon_suf_less[OF \<open>Lyndon v\<close> this]
      have "z \<noteq> v \<Longrightarrow> v <lex z"
        by blast
      thus "u\<cdot>v <lex z"
        using \<open>u \<cdot> v <lex v\<close> rlex.less_trans
        by fast
    next
      assume "\<not> z \<le>ns v"
      then obtain z' where "z' \<le>ns u" "z' \<noteq> u" "z'\<cdot>v = z"
        using \<open>z \<le>ns u \<cdot> v\<close> \<open>z \<noteq> u \<cdot> v\<close> suffix_append[of z u v]
        unfolding nonempty_suffix_def
        by force
      from Lyndon_suf_less[OF \<open>Lyndon u\<close> this(1) this(2)]
      have "u <lex z'".
      thus "u\<cdot>v <lex z"
        using  \<open>z' \<le>ns u\<close> lexord_app_right_linorder[of u z' v v] suffix_length_le[of z' u]
        unfolding nonempty_suffix_def \<open>z' \<cdot> v = z\<close>
        by blast
    qed
  }
  thus ?thesis
    using suf_nemp[OF LyndonD_nemp[OF \<open>Lyndon v\<close>], of u, THEN suf_less_Lyndon]
    by blast
qed

section "Longest Lyndon suffix"

fun longest_Lyndon_suffix:: "'a list \<Rightarrow> 'a list" ("LynSuf") where
  "longest_Lyndon_suffix \<epsilon> = \<epsilon>" |
  "longest_Lyndon_suffix (a#w) = (if Lyndon (a#w) then a#w else longest_Lyndon_suffix w)"

lemma longest_Lyndon_suf_ext: "\<not> Lyndon (a # w) \<Longrightarrow> LynSuf w = LynSuf (a # w)"
  using longest_Lyndon_suffix.simps(2) by presburger

lemma longest_Lyndon_suf_suf: "w \<noteq> \<epsilon> \<Longrightarrow> LynSuf w \<le>s w"
proof(induction w rule: longest_Lyndon_suffix.induct)
  case 1
  then show ?case by simp 
next
  case (2 a w)
  show ?case
  proof(cases "Lyndon (a#w)")
    case True
    then show ?thesis by auto
  next
    case False
    from "2.IH"[OF this, unfolded longest_Lyndon_suf_ext[OF this], THEN suffix_ConsI, of a]
      Lyndon_sing False
    show ?thesis by blast
  qed
qed

lemma longest_Lyndon_suf_max: 
  "v \<le>s w  \<Longrightarrow> Lyndon v \<Longrightarrow> v \<le>s (LynSuf w)"
proof(induction w arbitrary: v rule: longest_Lyndon_suffix.induct)
  case 1
  then show ?case
    using longest_Lyndon_suffix.simps(1) by presburger 
next
  case (2 a w)
  show ?case
  proof(cases "Lyndon (a#w)")
    case True
    then show ?thesis
      using "2.prems"(1) longest_Lyndon_suffix.simps(2) by presburger
  next
    case False
    have "v \<noteq> a # w"
      using "2.prems"(2) False by blast
    from "2.IH"[OF False _ "2.prems"(2), unfolded longest_Lyndon_suf_ext[OF False]]
       "2.prems"(1)[unfolded suffix_Cons] this
    show ?thesis by fast
  qed  
qed

lemma longest_Lyndon_suf_Lyndon_id: assumes "Lyndon w" 
  shows "LynSuf w = w"
proof(cases "w = \<epsilon>", simp)
  case False
  from longest_Lyndon_suf_suf[OF this]
    suffix_order.order_refl[THEN longest_Lyndon_suf_max[OF _ assms]]
    suffix_order.order.antisym 
  show ?thesis by blast
qed

lemma longest_Lyndon_suf_longest: "w \<noteq> \<epsilon> \<Longrightarrow> v' \<le>s w \<Longrightarrow> Lyndon v' \<Longrightarrow> \<^bold>|v'\<^bold>| \<le> \<^bold>|(LynSuf w)\<^bold>|"
  using longest_Lyndon_suf_max suffix_length_le by blast

lemma longest_Lyndon_suf_sing: "LynSuf [a] = [a]"
  using Lyndon_sing longest_Lyndon_suf_Lyndon_id by blast

lemma longest_Lyndon_suf_Lyndon: "w \<noteq> \<epsilon> \<Longrightarrow> Lyndon (LynSuf w)"
proof(induction w rule: longest_Lyndon_suffix.induct, blast)
  case (2 a w)
  show ?case
  proof(cases "Lyndon (a#w)")
    case True
    then show ?thesis
      using longest_Lyndon_suf_Lyndon_id by presburger
  next
    case False
    from "2.IH"[OF this, unfolded longest_Lyndon_suf_ext[OF this]] Lyndon_sing
    show ?thesis by fastforce
  qed
qed  

lemma longest_Lyndon_suf_nemp: "w \<noteq> \<epsilon> \<Longrightarrow> LynSuf w \<noteq> \<epsilon>"
  using longest_Lyndon_suf_Lyndon[THEN LyndonD_nemp].

lemma longest_Lyndon_sufI:
  assumes "q \<le>s w" and "Lyndon q" and all_s: "(\<forall> s. (s \<le>s w \<and> Lyndon s) \<longrightarrow> s \<le>s q)" 
  shows "LynSuf w = q"
proof(cases "w = \<epsilon>")
  case True
  then show ?thesis
    using assms(1) longest_Lyndon_suffix.simps(1) suffix_bot.bot.extremum_uniqueI by blast 
next
  case False
  from all_s longest_Lyndon_suf_Lyndon[OF this] longest_Lyndon_suf_max[OF assms(1) assms(2)]
    longest_Lyndon_suf_suf[OF this] suffix_order.eq_iff
  show ?thesis by blast
qed

corollary longest_Lyndon_sufI': 
  assumes "q \<le>s w" and "Lyndon q" and all_s: "\<forall> s. (s \<le>s w \<and> Lyndon s) \<longrightarrow> \<^bold>|s\<^bold>| \<le> \<^bold>|q\<^bold>|" 
  shows "LynSuf w = q"
  using longest_Lyndon_sufI[OF \<open>q \<le>s w\<close> \<open>Lyndon q\<close>] suf_ruler_le all_s \<open>q \<le>s w\<close> by blast

text\<open>The next lemma is fabricated to suit the upcoming definition of longest Lyndon factorization.\<close>

lemma longest_Lyndon_suf_shorter: assumes "w \<noteq> \<epsilon>" 
  shows "\<^bold>|w\<^sup><\<inverse>(LynSuf w)\<^bold>| < \<^bold>|w\<^bold>|"
  using nemp_len[OF longest_Lyndon_suf_nemp[OF \<open>w \<noteq> \<epsilon>\<close>]] arg_cong[OF rq_suf[OF longest_Lyndon_suf_suf[OF \<open>w \<noteq> \<epsilon>\<close>]], of length] 
  unfolding length_append by linarith  

section "Lyndon factorizations"

function Lyndon_fac::"'a list  \<Rightarrow> 'a list list" ("LynFac")
  where "Lyndon_fac w  = (if w \<noteq> \<epsilon> then ((Lyndon_fac (w \<^sup><\<inverse>(LynSuf w) )) \<cdot> [LynSuf w]) else \<epsilon>)"
  using longest_Lyndon_suffix.cases by blast+
termination
proof(relation "measure length", simp)
  show "\<And>w. w \<noteq> \<epsilon> \<Longrightarrow> (w\<^sup><\<inverse>LynSuf w, w) \<in> measure length"
    unfolding measure_def inv_image_def using longest_Lyndon_suf_shorter by blast
qed

text\<open>The factorization @{term "Lyndon_fac w"} obtained by taking always the longest Lyndon suffix is well defined, 
and called ``Lyndon factorization (of $w$)''.\<close>


lemma Lyndon_fac_simp: "w \<noteq> \<epsilon> \<Longrightarrow> Lyndon_fac w =  Lyndon_fac (w\<^sup><\<inverse>LynSuf w) \<cdot> (LynSuf w # \<epsilon>)"
  using Lyndon_fac.simps[of w] by meson

lemma Lyndon_fac_emp: "Lyndon_fac \<epsilon> = \<epsilon>"
  by simp

text\<open>Note that the Lyndon factorization of a Lyndon word is trivial.\<close>

lemma Lyndon_fac_longest_Lyndon_id: "Lyndon w \<Longrightarrow> Lyndon_fac w = [w]"
  by (simp add: longest_Lyndon_suf_Lyndon_id) 

text\<open>Lyndon factorization is composed of Lyndon words ...\<close>

lemma Lyndon_fac_set: "z \<in> set (Lyndon_fac w) \<Longrightarrow> Lyndon z"
proof(induction w rule:  Lyndon_fac.induct)
  case (1 w)
  then show "Lyndon z"
  proof (cases "w = \<epsilon>")
    assume "w \<noteq> \<epsilon>"
    have "Lyndon_fac w  = (Lyndon_fac (w \<^sup><\<inverse>(LynSuf w) )) \<cdot> [LynSuf w]"
      using Lyndon_fac_simp[OF \<open>w \<noteq> \<epsilon>\<close>].
    from set_ConsD[OF "1.prems"(1)[unfolded rotate1.simps(2)[of "LynSuf w" "Lyndon_fac (w \<^sup><\<inverse>(LynSuf w) )", folded this, symmetric], unfolded set_rotate1]]
    have "z = LynSuf w \<or> z \<in> set (Lyndon_fac (w \<^sup><\<inverse>(LynSuf w) ))".
    thus "Lyndon z"
      using "1.IH"[OF \<open>w \<noteq> \<epsilon>\<close>] longest_Lyndon_suf_Lyndon[OF \<open>w \<noteq> \<epsilon>\<close>]
      by blast
  next
    assume "w = \<epsilon>"
    thus "Lyndon z"
      using "1.prems"
      unfolding Lyndon_fac_emp[folded \<open>w = \<epsilon>\<close>] list.set(1) empty_iff
      by blast
  qed
qed

text\<open>...and it indeed is a factorization of the argument.\<close>

lemma Lyndon_fac_longest_dec: "concat (Lyndon_fac w) = w"
proof(induction w rule: Lyndon_fac.induct)
  case (1 w)
  thus "concat (LynFac w) = w"
  proof (cases "w = \<epsilon>", simp)
  assume "w \<noteq> \<epsilon>"
    have eq: "concat (Lyndon_fac w) = concat ( (Lyndon_fac (w \<^sup><\<inverse>(LynSuf w) )) ) \<cdot> concat ([LynSuf w])"
      unfolding Lyndon_fac_simp[OF \<open>w \<noteq> \<epsilon>\<close>] concat_morph..
    from this[unfolded "1.IH"[OF \<open>w \<noteq> \<epsilon>\<close>] concat_sing' rq_suf[OF longest_Lyndon_suf_suf[OF \<open>w \<noteq> \<epsilon>\<close>]]]
    show ?case.
  qed
qed

text\<open>The following lemma makes explicit the inductive character of the definition of @{term Lyndon_fac}.\<close>

lemma Lyndon_fac_longest_pref: "us \<le>p Lyndon_fac w \<Longrightarrow> Lyndon_fac (concat us) = us"
proof(induction w arbitrary: us rule:  Lyndon_fac.induct)
  case (1 w)
  thus "LynFac (concat us) = us"
  proof (cases "w = \<epsilon>", simp)
    assume "w \<noteq> \<epsilon>"
    have step: "Lyndon_fac w = (Lyndon_fac (w \<^sup><\<inverse>(LynSuf w))) \<cdot> [LynSuf w]"
      using Lyndon_fac_simp[OF \<open>w \<noteq> \<epsilon>\<close>].

    consider (neq) "us \<noteq> Lyndon_fac w" | (eq) "us = Lyndon_fac w"
      using "1.prems" le_neq_implies_less by blast
    then show "LynFac (concat us) = us"
    proof(cases)
      case neq
      hence "us \<le>p Lyndon_fac (w\<^sup><\<inverse>LynSuf w)"
        using "1.prems" last_no_split[of us "Lyndon_fac (w\<^sup><\<inverse>LynSuf w)" "LynSuf w"] 
        unfolding step[symmetric] by blast
      thus "LynFac (concat us) = us"
        using "1.IH" \<open>w \<noteq> \<epsilon>\<close> by blast 
    next
      case eq
      show "LynFac (concat us) = us"
        using Lyndon_fac_longest_dec[of w, folded eq] eq by simp
    qed
  qed
qed

text\<open>We give name to an important predicate: monotone (nonincreasing) list of Lyndon words.\<close>

definition Lyndon_mono :: "'a list list \<Rightarrow>  bool" where
  "Lyndon_mono ws \<longleftrightarrow> (\<forall> u \<in> set ws. Lyndon u) \<and> (rlex.sorted (rev ws))"

lemma Lyndon_mono_set: "Lyndon_mono ws \<Longrightarrow> u \<in> set ws \<Longrightarrow> Lyndon u"
  unfolding Lyndon_mono_def by blast

lemma Lyndon_mono_sorted: "Lyndon_mono ws \<Longrightarrow> rlex.sorted (rev ws)"
  unfolding Lyndon_mono_def by blast

lemma Lyndon_mono_nth: "Lyndon_mono ws \<Longrightarrow> i \<le> j \<Longrightarrow> j < \<^bold>|ws\<^bold>| \<Longrightarrow> ws!j \<le>lex ws!i"
  unfolding Lyndon_mono_def using  rlex.sorted_rev_nth_mono by blast

lemma Lyndon_mono_empty[simp]: "Lyndon_mono \<epsilon>"
  unfolding Lyndon_mono_def by auto

lemma Lyndon_mono_sing: "Lyndon u \<Longrightarrow> Lyndon_mono [u]"
  unfolding Lyndon_mono_def by auto

lemma Lyndon_mono_fac_Lyndon_mono: 
  assumes "ps \<le>f ws" and "Lyndon_mono ws" shows "Lyndon_mono ps"  
unfolding Lyndon_mono_def
proof
  show "\<forall>x \<in> (set ps). Lyndon x" 
    using \<open>Lyndon_mono ws\<close>[unfolded Lyndon_mono_def] set_mono_sublist[OF \<open>ps \<le>f ws\<close>] by blast
  show "linorder.sorted (\<le>lex) (rev ps)"
    using rlex.sorted_append \<open>Lyndon_mono ws\<close>[unfolded Lyndon_mono_def] \<open>ps \<le>f ws\<close>[unfolded sublist_def] by fastforce
qed

text\<open>Lyndon factorization is monotone! 
Altogether, we have shown that the Lyndon factorization is a monotone factorization 
into Lyndon words.\<close>

theorem fac_Lyndon_mono: "Lyndon_mono (Lyndon_fac w)"
proof (induct "Lyndon_fac w" arbitrary: w rule: rev_induct, simp)
  case (snoc x xs)
  have "Lyndon x"
    using Lyndon_fac_set[of x, unfolded in_set_conv_decomp, of w, folded snoc.hyps(2)] by fast
  have "concat (xs \<cdot> [x]) = w"
    using Lyndon_fac_longest_dec[of w, folded snoc.hyps(2)] by auto
  then show "Lyndon_mono (LynFac w)"
  proof (cases "xs = \<epsilon>")
    assume "xs = \<epsilon>"
    show "Lyndon_mono (LynFac w)"
      unfolding Lyndon_mono_def \<open>xs \<cdot> [x] = LynFac w\<close>[symmetric] \<open>xs = \<epsilon>\<close> append.left_neutral 
                rlex.sorted1[of x]  
      using \<open>Lyndon x\<close> by force
  next
    assume "xs \<noteq> \<epsilon>"
    have "concat (xs \<cdot> [x]) \<noteq> \<epsilon>" and "w \<noteq> \<epsilon>"
      using Lyndon_fac_longest_dec snoc.hyps(2) by auto
    have "x = LynSuf w" and "xs = LynFac (w\<^sup><\<inverse>LynSuf w )"           
      using Lyndon_fac.simps[of w, folded snoc.hyps(2)] \<open>w \<noteq> \<epsilon>\<close>
        Lyndon_fac_longest_dec append1_eq_conv[of xs x "LynFac (w\<^sup><\<inverse>LynSuf w )" "LynSuf w"] by presburger+       
    from Lyndon_mono_sorted[OF snoc.hyps(1)[OF \<open>xs = LynFac (w\<^sup><\<inverse>LynSuf w )\<close>], folded this]
    have "dual_rlex.sorted  xs"
      unfolding sorted_dual_rev_iff.
    have "Lyndon (last xs)"
      using Lyndon_fac_set[of "last xs" "w\<^sup><\<inverse>LynSuf w", folded \<open>xs = LynFac (w\<^sup><\<inverse>LynSuf w)\<close>, OF last_in_set[OF \<open>xs \<noteq> \<epsilon>\<close>]].
    have "x \<le>lex last xs"
    proof(rule ccontr)
      assume "\<not> x \<le>lex last xs" hence "last xs <lex x" by auto
      from Lyndon_concat[OF  \<open>Lyndon (last xs)\<close> \<open>Lyndon x\<close> this]
      have "Lyndon ((last xs) \<cdot> x)".
      have "(last xs) \<cdot> x \<le>s concat (xs \<cdot> [x])"
        using \<open>xs \<noteq> \<epsilon>\<close> concat_last_suf by auto
      from longest_Lyndon_suf_longest[OF \<open>concat (xs \<cdot> [x]) \<noteq> \<epsilon>\<close>  this \<open>Lyndon ((last xs) \<cdot> x)\<close>, 
          unfolded \<open>concat (xs \<cdot> [x]) = w\<close>, folded \<open>x = LynSuf w\<close>]
      show False
        using \<open>Lyndon (last xs)\<close> by simp 
    qed 
    have "dual_rlex.sorted (butlast xs \<cdot> [last xs])"
      by (simp add: \<open>linorder.sorted (\<lambda>x y. y \<le>lex x) xs\<close> \<open>xs \<noteq> \<epsilon>\<close>)
    from this \<open>x \<le>lex last xs\<close>
    have "dual_rlex.sorted (butlast xs \<cdot> [last xs,x])"
      using dual_rlex.sorted_append by auto   
    from this[unfolded hd_word[of "last xs" "[x]"] lassoc append_butlast_last_id[OF \<open>xs \<noteq> \<epsilon>\<close>]]
    have "rlex.sorted (rev (LynFac w))"
      unfolding  \<open>xs \<cdot> [x] = LynFac w\<close>[symmetric] sorted_dual_rev_iff[symmetric].
    thus "Lyndon_mono (LynFac w)"
      unfolding Lyndon_mono_def using Lyndon_fac_set by blast
  qed
qed

text\<open>Now we want to show the converse: any monotone factorization into Lyndon words is the Lyndon factorization\<close>

text\<open>The last element in the Lyndon factorization is the smallest suffix.\<close>

lemma Lyndon_mono_last_smallest: "Lyndon_mono ws \<Longrightarrow>s \<le>ns (concat ws) \<Longrightarrow> last ws \<le>lex s"
proof(induct ws arbitrary: s rule: rev_induct, fastforce)
  case (snoc a ws)
  have "ws\<cdot>[a] \<noteq> \<epsilon>"
    by blast
  have "last (ws\<cdot>[a]) = a"
    by simp
  from last_in_set[OF \<open>ws\<cdot>[a] \<noteq> \<epsilon>\<close>, unfolded this] \<open>Lyndon_mono (ws \<cdot> [a])\<close>[unfolded Lyndon_mono_def]
  have "Lyndon a"
    by blast
  show ?case
  proof(cases "s \<le>ns a")
    case True
    from Lyndon_suf_le[OF \<open>Lyndon a\<close>] this
    show ?thesis
      by simp
  next
    case False
    hence "ws \<noteq> \<epsilon>"
      using snoc.prems(2) by force
    obtain s' where "s = s'\<cdot>a"
      using False snoc.prems(2)[unfolded concat_append[of ws "[a]", unfolded concat_sing']] suffix_append[of s "concat ws" a]
      unfolding nonempty_suffix_def
      by blast
    hence "s' \<le>ns concat ws"
      using False snoc.prems(2) by fastforce
    have "Lyndon_mono ws"
      using \<open>Lyndon_mono (ws\<cdot>[a])\<close> Lyndon_mono_fac_Lyndon_mono
      by blast
    from snoc.hyps[OF this \<open>s' \<le>ns concat ws\<close>]
    have "last ws \<le>lex s'" 
      by auto
    hence "last ws \<le>lex s'\<cdot>a"
      using local.lexordp_eq_trans ord.lexordp_eq_pref by blast
    have "a \<le>lex last ws"
      using \<open>Lyndon_mono (ws\<cdot>[a])\<close>
      unfolding Lyndon_mono_def
      by (simp add: \<open>ws \<noteq> \<epsilon>\<close> last_ConsL)
    from dual_rlex.order_trans[OF \<open>last ws \<le>lex s' \<cdot> a\<close> this, folded \<open>s = s' \<cdot> a\<close>]
    show ?thesis
      unfolding \<open>last (ws\<cdot>[a]) = a\<close>
      by blast
  qed
qed


text\<open>A monotone list, if seen as a factorization,
must end with the longest suffix\<close>

lemma Lyndon_mono_last_longest: assumes "ws \<noteq> \<epsilon>" and "Lyndon_mono ws" 
  shows "LynSuf (concat ws) = last ws"
proof-
  have "Lyndon (last ws)"
    using Lyndon_mono_set assms(1) assms(2) last_in_set by blast
  hence "last ws \<noteq> \<epsilon>"
    using LyndonD_nemp by blast
  hence "last ws \<le>ns LynSuf (concat ws)"
    using longest_Lyndon_suf_max[OF  concat_last_suf[OF assms(1)] \<open>Lyndon (last ws)\<close>]
    unfolding nonempty_suffix_def
    by blast

  have "concat ws \<noteq> \<epsilon>"
    using Lyndon.simps assms(2)[unfolded Lyndon_mono_def] set_nemp_concat_nemp[OF assms(1)]
    by blast
  from longest_Lyndon_suf_nemp[OF this] longest_Lyndon_suf_suf[OF this]
  have "LynSuf (concat ws) \<le>ns concat ws"
    unfolding nonempty_suffix_def
    by simp
 
  show ?thesis
    using Lyndon_mono_last_smallest[OF \<open>Lyndon_mono ws\<close> \<open>LynSuf (concat ws) \<le>ns concat ws\<close>]
      Lyndon_suf_le[OF longest_Lyndon_suf_Lyndon[OF \<open>concat ws \<noteq> \<epsilon>\<close>], OF \<open>last ws \<le>ns LynSuf (concat ws)\<close>]
      dual_rlex.eq_iff
    by simp
qed

text\<open>Therefore, by construction, 
any monotone list is the Lyndon factorization of its concatenation\<close>

lemma Lyndon_mono_fac:
  "Lyndon_mono ws \<Longrightarrow> ws = Lyndon_fac (concat ws)"
proof (induct ws rule: rev_induct, simp)
  case (snoc x xs)
  have "Lyndon_mono xs"
    using \<open>Lyndon_mono (xs \<cdot> [x])\<close>  
    unfolding Lyndon_mono_def
    by simp 
  from snoc.hyps[OF this]
  have "xs = LynFac (concat xs)".
  have "x = LynSuf (concat (xs \<cdot> [x]))"
    using Lyndon_mono_last_longest[OF _ \<open>Lyndon_mono (xs \<cdot> [x])\<close>, unfolded last_snoc] by simp
  have "concat (xs \<cdot> [x])\<^sup><\<inverse>x = concat xs"
    by simp
  have "concat (xs \<cdot> [x]) \<noteq> \<epsilon>"
    using Lyndon_mono_set snoc.prems by auto
  from this
  show ?case
    using Lyndon_fac.simps[of "concat (xs \<cdot> [x])", folded \<open>x = LynSuf (concat (xs \<cdot> [x]))\<close>,
        unfolded \<open>concat (xs \<cdot> [x])\<^sup><\<inverse>x = concat xs\<close>, folded \<open>xs = LynFac (concat xs)\<close>] 
    by presburger
qed


text\<open>This implies that the Lyndon factorization can be characterized
in two equivalent ways: as the (unique) monotone factorization (into Lyndon words) or as
the "suffix greedy" factorization (into Lyndon words).
\<close>

corollary Lyndon_mono_fac_iff: "Lyndon_mono ws \<longleftrightarrow> ws = LynFac (concat ws)"
  using Lyndon_mono_fac fac_Lyndon_mono[of "concat ws"] by fastforce

corollary Lyndon_mono_unique: assumes "Lyndon_mono ws" and "Lyndon_mono zs" and "concat ws = concat zs" 
  shows "ws = zs"
  using Lyndon_mono_fac[OF \<open>Lyndon_mono ws\<close>] Lyndon_mono_fac[OF \<open>Lyndon_mono zs\<close>] 
  unfolding \<open>concat ws = concat zs\<close>  by simp


subsection "Standard factorization"

lemma Lyndon_std: assumes "Lyndon w" "1 < \<^bold>|w\<^bold>|"
  obtains l m where "w = l\<cdot>m" and "Lyndon l" and "Lyndon m" and "l <lex m"
proof-
  have "w \<noteq> \<epsilon>" "tl w \<noteq> \<epsilon>"
    using \<open>1 < \<^bold>|w\<^bold>|\<close> long_list_tl by auto
  define m where  "m = LynSuf (tl w)"
  hence "Lyndon m"
    using \<open>tl w \<noteq> \<epsilon>\<close> local.longest_Lyndon_suf_Lyndon by blast
  have "m \<le>s w"
    unfolding m_def 
    using suffix_order.order.trans[OF longest_Lyndon_suf_suf[OF \<open>tl w \<noteq> \<epsilon>\<close>] suffix_tl[of w]]. 
  moreover have "m \<noteq> w"
    unfolding m_def using  hd_word'[OF \<open>w \<noteq> \<epsilon>\<close>] list.simps(3) longest_Lyndon_suf_suf[OF \<open>tl w \<noteq> \<epsilon>\<close>] same_suffix_nil
    by fastforce
  ultimately obtain l where "w = l\<cdot>m" and "l \<noteq> \<epsilon>"
    by force

  have "Lyndon l"
  proof (rule unbordered_pref_Lyndon[OF \<open>Lyndon w\<close>[unfolded \<open>w = l\<cdot>m\<close>] \<open>l \<noteq> \<epsilon>\<close>], rule)
    assume "bordered l"
    from unbordered_border[OF this, unfolded border_def]
    obtain s where "s \<noteq> \<epsilon>" and "s \<noteq> l" and "s \<le>p l" and "s \<le>s l" and "\<not> bordered s"
      by blast 
    have "Lyndon s"       
      using unbordered_pref_Lyndon[OF _ \<open>s \<noteq> \<epsilon>\<close> \<open>\<not> bordered s\<close>, of "s\<inverse>\<^sup>>l\<cdot>m", unfolded lassoc lq_pref[OF \<open>s \<le>p l\<close>]]
      \<open>Lyndon w\<close>[unfolded \<open>w = l \<cdot> m\<close>] by blast
    have "s <lex m"
      using Lyndon_pref_suf_less[OF \<open>Lyndon w\<close> _ nsI[OF LyndonD_nemp[OF \<open>Lyndon m\<close>] \<open>m \<le>s w\<close>] 
         \<open>m \<noteq> w\<close>, of s] Lyndon.elims(2)[OF \<open>Lyndon m\<close>]  
         \<open>s \<le>p l\<close> prefix_append[of s l m, folded \<open>w = l \<cdot> m\<close>]
      by presburger
    from Lyndon_concat[OF \<open>Lyndon s\<close> \<open>Lyndon m\<close> this]
    have "Lyndon (s\<cdot>m)".
    moreover have "s\<cdot>m \<le>s tl w" 
      unfolding \<open>w = l \<cdot> m\<close> using \<open>s \<noteq> l\<close> \<open>s \<le>s l\<close> list.collapse[OF \<open>w \<noteq> \<epsilon>\<close>, unfolded \<open>w = l \<cdot> m\<close>] by force
    ultimately show False
      using m_def \<open>s \<noteq> \<epsilon>\<close> longest_Lyndon_suf_max same_suffix_nil by blast
  qed

  have "l <lex m"
    using Lyndon_pref_suf_less[OF \<open>Lyndon w\<close> prefI[OF \<open>w = l \<cdot> m\<close>[symmetric]] 
        nsI[OF longest_Lyndon_suf_nemp[OF \<open>tl w \<noteq> \<epsilon>\<close>, folded  m_def] \<open>m \<le>s w\<close>] \<open>m \<noteq> w\<close>].
  from that[OF \<open>w = l \<cdot> m\<close> \<open>Lyndon l\<close>  \<open>Lyndon m\<close> this]
  show thesis.
qed

corollary Lyndon_std_iff: 
  "Lyndon w \<longleftrightarrow> (\<^bold>|w\<^bold>| = 1 \<or> (\<exists> l m. w = l\<cdot>m \<and> Lyndon l \<and> Lyndon m \<and> l <lex m))" 
  (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
    using Lyndon_std[OF \<open>Lyndon w\<close>] 
      nemp_pos_len[OF LyndonD_nemp[OF \<open>Lyndon w\<close>], unfolded le_eq_less_or_eq]
    by metis
next
  assume ?R
  thus ?L
  proof(rule disjE, fastforce)
    show \<open>\<exists>l m. w = l \<cdot> m \<and> Lyndon l \<and> Lyndon m \<and> l <lex m \<Longrightarrow> Lyndon w\<close> 
      using Lyndon_concat by blast
  qed
qed

end  \<comment> \<open>end context linorder\<close>

end