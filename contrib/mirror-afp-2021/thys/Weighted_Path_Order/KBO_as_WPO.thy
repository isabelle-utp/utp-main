subsection \<open>A restricted equality between KBO and WPO\<close>

text \<open>The remaining difficulty to make KBO an instance of WPO is the
  different treatment of lexicographic comparisons, which is unrestricted in KBO,
  but there is a length-restriction in WPO. 
  Therefore we will only show that KBO is an instance of WPO if we compare terms with 
  bounded arity.\<close>

text \<open>This restriction does however not prohibit us from lifting properties of WPO to KBO.
  For instance, for several properties one can choose a large-enough bound restriction of WPO, 
  since there are only finitely many arities occurring in a property.\<close>

theory KBO_as_WPO
  imports 
    WPO 
    KBO_Transformation
begin

definition bounded_arity :: "nat \<Rightarrow> ('f \<times> nat)set \<Rightarrow> bool" where
  "bounded_arity b F = (\<forall> (f,n) \<in> F. n \<le> b)" 

lemma finite_funas_term[simp,intro]: "finite (funas_term t)" 
  by (induct t, auto)

context weight_fun begin

definition "weight_le s t \<equiv>
  (vars_term_ms (SCF s) \<subseteq># vars_term_ms (SCF t) \<and> weight s \<le> weight t)"

definition "weight_less s t \<equiv>
  (vars_term_ms (SCF s) \<subseteq># vars_term_ms (SCF t) \<and> weight s < weight t)"

lemma weight_le_less_iff: "weight_le s t \<Longrightarrow> weight_less s t \<longleftrightarrow> weight s < weight t"
  by (auto simp: weight_le_def weight_less_def)

lemma weight_less_iff: "weight_less s t \<Longrightarrow> weight_le s t \<and> weight s < weight t"
  by (auto simp: weight_le_def weight_less_def)


abbreviation "weight_NS \<equiv> {(t,s). weight_le s t}"

abbreviation "weight_S \<equiv> {(t,s). weight_less s t}"

lemma weight_le_mono_one:
  assumes S: "weight_le s t"
  shows "weight_le (Fun f (ss1 @ s # ss2)) (Fun f (ss1 @ t # ss2))" (is "weight_le ?s ?t")
proof -
  from S have w: "weight s \<le> weight t" and v: "vars_term_ms (SCF s) \<subseteq># vars_term_ms (SCF t)" 
    by (auto simp: weight_le_def)
  have v': "vars_term_ms (SCF ?s) \<subseteq># vars_term_ms (SCF ?t)"
    using mset_replicate_mono[OF v] by simp
  have w': "weight ?s \<le> weight ?t" using sum_list_replicate_mono[OF w] by simp
  from v' w' show ?thesis by (auto simp: weight_le_def)
qed

lemma weight_le_ctxt: "weight_le s t \<Longrightarrow> weight_le (C\<langle>s\<rangle>) (C\<langle>t\<rangle>)"
  by (induct C, auto intro: weight_le_mono_one)

lemma SCF_stable:
  assumes "vars_term_ms (SCF s) \<subseteq># vars_term_ms (SCF t)"
  shows "vars_term_ms (SCF (s \<cdot> \<sigma>)) \<subseteq># vars_term_ms (SCF (t \<cdot> \<sigma>))"
  unfolding scf_term_subst
  using vars_term_ms_subst_mono[OF assms].

lemma SN_weight_S: "SN weight_S"
proof-
  from wf_inv_image[OF wf_less]
  have wf: "wf {(s,t). weight s < weight t}" by (auto simp: inv_image_def)
  show ?thesis
    by (unfold SN_iff_wf, rule wf_subset[OF wf], auto simp: weight_less_def)
qed

lemma weight_less_imp_le: "weight_less s t \<Longrightarrow> weight_le s t" by (simp add: weight_less_def weight_le_def)

lemma weight_le_Var_Var: "weight_le (Var x) (Var y) \<longleftrightarrow> x = y"
  by (auto simp: weight_le_def)
end

context kbo begin

lemma kbo_altdef:
    "kbo s t = (if weight_le t s
      then if weight_less t s
        then (True, True)
        else (case s of
          Var y \<Rightarrow> (False, (case t of Var x \<Rightarrow> x = y | Fun g ts \<Rightarrow> ts = [] \<and> least g))
        | Fun f ss \<Rightarrow> (case t of
            Var x \<Rightarrow> (True, True)
          | Fun g ts \<Rightarrow> if pr_strict (f, length ss) (g, length ts)
            then (True, True)
            else if pr_weak (f, length ss) (g, length ts)
            then lex_ext_unbounded kbo ss ts
            else (False, False)))
      else (False, False))"
  by (simp add: weight_le_less_iff weight_le_def)

end

context admissible_kbo begin

lemma weight_le_stable:
  assumes "weight_le s t"
  shows "weight_le (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
  using assms weight_stable_le SCF_stable by (auto simp: weight_le_def)

lemma weight_less_stable:
  assumes "weight_less s t"
  shows "weight_less (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
  using assms weight_stable_lt SCF_stable by (auto simp: weight_less_def)

lemma simple_arg_pos_weight: "simple_arg_pos weight_NS (f,n) i"
  unfolding simple_arg_pos_def
proof (intro allI impI, unfold snd_conv fst_conv)
  fix ts :: "('f,'a)term list" 
  assume i: "i < n" and len: "length ts = n" 
  from id_take_nth_drop[OF i[folded len]] i[folded len]
  obtain us vs where id: "Fun f ts = Fun f (us @ ts ! i # vs)" 
    and us: "us = take i ts" 
    and len: "length us = i" by auto
  have "length us < Suc (length us + length vs)" by auto
  from scf[OF this, of f] obtain j where [simp]: "scf (f, Suc (length us + length vs)) (length us) = Suc j"
    by (rule lessE)
  show "(Fun f ts, ts ! i) \<in> weight_NS" 
    unfolding weight_le_def id by (auto simp: o_def)
qed

lemma weight_lemmas:
  shows "refl weight_NS" and "trans weight_NS" and "trans weight_S"
    and "weight_NS O weight_S \<subseteq> weight_S" and "weight_S O weight_NS \<subseteq> weight_S"
  by (auto intro!: refl_onI transI simp: weight_le_def weight_less_def)

interpretation kbo': admissible_kbo w w0 pr_strict' pr_weak' least scf
  by (rule admissible_kbo')

context
  assumes least_global: "\<And> f g. least f \<Longrightarrow> pr_weak g (f,0)"
    and least_trans: "\<And> f g. least f \<Longrightarrow> pr_weak (f,0) g \<Longrightarrow> least (fst g) \<and> snd g = 0" 
  fixes n :: nat
begin

lemma kbo_instance_of_wpo_with_assms: "wpo_with_assms 
  weight_S weight_NS (\<lambda>f g. (pr_strict f g, pr_weak f g))
     (\<lambda>(f, n). n = 0 \<and> least f) full_status False (\<lambda>f. False)" 
  apply (unfold_locales)
                      apply (auto simp: weight_lemmas SN_weight_S pr_SN pr_strict_irrefl
      weight_less_stable weight_le_stable weight_le_mono_one weight_less_imp_le
      simple_arg_pos_weight)
                 apply (force dest: least_global least_trans simp: pr_strict)+
            apply (auto simp: pr_strict least dest:pr_weak_trans)
  done

interpretation wpo: wpo_with_assms
  where S = weight_S and NS = weight_NS
    and prc = "\<lambda>f g. (pr_strict f g, pr_weak f g)" and prl = "\<lambda>(f,n). n = 0 \<and> least f"
    and c = "\<lambda>_. Lex"
    and ssimple = False and large = "\<lambda>f. False" and \<sigma>\<sigma> = full_status
    and n = n 
  by (rule kbo_instance_of_wpo_with_assms)

lemma kbo_as_wpo_with_assms: assumes "bounded_arity n (funas_term t)"
  shows "kbo s t = wpo.wpo s t"
proof -
  define m where "m = size s + size t" 
  from m_def assms show ?thesis
  proof (induct m arbitrary: s t rule: less_induct)
    case (less m s t)
    hence IH: "size si + size ti < size s + size t \<Longrightarrow> bounded_arity n (funas_term ti) \<Longrightarrow> kbo si ti = wpo.wpo si ti" for si ti :: "('f,'a)term" by auto
    note wpo_sI = arg_cong[OF wpo.wpo.simps, of fst, THEN iffD2]
    note wpo_nsI = arg_cong[OF wpo.wpo.simps, of snd, THEN iffD2]
    note bounded = less(3)
    show ?case
    proof (cases s)
      case s: (Var x)
      have "\<not> weight_less t (Var x)"
        by (metis leD weight.simps(1) weight_le_less_iff weight_less_imp_le weight_w0)
      thus ?thesis
        by (cases t, auto simp add: s kbo_altdef wpo.wpo.simps, simp add: weight_le_def)
    next
      case s: (Fun f ss)
      show ?thesis
      proof (cases t)
        case t: (Var y)
        { assume "weight_le t s"
          then have "\<exists>s' \<in> set ss. weight_le t s'"
            apply (auto simp: s t weight_le_def)
            by (metis scf set_scf_list weight_w0)
          then obtain s' where s': "s' \<in> set ss" and "weight_le t s'" by auto
          from this(2) have "wpo.wpo_ns s' t"
          proof (induct s')
            case (Var x)
            then show ?case by (auto intro!:wpo_nsI simp: t weight_le_Var_Var)
          next
            case (Fun f' ss')
            from this(2) have "\<exists>s'' \<in> set ss'. weight_le t s''"
              apply (auto simp: t weight_le_def)
              by (metis scf set_scf_list weight_w0)
            then obtain s'' where "s'' \<in> set ss'" and "weight_le t s''" by auto
            with Fun(1)[OF this] Fun(2)
            show ?case by (auto intro!: wpo_nsI simp: t in_set_conv_nth)
          qed
          with s' have "\<exists>s' \<in> set ss. wpo.wpo_ns s' t" by auto
        }
        then 
        show ?thesis unfolding wpo.wpo.simps[of s t] kbo_altdef[of s t]
          by (auto simp add: s t weight_less_iff set_conv_nth, auto)
      next
        case t: (Fun g ts)
        {
          fix j
          assume "j < length ts" 
          hence "ts ! j \<in> set ts" by auto
          hence "funas_term (ts ! j) \<subseteq> funas_term t" unfolding t by auto
          with bounded have "bounded_arity n (funas_term (ts ! j))" unfolding bounded_arity_def by auto
        } note bounded_tj = this
        note IH_tj = IH[OF _ this]
        show ?thesis
        proof (cases "\<not> weight_le t s \<or> weight_less t s")
          case True  
          thus ?thesis unfolding wpo.wpo.simps[of s t] kbo_altdef[of s t]
            unfolding s t by (auto simp: weight_less_iff)
        next
          case False
          let ?f = "(f,length ss)" 
          let ?g = "(g,length ts)" 
          from False have wle: "weight_le t s = True" "weight_less t s = False" 
            "(s, t) \<in> weight_NS \<longleftrightarrow> True" "(s, t) \<in> weight_S \<longleftrightarrow> False" by auto
          have lex: "(Lex = Lex \<and> Lex = Lex) = True" by simp
          have sig: "set (wpo.\<sigma> ?f) = {..<length ss}"
            "set (wpo.\<sigma> ?g) = {..<length ts}" by auto
          have map: "map ((!) ss) (wpo.\<sigma> ?f) = ss"
            "map ((!) ts) (wpo.\<sigma> ?g) = ts"
            by (auto simp: map_nth)
          have sizes: "i < length ss \<Longrightarrow> size (ss ! i) < size s" for i unfolding s
            by (simp add: size_simp1)
          have sizet: "i < length ts \<Longrightarrow> size (ts ! i) < size t" for i unfolding t
            by (simp add: size_simp1)
          have wpo: "wpo.wpo s t = 
             (if \<exists>i\<in>{..<length ss}. wpo.wpo_ns (ss ! i) t then (True, True)
              else if pr_weak ?f ?g \<and> (\<forall>j\<in>{..<length ts}. wpo.wpo_s s (ts ! j))
              then if pr_strict ?f ?g then (True, True) else lex_ext wpo.wpo n ss ts
              else (False, False))" 
            unfolding wpo.wpo.simps[of s t]
            unfolding s t term.simps split Let_def lex if_True sig map
            unfolding s[symmetric] t[symmetric] wle if_True weight_less_iff if_False False snd_conv by auto
          have "kbo s t = (if pr_strict ?f ?g then (True, True)
               else if pr_weak ?f ?g then lex_ext_unbounded kbo ss ts
               else (False, False))" 
            unfolding kbo_altdef[of s t]
            unfolding s t term.simps split Let_def if_True 
            unfolding s[symmetric] t[symmetric] wle if_True weight_less_iff if_False by auto
          also have "lex_ext_unbounded kbo ss ts = lex_ext kbo n ss ts" 
            using bounded[unfolded t] unfolding bounded_arity_def lex_ext_def by auto
          also have "\<dots> = lex_ext wpo.wpo n ss ts" 
            by (rule lex_ext_cong[OF refl refl refl], rule IH_tj, auto dest!: sizes sizet)
          finally have kbo: "kbo s t =
              (if pr_strict ?f ?g then (True, True)
               else if pr_weak ?f ?g then lex_ext wpo.wpo n ss ts
               else (False, False))" .
          show ?thesis
          proof (cases "\<exists>i\<in>{..<length ss}. wpo.wpo_ns (ss ! i) t")
            case True
            then obtain i where i: "i < length ss" and "wpo.wpo_ns (ss ! i) t" by auto
            then obtain b where "wpo.wpo (ss ! i) t = (b, True)" by (cases "wpo.wpo (ss ! i) t", auto)
            also have "wpo.wpo (ss ! i) t = kbo (ss ! i) t" using i by (intro IH[symmetric, OF _ bounded], auto dest: sizes)
            finally have "NS (ss ! i) t" by simp
            from kbo_supt_one[OF this]
            have "S (Fun f (take i ss @ ss ! i # drop (Suc i) ss)) t" .
            also have "(take i ss @ ss ! i # drop (Suc i) ss) = ss" using i by (metis id_take_nth_drop)
            also have "Fun f ss = s" unfolding s by simp
            finally have "S s t" .
            with S_imp_NS[OF this]
            have "kbo s t = (True,True)" by (cases "kbo s t", auto) 
            with True show ?thesis unfolding wpo by auto
          next
            case False
            hence False: "(\<exists>i\<in>{..<length ss}. wpo.wpo_ns (ss ! i) t) = False" by simp
            {
              fix j
              assume NS: "NS s t" 
              assume j: "j < length ts" 
              (* here we make use of proven properties of KBO: subterm-property and transitivity,
                 perhaps there is a simple proof without already using these properties *)
              from kbo_supt_one[OF NS_refl, of g "take j ts" "ts ! j" "drop (Suc j) ts"]
              have S: "S t (ts ! j)" using id_take_nth_drop[OF j] unfolding t by auto
              from kbo_trans[of s t "ts ! j"] NS S have "S s (ts ! j)" by auto
              with S S_imp_NS[OF this]
              have "kbo s (ts ! j) = (True, True)" by (cases "kbo s (ts ! j)", auto)
              hence "wpo.wpo_s s (ts ! j)" 
                by (subst IH_tj[symmetric], insert sizet[OF j] j, auto)
            }
            thus ?thesis unfolding wpo kbo False if_False using lex_ext_stri_imp_nstri[of wpo.wpo n ss ts]
              by (cases "lex_ext wpo.wpo n ss ts", auto simp: pr_strict split: if_splits)
          qed
        qed
      qed
    qed
  qed
qed
end

text \<open>This is the main theorem. It tells us that KBO can be seen as an instance of WPO, under mild preconditions:
  the parameter $n$ for the lexicographic extension has to be chosen high enough to cover the arities of all 
  terms that should be compared.\<close>
lemma defines "prec \<equiv> ((\<lambda>f g. (pr_strict' f g, pr_weak' f g)))" 
  and "prl \<equiv> (\<lambda>(f, n). n = 0 \<and> least f)" 
  shows 
    kbo_encoding_is_valid_wpo: "wpo_with_assms weight_S weight_NS prec prl full_status False (\<lambda>f. False)"
  and 
    kbo_as_wpo: "bounded_arity n (funas_term t) \<Longrightarrow> kbo s t = wpo.wpo n weight_S weight_NS prec prl full_status (\<lambda>_. Lex) False (\<lambda>f. False) s t" 
  unfolding prec_def prl_def
  subgoal by (intro admissible_kbo.kbo_instance_of_wpo_with_assms[OF admissible_kbo'] 
        least_pr_weak' least_pr_weak'_trans)
  apply (subst kbo'_eq_kbo[symmetric])
  apply (subst admissible_kbo.kbo_as_wpo_with_assms[OF admissible_kbo' least_pr_weak' least_pr_weak'_trans, symmetric], (auto)[3])
  by auto

text \<open>As a proof-of-concept we show that now properties of WPO can be used to prove these properties for KBO.
  Here, as example we consider closure under substitutions and strong normalization, 
  but the following idea can be applied for several more properties:
  if the property involves only terms where the arities are bounded, then just choose the parameter $n$ large enough.
  This even works for strong normalization, since in an infinite chain of KBO-decreases $t_1 > t_2 > t_3 > ...$ all terms have
  a weight of at most the weight of $t_1$, and this weight is also a bound on the arities.\<close>

lemma KBO_stable_via_WPO: "S s t \<Longrightarrow> S (s \<cdot> (\<sigma> :: ('f,'a) subst)) (t \<cdot> \<sigma>)"
proof -
  let ?terms = "{t, t \<cdot> \<sigma>}" (* collect all rhss of comparisons *)
  let ?prec = "((\<lambda>f g. (pr_strict' f g, pr_weak' f g)))" 
  let ?prl = "(\<lambda>(f, n). n = 0 \<and> least f)" 
  have "finite (\<Union> (funas_term ` ?terms))" 
    by auto
  from finite_list[OF this] obtain F where F: "set F = \<Union> (funas_term ` ?terms)" by auto
  (* since there only finitely many symbols, we can take n as the maximal arity *)
  define n where "n = max_list (map snd F)" 

  (* now get a WPO for this choice of n *)
  interpret wpo: wpo_with_assms
  where S = weight_S and NS = weight_NS
    and prc = ?prec and prl = ?prl
    and c = "\<lambda>_. Lex"
    and ssimple = False and large = "\<lambda>f. False" and \<sigma>\<sigma> = full_status
    and n = n 
    by (rule kbo_encoding_is_valid_wpo)

  {
    fix t
    assume "t \<in> ?terms" 
    hence "funas_term t \<subseteq> set F" unfolding F by auto
    hence "bounded_arity n (funas_term t)" unfolding bounded_arity_def 
      using max_list[of _ "map snd F", folded n_def] by fastforce
  }
  (* for all the terms we have that KBO = WPO *)
  note kbo_as_wpo = kbo_as_wpo[OF this]

  (* and finally transfer the existing property of WPO to KBO *)
  from wpo.WPO_S_subst[of s t \<sigma>]
  show "S s t \<Longrightarrow> S (s \<cdot> \<sigma>) (t \<cdot> \<sigma>)"
    using kbo_as_wpo by auto
qed

lemma weight_is_arity_bound: "weight t \<le> b \<Longrightarrow> bounded_arity b (funas_term t)" 
proof (induct t)
  case (Fun f ts)
  have "sum_list (map weight ts) \<le> weight (Fun f ts)" 
    using sum_list_scf_list[of ts "scf (f,length ts)", OF scf] by auto
  also have "\<dots> \<le> b" using Fun by auto
  finally have sum_b: "sum_list (map weight ts) \<le> b" .
  {
    fix t
    assume t: "t \<in> set ts" 
    from split_list[OF this] have "weight t \<le> sum_list (map weight ts)" by auto
    with sum_b have "bounded_arity b (funas_term t)" using t Fun by auto
  } note IH = this
  have "length ts = sum_list (map (\<lambda> _. 1) ts)" by (induct ts, auto)
  also have "\<dots> \<le> sum_list (map weight ts)"
    apply (rule sum_list_mono)
    subgoal for t using weight_gt_0[of t] by auto
    done
  also have "\<dots> \<le> b" by fact
  finally have len: "length ts \<le> b" by auto
  from IH len show ?case unfolding bounded_arity_def by auto
qed (auto simp: bounded_arity_def)
  
lemma KBO_SN_via_WPO: "SN {(s,t). S s t}"
proof 
  fix f :: "nat \<Rightarrow> ('f,'a)term" 
  assume "\<forall>i. (f i, f (Suc i)) \<in> {(s, t). S s t}" 
  hence steps: "S (f i) (f (Suc i))" for i by auto
  define n where "n = weight (f 0)"

  have w_bound: "weight (f i) \<le> n" for i
  proof (induct i)
    case (Suc i)
    from steps[of i] have "weight (f (Suc i)) \<le> weight (f i)" 
      unfolding kbo.simps[of "f i"] by (auto split: if_splits)
    with Suc show ?case by simp
  qed (auto simp: n_def)

  let ?prec = "((\<lambda>f g. (pr_strict' f g, pr_weak' f g)))" 
  let ?prl = "(\<lambda>(f, n). n = 0 \<and> least f)" 

  (* now get a WPO for this choice of n *)
  interpret wpo: wpo_with_assms
  where S = weight_S and NS = weight_NS
    and prc = ?prec and prl = ?prl
    and c = "\<lambda>_. Lex"
    and ssimple = False and large = "\<lambda>f. False" and \<sigma>\<sigma> = full_status
    and n = n 
    by (rule kbo_encoding_is_valid_wpo)

  have "kbo (f i) (f (Suc i)) = wpo.wpo (f i) (f (Suc i))" for i
    by (rule kbo_as_wpo[OF weight_is_arity_bound[OF w_bound]])
  (* for all the terms in the infinite sequence f 0, f 1, ... 
     we have that KBO = WPO *)

  (* and finally derive contradiction to SN-property of WPO *)
  from steps[unfolded this] wpo.WPO_S_SN show False by auto
qed

end
  
end