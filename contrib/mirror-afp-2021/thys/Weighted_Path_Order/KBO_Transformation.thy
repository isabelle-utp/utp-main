section \<open>The Knuth--Bendix Order as an instance of WPO\<close>

text \<open>Making the Knuth--Bendix an instance of WPO is more complicated than in the 
  case of RPO and LPO, because of syntactic and semantic differences. 
  We face the two main challenges in two different theories and sub-sections.\<close>

subsection \<open>Aligning least elements\<close>

text \<open>In all of RPO, LPO and WPO there is the concept of a minimal term, e.g., 
  a constant term $c$ where $c$ is least in precedence among \emph{all function symbols}. 
  By contrast, in KBO a constant $c$ is minimal if it has minimal weight and has
  least precende \emph{among all constants of minimal weight}.\<close>

text \<open>In this theory we prove that for any KBO one can modify the precedence in a way
  that least constants $c$ also have least precendence among \emph{all function symbols},
  without changing the defined order. Hence, afterwards it will be simpler to relate such 
  a KBO to WPO.\<close>

theory KBO_Transformation
  imports WPO Knuth_Bendix_Order.KBO
begin

context admissible_kbo
begin

lemma weight_w0_unary:
  assumes *: "weight t = w0" "t = Fun f ts" "ts = t1 # ts'"
  shows "ts' = []" "w (f,1) = 0" 
proof -
  have "w0 + sum_list (map weight ts') \<le> weight t1 + sum_list (map weight ts')" 
    by (rule add_right_mono, rule weight_w0)
  also have "\<dots> = sum_list (map weight ts)" unfolding * by simp
  also have "\<dots> \<le> sum_list (map weight (scf_list (scf (f, length ts)) ts))" 
    by (rule sum_list_scf_list, insert scf, auto)
  finally have "w (f,length ts) + w0 + sum_list (map weight ts') \<le> weight t" unfolding * by simp
  with *(1) have sum: "sum_list (map weight ts') = 0" and wf: "w (f,length ts) = 0" by auto
  with weight_gt_0 show ts': "ts' = []" by (cases ts', auto)
  with wf show "w (f,1) = 0" using * by auto
qed

definition lConsts :: "('f \<times> nat)set" where "lConsts = { (f,0) | f. least f}" 
definition pr_strict' where "pr_strict' f g = (f \<notin> lConsts \<and> (pr_strict f g \<or> g \<in> lConsts))"
definition pr_weak' where "pr_weak' f g = ((f \<notin> lConsts \<and> pr_weak f g) \<or> g \<in> lConsts)"

lemma admissible_kbo': "admissible_kbo w w0 pr_strict' pr_weak' least scf" 
  apply (unfold_locales)
  subgoal by (rule w0)
  subgoal by (rule w0)
  subgoal for f g n using adm[of f g n] unfolding pr_weak'_def by (auto simp: lConsts_def)
  subgoal for f using least[of f] unfolding pr_weak'_def lConsts_def by auto
  subgoal by (rule scf)
  subgoal for f using pr_weak_refl[of f] unfolding pr_weak'_def by auto
  subgoal for f g h using pr_weak_trans[of f g h] unfolding pr_weak'_def by auto
  subgoal for f g using pr_strict[of f g] unfolding pr_strict'_def pr_weak'_def by auto
proof -
  show "SN {(x, y). pr_strict' x y}" (is "SN ?R")
  proof 
    fix f
    assume "\<forall> i. (f i, f (Suc i)) \<in> ?R" 
    hence steps: "\<And> i. (f i, f (Suc i)) \<in> ?R" by blast
    have "f i \<notin> lConsts" for i using steps[of i] unfolding pr_strict'_def by auto
    hence "pr_strict (f i) (f (Suc i))" for i using steps[of i] unfolding pr_strict'_def by auto
    with pr_SN show False by auto
  qed
qed
 
lemma least_pr_weak': "least f \<Longrightarrow> pr_weak' g (f,0)" unfolding lConsts_def pr_weak'_def by auto

lemma least_pr_weak'_trans: "least f \<Longrightarrow> pr_weak' (f,0) g \<Longrightarrow> least (fst g) \<and> snd g = 0" 
  unfolding lConsts_def pr_weak'_def by auto

context
begin
interpretation kbo': admissible_kbo w w0 pr_strict' pr_weak' least scf
  by (rule admissible_kbo')

lemma kbo'_eq_kbo: "kbo'.kbo s t = kbo s t" 
proof (induct s t rule: kbo.induct)
  case (1 s t)
  note simps = kbo.simps[of s t] kbo'.kbo.simps[of s t]
  show ?case unfolding simps
    apply (intro if_cong refl, intro term.case_cong refl)
  proof -
    fix f ss g ts
    assume *: "vars_term_ms (SCF t) \<subseteq># vars_term_ms (SCF s) \<and> weight t \<le> weight s"
      "\<not> weight t < weight s"
      and s: "s = Fun f ss"
      and t: "t = Fun g ts"
    let ?g = "(g,length ts)" 
    let ?f = "(f,length ss)" 
    have IH: "(if pr_strict ?f ?g then (True, True)
        else if pr_weak ?f ?g then lex_ext_unbounded kbo ss ts else (False, False))
      = (if pr_strict ?f ?g then (True, True)
        else if pr_weak ?f ?g then lex_ext_unbounded kbo'.kbo ss ts else (False, False))" 
      by (intro if_cong refl lex_ext_unbounded_cong, insert 1[OF * s t], auto)
    let ?P = "pr_strict' ?f ?g = pr_strict ?f ?g \<and> (\<not> pr_strict ?f ?g \<longrightarrow> pr_weak' ?f ?g = pr_weak ?f ?g)" 
    show "(if pr_strict' ?f ?g then (True, True)
        else if pr_weak' ?f ?g then lex_ext_unbounded kbo'.kbo ss ts else (False, False)) =
       (if pr_strict ?f ?g then (True, True)
        else if pr_weak ?f ?g then lex_ext_unbounded kbo ss ts else (False, False))" 
    proof (cases ?P)
      case True
      thus ?thesis unfolding IH by auto
    next
      case notP: False  
      hence fgC: "?f \<in> lConsts \<or> ?g \<in> lConsts" unfolding pr_strict'_def pr_weak'_def by auto
      hence weight: "weight s = w0" "weight t = w0" using * unfolding lConsts_def least s t by auto
      show ?thesis
      proof (cases "ss = [] \<and> ts = []")
        case empty: True
        with weight have "w ?f = w0" "w ?g = w0" unfolding s t by auto
        with empty have ?P unfolding pr_strict'_def pr_weak'_def using pr_weak_trans[of _ "(g,0)" "(f,0)"]
            pr_weak_trans[of _ "(f,0)" "(g,0)"]
          by (auto simp: lConsts_def pr_strict least)
        with notP show ?thesis by blast
      next
        case False
        {
          fix f and t :: "('f,'a)term"  and t1 ts' ts and g
          assume *: "weight t = w0" "t = Fun f ts" "ts = t1 # ts'"
          from weight_w0_unary[OF this]
          have ts': "ts' = []" and w: "w (f,1) = 0" .
          from adm[OF w] ts' 
          have "pr_weak (f, Suc (length ts')) g" by (cases g, auto)
        } note unary = this
        from fgC have "ss = [] \<or> ts = []" unfolding lConsts_def least by auto  
        thus ?thesis
        proof
          assume ss: "ss = []" 
          with False obtain t1 ts' where ts: "ts = t1 # ts'" by (cases ts, auto)
          show ?thesis unfolding ss ts using unary[OF weight(2) t ts]
            by (simp add: lex_ext_unbounded.simps pr_strict'_def lConsts_def pr_strict)
        next
          assume ts: "ts = []" 
          with False obtain s1 ss' where ss: "ss = s1 # ss'" by (cases ss, auto)
          show ?thesis unfolding ss ts using unary[OF weight(1) s ss]
            by (simp add: lex_ext_unbounded.simps pr_strict'_def pr_weak'_def lConsts_def pr_strict)
        qed
      qed
    qed
  qed
qed
end
end
end