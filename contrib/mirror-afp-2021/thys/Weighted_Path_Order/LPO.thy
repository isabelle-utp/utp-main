section \<open>The Lexicographic Path Order as an instance of WPO\<close>

text \<open>We first directly define the strict- and non-strict lexicographic path orders (LPO)
  w.r.t.\ some precedence, and then show that it is an instance of WPO.
  For this instance we use the trivial reduction pair in WPO ($\emptyset$, UNIV) and
  the status is the full one, i.e., taking parameters [0,..,n-1] for each n-ary symbol.\<close>

theory LPO
  imports
    WPO
begin

context
  fixes "pr" :: "('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool)"
    and prl :: "'f \<times> nat \<Rightarrow> bool"
    and n :: nat
begin
fun lpo :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool \<times> bool" 
  where
    "lpo (Var x) (Var y) = (False, x = y)" |
    "lpo (Var x) (Fun g ts) = (False, ts = [] \<and> prl (g,0))" |
    "lpo (Fun f ss) (Var y) = (let con = (\<exists> s \<in> set ss. snd (lpo s (Var y))) in (con,con))" |
    "lpo (Fun f ss) (Fun g ts) = (
      if (\<exists> s \<in> set ss. snd (lpo s (Fun g ts)))
         then (True,True)
         else (let (prs,prns) = pr (f,length ss) (g,length ts) in 
           if prns \<and> (\<forall> t \<in> set ts. fst (lpo (Fun f ss) t))
           then if prs
              then (True,True) 
              else lex_ext lpo n ss ts
           else (False,False)))"

end


locale lpo_with_assms = precedence prc prl
  for prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool"
    and prl :: "'f \<times> nat \<Rightarrow> bool"
    and n :: nat
begin

sublocale wpo_with_assms n "{}" UNIV prc prl full_status "\<lambda> _. Lex" False "\<lambda> _. False"
  by (unfold_locales, auto simp: refl_on_def trans_def simple_arg_pos_def)

abbreviation "lpo_pr \<equiv> lpo prc prl n" 
abbreviation "lpo_s \<equiv> \<lambda> s t. fst (lpo_pr s t)"
abbreviation "lpo_ns \<equiv> \<lambda> s t. snd (lpo_pr s t)"

lemma lpo_eq_wpo: "lpo_pr s t = wpo s t"
proof - 
  note simps = wpo.simps
  show ?thesis 
  proof (induct s t rule: lpo.induct[of _ prc prl n])
    case (1 x y)
    then show ?case by (simp add: simps)
  next
    case (2 x g ts)
    then show ?case by (auto simp: simps)
  next
    case (3 f ss y)
    then show ?case by (auto simp: simps[of "Fun f ss" "Var y"] Let_def set_conv_nth)
  next
    case IH: (4 f ss g ts)
    have id: "\<And> s. (s \<in> {}) = False" "\<And> s. (s \<in> UNIV) = True" 
      and "(\<exists>i\<in>{0..<length ss}. wpo_ns (ss ! i) t) = (\<exists>si\<in>set ss. wpo_ns si t)" 
      by (auto, force simp: set_conv_nth) 
    have id': "map ((!) ss) (\<sigma> (f, length ss)) = ss" for f ss by (intro nth_equalityI, auto)
    have ex: "(\<exists>i\<in>set (\<sigma> (f, length ss)). wpo_ns (ss ! i) (Fun g ts)) = (\<exists> si \<in> set ss. lpo_ns si (Fun g ts))" 
      using IH(1) unfolding set_conv_nth by auto
    obtain prs prns where prc: "prc (f, length ss) (g, length ts) = (prs, prns)" by force
    have lex: "(Lex = Lex \<and> Lex = Lex) = True" by simp
    show ?case
      unfolding lpo.simps simps[of "Fun f ss" "Fun g ts"] term.simps id id' if_False if_True lex
        Let_def ex prc split
    proof (rule sym, rule if_cong[OF refl refl], rule if_cong[OF conj_cong[OF refl] if_cong[OF refl refl] refl])
      assume "\<not> (\<exists>si\<in>set ss. lpo_ns si (Fun g ts))" 
      note IH = IH(2-)[OF this prc[symmetric] refl]
      from IH(1) show "(\<forall>j\<in>set (\<sigma> (g, length ts)). wpo_s (Fun f ss) (ts ! j)) = (\<forall>t\<in>set ts. lpo_s (Fun f ss) t)"
        unfolding set_conv_nth by auto
      assume "prns \<and> (\<forall>t\<in>set ts. lpo_s (Fun f ss) t)" "\<not> prs" 
      note IH = IH(2-)[OF this]
      show "lex_ext wpo n ss ts = lex_ext lpo_pr n ss ts" 
        using IH by (intro lex_ext_cong, auto)
    qed
  qed
qed

abbreviation "LPO_S \<equiv> {(s,t). lpo_s s t}"
abbreviation "LPO_NS \<equiv> {(s,t). lpo_ns s t}"

theorem LPO_SN_order_pair: "SN_order_pair LPO_S LPO_NS"
  unfolding lpo_eq_wpo by (rule WPO_SN_order_pair)

theorem LPO_S_subst: "(s,t) \<in> LPO_S \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> LPO_S" for \<sigma> :: "('f,'a)subst" 
  using WPO_S_subst unfolding lpo_eq_wpo .

theorem LPO_NS_subst: "(s,t) \<in> LPO_NS \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> LPO_NS" for \<sigma> :: "('f,'a)subst"
  using WPO_NS_subst unfolding lpo_eq_wpo .

theorem LPO_NS_ctxt: "(s,t) \<in> LPO_NS \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> LPO_NS" 
  using WPO_NS_ctxt unfolding lpo_eq_wpo .

theorem LPO_S_ctxt: "(s,t) \<in> LPO_S \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> LPO_S" 
  using WPO_S_ctxt unfolding lpo_eq_wpo by auto

theorem LPO_S_subset_LPO_NS: "LPO_S \<subseteq> LPO_NS" 
  using WPO_S_subset_WPO_NS unfolding lpo_eq_wpo .

theorem supt_subset_LPO_S: "{\<rhd>} \<subseteq> LPO_S" 
  using supt_subset_WPO_S unfolding lpo_eq_wpo by auto

theorem supteq_subset_LPO_NS: "{\<unrhd>} \<subseteq> LPO_NS" 
  using supteq_subset_WPO_NS unfolding lpo_eq_wpo by auto

end

end
