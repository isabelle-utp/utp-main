section \<open>The Recursive Path Order as an instance of WPO\<close>

text \<open>This theory defines the recursive path order (RPO) that given two terms provides two Booleans,
  whether the terms can be strictly or non-strictly oriented. It is proven that RPO is an instance of WPO, and hence,
  carries over all the nice properties of WPO immediately.\<close>
theory RPO
  imports
    WPO
begin

context
  fixes "pr" :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool"
    and prl :: "'f \<times> nat \<Rightarrow> bool"
    and c :: "'f \<times> nat \<Rightarrow> order_tag" 
    and n :: nat
begin

fun rpo  :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool \<times> bool" 
  where
    "rpo (Var x) (Var y) = (False, x = y)" |
    "rpo (Var x) (Fun g ts) = (False, ts = [] \<and> prl (g,0))" |
    "rpo (Fun f ss) (Var y) = (let con = (\<exists> s \<in> set ss. snd (rpo s (Var y))) in (con,con))" |
    "rpo (Fun f ss) (Fun g ts) = (
    if (\<exists> s \<in> set ss. snd (rpo s (Fun g ts)))
       then (True,True)
       else (let (prs,prns) = pr (f,length ss) (g,length ts) in 
         if prns \<and> (\<forall> t \<in> set ts. fst (rpo (Fun f ss) t))
         then if prs
              then (True,True) 
              else if c (f,length ss) = Lex \<and> c (g,length ts) = Lex
                   then lex_ext rpo n ss ts
                   else if c (f,length ss) = Mul \<and> c (g,length ts) = Mul
                        then mul_ext rpo ss ts
                        else (length ss \<noteq> 0 \<and> length ts = 0, length ts = 0)
          else (False,False)))"
end

locale rpo_with_assms = precedence prc prl
  for prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool"
    and prl :: "'f \<times> nat \<Rightarrow> bool"
    and c :: "'f \<times> nat \<Rightarrow> order_tag" 
    and n :: nat
begin

sublocale wpo_with_assms n "{}" UNIV prc prl full_status c False "\<lambda> _. False"
  by (unfold_locales, auto simp: refl_on_def trans_def simple_arg_pos_def)

abbreviation "rpo_pr \<equiv> rpo prc prl c n" 
abbreviation "rpo_s \<equiv> \<lambda> s t. fst (rpo_pr s t)"
abbreviation "rpo_ns \<equiv> \<lambda> s t. snd (rpo_pr s t)"

lemma rpo_eq_wpo: "rpo_pr s t = wpo s t"
proof -
  note simps = wpo.simps
  show ?thesis
  proof (induct s t rule: rpo.induct[of _ prc prl c n])
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
    have ex: "(\<exists>i\<in>set (\<sigma> (f, length ss)). wpo_ns (ss ! i) (Fun g ts)) = (\<exists> si \<in> set ss. rpo_ns si (Fun g ts))" 
      using IH(1) unfolding set_conv_nth by auto
    obtain prs prns where prc: "prc (f, length ss) (g, length ts) = (prs, prns)" by force
    show ?case
      unfolding rpo.simps simps[of "Fun f ss" "Fun g ts"] term.simps id id' if_False if_True
        Let_def ex prc split
    proof (rule sym, rule if_cong[OF refl refl], rule if_cong[OF conj_cong[OF refl] if_cong[OF refl refl if_cong[OF refl _ if_cong]] refl])
      assume "\<not> (\<exists>si\<in>set ss. rpo_ns si (Fun g ts))" 
      note IH = IH(2-)[OF this prc[symmetric] refl]
      from IH(1) show "(\<forall>j\<in>set (\<sigma> (g, length ts)). wpo_s (Fun f ss) (ts ! j)) = (\<forall>t\<in>set ts. rpo_s (Fun f ss) t)"
        unfolding set_conv_nth by auto
      assume "prns \<and> (\<forall>t\<in>set ts. rpo_s (Fun f ss) t)" "\<not> prs" 
      note IH = IH(2-)[OF this]
      {
        assume "c (f, length ss) = Lex \<and> c (g, length ts) = Lex" 
        from IH(1)[OF this]
        show "lex_ext wpo n ss ts = lex_ext rpo_pr n ss ts" 
          by (intro lex_ext_cong, auto)
      }
      {
        assume "\<not> (c (f, length ss) = Lex \<and> c (g, length ts) = Lex)" "c (f, length ss) = Mul \<and> c (g, length ts) = Mul" 
        from IH(2)[OF this]
        show "mul_ext wpo ss ts = mul_ext rpo_pr ss ts" 
          by (intro mul_ext_cong, auto)
      }
    qed auto
  qed
qed


abbreviation "RPO_S \<equiv> {(s,t). rpo_s s t}"
abbreviation "RPO_NS \<equiv> {(s,t). rpo_ns s t}"

theorem RPO_SN_order_pair: "SN_order_pair RPO_S RPO_NS"
  unfolding rpo_eq_wpo by (rule WPO_SN_order_pair)

theorem RPO_S_subst: "(s,t) \<in> RPO_S \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> RPO_S" for \<sigma> :: "('f,'a)subst" 
  using WPO_S_subst unfolding rpo_eq_wpo .

theorem RPO_NS_subst: "(s,t) \<in> RPO_NS \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> RPO_NS" for \<sigma> :: "('f,'a)subst"
  using WPO_NS_subst unfolding rpo_eq_wpo .

theorem RPO_NS_ctxt: "(s,t) \<in> RPO_NS \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> RPO_NS" 
  using WPO_NS_ctxt unfolding rpo_eq_wpo .

theorem RPO_S_ctxt: "(s,t) \<in> RPO_S \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> RPO_S" 
  using WPO_S_ctxt unfolding rpo_eq_wpo by auto

theorem RPO_S_subset_RPO_NS: "RPO_S \<subseteq> RPO_NS" 
  using WPO_S_subset_WPO_NS unfolding rpo_eq_wpo .

theorem supt_subset_RPO_S: "{\<rhd>} \<subseteq> RPO_S" 
  using supt_subset_WPO_S unfolding rpo_eq_wpo by auto

theorem supteq_subset_RPO_NS: "{\<unrhd>} \<subseteq> RPO_NS" 
  using supteq_subset_WPO_NS unfolding rpo_eq_wpo by auto

end
end
