section \<open>The Weighted Path Order\<close>

text \<open>This is a version of WPO that also permits multiset comparisons of lists of terms.
  It therefore generalizes RPO.\<close>

theory WPO
  imports
    Knuth_Bendix_Order.Lexicographic_Extension
    Knuth_Bendix_Order.Term_Aux
    Knuth_Bendix_Order.Order_Pair
    Polynomial_Factorization.Missing_List
    Status
    Precedence
    Multiset_Extension2
begin

datatype order_tag = Lex | Mul

locale wpo =
  fixes n :: nat
    and S NS :: "('f, 'v) term rel"
    and "prc" :: "('f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool)"
    and prl :: "'f \<times> nat \<Rightarrow> bool"
    and \<sigma>\<sigma> :: "'f status"
    and c :: "'f \<times> nat \<Rightarrow> order_tag" 
    and ssimple :: bool
    and large :: "'f \<times> nat \<Rightarrow> bool" 
begin

fun wpo :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool \<times> bool" 
  where
    "wpo s t =
    (case s of
      Var x \<Rightarrow> (False, 
        (case t of 
          Var y \<Rightarrow> x = y 
        | Fun g ts \<Rightarrow> (s, t) \<in> NS \<and> status \<sigma>\<sigma> (g, length ts) = [] \<and> prl (g, length ts)))
    | Fun f ss \<Rightarrow>
      if (s, t) \<in> S then (True, True)
      else if (s, t) \<in> NS then
        if \<exists> i \<in> set (status \<sigma>\<sigma> (f, length ss)). snd (wpo (ss ! i) t) then (True, True)
        else
          (case t of
            Var _ \<Rightarrow> (False, ssimple \<and> large (f, length ss))
          | Fun g ts \<Rightarrow> 
            (case prc (f, length ss) (g, length ts) of (prs, prns) \<Rightarrow>            
              if prns \<and> (\<forall> j \<in> set (status \<sigma>\<sigma> (g, length ts)). fst (wpo s (ts ! j))) then 
                if prs then (True, True)
                else let ss' = map (\<lambda> i. ss ! i) (status \<sigma>\<sigma> (f, length ss));
                         ts' = map (\<lambda> i. ts ! i) (status \<sigma>\<sigma> (g, length ts));
                         cf = c (f,length ss);
                         cg = c (g,length ts)    
                   in if cf = Lex \<and> cg = Lex 
                      then lex_ext wpo n ss' ts'
                      else if cf = Mul \<and> cg = Mul
                           then mul_ext wpo ss' ts'
                           else (length ss' \<noteq> 0 \<and> length ts' = 0, length ts' = 0)
              else (False, False)))
      else (False, False))"

declare wpo.simps [simp del]

abbreviation wpo_s (infix "\<succ>" 50) where "s \<succ> t \<equiv> fst (wpo s t)"
abbreviation wpo_ns (infix "\<succeq>" 50) where "s \<succeq> t \<equiv> snd (wpo s t)"

abbreviation "WPO_S \<equiv> {(s,t). s \<succ> t}"
abbreviation "WPO_NS \<equiv> {(s,t). s \<succeq> t}"

lemma wpo_s_imp_ns: "s \<succ> t \<Longrightarrow> s \<succeq> t"
  using lex_ext_stri_imp_nstri
  unfolding wpo.simps[of s t]
  by (auto simp: Let_def mul_ext_stri_imp_nstri split: term.splits if_splits prod.splits)

end

declare wpo.wpo.simps[code]


definition strictly_simple_status :: "'f status \<Rightarrow> ('f,'v)term rel \<Rightarrow> bool" where
  "strictly_simple_status \<sigma> rel = 
    (\<forall> f ts i. i \<in> set (status \<sigma> (f,length ts)) \<longrightarrow> (Fun f ts, ts ! i) \<in> rel)" 

locale wpo_with_assms = wpo +
  SN_order_pair + precedence +
  constrains S :: "('f, 'v) term rel" and NS :: _
    and prc :: "'f \<times> nat \<Rightarrow> 'f \<times> nat \<Rightarrow> bool \<times> bool"
    and prl :: "'f \<times> nat \<Rightarrow> bool"
    and ssimple :: bool
    and large :: "'f \<times> nat \<Rightarrow> bool" 
    and c :: "'f \<times> nat \<Rightarrow> order_tag" 
    and n :: nat
    and \<sigma>\<sigma> :: "'f status"
  assumes subst_S: "(s,t) \<in> S \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> S"
    and subst_NS: "(s,t) \<in> NS \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> NS"
    and ctxt_NS: "(s,t) \<in> NS \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> NS" 
    and S_imp_NS: "S \<subseteq> NS"
    and ws_status: "i \<in> set (status \<sigma>\<sigma> fn) \<Longrightarrow> simple_arg_pos NS fn i"
    and large: "ssimple \<Longrightarrow> large fn \<Longrightarrow> fst (prc fn gm) \<or> snd (prc fn gm) \<and> status \<sigma>\<sigma> gm = []"  
    and large_trans: "ssimple \<Longrightarrow> large fn \<Longrightarrow> snd (prc gm fn) \<Longrightarrow> large gm"  
    and ss_status: "ssimple \<Longrightarrow> i \<in> set (status \<sigma>\<sigma> fn) \<Longrightarrow> simple_arg_pos S fn i"
    and ss_S_non_empty: "ssimple \<Longrightarrow> S \<noteq> {}"
begin

lemma ss_NS_not_UNIV: "ssimple \<Longrightarrow> NS \<noteq> UNIV"
proof
  assume "ssimple" "NS = UNIV" 
  with ss_S_non_empty obtain a b where "(a,b) \<in> S" "(b,a) \<in> NS" by auto
  from compat_S_NS_point[OF this] have "(a,a) \<in> S" .
  with SN show False by fast
qed

abbreviation "\<sigma> \<equiv> status \<sigma>\<sigma>"


lemmas \<sigma> = status[of \<sigma>\<sigma>]

lemma NS_arg: assumes i: "i \<in> set (\<sigma> (f,length ts))"
  shows "(Fun f ts, ts ! i) \<in> NS"
  by (rule ws_status[OF i, unfolded simple_arg_pos_def fst_conv, rule_format],
      insert \<sigma>[of f "length ts"] i, auto)

lemma NS_subterm: assumes all: "\<And> f k. set (\<sigma> (f,k)) = {0 ..< k}"
  shows "s \<unrhd> t \<Longrightarrow> (s,t) \<in> NS"
proof (induct s t rule: supteq.induct)
  case (refl)
  from refl_NS show ?case unfolding refl_on_def by blast
next
  case (subt s ss t f)
  from subt(1) obtain i where i: "i < length ss" and s: "s = ss ! i" unfolding set_conv_nth by auto
  from NS_arg[of i f ss, unfolded all] s i have "(Fun f ss, s) \<in> NS" by auto
  from trans_NS_point[OF this subt(3)] show ?case .
qed


lemma \<sigma>E: "i \<in> set (\<sigma> (f, length ss)) \<Longrightarrow> ss ! i \<in> set ss" by (rule status_aux)

lemma wpo_ns_refl: 
  shows "s \<succeq> s"
proof (induct s)
  case (Fun f ss)
  {
    fix i
    assume si: "i \<in> set (\<sigma> (f,length ss))"
    from NS_arg[OF this] have "(Fun f ss, ss ! i) \<in> NS" .
    with si Fun[OF \<sigma>E[OF si]] have "wpo_s (Fun f ss) (ss ! i)" unfolding wpo.simps[of "Fun f ss" "ss ! i"]
      by auto
  } note wpo_s = this
  let ?ss = "map (\<lambda> i. ss ! i) (\<sigma> (f,length ss))"
  have rec11: "snd (lex_ext wpo n ?ss ?ss)"
    by (rule all_nstri_imp_lex_nstri, insert \<sigma>E[of _ f ss], auto simp: Fun)
  have rec12: "snd (mul_ext wpo ?ss ?ss)"
    unfolding mul_ext_def Let_def snd_conv 
    by (intro ns_mul_ext_refl_local,
        unfold locally_refl_def, auto simp: in_multiset_in_set[of ?ss] intro!: Fun status_aux)
  from rec11 rec12 show ?case using refl_NS_point prc_refl wpo_s
    by (cases "c (f,length ss)", auto simp: wpo.simps[of "Fun f ss" "Fun f ss"])
qed (simp add: wpo.simps)

lemma wpo_ns_imp_NS: "s \<succeq> t \<Longrightarrow> (s,t) \<in> NS" 
  using S_imp_NS
  by (cases s, auto simp: wpo.simps[of _ t], cases t, 
      auto simp: refl_NS_point split: if_splits)

lemma wpo_s_imp_NS: "s \<succ> t \<Longrightarrow> (s,t) \<in> NS" 
  by (rule wpo_ns_imp_NS[OF wpo_s_imp_ns])

lemma S_imp_wpo_s: assumes st: "(s,t) \<in> S"
  shows "s \<succ> t"
proof (cases s)
  case (Fun f ss)
  then show ?thesis using st by (auto simp: wpo.simps)
next
  case (Var x)
  from SN_imp_minimal[OF SN, rule_format, of undefined UNIV]
  obtain s where "\<And> u. (s,u) \<notin> S" by blast
  with subst_S[OF st[unfolded Var], of "\<lambda> _. s"]
  have False by auto
  then show ?thesis by auto
qed

lemma wpo_least_1: assumes "prl (f,length ss)" 
  and "(t, Fun f ss) \<in> NS"
  and "\<sigma> (f,length ss) = []"
shows "t \<succeq> Fun f ss"
proof (cases t)
  case (Var x)
  with assms show ?thesis by (simp add: wpo.simps)
next
  case (Fun g ts)
  let ?f = "(f,length ss)"
  let ?g = "(g,length ts)"
  obtain s ns where "prc ?g ?f = (s,ns)" by force
  with prl[OF assms(1), of ?g] have prc: "prc ?g ?f = (s,True)" by auto
  show ?thesis using assms(2)
    unfolding Fun 
    unfolding wpo.simps[of "Fun g ts" "Fun f ss"] term.simps assms(3)
    by (auto simp: prc lex_ext_least_1 mul_ext_def ns_mul_ext_bottom Let_def)
qed

lemma wpo_least_2: assumes "prl (f,length ss)" (is "prl ?f")
  and "(Fun f ss, t) \<notin> S"
  and "\<sigma> (f,length ss) = []"
shows "\<not> Fun f ss \<succ> t"
proof (cases t)
  case (Var x)
  with Var show ?thesis using assms(2-3) by (auto simp: wpo.simps split: if_splits)
next
  case (Fun g ts)
  let ?g = "(g,length ts)"
  obtain s ns where "prc ?f ?g = (s,ns)" by force
  with prl2[OF assms(1), of ?g] have prc: "prc ?f ?g = (False,ns)" by auto
  show ?thesis using assms(2) assms(3) unfolding Fun 
    by (simp add: wpo.simps[of _ "Fun g ts"] lex_ext_least_2 prc
        mul_ext_def s_mul_ext_bottom_strict Let_def)
qed


lemma wpo_least_3: assumes "prl (f,length ss)" (is "prl ?f") 
  and ns: "Fun f ss \<succeq> t"
  and NS: "(u, Fun f ss) \<in> NS"
  and ss: "\<sigma> (f,length ss) = []"
  and S: "\<And> x. (Fun f ss, x) \<notin> S"
  and u: "u = Var x" 
shows "u \<succeq> t"
proof (cases "(Fun f ss, t) \<in> S \<or> (u, Fun f ss) \<in> S \<or> (u, t) \<in> S")
  case True
  with wpo_ns_imp_NS[OF ns] NS compat_NS_S_point compat_S_NS_point have "(u, t) \<in> S" by blast
  from wpo_s_imp_ns[OF S_imp_wpo_s[OF this]] show ?thesis .
next
  case False
  from trans_NS_point[OF NS wpo_ns_imp_NS[OF ns]] have utA: "(u, t) \<in> NS" .
  show ?thesis
  proof (cases t)
    case t: (Var y)
    with ns False ss have *: "ssimple" "large (f,length ss)" 
      by (auto simp: wpo.simps split: if_splits)
    show ?thesis 
    proof (cases "x = y")
      case True
      thus ?thesis using ns * False utA ss
        unfolding wpo.simps[of u t] wpo.simps[of "Fun f ss" t]
        unfolding t u term.simps
        by (auto split: if_splits)
    next
      case False
      from utA[unfolded t u] 
      have "(Var x, Var y) \<in> NS" .
      from False subst_NS[OF this, of "\<lambda> z. if z = x then v else w" for v w]
      have "(v,w) \<in> NS" for v w by auto
      hence "NS = UNIV" by auto
      with ss_NS_not_UNIV[OF `ssimple`]
      have False by auto
      thus ?thesis ..
    qed
  next
    case (Fun g ts)
    let ?g = "(g,length ts)"
    obtain s ns where "prc ?f ?g = (s,ns)" by force
    with prl2[OF \<open>prl ?f\<close>, of ?g] have prc: "prc ?f ?g = (False,ns)" by auto
    show ?thesis
    proof (cases "\<sigma> ?g")
      case Nil
      with False Fun assms prc have "prc ?f ?g = (False,True)" 
        by (auto simp:  wpo.simps split: if_splits)
      with prl3[OF \<open>prl ?f\<close>, of ?g] have "prl ?g" by auto
      show ?thesis using utA unfolding Fun by (rule wpo_least_1[OF \<open>prl ?g\<close>], simp add: Nil)
    next
      case (Cons t1 tts)
      have "\<not> wpo_s (Fun f ss) (ts ! t1)" by (rule wpo_least_2[OF \<open>prl ?f\<close> S ss])
      with \<open>wpo_ns (Fun f ss) t\<close> False Fun Cons 
      have False by (simp add: ss wpo.simps split: if_splits)
      then show ?thesis ..
    qed
  qed
qed

(* Transitivity / compatibility of the orders *)
lemma wpo_compat: "
  (s \<succeq> t \<and> t \<succ> u \<longrightarrow> s \<succ> u) \<and>
  (s \<succ> t \<and> t \<succeq> u \<longrightarrow> s \<succ> u) \<and>
  (s \<succeq> t \<and> t \<succeq> u \<longrightarrow> s \<succeq> u)" (is "?tran s t u")
proof (induct "(s,t,u)" arbitrary: s t u rule: wf_induct[OF wf_measures[of "[\<lambda> (s,t,u). size s, \<lambda> (s,t,u). size t, \<lambda> (s,t,u). size u]"]])
  case 1
  note ind = 1[simplified]
  show "?tran s t u"
  proof (cases "(s,t) \<in> S \<or> (t,u) \<in> S \<or> (s,u) \<in> S")
    case True
    {
      assume st: "wpo_ns s t" and tu: "wpo_ns t u"
      from wpo_ns_imp_NS[OF st] wpo_ns_imp_NS[OF tu]
        True compat_NS_S_point compat_S_NS_point have "(s,u) \<in> S" by blast
      from S_imp_wpo_s[OF this] have "wpo_s s u" .
    }
    with wpo_s_imp_ns show ?thesis by blast
  next
    case False
    then have stS: "(s,t) \<notin> S" and tuS: "(t,u) \<notin> S" and suS: "(s,u) \<notin> S" by auto
    show ?thesis
    proof (cases t)
      note [simp] = wpo.simps[of s u] wpo.simps[of s t] wpo.simps[of t u]
      case (Var x)
      note wpo.simps[simp]
      show ?thesis
      proof safe
        assume "wpo_s t u"
        with Var show "wpo_s s u" by (cases u, auto)
      next
        assume gr: "wpo_s s t" and ge: "wpo_ns t u"
        from wpo_s_imp_NS[OF gr] have stA: "(s,t) \<in> NS" .
        from wpo_ns_imp_NS[OF ge] have tuA: "(t,u) \<in> NS" .
        from trans_NS_point[OF stA tuA] have suA: "(s,u) \<in> NS" .
        show "wpo_s s u"
        proof (cases u)
          case (Var y)
          with ge \<open>t = Var x\<close> have "t = u" by auto
          with gr show ?thesis by auto
        next
          case (Fun h us)
          let ?h = "(h,length us)"
          from Fun ge Var have us: "\<sigma> ?h = []" and pri: "prl ?h" by auto
          from gr Var obtain f ss where s: "s = Fun f ss" by (cases s, auto)
          let ?f = "(f,length ss)"
          from s gr Var False obtain i where i: "i \<in> set (\<sigma> ?f)" and sit: "ss ! i \<succeq> t" by (auto split: if_splits)        
          from trans_NS_point[OF wpo_ns_imp_NS[OF sit] tuA] have siu: "(ss ! i,u) \<in> NS" .
          from wpo_least_1[OF pri siu[unfolded Fun us] us]
          have "ss ! i \<succeq> u" unfolding Fun us .
          with i have "\<exists> i \<in> set (\<sigma> ?f). ss ! i \<succeq> u" by auto
          with s suA show ?thesis by simp
        qed
      next
        assume ge1: "wpo_ns s t" and ge2: "wpo_ns t u"
        show "wpo_ns s u"
        proof (cases u)
          case (Var y)
          with ge2 \<open>t = Var x\<close> have "t = u" by auto
          with ge1 show ?thesis by auto
        next
          case (Fun h us)
          let ?h = "(h,length us)"
          from Fun ge2 Var have us: "\<sigma> ?h = []" and pri: "prl ?h" by auto
          show ?thesis unfolding Fun us
            by (rule wpo_least_1[OF pri trans_NS_point[OF wpo_ns_imp_NS[OF ge1] 
                    wpo_ns_imp_NS[OF ge2[unfolded Fun us]]] us]) 
        qed
      qed
    next
      case (Fun g ts)
      let ?g = "(g,length ts)"
      let ?ts = "set (\<sigma> ?g)"
      let ?t = "Fun g ts"
      from Fun have t: "t = ?t" .
      show ?thesis 
      proof (cases s)
        case (Var x)
        show ?thesis
        proof safe
          assume gr: "wpo_s s t"
          with Var Fun show "wpo_s s u" by (auto simp: wpo.simps)
        next
          assume ge: "wpo_ns s t" and gr: "wpo_s t u"
          with Var Fun have pri: "prl ?g" and "\<sigma> ?g = []" by (auto simp: wpo.simps)
          with gr Fun show "wpo_s s u" using wpo_least_2[OF pri, of u] False by auto
        next
          assume ge1: "wpo_ns s t" and ge2: "wpo_ns t u"
          with Var Fun have pri: "prl ?g" and empty: "\<sigma> ?g = []" by (auto simp: wpo.simps)
          from wpo_ns_imp_NS[OF ge1] Var Fun empty have ns: "(Var x, Fun g ts) \<in> NS" by simp
          show "wpo_ns s u"
          proof (rule wpo_least_3[OF pri ge2[unfolded Fun empty] 
                wpo_ns_imp_NS[OF ge1[unfolded Fun empty]] empty _ Var], rule)
            fix v
            assume S: "(Fun g ts, v) \<in> S"
            from SN_imp_minimal[OF SN, rule_format, of undefined UNIV]
            obtain s where "\<And> u. (s,u) \<notin> S" by blast
            with compat_NS_S_point[OF subst_NS[OF ns, of "\<lambda> _. s"] subst_S[OF S, of "\<lambda> _. s"]]
            show False by auto
          qed
        qed
      next
        case (Fun f ss)
        let ?s = "Fun f ss"
        let ?f = "(f,length ss)"
        let ?ss = "set (\<sigma> ?f)"
        from Fun have s: "s = ?s" .
        let ?s1 = "\<exists> i \<in> ?ss. ss ! i \<succeq> t"
        let ?t1 = "\<exists> j \<in> ?ts. ts ! j \<succeq> u"
        let ?ls = "length ss"
        let ?lt = "length ts"
        obtain ps pns where prc: "prc ?f ?g = (ps,pns)" by force
        let ?tran2 = "\<lambda> a b c.  
           ((wpo_ns a b) \<and> (wpo_s b c) \<longrightarrow> (wpo_s a c)) \<and>
           ((wpo_s a b) \<and> (wpo_ns b c) \<longrightarrow> (wpo_s a c)) \<and> 
           ((wpo_ns a b) \<and> (wpo_ns b c) \<longrightarrow> (wpo_ns a c)) \<and> 
           ((wpo_s a b) \<and> (wpo_s b c) \<longrightarrow> (wpo_s a c))"
        from s have "\<forall> s' \<in> set ss. size s' < size s" by (auto simp: size_simps)
        with ind have ind2: "\<And> s' t' u'. \<lbrakk>s' \<in> set ss\<rbrakk> \<Longrightarrow> ?tran s' t' u'" by blast
        with wpo_s_imp_ns have ind3: "\<And> us s' t' u'. \<lbrakk>s' \<in> set ss; t' \<in> set ts\<rbrakk> \<Longrightarrow> ?tran2 s' t' u'" by blast
        let ?mss = "map (\<lambda> i. ss ! i) (\<sigma> ?f)"
        let ?mts = "map (\<lambda> j. ts ! j) (\<sigma> ?g)"
        have ind3': "\<And> us s' t' u'. \<lbrakk>s' \<in> set ?mss; t' \<in> set ?mts\<rbrakk> \<Longrightarrow> ?tran2 s' t' u'" 
          by (rule ind3, auto simp: status_aux)
        {
          assume ge1: "s \<succeq> t" and ge2: "t \<succ> u"
          from wpo_ns_imp_NS[OF ge1] have stA: "(s,t) \<in> NS" .
          from wpo_s_imp_NS[OF ge2] have tuA: "(t,u) \<in> NS" .
          from trans_NS_point[OF stA tuA] have suA: "(s,u) \<in> NS" .
          have "s \<succ> u"
          proof (cases ?s1)
            case True
            from this obtain i where i: "i \<in> ?ss" and ges: "ss ! i \<succeq> t" by auto
            from \<sigma>E[OF i] have s': "ss ! i \<in> set ss" .
            with i s s' ind2[of "ss ! i" t u, simplified] ges ge2 have "ss ! i \<succ> u" by auto
            then have "ss ! i \<succeq> u" by (rule wpo_s_imp_ns)
            with i s suA show ?thesis by (cases u, auto simp: wpo.simps)
          next
            case False
            show ?thesis
            proof (cases ?t1)
              case True
              from this obtain j where j: "j \<in> ?ts" and ges: "ts ! j \<succeq> u" by auto
              from \<sigma>E[OF j] have t': "ts ! j \<in> set ts" by auto
              from j t' t stS False ge1 s have ge1': "s \<succ> ts ! j" unfolding wpo.simps[of s t]
                by (auto split: if_splits prod.splits)        
              from t' s t ge1' ges ind[rule_format, of s "ts ! j" u, simplified] 
              show "s \<succ> u"
                using suA size_simps supt.intros unfolding wpo.simps[of s u] 
                by (auto split: if_splits)
            next
              case False
              from t this ge2 tuS obtain h us where u: "u = Fun h us" 
                by (cases u, auto simp: wpo.simps split: if_splits)
              let ?u = "Fun h us"
              let ?h = "(h,length us)"
              let ?us = "set (\<sigma> ?h)"
              let ?mus = "map (\<lambda> k. us ! k) (\<sigma> ?h)"
              from s t u ge1 ge2 have ge1: "?s \<succeq> ?t" and ge2: "?t \<succ> ?u" by auto
              from stA stS s t have stAS: "((?s,?t) \<in> S) = False" "((?s,?t) \<in> NS) = True" by auto
              from tuA tuS t u have tuAS: "((?t,?u) \<in> S) = False" "((?t,?u) \<in> NS) = True" by auto
              note ge1 = ge1[unfolded wpo.simps[of ?s ?t] stAS, simplified]
              note ge2 = ge2[unfolded wpo.simps[of ?t ?u] tuAS, simplified]              
              obtain ps2 pns2 where prc2: "prc ?g ?h = (ps2,pns2)" by force
              obtain ps3 pns3 where prc3: "prc ?f ?h = (ps3,pns3)" by force
              from \<open>\<not> ?s1\<close> t ge1 have st': "\<forall> j \<in> ?ts. ?s \<succ> ts ! j" by (auto split: if_splits prod.splits)
              from \<open>\<not> ?t1\<close> t u ge2 tuS have tu': "\<forall> k \<in> ?us. ?t \<succ> us ! k" by (auto split: if_splits prod.splits)
              from \<open>\<not> ?s1\<close> s t ge1 stS st' have fg: "pns" by (cases ?thesis, auto simp: prc) 
              from \<open>\<not> ?t1\<close> u ge2 tu' have gh: "pns2" by (cases ?thesis, auto simp: prc2)
              from \<open>\<not> ?s1\<close> have "?s1 = False" by simp
              note ge1 = ge1[unfolded this[unfolded t] if_False term.simps prc split]
              from \<open>\<not> ?t1\<close> have "?t1 = False" by simp
              note ge2 = ge2[unfolded this[unfolded u] if_False term.simps prc2 split]
              note compat = prc_compat[OF prc prc2 prc3]
              from fg gh compat have fh: "pns3" by simp 
              {
                fix k
                assume k: "k \<in> ?us"
                from \<sigma>E[OF this] have "size (us ! k) < size u" unfolding u using size_simps by auto
                with tu'[folded t] \<open>s \<succeq> t\<close> 
                  ind[rule_format, of s t "us ! k"] k have "s \<succ> us ! k" by blast
              } note su' = this
              show ?thesis
              proof (cases ps3)
                case True
                with su' s u fh prc3 suA show ?thesis by (auto simp: wpo.simps)
              next
                case False
                from False fg gh compat have nfg: "\<not> ps" and ngh: "\<not> ps2" and *: "ps = False" "ps2 = False" by blast+
                note ge1 = ge1[unfolded * if_False]
                note ge2 = ge2[unfolded * if_False]
                show ?thesis
                proof (cases "c ?f")
                  case Mul note cf = this
                  show ?thesis
                  proof (cases "c ?g")
                    case Mul note cg = this
                    show ?thesis
                    proof (cases "c ?h")
                      case Mul note ch = this
                      from ge1[unfolded cf cg]
                      have mul1: "snd (mul_ext wpo ?mss ?mts)" by (auto split: if_splits)
                      from ge2[unfolded cg ch]
                      have mul2: "fst (mul_ext wpo ?mts ?mus)" by (auto split: if_splits)
                      from mul1 mul2 mul_ext_compat[OF ind3', of ?mss ?mts ?mus]
                      have "fst (mul_ext wpo ?mss ?mus)"  by auto
                      with s u fh su' prc3 cf ch suA show ?thesis unfolding wpo.simps[of s u] by simp
                    next
                      case Lex note ch = this
                      from gh u ge2 tu' prc2 ngh cg ch have us_e: "?mus = []" by simp
                      from gh u ge2 tu' prc2 ngh cg ch have ts_ne: "?mts \<noteq> []" by (auto split: if_splits)
                      from ns_mul_ext_bottom_uniqueness[of "mset ?mts"]
                      have "\<And>f. snd (mul_ext f [] ?mts) \<Longrightarrow> ?mts = []" unfolding mul_ext_def by (simp add: Let_def)
                      with ts_ne fg \<open>\<not> ?s1\<close> t ge1 st' prc nfg cf cg have ss_ne: "?mss \<noteq> []"
                        by (cases ss) auto
                      from us_e ss_ne s u fh su' prc3 cf cg ch suA show ?thesis unfolding wpo.simps[of s u] by simp
                    qed
                  next
                    case Lex note cg = this
                    from fg \<open>\<not> ?s1\<close> t ge1 st' prc nfg cf cg have ts_e: "?mts = []" by simp
                    with gh \<open>\<not> ?t1\<close> u ge2 tu' prc2 ngh cg show ?thesis
                      by (cases "c ?h") (simp_all add: lex_ext_least_2)
                  qed
                next
                  case Lex note cf = this 
                  show ?thesis
                  proof (cases "c ?g")
                    case Mul note cg = this
                    from fg \<open>\<not> ?s1\<close> t ge1 st' prc nfg cf cg have ts_e: "?mts = []" by simp
                    with gh \<open>\<not> ?t1\<close> u ge2 tu' prc2 ngh cg show ?thesis
                      by (cases "c ?h") (auto simp: Let_def s_mul_ext_def s_mul_ext_bottom mul_ext_def elim: mult2_alt_sE)
                  next
                    case Lex note cg = this
                    show ?thesis
                    proof (cases "c ?h")
                      case Mul note ch = this
                      from gh u ge2 tu' ngh cg ch have us_e: "?mus = []" by simp
                      from gh u ge2 tu' ngh cg ch have ts_ne: "?mts \<noteq> []" by simp
                      from lex_ext_iff[of _ _ "[]" ?mts]
                      have "\<And>f. snd (lex_ext f n [] ?mts) \<Longrightarrow> ?mts = []" by simp
                      with ts_ne fg t ge1 st' nfg cf cg have ss_ne: "?mss \<noteq> []" by auto
                      from us_e ss_ne s u fh su' prc3 cf cg ch suA show ?thesis unfolding wpo.simps[of s u] by simp
                    next
                      case Lex note ch = this
                      from fg t ge1 st' nfg cf cg
                      have lex1: "snd (lex_ext wpo n ?mss ?mts)" by auto
                      from gh u ge2 tu' ngh cg ch
                      have lex2: "fst (lex_ext wpo n ?mts ?mus)" by auto
                      from lex1 lex2 lex_ext_compat[OF ind3', of ?mss ?mts ?mus]
                      have "fst (lex_ext wpo n ?mss ?mus)" by auto
                      with s u fh su' prc3 cf cg ch suA show ?thesis unfolding wpo.simps[of s u] by simp
                    qed
                  qed
                qed
              qed
            qed
          qed
        }
        moreover
        {
          assume ge1: "s \<succ> t" and ge2: "t \<succeq> u"
          from wpo_s_imp_NS[OF ge1] have stA: "(s,t) \<in> NS" .
          from wpo_ns_imp_NS[OF ge2] have tuA: "(t,u) \<in> NS" .
          from trans_NS_point[OF stA tuA] have suA: "(s,u) \<in> NS" .
          have "s \<succ> u"
          proof (cases ?s1)
            case True
            from True obtain i where i: "i \<in> ?ss" and ges: "ss ! i \<succeq> t" by auto
            from \<sigma>E[OF i] have s': "ss ! i \<in> set ss" by auto
            with s s' ind2[of "ss ! i" t u, simplified] ges ge2 have "ss ! i \<succeq> u" by auto
            with i s' s suA show ?thesis by (cases u, auto simp: wpo.simps)
          next
            case False
            show ?thesis
            proof (cases ?t1)
              case True
              from this obtain j where j: "j \<in> ?ts" and ges: "ts ! j \<succeq> u" by auto
              from \<sigma>E[OF j] have t': "ts ! j \<in> set ts" .
              from j t' t stS False ge1 s have ge1': "s \<succ> ts ! j" unfolding wpo.simps[of s t]
                by (auto split: if_splits prod.splits)        
              from t' s t ge1' ges ind[rule_format, of s "ts ! j" u, simplified] 
              show "s \<succ> u"
                using suA size_simps supt.intros unfolding wpo.simps[of s u] 
                by (auto split: if_splits)
            next
              case False
              show ?thesis
              proof (cases u)
                case u: (Fun h us)
                let ?u = "Fun h us"
                let ?h = "(h,length us)"
                let ?us = "set (\<sigma> ?h)"
                let ?mss = "map (\<lambda> i. ss ! i) (\<sigma> ?f)"
                let ?mts = "map (\<lambda> j. ts ! j) (\<sigma> ?g)"
                let ?mus = "map (\<lambda> k. us ! k) (\<sigma> ?h)"
                note \<sigma>E =  \<sigma>E[of _ f ss] \<sigma>E[of _ g ts] \<sigma>E[of _ h us]
                from s t u ge1 ge2 have ge1: "?s \<succ> ?t" and ge2: "?t \<succeq> ?u" by auto
                from stA stS s t have stAS: "((?s,?t) \<in> S) = False" "((?s,?t) \<in> NS) = True" by auto
                from tuA tuS t u have tuAS: "((?t,?u) \<in> S) = False" "((?t,?u) \<in> NS) = True" by auto
                note ge1 = ge1[unfolded wpo.simps[of ?s ?t] stAS, simplified]
                note ge2 = ge2[unfolded wpo.simps[of ?t ?u] tuAS, simplified]
                let ?lu = "length us"
                obtain ps2 pns2 where prc2: "prc ?g ?h = (ps2,pns2)" by force
                obtain ps3 pns3 where prc3: "prc ?f ?h = (ps3,pns3)" by force
                from \<open>\<not> ?s1\<close> t ge1 have st': "\<forall> j \<in> ?ts. ?s \<succ> ts ! j" by (auto split: if_splits prod.splits)
                from \<open>\<not> ?t1\<close> t u ge2 tuS have tu': "\<forall> k \<in> ?us. ?t \<succ> us ! k" by (auto split: if_splits prod.splits)
                from \<open>\<not> ?s1\<close> s t ge1 stS st' have fg: "pns" by (cases ?thesis, auto simp: prc) 
                from \<open>\<not> ?t1\<close> u ge2 tu' have gh: "pns2" by (cases ?thesis, auto simp: prc2)
                from \<open>\<not> ?s1\<close> have "?s1 = False" by simp
                note ge1 = ge1[unfolded this[unfolded t] if_False term.simps prc split]
                from \<open>\<not> ?t1\<close> have "?t1 = False" by simp
                note ge2 = ge2[unfolded this[unfolded u] if_False term.simps prc2 split]
                note compat = prc_compat[OF prc prc2 prc3]
                from fg gh compat have fh: "pns3" by simp 
                {
                  fix k
                  assume k: "k \<in> ?us"
                  from \<sigma>E(3)[OF this] have "size (us ! k) < size u" unfolding u using size_simps by auto
                  with tu'[folded t] wpo_s_imp_ns[OF \<open>s \<succ> t\<close>] 
                    ind[rule_format, of s t "us ! k"] k have "s \<succ> us ! k" by blast
                } note su' = this
                show ?thesis
                proof (cases ps3)
                  case True
                  with su' s u fh prc3 suA show ?thesis by (auto simp: wpo.simps)
                next
                  case False
                  from False fg gh compat have nfg: "\<not> ps" and ngh: "\<not> ps2" and *: "ps = False" "ps2 = False" by blast+
                  note ge1 = ge1[unfolded * if_False]
                  note ge2 = ge2[unfolded * if_False]
                  show ?thesis
                  proof (cases "c ?f")
                    case Mul note cf = this
                    show ?thesis
                    proof (cases "c ?g")
                      case Mul note cg = this
                      show ?thesis
                      proof (cases "c ?h")
                        case Mul note ch = this
                        from fg t ge1 st' nfg cf cg
                        have mul1: "fst (mul_ext wpo ?mss ?mts)" by auto
                        from gh u ge2 tu' ngh cg ch
                        have mul2: "snd (mul_ext wpo ?mts ?mus)" by auto
                        from mul1 mul2 mul_ext_compat[OF ind3', of ?mss ?mts ?mus]
                        have "fst (mul_ext wpo ?mss ?mus)" by auto
                        with s u fh su' prc3 cf ch suA show ?thesis unfolding wpo.simps[of s u] by simp
                      next
                        case Lex note ch = this
                        from gh u ge2 tu' ngh cg ch have us_e: "?mus = []" by simp
                        from fg t ge1 st' nfg cf cg s_mul_ext_bottom_strict
                        have ss_ne: "?mss \<noteq> []" by (cases ?mss) (auto simp: Let_def mul_ext_def)
                        from us_e ss_ne s u fh su' prc3 cf cg ch suA show ?thesis unfolding wpo.simps[of s u] by simp
                      qed
                    next
                      case Lex note cg = this
                      from fg t ge1 st' prc nfg cf cg s_mul_ext_bottom_strict
                      have ss_ne: "?mss \<noteq> []" by (auto simp: mul_ext_def)
                      from fg t ge1 st' nfg cf cg have ts_e: "?mts = []" by simp
                      show ?thesis
                      proof (cases "c ?h")
                        case Mul note ch = this
                        with gh u ge2 tu' ngh cg ch ns_mul_ext_bottom_uniqueness
                        have "?mus = []" by simp
                        with ss_ne s u fh su' prc3 cf cg ch s_mul_ext_bottom suA
                        show ?thesis unfolding wpo.simps[of s u] by (simp add: Let_def mul_ext_def s_mul_ext_def mult2_alt_s_def)
                      next
                        case Lex note ch = this
                        from lex_ext_iff[of _ _ "[]" ?mus]
                        have "\<And>f. snd (lex_ext f n [] ?mus) \<Longrightarrow> ?mus = []" by simp
                        with ts_e gh u ge2 tu' ngh cg ch
                        have "?mus = []" by simp
                        with ss_ne s u fh su' prc3 cf cg ch s_mul_ext_bottom suA
                        show ?thesis unfolding wpo.simps[of s u] by (simp add: mul_ext_def)
                      qed
                    qed
                  next
                    case Lex note cf = this
                    show ?thesis
                    proof (cases "c ?g")
                      case Mul note cg = this
                      from fg t ge1 st' nfg cf cg have ss_ne: "?mss \<noteq> []" by simp
                      from fg t ge1 st' nfg cf cg have ts_e: "?mts = []" by simp
                      show ?thesis
                      proof (cases "c ?h")
                        case Mul note ch = this
                        from ts_e gh u ge2 tu' ngh cg ch
                          ns_mul_ext_bottom_uniqueness[of "mset ?mus"]
                        have "?mus = []" by (simp add: mul_ext_def Let_def)
                        with ss_ne s u fh su' prc3 cf cg ch s_mul_ext_bottom suA
                        show ?thesis unfolding wpo.simps[of s u] by (simp add: mul_ext_def)
                      next
                        case Lex note ch = this
                        from gh u ge2 tu' prc2 ngh cg ch have "?mus = []" by simp
                        with ss_ne s u fh su' prc3 cf cg ch suA
                        show ?thesis unfolding wpo.simps[of s u] by (simp add: lex_ext_iff) 
                      qed
                    next
                      case Lex note cg = this
                      show ?thesis
                      proof (cases "c ?h")
                        case Mul note ch = this
                        from gh u ge2 tu' ngh cg ch have us_e: "?mus = []" by simp
                        have "\<And>f. fst (lex_ext f n ?mss ?mts) \<Longrightarrow> ?mss \<noteq> []"
                          by (cases ?mss) (simp_all add: lex_ext_iff)
                        with fg t ge1 st' prc nfg cf cg have ss_ne: "?mss \<noteq> []" by simp
                        with us_e s u fh su' prc3 cf cg ch suA show ?thesis unfolding wpo.simps[of s u] by simp
                      next
                        case Lex note ch = this
                        from fg t ge1 st' nfg cf cg
                        have lex1: "fst (lex_ext wpo n ?mss ?mts)" by auto
                        from gh u ge2 tu' ngh cg ch
                        have lex2: "snd (lex_ext wpo n ?mts ?mus)" by auto
                        from lex1 lex2 lex_ext_compat[OF ind3', of ?mss ?mts ?mus]
                        have "fst (lex_ext wpo n ?mss ?mus)" by auto
                        with s u fh su' prc3 cf cg ch suA show ?thesis unfolding wpo.simps[of s u] by simp
                      qed
                    qed
                  qed
                qed              
              next
                case (Var z)
                from ge2 \<open>\<not> ?t1\<close> tuS have "ssimple" "large ?g" unfolding Var t
                  by (auto simp: wpo.simps split: if_splits)    
                from large[OF this, of ?f]
                have large: "fst (prc ?g ?f) \<or> snd (prc ?g ?f) \<and> \<sigma> ?f = []" by auto
                obtain fgs fgns where prc_fg: "prc ?f ?g = (fgs,fgns)" by (cases "prc ?f ?g", auto) 
                from ge1 \<open>\<not> ?s1\<close> stS have weak_fg: "snd (prc ?f ?g)" unfolding s t using prc_fg
                  by (auto simp: wpo.simps split: if_splits)
                from refl_not_SN[of ?f] prc_SN have prc_irrefl: "\<not> fst (prc ?f ?f)" by auto
                from large have False
                proof
                  assume "fst (prc ?g ?f)" 
                  with weak_fg have "fst (prc ?f ?f)" by (metis prc_compat prod.collapse)
                  with prc_irrefl show False by auto
                next
                  assume weak: "snd (prc ?g ?f) \<and> \<sigma> ?f = []" 
                  let ?mss = "map (\<lambda> i. ss ! i) (\<sigma> ?f)"
                  let ?mts = "map (\<lambda> j. ts ! j) (\<sigma> ?g)"
                  {
                    assume "fst (prc ?f ?g)" 
                    with weak have "fst (prc ?f ?f)" by (metis prc_compat prod.collapse)
                    with prc_irrefl have False by auto
                  }
                  hence "\<not> fst (prc ?f ?g)" by auto
                  with ge1 \<open>\<not> ?s1\<close> stS prc_fg 
                  have "fst (lex_ext wpo n ?mss ?mts) \<or> fst (mul_ext wpo ?mss ?mts) \<or> ?mss \<noteq> []" 
                    unfolding wpo.simps[of s t] unfolding s t 
                    by (auto simp: Let_def split: if_splits)
                  with weak have "fst (lex_ext wpo n [] ?mts) \<or> fst (mul_ext wpo [] ?mts)" by auto
                  thus False using lex_ext_least_2 by (auto simp: mul_ext_def Let_def s_mul_ext_bottom_strict) 
                qed
                thus ?thesis ..
              qed
            qed
          qed
        }
        moreover
        {
          assume ge1: "s \<succeq> t" and ge2: "t \<succeq> u" and ngt1: "\<not> s \<succ> t" and ngt2: "\<not> t \<succ> u"
          from wpo_ns_imp_NS[OF ge1] have stA: "(s,t) \<in> NS" .
          from wpo_ns_imp_NS[OF ge2] have tuA: "(t,u) \<in> NS" .
          from trans_NS_point[OF stA tuA] have suA: "(s,u) \<in> NS" .
          from ngt1 stA have "\<not> ?s1" unfolding s t by (auto simp: wpo.simps split: if_splits)
          from ngt2 tuA have "\<not> ?t1" unfolding t by (cases u, auto simp: wpo.simps split: if_splits)
          have "s \<succeq> u"
          proof (cases u)
            case u: (Var x)
            from t \<open>\<not> ?t1\<close> ge2 tuA ngt2 have large: "ssimple" "large ?g" unfolding u
              by (auto simp: wpo.simps split: if_splits)
            from s t ngt1 ge1 have "snd (prc ?f ?g)" 
              by (auto simp: wpo.simps split: if_splits prod.splits)
            from large_trans[OF large this] suA large
            show ?thesis unfolding wpo.simps[of s u] using s u by auto
          next
            case u: (Fun h us)
            let ?u = "Fun h us"	 
            let ?h = "(h,length us)"
            let ?us = "set (\<sigma> ?h)"
            let ?mss = "map (\<lambda> i. ss ! i) (\<sigma> ?f)"
            let ?mts = "map (\<lambda> j. ts ! j) (\<sigma> ?g)"
            let ?mus = "map (\<lambda> k. us ! k) (\<sigma> ?h)"   
            from s t u ge1 ge2 have ge1: "?s \<succeq> ?t" and ge2: "?t \<succeq> ?u" by auto
            from stA stS s t have stAS: "((?s,?t) \<in> S) = False" "((?s,?t) \<in> NS) = True" by auto
            from tuA tuS t u have tuAS: "((?t,?u) \<in> S) = False" "((?t,?u) \<in> NS) = True" by auto
            note ge1 = ge1[unfolded wpo.simps[of ?s ?t] stAS, simplified]
            note ge2 = ge2[unfolded wpo.simps[of ?t ?u] tuAS, simplified]
            from s t u ngt1 ngt2 have ngt1: "\<not> ?s \<succ> ?t" and ngt2: "\<not> ?t \<succ> ?u" by auto
            note ngt1 = ngt1[unfolded wpo.simps[of ?s ?t] stAS, simplified]
            note ngt2 = ngt2[unfolded wpo.simps[of ?t ?u] tuAS, simplified]
            from \<open>\<not> ?s1\<close> t ge1 have st': "\<forall> j \<in> ?ts. ?s \<succ> ts ! j" by (cases ?thesis, auto)
            from \<open>\<not> ?t1\<close> u ge2 have tu': "\<forall> k \<in> ?us. ?t \<succ> us ! k" by (cases ?thesis, auto)
            let ?lu = "length us"        
            obtain ps2 pns2 where prc2: "prc ?g ?h = (ps2,pns2)" by force
            obtain ps3 pns3 where prc3: "prc ?f ?h = (ps3,pns3)" by force
            from \<open>\<not> ?s1\<close> t ge1 st' have fg: "pns" by (cases ?thesis, auto simp: prc) 
            from \<open>\<not> ?t1\<close> u ge2 tu' have gh: "pns2" by (cases ?thesis, auto simp: prc2)
            note compat = prc_compat[OF prc prc2 prc3]
            from \<open>\<not> ?s1\<close> have "?s1 = False" by simp
            note ge1 = ge1[unfolded this[unfolded t] if_False term.simps prc split]
            from \<open>\<not> ?t1\<close> have "?t1 = False" by simp
            note ge2 = ge2[unfolded this[unfolded u] if_False term.simps prc2 split]
            from compat fg gh have fh: pns3 by blast
            {
              fix k
              assume k: "k \<in> ?us"
              from \<sigma>E[OF this] have "size (us ! k) < size u" unfolding u using size_simps by auto
              with tu'[folded t] \<open>s \<succeq> t\<close>
                ind[rule_format, of s t "us ! k"] k have "s \<succ> us ! k" by blast
            } note su' = this
            from \<open>\<not> ?s1\<close> st' ge1 ngt1 s t have nfg: "\<not> ps"
              by (simp, cases ?thesis, simp, cases ps, auto simp: prc fg) 
            from \<open>\<not> ?t1\<close> tu' ge2 ngt2 t u have ngh: "\<not> ps2"
              by (simp, cases ?thesis, simp, cases ps2, auto simp: prc2 gh)
            show "s \<succeq> u"
            proof (cases "c ?f")
              case Mul note cf = this
              show ?thesis
              proof (cases "c ?g")
                case Mul note cg = this
                show ?thesis
                proof (cases "c ?h")
                  case Mul note ch = this
                  from fg t ge1 st' nfg cf cg
                  have mul1: "snd (mul_ext wpo ?mss ?mts)" by auto
                  from gh u ge2 tu' ngh cg ch
                  have mul2: "snd (mul_ext wpo ?mts ?mus)" by auto
                  from mul1 mul2 mul_ext_compat[OF ind3', of ?mss ?mts ?mus]
                  have "snd (mul_ext wpo ?mss ?mus)" by auto
                  with s u fh su' prc3 cf ch suA show ?thesis unfolding wpo.simps[of s u] by simp
                next
                  case Lex note ch = this
                  from gh u ge2 tu' ngh cg ch have us_e: "?mus = []" by simp
                  with s u fh su' prc3 cf cg ch suA show ?thesis unfolding wpo.simps[of s u] by simp
                qed
              next
                case Lex note cg = this
                from fg t ge1 st' nfg cf cg have ts_e: "?mts = []" by simp
                show ?thesis
                proof (cases "c ?h")
                  case Mul note ch = this
                  with gh u ge2 tu' ngh cg ch have "?mus = []" by simp
                  with s u fh su' prc3 cf cg ch ns_mul_ext_bottom suA
                  show ?thesis unfolding wpo.simps[of s u] by (simp add: ns_mul_ext_def mul_ext_def Let_def mult2_alt_ns_def)
                next
                  case Lex note ch = this
                  have "\<And>f. snd (lex_ext f n [] ?mus) \<Longrightarrow> ?mus = []" by (simp_all add: lex_ext_iff)
                  with ts_e gh u ge2 tu' ngh cg ch have "?mus = []" by simp
                  with s u fh su' prc3 cf cg ch suA show ?thesis unfolding wpo.simps[of s u] by simp
                qed
              qed
            next
              case Lex note cf = this
              show ?thesis
              proof (cases "c ?g")
                case Mul note cg = this
                from fg t ge1 st' prc nfg cf cg have ts_e: "?mts = []" by simp
                show ?thesis
                proof (cases "c ?h")
                  case Mul note ch = this
                  with ts_e gh u ge2 tu' ngh cg ch
                    ns_mul_ext_bottom_uniqueness[of "mset ?mus"]
                  have "?mus = []" by (simp add: Let_def mul_ext_def)
                  with s u fh su' prc3 cf cg ch suA show ?thesis unfolding wpo.simps[of s u] by simp
                next
                  case Lex note ch = this
                  with gh u ge2 tu' prc2 ngh cg ch have "?mus = []" by simp
                  with s u fh su' prc3 cf cg ch suA show ?thesis unfolding wpo.simps[of s u] by (simp add: lex_ext_least_1)
                qed
              next
                case Lex note cg = this
                show ?thesis
                proof (cases "c ?h")
                  case Mul note ch = this
                  with gh u ge2 tu' ngh cg ch have "?mus = []" by simp
                  with s u fh su' prc3 cf cg ch suA show ?thesis unfolding wpo.simps[of s u] by (simp add: lex_ext_least_1)
                next
                  case Lex note ch = this
                  from st' ge1 s t fg nfg cf cg
                  have lex1: "snd (lex_ext wpo n ?mss ?mts)" by (auto simp: prc)
                  from tu' ge2 t u gh ngh cg ch
                  have lex2: "snd (lex_ext wpo n ?mts ?mus)" by (auto simp: prc2)
                  from lex1 lex2 lex_ext_compat[OF ind3', of ?mss ?mts ?mus]
                  have "snd (lex_ext wpo n ?mss ?mus)" by auto
                  with fg gh su' s u fh cf cg ch suA show ?thesis unfolding wpo.simps[of s u] by (auto simp: prc3)
                qed
              qed
            qed
          qed
        }
        ultimately
        show ?thesis using wpo_s_imp_ns by auto
      qed
    qed
  qed
qed

lemma subterm_wpo_s_arg: assumes i: "i \<in> set (\<sigma> (f,length ss))"
  shows "Fun f ss \<succ> ss ! i"
proof -
  have refl: "ss ! i \<succeq> ss ! i" by (rule wpo_ns_refl)
  with i have "\<exists> t \<in> set (\<sigma> (f,length ss)). ss ! i \<succeq> ss ! i" by auto
  with NS_arg[OF i] i
  show ?thesis by (auto simp: wpo.simps)
qed

lemma subterm_wpo_ns_arg: assumes i: "i \<in> set (\<sigma> (f,length ss))"
  shows "Fun f ss \<succeq> ss ! i"
  by (rule wpo_s_imp_ns[OF subterm_wpo_s_arg[OF i]])

lemma wpo_ns_pre_mono: fixes f and bef aft :: "('f,'v)term list"
  defines "\<sigma>f \<equiv> \<sigma> (f, Suc (length bef + length aft))"
  assumes rel: "(wpo_ns s t)"
  shows "(\<forall>j\<in>set \<sigma>f. Fun f (bef @ s # aft) \<succ> (bef @ t # aft) ! j)
    \<and> (Fun f (bef @ s # aft), (Fun f (bef @ t # aft))) \<in> NS
    \<and> (\<forall> i < length \<sigma>f. ((map ((!) (bef @ s # aft)) \<sigma>f) ! i) \<succeq> ((map ((!) (bef @ t # aft)) \<sigma>f) ! i))"
    (is "_ \<and> _ \<and> ?three")
proof -
  let ?ss = "bef @ s # aft"
  let ?ts = "bef @ t # aft"
  let ?s = "Fun f ?ss"
  let ?t = "Fun f ?ts"
  let ?len = "Suc (length bef + length aft)"
  let ?f = "(f, ?len)"
  let ?\<sigma> = "\<sigma> ?f"
  from wpo_ns_imp_NS[OF rel] have stA: "(s,t) \<in> NS" .
  have ?three unfolding \<sigma>f_def
  proof (intro allI impI)
    fix i
    assume "i < length ?\<sigma>"
    then have id: "\<And> ss. (map ((!) ss) ?\<sigma>) ! i = ss ! (?\<sigma> ! i)" by auto
    show "wpo_ns ((map ((!) ?ss) ?\<sigma>) ! i) ((map ((!) ?ts) ?\<sigma>) ! i)"
    proof (cases "?\<sigma> ! i = length bef")
      case True
      then show ?thesis unfolding id using rel by auto
    next
      case False
      from append_Cons_nth_not_middle[OF this, of s aft t] wpo_ns_refl 
      show ?thesis unfolding id by auto
    qed
  qed
  have "\<forall>j\<in>set ?\<sigma>. wpo_s ?s ((bef @ t # aft) ! j)" (is ?one)
  proof
    fix j
    assume j: "j \<in> set ?\<sigma>"
    then have "j \<in> set (\<sigma> (f,length ?ss))" by simp
    from subterm_wpo_s_arg[OF this]
    have s: "wpo_s ?s (?ss ! j)" .
    show "wpo_s ?s (?ts ! j)"
    proof (cases "j = length bef")
      case False
      then have "?ss ! j = ?ts ! j" by (rule append_Cons_nth_not_middle)
      with s show ?thesis by simp
    next
      case True
      with s have "wpo_s ?s s" by simp
      with rel wpo_compat have "wpo_s ?s t" by blast
      with True show ?thesis by simp
    qed
  qed
  with \<open>?three\<close> ctxt_NS[OF stA] show ?thesis unfolding \<sigma>f_def by auto
qed

lemma wpo_ns_mono:
  assumes rel: "s \<succeq> t"
  shows "Fun f (bef @ s # aft) \<succeq> Fun f (bef @ t # aft)"
proof - 
  let ?ss = "bef @ s # aft"
  let ?ts = "bef @ t # aft"
  let ?s = "Fun f ?ss"
  let ?t = "Fun f ?ts"  
  let ?len = "Suc (length bef + length aft)"
  let ?f = "(f, ?len)"
  let ?\<sigma> = "\<sigma> ?f"
  from wpo_ns_pre_mono[OF rel]
  have id: "(\<forall>j\<in>set ?\<sigma>. wpo_s ?s ((bef @ t # aft) ! j)) = True" 
    "((?s,?t) \<in> NS) = True" 
    "length ?ss = ?len" "length ?ts = ?len"
    by auto 
  have "snd (lex_ext wpo n (map ((!) ?ss) ?\<sigma>) (map ((!) ?ts) ?\<sigma>))"
    by (rule all_nstri_imp_lex_nstri, intro allI impI, insert wpo_ns_pre_mono[OF rel], auto)
  moreover have "snd (mul_ext wpo (map ((!) ?ss) ?\<sigma>) (map ((!) ?ts) ?\<sigma>))"
    by (rule all_nstri_imp_mul_nstri, intro allI impI, insert wpo_ns_pre_mono[OF rel], auto)
  ultimately show ?thesis unfolding wpo.simps[of ?s ?t] term.simps id prc_refl
    using order_tag.exhaust by (auto simp: Let_def)
qed

lemma wpo_stable: fixes \<delta> :: "('f,'v)subst"
  shows "(s \<succ> t \<longrightarrow> s \<cdot> \<delta> \<succ> t \<cdot> \<delta>) \<and> (s \<succeq> t \<longrightarrow> s \<cdot> \<delta> \<succeq> t \<cdot> \<delta>)"
    (is "?p s t")
proof (induct "(s,t)" arbitrary:s t rule: wf_induct[OF wf_measure[of "\<lambda> (s,t). size s + size t"]])
  case (1 s t)
  from 1
  have "\<forall> s' t'. size s' + size t' < size s + size t \<longrightarrow> ?p s' t'" by auto
  note IH = this[rule_format]
  let ?s = "s \<cdot> \<delta>"
  let ?t = "t \<cdot> \<delta>"
  note simps = wpo.simps[of s t] wpo.simps[of ?s ?t]
  show "?case"
  proof (cases "((s,t) \<in> S \<or> (?s,?t) \<in> S) \<or> ((s,t) \<notin> NS \<or> \<not> wpo_ns s t)")
    case True
    then show ?thesis
    proof
      assume "(s,t) \<in> S \<or> (?s,?t) \<in> S"
      with subst_S[of s t \<delta>] have "(?s,?t) \<in> S" by blast
      from S_imp_wpo_s[OF this] have "wpo_s ?s ?t" .
      with wpo_s_imp_ns[OF this] show ?thesis by blast
    next
      assume "(s,t) \<notin> NS \<or> \<not> wpo_ns s t"
      with wpo_ns_imp_NS have st: "\<not> wpo_ns s t" by auto
      with wpo_s_imp_ns have "\<not> wpo_s s t" by auto
      with st show ?thesis by blast
    qed
  next
    case False
    then have not: "((s,t) \<in> S) = False" "((?s,?t) \<in> S) = False" 
      and stA: "(s,t) \<in> NS" and ns: "wpo_ns s t" by auto
    from subst_NS[OF stA] have sstsA: "(?s,?t) \<in> NS" by auto
    from stA sstsA have id: "((s,t) \<in> NS) = True" "((?s,?t) \<in> NS) = True" by auto
    note simps = simps[unfolded id not if_False if_True]
    show ?thesis
    proof (cases s)
      case (Var x) note s = this
      show ?thesis
      proof (cases t)
        case (Var y) note t = this
        show ?thesis unfolding simps(1) unfolding s t using wpo_ns_refl[of "\<delta> y"] by auto
      next
        case (Fun g ts) note t = this
        let ?g = "(g,length ts)"
        show ?thesis
        proof (cases "\<delta> x")
          case (Var y)
          then show ?thesis unfolding simps unfolding s t by simp
        next
          case (Fun f ss)
          let ?f = "(f, length ss)"
          show ?thesis 
          proof (cases "prl ?g")
            case False then show ?thesis unfolding simps unfolding s t Fun by auto
          next
            case True
            obtain s ns where "prc ?f ?g = (s,ns)" by force
            with prl[OF True, of ?f] have prc: "prc ?f ?g = (s, True)" by auto
            show ?thesis unfolding simps unfolding s t Fun 
              by (auto simp: Fun prc mul_ext_def ns_mul_ext_bottom Let_def intro!: all_nstri_imp_lex_nstri[of "[]", simplified])
          qed
        qed
      qed
    next
      case (Fun f ss) note s = this
      let ?f = "(f,length ss)"
      let ?ss = "set (\<sigma> ?f)"
      {
        fix i
        assume i: "i \<in> ?ss" and ns: "wpo_ns (ss ! i) t"
        from IH[of "ss ! i" t] \<sigma>E[OF i] ns have "wpo_ns (ss ! i \<cdot> \<delta>) ?t" using s
          by (auto simp: size_simps)
        then have "wpo_s ?s ?t" using i sstsA \<sigma>[of f "length ss"] unfolding simps unfolding s by force
        with wpo_s_imp_ns[OF this] have ?thesis by blast
      } note si_arg = this        
      show ?thesis
      proof (cases t)
        case t: (Var y) 
        show ?thesis
        proof (cases "\<exists>i\<in>?ss. wpo_ns (ss ! i) t")
          case True
          then obtain i
            where si: "i \<in> ?ss" and ns: "wpo_ns (ss ! i) t" 
            unfolding s t by auto
          from si_arg[OF this] show ?thesis .
        next
          case False
          with ns[unfolded simps] s t
          have ssimple and largef: "large ?f" by (auto split: if_splits)
          from False s t not 
          have "\<not> wpo_s s t" unfolding wpo.simps[of s t] by auto
          moreover          
          have "wpo_ns ?s ?t" 
          proof (cases "\<delta> y")
            case (Var z)
            show ?thesis unfolding wpo.simps[of ?s ?t] not id 
              unfolding s t using Var `ssimple` largef by auto
          next
            case (Fun g ts)
            let ?g = "(g,length ts)" 
            obtain ps pns where prc: "prc ?f ?g = (ps,pns)" by (cases "prc ?f ?g", auto)
            from prc_stri_imp_nstri[of ?f ?g] prc have ps: "ps \<Longrightarrow> pns" by auto
            {
              fix j
              assume "j \<in> set (\<sigma> ?g)"
              with set_status_nth[OF refl this] ss_status[OF `ssimple` this] t Fun
              have "(t \<cdot> \<delta>, ts ! j) \<in> S" by (auto simp: simple_arg_pos_def)
              with sstsA have S: "(s \<cdot> \<delta>, ts ! j) \<in> S" by (metis compat_NS_S_point)
              hence "wpo_s (s \<cdot> \<delta>) (ts ! j)" by (rule S_imp_wpo_s)
            } note ssimple = this
            from large[OF `ssimple` largef, of ?g, unfolded prc]
            have "ps \<or> pns \<and>  \<sigma> ?g = []" by auto 
            thus ?thesis using ssimple unfolding wpo.simps[of ?s ?t] not id 
              unfolding s t using Fun prc ps by (auto simp: lex_ext_least_1 mul_ext_def Let_def ns_mul_ext_bottom)
          qed
          ultimately show ?thesis by blast
        qed
      next
        case (Fun g ts) note t = this
        let ?g = "(g,length ts)"
        let ?ts = "set (\<sigma> ?g)"
        obtain prs prns where p: "prc ?f ?g = (prs, prns)" by force
        note ns = ns[unfolded simps, unfolded s t p term.simps split]
        show ?thesis
        proof (cases "\<exists> i \<in> ?ss. wpo_ns (ss ! i) t")
          case True
          with si_arg show ?thesis by blast
        next
          case False
          then have id: "(\<exists> i \<in> ?ss. wpo_ns (ss ! i) (Fun g ts)) = False" unfolding t by auto
          note ns = ns[unfolded this if_False]
          let ?mss = "map (\<lambda> s . s \<cdot> \<delta>) ss"
          let ?mts = "map (\<lambda> t . t \<cdot> \<delta>) ts"
          from ns have prns and s_tj: "\<And> j. j \<in> ?ts \<Longrightarrow> wpo_s (Fun f ss) (ts ! j)" 
            by (auto split: if_splits)
          {
            fix j
            assume j: "j \<in> ?ts"
            from \<sigma>E[OF this]
            have "size s + size (ts ! j) < size s + size t" unfolding t by (auto simp: size_simps)
            from IH[OF this] s_tj[OF j, folded s] have wpo: "wpo_s ?s (ts ! j \<cdot> \<delta>)" by auto
            from j \<sigma>[of g "length ts"] have "j < length ts" by auto
            with wpo have "wpo_s ?s (?mts ! j)" by auto
          } note ss_ts = this
          note \<sigma>E = \<sigma>E[of _ f ss] \<sigma>E[of _ g ts]
          show ?thesis
          proof (cases prs)
            case True
            with ss_ts sstsA p \<open>prns\<close> have "wpo_s ?s ?t" unfolding simps unfolding s t 
              by (auto split: if_splits)
            with wpo_s_imp_ns[OF this] show ?thesis by blast
          next
            case False
            let ?mmss = "map ((!) ss) (\<sigma> ?f)"
            let ?mmts = "map ((!) ts) (\<sigma> ?g)"
            let ?Mmss = "map ((!) ?mss) (\<sigma> ?f)"
            let ?Mmts = "map ((!) ?mts) (\<sigma> ?g)"
            have id_map: "?Mmss = map (\<lambda> t. t \<cdot> \<delta>) ?mmss" "?Mmts = map (\<lambda> t. t \<cdot> \<delta>) ?mmts"
              unfolding map_map o_def by (auto simp: set_status_nth)
            let ?ls = "length (\<sigma> ?f)"
            let ?lt = "length (\<sigma> ?g)"
            {
              fix si tj
              assume *: "si \<in> set ?mmss" "tj \<in> set ?mmts" 
              have "(wpo_s si tj \<longrightarrow> wpo_s (si \<cdot> \<delta>) (tj \<cdot> \<delta>)) \<and> (wpo_ns si tj \<longrightarrow> wpo_ns (si \<cdot> \<delta>) (tj \<cdot> \<delta>))" 
              proof (intro IH add_strict_mono)
                from *(1) have "si \<in> set ss" using set_status_nth[of _ _ _ \<sigma>\<sigma>] by auto
                then show "size si < size s" unfolding s by (auto simp: termination_simp)
                from *(2) have "tj \<in> set ts" using set_status_nth[of _ _ _ \<sigma>\<sigma>] by auto
                then show "size tj < size t" unfolding t by (auto simp: termination_simp)
              qed
              hence "wpo_s si tj \<Longrightarrow> wpo_s (si \<cdot> \<delta>) (tj \<cdot> \<delta>)"
                "wpo_ns si tj \<Longrightarrow> wpo_ns (si \<cdot> \<delta>) (tj \<cdot> \<delta>)" by blast+
            } note IH' = this
            {
              fix i 
              assume "i < ?ls" "i < ?lt" 
              then have i_f: "i < length (\<sigma> ?f)" and i_g: "i < length (\<sigma> ?g)" by auto
              with \<sigma>[of f "length ss"] \<sigma>[of g "length ts"] have i: "\<sigma> ?f ! i < length ss" "\<sigma> ?g ! i < length ts" 
                unfolding set_conv_nth by auto
              then have "size (ss ! (\<sigma> ?f ! i)) < size s" "size (ts ! (\<sigma> ?g ! i)) < size t" unfolding s t by (auto simp: size_simps)
              then have "size (ss ! (\<sigma> ?f ! i)) + size (ts ! (\<sigma> ?g ! i)) < size s + size t" by simp
              from IH[OF this] i i_f i_g
              have "(wpo_s (?mmss ! i) (?mmts ! i) \<Longrightarrow>
                     wpo_s (?mss ! (\<sigma> ?f ! i)) (?mts ! (\<sigma> ?g ! i)))" 
                "(wpo_ns (?mmss ! i) (?mmts ! i) \<Longrightarrow>
                     wpo_ns (?mss ! (\<sigma> ?f ! i)) (?mts ! (\<sigma> ?g ! i)))" by auto
            } note IH = this
            consider (Lex) "c ?f = Lex" "c ?g = Lex" | (Mul) "c ?f = Mul" "c ?g = Mul" | (Diff) "c ?f \<noteq> c ?g" 
              by (cases "c ?f"; cases "c ?g", auto)
            thus ?thesis
            proof cases
              case Lex
              from Lex False ns have "snd (lex_ext wpo n ?mmss ?mmts)" by (auto split: if_splits)
              from this[unfolded lex_ext_iff snd_conv]
              have len: "(?ls = ?lt \<or> ?lt \<le> n)"
                and choice: "(\<exists>i< ?ls.
               i < ?lt \<and> (\<forall>j<i. wpo_ns (?mmss ! j) (?mmts ! j)) \<and> wpo_s (?mmss ! i) (?mmts ! i)) \<or>
               (\<forall>i< ?lt. wpo_ns (?mmss ! i) (?mmts ! i)) \<and> ?lt \<le> ?ls" (is "?stri \<or> ?nstri") by auto
              from choice have "?stri \<or> (\<not> ?stri \<and> ?nstri)" by blast
              then show ?thesis
              proof
                assume ?stri
                then obtain i where i: "i < ?ls" "i < ?lt"
                  and NS: "(\<forall>j<i. wpo_ns (?mmss ! j) (?mmts ! j))" and S: "wpo_s (?mmss ! i) (?mmts ! i)" by auto
                with IH have "(\<forall>j<i. wpo_ns (?Mmss ! j) (?Mmts ! j))" "wpo_s (?Mmss ! i) (?Mmts ! i)" by auto
                with i len have "fst (lex_ext wpo n ?Mmss ?Mmts)" unfolding lex_ext_iff
                  by auto
                with Lex ss_ts sstsA p \<open>prns\<close> have "wpo_s ?s ?t" unfolding simps unfolding s t 
                  by (auto split: if_splits)
                with wpo_s_imp_ns[OF this] show ?thesis by blast
              next
                assume "\<not> ?stri \<and> ?nstri"
                then have ?nstri and nstri: "\<not> ?stri" by blast+
                with IH have "(\<forall>i< ?lt. wpo_ns (?Mmss ! i) (?Mmts ! i)) \<and> ?lt \<le> ?ls" by auto
                with len have "snd (lex_ext wpo n ?Mmss ?Mmts)" unfolding lex_ext_iff
                  by auto
                with Lex ss_ts sstsA p \<open>prns\<close> have ns: "wpo_ns ?s ?t" unfolding simps unfolding s t 
                  by (auto split: if_splits)
                {
                  assume "wpo_s s t"
                  from Lex this[unfolded simps, unfolded s t term.simps p split id] False
                  have "fst (lex_ext wpo n ?mmss ?mmts)" by (auto split: if_splits)
                  from this[unfolded lex_ext_iff fst_conv] nstri
                  have "(\<forall>i< ?lt. wpo_ns (?mmss ! i) (?mmts ! i)) \<and> ?lt < ?ls" by auto
                  with IH have "(\<forall>i< ?lt. wpo_ns (?Mmss ! i) (?Mmts ! i)) \<and> ?lt < ?ls" by auto
                  then have "fst (lex_ext wpo n ?Mmss ?Mmts)" using len unfolding lex_ext_iff by auto
                  with Lex ss_ts sstsA p \<open>prns\<close> have ns: "wpo_s ?s ?t" unfolding simps unfolding s t 
                    by (auto split: if_splits)
                }
                with ns show ?thesis by blast
              qed
            next
              case Diff
              thus ?thesis using ns ss_ts sstsA p \<open>prns\<close> unfolding simps unfolding s t
                by (auto simp: Let_def split: if_splits)
            next
              case Mul
              from Mul False ns have ge: "snd (mul_ext wpo ?mmss ?mmts)" by (auto split: if_splits)
              have ge: "snd (mul_ext wpo ?Mmss ?Mmts)" unfolding id_map
                by (rule nstri_mul_ext_map[OF _ _ ge], (intro IH', auto)+)
              {
                assume gr: "fst (mul_ext wpo ?mmss ?mmts)" 
                have gr\<sigma>: "fst (mul_ext wpo ?Mmss ?Mmts)" unfolding id_map
                  by (rule stri_mul_ext_map[OF _ _ gr], (intro IH', auto)+)
              } note gr = this
              from ge gr
              show ?thesis 
                using ss_ts \<open>prns\<close> unfolding simps 
                unfolding s t term.simps p split subst_apply_term.simps length_map Mul
                by (simp add: id_map id)
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma WPO_S_SN: "SN WPO_S"
proof - 
  {
    fix t :: "('f,'v)term"
    let ?S = "\<lambda>x. SN_on WPO_S {x}"
    note iff = SN_on_all_reducts_SN_on_conv[of WPO_S]
    {
      fix x
      have "?S (Var x)" unfolding iff[of "Var x"]
      proof (intro allI impI)
        fix s
        assume "(Var x, s) \<in> WPO_S"
        then have False by (cases s, auto simp: wpo.simps)
        then show "?S s" ..
      qed
    } note var_SN = this
    have "?S t"
    proof (induct t)
      case (Var x) show ?case by (rule var_SN)
    next
      case (Fun f ts)
      let ?Slist = "\<lambda> f ys. \<forall> i \<in> set (\<sigma> f). ?S (ys ! i)"
      let ?r3 = "{((f,ab), (g,ab')). ((c f = c g) \<longrightarrow> (?Slist f ab \<and> 
          (c f = Mul \<longrightarrow> fst (mul_ext wpo (map ((!) ab) (\<sigma> f)) (map ((!) ab') (\<sigma> g)))) \<and>
          (c f = Lex \<longrightarrow> fst (lex_ext wpo n (map ((!) ab) (\<sigma> f)) (map ((!) ab') (\<sigma> g))))))
       \<and> ((c f \<noteq> c g) \<longrightarrow> (map ((!) ab) (\<sigma> f) \<noteq> [] \<and> (map ((!) ab') (\<sigma> g)) = []))}"
      let ?r0 = "lex_two {(f,g). fst (prc f g)} {(f,g). snd (prc f g)} ?r3"
      {
        fix ab
        {
          assume "\<exists>S. S 0 = ab \<and> (\<forall>i. (S i, S (Suc i)) \<in> ?r3)"
          then obtain S where
            S0: "S 0 = ab" and
            SS: "\<forall>i. (S i, S (Suc i)) \<in> ?r3"
            by auto
          let ?Sf = "\<lambda>i. fst (fst (S i))"
          let ?Sn = "\<lambda>i. snd (fst (S i))"
          let ?Sfn = "\<lambda> i. fst (S i)"
          let ?Sts = "\<lambda>i. snd (S i)"
          let ?Sts\<sigma> = "\<lambda>i. map ((!) (?Sts i)) (\<sigma> (?Sfn i))"
          have False
          proof (cases "\<forall>i. c (?Sfn i) = Mul")
            case True
            let ?r' = "{((f,ys), (g,xs)).
                (\<forall> yi \<in>set ((map ((!) ys) (\<sigma> f))). SN_on WPO_S {yi})
                \<and> fst (mul_ext wpo (map ((!) ys) (\<sigma> f)) (map ((!) xs) (\<sigma> g)))}"
            {
              fix i
              from True[rule_format, of i] and True[rule_format, of "Suc i"]
                and SS[rule_format, of i]
              have "(S i, S (Suc i)) \<in> ?r'" by auto
            }
            then have Hf: "\<not> SN_on ?r' {S 0}"
              unfolding SN_on_def by auto
            from mul_ext_SN[of wpo, rule_format, OF wpo_ns_refl]
              and wpo_compat wpo_s_imp_ns
            have tmp: "SN {(ys, xs). (\<forall>y\<in>set ys. SN_on {(s, t). wpo_s s t} {y}) \<and> fst (mul_ext wpo ys xs)}" 
              (is "SN ?R") by blast
            have id: "?r' = inv_image ?R (\<lambda> (f,ys). map ((!) ys) (\<sigma> f))" by auto
            from SN_inv_image[OF tmp]
            have "SN ?r'" unfolding id . 
            from SN_on_subset2[OF subset_UNIV[of "{S 0}"], OF this]
            have "SN_on ?r' {(S 0)}" .
            with Hf show ?thesis ..
          next
            case False note HMul = this
            show ?thesis
            proof (cases "\<forall>i. c (?Sfn i) = Lex")
              case True
              let ?r' = "{((f,ys), (g,xs)).
                (\<forall> yi \<in>set ((map ((!) ys) (\<sigma> f))). SN_on WPO_S {yi})
                \<and> fst (lex_ext wpo n (map ((!) ys) (\<sigma> f)) (map ((!) xs) (\<sigma> g)))}"
              {
                fix i
                from SS[rule_format, of i] True[rule_format, of i] True[rule_format, of "Suc i"]
                have "(S i, S (Suc i)) \<in> ?r'" by auto
              }
              then have Hf: "\<not> SN_on ?r' {S 0}"
                unfolding SN_on_def by auto
              from wpo_compat have "\<And> x y z. wpo_ns x y \<Longrightarrow> wpo_s y z \<Longrightarrow> wpo_s x z" by blast
              from lex_ext_SN[of "wpo" n, OF this] 
              have tmp: "SN {(ys, xs). (\<forall>y\<in>set ys. SN_on WPO_S {y}) \<and> fst (lex_ext wpo n ys xs)}" 
                (is "SN ?R") .
              have id: "?r' = inv_image ?R (\<lambda> (f,ys). map ((!) ys) (\<sigma> f))" by auto
              from SN_inv_image[OF tmp]
              have "SN ?r'" unfolding id . 
              then have "SN_on ?r' {(S 0)}" unfolding SN_defs by blast
              with Hf show False .. 
            next
              case False note HLex = this
              from HMul and HLex
              have "\<exists>i. c (?Sfn i) \<noteq> c (?Sfn (Suc i))"
              proof (cases ?thesis, simp)
                case False
                then have T: "\<forall>i. c (?Sfn i) = c (?Sfn (Suc i))" by simp
                {
                  fix i
                  have "c (?Sfn i) = c (?Sfn 0)"
                  proof (induct i)
                    case (Suc j) then show ?case by (simp add: T[rule_format, of j])
                  qed simp
                }
                then show ?thesis using HMul HLex
                  by (cases "c (?Sfn 0)") auto
              qed
              then obtain i where
                Hdiff: "c (?Sfn i) \<noteq> c (?Sfn (Suc i))"
                by auto
              from Hdiff have Hf: "?Sts\<sigma> (Suc i) = []"
                using SS[rule_format, of i] by auto
              show ?thesis
              proof (cases "c (?Sfn (Suc i)) = c (?Sfn (Suc (Suc i)))")
                case False then show ?thesis using Hf and SS[rule_format, of "Suc i"] by auto
              next
                case True
                show ?thesis
                proof (cases "c (?Sfn (Suc i))")
                  case Mul
                  with True and SS[rule_format, of "Suc i"]
                  have "fst (mul_ext wpo (?Sts\<sigma> (Suc i)) (?Sts\<sigma> (Suc (Suc i))))" 
                    by auto
                  with Hf and s_mul_ext_bottom_strict show ?thesis
                    by (simp add: Let_def mul_ext_def s_mul_ext_bottom_strict)
                next
                  case Lex
                  with True and SS[rule_format, of "Suc i"]
                  have "fst (lex_ext wpo n (?Sts\<sigma> (Suc i)) (?Sts\<sigma> (Suc (Suc i))))"
                    by auto
                  with Hf show ?thesis by (simp add: lex_ext_iff)
                qed
              qed
            qed
          qed
        }
      }
      then have "SN ?r3" unfolding SN_on_def by blast
      have SN1:"SN ?r0" 
      proof (rule lex_two[OF _ prc_SN \<open>SN ?r3\<close>])
        let ?r' = "{(f,g). fst (prc f g)}"
        let ?r = "{(f,g). snd (prc f g)}"
        {
          fix a1 a2 a3
          assume "(a1,a2) \<in> ?r" "(a2,a3) \<in> ?r'"
          then have "(a1,a3) \<in> ?r'"
            by (cases "prc a1 a2", cases "prc a2 a3", cases "prc a1 a3", 
                insert prc_compat[of a1 a2 _ _ a3], force)
        }
        then show "?r O ?r' \<subseteq> ?r'" by auto
      qed
      let ?m = "\<lambda> (f,ts). ((f,length ts), ((f, length ts), ts))"
      let ?r = "{(a,b). (?m a, ?m b) \<in> ?r0}"
      have SN_r: "SN ?r" using SN_inv_image[OF SN1, of ?m] unfolding inv_image_def by fast
      let ?SA = "(\<lambda> x y. (x,y) \<in> S)"
      let ?NSA = "(\<lambda> x y. (x,y) \<in> NS)"
      let ?rr = "lex_two S NS ?r"
      define rr where "rr = ?rr" 
      from lex_two[OF compat_NS_S SN SN_r]
      have SN_rr: "SN rr" unfolding rr_def by auto
      let ?rrr = "inv_image rr (\<lambda> (f,ts). (Fun f ts, (f,ts)))"
      have SN_rrr: "SN ?rrr" 
        by (rule SN_inv_image[OF SN_rr])
      let ?ind = "\<lambda> (f,ts). ?Slist (f,length ts) ts \<longrightarrow> ?S (Fun f ts)"
      have "?ind (f,ts)"
      proof (rule SN_induct[OF SN_rrr, of ?ind])
        fix fts
        assume ind: "\<And> gss. (fts,gss) \<in> ?rrr \<Longrightarrow> ?ind gss"
        obtain f ts where Pair: "fts = (f,ts)" by force
        let ?f = "(f,length ts)"
        note ind = ind[unfolded Pair]
        show "?ind fts" unfolding Pair split
        proof (intro impI)
          assume ts: "?Slist ?f ts"
          let ?t = "Fun f ts"	
          show "?S ?t"
          proof (simp only: iff[of ?t], intro allI impI)
            fix s
            assume "(?t,s) \<in> WPO_S"
            then have "?t \<succ> s" by simp
            then show "?S s"
            proof (induct s, simp add: var_SN)
              case (Fun g ss) note IH = this
              let ?s = "Fun g ss"
              let ?g = "(g,length ss)"
              from Fun have t_gr_s: "?t \<succ> ?s" by auto
              show "?S ?s"
              proof (cases "\<exists> i \<in> set (\<sigma> ?f). ts ! i \<succeq> ?s")
                case True
                then obtain i where "i \<in> set (\<sigma> ?f)" and ge: "ts ! i \<succeq> ?s" by auto	      
                with ts have "?S (ts ! i)" by auto
                show "?S ?s"
                proof (unfold iff[of ?s], intro allI impI)
                  fix u
                  assume "(?s,u) \<in> WPO_S"
                  with wpo_compat ge have u: "ts ! i \<succ> u" by blast
                  with \<open>?S (ts ! i)\<close>[unfolded iff[of "ts ! i"]]
                  show "?S u" by simp
                qed
              next
                case False note oFalse = this
                from wpo_s_imp_NS[OF t_gr_s]
                have t_NS_s: "(?t,?s) \<in> NS" .
                show ?thesis
                proof (cases "(?t,?s) \<in> S")
                  case True
                  then have "((f,ts),(g,ss)) \<in> ?rrr" unfolding rr_def by auto
                  with ind have ind: "?ind (g,ss)" by auto
                  {
                    fix i
                    assume i: "i \<in> set (\<sigma> ?g)"
                    have "?s \<succeq> ss ! i" by (rule subterm_wpo_ns_arg[OF i])
                    with t_gr_s have ts: "?t \<succ> ss ! i" using wpo_compat by blast
                    have "?S (ss ! i)" using IH(1)[OF \<sigma>E[OF i] ts] by auto
                  } note SN_ss = this
                  from ind SN_ss show ?thesis by auto
                next
                  case False 
                  with t_NS_s oFalse 
                  have id: "(?t,?s) \<in> S = False" "(?t,?s) \<in> NS = True" by simp_all
                  let ?ls = "length ss"
                  let ?lt = "length ts"
                  let ?f = "(f,?lt)"
                  let ?g = "(g,?ls)"
                  obtain s1 ns1 where prc1: "prc ?f ?g = (s1,ns1)" by force
                  note t_gr_s = t_gr_s[unfolded wpo.simps[of ?t ?s], 
                      unfolded term.simps id if_True if_False prc1 split]
                  from oFalse t_gr_s have f_ge_g: "ns1"
                    by (cases ?thesis, auto)
                  from oFalse t_gr_s f_ge_g have small_ss: "\<forall> i \<in> set (\<sigma> ?g). ?t \<succ> ss ! i"
                    by (cases ?thesis, auto)
                  with Fun \<sigma>E[of _ g ss] have ss_S: "?Slist ?g ss" by auto
                  show ?thesis
                  proof (cases s1)
                    case True
                    then have "((f,ts),(g,ss)) \<in> ?r"  by (simp add: prc1)
                    with t_NS_s have "((f,ts),(g,ss)) \<in> ?rrr" unfolding rr_def by auto
                    with ind have "?ind (g,ss)" by auto
                    with ss_S show ?thesis by auto
                  next
                    case False
                    consider (Diff) "c ?f \<noteq> c ?g" | (Lex) "c ?f = Lex" "c ?g = Lex" | (Mul) "c ?f = Mul" "c ?g = Mul" 
                      by (cases "c ?f"; cases "c ?g", auto)
                    thus ?thesis
                    proof cases
                      case Diff
                      with False oFalse f_ge_g t_gr_s small_ss prc1 t_NS_s
                      have "((f,ts),(g,ss)) \<in> ?rrr" unfolding rr_def by (cases "c ?f"; cases "c ?g", auto)
                      with ind have "?ind (g,ss)" using Pair by auto
                      with ss_S show ?thesis by simp
                    next
                      case Lex
                      from False oFalse t_gr_s small_ss f_ge_g Lex
                      have lex: "fst (lex_ext wpo n (map ((!) ts) (\<sigma> ?f)) (map ((!) ss) (\<sigma> ?g)))"
                        by auto
                      from False lex ts f_ge_g Lex have "((f,ts),(g,ss)) \<in> ?r"
                        by (simp add: prc1)
                      with t_NS_s have "((f,ts),(g,ss)) \<in> ?rrr" unfolding rr_def by auto
                      with ind have "?ind (g,ss)" by auto
                      with ss_S show ?thesis by auto
                    next
                      case Mul
                      from False oFalse t_gr_s small_ss f_ge_g Mul
                      have mul: "fst (mul_ext wpo (map ((!) ts) (\<sigma> ?f)) (map ((!) ss) (\<sigma> ?g)))"
                        by auto
                      from False mul ts f_ge_g Mul have "((f,ts),(g,ss)) \<in> ?r"
                        by (simp add: prc1)
                      with t_NS_s have "((f,ts),(g,ss)) \<in> ?rrr" unfolding rr_def by auto
                      with ind have "?ind (g,ss)" by auto
                      with ss_S show ?thesis by auto
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
      with Fun show ?case using \<sigma>E[of _ f ts] by simp
    qed
  }
  from SN_I[OF this]
  show "SN {(s::('f, 'v)term, t). fst (wpo s t)}" .
qed

theorem WPO_SN_order_pair: "SN_order_pair WPO_S WPO_NS"
proof
  show "refl WPO_NS" using wpo_ns_refl unfolding refl_on_def by auto
  show "trans WPO_NS" using wpo_compat unfolding trans_def by blast
  show "trans WPO_S" using wpo_compat wpo_s_imp_ns unfolding trans_def by blast
  show "WPO_NS O WPO_S \<subseteq> WPO_S" using wpo_compat by blast
  show "WPO_S O WPO_NS \<subseteq> WPO_S" using wpo_compat by blast
  show "SN WPO_S" using WPO_S_SN .
qed

theorem WPO_S_subst: "(s,t) \<in> WPO_S \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> WPO_S" for \<sigma>
  using wpo_stable by auto

theorem WPO_NS_subst: "(s,t) \<in> WPO_NS \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> WPO_NS" for \<sigma>
  using wpo_stable by auto

theorem WPO_NS_ctxt: "(s,t) \<in> WPO_NS \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> WPO_NS" 
  using wpo_ns_mono by blast

theorem WPO_S_subset_WPO_NS: "WPO_S \<subseteq> WPO_NS" 
  using wpo_s_imp_ns by blast


context (* if \<sigma> is the full status, then WPO_S is a simplification order *)
  assumes \<sigma>_full: "\<And> f k. set (\<sigma> (f,k)) = {0 ..< k}"
begin

lemma subterm_wpo_s: "s \<rhd> t \<Longrightarrow> s \<succ> t"
proof (induct s t rule: supt.induct)
  case (arg s ss f)
  from arg[unfolded set_conv_nth] obtain i where i: "i < length ss" and s: "s = ss ! i" by auto  
  from \<sigma>_full[of f "length ss"] i have ii: "i \<in> set (\<sigma> (f,length ss))" by auto
  from subterm_wpo_s_arg[OF ii] s show ?case by auto
next
  case (subt s ss t f)
  from subt wpo_s_imp_ns have "\<exists> s \<in> set ss. wpo_ns s t" by blast
  from this[unfolded set_conv_nth] obtain i where ns: "ss ! i \<succeq> t" and i: "i < length ss" by auto
  from \<sigma>_full[of f "length ss"] i have ii: "i \<in> set (\<sigma> (f,length ss))" by auto
  from subt have "Fun f ss \<unrhd> t" by auto
  from NS_subterm[OF \<sigma>_full this] ns ii
  show ?case by (auto simp: wpo.simps)
qed

(* Compatibility of the subterm relation with the order relation:
    a subterm is smaller *)
lemma subterm_wpo_ns: assumes supteq: "s \<unrhd> t" shows "s \<succeq> t" 
proof -
  from supteq have "s = t \<or> s \<rhd> t" by auto
  then show ?thesis
  proof
    assume "s = t" then show ?thesis using wpo_ns_refl by blast
  next
    assume "s \<rhd> t"
    from wpo_s_imp_ns[OF subterm_wpo_s[OF this]]
    show ?thesis .
  qed
qed

lemma wpo_s_mono: assumes rels: "s \<succ> t"
  shows "Fun f (bef @ s # aft) \<succ> Fun f (bef @ t # aft)"
proof -
  let ?ss = "bef @ s # aft"
  let ?ts = "bef @ t # aft"
  let ?s = "Fun f ?ss"
  let ?t = "Fun f ?ts"
  let ?len = "Suc (length bef + length aft)"
  let ?f = "(f, ?len)"
  let ?\<sigma> = "\<sigma> ?f"
  from wpo_s_imp_ns[OF rels] have rel: "wpo_ns s t" .
  from wpo_ns_pre_mono[OF rel]
  have id: "(\<forall>j\<in>set ?\<sigma>. wpo_s ?s ((bef @ t # aft) ! j)) = True" 
    "((?s,?t) \<in> NS) = True" 
    "length ?ss = ?len" "length ?ts = ?len"
    by auto 
  let ?lb = "length bef" 
  from \<sigma>_full[of f ?len] have lb_mem: "?lb \<in> set ?\<sigma>" by auto
  then obtain i where \<sigma>i: "?\<sigma> ! i = ?lb" and i: "i < length ?\<sigma>" 
    unfolding set_conv_nth by force
  let ?mss = "map ((!) ?ss) ?\<sigma>"
  let ?mts = "map ((!) ?ts) ?\<sigma>"
  have "fst (lex_ext wpo n ?mss ?mts)" 
    unfolding lex_ext_iff fst_conv
  proof (intro conjI, force, rule disjI1, unfold length_map id, intro exI conjI, rule i, rule i, 
      intro allI impI)
    show "wpo_s (?mss ! i) (?mts ! i)" using \<sigma>i i rels by simp
  next
    fix j
    assume "j < i"
    with i have j: "j < length ?\<sigma>" by auto
    with wpo_ns_pre_mono[OF rel]
    show "?mss ! j \<succeq> ?mts ! j" by blast
  qed
  moreover 
  obtain lb nlb where part: "partition ((=) ?lb) ?\<sigma> = (lb, nlb)" by force
  hence mset_\<sigma>: "mset ?\<sigma> = mset lb + mset nlb" 
    by (induct ?\<sigma>, auto)
  let ?mlbs = "map ((!) ?ss) lb" 
  let ?mnlbs = "map ((!) ?ss) nlb" 
  let ?mlbt = "map ((!) ?ts) lb" 
  let ?mnlbt = "map ((!) ?ts) nlb" 
  have id1: "mset ?mss = mset ?mnlbs + mset ?mlbs" using mset_\<sigma> by auto
  have id2: "mset ?mts = mset ?mnlbt + mset ?mlbt" using mset_\<sigma> by auto
  from part lb_mem have lb: "?lb \<in> set lb" by auto
  have "fst (mul_ext wpo ?mss ?mts)" 
    unfolding mul_ext_def Let_def fst_conv
  proof (intro s_mul_extI_old, rule id1, rule id2)
    from lb show "mset ?mlbs \<noteq> {#}" by auto
    {
      fix i
      assume "i < length ?mnlbt" 
      then obtain j where id: "?mnlbs ! i = ?ss ! j" "?mnlbt ! i = ?ts ! j" "j \<in> set nlb" by auto
      with part have "j \<noteq> ?lb" by auto
      hence "?ss ! j = ?ts ! j" by (auto simp: nth_append)
      thus "(?mnlbs ! i, ?mnlbt ! i) \<in> WPO_NS" unfolding id using wpo_ns_refl by auto
    }
    fix u
    assume "u \<in># mset ?mlbt" 
    hence "u = t" using part by auto
    moreover have "s \<in># mset ?mlbs" using lb by force
    ultimately show "\<exists> v. v \<in>#  mset ?mlbs \<and> (v,u) \<in> WPO_S" using rels by force
  qed auto
  ultimately show ?thesis unfolding wpo.simps[of ?s ?t] term.simps id prc_refl
    using order_tag.exhaust by (auto simp: Let_def)
qed

theorem WPO_S_ctxt: "(s,t) \<in> WPO_S \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> WPO_S" 
  using wpo_s_mono by blast

theorem supt_subset_WPO_S: "{\<rhd>} \<subseteq> WPO_S" 
  using subterm_wpo_s by blast

theorem supteq_subset_WPO_NS: "{\<unrhd>} \<subseteq> WPO_NS" 
  using subterm_wpo_ns by blast

end

end

end
