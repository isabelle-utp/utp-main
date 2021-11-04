(*<*)
theory Safety
  imports Operational IVSubstTypingL BTVSubstTypingL 
begin
  (*>*)

method supp_calc = (metis (mono_tags, hide_lams) pure_supp  c.supp e.supp v.supp supp_l_empty opp.supp sup_bot.right_neutral supp_at_base)
declare infer_e.intros[simp]
declare infer_e.intros[intro]

chapter \<open>Safety\<close>

text \<open>Lemmas about the operational semantics leading up to progress and preservation and then
safety.\<close>

section \<open>Store Lemmas\<close>

abbreviation delta_ext (" _ \<sqsubseteq> _ ") where  
  "delta_ext \<Delta> \<Delta>' \<equiv> (setD \<Delta> \<subseteq> setD \<Delta>')" 

nominal_function dc_of :: "branch_s \<Rightarrow> string" where
  "dc_of (AS_branch dc _ _) = dc"
  apply(auto,simp add: eqvt_def dc_of_graph_aux_def)
  using   s_branch_s_branch_list.exhaust by metis
nominal_termination (eqvt) by lexicographic_order

lemma delta_sim_fresh: 
  assumes "\<Theta> \<turnstile> \<delta> \<sim> \<Delta>" and "atom u \<sharp> \<delta>"
  shows "atom u \<sharp> \<Delta>"
  using assms proof(induct rule : delta_sim.inducts)
  case (delta_sim_nilI \<Theta>)
  then show ?case using fresh_def supp_DNil by blast
next
  case (delta_sim_consI \<Theta> \<delta> \<Delta> v \<tau> u')
  hence  "\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f \<tau>" using check_v_wf  by meson
  hence  "supp \<tau> = {}" using  wfT_supp by fastforce
  moreover have  "atom u \<sharp> u'" using delta_sim_consI fresh_Cons fresh_Pair by blast
  moreover have "atom u \<sharp> \<Delta>" using delta_sim_consI fresh_Cons by blast
  ultimately show ?case using fresh_Pair fresh_DCons fresh_def by blast
qed

lemma delta_sim_v: 
  fixes \<Delta>::\<Delta>
  assumes "\<Theta> \<turnstile> \<delta> \<sim> \<Delta> " and "(u,v) \<in> set \<delta>" and "(u,\<tau>) \<in> setD \<Delta>" and "\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f \<Delta>"
  shows "\<Theta> ; {||} ; GNil \<turnstile> v \<Leftarrow> \<tau>"
  using assms proof(induct \<delta> arbitrary: \<Delta>)
  case Nil
  then show ?case by auto
next
  case (Cons uv \<delta>)
  obtain u' and v' where uv : "uv=(u',v')" by fastforce
  show ?case proof(cases "u'=u")
    case True
    hence  *:"\<Theta> \<turnstile> ((u,v')#\<delta>) \<sim> \<Delta>" using uv Cons by blast
    then obtain \<tau>' and \<Delta>' where tt: "\<Theta> ; {||} ; GNil \<turnstile> v' \<Leftarrow> \<tau>' \<and> u \<notin> fst ` set \<delta> \<and> \<Delta> = (u,\<tau>')#\<^sub>\<Delta>\<Delta>'" using delta_sim_elims(3)[OF *] by metis
    moreover hence "v'=v" using Cons True 
      by (metis Pair_inject fst_conv image_eqI set_ConsD uv)
    moreover have "\<tau>=\<tau>'" using wfD_unique tt Cons 
        setD.simps list.set_intros by blast
    ultimately show ?thesis by metis
  next
    case False
    hence  *:"\<Theta> \<turnstile> ((u',v')#\<delta>) \<sim> \<Delta>" using uv Cons by blast
    then obtain \<tau>' and \<Delta>' where tt: "\<Theta> \<turnstile> \<delta> \<sim> \<Delta>' \<and> \<Theta> ; {||} ; GNil \<turnstile> v' \<Leftarrow> \<tau>' \<and> u' \<notin> fst ` set \<delta> \<and> \<Delta> = (u',\<tau>')#\<^sub>\<Delta>\<Delta>'" using delta_sim_elims(3)[OF *] by metis

    moreover hence "\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f \<Delta>'" using wfD_elims Cons delta_sim_elims by metis
    ultimately show ?thesis using Cons  
      using False by auto
  qed
qed

lemma delta_sim_delta_lookup:
  assumes "\<Theta> \<turnstile> \<delta> \<sim> \<Delta> " and "(u, \<lbrace> z : b  | c \<rbrace>) \<in> setD \<Delta>" 
  shows "\<exists>v. (u,v) \<in> set \<delta>"
  using assms by(induct rule: delta_sim.inducts,auto+)

lemma update_d_stable:
  "fst ` set \<delta> = fst ` set (update_d \<delta> u v)"
proof(induct \<delta>)
  case Nil
  then show ?case by auto
next
  case (Cons a \<delta>)
  then show ?case using update_d.simps
    by (metis (no_types, lifting) eq_fst_iff image_cong image_insert list.simps(15) prod.exhaust_sel)
qed

lemma update_d_sim:
  fixes \<Delta>::\<Delta>
  assumes "\<Theta> \<turnstile> \<delta> \<sim> \<Delta>" and "\<Theta> ; {||} ; GNil \<turnstile> v \<Leftarrow> \<tau>" and "(u,\<tau>) \<in> setD \<Delta>" and "\<Theta> ; {||} ; GNil  \<turnstile>\<^sub>w\<^sub>f \<Delta>"
  shows "\<Theta> \<turnstile> (update_d \<delta> u v) \<sim> \<Delta>"
  using assms proof(induct \<delta> arbitrary: \<Delta>)
  case Nil
  then show ?case using delta_sim_consI by simp
next
  case (Cons uv \<delta>)
  obtain u' and v' where uv : "uv=(u',v')" by fastforce

  hence  *:"\<Theta> \<turnstile> ((u',v')#\<delta>) \<sim> \<Delta>" using uv Cons by blast
  then obtain \<tau>' and \<Delta>' where tt: "\<Theta> \<turnstile> \<delta> \<sim> \<Delta>' \<and> \<Theta> ; {||} ; GNil \<turnstile> v' \<Leftarrow> \<tau>' \<and> u' \<notin> fst ` set \<delta> \<and> \<Delta> = (u',\<tau>')#\<^sub>\<Delta>\<Delta>'" using delta_sim_elims * by metis

  show ?case proof(cases "u=u'")
    case True
    then have "(u,\<tau>') \<in> setD \<Delta>" using tt by auto
    then have "\<tau> = \<tau>'" using Cons  wfD_unique by metis
    moreover  have "update_d ((u',v')#\<delta>) u v = ((u',v)#\<delta>)" using update_d.simps True by presburger
    ultimately show ?thesis using delta_sim_consI tt Cons True 
      by (simp add: tt uv)
  next
    case False
    have  "\<Theta> \<turnstile> (u',v') # (update_d \<delta> u v) \<sim> (u',\<tau>')#\<^sub>\<Delta>\<Delta>'" 
    proof(rule delta_sim_consI)
      show "\<Theta> \<turnstile> update_d \<delta> u v \<sim> \<Delta>' " using Cons using delta_sim_consI 
          delta_sim.simps update_d.simps Cons  delta_sim_elims uv  tt 
          False fst_conv set_ConsD wfG_elims wfD_elims  by (metis setD_ConsD)
      show "\<Theta> ; {||} ; GNil  \<turnstile> v' \<Leftarrow> \<tau>'" using tt by auto
      show "u' \<notin> fst ` set (update_d \<delta> u v)" using  update_d.simps Cons update_d_stable tt by auto
    qed
    thus  ?thesis using False update_d.simps uv 
      by (simp add: tt)
  qed
qed

section \<open>Preservation\<close>
text \<open>Types are preserved under reduction step. Broken down into lemmas about different operations\<close>

subsection \<open>Function Application\<close>

lemma check_s_x_fresh:
  fixes x::x and s::s
  assumes "\<Theta> ; \<Phi> ; B ;  GNil ; D  \<turnstile> s \<Leftarrow> \<tau>" 
  shows "atom x \<sharp> s \<and> atom x \<sharp> \<tau> \<and> atom x \<sharp> D"
proof - 
  have "\<Theta> ; \<Phi> ; B ; GNil ; D \<turnstile>\<^sub>w\<^sub>f s : b_of \<tau>"  using check_s_wf[OF assms] by auto 
  moreover have "\<Theta> ; B ; GNil   \<turnstile>\<^sub>w\<^sub>f \<tau> " using check_s_wf assms by auto
  moreover have "\<Theta> ; B ; GNil   \<turnstile>\<^sub>w\<^sub>f D" using check_s_wf assms by auto
  ultimately show ?thesis using wf_supp x_fresh_u 
    by (meson fresh_GNil wfS_x_fresh wfT_x_fresh wfD_x_fresh)
qed

lemma check_funtyp_subst_b: 
  fixes b'::b
  assumes "check_funtyp \<Theta> \<Phi> {|bv|} (AF_fun_typ x b c \<tau> s)" and \<open> \<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f b' \<close>
  shows "check_funtyp \<Theta> \<Phi>  {||} (AF_fun_typ x b[bv::=b']\<^sub>b\<^sub>b (c[bv::=b']\<^sub>c\<^sub>b) \<tau>[bv::=b']\<^sub>\<tau>\<^sub>b s[bv::=b']\<^sub>s\<^sub>b)"
  using assms proof (nominal_induct "{|bv|}" "AF_fun_typ x b c \<tau> s" rule: check_funtyp.strong_induct)
  case (check_funtypI x' \<Theta> \<Phi> c' s' \<tau>')
  have "check_funtyp \<Theta> \<Phi> {||} (AF_fun_typ x' b[bv::=b']\<^sub>b\<^sub>b (c'[bv::=b']\<^sub>c\<^sub>b) \<tau>'[bv::=b']\<^sub>\<tau>\<^sub>b s'[bv::=b']\<^sub>s\<^sub>b)" proof
    show \<open>atom x' \<sharp> (\<Theta>, \<Phi>, {||}::bv fset, b[bv::=b']\<^sub>b\<^sub>b)\<close> using check_funtypI fresh_prodN x_fresh_b fresh_empty_fset by metis

    have  \<open> \<Theta> ; \<Phi> ; {||} ; ((x', b, c') #\<^sub>\<Gamma> GNil)[bv::=b']\<^sub>\<Gamma>\<^sub>b ; []\<^sub>\<Delta>[bv::=b']\<^sub>\<Delta>\<^sub>b  \<turnstile> s'[bv::=b']\<^sub>s\<^sub>b \<Leftarrow> \<tau>'[bv::=b']\<^sub>\<tau>\<^sub>b\<close>  proof(rule subst_b_check_s)
      show \<open> \<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f b' \<close> using check_funtypI by metis
      show \<open>{|bv|} = {|bv|}\<close> by auto
      show \<open> \<Theta> ; \<Phi> ; {|bv|} ; (x', b, c') #\<^sub>\<Gamma> GNil ; []\<^sub>\<Delta>  \<turnstile> s' \<Leftarrow> \<tau>'\<close> using check_funtypI by metis
    qed

    thus \<open> \<Theta> ; \<Phi> ; {||} ; (x', b[bv::=b']\<^sub>b\<^sub>b, c'[bv::=b']\<^sub>c\<^sub>b) #\<^sub>\<Gamma> GNil ; []\<^sub>\<Delta>  \<turnstile> s'[bv::=b']\<^sub>s\<^sub>b \<Leftarrow> \<tau>'[bv::=b']\<^sub>\<tau>\<^sub>b\<close> 
      using subst_gb.simps subst_db.simps by simp
  qed

  moreover have "(AF_fun_typ x b c \<tau> s) = (AF_fun_typ x' b c' \<tau>' s')"  using fun_typ.eq_iff check_funtypI by metis
  moreover hence "(AF_fun_typ x b[bv::=b']\<^sub>b\<^sub>b (c[bv::=b']\<^sub>c\<^sub>b) \<tau>[bv::=b']\<^sub>\<tau>\<^sub>b s[bv::=b']\<^sub>s\<^sub>b) = (AF_fun_typ x' b[bv::=b']\<^sub>b\<^sub>b (c'[bv::=b']\<^sub>c\<^sub>b) \<tau>'[bv::=b']\<^sub>\<tau>\<^sub>b s'[bv::=b']\<^sub>s\<^sub>b)"
    using  subst_ft_b.simps by metis
  ultimately show  ?case by metis
qed

lemma funtyp_simple_check:
  fixes s::s  and \<Delta>::\<Delta> and \<tau>::\<tau> and v::v  
  assumes "check_funtyp \<Theta> \<Phi>  ({||}::bv fset) (AF_fun_typ x b c \<tau> s)" and
    "\<Theta> ; {||} ; GNil \<turnstile> v \<Leftarrow> \<lbrace> x : b | c \<rbrace>" 
  shows "\<Theta> ; \<Phi> ;  {||} ; GNil ; DNil \<turnstile> s[x::=v]\<^sub>s\<^sub>v \<Leftarrow> \<tau>[x::=v]\<^sub>\<tau>\<^sub>v"
  using assms proof(nominal_induct  " ({||}::bv fset)" "AF_fun_typ x b c \<tau> s" avoiding: v x  rule: check_funtyp.strong_induct)
  case (check_funtypI x' \<Theta> \<Phi> c' s' \<tau>')

  hence eq1: "\<lbrace> x' : b  | c' \<rbrace> = \<lbrace> x : b  | c \<rbrace>" using funtyp_eq_iff_equalities by metis

  obtain x'' and c'' where xf:"\<lbrace> x : b  | c \<rbrace> = \<lbrace> x'' : b | c'' \<rbrace> \<and> atom x'' \<sharp> (x',v) \<and> atom x'' \<sharp> (x,c)" using obtain_fresh_z3 by metis 
  moreover have "atom x' \<sharp> c''" proof -
    have "supp  \<lbrace> x'' : b | c'' \<rbrace> = {}" using eq1 check_funtypI xf check_v_wf wfT_nil_supp by metis 
    hence "supp c'' \<subseteq> { atom x'' }" using  \<tau>.supp eq1 xf by (auto simp add: freshers)
    moreover have "atom x' \<noteq> atom x''" using xf fresh_Pair fresh_x_neq by metis
    ultimately show ?thesis using xf fresh_Pair fresh_x_neq fresh_def fresh_at_base by blast
  qed
  ultimately have eq2: "c''[x''::=[ x' ]\<^sup>v]\<^sub>c\<^sub>v = c'" using eq1  type_eq_subst_eq3(1)[of x' b c' x'' b  c''] by metis

  have "atom x' \<sharp> c" proof -
    have "supp  \<lbrace> x : b | c \<rbrace> = {}" using eq1 check_funtypI xf check_v_wf wfT_nil_supp by metis 
    hence "supp c \<subseteq> { atom x }" using  \<tau>.supp by auto
    moreover have "atom x \<noteq> atom x'" using check_funtypI fresh_Pair fresh_x_neq by metis
    ultimately show ?thesis using fresh_def by force
  qed
  hence eq: " c[x::=[ x' ]\<^sup>v]\<^sub>c\<^sub>v =  c' \<and> s'[x'::=v]\<^sub>s\<^sub>v = s[x::=v]\<^sub>s\<^sub>v \<and> \<tau>'[x'::=v]\<^sub>\<tau>\<^sub>v = \<tau>[x::=v]\<^sub>\<tau>\<^sub>v" 
    using funtyp_eq_iff_equalities type_eq_subst_eq3 check_funtypI by metis

  have " \<Theta> ; \<Phi> ; {||} ; ((x', b, c''[x''::=[ x' ]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> GNil)[x'::=v]\<^sub>\<Gamma>\<^sub>v ; []\<^sub>\<Delta>[x'::=v]\<^sub>\<Delta>\<^sub>v  \<turnstile> s'[x'::=v]\<^sub>s\<^sub>v \<Leftarrow> \<tau>'[x'::=v]\<^sub>\<tau>\<^sub>v" 
  proof(rule subst_check_check_s )
    show \<open>\<Theta> ; {||} ; GNil  \<turnstile> v \<Leftarrow> \<lbrace> x'' : b  | c'' \<rbrace>\<close> using check_funtypI eq1 xf by metis
    show \<open>atom x'' \<sharp> (x', v)\<close> using check_funtypI fresh_x_neq fresh_Pair xf by metis
    show \<open> \<Theta> ; \<Phi> ; {||} ; (x', b, c''[x''::=[ x' ]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> GNil ; []\<^sub>\<Delta>  \<turnstile> s' \<Leftarrow> \<tau>'\<close> using check_funtypI eq2 by metis
    show \<open> (x', b, c''[x''::=[ x' ]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> GNil = GNil  @ (x', b, c''[x''::=[ x' ]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> GNil\<close> using append_g.simps by auto
  qed
  hence " \<Theta>; \<Phi>; {||}; GNil; []\<^sub>\<Delta>  \<turnstile> s'[x'::=v]\<^sub>s\<^sub>v \<Leftarrow> \<tau>'[x'::=v]\<^sub>\<tau>\<^sub>v" using subst_gv.simps subst_dv.simps by auto
  thus ?case using eq  by auto
qed

lemma funtypq_simple_check:
  fixes s::s  and \<Delta>::\<Delta> and \<tau>::\<tau> and v::v  
  assumes "check_funtypq \<Theta> \<Phi>   (AF_fun_typ_none (AF_fun_typ x b c t s))" and
    "\<Theta> ; {||} ; GNil \<turnstile> v \<Leftarrow> \<lbrace> x : b | c \<rbrace>" 
  shows "\<Theta>; \<Phi>; {||}; GNil; DNil \<turnstile> s[x::=v]\<^sub>s\<^sub>v \<Leftarrow> t[x::=v]\<^sub>\<tau>\<^sub>v"
  using assms proof(nominal_induct  "(AF_fun_typ_none (AF_fun_typ x b c t s))" avoiding: v rule: check_funtypq.strong_induct)
  case (check_fundefq_simpleI \<Theta> \<Phi> x' c' t' s')
  hence eq: "\<lbrace> x : b  | c \<rbrace> = \<lbrace> x' : b  | c' \<rbrace> \<and> s'[x'::=v]\<^sub>s\<^sub>v = s[x::=v]\<^sub>s\<^sub>v \<and> t[x::=v]\<^sub>\<tau>\<^sub>v = t'[x'::=v]\<^sub>\<tau>\<^sub>v" 
    using funtyp_eq_iff_equalities by metis
  hence "\<Theta>; \<Phi>; {||}; GNil; []\<^sub>\<Delta>  \<turnstile> s'[x'::=v]\<^sub>s\<^sub>v \<Leftarrow> t'[x'::=v]\<^sub>\<tau>\<^sub>v" 
    using funtyp_simple_check[OF check_fundefq_simpleI(1)] check_fundefq_simpleI by metis
  thus ?case  using eq by metis
qed

lemma funtyp_poly_eq_iff_equalities:
  assumes "[[atom bv']]lst. AF_fun_typ x' b'' c' t' s' = [[atom bv]]lst. AF_fun_typ x b c t s" 
  shows "\<lbrace> x' : b''[bv'::=b']\<^sub>b\<^sub>b  | c'[bv'::=b']\<^sub>c\<^sub>b \<rbrace> = \<lbrace> x : b[bv::=b']\<^sub>b\<^sub>b  | c[bv::=b']\<^sub>c\<^sub>b \<rbrace> \<and> 
          s'[bv'::=b']\<^sub>s\<^sub>b[x'::=v]\<^sub>s\<^sub>v = s[bv::=b']\<^sub>s\<^sub>b[x::=v]\<^sub>s\<^sub>v \<and> t'[bv'::=b']\<^sub>\<tau>\<^sub>b[x'::=v]\<^sub>\<tau>\<^sub>v = t[bv::=b']\<^sub>\<tau>\<^sub>b[x::=v]\<^sub>\<tau>\<^sub>v" 
proof - 
  have "subst_ft_b (AF_fun_typ x' b'' c' t' s') bv' b' = subst_ft_b (AF_fun_typ x b c t s) bv b'"
    using subst_b_flip_eq_two subst_b_fun_typ_def assms by metis
  thus ?thesis using fun_typ.eq_iff subst_ft_b.simps funtyp_eq_iff_equalities subst_tb.simps 
    by (metis (full_types) assms fun_poly_arg_unique)

qed

lemma funtypq_poly_check:
  fixes s::s  and \<Delta>::\<Delta> and \<tau>::\<tau> and v::v  and b'::b
  assumes "check_funtypq \<Theta> \<Phi>   (AF_fun_typ_some bv (AF_fun_typ x b c t s))" and
    "\<Theta> ; {||} ; GNil \<turnstile> v \<Leftarrow> \<lbrace> x : b[bv::=b']\<^sub>b\<^sub>b | c[bv::=b']\<^sub>c\<^sub>b \<rbrace>"   and
    "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f b'" 
  shows "\<Theta>; \<Phi>; {||}; GNil; DNil \<turnstile> s[bv::=b']\<^sub>s\<^sub>b[x::=v]\<^sub>s\<^sub>v \<Leftarrow> t[bv::=b']\<^sub>\<tau>\<^sub>b[x::=v]\<^sub>\<tau>\<^sub>v"
  using assms proof(nominal_induct  "(AF_fun_typ_some bv (AF_fun_typ x b c t s))" avoiding: v rule: check_funtypq.strong_induct)
  case (check_funtypq_polyI bv' \<Theta> \<Phi>  x' b'' c' t' s')

  hence **:"\<lbrace> x' : b''[bv'::=b']\<^sub>b\<^sub>b  | c'[bv'::=b']\<^sub>c\<^sub>b \<rbrace> = \<lbrace> x : b[bv::=b']\<^sub>b\<^sub>b  | c[bv::=b']\<^sub>c\<^sub>b \<rbrace> \<and> 
          s'[bv'::=b']\<^sub>s\<^sub>b[x'::=v]\<^sub>s\<^sub>v = s[bv::=b']\<^sub>s\<^sub>b[x::=v]\<^sub>s\<^sub>v \<and> t'[bv'::=b']\<^sub>\<tau>\<^sub>b[x'::=v]\<^sub>\<tau>\<^sub>v = t[bv::=b']\<^sub>\<tau>\<^sub>b[x::=v]\<^sub>\<tau>\<^sub>v" 
    using funtyp_poly_eq_iff_equalities by metis

  have *:"check_funtyp \<Theta> \<Phi> {||} (AF_fun_typ x' b''[bv'::=b']\<^sub>b\<^sub>b (c'[bv'::=b']\<^sub>c\<^sub>b) (t'[bv'::=b']\<^sub>\<tau>\<^sub>b) s'[bv'::=b']\<^sub>s\<^sub>b)"
    using check_funtyp_subst_b[OF check_funtypq_polyI(5) check_funtypq_polyI(8)]  by metis
  moreover have "\<Theta> ; {||} ; GNil  \<turnstile> v \<Leftarrow> \<lbrace> x' : b''[bv'::=b']\<^sub>b\<^sub>b  | c'[bv'::=b']\<^sub>c\<^sub>b \<rbrace>" using ** check_funtypq_polyI by metis
  ultimately have "\<Theta>; \<Phi>; {||}; GNil; []\<^sub>\<Delta>  \<turnstile> s'[bv'::=b']\<^sub>s\<^sub>b[x'::=v]\<^sub>s\<^sub>v \<Leftarrow> t'[bv'::=b']\<^sub>\<tau>\<^sub>b[x'::=v]\<^sub>\<tau>\<^sub>v"
    using funtyp_simple_check[OF *] check_funtypq_polyI by metis
  thus ?case using ** by metis

qed

lemma fundef_simple_check:
  fixes s::s  and \<Delta>::\<Delta> and \<tau>::\<tau> and v::v  
  assumes "check_fundef \<Theta> \<Phi>   (AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c t s)))" and
    "\<Theta> ; {||} ; GNil \<turnstile> v \<Leftarrow> \<lbrace> x : b | c \<rbrace>" and "\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f \<Delta>"
  shows "\<Theta>; \<Phi>; {||}; GNil; \<Delta> \<turnstile> s[x::=v]\<^sub>s\<^sub>v \<Leftarrow> t[x::=v]\<^sub>\<tau>\<^sub>v"
  using assms proof(nominal_induct  "(AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c t s)))" avoiding: v rule: check_fundef.strong_induct)
  case (check_fundefI \<Theta> \<Phi>)
  then show ?case using funtypq_simple_check[THEN check_s_d_weakening(1) ] setD.simps by auto
qed

lemma fundef_poly_check:
  fixes s::s  and \<Delta>::\<Delta> and \<tau>::\<tau> and v::v  and b'::b
  assumes "check_fundef \<Theta> \<Phi>   (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c t s)))" and
    "\<Theta> ; {||} ; GNil \<turnstile> v \<Leftarrow> \<lbrace> x : b[bv::=b']\<^sub>b\<^sub>b | c[bv::=b']\<^sub>c\<^sub>b \<rbrace>" and "\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f \<Delta>" and  "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f b'" 
  shows "\<Theta>; \<Phi>; {||}; GNil; \<Delta> \<turnstile> s[bv::=b']\<^sub>s\<^sub>b[x::=v]\<^sub>s\<^sub>v \<Leftarrow> t[bv::=b']\<^sub>\<tau>\<^sub>b[x::=v]\<^sub>\<tau>\<^sub>v" 
  using assms proof(nominal_induct  "(AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c t s)))" avoiding: v rule: check_fundef.strong_induct)
  case (check_fundefI \<Theta> \<Phi>)
  then show ?case using funtypq_poly_check[THEN check_s_d_weakening(1) ] setD.simps by auto
qed

lemma preservation_app:
  assumes
    "Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ x1 b1 c1 \<tau>1' s1'))) = lookup_fun \<Phi> f" and  "(\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)"
  shows "\<Theta> ; \<Phi> ; B ; G ; \<Delta>  \<turnstile> ss \<Leftarrow> \<tau> \<Longrightarrow>  B = {||} \<Longrightarrow> G = GNil \<Longrightarrow> ss = LET x = (AE_app f v) IN s \<Longrightarrow>  
           \<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> LET x : (\<tau>1'[x1::=v]\<^sub>\<tau>\<^sub>v) = (s1'[x1::=v]\<^sub>s\<^sub>v) IN s \<Leftarrow> \<tau>" and
    "check_branch_s \<Theta> \<Phi> \<B> GNil \<Delta> tid dc const v cs \<tau> \<Longrightarrow> True" and 
    "check_branch_list \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist v css \<tau> \<Longrightarrow> True"
  using assms proof(nominal_induct \<tau> and \<tau> and \<tau>   avoiding: v rule: check_s_check_branch_s_check_branch_list.strong_induct)
  case (check_letI x2 \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e \<tau> z s2 b c)

  hence eq: "e = (AE_app f v)" by simp
  hence *:"\<Theta> ; \<Phi> ; {||} ;GNil ; \<Delta>  \<turnstile> (AE_app f v) \<Rightarrow> \<lbrace> z : b  | c \<rbrace>" using check_letI by auto

  then obtain x3 b3 c3 \<tau>3 s3 where
    **:"\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f \<Delta>  \<and>  \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<and>  Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ x3 b3 c3 \<tau>3 s3))) = lookup_fun \<Phi> f \<and> 
     \<Theta> ; {||} ; GNil  \<turnstile> v \<Leftarrow> \<lbrace> x3 : b3  | c3 \<rbrace> \<and>  atom x3 \<sharp> (\<Theta>, \<Phi>, ({||}::bv fset), GNil, \<Delta>, v, \<lbrace> z : b  | c \<rbrace>) \<and>  \<tau>3[x3::=v]\<^sub>\<tau>\<^sub>v = \<lbrace> z : b  | c \<rbrace>"
    using infer_e_elims(6)[OF *] subst_defs by metis

  obtain z3 where z3:"\<lbrace> x3 : b3  | c3 \<rbrace> =  \<lbrace> z3 : b3  | c3[x3::=V_var z3]\<^sub>c\<^sub>v \<rbrace> \<and>  atom z3 \<sharp> (x3, v,c3,x1,c1)" using obtain_fresh_z3 by metis

  have seq:"[[atom x3]]lst. s3 = [[atom x1]]lst. s1'" using fun_def_eq check_letI ** option.inject by metis

  let ?ft = "AF_fun_typ x3 b3 c3 \<tau>3 s3"


  have sup: "supp \<tau>3 \<subseteq> { atom x3} \<and> supp s3 \<subseteq> { atom x3}"  using wfPhi_f_supp ** by metis

  have "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let2 x2  \<tau>3[x3::=v]\<^sub>\<tau>\<^sub>v (s3[x3::=v]\<^sub>s\<^sub>v) s2 \<Leftarrow> \<tau>" proof
    show \<open>atom x2 \<sharp> (\<Theta>, \<Phi>, {||}::bv fset, GNil, \<Delta>, \<tau>3[x3::=v]\<^sub>\<tau>\<^sub>v, s3[x3::=v]\<^sub>s\<^sub>v, \<tau>)\<close>
      unfolding fresh_prodN using check_letI fresh_subst_v_if subst_v_\<tau>_def sup
      by (metis all_not_in_conv fresh_def fresh_empty_fset fresh_subst_sv_if fresh_subst_tv_if singleton_iff subset_singleton_iff)

    show \<open> \<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> s3[x3::=v]\<^sub>s\<^sub>v \<Leftarrow> \<tau>3[x3::=v]\<^sub>\<tau>\<^sub>v\<close> proof(rule fundef_simple_check)
      show \<open>check_fundef \<Theta> \<Phi> (AF_fundef f (AF_fun_typ_none (AF_fun_typ x3 b3 c3 \<tau>3 s3)))\<close> using ** check_letI lookup_fun_member by metis
      show \<open>\<Theta> ; {||} ; GNil  \<turnstile> v \<Leftarrow> \<lbrace> x3 : b3  | c3 \<rbrace>\<close> using ** by auto
      show \<open> \<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using ** by auto
    qed
    show \<open> \<Theta> ; \<Phi> ; {||} ; (x2, b_of \<tau>3[x3::=v]\<^sub>\<tau>\<^sub>v, c_of \<tau>3[x3::=v]\<^sub>\<tau>\<^sub>v x2) #\<^sub>\<Gamma> GNil ; \<Delta>  \<turnstile> s2 \<Leftarrow> \<tau>\<close>  
      using check_letI ** b_of.simps c_of.simps subst_defs  by metis
  qed

  moreover have "AS_let2 x2  \<tau>3[x3::=v]\<^sub>\<tau>\<^sub>v (s3[x3::=v]\<^sub>s\<^sub>v) s2 = AS_let2 x   (\<tau>1'[x1::=v]\<^sub>\<tau>\<^sub>v) (s1'[x1::=v]\<^sub>s\<^sub>v) s" proof -
    have *: "[[atom x2]]lst. s2 = [[atom x]]lst. s" using check_letI  s_branch_s_branch_list.eq_iff by auto
    moreover have " \<tau>3[x3::=v]\<^sub>\<tau>\<^sub>v = \<tau>1'[x1::=v]\<^sub>\<tau>\<^sub>v" using fun_ret_unique ** check_letI by metis
    moreover have "s3[x3::=v]\<^sub>s\<^sub>v = (s1'[x1::=v]\<^sub>s\<^sub>v)" using subst_v_flip_eq_two subst_v_s_def seq by metis
    ultimately show ?thesis using s_branch_s_branch_list.eq_iff by metis
  qed

  ultimately show ?case using check_letI by auto
qed(auto+)

lemma fresh_subst_v_subst_b:
  fixes x2::x and tm::"'a::{has_subst_v,has_subst_b}" and x::x
  assumes  "supp tm \<subseteq> { atom bv, atom x }" and "atom x2 \<sharp> v" 
  shows  "atom x2 \<sharp> tm[bv::=b]\<^sub>b[x::=v]\<^sub>v"  
  using assms proof(cases "x2=x")
  case True
  then show ?thesis using fresh_subst_v_if assms by blast
next
  case False
  hence "atom x2 \<sharp> tm" using assms fresh_def fresh_at_base by force
  hence "atom x2 \<sharp> tm[bv::=b]\<^sub>b" using  assms fresh_subst_if x_fresh_b False by force
  then show ?thesis using fresh_subst_v_if assms by auto
qed

lemma preservation_poly_app:
  assumes
    "Some (AF_fundef f (AF_fun_typ_some bv1 (AF_fun_typ x1 b1 c1 \<tau>1' s1'))) = lookup_fun \<Phi> f" and  "(\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)"
  shows "\<Theta> ; \<Phi> ; B ; G ; \<Delta>  \<turnstile> ss \<Leftarrow> \<tau> \<Longrightarrow>  B = {||} \<Longrightarrow> G = GNil \<Longrightarrow> ss = LET x = (AE_appP f b' v) IN s \<Longrightarrow> \<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f b'  \<Longrightarrow> 
               \<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> LET x : (\<tau>1'[bv1::=b']\<^sub>\<tau>\<^sub>b[x1::=v]\<^sub>\<tau>\<^sub>v) = (s1'[bv1::=b']\<^sub>s\<^sub>b[x1::=v]\<^sub>s\<^sub>v) IN s \<Leftarrow> \<tau>" and
    "check_branch_s \<Theta> \<Phi> \<B> GNil \<Delta> tid dc const v cs \<tau> \<Longrightarrow> True" and 
    "check_branch_list \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist v css \<tau> \<Longrightarrow> True"
  using assms proof(nominal_induct \<tau> and \<tau> and \<tau>   avoiding: v x1 rule: check_s_check_branch_s_check_branch_list.strong_induct)
  case (check_letI x2 \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e \<tau> z s2 b c)

  hence eq: "e = (AE_appP f b' v)" by simp
  hence *:"\<Theta> ; \<Phi> ; {||} ;GNil ; \<Delta>  \<turnstile> (AE_appP f b' v) \<Rightarrow> \<lbrace> z : b  | c \<rbrace>" using check_letI by auto

  then obtain x3 b3 c3 \<tau>3 s3 bv3 where
    **:"\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f \<Delta>  \<and>  \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<and>  Some (AF_fundef f (AF_fun_typ_some bv3 (AF_fun_typ x3 b3 c3 \<tau>3 s3))) = lookup_fun \<Phi> f \<and> 
     \<Theta> ; {||} ; GNil  \<turnstile> v \<Leftarrow> \<lbrace> x3 : b3[bv3::=b']\<^sub>b\<^sub>b   | c3[bv3::=b']\<^sub>c\<^sub>b  \<rbrace> \<and>  atom x3 \<sharp> GNil \<and>  \<tau>3[bv3::=b']\<^sub>\<tau>\<^sub>b[x3::=v]\<^sub>\<tau>\<^sub>v = \<lbrace> z : b  | c \<rbrace>
  \<and> \<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f b'"
    using infer_e_elims(21)[OF *] subst_defs  by metis

  obtain z3 where z3:"\<lbrace> x3 : b3  | c3 \<rbrace> =  \<lbrace> z3 : b3  | c3[x3::=V_var z3]\<^sub>c\<^sub>v \<rbrace> \<and>  atom z3 \<sharp> (x3, v,c3,x1,c1)" using obtain_fresh_z3 by metis

  let ?ft = "(AF_fun_typ x3 (b3[bv3::=b']\<^sub>b\<^sub>b) (c3[bv3::=b']\<^sub>c\<^sub>b) (\<tau>3[bv3::=b']\<^sub>\<tau>\<^sub>b) (s3[bv3::=b']\<^sub>s\<^sub>b))"

  have *:"check_fundef \<Theta> \<Phi> (AF_fundef f (AF_fun_typ_some bv3 (AF_fun_typ x3 b3 c3 \<tau>3 s3)))" using ** check_letI lookup_fun_member by metis

  hence ftq:"check_funtypq \<Theta> \<Phi> (AF_fun_typ_some bv3 (AF_fun_typ x3 b3 c3 \<tau>3 s3))" using check_fundef_elims by auto

  let ?ft = "AF_fun_typ_some bv3 (AF_fun_typ x3 b3 c3 \<tau>3 s3)"

  have sup: "supp \<tau>3 \<subseteq> { atom x3, atom bv3} \<and> supp s3 \<subseteq> { atom x3, atom bv3 }"  
    using  wfPhi_f_poly_supp_t wfPhi_f_poly_supp_s ** by metis

  have "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let2 x2  \<tau>3[bv3::=b']\<^sub>\<tau>\<^sub>b[x3::=v]\<^sub>\<tau>\<^sub>v (s3[bv3::=b']\<^sub>s\<^sub>b[x3::=v]\<^sub>s\<^sub>v) s2 \<Leftarrow> \<tau>" 
  proof
    show \<open>atom x2 \<sharp> (\<Theta>, \<Phi>, {||}::bv fset, GNil, \<Delta>, \<tau>3[bv3::=b']\<^sub>\<tau>\<^sub>b[x3::=v]\<^sub>\<tau>\<^sub>v, s3[bv3::=b']\<^sub>s\<^sub>b[x3::=v]\<^sub>s\<^sub>v, \<tau>)\<close> 
    proof -

      have "atom x2 \<sharp> \<tau>3[bv3::=b']\<^sub>\<tau>\<^sub>b[x3::=v]\<^sub>\<tau>\<^sub>v" 
        using fresh_subst_v_subst_b subst_v_\<tau>_def subst_b_\<tau>_def \<open> atom x2 \<sharp> v\<close> sup by fastforce      
      moreover have "atom x2 \<sharp> s3[bv3::=b']\<^sub>s\<^sub>b[x3::=v]\<^sub>s\<^sub>v" 
        using fresh_subst_v_subst_b subst_v_s_def subst_b_s_def \<open> atom x2 \<sharp> v\<close> sup 
      proof -
        have "\<forall>b. atom x2 = atom x3 \<or> atom x2 \<sharp> s3[bv3::=b]\<^sub>b"
          by (metis (no_types) check_letI.hyps(1) fresh_subst_sv_if(1) fresh_subst_v_subst_b insert_commute subst_v_s_def sup) (* 140 ms *)
        then show ?thesis
          by (metis check_letI.hyps(1) fresh_subst_sb_if fresh_subst_sv_if(1) has_subst_b_class.subst_b_fresh_x x_fresh_b) (* 78 ms *)
      qed
      ultimately show ?thesis using fresh_prodN check_letI by metis
    qed

    show \<open> \<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> s3[bv3::=b']\<^sub>s\<^sub>b[x3::=v]\<^sub>s\<^sub>v \<Leftarrow> \<tau>3[bv3::=b']\<^sub>\<tau>\<^sub>b[x3::=v]\<^sub>\<tau>\<^sub>v\<close> proof( rule fundef_poly_check)
      show \<open>check_fundef \<Theta> \<Phi> (AF_fundef f (AF_fun_typ_some bv3 (AF_fun_typ x3 b3 c3 \<tau>3 s3)))\<close>   
        using **  lookup_fun_member check_letI by metis
      show \<open>\<Theta> ; {||} ; GNil  \<turnstile> v \<Leftarrow> \<lbrace> x3 : b3[bv3::=b']\<^sub>b\<^sub>b  | c3[bv3::=b']\<^sub>c\<^sub>b \<rbrace>\<close> using ** by metis
      show \<open> \<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using ** by metis
      show \<open> \<Theta> ;  {||}  \<turnstile>\<^sub>w\<^sub>f b' \<close>  using ** by metis
    qed
    show \<open> \<Theta> ; \<Phi> ; {||} ; (x2, b_of \<tau>3[bv3::=b']\<^sub>\<tau>\<^sub>b[x3::=v]\<^sub>\<tau>\<^sub>v, c_of \<tau>3[bv3::=b']\<^sub>\<tau>\<^sub>b[x3::=v]\<^sub>\<tau>\<^sub>v x2) #\<^sub>\<Gamma> GNil ; \<Delta>  \<turnstile> s2 \<Leftarrow> \<tau>\<close> 
      using check_letI ** b_of.simps c_of.simps subst_defs by metis
  qed

  moreover have "AS_let2 x2  \<tau>3[bv3::=b']\<^sub>\<tau>\<^sub>b[x3::=v]\<^sub>\<tau>\<^sub>v (s3[bv3::=b']\<^sub>s\<^sub>b[x3::=v]\<^sub>s\<^sub>v) s2 = AS_let2 x   (\<tau>1'[bv1::=b']\<^sub>\<tau>\<^sub>b[x1::=v]\<^sub>\<tau>\<^sub>v) (s1'[bv1::=b']\<^sub>s\<^sub>b[x1::=v]\<^sub>s\<^sub>v) s" proof -
    have *: "[[atom x2]]lst. s2 = [[atom x]]lst. s" using check_letI  s_branch_s_branch_list.eq_iff by auto
    moreover have " \<tau>3[bv3::=b']\<^sub>\<tau>\<^sub>b[x3::=v]\<^sub>\<tau>\<^sub>v = \<tau>1'[bv1::=b']\<^sub>\<tau>\<^sub>b[x1::=v]\<^sub>\<tau>\<^sub>v" using fun_poly_ret_unique ** check_letI by metis
    moreover have "s3[bv3::=b']\<^sub>s\<^sub>b[x3::=v]\<^sub>s\<^sub>v = (s1'[bv1::=b']\<^sub>s\<^sub>b[x1::=v]\<^sub>s\<^sub>v)" using subst_v_flip_eq_two subst_v_s_def  fun_poly_body_unique ** check_letI by metis
    ultimately show ?thesis using s_branch_s_branch_list.eq_iff by metis
  qed

  ultimately show ?case using check_letI by auto
qed(auto+)

lemma check_s_plus:
  assumes "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> LET x = (AE_op Plus (V_lit (L_num n1)) (V_lit (L_num n2))) IN s'  \<Leftarrow> \<tau>" 
  shows   "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> LET x = (AE_val (V_lit (L_num (n1+n2)))) IN s' \<Leftarrow> \<tau>"   
proof  -
  obtain t1 where 1: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AE_op Plus (V_lit (L_num n1)) (V_lit (L_num n2)) \<Rightarrow> t1"
    using assms check_s_elims by metis
  then obtain z1 where 2: "t1 =  \<lbrace> z1 : B_int  | CE_val (V_var z1)  ==  CE_op Plus  ([V_lit (L_num n1)]\<^sup>c\<^sup>e) ([V_lit (L_num n2)]\<^sup>c\<^sup>e)  \<rbrace>"
    using infer_e_plus by metis

  obtain z2 where 3: \<open>\<Theta> ; \<Phi> ;  {||} ; GNil ; \<Delta>  \<turnstile> AE_val (V_lit (L_num (n1+n2))) \<Rightarrow> \<lbrace> z2 : B_int  | CE_val (V_var z2)  ==  CE_val (V_lit (L_num (n1+n2))) \<rbrace>\<close> 
    using infer_v_form infer_e_valI infer_v_litI   infer_l.intros infer_e_wf 1 
    by (simp add: fresh_GNil)

  let ?e = " (AE_op Plus (V_lit (L_num n1)) (V_lit (L_num n2)))"

  show ?thesis proof(rule  subtype_let)
    show "\<Theta> ; \<Phi> ; {||} ; GNil ; \<Delta>  \<turnstile> LET x = ?e IN s' \<Leftarrow> \<tau>" using assms by auto
    show "\<Theta> ; \<Phi> ; {||} ; GNil ; \<Delta>  \<turnstile> ?e \<Rightarrow> t1" using 1 by auto
    show "\<Theta> ; \<Phi> ; {||} ; GNil ; \<Delta>  \<turnstile> [ [ L_num (n1 + n2) ]\<^sup>v ]\<^sup>e \<Rightarrow> \<lbrace> z2 : B_int  | CE_val (V_var z2)  ==  CE_val (V_lit (L_num (n1+n2))) \<rbrace>" using 3 by auto
    show "\<Theta> ; {||} ; GNil  \<turnstile>  \<lbrace> z2 : B_int  | CE_val (V_var z2)  ==  CE_val (V_lit (L_num (n1+n2))) \<rbrace>  \<lesssim> t1" using subtype_bop_arith 
      by (metis "1" \<open>\<And>thesis. (\<And>z1. t1 = \<lbrace> z1 : B_int | [ [ z1 ]\<^sup>v ]\<^sup>c\<^sup>e == [ plus [ [ L_num n1 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ L_num n2 ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e \<rbrace> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> infer_e_wf(2) opp.distinct(1) type_for_lit.simps(3))
  qed

qed

lemma check_s_leq:
  assumes "\<Theta> ; \<Phi> ;  {||} ; GNil ; \<Delta>  \<turnstile> LET x = (AE_op LEq (V_lit (L_num n1)) (V_lit (L_num n2))) IN s'  \<Leftarrow> \<tau>" 
  shows "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> LET x = (AE_val (V_lit (if (n1 \<le> n2) then L_true else L_false))) IN s' \<Leftarrow> \<tau>"   
proof -
  obtain t1 where 1: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AE_op LEq (V_lit (L_num n1)) (V_lit (L_num n2)) \<Rightarrow> t1"
    using assms check_s_elims by metis
  then obtain z1 where 2: "t1 =  \<lbrace> z1 : B_bool  | CE_val (V_var z1)  ==  CE_op LEq  ([V_lit (L_num n1)]\<^sup>c\<^sup>e) ([V_lit (L_num n2)]\<^sup>c\<^sup>e)  \<rbrace>"
    using infer_e_leq by auto

  obtain z2 where 3: \<open>\<Theta> ; \<Phi> ;  {||} ; GNil ; \<Delta>  \<turnstile> AE_val (V_lit ((if (n1 \<le> n2) then L_true else L_false))) \<Rightarrow> \<lbrace> z2 : B_bool  | CE_val (V_var z2)  ==  CE_val (V_lit ((if (n1 \<le> n2) then L_true else L_false))) \<rbrace>\<close> 
    using infer_v_form infer_e_valI infer_v_litI   infer_l.intros infer_e_wf 1 
      fresh_GNil 
    by simp

  show ?thesis proof(rule subtype_let)
    show \<open> \<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (AE_op LEq [ L_num n1 ]\<^sup>v [ L_num n2 ]\<^sup>v) s' \<Leftarrow> \<tau>\<close> using assms by auto
    show \<open>\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AE_op LEq [ L_num n1 ]\<^sup>v [ L_num n2 ]\<^sup>v \<Rightarrow> t1\<close> using 1 by auto
    show \<open>\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> [ [ if n1 \<le> n2 then L_true else L_false ]\<^sup>v ]\<^sup>e \<Rightarrow> \<lbrace> z2 : B_bool  | CE_val (V_var z2)  ==  CE_val (V_lit ((if (n1 \<le> n2) then L_true else L_false))) \<rbrace>\<close> using 3 by auto
    show \<open>\<Theta> ; {||} ; GNil  \<turnstile> \<lbrace> z2 : B_bool  | CE_val (V_var z2)  ==  CE_val (V_lit ((if (n1 \<le> n2) then L_true else L_false))) \<rbrace> \<lesssim> t1\<close> 
      using subtype_bop_arith[where opp=LEq] check_s_wf assms 2  
      by (metis opp.distinct(1) subtype_bop_arith type_l_eq)
  qed
qed

lemma check_s_eq:
  assumes "\<Theta> ; \<Phi> ;  {||} ; GNil ; \<Delta>  \<turnstile> LET x = (AE_op Eq (V_lit (n1)) (V_lit ( n2))) IN s'  \<Leftarrow> \<tau>" 
  shows "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> LET x = (AE_val (V_lit (if (n1 = n2) then L_true else L_false))) IN s' \<Leftarrow> \<tau>"   
proof -
  obtain t1 where 1: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AE_op Eq (V_lit (n1)) (V_lit (n2)) \<Rightarrow> t1"
    using assms check_s_elims by metis
  then obtain z1 where 2: "t1 =  \<lbrace> z1 : B_bool  | CE_val (V_var z1)  ==  CE_op Eq  ([V_lit (n1)]\<^sup>c\<^sup>e) ([V_lit (n2)]\<^sup>c\<^sup>e)  \<rbrace>"
    using infer_e_leq by auto

  obtain z2 where 3: \<open>\<Theta> ; \<Phi> ;  {||} ; GNil ; \<Delta>  \<turnstile> AE_val (V_lit ((if (n1 = n2) then L_true else L_false))) \<Rightarrow> \<lbrace> z2 : B_bool  | CE_val (V_var z2)  ==  CE_val (V_lit ((if (n1 = n2) then L_true else L_false))) \<rbrace>\<close> 
    using infer_v_form infer_e_valI infer_v_litI   infer_l.intros infer_e_wf 1 
      fresh_GNil 
    by simp

  show ?thesis proof(rule subtype_let)
    show \<open> \<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (AE_op Eq [  n1 ]\<^sup>v [  n2 ]\<^sup>v) s' \<Leftarrow> \<tau>\<close> using assms by auto
    show \<open>\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AE_op Eq [  n1 ]\<^sup>v [  n2 ]\<^sup>v \<Rightarrow> t1\<close> using 1 by auto
    show \<open>\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> [ [ if n1 = n2 then L_true else L_false ]\<^sup>v ]\<^sup>e \<Rightarrow> \<lbrace> z2 : B_bool  | CE_val (V_var z2)  ==  CE_val (V_lit ((if (n1 = n2) then L_true else L_false))) \<rbrace>\<close> using 3 by auto
    show \<open>\<Theta> ; {||} ; GNil  \<turnstile> \<lbrace> z2 : B_bool  | CE_val (V_var z2)  ==  CE_val (V_lit ((if (n1 = n2) then L_true else L_false))) \<rbrace> \<lesssim> t1\<close> 
    proof -
      have " \<lbrace> z2 : B_bool  | [ [ z2 ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ eq [ [ n1 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ n2 ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  \<rbrace> = t1" using 2 
        by (metis \<tau>_fresh_c fresh_opp_all infer_l_form2 infer_l_fresh ms_fresh_all(31) ms_fresh_all(33) obtain_fresh_z type_e_eq type_l_eq)
      moreover have "\<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f GNil" using assms wfX_wfY by fastforce
      moreover have "base_for_lit n1 = base_for_lit n2" using 1 infer_e_wf wfE_elims(12) wfV_elims 
        by metis
      ultimately show ?thesis using subtype_bop_eq[OF \<open>\<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f GNil\<close>, of n1 n2 z2] by auto     
    qed
  qed
qed

subsection \<open>Operators\<close>

lemma preservation_plus:
  assumes "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , LET x = (AE_op Plus (V_lit (L_num n1)) (V_lit (L_num n2))) IN s' \<rangle> \<Leftarrow> \<tau>"        
  shows "\<Theta>; \<Phi>; \<Delta>  \<turnstile> \<langle> \<delta> , LET x =  (AE_val (V_lit (L_num (n1+n2)))) IN s' \<rangle> \<Leftarrow> \<tau>"
proof -

  have tt: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (AE_op Plus (V_lit (L_num n1)) (V_lit (L_num n2))) s' \<Leftarrow> \<tau>" and dsim: "\<Theta> \<turnstile> \<delta> \<sim> \<Delta>" and fd:"(\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)"
    using assms config_type_elims by blast+

  hence "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>AS_let x (AE_val (V_lit  (L_num (n1+n2)))) s' \<Leftarrow> \<tau>" using check_s_plus assms by auto  

  hence "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , AS_let x (AE_val (V_lit ( (L_num (n1+n2))))) s' \<rangle> \<Leftarrow> \<tau>" using dsim config_typeI fd by presburger
  then show ?thesis using dsim config_typeI 
    by (meson order_refl)
qed

lemma preservation_leq:
  assumes "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , AS_let x (AE_op LEq (V_lit (L_num n1)) (V_lit (L_num n2))) s' \<rangle> \<Leftarrow> \<tau>"        
  shows "\<Theta>; \<Phi>; \<Delta>  \<turnstile> \<langle> \<delta> , AS_let x (AE_val (V_lit (((if (n1 \<le> n2) then L_true else L_false))))) s' \<rangle> \<Leftarrow> \<tau>"
proof -

  have tt: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (AE_op LEq (V_lit (L_num n1)) (V_lit (L_num n2))) s' \<Leftarrow> \<tau>" and dsim: "\<Theta> \<turnstile> \<delta> \<sim> \<Delta>" and fd:"(\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)"
    using assms config_type_elims by blast+

  hence "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>AS_let x (AE_val (V_lit  ( ((if (n1 \<le> n2) then L_true else L_false))))) s' \<Leftarrow> \<tau>" using check_s_leq assms by auto  

  hence "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , AS_let x (AE_val (V_lit ( (((if (n1 \<le> n2) then L_true else L_false)))))) s' \<rangle> \<Leftarrow> \<tau>" using dsim config_typeI fd by presburger
  then show ?thesis using dsim config_typeI 
    by (meson order_refl)
qed

lemma preservation_eq:
  assumes "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , AS_let x (AE_op Eq (V_lit (n1)) (V_lit (n2))) s' \<rangle> \<Leftarrow> \<tau>"        
  shows "\<Theta>; \<Phi>; \<Delta>  \<turnstile> \<langle> \<delta> , AS_let x (AE_val (V_lit (((if (n1 = n2) then L_true else L_false))))) s' \<rangle> \<Leftarrow> \<tau>"
proof -

  have tt: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (AE_op Eq (V_lit (n1)) (V_lit (n2))) s' \<Leftarrow> \<tau>" and dsim: "\<Theta> \<turnstile> \<delta> \<sim> \<Delta>" and fd:"(\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)"
    using assms config_type_elims by blast+

  hence "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>AS_let x (AE_val (V_lit  ( ((if (n1 = n2) then L_true else L_false))))) s' \<Leftarrow> \<tau>" using check_s_eq assms by auto  

  hence "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , AS_let x (AE_val (V_lit ( (((if (n1 = n2) then L_true else L_false)))))) s' \<rangle> \<Leftarrow> \<tau>" using dsim config_typeI fd by presburger
  then show ?thesis using dsim config_typeI 
    by (meson order_refl)
qed

subsection \<open>Let Statements\<close>

lemma subst_s_abs_lst:
  fixes s::s and sa::s and v'::v
  assumes "[[atom x]]lst. s = [[atom xa]]lst. sa" and "atom xa \<sharp> v \<and> atom x \<sharp> v"
  shows "s[x::=v]\<^sub>s\<^sub>v = sa[xa::=v]\<^sub>s\<^sub>v"
proof -
  obtain c'::x where cdash: "atom c' \<sharp> (v, x, xa, s, sa)" using obtain_fresh by blast    
  moreover have " (x \<leftrightarrow> c') \<bullet> s = (xa \<leftrightarrow> c') \<bullet> sa" proof -
    have "atom c' \<sharp> (s, sa) \<and> atom c' \<sharp> (x, xa, s, sa)" using cdash by auto
    thus ?thesis using assms by auto
  qed
  ultimately show ?thesis using assms 
    using subst_sv_flip by auto 
qed

lemma check_let_val: 
  fixes v::v and s::s
  shows "\<Theta> ; \<Phi> ; B ; G ; \<Delta>  \<turnstile> ss \<Leftarrow> \<tau> \<Longrightarrow>  B = {||} \<Longrightarrow> G = GNil \<Longrightarrow> 
        ss = AS_let x (AE_val v) s \<or>  ss = AS_let2 x t (AS_val v) s \<Longrightarrow>  \<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> (s[x::=v]\<^sub>s\<^sub>v) \<Leftarrow> \<tau>" and
    "check_branch_s \<Theta> \<Phi> \<B> GNil \<Delta> tid dc const v cs \<tau> \<Longrightarrow> True" and 
    "check_branch_list \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist v css \<tau> \<Longrightarrow> True"
proof(nominal_induct \<tau> and \<tau> and \<tau>  avoiding: v rule: check_s_check_branch_s_check_branch_list.strong_induct)
  case (check_letI x1 \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e \<tau> z s1 b c)
  hence *:"e = AE_val v" by auto
  let ?G = "(x1, b, c[z::=V_var x1]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma>"
  have "\<Theta> ; \<Phi> ; \<B> ;  ?G[x1::=v]\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x1::=v]\<^sub>\<Delta>\<^sub>v  \<turnstile> s1[x1::=v]\<^sub>s\<^sub>v \<Leftarrow> \<tau>[x1::=v]\<^sub>\<tau>\<^sub>v" 
  proof(rule subst_infer_check_s(1))
    show **:\<open> \<Theta> ; \<B> ; \<Gamma> \<turnstile> v \<Rightarrow>  \<lbrace> z : b  | c \<rbrace>\<close> using infer_e_elims check_letI * by fast
    thus \<open>\<Theta> ; \<B> ; \<Gamma>  \<turnstile>  \<lbrace> z : b  | c \<rbrace> \<lesssim> \<lbrace> z : b  | c \<rbrace>\<close> using subtype_reflI  infer_v_wf by metis
    show \<open>atom z \<sharp> (x1, v)\<close> using check_letI fresh_Pair by auto
    show \<open>\<Theta> ; \<Phi> ; \<B> ; (x1, b, c[z::=V_var x1]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma> ; \<Delta>  \<turnstile> s1 \<Leftarrow> \<tau>\<close> using check_letI subst_defs by auto
    show "(x1, b, c[z::=V_var x1]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma> = GNil @ (x1, b, c[z::=V_var x1]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma>" by auto
  qed

  hence "\<Theta> ; \<Phi> ; \<B> ;  \<Gamma> ; \<Delta>  \<turnstile> s1[x1::=v]\<^sub>s\<^sub>v \<Leftarrow> \<tau>"  using check_letI by auto
  moreover have " s1[x1::=v]\<^sub>s\<^sub>v =  s[x::=v]\<^sub>s\<^sub>v" 
    by (metis (full_types) check_letI fresh_GNil infer_e_elims(7) s_branch_s_branch_list.distinct s_branch_s_branch_list.eq_iff(2) 
        subst_s_abs_lst wfG_x_fresh_in_v_simple)

  ultimately show ?case using check_letI by simp
next
  case (check_let2I x1 \<Theta> \<Phi> \<B> \<Gamma> \<Delta> t s1 \<tau> s2 )

  hence s1eq:"s1 = AS_val v" by auto
  let ?G = "(x1, b_of t, c_of t x1) #\<^sub>\<Gamma> \<Gamma>"
  obtain z::x where *:"atom z \<sharp> (x1 , v,t)"  using obtain_fresh_z by metis
  hence teq:"t =  \<lbrace> z : b_of t | c_of t z \<rbrace>" using b_of_c_of_eq by auto
  have "\<Theta> ; \<Phi> ; \<B> ;  ?G[x1::=v]\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x1::=v]\<^sub>\<Delta>\<^sub>v  \<turnstile> s2[x1::=v]\<^sub>s\<^sub>v \<Leftarrow> \<tau>[x1::=v]\<^sub>\<tau>\<^sub>v" 
  proof(rule subst_check_check_s(1))
    obtain t' where "\<Theta> ; \<B> ; \<Gamma> \<turnstile> v \<Rightarrow> t' \<and>  \<Theta> ; \<B> ; \<Gamma> \<turnstile> t' \<lesssim> t" using  check_s_elims(1) check_let2I(10) s1eq by auto
    thus  **:\<open> \<Theta> ; \<B> ; \<Gamma> \<turnstile> v \<Leftarrow> \<lbrace> z : b_of t | c_of t z \<rbrace>\<close> using  check_v.intros teq by auto
    show "atom z \<sharp> (x1, v)" using * by auto
    show \<open>  \<Theta> ; \<Phi> ; \<B> ; (x1, b_of t, c_of t x1) #\<^sub>\<Gamma> \<Gamma> ; \<Delta>  \<turnstile> s2 \<Leftarrow> \<tau>\<close> using check_let2I by auto
    show "(x1, b_of t , c_of t x1) #\<^sub>\<Gamma> \<Gamma> = GNil @ (x1, b_of t, (c_of t z)[z::=V_var x1]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma>" using append_g.simps c_of_switch * fresh_prodN by metis
  qed

  hence "\<Theta> ; \<Phi> ; \<B> ;  \<Gamma> ; \<Delta>  \<turnstile> s2[x1::=v]\<^sub>s\<^sub>v \<Leftarrow> \<tau>"  using check_let2I by auto
  moreover have " s2[x1::=v]\<^sub>s\<^sub>v =  s[x::=v]\<^sub>s\<^sub>v" using
      check_let2I fresh_GNil check_s_elims s_branch_s_branch_list.distinct s_branch_s_branch_list.eq_iff
      subst_s_abs_lst wfG_x_fresh_in_v_simple
  proof -
    have "AS_let2 x t (AS_val v) s = AS_let2 x1 t s1 s2"
      by (metis check_let2I.prems(3) s_branch_s_branch_list.distinct s_branch_s_branch_list.eq_iff(3)) (* 62 ms *)
    then show ?thesis
      by (metis (no_types) check_let2I check_let2I.prems(2) check_s_elims(1) fresh_GNil s_branch_s_branch_list.eq_iff(3) subst_s_abs_lst wfG_x_fresh_in_v_simple) (* 375 ms *)
  qed

  ultimately show ?case using check_let2I by simp
qed(auto+)

lemma preservation_let_val:
  assumes "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , AS_let x (AE_val v) s \<rangle> \<Leftarrow> \<tau> \<or> \<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , AS_let2 x t (AS_val v) s \<rangle> \<Leftarrow> \<tau>" (is "?A \<or> ?B")
  shows " \<exists>\<Delta>'. \<Theta>; \<Phi>; \<Delta>'  \<turnstile> \<langle> \<delta> , s[x::=v]\<^sub>s\<^sub>v \<rangle> \<Leftarrow> \<tau>  \<and> \<Delta> \<sqsubseteq> \<Delta>'"
proof -
  have tt:  "\<Theta> \<turnstile> \<delta> \<sim> \<Delta>" and fd: "(\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)"
    using assms by blast+

  have  "?A \<or> ?B" using assms by auto
  then have "\<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile>  s[x::=v]\<^sub>s\<^sub>v   \<Leftarrow> \<tau>"
  proof
    assume "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , AS_let x (AE_val v) s \<rangle> \<Leftarrow> \<tau>"
    hence * : " \<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile>  AS_let x (AE_val v) s  \<Leftarrow> \<tau>" by blast
    thus ?thesis using check_let_val by simp
  next
    assume "\<Theta>; \<Phi>; \<Delta>  \<turnstile> \<langle> \<delta> , AS_let2 x t (AS_val v) s \<rangle> \<Leftarrow> \<tau>"
    hence * : "\<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile>  AS_let2 x t (AS_val v) s  \<Leftarrow> \<tau>" by blast
    thus ?thesis using check_let_val by simp
  qed

  thus  ?thesis using tt config_typeI fd
      order_refl by metis
qed

lemma check_s_fst_snd:
  assumes "fst_snd = AE_fst \<and> v=v1 \<or> fst_snd = AE_snd \<and> v=v2" 
    and   "\<Theta>; \<Phi>; {||}; GNil; \<Delta> \<turnstile> AS_let x (fst_snd (V_pair v1 v2)) s' \<Leftarrow> \<tau>"
  shows "\<Theta>; \<Phi>; {||}; GNil; \<Delta> \<turnstile> AS_let x ( AE_val v) s' \<Leftarrow> \<tau>"
proof -
  have  1: \<open> \<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (fst_snd (V_pair v1 v2)) s' \<Leftarrow> \<tau>\<close> using assms by auto

  then obtain t1 where 2:"\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  (fst_snd (V_pair v1 v2)) \<Rightarrow> t1" using check_s_elims by auto

  show ?thesis using subtype_let 1 2 assms 
    by (meson infer_e_fst_pair infer_e_snd_pair)
qed

lemma preservation_fst_snd:
  assumes "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , LET x = (fst_snd (V_pair v1 v2)) IN s' \<rangle> \<Leftarrow> \<tau>" and 
    "fst_snd = AE_fst \<and> v=v1 \<or> fst_snd = AE_snd \<and> v=v2"
  shows "\<exists>\<Delta>'. \<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , LET x = (AE_val v) IN s' \<rangle> \<Leftarrow> \<tau>  \<and> \<Delta> \<sqsubseteq> \<Delta>'"
proof - 
  have  tt: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (fst_snd (V_pair v1 v2)) s' \<Leftarrow> \<tau> \<and> \<Theta> \<turnstile> \<delta> \<sim> \<Delta>" using assms by blast
  hence t2: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (fst_snd (V_pair v1 v2)) s' \<Leftarrow> \<tau>" by auto

  moreover have "\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd" using assms config_type_elims by auto
  ultimately show ?thesis using config_typeI order_refl tt assms check_s_fst_snd by metis
qed

inductive_cases check_branch_s_elims2[elim!]:
  "\<Theta> ; \<Phi> ;  \<B> ; \<Gamma> ; \<Delta>; tid ; cons ; const ; v \<turnstile> cs \<Leftarrow> \<tau>"

lemmas freshers = freshers atom_dom.simps toSet.simps fresh_def x_not_in_b_set
declare freshers [simp]

lemma subtype_eq_if:
  fixes t::\<tau> and va::v
  assumes "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f  \<lbrace> z : b_of t  | c_of t z \<rbrace>" and "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b_of t  | c  IMP c_of t z \<rbrace> "
  shows   "\<Theta> ; \<B> ; \<Gamma> \<turnstile> \<lbrace> z : b_of t  | c_of t z \<rbrace>  \<lesssim> \<lbrace> z : b_of t  | c  IMP c_of t z \<rbrace> "
proof -
  obtain x::x where xf:"atom x \<sharp> ((\<Theta>, \<B>, \<Gamma>, z, c_of t z, z, c  IMP  c_of t z ),c)" using obtain_fresh by metis

  moreover have "\<Theta> ; \<B> ; (x, b_of t, (c_of t z)[z::=[ x ]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> (c  IMP  c_of t z )[z::=[ x ]\<^sup>v]\<^sub>c\<^sub>v " 
    unfolding subst_cv.simps 
  proof(rule valid_eq_imp)

    have "\<Theta> ; \<B> ; (x, b_of t, (c_of t z)[z::=[ x ]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f (c  IMP  (c_of t z))[z::=[ x ]\<^sup>v]\<^sub>v    " 
      apply(rule  wfT_wfC_cons)
      apply(simp add: assms, simp add: assms, unfold fresh_prodN )
      using  xf fresh_prodN by metis+     
    thus "\<Theta> ; \<B> ; (x, b_of t, (c_of t z)[z::=[ x ]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c[z::=[ x ]\<^sup>v]\<^sub>c\<^sub>v  IMP  (c_of t z)[z::=[ x ]\<^sup>v]\<^sub>c\<^sub>v " 
      using subst_cv.simps subst_defs by auto
  qed

  ultimately show ?thesis using subtype_baseI assms fresh_Pair subst_defs by metis
qed

lemma subtype_eq_if_\<tau>:
  fixes t::\<tau> and va::v
  assumes "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f  t" and "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b_of t  | c  IMP c_of t z \<rbrace> " and "atom z \<sharp> t"
  shows   "\<Theta> ; \<B> ; \<Gamma> \<turnstile> t  \<lesssim> \<lbrace> z : b_of t  | c  IMP c_of t z \<rbrace> "
proof -
  have "t = \<lbrace> z : b_of t | c_of t z \<rbrace>" using b_of_c_of_eq assms by auto
  thus ?thesis  using subtype_eq_if assms  c_of.simps b_of.simps by metis
qed

lemma valid_conj:
  assumes  "\<Theta> ; \<B> ; \<Gamma> \<Turnstile> c1" and "\<Theta> ; \<B> ; \<Gamma> \<Turnstile> c2" 
  shows "\<Theta> ; \<B> ; \<Gamma> \<Turnstile> c1 AND c2" 
proof
  show \<open> \<Theta> ; \<B> ; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c1  AND  c2  \<close> using valid.simps wfC_conjI assms by auto
  show \<open>\<forall>i.  \<Theta> ; \<Gamma> \<turnstile> i \<and>  i \<Turnstile> \<Gamma>  \<longrightarrow>  i \<Turnstile> c1  AND  c2  \<close> 
  proof(rule+)
    fix i
    assume *:"\<Theta> ; \<Gamma> \<turnstile> i \<and> i \<Turnstile> \<Gamma> " 
    thus "i \<lbrakk> c1 \<rbrakk> ~ True" using assms valid.simps 
      using is_satis.cases by blast
    show "i \<lbrakk> c2 \<rbrakk> ~ True" using assms valid.simps 
      using is_satis.cases * by blast  
  qed
qed

subsection \<open>Other Statements\<close>

lemma check_if:
  fixes s'::s and cs::branch_s and css::branch_list and v::v
  shows    "\<Theta>; \<Phi>; B; G; \<Delta> \<turnstile>  s' \<Leftarrow> \<tau> \<Longrightarrow> s' =  IF (V_lit ll) THEN s1 ELSE s2 \<Longrightarrow>  
        \<Theta> ; {||} ; GNil  \<turnstile>\<^sub>w\<^sub>f \<tau> \<Longrightarrow> G = GNil \<Longrightarrow> B = {||} \<Longrightarrow> ll = L_true \<and> s = s1 \<or> ll = L_false \<and> s = s2 \<Longrightarrow> 
        \<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  s \<Leftarrow> \<tau>" and
    "check_branch_s \<Theta> \<Phi>  {||} GNil \<Delta> tid dc const v cs \<tau> \<Longrightarrow> True" and 
    "check_branch_list \<Theta> \<Phi>  {||} \<Gamma> \<Delta> tid dclist v css \<tau> \<Longrightarrow> True"
proof(nominal_induct \<tau> and \<tau> and \<tau>  rule: check_s_check_branch_s_check_branch_list.strong_induct)
  case (check_ifI z \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v s1 s2 \<tau>)
  obtain z' where teq: "\<tau> = \<lbrace> z' : b_of \<tau> | c_of \<tau> z' \<rbrace> \<and> atom z' \<sharp> (z,\<tau>)" using obtain_fresh_z_c_of by metis
  hence ceq: "(c_of \<tau> z')[z'::=[ z ]\<^sup>v]\<^sub>c\<^sub>v = (c_of \<tau> z)" using c_of_switch fresh_Pair by metis
  have zf: " atom z \<sharp> c_of \<tau> z'"
    using c_of_fresh check_ifI teq fresh_Pair fresh_at_base by metis
  hence 1:"\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> s \<Leftarrow>  \<lbrace> z : b_of \<tau>  | CE_val (V_lit ll)  ==  CE_val (V_lit ll)  IMP  c_of \<tau> z  \<rbrace>" using check_ifI by auto
  moreover have 2:"\<Theta> ; {||} ; GNil \<turnstile> (\<lbrace> z : b_of \<tau>  | CE_val (V_lit ll)  ==  CE_val (V_lit ll)  IMP  c_of \<tau> z  \<rbrace>) \<lesssim>  \<tau>" 
  proof - 
    have "\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f (\<lbrace> z : b_of \<tau>  | CE_val (V_lit ll )  ==  CE_val (V_lit ll)   IMP c_of \<tau> z  \<rbrace>)" using check_ifI check_s_wf by auto
    moreover have "\<Theta> ; {||} ; GNil  \<turnstile>\<^sub>w\<^sub>f \<tau>" using  check_s_wf check_ifI by auto
    ultimately show ?thesis using subtype_if_simp[of \<Theta> " {||}" z "b_of \<tau>" ll "c_of \<tau> z'" z'] using teq ceq zf subst_defs by metis
  qed
  ultimately show ?case  using check_s_supertype(1) check_ifI by metis
qed(auto+)

lemma preservation_if: 
  assumes  "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , IF (V_lit ll) THEN s1 ELSE s2 \<rangle> \<Leftarrow> \<tau>" and 
    "ll = L_true \<and> s = s1 \<or> ll = L_false \<and> s = s2"
  shows "\<Theta>; \<Phi>; \<Delta>  \<turnstile> \<langle>\<delta>, s\<rangle> \<Leftarrow> \<tau>  \<and> setD \<Delta> \<subseteq> setD \<Delta>"
proof -
  have *: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  AS_if (V_lit ll) s1 s2 \<Leftarrow> \<tau> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" 
    using assms config_type_elims by metis
  hence "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  s \<Leftarrow> \<tau>" using check_s_wf check_if assms by metis
  hence "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle>\<delta>, s\<rangle> \<Leftarrow> \<tau>  \<and> setD \<Delta> \<subseteq> setD \<Delta>" using config_typeI * 
    using assms(1) by blast
  thus ?thesis by blast
qed

lemma wfT_conj:
  assumes "\<Theta> ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c1 \<rbrace>" and  "\<Theta> ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c2 \<rbrace>"
  shows  "\<Theta> ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c1 AND c2\<rbrace>"
proof
  show \<open>atom z \<sharp> (\<Theta>, \<B>, GNil)\<close>
    apply(unfold fresh_prodN, intro conjI) 
    using wfTh_fresh wfT_wf assms apply metis
    using fresh_GNil x_not_in_b_set fresh_def by metis+   
  show \<open> \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f b \<close> using wfT_elims assms by metis
  have "\<Theta> ; \<B> ; (z, b, TRUE) #\<^sub>\<Gamma> GNil   \<turnstile>\<^sub>w\<^sub>f c1" using wfT_wfC fresh_GNil assms by auto
  moreover have "\<Theta> ; \<B> ; (z, b, TRUE) #\<^sub>\<Gamma> GNil   \<turnstile>\<^sub>w\<^sub>f c2" using wfT_wfC fresh_GNil assms by auto
  ultimately show \<open> \<Theta> ; \<B> ; (z, b, TRUE) #\<^sub>\<Gamma> GNil   \<turnstile>\<^sub>w\<^sub>f c1  AND  c2  \<close> using wfC_conjI by auto
qed

lemma subtype_conj:
  assumes    "\<Theta> ; \<B> ; GNil  \<turnstile> t \<lesssim> \<lbrace> z : b | c1 \<rbrace>" and   "\<Theta> ; \<B> ; GNil  \<turnstile> t \<lesssim> \<lbrace> z : b | c2 \<rbrace>" 
  shows   "\<Theta> ; \<B> ; GNil  \<turnstile> \<lbrace> z : b | c_of t z \<rbrace>  \<lesssim> \<lbrace> z : b | c1 AND c2 \<rbrace>" 
proof -
  have beq: "b_of t = b" using subtype_eq_base2 b_of.simps assms by metis
  obtain x::x where x:\<open>atom x \<sharp> (\<Theta>, \<B>, GNil, z, c_of t z, z, c1  AND  c2 )\<close> using obtain_fresh by metis
  thus ?thesis proof
    have "atom z \<sharp> t" using subtype_wf wfT_supp fresh_def x_not_in_b_set atom_dom.simps toSet.simps assms dom.simps by fastforce
    hence t:"t = \<lbrace> z : b_of t  | c_of t z \<rbrace>" using b_of_c_of_eq by auto
    thus  \<open> \<Theta> ; \<B> ; GNil   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b  | c_of t z \<rbrace> \<close> using subtype_wf beq assms by auto

    show \<open>\<Theta> ; \<B> ; (x, b, (c_of t z)[z::=[ x ]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma> GNil  \<Turnstile> (c1  AND  c2 )[z::=[ x ]\<^sup>v]\<^sub>v \<close>      
    proof -
      have \<open>\<Theta> ; \<B> ; (x, b, (c_of t z)[z::=[ x ]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma> GNil  \<Turnstile> c1[z::=[ x ]\<^sup>v]\<^sub>v \<close>
      proof(rule subtype_valid)
        show \<open>\<Theta> ; \<B> ; GNil  \<turnstile> t \<lesssim> \<lbrace> z : b | c1 \<rbrace>\<close> using assms by auto
        show \<open>atom x \<sharp> GNil\<close> using fresh_GNil by auto
        show \<open>t = \<lbrace> z : b  | c_of t z \<rbrace>\<close> using t beq by auto
        show \<open>\<lbrace> z : b  | c1 \<rbrace> = \<lbrace> z : b  | c1 \<rbrace>\<close> by auto
      qed
      moreover have \<open>\<Theta> ; \<B> ; (x, b, (c_of t z)[z::=[ x ]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma> GNil  \<Turnstile> c2[z::=[ x ]\<^sup>v]\<^sub>v \<close>
      proof(rule subtype_valid)
        show \<open>\<Theta> ; \<B> ; GNil  \<turnstile> t \<lesssim> \<lbrace> z : b | c2 \<rbrace>\<close> using assms by auto
        show \<open>atom x \<sharp> GNil\<close> using fresh_GNil by auto
        show \<open>t = \<lbrace> z : b  | c_of t z \<rbrace>\<close> using t beq by auto
        show \<open>\<lbrace> z : b  | c2 \<rbrace> = \<lbrace> z : b  | c2 \<rbrace>\<close> by auto
      qed
      ultimately show ?thesis unfolding subst_cv.simps subst_v_c_def  using valid_conj by metis
    qed
    thus \<open> \<Theta> ; \<B> ; GNil   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b  | c1  AND  c2  \<rbrace> \<close> using subtype_wf wfT_conj assms by auto
  qed
qed

lemma infer_v_conj:
  assumes "\<Theta> ; \<B> ; GNil  \<turnstile> v \<Leftarrow> \<lbrace> z : b | c1 \<rbrace>" and "\<Theta> ; \<B> ; GNil  \<turnstile> v \<Leftarrow> \<lbrace> z : b | c2 \<rbrace>"
  shows "\<Theta> ; \<B> ; GNil  \<turnstile> v \<Leftarrow> \<lbrace> z : b | c1 AND c2 \<rbrace>" 
proof -
  obtain t1 where t1: "\<Theta> ; \<B> ; GNil  \<turnstile> v \<Rightarrow> t1 \<and> \<Theta> ; \<B> ; GNil \<turnstile> t1 \<lesssim> \<lbrace> z : b | c1 \<rbrace>" 
    using assms check_v_elims by metis
  obtain t2 where t2: "\<Theta> ; \<B> ; GNil  \<turnstile> v \<Rightarrow> t2 \<and> \<Theta> ; \<B> ; GNil \<turnstile> t2 \<lesssim> \<lbrace> z : b | c2 \<rbrace>" 
    using assms check_v_elims by metis
  have teq: "t1 = \<lbrace> z : b | c_of t1 z \<rbrace>" using subtype_eq_base2 b_of.simps 
    by (metis (full_types) b_of_c_of_eq fresh_GNil infer_v_t_wf t1 wfT_x_fresh)
  have "t1 = t2" using infer_v_uniqueness t1 t2 by auto
  hence " \<Theta> ; \<B> ; GNil \<turnstile> \<lbrace> z : b | c_of t1 z \<rbrace> \<lesssim> \<lbrace> z : b | c1 AND c2 \<rbrace>" using subtype_conj t1 t2 by simp
  hence " \<Theta> ; \<B> ; GNil \<turnstile> t1 \<lesssim> \<lbrace> z : b | c1 AND c2 \<rbrace>" using teq by auto
  thus ?thesis using t1 using check_v.intros by auto
qed

lemma wfG_conj:
  fixes c1::c
  assumes  "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f (x, b, c1 AND c2) #\<^sub>\<Gamma> \<Gamma>"
  shows "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f (x, b, c1) #\<^sub>\<Gamma> \<Gamma>"
proof(cases "c1 \<in> {TRUE, FALSE}")
  case True
  then show ?thesis using assms wfG_cons2I  wfG_elims wfX_wfY by metis
next
  case False
  then show ?thesis using assms wfG_cons1I  wfG_elims wfX_wfY wfC_elims 
    by (metis wfG_elim2)
qed

lemma check_match:
  fixes s'::s and s::s and css::branch_list and cs::branch_s
  shows "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>  s \<Leftarrow> \<tau> \<Longrightarrow> True" and
    "\<Theta> ; \<Phi> ; B ; G ; \<Delta> ; tid ; dc ; const  ;  vcons \<turnstile>  cs \<Leftarrow>  \<tau> \<Longrightarrow> 
             vcons = V_cons tid dc v \<Longrightarrow> B =  {||} \<Longrightarrow> G = GNil \<Longrightarrow> cs =  (dc x' \<Rightarrow> s') \<Longrightarrow>  
             \<Theta> ; {||} ; GNil \<turnstile> v \<Leftarrow> const \<Longrightarrow> 
             \<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> s'[x'::=v]\<^sub>s\<^sub>v \<Leftarrow> \<tau>" and
    "\<Theta> ; \<Phi> ; B ; G ; \<Delta> ; tid ; dclist ; vcons  \<turnstile> css \<Leftarrow> \<tau> \<Longrightarrow> distinct (map fst dclist) \<Longrightarrow>
             vcons = V_cons tid dc v \<Longrightarrow> B =  {||} \<Longrightarrow> (dc, const) \<in> set dclist \<Longrightarrow> G = GNil \<Longrightarrow> 
             Some (AS_branch dc x' s') = lookup_branch dc css \<Longrightarrow> \<Theta> ; {||} ; GNil \<turnstile> v \<Leftarrow> const \<Longrightarrow> 
             \<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> s'[x'::=v]\<^sub>s\<^sub>v \<Leftarrow> \<tau>"
proof(nominal_induct \<tau> and \<tau> and \<tau> avoiding: x' v  rule: check_s_check_branch_s_check_branch_list.strong_induct)
  case (check_branch_list_consI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid consa consta va cs \<tau> dclist cssa)

  then obtain xa and sa where cseq:"cs = AS_branch consa xa sa" using check_branch_s_elims2[OF check_branch_list_consI(1)] by metis

  show ?case proof(cases "dc = consa")
    case True
    hence "cs = AS_branch consa x' s'" using check_branch_list_consI cseq 
      by (metis lookup_branch.simps(2) option.inject)
    moreover have "const = consta" using check_branch_list_consI distinct.simps 
      by (metis True dclist_distinct_unique list.set_intros(1))
    moreover have "va = V_cons tid consa v" using check_branch_list_consI True by auto
    ultimately  show ?thesis using check_branch_list_consI  by auto
  next
    case False
    hence "Some (AS_branch dc x' s') = lookup_branch dc cssa" using lookup_branch.simps(2) check_branch_list_consI(10) cseq by auto
    moreover have "(dc, const) \<in> set dclist" using check_branch_list_consI False by simp
    ultimately show ?thesis using check_branch_list_consI by auto
  qed

next
  case (check_branch_list_finalI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid cons const va cs \<tau>)
  hence " cs = AS_branch cons x' s'" using lookup.simps check_branch_list_finalI lookup_branch.simps option.inject 
    by (metis map_of.simps(1) map_of_Cons_code(2) option.distinct(1) s_branch_s_branch_list.exhaust(2) weak_map_of_SomeI)
  then show ?case using check_branch_list_finalI by auto
next
  case (check_branch_s_branchI \<Theta> \<B> \<Gamma> \<Delta> \<tau> const x \<Phi> tid cons va s)

  text \<open>Supporting facts here to make the main body of the proof concise\<close>
  have xf:"atom x \<sharp> \<tau>" proof -
    have "supp \<tau> \<subseteq> supp  \<B>" using wf_supp(4) check_branch_s_branchI  atom_dom.simps toSet.simps dom.simps by fastforce
    thus ?thesis using fresh_def x_not_in_b_set by blast
  qed

  hence "\<tau>[x::=v]\<^sub>\<tau>\<^sub>v = \<tau>" using forget_subst_v subst_v_\<tau>_def by auto
  have "\<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v = \<Delta>" using forget_subst_dv  wfD_x_fresh fresh_GNil check_branch_s_branchI by metis

  have "supp v = {}" using check_branch_s_branchI check_v_wf wfV_supp_nil by metis
  hence "supp va = {}" using \<open> va = V_cons tid cons v\<close> v.supp pure_supp by auto

  let ?G = "(x, b_of const, [ va ]\<^sup>c\<^sup>e  ==  [ V_cons tid cons [ x ]\<^sup>v ]\<^sup>c\<^sup>e   AND c_of const x ) #\<^sub>\<Gamma> \<Gamma>"
  obtain z::x where z: "const = \<lbrace> z : b_of const | c_of const z \<rbrace> \<and> atom z \<sharp> (x', v,x,const,va)" 
    using obtain_fresh_z_c_of by metis

  have  vt: \<open>\<Theta> ; \<B> ; GNil  \<turnstile> v \<Leftarrow> \<lbrace> z : b_of const  | [ va ]\<^sup>c\<^sup>e  ==  [ V_cons tid cons [ z ]\<^sup>v ]\<^sup>c\<^sup>e  AND c_of const z \<rbrace>\<close>
  proof(rule infer_v_conj)
    obtain t' where t: "\<Theta> ; \<B> ; GNil  \<turnstile> v \<Rightarrow> t' \<and> \<Theta> ; \<B> ; GNil \<turnstile> t' \<lesssim> const" 
      using check_v_elims check_branch_s_branchI by metis
    show "\<Theta> ; \<B> ; GNil  \<turnstile> v \<Leftarrow> \<lbrace> z : b_of const  | [ va ]\<^sup>c\<^sup>e  ==  [ V_cons tid cons [ z ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace>"        
    proof(rule check_v_top)

      show "\<Theta> ; \<B> ; GNil   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b_of const  | [ va ]\<^sup>c\<^sup>e  ==  [ V_cons tid cons [ z ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace> "     

      proof(rule wfG_wfT)
        show \<open> \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f (x, b_of const, ([ va ]\<^sup>c\<^sup>e  ==  [ V_cons tid cons [ z ]\<^sup>v ]\<^sup>c\<^sup>e    )[z::=[ x ]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> GNil \<close>
        proof -
          have 1: "va[z::=[ x ]\<^sup>v]\<^sub>v\<^sub>v  = va" using  forget_subst_v subst_v_v_def  z fresh_prodN by metis
          moreover have 2: "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f (x, b_of const, [ va ]\<^sup>c\<^sup>e  ==  [ V_cons tid cons [ x ]\<^sup>v ]\<^sup>c\<^sup>e   AND  c_of const x ) #\<^sub>\<Gamma> GNil  "
            using    check_branch_s_branchI(17)[THEN check_s_wf] \<open>\<Gamma> = GNil\<close> by auto      
          moreover hence "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f (x, b_of const, [ va ]\<^sup>c\<^sup>e  ==  [ V_cons tid cons [ x ]\<^sup>v ]\<^sup>c\<^sup>e ) #\<^sub>\<Gamma> GNil" 
            using wfG_conj by metis
          ultimately show ?thesis
            unfolding subst_cv.simps subst_cev.simps subst_vv.simps by auto
        qed      
        show \<open>atom x \<sharp> ([ va ]\<^sup>c\<^sup>e  ==  [ V_cons tid cons [ z ]\<^sup>v ]\<^sup>c\<^sup>e   )\<close> unfolding c.fresh ce.fresh v.fresh
          apply(intro conjI )        
          using  check_branch_s_branchI fresh_at_base z freshers apply simp
          using  check_branch_s_branchI fresh_at_base z freshers apply simp
          using pure_supp apply force
          using z fresh_x_neq fresh_prod5 by metis        
      qed
      show \<open>[ va ]\<^sup>c\<^sup>e = [ V_cons tid cons [ z ]\<^sup>v ]\<^sup>c\<^sup>e[z::=v]\<^sub>c\<^sub>e\<^sub>v\<close> 
        using \<open> va = V_cons tid cons v\<close> subst_cev.simps subst_vv.simps by auto
      show \<open> \<Theta> ; \<B> ; GNil \<turnstile> v \<Leftarrow> const \<close> using check_branch_s_branchI by auto
      show "supp [ va ]\<^sup>c\<^sup>e \<subseteq> supp \<B>" using \<open>supp va = {}\<close> ce.supp by simp
    qed
    show "\<Theta> ; \<B> ; GNil  \<turnstile> v \<Leftarrow> \<lbrace> z : b_of const  | c_of const z \<rbrace>" 
      using check_branch_s_branchI z by auto
  qed

  text \<open>Main body of proof for this case\<close>
  have "\<Theta> ; \<Phi> ; \<B> ; (?G)[x::=v]\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v  \<turnstile> s[x::=v]\<^sub>s\<^sub>v \<Leftarrow> \<tau>[x::=v]\<^sub>\<tau>\<^sub>v"
  proof(rule subst_check_check_s)
    show \<open>\<Theta> ; \<B> ; GNil  \<turnstile> v \<Leftarrow> \<lbrace> z : b_of const  | [ va ]\<^sup>c\<^sup>e  ==  [ V_cons tid cons [ z ]\<^sup>v ]\<^sup>c\<^sup>e   AND c_of const z \<rbrace>\<close> using vt by auto
    show \<open>atom z \<sharp> (x, v)\<close> using z fresh_prodN by auto
    show \<open> \<Theta> ; \<Phi> ; \<B> ; ?G ; \<Delta>  \<turnstile> s \<Leftarrow> \<tau>\<close> 
      using check_branch_s_branchI by auto

    show \<open> ?G = GNil @ (x, b_of const, ([ va ]\<^sup>c\<^sup>e  ==  [ V_cons tid cons [ z ]\<^sup>v ]\<^sup>c\<^sup>e   AND c_of const z)[z::=[ x ]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> GNil\<close>      
    proof -
      have "va[z::=[ x ]\<^sup>v]\<^sub>v\<^sub>v  = va" using  forget_subst_v subst_v_v_def  z fresh_prodN by metis
      moreover have  "(c_of const z)[z::=[ x ]\<^sup>v]\<^sub>c\<^sub>v = c_of const x" 
        using  c_of_switch[of z const x]  z fresh_prodN by metis
      ultimately show ?thesis
        unfolding subst_cv.simps subst_cev.simps subst_vv.simps append_g.simps         
        using c_of_switch[of z const x]  z fresh_prodN z fresh_prodN  check_branch_s_branchI by argo
    qed
  qed
  moreover have "s[x::=v]\<^sub>s\<^sub>v = s'[x'::=v]\<^sub>s\<^sub>v" 
    using check_branch_s_branchI subst_v_flip_eq_two subst_v_s_def s_branch_s_branch_list.eq_iff by metis
  ultimately show  ?case using  check_branch_s_branchI \<open>\<tau>[x::=v]\<^sub>\<tau>\<^sub>v = \<tau>\<close> \<open>\<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v = \<Delta>\<close> by auto
qed(auto+)

text \<open>Lemmas for while reduction. Making these separate lemmas allows flexibility in wiring them into the main proof and robustness
if we change it\<close>

lemma check_unit:
  fixes \<tau>::\<tau> and \<Phi>::\<Phi> and \<Delta>::\<Delta> and G::\<Gamma>
  assumes "\<Theta> ; {||} ; GNil  \<turnstile> \<lbrace> z : B_unit  | TRUE \<rbrace> \<lesssim> \<tau>'" and "\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f \<Delta>"  and "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>"  and "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f G"
  shows \<open> \<Theta> ; \<Phi> ; {||} ; G ; \<Delta>  \<turnstile> [[ L_unit ]\<^sup>v]\<^sup>s \<Leftarrow> \<tau>'\<close>
proof - 
  have *:"\<Theta> ; {||} ; GNil  \<turnstile> [L_unit]\<^sup>v \<Rightarrow> \<lbrace> z : B_unit  | [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_unit ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace>" 
    using infer_l.intros(4) infer_v_litI fresh_GNil assms  wfX_wfY   by (meson subtype_g_wf)
  moreover have "\<Theta> ; {||} ; GNil  \<turnstile> \<lbrace> z : B_unit  | [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_unit ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace> \<lesssim> \<tau>'" 
    using subtype_top subtype_trans * infer_v_wf 
    by (meson assms(1))
  ultimately show ?thesis (*apply(rule check_valI, auto simp add: assms,rule * )*)
    using subtype_top subtype_trans fresh_GNil assms check_valI assms check_s_g_weakening assms toSet.simps 
    by (metis bot.extremum infer_v_g_weakening subtype_weakening wfD_wf)
qed

lemma preservation_var:
  shows "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> VAR u : \<tau>' = v IN s \<Leftarrow> \<tau> \<Longrightarrow> \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<Longrightarrow> atom u \<sharp> \<delta> \<Longrightarrow> atom u \<sharp> \<Delta> \<Longrightarrow>
         \<Theta>; \<Phi>; {||}; GNil; (u,\<tau>')#\<^sub>\<Delta>\<Delta>  \<turnstile> s \<Leftarrow> \<tau> \<and> \<Theta> \<turnstile> (u,v)#\<delta> \<sim> (u,\<tau>')#\<^sub>\<Delta>\<Delta>"
    and
    "check_branch_s \<Theta> \<Phi>  {||} GNil \<Delta> tid dc const v cs \<tau> \<Longrightarrow> True" and 
    "check_branch_list \<Theta> \<Phi>  {||} \<Gamma> \<Delta> tid dclist v css \<tau> \<Longrightarrow> True"
proof(nominal_induct  "{||}::bv fset" GNil \<Delta> "VAR u : \<tau>' = v IN s" \<tau> and \<tau> and \<tau>  rule: check_s_check_branch_s_check_branch_list.strong_induct)
  case (check_varI u' \<Theta> \<Phi> \<Delta> \<tau> s')
  hence "\<Theta>; \<Phi>; {||}; GNil; (u, \<tau>') #\<^sub>\<Delta> \<Delta>  \<turnstile> s \<Leftarrow> \<tau>" using check_s_abs_u check_v_wf by metis

  moreover have "\<Theta> \<turnstile> ((u,v)#\<delta>) \<sim> ((u,\<tau>')#\<^sub>\<Delta>\<Delta>)" proof
    show \<open>\<Theta>  \<turnstile> \<delta> \<sim> \<Delta> \<close> using check_varI by auto
    show \<open>\<Theta> ; {||} ; GNil  \<turnstile> v \<Leftarrow> \<tau>'\<close> using check_varI by auto
    show \<open>u \<notin> fst ` set \<delta>\<close> using check_varI fresh_d_fst_d by auto
  qed

  ultimately show ?case by simp
qed(auto+)

lemma check_while:
  shows "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> WHILE s1 DO { s2 }  \<Leftarrow> \<tau> \<Longrightarrow> atom x \<sharp> (s1, s2) \<Longrightarrow>  atom z' \<sharp> x \<Longrightarrow>
       \<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> LET x : (\<lbrace> z' : B_bool  | TRUE \<rbrace>) = s1 IN (IF (V_var x) THEN (s2 ;; (WHILE s1 DO {s2}))  
            ELSE ([ V_lit L_unit]\<^sup>s))  \<Leftarrow> \<tau>" and
    "check_branch_s \<Theta> \<Phi>  {||} GNil \<Delta> tid dc const v cs \<tau> \<Longrightarrow> True" and 
    "check_branch_list \<Theta> \<Phi>  {||} \<Gamma> \<Delta> tid dclist v css \<tau> \<Longrightarrow> True"
proof(nominal_induct  "{||}::bv fset" GNil \<Delta> "AS_while s1 s2" \<tau> and \<tau> and \<tau>  avoiding: s1 s2 x z' rule: check_s_check_branch_s_check_branch_list.strong_induct)
  case (check_whileI \<Theta> \<Phi> \<Delta> s1 z s2 \<tau>')
  have teq:"\<lbrace> z' : B_bool  | TRUE \<rbrace> = \<lbrace> z : B_bool  | TRUE \<rbrace>" using \<tau>.eq_iff by auto

  show ?case proof
    have " atom x \<sharp> \<tau>' " using wfT_nil_supp fresh_def subtype_wfT check_whileI(5) by fast
    moreover have "atom x \<sharp> \<lbrace> z' : B_bool  | TRUE \<rbrace> " using \<tau>.fresh c.fresh b.fresh by metis  
    ultimately show \<open>atom x \<sharp> (\<Theta>, \<Phi>,  {||}, GNil, \<Delta>, \<lbrace> z' : B_bool  | TRUE \<rbrace>, s1, \<tau>')\<close>
      apply(unfold fresh_prodN)  
      using check_whileI  wb_x_fresh check_s_wf wfD_x_fresh fresh_empty_fset fresh_GNil fresh_Pair \<open>atom x \<sharp> \<tau>'\<close>  by metis

    show \<open> \<Theta> ; \<Phi> ;  {||} ; GNil ; \<Delta>  \<turnstile> s1 \<Leftarrow> \<lbrace> z' : B_bool  | TRUE \<rbrace>\<close> using check_whileI  teq by metis

    let ?G =  "(x, b_of \<lbrace> z' : B_bool  | TRUE \<rbrace>, c_of \<lbrace> z' : B_bool  | TRUE \<rbrace> x) #\<^sub>\<Gamma> GNil"

    have cof:"(c_of \<lbrace> z' : B_bool  | TRUE \<rbrace> x) = C_true" using c_of.simps check_whileI subst_cv.simps by metis
    have  wfg: "\<Theta> ;  {||} \<turnstile>\<^sub>w\<^sub>f ?G" proof 
      show "c_of \<lbrace> z' : B_bool  | TRUE \<rbrace> x \<in> {TRUE, FALSE}" using subst_cv.simps cof by auto
      show "\<Theta> ;  {||} \<turnstile>\<^sub>w\<^sub>f GNil " using wfG_nilI check_whileI wfX_wfY check_s_wf by metis
      show "atom x \<sharp> GNil" using fresh_GNil by auto
      show "\<Theta> ;  {||} \<turnstile>\<^sub>w\<^sub>f b_of \<lbrace> z' : B_bool  | TRUE \<rbrace>  " using wfB_boolI wfX_wfY check_s_wf b_of.simps 
        by (metis \<open>\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f GNil\<close>)
    qed

    obtain zz::x where zf:\<open>atom zz \<sharp> ((\<Theta>, \<Phi>, {||}::bv fset, ?G , \<Delta>, [ x ]\<^sup>v, 
                                  AS_seq s2 (AS_while s1 s2), AS_val [ L_unit ]\<^sup>v, \<tau>'),x,?G)\<close>
      using obtain_fresh by blast
    show \<open> \<Theta> ; \<Phi> ;  {||} ; ?G ; \<Delta>  \<turnstile> 
                   AS_if [ x ]\<^sup>v (AS_seq s2 (AS_while s1 s2)) (AS_val [ L_unit ]\<^sup>v) \<Leftarrow> \<tau>'\<close> 
    proof      
      show "atom zz \<sharp> (\<Theta>, \<Phi>, {||}::bv fset, ?G , \<Delta>, [ x ]\<^sup>v, AS_seq s2 (AS_while s1 s2), AS_val [ L_unit ]\<^sup>v, \<tau>')" using zf by auto
      show \<open>\<Theta> ; {||} ; ?G  \<turnstile> [ x ]\<^sup>v \<Leftarrow> \<lbrace> zz : B_bool  | TRUE \<rbrace>\<close> proof
        have "atom zz \<sharp> x \<and> atom zz \<sharp> (\<Theta>,  {||}::bv fset, ?G)" using zf fresh_prodN by metis
        thus \<open> \<Theta> ; {||} ; ?G  \<turnstile> [ x ]\<^sup>v \<Rightarrow>\<lbrace> zz : B_bool |  [[zz]\<^sup>v]\<^sup>c\<^sup>e == [[ x ]\<^sup>v]\<^sup>c\<^sup>e  \<rbrace>\<close> 
          using infer_v_varI lookup.simps wfg b_of.simps by metis
        thus  \<open>\<Theta> ; {||} ; ?G  \<turnstile> \<lbrace> zz : B_bool |  [[ zz ]\<^sup>v]\<^sup>c\<^sup>e == [[ x ]\<^sup>v]\<^sup>c\<^sup>e \<rbrace>  \<lesssim> \<lbrace> zz : B_bool  | TRUE \<rbrace>\<close>
          using subtype_top infer_v_wf by metis
      qed 
      show \<open> \<Theta> ; \<Phi> ; {||} ; ?G ; \<Delta>  \<turnstile> AS_seq s2 (AS_while s1 s2) \<Leftarrow> \<lbrace> zz : b_of \<tau>'  | [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e   IMP  c_of \<tau>' zz  \<rbrace>\<close> 
      proof 
        have "\<lbrace> zz : B_unit  | TRUE \<rbrace> = \<lbrace> z : B_unit  | TRUE \<rbrace>" using \<tau>.eq_iff by auto 
        thus \<open> \<Theta> ; \<Phi> ; {||} ; ?G ; \<Delta>  \<turnstile> s2 \<Leftarrow> \<lbrace> zz : B_unit  | TRUE \<rbrace>\<close> using check_s_g_weakening(1) [OF check_whileI(3) _ wfg] toSet.simps 
          by (simp add: \<open>\<lbrace> zz : B_unit | TRUE \<rbrace> = \<lbrace> z : B_unit | TRUE \<rbrace>\<close>)

        show \<open> \<Theta> ; \<Phi> ; {||} ; ?G ; \<Delta>  \<turnstile> AS_while s1 s2 \<Leftarrow> \<lbrace> zz : b_of \<tau>'  | [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e   IMP  c_of \<tau>' zz  \<rbrace>\<close>
        proof(rule check_s_supertype(1))
          have \<open> \<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_while s1 s2 \<Leftarrow> \<tau>'\<close> using  check_whileI by auto
          thus *:\<open> \<Theta> ; \<Phi> ; {||} ; ?G ; \<Delta>  \<turnstile> AS_while s1 s2 \<Leftarrow> \<tau>' \<close> using  check_s_g_weakening(1)[OF _ _ wfg] toSet.simps by auto

          show \<open>\<Theta> ; {||} ; ?G  \<turnstile> \<tau>'  \<lesssim> \<lbrace> zz : b_of \<tau>'  | [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e   IMP  c_of \<tau>' zz  \<rbrace>\<close> 
          proof(rule subtype_eq_if_\<tau>)
            show \<open> \<Theta> ; {||} ; ?G \<turnstile>\<^sub>w\<^sub>f \<tau>' \<close> using * check_s_wf by auto
            show \<open> \<Theta> ; {||} ; ?G  \<turnstile>\<^sub>w\<^sub>f \<lbrace> zz : b_of \<tau>'  | [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e   IMP  c_of \<tau>' zz  \<rbrace> \<close>
              apply(rule wfT_eq_imp, simp add: base_for_lit.simps)
              using subtype_wf check_whileI wfg zf fresh_prodN by metis+
            show \<open>atom zz \<sharp> \<tau>'\<close> using  zf fresh_prodN by metis
          qed
        qed

      qed
      show \<open> \<Theta> ; \<Phi> ; {||} ; ?G ; \<Delta>  \<turnstile> AS_val [ L_unit ]\<^sup>v \<Leftarrow> \<lbrace> zz : b_of \<tau>'  | [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_false ]\<^sup>v ]\<^sup>c\<^sup>e   IMP  c_of \<tau>' zz  \<rbrace>\<close>
      proof(rule check_s_supertype(1))

        show *:\<open> \<Theta> ; \<Phi> ; {||} ; ?G ; \<Delta>  \<turnstile> AS_val [ L_unit ]\<^sup>v \<Leftarrow> \<tau>'\<close> 
          using check_unit[OF check_whileI(5) _ _ wfg] using check_whileI wfg wfX_wfY check_s_wf by metis
        show \<open>\<Theta> ; {||} ; ?G  \<turnstile> \<tau>' \<lesssim> \<lbrace> zz : b_of \<tau>'  | [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_false ]\<^sup>v ]\<^sup>c\<^sup>e   IMP  c_of \<tau>' zz  \<rbrace>\<close> 
        proof(rule subtype_eq_if_\<tau>)
          show \<open> \<Theta> ; {||} ; ?G \<turnstile>\<^sub>w\<^sub>f \<tau>' \<close> using * check_s_wf by metis
          show \<open> \<Theta> ; {||} ; ?G  \<turnstile>\<^sub>w\<^sub>f \<lbrace> zz : b_of \<tau>'  | [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_false ]\<^sup>v ]\<^sup>c\<^sup>e   IMP  c_of \<tau>' zz  \<rbrace> \<close>                          
            apply(rule wfT_eq_imp, simp add: base_for_lit.simps)
            using subtype_wf check_whileI wfg zf fresh_prodN by metis+
          show \<open>atom zz \<sharp> \<tau>'\<close> using  zf fresh_prodN by metis
        qed
      qed
    qed
  qed
qed(auto+)

lemma check_s_narrow:
  fixes s::s and x::x
  assumes "atom x \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>, c, \<tau>, s)" and "\<Theta> ; \<Phi> ; \<B> ; (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma> ; \<Delta>  \<turnstile> s \<Leftarrow> \<tau>" and    
    "\<Theta> ; \<B> ; \<Gamma>  \<Turnstile> c "
  shows "\<Theta> ; \<Phi> ; \<B> ;  \<Gamma> ; \<Delta>  \<turnstile> s \<Leftarrow> \<tau>"
proof -
  let ?B = "({||}::bv fset)"
  let ?v = "V_lit L_true"

  obtain z::x where z: "atom z \<sharp> (x, [ L_true ]\<^sup>v,c)" using obtain_fresh by metis

  have "atom z \<sharp> c" using z fresh_prodN by auto
  hence c:"  c[x::=[ z ]\<^sup>v]\<^sub>v[z::=[ x ]\<^sup>v]\<^sub>c\<^sub>v = c" using  subst_v_c_def by simp

  have "\<Theta> ; \<Phi> ; \<B> ; ((x,B_bool, c) #\<^sub>\<Gamma> \<Gamma>)[x::=?v]\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=?v]\<^sub>\<Delta>\<^sub>v   \<turnstile>  s[x::=?v]\<^sub>s\<^sub>v   \<Leftarrow> \<tau>[x::=?v]\<^sub>\<tau>\<^sub>v" proof(rule  subst_infer_check_s(1) )
    show vt: \<open> \<Theta> ; \<B> ; \<Gamma>  \<turnstile> [ L_true ]\<^sup>v \<Rightarrow> \<lbrace> z : B_bool | (CE_val (V_var z)) == (CE_val (V_lit  L_true )) \<rbrace>   \<close> 
      using infer_v_litI check_s_wf wfG_elims(2) infer_trueI assms by metis     
    show \<open>\<Theta> ; \<B> ; \<Gamma>  \<turnstile> \<lbrace> z : B_bool | (CE_val (V_var z)) == (CE_val (V_lit  L_true )) \<rbrace> \<lesssim> \<lbrace> z : B_bool  | c[x::=[ z ]\<^sup>v]\<^sub>v \<rbrace>\<close> proof
      show \<open>atom x \<sharp> (\<Theta>, \<B>, \<Gamma>, z, [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e , z, c[x::=[ z ]\<^sup>v]\<^sub>v)\<close> 
        apply(unfold fresh_prodN, intro conjI) 
        prefer 5
        using c.fresh ce.fresh v.fresh z fresh_prodN apply auto[1]
        prefer 6
        using fresh_subst_v_if[of "atom x" c x] assms fresh_prodN apply simp
        using z assms fresh_prodN apply metis
        using z  assms fresh_prodN apply metis
        using z assms  fresh_prodN apply metis
        using z fresh_prodN assms fresh_at_base by metis+
      show \<open> \<Theta> ; \<B> ; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : B_bool  | [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace> \<close> using vt infer_v_wf by simp
      show \<open> \<Theta> ; \<B> ; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : B_bool  | c[x::=[ z ]\<^sup>v]\<^sub>v \<rbrace> \<close> proof(rule wfG_wfT)    
        show \<open> \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f (x, B_bool, c[x::=[ z ]\<^sup>v]\<^sub>v[z::=[ x ]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma> \<close> using c check_s_wf assms by metis
        have " atom x \<sharp> [ z ]\<^sup>v" using v.fresh z fresh_at_base by auto
        thus  \<open>atom x \<sharp> c[x::=[ z ]\<^sup>v]\<^sub>v\<close> using fresh_subst_v_if[of "atom x" c ] by auto
      qed
      have wfg: "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f(x, B_bool, ([ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e )[z::=[ x ]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>" 
        using wfT_wfG vt infer_v_wf fresh_prodN assms by simp
      show  \<open>\<Theta> ; \<B> ; (x, B_bool, ([ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e )[z::=[ x ]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> c[x::=[ z ]\<^sup>v]\<^sub>v[z::=[ x ]\<^sup>v]\<^sub>v \<close> 
        using c valid_weakening[OF assms(3) _ wfg ] toSet.simps 
        using subst_v_c_def by auto
    qed
    show \<open>atom z \<sharp> (x, [ L_true ]\<^sup>v)\<close> using z fresh_prodN by metis
    show \<open> \<Theta> ; \<Phi> ; \<B> ; (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma> ; \<Delta>  \<turnstile> s \<Leftarrow> \<tau>\<close> using assms by auto

    thus \<open>(x, B_bool, c) #\<^sub>\<Gamma> \<Gamma> = GNil @ (x, B_bool, c[x::=[ z ]\<^sup>v]\<^sub>v[z::=[ x ]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma>\<close> using append_g.simps c by auto
  qed

  moreover have "((x,B_bool, c) #\<^sub>\<Gamma> \<Gamma>)[x::=?v]\<^sub>\<Gamma>\<^sub>v = \<Gamma> " using subst_gv.simps by auto
  ultimately show ?thesis using assms forget_subst_dv forget_subst_sv forget_subst_tv fresh_prodN  by metis
qed

lemma check_assert_s:
  fixes s::s and x::x
  assumes "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  AS_assert c s  \<Leftarrow> \<tau>"
  shows "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  s  \<Leftarrow> \<tau> \<and> \<Theta> ; {||} ; GNil  \<Turnstile> c "
proof -
  let ?B = "({||}::bv fset)"
  let ?v = "V_lit L_true"

  obtain x where x: "\<Theta> ; \<Phi> ; ?B ; (x,B_bool, c) #\<^sub>\<Gamma> GNil ; \<Delta>  \<turnstile>  s  \<Leftarrow> \<tau> \<and> atom x \<sharp> (\<Theta>, \<Phi>, ?B, GNil, \<Delta>, c, \<tau>, s ) \<and> \<Theta> ; ?B ; GNil \<Turnstile> c " 
    using check_s_elims(10)[OF \<open>\<Theta> ; \<Phi> ; ?B ; GNil ; \<Delta>  \<turnstile>  AS_assert c s   \<Leftarrow> \<tau>\<close>] valid.simps by metis

  show ?thesis using assms check_s_narrow x by metis
qed

lemma infer_v_pair2I:
  "atom z \<sharp> (v1, v2) \<Longrightarrow>
   atom z \<sharp> (\<Theta>, \<B>, \<Gamma>) \<Longrightarrow>
   \<Theta> ; \<B> ; \<Gamma> \<turnstile> v1 \<Rightarrow> t1 \<Longrightarrow>
   \<Theta> ; \<B> ; \<Gamma> \<turnstile> v2 \<Rightarrow> t2 \<Longrightarrow>
   b1 = b_of t1 \<Longrightarrow> b2 = b_of t2 \<Longrightarrow> 
  \<Theta> ; \<B> ; \<Gamma> \<turnstile> [ v1 , v2 ]\<^sup>v \<Rightarrow> \<lbrace> z : [ b1 , b2 ]\<^sup>b  | [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ v1 , v2 ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace>"
  using infer_v_pairI by simp

subsection \<open>Main Lemma\<close>

lemma preservation: 
  assumes "\<Phi> \<turnstile> \<langle>\<delta>, s\<rangle> \<longrightarrow> \<langle>\<delta>', s'\<rangle>" and "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle>\<delta>, s\<rangle> \<Leftarrow> \<tau>"
  shows "\<exists>\<Delta>'. \<Theta>; \<Phi>; \<Delta>' \<turnstile> \<langle>\<delta>', s'\<rangle> \<Leftarrow> \<tau> \<and> \<Delta> \<sqsubseteq> \<Delta>'" 
  using assms 
proof(induct arbitrary: \<tau> rule: reduce_stmt.induct)
  case (reduce_let_plusI \<delta> x n1 n2 s')
  then show ?case using preservation_plus
    by (metis order_refl)  
next
  case (reduce_let_leqI b n1 n2 \<delta> x s) 
  then show ?case using preservation_leq  by (metis order_refl)  
next
  case (reduce_let_eqI b n1 n2 \<Phi> \<delta> x s)
  then show ?case using preservation_eq[OF reduce_let_eqI(2)] order_refl by metis
next
  case (reduce_let_appI f z b c \<tau>' s' \<Phi> \<delta> x v s)
  hence tt: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (AE_app f v) s \<Leftarrow> \<tau> \<and> \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" using config_type_elims[OF reduce_let_appI(2)] by metis 
  hence *:"\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (AE_app f v) s \<Leftarrow> \<tau>" by auto

  hence  "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let2 x   (\<tau>'[z::=v]\<^sub>\<tau>\<^sub>v) (s'[z::=v]\<^sub>s\<^sub>v) s \<Leftarrow> \<tau>" 
    using preservation_app reduce_let_appI tt by auto

  hence "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , AS_let2 x (\<tau>'[z::=v]\<^sub>\<tau>\<^sub>v) s'[z::=v]\<^sub>s\<^sub>v s \<rangle> \<Leftarrow> \<tau>"  using  config_typeI tt by auto
  then show ?case using tt order_refl reduce_let_appI by metis

next
  case (reduce_let_appPI f bv z b c \<tau>' s' \<Phi> \<delta> x b' v s)

  hence tt: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (AE_appP f b' v) s \<Leftarrow> \<tau> \<and> \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" using config_type_elims[OF reduce_let_appPI(2)] by metis 
  hence *:"\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (AE_appP f b' v) s \<Leftarrow> \<tau>" by auto

  have  "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let2 x   (\<tau>'[bv::=b']\<^sub>\<tau>\<^sub>b[z::=v]\<^sub>\<tau>\<^sub>v) (s'[bv::=b']\<^sub>s\<^sub>b[z::=v]\<^sub>s\<^sub>v) s \<Leftarrow> \<tau>" 
  proof(rule preservation_poly_app) 
    show \<open>Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ z b c  \<tau>' s'))) = lookup_fun \<Phi> f\<close> using reduce_let_appPI by metis
    show \<open>\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd\<close> using tt lookup_fun_member by metis
    show \<open> \<Theta> ; \<Phi> ;{||} ; GNil ; \<Delta>  \<turnstile> AS_let x (AE_appP f b' v) s \<Leftarrow> \<tau>\<close> using * by auto
    show \<open> \<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f b' \<close> using check_s_elims infer_e_wf wfE_elims * by metis
  qed(auto+)

  hence "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , AS_let2 x (\<tau>'[bv::=b']\<^sub>\<tau>\<^sub>b[z::=v]\<^sub>\<tau>\<^sub>v) s'[bv::=b']\<^sub>s\<^sub>b[z::=v]\<^sub>s\<^sub>v s \<rangle> \<Leftarrow> \<tau>"  using  config_typeI tt by auto
  then show ?case using tt order_refl reduce_let_appI by metis

next
  case (reduce_if_trueI \<delta> s1 s2) 
  then show ?case using preservation_if by metis
next
  case (reduce_if_falseI uw \<delta> s1 s2)
  then show ?case using preservation_if by metis
next
  case (reduce_let_valI \<delta> x v s)
  then show ?case using preservation_let_val by presburger
next
  case (reduce_let_mvar u v \<delta> \<Phi>  x s)
  hence *:"\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (AE_mvar u) s \<Leftarrow> \<tau> \<and> \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" 
    using config_type_elims by blast

  hence **: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (AE_mvar u) s \<Leftarrow> \<tau>" by auto
  obtain xa::x and za::x and ca::c and ba::b and sa::s where
    sa1: "atom xa \<sharp> (\<Theta>, \<Phi>, {||}::bv fset, GNil, \<Delta>, AE_mvar u, \<tau>) \<and>  atom za \<sharp> (xa, \<Theta>, \<Phi>, {||}::bv fset, GNil, \<Delta>, AE_mvar u, \<tau>, sa) \<and>
     \<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> AE_mvar u \<Rightarrow> \<lbrace> za : ba  | ca \<rbrace> \<and>
     \<Theta> ; \<Phi> ; {||} ; (xa, ba, ca[za::=V_var xa]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> GNil ; \<Delta>   \<turnstile> sa \<Leftarrow> \<tau> \<and>
       (\<forall>c. atom c \<sharp> (s, sa) \<longrightarrow> atom c \<sharp> (x, xa, s, sa) \<longrightarrow> (x \<leftrightarrow> c) \<bullet> s = (xa \<leftrightarrow> c) \<bullet> sa)" 
    using check_s_elims(2)[OF **] subst_defs by metis

  have "\<Theta> ; {||} ; GNil \<turnstile> v \<Leftarrow>  \<lbrace> za : ba  | ca \<rbrace>" proof -
    have " (u , \<lbrace> za : ba  | ca \<rbrace>) \<in> setD \<Delta>" using infer_e_elims(11) sa1 by fast
    thus  ?thesis using delta_sim_v reduce_let_mvar config_type_elims check_s_wf  by metis
  qed

  then obtain \<tau>' where  vst: "\<Theta> ; {||} ; GNil \<turnstile> v \<Rightarrow> \<tau>' \<and>
        \<Theta> ; {||} ; GNil \<turnstile> \<tau>'  \<lesssim>  \<lbrace> za : ba  | ca \<rbrace>" using check_v_elims by blast

  obtain za2 and ba2 and ca2 where  zbc: "\<tau>' = (\<lbrace> za2 : ba2 | ca2 \<rbrace>) \<and> atom za2 \<sharp> (xa, (xa, \<Theta>, \<Phi>, {||}::bv fset, GNil, \<Delta>, AE_val v, \<tau>, sa))"
    using obtain_fresh_z by blast
  have beq: "ba=ba2" using subtype_eq_base vst zbc by blast

  moreover have xaf: "atom xa \<sharp> (za, za2)" 
    apply(unfold fresh_prodN, intro conjI)
    using sa1 zbc fresh_prodN fresh_x_neq by metis+

  have sat2: " \<Theta> ; \<Phi> ; {||} ; GNil@(xa, ba, ca2[za2::=V_var xa]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> GNil ; \<Delta>   \<turnstile> sa \<Leftarrow> \<tau>" proof(rule ctx_subtype_s)
    show "\<Theta> ; \<Phi> ; {||} ; GNil @ (xa, ba, ca[za::=V_var xa]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> GNil ; \<Delta>  \<turnstile> sa \<Leftarrow> \<tau>" using sa1 by auto
    show "\<Theta> ; {||} ; GNil  \<turnstile> \<lbrace> za2 : ba  | ca2 \<rbrace> \<lesssim> \<lbrace> za : ba  | ca \<rbrace>" using beq zbc vst by fast
    show "atom xa \<sharp> (za, za2, ca, ca2)" proof -
      have *:"\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f (\<lbrace> za2 : ba2 | ca2 \<rbrace>) " using zbc vst subtype_wf by auto
      hence "supp ca2 \<subseteq> { atom za2 }" using wfT_supp_c[OF *] supp_GNil by simp
      moreover have "atom za2 \<sharp> xa" using zbc fresh_Pair fresh_x_neq by metis
      ultimately have  "atom xa \<sharp> ca2" using zbc supp_at_base fresh_def 
        by (metis empty_iff singleton_iff subset_singletonD)
      moreover have "atom xa \<sharp> ca" proof -
        have *:"\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f (\<lbrace> za : ba | ca \<rbrace>) " using zbc vst subtype_wf by auto
        hence "supp ca \<subseteq> { atom za }" using wfT_supp \<tau>.supp by force
        moreover have "xa \<noteq> za"  using   fresh_def fresh_x_neq xaf fresh_Pair by metis
        ultimately show ?thesis using fresh_def by auto
      qed
      ultimately show ?thesis using xaf sa1 fresh_prod4 fresh_Pair by metis
    qed
  qed
  hence dwf: "\<Theta> ; {||} ; GNil  \<turnstile>\<^sub>w\<^sub>f \<Delta>" using sa1 infer_e_wf by meson

  have "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let xa (AE_val v) sa \<Leftarrow> \<tau>" proof 
    have "atom xa \<sharp> (AE_val v)" using infer_v_wf(1) wfV_supp fresh_def e.fresh x_not_in_b_set vst by fastforce
    thus  "atom xa \<sharp> (\<Theta>, \<Phi>, {||}::bv fset, GNil, \<Delta>, AE_val v, \<tau>)" using sa1 freshers by simp 
    have "atom za2 \<sharp> (AE_val v)" using infer_v_wf(1) wfV_supp fresh_def e.fresh x_not_in_b_set vst by fastforce
    thus "atom za2 \<sharp> (xa, \<Theta>, \<Phi>, {||}::bv fset, GNil, \<Delta>, AE_val v, \<tau>, sa)" using zbc freshers fresh_prodN by auto
    have " \<Theta>    \<turnstile>\<^sub>w\<^sub>f \<Phi>" using sa1 infer_e_wf by auto
    thus  "\<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> AE_val v \<Rightarrow> \<lbrace> za2 : ba  | ca2 \<rbrace>" 
      using zbc vst beq dwf infer_e_valI by blast
    show "\<Theta> ; \<Phi> ; {||} ; (xa, ba, ca2[za2::=V_var xa]\<^sub>v) #\<^sub>\<Gamma> GNil ; \<Delta>   \<turnstile> sa \<Leftarrow> \<tau>" using sat2 append_g.simps subst_defs by metis
  qed
  moreover have  "AS_let xa (AE_val v) sa =  AS_let x (AE_val v) s" proof -
    have "[[atom x]]lst. s = [[atom xa]]lst. sa" 
      using sa1 Abs1_eq_iff_all(3)[where z=" (s, sa)"] by metis
    thus ?thesis using s_branch_s_branch_list.eq_iff(2) by metis
  qed
  ultimately have "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let x (AE_val v) s \<Leftarrow> \<tau>"  by auto

  then show ?case using reduce_let_mvar * config_typeI
    by (meson order_refl)
next
  case (reduce_let2I \<Phi> \<delta> s1 \<delta>' s1'  x t s2)
  hence **: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> AS_let2 x t s1 s2  \<Leftarrow> \<tau>  \<and> \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" using config_type_elims[OF reduce_let2I(3)] by blast
  hence *:"\<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> AS_let2 x t s1 s2  \<Leftarrow> \<tau>" by auto

  obtain xa::x and  z::x and c and b and s2a::s where st: "atom xa \<sharp> (\<Theta>, \<Phi>, {||}::bv fset, GNil, \<Delta>, t, s1, \<tau>)  \<and>
       \<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> s1 \<Leftarrow> t \<and>
       \<Theta> ; \<Phi> ; {||} ; (xa, b_of t, c_of t xa) #\<^sub>\<Gamma> GNil ; \<Delta>   \<turnstile> s2a \<Leftarrow> \<tau> \<and>  ([[atom x]]lst. s2 = [[atom xa]]lst. s2a) "
    using check_s_elims(4)[OF *] Abs1_eq_iff_all(3) by metis

  hence "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , s1 \<rangle> \<Leftarrow> t"  using config_typeI ** by auto
  then obtain \<Delta>' where s1r: "\<Theta>; \<Phi>; \<Delta>' \<turnstile> \<langle> \<delta>' , s1' \<rangle> \<Leftarrow> t \<and> \<Delta> \<sqsubseteq> \<Delta>'" using reduce_let2I by presburger

  have  "\<Theta>; \<Phi>; {||}; GNil; \<Delta>'  \<turnstile> AS_let2 xa t s1' s2a  \<Leftarrow> \<tau>" 
  proof(rule check_let2I)
    show *:"\<Theta>; \<Phi>; {||}; GNil; \<Delta>'  \<turnstile> s1' \<Leftarrow> t" using config_type_elims st s1r by metis
    show  "atom xa \<sharp> (\<Theta>, \<Phi>, {||}::bv fset, GNil, \<Delta>',t, s1', \<tau>)" proof -  
      have "atom xa \<sharp> s1'" using  check_s_x_fresh *  by auto
      moreover have "atom xa \<sharp> \<Delta>'" using check_s_x_fresh * by auto
      ultimately show ?thesis  using st fresh_prodN by metis
    qed

    show "\<Theta> ; \<Phi> ; {||} ; (xa, b_of t, c_of t xa) #\<^sub>\<Gamma> GNil ; \<Delta>'  \<turnstile> s2a \<Leftarrow> \<tau>"  proof -
      have "\<Theta> ; {||} ; GNil  \<turnstile>\<^sub>w\<^sub>f \<Delta>'" using * check_s_wf by auto
      moreover have "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f ((xa, b_of t, c_of t xa) #\<^sub>\<Gamma> GNil)" using st check_s_wf by auto
      ultimately have "\<Theta> ; {||} ; ((xa, b_of t , c_of t xa) #\<^sub>\<Gamma> GNil)  \<turnstile>\<^sub>w\<^sub>f \<Delta>'" using wf_weakening by auto
      thus  ?thesis using check_s_d_weakening check_s_wf st  s1r by metis
    qed
  qed
  moreover have "AS_let2 xa t s1' s2a = AS_let2 x t s1' s2"  using st s_branch_s_branch_list.eq_iff by metis
  ultimately have "\<Theta>; \<Phi>; {||}; GNil; \<Delta>'  \<turnstile> AS_let2 x t s1' s2  \<Leftarrow> \<tau>" using st by argo
  moreover have "\<Theta> \<turnstile> \<delta>' \<sim> \<Delta>'" using config_type_elims s1r by fast
  ultimately show ?case using config_typeI **
    by (meson s1r)
next
  case (reduce_let2_valI vb \<delta> x t v s)
  then show ?case using preservation_let_val by meson
next
  case (reduce_varI u \<delta> \<Phi> \<tau>' v s)

  hence ** : "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_var u \<tau>' v s \<Leftarrow> \<tau> \<and> \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" 
    using config_type_elims by meson
  have uf: "atom u \<sharp> \<Delta>" using reduce_varI delta_sim_fresh by force  
  hence *: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_var u \<tau>' v s \<Leftarrow> \<tau>" and " \<Theta> \<turnstile> \<delta> \<sim> \<Delta>" using **  by auto

  thus ?case using preservation_var reduce_varI config_typeI ** set_subset_Cons
      setD_ConsD subsetI  by (metis delta_sim_fresh)

next
  case (reduce_assignI \<Phi> \<delta> u v )
  hence *: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_assign u v  \<Leftarrow> \<tau> \<and> \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" 
    using config_type_elims by meson
  then obtain z and \<tau>' where zt: "\<Theta> ; {||} ; GNil \<turnstile> (\<lbrace> z : B_unit | TRUE \<rbrace>) \<lesssim> \<tau> \<and> (u,\<tau>') \<in> setD \<Delta> \<and> \<Theta> ; {||} ; GNil \<turnstile> v \<Leftarrow> \<tau>' \<and> \<Theta> ; {||} ; GNil  \<turnstile>\<^sub>w\<^sub>f \<Delta>" 
    using check_s_elims(8) by metis
  hence "\<Theta> \<turnstile> update_d \<delta> u v \<sim> \<Delta>" using update_d_sim  * by metis
  moreover have "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_val (V_lit L_unit ) \<Leftarrow> \<tau>" using zt * check_s_v_unit check_s_wf
    by auto
  ultimately show ?case using config_typeI * by (meson order_refl)
next
  case (reduce_seq1I \<Phi> \<delta> s)
  hence "\<Theta> ; \<Phi> ;   {||} ; GNil ; \<Delta> \<turnstile> s \<Leftarrow> \<tau> \<and> \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" 
    using check_s_elims config_type_elims by force
  then show ?case  using config_typeI by blast
next
  case (reduce_seq2I s1 v \<Phi> \<delta> \<delta>' s1' s2)
  hence tt: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_seq s1 s2 \<Leftarrow> \<tau> \<and> \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" 
    using config_type_elims by blast
  then obtain z where zz: "\<Theta> ; \<Phi> ; {||} ; GNil; \<Delta>  \<turnstile> s1 \<Leftarrow> (\<lbrace> z : B_unit | TRUE \<rbrace>) \<and>  \<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> s2 \<Leftarrow> \<tau>" 
    using check_s_elims by blast
  hence "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle> \<delta> , s1 \<rangle> \<Leftarrow> (\<lbrace> z : B_unit | TRUE \<rbrace>)" 
    using tt config_typeI tt by simp 
  then obtain \<Delta>' where *: "\<Theta>; \<Phi>; \<Delta>' \<turnstile> \<langle> \<delta>' , s1' \<rangle> \<Leftarrow> (\<lbrace> z : B_unit | TRUE \<rbrace>) \<and> \<Delta> \<sqsubseteq> \<Delta>'" 
    using reduce_seq2I by meson
  moreover hence  s't: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>'  \<turnstile> s1' \<Leftarrow> (\<lbrace> z : B_unit | TRUE \<rbrace>) \<and> \<Theta> \<turnstile> \<delta>' \<sim> \<Delta>'" 
    using config_type_elims by force
  moreover hence "\<Theta> ; {||} ; GNil  \<turnstile>\<^sub>w\<^sub>f \<Delta>'" using check_s_wf by meson
  moreover hence  "\<Theta>; \<Phi>; {||}; GNil; \<Delta>'  \<turnstile> s2 \<Leftarrow> \<tau>" 
    using calculation(1) zz check_s_d_weakening * by metis
  moreover hence  "\<Theta>; \<Phi>; {||}; GNil; \<Delta>'  \<turnstile> (AS_seq s1' s2) \<Leftarrow> \<tau>" 
    using check_seqI zz s't by meson 
  ultimately have  "\<Theta>; \<Phi>; \<Delta>'  \<turnstile> \<langle> \<delta>' , AS_seq s1' s2 \<rangle> \<Leftarrow> \<tau> \<and> \<Delta> \<sqsubseteq> \<Delta>'"
    using zz config_typeI tt  by meson
  then show ?case by meson
next
  case (reduce_whileI x  s1 s2 z' \<Phi> \<delta> )

  hence *: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_while s1 s2  \<Leftarrow> \<tau> \<and> \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" 
    using config_type_elims by meson

  hence  **:"\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_while s1 s2  \<Leftarrow> \<tau>" by auto
  hence "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_let2 x (\<lbrace> z' : B_bool  | TRUE \<rbrace>) s1 (AS_if (V_var x) (AS_seq s2 (AS_while s1 s2))  (AS_val (V_lit L_unit)) ) \<Leftarrow> \<tau>"
    using check_while reduce_whileI by auto
  thus ?case  using config_typeI *   by (meson subset_refl)

next
  case (reduce_caseI dc x' s' css \<Phi> \<delta> tyid  v)

  hence **: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> AS_match (V_cons tyid dc v) css \<Leftarrow> \<tau> \<and> \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)"
    using config_type_elims[OF reduce_caseI(2)] by metis
  hence ***: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AS_match (V_cons tyid  dc v) css \<Leftarrow> \<tau>" by auto

  let ?vcons = "V_cons tyid dc v"

  obtain dclist tid  and z::x where cv:  "\<Theta>; {||} ; GNil \<turnstile> (V_cons tyid dc v) \<Leftarrow> (\<lbrace> z : B_id tid | TRUE \<rbrace>) \<and> 
    \<Theta>; \<Phi>; {||}; GNil; \<Delta> ; tid ; dclist ; (V_cons tyid dc v) \<turnstile> css \<Leftarrow> \<tau> \<and>  AF_typedef tid dclist \<in> set \<Theta> \<and> 
 \<Theta> ; {||} ; GNil  \<turnstile> V_cons tyid dc v \<Leftarrow> \<lbrace> z : B_id tid  | TRUE \<rbrace>"
    using check_s_elims(9)[OF ***] by metis

  hence vi:" \<Theta> ; {||} ; GNil  \<turnstile> V_cons tyid dc v \<Leftarrow> \<lbrace> z : B_id tid  | TRUE \<rbrace>" by auto
  obtain tcons where vi2:" \<Theta> ; {||} ; GNil  \<turnstile> V_cons tyid dc v \<Rightarrow> tcons \<and> \<Theta> ; {||} ; GNil  \<turnstile> tcons \<lesssim>  \<lbrace> z : B_id tid  | TRUE \<rbrace>" 
    using check_v_elims(1)[OF vi] by metis
  hence vi1: "\<Theta> ; {||} ; GNil  \<turnstile> V_cons tyid dc v \<Rightarrow> tcons" by auto

  show ?case proof(rule infer_v_elims(4)[OF vi1],goal_cases)
    case (1 dclist2 tc tv z2)
    have "tyid = tid" using \<tau>.eq_iff using subtype_eq_base vi2 1 by fastforce 
    hence deq:"dclist = dclist2"  using check_v_wf wfX_wfY cv 1  wfTh_dclist_unique by metis
    have "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> s'[x'::=v]\<^sub>s\<^sub>v \<Leftarrow> \<tau>" proof(rule check_match(3))     
      show \<open> \<Theta> ;  \<Phi> ;  {||} ; GNil ; \<Delta> ; tyid ; dclist ; ?vcons \<turnstile> css \<Leftarrow> \<tau>\<close> using \<open>tyid = tid\<close> cv by auto
      show "distinct (map fst dclist)" using wfTh_dclist_distinct check_v_wf wfX_wfY cv by metis
      show \<open>?vcons = V_cons tyid dc v\<close> by auto
      show \<open>{||} = {||}\<close> by auto
      show \<open>(dc, tc) \<in> set dclist\<close> using 1 deq by auto
      show \<open>GNil = GNil\<close> by auto
      show \<open>Some (AS_branch dc x' s') = lookup_branch dc css\<close> using reduce_caseI by auto
      show \<open>\<Theta> ; {||} ; GNil  \<turnstile> v \<Leftarrow> tc\<close> using 1 check_v.intros by auto
    qed
    thus  ?case using config_typeI ** by blast
  qed

next
  case (reduce_let_fstI \<Phi> \<delta> x v1 v2 s)
  thus ?case using preservation_fst_snd order_refl by metis
next
  case (reduce_let_sndI  \<Phi> \<delta> x v1 v2 s)
  thus ?case using preservation_fst_snd order_refl by metis
next
  case (reduce_let_concatI \<Phi> \<delta> x v1 v2 s)
  hence elim: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  AS_let x (AE_concat (V_lit (L_bitvec v1)) (V_lit (L_bitvec v2))) s \<Leftarrow> \<tau> \<and> 
                  \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" 
    using config_type_elims by metis

  obtain z::x where z: "atom z \<sharp> (AE_concat (V_lit (L_bitvec v1)) (V_lit (L_bitvec v2)), GNil, CE_val (V_lit (L_bitvec (v1 @ v2))))" 
    using obtain_fresh by metis

  have "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f GNil" using check_s_wf elim by auto

  have "\<Theta>; \<Phi>; {||}; GNil; \<Delta> \<turnstile> AS_let x (AE_val (V_lit (L_bitvec (v1 @ v2)))) s \<Leftarrow> \<tau>" proof(rule subtype_let)
    show \<open> \<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> AS_let x (AE_concat (V_lit (L_bitvec v1)) (V_lit (L_bitvec v2))) s \<Leftarrow> \<tau>\<close> using elim by auto
    show \<open>\<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> (AE_concat (V_lit (L_bitvec v1)) (V_lit (L_bitvec v2))) \<Rightarrow> \<lbrace> z : B_bitvec  | CE_val (V_var z)  == (CE_concat ([V_lit (L_bitvec v1)]\<^sup>c\<^sup>e) ([V_lit (L_bitvec v2)]\<^sup>c\<^sup>e))\<rbrace> \<close> 
      (is "\<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> ?e1 \<Rightarrow> ?t1")
    proof
      show \<open> \<Theta> ; {||} ; GNil  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using check_s_wf elim by auto
      show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using check_s_wf elim by auto
      show \<open> \<Theta> ; {||} ; GNil  \<turnstile> V_lit (L_bitvec v1) \<Rightarrow> \<lbrace> z : B_bitvec | CE_val (V_var z) == CE_val (V_lit (L_bitvec v1)) \<rbrace>\<close> 
        using infer_v_litI infer_l.intros  \<open>\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f GNil\<close>  fresh_GNil by auto
      show \<open> \<Theta> ; {||} ; GNil  \<turnstile> V_lit (L_bitvec v2) \<Rightarrow> \<lbrace> z : B_bitvec | CE_val (V_var z) == CE_val (V_lit (L_bitvec v2)) \<rbrace>\<close> 
        using infer_v_litI infer_l.intros  \<open>\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f GNil\<close>  fresh_GNil by auto
      show \<open>atom z \<sharp> AE_concat (V_lit (L_bitvec v1)) (V_lit (L_bitvec v2))\<close> using z fresh_Pair by metis
      show \<open>atom z \<sharp> GNil\<close> using z fresh_Pair by auto
    qed
    show \<open>\<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> AE_val (V_lit (L_bitvec (v1 @ v2))) \<Rightarrow>  \<lbrace> z : B_bitvec  | CE_val (V_var z) == CE_val (V_lit (L_bitvec (v1 @ v2))) \<rbrace> \<close> 
      (is "\<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> ?e2 \<Rightarrow> ?t2")
      using infer_e_valI infer_v_litI infer_l.intros  \<open>\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f GNil\<close>  fresh_GNil check_s_wf elim by metis
    show \<open>\<Theta> ; {||} ; GNil  \<turnstile> ?t2 \<lesssim> ?t1\<close> using subtype_concat check_s_wf elim by auto
  qed

  thus ?case  using config_typeI elim by (meson order_refl)
next
  case (reduce_let_lenI \<Phi> \<delta> x v s)
  hence elim: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  AS_let x (AE_len (V_lit (L_bitvec v))) s \<Leftarrow> \<tau> \<and> \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" 
    using check_s_elims config_type_elims by metis

  then obtain t where t: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile> AE_len (V_lit (L_bitvec v)) \<Rightarrow> t"   using check_s_elims by meson

  moreover then obtain z::x where  "t = \<lbrace> z : B_int  | CE_val (V_var z)  ==  CE_len ([V_lit (L_bitvec v)]\<^sup>c\<^sup>e)  \<rbrace>" using infer_e_elims by meson 

  moreover obtain z'::x where "atom z' \<sharp> v" using obtain_fresh by metis
  moreover have  "\<Theta>; \<Phi>; {||}; GNil; \<Delta> \<turnstile>  AE_val (V_lit (L_num (int (length v)))) \<Rightarrow> \<lbrace> z' : B_int  | CE_val (V_var z')  ==  CE_val (V_lit (L_num (int (length v))))  \<rbrace>" 
    using infer_e_valI infer_v_litI infer_l.intros(3)  t  check_s_wf elim 
    by (metis infer_l_form2 type_for_lit.simps(3))

  moreover have "\<Theta> ; {||} ; GNil \<turnstile>   \<lbrace> z' : B_int  | CE_val (V_var z')  ==  CE_val (V_lit (L_num (int (length v))))  \<rbrace> \<lesssim> 
                           \<lbrace> z : B_int  | CE_val (V_var z)  ==  CE_len [(V_lit (L_bitvec v))]\<^sup>c\<^sup>e  \<rbrace>" using subtype_len check_s_wf elim by auto

  ultimately have "\<Theta>; \<Phi>; {||}; GNil; \<Delta> \<turnstile>  AS_let x (AE_val (V_lit (L_num (int (length v)))))  s \<Leftarrow> \<tau>" using subtype_let by (meson elim)
  thus ?case  using config_typeI elim by (meson order_refl)
next
  case (reduce_let_splitI n v v1 v2 \<Phi> \<delta> x s)
  hence elim: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  AS_let x (AE_split (V_lit (L_bitvec v)) (V_lit (L_num n))) s \<Leftarrow> \<tau> \<and> 
                  \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" 
    using config_type_elims by metis

  obtain z::x where z: "atom z \<sharp> (AE_split (V_lit (L_bitvec v)) (V_lit (L_num n)), GNil, CE_val (V_lit (L_bitvec (v1 @ v2))), 
([ L_bitvec v1 ]\<^sup>v, [ L_bitvec v2 ]\<^sup>v), \<Theta>, {||}::bv fset)" 
    using obtain_fresh by metis

  have *:"\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f GNil" using check_s_wf elim by auto

  have "\<Theta>; \<Phi>; {||}; GNil; \<Delta> \<turnstile> AS_let x (AE_val (V_pair (V_lit (L_bitvec v1)) (V_lit (L_bitvec v2)))) s \<Leftarrow> \<tau>" proof(rule subtype_let)

    show \<open> \<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> AS_let x (AE_split (V_lit (L_bitvec v)) (V_lit (L_num n))) s \<Leftarrow> \<tau>\<close> using elim by auto
    show \<open>\<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> (AE_split (V_lit (L_bitvec v)) (V_lit (L_num n))) \<Rightarrow> \<lbrace> z : B_pair B_bitvec B_bitvec  
                 |   ((CE_val (V_lit (L_bitvec v))) == (CE_concat (CE_fst (CE_val (V_var z))) (CE_snd (CE_val (V_var z)))))
                  AND (((CE_len (CE_fst (CE_val (V_var z))))) == (CE_val (V_lit (L_num n)))) \<rbrace> \<close> 
      (is "\<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> ?e1 \<Rightarrow> ?t1") 
    proof
      show \<open> \<Theta> ; {||} ; GNil  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using check_s_wf elim by auto
      show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using check_s_wf elim by auto
      show \<open> \<Theta> ; {||} ; GNil  \<turnstile> V_lit (L_bitvec v) \<Rightarrow> \<lbrace> z : B_bitvec | CE_val (V_var z) == CE_val (V_lit (L_bitvec v)) \<rbrace>\<close> 
        using infer_v_litI infer_l.intros  \<open>\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f GNil\<close>  fresh_GNil by auto
      show "\<Theta> ; {||} ; GNil  \<turnstile> ([ L_num
                           n ]\<^sup>v) \<Leftarrow> \<lbrace> z : B_int  | (([ leq [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e)  ==  ([ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e))   AND  [ leq [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e [| [ [ L_bitvec
                   v ]\<^sup>v ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e   \<rbrace>" using split_n  reduce_let_splitI check_v_num_leq * wfX_wfY  by metis
      show \<open>atom z \<sharp> AE_split [ L_bitvec v ]\<^sup>v [ L_num n ]\<^sup>v\<close> using z fresh_Pair by auto
      show \<open>atom z \<sharp> GNil\<close> using z fresh_Pair by auto
      show \<open>atom z \<sharp> AE_split [ L_bitvec v ]\<^sup>v [ L_num n ]\<^sup>v\<close> using z fresh_Pair by auto
      show \<open>atom z \<sharp> GNil\<close> using z fresh_Pair by auto
      show \<open>atom z \<sharp> AE_split [ L_bitvec v ]\<^sup>v [ L_num n ]\<^sup>v\<close> using z fresh_Pair by auto
      show \<open>atom z \<sharp> GNil\<close> using z fresh_Pair by auto
    qed

    show \<open>\<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> AE_val (V_pair (V_lit (L_bitvec v1)) (V_lit (L_bitvec v2))) \<Rightarrow>  \<lbrace> z : B_pair B_bitvec  B_bitvec  | CE_val (V_var z) == CE_val ((V_pair (V_lit (L_bitvec v1)) (V_lit (L_bitvec v2)))) \<rbrace> \<close> 
      (is "\<Theta>; \<Phi>; {||}; GNil; \<Delta>   \<turnstile> ?e2 \<Rightarrow> ?t2")
      apply(rule infer_e_valI)
      using check_s_wf elim apply metis
      using check_s_wf elim apply metis      
      apply(rule infer_v_pair2I)
      using z fresh_prodN apply metis
      using z fresh_GNil fresh_prodN apply metis
      using  infer_v_litI infer_l.intros  \<open>\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f GNil\<close> b_of.simps  apply blast+
      using b_of.simps apply simp+
      done
    show \<open>\<Theta> ; {||} ; GNil  \<turnstile> ?t2 \<lesssim> ?t1\<close> using subtype_split check_s_wf elim reduce_let_splitI by auto
  qed

  thus ?case  using config_typeI elim by (meson order_refl)
next
  case (reduce_assert1I \<Phi> \<delta> c v)

  hence elim: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  AS_assert c [v]\<^sup>s   \<Leftarrow> \<tau> \<and> 
                  \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" 
    using config_type_elims reduce_assert1I by metis
  hence *:"\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  AS_assert c [v]\<^sup>s   \<Leftarrow> \<tau>" by auto

  have  "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  [v]\<^sup>s   \<Leftarrow> \<tau>" using  check_assert_s *  by metis
  thus  ?case using elim config_typeI  by blast
next
  case (reduce_assert2I \<Phi> \<delta> s \<delta>' s' c)

  hence elim: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  AS_assert c s  \<Leftarrow> \<tau> \<and> 
                  \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<and> (\<forall>fd\<in>set \<Phi>. check_fundef \<Theta> \<Phi> fd)" 
    using config_type_elims by metis
  hence *:"\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  AS_assert c s   \<Leftarrow> \<tau>" by auto

  have  cv: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>  \<turnstile>  s   \<Leftarrow> \<tau> \<and> \<Theta> ; {||} ; GNil  \<Turnstile> c " using check_assert_s *  by metis

  hence "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle>\<delta>, s\<rangle> \<Leftarrow> \<tau>" using elim config_typeI by simp
  then obtain \<Delta>' where D: "\<Theta>; \<Phi>; \<Delta>' \<turnstile> \<langle> \<delta>' , s' \<rangle> \<Leftarrow> \<tau>  \<and> \<Delta> \<sqsubseteq> \<Delta>'" using reduce_assert2I by metis
  hence **:"\<Theta>; \<Phi>; {||}; GNil; \<Delta>' \<turnstile> s' \<Leftarrow> \<tau> \<and> \<Theta> \<turnstile> \<delta>' \<sim> \<Delta>'" using config_type_elims by metis

  obtain x::x where x:"atom x \<sharp> (\<Theta>, \<Phi>, ({||}::bv fset), GNil, \<Delta>', c, \<tau>, s')" using obtain_fresh by metis

  have *:"\<Theta>; \<Phi>; {||}; GNil; \<Delta>'  \<turnstile> AS_assert c s'  \<Leftarrow> \<tau>" proof
    show "atom x \<sharp> (\<Theta>, \<Phi>, {||}, GNil, \<Delta>', c, \<tau>, s')" using x by auto
    have "\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f c" using * check_s_wf by auto
    hence wfg:"\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f (x, B_bool, c) #\<^sub>\<Gamma> GNil" using wfC_wfG wfB_boolI check_s_wf *  fresh_GNil by auto
    moreover have cs: "\<Theta>; \<Phi>; {||}; GNil; \<Delta>' \<turnstile> s' \<Leftarrow> \<tau>" using ** by auto
    ultimately show  "\<Theta> ; \<Phi> ; {||} ; (x, B_bool, c) #\<^sub>\<Gamma> GNil ; \<Delta>'  \<turnstile> s' \<Leftarrow> \<tau>" using check_s_g_weakening(1)[OF cs _ wfg]   toSet.simps  by simp
    show "\<Theta> ; {||} ; GNil  \<Turnstile> c " using cv by auto
    show "\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f \<Delta>' " using check_s_wf ** by auto
  qed

  thus  ?case using elim config_typeI D ** by metis
qed

lemma preservation_many: 
  assumes " \<Phi>  \<turnstile> \<langle>\<delta>, s\<rangle> \<longrightarrow>\<^sup>* \<langle> \<delta>' , s' \<rangle>"
  shows "\<Theta>; \<Phi>; \<Delta> \<turnstile>  \<langle>\<delta>, s\<rangle> \<Leftarrow> \<tau> \<Longrightarrow> \<exists>\<Delta>'. \<Theta>; \<Phi>; \<Delta>' \<turnstile> \<langle> \<delta>' , s' \<rangle> \<Leftarrow> \<tau> \<and> \<Delta> \<sqsubseteq> \<Delta>'" 
  using assms proof(induct arbitrary: \<Delta> rule: reduce_stmt_many.induct)
  case (reduce_stmt_many_oneI \<Phi> \<delta> s \<delta>' s')
  then show ?case using preservation by simp
next
  case (reduce_stmt_many_manyI \<Phi> \<delta> s \<delta>' s' \<delta>'' s'')
  then show ?case using preservation subset_trans by metis
qed

section \<open>Progress\<close>
text \<open>We prove that a well typed program is either a value or we can make a step\<close>

lemma check_let_op_infer:
  assumes  "\<Theta>; \<Phi>; {||}; \<Gamma>; \<Delta>   \<turnstile> LET x = (AE_op opp v1 v2) IN s \<Leftarrow> \<tau>" and "supp ( LET x = (AE_op opp v1 v2) IN s) \<subseteq> atom`fst`setD \<Delta>"
  shows  "\<exists> z b c. \<Theta>; \<Phi>; {||}; \<Gamma>; \<Delta> \<turnstile>  (AE_op opp v1 v2) \<Rightarrow> \<lbrace>z:b|c\<rbrace>"
proof - 
  have xx: "\<Theta>; \<Phi>; {||}; \<Gamma>; \<Delta> \<turnstile> LET x = (AE_op opp v1 v2) IN s \<Leftarrow> \<tau>" using assms by simp
  then show ?thesis using check_s_elims(2)[OF xx] by meson
qed

lemma infer_pair:
  assumes "\<Theta> ; B; \<Gamma> \<turnstile>  v  \<Rightarrow> \<lbrace> z : B_pair b1 b2  | c \<rbrace>" and "supp v = {}"
  obtains v1 and v2 where "v = V_pair v1 v2" 
  using assms proof(nominal_induct v rule: v.strong_induct)
  case (V_lit x)
  then show ?case by auto
next
  case (V_var x)
  then show ?case using v.supp supp_at_base by auto
next
  case (V_pair x1a x2a)
  then show ?case by auto
next
  case (V_cons x1a x2a x3)
  then show ?case by auto
next
  case (V_consp x1a x2a x3 x4)
  then show ?case by auto
qed

lemma progress_fst:
  assumes  "\<Theta>; \<Phi>; {||}; \<Gamma>; \<Delta>  \<turnstile> LET x = (AE_fst v) IN s \<Leftarrow> \<tau>" and  "\<Theta> \<turnstile> \<delta> \<sim> \<Delta>" and 
    "supp (LET x = (AE_fst v) IN s)  \<subseteq> atom`fst`setD \<Delta>"
  shows "\<exists>\<delta>' s'. \<Phi>  \<turnstile> \<langle> \<delta> , LET x = (AE_fst v) IN s \<rangle> \<longrightarrow> \<langle>\<delta>', s'\<rangle>"
proof -
  have *:"supp v = {}" using assms s_branch_s_branch_list.supp by auto
  obtain z and b and c where "\<Theta>; \<Phi>; {||}; \<Gamma>; \<Delta> \<turnstile>  (AE_fst v ) \<Rightarrow> \<lbrace> z : b  | c \<rbrace>" 
    using check_s_elims(2)  using assms by meson
  moreover obtain z' and b' and c' where "\<Theta> ; {||} ; \<Gamma> \<turnstile>  v  \<Rightarrow> \<lbrace> z' : B_pair b b'  | c' \<rbrace>" 
    using infer_e_elims(8)  using calculation by auto 
  moreover then obtain v1 and v2 where "V_pair v1 v2 = v" 
    using * infer_pair by metis
  ultimately show ?thesis using reduce_let_fstI assms  by metis
qed

lemma progress_let:
  assumes "\<Theta>; \<Phi>; {||}; \<Gamma>; \<Delta> \<turnstile> LET x = e IN s \<Leftarrow> \<tau>" and "\<Theta> \<turnstile> \<delta> \<sim> \<Delta>" and 
    "supp (LET x = e IN s) \<subseteq> atom ` fst ` setD \<Delta>" and "sble \<Theta> \<Gamma>"
  shows "\<exists>\<delta>' s'. \<Phi>  \<turnstile> \<langle> \<delta> , LET x = e IN s\<rangle> \<longrightarrow> \<langle> \<delta>' , s'\<rangle>"
proof -
  obtain z b c where *: "\<Theta>; \<Phi>; {||}; \<Gamma>; \<Delta>  \<turnstile> e \<Rightarrow> \<lbrace> z : b  | c \<rbrace> " using check_s_elims(2)[OF assms(1)] by metis
  have **: "supp e \<subseteq> atom ` fst ` setD \<Delta>" using assms s_branch_s_branch_list.supp by auto
  from * ** assms show ?thesis proof(nominal_induct "\<lbrace> z : b  | c \<rbrace>"  rule: infer_e.strong_induct)
    case (infer_e_valI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v)
    then show ?case using reduce_stmt_elims reduce_let_valI by metis
  next
    case (infer_e_plusI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 c2 z3)
    hence vf: "supp v1 = {} \<and> supp v2 = {}"  by force
    then obtain n1 and n2 where *: "v1 = V_lit (L_num n1)  \<and> v2 = (V_lit (L_num n2))" using infer_int infer_e_plusI by metis
    then show ?case using reduce_let_plusI * by metis
  next
    case (infer_e_leqI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 c2 z3)
    hence vf: "supp v1 = {} \<and> supp v2 = {}"  by force
    then obtain n1 and n2 where *: "v1 = V_lit (L_num n1)  \<and> v2 = (V_lit (L_num n2))" using infer_int infer_e_leqI by metis
    then show ?case using reduce_let_leqI * by metis
  next
    case (infer_e_eqI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 bb c1 v2 z2 c2 z3)
    hence vf: "supp v1 = {} \<and> supp v2 = {}"  by force
    then obtain n1 and n2 where *: "v1 = V_lit n1  \<and> v2 = (V_lit n2)" using infer_lit infer_e_eqI by metis
    then show ?case using reduce_let_eqI by blast
  next
    case (infer_e_appI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> f x b c \<tau>' s' v)
    then show ?case using reduce_let_appI by metis
  next
    case (infer_e_appPI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> b' f bv x b c \<tau>' s' v)
    then show ?case using reduce_let_appPI by metis
  next
    case (infer_e_fstI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v z' b2 c z)
    hence "supp v = {}" by force
    then obtain v1 and v2 where "v = V_pair v1 v2" using infer_e_fstI infer_pair by metis
    then show ?case using reduce_let_fstI * by metis
  next
    case (infer_e_sndI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v z' b1 c z)
    hence "supp v = {}" by force
    then obtain v1 and v2 where "v = V_pair v1 v2" using infer_e_sndI infer_pair by metis
    then show ?case using reduce_let_sndI * by metis
  next
    case (infer_e_lenI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v z' c za)
    hence "supp v = {}" by force
    then obtain bvec where "v = V_lit (L_bitvec bvec)" using infer_e_lenI infer_bitvec by metis
    then show ?case using reduce_let_lenI * by metis
  next
    case (infer_e_mvarI \<Theta> \<B> \<Gamma> \<Phi> \<Delta> u)
    hence "(u, \<lbrace> z : b  | c \<rbrace>) \<in> setD \<Delta>" using infer_e_elims(10) by meson
    then obtain v where "(u,v) \<in> set \<delta>" using infer_e_mvarI delta_sim_delta_lookup by meson
    then show ?case using reduce_let_mvar by metis
  next
    case (infer_e_concatI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 c2 z3)
    hence vf: "supp v1 = {} \<and> supp v2 = {}"  by force
    then obtain n1 and n2 where *: "v1 = V_lit (L_bitvec n1)  \<and> v2 = (V_lit (L_bitvec n2))" using infer_bitvec infer_e_concatI by metis
    then show ?case using reduce_let_concatI * by metis
  next
    case (infer_e_splitI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 z3)
    hence vf: "supp v1 = {} \<and> supp v2 = {}"  by force
    then obtain n1 and n2 where *: "v1 = V_lit (L_bitvec n1)  \<and> v2 = (V_lit (L_num n2))" using infer_bitvec infer_e_splitI check_int by metis

    have "0 \<le> n2 \<and> n2 \<le> int (length n1)" using  check_v_range[OF _ * ]   infer_e_splitI by simp
    then obtain bv1 and bv2 where "split n2 n1 (bv1 , bv2)" using obtain_split by metis
    then show ?case using reduce_let_splitI * by metis
  qed
qed 

lemma check_css_lookup_branch_exist:
  fixes s::s and cs::branch_s and css::branch_list and v::v
  shows 
    "\<Theta>; \<Phi>; B; G; \<Delta> \<turnstile>  s \<Leftarrow> \<tau> \<Longrightarrow> True" and 
    "check_branch_s \<Theta> \<Phi>  {||} GNil \<Delta> tid dc const v cs \<tau> \<Longrightarrow> True" and 
    "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>; tid; dclist; v \<turnstile> css \<Leftarrow> \<tau> \<Longrightarrow> (dc, t) \<in> set dclist \<Longrightarrow>  
              \<exists>x' s'. Some (AS_branch dc x' s') = lookup_branch dc css"
proof(nominal_induct \<tau> and \<tau> and \<tau>  rule: check_s_check_branch_s_check_branch_list.strong_induct)
  case (check_branch_list_consI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid cons const v cs \<tau> dclist css)
  then show ?case  using lookup_branch.simps check_branch_list_finalI by force
next
  case (check_branch_list_finalI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid cons const v cs \<tau>)
  then show ?case  using lookup_branch.simps check_branch_list_finalI by force
qed(auto+)

lemma progress_aux:  
  shows    "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> s \<Leftarrow> \<tau> \<Longrightarrow> \<B> = {||} \<Longrightarrow>  sble \<Theta> \<Gamma> \<Longrightarrow> supp s \<subseteq> atom ` fst ` setD \<Delta> \<Longrightarrow> \<Theta> \<turnstile> \<delta> \<sim> \<Delta> \<Longrightarrow> 
               (\<exists>v. s = [v]\<^sup>s) \<or> (\<exists>\<delta>' s'. \<Phi> \<turnstile> \<langle>\<delta>, s\<rangle> \<longrightarrow> \<langle>\<delta>', s'\<rangle>)" and
    "\<Theta>; \<Phi>; {||}; \<Gamma>; \<Delta>; tid; dc; const; v2 \<turnstile> cs \<Leftarrow> \<tau>  \<Longrightarrow> supp cs = {} \<Longrightarrow> True " 
    "\<Theta>; \<Phi>; {||}; \<Gamma>; \<Delta>; tid; dclist; v2 \<turnstile> css \<Leftarrow> \<tau> \<Longrightarrow> supp css = {} \<Longrightarrow> True " 
proof(induct  rule: check_s_check_branch_s_check_branch_list.inducts)
  case (check_valI \<Delta> \<Theta> \<Gamma> v \<tau>' \<tau>)
  then show ?case by auto
next
  case (check_letI x \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e \<tau> z s b c)
  hence "\<Theta>; \<Phi>; {||}; \<Gamma>; \<Delta>   \<turnstile>   AS_let x e s \<Leftarrow> \<tau>" using Typing.check_letI by meson
  then show ?case using progress_let check_letI by metis
next
  case (check_branch_s_branchI \<Theta> \<B> \<Gamma> \<Delta> \<tau> const x \<Phi> tid cons v s)
  then show ?case by auto
next
  case (check_branch_list_consI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist v cs \<tau> css)
  then show ?case by auto
next
  case (check_branch_list_finalI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist v cs \<tau>)
  then show ?case by auto
next
  case (check_ifI z \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v s1 s2 \<tau>)
  have "supp v = {}" using check_ifI s_branch_s_branch_list.supp by auto
  hence "v = V_lit L_true \<or> v = V_lit L_false" using  check_bool_options check_ifI by auto
  then show ?case using reduce_if_falseI reduce_if_trueI check_ifI by meson
next
  case (check_let2I x \<Theta> \<Phi> \<B> G \<Delta> t s1 \<tau> s2 )
  then consider  " (\<exists>v. s1 = AS_val v)" | "(\<exists>\<delta>' a. \<Phi>  \<turnstile> \<langle>\<delta>, s1\<rangle> \<longrightarrow> \<langle>\<delta>', a\<rangle>)" by auto
  then show ?case proof(cases)
    case 1
    then show ?thesis using reduce_let2_valI by fast
  next
    case 2
    then show ?thesis using reduce_let2I check_let2I by meson
  qed
next
  case (check_varI u \<Theta> \<Phi> \<B> \<Gamma> \<Delta> \<tau>' v \<tau> s)

  obtain uu::u where uf: "atom uu \<sharp> (u,\<delta>,s) " using obtain_fresh by blast
  obtain sa where " (uu \<leftrightarrow> u ) \<bullet> s = sa" by presburger
  moreover have "atom uu \<sharp> s" using uf fresh_prod3 by auto
  ultimately have "AS_var uu \<tau>' v sa = AS_var u \<tau>' v s" using s_branch_s_branch_list.eq_iff(7) Abs1_eq_iff(3)[of uu sa u s] by auto

  moreover have "atom uu \<sharp> \<delta>" using uf fresh_prod3 by auto
  ultimately have "\<Phi> \<turnstile> \<langle>\<delta>, AS_var u \<tau>' v s\<rangle> \<longrightarrow> \<langle>(uu, v) # \<delta>, sa\<rangle>"
    using reduce_varI uf by metis
  then show ?case by auto
next
  case (check_assignI \<Delta> u \<tau> P G v z \<tau>')
  then show ?case using reduce_assignI by blast
next
  case (check_whileI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 z s2 \<tau>')
  obtain x::x where "atom x \<sharp> (s1,s2)" using obtain_fresh by metis
  moreover obtain z::x where "atom z \<sharp> x" using obtain_fresh by metis
  ultimately show ?case using reduce_whileI by fast
next
  case (check_seqI P \<Phi> \<B> G \<Delta> s1 z s2 \<tau>)
  thus  ?case proof(cases "\<exists>v. s1 = AS_val v")
    case True
    then obtain v where v: "s1 = AS_val v" by blast
    hence "supp v = {}" using check_seqI by auto
    have "\<exists>z1 c1. P; \<B>; G \<turnstile> v \<Rightarrow> (\<lbrace> z1 : B_unit | c1 \<rbrace>)" proof - 
      obtain t where t:"P; \<B>; G \<turnstile> v \<Rightarrow> t \<and> P; \<B> ; G \<turnstile> t \<lesssim> (\<lbrace> z : B_unit | TRUE \<rbrace>)"  
        using v check_seqI(1) check_s_elims(1) by blast
      obtain z1 and b1 and c1 where teq: "t =  (\<lbrace> z1 : b1 | c1 \<rbrace>)" using obtain_fresh_z by meson
      hence "b1 = B_unit" using subtype_eq_base t by meson
      thus ?thesis using t teq by fast
    qed
    then obtain z1 and c1 where "P ; \<B> ; G \<turnstile> v \<Rightarrow> (\<lbrace> z1 : B_unit | c1 \<rbrace>)" by auto
    hence "v = V_lit L_unit" using infer_v_unit_form \<open>supp v = {}\<close> by simp
    hence "s1 = AS_val (V_lit L_unit)" using v by auto
    then show ?thesis using check_seqI reduce_seq1I by meson
  next
    case False
    then show ?thesis using check_seqI reduce_seq2I 
      by (metis Un_subset_iff s_branch_s_branch_list.supp(9))
  qed

next
  case (check_caseI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist v cs \<tau>  z)
  hence "supp v = {}" by auto

  then obtain v' and dc and t::\<tau> where v: "v = V_cons tid dc v' \<and> (dc, t) \<in> set dclist" 
    using  check_v_tid_form check_caseI by metis
  obtain z and b and c where teq: "t = (\<lbrace> z : b | c \<rbrace>)" using obtain_fresh_z by meson

  moreover then obtain x' s' where  "Some (AS_branch dc x' s') = lookup_branch dc cs" using  v teq check_caseI check_css_lookup_branch_exist by metis
  ultimately show ?case using reduce_caseI v check_caseI dc_of.cases by metis
next
  case (check_assertI x \<Theta> \<Phi> \<B> \<Gamma> \<Delta> c \<tau> s)
  hence sps: "supp s \<subseteq> atom ` fst ` setD \<Delta>" by auto
  have "atom x \<sharp> c " using check_assertI by auto
  have "atom x \<sharp> \<Gamma>" using check_assertI check_s_wf wfG_elims by metis
  have "sble \<Theta> ((x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>)" proof -
    obtain i' where i':" i' \<Turnstile> \<Gamma>  \<and>  \<Theta>; \<Gamma> \<turnstile> i'" using check_assertI sble_def by metis
    obtain i::valuation where i:"i = i' ( x \<mapsto> SBool True)" by auto

    have "i \<Turnstile> (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>" proof -
      have "i' \<Turnstile> c" using valid.simps i'  check_assertI by metis
      hence "i \<Turnstile> c" using is_satis_weakening_x i \<open>atom x \<sharp> c\<close> by auto
      moreover have "i \<Turnstile> \<Gamma>"  using is_satis_g_weakening_x i' i  check_assertI \<open>atom x \<sharp> \<Gamma>\<close> by metis
      ultimately show ?thesis   using is_satis_g.simps i by auto
    qed
    moreover have "\<Theta> ; ((x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>) \<turnstile> i" proof(rule  wfI_cons)
      show \<open> i' \<Turnstile> \<Gamma> \<close> using i' by auto
      show \<open> \<Theta> ; \<Gamma> \<turnstile> i'\<close> using i' by auto
      show \<open>i = i'(x \<mapsto> SBool True)\<close> using i by auto
      show \<open> \<Theta>  \<turnstile> SBool True: B_bool\<close> using wfRCV_BBoolI by auto
      show \<open>atom x \<sharp> \<Gamma>\<close> using check_assertI check_s_wf wfG_elims by auto
    qed
    ultimately show  ?thesis using sble_def by auto
  qed
  then consider "(\<exists>v. s = [v]\<^sup>s)" | "(\<exists>\<delta>' a.  \<Phi>  \<turnstile> \<langle>\<delta>, s\<rangle> \<longrightarrow> \<langle> \<delta>', a\<rangle>)" using check_assertI sps by metis
  hence "(\<exists>\<delta>' a.  \<Phi>  \<turnstile> \<langle>\<delta>, ASSERT c IN s\<rangle> \<longrightarrow> \<langle>\<delta>', a\<rangle>)" proof(cases)
    case 1
    then show ?thesis using reduce_assert1I by metis
  next
    case 2
    then show ?thesis using reduce_assert2I by metis
  qed  
  thus ?case by auto
qed

lemma progress:
  assumes "\<Theta>; \<Phi>; \<Delta> \<turnstile> \<langle>\<delta>, s\<rangle> \<Leftarrow> \<tau>" 
  shows "(\<exists>v. s = [v]\<^sup>s) \<or> (\<exists>\<delta>' s'. \<Phi>  \<turnstile> \<langle>\<delta>, s\<rangle> \<longrightarrow> \<langle>\<delta>', s'\<rangle>)"
proof -
  have "\<Theta>; \<Phi>; {||}; GNil; \<Delta> \<turnstile> s \<Leftarrow> \<tau>" and "\<Theta> \<turnstile> \<delta> \<sim> \<Delta>"
    using config_type_elims[OF assms(1)] by auto+
  moreover hence "supp s \<subseteq> atom ` fst ` setD \<Delta>" using check_s_wf wfS_supp by fastforce
  moreover have "sble \<Theta> GNil" using sble_def wfI_def is_satis_g.simps by simp
  ultimately show  ?thesis using progress_aux by blast
qed

section \<open>Safety\<close>

lemma  safety_stmt:
  assumes "\<Phi> \<turnstile> \<langle>\<delta>, s\<rangle> \<longrightarrow>\<^sup>* \<langle>\<delta>', s'\<rangle>" and "\<Theta>; \<Phi>; \<Delta> \<turnstile>  \<langle>\<delta>, s\<rangle> \<Leftarrow> \<tau>"
  shows  "(\<exists>v. s' = [v]\<^sup>s) \<or> (\<exists>\<delta>'' s''. \<Phi>  \<turnstile> \<langle>\<delta>', s'\<rangle> \<longrightarrow> \<langle>\<delta>'', s''\<rangle>)"  
  using preservation_many progress assms  by meson

lemma safety:
  assumes "\<turnstile> \<langle>PROG \<Theta> \<Phi> \<G> s\<rangle> \<Leftarrow> \<tau>" and  "\<Phi>  \<turnstile> \<langle>\<delta>_of \<G>, s\<rangle> \<longrightarrow>\<^sup>* \<langle>\<delta>', s'\<rangle>"
  shows  "(\<exists>v. s' = [v]\<^sup>s) \<or> (\<exists>\<delta>'' s''. \<Phi>  \<turnstile> \<langle>\<delta>', s'\<rangle> \<longrightarrow> \<langle>\<delta>'', s''\<rangle>)"   
  using assms config_type_prog_elims safety_stmt by metis

end