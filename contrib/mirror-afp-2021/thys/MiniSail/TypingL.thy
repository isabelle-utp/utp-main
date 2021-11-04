(*<*)
theory TypingL
  imports Typing RCLogicL "HOL-Eisbach.Eisbach"
begin
  (*>*)

chapter  \<open>Typing Lemmas\<close>

section \<open>Prelude\<close>

text \<open>Needed as the typing elimination rules give us facts for an alpha-equivalent version of a term
      and so need to be able to 'jump back' to a typing judgement for the orginal term\<close>

lemma \<tau>_fresh_c[simp]:
  assumes "atom x \<sharp> \<lbrace> z : b | c \<rbrace>" and "atom z \<sharp> x"
  shows "atom x \<sharp> c"
  using \<tau>.fresh assms fresh_at_base 
  by (simp add: fresh_at_base(2))

lemmas subst_defs = subst_b_b_def subst_b_c_def subst_b_\<tau>_def subst_v_v_def subst_v_c_def subst_v_\<tau>_def

lemma wfT_wfT_if1:
  assumes "wfT \<Theta> \<B> \<Gamma> (\<lbrace> z : b_of t  | CE_val v  ==  CE_val (V_lit L_false) IMP  c_of t z  \<rbrace>)" and "atom z \<sharp> (\<Gamma>,t)"
  shows "wfT \<Theta> \<B> \<Gamma> t" 
  using assms proof(nominal_induct t avoiding: \<Gamma> z rule: \<tau>.strong_induct)
  case (T_refined_type z' b' c')
  show ?case proof(rule wfT_wfT_if)
    show \<open> \<Theta>; \<B>; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b'  | [ v ]\<^sup>c\<^sup>e  ==  [ [ L_false ]\<^sup>v ]\<^sup>c\<^sup>e   IMP  c'[z'::=[ z]\<^sup>v]\<^sub>c\<^sub>v  \<rbrace> \<close> 
      using T_refined_type b_of.simps c_of.simps subst_defs by metis
    show \<open>atom z \<sharp> (c', \<Gamma>)\<close> using T_refined_type fresh_prodN \<tau>_fresh_c by metis
  qed
qed

lemma fresh_u_replace_true:
  fixes bv::bv and \<Gamma>::\<Gamma>
  assumes "atom bv \<sharp> \<Gamma>' @ (x, b, c) #\<^sub>\<Gamma> \<Gamma>"
  shows "atom bv \<sharp> \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>"
  using fresh_append_g fresh_GCons assms fresh_Pair c.fresh(1) by auto

lemma wf_replace_true1:
  fixes \<Gamma>::\<Gamma> and \<Phi>::\<Phi> and \<Theta>::\<Theta> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and c''::c and c'::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and b'::b and b::b and s::s  
    and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def and cs::branch_s and css::branch_list

shows  "\<Theta>; \<B>; G \<turnstile>\<^sub>w\<^sub>f v : b' \<Longrightarrow> G =  \<Gamma>' @ (x, b, c) #\<^sub>\<Gamma> \<Gamma> \<Longrightarrow> \<Theta> ;  \<B> ;  \<Gamma>' @ ((x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>) \<turnstile>\<^sub>w\<^sub>f v : b'" and
  "\<Theta>; \<B>; G  \<turnstile>\<^sub>w\<^sub>f c'' \<Longrightarrow>  G =   \<Gamma>' @(x, b, c) #\<^sub>\<Gamma> \<Gamma> \<Longrightarrow>  \<Theta> ;  \<B> ; \<Gamma>' @ ((x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>) \<turnstile>\<^sub>w\<^sub>f  c''" and
  "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f G \<Longrightarrow>  G =   \<Gamma>' @(x, b, c) #\<^sub>\<Gamma> \<Gamma> \<Longrightarrow>    \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f   \<Gamma>' @ ((x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>) " and
  "\<Theta>; \<B>; G \<turnstile>\<^sub>w\<^sub>f \<tau> \<Longrightarrow>  G =   \<Gamma>' @(x, b, c) #\<^sub>\<Gamma> \<Gamma> \<Longrightarrow>  \<Theta> ;  \<B> ;  \<Gamma>' @ ((x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>) \<turnstile>\<^sub>w\<^sub>f  \<tau>" and
  "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ts \<Longrightarrow>  True" and 
  "\<turnstile>\<^sub>w\<^sub>f P \<Longrightarrow> True" and
  "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f b \<Longrightarrow> True" and
  "\<Theta> ;  \<B> ; G  \<turnstile>\<^sub>w\<^sub>f ce : b' \<Longrightarrow>  G =   \<Gamma>' @(x, b, c) #\<^sub>\<Gamma> \<Gamma> \<Longrightarrow>  \<Theta> ;  \<B> ;  \<Gamma>' @ ((x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>) \<turnstile>\<^sub>w\<^sub>f ce : b'" and
  "\<Theta>  \<turnstile>\<^sub>w\<^sub>f td \<Longrightarrow>   True"
proof(nominal_induct   
    b' and c'' and G and \<tau> and ts and P and b and b' and td 
    arbitrary: \<Gamma> \<Gamma>'  and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>'
    rule:wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.strong_induct)
  case (wfB_intI \<Theta> \<B>)
  then show ?case using wf_intros by metis
next
  case (wfB_boolI \<Theta> \<B>)
  then show ?case using wf_intros by metis
next
  case (wfB_unitI \<Theta> \<B>)
  then show ?case using wf_intros by metis
next
  case (wfB_bitvecI \<Theta> \<B>)
  then show ?case using wf_intros by metis
next
  case (wfB_pairI \<Theta> \<B> b1 b2)
  then show ?case using wf_intros by metis
next
  case (wfB_consI \<Theta> s dclist \<B>)
  then show ?case using wf_intros by metis
next
  case (wfB_appI \<Theta> b s bv dclist \<B>)
  then show ?case using wf_intros by metis
next
  case (wfV_varI \<Theta> \<B> \<Gamma>'' b' c x')
  hence wfg: \<open> \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> \<close> by auto
  show ?case proof(cases "x=x'")
    case True
    hence "Some (b, TRUE) = lookup (\<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>) x'" using lookup.simps lookup_inside_wf wfg by simp
    thus ?thesis using Wellformed.wfV_varI[OF wfg] 
      by (metis True lookup_inside_wf old.prod.inject option.inject wfV_varI.hyps(1) wfV_varI.hyps(3) wfV_varI.prems)        
  next
    case False
    hence "Some (b', c) = lookup (\<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>) x'" using  lookup_inside2  wfV_varI by metis
    then show ?thesis using Wellformed.wfV_varI[OF wfg]                                     
      by (metis wfG_elim2 wfG_suffix wfV_varI.hyps(1) wfV_varI.hyps(2) wfV_varI.hyps(3) 
          wfV_varI.prems Wellformed.wfV_varI wf_replace_inside(1))
  qed
next
  case (wfV_litI \<Theta> \<B> \<Gamma> l)
  then show ?case using wf_intros using wf_intros by metis
next
  case (wfV_pairI \<Theta> \<B> \<Gamma> v1 b1 v2 b2)
  then show ?case using wf_intros by metis
next
  case (wfV_consI s dclist \<Theta> dc x b' c \<B> \<Gamma> v)
  then show ?case using wf_intros by metis
next
  case (wfV_conspI s bv dclist \<Theta> dc xc bc cc \<B> b' \<Gamma>'' v)
  show ?case proof 
    show \<open>AF_typedef_poly s bv dclist \<in> set \<Theta>\<close> using wfV_conspI by metis
    show \<open>(dc, \<lbrace> xc : bc  | cc \<rbrace>) \<in> set dclist\<close>  using wfV_conspI by metis
    show \<open> \<Theta> ;\<B>  \<turnstile>\<^sub>w\<^sub>f b' \<close>  using wfV_conspI by metis
    show \<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : bc[bv::=b']\<^sub>b\<^sub>b \<close>  using wfV_conspI by metis
    have "atom bv \<sharp> \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>" using fresh_u_replace_true wfV_conspI by metis
    thus  \<open>atom bv \<sharp> (\<Theta>, \<B>, \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>, b', v)\<close>  using wfV_conspI fresh_prodN by metis
  qed
next
  case (wfCE_valI \<Theta> \<B> \<Gamma> v b)
  then show ?case using wf_intros by metis
next
  case (wfCE_plusI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case using wf_intros by metis
next
  case (wfCE_leqI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case using wf_intros by metis
next
  case (wfCE_eqI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case using wf_intros by metis
next
  case (wfCE_fstI \<Theta> \<B> \<Gamma> v1 b1 b2)
  then show ?case using wf_intros by metis
next
  case (wfCE_sndI \<Theta> \<B> \<Gamma> v1 b1 b2)
  then show ?case using wf_intros by metis
next
  case (wfCE_concatI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case using wf_intros by metis
next
  case (wfCE_lenI \<Theta> \<B> \<Gamma> v1)
  then show ?case using wf_intros by metis
next
  case (wfTI z \<Theta> \<B> \<Gamma>''  b' c')
  show ?case proof
    show \<open>atom z \<sharp> (\<Theta>, \<B>, \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>)\<close>  using wfTI fresh_append_g fresh_GCons fresh_prodN  by auto
    show \<open> \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f b' \<close> using wfTI by metis
    show \<open> \<Theta>; \<B>; (z, b', TRUE) #\<^sub>\<Gamma> \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c' \<close>  using wfTI append_g.simps by metis
  qed
next
  case (wfC_eqI \<Theta> \<B> \<Gamma> e1 b e2)
  then show ?case using wf_intros by metis
next
  case (wfC_trueI \<Theta> \<B> \<Gamma>)
  then show ?case using wf_intros by metis
next
  case (wfC_falseI \<Theta> \<B> \<Gamma>)
  then show ?case using wf_intros by metis
next
  case (wfC_conjI \<Theta> \<B> \<Gamma> c1 c2)
  then show ?case using wf_intros by metis
next
  case (wfC_disjI \<Theta> \<B> \<Gamma> c1 c2)
  then show ?case using wf_intros by metis
next
  case (wfC_notI \<Theta> \<B> \<Gamma> c1)
  then show ?case using wf_intros by metis
next
  case (wfC_impI \<Theta> \<B> \<Gamma> c1 c2)
  then show ?case using wf_intros by metis
next
  case (wfG_nilI \<Theta> \<B>)
  then show ?case  using GNil_append by blast
next
  case (wfG_cons1I c \<Theta> \<B> \<Gamma>'' x b)
  then show ?case using wf_intros wfG_cons_TRUE2 wfG_elims(2) wfG_replace_inside wfG_suffix
    by (metis (no_types, lifting))
next
  case (wfG_cons2I c \<Theta> \<B> \<Gamma>'' x' b)
  then show ?case using wf_intros 
    by (metis wfG_cons_TRUE2 wfG_elims(2) wfG_replace_inside wfG_suffix)
next
  case wfTh_emptyI
  then show ?case  using wf_intros by metis
next
  case (wfTh_consI tdef \<Theta>)
  then show ?case  using wf_intros by metis
next
  case (wfTD_simpleI \<Theta> lst s)
  then show ?case  using wf_intros by metis
next
  case (wfTD_poly \<Theta> bv lst s)
  then show ?case  using wf_intros by metis
next
  case (wfTs_nil \<Theta> \<B> \<Gamma>)
  then show ?case  using wf_intros by metis
next
  case (wfTs_cons \<Theta> \<B> \<Gamma> \<tau> dc ts)
  then show ?case  using wf_intros by metis
qed

lemma wf_replace_true2:
  fixes \<Gamma>::\<Gamma> and \<Phi>::\<Phi> and \<Theta>::\<Theta> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and c''::c and c'::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and b'::b and b::b and s::s  
    and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def and cs::branch_s and css::branch_list

shows   "\<Theta> ; \<Phi> ;  \<B> ; G ; D  \<turnstile>\<^sub>w\<^sub>f e : b' \<Longrightarrow> G =   \<Gamma>' @(x, b, c) #\<^sub>\<Gamma> \<Gamma> \<Longrightarrow>  \<Theta> ; \<Phi> ;  \<B> ;  \<Gamma>' @ ((x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>); D \<turnstile>\<^sub>w\<^sub>f e : b'" and
  "\<Theta> ; \<Phi> ; \<B> ; G ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b' \<Longrightarrow>  G =   \<Gamma>' @(x, b, c) #\<^sub>\<Gamma> \<Gamma> \<Longrightarrow> \<Theta> ; \<Phi> ; \<B> ;   \<Gamma>' @ ((x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>) ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b'" and
  "\<Theta> ; \<Phi> ; \<B> ; G ; \<Delta> ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f cs : b' \<Longrightarrow>   G =   \<Gamma>' @(x, b, c) #\<^sub>\<Gamma> \<Gamma> \<Longrightarrow> \<Theta> ; \<Phi> ; \<B> ;  \<Gamma>' @ ((x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>) ; \<Delta> ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f cs : b'" and
  "\<Theta> ; \<Phi> ; \<B> ; G ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b' \<Longrightarrow>   G =   \<Gamma>' @(x, b, c) #\<^sub>\<Gamma> \<Gamma> \<Longrightarrow> \<Theta> ; \<Phi> ; \<B> ;   \<Gamma>' @ ((x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>) ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b'" and

"\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> \<Longrightarrow> True" and
"\<Theta>; \<B>; G  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<Longrightarrow>  G =   \<Gamma>' @(x, b, c) #\<^sub>\<Gamma> \<Gamma> \<Longrightarrow>  \<Theta> ;  \<B> ;  \<Gamma>' @ ((x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>) \<turnstile>\<^sub>w\<^sub>f \<Delta>" and

"\<Theta> ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f ftq \<Longrightarrow> True" and
"\<Theta> ; \<Phi> ; \<B> \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow>   True"
proof(nominal_induct   
    b' and b' and b' and b' and \<Phi> and \<Delta> and ftq and ft 
    arbitrary: \<Gamma> \<Gamma>'  and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>' and \<Gamma> \<Gamma>'
    rule:wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.strong_induct)

  case (wfE_valI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v b)
  then show ?case using wf_intros using wf_intros wf_replace_true1 by metis
next
  case (wfE_plusI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros wf_replace_true1 by metis
next
  case (wfE_leqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros wf_replace_true1 by metis
next
  case (wfE_eqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b v2)
  then show ?case using wf_intros wf_replace_true1 by metis
next
  case (wfE_fstI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case using wf_intros wf_replace_true1 by metis
next
  case (wfE_sndI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case using wf_intros wf_replace_true1 by metis
next
  case (wfE_concatI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros wf_replace_true1 by metis
next
  case (wfE_splitI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros wf_replace_true1 by metis
next
  case (wfE_lenI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1)
  then show ?case using wf_intros wf_replace_true1 by metis
next
  case (wfE_appI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> f x b c \<tau> s v)
  then show ?case using wf_intros wf_replace_true1 by metis
next
  case (wfE_appPI \<Theta> \<Phi> \<B> \<Gamma>'' \<Delta> b' bv v \<tau> f x1 b1 c1 s)
  show ?case proof
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wfE_appPI wf_replace_true1 by metis
    show \<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfE_appPI by metis
    show \<open> \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f b' \<close> using wfE_appPI by metis
    have "atom bv \<sharp> \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>" using fresh_u_replace_true wfE_appPI fresh_prodN by metis
    thus  \<open>atom bv \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>, \<Delta>, b', v, (b_of \<tau>)[bv::=b']\<^sub>b)\<close> 
      using wfE_appPI fresh_prodN by auto
    show \<open>Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x1 b1 c1 \<tau> s))) = lookup_fun \<Phi> f\<close> using wfE_appPI by metis
    show \<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b1[bv::=b']\<^sub>b  \<close> using wfE_appPI wf_replace_true1 by metis
  qed
next
  case (wfE_mvarI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> u \<tau>)
  then show ?case using wf_intros wf_replace_true1 by metis
next

  case (wfS_valI \<Theta> \<Phi> \<B> \<Gamma> v b \<Delta>)
  then show ?case using wf_intros wf_replace_true1 by metis
next
  case (wfS_letI  \<Theta> \<Phi> \<B> \<Gamma>'' \<Delta> e b' x1 s b1)
  show ?case proof 
    show \<open> \<Theta> ; \<Phi> ; \<B> ; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b' \<close> using wfS_letI wf_replace_true1 by metis
    have  \<open> \<Theta> ; \<Phi> ; \<B> ; ((x1, b', TRUE) #\<^sub>\<Gamma> \<Gamma>') @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b1 \<close> apply(rule  wfS_letI(4))
      using wfS_letI  append_g.simps by simp
    thus  \<open> \<Theta> ; \<Phi> ; \<B> ; (x1, b', TRUE) #\<^sub>\<Gamma> \<Gamma>'@ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b1 \<close> using append_g.simps by auto
    show \<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfS_letI by metis
    show "atom x1 \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>, \<Delta>, e, b1)" using fresh_append_g fresh_GCons fresh_prodN wfS_letI by auto
  qed
next
  case (wfS_assertI \<Theta> \<Phi> \<B> x' c \<Gamma>'' \<Delta> s b')
  show ?case proof
    show \<open> \<Theta> ; \<Phi> ; \<B> ; (x', B_bool, c) #\<^sub>\<Gamma> \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b' \<close> 
      using wfS_assertI (2)[of "(x', B_bool, c) #\<^sub>\<Gamma> \<Gamma>'" \<Gamma>] wfS_assertI by simp
    show \<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c \<close> using wfS_assertI wf_replace_true1 by metis
    show \<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfS_assertI by metis    
    show  \<open>atom x' \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>, \<Delta>, c, b', s)\<close> using wfS_assertI fresh_prodN by simp
  qed
next
  case (wfS_let2I  \<Theta> \<Phi> \<B> \<Gamma>'' \<Delta> s1 \<tau>  x' s2 ba')
  show ?case proof
    show \<open> \<Theta> ; \<Phi> ; \<B> ; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s1 : b_of \<tau> \<close> using wfS_let2I wf_replace_true1 by metis
    show \<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<tau> \<close>  using wfS_let2I wf_replace_true1 by metis
    have  \<open> \<Theta> ; \<Phi> ; \<B> ; ((x', b_of \<tau>, TRUE) #\<^sub>\<Gamma> \<Gamma>') @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s2 : ba' \<close>  
      apply(rule wfS_let2I(5))
      using wfS_let2I append_g.simps by auto
    thus \<open> \<Theta> ; \<Phi> ; \<B> ; (x', b_of \<tau>, TRUE) #\<^sub>\<Gamma> \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s2 : ba' \<close>  using wfS_let2I append_g.simps by auto
    show \<open>atom x' \<sharp>  (\<Phi>, \<Theta>, \<B>, \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>, \<Delta>, s1, ba', \<tau>)\<close>   using fresh_append_g fresh_GCons fresh_prodN wfS_let2I by auto
  qed
next
  case (wfS_ifI \<Theta> \<B> \<Gamma> v \<Phi> \<Delta> s1 b s2)
  then show ?case using wf_intros wf_replace_true1 by metis
next
  case (wfS_varI \<Theta> \<B> \<Gamma>'' \<tau> v u \<Phi> \<Delta>  b' s)
  show ?case proof
    show \<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<tau> \<close> using wfS_varI wf_replace_true1 by metis
    show \<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b_of \<tau> \<close>  using wfS_varI wf_replace_true1 by metis
    show \<open>atom u \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>, \<Delta>, \<tau>, v, b')\<close>  using wfS_varI u_fresh_g fresh_prodN by auto
    show \<open> \<Theta> ; \<Phi> ; \<B> ; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> ; (u, \<tau>) #\<^sub>\<Delta> \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b' \<close>  using wfS_varI by metis
  qed

next
  case (wfS_assignI u \<tau> \<Delta> \<Theta> \<B> \<Gamma> \<Phi> v)
  then show ?case using wf_intros wf_replace_true1 by metis
next
  case (wfS_whileI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 s2 b)
  then show ?case using wf_intros wf_replace_true1 by metis
next
  case (wfS_seqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 s2 b)
  then show ?case using wf_intros by metis
next
  case (wfS_matchI \<Theta> \<B> \<Gamma>'' v tid dclist \<Delta> \<Phi> cs b')
  show ?case proof
    show \<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : B_id tid \<close> using wfS_matchI wf_replace_true1 by auto
    show \<open>AF_typedef tid dclist \<in> set \<Theta>\<close> using wfS_matchI by auto
    show \<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfS_matchI by auto
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wfS_matchI by auto
    show \<open> \<Theta> ; \<Phi> ; \<B> ; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f cs : b' \<close> using wfS_matchI by auto
  qed
next
  case (wfS_branchI \<Theta> \<Phi> \<B> x' \<tau> \<Gamma>'' \<Delta> s b' tid dc)
  show ?case proof
    have \<open> \<Theta> ; \<Phi> ; \<B> ; ((x', b_of \<tau>, TRUE) #\<^sub>\<Gamma> \<Gamma>') @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b' \<close> using wfS_branchI append_g.simps by metis
    thus  \<open> \<Theta> ; \<Phi> ; \<B> ; (x', b_of \<tau>, TRUE) #\<^sub>\<Gamma> \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b' \<close> using wfS_branchI append_g.simps append_g.simps by metis
    show \<open>atom x' \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>, \<Delta>, \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>, \<tau>)\<close> using wfS_branchI by auto
    show \<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfS_branchI by auto
  qed
next
  case (wfS_finalI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dc t cs b)
  then show ?case using wf_intros by metis
next
  case (wfS_cons \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dc t cs b dclist css)
  then show ?case using wf_intros by metis
next
  case (wfD_emptyI \<Theta> \<B> \<Gamma>)
  then show ?case  using wf_intros wf_replace_true1 by metis
next
  case (wfD_cons \<Theta> \<B> \<Gamma> \<Delta> \<tau> u)
  then show ?case  using wf_intros wf_replace_true1 by metis
next
  case (wfPhi_emptyI \<Theta>)
  then show ?case  using wf_intros by metis
next
  case (wfPhi_consI f \<Theta> \<Phi> ft)
  then show ?case  using wf_intros by metis
next
  case (wfFTNone \<Theta> \<Phi> ft)
  then show ?case  using wf_intros by metis
next
  case (wfFTSome \<Theta> \<Phi> bv ft)
  then show ?case  using wf_intros by metis
next
  case (wfFTI \<Theta> B b \<Phi> x c s \<tau>)
  then show ?case  using wf_intros by metis
qed

lemmas wf_replace_true = wf_replace_true1 wf_replace_true2

section \<open>Subtyping\<close>

lemma subtype_reflI2:
  fixes \<tau>::\<tau>
  assumes  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f  \<tau>"
  shows "\<Theta>; \<B>; \<Gamma> \<turnstile> \<tau> \<lesssim> \<tau>"
proof -
  obtain z b c where *:"\<tau> = \<lbrace> z : b  | c \<rbrace> \<and> atom z \<sharp> (\<Theta>,\<B>,\<Gamma>) \<and>  \<Theta>; \<B>; (z, b, TRUE) #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c" 
    using  wfT_elims(1)[OF assms] by metis
  obtain x::x where **: "atom x \<sharp> (\<Theta>, \<B>, \<Gamma>, c,  z ,c, z , c )" using obtain_fresh by metis
  have "\<Theta>; \<B>; \<Gamma> \<turnstile> \<lbrace> z : b  | c \<rbrace> \<lesssim> \<lbrace> z : b  | c \<rbrace>" proof
    show "\<Theta>; \<B>; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b  | c \<rbrace>" using * assms by auto
    show "\<Theta>; \<B>; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b  | c \<rbrace>" using * assms by auto
    show "atom x \<sharp> (\<Theta>, \<B>, \<Gamma>, z , c , z , c )" using fresh_prod6 fresh_prod5 ** by metis
    thus  "\<Theta>; \<B>; (x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> c[z::=V_var x]\<^sub>v  " using wfT_wfC_cons assms * ** subst_v_c_def  by simp
  qed
  thus ?thesis using * by auto
qed

lemma subtype_reflI:  
  assumes "\<lbrace> z1 : b | c1 \<rbrace>  =  \<lbrace> z2 : b | c2 \<rbrace>" and wf1: "\<Theta>; \<B>;\<Gamma> \<turnstile>\<^sub>w\<^sub>f (\<lbrace> z1 : b | c1 \<rbrace>)"
  shows "\<Theta>; \<B>; \<Gamma> \<turnstile>  (\<lbrace> z1 : b | c1 \<rbrace>)  \<lesssim>  (\<lbrace> z2 : b | c2 \<rbrace>)"
  using assms subtype_reflI2 by metis

nominal_function base_eq :: "\<Gamma> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> bool" where
  "base_eq _ \<lbrace> z1 : b1| c1 \<rbrace>  \<lbrace> z2 : b2 | c2 \<rbrace> = (b1 = b2)" 
  apply(auto,simp add: eqvt_def base_eq_graph_aux_def )
  by (meson \<tau>.exhaust)
nominal_termination (eqvt)  by lexicographic_order

lemma subtype_wfT:
  fixes t1::\<tau> and t2::\<tau>
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> t1 \<lesssim> t2" 
  shows "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f t1 \<and> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f t2"
  using assms subtype_elims by metis

lemma  subtype_eq_base:
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile>  (\<lbrace> z1 : b1| c1 \<rbrace>)  \<lesssim> (\<lbrace> z2 : b2 | c2 \<rbrace>)"
  shows "b1=b2"
  using subtype.simps  assms by auto

lemma subtype_eq_base2: 
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> t1  \<lesssim> t2"
  shows "b_of t1 = b_of t2"
  using assms proof(rule  subtype.induct[of \<Theta>  \<B> \<Gamma> t1 t2],goal_cases)
  case (1 \<Theta>  \<Gamma> z1 b c1 z2 c2 x)
  then show ?case using subtype_eq_base by auto
qed

lemma  subtype_wf: 
  fixes \<tau>1::\<tau> and \<tau>2::\<tau>
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile>  \<tau>1  \<lesssim>  \<tau>2" 
  shows "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>1 \<and>\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>2"
  using assms
proof(rule  subtype.induct[of \<Theta> \<B> \<Gamma> \<tau>1 \<tau>2],goal_cases)
  case (1 \<Theta>  \<Gamma>G z1 b c1 z2 c2 x)
  then show ?case by blast
qed

lemma  subtype_g_wf: 
  fixes \<tau>1::\<tau> and \<tau>2::\<tau> and \<Gamma>::\<Gamma>
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile>  \<tau>1  \<lesssim>  \<tau>2" 
  shows "\<Theta> ; \<B>\<turnstile>\<^sub>w\<^sub>f \<Gamma>"
  using assms
proof(rule  subtype.induct[of \<Theta> \<B> \<Gamma> \<tau>1 \<tau>2],goal_cases)
  case (1 \<Theta> \<B> \<Gamma> z1 b c1 z2 c2 x)
  then show ?case using wfX_wfY by auto
qed

text \<open> For when we have a particular y that satisfies  the freshness conditions that we want the validity check to use \<close>

lemma valid_flip_simple: 
  assumes "\<Theta>; \<B>; (z, b, c) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> c'" and  "atom z \<sharp> \<Gamma>" and "atom x \<sharp> (z, c, z, c', \<Gamma>)"
  shows "\<Theta>; \<B>; (x, b, (z \<leftrightarrow> x ) \<bullet> c) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> (z \<leftrightarrow> x ) \<bullet> c'"
proof -
  have "(z \<leftrightarrow> x ) \<bullet> \<Theta>; \<B>; (z \<leftrightarrow> x ) \<bullet> ((z, b,  c) #\<^sub>\<Gamma> \<Gamma>)  \<Turnstile> (z \<leftrightarrow> x ) \<bullet> c'"
    using True_eqvt valid.eqvt assms beta_flip_eq wfX_wfY by metis
  moreover have " \<turnstile>\<^sub>w\<^sub>f \<Theta>" using valid.simps wfC_wf wfG_wf assms by metis
  ultimately show ?thesis 
    using theta_flip_eq G_cons_flip_fresh3[of x \<Gamma> z b c]  assms fresh_Pair flip_commute by metis
qed

lemma valid_wf_all:
  assumes " \<Theta>; \<B>; (z0,b,c0)#\<^sub>\<Gamma>G \<Turnstile> c"   
  shows "wfG \<Theta> \<B> G" and "wfC \<Theta> \<B> ((z0,b,c0)#\<^sub>\<Gamma>G) c" and "atom z0 \<sharp> G"
  using valid.simps wfC_wf wfG_cons assms by metis+

lemma valid_wfT: 
  fixes z::x
  assumes " \<Theta>; \<B>; (z0,b,c0[z::=V_var z0]\<^sub>v)#\<^sub>\<Gamma>G \<Turnstile> c[z::=V_var z0]\<^sub>v" and "atom z0 \<sharp> (\<Theta>, \<B>, G,c,c0)"
  shows "\<Theta>; \<B>; G \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c0 \<rbrace>"    and  "\<Theta>; \<B>; G \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c \<rbrace>"
proof -
  have "atom z0 \<sharp> c0" using assms fresh_Pair by auto
  moreover have *:" \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f (z0,b,c0[z::=V_var z0]\<^sub>c\<^sub>v)#\<^sub>\<Gamma>G" using valid_wf_all wfX_wfY assms subst_v_c_def by metis
  ultimately show wft: "\<Theta>; \<B>; G \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c0 \<rbrace>"  using wfG_wfT[OF *] by auto

  have "atom z0 \<sharp> c" using assms fresh_Pair by auto
  moreover have wfc: "\<Theta>; \<B>; (z0,b,c0[z::=V_var z0]\<^sub>v)#\<^sub>\<Gamma>G  \<turnstile>\<^sub>w\<^sub>f c[z::=V_var z0]\<^sub>v" using valid_wf_all assms by metis
  have  "\<Theta>; \<B>; G \<turnstile>\<^sub>w\<^sub>f \<lbrace> z0 : b | c[z::=V_var z0]\<^sub>v \<rbrace>" proof
    show \<open>atom z0 \<sharp> (\<Theta>, \<B>, G)\<close> using assms fresh_prodN by simp
    show \<open> \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f b \<close> using wft wfT_wfB by force
    show \<open> \<Theta>; \<B>; (z0, b, TRUE) #\<^sub>\<Gamma> G   \<turnstile>\<^sub>w\<^sub>f c[z::=[ z0 ]\<^sup>v]\<^sub>v \<close> using wfc wfC_replace_inside[OF wfc, of GNil z0 b "c0[z::=[ z0 ]\<^sup>v]\<^sub>v" G C_true] wfC_trueI 
        append_g.simps 
      by (metis "local.*" wfG_elim2 wf_trans(2))
  qed
  moreover have "\<lbrace> z0 : b | c[z::=V_var z0]\<^sub>v \<rbrace> =  \<lbrace> z : b | c \<rbrace>" using \<open>atom z0 \<sharp> c0\<close> \<tau>.eq_iff  Abs1_eq_iff(3) 
    using calculation(1) subst_v_c_def by auto
  ultimately show   "\<Theta>; \<B>; G \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c \<rbrace>" by auto
qed

lemma valid_flip: 
  fixes c::c and z::x and z0::x and xx2::x
  assumes " \<Theta>; \<B>; (xx2, b, c0[z0::=V_var xx2]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> c[z::=V_var xx2]\<^sub>v" and 
    "atom xx2 \<sharp> (c0,\<Gamma>,c,z) " and "atom z0 \<sharp> (\<Gamma>,c,z)"
  shows " \<Theta>; \<B>; (z0, b, c0) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> c[z::=V_var z0]\<^sub>v"
proof -

  have " \<turnstile>\<^sub>w\<^sub>f \<Theta>" using assms valid_wf_all wfX_wfY by metis
  hence " \<Theta> ;  \<B> ; (xx2 \<leftrightarrow> z0 ) \<bullet> ((xx2, b, c0[z0::=V_var xx2]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>)  \<Turnstile> ((xx2 \<leftrightarrow> z0 ) \<bullet> c[z::=V_var xx2]\<^sub>v)"
    using valid.eqvt True_eqvt assms beta_flip_eq theta_flip_eq by metis
  hence " \<Theta>; \<B>; (((xx2 \<leftrightarrow> z0 ) \<bullet> xx2, b, (xx2 \<leftrightarrow> z0 ) \<bullet> c0[z0::=V_var xx2]\<^sub>v) #\<^sub>\<Gamma> (xx2 \<leftrightarrow> z0 ) \<bullet> \<Gamma>)  \<Turnstile> ((xx2 \<leftrightarrow> z0 ) \<bullet>(c[z::=V_var xx2]\<^sub>v))"
    using G_cons_flip[of xx2 z0 xx2 b "c0[z0::=V_var xx2]\<^sub>v" \<Gamma>] by auto
  moreover have "(xx2 \<leftrightarrow> z0 ) \<bullet> xx2 = z0" by simp
  moreover have "(xx2 \<leftrightarrow> z0 ) \<bullet> c0[z0::=V_var xx2]\<^sub>v = c0" 
    using assms subst_cv_v_flip[of xx2 c0 z0 "V_var z0"] assms fresh_prod4 by auto
  moreover have "(xx2 \<leftrightarrow> z0 ) \<bullet> \<Gamma> = \<Gamma>" proof -  
    have "atom xx2 \<sharp> \<Gamma>" using assms by auto
    moreover have "atom z0 \<sharp> \<Gamma>" using assms by auto
    ultimately show ?thesis using flip_fresh_fresh by auto
  qed
  moreover have "(xx2 \<leftrightarrow> z0 ) \<bullet> (c[z::=V_var xx2]\<^sub>v) =c[z::=V_var z0]\<^sub>v" 
    using subst_cv_v_flip3 assms by simp
  ultimately show ?thesis by auto
qed

lemma subtype_valid:
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> t1  \<lesssim> t2" and "atom y \<sharp> \<Gamma>" and "t1 = \<lbrace> z1 : b  | c1 \<rbrace>" and "t2 =  \<lbrace> z2 : b  | c2 \<rbrace>"
  shows  "\<Theta>; \<B>; ((y, b, c1[z1::=V_var y]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>) \<Turnstile> c2[z2::=V_var y]\<^sub>v"
  using assms proof(nominal_induct t2 avoiding: y rule: subtype.strong_induct)
  case (subtype_baseI x \<Theta> \<B> \<Gamma> z c z' c' ba)

  hence "(x \<leftrightarrow> y) \<bullet> \<Theta> ; (x \<leftrightarrow> y) \<bullet> \<B> ; (x \<leftrightarrow> y) \<bullet> ((x, ba, c[z::=[ x ]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>)  \<Turnstile> (x \<leftrightarrow> y) \<bullet> c'[z'::=[ x ]\<^sup>v]\<^sub>v" using valid.eqvt 
    using permute_boolI by blast
  moreover have  " \<turnstile>\<^sub>w\<^sub>f \<Theta>" using valid.simps wfC_wf wfG_wf subtype_baseI by metis
  ultimately have  "\<Theta>; \<B>;  ((y, ba, (x \<leftrightarrow> y) \<bullet> c[z::=[ x ]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>)  \<Turnstile> (x \<leftrightarrow> y) \<bullet> c'[z'::=[ x ]\<^sup>v]\<^sub>v" 
    using subtype_baseI theta_flip_eq beta_flip_eq \<tau>.eq_iff  G_cons_flip_fresh3[of y \<Gamma> x ba]  by (metis flip_commute)
  moreover have "(x \<leftrightarrow> y) \<bullet> c[z::=[ x ]\<^sup>v]\<^sub>v = c1[z1::=[ y ]\<^sup>v]\<^sub>v" 
    by (metis subtype_baseI permute_flip_cancel subst_cv_id subst_cv_v_flip3 subst_cv_var_flip type_eq_subst_eq wfT_fresh_c subst_v_c_def)
  moreover have  "(x \<leftrightarrow> y) \<bullet> c'[z'::=[ x ]\<^sup>v]\<^sub>v = c2[z2::=[ y ]\<^sup>v]\<^sub>v" 
    by (metis subtype_baseI permute_flip_cancel subst_cv_id subst_cv_v_flip3 subst_cv_var_flip type_eq_subst_eq wfT_fresh_c subst_v_c_def)

  ultimately show ?case using subtype_baseI \<tau>.eq_iff by metis
qed

lemma subtype_valid_simple:
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> t1  \<lesssim> t2" and "atom z \<sharp> \<Gamma>" and "t1 = \<lbrace> z : b  | c1 \<rbrace>" and "t2 =  \<lbrace> z : b  | c2 \<rbrace>"
  shows  "\<Theta>; \<B>; ((z, b, c1) #\<^sub>\<Gamma> \<Gamma>) \<Turnstile> c2"
  using subst_v_c_def subst_v_id assms subtype_valid[OF assms] by simp

lemma obtain_for_t_with_fresh:
  assumes "atom x \<sharp> t"
  shows "\<exists>b c. t = \<lbrace> x : b | c \<rbrace>"
proof -
  obtain z1 b1 c1 where *:" t =  \<lbrace> z1 : b1 | c1 \<rbrace> \<and> atom z1 \<sharp> t" using obtain_fresh_z by metis
  then have "t = (x \<leftrightarrow> z1) \<bullet> t" using flip_fresh_fresh assms by metis
  also have "... = \<lbrace> (x \<leftrightarrow> z1) \<bullet> z1 : (x \<leftrightarrow> z1) \<bullet> b1 | (x \<leftrightarrow> z1) \<bullet> c1 \<rbrace>" using * assms by simp
  also have "... = \<lbrace> x : b1 | (x \<leftrightarrow> z1) \<bullet> c1 \<rbrace>" using * assms by auto
  finally show ?thesis by auto
qed

lemma subtype_trans: 
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> \<tau>1 \<lesssim> \<tau>2" and "\<Theta>; \<B>; \<Gamma> \<turnstile> \<tau>2 \<lesssim> \<tau>3"
  shows "\<Theta>; \<B>; \<Gamma> \<turnstile> \<tau>1 \<lesssim> \<tau>3"
  using assms proof(nominal_induct  avoiding: \<tau>3 rule: subtype.strong_induct)
  case (subtype_baseI x \<Theta> \<B> \<Gamma> z c z' c' b)
  hence "b_of \<tau>3 = b" using  subtype_eq_base2 b_of.simps by metis
  then obtain z'' c'' where t3: "\<tau>3 = \<lbrace> z'' : b | c''\<rbrace> \<and> atom z'' \<sharp> x" 
    using obtain_fresh_z2 by metis
  hence xf: "atom x \<sharp> (z'', c'')" using fresh_prodN subtype_baseI \<tau>.fresh by auto
  have "\<Theta>; \<B>; \<Gamma> \<turnstile> \<lbrace> z : b  | c \<rbrace> \<lesssim> \<lbrace> z'' : b | c''\<rbrace>" 
  proof(rule Typing.subtype_baseI)
    show \<open>atom x \<sharp> (\<Theta>, \<B>, \<Gamma>, z, c, z'', c'')\<close> using t3 fresh_prodN subtype_baseI xf by simp
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b  | c \<rbrace> \<close> using subtype_baseI by auto
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z'' : b  | c'' \<rbrace> \<close> using subtype_baseI t3 subtype_elims by metis
    have " \<Theta>; \<B>; (x, b, c'[z'::=[ x ]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> c''[z''::=[ x ]\<^sup>v]\<^sub>v "
      using subtype_valid[OF \<open>\<Theta>; \<B>; \<Gamma>  \<turnstile> \<lbrace> z' : b  | c' \<rbrace> \<lesssim> \<tau>3\<close> , of x z' b c' z'' c''] subtype_baseI 
        t3 by simp
    thus \<open>\<Theta>; \<B>; (x, b, c[z::=[ x ]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> c''[z''::=[ x ]\<^sup>v]\<^sub>v \<close>
      using  valid_trans_full[of \<Theta> \<B> x b c z \<Gamma> c' z' c'' z'' ] subtype_baseI  t3 by simp
  qed
  thus ?case using t3 by simp
qed

lemma subtype_eq_e:
  assumes "\<forall>i s1 s2 G. wfG P \<B> G \<and> wfI P G i \<and> eval_e i e1 s1 \<and> eval_e i e2 s2 \<longrightarrow> s1 = s2"   and "atom z1 \<sharp> e1" and "atom z2 \<sharp> e2" and "atom z1 \<sharp> \<Gamma>" and "atom z2 \<sharp> \<Gamma>"
    and "wfCE P  \<B> \<Gamma>  e1 b" and "wfCE P  \<B> \<Gamma>  e2 b" 
  shows "P; \<B>; \<Gamma> \<turnstile> \<lbrace> z1 : b  | CE_val (V_var z1)  ==  e1 \<rbrace> \<lesssim> (\<lbrace> z2 : b  | CE_val (V_var z2)  ==  e2  \<rbrace>)"
proof -

  have "wfCE P  \<B> \<Gamma> e1 b" and "wfCE P  \<B> \<Gamma>  e2 b" using  assms by auto

  have wst1: "wfT P \<B> \<Gamma> (\<lbrace> z1 : b  | CE_val (V_var z1)  ==  e1  \<rbrace>)" 
    using wfC_e_eq  wfTI assms wfX_wfB wfG_fresh_x 
    by (simp add: wfT_e_eq)

  moreover have wst2:"wfT P \<B> \<Gamma> (\<lbrace> z2 : b  | CE_val (V_var z2)  ==  e2  \<rbrace>)" 
    using wfC_e_eq wfX_wfB wfTI assms wfG_fresh_x 
    by (simp add: wfT_e_eq)

  moreover obtain x::x where xf: "atom x \<sharp> (P,  \<B> , z1, CE_val (V_var z1)  ==  e1 , z2, CE_val (V_var z2)  ==  e2 , \<Gamma>)" using obtain_fresh by blast
  moreover have vld: "P; \<B> ; (x, b, (CE_val (V_var z1)  ==  e1 )[z1::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> (CE_val (V_var z2)  ==  e2 )[z2::=V_var x]\<^sub>v "  (is "P; \<B> ; ?G \<Turnstile> ?c")
  proof -

    have wbg: "P; \<B> \<turnstile>\<^sub>w\<^sub>f ?G  \<and> P ;  \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and>  toSet \<Gamma> \<subseteq> toSet ?G"  proof -        
      have "P; \<B> \<turnstile>\<^sub>w\<^sub>f ?G"  proof(rule wfG_consI) 
        show "P; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>" using assms wfX_wfY by metis
        show "atom x \<sharp> \<Gamma>" using xf by auto
        show "P; \<B>  \<turnstile>\<^sub>w\<^sub>f b " using assms(6) wfX_wfB by auto
        show "P; \<B> ; (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f (CE_val (V_var z1)  ==  e1 )[z1::=V_var x]\<^sub>v " 
          using wfC_e_eq[OF assms(6)] wf_subst(2)
          by (simp add: \<open>atom x \<sharp> \<Gamma>\<close> assms(2) subst_v_c_def)
      qed
      moreover hence  "P; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>" using wfG_elims by metis
      ultimately show ?thesis using toSet.simps by auto 
    qed

    have wsc: "wfC P \<B> ?G ?c" proof -
      have "wfCE P \<B> ?G  (CE_val (V_var x)) b" proof      
        show \<open> P; \<B> ; (x, b, (CE_val (V_var z1)  ==  e1 )[z1::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_var x : b \<close> using wfV_varI lookup.simps wbg by auto
      qed
      moreover have "wfCE P \<B> ?G e2 b" using wf_weakening assms wbg by metis
      ultimately have "wfC P \<B> ?G  (CE_val (V_var x)  ==  e2 )" using wfC_eqI by simp
      thus ?thesis using subst_cv.simps(6) \<open>atom z2 \<sharp> e2\<close> subst_v_c_def by simp
    qed

    moreover have "\<forall>i. wfI P ?G i \<and> is_satis_g i ?G \<longrightarrow> is_satis i ?c" proof(rule allI , rule impI)
      fix i
      assume as: "wfI P ?G i \<and> is_satis_g i ?G" 
      hence "is_satis i  ((CE_val (V_var z1)  ==  e1 )[z1::=V_var x]\<^sub>v)" 
        by (simp add: is_satis_g.simps(2))
      hence "is_satis i  (CE_val (V_var x)  ==  e1 )" using subst_cv.simps assms subst_v_c_def by auto
      then obtain s1 and s2 where *:"eval_e i (CE_val (V_var x)) s1 \<and> eval_e i e1 s2 \<and> s1=s2" using is_satis.simps eval_c_elims by metis
      moreover hence "eval_e i e2 s1" proof -
        have **:"wfI P ?G i" using as by auto
        moreover have "wfCE  P \<B> ?G e1 b \<and> wfCE  P \<B> ?G  e2 b" using assms xf wf_weakening wbg by metis
        moreover then  obtain s2' where "eval_e i e2 s2'" using assms wfI_wfCE_eval_e ** by metis
        ultimately show ?thesis using * assms(1) wfX_wfY by metis
      qed
      ultimately have  "is_satis i  (CE_val (V_var x)  ==  e2 )" using is_satis.simps eval_c_eqI by force
      thus "is_satis i  ((CE_val (V_var z2)  ==  e2 )[z2::=V_var x]\<^sub>v)"  using is_satis.simps eval_c_eqI assms subst_cv.simps subst_v_c_def by auto
    qed
    ultimately show ?thesis using valid.simps by simp
  qed
  moreover have "atom x \<sharp> (P, \<B>, \<Gamma>,  z1 ,  CE_val (V_var z1)  ==  e1, z2,  CE_val (V_var z2)  ==  e2 ) " 
    unfolding fresh_prodN using  xf fresh_prod7 \<tau>.fresh by fast
  ultimately show ?thesis using subtype_baseI[OF _ wst1 wst2  vld] xf by simp
qed

lemma subtype_eq_e_nil:
  assumes  "\<forall>i s1 s2 G. wfG P \<B> G \<and> wfI P G i \<and> eval_e i e1 s1 \<and> eval_e i e2 s2 \<longrightarrow> s1 = s2" and "supp e1 = {}" and "supp e2 = {}" and "wfTh P" 
    and "wfCE  P  \<B> GNil  e1 b" and "wfCE  P  \<B> GNil  e2 b"  and "atom z1 \<sharp> GNil" and "atom z2 \<sharp> GNil"
  shows "P; \<B> ; GNil  \<turnstile> \<lbrace> z1 : b  | CE_val (V_var z1)  ==  e1 \<rbrace> \<lesssim> (\<lbrace> z2 : b  | CE_val (V_var z2)  ==  e2  \<rbrace>)"
  apply(rule subtype_eq_e,auto simp add: assms e.fresh)
  using  assms fresh_def e.fresh  supp_GNil by metis+

lemma subtype_gnil_fst_aux:
  assumes "supp v\<^sub>1 = {}" and "supp (V_pair v\<^sub>1 v\<^sub>2) = {}" and "wfTh P" and "wfCE  P \<B> GNil (CE_val v\<^sub>1) b" and "wfCE  P \<B> GNil  (CE_fst [V_pair v\<^sub>1 v\<^sub>2]\<^sup>c\<^sup>e) b" and 
    "wfCE  P \<B> GNil  (CE_val v\<^sub>2) b2"  and "atom z1 \<sharp> GNil" and "atom z2 \<sharp> GNil"
  shows "P; \<B> ; GNil  \<turnstile> (\<lbrace> z1 : b | CE_val (V_var z1)  ==  CE_val v\<^sub>1  \<rbrace>) \<lesssim> (\<lbrace> z2 : b | CE_val (V_var z2)  ==  CE_fst [V_pair v\<^sub>1 v\<^sub>2]\<^sup>c\<^sup>e \<rbrace>)"
proof - 
  have "\<forall>i s1 s2 G . wfG P \<B> G \<and> wfI P G i \<and> eval_e i ( CE_val v\<^sub>1) s1 \<and> eval_e i  (CE_fst [V_pair v\<^sub>1 v\<^sub>2]\<^sup>c\<^sup>e) s2 \<longrightarrow> s1 = s2" proof(rule+) 
    fix i s1 s2 G
    assume as: "wfG P \<B> G \<and> wfI P G i \<and> eval_e i (CE_val v\<^sub>1) s1 \<and> eval_e i (CE_fst [V_pair v\<^sub>1 v\<^sub>2]\<^sup>c\<^sup>e) s2"
    hence "wfCE  P \<B> G  (CE_val v\<^sub>2) b2" using assms wf_weakening 
      by (metis empty_subsetI toSet.simps(1))
    then obtain s3 where "eval_e i (CE_val v\<^sub>2) s3" using wfI_wfCE_eval_e as by metis
    hence "eval_v i ((V_pair  v\<^sub>1 v\<^sub>2)) (SPair s1 s3)"
      by (meson as eval_e_elims(1) eval_v_pairI)
    hence "eval_e i (CE_fst [V_pair v\<^sub>1 v\<^sub>2]\<^sup>c\<^sup>e) s1" using eval_e_fstI eval_e_valI by metis
    show "s1 = s2" using as eval_e_uniqueness
      using \<open>eval_e i (CE_fst [V_pair v\<^sub>1 v\<^sub>2]\<^sup>c\<^sup>e) s1\<close> by auto
  qed
  thus ?thesis using subtype_eq_e_nil  ce.supp assms by auto
qed

lemma subtype_gnil_snd_aux:
  assumes "supp v\<^sub>2 = {}" and "supp (V_pair v\<^sub>1 v\<^sub>2) = {}" and "wfTh P" and "wfCE  P \<B> GNil  (CE_val v\<^sub>2) b" and 
    "wfCE  P \<B> GNil  (CE_snd [(V_pair v\<^sub>1 v\<^sub>2)]\<^sup>c\<^sup>e) b" and 
    "wfCE  P \<B> GNil  (CE_val v\<^sub>1) b2"  and "atom z1 \<sharp> GNil" and "atom z2 \<sharp> GNil"
  shows "P; \<B> ; GNil  \<turnstile> (\<lbrace> z1 : b | CE_val (V_var z1)  ==  CE_val v\<^sub>2  \<rbrace>) \<lesssim> (\<lbrace> z2 : b | CE_val (V_var z2)  ==  CE_snd [(V_pair v\<^sub>1 v\<^sub>2)]\<^sup>c\<^sup>e \<rbrace>)"
proof - 
  have "\<forall>i s1 s2 G. wfG P \<B> G \<and> wfI P G i \<and> eval_e i ( CE_val v\<^sub>2) s1 \<and> eval_e i  (CE_snd [(V_pair v\<^sub>1 v\<^sub>2)]\<^sup>c\<^sup>e) s2 \<longrightarrow> s1 = s2" proof(rule+) 
    fix i s1 s2 G
    assume as: " wfG P \<B> G \<and> wfI P G i \<and> eval_e i (CE_val v\<^sub>2) s1 \<and> eval_e i (CE_snd [(V_pair v\<^sub>1 v\<^sub>2)]\<^sup>c\<^sup>e) s2"
    hence "wfCE  P \<B> G  (CE_val v\<^sub>1) b2" using assms wf_weakening 
      by (metis empty_subsetI toSet.simps(1))
    then obtain s3 where "eval_e i (CE_val v\<^sub>1) s3" using wfI_wfCE_eval_e as by metis
    hence "eval_v i ((V_pair  v\<^sub>1 v\<^sub>2)) (SPair s3 s1)"
      by (meson as eval_e_elims eval_v_pairI)
    hence "eval_e i (CE_snd [(V_pair v\<^sub>1 v\<^sub>2)]\<^sup>c\<^sup>e) s1" using eval_e_sndI eval_e_valI by metis
    show "s1 = s2" using as eval_e_uniqueness
      using \<open>eval_e i (CE_snd [V_pair v\<^sub>1 v\<^sub>2]\<^sup>c\<^sup>e) s1\<close> by auto
  qed
  thus ?thesis using assms subtype_eq_e_nil  by (simp add: ce.supp ce.supp)
qed

lemma subtype_gnil_fst:
  assumes "\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f  [#1[[v\<^sub>1,v\<^sub>2]\<^sup>v]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e : b" 
  shows "\<Theta> ;  {||} ; GNil  \<turnstile> (\<lbrace> z\<^sub>1 : b | [[z\<^sub>1]\<^sup>v]\<^sup>c\<^sup>e ==  [v\<^sub>1]\<^sup>c\<^sup>e  \<rbrace>) \<lesssim> 
        (\<lbrace> z\<^sub>2 : b | [[z\<^sub>2]\<^sup>v]\<^sup>c\<^sup>e ==   [#1[[v\<^sub>1, v\<^sub>2]\<^sup>v]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e \<rbrace>)"
proof  -
  obtain b2 where **:" \<Theta> ;   {||} ; GNil \<turnstile>\<^sub>w\<^sub>f V_pair v\<^sub>1 v\<^sub>2 : B_pair b b2" using wfCE_elims(4)[OF assms ] wfCE_elims by metis
  obtain b1' b2' where *:"B_pair b b2 = B_pair b1' b2' \<and>  \<Theta> ;   {||} ; GNil \<turnstile>\<^sub>w\<^sub>f v\<^sub>1 : b1'  \<and>  \<Theta> ;   {||} ; GNil \<turnstile>\<^sub>w\<^sub>f v\<^sub>2 : b2'" 
    using wfV_elims(3)[OF **] by metis

  show ?thesis proof(rule subtype_gnil_fst_aux)
    show \<open>supp v\<^sub>1 = {}\<close> using * wfV_supp_nil by auto
    show \<open>supp (V_pair v\<^sub>1 v\<^sub>2) = {}\<close> using ** wfV_supp_nil e.supp by metis
    show \<open>\<turnstile>\<^sub>w\<^sub>f \<Theta>\<close> using assms wfX_wfY   by metis
    show \<open>\<Theta>; {||}; GNil  \<turnstile>\<^sub>w\<^sub>f CE_val v\<^sub>1 : b \<close> using  wfCE_valI  "*" by auto
    show \<open>\<Theta>; {||}; GNil  \<turnstile>\<^sub>w\<^sub>f CE_fst [V_pair v\<^sub>1 v\<^sub>2]\<^sup>c\<^sup>e : b \<close> using assms by auto
    show \<open>\<Theta>; {||}; GNil  \<turnstile>\<^sub>w\<^sub>f CE_val v\<^sub>2 : b2 \<close>using  wfCE_valI  "*" by auto
    show \<open>atom z\<^sub>1 \<sharp> GNil\<close> using fresh_GNil by metis
    show \<open>atom z\<^sub>2 \<sharp> GNil\<close> using fresh_GNil by metis
  qed
qed

lemma subtype_gnil_snd:
  assumes "wfCE  P  {||} GNil  (CE_snd ([V_pair v\<^sub>1 v\<^sub>2]\<^sup>c\<^sup>e)) b" 
  shows "P ;  {||} ; GNil  \<turnstile> (\<lbrace> z1 : b | CE_val (V_var z1)  ==  CE_val v\<^sub>2  \<rbrace>) \<lesssim> (\<lbrace> z2 : b | CE_val (V_var z2)  ==  CE_snd [(V_pair v\<^sub>1 v\<^sub>2)]\<^sup>c\<^sup>e \<rbrace>)"
proof  -
  obtain b1 where **:" P ;   {||} ; GNil \<turnstile>\<^sub>w\<^sub>f V_pair v\<^sub>1 v\<^sub>2 : B_pair b1 b " using wfCE_elims assms by metis
  obtain b1' b2' where *:"B_pair b1 b = B_pair b1' b2' \<and>  P ;   {||} ; GNil \<turnstile>\<^sub>w\<^sub>f v\<^sub>1 : b1'  \<and>  P ;   {||} ; GNil \<turnstile>\<^sub>w\<^sub>f v\<^sub>2 : b2'" using wfV_elims(3)[OF **] by metis

  show ?thesis proof(rule subtype_gnil_snd_aux)
    show \<open>supp v\<^sub>2 = {}\<close> using * wfV_supp_nil by auto
    show \<open>supp (V_pair v\<^sub>1 v\<^sub>2) = {}\<close> using ** wfV_supp_nil e.supp by metis
    show \<open>\<turnstile>\<^sub>w\<^sub>f P\<close> using assms wfX_wfY  by metis
    show \<open>P; {||}; GNil  \<turnstile>\<^sub>w\<^sub>f CE_val v\<^sub>1 : b1 \<close> using wfCE_valI   "*" by simp
    show \<open>P; {||}; GNil  \<turnstile>\<^sub>w\<^sub>f CE_snd [(V_pair v\<^sub>1 v\<^sub>2)]\<^sup>c\<^sup>e : b \<close> using assms by auto
    show \<open>P; {||}; GNil  \<turnstile>\<^sub>w\<^sub>f CE_val v\<^sub>2 : b \<close>using  wfCE_valI  "*" by simp
    show \<open>atom z1 \<sharp> GNil\<close> using fresh_GNil by metis
    show \<open>atom z2 \<sharp> GNil\<close> using fresh_GNil by metis
  qed
qed

lemma subtype_fresh_tau:
  fixes x::x
  assumes "atom x \<sharp> t1" and "atom x \<sharp>  \<Gamma>" and "P; \<B>; \<Gamma> \<turnstile> t1 \<lesssim> t2"
  shows "atom x \<sharp> t2"
proof -
  have wfg: "P; \<B> \<turnstile>\<^sub>w\<^sub>f  \<Gamma>" using subtype_wf wfX_wfY  assms by metis
  have wft: "wfT P \<B> \<Gamma> t2" using subtype_wf wfX_wfY assms by blast
  hence "supp t2 \<subseteq> atom_dom \<Gamma> \<union> supp \<B>" using wf_supp 
    using atom_dom.simps by auto
  moreover have "atom x \<notin> atom_dom \<Gamma>" using \<open>atom x \<sharp> \<Gamma>\<close> wfG_atoms_supp_eq wfg fresh_def by blast 
  ultimately show "atom x \<sharp> t2" using fresh_def
    by (metis Un_iff contra_subsetD x_not_in_b_set)
qed

lemma subtype_if_simp:
  assumes "wfT P \<B> GNil (\<lbrace> z1 : b  | CE_val (V_lit l )  ==  CE_val (V_lit l)   IMP  c[z::=V_var z1]\<^sub>v  \<rbrace>)" and
    "wfT P \<B> GNil (\<lbrace> z : b  | c \<rbrace>)" and "atom z1 \<sharp> c"
  shows  "P; \<B> ; GNil \<turnstile> (\<lbrace> z1 : b  | CE_val (V_lit l)  ==  CE_val (V_lit l)  IMP  c[z::=V_var z1]\<^sub>v  \<rbrace>) \<lesssim>  (\<lbrace> z : b | c \<rbrace>)" 
proof -
  obtain x::x where xx: "atom x \<sharp> ( P , \<B> , z1, CE_val (V_lit l)  ==  CE_val (V_lit l)   IMP  c[z::=V_var z1]\<^sub>v , z, c, GNil)" using obtain_fresh_z by blast
  hence xx2: " atom x \<sharp> (CE_val (V_lit l)  ==  CE_val (V_lit l)   IMP  c[z::=V_var z1]\<^sub>v , c, GNil)" using fresh_prod7 fresh_prod3 by fast
  have *:"P; \<B> ; (x, b, (CE_val (V_lit l)  ==  CE_val (V_lit l)   IMP  c[z::=V_var z1]\<^sub>v )[z1::=V_var x]\<^sub>v) #\<^sub>\<Gamma> GNil  \<Turnstile> c[z::=V_var x]\<^sub>v " (is "P; \<B> ; ?G \<Turnstile> ?c" ) proof -
    have "wfC P \<B> ?G ?c"  using wfT_wfC_cons[OF assms(1) assms(2),of x] xx fresh_prod5 fresh_prod3 subst_v_c_def by metis
    moreover have "(\<forall>i. wfI P ?G i \<and> is_satis_g i ?G \<longrightarrow> is_satis i ?c)" proof(rule allI, rule impI)
      fix i
      assume as1: "wfI P ?G i \<and> is_satis_g i ?G" 
      have "((CE_val (V_lit l)  ==  CE_val (V_lit l)   IMP  c[z::=V_var z1]\<^sub>v )[z1::=V_var x]\<^sub>v) =  ((CE_val (V_lit l)  ==  CE_val (V_lit l) IMP  c[z::=V_var x]\<^sub>v ))" 
        using assms subst_v_c_def by auto
      hence "is_satis i ((CE_val (V_lit l)  ==  CE_val (V_lit l) IMP  c[z::=V_var x]\<^sub>v ))" using is_satis_g.simps as1 by presburger
      moreover have "is_satis i ((CE_val (V_lit l)  ==  CE_val (V_lit l)))" using is_satis.simps eval_c_eqI[of i "(CE_val (V_lit l))" "eval_l l"] eval_e_uniqueness 
          eval_e_valI eval_v_litI by metis
      ultimately show  "is_satis i ?c" using  is_satis_mp[of i] by metis
    qed
    ultimately show ?thesis using valid.simps by simp
  qed
  moreover have "atom x \<sharp> (P, \<B>, GNil,  z1 ,  CE_val (V_lit l)  ==  CE_val (V_lit l)   IMP  c[z::=V_var z1]\<^sub>v  ,  z, c )" 
    unfolding fresh_prod5 \<tau>.fresh using xx fresh_prodN x_fresh_b by metis
  ultimately show ?thesis using subtype_baseI assms xx xx2  by metis
qed

lemma subtype_if:
  assumes "P; \<B>; \<Gamma> \<turnstile> \<lbrace> z : b  | c \<rbrace> \<lesssim> \<lbrace> z' : b  | c' \<rbrace>" and 
    "wfT P \<B> \<Gamma> (\<lbrace> z1 : b  | CE_val v  ==  CE_val (V_lit l) IMP  c[z::=V_var z1]\<^sub>v  \<rbrace>)"  and
    "wfT P \<B> \<Gamma> (\<lbrace> z2 : b  | CE_val v  ==  CE_val (V_lit l) IMP  c'[z'::=V_var z2]\<^sub>v  \<rbrace>)" and 
    "atom z1 \<sharp> v" and  "atom z \<sharp> \<Gamma>" and "atom z1 \<sharp> c" and "atom z2 \<sharp> c'" and "atom z2 \<sharp> v"
  shows   "P; \<B> ; \<Gamma> \<turnstile> \<lbrace> z1 : b  | CE_val v  ==  CE_val (V_lit l)   IMP  c[z::=V_var z1]\<^sub>v  \<rbrace> \<lesssim> \<lbrace> z2 : b  | CE_val v  ==  CE_val (V_lit l) IMP  c'[z'::=V_var z2]\<^sub>v  \<rbrace>"
proof -
  obtain x::x where xx: "atom x \<sharp> (P,\<B>,z,c,z', c', z1, CE_val v  ==  CE_val (V_lit l) IMP  c[z::=V_var z1]\<^sub>v , z2, CE_val v  ==  CE_val (V_lit l) IMP  c'[z'::=V_var z2]\<^sub>v , \<Gamma>)" 
    using obtain_fresh_z by blast
  hence xf: "atom x \<sharp> (z, c, z', c', \<Gamma>)" by simp
  have xf2: "atom x \<sharp> (z1, CE_val v  ==  CE_val (V_lit l) IMP c[z::=V_var z1]\<^sub>v , z2, CE_val v  ==  CE_val (V_lit l)   IMP  c'[z'::=V_var z2]\<^sub>v , \<Gamma>)" 
    using xx fresh_prod4 fresh_prodN by metis

  moreover have "P; \<B> ; (x, b, (CE_val v  ==  CE_val (V_lit l)   IMP  c[z::=V_var z1]\<^sub>v )[z1::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> (CE_val v  ==  CE_val (V_lit l)   IMP  c'[z'::=V_var z2]\<^sub>v )[z2::=V_var x]\<^sub>v" 
    (is "P; \<B> ; ?G \<Turnstile> ?c" )
  proof -
    have wbc: "wfC P \<B> ?G ?c" using  assms xx fresh_prod4 fresh_prod2 wfT_wfC_cons assms subst_v_c_def by metis

    moreover have "\<forall>i. wfI P ?G i \<and> is_satis_g i ?G \<longrightarrow> is_satis i ?c" proof(rule allI, rule impI)
      fix i
      assume a1: "wfI P ?G i \<and> is_satis_g i ?G"

      have *: " is_satis i ((CE_val v  ==  CE_val (V_lit l))) \<longrightarrow> is_satis i ((c'[z'::=V_var z2]\<^sub>v )[z2::=V_var x]\<^sub>v)" 
      proof 
        assume a2: "is_satis i ((CE_val v  ==  CE_val (V_lit l)))" 

        have "is_satis i ((CE_val v  ==  CE_val (V_lit l)   IMP  (c[z::=V_var z1]\<^sub>v ))[z1::=V_var x]\<^sub>v)" 
          using a1 is_satis_g.simps  by simp
        moreover have "((CE_val v  ==  CE_val (V_lit l)  IMP  (c[z::=V_var z1]\<^sub>v ))[z1::=V_var x]\<^sub>v) =  (CE_val v  ==  CE_val (V_lit l)   IMP  ((c[z::=V_var z1]\<^sub>v )[z1::=V_var x]\<^sub>v))" 
          using  assms subst_v_c_def by simp
        ultimately have "is_satis i (CE_val v  ==  CE_val (V_lit l) IMP  ((c[z::=V_var z1]\<^sub>v )[z1::=V_var x]\<^sub>v))" by argo

        hence  "is_satis i  ((c[z::=V_var z1]\<^sub>v )[z1::=V_var x]\<^sub>v)" using a2 is_satis_mp by auto
        moreover have "((c[z::=V_var z1]\<^sub>v )[z1::=V_var x]\<^sub>v) =  ((c[z::=V_var x]\<^sub>v ))" using assms by auto
        ultimately have  "is_satis i ((c[z::=V_var x]\<^sub>v ))"  using a2 is_satis.simps by auto

        hence "is_satis_g i ((x,b,(c[z::=V_var x]\<^sub>v )) #\<^sub>\<Gamma> \<Gamma>)" using a1 is_satis_g.simps by meson
        moreover have "wfI P ((x,b,(c[z::=V_var x]\<^sub>v )) #\<^sub>\<Gamma> \<Gamma>) i" proof -
          obtain s where "Some s = i x \<and> wfRCV P s b \<and> wfI P \<Gamma> i" using wfI_def a1 by auto
          thus ?thesis using wfI_def by auto
        qed
        ultimately have  "is_satis i ((c'[z'::=V_var x]\<^sub>v))" using subtype_valid assms(1) xf valid.simps by simp

        moreover have "(c'[z'::=V_var x]\<^sub>v) = ((c'[z'::=V_var z2]\<^sub>v )[z2::=V_var x]\<^sub>v)" using assms by auto
        ultimately show "is_satis i ((c'[z'::=V_var z2]\<^sub>v )[z2::=V_var x]\<^sub>v)" by auto
      qed

      moreover have "?c =  ((CE_val v  ==  CE_val (V_lit l))  IMP  ((c'[z'::=V_var z2]\<^sub>v )[z2::=V_var x]\<^sub>v))" 
        using  assms subst_v_c_def by simp

      moreover have "\<exists>b1 b2. eval_c i (CE_val v  ==  CE_val (V_lit l) ) b1 \<and> 
                     eval_c i c'[z'::=V_var z2]\<^sub>v[z2::=V_var x]\<^sub>v b2" proof -

        have "wfC P \<B> ?G (CE_val v  ==  CE_val (V_lit l))"  using wbc wfC_elims(7) assms subst_cv.simps subst_v_c_def by fastforce

        moreover have "wfC P \<B> ?G (c'[z'::=V_var z2]\<^sub>v[z2::=V_var x]\<^sub>v)" proof(rule wfT_wfC_cons)
          show \<open> P; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z1 : b  | CE_val v  ==  CE_val (V_lit l)   IMP  (c[z::=V_var z1]\<^sub>v)  \<rbrace> \<close> using assms subst_v_c_def by auto
          have " \<lbrace> z2 : b  | c'[z'::=V_var z2]\<^sub>v \<rbrace> =  \<lbrace> z' : b  | c' \<rbrace>" using assms subst_v_c_def by auto
          thus  \<open> P; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z2 : b  | c'[z'::=V_var z2]\<^sub>v \<rbrace> \<close> using assms subtype_elims by metis
          show \<open>atom x \<sharp> (CE_val v  ==  CE_val (V_lit l)   IMP  c[z::=V_var z1]\<^sub>v , c'[z'::=V_var z2]\<^sub>v, \<Gamma>)\<close> using xx fresh_Pair c.fresh by metis
        qed

        ultimately show ?thesis using wfI_wfC_eval_c a1 subst_v_c_def by simp
      qed

      ultimately show "is_satis i ?c" using is_satis_imp[OF *] by auto
    qed
    ultimately show  ?thesis using valid.simps by simp
  qed
  moreover have "atom x \<sharp> (P, \<B>, \<Gamma>, z1 ,  CE_val v  ==  CE_val (V_lit l)   IMP  c[z::=V_var z1]\<^sub>v  ,  z2 , CE_val v  ==  CE_val (V_lit l)   IMP  c'[z'::=V_var z2]\<^sub>v )" 
    unfolding fresh_prod5 \<tau>.fresh using xx xf2 fresh_prodN x_fresh_b by metis
  ultimately show ?thesis using subtype_baseI assms  xf2 by metis 
qed

lemma eval_e_concat_eq:
  assumes  "wfI \<Theta> \<Gamma> i" 
  shows "\<exists>s. eval_e i (CE_val (V_lit (L_bitvec (v1 @ v2))) ) s \<and> eval_e i (CE_concat [(V_lit (L_bitvec v1))]\<^sup>c\<^sup>e [(V_lit (L_bitvec v2))]\<^sup>c\<^sup>e) s"
  using eval_e_valI eval_e_concatI eval_v_litI eval_l.simps by metis

lemma is_satis_eval_e_eq_imp:
  assumes "wfI \<Theta> \<Gamma> i" and "eval_e i e1 s" and "eval_e i e2 s"
    and  "is_satis i (CE_val (V_var x) == e1)"  (is "is_satis i ?c1")
  shows "is_satis i (CE_val (V_var x) == e2)"
proof -
  have *:"eval_c i ?c1 True" using assms is_satis.simps by blast
  hence "eval_e i (CE_val (V_var x)) s" using assms is_satis.simps eval_c_elims
    by (metis (full_types) eval_e_uniqueness)
  thus ?thesis using is_satis.simps eval_c.intros assms by fastforce
qed

lemma valid_eval_e_eq:
  fixes e1::ce and e2::ce
  assumes "\<forall>\<Gamma> i. wfI \<Theta> \<Gamma> i \<longrightarrow> (\<exists>s. eval_e i e1 s \<and> eval_e i e2 s)" and "\<Theta>; \<B>; GNil  \<turnstile>\<^sub>w\<^sub>f e1 : b " and  "\<Theta>; \<B>; GNil  \<turnstile>\<^sub>w\<^sub>f e2 : b"
  shows    "\<Theta>; \<B>; (x, b, (CE_val (V_var x)  ==  e1 )) #\<^sub>\<Gamma>  GNil  \<Turnstile> (CE_val (V_var x)  ==  e2) "
proof(rule validI)
  show "\<Theta>; \<B>; (x, b, CE_val (V_var x)  ==  e1 ) #\<^sub>\<Gamma> GNil  \<turnstile>\<^sub>w\<^sub>f CE_val (V_var x)  ==  e2" 
  proof
    have " \<Theta> ;  \<B> ; (x, b, TRUE )#\<^sub>\<Gamma>GNil \<turnstile>\<^sub>w\<^sub>f CE_val (V_var x)  ==  e1" using assms wfC_eqI wfE_valI wfV_varI wfX_wfY 
      by (simp add: fresh_GNil wfC_e_eq)    
    hence "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f (x, b, CE_val (V_var x)  ==  e1 ) #\<^sub>\<Gamma> GNil" using wfG_consI fresh_GNil wfX_wfY assms wfX_wfB by metis
    thus "\<Theta>; \<B>; (x, b, CE_val (V_var x)  ==  e1 ) #\<^sub>\<Gamma> GNil  \<turnstile>\<^sub>w\<^sub>f CE_val (V_var x) : b " using  wfCE_valI wfV_varI wfX_wfY 
        lookup.simps  assms wfX_wfY by simp
    show "\<Theta>; \<B>; (x, b, CE_val (V_var x)  ==  e1 ) #\<^sub>\<Gamma> GNil  \<turnstile>\<^sub>w\<^sub>f e2 : b " using assms wf_weakening wfX_wfY 
      by (metis (full_types) \<open>\<Theta>; \<B>; (x, b, CE_val (V_var x) == e1 ) #\<^sub>\<Gamma> GNil  \<turnstile>\<^sub>w\<^sub>f CE_val (V_var x) : b\<close> empty_iff subsetI toSet.simps(1))
  qed
  show " \<forall>i. wfI \<Theta> ((x, b, CE_val (V_var x)  ==  e1 ) #\<^sub>\<Gamma> GNil) i \<and> is_satis_g i ((x, b, CE_val (V_var x)  ==  e1 ) #\<^sub>\<Gamma> GNil) \<longrightarrow> is_satis i (CE_val (V_var x)  ==  e2 )"
  proof(rule,rule)
    fix i
    assume "wfI \<Theta> ((x, b, CE_val (V_var x)  ==  e1 ) #\<^sub>\<Gamma> GNil) i \<and> is_satis_g i ((x, b, CE_val (V_var x)  ==  e1 ) #\<^sub>\<Gamma> GNil)"
    moreover then obtain s where "eval_e i e1 s \<and> eval_e i e2 s" using assms by auto
    ultimately show "is_satis i (CE_val (V_var x)  ==  e2 )" using assms  is_satis_eval_e_eq_imp is_satis_g.simps by meson
  qed
qed

lemma subtype_concat:
  assumes " \<turnstile>\<^sub>w\<^sub>f \<Theta>"
  shows "\<Theta>; \<B>; GNil  \<turnstile> \<lbrace> z : B_bitvec  | CE_val (V_var z)  ==  CE_val (V_lit (L_bitvec (v1 @ v2)))  \<rbrace> \<lesssim> 
            \<lbrace> z : B_bitvec  | CE_val (V_var z)  ==  CE_concat [(V_lit (L_bitvec v1))]\<^sup>c\<^sup>e [(V_lit (L_bitvec v2))]\<^sup>c\<^sup>e  \<rbrace>" (is "\<Theta>; \<B>; GNil  \<turnstile> ?t1 \<lesssim> ?t2")
proof -
  obtain x::x where x: "atom x \<sharp> (\<Theta>, \<B>, GNil,  z , CE_val (V_var z)  ==  CE_val (V_lit (L_bitvec (v1 @ v2))),
            z , CE_val (V_var z)  ==  CE_concat [V_lit (L_bitvec v1)]\<^sup>c\<^sup>e [V_lit (L_bitvec v2)]\<^sup>c\<^sup>e )" 
    (is "?xfree" )
    using obtain_fresh by auto

  have wb1: "\<Theta>; \<B>; GNil  \<turnstile>\<^sub>w\<^sub>f CE_val (V_lit (L_bitvec (v1 @ v2))) : B_bitvec" using wfX_wfY wfCE_valI wfV_litI assms base_for_lit.simps wfG_nilI by metis
  hence wb2: "\<Theta>; \<B>; GNil  \<turnstile>\<^sub>w\<^sub>f CE_concat [(V_lit (L_bitvec v1))]\<^sup>c\<^sup>e [(V_lit (L_bitvec v2))]\<^sup>c\<^sup>e : B_bitvec" 
    using wfCE_concatI wfX_wfY wfV_litI base_for_lit.simps wfCE_valI by metis

  show ?thesis proof
    show " \<Theta>; \<B>; GNil  \<turnstile>\<^sub>w\<^sub>f ?t1" using wfT_e_eq fresh_GNil wb1 wb2 by metis
    show " \<Theta>; \<B>; GNil  \<turnstile>\<^sub>w\<^sub>f ?t2" using wfT_e_eq fresh_GNil wb1 wb2 by metis
    show ?xfree using x by auto
    show "\<Theta>; \<B>; (x, B_bitvec, (CE_val (V_var z)  ==  CE_val (V_lit (L_bitvec (v1 @ v2))) )[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma>
           GNil  \<Turnstile> (CE_val (V_var z)  ==  CE_concat [(V_lit (L_bitvec v1))]\<^sup>c\<^sup>e [(V_lit (L_bitvec v2))]\<^sup>c\<^sup>e )[z::=V_var x]\<^sub>v " 
      using valid_eval_e_eq eval_e_concat_eq wb1 wb2 subst_v_c_def by fastforce
  qed
qed

lemma subtype_len:
  assumes " \<turnstile>\<^sub>w\<^sub>f \<Theta>"
  shows "\<Theta>; \<B>; GNil  \<turnstile>   \<lbrace> z' : B_int  | CE_val (V_var z')  ==  CE_val (V_lit (L_num (int (length v))))  \<rbrace> \<lesssim> 
                           \<lbrace> z : B_int  | CE_val (V_var z)  ==  CE_len [(V_lit (L_bitvec v))]\<^sup>c\<^sup>e  \<rbrace>" (is "\<Theta>; \<B>; GNil  \<turnstile> ?t1 \<lesssim> ?t2")
proof -

  have *: "\<Theta>  \<turnstile>\<^sub>w\<^sub>f []  \<and>  \<Theta>; \<B>; GNil  \<turnstile>\<^sub>w\<^sub>f []\<^sub>\<Delta> " using assms wfG_nilI wfD_emptyI wfPhi_emptyI by auto
  obtain x::x where x: "atom x \<sharp>  (\<Theta>, \<B>, GNil,  z' ,  CE_val (V_var z')  ==  
          CE_val (V_lit (L_num (int (length v)))) ,  z, CE_val (V_var z)  ==  CE_len [(V_lit (L_bitvec v))]\<^sup>c\<^sup>e )"
    (is "atom x \<sharp> ?F")
    using obtain_fresh by metis
  then show ?thesis proof
    have "\<Theta>  ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f CE_val (V_lit (L_num (int (length v)))) : B_int" 
      using wfCE_valI * wfV_litI base_for_lit.simps 
      by (metis wfE_valI wfX_wfY)

    thus  "\<Theta>; \<B>; GNil  \<turnstile>\<^sub>w\<^sub>f  ?t1" using wfT_e_eq fresh_GNil by auto

    have "\<Theta>  ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f CE_len [(V_lit (L_bitvec v))]\<^sup>c\<^sup>e : B_int"       
      using wfE_valI * wfV_litI base_for_lit.simps  wfE_valI wfX_wfY 
      by (metis wfCE_lenI wfCE_valI)

    thus "\<Theta>; \<B>; GNil  \<turnstile>\<^sub>w\<^sub>f  ?t2" using wfT_e_eq fresh_GNil  by auto

    show  "\<Theta>; \<B>; (x, B_int, (CE_val (V_var z')  ==  CE_val (V_lit (L_num (int (length v)))) )[z'::=V_var x]\<^sub>v) #\<^sub>\<Gamma> GNil  \<Turnstile> (CE_val (V_var z)  ==  CE_len [(V_lit (L_bitvec v))]\<^sup>c\<^sup>e )[z::=V_var x]\<^sub>v"
      (is "\<Theta>; \<B>; ?G \<Turnstile> ?c" ) using valid_len assms subst_v_c_def by auto      
  qed
qed

lemma subtype_base_fresh:
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b  | c \<rbrace>" and "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b  | c' \<rbrace> " and
    "atom z \<sharp> \<Gamma>" and "\<Theta>; \<B>; (z, b, c) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> c'"
  shows "\<Theta>; \<B>; \<Gamma> \<turnstile> \<lbrace> z : b  | c \<rbrace> \<lesssim> \<lbrace> z : b  | c' \<rbrace>"
proof  -
  obtain x::x where *:"atom x \<sharp> ((\<Theta> , \<B> , z, c, z, c', \<Gamma>) , (\<Theta>, \<B>, \<Gamma>, \<lbrace> z : b  | c \<rbrace>, \<lbrace> z : b  | c' \<rbrace>))" using obtain_fresh by metis
  moreover hence "atom x \<sharp> \<Gamma>" using fresh_Pair by auto
  moreover hence "\<Theta>; \<B>; (x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> c'[z::=V_var x]\<^sub>v" using assms valid_flip_simple  * subst_v_c_def  by auto
  ultimately show ?thesis using subtype_baseI assms \<tau>.fresh fresh_Pair by metis
qed

lemma subtype_bop_arith:
  assumes "wfG \<Theta> \<B>  \<Gamma>" and "(opp = Plus \<and> ll = (L_num (n1+n2))) \<or> (opp = LEq \<and> ll = ( if n1\<le>n2 then L_true else L_false))"  
    and "(opp = Plus \<longrightarrow> b = B_int) \<and> (opp = LEq \<longrightarrow> b = B_bool)"
  shows "\<Theta>; \<B>; \<Gamma>  \<turnstile> (\<lbrace> z : b | C_eq (CE_val (V_var z))  (CE_val (V_lit (ll))) \<rbrace>) \<lesssim>  
                           \<lbrace> z : b | C_eq (CE_val (V_var z)) (CE_op opp [(V_lit (L_num n1))]\<^sup>c\<^sup>e [(V_lit (L_num n2))]\<^sup>c\<^sup>e) \<rbrace>" (is "\<Theta>; \<B>; \<Gamma>  \<turnstile> ?T1 \<lesssim> ?T2")   
proof -  
  obtain x::x where  xf: "atom x \<sharp> (z, CE_val (V_var z)  ==  CE_val (V_lit (ll)) , z, CE_val (V_var z)  ==  CE_op opp [(V_lit (L_num n1))]\<^sup>c\<^sup>e [(V_lit (L_num n2))]\<^sup>c\<^sup>e , \<Gamma>)" 
    using obtain_fresh by blast

  have "\<Theta>; \<B>; \<Gamma>  \<turnstile> (\<lbrace> x : b | C_eq (CE_val (V_var x))  (CE_val (V_lit (ll))) \<rbrace>) \<lesssim>  
                           \<lbrace> x : b | C_eq (CE_val (V_var x)) (CE_op opp [(V_lit (L_num n1))]\<^sup>c\<^sup>e [(V_lit (L_num n2))]\<^sup>c\<^sup>e) \<rbrace>" (is "\<Theta>; \<B>; \<Gamma>  \<turnstile> ?S1 \<lesssim> ?S2") 
  proof(rule  subtype_base_fresh)

    show "atom x \<sharp> \<Gamma>" using xf fresh_Pair by auto

    show  "wfT \<Theta> \<B> \<Gamma> (\<lbrace> x : b | CE_val (V_var x)  ==  CE_val (V_lit ll)  \<rbrace>)" (is "wfT \<Theta> \<B> ?A ?B") 
    proof(rule wfT_e_eq)
      have   " \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f (V_lit ll) : b" using wfV_litI base_for_lit.simps assms by metis
      thus " \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_val (V_lit ll) : b" using wfCE_valI by auto
      show "atom x \<sharp> \<Gamma>" using xf fresh_Pair by auto
    qed

    consider "opp = Plus" | "opp = LEq" using opp.exhaust assms by blast
    then show  "wfT \<Theta>  \<B>  \<Gamma> (\<lbrace> x : b  | CE_val (V_var x)  ==  CE_op opp [(V_lit (L_num n1))]\<^sup>c\<^sup>e [(V_lit (L_num n2))]\<^sup>c\<^sup>e  \<rbrace>)" (is "wfT \<Theta> \<B>  ?A ?C")
    proof(cases)
      case 1
      then show "\<Theta> ; \<B> ; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<lbrace> x : b  | [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ opp [ [ L_num n1 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ L_num n2 ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  \<rbrace>"   
        using wfCE_valI  wfCE_plusI  assms wfV_litI base_for_lit.simps assms 
        by (metis \<open>atom x \<sharp> \<Gamma>\<close> wfT_e_eq)
    next
      case 2
      then show "\<Theta> ; \<B> ; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<lbrace> x : b  | [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ opp [ [ L_num n1 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ L_num n2 ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  \<rbrace>  "  
        using wfCE_valI  wfCE_plusI  assms wfV_litI base_for_lit.simps assms 

        by (metis \<open>atom x \<sharp> \<Gamma>\<close> wfCE_leqI wfT_e_eq)
    qed    

    show   "\<Theta>; \<B> ; (x, b, (CE_val (V_var x)  ==  CE_val (V_lit (ll)) )) #\<^sub>\<Gamma> \<Gamma>  
                          \<Turnstile> (CE_val (V_var x)  ==  CE_op opp [V_lit (L_num n1)]\<^sup>c\<^sup>e [V_lit (L_num n2)]\<^sup>c\<^sup>e)" (is "\<Theta>; \<B>; ?G \<Turnstile> ?c")
      using valid_arith_bop assms xf by simp

  qed
  moreover have "?S1 = ?T1 " using type_l_eq by auto
  moreover have "?S2 = ?T2" using type_e_eq ce.fresh v.fresh supp_l_empty fresh_def empty_iff fresh_e_opp 
    by (metis ms_fresh_all(4))
  ultimately show ?thesis by auto 

qed

lemma subtype_bop_eq:
  assumes "wfG \<Theta> \<B>  \<Gamma>" and "base_for_lit l1 = base_for_lit l2"
  shows "\<Theta>; \<B>; \<Gamma>  \<turnstile> (\<lbrace> z : B_bool | C_eq (CE_val (V_var z)) (CE_val (V_lit (if l1 = l2 then L_true else L_false))) \<rbrace>) \<lesssim>  
                      \<lbrace> z : B_bool | C_eq (CE_val (V_var z)) (CE_op Eq [(V_lit l1)]\<^sup>c\<^sup>e [(V_lit l2)]\<^sup>c\<^sup>e) \<rbrace>" (is "\<Theta>; \<B>; \<Gamma>  \<turnstile> ?T1 \<lesssim> ?T2")   
proof -
  let ?ll = "if l1 = l2 then L_true else L_false"
  obtain x::x where  xf: "atom x \<sharp> (z, CE_val (V_var z)  ==  CE_val (V_lit (if l1 = l2 then L_true else L_false)) , z, CE_val (V_var z)  ==  CE_op Eq  [(V_lit l1)]\<^sup>c\<^sup>e [(V_lit l2)]\<^sup>c\<^sup>e , \<Gamma>, (\<Theta>, \<B>, \<Gamma>))" 
    using obtain_fresh by blast

  have "\<Theta>; \<B>; \<Gamma>  \<turnstile> (\<lbrace> x : B_bool | C_eq (CE_val (V_var x))  (CE_val (V_lit (?ll))) \<rbrace>) \<lesssim>  
                           \<lbrace> x : B_bool | C_eq (CE_val (V_var x)) (CE_op Eq [(V_lit (l1))]\<^sup>c\<^sup>e [(V_lit (l2))]\<^sup>c\<^sup>e) \<rbrace>" (is "\<Theta>; \<B>; \<Gamma>  \<turnstile> ?S1 \<lesssim> ?S2") 
  proof(rule  subtype_base_fresh)

    show "atom x \<sharp> \<Gamma>" using xf fresh_Pair by auto

    show  "wfT \<Theta> \<B> \<Gamma> (\<lbrace> x : B_bool | CE_val (V_var x)  ==  CE_val (V_lit ?ll)  \<rbrace>)" (is "wfT \<Theta> \<B> ?A ?B") 
    proof(rule wfT_e_eq)
      have   " \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f (V_lit ?ll) : B_bool" using wfV_litI base_for_lit.simps assms by metis
      thus " \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_val (V_lit ?ll) : B_bool" using wfCE_valI by auto
      show "atom x \<sharp> \<Gamma>" using xf fresh_Pair by auto
    qed

    show " \<Theta> ; \<B> ; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<lbrace> x : B_bool  | [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ eq [ [ l1 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ l2 ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  \<rbrace> "   
    proof(rule wfT_e_eq)
      show "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f [ eq [ [ l1 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ l2 ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e : B_bool" 
        apply(rule wfCE_eqI, rule wfCE_valI)
        apply(rule wfV_litI, simp add: assms)
        using wfV_litI assms wfCE_valI by auto   
      show "atom x \<sharp> \<Gamma>"  using xf fresh_Pair by auto
    qed

    show   "\<Theta>; \<B> ; (x, B_bool, (CE_val (V_var x)  ==  CE_val (V_lit (?ll)) )) #\<^sub>\<Gamma> \<Gamma>  
                          \<Turnstile> (CE_val (V_var x)  ==  CE_op Eq [V_lit (l1)]\<^sup>c\<^sup>e [V_lit (l2)]\<^sup>c\<^sup>e)" (is "\<Theta>; \<B>; ?G \<Turnstile> ?c")
      using valid_eq_bop assms xf by auto

  qed
  moreover have "?S1 = ?T1 " using type_l_eq by auto
  moreover have "?S2 = ?T2" using type_e_eq ce.fresh v.fresh supp_l_empty fresh_def empty_iff fresh_e_opp 
    by (metis ms_fresh_all(4))
  ultimately show ?thesis by auto 

qed

lemma subtype_top:
  assumes "wfT \<Theta> \<B> G  (\<lbrace> z : b | c  \<rbrace>)"
  shows  "\<Theta>; \<B>; G  \<turnstile>  (\<lbrace> z : b | c  \<rbrace>) \<lesssim> (\<lbrace> z : b | TRUE  \<rbrace>)"
proof - 
  obtain x::x where *: "atom x \<sharp> (\<Theta>, \<B>, G,  z ,  c,  z , TRUE)" using obtain_fresh by blast
  then show ?thesis proof(rule subtype_baseI)
    show \<open> \<Theta>; \<B>; G  \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b  | c \<rbrace> \<close> using assms by auto
    show \<open> \<Theta>; \<B>;G  \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b  | TRUE \<rbrace> \<close> using wfT_TRUE assms wfX_wfY b_of.simps wfT_wf
      by (metis wfX_wfB(8))
    hence "\<Theta>  ; \<B>  \<turnstile>\<^sub>w\<^sub>f  (x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> G" using wfT_wf_cons3 assms fresh_Pair * subst_v_c_def by auto
    thus  \<open>\<Theta>; \<B>; (x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> G  \<Turnstile> (TRUE)[z::=V_var x]\<^sub>v \<close> using valid_trueI subst_cv.simps subst_v_c_def by metis
  qed
qed

lemma if_simp:
  "(if x = x then e1 else e2) = e1"
  by auto

lemma subtype_split:
  assumes "split n v (v1,v2)" and "\<turnstile>\<^sub>w\<^sub>f \<Theta>"
  shows "\<Theta> ; {||} ; GNil  \<turnstile> \<lbrace> z : [ B_bitvec , B_bitvec ]\<^sup>b  | [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ [ L_bitvec
           v1 ]\<^sup>v , [ L_bitvec
                       v2 ]\<^sup>v ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace> \<lesssim> \<lbrace> z : [ B_bitvec , B_bitvec ]\<^sup>b  | [ [ L_bitvec
          v ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [#1[ [ z ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e @@ [#2[ [ z ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e   AND  [| [#1[ [ z ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e  ==  [ [ L_num
                                                             n ]\<^sup>v ]\<^sup>c\<^sup>e   \<rbrace>" 
    (is "\<Theta> ;?B ; GNil  \<turnstile> \<lbrace> z : [ B_bitvec , B_bitvec ]\<^sup>b  | ?c1 \<rbrace>  \<lesssim> \<lbrace> z : [ B_bitvec , B_bitvec ]\<^sup>b  | ?c2 \<rbrace>")
proof -
  obtain x::x where xf:"atom x \<sharp> (\<Theta>, ?B, GNil, z, ?c1,z, ?c2 )"  using obtain_fresh by auto
  then show ?thesis proof(rule subtype_baseI)
    show *: \<open>\<Theta> ; ?B ; (x, [ B_bitvec , B_bitvec ]\<^sup>b, (?c1)[z::=[ x ]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma>
                    GNil  \<Turnstile> (?c2)[z::=[ x ]\<^sup>v]\<^sub>v \<close> 
      unfolding subst_v_c_def subst_cv.simps subst_cev.simps subst_vv.simps if_simp      
      using valid_split[OF assms, of x] by simp
    show \<open> \<Theta> ; ?B ; GNil   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : [ B_bitvec , B_bitvec ]\<^sup>b| ?c1 \<rbrace> \<close> using valid_wfT[OF *] xf fresh_prodN by metis
    show \<open> \<Theta> ; ?B ; GNil   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : [ B_bitvec , B_bitvec ]\<^sup>b| ?c2 \<rbrace> \<close>  using valid_wfT[OF *] xf fresh_prodN by metis
  qed
qed

lemma subtype_range:
  fixes n::int and \<Gamma>::\<Gamma>
  assumes "0 \<le> n \<and> n \<le> int (length v)" and "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f \<Gamma>" 
  shows "\<Theta> ; {||} ; \<Gamma>  \<turnstile> \<lbrace>   z : B_int  |  [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e == [ [ L_num n ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrace> \<lesssim>
                           \<lbrace> z : B_int  | ([ leq [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e )  AND  (
                                   [ leq [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e [| [ [ L_bitvec v ]\<^sup>v ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e)   \<rbrace>"
    (is  "\<Theta> ; ?B ; \<Gamma>  \<turnstile> \<lbrace>   z : B_int | ?c1 \<rbrace> \<lesssim>  \<lbrace> z : B_int  | ?c2 AND ?c3 \<rbrace>")
proof -
  obtain x::x where *:\<open>atom x \<sharp> (\<Theta>, ?B, \<Gamma>, z, ?c1 , z, ?c2 AND ?c3)\<close> using obtain_fresh by auto
  moreover have **:\<open>\<Theta> ; ?B ; (x, B_int, (?c1)[z::=[ x ]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> (?c2 AND ?c3)[z::=[ x ]\<^sup>v]\<^sub>v\<close> 
    unfolding subst_v_c_def subst_cv.simps subst_cev.simps subst_vv.simps if_simp using valid_range_length[OF assms(1)] assms fresh_prodN * by simp

  moreover hence \<open> \<Theta> ; ?B ; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : B_int  | [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_num n ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace> \<close> using 
      valid_wfT * fresh_prodN by metis
  moreover have \<open> \<Theta> ; ?B ; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : B_int  | ?c2 AND ?c3  \<rbrace> \<close> 
    using valid_wfT[OF **]  * fresh_prodN by metis
  ultimately show ?thesis using subtype_baseI by auto
qed

lemma check_num_range:
  assumes "0 \<le> n \<and> n \<le> int (length v)" and "\<turnstile>\<^sub>w\<^sub>f \<Theta>"
  shows "\<Theta> ; {||} ; GNil  \<turnstile> ([ L_num n ]\<^sup>v) \<Leftarrow> \<lbrace> z : B_int  | ([ leq [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e)   AND
      [ leq [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e [| [ [ L_bitvec v ]\<^sup>v ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e   \<rbrace>"
  using assms subtype_range check_v.intros infer_v_litI wfG_nilI 
  by (meson infer_natI)

section \<open>Literals\<close>

nominal_function type_for_lit :: "l \<Rightarrow> \<tau>" where
  "type_for_lit (L_true) = (\<lbrace> z : B_bool | [[z]\<^sup>v]\<^sup>c\<^sup>e == [V_lit L_true]\<^sup>c\<^sup>e \<rbrace>)"
| "type_for_lit (L_false) = (\<lbrace> z : B_bool | [[z]\<^sup>v]\<^sup>c\<^sup>e == [V_lit L_false]\<^sup>c\<^sup>e \<rbrace>)"
| "type_for_lit (L_num n) = (\<lbrace> z : B_int |  [[z]\<^sup>v]\<^sup>c\<^sup>e == [V_lit (L_num n)]\<^sup>c\<^sup>e \<rbrace>)"
| "type_for_lit (L_unit) = (\<lbrace> z : B_unit |  [[z]\<^sup>v]\<^sup>c\<^sup>e == [V_lit (L_unit )]\<^sup>c\<^sup>e \<rbrace>)" (* could have done { z : unit | True } but want the uniformity *)
| "type_for_lit (L_bitvec v) = (\<lbrace> z : B_bitvec |  [[z]\<^sup>v]\<^sup>c\<^sup>e == [V_lit (L_bitvec v)]\<^sup>c\<^sup>e \<rbrace>)"
  by (auto simp: eqvt_def type_for_lit_graph_aux_def, metis l.strong_exhaust,(simp add: permute_int_def flip_bitvec0)+ )
nominal_termination (eqvt) by lexicographic_order


nominal_function type_for_var :: "\<Gamma> \<Rightarrow> \<tau> \<Rightarrow> x \<Rightarrow> \<tau>" where
  "type_for_var G \<tau> x = (case lookup G x of 
                       None \<Rightarrow> \<tau>
                  | Some (b,c) \<Rightarrow> (\<lbrace> x : b | c \<rbrace>)) "  
  apply auto  unfolding eqvt_def apply(rule allI)  unfolding type_for_var_graph_aux_def eqvt_def by simp
nominal_termination (eqvt) by lexicographic_order

lemma infer_l_form:
  fixes l::l and tm::"'a::fs"
  assumes "\<turnstile> l \<Rightarrow> \<tau>" 
  shows "\<exists>z b. \<tau> = (\<lbrace> z : b | C_eq (CE_val (V_var z)) (CE_val (V_lit l)) \<rbrace>) \<and> atom z \<sharp> tm"
proof -
  obtain z' and b where t:"\<tau> = (\<lbrace> z' : b | C_eq (CE_val (V_var z')) (CE_val (V_lit l)) \<rbrace>)" using infer_l_elims  assms  using infer_l.simps type_for_lit.simps 
      type_for_lit.cases by blast
  obtain z::x where zf: "atom z \<sharp> tm" using obtain_fresh by metis
  have "\<tau> = \<lbrace> z : b | C_eq (CE_val (V_var z)) (CE_val (V_lit l)) \<rbrace>" using type_e_eq ce.fresh v.fresh l.fresh 
    by (metis t type_l_eq)
  thus ?thesis using zf by auto
qed

lemma infer_l_form3:
  fixes l::l
  assumes "\<turnstile> l \<Rightarrow> \<tau>" 
  shows "\<exists>z. \<tau> = (\<lbrace> z : base_for_lit l | C_eq (CE_val (V_var z)) (CE_val (V_lit l)) \<rbrace>)"
  using infer_l_elims using assms  using infer_l.simps type_for_lit.simps base_for_lit.simps by auto

lemma infer_l_form4[simp]:
  fixes \<Gamma>::\<Gamma>
  assumes "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> "   
  shows "\<exists>z. \<turnstile> l \<Rightarrow> (\<lbrace> z : base_for_lit l | C_eq (CE_val (V_var z)) (CE_val (V_lit l)) \<rbrace>)"
  using assms  infer_l_form2 infer_l_form3 by metis

lemma infer_v_unit_form:
  fixes v::v
  assumes "P ;  \<B> ; \<Gamma> \<turnstile> v \<Rightarrow> (\<lbrace> z1 : B_unit | c1 \<rbrace>)" and "supp v = {}"
  shows "v = V_lit L_unit"
  using assms proof(nominal_induct \<Gamma> v "\<lbrace> z1 : B_unit | c1 \<rbrace>" rule: infer_v.strong_induct)
  case (infer_v_varI \<Theta> \<B> c x z)
  then show ?case using supp_at_base by auto
next
  case (infer_v_litI \<Theta> \<B> \<Gamma> l)
  from \<open>\<turnstile> l \<Rightarrow> \<lbrace> z1 : B_unit  | c1 \<rbrace>\<close>  show ?case by(nominal_induct "\<lbrace> z1 : B_unit  | c1 \<rbrace>" rule: infer_l.strong_induct,auto)
qed

lemma base_for_lit_wf:
  assumes "\<turnstile>\<^sub>w\<^sub>f \<Theta>"
  shows   "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f base_for_lit l"
  using base_for_lit.simps using  wfV_elims wf_intros  assms l.exhaust by metis

lemma infer_l_t_wf:
  fixes \<Gamma>::\<Gamma>
  assumes "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and> atom z \<sharp> \<Gamma>"
  shows  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f  \<lbrace> z : base_for_lit l |  C_eq (CE_val (V_var z)) (CE_val (V_lit l)) \<rbrace>"
proof 
  show "atom z \<sharp>  (\<Theta>, \<B>, \<Gamma>)" using  wfG_fresh_x assms by auto
  show "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f base_for_lit l" using base_for_lit_wf assms wfX_wfY by metis
  thus "\<Theta>; \<B>; (z, base_for_lit l, TRUE) #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f CE_val (V_var z)  ==  CE_val (V_lit l)" using wfC_v_eq wfV_litI assms wfX_wfY by metis
qed

lemma infer_l_wf:
  fixes l::l and \<Gamma>::\<Gamma> and \<tau>::\<tau> and \<Theta>::\<Theta>
  assumes "\<turnstile> l \<Rightarrow> \<tau>" and "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>"
  shows "\<turnstile>\<^sub>w\<^sub>f \<Theta>" and  "\<Theta> ; \<B>   \<turnstile>\<^sub>w\<^sub>f \<Gamma>" and "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<tau>"
proof -
  show *:"\<Theta> ;  \<B>   \<turnstile>\<^sub>w\<^sub>f \<Gamma>" using assms infer_l_elims by auto
  thus  "\<turnstile>\<^sub>w\<^sub>f \<Theta>" using wfX_wfY by auto
  show *:"\<Theta> ;  \<B>  ; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<tau>" using infer_l_t_wf assms infer_l_form3 * 
    by (metis \<open>\<turnstile>\<^sub>w\<^sub>f \<Theta>\<close> fresh_GNil wfG_nilI wfT_weakening_nil)
qed

lemma infer_l_uniqueness: 
  fixes l::l
  assumes "\<turnstile> l \<Rightarrow> \<tau>" and "\<turnstile> l \<Rightarrow> \<tau>'" 
  shows "\<tau> = \<tau>'"
  using assms
proof -
  obtain z and b where zt: "\<tau> = (\<lbrace> z : b  | C_eq (CE_val (V_var z)) (CE_val (V_lit l)) \<rbrace>)" using infer_l_form assms by blast
  obtain z' and b where z't: "\<tau>' = (\<lbrace> z' : b  | C_eq (CE_val (V_var z')) (CE_val (V_lit l)) \<rbrace>)" using infer_l_form assms   by blast
  thus ?thesis using type_l_eq zt z't   assms infer_l.simps infer_l_elims l.distinct    
    by (metis infer_l_form3)
qed

section \<open>Values\<close>

lemma type_v_eq:
  assumes "\<lbrace> z1 : b1 | c1 \<rbrace> = \<lbrace> z : b  | C_eq (CE_val (V_var z)) (CE_val (V_var x)) \<rbrace>" and "atom z \<sharp> x"
  shows "b = b1" and "c1 =  C_eq (CE_val (V_var z1)) (CE_val (V_var x))"
  using assms  by (auto,metis Abs1_eq_iff \<tau>.eq_iff assms c.fresh ce.fresh type_e_eq v.fresh)

lemma infer_var2 [elim]:
  assumes "P; \<B> ; G \<turnstile> V_var x \<Rightarrow> \<tau>"
  shows "\<exists>b c. Some (b,c) = lookup G x"
  using assms infer_v_elims lookup_iff   by (metis (no_types, lifting))

lemma infer_var3 [elim]:
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> V_var x \<Rightarrow> \<tau>"
  shows "\<exists>z b c. Some (b,c) = lookup \<Gamma> x \<and> \<tau> = (\<lbrace> z : b | C_eq (CE_val (V_var z)) (CE_val (V_var x)) \<rbrace>) \<and> atom z \<sharp> x \<and> atom z \<sharp> (\<Theta>, \<B>, \<Gamma>)"
  using infer_v_elims(1)[OF assms(1)] by metis

lemma infer_bool_options2:
  fixes v::v
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace> z : b | c \<rbrace>" and "supp v = {} \<and> b = B_bool"
  shows  "v = V_lit L_true \<or> (v = (V_lit L_false))"
  using assms
proof(nominal_induct "\<lbrace> z : b | c \<rbrace>"  rule: infer_v.strong_induct)
  case (infer_v_varI \<Theta> \<B> \<Gamma> c x z)
  then show ?case using v.supp supp_at_base by auto
next
  case (infer_v_litI \<Theta> \<B> \<Gamma> l)
  from \<open> \<turnstile> l \<Rightarrow> \<lbrace> z : b  | c \<rbrace>\<close> show ?case proof(nominal_induct "\<lbrace> z : b  | c \<rbrace>"  rule: infer_l.strong_induct)
    case (infer_trueI z)
    then show ?case by auto
  next
    case (infer_falseI z)
    then show ?case by auto
  next
    case (infer_natI n z)
    then show ?case using infer_v_litI by simp
  next
    case (infer_unitI z)
    then show ?case using infer_v_litI by simp
  next
    case (infer_bitvecI bv z)
    then show ?case using infer_v_litI by simp
  qed
qed(auto+)

lemma infer_bool_options:
  fixes v::v
  assumes "\<Theta>; \<B>; \<Gamma>  \<turnstile> v \<Rightarrow> \<lbrace> z : B_bool  | c \<rbrace>" and "supp v = {}"
  shows "v = V_lit L_true \<or> (v = (V_lit L_false))"
  using infer_bool_options2  assms by blast

lemma infer_int2:
  fixes v::v
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace> z : b | c \<rbrace>"
  shows "supp v = {}  \<and> b = B_int \<longrightarrow> (\<exists>n. v = V_lit (L_num n))"
  using assms
proof(nominal_induct "\<lbrace> z : b | c \<rbrace>"  rule: infer_v.strong_induct)
  case (infer_v_varI \<Theta> \<B> \<Gamma> c x z)
  then show ?case using v.supp supp_at_base by auto
next
  case (infer_v_litI \<Theta> \<B> \<Gamma> l)
  from \<open> \<turnstile> l \<Rightarrow> \<lbrace> z : b  | c \<rbrace>\<close> show ?case proof(nominal_induct "\<lbrace> z : b  | c \<rbrace>"  rule: infer_l.strong_induct)
    case (infer_trueI z)
    then show ?case by auto
  next
    case (infer_falseI z)
    then show ?case by auto
  next
    case (infer_natI n z)
    then show ?case using infer_v_litI by simp
  next
    case (infer_unitI z)
    then show ?case using infer_v_litI by simp
  next
    case (infer_bitvecI bv z)
    then show ?case using infer_v_litI by simp
  qed
qed(auto+)

lemma infer_bitvec:
  fixes \<Theta>::\<Theta> and v::v
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace> z' : B_bitvec | c' \<rbrace>" and "supp v = {}"
  shows "\<exists>bv. v = V_lit (L_bitvec bv)"
  using assms proof(nominal_induct v rule: v.strong_induct)
  case (V_lit l)
  then show ?case by(nominal_induct l rule: l.strong_induct,force+)
next
  case (V_consp s dc b v)
  then show ?case using  infer_v_elims(7)[OF V_consp(2)] \<tau>.eq_iff by auto
next
  case (V_var x)
  then show ?case using supp_at_base by auto
qed(force+)

lemma infer_int:
  assumes "infer_v \<Theta> \<B> \<Gamma> v  (\<lbrace> z : B_int | c \<rbrace>)" and "supp v= {}"
  shows "\<exists>n. V_lit (L_num n) = v"
  using assms infer_int2  by (metis (no_types, lifting))

lemma infer_lit:
  assumes "infer_v \<Theta> \<B> \<Gamma> v  (\<lbrace> z : b | c \<rbrace>)" and "supp v= {}" and "b \<in> { B_bool , B_int , B_unit }"
  shows "\<exists>l. V_lit l = v"
  using assms proof(nominal_induct v rule: v.strong_induct)
  case (V_lit x)
  then show ?case   by (simp add: supp_at_base)
next
  case (V_var x)
  then show ?case 
    by (simp add: supp_at_base)
next
  case (V_pair x1a x2a)
  then show ?case  using supp_at_base by auto
next
  case (V_cons x1a x2a x3)
  then show ?case   using supp_at_base by auto
next
  case (V_consp x1a x2a x3 x4)
  then show ?case    using supp_at_base by auto
qed

lemma infer_v_form[simp]:
  fixes v::v
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>" 
  shows "\<exists>z b. \<tau> = (\<lbrace> z : b | C_eq (CE_val (V_var z)) (CE_val v)\<rbrace>) \<and> atom z \<sharp> v \<and> atom z \<sharp> (\<Theta>, \<B>, \<Gamma>)"
  using assms
proof(nominal_induct   rule: infer_v.strong_induct)
  case (infer_v_varI \<Theta> \<B> \<Gamma> b c x z)
  then show ?case by force
next
  case (infer_v_litI \<Theta> \<B> \<Gamma> l \<tau>)
  then obtain z and b where "\<tau> = \<lbrace> z : b  | CE_val (V_var z)  ==  CE_val (V_lit l)  \<rbrace> \<and>atom z \<sharp> (\<Theta>, \<B>, \<Gamma>) "
    using infer_l_form by metis
  moreover hence  "atom z \<sharp> (V_lit l)" using supp_l_empty v.fresh(1) fresh_prod2 fresh_def by blast
  ultimately show ?case by metis
next
  case (infer_v_pairI z v1 v2 \<Theta> \<B> \<Gamma> t1 t2)
  then show ?case by force
next
  case (infer_v_consI s dclist \<Theta> dc tc \<B> \<Gamma> v tv z)
  moreover hence "atom z \<sharp> (V_cons s dc v)" using
      Un_commute b.supp(3) fresh_def sup_bot.right_neutral supp_b_empty v.supp(4) pure_supp by metis
  ultimately show ?case using fresh_prodN by metis
next
  case (infer_v_conspI s bv dclist \<Theta> dc tc \<B> \<Gamma> v tv b z)
  moreover hence "atom z \<sharp> (V_consp s dc b v)" unfolding v.fresh using pure_fresh fresh_prodN * by metis
  ultimately show ?case using fresh_prodN by metis
qed

lemma infer_v_form2:
  fixes v::v
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> (\<lbrace> z : b | c \<rbrace>)" and "atom z \<sharp> v" 
  shows "c = C_eq (CE_val (V_var z)) (CE_val v)"
  using assms 
proof -
  obtain z' and b' where "(\<lbrace> z : b | c \<rbrace>)  = (\<lbrace> z' : b'  | CE_val (V_var z')  ==  CE_val v  \<rbrace>) \<and> atom z' \<sharp> v"
    using infer_v_form assms by meson
  thus ?thesis using Abs1_eq_iff(3) \<tau>.eq_iff  type_e_eq
    by (metis assms(2) ce.fresh(1))
qed

lemma infer_v_form3:
  fixes v::v
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>"  and "atom z \<sharp> (v,\<Gamma>)"
  shows "\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace> z : b_of \<tau> | C_eq (CE_val (V_var z)) (CE_val v)\<rbrace>"
proof -
  obtain z' and b' where "\<tau> = \<lbrace> z' : b' | C_eq (CE_val (V_var z')) (CE_val v)\<rbrace> \<and> atom z' \<sharp> v \<and> atom z' \<sharp> (\<Theta>, \<B>, \<Gamma>)" 
    using infer_v_form assms by metis
  moreover hence "\<lbrace> z' : b' | C_eq (CE_val (V_var z')) (CE_val v)\<rbrace> = \<lbrace> z : b' | C_eq (CE_val (V_var z)) (CE_val v)\<rbrace>" 
    using assms type_e_eq fresh_Pair ce.fresh by auto
  ultimately show  ?thesis using  b_of.simps assms by auto
qed

lemma infer_v_form4:
  fixes v::v
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>"  and "atom z \<sharp> (v,\<Gamma>)" and "b = b_of \<tau>"
  shows "\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace> z : b | C_eq (CE_val (V_var z)) (CE_val v)\<rbrace>"
  using assms infer_v_form3 by simp

lemma infer_v_v_wf:
  fixes v::v
  shows "\<Theta>; \<B> ; G \<turnstile> v \<Rightarrow> \<tau> \<Longrightarrow>  \<Theta>; \<B>; G \<turnstile>\<^sub>w\<^sub>f v : (b_of \<tau>)"
proof(induct rule: infer_v.induct)
  case (infer_v_varI \<Theta> \<B> \<Gamma> b c x z)
  then show ?case using  wfC_elims  wf_intros by auto
next
  case (infer_v_pairI z v1 v2 \<Theta> \<B> \<Gamma> t1 t2)
  then show ?case using  wfC_elims  wf_intros by auto
next
  case (infer_v_litI \<Theta> \<B> \<Gamma> l \<tau>)
  hence "b_of \<tau> = base_for_lit l" using infer_l_form3 b_of.simps by metis
  then show ?case using wfV_litI infer_l_wf infer_v_litI wfG_b_weakening
    by (metis fempty_fsubsetI)
next
  case (infer_v_consI s dclist \<Theta> dc tc \<B> \<Gamma> v tv z)
  then show ?case using  wfC_elims  wf_intros 
    by (metis (no_types, lifting) b_of.simps has_fresh_z2 subtype_eq_base2)
next
  case (infer_v_conspI s bv dclist \<Theta> dc tc \<B> \<Gamma> v tv b z)
  obtain z1 b1 c1 where t:"tc = \<lbrace> z1 : b1 | c1 \<rbrace>" using obtain_fresh_z by metis
  show ?case unfolding b_of.simps proof(rule wfV_conspI)
    show \<open>AF_typedef_poly s bv dclist \<in> set \<Theta>\<close> using infer_v_conspI by auto
    show \<open>(dc,  \<lbrace> z1 : b1 | c1 \<rbrace> ) \<in> set dclist\<close> using infer_v_conspI t by auto
    show \<open> \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f b \<close> using infer_v_conspI by auto
    show \<open>atom bv \<sharp> (\<Theta>, \<B>, \<Gamma>, b, v)\<close> using infer_v_conspI by auto
    have " b1[bv::=b]\<^sub>b\<^sub>b = b_of tv" using subtype_eq_base2[OF infer_v_conspI(5)] b_of.simps t subst_tb.simps by auto
    thus \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b1[bv::=b]\<^sub>b\<^sub>b \<close> using infer_v_conspI by auto
  qed
qed

lemma infer_v_t_form_wf:
  assumes " wfB \<Theta> \<B> b" and "wfV  \<Theta> \<B> \<Gamma> v b" and "atom z \<sharp> \<Gamma>"
  shows "wfT \<Theta> \<B> \<Gamma> \<lbrace> z : b | C_eq (CE_val (V_var z)) (CE_val v)\<rbrace>"
  using wfT_v_eq assms by auto

lemma infer_v_t_wf:
  fixes v::v
  assumes "\<Theta>; \<B>; G \<turnstile> v \<Rightarrow> \<tau>"
  shows "wfT \<Theta> \<B> G \<tau> \<and>  wfB  \<Theta> \<B> (b_of \<tau>) "
proof -
  obtain z and b where "\<tau> = \<lbrace> z : b  | CE_val (V_var z)  ==  CE_val v  \<rbrace> \<and> atom z \<sharp> v \<and> atom z \<sharp> (\<Theta>, \<B>, G)" using infer_v_form assms by metis
  moreover have  "wfB  \<Theta> \<B> b" using infer_v_v_wf b_of.simps wfX_wfB(1) assms 
    using calculation by fastforce
  ultimately show "wfT \<Theta> \<B> G \<tau> \<and>   wfB  \<Theta> \<B> (b_of \<tau>)" using infer_v_v_wf  infer_v_t_form_wf assms by fastforce
qed

lemma infer_v_wf: 
  fixes  v::v
  assumes "\<Theta>; \<B>; G \<turnstile> v \<Rightarrow> \<tau>"
  shows  "\<Theta>; \<B>; G \<turnstile>\<^sub>w\<^sub>f v : (b_of \<tau>)" and "wfT \<Theta> \<B> G \<tau>"  and "wfTh \<Theta>" and "wfG \<Theta> \<B> G"
proof -
  show "\<Theta>; \<B>; G \<turnstile>\<^sub>w\<^sub>f v : b_of \<tau> " using infer_v_v_wf assms by auto
  show "\<Theta>; \<B>; G   \<turnstile>\<^sub>w\<^sub>f \<tau>" using infer_v_t_wf assms by auto
  thus  "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f G" using wfX_wfY by auto
  thus  "\<turnstile>\<^sub>w\<^sub>f \<Theta>" using  wfX_wfY by auto
qed

lemma check_bool_options:
  assumes "\<Theta>; \<B>; \<Gamma>  \<turnstile> v \<Leftarrow> \<lbrace> z : B_bool  | TRUE \<rbrace>" and "supp v = {}"
  shows "v = V_lit L_true \<or> v = V_lit L_false"
proof -
  obtain t1 where  " \<Theta>; \<B>; \<Gamma>  \<turnstile> t1 \<lesssim>  \<lbrace> z : B_bool  | TRUE \<rbrace> \<and> \<Theta>; \<B>; \<Gamma>  \<turnstile> v \<Rightarrow> t1" using check_v_elims 
    using assms by blast
  thus ?thesis using infer_bool_options assms
    by (metis \<tau>.exhaust b_of.simps subtype_eq_base2)
qed

lemma check_v_wf:
  fixes v::v and \<Gamma>::\<Gamma> and \<tau>::\<tau>
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Leftarrow> \<tau>"
  shows " \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>" and "\<Theta>; \<B>;\<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b_of \<tau>" and "\<Theta>; \<B>;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>"
proof -
  obtain \<tau>' where *: "\<Theta>; \<B>; \<Gamma> \<turnstile> \<tau>' \<lesssim> \<tau> \<and> \<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>'" using check_v_elims assms by auto
  thus "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma> " and "\<Theta>; \<B>;\<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b_of \<tau>" and "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>"  
    using infer_v_wf infer_v_v_wf  subtype_eq_base2   *  subtype_wf  by metis+
qed

lemma infer_v_form_fresh:
  fixes v::v and t::"'a::fs" 
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>" 
  shows "\<exists>z b. \<tau> = \<lbrace> z : b | C_eq (CE_val (V_var z)) (CE_val v)\<rbrace> \<and> atom z \<sharp> (t,v)"
proof -
  obtain z' and b' where "\<tau> = \<lbrace> z' : b' | C_eq (CE_val (V_var z')) (CE_val v)\<rbrace>" using infer_v_form assms by blast
  moreover then obtain z and b and c where "\<tau> = \<lbrace> z : b | c \<rbrace> \<and> atom z \<sharp> (t,v)" using obtain_fresh_z by metis
  ultimately have "\<tau> = \<lbrace> z : b | C_eq (CE_val (V_var z)) (CE_val v)\<rbrace> \<and>  atom z \<sharp> (t,v) "
    using assms infer_v_form2  by auto
  thus ?thesis by blast
qed

text \<open> More generally, if support of a term is empty then any G will do \<close>

lemma infer_v_form_consp:
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> V_consp s dc b v \<Rightarrow> \<tau>"
  shows "b_of \<tau> = B_app s b"
  using assms proof(nominal_induct "V_consp s dc b v" \<tau>   rule: infer_v.strong_induct)
  case (infer_v_conspI bv dclist \<Theta> tc \<B> \<Gamma> tv z)
  then show ?case using b_of.simps by metis
qed

lemma lookup_in_rig_b:
  assumes "Some (b2, c2) = lookup (\<Gamma>[x\<longmapsto>c']) x'" and
    "Some (b1, c1) = lookup \<Gamma> x'"
  shows "b1 = b2"
  using assms lookup_in_rig[OF assms(2)] 
  by (metis option.inject prod.inject)

lemma infer_v_uniqueness_rig:
  fixes x::x and c::c
  assumes "infer_v P B G v \<tau>" and "infer_v P B (replace_in_g G x c') v \<tau>'"
  shows "\<tau> = \<tau>'"
  using assms
proof(nominal_induct "v"  arbitrary: \<tau>' \<tau> rule: v.strong_induct)
  case (V_lit l)
  hence "infer_l l \<tau>" and "infer_l l \<tau>'" using assms(1) infer_v_elims(2) by auto
  then show ?case using infer_l_uniqueness  by presburger
next
  case (V_var y)

  obtain b and c where bc: "Some (b,c) = lookup G y"  
    using assms(1) infer_v_elims(2)  using V_var.prems(1) lookup_iff by force
  then obtain  c'' where bc':"Some (b,c'') = lookup  (replace_in_g G x c') y" 
    using lookup_in_rig by blast

  obtain z  where "\<tau> = (\<lbrace> z : b |  C_eq (CE_val (V_var z)) (CE_val (V_var y)) \<rbrace>)" using infer_v_elims(1)[of P B G y \<tau>] V_var
      bc option.inject prod.inject lookup_in_g by metis
  moreover obtain z' where "\<tau>' = (\<lbrace> z' : b |  C_eq (CE_val (V_var z')) (CE_val (V_var y)) \<rbrace>)" using infer_v_elims(1)[of P B _ y \<tau>']  V_var
      option.inject prod.inject  lookup_in_rig  by (metis bc')
  ultimately show ?case using type_e_eq 
    by (metis V_var.prems(1) V_var.prems(2) \<tau>.eq_iff ce.fresh(1) finite.emptyI fresh_atom_at_base 
        fresh_finite_insert infer_v_elims(1) v.fresh(2))
next 
  case (V_pair v1 v2)
  obtain  z and z1 and z2 and t1 and t2 and c1 and c2 where
    t1: "\<tau> = (\<lbrace> z :  [ b_of t1 , b_of t2 ]\<^sup>b   | CE_val (V_var z)  ==  CE_val (V_pair v1 v2)  \<rbrace>) \<and> 
           atom z \<sharp> (v1, v2) \<and>  P ; B ; G  \<turnstile> v1 \<Rightarrow> t1 \<and>  P ; B ; G  \<turnstile> v2 \<Rightarrow> t2"
    using infer_v_elims(3)[OF V_pair(3)] by metis
  moreover obtain  z' and z1' and z2' and t1' and t2' and c1' and c2' where
    t2: "\<tau>' = (\<lbrace> z' :  [ b_of t1' , b_of t2' ]\<^sup>b  | CE_val (V_var z')  ==  CE_val (V_pair v1 v2)  \<rbrace>) \<and> 
             atom z' \<sharp> (v1, v2) \<and>  P ;  B ; (replace_in_g G x c')  \<turnstile> v1 \<Rightarrow> t1' \<and>  
             P ;  B ; (replace_in_g G x c')  \<turnstile> v2 \<Rightarrow> t2'"
    using infer_v_elims(3)[OF V_pair(4)] by metis
  ultimately have "t1 = t1' \<and> t2 = t2'" using V_pair.hyps(1) V_pair.hyps(2) \<tau>.eq_iff by blast
  then show ?case using t1 t2 by simp
next
  case (V_cons s dc v)
  obtain x and z and tc and dclist where  t1: "\<tau> = (\<lbrace> z : B_id s  | CE_val (V_var z)  ==  CE_val (V_cons s dc v) \<rbrace>) \<and>  
          AF_typedef s dclist \<in> set P \<and>
        (dc, tc) \<in> set dclist \<and> atom z \<sharp> v" 
    using infer_v_elims(4)[OF V_cons(2)] by metis
  moreover obtain x' and z' and tc' and dclist' where  t2: "\<tau>' = (\<lbrace> z' : B_id s  | CE_val (V_var z')  ==  CE_val (V_cons s dc v) \<rbrace>)
  \<and>  AF_typedef s dclist' \<in> set P \<and> (dc, tc') \<in> set dclist' \<and> atom z' \<sharp> v" 
    using infer_v_elims(4)[OF V_cons(3)] by metis
  moreover have a: "AF_typedef s dclist' \<in> set P" and b:"(dc,tc') \<in> set dclist'" and c:"AF_typedef s dclist \<in> set P" and
    d:"(dc, tc) \<in> set dclist" using t1 t2 by auto
  ultimately have "tc =  tc'" using wfTh_dc_t_unique2   infer_v_wf(3)[OF V_cons(2)] by metis

  moreover have "atom z \<sharp> CE_val (V_cons s dc v) \<and> atom z' \<sharp> CE_val (V_cons s dc v)" 
    using e.fresh(1)  v.fresh(4) t1 t2 pure_fresh by auto
  ultimately have "(\<lbrace> z : B_id s  | CE_val (V_var z)  ==  CE_val (V_cons s dc v) \<rbrace>) = (\<lbrace> z' : B_id s  | CE_val (V_var z')  ==  CE_val (V_cons s dc v) \<rbrace>)" 
    using type_e_eq by metis
  thus ?case using t1 t2 by simp
next
  case (V_consp s dc b v)
  from V_consp(2) V_consp show ?case proof(nominal_induct  "V_consp s dc b v" \<tau> arbitrary: v rule:infer_v.strong_induct)

    case (infer_v_conspI bv dclist \<Theta> tc \<B> \<Gamma> v tv z)

    obtain z3 and b3 where *:"\<tau>' = \<lbrace> z3 : b3 | [ [ z3 ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ V_consp s dc b v ]\<^sup>c\<^sup>e  \<rbrace> \<and> atom z3 \<sharp>  V_consp s dc b v"
      using infer_v_form[OF \<open>\<Theta>; \<B>; \<Gamma>[x\<longmapsto>c'] \<turnstile> V_consp s dc b v \<Rightarrow> \<tau>'\<close> ] by metis
    moreover then have "b3 = B_app s b" using  infer_v_form_consp b_of.simps * infer_v_conspI by metis

    moreover have "\<lbrace> z3 : B_app s b  | [ [ z3 ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ V_consp s dc b v ]\<^sup>c\<^sup>e  \<rbrace> =  \<lbrace> z : B_app s b  | [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ V_consp s dc b v ]\<^sup>c\<^sup>e  \<rbrace>"
    proof - 
      have "atom z3 \<sharp> [V_consp s dc b v]\<^sup>c\<^sup>e" using * ce.fresh by auto
      moreover have "atom z \<sharp> [V_consp s dc b v]\<^sup>c\<^sup>e" using * infer_v_conspI ce.fresh v.fresh pure_fresh by metis
      ultimately show ?thesis  using type_e_eq  infer_v_conspI v.fresh ce.fresh by metis
    qed
    ultimately  show ?case using * by auto
  qed
qed

lemma infer_v_uniqueness: 
  assumes "infer_v P B G v \<tau>" and "infer_v P B G v \<tau>'"
  shows "\<tau> = \<tau>'"
proof - 
  obtain x::x where "atom x \<sharp> G" using obtain_fresh by metis
  hence "G [ x \<longmapsto> C_true ] = G" using replace_in_g_forget assms infer_v_wf by fast
  thus ?thesis using infer_v_uniqueness_rig assms by metis
qed

lemma infer_v_tid_form:
  fixes v::v
  assumes "\<Theta> ; B ; \<Gamma>  \<turnstile> v \<Rightarrow> \<lbrace> z : B_id tid  | c \<rbrace>" and  "AF_typedef tid dclist \<in> set \<Theta>" and "supp v = {}"
  shows "\<exists>dc v' t. v = V_cons tid dc v' \<and> (dc , t ) \<in> set dclist"
  using assms proof(nominal_induct  v "\<lbrace> z : B_id tid  | c \<rbrace>" rule: infer_v.strong_induct)
  case (infer_v_varI \<Theta> \<B> c x z)
  then show ?case using v.supp supp_at_base  by auto
next
  case (infer_v_litI \<Theta> \<B> l)
  then show ?case by auto
next
  case (infer_v_consI dclist1 \<Theta> dc tc \<B> \<Gamma> v tv z)
  hence "supp v = {}" using v.supp by simp
  then obtain dca and v' where *:"V_cons tid dc v = V_cons tid dca v'" using infer_v_consI by auto
  hence "dca = dc" using v.eq_iff(4)  by auto
  hence  "V_cons tid dc v = V_cons tid dca v' \<and>  (dca, tc) \<in> set dclist1" using infer_v_consI * by auto
  moreover have "dclist = dclist1" using wfTh_dclist_unique infer_v_consI wfX_wfY \<open>dca=dc\<close> 
  proof -
    show ?thesis
      by (meson \<open>AF_typedef tid dclist1 \<in> set \<Theta>\<close> \<open>\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> tv\<close> infer_v_consI.prems infer_v_wf(4) wfTh_dclist_unique wfX_wfY) 
  qed
  ultimately show ?case by auto
qed

lemma check_v_tid_form:  
  assumes "\<Theta> ; B ; \<Gamma>  \<turnstile> v \<Leftarrow> \<lbrace> z : B_id tid  | TRUE \<rbrace>"  and "AF_typedef tid dclist \<in> set \<Theta>"  and "supp v = {}"
  shows "\<exists>dc v' t. v = V_cons tid dc v' \<and> (dc , t ) \<in> set dclist"
  using assms proof(nominal_induct  v "\<lbrace> z : B_id tid  | TRUE \<rbrace>" rule: check_v.strong_induct)
  case (check_v_subtypeI \<Theta> \<B> \<Gamma> \<tau>1 v)
  then obtain z and c where "\<tau>1 = \<lbrace> z : B_id tid | c \<rbrace>" using subtype_eq_base2 b_of.simps 
    by (metis obtain_fresh_z2)
  then show ?case  using infer_v_tid_form check_v_subtypeI by simp
qed

lemma check_v_num_leq:
  fixes n::int and \<Gamma>::\<Gamma>
  assumes "0 \<le> n \<and> n \<le> int (length v)" and " \<turnstile>\<^sub>w\<^sub>f \<Theta> " and "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f \<Gamma>"
  shows "\<Theta> ; {||} ; \<Gamma>  \<turnstile> [ L_num n ]\<^sup>v \<Leftarrow> \<lbrace> z : B_int  | ([ leq [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e)   
       AND  ([ leq [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e [| [ [ L_bitvec  v ]\<^sup>v ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e )  \<rbrace>" 
proof - 
  have "\<Theta> ; {||} ; \<Gamma>  \<turnstile> [ L_num n ]\<^sup>v \<Rightarrow>  \<lbrace> z : B_int  | [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_num n ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace>" 
    using infer_v_litI infer_natI wfG_nilI assms by auto
  thus ?thesis using subtype_range[OF assms(1) ] assms check_v_subtypeI by metis
qed

lemma check_int:
  assumes "check_v \<Theta> \<B> \<Gamma> v  (\<lbrace> z : B_int | c \<rbrace>)" and "supp v = {}"
  shows "\<exists>n. V_lit (L_num n) = v"
  using assms infer_int check_v_elims  by (metis b_of.simps infer_v_form subtype_eq_base2)

definition sble :: "\<Theta> \<Rightarrow> \<Gamma> \<Rightarrow> bool" where
  "sble \<Theta> \<Gamma> = (\<exists>i. i \<Turnstile> \<Gamma> \<and> \<Theta> ; \<Gamma> \<turnstile> i)"

lemma check_v_range:
  assumes "\<Theta> ; B ; \<Gamma> \<turnstile> v2 \<Leftarrow> \<lbrace> z : B_int  | [ leq [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e   AND  
            [ leq [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e [| [ v1 ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e   \<rbrace>  "
    (is "\<Theta> ; ?B ; \<Gamma> \<turnstile> v2 \<Leftarrow> \<lbrace> z : B_int | ?c1 \<rbrace>") 
    and "v1 = V_lit (L_bitvec bv) \<and> v2 = V_lit (L_num n) " and "atom z \<sharp> \<Gamma>" and "sble \<Theta> \<Gamma>"
  shows "0 \<le> n \<and> n \<le> int (length bv)"
proof - 
  have  "\<Theta> ; ?B ; \<Gamma> \<turnstile>  \<lbrace>   z : B_int  |  [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e == [ [ L_num n ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrace> \<lesssim> \<lbrace> z : B_int | ?c1 \<rbrace>" 
    using check_v_elims assms 
    by (metis infer_l_uniqueness infer_natI infer_v_elims(2))
  moreover have "atom z \<sharp> \<Gamma>" using fresh_GNil assms by simp
  ultimately have  "\<Theta> ; ?B ; ((z, B_int, [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_num n ]\<^sup>v ]\<^sup>c\<^sup>e ) #\<^sub>\<Gamma> \<Gamma>)  \<Turnstile> ?c1" 
    using subtype_valid_simple by auto
  thus ?thesis using assms valid_range_length_inv check_v_wf wfX_wfY sble_def by metis
qed

section \<open>Expressions\<close>

lemma infer_e_plus[elim]:
  fixes v1::v and v2::v
  assumes "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_op Plus v1 v2 \<Rightarrow> \<tau>"
  shows "\<exists>z . (\<lbrace> z : B_int |  C_eq (CE_val (V_var z)) (CE_op Plus [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e) \<rbrace> = \<tau>)"
  using infer_e_elims assms by metis

lemma infer_e_leq[elim]:
  assumes "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_op LEq v1 v2 \<Rightarrow> \<tau>"
  shows "\<exists>z . (\<lbrace> z : B_bool |  C_eq (CE_val (V_var z)) (CE_op LEq [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e) \<rbrace> = \<tau>)"
  using infer_e_elims assms by metis

lemma infer_e_eq[elim]:
  assumes "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_op Eq v1 v2 \<Rightarrow> \<tau>"
  shows "\<exists>z . (\<lbrace> z : B_bool |  C_eq (CE_val (V_var z)) (CE_op Eq [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e) \<rbrace> = \<tau>)"
  using infer_e_elims(25)[OF assms] by metis

lemma infer_e_e_wf: 
  fixes e::e
  assumes "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> e \<Rightarrow> \<tau>" 
  shows "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b_of \<tau>" 
  using assms proof(nominal_induct \<tau> avoiding: \<tau> rule: infer_e.strong_induct)
  case (infer_e_valI \<Theta> \<B> \<Gamma> \<Delta>' \<Phi> v \<tau>)
  then show ?case using  infer_v_v_wf wf_intros by metis
next
  case (infer_e_plusI \<Theta> \<B> \<Gamma> \<Delta>' \<Phi> v1 z1 c1 v2 z2 c2 z3)
  then show ?case using  b_of.simps infer_v_v_wf wf_intros by metis
next
  case (infer_e_leqI \<Theta> \<B> \<Gamma> \<Delta>' v1 z1 c1 v2 z2 c2 z3)
  then show ?case using  b_of.simps infer_v_v_wf wf_intros by metis
next
  case (infer_e_eqI \<Theta> \<B> \<Gamma> \<Delta>' v1 z1 c1 v2 z2 c2 z3)
  then show ?case using  b_of.simps infer_v_v_wf wf_intros by metis
next
  case (infer_e_appI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> f x b c \<tau>' s' v \<tau>'')
  have "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_app f v : b_of \<tau>' " proof 
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using infer_e_appI by auto
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using infer_e_appI by auto
    show \<open>Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c \<tau>' s'))) = lookup_fun \<Phi> f\<close> using infer_e_appI by auto
    show "\<Theta>; \<B>;\<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b" using infer_e_appI check_v_wf b_of.simps by metis
  qed
  moreover have "b_of \<tau>' = b_of (\<tau>'[x::=v]\<^sub>v)" using subst_tbase_eq subst_v_\<tau>_def by auto
  ultimately show ?case using infer_e_appI subst_v_c_def subst_b_\<tau>_def by auto
next
  case (infer_e_appPI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> b' f bv x b c \<tau>'' s' v \<tau>')

  have "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_appP f b' v : (b_of \<tau>'')[bv::=b']\<^sub>b " proof
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using infer_e_appPI by auto
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using infer_e_appPI by auto
    show \<open>Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau>'' s'))) = lookup_fun \<Phi> f\<close> using * infer_e_appPI by metis
    show "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f b'" using infer_e_appPI by auto
    show "\<Theta>; \<B>;\<Gamma> \<turnstile>\<^sub>w\<^sub>f v : (b[bv::=b']\<^sub>b)" using infer_e_appPI check_v_wf b_of.simps subst_b_b_def by metis
    have "atom bv \<sharp> (b_of \<tau>'')[bv::=b']\<^sub>b\<^sub>b" using fresh_subst_if subst_b_b_def infer_e_appPI by metis
    thus  "atom bv \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>, b', v, (b_of \<tau>'')[bv::=b']\<^sub>b)" using infer_e_appPI fresh_prodN subst_b_b_def by metis
  qed
  moreover have "b_of \<tau>' = (b_of \<tau>'')[bv::=b']\<^sub>b" 
    using \<open>\<tau>''[bv::=b']\<^sub>b[x::=v]\<^sub>v = \<tau>'\<close> b_of_subst_bb_commute subst_tbase_eq  subst_b_b_def subst_v_\<tau>_def subst_b_\<tau>_def by auto
  ultimately show ?case using infer_e_appI by auto
next
  case (infer_e_fstI \<Theta> \<B> \<Gamma> \<Delta>' \<Phi> v z' b1 b2 c z)
  then show ?case using  b_of.simps infer_v_v_wf wf_intros by metis
next
  case (infer_e_sndI \<Theta> \<B> \<Gamma> \<Delta>' \<Phi> v z' b1 b2 c z)
  then show ?case using  b_of.simps infer_v_v_wf wf_intros by metis
next
  case (infer_e_lenI \<Theta> \<B> \<Gamma> \<Delta>' \<Phi> v z' c z)
  then show ?case using  b_of.simps infer_v_v_wf wf_intros by metis
next
  case (infer_e_mvarI \<Theta> \<Gamma> \<Phi> \<Delta> u \<tau>)
  then show ?case using  b_of.simps infer_v_v_wf wf_intros by metis
next
  case (infer_e_concatI \<Theta> \<B> \<Gamma> \<Delta>' \<Phi> v1 z1 c1 v2 z2 c2 z3)
  then show ?case using  b_of.simps infer_v_v_wf wf_intros by metis
next
  case (infer_e_splitI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 z3)
  have " \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_split v1 v2  : B_pair B_bitvec B_bitvec"
  proof
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>" using infer_e_splitI by auto
    show "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>" using infer_e_splitI by auto 
    show "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_bitvec" using infer_e_splitI b_of.simps infer_v_wf by metis
    show "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_int" using infer_e_splitI b_of.simps check_v_wf by metis
  qed  
  then show ?case using  b_of.simps by auto
qed

lemma infer_e_t_wf:
  fixes e::e and \<Gamma>::\<Gamma> and \<tau>::\<tau> and \<Delta>::\<Delta> and \<Phi>::\<Phi>
  assumes "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> e \<Rightarrow> \<tau>"
  shows "\<Theta>; \<B>;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau> \<and> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>" 
  using assms proof(induct  rule: infer_e.induct)
  case (infer_e_valI \<Theta> \<B> \<Gamma> \<Delta>' \<Phi> v \<tau>)
  then show ?case using infer_v_t_wf by auto
next
  case (infer_e_plusI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 c2 z3)
  hence "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_op Plus [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e : B_int" using wfCE_plusI wfD_emptyI wfPhi_emptyI infer_v_v_wf  wfCE_valI
    by (metis b_of.simps infer_v_wf)
  then show ?case  using wfT_e_eq infer_e_plusI by auto
next
  case (infer_e_leqI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 c2 z3)
  hence " \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_op LEq [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e : B_bool" using wfCE_leqI wfD_emptyI wfPhi_emptyI infer_v_v_wf wfCE_valI
    by (metis b_of.simps infer_v_wf)
  then show ?case  using wfT_e_eq infer_e_leqI by auto
next
  case (infer_e_eqI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 b c1 v2 z2 c2 z3)
  hence " \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_op Eq [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e : B_bool" using wfCE_eqI wfD_emptyI wfPhi_emptyI infer_v_v_wf wfCE_valI
    by (metis b_of.simps infer_v_wf)
  then show ?case  using wfT_e_eq infer_e_eqI by auto
next
  case (infer_e_appI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> f x b c \<tau> s' v \<tau>')
  show ?case proof
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>" using infer_e_appI by auto
    show "\<Theta>; \<B>; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<tau>'" proof -
      have *:" \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b " using infer_e_appI check_v_wf(2) b_of.simps by metis
      moreover have *:"\<Theta>; \<B>; (x, b, c) #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<tau>" proof(rule  wf_weakening1(4))
        show \<open> \<Theta>; \<B>; (x,b,c)#\<^sub>\<Gamma>GNil  \<turnstile>\<^sub>w\<^sub>f \<tau> \<close> using  wfPhi_f_simple_wfT wfD_wf infer_e_appI wb_b_weakening by fastforce
        have "\<Theta> ;  \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> x : b | c \<rbrace>" using infer_e_appI check_v_wf(3) by auto
        thus  \<open> \<Theta> ;  \<B> \<turnstile>\<^sub>w\<^sub>f (x, b, c) #\<^sub>\<Gamma> \<Gamma> \<close> using infer_e_appI 
            wfT_wfC[THEN wfG_consI[rotated 3] ]  *  wfT_wf_cons fresh_prodN by simp
        show \<open>toSet ((x,b,c)#\<^sub>\<Gamma>GNil) \<subseteq> toSet ((x, b, c) #\<^sub>\<Gamma> \<Gamma>)\<close> using toSet.simps by auto
      qed
      moreover have "((x, b, c) #\<^sub>\<Gamma> \<Gamma>)[x::=v]\<^sub>\<Gamma>\<^sub>v = \<Gamma>" using subst_gv.simps by auto

      ultimately show ?thesis using infer_e_appI wf_subst1(4)[OF *, of GNil x b c \<Gamma> v] subst_v_\<tau>_def by auto
    qed
  qed
next
  case (infer_e_appPI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> b' f bv x b c \<tau>' s' v \<tau>)

  have "\<Theta>; \<B>; ((x, b[bv::=b']\<^sub>b\<^sub>b, c[bv::=b']\<^sub>c\<^sub>b) #\<^sub>\<Gamma> \<Gamma>)[x::=v]\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f (\<tau>'[bv::=b']\<^sub>b)[x::=v]\<^sub>\<tau>\<^sub>v" 
  proof(rule wf_subst(4))
    show \<open> \<Theta>; \<B>; (x, b[bv::=b']\<^sub>b\<^sub>b, c[bv::=b']\<^sub>c\<^sub>b) #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<tau>'[bv::=b']\<^sub>b \<close>  
    proof(rule  wf_weakening1(4))
      have  \<open> \<Theta> ; {|bv|} ; (x,b,c)#\<^sub>\<Gamma>GNil  \<turnstile>\<^sub>w\<^sub>f \<tau>' \<close> using  wfPhi_f_poly_wfT  infer_e_appI infer_e_appPI by simp
      thus  \<open> \<Theta>; \<B>; (x,b[bv::=b']\<^sub>b\<^sub>b,c[bv::=b']\<^sub>c\<^sub>b)#\<^sub>\<Gamma>GNil  \<turnstile>\<^sub>w\<^sub>f \<tau>'[bv::=b']\<^sub>b \<close> 
        using wfT_subst_wfT infer_e_appPI wb_b_weakening subst_b_\<tau>_def subst_v_\<tau>_def by presburger
      have "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> x :  b[bv::=b']\<^sub>b\<^sub>b | c[bv::=b']\<^sub>c\<^sub>b \<rbrace>" 
        using infer_e_appPI check_v_wf(3) subst_b_b_def subst_b_c_def by metis
      thus  \<open> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f (x, b[bv::=b']\<^sub>b\<^sub>b, c[bv::=b']\<^sub>c\<^sub>b) #\<^sub>\<Gamma> \<Gamma> \<close> 
        using infer_e_appPI wfT_wfC[THEN wfG_consI[rotated 3] ]  * wfX_wfY wfT_wf_cons wb_b_weakening by metis
      show \<open>toSet ((x,b[bv::=b']\<^sub>b\<^sub>b,c[bv::=b']\<^sub>c\<^sub>b)#\<^sub>\<Gamma>GNil) \<subseteq> toSet ((x, b[bv::=b']\<^sub>b\<^sub>b, c[bv::=b']\<^sub>c\<^sub>b) #\<^sub>\<Gamma> \<Gamma>)\<close> using toSet.simps by auto
    qed
    show \<open>(x, b[bv::=b']\<^sub>b\<^sub>b, c[bv::=b']\<^sub>c\<^sub>b) #\<^sub>\<Gamma> \<Gamma> = GNil @ (x, b[bv::=b']\<^sub>b\<^sub>b, c[bv::=b']\<^sub>c\<^sub>b) #\<^sub>\<Gamma> \<Gamma>\<close> using append_g.simps by auto
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v :b[bv::=b']\<^sub>b\<^sub>b  \<close> using infer_e_appPI check_v_wf(2) b_of.simps subst_b_b_def by metis
  qed
  moreover have "((x, b[bv::=b']\<^sub>b\<^sub>b, c[bv::=b']\<^sub>c\<^sub>b) #\<^sub>\<Gamma> \<Gamma>)[x::=v]\<^sub>\<Gamma>\<^sub>v = \<Gamma>" using subst_gv.simps by auto
  ultimately show ?case using infer_e_appPI subst_v_\<tau>_def by simp
next
  case (infer_e_fstI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v z' b1 b2 c z)
  hence "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_fst [v]\<^sup>c\<^sup>e: b1" using wfCE_fstI wfD_emptyI wfPhi_emptyI infer_v_v_wf 
      b_of.simps  using wfCE_valI by fastforce
  then show ?case  using wfT_e_eq infer_e_fstI by auto
next
  case (infer_e_sndI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v z' b1 b2 c z)
  hence "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_snd  [v]\<^sup>c\<^sup>e: b2" using wfCE_sndI wfD_emptyI wfPhi_emptyI infer_v_v_wf wfCE_valI
    by (metis b_of.simps infer_v_wf)
  then show ?case  using wfT_e_eq infer_e_sndI by auto
next
  case (infer_e_lenI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v z' c z)
  hence "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_len [v]\<^sup>c\<^sup>e: B_int" using wfCE_lenI wfD_emptyI wfPhi_emptyI infer_v_v_wf wfCE_valI
    by (metis b_of.simps infer_v_wf)
  then show ?case  using wfT_e_eq infer_e_lenI by auto
next
  case (infer_e_mvarI \<Theta> \<Gamma> \<Phi> \<Delta> u \<tau>)
  then show ?case using wfD_wfT by blast
next
  case (infer_e_concatI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 c2 z3)
  hence "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_concat [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e: B_bitvec" using wfCE_concatI wfD_emptyI wfPhi_emptyI infer_v_v_wf  wfCE_valI
    by (metis b_of.simps infer_v_wf)
  then show ?case  using wfT_e_eq infer_e_concatI by auto
next
  case (infer_e_splitI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 z3)

  hence wfg: " \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f (z3, [ B_bitvec , B_bitvec ]\<^sup>b, TRUE) #\<^sub>\<Gamma> \<Gamma>" 
    using infer_v_wf wfG_cons2I wfB_pairI wfB_bitvecI by simp
  have wfz: "\<Theta>; \<B>; (z3, [ B_bitvec , B_bitvec ]\<^sup>b, TRUE) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f [ [ z3 ]\<^sup>v ]\<^sup>c\<^sup>e : [ B_bitvec , B_bitvec ]\<^sup>b "
    apply(rule wfCE_valI , rule wfV_varI)
    using wfg  apply simp
    using lookup.simps(2)[of z3 "[ B_bitvec , B_bitvec ]\<^sup>b" TRUE \<Gamma> z3] by simp
  have 1: "\<Theta>; \<B>; (z3, [ B_bitvec , B_bitvec ]\<^sup>b, TRUE) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f [ v2 ]\<^sup>c\<^sup>e : B_int " 
    using check_v_wf[OF infer_e_splitI(4)]  wf_weakening(1)[OF _ wfg] b_of.simps   toSet.simps wfCE_valI by fastforce
  have 2: "\<Theta>; \<B>; (z3, [ B_bitvec , B_bitvec ]\<^sup>b, TRUE) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f [ v1 ]\<^sup>c\<^sup>e : B_bitvec" 
    using infer_v_wf[OF infer_e_splitI(3)]  wf_weakening(1)[OF _ wfg] b_of.simps   toSet.simps wfCE_valI by fastforce

  have "\<Theta>; \<B>; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z3 : [ B_bitvec , B_bitvec ]\<^sup>b  | [ v1 ]\<^sup>c\<^sup>e  ==  [ [#1[ [ z3 ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e @@ [#2[ [ z3 ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e   AND  [| [#1[ [ z3 ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e  ==  [ v2 ]\<^sup>c\<^sup>e   \<rbrace>"
  proof
    show "atom z3 \<sharp> (\<Theta>, \<B>, \<Gamma>)" using infer_e_splitI wfTh_x_fresh wfX_wfY fresh_prod3 wfG_fresh_x by metis
    show "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f [ B_bitvec , B_bitvec ]\<^sup>b " using wfB_pairI wfB_bitvecI infer_e_splitI wfX_wfY by metis
    show "\<Theta>; \<B>; (z3, [ B_bitvec , B_bitvec ]\<^sup>b, TRUE) #\<^sub>\<Gamma>
              \<Gamma>   \<turnstile>\<^sub>w\<^sub>f [ v1 ]\<^sup>c\<^sup>e  ==  [ [#1[ [ z3 ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e @@ [#2[ [ z3 ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e   AND  [| [#1[ [ z3 ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e  ==  [ v2 ]\<^sup>c\<^sup>e" 
      using wfg wfz 1 2 wf_intros by meson
  qed
  thus ?case using infer_e_splitI by auto
qed

lemma infer_e_wf:
  fixes e::e and \<Gamma>::\<Gamma> and \<tau>::\<tau> and \<Delta>::\<Delta> and \<Phi>::\<Phi>
  assumes "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> e \<Rightarrow> \<tau>"
  shows "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>" and "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>" and "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>" and "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : (b_of \<tau>)"
  using infer_e_t_wf infer_e_e_wf wfE_wf  assms by metis+

lemma infer_e_fresh:
  fixes x::x
  assumes "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> e \<Rightarrow> \<tau>" and "atom x \<sharp> \<Gamma>"
  shows "atom x \<sharp> (e,\<tau>)"
proof - 
  have "atom x \<sharp> e" using infer_e_e_wf[THEN wfE_x_fresh,OF assms(1)] assms(2) by auto
  moreover have "atom x \<sharp> \<tau>" using assms infer_e_wf  wfT_x_fresh by metis
  ultimately show ?thesis using fresh_Pair by auto
qed

inductive check_e :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> e \<Rightarrow> \<tau> \<Rightarrow> bool"  (" _ ; _ ; _ ; _ ; _  \<turnstile> _ \<Leftarrow> _" [50, 50, 50] 50) where
  check_e_subtypeI: "\<lbrakk> infer_e T P B G D e \<tau>' ; subtype T B G \<tau>' \<tau> \<rbrakk> \<Longrightarrow> check_e T P B G D e \<tau>"
equivariance check_e
nominal_inductive check_e  .

inductive_cases check_e_elims[elim!]:
  "check_e F D B G \<Theta> (AE_val v) \<tau>"
  "check_e F D B G \<Theta> e \<tau>"

lemma infer_e_fst_pair:
  fixes v1::v
  assumes "\<Theta> ; \<Phi> ; {||} ; GNil ; \<Delta>  \<turnstile> [#1[ v1 , v2 ]\<^sup>v]\<^sup>e \<Rightarrow> \<tau>"
  shows "\<exists>\<tau>'. \<Theta> ; \<Phi> ; {||} ; GNil ; \<Delta>  \<turnstile> [v1]\<^sup>e \<Rightarrow> \<tau>' \<and> 
        \<Theta> ; {||} ; GNil \<turnstile> \<tau>' \<lesssim> \<tau>"
proof -
  obtain z' and b1 and b2 and c and z where ** : "\<tau> = (\<lbrace> z : b1  | C_eq (CE_val (V_var z))  (CE_fst [(V_pair v1 v2)]\<^sup>c\<^sup>e)  \<rbrace>) \<and> 
          wfD \<Theta> {||} GNil \<Delta> \<and> wfPhi \<Theta> \<Phi> \<and>
              (\<Theta> ; {||} ; GNil  \<turnstile> V_pair v1 v2 \<Rightarrow> \<lbrace> z' : B_pair b1 b2  | c \<rbrace>) \<and> atom z \<sharp> V_pair v1 v2 "
    using infer_e_elims assms  by metis
  hence *:" \<Theta> ; {||} ; GNil  \<turnstile> V_pair v1 v2 \<Rightarrow> \<lbrace> z' : B_pair b1 b2  | c \<rbrace>" by auto

  obtain  t1a  and t2a  where
    *: "\<Theta> ; {||} ; GNil  \<turnstile> v1 \<Rightarrow> t1a \<and>   \<Theta> ; {||} ; GNil  \<turnstile> v2 \<Rightarrow> t2a \<and>  B_pair b1 b2 = B_pair (b_of t1a) (b_of t2a)"
    using infer_v_elims(5)[OF *] by metis

  hence  suppv: "supp v1 = {}  \<and> supp v2 = {} \<and> supp (V_pair v1 v2) = {}" using ** infer_v_v_wf wfV_supp atom_dom.simps toSet.simps supp_GNil  
    by (meson wfV_supp_nil)

  obtain z1 and b1' where "t1a = \<lbrace> z1 : b1'  | [ [ z1 ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v1 ]\<^sup>c\<^sup>e  \<rbrace> " 
    using infer_v_form[of \<Theta> "{||}" GNil v1 t1a] * by auto
  moreover hence "b1' = b1" using * b_of.simps by simp
  ultimately have  "\<Theta> ; {||} ; GNil  \<turnstile> v1 \<Rightarrow> \<lbrace> z1 : b1  | CE_val (V_var z1)  ==  CE_val v1 \<rbrace>" using * by auto
  moreover have "\<Theta> ; {||} ; GNil  \<turnstile>\<^sub>w\<^sub>f CE_fst [V_pair v1 v2]\<^sup>c\<^sup>e : b1" using wfCE_fstI infer_v_wf(1) ** b_of.simps wfCE_valI by metis
  moreover hence st: "\<Theta> ; {||} ; GNil  \<turnstile> \<lbrace> z1 : b1  | CE_val (V_var z1)  ==  CE_val v1 \<rbrace> \<lesssim> (\<lbrace> z : b1  | CE_val (V_var z)  ==  CE_fst [V_pair v1 v2]\<^sup>c\<^sup>e  \<rbrace>)" 
    using subtype_gnil_fst infer_v_v_wf by auto
  moreover have "wfD \<Theta> {||} GNil \<Delta> \<and>  wfPhi \<Theta> \<Phi>" using **  by auto
  ultimately show ?thesis  using wfX_wfY  ** infer_e_valI by metis
qed

lemma infer_e_snd_pair:
  assumes  "\<Theta> ; \<Phi> ;  {||} ; GNil ; \<Delta>  \<turnstile> AE_snd (V_pair v1 v2) \<Rightarrow> \<tau>"
  shows  "\<exists>\<tau>'. \<Theta> ; \<Phi> ; {||} ; GNil ; \<Delta>  \<turnstile> AE_val v2 \<Rightarrow> \<tau>' \<and> \<Theta> ; {||} ; GNil \<turnstile> \<tau>' \<lesssim> \<tau>"
proof -
  obtain z' and b1 and b2 and c and z where ** : "(\<tau> = (\<lbrace> z : b2  | C_eq (CE_val (V_var z)) (CE_snd [(V_pair v1 v2)]\<^sup>c\<^sup>e)  \<rbrace>)) \<and> 
           (wfD \<Theta> {||} GNil \<Delta>) \<and> (wfPhi \<Theta> \<Phi>) \<and>
              \<Theta> ; {||} ; GNil  \<turnstile> V_pair v1 v2 \<Rightarrow> \<lbrace> z' : B_pair b1 b2  | c \<rbrace> \<and> atom z \<sharp> V_pair v1 v2 "
    using infer_e_elims(9)[OF assms(1)]  by metis
  hence *:" \<Theta> ; {||} ; GNil  \<turnstile> V_pair v1 v2 \<Rightarrow> \<lbrace> z' : B_pair b1 b2  | c \<rbrace>" by auto

  obtain  t1a  and t2a  where
    *: "\<Theta> ; {||} ; GNil  \<turnstile> v1 \<Rightarrow> t1a \<and>   \<Theta> ; {||} ; GNil  \<turnstile> v2 \<Rightarrow> t2a \<and>  B_pair b1 b2 = B_pair (b_of t1a) (b_of t2a)"
    using infer_v_elims(5)[OF *] by metis

  hence  suppv: "supp v1 = {} \<and> supp v2 = {} \<and> supp (V_pair v1 v2) = {}" using infer_v_v_wf wfV.simps v.supp  by (meson "**" wfV_supp_nil)

  obtain z2 and b2' where "t2a = \<lbrace> z2 : b2'  | [ [ z2 ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v2 ]\<^sup>c\<^sup>e  \<rbrace> " 
    using infer_v_form[of \<Theta> "{||}" GNil v2 t2a] * by auto
  moreover hence "b2' = b2" using * b_of.simps by simp

  ultimately have  "\<Theta> ; {||} ; GNil  \<turnstile> v2 \<Rightarrow> \<lbrace> z2 : b2  | CE_val (V_var z2)  ==  CE_val v2 \<rbrace>" using * by auto
  moreover have "\<Theta> ; {||} ; GNil  \<turnstile>\<^sub>w\<^sub>f CE_snd [V_pair v1 v2]\<^sup>c\<^sup>e : b2" using wfCE_sndI infer_v_wf(1) ** b_of.simps wfCE_valI by metis
  moreover hence st: "\<Theta> ; {||} ; GNil  \<turnstile> \<lbrace> z2 : b2  | CE_val (V_var z2)  ==  CE_val v2 \<rbrace> \<lesssim> (\<lbrace> z : b2  | CE_val (V_var z)  ==  CE_snd [V_pair v1 v2]\<^sup>c\<^sup>e  \<rbrace>)" 
    using subtype_gnil_snd infer_v_v_wf by auto
  moreover have "wfD \<Theta> {||} GNil \<Delta> \<and>  wfPhi \<Theta> \<Phi>" using ** by metis
  ultimately show ?thesis  using wfX_wfY  ** infer_e_valI by metis
qed

section \<open>Statements\<close>

lemma check_s_v_unit:
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> (\<lbrace> z : B_unit | TRUE \<rbrace>) \<lesssim> \<tau>"  and "wfD \<Theta> \<B> \<Gamma> \<Delta>" and "wfPhi \<Theta> \<Phi>"
  shows  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AS_val (V_lit L_unit ) \<Leftarrow> \<tau>" 
proof - 
  have "wfG \<Theta> \<B> \<Gamma>" using assms subtype_g_wf by meson
  moreover hence "wfTh \<Theta>" using wfG_wf by simp
  moreover obtain z'::x where "atom z' \<sharp> \<Gamma>" using obtain_fresh by auto
  ultimately have *:"\<Theta>; \<B>; \<Gamma> \<turnstile> V_lit L_unit \<Rightarrow> \<lbrace> z' : B_unit | CE_val (V_var z')  ==  CE_val (V_lit L_unit)  \<rbrace>" 
    using infer_v_litI infer_unitI by simp
  moreover have "wfT \<Theta> \<B> \<Gamma> (\<lbrace> z' : B_unit | CE_val (V_var z')  ==  CE_val (V_lit L_unit)  \<rbrace>)" using infer_v_t_wf
    by (meson calculation)
  moreover then have  "\<Theta>; \<B>; \<Gamma> \<turnstile> (\<lbrace> z' : B_unit | CE_val (V_var z')  ==  CE_val (V_lit L_unit)  \<rbrace>)  \<lesssim> \<tau>" using subtype_trans subtype_top assms 
      type_for_lit.simps(4) wfX_wfY by metis
  ultimately show  ?thesis using  check_valI assms * by auto
qed

lemma check_s_check_branch_s_wf:
  fixes s::s and cs::branch_s and \<Theta>::\<Theta> and \<Phi>::\<Phi> and \<Gamma>::\<Gamma> and \<Delta>::\<Delta> and v::v and \<tau>::\<tau> and css::branch_list
  shows "\<Theta> ; \<Phi> ; B ; \<Gamma> ; \<Delta> \<turnstile> s \<Leftarrow> \<tau>        \<Longrightarrow> \<Theta> ; B \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and>  wfTh \<Theta> \<and> wfD \<Theta> B \<Gamma> \<Delta> \<and> wfT \<Theta> B \<Gamma> \<tau> \<and> wfPhi \<Theta> \<Phi> " and 
    "check_branch_s \<Theta> \<Phi> B \<Gamma> \<Delta>  tid cons const v cs  \<tau> \<Longrightarrow> \<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and>  wfTh \<Theta> \<and> wfD \<Theta> B \<Gamma> \<Delta> \<and> wfT \<Theta> B \<Gamma> \<tau> \<and> wfPhi \<Theta> \<Phi> "
    "check_branch_list \<Theta> \<Phi> B \<Gamma> \<Delta>  tid dclist v css  \<tau> \<Longrightarrow> \<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and>  wfTh \<Theta> \<and> wfD \<Theta> B \<Gamma> \<Delta> \<and> wfT \<Theta> B \<Gamma> \<tau> \<and> wfPhi \<Theta> \<Phi> " 
proof(induct rule: check_s_check_branch_s_check_branch_list.inducts)
  case (check_valI \<Theta> B \<Gamma> \<Delta> \<Phi> v \<tau>' \<tau>)
  then show ?case using infer_v_wf  infer_v_wf subtype_wf wfX_wfY wfS_valI 
    by (metis subtype_eq_base2)
next
  case (check_letI x \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e \<tau> z s b c)
  then have *:"wfT \<Theta> \<B> ((x, b , c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>) \<tau>" by force
  moreover have "atom x \<sharp> \<tau>" using check_letI fresh_prodN by force
  ultimately have "\<Theta>; \<B>;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>" using wfT_restrict2 by force
  then show ?case  using check_letI  infer_e_wf wfS_letI wfX_wfY wfG_elims by metis
next
  case (check_assertI x \<Theta> \<Phi> \<B> \<Gamma> \<Delta> c \<tau> s)
  then have *:"wfT \<Theta> \<B> ((x, B_bool , c) #\<^sub>\<Gamma> \<Gamma>) \<tau>" by force
  moreover have "atom x \<sharp> \<tau>" using check_assertI fresh_prodN by force
  ultimately have "\<Theta>; \<B>;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>" using wfT_restrict2 by force
  then show ?case  using check_assertI   wfS_assertI wfX_wfY wfG_elims by metis
next
  case (check_branch_s_branchI \<Theta> \<B> \<Gamma> \<Delta> \<tau> cons const x v \<Phi> s tid)
  then show ?case using wfX_wfY by metis
next
  case (check_branch_list_consI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist' v cs \<tau> css )
  then show ?case using wfX_wfY by metis
next
  case (check_branch_list_finalI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist' v cs \<tau> )
  then show ?case using wfX_wfY by metis
next
  case (check_ifI z \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v s1 s2 \<tau>)
  hence *:"wfT \<Theta>  \<B> \<Gamma> (\<lbrace> z : b_of \<tau>  | CE_val v  ==  CE_val (V_lit L_false) IMP  c_of \<tau> z  \<rbrace>)" (is "wfT \<Theta>  \<B> \<Gamma> ?tau") by auto
  hence "wfT \<Theta> \<B> \<Gamma> \<tau>" using wfT_wfT_if1 check_ifI  fresh_prodN by metis
  hence " \<Theta>; \<B>; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<tau> " using check_ifI b_of_c_of_eq fresh_prodN by auto
  thus ?case using check_ifI by metis
next
  case (check_let2I x \<Theta> \<Phi> \<B> G \<Delta> t s1 \<tau> s2)
  then have "wfT \<Theta> \<B> ((x, b_of t, (c_of t x)) #\<^sub>\<Gamma> G) \<tau>" by fastforce
  moreover have "atom x \<sharp> \<tau>" using check_let2I by force
  ultimately have "wfT \<Theta> \<B>  G \<tau>" using wfT_restrict2 by metis
  then show ?case using check_let2I by argo
next
  case (check_varI u \<Delta> P G v \<tau>' \<Phi> s \<tau>)
  then show ?case using wfG_elims wfD_elims 
      list.distinct list.inject by metis
next
  case (check_assignI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> u \<tau> v z \<tau>')
  obtain z'::x where *:"atom z' \<sharp> \<Gamma>" using obtain_fresh by metis
  moreover have "\<lbrace> z : B_unit | TRUE \<rbrace> = \<lbrace> z' : B_unit | TRUE \<rbrace>" by auto
  moreover hence "wfT \<Theta> \<B> \<Gamma> \<lbrace> z' : B_unit |TRUE \<rbrace>" using wfT_TRUE check_assignI check_v_wf * wfB_unitI wfG_wf by metis
  ultimately show ?case  using check_v.cases infer_v_wf  subtype_wf check_assignI wfT_wf check_v_wf wfG_wf
    by (meson subtype_wf)
next
  case (check_whileI \<Phi> \<Delta> G P s1 z s2 \<tau>')
  then show ?case using subtype_wf subtype_wf by auto
next
  case (check_seqI \<Delta> G P s1 z s2 \<tau>)
  then show ?case by fast
next
  case (check_caseI \<Theta> \<Phi> \<B> \<Gamma> \<Delta>  dclist cs \<tau> tid v z)
  then show ?case by fast
qed

lemma check_s_check_branch_s_wfS:
  fixes s::s and cs::branch_s and \<Theta>::\<Theta> and \<Phi>::\<Phi> and \<Gamma>::\<Gamma> and \<Delta>::\<Delta> and v::v and \<tau>::\<tau> and css::branch_list
  shows "\<Theta> ; \<Phi> ; B ; \<Gamma> ; \<Delta> \<turnstile> s \<Leftarrow> \<tau>        \<Longrightarrow>   \<Theta> ; \<Phi> ; B ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b_of \<tau>  " and 
    "check_branch_s \<Theta> \<Phi> B \<Gamma> \<Delta>  tid cons const v cs  \<tau> \<Longrightarrow>  wfCS \<Theta> \<Phi> B \<Gamma> \<Delta> tid cons const cs (b_of \<tau>)"
    "check_branch_list \<Theta> \<Phi> B \<Gamma> \<Delta>  tid dclist v css  \<tau> \<Longrightarrow>  wfCSS \<Theta> \<Phi> B \<Gamma> \<Delta> tid dclist css (b_of \<tau>)" 
proof(induct rule: check_s_check_branch_s_check_branch_list.inducts)
  case (check_valI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v \<tau>' \<tau>)
  then show ?case using infer_v_wf  infer_v_wf subtype_wf wfX_wfY wfS_valI 
    by (metis subtype_eq_base2)
next
  case (check_letI x \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e \<tau> z s b c)
  show ?case proof
    show \<open> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b \<close> using infer_e_wf check_letI b_of.simps by metis
    show \<open> \<Theta> ; \<Phi> ; \<B> ; (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b_of \<tau> \<close>  
      using check_letI b_of.simps wf_replace_true2(2)[OF check_letI(5)]   append_g.simps by metis
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close>  using infer_e_wf check_letI b_of.simps by metis
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>, e, b_of \<tau>)\<close> 
      apply(simp add: fresh_prodN, intro conjI)
      using  check_letI(1) fresh_prod7 by simp+ 
  qed
next
  case (check_assertI x \<Theta> \<Phi> \<B> \<Gamma> \<Delta> c \<tau> s)
  show ?case proof

    show \<open> \<Theta> ; \<Phi> ; \<B> ; (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b_of \<tau> \<close> using check_assertI by auto
  next
    show \<open> \<Theta>; \<B>; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c \<close> using check_assertI by auto
  next
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using check_assertI by auto
  next
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>, c, b_of \<tau>, s)\<close> using check_assertI by auto
  qed
next
  case (check_branch_s_branchI \<Theta> \<B> \<Gamma> \<Delta> \<tau> const x \<Phi> tid cons v s)
  show ?case proof
    show \<open> \<Theta> ; \<Phi> ; \<B> ; (x, b_of const, TRUE) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b_of \<tau> \<close> 
      using wf_replace_true append_g.simps check_branch_s_branchI by metis
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>, \<Gamma>, const)\<close> 
      using wf_replace_true append_g.simps check_branch_s_branchI fresh_prodN by metis
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wf_replace_true append_g.simps check_branch_s_branchI by metis
  qed
next
  case (check_branch_list_consI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid cons const v cs \<tau> dclist css)
  then show ?case using wf_intros by metis
next
  case (check_branch_list_finalI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid cons const v cs \<tau>)
  then show ?case using wf_intros by metis
next
  case (check_ifI z \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v s1 s2 \<tau>)
  show ?case using wfS_ifI check_v_wf check_ifI b_of.simps by metis
next
  case (check_let2I x \<Theta> \<Phi> \<B> G \<Delta> t s1 \<tau> s2)
  show ?case proof
    show \<open> \<Theta> ; \<Phi> ; \<B> ; G ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s1 : b_of t \<close>  using check_let2I  b_of.simps by metis 
    show \<open> \<Theta>; \<B>; G   \<turnstile>\<^sub>w\<^sub>f t \<close>  using  check_let2I check_s_check_branch_s_wf  by metis
    show \<open> \<Theta> ; \<Phi> ; \<B> ; (x, b_of t, TRUE) #\<^sub>\<Gamma> G ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s2 : b_of \<tau> \<close>  
      using check_let2I(5) wf_replace_true2(2) append_g.simps check_let2I by metis 
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>, \<B>, G, \<Delta>, s1, b_of \<tau>, t)\<close>  
      apply(simp add: fresh_prodN, intro conjI)
      using  check_let2I(1) fresh_prod7 by simp+ 
  qed
next
  case (check_varI u \<Theta> \<Phi> \<B> \<Gamma> \<Delta> \<tau>' v \<tau> s)
  show ?case proof
    show \<open> \<Theta>; \<B>; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<tau>' \<close> using check_v_wf check_varI by metis
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b_of \<tau>' \<close>  using check_v_wf check_varI by metis
    show \<open>atom u \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>, \<tau>', v, b_of \<tau>)\<close>  using check_varI fresh_prodN u_fresh_b by metis
    show \<open> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; (u, \<tau>') #\<^sub>\<Delta>\<Delta> \<turnstile>\<^sub>w\<^sub>f s : b_of \<tau> \<close>  using check_varI by metis
  qed   
next
  case (check_assignI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> u \<tau> v z \<tau>')
  then show ?case using wf_intros check_v_wf subtype_eq_base2 b_of.simps by metis
next
  case (check_whileI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 z s2 \<tau>')
  thus ?case using wf_intros  b_of.simps  check_v_wf subtype_eq_base2 b_of.simps by metis
next
  case (check_seqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 z s2 \<tau>)
  thus ?case using wf_intros  b_of.simps  by metis
next
  case (check_caseI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist v cs \<tau> z)
  show  ?case proof
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : B_id tid \<close> using check_caseI check_v_wf b_of.simps  by metis
    show \<open>AF_typedef tid dclist \<in> set \<Theta>\<close>  using check_caseI by metis
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close>  using check_caseI check_s_check_branch_s_wf by metis
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close>  using check_caseI check_s_check_branch_s_wf  by metis
    show \<open> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f cs : b_of \<tau> \<close>  using check_caseI by metis
  qed
qed

lemma check_s_wf:
  fixes s::s
  assumes "\<Theta> ; \<Phi> ; B ; \<Gamma> ; \<Delta> \<turnstile> s \<Leftarrow> \<tau>"
  shows "\<Theta> ; B \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and> wfT \<Theta> B \<Gamma> \<tau> \<and> wfPhi \<Theta> \<Phi> \<and> wfTh \<Theta> \<and> wfD \<Theta> B \<Gamma> \<Delta> \<and> wfS  \<Theta> \<Phi> B \<Gamma> \<Delta> s (b_of \<tau>)"  
  using check_s_check_branch_s_wf check_s_check_branch_s_wfS assms  by meson

lemma check_s_flip_u1:
  fixes s::s and u::u and u'::u
  assumes  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> s \<Leftarrow> \<tau>"
  shows "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; ( u \<leftrightarrow> u') \<bullet> \<Delta>  \<turnstile> (u \<leftrightarrow> u') \<bullet> s \<Leftarrow>  \<tau>" 
proof - 
  have  "(u \<leftrightarrow> u') \<bullet> \<Theta> ; (u \<leftrightarrow> u') \<bullet> \<Phi> ;  (u \<leftrightarrow> u') \<bullet>  \<B> ; (u \<leftrightarrow> u') \<bullet>  \<Gamma> ;  (u \<leftrightarrow> u') \<bullet> \<Delta>    \<turnstile> (u \<leftrightarrow> u') \<bullet> s \<Leftarrow> (u \<leftrightarrow> u') \<bullet> \<tau>" 
    using check_s.eqvt assms  by blast
  thus  ?thesis using check_s_wf[OF assms] flip_u_eq phi_flip_eq  by metis
qed

lemma check_s_flip_u2: 
  fixes s::s and u::u and u'::u
  assumes "\<Theta> ; \<Phi> ;  B ; \<Gamma> ; ( u \<leftrightarrow> u') \<bullet> \<Delta>   \<turnstile> (u \<leftrightarrow> u') \<bullet> s \<Leftarrow>  \<tau>" 
  shows "\<Theta> ; \<Phi> ;  B ; \<Gamma> ; \<Delta>  \<turnstile> s \<Leftarrow> \<tau>"
proof - 
  have "\<Theta> ; \<Phi> ; B ; \<Gamma> ; ( u \<leftrightarrow> u') \<bullet> ( u \<leftrightarrow> u') \<bullet> \<Delta>   \<turnstile> ( u \<leftrightarrow> u') \<bullet> (u \<leftrightarrow> u') \<bullet> s \<Leftarrow>  \<tau>" 
    using check_s_flip_u1 assms by blast
  thus ?thesis using  permute_flip_cancel by force
qed

lemma check_s_flip_u:
  fixes s::s and u::u and u'::u
  shows "\<Theta> ; \<Phi> ; B ; \<Gamma> ; ( u \<leftrightarrow> u') \<bullet> \<Delta>  \<turnstile> (u \<leftrightarrow> u') \<bullet> s \<Leftarrow>  \<tau> = (\<Theta> ; \<Phi> ; B ; \<Gamma> ; \<Delta> \<turnstile> s \<Leftarrow> \<tau>)"
  using check_s_flip_u1  check_s_flip_u2 by metis

lemma check_s_abs_u:
  fixes s::s and s'::s and u::u and u'::u and \<tau>'::\<tau>
  assumes "[[atom u]]lst. s = [[atom u']]lst. s'" and "atom u \<sharp> \<Delta>" and "atom u' \<sharp> \<Delta>"
    and "\<Theta> ; B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>'" 
    and "\<Theta> ; \<Phi> ; B ; \<Gamma> ; ( u , \<tau>') #\<^sub>\<Delta>\<Delta>  \<turnstile> s \<Leftarrow>  \<tau>"
  shows "\<Theta> ; \<Phi> ; B ; \<Gamma> ; ( u', \<tau>' ) #\<^sub>\<Delta>\<Delta> \<turnstile> s' \<Leftarrow> \<tau>"
proof -
  have "\<Theta> ; \<Phi> ; B ; \<Gamma> ; ( u' \<leftrightarrow> u) \<bullet> (( u , \<tau>') #\<^sub>\<Delta>\<Delta>)  \<turnstile> ( u' \<leftrightarrow> u) \<bullet> s \<Leftarrow>  \<tau>"
    using assms check_s_flip_u by metis
  moreover have " ( u' \<leftrightarrow> u) \<bullet> (( u , \<tau>') #\<^sub>\<Delta> \<Delta>) = ( u' , \<tau>') #\<^sub>\<Delta>\<Delta>" proof -
    have " ( u' \<leftrightarrow> u) \<bullet> (( u , \<tau>') #\<^sub>\<Delta> \<Delta>) = ((u' \<leftrightarrow> u) \<bullet> u, (u' \<leftrightarrow> u) \<bullet> \<tau>') #\<^sub>\<Delta> (u' \<leftrightarrow> u) \<bullet> \<Delta>"  
      using  DCons_eqvt  Pair_eqvt by auto
    also have "... = ( u' , (u' \<leftrightarrow> u) \<bullet> \<tau>') #\<^sub>\<Delta> \<Delta>" 
      using assms flip_fresh_fresh by auto
    also have "... = ( u' , \<tau>') #\<^sub>\<Delta> \<Delta>" using
        u_not_in_t fresh_def flip_fresh_fresh assms by metis
    finally show ?thesis by auto
  qed
  moreover have "( u' \<leftrightarrow> u) \<bullet> s = s'" using assms Abs1_eq_iff(3)[of u' s' u s] by auto
  ultimately show ?thesis by auto
qed

section \<open>Additional Elimination and Intros\<close>

subsection  \<open>Values\<close> 

nominal_function b_for :: "opp \<Rightarrow> b" where
  "b_for Plus = B_int"
| "b_for LEq = B_bool" | "b_for Eq = B_bool"
  apply(auto,simp add: eqvt_def b_for_graph_aux_def )
  by (meson opp.exhaust)
nominal_termination (eqvt)  by lexicographic_order


lemma infer_v_pair2I:
  fixes  v\<^sub>1::v and  v\<^sub>2::v
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> v\<^sub>1 \<Rightarrow> \<tau>\<^sub>1" and "\<Theta>; \<B>; \<Gamma> \<turnstile> v\<^sub>2 \<Rightarrow> \<tau>\<^sub>2"
  shows "\<exists>\<tau>. \<Theta>; \<B>; \<Gamma> \<turnstile> V_pair v\<^sub>1 v\<^sub>2 \<Rightarrow> \<tau> \<and> b_of \<tau> = B_pair (b_of \<tau>\<^sub>1) (b_of \<tau>\<^sub>2)"
proof - 
  obtain z1 and b1 and c1 and z2 and b2 and c2 where zbc: "\<tau>\<^sub>1 = (\<lbrace> z1 : b1 | c1 \<rbrace>) \<and> \<tau>\<^sub>2 = (\<lbrace> z2 : b2 | c2 \<rbrace>)"
    using \<tau>.exhaust by meson
  obtain z::x where "atom z \<sharp> ( v\<^sub>1, v\<^sub>2,\<Theta>, \<B>,\<Gamma>)" using obtain_fresh
    by blast
  hence "atom z \<sharp> ( v\<^sub>1, v\<^sub>2) \<and> atom z \<sharp> (\<Theta>, \<B>,\<Gamma>)" using fresh_prodN by metis
  hence " \<Theta>; \<B>; \<Gamma> \<turnstile> V_pair v\<^sub>1 v\<^sub>2 \<Rightarrow> \<lbrace> z : [ b_of \<tau>\<^sub>1 , b_of \<tau>\<^sub>2 ]\<^sup>b  | CE_val (V_var z)  ==  CE_val (V_pair v\<^sub>1 v\<^sub>2)  \<rbrace>"  
    using assms infer_v_pairI zbc by metis
  moreover obtain \<tau> where "\<tau> = (\<lbrace> z : B_pair b1 b2  | CE_val (V_var z)  ==  CE_val (V_pair v\<^sub>1 v\<^sub>2)  \<rbrace>)" by blast
  moreover hence "b_of \<tau> = B_pair (b_of \<tau>\<^sub>1) (b_of \<tau>\<^sub>2)" using b_of.simps zbc by presburger
  ultimately show ?thesis using b_of.simps by metis
qed

lemma infer_v_pair2I_zbc:
  fixes  v\<^sub>1::v and  v\<^sub>2::v
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> v\<^sub>1 \<Rightarrow> \<tau>\<^sub>1" and "\<Theta>; \<B>; \<Gamma> \<turnstile> v\<^sub>2 \<Rightarrow> \<tau>\<^sub>2"
  shows "\<exists>z \<tau>. \<Theta>; \<B>; \<Gamma> \<turnstile> V_pair v\<^sub>1 v\<^sub>2 \<Rightarrow> \<tau> \<and> \<tau> = (\<lbrace> z : B_pair (b_of \<tau>\<^sub>1) (b_of \<tau>\<^sub>2) | C_eq (CE_val (V_var z)) (CE_val (V_pair v\<^sub>1 v\<^sub>2)) \<rbrace>) \<and> atom z \<sharp> (v\<^sub>1,v\<^sub>2) \<and> atom z \<sharp> \<Gamma>"
proof - 
  obtain z1 and b1 and c1 and z2 and b2 and c2 where zbc: "\<tau>\<^sub>1 = (\<lbrace> z1 : b1 | c1 \<rbrace>) \<and> \<tau>\<^sub>2 = (\<lbrace> z2 : b2 | c2 \<rbrace>)"
    using \<tau>.exhaust by meson
  obtain z::x where * : "atom z \<sharp> ( v\<^sub>1, v\<^sub>2,\<Gamma>,\<Theta> , \<B> )"  using obtain_fresh
    by blast
  hence vinf: " \<Theta>; \<B>; \<Gamma> \<turnstile> V_pair v\<^sub>1 v\<^sub>2 \<Rightarrow> \<lbrace> z :[ b_of \<tau>\<^sub>1 , b_of \<tau>\<^sub>2 ]\<^sup>b  | CE_val (V_var z)  ==  CE_val (V_pair v\<^sub>1 v\<^sub>2)  \<rbrace>"  
    using assms infer_v_pairI by simp
  moreover obtain \<tau> where "\<tau> = (\<lbrace> z : B_pair b1 b2  | CE_val (V_var z)  ==  CE_val (V_pair v\<^sub>1 v\<^sub>2)  \<rbrace>)" by blast
  moreover have "b_of \<tau>\<^sub>1 = b1 \<and> b_of \<tau>\<^sub>2 = b2" using zbc b_of.simps by auto
  ultimately have "\<Theta>; \<B>; \<Gamma> \<turnstile> V_pair v\<^sub>1 v\<^sub>2 \<Rightarrow> \<tau> \<and> \<tau> = (\<lbrace> z : B_pair (b_of \<tau>\<^sub>1) (b_of \<tau>\<^sub>2) | CE_val (V_var z)  ==  CE_val (V_pair v\<^sub>1 v\<^sub>2)  \<rbrace>)" by auto
  thus ?thesis using * fresh_prod2 fresh_prod3 by metis
qed

lemma infer_v_pair2E:
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> V_pair v\<^sub>1 v\<^sub>2 \<Rightarrow> \<tau>"
  shows "\<exists>\<tau>\<^sub>1 \<tau>\<^sub>2 z . \<Theta>; \<B>; \<Gamma> \<turnstile> v\<^sub>1 \<Rightarrow> \<tau>\<^sub>1 \<and> \<Theta>; \<B>; \<Gamma> \<turnstile> v\<^sub>2 \<Rightarrow> \<tau>\<^sub>2 \<and> 
           \<tau> = (\<lbrace> z : B_pair (b_of \<tau>\<^sub>1) (b_of \<tau>\<^sub>2) | C_eq (CE_val (V_var z)) (CE_val (V_pair v\<^sub>1 v\<^sub>2)) \<rbrace>) \<and> atom z \<sharp>  (v\<^sub>1, v\<^sub>2)" 
proof - 
  obtain z and t1 and t2 where 
    "\<tau> = (\<lbrace> z : B_pair (b_of t1) (b_of t2)  | CE_val (V_var z)  ==  CE_val (V_pair v\<^sub>1 v\<^sub>2)  \<rbrace>) \<and>
        atom z \<sharp> (v\<^sub>1, v\<^sub>2) \<and>  \<Theta>; \<B>; \<Gamma> \<turnstile> v\<^sub>1 \<Rightarrow> t1 \<and>  \<Theta>; \<B>; \<Gamma> \<turnstile> v\<^sub>2 \<Rightarrow> t2 " using infer_v_elims(3)[OF assms ] by metis 
  thus ?thesis using b_of.simps  by metis
qed

subsection  \<open>Expressions\<close>

lemma infer_e_app2E:
  fixes \<Phi>::\<Phi> and \<Theta>::\<Theta>
  assumes "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_app f v \<Rightarrow> \<tau>"
  shows "\<exists>x b c s' \<tau>'.  wfD  \<Theta> \<B> \<Gamma> \<Delta> \<and> Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c \<tau>' s'))) = lookup_fun \<Phi> f \<and>  \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> \<and>
       \<Theta>; \<B>; \<Gamma> \<turnstile> v \<Leftarrow> \<lbrace> x : b  | c \<rbrace> \<and> \<tau> = \<tau>'[x::=v]\<^sub>\<tau>\<^sub>v \<and> atom x \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>, v, \<tau>)"
  using infer_e_elims(6)[OF assms] b_of.simps subst_defs by metis

lemma infer_e_appP2E:
  fixes \<Phi>::\<Phi> and \<Theta>::\<Theta>
  assumes "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_appP f b v \<Rightarrow> \<tau>"
  shows "\<exists>bv x ba c s' \<tau>'.  wfD  \<Theta> \<B> \<Gamma> \<Delta> \<and> Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x ba c \<tau>' s'))) = lookup_fun \<Phi> f \<and>  \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> \<and>  \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f b   \<and>
      (\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Leftarrow> \<lbrace> x : ba[bv::=b]\<^sub>b\<^sub>b  | c[bv::=b]\<^sub>c\<^sub>b \<rbrace>) \<and> (\<tau> = \<tau>'[bv::=b]\<^sub>\<tau>\<^sub>b[x::=v]\<^sub>\<tau>\<^sub>v) \<and> atom x \<sharp> \<Gamma> \<and> atom bv \<sharp> v"
proof -
  obtain bv x ba c s' \<tau>' where *:"wfD  \<Theta> \<B> \<Gamma> \<Delta> \<and> Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x ba c \<tau>' s'))) = lookup_fun \<Phi> f \<and>  \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> \<and>  \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f b   \<and>
      (\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Leftarrow> \<lbrace> x : ba[bv::=b]\<^sub>b\<^sub>b  | c[bv::=b]\<^sub>c\<^sub>b \<rbrace>) \<and> (\<tau> = \<tau>'[bv::=b]\<^sub>\<tau>\<^sub>b[x::=v]\<^sub>\<tau>\<^sub>v) \<and> atom x \<sharp> \<Gamma> \<and> atom bv \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>, b, v, \<tau>)" 
    using infer_e_elims(21)[OF assms] subst_defs by metis
  moreover then have "atom bv \<sharp> v" using fresh_prodN by metis
  ultimately show ?thesis by metis
qed

section \<open>Weakening\<close>

text \<open> Lemmas showing that typing judgements hold when a context is extended \<close>

lemma subtype_weakening:
  fixes \<Gamma>'::\<Gamma>
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> \<tau>1 \<lesssim> \<tau>2" and  "toSet \<Gamma> \<subseteq> toSet \<Gamma>'" and "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>'" 
  shows  "\<Theta>; \<B>; \<Gamma>' \<turnstile> \<tau>1 \<lesssim> \<tau>2"
  using assms proof(nominal_induct \<tau>2 avoiding: \<Gamma>' rule: subtype.strong_induct)

  case (subtype_baseI x \<Theta> \<B> \<Gamma> z c z' c' b)
  show ?case proof
    show *:"\<Theta>; \<B>; \<Gamma>'   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b  | c \<rbrace>" using wfT_weakening subtype_baseI by metis
    show "\<Theta>; \<B>; \<Gamma>'   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z' : b  | c' \<rbrace>" using wfT_weakening subtype_baseI by metis
    show "atom x \<sharp> (\<Theta>, \<B>, \<Gamma>',  z ,  c ,  z' ,  c' )" using subtype_baseI fresh_Pair by metis
    have "toSet ((x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>) \<subseteq>  toSet ((x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>')" using subtype_baseI toSet.simps by blast
    moreover have "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f (x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>'" using wfT_wf_cons3[OF *, of x] subtype_baseI fresh_Pair subst_defs by metis
    ultimately show "\<Theta>; \<B>; (x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>'  \<Turnstile> c'[z'::=V_var x]\<^sub>v" using valid_weakening subtype_baseI by metis
  qed
qed

method many_rules uses add = ( (rule+),((simp add: add)+)?)

lemma infer_v_g_weakening:
  fixes e::e and \<Gamma>'::\<Gamma> and v::v
  assumes "\<Theta>;  \<B> ; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>" and "toSet \<Gamma> \<subseteq> toSet \<Gamma>'" and "\<Theta>  ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>'"
  shows   "\<Theta>;  \<B> ; \<Gamma>' \<turnstile> v \<Rightarrow> \<tau>"
  using assms proof(nominal_induct   avoiding: \<Gamma>'  rule: infer_v.strong_induct)
  case (infer_v_varI \<Theta> \<B> \<Gamma> b c x' z)  
  show ?case proof
    show \<open> \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<close> using infer_v_varI by auto
    show \<open>Some (b, c) = lookup \<Gamma>' x'\<close> using infer_v_varI lookup_weakening by metis
    show \<open>atom z \<sharp> x'\<close> using infer_v_varI by auto
    show \<open>atom z \<sharp> (\<Theta>, \<B>, \<Gamma>')\<close> using infer_v_varI by auto
  qed
next
  case (infer_v_litI \<Theta> \<B> \<Gamma> l \<tau>)
  then show ?case using infer_v.intros by simp
next
  case (infer_v_pairI z v1 v2 \<Theta> \<B> \<Gamma> t1 t2)
  then show ?case using infer_v.intros by simp
next
  case (infer_v_consI s dclist \<Theta> dc tc \<B> \<Gamma> v tv z)
  show ?case proof 
    show \<open>AF_typedef s dclist \<in> set \<Theta>\<close> using infer_v_consI by auto
    show \<open>(dc, tc) \<in> set dclist\<close> using infer_v_consI by auto
    show \<open> \<Theta>; \<B>; \<Gamma>' \<turnstile> v \<Rightarrow> tv\<close> using infer_v_consI by auto
    show \<open>\<Theta>; \<B>; \<Gamma>'  \<turnstile> tv \<lesssim> tc\<close> using infer_v_consI subtype_weakening by auto
    show \<open>atom z \<sharp> v\<close> using infer_v_consI by auto
    show \<open>atom z \<sharp> (\<Theta>, \<B>, \<Gamma>')\<close> using infer_v_consI by auto
  qed
next
  case (infer_v_conspI s bv dclist \<Theta> dc tc \<B> \<Gamma> v tv b z)
  show ?case proof
    show \<open>AF_typedef_poly s bv dclist \<in> set \<Theta>\<close> using infer_v_conspI by auto
    show \<open>(dc, tc) \<in> set dclist\<close> using infer_v_conspI by auto 
    show \<open> \<Theta>; \<B>; \<Gamma>' \<turnstile> v \<Rightarrow> tv\<close> using infer_v_conspI by auto
    show \<open>\<Theta>; \<B>; \<Gamma>'  \<turnstile> tv \<lesssim> tc[bv::=b]\<^sub>\<tau>\<^sub>b\<close> using infer_v_conspI subtype_weakening by auto
    show \<open>atom z \<sharp> (\<Theta>, \<B>, \<Gamma>', v, b)\<close> using infer_v_conspI by auto
    show \<open>atom bv \<sharp> (\<Theta>, \<B>, \<Gamma>', v, b)\<close> using infer_v_conspI by auto
    show \<open> \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f b \<close> using infer_v_conspI by auto
  qed
qed

lemma check_v_g_weakening:
  fixes e::e and \<Gamma>'::\<Gamma>
  assumes "\<Theta>;  \<B> ; \<Gamma> \<turnstile> v \<Leftarrow> \<tau>" and "toSet \<Gamma> \<subseteq> toSet \<Gamma>'" and "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>'" 
  shows   "\<Theta>;  \<B> ; \<Gamma>' \<turnstile> v \<Leftarrow> \<tau>"
  using subtype_weakening infer_v_g_weakening check_v_elims  check_v_subtypeI assms by metis

lemma infer_e_g_weakening:
  fixes e::e and \<Gamma>'::\<Gamma>
  assumes "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> e \<Rightarrow> \<tau>" and "toSet \<Gamma> \<subseteq> toSet \<Gamma>'" and "\<Theta> ;  \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>'"
  shows   "\<Theta> ; \<Phi> ;  \<B> ; \<Gamma>'; \<Delta> \<turnstile> e \<Rightarrow> \<tau>"
  using assms proof(nominal_induct \<tau> avoiding: \<Gamma>'  rule: infer_e.strong_induct)
  case (infer_e_valI \<Theta> \<B> \<Gamma> \<Delta>' \<Phi> v \<tau>)
  then show ?case using infer_v_g_weakening wf_weakening infer_e.intros by metis
next
  case (infer_e_plusI \<Theta>  \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 c2 z3)

  obtain z'::x where z': "atom z' \<sharp> v1 \<and> atom z' \<sharp> v2 \<and> atom z' \<sharp> \<Gamma>'" using obtain_fresh fresh_prod3 by metis
  moreover hence  *:"\<lbrace> z3 : B_int  | CE_val (V_var z3)  ==  CE_op Plus [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e  \<rbrace> = (\<lbrace> z' : B_int  | CE_val (V_var z')  ==  CE_op Plus [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e  \<rbrace>)" 
    using infer_e_plusI type_e_eq ce.fresh fresh_e_opp by auto

  have "\<Theta> ; \<Phi> ;  \<B> ; \<Gamma>' ; \<Delta>  \<turnstile> AE_op Plus v1 v2 \<Rightarrow> \<lbrace> z' : B_int  | CE_val (V_var z')  ==  CE_op Plus  [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e  \<rbrace>" proof
    show \<open> \<Theta> ;  \<B> ; \<Gamma>'  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wf_weakening infer_e_plusI by auto
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using infer_e_plusI by auto
    show \<open> \<Theta> ;  \<B> ; \<Gamma>'  \<turnstile> v1 \<Rightarrow> \<lbrace> z1 : B_int  | c1 \<rbrace>\<close> using infer_v_g_weakening infer_e_plusI by auto
    show \<open> \<Theta> ;  \<B> ; \<Gamma>'  \<turnstile> v2 \<Rightarrow> \<lbrace> z2 : B_int  | c2 \<rbrace>\<close> using infer_v_g_weakening infer_e_plusI by auto
    show \<open>atom z' \<sharp> AE_op Plus v1 v2\<close> using z'  by auto
    show \<open>atom z' \<sharp> \<Gamma>'\<close> using z' by auto
  qed
  thus ?case using * by metis

next
  case (infer_e_leqI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 c2 z3)
  obtain z'::x where z': "atom z' \<sharp> v1 \<and> atom z' \<sharp> v2 \<and> atom z' \<sharp> \<Gamma>'" using obtain_fresh fresh_prod3 by metis

  moreover hence  *:"\<lbrace> z3 : B_bool  | CE_val (V_var z3)  ==  CE_op LEq  [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e  \<rbrace> = (\<lbrace> z' : B_bool  | CE_val (V_var z')  ==  CE_op LEq  [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e  \<rbrace>)" 
    using infer_e_leqI type_e_eq ce.fresh fresh_e_opp by auto

  have "\<Theta> ; \<Phi> ;  \<B> ; \<Gamma>' ; \<Delta>  \<turnstile> AE_op LEq v1 v2 \<Rightarrow> \<lbrace> z' : B_bool  | CE_val (V_var z')  ==  CE_op LEq  [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e  \<rbrace>" proof
    show \<open> \<Theta> ;  \<B> ; \<Gamma>'  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wf_weakening infer_e_leqI by auto
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using infer_e_leqI by auto
    show \<open> \<Theta> ;  \<B> ; \<Gamma>'  \<turnstile> v1 \<Rightarrow> \<lbrace> z1 : B_int  | c1 \<rbrace>\<close> using infer_v_g_weakening infer_e_leqI by auto
    show \<open> \<Theta> ;  \<B> ; \<Gamma>'  \<turnstile> v2 \<Rightarrow> \<lbrace> z2 : B_int  | c2 \<rbrace>\<close> using infer_v_g_weakening infer_e_leqI by auto
    show \<open>atom z' \<sharp> AE_op LEq v1 v2\<close> using z'  by auto
    show \<open>atom z' \<sharp> \<Gamma>'\<close> using z' by auto
  qed
  thus ?case using * by metis
next
  case (infer_e_eqI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 bb c1 v2 z2 c2 z3)
  obtain z'::x where z': "atom z' \<sharp> v1 \<and> atom z' \<sharp> v2 \<and> atom z' \<sharp> \<Gamma>'" using obtain_fresh fresh_prod3 by metis

  moreover hence  *:"\<lbrace> z3 : B_bool  | CE_val (V_var z3)  ==  CE_op Eq  [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e  \<rbrace> = (\<lbrace> z' : B_bool  | CE_val (V_var z')  ==  CE_op Eq  [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e  \<rbrace>)" 
    using infer_e_eqI type_e_eq ce.fresh fresh_e_opp by auto

  have "\<Theta> ; \<Phi> ;  \<B> ; \<Gamma>' ; \<Delta>  \<turnstile> AE_op Eq v1 v2 \<Rightarrow> \<lbrace> z' : B_bool  | CE_val (V_var z')  ==  CE_op Eq  [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e  \<rbrace>" proof
    show \<open> \<Theta> ;  \<B> ; \<Gamma>'  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wf_weakening infer_e_eqI by auto
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using infer_e_eqI by auto
    show \<open> \<Theta> ;  \<B> ; \<Gamma>'  \<turnstile> v1 \<Rightarrow> \<lbrace> z1 : bb  | c1 \<rbrace>\<close> using infer_v_g_weakening infer_e_eqI by auto
    show \<open> \<Theta> ;  \<B> ; \<Gamma>'  \<turnstile> v2 \<Rightarrow> \<lbrace> z2 : bb  | c2 \<rbrace>\<close> using infer_v_g_weakening infer_e_eqI by auto
    show \<open>atom z' \<sharp> AE_op Eq v1 v2\<close> using z'  by auto
    show \<open>atom z' \<sharp> \<Gamma>'\<close> using z' by auto
    show "bb \<in> {B_bool, B_int, B_unit}" using infer_e_eqI by auto
  qed
  thus ?case using * by metis
next
  case (infer_e_appI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> f x b c \<tau>' s' v \<tau>)
  show ?case proof 
    show "\<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f \<Delta> "  using wf_weakening infer_e_appI by auto
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>"   using wf_weakening infer_e_appI by auto
    show "Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c \<tau>' s'))) = lookup_fun \<Phi> f"  using wf_weakening infer_e_appI by auto
    show "\<Theta>; \<B>; \<Gamma>'  \<turnstile> v \<Leftarrow> \<lbrace> x : b  | c \<rbrace>"  using wf_weakening infer_e_appI check_v_g_weakening by auto
    show "atom x \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>', \<Delta>, v, \<tau>)"  using wf_weakening infer_e_appI by auto
    show "\<tau>'[x::=v]\<^sub>v = \<tau>"  using wf_weakening infer_e_appI by auto
  qed

next
  case (infer_e_appPI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> b' f bv x b c \<tau>' s' v \<tau>)

  hence *:"\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_appP f b' v \<Rightarrow> \<tau>" using Typing.infer_e_appPI by auto

  obtain x'::x where x':"atom x' \<sharp> (s', c, \<tau>', (\<Gamma>',v,\<tau>)) \<and> (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau>' s'))) =  (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x' b ((x' \<leftrightarrow> x) \<bullet> c) ((x' \<leftrightarrow> x) \<bullet> \<tau>') ((x' \<leftrightarrow> x) \<bullet> s'))))" 
    using obtain_fresh_fun_def[of s' c \<tau>' "(\<Gamma>',v,\<tau>)" f x b]
    by (metis fun_def.eq_iff fun_typ_q.eq_iff(2))

  hence **: " \<lbrace> x : b  | c \<rbrace> = \<lbrace> x' : b  | (x' \<leftrightarrow> x) \<bullet> c \<rbrace>" 
    using fresh_PairD(1) fresh_PairD(2) type_eq_flip by blast
  have "atom x' \<sharp> \<Gamma>" using x' infer_e_appPI fresh_weakening fresh_Pair by metis

  show ?case proof(rule Typing.infer_e_appPI[where x=x' and bv=bv and b=b and c="(x' \<leftrightarrow> x) \<bullet> c" and \<tau>'="(x' \<leftrightarrow> x) \<bullet> \<tau>'"and s'="((x' \<leftrightarrow> x) \<bullet> s')"])
    show \<open> \<Theta> ;  \<B> ; \<Gamma>'  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wf_weakening infer_e_appPI by auto
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wf_weakening infer_e_appPI by auto
    show "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f b'" using infer_e_appPI by auto
    show "Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x' b ((x' \<leftrightarrow> x) \<bullet> c) ((x' \<leftrightarrow> x) \<bullet> \<tau>') ((x' \<leftrightarrow> x) \<bullet> s')))) = lookup_fun \<Phi> f" using x' infer_e_appPI by argo
    show "\<Theta>; \<B>; \<Gamma>'  \<turnstile> v \<Leftarrow> \<lbrace> x' : b[bv::=b']\<^sub>b  | ((x' \<leftrightarrow> x) \<bullet> c)[bv::=b']\<^sub>b \<rbrace>" using **
        \<tau>.eq_iff check_v_g_weakening infer_e_appPI.hyps infer_e_appPI.prems(1) infer_e_appPI.prems subst_defs
        subst_tb.simps by metis
    show "atom x' \<sharp> \<Gamma>'" using x' fresh_prodN by metis

    have "atom x \<sharp> (v, \<tau>) \<and> atom x' \<sharp> (v, \<tau>)" using x' infer_e_fresh[OF *] e.fresh(2) fresh_Pair infer_e_appPI \<open>atom x' \<sharp> \<Gamma>\<close> e.fresh by metis
    moreover then have "((x' \<leftrightarrow> x) \<bullet> \<tau>')[bv::=b']\<^sub>\<tau>\<^sub>b = (x' \<leftrightarrow> x) \<bullet> (\<tau>'[bv::=b']\<^sub>\<tau>\<^sub>b)" using  subst_b_x_flip 
      by (metis subst_b_\<tau>_def)
    ultimately show "((x' \<leftrightarrow> x) \<bullet> \<tau>')[bv::=b']\<^sub>b[x'::=v]\<^sub>v = \<tau>" 
      using infer_e_appPI subst_tv_flip subst_defs by metis

    show "atom bv \<sharp>  (\<Theta>, \<Phi>, \<B>, \<Gamma>', \<Delta>, b', v, \<tau>)" using infer_e_appPI fresh_prodN by metis
  qed

next
  case (infer_e_fstI \<Theta>  \<B> \<Gamma> \<Delta> \<Phi> v z'' b1 b2 c z)

  obtain z'::x where  *: "atom z' \<sharp> \<Gamma>' \<and> atom z' \<sharp> v \<and> atom z' \<sharp> c" using obtain_fresh_z fresh_Pair by metis 
  hence **:"\<lbrace> z : b1  | CE_val (V_var z)  ==  CE_fst [v]\<^sup>c\<^sup>e  \<rbrace> =  \<lbrace> z' : b1  | CE_val (V_var z')  ==  CE_fst [v]\<^sup>c\<^sup>e  \<rbrace>"
    using  type_e_eq infer_e_fstI v.fresh e.fresh ce.fresh obtain_fresh_z fresh_Pair by metis

  have "\<Theta> ; \<Phi> ;  \<B> ; \<Gamma>' ; \<Delta>  \<turnstile> AE_fst v \<Rightarrow> \<lbrace> z' : b1  | CE_val (V_var z')  ==  CE_fst [v]\<^sup>c\<^sup>e  \<rbrace>" proof
    show \<open> \<Theta> ;  \<B> ; \<Gamma>'  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wf_weakening infer_e_fstI by auto
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wf_weakening infer_e_fstI by auto
    show "\<Theta> ;  \<B> ; \<Gamma>'  \<turnstile> v \<Rightarrow> \<lbrace> z'' : B_pair b1 b2  |  c \<rbrace>" using infer_v_g_weakening infer_e_fstI  by metis
    show "atom z' \<sharp> AE_fst v" using * ** e.supp by auto
    show "atom z' \<sharp> \<Gamma>'" using * by auto
  qed
  thus ?case using * ** by metis
next
  case (infer_e_sndI \<Theta>  \<B> \<Gamma> \<Delta> \<Phi> v z'' b1 b2 c z)

  obtain z'::x where  *: "atom z' \<sharp> \<Gamma>' \<and> atom z' \<sharp> v \<and> atom z' \<sharp> c"  using obtain_fresh_z fresh_Pair by metis 
  hence **:"\<lbrace> z : b2  | CE_val (V_var z)  ==  CE_snd [v]\<^sup>c\<^sup>e  \<rbrace> =  \<lbrace> z' : b2  | CE_val (V_var z')  ==  CE_snd [v]\<^sup>c\<^sup>e  \<rbrace>"
    using  type_e_eq infer_e_sndI e.fresh ce.fresh obtain_fresh_z fresh_Pair by metis

  have "\<Theta> ; \<Phi> ;  \<B> ; \<Gamma>' ; \<Delta>  \<turnstile> AE_snd v \<Rightarrow> \<lbrace> z' : b2  | CE_val (V_var z')  ==  CE_snd [v]\<^sup>c\<^sup>e  \<rbrace>" proof
    show \<open> \<Theta> ;  \<B> ;\<Gamma>'  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wf_weakening infer_e_sndI by auto
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wf_weakening infer_e_sndI by auto
    show "\<Theta> ;  \<B> ; \<Gamma>'  \<turnstile> v \<Rightarrow> \<lbrace> z'' : B_pair b1 b2  |  c \<rbrace>" using infer_v_g_weakening infer_e_sndI    by metis
    show "atom z' \<sharp> AE_snd v" using * e.supp by auto
    show "atom z' \<sharp> \<Gamma>'" using * by auto
  qed
  thus ?case using ** by metis
next
  case (infer_e_lenI \<Theta>  \<B> \<Gamma> \<Delta> \<Phi> v z'' c z)

  obtain z'::x where  *: "atom z' \<sharp> \<Gamma>' \<and> atom z' \<sharp> v \<and> atom z' \<sharp> c"  using obtain_fresh_z fresh_Pair by metis 
  hence **:"\<lbrace> z : B_int  | CE_val (V_var z)  ==  CE_len [v]\<^sup>c\<^sup>e  \<rbrace> =  \<lbrace> z' : B_int  | CE_val (V_var z')  ==  CE_len [v]\<^sup>c\<^sup>e  \<rbrace>"
    using  type_e_eq infer_e_lenI e.fresh ce.fresh obtain_fresh_z fresh_Pair by metis

  have "\<Theta> ; \<Phi> ; \<B> ; \<Gamma>' ; \<Delta>  \<turnstile> AE_len v \<Rightarrow> \<lbrace> z' : B_int  | CE_val (V_var z')  ==  CE_len [v]\<^sup>c\<^sup>e  \<rbrace>" proof
    show \<open> \<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wf_weakening infer_e_lenI by auto
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wf_weakening infer_e_lenI by auto
    show "\<Theta> ;  \<B> ; \<Gamma>' \<turnstile> v \<Rightarrow> \<lbrace> z'' : B_bitvec  | c \<rbrace>" using infer_v_g_weakening infer_e_lenI    by metis
    show "atom z' \<sharp> AE_len v" using * e.supp by auto
    show "atom z' \<sharp> \<Gamma>'" using * by auto
  qed
  thus ?case using * ** by metis
next
  case (infer_e_mvarI \<Theta> \<Gamma> \<Phi> \<Delta> u \<tau>)
  then show ?case using  wf_weakening infer_e.intros by metis
next
  case (infer_e_concatI \<Theta>  \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 c2 z3)

  obtain z'::x where  *: "atom z' \<sharp> \<Gamma>' \<and> atom z' \<sharp> v1 \<and> atom z' \<sharp> v2" using obtain_fresh_z fresh_Pair by metis 
  hence **:"\<lbrace> z3 : B_bitvec  | CE_val (V_var z3)  ==  CE_concat [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e \<rbrace> =  \<lbrace> z' : B_bitvec  | CE_val (V_var z')  ==  CE_concat [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e \<rbrace>"
    using  type_e_eq infer_e_concatI e.fresh ce.fresh obtain_fresh_z fresh_Pair by metis

  have "\<Theta> ; \<Phi> ;  \<B> ; \<Gamma>' ; \<Delta>  \<turnstile> AE_concat v1 v2 \<Rightarrow> \<lbrace> z' : B_bitvec  | CE_val (V_var z')  ==  CE_concat [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e  \<rbrace>" proof
    show \<open> \<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wf_weakening infer_e_concatI by auto
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wf_weakening infer_e_concatI by auto
    show "\<Theta> ;  \<B> ; \<Gamma>' \<turnstile> v1 \<Rightarrow> \<lbrace> z1 : B_bitvec  |  c1 \<rbrace>" using infer_v_g_weakening infer_e_concatI    by metis
    show "\<Theta> ;  \<B> ; \<Gamma>' \<turnstile> v2 \<Rightarrow> \<lbrace> z2 : B_bitvec  |  c2 \<rbrace>" using infer_v_g_weakening infer_e_concatI    by metis
    show "atom z' \<sharp> AE_concat v1 v2" using * e.supp by auto
    show "atom z' \<sharp> \<Gamma>'" using * by auto
  qed
  thus ?case using * ** by metis
next
  case (infer_e_splitI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 z3)
  show ?case proof
    show "\<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f \<Delta>" using infer_e_splitI wf_weakening by auto
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " using infer_e_splitI wf_weakening by auto
    show "\<Theta>; \<B>; \<Gamma>' \<turnstile> v1 \<Rightarrow> \<lbrace> z1 : B_bitvec  | c1 \<rbrace>" using infer_v_g_weakening infer_e_splitI by metis
    show "\<Theta>; \<B>; \<Gamma>'  \<turnstile> v2 \<Leftarrow> \<lbrace> z2 : B_int  | [ leq [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ z2 ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e 
                  AND  [ leq [ [ z2 ]\<^sup>v ]\<^sup>c\<^sup>e [| [ v1 ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e   \<rbrace>" 
      using check_v_g_weakening infer_e_splitI by metis
    show "atom z1 \<sharp> AE_split v1 v2" using infer_e_splitI by auto
    show "atom z1 \<sharp> \<Gamma>'" using infer_e_splitI by auto
    show "atom z2 \<sharp> AE_split v1 v2" using infer_e_splitI by auto
    show "atom z2 \<sharp> \<Gamma>'" using infer_e_splitI by auto
    show "atom z3 \<sharp> AE_split v1 v2" using infer_e_splitI by auto
    show "atom z3 \<sharp> \<Gamma>'" using infer_e_splitI by auto
  qed
qed

text \<open> Special cases proved explicitly, other cases at the end with method + \<close>

lemma infer_e_d_weakening:
  fixes e::e
  assumes "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> e \<Rightarrow> \<tau>" and "setD \<Delta> \<subseteq> setD \<Delta>'" and "wfD \<Theta>  \<B> \<Gamma> \<Delta>'" 
  shows   "\<Theta>; \<Phi> ;  \<B> ; \<Gamma> ; \<Delta>' \<turnstile> e \<Rightarrow> \<tau>"
  using assms by(nominal_induct \<tau> avoiding: \<Delta>' rule: infer_e.strong_induct,auto simp add:infer_e.intros)

lemma  wfG_x_fresh_in_v_simple:
  fixes x::x and v :: v
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>" and "atom x \<sharp> \<Gamma>" 
  shows "atom x \<sharp> v"
  using wfV_x_fresh infer_v_wf assms by metis

lemma check_s_g_weakening:
  fixes v::v and s::s and cs::branch_s and x::x and c::c and b::b and \<Gamma>'::\<Gamma> and \<Theta>::\<Theta> and css::branch_list
  shows  "check_s \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s  t \<Longrightarrow> toSet \<Gamma> \<subseteq> toSet \<Gamma>' \<Longrightarrow>  \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<Longrightarrow> check_s \<Theta> \<Phi> \<B> \<Gamma>' \<Delta>  s   t"  and 
    "check_branch_s \<Theta> \<Phi> \<B> \<Gamma> \<Delta>  tid cons const v cs t \<Longrightarrow>  toSet \<Gamma> \<subseteq> toSet \<Gamma>' \<Longrightarrow>  \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>'  \<Longrightarrow> check_branch_s \<Theta> \<Phi> \<B> \<Gamma>' \<Delta> tid cons const v cs t" and
    "check_branch_list \<Theta> \<Phi> \<B> \<Gamma> \<Delta>  tid dclist v css t \<Longrightarrow>  toSet \<Gamma> \<subseteq> toSet \<Gamma>' \<Longrightarrow>  \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>'  \<Longrightarrow> check_branch_list \<Theta> \<Phi> \<B> \<Gamma>' \<Delta> tid dclist v css t"
proof(nominal_induct t and t and t avoiding: \<Gamma>'   rule: check_s_check_branch_s_check_branch_list.strong_induct)
  case (check_valI \<Theta> \<B> \<Gamma> \<Delta>' \<Phi> v \<tau>' \<tau>)
  then show ?case using Typing.check_valI infer_v_g_weakening wf_weakening subtype_weakening  by metis
next
  case (check_letI x \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e \<tau> z s b c)
  hence xf:"atom x \<sharp> \<Gamma>'"  by metis
  show ?case proof
    show "atom x \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>', \<Delta>, e, \<tau>)" using check_letI using fresh_prod4 xf by metis
    show "\<Theta> ; \<Phi> ; \<B> ; \<Gamma>' ; \<Delta>  \<turnstile> e \<Rightarrow> \<lbrace> z : b  | c \<rbrace>" using infer_e_g_weakening check_letI by metis
    show "atom z \<sharp> (x, \<Theta>, \<Phi>, \<B>, \<Gamma>', \<Delta>, e, \<tau>, s)" 
      by(unfold fresh_prodN,auto simp add: check_letI fresh_prodN) 
    have "toSet ((x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>) \<subseteq> toSet ((x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>')" using check_letI toSet.simps 
      by (metis Un_commute Un_empty_right Un_insert_right insert_mono)
    moreover hence "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f ((x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>')" using check_letI wfG_cons_weakening check_s_wf by metis
    ultimately show "\<Theta> ; \<Phi> ; \<B> ; (x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>' ; \<Delta>  \<turnstile> s \<Leftarrow> \<tau>" using check_letI by metis
  qed
next
  case (check_let2I x \<Theta> \<Phi> \<B> G \<Delta> t s1 \<tau> s2)
  show ?case proof
    show "atom x \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>', \<Delta>, t, s1, \<tau>)" using check_let2I using fresh_prod4 by auto
    show "\<Theta> ; \<Phi> ; \<B> ; \<Gamma>' ; \<Delta>  \<turnstile> s1 \<Leftarrow> t" using check_let2I by metis
    have "toSet ((x, b_of t, c_of t x) #\<^sub>\<Gamma> G) \<subseteq> toSet ((x, b_of t, c_of t x ) #\<^sub>\<Gamma> \<Gamma>')" using check_let2I by auto
    moreover hence "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f ((x, b_of t, c_of t x) #\<^sub>\<Gamma> \<Gamma>')" using check_let2I wfG_cons_weakening check_s_wf by metis
    ultimately show "\<Theta> ; \<Phi> ; \<B> ; (x, b_of t, c_of t x) #\<^sub>\<Gamma> \<Gamma>' ; \<Delta>  \<turnstile> s2 \<Leftarrow> \<tau>" using check_let2I by metis
  qed
next
  case (check_branch_list_consI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist' v cs \<tau> css dclist)
  thus ?case using Typing.check_branch_list_consI by metis
next
  case (check_branch_list_finalI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist' v cs \<tau> dclist)
  thus ?case using Typing.check_branch_list_finalI by metis
next
  case (check_branch_s_branchI \<Theta> \<B> \<Gamma> \<Delta> \<tau> const x \<Phi> tid cons v  s)
  show ?case proof
    show "\<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f \<Delta> " using  wf_weakening2(6) check_branch_s_branchI by metis
    show "\<turnstile>\<^sub>w\<^sub>f \<Theta>" using check_branch_s_branchI by auto
    show "\<Theta>; \<B>; \<Gamma>'   \<turnstile>\<^sub>w\<^sub>f \<tau> "  using check_branch_s_branchI wfT_weakening \<open>wfG  \<Theta> \<B> \<Gamma>'\<close> by presburger

    show "\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f const " using check_branch_s_branchI by auto
    show "atom x \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>', \<Delta>, tid, cons, const, v, \<tau>)" using check_branch_s_branchI by auto
    have "toSet ((x, b_of const, CE_val v  ==  CE_val(V_cons tid cons (V_var x))   AND  c_of const x) #\<^sub>\<Gamma> \<Gamma>) \<subseteq> toSet ((x, b_of const, CE_val v  ==  CE_val (V_cons tid cons (V_var x)) AND  c_of const x) #\<^sub>\<Gamma> \<Gamma>')" 
      using check_branch_s_branchI by auto
    moreover hence "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f ((x, b_of const, CE_val v  ==  CE_val (V_cons tid cons (V_var x))   AND  c_of const x ) #\<^sub>\<Gamma> \<Gamma>')" 
      using check_branch_s_branchI wfG_cons_weakening check_s_wf by metis
    ultimately show "\<Theta> ; \<Phi> ; \<B> ; (x, b_of const, CE_val v  ==  CE_val (V_cons tid cons (V_var x))   AND  c_of const x ) #\<^sub>\<Gamma> \<Gamma>' ; \<Delta>  \<turnstile> s \<Leftarrow> \<tau>" 
      using check_branch_s_branchI  using fresh_dom_free by auto
  qed
next
  case (check_ifI z \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v s1 s2 \<tau>)
  show ?case proof
    show \<open>atom z \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>', \<Delta>, v, s1, s2, \<tau>)\<close> using fresh_prodN check_ifI by auto
    show \<open>\<Theta>; \<B>; \<Gamma>'  \<turnstile> v \<Leftarrow> \<lbrace> z : B_bool  | TRUE \<rbrace>\<close> using check_v_g_weakening check_ifI by auto
    show \<open> \<Theta> ; \<Phi> ; \<B> ; \<Gamma>' ; \<Delta>  \<turnstile> s1 \<Leftarrow> \<lbrace> z : b_of \<tau>  | CE_val v  ==  CE_val (V_lit L_true)   IMP  c_of \<tau> z  \<rbrace>\<close> using  check_ifI by auto
    show \<open> \<Theta> ; \<Phi> ; \<B> ; \<Gamma>' ; \<Delta>  \<turnstile> s2 \<Leftarrow> \<lbrace> z : b_of \<tau>  | CE_val v  ==  CE_val (V_lit L_false)   IMP  c_of \<tau> z  \<rbrace>\<close> using  check_ifI by auto
  qed
next 
  case (check_whileI \<Delta> G P s1 z s2 \<tau>')
  then show ?case using check_s_check_branch_s_check_branch_list.intros check_v_g_weakening subtype_weakening wf_weakening  
    by (meson infer_v_g_weakening)
next
  case (check_seqI \<Delta> G P s1 z s2 \<tau>)
  then show ?case using check_s_check_branch_s_check_branch_list.intros check_v_g_weakening subtype_weakening wf_weakening 
    by (meson infer_v_g_weakening)
next
  case (check_varI u \<Theta> \<Phi> \<B> \<Gamma> \<Delta> \<tau>' v \<tau> s)
  thus ?case  using check_v_g_weakening check_s_check_branch_s_check_branch_list.intros by auto
next
  case (check_assignI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> u \<tau> v z \<tau>')
  show ?case proof 
    show \<open>\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using check_assignI by auto
    show \<open>\<Theta>; \<B>;  \<Gamma>' \<turnstile>\<^sub>w\<^sub>f \<Delta>\<close> using check_assignI  wf_weakening by auto
    show \<open>(u, \<tau>) \<in> setD \<Delta>\<close> using check_assignI by auto
    show \<open>\<Theta>; \<B>; \<Gamma>'  \<turnstile> v \<Leftarrow> \<tau>\<close> using check_assignI  check_v_g_weakening by auto
    show \<open>\<Theta>; \<B>; \<Gamma>'  \<turnstile> \<lbrace> z : B_unit  | TRUE \<rbrace> \<lesssim> \<tau>'\<close> using  subtype_weakening check_assignI by auto
  qed
next
  case (check_caseI \<Delta> \<Gamma> \<Theta> dclist cs \<tau> tid v z)

  then show ?case using check_s_check_branch_s_check_branch_list.intros check_v_g_weakening subtype_weakening wf_weakening
    by (meson infer_v_g_weakening)
next
  case (check_assertI x \<Theta> \<Phi> \<B> \<Gamma> \<Delta> c \<tau> s)
  show ?case proof
    show \<open>atom x \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>', \<Delta>, c, \<tau>, s)\<close> using check_assertI by auto

    have " \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f  (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>" using check_assertI check_s_wf by metis
    hence *:" \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f  (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>'"   using wfG_cons_weakening check_assertI by metis
    moreover have "toSet ((x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>) \<subseteq> toSet ((x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>')" using check_assertI by auto
    thus  \<open> \<Theta> ; \<Phi> ; \<B> ; (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>' ; \<Delta>  \<turnstile> s \<Leftarrow> \<tau>\<close> using check_assertI(11) [OF _ *] by auto

    show \<open>\<Theta>; \<B>; \<Gamma>'  \<Turnstile> c \<close> using check_assertI valid_weakening by metis
    show \<open> \<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using check_assertI wf_weakening by metis
  qed
qed

lemma  wfG_xa_fresh_in_v:
  fixes c::c and \<Gamma>::\<Gamma> and G::\<Gamma> and v::v and xa::x
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>" and "G=( \<Gamma>'@ (x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>)" and "atom xa \<sharp> G" and "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f G"
  shows "atom xa \<sharp> v"
proof -
  have "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b_of \<tau>"  using infer_v_wf assms by metis
  hence "supp v \<subseteq> atom_dom \<Gamma>  \<union> supp \<B>" using wfV_supp by simp
  moreover have  "atom xa \<notin> atom_dom G"  
    using assms wfG_atoms_supp_eq[OF assms(4)] fresh_def by metis
  ultimately show ?thesis using fresh_def
    using assms infer_v_wf wfG_atoms_supp_eq
      fresh_GCons  fresh_append_g subsetCE
    by (metis wfG_x_fresh_in_v_simple)
qed

lemma fresh_z_subst_g:
  fixes G::\<Gamma>
  assumes "atom z' \<sharp> (x,v)" and \<open>atom z' \<sharp> G\<close>
  shows "atom z' \<sharp> G[x::=v]\<^sub>\<Gamma>\<^sub>v"
proof - 
  have "atom z' \<sharp> v" using assms fresh_prod2 by auto
  thus ?thesis  using fresh_subst_gv assms by metis
qed

lemma  wfG_xa_fresh_in_subst_v:
  fixes c::c and v::v and x::x  and \<Gamma>::\<Gamma> and G::\<Gamma> and xa::x
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>" and "G=( \<Gamma>'@ (x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>)" and "atom xa \<sharp> G" and "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f G"
  shows "atom xa \<sharp> (subst_gv G x v)"
proof -
  have "atom xa \<sharp> v" using wfG_xa_fresh_in_v assms by metis
  thus ?thesis using fresh_subst_gv assms by metis
qed

subsection \<open>Weakening Immutable Variable Context\<close>

declare check_s_check_branch_s_check_branch_list.intros[simp]
declare check_s_check_branch_s_check_branch_list.intros[intro]

lemma check_s_d_weakening:
  fixes s::s and v::v and cs::branch_s and css::branch_list
  shows  " \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> s \<Leftarrow> \<tau> \<Longrightarrow>  setD \<Delta> \<subseteq> setD \<Delta>' \<Longrightarrow>  wfD  \<Theta> \<B> \<Gamma> \<Delta>' \<Longrightarrow> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta>' \<turnstile> s \<Leftarrow> \<tau>" and 
    "check_branch_s \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid cons const v cs \<tau> \<Longrightarrow>  setD \<Delta> \<subseteq> setD \<Delta>' \<Longrightarrow>  wfD  \<Theta> \<B> \<Gamma> \<Delta>' \<Longrightarrow> check_branch_s \<Theta> \<Phi> \<B> \<Gamma> \<Delta>' tid cons const v cs \<tau>" and 
    "check_branch_list \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist v css \<tau> \<Longrightarrow>  setD \<Delta> \<subseteq> setD \<Delta>' \<Longrightarrow>  wfD  \<Theta> \<B> \<Gamma> \<Delta>' \<Longrightarrow> check_branch_list \<Theta> \<Phi> \<B> \<Gamma> \<Delta>' tid dclist v css \<tau>"
proof(nominal_induct \<tau> and \<tau> and \<tau> avoiding: \<Delta>'   arbitrary: v rule: check_s_check_branch_s_check_branch_list.strong_induct)
  case (check_valI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v \<tau>' \<tau>)
  then show ?case using check_s_check_branch_s_check_branch_list.intros by blast
next
  case (check_letI x \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e \<tau> z s b c)
  show ?case proof
    show "atom x \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>', e, \<tau>)"  using check_letI by auto
    show "atom z \<sharp> (x, \<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>', e, \<tau>, s)" using check_letI by auto
    show "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta>'  \<turnstile> e \<Rightarrow> \<lbrace> z : b  | c \<rbrace>"  using check_letI infer_e_d_weakening by auto
    have "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f (x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>" using check_letI check_s_wf by metis
    moreover have "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>'" using check_letI check_s_wf by metis
    ultimately have "\<Theta>; \<B>; (x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>'"  using wf_weakening2(6)  toSet.simps by fast
    thus  "\<Theta> ; \<Phi> ; \<B> ; (x, b, c[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma> ; \<Delta>'  \<turnstile> s \<Leftarrow> \<tau>"   using check_letI by simp
  qed
next
  case (check_branch_s_branchI \<Theta> \<B> \<Gamma> \<Delta> \<tau> const x \<Phi> tid cons v  s)
  moreover have "\<Theta> ;\<B> \<turnstile>\<^sub>w\<^sub>f (x, b_of const, CE_val v  ==  CE_val (V_cons tid cons (V_var x))   AND  c_of const x ) #\<^sub>\<Gamma> \<Gamma>" 
    using check_s_wf[OF check_branch_s_branchI(16) ] by metis
  moreover hence " \<Theta> ;\<B> ; (x, b_of const, CE_val v  ==  CE_val (V_cons tid cons (V_var x))   AND  c_of const x ) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>'" 
    using wf_weakening2(6) check_branch_s_branchI by fastforce
  ultimately show ?case 
    using  check_s_check_branch_s_check_branch_list.intros by simp
next
  case (check_branch_list_consI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist v cs \<tau> css)
  then show ?case using check_s_check_branch_s_check_branch_list.intros  by meson
next
  case (check_branch_list_finalI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist v cs \<tau>)
  then show ?case using check_s_check_branch_s_check_branch_list.intros  by meson
next
  case (check_ifI z \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v s1 s2 \<tau>)
  show ?case proof
    show \<open>atom z \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>', v, s1, s2, \<tau>)\<close> using fresh_prodN check_ifI by auto
    show \<open>\<Theta>; \<B>; \<Gamma>  \<turnstile> v \<Leftarrow> \<lbrace> z : B_bool  | TRUE \<rbrace>\<close> using  check_ifI by auto
    show \<open> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta>'  \<turnstile> s1 \<Leftarrow> \<lbrace> z : b_of \<tau>  | CE_val v  ==  CE_val (V_lit L_true)   IMP  c_of \<tau> z  \<rbrace>\<close> using  check_ifI by auto
    show \<open> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta>'  \<turnstile> s2 \<Leftarrow> \<lbrace> z : b_of \<tau>  | CE_val v  ==  CE_val (V_lit L_false)   IMP  c_of \<tau> z  \<rbrace>\<close> using  check_ifI by auto
  qed
next
  case (check_assertI x \<Theta> \<Phi> \<B> \<Gamma> \<Delta> c \<tau> s)
  show ?case proof
    show "atom x \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>', c, \<tau>,s)" using fresh_prodN check_assertI by auto
    show *:" \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>' " using check_assertI by auto
    hence  "\<Theta>; \<B>; (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>' " using wf_weakening2(6)[OF *, of " (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>"] check_assertI check_s_wf toSet.simps by auto
    thus  "\<Theta> ; \<Phi> ; \<B> ; (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma> ; \<Delta>'  \<turnstile> s \<Leftarrow> \<tau>" 
      using check_assertI(11)[OF \<open>setD \<Delta> \<subseteq> setD \<Delta>'\<close>] by simp
        (* wf_weakening2(6) check_s_wf check_assertI *)
    show "\<Theta>; \<B>; \<Gamma>  \<Turnstile> c " using fresh_prodN check_assertI by auto

  qed
next
  case (check_let2I x \<Theta> \<Phi> \<B> G \<Delta> t s1 \<tau> s2)
  show ?case proof
    show "atom x \<sharp> (\<Theta>, \<Phi>, \<B>, G, \<Delta>', t , s1, \<tau>)"  using check_let2I by auto

    show "\<Theta> ; \<Phi> ; \<B> ; G ; \<Delta>'  \<turnstile> s1 \<Leftarrow> t"  using check_let2I infer_e_d_weakening by auto
    have "\<Theta>; \<B>; (x, b_of t, c_of t x ) #\<^sub>\<Gamma> G \<turnstile>\<^sub>w\<^sub>f \<Delta>'"  using check_let2I wf_weakening2(6) check_s_wf by fastforce 
    thus  "\<Theta> ; \<Phi> ; \<B> ; (x, b_of t, c_of t x) #\<^sub>\<Gamma> G ; \<Delta>'  \<turnstile> s2 \<Leftarrow> \<tau>"   using check_let2I by simp
  qed
next
  case (check_varI u \<Theta> \<Phi> \<B> \<Gamma> \<Delta> \<tau>' v \<tau> s)
  show ?case proof
    show "atom u \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>', \<tau>', v, \<tau>)" using check_varI by auto
    show "\<Theta>; \<B>; \<Gamma>  \<turnstile> v \<Leftarrow> \<tau>'" using check_varI by auto
    have "setD ((u, \<tau>') #\<^sub>\<Delta>\<Delta>) \<subseteq> setD ((u, \<tau>') #\<^sub>\<Delta>\<Delta>')" using setD.simps check_varI by auto
    moreover have "u \<notin> fst ` setD \<Delta>'" using check_varI(1) setD.simps fresh_DCons   by (simp add: fresh_d_not_in)
    moreover hence "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f (u, \<tau>') #\<^sub>\<Delta>\<Delta>' " using wfD_cons  fresh_DCons setD.simps check_varI check_v_wf  by metis
    ultimately show   "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; (u, \<tau>') #\<^sub>\<Delta>\<Delta>'  \<turnstile> s \<Leftarrow> \<tau>" using check_varI by auto
  qed
next
  case (check_assignI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> u \<tau> v z \<tau>')
  moreover hence "(u, \<tau>) \<in> setD \<Delta>'" by auto
  ultimately show ?case using Typing.check_assignI by simp
next
  case (check_whileI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 z s2 \<tau>')
  then show ?case using check_s_check_branch_s_check_branch_list.intros  by meson
next
  case (check_seqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 z s2 \<tau>)
  then show ?case using check_s_check_branch_s_check_branch_list.intros  by meson
next
  case (check_caseI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist v cs \<tau> z)
  then show ?case using check_s_check_branch_s_check_branch_list.intros  by meson

qed

lemma valid_ce_eq:
  fixes v::v and ce2::ce
  assumes "ce1 = ce2[x::=v]\<^sub>c\<^sub>e\<^sub>v" and "wfV \<Theta>  \<B> GNil v b" and  "wfCE \<Theta>  \<B>  ((x, b, TRUE) #\<^sub>\<Gamma> GNil) ce2 b'" and "wfCE \<Theta>  \<B> GNil ce1 b'"
  shows \<open>\<Theta>; \<B>; (x, b, ([[x ]\<^sup>v]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e )) #\<^sub>\<Gamma> GNil  \<Turnstile> ce1  ==  ce2 \<close>
  unfolding valid.simps proof
  have wfg: "\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f  (x, b, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e ) #\<^sub>\<Gamma> GNil" 
    using wfG_cons1I wfG_nilI wfX_wfY assms wf_intros 
    by (meson fresh_GNil wfC_e_eq wfG_intros2)

  show wf: \<open>\<Theta>; \<B>; (x, b, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e ) #\<^sub>\<Gamma> GNil   \<turnstile>\<^sub>w\<^sub>f ce1  ==  ce2  \<close> 
    apply(rule wfC_eqI[where b=b'])
    using wfg toSet.simps assms wfCE_weakening apply simp

    using wfg assms wf_replace_inside1(8) assms 
    using wfC_trueI wf_trans(8)  by auto

  show \<open>\<forall>i. ((\<Theta> ; (x, b, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e ) #\<^sub>\<Gamma> GNil \<turnstile> i) \<and>  (i \<Turnstile> (x, b, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e ) #\<^sub>\<Gamma> GNil)  \<longrightarrow>
             (i \<Turnstile> (ce1  ==  ce2 )))\<close> proof(rule+,goal_cases)
    fix i
    assume as:"\<Theta> ; (x, b, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e ) #\<^sub>\<Gamma> GNil \<turnstile> i \<and>  i \<Turnstile> (x, b, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e ) #\<^sub>\<Gamma> GNil"
    have 1:"wfV \<Theta>  \<B> ((x, b, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e ) #\<^sub>\<Gamma> GNil) v b" 
      using wf_weakening assms append_g.simps toSet.simps wf wfX_wfY 
      by (metis empty_subsetI)
    hence "\<exists>s. i \<lbrakk> v \<rbrakk> ~ s"  using eval_v_exist[OF _ 1] as by auto
    then obtain s where iv:"i\<lbrakk> v \<rbrakk> ~ s" ..

    hence ix:"i x = Some s" proof -
      have "i \<Turnstile> [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e" using is_satis_g.simps as by auto
      hence "i \<lbrakk> [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e \<rbrakk> ~ True" using is_satis.simps by auto
      hence "i \<lbrakk>  [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ s"  using  
          iv eval_e_elims
        by (metis eval_c_elims(7) eval_e_uniqueness eval_e_valI) 
      thus ?thesis using eval_v_elims(2) eval_e_elims(1) by metis
    qed

    have 1:"wfCE \<Theta>  \<B> ((x, b, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e ) #\<^sub>\<Gamma> GNil) ce1 b'" 
      using wfCE_weakening assms append_g.simps toSet.simps wf wfX_wfY 
      by (metis empty_subsetI)
    hence "\<exists>s1. i \<lbrakk> ce1 \<rbrakk> ~ s1"  using eval_e_exist assms as by auto
    then obtain s1 where s1: "i\<lbrakk>ce1\<rbrakk> ~ s1" ..

    moreover have "i\<lbrakk> ce2 \<rbrakk> ~ s1" proof -
      have "i\<lbrakk> ce2[x::=v]\<^sub>c\<^sub>e\<^sub>v \<rbrakk> ~ s1" using assms s1 by auto
      moreover have "ce1 = ce2[x::=v]\<^sub>c\<^sub>e\<^sub>v" using subst_v_ce_def assms subst_v_simple_commute by auto
      ultimately have "i(x \<mapsto> s) \<lbrakk> ce2 \<rbrakk> ~ s1" 
        using ix subst_e_eval_v[of i ce1 s1 "ce2[z::=[ x ]\<^sup>v]\<^sub>v" x v s] iv s1 by auto
      moreover have "i(x \<mapsto> s) = i" using ix by auto
      ultimately show ?thesis by auto
    qed
    ultimately show "i \<lbrakk> ce1  ==  ce2 \<rbrakk> ~ True " using eval_c_eqI by metis
  qed
qed


lemma check_v_top:
  fixes v::v
  assumes  "\<Theta>; \<B>; GNil  \<turnstile> v \<Leftarrow> \<tau>" and "ce1 = ce2[z::=v]\<^sub>c\<^sub>e\<^sub>v" and  "\<Theta>; \<B>; GNil  \<turnstile>\<^sub>w\<^sub>f  \<lbrace> z : b_of \<tau>  | ce1 == ce2  \<rbrace>"    
    and "supp ce1 \<subseteq> supp  \<B>"
  shows "\<Theta>; \<B>; GNil  \<turnstile> v \<Leftarrow> \<lbrace> z : b_of \<tau>  | ce1 == ce2  \<rbrace>"      
proof -
  obtain t where t: "\<Theta>; \<B>; GNil  \<turnstile> v \<Rightarrow> t \<and> \<Theta>; \<B>; GNil  \<turnstile> t \<lesssim> \<tau>" 
    using assms check_v_elims by metis

  then obtain z' and b' where *:"t = \<lbrace> z' : b'  | [ [ z' ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e  \<rbrace> \<and> atom z' \<sharp> v \<and> atom z' \<sharp> (\<Theta>, \<B>,GNil)"
    using assms  infer_v_form by metis
  have beq: "b_of t = b_of \<tau>" using subtype_eq_base2 b_of.simps t by auto 
  obtain x::x where xf: \<open>atom x \<sharp> (\<Theta>, \<B>, GNil, z', [ [ z' ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e , z, ce1  ==  ce2 )\<close> 
    using obtain_fresh by metis

  have "\<Theta>; \<B>; (x, b_of \<tau>, TRUE) #\<^sub>\<Gamma> GNil   \<turnstile>\<^sub>w\<^sub>f (ce1[z::=[ x ]\<^sup>v]\<^sub>v  ==  ce2[z::=[ x ]\<^sup>v]\<^sub>v )"
    using wfT_wfC2[OF assms(3), of x] subst_cv.simps(6) subst_v_c_def subst_v_ce_def fresh_GNil by simp

  then obtain b2 where b2: "\<Theta>; \<B>; (x, b_of t, TRUE) #\<^sub>\<Gamma> GNil \<turnstile>\<^sub>w\<^sub>f ce1[z::=[ x ]\<^sup>v]\<^sub>v : b2 \<and> 
            \<Theta>; \<B>; (x, b_of t, TRUE) #\<^sub>\<Gamma> GNil \<turnstile>\<^sub>w\<^sub>f ce2[z::=[ x ]\<^sup>v]\<^sub>v : b2" using wfC_elims(3)
    beq by metis

  from xf have "\<Theta>; \<B>; GNil  \<turnstile> \<lbrace> z' : b_of t  | [ [ z' ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e  \<rbrace> \<lesssim>  \<lbrace> z : b_of t  | ce1 == ce2  \<rbrace>" 
  proof  
    show \<open> \<Theta>; \<B>; GNil   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z' : b_of t  | [ [ z' ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e  \<rbrace> \<close> using b_of.simps assms infer_v_wf t * by auto
    show \<open> \<Theta>; \<B>; GNil   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b_of t  | ce1  ==  ce2  \<rbrace> \<close> using beq assms by auto
    have \<open>\<Theta>; \<B>; (x, b_of t, ([ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e )) #\<^sub>\<Gamma> GNil  \<Turnstile> (ce1[z::=[ x ]\<^sup>v]\<^sub>v  ==  ce2[z::=[ x ]\<^sup>v]\<^sub>v ) \<close>  
    proof(rule valid_ce_eq)
      show \<open>ce1[z::=[ x ]\<^sup>v]\<^sub>v = ce2[z::=[ x ]\<^sup>v]\<^sub>v[x::=v]\<^sub>c\<^sub>e\<^sub>v\<close> proof -
        have "atom z \<sharp> ce1" using assms fresh_def x_not_in_b_set by fast 
        hence "ce1[z::=[ x ]\<^sup>v]\<^sub>v = ce1" 
          using forget_subst_v by auto
        also have "... = ce2[z::=v]\<^sub>c\<^sub>e\<^sub>v" using assms by auto
        also have "... = ce2[z::=[ x ]\<^sup>v]\<^sub>v[x::=v]\<^sub>c\<^sub>e\<^sub>v" proof -
          have "atom x \<sharp> ce2" using  xf fresh_prodN c.fresh by metis
          thus ?thesis using subst_v_simple_commute subst_v_ce_def by simp
        qed
        finally show ?thesis by auto
      qed
      show \<open> \<Theta>; \<B>; GNil \<turnstile>\<^sub>w\<^sub>f v : b_of t \<close> using infer_v_wf t by simp
      show  \<open>  \<Theta>; \<B>; (x, b_of t, TRUE) #\<^sub>\<Gamma> GNil \<turnstile>\<^sub>w\<^sub>f ce2[z::=[ x ]\<^sup>v]\<^sub>v : b2 \<close>  using b2 by auto

      have " \<Theta>; \<B>; (x, b_of t, TRUE) #\<^sub>\<Gamma> GNil \<turnstile>\<^sub>w\<^sub>f ce1[z::=[ x ]\<^sup>v]\<^sub>v : b2" using b2 by auto
      moreover have "atom x \<sharp> ce1[z::=[ x ]\<^sup>v]\<^sub>v" 
        using fresh_subst_v_if assms fresh_def 
        using \<open>\<Theta>; \<B>; GNil \<turnstile>\<^sub>w\<^sub>f v : b_of t\<close> \<open>ce1[z::=[ x ]\<^sup>v]\<^sub>v = ce2[z::=[ x ]\<^sup>v]\<^sub>v[x::=v]\<^sub>c\<^sub>e\<^sub>v\<close> 
          fresh_GNil subst_v_ce_def wfV_x_fresh by auto
      ultimately show  \<open>  \<Theta>; \<B>; GNil \<turnstile>\<^sub>w\<^sub>f ce1[z::=[ x ]\<^sup>v]\<^sub>v : b2 \<close> using
          wf_restrict(8) by force
    qed
    moreover have v: "v[z'::=[ x ]\<^sup>v]\<^sub>v\<^sub>v  = v" 
      using forget_subst assms infer_v_wf wfV_supp x_not_in_b_set 
      by (simp add: "local.*")
    ultimately show "\<Theta>; \<B>; (x, b_of t, ([ [ z' ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ v ]\<^sup>c\<^sup>e )[z'::=[ x ]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma> GNil  \<Turnstile> (ce1  ==  ce2 )[z::=[ x ]\<^sup>v]\<^sub>v" 
      unfolding subst_cv.simps subst_v_c_def subst_cev.simps subst_vv.simps
      using subst_v_ce_def by simp
  qed
  thus ?thesis using b_of.simps assms * check_v_subtypeI t b_of.simps subtype_eq_base2 by metis
qed

end

