(*<*)
theory WellformedL
  imports Wellformed "SyntaxL"
begin                                                                                                                                                                                   
(*>*)

chapter \<open>Wellformedness Lemmas\<close>

section \<open>Prelude\<close>

lemma b_of_subst_bb_commute:
   "(b_of (\<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)) =  (b_of \<tau>)[bv::=b]\<^sub>b\<^sub>b"
proof -
  obtain z' and b' and c' where "\<tau> = \<lbrace> z' : b' | c' \<rbrace> " using obtain_fresh_z by metis
  moreover hence "(b_of (\<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)) = b_of \<lbrace> z' : b'[bv::=b]\<^sub>b\<^sub>b | c' \<rbrace>" using subst_tb.simps by simp
  ultimately show ?thesis using subst_tv.simps subst_tb.simps by simp
qed

lemmas wf_intros = wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.intros wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.intros

lemmas freshers = fresh_prodN b.fresh c.fresh v.fresh ce.fresh fresh_GCons fresh_GNil fresh_at_base 

section \<open>Strong Elimination\<close>

text \<open>Inversion/elimination for well-formed polymorphic constructors \<close>
lemma wf_strong_elim:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" 
           and \<Delta>::\<Delta> and b::b and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def and s::s and tm::"'a::fs" 
          and cs::branch_s and css::branch_list and \<Theta>::\<Theta>
   shows  "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f (V_consp tyid dc b v) : b'' \<Longrightarrow> (\<exists> bv dclist x b' c. b'' = B_app tyid b \<and>
             AF_typedef_poly tyid bv dclist \<in> set \<Theta> \<and>
            (dc, \<lbrace> x : b'  | c \<rbrace>) \<in> set dclist \<and>
               \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b  \<and> atom bv \<sharp> (\<Theta>, \<B>, \<Gamma>, b, v) \<and>  \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b'[bv::=b]\<^sub>b\<^sub>b \<and> atom bv \<sharp> tm)" and           
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f  c           \<Longrightarrow> True" and
         "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>                \<Longrightarrow> True" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<tau>            \<Longrightarrow> True" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ts \<Longrightarrow> True" and 
         "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow>True" and       
         "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b \<Longrightarrow> True " and      
         "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce : b'    \<Longrightarrow> True" and
         "\<Theta>  \<turnstile>\<^sub>w\<^sub>f td \<Longrightarrow>   True"
proof(nominal_induct
      "V_consp tyid dc b v" b'' and c and \<Gamma> and \<tau> and ts and \<Theta> and b and b' and td 
     avoiding: tm
  
rule:wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.strong_induct)
  case (wfV_conspI bv dclist \<Theta> x b' c \<B> \<Gamma>)
  then show ?case by force
qed(auto+)

section \<open>Context Extension\<close>

definition wfExt :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Gamma> \<Rightarrow> bool" (" _ ; _  \<turnstile>\<^sub>w\<^sub>f _ < _ " [50,50,50] 50)   where
  "wfExt T B G1 G2 = (wfG T B G2 \<and> wfG T B G1 \<and> toSet G1 \<subseteq> toSet G2)" 

section \<open>Context\<close>

lemma wfG_cons[ms_wb]:
  fixes \<Gamma>::\<Gamma>
  assumes "P; \<B>  \<turnstile>\<^sub>w\<^sub>f (z,b,c)  #\<^sub>\<Gamma>\<Gamma>"
  shows "P; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and> atom z \<sharp> \<Gamma> \<and> wfB P \<B> b" 
  using wfG_elims(2)[OF assms] by metis

lemma wfG_cons2[ms_wb]:
  fixes \<Gamma>::\<Gamma>
  assumes "P; \<B>  \<turnstile>\<^sub>w\<^sub>f zbc  #\<^sub>\<Gamma>\<Gamma>"
  shows "P; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>" 
proof -
  obtain z and b and c where zbc: "zbc=(z,b,c)" using prod_cases3 by blast
  hence  "P; \<B>  \<turnstile>\<^sub>w\<^sub>f (z,b,c)  #\<^sub>\<Gamma>\<Gamma>" using assms by auto
  thus ?thesis using zbc wfG_cons assms by simp
qed

lemma wf_g_unique: 
  fixes \<Gamma>::\<Gamma>
  assumes "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f  \<Gamma>" and "(x,b,c) \<in> toSet \<Gamma>" and "(x,b',c') \<in> toSet \<Gamma>"
  shows "b=b' \<and> c=c'"
using assms proof(induct \<Gamma> rule: \<Gamma>.induct)
  case GNil
  then show ?case by simp
next
  case (GCons a \<Gamma>)
  consider "(x,b,c)=a \<and> (x,b',c')=a" | "(x,b,c)=a \<and> (x,b',c')\<noteq>a" | "(x,b,c)\<noteq>a \<and> (x,b',c')=a" | "(x,b,c)\<noteq> a \<and> (x,b',c')\<noteq>a" by blast
  then show ?case proof(cases)
    case 1
    then show ?thesis  by auto
  next
    case 2
    hence "atom x \<sharp> \<Gamma>"  using wfG_elims(2) GCons by blast
    moreover have "(x,b',c') \<in> toSet \<Gamma>" using GCons 2 by force
    ultimately show ?thesis    using forget_subst_gv fresh_GCons fresh_GNil fresh_gamma_elem \<Gamma>.distinct subst_gv.simps 2 GCons by metis
  next
    case 3
    hence "atom x \<sharp> \<Gamma>"  using wfG_elims(2) GCons by blast
    moreover have "(x,b,c) \<in> toSet \<Gamma>" using GCons 3 by force
    ultimately show ?thesis
           using forget_subst_gv fresh_GCons fresh_GNil fresh_gamma_elem \<Gamma>.distinct subst_gv.simps 3 GCons by metis
  next
    case 4
    then obtain x'' and b'' and c''::c where xbc: "a=(x'',b'',c'')" 
      using prod_cases3 by blast
    hence "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f ((x'',b'',c'')  #\<^sub>\<Gamma>\<Gamma>)" using GCons wfG_elims by blast
    hence "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and> (x, b, c) \<in> toSet \<Gamma> \<and> (x, b', c') \<in> toSet \<Gamma>"  using  GCons wfG_elims 4 xbc
          prod_cases3 set_GConsD   using forget_subst_gv fresh_GCons fresh_GNil fresh_gamma_elem \<Gamma>.distinct subst_gv.simps 4 GCons by meson
    thus ?thesis using GCons by auto    
  qed
qed

lemma lookup_if1:
  fixes \<Gamma>::\<Gamma>
  assumes "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>" and  "Some (b,c) = lookup \<Gamma> x"
  shows "(x,b,c) \<in> toSet \<Gamma> \<and> (\<forall>b' c'. (x,b',c') \<in> toSet \<Gamma> \<longrightarrow> b'=b \<and> c'=c)"
using assms proof(induct \<Gamma> rule: \<Gamma>.induct)
  case GNil
  then show ?case by auto
next
  case (GCons xbc \<Gamma>)
  then obtain x' and b' and c'::c where xbc: "xbc=(x',b',c')" 
    using prod_cases3 by blast
  then show ?case using wf_g_unique GCons lookup_in_g xbc
     lookup.simps set_GConsD wfG.cases 
     insertE insert_is_Un toSet.simps wfG_elims by metis
qed

lemma lookup_if2:
  assumes "wfG P \<B> \<Gamma>" and   "(x,b,c) \<in> toSet \<Gamma> \<and> (\<forall>b' c'. (x,b',c') \<in> toSet \<Gamma> \<longrightarrow> b'=b \<and> c'=c)"
  shows "Some (b,c) = lookup \<Gamma> x" 
using assms proof(induct \<Gamma> rule: \<Gamma>.induct)
  case GNil
  then show ?case by auto
next
  case (GCons xbc \<Gamma>)
  then obtain x' and b' and c'::c where xbc: "xbc=(x',b',c')" 
    using prod_cases3 by blast
  then show ?case proof(cases "x=x'")
    case True
    then show ?thesis using lookup.simps GCons xbc by simp
  next
    case False
    then show ?thesis using lookup.simps GCons xbc toSet.simps Un_iff set_GConsD wfG_cons2 
      by (metis (full_types) Un_iff set_GConsD toSet.simps(2) wfG_cons2)
  qed
qed
    
lemma lookup_iff:
  fixes \<Theta>::\<Theta> and \<Gamma>::\<Gamma>
  assumes "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>"
  shows "Some (b,c) = lookup \<Gamma> x \<longleftrightarrow> (x,b,c) \<in> toSet \<Gamma> \<and> (\<forall>b' c'. (x,b',c') \<in> toSet \<Gamma> \<longrightarrow> b'=b \<and> c'=c)"
  using assms lookup_if1 lookup_if2 by meson

lemma wfG_lookup_wf:
  fixes \<Theta>::\<Theta> and \<Gamma>::\<Gamma> and b::b and \<B>::\<B>
  assumes "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>" and "Some (b,c) = lookup \<Gamma> x"
  shows "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b"
using assms proof(induct \<Gamma> rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x' b' c' \<Gamma>')
  then show ?case proof(cases "x=x'")
    case True
    then show ?thesis using lookup.simps wfG_elims(2) GCons by fastforce 
  next
    case False
    then show ?thesis using lookup.simps wfG_elims(2) GCons by fastforce 
  qed
qed    

lemma wfG_unique:
  fixes \<Gamma>::\<Gamma>
  assumes "wfG B \<Theta> ((x, b, c)   #\<^sub>\<Gamma> \<Gamma>)" and "(x1,b1,c1) \<in> toSet ((x, b, c)   #\<^sub>\<Gamma> \<Gamma>)" and "x1=x"
  shows "b1 = b \<and> c1 = c"
proof - 
  have "(x, b, c) \<in> toSet ((x, b, c)   #\<^sub>\<Gamma> \<Gamma>)" by simp
  thus ?thesis using wf_g_unique assms by blast
qed

lemma wfG_unique_full:
  fixes \<Gamma>::\<Gamma>
  assumes "wfG \<Theta> B (\<Gamma>'@(x, b, c)   #\<^sub>\<Gamma> \<Gamma>)" and "(x1,b1,c1) \<in> toSet (\<Gamma>'@(x, b, c)   #\<^sub>\<Gamma> \<Gamma>)" and "x1=x"
  shows "b1 = b \<and> c1 = c"
proof - 
  have "(x, b, c) \<in> toSet (\<Gamma>'@(x, b, c)   #\<^sub>\<Gamma> \<Gamma>)" by simp
  thus ?thesis using wf_g_unique assms by blast
qed

section \<open>Converting between wb forms\<close>

text \<open> We cannot prove wfB properties here for expressions and statements as need some more facts about @{term \<Phi>}
   context which we can prove without this lemma. Trying to cram everything into a single large
   mutually recursive lemma is not a good idea \<close>

lemma wfX_wfY1:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and b::b and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def and cs::branch_s
           and css::branch_list
  shows  wfV_wf: "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b \<Longrightarrow>  \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and> \<turnstile>\<^sub>w\<^sub>f \<Theta>  " and              
         wfC_wf: "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and> \<turnstile>\<^sub>w\<^sub>f \<Theta> " and
         wfG_wf :"\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<Longrightarrow>  \<turnstile>\<^sub>w\<^sub>f \<Theta>"  and
         wfT_wf: "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau> \<Longrightarrow>  \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and>  \<turnstile>\<^sub>w\<^sub>f \<Theta> \<and> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b_of \<tau>" and
         wfTs_wf:"\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ts \<Longrightarrow>  \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and>  \<turnstile>\<^sub>w\<^sub>f \<Theta>" and 
         "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow> True" and       
         wfB_wf: "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b \<Longrightarrow>   \<turnstile>\<^sub>w\<^sub>f \<Theta>" and      
         wfCE_wf: "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce : b \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and>  \<turnstile>\<^sub>w\<^sub>f \<Theta> "  and
         wfTD_wf: "\<Theta> \<turnstile>\<^sub>w\<^sub>f td \<Longrightarrow>  \<turnstile>\<^sub>w\<^sub>f \<Theta>"
proof(induct    rule:wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.inducts)

  case (wfV_varI \<Theta> \<B> \<Gamma> b c x)
  hence "(x,b,c) \<in> toSet \<Gamma>" using lookup_iff lookup_in_g by presburger
  hence "b \<in> fst`snd`toSet \<Gamma>" by force
  hence "wfB \<Theta> \<B> b" using wfV_varI using wfG_lookup_wf by auto
  then show ?case using wfV_varI wfV_elims wf_intros by metis
next
  case (wfV_litI \<Theta> \<B> \<Gamma> l)
  moreover have "wfTh \<Theta>" using wfV_litI by metis
  ultimately  show ?case using   wf_intros base_for_lit.simps l.exhaust by metis
next
  case (wfV_pairI \<Theta> \<B> \<Gamma> v1 b1 v2 b2)
  then show ?case using wfB_pairI by simp
next
  case (wfV_consI s dclist \<Theta> dc x b c \<B> \<Gamma> v)
  then show ?case using   wf_intros  by metis
next
  case (wfTI z \<Gamma> \<Theta> \<B> b c)
  then show ?case using wf_intros b_of.simps wfG_cons2 by metis
qed(auto)

lemma wfX_wfY2:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and b::b and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def and cs::branch_s
           and css::branch_list
  shows 
         wfE_wf: "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<and>  \<turnstile>\<^sub>w\<^sub>f \<Theta> \<and> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>  " and
         wfS_wf: "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<and>  \<turnstile>\<^sub>w\<^sub>f \<Theta> \<and> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>   " and
         "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f cs : b \<Longrightarrow>  \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<and>  \<turnstile>\<^sub>w\<^sub>f \<Theta> \<and> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " and
         "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b \<Longrightarrow>  \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<and>  \<turnstile>\<^sub>w\<^sub>f \<Theta> \<and> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " and       
         wfPhi_wf: "\<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) \<Longrightarrow>  \<turnstile>\<^sub>w\<^sub>f \<Theta>" and
         wfD_wf:   "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<and>  \<turnstile>\<^sub>w\<^sub>f \<Theta> " and       
         wfFTQ_wf: "\<Theta> ; \<Phi>   \<turnstile>\<^sub>w\<^sub>f ftq \<Longrightarrow> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>  \<and> \<turnstile>\<^sub>w\<^sub>f \<Theta>" and
         wfFT_wf:  "\<Theta> ; \<Phi>  ; \<B> \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<and>  \<turnstile>\<^sub>w\<^sub>f \<Theta>"           
proof(induct    rule:wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.inducts)
  case (wfS_varI \<Theta> \<B> \<Gamma> \<tau> v u \<Delta> \<Phi> s b)
  then show ?case using wfD_elims by auto
next
  case (wfS_assignI u \<tau> \<Delta> \<Theta> \<B> \<Gamma> \<Phi> v)
  then show ?case using wf_intros by metis
next
  case (wfD_emptyI \<Theta> \<B> \<Gamma>)
  then show ?case using wfX_wfY1 by auto
next
  case (wfS_assertI \<Theta> \<Phi> \<B> x c \<Gamma> \<Delta> s b)
  then have "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>" using wfX_wfY1 by auto
  moreover have "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>" using wfS_assertI by auto
  moreover have "\<turnstile>\<^sub>w\<^sub>f \<Theta>  \<and>  \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " using wfS_assertI by auto
  ultimately  show ?case by auto
qed(auto)

lemmas wfX_wfY=wfX_wfY1 wfX_wfY2

lemma setD_ConsD:
  "ut \<in> setD (ut' #\<^sub>\<Delta> D) = (ut = ut' \<or> ut \<in> setD D)"
proof(induct D rule: \<Delta>_induct)
  case DNil
  then show ?case by auto
next
  case (DCons u' t' x2)
  then show ?case using setD.simps by auto
qed

lemma wfD_wfT:
  fixes \<Delta>::\<Delta> and \<tau>::\<tau>
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>"
  shows "\<forall>(u,\<tau>) \<in> setD \<Delta>. \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>"
using assms proof(induct \<Delta> rule: \<Delta>_induct)
  case DNil
  then show ?case by auto
next
  case (DCons u' t' x2)
  then show ?case using wfD_elims DCons setD_ConsD
    by (metis case_prodI2 set_ConsD)
qed

lemma subst_b_lookup_d:
  assumes "u \<notin> fst ` setD \<Delta>"
  shows  "u \<notin> fst ` setD \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b" 
using assms proof(induct \<Delta> rule: \<Delta>_induct)
  case DNil
  then show ?case by auto
next
  case (DCons u' t'  x2) 
  hence "u\<noteq>u'" using DCons by simp
  show ?case using DCons subst_db.simps by simp
qed

lemma wfG_cons_splitI:
  fixes  \<Phi>::\<Phi> and \<Gamma>::\<Gamma>
  assumes "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>" and "atom x \<sharp> \<Gamma>" and "wfB \<Theta> \<B> b" and
      "c \<in> { TRUE, FALSE } \<longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> " and
      "c \<notin> { TRUE, FALSE } \<longrightarrow> \<Theta>  ;\<B> ;  (x,b,C_true)  #\<^sub>\<Gamma>\<Gamma> \<turnstile>\<^sub>w\<^sub>f c"
    shows "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f ((x,b,c)  #\<^sub>\<Gamma>\<Gamma>)"
  using wfG_cons1I wfG_cons2I assms by metis

lemma wfG_consI:
  fixes  \<Phi>::\<Phi> and \<Gamma>::\<Gamma> and c::c
  assumes "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>" and "atom x \<sharp> \<Gamma>" and "wfB \<Theta> \<B> b" and
   "\<Theta>  ; \<B> ; (x,b,C_true)  #\<^sub>\<Gamma>\<Gamma> \<turnstile>\<^sub>w\<^sub>f c"
  shows "\<Theta>  ; \<B> \<turnstile>\<^sub>w\<^sub>f ((x,b,c)  #\<^sub>\<Gamma>\<Gamma>)"
  using wfG_cons1I wfG_cons2I wfG_cons_splitI wfC_trueI assms by metis

lemma wfG_elim2:
  fixes c::c
  assumes  "wfG P \<B>  ((x,b,c)  #\<^sub>\<Gamma>\<Gamma>)" 
  shows "P; \<B> ; (x, b, TRUE)   #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c \<and> wfB P \<B> b" 
proof(cases "c \<in> {TRUE,FALSE}")
  case True
  have "P; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<and> atom x \<sharp> \<Gamma> \<and> wfB P \<B> b"  using wfG_elims(2)[OF assms] by auto
  hence "P; \<B> \<turnstile>\<^sub>w\<^sub>f ((x,b,TRUE)  #\<^sub>\<Gamma>\<Gamma>) \<and> wfB P \<B> b" using wfG_cons2I by auto
  thus ?thesis using wfC_trueI wfC_falseI True by auto
next
  case False
  then show ?thesis using wfG_elims(2)[OF assms] by auto
qed

lemma wfG_cons_wfC:
  fixes \<Gamma>::\<Gamma> and c::c
  assumes "\<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f (x, b, c)   #\<^sub>\<Gamma> \<Gamma>"
  shows "\<Theta> ; B ; ((x, b, TRUE)   #\<^sub>\<Gamma> \<Gamma>) \<turnstile>\<^sub>w\<^sub>f c"
  using assms wfG_elim2 by auto

lemma wfG_wfB:
  assumes "wfG P \<B> \<Gamma>" and "b \<in> fst`snd`toSet \<Gamma>"
  shows "wfB P \<B> b"
using assms proof(induct \<Gamma> rule:\<Gamma>_induct)
case GNil
  then show ?case by auto
next
  case (GCons x' b' c' \<Gamma>')
  show ?case proof(cases "b=b'")
    case True
    then show ?thesis using wfG_elim2  GCons by auto
  next
    case False
    hence "b \<in> fst`snd`toSet \<Gamma>'" using GCons by auto
    moreover have "wfG P \<B> \<Gamma>'" using wfG_cons GCons by auto
    ultimately show ?thesis using GCons by auto
  qed
qed

lemma wfG_cons_TRUE:
  fixes \<Gamma>::\<Gamma> and b::b
  assumes "P; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>" and "atom z \<sharp> \<Gamma>" and "P; \<B> \<turnstile>\<^sub>w\<^sub>f b"
  shows "P  ; \<B> \<turnstile>\<^sub>w\<^sub>f (z, b, TRUE)   #\<^sub>\<Gamma> \<Gamma>" 
  using wfG_cons2I wfG_wfB assms by simp

lemma wfG_cons_TRUE2:
  assumes "P; \<B> \<turnstile>\<^sub>w\<^sub>f (z,b,c)  #\<^sub>\<Gamma>\<Gamma>" and "atom z \<sharp> \<Gamma>"
  shows "P; \<B> \<turnstile>\<^sub>w\<^sub>f (z, b, TRUE)   #\<^sub>\<Gamma> \<Gamma>" 
  using  wfG_cons wfG_cons2I assms by simp

lemma wfG_suffix:
  fixes \<Gamma>::\<Gamma>
  assumes "wfG P \<B> (\<Gamma>'@\<Gamma>)"
  shows "wfG P \<B> \<Gamma>"
using assms proof(induct \<Gamma>' rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x b c \<Gamma>')
  hence " P; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>' @ \<Gamma>" using wfG_elims by auto
  then show ?case using GCons  wfG_elims by auto
qed

lemma wfV_wfCE:
  fixes v::v
  assumes "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b" 
  shows " \<Theta> ;  \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_val v : b"
proof -
  have  "\<Theta> \<turnstile>\<^sub>w\<^sub>f ([]::\<Phi>) "  using wfPhi_emptyI wfV_wf wfG_wf assms by metis
  moreover have "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f []\<^sub>\<Delta>" using wfD_emptyI wfV_wf wfG_wf assms by metis
  ultimately show ?thesis using wfCE_valI assms by auto
qed
  
section \<open>Support\<close>

lemma wf_supp1:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and b::b and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def and cs::branch_s and css ::branch_list

  shows  wfV_supp: "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b \<Longrightarrow>  supp v \<subseteq> atom_dom \<Gamma> \<union> supp \<B>" and       
         wfC_supp: "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c \<Longrightarrow> supp c \<subseteq> atom_dom \<Gamma> \<union> supp \<B>" and
         wfG_supp: "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<Longrightarrow>  atom_dom \<Gamma> \<subseteq> supp \<Gamma>" and
         wfT_supp: "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau> \<Longrightarrow>  supp \<tau> \<subseteq> atom_dom \<Gamma> \<union> supp \<B> " and
         wfTs_supp: "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ts \<Longrightarrow>  supp ts \<subseteq> atom_dom \<Gamma> \<union> supp \<B>" and 
         wfTh_supp: "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow> supp \<Theta> = {}" and       
         wfB_supp: "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b \<Longrightarrow> supp b \<subseteq> supp \<B>" and      
         wfCE_supp: "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce : b \<Longrightarrow> supp ce \<subseteq>  atom_dom \<Gamma> \<union> supp \<B>" and
         wfTD_supp: "\<Theta>  \<turnstile>\<^sub>w\<^sub>f td \<Longrightarrow> supp td \<subseteq>  {}" 
proof(induct    rule:wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.inducts)
  case (wfB_consI \<Theta> s dclist \<B>)
  then show ?case by(auto simp add: b.supp pure_supp)
next
  case (wfB_appI \<Theta> \<B> b s bv dclist)
  then show ?case by(auto simp add: b.supp pure_supp)
next
  case (wfV_varI \<Theta> \<B> \<Gamma> b c x)
  then show ?case using v.supp wfV_elims  
     empty_subsetI insert_subset supp_at_base 
     fresh_dom_free2 lookup_if1 
    by (metis sup.coboundedI1)
next
  case (wfV_litI \<Theta> \<B> \<Gamma> l)
  then show ?case using supp_l_empty v.supp by simp
next
  case (wfV_pairI \<Theta> \<B> \<Gamma> v1 b1 v2 b2)
   then show ?case using v.supp wfV_elims  by (metis Un_subset_iff)
next
  case (wfV_consI s dclist \<Theta> dc x b c \<B> \<Gamma> v)
  then show ?case using v.supp wfV_elims  
    Un_commute b.supp sup_bot.right_neutral supp_b_empty pure_supp by metis
next
  case (wfV_conspI typid bv dclist \<Theta> dc x b' c \<B> \<Gamma> v b)
  then show ?case  unfolding v.supp 
    using wfV_elims  
    Un_commute b.supp sup_bot.right_neutral supp_b_empty pure_supp 
    by (simp add: Un_commute pure_supp sup.coboundedI1)
next
  case (wfC_eqI \<Theta> \<B> \<Gamma> e1 b e2)
  hence "supp e1 \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using   c.supp wfC_elims 
    image_empty list.set(1) sup_bot.right_neutral  by (metis IntI UnE empty_iff subsetCE subsetI)
  moreover have "supp e2 \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using   c.supp wfC_elims 
    image_empty list.set(1) sup_bot.right_neutral IntI UnE empty_iff subsetCE subsetI
    by (metis wfC_eqI.hyps(4))
  ultimately show ?case using c.supp by auto
next
  case (wfG_cons1I c \<Theta> \<B> \<Gamma> x b)
  then show ?case using atom_dom.simps  dom_supp_g supp_GCons by metis
next
  case (wfG_cons2I c \<Theta> \<B> \<Gamma> x b)
  then show ?case using atom_dom.simps  dom_supp_g supp_GCons by metis
next
  case wfTh_emptyI
  then show ?case  by (simp add: supp_Nil)
next
  case (wfTh_consI \<Theta> lst)
  then show ?case using supp_Cons by fast
next
  case (wfTD_simpleI \<Theta> lst s)
  then have "supp (AF_typedef s lst ) = supp lst \<union> supp s" using type_def.supp  by auto
  then show ?case using wfTD_simpleI pure_supp 
    by (simp add: pure_supp supp_Cons supp_at_base)
next
  case (wfTD_poly \<Theta> bv lst s)
  then have "supp (AF_typedef_poly s bv lst ) = supp lst - { atom bv } \<union> supp s" using type_def.supp  by auto
  then show ?case using wfTD_poly pure_supp 
    by (simp add: pure_supp supp_Cons supp_at_base)
next
  case (wfTs_nil \<Theta> \<B> \<Gamma>)
  then show ?case using supp_Nil by auto
next
  case (wfTs_cons \<Theta> \<B> \<Gamma> \<tau> dc ts)
  then show ?case using supp_Cons supp_Pair pure_supp[of dc] by blast
next
  case (wfCE_valI \<Theta> \<B> \<Gamma> v b)
  thus ?case using ce.supp wfCE_elims by simp
next
  case (wfCE_plusI \<Theta> \<B> \<Gamma> v1 v2)
  hence "supp (CE_op Plus v1 v2) \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using ce.supp pure_supp 
    by (simp add: wfCE_plusI opp.supp)  
  then show ?case using  ce.supp wfCE_elims UnCI subsetCE subsetI x_not_in_b_set by auto
next
  case (wfCE_leqI \<Theta> \<B> \<Gamma> v1 v2)
  hence "supp (CE_op LEq v1 v2) \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using ce.supp pure_supp 
    by (simp add: wfCE_plusI opp.supp)  
  then show ?case using  ce.supp wfE_elims UnCI subsetCE subsetI x_not_in_b_set by auto
next
  case (wfCE_eqI \<Theta> \<B> \<Gamma> v1 b v2 )
  hence "supp (CE_op Eq v1 v2) \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using ce.supp pure_supp 
    by (simp add: wfCE_eqI opp.supp)  
  then show ?case using  ce.supp wfE_elims UnCI subsetCE subsetI x_not_in_b_set by auto
next
  case (wfCE_fstI \<Theta> \<B> \<Gamma> v1 b1 b2)
  thus ?case using ce.supp wfCE_elims by simp
next
  case (wfCE_sndI \<Theta> \<B> \<Gamma> v1 b1 b2)
 thus ?case using ce.supp wfCE_elims by simp
next
  case (wfCE_concatI \<Theta>  \<B> \<Gamma> v1 v2)
  thus ?case using ce.supp wfCE_elims by simp
next
  case (wfCE_lenI \<Theta>  \<B> \<Gamma>  v1)
  thus ?case using ce.supp wfCE_elims by simp
next
   case (wfTI z \<Theta> \<B> \<Gamma> b c)
  hence "supp c \<subseteq> supp z \<union> atom_dom \<Gamma> \<union> supp \<B>" using  supp_at_base dom_cons  by metis
  moreover have "supp b \<subseteq> supp \<B>"  using wfTI by auto
  ultimately have " supp  \<lbrace> z : b  | c \<rbrace> \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using \<tau>.supp supp_at_base by force
  thus ?case by auto
qed(auto)

lemma wf_supp2:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and 
        ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and b::b and ftq::fun_typ_q and 
        ft::fun_typ and ce::ce and td::type_def and cs::branch_s and css ::branch_list
  shows
         wfE_supp: "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b \<Longrightarrow> (supp e \<subseteq>  atom_dom \<Gamma> \<union> supp \<B> \<union> atom ` fst ` setD \<Delta>)" and (* \<and> ( \<Phi> = [] \<longrightarrow> supp e \<inter> supp \<B> = {})" and*)
         wfS_supp: "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<Longrightarrow> supp s \<subseteq> atom_dom \<Gamma> \<union> atom ` fst ` setD \<Delta> \<union> supp \<B>" and
         "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f cs : b \<Longrightarrow>  supp cs \<subseteq> atom_dom \<Gamma> \<union> atom ` fst ` setD \<Delta> \<union> supp \<B>" and
         "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b \<Longrightarrow>  supp css \<subseteq> atom_dom \<Gamma> \<union> atom ` fst ` setD \<Delta> \<union> supp \<B>" and      
         wfPhi_supp: "\<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) \<Longrightarrow>  supp \<Phi> = {}" and
         wfD_supp: "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<Longrightarrow> supp \<Delta> \<subseteq> atom`fst`(setD \<Delta>) \<union> atom_dom \<Gamma> \<union> supp \<B> " and      
         "\<Theta> ; \<Phi>   \<turnstile>\<^sub>w\<^sub>f ftq \<Longrightarrow> supp ftq = {}" and
         "\<Theta> ; \<Phi>  ; \<B> \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow> supp ft \<subseteq> supp \<B>"      
proof(induct    rule:wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.inducts)
  case (wfE_valI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v b)
  hence "supp (AE_val v) \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using e.supp wf_supp1 by simp
  then show ?case using  e.supp wfE_elims UnCI subsetCE subsetI x_not_in_b_set by metis
next
  case (wfE_plusI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  hence "supp (AE_op Plus v1 v2) \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  
    using  wfE_plusI opp.supp wf_supp1 e.supp pure_supp Un_least 
    by (metis sup_bot.left_neutral)

  then show ?case using  e.supp wfE_elims UnCI subsetCE subsetI x_not_in_b_set by metis
next
  case (wfE_leqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  hence "supp (AE_op LEq v1 v2) \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using e.supp pure_supp Un_least 
    sup_bot.left_neutral  using opp.supp wf_supp1 by auto
  then show ?case using  e.supp wfE_elims UnCI subsetCE subsetI x_not_in_b_set by metis
next
  case (wfE_eqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b v2)
  hence "supp (AE_op Eq v1 v2) \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using e.supp pure_supp Un_least 
    sup_bot.left_neutral  using opp.supp wf_supp1 by auto
  then show ?case using  e.supp wfE_elims UnCI subsetCE subsetI x_not_in_b_set by metis
next
  case (wfE_fstI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b1 b2)
 hence "supp (AE_fst  v1 ) \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using e.supp pure_supp   sup_bot.left_neutral  using opp.supp wf_supp1 by auto
  then show ?case using  e.supp wfE_elims UnCI subsetCE subsetI x_not_in_b_set by metis
next
  case (wfE_sndI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b1 b2)
 hence "supp (AE_snd  v1 ) \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using e.supp pure_supp     wfE_plusI opp.supp wf_supp1  by (metis Un_least)
  then show ?case using  e.supp wfE_elims UnCI subsetCE subsetI x_not_in_b_set by metis
next
  case (wfE_concatI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  hence "supp (AE_concat v1 v2) \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using e.supp pure_supp 
    wfE_plusI opp.supp wf_supp1  by (metis Un_least)
  then show ?case using  e.supp wfE_elims UnCI subsetCE subsetI x_not_in_b_set by metis
next
  case (wfE_splitI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  hence "supp (AE_split v1 v2) \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using e.supp pure_supp 
    wfE_plusI opp.supp wf_supp1  by (metis Un_least)
  then show ?case using  e.supp wfE_elims UnCI subsetCE subsetI x_not_in_b_set by metis
next
  case (wfE_lenI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1)
  hence "supp (AE_len v1 ) \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using e.supp pure_supp 
    using e.supp pure_supp   sup_bot.left_neutral  using opp.supp wf_supp1 by auto
  then show ?case using  e.supp wfE_elims UnCI subsetCE subsetI x_not_in_b_set by metis
next
  case (wfE_appI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> f x b c \<tau> s v)
  then obtain b where "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b" using wfE_elims by metis          
  hence  "supp v \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"  using wfE_appI wf_supp1 by metis
  hence "supp (AE_app f v) \<subseteq> atom_dom \<Gamma> \<union> supp \<B>" using e.supp pure_supp by fast
  then show ?case using  e.supp(2)  UnCI subsetCE subsetI wfE_appI  using b.supp(3) pure_supp x_not_in_b_set by metis
next
  case (wfE_appPI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> b' bv v \<tau> f xa ba ca s)
  then obtain b where "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : ( b[bv::=b']\<^sub>b)" using wfE_elims by metis          
  hence  "supp v \<subseteq> atom_dom \<Gamma> \<union> supp \<B> "  using wfE_appPI wf_supp1 by auto
  moreover have "supp b' \<subseteq> supp  \<B>" using wf_supp1(7) wfE_appPI by simp
  ultimately show ?case unfolding  e.supp using  wfE_appPI pure_supp by fast
next
  case (wfE_mvarI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> u \<tau>)
     then  obtain \<tau> where "(u,\<tau>) \<in> setD \<Delta>" using wfE_elims(10) by metis
  hence "atom u \<in> atom`fst`setD \<Delta>" by force
  hence "supp (AE_mvar u ) \<subseteq> atom`fst`setD \<Delta>" using e.supp
    by (simp add: supp_at_base)
  thus ?case using UnCI subsetCE subsetI e.supp wfE_mvarI supp_at_base subsetCE supp_at_base u_not_in_b_set 
    by (simp add: supp_at_base)
next
  case (wfS_valI \<Theta> \<Phi> \<B> \<Gamma> v b \<Delta>)
  then show ?case using wf_supp1 
    by (metis s_branch_s_branch_list.supp(1) sup.coboundedI2 sup_assoc sup_commute) 
next
  case (wfS_letI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e b' x s b)
  then show ?case  by auto
next
  case (wfS_let2I \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 \<tau> x s2 b)
  then show ?case unfolding  s_branch_s_branch_list.supp (3) using wf_supp1(4)[OF wfS_let2I(3)] by auto
next
  case (wfS_ifI \<Theta> \<B> \<Gamma> v \<Phi> \<Delta> s1 b s2)
  then show ?case  using wf_supp1(1)[OF wfS_ifI(1)]  by auto
next
  case (wfS_varI \<Theta> \<B> \<Gamma> \<tau> v u \<Delta> \<Phi> s b)
  then show ?case  using  wf_supp1(1)[OF wfS_varI(2)]  wf_supp1(4)[OF wfS_varI(1)]  by auto
next
next
  case (wfS_assignI u \<tau> \<Delta> \<Theta> \<B> \<Gamma> \<Phi> v)
  hence "supp u \<subseteq> atom ` fst ` setD \<Delta>" proof(induct \<Delta> rule:\<Delta>_induct)
    case DNil
    then show ?case by auto
  next
    case (DCons u' t' \<Delta>')
    show ?case proof(cases "u=u'")
      case True
      then show ?thesis using toSet.simps DCons supp_at_base by fastforce
    next
      case False
      then show ?thesis  using toSet.simps DCons supp_at_base wfS_assignI 
        by (metis empty_subsetI fstI image_eqI insert_subset)
    qed
  qed
  then show ?case using s_branch_s_branch_list.supp(8) wfS_assignI wf_supp1(1)[OF wfS_assignI(6)] by auto
next
  case (wfS_matchI \<Theta> \<B> \<Gamma> v tid dclist \<Delta> \<Phi> cs b)
  then show ?case using wf_supp1(1)[OF wfS_matchI(1)] by auto
next
 case (wfS_branchI \<Theta> \<Phi> \<B> x \<tau> \<Gamma> \<Delta> s b tid dc)
  moreover have "supp s \<subseteq> supp x \<union> atom_dom \<Gamma> \<union> atom ` fst ` setD \<Delta> \<union> supp \<B>" 
    using dom_cons supp_at_base wfS_branchI by auto
  moreover hence "supp s - set [atom x] \<subseteq> atom_dom \<Gamma> \<union> atom ` fst ` setD \<Delta> \<union> supp \<B>" using supp_at_base by force
  ultimately have
     "(supp s - set [atom x]) \<union> (supp dc ) \<subseteq> atom_dom \<Gamma> \<union> atom ` fst ` setD \<Delta> \<union> supp \<B>"
     by (simp add: pure_supp)
  thus ?case using s_branch_s_branch_list.supp(2) by auto
next
  case (wfD_emptyI \<Theta> \<B> \<Gamma>)
  then show ?case using supp_DNil by auto
next
  case (wfD_cons \<Theta> \<B> \<Gamma> \<Delta> \<tau> u)
  have "supp ((u, \<tau>)  #\<^sub>\<Delta> \<Delta>) = supp u \<union> supp \<tau> \<union> supp \<Delta>" using supp_DCons supp_Pair by metis
  also have "... \<subseteq>  supp u \<union> atom ` fst ` setD \<Delta> \<union> atom_dom \<Gamma> \<union> supp \<B>" 
    using wfD_cons wf_supp1(4)[OF wfD_cons(3)] by auto
  also have "... \<subseteq> atom ` fst ` setD ((u, \<tau>)  #\<^sub>\<Delta> \<Delta>) \<union> atom_dom \<Gamma> \<union> supp \<B>" using supp_at_base by auto
  finally show ?case by auto
next
  case (wfPhi_emptyI \<Theta>)
  then show ?case using supp_Nil by auto
next
  case (wfPhi_consI f \<Theta> \<Phi> ft)
  then show ?case using fun_def.supp
    by (simp add: pure_supp supp_Cons)
next
  case (wfFTI \<Theta> B' b s x c \<tau> \<Phi>)
  have " supp (AF_fun_typ x b c \<tau> s) = supp c \<union> (supp \<tau> \<union> supp s) - set [atom x] \<union> supp b" using fun_typ.supp by auto
  thus ?case using wfFTI wf_supp1 
  proof -
    have f1: "supp \<tau> \<subseteq> {atom x} \<union> atom_dom GNil \<union> supp B'"
      using dom_cons wfFTI.hyps wf_supp1(4) by blast (* 0.0 ms *)
    have "supp b \<subseteq> supp B'"
      using wfFTI.hyps(1) wf_supp1(7) by blast (* 0.0 ms *)
    then show ?thesis
      using f1 \<open>supp (AF_fun_typ x b c \<tau> s) = supp c \<union> (supp \<tau> \<union> supp s) - set [atom x] \<union> supp b\<close> 
             wfFTI.hyps(4) wfFTI.hyps by auto (* 234 ms *)
  qed 
next
  case (wfFTNone \<Theta> \<Phi> ft)
  then show ?case by (simp add: fun_typ_q.supp(2))
next
  case (wfFTSome \<Theta> \<Phi> bv ft)
  then show ?case using fun_typ_q.supp
    by (simp add: supp_at_base)
next
  case (wfS_assertI \<Theta> \<Phi> \<B> x c \<Gamma> \<Delta> s b)
  then have "supp c \<subseteq> atom_dom \<Gamma> \<union> atom ` fst ` setD \<Delta> \<union> supp \<B>" using wf_supp1 
    by (metis Un_assoc Un_commute le_supI2)
  moreover have "supp s  \<subseteq> atom_dom \<Gamma> \<union> atom ` fst ` setD \<Delta> \<union> supp \<B>" proof 
    fix z
    assume *:"z \<in> supp s"
    have **:"atom x \<notin> supp s" using wfS_assertI fresh_prodN fresh_def by metis
    have "z \<in> atom_dom ((x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>) \<union> atom ` fst ` setD \<Delta> \<union> supp \<B>" using wfS_assertI * by blast
    have "z \<in>  atom_dom ((x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>) \<Longrightarrow> z \<in> atom_dom \<Gamma>" using * ** by auto 
    thus  "z \<in> atom_dom \<Gamma> \<union> atom ` fst ` setD \<Delta> \<union> supp \<B>" using * ** 
      using \<open>z \<in> atom_dom ((x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>) \<union> atom ` fst ` setD \<Delta> \<union> supp \<B>\<close> by blast
  qed 
  ultimately show ?case by auto
qed(auto)

lemmas wf_supp = wf_supp1 wf_supp2

lemma wfV_supp_nil:
  fixes v::v
  assumes "P ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f v : b" 
  shows "supp v = {}"
  using wfV_supp[of P " {||}"  GNil v b] dom.simps toSet.simps
  using assms by auto

lemma wfT_TRUE_aux:
  assumes "wfG P \<B> \<Gamma>" and "atom z \<sharp> (P, \<B>, \<Gamma>)" and "wfB P \<B> b"
  shows "wfT P \<B> \<Gamma> (\<lbrace> z : b  | TRUE \<rbrace>)"  
proof (rule)
  show \<open> atom z \<sharp> (P, \<B>, \<Gamma>)\<close> using assms by auto
  show \<open> P; \<B> \<turnstile>\<^sub>w\<^sub>f b \<close> using assms by auto
  show \<open> P ;\<B> ;  (z, b, TRUE)   #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f TRUE \<close> using wfG_cons2I wfC_trueI assms by auto
qed

lemma wfT_TRUE:
  assumes "wfG P \<B> \<Gamma>" and "wfB P \<B> b"
  shows "wfT P \<B> \<Gamma> (\<lbrace> z : b  | TRUE \<rbrace>)" 
proof -
  obtain z'::x where *:"atom z' \<sharp> (P, \<B>, \<Gamma>)" using obtain_fresh by metis
  hence "\<lbrace> z : b  | TRUE \<rbrace> = \<lbrace> z' : b  | TRUE \<rbrace>" by auto
  thus ?thesis using wfT_TRUE_aux assms * by metis
qed

lemma phi_flip_eq:
  assumes "wfPhi T P"
  shows  "(x \<leftrightarrow> xa) \<bullet> P = P"
  using wfPhi_supp[OF assms] flip_fresh_fresh fresh_def by blast

lemma wfC_supp_cons:
  fixes c'::c and G::\<Gamma>
  assumes "P; \<B> ; (x', b' , TRUE)  #\<^sub>\<Gamma>G \<turnstile>\<^sub>w\<^sub>f c'" 
  shows "supp c' \<subseteq> atom_dom G \<union> supp x' \<union> supp \<B>" and "supp c' \<subseteq> supp G \<union> supp x' \<union> supp \<B>"
proof -
  show "supp c' \<subseteq> atom_dom G \<union> supp x' \<union> supp \<B>"
    using  wfC_supp[OF assms] dom_cons supp_at_base by blast
  moreover have "atom_dom G \<subseteq> supp G"
    by (meson assms wfC_wf wfG_cons wfG_supp)
  ultimately show "supp c' \<subseteq> supp G \<union> supp x' \<union> supp \<B>" using wfG_supp assms wfG_cons wfC_wf by fast
qed

lemma wfG_dom_supp:
  fixes x::x
  assumes "wfG P \<B> G"
  shows "atom x \<in> atom_dom G \<longleftrightarrow> atom x \<in> supp G"
using assms proof(induct G rule: \<Gamma>_induct)
  case GNil
  then show ?case using dom.simps  supp_of_atom_list
    using supp_GNil by auto
next
  case (GCons x' b' c' G)

  show ?case proof(cases "x' = x")
    case True
    then show ?thesis using dom.simps supp_of_atom_list supp_at_base 
      using supp_GCons by auto
  next
    case False
    have "(atom x \<in> atom_dom ((x', b', c')   #\<^sub>\<Gamma> G)) = (atom x \<in> atom_dom G)" using atom_dom.simps False by simp
    also have "... = (atom x \<in> supp  G)" using GCons wfG_elims by metis
    also have "... = (atom x \<in> (supp (x', b', c') \<union> supp G))" proof
      show "atom x \<in> supp G \<Longrightarrow> atom x \<in> supp (x', b', c') \<union> supp G" by auto
      assume "atom x \<in> supp (x', b', c') \<union> supp G"
      then consider "atom x \<in> supp (x', b', c')" | "atom x \<in> supp G" by auto
      then show "atom x \<in> supp G" proof(cases)
        case 1
        assume " atom x \<in> supp (x', b', c') "
        hence "atom x \<in>  supp c'" using supp_triple False supp_b_empty supp_at_base by force

        moreover have "P; \<B> ; (x', b' , TRUE)  #\<^sub>\<Gamma>G \<turnstile>\<^sub>w\<^sub>f c'" using wfG_elim2 GCons by simp
        moreover hence "supp c' \<subseteq> supp G \<union> supp x' \<union> supp \<B>" using wfC_supp_cons by auto
        ultimately have  "atom x \<in> supp G \<union> supp x' "   using x_not_in_b_set by auto
        then show ?thesis using False supp_at_base  by (simp add: supp_at_base)
      next
        case 2
        then show ?thesis by simp
      qed
    qed
    also have "... = (atom x \<in> supp ((x', b', c')   #\<^sub>\<Gamma> G))"  using supp_at_base False supp_GCons by simp
    finally show ?thesis by simp
  qed
qed

lemma wfG_atoms_supp_eq : 
  fixes x::x
  assumes "wfG P \<B> G"
  shows "atom x \<in> atom_dom G \<longleftrightarrow> atom x \<in> supp G"
  using wfG_dom_supp assms by auto

lemma beta_flip_eq:
  fixes x::x and xa::x and \<B>::\<B>
  shows  "(x \<leftrightarrow> xa) \<bullet> \<B> = \<B>"
proof - 
  have "atom x \<sharp> \<B> \<and> atom xa \<sharp> \<B>" using x_not_in_b_set fresh_def supp_set by metis
  thus ?thesis  by (simp add: flip_fresh_fresh fresh_def)
qed

lemma theta_flip_eq2:
  assumes "\<turnstile>\<^sub>w\<^sub>f \<Theta>"
  shows  " (z \<leftrightarrow> za ) \<bullet> \<Theta> = \<Theta>"
proof -
  have "supp \<Theta> = {}" using wfTh_supp assms by simp
  thus ?thesis 
      by (simp add: flip_fresh_fresh fresh_def)
  qed

lemma theta_flip_eq:
  assumes "wfTh \<Theta>"
  shows  "(x \<leftrightarrow> xa) \<bullet> \<Theta> = \<Theta>"
  using wfTh_supp flip_fresh_fresh fresh_def 
  by (simp add: assms theta_flip_eq2)

lemma wfT_wfC:
  fixes c::c 
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c \<rbrace>" and "atom z \<sharp> \<Gamma>"
  shows "\<Theta>; \<B>; (z,b,TRUE)  #\<^sub>\<Gamma>\<Gamma> \<turnstile>\<^sub>w\<^sub>f c"
proof -
  obtain za ba ca where *:"\<lbrace> z : b  | c \<rbrace> = \<lbrace> za : ba  | ca \<rbrace> \<and> atom za \<sharp> (\<Theta>,\<B>,\<Gamma>) \<and>  \<Theta>; \<B>; (za, ba, TRUE)   #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ca"
    using wfT_elims[OF assms(1)] by metis
  hence c1: "[[atom z]]lst. c = [[atom za]]lst. ca" using \<tau>.eq_iff by meson
  show ?thesis proof(cases "z=za")
    case True
    hence "ca = c" using  c1  by (simp add: Abs1_eq_iff(3))
    then show ?thesis using * True by simp
  next
    case False
    have " \<turnstile>\<^sub>w\<^sub>f \<Theta>" using wfT_wf wfG_wf assms by metis
    moreover have "atom za \<sharp> \<Gamma>" using * fresh_prodN by auto
    ultimately have  "\<Theta>; \<B>; (z \<leftrightarrow> za ) \<bullet> (za, ba, TRUE)   #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f (z \<leftrightarrow> za ) \<bullet> ca" 
      using wfC.eqvt theta_flip_eq2  beta_flip_eq * GCons_eqvt assms flip_fresh_fresh  by metis
    moreover have "atom z \<sharp> ca"     
    proof -
      have "supp ca \<subseteq> atom_dom \<Gamma> \<union> { atom za } \<union> supp \<B>" using  * wfC_supp atom_dom.simps toSet.simps by fastforce
      moreover have "atom z \<notin> atom_dom \<Gamma> " using assms fresh_def wfT_wf  wfG_dom_supp wfC_supp by metis
      moreover hence  "atom z \<notin> atom_dom \<Gamma> \<union> { atom za }" using False by simp
      moreover have "atom z \<notin> supp \<B>" using x_not_in_b_set by simp
      ultimately show ?thesis using fresh_def False by fast
    qed
    moreover hence  "(z \<leftrightarrow> za ) \<bullet> ca = c" using type_eq_subst_eq1(3)  * by metis 
    ultimately show  ?thesis using assms G_cons_flip_fresh * by auto
  qed
qed

lemma u_not_in_dom_g:
  fixes u::u
  shows  "atom u \<notin> atom_dom  G"
  using toSet.simps atom_dom.simps u_not_in_x_atoms by auto

lemma bv_not_in_dom_g:
  fixes bv::bv
  shows  "atom bv \<notin> atom_dom  G"
  using toSet.simps atom_dom.simps u_not_in_x_atoms by auto
  
text \<open>An important lemma that confirms that @{term \<Gamma>} does not rely on mutable variables\<close>
lemma u_not_in_g:
  fixes u::u
  assumes "wfG \<Theta> B G"
  shows  "atom u \<notin> supp G"
using assms proof(induct G rule: \<Gamma>_induct)
case GNil
  then show ?case using supp_GNil fresh_def 
    using fresh_set_empty by fastforce
next
  case (GCons x b c \<Gamma>')
   moreover hence "atom u \<notin> supp b"  using 
    wfB_supp wfC_supp u_not_in_x_atoms wfG_elims wfX_wfY by auto
   moreover hence "atom u \<notin> supp x"  using u_not_in_x_atoms supp_at_base by blast
   moreover hence "atom u \<notin> supp c" proof -
     have "\<Theta> ; B ; (x, b, TRUE)   #\<^sub>\<Gamma> \<Gamma>'   \<turnstile>\<^sub>w\<^sub>f c" using wfG_cons_wfC GCons by simp
     hence "supp c \<subseteq> atom_dom ((x, b, TRUE)   #\<^sub>\<Gamma> \<Gamma>') \<union> supp B" using wfC_supp by blast
     thus ?thesis using u_not_in_dom_g u_not_in_b_atoms 
       using u_not_in_b_set by auto
   qed
   ultimately have "atom u \<notin> supp (x,b,c)" using supp_Pair by simp
   thus  ?case using supp_GCons GCons wfG_elims by blast
qed

text \<open>An important lemma that confirms that types only depend on immutable variables\<close>
lemma u_not_in_t:
  fixes u::u
  assumes "wfT \<Theta> B G \<tau>"
  shows  "atom u \<notin> supp \<tau>"
proof -
  have "supp \<tau> \<subseteq> atom_dom G \<union> supp B" using  wfT_supp assms by auto
  thus ?thesis using u_not_in_dom_g u_not_in_b_set  by blast 
qed  

lemma wfT_supp_c:
  fixes \<B>::\<B> and z::x
  assumes "wfT P \<B> \<Gamma> (\<lbrace> z : b  | c \<rbrace>)" 
  shows "supp c - { atom z } \<subseteq> atom_dom \<Gamma> \<union> supp  \<B>"
  using wf_supp \<tau>.supp assms 
  by (metis Un_subset_iff empty_set list.simps(15)) 

lemma wfG_wfC[ms_wb]:
  assumes "wfG P \<B> ((x,b,c)  #\<^sub>\<Gamma>\<Gamma>)"
  shows "wfC P \<B> ((x,b,TRUE)  #\<^sub>\<Gamma>\<Gamma>) c"
using assms proof(cases "c \<in> {TRUE,FALSE}")
  case True
  have "atom x \<sharp> \<Gamma> \<and> wfG P \<B> \<Gamma> \<and> wfB P \<B> b" using wfG_cons assms by auto
  hence "wfG P \<B>  ((x,b,TRUE)  #\<^sub>\<Gamma>\<Gamma>)" using wfG_cons2I by auto
  then show ?thesis using wfC_trueI wfC_falseI True by auto
next
  case False
  then show ?thesis using wfG_elims assms by blast
qed

lemma wfT_wf_cons: 
  assumes "wfT P \<B> \<Gamma> \<lbrace> z : b  | c \<rbrace>" and "atom z \<sharp> \<Gamma>"
  shows "wfG P \<B> ((z,b,c)  #\<^sub>\<Gamma>\<Gamma>)"
using assms proof(cases "c \<in> { TRUE,FALSE }")
  case True
  then show ?thesis using wfT_wfC wfC_wf wfG_wfB  wfG_cons2I assms wfT_wf by fastforce
next
  case False
  then show ?thesis using wfT_wfC wfC_wf wfG_wfB  wfG_cons1I wfT_wf wfT_wfC assms by fastforce
qed

lemma wfV_b_fresh:
  fixes b::b and v::v and bv::bv 
  assumes  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v: b" and "bv |\<notin>| \<B>"
  shows "atom bv \<sharp> v"
using wfV_supp  bv_not_in_dom_g fresh_def assms bv_not_in_bset_supp by blast

lemma wfCE_b_fresh:
  fixes b::b and ce::ce and bv::bv 
  assumes  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce: b" and "bv |\<notin>| \<B>"
  shows "atom bv \<sharp> ce"
using bv_not_in_dom_g fresh_def assms bv_not_in_bset_supp wf_supp1(8) by fast
 
section \<open>Freshness\<close>

lemma wfG_fresh_x:
  fixes \<Gamma>::\<Gamma> and z::x
  assumes "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>" and "atom z \<sharp> \<Gamma>" 
  shows "atom z \<sharp> (\<Theta>,\<B>, \<Gamma>)"
unfolding fresh_prodN apply(intro conjI)
  using wf_supp1 wfX_wfY assms fresh_def x_not_in_b_set by(metis empty_iff)+

lemma wfG_wfT:
  assumes "wfG P \<B> ((x, b, c[z::=V_var x]\<^sub>c\<^sub>v)   #\<^sub>\<Gamma> G)" and "atom x \<sharp> c"
  shows "P; \<B> ; G \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c \<rbrace>" 
proof - 
  have " P; \<B> ; (x, b, TRUE)   #\<^sub>\<Gamma> G  \<turnstile>\<^sub>w\<^sub>f c[z::=V_var x]\<^sub>c\<^sub>v \<and> wfB P \<B> b" using  assms 
    using wfG_elim2 by auto
  moreover have "atom x \<sharp>  (P ,\<B>,G)" using wfG_elims assms wfG_fresh_x by metis
  ultimately have  "wfT P \<B> G \<lbrace> x : b | c[z::=V_var x]\<^sub>c\<^sub>v \<rbrace>" using wfTI assms by metis
  moreover have "\<lbrace> x : b | c[z::=V_var x]\<^sub>c\<^sub>v \<rbrace> = \<lbrace> z : b | c \<rbrace>" using type_eq_subst \<open>atom x \<sharp> c\<close> by auto
  ultimately show  ?thesis by auto
qed

lemma wfT_wfT_if:
  assumes "wfT \<Theta> \<B> \<Gamma> (\<lbrace> z2 : b  | CE_val v  ==  CE_val (V_lit L_false) IMP  c[z::=V_var z2]\<^sub>c\<^sub>v  \<rbrace>)" and "atom z2 \<sharp> (c,\<Gamma>)"
  shows "wfT \<Theta> \<B> \<Gamma> \<lbrace> z : b |  c \<rbrace>" 
proof -
  have *: "atom z2 \<sharp> (\<Theta>, \<B>, \<Gamma>)" using wfG_fresh_x wfX_wfY assms fresh_Pair by metis
  have "wfB \<Theta> \<B>  b" using assms wfT_elims by metis
  have "\<Theta>; \<B>; (GCons (z2,b,TRUE) \<Gamma>) \<turnstile>\<^sub>w\<^sub>f  (CE_val v  ==  CE_val (V_lit L_false) IMP  c[z::=V_var z2]\<^sub>c\<^sub>v)"  using wfT_wfC assms fresh_Pair by auto
  hence "\<Theta>; \<B>; ((z2,b,TRUE)  #\<^sub>\<Gamma>\<Gamma>) \<turnstile>\<^sub>w\<^sub>f c[z::=V_var z2]\<^sub>c\<^sub>v"  using wfC_elims by metis
  hence "wfT \<Theta> \<B> \<Gamma>  (\<lbrace> z2 : b  | c[z::=V_var z2]\<^sub>c\<^sub>v\<rbrace>)" using assms fresh_Pair wfTI \<open>wfB \<Theta> \<B> b\<close> * by auto
  moreover have "\<lbrace> z : b |  c \<rbrace> = \<lbrace> z2 : b | c[z::=V_var z2]\<^sub>c\<^sub>v \<rbrace>"  using type_eq_subst assms fresh_Pair by auto
  ultimately show ?thesis using wfTI assms by argo
qed

lemma wfT_fresh_c:
  fixes x::x
  assumes "wfT P \<B> \<Gamma> \<lbrace> z : b | c \<rbrace>" and "atom x \<sharp> \<Gamma>" and "x \<noteq> z"
  shows "atom x \<sharp> c"
proof(rule ccontr)
  assume "\<not> atom x \<sharp> c"
  hence *:"atom x \<in> supp c" using fresh_def by auto
  moreover have "supp c - set [atom z] \<union> supp b \<subseteq> atom_dom \<Gamma> \<union> supp \<B>"
    using assms  wfT_supp \<tau>.supp by blast
  moreover hence "atom x \<in> supp c - set [atom z]" using assms  * by auto
  ultimately have "atom x \<in> atom_dom \<Gamma>" using x_not_in_b_set by auto
  thus False using assms wfG_atoms_supp_eq wfT_wf fresh_def by metis
qed

lemma wfG_x_fresh [simp]: 
  fixes x::x
  assumes "wfG P \<B> G"
  shows "atom x \<notin> atom_dom G \<longleftrightarrow> atom x \<sharp> G"
  using wfG_atoms_supp_eq assms fresh_def  by metis

lemma wfD_x_fresh:
  fixes x::x
  assumes "atom x \<sharp> \<Gamma>" and "wfD P B \<Gamma> \<Delta>"
  shows "atom x \<sharp> \<Delta>"
using assms proof(induct \<Delta> rule: \<Delta>_induct)
  case DNil
  then show ?case using supp_DNil fresh_def by auto
next
  case (DCons u' t'  \<Delta>')
  have wfg: "wfG P B \<Gamma>" using wfD_wf DCons by blast
  hence wfd: "wfD P B \<Gamma> \<Delta>'" using wfD_elims DCons by blast
  have "supp t' \<subseteq> atom_dom \<Gamma> \<union> supp B" using wfT_supp DCons wfD_elims  by metis
  moreover have "atom x \<notin> atom_dom \<Gamma>" using DCons(2) fresh_def wfG_supp wfg by blast
  ultimately have  "atom x \<sharp> t'" using fresh_def DCons wfG_supp wfg x_not_in_b_set by blast
  moreover have "atom x \<sharp> u'" using supp_at_base fresh_def by fastforce
  ultimately have "atom x \<sharp> (u',t')" using supp_Pair by fastforce
  thus ?case using DCons fresh_DCons wfd by fast
qed

lemma wfG_fresh_x2:
  fixes \<Gamma>::\<Gamma> and z::x and \<Delta>::\<Delta> and \<Phi>::\<Phi>
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>" and "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>" and "atom z \<sharp> \<Gamma>" 
  shows "atom z \<sharp> (\<Theta>,\<Phi>,\<B>, \<Gamma>,\<Delta>)"
  unfolding fresh_prodN apply(intro conjI)
  using wfG_fresh_x assms fresh_prod3 wfX_wfY apply metis
  using wf_supp2(5)  assms fresh_def apply blast
  using assms wfG_fresh_x wfX_wfY fresh_prod3 apply metis
  using assms wfG_fresh_x wfX_wfY fresh_prod3 apply metis
  using wf_supp2(6)  assms fresh_def wfD_x_fresh by metis

lemma wfV_x_fresh:
  fixes v::v and b::b and \<Gamma>::\<Gamma> and x::x
  assumes "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b" and "atom x \<sharp> \<Gamma>"
  shows "atom x \<sharp> v"
proof -
  have "supp v \<subseteq> atom_dom \<Gamma> \<union> supp  \<B> " using assms wfV_supp by auto
  moreover have "atom x \<notin> atom_dom \<Gamma>" using fresh_def assms
     dom.simps subsetCE  wfG_elims wfG_supp  by (metis dom_supp_g)
  moreover have "atom x \<notin> supp \<B>" using x_not_in_b_set by auto
  ultimately show ?thesis using fresh_def by fast
qed

lemma wfE_x_fresh:
  fixes e::e and b::b and \<Gamma>::\<Gamma> and \<Delta>::\<Delta> and \<Phi>::\<Phi>  and x::x
  assumes "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b" and "atom x \<sharp> \<Gamma>"
  shows "atom x \<sharp> e"
proof -
  have "wfG \<Theta> \<B> \<Gamma>" using assms wfE_wf by auto
  hence "supp e \<subseteq> atom_dom \<Gamma> \<union> supp \<B> \<union> atom`fst`setD \<Delta>" using wfE_supp dom.simps assms by auto
  moreover have "atom x \<notin> atom_dom \<Gamma>" using fresh_def assms
     dom.simps subsetCE  \<open>wfG \<Theta> \<B> \<Gamma>\<close>  wfG_supp  by (metis dom_supp_g)
  moreover have "atom x \<notin> atom`fst`setD \<Delta>" by auto
  ultimately show ?thesis using fresh_def x_not_in_b_set by fast 
qed

lemma wfT_x_fresh:
  fixes \<tau>::\<tau> and \<Gamma>::\<Gamma> and  x::x
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>" and "atom x \<sharp> \<Gamma>"
  shows "atom x \<sharp> \<tau>"
proof -
  have "wfG \<Theta> \<B> \<Gamma>" using assms wfX_wfY by auto
  hence "supp \<tau> \<subseteq> atom_dom \<Gamma> \<union> supp \<B>" using wfT_supp dom.simps assms by auto
  moreover have "atom x \<notin> atom_dom \<Gamma>" using fresh_def assms
     dom.simps subsetCE  \<open>wfG \<Theta> \<B> \<Gamma>\<close>  wfG_supp  by (metis dom_supp_g)
  moreover have "atom x \<notin> supp \<B>" using x_not_in_b_set by simp
  ultimately show ?thesis using fresh_def by fast 
qed

lemma wfS_x_fresh:
  fixes s::s  and \<Delta>::\<Delta> and x::x
  assumes "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>  \<turnstile>\<^sub>w\<^sub>f s : b" and "atom x \<sharp> \<Gamma>"
  shows "atom x \<sharp> s"
proof - 
  have "supp s \<subseteq> atom_dom \<Gamma> \<union> atom ` fst ` setD \<Delta> \<union> supp \<B>"  using  wf_supp assms by metis
  moreover have "atom x \<notin> atom ` fst ` setD \<Delta>" by auto
  moreover have "atom x \<notin> atom_dom \<Gamma>" using assms fresh_def wfG_dom_supp wfX_wfY by metis
  moreover have "atom x \<notin> supp \<B>" using supp_b_empty supp_fset 
    by (simp add: x_not_in_b_set)
  ultimately show ?thesis using fresh_def by fast 
qed

lemma wfTh_fresh:
  fixes x
  assumes "wfTh T"
  shows "atom x \<sharp> T"
  using wf_supp1 assms fresh_def by fastforce

lemmas wfTh_x_fresh = wfTh_fresh

lemma wfPhi_fresh:
  fixes x
  assumes "wfPhi T P"
  shows "atom x \<sharp> P"
  using wf_supp assms fresh_def by fastforce

lemmas wfPhi_x_fresh = wfPhi_fresh
lemmas wb_x_fresh = wfTh_x_fresh wfPhi_x_fresh wfD_x_fresh wfT_x_fresh wfV_x_fresh

lemma wfG_inside_fresh[ms_fresh]:
  fixes \<Gamma>::\<Gamma> and x::x
  assumes "wfG P \<B> (\<Gamma>'@((x,b,c)  #\<^sub>\<Gamma>\<Gamma>))"
  shows "atom x \<notin> atom_dom \<Gamma>'"
using assms proof(induct \<Gamma>' rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x1 b1 c1 \<Gamma>1)
  moreover hence "atom x \<notin> atom ` fst `({(x1,b1,c1)})" proof -
    have *: "P; \<B>  \<turnstile>\<^sub>w\<^sub>f (\<Gamma>1 @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma>)" using wfG_elims append_g.simps GCons by metis
    have "atom x1 \<sharp>  (\<Gamma>1 @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma>)" using GCons wfG_elims append_g.simps by metis
    hence "atom x1 \<notin> atom_dom  (\<Gamma>1 @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma>)" using wfG_dom_supp fresh_def * by metis
    thus ?thesis by auto
  qed
  ultimately show ?case using append_g.simps atom_dom.simps toSet.simps wfG_elims dom.simps
    by (metis image_insert insert_iff insert_is_Un)
qed

lemma wfG_inside_x_in_atom_dom:
  fixes c::c and x::x  and \<Gamma>::\<Gamma> 
  shows "atom x \<in> atom_dom ( \<Gamma>'@ (x, b, c[z::=V_var x]\<^sub>c\<^sub>v)   #\<^sub>\<Gamma> \<Gamma>)"
  by(induct \<Gamma>'  rule: \<Gamma>_induct, (simp add: toSet.simps atom_dom.simps)+)

lemma wfG_inside_x_neq:
  fixes c::c and x::x  and \<Gamma>::\<Gamma> and G::\<Gamma> and xa::x
  assumes "G=( \<Gamma>'@ (x, b, c[z::=V_var x]\<^sub>c\<^sub>v)   #\<^sub>\<Gamma> \<Gamma>)" and "atom xa \<sharp> G" and " \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f G"
  shows "xa \<noteq> x"
proof - 
  have "atom xa \<notin> atom_dom G"  using fresh_def wfG_atoms_supp_eq assms by metis
  moreover have "atom x \<in> atom_dom G" using wfG_inside_x_in_atom_dom assms by simp
  ultimately show ?thesis by auto
qed

lemma wfG_inside_x_fresh:
  fixes c::c and x::x  and \<Gamma>::\<Gamma> and G::\<Gamma> and xa::x
  assumes "G=( \<Gamma>'@ (x, b, c[z::=V_var x]\<^sub>c\<^sub>v)   #\<^sub>\<Gamma> \<Gamma>)" and "atom xa \<sharp> G" and " \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f G"
  shows "atom xa \<sharp> x"
  using fresh_def supp_at_base wfG_inside_x_neq assms by auto

lemma wfT_nil_supp:
  fixes t::\<tau>
  assumes "\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f t" 
  shows "supp t = {}"
  using wfT_supp atom_dom.simps assms toSet.simps by force

section \<open>Misc\<close>

lemma wfG_cons_append:
  fixes b'::b
  assumes "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f ((x', b', c')   #\<^sub>\<Gamma> \<Gamma>') @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma>"
  shows "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f (\<Gamma>' @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma>)  \<and> atom x' \<sharp> (\<Gamma>' @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma>) \<and> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b' \<and> x' \<noteq> x"
proof - 
  have "((x', b', c')   #\<^sub>\<Gamma> \<Gamma>') @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma> = (x', b', c')   #\<^sub>\<Gamma> (\<Gamma>' @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma>)" using append_g.simps by auto
  hence *:"\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f  (\<Gamma>' @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma>)  \<and> atom x' \<sharp> (\<Gamma>' @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma>) \<and> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b'" using assms wfG_cons by metis
  moreover have "atom x' \<sharp> x" proof(rule wfG_inside_x_fresh[of "(\<Gamma>' @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma>)"])
    show "\<Gamma>' @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma> = \<Gamma>' @ (x, b, c[x::=V_var x]\<^sub>c\<^sub>v)   #\<^sub>\<Gamma> \<Gamma>" by simp
      show "  atom x' \<sharp> \<Gamma>' @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma>" using * by auto
      show "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>' @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma>  " using * by auto
    qed
  ultimately show  ?thesis by auto
qed

lemma flip_u_eq:
  fixes  u::u and u'::u and \<Theta>::\<Theta> and \<tau>::\<tau>
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>" 
  shows "(u \<leftrightarrow> u') \<bullet> \<tau> = \<tau>" and  "(u \<leftrightarrow> u') \<bullet> \<Gamma> = \<Gamma>"  and "(u \<leftrightarrow> u') \<bullet> \<Theta> = \<Theta>" and "(u \<leftrightarrow> u') \<bullet> \<B> = \<B>"
proof -
  show "(u \<leftrightarrow> u') \<bullet> \<tau> = \<tau>" using wfT_supp flip_fresh_fresh
    by (metis assms(1) fresh_def u_not_in_t)
  show "(u \<leftrightarrow> u') \<bullet> \<Gamma> = \<Gamma>" using u_not_in_g wfX_wfY assms flip_fresh_fresh fresh_def by metis
  show  "(u \<leftrightarrow> u') \<bullet> \<Theta> = \<Theta>" using theta_flip_eq assms wfX_wfY by metis
  show  "(u \<leftrightarrow> u') \<bullet> \<B> = \<B>" using u_not_in_b_set flip_fresh_fresh fresh_def by metis
qed

lemma wfT_wf_cons_flip: 
  fixes c::c and x::x
  assumes "wfT P \<B> \<Gamma> \<lbrace> z : b  | c \<rbrace>" and "atom x \<sharp> (c,\<Gamma>)"
  shows "wfG P \<B> ((x,b,c[z::=V_var x]\<^sub>c\<^sub>v)  #\<^sub>\<Gamma>\<Gamma>)"
proof -
  have "\<lbrace> x : b | c[z::=V_var x]\<^sub>c\<^sub>v \<rbrace> = \<lbrace> z : b  | c \<rbrace>" using assms freshers type_eq_subst by metis
  hence *:"wfT P \<B> \<Gamma>  \<lbrace> x : b | c[z::=V_var x]\<^sub>c\<^sub>v \<rbrace>" using assms by metis
  show ?thesis proof(rule wfG_consI)
    show \<open> P; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<close> using assms wfT_wf by auto
    show \<open>atom x \<sharp> \<Gamma>\<close> using assms   by auto
    show \<open> P; \<B>  \<turnstile>\<^sub>w\<^sub>f b \<close> using assms wfX_wfY b_of.simps  by metis
    show \<open> P; \<B> ; (x, b, TRUE)   #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c[z::=V_var x]\<^sub>c\<^sub>v \<close> using wfT_wfC * assms fresh_Pair by metis
  qed
qed

section \<open>Context Strengthening\<close>

text \<open>We can remove an entry for a variable from the context if the variable doesn't appear in the 
term and the variable is not used later in the context or any other context\<close>

lemma fresh_restrict:
  fixes y::"'a::at_base" and \<Gamma>::\<Gamma>
  assumes  "atom y \<sharp>  (\<Gamma>' @ (x, b, c)   #\<^sub>\<Gamma> \<Gamma>)"
  shows "atom y \<sharp> (\<Gamma>'@\<Gamma>)"
using assms proof(induct \<Gamma>' rule: \<Gamma>_induct)
  case GNil
  then show ?case using fresh_GCons fresh_GNil by auto
next
  case (GCons x' b' c' \<Gamma>'')
  then show ?case using fresh_GCons fresh_GNil by auto
qed

lemma wf_restrict1:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and b::b and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def
        and cs::branch_s and css::branch_list
  shows  "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b        \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c')  #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> atom x \<sharp> v \<Longrightarrow> atom x \<sharp> \<Gamma>\<^sub>1  \<Longrightarrow> \<Theta>; \<B>;  \<Gamma>\<^sub>1@\<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f  v : b" and
       
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f  c           \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c')  #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> atom x \<sharp> c\<Longrightarrow> atom x \<sharp> \<Gamma>\<^sub>1 \<Longrightarrow> \<Theta> ;  \<B> ; \<Gamma>\<^sub>1@\<Gamma>\<^sub>2  \<turnstile>\<^sub>w\<^sub>f  c" and
         "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>                \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c')  #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow>  atom x \<sharp> \<Gamma>\<^sub>1 \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>\<^sub>1@\<Gamma>\<^sub>2" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<tau>            \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c')  #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> atom x \<sharp> \<tau>\<Longrightarrow> atom x \<sharp> \<Gamma>\<^sub>1 \<Longrightarrow>  \<Theta>; \<B>;  \<Gamma>\<^sub>1@\<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f  \<tau>" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ts \<Longrightarrow> True" and 
         "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow>True" and
       
         "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b \<Longrightarrow> True" and
        
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ce : b    \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c')  #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> atom x \<sharp> ce  \<Longrightarrow> atom x \<sharp> \<Gamma>\<^sub>1 \<Longrightarrow> \<Theta>; \<B>;  \<Gamma>\<^sub>1@\<Gamma>\<^sub>2  \<turnstile>\<^sub>w\<^sub>f  ce : b"  and 
         "\<Theta>  \<turnstile>\<^sub>w\<^sub>f td \<Longrightarrow> True"
proof(induct   arbitrary: \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1  and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1  and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 
               rule:wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.inducts)
  case (wfV_varI \<Theta> \<B> \<Gamma> b c y)
  hence "y\<noteq>x" using v.fresh by auto
  hence "Some (b, c) = lookup (\<Gamma>\<^sub>1@\<Gamma>\<^sub>2) y" using lookup_restrict wfV_varI by metis
  then show ?case using wfV_varI wf_intros by metis
next
  case (wfV_litI \<Theta> \<Gamma> l)
  then show ?case using e.fresh wf_intros by metis
next
  case (wfV_pairI \<Theta> \<B> \<Gamma> v1 b1 v2 b2)
  show ?case proof
    show "\<Theta>; \<B>; \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f v1 : b1" using wfV_pairI by auto
    show "\<Theta>; \<B>; \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f v2 : b2" using wfV_pairI by auto
  qed
next
  case (wfV_consI s dclist \<Theta> dc x b c \<B> \<Gamma> v)
  show ?case proof
    show "AF_typedef s dclist \<in> set \<Theta>" using wfV_consI by auto
    show "(dc, \<lbrace> x : b  | c \<rbrace>) \<in> set dclist" using wfV_consI by auto
    show "\<Theta>; \<B>; \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f v : b" using wfV_consI by auto
  qed
next
   case (wfV_conspI s bv dclist \<Theta> dc x b' c \<B> b \<Gamma> v)
    show ?case proof
    show "AF_typedef_poly s bv dclist \<in> set \<Theta>" using wfV_conspI by auto
    show "(dc, \<lbrace> x : b'  | c \<rbrace>) \<in> set dclist" using wfV_conspI by auto
    show "\<Theta>; \<B>    \<turnstile>\<^sub>w\<^sub>f  b" using wfV_conspI by auto
    show " \<Theta>; \<B>; \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f v : b'[bv::=b]\<^sub>b\<^sub>b" using wfV_conspI by auto
    show "atom bv \<sharp> (\<Theta>, \<B>, \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2, b, v)" unfolding fresh_prodN fresh_append_g  using wfV_conspI fresh_prodN fresh_GCons fresh_append_g by metis
  qed
next 
  case (wfCE_valI \<Theta> \<B> \<Gamma> v b)
  then show ?case using ce.fresh wf_intros by metis
next
  case (wfCE_plusI \<Theta> \<B> \<Gamma> v1 v2)
   then show ?case using ce.fresh wf_intros by metis
next
  case (wfCE_leqI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case using ce.fresh wf_intros by metis
next
  case (wfCE_eqI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case using ce.fresh wf_intros by metis
next
  case (wfCE_fstI \<Theta> \<B> \<Gamma> v1 b1 b2)
   then show ?case using ce.fresh wf_intros by metis
next
  case (wfCE_sndI \<Theta> \<B> \<Gamma> v1 b1 b2)
 then show ?case using ce.fresh wf_intros by metis
next
  case (wfCE_concatI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case using ce.fresh wf_intros by metis
next
  case (wfCE_lenI \<Theta> \<B> \<Gamma> v1)
  then show ?case using ce.fresh wf_intros by metis
next
  case (wfTI z \<Theta> \<B> \<Gamma> b c)
  hence "x \<noteq> z" using wfTI
   fresh_GCons fresh_prodN fresh_PairD(1) fresh_gamma_append not_self_fresh by metis
  show ?case proof
    show \<open>atom z \<sharp> (\<Theta>, \<B>, \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2)\<close> using wfTI fresh_restrict[of z] using wfG_fresh_x wfX_wfY wfTI fresh_prodN by metis
    show \<open> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b \<close> using wfTI by auto
    have "\<Theta>; \<B>; ((z, b, TRUE)   #\<^sub>\<Gamma> \<Gamma>\<^sub>1) @ \<Gamma>\<^sub>2  \<turnstile>\<^sub>w\<^sub>f c " proof(rule  wfTI(5)[of "(z, b, TRUE)   #\<^sub>\<Gamma> \<Gamma>\<^sub>1" ])
      show \<open>(z, b, TRUE)   #\<^sub>\<Gamma> \<Gamma> = ((z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>\<^sub>1) @ (x, b', c')  #\<^sub>\<Gamma> \<Gamma>\<^sub>2\<close> using wfTI by auto
      show \<open>atom x \<sharp> c\<close> using wfTI \<tau>.fresh \<open>x \<noteq> z\<close> by auto
      show \<open>atom x \<sharp> (z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>\<^sub>1\<close> using wfTI \<open>x \<noteq> z\<close> fresh_GCons by simp
    qed
    thus  \<open> \<Theta>; \<B>; (z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2  \<turnstile>\<^sub>w\<^sub>f c \<close>  by auto
  qed
next
  case (wfC_eqI \<Theta> \<B> \<Gamma> e1 b e2)
  show ?case proof
    show "\<Theta>; \<B>; \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2  \<turnstile>\<^sub>w\<^sub>f e1 : b " using wfC_eqI c.fresh fresh_Nil by auto
    show "\<Theta>; \<B>; \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2  \<turnstile>\<^sub>w\<^sub>f e2 : b " using wfC_eqI c.fresh fresh_Nil by auto
  qed
next
  case (wfC_trueI \<Theta> \<Gamma>)
  then show ?case using c.fresh wf_intros by metis
next
  case (wfC_falseI \<Theta> \<Gamma>)
  then show ?case using c.fresh wf_intros by metis
next
  case (wfC_conjI \<Theta> \<Gamma> c1 c2)
  then show ?case using c.fresh wf_intros by metis
next
  case (wfC_disjI \<Theta> \<Gamma> c1 c2)
  then show ?case using c.fresh wf_intros by metis
next
case (wfC_notI \<Theta> \<Gamma> c1)
  then show ?case using c.fresh wf_intros by metis
next
  case (wfC_impI \<Theta> \<Gamma> c1 c2)
  then show ?case using c.fresh wf_intros by metis
next
  case (wfG_nilI \<Theta>)
  then show ?case using wfV_varI wf_intros 
    by (meson GNil_append \<Gamma>.simps(3))
next
  case (wfG_cons1I c1 \<Theta> \<B> G x1 b1)
  show  ?case proof(cases "\<Gamma>\<^sub>1=GNil")
    case True
    then show ?thesis using wfG_cons1I wfG_consI by auto
  next
    case False
    then obtain G'::\<Gamma> where *:"(x1, b1, c1)  #\<^sub>\<Gamma> G' = \<Gamma>\<^sub>1" using  GCons_eq_append_conv wfG_cons1I by auto
    hence **:"G=G' @ (x, b', c')  #\<^sub>\<Gamma> \<Gamma>\<^sub>2" using wfG_cons1I by auto

    have " \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f (x1, b1, c1)  #\<^sub>\<Gamma> (G' @ \<Gamma>\<^sub>2)" proof(rule Wellformed.wfG_cons1I)
      show \<open>c1 \<notin> {TRUE, FALSE}\<close> using wfG_cons1I by auto
      show \<open>atom x1 \<sharp> G' @ \<Gamma>\<^sub>2\<close> using wfG_cons1I(4) ** fresh_restrict by metis
      have " atom x \<sharp> G'" using wfG_cons1I *  using fresh_GCons by blast
      thus  \<open> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f G' @ \<Gamma>\<^sub>2 \<close> using wfG_cons1I(3)[of G'] **  by auto
      have "atom x \<sharp> c1 \<and> atom x \<sharp> (x1, b1, TRUE)  #\<^sub>\<Gamma> G'" using fresh_GCons \<open>atom x \<sharp> \<Gamma>\<^sub>1\<close> * by auto
      thus  \<open> \<Theta>; \<B>; (x1, b1, TRUE)  #\<^sub>\<Gamma> G' @ \<Gamma>\<^sub>2  \<turnstile>\<^sub>w\<^sub>f c1 \<close> using wfG_cons1I(6)[of "(x1, b1, TRUE)  #\<^sub>\<Gamma> G'"]  ** * wfG_cons1I by auto
      show \<open> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b1 \<close> using wfG_cons1I by auto
    qed
    thus ?thesis using * by auto
  qed
next
  case (wfG_cons2I c1 \<Theta> \<B> G x1 b1)
  show  ?case proof(cases "\<Gamma>\<^sub>1=GNil")
    case True
    then show ?thesis using wfG_cons2I wfG_consI by auto
  next
    case False
    then obtain G'::\<Gamma> where *:"(x1, b1, c1)  #\<^sub>\<Gamma> G' = \<Gamma>\<^sub>1" using  GCons_eq_append_conv wfG_cons2I by auto
    hence **:"G=G' @ (x, b', c')  #\<^sub>\<Gamma> \<Gamma>\<^sub>2" using wfG_cons2I by auto

    have " \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f (x1, b1, c1)  #\<^sub>\<Gamma> (G' @ \<Gamma>\<^sub>2)" proof(rule Wellformed.wfG_cons2I)
      show \<open>c1 \<in> {TRUE, FALSE}\<close> using wfG_cons2I by auto
      show \<open>atom x1 \<sharp> G' @ \<Gamma>\<^sub>2\<close> using wfG_cons2I ** fresh_restrict by metis
      have " atom x \<sharp> G'" using wfG_cons2I *  using fresh_GCons by blast
      thus  \<open> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f G' @ \<Gamma>\<^sub>2 \<close> using wfG_cons2I **  by auto     
      show \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b1 \<close> using wfG_cons2I by auto
    qed
    thus ?thesis using * by auto
  qed
qed(auto)+

lemma wf_restrict2:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and b::b and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def
        and cs::branch_s and css::branch_list
  shows          "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b    \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c') #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> atom x \<sharp> e  \<Longrightarrow> atom x \<sharp> \<Gamma>\<^sub>1 \<Longrightarrow> atom x \<sharp> \<Delta> \<Longrightarrow> \<Theta>; \<Phi>; \<B>;  \<Gamma>\<^sub>1@\<Gamma>\<^sub>2 ;  \<Delta> \<turnstile>\<^sub>w\<^sub>f  e : b" and
         "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b   \<Longrightarrow> True" and
         "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f cs : b \<Longrightarrow> True" and
         "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b \<Longrightarrow> True" and     
         "\<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) \<Longrightarrow> True " and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<Delta>  \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c') #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> atom x \<sharp> \<Gamma>\<^sub>1 \<Longrightarrow> atom x \<sharp> \<Delta> \<Longrightarrow> \<Theta>; \<B>; \<Gamma>\<^sub>1@\<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f  \<Delta>" and       
         "\<Theta> ; \<Phi>   \<turnstile>\<^sub>w\<^sub>f ftq \<Longrightarrow> True" and
         "\<Theta> ; \<Phi>  ; \<B> \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow> True" 
    
proof(induct   arbitrary: \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1  and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1  and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 
               rule:wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.inducts)
  case (wfE_valI \<Theta> \<Phi> \<Gamma> \<Delta> v b)
  then show ?case using e.fresh wf_intros wf_restrict1 by metis
next
  case (wfE_plusI \<Theta> \<Phi> \<Gamma> \<Delta> v1 v2)
  then show ?case using e.fresh wf_intros wf_restrict1 by metis
next
  case (wfE_leqI \<Theta> \<Phi> \<Gamma> \<Delta> v1 v2)
  then show ?case using e.fresh wf_intros wf_restrict1 by metis
next
  case (wfE_eqI \<Theta> \<Phi> \<Gamma> \<Delta> v1 b v2)
  then show ?case using e.fresh wf_intros wf_restrict1 by metis
next
  case (wfE_fstI \<Theta> \<Phi> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case using e.fresh wf_intros wf_restrict1 by metis
next
  case (wfE_sndI \<Theta> \<Phi> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case using e.fresh wf_intros wf_restrict1 by metis
next
  case (wfE_concatI \<Theta> \<Phi> \<Gamma> \<Delta> v1 v2)
  then show ?case using e.fresh wf_intros wf_restrict1 by metis
next
  case (wfE_splitI \<Theta> \<Phi> \<Gamma> \<Delta> v1 v2)
  then show ?case using e.fresh wf_intros wf_restrict1 by metis
next
  case (wfE_lenI \<Theta> \<Phi> \<Gamma> \<Delta> v1)
  then show ?case using e.fresh wf_intros wf_restrict1 by metis
next
  case (wfE_appI \<Theta> \<Phi> \<Gamma> \<Delta> f x b c \<tau> s' v)
  then show ?case using e.fresh wf_intros wf_restrict1 by metis
next
  case (wfE_appPI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> b' bv v \<tau> f x b c s)
  show ?case proof
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wfE_appPI by auto
    show \<open> \<Theta>; \<B>; \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close>  using wfE_appPI by auto
    show \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b' \<close>  using wfE_appPI by auto

    have "atom bv \<sharp>  \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2" using  wfE_appPI fresh_prodN fresh_restrict  by metis
    thus  \<open>atom bv \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2, \<Delta>, b', v, (b_of \<tau>)[bv::=b']\<^sub>b)\<close>  
      using wfE_appPI fresh_prodN by auto

    show \<open>Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f\<close>  using wfE_appPI by auto
    show \<open> \<Theta>; \<B>; \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f v : b[bv::=b']\<^sub>b \<close>  using wfE_appPI wf_restrict1 by auto
  qed
next
  case (wfE_mvarI \<Theta> \<Phi> \<Gamma> \<Delta> u \<tau>)
  then show ?case using e.fresh wf_intros by metis
next
  case (wfD_emptyI \<Theta> \<Gamma>)
  then show ?case using c.fresh wf_intros wf_restrict1 by metis
next
  case (wfD_cons \<Theta> \<B> \<Gamma> \<Delta> \<tau> u)
  show ?case proof
    show "\<Theta>; \<B>; \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2  \<turnstile>\<^sub>w\<^sub>f \<Delta>" using wfD_cons fresh_DCons by metis
    show "\<Theta>; \<B>; \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2  \<turnstile>\<^sub>w\<^sub>f \<tau> " using wfD_cons fresh_DCons fresh_Pair wf_restrict1 by metis
    show "u \<notin> fst ` setD \<Delta>" using wfD_cons by auto
  qed
next
  case (wfFTNone \<Theta> ft)
  then show ?case by auto
next
  case (wfFTSome \<Theta> bv ft)
  then show ?case by auto
next
  case (wfFTI \<Theta> B b \<Phi> x c s \<tau>)
  then show ?case by auto
qed(auto)+

lemmas wf_restrict=wf_restrict1 wf_restrict2

lemma wfT_restrict2:
  fixes \<tau>::\<tau>
  assumes "wfT \<Theta> \<B> ((x, b, c) #\<^sub>\<Gamma> \<Gamma>) \<tau>" and "atom x \<sharp> \<tau>" 
  shows "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>"
  using wf_restrict1(4)[of \<Theta> \<B> "((x, b, c) #\<^sub>\<Gamma> \<Gamma>)"  \<tau> GNil x "b" "c" \<Gamma>] assms fresh_GNil append_g.simps by auto

lemma wfG_intros2:
  assumes "wfC P \<B> ((x,b,TRUE) #\<^sub>\<Gamma>\<Gamma>) c"
  shows  "wfG P \<B>  ((x,b,c) #\<^sub>\<Gamma>\<Gamma>)"
proof - 
  have "wfG P \<B>   ((x,b,TRUE) #\<^sub>\<Gamma>\<Gamma>)" using wfC_wf  assms by auto
  hence *:"wfG P \<B> \<Gamma> \<and> atom x \<sharp> \<Gamma> \<and> wfB P \<B> b" using wfG_elims by metis
  show ?thesis using assms proof(cases "c \<in> {TRUE,FALSE}")
    case True 
    then show ?thesis using wfG_cons2I * by auto
  next
    case False
    then show ?thesis using wfG_cons1I * assms by auto
  qed
qed

section \<open>Type Definitions\<close>

lemma wf_theta_weakening1: 
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and b::b and \<B> :: \<B> and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def
         and cs::branch_s and css::branch_list and t::\<tau>

  shows  "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b \<Longrightarrow>  \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>' ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>' ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f  c" and
         "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>' ; \<B>   \<turnstile>\<^sub>w\<^sub>f \<Gamma>" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<tau> \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow>  \<Theta>' ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f  \<tau>" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ts \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>' ; \<B> ;  \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ts" and 
         "\<turnstile>\<^sub>w\<^sub>f P \<Longrightarrow> True " and
         "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b  \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>' ; \<B>  \<turnstile>\<^sub>w\<^sub>f b"  and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ce : b \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>' ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce : b" and
         "\<Theta>  \<turnstile>\<^sub>w\<^sub>f td \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>'  \<turnstile>\<^sub>w\<^sub>f td"
proof(nominal_induct b and c and \<Gamma> and \<tau> and ts and P and b and b and td 
      avoiding: \<Theta>'     
      rule:wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.strong_induct)
  case (wfV_consI s dclist \<Theta> dc x b c \<B> \<Gamma> v)
  show ?case proof
    show \<open>AF_typedef s dclist \<in> set \<Theta>'\<close> using wfV_consI by auto
    show \<open>(dc, \<lbrace> x : b  | c \<rbrace>) \<in> set dclist\<close> using wfV_consI by auto
    show \<open> \<Theta>' ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b \<close> using wfV_consI by auto
  qed
next
  case (wfV_conspI s bv dclist \<Theta> dc x b' c \<B> b \<Gamma> v)
    show ?case proof
    show \<open>AF_typedef_poly s bv dclist \<in> set \<Theta>'\<close> using wfV_conspI by auto
    show \<open>(dc, \<lbrace> x : b'  | c \<rbrace>) \<in> set dclist\<close> using wfV_conspI by auto
    show \<open>\<Theta>' ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b'[bv::=b]\<^sub>b\<^sub>b  \<close> using wfV_conspI by auto
    show "\<Theta>' ;  \<B>  \<turnstile>\<^sub>w\<^sub>f b "  using wfV_conspI by auto
    show "atom bv \<sharp> (\<Theta>', \<B>, \<Gamma>, b, v)" using wfV_conspI fresh_prodN by auto
  qed
next
  case (wfTI z \<Theta> \<B> \<Gamma> b c)
  thus ?case using Wellformed.wfTI by auto
next
  case (wfB_consI \<Theta> s dclist)
  show ?case proof 
    show \<open>   \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<close> using wfB_consI by auto
    show \<open>AF_typedef s dclist \<in> set \<Theta>'\<close>  using wfB_consI by auto
  qed
next   
  case (wfB_appI \<Theta> \<B> b s bv dclist)
  show ?case proof 
    show \<open>   \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<close> using wfB_appI by auto
    show \<open>AF_typedef_poly s bv dclist \<in> set \<Theta>'\<close>  using wfB_appI by auto
    show "\<Theta>' ;   \<B>  \<turnstile>\<^sub>w\<^sub>f b" using wfB_appI by simp
  qed
qed(metis wf_intros)+

lemma wf_theta_weakening2: 
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and b::b and \<B> :: \<B> and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def
         and cs::branch_s and css::branch_list and t::\<tau>
  shows 
         "\<Theta>; \<Phi>; \<B>; \<Gamma>  ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>' ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b" and
         "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>' ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b" and
         "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f cs : b \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>' ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> ; tid ; dc ; t  \<turnstile>\<^sub>w\<^sub>f cs : b" and
         "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>' ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b" and     
         "\<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>' \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>)" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<Longrightarrow> \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>' ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f  \<Delta>" and
         "\<Theta> ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f ftq \<Longrightarrow>  \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>' ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f ftq" and
         "\<Theta> ; \<Phi> ; \<B> \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow>  \<turnstile>\<^sub>w\<^sub>f \<Theta>' \<Longrightarrow> set \<Theta> \<subseteq> set \<Theta>' \<Longrightarrow> \<Theta>' ; \<Phi> ; \<B> \<turnstile>\<^sub>w\<^sub>f ft" 
 
proof(nominal_induct b and b and b and b and \<Phi> and \<Delta> and  ftq and ft 
      avoiding: \<Theta>'     
rule:wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.strong_induct)
  case (wfE_appPI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> b' bv v \<tau> f x b c s)
  show ?case proof
    show \<open> \<Theta>'  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wfE_appPI by auto
    show \<open> \<Theta>' ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfE_appPI by auto
    show \<open> \<Theta>' ; \<B>  \<turnstile>\<^sub>w\<^sub>f b' \<close> using wfE_appPI wf_theta_weakening1 by auto
    show \<open>atom bv \<sharp> (\<Phi>, \<Theta>', \<B>, \<Gamma>, \<Delta>, b', v, (b_of \<tau>)[bv::=b']\<^sub>b)\<close> using wfE_appPI by auto
    show \<open>Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f\<close> using wfE_appPI by auto
    show \<open> \<Theta>' ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b[bv::=b']\<^sub>b \<close> using wfE_appPI wf_theta_weakening1 by auto
  qed
next
  case (wfS_matchI \<Theta> \<B> \<Gamma> v tid  dclist \<Delta> \<Phi> cs b)
  show ?case proof
    show \<open> \<Theta>' ; \<B> ;  \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : B_id tid \<close> using wfS_matchI wf_theta_weakening1 by auto
    show \<open>AF_typedef tid dclist \<in> set \<Theta>'\<close> using wfS_matchI by auto
    show \<open> \<Theta>' ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfS_matchI by auto
    show \<open> \<Theta>'  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wfS_matchI by auto
    show \<open>\<Theta>'; \<Phi>; \<B>; \<Gamma>; \<Delta>; tid; dclist \<turnstile>\<^sub>w\<^sub>f cs : b \<close> using wfS_matchI by auto
  qed
next
   case (wfS_varI \<Theta> \<B> \<Gamma> \<tau> v u \<Phi> \<Delta> b s)
  show ?case proof
    show \<open> \<Theta>' ; \<B> ; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<tau> \<close> using wfS_varI wf_theta_weakening1 by auto
    show \<open> \<Theta>' ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b_of \<tau> \<close> using wfS_varI wf_theta_weakening1 by auto
    show \<open>atom u \<sharp> (\<Phi>, \<Theta>', \<B>, \<Gamma>, \<Delta>, \<tau>, v, b)\<close> using wfS_varI by auto
    show \<open> \<Theta>' ; \<Phi> ; \<B> ; \<Gamma> ; (u, \<tau>)  #\<^sub>\<Delta> \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<close> using wfS_varI by auto
  qed
next
  case (wfS_letI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e b' x s b)
  show ?case proof
    show \<open> \<Theta>' ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b' \<close> using wfS_letI by auto
    show \<open> \<Theta>' ; \<Phi> ; \<B> ; (x, b', TRUE)  #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<close> using wfS_letI by auto
    show \<open> \<Theta>' ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfS_letI by auto
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>', \<B>, \<Gamma>, \<Delta>, e, b)\<close> using wfS_letI by auto
  qed
next
  case (wfS_let2I \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 \<tau> x s2 b)
  show ?case proof
    show \<open> \<Theta>' ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s1 : b_of \<tau> \<close> using wfS_let2I by auto
    show \<open> \<Theta>' ; \<B> ; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<tau> \<close> using wfS_let2I wf_theta_weakening1 by auto
    show \<open> \<Theta>' ; \<Phi> ; \<B> ; (x, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s2 : b \<close> using wfS_let2I by auto
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>', \<B>, \<Gamma>, \<Delta>, s1, b, \<tau>)\<close> using wfS_let2I by auto
  qed
next
  case (wfS_branchI \<Theta> \<Phi> \<B> x \<tau> \<Gamma> \<Delta> s b tid dc)
  show ?case proof
    show \<open> \<Theta>' ; \<Phi> ; \<B> ; (x, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<close> using wfS_branchI by auto
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>', \<B>, \<Gamma>, \<Delta>, \<Gamma>, \<tau>)\<close> using wfS_branchI by auto
    show \<open> \<Theta>' ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfS_branchI by auto
  qed
next
   case (wfPhi_consI f \<Phi> \<Theta> ft)
  show ?case proof
    show "f \<notin> name_of_fun ` set \<Phi>" using wfPhi_consI by auto
    show "\<Theta>' ; \<Phi> \<turnstile>\<^sub>w\<^sub>f ft"  using wfPhi_consI by auto
    show "\<Theta>' \<turnstile>\<^sub>w\<^sub>f \<Phi>"  using wfPhi_consI by auto
  qed
next
  case (wfFTNone \<Theta> ft)
  then show ?case using  wf_intros by metis
next
  case (wfFTSome \<Theta> bv ft)
  then show ?case using wf_intros by metis
next
  case (wfFTI \<Theta> B b \<Phi> x c s \<tau>)
  thus ?case using Wellformed.wfFTI wf_theta_weakening1 by simp
next
  case (wfS_assertI \<Theta> \<Phi> \<B> x c \<Gamma> \<Delta> s b)
  show ?case proof  
    show \<open> \<Theta>' ; \<Phi> ; \<B> ; (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<close> using wfS_assertI wf_theta_weakening1 by auto
    show \<open> \<Theta>' ; \<B> ; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c \<close> using wfS_assertI wf_theta_weakening1 by auto
    show \<open> \<Theta>' ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfS_assertI wf_theta_weakening1 by auto
    have "atom x \<sharp> \<Theta>'" using wf_supp(6)[OF \<open>\<turnstile>\<^sub>w\<^sub>f \<Theta>' \<close>] fresh_def by auto
    thus  \<open>atom x \<sharp> (\<Phi>, \<Theta>', \<B>, \<Gamma>, \<Delta>, c, b, s)\<close> using wfS_assertI fresh_prodN fresh_def by simp
  qed
qed(metis wf_intros wf_theta_weakening1 )+

lemmas wf_theta_weakening = wf_theta_weakening1 wf_theta_weakening2

lemma lookup_wfTD:
  fixes td::type_def
  assumes  "td \<in> set \<Theta>" and "\<turnstile>\<^sub>w\<^sub>f \<Theta>"
  shows "\<Theta> \<turnstile>\<^sub>w\<^sub>f td"
 using assms  proof(induct \<Theta> )
  case Nil
  then show ?case by auto
next
  case (Cons td'  \<Theta>')
  then consider "td = td'" | "td \<in> set \<Theta>'" by auto
  then have "\<Theta>' \<turnstile>\<^sub>w\<^sub>f td" proof(cases)
    case 1
    then show ?thesis using Cons using wfTh_elims by auto
  next
    case 2
    then show ?thesis using Cons using wfTh_elims by auto
  qed
  then show ?case using wf_theta_weakening Cons  by (meson set_subset_Cons)
qed

subsection \<open>Simple\<close>

lemma wfTh_dclist_unique:
  assumes   "wfTh \<Theta>" and "AF_typedef tid dclist1 \<in> set \<Theta>" and  "AF_typedef tid dclist2 \<in> set \<Theta>" 
  shows "dclist1 = dclist2"
using assms proof(induct \<Theta> rule: \<Theta>_induct)
  case TNil
  then show ?case by auto
next
  case (AF_typedef tid' dclist' \<Theta>')
  then show ?case using wfTh_elims
    by (metis image_eqI name_of_type.simps(1) set_ConsD type_def.eq_iff(1))
next
  case (AF_typedef_poly tid bv dclist \<Theta>')
  then show ?case using wfTh_elims by auto
qed

lemma wfTs_ctor_unique:
  fixes dclist::"(string*\<tau>) list"
  assumes  "\<Theta> ; {||}  ; GNil \<turnstile>\<^sub>w\<^sub>f  dclist" and "(c, t1) \<in> set dclist"  and "(c,t2) \<in> set dclist"  
  shows "t1 = t2" 
  using assms proof(induct dclist rule: list.inducts)
  case Nil
  then show ?case by auto
next
  case (Cons x1 x2)
  consider "x1 = (c,t1)" | "x1 = (c,t2)" | "x1 \<noteq> (c,t1) \<and> x1 \<noteq> (c,t2)" by auto
  thus ?case proof(cases)
    case 1
    then show ?thesis using Cons wfTs_elims set_ConsD
      by (metis fst_conv image_eqI prod.inject)
  next
    case 2
      then show ?thesis using Cons wfTs_elims set_ConsD
      by (metis fst_conv image_eqI prod.inject)
  next
    case 3
    then show ?thesis using Cons wfTs_elims by (metis set_ConsD)
  qed
qed

lemma wfTD_ctor_unique:
  assumes  "\<Theta> \<turnstile>\<^sub>w\<^sub>f (AF_typedef tid dclist)" and "(c, t1) \<in> set dclist"  and "(c,t2) \<in> set dclist"  
  shows "t1 = t2" 
  using wfTD_elims wfTs_elims assms  wfTs_ctor_unique by metis

lemma wfTh_ctor_unique:
  assumes   "wfTh \<Theta>" and "AF_typedef tid dclist \<in> set \<Theta>" and "(c, t1) \<in> set dclist"  and "(c,t2) \<in> set dclist"  
  shows "t1 = t2" 
  using lookup_wfTD wfTD_ctor_unique assms by metis

lemma wfTs_supp_t:
  fixes dclist::"(string*\<tau>) list"
  assumes "(c,t) \<in> set dclist" and "\<Theta> ; B ; GNil \<turnstile>\<^sub>w\<^sub>f dclist" 
  shows "supp t \<subseteq> supp B"
using assms proof(induct dclist arbitrary: c t rule:list.induct)
  case Nil
  then show ?case by auto
next
  case (Cons ct dclist')
  then consider "ct = (c,t)" | "(c,t) \<in> set dclist'" by auto
  then show ?case proof(cases)
    case 1
    then have "\<Theta> ; B ; GNil \<turnstile>\<^sub>w\<^sub>f t" using Cons wfTs_elims by blast
    thus ?thesis using wfT_supp atom_dom.simps by force
  next
    case 2
    then show ?thesis using Cons wfTs_elims by metis
  qed
qed

lemma wfTh_lookup_supp_empty:
  fixes t::\<tau>
  assumes  "AF_typedef tid dclist \<in> set \<Theta>" and "(c,t) \<in> set dclist" and "\<turnstile>\<^sub>w\<^sub>f \<Theta>"
  shows "supp t = {}" 
proof - 
  have "\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f dclist" using assms lookup_wfTD  wfTD_elims by metis
  thus ?thesis using wfTs_supp_t assms by force
qed

lemma wfTh_supp_b:
  assumes  "AF_typedef tid dclist \<in> set \<Theta>" and "(dc,\<lbrace> z : b | c \<rbrace> ) \<in> set dclist" and "\<turnstile>\<^sub>w\<^sub>f \<Theta>"
  shows "supp b = {}" 
  using assms wfTh_lookup_supp_empty \<tau>.supp by blast

lemma wfTh_b_eq_iff:
  fixes bva1::bv and bva2::bv and dc::string 
  assumes "(dc, \<lbrace> x1 : b1  | c1 \<rbrace>) \<in> set dclist1" and "(dc, \<lbrace> x2 : b2  | c2 \<rbrace>) \<in> set dclist2" and
   "wfTs P {|bva1|} GNil dclist1" and  "wfTs P {|bva2|} GNil dclist2" 
  "[[atom bva1]]lst.dclist1 = [[atom bva2]]lst.dclist2"
 shows  "[[atom bva1]]lst. (dc,\<lbrace> x1 : b1  | c1 \<rbrace>) = [[atom bva2]]lst. (dc,\<lbrace> x2 : b2  | c2 \<rbrace>)"
using assms proof(induct dclist1 arbitrary: dclist2)
  case Nil
  then show ?case by auto
next
  case (Cons dct1' dclist1')
  show ?case proof(cases "dclist2 = []")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    then obtain dct2' and dclist2' where cons:"dct2' # dclist2' = dclist2" using list.exhaust by metis
    hence *:"[[atom bva1]]lst. dclist1' = [[atom bva2]]lst. dclist2' \<and> [[atom bva1]]lst. dct1' = [[atom bva2]]lst. dct2'" 
      using Cons lst_head_cons Cons cons by metis
    hence **: "fst dct1' = fst dct2'" using lst_fst[THEN lst_pure] 
      by (metis (no_types) \<open>[[atom bva1]]lst. dclist1' = [[atom bva2]]lst. dclist2' \<and> [[atom bva1]]lst. dct1' = [[atom bva2]]lst. dct2'\<close> 
            \<open>\<And>x2 x1 t2' t2a t2 t1. [[atom x1]]lst. (t1, t2a) = [[atom x2]]lst. (t2, t2') \<Longrightarrow> t1 = t2\<close> fst_conv surj_pair)    
    show ?thesis proof(cases "fst dct1' = dc")
      case True
      have "dc \<notin> fst ` set dclist1'" using  wfTs_elims Cons by (metis True fstI)
      hence 1:"(dc, \<lbrace> x1 : b1  | c1 \<rbrace>) = dct1'" using Cons by (metis fstI image_iff set_ConsD)
      have "dc \<notin> fst ` set dclist2'" using  wfTs_elims Cons cons 
        by (metis "**" True fstI)
      hence 2:"(dc, \<lbrace> x2 : b2  | c2 \<rbrace>) = dct2' " using Cons cons  by (metis  fst_conv image_eqI set_ConsD)
      then show ?thesis using Cons *  1 2   by blast
    next
      case False
      hence "fst dct2' \<noteq> dc" using **  by auto
      hence "(dc, \<lbrace> x1 : b1  | c1 \<rbrace>) \<in> set dclist1' \<and> (dc, \<lbrace> x2 : b2  | c2 \<rbrace>) \<in> set dclist2' " using Cons cons False 
        by (metis fstI set_ConsD)
      moreover have "[[atom bva1]]lst. dclist1' = [[atom bva2]]lst. dclist2'" using * False  by metis
      ultimately  show ?thesis using Cons ** *  
        using cons wfTs_elims(2) by blast
    qed
  qed
qed


subsection \<open>Polymorphic\<close>

lemma wfTh_wfTs_poly:
  fixes dclist::"(string * \<tau>) list"
  assumes "AF_typedef_poly tyid bva dclist \<in> set P" and "\<turnstile>\<^sub>w\<^sub>f P"
  shows  "P ; {|bva|}  ; GNil \<turnstile>\<^sub>w\<^sub>f  dclist"
proof -
  have *:"P \<turnstile>\<^sub>w\<^sub>f AF_typedef_poly tyid bva dclist" using lookup_wfTD assms by simp

  obtain bv lst where *:"P ; {|bv|}  ; GNil \<turnstile>\<^sub>w\<^sub>f lst  \<and> 
       (\<forall>c. atom c \<sharp> (dclist, lst) \<longrightarrow> atom c \<sharp> (bva, bv, dclist, lst) \<longrightarrow> (bva \<leftrightarrow> c) \<bullet> dclist = (bv \<leftrightarrow> c) \<bullet> lst)"  
    using wfTD_elims(2)[OF *] by metis

  obtain c::bv where  **:"atom c \<sharp> ((dclist, lst),(bva, bv, dclist, lst))" using obtain_fresh by metis
  have "P ; {|bv|}  ; GNil \<turnstile>\<^sub>w\<^sub>f lst" using * by metis
  hence "wfTs ((bv \<leftrightarrow> c) \<bullet> P)  ((bv \<leftrightarrow> c) \<bullet> {|bv|})  ((bv \<leftrightarrow> c) \<bullet> GNil) ((bv \<leftrightarrow> c) \<bullet> lst)" using ** wfTs.eqvt by metis
  hence "wfTs P  {|c|}  GNil ((bva \<leftrightarrow> c) \<bullet> dclist)" using * theta_flip_eq fresh_GNil assms 
  proof -
    have "\<forall>b ba. (ba::bv \<leftrightarrow> b) \<bullet> P = P"  by (metis \<open>\<turnstile>\<^sub>w\<^sub>f P\<close> theta_flip_eq)
    then show ?thesis
      using "*" "**" \<open>(bv \<leftrightarrow> c) \<bullet> P ; (bv \<leftrightarrow> c) \<bullet> {|bv|} ; (bv \<leftrightarrow> c) \<bullet> GNil \<turnstile>\<^sub>w\<^sub>f (bv \<leftrightarrow> c) \<bullet> lst\<close> by fastforce
  qed
  hence "wfTs ((bva \<leftrightarrow> c) \<bullet> P)  ((bva \<leftrightarrow> c) \<bullet> {|bva|})  ((bva \<leftrightarrow> c) \<bullet> GNil) ((bva \<leftrightarrow> c) \<bullet> dclist)" 
         using wfTs.eqvt fresh_GNil 
         by (simp add: assms(2) theta_flip_eq2)

  thus ?thesis using wfTs.eqvt permute_flip_cancel by metis
qed

lemma wfTh_dclist_poly_unique:
  assumes   "wfTh \<Theta>" and "AF_typedef_poly tid bva dclist1 \<in> set \<Theta>" and  "AF_typedef_poly tid bva2 dclist2 \<in> set \<Theta>" 
  shows "[[atom bva]]lst. dclist1 = [[atom bva2]]lst.dclist2"
using assms proof(induct \<Theta> rule: \<Theta>_induct)
  case TNil
  then show ?case by auto
next
  case (AF_typedef tid' dclist' \<Theta>')
  then show ?case using wfTh_elims by auto
next
  case (AF_typedef_poly tid bv dclist \<Theta>')
  then show ?case using wfTh_elims  image_eqI name_of_type.simps set_ConsD type_def.eq_iff 
    by (metis Abs1_eq(3))
qed

lemma wfTh_poly_lookup_supp:
  fixes t::\<tau>
  assumes  "AF_typedef_poly tid bv dclist \<in> set \<Theta>" and "(c,t) \<in> set dclist" and "\<turnstile>\<^sub>w\<^sub>f \<Theta>"
  shows "supp t \<subseteq> {atom bv}" 
proof - 
  have "supp dclist  \<subseteq> {atom bv}"   using assms lookup_wfTD  wf_supp1 type_def.supp 
    by (metis Diff_single_insert Un_subset_iff list.simps(15) supp_Nil supp_of_atom_list)
  then show ?thesis using assms(2) proof(induct dclist)
    case Nil
    then show ?case by auto
  next
    case (Cons a dclist)
    then show ?case using supp_Pair supp_Cons 
      by (metis (mono_tags, hide_lams) Un_empty_left Un_empty_right pure_supp subset_Un_eq subset_singletonD supp_list_member)
  qed
qed
  
lemma wfTh_poly_supp_b:
  assumes  "AF_typedef_poly tid  bv dclist \<in> set \<Theta>" and "(dc,\<lbrace> z : b | c \<rbrace> ) \<in> set dclist" and "\<turnstile>\<^sub>w\<^sub>f \<Theta>"
  shows "supp b \<subseteq> {atom bv}" 
  using assms wfTh_poly_lookup_supp \<tau>.supp by force

lemma subst_g_inside:  
  fixes x::x and c::c and \<Gamma>::\<Gamma>  and \<Gamma>'::\<Gamma>
  assumes "wfG P \<B> (\<Gamma>' @ (x, b, c[z::=V_var x]\<^sub>c\<^sub>v)  #\<^sub>\<Gamma> \<Gamma>)" 
  shows  "(\<Gamma>' @ (x, b, c[z::=V_var x]\<^sub>c\<^sub>v)  #\<^sub>\<Gamma> \<Gamma>)[x::=v]\<^sub>\<Gamma>\<^sub>v =  (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v@\<Gamma>)"  
using assms proof(induct \<Gamma>' rule: \<Gamma>_induct)
  case GNil
  then show ?case using subst_gb.simps by simp
next
  case (GCons x' b' c' G) 
  hence wfg:"wfG P \<B> (G @ (x, b, c[z::=V_var x]\<^sub>c\<^sub>v)  #\<^sub>\<Gamma> \<Gamma>) \<and> atom x' \<sharp> (G @ (x, b, c[z::=V_var x]\<^sub>c\<^sub>v)  #\<^sub>\<Gamma> \<Gamma>)" using wfG_elims(2) 
    using GCons.prems append_g.simps by metis 
  hence "atom x \<notin> atom_dom ((x', b', c')  #\<^sub>\<Gamma> G)"  using  GCons wfG_inside_fresh by fast
  hence "x\<noteq>x'" 
    using  GCons append_Cons  wfG_inside_fresh atom_dom.simps toSet.simps by simp
  hence "((GCons (x', b', c') G) @ (GCons (x, b, c[z::=V_var x]\<^sub>c\<^sub>v) \<Gamma>))[x::=v]\<^sub>\<Gamma>\<^sub>v  =  
         (GCons (x', b', c') (G @ (GCons (x, b, c[z::=V_var x]\<^sub>c\<^sub>v) \<Gamma>)))[x::=v]\<^sub>\<Gamma>\<^sub>v" by auto
  also have "... =  GCons (x', b', c'[x::=v]\<^sub>c\<^sub>v) ((G @ (GCons (x, b, c[z::=V_var x]\<^sub>c\<^sub>v) \<Gamma>))[x::=v]\<^sub>\<Gamma>\<^sub>v)"  
      using subst_gv.simps \<open>x\<noteq>x'\<close> by simp
  also have "... = (x', b', c'[x::=v]\<^sub>c\<^sub>v)  #\<^sub>\<Gamma> (G[x::=v]\<^sub>\<Gamma>\<^sub>v @ \<Gamma>)" using GCons  wfg by blast
  also have "... = ((x', b', c')  #\<^sub>\<Gamma> G)[x::=v]\<^sub>\<Gamma>\<^sub>v @ \<Gamma>"  using subst_gv.simps \<open>x\<noteq>x'\<close>  by simp
  finally show ?case by auto
qed

lemma wfTh_td_eq: 
  assumes "td1 \<in> set (td2 # P)" and "wfTh (td2 # P)" and "name_of_type td1 = name_of_type td2"
  shows "td1 = td2"
proof(rule ccontr)
  assume as: "td1 \<noteq> td2"
  have "name_of_type td2 \<notin> name_of_type ` set P" using wfTh_elims(2)[OF assms(2)] by metis
  moreover have "td1 \<in> set P" using assms as by simp
  ultimately have "name_of_type td1 \<noteq> name_of_type td2"
    by (metis rev_image_eqI)
  thus False using assms by auto
qed

lemma wfTh_td_unique:
  assumes "td1 \<in> set P" and "td2  \<in> set P" and "wfTh P" and "name_of_type td1 = name_of_type td2"
  shows "td1 = td2"
using assms proof(induct P rule: list.induct)
  case Nil
  then show ?case by auto
next
  case (Cons td \<Theta>')
  consider "td = td1" | "td = td2" | "td \<noteq> td1 \<and> td \<noteq> td2" by auto
  then  show ?case proof(cases)
    case 1
    then show ?thesis using Cons wfTh_elims wfTh_td_eq by metis
  next
    case 2
    then show ?thesis using Cons wfTh_elims wfTh_td_eq by metis
  next
    case 3
    then show ?thesis using Cons wfTh_elims by auto
  qed
qed

lemma wfTs_distinct:
 fixes dclist::"(string * \<tau>) list"
 assumes "\<Theta> ; B  ; GNil \<turnstile>\<^sub>w\<^sub>f  dclist"
 shows "distinct (map fst dclist)"
using assms proof(induct dclist rule: list.induct)
  case Nil
  then show ?case by auto
next
  case (Cons x1 x2)
  then show ?case
      by (metis Cons.hyps Cons.prems distinct.simps(2) fst_conv list.set_map list.simps(9) wfTs_elims(2)) 
qed 

lemma wfTh_dclist_distinct:
  assumes "AF_typedef s dclist \<in> set P" and "wfTh P"
  shows "distinct (map fst  dclist)"
proof - 
  have "wfTD P (AF_typedef s dclist)" using assms lookup_wfTD by auto
  hence "wfTs P {||} GNil dclist" using wfTD_elims by metis
  thus ?thesis using wfTs_distinct by metis
qed

lemma wfTh_dc_t_unique2:
  assumes "AF_typedef s dclist' \<in> set P" and "(dc,tc' ) \<in> set dclist'" and "AF_typedef s dclist \<in> set P" and "wfTh P" and
        "(dc,  tc) \<in> set dclist"
      shows "tc= tc'"
proof - 
  have "dclist = dclist'" using assms wfTh_td_unique name_of_type.simps by force
  moreover have "distinct (map fst  dclist)"  using wfTh_dclist_distinct assms by auto
  ultimately show ?thesis using assms 
    by (meson eq_key_imp_eq_value)
qed

lemma wfTh_dc_t_unique:
  assumes "AF_typedef s dclist' \<in> set P" and "(dc, \<lbrace> x' : b'  | c' \<rbrace> ) \<in> set dclist'" and "AF_typedef s dclist \<in> set P" and "wfTh P" and
        "(dc,  \<lbrace> x : b  | c \<rbrace>) \<in> set dclist"
      shows "\<lbrace> x' : b'  | c' \<rbrace>= \<lbrace> x : b  | c \<rbrace>"
  using assms wfTh_dc_t_unique2 by metis

lemma wfTs_wfT:
  fixes dclist::"(string *\<tau>) list" and t::\<tau>
  assumes "\<Theta>; \<B>; GNil  \<turnstile>\<^sub>w\<^sub>f dclist"  and "(dc,t) \<in> set dclist" 
  shows "\<Theta>; \<B>; GNil  \<turnstile>\<^sub>w\<^sub>f t"
using assms proof(induct dclist rule:list.induct)
  case Nil
  then show ?case by auto
next
  case (Cons x1 x2)
  thus ?case using  wfTs_elims(2)[OF Cons(2)] by auto
qed

lemma wfTh_wfT:
  fixes t::\<tau>
  assumes "wfTh P"  and "AF_typedef tid dclist \<in> set P" and "(dc,t) \<in> set dclist" 
  shows "P ; {||} ; GNil  \<turnstile>\<^sub>w\<^sub>f t"
proof - 
  have "P  \<turnstile>\<^sub>w\<^sub>f AF_typedef tid dclist" using lookup_wfTD assms by auto
  hence "P ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f dclist" using wfTD_elims by auto
  thus ?thesis using wfTs_wfT assms by auto
qed

lemma td_lookup_eq_iff:
  fixes dc :: string and bva1::bv and bva2::bv
  assumes "[[atom bva1]]lst. dclist1 = [[atom bva2]]lst. dclist2" and "(dc, \<lbrace> x : b  | c \<rbrace>) \<in> set dclist1" 
  shows "\<exists>x2 b2 c2. (dc, \<lbrace> x2 : b2  | c2 \<rbrace>) \<in> set dclist2" 
using assms proof(induct dclist1 arbitrary: dclist2)
  case Nil
  then show ?case by auto
next
  case (Cons dct1' dclist1')
  then obtain dct2' and dclist2' where cons:"dct2' # dclist2' = dclist2"   using  lst_head_cons_neq_nil[OF Cons(2)] list.exhaust by metis
  hence *:"[[atom bva1]]lst. dclist1' = [[atom bva2]]lst. dclist2' \<and> [[atom bva1]]lst. dct1' = [[atom bva2]]lst. dct2'" 
    using Cons lst_head_cons Cons cons by metis
  show ?case proof(cases "dc=fst dct1'")
    case True
    hence "dc = fst dct2'" using * lst_fst[ THEN lst_pure ] 
    proof -
      show ?thesis
        by (metis (no_types) "local.*" True \<open>\<And>x2 x1 t2' t2a t2 t1. [[atom x1]]lst. (t1, t2a) = [[atom x2]]lst. (t2, t2') \<Longrightarrow> t1 = t2\<close> prod.exhaust_sel) (* 31 ms *)
    qed    
    obtain x2 b2 and c2 where "snd dct2' = \<lbrace> x2 : b2  | c2 \<rbrace>" using obtain_fresh_z by metis
    hence "(dc, \<lbrace> x2 : b2  | c2 \<rbrace>) = dct2'" using  \<open>dc = fst dct2'\<close> 
      by (metis prod.exhaust_sel)
    then show ?thesis using cons by force
  next
    case False
    hence "(dc, \<lbrace> x : b  | c \<rbrace>) \<in> set dclist1'" using Cons by auto
    then show ?thesis using Cons 
      by (metis "local.*" cons list.set_intros(2))
  qed
qed

lemma lst_t_b_eq_iff:
  fixes bva1::bv and bva2::bv
  assumes "[[atom bva1]]lst. \<lbrace> x1 : b1  | c1 \<rbrace> = [[atom bva2]]lst. \<lbrace> x2 : b2  | c2 \<rbrace>" 
  shows "[[atom bva1]]lst. b1 = [[atom bva2]]lst.b2" 
proof(subst  Abs1_eq_iff_all(3)[of bva1 b1  bva2 b2],rule,rule,rule)
  fix c::bv
  assume "atom c \<sharp> ( \<lbrace> x1 : b1  | c1 \<rbrace> ,  \<lbrace> x2 : b2  | c2 \<rbrace>)" and "atom c \<sharp> (bva1, bva2, b1, b2)"

  show "(bva1 \<leftrightarrow> c) \<bullet> b1 = (bva2 \<leftrightarrow> c) \<bullet> b2" using assms Abs1_eq_iff(3) assms 
    by (metis Abs1_eq_iff_fresh(3) \<open>atom c \<sharp> (bva1, bva2, b1, b2)\<close> \<tau>.fresh \<tau>.perm_simps type_eq_subst_eq2(2))
qed

lemma wfTh_typedef_poly_b_eq_iff:  
  assumes "AF_typedef_poly tyid bva1 dclist1 \<in> set P" and "(dc, \<lbrace> x1 : b1  | c1 \<rbrace>) \<in> set dclist1"
  and "AF_typedef_poly tyid bva2 dclist2 \<in> set P" and "(dc, \<lbrace> x2 : b2  | c2 \<rbrace>) \<in> set dclist2" and "\<turnstile>\<^sub>w\<^sub>f P"
shows "b1[bva1::=b]\<^sub>b\<^sub>b = b2[bva2::=b]\<^sub>b\<^sub>b"
proof - 
  have "[[atom bva1]]lst. dclist1 = [[atom bva2]]lst.dclist2" using assms wfTh_dclist_poly_unique by metis
  hence "[[atom bva1]]lst. (dc,\<lbrace> x1 : b1  | c1 \<rbrace>) = [[atom bva2]]lst. (dc,\<lbrace> x2 : b2  | c2 \<rbrace>)" using wfTh_b_eq_iff assms wfTh_wfTs_poly by metis
  hence "[[atom bva1]]lst. \<lbrace> x1 : b1  | c1 \<rbrace> = [[atom bva2]]lst. \<lbrace> x2 : b2  | c2 \<rbrace>" using lst_snd by metis
  hence "[[atom bva1]]lst. b1 = [[atom bva2]]lst.b2" using lst_t_b_eq_iff by metis
  thus ?thesis using subst_b_flip_eq_two subst_b_b_def by metis
qed

section \<open>Equivariance Lemmas\<close>

lemma x_not_in_u_set[simp]:
  fixes  x::x and us::"u fset"
  shows "atom x \<notin> supp us"
  by(induct us,auto, simp add: supp_finsert supp_at_base)

lemma wfS_flip_eq:
  fixes s1::s and x1::x and s2::s and x2::x  and \<Delta>::\<Delta>
  assumes "[[atom x1]]lst. s1 = [[atom x2]]lst. s2" and "[[atom x1]]lst. t1 = [[atom x2]]lst. t2"  and "[[atom x1]]lst. c1 = [[atom x2]]lst. c2" and "atom x2 \<sharp> \<Gamma>" and
           " \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>"  and
        "\<Theta> ; \<Phi>  ; \<B> ; (x1, b, c1)  #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s1 : b_of t1"
       shows  "\<Theta> ; \<Phi>  ; \<B> ; (x2, b, c2)  #\<^sub>\<Gamma> \<Gamma> ; \<Delta>  \<turnstile>\<^sub>w\<^sub>f s2 : b_of t2"
proof(cases "x1=x2")
  case True
  hence "s1 = s2 \<and> t1 = t2 \<and> c1 = c2" using assms Abs1_eq_iff by metis
  then show ?thesis using assms True by simp
next
  case False
  have "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<and> \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> \<and>  \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>" using wfX_wfY assms by metis
  moreover have "atom x1 \<sharp> \<Gamma>" using wfX_wfY wfG_elims assms by metis
  moreover hence "atom x1 \<sharp> \<Delta> \<and> atom x2 \<sharp> \<Delta> " using wfD_x_fresh assms by auto
  ultimately have " \<Theta> ; \<Phi>  ; \<B> ; (x2 \<leftrightarrow> x1) \<bullet> ((x1, b, c1)  #\<^sub>\<Gamma>  \<Gamma>) ; \<Delta>  \<turnstile>\<^sub>w\<^sub>f (x2 \<leftrightarrow> x1) \<bullet> s1 :  (x2 \<leftrightarrow> x1) \<bullet> b_of t1"
    using wfS.eqvt theta_flip_eq phi_flip_eq assms  flip_base_eq beta_flip_eq flip_fresh_fresh supp_b_empty by metis
  hence   " \<Theta> ; \<Phi>  ; \<B> ;  ((x2, b, (x2 \<leftrightarrow> x1) \<bullet> c1)  #\<^sub>\<Gamma>  ((x2 \<leftrightarrow> x1) \<bullet> \<Gamma>)) ; \<Delta>  \<turnstile>\<^sub>w\<^sub>f (x2 \<leftrightarrow> x1) \<bullet> s1 :   b_of ((x2 \<leftrightarrow> x2) \<bullet> t1)"  by fastforce
  thus ?thesis using assms Abs1_eq_iff 
  proof -
   have f1: "x2 = x1 \<and> t2 = t1 \<or> x2 \<noteq> x1 \<and> t2 = (x2 \<leftrightarrow> x1) \<bullet> t1 \<and> atom x2 \<sharp> t1"
     by (metis (full_types) Abs1_eq_iff(3) \<open>[[atom x1]]lst. t1 = [[atom x2]]lst. t2\<close>) (* 125 ms *)
   then have "x2 \<noteq> x1 \<and> s2 = (x2 \<leftrightarrow> x1) \<bullet> s1 \<and> atom x2 \<sharp> s1 \<longrightarrow> b_of t2 = (x2 \<leftrightarrow> x1) \<bullet> b_of t1"
     by (metis b_of.eqvt) (* 0.0 ms *)
   then show ?thesis
    using f1 by (metis (no_types) Abs1_eq_iff(3) G_cons_flip_fresh3 \<open>[[atom x1]]lst. c1 = [[atom x2]]lst. c2\<close> \<open>[[atom x1]]lst. s1 = [[atom x2]]lst. s2\<close> \<open>\<Theta> ; \<Phi>  ; \<B> ; (x1, b, c1)  #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s1 : b_of t1\<close> \<open>\<Theta> ; \<Phi>  ; \<B> ; (x2 \<leftrightarrow> x1) \<bullet> ((x1, b, c1)  #\<^sub>\<Gamma> \<Gamma>) ; \<Delta> \<turnstile>\<^sub>w\<^sub>f (x2 \<leftrightarrow> x1) \<bullet> s1 : (x2 \<leftrightarrow> x1) \<bullet> b_of t1\<close> \<open>atom x1 \<sharp> \<Gamma>\<close> \<open>atom x2 \<sharp> \<Gamma>\<close>) (* 593 ms *)
  qed
qed

section \<open>Lookup\<close>

lemma wf_not_in_prefix:
  assumes "\<Theta> ; B \<turnstile>\<^sub>w\<^sub>f (\<Gamma>'@(x,b1,c1) #\<^sub>\<Gamma>\<Gamma>)"
  shows "x \<notin> fst ` toSet \<Gamma>'"
using assms proof(induct \<Gamma>' rule: \<Gamma>.induct)
  case GNil
  then show ?case by simp
next
  case (GCons xbc \<Gamma>')
  then obtain x' and b' and c'::c where xbc: "xbc=(x',b',c')" 
    using prod_cases3 by blast
  hence *:"(xbc  #\<^sub>\<Gamma> \<Gamma>') @ (x, b1, c1)  #\<^sub>\<Gamma> \<Gamma> = ((x',b',c') #\<^sub>\<Gamma>(\<Gamma>'@ ((x, b1, c1)  #\<^sub>\<Gamma> \<Gamma>)))" by simp
  hence "atom x' \<sharp> (\<Gamma>'@(x,b1,c1) #\<^sub>\<Gamma>\<Gamma>)" using wfG_elims(2) GCons by metis
    
  moreover have "\<Theta> ; B \<turnstile>\<^sub>w\<^sub>f (\<Gamma>' @ (x, b1, c1)  #\<^sub>\<Gamma> \<Gamma>)" using GCons wfG_elims * by metis
  ultimately have  "atom x' \<notin> atom_dom (\<Gamma>'@(x,b1,c1) #\<^sub>\<Gamma>\<Gamma>)" using wfG_dom_supp GCons append_g.simps xbc fresh_def by fast
  hence "x' \<noteq> x" using GCons fresh_GCons xbc by fastforce
  then show ?case using GCons xbc toSet.simps
    using Un_commute \<open>\<Theta> ; B \<turnstile>\<^sub>w\<^sub>f \<Gamma>' @ (x, b1, c1)  #\<^sub>\<Gamma> \<Gamma>\<close> atom_dom.simps by auto
qed

lemma lookup_inside_wf[simp]:
  assumes "\<Theta> ; B \<turnstile>\<^sub>w\<^sub>f (\<Gamma>'@(x,b1,c1) #\<^sub>\<Gamma>\<Gamma>)"
  shows "Some (b1,c1) = lookup (\<Gamma>'@(x,b1,c1) #\<^sub>\<Gamma>\<Gamma>) x"
  using wf_not_in_prefix lookup_inside assms by fast

lemma lookup_weakening:
  fixes \<Theta>::\<Theta> and \<Gamma>::\<Gamma> and \<Gamma>'::\<Gamma>
  assumes "Some (b,c) = lookup \<Gamma> x" and "toSet \<Gamma> \<subseteq> toSet \<Gamma>'" and "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>'" and "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>"
  shows "Some (b,c) = lookup \<Gamma>' x"
proof -
  have "(x,b,c) \<in> toSet \<Gamma> \<and> (\<forall>b' c'. (x,b',c') \<in> toSet \<Gamma> \<longrightarrow> b'=b \<and> c'=c)" using assms lookup_iff toSet.simps by force
  hence "(x,b,c) \<in> toSet \<Gamma>'" using assms by auto
  moreover have "(\<forall>b' c'. (x,b',c') \<in> toSet \<Gamma>' \<longrightarrow> b'=b \<and> c'=c)" using assms wf_g_unique 
    using calculation by auto
  ultimately show ?thesis using lookup_iff 
    using assms(3) by blast
qed

lemma wfPhi_lookup_fun_unique:
  fixes \<Phi>::\<Phi>
  assumes "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>" and "AF_fundef f fd \<in> set \<Phi>" 
  shows "Some (AF_fundef f fd) = lookup_fun \<Phi> f"
using assms proof(induct \<Phi> rule: list.induct )
  case Nil
  then show ?case using lookup_fun.simps by simp
next
  case (Cons  a  \<Phi>')
  then obtain f' and fd' where a:"a = AF_fundef f' fd'" using fun_def.exhaust by auto  
  have wf: "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>' \<and> f' \<notin> name_of_fun ` set \<Phi>' " using wfPhi_elims Cons a by metis
  then show ?case  using Cons lookup_fun.simps using Cons  lookup_fun.simps wf a 
      by (metis image_eqI name_of_fun.simps set_ConsD)
qed

lemma lookup_fun_weakening:
  fixes \<Phi>'::\<Phi>
  assumes "Some fd = lookup_fun \<Phi> f" and "set \<Phi> \<subseteq> set \<Phi>'" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>'"
  shows "Some fd = lookup_fun \<Phi>' f"
using assms proof(induct \<Phi> )
  case Nil
  then show ?case using lookup_fun.simps by simp
next
  case (Cons  a  \<Phi>'')
  then obtain f' and fd' where a: "a = AF_fundef f' fd'" using fun_def.exhaust by auto
  then show ?case proof(cases "f=f'")
    case True
    then show ?thesis using lookup_fun.simps Cons wfPhi_lookup_fun_unique a 
      by (metis lookup_fun_member subset_iff)
  next
    case False
    then show ?thesis  using lookup_fun.simps Cons 
      using \<open>a = AF_fundef f' fd'\<close> by auto
  qed
qed

lemma  fundef_poly_fresh_bv:
  assumes "atom bv2 \<sharp> (bv1,b1,c1,\<tau>1,s1)"
  shows  * : "(AF_fun_typ_some bv2 (AF_fun_typ x1 ((bv1\<leftrightarrow>bv2) \<bullet> b1) ((bv1\<leftrightarrow>bv2) \<bullet>c1) ((bv1\<leftrightarrow>bv2) \<bullet> \<tau>1) ((bv1\<leftrightarrow>bv2) \<bullet> s1)) = (AF_fun_typ_some bv1 (AF_fun_typ x1 b1 c1 \<tau>1 s1)))" 
        (is "(AF_fun_typ_some ?bv ?fun_typ = AF_fun_typ_some ?bva ?fun_typa)")
proof -
  have 1:"atom bv2 \<notin> set [atom x1]" using bv_not_in_x_atoms by simp
  have 2:"bv1 \<noteq> bv2" using assms by auto
  have 3:"(bv2 \<leftrightarrow> bv1) \<bullet> x1 = x1" using pure_fresh flip_fresh_fresh 
    by (simp add: flip_fresh_fresh)
  have "  AF_fun_typ x1 ((bv1 \<leftrightarrow> bv2) \<bullet> b1) ((bv1 \<leftrightarrow> bv2) \<bullet> c1) ((bv1 \<leftrightarrow> bv2) \<bullet> \<tau>1) ((bv1 \<leftrightarrow> bv2) \<bullet> s1) = (bv2 \<leftrightarrow> bv1) \<bullet> AF_fun_typ x1 b1 c1 \<tau>1 s1"
    using 1 2 3 assms   by (simp add: flip_commute)
  moreover have "(atom bv2 \<sharp> c1 \<and> atom bv2 \<sharp> \<tau>1 \<and> atom bv2 \<sharp> s1 \<or> atom bv2 \<in> set [atom x1])  \<and> atom bv2 \<sharp> b1" 
     using 1 2 3 assms  fresh_prod5 by metis
  ultimately show ?thesis unfolding  fun_typ_q.eq_iff  Abs1_eq_iff(3) fun_typ.fresh 1 2 by fastforce
qed


text \<open>It is possible to collapse some of the easy to prove inductive cases into a single proof at the qed line
   but this makes it fragile under change. For example, changing the lemma statement might make one of the previously
   trivial cases non-trivial and so the collapsing needs to be unpacked. Is there a way to find which case
   has failed in the qed line?\<close>

lemma wb_b_weakening1:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and \<B>::\<B> and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def
          and cs::branch_s and css::branch_list

  shows  "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b \<Longrightarrow> \<B> |\<subseteq>| \<B>' \<Longrightarrow> \<Theta>; \<B>' ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c \<Longrightarrow>\<B> |\<subseteq>| \<B>'  \<Longrightarrow> \<Theta>; \<B>' ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f  c" and
         "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>   \<Longrightarrow>\<B> |\<subseteq>| \<B>'  \<Longrightarrow> \<Theta>; \<B>' \<turnstile>\<^sub>w\<^sub>f \<Gamma> " and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<tau> \<Longrightarrow> \<B> |\<subseteq>| \<B>' \<Longrightarrow>  \<Theta>; \<B>' ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f  \<tau>" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ts  \<Longrightarrow>  \<B> |\<subseteq>| \<B>' \<Longrightarrow> \<Theta>; \<B>' ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ts" and 
         "\<turnstile>\<^sub>w\<^sub>f P \<Longrightarrow> True " and     
         "wfB \<Theta> \<B> b \<Longrightarrow>  \<B> |\<subseteq>| \<B>' \<Longrightarrow> wfB \<Theta> \<B>' b" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ce : b \<Longrightarrow> \<B> |\<subseteq>| \<B>' \<Longrightarrow> \<Theta>; \<B>' ;  \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce : b" and
         "\<Theta>  \<turnstile>\<^sub>w\<^sub>f td \<Longrightarrow> True"
proof(nominal_induct b and c and \<Gamma> and \<tau> and ts and P and b and b and td 
     avoiding:  \<B>'
rule:wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.strong_induct)
  case (wfV_conspI s bv dclist \<Theta> dc x b' c \<B> b \<Gamma> v)
  show ?case proof
    show \<open>AF_typedef_poly s bv dclist \<in> set \<Theta>\<close> using wfV_conspI by metis
    show \<open>(dc, \<lbrace> x : b'  | c \<rbrace>) \<in> set dclist\<close> using wfV_conspI  by auto
    show \<open> \<Theta> ;  \<B>'  \<turnstile>\<^sub>w\<^sub>f b \<close> using wfV_conspI by auto
    show \<open>atom bv \<sharp>  (\<Theta>, \<B>', \<Gamma>, b, v)\<close>  using fresh_prodN wfV_conspI by auto
    thus \<open> \<Theta>; \<B>' ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b'[bv::=b]\<^sub>b\<^sub>b \<close> using wfV_conspI by simp
  qed
next
 case (wfTI z \<Theta> \<B> \<Gamma> b c)
  show ?case proof 
    show "atom z \<sharp>  (\<Theta>, \<B>', \<Gamma>)" using wfTI by auto
    show "\<Theta>; \<B>'  \<turnstile>\<^sub>w\<^sub>f b " using wfTI by auto
    show "\<Theta>; \<B>' ; (z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c " using wfTI by auto
  qed
qed( (auto simp add: wf_intros | metis wf_intros)+ )

lemma wb_b_weakening2:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and \<B>::\<B> and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def
          and cs::branch_s and css::branch_list

  shows 
         "\<Theta>; \<Phi>; \<B>; \<Gamma>  ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b \<Longrightarrow> \<B> |\<subseteq>| \<B>' \<Longrightarrow> \<Theta> ; \<Phi> ; \<B>' ;  \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b" and
         "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<Longrightarrow> \<B> |\<subseteq>| \<B>' \<Longrightarrow> \<Theta> ; \<Phi> ; \<B>' ;  \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b" and
         "\<Theta> ; \<Phi> ; \<B>  ; \<Gamma> ; \<Delta> ; tid ; dc ; t  \<turnstile>\<^sub>w\<^sub>f cs : b \<Longrightarrow> \<B> |\<subseteq>| \<B>' \<Longrightarrow>  \<Theta> ; \<Phi> ; \<B>' ; \<Gamma> ; \<Delta> ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f cs : b" and
         "\<Theta> ; \<Phi> ; \<B>  ; \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b \<Longrightarrow> \<B> |\<subseteq>| \<B>' \<Longrightarrow>  \<Theta> ; \<Phi> ; \<B>' ; \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b" and       
         "\<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) \<Longrightarrow> True" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<Longrightarrow> \<B> |\<subseteq>| \<B>' \<Longrightarrow>  \<Theta>; \<B>' ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f  \<Delta>" and
         "\<Theta> ; \<Phi>   \<turnstile>\<^sub>w\<^sub>f ftq \<Longrightarrow> True" and
         "\<Theta> ; \<Phi>  ; \<B> \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow> \<B> |\<subseteq>| \<B>' \<Longrightarrow> \<Theta> ; \<Phi>  ; \<B>' \<turnstile>\<^sub>w\<^sub>f ft"
proof(nominal_induct b and b and b and b and \<Phi> and \<Delta> and ftq and ft  
   avoiding:  \<B>'
   rule:wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.strong_induct)
  case (wfE_valI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v b)
  then show ?case using wf_intros wb_b_weakening1 by metis
next
  case (wfE_plusI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros  wb_b_weakening1 by metis
next
  case (wfE_leqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros  wb_b_weakening1 by metis
next
  case (wfE_eqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b v2)
  then show ?case  using wf_intros  wb_b_weakening1 
    by meson
next
  case (wfE_fstI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case using Wellformed.wfE_fstI  wb_b_weakening1 by metis
next
  case (wfE_sndI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case using wf_intros  wb_b_weakening1 by metis
next
  case (wfE_concatI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros wb_b_weakening1 by metis
next
  case (wfE_splitI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros wb_b_weakening1 by metis
next
  case (wfE_lenI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1) 
  then show ?case using wf_intros wb_b_weakening1 by metis
next
  case (wfE_appI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> f ft v)
  then show ?case using wf_intros using wb_b_weakening1  by meson
next
  case (wfE_appPI \<Theta> \<Phi> \<B>1 \<Gamma> \<Delta> b' bv1 v1 \<tau>1 f1 x1 b1 c1 s1)

  have "\<Theta> ; \<Phi>  ; \<B>' ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_appP f1 b' v1 : (b_of \<tau>1)[bv1::=b']\<^sub>b" 
  proof
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>" using wfE_appPI by auto
    show "\<Theta>; \<B>' ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> "  using wfE_appPI by auto
    show "\<Theta>; \<B>'  \<turnstile>\<^sub>w\<^sub>f b' "  using wfE_appPI wb_b_weakening1 by auto
    thus " atom bv1 \<sharp> (\<Phi>, \<Theta>, \<B>', \<Gamma>, \<Delta>, b', v1, (b_of \<tau>1)[bv1::=b']\<^sub>b)"  
      using  wfE_appPI fresh_prodN by auto

    show "Some (AF_fundef f1 (AF_fun_typ_some bv1 (AF_fun_typ x1 b1 c1 \<tau>1 s1))) = lookup_fun \<Phi> f1"  using wfE_appPI by auto
    show "\<Theta>; \<B>' ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : b1[bv1::=b']\<^sub>b "  using wfE_appPI wb_b_weakening1 by auto
  qed
  then show ?case by auto
next
  case (wfE_mvarI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> u \<tau>)
  then show ?case using wf_intros wb_b_weakening1 by metis
next
  case (wfS_valI \<Theta> \<Phi> \<B> \<Gamma> v b \<Delta>)
  then show ?case using wf_intros wb_b_weakening1 by metis
next
  case (wfS_letI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e b' x s b)
  show ?case proof
    show \<open> \<Theta> ; \<Phi>  ; \<B>' ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b' \<close> using wfS_letI by auto
    show \<open> \<Theta> ; \<Phi>  ; \<B>' ; (x, b', TRUE)  #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<close> using wfS_letI by auto
    show \<open> \<Theta>; \<B>' ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfS_letI by auto
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>, \<B>', \<Gamma>, \<Delta>, e, b)\<close> using wfS_letI by auto
  qed
next
  case (wfS_let2I \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 \<tau> x s2 b)
  then show ?case using wb_b_weakening1 Wellformed.wfS_let2I by simp
next
  case (wfS_ifI \<Theta> \<B> \<Gamma> v \<Phi> \<Delta> s1 b s2)
  then show ?case using  wb_b_weakening1 Wellformed.wfS_ifI by simp
next
  case (wfS_varI \<Theta> \<B> \<Gamma> \<tau> v u \<Delta> \<Phi> s b)
  then show ?case using wb_b_weakening1 Wellformed.wfS_varI by simp
next
  case (wfS_assignI u \<tau> \<Delta> \<Theta> \<B> \<Gamma> \<Phi> v)
  then show ?case using wb_b_weakening1 Wellformed.wfS_assignI by simp
next
case (wfS_whileI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 s2 b)
  then show ?case using wb_b_weakening1 Wellformed.wfS_whileI by simp
next
  case (wfS_seqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 s2 b)
  then show ?case using Wellformed.wfS_seqI   by metis
next
  case (wfS_matchI \<Theta> \<B> \<Gamma> v tid dclist \<Delta> \<Phi> cs b)
  then show ?case using  wb_b_weakening1 Wellformed.wfS_matchI by metis
next
  case (wfS_branchI \<Theta> \<Phi> \<B> x \<tau> \<Gamma> \<Delta> s b tid dc)
  then show ?case  using Wellformed.wfS_branchI by auto
next
  case (wfS_finalI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist' cs b dclist)
  then show ?case  using wf_intros by metis
next
  case (wfS_cons \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist' cs b css dclist)
  then show ?case  using wf_intros by metis
next
  case (wfD_emptyI \<Theta> \<B> \<Gamma>)
  then show ?case using wf_intros wb_b_weakening1 by metis
next
  case (wfD_cons \<Theta> \<B> \<Gamma> \<Delta> \<tau> u)
  then show ?case using wf_intros wb_b_weakening1 by metis
next
  case (wfPhi_emptyI \<Theta>)
  then show ?case using wf_intros wb_b_weakening1 by metis
next
  case (wfPhi_consI f \<Theta> \<Phi> ft)
  then show ?case using wf_intros wb_b_weakening1 by metis
next
  case (wfFTSome \<Theta> bv ft)
  then show ?case  using wf_intros wb_b_weakening1 by metis
next
  case (wfFTI \<Theta> B b s x c \<tau> \<Phi>)
  show ?case proof
    show "\<Theta>; \<B>'  \<turnstile>\<^sub>w\<^sub>f b"   using wfFTI wb_b_weakening1 by auto
    
    show "supp c \<subseteq> {atom x}" using wfFTI wb_b_weakening1 by auto
    show "\<Theta>; \<B>' ; (x, b, c) #\<^sub>\<Gamma> GNil   \<turnstile>\<^sub>w\<^sub>f \<tau> " using wfFTI wb_b_weakening1 by auto
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " using wfFTI wb_b_weakening1 by auto
    from \<open> B |\<subseteq>| \<B>'\<close> have "supp B \<subseteq> supp \<B>'" proof(induct B)
      case empty
      then show ?case by auto
    next
      case (insert x B)
      then show ?case 
        by (metis fsubset_funion_eq subset_Un_eq supp_union_fset)
    qed
    thus  "supp s \<subseteq> {atom x} \<union> supp \<B>'" using wfFTI by auto
  qed  
next
  case (wfS_assertI \<Theta> \<Phi> \<B> x c \<Gamma> \<Delta> s b)
  show ?case proof
    show \<open> \<Theta> ; \<Phi> ; \<B>' ; (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<close> using wb_b_weakening1 wfS_assertI by simp
    show \<open> \<Theta>; \<B>' ; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c \<close>  using wb_b_weakening1 wfS_assertI by simp
    show \<open> \<Theta>; \<B>' ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wb_b_weakening1 wfS_assertI by simp
    have "atom x \<sharp>  \<B>'" using x_not_in_b_set fresh_def by metis
    thus  \<open>atom x \<sharp> (\<Phi>, \<Theta>, \<B>', \<Gamma>, \<Delta>, c, b, s)\<close> using wfS_assertI fresh_prodN by simp
  qed   
qed(auto)

lemmas wb_b_weakening = wb_b_weakening1 wb_b_weakening2

lemma wfG_b_weakening:
  fixes \<Gamma>::\<Gamma>
  assumes "\<B> |\<subseteq>| \<B>'" and "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>"
  shows "\<Theta>; \<B>'  \<turnstile>\<^sub>w\<^sub>f \<Gamma> "
  using wb_b_weakening assms by auto

lemma wfT_b_weakening:
  fixes \<Gamma>::\<Gamma> and \<Theta>::\<Theta> and \<tau>::\<tau>
  assumes "\<B> |\<subseteq>| \<B>'" and "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<tau>"
  shows "\<Theta>; \<B>' ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<tau> "
  using wb_b_weakening assms by auto

lemma wfB_subst_wfB:
  fixes \<tau>::\<tau> and b'::b and b::b
  assumes "\<Theta> ; {|bv|}  \<turnstile>\<^sub>w\<^sub>f b" and "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b'"
  shows "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b[bv::=b']\<^sub>b\<^sub>b "
using assms proof(nominal_induct b rule:b.strong_induct)
  case B_int
  hence  "\<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f B_int" using wfB_intI wfX_wfY by fast
  then show ?case using subst_bb.simps wb_b_weakening by fastforce
next
  case B_bool
  hence  "\<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f B_bool" using wfB_boolI wfX_wfY by fast
  then show ?case using subst_bb.simps wb_b_weakening by fastforce
next
  case (B_id x )
  hence " \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f (B_id x)" using wfB_consI wfB_elims wfX_wfY by metis
  then show ?case using  subst_bb.simps(4) by auto
next
  case (B_pair x1 x2)
  then show ?case using subst_bb.simps 
    by (metis wfB_elims(1) wfB_pairI)
next
  case B_unit
  hence  "\<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f B_unit" using wfB_unitI wfX_wfY by fast
  then show ?case using subst_bb.simps wb_b_weakening by fastforce
next
  case B_bitvec
  hence  "\<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f B_bitvec" using wfB_bitvecI wfX_wfY by fast
  then show ?case using subst_bb.simps wb_b_weakening by fastforce
next
  case (B_var x)
  then show ?case 
  proof -
    have False
      using B_var.prems(1) wfB.cases by fastforce (* 781 ms *)
    then show ?thesis  by metis 
  qed
next
  case (B_app s b)
  then obtain bv' dclist where *:"AF_typedef_poly s bv' dclist \<in> set \<Theta> \<and> \<Theta> ; {|bv|}   \<turnstile>\<^sub>w\<^sub>f b" using wfB_elims by metis
  show ?case unfolding subst_b_simps proof
    show "\<turnstile>\<^sub>w\<^sub>f \<Theta> " using B_app wfX_wfY by metis
    show "\<Theta> ;   \<B>  \<turnstile>\<^sub>w\<^sub>f b[bv::=b']\<^sub>b\<^sub>b " using * B_app forget_subst wfB_supp fresh_def 
      by (metis ex_in_conv subset_empty subst_b_b_def supp_empty_fset)
    show "AF_typedef_poly s bv' dclist \<in> set \<Theta>" using * by auto
  qed
qed

lemma wfT_subst_wfB:
  fixes \<tau>::\<tau> and b'::b
  assumes "\<Theta> ; {|bv|} ; (x, b, c)  #\<^sub>\<Gamma> GNil   \<turnstile>\<^sub>w\<^sub>f \<tau>" and "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b'"
  shows "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f (b_of \<tau>)[bv::=b']\<^sub>b\<^sub>b "
proof -
  obtain b where  "\<Theta> ; {|bv|} \<turnstile>\<^sub>w\<^sub>f b \<and> b_of \<tau> = b" using wfT_elims b_of.simps assms by metis
  thus ?thesis using wfB_subst_wfB assms by auto
qed

lemma wfG_cons_unique:
  assumes "(x1,b1,c1) \<in> toSet (((x,b,c) #\<^sub>\<Gamma>\<Gamma>))" and "wfG \<Theta> \<B> (((x,b,c) #\<^sub>\<Gamma>\<Gamma>))" and "x = x1"
  shows "b1 = b \<and> c1 = c" 
proof -
  have "x1 \<notin> fst ` toSet \<Gamma>" 
  proof -
    have "atom x1 \<sharp> \<Gamma>" using assms wfG_cons by metis
    then show ?thesis
      using fresh_gamma_elem 
      by (metis assms(2) atom_dom.simps dom.simps rev_image_eqI wfG_cons2 wfG_x_fresh)
  qed
  thus ?thesis using assms by force
qed

lemma wfG_member_unique:
  assumes "(x1,b1,c1) \<in> toSet (\<Gamma>'@((x,b,c) #\<^sub>\<Gamma>\<Gamma>))" and "wfG \<Theta> \<B> (\<Gamma>'@((x,b,c) #\<^sub>\<Gamma>\<Gamma>))" and "x = x1"
  shows "b1 = b \<and> c1 = c" 
  using assms proof(induct \<Gamma>' rule: \<Gamma>_induct)
  case GNil
  then show ?case using wfG_suffix wfG_cons_unique append_g.simps by metis
next
  case (GCons x' b' c' \<Gamma>')
  moreover hence "(x1, b1, c1) \<in> toSet (\<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>)" using wf_not_in_prefix by fastforce
  ultimately show ?case using wfG_cons by fastforce
qed

section \<open>Function Definitions\<close>

lemma wb_phi_weakening:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and \<B>::\<B> and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def
         and cs::branch_s and css::branch_list and \<Phi>::\<Phi>
  shows
         "\<Theta>; \<Phi>; \<B>; \<Gamma>  ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b \<Longrightarrow> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>' \<Longrightarrow> set \<Phi>  \<subseteq> set \<Phi>' \<Longrightarrow> \<Theta> ; \<Phi>' ; \<B> ;  \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b" and
         "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b  \<Longrightarrow> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>' \<Longrightarrow> set \<Phi>  \<subseteq> set \<Phi>' \<Longrightarrow> \<Theta> ; \<Phi>' ; \<B> ;  \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b" and
         "\<Theta> ; \<Phi> ; \<B>  ; \<Gamma> ; \<Delta> ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f cs : b \<Longrightarrow> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>' \<Longrightarrow> set \<Phi>  \<subseteq> set \<Phi>' \<Longrightarrow>   \<Theta> ; \<Phi>' ; \<B> ; \<Gamma> ; \<Delta> ; tid ; dc ; t  \<turnstile>\<^sub>w\<^sub>f cs : b" and
         "\<Theta> ; \<Phi> ; \<B>  ; \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b \<Longrightarrow> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>' \<Longrightarrow> set \<Phi>  \<subseteq> set \<Phi>' \<Longrightarrow>  \<Theta> ; \<Phi>' ; \<B> ; \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b" and      
         "\<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) \<Longrightarrow> True" and
          "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<Longrightarrow> True" and       
          "\<Theta> ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f ftq \<Longrightarrow> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>' \<Longrightarrow> set \<Phi>  \<subseteq> set \<Phi>' \<Longrightarrow> \<Theta> ; \<Phi>'  \<turnstile>\<^sub>w\<^sub>f ftq" and
         "\<Theta> ; \<Phi> ; \<B> \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow>  \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>' \<Longrightarrow> set \<Phi>  \<subseteq> set \<Phi>' \<Longrightarrow> \<Theta> ; \<Phi>' ; \<B> \<turnstile>\<^sub>w\<^sub>f ft"      
proof(nominal_induct
          b and b and b and b and \<Phi> and \<Delta> and  ftq and ft 
          avoiding:  \<Phi>'         
       rule:wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.strong_induct)
  case (wfE_valI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v b)
  then show ?case using wf_intros by metis
next
  case (wfE_plusI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros by metis
next
  case (wfE_leqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros by metis
next
  case (wfE_eqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b v2)
  then show ?case using wf_intros by metis
next
  case (wfE_fstI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case using wf_intros by metis
next
  case (wfE_sndI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case using wf_intros by metis
next
  case (wfE_concatI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros by metis
next
  case (wfE_splitI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros by metis
next
  case (wfE_lenI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1)
  then show ?case using wf_intros by metis
next
  case (wfE_appI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> f x b c \<tau> s v)
  then show ?case using wf_intros lookup_fun_weakening by metis
next
  case (wfE_appPI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> b' bv v \<tau> f x b c s)
  show ?case proof
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>' \<close> using wfE_appPI by auto
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfE_appPI by auto
    show \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b' \<close> using wfE_appPI by auto
    show \<open>atom bv \<sharp> (\<Phi>', \<Theta>, \<B>, \<Gamma>, \<Delta>, b', v, (b_of \<tau>)[bv::=b']\<^sub>b)\<close> using wfE_appPI by auto
    show \<open>Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi>' f\<close> 
      using wfE_appPI lookup_fun_weakening by metis
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b[bv::=b']\<^sub>b \<close> using wfE_appPI by auto
  qed
next
  case (wfE_mvarI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> u \<tau>)
  then show ?case using wf_intros by metis
next
  case (wfS_valI \<Theta> \<Phi> \<B> \<Gamma> v b \<Delta>)
  then show ?case using wf_intros by metis
next
  case (wfS_letI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e b' x s b)
  then show ?case using Wellformed.wfS_letI by fastforce
next
  case (wfS_let2I \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 b' x s2 b)
  then show ?case   using Wellformed.wfS_let2I by fastforce
next
  case (wfS_ifI \<Theta> \<B> \<Gamma> v \<Phi> \<Delta> s1 b s2)
  then show ?case  using wf_intros by metis
next
  case (wfS_varI \<Theta> \<B> \<Gamma> \<tau> v u \<Phi> \<Delta> b s)
  show ?case proof
    show \<open> \<Theta>; \<B>; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<tau> \<close> using wfS_varI by simp
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b_of \<tau> \<close> using wfS_varI by simp
    show \<open>atom u \<sharp> (\<Phi>', \<Theta>, \<B>, \<Gamma>, \<Delta>, \<tau>, v, b)\<close> using wfS_varI by simp
    show \<open> \<Theta> ; \<Phi>' ; \<B> ; \<Gamma> ; (u, \<tau>)  #\<^sub>\<Delta> \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<close> using wfS_varI by simp
  qed
next
  case (wfS_assignI u \<tau> \<Delta> \<Theta> \<B> \<Gamma> \<Phi> v)
  then show ?case  using wf_intros by metis
next
  case (wfS_whileI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 s2 b)
  then show ?case  using wf_intros by metis
next
  case (wfS_seqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 s2 b)
  then show ?case  using wf_intros by metis
next
  case (wfS_matchI \<Theta> \<B> \<Gamma> v tid dclist \<Delta> \<Phi> cs b)
  then show ?case  using wf_intros by metis
next
  case (wfS_branchI \<Theta> \<Phi> \<B> x \<tau> \<Gamma> \<Delta> s b tid dc)
  then show ?case using Wellformed.wfS_branchI by fastforce
next
  case (wfS_assertI \<Theta> \<Phi> \<B> x c \<Gamma> \<Delta> s b)
  show ?case proof
    show \<open> \<Theta> ; \<Phi>' ; \<B> ; (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<close>  using wfS_assertI by auto
  next
    show \<open> \<Theta>; \<B>; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c \<close> using wfS_assertI by auto
  next
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close>  using wfS_assertI by auto
    have "atom x \<sharp> \<Phi>'" using wfS_assertI wfPhi_supp fresh_def by blast
    thus  \<open>atom x \<sharp> (\<Phi>', \<Theta>, \<B>, \<Gamma>, \<Delta>, c, b, s)\<close>  using fresh_prodN wfS_assertI wfPhi_supp fresh_def by auto
  qed
next
  case (wfFTI \<Theta> B b s x c \<tau> \<Phi>)
  show ?case proof
    show \<open> \<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f b \<close>  using wfFTI by auto
  next
    show \<open>supp c \<subseteq> {atom x}\<close> using wfFTI by auto
  next
    show \<open> \<Theta> ; B ; (x, b, c) #\<^sub>\<Gamma> GNil   \<turnstile>\<^sub>w\<^sub>f \<tau> \<close> using wfFTI by auto
  next
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>' \<close> using wfFTI by auto
  next
    show \<open>supp s \<subseteq> {atom x} \<union> supp B\<close> using wfFTI by auto
  qed
qed(auto|metis wf_intros)+


lemma wfT_fun_return_t:
  fixes \<tau>a'::\<tau> and \<tau>'::\<tau>
  assumes "\<Theta>; \<B>; (xa, b, ca)  #\<^sub>\<Gamma> GNil  \<turnstile>\<^sub>w\<^sub>f \<tau>a'" and "(AF_fun_typ x b c \<tau>' s') = (AF_fun_typ xa b ca \<tau>a' sa')"
  shows  "\<Theta>; \<B>; (x, b, c)  #\<^sub>\<Gamma> GNil  \<turnstile>\<^sub>w\<^sub>f \<tau>'"
proof - 
  obtain cb::x where xf: "atom cb  \<sharp> (c, \<tau>', s', sa', \<tau>a', ca, x , xa)" using obtain_fresh by blast
  hence  "atom cb \<sharp> (c, \<tau>', s', sa', \<tau>a', ca) \<and>  atom cb \<sharp> (x, xa, ((c, \<tau>'), s'), (ca, \<tau>a'), sa')" using  fresh_prod6 fresh_prod4 fresh_prod8 by auto
  hence *:"c[x::=V_var cb]\<^sub>c\<^sub>v = ca[xa::=V_var cb]\<^sub>c\<^sub>v \<and> \<tau>'[x::=V_var cb]\<^sub>\<tau>\<^sub>v = \<tau>a'[xa::=V_var cb]\<^sub>\<tau>\<^sub>v" using assms \<tau>.eq_iff Abs1_eq_iff_all by auto

  have **: "\<Theta>; \<B>; (xa \<leftrightarrow> cb ) \<bullet> ((xa, b, ca)  #\<^sub>\<Gamma> GNil)  \<turnstile>\<^sub>w\<^sub>f (xa \<leftrightarrow> cb ) \<bullet> \<tau>a'" using assms True_eqvt beta_flip_eq theta_flip_eq wfG_wf 
    by (metis GCons_eqvt GNil_eqvt wfT.eqvt wfT_wf)

  have "\<Theta>; \<B>; (x \<leftrightarrow> cb ) \<bullet> ((x, b, c)  #\<^sub>\<Gamma> GNil)  \<turnstile>\<^sub>w\<^sub>f (x \<leftrightarrow> cb ) \<bullet> \<tau>'" proof -
    have "(xa \<leftrightarrow> cb ) \<bullet> xa = (x \<leftrightarrow> cb ) \<bullet> x"  using xf by auto
    hence "(x \<leftrightarrow> cb ) \<bullet> ((x, b, c)  #\<^sub>\<Gamma> GNil) = (xa \<leftrightarrow> cb ) \<bullet> ((xa, b, ca)  #\<^sub>\<Gamma> GNil)"  using * ** xf G_cons_flip fresh_GNil by simp
    thus ?thesis using ** * xf by simp
  qed
  thus ?thesis  using  beta_flip_eq theta_flip_eq  wfT_wf wfG_wf  * ** True_eqvt wfT.eqvt permute_flip_cancel by metis
qed

lemma wfFT_wf_aux:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q and s::s and \<Delta>::\<Delta>
  assumes "\<Theta> ; \<Phi>  ; B \<turnstile>\<^sub>w\<^sub>f (AF_fun_typ x b c \<tau> s)" 
  shows "\<Theta> ; B ; (x,b,c) #\<^sub>\<Gamma> GNil \<turnstile>\<^sub>w\<^sub>f \<tau> \<and> \<Theta>  \<turnstile>\<^sub>w\<^sub>f  \<Phi> \<and> supp s \<subseteq> { atom x } \<union> supp B"
proof -
  obtain xa and ca and sa and \<tau>' where *:"\<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f b  \<and>  (\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>  )  \<and>
    supp sa \<subseteq> {atom xa} \<union> supp B \<and>  (\<Theta> ; B ; (xa, b, ca)  #\<^sub>\<Gamma> GNil   \<turnstile>\<^sub>w\<^sub>f \<tau>')  \<and>  
  AF_fun_typ x b c \<tau> s = AF_fun_typ xa b ca \<tau>' sa " 
    using wfFT.simps[of \<Theta> \<Phi> B "AF_fun_typ x b c \<tau> s"] assms by auto
 
  moreover hence **: "(AF_fun_typ x b c \<tau> s) = (AF_fun_typ xa b ca \<tau>' sa)" by simp
  ultimately have "\<Theta> ; B ; (x,b,c) #\<^sub>\<Gamma>GNil \<turnstile>\<^sub>w\<^sub>f \<tau>"  using wfT_fun_return_t by metis
  moreover have " (\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>  ) "  using * by auto
  moreover have "supp s \<subseteq> { atom x } \<union> supp B" proof -
    have "[[atom x]]lst.s = [[atom xa]]lst.sa" using ** fun_typ.eq_iff lst_fst lst_snd by metis
    thus ?thesis using lst_supp_subset * by metis
  qed
  ultimately show ?thesis by auto
qed

lemma wfFT_simple_wf:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q and s::s and \<Delta>::\<Delta>
  assumes "\<Theta> ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f (AF_fun_typ_none (AF_fun_typ x b c \<tau> s))" 
  shows "\<Theta> ; {||} ; (x,b,c) #\<^sub>\<Gamma>GNil \<turnstile>\<^sub>w\<^sub>f \<tau> \<and> \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> \<and> supp s \<subseteq> { atom x } "
proof -
  have  *:"\<Theta> ; \<Phi>  ; {||} \<turnstile>\<^sub>w\<^sub>f (AF_fun_typ x b c \<tau> s)" using wfFTQ_elims assms by auto
  thus ?thesis using wfFT_wf_aux by force
qed

lemma wfFT_poly_wf:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ftq :: fun_typ_q and s::s and \<Delta>::\<Delta>
  assumes "\<Theta> ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))" 
  shows "\<Theta> ; {|bv|} ; (x,b,c) #\<^sub>\<Gamma>GNil \<turnstile>\<^sub>w\<^sub>f \<tau> \<and> \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> \<and> \<Theta> ; \<Phi>  ; {|bv|}  \<turnstile>\<^sub>w\<^sub>f (AF_fun_typ x b c \<tau> s)"
proof -
  obtain bv1 ft1 where  *:"\<Theta> ; \<Phi>  ; {|bv1|} \<turnstile>\<^sub>w\<^sub>f ft1 \<and> [[atom bv1]]lst. ft1 = [[atom bv]]lst. AF_fun_typ x b c \<tau> s" 
    using wfFTQ_elims(3)[OF assms]  by metis

  show ?thesis proof(cases "bv1 = bv")
    case True
    then show ?thesis using *  fun_typ_q.eq_iff  Abs1_eq_iff   by (metis (no_types, hide_lams) wfFT_wf_aux)
  next
    case False
    obtain x1 b1 c1 t1 s1 where **: "ft1 = AF_fun_typ x1 b1 c1 t1 s1" using fun_typ.eq_iff 
      by (meson fun_typ.exhaust)

    hence eqv: "(bv \<leftrightarrow> bv1) \<bullet>  AF_fun_typ x1 b1 c1 t1 s1 = AF_fun_typ x b c \<tau> s \<and> atom bv1 \<sharp> AF_fun_typ x b c \<tau> s" using 
         Abs1_eq_iff(3) * False by metis

    have "(bv \<leftrightarrow> bv1) \<bullet> \<Theta> ; (bv \<leftrightarrow> bv1) \<bullet> \<Phi> ; (bv \<leftrightarrow> bv1) \<bullet> {|bv1|} \<turnstile>\<^sub>w\<^sub>f (bv \<leftrightarrow> bv1) \<bullet> ft1" using wfFT.eqvt * by metis   
    moreover have "(bv \<leftrightarrow> bv1) \<bullet> \<Phi> = \<Phi>" using phi_flip_eq wfX_wfY * by metis
    moreover have "(bv \<leftrightarrow> bv1) \<bullet> \<Theta> =\<Theta>" using wfX_wfY *  theta_flip_eq2 by metis
    moreover have "(bv \<leftrightarrow> bv1) \<bullet> ft1 = AF_fun_typ x b c \<tau> s" using eqv ** by metis
    ultimately have  "\<Theta> ; \<Phi>  ; {|bv|} \<turnstile>\<^sub>w\<^sub>f AF_fun_typ x b c \<tau> s"  by auto
    thus ?thesis using wfFT_wf_aux by auto
  qed
qed

lemma wfFT_poly_wfT:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q
  assumes "\<Theta> ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))"
  shows "\<Theta> ; {| bv |} ; (x,b,c) #\<^sub>\<Gamma>GNil \<turnstile>\<^sub>w\<^sub>f \<tau>"
  using wfFT_poly_wf assms by simp

lemma b_of_supp:
  "supp (b_of t) \<subseteq> supp t"
proof(nominal_induct t rule:\<tau>.strong_induct)
  case (T_refined_type x b c)
  then show ?case by auto
qed

lemma wfPhi_f_simple_wf:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q and s::s and \<Phi>'::\<Phi>
   assumes "AF_fundef f  (AF_fun_typ_none (AF_fun_typ x b c \<tau> s)) \<in> set \<Phi> " and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>" and "set \<Phi> \<subseteq> set \<Phi>'" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>'"
  shows "\<Theta> ; {||} ; (x,b,c) #\<^sub>\<Gamma> GNil \<turnstile>\<^sub>w\<^sub>f \<tau> \<and> \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> \<and> supp s \<subseteq> { atom x }"
using assms proof(induct \<Phi> rule: \<Phi>_induct)
  case PNil
  then show ?case by auto
next
  case (PConsSome f1 bv x1 b1 c1 \<tau>1 s' \<Phi>'')
  hence "AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c \<tau> s)) \<in> set \<Phi>''" by auto
  moreover have " \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>'' \<and> set \<Phi>'' \<subseteq> set \<Phi>'" using wfPhi_elims(3) PConsSome by auto
  ultimately show  ?case using PConsSome wfPhi_elims wfFT_simple_wf by auto
next
  case (PConsNone f' x' b' c' \<tau>' s' \<Phi>'')
  show ?case proof(cases "f=f'")
    case True
    have "AF_fun_typ_none (AF_fun_typ x' b' c' \<tau>' s') = AF_fun_typ_none (AF_fun_typ x b c \<tau> s)" 
      by (metis PConsNone.prems(1) PConsNone.prems(2) True fun_def.eq_iff image_eqI name_of_fun.simps set_ConsD wfPhi_elims(2))
    hence *:"\<Theta> ; \<Phi>'' \<turnstile>\<^sub>w\<^sub>f AF_fun_typ_none (AF_fun_typ x b c \<tau> s) " using wfPhi_elims(2)[OF PConsNone(3)] by metis
    hence "\<Theta> ; \<Phi>'' ; {||} \<turnstile>\<^sub>w\<^sub>f (AF_fun_typ x b c \<tau> s)" using wfFTQ_elims(1) by metis
    thus ?thesis using wfFT_simple_wf[OF *] wb_phi_weakening PConsNone by force
  next
    case False
    hence "AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c \<tau> s)) \<in> set \<Phi>''" using PConsNone by simp
    moreover have " \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>'' \<and> set \<Phi>'' \<subseteq> set \<Phi>'" using wfPhi_elims(3) PConsNone by auto
    ultimately show  ?thesis using PConsNone wfPhi_elims wfFT_simple_wf by auto
  qed
qed

lemma wfPhi_f_simple_wfT:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q
  assumes "Some (AF_fundef f  (AF_fun_typ_none (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>"
  shows "\<Theta> ; {||} ; (x,b,c) #\<^sub>\<Gamma>GNil \<turnstile>\<^sub>w\<^sub>f \<tau>"
  using wfPhi_f_simple_wf assms  using lookup_fun_member by blast

lemma  wfPhi_f_simple_supp_b:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q
  assumes "Some (AF_fundef f  (AF_fun_typ_none (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>"
  shows "supp b = {}"
proof -
  have "\<Theta> ; {||} ; (x,b,c) #\<^sub>\<Gamma>GNil \<turnstile>\<^sub>w\<^sub>f \<tau>" using wfPhi_f_simple_wfT assms by auto
  thus ?thesis using wfT_wf wfG_cons wfB_supp by fastforce
qed

lemma wfPhi_f_simple_supp_t:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q
  assumes "Some (AF_fundef f  (AF_fun_typ_none (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>"
  shows "supp \<tau> \<subseteq> { atom x }"
  using wfPhi_f_simple_wfT wfT_supp assms by fastforce

lemma  wfPhi_f_simple_supp_c:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q
  assumes "Some (AF_fundef f  (AF_fun_typ_none (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>"
  shows "supp c \<subseteq> { atom x }"
proof -
  have "\<Theta> ; {||} ; (x,b,c) #\<^sub>\<Gamma>GNil \<turnstile>\<^sub>w\<^sub>f \<tau>" using wfPhi_f_simple_wfT assms by auto
  thus ?thesis using wfG_wfC wfC_supp wfT_wf by fastforce
qed

lemma  wfPhi_f_simple_supp_s:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q
  assumes "Some (AF_fundef f  (AF_fun_typ_none (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>"
  shows "supp s \<subseteq> {atom x}"
proof -
  have "AF_fundef f  (AF_fun_typ_none (AF_fun_typ x b c \<tau> s)) \<in> set \<Phi>" using lookup_fun_member assms by auto
  hence "supp s \<subseteq> { atom x }" using wfPhi_f_simple_wf assms by blast
  thus ?thesis using wf_supp(3)  atom_dom.simps toSet.simps  x_not_in_u_set x_not_in_b_set setD.simps 
    using wf_supp2(2) by fastforce
qed

lemma wfPhi_f_poly_wf:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q and s::s and \<Phi>'::\<Phi>
   assumes "AF_fundef f  (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s)) \<in> set \<Phi> " and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>" and "set \<Phi> \<subseteq> set \<Phi>'" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>'"
  shows "\<Theta> ; {|bv|} ; (x,b,c) #\<^sub>\<Gamma>GNil \<turnstile>\<^sub>w\<^sub>f \<tau> \<and> \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>' \<and> \<Theta> ; \<Phi>' ;  {|bv|} \<turnstile>\<^sub>w\<^sub>f  (AF_fun_typ x b c \<tau> s)"
using assms proof(induct \<Phi> rule: \<Phi>_induct)
  case PNil
  then show ?case by auto
next
  case (PConsNone f x b c \<tau> s' \<Phi>'')
  moreover have " \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>'' \<and> set \<Phi>'' \<subseteq> set \<Phi>'" using wfPhi_elims(3) PConsNone by auto
  ultimately show  ?case using PConsNone wfPhi_elims wfFT_poly_wf by auto
next
  case (PConsSome f1 bv1 x1 b1 c1 \<tau>1 s1 \<Phi>'')
  show ?case proof(cases "f=f1")
  case True
    have "AF_fun_typ_some bv1 (AF_fun_typ x1 b1 c1 \<tau>1 s1) = AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s)"       
      by (metis PConsSome.prems(1) PConsSome.prems(2) True fun_def.eq_iff list.set_intros(1) option.inject wfPhi_lookup_fun_unique)
    hence *:"\<Theta> ; \<Phi>''  \<turnstile>\<^sub>w\<^sub>f AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s) " using wfPhi_elims PConsSome by metis  
    thus ?thesis using wfFT_poly_wf * wb_phi_weakening PConsSome 
      by (meson set_subset_Cons)
  next
    case False
    hence "AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s)) \<in> set \<Phi>''" using PConsSome 
      by (meson fun_def.eq_iff set_ConsD)
    moreover have " \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>'' \<and> set \<Phi>'' \<subseteq> set \<Phi>'" using wfPhi_elims(3) PConsSome 
      by (meson dual_order.trans set_subset_Cons)
    ultimately show  ?thesis using PConsSome wfPhi_elims wfFT_poly_wf 
      by blast
  qed
qed

lemma wfPhi_f_poly_wfT:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q
  assumes "Some (AF_fundef f  (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>"
  shows "\<Theta> ; {| bv |} ; (x,b,c) #\<^sub>\<Gamma>GNil \<turnstile>\<^sub>w\<^sub>f \<tau>"
using assms proof(induct \<Phi> rule: \<Phi>_induct)
  case PNil
  then show ?case by auto
next
  case (PConsSome f1 bv1 x1 b1 c1 \<tau>1 s' \<Phi>')
  then show ?case proof(cases "f1=f")
    case True
    hence "lookup_fun (AF_fundef f1 (AF_fun_typ_some bv1 (AF_fun_typ x1 b1 c1 \<tau>1 s'))  # \<Phi>') f = Some (AF_fundef f1 (AF_fun_typ_some bv1 (AF_fun_typ x1 b1 c1 \<tau>1 s')))" using 
       lookup_fun.simps  using PConsSome.prems by simp
    then show ?thesis using PConsSome.prems wfPhi_elims wfFT_poly_wfT
      by (metis option.inject)
  next
    case False
    then show ?thesis using PConsSome using lookup_fun.simps 
      using wfPhi_elims(3) by auto
  qed
next
  case (PConsNone f' x' b' c' \<tau>' s' \<Phi>')
  then show ?case proof(cases "f'=f")
    case True
    then have *:"\<Theta> ; \<Phi>' \<turnstile>\<^sub>w\<^sub>f AF_fun_typ_none (AF_fun_typ x' b' c' \<tau>' s') " using lookup_fun.simps PConsNone wfPhi_elims by metis
    thus ?thesis using PConsNone wfFT_poly_wfT wfPhi_elims lookup_fun.simps 
      by (metis fun_def.eq_iff fun_typ_q.distinct(1) option.inject)
  next
    case False  
    thus ?thesis using PConsNone wfPhi_elims 
      by (metis False lookup_fun.simps(2))
  qed
qed

lemma  wfPhi_f_poly_supp_b:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q
  assumes "Some (AF_fundef f  (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>"
  shows "supp b \<subseteq> supp bv"
proof -
  have "\<Theta> ; {|bv|} ; (x,b,c) #\<^sub>\<Gamma>GNil \<turnstile>\<^sub>w\<^sub>f \<tau>" using wfPhi_f_poly_wfT assms by auto
  thus ?thesis using wfT_wf wfG_cons wfB_supp by fastforce
qed

lemma wfPhi_f_poly_supp_t:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q
  assumes "Some (AF_fundef f  (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>"
  shows "supp \<tau> \<subseteq> { atom x , atom bv }"
 using wfPhi_f_poly_wfT[OF assms, THEN wfT_supp]  atom_dom.simps  supp_at_base by auto


lemma wfPhi_f_poly_supp_b_of_t:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q
  assumes "Some (AF_fundef f  (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>"
  shows "supp (b_of \<tau>) \<subseteq> { atom bv }"
proof - 
  have "atom x \<notin> supp (b_of \<tau>)" using x_fresh_b  by auto
  moreover have "supp (b_of \<tau>) \<subseteq> { atom x , atom bv }" using wfPhi_f_poly_supp_t  
    using   supp_at_base b_of.simps wfPhi_f_poly_supp_t \<tau>.supp b_of_supp assms by fast
  ultimately show ?thesis by blast
qed

lemma wfPhi_f_poly_supp_c:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q
  assumes "Some (AF_fundef f  (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>"
  shows "supp c \<subseteq> { atom x, atom bv }"
proof - 
  have "\<Theta> ; {|bv|} ; (x,b,c) #\<^sub>\<Gamma>GNil \<turnstile>\<^sub>w\<^sub>f \<tau>" using wfPhi_f_poly_wfT assms by auto
  thus ?thesis using wfG_wfC wfC_supp wfT_wf 
    using supp_at_base by fastforce
qed

lemma  wfPhi_f_poly_supp_s:
  fixes \<tau>::\<tau> and \<Theta>::\<Theta> and \<Phi>::\<Phi> and ft :: fun_typ_q
  assumes "Some (AF_fundef f  (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f" and "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>"
  shows "supp s \<subseteq> {atom x, atom bv}"
proof -

  have "AF_fundef f  (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s)) \<in> set \<Phi>" using lookup_fun_member assms by auto
  hence *:"\<Theta> ; \<Phi>  ; {|bv|} \<turnstile>\<^sub>w\<^sub>f (AF_fun_typ x b c \<tau> s)" using assms wfPhi_f_poly_wf by simp
  
  thus ?thesis using wfFT_wf_aux[OF *]  using supp_at_base by auto
qed

lemmas wfPhi_f_supp = wfPhi_f_poly_supp_b wfPhi_f_simple_supp_b wfPhi_f_poly_supp_c 
    wfPhi_f_simple_supp_t wfPhi_f_poly_supp_t wfPhi_f_simple_supp_t wfPhi_f_poly_wfT wfPhi_f_simple_wfT 
    wfPhi_f_poly_supp_s wfPhi_f_simple_supp_s

lemma fun_typ_eq_ret_unique: 
  assumes "(AF_fun_typ x1 b1 c1 \<tau>1' s1') =  (AF_fun_typ x2 b2 c2 \<tau>2' s2')"
  shows  "\<tau>1'[x1::=v]\<^sub>\<tau>\<^sub>v = \<tau>2'[x2::=v]\<^sub>\<tau>\<^sub>v"
proof -
  have "[[atom x1]]lst. \<tau>1' = [[atom x2]]lst. \<tau>2'" using assms lst_fst fun_typ.eq_iff lst_snd by metis
  thus ?thesis using subst_v_flip_eq_two[of x1 \<tau>1' x2 \<tau>2' v] subst_v_\<tau>_def by metis
qed

lemma fun_typ_eq_body_unique: 
  fixes v::v and x1::x and x2::x and s1'::s and s2'::s
  assumes "(AF_fun_typ x1 b1 c1 \<tau>1' s1') =  (AF_fun_typ x2 b2 c2 \<tau>2' s2')"
  shows  "s1'[x1::=v]\<^sub>s\<^sub>v = s2'[x2::=v]\<^sub>s\<^sub>v"
proof -
  have "[[atom x1]]lst. s1' = [[atom x2]]lst. s2'" using assms lst_fst fun_typ.eq_iff lst_snd by metis
  thus ?thesis using subst_v_flip_eq_two[of x1 s1' x2 s2' v] subst_v_s_def by metis
qed

lemma fun_ret_unique:
  assumes "Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ x1 b1 c1 \<tau>1' s1'))) = lookup_fun \<Phi> f" and "Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ x2 b2 c2 \<tau>2' s2'))) = lookup_fun \<Phi> f"
  shows "\<tau>1'[x1::=v]\<^sub>\<tau>\<^sub>v = \<tau>2'[x2::=v]\<^sub>\<tau>\<^sub>v"
proof -
  have *: " (AF_fundef f (AF_fun_typ_none (AF_fun_typ x1 b1 c1 \<tau>1' s1'))) = (AF_fundef f (AF_fun_typ_none (AF_fun_typ x2 b2 c2 \<tau>2' s2')))" using option.inject assms by metis
  thus ?thesis using fun_typ_eq_ret_unique fun_def.eq_iff fun_typ_q.eq_iff by metis
qed

lemma fun_poly_arg_unique:
  fixes bv1::bv and bv2::bv and b::b and \<tau>1::\<tau> and \<tau>2::\<tau>
  assumes "[[atom bv1]]lst. (AF_fun_typ x1 b1 c1 \<tau>1 s1) = [[atom bv2]]lst. (AF_fun_typ x2 b2 c2 \<tau>2 s2)" (is "[[atom ?x]]lst. ?a = [[atom ?y]]lst. ?b")
  shows "\<lbrace> x1 : b1[bv1::=b]\<^sub>b\<^sub>b | c1[bv1::=b]\<^sub>c\<^sub>b \<rbrace> = \<lbrace> x2 : b2[bv2::=b]\<^sub>b\<^sub>b | c2[bv2::=b]\<^sub>c\<^sub>b \<rbrace>" 
proof -
  obtain c::bv where *:"atom c \<sharp> (b,b1,b2,c1,c2) \<and> atom c \<sharp> (bv1, bv2, AF_fun_typ x1 b1 c1 \<tau>1 s1, AF_fun_typ x2 b2 c2 \<tau>2 s2)" using obtain_fresh fresh_Pair by metis
  hence "(bv1 \<leftrightarrow> c) \<bullet> AF_fun_typ x1 b1 c1 \<tau>1 s1 = (bv2 \<leftrightarrow> c) \<bullet> AF_fun_typ x2 b2 c2 \<tau>2 s2" using  Abs1_eq_iff_all(3)[of ?x ?a ?y ?b] assms by metis
  hence "AF_fun_typ x1 ((bv1 \<leftrightarrow> c) \<bullet> b1) ((bv1 \<leftrightarrow> c) \<bullet> c1) ((bv1 \<leftrightarrow> c) \<bullet> \<tau>1) ((bv1 \<leftrightarrow> c) \<bullet> s1) = AF_fun_typ x2 ((bv2 \<leftrightarrow> c) \<bullet> b2) ((bv2 \<leftrightarrow> c) \<bullet> c2) ((bv2 \<leftrightarrow> c) \<bullet> \<tau>2) ((bv2 \<leftrightarrow> c) \<bullet> s2)" 
    using fun_typ_flip by metis    
  hence **:"\<lbrace> x1 :((bv1 \<leftrightarrow> c) \<bullet> b1) | ((bv1 \<leftrightarrow> c) \<bullet> c1) \<rbrace> = \<lbrace> x2 : ((bv2 \<leftrightarrow> c) \<bullet> b2) | ((bv2 \<leftrightarrow> c) \<bullet> c2) \<rbrace>" (is "\<lbrace> x1 : ?b1 | ?c1 \<rbrace> = \<lbrace> x2 : ?b2 | ?c2 \<rbrace>") using fun_arg_unique_aux by metis
  hence "\<lbrace> x1 :((bv1 \<leftrightarrow> c) \<bullet> b1) | ((bv1 \<leftrightarrow> c) \<bullet> c1) \<rbrace>[c::=b]\<^sub>\<tau>\<^sub>b = \<lbrace> x2 : ((bv2 \<leftrightarrow> c) \<bullet> b2) | ((bv2 \<leftrightarrow> c) \<bullet> c2) \<rbrace>[c::=b]\<^sub>\<tau>\<^sub>b" by metis
  hence "\<lbrace> x1 :((bv1 \<leftrightarrow> c) \<bullet> b1)[c::=b]\<^sub>b\<^sub>b | ((bv1 \<leftrightarrow> c) \<bullet> c1)[c::=b]\<^sub>c\<^sub>b \<rbrace> = \<lbrace> x2 : ((bv2 \<leftrightarrow> c) \<bullet> b2)[c::=b]\<^sub>b\<^sub>b | ((bv2 \<leftrightarrow> c) \<bullet> c2)[c::=b]\<^sub>c\<^sub>b \<rbrace>" using subst_tb.simps by metis  
  thus ?thesis using *  flip_subst_subst subst_b_c_def subst_b_b_def fresh_prodN flip_commute by metis
qed

lemma fun_poly_ret_unique:
  assumes "Some (AF_fundef f (AF_fun_typ_some bv1 (AF_fun_typ x1 b1 c1 \<tau>1' s1'))) = lookup_fun \<Phi> f" and "Some (AF_fundef f (AF_fun_typ_some bv2 (AF_fun_typ x2 b2 c2 \<tau>2' s2'))) = lookup_fun \<Phi> f"
  shows "\<tau>1'[bv1::=b]\<^sub>\<tau>\<^sub>b[x1::=v]\<^sub>\<tau>\<^sub>v = \<tau>2'[bv2::=b]\<^sub>\<tau>\<^sub>b[x2::=v]\<^sub>\<tau>\<^sub>v"
proof -
  have *: " (AF_fundef f (AF_fun_typ_some bv1 (AF_fun_typ x1 b1 c1 \<tau>1' s1'))) = (AF_fundef f (AF_fun_typ_some bv2 (AF_fun_typ x2 b2 c2 \<tau>2' s2')))" using option.inject assms by metis
  hence "AF_fun_typ_some bv1 (AF_fun_typ x1 b1 c1 \<tau>1' s1') = AF_fun_typ_some bv2 (AF_fun_typ x2 b2 c2 \<tau>2' s2')" 
      (is "AF_fun_typ_some bv1 ?ft1 = AF_fun_typ_some bv2 ?ft2") using fun_def.eq_iff by metis
  hence **:"[[atom bv1]]lst. ?ft1 = [[atom bv2]]lst. ?ft2" using fun_typ_q.eq_iff(1) by metis

  hence *:"subst_ft_b ?ft1 bv1 b = subst_ft_b ?ft2 bv2 b" using subst_b_flip_eq_two subst_b_fun_typ_def by metis
  have "[[atom x1]]lst. \<tau>1'[bv1::=b]\<^sub>\<tau>\<^sub>b = [[atom x2]]lst. \<tau>2'[bv2::=b]\<^sub>\<tau>\<^sub>b" 
    apply(rule lst_snd[of _ "c1[bv1::=b]\<^sub>c\<^sub>b" _ _ "c2[bv2::=b]\<^sub>c\<^sub>b"])
    apply(rule lst_fst[of _ _ "s1'[bv1::=b]\<^sub>s\<^sub>b" _ _ "s2'[bv2::=b]\<^sub>s\<^sub>b"])
    using *  subst_ft_b.simps fun_typ.eq_iff by metis
  thus ?thesis using subst_v_flip_eq_two subst_v_\<tau>_def by metis
qed

lemma fun_poly_body_unique:
  assumes "Some (AF_fundef f (AF_fun_typ_some bv1 (AF_fun_typ x1 b1 c1 \<tau>1' s1'))) = lookup_fun \<Phi> f" and "Some (AF_fundef f (AF_fun_typ_some bv2 (AF_fun_typ x2 b2 c2 \<tau>2' s2'))) = lookup_fun \<Phi> f"
  shows "s1'[bv1::=b]\<^sub>s\<^sub>b[x1::=v]\<^sub>s\<^sub>v = s2'[bv2::=b]\<^sub>s\<^sub>b[x2::=v]\<^sub>s\<^sub>v"
proof - 
  have *: " (AF_fundef f (AF_fun_typ_some bv1 (AF_fun_typ x1 b1 c1 \<tau>1' s1'))) = (AF_fundef f (AF_fun_typ_some bv2 (AF_fun_typ x2 b2 c2 \<tau>2' s2')))" 
    using option.inject assms by metis
  hence "AF_fun_typ_some bv1 (AF_fun_typ x1 b1 c1 \<tau>1' s1') = AF_fun_typ_some bv2 (AF_fun_typ x2 b2 c2 \<tau>2' s2')" 
      (is "AF_fun_typ_some bv1 ?ft1 = AF_fun_typ_some bv2 ?ft2") using fun_def.eq_iff by metis
  hence **:"[[atom bv1]]lst. ?ft1 = [[atom bv2]]lst. ?ft2" using fun_typ_q.eq_iff(1) by metis

  hence *:"subst_ft_b ?ft1 bv1 b = subst_ft_b ?ft2 bv2 b" using subst_b_flip_eq_two subst_b_fun_typ_def by metis
  have "[[atom x1]]lst. s1'[bv1::=b]\<^sub>s\<^sub>b = [[atom x2]]lst. s2'[bv2::=b]\<^sub>s\<^sub>b" 
    using lst_snd lst_fst subst_ft_b.simps fun_typ.eq_iff 
    by (metis "local.*")

  thus ?thesis using subst_v_flip_eq_two subst_v_s_def by metis
qed

lemma funtyp_eq_iff_equalities:
  fixes s'::s and s::s
  assumes " [[atom x']]lst. ((c', \<tau>'), s') = [[atom x]]lst. ((c, \<tau>), s)" 
  shows "\<lbrace> x' : b  | c' \<rbrace> = \<lbrace> x : b  | c \<rbrace> \<and>  s'[x'::=v]\<^sub>s\<^sub>v = s[x::=v]\<^sub>s\<^sub>v \<and> \<tau>'[x'::=v]\<^sub>\<tau>\<^sub>v = \<tau>[x::=v]\<^sub>\<tau>\<^sub>v"
proof - 
  have  "[[atom x']]lst. s' = [[atom x]]lst. s" and "[[atom x']]lst. \<tau>' = [[atom x]]lst. \<tau>" and
           " [[atom x']]lst. c' = [[atom x]]lst. c" using lst_snd lst_fst assms by metis+
  thus ?thesis using   subst_v_flip_eq_two  \<tau>.eq_iff 
    by (metis assms fun_typ.eq_iff fun_typ_eq_body_unique fun_typ_eq_ret_unique)
qed

section \<open>Weakening\<close>

lemma wfX_wfB1:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and b::b and \<B>::\<B> and \<Phi>::\<Phi> and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def
           and cs::branch_s and css::branch_list
  shows  wfV_wfB: "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b" and     
         "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c \<Longrightarrow> True" and
         "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<Longrightarrow>   True" and
         wfT_wfB: "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau> \<Longrightarrow>  \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b_of \<tau> " and
         "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ts \<Longrightarrow>  True" and 
         "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow> True" and     
         "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b \<Longrightarrow>  True" and       
         wfCE_wfB: "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce : b \<Longrightarrow> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b" and
         "\<Theta>  \<turnstile>\<^sub>w\<^sub>f td \<Longrightarrow> True"
proof(induct   rule:wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.inducts)
 case (wfV_varI \<Theta> \<B> \<Gamma> b c x)
  hence "(x,b,c) \<in> toSet \<Gamma>" using lookup_iff wfV_wf  using lookup_in_g by presburger
  hence "b \<in> fst`snd`toSet \<Gamma>" by force
  hence "wfB \<Theta> \<B> b" using wfG_wfB wfV_varI by metis
  then show ?case using wfV_elims wfG_wf  wf_intros by metis
next
  case (wfV_litI \<Theta> \<Gamma> l)
  moreover have "wfTh \<Theta>" using wfV_wf wfG_wf wfV_litI by metis
  ultimately  show ?case using wfV_wf wfG_wf  wf_intros base_for_lit.simps l.exhaust by metis
next
  case (wfV_pairI \<Theta> \<Gamma> v1 b1 v2 b2)
   then show ?case using  wfG_wf  wf_intros by metis
next
  case (wfV_consI s dclist \<Theta> dc x b c B \<Gamma> v)
  then show ?case
    using wfV_wf wfG_wf   wfB_consI by metis  
next
  case (wfV_conspI s bv dclist \<Theta> dc x b' c \<B> b \<Gamma> v)
  then show ?case
    using wfV_wf wfG_wf  using wfB_appI by metis
next
  case (wfCE_valI \<Theta> \<B> \<Gamma> v b)
  then show ?case using wfB_elims by auto
next
  case (wfCE_plusI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case using wfB_elims by auto
next
  case (wfCE_leqI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case using  wfV_wf wfG_wf  wf_intros wfX_wfY by metis
next
  case (wfCE_eqI \<Theta> \<B> \<Gamma> v1 b v2)
  then show ?case using  wfV_wf wfG_wf  wf_intros wfX_wfY by metis
next
  case (wfCE_fstI \<Theta> \<B> \<Gamma> v1 b1 b2)
  then show ?case using  wfB_elims by metis
next
  case (wfCE_sndI \<Theta> \<B> \<Gamma> v1 b1 b2)
  then show ?case using wfB_elims by metis
next
  case (wfCE_concatI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case using wfB_elims by auto
next
  case (wfCE_lenI \<Theta> \<B> \<Gamma> v1)
  then show ?case using  wfV_wf wfG_wf  wf_intros wfX_wfY by metis
qed(auto | metis wfV_wf wfG_wf  wf_intros )+

lemma wfX_wfB2:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and b::b and \<B>::\<B> and \<Phi>::\<Phi> and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def
           and cs::branch_s and css::branch_list
  shows
         wfE_wfB: "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b \<Longrightarrow> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b"  and
         wfS_wfB: "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<Longrightarrow> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b" and
         wfCS_wfB: "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f cs : b \<Longrightarrow>  \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b" and
         wfCSS_wfB: "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b \<Longrightarrow>  \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b" and     
         "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> \<Longrightarrow> True" and
         "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<Longrightarrow>  True" and   
         "\<Theta> ; \<Phi>   \<turnstile>\<^sub>w\<^sub>f ftq \<Longrightarrow> True" and
         "\<Theta> ; \<Phi>  ; \<B> \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow> \<B> |\<subseteq>| \<B>' \<Longrightarrow> \<Theta> ; \<Phi>  ; \<B>' \<turnstile>\<^sub>w\<^sub>f ft" 
proof(induct   rule:wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.inducts) 
  case (wfE_valI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v b)
  then show ?case using wfB_elims wfX_wfB1 by metis
next
  case (wfE_plusI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wfB_elims wfX_wfB1 by metis
next
  case (wfE_eqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b v2)
  then show ?case using wfB_boolI  wfX_wfY by metis
next
  case (wfE_fstI \<Theta> \<Phi> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case using wfB_elims wfX_wfB1 by metis
next
  case (wfE_sndI \<Theta> \<Phi> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case using wfB_elims wfX_wfB1 by metis
next
  case (wfE_concatI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wfB_elims wfX_wfB1 by metis
next
  case (wfE_splitI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wfB_elims wfX_wfB1 
    using wfB_pairI by auto
next
  case (wfE_lenI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1)
  then show ?case using wfB_elims wfX_wfB1 
    using wfB_intI wfX_wfY1(1) by auto
next
  case (wfE_appI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> f x b c \<tau> s v)
  hence "\<Theta>; \<B>;(x,b,c) #\<^sub>\<Gamma> GNil  \<turnstile>\<^sub>w\<^sub>f \<tau>"  using wfPhi_f_simple_wfT wfT_b_weakening by fast
  then show ?case using b_of.simps using wfT_b_weakening
     by (metis b_of.cases bot.extremum wfT_elims(2))
next
  case (wfE_appPI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> b' bv v \<tau> f x b c s)
  hence "\<Theta> ; {| bv |} ;(x,b,c) #\<^sub>\<Gamma> GNil  \<turnstile>\<^sub>w\<^sub>f \<tau>"  using wfPhi_f_poly_wfT wfX_wfY by blast
  then show ?case using wfE_appPI b_of.simps using wfT_b_weakening wfT_elims  wfT_subst_wfB subst_b_b_def  by metis
next
  case (wfE_mvarI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> u \<tau>)
  hence "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>" using wfD_wfT by fast
  then show ?case using wfT_elims b_of.simps by metis
next
  case (wfFTNone \<Theta> ft)
  then show ?case by auto
next
  case (wfFTSome \<Theta> bv ft)
  then show ?case by auto
next
  case (wfS_valI \<Theta> \<Phi> \<B> \<Gamma> v b \<Delta>)
  then show ?case using wfX_wfB1 by auto
next
  case (wfS_letI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e b' x s b)
  then show ?case using wfX_wfB1 by auto
next
  case (wfS_let2I \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 \<tau> x s2 b)
  then show ?case using wfX_wfB1 by auto
next
  case (wfS_ifI \<Theta> \<B> \<Gamma> v \<Phi> \<Delta> s1 b s2)
  then show ?case using wfX_wfB1 by auto
next
  case (wfS_varI \<Theta> \<B> \<Gamma> \<tau> v u \<Phi> \<Delta> b s)
  then show ?case using wfX_wfB1 by auto
next
  case (wfS_assignI u \<tau> \<Delta> \<Theta> \<B> \<Gamma> \<Phi> v)
  then show ?case using wfX_wfB1 
    using wfB_unitI wfX_wfY2(5) by auto
next
  case (wfS_whileI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 s2 b)
  then show ?case using wfX_wfB1 by auto
next
  case (wfS_seqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 s2 b)
  then show ?case using wfX_wfB1 by auto
next
  case (wfS_matchI \<Theta> \<B> \<Gamma> v tid dclist \<Delta> \<Phi> cs b)
  then show ?case using wfX_wfB1 by auto
next
  case (wfS_branchI \<Theta> \<Phi> \<B> x \<tau> \<Gamma> \<Delta> s b tid dc)
  then show ?case using wfX_wfB1 by auto
next
  case (wfS_finalI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dc t cs b)
  then show ?case using wfX_wfB1 by auto
next
  case (wfS_cons \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dc t cs b dclist css)
  then show ?case using wfX_wfB1 by auto      
next
  case (wfD_emptyI \<Theta> \<B> \<Gamma>)
  then show ?case using wfX_wfB1 by auto
next
  case (wfD_cons \<Theta> \<B> \<Gamma> \<Delta> \<tau> u)
  then show ?case using wfX_wfB1 by auto
next
  case (wfPhi_emptyI \<Theta>)
  then show ?case using wfX_wfB1 by auto
next
  case (wfPhi_consI f \<Theta> \<Phi> ft)
  then show ?case using wfX_wfB1 by auto
next
  case (wfFTI \<Theta> B b \<Phi> x c s \<tau>)
  then show ?case using wfX_wfB1 
    by (meson Wellformed.wfFTI wb_b_weakening2(8))
qed(metis wfV_wf wfG_wf  wf_intros wfX_wfB1)

lemmas wfX_wfB = wfX_wfB1 wfX_wfB2

lemma wf_weakening1:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and \<B>::\<B> and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def
         and cs::branch_s and css::branch_list

  shows  wfV_weakening: "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<Longrightarrow> toSet \<Gamma> \<subseteq> toSet \<Gamma>' \<Longrightarrow> \<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f v : b" and
         wfC_weakening: "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<Longrightarrow> toSet \<Gamma> \<subseteq> toSet \<Gamma>'  \<Longrightarrow> \<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f  c" and
         "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<Longrightarrow>  True" and
         wfT_weakening: "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<tau> \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<Longrightarrow> toSet \<Gamma> \<subseteq> toSet \<Gamma>' \<Longrightarrow>  \<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f  \<tau>" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ts  \<Longrightarrow>  True" and 
         "\<turnstile>\<^sub>w\<^sub>f P \<Longrightarrow> True " and
         wfB_weakening: "wfB \<Theta> \<B> b \<Longrightarrow>  \<B> |\<subseteq>| \<B>' \<Longrightarrow> wfB \<Theta> \<B> b" and 
         wfCE_weakening: "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ce : b \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<Longrightarrow> toSet \<Gamma> \<subseteq> toSet \<Gamma>' \<Longrightarrow> \<Theta>; \<B>;  \<Gamma>' \<turnstile>\<^sub>w\<^sub>f ce : b"  and
         "\<Theta>  \<turnstile>\<^sub>w\<^sub>f td \<Longrightarrow> True"
proof(nominal_induct
          b and c and \<Gamma> and \<tau> and ts and P and b and b and td 
          avoiding:  \<Gamma>'          
          rule:wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.strong_induct)
 case (wfV_varI \<Theta> \<B> \<Gamma> b c x)
  hence "Some (b, c) = lookup \<Gamma>' x" using  lookup_weakening  by metis
  then show ?case using Wellformed.wfV_varI wfV_varI by metis
next
  case (wfTI z \<Theta> \<B>  \<Gamma>  b c)  (* This proof pattern is used elsewhere when proving weakening for typing predicates *)
  show ?case proof
    show \<open>atom z \<sharp> (\<Theta>, \<B>, \<Gamma>')\<close> using wfTI by auto
    show \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b \<close> using wfTI by auto
    have *:"toSet ((z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>) \<subseteq> toSet ((z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>')" using toSet.simps wfTI by auto
    thus  \<open> \<Theta>; \<B>; (z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>'   \<turnstile>\<^sub>w\<^sub>f c \<close> using wfTI(8)[OF _ *] wfTI wfX_wfY
      by (simp add: wfG_cons_TRUE)
  qed
next
  case (wfV_conspI s bv dclist \<Theta> dc x b' c \<B> b \<Gamma> v)
  show ?case proof
    show \<open>AF_typedef_poly s bv dclist \<in> set \<Theta>\<close> using wfV_conspI by auto
    show \<open>(dc, \<lbrace> x : b'  | c \<rbrace>) \<in> set dclist\<close> using wfV_conspI by auto
    show \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b \<close> using wfV_conspI by auto
    show \<open>atom bv \<sharp> (\<Theta>, \<B>, \<Gamma>', b, v)\<close> using wfV_conspI by simp
    show \<open> \<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f v : b'[bv::=b]\<^sub>b\<^sub>b \<close> using wfV_conspI by auto
  qed
qed(metis wf_intros)+

lemma wf_weakening2:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and \<B>::\<B> and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def
         and cs::branch_s and css::branch_list
  shows 
         wfE_weakening: "\<Theta>; \<Phi>; \<B>; \<Gamma>  ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<Longrightarrow> toSet \<Gamma> \<subseteq> toSet \<Gamma>' \<Longrightarrow> \<Theta>; \<Phi>; \<B>;  \<Gamma>' ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b" and
         wfS_weakening: "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<Longrightarrow> toSet \<Gamma> \<subseteq> toSet \<Gamma>' \<Longrightarrow> \<Theta>; \<Phi>; \<B>;  \<Gamma>' ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b" and
         "\<Theta> ; \<Phi> ; \<B>  ; \<Gamma> ; \<Delta> ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f cs : b \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<Longrightarrow> toSet \<Gamma> \<subseteq> toSet \<Gamma>' \<Longrightarrow>  \<Theta>; \<Phi>; \<B>; \<Gamma>' ; \<Delta> ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f cs : b" and
         "\<Theta> ; \<Phi> ; \<B>  ; \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<Longrightarrow> toSet \<Gamma> \<subseteq> toSet \<Gamma>' \<Longrightarrow>  \<Theta>; \<Phi>; \<B>; \<Gamma>' ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b" and       
         "\<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) \<Longrightarrow> True" and
         wfD_weakning: "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<Longrightarrow> toSet \<Gamma> \<subseteq> toSet \<Gamma>' \<Longrightarrow>  \<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f  \<Delta>" and       
         "\<Theta> ; \<Phi>   \<turnstile>\<^sub>w\<^sub>f ftq \<Longrightarrow> True" and
         "\<Theta> ; \<Phi>  ; \<B> \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow>   True" 
proof(nominal_induct
          b and b and b and b and \<Phi> and \<Delta> and ftq and ft
          avoiding:  \<Gamma>'          
          rule:wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.strong_induct)
  case (wfE_appPI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> b' bv v \<tau> f x b c s)
  show ?case proof
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wfE_appPI by auto
    show \<open> \<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfE_appPI by auto
    show \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b' \<close> using wfE_appPI by auto
    show \<open>atom bv \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>', \<Delta>, b', v, (b_of \<tau>)[bv::=b']\<^sub>b)\<close> using wfE_appPI by auto
    show \<open>Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f\<close> using wfE_appPI by auto
    show \<open> \<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f v : b[bv::=b']\<^sub>b \<close> using wfE_appPI wf_weakening1 by auto
  qed
next                          
  case (wfS_letI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e b' x s b)
  show ?case proof(rule)
    show \<open> \<Theta> ; \<Phi>  ; \<B> ; \<Gamma>' ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b' \<close> using wfS_letI by auto
    have "toSet ((x, b', TRUE)  #\<^sub>\<Gamma> \<Gamma>) \<subseteq> toSet  ((x, b', TRUE)  #\<^sub>\<Gamma> \<Gamma>')"  using wfS_letI by auto
    thus \<open> \<Theta> ; \<Phi>  ; \<B> ; (x, b', TRUE)  #\<^sub>\<Gamma> \<Gamma>' ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<close>  using wfS_letI by (meson wfG_cons wfG_cons_TRUE wfS_wf)
    show \<open> \<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close>  using wfS_letI by auto
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>', \<Delta>, e, b)\<close>  using wfS_letI by auto
  qed
next
  case (wfS_let2I \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 \<tau> x s2 b)
  show ?case proof
    show \<open> \<Theta> ; \<Phi>  ; \<B> ; \<Gamma>' ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s1 : b_of \<tau> \<close> using wfS_let2I by auto
    show \<open> \<Theta>; \<B>; \<Gamma>'   \<turnstile>\<^sub>w\<^sub>f \<tau> \<close>  using wfS_let2I wf_weakening1 by auto
    have "toSet ((x, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma>) \<subseteq> toSet  ((x, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma>')"  using wfS_let2I by auto
    thus \<open> \<Theta> ; \<Phi>  ; \<B> ; (x, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma>' ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s2 : b \<close>  using wfS_let2I    by (meson wfG_cons wfG_cons_TRUE wfS_wf)
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>', \<Delta>, s1, b, \<tau>)\<close>  using wfS_let2I by auto
  qed
next
  case (wfS_varI \<Theta> \<B> \<Gamma> \<tau> v u \<Phi> \<Delta> b s)
  show ?case proof
    show "\<Theta>; \<B>; \<Gamma>'  \<turnstile>\<^sub>w\<^sub>f \<tau> " using wfS_varI wf_weakening1 by auto
    show "\<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f v : b_of \<tau> "  using wfS_varI wf_weakening1 by auto
    show "atom u \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>', \<Delta>, \<tau>, v, b)"  using wfS_varI by auto
    show "\<Theta> ; \<Phi>  ; \<B> ; \<Gamma>' ; (u, \<tau>)  #\<^sub>\<Delta> \<Delta>  \<turnstile>\<^sub>w\<^sub>f s : b "  using wfS_varI by auto
  qed
next
  case (wfS_branchI \<Theta> \<Phi> \<B> x \<tau>  \<Gamma> \<Delta> s b tid dc)
  show ?case proof
    have "toSet ((x, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma>) \<subseteq> toSet  ((x, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma>')"  using wfS_branchI by auto
    thus \<open> \<Theta> ; \<Phi>  ; \<B> ; (x, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma>' ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<close> using wfS_branchI  by (meson wfG_cons wfG_cons_TRUE wfS_wf)
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>', \<Delta>, \<Gamma>', \<tau>)\<close> using wfS_branchI by auto
    show \<open> \<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfS_branchI by auto
  qed
next
  case (wfS_finalI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist' cs b dclist)
  then show ?case using wf_intros by metis
next
  case (wfS_cons \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist' cs b css dclist)
  then show ?case using wf_intros by metis
next
  case (wfS_assertI \<Theta> \<Phi> \<B> x c \<Gamma> \<Delta> s b)
  show ?case proof(rule)
    show \<open> \<Theta>; \<B>; \<Gamma>'   \<turnstile>\<^sub>w\<^sub>f c \<close> using wfS_assertI wf_weakening1 by auto
    have "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>'" proof(rule wfG_consI)
      show \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<close> using wfS_assertI by auto
      show \<open>atom x \<sharp> \<Gamma>'\<close> using wfS_assertI by auto
      show \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f B_bool \<close> using wfS_assertI wfB_boolI wfX_wfY by metis
      have "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f (x, B_bool, TRUE) #\<^sub>\<Gamma> \<Gamma>'" proof
        show "(TRUE) \<in> {TRUE, FALSE}" by auto
        show \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<close> using wfS_assertI by auto
        show \<open>atom x \<sharp> \<Gamma>'\<close> using wfS_assertI by auto
        show \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f B_bool \<close> using wfS_assertI wfB_boolI wfX_wfY by metis
      qed
      thus  \<open> \<Theta>; \<B>; (x, B_bool, TRUE) #\<^sub>\<Gamma> \<Gamma>' \<turnstile>\<^sub>w\<^sub>f c \<close> 
       using  wf_weakening1(2)[OF \<open> \<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f c \<close>  \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f (x, B_bool, TRUE) #\<^sub>\<Gamma> \<Gamma>' \<close>] by force
    qed  
    thus  \<open> \<Theta>; \<Phi>; \<B>; (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>' ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<close> using wfS_assertI by fastforce   
    show \<open> \<Theta>; \<B>; \<Gamma>' \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfS_assertI by auto
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>', \<Delta>, c, b, s)\<close> using wfS_assertI by auto
  qed
qed(metis wf_intros wf_weakening1)+

lemmas wf_weakening = wf_weakening1 wf_weakening2

lemma wfV_weakening_cons:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and c::c
  assumes "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b"  and "atom y \<sharp> \<Gamma>" and "\<Theta>; \<B>; ((y,b',TRUE) #\<^sub>\<Gamma> \<Gamma>) \<turnstile>\<^sub>w\<^sub>f c" 
  shows "\<Theta>; \<B>; (y,b',c) #\<^sub>\<Gamma>\<Gamma> \<turnstile>\<^sub>w\<^sub>f  v : b"
proof -
  have "wfG \<Theta> \<B> ((y,b',c) #\<^sub>\<Gamma>\<Gamma>)" using wfG_intros2 assms by auto
  moreover have "toSet \<Gamma> \<subseteq> toSet ((y,b',c) #\<^sub>\<Gamma>\<Gamma>)" using toSet.simps by auto
  ultimately show ?thesis using wf_weakening  using assms(1) by blast
qed

lemma wfG_cons_weakening:
  fixes \<Gamma>'::\<Gamma>
  assumes "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f ((x, b, c)  #\<^sub>\<Gamma> \<Gamma>)" and  "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>'" and "toSet \<Gamma> \<subseteq> toSet \<Gamma>'" and "atom x \<sharp> \<Gamma>'"
  shows  "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f ((x, b, c)  #\<^sub>\<Gamma> \<Gamma>')"
proof(cases "c \<in> {TRUE,FALSE}")
  case True
  then show ?thesis using wfG_wfB  wfG_cons2I assms by auto
next
  case False
  hence *:"\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<and> atom x \<sharp> \<Gamma> \<and>  \<Theta>; \<B>; (x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c" 
    using  wfG_elims(2)[OF assms(1)] by auto
  have a1:"\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f  (x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>'" using wfG_wfB wfG_cons2I assms by simp
  moreover have a2:"toSet ((x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma> ) \<subseteq> toSet ((x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>')" using toSet.simps assms by blast
  moreover have " \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f (x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>'" proof
    show "(TRUE) \<in> {TRUE, FALSE}" by auto
    show "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>'" using assms by auto
    show "atom x \<sharp> \<Gamma>'" using assms by auto
    show "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b" using assms wfG_elims by metis
  qed  
  hence " \<Theta>; \<B>;  (x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>'  \<turnstile>\<^sub>w\<^sub>f c" using wf_weakening  a1 a2 * by auto
  then show ?thesis using wfG_cons1I[of c \<Theta> \<B> \<Gamma>' x b, OF False ] wfG_wfB assms by simp
qed

lemma wfT_weakening_aux:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and c::c
  assumes "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c \<rbrace>"  and "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f  \<Gamma>'" and "toSet \<Gamma> \<subseteq> toSet \<Gamma>'" and "atom z \<sharp> \<Gamma>'"
  shows "\<Theta>; \<B>; \<Gamma>'  \<turnstile>\<^sub>w\<^sub>f  \<lbrace> z : b | c \<rbrace>" 
proof 
  show \<open>atom z \<sharp> (\<Theta>, \<B>, \<Gamma>')\<close> 
    using wf_supp wfX_wfY assms fresh_prodN fresh_def x_not_in_b_set wfG_fresh_x by metis
  show \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b \<close> using assms wfT_elims by metis
  show \<open> \<Theta>; \<B>; (z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>'   \<turnstile>\<^sub>w\<^sub>f c \<close> proof - 
    have *:"\<Theta>; \<B>; (z,b,TRUE) #\<^sub>\<Gamma>\<Gamma> \<turnstile>\<^sub>w\<^sub>f c" using wfT_wfC fresh_weakening assms by auto
    moreover have a1:"\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f  (z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>'" using wfG_cons2I assms \<open>\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f  b\<close> by simp
    moreover have a2:"toSet ((z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma> ) \<subseteq> toSet ((z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>')" using toSet.simps assms by blast
    moreover have " \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f (z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>' " proof
      show "(TRUE) \<in> {TRUE, FALSE}" by auto
      show "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>'" using assms by auto
      show "atom z \<sharp> \<Gamma>'" using assms by auto
      show "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b" using assms wfT_elims by metis
    qed  
    thus ?thesis  using wf_weakening a1 a2 * by auto
  qed    
qed

lemma wfT_weakening_all:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and \<tau>::\<tau>
  assumes "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<tau>"  and "\<Theta>; \<B>' \<turnstile>\<^sub>w\<^sub>f  \<Gamma>'" and "toSet \<Gamma> \<subseteq> toSet \<Gamma>'" and "\<B> |\<subseteq>| \<B>'" 
  shows "\<Theta>; \<B>' ; \<Gamma>'  \<turnstile>\<^sub>w\<^sub>f  \<tau>" 
  using wb_b_weakening assms wfT_weakening by metis

lemma wfT_weakening_nil:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and \<tau>::\<tau>
  assumes "\<Theta> ; {||} ; GNil  \<turnstile>\<^sub>w\<^sub>f \<tau>"  and "\<Theta>; \<B>' \<turnstile>\<^sub>w\<^sub>f  \<Gamma>'" 
  shows "\<Theta>; \<B>' ; \<Gamma>'  \<turnstile>\<^sub>w\<^sub>f  \<tau>" 
  using wfT_weakening_all
  using assms(1) assms(2) toSet.simps(1) by blast

lemma wfTh_wfT2: 
  fixes x::x and v::v and \<tau>::\<tau> and G::\<Gamma>
  assumes "wfTh \<Theta>" and "AF_typedef s dclist \<in> set \<Theta>" and 
      "(dc, \<tau>) \<in> set dclist"  and "\<Theta> ; B \<turnstile>\<^sub>w\<^sub>f G"
  shows "supp \<tau> = {}" and "\<tau>[x::=v]\<^sub>\<tau>\<^sub>v = \<tau>" and "wfT \<Theta> B G \<tau>"
proof -
  show  "supp \<tau> = {}" proof(rule ccontr)
    assume a1: "supp \<tau> \<noteq> {}"
    have  "supp \<Theta> \<noteq> {}" proof -
      obtain dclist where dc: "AF_typedef s dclist \<in> set \<Theta> \<and> (dc, \<tau>) \<in> set dclist" 
        using assms  by auto
      hence "supp (dc,\<tau>)  \<noteq> {}" 
        using a1  by (simp add: supp_Pair)
      hence "supp dclist  \<noteq> {}" using dc supp_list_member by auto
      hence "supp (AF_typedef s dclist) \<noteq> {}"  using type_def.supp by auto
      thus ?thesis using supp_list_member dc by auto
    qed
    thus False using assms wfTh_supp by simp
  qed
  thus "\<tau>[x::=v]\<^sub>\<tau>\<^sub>v = \<tau>"  by (simp add: fresh_def)
  have "wfT \<Theta> {||} GNil \<tau>" using assms wfTh_wfT by auto
  thus "wfT \<Theta> B G \<tau>" using assms wfT_weakening_nil by simp
qed

lemma wf_d_weakening:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and s::s and \<B>::\<B> and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def
         and cs::branch_s and css::branch_list
  shows 
         "\<Theta>; \<Phi>; \<B>; \<Gamma>  ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b \<Longrightarrow> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>' \<Longrightarrow> setD \<Delta> \<subseteq> setD \<Delta>' \<Longrightarrow> \<Theta>; \<Phi>; \<B>;  \<Gamma> ; \<Delta>' \<turnstile>\<^sub>w\<^sub>f e : b" and
         "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<Longrightarrow> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>' \<Longrightarrow> setD \<Delta> \<subseteq> setD \<Delta>' \<Longrightarrow> \<Theta>; \<Phi>; \<B>;  \<Gamma> ; \<Delta>' \<turnstile>\<^sub>w\<^sub>f s : b" and
         "\<Theta> ; \<Phi> ; \<B>  ; \<Gamma> ; \<Delta> ; tid ; dc ; t  \<turnstile>\<^sub>w\<^sub>f cs : b \<Longrightarrow> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>' \<Longrightarrow> setD \<Delta> \<subseteq> setD \<Delta>' \<Longrightarrow>  \<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta>' ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f cs : b" and
         "\<Theta> ; \<Phi> ; \<B>  ; \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b \<Longrightarrow> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>' \<Longrightarrow> setD \<Delta> \<subseteq> setD \<Delta>' \<Longrightarrow>   \<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta>' ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b" and       
         "\<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) \<Longrightarrow> True" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<Longrightarrow> True" and        
         "\<Theta> ; \<Phi>   \<turnstile>\<^sub>w\<^sub>f ftq \<Longrightarrow> True" and
         "\<Theta> ; \<Phi>  ; \<B> \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow>   True"
proof(nominal_induct
          b and b and b and b and \<Phi> and \<Delta> and  ftq and ft 
          avoiding:  \<Delta>'         
       rule:wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.strong_induct)
  case (wfE_valI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v b)
  then show ?case using wf_intros by metis
next
  case (wfE_plusI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros by metis
next
  case (wfE_leqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros by metis
next
  case (wfE_eqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b v2)
  then show ?case using wf_intros by metis
next
  case (wfE_fstI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case using wf_intros by metis
next
  case (wfE_sndI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case using wf_intros by metis
next
  case (wfE_concatI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros by metis
next
  case (wfE_splitI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_intros by metis
next
  case (wfE_lenI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1)
  then show ?case using wf_intros by metis
next
  case (wfE_appI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> f x b c \<tau> s v)
  then show ?case using wf_intros by metis
next
   case (wfE_appPI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> b' bv v \<tau> f x b c s)
   show ?case proof(rule, (rule wfE_appPI)+)
    show \<open>atom bv \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>', b', v, (b_of \<tau>)[bv::=b']\<^sub>b)\<close>  using wfE_appPI by auto
    show \<open>Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f\<close>  using wfE_appPI by auto
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b[bv::=b']\<^sub>b \<close>  using wfE_appPI by auto
  qed
next
  case (wfE_mvarI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> u \<tau>)
  show ?case proof
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wfE_mvarI by auto
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>' \<close> using wfE_mvarI by auto
    show \<open>(u, \<tau>) \<in> setD \<Delta>'\<close> using wfE_mvarI by auto
  qed
next
  case (wfS_valI \<Theta> \<Phi> \<B> \<Gamma> v b \<Delta>)
  then show ?case using wf_intros by metis
next
  case (wfS_letI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e b' x s b)
  show ?case proof(rule)
    show \<open> \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>' \<turnstile>\<^sub>w\<^sub>f e : b' \<close> using wfS_letI by auto
    have "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f  (x, b', TRUE)  #\<^sub>\<Gamma> \<Gamma>"  using wfG_cons2I wfX_wfY wfS_letI by metis
    hence "\<Theta>; \<B>; (x, b', TRUE)  #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>'" using wf_weakening2(6) wfS_letI by force
    thus \<open> \<Theta> ; \<Phi>  ; \<B> ; (x, b', TRUE)  #\<^sub>\<Gamma> \<Gamma> ; \<Delta>' \<turnstile>\<^sub>w\<^sub>f s : b \<close> using wfS_letI by metis
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>' \<close> using wfS_letI by auto
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>', e, b)\<close> using wfS_letI by auto
  qed
next
  case (wfS_assertI \<Theta> \<Phi> \<B> x c \<Gamma> \<Delta> s b)
  show ?case proof
    have "\<Theta>; \<B>; (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>'" proof(rule  wf_weakening2(6))
      show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>' \<close> using wfS_assertI by auto
    next
      show \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma> \<close> using wfS_assertI wfX_wfY by metis
    next
      show \<open>toSet \<Gamma> \<subseteq> toSet ((x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>)\<close> using wfS_assertI by auto
    qed
    thus  \<open> \<Theta>; \<Phi>; \<B>; (x, B_bool, c) #\<^sub>\<Gamma> \<Gamma> ; \<Delta>' \<turnstile>\<^sub>w\<^sub>f s : b \<close> using wfS_assertI wfX_wfY by metis
  next
    show \<open> \<Theta>; \<B>; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c \<close> using wfS_assertI by auto
  next
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>' \<close> using wfS_assertI by auto
  next
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>', c, b, s)\<close> using wfS_assertI by auto
  qed
next
  case (wfS_let2I \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 \<tau> x s2 b)
  show ?case proof
    show \<open> \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>' \<turnstile>\<^sub>w\<^sub>f s1 : b_of \<tau> \<close> using wfS_let2I by auto
    show \<open> \<Theta>; \<B>; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<tau> \<close> using wfS_let2I by auto
    have "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f  (x, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma>"  using wfG_cons2I wfX_wfY wfS_let2I by metis
    hence "\<Theta>; \<B>; (x, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>'" using wf_weakening2(6) wfS_let2I by force
    thus  \<open> \<Theta> ; \<Phi>  ; \<B> ; (x, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma> ; \<Delta>' \<turnstile>\<^sub>w\<^sub>f s2 : b \<close> using  wfS_let2I by metis
    show \<open>atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>', s1, b,\<tau>)\<close> using wfS_let2I by auto
  qed
next
  case (wfS_ifI \<Theta> \<B> \<Gamma> v \<Phi> \<Delta> s1 b s2)
  then show ?case using wf_intros by metis
next
  case (wfS_varI \<Theta> \<B> \<Gamma> \<tau> v u \<Phi> \<Delta> b s)
  show ?case proof
    show \<open> \<Theta>; \<B>; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<tau> \<close> using wfS_varI by auto
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b_of \<tau> \<close>  using wfS_varI by auto
    show \<open>atom u \<sharp>  (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>', \<tau>, v, b)\<close>  using wfS_varI setD.simps by auto
    have "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f (u, \<tau>)  #\<^sub>\<Delta> \<Delta>'" using wfS_varI wfD_cons setD.simps u_fresh_d by metis 
    thus  \<open> \<Theta> ; \<Phi>  ; \<B> ; \<Gamma> ; (u, \<tau>)  #\<^sub>\<Delta> \<Delta>' \<turnstile>\<^sub>w\<^sub>f s : b \<close>  using wfS_varI setD.simps by blast
  qed
next
  case (wfS_assignI u \<tau> \<Delta> \<Theta> \<B> \<Gamma> \<Phi> v)
  show ?case proof
    show \<open>(u, \<tau>) \<in> setD \<Delta>'\<close> using wfS_assignI setD.simps by auto
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>' \<close> using wfS_assignI by auto
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wfS_assignI by auto
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b_of \<tau> \<close> using wfS_assignI by auto
  qed
next
  case (wfS_whileI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 s2 b)
  then show ?case using wf_intros by metis
next
  case (wfS_seqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 s2 b)
  then show ?case using wf_intros by metis
next
  case (wfS_matchI \<Theta> \<B> \<Gamma> v tid dclist \<Delta> \<Phi> cs b)
  then show ?case using wf_intros by metis
next
  case (wfS_branchI \<Theta> \<Phi> \<B> x \<tau> \<Gamma> \<Delta> s b tid dc)
  show ?case proof
    have "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f  (x, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma>"  using wfG_cons2I wfX_wfY wfS_branchI by metis
    hence "\<Theta>; \<B>; (x, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>'" using wf_weakening2(6) wfS_branchI by force
    thus  \<open> \<Theta> ; \<Phi>  ; \<B> ; (x, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma> ; \<Delta>' \<turnstile>\<^sub>w\<^sub>f s : b \<close> using wfS_branchI by simp
    show \<open> atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>', \<Gamma>, \<tau>)\<close> using wfS_branchI by auto
    show \<open> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>' \<close> using wfS_branchI by auto
  qed
next
  case (wfS_finalI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist' cs b dclist)
  then show ?case using wf_intros by metis
next
  case (wfS_cons \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist' cs b css dclist)
  then show ?case using wf_intros by metis
qed(auto+)

section \<open>Useful well-formedness instances\<close>

text \<open>Well-formedness for particular constructs that we will need later\<close>

lemma wfC_e_eq:
  fixes ce::ce and \<Gamma>::\<Gamma>
  assumes "\<Theta> ;  \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce : b" and "atom x \<sharp> \<Gamma> "
  shows "\<Theta> ;  \<B> ; ((x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>)  \<turnstile>\<^sub>w\<^sub>f (CE_val (V_var x)  ==  ce )"
proof - 
  have "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b" using assms wfX_wfB by auto
  hence wbg: "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>" using wfX_wfY assms by auto
  show ?thesis proof
    show *:"\<Theta> ;  \<B> ; (x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_val (V_var x) : b"
    proof(rule)     
      show "\<Theta> ;  \<B> ; (x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_var x : b " proof
        show "\<Theta>  ;  \<B> \<turnstile>\<^sub>w\<^sub>f (x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma> " using wfG_cons2I wfX_wfY assms \<open>\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b\<close> by auto
        show "Some (b, TRUE) = lookup ((x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>) x" using lookup.simps by auto
      qed
    qed
    show "\<Theta> ;  \<B> ; (x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f ce : b"
      using assms wf_weakening1(8)[OF assms(1), of "(x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma> "] * toSet.simps wfX_wfY
      by (metis Un_subset_iff equalityE)
  qed
qed

lemma wfC_e_eq2:
  fixes e1::ce and e2::ce
  assumes  "\<Theta>  ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f e1 : b"  and  "\<Theta>  ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f e2 : b"  and " \<turnstile>\<^sub>w\<^sub>f \<Theta>" and "atom x \<sharp> \<Gamma>"
  shows "\<Theta>; \<B>; (x, b, (CE_val (V_var x)) == e1)   #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f  (CE_val (V_var x)) == e2 "
proof(rule wfC_eqI)
  have *: "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f (x, b, CE_val (V_var x)  ==  e1 )  #\<^sub>\<Gamma> \<Gamma>" proof(rule wfG_cons1I )
    show "(CE_val (V_var x)  ==  e1 ) \<notin> {TRUE, FALSE}" by auto
    show "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>" using assms wfX_wfY by metis
    show *:"atom x \<sharp> \<Gamma>" using assms by auto
    show "\<Theta>; \<B>; (x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f CE_val (V_var x)  ==  e1" using wfC_e_eq assms * by auto
    show "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b" using assms wfX_wfB by auto
  qed
  show "\<Theta>; \<B>; (x, b, CE_val (V_var x)  ==  e1 )  #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_val (V_var x) : b" using assms * wfCE_valI wfV_varI by auto
  show "\<Theta>; \<B>; (x, b, CE_val (V_var x)  ==  e1 )  #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f e2 : b" proof(rule wf_weakening1(8))
    show "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f e2 : b " using assms by auto
    show "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f (x, b, CE_val (V_var x)  ==  e1 )  #\<^sub>\<Gamma> \<Gamma>" using * by auto
    show "toSet \<Gamma> \<subseteq> toSet ((x, b, CE_val (V_var x)  ==  e1 )  #\<^sub>\<Gamma> \<Gamma>)" by auto
  qed
qed

lemma wfT_wfT_if_rev:
  assumes "wfV P \<B> \<Gamma> v  (base_for_lit l)" and "wfT P \<B> \<Gamma> t" and \<open>atom z1 \<sharp> \<Gamma>\<close>
  shows "wfT P \<B> \<Gamma> (\<lbrace> z1 : b_of t  | CE_val v  ==  CE_val (V_lit l) IMP  (c_of t z1)  \<rbrace>)"
proof
  show \<open> P; \<B>  \<turnstile>\<^sub>w\<^sub>f b_of t \<close> using wfX_wfY assms by meson
  have wfg: " P; \<B>  \<turnstile>\<^sub>w\<^sub>f  (z1, b_of t, TRUE)  #\<^sub>\<Gamma> \<Gamma>" using assms wfV_wf  wfG_cons2I wfX_wfY 
    by (meson wfG_cons_TRUE)
  show \<open> P; \<B> ; (z1, b_of t, TRUE)  #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f [ v ]\<^sup>c\<^sup>e  ==  [ [ l ]\<^sup>v ]\<^sup>c\<^sup>e   IMP  c_of t z1  \<close> proof
    show *: \<open> P; \<B> ; (z1, b_of t, TRUE)  #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f [ v ]\<^sup>c\<^sup>e  ==  [ [ l ]\<^sup>v ]\<^sup>c\<^sup>e  \<close> 
    proof(rule wfC_eqI[where b="base_for_lit l"])
      show "P; \<B> ; (z1, b_of t, TRUE)  #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f [ v ]\<^sup>c\<^sup>e : base_for_lit l" 
        using assms wf_intros wf_weakening wfg   by (meson wfV_weakening_cons)
      show "P; \<B> ; (z1, b_of t, TRUE)  #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f [ [ l ]\<^sup>v ]\<^sup>c\<^sup>e : base_for_lit l" using wfg assms wf_intros wf_weakening wfV_weakening_cons by meson
    qed    
    have " t = \<lbrace> z1 : b_of t | c_of t z1 \<rbrace>" using c_of_eq 
      using assms(2) assms(3) b_of_c_of_eq wfT_x_fresh by auto
    thus  \<open> P; \<B> ; (z1, b_of t, TRUE)  #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c_of t z1 \<close> using wfT_wfC assms wfG_elims * by simp
  qed
  show \<open>atom z1 \<sharp>  (P, \<B>, \<Gamma>)\<close> using assms wfG_fresh_x wfX_wfY by metis
qed

lemma wfT_eq_imp:
  fixes zz::x and ll::l and \<tau>'::\<tau>
  assumes "base_for_lit ll = B_bool" and "\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f \<tau>'" and
          "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f (x, b_of \<lbrace> z' : B_bool  | TRUE \<rbrace>, c_of \<lbrace> z' : B_bool  | TRUE \<rbrace> x)  #\<^sub>\<Gamma> GNil" and "atom zz \<sharp> x"
  shows "\<Theta> ; {||} ; (x, b_of \<lbrace> z' : B_bool  | TRUE \<rbrace>, c_of \<lbrace> z' : B_bool  | TRUE \<rbrace> x)  #\<^sub>\<Gamma>
                 GNil   \<turnstile>\<^sub>w\<^sub>f \<lbrace> zz : b_of \<tau>'  | [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ ll ]\<^sup>v ]\<^sup>c\<^sup>e   IMP  c_of \<tau>' zz  \<rbrace>"
proof(rule wfT_wfT_if_rev)
  show \<open> \<Theta> ; {||} ; (x, b_of \<lbrace> z' : B_bool  | TRUE \<rbrace>, c_of \<lbrace> z' : B_bool  | TRUE \<rbrace> x)  #\<^sub>\<Gamma> GNil \<turnstile>\<^sub>w\<^sub>f [ x ]\<^sup>v : base_for_lit ll \<close> 
    using wfV_varI lookup.simps base_for_lit.simps assms by simp
  show \<open> \<Theta> ; {||} ; (x, b_of \<lbrace> z' : B_bool  | TRUE \<rbrace>, c_of \<lbrace> z' : B_bool  | TRUE \<rbrace> x)  #\<^sub>\<Gamma> GNil   \<turnstile>\<^sub>w\<^sub>f \<tau>' \<close> 
    using wf_weakening assms toSet.simps by auto
  show \<open>atom zz \<sharp> (x, b_of \<lbrace> z' : B_bool  | TRUE \<rbrace>, c_of \<lbrace> z' : B_bool  | TRUE \<rbrace> x)  #\<^sub>\<Gamma> GNil\<close> 
    unfolding fresh_GCons fresh_prod3 b_of.simps c_of_true 
    using x_fresh_b fresh_GNil   c_of_true c.fresh assms by metis
qed

lemma wfC_v_eq:
  fixes ce::ce and \<Gamma>::\<Gamma> and v::v
  assumes "\<Theta> ;  \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b" and "atom x \<sharp> \<Gamma> "
  shows "\<Theta> ;  \<B> ; ((x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>)  \<turnstile>\<^sub>w\<^sub>f (CE_val (V_var x)  ==  CE_val v )"
  using wfC_e_eq wfCE_valI assms wfX_wfY  by auto

lemma wfT_e_eq:
  fixes ce::ce
  assumes "\<Theta> ;  \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce : b" and "atom z \<sharp> \<Gamma>"
  shows "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | CE_val (V_var z) == ce \<rbrace>"
proof
  show "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b" using wfX_wfB assms by auto
  show " atom z \<sharp> (\<Theta>, \<B>, \<Gamma>)" using assms wfG_fresh_x wfX_wfY by metis
  show "\<Theta> ;  \<B> ; (z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_val (V_var z)  ==  ce "
    using wfTI wfC_e_eq assms wfTI by auto
qed

lemma wfT_v_eq:
  assumes " wfB \<Theta> \<B> b" and "wfV  \<Theta> \<B> \<Gamma> v b" and "atom z \<sharp> \<Gamma>"
  shows "wfT \<Theta> \<B> \<Gamma> \<lbrace> z : b | C_eq (CE_val (V_var z)) (CE_val v)\<rbrace>"
  using wfT_e_eq wfE_valI assms wfX_wfY 
  by (simp add: wfCE_valI)

lemma wfC_wfG:
  fixes \<Gamma>::\<Gamma> and c::c and b::b
  assumes "\<Theta> ; B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c" and "\<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f b" and "atom x \<sharp> \<Gamma>" 
  shows "\<Theta> ; B \<turnstile>\<^sub>w\<^sub>f (x,b,c)#\<^sub>\<Gamma> \<Gamma>" 
proof - 
  have " \<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>" using wfG_cons2I assms wfX_wfY by fast
  hence " \<Theta> ; B ; (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c " using wfC_weakening assms by force
  thus ?thesis using wfG_consI assms wfX_wfY by metis
qed

section \<open>Replacing the constraint on a variable in a context\<close>

lemma wfG_cons_fresh2:
  fixes \<Gamma>'::\<Gamma>
  assumes "wfG P \<B> (( (x',b',c')  #\<^sub>\<Gamma> \<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>))"
  shows "x'\<noteq>x" 
proof - 
  have "atom x' \<sharp> (\<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>)" 
    using assms wfG_elims(2) by blast
  thus ?thesis 
    using  fresh_gamma_append[of "atom x'" \<Gamma>' "(x, b, c)  #\<^sub>\<Gamma> \<Gamma>"] fresh_GCons fresh_prod3[of "atom x'" x b c] by auto
qed

lemma replace_in_g_inside:
  fixes \<Gamma>::\<Gamma>
  assumes "wfG P \<B> (\<Gamma>'@((x,b0,c0') #\<^sub>\<Gamma>\<Gamma>))" 
  shows "replace_in_g (\<Gamma>'@((x,b0,c0') #\<^sub>\<Gamma>\<Gamma>)) x c0 = (\<Gamma>'@((x,b0,c0) #\<^sub>\<Gamma>\<Gamma>))"
using assms proof(induct \<Gamma>' rule: \<Gamma>_induct)
  case GNil
  then show ?case using replace_in_g.simps by auto
next
  case (GCons x' b' c' \<Gamma>'')
  hence "P; \<B> \<turnstile>\<^sub>w\<^sub>f ((x', b', c')  #\<^sub>\<Gamma> (\<Gamma>''@ (x, b0, c0')  #\<^sub>\<Gamma> \<Gamma> ))" by simp
  hence "x \<noteq> x'" using  wfG_cons_fresh2 by metis
  then show ?case using replace_in_g.simps GCons  by (simp add: wfG_cons)
qed

lemma wfG_supp_rig_eq:
  fixes \<Gamma>::\<Gamma>
  assumes  "wfG P \<B> (\<Gamma>'' @ (x, b0, c0)  #\<^sub>\<Gamma> \<Gamma>)" and "wfG P \<B> (\<Gamma>'' @ (x, b0, c0')  #\<^sub>\<Gamma> \<Gamma>)"
  shows "supp (\<Gamma>'' @ (x, b0, c0')  #\<^sub>\<Gamma> \<Gamma>) \<union> supp \<B> = supp (\<Gamma>'' @ (x, b0, c0)  #\<^sub>\<Gamma> \<Gamma>) \<union> supp \<B>"
using assms proof(induct \<Gamma>'')
  case GNil
  have "supp (GNil @ (x, b0, c0')  #\<^sub>\<Gamma> \<Gamma>) \<union> supp \<B>  = supp ((x, b0, c0')  #\<^sub>\<Gamma> \<Gamma>) \<union> supp \<B>" using supp_Cons supp_GNil by auto
  also have "... = supp x \<union> supp b0 \<union> supp c0' \<union> supp \<Gamma> \<union> supp \<B> " using supp_GCons by auto
  also have "... = supp x \<union> supp b0 \<union> supp c0 \<union> supp \<Gamma> \<union> supp \<B> " using GNil wfG_wfC[THEN wfC_supp_cons(2) ] by fastforce
  also have "... =  (supp ((x, b0, c0)  #\<^sub>\<Gamma> \<Gamma>)) \<union> supp \<B> " using supp_GCons by auto
  finally have "supp (GNil @ (x, b0, c0')  #\<^sub>\<Gamma> \<Gamma>) \<union> supp \<B> = supp (GNil @ (x, b0, c0)  #\<^sub>\<Gamma> \<Gamma>) \<union> supp \<B>" using supp_Cons supp_GNil by auto
  then show ?case using supp_GCons wfG_cons2 by auto
next
  case (GCons xbc \<Gamma>1)
  moreover have " (xbc  #\<^sub>\<Gamma> \<Gamma>1) @ (x, b0, c0)  #\<^sub>\<Gamma> \<Gamma>  =  (xbc  #\<^sub>\<Gamma> (\<Gamma>1 @ (x, b0, c0)  #\<^sub>\<Gamma> \<Gamma>))"  by simp
  moreover have " (xbc  #\<^sub>\<Gamma> \<Gamma>1) @ (x, b0, c0')  #\<^sub>\<Gamma> \<Gamma>  =  (xbc  #\<^sub>\<Gamma> (\<Gamma>1 @ (x, b0, c0')  #\<^sub>\<Gamma> \<Gamma>))"  by simp
  ultimately have  "(P; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>1 @ ((x, b0, c0)  #\<^sub>\<Gamma> \<Gamma>))  \<and>  P; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>1 @ ((x, b0, c0')  #\<^sub>\<Gamma> \<Gamma>)" using wfG_cons2 by metis
  thus ?case using GCons supp_GCons by auto
qed

lemma fresh_replace_inside[ms_fresh]:
  fixes y::x and \<Gamma>::\<Gamma>
  assumes  "wfG P \<B> (\<Gamma>'' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>)" and "wfG P \<B> (\<Gamma>'' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>)"
  shows "atom y \<sharp> (\<Gamma>'' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>) = atom y \<sharp> (\<Gamma>'' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>)"
  unfolding fresh_def  using wfG_supp_rig_eq assms x_not_in_b_set by fast

lemma wf_replace_inside1:
  fixes \<Gamma>::\<Gamma> and \<Phi>::\<Phi> and \<Theta>::\<Theta> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and c''::c and c'::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and b'::b and b::b and s::s  
           and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def and cs::branch_s and css::branch_list

shows  wfV_replace_inside: "\<Theta>; \<B>; G \<turnstile>\<^sub>w\<^sub>f v : b' \<Longrightarrow> G =  (\<Gamma>' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>) \<Longrightarrow> \<Theta>; \<B>; ((x,b,TRUE) #\<^sub>\<Gamma>\<Gamma>) \<turnstile>\<^sub>w\<^sub>f c \<Longrightarrow> \<Theta> ;  \<B> ; (\<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>) \<turnstile>\<^sub>w\<^sub>f v : b'" and
       wfC_replace_inside: "\<Theta>; \<B>; G  \<turnstile>\<^sub>w\<^sub>f c'' \<Longrightarrow> G =  (\<Gamma>' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>) \<Longrightarrow> \<Theta>; \<B>; ((x,b,TRUE) #\<^sub>\<Gamma>\<Gamma>) \<turnstile>\<^sub>w\<^sub>f c \<Longrightarrow> \<Theta> ;  \<B> ; (\<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>) \<turnstile>\<^sub>w\<^sub>f  c''" and
       wfG_replace_inside: "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f G \<Longrightarrow> G =  (\<Gamma>' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>) \<Longrightarrow> \<Theta>; \<B>; ((x,b,TRUE) #\<^sub>\<Gamma>\<Gamma>) \<turnstile>\<^sub>w\<^sub>f c \<Longrightarrow>   \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f  (\<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>) " and
       wfT_replace_inside: "\<Theta>; \<B>; G \<turnstile>\<^sub>w\<^sub>f \<tau> \<Longrightarrow> G =  (\<Gamma>' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>) \<Longrightarrow> \<Theta>; \<B>; ((x,b,TRUE) #\<^sub>\<Gamma>\<Gamma>) \<turnstile>\<^sub>w\<^sub>f c \<Longrightarrow>  \<Theta> ;  \<B> ; (\<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>) \<turnstile>\<^sub>w\<^sub>f  \<tau>" and
       "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ts \<Longrightarrow>  True" and 
       "\<turnstile>\<^sub>w\<^sub>f P \<Longrightarrow> True" and
        "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b \<Longrightarrow> True" and  
       wfCE_replace_inside: "\<Theta> ;  \<B> ; G  \<turnstile>\<^sub>w\<^sub>f ce : b' \<Longrightarrow> G =  (\<Gamma>' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>) \<Longrightarrow> \<Theta>; \<B>; ((x,b,TRUE) #\<^sub>\<Gamma>\<Gamma>) \<turnstile>\<^sub>w\<^sub>f c \<Longrightarrow> \<Theta> ;  \<B> ; (\<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>) \<turnstile>\<^sub>w\<^sub>f ce : b'" and
       "\<Theta>  \<turnstile>\<^sub>w\<^sub>f td \<Longrightarrow>   True"
proof(nominal_induct   
          b' and  c'' and G and \<tau> and ts and P and b and b' and td 
      avoiding: \<Gamma>' c'
rule:wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.strong_induct)
  case (wfV_varI \<Theta> \<B> \<Gamma>2 b2 c2 x2)
  then show ?case using wf_intros by (metis lookup_in_rig_eq lookup_in_rig_neq replace_in_g_inside)
next
  case (wfV_conspI s bv dclist \<Theta> dc x1 b' c1 \<B> b1 \<Gamma>1 v)
  show ?case proof
    show \<open>AF_typedef_poly s bv dclist \<in> set \<Theta>\<close> using wfV_conspI by auto
    show \<open>(dc, \<lbrace> x1 : b'  | c1 \<rbrace>) \<in> set dclist\<close> using wfV_conspI by auto
    show \<open> \<Theta> ;  \<B>   \<turnstile>\<^sub>w\<^sub>f b1 \<close> using wfV_conspI by auto
    show *: \<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b'[bv::=b1]\<^sub>b\<^sub>b \<close> using wfV_conspI by auto
    moreover have "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>" using wfV_wf wfV_conspI by simp
    ultimately have "atom bv \<sharp> \<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>" unfolding fresh_def using wfV_wf  wfG_supp_rig_eq  wfV_conspI 
      by (metis Un_iff fresh_def)
    thus \<open>atom bv \<sharp> (\<Theta>, \<B>, \<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>, b1, v)\<close>  
      unfolding fresh_prodN using fresh_prodN wfV_conspI by metis    
  qed
next
  case (wfTI z \<Theta> \<B> G  b1 c1)
  show ?case proof
    show \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b1 \<close> using wfTI by auto

    have "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f (x, b, c)  #\<^sub>\<Gamma> \<Gamma>" using wfG_consI  wfTI  wfG_cons  wfX_wfY by metis
    moreover hence *:"wfG \<Theta> \<B> (\<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>)"  using wfX_wfY 
       by (metis append_g.simps(2) wfG_cons2 wfTI.hyps wfTI.prems(1) wfTI.prems(2))
    hence \<open>atom z \<sharp> \<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>\<close> 
      using fresh_replace_inside[of \<Theta> \<B> \<Gamma>' x b c \<Gamma> c' z,OF *] wfTI wfX_wfY wfG_elims by metis
    thus \<open>atom z \<sharp> (\<Theta>, \<B>, \<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>)\<close> using wfG_fresh_x[OF *] by auto 

    have "(z, b1, TRUE)  #\<^sub>\<Gamma> G = ((z, b1, TRUE)  #\<^sub>\<Gamma> \<Gamma>') @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>" 
      using wfTI append_g.simps by metis
    thus \<open> \<Theta>; \<B>; (z, b1, TRUE)  #\<^sub>\<Gamma> \<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c1 \<close> 
      using wfTI(9)[OF _ wfTI(11)] by fastforce
  qed
next
  case (wfG_nilI \<Theta>)
  hence "GNil = (x, b, c')  #\<^sub>\<Gamma> \<Gamma>" using append_g.simps \<Gamma>.distinct GNil_append by auto
  hence "False" using \<Gamma>.distinct by auto
  then show ?case by auto
next
  case (wfG_cons1I c1 \<Theta> \<B> G x1 b1)
  show  ?case proof(cases "\<Gamma>'=GNil")
    case True
    then show ?thesis using wfG_cons1I wfG_consI by auto
  next
    case False
    then  obtain G'::\<Gamma> where *:"(x1, b1, c1)  #\<^sub>\<Gamma> G' = \<Gamma>'" using wfG_cons1I wfG_cons1I(7) GCons_eq_append_conv by auto
    hence **:" G = G' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>" using wfG_cons1I by auto
    hence " \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f G' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>" using  wfG_cons1I by auto
    have "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f (x1, b1, c1)  #\<^sub>\<Gamma> G' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>" proof(rule Wellformed.wfG_cons1I)
      show "c1 \<notin> {TRUE, FALSE}" using wfG_cons1I by auto
      show "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f G' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma> " using wfG_cons1I(3)[of G',OF **] wfG_cons1I by auto
      show "atom x1 \<sharp> G' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>"  using wfG_cons1I * ** fresh_replace_inside  by metis
      show "\<Theta>; \<B>; (x1, b1, TRUE)  #\<^sub>\<Gamma> G' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c1" using wfG_cons1I(6)[of " (x1, b1, TRUE)  #\<^sub>\<Gamma> G'"] wfG_cons1I ** by auto
      show "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b1" using wfG_cons1I by auto
    qed
    thus ?thesis using * by auto
  qed
next
  case (wfG_cons2I c1 \<Theta> \<B> G x1 b1)
   show  ?case proof(cases "\<Gamma>'=GNil")
    case True
    then show ?thesis using wfG_cons2I wfG_consI by auto
  next
    case False
    then  obtain G'::\<Gamma> where *:"(x1, b1, c1)  #\<^sub>\<Gamma> G' = \<Gamma>'" using wfG_cons2I GCons_eq_append_conv by auto
    hence **:" G = G' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>" using wfG_cons2I by auto
    moreover have " \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f G' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>" using wfG_cons2I * ** by auto
    moreover hence "atom x1 \<sharp> G' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>" using wfG_cons2I * ** fresh_replace_inside  by metis
    ultimately show  ?thesis using Wellformed.wfG_cons2I[OF wfG_cons2I(1), of \<Theta> \<B> "G'@ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>"  x1 b1] wfG_cons2I * ** by auto
  qed
qed(metis  wf_intros )+

lemma wf_replace_inside2:
  fixes \<Gamma>::\<Gamma> and \<Phi>::\<Phi> and \<Theta>::\<Theta> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and c''::c and c'::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and b'::b and b::b and s::s  
           and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def and cs::branch_s and css::branch_list
shows 
       "\<Theta> ; \<Phi> ;  \<B> ; G ; D  \<turnstile>\<^sub>w\<^sub>f e : b' \<Longrightarrow> G =  (\<Gamma>' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>) \<Longrightarrow> \<Theta>; \<B>; ((x,b,TRUE) #\<^sub>\<Gamma>\<Gamma>) \<turnstile>\<^sub>w\<^sub>f c \<Longrightarrow> \<Theta> ; \<Phi> ;  \<B> ; (\<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>); D \<turnstile>\<^sub>w\<^sub>f e : b'" and
       "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b \<Longrightarrow> True" and
       "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f cs : b \<Longrightarrow> True" and
       "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b \<Longrightarrow> True" and
       "\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> \<Longrightarrow> True" and
       "\<Theta>; \<B>; G  \<turnstile>\<^sub>w\<^sub>f \<Delta> \<Longrightarrow>  G =  (\<Gamma>' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>) \<Longrightarrow> \<Theta>; \<B>; ((x,b,TRUE) #\<^sub>\<Gamma>\<Gamma>) \<turnstile>\<^sub>w\<^sub>f c \<Longrightarrow> \<Theta> ;  \<B> ; (\<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>) \<turnstile>\<^sub>w\<^sub>f \<Delta>" and     
       "\<Theta> ; \<Phi>   \<turnstile>\<^sub>w\<^sub>f ftq \<Longrightarrow> True" and
       "\<Theta> ; \<Phi>  ; \<B> \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow>   True"
proof(nominal_induct   
          b' and b and b and b and  \<Phi> and \<Delta> and  ftq and ft 
      avoiding: \<Gamma>' c'
      rule:wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.strong_induct)
case (wfE_valI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v b)
  then show ?case using wf_replace_inside1 Wellformed.wfE_valI by auto
next
  case (wfE_plusI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_replace_inside1 Wellformed.wfE_plusI by auto
next
  case (wfE_leqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_replace_inside1 Wellformed.wfE_leqI by auto
next
  case (wfE_eqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b v2)
  then show ?case using wf_replace_inside1 Wellformed.wfE_eqI by metis
next
  case (wfE_fstI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case using wf_replace_inside1 Wellformed.wfE_fstI by metis
next
  case (wfE_sndI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case using wf_replace_inside1 Wellformed.wfE_sndI by metis
next
  case (wfE_concatI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_replace_inside1 Wellformed.wfE_concatI by auto
next
  case (wfE_splitI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case using wf_replace_inside1 Wellformed.wfE_splitI by auto
next
  case (wfE_lenI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1)
  then show ?case using wf_replace_inside1 Wellformed.wfE_lenI by metis
next
  case (wfE_appI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> f x b c \<tau> s v)
  then show ?case using wf_replace_inside1 Wellformed.wfE_appI by metis
next
  case (wfE_appPI \<Theta> \<Phi> \<B> \<Gamma>'' \<Delta> b' bv v \<tau> f x1 b1 c1 s)
  show ?case proof
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wfE_appPI by auto
    show \<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<close> using wfE_appPI by auto
    show \<open> \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b' \<close> using wfE_appPI by auto
    show *:\<open> \<Theta>; \<B>; \<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b1[bv::=b']\<^sub>b \<close> using wfE_appPI wf_replace_inside1 by auto

    moreover have "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>" using wfV_wf wfE_appPI by metis
    ultimately have "atom bv \<sharp>  \<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>"  
      unfolding fresh_def using wfV_wf wfG_supp_rig_eq wfE_appPI Un_iff fresh_def  by metis 

    thus  \<open>atom bv \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>, \<Delta>, b', v, (b_of \<tau>)[bv::=b']\<^sub>b)\<close>
      using wfE_appPI  fresh_prodN by metis
    show \<open>Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x1 b1 c1 \<tau> s))) = lookup_fun \<Phi> f\<close> using wfE_appPI by auto
  qed
next
  case (wfE_mvarI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> u \<tau>)
  then show ?case using wf_replace_inside1 Wellformed.wfE_mvarI by metis
next
  case (wfD_emptyI \<Theta> \<B> \<Gamma>)
  then show ?case using wf_replace_inside1 Wellformed.wfD_emptyI by metis
next
  case (wfD_cons \<Theta> \<B> \<Gamma> \<Delta> \<tau> u)
  then show ?case using wf_replace_inside1 Wellformed.wfD_emptyI 
    by (simp add: wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.wfD_cons)
next
  case (wfFTNone \<Theta> \<Phi> ft)
  then show ?case using wf_replace_inside1 Wellformed.wfD_emptyI by metis
next
  case (wfFTSome \<Theta> \<Phi> bv ft)
  then show ?case using wf_replace_inside1 Wellformed.wfD_emptyI by metis
qed(auto)

lemmas wf_replace_inside = wf_replace_inside1 wf_replace_inside2

lemma wfC_replace_cons:
  assumes "wfG P \<B> ((x,b,c1) #\<^sub>\<Gamma>\<Gamma>)" and "wfC P \<B> ((x,b,TRUE) #\<^sub>\<Gamma>\<Gamma>) c2" 
  shows "wfC P \<B> ((x,b,c1) #\<^sub>\<Gamma>\<Gamma>) c2" 
proof -
  have "wfC P \<B> (GNil@((x,b,c1) #\<^sub>\<Gamma>\<Gamma>)) c2" proof(rule wf_replace_inside1(2))
    show " P; \<B> ; (x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c2 " using wfG_elim2 assms by auto
    show \<open>(x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma> = GNil @ (x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>\<close> using append_g.simps by auto
    show \<open>P; \<B> ; (x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c1  \<close>  using wfG_elim2 assms by auto
  qed
  thus ?thesis using append_g.simps by auto
qed

lemma wfC_refl:
  assumes "wfG \<Theta> \<B> ((x, b', c') #\<^sub>\<Gamma>\<Gamma>)" 
  shows   "wfC \<Theta> \<B> ((x, b', c') #\<^sub>\<Gamma>\<Gamma>) c'"
  using wfG_wfC assms wfC_replace_cons by auto

lemma wfG_wfC_inside:
  assumes " (x, b, c)  \<in> toSet G" and "wfG \<Theta> B G" 
  shows  "wfC \<Theta> B G c"
  using assms proof(induct G rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x' b' c' \<Gamma>')
  then consider (hd) "(x, b, c) = (x',b',c')" | (tail) "(x, b, c) \<in> toSet \<Gamma>'" using toSet.simps by auto
  then show ?case proof(cases)
    case hd
    then show ?thesis using GCons wf_weakening
      by (metis wfC_replace_cons wfG_cons_wfC)
  next
    case tail
    then show ?thesis using GCons wf_weakening 
      by (metis insert_iff insert_is_Un subsetI toSet.simps(2) wfG_cons2)
  qed
qed

lemma wfT_wf_cons3:
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c \<rbrace>" and "atom y \<sharp> (c,\<Gamma>)"
  shows  "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f (y, b, c[z::=V_var y]\<^sub>c\<^sub>v)  #\<^sub>\<Gamma>  \<Gamma>"
proof -
  have "\<lbrace> z : b | c \<rbrace> = \<lbrace> y : b |  (y \<leftrightarrow> z) \<bullet> c \<rbrace>" using type_eq_flip assms by auto
  moreover hence " (y \<leftrightarrow> z) \<bullet> c = c[z::=V_var y]\<^sub>c\<^sub>v" using  assms subst_v_c_def by auto
  ultimately have "\<lbrace> z : b | c \<rbrace> = \<lbrace> y : b |  c[z::=V_var y]\<^sub>c\<^sub>v \<rbrace>" by metis
  thus  ?thesis using assms wfT_wf_cons[of \<Theta> \<B> \<Gamma> y b] fresh_Pair by metis
qed

lemma wfT_wfC_cons:
  assumes "wfT P \<B> \<Gamma> \<lbrace> z1 : b  | c1 \<rbrace>" and "wfT P \<B> \<Gamma> \<lbrace> z2 : b  | c2 \<rbrace>"  and "atom x \<sharp> (c1,c2,\<Gamma>)"
  shows "wfC P \<B> ((x,b,c1[z1::=V_var x]\<^sub>v) #\<^sub>\<Gamma>\<Gamma>) (c2[z2::=V_var x]\<^sub>v)" (is "wfC P \<B> ?G ?c")
proof -
  have eq: "\<lbrace> z2 : b  | c2 \<rbrace> = \<lbrace> x : b | c2[z2::=V_var x]\<^sub>c\<^sub>v \<rbrace>" using type_eq_subst assms fresh_prod3 by simp
  have eq2: "\<lbrace> z1 : b  | c1 \<rbrace> = \<lbrace> x : b | c1[z1::=V_var x]\<^sub>c\<^sub>v \<rbrace>" using type_eq_subst assms fresh_prod3 by simp
  moreover have "wfT P \<B> \<Gamma> \<lbrace> x : b  | c1[z1::=V_var x]\<^sub>c\<^sub>v \<rbrace>" using assms eq2 by auto
  moreover hence "wfG P \<B> ((x,b,c1[z1::=V_var x]\<^sub>c\<^sub>v) #\<^sub>\<Gamma>\<Gamma>)" using wfT_wf_cons fresh_prod3 assms by auto
  moreover have "wfT P \<B> \<Gamma> \<lbrace> x : b  | c2[z2::=V_var x]\<^sub>c\<^sub>v \<rbrace>" using assms eq by auto
  moreover hence "wfC P \<B> ((x,b,TRUE) #\<^sub>\<Gamma>\<Gamma>)  (c2[z2::=V_var x]\<^sub>c\<^sub>v)" using wfT_wfC assms fresh_prod3 by simp
  ultimately show ?thesis using wfC_replace_cons subst_v_c_def by simp
qed

lemma wfT_wfC2:
  fixes c::c  and x::x
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c \<rbrace>" and "atom x \<sharp> \<Gamma>"
  shows "\<Theta>; \<B>; (x,b,TRUE)#\<^sub>\<Gamma>\<Gamma> \<turnstile>\<^sub>w\<^sub>f c[z::=[x]\<^sup>v]\<^sub>v"
proof(cases "x=z")
  case True
  then show ?thesis using wfT_wfC assms by auto
next
  case False
  hence "atom x \<sharp> c" using wfT_fresh_c assms by metis
  hence "\<lbrace> x : b  | c[z::=[ x ]\<^sup>v]\<^sub>v \<rbrace> = \<lbrace> z : b | c \<rbrace>" 
    using \<tau>.eq_iff Abs1_eq_iff(3)[of x "c[z::=[ x ]\<^sup>v]\<^sub>v" z c] 
    by (metis flip_subst_v type_eq_flip)
  hence " \<Theta>; \<B>; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f \<lbrace> x : b  | c[z::=[ x ]\<^sup>v]\<^sub>v \<rbrace>" using assms by metis
  thus ?thesis using wfT_wfC assms by auto
qed

lemma wfT_wfG: 
  fixes x::x and \<Gamma>::\<Gamma> and z::x and c::c and b::b
  assumes "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c \<rbrace>" and "atom x \<sharp> \<Gamma>" 
  shows "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f (x,b, c[z::=[ x ]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>"
proof - 
  have "\<Theta>; \<B>; (x, b, TRUE) #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c[z::=[ x ]\<^sup>v]\<^sub>v" using wfT_wfC2 assms by metis
  thus ?thesis using wfG_consI assms wfT_wfB b_of.simps wfX_wfY by metis
qed

lemma wfG_replace_inside2:
  fixes \<Gamma>::\<Gamma> 
  assumes "wfG P \<B> (\<Gamma>' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>)" and "wfG P \<B> ((x,b,c) #\<^sub>\<Gamma>\<Gamma>)"
  shows "wfG P \<B> (\<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>)"
proof - 
  have "wfC P \<B> ((x,b,TRUE) #\<^sub>\<Gamma>\<Gamma>) c" using wfG_wfC assms by auto
  thus ?thesis using wf_replace_inside1(3)[OF assms(1)] by auto
qed

lemma wfG_replace_inside_full:
  fixes \<Gamma>::\<Gamma> 
  assumes "wfG P \<B> (\<Gamma>' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>)" and "wfG P \<B> (\<Gamma>'@((x,b,c) #\<^sub>\<Gamma>\<Gamma>))"
  shows "wfG P \<B> (\<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>)"
proof - 
  have "wfG P \<B> ((x,b,c) #\<^sub>\<Gamma>\<Gamma>)" using wfG_suffix assms by auto
  thus ?thesis using wfG_replace_inside assms by auto
qed

lemma wfT_replace_inside2:
  assumes "wfT \<Theta> \<B> (\<Gamma>' @ (x, b, c')  #\<^sub>\<Gamma> \<Gamma>) t" and "wfG \<Theta> \<B> (\<Gamma>'@((x,b,c) #\<^sub>\<Gamma>\<Gamma>))"
  shows "wfT \<Theta> \<B> (\<Gamma>' @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>) t"
proof -
  have "wfG \<Theta> \<B> (((x,b,c) #\<^sub>\<Gamma>\<Gamma>))" using wfG_suffix assms by auto
  hence "wfC \<Theta> \<B> ((x,b,TRUE) #\<^sub>\<Gamma>\<Gamma>) c" using wfG_wfC by auto
  thus ?thesis   using wf_replace_inside assms by metis
qed

lemma wfD_unique:
  assumes "wfD P  \<B> \<Gamma> \<Delta>" and " (u,\<tau>') \<in> setD \<Delta>" and "(u,\<tau>) \<in> setD \<Delta>"
  shows "\<tau>'=\<tau>"
using assms  proof(induct \<Delta> rule: \<Delta>_induct)
  case DNil
  then show ?case by auto
next
  case (DCons u' t' D)
  hence *: "wfD P \<B> \<Gamma> ((u',t') #\<^sub>\<Delta> D)" using Cons by auto
  show ?case proof(cases "u=u'")
    case True
    then have "u \<notin> fst ` setD D" using wfD_elims *  by blast
    then show ?thesis using DCons by force
  next
    case False
    then show ?thesis using DCons wfD_elims *  by (metis fst_conv setD_ConsD)
  qed
qed

lemma replace_in_g_forget:
  fixes x::x
  assumes "wfG P B G"
  shows "atom x \<notin> atom_dom G \<Longrightarrow> (G[x\<longmapsto>c]) = G" and
  "atom x \<sharp> G \<Longrightarrow>  (G[x\<longmapsto>c]) = G"
proof -
  show "atom x \<notin> atom_dom G \<Longrightarrow> G[x\<longmapsto>c] = G" by (induct G rule: \<Gamma>_induct,auto)
  thus  "atom x \<sharp> G \<Longrightarrow>  (G[x\<longmapsto>c]) = G" using wfG_x_fresh assms by simp
qed

lemma replace_in_g_fresh_single:
  fixes G::\<Gamma> and x::x
  assumes  \<open>\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f G[x'\<longmapsto>c'']\<close> and "atom x \<sharp> G" and \<open>\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f G \<close>
  shows "atom x \<sharp> G[x'\<longmapsto>c'']" 
  using rig_dom_eq wfG_dom_supp assms fresh_def atom_dom.simps dom.simps by metis

section \<open>Preservation of well-formedness under substitution\<close>

lemma wfC_cons_switch:
  fixes c::c and c'::c
  assumes "\<Theta>; \<B>; (x, b, c)  #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c'"
  shows "\<Theta>; \<B>; (x, b, c')  #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c"
proof -
  have *:"\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f  (x, b, c)  #\<^sub>\<Gamma> \<Gamma>" using wfC_wf assms by auto
  hence "atom x \<sharp> \<Gamma> \<and> wfG \<Theta> \<B> \<Gamma> \<and> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b" using wfG_cons by auto
  hence " \<Theta>; \<B>; (x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f TRUE " using wfC_trueI wfG_cons2I by simp
  hence "\<Theta>; \<B>;(x, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c'" 
    using wf_replace_inside1(2)[of \<Theta> \<B> "(x, b, c)  #\<^sub>\<Gamma> \<Gamma>" c' GNil x b c \<Gamma> TRUE] assms by auto
  hence "wfG \<Theta> \<B> ((x,b,c') #\<^sub>\<Gamma>\<Gamma>)" using wf_replace_inside1(3)[OF *, of GNil x b c \<Gamma> c'] by auto
  moreover have "wfC \<Theta> \<B> ((x,b,TRUE) #\<^sub>\<Gamma>\<Gamma>) c" proof(cases "c \<in> { TRUE, FALSE }")
    case True
    have "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f  \<Gamma> \<and> atom x \<sharp> \<Gamma> \<and> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b" using wfG_elims(2)[OF *] by auto
    hence "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f  (x,b,TRUE) #\<^sub>\<Gamma> \<Gamma>" using wfG_cons_TRUE by auto
    then show ?thesis using wfC_trueI wfC_falseI True by auto
  next
    case False
    then show ?thesis using wfG_elims(2)[OF *] by auto
  qed
  ultimately show  ?thesis using wfC_replace_cons by auto
qed

lemma subst_g_inside_simple:
  fixes \<Gamma>\<^sub>1::\<Gamma> and \<Gamma>\<^sub>2::\<Gamma> 
  assumes "wfG P \<B> (\<Gamma>\<^sub>1@((x,b,c) #\<^sub>\<Gamma>\<Gamma>\<^sub>2))"
  shows "(\<Gamma>\<^sub>1@((x,b,c) #\<^sub>\<Gamma>\<Gamma>\<^sub>2))[x::=v]\<^sub>\<Gamma>\<^sub>v = \<Gamma>\<^sub>1[x::=v]\<^sub>\<Gamma>\<^sub>v@\<Gamma>\<^sub>2" 
using assms proof(induct \<Gamma>\<^sub>1 rule: \<Gamma>_induct)
  case GNil
  then show ?case using subst_gv.simps by simp
next
  case (GCons x' b' c' G)
  hence *:"P; \<B>  \<turnstile>\<^sub>w\<^sub>f (x', b', c')  #\<^sub>\<Gamma> (G @ (x, b, c)  #\<^sub>\<Gamma> \<Gamma>\<^sub>2)" by auto
  hence "x\<noteq>x'" 
    using  GCons append_Cons  wfG_cons_fresh2[OF *] by auto
  hence "((GCons (x', b', c') G) @ (GCons (x, b, c)  \<Gamma>\<^sub>2))[x::=v]\<^sub>\<Gamma>\<^sub>v  =  
         (GCons (x', b', c') (G @ (GCons (x, b, c)  \<Gamma>\<^sub>2)))[x::=v]\<^sub>\<Gamma>\<^sub>v" by auto
  also have "... =  GCons (x', b', c'[x::=v]\<^sub>c\<^sub>v) ((G @ (GCons (x, b, c)  \<Gamma>\<^sub>2))[x::=v]\<^sub>\<Gamma>\<^sub>v)"  
      using subst_gv.simps \<open>x\<noteq>x'\<close> by simp
  also have "... = (x', b', c'[x::=v]\<^sub>c\<^sub>v)  #\<^sub>\<Gamma> (G[x::=v]\<^sub>\<Gamma>\<^sub>v @  \<Gamma>\<^sub>2)" using GCons * wfG_elims by metis
  also have "... = ((x', b', c')  #\<^sub>\<Gamma> G)[x::=v]\<^sub>\<Gamma>\<^sub>v @  \<Gamma>\<^sub>2"  using subst_gv.simps \<open>x\<noteq>x'\<close>  by simp
  finally show ?case by blast
qed

lemma subst_c_TRUE_FALSE:
  fixes c::c
  assumes "c \<notin> {TRUE,FALSE}" 
  shows "c[x::=v']\<^sub>c\<^sub>v \<notin> {TRUE, FALSE}"
using assms by(nominal_induct c rule:c.strong_induct,auto simp add: subst_cv.simps)

lemma lookup_subst:
  assumes "Some (b, c) = lookup \<Gamma> x" and "x \<noteq> x'" 
  shows "\<exists>c'. Some (b,c') = lookup \<Gamma>[x'::=v']\<^sub>\<Gamma>\<^sub>v x"
using assms proof(induct \<Gamma> rule: \<Gamma>_induct)
case GNil
  then show ?case by auto
next
  case (GCons x1 b1 c1 \<Gamma>1)
  then show ?case proof(cases "x1=x'")
    case True
    then show ?thesis using subst_gv.simps GCons by auto
  next
    case False
    hence  *:"((x1, b1, c1)  #\<^sub>\<Gamma> \<Gamma>1)[x'::=v']\<^sub>\<Gamma>\<^sub>v =  ((x1, b1, c1[x'::=v']\<^sub>c\<^sub>v)  #\<^sub>\<Gamma> \<Gamma>1[x'::=v']\<^sub>\<Gamma>\<^sub>v)" using subst_gv.simps by auto
    then show ?thesis proof(cases "x1=x")
      case True
      then show ?thesis using lookup.simps *
        using GCons.prems(1) by auto
    next
      case False
      then show ?thesis using lookup.simps *
        using GCons.prems(1)  by (simp add: GCons.hyps assms(2))
    qed
  qed
qed

lemma lookup_subst2:
  assumes "Some (b, c) = lookup (\<Gamma>'@((x',b\<^sub>1,c0[z0::=[x']\<^sup>v]\<^sub>c\<^sub>v)#\<^sub>\<Gamma>\<Gamma>)) x" and "x \<noteq> x'" and
          "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f (\<Gamma>'@((x',b\<^sub>1,c0[z0::=[x']\<^sup>v]\<^sub>c\<^sub>v)#\<^sub>\<Gamma>\<Gamma>))" 
  shows "\<exists>c'. Some (b,c') = lookup (\<Gamma>'[x'::=v']\<^sub>\<Gamma>\<^sub>v@\<Gamma>) x"
  using assms lookup_subst subst_g_inside by metis

lemma wf_subst1:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and b::b and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def
  shows  wfV_subst: "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b        \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c') #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> \<Theta>; \<B>;\<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f v' : b'  \<Longrightarrow> \<Theta> ;  \<B>  ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f v[x::=v']\<^sub>v\<^sub>v : b" and
         wfC_subst: "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f  c           \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c') #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> \<Theta>; \<B>; \<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f v' : b' \<Longrightarrow> \<Theta>; \<B>;  \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f c[x::=v']\<^sub>c\<^sub>v" and
          wfG_subst: "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>                \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c') #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> \<Theta>; \<B>  ; \<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f v' : b' \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v" and
          wfT_subst: "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<tau>            \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c') #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> \<Theta>; \<B>  ; \<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f v' : b' \<Longrightarrow> \<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f \<tau>[x::=v']\<^sub>\<tau>\<^sub>v" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ts \<Longrightarrow> True" and 
         "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow>True" and
         "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b \<Longrightarrow> True " and
          wfCE_subst: "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce : b    \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c') #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> \<Theta>; \<B>  ; \<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f v' : b'  \<Longrightarrow> \<Theta> ;  \<B>  ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v  \<turnstile>\<^sub>w\<^sub>f  ce[x::=v']\<^sub>c\<^sub>e\<^sub>v : b" and
         "\<Theta>  \<turnstile>\<^sub>w\<^sub>f td \<Longrightarrow>   True"
proof(nominal_induct 
      b and c and \<Gamma> and \<tau> and ts and \<Theta> and b and  b and td 
      avoiding: x v' 
      arbitrary: \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1
      rule:wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.strong_induct)
 case (wfV_varI \<Theta> \<B> \<Gamma> b1 c1 x1)
  
  show ?case proof(cases "x1=x")
    case True
    hence "(V_var x1)[x::=v']\<^sub>v\<^sub>v = v' " using subst_vv.simps by auto
    moreover have "b' = b1" using wfV_varI True  lookup_inside_wf
      by (metis option.inject prod.inject)
    moreover have " \<Theta>; \<B>  ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f v' : b'" using  wfV_varI subst_g_inside_simple wf_weakening 
      append_g_toSetU sup_ge2  wfV_wf by metis
    ultimately show ?thesis by auto
  next
    case False
    hence "(V_var x1)[x::=v']\<^sub>v\<^sub>v = (V_var x1) " using subst_vv.simps by auto
    moreover have "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v" using wfV_varI by simp
    moreover obtain c1' where "Some (b1, c1') = lookup \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v x1"  using    wfV_varI  False  lookup_subst by metis
    ultimately show ?thesis using  Wellformed.wfV_varI[of \<Theta>  \<B> "\<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v" b1 c1' x1] by metis
  qed  
next
  case (wfV_litI \<Theta> \<Gamma> l)
  then show ?case using  subst_vv.simps  wf_intros by auto
next
  case (wfV_pairI \<Theta> \<Gamma> v1 b1 v2 b2)
  then show ?case using subst_vv.simps  wf_intros by auto
next
  case (wfV_consI s dclist \<Theta> dc x b c \<Gamma> v)
  then show ?case using subst_vv.simps  wf_intros by auto
next
  case (wfV_conspI s bv dclist \<Theta> dc x' b' c \<B> b \<Gamma> va)
  show ?case unfolding subst_vv.simps proof
    show \<open>AF_typedef_poly s bv dclist \<in> set \<Theta>\<close> and \<open>(dc, \<lbrace> x' : b'  | c \<rbrace>) \<in> set dclist\<close> using wfV_conspI by auto
    show \<open> \<Theta> ;\<B>  \<turnstile>\<^sub>w\<^sub>f b \<close> using wfV_conspI by auto
    have "atom bv \<sharp> \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v" using fresh_subst_gv_if wfV_conspI by metis
    moreover have "atom bv \<sharp> va[x::=v']\<^sub>v\<^sub>v" using wfV_conspI fresh_subst_if  by simp
    ultimately show \<open>atom bv \<sharp> (\<Theta>, \<B>, \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v, b, va[x::=v']\<^sub>v\<^sub>v)\<close> unfolding fresh_prodN  using wfV_conspI by auto
    show \<open> \<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f va[x::=v']\<^sub>v\<^sub>v : b'[bv::=b]\<^sub>b\<^sub>b \<close> using wfV_conspI by auto
  qed
next
  case (wfTI z \<Theta> \<B> \<Gamma>  b c)
  have "  \<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b  | c[x::=v']\<^sub>c\<^sub>v  \<rbrace>" proof
    have  \<open>\<Theta>; \<B>; ((z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>)[x::=v']\<^sub>\<Gamma>\<^sub>v   \<turnstile>\<^sub>w\<^sub>f c[x::=v']\<^sub>c\<^sub>v  \<close> 
    proof(rule  wfTI(9))
      show \<open>(z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma> = ((z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>\<^sub>1) @ (x, b', c')  #\<^sub>\<Gamma> \<Gamma>\<^sub>2\<close> using wfTI append_g.simps by simp
      show \<open> \<Theta>; \<B>; \<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f v' : b' \<close> using wfTI by auto
    qed
    thus *:\<open>\<Theta>; \<B>; (z, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v   \<turnstile>\<^sub>w\<^sub>f c[x::=v']\<^sub>c\<^sub>v  \<close> 
      using subst_gv.simps subst_cv.simps wfTI fresh_x_neq by auto

    have "atom z \<sharp> \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v" using fresh_subst_gv_if wfTI by metis
    moreover have "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f  \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v" using wfTI wfX_wfY wfG_elims subst_gv.simps * by metis
    ultimately show  \<open>atom z \<sharp>  (\<Theta>, \<B>, \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v)\<close> using wfG_fresh_x  by metis
    show \<open>  \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b  \<close> using wfTI by auto   
  qed
  thus ?case using subst_tv.simps wfTI by auto
next
  case (wfC_trueI \<Theta> \<Gamma>)
  then show ?case using subst_cv.simps  wf_intros by auto
next
  case (wfC_falseI \<Theta> \<Gamma>)
  then show ?case using subst_cv.simps  wf_intros by auto
next
  case (wfC_eqI \<Theta> \<B> \<Gamma> e1 b e2)
  show ?case proof(subst subst_cv.simps,rule)
    show "\<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v  \<turnstile>\<^sub>w\<^sub>f e1[x::=v']\<^sub>c\<^sub>e\<^sub>v : b " using wfC_eqI subst_dv.simps by auto
    show "\<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v  \<turnstile>\<^sub>w\<^sub>f e2[x::=v']\<^sub>c\<^sub>e\<^sub>v : b " using wfC_eqI by auto
  qed
next
  case (wfC_conjI \<Theta> \<Gamma> c1 c2)
  then show ?case using subst_cv.simps  wf_intros by auto
next
  case (wfC_disjI \<Theta> \<Gamma> c1 c2)
  then show ?case using subst_cv.simps  wf_intros by auto
next
  case (wfC_notI \<Theta> \<Gamma> c1)
  then show ?case using subst_cv.simps  wf_intros by auto
next
  case (wfC_impI \<Theta> \<Gamma> c1 c2)
  then show ?case using subst_cv.simps  wf_intros by auto
next
  case (wfG_nilI \<Theta>)
  then show ?case using subst_cv.simps  wf_intros by auto
next
  case (wfG_cons1I c \<Theta> \<B> \<Gamma> y b)

  show ?case proof(cases "x=y")
    case True
    hence "((y, b, c)  #\<^sub>\<Gamma> \<Gamma>)[x::=v']\<^sub>\<Gamma>\<^sub>v  = \<Gamma>" using subst_gv.simps by auto
    moreover have  "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma>"  using  wfG_cons1I by auto
    ultimately show ?thesis by auto
  next
    case False
    have "\<Gamma>\<^sub>1 \<noteq> GNil" using wfG_cons1I False by auto
    then obtain G where "\<Gamma>\<^sub>1 = (y, b, c)  #\<^sub>\<Gamma> G" using GCons_eq_append_conv wfG_cons1I by auto
    hence *:"\<Gamma> = G @ (x, b', c')  #\<^sub>\<Gamma> \<Gamma>\<^sub>2" using wfG_cons1I by auto
    hence  "((y, b, c)  #\<^sub>\<Gamma> \<Gamma>)[x::=v']\<^sub>\<Gamma>\<^sub>v  =(y, b, c[x::=v']\<^sub>c\<^sub>v) #\<^sub>\<Gamma>\<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v" using subst_gv.simps False by auto
    moreover have "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f (y, b, c[x::=v']\<^sub>c\<^sub>v) #\<^sub>\<Gamma>\<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v" proof(rule  Wellformed.wfG_cons1I)
      show \<open>c[x::=v']\<^sub>c\<^sub>v \<notin> {TRUE, FALSE}\<close> using wfG_cons1I subst_c_TRUE_FALSE by auto
      show \<open> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<close> using wfG_cons1I * by auto
      have "\<Gamma> = (G @ ((x, b', c') #\<^sub>\<Gamma>GNil)) @ \<Gamma>\<^sub>2" using * append_g_assoc by auto
      hence "atom y \<sharp> \<Gamma>\<^sub>2" using fresh_suffix  \<open>atom y \<sharp> \<Gamma>\<close>  by auto
      hence "atom y \<sharp> v'" using wfG_cons1I wfV_x_fresh by metis
      thus \<open>atom y \<sharp> \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v\<close> using fresh_subst_gv wfG_cons1I by auto
      have "((y, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>)[x::=v']\<^sub>\<Gamma>\<^sub>v = (y, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v" using subst_gv.simps subst_cv.simps False by auto
      thus  \<open> \<Theta>; \<B>; (y, b, TRUE)  #\<^sub>\<Gamma> \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v  \<turnstile>\<^sub>w\<^sub>f c[x::=v']\<^sub>c\<^sub>v \<close> using wfG_cons1I(6)[of "(y,b,TRUE) #\<^sub>\<Gamma>G"] * subst_gv.simps 
        wfG_cons1I by fastforce
      show "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b " using wfG_cons1I by auto
    qed
    ultimately show ?thesis by auto   
  qed
next
  case (wfG_cons2I c \<Theta> \<B> \<Gamma> y b)
  show ?case proof(cases "x=y")
    case True
    hence "((y, b, c)  #\<^sub>\<Gamma> \<Gamma>)[x::=v']\<^sub>\<Gamma>\<^sub>v  = \<Gamma>" using subst_gv.simps by auto
    moreover have  "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>"  using  wfG_cons2I by auto
    ultimately show ?thesis by auto
  next
    case False
    have "\<Gamma>\<^sub>1 \<noteq> GNil" using wfG_cons2I False by auto
    then obtain G where "\<Gamma>\<^sub>1 = (y, b, c)  #\<^sub>\<Gamma> G"  using GCons_eq_append_conv wfG_cons2I by auto
    hence *:"\<Gamma> = G @ (x, b', c')  #\<^sub>\<Gamma> \<Gamma>\<^sub>2" using wfG_cons2I by auto
    hence  "((y, b, c)  #\<^sub>\<Gamma> \<Gamma>)[x::=v']\<^sub>\<Gamma>\<^sub>v  =(y, b, c[x::=v']\<^sub>c\<^sub>v) #\<^sub>\<Gamma>\<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v" using subst_gv.simps False by auto
    moreover have "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f (y, b, c[x::=v']\<^sub>c\<^sub>v) #\<^sub>\<Gamma>\<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v" proof(rule  Wellformed.wfG_cons2I)
      show \<open>c[x::=v']\<^sub>c\<^sub>v \<in> {TRUE, FALSE}\<close> using subst_cv.simps wfG_cons2I by auto
      show \<open> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<close> using wfG_cons2I * by auto
      have "\<Gamma> = (G @ ((x, b', c') #\<^sub>\<Gamma>GNil)) @ \<Gamma>\<^sub>2" using * append_g_assoc by auto
      hence "atom y \<sharp> \<Gamma>\<^sub>2" using fresh_suffix wfG_cons2I by metis
      hence "atom y \<sharp> v'" using wfG_cons2I  wfV_x_fresh by metis
      thus \<open>atom y \<sharp> \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v\<close> using fresh_subst_gv wfG_cons2I by auto
      show "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b " using wfG_cons2I by auto
    qed
    ultimately show ?thesis by auto  
  qed
next
  case (wfCE_valI \<Theta> \<B> \<Gamma> v b)
   then show ?case using subst_vv.simps  wf_intros by auto
next
  case (wfCE_plusI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case using subst_vv.simps  wf_intros by auto
next
  case (wfCE_leqI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case using subst_vv.simps  wf_intros by auto
next
  case (wfCE_eqI \<Theta> \<B> \<Gamma> v1 b v2)
  then show ?case unfolding subst_cev.simps
    using  Wellformed.wfCE_eqI by metis
next
  case (wfCE_fstI \<Theta> \<B> \<Gamma> v1 b1 b2)
  then show ?case using Wellformed.wfCE_fstI subst_cev.simps by metis
next
  case (wfCE_sndI \<Theta> \<B> \<Gamma> v1 b1 b2)
 then show ?case using subst_cev.simps  wf_intros by metis
next
  case (wfCE_concatI \<Theta> \<B> \<Gamma> v1 v2)
 then show ?case using subst_vv.simps  wf_intros by auto
next
  case (wfCE_lenI \<Theta> \<B> \<Gamma> v1)
  then show ?case using subst_vv.simps  wf_intros by auto
qed(metis subst_sv.simps wf_intros)+

lemma wf_subst2:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and b::b and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def
  shows    "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b    \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c') #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> \<Theta>; \<B>  ; \<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f v' : b'  \<Longrightarrow> \<Theta> ; \<Phi> ;  \<B>  ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ;  \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f  e[x::=v']\<^sub>e\<^sub>v : b" and
         "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b   \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c') #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> \<Theta> ;\<B>  ; \<Gamma>\<^sub>2 \<turnstile>\<^sub>w\<^sub>f v' : b'  \<Longrightarrow> \<Theta> ; \<Phi> ;  \<B>  ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f  s[x::=v']\<^sub>s\<^sub>v : b" and
         "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f cs : b \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c') #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> \<Theta>; \<B>; \<Gamma>\<^sub>2  \<turnstile>\<^sub>w\<^sub>f v' : b'  \<Longrightarrow> \<Theta>; \<Phi>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f  subst_branchv cs x v' : b" and
         "\<Theta>; \<Phi>; \<B>; \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c') #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> \<Theta>; \<B>; \<Gamma>\<^sub>2  \<turnstile>\<^sub>w\<^sub>f v' : b'  \<Longrightarrow> \<Theta>; \<Phi>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f  subst_branchlv css x v' : b" and        
         "\<Theta>  \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) \<Longrightarrow> True " and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<Delta>  \<Longrightarrow> \<Gamma>=\<Gamma>\<^sub>1@((x,b',c') #\<^sub>\<Gamma>\<Gamma>\<^sub>2) \<Longrightarrow> \<Theta>; \<B>  ; \<Gamma>\<^sub>2   \<turnstile>\<^sub>w\<^sub>f v' : b' \<Longrightarrow> \<Theta> ;  \<B> ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f  \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v" and    
         "\<Theta> ; \<Phi>   \<turnstile>\<^sub>w\<^sub>f ftq \<Longrightarrow> True" and
         "\<Theta> ; \<Phi>  ; \<B> \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow>   True"
proof(nominal_induct 
      b and b and b and b and  \<Phi> and \<Delta> and ftq and ft 
      avoiding: x v' 
      arbitrary: \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1
      rule:wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.strong_induct) 
  case (wfE_valI \<Theta> \<Gamma> v b)
  then show ?case using subst_vv.simps  wf_intros wf_subst1 
    by (metis subst_ev.simps(1))
next
  case (wfE_plusI \<Theta> \<Gamma> v1 v2)
  then show ?case using subst_vv.simps  wf_intros wf_subst1 by auto
next
  case (wfE_leqI \<Theta> \<Phi> \<Gamma> \<Delta> v1 v2)
  then show ?case 
    using subst_vv.simps  subst_ev.simps subst_ev.simps wf_subst1 Wellformed.wfE_leqI 
    by auto
next
  case (wfE_eqI \<Theta> \<Phi> \<Gamma> \<Delta> v1 b v2)
  then show ?case 
    using subst_vv.simps  subst_ev.simps subst_ev.simps wf_subst1 Wellformed.wfE_eqI     
  proof -
    show ?thesis
      by (metis (no_types) subst_ev.simps(4) wfE_eqI.hyps(1) wfE_eqI.hyps(4) wfE_eqI.hyps(5) wfE_eqI.hyps(6) wfE_eqI.hyps(7) wfE_eqI.prems(1) wfE_eqI.prems(2) wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.wfE_eqI wfV_subst) (* 31 ms *)
  qed
next
  case (wfE_fstI \<Theta> \<Gamma> v1 b1 b2)
  then show ?case using subst_vv.simps subst_ev.simps wf_subst1 Wellformed.wfE_fstI 
  proof -
    show ?thesis
      by (metis (full_types) subst_ev.simps(5) wfE_fstI.hyps(1) wfE_fstI.hyps(4) wfE_fstI.hyps(5) wfE_fstI.prems(1) wfE_fstI.prems(2) wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.wfE_fstI wf_subst1(1)) (* 78 ms *)
  qed
next
  case (wfE_sndI \<Theta> \<Gamma> v1 b1 b2)
  then show ?case 
      by (metis (full_types) subst_ev.simps wfE_sndI Wellformed.wfE_sndI wf_subst1(1)) 
next
  case (wfE_concatI \<Theta> \<Phi> \<Gamma> \<Delta> v1 v2)
  then show ?case 
    by (metis (full_types) subst_ev.simps wfE_sndI Wellformed.wfE_concatI wf_subst1(1)) 
next
  case (wfE_splitI \<Theta> \<Phi> \<Gamma> \<Delta> v1 v2)
  then show ?case 
      by (metis (full_types) subst_ev.simps wfE_sndI Wellformed.wfE_splitI wf_subst1(1)) 
next
  case (wfE_lenI \<Theta> \<Phi> \<Gamma> \<Delta> v1)
then show ?case 
      by (metis (full_types) subst_ev.simps wfE_sndI Wellformed.wfE_lenI wf_subst1(1))
next
  case (wfE_appI \<Theta> \<Phi> \<Gamma> \<Delta> f x b c \<tau> s' v)
then show ?case 
      by (metis (full_types) subst_ev.simps wfE_sndI Wellformed.wfE_appI wf_subst1(1))
next
   case (wfE_appPI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> b' bv1 v1 \<tau>1 f1 x1 b1 c1 s1)
  show ?case proof(subst subst_ev.simps, rule)
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>" using wfE_appPI wfX_wfY by metis
    show "\<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v " using wfE_appPI by auto
    show "Some (AF_fundef f1 (AF_fun_typ_some bv1 (AF_fun_typ x1 b1 c1 \<tau>1 s1))) = lookup_fun \<Phi> f1" using wfE_appPI by auto
    show "\<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f v1[x::=v']\<^sub>v\<^sub>v : b1[bv1::=b']\<^sub>b " using wfE_appPI wf_subst1 by auto
    show "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b' " using wfE_appPI by auto
    have "atom bv1 \<sharp> \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v" using fresh_subst_gv_if wfE_appPI by metis
    moreover have "atom bv1 \<sharp> v1[x::=v']\<^sub>v\<^sub>v" using wfE_appPI fresh_subst_if  by simp
    moreover have "atom bv1 \<sharp> \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v" using wfE_appPI fresh_subst_dv_if by simp
    ultimately show "atom bv1 \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v, \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v, b', v1[x::=v']\<^sub>v\<^sub>v, (b_of \<tau>1)[bv1::=b']\<^sub>b)" 
      using wfE_appPI fresh_prodN by metis
  qed
next
  case (wfE_mvarI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> u \<tau>)
  have " \<Theta> ; \<Phi>  ; \<B> ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f (AE_mvar u) : b_of \<tau>[x::=v']\<^sub>\<tau>\<^sub>v" proof
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " using wfE_mvarI by auto
    show "\<Theta>; \<B>  ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v  \<turnstile>\<^sub>w\<^sub>f \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v " using wfE_mvarI by auto
    show "(u, \<tau>[x::=v']\<^sub>\<tau>\<^sub>v) \<in> setD \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v" using wfE_mvarI subst_dv_member by auto
  qed
  thus ?case using subst_ev.simps b_of_subst by auto
next
  case (wfD_emptyI \<Theta> \<Gamma>)
  then show ?case using subst_dv.simps  wf_intros wf_subst1 by auto
next
   case (wfD_cons \<Theta> \<B> \<Gamma> \<Delta> \<tau> u)
  moreover hence "u \<notin> fst ` setD \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v" using subst_dv.simps subst_dv_iff  using subst_dv_fst_eq by presburger
  ultimately show ?case using subst_dv.simps Wellformed.wfD_cons wf_subst1 by auto
next
  case (wfPhi_emptyI \<Theta>)
  then show ?case by auto
next
  case (wfPhi_consI f \<Theta> \<Phi> ft)
  then show ?case by auto
next
   case (wfS_assertI \<Theta> \<Phi> \<B> x2 c \<Gamma> \<Delta> s b)
   show ?case unfolding subst_sv.simps proof
     show \<open> \<Theta>; \<Phi>; \<B>; (x2, B_bool, c[x::=v']\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f s[x::=v']\<^sub>s\<^sub>v : b \<close> 
       using wfS_assertI(4)[of "(x2, B_bool, c) #\<^sub>\<Gamma> \<Gamma>\<^sub>1" x ]  wfS_assertI by auto

     show \<open> \<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v   \<turnstile>\<^sub>w\<^sub>f c[x::=v']\<^sub>c\<^sub>v \<close> using wfS_assertI wf_subst1 by auto
     show \<open> \<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<close>  using wfS_assertI wf_subst1 by auto
     show \<open>atom x2 \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v, \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v, c[x::=v']\<^sub>c\<^sub>v, b, s[x::=v']\<^sub>s\<^sub>v)\<close>  
      apply(unfold fresh_prodN,intro conjI) 
      apply(simp add: wfS_assertI )+
      apply(metis fresh_subst_gv_if wfS_assertI)
      apply(simp add: fresh_prodN fresh_subst_dv_if wfS_assertI)
      apply(simp add: fresh_prodN fresh_subst_v_if subst_v_e_def wfS_assertI)        
      apply(simp add: fresh_prodN fresh_subst_v_if subst_v_\<tau>_def wfS_assertI)  
      by(simp add: fresh_prodN fresh_subst_v_if subst_v_s_def wfS_assertI)  
  qed
next
  case (wfS_letI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e b1 y s b2)
  have "\<Theta> ; \<Phi>  ; \<B> ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f LET y = (e[x::=v']\<^sub>e\<^sub>v) IN (s[x::=v']\<^sub>s\<^sub>v) : b2"  
  proof
    show \<open> \<Theta> ; \<Phi>  ; \<B> ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f e[x::=v']\<^sub>e\<^sub>v : b1 \<close> using wfS_letI by auto
    have  \<open> \<Theta> ; \<Phi>  ; \<B> ; ((y, b1, TRUE)  #\<^sub>\<Gamma> \<Gamma>)[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f s[x::=v']\<^sub>s\<^sub>v : b2 \<close> 
      using wfS_letI(6) wfS_letI append_g.simps by metis 
    thus \<open> \<Theta> ; \<Phi>  ; \<B> ; (y, b1, TRUE)  #\<^sub>\<Gamma> \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f s[x::=v']\<^sub>s\<^sub>v : b2 \<close> 
      using wfS_letI subst_gv.simps by auto
    show \<open> \<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<close> using wfS_letI by auto
    show \<open>atom y \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v, \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v, e[x::=v']\<^sub>e\<^sub>v, b2)\<close> 
      apply(unfold fresh_prodN,intro conjI) 
       apply(simp add: wfS_letI )+
       apply(metis fresh_subst_gv_if wfS_letI)
       apply(simp add: fresh_prodN fresh_subst_dv_if wfS_letI)
       apply(simp add: fresh_prodN fresh_subst_v_if subst_v_e_def wfS_letI)
       apply(simp add: fresh_prodN fresh_subst_v_if subst_v_\<tau>_def wfS_letI)      
   done
  qed
  thus ?case using subst_sv.simps wfS_letI by auto
next
  case (wfS_let2I \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 \<tau> y s2 b)
  have "\<Theta> ; \<Phi>  ; \<B> ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f LET y : \<tau>[x::=v']\<^sub>\<tau>\<^sub>v = (s1[x::=v']\<^sub>s\<^sub>v) IN (s2[x::=v']\<^sub>s\<^sub>v) : b"  
  proof
    show \<open> \<Theta> ; \<Phi>  ; \<B> ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f s1[x::=v']\<^sub>s\<^sub>v :  b_of (\<tau>[x::=v']\<^sub>\<tau>\<^sub>v) \<close> using wfS_let2I b_of_subst by simp
    have \<open> \<Theta> ; \<Phi>  ; \<B> ; ((y, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma>)[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f s2[x::=v']\<^sub>s\<^sub>v : b \<close>  
      using wfS_let2I append_g.simps by metis
    thus \<open> \<Theta> ; \<Phi>  ; \<B> ; (y, b_of \<tau>[x::=v']\<^sub>\<tau>\<^sub>v, TRUE)  #\<^sub>\<Gamma> \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f s2[x::=v']\<^sub>s\<^sub>v : b \<close> 
      using wfS_let2I subst_gv.simps append_g.simps using b_of_subst by simp
    show \<open>   \<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v   \<turnstile>\<^sub>w\<^sub>f \<tau>[x::=v']\<^sub>\<tau>\<^sub>v  \<close> using wfS_let2I wf_subst1 by metis
    show \<open>atom y \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v, \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v, s1[x::=v']\<^sub>s\<^sub>v, b, \<tau>[x::=v']\<^sub>\<tau>\<^sub>v)\<close> 
      apply(unfold fresh_prodN,intro conjI) 
       apply(simp add: wfS_let2I )+
       apply(metis fresh_subst_gv_if wfS_let2I)
       apply(simp add: fresh_prodN fresh_subst_dv_if wfS_let2I)
       apply(simp add: fresh_prodN fresh_subst_v_if subst_v_e_def wfS_let2I)
       apply(simp add: fresh_prodN fresh_subst_v_if subst_v_\<tau>_def wfS_let2I)+
      done
  qed
  thus ?case using subst_sv.simps(3) subst_tv.simps wfS_let2I by auto
next
  case (wfS_varI \<Theta> \<B> \<Gamma> \<tau> v u \<Phi> \<Delta> b s)
  show ?case proof(subst subst_sv.simps, auto simp add: u_fresh_xv,rule) 
    show \<open> \<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v   \<turnstile>\<^sub>w\<^sub>f \<tau>[x::=v']\<^sub>\<tau>\<^sub>v \<close> using wfS_varI wf_subst1 by auto
    have "b_of (\<tau>[x::=v']\<^sub>\<tau>\<^sub>v) = b_of \<tau>" using b_of_subst by auto
    thus \<open> \<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f v[x::=v']\<^sub>v\<^sub>v : b_of \<tau>[x::=v']\<^sub>\<tau>\<^sub>v \<close> using wfS_varI wf_subst1 by auto
    have *:"atom u \<sharp> v'" using wfV_supp wfS_varI fresh_def by metis
    show   \<open>atom u \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v, \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v, \<tau>[x::=v']\<^sub>\<tau>\<^sub>v, v[x::=v']\<^sub>v\<^sub>v,  b)\<close> 
      unfolding fresh_prodN apply(auto simp add: wfS_varI)
      using wfS_varI fresh_subst_gv * fresh_subst_dv by metis+
    show \<open> \<Theta> ; \<Phi>  ; \<B> ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; (u, \<tau>[x::=v']\<^sub>\<tau>\<^sub>v)  #\<^sub>\<Delta> \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f s[x::=v']\<^sub>s\<^sub>v : b \<close> using wfS_varI by auto
  qed
next
  case (wfS_assignI u \<tau> \<Delta> \<Theta> \<B> \<Gamma> \<Phi> v)
  show ?case proof(subst subst_sv.simps, rule wf_intros)
    show \<open>(u, \<tau>[x::=v']\<^sub>\<tau>\<^sub>v) \<in> setD \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v\<close> using subst_dv_iff wfS_assignI  using subst_dv_fst_eq 
      using subst_dv_member by auto
    show \<open> \<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v  \<turnstile>\<^sub>w\<^sub>f \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<close> using wfS_assignI by auto
    show \<open> \<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f v[x::=v']\<^sub>v\<^sub>v : b_of \<tau>[x::=v']\<^sub>\<tau>\<^sub>v \<close> using wfS_assignI b_of_subst wf_subst1 by auto
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> "  using wfS_assignI by auto
  qed
next
  case (wfS_matchI \<Theta> \<B> \<Gamma> v tid dclist \<Delta> \<Phi> cs b)
  show ?case  proof(subst subst_sv.simps, rule wf_intros)
    show \<open> \<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f v[x::=v']\<^sub>v\<^sub>v : B_id tid \<close> using wfS_matchI wf_subst1  by auto
    show \<open>AF_typedef tid dclist \<in> set \<Theta>\<close> using wfS_matchI by auto
    show \<open> \<Theta> ; \<Phi>  ; \<B> ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v ; tid ; dclist  \<turnstile>\<^sub>w\<^sub>f subst_branchlv cs x v'  : b \<close> using wfS_matchI by simp
    show "\<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v  \<turnstile>\<^sub>w\<^sub>f \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v " using wfS_matchI by auto
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " using wfS_matchI by auto
  qed
next
  case (wfS_branchI \<Theta> \<Phi> \<B> y \<tau> \<Gamma> \<Delta> s b tid dc)
  have " \<Theta> ; \<Phi>  ; \<B> ; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v ; tid ; dc ; \<tau> \<turnstile>\<^sub>w\<^sub>f  dc y \<Rightarrow> (s[x::=v']\<^sub>s\<^sub>v) : b" 
  proof 
    have \<open> \<Theta> ; \<Phi>  ; \<B> ; ((y, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma>)[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f s[x::=v']\<^sub>s\<^sub>v : b \<close> 
      using wfS_branchI append_g.simps by metis
    thus \<open> \<Theta> ; \<Phi>  ; \<B> ; (y, b_of \<tau>, TRUE)  #\<^sub>\<Gamma> \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v ; \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<turnstile>\<^sub>w\<^sub>f s[x::=v']\<^sub>s\<^sub>v : b \<close> 
      using subst_gv.simps b_of_subst wfS_branchI by simp
    show \<open>atom y \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v, \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v, \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v, \<tau>)\<close> 
       apply(unfold fresh_prodN,intro conjI) 
       apply(simp add: wfS_branchI )+
       apply(metis fresh_subst_gv_if wfS_branchI)
       apply(simp add: fresh_prodN fresh_subst_dv_if wfS_branchI)
       apply(metis fresh_subst_gv_if wfS_branchI)+      
      done
    show \<open> \<Theta>; \<B>; \<Gamma>[x::=v']\<^sub>\<Gamma>\<^sub>v \<turnstile>\<^sub>w\<^sub>f \<Delta>[x::=v']\<^sub>\<Delta>\<^sub>v \<close> using wfS_branchI by auto
  qed
  thus ?case using subst_branchv.simps wfS_branchI by auto
next
  case (wfS_finalI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist' cs b dclist)
  then show ?case using subst_branchlv.simps wf_intros by metis
next
  case (wfS_cons \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist' cs b css dclist)
  then show ?case using subst_branchlv.simps wf_intros by metis

qed(metis subst_sv.simps wf_subst1 wf_intros)+

lemmas wf_subst = wf_subst1 wf_subst2

lemma wfG_subst_wfV:
  assumes "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>' @ (x, b, c0[z0::=V_var x]\<^sub>c\<^sub>v)  #\<^sub>\<Gamma> \<Gamma>" and "wfV \<Theta> \<B> \<Gamma> v b"
  shows "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v @ \<Gamma> "
  using assms wf_subst subst_g_inside_simple by auto

lemma wfG_member_subst:
  assumes "(x1,b1,c1) \<in> toSet (\<Gamma>'@\<Gamma>)" and "wfG \<Theta> \<B> (\<Gamma>'@((x,b,c) #\<^sub>\<Gamma>\<Gamma>))" and "x \<noteq> x1"
  shows "\<exists>c1'. (x1,b1,c1') \<in> toSet ((\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v)@\<Gamma>)" 
proof -
  consider (lhs) "(x1,b1,c1) \<in> toSet \<Gamma>'"  |  (rhs) "(x1,b1,c1) \<in> toSet \<Gamma>" using  append_g_toSetU assms by auto
  thus ?thesis  proof(cases)
    case lhs
    hence "(x1,b1,c1[x::=v]\<^sub>c\<^sub>v) \<in> toSet (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v)" using   wfG_inside_fresh[THEN subst_gv_member_iff[OF lhs]] assms by metis
    hence "(x1,b1,c1[x::=v]\<^sub>c\<^sub>v) \<in> toSet (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v@\<Gamma>)"  using append_g_toSetU  by auto
    then show ?thesis by auto
  next
    case rhs
    hence "(x1,b1,c1) \<in> toSet (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v@\<Gamma>)"  using append_g_toSetU  by auto
    then show ?thesis by auto
  qed 
qed

lemma wfG_member_subst2:
  assumes "(x1,b1,c1) \<in> toSet (\<Gamma>'@((x,b,c) #\<^sub>\<Gamma>\<Gamma>))" and "wfG \<Theta> \<B> (\<Gamma>'@((x,b,c) #\<^sub>\<Gamma>\<Gamma>))" and "x \<noteq> x1"
  shows "\<exists>c1'. (x1,b1,c1') \<in> toSet ((\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v)@\<Gamma>)" 
proof -
  consider (lhs) "(x1,b1,c1) \<in> toSet \<Gamma>'"  |  (rhs) "(x1,b1,c1) \<in> toSet \<Gamma>" using  append_g_toSetU assms by auto
  thus ?thesis  proof(cases)
    case lhs
    hence "(x1,b1,c1[x::=v]\<^sub>c\<^sub>v) \<in> toSet (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v)" using   wfG_inside_fresh[THEN subst_gv_member_iff[OF lhs]] assms by metis
    hence "(x1,b1,c1[x::=v]\<^sub>c\<^sub>v) \<in> toSet (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v@\<Gamma>)"  using append_g_toSetU  by auto
    then show ?thesis by auto
  next
    case rhs
    hence "(x1,b1,c1) \<in> toSet (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v@\<Gamma>)"  using append_g_toSetU  by auto
    then show ?thesis by auto
  qed 
qed

lemma wbc_subst:
  fixes \<Gamma>::\<Gamma> and \<Gamma>'::\<Gamma> and v::v
  assumes "wfC \<Theta> \<B> (\<Gamma>'@((x,b,c') #\<^sub>\<Gamma>\<Gamma>)) c"  and  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b"
  shows "\<Theta>; \<B>; ((\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v)@\<Gamma>) \<turnstile>\<^sub>w\<^sub>f c[x::=v]\<^sub>c\<^sub>v" 
proof - 
  have "(\<Gamma>'@((x,b,c') #\<^sub>\<Gamma>\<Gamma>))[x::=v]\<^sub>\<Gamma>\<^sub>v = ((\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v)@\<Gamma>)" using assms subst_g_inside_simple wfC_wf by metis
  thus ?thesis  using wf_subst1(2)[OF assms(1) _ assms(2)] by metis
qed

lemma wfG_inside_fresh_suffix:
  assumes "wfG P B (\<Gamma>'@(x,b,c) #\<^sub>\<Gamma>\<Gamma>)"
  shows "atom x \<sharp> \<Gamma>"
proof -
  have "wfG P B ((x,b,c) #\<^sub>\<Gamma>\<Gamma>)"  using wfG_suffix assms by auto
  thus ?thesis  using wfG_elims by metis
qed

lemmas wf_b_subst_lemmas = subst_eb.simps wf_intros 
    forget_subst subst_b_b_def subst_b_v_def subst_b_ce_def fresh_e_opp_all subst_bb.simps wfV_b_fresh ms_fresh_all(6)

lemma wf_b_subst1:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and b::b and ftq::fun_typ_q and ft::fun_typ and s::s and b'::b and ce::ce and td::type_def
            and cs::branch_s and css::branch_list
  shows  "\<Theta> ; B'  ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b'  \<Longrightarrow> {|bv|} = B'   \<Longrightarrow> \<Theta> ;  B  \<turnstile>\<^sub>w\<^sub>f b  \<Longrightarrow> \<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile>\<^sub>w\<^sub>f  v[bv::=b]\<^sub>v\<^sub>b : b'[bv::=b]\<^sub>b\<^sub>b" and
         "\<Theta> ; B' ;  \<Gamma>  \<turnstile>\<^sub>w\<^sub>f  c           \<Longrightarrow>  {|bv|} = B' \<Longrightarrow> \<Theta> ;  B \<turnstile>\<^sub>w\<^sub>f  b \<Longrightarrow> \<Theta> ; B ;  \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f  c[bv::=b]\<^sub>c\<^sub>b" and
         "\<Theta> ;  B' \<turnstile>\<^sub>w\<^sub>f \<Gamma>           \<Longrightarrow> {|bv|} = B'      \<Longrightarrow>  \<Theta> ; B \<turnstile>\<^sub>w\<^sub>f b \<Longrightarrow> \<Theta> ; B \<turnstile>\<^sub>w\<^sub>f  \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b" and
         "\<Theta> ;  B' ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<tau>        \<Longrightarrow> {|bv|} = B'  \<Longrightarrow> \<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f  b \<Longrightarrow> \<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f  \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ts \<Longrightarrow> True" and 
         "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow>True" and        
         "\<Theta> ;  B'  \<turnstile>\<^sub>w\<^sub>f b' \<Longrightarrow>  {|bv|} = B' \<Longrightarrow>  \<Theta> ;  B  \<turnstile>\<^sub>w\<^sub>f  b \<Longrightarrow>  \<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f b'[bv::=b]\<^sub>b\<^sub>b " and        
         "\<Theta> ;  B' ;  \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce : b'    \<Longrightarrow> {|bv|} = B' \<Longrightarrow> \<Theta> ;  B  \<turnstile>\<^sub>w\<^sub>f  b  \<Longrightarrow> \<Theta> ;  B  ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile>\<^sub>w\<^sub>f  ce[bv::=b]\<^sub>c\<^sub>e\<^sub>b : b'[bv::=b]\<^sub>b\<^sub>b"  and
         "\<Theta>  \<turnstile>\<^sub>w\<^sub>f td \<Longrightarrow>   True"
proof(nominal_induct 
      b' and c and \<Gamma> and \<tau> and ts and \<Theta> and b' and  b' and td 
      avoiding: bv b B
     rule:wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.strong_induct)
  case (wfB_intI \<Theta> \<B>)
  then show ?case using subst_bb.simps wf_intros wfX_wfY   by metis
next
  case (wfB_boolI \<Theta> \<B>)
 then show ?case using subst_bb.simps wf_intros wfX_wfY   by metis
next
  case (wfB_unitI \<Theta> \<B>)
  then show ?case using subst_bb.simps wf_intros wfX_wfY   by metis
next
  case (wfB_bitvecI \<Theta> \<B>)
  then show ?case using subst_bb.simps wf_intros wfX_wfY   by metis
next
  case (wfB_pairI \<Theta> \<B> b1 b2)
  then show ?case using subst_bb.simps wf_intros wfX_wfY   by metis
next
  case (wfB_consI \<Theta> s dclist \<B>)
  then show ?case using subst_bb.simps Wellformed.wfB_consI by simp
next
  case (wfB_appI \<Theta> ba s bva dclist \<B>)
  then show ?case using subst_bb.simps Wellformed.wfB_appI forget_subst wfB_supp 
    by (metis bot.extremum_uniqueI ex_in_conv fresh_def subst_b_b_def supp_empty_fset)
next
  case (wfV_varI \<Theta> \<B>1 \<Gamma> b1 c x)
  show ?case unfolding subst_vb.simps proof
    show "\<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b " using wfV_varI by auto
    show "Some (b1[bv::=b]\<^sub>b\<^sub>b, c[bv::=b]\<^sub>c\<^sub>b) = lookup \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b x" using subst_b_lookup wfV_varI by simp
  qed
next
  case (wfV_litI \<Theta> \<B> \<Gamma> l)
  then show ?case using Wellformed.wfV_litI subst_b_base_for_lit by simp
next
  case (wfV_pairI \<Theta> \<B>1 \<Gamma> v1 b1 v2 b2)
  show ?case unfolding subst_vb.simps proof(subst subst_bb.simps,rule)
    show "\<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f v1[bv::=b]\<^sub>v\<^sub>b : b1[bv::=b]\<^sub>b\<^sub>b" using wfV_pairI by simp
    show "\<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f v2[bv::=b]\<^sub>v\<^sub>b : b2[bv::=b]\<^sub>b\<^sub>b " using wfV_pairI by simp
  qed
next
  case (wfV_consI s dclist \<Theta> dc x b' c \<B>' \<Gamma> v) 
  show ?case unfolding subst_vb.simps proof(subst subst_bb.simps, rule  Wellformed.wfV_consI) 
    show 1:"AF_typedef s dclist \<in> set \<Theta>" using wfV_consI by auto
    show 2:"(dc, \<lbrace> x : b'  | c \<rbrace>) \<in> set dclist"  using wfV_consI by auto
    have "\<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f v[bv::=b]\<^sub>v\<^sub>b : b'[bv::=b]\<^sub>b\<^sub>b"  using wfV_consI by auto
    moreover hence "supp b' = {}" using 1 2 wfTh_lookup_supp_empty \<tau>.supp wfX_wfY by blast
    moreover hence  "b'[bv::=b]\<^sub>b\<^sub>b = b'" using  forget_subst subst_bb_def fresh_def       by (metis empty_iff subst_b_b_def)
    ultimately show  "\<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f v[bv::=b]\<^sub>v\<^sub>b : b'" using wfV_consI by simp
  qed
next
  case (wfV_conspI s bva dclist \<Theta> dc x b' c \<B>' ba \<Gamma> v)
  have *:"atom bv \<sharp> b'" using  wfTh_poly_supp_b[of s bva dclist \<Theta> dc x b' c] fresh_def wfX_wfY \<open>atom bva \<sharp> bv\<close> 
    by (metis insert_iff not_self_fresh singleton_insert_inj_eq' subsetI subset_antisym wfV_conspI wfV_conspI.hyps(4) wfV_conspI.prems(2))
  show ?case unfolding subst_vb.simps subst_bb.simps proof
    show \<open>AF_typedef_poly s bva dclist \<in> set \<Theta>\<close> using wfV_conspI by auto
    show \<open>(dc, \<lbrace> x : b'  | c \<rbrace>) \<in> set dclist\<close> using wfV_conspI by auto
    thus \<open> \<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f ba[bv::=b]\<^sub>b\<^sub>b \<close> using wfV_conspI by metis
    have "atom bva \<sharp> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b" using fresh_subst_if subst_b_\<Gamma>_def wfV_conspI by metis
    moreover have "atom bva \<sharp> ba[bv::=b]\<^sub>b\<^sub>b"  using fresh_subst_if subst_b_b_def wfV_conspI by metis
    moreover have "atom bva \<sharp> v[bv::=b]\<^sub>v\<^sub>b"  using fresh_subst_if subst_b_v_def wfV_conspI by metis 
    ultimately show \<open>atom bva \<sharp> (\<Theta>, B, \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b, ba[bv::=b]\<^sub>b\<^sub>b, v[bv::=b]\<^sub>v\<^sub>b)\<close> 
      unfolding fresh_prodN using wfV_conspI fresh_def supp_fset by auto 
    show \<open> \<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f v[bv::=b]\<^sub>v\<^sub>b : b'[bva::=ba[bv::=b]\<^sub>b\<^sub>b]\<^sub>b\<^sub>b \<close> 
      using wfV_conspI  subst_bb_commute[of bv b' bva ba b] * wfV_conspI by metis
  qed
next
  case (wfTI z \<Theta> \<B>' \<Gamma>'  b' c)
  show ?case proof(subst subst_tb.simps, rule Wellformed.wfTI)
    show "atom z \<sharp>  (\<Theta>, B, \<Gamma>'[bv::=b]\<^sub>\<Gamma>\<^sub>b)" using wfTI   subst_g_b_x_fresh by simp
    show "\<Theta> ;  B  \<turnstile>\<^sub>w\<^sub>f b'[bv::=b]\<^sub>b\<^sub>b " using wfTI by auto
    show "\<Theta> ;  B ; (z, b'[bv::=b]\<^sub>b\<^sub>b, TRUE)  #\<^sub>\<Gamma> \<Gamma>'[bv::=b]\<^sub>\<Gamma>\<^sub>b   \<turnstile>\<^sub>w\<^sub>f c[bv::=b]\<^sub>c\<^sub>b " using wfTI by simp
  qed
next
  case (wfC_eqI \<Theta> \<B>' \<Gamma> e1 b' e2)
  thus ?case using Wellformed.wfC_eqI subst_db.simps  subst_cb.simps wfC_eqI by metis
next
  case (wfG_nilI \<Theta> \<B>')
  then show ?case using Wellformed.wfG_nilI subst_gb.simps by simp
next
  case (wfG_cons1I c' \<Theta> \<B>' \<Gamma>' x b')
  show ?case proof(subst subst_gb.simps, rule Wellformed.wfG_cons1I)
    show "c'[bv::=b]\<^sub>c\<^sub>b \<notin> {TRUE, FALSE}" using wfG_cons1I(1)
      by(nominal_induct c' rule: c.strong_induct,auto+) 
    show "\<Theta> ;  B  \<turnstile>\<^sub>w\<^sub>f \<Gamma>'[bv::=b]\<^sub>\<Gamma>\<^sub>b "  using wfG_cons1I by auto
    show "atom x \<sharp> \<Gamma>'[bv::=b]\<^sub>\<Gamma>\<^sub>b"  using wfG_cons1I subst_g_b_x_fresh by auto
    show "\<Theta> ;  B ; (x, b'[bv::=b]\<^sub>b\<^sub>b, TRUE)  #\<^sub>\<Gamma> \<Gamma>'[bv::=b]\<^sub>\<Gamma>\<^sub>b   \<turnstile>\<^sub>w\<^sub>f c'[bv::=b]\<^sub>c\<^sub>b"  using wfG_cons1I by auto
    show "\<Theta> ;  B  \<turnstile>\<^sub>w\<^sub>f b'[bv::=b]\<^sub>b\<^sub>b "  using wfG_cons1I by auto
  qed   
next
  case (wfG_cons2I c' \<Theta> \<B>' \<Gamma>' x b')
  show ?case proof(subst subst_gb.simps, rule Wellformed.wfG_cons2I)
    show "c'[bv::=b]\<^sub>c\<^sub>b \<in> {TRUE, FALSE}" using wfG_cons2I by auto
    show "\<Theta> ;  B  \<turnstile>\<^sub>w\<^sub>f \<Gamma>'[bv::=b]\<^sub>\<Gamma>\<^sub>b "  using wfG_cons2I by auto
    show "atom x \<sharp> \<Gamma>'[bv::=b]\<^sub>\<Gamma>\<^sub>b"  using wfG_cons2I subst_g_b_x_fresh by auto
    show "\<Theta> ;  B  \<turnstile>\<^sub>w\<^sub>f b'[bv::=b]\<^sub>b\<^sub>b "  using wfG_cons2I by auto
  qed
next
  case (wfCE_valI \<Theta> \<B> \<Gamma> v b)
  then show ?case using subst_ceb.simps wf_intros wfX_wfY   
    by (metis wf_b_subst_lemmas wfCE_b_fresh)
next
  case (wfCE_plusI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case using  subst_bb.simps subst_ceb.simps wf_intros wfX_wfY   
    by metis
next
  case (wfCE_leqI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case using  subst_bb.simps subst_ceb.simps wf_intros wfX_wfY   
    by metis
next
  case (wfCE_eqI \<Theta> \<B> \<Gamma> v1 b v2)
  then show ?case using  subst_bb.simps subst_ceb.simps wf_intros wfX_wfY   
    by metis
next
  case (wfCE_fstI \<Theta> \<B> \<Gamma> v1 b1 b2)
   then show ?case 
     by (metis (no_types) subst_bb.simps(5) subst_ceb.simps(3) wfCE_fstI.hyps(2) 
        wfCE_fstI.prems(1) wfCE_fstI.prems(2) Wellformed.wfCE_fstI) 
next
  case (wfCE_sndI \<Theta> \<B> \<Gamma> v1 b1 b2)
  then show ?case 
     by (metis (no_types) subst_bb.simps(5) subst_ceb.simps wfCE_sndI.hyps(2) 
        wfCE_sndI wfCE_sndI.prems(2) Wellformed.wfCE_sndI) 
next
  case (wfCE_concatI \<Theta> \<B> \<Gamma> v1 v2)
   then show ?case using  subst_bb.simps subst_ceb.simps wf_intros wfX_wfY wf_b_subst_lemmas wfCE_b_fresh  
   proof -
     show ?thesis
       using wfCE_concatI.hyps(2) wfCE_concatI.hyps(4) wfCE_concatI.prems(1) wfCE_concatI.prems(2) 
           Wellformed.wfCE_concatI by auto (* 46 ms *)
   qed
next
  case (wfCE_lenI \<Theta> \<B> \<Gamma> v1)
   then show ?case using  subst_bb.simps subst_ceb.simps wf_intros wfX_wfY wf_b_subst_lemmas wfCE_b_fresh  by metis
qed(auto simp add: wf_intros)

lemma wf_b_subst2:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and b::b and ftq::fun_typ_q and ft::fun_typ and s::s and b'::b and ce::ce and td::type_def
            and cs::branch_s and css::branch_list
  shows  "\<Theta> ; \<Phi> ;  B' ;  \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f e : b'    \<Longrightarrow> {|bv|} = B' \<Longrightarrow> \<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f  b  \<Longrightarrow> \<Theta> ; \<Phi> ;  B  ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b ;  \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b \<turnstile>\<^sub>w\<^sub>f  e[bv::=b]\<^sub>e\<^sub>b : b'[bv::=b]\<^sub>b\<^sub>b" and
         "\<Theta> ; \<Phi> ;  \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b   \<Longrightarrow> True" and
         "\<Theta> ; \<Phi> ;  \<B> ; \<Gamma> ; \<Delta> ; tid ; dc ; t  \<turnstile>\<^sub>w\<^sub>f cs : b \<Longrightarrow> True" and
         "\<Theta> ; \<Phi> ;  \<B> ; \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b \<Longrightarrow> True" and      
         "\<Theta>  \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) \<Longrightarrow> True " and
         "\<Theta> ;  B' ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<Delta>   \<Longrightarrow> {|bv|} = B' \<Longrightarrow> \<Theta> ; B   \<turnstile>\<^sub>w\<^sub>f b \<Longrightarrow> \<Theta> ;  B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f  \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b" and      
         "\<Theta> ; \<Phi>   \<turnstile>\<^sub>w\<^sub>f ftq \<Longrightarrow> True" and
         "\<Theta> ; \<Phi>  ; \<B> \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow>   True"
proof(nominal_induct 
      b' and b and b and b and \<Phi> and \<Delta> and  ftq and ft 
      avoiding: bv b B
rule:wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.strong_induct)
  case (wfE_valI \<Theta>' \<Phi>' \<B>' \<Gamma>' \<Delta>' v' b')
  then show ?case unfolding subst_vb.simps subst_eb.simps using wf_b_subst1(1) Wellformed.wfE_valI  by auto    
next
  case (wfE_plusI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case unfolding subst_eb.simps  
      using wf_b_subst_lemmas wf_b_subst1(1)  Wellformed.wfE_plusI 
    proof -
      have "\<forall>b ba v g f ts. (( ts ; f ; g[bv::=ba]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f v[bv::=ba]\<^sub>v\<^sub>b : b[bv::=ba]\<^sub>b\<^sub>b) \<or> \<not> ts ; \<B> ; g \<turnstile>\<^sub>w\<^sub>f v : b ) \<or> \<not> ts ; f \<turnstile>\<^sub>w\<^sub>f ba"
        using wfE_plusI.prems(1) wf_b_subst1(1) by force (* 0.0 ms *)
      then show "\<Theta> ; \<Phi> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b \<turnstile>\<^sub>w\<^sub>f [ plus v1[bv::=b]\<^sub>v\<^sub>b v2[bv::=b]\<^sub>v\<^sub>b ]\<^sup>e : B_int[bv::=b]\<^sub>b\<^sub>b"
   
        by (metis wfE_plusI.hyps(1) wfE_plusI.hyps(4) wfE_plusI.hyps(5) wfE_plusI.hyps(6) wfE_plusI.prems(1) wfE_plusI.prems(2) wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.wfE_plusI wf_b_subst_lemmas(86))
    qed
next
  case (wfE_leqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
   then show ?case unfolding subst_eb.simps  
     using wf_b_subst_lemmas wf_b_subst1  Wellformed.wfE_leqI       
   proof -
     have "\<And>ts f b ba g v. \<not> (ts ; f \<turnstile>\<^sub>w\<^sub>f b) \<or> \<not> (ts ; {|ba|} ; g \<turnstile>\<^sub>w\<^sub>f v : B_int) \<or> (ts ; f ; g[ba::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f v[ba::=b]\<^sub>v\<^sub>b : B_int)"
       by (metis wf_b_subst1(1) wf_b_subst_lemmas(86)) (* 46 ms *)
     then show "\<Theta> ; \<Phi> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b \<turnstile>\<^sub>w\<^sub>f [ leq v1[bv::=b]\<^sub>v\<^sub>b v2[bv::=b]\<^sub>v\<^sub>b ]\<^sup>e : B_bool[bv::=b]\<^sub>b\<^sub>b"
       by (metis (no_types) wfE_leqI.hyps(1) wfE_leqI.hyps(4) wfE_leqI.hyps(5) wfE_leqI.hyps(6) wfE_leqI.prems(1) wfE_leqI.prems(2) wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.wfE_leqI wf_b_subst_lemmas(87)) (* 46 ms *)
   qed   
next
  case (wfE_eqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 bb v2)
  show ?case unfolding subst_eb.simps subst_bb.simps proof
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wfX_wfY wfE_eqI by metis
    show \<open> \<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b \<close> using wfX_wfY wfE_eqI by metis
    show \<open> \<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f v1[bv::=b]\<^sub>v\<^sub>b : bb \<close> using subst_bb.simps wfE_eqI 
      by (metis (no_types, hide_lams) empty_iff insert_iff wf_b_subst1(1))
    show \<open> \<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f v2[bv::=b]\<^sub>v\<^sub>b : bb \<close> using wfX_wfY wfE_eqI       
      by (metis insert_iff singleton_iff wf_b_subst1(1) wf_b_subst_lemmas(86) wf_b_subst_lemmas(87) wf_b_subst_lemmas(90))
    show \<open>bb \<in> {B_bool, B_int, B_unit}\<close> using wfE_eqI by auto
  qed     
next
  case (wfE_fstI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case unfolding subst_eb.simps   using wf_b_subst_lemmas(84) wf_b_subst1(1)  Wellformed.wfE_fstI         
    by (metis wf_b_subst_lemmas(89))
next
  case (wfE_sndI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 b1 b2)
  then show ?case unfolding subst_eb.simps   using wf_b_subst_lemmas(86) wf_b_subst1(1)  Wellformed.wfE_sndI 
  by (metis wf_b_subst_lemmas(89))
next
  case (wfE_concatI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
then show ?case unfolding subst_eb.simps   using wf_b_subst_lemmas(86) wf_b_subst1(1)  Wellformed.wfE_concatI  
  by (metis wf_b_subst_lemmas(91))
next
  case (wfE_splitI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1 v2)
  then show ?case unfolding subst_eb.simps   using wf_b_subst_lemmas(86) wf_b_subst1(1)  Wellformed.wfE_splitI    
    by (metis wf_b_subst_lemmas(89) wf_b_subst_lemmas(91))
next
  case (wfE_lenI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v1)
  then show ?case unfolding subst_eb.simps   using wf_b_subst_lemmas(86) wf_b_subst1(1)  Wellformed.wfE_lenI  
    by (metis wf_b_subst_lemmas(91) wf_b_subst_lemmas(89))
next
  case (wfE_appI \<Theta> \<Phi> \<B>' \<Gamma> \<Delta> f x b' c \<tau> s v)
  hence bf: "atom bv \<sharp> b'" using wfPhi_f_simple_wfT wfT_supp bv_not_in_dom_g  wfPhi_f_simple_supp_b fresh_def by fast
  hence bseq: "b'[bv::=b]\<^sub>b\<^sub>b = b'" using subst_bb.simps wf_b_subst_lemmas by metis
  have "\<Theta> ; \<Phi>  ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b \<turnstile>\<^sub>w\<^sub>f (AE_app f (v[bv::=b]\<^sub>v\<^sub>b)) : (b_of (\<tau>[bv::=b]\<^sub>\<tau>\<^sub>b))" 
  proof
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi>" using wfE_appI by auto
    show "\<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b " using wfE_appI by simp 
    have "atom bv \<sharp> \<tau>" using wfPhi_f_simple_wfT[OF wfE_appI(5) wfE_appI(1),THEN wfT_supp]  bv_not_in_dom_g fresh_def by force
    hence " \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b = \<tau>"  using forget_subst subst_b_\<tau>_def by metis
    thus  "Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ x b' c \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b s))) = lookup_fun \<Phi> f" using wfE_appI by simp
    show "\<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f v[bv::=b]\<^sub>v\<^sub>b : b'" using wfE_appI bseq wf_b_subst1 by metis
  qed
  then show ?case using subst_eb.simps b_of_subst_bb_commute by simp
next
  case (wfE_appPI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> b' bv1 v1 \<tau>1 f x1 b1 c1 s1)
  then have *: "atom bv \<sharp> b1" using wfPhi_f_supp(1)  wfE_appPI(7,11) 
      by (metis fresh_def fresh_finsert singleton_iff subsetD fresh_def supp_at_base wfE_appPI.hyps(1))
  have "\<Theta> ; \<Phi>  ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b \<turnstile>\<^sub>w\<^sub>f AE_appP f b'[bv::=b]\<^sub>b\<^sub>b (v1[bv::=b]\<^sub>v\<^sub>b) : (b_of \<tau>1)[bv1::=b'[bv::=b]\<^sub>b\<^sub>b]\<^sub>b"
  proof
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> using wfE_appPI by auto
    show \<open> \<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b \<close> using wfE_appPI by auto
    show \<open> \<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f b'[bv::=b]\<^sub>b\<^sub>b \<close> using wfE_appPI wf_b_subst1 by auto
    have "atom bv1 \<sharp> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b" using fresh_subst_if subst_b_\<Gamma>_def wfE_appPI by metis
    moreover have "atom bv1 \<sharp> b'[bv::=b]\<^sub>b\<^sub>b"  using fresh_subst_if subst_b_b_def wfE_appPI by metis
    moreover have "atom bv1 \<sharp> v1[bv::=b]\<^sub>v\<^sub>b"  using fresh_subst_if subst_b_v_def wfE_appPI by metis 
    moreover have "atom bv1 \<sharp> \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b" using fresh_subst_if subst_b_\<Delta>_def wfE_appPI by metis 
    moreover have "atom bv1 \<sharp> (b_of \<tau>1)[bv1::=b'[bv::=b]\<^sub>b\<^sub>b]\<^sub>b\<^sub>b" using fresh_subst_if subst_b_b_def wfE_appPI by metis 
    ultimately show "atom bv1 \<sharp> (\<Phi>, \<Theta>, B, \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b, \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b, b'[bv::=b]\<^sub>b\<^sub>b, v1[bv::=b]\<^sub>v\<^sub>b, (b_of \<tau>1)[bv1::=b'[bv::=b]\<^sub>b\<^sub>b]\<^sub>b)"
      using wfE_appPI using fresh_def fresh_prodN subst_b_b_def by metis
    show \<open>Some (AF_fundef f (AF_fun_typ_some bv1 (AF_fun_typ x1 b1 c1 \<tau>1 s1))) = lookup_fun \<Phi> f\<close> using wfE_appPI by auto

    have  \<open> \<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f v1[bv::=b]\<^sub>v\<^sub>b : b1[bv1::=b']\<^sub>b[bv::=b]\<^sub>b\<^sub>b \<close>  
      using wfE_appPI  subst_b_b_def * wf_b_subst1 by metis
    thus  \<open> \<Theta> ; B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f v1[bv::=b]\<^sub>v\<^sub>b : b1[bv1::=b'[bv::=b]\<^sub>b\<^sub>b]\<^sub>b \<close> 
       using  subst_bb_commute subst_b_b_def *  by auto
  qed
  moreover have "atom bv \<sharp> b_of \<tau>1" proof -
    have "supp  (b_of \<tau>1) \<subseteq> { atom bv1 }" using wfPhi_f_poly_supp_b_of_t
      using b_of.simps  wfE_appPI  wfPhi_f_supp(5) by simp
    thus ?thesis using  wfE_appPI 
      fresh_def fresh_finsert singleton_iff subsetD fresh_def supp_at_base wfE_appPI.hyps by metis
  qed
  ultimately show ?case using subst_eb.simps(3) subst_bb_commute subst_b_b_def * by simp
next
  case (wfE_mvarI \<Theta> \<Phi> \<B>' \<Gamma> \<Delta> u \<tau>)

  have "\<Theta> ; \<Phi>  ;  B ; subst_gb  \<Gamma> bv b ; subst_db  \<Delta> bv b \<turnstile>\<^sub>w\<^sub>f (AE_mvar u)[bv::=b]\<^sub>e\<^sub>b : (b_of (\<tau>[bv::=b]\<^sub>\<tau>\<^sub>b))" 
  proof(subst subst_eb.simps,rule Wellformed.wfE_mvarI)
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> "  using wfE_mvarI by simp
    show "\<Theta> ;  B ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b"  using wfE_mvarI by metis
    show "(u, \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b) \<in> setD \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b" 
      using wfE_mvarI subst_db.simps set_insert subst_d_b_member by simp
  qed
  thus  ?case using  b_of_subst_bb_commute by auto

next
  case (wfS_seqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 s2 b)
  then show ?case using subst_bb.simps wf_intros wfX_wfY   by metis
next
  case (wfD_emptyI \<Theta> \<B>' \<Gamma>)
  then show ?case using subst_db.simps Wellformed.wfD_emptyI wf_b_subst1 by simp
next
  case (wfD_cons \<Theta> \<B>' \<Gamma>' \<Delta> \<tau> u)
  show ?case proof(subst subst_db.simps, rule Wellformed.wfD_cons )
    show "\<Theta> ;  B ; \<Gamma>'[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b " using wfD_cons by auto
    show "\<Theta> ;  B ; \<Gamma>'[bv::=b]\<^sub>\<Gamma>\<^sub>b   \<turnstile>\<^sub>w\<^sub>f \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b  "  using wfD_cons wf_b_subst1 by auto
    show "u \<notin> fst ` setD \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b" using wfD_cons subst_b_lookup_d by metis
  qed    
next
  case (wfS_assertI \<Theta> \<Phi> \<B> x c \<Gamma> \<Delta> s b)
  show ?case by auto
qed(auto)

lemmas wf_b_subst = wf_b_subst1 wf_b_subst2

lemma wfT_subst_wfT:
  fixes \<tau>::\<tau> and b'::b and bv::bv 
  assumes "\<Theta> ; {|bv|} ; (x,b,c) #\<^sub>\<Gamma>GNil   \<turnstile>\<^sub>w\<^sub>f \<tau>" and "\<Theta> ; B \<turnstile>\<^sub>w\<^sub>f b'"
  shows "\<Theta> ;  B ; (x,b[bv::=b']\<^sub>b\<^sub>b,c[bv::=b']\<^sub>c\<^sub>b) #\<^sub>\<Gamma>GNil  \<turnstile>\<^sub>w\<^sub>f  (\<tau>[bv::=b']\<^sub>\<tau>\<^sub>b)"
proof - 
  have  "\<Theta> ;  B ; ((x,b,c) #\<^sub>\<Gamma>GNil)[bv::=b']\<^sub>\<Gamma>\<^sub>b  \<turnstile>\<^sub>w\<^sub>f  (\<tau>[bv::=b']\<^sub>\<tau>\<^sub>b)"
    using wf_b_subst assms by metis
  thus ?thesis using subst_gb.simps wf_b_subst_lemmas wfCE_b_fresh  by metis
qed

lemma wf_trans:
  fixes \<Gamma>::\<Gamma> and  \<Gamma>'::\<Gamma> and v::v and e::e and c::c and \<tau>::\<tau> and ts::"(string*\<tau>) list" and \<Delta>::\<Delta> and b::b and ftq::fun_typ_q and ft::fun_typ and ce::ce and td::type_def and s::s
          and cs::branch_s and css::branch_list and \<Theta>::\<Theta>
  shows  "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b'        \<Longrightarrow> \<Gamma> = (x, b, c2)  #\<^sub>\<Gamma> G  \<Longrightarrow> \<Theta>; \<B>; (x, b, c1)  #\<^sub>\<Gamma> G   \<turnstile>\<^sub>w\<^sub>f c2  \<Longrightarrow>  \<Theta>; \<B>; (x, b, c1)  #\<^sub>\<Gamma> G   \<turnstile>\<^sub>w\<^sub>f v : b'" and
          "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f  c           \<Longrightarrow> \<Gamma> = (x, b, c2)  #\<^sub>\<Gamma> G \<Longrightarrow> \<Theta>; \<B>; (x, b, c1)  #\<^sub>\<Gamma> G   \<turnstile>\<^sub>w\<^sub>f c2 \<Longrightarrow> \<Theta>; \<B>; (x, b, c1)  #\<^sub>\<Gamma> G   \<turnstile>\<^sub>w\<^sub>f c" and
         "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>                \<Longrightarrow> True" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<tau>            \<Longrightarrow> True" and
         "\<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ts \<Longrightarrow> True" and 
         "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow>True" and      
         "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b \<Longrightarrow> True " and       
         "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce : b'    \<Longrightarrow> \<Gamma> = (x, b, c2)  #\<^sub>\<Gamma> G \<Longrightarrow> \<Theta>; \<B>; (x, b, c1)  #\<^sub>\<Gamma> G   \<turnstile>\<^sub>w\<^sub>f c2  \<Longrightarrow> \<Theta>; \<B>; (x, b, c1)  #\<^sub>\<Gamma> G   \<turnstile>\<^sub>w\<^sub>f ce : b' " and
         "\<Theta>  \<turnstile>\<^sub>w\<^sub>f td \<Longrightarrow>   True"
proof(nominal_induct
     b' and c and \<Gamma> and \<tau> and ts and \<Theta> and  b and  b' and td 
     avoiding: c1
   arbitrary: \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 and  \<Gamma>\<^sub>1 and \<Gamma>\<^sub>1 
   rule:wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.strong_induct)
  case (wfV_varI \<Theta> \<B> \<Gamma> b' c' x')
  have wbg: "\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f (x, b, c1)  #\<^sub>\<Gamma> G " using wfC_wf wfV_varI by simp
  show ?case proof(cases "x=x'")
    case True
    have "Some (b', c1) = lookup ((x, b, c1)  #\<^sub>\<Gamma> G) x'" using lookup.simps wfV_varI  using True by auto
    then show ?thesis using Wellformed.wfV_varI wbg by simp
  next
    case False
    then have "Some (b', c') = lookup ((x, b, c1)  #\<^sub>\<Gamma> G) x'" using lookup.simps wfV_varI 
      by simp
    then show ?thesis using Wellformed.wfV_varI wbg by simp
  qed 
next
 case (wfV_conspI s bv dclist \<Theta> dc x1 b' c \<B> b1 \<Gamma> v)
  show ?case proof
    show \<open>AF_typedef_poly s bv dclist \<in> set \<Theta>\<close> using wfV_conspI by auto
    show \<open>(dc, \<lbrace> x1 : b'  | c \<rbrace>) \<in> set dclist\<close> using wfV_conspI by auto
    show \<open>\<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b1 \<close> using wfV_conspI by auto
    show \<open>atom bv \<sharp> (\<Theta>, \<B>, (x, b, c1)  #\<^sub>\<Gamma> G, b1, v)\<close> unfolding fresh_prodN fresh_GCons using wfV_conspI  fresh_prodN fresh_GCons by simp
    show \<open>\<Theta>; \<B>; (x, b, c1)  #\<^sub>\<Gamma> G \<turnstile>\<^sub>w\<^sub>f v : b'[bv::=b1]\<^sub>b\<^sub>b\<close> using wfV_conspI by auto
  qed
qed( (auto | metis wfC_wf wf_intros) +)


end