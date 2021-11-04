(*<*)
theory BTVSubstTypingL
  imports  "HOL-Eisbach.Eisbach_Tools" ContextSubtypingL SubstMethods
begin
  (*>*)

chapter \<open>Basic Type Variable Substitution Lemmas\<close>
text \<open>Lemmas that show that types are preserved, in some way, 
under basic type variable substitution\<close>

lemma subst_vv_subst_bb_commute:
  fixes bv::bv and b::b and x::x and v::v
  assumes "atom bv \<sharp> v"
  shows "(v'[x::=v]\<^sub>v\<^sub>v)[bv::=b]\<^sub>v\<^sub>b = (v'[bv::=b]\<^sub>v\<^sub>b)[x::=v]\<^sub>v\<^sub>v" 
  using assms proof(nominal_induct v'  rule: v.strong_induct)
  case (V_lit x)
  then show ?case using subst_vb.simps subst_vv.simps by simp
next
  case (V_var y)
  hence "v[bv::=b]\<^sub>v\<^sub>b=v" using forget_subst subst_b_v_def by metis
  then show ?case unfolding subst_vb.simps(2) subst_vv.simps(2) using V_var by auto
next
  case (V_pair x1a x2a)
  then show ?case using subst_vb.simps subst_vv.simps by simp
next
  case (V_cons x1a x2a x3)
  then show ?case using subst_vb.simps subst_vv.simps by simp
next
  case (V_consp x1a x2a x3 x4)
  then show ?case using subst_vb.simps subst_vv.simps by simp
qed

lemma subst_cev_subst_bb_commute:
  fixes bv::bv and b::b and x::x and v::v
  assumes "atom bv \<sharp> v"
  shows "(ce[x::=v]\<^sub>v)[bv::=b]\<^sub>c\<^sub>e\<^sub>b = (ce[bv::=b]\<^sub>c\<^sub>e\<^sub>b)[x::=v]\<^sub>v" 
  using assms apply (nominal_induct ce  rule: ce.strong_induct, (simp add: subst_vv_subst_bb_commute subst_ceb.simps subst_cv.simps))
  using assms subst_vv_subst_bb_commute subst_ceb.simps subst_cv.simps 
  by (simp add: subst_v_ce_def)+

lemma subst_cv_subst_bb_commute:
  fixes bv::bv and b::b and x::x and v::v
  assumes "atom bv \<sharp> v"
  shows "c[x::=v]\<^sub>c\<^sub>v[bv::=b]\<^sub>c\<^sub>b = (c[bv::=b]\<^sub>c\<^sub>b)[x::=v]\<^sub>c\<^sub>v" 
  using assms apply (nominal_induct c  rule: c.strong_induct )
  using assms subst_vv_subst_bb_commute subst_ceb.simps subst_cv.simps 
    subst_v_c_def subst_b_c_def   apply auto
  using subst_cev_subst_bb_commute subst_v_ce_def by auto+

lemma subst_b_c_of:
  "(c_of \<tau> z)[bv::=b]\<^sub>c\<^sub>b =  c_of (\<tau>[bv::=b]\<^sub>\<tau>\<^sub>b) z"
proof(nominal_induct \<tau> avoiding: z rule:\<tau>.strong_induct)
  case (T_refined_type z' b' c')
  moreover have "atom bv \<sharp> [ z ]\<^sup>v " using fresh_at_base v.fresh by auto
  ultimately show ?case using subst_cv_subst_bb_commute[of bv "V_var z" c' z' b]  c_of.simps subst_tb.simps by metis
qed

lemma subst_b_b_of:
  "(b_of \<tau>)[bv::=b]\<^sub>b\<^sub>b =  b_of (\<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)"
  by(nominal_induct \<tau> rule:\<tau>.strong_induct, simp add: b_of.simps subst_tb.simps )

lemma subst_b_if:
  "\<lbrace> z : b_of \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b  | CE_val (v[bv::=b]\<^sub>v\<^sub>b)  ==  CE_val (V_lit ll)   IMP  c_of \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b z  \<rbrace> = \<lbrace> z : b_of \<tau> | CE_val (v)  ==  CE_val (V_lit ll)   IMP  c_of \<tau> z  \<rbrace>[bv::=b]\<^sub>\<tau>\<^sub>b "
  unfolding subst_tb.simps subst_cb.simps subst_ceb.simps subst_vb.simps using subst_b_b_of   subst_b_c_of by auto

lemma subst_b_top_eq:
  "\<lbrace> z : B_unit  | TRUE \<rbrace>[bv::=b]\<^sub>\<tau>\<^sub>b = \<lbrace> z : B_unit  | TRUE \<rbrace>" and "\<lbrace> z : B_bool  | TRUE \<rbrace>[bv::=b]\<^sub>\<tau>\<^sub>b = \<lbrace> z : B_bool  | TRUE \<rbrace>"  and "\<lbrace> z : B_id tid | TRUE \<rbrace> = \<lbrace> z : B_id tid | TRUE \<rbrace>[bv::=b]\<^sub>\<tau>\<^sub>b"
  unfolding  subst_tb.simps subst_bb.simps subst_cb.simps by auto

lemmas subst_b_eq = subst_b_c_of subst_b_b_of subst_b_if subst_b_top_eq

lemma subst_cx_subst_bb_commute[simp]:
  fixes bv::bv and b::b and x::x and v'::c
  shows "(v'[x::=V_var y]\<^sub>c\<^sub>v)[bv::=b]\<^sub>c\<^sub>b = (v'[bv::=b]\<^sub>c\<^sub>b)[x::=V_var y]\<^sub>c\<^sub>v" 
  using subst_cv_subst_bb_commute fresh_at_base  v.fresh by auto

lemma subst_b_infer_b:
  fixes l::l and b::b
  assumes " \<turnstile> l \<Rightarrow> \<tau>" and "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f b" and "B = {|bv|}"
  shows  "\<turnstile> l \<Rightarrow> (\<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)" 
  using assms infer_l_form3 infer_l_form4 wf_b_subst infer_l_wf subst_tb.simps base_for_lit.simps subst_tb.simps
    subst_b_base_for_lit subst_cb.simps(6) subst_ceb.simps(1) subst_vb.simps(1) subst_vb.simps(2) type_l_eq
  by metis

lemma subst_b_subtype:
  fixes s::s and b'::b
  assumes  "\<Theta> ; {|bv|} ; \<Gamma>  \<turnstile> \<tau>1 \<lesssim> \<tau>2" and "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f b'"  and "B = {|bv|}" 
  shows "\<Theta> ; {||} ; \<Gamma>[bv::=b']\<^sub>\<Gamma>\<^sub>b  \<turnstile> \<tau>1[bv::=b']\<^sub>\<tau>\<^sub>b \<lesssim> \<tau>2[bv::=b']\<^sub>\<tau>\<^sub>b"
  using assms proof(nominal_induct "{|bv|}"  \<Gamma> \<tau>1 \<tau>2 rule:subtype.strong_induct)
  case (subtype_baseI x \<Theta> \<Gamma> z c z' c' b)

  hence **: "\<Theta> ; {|bv|} ; (x, b, c[z::=V_var x]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile> c'[z'::=V_var x]\<^sub>c\<^sub>v " using validI subst_defs by metis

  have "\<Theta> ; {||} ; \<Gamma>[bv::=b']\<^sub>\<Gamma>\<^sub>b  \<turnstile> \<lbrace> z : b[bv::=b']\<^sub>b\<^sub>b | c[bv::=b']\<^sub>c\<^sub>b \<rbrace>  \<lesssim> \<lbrace> z' : b[bv::=b']\<^sub>b\<^sub>b | c'[bv::=b']\<^sub>c\<^sub>b \<rbrace>" proof(rule Typing.subtype_baseI)
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b']\<^sub>\<Gamma>\<^sub>b   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b[bv::=b']\<^sub>b\<^sub>b  | c[bv::=b']\<^sub>c\<^sub>b \<rbrace> " 
      using subtype_baseI assms wf_b_subst(4) subst_tb.simps subst_defs  by metis
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b']\<^sub>\<Gamma>\<^sub>b   \<turnstile>\<^sub>w\<^sub>f \<lbrace> z' : b[bv::=b']\<^sub>b\<^sub>b  | c'[bv::=b']\<^sub>c\<^sub>b \<rbrace> " 
      using subtype_baseI assms wf_b_subst(4) subst_tb.simps by metis
    show "atom x \<sharp>(\<Theta>, {||}::bv fset, \<Gamma>[bv::=b']\<^sub>\<Gamma>\<^sub>b,  z , c[bv::=b']\<^sub>c\<^sub>b ,  z'  , c'[bv::=b']\<^sub>c\<^sub>b )" 
      apply(unfold fresh_prodN,auto simp add: * fresh_prodN fresh_empty_fset) 
      using subst_b_fresh_x * fresh_prodN  \<open>atom x \<sharp> c\<close> \<open>atom x \<sharp> c'\<close> subst_defs subtype_baseI by metis+
    have "\<Theta> ; {||} ; (x, b[bv::=b']\<^sub>b\<^sub>b, c[z::=V_var x]\<^sub>v[bv::=b']\<^sub>c\<^sub>b) #\<^sub>\<Gamma> \<Gamma>[bv::=b']\<^sub>\<Gamma>\<^sub>b  \<Turnstile> c'[z'::=V_var x]\<^sub>v[bv::=b']\<^sub>c\<^sub>b" 
      using ** subst_b_valid subst_gb.simps assms  subtype_baseI  by metis
    thus "\<Theta> ; {||} ; (x, b[bv::=b']\<^sub>b\<^sub>b, (c[bv::=b']\<^sub>c\<^sub>b)[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>[bv::=b']\<^sub>\<Gamma>\<^sub>b  \<Turnstile> (c'[bv::=b']\<^sub>c\<^sub>b)[z'::=V_var x]\<^sub>v" 
      using subst_defs subst_cv_subst_bb_commute  by (metis subst_cx_subst_bb_commute)
  qed
  thus ?case using subtype_baseI subst_tb.simps subst_defs by metis
qed

lemma b_of_subst_bv:
  "(b_of \<tau>)[x::=v]\<^sub>b\<^sub>b = b_of (\<tau>[x::=v]\<^sub>\<tau>\<^sub>b)"
proof -
  obtain z b c where *:"\<tau> = \<lbrace> z : b | c \<rbrace> \<and> atom z \<sharp> (x,v)" using obtain_fresh_z by metis
  thus ?thesis  using subst_tv.simps * by auto 
qed

lemma subst_b_infer_v:
  fixes v::v and b::b
  assumes "\<Theta> ; B ; G \<turnstile> v \<Rightarrow> \<tau>" and "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f b" and "B = {|bv|}"
  shows  "\<Theta> ; {||} ; G[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> (\<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)" 
  using assms proof(nominal_induct avoiding: b bv rule: infer_v.strong_induct)
  case (infer_v_varI \<Theta> \<B> \<Gamma> b' c x z)
  show ?case unfolding  subst_b_simps proof
    show "\<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b " using infer_v_varI wf_b_subst by metis
    show "Some (b'[bv::=b]\<^sub>b\<^sub>b, c[bv::=b]\<^sub>c\<^sub>b) = lookup \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b x" using subst_b_lookup infer_v_varI by metis
    show "atom z \<sharp> x" using infer_v_varI by auto
    show "atom z \<sharp>  (\<Theta>, {||}, \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b) " by(fresh_mth add: infer_v_varI subst_b_fresh_x subst_b_\<Gamma>_def fresh_prodN fresh_empty_fset )
  qed
next
  case (infer_v_litI \<Theta> \<B> \<Gamma> l \<tau>)
  then show ?case using Typing.infer_v_litI subst_b_infer_b 
    using wf_b_subst1(3) by auto
next
  case (infer_v_pairI z v1 v2 \<Theta> \<B> \<Gamma> t1 t2)
  show ?case unfolding   subst_b_simps b_of_subst_bv proof
    show "atom z \<sharp> (v1[bv::=b]\<^sub>v\<^sub>b, v2[bv::=b]\<^sub>v\<^sub>b)" by(fresh_mth add: infer_v_pairI subst_b_fresh_x)
    show "atom z \<sharp> (\<Theta>, {||}, \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b)" by(fresh_mth add: infer_v_pairI subst_b_fresh_x subst_b_\<Gamma>_def fresh_empty_fset)
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v1[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> t1[bv::=b]\<^sub>\<tau>\<^sub>b" using infer_v_pairI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v2[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> t2[bv::=b]\<^sub>\<tau>\<^sub>b" using infer_v_pairI by auto
  qed
next
  case (infer_v_consI s dclist \<Theta> dc tc \<B> \<Gamma> v tv z)
  show ?case unfolding   subst_b_simps b_of_subst_bv proof
    show "AF_typedef s dclist \<in> set \<Theta>" using infer_v_consI by auto
    show "(dc, tc) \<in> set dclist"  using infer_v_consI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> tv[bv::=b]\<^sub>\<tau>\<^sub>b" using infer_v_consI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> tv[bv::=b]\<^sub>\<tau>\<^sub>b \<lesssim> tc" proof -
      have "atom bv \<sharp> tc" using wfTh_lookup_supp_empty fresh_def infer_v_consI infer_v_wf by fast
      moreover have  "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> tv[bv::=b]\<^sub>\<tau>\<^sub>b \<lesssim> tc[bv::=b]\<^sub>\<tau>\<^sub>b"  
        using subst_b_subtype infer_v_consI by simp     
      ultimately show  ?thesis using forget_subst subst_b_\<tau>_def by metis
    qed
    show "atom z \<sharp> v[bv::=b]\<^sub>v\<^sub>b"  using infer_v_consI using  subst_b_fresh_x subst_b_v_def by metis
    show "atom z \<sharp> (\<Theta>, {||}, \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b)"  by(fresh_mth add: infer_v_consI subst_b_fresh_x subst_b_\<Gamma>_def fresh_empty_fset)
  qed
next
  case (infer_v_conspI s bv2 dclist2 \<Theta> dc tc \<B> \<Gamma> v tv ba z)

  have "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> V_consp s dc (ba[bv::=b]\<^sub>b\<^sub>b) (v[bv::=b]\<^sub>v\<^sub>b) \<Rightarrow> \<lbrace> z : B_app s (ba[bv::=b]\<^sub>b\<^sub>b)  | [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ V_consp s dc (ba[bv::=b]\<^sub>b\<^sub>b) (v[bv::=b]\<^sub>v\<^sub>b) ]\<^sup>c\<^sup>e  \<rbrace>"
  proof(rule Typing.infer_v_conspI)
    show "AF_typedef_poly s bv2 dclist2 \<in> set \<Theta>" using infer_v_conspI by auto
    show "(dc, tc) \<in> set dclist2"  using infer_v_conspI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> tv[bv::=b]\<^sub>\<tau>\<^sub>b" 
      using infer_v_conspI subst_tb.simps by metis

    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> tv[bv::=b]\<^sub>\<tau>\<^sub>b \<lesssim> tc[bv2::=ba[bv::=b]\<^sub>b\<^sub>b]\<^sub>\<tau>\<^sub>b" proof -
      have "supp tc \<subseteq> { atom bv2 }" using infer_v_conspI wfTh_poly_lookup_supp wfX_wfY by metis
      moreover have "bv2 \<noteq> bv"  using \<open>atom bv2 \<sharp> \<B>\<close> \<open>\<B> = {|bv|} \<close> fresh_at_base fresh_def 
        using fresh_finsert by fastforce
      ultimately have "atom bv \<sharp> tc" unfolding fresh_def by auto
      hence "tc[bv2::=ba[bv::=b]\<^sub>b\<^sub>b]\<^sub>\<tau>\<^sub>b = tc[bv2::=ba]\<^sub>\<tau>\<^sub>b[bv::=b]\<^sub>\<tau>\<^sub>b" 
        using subst_tb_commute by metis
      moreover  have "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> tv[bv::=b]\<^sub>\<tau>\<^sub>b \<lesssim> tc[bv2::=ba]\<^sub>\<tau>\<^sub>b[bv::=b]\<^sub>\<tau>\<^sub>b" 
        using infer_v_conspI(7) subst_b_subtype infer_v_conspI by metis
      ultimately show ?thesis by auto
    qed    
    show "atom z \<sharp> (\<Theta>, {||}, \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b, v[bv::=b]\<^sub>v\<^sub>b, ba[bv::=b]\<^sub>b\<^sub>b)" 
      apply(unfold fresh_prodN, intro conjI, auto simp add: infer_v_conspI fresh_empty_fset)
      using \<open>atom z \<sharp> \<Gamma>\<close>  fresh_subst_if   subst_b_\<Gamma>_def x_fresh_b  apply metis
      using \<open>atom z \<sharp> v\<close>  fresh_subst_if   subst_b_v_def x_fresh_b  by metis
    show "atom bv2 \<sharp> (\<Theta>, {||}, \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b, v[bv::=b]\<^sub>v\<^sub>b, ba[bv::=b]\<^sub>b\<^sub>b)" 
      apply(unfold fresh_prodN, intro conjI, auto simp add: infer_v_conspI fresh_empty_fset)
      using \<open>atom bv2 \<sharp> b\<close>  \<open>atom bv2 \<sharp> \<Gamma>\<close> fresh_subst_if   subst_b_\<Gamma>_def apply metis
      using \<open>atom bv2 \<sharp> b\<close>  \<open>atom bv2 \<sharp> v\<close> fresh_subst_if   subst_b_v_def apply metis
      using \<open>atom bv2 \<sharp> b\<close>  \<open>atom bv2 \<sharp> ba\<close> fresh_subst_if   subst_b_b_def by metis
    show "\<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f ba[bv::=b]\<^sub>b\<^sub>b " 
      using infer_v_conspI  wf_b_subst by metis
  qed
  thus ?case using subst_vb.simps subst_tb.simps subst_bb.simps by simp

qed

lemma subst_b_check_v:
  fixes v::v and b::b
  assumes "\<Theta> ; B ; G \<turnstile> v \<Leftarrow> \<tau>" and "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f b" and "B = {|bv|}"
  shows  "\<Theta> ; {||} ; G[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v[bv::=b]\<^sub>v\<^sub>b \<Leftarrow> (\<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)" 
proof -
  obtain \<tau>' where "\<Theta> ; B ; G \<turnstile> v \<Rightarrow> \<tau>' \<and>  \<Theta> ; B ; G  \<turnstile> \<tau>' \<lesssim> \<tau>" using check_v_elims[OF assms(1)] by metis
  thus ?thesis using subst_b_subtype subst_b_infer_v assms 
    by (metis (no_types)  check_v_subtypeI subst_b_infer_v subst_b_subtype)
qed

lemma subst_vv_subst_vb_switch:
  shows  "(v'[bv::=b']\<^sub>v\<^sub>b)[x::=v[bv::=b']\<^sub>v\<^sub>b]\<^sub>v\<^sub>v = v'[x::=v]\<^sub>v\<^sub>v[bv::=b']\<^sub>v\<^sub>b"
proof(nominal_induct v' rule:v.strong_induct)
  case (V_lit x)
  then show ?case using subst_vv.simps subst_vb.simps by auto
next
  case (V_var x)
  then show ?case using subst_vv.simps subst_vb.simps by auto
next
  case (V_pair x1a x2a)
  then show ?case using subst_vv.simps subst_vb.simps v.fresh by auto
next
  case (V_cons x1a x2a x3)
  then show ?case using subst_vv.simps subst_vb.simps v.fresh by auto
next
  case (V_consp x1a x2a x3 x4)
  then show ?case using subst_vv.simps subst_vb.simps v.fresh pure_fresh 
    by (metis forget_subst subst_b_b_def)
qed

lemma subst_cev_subst_vb_switch:
  shows  "(ce[bv::=b']\<^sub>c\<^sub>e\<^sub>b)[x::=v[bv::=b']\<^sub>v\<^sub>b]\<^sub>c\<^sub>e\<^sub>v = (ce[x::=v]\<^sub>c\<^sub>e\<^sub>v)[bv::=b']\<^sub>c\<^sub>e\<^sub>b"
  by(nominal_induct ce rule:ce.strong_induct, auto simp add: subst_vv_subst_vb_switch ce.fresh)

lemma subst_cv_subst_vb_switch:
  shows  "(c[bv::=b']\<^sub>c\<^sub>b)[x::=v[bv::=b']\<^sub>v\<^sub>b]\<^sub>c\<^sub>v = c[x::=v]\<^sub>c\<^sub>v[bv::=b']\<^sub>c\<^sub>b"
  by(nominal_induct c rule:c.strong_induct, auto simp add: subst_cev_subst_vb_switch c.fresh)

lemma subst_tv_subst_vb_switch:
  shows  "(\<tau>[bv::=b']\<^sub>\<tau>\<^sub>b)[x::=v[bv::=b']\<^sub>v\<^sub>b]\<^sub>\<tau>\<^sub>v = \<tau>[x::=v]\<^sub>\<tau>\<^sub>v[bv::=b']\<^sub>\<tau>\<^sub>b"
proof(nominal_induct \<tau> avoiding: x v rule:\<tau>.strong_induct)
  case (T_refined_type z b c )
  hence ceq: "(c[bv::=b']\<^sub>c\<^sub>b)[x::=v[bv::=b']\<^sub>v\<^sub>b]\<^sub>c\<^sub>v = c[x::=v]\<^sub>c\<^sub>v[bv::=b']\<^sub>c\<^sub>b" using subst_cv_subst_vb_switch by auto

  moreover have "atom z \<sharp> v[bv::=b']\<^sub>v\<^sub>b" using x_fresh_b fresh_subst_if subst_b_v_def T_refined_type by metis

  hence "\<lbrace> z : b  | c \<rbrace>[bv::=b']\<^sub>\<tau>\<^sub>b[x::=v[bv::=b']\<^sub>v\<^sub>b]\<^sub>\<tau>\<^sub>v = \<lbrace> z : b[bv::=b']\<^sub>b\<^sub>b  | (c[bv::=b']\<^sub>c\<^sub>b)[x::=v[bv::=b']\<^sub>v\<^sub>b]\<^sub>c\<^sub>v \<rbrace>"
    using subst_tv.simps subst_tb.simps T_refined_type fresh_Pair by metis

  moreover have "\<lbrace> z : b[bv::=b']\<^sub>b\<^sub>b  | (c[bv::=b']\<^sub>c\<^sub>b)[x::=v[bv::=b']\<^sub>v\<^sub>b]\<^sub>c\<^sub>v \<rbrace>  =  \<lbrace> z : b  | c[x::=v]\<^sub>c\<^sub>v \<rbrace>[bv::=b']\<^sub>\<tau>\<^sub>b"
    using subst_tv.simps subst_tb.simps ceq \<tau>.fresh forget_subst[of "bv" b b'] subst_b_b_def T_refined_type by metis

  ultimately show ?case using subst_tv.simps subst_tb.simps ceq T_refined_type by auto
qed

lemma subst_tb_triple:
  assumes "atom bv \<sharp> \<tau>'" 
  shows  "\<tau>'[bv'::=b'[bv::=b]\<^sub>b\<^sub>b]\<^sub>\<tau>\<^sub>b[x'::=v'[bv::=b]\<^sub>v\<^sub>b]\<^sub>\<tau>\<^sub>v = \<tau>'[bv'::=b']\<^sub>\<tau>\<^sub>b[x'::=v']\<^sub>\<tau>\<^sub>v[bv::=b]\<^sub>\<tau>\<^sub>b"  
proof -
  have "\<tau>'[bv'::=b'[bv::=b]\<^sub>b\<^sub>b]\<^sub>\<tau>\<^sub>b[x'::=v'[bv::=b]\<^sub>v\<^sub>b]\<^sub>\<tau>\<^sub>v = \<tau>'[bv'::=b']\<^sub>\<tau>\<^sub>b[bv::=b]\<^sub>\<tau>\<^sub>b [x'::=v'[bv::=b]\<^sub>v\<^sub>b]\<^sub>\<tau>\<^sub>v"
    using subst_tb_commute \<open>atom bv \<sharp> \<tau>'\<close> by auto
  also have "... = \<tau>'[bv'::=b']\<^sub>\<tau>\<^sub>b [x'::=v']\<^sub>\<tau>\<^sub>v[bv::=b]\<^sub>\<tau>\<^sub>b" 
    using subst_tv_subst_vb_switch by auto
  finally show ?thesis using fresh_subst_if forget_subst by auto
qed

lemma subst_b_infer_e:
  fixes s::s and b::b
  assumes "\<Theta> ; \<Phi> ; B ; G; D \<turnstile> e \<Rightarrow> \<tau>" and "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f b"  and "B = {|bv|}" 
  shows  "\<Theta> ; \<Phi> ; {||} ; G[bv::=b]\<^sub>\<Gamma>\<^sub>b; D[bv::=b]\<^sub>\<Delta>\<^sub>b \<turnstile> (e[bv::=b]\<^sub>e\<^sub>b) \<Rightarrow> (\<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)" 
  using assms proof(nominal_induct avoiding: b rule: infer_e.strong_induct)
  case (infer_e_valI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v \<tau>)
  thus ?case using  subst_eb.simps infer_e.intros wf_b_subst subst_db.simps wf_b_subst infer_v_wf subst_b_infer_v 
    by (metis forget_subst ms_fresh_all(1) wfV_b_fresh)
next
  case (infer_e_plusI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 c2 z3)

  show ?case unfolding subst_b_simps subst_eb.simps proof(rule Typing.infer_e_plusI)
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b " using wf_b_subst(10) subst_db.simps infer_e_plusI wfX_wfY 
      by (metis wf_b_subst(15))
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " using infer_e_plusI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v1[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> \<lbrace> z1 : B_int  | c1[bv::=b]\<^sub>c\<^sub>b \<rbrace>" using subst_b_infer_v  infer_e_plusI subst_b_simps by force
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v2[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> \<lbrace> z2 : B_int  | c2[bv::=b]\<^sub>c\<^sub>b \<rbrace>" using subst_b_infer_v  infer_e_plusI subst_b_simps by force
    show "atom z3 \<sharp> AE_op Plus (v1[bv::=b]\<^sub>v\<^sub>b) (v2[bv::=b]\<^sub>v\<^sub>b)" using  subst_b_simps infer_e_plusI subst_b_fresh_x subst_b_e_def by metis
    show "atom z3 \<sharp> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b" using subst_g_b_x_fresh infer_e_plusI by auto
  qed
next
  case (infer_e_leqI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 c2 z3)
  show ?case unfolding subst_b_simps proof(rule Typing.infer_e_leqI)
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  " using wf_b_subst(10) subst_db.simps infer_e_leqI wfX_wfY 
      by (metis wf_b_subst(15))
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " using infer_e_leqI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v1[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> \<lbrace> z1 : B_int  | c1[bv::=b]\<^sub>c\<^sub>b \<rbrace>" using subst_b_infer_v  infer_e_leqI subst_b_simps by force
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v2[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> \<lbrace> z2 : B_int  | c2[bv::=b]\<^sub>c\<^sub>b \<rbrace>" using subst_b_infer_v  infer_e_leqI subst_b_simps by force
    show "atom z3 \<sharp> AE_op LEq (v1[bv::=b]\<^sub>v\<^sub>b) (v2[bv::=b]\<^sub>v\<^sub>b)" using  subst_b_simps infer_e_leqI subst_b_fresh_x subst_b_e_def by metis
    show "atom z3 \<sharp> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b" using subst_g_b_x_fresh infer_e_leqI by auto
  qed
next
  case (infer_e_eqI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 bb c1 v2 z2 c2 z3)
  show ?case unfolding subst_b_simps proof(rule Typing.infer_e_eqI)
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  " using wf_b_subst(10) subst_db.simps infer_e_eqI wfX_wfY 
      by (metis wf_b_subst(15))
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " using infer_e_eqI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v1[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> \<lbrace> z1 : bb[bv::=b]\<^sub>b\<^sub>b  | c1[bv::=b]\<^sub>c\<^sub>b \<rbrace>" using subst_b_infer_v  infer_e_eqI subst_b_simps by force
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v2[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> \<lbrace> z2 : bb[bv::=b]\<^sub>b\<^sub>b  | c2[bv::=b]\<^sub>c\<^sub>b \<rbrace>" using subst_b_infer_v  infer_e_eqI subst_b_simps by force
    show "atom z3 \<sharp> AE_op Eq (v1[bv::=b]\<^sub>v\<^sub>b) (v2[bv::=b]\<^sub>v\<^sub>b)" using  subst_b_simps infer_e_eqI subst_b_fresh_x subst_b_e_def by metis
    show "atom z3 \<sharp> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b" using subst_g_b_x_fresh infer_e_eqI by auto
    show "bb[bv::=b]\<^sub>b\<^sub>b  \<in> {B_bool, B_int, B_unit}" using infer_e_eqI by auto
  qed
next
  case (infer_e_appI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> f x b' c \<tau>' s' v \<tau>)
  show ?case proof(subst subst_eb.simps, rule Typing.infer_e_appI)
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b"  using wf_b_subst(10) subst_db.simps infer_e_appI wfX_wfY by (metis wf_b_subst(15))
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " using infer_e_appI by auto
    show "Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ x b' c \<tau>' s'))) = lookup_fun \<Phi> f" using infer_e_appI by auto
        (*show  "\<Theta> ; {||} ; (x, b', c) #\<^sub>\<Gamma> GNil   \<turnstile>\<^sub>w\<^sub>f \<tau>'" using infer_e_appI sory*)
    have "atom bv \<sharp> b'"  using \<open>\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close> infer_e_appI wfPhi_f_supp  fresh_def[of "atom bv" b'] by simp
    hence "b' = b'[bv::=b]\<^sub>b\<^sub>b" using subst_b_simps 
      using has_subst_b_class.forget_subst subst_b_b_def by force
    moreover have  ceq:"c = c[bv::=b]\<^sub>c\<^sub>b" using subst_b_simps proof -
      have "supp c \<subseteq> {atom x}" using infer_e_appI wfPhi_f_simple_supp_c[OF  _  \<open>\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close>]  by simp
      hence "atom bv \<sharp> c" using
          fresh_def[of "atom bv" c] 
        using fresh_def fresh_finsert insert_absorb 
          insert_subset ms_fresh_all supp_at_base x_not_in_b_set fresh_prodN by metis
      thus ?thesis 
        using forget_subst subst_b_c_def  fresh_def[of "atom bv" c] by metis    
    qed 
    show   "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> v[bv::=b]\<^sub>v\<^sub>b \<Leftarrow> \<lbrace> x : b'  | c \<rbrace>"  
      using subst_b_check_v subst_tb.simps subst_vb.simps infer_e_appI 
    proof -
      have "\<Theta> ; {|bv|} ; \<Gamma> \<turnstile> v \<Leftarrow> \<lbrace> x : b' | c \<rbrace>"
        by (metis \<open>\<B> = {|bv|}\<close> \<open>\<Theta> ; \<B> ; \<Gamma> \<turnstile> v \<Leftarrow> \<lbrace> x : b' | c \<rbrace>\<close>) (* 0.0 ms *)
      then show ?thesis 
        by (metis (no_types) \<open>\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f b\<close> \<open>b' = b'[bv::=b]\<^sub>b\<^sub>b\<close> subst_b_check_v subst_tb.simps ceq) 
    qed
    show "atom x \<sharp> (\<Theta>, \<Phi>, {||}::bv fset, \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b, \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b, v[bv::=b]\<^sub>v\<^sub>b, \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)"
      apply (fresh_mth add:  fresh_prodN subst_g_b_x_fresh infer_e_appI )
      using subst_b_fresh_x infer_e_appI apply metis+
      done            
    have "supp \<tau>' \<subseteq> { atom x }" using wfPhi_f_simple_supp_t  infer_e_appI by auto
    hence "atom bv \<sharp> \<tau>'" using fresh_def fresh_at_base by force
    then  show  "\<tau>'[x::=v[bv::=b]\<^sub>v\<^sub>b]\<^sub>v = \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b" using infer_e_appI 
        forget_subst subst_b_\<tau>_def subst_tv_subst_vb_switch subst_defs by metis
  qed
next
  case (infer_e_appPI \<Theta>' \<B> \<Gamma>' \<Delta> \<Phi>' b' f' bv' x' b1 c \<tau>' s' v' \<tau>1)

  have beq: "b1[bv'::=b']\<^sub>b\<^sub>b[bv::=b]\<^sub>b\<^sub>b =  b1[bv'::=b'[bv::=b]\<^sub>b\<^sub>b]\<^sub>b\<^sub>b" 
  proof -
    have "supp b1 \<subseteq> { atom bv' }" using wfPhi_f_poly_supp_b infer_e_appPI 
      using supp_at_base by blast
    moreover have "bv \<noteq> bv'" using infer_e_appPI fresh_def supp_at_base 
      by (simp add: fresh_def supp_at_base)
    ultimately have "atom bv \<sharp> b1" using fresh_def fresh_at_base by force
    thus ?thesis by simp
  qed

  have ceq: "(c[bv'::=b']\<^sub>c\<^sub>b)[bv::=b]\<^sub>c\<^sub>b = c[bv'::=b'[bv::=b]\<^sub>b\<^sub>b]\<^sub>c\<^sub>b" proof -
    have "supp c \<subseteq> { atom bv', atom x' }" using wfPhi_f_poly_supp_c infer_e_appPI 
      using supp_at_base by blast
    moreover have "bv \<noteq> bv'" using infer_e_appPI fresh_def supp_at_base 
      by (simp add: fresh_def supp_at_base)
    moreover have "atom x' \<noteq> atom bv" by auto
    ultimately have "atom bv \<sharp> c" using fresh_def[of "atom bv" c] fresh_at_base by auto
    thus ?thesis by simp
  qed

  show ?case proof(subst subst_eb.simps, rule Typing.infer_e_appPI)
    show "\<Theta>' ; {||} ; \<Gamma>'[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b " using wf_b_subst subst_db.simps infer_e_appPI wfX_wfY by metis
    show "\<Theta>'  \<turnstile>\<^sub>w\<^sub>f \<Phi>' " using infer_e_appPI by auto
    show "Some (AF_fundef f' (AF_fun_typ_some bv' (AF_fun_typ x' b1 c \<tau>' s'))) = lookup_fun \<Phi>' f'" using infer_e_appPI by auto
    thus  "\<Theta>' ; {||} ; \<Gamma>'[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> v'[bv::=b]\<^sub>v\<^sub>b \<Leftarrow> \<lbrace> x' : b1[bv'::=b'[bv::=b]\<^sub>b\<^sub>b]\<^sub>b  | c[bv'::=b'[bv::=b]\<^sub>b\<^sub>b]\<^sub>b \<rbrace>"  
      using subst_b_check_v subst_tb.simps subst_b_simps infer_e_appPI 
    proof -
      have "\<Theta>' ; {||} ; \<Gamma>'[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> v'[bv::=b]\<^sub>v\<^sub>b \<Leftarrow> \<lbrace> x' : b1[bv'::=b']\<^sub>b[bv::=b]\<^sub>b\<^sub>b  | (c[bv'::=b']\<^sub>b)[bv::=b]\<^sub>c\<^sub>b \<rbrace>" 
        using  infer_e_appPI subst_b_check_v subst_tb.simps by metis
      thus  ?thesis using beq ceq  subst_defs by metis
    qed
    show "atom x' \<sharp> \<Gamma>'[bv::=b]\<^sub>\<Gamma>\<^sub>b" using subst_g_b_x_fresh infer_e_appPI by auto
    show  "\<tau>'[bv'::=b'[bv::=b]\<^sub>b\<^sub>b]\<^sub>b[x'::=v'[bv::=b]\<^sub>v\<^sub>b]\<^sub>v = \<tau>1[bv::=b]\<^sub>\<tau>\<^sub>b" proof - (* \<tau>'[bv'::=b']\<^sub>\<tau>\<^sub>b[x'::=v']\<^sub>\<tau>\<^sub>v = \<tau>1 *)

      have "supp \<tau>' \<subseteq> { atom x', atom bv' }" using wfPhi_f_poly_supp_t  infer_e_appPI by auto
      moreover hence "bv \<noteq> bv'" using infer_e_appPI fresh_def supp_at_base 
        by (simp add: fresh_def supp_at_base)
      ultimately have "atom bv \<sharp> \<tau>'" using fresh_def by force
      hence "\<tau>'[bv'::=b'[bv::=b]\<^sub>b\<^sub>b]\<^sub>b[x'::=v'[bv::=b]\<^sub>v\<^sub>b]\<^sub>v = \<tau>'[bv'::=b']\<^sub>b[x'::=v']\<^sub>v[bv::=b]\<^sub>\<tau>\<^sub>b"  using subst_tb_triple subst_defs by auto 
      thus ?thesis using infer_e_appPI by metis
    qed
    show "atom bv' \<sharp> (\<Theta>', \<Phi>', {||}, \<Gamma>'[bv::=b]\<^sub>\<Gamma>\<^sub>b, \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b, b'[bv::=b]\<^sub>b\<^sub>b, v'[bv::=b]\<^sub>v\<^sub>b, \<tau>1[bv::=b]\<^sub>\<tau>\<^sub>b)" 
      unfolding fresh_prodN apply( auto simp add: infer_e_appPI fresh_empty_fset)
      using fresh_subst_if subst_b_\<Gamma>_def  subst_b_\<Delta>_def  subst_b_b_def subst_b_v_def subst_b_\<tau>_def infer_e_appPI by metis+
    show "\<Theta>' ; {||}  \<turnstile>\<^sub>w\<^sub>f b'[bv::=b]\<^sub>b\<^sub>b " using infer_e_appPI wf_b_subst by simp
  qed
next
  case (infer_e_fstI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v z' b1 b2 c z)
  show ?case unfolding subst_b_simps proof(rule Typing.infer_e_fstI)
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b " using wf_b_subst(10) subst_db.simps infer_e_fstI wfX_wfY 
      by (metis wf_b_subst(15))
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " using infer_e_fstI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> \<lbrace> z' : B_pair b1[bv::=b]\<^sub>b\<^sub>b b2[bv::=b]\<^sub>b\<^sub>b  | c[bv::=b]\<^sub>c\<^sub>b \<rbrace>" 
      using subst_b_infer_v subst_tb.simps subst_b_simps infer_e_fstI by force
    show "atom z \<sharp> AE_fst (v[bv::=b]\<^sub>v\<^sub>b)" using infer_e_fstI subst_b_fresh_x subst_b_v_def e.fresh by metis
    show "atom z \<sharp> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b" using subst_g_b_x_fresh infer_e_fstI by auto
  qed
next
  case (infer_e_sndI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v z' b1 b2 c z)
  show ?case unfolding subst_b_simps proof(rule Typing.infer_e_sndI)
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  " using wf_b_subst(10) subst_db.simps infer_e_sndI wfX_wfY 
      by (metis wf_b_subst(15))
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " using infer_e_sndI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> \<lbrace> z' : B_pair b1[bv::=b]\<^sub>b\<^sub>b b2[bv::=b]\<^sub>b\<^sub>b  | c[bv::=b]\<^sub>c\<^sub>b \<rbrace>" 
      using subst_b_infer_v subst_tb.simps subst_b_simps infer_e_sndI by force
    show "atom z \<sharp> AE_snd (v[bv::=b]\<^sub>v\<^sub>b)" using infer_e_sndI subst_b_fresh_x subst_b_v_def e.fresh by metis
    show "atom z \<sharp> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b" using subst_g_b_x_fresh infer_e_sndI by auto
  qed
next
  case (infer_e_lenI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v z' c z)
  show ?case unfolding subst_b_simps proof(rule Typing.infer_e_lenI)
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  " using wf_b_subst(10) subst_db.simps infer_e_lenI wfX_wfY 
      by (metis wf_b_subst(15))
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " using infer_e_lenI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> \<lbrace> z' : B_bitvec  | c[bv::=b]\<^sub>c\<^sub>b \<rbrace>" 
      using subst_b_infer_v subst_tb.simps subst_b_simps infer_e_lenI by force
    show "atom z \<sharp> AE_len (v[bv::=b]\<^sub>v\<^sub>b)" using infer_e_lenI subst_b_fresh_x subst_b_v_def e.fresh by metis
    show "atom z \<sharp> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b" using subst_g_b_x_fresh infer_e_lenI by auto
  qed
next
  case (infer_e_mvarI \<Theta> \<B> \<Gamma> \<Phi> \<Delta> u \<tau>)
  show ?case proof(subst  subst subst_eb.simps, rule Typing.infer_e_mvarI)
    show "\<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b " using infer_e_mvarI wf_b_subst by auto
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> "  using infer_e_mvarI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b "   using infer_e_mvarI  using wf_b_subst(10) subst_db.simps infer_e_sndI wfX_wfY 
      by (metis wf_b_subst(15))
    show "(u, \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b) \<in> setD \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b"  using infer_e_mvarI subst_db.simps set_insert 
        subst_d_b_member by simp
  qed
next
  case (infer_e_concatI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 c2 z3)
  show ?case unfolding subst_b_simps proof(rule Typing.infer_e_concatI)
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b " using wf_b_subst(10) subst_db.simps infer_e_concatI wfX_wfY 
      by (metis wf_b_subst(15))
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " using infer_e_concatI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v1[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> \<lbrace> z1 : B_bitvec  | c1[bv::=b]\<^sub>c\<^sub>b \<rbrace>" 
      using subst_b_infer_v subst_tb.simps subst_b_simps infer_e_concatI by force
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v2[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> \<lbrace> z2 : B_bitvec  | c2[bv::=b]\<^sub>c\<^sub>b \<rbrace>" 
      using subst_b_infer_v subst_tb.simps subst_b_simps infer_e_concatI by force
    show "atom z3 \<sharp> AE_concat (v1[bv::=b]\<^sub>v\<^sub>b) (v2[bv::=b]\<^sub>v\<^sub>b)" using infer_e_concatI subst_b_fresh_x subst_b_v_def e.fresh by metis
    show "atom z3 \<sharp> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b" using subst_g_b_x_fresh infer_e_concatI by auto
  qed
next
  case (infer_e_splitI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 z3)
  show ?case unfolding subst_b_simps proof(rule Typing.infer_e_splitI)
    show \<open> \<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b \<close> using wf_b_subst(10) subst_db.simps infer_e_splitI wfX_wfY 
      by (metis wf_b_subst(15))
    show \<open> \<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> \<close>  using infer_e_splitI by auto
    show \<open> \<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v1[bv::=b]\<^sub>v\<^sub>b \<Rightarrow> \<lbrace> z1 : B_bitvec  | c1[bv::=b]\<^sub>c\<^sub>b \<rbrace>\<close>  
      using subst_b_infer_v subst_tb.simps subst_b_simps infer_e_splitI by force
    show \<open>\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> v2[bv::=b]\<^sub>v\<^sub>b \<Leftarrow> \<lbrace> z2 : B_int  | [ leq [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ z2 ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e   AND
                  [ leq [ [ z2 ]\<^sup>v ]\<^sup>c\<^sup>e [| [ v1[bv::=b]\<^sub>v\<^sub>b ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  ==  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e   \<rbrace>\<close>  
      using subst_b_check_v subst_tb.simps subst_b_simps infer_e_splitI 
    proof -
      have "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> v2[bv::=b]\<^sub>v\<^sub>b \<Leftarrow> \<lbrace> z2 : B_int | [ leq [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ z2 ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e == [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e AND [ leq [ [ z2 ]\<^sup>v ]\<^sup>c\<^sup>e [| [ v1 ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e == [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrace>[bv::=b]\<^sub>\<tau>\<^sub>b"
        using infer_e_splitI.hyps(7) infer_e_splitI.prems(1) infer_e_splitI.prems(2) subst_b_check_v by presburger (* 0.0 ms *)
      then show ?thesis
        by simp (* 0.0 ms *)
    qed
    show \<open>atom z1 \<sharp> AE_split (v1[bv::=b]\<^sub>v\<^sub>b) (v2[bv::=b]\<^sub>v\<^sub>b)\<close> using infer_e_splitI subst_b_fresh_x subst_b_v_def e.fresh by metis
    show \<open>atom z1 \<sharp> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b\<close> using subst_g_b_x_fresh infer_e_splitI by auto

    show \<open>atom z2 \<sharp> AE_split (v1[bv::=b]\<^sub>v\<^sub>b) (v2[bv::=b]\<^sub>v\<^sub>b)\<close>  using infer_e_splitI subst_b_fresh_x subst_b_v_def e.fresh by metis

    show \<open>atom z2 \<sharp> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b\<close> using subst_g_b_x_fresh infer_e_splitI by auto
    show \<open>atom z3 \<sharp> AE_split (v1[bv::=b]\<^sub>v\<^sub>b) (v2[bv::=b]\<^sub>v\<^sub>b)\<close>  using infer_e_splitI subst_b_fresh_x subst_b_v_def e.fresh by metis
    show \<open>atom z3 \<sharp> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b\<close> using subst_g_b_x_fresh infer_e_splitI by auto
  qed
qed

text \<open>This is needed for preservation. When we apply a function "f [b] v" we need to 
substitute into the body of the function f replacing type-variable with b\<close>

lemma subst_b_c_of_forget:
  assumes "atom bv \<sharp> const"
  shows "(c_of const x)[bv::=b]\<^sub>c\<^sub>b = c_of const x" 
  using assms proof(nominal_induct const avoiding: x rule:\<tau>.strong_induct)
  case (T_refined_type x' b' c')
  hence "c_of \<lbrace> x' : b' | c' \<rbrace> x = c'[x'::=V_var x]\<^sub>c\<^sub>v" using c_of.simps by metis
  moreover have "atom bv \<sharp> c'[x'::=V_var x]\<^sub>c\<^sub>v" proof -
    have "atom bv \<sharp> c'" using T_refined_type \<tau>.fresh by simp
    moreover have "atom bv \<sharp> V_var x" using v.fresh by simp
    ultimately show ?thesis   
      using T_refined_type \<tau>.fresh subst_b_c_def fresh_subst_if
        \<tau>_fresh_c fresh_subst_cv_if has_subst_b_class.subst_b_fresh_x ms_fresh_all(37) ms_fresh_all assms by metis
  qed
  ultimately show ?case using forget_subst subst_b_c_def by metis
qed

lemma subst_b_check_s:
  fixes s::s and b::b and cs::branch_s and css::branch_list and v::v and \<tau>::\<tau>
  assumes "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f b"  and "B = {|bv|}" (*and "D = []"*)
  shows  "\<Theta> ; \<Phi> ; B ; G; D \<turnstile> s \<Leftarrow> \<tau> \<Longrightarrow> \<Theta> ; \<Phi> ; {||} ; G[bv::=b]\<^sub>\<Gamma>\<^sub>b; D[bv::=b]\<^sub>\<Delta>\<^sub>b \<turnstile> (s[bv::=b]\<^sub>s\<^sub>b) \<Leftarrow> (\<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)" and
    "\<Theta> ; \<Phi> ; B ; G; D ; tid ; cons ; const ; v \<turnstile> cs \<Leftarrow> \<tau> \<Longrightarrow> \<Theta> ; \<Phi> ; {||} ; G[bv::=b]\<^sub>\<Gamma>\<^sub>b; D[bv::=b]\<^sub>\<Delta>\<^sub>b ; tid ; cons ; const ; v[bv::=b]\<^sub>v\<^sub>b \<turnstile> (subst_branchb cs bv b) \<Leftarrow> (\<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)" and
    "\<Theta> ; \<Phi> ; B ; G; D ; tid ; dclist ; v \<turnstile> css \<Leftarrow> \<tau> \<Longrightarrow> \<Theta> ; \<Phi> ; {||} ; G[bv::=b]\<^sub>\<Gamma>\<^sub>b; D[bv::=b]\<^sub>\<Delta>\<^sub>b ; tid ; dclist ; v[bv::=b]\<^sub>v\<^sub>b \<turnstile> (subst_branchlb css bv b ) \<Leftarrow> (\<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)" 
  using assms proof(induct  rule: check_s_check_branch_s_check_branch_list.inducts)
  note facts = wfD_emptyI wfX_wfY wf_b_subst subst_b_subtype subst_b_infer_v
  case (check_valI \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v \<tau>' \<tau>)
  show ?case 
    apply(subst subst_sb.simps, rule Typing.check_valI) 
    using facts check_valI apply metis
    using check_valI subst_b_infer_v wf_b_subst subst_b_subtype apply blast
    using check_valI subst_b_infer_v wf_b_subst subst_b_subtype apply blast  
    using check_valI subst_b_infer_v wf_b_subst subst_b_subtype by metis
next
  case (check_letI x \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e \<tau> z s b' c)
  show ?case proof(subst subst_sb.simps, rule Typing.check_letI) 

    show "atom x \<sharp>(\<Theta>, \<Phi>, {||}, \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b, \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b, e[bv::=b]\<^sub>e\<^sub>b, \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)" (*using check_letI  subst_b_\<tau>_def subst_b_\<Gamma>_def subst_b_fresh_x fresh_prod4 subst_b_c_def sory*)
      apply(unfold fresh_prodN,auto)
      apply(simp add: check_letI fresh_empty_fset)+
      apply(metis *   subst_b_fresh_x check_letI fresh_prodN)+ done
    show "atom z \<sharp> (x, \<Theta>, \<Phi>, {||}, \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b, \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b, e[bv::=b]\<^sub>e\<^sub>b, \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b, s[bv::=b]\<^sub>s\<^sub>b)"  
      apply(unfold fresh_prodN,auto)
      apply(simp add: check_letI fresh_empty_fset)+
      apply(metis *   subst_b_fresh_x check_letI fresh_prodN)+ done
    show "\<Theta> ; \<Phi> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  \<turnstile> e[bv::=b]\<^sub>e\<^sub>b \<Rightarrow> \<lbrace> z : b'[bv::=b]\<^sub>b\<^sub>b  | c[bv::=b]\<^sub>c\<^sub>b  \<rbrace>" 
      using check_letI subst_b_infer_e subst_tb.simps by metis
    have "c[z::=[ x ]\<^sup>v]\<^sub>c\<^sub>v[bv::=b]\<^sub>c\<^sub>b =  (c[bv::=b]\<^sub>c\<^sub>b)[z::=V_var x]\<^sub>c\<^sub>v" 
      using subst_cv_subst_bb_commute[of bv "V_var x" c z b] fresh_at_base by simp
    thus "\<Theta> ; \<Phi> ; {||} ; ((x, b'[bv::=b]\<^sub>b\<^sub>b , (c[bv::=b]\<^sub>c\<^sub>b)[z::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b) ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  \<turnstile> s[bv::=b]\<^sub>s\<^sub>b \<Leftarrow> \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b" 
      using check_letI subst_gb.simps subst_defs by metis
  qed
next
  case (check_assertI x \<Theta> \<Phi> \<B> \<Gamma> \<Delta> c \<tau> s)
  show ?case proof(subst subst_sb.simps, rule Typing.check_assertI)
    show "atom x \<sharp> (\<Theta>, \<Phi>, {||}, \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b, \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b,  c[bv::=b]\<^sub>c\<^sub>b, \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b, s[bv::=b]\<^sub>s\<^sub>b)"   
      apply(unfold fresh_prodN,auto)
      apply(simp add: check_assertI fresh_empty_fset)+
      apply(metis *   subst_b_fresh_x check_assertI fresh_prodN)+ done

    have "\<Theta> ; \<Phi> ; {||} ; ((x, B_bool, c) #\<^sub>\<Gamma> \<Gamma>)[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  \<turnstile> s[bv::=b]\<^sub>s\<^sub>b \<Leftarrow> \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b" using  check_assertI
      by metis
    thus "\<Theta> ; \<Phi> ; {||} ; (x, B_bool, c[bv::=b]\<^sub>c\<^sub>b) #\<^sub>\<Gamma> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  \<turnstile> s[bv::=b]\<^sub>s\<^sub>b \<Leftarrow> \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b" using  subst_gb.simps by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<Turnstile> c[bv::=b]\<^sub>c\<^sub>b " using subst_b_valid  check_assertI by simp
    show " \<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b " using wf_b_subst2(6) check_assertI by simp
  qed
next
  case (check_branch_list_consI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist v cs \<tau> css)
  then show ?case unfolding subst_branchlb.simps using Typing.check_branch_list_consI by simp
next
  case (check_branch_list_finalI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dclist v cs \<tau>)
  then show ?case unfolding subst_branchlb.simps using Typing.check_branch_list_finalI by simp
next
  case (check_branch_s_branchI \<Theta> \<B> \<Gamma> \<Delta> \<tau> const x \<Phi> tid cons v s)

  show ?case unfolding subst_b_simps proof(rule Typing.check_branch_s_branchI) 
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  "  using check_branch_s_branchI wf_b_subst subst_db.simps by metis
    show "\<turnstile>\<^sub>w\<^sub>f \<Theta> " using check_branch_s_branchI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b   \<turnstile>\<^sub>w\<^sub>f \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b "   using check_branch_s_branchI wf_b_subst by metis

    show "atom x \<sharp>(\<Theta>, \<Phi>, {||}, \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b, \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b, tid, cons , const, v[bv::=b]\<^sub>v\<^sub>b, \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)"       
      apply(unfold fresh_prodN,auto)
      apply(simp add: check_branch_s_branchI fresh_empty_fset)+
      apply(metis *   subst_b_fresh_x check_branch_s_branchI fresh_prodN)+
      done
    show wft:"\<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f  const" using check_branch_s_branchI  by auto
    hence "(b_of const) = (b_of const)[bv::=b]\<^sub>b\<^sub>b" 
      using wfT_nil_supp   fresh_def[of "atom bv" ] forget_subst subst_b_b_def \<tau>.supp
        bot.extremum_uniqueI ex_in_conv fresh_def supp_empty_fset 
      by (metis b_of_supp)
    moreover have "(c_of const x)[bv::=b]\<^sub>c\<^sub>b = c_of const x" 
      using wft   wfT_nil_supp   fresh_def[of "atom bv" ] forget_subst subst_b_c_def \<tau>.supp
        bot.extremum_uniqueI ex_in_conv fresh_def supp_empty_fset  subst_b_c_of_forget by metis
    ultimately show  "\<Theta> ; \<Phi> ; {||} ; (x, b_of const, CE_val (v[bv::=b]\<^sub>v\<^sub>b)  ==  CE_val(V_cons tid cons (V_var x)) AND c_of const x) #\<^sub>\<Gamma> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b   \<turnstile> s[bv::=b]\<^sub>s\<^sub>b \<Leftarrow> \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b"  
      using check_branch_s_branchI subst_gb.simps by auto
  qed
next
  case (check_ifI z \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v s1 s2 \<tau>)
  show ?case unfolding subst_b_simps proof(rule  Typing.check_ifI) 
    show \<open>atom z \<sharp> (\<Theta>, \<Phi>, {||}, \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b, \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b, v[bv::=b]\<^sub>v\<^sub>b, s1[bv::=b]\<^sub>s\<^sub>b, s2[bv::=b]\<^sub>s\<^sub>b, \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)\<close> 
      by(unfold fresh_prodN,auto, auto simp add: check_ifI fresh_empty_fset subst_b_fresh_x )
    have "\<lbrace> z : B_bool  | TRUE \<rbrace>[bv::=b]\<^sub>\<tau>\<^sub>b  = \<lbrace> z : B_bool  | TRUE \<rbrace>"  by auto
    thus \<open>\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> v[bv::=b]\<^sub>v\<^sub>b \<Leftarrow> \<lbrace> z : B_bool  | TRUE \<rbrace>\<close> using check_ifI subst_b_check_v by metis
    show \<open> \<Theta> ; \<Phi> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  \<turnstile> s1[bv::=b]\<^sub>s\<^sub>b \<Leftarrow> \<lbrace> z : b_of \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b  | CE_val (v[bv::=b]\<^sub>v\<^sub>b)  ==  CE_val (V_lit L_true)   IMP  c_of \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b z  \<rbrace>\<close> 
      using subst_b_if check_ifI by metis
    show \<open> \<Theta> ; \<Phi> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  \<turnstile> s2[bv::=b]\<^sub>s\<^sub>b \<Leftarrow> \<lbrace> z : b_of \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b  | CE_val (v[bv::=b]\<^sub>v\<^sub>b)  ==  CE_val (V_lit L_false)   IMP  c_of \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b z  \<rbrace>\<close> 
      using subst_b_if check_ifI by metis
  qed
next
  case (check_let2I x \<Theta> \<Phi> \<B> G \<Delta> t s1 \<tau> s2 )
  show ?case unfolding subst_b_simps proof (rule Typing.check_let2I)
    have "atom x \<sharp> b" using x_fresh_b by auto
    show \<open>atom x \<sharp> (\<Theta>, \<Phi>, {||}, G[bv::=b]\<^sub>\<Gamma>\<^sub>b, \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b, t[bv::=b]\<^sub>\<tau>\<^sub>b, s1[bv::=b]\<^sub>s\<^sub>b, \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)\<close>      
      apply(unfold fresh_prodN, auto, auto simp add: check_let2I fresh_prodN fresh_empty_fset)
      apply(metis  subst_b_fresh_x check_let2I fresh_prodN)+
      done

    show \<open> \<Theta> ; \<Phi> ; {||} ; G[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  \<turnstile> s1[bv::=b]\<^sub>s\<^sub>b \<Leftarrow> t[bv::=b]\<^sub>\<tau>\<^sub>b \<close> using check_let2I subst_tb.simps  by auto
    show \<open> \<Theta> ; \<Phi> ; {||} ; (x, b_of t[bv::=b]\<^sub>\<tau>\<^sub>b, c_of t[bv::=b]\<^sub>\<tau>\<^sub>b x) #\<^sub>\<Gamma> G[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  \<turnstile> s2[bv::=b]\<^sub>s\<^sub>b \<Leftarrow> \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b\<close> 
      using check_let2I subst_tb.simps  subst_gb.simps b_of.simps subst_b_c_of subst_b_b_of by auto
  qed
next
  case (check_varI u \<Theta> \<Phi> \<B> \<Gamma> \<Delta> \<tau>' v \<tau> s)
  show ?case unfolding subst_b_simps proof(rule Typing.check_varI) 
    show "atom u \<sharp>  (\<Theta>, \<Phi>, {||}, \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b, \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b, \<tau>'[bv::=b]\<^sub>\<tau>\<^sub>b, v[bv::=b]\<^sub>v\<^sub>b, \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b) "
      by(unfold fresh_prodN,auto simp add: check_varI fresh_empty_fset subst_b_fresh_u )
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> v[bv::=b]\<^sub>v\<^sub>b \<Leftarrow> \<tau>'[bv::=b]\<^sub>\<tau>\<^sub>b" using check_varI subst_b_check_v by auto
    show "\<Theta> ; \<Phi> ; {||} ; (subst_gb  \<Gamma> bv b) ; (u, (\<tau>'[bv::=b]\<^sub>\<tau>\<^sub>b)) #\<^sub>\<Delta> (subst_db  \<Delta> bv b)   \<turnstile> (s[bv::=b]\<^sub>s\<^sub>b) \<Leftarrow> (\<tau>[bv::=b]\<^sub>\<tau>\<^sub>b)" using check_varI by auto
  qed
next
  case (check_assignI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> u \<tau> v z \<tau>')
  show ?case unfolding subst_b_simps proof( rule Typing.check_assignI) 
    show "\<Theta>  \<turnstile>\<^sub>w\<^sub>f \<Phi> " using check_assignI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile>\<^sub>w\<^sub>f \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b " using wf_b_subst check_assignI by auto
    show "(u, \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b) \<in> setD \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b" using check_assignI subst_d_b_member  by simp
    show " \<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> v[bv::=b]\<^sub>v\<^sub>b \<Leftarrow> \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b"  using check_assignI subst_b_check_v by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> \<lbrace> z : B_unit  | TRUE \<rbrace> \<lesssim> \<tau>'[bv::=b]\<^sub>\<tau>\<^sub>b" using check_assignI subst_b_subtype subst_b_simps subst_tb.simps by fastforce
  qed
next
  case (check_whileI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 z s2 \<tau>')
  show ?case unfolding subst_b_simps proof(rule Typing.check_whileI) 
    show "\<Theta> ; \<Phi> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  \<turnstile> s1[bv::=b]\<^sub>s\<^sub>b \<Leftarrow> \<lbrace> z : B_bool  | TRUE \<rbrace>" using check_whileI by auto
    show "\<Theta> ; \<Phi> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  \<turnstile> s2[bv::=b]\<^sub>s\<^sub>b \<Leftarrow> \<lbrace> z : B_unit  | TRUE \<rbrace>" using check_whileI by auto
    show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> \<lbrace> z : B_unit  | TRUE \<rbrace> \<lesssim> \<tau>'[bv::=b]\<^sub>\<tau>\<^sub>b"  using subst_b_subtype check_whileI by fastforce
  qed     
next
  case (check_seqI \<Theta> \<Phi> \<B> \<Gamma> \<Delta> s1 z s2 \<tau>)
  then show ?case unfolding subst_sb.simps using check_seqI Typing.check_seqI subst_b_eq by metis
next
  case (check_caseI \<Theta> \<Phi> \<B>  \<Gamma> \<Delta> tid dclist v cs \<tau>  z)
  show ?case unfolding subst_b_simps proof(rule Typing.check_caseI)
    show \<open> \<Theta> ;  \<Phi> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b ; \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b ; tid ; dclist ; v[bv::=b]\<^sub>v\<^sub>b \<turnstile> subst_branchlb cs bv b \<Leftarrow> \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b\<close> using check_caseI by auto
    show \<open>AF_typedef tid dclist \<in> set \<Theta>\<close> using check_caseI by auto
    show \<open>\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> v[bv::=b]\<^sub>v\<^sub>b \<Leftarrow> \<lbrace> z : B_id tid  | TRUE \<rbrace>\<close> using check_caseI subst_b_check_v subst_b_simps subst_tb.simps subst_b_simps       
    proof -
      have "\<lbrace> z : B_id tid | TRUE \<rbrace> = \<lbrace> z : B_id tid | TRUE \<rbrace>[bv::=b]\<^sub>\<tau>\<^sub>b" using subst_b_eq by auto
      then show ?thesis
        by (metis (no_types) check_caseI.hyps(4) check_caseI.prems(1) check_caseI.prems(2) subst_b_check_v) (* 31 ms *)
    qed
    show \<open>   \<turnstile>\<^sub>w\<^sub>f \<Theta> \<close> using check_caseI by auto
  qed
qed

end
