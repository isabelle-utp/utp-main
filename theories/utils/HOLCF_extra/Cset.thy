theory Cset
imports HOLCF Tr_Logic Cfun_Partial "~~/src/HOL/HOLCF/Library/HOL_Cpo"
begin

section {* LCF-style sets *}

default_sort pcpo

subsection {* Definition of continuous set type *}

pcpodef (open) 'a cset = "{f :: 'a \<rightarrow> tr. f\<cdot>\<bottom> = \<bottom>}"
  by simp_all

definition
  cset_abs :: "('a \<rightarrow> tr) \<rightarrow> ('a cset)"
where
  "cset_abs = (\<Lambda> f. Abs_cset (strictify\<cdot>f))"

definition
  cset_rep :: "('a cset) \<rightarrow> ('a \<rightarrow> tr)"
where
  "cset_rep = (\<Lambda> xs. Rep_cset xs)"

definition CCollect :: "('a \<rightarrow> tr) \<Rightarrow> 'a cset" where
"CCollect = (\<lambda> f. cset_abs\<cdot>f)"

text {* Set collect for flat values only, guaranteed continuity *}
definition CCollectF :: "(('a::pcpo) \<Rightarrow> tr) \<Rightarrow> 'a cset" where
"CCollectF \<equiv> \<lambda> f. cset_abs\<cdot>(\<Lambda> x. if (x \<in> flat) then f x else \<bottom>)"

definition cmember :: "'a \<Rightarrow> 'a cset \<Rightarrow> tr" where
"cmember x P = (cset_rep\<cdot>P)\<cdot>x"

notation (xsymbols)
  cmember    ("op \<in>\<in>") and
  cmember    ("(_/ \<in>\<in> _)" [50, 51] 50)

lemma cset_rep_beta: "cset_rep\<cdot>f = Rep_cset f"
  unfolding cset_rep_def by (simp add: cont_Rep_cset)

lemma Rep_cset_strict' [simp]: "Rep_cset xs\<cdot>\<bottom> = \<bottom>"
  by (insert Rep_cset[of xs], simp)

lemma cset_rep_strict' [simp]: "cset_rep\<cdot>xs\<cdot>\<bottom> = \<bottom>"
  by (simp add:cset_rep_def cont_Rep_cset)

lemma cset_abs_cset_rep [simp]: "cset_abs\<cdot>(cset_rep\<cdot>xs) = xs"
  unfolding cset_abs_def cset_rep_def
  by (simp add: cont_Rep_cset cont_Abs_cset strictify_cancel Rep_cset_inverse)

lemma cset_rep_cset_abs [simp]: "cset_rep\<cdot>(cset_abs\<cdot>f) = strictify\<cdot>f"
  unfolding cset_abs_def cset_rep_def
  by (simp add: cont_Abs_cset cont_Rep_cset Abs_cset_inverse strictify_cancel)

lemma cset_rep_strict [simp]: "cset_rep\<cdot>\<bottom> = \<bottom>"
  unfolding cset_rep_beta 
  by (rule Rep_cset_strict)

lemma cset_abs_mem_beta [simp]: "(x \<in>\<in> cset_abs\<cdot>f) = strictify\<cdot>f\<cdot>x"
  by (simp add:cmember_def)

lemma cset_abs_strict [simp]: "cset_abs\<cdot>\<bottom> = \<bottom>"
  by (metis (hide_lams, no_types) cset_abs_cset_rep strictI)

lemma cset_eq_iff: "xs = ys \<longleftrightarrow> cset_rep\<cdot>xs = cset_rep\<cdot>ys"
  by (simp add: cset_rep_def cont_Rep_cset Rep_cset_inject)

lemma cset_below_iff: "xs \<sqsubseteq> ys \<longleftrightarrow> cset_rep\<cdot>xs \<sqsubseteq> cset_rep\<cdot>ys"
  by (simp add: cset_rep_def cont_Rep_cset below_cset_def)

lemma cmem_CCollect_eq [iff]: "cmember a (CCollect P) = strictify\<cdot>P\<cdot>a"
  by (simp add:cmember_def CCollect_def Abs_cset_inverse)

lemma CCollect_cmem_eq [simp]: "CCollect (\<Lambda> x. cmember x A) = A"
  by (simp add: CCollect_def cmember_def Rep_cfun_inverse Rep_cset_inverse)

text {* Continuity of membership and collect *}

lemma cont_CCollect [simp,cont2cont]: "cont f \<Longrightarrow> cont (\<lambda>x . CCollect (f x))"
  by (simp add:CCollect_def cont_Abs_cset)

lemma cont_flat_func [simp, cont2cont]: "cont (\<lambda> x. if (x \<in> flat) then f x else \<bottom>)"
  by (rule cont_flat_cdom, auto simp add:cdom_def)

lemma cont_CCollectF [simp,cont2cont]: "cont f \<Longrightarrow> cont (\<lambda>x . CCollectF (f x))"
  apply (auto simp add:CCollectF_def)
  apply (rule cont2cont, simp)
  apply (rule cont2cont_LAM)
  apply (rule cont2cont)
  apply (rule cont2cont)
  apply (simp)
  apply (rule cont2cont_fun)
  apply (simp_all)
done

lemma cont_cmember1 [simp,cont2cont]: "cont f \<Longrightarrow> cont (\<lambda> x. f x \<in>\<in> xs)"
  by (simp add:cmember_def cont_Rep_cset)

lemma cont_cmember2 [simp,cont2cont]: "cont f \<Longrightarrow> cont (\<lambda> xs. x \<in>\<in> f xs)"
  by (simp add:cmember_def cont_Rep_cset)

lemma cont_Rep_cset1: "cont (\<lambda>x. x \<in>\<in> xs)"
  by simp

lemma cont_Rep_cset2: "cont (\<lambda>xs. x \<in>\<in> xs)"
  by simp

lemmas monofun_Rep_cset = cont_Rep_cset [THEN cont2mono]

lemmas monofun_Rep_cset1 = cont_Rep_cset1 [THEN cont2mono]
lemmas monofun_Rep_cset2 = cont_Rep_cset2 [THEN cont2mono]

(*
lemma CCollectF_mem [simp]: "x \<in> flat \<Longrightarrow> x \<in>\<in> CCollectF f = f x"
  apply (simp add:cmember_def CCollectF_def)
*)

text {* Extensionality for continuous sets *}

lemma cset_mem_iff: "xs = ys \<longleftrightarrow> (\<forall>x. (x \<in>\<in> xs) = (x \<in>\<in> ys))"
  by (auto simp add:cmember_def Rep_cset_inject [symmetric] cfun_eq_iff cset_rep_beta)

lemma cset_eqI: "(\<And>x. (x \<in>\<in> xs) = (x \<in>\<in> ys)) \<Longrightarrow> xs = ys"
  by (simp add: cset_mem_iff)

text {* Extensionality wrt. ordering for continuous sets *}

lemma cset_mem_below_iff: "xs \<sqsubseteq> ys \<longleftrightarrow> (\<forall>x. (x \<in>\<in> xs) \<sqsubseteq> (x \<in>\<in> ys))" 
  by (auto simp add: below_cset_def cfun_below_iff cmember_def cset_rep_beta)

lemma cset_belowI: "(\<And>x. (x \<in>\<in> xs) \<sqsubseteq> (x \<in>\<in> ys)) \<Longrightarrow> xs \<sqsubseteq> ys"
  by (simp add: cset_mem_below_iff)

text {* monotonicity of membership *}

lemma monofun_cset_set: "xs \<sqsubseteq> ys \<Longrightarrow> (x \<in>\<in> xs) \<sqsubseteq> (x \<in>\<in> ys)"
  by (simp add: cset_mem_below_iff)

lemma monofun_cset_mem: "x \<sqsubseteq> y \<Longrightarrow> (x \<in>\<in> xs) \<sqsubseteq> (y \<in>\<in> xs)"
  by (rule monofun_Rep_cset1 [THEN monofunE], simp)

lemma monofun_cfun: "\<lbrakk>xs \<sqsubseteq> ys; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> (x \<in>\<in> xs) \<sqsubseteq> (y \<in>\<in> ys)"
  by (rule below_trans [OF monofun_cset_set monofun_cset_mem])

text {* Set Mapping Function *}

definition cset_map :: "('b \<rightarrow> 'a) \<rightarrow> ('a cset) \<rightarrow> ('b cset)" where
"cset_map = (\<Lambda> f. cset_abs oo cfun_map\<cdot>f\<cdot>ID oo cset_rep)"

lemma cset_map_beta [simp]: "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> (x \<in>\<in> cset_map\<cdot>f\<cdot>xs) = (f\<cdot>x \<in>\<in> xs)"
  by (simp add:cset_map_def cfun_map_def cont2cont_LAM cfun_eq_iff cmember_def strictify_cancel)

lemma cset_map_ID [domain_map_ID]: "cset_map\<cdot>ID = ID"
  unfolding cfun_eq_iff cset_mem_iff by simp

lemma cset_map_map:
  "\<lbrakk> f1\<cdot>\<bottom> = \<bottom>; f2\<cdot>\<bottom> = \<bottom> \<rbrakk> \<Longrightarrow>
   cset_map\<cdot>f1\<cdot>(cset_map\<cdot>f2\<cdot>p) =
    cset_map\<cdot>(\<Lambda> x. f2\<cdot>(f1\<cdot>x))\<cdot>p"
  by (rule cset_eqI) simp


lemma ep_pair_cset_map:
  assumes "ep_pair e p"
  shows "ep_pair (cset_map\<cdot>p) (cset_map\<cdot>e)"
proof
  interpret e1p1: pcpo_ep_pair e p 
    unfolding pcpo_ep_pair_def by fact
  fix x show "cset_map\<cdot>e\<cdot>(cset_map\<cdot>p\<cdot>x) = x"
    unfolding cset_map_def
    apply (simp add:cset_eq_iff strictify_cancel)
    apply (rule ep_pair.e_inverse)
    apply (rule ep_pair_cfun_map)
    apply (simp add:assms)
    apply (simp add:ep_pair_ID_ID)
  done

  fix x show "cset_map\<cdot>p\<cdot>(cset_map\<cdot>e\<cdot>x) \<sqsubseteq> x"
    apply (rule cset_belowI, simp)
    apply (rule monofun_cset_mem)
    apply (rule e1p1.e_p_below)
  done
qed


lemma deflation_cset_map [domain_deflation]:
  assumes 1: "deflation d"
  shows "deflation (cset_map\<cdot>d)"
apply (rule deflation.intro)
apply (rule cset_eqI)
apply (metis "1" cset_map_beta deflation.idem deflation_strict)
apply (metis "1" ID1 cset_map_ID deflation.below_ID monofun_cfun_arg monofun_cfun_fun)
done

(*
lemma Collect_eq_iff: "x = y \<longleftrightarrow> CCollect x = CCollect y"
  apply (simp add:cfun_eq_iff cmem_CCollect_eq)
  apply (simp add:CCollect_def)
  by (metis cfun_eq_iff cmem_CCollect_eq)
*)

lemma sort_finite_deflation: "deflation (d:: ('a::{cpo,finite}) \<rightarrow> 'a) \<Longrightarrow> finite_deflation d"
   by (rule finite_deflation_intro, simp_all add:finite)

lemma UNIV_tr: "(UNIV :: tr set) = {\<bottom>,TT,FF}"
  by (auto, case_tac x rule:trE, simp_all)

lemma finite_tr: "finite (UNIV :: tr set)"
  by (simp add:UNIV_tr)

lemma finite_deflation_cset_map:
  assumes 1: "finite_deflation d"
  shows "finite_deflation (cset_map\<cdot>d)"
proof (intro finite_deflation_intro)
  interpret d1: finite_deflation d by fact
  have "deflation d" by fact
  thus "deflation (cset_map\<cdot>d)" by (rule deflation_cset_map)

  have findef_ID: "finite_deflation (ID :: tr \<rightarrow> tr)"
    apply (rule finite_deflation_intro)
    apply (simp add:deflation_ID)
    apply (metis finite_imageI finite_range_imp_finite_fixes finite_tr)
  done
   
  from 1 findef_ID have "finite_deflation (cfun_map\<cdot>d\<cdot>(ID :: tr \<rightarrow> tr))"
    by (rule finite_deflation_cfun_map)

  then have "finite {f. cfun_map\<cdot>d\<cdot>(ID :: tr \<rightarrow>tr)\<cdot>f = f}"
    by (rule finite_deflation.finite_fixes)

  moreover have "inj (\<lambda>f. cset_rep\<cdot>f)"
    by (rule inj_onI, simp add:cset_eq_iff)
  ultimately have "finite ((\<lambda>xs. cset_rep\<cdot>xs) -` {f. cfun_map\<cdot>d\<cdot>ID\<cdot>f = f})"
    by (rule finite_vimageI)
  then show "finite {f. cset_map\<cdot>d\<cdot>f = f}"
    unfolding cset_map_def cset_eq_iff
    apply (simp add:strictify_cancel)
    apply (subgoal_tac "\<And> f. cfun_map\<cdot>d\<cdot>ID\<cdot>(cset_rep\<cdot>f)\<cdot>\<bottom> = \<bottom>")
    apply (simp add:strictify_cancel)
    apply (simp)
    apply (metis (hide_lams, no_types) Rep_cset_strict' below_bottom_iff cset_rep_beta d1.below)
  done
qed

lemma approx_chain_cset_map:
  assumes "approx_chain a"
  shows "approx_chain (\<lambda>i. cset_map\<cdot>(a i))"
  using assms unfolding approx_chain_def
  by (simp add: lub_APP cset_map_ID finite_deflation_cset_map)

instance cset :: (bifinite) bifinite
proof
  show "\<exists>(a::nat \<Rightarrow> ('a cset) \<rightarrow> ('a cset)). approx_chain a"
    using bifinite [where 'a='a]
    by (fast intro!: approx_chain_cset_map)
qed

definition "cset_emb = udom_emb (\<lambda>i. cset_map\<cdot>(udom_approx i))"
definition "cset_prj = udom_prj (\<lambda>i. cset_map\<cdot>(udom_approx i))"

lemma ep_pair_cset: "ep_pair cset_emb cset_prj"
  unfolding cset_emb_def cset_prj_def
  by (simp add: ep_pair_udom approx_chain_cset_map)

definition cset_defl :: "udom defl \<rightarrow> udom defl"
  where "cset_defl = defl_fun1 cset_emb cset_prj cset_map"

lemma cast_cset_defl:
  "cast\<cdot>(cset_defl\<cdot>A) =
    cset_emb oo cset_map\<cdot>(cast\<cdot>A) oo cset_prj"
using ep_pair_cset finite_deflation_cset_map
unfolding cset_defl_def by (rule cast_defl_fun1)

instantiation cset :: ("domain") "domain"
begin

definition
  "emb = cset_emb oo cset_map\<cdot>prj"

definition
  "prj = cset_map\<cdot>emb oo cset_prj"

definition
  "defl (t::('a cset) itself) = cset_defl\<cdot>DEFL('a)"

definition
  "(liftemb :: ('a cset) u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> ('a cset) u) = u_map\<cdot>prj"

definition
  "liftdefl (t::('a cset) itself) = liftdefl_of\<cdot>DEFL('a cset)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a cset)"
    unfolding emb_cset_def prj_cset_def
    by (intro ep_pair_comp ep_pair_cset ep_pair_cset_map ep_pair_emb_prj)
  show "cast\<cdot>DEFL('a cset) = emb oo (prj :: udom \<rightarrow> 'a cset)"
    unfolding emb_cset_def prj_cset_def defl_cset_def cast_cset_defl
    by (simp add: cast_DEFL oo_def cset_eq_iff cset_map_map)
qed (fact liftemb_cset_def liftprj_cset_def liftdefl_cset_def)+

end

lemma DEFL_cset [domain_defl_simps]:
  "DEFL('a::domain cset) = cset_defl\<cdot>DEFL('a)"
by (rule defl_cset_def)

lemma isodefl_cset [domain_isodefl]:
  "isodefl d t \<Longrightarrow>
    isodefl (cset_map\<cdot>d) (cset_defl\<cdot>t)"
apply (rule isodeflI)
apply (simp add: cast_cset_defl cast_isodefl)
apply (simp add: emb_cset_def prj_cset_def)
apply (simp add: cset_map_map isodefl_strict)
done



setup {*
  fold Domain_Take_Proofs.add_rec_type
    [(@{type_name cset}, [true])]
*}

lemma cmem_bot [simp]: "x \<in>\<in> \<bottom> = \<bottom>"
  by (simp add:cmember_def)

lemma CCollect_bot [simp]: "CCollect \<bottom> = \<bottom>"
  by (simp add:CCollect_def)

subsection {* Set operators *}

definition cempty :: "'a cset" ("\<emptyset>") where
"\<emptyset> = CCollect (\<Lambda> x. FF)"

definition cuniv :: "'a cset" where
"cuniv = CCollect (\<Lambda> x. TT)"

lemma cmem_empty [simp]: "x \<noteq> \<bottom> \<Longrightarrow> x \<in>\<in> \<emptyset> = FF"
  by (simp add:cmember_def cempty_def CCollect_def Abs_cset_inverse)

lemma cmem_cuniv [simp]: "x \<noteq> \<bottom> \<Longrightarrow> x \<in>\<in> cuniv = TT"
  by (simp add:cmember_def cuniv_def CCollect_def Abs_cset_inverse)

definition cunion :: "'a cset \<rightarrow> 'a cset \<rightarrow> 'a cset" where
"cunion = (\<Lambda> p q. CCollect (\<Lambda> x. (x \<in>\<in> p) \<or>\<or> (x \<in>\<in> q)))"

abbreviation cunion_syn :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> 'a cset" (infixl "\<union>\<union>" 60) where
"x \<union>\<union> y \<equiv> cunion\<cdot>x\<cdot>y"



text {* For the time being, set injenction is converted to sets of flat values.
        This may be too restrictive, but if a larger set than flat can be found
        which preserver continuity then this can be inserted *}

definition set2cset_aux :: "('a::pcpo) set \<Rightarrow> 'a \<Rightarrow> tr" where
"set2cset_aux xs = (\<lambda> x. if (x \<in> flat) then (if (x \<in> xs) then TT else FF) else \<bottom>)"

lemma cont_set2cset_aux [cont2cont, simp]: 
  "cont (set2cset_aux xs)"
  apply (rule cont_flat_cdom)
  apply (simp add:cdom_def set2cset_aux_def)
done  

definition set2cset :: "('a::pcpo) set \<Rightarrow> 'a cset" where
"set2cset xs = cset_abs\<cdot>(\<Lambda> x. set2cset_aux xs x)"
 
definition cset2set :: "('a::pcpo) cset \<Rightarrow> 'a set" where
"cset2set xs = {x. \<lbrakk> x \<in>\<in> xs \<rbrakk>st}"

lemma set2cset_inv[simp]: "xs \<subseteq> flat \<Longrightarrow> cset2set (set2cset xs) = xs"
  apply (simp add:cset2set_def set2cset_def cmember_def)
  apply (simp add:set_eq_iff)
  apply (clarify)
  apply (case_tac "x = \<bottom>")
  apply (simp add:flat_def)
  apply (metis (lifting) Cfun_Partial.flat_def flat_nbot set_rev_mp)
  apply (simp)
  apply (simp add:flat_def set2cset_aux_def)
  apply (auto)
done

lemma set2cset_mem[simp]: "xs \<subseteq> flat \<Longrightarrow> \<lbrakk>x \<in>\<in> set2cset xs\<rbrakk>st \<longleftrightarrow> x \<in> xs"
  apply (simp add:set2cset_def)
  apply (case_tac "x = \<bottom>")
  apply (simp add:flat_def)
  apply (metis (lifting) Cfun_Partial.flat_def flat_nbot set_rev_mp)
  apply (auto simp add:set2cset_aux_def)
done

lemma set2cset_nbot[simp]: 
  "\<lbrakk> (xs::('a::pcpo) set) \<subseteq> flat; \<exists> (x::'a). x \<in> flat \<rbrakk> \<Longrightarrow> set2cset xs \<noteq> \<bottom>"
  apply (auto simp add:set2cset_def)
  apply (drule_tac f="cset_rep" in cfun_arg_cong)
  apply (simp)
  apply (case_tac "\<exists>y . y \<in> xs")
  apply (erule exE)
  apply (drule_tac x="y" in cfun_fun_cong)
  apply (simp)
  apply (case_tac "y=\<bottom>")
  apply (force simp add:flat_def flat_value_def)
  apply (simp add:set2cset_aux_def)
  apply (auto)
  apply (drule_tac x="x" in cfun_fun_cong)
  apply (simp)
  apply (case_tac "x=\<bottom>")
  apply (simp_all add:set2cset_aux_def)
done

definition flat_cset :: "'a cset \<Rightarrow> bool" where
"flat_cset xs = (\<forall>x. (x \<in>\<in> xs) \<noteq> \<bottom> \<longleftrightarrow> flat_value x)"

lemma cset2set_inv[simp]: 
  "flat_cset xs \<Longrightarrow> set2cset (cset2set xs) = xs"
  apply (simp add: cset_mem_iff)
  apply (auto simp add:cset2set_def set2cset_def staut_def)
  apply (case_tac "x=\<bottom>")
  apply (simp)
  apply (metis (no_types) cmember_def cset_rep_strict')
  apply (simp)
  apply (simp add:set2cset_aux_def flat_cset_def)
  apply (auto)
  apply (force simp add:flat_def)
  apply (metis Cfun_Partial.flat_def Exh_tr mem_Collect_eq)
  apply (metis (lifting) Cfun_Partial.flat_def mem_Collect_eq)
done

(*

(*
definition fdom :: "('a::pcpo \<rightarrow> 'b::pcpo) \<rightarrow> 'a cset" where
"fdom = (\<Lambda> f. CCollectF (\<lambda> x. if (f\<cdot>x = \<bottom>) then FF else TT))"

lemma "cont (\<lambda> f. CCollectF (\<lambda> x. if (f\<cdot>x = \<bottom>) then FF else TT))"
  apply (rule cont2cont)
oops
*)

(*
definition fran :: "('a::pcpo \<rightarrow> 'b::pcpo) \<rightarrow> 'b cset" where
"fran = (\<Lambda> f. CCollectF (\<lambda> f x. if (f\<cdot>x = \<bottom>) then FF else TT))"
*)




subsection {* Strict Lists to sets *}

fixrec slist2cset :: "('a::domain) slist \<rightarrow> 'a cset" where
"slist2cset\<cdot>SNil = \<emptyset>" |
"\<lbrakk>x\<noteq>\<bottom>;xs\<noteq>\<bottom>\<rbrakk> \<Longrightarrow> slist2cset\<cdot>(SCons\<cdot>x\<cdot>xs) = cinsert\<cdot>x\<cdot>(slist2cset\<cdot>xs)"
*)

(*
lemma "\<lbrakk>x \<noteq> \<bottom>;xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> \<lbrakk>x \<in>\<in> slist2cset\<cdot>(SCons\<cdot>x\<cdot>xs)\<rbrakk>st"
  apply (simp)
*)

(*
lemma cunion_thms:
  "\<bottom> \<union>\<union> y = \<bottom>"
  "x \<union>\<union> \<bottom> = \<bottom>"
  "x \<union>\<union> (y \<union>\<union> z) = (x \<union>\<union> y) \<union>\<union> z"
  "x \<union>\<union> y = y \<union>\<union> x"
  "x \<union>\<union> x = x"
  "x \<union>\<union> \<emptyset> = x"
  apply (simp add:cunion_def cont2cont_LAM)
  apply (simp add:cunion_def cont2cont_LAM)
  apply (simp add:cunion_def cont2cont_LAM)
  apply (simp add:strictify_cancel)
  apply (simp add:vor_assoc)
  apply (simp add:vor_comm)
  done

lemma cont_cunion [simp,cont2cont]: 
  "cont (op \<union>\<union>)" "cont (\<lambda> x. x \<union>\<union> y)" "cont (\<lambda> y. x \<union>\<union> y)"
  by (simp_all)

lemma cunion_mem [intro]: "\<lbrakk>x \<in>\<in> xs\<rbrakk>wt \<Longrightarrow> \<lbrakk>x \<in>\<in> (xs \<union>\<union> ys)\<rbrakk>wt"
  by (simp add:cunion_def cont2cont_LAM)

definition cinter :: "'a cset \<rightarrow> 'a cset \<rightarrow> 'a cset" where
"cinter = (\<Lambda> p q. CCollect (\<Lambda> x. (x \<in>\<in> p) \<and>\<and> (x \<in>\<in> q)))"

abbreviation cinter_syn :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> 'a cset" (infixl "\<inter>\<inter>" 55) where
"x \<inter>\<inter> y \<equiv> cinter\<cdot>x\<cdot>y"

lemma cinter_thms:
  "\<bottom> \<inter>\<inter> y = \<bottom>"
  "x \<inter>\<inter> \<bottom> = \<bottom>"
  "x \<inter>\<inter> (y \<inter>\<inter> z) = (x \<inter>\<inter> y) \<inter>\<inter> z"
  "x \<inter>\<inter> y = y \<inter>\<inter> x"
  "x \<inter>\<inter> x = x"
  "x \<inter>\<inter> cuniv = x"
  apply (simp_all add:cinter_def cont2cont_LAM)
  apply (simp add:vand_assoc)
  apply (simp add:vand_comm)
done

lemma cont_cinter [simp,cont2cont]: 
  "cont (op \<inter>\<inter>)" "cont (\<lambda> x. x \<inter>\<inter> y)" "cont (\<lambda> y. x \<inter>\<inter> y)"
  by (simp_all)

subsection {* Weak and strong sets *}

definition wset :: "'a cset \<Rightarrow> 'a set" where
"wset xs = {x. \<lbrakk>x \<in>\<in> xs\<rbrakk>wt}"

definition sset :: "'a cset \<Rightarrow> 'a set" where
"sset xs = {x. \<lbrakk>x \<in>\<in> xs\<rbrakk>st}"

lemma sset_in_wset: "sset xs \<subseteq> wset xs"
  by (auto simp add:wset_def sset_def wtaut_def)

lemma cmem_sset: "\<lbrakk>x\<in>\<in>xs\<rbrakk>st \<longleftrightarrow> x\<in>sset xs"
  by (simp add:sset_def)

lemma cmem_wset: "\<lbrakk>x\<in>\<in>xs\<rbrakk>wt \<longleftrightarrow> x\<in>wset xs"
  by (simp add:wset_def)

(* These definitions only allows construction of sets of flat values *)
definition csingle :: "('a::pcpo) \<Rightarrow> 'a cset" where
"csingle = (\<lambda> x. if (x \<in> flat) then CCollectF (\<lambda> y. if (x = y) then TT else FF) else \<bottom>)"

definition cinsert :: "('a::pcpo) \<rightarrow> 'a cset \<rightarrow> 'a cset" where
"cinsert = (\<Lambda> x xs. (csingle x) \<union>\<union> xs)"

lemma csingle_nflat[simp]: "x \<notin> flat \<Longrightarrow> csingle x = \<bottom>"
  by (simp add:csingle_def CCollectF_def)

lemma cdom_csingle: "cdom csingle = flat"
  apply (auto simp add: cdom_def)
  apply (simp_all add:csingle_def CCollectF_def)
  apply (case_tac "x \<in> flat")
  apply (simp_all)
  apply (drule_tac f="cset_rep" in cfun_arg_cong)
  apply (simp)
  apply (drule_tac x="x" in cfun_fun_cong)
  apply (simp)
done
  
lemma cont_csingle[simp,cont2cont]: "cont csingle"
  by (simp add:cdom_csingle cont_flat_cdom)

lemma csingle_mem [simp]: "x \<in> flat \<Longrightarrow> \<lbrakk>x \<in>\<in> csingle x\<rbrakk>wt"
  by (simp add:csingle_def)

lemma cinsert_mem: "x \<in> flat \<Longrightarrow> \<lbrakk>x \<in>\<in> cinsert\<cdot>x\<cdot>xs\<rbrakk>wt"
  by (auto simp add:cinsert_def cont2cont_LAM)

text {* To make this work we need a notion of typing. It must be the case that xs is a subset of
   a downward closed set t (i.e. a type). The membership check then returns TT if x in xs AND x is in t,
   FF if x is only in t and \<bottom> otherwise *}
*)


default_sort cpo

end
