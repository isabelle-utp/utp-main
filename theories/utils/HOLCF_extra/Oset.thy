theory Oset
imports HOLCF Boolu Cfun_Partial
begin

default_sort cpo

pcpodef (open) 'a oset = "UNIV :: ('a \<rightarrow> bool\<^sub>\<bottom>) set"
  by simp_all

definition
  oset_abs :: "('a \<rightarrow> bool\<^sub>\<bottom>) \<rightarrow> ('a oset)"
where
  "oset_abs = (\<Lambda> f. Abs_oset f)"

definition
  oset_rep :: "('a oset) \<rightarrow> ('a \<rightarrow> bool\<^sub>\<bottom>)"
where
  "oset_rep = (\<Lambda> xs. Rep_oset xs)"

definition OCollect :: "('a \<rightarrow> bool\<^sub>\<bottom>) \<Rightarrow> 'a oset" where
"OCollect = (\<lambda> f. oset_abs\<cdot>f)"

text {* Set collect for flat values only, guaranteed continuity *}
definition OCollectF :: "(('a::pcpo) \<Rightarrow> bool\<^sub>\<bottom>) \<Rightarrow> 'a oset" where
"OCollectF \<equiv> \<lambda> f. oset_abs\<cdot>(\<Lambda> x. if (x \<in> flat) then f x else \<bottom>)"

definition omember :: "'a \<Rightarrow> 'a oset \<Rightarrow> bool\<^sub>\<bottom>" where
"omember x P = (oset_rep\<cdot>P)\<cdot>x"

notation (xsymbols)
  omember    ("op \<in>\<in>") and
  omember    ("(_/ \<in>\<in> _)" [50, 51] 50)

lemma oset_rep_beta: "oset_rep\<cdot>f = Rep_oset f"
  unfolding oset_rep_def by (simp add: cont_Rep_oset)

lemma oset_abs_oset_rep [simp]: "oset_abs\<cdot>(oset_rep\<cdot>f) = f"
  unfolding oset_abs_def oset_rep_def
  by (simp add: cont_Abs_oset cont_Rep_oset Rep_oset_inverse)

lemma oset_rep_oset_abs [simp]: "oset_rep\<cdot>(oset_abs\<cdot>f) = f"
  unfolding oset_abs_def oset_rep_def
  by (simp add: cont_Abs_oset cont_Rep_oset Abs_oset_inverse)

lemma oset_rep_strict [simp]: "oset_rep\<cdot>\<bottom> = \<bottom>"
  unfolding oset_rep_beta by (rule Rep_oset_strict)

lemma oset_abs_mem_beta [simp]: "(x \<in>\<in> oset_abs\<cdot>f) = f\<cdot>x"
  by (simp add:omember_def)

lemma oset_abs_strict [simp]: "oset_abs\<cdot>\<bottom> = \<bottom>"
  by (metis (lifting) oset_abs_oset_rep oset_rep_strict)

lemma oset_eq_iff: "xs = ys \<longleftrightarrow> oset_rep\<cdot>xs = oset_rep\<cdot>ys"
  by (simp add: oset_rep_def cont_Rep_oset Rep_oset_inject)

lemma oset_below_iff: "xs \<sqsubseteq> ys \<longleftrightarrow> oset_rep\<cdot>xs \<sqsubseteq> oset_rep\<cdot>ys"
  by (simp add: oset_rep_def cont_Rep_oset below_oset_def)

lemma omem_OCollect_eq [iff]: "omember a (OCollect P) = P\<cdot>a"
  by (simp add:omember_def OCollect_def Abs_oset_inverse)

lemma CCollect_cmem_eq [simp]: "OCollect (\<Lambda> x. omember x A) = A"
  by (simp add: OCollect_def omember_def Rep_cfun_inverse Rep_oset_inverse)

text {* Continuity of membership and collect *}

lemma cont_OCollect [simp,cont2cont]: "cont f \<Longrightarrow> cont (\<lambda>x . OCollect (f x))"
  by (simp add:OCollect_def cont_Abs_oset)

lemma cont_flat_func [simp, cont2cont]: "cont (\<lambda> x. if (x \<in> flat) then f x else \<bottom>)"
  by (rule cont_flat_cdom, auto simp add:cdom_def)

lemma cont_OCollectF [simp,cont2cont]: "cont f \<Longrightarrow> cont (\<lambda>x . OCollectF (f x))"
  apply (auto simp add:OCollectF_def)
  apply (rule cont2cont, simp)
  apply (rule cont2cont_LAM)
  apply (rule cont2cont)
  apply (rule cont2cont)
  apply (rule cont2cont_fun)
  apply (simp_all)
done

lemma cont_omember1 [simp,cont2cont]: "cont f \<Longrightarrow> cont (\<lambda> x. f x \<in>\<in> xs)"
  by (simp add:omember_def cont_Rep_oset)

lemma cont_omember2 [simp,cont2cont]: "cont f \<Longrightarrow> cont (\<lambda> xs. x \<in>\<in> f xs)"
  by (simp add:omember_def cont_Rep_oset)

lemma cont_Rep_oset1: "cont (\<lambda>x. x \<in>\<in> xs)"
  by simp

lemma cont_Rep_oset2: "cont (\<lambda>xs. x \<in>\<in> xs)"
  by simp

lemmas monofun_Rep_oset = cont_Rep_oset [THEN cont2mono]

lemmas monofun_Rep_oset1 = cont_Rep_oset1 [THEN cont2mono]
lemmas monofun_Rep_oset2 = cont_Rep_oset2 [THEN cont2mono]

lemma OCollectF_mem [simp]: "x \<in> flat \<Longrightarrow> x \<in>\<in> OCollectF f = f x"
  by (simp add:omember_def OCollectF_def)

text {* Extensionality for continuous sets *}

lemma oset_mem_iff: "xs = ys \<longleftrightarrow> (\<forall>x. (x \<in>\<in> xs) = (x \<in>\<in> ys))"
  by (auto simp add:omember_def Rep_oset_inject [symmetric] cfun_eq_iff oset_rep_beta)

lemma oset_eqI: "(\<And>x. (x \<in>\<in> xs) = (x \<in>\<in> ys)) \<Longrightarrow> xs = ys"
  by (simp add: oset_mem_iff)

text {* Extensionality wrt. ordering for continuous sets *}

lemma oset_mem_below_iff: "xs \<sqsubseteq> ys \<longleftrightarrow> (\<forall>x. (x \<in>\<in> xs) \<sqsubseteq> (x \<in>\<in> ys))" 
  by (auto simp add: below_oset_def cfun_below_iff omember_def oset_rep_beta)

lemma oset_belowI: "(\<And>x. (x \<in>\<in> xs) \<sqsubseteq> (x \<in>\<in> ys)) \<Longrightarrow> xs \<sqsubseteq> ys"
  by (simp add: oset_mem_below_iff)

text {* monotonicity of membership *}

lemma monofun_oset_set: "xs \<sqsubseteq> ys \<Longrightarrow> (x \<in>\<in> xs) \<sqsubseteq> (x \<in>\<in> ys)"
  by (simp add: oset_mem_below_iff)

lemma monofun_oset_mem: "x \<sqsubseteq> y \<Longrightarrow> (x \<in>\<in> xs) \<sqsubseteq> (y \<in>\<in> xs)"
  by (rule monofun_Rep_oset1 [THEN monofunE], simp)

lemma monofun_cfun: "\<lbrakk>xs \<sqsubseteq> ys; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> (x \<in>\<in> xs) \<sqsubseteq> (y \<in>\<in> ys)"
  by (rule below_trans [OF monofun_oset_set monofun_oset_mem])

text {* Set Mapping Function *}

definition oset_map :: "('b \<rightarrow> 'a) \<rightarrow> ('a oset) \<rightarrow> ('b oset)" where
"oset_map = (\<Lambda> f. oset_abs oo cfun_map\<cdot>f\<cdot>ID oo oset_rep)"

lemma oset_map_beta [simp]: "(x \<in>\<in> oset_map\<cdot>f\<cdot>xs) = (f\<cdot>x \<in>\<in> xs)"
  by (simp add:oset_map_def cfun_map_def cont2cont_LAM cfun_eq_iff omember_def)

lemma oset_map_ID [domain_map_ID]: "oset_map\<cdot>ID = ID"
  unfolding cfun_eq_iff oset_mem_iff by simp

lemma oset_map_map:
  "oset_map\<cdot>f1\<cdot>(oset_map\<cdot>f2\<cdot>p) =
    oset_map\<cdot>(\<Lambda> x. f2\<cdot>(f1\<cdot>x))\<cdot>p"
  by (rule oset_eqI) simp

lemma ep_pair_oset_map:
  assumes "ep_pair e p"
  shows "ep_pair (oset_map\<cdot>p) (oset_map\<cdot>e)"
proof
  interpret e1p1: ep_pair e p by fact
  fix x show "oset_map\<cdot>e\<cdot>(oset_map\<cdot>p\<cdot>x) = x"
    by (simp add:oset_mem_iff)

  fix x show "oset_map\<cdot>p\<cdot>(oset_map\<cdot>e\<cdot>x) \<sqsubseteq> x"
    apply (rule oset_belowI, simp)
    apply (rule monofun_oset_mem)
    apply (rule e1p1.e_p_below)
  done
qed

lemma deflation_oset_map [domain_deflation]:
  assumes 1: "deflation d"
  shows "deflation (oset_map\<cdot>d)"
apply (rule deflation.intro)
apply (rule oset_eqI)
apply (simp add: "1" deflation.idem)
apply (metis "1" ID1 oset_map_ID deflation.below_ID monofun_cfun_arg monofun_cfun_fun)
done

lemma Collect_eq_iff: "x = y \<longleftrightarrow> OCollect x = OCollect y"
  by (metis cfun_eq_iff omem_OCollect_eq)

lemma sort_finite_deflation: "deflation (d:: ('a::{cpo,finite}) \<rightarrow> 'a) \<Longrightarrow> finite_deflation d"
   by (rule finite_deflation_intro, simp_all add:finite)

lemma UNIV_boolu: "(UNIV :: (bool\<^sub>\<bottom>) set) = {\<bottom>,tt,ff}"
  by (auto, case_tac x rule:booluE, simp_all)

lemma finite_boolu: "finite (UNIV :: (bool\<^sub>\<bottom>) set)"
  by (simp add:UNIV_boolu)

lemma finite_deflation_oset_map:
  assumes 1: "finite_deflation d"
  shows "finite_deflation (oset_map\<cdot>d)"
proof (intro finite_deflation_intro)
  interpret d1: finite_deflation d by fact
  have "deflation d" by fact
  thus "deflation (oset_map\<cdot>d)" by (rule deflation_oset_map)

  have findef_ID: "finite_deflation (ID :: bool\<^sub>\<bottom> \<rightarrow> bool\<^sub>\<bottom>)"
    apply (rule finite_deflation_intro)
    apply (simp add:deflation_ID)
    apply (metis finite_imageI finite_range_imp_finite_fixes finite_boolu)
  done
   
  from 1 findef_ID have "finite_deflation (cfun_map\<cdot>d\<cdot>(ID :: bool\<^sub>\<bottom> \<rightarrow> bool\<^sub>\<bottom>))"
    by (rule finite_deflation_cfun_map)

  then have "finite {f. cfun_map\<cdot>d\<cdot>(ID :: bool\<^sub>\<bottom> \<rightarrow> bool\<^sub>\<bottom>)\<cdot>f = f}"
    by (rule finite_deflation.finite_fixes)

  moreover have "inj (\<lambda>f. oset_rep\<cdot>f)"
    by (rule inj_onI, simp add:oset_eq_iff)
  ultimately have "finite ((\<lambda>xs. oset_rep\<cdot>xs) -` {f. cfun_map\<cdot>d\<cdot>ID\<cdot>f = f})"
    by (rule finite_vimageI)
  then show "finite {f. oset_map\<cdot>d\<cdot>f = f}"
    unfolding oset_map_def oset_eq_iff
    by (simp)
qed

lemma approx_chain_oset_map:
  assumes "approx_chain a"
  shows "approx_chain (\<lambda>i. oset_map\<cdot>(a i))"
  using assms unfolding approx_chain_def
  by (simp add: lub_APP oset_map_ID finite_deflation_oset_map)


instance oset :: (bifinite) bifinite
proof
  show "\<exists>(a::nat \<Rightarrow> ('a oset) \<rightarrow> ('a oset)). approx_chain a"
    using bifinite [where 'a='a]
    by (fast intro!: approx_chain_oset_map)
qed

definition "oset_emb = udom_emb (\<lambda>i. oset_map\<cdot>(udom_approx i))"
definition "oset_prj = udom_prj (\<lambda>i. oset_map\<cdot>(udom_approx i))"

lemma ep_pair_oset: "ep_pair oset_emb oset_prj"
  unfolding oset_emb_def oset_prj_def
  by (simp add: ep_pair_udom approx_chain_oset_map)

definition oset_defl :: "udom defl \<rightarrow> udom defl"
  where "oset_defl = defl_fun1 oset_emb oset_prj oset_map"

lemma cast_oset_defl:
  "cast\<cdot>(oset_defl\<cdot>A) =
    oset_emb oo oset_map\<cdot>(cast\<cdot>A) oo oset_prj"
using ep_pair_oset finite_deflation_oset_map
unfolding oset_defl_def by (rule cast_defl_fun1)

instantiation oset :: ("domain") "domain"
begin

definition
  "emb = oset_emb oo oset_map\<cdot>prj"

definition
  "prj = oset_map\<cdot>emb oo oset_prj"

definition
  "defl (t::('a oset) itself) = oset_defl\<cdot>DEFL('a)"

definition
  "(liftemb :: ('a oset) u \<rightarrow> udom u) = u_map\<cdot>emb"

definition
  "(liftprj :: udom u \<rightarrow> ('a oset) u) = u_map\<cdot>prj"

definition
  "liftdefl (t::('a oset) itself) = liftdefl_of\<cdot>DEFL('a oset)"

instance proof
  show "ep_pair emb (prj :: udom \<rightarrow> 'a oset)"
    unfolding emb_oset_def prj_oset_def
    by (intro ep_pair_comp ep_pair_oset ep_pair_oset_map ep_pair_emb_prj)
  show "cast\<cdot>DEFL('a oset) = emb oo (prj :: udom \<rightarrow> 'a oset)"
    unfolding emb_oset_def prj_oset_def defl_oset_def cast_oset_defl
    by (simp add: cast_DEFL oo_def oset_eq_iff oset_map_map)
qed (fact liftemb_oset_def liftprj_oset_def liftdefl_oset_def)+

end

lemma DEFL_oset [domain_defl_simps]:
  "DEFL('a::domain oset) = oset_defl\<cdot>DEFL('a)"
by (rule defl_oset_def)

lemma isodefl_oset [domain_isodefl]:
  "isodefl d t \<Longrightarrow>
    isodefl (oset_map\<cdot>d) (oset_defl\<cdot>t)"
apply (rule isodeflI)
apply (simp add: cast_oset_defl cast_isodefl)
apply (simp add: emb_oset_def prj_oset_def)
apply (simp add: oset_map_map isodefl_strict)
done

setup {*
  fold Domain_Take_Proofs.add_rec_type
    [(@{type_name oset}, [true])]
*}


definition fdom :: "('a::pcpo \<rightarrow> 'b::pcpo) \<rightarrow> 'a oset" where
"fdom = (\<Lambda> f. OCollectF (\<lambda> x. if (f\<cdot>x = \<bottom>) then ff else tt))"

lemma cont_if[cont2cont,simp]: "cont f \<Longrightarrow> cont (\<lambda> x. if (f x = \<bottom>) then ff else tt)"
  apply (rule contI)
  apply (rule is_lubI)
  apply (rule is_ubI)
  apply (smt ch2ch_cont cont2contlubE ff_below_tt lub_eq_bottom_iff po_eq_conv rangeE)
  apply (smt Boolu.dist_eq_tr(4) ch2ch_cont cont2contlubE cont2monofunE cont_id lub_eq_bottom_iff ub_rangeD)
done

end
