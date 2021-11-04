(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>Hom\<close>-functor\<close>
theory CZH_ECAT_Hom
  imports 
    CZH_ECAT_Set
    CZH_ECAT_PCategory
begin



subsection\<open>\<open>hom\<close>-function\<close>


text\<open>
The \<open>hom\<close>-function is a part of the definition of the \<open>Hom\<close>-functor,
as presented in \cite{noauthor_nlab_nodate}\footnote{\url{
https://ncatlab.org/nlab/show/hom-functor
}}.
\<close>

definition cf_hom :: "V \<Rightarrow> V \<Rightarrow> V"
  where "cf_hom \<CC> f =
    [
      (
        \<lambda>q\<in>\<^sub>\<circ>Hom \<CC> (\<CC>\<lparr>Cod\<rparr>\<lparr>vpfst f\<rparr>) (\<CC>\<lparr>Dom\<rparr>\<lparr>vpsnd f\<rparr>).
          vpsnd f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> q \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> vpfst f
      ),
      Hom \<CC> (\<CC>\<lparr>Cod\<rparr>\<lparr>vpfst f\<rparr>) (\<CC>\<lparr>Dom\<rparr>\<lparr>vpsnd f\<rparr>),
      Hom \<CC> (\<CC>\<lparr>Dom\<rparr>\<lparr>vpfst f\<rparr>) (\<CC>\<lparr>Cod\<rparr>\<lparr>vpsnd f\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_hom_components:
  shows "cf_hom \<CC> f\<lparr>ArrVal\<rparr> = 
      (
        \<lambda>q\<in>\<^sub>\<circ>Hom \<CC> (\<CC>\<lparr>Cod\<rparr>\<lparr>vpfst f\<rparr>) (\<CC>\<lparr>Dom\<rparr>\<lparr>vpsnd f\<rparr>). 
          vpsnd f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> q \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> vpfst f
      )"
    and "cf_hom \<CC> f\<lparr>ArrDom\<rparr> = Hom \<CC> (\<CC>\<lparr>Cod\<rparr>\<lparr>vpfst f\<rparr>) (\<CC>\<lparr>Dom\<rparr>\<lparr>vpsnd f\<rparr>)"
    and "cf_hom \<CC> f\<lparr>ArrCod\<rparr> = Hom \<CC> (\<CC>\<lparr>Dom\<rparr>\<lparr>vpfst f\<rparr>) (\<CC>\<lparr>Cod\<rparr>\<lparr>vpsnd f\<rparr>)"
  unfolding cf_hom_def arr_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Arrow value\<close>

mk_VLambda cf_hom_components(1)
  |vsv cf_hom_ArrVal_vsv[cat_cs_intros]|

lemma cf_hom_ArrVal_vdomain[cat_cs_simps]:
  assumes "g : a \<mapsto>\<^bsub>op_cat \<CC>\<^esub> b" and "f : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'"
  shows "\<D>\<^sub>\<circ> (cf_hom \<CC> [g, f]\<^sub>\<circ>\<lparr>ArrVal\<rparr>) = Hom \<CC> a a'"
  using assms 
  unfolding cf_hom_components
  by (simp_all add: nat_omega_simps cat_op_simps cat_cs_simps)

lemma cf_hom_ArrVal_app[cat_cs_simps]:
  assumes "g : c \<mapsto>\<^bsub>op_cat \<CC>\<^esub> d" and "q : c \<mapsto>\<^bsub>\<CC>\<^esub> c'" and "f : c' \<mapsto>\<^bsub>\<CC>\<^esub> d'"
  shows "cf_hom \<CC> [g, f]\<^sub>\<circ>\<lparr>ArrVal\<rparr>\<lparr>q\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> q \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g"
  using assms 
  unfolding cf_hom_components
  by (simp_all add: nat_omega_simps cat_op_simps cat_cs_simps)

lemma (in category) cf_hom_ArrVal_vrange:
  assumes "g : a \<mapsto>\<^bsub>op_cat \<CC>\<^esub> b" and "f : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'"
  shows "\<R>\<^sub>\<circ> (cf_hom \<CC> [g, f]\<^sub>\<circ>\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> Hom \<CC> b b'"
proof(intro vsubsetI)
  interpret gf: vsv \<open>cf_hom \<CC> [g, f]\<^sub>\<circ>\<lparr>ArrVal\<rparr>\<close> 
    unfolding cf_hom_components by auto
  fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (cf_hom \<CC> [g, f]\<^sub>\<circ>\<lparr>ArrVal\<rparr>)"
  then obtain q where y_def: "y = cf_hom \<CC> [g, f]\<^sub>\<circ>\<lparr>ArrVal\<rparr>\<lparr>q\<rparr>"
    and "q \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cf_hom \<CC> [g, f]\<^sub>\<circ>\<lparr>ArrVal\<rparr>)"
    by (metis gf.vrange_atD)
  then have q: "q : a \<mapsto>\<^bsub>\<CC>\<^esub> a'" 
    unfolding cf_hom_ArrVal_vdomain[OF assms] by simp
  from assms q show "y \<in>\<^sub>\<circ> Hom \<CC> b b'"
    unfolding y_def cf_hom_ArrVal_app[OF assms(1) q assms(2)] cat_op_simps 
    by (auto intro: cat_cs_intros)
qed


subsubsection\<open>Arrow domain\<close>

lemma (in category) cf_hom_ArrDom:
  assumes "gf : [c, c']\<^sub>\<circ> \<mapsto>\<^bsub>op_cat \<CC> \<times>\<^sub>C \<CC>\<^esub> dd'"
  shows "cf_hom \<CC> gf\<lparr>ArrDom\<rparr> = Hom \<CC> c c'"
proof-
  from assms obtain g f d d' 
    where "gf = [g, f]\<^sub>\<circ>" and "g : c \<mapsto>\<^bsub>op_cat \<CC>\<^esub> d" and "f : c' \<mapsto>\<^bsub>\<CC>\<^esub> d'"
    unfolding cf_hom_components 
    by (elim cat_prod_2_is_arrE[rotated 2]) (auto intro: cat_cs_intros)
  then show ?thesis
    unfolding cf_hom_components 
    by (simp_all add: nat_omega_simps cat_op_simps cat_cs_simps)
qed

lemmas [cat_cs_simps] = category.cf_hom_ArrDom


subsubsection\<open>Arrow codomain\<close>

lemma (in category) cf_hom_ArrCod:
  assumes "gf : cc' \<mapsto>\<^bsub>op_cat \<CC> \<times>\<^sub>C \<CC>\<^esub> [d, d']\<^sub>\<circ>"
  shows "cf_hom \<CC> gf\<lparr>ArrCod\<rparr> = Hom \<CC> d d'"
proof-
  from assms obtain g f c c' 
    where "gf = [g, f]\<^sub>\<circ>" and "g : c \<mapsto>\<^bsub>op_cat \<CC>\<^esub> d" and "f : c' \<mapsto>\<^bsub>\<CC>\<^esub> d'"
    unfolding cf_hom_components 
    by (elim cat_prod_2_is_arrE[rotated 2]) (auto intro: cat_cs_intros)
  then show ?thesis
    unfolding cf_hom_components 
    by (simp_all add: nat_omega_simps cat_op_simps cat_cs_simps)
qed

lemmas [cat_cs_simps] = category.cf_hom_ArrCod


subsubsection\<open>\<open>hom\<close>-function is an arrow in the category \<open>Set\<close>\<close>

lemma (in category) cat_cf_hom_ArrRel:
  assumes "gf : cc' \<mapsto>\<^bsub>op_cat \<CC> \<times>\<^sub>C \<CC>\<^esub> dd'"
  shows "arr_Set \<alpha> (cf_hom \<CC> gf)"
proof(intro arr_SetI)
  from assms obtain g f c c' d d'
    where gf_def: "gf = [g, f]\<^sub>\<circ>"
      and cc'_def: "cc' = [c, c']\<^sub>\<circ>"
      and dd'_def: "dd' = [d, d']\<^sub>\<circ>"
      and op_g: "g : c \<mapsto>\<^bsub>op_cat \<CC>\<^esub> d" 
      and f: "f : c' \<mapsto>\<^bsub>\<CC>\<^esub> d'"
    unfolding cf_hom_components 
    by (elim cat_prod_2_is_arrE[rotated 2]) (auto intro: cat_cs_intros)
  from op_g have g: "g : d \<mapsto>\<^bsub>\<CC>\<^esub> c" unfolding cat_op_simps by simp
  then have [simp]: "\<CC>\<lparr>Dom\<rparr>\<lparr>g\<rparr> = d" "\<CC>\<lparr>Cod\<rparr>\<lparr>g\<rparr> = c" 
    and d: "d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by auto
  from f have [simp]: "\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = c'" "\<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = d'" 
    and c': "c' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and d': "d' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by auto
  show "vfsequence (cf_hom \<CC> gf)" unfolding cf_hom_def by simp
  show vsv_hom_fg: "vsv (cf_hom \<CC> gf\<lparr>ArrVal\<rparr>)"
    unfolding cf_hom_components by auto
  show "vcard (cf_hom \<CC> gf) = 3\<^sub>\<nat>"
    unfolding cf_hom_def by (simp add: nat_omega_simps)
  show [simp]: "\<D>\<^sub>\<circ> (cf_hom \<CC> gf\<lparr>ArrVal\<rparr>) = cf_hom \<CC> gf\<lparr>ArrDom\<rparr>"
    unfolding cf_hom_components by auto
  show "\<R>\<^sub>\<circ> (cf_hom \<CC> gf\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> cf_hom \<CC> gf\<lparr>ArrCod\<rparr>"
  proof(rule vsubsetI)
    interpret hom_fg: vsv \<open>cf_hom \<CC> gf\<lparr>ArrVal\<rparr>\<close> by (simp add: vsv_hom_fg)
    fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (cf_hom \<CC> gf\<lparr>ArrVal\<rparr>)"
    then obtain q where y_def: "y = cf_hom \<CC> gf\<lparr>ArrVal\<rparr>\<lparr>q\<rparr>" 
      and q: "q \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cf_hom \<CC> gf\<lparr>ArrVal\<rparr>)"
      by (blast dest: hom_fg.vrange_atD)
    from q have q: "q : c \<mapsto>\<^bsub>\<CC>\<^esub> c'" 
      by (simp add: cf_hom_ArrDom[OF assms[unfolded cc'_def]])
    with g f have "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> q \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g : d \<mapsto>\<^bsub>\<CC>\<^esub> d'" 
      by (auto intro: cat_cs_intros)
    then show "y \<in>\<^sub>\<circ> cf_hom \<CC> gf\<lparr>ArrCod\<rparr>"  
      unfolding cf_hom_ArrCod[OF assms[unfolded dd'_def]]
      unfolding y_def gf_def cf_hom_ArrVal_app[OF op_g q f] 
      by auto
  qed
  from c c' show "cf_hom \<CC> gf\<lparr>ArrDom\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding cf_hom_components gf_def
    by (auto simp: nat_omega_simps intro: cat_cs_intros)
  from d d' show "cf_hom \<CC> gf\<lparr>ArrCod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding cf_hom_components gf_def
    by (auto simp: nat_omega_simps intro: cat_cs_intros)
qed auto

lemmas [cat_cs_intros] = category.cat_cf_hom_ArrRel

lemma (in category) cat_cf_hom_cat_Set_is_arr:
  assumes "gf : [a, b]\<^sub>\<circ> \<mapsto>\<^bsub>op_cat \<CC> \<times>\<^sub>C \<CC>\<^esub> [c, d]\<^sub>\<circ>"
  shows "cf_hom \<CC> gf : Hom \<CC> a b \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> c d"
proof(intro is_arrI)
  from assms cat_cf_hom_ArrRel show "cf_hom \<CC> gf \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Arr\<rparr>"
    unfolding cat_Set_components by auto
  with assms show 
    "cat_Set \<alpha>\<lparr>Dom\<rparr>\<lparr>cf_hom \<CC> gf\<rparr> = Hom \<CC> a b"
    "cat_Set \<alpha>\<lparr>Cod\<rparr>\<lparr>cf_hom \<CC> gf\<rparr> = Hom \<CC> c d"
    unfolding cat_Set_components
    by (simp_all add: cf_hom_ArrDom[OF assms] cf_hom_ArrCod[OF assms])
qed

lemma (in category) cat_cf_hom_cat_Set_is_arr':
  assumes "gf : [a, b]\<^sub>\<circ> \<mapsto>\<^bsub>op_cat \<CC> \<times>\<^sub>C \<CC>\<^esub> [c, d]\<^sub>\<circ>"
    and "\<AA>' = Hom \<CC> a b"
    and "\<BB>' = Hom \<CC> c d"
    and "\<CC>' = cat_Set \<alpha>"
  shows "cf_hom \<CC> gf : \<AA>' \<mapsto>\<^bsub>\<CC>'\<^esub> \<BB>'"
  using assms(1) unfolding assms(2-4) by (rule cat_cf_hom_cat_Set_is_arr)

lemmas [cat_cs_intros] = category.cat_cf_hom_cat_Set_is_arr'


subsubsection\<open>Composition\<close>

lemma (in category) cat_cf_hom_Comp: 
  assumes "g : b \<mapsto>\<^bsub>op_cat \<CC>\<^esub> c" 
    and "g' : b' \<mapsto>\<^bsub>\<CC>\<^esub> c'" 
    and "f : a \<mapsto>\<^bsub>op_cat \<CC>\<^esub> b"
    and "f' : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'"
  shows 
    "cf_hom \<CC> [g, g']\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [f, f']\<^sub>\<circ> =
      cf_hom \<CC> [g \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f, g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f']\<^sub>\<circ>"
proof-

  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)

  from assms(1,3) have g: "g : c \<mapsto>\<^bsub>\<CC>\<^esub> b" and f: "f : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
    unfolding cat_op_simps by simp_all

  from assms(2,4) g f Set.category_axioms category_axioms have gg'_ff': 
    "cf_hom \<CC> [g, g']\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [f, f']\<^sub>\<circ> :
      Hom \<CC> a a' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> c c'"
    by (cs_concl cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros)
  then have dom_lhs: 
    "\<D>\<^sub>\<circ> ((cf_hom \<CC> [g, g']\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [f, f']\<^sub>\<circ>)\<lparr>ArrVal\<rparr>) = 
      Hom \<CC> a a'"
    by (cs_concl cs_simp: cat_cs_simps)+
  from assms(2,4) g f Set.category_axioms category_axioms have gf_g'f':
    "cf_hom \<CC> [g \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f, g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f']\<^sub>\<circ> : 
      Hom \<CC> a a' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> c c'"
    by (cs_concl cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros)
  then have dom_rhs: 
    "\<D>\<^sub>\<circ> (cf_hom \<CC> [g \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f, g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f']\<^sub>\<circ>\<lparr>ArrVal\<rparr>) = Hom \<CC> a a'" 
    by (cs_concl cs_simp: cat_cs_simps)

  show ?thesis
  proof(rule arr_Set_eqI[of \<alpha>])
    
    from gg'_ff' show arr_Set_gg'_ff':
      "arr_Set \<alpha> (cf_hom \<CC> [g, g']\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [f, f']\<^sub>\<circ>)"
      by (auto dest: cat_Set_is_arrD(1))
    from gf_g'f' show arr_Set_gf_g'f':
      "arr_Set \<alpha> (cf_hom \<CC> [g \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f, g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f']\<^sub>\<circ>)"
      by (auto dest: cat_Set_is_arrD(1))
  
    show "(cf_hom \<CC> [g, g']\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [f, f']\<^sub>\<circ>)\<lparr>ArrVal\<rparr> = 
      cf_hom \<CC> [g \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f, g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f']\<^sub>\<circ>\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix q assume "q \<in>\<^sub>\<circ> Hom \<CC> a a'"
      then have q: "q : a \<mapsto>\<^bsub>\<CC>\<^esub> a'" by auto
      from category_axioms g f assms(2,4) q Set.category_axioms show 
        "(cf_hom \<CC> [g, g']\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [f, f']\<^sub>\<circ>)\<lparr>ArrVal\<rparr>\<lparr>q\<rparr> = 
          cf_hom \<CC> [g \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f, g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f']\<^sub>\<circ>\<lparr>ArrVal\<rparr>\<lparr>q\<rparr>"
        by 
          (
            cs_concl 
              cs_intro: cat_op_intros cat_cs_intros cat_prod_cs_intros 
              cs_simp: cat_op_simps cat_cs_simps   
         )
    qed (use arr_Set_gg'_ff' arr_Set_gf_g'f' in auto)
  
  qed (use gg'_ff' gf_g'f' in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

qed

lemmas [cat_cs_simps] = category.cat_cf_hom_Comp


subsubsection\<open>Identity\<close>

lemma (in category) cat_cf_hom_CId:
  assumes "[c, c']\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<CC> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
  shows "cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>, \<CC>\<lparr>CId\<rparr>\<lparr>c'\<rparr>]\<^sub>\<circ> = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> c c'\<rparr>"
proof-

  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)
  interpret op_\<CC>: category \<alpha> \<open>op_cat \<CC>\<close> by (rule category_op)

  from assms have op_c: "c \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>" and c': "c' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by (auto elim: cat_prod_2_ObjE[rotated 2] intro: cat_cs_intros)
  then have c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" unfolding cat_op_simps by simp

  from c c' category_axioms Set.category_axioms have cf_hom_cc': 
    "cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>, \<CC>\<lparr>CId\<rparr>\<lparr>c'\<rparr>]\<^sub>\<circ> : Hom \<CC> c c' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> c c'"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_op_simps 
          cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
      )
  then have dom_lhs: "\<D>\<^sub>\<circ> (cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>, \<CC>\<lparr>CId\<rparr>\<lparr>c'\<rparr>]\<^sub>\<circ>\<lparr>ArrVal\<rparr>) = Hom \<CC> c c'"
    by (cs_concl cs_simp: cat_cs_simps)
  from c c' category_axioms Set.category_axioms have CId_cc':
    "cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> c c'\<rparr> : Hom \<CC> c c' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> c c'"
    by 
      (
        cs_concl 
          cs_simp: cat_Set_cs_simps cat_Set_components(1) 
          cs_intro: cat_cs_intros cat_prod_cs_intros
      )
  then have dom_rhs: "\<D>\<^sub>\<circ> (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> c c'\<rparr>\<lparr>ArrVal\<rparr>) = Hom \<CC> c c'"    
    by (cs_concl cs_simp: cat_cs_simps )

  show ?thesis
  proof(rule arr_Set_eqI[of \<alpha>])
    from cf_hom_cc' show arr_Set_CId_cc': 
      "arr_Set \<alpha> (cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>, \<CC>\<lparr>CId\<rparr>\<lparr>c'\<rparr>]\<^sub>\<circ>)"
      by (auto dest: cat_Set_is_arrD(1))  
    from CId_cc' show arr_Set_Hom_cc': 
      "arr_Set \<alpha> (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> c c'\<rparr>)"
      by (auto simp: cat_Set_is_arrD(1))
    show "cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>, \<CC>\<lparr>CId\<rparr>\<lparr>c'\<rparr>]\<^sub>\<circ>\<lparr>ArrVal\<rparr> =
      cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> c c'\<rparr>\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
      fix q assume "q : c \<mapsto>\<^bsub>\<CC>\<^esub> c'" 
      with category_axioms show
        "cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>, \<CC>\<lparr>CId\<rparr>\<lparr>c'\<rparr>]\<^sub>\<circ>\<lparr>ArrVal\<rparr>\<lparr>q\<rparr> = 
          cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> c c'\<rparr>\<lparr>ArrVal\<rparr>\<lparr>q\<rparr>"
        by (*slow*)
          (
            cs_concl
              cs_simp: cat_cs_simps cat_op_simps cat_Set_cs_simps
              cs_intro: cat_cs_intros
         )
    qed (use arr_Set_CId_cc' arr_Set_Hom_cc' in auto)
  
  qed (use cf_hom_cc' CId_cc' in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

qed

lemmas [cat_cs_simps] = category.cat_cf_hom_CId


subsubsection\<open>Opposite \<open>hom\<close>-function\<close>

lemma (in category) cat_op_cat_cf_hom:
  assumes "g : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and "g' : a' \<mapsto>\<^bsub>op_cat \<CC>\<^esub> b'"
  shows "cf_hom (op_cat \<CC>) [g, g']\<^sub>\<circ> = cf_hom \<CC> [g', g]\<^sub>\<circ>"
proof(rule arr_Set_eqI[of \<alpha>])
  from assms show "arr_Set \<alpha> (cf_hom (op_cat \<CC>) [g, g']\<^sub>\<circ>)"
    by 
      ( 
        cs_concl 
          cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_prod_cs_intros
      )
  from assms show "arr_Set \<alpha> (cf_hom \<CC> [g', g]\<^sub>\<circ>)"
    by 
      ( 
        cs_concl 
          cs_simp: cat_op_simps 
          cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
      )
  from assms have dom_lhs:
    "\<D>\<^sub>\<circ> (cf_hom (op_cat \<CC>) [g, g']\<^sub>\<circ>\<lparr>ArrVal\<rparr>) = Hom \<CC> a' a"
    by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
  from assms have dom_rhs: "\<D>\<^sub>\<circ> (cf_hom \<CC> [g', g]\<^sub>\<circ>\<lparr>ArrVal\<rparr>) = Hom \<CC> a' a"
    by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
  show "cf_hom (op_cat \<CC>) [g, g']\<^sub>\<circ>\<lparr>ArrVal\<rparr> = cf_hom \<CC> [g', g]\<^sub>\<circ>\<lparr>ArrVal\<rparr>"
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
    fix f assume "f : a' \<mapsto>\<^bsub>\<CC>\<^esub> a"
    with assms show 
      "cf_hom (op_cat \<CC>) [g, g']\<^sub>\<circ>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> = cf_hom \<CC> [g', g]\<^sub>\<circ>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
      unfolding cat_op_simps
      by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
  qed (simp_all add: cf_hom_components)
  from category_axioms assms show 
    "cf_hom (op_cat \<CC>) [g, g']\<^sub>\<circ>\<lparr>ArrDom\<rparr> = cf_hom \<CC> [g', g]\<^sub>\<circ>\<lparr>ArrDom\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: category.cf_hom_ArrDom cat_op_simps 
          cs_intro: cat_op_intros cat_prod_cs_intros
      )
  from category_axioms assms show 
    "cf_hom (op_cat \<CC>) [g, g']\<^sub>\<circ>\<lparr>ArrCod\<rparr> = cf_hom \<CC> [g', g]\<^sub>\<circ>\<lparr>ArrCod\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: category.cf_hom_ArrCod cat_op_simps 
          cs_intro: cat_op_intros cat_prod_cs_intros
      )
qed

lemmas [cat_cs_simps] = category.cat_op_cat_cf_hom



subsection\<open>\<open>Hom\<close>-functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
See \cite{noauthor_nlab_nodate}\footnote{\url{
https://ncatlab.org/nlab/show/hom-functor
}}.
\<close>

definition cf_Hom :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>Hom\<^sub>O\<^sub>.\<^sub>C\<index>_'(/-,-/')\<close>)
  where "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-) = 
    [
      (\<lambda>a\<in>\<^sub>\<circ>(op_cat \<CC> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>. Hom \<CC> (vpfst a) (vpsnd a)),
      (\<lambda>f\<in>\<^sub>\<circ>(op_cat \<CC> \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>. cf_hom \<CC> f),
      op_cat \<CC> \<times>\<^sub>C \<CC>,
      cat_Set \<alpha>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_Hom_components:
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr> = 
    (\<lambda>a\<in>\<^sub>\<circ>(op_cat \<CC> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>. Hom \<CC> (vpfst a) (vpsnd a))"
    and "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ArrMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>(op_cat \<CC> \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>. cf_hom \<CC> f)"
    and "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>HomDom\<rparr> = op_cat \<CC> \<times>\<^sub>C \<CC>"
    and "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>HomCod\<rparr> = cat_Set \<alpha>"
  unfolding cf_Hom_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda cf_Hom_components(1)
  |vsv cf_Hom_ObjMap_vsv|

lemma cf_Hom_ObjMap_vdomain[cat_cs_simps]:  
  "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>) = (op_cat \<CC> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
  unfolding cf_Hom_components by simp

lemma cf_Hom_ObjMap_app[cat_cs_simps]: 
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<CC> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> = Hom \<CC> a b"
  using assms unfolding cf_Hom_components by (simp add: nat_omega_simps)
                
lemma (in category) cf_Hom_ObjMap_vrange: 
  "\<R>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
proof(intro vsubsetI)
  interpret op_\<CC>: category \<alpha> \<open>op_cat \<CC>\<close> by (simp add: category_op)
  fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>)"
  then obtain x where y_def: "y = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>" 
    and x: "x \<in>\<^sub>\<circ> (op_cat \<CC> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
    unfolding cf_Hom_components by auto
  then obtain a b where x_def: "x = [a, b]\<^sub>\<circ>" 
    and a: "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>" 
    and b: "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    by (elim cat_prod_2_ObjE[OF op_\<CC>.category_axioms category_axioms x])
  from a have a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" unfolding cat_op_simps by simp
  from a b show "y \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    unfolding 
      y_def x_def cf_Hom_ObjMap_app[OF x[unfolded x_def]] cat_Set_components
    by (auto simp: cat_cs_intros)
qed


subsubsection\<open>Arrow map\<close>

mk_VLambda cf_Hom_components(2)
  |vsv cf_Hom_ArrMap_vsv|
  |vdomain cf_Hom_ArrMap_vdomain[cat_cs_simps]|
  |app cf_Hom_ArrMap_app[cat_cs_simps]|


subsubsection\<open>\<open>Hom\<close>-functor is a functor\<close>

lemma (in category) cat_Hom_is_functor:
  "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-) : op_cat \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-

  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)
  interpret \<CC>\<CC>: category \<alpha> \<open>op_cat \<CC> \<times>\<^sub>C \<CC>\<close>
    by (simp add: category_axioms category_cat_prod_2 category_op)
  interpret op_\<CC>: category \<alpha> \<open>op_cat \<CC>\<close> by (rule category_op)

  show ?thesis
  proof(intro is_functorI')

    show "vfsequence Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)"
      unfolding cf_Hom_def by simp
    show op_\<CC>_\<CC>: "category \<alpha> (op_cat \<CC> \<times>\<^sub>C \<CC>)" by (auto simp: cat_cs_intros)
    show "vcard Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-) = 4\<^sub>\<nat>"
      unfolding cf_Hom_def by (simp add: nat_omega_simps)
  
    show "\<R>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
      by (simp add: cf_Hom_ObjMap_vrange)
    show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>\<lparr>cd\<rparr>"
      if gf: "gf : ab \<mapsto>\<^bsub>op_cat \<CC> \<times>\<^sub>C \<CC>\<^esub> cd" for gf ab cd
      unfolding slicing_simps cat_smc_cat_Set[symmetric]
    proof-
      obtain g f a b c d where gf_def: "gf = [g, f]\<^sub>\<circ>"
        and ab_def: "ab = [a, b]\<^sub>\<circ>"
        and cd_def: "cd = [c, d]\<^sub>\<circ>"   
        and "g : a \<mapsto>\<^bsub>op_cat \<CC>\<^esub> c"  
        and f: "f : b \<mapsto>\<^bsub>\<CC>\<^esub> d"
        by (elim cat_prod_2_is_arrE[OF category_op category_axioms gf])
      then have g: "g : c \<mapsto>\<^bsub>\<CC>\<^esub> a" unfolding cat_op_simps by simp
      from category_axioms that g f show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> :
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>\<lparr>cd\<rparr>"
        unfolding gf_def ab_def cd_def (*slow*)
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)
    qed

    show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ArrMap\<rparr>\<lparr>gg' \<circ>\<^sub>A\<^bsub>op_cat \<CC> \<times>\<^sub>C \<CC>\<^esub> ff'\<rparr> = 
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ArrMap\<rparr>\<lparr>gg'\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ArrMap\<rparr>\<lparr>ff'\<rparr>"
      if gg': "gg' : bb' \<mapsto>\<^bsub>op_cat \<CC> \<times>\<^sub>C \<CC>\<^esub> cc'" 
        and ff': "ff' : aa' \<mapsto>\<^bsub>op_cat \<CC> \<times>\<^sub>C \<CC>\<^esub> bb'" 
      for gg' bb' cc' ff' aa'
    proof-
      obtain g g' b b' c c' 
        where gg'_def: "gg' = [g, g']\<^sub>\<circ>"
          and bb'_def: "bb' = [b, b']\<^sub>\<circ>"
          and cc'_def: "cc' = [c, c']\<^sub>\<circ>"   
          and "g : b \<mapsto>\<^bsub>op_cat \<CC>\<^esub> c"  
          and g': "g' : b' \<mapsto>\<^bsub>\<CC>\<^esub> c'"
        by (elim cat_prod_2_is_arrE[OF category_op category_axioms gg'])
      moreover obtain f f' a a' b'' b''' 
        where ff'_def: "ff' = [f, f']\<^sub>\<circ>"
          and aa'_def: "aa' = [a, a']\<^sub>\<circ>"
          and "bb' = [b'', b''']\<^sub>\<circ>"   
          and "f : a \<mapsto>\<^bsub>op_cat \<CC>\<^esub> b''"  
          and "f' : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'''"
        by (elim cat_prod_2_is_arrE[OF category_op category_axioms ff'])
      ultimately have f: "f : b \<mapsto>\<^bsub>\<CC>\<^esub> a" 
        and f': "f' : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'" 
        and g: "g : c \<mapsto>\<^bsub>\<CC>\<^esub> b"
        by (auto simp: cat_op_simps)
      from category_axioms that g f  g' f' show ?thesis
        unfolding 
          slicing_simps cat_smc_cat_Set[symmetric] 
          gg'_def bb'_def cc'_def ff'_def aa'_def
        by (*slow*)
          (
            cs_concl
              cs_simp: cat_cs_simps cat_op_simps cat_prod_cs_simps
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
    qed

    show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ArrMap\<rparr>\<lparr>(op_cat \<CC> \<times>\<^sub>C \<CC>)\<lparr>CId\<rparr>\<lparr>cc'\<rparr>\<rparr> = 
      cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>\<lparr>cc'\<rparr>\<rparr>"
      if "cc' \<in>\<^sub>\<circ> (op_cat \<CC> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>" for cc'
    proof-
      from that obtain c c' 
        where cc'_def: "cc' = [c, c']\<^sub>\<circ>" 
          and c: "c \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
          and c': "c' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        by (elim cat_prod_2_ObjE[rotated 2]) (auto intro: cat_cs_intros)
      then have c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" unfolding cat_op_simps by simp
      with c' category_axioms Set.category_axioms that show ?thesis
        unfolding cc'_def
        by
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_op_simps cat_prod_cs_simps
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
    qed

  qed (auto simp: cf_Hom_components cat_cs_intros)

qed

lemma (in category) cat_Hom_is_functor':
  assumes "\<beta> = \<alpha>" and "\<AA>' = op_cat \<CC> \<times>\<^sub>C \<CC>" and "\<BB>' = cat_Set \<alpha>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-) : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<BB>'"
  unfolding assms by (rule cat_Hom_is_functor)

lemmas [cat_cs_intros] = category.cat_Hom_is_functor'



subsection\<open>Composition of a \<open>Hom\<close>-functor and two functors\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cf_bcomp_Hom :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>Hom\<^sub>O\<^sub>.\<^sub>C\<index>_'(/_-,_-/')\<close>)
  \<comment>\<open>The following definition may seem redundant, but it will help to avoid
  proof duplication later.\<close>
  where "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>-) = cf_cn_cov_bcomp (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)) \<FF> \<GG>"


subsubsection\<open>Object map\<close>

lemma cf_bcomp_Hom_ObjMap_vsv: "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>-)\<lparr>ObjMap\<rparr>)"
  unfolding cf_bcomp_Hom_def by (rule cf_cn_cov_bcomp_ObjMap_vsv)

lemma cf_bcomp_Hom_ObjMap_vdomain[cat_cs_simps]:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>-)\<lparr>ObjMap\<rparr>) = (op_cat \<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
  using assms unfolding cf_bcomp_Hom_def by (rule cf_cn_cov_bcomp_ObjMap_vdomain)

lemma cf_bcomp_Hom_ObjMap_app[cat_cs_simps]:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>-)\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> = 
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>, \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet>"
  using assms unfolding cf_bcomp_Hom_def by (rule cf_cn_cov_bcomp_ObjMap_app)
  
lemma (in category) cf_bcomp_Hom_ObjMap_vrange:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>-)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  using category_axioms
  unfolding cf_bcomp_Hom_def
  by (intro cf_cn_cov_bcomp_ObjMap_vrange[OF assms])
    (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)


subsubsection\<open>Arrow map\<close>

lemma cf_bcomp_Hom_ArrMap_vsv: "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>-)\<lparr>ArrMap\<rparr>)"
  unfolding cf_bcomp_Hom_def by (rule cf_cn_cov_bcomp_ArrMap_vsv)

lemma cf_bcomp_Hom_ArrMap_vdomain[cat_cs_simps]:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>-)\<lparr>ArrMap\<rparr>) = (op_cat \<AA> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>"
  using assms 
  unfolding cf_bcomp_Hom_def 
  by (rule cf_cn_cov_bcomp_ArrMap_vdomain)

lemma cf_bcomp_Hom_ArrMap_app[cat_cs_simps]:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "[f, g]\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<AA> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>"
  shows 
    "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>-)\<lparr>ArrMap\<rparr>\<lparr>f, g\<rparr>\<^sub>\<bullet> = 
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>, \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>\<rparr>\<^sub>\<bullet>"
  using assms 
  unfolding cf_bcomp_Hom_def 
  by (rule cf_cn_cov_bcomp_ArrMap_app)

lemma (in category) cf_bcomp_Hom_ArrMap_vrange:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>-)\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Arr\<rparr>"
  using category_axioms
  unfolding cf_bcomp_Hom_def
  by (intro cf_cn_cov_bcomp_ArrMap_vrange[OF assms])
    (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)


subsubsection\<open>Composition of a \<open>Hom\<close>-functor and two functors is a functor\<close>

lemma (in category) cat_cf_bcomp_Hom_is_functor:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>-) : op_cat \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  using assms category_axioms
  unfolding cf_bcomp_Hom_def
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemma (in category) cat_cf_bcomp_Hom_is_functor':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<beta> = \<alpha>"
    and "\<AA>' = op_cat \<AA> \<times>\<^sub>C \<BB>"
    and "\<BB>' = cat_Set \<alpha>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>-) : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<BB>'"
  using assms(1,2) unfolding assms(3-5) by (rule cat_cf_bcomp_Hom_is_functor)

lemmas [cat_cs_intros] = category.cat_cf_bcomp_Hom_is_functor'



subsection\<open>Composition of a \<open>Hom\<close>-functor and a functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See subsection 1.15 in \cite{bodo_categories_1970}.\<close>

definition cf_lcomp_Hom :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>Hom\<^sub>O\<^sub>.\<^sub>C\<index>_'(/_-,-/')\<close>)
  where "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) = cf_cn_cov_lcomp \<CC> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)) \<FF>"

definition cf_rcomp_Hom :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>Hom\<^sub>O\<^sub>.\<^sub>C\<index>_'(/-,_-/')\<close>)
  where "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-) = cf_cn_cov_rcomp \<CC> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)) \<GG>"


subsubsection\<open>Object map\<close>

lemma cf_lcomp_Hom_ObjMap_vsv[cat_cs_intros]: "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<lparr>ObjMap\<rparr>)"
  unfolding cf_lcomp_Hom_def by (rule cf_cn_cov_lcomp_ObjMap_vsv)

lemma cf_rcomp_Hom_ObjMap_vsv[cat_cs_intros]: "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ObjMap\<rparr>)"
  unfolding cf_rcomp_Hom_def by (rule cf_cn_cov_rcomp_ObjMap_vsv)

lemma cf_lcomp_Hom_ObjMap_vdomain[cat_cs_simps]:
  assumes "category \<alpha> \<CC>" and "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<lparr>ObjMap\<rparr>) = (op_cat \<BB> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
  using assms
  by (cs_concl cs_simp: cat_cs_simps cf_lcomp_Hom_def cs_intro: cat_cs_intros)

lemma cf_rcomp_Hom_ObjMap_vdomain[cat_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ObjMap\<rparr>) = (op_cat \<CC> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
  using assms
  by (cs_concl cs_simp: cat_cs_simps cf_rcomp_Hom_def cs_intro: cat_cs_intros)

lemma cf_lcomp_Hom_ObjMap_app[cat_cs_simps]:
  assumes "category \<alpha> \<CC>"
    and "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "b \<in>\<^sub>\<circ> op_cat \<BB>\<lparr>Obj\<rparr>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<lparr>ObjMap\<rparr>\<lparr>b, c\<rparr>\<^sub>\<bullet> = 
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>, c\<rparr>\<^sub>\<bullet>"
  using assms
  unfolding cf_lcomp_Hom_def
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_prod_cs_intros)

lemma cf_rcomp_Hom_ObjMap_app[cat_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "c \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ObjMap\<rparr>\<lparr>c, b\<rparr>\<^sub>\<bullet> =
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>\<lparr>c, \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet>"
  using assms
  by 
    (
      cs_concl
        cs_simp: cat_cs_simps cf_rcomp_Hom_def
        cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
    )

lemma (in category) cat_cf_lcomp_Hom_ObjMap_vrange: 
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  using category_axioms assms
  unfolding cf_lcomp_Hom_def
  by (intro cf_cn_cov_lcomp_ObjMap_vrange) 
    (cs_concl cs_intro: cat_cs_intros)

lemma (in category) cat_cf_rcomp_Hom_ObjMap_vrange: 
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  using category_axioms assms
  unfolding cf_rcomp_Hom_def  
  by (intro cf_cn_cov_rcomp_ObjMap_vrange) 
    (cs_concl cs_intro: cat_cs_intros)


subsubsection\<open>Arrow map\<close>

lemma cf_lcomp_Hom_ArrMap_vsv[cat_cs_intros]: "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<lparr>ArrMap\<rparr>)"
  unfolding cf_lcomp_Hom_def by (rule cf_cn_cov_lcomp_ArrMap_vsv)

lemma cf_rcomp_Hom_ArrMap_vsv[cat_cs_intros]: "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ArrMap\<rparr>)"
  unfolding cf_rcomp_Hom_def by (rule cf_cn_cov_rcomp_ArrMap_vsv)

lemma cf_lcomp_Hom_ArrMap_vdomain[cat_cs_simps]:  
  assumes "category \<alpha> \<CC>" and "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<lparr>ArrMap\<rparr>) = (op_cat \<BB> \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>"
  using assms
  unfolding cf_lcomp_Hom_def
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemma cf_rcomp_Hom_ArrMap_vdomain[cat_cs_simps]:  
  assumes "category \<alpha> \<CC>" and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ArrMap\<rparr>) = (op_cat \<CC> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>"
  using assms unfolding cf_rcomp_Hom_def by (cs_concl cs_simp: cat_cs_simps)

lemma cf_lcomp_Hom_ArrMap_app[cat_cs_simps]:
  assumes "category \<alpha> \<CC>" 
    and "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "g : a \<mapsto>\<^bsub>op_cat \<BB>\<^esub> b"
    and "f : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> =
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>, f\<rparr>\<^sub>\<bullet>"
  using assms
  unfolding cf_lcomp_Hom_def cat_op_simps 
  by 
    (
      cs_concl 
        cs_simp: cat_cs_simps cat_op_simps 
        cs_intro: cat_cs_intros cat_prod_cs_intros
    )

lemma cf_rcomp_Hom_ArrMap_app[cat_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "g : a \<mapsto>\<^bsub>op_cat \<CC>\<^esub> b"
    and "f : a' \<mapsto>\<^bsub>\<BB>\<^esub> b'"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> =
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ArrMap\<rparr>\<lparr>g, \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>\<^sub>\<bullet>"
  using assms 
  by
    (
      cs_concl
        cs_simp: cat_cs_simps cf_rcomp_Hom_def
        cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
    )

lemma (in category) cf_lcomp_Hom_ArrMap_vrange: 
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Arr\<rparr>"
  using category_axioms assms
  unfolding cf_lcomp_Hom_def
  by (intro cf_cn_cov_lcomp_ArrMap_vrange)
    (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemma (in category) cf_rcomp_Hom_ArrMap_vrange: 
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Arr\<rparr>"
  using category_axioms assms
  unfolding cf_rcomp_Hom_def
  by (intro cf_cn_cov_rcomp_ArrMap_vrange)
    (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)


subsubsection\<open>Further properties\<close>

lemma cf_bcomp_Hom_cf_lcomp_Hom[cat_cs_simps]:
  "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,cf_id \<CC>-) = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)"
  unfolding cf_lcomp_Hom_def cf_cn_cov_lcomp_def cf_bcomp_Hom_def ..

lemma cf_bcomp_Hom_cf_rcomp_Hom[cat_cs_simps]:
  "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(cf_id \<CC>-,\<GG>-) = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)"
  unfolding cf_rcomp_Hom_def cf_cn_cov_rcomp_def cf_bcomp_Hom_def ..


subsubsection\<open>Composition of a \<open>Hom\<close>-functor and a functor is a functor\<close>

lemma (in category) cat_cf_lcomp_Hom_is_functor:
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  using category_axioms assms
  unfolding cf_lcomp_Hom_def
  by (intro cf_cn_cov_lcomp_is_functor) 
    (cs_concl cs_intro: cat_cs_intros)

lemma (in category) cat_cf_lcomp_Hom_is_functor':
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<beta> = \<alpha>" 
    and "\<AA>' = op_cat \<BB> \<times>\<^sub>C \<CC>" 
    and "\<BB>' = cat_Set \<alpha>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<BB>'"
  using assms(1) 
  unfolding assms(2-4) 
  by (rule cat_cf_lcomp_Hom_is_functor) 

lemmas [cat_cs_intros] = category.cat_cf_lcomp_Hom_is_functor'

lemma (in category) cat_cf_rcomp_Hom_is_functor:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-) : op_cat \<CC> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  using category_axioms assms
  unfolding cf_rcomp_Hom_def
  by (intro cf_cn_cov_rcomp_is_functor) 
    (cs_concl cs_intro: cat_cs_intros cat_op_intros)

lemma (in category) cat_cf_rcomp_Hom_is_functor':
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<beta> = \<alpha>" 
    and "\<AA>' = op_cat \<CC> \<times>\<^sub>C \<BB>" 
    and "\<BB>' = cat_Set \<alpha>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-) : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<BB>'"
  using assms(1) 
  unfolding assms(2-4) 
  by (rule cat_cf_rcomp_Hom_is_functor) 

lemmas [cat_cs_intros] = category.cat_cf_rcomp_Hom_is_functor'


subsubsection\<open>Flip of a projections of a \<open>Hom\<close>-functor\<close>

lemma (in category) cat_bifunctor_flip_cf_rcomp_Hom:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows 
    "bifunctor_flip (op_cat \<CC>) \<BB> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)) =
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(op_cf \<GG>-,-)"
proof(rule cf_eqI)

  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms)

  from category_axioms assms show bf_Hom:
    "bifunctor_flip (op_cat \<CC>) \<BB> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-) :
      \<BB> \<times>\<^sub>C op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_intro: cat_cs_intros)
  from category_axioms assms show op_Hom:
    "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(op_cf \<GG>-,-) : \<BB> \<times>\<^sub>C op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros)

  from bf_Hom have ObjMap_dom_lhs:
    "\<D>\<^sub>\<circ> (bifunctor_flip (op_cat \<CC>) \<BB> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ObjMap\<rparr>) = 
      (\<BB> \<times>\<^sub>C op_cat \<CC>)\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  from op_Hom have ObjMap_dom_rhs:
    "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(op_cf \<GG>-,-)\<lparr>ObjMap\<rparr>) = (\<BB> \<times>\<^sub>C op_cat \<CC>)\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  from bf_Hom have ArrMap_dom_lhs:
    "\<D>\<^sub>\<circ> (bifunctor_flip (op_cat \<CC>) \<BB> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ArrMap\<rparr>) = 
      (\<BB> \<times>\<^sub>C op_cat \<CC>)\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  from op_Hom have ArrMap_dom_rhs:
    "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(op_cf \<GG>-,-)\<lparr>ArrMap\<rparr>) = (\<BB> \<times>\<^sub>C op_cat \<CC>)\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)

  show 
    "bifunctor_flip (op_cat \<CC>) \<BB> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ObjMap\<rparr> =
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(op_cf \<GG>-,-)\<lparr>ObjMap\<rparr>"
  proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
    fix bc assume "bc \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C op_cat \<CC>)\<lparr>Obj\<rparr>"
    then obtain b c 
      where bc_def: "bc = [b, c]\<^sub>\<circ>" and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
      by 
        (
          auto 
            elim: cat_prod_2_ObjE[OF \<GG>.HomDom.category_axioms category_op] 
            simp: cat_op_simps
        )
    from category_axioms assms b c show 
      "bifunctor_flip (op_cat \<CC>) \<BB> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ObjMap\<rparr>\<lparr>bc\<rparr> =
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(op_cf \<GG>-,-)\<lparr>ObjMap\<rparr>\<lparr>bc\<rparr>"
      unfolding bc_def
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_op_simps 
            cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
        )
  qed (auto intro: cat_cs_intros)

  show 
    "bifunctor_flip (op_cat \<CC>) \<BB> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ArrMap\<rparr> =
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(op_cf \<GG>-,-)\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
    fix gf assume "gf \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C op_cat \<CC>)\<lparr>Arr\<rparr>"
    then obtain g f 
      where gf_def: "gf = [g, f]\<^sub>\<circ>" and "g \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" and "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
      by 
        (
          auto 
            elim: cat_prod_2_ArrE[OF \<GG>.HomDom.category_axioms category_op] 
            simp: cat_op_simps
        )
    then obtain a b c d where g: "g : a \<mapsto>\<^bsub>\<BB>\<^esub> b" and f: "f : c \<mapsto>\<^bsub>\<CC>\<^esub> d"
      by (auto intro!: is_arrI)
    from category_axioms assms g f show 
      "bifunctor_flip (op_cat \<CC>) \<BB> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> =
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(op_cf \<GG>-,-)\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr>"
      unfolding gf_def
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_op_simps
            cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
        )
  qed (auto intro: cat_cs_intros)

qed (auto intro: cat_cs_intros simp: cat_op_simps)

lemmas [cat_cs_simps] = category.cat_bifunctor_flip_cf_rcomp_Hom 

lemma (in category) cat_bifunctor_flip_cf_lcomp_Hom:
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows 
    "bifunctor_flip (op_cat \<BB>) \<CC> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)) =
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(-,op_cf \<FF>-)"
proof-
  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(1))
  note Hom_\<FF> = 
    category.cat_bifunctor_flip_cf_rcomp_Hom
      [
        OF category_op is_functor_op[OF assms], 
        unfolded cat_op_simps, 
        symmetric
      ]
  from category_axioms assms show ?thesis
    by (subst Hom_\<FF>)
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_op_simps 
          cs_intro: cat_cs_intros cat_op_intros
      )+
qed

lemmas [cat_cs_simps] = category.cat_bifunctor_flip_cf_lcomp_Hom



subsection\<open>Projections of the \<open>Hom\<close>-functor\<close>


text\<open>
The projections of the \<open>Hom\<close>-functor coincide with the definitions
of the \<open>Hom\<close>-functor given in Chapter II-2 in \cite{mac_lane_categories_2010}.
They are also exposed in the aforementioned article in 
nLab \cite{noauthor_nlab_nodate}\footnote{\url{
https://ncatlab.org/nlab/show/hom-functor
}}.
\<close>


subsubsection\<open>Definitions and elementary properties\<close>

definition cf_Hom_snd :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>Hom\<^sub>O\<^sub>.\<^sub>C\<index>_'(/_,-/')\<close>)
  where "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<^bsub>op_cat \<CC>,\<CC>\<^esub>(a,-)\<^sub>C\<^sub>F"
definition cf_Hom_fst :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>Hom\<^sub>O\<^sub>.\<^sub>C\<index>_'(/-,_/')\<close>)
  where "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,b) = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<^bsub>op_cat \<CC>,\<CC>\<^esub>(-,b)\<^sub>C\<^sub>F"


subsubsection\<open>Projections of the \<open>Hom\<close>-functor are functors\<close>

lemma (in category) cat_cf_Hom_snd_is_functor:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-  
  from assms have a: "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>" unfolding cat_op_simps by simp
  have op_\<CC>: "category \<alpha> (op_cat \<CC>)" by (auto intro: cat_cs_intros)
  from op_\<CC> category_axioms cat_Hom_is_functor a show ?thesis
    unfolding cf_Hom_snd_def by (rule bifunctor_proj_snd_is_functor)
qed

lemma (in category) cat_cf_Hom_snd_is_functor':
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "\<beta> = \<alpha>" and "\<CC>' = \<CC>" and "\<DD>' = cat_Set \<alpha>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<DD>'"
  using assms(1) unfolding assms(2-4) by (rule cat_cf_Hom_snd_is_functor)

lemmas [cat_cs_intros] = category.cat_cf_Hom_snd_is_functor'

lemma (in category) cat_cf_Hom_fst_is_functor:
  assumes "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,b) : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-  
  have op_\<CC>: "category \<alpha> (op_cat \<CC>)" by (auto intro: cat_cs_intros)
  from op_\<CC> category_axioms cat_Hom_is_functor assms show ?thesis
    unfolding cf_Hom_fst_def by (rule bifunctor_proj_fst_is_functor)
qed

lemma (in category) cat_cf_Hom_fst_is_functor':
  assumes "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "\<beta> = \<alpha>" and "\<CC>' = op_cat \<CC>" and "\<DD>' = cat_Set \<alpha>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,b) : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<DD>'"
  using assms(1) unfolding assms(2-4) by (rule cat_cf_Hom_fst_is_functor)

lemmas [cat_cs_intros] = category.cat_cf_Hom_fst_is_functor'


subsubsection\<open>Object maps\<close>

lemma (in category) cat_cf_Hom_snd_ObjMap_vsv[cat_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)\<lparr>ObjMap\<rparr>)"
  unfolding cf_Hom_snd_def
  using category_axioms assms
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)

lemmas [cat_cs_intros] = category.cat_cf_Hom_snd_ObjMap_vsv

lemma (in category) cat_cf_Hom_fst_ObjMap_vsv[cat_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,b)\<lparr>ObjMap\<rparr>)"
  unfolding cf_Hom_fst_def
  using category_axioms assms
  by
    (
      cs_concl 
        cs_simp: cat_prod_cs_simps cat_cs_simps
        cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
    )

lemmas [cat_cs_intros] = category.cat_cf_Hom_fst_ObjMap_vsv

lemma (in category) cat_cf_Hom_snd_ObjMap_vdomain[cat_cs_simps]:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)\<lparr>ObjMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
  using category_axioms assms
  unfolding cf_Hom_snd_def
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)

lemmas [cat_cs_simps] = category.cat_cf_Hom_snd_ObjMap_vdomain

lemma (in category) cat_cf_Hom_fst_ObjMap_vdomain[cat_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,b)\<lparr>ObjMap\<rparr>) = op_cat \<CC>\<lparr>Obj\<rparr>"
  using category_axioms assms
  unfolding cf_Hom_fst_def
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)

lemmas [cat_cs_simps] = category.cat_cf_Hom_fst_ObjMap_vdomain

lemma (in category) cat_cf_Hom_snd_ObjMap_app[cat_cs_simps]:
  assumes "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> = Hom \<CC> a b"
proof-
  from assms have ab: "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<CC> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
    by (intro cat_prod_2_ObjI) (auto intro: cat_cs_intros)
  show ?thesis
    unfolding 
      cf_Hom_snd_def
      bifunctor_proj_snd_ObjMap_app[OF category_op category_axioms ab]
      cf_Hom_ObjMap_app[OF ab]
      ..
qed

lemmas [cat_cs_simps] = category.cat_cf_Hom_snd_ObjMap_app

lemma (in category) cat_cf_Hom_fst_ObjMap_app[cat_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,b)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = Hom \<CC> a b"
proof-
  from assms have ab: "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<CC> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
    by (intro cat_prod_2_ObjI) (auto intro: cat_cs_intros)
  show ?thesis
    unfolding 
      cf_Hom_fst_def
      bifunctor_proj_fst_ObjMap_app[OF category_op category_axioms ab]
      cf_Hom_ObjMap_app[OF ab]
      ..
qed

lemmas [cat_cs_simps] = category.cat_cf_Hom_fst_ObjMap_app


subsubsection\<open>Arrow maps\<close>

lemma (in category) cat_cf_Hom_snd_ArrMap_vsv[cat_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
  shows "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)\<lparr>ArrMap\<rparr>)"
  unfolding cf_Hom_snd_def
  using category_axioms assms
  by
    (
      cs_concl 
        cs_simp: cat_cs_simps 
        cs_intro: bifunctor_proj_snd_ArrMap_vsv cat_cs_intros cat_op_intros
    )

lemmas [cat_cs_intros] = category.cat_cf_Hom_snd_ArrMap_vsv

lemma (in category) cat_cf_Hom_fst_ArrMap_vsv[cat_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,b)\<lparr>ArrMap\<rparr>)"
  unfolding cf_Hom_fst_def
  using category_axioms assms
  by
    (
      cs_concl 
        cs_simp: cat_cs_simps
        cs_intro: bifunctor_proj_fst_ArrMap_vsv cat_cs_intros cat_op_intros
    )

lemmas [cat_cs_intros] = category.cat_cf_Hom_fst_ArrMap_vsv

lemma (in category) cat_cf_Hom_snd_ArrMap_vdomain[cat_cs_simps]:
  assumes "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)\<lparr>ArrMap\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
  using category_axioms assms
  unfolding cf_Hom_snd_def
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)

lemmas [cat_cs_simps] = category.cat_cf_Hom_snd_ArrMap_vdomain

lemma (in category) cat_cf_Hom_fst_ArrMap_vdomain[cat_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,b)\<lparr>ArrMap\<rparr>) = op_cat \<CC>\<lparr>Arr\<rparr>"
  using category_axioms assms
  unfolding cf_Hom_fst_def
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)

lemmas [cat_cs_simps] = category.cat_cf_Hom_fst_ArrMap_vdomain

lemma (in category) cat_cf_Hom_snd_ArrMap_app[cat_cs_simps]:
  assumes "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>" and "f : b \<mapsto>\<^bsub>\<CC>\<^esub> b'"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = cf_hom \<CC> [op_cat \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>, f]\<^sub>\<circ>"
proof-
  from assms(2) have f: "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by (simp add: cat_cs_intros)
  from category_axioms assms show ?thesis
    unfolding 
      cf_Hom_snd_def
      bifunctor_proj_snd_ArrMap_app[OF category_op category_axioms assms(1) f]
      cat_op_simps
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
      )
qed

lemmas [cat_cs_simps] = category.cat_cf_Hom_snd_ArrMap_app

lemma (in category) cat_cf_Hom_fst_ArrMap_app[cat_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "f : a \<mapsto>\<^bsub>op_cat \<CC>\<^esub> a'"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,b)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = cf_hom \<CC> [f, \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>]\<^sub>\<circ>"
proof-
  from assms(2) have f: "f \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Arr\<rparr>" by (simp add: cat_cs_intros)
  with category_axioms assms show ?thesis
    unfolding 
      cf_Hom_fst_def
      bifunctor_proj_fst_ArrMap_app[OF category_op category_axioms assms(1) f]
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
      )
qed

lemmas [cat_cs_simps] = category.cat_cf_Hom_fst_ArrMap_app


subsubsection\<open>Opposite \<open>Hom\<close>-functor projections\<close>

lemma (in category) cat_op_cat_cf_Hom_snd:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(a,-) = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,a)"
proof(rule cf_eqI[of \<alpha>])

  from assms category_axioms show 
    "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(a,-) : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"  
    by
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_op_simps   
          cs_intro: cat_cs_intros cat_op_intros
      )
  from assms category_axioms show 
    "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,a) : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_op_simps   
          cs_intro: cat_cs_intros cat_op_intros
      )

  show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(a,-)\<lparr>ObjMap\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,a)\<lparr>ObjMap\<rparr>"
  proof(rule vsv_eqI)
    from assms category_axioms show "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(a,-)\<lparr>ObjMap\<rparr>)"
      by (intro is_functor.cf_ObjMap_vsv)
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_op_simps 
            cs_intro: cat_cs_intros cat_op_intros
        )
    from assms category_axioms show "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,a)\<lparr>ObjMap\<rparr>)"
      by (intro is_functor.cf_ObjMap_vsv)
        (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms category_axioms show 
      "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(a,-)\<lparr>ObjMap\<rparr>) = \<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,a)\<lparr>ObjMap\<rparr>)"
      by
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_op_simps   
            cs_intro: cat_cs_intros cat_op_intros
        )
    show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(a,-)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,a)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "b \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(a,-)\<lparr>ObjMap\<rparr>)" for b
    proof-
      from that have "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        by 
          (
            simp add: 
              category.cat_cf_Hom_snd_ObjMap_vdomain[
                OF category_op, unfolded cat_op_simps, OF assms
                ]
          )
      from category_axioms assms this show ?thesis
        by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_op_intros)
    qed
  qed
  
  show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(a,-)\<lparr>ArrMap\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,a)\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI)
    from assms category_axioms show "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(a,-)\<lparr>ArrMap\<rparr>)"
      by (intro is_functor.cf_ArrMap_vsv)
        (cs_concl cs_intro: cat_cs_intros cat_op_intros)
    from assms category_axioms show "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,a)\<lparr>ArrMap\<rparr>)"
      by (intro is_functor.cf_ArrMap_vsv)
        (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms category_axioms show 
      "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(a,-)\<lparr>ArrMap\<rparr>) = \<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,a)\<lparr>ArrMap\<rparr>)"
      by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_op_intros)
    show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(a,-)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,a)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      if "f \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(a,-)\<lparr>ArrMap\<rparr>)" for f
    proof-
      from that have "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
        by 
          (
            simp add: 
              category.cat_cf_Hom_snd_ArrMap_vdomain[
                OF category_op, unfolded cat_op_simps, OF assms
                ]
          )
      then obtain a b where "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" by auto
      from category_axioms assms this show ?thesis
        by 
          (
            cs_concl
              cs_simp: cat_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros cat_op_intros
          )
    qed
  qed

qed simp_all

lemmas [cat_op_simps] = category.cat_op_cat_cf_Hom_snd

lemma (in category) cat_op_cat_cf_Hom_fst:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(-,a) = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)"
proof-
  from assms have a: "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>" unfolding cat_op_simps .
  have "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat (op_cat \<CC>)(a,-)" 
    unfolding cat_op_simps ..
  also have "\<dots> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(op_cat \<CC>)(-,a)"
    unfolding category.cat_op_cat_cf_Hom_snd[OF category_op a] by simp
  finally show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(op_cat \<CC>)(-,a) = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)" by simp
qed

lemmas [cat_op_simps] = category.cat_op_cat_cf_Hom_fst


subsubsection\<open>\<open>Hom\<close>-functors are injections on objects\<close>

lemma (in category) cat_cf_Hom_snd_inj:
  assumes "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-)" 
    and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "a = b"
proof(rule ccontr)
  assume prems: "a \<noteq> b"
  from assms(1) have "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>" 
    by simp
  then have "Hom \<CC> a b = Hom \<CC> b b"
    unfolding 
      cat_cf_Hom_snd_ObjMap_app[unfolded cat_op_simps, OF assms(2,3)]
      cat_cf_Hom_snd_ObjMap_app[unfolded cat_op_simps, OF assms(3,3)]
    by simp
  with assms prems show False by (force intro: cat_cs_intros)
qed

lemma (in category) cat_cf_Hom_fst_inj:
  assumes "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,a) = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,b)" and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "a = b"
proof(rule ccontr)
  assume prems: "a \<noteq> b"
  from assms(1) have "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,a)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,b)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>" 
    by simp
  then have "Hom \<CC> b a = Hom \<CC> b b"
    unfolding 
      cat_cf_Hom_fst_ObjMap_app[unfolded cat_op_simps, OF assms(2,3)]
      cat_cf_Hom_fst_ObjMap_app[unfolded cat_op_simps, OF assms(3,3)]
    by simp
  with assms prems show False by (force intro: cat_cs_intros)
qed


subsubsection\<open>\<open>Hom\<close>-functor is an array bifunctor\<close>

lemma (in category) cat_cf_Hom_is_cf_array:
  \<comment>\<open>See Chapter II-3 in \cite{mac_lane_categories_2010}.\<close>
  "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-) =
    cf_array (op_cat \<CC>) \<CC> (cat_Set \<alpha>) (cf_Hom_fst \<alpha> \<CC>) (cf_Hom_snd \<alpha> \<CC>)"
proof(rule cf_eqI[of \<alpha>])

  show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-) : op_cat \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (rule cat_Hom_is_functor)

  have c1: "category \<alpha> (op_cat \<CC>)" by (auto intro: cat_cs_intros)
  have c2: "category \<alpha> \<CC>" by (auto intro: cat_cs_intros)
  have c3: "category \<alpha> (cat_Set \<alpha>)" by (simp add: category_cat_Set)
  have c4: "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,c) : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    if "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for c
    using that by (rule cat_cf_Hom_fst_is_functor)
  have c5: "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    if "b \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>" for b
    using that unfolding cat_op_simps by (rule cat_cf_Hom_snd_is_functor)
  have c6: "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-)\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,c)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    if "b \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>" and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for b c
    using that category_axioms
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  have c7: 
    "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b',-)\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,c)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,c' )\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,- )\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>"
    if "f : b \<mapsto>\<^bsub>op_cat \<CC>\<^esub> b'" and "g : c \<mapsto>\<^bsub>\<CC>\<^esub> c'" for b c  b'  c' f g 
    using that category_axioms 
    unfolding cat_op_simps
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_op_simps 
          cs_intro: cat_cs_intros cat_op_intros
      )
  
  let ?cfa =
    \<open>cf_array (op_cat \<CC>) \<CC> (cat_Set \<alpha>) (cf_Hom_fst \<alpha> \<CC>) (cf_Hom_snd \<alpha> \<CC>)\<close>

  note cf_array_specification = 
    cf_array_specification[OF c1 c2 c3 c4 c5 c6 c7, simplified]

  from c1 c2 c3 c4 c5 c6 c7 show "?cfa : op_cat \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (rule cf_array_is_functor)

  show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr> = ?cfa\<lparr>ObjMap\<rparr>"
  proof(rule vsv_eqI, unfold cat_cs_simps)
    fix aa' assume "aa' \<in>\<^sub>\<circ> (op_cat \<CC> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
    then obtain a a' 
      where aa'_def: "aa' = [a, a']\<^sub>\<circ>" 
        and a: "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>" 
        and a': "a' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
      by (elim cat_prod_2_ObjE[OF c1 c2])
    from category_axioms a a' show 
      "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ObjMap\<rparr>\<lparr>aa'\<rparr> = ?cfa\<lparr>ObjMap\<rparr>\<lparr>aa'\<rparr>"
      unfolding aa'_def cf_array_specification(2)[OF a a'] cat_op_simps
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cs_intro: cat_op_intros cat_prod_cs_intros
        )
  qed (auto simp: cf_array_ObjMap_vsv cf_Hom_ObjMap_vsv cat_cs_simps)

  show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,-)\<lparr>ArrMap\<rparr> = ?cfa\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI, unfold cat_cs_simps)
    fix ff' assume "ff' \<in>\<^sub>\<circ> (op_cat \<CC> \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>"
    then obtain f f' 
      where ff'_def: "ff' = [f, f']\<^sub>\<circ>" 
        and f: "f \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Arr\<rparr>" 
        and f': "f' \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
      by (elim cat_prod_2_ArrE[OF c1 c2])
    then obtain a b a' b' 
      where f: "f : a \<mapsto>\<^bsub>op_cat \<CC>\<^esub> b" and f': "f' : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'"
      by (blast intro: is_arrI)
    from category_axioms f f' show "cf_hom \<CC> ff' = ?cfa\<lparr>ArrMap\<rparr>\<lparr>ff'\<rparr>"
      unfolding ff'_def cat_op_simps
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_op_simps 
            cs_intro: cat_cs_intros cat_op_intros
        )
  qed (auto simp: cf_array_ArrMap_vsv cf_Hom_ArrMap_vsv cat_cs_simps)

qed simp_all


subsubsection\<open>
Projections of the compositions of a \<open>Hom\<close>-functor and a functor are
projections of the \<open>Hom\<close>-functor
\<close>

lemma (in category) cat_cf_rcomp_Hom_cf_Hom_snd:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<^bsub>op_cat \<CC>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) \<circ>\<^sub>C\<^sub>F \<GG>"
  using category_axioms assms 
  unfolding cf_rcomp_Hom_def cf_Hom_snd_def
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)

lemmas [cat_cs_simps] = category.cat_cf_rcomp_Hom_cf_Hom_snd

lemma (in category) cat_cf_lcomp_Hom_cf_Hom_snd:
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<^bsub>op_cat \<BB>,\<CC>\<^esub>(b,-)\<^sub>C\<^sub>F = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-)"
  using category_axioms assms 
  unfolding cf_lcomp_Hom_def cf_Hom_snd_def
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)

lemmas [cat_cs_simps] = category.cat_cf_lcomp_Hom_cf_Hom_snd

lemma (in category) cat_cf_rcomp_Hom_cf_Hom_fst:
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>-)\<^bsub>op_cat \<CC>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
proof-

  from category_axioms assms have H\<FF>b:
    "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>-)\<^bsub>op_cat \<CC>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_intro: cat_cs_intros)
  from category_axioms assms have H\<FF>b':
    "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_intro: cat_cs_intros)

  from category_axioms assms have [cat_cs_simps]:
    "\<D>\<^sub>\<circ> ((Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>-)\<^bsub>op_cat \<CC>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>) = op_cat \<CC>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)+
  from category_axioms assms have [cat_cs_simps]:
    "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<lparr>ObjMap\<rparr>) = op_cat \<CC>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

  from category_axioms assms have [cat_cs_simps]:
    "\<D>\<^sub>\<circ> ((Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>-)\<^bsub>op_cat \<CC>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>) = op_cat \<CC>\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)+
  from category_axioms assms have [cat_cs_simps]:
    "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<lparr>ArrMap\<rparr>) = op_cat \<CC>\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

  show ?thesis
  proof(rule cf_eqI[OF H\<FF>b H\<FF>b'])

    show 
      "(Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>-)\<^bsub>op_cat \<CC>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr> = 
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<lparr>ObjMap\<rparr>"
    proof(rule vsv_eqI, unfold cat_cs_simps)
      from category_axioms assms show 
        "vsv ((Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>-)\<^bsub>op_cat \<CC>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>)"
        by (intro bifunctor_proj_fst_ObjMap_vsv[of \<alpha>]) 
          (cs_concl cs_intro: cat_cs_intros)+
      from assms show "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<lparr>ObjMap\<rparr>)"
        by (intro cat_cf_Hom_fst_ObjMap_vsv)
          (cs_concl cs_intro: cat_cs_intros)+
      fix a assume prems: "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
      with category_axioms assms show 
        "(Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>-)\<^bsub>op_cat \<CC>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = 
          Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps 
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
    qed simp

    show 
      "(Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>-)\<^bsub>op_cat \<CC>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr> = 
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<lparr>ArrMap\<rparr>"
    proof(rule vsv_eqI, unfold cat_cs_simps cat_op_simps)
      from category_axioms assms show 
        "vsv ((Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>-)\<^bsub>op_cat \<CC>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>)"
        by (intro bifunctor_proj_fst_ArrMap_vsv[of \<alpha>]) 
          (cs_concl cs_intro: cat_cs_intros)+
      from assms show "vsv (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<lparr>ArrMap\<rparr>)"
        by (intro cat_cf_Hom_fst_ArrMap_vsv)
          (cs_concl cs_intro: cat_cs_intros)+
      fix f assume "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
      then obtain a' b' where "f : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'" by (auto simp: cat_op_simps)
      from category_axioms assms this show 
        "(Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>-)\<^bsub>op_cat \<CC>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = 
          Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
    qed simp

  qed simp_all

qed

lemmas [cat_cs_simps] = category.cat_cf_rcomp_Hom_cf_Hom_fst

text\<open>\newpage\<close>

end