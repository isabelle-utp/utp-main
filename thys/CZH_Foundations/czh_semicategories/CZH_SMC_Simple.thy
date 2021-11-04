(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Simple semicategories\<close>
theory CZH_SMC_Simple
  imports 
    CZH_DG_Simple
    CZH_SMC_Semifunctor
begin



subsection\<open>Background\<close>


text\<open>
The section presents a variety of simple semicategories, such as the empty
semicategory \<open>0\<close> and a semicategory with one object and one arrow \<open>1\<close>.
All of the entities presented in this section are generalizations of certain
simple categories, whose definitions can be found 
in \cite{mac_lane_categories_2010}.
\<close>



subsection\<open>Empty semicategory \<open>0\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-2 in \cite{mac_lane_categories_2010}.\<close>

definition smc_0 :: "V"
  where "smc_0 = [0, 0, 0, 0, 0]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smc_0_components:
  shows "smc_0\<lparr>Obj\<rparr> = 0"
    and "smc_0\<lparr>Arr\<rparr> = 0"
    and "smc_0\<lparr>Dom\<rparr> = 0"
    and "smc_0\<lparr>Cod\<rparr> = 0"
    and "smc_0\<lparr>Comp\<rparr> = 0"
  unfolding smc_0_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma dg_smc_0: "smc_dg smc_0 = dg_0"
  unfolding smc_dg_def smc_0_def dg_0_def dg_field_simps
  by (simp add: nat_omega_simps)

lemmas_with (in \<Z>) [folded dg_smc_0, unfolded slicing_simps]: 
  smc_0_is_arr_iff = dg_0_is_arr_iff


subsubsection\<open>\<open>0\<close> is a semicategory\<close>

lemma (in \<Z>) semicategory_smc_0: "semicategory \<alpha> smc_0"
proof(intro semicategoryI)
  show "vfsequence smc_0" unfolding smc_0_def by (simp add: nat_omega_simps)
  show "vcard smc_0 = 5\<^sub>\<nat>" unfolding smc_0_def by (simp add: nat_omega_simps)
  show "digraph \<alpha> (smc_dg smc_0)"
    by (simp add: dg_smc_0 \<Z>.digraph_dg_0 \<Z>_axioms)
qed (auto simp: smc_0_components smc_0_is_arr_iff)


subsubsection\<open>A semicategory without objects is empty\<close>

lemma (in semicategory) smc_smc_0_if_Obj_0:
  assumes "\<CC>\<lparr>Obj\<rparr> = 0"
  shows "\<CC> = smc_0"
  by (rule smc_eqI[of \<alpha>])
    (
      auto simp:
        smc_cs_intros
        assms
        semicategory_smc_0 
        smc_0_components 
        smc_Arr_vempty_if_Obj_vempty 
        smc_Cod_vempty_if_Arr_vempty 
        smc_Dom_vempty_if_Arr_vempty
        smc_Comp_vempty_if_Arr_vempty
    )



subsection\<open>Empty semifunctor\<close>


text\<open>
An empty semifunctor is defined as a semifunctor between an
empty semicategory and an arbitrary semicategory.
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition smcf_0 :: "V \<Rightarrow> V"
  where "smcf_0 \<AA> = [0, 0, smc_0, \<AA>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smcf_0_components:
  shows "smcf_0 \<AA>\<lparr>ObjMap\<rparr> = 0"
    and "smcf_0 \<AA>\<lparr>ArrMap\<rparr> = 0"
    and "smcf_0 \<AA>\<lparr>HomDom\<rparr> = smc_0"
    and "smcf_0 \<AA>\<lparr>HomCod\<rparr> = \<AA>"
  unfolding smcf_0_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smcf_dghm_smcf_0: "smcf_dghm (smcf_0 \<AA>) = dghm_0 (smc_dg \<AA>)"
  unfolding 
    smcf_dghm_def smcf_0_def dg_0_def smc_0_def dghm_0_def smc_dg_def 
    dg_field_simps dghm_field_simps 
  by (simp add: nat_omega_simps)


subsubsection\<open>Empty semifunctor is a faithful semifunctor\<close>

lemma (in \<Z>) smcf_0_is_semifunctor: 
  assumes "semicategory \<alpha> \<AA>"
  shows "smcf_0 \<AA> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<AA>"
proof(rule is_ft_semifunctorI)
  show "smcf_0 \<AA> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  proof(rule is_semifunctorI, unfold dg_smc_0 smcf_dghm_smcf_0)
    show "vfsequence (smcf_0 \<AA>)" unfolding smcf_0_def by simp
    show "vcard (smcf_0 \<AA>) = 4\<^sub>\<nat>"
      unfolding smcf_0_def by (simp add: nat_omega_simps)
    show "dghm_0 (smc_dg \<AA>) : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<AA>"
      by 
        (
          simp add: 
            assms 
            dghm_0_is_dghm 
            is_ft_dghm.axioms(1) 
            semicategory.smc_digraph
        )
  qed (auto simp: assms semicategory_smc_0 smcf_0_components smc_0_is_arr_iff)
  show "smcf_dghm (smcf_0 \<AA>) : smc_dg smc_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> smc_dg \<AA>"
    by 
      (
        auto simp: 
          assms 
          \<Z>.dghm_0_is_dghm
          \<Z>_axioms 
          dg_smc_0 
          semicategory.smc_digraph 
          smcf_dghm_smcf_0
      )
qed



subsection\<open>\<open>10\<close>: semicategory with one object and no arrows\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition smc_10 :: "V \<Rightarrow> V"
  where "smc_10 \<aa> = [set {\<aa>}, 0, 0, 0, 0]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smc_10_components:
  shows "smc_10 \<aa>\<lparr>Obj\<rparr> = set {\<aa>}"
    and "smc_10 \<aa>\<lparr>Arr\<rparr> = 0"
    and "smc_10 \<aa>\<lparr>Dom\<rparr> = 0"
    and "smc_10 \<aa>\<lparr>Cod\<rparr> = 0"
    and "smc_10 \<aa>\<lparr>Comp\<rparr> = 0"
  unfolding smc_10_def dg_field_simps by (auto simp: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smc_dg_smc_10: "smc_dg (smc_10 \<aa>) = (dg_10 \<aa>)"
  unfolding smc_dg_def smc_10_def dg_10_def dg_field_simps
  by (simp add: nat_omega_simps)

lemmas_with (in \<Z>) [folded smc_dg_smc_10, unfolded slicing_simps]: 
  smc_10_is_arr_iff = dg_10_is_arr_iff


subsubsection\<open>\<open>10\<close> is a semicategory\<close>

lemma (in \<Z>) semicategory_smc_10: 
  assumes "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" 
  shows "semicategory \<alpha> (smc_10 \<aa>)"
proof(intro semicategoryI)
  show "vfsequence (smc_10 \<aa>)" 
    unfolding smc_10_def by (simp add: nat_omega_simps)
  show "vcard (smc_10 \<aa>) = 5\<^sub>\<nat>" 
    unfolding smc_10_def by (simp add: nat_omega_simps)
  show "digraph \<alpha> (smc_dg (smc_10 \<aa>))"
    unfolding smc_dg_smc_10 by (rule digraph_dg_10[OF assms])
qed (auto simp: smc_10_components smc_10_is_arr_iff vsubset_vsingleton_leftI)


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma smc_10_is_arr_iff: "\<FF> : \<AA> \<mapsto>\<^bsub>smc_10 \<aa>\<^esub> \<BB> \<longleftrightarrow> False"
  unfolding is_arr_def smc_10_components by simp



subsection\<open>\<open>1\<close>: semicategory with one object and one arrow\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition smc_1 :: "V \<Rightarrow> V \<Rightarrow> V"
  where "smc_1 \<aa> \<ff> = 
    [set {\<aa>}, set {\<ff>}, set {\<langle>\<ff>, \<aa>\<rangle>}, set {\<langle>\<ff>, \<aa>\<rangle>}, set {\<langle>[\<ff>, \<ff>]\<^sub>\<circ>, \<ff>\<rangle>}]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smc_1_components:
  shows "smc_1 \<aa> \<ff>\<lparr>Obj\<rparr> = set {\<aa>}"
    and "smc_1 \<aa> \<ff>\<lparr>Arr\<rparr> = set {\<ff>}"
    and "smc_1 \<aa> \<ff>\<lparr>Dom\<rparr> = set {\<langle>\<ff>, \<aa>\<rangle>}"
    and "smc_1 \<aa> \<ff>\<lparr>Cod\<rparr> = set {\<langle>\<ff>, \<aa>\<rangle>}"
    and "smc_1 \<aa> \<ff>\<lparr>Comp\<rparr> = set {\<langle>[\<ff>, \<ff>]\<^sub>\<circ>, \<ff>\<rangle>}"
  unfolding smc_1_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma dg_smc_1: "smc_dg (smc_1 \<aa> \<ff>) = dg_1 \<aa> \<ff>"
  unfolding smc_dg_def smc_1_def dg_1_def dg_field_simps
  by (simp add: nat_omega_simps)

lemmas_with [folded dg_smc_1, unfolded slicing_simps]: 
  smc_1_is_arrI = dg_1_is_arrI
  and smc_1_is_arrD = dg_1_is_arrD
  and smc_1_is_arrE = dg_1_is_arrE
  and smc_1_is_arr_iff = dg_1_is_arr_iff


subsubsection\<open>Composition\<close>

lemma smc_1_Comp_app[simp]: "\<ff> \<circ>\<^sub>A\<^bsub>smc_1 \<aa> \<ff>\<^esub> \<ff> = \<ff>"
  unfolding smc_1_components by simp


subsubsection\<open>\<open>1\<close> is a semicategory\<close>

lemma (in \<Z>) semicategory_smc_1: 
  assumes "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" and "\<ff> \<in>\<^sub>\<circ> Vset \<alpha>" 
  shows "semicategory \<alpha> (smc_1 \<aa> \<ff>)"
proof(intro semicategoryI, unfold dg_smc_1)
  show "vfsequence (smc_1 \<aa> \<ff>)"
    unfolding smc_1_def by (simp add: nat_omega_simps)
  show "vcard (smc_1 \<aa> \<ff>) = 5\<^sub>\<nat>"
    unfolding smc_1_def by (simp add: nat_omega_simps)
qed 
  (
    auto simp: 
      assms
      digraph_dg_1 
      smc_1_is_arr_iff 
      smc_1_components  
      vsubset_vsingleton_leftI
  )

text\<open>\newpage\<close>

end