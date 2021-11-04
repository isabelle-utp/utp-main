(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Simple digraphs\<close>
theory CZH_DG_Simple
  imports CZH_DG_DGHM
begin



subsection\<open>Background\<close>


text\<open>
The section presents a variety of simple digraphs, such as the empty digraph \<open>0\<close>
and a digraph with one object and one arrow \<open>1\<close>. All of the entities 
presented in this section are generalizations of certain simple categories,
whose definitions can be found in \cite{mac_lane_categories_2010}.
\<close>



subsection\<open>Empty digraph \<open>0\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-2 in \cite{mac_lane_categories_2010}.\<close>

definition dg_0 :: V
  where "dg_0 = [0, 0, 0, 0]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dg_0_components:
  shows "dg_0\<lparr>Obj\<rparr> = 0"
    and "dg_0\<lparr>Arr\<rparr> = 0"
    and "dg_0\<lparr>Dom\<rparr> = 0"
    and "dg_0\<lparr>Cod\<rparr> = 0"
  unfolding dg_0_def dg_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>\<open>0\<close> is a digraph\<close>

lemma (in \<Z>) digraph_dg_0: "digraph \<alpha> dg_0"
proof(intro digraphI)
  show "vfsequence dg_0" unfolding dg_0_def by (simp add: nat_omega_simps)
  show "vcard dg_0 = 4\<^sub>\<nat>" unfolding dg_0_def by (simp add: nat_omega_simps)
qed (auto simp: dg_0_components)


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma dg_0_is_arr_iff[simp]: "\<FF> : \<AA> \<mapsto>\<^bsub>dg_0\<^esub> \<BB> \<longleftrightarrow> False" 
  by (rule iffI; (elim is_arrE)?) (auto simp: dg_0_components)


subsubsection\<open>A digraph without objects is empty\<close>

lemma (in digraph) dg_dg_0_if_Obj_0:
  assumes "\<CC>\<lparr>Obj\<rparr> = 0"
  shows "\<CC> = dg_0"
  by (rule dg_eqI[of \<alpha>])
    (
      auto simp:
        dg_cs_intros
        assms
        digraph_dg_0 
        dg_0_components 
        dg_Arr_vempty_if_Obj_vempty 
        dg_Cod_vempty_if_Arr_vempty 
        dg_Dom_vempty_if_Arr_vempty
    )



subsection\<open>Empty digraph homomorphism\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition dghm_0 :: "V \<Rightarrow> V"
  where "dghm_0 \<AA> = [0, 0, dg_0, \<AA>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dghm_0_components:
  shows "dghm_0 \<AA>\<lparr>ObjMap\<rparr> = 0"
    and "dghm_0 \<AA>\<lparr>ArrMap\<rparr> = 0"
    and "dghm_0 \<AA>\<lparr>HomDom\<rparr> = dg_0"
    and "dghm_0 \<AA>\<lparr>HomCod\<rparr> = \<AA>"
  unfolding dghm_0_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Empty digraph homomorphism is a faithful digraph homomorphism\<close>

lemma (in \<Z>) dghm_0_is_dghm: 
  assumes "digraph \<alpha> \<AA>"
  shows "dghm_0 \<AA> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<AA>"
proof(rule is_ft_dghmI)
  show "dghm_0 \<AA> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA>"
  proof(rule is_dghmI)
    show "vfsequence (dghm_0 \<AA>)" unfolding dghm_0_def by simp
    show "vcard (dghm_0 \<AA>) = 4\<^sub>\<nat>"
      unfolding dghm_0_def by (simp add: nat_omega_simps)
  qed (auto simp: assms digraph_dg_0 dghm_0_components dg_0_components)
qed (auto simp: dg_0_components dghm_0_components)



subsection\<open>\<open>10\<close>: digraph with one object and no arrows\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition dg_10 :: "V \<Rightarrow> V"
  where "dg_10 \<aa> = [set {\<aa>}, 0, 0, 0]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dg_10_components:
  shows "dg_10 \<aa>\<lparr>Obj\<rparr> = set {\<aa>}"
    and "dg_10 \<aa>\<lparr>Arr\<rparr> = 0"
    and "dg_10 \<aa>\<lparr>Dom\<rparr> = 0"
    and "dg_10 \<aa>\<lparr>Cod\<rparr> = 0"
  unfolding dg_10_def dg_field_simps by (auto simp: nat_omega_simps)


subsubsection\<open>\<open>10\<close> is a digraph\<close>

lemma (in \<Z>) digraph_dg_10: 
  assumes "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" 
  shows "digraph \<alpha> (dg_10 \<aa>)"
proof(intro digraphI)
  show "vfsequence (dg_10 \<aa>)" unfolding dg_10_def by (simp add: nat_omega_simps)
  show "vcard (dg_10 \<aa>) = 4\<^sub>\<nat>" unfolding dg_10_def by (simp add: nat_omega_simps)
  show "(\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B. Hom (dg_10 \<aa>) a' b') \<in>\<^sub>\<circ> Vset \<alpha>" for A B
  proof-
    have "(\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B. Hom (dg_10 \<aa>) a' b') \<subseteq>\<^sub>\<circ> dg_10 \<aa>\<lparr>Arr\<rparr>" by auto
    moreover have "dg_10 \<aa>\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> 0" unfolding dg_10_components by auto
    ultimately show ?thesis using vempty_is_zet vsubset_in_VsetI by presburger
  qed
qed (auto simp: assms dg_10_components vsubset_vsingleton_leftI)


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma dg_10_is_arr_iff: "\<FF> : \<AA> \<mapsto>\<^bsub>dg_10 \<aa>\<^esub> \<BB> \<longleftrightarrow> False"
  unfolding is_arr_def dg_10_components by simp



subsection\<open>\<open>1\<close>: digraph with one object and one arrow\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition dg_1 :: "V \<Rightarrow> V \<Rightarrow> V"
  where "dg_1 \<aa> \<ff> = [set {\<aa>}, set {\<ff>}, set {\<langle>\<ff>, \<aa>\<rangle>}, set {\<langle>\<ff>, \<aa>\<rangle>}]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dg_1_components:
  shows "dg_1 \<aa> \<ff>\<lparr>Obj\<rparr> = set {\<aa>}"
    and "dg_1 \<aa> \<ff>\<lparr>Arr\<rparr> = set {\<ff>}"
    and "dg_1 \<aa> \<ff>\<lparr>Dom\<rparr> = set {\<langle>\<ff>, \<aa>\<rangle>}"
    and "dg_1 \<aa> \<ff>\<lparr>Cod\<rparr> = set {\<langle>\<ff>, \<aa>\<rangle>}"
  unfolding dg_1_def dg_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>\<open>1\<close> is a digraph\<close>

lemma (in \<Z>) digraph_dg_1: 
  assumes "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" and "\<ff> \<in>\<^sub>\<circ> Vset \<alpha>" 
  shows "digraph \<alpha> (dg_1 \<aa> \<ff>)"
proof(intro digraphI)
  show "vfsequence (dg_1 \<aa> \<ff>)" unfolding dg_1_def by (simp add: nat_omega_simps)
  show "vcard (dg_1 \<aa> \<ff>) = 4\<^sub>\<nat>" unfolding dg_1_def by (simp add: nat_omega_simps)
  show "(\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B. Hom (dg_1 \<aa> \<ff>) a' b') \<in>\<^sub>\<circ> Vset \<alpha>" for A B
  proof-
    have "(\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B. Hom (dg_1 \<aa> \<ff>) a' b') \<subseteq>\<^sub>\<circ> dg_1 \<aa> \<ff>\<lparr>Arr\<rparr>" by auto
    moreover have "dg_1 \<aa> \<ff>\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> set {\<ff>}" unfolding dg_1_components by auto
    moreover from assms(2) have "set {\<ff>} \<in>\<^sub>\<circ> Vset \<alpha>" 
      by (simp add: Limit_vsingleton_in_VsetI)
    ultimately show ?thesis 
      unfolding dg_1_components by (auto simp: vsubset_in_VsetI)
  qed
qed (auto simp: assms dg_1_components vsubset_vsingleton_leftI)


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma dg_1_is_arrI:
  assumes "a = \<aa>" and "b = \<aa>" and "f = \<ff>" 
  shows "f : a \<mapsto>\<^bsub>dg_1 \<aa> \<ff>\<^esub> b"
  using assms by (intro is_arrI) (auto simp: dg_1_components)

lemma dg_1_is_arrD:
  assumes "f : a \<mapsto>\<^bsub>dg_1 \<aa> \<ff>\<^esub> b"
  shows "a = \<aa>" and "b = \<aa>" and "f = \<ff>" 
  using assms by (all\<open>elim is_arrE\<close>) (auto simp: dg_1_components)

lemma dg_1_is_arrE:
  assumes "f : a \<mapsto>\<^bsub>dg_1 \<aa> \<ff>\<^esub> b"
  obtains "a = \<aa>" and "b = \<aa>" and "f = \<ff>" 
  using assms by (elim is_arrE) (force simp: dg_1_components)

lemma dg_1_is_arr_iff: "f : a \<mapsto>\<^bsub>dg_1 \<aa> \<ff>\<^esub> b \<longleftrightarrow> (a = \<aa> \<and> b = \<aa> \<and> f = \<ff>)" 
  by (rule iffI; (elim is_arrE)?) 
    (auto simp: dg_1_components intro: dg_1_is_arrI)

text\<open>\newpage\<close>

end