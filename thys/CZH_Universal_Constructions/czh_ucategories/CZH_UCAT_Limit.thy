(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Limits\<close>
theory CZH_UCAT_Limit
  imports 
    CZH_UCAT_Universal
    CZH_Elementary_Categories.CZH_ECAT_Discrete 
    CZH_Elementary_Categories.CZH_ECAT_SS
    CZH_Elementary_Categories.CZH_ECAT_Parallel
begin



subsection\<open>Background\<close>

named_theorems cat_lim_cs_simps
named_theorems cat_lim_cs_intros



subsection\<open>Cone and cocone\<close>


text\<open>
In the context of this work, the concept of a cone corresponds to that of a cone
to the base of a functor from a vertex, as defined in Chapter III-4 in
\cite{mac_lane_categories_2010}; the concept of a cocone corresponds to that
of a cone from the base of a functor to a vertex, as defined in Chapter III-3
in \cite{mac_lane_categories_2010}.

In this body of work, only limits and colimits of functors with tiny maps 
are considered. The definitions of a cone and a cocone also reflect this.
However, this restriction may be removed in the future.
\<close>

(*TODO: remove the size limitation; see TODO in the next subsection*)
locale is_cat_cone = is_tm_ntcf \<alpha> \<JJ> \<CC> \<open>cf_const \<JJ> \<CC> c\<close> \<FF> \<NN> for \<alpha> c \<JJ> \<CC> \<FF> \<NN> +
  assumes cat_cone_obj[cat_lim_cs_intros]: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"

syntax "_is_cat_cone" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_cone \<alpha> c \<JJ> \<CC> \<FF> \<NN>"

locale is_cat_cocone = is_tm_ntcf \<alpha> \<JJ> \<CC> \<FF> \<open>cf_const \<JJ> \<CC> c\<close> \<NN> for \<alpha> c \<JJ> \<CC> \<FF> \<NN> +
  assumes cat_cocone_obj[cat_lim_cs_intros]: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"

syntax "_is_cat_cocone" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_cocone \<alpha> c \<JJ> \<CC> \<FF> \<NN>"


text\<open>Rules.\<close>

lemma (in is_cat_cone) is_cat_cone_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "c' = c" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "\<NN> : c' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_cone_axioms)

mk_ide rf is_cat_cone_def[unfolded is_cat_cone_axioms_def]
  |intro is_cat_coneI|
  |dest is_cat_coneD[dest!]|
  |elim is_cat_coneE[elim!]|

lemma (in is_cat_cone) is_cat_coneD'[cat_lim_cs_intros]:
  assumes "c' = cf_const \<JJ> \<CC> c"
  shows "\<NN> : c' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  unfolding assms by (cs_concl cs_intro: cat_small_cs_intros)

lemmas [cat_lim_cs_intros] = is_cat_cone.is_cat_coneD'

lemma (in is_cat_cocone) is_cat_cocone_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "c' = c" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "\<NN> : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_cocone_axioms)

mk_ide rf is_cat_cocone_def[unfolded is_cat_cocone_axioms_def]
  |intro is_cat_coconeI|
  |dest is_cat_coconeD[dest!]|
  |elim is_cat_coconeE[elim!]|

lemma (in is_cat_cocone) is_cat_coconeD'[cat_lim_cs_intros]:
  assumes "c' = cf_const \<JJ> \<CC> c"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m c' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  unfolding assms by (cs_concl cs_intro: cat_small_cs_intros)

lemmas [cat_lim_cs_intros] = is_cat_cocone.is_cat_coconeD'


text\<open>Duality.\<close>

lemma (in is_cat_cone) is_cat_cocone_op:
  "op_ntcf \<NN> : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_coconeI)
    (cs_concl cs_simp: cat_op_simps cs_intro: cat_lim_cs_intros cat_op_intros)+

lemma (in is_cat_cone) is_cat_cocone_op'[cat_op_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>" and "\<FF>' = op_cf \<FF>"
  shows "op_ntcf \<NN> : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_cocone_op)

lemmas [cat_op_intros] = is_cat_cone.is_cat_cocone_op'

lemma (in is_cat_cocone) is_cat_cone_op:
  "op_ntcf \<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_coneI)
    (cs_concl cs_simp: cat_op_simps cs_intro: cat_lim_cs_intros cat_op_intros)

lemma (in is_cat_cocone) is_cat_cone_op'[cat_op_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>" and "\<FF>' = op_cf \<FF>"
  shows "op_ntcf \<NN> : c <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_cone_op)

lemmas [cat_op_intros] = is_cat_cocone.is_cat_cone_op'


text\<open>Elementary properties.\<close>

lemma (in is_cat_cone) cat_cone_LArr_app_is_arr: 
  assumes "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
  shows "\<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> : c \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>"
proof-
  from assms have [simp]: "cf_const \<JJ> \<CC> c\<lparr>ObjMap\<rparr>\<lparr>j\<rparr> = c"
    by (cs_concl cs_simp: cat_cs_simps)
  from ntcf_NTMap_is_arr[OF assms] show ?thesis by simp 
qed

lemma (in is_cat_cone) cat_cone_LArr_app_is_arr'[cat_lim_cs_intros]: 
  assumes "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" and "\<FF>j = \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>"
  shows "\<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> : c \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>j"
  using assms(1) unfolding assms(2) by (rule cat_cone_LArr_app_is_arr)

lemmas [cat_lim_cs_intros] = is_cat_cone.cat_cone_LArr_app_is_arr'

lemma (in is_cat_cocone) cat_cocone_LArr_app_is_arr: 
  assumes "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
  shows "\<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> c"
proof-
  from assms have [simp]: "cf_const \<JJ> \<CC> c\<lparr>ObjMap\<rparr>\<lparr>j\<rparr> = c"
    by (cs_concl cs_simp: cat_cs_simps)
  from ntcf_NTMap_is_arr[OF assms] show ?thesis by simp 
qed

lemma (in is_cat_cocone) cat_cocone_LArr_app_is_arr'[cat_lim_cs_intros]: 
  assumes "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" and "\<FF>j = \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>"
  shows "\<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> : \<FF>j \<mapsto>\<^bsub>\<CC>\<^esub> c"
  using assms(1) unfolding assms(2) by (rule cat_cocone_LArr_app_is_arr)

lemmas [cat_lim_cs_intros] = is_cat_cocone.cat_cocone_LArr_app_is_arr'

lemma (in is_cat_cone) cat_cone_Comp_commute[cat_lim_cs_simps]:
  assumes "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b"
  shows "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
  using ntcf_Comp_commute[symmetric, OF assms] assms 
  by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemmas [cat_lim_cs_simps] = is_cat_cone.cat_cone_Comp_commute

lemma (in is_cat_cocone) cat_cocone_Comp_commute[cat_lim_cs_simps]:
  assumes "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b"
  shows "\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
  using ntcf_Comp_commute[OF assms] assms 
  by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemmas [cat_lim_cs_simps] = is_cat_cocone.cat_cocone_Comp_commute


text\<open>Utilities/helper lemmas.\<close>

lemma (in is_cat_cone) helper_cat_cone_ntcf_vcomp_Comp:
  assumes "\<NN>' : c' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "f' : c' \<mapsto>\<^bsub>\<CC>\<^esub> c" 
    and "\<NN>' = \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'" 
    and "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
  shows "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
proof-
  from assms(3) have "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = (\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
    by simp
  from this assms(1,2,4) show "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
    by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma (in is_cat_cone) helper_cat_cone_Comp_ntcf_vcomp:
  assumes "\<NN>' : c' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "f' : c' \<mapsto>\<^bsub>\<CC>\<^esub> c" 
    and "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr> \<Longrightarrow> \<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'" 
  shows "\<NN>' = \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
proof-
  interpret \<NN>': is_cat_cone \<alpha> c' \<JJ> \<CC> \<FF> \<NN>' by (rule assms(1))
  show ?thesis
  proof(rule ntcf_eqI[OF \<NN>'.is_ntcf_axioms])
    from assms(2) show 
      "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f' : cf_const \<JJ> \<CC> c' \<mapsto>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    show "\<NN>'\<lparr>NTMap\<rparr> = (\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold cat_cs_simps)
      show "vsv ((\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>)"
        by (cs_concl cs_intro: cat_cs_intros)
      from assms show "\<JJ>\<lparr>Obj\<rparr> = \<D>\<^sub>\<circ> ((\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>)"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      fix j assume prems': "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
      with assms(1,2) show "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = (\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps assms(3) cs_intro: cat_cs_intros)
    qed auto
  qed simp_all
qed

lemma (in is_cat_cone) helper_cat_cone_Comp_ntcf_vcomp_iff:
  assumes "\<NN>' : c' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "f' : c' \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> \<NN>' = \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f' \<longleftrightarrow>
    f' : c' \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> (\<forall>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f')"
  using 
    helper_cat_cone_ntcf_vcomp_Comp[OF assms]
    helper_cat_cone_Comp_ntcf_vcomp[OF assms]
  by (intro iffI; elim conjE; intro conjI) metis+

lemma (in is_cat_cocone) helper_cat_cocone_ntcf_vcomp_Comp:
  assumes "\<NN>' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> c'" 
    and "\<NN>' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>" 
    and "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
  shows "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
proof-
  interpret \<NN>': is_cat_cocone \<alpha> c' \<JJ> \<CC> \<FF> \<NN>' by (rule assms(1))
  from assms(3) have "op_ntcf \<NN>' = op_ntcf (ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)" by simp
  from this assms(2) have op_\<NN>':
    "op_ntcf \<NN>' = op_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f'"
    by (cs_prems cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros)
  have "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f'"
    by 
      (
        rule is_cat_cone.helper_cat_cone_ntcf_vcomp_Comp[
          OF is_cat_cone_op \<NN>'.is_cat_cone_op, 
          unfolded cat_op_simps, 
          OF assms(2) op_\<NN>' assms(4)
          ]
      )
  from this assms(2,4) show "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
    by (cs_prems cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
qed

lemma (in is_cat_cocone) helper_cat_cocone_Comp_ntcf_vcomp:
  assumes "\<NN>' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> c'" 
    and "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr> \<Longrightarrow> \<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>" 
  shows "\<NN>' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>"
proof-
  interpret \<NN>': is_cat_cocone \<alpha> c' \<JJ> \<CC> \<FF> \<NN>' by (rule assms(1))
  from assms(2) have \<NN>'j: "\<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f'"
    if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
    using that
    unfolding assms(3)[OF that] 
    by (cs_concl cs_simp: cat_op_simps cat_cs_simps cs_intro: cat_cs_intros)
  have op_\<NN>': 
    "op_ntcf \<NN>' = op_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f'"
    by 
      (
        rule is_cat_cone.helper_cat_cone_Comp_ntcf_vcomp[
          OF is_cat_cone_op \<NN>'.is_cat_cone_op,
          unfolded cat_op_simps, 
          OF assms(2) \<NN>'j, 
          simplified
          ]
      )
  from assms(2) show "\<NN>' = (ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)"
    by 
      (
        cs_concl 
          cs_simp: 
            cat_op_simps op_\<NN>' eq_op_ntcf_iff[symmetric, OF \<NN>'.is_ntcf_axioms]
          cs_intro: cat_cs_intros
      )
qed

lemma (in is_cat_cocone) helper_cat_cocone_Comp_ntcf_vcomp_iff:
  assumes "\<NN>' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e c' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> c' \<and> \<NN>' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> \<longleftrightarrow>
    f' : c \<mapsto>\<^bsub>\<CC>\<^esub> c' \<and> (\<forall>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<NN>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>)"
  using 
    helper_cat_cocone_ntcf_vcomp_Comp[OF assms]
    helper_cat_cocone_Comp_ntcf_vcomp[OF assms]
  by (intro iffI; elim conjE; intro conjI) metis+



subsection\<open>Limit and colimit\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The concept of a limit is introduced in Chapter III-4 in
\cite{mac_lane_categories_2010}; the concept of a colimit is introduced in
Chapter III-3 in \cite{mac_lane_categories_2010}.
\<close>

(*TODO: remove the size limitation*)
locale is_cat_limit = is_cat_cone \<alpha> r \<JJ> \<CC> \<FF> u for \<alpha> \<JJ> \<CC> \<FF> r u +
  assumes cat_lim_ua_fo: 
    "universal_arrow_fo (\<Delta>\<^sub>C \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u)"

syntax "_is_cat_limit" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_limit \<alpha> \<JJ> \<CC> \<FF> r u"

locale is_cat_colimit = is_cat_cocone \<alpha> r \<JJ> \<CC> \<FF> u for \<alpha> \<JJ> \<CC> \<FF> r u +
  assumes cat_colim_ua_fo: "universal_arrow_fo 
    (\<Delta>\<^sub>C \<alpha> (op_cat \<JJ>) (op_cat \<CC>)) (cf_map \<FF>) r (ntcf_arrow (op_ntcf u))"

syntax "_is_cat_colimit" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r u"


text\<open>Rules.\<close>

lemma (in is_cat_limit) is_cat_limit_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "r' = r" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "u : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_limit_axioms)

mk_ide rf is_cat_limit_def[unfolded is_cat_limit_axioms_def]
  |intro is_cat_limitI|
  |dest is_cat_limitD[dest]|
  |elim is_cat_limitE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_limitD(1)

lemma (in is_cat_colimit) is_cat_colimit_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "r' = r" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "u : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_colimit_axioms)

mk_ide rf is_cat_colimit_def[unfolded is_cat_colimit_axioms_def]
  |intro is_cat_colimitI|
  |dest is_cat_colimitD[dest]|
  |elim is_cat_colimitE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_colimitD(1)


text\<open>Duality\<close>

lemma (in is_cat_limit) is_cat_colimit_op:
  "op_ntcf u : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  using cat_lim_ua_fo
  by (intro is_cat_colimitI)
    (cs_concl cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros)

lemma (in is_cat_limit) is_cat_colimit_op'[cat_op_intros]:
  assumes "\<FF>' = op_cf \<FF>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>"
  shows "op_ntcf u : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_colimit_op)

lemmas [cat_op_intros] = is_cat_limit.is_cat_colimit_op'

lemma (in is_cat_colimit) is_cat_limit_op:
  "op_ntcf u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  using cat_colim_ua_fo
  by (intro is_cat_limitI)
    (cs_concl cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros)

lemma (in is_cat_colimit) is_cat_colimit_op'[cat_op_intros]:
  assumes "\<FF>' = op_cf \<FF>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>"
  shows "op_ntcf u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_limit_op)

lemmas [cat_op_intros] = is_cat_colimit.is_cat_colimit_op'


text\<open>Elementary properties of limits and colimits.\<close>

sublocale is_cat_limit \<subseteq> \<Delta>: is_functor \<alpha> \<CC> \<open>cat_Funct \<alpha> \<JJ> \<CC>\<close> \<open>\<Delta>\<^sub>C \<alpha> \<JJ> \<CC>\<close>
  by (cs_concl cs_intro: cat_cs_intros cat_small_cs_intros)

sublocale is_cat_colimit \<subseteq> \<Delta>: is_functor 
  \<alpha> \<open>op_cat \<CC>\<close> \<open>cat_Funct \<alpha> (op_cat \<JJ>) (op_cat \<CC>)\<close> \<open>\<Delta>\<^sub>C \<alpha> (op_cat \<JJ>) (op_cat \<CC>)\<close>
  by (cs_concl cs_intro: cat_small_cs_intros cat_cs_intros cat_op_intros)


subsubsection\<open>Universal property\<close>

lemma is_cat_limitI':
  assumes "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<And>u' r'. \<lbrakk> u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<rbrakk> \<Longrightarrow> 
      \<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
  shows "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_cat_limitI is_functor.universal_arrow_foI)
  interpret u: is_cat_cone \<alpha> r \<JJ> \<CC> \<FF> u by (rule assms(1))
  show "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (cs_concl cs_intro: cat_lim_cs_intros)
  show "\<Delta>\<^sub>C \<alpha> \<JJ> \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Funct \<alpha> \<JJ> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros cat_small_cs_intros)
  show "ntcf_arrow u : \<Delta>\<^sub>C \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>cat_Funct \<alpha> \<JJ> \<CC>\<^esub> cf_map \<FF>"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_lim_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
      )
  fix r' u' assume prems: 
    "r' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "u' : \<Delta>\<^sub>C \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<mapsto>\<^bsub>cat_Funct \<alpha> \<JJ> \<CC>\<^esub> cf_map \<FF>"
  note u' = cat_Funct_is_arrD[OF prems(2)]
  from u'(1) prems(1) have u'_is_tm_ntcf:
    "ntcf_of_ntcf_arrow \<JJ> \<CC> u' : cf_const \<JJ> \<CC> r' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    by 
      (
        cs_prems 
          cs_simp: cat_cs_simps cat_small_cs_simps cat_FUNCT_cs_simps 
          cs_intro: cat_cs_intros
      )
  from this prems(1) have u'_is_cat_cone: 
    "ntcf_of_ntcf_arrow \<JJ> \<CC> u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (intro is_cat_coneI)
  interpret u': is_cat_cone \<alpha> r' \<JJ> \<CC> \<FF> \<open>ntcf_of_ntcf_arrow \<JJ> \<CC> u'\<close>
    by (rule u'_is_cat_cone)
  from assms(2)[OF u'_is_cat_cone] obtain f' where f': "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
    and u'_def: "ntcf_of_ntcf_arrow \<JJ> \<CC> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
    and unique: "\<And>f''.
      \<lbrakk>
        f'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r; 
        ntcf_of_ntcf_arrow \<JJ> \<CC> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f''
      \<rbrakk> \<Longrightarrow> f'' = f'"
    by (meson prems(1))
  from u'_def have u'_NTMap_app:
    "ntcf_of_ntcf_arrow \<JJ> \<CC> u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = (u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
    if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j 
    by simp
  have u'_NTMap_app: "u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = u\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
    if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j 
    using u'_NTMap_app[OF that] that f'
    by (cs_prems cs_simp: cat_cs_simps cat_FUNCT_cs_simps cs_intro: cat_cs_intros)
  show "\<exists>!f'.
    f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and>
    u' = umap_fo (\<Delta>\<^sub>C \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
  proof(intro ex1I conjI; (elim conjE)?)
    show "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r" by (rule f')
    have u'_def'[symmetric, cat_cs_simps]: 
      "ntcf_of_ntcf_arrow \<JJ> \<CC> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
    proof(rule ntcf_eqI)
      from u'_is_tm_ntcf show 
        "ntcf_of_ntcf_arrow \<JJ> \<CC> u' : cf_const \<JJ> \<CC> r' \<mapsto>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_intro: cat_small_cs_intros)
      from f' show 
        "u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f' : cf_const \<JJ> \<CC> r' \<mapsto>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      show 
        "ntcf_of_ntcf_arrow \<JJ> \<CC> u'\<lparr>NTMap\<rparr> = (u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>"
      proof(rule vsv_eqI)
        from f' show "\<D>\<^sub>\<circ> (ntcf_of_ntcf_arrow \<JJ> \<CC> u'\<lparr>NTMap\<rparr>) = 
          \<D>\<^sub>\<circ> ((u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>)"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)    
        show "ntcf_of_ntcf_arrow \<JJ> \<CC> u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = 
          (u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
          if "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (ntcf_of_ntcf_arrow \<JJ> \<CC> u'\<lparr>NTMap\<rparr>)" for a
        proof-
          from that have "a \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" by (cs_prems cs_simp: cat_cs_simps)    
          with f' show 
            "ntcf_of_ntcf_arrow \<JJ> \<CC> u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
              (u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
            by 
              (
                cs_concl 
                  cs_simp: cat_cs_simps cat_FUNCT_cs_simps u'_NTMap_app 
                  cs_intro: cat_cs_intros
              )
        qed
      qed (auto intro: cat_cs_intros)
    qed simp_all
    from f' u'(1) show 
      "u' = umap_fo (\<Delta>\<^sub>C \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
      by (subst u'(2))
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_small_cs_intros
        )
    fix f'' assume prems': 
      "f'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"
      "u' = umap_fo (\<Delta>\<^sub>C \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f''\<rparr>"  
    from prems'(2,1) u'(1) have 
      "ntcf_of_ntcf_arrow \<JJ> \<CC> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f''"
      by (subst (asm) u'(2))
        (
          cs_prems 
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from unique[OF prems'(1) this] show "f'' = f'" .
  qed
qed (intro assms)+

lemma (in is_cat_limit) cat_lim_unique_cone:
  assumes "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
  shows "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
proof-
  interpret u': is_cat_cone \<alpha> r' \<JJ> \<CC> \<FF> u' by (rule assms(1))
  have "ntcf_arrow u' : \<Delta>\<^sub>C \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<mapsto>\<^bsub>cat_Funct \<alpha> \<JJ> \<CC>\<^esub> cf_map \<FF>"
    by 
      (
        cs_concl 
          cs_intro: cat_lim_cs_intros cat_FUNCT_cs_intros cs_simp: cat_cs_simps
      )
  from \<Delta>.universal_arrow_foD(3)[OF cat_lim_ua_fo u'.cat_cone_obj this] obtain f'
    where f': "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r" 
      and u': "ntcf_arrow u' =
      umap_fo (\<Delta>\<^sub>C \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
      and unique:
        "\<lbrakk>
          f'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r;
          ntcf_arrow u' =
            umap_fo (\<Delta>\<^sub>C \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f''\<rparr>
         \<rbrakk> \<Longrightarrow> f'' = f'"
    for f''
    by metis
  show "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
  proof(intro ex1I conjI; (elim conjE)?)
    show "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r" by (rule f')
    with u' show "u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
      by 
        (
          cs_prems 
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_small_cs_intros
        )
    fix f'' assume prems: "f'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r"  "u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f''"
    from prems(1) have "ntcf_arrow u' =
      umap_fo (\<Delta>\<^sub>C \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f''\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps prems(2)[symmetric] 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_small_cs_intros
        )
    from prems(1) this show "f'' = f'" by (intro unique)
  qed
qed  

lemma (in is_cat_limit) cat_lim_unique_cone':
  assumes "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows 
    "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> (\<forall>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = u\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f')"
  by (fold helper_cat_cone_Comp_ntcf_vcomp_iff[OF assms(1)])
    (intro cat_lim_unique_cone assms)

lemma (in is_cat_limit) cat_lim_unique:
  assumes "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
  by (intro cat_lim_unique_cone[OF is_cat_limitD(1)[OF assms]])

lemma (in is_cat_limit) cat_lim_unique':
  assumes "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows 
    "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> r \<and> (\<forall>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = u\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f')"
  by (intro cat_lim_unique_cone'[OF is_cat_limitD(1)[OF assms]])

lemma (in is_cat_colimit) cat_colim_unique_cocone:
  assumes "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
proof-
  interpret u': is_cat_cocone \<alpha> r' \<JJ> \<CC> \<FF> u' by (rule assms(1))
  from u'.cat_cocone_obj have op_r': "r' \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
    unfolding cat_op_simps by simp
  from 
    is_cat_limit.cat_lim_unique_cone[
      OF is_cat_limit_op u'.is_cat_cone_op, folded op_ntcf_ntcf_const
      ]
  obtain f' where f': "f' : r' \<mapsto>\<^bsub>op_cat \<CC>\<^esub> r"
    and [cat_cs_simps]: 
      "op_ntcf u' = op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf (ntcf_const \<JJ> \<CC> f')"
    and unique: 
      "\<lbrakk>
        f'' : r' \<mapsto>\<^bsub>op_cat \<CC>\<^esub> r;
        op_ntcf u' = op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf (ntcf_const \<JJ> \<CC> f'')
       \<rbrakk> \<Longrightarrow> f'' = f'" 
    for f''
    by metis
  show ?thesis
  proof(intro ex1I conjI; (elim conjE)?)
    from f' show f': "f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r'" unfolding cat_op_simps by simp
    show "u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
      by (rule eq_op_ntcf_iff[THEN iffD1], insert f')
        (cs_concl cs_intro: cat_cs_intros cs_simp: cat_cs_simps cat_op_simps)+
    fix f'' assume prems: "f'' : r \<mapsto>\<^bsub>\<CC>\<^esub> r'" "u' = ntcf_const \<JJ> \<CC> f'' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
    from prems(1) have "f'' : r' \<mapsto>\<^bsub>op_cat \<CC>\<^esub> r" unfolding cat_op_simps by simp
    moreover from prems(1) have 
      "op_ntcf u' = op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf (ntcf_const \<JJ> \<CC> f'')"
      unfolding prems(2)
      by (cs_concl cs_intro: cat_cs_intros cs_simp: cat_cs_simps cat_op_simps)
    ultimately show "f'' = f'" by (rule unique)
  qed
qed

lemma (in is_cat_colimit) cat_colim_unique_cocone':
  assumes "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows 
    "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and> (\<forall>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> u\<lparr>NTMap\<rparr>\<lparr>j\<rparr>)"
  by (fold helper_cat_cocone_Comp_ntcf_vcomp_iff[OF assms(1)])
    (intro cat_colim_unique_cocone assms)

lemma (in is_cat_colimit) cat_colim_unique:
  assumes "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and> u' = ntcf_const \<JJ> \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
  by (intro cat_colim_unique_cocone[OF is_cat_colimitD(1)[OF assms]])

lemma (in is_cat_colimit) cat_colim_unique':
  assumes "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows
    "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<CC>\<^esub> r' \<and> (\<forall>j\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> u\<lparr>NTMap\<rparr>\<lparr>j\<rparr>)"
proof-
  interpret u': is_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r' u' by (rule assms(1))
  show ?thesis
    by (fold helper_cat_cocone_Comp_ntcf_vcomp_iff[OF u'.is_cat_cocone_axioms])
      (intro cat_colim_unique assms)
qed

lemma cat_lim_ex_is_arr_isomorphism:
  assumes "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r" and "u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
proof-
  interpret u: is_cat_limit \<alpha> \<JJ> \<CC> \<FF> r u by (rule assms(1))
  interpret u': is_cat_limit \<alpha> \<JJ> \<CC> \<FF> r' u' by (rule assms(2))
  obtain f where f: "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r"
    and u': "ntcf_arrow u' =
    umap_fo (\<Delta>\<^sub>C \<alpha> \<JJ> \<CC>) (cf_map \<FF>) r (ntcf_arrow u) r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
    by 
      (
        elim u.\<Delta>.cf_universal_arrow_fo_ex_is_arr_isomorphism[
          OF u.cat_lim_ua_fo u'.cat_lim_ua_fo
          ]
      )
  from f have "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r" by auto
  from u' this have "u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
    by
      (
        cs_prems
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_small_cs_simps
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_small_cs_intros
      )
  with f that show ?thesis by simp
qed

lemma cat_lim_ex_is_arr_isomorphism':
  assumes "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r" 
    and "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr> \<Longrightarrow> u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = u\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
proof-
  interpret u: is_cat_limit \<alpha> \<JJ> \<CC> \<FF> r u by (rule assms(1))
  interpret u': is_cat_limit \<alpha> \<JJ> \<CC> \<FF> r' u' by (rule assms(2))
  from assms obtain f 
    where iso_f: "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r" and u'_def: "u' = u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f"
    by (rule cat_lim_ex_is_arr_isomorphism)
  then have f: "f : r' \<mapsto>\<^bsub>\<CC>\<^esub> r" by auto
  then have "u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = u\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f" if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
    by 
      (
        intro u.helper_cat_cone_ntcf_vcomp_Comp[
          OF u'.is_cat_cone_axioms f u'_def that
          ]
      )
  with iso_f that show ?thesis by simp
qed

lemma cat_colim_ex_is_arr_isomorphism:
  assumes "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r'" and "u' = ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
proof-
  interpret u: is_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r u by (rule assms(1))
  interpret u': is_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r' u' by (rule assms(2))
  obtain f where f: "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>op_cat \<CC>\<^esub> r"
    and [cat_cs_simps]: 
      "op_ntcf u' = op_ntcf u \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f"
    by 
      (
        elim cat_lim_ex_is_arr_isomorphism[
          OF u.is_cat_limit_op u'.is_cat_limit_op
          ]
      )
  from f have iso_f: "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r'" unfolding cat_op_simps by simp
  then have f: "f : r \<mapsto>\<^bsub>\<CC>\<^esub> r'" by auto
  have "u' = ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
    by (rule eq_op_ntcf_iff[THEN iffD1], insert f)
      (cs_concl cs_intro: cat_cs_intros cs_simp: cat_cs_simps cat_op_simps)+
  from iso_f this that show ?thesis by simp
qed

lemma cat_colim_ex_is_arr_isomorphism':
  assumes "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "u' : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r' : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r'"
    and "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr> \<Longrightarrow> u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> u\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
proof-
  interpret u: is_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r u by (rule assms(1))
  interpret u': is_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r' u' by (rule assms(2))
  from assms obtain f 
    where iso_f: "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r'" and u'_def: "u' = ntcf_const \<JJ> \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F u"
    by (rule cat_colim_ex_is_arr_isomorphism)
  then have f: "f : r \<mapsto>\<^bsub>\<CC>\<^esub> r'" by auto
  then have "u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> u\<lparr>NTMap\<rparr>\<lparr>j\<rparr>" if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
    by 
      (
        intro u.helper_cat_cocone_ntcf_vcomp_Comp[
          OF u'.is_cat_cocone_axioms f u'_def that
          ]
      )
  with iso_f that show ?thesis by simp
qed



subsection\<open>Finite limit and finite colimit\<close>

locale is_cat_finite_limit = is_cat_limit \<alpha> \<JJ> \<CC> \<FF> r u + finite_category \<alpha> \<JJ>
  for \<alpha> \<JJ> \<CC> \<FF> r u

syntax "_is_cat_finite_limit" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_finite_limit \<alpha> \<JJ> \<CC> \<FF> r u"

locale is_cat_finite_colimit = is_cat_colimit \<alpha> \<JJ> \<CC> \<FF> r u + finite_category \<alpha> \<JJ>
  for \<alpha> \<JJ> \<CC> \<FF> r u

syntax "_is_cat_finite_colimit" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_finite_colimit \<alpha> \<JJ> \<CC> \<FF> r u"


text\<open>Rules.\<close>

lemma (in is_cat_finite_limit) is_cat_finite_limit_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "r' = r" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "u : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_limit_axioms)

mk_ide rf is_cat_finite_limit_def
  |intro is_cat_finite_limitI|
  |dest is_cat_finite_limitD[dest]|
  |elim is_cat_finite_limitE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_finite_limitD

lemma (in is_cat_finite_colimit) 
  is_cat_finite_colimit_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "r' = r" and "\<JJ>' = \<JJ>" and "\<CC>' = \<CC>" and "\<FF>' = \<FF>"
  shows "u : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n r' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_colimit_axioms)

mk_ide rf is_cat_finite_colimit_def[unfolded is_cat_colimit_axioms_def]
  |intro is_cat_finite_colimitI|
  |dest is_cat_finite_colimitD[dest]|
  |elim is_cat_finite_colimitE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_finite_colimitD


text\<open>Duality\<close>

lemma (in is_cat_finite_limit) is_cat_finite_colimit_op:
  "op_ntcf u : op_cf \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n r : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by 
    (
      cs_concl cs_intro:
        is_cat_finite_colimitI cat_op_intros cat_small_cs_intros
    )

lemma (in is_cat_finite_limit) is_cat_finite_colimit_op'[cat_op_intros]:
  assumes "\<FF>' = op_cf \<FF>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>"
  shows "op_ntcf u : \<FF>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n r : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_colimit_op)

lemmas [cat_op_intros] = is_cat_finite_limit.is_cat_finite_colimit_op'

lemma (in is_cat_finite_colimit) is_cat_finite_limit_op:
  "op_ntcf u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by 
    (
      cs_concl cs_intro: 
        is_cat_finite_limitI cat_op_intros cat_small_cs_intros
    )

lemma (in is_cat_finite_colimit) is_cat_finite_colimit_op'[cat_op_intros]:
  assumes "\<FF>' = op_cf \<FF>" and "\<JJ>' = op_cat \<JJ>" and "\<CC>' = op_cat \<CC>"
  shows "op_ntcf u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m\<^sub>.\<^sub>f\<^sub>i\<^sub>n \<FF>' : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_limit_op)

lemmas [cat_op_intros] = is_cat_finite_colimit.is_cat_finite_colimit_op'



subsection\<open>Product and coproduct\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The definition of the product object is a specialization of the 
definition presented in Chapter III-4 in \cite{mac_lane_categories_2010}.
In the definition presented below, the discrete category that is used in the 
definition presented in \cite{mac_lane_categories_2010} is parameterized by
an index set and the functor from the discrete category is 
parameterized by a function from the index set to the set of 
the objects of the category.
\<close>

locale is_cat_obj_prod = 
  is_cat_limit \<alpha> \<open>:\<^sub>C I\<close> \<CC> \<open>:\<rightarrow>: I A \<CC>\<close> P \<pi> + cf_discrete \<alpha> I A \<CC>
  for \<alpha> I A \<CC> P \<pi>

syntax "_is_cat_obj_prod" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_obj_prod \<alpha> I A \<CC> P \<pi>"

locale is_cat_obj_coprod = 
  is_cat_colimit \<alpha> \<open>:\<^sub>C I\<close> \<CC> \<open>:\<rightarrow>: I A \<CC>\<close> U \<pi> + cf_discrete \<alpha> I A \<CC>
  for \<alpha> I A \<CC> U \<pi>

syntax "_is_cat_obj_coprod" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_obj_coprod \<alpha> I A \<CC> U \<pi>"


text\<open>Rules.\<close>

lemma (in is_cat_obj_prod) is_cat_obj_prod_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "P' = P" and "A' = A" and "I' = I" and "\<CC>' = \<CC>" 
  shows "\<pi> : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A' : I' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_prod_axioms)

mk_ide rf is_cat_obj_prod_def
  |intro is_cat_obj_prodI|
  |dest is_cat_obj_prodD[dest]|
  |elim is_cat_obj_prodE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_obj_prodD

lemma (in is_cat_obj_coprod) is_cat_obj_coprod_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "U' = U" and "A' = A" and "I' = I" and "\<CC>' = \<CC>" 
  shows "\<pi> : A' >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U' : I' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_coprod_axioms)

mk_ide rf is_cat_obj_coprod_def
  |intro is_cat_obj_coprodI|
  |dest is_cat_obj_coprodD[dest]|
  |elim is_cat_obj_coprodE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_obj_coprodD


text\<open>Duality.\<close>

lemma (in is_cat_obj_prod) is_cat_obj_coprod_op:
  "op_ntcf \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  using cf_discrete_vdomain_vsubset_Vset
  by (intro is_cat_obj_coprodI)
    (cs_concl cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros)

lemma (in is_cat_obj_prod) is_cat_obj_coprod_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_coprod_op)

lemmas [cat_op_intros] = is_cat_obj_prod.is_cat_obj_coprod_op'

lemma (in is_cat_obj_coprod) is_cat_obj_prod_op:
  "op_ntcf \<pi> : U <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  using cf_discrete_vdomain_vsubset_Vset
  by (intro is_cat_obj_prodI)
    (cs_concl cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros)

lemma (in is_cat_obj_coprod) is_cat_obj_prod_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<pi> : U <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_prod_op)

lemmas [cat_op_intros] = is_cat_obj_coprod.is_cat_obj_prod_op'


subsubsection\<open>Universal property\<close>

(*cat_obj_prod_unique_cone already proven*)
lemma (in is_cat_obj_prod) cat_obj_prod_unique_cone':
  assumes "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: I A \<CC> : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : P' \<mapsto>\<^bsub>\<CC>\<^esub> P \<and> (\<forall>j\<in>\<^sub>\<circ>I. \<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f')"
  by 
    (
      rule cat_lim_unique_cone'[
        OF assms, unfolded the_cat_discrete_components(1)
        ]
    )

lemma (in is_cat_obj_prod) cat_obj_prod_unique:
  assumes "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : P' \<mapsto>\<^bsub>\<CC>\<^esub> P \<and> \<pi>' = \<pi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) \<CC> f'"
  by (intro cat_lim_unique[OF is_cat_obj_prodD(1)[OF assms]])

lemma (in is_cat_obj_prod) cat_obj_prod_unique':
  assumes "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : P' \<mapsto>\<^bsub>\<CC>\<^esub> P \<and> (\<forall>i\<in>\<^sub>\<circ>I. \<pi>'\<lparr>NTMap\<rparr>\<lparr>i\<rparr> = \<pi>\<lparr>NTMap\<rparr>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f')"
proof-
  interpret \<pi>': is_cat_obj_prod \<alpha> I A \<CC> P' \<pi>' by (rule assms(1))
  show ?thesis
    by 
      (
        rule cat_lim_unique'[
          OF \<pi>'.is_cat_limit_axioms, unfolded the_cat_discrete_components(1)
          ]
      )
qed

lemma (in is_cat_obj_coprod) cat_obj_coprod_unique_cocone':
  assumes "\<pi>' : :\<rightarrow>: I A \<CC> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e U' : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : U \<mapsto>\<^bsub>\<CC>\<^esub> U' \<and> (\<forall>j\<in>\<^sub>\<circ>I. \<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>)"
  by 
    (
      rule cat_colim_unique_cocone'[
        OF assms, unfolded the_cat_discrete_components(1)
        ]
    )

lemma (in is_cat_obj_coprod) cat_obj_coprod_unique:
  assumes "\<pi>' : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U' : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : U \<mapsto>\<^bsub>\<CC>\<^esub> U' \<and> \<pi>' = ntcf_const (:\<^sub>C I) \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<pi>"
  by (intro cat_colim_unique[OF is_cat_obj_coprodD(1)[OF assms]])

lemma (in is_cat_obj_coprod) cat_obj_coprod_unique':
  assumes "\<pi>' : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U' : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : U \<mapsto>\<^bsub>\<CC>\<^esub> U' \<and> (\<forall>j\<in>\<^sub>\<circ>I. \<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>)"
  by 
    (
      rule cat_colim_unique'[
        OF is_cat_obj_coprodD(1)[OF assms], unfolded the_cat_discrete_components
        ]
    )

lemma cat_obj_prod_ex_is_arr_isomorphism:
  assumes "\<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : P' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> P" and "\<pi>' = \<pi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) \<CC> f"
proof-
  interpret \<pi>: is_cat_obj_prod \<alpha> I A \<CC> P \<pi> by (rule assms(1))
  interpret \<pi>': is_cat_obj_prod \<alpha> I A \<CC> P' \<pi>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_lim_ex_is_arr_isomorphism[
          OF \<pi>.is_cat_limit_axioms \<pi>'.is_cat_limit_axioms
          ]
      )
qed

lemma cat_obj_prod_ex_is_arr_isomorphism':
  assumes "\<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : P' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> P" 
    and "\<And>j. j \<in>\<^sub>\<circ> I \<Longrightarrow> \<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
proof-
  interpret \<pi>: is_cat_obj_prod \<alpha> I A \<CC> P \<pi> by (rule assms(1))
  interpret \<pi>': is_cat_obj_prod \<alpha> I A \<CC> P' \<pi>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_lim_ex_is_arr_isomorphism'[
          OF \<pi>.is_cat_limit_axioms \<pi>'.is_cat_limit_axioms,
          unfolded the_cat_discrete_components(1)
          ]
      )
qed

lemma cat_obj_coprod_ex_is_arr_isomorphism:
  assumes "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<pi>' : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U' : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : U \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> U'" and "\<pi>' = ntcf_const (:\<^sub>C I) \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<pi>"
proof-
  interpret \<pi>: is_cat_obj_coprod \<alpha> I A \<CC> U \<pi> by (rule assms(1))
  interpret \<pi>': is_cat_obj_coprod \<alpha> I A \<CC> U' \<pi>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_colim_ex_is_arr_isomorphism[
          OF \<pi>.is_cat_colimit_axioms \<pi>'.is_cat_colimit_axioms
          ]
      )
qed

lemma cat_obj_coprod_ex_is_arr_isomorphism':
  assumes "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<pi>' : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> U' : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : U \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> U'" 
    and "\<And>j. j \<in>\<^sub>\<circ> I \<Longrightarrow> \<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>"
proof-
  interpret \<pi>: is_cat_obj_coprod \<alpha> I A \<CC> U \<pi> by (rule assms(1))
  interpret \<pi>': is_cat_obj_coprod \<alpha> I A \<CC> U' \<pi>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_colim_ex_is_arr_isomorphism'[
          OF \<pi>.is_cat_colimit_axioms \<pi>'.is_cat_colimit_axioms,
          unfolded the_cat_discrete_components(1)
          ]
      )
qed



subsection\<open>Finite product and finite coproduct\<close>

locale is_cat_finite_obj_prod = is_cat_obj_prod \<alpha> I A \<CC> P \<pi> 
  for \<alpha> I A \<CC> P \<pi> +
  assumes cat_fin_obj_prod_index_in_\<omega>: "I \<in>\<^sub>\<circ> \<omega>" 

syntax "_is_cat_finite_obj_prod" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_finite_obj_prod \<alpha> I A \<CC> P \<pi>"

locale is_cat_finite_obj_coprod = is_cat_obj_coprod \<alpha> I A \<CC> U \<pi> 
  for \<alpha> I A \<CC> U \<pi> +
  assumes cat_fin_obj_coprod_index_in_\<omega>: "I \<in>\<^sub>\<circ> \<omega>" 

syntax "_is_cat_finite_obj_coprod" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n U : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_finite_obj_coprod \<alpha> I A \<CC> U \<pi>"

lemma (in is_cat_finite_obj_prod) cat_fin_obj_prod_index_vfinite: "vfinite I"
  using cat_fin_obj_prod_index_in_\<omega> by auto

sublocale is_cat_finite_obj_prod \<subseteq> I: finite_category \<alpha> \<open>:\<^sub>C I\<close>
  by (intro finite_categoryI')
    (
      auto
        simp: NTDom.HomDom.tiny_dg_category the_cat_discrete_components
        intro!: cat_fin_obj_prod_index_vfinite
    )

lemma (in is_cat_finite_obj_coprod) cat_fin_obj_coprod_index_vfinite:
  "vfinite I"
  using cat_fin_obj_coprod_index_in_\<omega> by auto

sublocale is_cat_finite_obj_coprod \<subseteq> I: finite_category \<alpha> \<open>:\<^sub>C I\<close>
  by (intro finite_categoryI')
    (
      auto 
        simp: NTDom.HomDom.tiny_dg_category the_cat_discrete_components 
        intro!: cat_fin_obj_coprod_index_vfinite
    )


text\<open>Rules.\<close>

lemma (in is_cat_finite_obj_prod) 
  is_cat_finite_obj_prod_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "P' = P" and "A' = A" and "I' = I" and "\<CC>' = \<CC>" 
  shows "\<pi> : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n A' : I' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_obj_prod_axioms)

mk_ide rf 
  is_cat_finite_obj_prod_def[unfolded is_cat_finite_obj_prod_axioms_def]
  |intro is_cat_finite_obj_prodI|
  |dest is_cat_finite_obj_prodD[dest]|
  |elim is_cat_finite_obj_prodE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_finite_obj_prodD

lemma (in is_cat_finite_obj_coprod) 
  is_cat_finite_obj_coprod_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "U' = U" and "A' = A" and "I' = I" and "\<CC>' = \<CC>" 
  shows "\<pi> : A' >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n U' : I' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_obj_coprod_axioms)

mk_ide rf 
  is_cat_finite_obj_coprod_def[unfolded is_cat_finite_obj_coprod_axioms_def]
  |intro is_cat_finite_obj_coprodI|
  |dest is_cat_finite_obj_coprodD[dest]|
  |elim is_cat_finite_obj_coprodE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_finite_obj_coprodD


text\<open>Duality.\<close>

lemma (in is_cat_finite_obj_prod) is_cat_finite_obj_coprod_op:
  "op_ntcf \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_finite_obj_coprodI)
    (
      cs_concl 
        cs_simp: cat_op_simps 
        cs_intro: cat_fin_obj_prod_index_in_\<omega> cat_cs_intros cat_op_intros
    )

lemma (in is_cat_finite_obj_prod) is_cat_finite_obj_coprod_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n P : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_obj_coprod_op)

lemmas [cat_op_intros] = is_cat_finite_obj_prod.is_cat_finite_obj_coprod_op'

lemma (in is_cat_finite_obj_coprod) is_cat_finite_obj_prod_op:
  "op_ntcf \<pi> : U <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_finite_obj_prodI)
    (
      cs_concl 
        cs_simp: cat_op_simps 
        cs_intro: cat_fin_obj_coprod_index_in_\<omega> cat_cs_intros cat_op_intros
    )

lemma (in is_cat_finite_obj_coprod) is_cat_finite_obj_prod_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<pi> : U <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod>\<^sub>.\<^sub>f\<^sub>i\<^sub>n A : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_finite_obj_prod_op)

lemmas [cat_op_intros] = is_cat_finite_obj_coprod.is_cat_finite_obj_prod_op'



subsection\<open>Product and coproduct of two objects\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_cat_obj_prod_2 = is_cat_obj_prod \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 a b\<close> \<CC> P \<pi>
  for \<alpha> a b \<CC> P \<pi>

syntax "_is_cat_obj_prod_2" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {_,_} :/ 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a,b} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_obj_prod_2 \<alpha> a b \<CC> P \<pi>"

locale is_cat_obj_coprod_2 = is_cat_obj_coprod \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 a b\<close> \<CC> P \<pi>
  for \<alpha> a b \<CC> P \<pi>

syntax "_is_cat_obj_coprod_2" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ {_,_} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> _ :/ 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<pi> : {a,b} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> U : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_obj_coprod_2 \<alpha> a b \<CC> U \<pi>"

abbreviation proj_fst where "proj_fst \<pi> \<equiv> vpfst (\<pi>\<lparr>NTMap\<rparr>)"
abbreviation proj_snd where "proj_snd \<pi> \<equiv> vpsnd (\<pi>\<lparr>NTMap\<rparr>)"


text\<open>Rules.\<close>

lemma (in is_cat_obj_prod_2) is_cat_obj_prod_2_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "P' = P" and "a' = a" and "b' = b" and "\<CC>' = \<CC>" 
  shows "\<pi> : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a',b'} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_prod_2_axioms)

mk_ide rf is_cat_obj_prod_2_def
  |intro is_cat_obj_prod_2I|
  |dest is_cat_obj_prod_2D[dest]|
  |elim is_cat_obj_prod_2E[elim]|

lemmas [cat_lim_cs_intros] = is_cat_obj_prod_2D

lemma (in is_cat_obj_coprod_2) is_cat_obj_coprod_2_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "P' = P" and "a' = a" and "b' = b" and "\<CC>' = \<CC>" 
  shows "\<pi> : {a',b'} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> P' : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_coprod_2_axioms)

mk_ide rf is_cat_obj_coprod_2_def
  |intro is_cat_obj_coprod_2I|
  |dest is_cat_obj_coprod_2D[dest]|
  |elim is_cat_obj_coprod_2E[elim]|

lemmas [cat_lim_cs_intros] = is_cat_obj_coprod_2D


text\<open>Duality.\<close>

lemma (in is_cat_obj_prod_2) is_cat_obj_coprod_2_op:
  "op_ntcf \<pi> : {a,b} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> P : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (rule is_cat_obj_coprod_2I[OF is_cat_obj_coprod_op])

lemma (in is_cat_obj_prod_2) is_cat_obj_coprod_2_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<pi> : {a,b} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> P : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_coprod_2_op)

lemmas [cat_op_intros] = is_cat_obj_prod_2.is_cat_obj_coprod_2_op'

lemma (in is_cat_obj_coprod_2) is_cat_obj_prod_2_op:
  "op_ntcf \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a,b} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (rule is_cat_obj_prod_2I[OF is_cat_obj_prod_op])

lemma (in is_cat_obj_coprod_2) is_cat_obj_prod_2_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a,b} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_obj_prod_2_op)

lemmas [cat_op_intros] = is_cat_obj_coprod_2.is_cat_obj_prod_2_op'


text\<open>Product/coproduct of two objects is a finite product/coproduct.\<close>

sublocale is_cat_obj_prod_2 \<subseteq> is_cat_finite_obj_prod \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 a b\<close> \<CC> P \<pi>
proof(intro is_cat_finite_obj_prodI)
  show "2\<^sub>\<nat> \<in>\<^sub>\<circ> \<omega>" by simp
qed (cs_concl cs_simp: two[symmetric] cs_intro: cat_lim_cs_intros)

sublocale is_cat_obj_coprod_2 \<subseteq> is_cat_finite_obj_coprod \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 a b\<close> \<CC> P \<pi>
proof(intro is_cat_finite_obj_coprodI)
  show "2\<^sub>\<nat> \<in>\<^sub>\<circ> \<omega>" by simp
qed (cs_concl cs_simp: two[symmetric] cs_intro: cat_lim_cs_intros)


text\<open>Elementary properties.\<close>

lemma (in is_cat_obj_prod_2) cat_obj_prod_2_lr_in_Obj:
  shows cat_obj_prod_2_left_in_Obj[cat_lim_cs_intros]: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and cat_obj_prod_2_right_in_Obj[cat_lim_cs_intros]: "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
proof-
  have 0: "0 \<in>\<^sub>\<circ> 2\<^sub>\<nat>" and 1: "1\<^sub>\<nat> \<in>\<^sub>\<circ> 2\<^sub>\<nat>" by simp_all
  show "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by 
      (
        intro 
          cf_discrete_selector_vrange[OF 0, simplified]
          cf_discrete_selector_vrange[OF 1, simplified]
      )+
qed

lemmas [cat_lim_cs_intros] = is_cat_obj_prod_2.cat_obj_prod_2_lr_in_Obj

lemma (in is_cat_obj_coprod_2) cat_obj_coprod_2_lr_in_Obj:
  shows cat_obj_coprod_2_left_in_Obj[cat_lim_cs_intros]: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and cat_obj_coprod_2_right_in_Obj[cat_lim_cs_intros]: "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  by 
    (
      intro is_cat_obj_prod_2.cat_obj_prod_2_lr_in_Obj[
        OF is_cat_obj_prod_2_op, unfolded cat_op_simps
        ]
    )+

lemmas [cat_lim_cs_intros] = is_cat_obj_coprod_2.cat_obj_coprod_2_lr_in_Obj


text\<open>Utilities/help lemmas.\<close>

lemma helper_I2_proj_fst_proj_snd_iff: 
  "(\<forall>j\<in>\<^sub>\<circ>2\<^sub>\<nat>. \<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f') \<longleftrightarrow>
    (proj_fst \<pi>' = proj_fst \<pi> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' \<and> proj_snd \<pi>' = proj_snd \<pi> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f')" 
  unfolding two by auto

lemma helper_I2_proj_fst_proj_snd_iff': 
  "(\<forall>j\<in>\<^sub>\<circ>2\<^sub>\<nat>. \<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>) \<longleftrightarrow>
    (proj_fst \<pi>' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> proj_fst \<pi> \<and> proj_snd \<pi>' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> proj_snd \<pi>)" 
  unfolding two by auto


subsubsection\<open>Universal property\<close>

lemma (in is_cat_obj_prod_2) cat_obj_prod_2_unique_cone':
  assumes "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: (2\<^sub>\<nat>) (if2 a b) \<CC> : :\<^sub>C (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows
    "\<exists>!f'. f' : P' \<mapsto>\<^bsub>\<CC>\<^esub> P \<and>
      proj_fst \<pi>' = proj_fst \<pi> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' \<and>
      proj_snd \<pi>' = proj_snd \<pi> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
  by 
    (
      rule cat_obj_prod_unique_cone'[
        OF assms, unfolded helper_I2_proj_fst_proj_snd_iff
        ]
    )

lemma (in is_cat_obj_prod_2) cat_obj_prod_2_unique:
  assumes "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a,b} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : P' \<mapsto>\<^bsub>\<CC>\<^esub> P \<and> \<pi>' = \<pi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C (2\<^sub>\<nat>)) \<CC> f'"
  by (rule cat_obj_prod_unique[OF is_cat_obj_prod_2D[OF assms]])

lemma (in is_cat_obj_prod_2) cat_obj_prod_2_unique':
  assumes "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a,b} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows
    "\<exists>!f'. f' : P' \<mapsto>\<^bsub>\<CC>\<^esub> P \<and>
      proj_fst \<pi>' = proj_fst \<pi> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' \<and>
      proj_snd \<pi>' = proj_snd \<pi> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
  by 
    (
      rule cat_obj_prod_unique'[
        OF is_cat_obj_prod_2D[OF assms], 
        unfolded helper_I2_proj_fst_proj_snd_iff
        ]
    )

lemma (in is_cat_obj_coprod_2) cat_obj_coprod_2_unique_cocone':
  assumes "\<pi>' : :\<rightarrow>: (2\<^sub>\<nat>) (if2 a b) \<CC> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e P' : :\<^sub>C (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows
    "\<exists>!f'. f' : P \<mapsto>\<^bsub>\<CC>\<^esub> P' \<and>
      proj_fst \<pi>' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> proj_fst \<pi> \<and>
      proj_snd \<pi>' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> proj_snd \<pi>"
  by 
    (
      rule cat_obj_coprod_unique_cocone'[
        OF assms, unfolded helper_I2_proj_fst_proj_snd_iff'
        ]
    )

lemma (in is_cat_obj_coprod_2) cat_obj_coprod_2_unique:
  assumes "\<pi>' : {a,b} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> P' : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : P \<mapsto>\<^bsub>\<CC>\<^esub> P' \<and> \<pi>' = ntcf_const (:\<^sub>C (2\<^sub>\<nat>)) \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<pi>"
  by (rule cat_obj_coprod_unique[OF is_cat_obj_coprod_2D[OF assms]])

lemma (in is_cat_obj_coprod_2) cat_obj_coprod_2_unique':
  assumes "\<pi>' : {a,b} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> P' : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows
    "\<exists>!f'. f' : P \<mapsto>\<^bsub>\<CC>\<^esub> P' \<and>
      proj_fst \<pi>' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> proj_fst \<pi> \<and>
      proj_snd \<pi>' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> proj_snd \<pi>"
  by 
    (
      rule cat_obj_coprod_unique'[
        OF is_cat_obj_coprod_2D[OF assms], 
        unfolded helper_I2_proj_fst_proj_snd_iff'
        ]
    )

lemma cat_obj_prod_2_ex_is_arr_isomorphism:
  assumes "\<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a,b} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<pi>' : P' <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<times> {a,b} : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : P' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> P" and "\<pi>' = \<pi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C (2\<^sub>\<nat>)) \<CC> f"
proof-
  interpret \<pi>: is_cat_obj_prod_2 \<alpha> a b \<CC> P \<pi> by (rule assms(1))
  interpret \<pi>': is_cat_obj_prod_2 \<alpha> a b \<CC> P' \<pi>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_obj_prod_ex_is_arr_isomorphism[
          OF \<pi>.is_cat_obj_prod_axioms \<pi>'.is_cat_obj_prod_axioms
          ]
      )
qed

lemma cat_obj_coprod_2_ex_is_arr_isomorphism:
  assumes "\<pi> : {a,b} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> U : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<pi>' : {a,b} >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<uplus> U' : 2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : U \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> U'" and "\<pi>' = ntcf_const (:\<^sub>C (2\<^sub>\<nat>)) \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<pi>"
proof-
  interpret \<pi>: is_cat_obj_coprod_2 \<alpha> a b \<CC> U \<pi> by (rule assms(1))
  interpret \<pi>': is_cat_obj_coprod_2 \<alpha> a b \<CC> U' \<pi>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_obj_coprod_ex_is_arr_isomorphism[
          OF \<pi>.is_cat_obj_coprod_axioms \<pi>'.is_cat_obj_coprod_axioms
          ]
      )
qed



subsection\<open>Pullbacks and pushouts\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The definitions and the elementary properties of the pullbacks and the 
pushouts can be found, for example, in Chapter III-3 and Chapter III-4 in 
\cite{mac_lane_categories_2010}. 
\<close>

locale is_cat_pullback =
  is_cat_limit \<alpha> \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> X x + 
  cf_scospan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC>
  for \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x 

syntax "_is_cat_pullback" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b _\<rightarrow>_\<rightarrow>_\<leftarrow>_\<leftarrow>_ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51, 51, 51, 51] 51)
translations "x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_pullback \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x"
                        
locale is_cat_pushout =
  is_cat_colimit \<alpha> \<open>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> X x +
  cf_sspan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC>
  for \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x

syntax "_is_cat_pushout" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _\<leftarrow>_\<leftarrow>_\<rightarrow>_\<rightarrow>_ >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51, 51, 51, 51] 51)
translations "x : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_pushout \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x"


text\<open>Rules.\<close>

lemma (in is_cat_pullback) is_cat_pullback_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
    and "\<aa>' = \<aa>"
    and "\<gg>' = \<gg>"
    and "\<oo>' = \<oo>"
    and "\<ff>' = \<ff>"
    and "\<bb>' = \<bb>"
    and "\<CC>' = \<CC>"
    and "X' = X"
  shows "x : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>'\<rightarrow>\<gg>'\<rightarrow>\<oo>'\<leftarrow>\<ff>'\<leftarrow>\<bb>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_pullback_axioms)

mk_ide rf is_cat_pullback_def
  |intro is_cat_pullbackI|
  |dest is_cat_pullbackD[dest]|
  |elim is_cat_pullbackE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_pullbackD

lemma (in is_cat_pushout) is_cat_pushout_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
    and "\<aa>' = \<aa>"
    and "\<gg>' = \<gg>"
    and "\<oo>' = \<oo>"
    and "\<ff>' = \<ff>"
    and "\<bb>' = \<bb>"
    and "\<CC>' = \<CC>"
    and "X' = X"
  shows "x : \<aa>'\<leftarrow>\<gg>'\<leftarrow>\<oo>'\<rightarrow>\<ff>'\<rightarrow>\<bb>' >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_pushout_axioms)

mk_ide rf is_cat_pushout_def
  |intro is_cat_pushoutI|
  |dest is_cat_pushoutD[dest]|
  |elim is_cat_pushoutE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_pushoutD


text\<open>Duality.\<close>

lemma (in is_cat_pullback) is_cat_pushout_op:
  "op_ntcf x : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_pushoutI) 
    (cs_concl cs_simp: cat_op_simps cs_intro: cat_op_intros)+

lemma (in is_cat_pullback) is_cat_pushout_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf x : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_pushout_op)

lemmas [cat_op_intros] = is_cat_pullback.is_cat_pushout_op'

lemma (in is_cat_pushout) is_cat_pullback_op:
  "op_ntcf x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_pullbackI) 
    (cs_concl cs_simp: cat_op_simps cs_intro: cat_op_intros)+

lemma (in is_cat_pushout) is_cat_pullback_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_pullback_op)

lemmas [cat_op_intros] = is_cat_pushout.is_cat_pullback_op'


text\<open>Elementary properties.\<close>

lemma cat_cone_cospan:
  assumes "x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "cf_scospan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC>"
  shows "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr>"
    and "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
    and "\<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
proof-
  interpret x: is_cat_cone \<alpha> X \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> x 
    by (rule assms(1))
  interpret cospan: cf_scospan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> by (rule assms(2))
  have \<gg>\<^sub>S\<^sub>S: "\<gg>\<^sub>S\<^sub>S : \<aa>\<^sub>S\<^sub>S \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> \<oo>\<^sub>S\<^sub>S" and \<ff>\<^sub>S\<^sub>S: "\<ff>\<^sub>S\<^sub>S : \<bb>\<^sub>S\<^sub>S \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> \<oo>\<^sub>S\<^sub>S" 
    by (cs_concl cs_simp: cs_intro: cat_ss_cs_intros)+
  from x.ntcf_Comp_commute[OF \<gg>\<^sub>S\<^sub>S] \<gg>\<^sub>S\<^sub>S \<ff>\<^sub>S\<^sub>S show
    "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr>"
    by (cs_prems cs_simp: cat_ss_cs_simps cat_cs_simps cs_intro: cat_cs_intros)
  moreover from x.ntcf_Comp_commute[OF \<ff>\<^sub>S\<^sub>S] \<gg>\<^sub>S\<^sub>S \<ff>\<^sub>S\<^sub>S show 
    "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
    by (cs_prems cs_simp: cat_ss_cs_simps cat_cs_simps cs_intro: cat_cs_intros)
  ultimately show "\<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>" by simp
qed

lemma (in is_cat_pullback) cat_pb_cone_cospan:
  shows "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr>"
    and "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
    and "\<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
  by (all\<open>rule cat_cone_cospan[OF is_cat_cone_axioms cf_scospan_axioms]\<close>)

lemma cat_cocone_span:
  assumes "x : \<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e X : \<leftarrow>\<bullet>\<rightarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "cf_sspan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC>"
  shows "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>"
    and "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
    and "x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
proof-
  interpret x: is_cat_cocone \<alpha> X \<open>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> x
    by (rule assms(1))
  interpret span: cf_sspan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> by (rule assms(2))
  note op = 
    cat_cone_cospan
      [
        OF 
          x.is_cat_cone_op[unfolded cat_op_simps] 
          span.cf_scospan_op, 
          unfolded cat_op_simps
      ]
  from op(1) show "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>"
    by 
      (
        cs_prems 
          cs_simp: cat_ss_cs_simps cat_op_simps 
          cs_intro: cat_cs_intros cat_ss_cs_intros
      )
  moreover from op(2) show "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
    by 
      (
        cs_prems 
          cs_simp: cat_ss_cs_simps cat_op_simps 
          cs_intro: cat_cs_intros cat_ss_cs_intros
      )
  ultimately show "x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>" by auto
qed

lemma (in is_cat_pushout) cat_po_cocone_span:
  shows "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>"
    and "x\<lparr>NTMap\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
    and "x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
  by (all\<open>rule cat_cocone_span[OF is_cat_cocone_axioms cf_sspan_axioms]\<close>)


subsubsection\<open>Universal property\<close>

lemma is_cat_pullbackI':
  assumes "x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "cf_scospan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC>"
    and "\<And>x' X'.
      x' : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
        \<exists>!f'.
          f' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X \<and>
          x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' \<and>
          x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
  shows "x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_cat_pullbackI is_cat_limitI')

  show "x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    by (rule assms(1))
  interpret x: is_cat_cone \<alpha> X \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> x 
    by (rule assms(1))
  show "cf_scospan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC>" by (rule assms(2))
  interpret cospan: cf_scospan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> by (rule assms(2))

  fix u' r' assume prems:
    "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"

  interpret u': is_cat_cone \<alpha> r' \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> u' 
    by (rule prems)

  from assms(3)[OF prems] obtain f' 
    where f': "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> X"
      and u'_\<aa>\<^sub>S\<^sub>S: "u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
      and u'_\<bb>\<^sub>S\<^sub>S: "u'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
      and unique_f': "\<And>f''.
        \<lbrakk>
          f'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> X;
          u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'';
          u'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''
        \<rbrakk> \<Longrightarrow> f'' = f'"
    by metis

  show "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> X \<and> u' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'"
  proof(intro ex1I conjI; (elim conjE)?)

    show "u' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'"
    proof(rule ntcf_eqI)
      show "u' : cf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> r' \<mapsto>\<^sub>C\<^sub>F \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (rule u'.is_ntcf_axioms)
      from f' show 
        "x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f' :
          cf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> r' \<mapsto>\<^sub>C\<^sub>F \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> :
          \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      from f' have dom_rhs: 
        "\<D>\<^sub>\<circ> ((x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f')\<lparr>NTMap\<rparr>) = \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      show "u'\<lparr>NTMap\<rparr> = (x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f')\<lparr>NTMap\<rparr>"
      proof(rule vsv_eqI, unfold cat_cs_simps dom_rhs)
        fix a assume prems': "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
        from this f' x.is_ntcf_axioms show
          "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
          by (elim the_cat_scospan_ObjE; simp only:)
            (
              cs_concl
                cs_simp:
                  cat_cs_simps cat_ss_cs_simps 
                  u'_\<bb>\<^sub>S\<^sub>S u'_\<aa>\<^sub>S\<^sub>S 
                  cat_cone_cospan(1)[OF assms(1,2)] 
                  cat_cone_cospan(1)[OF prems assms(2)] 
                cs_intro: cat_cs_intros cat_ss_cs_intros
            )+
      qed (cs_concl cs_intro: cat_cs_intros | auto)+
    qed simp_all

    fix f'' assume prems: 
      "f'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> X" "u' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f''"
    have \<aa>\<^sub>S\<^sub>S: "\<aa>\<^sub>S\<^sub>S \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" and \<bb>\<^sub>S\<^sub>S: "\<bb>\<^sub>S\<^sub>S \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" 
      by (cs_concl cs_simp: cs_intro: cat_ss_cs_intros)+
    have "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''" if "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" for a
    proof-
      from prems(2) have 
        "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by simp
      from this that prems(1) show "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''"
        by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    qed
    from unique_f'[OF prems(1) this[OF \<aa>\<^sub>S\<^sub>S] this[OF \<bb>\<^sub>S\<^sub>S]] show "f'' = f'".

  qed (intro f')

qed

lemma is_cat_pushoutI':
  assumes "x : \<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e X : \<leftarrow>\<bullet>\<rightarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "cf_sspan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC>"
    and "\<And>x' X'. x' : \<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e X' : \<leftarrow>\<bullet>\<rightarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
      \<exists>!f'.
        f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and>
        x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<and>
        x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
  shows "x : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret x: is_cat_cocone \<alpha> X \<open>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> x 
    by (rule assms(1))
  interpret span: cf_sspan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> by (rule assms(2))
  have assms_3': 
    "\<exists>!f'.
      f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and>
      x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f' \<and>
      x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f'"
    if "x' : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>op_cat \<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    for x' X'
  proof-
    from that(1) have [cat_op_simps]:
      "f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and> 
      x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f' \<and>
      x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f' \<longleftrightarrow>
        f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and>
        x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<and>
        x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>" 
      for f'
      by (intro iffI conjI; (elim conjE)?)
        (
          cs_concl 
            cs_simp: category.op_cat_Comp[symmetric] cat_op_simps cat_cs_simps 
            cs_intro: cat_cs_intros cat_ss_cs_intros
        )+
    interpret x': 
      is_cat_cone \<alpha> X' \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close> \<open>op_cat \<CC>\<close> \<open>\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>op_cat \<CC>\<^esub>\<close> x'
      by (rule that)
    show ?thesis
      unfolding cat_op_simps
      by 
        (
          rule assms(3)[
            OF x'.is_cat_cocone_op[unfolded cat_op_simps], 
            unfolded cat_op_simps
            ]
        )
  qed
  interpret op_x: is_cat_pullback \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<open>op_cat \<CC>\<close> X \<open>op_ntcf x\<close> 
    using 
      is_cat_pullbackI'
        [
          OF x.is_cat_cone_op[unfolded cat_op_simps] 
          span.cf_scospan_op, 
          unfolded cat_op_simps, 
          OF assms_3'
        ]
    by simp
  show "x : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (rule op_x.is_cat_pushout_op[unfolded cat_op_simps])
qed
                   
lemma (in is_cat_pullback) cat_pb_unique_cone:
  assumes "x' : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'.
    f' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
proof-
  interpret x': is_cat_cone \<alpha> X' \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> x' 
    by (rule assms)
  from cat_lim_unique_cone[OF assms] obtain f'
    where f': "f' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X" 
      and x'_def: "x' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'"
      and unique_f': "\<And>f''.
        \<lbrakk> f'' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X; x' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'' \<rbrakk> \<Longrightarrow>
        f'' = f'"
    by auto
  have \<aa>\<^sub>S\<^sub>S: "\<aa>\<^sub>S\<^sub>S \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" and \<bb>\<^sub>S\<^sub>S: "\<bb>\<^sub>S\<^sub>S \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
    by (cs_concl cs_intro: cat_ss_cs_intros)+
  show ?thesis
  proof(intro ex1I conjI; (elim conjE)?)
    show "f' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X" by (rule f')
    have "x'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'" if "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" for a
    proof-
      from x'_def have 
        "x'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by simp
      from this that f' show "x'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
        by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    qed
    from this[OF \<aa>\<^sub>S\<^sub>S] this[OF \<bb>\<^sub>S\<^sub>S] show 
      "x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
      "x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
      by auto
    fix f'' assume prems': 
      "f'' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X"
      "x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''"
      "x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''"
    have "x' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f''"
    proof(rule ntcf_eqI)
      show "x' : cf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> X' \<mapsto>\<^sub>C\<^sub>F \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (rule x'.is_ntcf_axioms)
      from prems'(1) show
        "x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'' :
          cf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> X' \<mapsto>\<^sub>C\<^sub>F \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> :
          \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      have dom_lhs: "\<D>\<^sub>\<circ> (x'\<lparr>NTMap\<rparr>) = \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" 
        by (cs_concl cs_simp: cat_cs_simps)
      from prems'(1) have dom_rhs:
        "\<D>\<^sub>\<circ> ((x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'')\<lparr>NTMap\<rparr>) = \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      show "x'\<lparr>NTMap\<rparr> = (x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'')\<lparr>NTMap\<rparr>"
      proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
        fix a assume prems'': "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
        from this prems'(1) show 
          "x'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
          by (elim the_cat_scospan_ObjE; simp only:)
            (
              cs_concl 
                cs_simp: 
                  prems'(2,3)
                  cat_cone_cospan(1,2)[OF assms cf_scospan_axioms] 
                  cat_pb_cone_cospan 
                  cat_ss_cs_simps cat_cs_simps 
                cs_intro: cat_ss_cs_intros cat_cs_intros
            )+
      qed (auto simp: cat_cs_intros)
    qed simp_all
    from unique_f'[OF prems'(1) this] show "f'' = f'".
  qed
qed

lemma (in is_cat_pullback) cat_pb_unique:
  assumes "x' : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X \<and> x' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<CC> f'"
  by (rule cat_lim_unique[OF is_cat_pullbackD(1)[OF assms]])

lemma (in is_cat_pullback) cat_pb_unique':
  assumes "x' : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'.
    f' : X' \<mapsto>\<^bsub>\<CC>\<^esub> X \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
proof-
  interpret x': is_cat_pullback \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X' x' by (rule assms(1))
  show ?thesis by (rule cat_pb_unique_cone[OF x'.is_cat_cone_axioms])
qed

lemma (in is_cat_pushout) cat_po_unique_cocone:
  assumes "x' : \<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e X' : \<leftarrow>\<bullet>\<rightarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'.
    f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
proof-
  interpret x': is_cat_cocone \<alpha> X' \<open>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<close> \<CC> \<open>\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<close> x'
    by (rule assms(1))
  have [cat_op_simps]:
    "f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f' \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f' \<longleftrightarrow>
      f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and>
      x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<and>
      x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>" 
    for f'
    by (intro iffI conjI; (elim conjE)?)
      (
        cs_concl 
          cs_simp: category.op_cat_Comp[symmetric] cat_op_simps cat_cs_simps  
          cs_intro: cat_cs_intros cat_ss_cs_intros
      )+
  show ?thesis
    by 
      (
        rule is_cat_pullback.cat_pb_unique_cone[
          OF is_cat_pullback_op x'.is_cat_cone_op[unfolded cat_op_simps], 
          unfolded cat_op_simps
          ]
     )
qed

lemma (in is_cat_pushout) cat_po_unique:
  assumes "x' : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and> x' = ntcf_const \<leftarrow>\<bullet>\<rightarrow>\<^sub>C \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F x"
  by (rule cat_colim_unique[OF is_cat_pushoutD(1)[OF assms]])

lemma (in is_cat_pushout) cat_po_unique':
  assumes "x' : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'.
    f' : X \<mapsto>\<^bsub>\<CC>\<^esub> X' \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<and>
    x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
proof-
  interpret x': is_cat_pushout \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X' x' by (rule assms(1))
  show ?thesis by (rule cat_po_unique_cocone[OF x'.is_cat_cocone_axioms])
qed

lemma cat_pullback_ex_is_arr_isomorphism:
  assumes "x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "x' : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : X' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> X" 
    and "x' = x \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<rightarrow>\<bullet>\<leftarrow>\<^sub>C  \<CC> f"
proof-
  interpret x: is_cat_pullback \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x by (rule assms(1))
  interpret x': is_cat_pullback \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X' x' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_lim_ex_is_arr_isomorphism[
          OF x.is_cat_limit_axioms x'.is_cat_limit_axioms
          ]
      )
qed

lemma cat_pullback_ex_is_arr_isomorphism':
  assumes "x : X <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "x' : X' <\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>b \<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : X' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> X" 
    and "x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    and "x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
proof-
  interpret x: is_cat_pullback \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x by (rule assms(1))
  interpret x': is_cat_pullback \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X' x' by (rule assms(2))
  obtain f where f: "f : X' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> X"
    and "j \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr> \<Longrightarrow> x'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f" for j
    by 
      (
        elim cat_lim_ex_is_arr_isomorphism'[
          OF x.is_cat_limit_axioms x'.is_cat_limit_axioms
          ]
      )
  then have 
    "x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f" 
    "x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    by (auto simp: cat_ss_cs_intros)
  with f show ?thesis using that by simp
qed

lemma cat_pushout_ex_is_arr_isomorphism:
  assumes "x : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "x' : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : X \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> X'" 
    and "x' = ntcf_const \<leftarrow>\<bullet>\<rightarrow>\<^sub>C \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F x"
proof-
  interpret x: is_cat_pushout \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x by (rule assms(1))
  interpret x': is_cat_pushout \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X' x' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_colim_ex_is_arr_isomorphism[
          OF x.is_cat_colimit_axioms x'.is_cat_colimit_axioms
          ]
      )
qed

lemma cat_pushout_ex_is_arr_isomorphism':
  assumes "x : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "x' : \<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb> >\<^sub>C\<^sub>F\<^sub>.\<^sub>p\<^sub>o X' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : X \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> X'" 
    and "x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr>"
    and "x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
proof-
  interpret x: is_cat_pushout \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X x by (rule assms(1))
  interpret x': is_cat_pushout \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> X' x' by (rule assms(2))
  obtain f where f: "f : X \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> X'"
    and "j \<in>\<^sub>\<circ> \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Obj\<rparr> \<Longrightarrow> x'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>j\<rparr>" for j
    by 
      (
        elim cat_colim_ex_is_arr_isomorphism'[
          OF x.is_cat_colimit_axioms x'.is_cat_colimit_axioms,
          unfolded the_cat_parallel_components(1)
          ]
      )
  then have "x'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr>"
    and "x'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> x\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr>"
    by (auto simp: cat_ss_cs_intros)
  with f show ?thesis using that by simp
qed



subsection\<open>Equalizers and coequalizers\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
See \cite{noauthor_wikipedia_2001}\footnote{
\url{https://en.wikipedia.org/wiki/Equaliser_(mathematics)}
}.
\<close>

locale is_cat_equalizer =
  is_cat_limit \<alpha> \<open>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<close> \<CC> \<open>\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>\<close> E \<epsilon> 
  for \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> +
  assumes cat_eq_\<gg>[cat_lim_cs_intros]: "\<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
    and cat_eq_\<ff>[cat_lim_cs_intros]: "\<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"

syntax "_is_cat_equalizer" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q '(_,_,_,_') :/ \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51, 51] 51)
translations "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon>"

locale is_cat_coequalizer =
  is_cat_colimit \<alpha> \<open>\<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L\<close> \<CC> \<open>\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg>\<close> E \<epsilon> 
  for \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> +
  assumes cat_coeq_\<gg>[cat_lim_cs_intros]: "\<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    and cat_coeq_\<ff>[cat_lim_cs_intros]: "\<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"

syntax "_is_cat_coequalizer" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ '(_,_,_,_') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q _ :/ \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51, 51] 51)
translations "\<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" \<rightleftharpoons> 
  "CONST is_cat_coequalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon>"


text\<open>Rules.\<close>

lemma (in is_cat_equalizer) is_cat_equalizer_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
    and "E' = E"
    and "\<aa>' = \<aa>"
    and "\<bb>' = \<bb>"
    and "\<gg>' = \<gg>"
    and "\<ff>' = \<ff>"
    and "\<CC>' = \<CC>"
  shows "\<epsilon> : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>',\<bb>',\<gg>',\<ff>') : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_equalizer_axioms)

mk_ide rf is_cat_equalizer_def[unfolded is_cat_equalizer_axioms_def]
  |intro is_cat_equalizerI|
  |dest is_cat_equalizerD[dest]|
  |elim is_cat_equalizerE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_equalizerD(1)

lemma (in is_cat_coequalizer) is_cat_coequalizer_axioms'[cat_lim_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
    and "E' = E"
    and "\<aa>' = \<aa>"
    and "\<bb>' = \<bb>"
    and "\<gg>' = \<gg>"
    and "\<ff>' = \<ff>"
    and "\<CC>' = \<CC>"
  shows "\<epsilon> : (\<aa>',\<bb>',\<gg>',\<ff>') >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_coequalizer_axioms)

mk_ide rf is_cat_coequalizer_def[unfolded is_cat_coequalizer_axioms_def]
  |intro is_cat_coequalizerI|
  |dest is_cat_coequalizerD[dest]|
  |elim is_cat_coequalizerE[elim]|

lemmas [cat_lim_cs_intros] = is_cat_coequalizerD(1)


text\<open>Elementary properties.\<close>

sublocale is_cat_equalizer \<subseteq> cf_parallel \<alpha> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> \<CC> 
  by (intro cf_parallelI cat_parallelI)
    (simp_all add: cat_parallel_cs_intros cat_lim_cs_intros cat_cs_intros)

sublocale is_cat_coequalizer \<subseteq> cf_parallel \<alpha> \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> \<CC>
  by (intro cf_parallelI cat_parallelI)
    (
      simp_all add: 
        cat_parallel_cs_intros cat_lim_cs_intros cat_cs_intros 
        cat_PL_ineq[symmetric]
    )


text\<open>Duality.\<close>

lemma (in is_cat_equalizer) is_cat_coequalizer_op:
  "op_ntcf \<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_coequalizerI)
    (cs_concl cs_simp: cat_op_simps cs_intro: cat_op_intros cat_lim_cs_intros)+

lemma (in is_cat_equalizer) is_cat_coequalizer_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_coequalizer_op)

lemmas [cat_op_intros] = is_cat_equalizer.is_cat_coequalizer_op'

lemma (in is_cat_coequalizer) is_cat_equalizer_op:
  "op_ntcf \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by (intro is_cat_equalizerI)
    (
      cs_concl
        cs_simp: cat_op_simps
        cs_intro: cat_cs_intros cat_op_intros cat_lim_cs_intros
    )+

lemma (in is_cat_coequalizer) is_cat_equalizer_op'[cat_op_intros]:
  assumes "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cat_equalizer_op)

lemmas [cat_op_intros] = is_cat_coequalizer.is_cat_equalizer_op'


text\<open>Elementary properties.\<close>

lemma cf_parallel_if_is_cat_cone:
  assumes "\<epsilon> :
    E <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> : \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
    and "\<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
  shows "cf_parallel \<alpha> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> \<CC>"
proof-
  let ?II = \<open>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<close> and ?II_II = \<open>\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>\<close>
  interpret is_cat_cone \<alpha> E ?II \<CC> ?II_II \<epsilon> by (rule assms(1))
  show ?thesis
    by (intro cf_parallelI cat_parallelI)
      (
        simp_all add: 
          assms cat_parallel_cs_intros cat_lim_cs_intros cat_cs_intros
      )
qed

lemma cf_parallel_if_is_cat_cocone:
  assumes "\<epsilon>' :
    \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E' : \<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    and "\<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
  shows "cf_parallel \<alpha> \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> \<CC>"
proof-
  let ?II = \<open>\<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L\<close> and ?II_II = \<open>\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg>\<close>
  interpret is_cat_cocone \<alpha> E' ?II \<CC> ?II_II \<epsilon>' by (rule assms(1))
  show ?thesis
    by (intro cf_parallelI cat_parallelI)
      (
        simp_all add: 
          assms 
          cat_parallel_cs_intros 
          cat_lim_cs_intros 
          cat_cs_intros
          cat_PL_ineq[symmetric]
      )
qed

lemma (in category) cat_cf_parallel_cat_equalizer: 
  assumes "\<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>" and "\<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
  shows "cf_parallel \<alpha> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> \<CC>"
  using assms 
  by (intro cf_parallelI cat_parallelI)
    (auto simp: cat_parallel_cs_intros cat_cs_intros)

lemma (in category) cat_cf_parallel_cat_coequalizer: 
  assumes "\<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>" and "\<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
  shows "cf_parallel \<alpha> \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> \<CC>"
  using assms 
  by (intro cf_parallelI cat_parallelI)
    (simp_all add: cat_parallel_cs_intros cat_cs_intros cat_PL_ineq[symmetric])

lemma cat_cone_cf_par_eps_NTMap_app:
  assumes "\<epsilon> :
    E <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> : \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>" 
    and "\<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
  shows 
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>" 
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>"
proof-
  let ?II = \<open>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<close> and ?II_II = \<open>\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>\<close>
  interpret \<epsilon>: is_cat_cone \<alpha> E ?II \<CC> ?II_II \<epsilon> by (rule assms(1))
  from assms(2,3) have \<aa>: "\<aa> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and \<bb>: "\<bb> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  interpret par: cf_parallel \<alpha> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> \<CC> 
    by (intro cf_parallel_if_is_cat_cone, rule assms) (auto intro: assms \<aa> \<bb>)
  have \<gg>\<^sub>P\<^sub>L: "\<gg>\<^sub>P\<^sub>L : \<aa>\<^sub>P\<^sub>L \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<^esub> \<bb>\<^sub>P\<^sub>L" 
    and \<ff>\<^sub>P\<^sub>L: "\<ff>\<^sub>P\<^sub>L : \<aa>\<^sub>P\<^sub>L \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<^esub> \<bb>\<^sub>P\<^sub>L"
    by 
      (
        simp_all add: 
          par.the_cat_parallel_is_arr_\<aa>\<bb>\<gg> par.the_cat_parallel_is_arr_\<aa>\<bb>\<ff>
      )
  from \<epsilon>.ntcf_Comp_commute[OF \<gg>\<^sub>P\<^sub>L] show "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>"
    by (*slow*)
      (
        cs_prems 
          cs_simp: cat_parallel_cs_simps cat_cs_simps 
          cs_intro: cat_cs_intros cat_parallel_cs_intros 
      )
  from \<epsilon>.ntcf_Comp_commute[OF \<ff>\<^sub>P\<^sub>L] show "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>"
    by (*slow*)
      (
        cs_prems 
          cs_simp: cat_parallel_cs_simps cat_cs_simps 
          cs_intro: cat_cs_intros cat_parallel_cs_intros 
      )
qed

lemma cat_cocone_cf_par_eps_NTMap_app:
  assumes "\<epsilon> :
    \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E : \<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>" 
    and "\<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
  shows 
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>" 
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"    
proof-
  let ?II = \<open>\<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L\<close> and ?II_II = \<open>\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg>\<close>
  interpret \<epsilon>: is_cat_cocone \<alpha> E ?II \<CC> ?II_II \<epsilon> by (rule assms(1))
  from assms(2,3) have \<aa>: "\<aa> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and \<bb>: "\<bb> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  interpret par: cf_parallel \<alpha> \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> \<CC> 
    by (intro cf_parallel_if_is_cat_cocone, rule assms) (auto intro: assms \<aa> \<bb>)
  note \<epsilon>_NTMap_app = 
    cat_cone_cf_par_eps_NTMap_app[
      OF \<epsilon>.is_cat_cone_op[unfolded cat_op_simps],
      unfolded cat_op_simps,  
      OF assms(2,3)
      ]
  from \<epsilon>_NTMap_app show \<epsilon>_NTMap_app:
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>"
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
    by 
      (
        cs_concl
          cs_simp: cat_parallel_cs_simps category.op_cat_Comp[symmetric] 
          cs_intro: cat_cs_intros cat_parallel_cs_intros
      )+
qed

lemma (in is_cat_equalizer) cat_eq_2_eps_NTMap_app:
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>" 
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>"
  by 
    (
      intro cat_cone_cf_par_eps_NTMap_app[
        OF is_cat_cone_axioms cat_eq_\<gg> cat_eq_\<ff>
        ]
    )+

lemma (in is_cat_coequalizer) cat_coeq_2_eps_NTMap_app:
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>" 
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
  by 
    (
      intro cat_cocone_cf_par_eps_NTMap_app[
        OF is_cat_cocone_axioms cat_coeq_\<gg> cat_coeq_\<ff>
        ]
    )+

lemma (in is_cat_equalizer) cat_eq_Comp_eq: 
  "\<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>"
  "\<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>"
  unfolding cat_eq_2_eps_NTMap_app[symmetric] by simp_all

lemma (in is_cat_coequalizer) cat_coeq_Comp_eq: 
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff>"
  "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<ff> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<gg>"
  unfolding cat_coeq_2_eps_NTMap_app[symmetric] by simp_all


subsubsection\<open>Universal property\<close>

lemma is_cat_equalizerI':
  assumes "\<epsilon> :
    E <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> : \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
    and "\<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
    and "\<And>\<epsilon>' E'. \<epsilon>' :
      E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> : 
      \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
      \<exists>!f'. f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
  shows "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  let ?II = \<open>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<close> and ?II_II = \<open>\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>\<close>
  interpret \<epsilon>: is_cat_cone \<alpha> E ?II \<CC> ?II_II \<epsilon> by (rule assms(1))
  interpret \<CC>: cf_parallel \<alpha> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> \<CC>
    by (rule \<epsilon>.NTDom.HomCod.cat_cf_parallel_cat_equalizer[OF assms(2,3)])
  show ?thesis
  proof(intro is_cat_equalizerI is_cat_limitI' assms(1-3))
    fix u' r' assume prems: "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    interpret u': is_cat_cone \<alpha> r' ?II \<CC> ?II_II u' by (rule prems)
    from assms(4)[OF prems] obtain f'
      where f': "f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E"
        and u'_NTMap_app_\<aa>: "u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
        and unique_f': 
          "\<And>f''.
            \<lbrakk>
              f'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E; 
              u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''
            \<rbrakk> \<Longrightarrow> f'' = f'"
      by metis
    show "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> u' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'"
    proof(intro ex1I conjI; (elim conjE)?)
      show "u' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'"
      proof(rule ntcf_eqI)
        show "u' : cf_const ?II \<CC> r' \<mapsto>\<^sub>C\<^sub>F ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
          by (rule u'.is_ntcf_axioms)
        from f' show "\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f' :
          cf_const ?II \<CC> r' \<mapsto>\<^sub>C\<^sub>F ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
          by 
            (
              cs_concl 
                cs_simp: cat_cs_simps cat_ss_cs_simps 
                cs_intro: cat_cs_intros cat_ss_cs_intros
            )
        have dom_lhs: "\<D>\<^sub>\<circ> (u'\<lparr>NTMap\<rparr>) = ?II\<lparr>Obj\<rparr>"
          unfolding cat_cs_simps by simp
        from f' have dom_rhs:
          "\<D>\<^sub>\<circ> ((\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f')\<lparr>NTMap\<rparr>) = ?II\<lparr>Obj\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        show "u'\<lparr>NTMap\<rparr> = (\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f')\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          fix a assume prems': "a \<in>\<^sub>\<circ> ?II\<lparr>Obj\<rparr>"
          note [cat_parallel_cs_simps] = 
            cat_cone_cf_par_eps_NTMap_app[OF u'.is_cat_cone_axioms assms(2-3)]
            cat_cone_cf_par_eps_NTMap_app[OF assms(1-3)]
            u'_NTMap_app_\<aa>
          from prems' f' assms(2,3) show 
            "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
            by (elim the_cat_parallel_ObjE; simp only:)
              (
                cs_concl 
                  cs_simp: cat_parallel_cs_simps cat_cs_simps
                  cs_intro: cat_cs_intros cat_parallel_cs_intros
              )
        qed (cs_concl cs_intro: V_cs_intros cat_cs_intros)+
      qed simp_all
      fix f'' assume prems'': 
        "f'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E" "u' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f''"
      from prems''(2) have u'_NTMap_a:
        "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        for a 
        by simp
      have "u'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''"  
        using u'_NTMap_a[of \<aa>\<^sub>P\<^sub>L] prems''(1) 
        by 
          (
            cs_prems 
              cs_simp: cat_parallel_cs_simps cat_cs_simps 
              cs_intro: cat_parallel_cs_intros cat_cs_intros
          )
      from unique_f'[OF prems''(1) this] show "f'' = f'".
    qed (rule f')
  qed
qed

lemma is_cat_coequalizerI':
  assumes "\<epsilon> :
    \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E : 
    \<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    and "\<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    and "\<And>\<epsilon>' E'. \<epsilon>' :
      \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E' : 
      \<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<Longrightarrow>
      \<exists>!f'. f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>"
  shows "\<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  let ?op_II = \<open>\<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L\<close> 
    and ?op_II_II = \<open>\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg>\<close>
    and ?II = \<open>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<close>
    and ?II_II = \<open>\<up>\<up>\<rightarrow>\<up>\<up> (op_cat \<CC>) \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>\<close>
  interpret \<epsilon>: is_cat_cocone \<alpha> E ?op_II \<CC> ?op_II_II \<epsilon> by (rule assms(1))
  interpret par: cf_parallel \<alpha> \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L  \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> \<CC>
    by (rule \<epsilon>.NTDom.HomCod.cat_cf_parallel_cat_coequalizer[OF assms(2,3)])
  interpret op_par: cf_parallel \<alpha> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> \<open>op_cat \<CC>\<close>
    by (rule par.cf_parallel_op)
  have assms_4': 
    "\<exists>!f'. f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f'"
    if "\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>" for \<epsilon>' E'
  proof-
    have [cat_op_simps]:
      "f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f' \<longleftrightarrow>
        f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>"
      for f'
      by (intro iffI conjI; (elim conjE)?)
        (
          cs_concl 
            cs_simp: category.op_cat_Comp[symmetric] cat_op_simps cat_cs_simps 
            cs_intro: cat_cs_intros cat_parallel_cs_intros
        )+
    interpret \<epsilon>': is_cat_cone \<alpha> E' ?II \<open>op_cat \<CC>\<close> ?II_II \<epsilon>' by (rule that)
    show ?thesis
      unfolding cat_op_simps
      by 
        (
          rule assms(4)[
            OF \<epsilon>'.is_cat_cocone_op[unfolded cat_op_simps], 
            unfolded cat_op_simps
            ]
        )
  qed
  interpret op_\<epsilon>: is_cat_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<open>op_cat \<CC>\<close> E \<open>op_ntcf \<epsilon>\<close> 
    by 
      (
        rule 
          is_cat_equalizerI'
            [
              OF \<epsilon>.is_cat_cone_op[unfolded cat_op_simps], 
              unfolded cat_op_simps, 
              OF assms(2,3) assms_4'
            ]
      )
  show ?thesis by (rule op_\<epsilon>.is_cat_coequalizer_op[unfolded cat_op_simps])
qed

lemma (in is_cat_equalizer) cat_eq_unique_cone:
  assumes "\<epsilon>' :
    E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> : \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    (is \<open>\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>\<close>)
  shows "\<exists>!f'. f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
proof-
  interpret \<epsilon>': is_cat_cone \<alpha> E' ?II \<CC> ?II_II \<epsilon>' by (rule assms(1))
  from cat_lim_unique_cone[OF assms(1)] obtain f' where f': "f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E"
    and \<epsilon>'_def: "\<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'"
    and unique: 
      "\<lbrakk> f'' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E; \<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'' \<rbrakk> \<Longrightarrow> f'' = f'" 
    for f''
    by auto
  show ?thesis
  proof(intro ex1I conjI; (elim conjE)?)
    show f': "f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E" by (rule f')
    from \<epsilon>'_def have "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = (\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f')\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>"
      by simp
    from this f' show \<epsilon>'_NTMap_app_I: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
      by 
        (
          cs_prems 
            cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_parallel_cs_intros
        )
    fix f'' assume prems: 
      "f'' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E" "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''"
    have "\<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f''"
    proof(rule ntcf_eqI[OF ])
      show "\<epsilon>' : cf_const ?II \<CC> E' \<mapsto>\<^sub>C\<^sub>F ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (rule \<epsilon>'.is_ntcf_axioms)
      from f' prems(1) show "\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'' :
        cf_const ?II \<CC> E' \<mapsto>\<^sub>C\<^sub>F ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      show "\<epsilon>'\<lparr>NTMap\<rparr> = (\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'')\<lparr>NTMap\<rparr>"
      proof(rule vsv_eqI, unfold cat_cs_simps)
        show "vsv ((\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'')\<lparr>NTMap\<rparr>)"
          by (cs_concl cs_intro: cat_cs_intros)
        from prems(1) show 
          "?II\<lparr>Obj\<rparr> = \<D>\<^sub>\<circ> ((\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'')\<lparr>NTMap\<rparr>)"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        fix a assume prems': "a \<in>\<^sub>\<circ> ?II\<lparr>Obj\<rparr>"
        note [cat_cs_simps] = 
          cat_eq_2_eps_NTMap_app
          cat_cone_cf_par_eps_NTMap_app[
            OF \<epsilon>'.is_cat_cone_axioms cf_parallel_\<gg>' cf_parallel_\<ff>'
            ]
        from prems' prems(1) have [cat_cs_simps]: 
          "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''"
          by (elim the_cat_parallel_ObjE; simp only:)
            (
                cs_concl 
                  cs_simp: cat_cs_simps cat_parallel_cs_simps prems(2)
                  cs_intro: cat_cs_intros cat_parallel_cs_intros
            )+
        from prems' prems show 
          "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const ?II \<CC> f'')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      qed auto
    qed simp_all
    from unique[OF prems(1) this] show "f'' = f'" .      
  qed
qed

lemma (in is_cat_equalizer) cat_eq_unique:
  assumes "\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows 
    "\<exists>!f'. f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> \<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> f'"
  by (rule cat_lim_unique[OF is_cat_equalizerD(1)[OF assms]])

lemma (in is_cat_equalizer) cat_eq_unique':
  assumes "\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : E' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
proof-
  interpret \<epsilon>': is_cat_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E' \<epsilon>' by (rule assms(1))
  show ?thesis by (rule cat_eq_unique_cone[OF \<epsilon>'.is_cat_cone_axioms])
qed

lemma (in is_cat_coequalizer) cat_coeq_unique_cocone:
  assumes "\<epsilon>' :
    \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<bb> \<aa> \<ff> \<gg> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E' : \<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    (is \<open>\<epsilon>' : ?II_II >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>c\<^sub>o\<^sub>n\<^sub>e E' : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>\<close>)
  shows "\<exists>!f'. f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>"
proof-
  interpret \<epsilon>': is_cat_cocone \<alpha> E' ?II \<CC> ?II_II \<epsilon>' by (rule assms(1))
  have [cat_op_simps]:
    "f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f' \<longleftrightarrow>
      f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>" 
    for f'
    by (intro iffI conjI; (elim conjE)?)
      (
        cs_concl
          cs_simp: category.op_cat_Comp[symmetric] cat_op_simps cat_cs_simps 
          cs_intro: cat_cs_intros cat_parallel_cs_intros
      )+
  show ?thesis
    by 
      (
        rule is_cat_equalizer.cat_eq_unique_cone[
          OF is_cat_equalizer_op \<epsilon>'.is_cat_cone_op[unfolded cat_op_simps],
          unfolded cat_op_simps
          ]
     )
qed

lemma (in is_cat_coequalizer) cat_coeq_unique:
  assumes "\<epsilon>' : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'.
    f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and>
    \<epsilon>' = ntcf_const (\<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L) \<CC> f' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon>"
  by (rule cat_colim_unique[OF is_cat_coequalizerD(1)[OF assms]])

lemma (in is_cat_coequalizer) cat_coeq_unique':
  assumes "\<epsilon>' : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<exists>!f'. f' : E \<mapsto>\<^bsub>\<CC>\<^esub> E' \<and> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>"
proof-
  interpret \<epsilon>': is_cat_coequalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E' \<epsilon>' by (rule assms(1))
  show ?thesis by (rule cat_coeq_unique_cocone[OF \<epsilon>'.is_cat_cocone_axioms])
qed

lemma cat_equalizer_2_ex_is_arr_isomorphism:
  assumes "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : E' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E"
    and "\<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> f"
proof-
  interpret \<epsilon>: is_cat_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> by (rule assms(1))
  interpret \<epsilon>': is_cat_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E' \<epsilon>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_lim_ex_is_arr_isomorphism[
          OF \<epsilon>.is_cat_limit_axioms \<epsilon>'.is_cat_limit_axioms
          ]
      )
qed

lemma cat_equalizer_2_ex_is_arr_isomorphism':
  assumes "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<epsilon>' : E' <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : E' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E"
    and "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    and "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
proof-
  interpret \<epsilon>: is_cat_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> by (rule assms(1))
  interpret \<epsilon>': is_cat_equalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E' \<epsilon>' by (rule assms(2))
  obtain f where f: "f : E' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E"
    and "j \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<lparr>Obj\<rparr> \<Longrightarrow> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f" for j
    by 
      (
        elim cat_lim_ex_is_arr_isomorphism'[
          OF \<epsilon>.is_cat_limit_axioms \<epsilon>'.is_cat_limit_axioms
          ]
      )
  then have 
    "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    unfolding the_cat_parallel_components by auto
  with f show ?thesis using that by simp
qed

lemma cat_coequalizer_2_ex_is_arr_isomorphism:
  assumes "\<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<epsilon>' : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : E \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E'" 
    and "\<epsilon>' = ntcf_const (\<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L)  \<CC> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon>"
proof-
  interpret \<epsilon>: is_cat_coequalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> by (rule assms(1))
  interpret \<epsilon>': is_cat_coequalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E' \<epsilon>' by (rule assms(2))
  from that show ?thesis
    by 
      (
        elim cat_colim_ex_is_arr_isomorphism[
          OF \<epsilon>.is_cat_colimit_axioms \<epsilon>'.is_cat_colimit_axioms
          ]
      )
qed

lemma cat_coequalizer_2_ex_is_arr_isomorphism':
  assumes "\<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<epsilon>' : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E' : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains f where "f : E \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E'" 
    and "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>"
    and "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr>"
proof-
  interpret \<epsilon>: is_cat_coequalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> by (rule assms(1))
  interpret \<epsilon>': is_cat_coequalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E' \<epsilon>' by (rule assms(2))
  obtain f where f: "f : E \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> E'"
    and "j \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<bb>\<^sub>P\<^sub>L \<aa>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L\<lparr>Obj\<rparr> \<Longrightarrow> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>j\<rparr>" for j
    by 
      (
        elim cat_colim_ex_is_arr_isomorphism'[
          OF \<epsilon>.is_cat_colimit_axioms \<epsilon>'.is_cat_colimit_axioms
          ]
      )
  then have 
    "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>"
    "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr> = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<bb>\<^sub>P\<^sub>L\<rparr>"
    unfolding the_cat_parallel_components by auto
  with f show ?thesis using that by simp
qed



subsection\<open>Projection cone\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition ntcf_obj_prod_base :: "V \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "ntcf_obj_prod_base \<CC> I F P f =
    [(\<lambda>j\<in>\<^sub>\<circ>:\<^sub>C I\<lparr>Obj\<rparr>. f j), cf_const (:\<^sub>C I) \<CC> P, :\<rightarrow>: I F \<CC>, :\<^sub>C I, \<CC>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_obj_prod_base_components:
  shows "ntcf_obj_prod_base \<CC> I F P f\<lparr>NTMap\<rparr> = (\<lambda>j\<in>\<^sub>\<circ>:\<^sub>C I\<lparr>Obj\<rparr>. f j)"
    and "ntcf_obj_prod_base \<CC> I F P f\<lparr>NTDom\<rparr> = cf_const (:\<^sub>C I) \<CC> P"
    and "ntcf_obj_prod_base \<CC> I F P f\<lparr>NTCod\<rparr> = :\<rightarrow>: I F \<CC>"
    and "ntcf_obj_prod_base \<CC> I F P f\<lparr>NTDGDom\<rparr> = :\<^sub>C I"
    and "ntcf_obj_prod_base \<CC> I F P f\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding ntcf_obj_prod_base_def nt_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda ntcf_obj_prod_base_components(1)
  |vsv ntcf_obj_prod_base_NTMap_vsv[cat_cs_intros]|
  |vdomain ntcf_obj_prod_base_NTMap_vdomain[cat_cs_simps]|
  |app ntcf_obj_prod_base_NTMap_app[cat_cs_simps]|


subsubsection\<open>Projection natural transformation is a cone\<close>

lemma (in tm_cf_discrete) tm_cf_discrete_ntcf_obj_prod_base_is_cat_cone:
  assumes "P \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "\<And>a. a \<in>\<^sub>\<circ> I \<Longrightarrow> f a : P \<mapsto>\<^bsub>\<CC>\<^esub> F a"
  shows "ntcf_obj_prod_base \<CC> I F P f : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: I F \<CC> : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_cat_coneI is_tm_ntcfI' is_ntcfI')
  from assms(2) have [cat_cs_intros]: 
    "\<lbrakk> a \<in>\<^sub>\<circ> I; P' = P; Fa = F a \<rbrakk> \<Longrightarrow> f a : P' \<mapsto>\<^bsub>\<CC>\<^esub> Fa" for a P' Fa 
    by simp
  show "vfsequence (ntcf_obj_prod_base \<CC> I F P f)"
    unfolding ntcf_obj_prod_base_def by auto
  show "vcard (ntcf_obj_prod_base \<CC> I F P f) = 5\<^sub>\<nat>"
    unfolding ntcf_obj_prod_base_def by (auto simp: nat_omega_simps)
  from assms show "cf_const (:\<^sub>C I) \<CC> P : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by 
      (
        cs_concl
          cs_intro: 
            cf_discrete_vdomain_vsubset_Vset 
            cat_discrete_cs_intros 
            cat_cs_intros
      )
  show ":\<rightarrow>: I F \<CC> : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_discrete_cs_intros)
  show "ntcf_obj_prod_base \<CC> I F P f\<lparr>NTMap\<rparr>\<lparr>a\<rparr> :
    cf_const (:\<^sub>C I) \<CC> P\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> :\<rightarrow>: I F \<CC>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    if "a \<in>\<^sub>\<circ> :\<^sub>C I\<lparr>Obj\<rparr>" for a
  proof-
    from that have "a \<in>\<^sub>\<circ> I" unfolding the_cat_discrete_components by simp
    from that this show ?thesis
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_discrete_cs_simps cs_intro: cat_cs_intros
        )
  qed
  show 
    "ntcf_obj_prod_base \<CC> I F P f\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
      cf_const (:\<^sub>C I) \<CC> P\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> =
      :\<rightarrow>: I F \<CC>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ntcf_obj_prod_base \<CC> I F P f\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
    if "g : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> b" for a b g
  proof-
    note g = the_cat_discrete_is_arrD[OF that]
    from that g(4)[unfolded g(7-9)] g(1)[unfolded g(7-9)] show ?thesis
      unfolding g(7-9)
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_discrete_cs_simps 
            cs_intro: 
              cf_discrete_vdomain_vsubset_Vset 
              cat_cs_intros cat_discrete_cs_intros
        )
  qed
  from assms(1) show "cf_const (:\<^sub>C I) \<CC> P : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    by 
      (
        cs_concl cs_intro: 
          cat_cs_intros cat_small_cs_intros cat_small_discrete_cs_intros
      )
qed 
  (
    auto simp: 
      assms 
      ntcf_obj_prod_base_components 
      tm_cf_discrete_the_cf_discrete_is_tm_functor
  )

lemma (in tm_cf_discrete) tm_cf_discrete_ntcf_obj_prod_base_is_cat_obj_prod:
  assumes "P \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "\<And>a. a \<in>\<^sub>\<circ> I \<Longrightarrow> f a : P \<mapsto>\<^bsub>\<CC>\<^esub> F a"
    and "\<And>u' r'.
      \<lbrakk> u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: I F \<CC> : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<rbrakk> \<Longrightarrow> 
        \<exists>!f'.
          f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P \<and>
          u' = ntcf_obj_prod_base \<CC> I F P f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (:\<^sub>C I) \<CC> f'"
  shows "ntcf_obj_prod_base \<CC> I F P f : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> F : I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof
  (
    intro 
      is_cat_obj_prodI 
      is_cat_limitI' 
      tm_cf_discrete_ntcf_obj_prod_base_is_cat_cone[OF assms(1,2), simplified] 
      assms(1,3)
  )
  show "cf_discrete \<alpha> I F \<CC>"
    by (cs_concl cs_intro: cat_small_discrete_cs_intros)
qed



subsection\<open>Equalizer cone\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition ntcf_equalizer_base :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e =
    [
      (\<lambda>x\<in>\<^sub>\<circ>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<lparr>Obj\<rparr>. e x),
      cf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> E,
      \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>,
      \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L,
      \<CC>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_equalizer_base_components:
  shows "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTMap\<rparr> =
    (\<lambda>x\<in>\<^sub>\<circ>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<lparr>Obj\<rparr>. e x)"
    and [cat_lim_cs_simps]: "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTDom\<rparr> =
      cf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> E"
    and [cat_lim_cs_simps]: "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTCod\<rparr> =
      \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>"
    and [cat_lim_cs_simps]: 
      "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTDGDom\<rparr> = \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L"
    and [cat_lim_cs_simps]: 
      "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding ntcf_equalizer_base_def nt_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda ntcf_equalizer_base_components(1)
  |vsv ntcf_equalizer_base_NTMap_vsv[cat_lim_cs_intros]|
  |vdomain ntcf_equalizer_base_NTMap_vdomain[cat_lim_cs_simps]|
  |app ntcf_equalizer_base_NTMap_app[cat_lim_cs_simps]|


subsubsection\<open>Equalizer cone is a cone\<close>

lemma (in category) cat_ntcf_equalizer_base_is_cat_cone:
  assumes "e \<aa>\<^sub>P\<^sub>L : E \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    and "e \<bb>\<^sub>P\<^sub>L : E \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
    and "e \<bb>\<^sub>P\<^sub>L = \<gg> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> e \<aa>\<^sub>P\<^sub>L"
    and "e \<bb>\<^sub>P\<^sub>L = \<ff> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> e \<aa>\<^sub>P\<^sub>L"
    and "\<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
    and "\<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
  shows "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e :
    E <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> :
    \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret par: cf_parallel \<alpha> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> \<CC> 
    by (intro cf_parallelI cat_parallelI assms(5,6))
      (simp_all add: cat_parallel_cs_intros cat_cs_intros)
  show ?thesis
  proof(intro is_cat_coneI is_tm_ntcfI' is_ntcfI')
    show "vfsequence (ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e)"
      unfolding ntcf_equalizer_base_def by auto
    show "vcard (ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e) = 5\<^sub>\<nat>"
      unfolding ntcf_equalizer_base_def by (simp add: nat_omega_simps)
    from assms(2) show 
      "cf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> E : \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_small_cs_intros cat_parallel_cs_intros cat_cs_intros
        )
    then show "cf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> E : \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: cat_small_cs_intros)
    from assms show 
      "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> : \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_parallel_cs_intros)
    then show "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff> : \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: cat_small_cs_intros)
    show 
      "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTMap\<rparr>\<lparr>i\<rparr> :
        cf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> E\<lparr>ObjMap\<rparr>\<lparr>i\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub>
        \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>"
      if "i \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<lparr>Obj\<rparr>" for i 
    proof-
      from that assms(1,2,5,6) show ?thesis
        by (elim the_cat_parallel_ObjE; simp only:)
          ( 
            cs_concl 
              cs_simp: cat_lim_cs_simps cat_cs_simps cat_parallel_cs_simps 
              cs_intro: cat_cs_intros cat_parallel_cs_intros
          )
    qed
    show 
      "ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTMap\<rparr>\<lparr>b'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
        cf_const (\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L) \<CC> E\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> =
          \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L \<aa> \<bb> \<gg> \<ff>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
          ntcf_equalizer_base \<CC> \<aa> \<bb> \<gg> \<ff> E e\<lparr>NTMap\<rparr>\<lparr>a'\<rparr>"
      if "f' : a' \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<^esub> b'" for a' b' f'
      using that assms(1,2,5,6)
      by (elim par.the_cat_parallel_is_arrE; simp only:)
        (
          cs_concl 
            cs_simp: 
              cat_cs_simps 
              cat_lim_cs_simps 
              cat_parallel_cs_simps 
              assms(3,4)[symmetric]
            cs_intro: cat_parallel_cs_intros
        )+
  qed 
    (
      use assms(2) in 
        \<open>
          cs_concl
            cs_intro: cat_lim_cs_intros cat_cs_intros 
            cs_simp: cat_lim_cs_simps
        \<close>
    )+
qed



subsection\<open>Limits by products and equalizers\<close>

lemma cat_limit_of_cat_prod_obj_and_cat_equalizer:
  \<comment>\<open>See Theorem 1 in Chapter V-2 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>\<aa> \<bb> \<gg> \<ff>. \<lbrakk> \<ff> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>; \<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb> \<rbrakk> \<Longrightarrow>
      \<exists>E \<epsilon>. \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>A. tm_cf_discrete \<alpha> (\<JJ>\<lparr>Obj\<rparr>) A \<CC> \<Longrightarrow>
      \<exists>P \<pi>. \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : \<JJ>\<lparr>Obj\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>A. tm_cf_discrete \<alpha> (\<JJ>\<lparr>Arr\<rparr>) A \<CC> \<Longrightarrow>
      \<exists>P \<pi>. \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : \<JJ>\<lparr>Arr\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains r u where "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-

  let ?L =\<open>\<lambda>u. \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>u\<rparr>\<rparr>\<close> and ?R =\<open>\<lambda>i. \<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>\<close>
  
  interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<CC> \<FF> by (rule assms(1))

  have "?R j \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
    by (cs_concl cs_intro: cat_cs_intros that)

  have "tm_cf_discrete \<alpha> (\<JJ>\<lparr>Obj\<rparr>) ?R \<CC>"
  proof(intro tm_cf_discreteI)
    show "\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" if "i \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for i
      by (cs_concl cs_intro: cat_cs_intros that)
    show "VLambda (\<JJ>\<lparr>Obj\<rparr>) ?R \<in>\<^sub>\<circ> Vset \<alpha>"
    proof(rule vbrelation.vbrelation_Limit_in_VsetI)
      show "\<R>\<^sub>\<circ> (VLambda (\<JJ>\<lparr>Obj\<rparr>) ?R) \<in>\<^sub>\<circ> Vset \<alpha>"
      proof-
        have "\<R>\<^sub>\<circ> (VLambda (\<JJ>\<lparr>Obj\<rparr>) ?R) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)"
          by (auto simp: \<FF>.cf_ObjMap_vdomain)
        moreover have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
          by (force intro: vrange_in_VsetI \<FF>.tm_cf_ObjMap_in_Vset)
        ultimately show ?thesis by auto
      qed
    qed (auto simp: cat_small_cs_intros)
    show "(\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    proof(rule vbrelation.vbrelation_Limit_in_VsetI)
      show "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
      proof-
        have "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr>\<rparr>) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
        proof(rule vrange_VLambda_vsubset)
          fix x assume x: "x \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
          then have "\<JJ>\<lparr>CId\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
            by (auto intro: cat_cs_intros simp: cat_cs_simps)
          moreover from x have "\<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<JJ>\<lparr>CId\<rparr>\<lparr>x\<rparr>\<rparr>"
            by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
          ultimately show "\<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
            by (simp add: \<FF>.ArrMap.vsv_vimageI2)
        qed
        moreover have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
          by (force intro: vrange_in_VsetI \<FF>.tm_cf_ArrMap_in_Vset)
        ultimately show ?thesis by auto
      qed
    qed (auto simp: cat_small_cs_intros)
  qed (auto intro: cat_cs_intros)

  from assms(3)[where A=\<open>?R\<close>, OF this] obtain P\<^sub>O \<pi>\<^sub>O
    where \<pi>\<^sub>O: "\<pi>\<^sub>O : P\<^sub>O <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> ?R : \<JJ>\<lparr>Obj\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by clarsimp

  interpret \<pi>\<^sub>O: is_cat_obj_prod \<alpha> \<open>\<JJ>\<lparr>Obj\<rparr>\<close> ?R \<CC> P\<^sub>O \<pi>\<^sub>O by (rule \<pi>\<^sub>O)

  have P\<^sub>O: "P\<^sub>O \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (intro \<pi>\<^sub>O.cat_cone_obj)

  have "?L u \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" if "u \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>" for u
  proof-
    from that obtain a b where "u : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
    then show ?thesis by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed

  have tm_cf_discrete: "tm_cf_discrete \<alpha> (\<JJ>\<lparr>Arr\<rparr>) ?L \<CC>"
  proof(intro tm_cf_discreteI)
    show "\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" if "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>" for f
    proof-
      from that obtain a b where "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
      then show ?thesis 
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    qed
 
    show "(\<lambda>u\<in>\<^sub>\<circ>\<JJ>\<lparr>Arr\<rparr>. \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>u\<rparr>\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    proof(rule vbrelation.vbrelation_Limit_in_VsetI)
      show "\<R>\<^sub>\<circ> (\<lambda>u\<in>\<^sub>\<circ>\<JJ>\<lparr>Arr\<rparr>. ?L u) \<in>\<^sub>\<circ> Vset \<alpha>"
      proof-
        have "\<R>\<^sub>\<circ> (\<lambda>u\<in>\<^sub>\<circ>\<JJ>\<lparr>Arr\<rparr>. ?L u) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)"
        proof(rule vrange_VLambda_vsubset)
          fix f assume "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>"
          then obtain a b where "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
          then show "\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)"
            by 
              (
                cs_concl 
                  cs_simp: cat_cs_simps cs_intro: V_cs_intros cat_cs_intros
              )
        qed
        moreover have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
          by (auto intro: vrange_in_VsetI \<FF>.tm_cf_ObjMap_in_Vset)
        ultimately show ?thesis by auto
      qed
    qed (auto simp: cat_small_cs_intros)

    show "(\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Arr\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>i\<rparr>\<rparr>\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    proof(rule vbrelation.vbrelation_Limit_in_VsetI)
      show "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Arr\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>i\<rparr>\<rparr>\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
      proof-
        have "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Arr\<rparr>. \<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>i\<rparr>\<rparr>\<rparr>) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
        proof(rule vrange_VLambda_vsubset)
          fix f assume "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>"
          then obtain a b where f: "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
          then have "\<JJ>\<lparr>CId\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
            by (auto intro: cat_cs_intros simp: cat_cs_simps)
          moreover from f have 
            "\<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr>\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<JJ>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rparr>"
            by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
          ultimately show "\<CC>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr>\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
            by (simp add: \<FF>.ArrMap.vsv_vimageI2)
        qed
        moreover have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
          by (force intro: vrange_in_VsetI \<FF>.tm_cf_ArrMap_in_Vset)
        ultimately show ?thesis by auto
      qed
    qed (auto simp: cat_small_cs_intros)
  qed (auto intro: cat_cs_intros)

  from assms(4)[where A=\<open>?L\<close>, OF this, simplified] obtain P\<^sub>A \<pi>\<^sub>A
    where \<pi>\<^sub>A: "\<pi>\<^sub>A : P\<^sub>A <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> ?L : \<JJ>\<lparr>Arr\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by auto

  interpret \<pi>\<^sub>A: is_cat_obj_prod \<alpha> \<open>\<JJ>\<lparr>Arr\<rparr>\<close> ?L \<CC> P\<^sub>A \<pi>\<^sub>A by (rule \<pi>\<^sub>A)

  let ?F = \<open>\<lambda>u. \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>u\<rparr>\<rparr>\<close> and ?f = \<open>\<lambda>u. \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>u\<rparr>\<rparr>\<close> 
  let ?\<pi>\<^sub>O' = \<open>ntcf_obj_prod_base \<CC> (:\<^sub>C (\<JJ>\<lparr>Arr\<rparr>)\<lparr>Obj\<rparr>) ?F P\<^sub>O ?f\<close>

  have \<pi>\<^sub>O': "?\<pi>\<^sub>O' :
    P\<^sub>O <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: (\<JJ>\<lparr>Arr\<rparr>) (\<lambda>u. \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>u\<rparr>\<rparr>) \<CC> :
    :\<^sub>C (\<JJ>\<lparr>Arr\<rparr>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    unfolding the_cat_discrete_components(1)
  proof
    (
      intro 
        tm_cf_discrete.tm_cf_discrete_ntcf_obj_prod_base_is_cat_cone 
        tm_cf_discrete
    )
    fix f assume "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>"
    then obtain a b where "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
    then show "\<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr> : P\<^sub>O \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr>"
      by 
        (
          cs_concl
            cs_simp:
              the_cat_discrete_components(1) cat_discrete_cs_simps cat_cs_simps
            cs_intro: cat_cs_intros
        )
  qed (intro P\<^sub>O)

  from \<pi>\<^sub>A.cat_obj_prod_unique_cone'[OF \<pi>\<^sub>O'] obtain f' 
    where f': "f' : P\<^sub>O \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A"
      and \<pi>\<^sub>O'_NTMap_app: 
        "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr> \<Longrightarrow> ?\<pi>\<^sub>O'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
      and unique_f':
        "\<lbrakk>
          f'' : P\<^sub>O \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A;
          \<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr> \<Longrightarrow> ?\<pi>\<^sub>O'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''
         \<rbrakk> \<Longrightarrow> f'' = f'"
      for f''
    by metis

  have \<pi>\<^sub>O_NTMap_app_Cod: 
    "\<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>b\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'" if "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" for f a b 
  proof-
    from that have "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>" by auto
    from \<pi>\<^sub>O'_NTMap_app[OF this] that show ?thesis
      by 
        (
          cs_prems 
            cs_simp: cat_cs_simps the_cat_discrete_components(1)
            cs_intro: cat_cs_intros
        )
  qed

  from this[symmetric] have \<pi>\<^sub>A_NTMap_Comp_app: 
    "\<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> q) = \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> q" 
    if "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" and "q : c \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>O" for q f a b c 
    using that f'
    by (intro \<FF>.HomCod.cat_assoc_helper)
      (
        cs_concl 
          cs_simp: 
            cat_cs_simps cat_discrete_cs_simps the_cat_discrete_components(1)
          cs_intro: cat_cs_intros
      )+

  let ?g = \<open>\<lambda>u. \<FF>\<lparr>ArrMap\<rparr>\<lparr>u\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>\<JJ>\<lparr>Dom\<rparr>\<lparr>u\<rparr>\<rparr>\<close> 
  let ?\<pi>\<^sub>O'' = \<open>ntcf_obj_prod_base \<CC> (:\<^sub>C (\<JJ>\<lparr>Arr\<rparr>)\<lparr>Obj\<rparr>) ?F P\<^sub>O ?g\<close>
  
  have \<pi>\<^sub>O'': "?\<pi>\<^sub>O'' : P\<^sub>O <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: (\<JJ>\<lparr>Arr\<rparr>) ?L \<CC> : :\<^sub>C (\<JJ>\<lparr>Arr\<rparr>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    unfolding the_cat_discrete_components(1)
  proof
    (
      intro 
        tm_cf_discrete.tm_cf_discrete_ntcf_obj_prod_base_is_cat_cone  
        tm_cf_discrete
    )
    show "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>\<JJ>\<lparr>Dom\<rparr>\<lparr>f\<rparr>\<rparr> : P\<^sub>O \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr>"
      if "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>" for f
    proof-
      from that obtain a b where "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b"  by auto
      then show ?thesis
        by  
          (
            cs_concl 
              cs_simp: 
                cat_cs_simps cat_discrete_cs_simps 
                the_cat_discrete_components(1) 
              cs_intro: cat_cs_intros
          )
    qed
  qed (intro P\<^sub>O)

  from \<pi>\<^sub>A.cat_obj_prod_unique_cone'[OF \<pi>\<^sub>O''] obtain g' 
    where g': "g' : P\<^sub>O \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A"
      and \<pi>\<^sub>O''_NTMap_app: 
        "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr> \<Longrightarrow> ?\<pi>\<^sub>O''\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g'"
      and unique_g':
        "\<lbrakk>
          g'' : P\<^sub>O \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A;
          \<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr> \<Longrightarrow> ?\<pi>\<^sub>O''\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g''
         \<rbrakk> \<Longrightarrow> g'' = g'"
      for g''
    by (metis (lifting))

  have "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g'" 
    if "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" for f a b 
  proof-
    from that have "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>" by auto
    from \<pi>\<^sub>O''_NTMap_app[OF this] that show ?thesis
      by 
        (
          cs_prems 
            cs_simp: cat_cs_simps the_cat_discrete_components(1)
            cs_intro: cat_cs_intros
        )
  qed
  then have \<pi>\<^sub>O_NTMap_app_Dom: 
    "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> q) =
      (\<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g') \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> q" 
    if "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" and "q : c \<mapsto>\<^bsub>\<CC>\<^esub>  P\<^sub>O" for q f a b c 
    using that g' 
    by (intro \<FF>.HomCod.cat_assoc_helper)
      (
        cs_concl 
          cs_simp: 
            cat_cs_simps cat_discrete_cs_simps the_cat_discrete_components(1)
          cs_intro: cat_cs_intros
      )

  from assms(2)[OF f' g'] obtain E \<epsilon> where \<epsilon>: 
    "\<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (P\<^sub>O,P\<^sub>A,g',f') : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by clarsimp

  interpret \<epsilon>: is_cat_equalizer \<alpha> P\<^sub>O P\<^sub>A g' f' \<CC> E \<epsilon> by (rule \<epsilon>)

  define \<mu> where "\<mu> =
    [(\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>), cf_const \<JJ> \<CC> E, \<FF>, \<JJ>, \<CC>]\<^sub>\<circ>"

  have \<mu>_components:
    "\<mu>\<lparr>NTMap\<rparr> = (\<lambda>i\<in>\<^sub>\<circ>\<JJ>\<lparr>Obj\<rparr>. \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>)"
    "\<mu>\<lparr>NTDom\<rparr> = cf_const \<JJ> \<CC> E"
    "\<mu>\<lparr>NTCod\<rparr> = \<FF>"
    "\<mu>\<lparr>NTDGDom\<rparr> = \<JJ>"
    "\<mu>\<lparr>NTDGCod\<rparr> = \<CC>"
    unfolding \<mu>_def nt_field_simps by (simp_all add: nat_omega_simps)

  have [cat_cs_simps]: 
    "\<mu>\<lparr>NTMap\<rparr>\<lparr>i\<rparr> = \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr>" if "i \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" 
    for i
    using that unfolding \<mu>_components by simp

  have "\<mu> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  proof(intro is_cat_limitI')

    show \<mu>: "\<mu> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    proof(intro is_cat_coneI is_tm_ntcfI' is_ntcfI')
      show "vfsequence \<mu>" unfolding \<mu>_def by simp 
      show "vcard \<mu> = 5\<^sub>\<nat>" unfolding \<mu>_def by (simp add: nat_omega_simps)
      show "cf_const \<JJ> \<CC> E : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_intro: cat_cs_intros cat_lim_cs_intros)
      show "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" by (cs_concl cs_intro: cat_cs_intros)
      show "\<mu>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : cf_const \<JJ> \<CC> E\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        if "a \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for a
        using that
        by 
          (
            cs_concl 
              cs_simp: 
                cat_cs_simps 
                cat_discrete_cs_simps 
                cat_parallel_cs_simps 
                the_cat_discrete_components(1) 
              cs_intro: cat_cs_intros cat_lim_cs_intros cat_parallel_cs_intros
          )
      show 
        "\<mu>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> cf_const \<JJ> \<CC> E\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
          \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<mu>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        if "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" for a b f
        using that \<epsilon> g' f' 
        by 
          (
            cs_concl
              cs_simp:
                cat_parallel_cs_simps
                cat_cs_simps 
                the_cat_discrete_components(1) 
                \<pi>\<^sub>O_NTMap_app_Cod 
                \<pi>\<^sub>O_NTMap_app_Dom 
                \<epsilon>.cat_eq_Comp_eq(1) 
              cs_intro: cat_lim_cs_intros cat_cs_intros cat_parallel_cs_intros
          )
      show "cf_const \<JJ> \<CC> E : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
        by 
          (
            cs_concl cs_simp: cs_intro: 
              cat_lim_cs_intros cat_cs_intros cat_small_cs_intros
          )
      show "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_simp: cs_intro: cat_small_cs_intros)

    qed (auto simp: \<mu>_components cat_lim_cs_intros)

    interpret \<mu>: is_cat_cone \<alpha> E \<JJ> \<CC> \<FF> \<mu> by (rule \<mu>)

    show "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> u' = \<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
      if "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" for u' r'
    proof-

      interpret u': is_cat_cone \<alpha> r' \<JJ> \<CC> \<FF> u' by (rule that)

      let ?u' = \<open>\<lambda>j. u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr>\<close> 
      let ?\<pi>' = \<open>ntcf_obj_prod_base \<CC> (\<JJ>\<lparr>Obj\<rparr>) ?R r' ?u'\<close>

      have \<pi>'_NTMap_app: "?\<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr>" if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
        using that 
        unfolding ntcf_obj_prod_base_components the_cat_discrete_components 
        by auto

      have \<pi>': "?\<pi>' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: (\<JJ>\<lparr>Obj\<rparr>) ?R \<CC> : :\<^sub>C (\<JJ>\<lparr>Obj\<rparr>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        unfolding the_cat_discrete_components(1)
      proof(intro tm_cf_discrete.tm_cf_discrete_ntcf_obj_prod_base_is_cat_cone)
        show "tm_cf_discrete \<alpha> (\<JJ>\<lparr>Obj\<rparr>) ?R \<CC>"
        proof(intro tm_cf_discreteI)
          show "\<FF>\<lparr>ObjMap\<rparr>\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" if "i \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for i
            using that 
            by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        qed
          (
            auto intro: 
              cat_cs_intros
              P\<^sub>O 
              \<pi>\<^sub>O.NTCod.tm_cf_ArrMap_in_Vset[unfolded the_cf_discrete_components]
              \<pi>\<^sub>O.NTCod.tm_cf_ObjMap_in_Vset[unfolded the_cf_discrete_components]
          )
        show "u'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> : r' \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>j\<rparr>" if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
          using that by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      qed (auto simp: cat_lim_cs_intros)

      from \<pi>\<^sub>O.cat_obj_prod_unique_cone'[OF this] obtain h' 
        where h': "h' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>O"
          and \<pi>'_NTMap_app': 
            "\<And>j. j \<in>\<^sub>\<circ> (\<JJ>\<lparr>Obj\<rparr>) \<Longrightarrow> ?\<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h'"
          and unique_h': "\<And>h''.
            \<lbrakk> 
              h'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>O;
              \<And>j. j \<in>\<^sub>\<circ> (\<JJ>\<lparr>Obj\<rparr>) \<Longrightarrow> ?\<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h'' 
            \<rbrakk> \<Longrightarrow> h'' = h'"
        by metis

      interpret \<pi>':
        is_cat_cone \<alpha> r' \<open>:\<^sub>C (\<JJ>\<lparr>Obj\<rparr>)\<close> \<CC> \<open>:\<rightarrow>: (\<JJ>\<lparr>Obj\<rparr>) (app (\<FF>\<lparr>ObjMap\<rparr>)) \<CC>\<close> ?\<pi>'
        by (rule \<pi>')

      let ?u'' = \<open>\<lambda>u. u'\<lparr>NTMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>u\<rparr>\<rparr>\<close> 
      let ?\<pi>'' = \<open>ntcf_obj_prod_base \<CC> (\<JJ>\<lparr>Arr\<rparr>) ?L r' ?u''\<close>

      have \<pi>''_NTMap_app: "?\<pi>''\<lparr>NTMap\<rparr>\<lparr>f\<rparr> = u'\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
        if "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" for f a b 
        using that 
        unfolding ntcf_obj_prod_base_components the_cat_discrete_components 
        by (cs_concl cs_simp: V_cs_simps cat_cs_simps cs_intro: cat_cs_intros)
      
      have \<pi>'': "?\<pi>'' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e :\<rightarrow>: (\<JJ>\<lparr>Arr\<rparr>) ?L \<CC> : :\<^sub>C (\<JJ>\<lparr>Arr\<rparr>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        unfolding the_cat_discrete_components(1)
      proof
        (
          intro 
            tm_cf_discrete.tm_cf_discrete_ntcf_obj_prod_base_is_cat_cone 
            tm_cf_discrete
        )
        fix f assume "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>"
        then obtain a b where "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
        then show "u'\<lparr>NTMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr> : r' \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<JJ>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      qed (simp add: cat_lim_cs_intros)

      from \<pi>\<^sub>A.cat_obj_prod_unique_cone'[OF this] obtain h'' 
        where h'': "h'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A"
          and \<pi>''_NTMap_app': 
            "\<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr> \<Longrightarrow> ?\<pi>''\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h''"
          and unique_h'': "\<And>h'''.
            \<lbrakk> 
              h''' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A;
              \<And>j. j \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr> \<Longrightarrow> ?\<pi>''\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h''' 
            \<rbrakk> \<Longrightarrow> h''' = h''"
        by metis

      interpret \<pi>'': is_cat_cone \<alpha> r' \<open>:\<^sub>C (\<JJ>\<lparr>Arr\<rparr>)\<close> \<CC> \<open>:\<rightarrow>: (\<JJ>\<lparr>Arr\<rparr>) ?L \<CC>\<close> ?\<pi>''
        by (rule \<pi>'')

      have g'h'_f'h': "g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h'"  
      proof-

        from g' h' have g'h': "g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        from f' h' have f'h': "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>A"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

        have "?\<pi>''\<lparr>NTMap\<rparr>\<lparr>f\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h')"
          if "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>" for f
        proof-
          from that obtain a b where f: "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
          then have "?\<pi>''\<lparr>NTMap\<rparr>\<lparr>f\<rparr> = u'\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
            by (cs_concl cs_simp: \<pi>''_NTMap_app cat_cs_simps)
          also from f have "\<dots> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<pi>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
            by 
              (
                cs_concl 
                  cs_simp: \<pi>'_NTMap_app cat_lim_cs_simps cs_intro: cat_cs_intros
              )
          also from f g' h' have "\<dots> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h')" 
            by 
              (
                cs_concl
                  cs_simp: 
                    cat_cs_simps 
                    cat_discrete_cs_simps
                    the_cat_discrete_components(1) 
                    \<pi>'_NTMap_app'
                    \<pi>\<^sub>O_NTMap_app_Dom 
                  cs_intro: cat_cs_intros
              )
          finally show ?thesis by simp
        qed
          
        from unique_h''[OF g'h' this, simplified] have g'h'_h'': 
          "g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h' = h''".
        have "?\<pi>''\<lparr>NTMap\<rparr>\<lparr>f\<rparr> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h')"
          if "f \<in>\<^sub>\<circ> \<JJ>\<lparr>Arr\<rparr>" for f
        proof-
          from that obtain a b where f: "f : a \<mapsto>\<^bsub>\<JJ>\<^esub> b" by auto
          then have "?\<pi>''\<lparr>NTMap\<rparr>\<lparr>f\<rparr> = u'\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
            by (cs_concl cs_simp: \<pi>''_NTMap_app cat_cs_simps)
          also from f have "\<dots> = ?\<pi>'\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
            by (cs_concl cs_simp: \<pi>'_NTMap_app cs_intro: cat_cs_intros)
          also from f have "\<dots> = \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h'"
            by (cs_concl cs_simp: \<pi>'_NTMap_app' cs_intro: cat_cs_intros)
          also from f g' h' have "\<dots> = (\<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f') \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h'"
            by (cs_concl cs_simp: \<pi>\<^sub>O_NTMap_app_Cod cs_intro: cat_cs_intros)
          also from that f' h' have "\<dots> = \<pi>\<^sub>A\<lparr>NTMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h')"
            by 
              (
                cs_concl
                  cs_simp: cat_cs_simps the_cat_discrete_components(1) 
                  cs_intro: cat_cs_intros
               )
          finally show ?thesis by simp
        qed
        from unique_h''[OF f'h' this, simplified] have f'h'_h'': 
          "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h' = h''".
        from g'h'_h'' f'h'_h'' show ?thesis by simp
      qed

      let ?II = \<open>\<up>\<up>\<^sub>C \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L\<close> 
        and ?II_II = \<open>\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L P\<^sub>O P\<^sub>A g' f'\<close>

    define \<epsilon>' where "\<epsilon>' =
      [
        (\<lambda>f\<in>\<^sub>\<circ>?II\<lparr>Obj\<rparr>. (f = \<aa>\<^sub>P\<^sub>L ? h' : (f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h'))),
        cf_const ?II \<CC> r',
        ?II_II,
        ?II,
        \<CC>
      ]\<^sub>\<circ>"

    have \<epsilon>'_components: 
      "\<epsilon>'\<lparr>NTMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>?II\<lparr>Obj\<rparr>. (f = \<aa>\<^sub>P\<^sub>L ? h' : (f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h')))"
      "\<epsilon>'\<lparr>NTDom\<rparr> = cf_const ?II \<CC> r'"
      "\<epsilon>'\<lparr>NTCod\<rparr> = ?II_II"
      "\<epsilon>'\<lparr>NTDGDom\<rparr> = ?II"
      "\<epsilon>'\<lparr>NTDGCod\<rparr> = \<CC>"
      unfolding \<epsilon>'_def nt_field_simps by (simp_all add: nat_omega_simps)

    have \<epsilon>'_NTMap_app_I2: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = h'" if "x = \<aa>\<^sub>P\<^sub>L" for x 
    proof-
      have "x \<in>\<^sub>\<circ> ?II\<lparr>Obj\<rparr>"
        unfolding that by (cs_concl cs_intro: cat_parallel_cs_intros)
      then show ?thesis unfolding \<epsilon>'_components that by simp
    qed

    have \<epsilon>'_NTMap_app_sI2: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h'" if "x = \<bb>\<^sub>P\<^sub>L" for x 
    proof-      
      have "x \<in>\<^sub>\<circ> ?II\<lparr>Obj\<rparr>"
        unfolding that by (cs_concl cs_intro: cat_parallel_cs_intros)
      with \<epsilon>.cat_parallel_\<aa>\<bb> show ?thesis
        unfolding \<epsilon>'_components by (cs_concl cs_simp: V_cs_simps that)
    qed

    interpret par: cf_parallel \<alpha> \<aa>\<^sub>P\<^sub>L \<bb>\<^sub>P\<^sub>L \<gg>\<^sub>P\<^sub>L \<ff>\<^sub>P\<^sub>L P\<^sub>O P\<^sub>A g' f' \<CC>
      by (intro cf_parallelI cat_parallelI)
        (
          simp_all add: 
            cat_cs_intros cat_parallel_cs_intros cat_PL_ineq[symmetric]
        )

    have "\<epsilon>' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e ?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    proof(intro is_cat_coneI is_tm_ntcfI' is_ntcfI')
      show "vfsequence \<epsilon>'" unfolding \<epsilon>'_def by auto
      show "vcard \<epsilon>' = 5\<^sub>\<nat>" unfolding \<epsilon>'_def by (simp add: nat_omega_simps)
      from h' show "cf_const (?II) \<CC> r' : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      show "?II_II : ?II \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (cs_concl cs_simp: cat_parallel_cs_simps cs_intro: cat_cs_intros)
      from h' show "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : 
        cf_const ?II \<CC> r'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> ?II_II\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        if "a \<in>\<^sub>\<circ> ?II\<lparr>Obj\<rparr>" for a 
        using that
        by (elim the_cat_parallel_ObjE; simp only:)
          (
            cs_concl 
              cs_simp: 
                \<epsilon>'_NTMap_app_I2 \<epsilon>'_NTMap_app_sI2 
                cat_cs_simps cat_parallel_cs_simps 
              cs_intro: cat_cs_intros cat_parallel_cs_intros
          )
      from h' f' g'h'_f'h' show 
        "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> cf_const ?II \<CC> r'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
          ?II_II\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
          if "f : a \<mapsto>\<^bsub>?II\<^esub> b" for a b f
          using that
          by (elim \<epsilon>.the_cat_parallel_is_arrE; simp only:)
            (
              cs_concl 
                cs_intro: cat_cs_intros cat_parallel_cs_intros 
                cs_simp:
                  cat_cs_simps
                  cat_parallel_cs_simps
                  \<epsilon>'_NTMap_app_I2 
                  \<epsilon>'_NTMap_app_sI2
            )+
      qed 
        (
          simp add: \<epsilon>'_components | 
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_lim_cs_intros cat_cs_intros cat_small_cs_intros 
        )+
    from \<epsilon>.cat_eq_unique_cone[OF this] obtain t'
      where t': "t' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E"
        and \<epsilon>'_NTMap_app: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> t'"
        and unique_t':
          "\<lbrakk> t'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E; \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> t''\<rbrakk> \<Longrightarrow> 
            t'' = t'" 
        for t''
      by metis

    show "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E \<and> u' = \<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f'"
    proof(intro ex1I conjI; (elim conjE)?, (rule t')?)
      show [symmetric, cat_cs_simps]: "u' = \<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t'"
      proof(rule ntcf_eqI[OF u'.is_ntcf_axioms])
        from t' show 
          "\<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t' : cf_const \<JJ> \<CC> r' \<mapsto>\<^sub>C\<^sub>F \<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        show "u'\<lparr>NTMap\<rparr> = (\<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t')\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI)
          show "vsv ((\<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t')\<lparr>NTMap\<rparr>)"
            by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
          from t' show 
            "\<D>\<^sub>\<circ> (u'\<lparr>NTMap\<rparr>) = \<D>\<^sub>\<circ> ((\<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t')\<lparr>NTMap\<rparr>)"
            by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
          show "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
            if "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (u'\<lparr>NTMap\<rparr>)" for a
          proof-
            from that have "a \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" by (cs_prems cs_simp: cat_cs_simps)
            with t' show "u'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t')\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
              by 
                (
                  cs_concl
                    cs_simp:
                      cat_cs_simps 
                      \<pi>'_NTMap_app
                      cat_parallel_cs_simps
                      the_cat_discrete_components(1)
                      \<epsilon>'_NTMap_app[symmetric]
                      \<epsilon>'_NTMap_app_I2
                      \<pi>'_NTMap_app'[symmetric]
                    cs_intro: cat_cs_intros cat_parallel_cs_intros
                )
          qed
        qed auto
      qed simp_all

      fix t'' assume prems': 
        "t'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> E" "u' = \<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t''"
      then have u'_NTMap_app_x:
        "u'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = (\<mu> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> t'')\<lparr>NTMap\<rparr>\<lparr>x\<rparr>"
        for x 
        by simp
      have "?\<pi>'\<lparr>NTMap\<rparr>\<lparr>j\<rparr> = \<pi>\<^sub>O\<lparr>NTMap\<rparr>\<lparr>j\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> t'')" 
        if "j \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for j
        using u'_NTMap_app_x[of j] prems'(1) that
        by 
          (
            cs_prems 
              cs_simp:
                cat_cs_simps 
                cat_discrete_cs_simps 
                cat_parallel_cs_simps 
                the_cat_discrete_components(1) 
              cs_intro: cat_cs_intros cat_parallel_cs_intros
          ) 
          (simp add: \<pi>'_NTMap_app[OF that, symmetric])
      moreover from prems'(1) have "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> t'' : r' \<mapsto>\<^bsub>\<CC>\<^esub> P\<^sub>O"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_parallel_cs_simps 
              cs_intro: cat_cs_intros cat_parallel_cs_intros
          )
      ultimately have [cat_cs_simps]: 
        "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<^sub>P\<^sub>L\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> t'' = h'" 
        by (intro unique_h') simp
      show "t'' = t'"
        by (rule unique_t', intro prems'(1)) 
          (cs_concl cs_simp: \<epsilon>'_NTMap_app_I2 cat_cs_simps)
      qed
    qed
 
  qed
  
  then show ?thesis using that by clarsimp

qed

lemma cat_colimit_of_cat_prod_obj_and_cat_coequalizer:
  \<comment>\<open>See Theorem 1 in Chapter V-2 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<FF> : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>\<aa> \<bb> \<gg> \<ff>. \<lbrakk> \<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>; \<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa> \<rbrakk> \<Longrightarrow>
      \<exists>E \<epsilon>. \<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>A. tm_cf_discrete \<alpha> (\<JJ>\<lparr>Obj\<rparr>) A \<CC> \<Longrightarrow>
      \<exists>P \<pi>. \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : \<JJ>\<lparr>Obj\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>A. tm_cf_discrete \<alpha> (\<JJ>\<lparr>Arr\<rparr>) A \<CC> \<Longrightarrow>
      \<exists>P \<pi>. \<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : \<JJ>\<lparr>Arr\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains r u where "u : \<FF> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m r : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<FF>: is_tm_functor \<alpha> \<JJ> \<CC> \<FF> by (rule assms(1))
  have "\<exists>E \<epsilon>. \<epsilon> : E <\<^sub>C\<^sub>F\<^sub>.\<^sub>e\<^sub>q (\<aa>,\<bb>,\<gg>,\<ff>) : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    if "\<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>" "\<gg> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>" for \<aa> \<bb> \<gg> \<ff>
  proof-
    from assms(2)[OF that(1,2)] obtain E \<epsilon> 
      where \<epsilon>: "\<epsilon> : (\<aa>,\<bb>,\<gg>,\<ff>) >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>e\<^sub>q E : \<up>\<up>\<^sup>2\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by clarsimp
    interpret \<epsilon>: is_cat_coequalizer \<alpha> \<aa> \<bb> \<gg> \<ff> \<CC> E \<epsilon> by (rule \<epsilon>)
    from \<epsilon>.is_cat_equalizer_op[unfolded cat_op_simps] show ?thesis by auto
  qed
  moreover have "\<exists>P \<pi>. \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : \<JJ>\<lparr>Obj\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    if "tm_cf_discrete \<alpha> (\<JJ>\<lparr>Obj\<rparr>) A (op_cat \<CC>)" for A
  proof-
    interpret tm_cf_discrete \<alpha> \<open>\<JJ>\<lparr>Obj\<rparr>\<close> A \<open>op_cat \<CC>\<close> by (rule that)
    from assms(3)[OF tm_cf_discrete_op[unfolded cat_op_simps]] obtain P \<pi> 
      where \<pi>: "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : \<JJ>\<lparr>Obj\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by clarsimp 
    interpret \<pi>: is_cat_obj_coprod \<alpha> \<open>\<JJ>\<lparr>Obj\<rparr>\<close> A \<CC> P \<pi> by (rule \<pi>)
    from \<pi>.is_cat_obj_prod_op show ?thesis by auto
  qed
  moreover have "\<exists>P \<pi>. \<pi> : P <\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Prod> A : \<JJ>\<lparr>Arr\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    if "tm_cf_discrete \<alpha> (\<JJ>\<lparr>Arr\<rparr>) A (op_cat \<CC>)" for A 
  proof-
    interpret tm_cf_discrete \<alpha> \<open>\<JJ>\<lparr>Arr\<rparr>\<close> A \<open>op_cat \<CC>\<close> by (rule that)
    from assms(4)[OF tm_cf_discrete_op[unfolded cat_op_simps]] obtain P \<pi> 
      where \<pi>: "\<pi> : A >\<^sub>C\<^sub>F\<^sub>.\<^sub>\<Coprod> P : \<JJ>\<lparr>Arr\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by clarsimp 
    interpret \<pi>: is_cat_obj_coprod \<alpha> \<open>\<JJ>\<lparr>Arr\<rparr>\<close> A \<CC> P \<pi> by (rule \<pi>)
    from \<pi>.is_cat_obj_prod_op show ?thesis by auto
  qed
  ultimately obtain u r where u: 
    "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m op_cf \<FF> : op_cat \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    by 
      (
        rule cat_limit_of_cat_prod_obj_and_cat_equalizer[
          OF \<FF>.is_tm_functor_op, unfolded cat_op_simps
          ]
      )
  interpret u: is_cat_limit \<alpha> \<open>op_cat \<JJ>\<close> \<open>op_cat \<CC>\<close> \<open>op_cf \<FF>\<close> r u by (rule u)
  from u.is_cat_colimit_op[unfolded cat_op_simps] that show ?thesis by simp
qed

text\<open>\newpage\<close>

end