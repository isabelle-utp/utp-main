(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Subcategory\<close>
theory CZH_ECAT_Subcategory
  imports 
    CZH_ECAT_Functor
    CZH_Foundations.CZH_SMC_Subsemicategory
begin



subsection\<open>Background\<close>

named_theorems cat_sub_cs_intros
named_theorems cat_sub_bw_cs_intros
named_theorems cat_sub_fw_cs_intros
named_theorems cat_sub_bw_cs_simps



subsection\<open>Simple subcategory\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

locale subcategory = sdg: category \<alpha> \<BB> + dg: category \<alpha> \<CC> for \<alpha> \<BB> \<CC>  +
  assumes subcat_subsemicategory: "cat_smc \<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<CC>" 
    and subcat_CId: "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow> \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"

abbreviation is_subcategory ("(_/ \<subseteq>\<^sub>C\<index> _)" [51, 51] 50)
  where "\<BB> \<subseteq>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<equiv> subcategory \<alpha> \<BB> \<CC>"


text\<open>Rules.\<close>

lemma (in subcategory) subcategory_axioms'[cat_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<BB>' = \<BB>"
  shows "\<BB>' \<subseteq>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>"
  unfolding assms by (rule subcategory_axioms)

lemma (in subcategory) subcategory_axioms''[cat_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<CC>' = \<CC>"
  shows "\<BB> \<subseteq>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule subcategory_axioms)

mk_ide rf subcategory_def[unfolded subcategory_axioms_def]
  |intro subcategoryI[intro!]|
  |dest subcategoryD[dest]|
  |elim subcategoryE[elim!]|

lemmas [cat_sub_cs_intros] = subcategoryD(1,2)

lemma subcategoryI':
  assumes "category \<alpha> \<BB>"
    and "category \<alpha> \<CC>"
    and "\<And>a. a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow> a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<And>a b f. f : a \<mapsto>\<^bsub>\<BB>\<^esub> b \<Longrightarrow> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "\<And>b c g a f. \<lbrakk> g : b \<mapsto>\<^bsub>\<BB>\<^esub> c; f : a \<mapsto>\<^bsub>\<BB>\<^esub> b \<rbrakk> \<Longrightarrow>
      g \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    and "\<And>a. a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow> \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
  shows "\<BB> \<subseteq>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(1))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(2))  
  show ?thesis
    by 
      (
        intro subcategoryI subsemicategoryI', 
        unfold slicing_simps; 
        (intro \<BB>.cat_semicategory \<CC>.cat_semicategory assms)?
      )
qed


text\<open>A subcategory is a subsemicategory.\<close>

context subcategory
begin

interpretation subsmc: subsemicategory \<alpha> \<open>cat_smc \<BB>\<close> \<open>cat_smc \<CC>\<close>
  by (rule subcat_subsemicategory)

lemmas_with [unfolded slicing_simps slicing_commute]:
  subcat_Obj_vsubset = subsmc.subsmc_Obj_vsubset
  and subcat_is_arr_vsubset = subsmc.subsmc_is_arr_vsubset
  and subcat_subdigraph_op_dg_op_dg = subsmc.subsmc_subdigraph_op_dg_op_dg
  and subcat_objD = subsmc.subsmc_objD
  and subcat_arrD = subsmc.subsmc_arrD
  and subcat_dom_simp = subsmc.subsmc_dom_simp
  and subcat_cod_simp = subsmc.subsmc_cod_simp
  and subcat_is_arrD = subsmc.subsmc_is_arrD

lemmas_with [unfolded slicing_simps slicing_commute]:
  subcat_Comp_simp = subsmc.subsmc_Comp_simp
  and subcat_is_idem_arrD = subsmc.subsmc_is_idem_arrD

end

lemmas [cat_sub_fw_cs_intros] = 
  subcategory.subcat_Obj_vsubset
  subcategory.subcat_is_arr_vsubset
  subcategory.subcat_objD
  subcategory.subcat_arrD
  subcategory.subcat_is_arrD

lemmas [cat_sub_bw_cs_simps] =
  subcategory.subcat_dom_simp
  subcategory.subcat_cod_simp

lemmas [cat_sub_fw_cs_intros] = 
  subcategory.subcat_is_idem_arrD

lemmas [cat_sub_bw_cs_simps] = 
  subcategory.subcat_Comp_simp


text\<open>The opposite subcategory.\<close>

lemma (in subcategory) subcat_subcategory_op_cat: "op_cat \<BB> \<subseteq>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
proof(rule subcategoryI)
  show "cat_smc (op_cat \<BB>) \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc (op_cat \<CC>)"
    unfolding slicing_commute[symmetric]
    by (intro subsmc_subsemicategory_op_smc subcat_subsemicategory)    
qed (simp_all add: sdg.category_op dg.category_op cat_op_simps subcat_CId)

lemmas subcat_subcategory_op_cat[intro] = subcategory.subcat_subcategory_op_cat


text\<open>Elementary properties.\<close>

lemma (in subcategory) subcat_CId_is_arr[intro]:
  assumes "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<BB>\<^esub> a"
proof-
  from assms have \<BB>\<CC>: "\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>" by (simp add: subcat_CId)
  from assms have "\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<BB>\<^esub> a" by (auto intro: cat_cs_intros)
  then show ?thesis unfolding \<BB>\<CC> by simp
qed


text\<open>Further rules.\<close>

lemma (in subcategory) subcat_CId_simp[cat_sub_bw_cs_simps]:
  assumes "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
  shows "\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
  using assms by (simp add: subcat_CId)

lemmas [cat_sub_bw_cs_simps] = subcategory.subcat_CId_simp 

lemma (in subcategory) subcat_is_right_inverseD[cat_sub_fw_cs_intros]: 
  assumes "is_right_inverse \<BB> g f" 
  shows "is_right_inverse \<CC> g f"
  using assms subcategory_axioms
  by (elim is_right_inverseE, intro is_right_inverseI)
    (
      cs_concl 
        cs_simp: cat_sub_bw_cs_simps[symmetric]
        cs_intro: cat_sub_fw_cs_intros cat_cs_intros cat_sub_cs_intros
    )

lemmas [cat_sub_fw_cs_intros] = subcategory.subcat_is_right_inverseD

lemma (in subcategory) subcat_is_left_inverseD[cat_sub_fw_cs_intros]: 
  assumes "is_left_inverse \<BB> g f" 
  shows "is_left_inverse \<CC> g f"
proof-
  have "op_cat \<BB> \<subseteq>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>" by (simp add: subcat_subcategory_op_cat)
  from subcategory.subcat_is_right_inverseD[OF this] show ?thesis 
    unfolding cat_op_simps using assms.
qed

lemmas [cat_sub_fw_cs_intros] = subcategory.subcat_is_left_inverseD

lemma (in subcategory) subcat_is_inverseD[cat_sub_fw_cs_intros]: 
  assumes "is_inverse \<BB> g f" 
  shows "is_inverse \<CC> g f"
  using assms subcategory_axioms
  by (elim is_inverseE, intro is_inverseI)
    (
      cs_concl 
        cs_simp: cat_sub_bw_cs_simps[symmetric]
        cs_intro: cat_sub_fw_cs_intros cat_cs_intros cat_sub_cs_intros
    )

lemmas [cat_sub_fw_cs_intros] = subcategory.subcat_is_inverseD

lemma (in subcategory) subcat_is_arr_isomorphismD[cat_sub_fw_cs_intros]:
  assumes "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> b" 
  shows "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
proof(intro is_arr_isomorphismI)
  from subcategory_axioms is_arr_isomorphismD(1)[OF assms] show "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    by 
      (
        cs_concl 
          cs_simp: cat_sub_bw_cs_simps[symmetric] cs_intro: cat_sub_fw_cs_intros
      )
  from assms have "is_inverse \<BB> (f\<inverse>\<^sub>C\<^bsub>\<BB>\<^esub>) f"
    by (rule sdg.cat_the_inverse_is_inverse)
  with subcategory_axioms show "is_inverse \<CC> (f\<inverse>\<^sub>C\<^bsub>\<BB>\<^esub>) f"
    by (elim is_inverseE, intro is_inverseI)
      (
        cs_concl 
          cs_simp: cat_sub_bw_cs_simps[symmetric] 
          cs_intro: cat_sub_fw_cs_intros cat_cs_intros
      )
qed

lemmas [cat_sub_fw_cs_intros] = subcategory.subcat_is_arr_isomorphismD

lemma (in subcategory) subcat_the_inverse_simp[cat_sub_bw_cs_simps]:
  assumes "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> b" 
  shows "f\<inverse>\<^sub>C\<^bsub>\<BB>\<^esub> = f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>"
proof-
  from assms have "is_inverse \<BB> (f\<inverse>\<^sub>C\<^bsub>\<BB>\<^esub>) f"
    by (auto dest: sdg.cat_the_inverse_is_inverse)
  with subcategory_axioms have inv_f\<BB>: "is_inverse \<CC> (f\<inverse>\<^sub>C\<^bsub>\<BB>\<^esub>) f" 
    by (auto dest: cat_sub_fw_cs_intros)
  from assms have "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b" by (auto dest: cat_sub_fw_cs_intros)
  then have inv_f\<CC>: "is_inverse \<CC> (f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>) f" 
    by (auto dest: dg.cat_the_inverse_is_inverse)
  from inv_f\<BB> inv_f\<CC> show ?thesis by (intro dg.cat_is_inverse_eq)
qed

lemmas [cat_sub_bw_cs_simps] = subcategory.subcat_the_inverse_simp

lemma (in subcategory) subcat_obj_isoD:
  assumes "a \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<BB>\<^esub> b" 
  shows "a \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> b"
  using assms subcategory_axioms
  by (elim obj_isoE) 
    (
      cs_concl 
        cs_simp: cat_sub_bw_cs_simps cs_intro: obj_isoI cat_sub_fw_cs_intros
    )

lemmas [cat_sub_fw_cs_intros] = subcategory.subcat_obj_isoD


subsubsection\<open>Subcategory relation is a partial order\<close>

lemma subcat_refl:
  assumes "category \<alpha> \<AA>"
  shows "\<AA> \<subseteq>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  interpret category \<alpha> \<AA> by (rule assms)
  show ?thesis 
    by (auto intro: cat_cs_intros slicing_intros subdg_refl subsemicategoryI)
qed

lemma subcat_trans: 
  assumes "\<AA> \<subseteq>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<AA> \<subseteq>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<AA>\<BB>: subcategory \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<CC>: subcategory \<alpha> \<BB> \<CC> by (rule assms(2))
  show ?thesis 
  proof(rule subcategoryI)
    show "cat_smc \<AA> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"
      by 
        (
          meson 
            \<AA>\<BB>.subcat_subsemicategory 
            \<BB>\<CC>.subcat_subsemicategory 
            subsmc_trans
        )
  qed 
    ( 
      use \<AA>\<BB>.subcategory_axioms \<BB>\<CC>.subcategory_axioms in 
        \<open>auto simp: \<AA>\<BB>.subcat_Obj_vsubset cat_sub_bw_cs_simps\<close>
    )
qed

lemma subcat_antisym:
  assumes "\<AA> \<subseteq>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "\<AA> = \<BB>"
proof-
  interpret \<AA>\<BB>: subcategory \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<AA>: subcategory \<alpha> \<BB> \<AA> by (rule assms(2))
  show ?thesis
  proof(rule cat_eqI)
    from 
      subsmc_antisym[
        OF \<AA>\<BB>.subcat_subsemicategory \<BB>\<AA>.subcat_subsemicategory
        ] 
    have 
      "cat_smc \<AA>\<lparr>Obj\<rparr> = cat_smc \<BB>\<lparr>Obj\<rparr>" "cat_smc \<AA>\<lparr>Arr\<rparr> = cat_smc \<BB>\<lparr>Arr\<rparr>"
      by simp_all
    then show Obj: "\<AA>\<lparr>Obj\<rparr> = \<BB>\<lparr>Obj\<rparr>" and Arr: "\<AA>\<lparr>Arr\<rparr> = \<BB>\<lparr>Arr\<rparr>" 
      unfolding slicing_simps by simp_all
    show "\<AA>\<lparr>Dom\<rparr> = \<BB>\<lparr>Dom\<rparr>"
      by (rule vsv_eqI) (auto simp: \<AA>\<BB>.subcat_dom_simp Arr cat_cs_simps)
    show "\<AA>\<lparr>Cod\<rparr> = \<BB>\<lparr>Cod\<rparr>"
      by (rule vsv_eqI) (auto simp: \<BB>\<AA>.subcat_cod_simp Arr cat_cs_simps)
    have "cat_smc \<AA> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<BB>" "cat_smc \<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<AA>" 
      by (simp_all add: \<AA>\<BB>.subcat_subsemicategory \<BB>\<AA>.subcat_subsemicategory)
    from subsmc_antisym[OF this] have "cat_smc \<AA> = cat_smc \<BB>" .
    then have "cat_smc \<AA>\<lparr>Comp\<rparr> = cat_smc \<BB>\<lparr>Comp\<rparr>" by auto
    then show "\<AA>\<lparr>Comp\<rparr> = \<BB>\<lparr>Comp\<rparr>" unfolding slicing_simps by simp
    show "\<AA>\<lparr>CId\<rparr> = \<BB>\<lparr>CId\<rparr>"
      by (rule vsv_eqI) (auto simp: Obj \<AA>\<BB>.subcat_CId_simp cat_cs_simps)
  qed (auto intro: cat_cs_intros)
qed



subsection\<open>Inclusion functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

abbreviation (input) cf_inc :: "V \<Rightarrow> V \<Rightarrow> V"
  where "cf_inc \<equiv> dghm_inc"


text\<open>Slicing.\<close>

lemma dghm_smcf_inc[slicing_commute]: 
  "dghm_inc (cat_smc \<BB>) (cat_smc \<CC>) = cf_smcf (cf_inc \<BB> \<CC>)"
  unfolding cf_smcf_def dghm_inc_def cat_smc_def dg_field_simps dghm_field_simps 
  by (simp_all add: nat_omega_simps)


text\<open>Elementary properties.\<close>

lemmas [cat_cs_simps] = 
  dghm_inc_ObjMap_app 
  dghm_inc_ArrMap_app


subsubsection\<open>Canonical inclusion functor associated with a subcategory\<close>

sublocale subcategory \<subseteq> inc: is_ft_functor \<alpha> \<BB> \<CC> \<open>cf_inc \<BB> \<CC>\<close>
proof(rule is_ft_functorI)
  interpret subsmc: subsemicategory \<alpha> \<open>cat_smc \<BB>\<close> \<open>cat_smc \<CC>\<close>
    by (rule subcat_subsemicategory)
  show "cf_inc \<BB> \<CC> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"  
  proof(rule is_functorI) 
    show "vfsequence (cf_inc \<BB> \<CC>)" unfolding dghm_inc_def by auto
    show "vcard (cf_inc \<BB> \<CC>) = 4\<^sub>\<nat>"
      unfolding dghm_inc_def by (simp add: nat_omega_simps)
    from sdg.cat_CId_is_arr subcat_CId_simp show "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow> 
      cf_inc \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>\<BB>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>cf_inc \<BB> \<CC>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      for c
      unfolding dghm_inc_components by force
    from subsmc.inc.is_ft_semifunctor_axioms show 
      "cf_smcf (cf_inc \<BB> \<CC>) : cat_smc \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"
      unfolding slicing_commute by auto
  qed (auto simp: dghm_inc_components cat_cs_intros)
  from subsmc.inc.is_ft_semifunctor_axioms show 
    "cf_smcf (cf_inc \<BB> \<CC>) : cat_smc \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> cat_smc \<CC>" 
    unfolding slicing_commute by auto
qed

lemmas (in subcategory) subcat_cf_inc_is_ft_functor = inc.is_ft_functor_axioms


subsubsection\<open>Inclusion functor for the opposite categories\<close>

lemma (in subcategory) subcat_cf_inc_op_cat_is_functor:
  "cf_inc (op_cat \<BB>) (op_cat \<CC>) : op_cat \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  by 
    (
      intro 
        subcategory.subcat_cf_inc_is_ft_functor
        subcat_subcategory_op_cat
    )
  
lemma (in subcategory) subcat_op_cat_cf_inc: 
  "cf_inc (op_cat \<BB>) (op_cat \<CC>) = op_cf (cf_inc \<BB> \<CC>)"
  by (rule cf_eqI)
    (
      auto 
        simp: 
          cat_op_simps 
          dghm_inc_components
          subcat_cf_inc_op_cat_is_functor
          is_ft_functor.axioms(1) 
        intro: cat_op_intros 
    )



subsection\<open>Full subcategory\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

locale fl_subcategory = subcategory +
  assumes fl_subcat_fl_subsemicategory: "cat_smc \<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"

abbreviation is_fl_subcategory ("(_/ \<subseteq>\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<index> _)" [51, 51] 50)
  where "\<BB> \<subseteq>\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC> \<equiv> fl_subcategory \<alpha> \<BB> \<CC>"


text\<open>Rules.\<close>

mk_ide rf fl_subcategory_def[unfolded fl_subcategory_axioms_def]
  |intro fl_subcategoryI|
  |dest fl_subcategoryD[dest]|
  |elim fl_subcategoryE[elim!]|

lemmas [cat_sub_cs_intros] = fl_subcategoryD(1)


text\<open>Elementary properties.\<close>

sublocale fl_subcategory \<subseteq> inc: is_fl_functor \<alpha> \<BB> \<CC> \<open>cf_inc \<BB> \<CC>\<close>
proof(rule is_fl_functorI)
  interpret fl_subsemicategory \<alpha> \<open>cat_smc \<BB>\<close> \<open>cat_smc \<CC>\<close>
    by (rule fl_subcat_fl_subsemicategory)
  from inc.is_fl_semifunctor_axioms show 
    "cf_smcf (dghm_inc \<BB> \<CC>) : cat_smc \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"
    unfolding slicing_commute by simp
qed (rule inc.is_functor_axioms)



subsection\<open>Wide subcategory\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
See 
\cite{noauthor_nlab_nodate}\footnote{
\url{https://ncatlab.org/nlab/show/wide+subcategory}
}.
\<close>

locale wide_subcategory = subcategory +
  assumes wide_subcat_wide_subsemicategory: "cat_smc \<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"

abbreviation is_wide_subcategory ("(_/ \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<index> _)" [51, 51] 50)
  where "\<BB> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<CC> \<equiv> wide_subcategory \<alpha> \<BB> \<CC>"


text\<open>Rules.\<close>

mk_ide rf wide_subcategory_def[unfolded wide_subcategory_axioms_def]
  |intro wide_subcategoryI|
  |dest wide_subcategoryD[dest]|
  |elim wide_subcategoryE[elim!]|

lemmas [cat_sub_cs_intros] = wide_subcategoryD(1)


text\<open>Wide subcategory is wide subsemicategory.\<close>

context wide_subcategory
begin

interpretation wide_subsmc: wide_subsemicategory \<alpha> \<open>cat_smc \<BB>\<close> \<open>cat_smc \<CC>\<close>
  by (rule wide_subcat_wide_subsemicategory)

lemmas_with [unfolded slicing_simps]:
  wide_subcat_Obj[dg_sub_bw_cs_intros] = wide_subsmc.wide_subsmc_Obj
  and wide_subcat_obj_eq[dg_sub_bw_cs_simps] = wide_subsmc.wide_subsmc_obj_eq

end

lemmas [cat_sub_bw_cs_simps] =  wide_subcategory.wide_subcat_obj_eq[symmetric]
lemmas [cat_sub_bw_cs_simps] = wide_subsemicategory.wide_subsmc_obj_eq


subsubsection\<open>The wide subcategory relation is a partial order\<close>

lemma wide_subcat_refl: 
  assumes "category \<alpha> \<AA>" 
  shows "\<AA> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  interpret category \<alpha> \<AA> by (rule assms)
  show ?thesis
    by
      (
        auto intro: 
          assms
          slicing_intros 
          wide_subsmc_refl 
          wide_subcategoryI 
          subsmc_refl 
      )
qed

lemma wide_subcat_trans[trans]:
  assumes "\<AA> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<AA> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<AA>\<BB>: wide_subcategory \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<CC>: wide_subcategory \<alpha> \<BB> \<CC> by (rule assms(2))
  show ?thesis
    by 
      (
        intro 
          wide_subcategoryI 
          subcat_trans[OF \<AA>\<BB>.subcategory_axioms \<BB>\<CC>.subcategory_axioms], 
        rule wide_subsmc_trans, 
        rule \<AA>\<BB>.wide_subcat_wide_subsemicategory, 
        rule \<BB>\<CC>.wide_subcat_wide_subsemicategory
     )
qed

lemma wide_subcat_antisym:
  assumes "\<AA> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "\<AA> = \<BB>"
proof-
  interpret \<AA>\<BB>: wide_subcategory \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<AA>: wide_subcategory \<alpha> \<BB> \<AA> by (rule assms(2))
  show ?thesis 
    by (rule subcat_antisym[OF \<AA>\<BB>.subcategory_axioms \<BB>\<AA>.subcategory_axioms])
qed



subsection\<open>Replete subcategory\<close>


subsubsection\<open>Definition and elementary properties\<close>

text\<open>
See nLab
\cite{noauthor_nlab_nodate}\footnote{
\url{https://ncatlab.org/nlab/show/replete+subcategory}
}.
\<close>

locale replete_subcategory = subcategory \<alpha> \<BB> \<CC> for \<alpha> \<BB> \<CC> +
  assumes rep_subcat_is_arr_isomorphism_is_arr: 
    "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow> f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b \<Longrightarrow> f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"

abbreviation is_replete_subcategory ("(_/ \<subseteq>\<^sub>C\<^sub>.\<^sub>r\<^sub>e\<^sub>p\<index> _)" [51, 51] 50)
  where "\<BB> \<subseteq>\<^sub>C\<^sub>.\<^sub>r\<^sub>e\<^sub>p\<^bsub>\<alpha>\<^esub> \<CC> \<equiv> replete_subcategory \<alpha> \<BB> \<CC>"


text\<open>Rules.\<close>

mk_ide rf replete_subcategory_def[unfolded replete_subcategory_axioms_def]
  |intro replete_subcategoryI|
  |dest replete_subcategoryD[dest]|
  |elim replete_subcategoryE[elim!]|

lemmas [cat_sub_cs_intros] = replete_subcategoryD(1)


text\<open>Elementary properties.\<close>

lemma (in replete_subcategory) (*not cat_sub_intro*)
  rep_subcat_is_arr_isomorphism_is_arr_isomorphism_left:
  assumes "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  shows "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> b"
proof(intro is_arr_isomorphismI is_inverseI)
  from assms show f: "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" 
    by (auto intro: rep_subcat_is_arr_isomorphism_is_arr)
  have "f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> a"
    by (rule dg.cat_the_inverse_is_arr_isomorphism[OF assms(2)])
  with f show inv_f: "f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> : b \<mapsto>\<^bsub>\<BB>\<^esub> a" 
    by (auto intro: rep_subcat_is_arr_isomorphism_is_arr)
  show "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" by (rule f)
  from dg.category_axioms assms have [cat_sub_bw_cs_simps]: 
    "f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  from dg.category_axioms assms have [cat_sub_bw_cs_simps]: 
    "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  from subcategory_axioms f inv_f show "f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
    by (cs_concl cs_simp: cat_sub_bw_cs_simps cs_intro: cat_cs_intros)
  from subcategory_axioms f inv_f show "f \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> = \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
    by (cs_concl cs_simp: cat_sub_bw_cs_simps cs_intro: cat_cs_intros)
qed

lemma (in replete_subcategory) (*not cat_sub_intro*)
  rep_subcat_is_arr_isomorphism_is_arr_isomorphism_right:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  shows "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> b"
proof-
  from assms(2) have "f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> a"
    by (rule dg.cat_the_inverse_is_arr_isomorphism)
  with assms(1) have inv_f: "f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> a"
    by (intro rep_subcat_is_arr_isomorphism_is_arr_isomorphism_left)
  then have "(f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>)\<inverse>\<^sub>C\<^bsub>\<BB>\<^esub> : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> b" 
    by (rule sdg.cat_the_inverse_is_arr_isomorphism)
  moreover from replete_subcategory_axioms assms inv_f have "(f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>)\<inverse>\<^sub>C\<^bsub>\<BB>\<^esub> = f"
    by 
      (
        cs_concl 
          cs_simp: cat_sub_bw_cs_simps cat_cs_simps cs_intro: cat_cs_intros 
      )
  ultimately show ?thesis by simp
qed

lemma (in replete_subcategory) (*not cat_sub_bw_cs_simps*)
  rep_subcat_is_arr_isomorphism_is_arr_isomorphism_left_iff:
  assumes "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
  shows "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> b \<longleftrightarrow> f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  using assms replete_subcategory_axioms 
  by (intro iffI)
    (
      cs_concl cs_intro: 
        rep_subcat_is_arr_isomorphism_is_arr_isomorphism_left 
        cat_sub_fw_cs_intros
    )

lemma (in replete_subcategory) (*not cat_sub_bw_cs_simps*)
  rep_subcat_is_arr_isomorphism_is_arr_isomorphism_right_iff:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
  shows "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> b \<longleftrightarrow> f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  using assms replete_subcategory_axioms 
  by (intro iffI)
    (
      cs_concl cs_intro: 
        rep_subcat_is_arr_isomorphism_is_arr_isomorphism_right
        cat_sub_fw_cs_intros
    )


subsubsection\<open>The replete subcategory relation is a partial order\<close>

lemma rep_subcat_refl: 
  assumes "category \<alpha> \<AA>" 
  shows "\<AA> \<subseteq>\<^sub>C\<^sub>.\<^sub>r\<^sub>e\<^sub>p\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  interpret category \<alpha> \<AA> by (rule assms)
  show ?thesis 
    by (intro replete_subcategoryI subcat_refl assms is_arr_isomorphismD(1))
qed

lemma rep_subcat_trans[trans]:
  assumes "\<AA> \<subseteq>\<^sub>C\<^sub>.\<^sub>r\<^sub>e\<^sub>p\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>C\<^sub>.\<^sub>r\<^sub>e\<^sub>p\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<AA> \<subseteq>\<^sub>C\<^sub>.\<^sub>r\<^sub>e\<^sub>p\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<AA>\<BB>: replete_subcategory \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<CC>: replete_subcategory \<alpha> \<BB> \<CC> by (rule assms(2))
  show ?thesis
  proof
    (
      intro 
        replete_subcategoryI 
        subcat_trans[OF \<AA>\<BB>.subcategory_axioms \<BB>\<CC>.subcategory_axioms]
    )
    fix a b f assume prems: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
    have "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
      by 
        (
          rule \<AA>\<BB>.dg.cat_is_arrD(3)
            [
              OF \<BB>\<CC>.rep_subcat_is_arr_isomorphism_is_arr[
                OF \<AA>\<BB>.subcat_objD[OF prems(1)] prems(2)
                ]
            ]
        )
    then have "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> b"
      by 
        (
          rule \<BB>\<CC>.rep_subcat_is_arr_isomorphism_is_arr_isomorphism_right[
            OF _ prems(2)
            ]
        )
    then show "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
      by (rule \<AA>\<BB>.rep_subcat_is_arr_isomorphism_is_arr[OF prems(1)])
  qed
qed

lemma rep_subcat_antisym:
  assumes "\<AA> \<subseteq>\<^sub>C\<^sub>.\<^sub>r\<^sub>e\<^sub>p\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>C\<^sub>.\<^sub>r\<^sub>e\<^sub>p\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "\<AA> = \<BB>"
proof-
  interpret \<AA>\<BB>: replete_subcategory \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<AA>: replete_subcategory \<alpha> \<BB> \<AA> by (rule assms(2))
  show ?thesis 
    by (rule subcat_antisym[OF \<AA>\<BB>.subcategory_axioms \<BB>\<AA>.subcategory_axioms])
qed



subsection\<open>Wide replete subcategory\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale wide_replete_subcategory = 
  wide_subcategory \<alpha> \<BB> \<CC> + replete_subcategory \<alpha> \<BB> \<CC> for \<alpha> \<BB> \<CC>

abbreviation is_wide_replete_subcategory ("(_/ \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>r\<index> _)" [51, 51] 50)
  where "\<BB> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>r\<^bsub>\<alpha>\<^esub> \<CC> \<equiv> wide_replete_subcategory \<alpha> \<BB> \<CC>"


text\<open>Rules.\<close>

mk_ide rf wide_replete_subcategory_def
  |intro wide_replete_subcategoryI|
  |dest wide_replete_subcategoryD[dest]|
  |elim wide_replete_subcategoryE[elim!]|

lemmas [cat_sub_cs_intros] = wide_replete_subcategoryD


text\<open>Wide replete subcategory preserves isomorphisms.\<close>

lemma (in wide_replete_subcategory) 
  wr_subcat_is_arr_isomorphism_is_arr_isomorphism:
  "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> b \<longleftrightarrow> f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
proof(rule iffI)
  assume prems: "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  then have "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  then have a: "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by (simp add: wide_subcat_obj_eq)
  show "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> b"
    by (intro rep_subcat_is_arr_isomorphism_is_arr_isomorphism_left[OF a prems])
qed 
  (
    use wide_replete_subcategory_axioms in
      \<open>cs_concl cs_intro: cat_sub_fw_cs_intros \<close>
  )

lemmas [cat_sub_bw_cs_simps] = 
  wide_replete_subcategory.wr_subcat_is_arr_isomorphism_is_arr_isomorphism


subsubsection\<open>The wide replete subcategory relation is a partial order\<close>

lemma wr_subcat_refl: 
  assumes "category \<alpha> \<AA>" 
  shows "\<AA> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>r\<^bsub>\<alpha>\<^esub> \<AA>"
  by (intro wide_replete_subcategoryI wide_subcat_refl rep_subcat_refl assms)

lemma wr_subcat_trans[trans]:
  assumes "\<AA> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>r\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>r\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<AA> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>r\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<AA>\<BB>: wide_replete_subcategory \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<CC>: wide_replete_subcategory \<alpha> \<BB> \<CC> by (rule assms(2))
  show ?thesis
    by 
      (
        intro wide_replete_subcategoryI,
        rule wide_subcat_trans, 
        rule \<AA>\<BB>.wide_subcategory_axioms,
        rule \<BB>\<CC>.wide_subcategory_axioms,
        rule rep_subcat_trans,
        rule \<AA>\<BB>.replete_subcategory_axioms,
        rule \<BB>\<CC>.replete_subcategory_axioms
      )
qed

lemma wr_subcat_antisym:
  assumes "\<AA> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>r\<^bsub>\<alpha>\<^esub>  \<BB>" and "\<BB> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>r\<^bsub>\<alpha>\<^esub>  \<AA>"
  shows "\<AA> = \<BB>"
proof-
  interpret \<AA>\<BB>: wide_replete_subcategory \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<AA>: wide_replete_subcategory \<alpha> \<BB> \<AA> by (rule assms(2))
  show ?thesis 
    by (rule subcat_antisym[OF \<AA>\<BB>.subcategory_axioms \<BB>\<AA>.subcategory_axioms])
qed

text\<open>\newpage\<close>

end