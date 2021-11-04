(* Copyright 2020 (C) Mihails Milehins *)

section\<open>Orders\<close>
theory CZH_ECAT_Order
  imports 
    CZH_ECAT_Functor
begin



subsection\<open>Background\<close>

named_theorems cat_order_cs_simps
named_theorems cat_order_cs_intros



subsection\<open>Preorder category\<close>


text\<open>See Chapter I-2 in \cite{mac_lane_categories_2010}.\<close>

locale cat_preorder = category \<alpha> \<CC> for \<alpha> \<CC> +
  assumes cat_peo: 
    "\<lbrakk> a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow>
      (\<exists>f. Hom \<CC> a b = set {f}) \<or> (Hom \<CC> a b = 0)"


text\<open>Rules.\<close>

lemma (in cat_preorder) cat_preorder_axioms'[cat_order_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "cat_preorder \<alpha>' \<CC>"
  unfolding assms by (rule cat_preorder_axioms)

mk_ide rf cat_preorder_def[unfolded cat_preorder_axioms_def]
  |intro cat_preorderI|
  |dest cat_preorderD[dest]|
  |elim cat_preorderE[elim]|

lemmas [cat_order_cs_intros] = cat_preorderD(1)


text\<open>Elementary properties.\<close>

lemma (in cat_preorder) cat_peo_HomE:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  obtains f where \<open>Hom \<CC> a b = set {f}\<close> | \<open>Hom \<CC> a b = 0\<close>
  using cat_peo[OF assms] by auto

lemma (in cat_preorder) cat_peo_is_thin_category:
  \<comment>\<open>
  The statement of the lemma appears in
  nLab \cite{noauthor_nlab_nodate}\footnote{
  \url{https://ncatlab.org/nlab/show/preorder}
  }.\<close>
  assumes "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and "g : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "f = g"
proof-
  note f = cat_is_arrD[OF assms(1)]
  from assms have "Hom \<CC> a b \<noteq> 0" by (metis HomI eq0_iff)
  with cat_peo_HomE[OF f(2,3)] obtain h where "Hom \<CC> a b = set {h}" by auto
  moreover from assms have "f \<in>\<^sub>\<circ> Hom \<CC> a b" and "g \<in>\<^sub>\<circ> Hom \<CC> a b" by auto
  ultimately have "h = f" and "h = g" by auto
  then show ?thesis by auto
qed



subsection\<open>Order relation\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition is_le :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" (infix \<open>\<le>\<^sub>O\<index>\<close> 50)
  where "a \<le>\<^sub>O\<^bsub>\<CC>\<^esub> b \<longleftrightarrow> Hom \<CC> a b \<noteq> 0"


text\<open>Rules.\<close>

mk_ide is_le_def
  |intro is_leI|
  |dest is_leD[dest]|
  |elim is_leE[elim]|


text\<open>Elementary properties.\<close>

lemma (in cat_preorder) cat_peo_is_le[cat_order_cs_intros]: 
  assumes "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "a \<le>\<^sub>O\<^bsub>\<CC>\<^esub> b"
  using assms by (force intro: is_leI)

lemmas [cat_order_cs_intros] = cat_preorder.cat_peo_is_le

lemma (in cat_preorder) cat_peo_is_le_ex1:
  assumes "a \<le>\<^sub>O\<^bsub>\<CC>\<^esub> b" and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "\<exists>!f. f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
proof-
  from assms have "Hom \<CC> a b \<noteq> 0" by auto
  with assms cat_peo obtain f where Hom_ab: "Hom \<CC> a b = set {f}" by meson
  show "\<exists>!f. f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  proof(intro ex1I)
    from Hom_ab show "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" by auto
    fix g assume "g : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    with Hom_ab show "g = f" by auto
  qed
qed

lemma (in cat_preorder) cat_peo_is_le_ex[elim]:
  assumes "a \<le>\<^sub>O\<^bsub>\<CC>\<^esub> b" and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  obtains f where "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  using cat_peo_is_le_ex1[OF assms] that by clarsimp


subsubsection\<open>Order relation on a preorder category is a preorder\<close>

lemma (in cat_preorder) is_le_refl: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "a \<le>\<^sub>O\<^bsub>\<CC>\<^esub> a"
proof(intro is_leI)
  from assms have "\<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> Hom \<CC> a a" by (cs_concl cs_intro: cat_cs_intros)
  then show "Hom \<CC> a a \<noteq> 0" by force
qed

lemma (in cat_preorder) is_le_trans: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "a \<le>\<^sub>O\<^bsub>\<CC>\<^esub> b"
    and "b \<le>\<^sub>O\<^bsub>\<CC>\<^esub> c"
  shows "a \<le>\<^sub>O\<^bsub>\<CC>\<^esub> c"
proof(intro is_leI)
  from assms obtain f where f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" by auto
  from assms obtain g where g: "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" by auto
  from f g have "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c"
    by (cs_concl cs_intro: cat_cs_intros)
  then show "Hom \<CC> a c \<noteq> 0" by force
qed



subsection\<open>Partial order category\<close>


text\<open>See Chapter I-2 in \cite{mac_lane_categories_2010}.\<close>

locale cat_partial_order = cat_preorder \<alpha> \<CC> for \<alpha> \<CC> +
  assumes cat_po: "\<lbrakk> a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; a \<le>\<^sub>O\<^bsub>\<CC>\<^esub> b; b \<le>\<^sub>O\<^bsub>\<CC>\<^esub> a \<rbrakk> \<Longrightarrow> a = b"


text\<open>Rules.\<close>

lemma (in cat_partial_order) cat_partial_order_axioms'[cat_order_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "cat_partial_order \<alpha>' \<CC>"
  unfolding assms by (rule cat_partial_order_axioms)

mk_ide rf cat_partial_order_def[unfolded cat_partial_order_axioms_def]
  |intro cat_partial_orderI|
  |dest cat_partial_orderD[dest]|
  |elim cat_partial_orderE[elim]|

lemmas [cat_order_cs_intros] = cat_partial_orderD(1)



subsection\<open>Linear order category\<close>


text\<open>See Chapter I-2 in \cite{mac_lane_categories_2010}.\<close>

locale cat_linear_order = cat_partial_order \<alpha> \<CC> for \<alpha> \<CC> +
  assumes cat_lo: "\<lbrakk> a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> a \<le>\<^sub>O\<^bsub>\<CC>\<^esub> b \<or> b \<le>\<^sub>O\<^bsub>\<CC>\<^esub> a"


text\<open>Rules.\<close>

lemma (in cat_linear_order) cat_linear_order_axioms'[cat_order_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "cat_linear_order \<alpha>' \<CC>"
  unfolding assms by (rule cat_linear_order_axioms)

mk_ide rf cat_linear_order_def[unfolded cat_linear_order_axioms_def]
  |intro cat_linear_orderI|
  |dest cat_linear_orderD[dest]|
  |elim cat_linear_orderE[elim]|

lemmas [cat_order_cs_intros] = cat_linear_orderD(1)



subsection\<open>Preorder functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
See \cite{noauthor_nlab_nodate}\footnote{
\url{https://ncatlab.org/nlab/show/monotone+function}
}.
\<close>

locale is_preorder_functor = 
  is_functor \<alpha> \<AA> \<BB> \<FF> + HomDom: cat_preorder \<alpha> \<AA> + HomCod: cat_preorder \<alpha> \<BB>
  for \<alpha> \<AA> \<BB> \<FF> 

syntax "_is_preorder_functor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_preorder_functor \<alpha> \<AA> \<BB> \<FF>"


text\<open>Rules.\<close>

lemma (in is_preorder_functor) is_preorder_functor_axioms'[cat_order_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_preorder_functor_axioms)
 
mk_ide rf is_preorder_functor_def
  |intro is_preorder_functorI|
  |dest is_preorder_functorD[dest]|
  |elim is_preorder_functorE[elim]|

lemmas [cat_order_cs_intros] = is_preorder_functorD


subsubsection\<open>A preorder functor is a faithful functor\<close>

sublocale is_preorder_functor \<subseteq> is_ft_functor
proof(intro is_ft_functorI')
  fix a b assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  show "v11 (\<FF>\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<AA> a b)"
  proof
    (
      intro vsv.vsv_valeq_v11I, 
      unfold vdomain_vlrestriction cat_cs_simps vintersection_iff; 
      (elim conjE)?
    )
    fix g f assume "g : a \<mapsto>\<^bsub>\<AA>\<^esub> b" "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"  
    then show "g = f" by (auto simp: HomDom.cat_peo_is_thin_category)
  qed simp
qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)


lemmas (in is_preorder_functor) is_preorder_functor_is_ft_functor = 
  is_ft_functor_axioms

lemmas [cat_order_cs_intros] = 
  is_preorder_functor.is_preorder_functor_is_ft_functor


subsubsection\<open>A preorder functor is a monotone function\<close>

lemma (in is_preorder_functor) cat_peo:
  \<comment>\<open>
  Based on \cite{noauthor_nlab_nodate}\footnote{
  \url{https://ncatlab.org/nlab/show/monotone+function}
  }\<close>
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "a \<le>\<^sub>O\<^bsub>\<AA>\<^esub> b"
  shows "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<le>\<^sub>O\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
proof-
  from assms obtain f where "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" by auto
  then have "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    by (simp add: cf_ArrMap_is_arr)
  then show "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<le>\<^sub>O\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    by (cs_concl cs_intro: cat_order_cs_intros)
qed


subsubsection\<open>Composition of preorder functors\<close>

lemma cf_comp_is_preorder_functor[cat_order_cs_intros]:
  assumes "\<GG> : \<BB> \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<GG>: is_preorder_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1))
  interpret \<FF>: is_preorder_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by (intro is_preorder_functorI)
      (cs_concl cs_intro: cat_cs_intros cat_order_cs_intros)+
qed

lemma (in cat_preorder) cat_peo_cf_is_preorder_functor: 
  "cf_id \<CC> : \<CC> \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> \<CC>"
  by (intro is_preorder_functorI)
    (cs_concl cs_intro: cat_cs_intros cat_order_cs_intros)+

lemma (in cat_preorder) cat_peo_cf_is_preorder_functor'[cat_order_cs_intros]:
  assumes "\<AA>' = \<CC>" and "\<BB>' = \<CC>"
  shows "cf_id \<CC> : \<AA>' \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule cat_peo_cf_is_preorder_functor)

lemmas [cat_order_cs_intros] = cat_preorder.cat_peo_cf_is_preorder_functor'

end