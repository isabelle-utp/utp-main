(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Discrete category\<close>
theory CZH_ECAT_Discrete
  imports 
    CZH_ECAT_Simple
    CZH_ECAT_Small_Functor
begin



subsection\<open>Abstract discrete category\<close>

named_theorems cat_discrete_cs_simps
named_theorems cat_discrete_cs_intros


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-2 in \cite{mac_lane_categories_2010}.\<close>

locale cat_discrete = category \<alpha> \<CC> for \<alpha> \<CC> +
  assumes cat_discrete_Arr: "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<Longrightarrow> f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>)"


text\<open>Rules.\<close>

lemma (in cat_discrete)
  assumes "\<alpha>' = \<alpha>" "\<CC>' = \<CC>"
  shows "cat_discrete \<alpha>' \<CC>'"
  unfolding assms by (rule cat_discrete_axioms)

mk_ide rf cat_discrete_def[unfolded cat_discrete_axioms_def]
  |intro cat_discreteI|
  |dest cat_discreteD[dest]|
  |elim cat_discreteE[elim]|

lemmas [cat_discrete_cs_intros] = cat_discreteD(1)


text\<open>Elementary properties.\<close>

lemma (in cat_discrete) cat_discrete_is_arrD[dest]:
  assumes "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "b = a" and "f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
proof-
  from assms cat_discrete_Arr have "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>)" 
    by (auto simp: cat_cs_simps)
  with cat_CId_vdomain obtain a' where f_def: "f = \<CC>\<lparr>CId\<rparr>\<lparr>a'\<rparr>" and "a' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    by (blast dest: CId.vrange_atD)
  then have "f : a' \<mapsto>\<^bsub>\<CC>\<^esub> a'" by (auto intro: cat_CId_is_arr')
  with assms have "a = a'" and "b = a'" by blast+
  with f_def show "b = a" and "f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>" by auto
qed

lemma (in cat_discrete) cat_discrete_is_arrE[elim]:
  assumes "f : b \<mapsto>\<^bsub>\<CC>\<^esub> c"
  obtains a where "f : a \<mapsto>\<^bsub>\<CC>\<^esub> a" and "f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
  using assms by auto



subsection\<open>The discrete category\<close>

text\<open>
As explained in Chapter I-2 in \cite{mac_lane_categories_2010}, every discrete
category is identified with its set of objects. 
In this work, it is assumed that the set of objects and the set of arrows
in the canonical discrete category coincide; the domain and the codomain 
functions are identities.
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition the_cat_discrete :: "V \<Rightarrow> V" (\<open>:\<^sub>C\<close>)
  where ":\<^sub>C I = [I, I, vid_on I, vid_on I, (\<lambda>fg\<in>\<^sub>\<circ>fid_on I. fg\<lparr>0\<rparr>), vid_on I]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma the_cat_discrete_components:
  shows ":\<^sub>C I\<lparr>Obj\<rparr> = I"
    and ":\<^sub>C I\<lparr>Arr\<rparr> = I"
    and ":\<^sub>C I\<lparr>Dom\<rparr> = vid_on I"
    and ":\<^sub>C I\<lparr>Cod\<rparr> = vid_on I"
    and ":\<^sub>C I\<lparr>Comp\<rparr> = (\<lambda>fg\<in>\<^sub>\<circ>fid_on I. fg\<lparr>0\<rparr>)"
    and ":\<^sub>C I\<lparr>CId\<rparr> = vid_on I"
  unfolding the_cat_discrete_def dg_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Domain\<close>

mk_VLambda the_cat_discrete_components(3)[folded VLambda_vid_on]
  |vsv the_cat_discrete_Dom_vsv[cat_discrete_cs_intros]|
  |vdomain the_cat_discrete_Dom_vdomain[cat_discrete_cs_simps]|
  |app the_cat_discrete_Dom_app[cat_discrete_cs_simps]|


subsubsection\<open>Codomain\<close>

mk_VLambda the_cat_discrete_components(4)[folded VLambda_vid_on]
  |vsv the_cat_discrete_Cod_vsv[cat_discrete_cs_intros]|
  |vdomain the_cat_discrete_Cod_vdomain[cat_discrete_cs_simps]|
  |app the_cat_discrete_Cod_app[cat_discrete_cs_simps]|


subsubsection\<open>Composition\<close>

lemma the_cat_discrete_Comp_vsv[cat_discrete_cs_intros]: "vsv (:\<^sub>C I\<lparr>Comp\<rparr>)"
  unfolding the_cat_discrete_components by simp

lemma the_cat_discrete_Comp_vdomain: "\<D>\<^sub>\<circ> (:\<^sub>C I\<lparr>Comp\<rparr>) = fid_on I"
  unfolding the_cat_discrete_components by simp

lemma the_cat_discrete_Comp_vrange: 
  "\<R>\<^sub>\<circ> (:\<^sub>C I\<lparr>Comp\<rparr>) = I"
proof(intro vsubset_antisym vsubsetI)
  fix f assume "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (:\<^sub>C I\<lparr>Comp\<rparr>)"
  then obtain gg where f_def: "f = :\<^sub>C I\<lparr>Comp\<rparr>\<lparr>gg\<rparr>" and gg: "gg \<in>\<^sub>\<circ> fid_on I"
    unfolding the_cat_discrete_components by auto
  from gg show "f \<in>\<^sub>\<circ> I"
    unfolding f_def the_cat_discrete_components by clarsimp
next
  fix f assume "f \<in>\<^sub>\<circ> I"
  then have "[f, f]\<^sub>\<circ> \<in>\<^sub>\<circ> fid_on I" by clarsimp
  moreover then have "f = :\<^sub>C I\<lparr>Comp\<rparr>\<lparr>f, f\<rparr>\<^sub>\<bullet>"
    unfolding the_cat_discrete_components by simp
  ultimately show "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (:\<^sub>C I\<lparr>Comp\<rparr>)"
    unfolding the_cat_discrete_components
    by (metis rel_VLambda.vsv_vimageI2 vdomain_VLambda)
qed
 
lemma the_cat_discrete_Comp_app[cat_discrete_cs_simps]: 
  assumes "i \<in>\<^sub>\<circ> I"
  shows "i \<circ>\<^sub>A\<^bsub>:\<^sub>C I\<^esub> i = i"
proof-
  from assms have "[i, i]\<^sub>\<circ> \<in>\<^sub>\<circ> fid_on I" by clarsimp
  then show ?thesis unfolding the_cat_discrete_components by simp
qed


subsubsection\<open>Identity\<close>

mk_VLambda the_cat_discrete_components(6)[folded VLambda_vid_on]
  |vsv the_cat_discrete_CId_vsv[cat_discrete_cs_intros]|
  |vdomain the_cat_discrete_CId_vdomain[cat_discrete_cs_simps]|
  |app the_cat_discrete_CId_app[cat_discrete_cs_simps]|


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma the_cat_discrete_is_arrI:
  assumes "i \<in>\<^sub>\<circ> I"
  shows "i : i \<mapsto>\<^bsub>:\<^sub>C I\<^esub> i"
  using assms unfolding is_arr_def the_cat_discrete_components by simp

lemma the_cat_discrete_is_arrI'[cat_discrete_cs_intros]:
  assumes "i \<in>\<^sub>\<circ> I"
    and "a = i"
    and "b = i"
  shows "i : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> b"
  using assms(1) unfolding assms(2,3) by (rule the_cat_discrete_is_arrI)

lemma the_cat_discrete_is_arrD:
  assumes "f : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> b"
  shows "f : f \<mapsto>\<^bsub>:\<^sub>C I\<^esub> f"
    and "a : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> a" 
    and "b : b \<mapsto>\<^bsub>:\<^sub>C I\<^esub> b"
    and "f \<in>\<^sub>\<circ> I"
    and "a \<in>\<^sub>\<circ> I"
    and "b \<in>\<^sub>\<circ> I"
    and "f = a"
    and "f = b"
    and "b = a"
  using assms unfolding is_arr_def the_cat_discrete_components by force+


subsubsection\<open>The discrete category is a discrete category\<close>

lemma (in \<Z>) cat_discrete_the_cat_discrete:
  assumes "I \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  shows "cat_discrete \<alpha> (:\<^sub>C I)"
proof(intro cat_discreteI categoryI')
  show "vfsequence (:\<^sub>C I)" unfolding the_cat_discrete_def by simp
  show "vcard (:\<^sub>C I) = 6\<^sub>\<nat>"
    unfolding the_cat_discrete_def by (simp add: nat_omega_simps)
  show "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (:\<^sub>C I\<lparr>Comp\<rparr>) \<longleftrightarrow> 
    (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>:\<^sub>C I\<^esub> c \<and> f : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> b)"
    for gf
    unfolding the_cat_discrete_Comp_vdomain
  proof
    assume "gf \<in>\<^sub>\<circ> fid_on I"
    then obtain a where "gf = [a, a]\<^sub>\<circ>" and "a \<in>\<^sub>\<circ> I" by clarsimp
    moreover then have "a : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> a" 
      by (auto intro: the_cat_discrete_is_arrI)
    ultimately show 
      "\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>:\<^sub>C I\<^esub> c \<and> f : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> b"
      by auto 
  next
    assume "\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>:\<^sub>C I\<^esub> c \<and> f : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> b"
    then obtain g f b c a where gf_def: "gf = [g, f]\<^sub>\<circ>"  
      and g: "g : b \<mapsto>\<^bsub>:\<^sub>C I\<^esub> c"
      and f: "f : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> b"
      by clarsimp
    then have "g = f" by (metis is_arrE the_cat_discrete_is_arrD(1))
    with the_cat_discrete_is_arrD(4)[OF f] show "gf \<in>\<^sub>\<circ> fid_on I"
      unfolding gf_def by clarsimp
  qed
  show "g \<circ>\<^sub>A\<^bsub>:\<^sub>C I\<^esub> f : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> c" if "g : b \<mapsto>\<^bsub>:\<^sub>C I\<^esub> c" and "f : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> b"
    for g b c f a
  proof-
    from that have fba: "f = a" "b = a" and a: "a \<in>\<^sub>\<circ> I" 
      unfolding the_cat_discrete_is_arrD[OF that(2)] by (simp_all add: \<open>a \<in>\<^sub>\<circ> I\<close>)
    from that have gcb: "g = b" "c = b"
      unfolding the_cat_discrete_is_arrD[OF that(1)] by simp_all
    from a show ?thesis
      unfolding fba gcb  
      by 
        (
          cs_concl 
            cs_simp: cat_discrete_cs_simps cs_intro: cat_discrete_cs_intros
        )
  qed
  show "h \<circ>\<^sub>A\<^bsub>:\<^sub>C I\<^esub> g \<circ>\<^sub>A\<^bsub>:\<^sub>C I\<^esub> f = h \<circ>\<^sub>A\<^bsub>:\<^sub>C I\<^esub> (g \<circ>\<^sub>A\<^bsub>:\<^sub>C I\<^esub> f)"
    if "h : c \<mapsto>\<^bsub>:\<^sub>C I\<^esub> d" and "g : b \<mapsto>\<^bsub>:\<^sub>C I\<^esub> c" and "f : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> b"
    for h c d g b f a
  proof-
    from that have fba: "f = a" "b = a" and a: "a \<in>\<^sub>\<circ> I" 
      unfolding the_cat_discrete_is_arrD[OF that(3)] by (simp_all add: \<open>a \<in>\<^sub>\<circ> I\<close>)
    from that have gcb: "g = b" "c = b" 
      unfolding the_cat_discrete_is_arrD[OF that(2)] by simp_all
    from that have hcd: "h = c" "d = c"
      unfolding the_cat_discrete_is_arrD[OF that(1)] by simp_all
    from a show ?thesis
      unfolding fba gcb hcd by (cs_concl cs_simp: cat_discrete_cs_simps)
  qed
  show ":\<^sub>C I\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>:\<^sub>C I\<^esub> f = f" if "f : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> b" for f a b
  proof-
    from that have fba: "f = a" "b = a" and a: "a \<in>\<^sub>\<circ> I" 
      unfolding the_cat_discrete_is_arrD[OF that] by (simp_all add: \<open>a \<in>\<^sub>\<circ> I\<close>)
    from a show ?thesis 
      by (cs_concl cs_simp: cat_discrete_cs_simps fba)
  qed
  show "f \<circ>\<^sub>A\<^bsub>:\<^sub>C I\<^esub> :\<^sub>C I\<lparr>CId\<rparr>\<lparr>b\<rparr> = f" if "f : b \<mapsto>\<^bsub>:\<^sub>C I\<^esub> c" for f b c
  proof-
    from that have fba: "f = b" "c = b" and b: "b \<in>\<^sub>\<circ> I" 
      unfolding the_cat_discrete_is_arrD[OF that] by (simp_all add: \<open>b \<in>\<^sub>\<circ> I\<close>)
    from b show ?thesis 
      by (cs_concl cs_simp: cat_discrete_cs_simps fba)
  qed
  show ":\<^sub>C I\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> a"
    if "a \<in>\<^sub>\<circ> :\<^sub>C I\<lparr>Obj\<rparr>" for a 
    using that 
    by (auto simp: the_cat_discrete_components intro: cat_discrete_cs_intros)
  show "\<Union>\<^sub>\<circ>((\<lambda>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>(VLambda B (Hom (:\<^sub>C I) a) `\<^sub>\<circ> B)) `\<^sub>\<circ> A) \<in>\<^sub>\<circ> Vset \<alpha>"
    if "A \<subseteq>\<^sub>\<circ> :\<^sub>C I\<lparr>Obj\<rparr>"
      and "B \<subseteq>\<^sub>\<circ> :\<^sub>C I\<lparr>Obj\<rparr>"
      and "A \<in>\<^sub>\<circ> Vset \<alpha>"
      and "B \<in>\<^sub>\<circ> Vset \<alpha>"
    for A B
  proof-
    have "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (:\<^sub>C I) a b) \<subseteq>\<^sub>\<circ> A \<union>\<^sub>\<circ> B"
    proof(intro vsubsetI, elim vifunionE, unfold in_Hom_iff)
      fix i j f assume prems: "i \<in>\<^sub>\<circ> A" "j \<in>\<^sub>\<circ> B" "f : i \<mapsto>\<^bsub>:\<^sub>C I\<^esub> j"
      then show "f \<in>\<^sub>\<circ> A \<union>\<^sub>\<circ> B" 
        unfolding the_cat_discrete_is_arrD[OF prems(3)] by simp
    qed
    moreover have "A \<union>\<^sub>\<circ> B \<in>\<^sub>\<circ> Vset \<alpha>" by (simp add: that(3,4) vunion_in_VsetI)
    ultimately show "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (:\<^sub>C I) a b) \<in>\<^sub>\<circ> Vset \<alpha>"
      by (auto simp: vsubset_in_VsetI)
  qed
qed (auto simp: assms the_cat_discrete_components intro: cat_cs_intros)

lemmas [cat_discrete_cs_intros] = \<Z>.cat_discrete_the_cat_discrete


subsubsection\<open>Opposite discrete category\<close>

lemma (in \<Z>) the_cat_discrete_op[cat_op_simps]:
  assumes "I \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  shows "op_cat (:\<^sub>C I) = :\<^sub>C I"
proof(rule cat_eqI[of \<alpha>])
  from assms show dI: "category \<alpha> (:\<^sub>C I)"
    by (cs_concl cs_intro: cat_discrete_the_cat_discrete cat_discrete_cs_intros)
  then show op_dI: "category \<alpha> (op_cat (:\<^sub>C I))"
    by (cs_concl cs_intro: cat_op_intros)
  interpret category \<alpha> \<open>op_cat (:\<^sub>C I)\<close> by (rule op_dI)
  show "op_cat (:\<^sub>C I)\<lparr>Comp\<rparr> = :\<^sub>C I\<lparr>Comp\<rparr>"
  proof(rule vsv_eqI)
    show "\<D>\<^sub>\<circ> (op_cat (:\<^sub>C I)\<lparr>Comp\<rparr>) = \<D>\<^sub>\<circ> (:\<^sub>C I\<lparr>Comp\<rparr>)"
      by (simp add: the_cat_discrete_components op_cat_components)
    fix gf assume "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (op_cat (:\<^sub>C I)\<lparr>Comp\<rparr>)"
    then have "gf \<in>\<^sub>\<circ> fid_on I" 
      by (simp add: the_cat_discrete_components op_cat_components)
    then obtain h where gf_def: "gf = [h, h]\<^sub>\<circ>" and h: "h \<in>\<^sub>\<circ> I" by clarsimp
    from dI h show "op_cat (:\<^sub>C I)\<lparr>Comp\<rparr>\<lparr>gf\<rparr> = :\<^sub>C I\<lparr>Comp\<rparr>\<lparr>gf\<rparr>" 
      by 
        ( 
          cs_concl 
            cs_simp: cat_op_simps gf_def cs_intro: cat_discrete_cs_intros
        )
  qed (auto intro: cat_discrete_cs_intros)
qed (unfold the_cat_discrete_components op_cat_components, simp_all)



subsection\<open>Discrete functor\<close>


subsubsection\<open>Local assumptions for the discrete functor\<close>


text\<open>See Chapter III in \cite{mac_lane_categories_2010}).\<close>

locale cf_discrete = category \<alpha> \<CC> for \<alpha> I F \<CC> +
  assumes cf_discrete_selector_vrange[cat_discrete_cs_intros]: 
    "i \<in>\<^sub>\<circ> I \<Longrightarrow> F i \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and cf_discrete_vdomain_vsubset_Vset: "I \<subseteq>\<^sub>\<circ> Vset \<alpha>"

lemmas (in cf_discrete) cf_discrete_category = category_axioms

lemmas [cat_discrete_cs_intros] = cf_discrete.cf_discrete_category


text\<open>Rules.\<close>

lemma (in cf_discrete) cf_discrete_axioms'[cat_discrete_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "I' = I" and "F' = F" 
  shows "cf_discrete \<alpha>' I' F' \<CC>"
  unfolding assms by (rule cf_discrete_axioms)

mk_ide rf cf_discrete_def[unfolded cf_discrete_axioms_def]
  |intro cf_discreteI|
  |dest cf_discreteD[dest]|
  |elim cf_discreteE[elim]|


text\<open>Elementary properties.\<close>

lemma (in cf_discrete) cf_discrete_is_functor_cf_CId_selector_is_arr: 
  assumes "i \<in>\<^sub>\<circ> I"
  shows "\<CC>\<lparr>CId\<rparr>\<lparr>F i\<rparr> : F i \<mapsto>\<^bsub>\<CC>\<^esub> F i"
  using assms by (meson cat_CId_is_arr' cf_discreteD(2) cf_discrete_axioms)

lemma (in cf_discrete) 
  cf_discrete_is_functor_cf_CId_selector_is_arr'[cat_discrete_cs_intros]: 
  assumes "i \<in>\<^sub>\<circ> I" and "a = F i" and "b = F i"
  shows "\<CC>\<lparr>CId\<rparr>\<lparr>F i\<rparr> : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  using assms(1)
  unfolding assms(2,3) 
  by (rule cf_discrete_is_functor_cf_CId_selector_is_arr)


subsubsection\<open>Definition and elementary properties\<close>

definition the_cf_discrete :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> V" (\<open>:\<rightarrow>:\<close>)
  where ":\<rightarrow>: I F \<CC> = [VLambda I F, (\<lambda>i\<in>\<^sub>\<circ>I. \<CC>\<lparr>CId\<rparr>\<lparr>F i\<rparr>), :\<^sub>C I, \<CC>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma the_cf_discrete_components:
  shows ":\<rightarrow>: I F \<CC>\<lparr>ObjMap\<rparr> = (\<lambda>i\<in>\<^sub>\<circ>I. F i)"
    and ":\<rightarrow>: I F \<CC>\<lparr>ArrMap\<rparr> = (\<lambda>i\<in>\<^sub>\<circ>I. \<CC>\<lparr>CId\<rparr>\<lparr>F i\<rparr>)"
    and [cat_discrete_cs_simps]: ":\<rightarrow>: I F \<CC>\<lparr>HomDom\<rparr> = :\<^sub>C I"
    and [cat_discrete_cs_simps]: ":\<rightarrow>: I F \<CC>\<lparr>HomCod\<rparr> = \<CC>"
  unfolding the_cf_discrete_def dghm_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda the_cf_discrete_components(1)
  |vsv the_cf_discrete_ObjMap_vsv[cat_discrete_cs_intros]|
  |vdomain the_cf_discrete_ObjMap_vdomain[cat_discrete_cs_simps]|
  |app the_cf_discrete_ObjMap_app[cat_discrete_cs_simps]|

lemma (in cf_discrete) cf_discrete_the_cf_discrete_ObjMap_vrange: 
  "\<R>\<^sub>\<circ> (:\<rightarrow>: I F \<CC>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  using cf_discrete_is_functor_cf_CId_selector_is_arr
  unfolding the_cf_discrete_components
  by (intro vrange_VLambda_vsubset) auto


subsubsection\<open>Arrow map\<close>

mk_VLambda the_cf_discrete_components(2)
  |vsv the_cf_discrete_ArrMap_vsv[cat_discrete_cs_intros]|
  |vdomain the_cf_discrete_ArrMap_vdomain[cat_discrete_cs_simps]|
  |app the_cf_discrete_ArrMap_app[cat_discrete_cs_simps]|

lemma (in cf_discrete) cf_discrete_the_cf_discrete_ArrMap_vrange: 
  "\<R>\<^sub>\<circ> (:\<rightarrow>: I F \<CC>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  using cf_discrete_is_functor_cf_CId_selector_is_arr
  unfolding the_cf_discrete_components
  by (intro vrange_VLambda_vsubset) (auto simp: cf_discrete_selector_vrange)


subsubsection\<open>Discrete functor is a functor\<close>

lemma (in cf_discrete) cf_discrete_the_cf_discrete_is_functor:  
  ":\<rightarrow>: I F \<CC> : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_functorI')
  show "vfsequence (:\<rightarrow>: I F \<CC>)" unfolding the_cf_discrete_def by simp
  show "category \<alpha> (:\<^sub>C I)"
    by 
      (
        simp add:
          cat_discrete_the_cat_discrete 
          cf_discrete_vdomain_vsubset_Vset 
          cat_discrete.axioms(1)
      )  
  show "vcard (:\<rightarrow>: I F \<CC>) = 4\<^sub>\<nat>"
    unfolding the_cf_discrete_def by (simp add: nat_omega_simps)
  show 
    ":\<rightarrow>: I F \<CC>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : :\<rightarrow>: I F \<CC>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> :\<rightarrow>: I F \<CC>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    if "f : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> b" for f a b
  proof-
    from that have fba: "f = a" "b = a" and a: "a \<in>\<^sub>\<circ> I" 
      unfolding the_cat_discrete_is_arrD[OF that] by (simp_all add: \<open>a \<in>\<^sub>\<circ> I\<close>)
    from that \<open>a \<in>\<^sub>\<circ> I\<close> show ?thesis
      by 
        (
          cs_concl 
            cs_simp: cat_discrete_cs_simps fba cs_intro: cat_discrete_cs_intros
        )
  qed
  show ":\<rightarrow>: I F \<CC>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>:\<^sub>C I\<^esub> f\<rparr> = 
    :\<rightarrow>: I F \<CC>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> :\<rightarrow>: I F \<CC>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
    if "g : b \<mapsto>\<^bsub>:\<^sub>C I\<^esub> c" and "f : a \<mapsto>\<^bsub>:\<^sub>C I\<^esub> b" for g b c f a
  proof-
    from that have gfacb: "f = a" "a = b" "g = b" "c = b" and b: "b \<in>\<^sub>\<circ> I"  
      by 
        (
          simp_all add: 
            the_cat_discrete_is_arrD(8-9)[OF that(1)] 
            the_cat_discrete_is_arrD(5-9)[OF that(2)]
        )
    have "F b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (simp add: b cf_discrete_selector_vrange)
    from b category_axioms this show ?thesis
      using that 
      unfolding gfacb
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_discrete_cs_simps cs_intro: cat_cs_intros
        )
  qed
  show ":\<rightarrow>: I F \<CC>\<lparr>ArrMap\<rparr>\<lparr>:\<^sub>C I\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>:\<rightarrow>: I F \<CC>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
    if "c \<in>\<^sub>\<circ> :\<^sub>C I\<lparr>Obj\<rparr>" for c
    using that
    unfolding the_cat_discrete_components(1)
    by (cs_concl cs_simp: cat_discrete_cs_simps cs_intro: cat_cs_intros)
qed 
  (
    auto simp: 
      the_cf_discrete_components 
      the_cat_discrete_components 
      cat_cs_intros
      cat_discrete_cs_intros
  ) 

lemma (in cf_discrete) cf_discrete_the_cf_discrete_is_functor':
  assumes "\<AA>' = :\<^sub>C I" and "\<CC>' = \<CC>"
  shows ":\<rightarrow>: I F \<CC> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule cf_discrete_the_cf_discrete_is_functor)

lemmas [cat_discrete_cs_intros] = 
  cf_discrete.cf_discrete_the_cf_discrete_is_functor'


subsubsection\<open>Uniqueness of the discrete category\<close>

lemma (in cat_discrete) cat_discrete_iso_the_cat_discrete:
  assumes "I \<subseteq>\<^sub>\<circ> Vset \<alpha>" and "I \<approx>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  obtains F where ":\<rightarrow>: I F \<CC> : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<CC>"
proof-

  from assms obtain F where v11_f: "v11 F" 
    and dr[simp]: "\<D>\<^sub>\<circ> F = I" "\<R>\<^sub>\<circ> F = \<CC>\<lparr>Obj\<rparr>" 
    by auto
  let ?F = "\<lambda>i. F\<lparr>i\<rparr>"
  interpret F: v11 F by (rule v11_f)
  from assms(1) interpret \<CC>: cf_discrete \<alpha> I ?F \<CC> 
    apply(intro cf_discreteI) 
    unfolding dr[symmetric] 
    by (cs_concl cs_intro: V_cs_intros cat_cs_intros)+
  have ":\<rightarrow>: I ?F \<CC> : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<CC>"
  proof(intro is_iso_functorI')
    from \<CC>.cf_discrete_selector_vrange show  
      ":\<rightarrow>: I ?F \<CC> : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
      by (intro cf_discrete.cf_discrete_the_cf_discrete_is_functor cf_discreteI)
        (auto simp: category_axioms assms(1))
    show "v11 (:\<rightarrow>: I ?F \<CC>\<lparr>ArrMap\<rparr>)"
    proof(rule vsv.vsv_valeq_v11I, unfold the_cf_discrete_ArrMap_vdomain)
      fix i j assume prems:
        "i \<in>\<^sub>\<circ> I" "j \<in>\<^sub>\<circ> I" ":\<rightarrow>: I ?F \<CC>\<lparr>ArrMap\<rparr>\<lparr>i\<rparr> = :\<rightarrow>: I ?F \<CC>\<lparr>ArrMap\<rparr>\<lparr>j\<rparr>"
      from prems(3) have "\<CC>\<lparr>CId\<rparr>\<lparr>?F i\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>?F j\<rparr>"
        unfolding 
          the_cf_discrete_ArrMap_app[OF prems(1)]
          the_cf_discrete_ArrMap_app[OF prems(2)].
      then have "?F i = ?F j"
        by 
          (
            metis 
              \<CC>.cf_discrete_is_functor_cf_CId_selector_is_arr 
              prems(1,2) 
              cat_is_arrD(4)
          )
      with F.v11_eq_iff prems show "i = j" by simp
    qed (simp add: the_cf_discrete_components)
    show "\<R>\<^sub>\<circ> (:\<rightarrow>: I ?F \<CC>\<lparr>ArrMap\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
    proof(intro vsubset_antisym vsubsetI)
      fix f assume "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (:\<rightarrow>: I ?F \<CC>\<lparr>ArrMap\<rparr>)"
      with \<CC>.cf_discrete_the_cf_discrete_ArrMap_vrange show "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" 
        by auto
    next
      fix f assume "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
      then obtain a b where "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" by auto
      then obtain a where f_def: "f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>" and a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
      from a F.vrange_atD dr obtain i where a_def: "a = ?F i" and i: "i \<in>\<^sub>\<circ> I"
        by blast
      from a i show "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (:\<rightarrow>: I ?F \<CC>\<lparr>ArrMap\<rparr>)"
        unfolding a_def f_def the_cf_discrete_components by auto
    qed
  qed (auto simp: v11_f the_cf_discrete_components)
  with that show ?thesis by simp

qed


subsubsection\<open>Opposite discrete functor\<close>

lemma (in cf_discrete) cf_discrete_the_cf_discrete_op[cat_op_simps]:
  "op_cf (:\<rightarrow>: I F \<CC>) = :\<rightarrow>: I F (op_cat \<CC>)"
proof(rule cf_eqI)
  from cf_discrete_vdomain_vsubset_Vset show 
    "op_cf (:\<rightarrow>: I F \<CC>) : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    by 
      (
        cs_concl 
          cs_simp: cat_op_simps cs_intro: cat_op_intros cat_discrete_cs_intros
      )
  show ":\<rightarrow>: I F (op_cat \<CC>) : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
  proof(intro cf_discrete.cf_discrete_the_cf_discrete_is_functor cf_discreteI)
    fix i assume "i \<in>\<^sub>\<circ> I"
    then show "F i \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
      by (simp add: cat_op_simps cf_discrete_selector_vrange)
  qed (intro cf_discrete_vdomain_vsubset_Vset cat_cs_intros)+
qed (unfold cat_op_simps the_cf_discrete_components, simp_all)

lemmas [cat_op_simps] = cf_discrete.cf_discrete_the_cf_discrete_op

lemma (in cf_discrete) cf_discrete_op[cat_op_intros]: 
  "cf_discrete \<alpha> I F (op_cat \<CC>)"
proof(intro cf_discreteI)
  show "category \<alpha> (op_cat \<CC>)" by (cs_concl cs_intro: cat_cs_intros)
  fix i assume "i \<in>\<^sub>\<circ> I"
  then show "F i \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_op_simps cs_intro: cat_discrete_cs_intros)
qed (intro cf_discrete_vdomain_vsubset_Vset)

lemmas [cat_op_intros] = cf_discrete.cf_discrete_op



subsection\<open>Tiny discrete category\<close>


subsubsection\<open>Background\<close>

named_theorems cat_small_discrete_cs_simps
named_theorems cat_small_discrete_cs_intros

lemmas [cat_small_discrete_cs_simps] = cat_discrete_cs_simps
lemmas [cat_small_discrete_cs_intros] = cat_discrete_cs_intros


subsubsection\<open>Definition and elementary properties\<close>

locale tiny_cat_discrete = cat_discrete \<alpha> \<CC> + tiny_category \<alpha> \<CC> for \<alpha> \<CC>


text\<open>Rules.\<close>

lemma (in tiny_cat_discrete) tiny_cat_discrete_axioms'[cat_discrete_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<CC>' = \<CC>"
  shows "tiny_cat_discrete \<alpha>' \<CC>'"
  unfolding assms by (rule tiny_cat_discrete_axioms)

mk_ide rf tiny_cat_discrete_def
  |intro tiny_cat_discreteI|
  |dest tiny_cat_discreteD[dest]|
  |elim tiny_cat_discreteE[elim]|

lemmas [cat_small_discrete_cs_intros] = tiny_cat_discreteD

lemma tiny_cat_discreteI':
  assumes "tiny_category \<alpha> \<CC>" and "\<And>f. f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<Longrightarrow> f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>)"
  shows "tiny_cat_discrete \<alpha> \<CC>"
proof(intro tiny_cat_discreteI cat_discreteI)
  interpret tiny_category \<alpha> \<CC> by (rule assms(1))
  show "category \<alpha> \<CC>" by (auto intro: tiny_dg_category)
  show "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>)" if "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" for f using that by (rule assms(2))
qed (auto intro: assms(1))


subsubsection\<open>The discrete category is a tiny category\<close>

lemma (in \<Z>) tiny_cat_discrete_the_cat_discrete[cat_small_discrete_cs_intros]:
  assumes "I \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "tiny_cat_discrete \<alpha> (:\<^sub>C I)"
proof(intro tiny_cat_discreteI cat_discrete_the_cat_discrete)
  from assms show "I \<subseteq>\<^sub>\<circ> Vset \<alpha>" by auto
  then interpret cat_discrete \<alpha> \<open>:\<^sub>C I\<close> by (intro cat_discrete_the_cat_discrete)
  show "tiny_category \<alpha> (:\<^sub>C I)"
    by (intro tiny_categoryI', unfold the_cat_discrete_components)
      (auto intro: cat_cs_intros assms)
qed

lemmas [cat_small_discrete_cs_intros] = \<Z>.cat_discrete_the_cat_discrete



subsection\<open>Discrete functor with tiny maps\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale tm_cf_discrete = category \<alpha> \<CC> for \<alpha> I F \<CC> +
  assumes tm_cf_discrete_selector_vrange[cat_small_discrete_cs_intros]: 
    "i \<in>\<^sub>\<circ> I \<Longrightarrow> F i \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and tm_cf_discrete_ObjMap_in_Vset: "VLambda I F \<in>\<^sub>\<circ> Vset \<alpha>"
    and tm_cf_discrete_ArrMap_in_Vset: "(\<lambda>i\<in>\<^sub>\<circ>I. \<CC>\<lparr>CId\<rparr>\<lparr>F i\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"


text\<open>Rules.\<close>

lemma (in tm_cf_discrete) tm_cf_discrete_axioms'[cat_small_discrete_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "I' = I" and "F' = F" 
  shows "tm_cf_discrete \<alpha>' I' F' \<CC>"
  unfolding assms by (rule tm_cf_discrete_axioms)

mk_ide rf tm_cf_discrete_def[unfolded tm_cf_discrete_axioms_def]
  |intro tm_cf_discreteI|
  |dest tm_cf_discreteD[dest]|
  |elim tm_cf_discreteE[elim]|

lemma tm_cf_discreteI': 
  assumes "cf_discrete \<alpha> I F \<CC>"
    and "(\<lambda>i\<in>\<^sub>\<circ>I. F i) \<in>\<^sub>\<circ> Vset \<alpha>"
    and "(\<lambda>i\<in>\<^sub>\<circ>I. \<CC>\<lparr>CId\<rparr>\<lparr>F i\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "tm_cf_discrete \<alpha> I F \<CC>"
proof-
  interpret cf_discrete \<alpha> I F \<CC> by (rule assms(1))
  show ?thesis
    by (intro tm_cf_discreteI)
      (auto intro: assms cf_discrete_selector_vrange cat_cs_intros)
qed


text\<open>Elementary properties.\<close>

sublocale tm_cf_discrete \<subseteq> cf_discrete
proof(intro cf_discreteI)
  from tm_cf_discrete_ObjMap_in_Vset have "\<D>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>I. F i) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (cs_concl cs_intro: vdomain_in_VsetI)
  then show "I \<subseteq>\<^sub>\<circ> Vset \<alpha>" by auto
qed (auto intro: cat_cs_intros tm_cf_discrete_selector_vrange)

lemmas (in tm_cf_discrete) tm_cf_discrete_is_cf_discrete_axioms = 
  cf_discrete_axioms

lemmas [cat_small_discrete_cs_intros] = 
  tm_cf_discrete.tm_cf_discrete_is_cf_discrete_axioms

lemma (in tm_cf_discrete) 
  tm_cf_discrete_index_in_Vset[cat_small_discrete_cs_intros]: 
  "I \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from tm_cf_discrete_ObjMap_in_Vset have "\<D>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>I. F i) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (cs_concl cs_intro: vdomain_in_VsetI)
  then show ?thesis by simp
qed


subsubsection\<open>Opposite discrete functor with tiny maps\<close>

lemma (in tm_cf_discrete) tm_cf_discrete_op[cat_op_intros]: 
  "tm_cf_discrete \<alpha> I F (op_cat \<CC>)"
  using tm_cf_discrete_ObjMap_in_Vset tm_cf_discrete_ArrMap_in_Vset 
  by (intro tm_cf_discreteI' cf_discrete_op) (auto simp: cat_op_simps)

lemmas [cat_op_intros] = tm_cf_discrete.tm_cf_discrete_op


subsubsection\<open>Discrete functor with tiny maps is a functor with tiny maps\<close>

lemma (in tm_cf_discrete) tm_cf_discrete_the_cf_discrete_is_tm_functor: 
  ":\<rightarrow>: I F \<CC> : :\<^sub>C I \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  by (intro is_tm_functorI' cf_discrete_the_cf_discrete_is_functor)
    (
      auto simp: 
        the_cf_discrete_components 
        tm_cf_discrete_ObjMap_in_Vset 
        tm_cf_discrete_ArrMap_in_Vset
    )

lemma (in tm_cf_discrete) tm_cf_discrete_the_cf_discrete_is_tm_functor':
  assumes "\<AA>' = :\<^sub>C I" and "\<CC>' = \<CC>"
  shows ":\<rightarrow>: I F \<CC> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule tm_cf_discrete_the_cf_discrete_is_tm_functor)

lemmas [cat_discrete_cs_intros] = 
  tm_cf_discrete.tm_cf_discrete_the_cf_discrete_is_tm_functor'

text\<open>\newpage\<close>

end