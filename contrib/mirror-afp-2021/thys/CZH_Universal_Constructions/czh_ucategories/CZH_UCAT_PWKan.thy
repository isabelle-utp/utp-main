(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Pointwise Kan extensions\<close>
theory CZH_UCAT_PWKan
  imports CZH_UCAT_Kan
begin



subsection\<open>Pointwise Kan extensions\<close>


text\<open>
The following subsection is based on elements of the
content of section 6.3 in \cite{riehl_category_2016} and
Chapter X-5 in \cite{mac_lane_categories_2010}.
\<close>

locale is_cat_pw_rKe = is_cat_rKe \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT> \<GG> \<epsilon>
  for \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT> \<GG> \<epsilon> +
  assumes cat_pw_rKe_preserved: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow>
    \<epsilon> :
      \<GG> \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT> :
      \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) : \<AA> \<mapsto>\<mapsto>\<^sub>C cat_Set \<alpha>)"

syntax "_is_cat_pw_rKe" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (
    \<open>(_ :/ _ \<circ>\<^sub>C\<^sub>F _ \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^sub>.\<^sub>p\<^sub>w\<index> _ :/ _ \<mapsto>\<^sub>C _ \<mapsto>\<^sub>C _)\<close> 
    [51, 51, 51, 51, 51, 51, 51] 51
  )
translations "\<epsilon> : \<GG> \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^sub>.\<^sub>p\<^sub>w\<^bsub>\<alpha>\<^esub> \<TT> : \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C \<AA>" \<rightleftharpoons> 
  "CONST is_cat_pw_rKe \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT> \<GG> \<epsilon>"

locale is_cat_pw_lKe = is_cat_lKe \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT> \<FF> \<eta>
  for \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT> \<FF> \<eta> +
  assumes cat_pw_lKe_preserved: "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr> \<Longrightarrow>
    op_ntcf \<eta> :
      op_cf \<FF> \<circ>\<^sub>C\<^sub>F op_cf \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> op_cf \<TT> :
      op_cat \<BB> \<mapsto>\<^sub>C op_cat \<CC> \<mapsto>\<^sub>C (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C cat_Set \<alpha>)"

syntax "_is_cat_pw_lKe" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (
    \<open>(_ :/ _ \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^sub>.\<^sub>p\<^sub>w\<index> _ \<circ>\<^sub>C\<^sub>F _ :/ _ \<mapsto>\<^sub>C _ \<mapsto>\<^sub>C _)\<close> 
    [51, 51, 51, 51, 51, 51, 51] 51
  )
translations "\<eta> : \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^sub>.\<^sub>p\<^sub>w\<^bsub>\<alpha>\<^esub> \<FF> \<circ>\<^sub>C\<^sub>F \<KK> : \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C \<AA>" \<rightleftharpoons> 
  "CONST is_cat_pw_lKe \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT> \<FF> \<eta>"

lemma (in is_cat_pw_rKe) cat_pw_rKe_preserved'[cat_Kan_cs_intros]: 
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "\<AA>' = \<AA>"
    and "\<HH>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-)"
    and "\<EE>' = cat_Set \<alpha>"
  shows "\<epsilon> : \<GG> \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT> : \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C (\<HH>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C \<EE>')"
  using assms(1) unfolding assms(2-4) by (rule cat_pw_rKe_preserved)

lemmas [cat_Kan_cs_intros] = is_cat_pw_rKe.cat_pw_rKe_preserved'

lemma (in is_cat_pw_lKe) cat_pw_lKe_preserved'[cat_Kan_cs_intros]: 
  assumes "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>"
    and "\<FF>' = op_cf \<FF>"
    and "\<KK>' = op_cf \<KK>"
    and "\<TT>' = op_cf \<TT>"
    and "\<BB>' = op_cat \<BB>"
    and "\<CC>' = op_cat \<CC>"
    and "\<AA>' = op_cat \<AA>"
    and "\<HH>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a)"
    and "\<EE>' = cat_Set \<alpha>"
  shows "op_ntcf \<eta> :
    \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT>' : \<BB>' \<mapsto>\<^sub>C \<CC>' \<mapsto>\<^sub>C (\<HH>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C \<EE>')"
  using assms(1) unfolding assms by (rule cat_pw_lKe_preserved)

lemmas [cat_Kan_cs_intros] = is_cat_pw_lKe.cat_pw_lKe_preserved'


text\<open>Rules.\<close>

lemma (in is_cat_pw_rKe) is_cat_pw_rKe_axioms'[cat_Kan_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
    and "\<GG>' = \<GG>"
    and "\<KK>' = \<KK>"
    and "\<TT>' = \<TT>"
    and "\<BB>' = \<BB>"
    and "\<AA>' = \<AA>"
    and "\<CC>' = \<CC>"
  shows "\<epsilon> : \<GG>' \<circ>\<^sub>C\<^sub>F \<KK>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^sub>.\<^sub>p\<^sub>w\<^bsub>\<alpha>'\<^esub> \<TT>' : \<BB>' \<mapsto>\<^sub>C \<CC>' \<mapsto>\<^sub>C \<AA>'"
  unfolding assms by (rule is_cat_pw_rKe_axioms)

mk_ide rf is_cat_pw_rKe_def[unfolded is_cat_pw_rKe_axioms_def]
  |intro is_cat_pw_rKeI|
  |dest is_cat_pw_rKeD[dest]|
  |elim is_cat_pw_rKeE[elim]|

lemmas [cat_Kan_cs_intros] = is_cat_pw_rKeD(1)

lemma (in is_cat_pw_lKe) is_cat_pw_lKe_axioms'[cat_Kan_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
    and "\<FF>' = \<FF>"
    and "\<KK>' = \<KK>"
    and "\<TT>' = \<TT>"
    and "\<BB>' = \<BB>"
    and "\<AA>' = \<AA>"
    and "\<CC>' = \<CC>"
  shows "\<eta> : \<TT>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^sub>.\<^sub>p\<^sub>w\<^bsub>\<alpha>'\<^esub> \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>' : \<BB>' \<mapsto>\<^sub>C \<CC>' \<mapsto>\<^sub>C \<AA>'"
  unfolding assms by (rule is_cat_pw_lKe_axioms)

mk_ide rf is_cat_pw_lKe_def[unfolded is_cat_pw_lKe_axioms_def]
  |intro is_cat_pw_lKeI|
  |dest is_cat_pw_lKeD[dest]|
  |elim is_cat_pw_lKeE[elim]|

lemmas [cat_Kan_cs_intros] = is_cat_pw_lKeD(1)


text\<open>Duality.\<close>

lemma (in is_cat_pw_rKe) is_cat_pw_lKe_op:
  "op_ntcf \<epsilon> :
    op_cf \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^sub>.\<^sub>p\<^sub>w\<^bsub>\<alpha>\<^esub> op_cf \<GG> \<circ>\<^sub>C\<^sub>F op_cf \<KK> :
    op_cat \<BB> \<mapsto>\<^sub>C op_cat \<CC> \<mapsto>\<^sub>C op_cat \<AA>"
proof(intro is_cat_pw_lKeI, unfold cat_op_simps)
  fix a assume prems: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  from cat_pw_rKe_preserved[OF prems] prems show
    "\<epsilon> :
      \<GG> \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT> :
      \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<AA>(-,a) : \<AA> \<mapsto>\<mapsto>\<^sub>C cat_Set \<alpha>)"
    by (cs_concl cs_simp: cat_op_simps cs_intro: cat_cs_intros)    
qed (cs_concl cs_intro: cat_op_intros)

lemma (in is_cat_pw_rKe) is_cat_pw_lKe_op'[cat_op_intros]:
  assumes "\<TT>' = op_cf \<TT>"
    and "\<GG>' = op_cf \<GG>"
    and "\<KK>' = op_cf \<KK>"
    and "\<BB>' = op_cat \<BB>"
    and "\<AA>' = op_cat \<AA>"
    and "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<epsilon> : \<TT>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^sub>.\<^sub>p\<^sub>w\<^bsub>\<alpha>\<^esub> \<GG>' \<circ>\<^sub>C\<^sub>F \<KK>' : \<BB>' \<mapsto>\<^sub>C \<CC>' \<mapsto>\<^sub>C \<AA>'"
  unfolding assms by (rule is_cat_pw_lKe_op)

lemmas [cat_op_intros] = is_cat_pw_rKe.is_cat_pw_lKe_op'

lemma (in is_cat_pw_lKe) is_cat_pw_rKe_op:
  "op_ntcf \<eta> :
    op_cf \<FF> \<circ>\<^sub>C\<^sub>F op_cf \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^sub>.\<^sub>p\<^sub>w\<^bsub>\<alpha>\<^esub> op_cf \<TT> :
    op_cat \<BB> \<mapsto>\<^sub>C op_cat \<CC> \<mapsto>\<^sub>C op_cat \<AA>"
proof(intro is_cat_pw_rKeI, unfold cat_op_simps)
  fix a assume prems: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  from cat_pw_lKe_preserved[unfolded cat_op_simps, OF prems] prems show 
    "op_ntcf \<eta> :
      op_cf \<FF> \<circ>\<^sub>C\<^sub>F op_cf \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> op_cf \<TT> :
      op_cat \<BB> \<mapsto>\<^sub>C op_cat \<CC> \<mapsto>\<^sub>C
      (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<AA>(a,-) : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C cat_Set \<alpha>)"
    by (cs_concl cs_simp: cat_op_simps cs_intro: cat_cs_intros)    
qed (cs_concl cs_intro: cat_op_intros)

lemma (in is_cat_pw_lKe) is_cat_pw_lKe_op'[cat_op_intros]:
  assumes "\<TT>' = op_cf \<TT>"
    and "\<FF>' = op_cf \<FF>"
    and "\<KK>' = op_cf \<KK>"
    and "\<BB>' = op_cat \<BB>"
    and "\<AA>' = op_cat \<AA>"
    and "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<eta> : \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^sub>.\<^sub>p\<^sub>w\<^bsub>\<alpha>\<^esub> \<TT>' : \<BB>' \<mapsto>\<^sub>C \<CC>' \<mapsto>\<^sub>C \<AA>'"
  unfolding assms by (rule is_cat_pw_rKe_op)

lemmas [cat_op_intros] = is_cat_pw_lKe.is_cat_pw_lKe_op'



(*FIXME: any reason not to generalize and include in CZH_UCAT_Hom?*)
subsection\<open>Cone functor\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cf_Cone :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_Cone \<alpha> \<beta> \<FF> = 
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_Funct \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (\<FF>\<lparr>HomCod\<rparr>)(-,cf_map \<FF>) \<circ>\<^sub>C\<^sub>F
    op_cf (\<Delta>\<^sub>C \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (\<FF>\<lparr>HomCod\<rparr>))"


text\<open>An alternative form of the definition.\<close>

context is_functor
begin

lemma cf_Cone_def': 
  "cf_Cone \<alpha> \<beta> \<FF> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_Funct \<alpha> \<AA> \<BB>(-,cf_map \<FF>) \<circ>\<^sub>C\<^sub>F op_cf (\<Delta>\<^sub>C \<alpha> \<AA> \<BB>)"
  unfolding cf_Cone_def cat_cs_simps by simp

end


subsubsection\<open>Object map\<close>

lemma (in is_tm_functor) cf_Cone_ObjMap_vsv[cat_Kan_cs_intros]:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
  shows "vsv (cf_Cone \<alpha> \<beta> \<FF>\<lparr>ObjMap\<rparr>)"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C \<alpha> \<AA> \<BB>\<close>
    by
      (
        cs_concl cs_intro: 
          cat_small_cs_intros cat_cs_intros cat_op_intros
      )+
  from \<Delta>.is_functor_axioms assms(2) interpret \<beta>\<Delta>: 
    is_functor \<beta> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C \<alpha> \<AA> \<BB>\<close>
    by (cs_intro_step is_functor.cf_is_functor_if_ge_Limit)
      (cs_concl cs_intro: cat_cs_intros)+
  from assms(2) show ?thesis
    unfolding cf_Cone_def
    by
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_Funct_components(1) cat_op_simps 
          cs_intro:
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_Kan_cs_intros] = is_tm_functor.cf_Cone_ObjMap_vsv

lemma (in is_tm_functor) cf_Cone_ObjMap_vdomain[cat_Kan_cs_simps]:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (cf_Cone \<alpha> \<beta> \<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C \<alpha> \<AA> \<BB>\<close>
    by
      (
        cs_concl cs_intro: 
          cat_small_cs_intros cat_cs_intros cat_op_intros
      )+
  from \<Delta>.is_functor_axioms assms(2) interpret \<beta>\<Delta>: 
    is_functor \<beta> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C \<alpha> \<AA> \<BB>\<close>
    by (cs_intro_step is_functor.cf_is_functor_if_ge_Limit)
      (cs_concl cs_intro: cat_cs_intros)+
  from assms(2) show ?thesis
    unfolding cf_Cone_def'
    by
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_Funct_components(1) cat_op_simps
          cs_intro:
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_Kan_cs_simps] = is_tm_functor.cf_Cone_ObjMap_vdomain

lemma (in is_tm_functor) cf_Cone_ObjMap_app[cat_Kan_cs_simps]:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "cf_Cone \<alpha> \<beta> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> =
    Hom (cat_Funct \<alpha> \<AA> \<BB>) (cf_map (cf_const \<AA> \<BB> b)) (cf_map \<FF>)"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C \<alpha> \<AA> \<BB>\<close>
    by
      (
        cs_concl cs_intro: 
          cat_small_cs_intros cat_cs_intros cat_op_intros
      )+
  from \<Delta>.is_functor_axioms assms(2) interpret \<beta>\<Delta>: 
    is_functor \<beta> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C \<alpha> \<AA> \<BB>\<close>
    by (cs_intro_step is_functor.cf_is_functor_if_ge_Limit)
      (cs_concl cs_intro: cat_cs_intros)+
  from assms(2,3) show ?thesis
    unfolding cf_Cone_def
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_Funct_components(1) cat_op_simps
          cs_intro:
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_Kan_cs_simps] = is_tm_functor.cf_Cone_ObjMap_app


subsubsection\<open>Arrow map\<close>

lemma (in is_tm_functor) cf_Cone_ArrMap_vsv[cat_Kan_cs_intros]:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
  shows "vsv (cf_Cone \<alpha> \<beta> \<FF>\<lparr>ArrMap\<rparr>)"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C \<alpha> \<AA> \<BB>\<close>
    by
      (
        cs_concl cs_intro: 
          cat_small_cs_intros cat_cs_intros cat_op_intros
      )+
  from \<Delta>.is_functor_axioms assms(2) interpret \<beta>\<Delta>: 
    is_functor \<beta> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C \<alpha> \<AA> \<BB>\<close>
    by (cs_intro_step is_functor.cf_is_functor_if_ge_Limit)
      (cs_concl cs_intro: cat_cs_intros)+
  from assms(2) show ?thesis
    unfolding cf_Cone_def
    by
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_Funct_components(1) cat_op_simps 
          cs_intro:
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_Kan_cs_intros] = is_tm_functor.cf_Cone_ArrMap_vsv

lemma (in is_tm_functor) cf_Cone_ArrMap_vdomain[cat_Kan_cs_simps]:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (cf_Cone \<alpha> \<beta> \<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C \<alpha> \<AA> \<BB>\<close>
    by
      (
        cs_concl cs_intro: 
          cat_small_cs_intros cat_cs_intros cat_op_intros
      )+
  from \<Delta>.is_functor_axioms assms(2) interpret \<beta>\<Delta>: 
    is_functor \<beta> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C \<alpha> \<AA> \<BB>\<close>
    by (cs_intro_step is_functor.cf_is_functor_if_ge_Limit)
      (cs_concl cs_intro: cat_cs_intros)+
  from assms(2) show ?thesis
    unfolding cf_Cone_def'
    by
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_Funct_components(1) cat_op_simps
          cs_intro:
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_Kan_cs_simps] = is_tm_functor.cf_Cone_ArrMap_vdomain

lemma (in is_tm_functor) cf_Cone_ArrMap_app[cat_Kan_cs_simps]:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    and "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "cf_Cone \<alpha> \<beta> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = cf_hom
    (cat_Funct \<alpha> \<AA> \<BB>)
    [ntcf_arrow (ntcf_const \<AA> \<BB> f), cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>cf_map \<FF>\<rparr>]\<^sub>\<circ>"
proof-
  from assms interpret \<beta>: \<Z> \<beta> by simp 
  from assms interpret \<Delta>: is_functor \<alpha> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C \<alpha> \<AA> \<BB>\<close>
    by
      (
        cs_concl cs_intro: 
          cat_small_cs_intros cat_cs_intros cat_op_intros
      )+
  from \<Delta>.is_functor_axioms assms(2) interpret \<beta>\<Delta>: 
    is_functor \<beta> \<BB> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close> \<open>\<Delta>\<^sub>C \<alpha> \<AA> \<BB>\<close>
    by (cs_intro_step is_functor.cf_is_functor_if_ge_Limit)
      (cs_concl cs_intro: cat_cs_intros)+
  from assms(2,3) show ?thesis
    unfolding cf_Cone_def
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_Funct_components(1) cat_op_simps 
          cs_intro:
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros cat_op_intros
      )
qed

lemmas [cat_Kan_cs_simps] = is_tm_functor.cf_Cone_ArrMap_app


subsubsection\<open>The cone functor is a functor\<close>

lemma (in is_tm_functor) tm_cf_cf_Cone_is_functor:
  "cf_Cone \<alpha> \<alpha> \<FF> : op_cat \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  unfolding cf_Cone_def'
  by
    (
      cs_concl
        cs_simp: cat_op_simps cat_Funct_components(1)
        cs_intro:
          cat_small_cs_intros
          cat_cs_intros
          cat_FUNCT_cs_intros
          cat_op_intros
    )

lemma (in is_tm_functor) tm_cf_cf_Cone_is_functor_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "cf_Cone \<alpha> \<beta> \<FF> : op_cat \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
proof-
  from assms interpret \<AA>\<BB>: category \<alpha> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close>
    by
      (
        cs_concl cs_intro:
          cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  interpret \<beta>_\<AA>\<BB>: category \<beta> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close>
    by (rule \<AA>\<BB>.cat_category_if_ge_Limit)
      (cs_concl cs_intro: cat_cs_intros assms)+
  from assms interpret op_\<Delta>: 
    is_tiny_functor \<beta> \<open>op_cat \<BB>\<close> \<open>op_cat (cat_Funct \<alpha> \<AA> \<BB>)\<close> \<open>op_cf (\<Delta>\<^sub>C \<alpha> \<AA> \<BB>)\<close>
    by (intro is_functor.cf_is_tiny_functor_if_ge_Limit)
      (
        cs_concl cs_intro:
          cat_small_cs_intros cat_cs_intros cat_op_intros
      )+
  have "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_Funct \<alpha> \<AA> \<BB>(-,cf_map \<FF>) :
    op_cat (cat_Funct \<alpha> \<AA> \<BB>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
    by
      (
        cs_concl
          cs_simp: cat_Funct_components(1)
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  then show "cf_Cone \<alpha> \<beta> \<FF> : op_cat \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
    unfolding cf_Cone_def'
    by (cs_concl cs_intro: cat_cs_intros)
qed



subsection\<open>Lemma X.5: \<open>L_10_5_N\<close>\label{sec:lem_X_5_start}\<close>


text\<open>
This subsection and several further subsections 
(\ref{sec:lem_X_5_start}-\ref{sec:lem_X_5_end})
expose definitions that are used in the proof of the technical lemma that
was used in the proof of Theorem 3 from Chapter X-5
in \cite{mac_lane_categories_2010}.
\<close>

definition L_10_5_N :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "L_10_5_N \<alpha> \<beta> \<TT> \<KK> c =
    [
      (
        \<lambda>a\<in>\<^sub>\<circ>\<TT>\<lparr>HomCod\<rparr>\<lparr>Obj\<rparr>.
          cf_nt \<alpha> \<beta> \<KK>\<lparr>ObjMap\<rparr>\<lparr>cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<TT>\<lparr>HomCod\<rparr>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>), c\<rparr>\<^sub>\<bullet>
      ),
      (
        \<lambda>f\<in>\<^sub>\<circ>\<TT>\<lparr>HomCod\<rparr>\<lparr>Arr\<rparr>.
          cf_nt \<alpha> \<beta> \<KK>\<lparr>ArrMap\<rparr>\<lparr>
            ntcf_arrow (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<TT>\<lparr>HomCod\<rparr>(f,-) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<TT>), \<KK>\<lparr>HomCod\<rparr>\<lparr>CId\<rparr>\<lparr>c\<rparr>
            \<rparr>\<^sub>\<bullet>
      ),
      op_cat (\<TT>\<lparr>HomCod\<rparr>),
      cat_Set \<beta>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma L_10_5_N_components:
  shows "L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr> =
      (
        \<lambda>a\<in>\<^sub>\<circ>\<TT>\<lparr>HomCod\<rparr>\<lparr>Obj\<rparr>.
          cf_nt \<alpha> \<beta> \<KK>\<lparr>ObjMap\<rparr>\<lparr>cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<TT>\<lparr>HomCod\<rparr>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>), c\<rparr>\<^sub>\<bullet>
      )"
    and "L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ArrMap\<rparr> =
      (
        \<lambda>f\<in>\<^sub>\<circ>\<TT>\<lparr>HomCod\<rparr>\<lparr>Arr\<rparr>.
          cf_nt \<alpha> \<beta> \<KK>\<lparr>ArrMap\<rparr>\<lparr>
            ntcf_arrow (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<TT>\<lparr>HomCod\<rparr>(f,-) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<TT>), \<KK>\<lparr>HomCod\<rparr>\<lparr>CId\<rparr>\<lparr>c\<rparr>
            \<rparr>\<^sub>\<bullet>
      )"
    and "L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>HomDom\<rparr> = op_cat (\<TT>\<lparr>HomCod\<rparr>)"
    and "L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>HomCod\<rparr> = cat_Set \<beta>"
  unfolding L_10_5_N_def dghm_field_simps by (simp_all add: nat_omega_simps)

context
  fixes \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<TT>: "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)
interpretation \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule \<TT>)

lemmas L_10_5_N_components' = L_10_5_N_components[
    where \<TT>=\<TT> and \<KK>=\<KK>, unfolded cat_cs_simps
    ]

lemmas [cat_Kan_cs_simps] = L_10_5_N_components'(3,4)

end


subsubsection\<open>Object map\<close>

mk_VLambda L_10_5_N_components(1)
  |vsv L_10_5_N_ObjMap_vsv[cat_Kan_cs_intros]|

context
  fixes \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT> c
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<TT>: "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

mk_VLambda L_10_5_N_components'(1)[OF \<KK> \<TT>]
  |vdomain L_10_5_N_ObjMap_vdomain[cat_Kan_cs_simps]|
  |app L_10_5_N_ObjMap_app[cat_Kan_cs_simps]|

end


subsubsection\<open>Arrow map\<close>

mk_VLambda L_10_5_N_components(2)
  |vsv L_10_5_N_ArrMap_vsv[cat_Kan_cs_intros]|

context
  fixes \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT> c
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<TT>: "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

mk_VLambda L_10_5_N_components'(2)[OF \<KK> \<TT>]
  |vdomain L_10_5_N_ArrMap_vdomain[cat_Kan_cs_simps]|
  |app L_10_5_N_ArrMap_app[cat_Kan_cs_simps]|

end


subsubsection\<open>\<open>L_10_5_N\<close> is a functor\<close>

lemma L_10_5_N_is_functor: 
  assumes "\<Z> \<beta>" 
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "L_10_5_N \<alpha> \<beta> \<TT> \<KK> c : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
proof-

  let ?FUNCT = \<open>\<lambda>\<AA>. cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)\<close>

  interpret \<beta>: \<Z> \<beta> by (rule assms(1))

  interpret \<KK>: is_tm_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(3))
  interpret \<TT>: is_tm_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(4))

  from assms(2) interpret FUNCT_\<BB>: tiny_category \<beta> \<open>?FUNCT \<BB>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  
  interpret \<beta>\<KK>: is_tiny_functor \<beta> \<BB> \<CC> \<KK>
    by (rule is_functor.cf_is_tiny_functor_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<TT>: is_tiny_functor \<beta> \<BB> \<AA> \<TT>
    by (rule is_functor.cf_is_tiny_functor_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+

  from assms(2) interpret cf_nt: 
    is_functor \<beta> \<open>?FUNCT \<BB> \<times>\<^sub>C \<CC>\<close> \<open>cat_Set \<beta>\<close> \<open>cf_nt \<alpha> \<beta> \<KK>\<close>
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

  show ?thesis
  proof(intro is_functorI')

    show "vfsequence (L_10_5_N \<alpha> \<beta> \<TT> \<KK> c)" unfolding L_10_5_N_def by simp
    show "vcard (L_10_5_N \<alpha> \<beta> \<TT> \<KK> c) = 4\<^sub>\<nat>" 
      unfolding L_10_5_N_def by (simp add: nat_omega_simps)
    show "vsv (L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>)" 
      by (cs_concl cs_intro: cat_Kan_cs_intros)
    from assms(3,4) show "vsv (L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ArrMap\<rparr>)"
      by (cs_concl cs_intro: cat_Kan_cs_intros)
    from assms show "\<D>\<^sub>\<circ> (L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>) = op_cat \<AA>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_Kan_cs_simps cat_op_simps cs_intro: cat_cs_intros
        )
    show "\<R>\<^sub>\<circ> (L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<beta>\<lparr>Obj\<rparr>"
      unfolding L_10_5_N_components'[OF \<KK>.is_functor_axioms \<TT>.is_functor_axioms]
    proof(rule vrange_VLambda_vsubset)
      fix a assume prems: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      from prems assms show
        "cf_nt \<alpha> \<beta> \<KK>\<lparr>ObjMap\<rparr>\<lparr>cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>), c\<rparr>\<^sub>\<bullet> \<in>\<^sub>\<circ>
          cat_Set \<beta>\<lparr>Obj\<rparr>"
        by 
          (
            cs_concl
              cs_simp: cat_Set_components(1) cat_cs_simps  cat_FUNCT_cs_simps
              cs_intro: 
                cat_cs_intros FUNCT_\<BB>.cat_Hom_in_Vset cat_FUNCT_cs_intros
          )
    qed

    from assms show "\<D>\<^sub>\<circ> (L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ArrMap\<rparr>) = op_cat \<AA>\<lparr>Arr\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_Kan_cs_simps cat_op_simps cs_intro: cat_cs_intros
        )

    show "L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> :
      L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "f : a \<mapsto>\<^bsub>op_cat \<AA>\<^esub> b" for a b f
      using that assms
      unfolding cat_op_simps
      by 
        (
          cs_concl 
            cs_simp: L_10_5_N_ArrMap_app L_10_5_N_ObjMap_app 
            cs_intro: cat_cs_intros cat_prod_cs_intros cat_FUNCT_cs_intros
        )

    show 
      "L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>op_cat \<AA>\<^esub> f\<rparr> =
        L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      if "g : b' \<mapsto>\<^bsub>op_cat \<AA>\<^esub> c'" and "f : a' \<mapsto>\<^bsub>op_cat \<AA>\<^esub> b'" for b' c' g a' f
    proof-
      from that assms(5) show ?thesis
        unfolding cat_op_simps
        by (*slow*)
          (
            cs_concl
              cs_intro:
                cat_cs_intros
                cat_prod_cs_intros
                cat_FUNCT_cs_intros 
                cat_op_intros
              cs_simp:
                cat_cs_simps
                cat_Kan_cs_simps
                cat_FUNCT_cs_simps 
                cat_prod_cs_simps 
                cat_op_simps
                cf_nt.cf_ArrMap_Comp[symmetric]
          )
    qed

    show 
      "L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ArrMap\<rparr>\<lparr>op_cat \<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>\<rparr> =
        cat_Set \<beta>\<lparr>CId\<rparr>\<lparr>L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
      if "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>" for a
    proof-
      note [cat_cs_simps] = 
        ntcf_id_cf_comp[symmetric] 
        ntcf_arrow_id_ntcf_id[symmetric]
        cat_FUNCT_CId_app[symmetric] 
      from that[unfolded cat_op_simps] assms show ?thesis
        by (*slow*)
          (
            cs_concl
              cs_intro:
                cat_cs_intros
                cat_FUNCT_cs_intros
                cat_prod_cs_intros
                cat_op_intros
              cs_simp: 
                cat_FUNCT_cs_simps cat_cs_simps cat_Kan_cs_simps cat_op_simps
          )
    qed

  qed (cs_concl cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros)+

qed

lemma L_10_5_N_is_functor'[cat_Kan_cs_intros]: 
  assumes "\<Z> \<beta>" 
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<AA>' = op_cat \<AA>"
    and "\<BB>' = cat_Set \<beta>"
    and "\<beta>' = \<beta>"
  shows "L_10_5_N \<alpha> \<beta> \<TT> \<KK> c : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>'\<^esub> \<BB>'"
  using assms(1-5) unfolding assms(6-8) by (rule L_10_5_N_is_functor)



subsection\<open>Lemma X.5: \<open>L_10_5_\<upsilon>_arrow\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition L_10_5_\<upsilon>_arrow :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau> a b =
    [
      (\<lambda>f\<in>\<^sub>\<circ>Hom (\<KK>\<lparr>HomCod\<rparr>) c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>). \<tau>\<lparr>NTMap\<rparr>\<lparr>0, b, f\<rparr>\<^sub>\<bullet>),
      Hom (\<KK>\<lparr>HomCod\<rparr>) c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>),
      Hom (\<TT>\<lparr>HomCod\<rparr>) a (\<TT>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma L_10_5_\<upsilon>_arrow_components:
  shows "L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau> a b\<lparr>ArrVal\<rparr> =
    (\<lambda>f\<in>\<^sub>\<circ>Hom (\<KK>\<lparr>HomCod\<rparr>) c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>). \<tau>\<lparr>NTMap\<rparr>\<lparr>0, b, f\<rparr>\<^sub>\<bullet>)"
    and "L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau> a b\<lparr>ArrDom\<rparr> = Hom (\<KK>\<lparr>HomCod\<rparr>) c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    and "L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau> a b\<lparr>ArrCod\<rparr> = Hom (\<TT>\<lparr>HomCod\<rparr>) a (\<TT>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
  unfolding L_10_5_\<upsilon>_arrow_def arr_field_simps 
  by (simp_all add: nat_omega_simps) 

context
  fixes \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<TT>: "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)
interpretation \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule \<TT>)

lemmas L_10_5_\<upsilon>_arrow_components' = L_10_5_\<upsilon>_arrow_components[
    where \<TT>=\<TT> and \<KK>=\<KK>, unfolded cat_cs_simps
    ]

lemmas [cat_Kan_cs_simps] = L_10_5_\<upsilon>_arrow_components'(2,3)

end


subsubsection\<open>Arrow value\<close>

mk_VLambda L_10_5_\<upsilon>_arrow_components(1)
  |vsv L_10_5_\<upsilon>_arrow_ArrVal_vsv[cat_Kan_cs_intros]|

context
  fixes \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<TT>: "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

mk_VLambda L_10_5_\<upsilon>_arrow_components'(1)[OF \<KK> \<TT>]
  |vdomain L_10_5_\<upsilon>_arrow_ArrVal_vdomain[cat_Kan_cs_simps]|
  |app L_10_5_\<upsilon>_arrow_ArrVal_app[unfolded in_Hom_iff]|

end

lemma L_10_5_\<upsilon>_arrow_ArrVal_app':
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "f : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
  shows "L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau> a b\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> = \<tau>\<lparr>NTMap\<rparr>\<lparr>0, b, f\<rparr>\<^sub>\<bullet>"
proof-
  interpret \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))
  from assms(3) have c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  show ?thesis by (rule L_10_5_\<upsilon>_arrow_ArrVal_app[OF assms(1,2,3)])
qed


subsubsection\<open>\<open>L_10_5_\<upsilon>_arrow\<close> is an arrow\<close>

lemma L_10_5_\<upsilon>_arrow_ArrVal_is_arr: 
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<tau>' = ntcf_arrow \<tau>"
    and "\<tau> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "f : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau>' a b\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> : a \<mapsto>\<^bsub>\<AA>\<^esub> \<TT>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
proof-
  interpret \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))
  interpret \<tau>: is_cat_cone \<alpha> a \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<tau> by (rule assms(4))
  from assms(5,6) show ?thesis
    unfolding assms(3)
    by
      (
        cs_concl
          cs_simp:
            cat_cs_simps
            L_10_5_\<upsilon>_arrow_ArrVal_app
            cat_comma_cs_simps
            cat_FUNCT_cs_simps
          cs_intro: cat_cs_intros cat_comma_cs_intros
      )
qed

lemma L_10_5_\<upsilon>_arrow_ArrVal_is_arr'[cat_Kan_cs_intros]: 
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<tau>' = ntcf_arrow \<tau>"
    and "a' = a"
    and "b' = \<TT>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    and "\<AA>' = \<AA>"
    and "\<tau> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "f : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau>' a b\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> : a' \<mapsto>\<^bsub>\<AA>\<^esub> b'"
  using assms(1-3, 7-9) 
  unfolding assms(3-6) 
  by (rule L_10_5_\<upsilon>_arrow_ArrVal_is_arr)


subsubsection\<open>Further elementary properties\<close>

lemma L_10_5_\<upsilon>_arrow_is_arr: 
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<tau>' = ntcf_arrow \<tau>"
    and "\<tau> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau>' a b :
    Hom \<CC> c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<AA> a (\<TT>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
proof-
  note L_10_5_\<upsilon>_arrow_components = L_10_5_\<upsilon>_arrow_components'[OF assms(1,2)]
  interpret \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))
  interpret \<tau>: is_cat_cone \<alpha> a \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<tau> by (rule assms(5))
  show ?thesis
  proof(intro cat_Set_is_arrI)
    show "arr_Set \<alpha> (L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau>' a b)"
    proof(intro arr_SetI)
      show "vfsequence (L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau>' a b)" 
        unfolding L_10_5_\<upsilon>_arrow_def by simp
      show "vcard (L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau>' a b) = 3\<^sub>\<nat>"
        unfolding L_10_5_\<upsilon>_arrow_def by (simp add: nat_omega_simps)
      show 
        "\<R>\<^sub>\<circ> (L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau>' a b\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ>
          L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau>' a b\<lparr>ArrCod\<rparr>"
        unfolding L_10_5_\<upsilon>_arrow_components
      proof(intro vrange_VLambda_vsubset, unfold in_Hom_iff)
        fix f assume "f : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        from L_10_5_\<upsilon>_arrow_ArrVal_is_arr[OF assms(1,2,4,5) this assms(6)] this 
        show "\<tau>'\<lparr>NTMap\<rparr>\<lparr>0, b, f\<rparr>\<^sub>\<bullet> : a \<mapsto>\<^bsub>\<AA>\<^esub> \<TT>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
          by 
            (
              cs_prems 
                cs_simp: L_10_5_\<upsilon>_arrow_ArrVal_app' cat_cs_simps 
                cs_intro: cat_cs_intros
            ) 
      qed
      from assms(3,6) show "L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau>' a b\<lparr>ArrDom\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
        by (cs_concl cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros)
      from assms(1-3,6) \<tau>.cat_cone_obj show
        "L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau>' a b\<lparr>ArrCod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
        by (cs_concl cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros)
    qed (auto simp: L_10_5_\<upsilon>_arrow_components)
  qed (simp_all add: L_10_5_\<upsilon>_arrow_components)
qed

lemma L_10_5_\<upsilon>_arrow_is_arr'[cat_Kan_cs_intros]: 
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<tau>' = ntcf_arrow \<tau>"
    and "\<tau> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "A = Hom \<CC> c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    and "B = Hom \<AA> a (\<TT>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    and "\<CC>' = cat_Set \<alpha>"
  shows "L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau>' a b : A \<mapsto>\<^bsub>\<CC>'\<^esub> B"
  using assms(1-6) unfolding assms(7-9) by (rule L_10_5_\<upsilon>_arrow_is_arr)

lemma L_10_5_\<upsilon>_cf_hom[cat_Kan_cs_simps]:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<tau>' = ntcf_arrow \<tau>"
    and "\<tau> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "f : a' \<mapsto>\<^bsub>\<BB>\<^esub> b'"
  shows 
    "L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau>' a b' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
    cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>, \<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>]\<^sub>\<circ> =
      cf_hom \<AA> [\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>, \<TT>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
      L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau>' a a'"
    (is "?lhs = ?rhs")
proof-

  interpret \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))
  interpret \<tau>: is_cat_cone \<alpha> a \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<tau> by (rule assms(5))

  have [cat_Kan_cs_simps]:
    "\<tau>\<lparr>NTMap\<rparr>\<lparr>a'', b'', \<KK>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'\<rparr>\<^sub>\<bullet> = 
      \<TT>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<tau>\<lparr>NTMap\<rparr>\<lparr>a', b', f'\<rparr>\<^sub>\<bullet>"
    if F_def: "F = [[a', b', f']\<^sub>\<circ>, [a'', b'', f'']\<^sub>\<circ>, [g', h']\<^sub>\<circ>]\<^sub>\<circ>"
      and A_def: "A = [a', b', f']\<^sub>\<circ>"
      and B_def: "B = [a'', b'', f'']\<^sub>\<circ>"
      and F: "F : A \<mapsto>\<^bsub>c \<down>\<^sub>C\<^sub>F \<KK>\<^esub> B"
    for F A B a' b' f' a'' b'' f'' g' h'
  proof-
    from F[unfolded F_def A_def B_def] assms(3) have a'_def: "a' = 0"
      and a''_def: "a'' = 0"
      and g'_def: "g' = 0"
      and h': "h' : b' \<mapsto>\<^bsub>\<BB>\<^esub> b''"
      and f': "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
      and f'': "f'' : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b''\<rparr>"
      and f''_def: "\<KK>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' = f''"
      by auto
    from 
      \<tau>.ntcf_Comp_commute[OF F] 
      that(2) F g' h' f' f'' 
      \<KK>.is_functor_axioms 
      \<TT>.is_functor_axioms 
    show 
      "\<tau>\<lparr>NTMap\<rparr>\<lparr>a'', b'', \<KK>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'\<rparr>\<^sub>\<bullet> = 
        \<TT>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<tau>\<lparr>NTMap\<rparr>\<lparr>a', b', f'\<rparr>\<^sub>\<bullet>"
      unfolding F_def A_def B_def a'_def a''_def g'_def 
      by (*slow*)
        (
          cs_prems 1
            cs_simp: cat_cs_simps cat_comma_cs_simps f''_def[symmetric]
            cs_intro: cat_cs_intros cat_comma_cs_intros
        )
  qed

  from assms(3) assms(6,7) \<KK>.HomCod.category_axioms have lhs_is_arr:
    "?lhs : Hom \<CC> c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<AA> a (\<TT>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>)"
    unfolding assms(4)
    by
      (
        cs_concl cs_simp: cs_intro:
          cat_lim_cs_intros 
          cat_cs_intros 
          cat_Kan_cs_intros 
          cat_prod_cs_intros 
          cat_op_intros
      )
  then have dom_lhs: "\<D>\<^sub>\<circ> ((?lhs)\<lparr>ArrVal\<rparr>) = Hom \<CC> c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>)" 
    by (cs_concl cs_simp: cat_cs_simps)
  from assms(3) assms(6,7) \<KK>.HomCod.category_axioms \<TT>.HomCod.category_axioms 
  have rhs_is_arr:
    "?rhs : Hom \<CC> c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<AA> a (\<TT>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>)"
    unfolding assms(4)
    by
      (
        cs_concl cs_intro:
          cat_lim_cs_intros 
          cat_cs_intros 
          cat_Kan_cs_intros 
          cat_prod_cs_intros 
          cat_op_intros
      )
  then have dom_rhs: "\<D>\<^sub>\<circ> ((?rhs)\<lparr>ArrVal\<rparr>) = Hom \<CC> c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>)" 
    by (cs_concl cs_simp: cat_cs_simps)
  show ?thesis
  proof(rule arr_Set_eqI)
    from lhs_is_arr show arr_Set_lhs: "arr_Set \<alpha> ?lhs"
      by (auto dest: cat_Set_is_arrD(1))
    from rhs_is_arr show arr_Set_rhs: "arr_Set \<alpha> ?rhs"
      by (auto dest: cat_Set_is_arrD(1))
    show "?lhs\<lparr>ArrVal\<rparr> = ?rhs\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
      fix g assume prems: "g : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>"
      from prems assms(7) have \<KK>f: 
        "\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
        by (cs_concl cs_intro: cat_cs_intros)
      with assms(6,7) prems \<KK>.HomCod.category_axioms \<TT>.HomCod.category_axioms 
      show "?lhs\<lparr>ArrVal\<rparr>\<lparr>g\<rparr> = ?rhs\<lparr>ArrVal\<rparr>\<lparr>g\<rparr>"
          by (*slow*)
            (
              cs_concl
                cs_intro:
                  cat_lim_cs_intros 
                  cat_cs_intros 
                  cat_Kan_cs_intros
                  cat_comma_cs_intros
                  cat_prod_cs_intros 
                  cat_op_intros 
                  cat_1_is_arrI
                cs_simp:
                  L_10_5_\<upsilon>_arrow_ArrVal_app' 
                  cat_cs_simps
                  cat_Kan_cs_simps
                  cat_op_simps
                  cat_FUNCT_cs_simps
                  cat_comma_cs_simps
                  assms(4)
            )+
    qed (use arr_Set_lhs arr_Set_rhs in auto)
  qed
    (
      use lhs_is_arr rhs_is_arr in
        \<open>cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros\<close>
    )+
qed



subsection\<open>Lemma X.5: \<open>L_10_5_\<tau>\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition L_10_5_\<tau> where "L_10_5_\<tau> \<TT> \<KK> c \<upsilon> a = 
  [
    (\<lambda>bf\<in>\<^sub>\<circ>c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>. \<upsilon>\<lparr>NTMap\<rparr>\<lparr>bf\<lparr>1\<^sub>\<nat>\<rparr>\<rparr>\<lparr>ArrVal\<rparr>\<lparr>bf\<lparr>2\<^sub>\<nat>\<rparr>\<rparr>),
    cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) (\<TT>\<lparr>HomCod\<rparr>) a,
    \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>,
    c \<down>\<^sub>C\<^sub>F \<KK>,
    (\<TT>\<lparr>HomCod\<rparr>)
  ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma L_10_5_\<tau>_components: 
  shows "L_10_5_\<tau> \<TT> \<KK> c \<upsilon> a\<lparr>NTMap\<rparr> =
    (\<lambda>bf\<in>\<^sub>\<circ>c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>. \<upsilon>\<lparr>NTMap\<rparr>\<lparr>bf\<lparr>1\<^sub>\<nat>\<rparr>\<rparr>\<lparr>ArrVal\<rparr>\<lparr>bf\<lparr>2\<^sub>\<nat>\<rparr>\<rparr>)"
    and "L_10_5_\<tau> \<TT> \<KK> c \<upsilon> a\<lparr>NTDom\<rparr> = cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) (\<TT>\<lparr>HomCod\<rparr>) a"
    and "L_10_5_\<tau> \<TT> \<KK> c \<upsilon> a\<lparr>NTCod\<rparr> = \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>"
    and "L_10_5_\<tau> \<TT> \<KK> c \<upsilon> a\<lparr>NTDGDom\<rparr> = c \<down>\<^sub>C\<^sub>F \<KK>"
    and "L_10_5_\<tau> \<TT> \<KK> c \<upsilon> a\<lparr>NTDGCod\<rparr> = (\<TT>\<lparr>HomCod\<rparr>)"
  unfolding L_10_5_\<tau>_def nt_field_simps by (simp_all add: nat_omega_simps)

context
  fixes \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<TT>: "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)
interpretation \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule \<TT>)

lemmas L_10_5_\<tau>_components' = L_10_5_\<tau>_components[
  where \<TT>=\<TT> and \<KK>=\<KK>, unfolded cat_cs_simps
  ]

lemmas [cat_Kan_cs_simps] = L_10_5_\<tau>_components'(2-5)

end


subsubsection\<open>Natural transformation map\<close>

mk_VLambda L_10_5_\<tau>_components(1)
  |vsv L_10_5_\<tau>_NTMap_vsv[cat_Kan_cs_intros]|
  |vdomain L_10_5_\<tau>_NTMap_vdomain[cat_Kan_cs_simps]|

lemma L_10_5_\<tau>_NTMap_app[cat_Kan_cs_simps]: 
  assumes "bf = [0, b, f]\<^sub>\<circ>" and "bf \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>" 
  shows "L_10_5_\<tau> \<TT> \<KK> c \<upsilon> a\<lparr>NTMap\<rparr>\<lparr>bf\<rparr> = \<upsilon>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
  using assms unfolding L_10_5_\<tau>_components by (simp add: nat_omega_simps)


subsubsection\<open>\<open>L_10_5_\<tau>\<close> is a cone\<close>

lemma L_10_5_\<tau>_is_cat_cone[cat_cs_intros]:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and \<upsilon>'_def: "\<upsilon>' = ntcf_arrow \<upsilon>"
    and \<upsilon>: "\<upsilon> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "L_10_5_\<tau> \<TT> \<KK> c \<upsilon>' a : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-

  let ?H_\<CC> = \<open>\<lambda>c. Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-)\<close> 
  let ?H_\<AA> = \<open>\<lambda>a. Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-)\<close>

  interpret \<KK>: is_tm_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<TT>: is_tm_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))

  from assms(3) interpret c\<KK>: tiny_category \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close>
    by (cs_concl cs_intro: cat_comma_cs_intros)
  from assms(3) interpret \<Pi>c: is_tm_functor \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<BB> \<open>c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close>
    by
      (
        cs_concl
          cs_simp: cat_comma_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_comma_cs_intros
      )
  interpret \<upsilon>: is_ntcf \<alpha> \<BB> \<open>cat_Set \<alpha>\<close> \<open>?H_\<CC> c \<circ>\<^sub>C\<^sub>F \<KK>\<close> \<open>?H_\<AA> a \<circ>\<^sub>C\<^sub>F \<TT>\<close> \<upsilon>
    by (rule \<upsilon>)

  show ?thesis
  proof(intro is_cat_coneI is_tm_ntcfI' is_ntcfI')
    show "vfsequence (L_10_5_\<tau> \<TT> \<KK> c \<upsilon>' a)" unfolding L_10_5_\<tau>_def by simp
    show "vcard (L_10_5_\<tau> \<TT> \<KK> c \<upsilon>' a) = 5\<^sub>\<nat>" 
      unfolding L_10_5_\<tau>_def by (simp add: nat_omega_simps)
    from a interpret cf_const:
      is_tm_functor \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> a\<close> 
      by (cs_concl cs_intro: cat_small_cs_intros cat_cs_intros)
    show "L_10_5_\<tau> \<TT> \<KK> c \<upsilon>' a\<lparr>NTMap\<rparr>\<lparr>bf\<rparr> :
      cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> a\<lparr>ObjMap\<rparr>\<lparr>bf\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>bf\<rparr>"
      if "bf \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>" for bf
    proof-
      from that assms(3) obtain b f 
        where bf_def: "bf = [0, b, f]\<^sub>\<circ>"
          and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
          and f: "f : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by auto
      from \<upsilon>.ntcf_NTMap_is_arr[OF b] a b assms(3) f have "\<upsilon>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> :
        Hom \<CC> c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<AA> a (\<TT>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
        by
          (
            cs_prems 
              cs_simp: cat_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros cat_op_intros
          )
      with that b f show "L_10_5_\<tau> \<TT> \<KK> c \<upsilon>' a\<lparr>NTMap\<rparr>\<lparr>bf\<rparr> :
        cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> a\<lparr>ObjMap\<rparr>\<lparr>bf\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>bf\<rparr>"
        unfolding bf_def \<upsilon>'_def
        by
          (
            cs_concl
              cs_simp:
                cat_cs_simps 
                cat_Kan_cs_simps 
                cat_comma_cs_simps
                cat_FUNCT_cs_simps
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
    qed

    show 
      "L_10_5_\<tau> \<TT> \<KK> c \<upsilon>' a\<lparr>NTMap\<rparr>\<lparr>B\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> a\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> =
        (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> L_10_5_\<tau> \<TT> \<KK> c \<upsilon>' a\<lparr>NTMap\<rparr>\<lparr>A\<rparr>"
      if "F : A \<mapsto>\<^bsub>c \<down>\<^sub>C\<^sub>F \<KK>\<^esub> B" for A B F
    proof-
      from \<KK>.is_functor_axioms that assms(3) obtain a' f a'' f' g 
        where F_def: "F = [[0, a', f]\<^sub>\<circ>, [0, a'', f']\<^sub>\<circ>, [0, g]\<^sub>\<circ>]\<^sub>\<circ>"
          and A_def: "A = [0, a', f]\<^sub>\<circ>"
          and B_def: "B = [0, a'', f']\<^sub>\<circ>"
          and g: "g : a' \<mapsto>\<^bsub>\<BB>\<^esub> a''"
          and f: "f : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>"
          and f': "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>a''\<rparr>" 
          and f'_def: "\<KK>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = f'" 
        by auto
      from \<upsilon>.ntcf_Comp_commute[OF g] have 
        "(\<upsilon>\<lparr>NTMap\<rparr>\<lparr>a''\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> (?H_\<CC> c \<circ>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>)\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> =
          ((?H_\<AA> a \<circ>\<^sub>C\<^sub>F \<TT>)\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> \<upsilon>\<lparr>NTMap\<rparr>\<lparr>a'\<rparr>)\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
        by simp
      from this a g f f' \<KK>.HomCod.category_axioms \<TT>.HomCod.category_axioms 
      have [cat_cs_simps]:
        "\<upsilon>\<lparr>NTMap\<rparr>\<lparr>a''\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<KK>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr> = 
          \<TT>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<upsilon>\<lparr>NTMap\<rparr>\<lparr>a'\<rparr>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
        by (*slow*)
          (
            cs_prems
              cs_simp: cat_cs_simps cat_op_simps
              cs_intro: cat_cs_intros cat_prod_cs_intros cat_op_intros
          )
      from that a g f f' \<KK>.HomCod.category_axioms \<TT>.HomCod.category_axioms 
      show ?thesis
        unfolding F_def A_def B_def \<upsilon>'_def (*slow*)
        by
          (
            cs_concl
              cs_simp:
                f'_def[symmetric] 
                cat_cs_simps 
                cat_Kan_cs_simps 
                cat_comma_cs_simps 
                cat_FUNCT_cs_simps
                cat_op_simps 
              cs_intro: cat_cs_intros cat_op_intros
          )
    qed

  qed
    (
      use assms in
        \<open>
          cs_concl
            cs_simp: cat_cs_simps cat_Kan_cs_simps 
            cs_intro: cat_small_cs_intros cat_cs_intros cat_Kan_cs_intros a
        \<close>
    )+

qed

lemma L_10_5_\<tau>_is_cat_cone'[cat_Kan_cs_intros]:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<upsilon>' = ntcf_arrow \<upsilon>"
    and "\<FF>' = \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>"
    and "c\<KK> = c \<down>\<^sub>C\<^sub>F \<KK>"
    and "\<AA>' = \<AA>"
    and "\<alpha>' = \<alpha>"
    and "\<upsilon> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT> :
      \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "L_10_5_\<tau> \<TT> \<KK> c \<upsilon>' a : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<FF>' : c\<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<AA>'"
  using assms(1-4,9,10) unfolding assms(5-8) by (rule L_10_5_\<tau>_is_cat_cone)



subsection\<open>Lemma X.5: \<open>L_10_5_\<upsilon>\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition L_10_5_\<upsilon> :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau> a =
    [
      (\<lambda>b\<in>\<^sub>\<circ>\<TT>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr>. L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau> a b),
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<KK>\<lparr>HomCod\<rparr>(c,-) \<circ>\<^sub>C\<^sub>F \<KK>,
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<TT>\<lparr>HomCod\<rparr>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>,
      \<TT>\<lparr>HomDom\<rparr>,
      cat_Set \<alpha>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma L_10_5_\<upsilon>_components: 
  shows "L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau> a\<lparr>NTMap\<rparr> =
    (\<lambda>b\<in>\<^sub>\<circ>\<TT>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr>. L_10_5_\<upsilon>_arrow \<TT> \<KK> c \<tau> a b)"
    and "L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau> a\<lparr>NTDom\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<KK>\<lparr>HomCod\<rparr>(c,-) \<circ>\<^sub>C\<^sub>F \<KK>"
    and "L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau> a\<lparr>NTCod\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<TT>\<lparr>HomCod\<rparr>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>"
    and "L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau> a\<lparr>NTDGDom\<rparr> = \<TT>\<lparr>HomDom\<rparr>"
    and "L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau> a\<lparr>NTDGCod\<rparr> = cat_Set \<alpha>"
  unfolding L_10_5_\<upsilon>_def nt_field_simps by (simp_all add: nat_omega_simps)

context
  fixes \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<TT>: "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)
interpretation \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule \<TT>)

lemmas L_10_5_\<upsilon>_components' = L_10_5_\<upsilon>_components[
  where \<TT>=\<TT> and \<KK>=\<KK>, unfolded cat_cs_simps
  ]

lemmas [cat_Kan_cs_simps] = L_10_5_\<upsilon>_components'(2-5)

end


subsubsection\<open>Natural transformation map\<close>

mk_VLambda L_10_5_\<upsilon>_components(1)
  |vsv L_10_5_\<upsilon>_NTMap_vsv[cat_Kan_cs_intros]|

context
  fixes \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<TT>: "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)
interpretation \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule \<TT>)

mk_VLambda L_10_5_\<upsilon>_components'(1)[OF \<KK> \<TT>]
  |vdomain L_10_5_\<upsilon>_NTMap_vdomain[cat_Kan_cs_simps]|
  |app L_10_5_\<upsilon>_NTMap_app[cat_Kan_cs_simps]|

end


subsubsection\<open>\<open>L_10_5_\<upsilon>\<close> is a natural transformation\<close>

lemma L_10_5_\<upsilon>_is_ntcf:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and \<tau>'_def: "\<tau>' = ntcf_arrow \<tau>"
    and \<tau>: "\<tau> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau>' a :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    (is \<open>?L_10_5_\<upsilon> : ?H_\<CC> c \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F ?H_\<AA> a \<circ>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>\<close>)
proof-

  interpret \<KK>: is_tm_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<TT>: is_tm_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))

  interpret \<tau>: is_cat_cone \<alpha> a \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<tau>  
    by (rule assms(5))

  from assms(3) interpret c\<KK>: tiny_category \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close>
    by (cs_concl cs_intro: cat_comma_cs_intros)
  from assms(3) interpret \<Pi>c: is_tm_functor \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<BB> \<open>c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close>
    by
      (
        cs_concl
          cs_simp: cat_comma_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_comma_cs_intros
      )

  show "?L_10_5_\<upsilon> : ?H_\<CC> c \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F ?H_\<AA> a \<circ>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  proof(intro is_ntcfI')
    show "vfsequence ?L_10_5_\<upsilon>" unfolding L_10_5_\<upsilon>_def by auto
    show "vcard ?L_10_5_\<upsilon> = 5\<^sub>\<nat>" 
      unfolding L_10_5_\<upsilon>_def by (simp add: nat_omega_simps)
    show "?L_10_5_\<upsilon>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> :
      (?H_\<CC> c \<circ>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> (?H_\<AA> a \<circ>\<^sub>C\<^sub>F \<TT>)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" for b
    proof-
      from a that assms(3) show ?thesis
        unfolding \<tau>'_def
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_Kan_cs_simps
              cs_intro:
                cat_Kan_cs_intros
                cat_lim_cs_intros
                cat_cs_intros
                cat_op_intros
          )
    qed
    show
      "?L_10_5_\<upsilon>\<lparr>NTMap\<rparr>\<lparr>b'\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> (?H_\<CC> c \<circ>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        (?H_\<AA> a \<circ>\<^sub>C\<^sub>F \<TT>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?L_10_5_\<upsilon>\<lparr>NTMap\<rparr>\<lparr>a'\<rparr>"
      if "f : a' \<mapsto>\<^bsub>\<BB>\<^esub> b'" for a' b' f
    proof-
      from that a assms(3) show ?thesis
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_Kan_cs_simps cat_op_simps \<tau>'_def
              cs_intro: cat_lim_cs_intros cat_cs_intros 
          )
    qed

  qed
    (
      use assms(3,6) in
        \<open>
          cs_concl
            cs_simp: cat_cs_simps cat_Kan_cs_simps
            cs_intro: cat_cs_intros cat_Kan_cs_intros
        \<close>
    )+

qed

lemma L_10_5_\<upsilon>_is_ntcf'[cat_Kan_cs_intros]:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<tau>' = ntcf_arrow \<tau>"
    and "\<FF>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<circ>\<^sub>C\<^sub>F \<KK>"
    and "\<GG>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>"
    and "\<BB>' = \<BB>"
    and "\<CC>' = cat_Set \<alpha>"
    and "\<alpha>' = \<alpha>"
    and "\<tau> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau>' a : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  using assms(1-4,10,11) unfolding assms(5-9) by (rule L_10_5_\<upsilon>_is_ntcf)



subsection\<open>Lemma X.5: \<open>L_10_5_\<chi>_arrow\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition L_10_5_\<chi>_arrow 
  where "L_10_5_\<chi>_arrow \<alpha> \<beta> \<TT> \<KK> c a =
    [
      (\<lambda>\<upsilon>\<in>\<^sub>\<circ>L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>. ntcf_arrow (L_10_5_\<tau> \<TT> \<KK> c \<upsilon> a)), 
      L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>,
      cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma L_10_5_\<chi>_arrow_components: 
  shows "L_10_5_\<chi>_arrow \<alpha> \<beta> \<TT> \<KK> c a\<lparr>ArrVal\<rparr> = 
      (\<lambda>\<upsilon>\<in>\<^sub>\<circ>L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>. ntcf_arrow (L_10_5_\<tau> \<TT> \<KK> c \<upsilon> a))"
    and "L_10_5_\<chi>_arrow \<alpha> \<beta> \<TT> \<KK> c a\<lparr>ArrDom\<rparr> = L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "L_10_5_\<chi>_arrow \<alpha> \<beta> \<TT> \<KK> c a\<lparr>ArrCod\<rparr> = 
      cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
  unfolding L_10_5_\<chi>_arrow_def arr_field_simps
  by (simp_all add: nat_omega_simps)

lemmas [cat_Kan_cs_simps] = L_10_5_\<chi>_arrow_components(2,3)


subsubsection\<open>Arrow value\<close>

mk_VLambda L_10_5_\<chi>_arrow_components(1)
  |vsv L_10_5_\<chi>_arrow_vsv[cat_Kan_cs_intros]|
  |vdomain L_10_5_\<chi>_arrow_vdomain|
  |app L_10_5_\<chi>_arrow_app|

lemma L_10_5_\<chi>_arrow_vdomain'[cat_Kan_cs_simps]:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (L_10_5_\<chi>_arrow \<alpha> \<beta> \<TT> \<KK> c a\<lparr>ArrVal\<rparr>) = Hom 
    (cat_FUNCT \<alpha> \<BB> (cat_Set \<alpha>)) 
    (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<circ>\<^sub>C\<^sub>F \<KK>)) 
    (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>))"
  using assms
  by
    (
      cs_concl 
        cs_simp: cat_cs_simps cat_Kan_cs_simps L_10_5_\<chi>_arrow_vdomain 
        cs_intro: cat_cs_intros
    )

lemma L_10_5_\<chi>_arrow_app'[cat_Kan_cs_simps]:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and \<upsilon>'_def: "\<upsilon>' = ntcf_arrow \<upsilon>"
    and \<upsilon>: "\<upsilon> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows 
    "L_10_5_\<chi>_arrow \<alpha> \<beta> \<TT> \<KK> c a\<lparr>ArrVal\<rparr>\<lparr>\<upsilon>'\<rparr> =
      ntcf_arrow (L_10_5_\<tau> \<TT> \<KK> c \<upsilon>' a)"
  using assms
  by
    (
      cs_concl
        cs_simp: cat_cs_simps cat_Kan_cs_simps L_10_5_\<chi>_arrow_app 
        cs_intro: cat_cs_intros cat_FUNCT_cs_intros
    )

lemma \<upsilon>\<tau>a_def:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and \<upsilon>\<tau>a'_def: "\<upsilon>\<tau>a' = ntcf_arrow \<upsilon>\<tau>a"
    and \<upsilon>\<tau>a: "\<upsilon>\<tau>a :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT> :
      \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<upsilon>\<tau>a = L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c (ntcf_arrow (L_10_5_\<tau> \<TT> \<KK> c \<upsilon>\<tau>a' a)) a"
  (is \<open>\<upsilon>\<tau>a = ?L_10_5_\<upsilon> (ntcf_arrow ?L_10_5_\<tau>) a\<close>)
proof-

  interpret \<KK>: is_tm_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<TT>: is_tm_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))

  interpret \<upsilon>\<tau>a: is_ntcf 
    \<alpha> \<BB> \<open>cat_Set \<alpha>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<circ>\<^sub>C\<^sub>F \<KK>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>\<close> \<upsilon>\<tau>a
    by (rule \<upsilon>\<tau>a)

  show ?thesis
  proof(rule ntcf_eqI)
    show "\<upsilon>\<tau>a : 
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by (rule \<upsilon>\<tau>a)
    from assms(1-3) a show 
      "?L_10_5_\<upsilon> (ntcf_arrow ?L_10_5_\<tau>) a :
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>" 
      by
        (
          cs_concl
            cs_simp: cat_Kan_cs_simps \<upsilon>\<tau>a'_def
            cs_intro: cat_cs_intros cat_Kan_cs_intros
        )
    have dom_lhs: "\<D>\<^sub>\<circ> (\<upsilon>\<tau>a\<lparr>NTMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)
    have dom_rhs: "\<D>\<^sub>\<circ> (?L_10_5_\<upsilon> (ntcf_arrow (?L_10_5_\<tau>)) a\<lparr>NTMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros)
    show "\<upsilon>\<tau>a\<lparr>NTMap\<rparr> = ?L_10_5_\<upsilon> (ntcf_arrow ?L_10_5_\<tau>) a\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix b assume prems: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
      from prems assms(3) a have lhs: "\<upsilon>\<tau>a\<lparr>NTMap\<rparr>\<lparr>b\<rparr> :
        Hom \<CC> c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<AA> a (\<TT>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros
          )
      then have dom_lhs: "\<D>\<^sub>\<circ> (\<upsilon>\<tau>a\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<lparr>ArrVal\<rparr>) = Hom \<CC> c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
        by (cs_concl cs_simp: cat_cs_simps)
      from prems assms(3) a have rhs: 
        "L_10_5_\<upsilon>_arrow \<TT> \<KK> c (ntcf_arrow ?L_10_5_\<tau>) a b :
          Hom \<CC> c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<AA> a (\<TT>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
        unfolding \<upsilon>\<tau>a'_def
        by
          (
            cs_concl 
              cs_simp: cat_Kan_cs_simps 
              cs_intro: cat_small_cs_intros cat_Kan_cs_intros cat_cs_intros
          )

      then have dom_rhs: 
        "\<D>\<^sub>\<circ> (L_10_5_\<upsilon>_arrow \<TT> \<KK> c  (ntcf_arrow ?L_10_5_\<tau>) a b\<lparr>ArrVal\<rparr>) =
          Hom \<CC> c (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
        by (cs_concl cs_simp: cat_cs_simps)
      have [cat_cs_simps]:  
        "\<upsilon>\<tau>a\<lparr>NTMap\<rparr>\<lparr>b\<rparr> = L_10_5_\<upsilon>_arrow \<TT> \<KK> c (ntcf_arrow ?L_10_5_\<tau>) a b"
      proof(rule arr_Set_eqI)
        from lhs show arr_Set_lhs: "arr_Set \<alpha> (\<upsilon>\<tau>a\<lparr>NTMap\<rparr>\<lparr>b\<rparr>)"
          by (auto dest: cat_Set_is_arrD(1))
        from rhs show arr_Set_rhs: 
          "arr_Set \<alpha> (L_10_5_\<upsilon>_arrow \<TT> \<KK> c (ntcf_arrow (?L_10_5_\<tau>)) a b)"
          by (auto dest: cat_Set_is_arrD(1))
        show "\<upsilon>\<tau>a\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<lparr>ArrVal\<rparr> = 
          L_10_5_\<upsilon>_arrow \<TT> \<KK> c (ntcf_arrow ?L_10_5_\<tau>) a b\<lparr>ArrVal\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
          fix f assume "f : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
          with assms prems show 
            "\<upsilon>\<tau>a\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> =
              L_10_5_\<upsilon>_arrow \<TT> \<KK> c (ntcf_arrow ?L_10_5_\<tau>) a b\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
            unfolding \<upsilon>\<tau>a'_def
            by
              (
                cs_concl
                  cs_simp:
                    cat_Kan_cs_simps cat_FUNCT_cs_simps L_10_5_\<upsilon>_arrow_ArrVal_app 
                  cs_intro: cat_cs_intros cat_comma_cs_intros
              )
        qed (use arr_Set_lhs arr_Set_rhs in auto)
      qed (use lhs rhs in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

      from prems show 
        "\<upsilon>\<tau>a\<lparr>NTMap\<rparr>\<lparr>b\<rparr> = L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c (ntcf_arrow ?L_10_5_\<tau>) a\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
        by
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_Kan_cs_simps cs_intro: cat_cs_intros
          )

    qed (cs_concl cs_intro: cat_cs_intros cat_Kan_cs_intros V_cs_intros)+

  qed simp_all

qed



subsection\<open>Lemma X.5: \<open>L_10_5_\<chi>'_arrow\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition L_10_5_\<chi>'_arrow :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "L_10_5_\<chi>'_arrow \<alpha> \<beta> \<TT> \<KK> c a =
    [
      (
        \<lambda>\<tau>\<in>\<^sub>\<circ>cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>.
          ntcf_arrow (L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau> a)
      ),
      cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>,
      L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma L_10_5_\<chi>'_arrow_components:
  shows "L_10_5_\<chi>'_arrow \<alpha> \<beta> \<TT> \<KK> c a\<lparr>ArrVal\<rparr> =
    (
      \<lambda>\<tau>\<in>\<^sub>\<circ>cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>.
        ntcf_arrow (L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau> a)
    )"
    and [cat_Kan_cs_simps]: "L_10_5_\<chi>'_arrow \<alpha> \<beta> \<TT> \<KK> c a\<lparr>ArrDom\<rparr> =
      cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and [cat_Kan_cs_simps]: "L_10_5_\<chi>'_arrow \<alpha> \<beta> \<TT> \<KK> c a\<lparr>ArrCod\<rparr> =
       L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
  unfolding L_10_5_\<chi>'_arrow_def arr_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Arrow value\<close>

mk_VLambda L_10_5_\<chi>'_arrow_components(1)
  |vsv L_10_5_\<chi>'_arrow_ArrVal_vsv[cat_Kan_cs_intros]|
  |vdomain L_10_5_\<chi>'_arrow_ArrVal_vdomain|
  |app L_10_5_\<chi>'_arrow_ArrVal_app|

lemma L_10_5_\<chi>'_arrow_ArrVal_vdomain'[cat_Kan_cs_simps]:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and \<tau>: "\<tau> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (L_10_5_\<chi>'_arrow \<alpha> \<beta> \<TT> \<KK> c a\<lparr>ArrVal\<rparr>) = Hom
    (cat_Funct \<alpha> (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA>)
    (cf_map (cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> a)) 
    (cf_map (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>))"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<tau>: is_cat_cone \<alpha> a \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<tau>
    by (rule assms(3))
  from assms(2,4) show ?thesis
    by 
      (
        cs_concl 
          cs_simp: cat_Kan_cs_simps L_10_5_\<chi>'_arrow_ArrVal_vdomain 
          cs_intro: cat_cs_intros
      )
qed

lemma L_10_5_\<chi>'_arrow_ArrVal_app'[cat_cs_simps]:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and \<tau>'_def: "\<tau>' = ntcf_arrow \<tau>"
    and \<tau>: "\<tau> : a <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "L_10_5_\<chi>'_arrow \<alpha> \<beta> \<TT> \<KK> c a\<lparr>ArrVal\<rparr>\<lparr>\<tau>'\<rparr> =
    ntcf_arrow (L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau>' a)"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<tau>: is_cat_cone \<alpha> a \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<tau>
    by (rule assms(4))
  from assms(2,5) have "\<tau>' \<in>\<^sub>\<circ> cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    unfolding \<tau>'_def
    by
      (
        cs_concl
          cs_simp: cat_Kan_cs_simps cat_Funct_components(1)
          cs_intro: cat_small_cs_intros cat_FUNCT_cs_intros cat_cs_intros
      )
  then show
    "L_10_5_\<chi>'_arrow \<alpha> \<beta> \<TT> \<KK> c a\<lparr>ArrVal\<rparr>\<lparr>\<tau>'\<rparr> =
      ntcf_arrow (L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau>' a)"
    unfolding L_10_5_\<chi>'_arrow_components by auto
qed


subsubsection\<open>\<open>L_10_5_\<chi>'_arrow\<close> is an isomorphism in the category \<open>Set\<close>\<close>

lemma L_10_5_\<chi>'_arrow_is_arr_isomorphism: 
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "L_10_5_\<chi>'_arrow \<alpha> \<beta> \<TT> \<KK> c a :
    cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<beta>\<^esub>
    L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" (*FIXME: any reason not to evaluate ObjMap*)
    (
      is 
        \<open>
          ?L_10_5_\<chi>'_arrow :
            cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<beta>\<^esub> 
            ?L_10_5_N\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>
        \<close>
    )
proof-

  let ?FUNCT = \<open>\<lambda>\<AA>. cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)\<close>
  let ?c\<KK>_\<AA> = \<open>cat_Funct \<alpha> (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA>\<close>
  let ?H_\<CC> = \<open>\<lambda>c. Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-)\<close>
  let ?H_\<AA> = \<open>\<lambda>c. Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-)\<close>

  from assms(1,2) interpret \<beta>: \<Z> \<beta> by simp 

  interpret \<KK>: is_tm_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(3))
  interpret \<TT>: is_tm_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(4))

  from \<KK>.vempty_is_zet assms interpret c\<KK>: tiny_category \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close>
    by (cs_concl cs_intro: cat_comma_cs_intros)
  from assms(2,6) interpret c\<KK>_\<AA>: category \<alpha> ?c\<KK>_\<AA>
    by
      (
        cs_concl cs_intro:
          cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  from \<KK>.vempty_is_zet assms interpret \<Pi>c: 
    is_tm_functor \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<BB> \<open>c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close>
    by (cs_concl cs_intro: cat_comma_cs_intros)

  from assms(2) interpret FUNCT_\<AA>: tiny_category \<beta> \<open>?FUNCT \<AA>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  from assms(2) interpret FUNCT_\<BB>: tiny_category \<beta> \<open>?FUNCT \<BB>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  from assms(2) interpret FUNCT_\<CC>: tiny_category \<beta> \<open>?FUNCT \<CC>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  
  have \<TT>\<Pi>: "\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    by (cs_concl cs_intro: cat_small_cs_intros cat_cs_intros)

  from assms(5,6) have [cat_cs_simps]: 
    "cf_of_cf_map (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (cf_map (cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> a)) =
      cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> a"
    "cf_of_cf_map (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (cf_map (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)) = \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>"
    "cf_of_cf_map \<BB> (cat_Set \<alpha>) (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<circ>\<^sub>C\<^sub>F \<KK>)) = 
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<circ>\<^sub>C\<^sub>F \<KK>"
    "cf_of_cf_map \<BB> (cat_Set \<alpha>) (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>)) = 
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>"
    by (cs_concl cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)+

  note cf_Cone_ObjMap_app = is_tm_functor.cf_Cone_ObjMap_app[OF \<TT>\<Pi> assms(1,2,6)]

  show ?thesis
  proof
    (
      intro cat_Set_is_arr_isomorphismI cat_Set_is_arrI arr_SetI, 
      unfold L_10_5_\<chi>'_arrow_components(3) cf_Cone_ObjMap_app
    )
    show "vfsequence ?L_10_5_\<chi>'_arrow" 
      unfolding L_10_5_\<chi>'_arrow_def by auto
    show \<chi>'_arrow_ArrVal_vsv: "vsv (?L_10_5_\<chi>'_arrow\<lparr>ArrVal\<rparr>)" 
      unfolding L_10_5_\<chi>'_arrow_components by auto
    show "vcard ?L_10_5_\<chi>'_arrow = 3\<^sub>\<nat>"
      unfolding L_10_5_\<chi>'_arrow_def by (simp add: nat_omega_simps)
    show [cat_cs_simps]: 
      "\<D>\<^sub>\<circ> (?L_10_5_\<chi>'_arrow\<lparr>ArrVal\<rparr>) = ?L_10_5_\<chi>'_arrow\<lparr>ArrDom\<rparr>"
      unfolding L_10_5_\<chi>'_arrow_components by simp
    show vrange_\<chi>'_arrow_vsubset_N'': 
      "\<R>\<^sub>\<circ> (?L_10_5_\<chi>'_arrow\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> ?L_10_5_N\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      unfolding L_10_5_\<chi>'_arrow_components
    proof(rule vrange_VLambda_vsubset)
      fix \<tau> assume prems: "\<tau> \<in>\<^sub>\<circ> cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      from this assms c\<KK>_\<AA>.category_axioms have \<tau>_is_arr:
        "\<tau> : cf_map (cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> a) \<mapsto>\<^bsub>?c\<KK>_\<AA>\<^esub> cf_map (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)"
        by
          (
            cs_prems
              cs_simp: cat_cs_simps cat_Kan_cs_simps cat_Funct_components(1)
              cs_intro: cat_small_cs_intros
          )
      note \<tau> = cat_Funct_is_arrD(1,2)[OF \<tau>_is_arr, unfolded cat_cs_simps]
      have "cf_of_cf_map (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (cf_map (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)) = \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>"
        by (cs_concl cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)
      from prems assms \<tau>(1) show 
        "ntcf_arrow (L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau> a) \<in>\<^sub>\<circ> ?L_10_5_N\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by (subst \<tau>(2)) (*slow*)
          (
            cs_concl
              cs_simp: cat_cs_simps cat_Kan_cs_simps
              cs_intro: 
                is_cat_coneI cat_cs_intros cat_Kan_cs_intros cat_FUNCT_cs_intros
          )
    qed

    show "\<R>\<^sub>\<circ> (?L_10_5_\<chi>'_arrow\<lparr>ArrVal\<rparr>) = ?L_10_5_N\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    proof
      (
        intro vsubset_antisym[OF vrange_\<chi>'_arrow_vsubset_N''], 
        intro vsubsetI
      )

      fix \<upsilon>\<tau>a assume "\<upsilon>\<tau>a \<in>\<^sub>\<circ> ?L_10_5_N\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      from this assms have \<upsilon>\<tau>a:
        "\<upsilon>\<tau>a : cf_map (?H_\<CC> c \<circ>\<^sub>C\<^sub>F \<KK>) \<mapsto>\<^bsub>?FUNCT \<BB>\<^esub> cf_map (?H_\<AA> a \<circ>\<^sub>C\<^sub>F \<TT>)"
        by 
          (
            cs_prems 
              cs_simp: cat_cs_simps cat_Kan_cs_simps cs_intro: cat_cs_intros
          )
      note \<upsilon>\<tau>a = cat_FUNCT_is_arrD[OF this, unfolded cat_cs_simps]
      interpret \<tau>: 
        is_cat_cone \<alpha> a \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>L_10_5_\<tau> \<TT> \<KK> c \<upsilon>\<tau>a a\<close>
        by (rule L_10_5_\<tau>_is_cat_cone[OF assms(3,4,5) \<upsilon>\<tau>a(2,1) assms(6)])

      show "\<upsilon>\<tau>a \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (?L_10_5_\<chi>'_arrow\<lparr>ArrVal\<rparr>)"
      proof(rule vsv.vsv_vimageI2')
        show "vsv (?L_10_5_\<chi>'_arrow\<lparr>ArrVal\<rparr>)" by (rule \<chi>'_arrow_ArrVal_vsv)
        from \<tau>.is_cat_cone_axioms assms show
          "ntcf_arrow (L_10_5_\<tau> \<TT> \<KK> c \<upsilon>\<tau>a a) \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (?L_10_5_\<chi>'_arrow\<lparr>ArrVal\<rparr>)"
          by
            (
              cs_concl
                cs_simp: cat_Kan_cs_simps 
                cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
            )
        from assms \<upsilon>\<tau>a(1,2) show 
          "\<upsilon>\<tau>a = ?L_10_5_\<chi>'_arrow\<lparr>ArrVal\<rparr>\<lparr>ntcf_arrow (L_10_5_\<tau> \<TT> \<KK> c \<upsilon>\<tau>a a)\<rparr>"
          by 
            (
              subst \<upsilon>\<tau>a(2), 
              cs_concl_step \<upsilon>\<tau>a_def[OF assms(3,4,5) \<upsilon>\<tau>a(2,1) assms(6)]  
            )
            (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      qed
    qed

    from assms show "?L_10_5_\<chi>'_arrow\<lparr>ArrDom\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
      by (intro Vset_trans[OF _ Vset_in_mono[OF assms(2)]])
        (
          cs_concl 
            cs_simp: cat_Kan_cs_simps cat_Funct_components(1) cf_Cone_ObjMap_app
            cs_intro: 
              cat_small_cs_intros
              cat_cs_intros
              cat_FUNCT_cs_intros 
              c\<KK>_\<AA>.cat_Hom_in_Vset
        )
    with assms(2) have "?L_10_5_\<chi>'_arrow\<lparr>ArrDom\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
      by (meson Vset_in_mono Vset_trans)
    from assms show "?L_10_5_N\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps cat_Kan_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros FUNCT_\<BB>.cat_Hom_in_Vset cat_FUNCT_cs_intros
        )
    show dom_\<chi>'_arrow: "\<D>\<^sub>\<circ> (?L_10_5_\<chi>'_arrow\<lparr>ArrVal\<rparr>) =
      Hom ?c\<KK>_\<AA> (cf_map (cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> a)) (cf_map (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>))"
      unfolding L_10_5_\<chi>'_arrow_components cf_Cone_ObjMap_app by simp
    show "?L_10_5_\<chi>'_arrow\<lparr>ArrDom\<rparr> = 
      Hom ?c\<KK>_\<AA> (cf_map (cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> a)) (cf_map (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>))"
      unfolding L_10_5_\<chi>'_arrow_components cf_Cone_ObjMap_app by simp
    show "v11 (?L_10_5_\<chi>'_arrow\<lparr>ArrVal\<rparr>)"
    proof(rule vsv.vsv_valeq_v11I, unfold dom_\<chi>'_arrow in_Hom_iff)
      fix \<tau>' \<tau>'' assume prems: 
        "\<tau>' : cf_map (cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> a) \<mapsto>\<^bsub>?c\<KK>_\<AA>\<^esub> cf_map (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)"
        "\<tau>'' : cf_map (cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> a) \<mapsto>\<^bsub>?c\<KK>_\<AA>\<^esub> cf_map (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)"
        "?L_10_5_\<chi>'_arrow\<lparr>ArrVal\<rparr>\<lparr>\<tau>'\<rparr> = ?L_10_5_\<chi>'_arrow\<lparr>ArrVal\<rparr>\<lparr>\<tau>''\<rparr>"
      note \<tau>' = cat_Funct_is_arrD[OF prems(1), unfolded cat_cs_simps]
        and \<tau>'' = cat_Funct_is_arrD[OF prems(2), unfolded cat_cs_simps]
      interpret \<tau>': is_cat_cone 
        \<alpha> a \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> \<tau>'\<close>
        by (rule is_cat_coneI[OF \<tau>'(1) assms(6)])
      interpret \<tau>'': is_cat_cone 
        \<alpha> a \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> \<tau>''\<close>
        by (rule is_cat_coneI[OF \<tau>''(1) assms(6)])
      have \<tau>'\<tau>': "ntcf_arrow (ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> \<tau>') = \<tau>'"
        by (subst (2) \<tau>'(2)) (cs_concl cs_simp: cat_FUNCT_cs_simps)
      have \<tau>''\<tau>'': "ntcf_arrow (ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> \<tau>'') = \<tau>''"
        by (subst (2) \<tau>''(2)) (cs_concl cs_simp: cat_FUNCT_cs_simps)
      from prems(3) \<tau>'(1) \<tau>''(1) assms have
        "L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau>' a = L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau>'' a"
        by (subst (asm) \<tau>'(2), use nothing in \<open>subst (asm) \<tau>''(2)\<close>) (*slow*)
          (
            cs_prems 
              cs_simp: \<tau>'\<tau>' \<tau>''\<tau>'' cat_cs_simps cat_FUNCT_cs_simps 
              cs_intro: cat_lim_cs_intros cat_Kan_cs_intros cat_cs_intros
          )
      from this have \<upsilon>\<tau>'a_\<upsilon>\<tau>''a: 
        "L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau>' a\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> =
          L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c \<tau>'' a\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>" 
        if "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "f : c \<mapsto>\<^bsub>\<CC>\<^esub> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)" for b f
        by simp
      have [cat_cs_simps]: "\<tau>'\<lparr>NTMap\<rparr>\<lparr>0, b, f\<rparr>\<^sub>\<bullet> = \<tau>''\<lparr>NTMap\<rparr>\<lparr>0, b, f\<rparr>\<^sub>\<bullet>"
        if "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "f : c \<mapsto>\<^bsub>\<CC>\<^esub> (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)" for b f
        using \<upsilon>\<tau>'a_\<upsilon>\<tau>''a[OF that] that
        by
          (
            cs_prems
              cs_simp: cat_Kan_cs_simps L_10_5_\<upsilon>_arrow_ArrVal_app
              cs_intro: cat_cs_intros 
          )
      have
        "ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> \<tau>' =
          ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> \<tau>''"
      proof(rule ntcf_eqI)
        show "ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> \<tau>' :
          cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> a \<mapsto>\<^sub>C\<^sub>F \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
          by (rule \<tau>'.is_ntcf_axioms)
        then have dom_lhs: 
          "\<D>\<^sub>\<circ> (ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> \<tau>'\<lparr>NTMap\<rparr>) = c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps)
        show "ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> \<tau>'' :
          cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> a \<mapsto>\<^sub>C\<^sub>F \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
          by (rule \<tau>''.is_ntcf_axioms)
        then have dom_rhs: 
          "\<D>\<^sub>\<circ> (ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> \<tau>''\<lparr>NTMap\<rparr>) = c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps)
        show
          "ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> \<tau>'\<lparr>NTMap\<rparr> =
            ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> \<tau>''\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          fix A assume "A \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
          with assms(5) obtain b f 
            where A_def: "A = [0, b, f]\<^sub>\<circ>"
              and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
              and f: "f : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
            by auto
          from b f show 
            "ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> \<tau>'\<lparr>NTMap\<rparr>\<lparr>A\<rparr> =
              ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> \<tau>''\<lparr>NTMap\<rparr>\<lparr>A\<rparr>"
            unfolding A_def 
            by (cs_concl cs_simp: cat_cs_simps cat_FUNCT_cs_simps)
        qed (cs_concl cs_intro: V_cs_intros)+
      qed simp_all
      then show "\<tau>' = \<tau>''"
      proof(rule inj_onD[OF bij_betw_imp_inj_on[OF bij_betw_ntcf_of_ntcf_arrow]])
        show "\<tau>' \<in>\<^sub>\<circ> ntcf_arrows \<alpha> (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA>"
          by (subst \<tau>'(2))
            (
              cs_concl cs_intro:
                cat_lim_cs_intros cat_cs_intros cat_FUNCT_cs_intros
            )
        show "\<tau>'' \<in>\<^sub>\<circ> ntcf_arrows \<alpha> (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA>"
          by (subst \<tau>''(2))
            (
              cs_concl cs_intro: 
                cat_lim_cs_intros cat_cs_intros cat_FUNCT_cs_intros
            )
      qed
    qed (cs_concl cs_intro: cat_Kan_cs_intros)

  qed auto

qed

lemma L_10_5_\<chi>'_arrow_is_arr_isomorphism'[cat_Kan_cs_intros]: 
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "A = cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "B = L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "\<CC>' = cat_Set \<beta>"
  shows "L_10_5_\<chi>'_arrow \<alpha> \<beta> \<TT> \<KK> c a : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> B"
  using assms(1-6)
  unfolding assms(7-9) 
  by (rule L_10_5_\<chi>'_arrow_is_arr_isomorphism)

lemma L_10_5_\<chi>'_arrow_is_arr: 
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "L_10_5_\<chi>'_arrow \<alpha> \<beta> \<TT> \<KK> c a :
      cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_Set \<beta>\<^esub>
      L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    by 
      (
        rule cat_Set_is_arr_isomorphismD(1)[
          OF L_10_5_\<chi>'_arrow_is_arr_isomorphism[OF assms(1-6)]
          ]
      )

lemma L_10_5_\<chi>'_arrow_is_arr'[cat_Kan_cs_intros]: 
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "A = cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "B = L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "\<CC>' = cat_Set \<beta>"
  shows "L_10_5_\<chi>'_arrow \<alpha> \<beta> \<TT> \<KK> c a : A \<mapsto>\<^bsub>\<CC>'\<^esub> B"
  using assms(1-6) unfolding assms(7-9) by (rule L_10_5_\<chi>'_arrow_is_arr)



subsection\<open>Lemma X.5: \<open>L_10_5_\<chi>\<close>\label{sec:lem_X_5_end}\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition L_10_5_\<chi> :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "L_10_5_\<chi> \<alpha> \<beta> \<TT> \<KK> c =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<TT>\<lparr>HomCod\<rparr>\<lparr>Obj\<rparr>. L_10_5_\<chi>'_arrow \<alpha> \<beta> \<TT> \<KK> c a),
      cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>),
      L_10_5_N \<alpha> \<beta> \<TT> \<KK> c,
      op_cat (\<TT>\<lparr>HomCod\<rparr>),
      cat_Set \<beta>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma L_10_5_\<chi>_components: 
  shows "L_10_5_\<chi> \<alpha> \<beta> \<TT> \<KK> c\<lparr>NTMap\<rparr> = 
    (\<lambda>a\<in>\<^sub>\<circ>\<TT>\<lparr>HomCod\<rparr>\<lparr>Obj\<rparr>. L_10_5_\<chi>'_arrow \<alpha> \<beta> \<TT> \<KK> c a)"
    and [cat_Kan_cs_simps]: 
      "L_10_5_\<chi> \<alpha> \<beta> \<TT> \<KK> c\<lparr>NTDom\<rparr> = cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)"
    and [cat_Kan_cs_simps]: 
      "L_10_5_\<chi> \<alpha> \<beta> \<TT> \<KK> c\<lparr>NTCod\<rparr> = L_10_5_N \<alpha> \<beta> \<TT> \<KK> c"
    and "L_10_5_\<chi> \<alpha> \<beta> \<TT> \<KK> c\<lparr>NTDGDom\<rparr> = op_cat (\<TT>\<lparr>HomCod\<rparr>)"
    and [cat_Kan_cs_simps]: "L_10_5_\<chi> \<alpha> \<beta> \<TT> \<KK> c\<lparr>NTDGCod\<rparr> = cat_Set \<beta>"
  unfolding L_10_5_\<chi>_def nt_field_simps by (simp_all add: nat_omega_simps)

context
  fixes \<alpha> \<AA> \<BB> \<TT>
  assumes \<TT>: "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

interpretation is_functor \<alpha> \<BB> \<AA> \<TT> by (rule \<TT>)

lemmas L_10_5_\<chi>_components' =
  L_10_5_\<chi>_components[where \<TT>=\<TT>, unfolded cat_cs_simps]

lemmas [cat_Kan_cs_simps] = L_10_5_\<chi>_components'(4)

end


subsubsection\<open>Natural transformation map\<close>

mk_VLambda L_10_5_\<chi>_components(1)
  |vsv L_10_5_\<chi>_NTMap_vsv[cat_Kan_cs_intros]|

context
  fixes \<alpha> \<AA> \<BB> \<TT>
  assumes \<TT>: "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

interpretation is_functor \<alpha> \<BB> \<AA> \<TT> by (rule \<TT>)

mk_VLambda L_10_5_\<chi>_components(1)[where \<TT>=\<TT>, unfolded cat_cs_simps]
  |vdomain L_10_5_\<chi>_NTMap_vdomain[cat_Kan_cs_simps]|
  |app L_10_5_\<chi>_NTMap_app[cat_Kan_cs_simps]|

end


subsubsection\<open>\<open>L_10_5_\<chi>\<close> is a natural isomorphism\<close>

lemma L_10_5_\<chi>_is_iso_ntcf:
  \<comment>\<open>See lemma on page 245 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "L_10_5_\<chi> \<alpha> \<beta> \<TT> \<KK> c :
    cf_Cone \<alpha> \<beta> (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o L_10_5_N \<alpha> \<beta> \<TT> \<KK> c :
    op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
    (is \<open>?L_10_5_\<chi> : ?cf_Cone \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o ?L_10_5_N : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>\<close>)
proof-

  let ?FUNCT = \<open>\<lambda>\<AA>. cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)\<close>
  let ?c\<KK>_\<AA> = \<open>cat_Funct \<alpha> (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA>\<close>
  let ?ntcf_c\<KK>_\<AA> = \<open>ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA>\<close>
  let ?\<TT>_c\<KK> = \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close>
  let ?H_\<CC> = \<open>\<lambda>c. Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-)\<close>
  let ?H_\<AA> = \<open>\<lambda>a. Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-)\<close>
  let ?L_10_5_\<chi>'_arrow = \<open>L_10_5_\<chi>'_arrow \<alpha> \<beta> \<TT> \<KK> c\<close>
  let ?cf_c\<KK>_\<AA> = \<open>cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA>\<close>
  let ?L_10_5_\<upsilon> = \<open>L_10_5_\<upsilon> \<alpha> \<TT> \<KK> c\<close>
  let ?L_10_5_\<upsilon>_arrow = \<open>L_10_5_\<upsilon>_arrow \<TT> \<KK> c\<close>

  interpret \<beta>: \<Z> \<beta> by (rule assms(1))

  interpret \<KK>: is_tm_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(3))
  interpret \<TT>: is_tm_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(4))

  from \<KK>.vempty_is_zet assms(5) interpret c\<KK>: tiny_category \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close>
    by (cs_concl cs_intro: cat_comma_cs_intros)
  from assms(2,5) interpret c\<KK>_\<AA>: category \<alpha> ?c\<KK>_\<AA>
    by
      (
        cs_concl cs_intro:
          cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  interpret \<beta>_c\<KK>_\<AA>: category \<beta> ?c\<KK>_\<AA>
    by (rule c\<KK>_\<AA>.cat_category_if_ge_Limit)
      (cs_concl cs_intro: cat_cs_intros assms(2))+
  from assms(2,5) interpret \<Delta>: is_functor \<alpha> \<AA> ?c\<KK>_\<AA> \<open>\<Delta>\<^sub>C \<alpha> (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA>\<close>
    by
      (
        cs_concl cs_intro: 
          cat_small_cs_intros cat_cs_intros cat_op_intros
      )+
  from \<Delta>.is_functor_axioms assms(2) interpret \<beta>\<Delta>: 
    is_functor \<beta> \<AA> ?c\<KK>_\<AA> \<open>\<Delta>\<^sub>C \<alpha> (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA>\<close>
    by (cs_intro_step is_functor.cf_is_functor_if_ge_Limit)
      (cs_concl cs_intro: cat_cs_intros)+
  from \<KK>.vempty_is_zet assms(5) interpret \<Pi>c: 
    is_tm_functor \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<BB> \<open>c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close>
    by
      (
        cs_concl
          cs_simp: cat_comma_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_comma_cs_intros
      )
  interpret \<beta>\<Pi>c: is_tiny_functor \<beta> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<BB> \<open>c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close>
    by (rule \<Pi>c.cf_is_tiny_functor_if_ge_Limit[OF assms(1,2)])
  
  interpret E: is_functor \<beta> \<open>?FUNCT \<CC> \<times>\<^sub>C \<CC>\<close> \<open>cat_Set \<beta>\<close> \<open>cf_eval \<alpha> \<beta> \<CC>\<close>
    by (rule \<KK>.HomCod.cat_cf_eval_is_functor[OF assms(1,2)])

  from assms(2) interpret FUNCT_\<AA>: tiny_category \<beta> \<open>?FUNCT \<AA>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  from assms(2) interpret FUNCT_\<BB>: tiny_category \<beta> \<open>?FUNCT \<BB>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  from assms(2) interpret FUNCT_\<CC>: tiny_category \<beta> \<open>?FUNCT \<CC>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  
  interpret \<beta>\<AA>: tiny_category \<beta> \<AA>
    by (rule category.cat_tiny_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_simp: cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<BB>: tiny_category \<beta> \<BB>
    by (rule category.cat_tiny_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_simp: cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<CC>: tiny_category \<beta> \<CC>
    by (rule category.cat_tiny_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_simp: cs_intro: cat_cs_intros\<close>)+

  interpret \<beta>\<KK>: is_tiny_functor \<beta> \<BB> \<CC> \<KK>
    by (rule is_functor.cf_is_tiny_functor_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_simp: cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<TT>: is_tiny_functor \<beta> \<BB> \<AA> \<TT>
    by (rule is_functor.cf_is_tiny_functor_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_simp: cs_intro: cat_cs_intros\<close>)+

  interpret cat_Set_\<alpha>\<beta>: subcategory \<beta> \<open>cat_Set \<alpha>\<close> \<open>cat_Set \<beta>\<close>
    by (rule \<KK>.subcategory_cat_Set_cat_Set[OF assms(1,2)])
  
  show ?thesis
  proof(intro is_iso_ntcfI is_ntcfI', unfold cat_op_simps)

    show "vfsequence (?L_10_5_\<chi>)" unfolding L_10_5_\<chi>_def by auto
    show "vcard (?L_10_5_\<chi>) = 5\<^sub>\<nat>" 
      unfolding L_10_5_\<chi>_def by (simp add: nat_omega_simps)
    from assms(2) show "?cf_Cone : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>" 
      by (intro is_tm_functor.tm_cf_cf_Cone_is_functor_if_ge_Limit)
        (cs_concl cs_intro: cat_small_cs_intros cat_cs_intros)+

    from assms show "?L_10_5_N : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>" 
      by (cs_concl cs_intro: cat_Kan_cs_intros)
    show "?L_10_5_\<chi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : 
      ?cf_Cone\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<beta>\<^esub> ?L_10_5_N\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a 
      using assms(2,3,4,5) that
      by
        (
          cs_concl 
            cs_simp: L_10_5_\<chi>_NTMap_app 
            cs_intro: cat_cs_intros L_10_5_\<chi>'_arrow_is_arr_isomorphism
         )
    from cat_Set_is_arr_isomorphismD[OF this] show 
      "?L_10_5_\<chi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : ?cf_Cone\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> ?L_10_5_N\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
      using that by auto

    have [cat_cs_simps]:
      "?L_10_5_\<chi>'_arrow b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub>
        cf_hom ?c\<KK>_\<AA> [ntcf_arrow (?ntcf_c\<KK>_\<AA> f), ntcf_arrow (ntcf_id ?\<TT>_c\<KK>)]\<^sub>\<circ> =
        cf_hom (?FUNCT \<BB>)
          [
            ntcf_arrow (ntcf_id (?H_\<CC> c \<circ>\<^sub>C\<^sub>F \<KK>)),
            ntcf_arrow (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(f,-) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<TT>)
          ]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?L_10_5_\<chi>'_arrow a"
      (
        is 
          "?L_10_5_\<chi>'_arrow b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?cf_hom_lhs =
            ?cf_hom_rhs \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?L_10_5_\<chi>'_arrow a"
      )
      if "f : b \<mapsto>\<^bsub>\<AA>\<^esub> a" for a b f
    proof-
      let ?H_f = \<open>Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(f,-)\<close>
      from that assms \<beta>_c\<KK>_\<AA>.category_axioms c\<KK>_\<AA>.category_axioms have lhs:
        "?L_10_5_\<chi>'_arrow b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?cf_hom_lhs :
          Hom ?c\<KK>_\<AA> (cf_map (?cf_c\<KK>_\<AA> a)) (cf_map ?\<TT>_c\<KK>) \<mapsto>\<^bsub>cat_Set \<beta>\<^esub>
          ?L_10_5_N\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by (*slow*)
          (
            cs_concl
              cs_simp:
                cat_Kan_cs_simps
                cat_cs_simps
                cat_FUNCT_cs_simps
                cat_Funct_components(1)
                cat_op_simps
              cs_intro:
                cat_Kan_cs_intros
                cat_small_cs_intros
                cat_FUNCT_cs_intros
                cat_cs_intros
                cat_prod_cs_intros
                cat_op_intros
          )
      then have dom_lhs:
        "\<D>\<^sub>\<circ> ((?L_10_5_\<chi>'_arrow b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?cf_hom_lhs)\<lparr>ArrVal\<rparr>) =
          Hom ?c\<KK>_\<AA> (cf_map (?cf_c\<KK>_\<AA> a)) (cf_map ?\<TT>_c\<KK>)"
        by (cs_concl cs_simp: cat_cs_simps)
      from that assms \<beta>_c\<KK>_\<AA>.category_axioms c\<KK>_\<AA>.category_axioms have rhs:
        "?cf_hom_rhs \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?L_10_5_\<chi>'_arrow a :
          Hom ?c\<KK>_\<AA> (cf_map (?cf_c\<KK>_\<AA> a)) (cf_map ?\<TT>_c\<KK>) \<mapsto>\<^bsub>cat_Set \<beta>\<^esub>
          ?L_10_5_N\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by (*slow*)
          (
            cs_concl
              cs_simp: 
                cat_Kan_cs_simps 
                cat_cs_simps
                cat_Funct_components(1)
                cat_op_simps
              cs_intro:
                cat_Kan_cs_intros
                cat_small_cs_intros
                cat_cs_intros
                cat_prod_cs_intros
                cat_FUNCT_cs_intros
                cat_op_intros
          )
      then have dom_rhs:
        "\<D>\<^sub>\<circ> ((?cf_hom_rhs \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?L_10_5_\<chi>'_arrow a)\<lparr>ArrVal\<rparr>) =
          Hom ?c\<KK>_\<AA> (cf_map (?cf_c\<KK>_\<AA> a)) (cf_map ?\<TT>_c\<KK>)"
        by (cs_concl cs_simp: cat_cs_simps)

      show ?thesis
      proof(rule arr_Set_eqI)
        from lhs show arr_Set_lhs: 
          "arr_Set \<beta> (?L_10_5_\<chi>'_arrow b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?cf_hom_lhs)"
          by (auto dest: cat_Set_is_arrD(1))
        from rhs show arr_Set_rhs:
          "arr_Set \<beta> (?cf_hom_rhs \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?L_10_5_\<chi>'_arrow a)"
          by (auto dest: cat_Set_is_arrD(1))
        show 
          "(?L_10_5_\<chi>'_arrow b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?cf_hom_lhs)\<lparr>ArrVal\<rparr> =
            (?cf_hom_rhs \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?L_10_5_\<chi>'_arrow a)\<lparr>ArrVal\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
          fix F assume prems: "F : cf_map (?cf_c\<KK>_\<AA> a) \<mapsto>\<^bsub>?c\<KK>_\<AA>\<^esub> cf_map ?\<TT>_c\<KK>"
          let ?F = \<open>ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> F\<close>
          from that have [cat_cs_simps]:
            "cf_of_cf_map (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (cf_map (?cf_c\<KK>_\<AA> a)) = ?cf_c\<KK>_\<AA> a"
            "cf_of_cf_map (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (cf_map (?\<TT>_c\<KK>)) = ?\<TT>_c\<KK>"
            by (cs_concl cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)
          note F = cat_Funct_is_arrD[OF prems, unfolded cat_cs_simps]
          from that F(1) have F_const_is_cat_cone:
            "?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_c\<KK>_\<AA> f : b <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e ?\<TT>_c\<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
            by
              (
                cs_concl
                  cs_simp: cat_cs_simps
                  cs_intro: cat_small_cs_intros is_cat_coneI cat_cs_intros
              )
          have [cat_cs_simps]:
            "?L_10_5_\<upsilon> (ntcf_arrow (?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_c\<KK>_\<AA> f)) b =
              ?H_f \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?L_10_5_\<upsilon> (ntcf_arrow ?F) a"
          proof(rule ntcf_eqI)
            from assms that F(1) show
              "?L_10_5_\<upsilon> (ntcf_arrow (?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_c\<KK>_\<AA> f)) b :
                ?H_\<CC> c \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F ?H_\<AA> b \<circ>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
              by
                (
                  cs_concl cs_intro:
                    cat_small_cs_intros 
                    cat_Kan_cs_intros 
                    cat_cs_intros 
                    is_cat_coneI
                )
            then have dom_\<upsilon>: 
              "\<D>\<^sub>\<circ> (?L_10_5_\<upsilon> (ntcf_arrow (?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_c\<KK>_\<AA> f)) b\<lparr>NTMap\<rparr>) = 
                \<BB>\<lparr>Obj\<rparr>"
              by (cs_concl cs_simp: cat_cs_simps)
            from assms that F(1) show 
              "?H_f \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?L_10_5_\<upsilon> (ntcf_arrow ?F) a :
                ?H_\<CC> c \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F ?H_\<AA> b \<circ>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
              by
                (
                  cs_concl cs_intro:
                    cat_Kan_cs_intros cat_cs_intros is_cat_coneI
                )
            then have dom_f\<TT>\<upsilon>:
              "\<D>\<^sub>\<circ> ((?H_f \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?L_10_5_\<upsilon> (ntcf_arrow ?F) a)\<lparr>NTMap\<rparr>) =
                \<BB>\<lparr>Obj\<rparr>"
              by (cs_concl cs_simp: cat_cs_simps)
            show 
              "?L_10_5_\<upsilon> (ntcf_arrow (?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_c\<KK>_\<AA> f)) b\<lparr>NTMap\<rparr> =
                (?H_f \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?L_10_5_\<upsilon> (ntcf_arrow ?F) a)\<lparr>NTMap\<rparr>"
            proof(rule vsv_eqI, unfold dom_\<upsilon> dom_f\<TT>\<upsilon>)
              fix b' assume prems': "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
              let ?Y = \<open>Yoneda_component (?H_\<AA> b) a f (\<TT>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>)\<close>
              let ?\<KK>b' = \<open>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>\<close>
              let ?\<TT>b' = \<open>\<TT>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>\<close>
              have [cat_cs_simps]:
                "?L_10_5_\<upsilon>_arrow (ntcf_arrow (?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_c\<KK>_\<AA> f)) b b' =
                  ?Y \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?L_10_5_\<upsilon>_arrow (ntcf_arrow ?F) a b'"
                (is \<open>?\<upsilon>_Ffbb' = ?Y\<upsilon>\<close>)
              proof-
                from assms prems' F_const_is_cat_cone have \<upsilon>_Ffbb': 
                  "?\<upsilon>_Ffbb' : Hom \<CC> c ?\<KK>b' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<AA> b ?\<TT>b'"
                  by 
                    (
                      cs_concl cs_intro:
                        cat_cs_intros L_10_5_\<upsilon>_arrow_is_arr
                    )
                then have dom_\<upsilon>_Ffbb': "\<D>\<^sub>\<circ> (?\<upsilon>_Ffbb'\<lparr>ArrVal\<rparr>) = Hom \<CC> c (?\<KK>b')"
                  by (cs_concl cs_simp: cat_cs_simps)
                from assms that \<TT>.HomCod.category_axioms prems' F(1) have Y\<upsilon>:
                  "?Y\<upsilon> : Hom \<CC> c ?\<KK>b' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<AA> b ?\<TT>b'"
                  by
                    (
                      cs_concl
                        cs_simp: cat_Kan_cs_simps cat_cs_simps cat_op_simps
                        cs_intro: is_cat_coneI cat_Kan_cs_intros cat_cs_intros
                    )
                then have dom_Y\<upsilon>: "\<D>\<^sub>\<circ> (?Y\<upsilon>\<lparr>ArrVal\<rparr>) = Hom \<CC> c (?\<KK>b')"
                  by (cs_concl cs_simp: cat_cs_simps)
                show ?thesis
                proof(rule arr_Set_eqI)
                  from \<upsilon>_Ffbb' show arr_Set_\<upsilon>_Ffbb': "arr_Set \<alpha> ?\<upsilon>_Ffbb'"
                    by (auto dest: cat_Set_is_arrD(1))
                  from Y\<upsilon> show arr_Set_Y\<upsilon>: "arr_Set \<alpha> ?Y\<upsilon>"
                    by (auto dest: cat_Set_is_arrD(1))
                  show "?\<upsilon>_Ffbb'\<lparr>ArrVal\<rparr> = ?Y\<upsilon>\<lparr>ArrVal\<rparr>"
                  proof(rule vsv_eqI, unfold dom_\<upsilon>_Ffbb' dom_Y\<upsilon> in_Hom_iff)
                    fix g assume "g : c \<mapsto>\<^bsub>\<CC>\<^esub> ?\<KK>b'"
                    with 
                      assms(2-) 
                      \<KK>.is_functor_axioms 
                      \<TT>.is_functor_axioms 
                      \<TT>.HomCod.category_axioms 
                      \<KK>.HomCod.category_axioms 
                      that prems' F(1) 
                    show "?\<upsilon>_Ffbb'\<lparr>ArrVal\<rparr>\<lparr>g\<rparr> = ?Y\<upsilon>\<lparr>ArrVal\<rparr>\<lparr>g\<rparr>"
                      by (*slow*)
                        (
                          cs_concl
                            cs_simp:
                              cat_Kan_cs_simps
                              cat_cs_simps
                              L_10_5_\<upsilon>_arrow_ArrVal_app
                              cat_comma_cs_simps
                              cat_op_simps
                            cs_intro: 
                              cat_Kan_cs_intros 
                              is_cat_coneI 
                              cat_cs_intros 
                              cat_comma_cs_intros
                              cat_op_intros 
                            cs_simp: cat_FUNCT_cs_simps
                            cs_intro: cat_small_cs_intros
                        )
                  qed (use arr_Set_\<upsilon>_Ffbb' arr_Set_Y\<upsilon> in auto)
                qed (use \<upsilon>_Ffbb' Y\<upsilon> in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+
              qed

              from assms prems' that F(1) show
                "?L_10_5_\<upsilon> (ntcf_arrow (?F \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_c\<KK>_\<AA> f)) b\<lparr>NTMap\<rparr>\<lparr>b'\<rparr> =
                  (?H_f \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?L_10_5_\<upsilon> (ntcf_arrow ?F) a)\<lparr>NTMap\<rparr>\<lparr>b'\<rparr>"
                by
                  (
                    cs_concl
                      cs_simp: cat_Kan_cs_simps cat_cs_simps
                      cs_intro: is_cat_coneI cat_Kan_cs_intros cat_cs_intros
                  )

            qed (cs_concl cs_intro: cat_Kan_cs_intros cat_cs_intros)+

          qed simp_all

          from that F(1) interpret F: is_cat_cone \<alpha> a \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>?\<TT>_c\<KK>\<close> ?F
            by (cs_concl cs_intro: is_cat_coneI cat_cs_intros)
          from
            assms(2-) prems F(1) that
            \<TT>.HomCod.cat_ntcf_Hom_snd_is_ntcf[OF that] (*speedup*)
            \<beta>_c\<KK>_\<AA>.category_axioms (*speedup*)
          show 
            "(?L_10_5_\<chi>'_arrow b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?cf_hom_lhs)\<lparr>ArrVal\<rparr>\<lparr>F\<rparr> =
              (?cf_hom_rhs \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?L_10_5_\<chi>'_arrow a)\<lparr>ArrVal\<rparr>\<lparr>F\<rparr>"
            by (subst (1 2) F(2)) (*exceptionally slow*)
            (
              cs_concl
                cs_simp: 
                  cat_cs_simps 
                  cat_Kan_cs_simps
                  cat_FUNCT_cs_simps 
                  cat_Funct_components(1) 
                  cat_op_simps 
                cs_intro: 
                  cat_small_cs_intros 
                  is_cat_coneI 
                  cat_Kan_cs_intros
                  cat_cs_intros 
                  cat_prod_cs_intros 
                  cat_FUNCT_cs_intros 
                  cat_op_intros
            )
        qed (use arr_Set_lhs arr_Set_rhs in auto)

      qed (use lhs rhs in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

    qed

    show 
      "?L_10_5_\<chi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?cf_Cone\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        ?L_10_5_N\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?L_10_5_\<chi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      if "f : b \<mapsto>\<^bsub>\<AA>\<^esub> a" for a b f
      using that assms
      by
        (
          cs_concl
            cs_simp:
              cat_cs_simps
              cat_Kan_cs_simps
              cat_Funct_components(1)
              cat_FUNCT_cs_simps
              cat_op_simps
            cs_intro: 
              cat_small_cs_intros
              cat_Kan_cs_intros
              cat_cs_intros
              cat_FUNCT_cs_intros
              cat_op_intros
        )

  qed 
    (
      cs_concl
        cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros cat_Kan_cs_intros
    )+

qed



subsection\<open>
The limit of \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> exists for every 
pointwise right Kan extension of \<open>\<TT>\<close> along \<open>\<KK>\<close>
\<close>

lemma (in is_cat_pw_rKe) cat_pw_rKe_ex_cat_limit:
  \<comment>\<open>Based on the elements of Chapter X-5 in \cite{mac_lane_categories_2010}.
    The size conditions for the functors \<open>\<KK>\<close> and \<open>\<TT>\<close> are related to the
    choice of the definition of the limit in this work (by definition,
    all limits are small).\<close>
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  obtains UA 
    where "UA : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def AG.\<Z>_Limit_\<alpha>\<omega> AG.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def AG.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  let ?FUNCT = \<open>\<lambda>\<AA>. cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)\<close>
  let ?H_A = \<open>\<lambda>f. Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(f,-)\<close>
  let ?H_A\<GG> = \<open>\<lambda>f. ?H_A f \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>\<close>
  let ?H_\<AA> = \<open>\<lambda>a. Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-)\<close>
  let ?H_\<AA>\<TT> = \<open>\<lambda>a. ?H_\<AA> a \<circ>\<^sub>C\<^sub>F \<TT>\<close>
  let ?H_\<AA>\<GG> = \<open>\<lambda>a. ?H_\<AA> a \<circ>\<^sub>C\<^sub>F \<GG>\<close>
  let ?H_\<CC> = \<open>\<lambda>c. Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-)\<close>
  let ?H_\<CC>\<KK> = \<open>\<lambda>c. ?H_\<CC> c \<circ>\<^sub>C\<^sub>F \<KK>\<close>
  let ?H_\<AA>\<epsilon> = \<open>\<lambda>b. ?H_\<AA> b \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon>\<close>
  let ?SET_\<KK> = \<open>exp_cat_cf \<alpha> (cat_Set \<alpha>) \<KK>\<close>
  let ?H_FUNCT = \<open>\<lambda>\<CC> \<FF>. Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>?FUNCT \<CC>(-,cf_map \<FF>)\<close>
  let ?ua_NTDGDom = \<open>op_cat (?FUNCT \<CC>)\<close>
  let ?ua_NTDom = \<open>\<lambda>a. ?H_FUNCT \<CC> (?H_\<AA>\<GG> a)\<close>
  let ?ua_NTCod = \<open>\<lambda>a. ?H_FUNCT \<BB> (?H_\<AA>\<TT> a) \<circ>\<^sub>C\<^sub>F op_cf ?SET_\<KK>\<close>
  let ?c\<KK>_\<AA> = \<open>cat_Funct \<alpha> (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA>\<close>
  let ?ua = 
    \<open>
      \<lambda>a. ntcf_ua_fo
        \<beta>
        ?SET_\<KK>
        (cf_map (?H_\<AA>\<TT> a))
        (cf_map (?H_\<AA>\<GG> a))
        (ntcf_arrow (?H_\<AA>\<epsilon> a))
    \<close>
  let ?cf_nt = \<open>cf_nt \<alpha> \<beta> (cf_id \<CC>)\<close>
  let ?cf_eval = \<open>cf_eval \<alpha> \<beta> \<CC>\<close>
  let ?\<TT>_c\<KK> = \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close>
  let ?cf_c\<KK>_\<AA> = \<open>cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA>\<close>
  let ?\<GG>c = \<open>\<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<close>
  let ?\<Delta> = \<open>\<Delta>\<^sub>C \<alpha> (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA>\<close>
  let ?ntcf_ua_fo = 
    \<open>
      \<lambda>a. ntcf_ua_fo
        \<beta> 
        ?SET_\<KK> 
        (cf_map (?H_\<AA>\<TT> a)) 
        (cf_map (?H_\<AA>\<GG> a)) 
        (ntcf_arrow (?H_\<AA>\<epsilon> a))
    \<close>
  let ?umap_fo =
    \<open>
      \<lambda>b. umap_fo
        ?SET_\<KK>
        (cf_map (?H_\<AA>\<TT> b))
        (cf_map (?H_\<AA>\<GG> b))
        (ntcf_arrow (?H_\<AA>\<epsilon> b))
        (cf_map (?H_\<CC> c))
    \<close>

  interpret \<KK>: is_tm_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<TT>: is_tm_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))

  from AG.vempty_is_zet assms(3) interpret c\<KK>: tiny_category \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close>
    by (cs_concl cs_intro: cat_comma_cs_intros)
  from \<alpha>\<beta> assms(3) interpret c\<KK>_\<AA>: category \<alpha> ?c\<KK>_\<AA>
    by
      (
        cs_concl cs_intro:
          cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  interpret \<beta>_c\<KK>_\<AA>: category \<beta> ?c\<KK>_\<AA>
    by (rule c\<KK>_\<AA>.cat_category_if_ge_Limit)
      (cs_concl cs_intro: cat_cs_intros \<alpha>\<beta>)+
  from \<alpha>\<beta> assms(3) interpret \<Delta>: is_functor \<alpha> \<AA> ?c\<KK>_\<AA> ?\<Delta>
    by
      (
        cs_concl cs_intro: 
          cat_small_cs_intros cat_cs_intros cat_op_intros
      )+
  from \<Delta>.is_functor_axioms \<alpha>\<beta> interpret \<beta>\<Delta>: 
    is_functor \<beta> \<AA> \<open>?c\<KK>_\<AA>\<close> \<open>?\<Delta>\<close>
    by (cs_intro_step is_functor.cf_is_functor_if_ge_Limit)
      (cs_concl cs_intro: cat_cs_intros)+
  from AG.vempty_is_zet assms(3) interpret \<Pi>c: 
    is_tm_functor \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<BB> \<open>c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close>
    by
      (
        cs_concl
          cs_simp: cat_comma_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_comma_cs_intros
      )
  interpret \<beta>\<Pi>c: is_tiny_functor \<beta> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<BB> \<open>c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close>
    by (rule \<Pi>c.cf_is_tiny_functor_if_ge_Limit[OF \<beta> \<alpha>\<beta>])
  
  interpret E: is_functor \<beta> \<open>?FUNCT \<CC> \<times>\<^sub>C \<CC>\<close> \<open>cat_Set \<beta>\<close> ?cf_eval
    by (rule AG.HomCod.cat_cf_eval_is_functor[OF \<beta> \<alpha>\<beta>])

  from \<alpha>\<beta> interpret FUNCT_\<AA>: tiny_category \<beta> \<open>?FUNCT \<AA>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  from \<alpha>\<beta> interpret FUNCT_\<BB>: tiny_category \<beta> \<open>?FUNCT \<BB>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  from \<alpha>\<beta> interpret FUNCT_\<CC>: tiny_category \<beta> \<open>?FUNCT \<CC>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  
  interpret \<beta>\<AA>: tiny_category \<beta> \<AA>
    by (rule category.cat_tiny_category_if_ge_Limit)
      (use \<alpha>\<beta> in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<BB>: tiny_category \<beta> \<BB>
    by (rule category.cat_tiny_category_if_ge_Limit)
      (use \<alpha>\<beta> in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<CC>: tiny_category \<beta> \<CC>
    by (rule category.cat_tiny_category_if_ge_Limit)
      (use \<alpha>\<beta> in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+

  interpret \<beta>\<KK>: is_tiny_functor \<beta> \<BB> \<CC> \<KK>
    by (rule is_functor.cf_is_tiny_functor_if_ge_Limit)
      (use \<alpha>\<beta> in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<GG>: is_tiny_functor \<beta> \<CC> \<AA> \<GG>
    by (rule is_functor.cf_is_tiny_functor_if_ge_Limit)
      (use \<alpha>\<beta> in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<TT>: is_tiny_functor \<beta> \<BB> \<AA> \<TT>
    by (rule is_functor.cf_is_tiny_functor_if_ge_Limit)
      (use \<alpha>\<beta> in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+

  interpret cat_Set_\<alpha>\<beta>: subcategory \<beta> \<open>cat_Set \<alpha>\<close> \<open>cat_Set \<beta>\<close>
    by (rule AG.subcategory_cat_Set_cat_Set[OF \<beta> \<alpha>\<beta>])

  from assms(3) \<alpha>\<beta> interpret Hom_c: is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<open>?H_\<CC> c\<close> 
    by (cs_concl cs_intro: cat_cs_intros)

  (** E' **)

  define E' :: V where "E' =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<AA>\<lparr>Obj\<rparr>. ?cf_eval\<lparr>ObjMap\<rparr>\<lparr>cf_map (?H_\<AA>\<GG> a), c\<rparr>\<^sub>\<bullet>),
      (\<lambda>f\<in>\<^sub>\<circ>\<AA>\<lparr>Arr\<rparr>. ?cf_eval\<lparr>ArrMap\<rparr>\<lparr>ntcf_arrow (?H_A\<GG> f), \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>\<^sub>\<bullet>),
      op_cat \<AA>,
      cat_Set \<beta>
    ]\<^sub>\<circ> "

  have E'_components:
    "E'\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>\<AA>\<lparr>Obj\<rparr>. ?cf_eval\<lparr>ObjMap\<rparr>\<lparr>cf_map (?H_\<AA>\<GG> a), c\<rparr>\<^sub>\<bullet>)"
    "E'\<lparr>ArrMap\<rparr> =
      (\<lambda>f\<in>\<^sub>\<circ>\<AA>\<lparr>Arr\<rparr>. ?cf_eval\<lparr>ArrMap\<rparr>\<lparr>ntcf_arrow (?H_A\<GG> f), \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>\<^sub>\<bullet>)"
    "E'\<lparr>HomDom\<rparr> = op_cat \<AA>"
    "E'\<lparr>HomCod\<rparr> = cat_Set \<beta>"
    unfolding E'_def dghm_field_simps by (simp_all add: nat_omega_simps)

  note [cat_cs_simps] = E'_components(3,4)
  
  have E'_ObjMap_app[cat_cs_simps]: 
    "E'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = ?cf_eval\<lparr>ObjMap\<rparr>\<lparr>cf_map (?H_\<AA>\<GG> a), c\<rparr>\<^sub>\<bullet>"
    if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
    using that unfolding E'_components by simp
  have E'_ArrMap_app[cat_cs_simps]: 
    "E'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = ?cf_eval\<lparr>ArrMap\<rparr>\<lparr>ntcf_arrow (?H_A\<GG> f), \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>\<^sub>\<bullet>"
    if "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" for f
    using that unfolding E'_components by simp

  have E': "E' : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
  proof(intro is_functorI')

    show "vfsequence E'" unfolding E'_def by auto
    show "vcard E' = 4\<^sub>\<nat>" unfolding E'_def by (simp add: nat_omega_simps)
    show "vsv (E'\<lparr>ObjMap\<rparr>)" unfolding E'_components by simp
    show "vsv (E'\<lparr>ArrMap\<rparr>)" unfolding E'_components by simp
    show "\<D>\<^sub>\<circ> (E'\<lparr>ObjMap\<rparr>) = op_cat \<AA>\<lparr>Obj\<rparr>"
      unfolding E'_components by (simp add: cat_op_simps)
    show "\<R>\<^sub>\<circ> (E'\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<beta>\<lparr>Obj\<rparr>"
      unfolding E'_components
    proof(rule vrange_VLambda_vsubset)
      fix a assume prems: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      then have "?H_\<AA>\<GG> a : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      with assms(3) prems show 
        "?cf_eval\<lparr>ObjMap\<rparr>\<lparr>cf_map (?H_\<AA>\<GG> a), c\<rparr>\<^sub>\<bullet> \<in>\<^sub>\<circ> cat_Set \<beta>\<lparr>Obj\<rparr>"
        by 
          (
            cs_concl
              cs_simp: cat_cs_simps cat_Set_components(1)
              cs_intro: cat_cs_intros cat_op_intros Ran.HomCod.cat_Hom_in_Vset
          )
    qed
    show "\<D>\<^sub>\<circ> (E'\<lparr>ArrMap\<rparr>) = op_cat \<AA>\<lparr>Arr\<rparr>"
      unfolding E'_components by (simp add: cat_op_simps)
    show "E'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : E'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> E'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "f : a \<mapsto>\<^bsub>op_cat \<AA>\<^esub> b" for a b f
    proof-
      from that[unfolded cat_op_simps] assms(3) show ?thesis
        by (intro cat_Set_\<alpha>\<beta>.subcat_is_arrD)
          (
            cs_concl 
              cs_simp:
                category.cf_eval_ObjMap_app
                category.cf_eval_ArrMap_app
                E'_ObjMap_app
                E'_ArrMap_app
              cs_intro: cat_cs_intros
          )
    qed
    then have [cat_cs_intros]: "E'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : A \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> B"
      if "A = E'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" and "B = E'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>" and "f : b \<mapsto>\<^bsub>\<AA>\<^esub> a" 
      for a b f A B
      using that by (simp add: cat_op_simps)
    show
      "E'\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>op_cat \<AA>\<^esub> f\<rparr> = E'\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> E'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      if "g : b \<mapsto>\<^bsub>op_cat \<AA>\<^esub> c" and "f : a \<mapsto>\<^bsub>op_cat \<AA>\<^esub> b" for b c g a f
    proof-
      note g = that(1)[unfolded cat_op_simps]
        and f = that(2)[unfolded cat_op_simps]
      from g f assms(3) \<alpha>\<beta> show ?thesis
        by 
          (
            cs_concl
              cs_intro:
                cat_small_cs_intros
                cat_cs_intros
                cat_prod_cs_intros
                cat_FUNCT_cs_intros 
                cat_op_intros
              cs_simp:
                cat_cs_simps
                cat_FUNCT_cs_simps 
                cat_prod_cs_simps 
                cat_op_simps
                E.cf_ArrMap_Comp[symmetric]
          )+
    qed
    
    show "E'\<lparr>ArrMap\<rparr>\<lparr>op_cat \<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>\<rparr> = cat_Set \<beta>\<lparr>CId\<rparr>\<lparr>E'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
      if "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>" for a
    proof(cs_concl_step cat_Set_\<alpha>\<beta>.subcat_CId[symmetric])
      from that[unfolded cat_op_simps] assms(3) show 
        "E'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: cat_Set_components(1) cat_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros
          )
      from that[unfolded cat_op_simps] assms(3) show 
        "E'\<lparr>ArrMap\<rparr>\<lparr>op_cat \<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>\<rparr> = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>E'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
        by
          (
            cs_concl 
              cs_intro: cat_cs_intros
              cs_simp:
                cat_Set_components(1)
                cat_cs_simps
                cat_op_simps
                ntcf_id_cf_comp[symmetric]
          )
    qed
  qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+
  then interpret E': is_functor \<beta> \<open>op_cat \<AA>\<close> \<open>cat_Set \<beta>\<close> E' by simp


  (** N' **)

  define N' :: V where "N' =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<AA>\<lparr>Obj\<rparr>. ?cf_nt\<lparr>ObjMap\<rparr>\<lparr>cf_map (?H_\<AA>\<GG> a), c\<rparr>\<^sub>\<bullet>),
      (\<lambda>f\<in>\<^sub>\<circ>\<AA>\<lparr>Arr\<rparr>. ?cf_nt\<lparr>ArrMap\<rparr>\<lparr>ntcf_arrow (?H_A\<GG> f), \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>\<^sub>\<bullet>),
      op_cat \<AA>,
      cat_Set \<beta>
    ]\<^sub>\<circ> "

  have N'_components:
    "N'\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>\<AA>\<lparr>Obj\<rparr>. ?cf_nt\<lparr>ObjMap\<rparr>\<lparr>cf_map (?H_\<AA>\<GG> a), c\<rparr>\<^sub>\<bullet>)"
    "N'\<lparr>ArrMap\<rparr> =
      (\<lambda>f\<in>\<^sub>\<circ>\<AA>\<lparr>Arr\<rparr>. ?cf_nt\<lparr>ArrMap\<rparr>\<lparr>ntcf_arrow (?H_A\<GG> f), \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>\<^sub>\<bullet>)"
    "N'\<lparr>HomDom\<rparr> = op_cat \<AA>"
    "N'\<lparr>HomCod\<rparr> = cat_Set \<beta>"
    unfolding N'_def dghm_field_simps by (simp_all add: nat_omega_simps)

  note [cat_cs_simps] = N'_components(3,4)
  
  have N'_ObjMap_app[cat_cs_simps]: 
    "N'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = ?cf_nt\<lparr>ObjMap\<rparr>\<lparr>cf_map (?H_\<AA>\<GG> a), c\<rparr>\<^sub>\<bullet>"
    if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
    using that unfolding N'_components by simp
  have N'_ArrMap_app[cat_cs_simps]: 
    "N'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = ?cf_nt\<lparr>ArrMap\<rparr>\<lparr>ntcf_arrow (?H_A\<GG> f), \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>\<^sub>\<bullet>"
    if "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" for f
    using that unfolding N'_components by simp

  from \<alpha>\<beta> interpret cf_nt_\<CC>: is_functor \<beta> \<open>?FUNCT \<CC> \<times>\<^sub>C \<CC>\<close> \<open>cat_Set \<beta>\<close> \<open>?cf_nt\<close>
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  
  have N': "N' : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
  proof(intro is_functorI')
    show "vfsequence N'" unfolding N'_def by simp
    show "vcard N' = 4\<^sub>\<nat>" unfolding N'_def by (simp add: nat_omega_simps)
    show "vsv (N'\<lparr>ObjMap\<rparr>)" unfolding N'_components by simp
    show "vsv (N'\<lparr>ArrMap\<rparr>)" unfolding N'_components by simp
    show "\<D>\<^sub>\<circ> (N'\<lparr>ObjMap\<rparr>) = op_cat \<AA>\<lparr>Obj\<rparr>"
      unfolding N'_components by (simp add: cat_op_simps)
    show "\<R>\<^sub>\<circ> (N'\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<beta>\<lparr>Obj\<rparr>"
      unfolding N'_components
    proof(rule vrange_VLambda_vsubset)
      fix a assume prems: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      with assms(3) \<alpha>\<beta> show 
        "?cf_nt\<lparr>ObjMap\<rparr>\<lparr>cf_map (?H_\<AA>\<GG> a), c\<rparr>\<^sub>\<bullet> \<in>\<^sub>\<circ> cat_Set \<beta>\<lparr>Obj\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: cat_Set_components(1) cat_cs_simps cat_FUNCT_cs_simps  
              cs_intro: cat_cs_intros FUNCT_\<CC>.cat_Hom_in_Vset cat_FUNCT_cs_intros
          )
    qed
    show "\<D>\<^sub>\<circ> (N'\<lparr>ArrMap\<rparr>) = op_cat \<AA>\<lparr>Arr\<rparr>" 
      unfolding N'_components by (simp add: cat_op_simps)
    show "N'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : N'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> N'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "f : a \<mapsto>\<^bsub>op_cat \<AA>\<^esub> b" for a b f
      using that[unfolded cat_op_simps] assms(3)
      by 
        (
          cs_concl 
            cs_simp: N'_ObjMap_app N'_ArrMap_app 
            cs_intro: cat_cs_intros cat_prod_cs_intros cat_FUNCT_cs_intros
        )
    show 
      "N'\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>op_cat \<AA>\<^esub> f\<rparr> = N'\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> N'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      if "g : b \<mapsto>\<^bsub>op_cat \<AA>\<^esub> c" and "f : a \<mapsto>\<^bsub>op_cat \<AA>\<^esub> b" for b c g a f
    proof-
      from that assms(3) \<alpha>\<beta> show ?thesis
        unfolding cat_op_simps
        by
          (
            cs_concl
              cs_intro:
                cat_cs_intros
                cat_prod_cs_intros
                cat_FUNCT_cs_intros 
                cat_op_intros
              cs_simp:
                cat_cs_simps
                cat_FUNCT_cs_simps 
                cat_prod_cs_simps 
                cat_op_simps
                cf_nt_\<CC>.cf_ArrMap_Comp[symmetric]
          )
    qed
    show "N'\<lparr>ArrMap\<rparr>\<lparr>op_cat \<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>\<rparr> = cat_Set \<beta>\<lparr>CId\<rparr>\<lparr>N'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
      if "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>" for a
    proof-
      note [cat_cs_simps] = 
        ntcf_id_cf_comp[symmetric] 
        ntcf_arrow_id_ntcf_id[symmetric]
        cat_FUNCT_CId_app[symmetric] 
      from that[unfolded cat_op_simps] assms(3) \<alpha>\<beta> show ?thesis
        by (*very slow*)
          (
            cs_concl
              cs_intro:
                cat_cs_intros
                cat_FUNCT_cs_intros
                cat_prod_cs_intros
                cat_op_intros
              cs_simp: cat_FUNCT_cs_simps cat_cs_simps cat_op_simps 
          )+
    qed
  qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+
  then interpret N': is_functor \<beta> \<open>op_cat \<AA>\<close> \<open>cat_Set \<beta>\<close> N' by simp


  (** Y' **)
  
  define Y' :: V where "Y' =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<AA>\<lparr>Obj\<rparr>. ntcf_Yoneda \<alpha> \<beta> \<CC>\<lparr>NTMap\<rparr>\<lparr>cf_map (?H_\<AA>\<GG> a), c\<rparr>\<^sub>\<bullet>),
      N',
      E',
      op_cat \<AA>,
      cat_Set \<beta>
    ]\<^sub>\<circ>"

  have Y'_components:
    "Y'\<lparr>NTMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>\<AA>\<lparr>Obj\<rparr>. ntcf_Yoneda \<alpha> \<beta> \<CC>\<lparr>NTMap\<rparr>\<lparr>cf_map (?H_\<AA>\<GG> a), c\<rparr>\<^sub>\<bullet>)"
    "Y'\<lparr>NTDom\<rparr> = N'"
    "Y'\<lparr>NTCod\<rparr> = E'"
    "Y'\<lparr>NTDGDom\<rparr> = op_cat \<AA>"
    "Y'\<lparr>NTDGCod\<rparr> = cat_Set \<beta>"
    unfolding Y'_def nt_field_simps by (simp_all add: nat_omega_simps)

  note [cat_cs_simps] = Y'_components(2-5)

  have Y'_NTMap_app[cat_cs_simps]: 
    "Y'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = ntcf_Yoneda \<alpha> \<beta> \<CC>\<lparr>NTMap\<rparr>\<lparr>cf_map (?H_\<AA>\<GG> a), c\<rparr>\<^sub>\<bullet>" 
    if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
    using that unfolding Y'_components by simp

  from \<beta> \<alpha>\<beta> interpret Y: 
    is_iso_ntcf \<beta> \<open>?FUNCT \<CC> \<times>\<^sub>C \<CC>\<close> \<open>cat_Set \<beta>\<close> ?cf_nt ?cf_eval \<open>ntcf_Yoneda \<alpha> \<beta> \<CC>\<close>
    by (rule AG.HomCod.cat_ntcf_Yoneda_is_ntcf)

  have Y': "Y' : N' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o E' : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
  proof(intro is_iso_ntcfI is_ntcfI')

    show "vfsequence Y'" unfolding Y'_def by simp
    show "vcard Y' = 5\<^sub>\<nat>"
      unfolding Y'_def by (simp add: nat_omega_simps)
    show "vsv (Y'\<lparr>NTMap\<rparr>)" unfolding Y'_components by auto
    show "\<D>\<^sub>\<circ> (Y'\<lparr>NTMap\<rparr>) = op_cat \<AA>\<lparr>Obj\<rparr>"
      unfolding Y'_components by (simp add: cat_op_simps)
    show Y'_NTMap_a: "Y'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : N'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<beta>\<^esub> E'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>" for a
      using that[unfolded cat_op_simps] assms(3)
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps
            cs_intro:
              cat_arrow_cs_intros
              cat_cs_intros
              cat_prod_cs_intros
              cat_FUNCT_cs_intros
        )
    then show "Y'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : N'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> E'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>" for a
      by (intro cat_Set_is_arr_isomorphismD[OF Y'_NTMap_a[OF that]])
    show
      "Y'\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> N'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        E'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> Y'\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      if "f : a \<mapsto>\<^bsub>op_cat \<AA>\<^esub> b" for a b f
    proof-
      note f = that[unfolded cat_op_simps]
      from f assms(3) show ?thesis
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps Y.ntcf_Comp_commute 
              cs_intro: cat_cs_intros cat_prod_cs_intros cat_FUNCT_cs_intros
          )+      
    qed
  qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+

  have E'_def: "E' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(-,?\<GG>c)"
  proof(rule cf_eqI)
    show "E' : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
      by (cs_concl cs_intro: cat_cs_intros)
    from assms(3) show
      "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(-,?\<GG>c) : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    have dom_lhs: "\<D>\<^sub>\<circ> (E'\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>" unfolding E'_components by simp
    from assms(3) have dom_rhs: 
      "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(-,?\<GG>c)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      unfolding E'_components 
      by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
    show "E'\<lparr>ObjMap\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(-,?\<GG>c)\<lparr>ObjMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      with assms(3) show "E'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(-,?\<GG>c)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by
          (
            cs_concl
              cs_simp: cat_op_simps cat_cs_simps
              cs_intro: cat_cs_intros cat_op_intros
          )
    qed (auto simp: E'_components cat_cs_intros assms(3))

    have dom_lhs: "\<D>\<^sub>\<circ> (E'\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>" unfolding E'_components by simp
    from assms(3) have dom_rhs: 
      "\<D>\<^sub>\<circ> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(-,?\<GG>c)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
      unfolding E'_components 
      by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
    
    show "E'\<lparr>ArrMap\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(-,?\<GG>c)\<lparr>ArrMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)

      fix f assume prems: "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
      then obtain a b where f: "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" by auto
      have [cat_cs_simps]:
        "cf_eval_arrow \<CC> (ntcf_arrow (?H_A\<GG> f)) (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) =
          cf_hom \<AA> [f, \<AA>\<lparr>CId\<rparr>\<lparr>?\<GG>c\<rparr>]\<^sub>\<circ>"
        (is \<open>?cf_eval_arrow = ?cf_hom_f\<GG>c\<close>)
      proof-
        have cf_eval_arrow_f_CId_\<GG>c:
          "?cf_eval_arrow :
            Hom \<AA> b ?\<GG>c \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<AA> a ?\<GG>c"
        proof(rule cf_eval_arrow_is_arr')
          from f show "?H_A\<GG> f :
            ?H_\<AA>\<GG> b \<mapsto>\<^sub>C\<^sub>F ?H_\<AA>\<GG> a : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
            by (cs_concl cs_intro: cat_cs_intros)
        qed
          (
            use f assms(3) in
              \<open>
                cs_concl
                  cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros
              \<close>
          )+
        from f assms(3) have dom_lhs:
          "\<D>\<^sub>\<circ> (?cf_eval_arrow\<lparr>ArrVal\<rparr>) = Hom \<AA> b ?\<GG>c"
          by
            (
              cs_concl
                cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros
            )
        from assms(3) f Ran.HomCod.category_axioms have cf_hom_f\<GG>c:
          "?cf_hom_f\<GG>c :
            Hom \<AA> b ?\<GG>c \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<AA> a ?\<GG>c"
          by 
            (
              cs_concl cs_intro:
                cat_cs_intros cat_prod_cs_intros cat_op_intros
            )
        from f assms(3) have dom_rhs: 
          "\<D>\<^sub>\<circ> (?cf_hom_f\<GG>c\<lparr>ArrVal\<rparr>) = Hom \<AA> b ?\<GG>c"
          by
            (
              cs_concl 
                cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros
            )

        show ?thesis
        proof(rule arr_Set_eqI)
          from cf_eval_arrow_f_CId_\<GG>c show "arr_Set \<alpha> ?cf_eval_arrow"
            by (auto dest: cat_Set_is_arrD(1))
          from cf_hom_f\<GG>c show "arr_Set \<alpha> ?cf_hom_f\<GG>c"
            by (auto dest: cat_Set_is_arrD(1))
          show "?cf_eval_arrow\<lparr>ArrVal\<rparr> = ?cf_hom_f\<GG>c\<lparr>ArrVal\<rparr>"
          proof(rule vsv_eqI, unfold dom_lhs dom_rhs, unfold in_Hom_iff)
            from f assms(3) show "vsv (?cf_eval_arrow\<lparr>ArrVal\<rparr>)"
              by (cs_concl cs_intro: cat_cs_intros)
            from f assms(3) show "vsv (?cf_hom_f\<GG>c\<lparr>ArrVal\<rparr>)"
              by
                (
                  cs_concl
                    cs_simp: cat_cs_simps cat_op_simps 
                    cs_intro: cat_cs_intros cat_op_intros
                )            
            fix g assume "g : b \<mapsto>\<^bsub>\<AA>\<^esub> ?\<GG>c"
            with f assms(3) show 
              "?cf_eval_arrow\<lparr>ArrVal\<rparr>\<lparr>g\<rparr> = ?cf_hom_f\<GG>c\<lparr>ArrVal\<rparr>\<lparr>g\<rparr>"
              by
                (
                  cs_concl
                    cs_simp: cat_cs_simps cat_op_simps
                    cs_intro: cat_cs_intros cat_op_intros
                )
          qed simp

        qed
          (
            use cf_eval_arrow_f_CId_\<GG>c cf_hom_f\<GG>c in 
              \<open>cs_concl cs_simp: cat_cs_simps\<close>
          )+

      qed
      
      from f prems assms(3) show
        "E'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(-,?\<GG>c)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
        by
          (
            cs_concl
              cs_simp: cat_op_simps cat_cs_simps 
              cs_intro: cat_cs_intros cat_op_intros
          )

    qed (auto simp: E'_components cat_cs_intros assms(3))

  qed simp_all

  from Y' have inv_Y': "inv_ntcf Y' :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(-,?\<GG>c) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o N' : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
    unfolding E'_def by (auto intro: iso_ntcf_is_arr_isomorphism)

  interpret N'': is_functor \<beta> \<open>op_cat \<AA>\<close> \<open>cat_Set \<beta>\<close> \<open>L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<close>
    by (rule L_10_5_N_is_functor[OF \<beta> \<alpha>\<beta> assms])


  (** \<psi> **)

  define \<psi> :: V
    where "\<psi> =
      [
        (\<lambda>a\<in>\<^sub>\<circ>\<AA>\<lparr>Obj\<rparr>. ?ntcf_ua_fo a\<lparr>NTMap\<rparr>\<lparr>cf_map (?H_\<CC> c)\<rparr>),
        N',
        L_10_5_N \<alpha> \<beta> \<TT> \<KK> c,
        op_cat \<AA>,
        cat_Set \<beta>
      ]\<^sub>\<circ>"

  have \<psi>_components:
    "\<psi>\<lparr>NTMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>\<AA>\<lparr>Obj\<rparr>. ?ntcf_ua_fo a\<lparr>NTMap\<rparr>\<lparr>cf_map (?H_\<CC> c)\<rparr>)"
    "\<psi>\<lparr>NTDom\<rparr> = N'"
    "\<psi>\<lparr>NTCod\<rparr> = L_10_5_N \<alpha> \<beta> \<TT> \<KK> c"
    "\<psi>\<lparr>NTDGDom\<rparr> = op_cat \<AA>"
    "\<psi>\<lparr>NTDGCod\<rparr> = cat_Set \<beta>"
    unfolding \<psi>_def nt_field_simps by (simp_all add: nat_omega_simps)

  note [cat_cs_simps] = Y'_components(2-5)

  have \<psi>_NTMap_app[cat_cs_simps]: 
    "\<psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = ?ntcf_ua_fo a\<lparr>NTMap\<rparr>\<lparr>cf_map (?H_\<CC> c)\<rparr>" 
    if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
    using that unfolding \<psi>_components by simp

  have \<psi>: "\<psi> : N' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o L_10_5_N \<alpha> \<beta> \<TT> \<KK> c : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
  proof-

    show ?thesis
    proof(intro is_iso_ntcfI is_ntcfI')

      show "vfsequence \<psi>" unfolding \<psi>_def by auto
      show "vcard \<psi> = 5\<^sub>\<nat>" unfolding \<psi>_def by (simp_all add: nat_omega_simps)
      show "N' : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>" by (rule N')
      show "L_10_5_N \<alpha> \<beta> \<TT> \<KK> c : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      show "\<psi>\<lparr>NTDom\<rparr> = N'" unfolding \<psi>_components by simp
      show "\<psi>\<lparr>NTCod\<rparr> = L_10_5_N \<alpha> \<beta> \<TT> \<KK> c" unfolding \<psi>_components by simp
      show "\<psi>\<lparr>NTDGDom\<rparr> = op_cat \<AA>" unfolding \<psi>_components by simp
      show "\<psi>\<lparr>NTDGCod\<rparr> = cat_Set \<beta>" unfolding \<psi>_components by simp
      show "vsv (\<psi>\<lparr>NTMap\<rparr>)" unfolding \<psi>_components by simp
      show "\<D>\<^sub>\<circ> (\<psi>\<lparr>NTMap\<rparr>) = op_cat \<AA>\<lparr>Obj\<rparr>" 
        unfolding \<psi>_components by (simp add: cat_op_simps)

      show \<psi>_NTMap_is_arr_isomorphism[unfolded cat_op_simps]:
        "\<psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : N'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<beta>\<^esub> L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        if "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>" for a
      proof-
        note a = that[unfolded cat_op_simps]
        interpret \<epsilon>: 
          is_cat_rKe_preserves \<alpha> \<BB> \<CC> \<AA> \<open>cat_Set \<alpha>\<close> \<KK> \<TT> \<GG> \<open>?H_\<AA> a\<close> \<epsilon>
          by (rule cat_pw_rKe_preserved[OF a])
        interpret a\<epsilon>: 
          is_cat_rKe \<alpha> \<BB> \<CC> \<open>cat_Set \<alpha>\<close> \<KK> \<open>?H_\<AA>\<TT> a\<close> \<open>?H_\<AA>\<GG> a\<close> \<open>?H_\<AA>\<epsilon> a\<close>
          by (rule \<epsilon>.cat_rKe_preserves)
        interpret is_iso_ntcf
          \<beta>
          \<open>op_cat (?FUNCT \<CC>)\<close>
          \<open>cat_Set \<beta>\<close>
          \<open>?H_FUNCT \<CC> (?H_\<AA>\<GG> a)\<close>
          \<open>?H_FUNCT \<BB> (?H_\<AA>\<TT> a) \<circ>\<^sub>C\<^sub>F op_cf ?SET_\<KK>\<close>
          \<open>?ntcf_ua_fo a\<close>
          by (rule a\<epsilon>.cat_rKe_ntcf_ua_fo_is_iso_ntcf_if_ge_Limit[OF \<beta> \<alpha>\<beta>])
        have "cf_map (?H_\<CC> c) \<in>\<^sub>\<circ> ?FUNCT \<CC>\<lparr>Obj\<rparr>"
          by
            (
              cs_concl 
                cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
                cs_intro: cat_cs_intros cat_FUNCT_cs_intros
            )
        from 
          iso_ntcf_is_arr_isomorphism[unfolded cat_op_simps, OF this] 
          a assms \<alpha>\<beta> 
        show ?thesis
          by (*very slow*)
            (
              cs_prems 
                cs_simp: 
                  cat_cs_simps cat_Kan_cs_simps cat_FUNCT_cs_simps cat_op_simps 
                cs_intro: 
                  cat_small_cs_intros 
                  cat_Kan_cs_intros
                  cat_cs_intros
                  cat_FUNCT_cs_intros
                  cat_op_intros
            )
      qed
      show \<psi>_NTMap_is_arr[unfolded cat_op_simps]: 
        "\<psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : N'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        if "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>" for a
        by 
          (
            rule cat_Set_is_arr_isomorphismD[
              OF \<psi>_NTMap_is_arr_isomorphism[OF that[unfolded cat_op_simps]]
              ]
          )

      show 
        "\<psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> N'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
          L_10_5_N \<alpha> \<beta> \<TT> \<KK> c\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> \<psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        if "f : a \<mapsto>\<^bsub>op_cat \<AA>\<^esub> b" for a b f
      proof-

        note f = that[unfolded cat_op_simps]
        from f have a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" by auto

        interpret p_a_\<epsilon>: 
          is_cat_rKe_preserves \<alpha> \<BB> \<CC> \<AA> \<open>cat_Set \<alpha>\<close> \<KK> \<TT> \<GG> \<open>?H_\<AA> a\<close> \<epsilon>
          by (rule cat_pw_rKe_preserved[OF a])
        interpret a_\<epsilon>: is_cat_rKe 
          \<alpha> \<BB> \<CC> \<open>cat_Set \<alpha>\<close> \<KK> \<open>?H_\<AA>\<TT> a\<close> \<open>?H_\<AA>\<GG> a\<close> \<open>?H_\<AA>\<epsilon> a\<close>
          by (rule p_a_\<epsilon>.cat_rKe_preserves)
        interpret ntcf_ua_fo_a_\<epsilon>: is_iso_ntcf
          \<beta> ?ua_NTDGDom \<open>cat_Set \<beta>\<close> \<open>?ua_NTDom a\<close> \<open>?ua_NTCod a\<close> \<open>?ua a\<close>
          by (rule a_\<epsilon>.cat_rKe_ntcf_ua_fo_is_iso_ntcf_if_ge_Limit[OF \<beta> \<alpha>\<beta>])

        interpret p_b_\<epsilon>:
          is_cat_rKe_preserves \<alpha> \<BB> \<CC> \<AA> \<open>cat_Set \<alpha>\<close> \<KK> \<TT> \<GG> \<open>?H_\<AA> b\<close> \<epsilon>
          by (rule cat_pw_rKe_preserved[OF b])
        interpret b_\<epsilon>: is_cat_rKe 
          \<alpha> \<BB> \<CC> \<open>cat_Set \<alpha>\<close> \<KK> \<open>?H_\<AA>\<TT> b\<close> \<open>?H_\<AA>\<GG> b\<close> \<open>?H_\<AA>\<epsilon> b\<close>
          by (rule p_b_\<epsilon>.cat_rKe_preserves)
        interpret ntcf_ua_fo_b_\<epsilon>: is_iso_ntcf
          \<beta> ?ua_NTDGDom \<open>cat_Set \<beta>\<close> \<open>?ua_NTDom b\<close> \<open>?ua_NTCod b\<close> \<open>?ua b\<close>
          by (rule b_\<epsilon>.cat_rKe_ntcf_ua_fo_is_iso_ntcf_if_ge_Limit[OF \<beta> \<alpha>\<beta>])

        interpret \<KK>_SET: is_tiny_functor \<beta> \<open>?FUNCT \<CC>\<close> \<open>?FUNCT \<BB>\<close> ?SET_\<KK>
          by 
            (
              rule exp_cat_cf_is_tiny_functor[
                OF \<beta> \<alpha>\<beta> AG.category_cat_Set AG.is_functor_axioms
                ]
            )
        from f interpret Hom_f:
          is_ntcf \<alpha> \<AA> \<open>cat_Set \<alpha>\<close> \<open>?H_\<AA> a\<close> \<open>?H_\<AA> b\<close> \<open>?H_A f\<close>
          by (cs_concl cs_intro: cat_cs_intros)

        let ?cf_hom_lhs =
          \<open>
            cf_hom
              (?FUNCT \<CC>)
              [ntcf_arrow (ntcf_id (?H_\<CC> c)), ntcf_arrow (?H_A\<GG> f)]\<^sub>\<circ>
          \<close>
        let ?cf_hom_rhs = 
          \<open>
            cf_hom
              (?FUNCT \<BB>)
              [
                ntcf_arrow (ntcf_id (?H_\<CC> c \<circ>\<^sub>C\<^sub>F \<KK>)),
                ntcf_arrow (?H_A f \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<TT>)
              ]\<^sub>\<circ>
          \<close>
        let ?dom =
          \<open>Hom (?FUNCT \<CC>) (cf_map (?H_\<CC> c)) (cf_map (?H_\<AA>\<GG> a))\<close>
        let ?cod = \<open>Hom (?FUNCT \<BB>) (cf_map (?H_\<CC>\<KK> c)) (cf_map (?H_\<AA>\<TT> b))\<close>
        let ?cf_hom_lhs_umap_fo_inter =
          \<open>Hom (?FUNCT \<CC>) (cf_map (?H_\<CC> c)) (cf_map (?H_\<AA>\<GG> b))\<close>
        let ?umap_fo_cf_hom_rhs_inter =
          \<open>Hom (?FUNCT \<BB>) (cf_map (?H_\<CC>\<KK> c)) (cf_map (?H_\<AA>\<TT> a))\<close>

        have [cat_cs_simps]:
          "?umap_fo b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?cf_hom_lhs =
            ?cf_hom_rhs \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?umap_fo a"
        proof-

          from f assms(3) \<alpha>\<beta> have cf_hom_lhs:
            "?cf_hom_lhs : ?dom \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> ?cf_hom_lhs_umap_fo_inter"
            by
              (
                cs_concl
                  cs_simp: cat_cs_simps cat_FUNCT_cs_simps
                  cs_intro:
                    cat_cs_intros
                    cat_FUNCT_cs_intros
                    cat_prod_cs_intros
                    cat_op_intros
              )
          from f assms(3) \<alpha>\<beta> have umap_fo_b:
            "?umap_fo b : ?cf_hom_lhs_umap_fo_inter \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> ?cod"
            by
              (
                cs_concl
                  cs_simp: cat_cs_simps cat_FUNCT_cs_simps
                  cs_intro: 
                    cat_small_cs_intros
                    cat_cs_intros
                    cat_FUNCT_cs_intros
                    cat_prod_cs_intros
                    cat_op_intros
              )
          from cf_hom_lhs umap_fo_b have umap_fo_cf_hom_lhs:
            "?umap_fo b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?cf_hom_lhs : ?dom \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> ?cod"
            by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
          then have dom_umap_fo_cf_hom_lhs: 
            "\<D>\<^sub>\<circ> ((?umap_fo b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?cf_hom_lhs)\<lparr>ArrVal\<rparr>) = ?dom"
            by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

          from f assms(3) \<alpha>\<beta> have cf_hom_rhs: 
            "?cf_hom_rhs : ?umap_fo_cf_hom_rhs_inter \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> ?cod"
            by (*slow*)
              (
                cs_concl
                  cs_simp: cat_cs_simps cat_FUNCT_cs_simps
                  cs_intro:
                    cat_cs_intros
                    cat_FUNCT_cs_intros
                    cat_prod_cs_intros
                    cat_op_intros
              )
          from f assms(3) \<alpha>\<beta> have umap_fo_a:
            "?umap_fo a : ?dom \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> ?umap_fo_cf_hom_rhs_inter"
            by (*slow*)
              (
                cs_concl
                  cs_simp: cat_cs_simps cat_FUNCT_cs_simps
                  cs_intro:
                    cat_small_cs_intros 
                    cat_cs_intros 
                    cat_FUNCT_cs_intros 
                    cat_prod_cs_intros 
                    cat_op_intros
              )
          from cf_hom_rhs umap_fo_a have cf_hom_rhs_umap_fo_a: 
            "?cf_hom_rhs \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?umap_fo a : ?dom \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> ?cod"
            by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros )
          then have dom_cf_hom_rhs_umap_fo_a: 
            "\<D>\<^sub>\<circ> ((?cf_hom_rhs \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?umap_fo a)\<lparr>ArrVal\<rparr>) = ?dom"
            by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
          
          show ?thesis
          proof(rule arr_Set_eqI)

            from umap_fo_cf_hom_lhs show arr_Set_umap_fo_cf_hom_lhs: 
              "arr_Set \<beta> (?umap_fo b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?cf_hom_lhs)"
              by (auto dest: cat_Set_is_arrD(1))
            from cf_hom_rhs_umap_fo_a show arr_Set_cf_hom_rhs_umap_fo_a: 
              "arr_Set \<beta> (?cf_hom_rhs \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?umap_fo a)"
              by (auto dest: cat_Set_is_arrD(1))

            show 
              "(?umap_fo b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?cf_hom_lhs)\<lparr>ArrVal\<rparr> =
                (?cf_hom_rhs \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?umap_fo a)\<lparr>ArrVal\<rparr>"
            proof
              (
                rule vsv_eqI, 
                unfold 
                  dom_umap_fo_cf_hom_lhs dom_cf_hom_rhs_umap_fo_a in_Hom_iff; 
                (rule refl)?
              )

              fix \<HH> assume prems:
                "\<HH> : cf_map (?H_\<CC> c) \<mapsto>\<^bsub>?FUNCT \<CC>\<^esub> cf_map (?H_\<AA>\<GG> a)"

              let ?\<HH> = \<open>ntcf_of_ntcf_arrow \<CC> (cat_Set \<alpha>) \<HH>\<close>
              let ?lhs = \<open>?H_\<AA>\<epsilon> b \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ((?H_A\<GG> f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<HH>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)\<close>
              let ?rhs = 
                \<open>(?H_A f \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?H_\<AA>\<epsilon> a \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<HH> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>))\<close>
              let ?cf_hom_\<AA>\<epsilon> = \<open>\<lambda>b b'. cf_hom \<AA> [\<AA>\<lparr>CId\<rparr>\<lparr>b\<rparr>, \<epsilon>\<lparr>NTMap\<rparr>\<lparr>b'\<rparr>]\<^sub>\<circ>\<close>
              let ?Yc = \<open>\<lambda>Q. Yoneda_component (?H_\<AA> b) a f Q\<close>
              let ?\<HH>\<KK> = \<open>\<lambda>b'. ?\<HH>\<lparr>NTMap\<rparr>\<lparr>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>\<rparr>\<close>
              let ?\<GG>\<KK> = \<open>\<lambda>b'. \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>\<rparr>\<close>

              have [cat_cs_simps]: 
                "cf_of_cf_map \<CC> (cat_Set \<alpha>) (cf_map (?H_\<CC> c)) = ?H_\<CC> c"
                by (cs_concl cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)
              have [cat_cs_simps]: 
                "cf_of_cf_map \<CC> (cat_Set \<alpha>) (cf_map (?H_\<AA>\<GG> a)) = ?H_\<AA>\<GG> a"
                by (cs_concl cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)
              note \<HH> = cat_FUNCT_is_arrD[OF prems, unfolded cat_cs_simps]
              have Hom_c: "?H_\<CC>\<KK> c : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
                by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

              have [cat_cs_simps]: "?lhs = ?rhs"
              proof(rule ntcf_eqI)
                from \<HH>(1) f show lhs: 
                  "?lhs : ?H_\<CC>\<KK> c \<mapsto>\<^sub>C\<^sub>F ?H_\<AA>\<TT> b : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
                  by (cs_concl cs_simp: cs_intro: cat_cs_intros)
                then have dom_lhs: "\<D>\<^sub>\<circ> (?lhs\<lparr>NTMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>" 
                  by (cs_concl cs_simp: cat_cs_simps)+
                from \<HH>(1) f show rhs: 
                  "?rhs : ?H_\<CC>\<KK> c \<mapsto>\<^sub>C\<^sub>F ?H_\<AA>\<TT> b : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
                  by (cs_concl cs_simp: cs_intro: cat_cs_intros)
                then have dom_rhs: "\<D>\<^sub>\<circ> (?rhs\<lparr>NTMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
                  by (cs_concl cs_simp: cat_cs_simps)+
                have [cat_cs_simps]:
                  "?cf_hom_\<AA>\<epsilon> b b' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> 
                    (?Yc (?\<GG>\<KK> b') \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<HH>\<KK> b') =
                      ?Yc (\<TT>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>) \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
                        (?cf_hom_\<AA>\<epsilon> a b' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<HH>\<KK> b')"
                  (is \<open>?lhs_Set = ?rhs_Set\<close>)
                  if "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" for b'
                proof-
                  let ?\<KK>b' = \<open>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>\<close>
                  from \<HH>(1) f that assms(3) Ran.HomCod.category_axioms 
                  have lhs_Set_is_arr: "?lhs_Set :
                    Hom \<CC> c (?\<KK>b') \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<AA> b (\<TT>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>)"
                    by
                      (
                        cs_concl
                          cs_simp: cat_cs_simps cat_op_simps 
                          cs_intro: 
                            cat_cs_intros cat_prod_cs_intros cat_op_intros
                      )
                  then have dom_lhs_Set: "\<D>\<^sub>\<circ> (?lhs_Set\<lparr>ArrVal\<rparr>) = Hom \<CC> c ?\<KK>b'" 
                    by (cs_concl cs_simp: cat_cs_simps)
                  from \<HH>(1) f that assms(3) Ran.HomCod.category_axioms 
                  have rhs_Set_is_arr: "?rhs_Set :
                    Hom \<CC> c (?\<KK>b') \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<AA> b (\<TT>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>)"
                    by
                      (
                        cs_concl
                          cs_simp: cat_cs_simps cat_op_simps 
                          cs_intro:
                            cat_cs_intros cat_prod_cs_intros cat_op_intros
                      )
                  then have dom_rhs_Set: "\<D>\<^sub>\<circ> (?rhs_Set\<lparr>ArrVal\<rparr>) = Hom \<CC> c ?\<KK>b'" 
                    by (cs_concl cs_simp: cat_cs_simps)
                show ?thesis
                proof(rule arr_Set_eqI)
                  from lhs_Set_is_arr show arr_Set_lhs_Set: "arr_Set \<alpha> ?lhs_Set" 
                    by (auto dest: cat_Set_is_arrD(1))
                  from rhs_Set_is_arr show arr_Set_rhs_Set: "arr_Set \<alpha> ?rhs_Set"
                    by (auto dest: cat_Set_is_arrD(1))
                  show "?lhs_Set\<lparr>ArrVal\<rparr> = ?rhs_Set\<lparr>ArrVal\<rparr>"
                  proof(rule vsv_eqI, unfold dom_lhs_Set dom_rhs_Set in_Hom_iff)
                    fix h assume "h : c \<mapsto>\<^bsub>\<CC>\<^esub> ?\<KK>b'"
                    with \<HH>(1) f that assms Ran.HomCod.category_axioms show 
                      "?lhs_Set\<lparr>ArrVal\<rparr>\<lparr>h\<rparr> = ?rhs_Set\<lparr>ArrVal\<rparr>\<lparr>h\<rparr>"
                      by (*exceptionally slow*) 
                        (
                          cs_concl 
                            cs_simp: cat_cs_simps cat_op_simps 
                            cs_intro: 
                              cat_cs_intros cat_prod_cs_intros cat_op_intros
                        )
                  qed (use arr_Set_lhs_Set arr_Set_rhs_Set in auto)
                qed
                  (
                    use lhs_Set_is_arr rhs_Set_is_arr in
                      \<open>cs_concl cs_simp: cat_cs_simps\<close>
                  )+

              qed

              show "?lhs\<lparr>NTMap\<rparr> = ?rhs\<lparr>NTMap\<rparr>"
              proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
                fix b' assume "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
                with \<HH>(1) f assms(3) show "?lhs\<lparr>NTMap\<rparr>\<lparr>b'\<rparr> = ?rhs\<lparr>NTMap\<rparr>\<lparr>b'\<rparr>"
                  by (*slow*)
                    (
                      cs_concl
                        cs_simp: cat_cs_simps cat_op_simps 
                        cs_intro: cat_cs_intros
                    )
              qed (cs_concl cs_intro: cat_cs_intros)

            qed simp_all

            from 
              assms(3) f \<HH>(1) prems \<alpha>\<beta> 
              (*speedup*)
              Ran.HomCod.category_axioms 
              FUNCT_\<CC>.category_axioms
              FUNCT_\<BB>.category_axioms
              AG.is_functor_axioms
              Ran.is_functor_axioms
              Hom_f.is_ntcf_axioms
            show
              "(?umap_fo b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?cf_hom_lhs)\<lparr>ArrVal\<rparr>\<lparr>\<HH>\<rparr> =
                (?cf_hom_rhs \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?umap_fo a)\<lparr>ArrVal\<rparr>\<lparr>\<HH>\<rparr>"
                by (subst (1 2) \<HH>(2)) (*exceptionally slow*)
                (
                  cs_concl
                    cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps
                    cs_intro:
                      cat_cs_intros 
                      cat_prod_cs_intros 
                      cat_FUNCT_cs_intros
                      cat_op_intros
                )

            qed
              (
                use arr_Set_umap_fo_cf_hom_lhs arr_Set_cf_hom_rhs_umap_fo_a in
                  auto
              )

          qed
            (
              use umap_fo_cf_hom_lhs cf_hom_rhs_umap_fo_a in
                \<open>cs_concl cs_simp: cat_cs_simps\<close>
            )+

        qed

        from f assms \<alpha>\<beta> show ?thesis
          by (*slow*)
            (
              cs_concl
                cs_simp: cat_cs_simps cat_Kan_cs_simps cat_FUNCT_cs_simps
                cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
            )

      qed

    qed auto

  qed


  (**main**)

  from L_10_5_\<chi>_is_iso_ntcf[OF \<beta> \<alpha>\<beta> assms] have inv_\<chi>:
    "inv_ntcf (L_10_5_\<chi> \<alpha> \<beta> \<TT> \<KK> c) :
      L_10_5_N \<alpha> \<beta> \<TT> \<KK> c \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o cf_Cone \<alpha> \<beta> ?\<TT>_c\<KK> :
      op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
    by (auto intro: iso_ntcf_is_arr_isomorphism)
 
  define \<phi> where "\<phi> = inv_ntcf (L_10_5_\<chi> \<alpha> \<beta> \<TT> \<KK> c) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<psi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf Y'"
  
  from inv_Y' \<psi> inv_\<chi> have \<phi>: "\<phi> :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(-,?\<GG>c) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o cf_Cone \<alpha> \<beta> ?\<TT>_c\<KK> :
    op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
    unfolding \<phi>_def by (cs_concl cs_intro: cat_cs_intros)

  interpret \<phi>: is_iso_ntcf
    \<beta> \<open>op_cat \<AA>\<close> \<open>cat_Set \<beta>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(-,?\<GG>c)\<close> \<open>cf_Cone \<alpha> \<beta> ?\<TT>_c\<KK>\<close> \<phi>
    by (rule \<phi>)

  let ?\<phi>_\<GG>c_CId = \<open>\<phi>\<lparr>NTMap\<rparr>\<lparr>?\<GG>c\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>?\<GG>c\<rparr>\<rparr>\<close>
  let ?ntcf_\<phi>_\<GG>c_CId = \<open>ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> ?\<phi>_\<GG>c_CId\<close>

  from AG.vempty_is_zet assms(3) have \<Delta>: "?\<Delta> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> ?c\<KK>_\<AA>"
    by
      (
        cs_concl
          cs_simp: cat_comma_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_comma_cs_intros
      )
  from assms(3) have \<GG>c: "?\<GG>c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    by (cs_concl cs_intro: cat_cs_intros)
  from AG.vempty_is_zet have \<TT>_c\<KK>: "cf_map (?\<TT>_c\<KK>) \<in>\<^sub>\<circ> ?c\<KK>_\<AA>\<lparr>Obj\<rparr>"
    by
      (
        cs_concl
          cs_simp: cat_Funct_components(1) 
          cs_intro: cat_small_cs_intros cat_FUNCT_cs_intros
      )

  from
    \<phi>.ntcf_NTMap_is_arr[unfolded cat_op_simps, OF \<GG>c]
    assms(3)
    AG.vempty_is_zet
    \<beta>.vempty_is_zet
    \<alpha>\<beta>
  have \<phi>_\<GG>c: "\<phi>\<lparr>NTMap\<rparr>\<lparr>?\<GG>c\<rparr> :
    Hom \<AA> ?\<GG>c?\<GG>c \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> 
    Hom ?c\<KK>_\<AA> (cf_map (?cf_c\<KK>_\<AA> ?\<GG>c)) (cf_map ?\<TT>_c\<KK>)"
    by (*very slow*)
      (
        cs_prems
          cs_simp:
            cat_cs_simps
            cat_Kan_cs_simps
            cat_comma_cs_simps 
            cat_op_simps 
            cat_Funct_components(1) 
          cs_intro: 
            cat_small_cs_intros
            cat_Kan_cs_intros
            cat_comma_cs_intros 
            cat_cs_intros 
            cat_FUNCT_cs_intros 
            cat_op_intros 
            category.cat_category_if_ge_Limit[where \<alpha>=\<alpha> and \<beta>=\<beta>]
            is_functor.cf_is_functor_if_ge_Limit[where \<alpha>=\<alpha> and \<beta>=\<beta>]
      )

  with assms(3) have \<phi>_\<GG>c_CId: 
    "?\<phi>_\<GG>c_CId : cf_map (?cf_c\<KK>_\<AA> ?\<GG>c) \<mapsto>\<^bsub>?c\<KK>_\<AA>\<^esub> cf_map ?\<TT>_c\<KK>"
    by (cs_concl cs_intro: cat_cs_intros)
  have ntcf_arrow_\<phi>_\<GG>c_CId: "ntcf_arrow ?ntcf_\<phi>_\<GG>c_CId = ?\<phi>_\<GG>c_CId"
    by (rule cat_Funct_is_arrD(2)[OF \<phi>_\<GG>c_CId, symmetric])
  have ua: "universal_arrow_fo ?\<Delta> (cf_map (?\<TT>_c\<KK>)) ?\<GG>c ?\<phi>_\<GG>c_CId"
    by 
      (
        rule is_functor.cf_universal_arrow_fo_if_is_iso_ntcf_if_ge_Limit[
          OF \<Delta> \<beta> \<alpha>\<beta> \<GG>c \<TT>_c\<KK> \<phi>[unfolded cf_Cone_def cat_cs_simps]
          ]
      )
  moreover have ntcf_\<phi>_\<GG>c_CId: 
    "?ntcf_\<phi>_\<GG>c_CId : ?\<GG>c <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e ?\<TT>_c\<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  proof(intro is_cat_coneI)
    from cat_Funct_is_arrD(1)[OF \<phi>_\<GG>c_CId] assms(3) AG.vempty_is_zet show 
      "ntcf_of_ntcf_arrow (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> ?\<phi>_\<GG>c_CId :
        ?cf_c\<KK>_\<AA> ?\<GG>c \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m ?\<TT>_c\<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
      by
        (
          cs_prems
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
  qed (rule \<GG>c)
  ultimately have "?ntcf_\<phi>_\<GG>c_CId : ?\<GG>c <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m ?\<TT>_c\<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    by 
      (
        intro is_cat_limitI[
          where u=\<open>?ntcf_\<phi>_\<GG>c_CId\<close>, unfolded ntcf_arrow_\<phi>_\<GG>c_CId
          ]
      )
  then show ?thesis using that by auto

qed



subsection\<open>The limit for the pointwise Kan extension\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Theorem 3 in Chapter X-5 in \cite{mac_lane_categories_2010}.\<close>

definition the_pw_cat_rKe_limit :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "the_pw_cat_rKe_limit \<alpha> \<KK> \<TT> \<GG> c =
    [
      \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>,
      (
        SOME UA.
          UA : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<TT>\<lparr>HomCod\<rparr>
      )
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma the_pw_cat_rKe_limit_components:
  shows "the_pw_cat_rKe_limit \<alpha> \<KK> \<TT> \<GG> c\<lparr>UObj\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
    and "the_pw_cat_rKe_limit \<alpha> \<KK> \<TT> \<GG> c\<lparr>UArr\<rparr> = 
      (
        SOME UA.
          UA : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<TT>\<lparr>HomCod\<rparr>
      )"
  unfolding the_pw_cat_rKe_limit_def ua_field_simps
  by (simp_all add: nat_omega_simps)

context is_functor
begin

lemmas the_pw_cat_rKe_limit_components' = 
  the_pw_cat_rKe_limit_components[where \<TT>=\<FF>, unfolded cat_cs_simps]

end


subsubsection\<open>The limit for the pointwise Kan extension is a limit\<close>

lemma (in is_cat_pw_rKe) cat_pw_rKe_the_pw_cat_rKe_limit_is_limit:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "the_pw_cat_rKe_limit \<alpha> \<KK> \<TT> \<GG> c\<lparr>UArr\<rparr> :
    the_pw_cat_rKe_limit \<alpha> \<KK> \<TT> \<GG> c\<lparr>UObj\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> :
    c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  from cat_pw_rKe_ex_cat_limit[OF assms] obtain UA 
    where UA: "UA : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    by auto
  show ?thesis
    unfolding the_pw_cat_rKe_limit_components
    by (rule someI2, unfold cat_cs_simps, rule UA)
qed

lemma (in is_cat_pw_rKe) cat_pw_rKe_the_ntcf_rKe_is_cat_rKe: 
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "the_ntcf_rKe \<alpha> \<TT> \<KK> (the_pw_cat_rKe_limit \<alpha> \<KK> \<TT> \<GG>) :
    the_cf_rKe \<alpha> \<TT> \<KK> (the_pw_cat_rKe_limit \<alpha> \<KK> \<TT> \<GG>) \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT> :
    \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C \<AA>"
proof-
  interpret \<TT>: is_tm_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))
  show "the_ntcf_rKe \<alpha> \<TT> \<KK> (the_pw_cat_rKe_limit \<alpha> \<KK> \<TT> \<GG>) :
    the_cf_rKe \<alpha> \<TT> \<KK> (the_pw_cat_rKe_limit \<alpha> \<KK> \<TT> \<GG>) \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT> :
    \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C \<AA>"
    by
      (
        rule
          the_ntcf_rKe_is_cat_rKe
            [
              OF
                assms(1)
                ntcf_rKe.NTCod.is_functor_axioms 
                cat_pw_rKe_the_pw_cat_rKe_limit_is_limit[OF assms]
            ]
      )
qed

text\<open>\newpage\<close>

end