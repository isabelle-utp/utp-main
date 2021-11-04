(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Simple Kan extensions\<close>
theory CZH_UCAT_Kan
  imports 
    CZH_Elementary_Categories.CZH_ECAT_Comma
    CZH_UCAT_Limit
    CZH_UCAT_Adjoints
begin



subsection\<open>Background\<close>

named_theorems ua_field_simps

definition UObj :: V where [ua_field_simps]: "UObj = 0"
definition UArr :: V where [ua_field_simps]: "UArr = 1\<^sub>\<nat>"

named_theorems cat_Kan_cs_simps
named_theorems cat_Kan_cs_intros



subsection\<open>Kan extension\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter X-3 in \cite{mac_lane_categories_2010}.\<close>

locale is_cat_rKe = 
  AG: is_functor \<alpha> \<BB> \<CC> \<KK> + 
  Ran: is_functor \<alpha> \<CC> \<AA> \<GG> +
  ntcf_rKe: is_ntcf \<alpha> \<BB> \<AA> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<KK>\<close> \<TT> \<epsilon>
  for \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT> \<GG> \<epsilon> +
  assumes cat_rKe_ua_fo:
    "universal_arrow_fo
      (exp_cat_cf \<alpha> \<AA> \<KK>)
      (cf_map \<TT>)
      (cf_map \<GG>)
      (ntcf_arrow \<epsilon>)"

syntax "_is_cat_rKe" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<circ>\<^sub>C\<^sub>F _ \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<index> _ :/ _ \<mapsto>\<^sub>C _ \<mapsto>\<^sub>C _)\<close> [51, 51, 51, 51, 51, 51, 51] 51)
translations "\<epsilon> : \<GG> \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT> : \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C \<AA>" \<rightleftharpoons> 
  "CONST is_cat_rKe \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT> \<GG> \<epsilon>"

locale is_cat_lKe =
  AG: is_functor \<alpha> \<BB> \<CC> \<KK> +
  Lan: is_functor \<alpha> \<CC> \<AA> \<FF> +
  ntcf_lKe: is_ntcf \<alpha> \<BB> \<AA> \<TT> \<open>\<FF> \<circ>\<^sub>C\<^sub>F \<KK>\<close> \<eta>
  for \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT> \<FF> \<eta> +
  assumes cat_lKe_ua_fo:
    "universal_arrow_fo
      (exp_cat_cf \<alpha> (op_cat \<AA>) (op_cf \<KK>))
      (cf_map \<TT>)
      (cf_map \<FF>)
      (ntcf_arrow (op_ntcf \<eta>))"

syntax "_is_cat_lKe" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<index> _ \<circ>\<^sub>C\<^sub>F _ :/ _ \<mapsto>\<^sub>C _ \<mapsto>\<^sub>C _)\<close> [51, 51, 51, 51, 51, 51, 51] 51)
translations "\<eta> : \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<FF> \<circ>\<^sub>C\<^sub>F \<KK> : \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C \<AA>" \<rightleftharpoons> 
  "CONST is_cat_lKe \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT> \<FF> \<eta>"


text\<open>Rules.\<close>

lemma (in is_cat_rKe) is_cat_rKe_axioms'[cat_Kan_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
    and "\<GG>' = \<GG>"
    and "\<KK>' = \<KK>"
    and "\<TT>' = \<TT>"
    and "\<BB>' = \<BB>"
    and "\<AA>' = \<AA>"
    and "\<CC>' = \<CC>"
  shows "\<epsilon> : \<GG>' \<circ>\<^sub>C\<^sub>F \<KK>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>'\<^esub> \<TT>' : \<BB>' \<mapsto>\<^sub>C \<CC>' \<mapsto>\<^sub>C \<AA>'"
  unfolding assms by (rule is_cat_rKe_axioms)

mk_ide rf is_cat_rKe_def[unfolded is_cat_rKe_axioms_def]
  |intro is_cat_rKeI|
  |dest is_cat_rKeD[dest]|
  |elim is_cat_rKeE[elim]|

lemmas [cat_Kan_cs_intros] = is_cat_rKeD(1-3)

lemma (in is_cat_lKe) is_cat_lKe_axioms'[cat_Kan_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
    and "\<FF>' = \<FF>"
    and "\<KK>' = \<KK>"
    and "\<TT>' = \<TT>"
    and "\<BB>' = \<BB>"
    and "\<AA>' = \<AA>"
    and "\<CC>' = \<CC>"
  shows "\<eta> : \<TT>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>' : \<BB>' \<mapsto>\<^sub>C \<CC>' \<mapsto>\<^sub>C \<AA>'"
  unfolding assms by (rule is_cat_lKe_axioms)

mk_ide rf is_cat_lKe_def[unfolded is_cat_lKe_axioms_def]
  |intro is_cat_lKeI|
  |dest is_cat_lKeD[dest]|
  |elim is_cat_lKeE[elim]|

lemmas [cat_Kan_cs_intros] = is_cat_lKeD(1-3)


text\<open>Duality.\<close>

lemma (in is_cat_rKe) is_cat_lKe_op:
  "op_ntcf \<epsilon> :
    op_cf \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> op_cf \<GG> \<circ>\<^sub>C\<^sub>F op_cf \<KK> :
    op_cat \<BB> \<mapsto>\<^sub>C op_cat \<CC> \<mapsto>\<^sub>C op_cat \<AA>"
  by (intro is_cat_lKeI, unfold cat_op_simps; (intro cat_rKe_ua_fo)?)
    (cs_concl cs_simp: cat_op_simps cs_intro: cat_op_intros)+

lemma (in is_cat_rKe) is_cat_lKe_op'[cat_op_intros]:
  assumes "\<TT>' = op_cf \<TT>"
    and "\<GG>' = op_cf \<GG>"
    and "\<KK>' = op_cf \<KK>"
    and "\<BB>' = op_cat \<BB>"
    and "\<AA>' = op_cat \<AA>"
    and "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<epsilon> : \<TT>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<GG>' \<circ>\<^sub>C\<^sub>F \<KK>' : \<BB>' \<mapsto>\<^sub>C \<CC>' \<mapsto>\<^sub>C \<AA>'"
  unfolding assms by (rule is_cat_lKe_op)

lemmas [cat_op_intros] = is_cat_rKe.is_cat_lKe_op'

lemma (in is_cat_lKe) is_cat_rKe_op:
  "op_ntcf \<eta> :
    op_cf \<FF> \<circ>\<^sub>C\<^sub>F op_cf \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> op_cf \<TT> :
    op_cat \<BB> \<mapsto>\<^sub>C op_cat \<CC> \<mapsto>\<^sub>C op_cat \<AA>"
  by (intro is_cat_rKeI, unfold cat_op_simps; (intro cat_lKe_ua_fo)?)
    (cs_concl cs_simp: cat_op_simps cs_intro: cat_op_intros)+

lemma (in is_cat_lKe) is_cat_lKe_op'[cat_op_intros]:
  assumes "\<TT>' = op_cf \<TT>"
    and "\<FF>' = op_cf \<FF>"
    and "\<KK>' = op_cf \<KK>"
    and "\<BB>' = op_cat \<BB>"
    and "\<AA>' = op_cat \<AA>"
    and "\<CC>' = op_cat \<CC>"
  shows "op_ntcf \<eta> : \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT>' : \<BB>' \<mapsto>\<^sub>C \<CC>' \<mapsto>\<^sub>C \<AA>'"
  unfolding assms by (rule is_cat_rKe_op)

lemmas [cat_op_intros] = is_cat_lKe.is_cat_lKe_op'


text\<open>Elementary properties.\<close>

lemma (in is_cat_rKe) cat_rKe_exp_cat_cf_cat_FUNCT_is_arr:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "exp_cat_cf \<alpha> \<AA> \<KK> : cat_FUNCT \<alpha> \<CC> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<BB> \<AA>"
  by 
    ( 
      rule exp_cat_cf_is_tiny_functor[
        OF assms Ran.HomCod.category_axioms AG.is_functor_axioms
        ]
    )

lemma (in is_cat_lKe) cat_lKe_exp_cat_cf_cat_FUNCT_is_arr:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "exp_cat_cf \<alpha> \<AA> \<KK> : cat_FUNCT \<alpha> \<CC> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<BB> \<AA>"
  by 
    ( 
      rule exp_cat_cf_is_tiny_functor[
        OF assms Lan.HomCod.category_axioms AG.is_functor_axioms
        ]
    )


subsubsection\<open>Universal property\<close>


text\<open>
See Chapter X-3 in \cite{mac_lane_categories_2010} and 
\cite{noauthor_wikipedia_2001}\footnote{
\url{https://en.wikipedia.org/wiki/Kan_extension}
}.
\<close>

lemma is_cat_rKeI':
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<epsilon> : \<GG> \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<And>\<GG>' \<epsilon>'.
      \<lbrakk> \<GG>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>; \<epsilon>' : \<GG>' \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> \<rbrakk> \<Longrightarrow>
        \<exists>!\<sigma>. \<sigma> : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> \<and> \<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)" 
  shows "\<epsilon> : \<GG> \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT> : \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C \<AA>"
proof-
  interpret \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC> \<AA> \<GG> by (rule assms(2))
  interpret \<epsilon>: is_ntcf \<alpha> \<BB> \<AA> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<KK>\<close> \<TT> \<epsilon> by (rule assms(3))
  let ?\<AA>\<KK> = \<open>exp_cat_cf \<alpha> \<AA> \<KK>\<close>
    and ?\<TT> = \<open>cf_map \<TT>\<close>
    and ?\<GG> = \<open>cf_map \<GG>\<close>
  show ?thesis
  proof(intro is_cat_rKeI is_functor.universal_arrow_foI assms)
    define \<beta> where "\<beta> = \<alpha> + \<omega>"
    have "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
      by (simp_all add: \<beta>_def \<KK>.\<Z>_Limit_\<alpha>\<omega> \<KK>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<KK>.\<Z>_\<alpha>_\<alpha>\<omega>)
    then interpret \<beta>: \<Z> \<beta> by simp 
    show "?\<AA>\<KK> : cat_FUNCT \<alpha> \<CC> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<BB> \<AA>"
      by 
        ( 
          cs_concl cs_intro: 
            cat_small_cs_intros 
            exp_cat_cf_is_tiny_functor[
              OF \<beta>.\<Z>_axioms \<alpha>\<beta> \<GG>.HomCod.category_axioms assms(1)
              ]
        )
    from \<alpha>\<beta> assms(2) show "cf_map \<GG> \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<CC> \<AA>\<lparr>Obj\<rparr>"
      unfolding cat_FUNCT_components
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_FUNCT_cs_intros)
    from assms(1-3) show "ntcf_arrow \<epsilon> :
      ?\<AA>\<KK>\<lparr>ObjMap\<rparr>\<lparr>?\<GG>\<rparr> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<BB> \<AA>\<^esub> ?\<TT>"
      by 
        (
          cs_concl 
            cs_simp: cat_Kan_cs_simps cat_FUNCT_cs_simps cat_FUNCT_components(1) 
            cs_intro: cat_FUNCT_cs_intros
        )
    fix \<FF>' \<epsilon>' assume prems: 
      "\<FF>' \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<CC> \<AA>\<lparr>Obj\<rparr>"
      "\<epsilon>' : ?\<AA>\<KK>\<lparr>ObjMap\<rparr>\<lparr>\<FF>'\<rparr> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<BB> \<AA>\<^esub> ?\<TT>"
    from prems(1) have "\<FF>' \<in>\<^sub>\<circ> cf_maps \<alpha> \<CC> \<AA>"  
      unfolding cat_FUNCT_components(1) by simp
    then obtain \<FF> where \<FF>'_def: "\<FF>' = cf_map \<FF>" and \<FF>: "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
      by clarsimp
    note \<epsilon>' = cat_FUNCT_is_arrD[OF prems(2)]
    from \<epsilon>'(1) \<FF> have \<epsilon>'_is_ntcf: 
      "ntcf_of_ntcf_arrow \<BB> \<AA> \<epsilon>' : \<FF> \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by 
        ( 
          cs_prems 
            cs_simp: \<FF>'_def cat_Kan_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    from assms(4)[OF \<FF> \<epsilon>'_is_ntcf] obtain \<sigma>
      where \<sigma>: "\<sigma> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
        and \<epsilon>'_def': "ntcf_of_ntcf_arrow \<BB> \<AA> \<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)"
        and unique_\<sigma>: "\<And>\<sigma>'. 
          \<lbrakk> 
            \<sigma>' : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>;
            ntcf_of_ntcf_arrow \<BB> \<AA> \<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>) 
          \<rbrakk> \<Longrightarrow> \<sigma>' = \<sigma>"
      by metis
    show "\<exists>!f'.
      f' : \<FF>' \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> \<AA>\<^esub> ?\<GG> \<and>
      \<epsilon>' = umap_fo ?\<AA>\<KK> ?\<TT> ?\<GG> (ntcf_arrow \<epsilon>) \<FF>'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    proof(intro ex1I conjI; (elim conjE)?, unfold \<FF>'_def)
      from \<sigma> show "ntcf_arrow \<sigma> : cf_map \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> \<AA>\<^esub> ?\<GG>"
        by (cs_concl cs_intro: cat_FUNCT_cs_intros)
      from \<alpha>\<beta> assms(1-3) \<sigma> \<epsilon>'(1) show 
        "\<epsilon>' = umap_fo
          ?\<AA>\<KK> ?\<TT> ?\<GG> (ntcf_arrow \<epsilon>) (cf_map \<FF>)\<lparr>ArrVal\<rparr>\<lparr>ntcf_arrow \<sigma>\<rparr>"
        by (subst \<epsilon>')
          (
            cs_concl 
              cs_simp: 
                \<epsilon>'_def'[symmetric] cat_cs_simps cat_FUNCT_cs_simps cat_Kan_cs_simps 
              cs_intro: 
                cat_small_cs_intros 
                cat_cs_intros 
                cat_Kan_cs_intros
                cat_FUNCT_cs_intros
          )
      fix \<sigma>' assume prems:
        "\<sigma>' : cf_map \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> \<AA>\<^esub> ?\<GG>"
        "\<epsilon>' = umap_fo ?\<AA>\<KK> ?\<TT> ?\<GG> (ntcf_arrow \<epsilon>) (cf_map \<FF>)\<lparr>ArrVal\<rparr>\<lparr>\<sigma>'\<rparr>"
      note \<sigma>' = cat_FUNCT_is_arrD[OF prems(1)]
      from \<sigma>'(1) \<FF> have "ntcf_of_ntcf_arrow \<CC> \<AA> \<sigma>' : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        by (cs_prems cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)
      moreover from prems(2) prems(1) \<alpha>\<beta> assms(1-3) this \<epsilon>'(1) have 
        "ntcf_of_ntcf_arrow \<BB> \<AA> \<epsilon>' =
          \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (ntcf_of_ntcf_arrow \<CC> \<AA> \<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)"
        by (subst (asm) \<epsilon>'(2))
          (
            cs_prems 
              cs_simp: cat_Kan_cs_simps cat_FUNCT_cs_simps cat_cs_simps 
              cs_intro: 
                cat_Kan_cs_intros
                cat_small_cs_intros
                cat_cs_intros
                cat_FUNCT_cs_intros
          )
      ultimately have \<sigma>_def: "\<sigma> = ntcf_of_ntcf_arrow \<CC> \<AA> \<sigma>'" 
        by (rule unique_\<sigma>[symmetric])
      show "\<sigma>' = ntcf_arrow \<sigma>"
        by (subst \<sigma>'(2), use nothing in \<open>subst \<sigma>_def\<close>)
          (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    qed
  qed
qed

lemma is_cat_lKeI':
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<eta> : \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F \<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<And>\<FF>' \<eta>'.
      \<lbrakk> \<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>; \<eta>' : \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' \<circ>\<^sub>C\<^sub>F \<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> \<rbrakk> \<Longrightarrow>
        \<exists>!\<sigma>. \<sigma> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> \<and> \<eta>' = (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>" 
  shows "\<eta> : \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<FF> \<circ>\<^sub>C\<^sub>F \<KK> : \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C \<AA>"
proof-
  interpret \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<FF>: is_functor \<alpha> \<CC> \<AA> \<FF> by (rule assms(2))
  interpret \<eta>: is_ntcf \<alpha> \<BB> \<AA> \<TT> \<open>\<FF> \<circ>\<^sub>C\<^sub>F \<KK>\<close> \<eta> by (rule assms(3))
  have 
    "\<exists>!\<sigma>.
      \<sigma> : \<GG>' \<mapsto>\<^sub>C\<^sub>F op_cf \<FF> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<AA> \<and>
      \<eta>' = op_ntcf \<eta> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F op_cf \<KK>)"
    if "\<GG>' : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<AA>"
      and "\<eta>' : \<GG>' \<circ>\<^sub>C\<^sub>F op_cf \<KK> \<mapsto>\<^sub>C\<^sub>F op_cf \<TT> : op_cat \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<AA>"
    for \<GG>' \<eta>'
  proof-
    interpret \<GG>': is_functor \<alpha> \<open>op_cat \<CC>\<close> \<open>op_cat \<AA>\<close> \<GG>' by (rule that(1))
    interpret \<eta>': 
      is_ntcf \<alpha> \<open>op_cat \<BB>\<close> \<open>op_cat \<AA>\<close> \<open>\<GG>' \<circ>\<^sub>C\<^sub>F op_cf \<KK>\<close> \<open>op_cf \<TT>\<close> \<eta>'
      by (rule that(2))
    from assms(4)[
        OF is_functor.is_functor_op[OF that(1), unfolded cat_op_simps],
        OF is_ntcf.is_ntcf_op[OF that(2), unfolded cat_op_simps]
        ]
    obtain \<sigma> where \<sigma>: "\<sigma> : \<FF> \<mapsto>\<^sub>C\<^sub>F op_cf \<GG>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
      and op_\<eta>'_def: "op_ntcf \<eta>' = \<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>"
      and unique_\<sigma>':
        "\<lbrakk>
          \<sigma>' : \<FF> \<mapsto>\<^sub>C\<^sub>F op_cf \<GG>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>;
          op_ntcf \<eta>' = \<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>
         \<rbrakk> \<Longrightarrow> \<sigma>' = \<sigma>"
      for \<sigma>'
      by metis
    interpret \<sigma>: is_ntcf \<alpha> \<CC> \<AA> \<FF> \<open>op_cf \<GG>'\<close> \<sigma> by (rule \<sigma>)
    show ?thesis
    proof(intro ex1I conjI; (elim conjE)?)
      show "op_ntcf \<sigma> : \<GG>' \<mapsto>\<^sub>C\<^sub>F op_cf \<FF> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<AA>"
        by (rule \<sigma>.is_ntcf_op[unfolded cat_op_simps])
      from op_\<eta>'_def have "op_ntcf (op_ntcf \<eta>') = op_ntcf (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>)"
        by simp
      from this \<sigma> assms(1-3) show \<eta>'_def:
        "\<eta>' = op_ntcf \<eta> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (op_ntcf \<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F op_cf \<KK>)"
        by (cs_prems cs_simp: cat_op_simps cs_intro: cat_cs_intros)
      fix \<sigma>' assume prems:
        "\<sigma>' : \<GG>' \<mapsto>\<^sub>C\<^sub>F op_cf \<FF> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<AA>"
        "\<eta>' = op_ntcf \<eta> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F op_cf \<KK>)"
      interpret \<sigma>': is_ntcf \<alpha> \<open>op_cat \<CC>\<close> \<open>op_cat \<AA>\<close> \<GG>' \<open>op_cf \<FF>\<close> \<sigma>' 
        by (rule prems(1))
      from prems(2) have 
        "op_ntcf \<eta>' = op_ntcf (op_ntcf \<eta> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F op_cf \<KK>))"
        by simp
      also have "\<dots> = op_ntcf \<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>"   
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_op_simps
              cs_intro: cat_cs_intros cat_op_intros
          )
      finally have "op_ntcf \<eta>' = op_ntcf \<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>" by simp
      from unique_\<sigma>'[OF \<sigma>'.is_ntcf_op[unfolded cat_op_simps] this] show 
        "\<sigma>' = op_ntcf \<sigma>" 
        by (auto simp: cat_op_simps)
    qed
  qed
  from 
    is_cat_rKeI'
      [
        OF \<KK>.is_functor_op \<FF>.is_functor_op \<eta>.is_ntcf_op[unfolded cat_op_simps], 
        unfolded cat_op_simps, 
        OF this
      ]
  interpret \<eta>: is_cat_rKe 
    \<alpha> 
    \<open>op_cat \<BB>\<close> 
    \<open>op_cat \<CC>\<close>
    \<open>op_cat \<AA>\<close> 
    \<open>op_cf \<KK>\<close> 
    \<open>op_cf \<TT>\<close> 
    \<open>op_cf \<FF>\<close> 
    \<open>op_ntcf \<eta>\<close>
    by simp
  show "\<eta> : \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<FF> \<circ>\<^sub>C\<^sub>F \<KK> : \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C \<AA>"
    by (rule \<eta>.is_cat_lKe_op[unfolded cat_op_simps])
qed

lemma (in is_cat_rKe) cat_rKe_unique:
  assumes "\<GG>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" and "\<epsilon>' : \<GG>' \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "\<exists>!\<sigma>. \<sigma> : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> \<and> \<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)" 
proof-

  interpret \<GG>': is_functor \<alpha> \<CC> \<AA> \<GG>' by (rule assms(1))
  interpret \<epsilon>': is_ntcf \<alpha> \<BB> \<AA> \<open>\<GG>' \<circ>\<^sub>C\<^sub>F \<KK>\<close> \<TT> \<epsilon>' by (rule assms(2))

  let ?\<TT> = \<open>cf_map \<TT>\<close>
    and ?\<GG> = \<open>cf_map \<GG>\<close>
    and ?\<GG>' = \<open>cf_map \<GG>'\<close>
    and ?\<epsilon> = \<open>ntcf_arrow \<epsilon>\<close>
    and ?\<epsilon>' = \<open>ntcf_arrow \<epsilon>'\<close>

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    by (simp_all add: \<beta>_def AG.\<Z>_Limit_\<alpha>\<omega> AG.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def AG.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp
  
  interpret \<AA>\<KK>: is_tiny_functor 
    \<beta> \<open>cat_FUNCT \<alpha> \<CC> \<AA>\<close> \<open>cat_FUNCT \<alpha> \<BB> \<AA>\<close> \<open>exp_cat_cf \<alpha> \<AA> \<KK>\<close>
    by (rule cat_rKe_exp_cat_cf_cat_FUNCT_is_arr[OF \<beta>.\<Z>_axioms \<alpha>\<beta>])

  from assms(1) have \<GG>': "?\<GG>' \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<CC> \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_FUNCT_components(1) cs_intro: cat_FUNCT_cs_intros)
  with assms(2) have
    "?\<epsilon>' : exp_cat_cf \<alpha> \<AA> \<KK>\<lparr>ObjMap\<rparr>\<lparr>?\<GG>'\<rparr> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<BB> \<AA>\<^esub> ?\<TT>"
    by 
      ( 
        cs_concl 
          cs_simp: cat_Kan_cs_simps cat_FUNCT_cs_simps 
          cs_intro: cat_cs_intros cat_FUNCT_cs_intros
      )

  from
    is_functor.universal_arrow_foD(3)[
      OF \<AA>\<KK>.is_functor_axioms cat_rKe_ua_fo \<GG>' this
      ]
  obtain f' where f': "f' : cf_map \<GG>' \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> \<AA>\<^esub> cf_map \<GG>"
    and \<epsilon>'_def: "?\<epsilon>' = umap_fo (exp_cat_cf \<alpha> \<AA> \<KK>) ?\<TT> ?\<GG> ?\<epsilon> ?\<GG>'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    and f'_unique: 
      "\<lbrakk> 
        f'' : ?\<GG>' \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> \<AA>\<^esub> ?\<GG>;
        ntcf_arrow \<epsilon>' = umap_fo (exp_cat_cf \<alpha> \<AA> \<KK>) ?\<TT> ?\<GG> ?\<epsilon> ?\<GG>'\<lparr>ArrVal\<rparr>\<lparr>f''\<rparr> 
       \<rbrakk> \<Longrightarrow> f'' = f'"
    for f''
    by metis
  
  show ?thesis
  proof(intro ex1I conjI; (elim conjE)?)
    from \<epsilon>'_def cat_FUNCT_is_arrD(1)[OF f'] show
      "\<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (ntcf_of_ntcf_arrow \<CC> \<AA> f' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)"
      by (subst (asm) cat_FUNCT_is_arrD(2)[OF f']) (*slow*)
        (
          cs_prems 
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_Kan_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    from cat_FUNCT_is_arrD(1)[OF f'] show f'_is_arr:
      "ntcf_of_ntcf_arrow \<CC> \<AA> f' : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by (cs_prems cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)
    fix \<sigma> assume prems: 
      "\<sigma> : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" "\<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)"
    interpret \<sigma>: is_ntcf \<alpha> \<CC> \<AA> \<GG>' \<GG> \<sigma> by (rule prems(1))
    from prems(1) have \<sigma>: 
      "ntcf_arrow \<sigma> : cf_map \<GG>' \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> \<AA>\<^esub> cf_map \<GG>"
      by (cs_concl cs_intro: cat_FUNCT_cs_intros)
    from prems have \<epsilon>'_def: "ntcf_arrow \<epsilon>' =
      umap_fo (exp_cat_cf \<alpha> \<AA> \<KK>) ?\<TT> ?\<GG> ?\<epsilon> ?\<GG>'\<lparr>ArrVal\<rparr>\<lparr>ntcf_arrow \<sigma>\<rparr>"
      by 
        (
          cs_concl
            cs_simp: prems(2) cat_Kan_cs_simps cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    show "\<sigma> = ntcf_of_ntcf_arrow \<CC> \<AA> f'"
      unfolding f'_unique[OF \<sigma> \<epsilon>'_def, symmetric]
      by (cs_concl cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)
  qed

qed

lemma (in is_cat_lKe) cat_lKe_unique:
  assumes "\<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" and "\<eta>' : \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' \<circ>\<^sub>C\<^sub>F \<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "\<exists>!\<sigma>. \<sigma> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> \<and> \<eta>' = (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>" 
proof-

  interpret \<FF>': is_functor \<alpha> \<CC> \<AA> \<FF>' by (rule assms(1))
  interpret \<eta>': is_ntcf \<alpha> \<BB> \<AA> \<TT> \<open>\<FF>' \<circ>\<^sub>C\<^sub>F \<KK>\<close> \<eta>' by (rule assms(2))
  interpret \<eta>: is_cat_rKe 
    \<alpha> \<open>op_cat \<BB>\<close> \<open>op_cat \<CC>\<close> \<open>op_cat \<AA>\<close> \<open>op_cf \<KK>\<close> \<open>op_cf \<TT>\<close> \<open>op_cf \<FF>\<close> \<open>op_ntcf \<eta>\<close>
    by (rule is_cat_rKe_op)

  from \<eta>.cat_rKe_unique[OF \<FF>'.is_functor_op \<eta>'.is_ntcf_op[unfolded cat_op_simps]]
  obtain \<sigma> where \<sigma>: "\<sigma> : op_cf \<FF>' \<mapsto>\<^sub>C\<^sub>F op_cf \<FF> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<AA>"
    and \<eta>'_def: "op_ntcf \<eta>' = op_ntcf \<eta> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F op_cf \<KK>)"
    and unique_\<sigma>': "\<And>\<sigma>'.
      \<lbrakk>
        \<sigma>' : op_cf \<FF>' \<mapsto>\<^sub>C\<^sub>F op_cf \<FF> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<AA>;
        op_ntcf \<eta>' = op_ntcf \<eta> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F op_cf \<KK>) 
      \<rbrakk> \<Longrightarrow> \<sigma>' = \<sigma>"
    by metis

  interpret \<sigma>: is_ntcf \<alpha> \<open>op_cat \<CC>\<close> \<open>op_cat \<AA>\<close> \<open>op_cf \<FF>'\<close> \<open>op_cf \<FF>\<close> \<sigma> 
    by (rule \<sigma>)
  
  show ?thesis
  proof(intro ex1I conjI; (elim conjE)?)
    show "op_ntcf \<sigma> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by (rule \<sigma>.is_ntcf_op[unfolded cat_op_simps])
    have "\<eta>' = op_ntcf (op_ntcf \<eta>')" by (cs_concl cs_simp: cat_op_simps)
    also from \<eta>'_def have "\<dots> = op_ntcf (op_ntcf \<eta> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F op_cf \<KK>))"
      by simp
    also have "\<dots> = op_ntcf \<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>"
      by (cs_concl cs_simp: cat_op_simps cs_intro: cat_cs_intros)
    finally show "\<eta>' = op_ntcf \<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>" by simp
    fix \<sigma>' assume prems: 
      "\<sigma>' : \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      "\<eta>' = \<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>"
    interpret \<sigma>': is_ntcf \<alpha> \<CC> \<AA> \<FF> \<FF>' \<sigma>' by (rule prems(1))
    from prems(2) have "op_ntcf \<eta>' = op_ntcf (\<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>)"
      by simp
    also have "\<dots> = op_ntcf \<eta> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (op_ntcf \<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F op_cf \<KK>)"
      by (cs_concl cs_simp: cat_op_simps cs_intro: cat_cs_intros)
    finally have "op_ntcf \<eta>' = op_ntcf \<eta> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (op_ntcf \<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F op_cf \<KK>)"
      by simp
    from unique_\<sigma>'[OF \<sigma>'.is_ntcf_op this] show "\<sigma>' = op_ntcf \<sigma>"
      by (auto simp: cat_op_simps)
  qed

qed


subsubsection\<open>Further properties\<close>

lemma (in is_cat_rKe) cat_rKe_ntcf_ua_fo_is_iso_ntcf_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows 
    "ntcf_ua_fo \<beta> (exp_cat_cf \<alpha> \<AA> \<KK>) (cf_map \<TT>) (cf_map \<GG>) (ntcf_arrow \<epsilon>) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> \<CC> \<AA>(-,cf_map \<GG>) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> \<BB> \<AA>(-,cf_map \<TT>) \<circ>\<^sub>C\<^sub>F op_cf (exp_cat_cf \<alpha> \<AA> \<KK>) :
      op_cat (cat_FUNCT \<alpha> \<CC> \<AA>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
proof-
  interpret \<AA>_\<KK>: 
    is_tiny_functor \<beta> \<open>cat_FUNCT \<alpha> \<CC> \<AA>\<close> \<open>cat_FUNCT \<alpha> \<BB> \<AA>\<close> \<open>exp_cat_cf \<alpha> \<AA> \<KK>\<close>
    by 
      (
        rule exp_cat_cf_is_tiny_functor[
          OF assms Ran.HomCod.category_axioms AG.is_functor_axioms
          ]
      )
  show ?thesis
    by 
      (
        rule is_functor.cf_ntcf_ua_fo_is_iso_ntcf[
          OF \<AA>_\<KK>.is_functor_axioms cat_rKe_ua_fo
          ]
      )
qed

lemma (in is_cat_lKe) cat_lKe_ntcf_ua_fo_is_iso_ntcf_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  defines "\<AA>\<KK> \<equiv> exp_cat_cf \<alpha> (op_cat \<AA>) (op_cf \<KK>)"
    and "\<AA>\<CC> \<equiv> cat_FUNCT \<alpha> (op_cat \<CC>) (op_cat \<AA>)"
    and "\<AA>\<BB> \<equiv> cat_FUNCT \<alpha> (op_cat \<BB>) (op_cat \<AA>)"
  shows 
    "ntcf_ua_fo \<beta> \<AA>\<KK> (cf_map \<TT>) (cf_map \<FF>) (ntcf_arrow (op_ntcf \<eta>)) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>\<CC>(-,cf_map \<FF>) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>\<BB>(-,cf_map \<TT>) \<circ>\<^sub>C\<^sub>F op_cf \<AA>\<KK> :
      op_cat \<AA>\<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
proof-
  note simps = \<AA>\<CC>_def \<AA>\<BB>_def \<AA>\<KK>_def
  interpret \<AA>_\<KK>: is_tiny_functor \<beta> \<AA>\<CC> \<AA>\<BB> \<AA>\<KK>
    unfolding simps
    by
      (
        rule exp_cat_cf_is_tiny_functor[
          OF assms(1,2) Lan.HomCod.category_op AG.is_functor_op
          ]
      )
  show ?thesis
    unfolding simps
    by 
      (
        rule is_functor.cf_ntcf_ua_fo_is_iso_ntcf[
          OF \<AA>_\<KK>.is_functor_axioms[unfolded simps] cat_lKe_ua_fo
          ]
      )
qed



subsection\<open>The Kan extension\<close>


text\<open>
The following subsection is based on the statement and proof of 
Theorem 1 in Chapter X-3 in \cite{mac_lane_categories_2010}.
In what follows, only the right Kan extension is considered for simplicity.
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition the_cf_rKe :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj =
    [
      (\<lambda>c\<in>\<^sub>\<circ>\<KK>\<lparr>HomCod\<rparr>\<lparr>Obj\<rparr>. lim_Obj c\<lparr>UObj\<rparr>),
      (
        \<lambda>g\<in>\<^sub>\<circ>\<KK>\<lparr>HomCod\<rparr>\<lparr>Arr\<rparr>. THE f.
          f :
            lim_Obj (\<KK>\<lparr>HomCod\<rparr>\<lparr>Dom\<rparr>\<lparr>g\<rparr>)\<lparr>UObj\<rparr> \<mapsto>\<^bsub>\<TT>\<lparr>HomCod\<rparr>\<^esub>
            lim_Obj (\<KK>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>g\<rparr>)\<lparr>UObj\<rparr> \<and>
          lim_Obj (\<KK>\<lparr>HomCod\<rparr>\<lparr>Dom\<rparr>\<lparr>g\<rparr>)\<lparr>UArr\<rparr> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> =
            lim_Obj (\<KK>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>g\<rparr>)\<lparr>UArr\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F 
            ntcf_const ((\<KK>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>g\<rparr>) \<down>\<^sub>C\<^sub>F \<KK>) (\<TT>\<lparr>HomCod\<rparr>) f
      ),
      \<KK>\<lparr>HomCod\<rparr>,
      \<TT>\<lparr>HomCod\<rparr>
    ]\<^sub>\<circ>"

definition the_ntcf_rKe :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "the_ntcf_rKe \<alpha> \<TT> \<KK> lim_Obj =
    [
      (
        \<lambda>c\<in>\<^sub>\<circ>\<TT>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr>.
          lim_Obj (\<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>)\<lparr>UArr\<rparr>\<lparr>NTMap\<rparr>\<lparr>0, c, \<KK>\<lparr>HomCod\<rparr>\<lparr>CId\<rparr>\<lparr>\<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>\<rparr>\<^sub>\<bullet>
      ),
      the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj \<circ>\<^sub>C\<^sub>F \<KK>,
      \<TT>,
      \<TT>\<lparr>HomDom\<rparr>,
      \<TT>\<lparr>HomCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma the_cf_rKe_components:
  shows "the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>ObjMap\<rparr> = 
    (\<lambda>c\<in>\<^sub>\<circ>\<KK>\<lparr>HomCod\<rparr>\<lparr>Obj\<rparr>. lim_Obj c\<lparr>UObj\<rparr>)"
    and "the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>ArrMap\<rparr> =
    (
      \<lambda>g\<in>\<^sub>\<circ>\<KK>\<lparr>HomCod\<rparr>\<lparr>Arr\<rparr>. THE f.
        f :
          lim_Obj (\<KK>\<lparr>HomCod\<rparr>\<lparr>Dom\<rparr>\<lparr>g\<rparr>)\<lparr>UObj\<rparr> \<mapsto>\<^bsub>\<TT>\<lparr>HomCod\<rparr>\<^esub>
          lim_Obj (\<KK>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>g\<rparr>)\<lparr>UObj\<rparr> \<and>
        lim_Obj (\<KK>\<lparr>HomCod\<rparr>\<lparr>Dom\<rparr>\<lparr>g\<rparr>)\<lparr>UArr\<rparr> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> =
          lim_Obj (\<KK>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>g\<rparr>)\<lparr>UArr\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F 
          ntcf_const ((\<KK>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>g\<rparr>) \<down>\<^sub>C\<^sub>F \<KK>) (\<TT>\<lparr>HomCod\<rparr>) f
    )"
    and "the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>HomDom\<rparr> = \<KK>\<lparr>HomCod\<rparr>"
    and "the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>HomCod\<rparr> = \<TT>\<lparr>HomCod\<rparr>"
  unfolding the_cf_rKe_def dghm_field_simps by (simp_all add: nat_omega_simps)

lemma the_ntcf_rKe_components:
  shows "the_ntcf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>NTMap\<rparr> =
      (
        \<lambda>c\<in>\<^sub>\<circ>\<TT>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr>.
          lim_Obj (\<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>)\<lparr>UArr\<rparr>\<lparr>NTMap\<rparr>\<lparr>0, c, \<KK>\<lparr>HomCod\<rparr>\<lparr>CId\<rparr>\<lparr>\<KK>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>\<rparr>\<^sub>\<bullet>
      )"
    and "the_ntcf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>NTDom\<rparr> = the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj \<circ>\<^sub>C\<^sub>F \<KK>"
    and "the_ntcf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>NTCod\<rparr> = \<TT>"
    and "the_ntcf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>NTDGDom\<rparr> = \<TT>\<lparr>HomDom\<rparr>"
    and "the_ntcf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>NTDGCod\<rparr> = \<TT>\<lparr>HomCod\<rparr>"
  unfolding the_ntcf_rKe_def nt_field_simps by (simp_all add: nat_omega_simps)

context
  fixes \<alpha> \<AA> \<BB> \<CC> \<KK> \<TT>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<TT>: "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)
interpretation \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule \<TT>)

lemmas the_cf_rKe_components' = the_cf_rKe_components[
    where \<KK>=\<KK> and \<TT>=\<TT> and \<alpha>=\<alpha>, unfolded \<KK>.cf_HomCod \<TT>.cf_HomCod
    ]

lemmas [cat_Kan_cs_simps] = the_cf_rKe_components'(3,4)

lemmas the_ntcf_rKe_components' = the_ntcf_rKe_components[
    where \<KK>=\<KK> and \<TT>=\<TT> and \<alpha>=\<alpha>, unfolded \<KK>.cf_HomCod \<TT>.cf_HomCod \<TT>.cf_HomDom
    ]

lemmas [cat_Kan_cs_simps] = the_ntcf_rKe_components'(2-5)

end


subsubsection\<open>Functor: object map\<close>

mk_VLambda the_cf_rKe_components(1)
  |vsv the_cf_rKe_ObjMap_vsv[cat_Kan_cs_intros]|

context
  fixes \<alpha> \<AA> \<BB> \<CC> \<KK> \<TT>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<TT>: "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)

mk_VLambda the_cf_rKe_components'(1)[OF \<KK> \<TT>]
  |vdomain the_cf_rKe_ObjMap_vdomain[cat_Kan_cs_simps]|
  |app the_cf_rKe_ObjMap_impl_app[cat_Kan_cs_simps]|

lemma the_cf_rKe_ObjMap_vrange: 
  assumes "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> lim_Obj c\<lparr>UObj\<rparr> \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<R>\<^sub>\<circ> (the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  unfolding the_cf_rKe_components'[OF \<KK> \<TT>]
  by (intro vrange_VLambda_vsubset assms)

end


subsubsection\<open>Functor: arrow map\<close>

mk_VLambda the_cf_rKe_components(2)
  |vsv the_cf_rKe_ArrMap_vsv[cat_Kan_cs_intros]|

context
  fixes \<alpha> \<BB> \<CC> \<KK>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)

mk_VLambda the_cf_rKe_components(2)[where \<alpha>=\<alpha> and \<KK>=\<KK>, unfolded \<KK>.cf_HomCod]
  |vdomain the_cf_rKe_ArrMap_vdomain[cat_Kan_cs_simps]|

context 
  fixes \<AA> \<TT> c c' g
  assumes \<TT>: "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and g: "g : c \<mapsto>\<^bsub>\<CC>\<^esub> c'"
begin

interpretation \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule \<TT>)

lemma g': "g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" using g by auto

mk_VLambda the_cf_rKe_components(2)[
    where \<alpha>=\<alpha> and \<KK>=\<KK> and \<TT>=\<TT>, unfolded \<KK>.cf_HomCod \<TT>.cf_HomCod
    ]
  |app the_cf_rKe_ArrMap_app_impl'|

lemmas the_cf_rKe_ArrMap_app' = the_cf_rKe_ArrMap_app_impl'[
    OF g', unfolded \<KK>.HomCod.cat_is_arrD[OF g]
    ]

end

end

lemma the_cf_rKe_ArrMap_app_impl:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "g : c \<mapsto>\<^bsub>\<CC>\<^esub> c'"
    and "u : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c' \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "\<exists>!f.
    f : r \<mapsto>\<^bsub>\<AA>\<^esub> r' \<and>
    u \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> = u' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> f"
proof-

  interpret \<KK>: is_tm_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))
  interpret u: is_cat_limit \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> r u
    by (rule assms(4))
  interpret u': is_cat_limit \<alpha> \<open>c' \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> r' u'
    by (rule assms(5))

  have const_r_def:
    "cf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r = cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>"
  proof(rule cf_eqI)
    show const_r: "cf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r : c' \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by (cs_concl cs_intro: cat_cs_intros cat_lim_cs_intros)
    from assms(3) show const_r_g\<KK>: 
      "cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> : c' \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)
    have ObjMap_dom_lhs: "\<D>\<^sub>\<circ> (cf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r\<lparr>ObjMap\<rparr>) = c' \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms(3) have ObjMap_dom_rhs: 
      "\<D>\<^sub>\<circ> ((cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>) = c' \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_comma_cs_intros
        )
    have ArrMap_dom_lhs: "\<D>\<^sub>\<circ> (cf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r\<lparr>ArrMap\<rparr>) = c' \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms(3) have ArrMap_dom_rhs: 
      "\<D>\<^sub>\<circ> ((cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>) = c' \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Arr\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_comma_cs_intros
        )
    show 
      "cf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r\<lparr>ObjMap\<rparr> =
        (cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>"
    proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
      fix A assume prems: "A \<in>\<^sub>\<circ> c' \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
      from prems assms obtain b f 
        where A_def: "A = [0, b, f]\<^sub>\<circ>"
          and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
          and f: "f : c' \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by auto
      from assms(1,3) prems f b show 
        "cf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> =
          (cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>A\<rparr>"
        unfolding A_def
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_comma_cs_simps 
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
    qed (use assms(3) in \<open>cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros\<close>)+
    show
      "cf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r\<lparr>ArrMap\<rparr> =
        (cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>"
    proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
      show "vsv (cf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r\<lparr>ArrMap\<rparr>)"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      from assms(3) show "vsv ((cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>)"
        by (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)
      fix F assume prems: "F \<in>\<^sub>\<circ> c' \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Arr\<rparr>"
      with prems obtain A B where F: "F : A \<mapsto>\<^bsub>c' \<down>\<^sub>C\<^sub>F \<KK>\<^esub> B"
        by (auto intro: is_arrI)
      with assms obtain b f b' f' h'
        where F_def: "F = [[0, b, f]\<^sub>\<circ>, [0, b', f']\<^sub>\<circ>, [0, h']\<^sub>\<circ>]\<^sub>\<circ>"
          and A_def: "A = [0, b, f]\<^sub>\<circ>"
          and B_def: "B = [0, b', f']\<^sub>\<circ>"
          and h': "h' : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
          and f: "f : c' \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
          and f': "f' : c' \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
          and f'_def: "\<KK>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = f'"
        by auto
      from prems assms(3) F g' h' f f' show
        "cf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> =
          (cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> r \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr>"
        unfolding F_def A_def B_def
        by (*slow*)
          (
            cs_concl
              cs_simp: cat_comma_cs_simps cat_cs_simps f'_def[symmetric]
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
    qed simp
  qed simp_all

  have \<TT>c'\<KK>: "\<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> = \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>"
  proof(rule cf_eqI)
    show "\<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c' \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by (cs_concl cs_intro: cat_cs_intros)
    from assms show " \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> : c' \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps 
            cs_intro: cat_comma_cs_intros cat_cs_intros
        )
    have ObjMap_dom_lhs: "\<D>\<^sub>\<circ> ((\<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>) = c' \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms have ObjMap_dom_rhs: 
      "\<D>\<^sub>\<circ> ((\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>) = c' \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
      by
        (
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_comma_cs_intros cat_cs_intros
        )
    show "(\<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr> = (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>"
    proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
      from assms show "vsv ((\<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>)"
        by
          (
            cs_concl
              cs_simp: cat_comma_cs_simps 
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
      from assms show "vsv ((\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>)"
        by (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)
      fix A assume prems: "A \<in>\<^sub>\<circ> c' \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
      from assms(3) prems obtain b f
        where A_def: "A = [0, b, f]\<^sub>\<circ>"
          and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
          and f: "f : c' \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by auto
      from prems assms b f show 
        "(\<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> =
          (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>A\<rparr>"
        unfolding A_def
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_comma_cs_simps
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
    qed simp

    have ArrMap_dom_lhs: "\<D>\<^sub>\<circ> ((\<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>) = c' \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms have ArrMap_dom_rhs:
      "\<D>\<^sub>\<circ> ((\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>) = c' \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Arr\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_comma_cs_intros cat_cs_intros
        )

    show "(\<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr> = (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>"
    proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
      from assms show "vsv ((\<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>)"
        by
          (
            cs_concl 
              cs_simp: cat_comma_cs_simps 
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
      from assms show "vsv ((\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>)"
        by (cs_concl cs_simp: cs_intro: cat_cs_intros cat_comma_cs_intros)

      fix F assume prems: "F \<in>\<^sub>\<circ> c' \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Arr\<rparr>"
      with prems obtain A B where F: "F : A \<mapsto>\<^bsub>c' \<down>\<^sub>C\<^sub>F \<KK>\<^esub> B"
        unfolding cat_comma_cs_simps by (auto intro: is_arrI)
      with assms(3) obtain b f b' f' h'
        where F_def: "F = [[0, b, f]\<^sub>\<circ>, [0, b', f']\<^sub>\<circ>, [0, h']\<^sub>\<circ>]\<^sub>\<circ>"
          and A_def: "A = [0, b, f]\<^sub>\<circ>"
          and B_def: "B = [0, b', f']\<^sub>\<circ>"
          and h': "h' : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
          and f: "f : c' \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
          and f': "f' : c' \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
          and f'_def: "\<KK>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = f'"
        by auto
      from prems assms(3) F g' h' f f' show
        "(\<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> =
          (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> \<circ>\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr>"
        unfolding F_def A_def B_def
        by (*slow*)
          (
            cs_concl
              cs_simp: cat_comma_cs_simps cat_cs_simps f'_def[symmetric]
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
    qed simp
  qed simp_all

  from assms(1-3) have
    "u \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> : r <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c' \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    by (intro is_cat_coneI is_tm_ntcfI')
      (
        cs_concl
          cs_intro:
            cat_cs_intros
            cat_comma_cs_intros
            cat_lim_cs_intros
            cat_small_cs_intros
          cs_simp: const_r_def \<TT>c'\<KK>
      )+
  with u'.cat_lim_unique_cone show
    "\<exists>!G.
      G : r \<mapsto>\<^bsub>\<AA>\<^esub> r' \<and>
      u \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> = u' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> G"
    by simp

qed

lemma the_cf_rKe_ArrMap_app:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "g : c \<mapsto>\<^bsub>\<CC>\<^esub> c'"
    and "lim_Obj c\<lparr>UArr\<rparr> :
      lim_Obj c\<lparr>UObj\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "lim_Obj c'\<lparr>UArr\<rparr> :
      lim_Obj c'\<lparr>UObj\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c' \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> :
    lim_Obj c\<lparr>UObj\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> lim_Obj c'\<lparr>UObj\<rparr>"
    and
      "lim_Obj c\<lparr>UArr\<rparr> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> =
        lim_Obj c'\<lparr>UArr\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
          ntcf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>)"
    and 
      "\<lbrakk>
        f : lim_Obj c\<lparr>UObj\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> lim_Obj c'\<lparr>UObj\<rparr>;
        lim_Obj c\<lparr>UArr\<rparr> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> =
          lim_Obj c'\<lparr>UArr\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> f
       \<rbrakk> \<Longrightarrow> f = the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>"
proof-

  interpret \<KK>: is_tm_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))
  interpret u: is_cat_limit 
    \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>lim_Obj c\<lparr>UObj\<rparr>\<close> \<open>lim_Obj c\<lparr>UArr\<rparr>\<close>
    by (rule assms(4))
  interpret u': is_cat_limit 
    \<alpha> \<open>c' \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>lim_Obj c'\<lparr>UObj\<rparr>\<close> \<open>lim_Obj c'\<lparr>UArr\<rparr>\<close>
    by (rule assms(5))

  from assms(3) have c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and c': "c' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto

  note the_cf_rKe_ArrMap_app_impl' =
    the_cf_rKe_ArrMap_app_impl[OF assms]
  note the_f = theI'[OF the_cf_rKe_ArrMap_app_impl[OF assms]]
  note the_f_is_arr = the_f[THEN conjunct1]
    and the_f_commutes = the_f[THEN conjunct2]

  from assms(3) the_f_is_arr show
    "the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> :
      lim_Obj c\<lparr>UObj\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> lim_Obj c'\<lparr>UObj\<rparr>"
    by (cs_concl cs_simp: the_cf_rKe_ArrMap_app' cs_intro: cat_cs_intros)
  moreover from assms(3) the_f_commutes show
    "lim_Obj c\<lparr>UArr\<rparr> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> =
      lim_Obj c'\<lparr>UArr\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
        ntcf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>)"
    by (cs_concl cs_simp: the_cf_rKe_ArrMap_app' cs_intro: cat_cs_intros)
  ultimately show "f = the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>"
    if "f : lim_Obj c\<lparr>UObj\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> lim_Obj c'\<lparr>UObj\<rparr>"
      and "lim_Obj c\<lparr>UArr\<rparr> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F g \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> =
        lim_Obj c'\<lparr>UArr\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c' \<down>\<^sub>C\<^sub>F \<KK>) \<AA> f"
    by (metis that the_cf_rKe_ArrMap_app_impl')

qed

lemma the_cf_rKe_ArrMap_is_arr'[cat_Kan_cs_intros]:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "g : c \<mapsto>\<^bsub>\<CC>\<^esub> c'"
    and "lim_Obj c\<lparr>UArr\<rparr> :
      lim_Obj c\<lparr>UObj\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "lim_Obj c'\<lparr>UArr\<rparr> :
      lim_Obj c'\<lparr>UObj\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F c' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c' \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "a = lim_Obj c\<lparr>UObj\<rparr>"
    and "b = lim_Obj c'\<lparr>UObj\<rparr>"
  shows "the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
  unfolding assms(6,7) by (rule the_cf_rKe_ArrMap_app[OF assms(1-5)])

lemma lim_Obj_the_cf_rKe_commute:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "lim_Obj a\<lparr>UArr\<rparr> :
      lim_Obj a\<lparr>UObj\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : a \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "lim_Obj b\<lparr>UArr\<rparr> :
      lim_Obj b\<lparr>UObj\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : b \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "[a', b', f']\<^sub>\<circ> \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
  shows  
    "lim_Obj a\<lparr>UArr\<rparr>\<lparr>NTMap\<rparr>\<lparr>a', b', f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr>\<^sub>\<bullet> =
      lim_Obj b\<lparr>UArr\<rparr>\<lparr>NTMap\<rparr>\<lparr>a', b', f'\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub>
        the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>" 
proof-

  interpret \<KK>: is_tm_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))

  note f = \<KK>.HomCod.cat_is_arrD[OF assms(5)]

  interpret lim_a: is_cat_limit
    \<alpha> \<open>a \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>lim_Obj a\<lparr>UObj\<rparr>\<close> \<open>lim_Obj a\<lparr>UArr\<rparr>\<close>
    by (rule assms(3))
  interpret lim_b: is_cat_limit 
    \<alpha> \<open>b \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>lim_Obj b\<lparr>UObj\<rparr>\<close> \<open>lim_Obj b\<lparr>UArr\<rparr>\<close> 
    by (rule assms(4))

  note f_app = the_cf_rKe_ArrMap_app[
      where lim_Obj=lim_Obj, OF assms(1,2,5,3,4)
      ]

  from f_app(2) have lim_a_f\<KK>_NTMap_app:
    "(lim_Obj a\<lparr>UArr\<rparr> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F f \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>NTMap\<rparr>\<lparr>A\<rparr> =
      (
        lim_Obj b\<lparr>UArr\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
        ntcf_const (b \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>)
      )\<lparr>NTMap\<rparr>\<lparr>A\<rparr>"
    if \<open>A \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>\<close> for A
    by simp
  show 
    "lim_Obj a\<lparr>UArr\<rparr>\<lparr>NTMap\<rparr>\<lparr>a', b', f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr>\<^sub>\<bullet> =
      lim_Obj b\<lparr>UArr\<rparr>\<lparr>NTMap\<rparr>\<lparr>a', b', f'\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub>
        the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>" 
  proof-
    from assms(5,6) have a'_def: "a' = 0"
      and b': "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
      and f': "f' : b \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
      by auto
    show 
      "lim_Obj a\<lparr>UArr\<rparr>\<lparr>NTMap\<rparr>\<lparr>a', b', f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr>\<^sub>\<bullet> =
        lim_Obj b\<lparr>UArr\<rparr>\<lparr>NTMap\<rparr>\<lparr>a', b', f'\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub>
          the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      using lim_a_f\<KK>_NTMap_app[OF assms(6)] f' assms(3,4,5,6) 
      unfolding a'_def
      by
        (
          cs_prems
            cs_simp: cat_cs_simps cat_comma_cs_simps cat_Kan_cs_simps
            cs_intro:
              cat_small_cs_intros
              cat_cs_intros
              cat_comma_cs_intros
              cat_Kan_cs_intros
        )      
  qed

qed


subsubsection\<open>Natural transformation: natural transformation map\<close>

mk_VLambda the_ntcf_rKe_components(1)
  |vsv the_ntcf_rKe_NTMap_vsv[cat_Kan_cs_intros]|

context
  fixes \<alpha> \<AA> \<BB> \<CC> \<KK> \<TT>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<TT>: "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)
interpretation \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule \<TT>)

mk_VLambda the_ntcf_rKe_components'(1)[OF \<KK> \<TT>]
  |vdomain the_ntcf_rKe_ObjMap_vdomain[cat_Kan_cs_simps]|
  |app the_ntcf_rKe_ObjMap_impl_app[cat_Kan_cs_simps]|

end


subsubsection\<open>The Kan extension is a Kan extension\<close>

lemma the_cf_rKe_is_functor:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> lim_Obj c\<lparr>UArr\<rparr> :
      lim_Obj c\<lparr>UObj\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-

  let ?UObj = \<open>\<lambda>a. lim_Obj a\<lparr>UObj\<rparr>\<close> 
  let ?UArr = \<open>\<lambda>a. lim_Obj a\<lparr>UArr\<rparr>\<close>
  let ?const_comma = \<open>\<lambda>a b. cf_const (a \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (?UObj b)\<close>
  let ?the_cf_rKe = \<open>the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<close>

  interpret \<KK>: is_tm_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))

  note [cat_lim_cs_intros] = is_cat_cone.cat_cone_obj
  
  show ?thesis
  proof(intro is_functorI')

    show "vfsequence ?the_cf_rKe" unfolding the_cf_rKe_def by simp
    show "vcard ?the_cf_rKe = 4\<^sub>\<nat>" 
      unfolding the_cf_rKe_def by (simp add: nat_omega_simps)
    show "vsv (?the_cf_rKe\<lparr>ObjMap\<rparr>)" by (cs_concl cs_intro: cat_Kan_cs_intros)
    moreover show "\<D>\<^sub>\<circ> (?the_cf_rKe\<lparr>ObjMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros)
    moreover show "\<R>\<^sub>\<circ> (?the_cf_rKe\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    proof
      (
        intro the_cf_rKe_ObjMap_vrange; 
        (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)?
      )
      fix c assume "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
      with assms(3)[OF this] show "?UObj c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_lim_cs_intros)
    qed
    ultimately have [cat_Kan_cs_intros]: 
      "?the_cf_rKe\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" if \<open>c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>\<close> for c
      by (metis that vsubsetE vsv.vsv_value)

    show "?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> :
      ?the_cf_rKe\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?the_cf_rKe\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for a b f
      using assms(2) that
      by 
        (
          cs_concl
            cs_simp: cat_Kan_cs_simps 
            cs_intro: 
              assms(3) cat_small_cs_intros cat_cs_intros cat_Kan_cs_intros
        )
    then have [cat_Kan_cs_intros]: "?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : A \<mapsto>\<^bsub>\<AA>\<^esub> B"
      if "A = ?the_cf_rKe\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" 
        and "B = ?the_cf_rKe\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
      for A B a b f
      by (simp add: that)

    show
      "?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr> =
        ?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> ?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      (is \<open>?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr> = ?the_rKe_g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> ?the_rKe_f\<close>)
      if g_is_arr: "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and f_is_arr: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for b c g a f
    proof-

      let ?ntcf_const_c = \<open>\<lambda>f. ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> f\<close>

      note g = \<KK>.HomCod.cat_is_arrD[OF that(1)]
        and f = \<KK>.HomCod.cat_is_arrD[OF that(2)]
      note lim_a = assms(3)[OF f(2)]
        and lim_b = assms(3)[OF g(2)]
        and lim_c = assms(3)[OF g(3)]
      from that have gf: "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c" 
        by (cs_concl cs_intro: cat_cs_intros)

      interpret lim_a: is_cat_limit
        \<alpha> \<open>a \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>?UObj a\<close> \<open>?UArr a\<close>
        by (rule lim_a)
      interpret lim_c: is_cat_limit
        \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>?UObj c\<close> \<open>?UArr c\<close>
        by (rule lim_c)

      show ?thesis
      proof
        (
          rule sym, 
          rule the_cf_rKe_ArrMap_app(3)[OF assms(1,2) gf lim_a lim_c]
        )

        from assms(1,2) that lim_a lim_b lim_c show 
          "?the_rKe_g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> ?the_rKe_f : ?UObj a \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj c"
          by
            (
              cs_concl
                cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_Kan_cs_intros
            )
      
        show
          "?UArr a \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> = 
            ?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_const_c (?the_rKe_g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> ?the_rKe_f)"
          (
            is 
              \<open>
                ?UArr a \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> =
                  ?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_const_c ?the_rKe_gf
              \<close>
           )
        proof(rule ntcf_eqI)
          from that show 
            "?UArr a \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> :
              cf_const (a \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (?UObj a) \<circ>\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F
              \<TT> \<circ>\<^sub>C\<^sub>F a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> \<circ>\<^sub>C\<^sub>F ((g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>) :
              c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
            by (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)
          have [cat_comma_cs_simps]: 
            "?const_comma a a \<circ>\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> = ?const_comma c a"
          proof(rule cf_eqI)
            from g_is_arr f_is_arr show
              "?const_comma a a \<circ>\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
              by
                (
                  cs_concl
                    cs_simp: cat_comma_cs_simps cat_cs_simps
                    cs_intro: 
                      cat_cs_intros cat_lim_cs_intros cat_comma_cs_intros
                )
            from g_is_arr f_is_arr show "?const_comma c a : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
              by
                (
                  cs_concl
                    cs_simp: cat_comma_cs_simps cat_cs_simps
                    cs_intro: 
                      cat_cs_intros cat_lim_cs_intros cat_comma_cs_intros
                )
            from g_is_arr f_is_arr have ObjMap_dom_lhs:
              "\<D>\<^sub>\<circ> ((?const_comma a a \<circ>\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>) =
                c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
              by
                (
                  cs_concl
                    cs_simp: cat_comma_cs_simps cat_cs_simps 
                    cs_intro: 
                      cat_comma_cs_intros cat_lim_cs_intros cat_cs_intros
                )
            from g_is_arr f_is_arr have ObjMap_dom_rhs:
              "\<D>\<^sub>\<circ> (?const_comma c a\<lparr>ObjMap\<rparr>) = c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
              by (cs_concl cs_simp: cat_comma_cs_simps cat_cs_simps)

            show
              "(?const_comma a a \<circ>\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr> =
                ?const_comma c a\<lparr>ObjMap\<rparr>"
            proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
              from f_is_arr g_is_arr show 
                "vsv ((?const_comma a a \<circ>\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>)"
                by
                  (
                    cs_concl
                      cs_simp: cat_comma_cs_simps cat_cs_simps 
                      cs_intro:
                        cat_cs_intros cat_lim_cs_intros cat_comma_cs_intros
                  )
              fix A assume prems: "A \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
              with g_is_arr obtain b' f' 
                where A_def: "A = [0, b', f']\<^sub>\<circ>"
                  and b': "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
                  and f': "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
                by auto
              from prems b' f' g_is_arr f_is_arr show 
                "(?const_comma a a \<circ>\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> =
                  ?const_comma c a\<lparr>ObjMap\<rparr>\<lparr>A\<rparr>"
                unfolding A_def
                by
                  (
                    cs_concl
                      cs_simp: cat_comma_cs_simps cat_cs_simps 
                      cs_intro:
                        cat_cs_intros cat_lim_cs_intros cat_comma_cs_intros
                  )
            qed (cs_concl cs_intro: cat_cs_intros)

            from g_is_arr f_is_arr have ArrMap_dom_lhs:
              "\<D>\<^sub>\<circ> ((?const_comma a a \<circ>\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>) = 
                c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Arr\<rparr>"
              by
                (
                  cs_concl
                    cs_simp: cat_comma_cs_simps cat_cs_simps 
                    cs_intro: 
                      cat_comma_cs_intros cat_lim_cs_intros cat_cs_intros
                )
            from g_is_arr f_is_arr have ArrMap_dom_rhs:
              "\<D>\<^sub>\<circ> (?const_comma c a\<lparr>ArrMap\<rparr>) = c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Arr\<rparr>"
              by (cs_concl cs_simp: cat_comma_cs_simps cat_cs_simps)

            show 
              "(?const_comma a a \<circ>\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr> =
                ?const_comma c a\<lparr>ArrMap\<rparr>"
            proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
              from f_is_arr g_is_arr show
                "vsv ((?const_comma a a \<circ>\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>)"
                by
                  (
                    cs_concl
                      cs_simp: cat_comma_cs_simps cat_cs_simps
                      cs_intro:
                        cat_cs_intros cat_lim_cs_intros cat_comma_cs_intros
                  )
              fix F assume "F \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Arr\<rparr>"
              then obtain A B where F: "F : A \<mapsto>\<^bsub>c \<down>\<^sub>C\<^sub>F \<KK>\<^esub> B"
                unfolding cat_comma_cs_simps by (auto intro: is_arrI)
              with g_is_arr obtain b' f' b'' f'' h'
                where F_def: "F = [[0, b', f']\<^sub>\<circ>, [0, b'', f'']\<^sub>\<circ>, [0, h']\<^sub>\<circ>]\<^sub>\<circ>"
                  and A_def: "A = [0, b', f']\<^sub>\<circ>"
                  and B_def: "B = [0, b'', f'']\<^sub>\<circ>"
                  and h': "h' : b' \<mapsto>\<^bsub>\<BB>\<^esub> b''"
                  and f': "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
                  and f'': "f'' : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b''\<rparr>"
                  and f''_def: "\<KK>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' = f''"
                by auto
              from F f_is_arr g_is_arr g' h' f' f'' show 
                "(?const_comma a a \<circ>\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> =
                  ?const_comma c a\<lparr>ArrMap\<rparr>\<lparr>F\<rparr>"
                unfolding F_def A_def B_def
                by
                  (
                    cs_concl
                      cs_intro:
                        cat_lim_cs_intros cat_cs_intros cat_comma_cs_intros
                      cs_simp: 
                        cat_cs_simps cat_comma_cs_simps f''_def[symmetric]
                  )
            qed (cs_concl cs_intro: cat_cs_intros)
          qed simp_all

          from that show
            "?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_const_c ?the_rKe_gf :
              cf_const (a \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (?UObj a) \<circ>\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F
              \<TT> \<circ>\<^sub>C\<^sub>F a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> \<circ>\<^sub>C\<^sub>F ((g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>) :
              c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
            by
              (
                cs_concl
                  cs_simp: cat_Kan_cs_simps cat_comma_cs_simps cat_cs_simps 
                  cs_intro: cat_comma_cs_intros cat_Kan_cs_intros cat_cs_intros
              )
          from that have dom_lhs:
            "\<D>\<^sub>\<circ> ((?UArr a \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>NTMap\<rparr>) = c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
            by
              (
                cs_concl
                  cs_intro: cat_cs_intros cat_comma_cs_intros
                  cs_simp: cat_cs_simps cat_comma_cs_simps
              )
          from that have dom_rhs: 
            "\<D>\<^sub>\<circ> ((?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_const_c ?the_rKe_gf)\<lparr>NTMap\<rparr>) = 
              c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
            by
              (
                cs_concl
                  cs_intro: cat_cs_intros cat_Kan_cs_intros cat_comma_cs_intros
                  cs_simp: cat_Kan_cs_simps cat_cs_simps cat_comma_cs_simps
              )
          show 
            "(?UArr a \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>NTMap\<rparr> =
              (?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_const_c ?the_rKe_gf)\<lparr>NTMap\<rparr>"
          proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
            fix A assume prems: "A \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
            with g_is_arr obtain b' f' 
              where A_def: "A = [0, b', f']\<^sub>\<circ>"
                and b': "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
                and f': "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
              by auto
            note \<TT>.HomCod.cat_Comp_assoc[cat_cs_simps del]
              and \<KK>.HomCod.cat_Comp_assoc[cat_cs_simps del]
              and category.cat_Comp_assoc[cat_cs_simps del]
            note [symmetric, cat_cs_simps] =
              lim_Obj_the_cf_rKe_commute[where lim_Obj=lim_Obj]
              \<KK>.HomCod.cat_Comp_assoc  
              \<TT>.HomCod.cat_Comp_assoc
            from assms(1,2) that prems lim_a lim_b lim_c b' f' show
              "(?UArr a \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>NTMap\<rparr>\<lparr>A\<rparr> =
                (?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_const_c ?the_rKe_gf)\<lparr>NTMap\<rparr>\<lparr>A\<rparr>"
              unfolding A_def
              by (*very slow*)
                (
                  cs_concl
                    cs_simp:
                      cat_cs_simps cat_Kan_cs_simps cat_comma_cs_simps 
                    cs_intro: 
                      cat_cs_intros cat_Kan_cs_intros cat_comma_cs_intros
                )+
          qed (cs_concl cs_simp: cs_intro: cat_cs_intros)+
        qed simp_all
      qed
    qed
    
    show "?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<AA>\<lparr>CId\<rparr>\<lparr>?the_cf_rKe\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      if "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for c
    proof-

      let ?ntcf_const_c = \<open>ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (\<AA>\<lparr>CId\<rparr>\<lparr>?UObj c\<rparr>)\<close>

      note lim_c = assms(3)[OF that]

      from that have CId_c: "\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr> : c \<mapsto>\<^bsub>\<CC>\<^esub> c" 
        by (cs_concl cs_intro: cat_cs_intros)

      interpret lim_c: is_cat_limit 
        \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>?UObj c\<close> \<open>?UArr c\<close>
        by (rule lim_c)

      show ?thesis
      proof
        (
          rule sym,
          rule the_cf_rKe_ArrMap_app(3)[
            where lim_Obj=lim_Obj, OF assms(1,2) CId_c lim_c lim_c
            ]
        )
        from that lim_c show 
          "\<AA>\<lparr>CId\<rparr>\<lparr>?the_cf_rKe\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr> : ?UObj c \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj c"
          by 
            (
              cs_concl
                cs_simp: cat_Kan_cs_simps
                cs_intro: cat_cs_intros cat_lim_cs_intros
            )
        have "?UArr c \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> =  ?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_const_c"
        proof(rule ntcf_eqI)
          from lim_c that show 
            "?UArr c \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> :
              cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (?UObj c) \<circ>\<^sub>C\<^sub>F (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F
              \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> \<circ>\<^sub>C\<^sub>F (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> :
              c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
            by (cs_concl cs_simp: cs_intro: cat_cs_intros cat_comma_cs_intros)
          from lim_c that show 
            "?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_const_c :
               cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (?UObj c) \<circ>\<^sub>C\<^sub>F (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F
               \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> \<circ>\<^sub>C\<^sub>F (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> :
               c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
            by 
              (
                cs_concl 
                  cs_intro: cat_cs_intros cat_lim_cs_intros 
                  cs_simp: \<KK>.cf_cf_arr_comma_CId cat_cs_simps
              )
          from that have dom_lhs:
            "\<D>\<^sub>\<circ> ((?UArr c \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>NTMap\<rparr>) = c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
            by 
              (
                cs_concl 
                  cs_simp: cat_cs_simps 
                  cs_intro: cat_cs_intros cat_comma_cs_intros
              )
          from that have dom_rhs:
            "\<D>\<^sub>\<circ> ((?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_const_c)\<lparr>NTMap\<rparr>) = c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
            by
              (
                cs_concl
                  cs_intro: cat_lim_cs_intros cat_cs_intros 
                  cs_simp: cat_cs_simps
              )
          show 
            "(?UArr c \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>NTMap\<rparr> =
              (?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_const_c)\<lparr>NTMap\<rparr>"
          proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
            fix A assume prems: "A \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
            with that obtain b f 
              where A_def: "A = [0, b, f]\<^sub>\<circ>"
                and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
                and f: "f : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
              by auto
            from that prems f have 
              "?UArr c\<lparr>NTMap\<rparr>\<lparr>0, b, f\<rparr>\<^sub>\<bullet> : ?UObj c \<mapsto>\<^bsub>\<AA>\<^esub> \<TT>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
              unfolding A_def
              by
                (
                  cs_concl
                    cs_simp: cat_cs_simps cat_comma_cs_simps 
                    cs_intro: cat_comma_cs_intros cat_cs_intros
                )
            from that prems f show 
              "(?UArr c \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK>)\<lparr>NTMap\<rparr>\<lparr>A\<rparr> =
                (?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?ntcf_const_c)\<lparr>NTMap\<rparr>\<lparr>A\<rparr>"
              unfolding A_def 
              by
                (
                  cs_concl
                    cs_simp: cat_cs_simps cat_comma_cs_simps
                    cs_intro: 
                      cat_lim_cs_intros cat_comma_cs_intros cat_cs_intros
                )
          qed (cs_concl cs_intro: cat_cs_intros)
        qed simp_all

        with that show 
          "?UArr c \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<KK> = 
            ?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (\<AA>\<lparr>CId\<rparr>\<lparr>?the_cf_rKe\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>)"
          by (cs_concl cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros)

      qed

    qed

  qed
    (
      cs_concl
        cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros cat_Kan_cs_intros
    )+

qed

lemma the_ntcf_rKe_is_ntcf:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> lim_Obj c\<lparr>UArr\<rparr> : 
      lim_Obj c\<lparr>UObj\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "the_ntcf_rKe \<alpha> \<TT> \<KK> lim_Obj :
    the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-

  let ?UObj = \<open>\<lambda>a. lim_Obj a\<lparr>UObj\<rparr>\<close> 
  let ?UArr = \<open>\<lambda>a. lim_Obj a\<lparr>UArr\<rparr>\<close>
  let ?const_comma = \<open>\<lambda>a b. cf_const (a \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (?UObj b)\<close>
  let ?the_cf_rKe = \<open>the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<close>
  let ?the_ntcf_rKe = \<open>the_ntcf_rKe \<alpha> \<TT> \<KK> lim_Obj\<close>

  interpret \<KK>: is_tm_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))
  interpret cf_rKe: is_functor \<alpha> \<CC> \<AA> \<open>?the_cf_rKe\<close>
    by (rule the_cf_rKe_is_functor[OF assms, simplified])

  show ?thesis
  proof(rule is_ntcfI')
    show "vfsequence ?the_ntcf_rKe" unfolding the_ntcf_rKe_def by simp
    show "vcard ?the_ntcf_rKe = 5\<^sub>\<nat>"
      unfolding the_ntcf_rKe_def by (simp add: nat_omega_simps)
    show "?the_ntcf_rKe\<lparr>NTMap\<rparr>\<lparr>b\<rparr> : 
      (?the_cf_rKe \<circ>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> \<TT>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" for b
    proof-
      let ?\<KK>b = \<open>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<close>
      from that have \<KK>b: "\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        by (cs_concl cs_intro: cat_cs_intros)
      note lim_\<KK>b = assms(3)[OF \<KK>b]
      interpret lim_\<KK>b: is_cat_limit 
        \<alpha> \<open>?\<KK>b \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F ?\<KK>b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>?UObj ?\<KK>b\<close> \<open>?UArr ?\<KK>b\<close>
        by (rule lim_\<KK>b)
      from that lim_\<KK>b show ?thesis
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_comma_cs_simps cat_Kan_cs_simps
              cs_intro: cat_cs_intros cat_comma_cs_intros cat_Kan_cs_intros
          )+
    qed
    show 
      "?the_ntcf_rKe\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> (?the_cf_rKe \<circ>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        \<TT>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> ?the_ntcf_rKe\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" for a b f 
    proof-
      let ?\<KK>a = \<open>\<KK>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<close> and ?\<KK>b = \<open>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<close> and ?\<KK>f = \<open>\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<close>
      from that have \<KK>a: "?\<KK>a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
        and \<KK>b: "?\<KK>b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        and \<KK>f: "?\<KK>f : ?\<KK>a \<mapsto>\<^bsub>\<CC>\<^esub> ?\<KK>b"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+
      note lim_\<KK>a = assms(3)[OF \<KK>a]
        and lim_\<KK>b = assms(3)[OF \<KK>b]
      from that have z_b_\<KK>b: "[0, b, \<CC>\<lparr>CId\<rparr>\<lparr>?\<KK>b\<rparr>]\<^sub>\<circ> \<in>\<^sub>\<circ> ?\<KK>b \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
        by (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)
      from 
        lim_Obj_the_cf_rKe_commute[
          OF assms(1,2) lim_\<KK>a lim_\<KK>b \<KK>f z_b_\<KK>b, symmetric
          ]
        that
      have [cat_Kan_cs_simps]:
        "?UArr ?\<KK>b\<lparr>NTMap\<rparr>\<lparr>0, b, \<CC>\<lparr>CId\<rparr>\<lparr>?\<KK>b\<rparr>\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> ?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>?\<KK>f\<rparr> =
          ?UArr ?\<KK>a\<lparr>NTMap\<rparr>\<lparr>0, b, ?\<KK>f\<rparr>\<^sub>\<bullet>"
        by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      interpret lim_\<KK>a: is_cat_limit
        \<alpha> \<open>?\<KK>a \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F ?\<KK>a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>?UObj ?\<KK>a\<close> \<open>?UArr ?\<KK>a\<close>
        by (rule lim_\<KK>a)
      interpret lim_\<KK>b: is_cat_limit 
        \<alpha> \<open>?\<KK>b \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F ?\<KK>b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>?UObj ?\<KK>b\<close> \<open>?UArr ?\<KK>b\<close>
        by (rule lim_\<KK>b)
      from that have 
        "[[0, a, \<CC>\<lparr>CId\<rparr>\<lparr>?\<KK>a\<rparr>]\<^sub>\<circ>, [0, b, ?\<KK>f]\<^sub>\<circ>, [0, f]\<^sub>\<circ>]\<^sub>\<circ> :
          [0, a, \<CC>\<lparr>CId\<rparr>\<lparr>?\<KK>a\<rparr>]\<^sub>\<circ> \<mapsto>\<^bsub>(?\<KK>a) \<down>\<^sub>C\<^sub>F \<KK>\<^esub> [0, b, ?\<KK>f]\<^sub>\<circ>"
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_comma_cs_simps
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
      from lim_\<KK>a.ntcf_Comp_commute[OF this, symmetric] that
      have [cat_Kan_cs_simps]:
        "\<TT>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> ?UArr (?\<KK>a)\<lparr>NTMap\<rparr> \<lparr>0, a, \<CC>\<lparr>CId\<rparr>\<lparr>?\<KK>a\<rparr>\<rparr>\<^sub>\<bullet> =
          ?UArr ?\<KK>a\<lparr>NTMap\<rparr>\<lparr>0, b, ?\<KK>f\<rparr>\<^sub>\<bullet>"
        by
          (
            cs_prems
              cs_simp: cat_cs_simps cat_comma_cs_simps
              cs_intro: cat_cs_intros cat_comma_cs_intros \<Z>.cat_1_is_arrI
          )
      from that show ?thesis
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_Kan_cs_simps cs_intro: cat_cs_intros
          )
    qed
  qed
    (
      cs_concl
        cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros cat_Kan_cs_intros
    )+

qed

lemma the_ntcf_rKe_is_cat_rKe:
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> lim_Obj c\<lparr>UArr\<rparr> :
      lim_Obj c\<lparr>UObj\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "the_ntcf_rKe \<alpha> \<TT> \<KK> lim_Obj :
    the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT> : \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C \<AA>"
proof-

  let ?UObj = \<open>\<lambda>a. lim_Obj a\<lparr>UObj\<rparr>\<close> 
  let ?UArr = \<open>\<lambda>a. lim_Obj a\<lparr>UArr\<rparr>\<close>
  let ?the_cf_rKe = \<open>the_cf_rKe \<alpha> \<TT> \<KK> lim_Obj\<close>
  let ?the_ntcf_rKe = \<open>the_ntcf_rKe \<alpha> \<TT> \<KK> lim_Obj\<close>

  interpret \<KK>: is_tm_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<TT>: is_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))
  interpret cf_rKe: is_functor \<alpha> \<CC> \<AA> ?the_cf_rKe
    by (rule the_cf_rKe_is_functor[OF assms, simplified])
  interpret ntcf_rKe: is_ntcf \<alpha> \<BB> \<AA> \<open>?the_cf_rKe \<circ>\<^sub>C\<^sub>F \<KK>\<close> \<TT> ?the_ntcf_rKe
    by (intro the_ntcf_rKe_is_ntcf assms(3))
      (cs_concl cs_intro: cat_cs_intros cat_small_cs_intros)+

  show ?thesis
  proof(rule is_cat_rKeI')

    fix \<GG> \<epsilon> assume prems: 
      "\<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" "\<epsilon> : \<GG> \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"

    interpret \<GG>: is_functor \<alpha> \<CC> \<AA> \<GG> by (rule prems(1))
    interpret \<epsilon>: is_ntcf \<alpha> \<BB> \<AA> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<KK>\<close> \<TT> \<epsilon> by (rule prems(2))

    define \<epsilon>' where "\<epsilon>' c =
      [
        (\<lambda>A\<in>\<^sub>\<circ>c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>. \<epsilon>\<lparr>NTMap\<rparr>\<lparr>A\<lparr>1\<^sub>\<nat>\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>A\<lparr>2\<^sub>\<nat>\<rparr>\<rparr>),
        cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>),
        \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>,
        c \<down>\<^sub>C\<^sub>F \<KK>,
        \<AA>
      ]\<^sub>\<circ>"
      for c

    have \<epsilon>'_components: 
      "\<epsilon>' c\<lparr>NTMap\<rparr> = (\<lambda>A\<in>\<^sub>\<circ>c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>. \<epsilon>\<lparr>NTMap\<rparr>\<lparr>A\<lparr>1\<^sub>\<nat>\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>A\<lparr>2\<^sub>\<nat>\<rparr>\<rparr>)"
      "\<epsilon>' c\<lparr>NTDom\<rparr> = cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>)"
      "\<epsilon>' c\<lparr>NTCod\<rparr> = \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>"
      "\<epsilon>' c\<lparr>NTDGDom\<rparr> = c \<down>\<^sub>C\<^sub>F \<KK>"
      "\<epsilon>' c\<lparr>NTDGCod\<rparr> = \<AA>"
      for c 
      unfolding \<epsilon>'_def nt_field_simps by (simp_all add: nat_omega_simps)
    note [cat_Kan_cs_simps] = \<epsilon>'_components(2-5)
    have [cat_Kan_cs_simps]: "\<epsilon>' c\<lparr>NTMap\<rparr>\<lparr>A\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      if "A = [a, b, f]\<^sub>\<circ>" and "[a, b, f]\<^sub>\<circ> \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>" for A a b c f
      using that unfolding \<epsilon>'_components by (auto simp: nat_omega_simps)

    have \<epsilon>': "\<epsilon>' c : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      and \<epsilon>'_unique: "\<exists>!f'.
        f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj c \<and>
        \<epsilon>' c = ?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> f'" 
      if c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for c
    proof-
      from that have "?the_cf_rKe\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> = ?UObj c"
        by (cs_concl cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros)
      interpret lim_c: is_cat_limit 
        \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>?UObj c\<close> \<open>?UArr c\<close>
        by (rule assms(3)[OF that])
      show "\<epsilon>' c : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : c \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      proof(intro is_cat_coneI is_tm_ntcfI' is_ntcfI')
        show "vfsequence (\<epsilon>' c)" unfolding \<epsilon>'_def by simp
        show "vcard (\<epsilon>' c) = 5\<^sub>\<nat>" unfolding \<epsilon>'_def by (simp add: nat_omega_simps)
        show "vsv (\<epsilon>' c\<lparr>NTMap\<rparr>)" unfolding \<epsilon>'_components by simp 
        show "\<D>\<^sub>\<circ> (\<epsilon>' c\<lparr>NTMap\<rparr>) = c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>" unfolding \<epsilon>'_components by simp
        show "\<epsilon>' c\<lparr>NTMap\<rparr>\<lparr>A\<rparr> :
          cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>)\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub>
          (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>A\<rparr>"
          if "A \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>" for A
        proof-
          from that prems c obtain b f 
            where A_def: "A = [0, b, f]\<^sub>\<circ>"
              and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
              and f: "f : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
            by auto
          from that prems f c that b f show ?thesis
            unfolding A_def
            by
              (
                cs_concl
                  cs_simp: cat_cs_simps cat_Kan_cs_simps cat_comma_cs_simps
                  cs_intro: cat_cs_intros cat_comma_cs_intros
              )
        qed
        show
          "\<epsilon>' c\<lparr>NTMap\<rparr>\<lparr>B\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> cf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> =
            (\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<epsilon>' c\<lparr>NTMap\<rparr>\<lparr>A\<rparr>"
          if "F : A \<mapsto>\<^bsub>c \<down>\<^sub>C\<^sub>F \<KK>\<^esub> B" for A B F
        proof-
          from that c 
          obtain b f b' f' k 
            where F_def: "F = [[0, b, f]\<^sub>\<circ>, [0, b', f']\<^sub>\<circ>, [0, k]\<^sub>\<circ>]\<^sub>\<circ>"
              and A_def: "A = [0, b, f]\<^sub>\<circ>"
              and B_def: "B = [0, b', f']\<^sub>\<circ>"
              and k: "k : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
              and f: "f : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
              and f': "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
              and f'_def: "\<KK>\<lparr>ArrMap\<rparr>\<lparr>k\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = f'"
            by auto
          from c that k f f' show ?thesis
            unfolding F_def A_def B_def
            by (*slow*)
              (
                cs_concl
                  cs_simp:
                    cat_cs_simps
                    cat_comma_cs_simps
                    cat_Kan_cs_simps
                    \<epsilon>.ntcf_Comp_commute''
                    f'_def[symmetric]
                  cs_intro: cat_cs_intros cat_comma_cs_intros
              )
        qed
      qed
        (
          use c that in
            \<open>
              cs_concl
                cs_simp: cat_Kan_cs_simps
                cs_intro: cat_small_cs_intros cat_cs_intros
            \<close>
        )+
      from is_cat_limit.cat_lim_unique_cone[OF assms(3)[OF that] this] show 
        "\<exists>!f'.
          f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj c \<and>
          \<epsilon>' c = ?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> f'"  
        by simp
    qed

    define \<sigma> :: V where
      "\<sigma> =
        [
          (
            \<lambda>c\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. THE f.
              f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj c \<and>
              \<epsilon>' c = ?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> f
          ),
          \<GG>,
          ?the_cf_rKe,
          \<CC>,
          \<AA>
        ]\<^sub>\<circ>"

    have \<sigma>_components:
      "\<sigma>\<lparr>NTMap\<rparr> =
        (
          \<lambda>c\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. THE f.
            f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj c \<and>
            \<epsilon>' c = ?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> f
        )"
      "\<sigma>\<lparr>NTDom\<rparr> = \<GG>"
      "\<sigma>\<lparr>NTCod\<rparr> = ?the_cf_rKe"
      "\<sigma>\<lparr>NTDGDom\<rparr> = \<CC>"
      "\<sigma>\<lparr>NTDGCod\<rparr> = \<AA>"
      unfolding \<sigma>_def nt_field_simps by (simp_all add: nat_omega_simps)

    note [cat_Kan_cs_simps] = \<sigma>_components(2-5)

    have \<sigma>_NTMap_app_def: "\<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> =
      (
        THE f.
          f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj c \<and>
          \<epsilon>' c = ?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> f
      )"
      if "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for c
      using that unfolding \<sigma>_components by simp

    have \<sigma>_NTMap_app_is_arr: "\<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj c"
      and \<epsilon>'_\<sigma>_commute:
        "\<epsilon>' c = ?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (\<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>)"
      and \<sigma>_NTMap_app_unique:
        "\<lbrakk>
          f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj c;
          \<epsilon>' c = ?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> f
         \<rbrakk> \<Longrightarrow> f = \<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
        if c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for c f
    proof-
      have 
        "\<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj c \<and>
        \<epsilon>' c = ?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (\<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>)"
        by 
          (
            cs_concl 
              cs_simp: cat_Kan_cs_simps \<sigma>_NTMap_app_def 
              cs_intro: theI' \<epsilon>'_unique that
          )
      then show "\<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj c"
        and "\<epsilon>' c = ?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (\<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>)"
        by simp_all
      with c \<epsilon>'_unique[OF c] show "f = \<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
        if "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj c"
          and "\<epsilon>' c = ?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> f"
        using that by metis
    qed

    have \<sigma>_NTMap_app_is_arr'[cat_Kan_cs_intros]: "\<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : a \<mapsto>\<^bsub>\<AA>'\<^esub> b"
      if "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
        and "a = \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>" 
        and "b = ?UObj c" 
        and "\<AA>' = \<AA>"
      for \<AA>' a b c
      by (simp add: that \<sigma>_NTMap_app_is_arr)

    have \<epsilon>'_NTMap_app_def: 
      "\<epsilon>' c\<lparr>NTMap\<rparr>\<lparr>A\<rparr> =
        (?UArr c \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const (c \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (\<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>))\<lparr>NTMap\<rparr>\<lparr>A\<rparr>"
      if "A \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>" and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for A c
      using \<epsilon>'_\<sigma>_commute[OF that(2)] by simp
    have \<epsilon>b_\<GG>f:
      "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        ?UArr c\<lparr>NTMap\<rparr>\<lparr>a, b, f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
      if "A = [a, b, f]\<^sub>\<circ>" and "A \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>" and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
      for A a b c f
    proof-
      interpret lim_c: is_cat_limit 
        \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>?UObj c\<close> \<open>?UArr c\<close>
        by (rule assms(3)[OF that(3)])
      from that have b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and f: "f : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by blast+
      show
        "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
          ?UArr c\<lparr>NTMap\<rparr>\<lparr>a, b, f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
        using \<epsilon>'_NTMap_app_def[OF that(2,3)] that(2,3)
        unfolding that(1)
        by
          (
            cs_prems
              cs_simp: cat_cs_simps cat_Kan_cs_simps
              cs_intro: cat_cs_intros cat_Kan_cs_intros
          )
    qed

    show "\<exists>!\<sigma>.
      \<sigma> : \<GG> \<mapsto>\<^sub>C\<^sub>F ?the_cf_rKe : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> \<and>
      \<epsilon> = ?the_ntcf_rKe \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)"
    proof(intro ex1I[where a=\<sigma>] conjI; (elim conjE)?)

      define \<tau> where "\<tau> a b f =
        [
          (
            \<lambda>F\<in>\<^sub>\<circ>b \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>.
              ?UArr b\<lparr>NTMap\<rparr>\<lparr>F\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<sigma>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>
          ),
          cf_const (b \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>),
          \<TT> \<circ>\<^sub>C\<^sub>F b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>,
          b \<down>\<^sub>C\<^sub>F \<KK>,
          \<AA>
        ]\<^sub>\<circ>"
        for a b f

      have \<tau>_components:
        "\<tau> a b f\<lparr>NTMap\<rparr> =
          (
            \<lambda>F\<in>\<^sub>\<circ>b \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>.
              ?UArr b\<lparr>NTMap\<rparr>\<lparr>F\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<sigma>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>
          )"
        "\<tau> a b f\<lparr>NTDom\<rparr> = cf_const (b \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)"
        "\<tau> a b f\<lparr>NTCod\<rparr> = \<TT> \<circ>\<^sub>C\<^sub>F b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>"
        "\<tau> a b f\<lparr>NTDGDom\<rparr> = b \<down>\<^sub>C\<^sub>F \<KK>"
        "\<tau> a b f\<lparr>NTDGCod\<rparr> = \<AA>"
        for a b f
        unfolding \<tau>_def nt_field_simps by (simp_all add: nat_omega_simps)
      note [cat_Kan_cs_simps] = \<tau>_components(2-5)
      have \<tau>_NTMap_app[cat_Kan_cs_simps]: 
        "\<tau> a b f\<lparr>NTMap\<rparr>\<lparr>F\<rparr> =
          ?UArr b\<lparr>NTMap\<rparr>\<lparr>F\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<sigma>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
        if "F \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>" for a b f F
        using that unfolding \<tau>_components by auto
      
      have \<tau>: "\<tau> a b f :
        \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> \<circ>\<^sub>C\<^sub>F b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK> : b \<down>\<^sub>C\<^sub>F \<KK> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        if f_is_arr: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for a b f
      proof-

        note f = \<KK>.HomCod.cat_is_arrD[OF that]
        note lim_a = assms(3)[OF f(2)] and lim_b = assms(3)[OF f(3)]

        interpret lim_b: is_cat_limit 
          \<alpha> \<open>b \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>?UObj b\<close> \<open>?UArr b\<close>
          by (rule lim_b)
        
        from f have a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto

        show ?thesis
        proof(intro is_cat_coneI is_tm_ntcfI' is_ntcfI')

          show "vfsequence (\<tau> a b f)" unfolding \<tau>_def by simp
          show "vcard (\<tau> a b f) = 5\<^sub>\<nat>" 
            unfolding \<tau>_def by (simp add: nat_omega_simps)
          show "vsv (\<tau> a b f\<lparr>NTMap\<rparr>)" unfolding \<tau>_components by auto
          show "\<D>\<^sub>\<circ> (\<tau> a b f\<lparr>NTMap\<rparr>) = b \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>" by (auto simp: \<tau>_components)
          show "\<tau> a b f\<lparr>NTMap\<rparr>\<lparr>A\<rparr> :
            cf_const (b \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub>
            (\<TT> \<circ>\<^sub>C\<^sub>F b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ObjMap\<rparr>\<lparr>A\<rparr>"
            if "A \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>" for A
          proof-
            from that f_is_arr obtain b' f' 
              where A_def: "A = [0, b', f']\<^sub>\<circ>"
                and b': "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
                and f': "f' : b \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
              by auto
            from  f_is_arr that b' f' a b show ?thesis
              unfolding A_def
              by
                (
                  cs_concl
                    cs_simp: cat_cs_simps cat_comma_cs_simps cat_Kan_cs_simps
                    cs_intro: cat_cs_intros cat_comma_cs_intros cat_Kan_cs_intros
                )   
          qed
          show
            "\<tau> a b f\<lparr>NTMap\<rparr>\<lparr>B\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub>
              cf_const (b \<down>\<^sub>C\<^sub>F \<KK>) \<AA> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> =
              (\<TT> \<circ>\<^sub>C\<^sub>F b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<tau> a b f\<lparr>NTMap\<rparr>\<lparr>A\<rparr>"
            if "F : A \<mapsto>\<^bsub>b \<down>\<^sub>C\<^sub>F \<KK>\<^esub> B" for A B F
          proof-
            from that have F: "F : A \<mapsto>\<^bsub>b \<down>\<^sub>C\<^sub>F \<KK>\<^esub> B"
              by (auto intro: is_arrI)
            with f_is_arr obtain b' f' b'' f'' h'
              where F_def: "F = [[0, b', f']\<^sub>\<circ>, [0, b'', f'']\<^sub>\<circ>, [0, h']\<^sub>\<circ>]\<^sub>\<circ>"
                and A_def: "A = [0, b', f']\<^sub>\<circ>"
                and B_def: "B = [0, b'', f'']\<^sub>\<circ>"
                and h': "h' : b' \<mapsto>\<^bsub>\<BB>\<^esub> b''"
                and f': "f' : b \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
                and f'': "f'' : b \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b''\<rparr>"
                and f''_def: "\<KK>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' = f''"
              by auto
            from
              lim_b.ntcf_Comp_commute[OF that] 
              that f_is_arr g' h' f' f'' 
            have [cat_Kan_cs_simps]:
              "?UArr b\<lparr>NTMap\<rparr>\<lparr>0, b'', \<KK>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'\<rparr>\<^sub>\<bullet> =
                \<TT>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> ?UArr b\<lparr>NTMap\<rparr>\<lparr>0, b', f'\<rparr>\<^sub>\<bullet>"
              unfolding F_def A_def B_def
              by
                (
                  cs_prems
                    cs_simp: 
                      cat_cs_simps cat_comma_cs_simps f''_def[symmetric]
                    cs_intro: cat_cs_intros cat_comma_cs_intros
                )
            from f_is_arr that g' h' f' f'' show ?thesis
              unfolding F_def A_def B_def (*very slow*)
              by
                (
                  cs_concl
                    cs_simp:
                      cat_cs_simps 
                      cat_Kan_cs_simps 
                      cat_comma_cs_simps 
                      f''_def[symmetric]
                    cs_intro:
                      cat_cs_intros cat_Kan_cs_intros cat_comma_cs_intros
                )+
          qed

        qed
          (
            use that f_is_arr in
              \<open>
                cs_concl
                  cs_simp: cat_cs_simps cat_Kan_cs_simps
                  cs_intro: cat_small_cs_intros cat_cs_intros
              \<close>
          )+
      qed

      show \<sigma>: "\<sigma> : \<GG> \<mapsto>\<^sub>C\<^sub>F ?the_cf_rKe : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      proof(rule is_ntcfI')

        show "vfsequence \<sigma>" unfolding \<sigma>_def by simp
        show "vcard \<sigma> = 5\<^sub>\<nat>" unfolding \<sigma>_def by (simp add: nat_omega_simps)
        show "vsv (\<sigma>\<lparr>NTMap\<rparr>)" unfolding \<sigma>_components by auto
        show "\<D>\<^sub>\<circ> (\<sigma>\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>" unfolding \<sigma>_components by simp
        show "\<sigma>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?the_cf_rKe\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
          if "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for a
          using that 
          by
            (
              cs_concl
                cs_simp: cat_cs_simps cat_Kan_cs_simps
                cs_intro: cat_cs_intros cat_Kan_cs_intros
            )

        then have [cat_Kan_cs_intros]: "\<sigma>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : b \<mapsto>\<^bsub>\<AA>\<^esub> c"
          if "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
            and "b = \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" 
            and "c = ?the_cf_rKe\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
          for a b c
          using that(1) unfolding that(2,3) by simp

        show 
          "\<sigma>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
            ?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<sigma>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
          if f_is_arr: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for a b f
        proof-

          note f = \<KK>.HomCod.cat_is_arrD[OF that]
          note lim_a = assms(3)[OF f(2)] and lim_b = assms(3)[OF f(3)]

          interpret lim_a: is_cat_limit 
            \<alpha> \<open>a \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>?UObj a\<close> \<open>?UArr a\<close>
            by (rule lim_a)
          interpret lim_b: is_cat_limit 
            \<alpha> \<open>b \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>?UObj b\<close> \<open>?UArr b\<close>
            by (rule lim_b)

          from f have a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
          
          from lim_b.cat_lim_unique_cone'[OF \<tau>[OF that]] obtain g' 
            where g': "g' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj b"
              and \<tau>_NTMap_app: "\<And>A. A \<in>\<^sub>\<circ> (b \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>) \<Longrightarrow>
                \<tau> a b f\<lparr>NTMap\<rparr>\<lparr>A\<rparr> = ?UArr b\<lparr>NTMap\<rparr>\<lparr>A\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> g'"
              and g'_unique: "\<And>g''.
                \<lbrakk>
                  g'' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj b;
                  \<And>A. A \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr> \<Longrightarrow>
                    \<tau> a b f\<lparr>NTMap\<rparr>\<lparr>A\<rparr> = ?UArr b\<lparr>NTMap\<rparr>\<lparr>A\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> g''
                \<rbrakk> \<Longrightarrow> g'' = g'"
            by metis

          have lim_Obj_a_f\<KK>[symmetric, cat_Kan_cs_simps]:
            "?UArr a\<lparr>NTMap\<rparr>\<lparr>a', b', f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr>\<^sub>\<bullet> =
              ?UArr b\<lparr>NTMap\<rparr>\<lparr>A\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> ?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
            if "A = [a', b', f']\<^sub>\<circ>" and "A \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>" for A a' b' f'
          proof-
            from that(2) f_is_arr have a'_def: "a' = 0" 
              and b': "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
              and f': "f' : b \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
              unfolding that(1) by auto
            show ?thesis 
              unfolding that(1) 
              by 
                (
                  rule 
                    lim_Obj_the_cf_rKe_commute
                      [
                        where lim_Obj=lim_Obj, 
                        OF 
                          assms(1,2) 
                          lim_a 
                          lim_b 
                          f_is_arr 
                          that(2)[unfolded that(1)] 
                      ]
                )
          qed
          {
            fix a' b' f' A
            note \<TT>.HomCod.cat_assoc_helper[
              where h=\<open>?UArr b\<lparr>NTMap\<rparr>\<lparr>a',b',f'\<rparr>\<^sub>\<bullet>\<close> 
                and g=\<open>?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<close>
                and q=\<open>?UArr a\<lparr>NTMap\<rparr>\<lparr>a', b', f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr>\<^sub>\<bullet>\<close>
                ]
          }
          note [cat_Kan_cs_simps] = this

          show ?thesis
          proof(rule trans_sym[where s=g'])
            show "\<sigma>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = g'"
            proof(rule g'_unique)
              from that show
                "\<sigma>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj b"
                by (cs_concl cs_intro: cat_cs_intros cat_Kan_cs_intros)
              fix A assume prems': "A \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
              with f_is_arr obtain b' f' 
                where A_def: "A = [0, b', f']\<^sub>\<circ>"
                  and b': "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
                  and f': "f' : b \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
                by auto
              from f_is_arr prems' show
                "\<tau> a b f\<lparr>NTMap\<rparr>\<lparr>A\<rparr> =
                  ?UArr b\<lparr>NTMap\<rparr>\<lparr>A\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> (\<sigma>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>)"
                unfolding A_def
                by
                  (
                    cs_concl
                      cs_simp: cat_cs_simps cat_Kan_cs_simps
                      cs_intro: cat_cs_intros cat_Kan_cs_intros
                  )
            qed
            show "?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<sigma>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = g'"
            proof(rule g'_unique)                  
              fix A assume prems': "A \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
              with f_is_arr obtain b' f' 
                where A_def: "A = [0, b', f']\<^sub>\<circ>"
                  and b': "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
                  and f': "f' : b \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
                by auto
              {
                fix a' b' f' A
                note \<TT>.HomCod.cat_assoc_helper
                  [
                    where h=\<open>?UArr b\<lparr>NTMap\<rparr>\<lparr>a', b', f'\<rparr>\<^sub>\<bullet>\<close> 
                      and g=\<open>\<sigma>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<close>
                      and q=\<open>\<epsilon>\<lparr>NTMap\<rparr>\<lparr>b'\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>\<close>
                  ]
              }
              note [cat_Kan_cs_simps] = 
                this
                \<epsilon>b_\<GG>f[OF A_def prems' b, symmetric]
                \<epsilon>b_\<GG>f[symmetric]
              from f_is_arr prems' b' f' show 
                "\<tau> a b f\<lparr>NTMap\<rparr>\<lparr>A\<rparr> =
                  ?UArr b\<lparr>NTMap\<rparr>\<lparr>A\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub>
                    (?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<sigma>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
                unfolding A_def
                by
                  (
                    cs_concl 
                      cs_simp: 
                        cat_cs_simps 
                        cat_Kan_cs_simps 
                        cat_comma_cs_simps
                        cat_op_simps
                      cs_intro: 
                        cat_cs_intros 
                        cat_Kan_cs_intros 
                        cat_comma_cs_intros 
                        cat_op_intros
                  )
            qed
              (
                use that in
                  \<open>
                    cs_concl
                      cs_simp: cat_Kan_cs_simps
                      cs_intro: cat_cs_intros cat_Kan_cs_intros
                  \<close>
              )
          qed
        qed
      qed
        (
          cs_concl
            cs_simp: cat_cs_simps cat_Kan_cs_simps
            cs_intro: cat_cs_intros
        )+
      then interpret \<sigma>: is_ntcf \<alpha> \<CC> \<AA> \<GG> \<open>?the_cf_rKe\<close> \<sigma> by simp

      show "\<epsilon> = ?the_ntcf_rKe \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)"
      proof(rule ntcf_eqI)
        have dom_lhs: "\<D>\<^sub>\<circ> (\<epsilon>\<lparr>NTMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>" 
          by (cs_concl cs_simp: cat_cs_simps)
        have dom_rhs: "\<D>\<^sub>\<circ> ((?the_ntcf_rKe \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>))\<lparr>NTMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        show "\<epsilon>\<lparr>NTMap\<rparr> = (?the_ntcf_rKe \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>))\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          fix b assume prems': "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
          note [cat_Kan_cs_simps] = \<epsilon>b_\<GG>f[
            where f=\<open>\<CC>\<lparr>CId\<rparr>\<lparr>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr>\<close> and c=\<open>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<close>, symmetric
            ]
          from prems' \<sigma> show 
            "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> = (?the_ntcf_rKe \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>))\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
            by
              (
                cs_concl
                  cs_simp: cat_cs_simps cat_comma_cs_simps cat_Kan_cs_simps 
                  cs_intro: cat_cs_intros cat_comma_cs_intros cat_Kan_cs_intros
              )
        qed (cs_concl cs_intro: cat_cs_intros V_cs_intros)
      qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+

      fix \<sigma>' assume prems':
        "\<sigma>' : \<GG> \<mapsto>\<^sub>C\<^sub>F ?the_cf_rKe : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        "\<epsilon> = ?the_ntcf_rKe \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)"

      interpret \<sigma>': is_ntcf \<alpha> \<CC> \<AA> \<GG> \<open>?the_cf_rKe\<close> \<sigma>' by (rule prems'(1))

      have \<epsilon>_NTMap_app[symmetric, cat_Kan_cs_simps]: 
        "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>b'\<rparr> =
          ?UArr (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>)\<lparr>NTMap\<rparr>\<lparr>a', b', \<CC>\<lparr>CId\<rparr>\<lparr>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>\<rparr>\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub>
          \<sigma>'\<lparr>NTMap\<rparr>\<lparr>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>\<rparr>"
        if "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "a' = 0" for a' b'
      proof-
        from prems'(2) have \<epsilon>_NTMap_app: 
          "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>b'\<rparr> = (?the_ntcf_rKe \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>))\<lparr>NTMap\<rparr>\<lparr>b'\<rparr>"
          for b'
          by simp
        show ?thesis
          using \<epsilon>_NTMap_app[of b'] that(1)
          unfolding that(2)
          by
            (
              cs_prems
                cs_simp: cat_cs_simps cat_comma_cs_simps cat_Kan_cs_simps
                cs_intro: cat_cs_intros cat_comma_cs_intros
            )
      qed
      {
        fix a' b' f' A
        note \<TT>.HomCod.cat_assoc_helper
          [
            where h=
              \<open>?UArr (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>)\<lparr>NTMap\<rparr>\<lparr>a', b', \<CC>\<lparr>CId\<rparr>\<lparr>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>\<rparr>\<rparr>\<^sub>\<bullet>\<close>
              and g=\<open>\<sigma>'\<lparr>NTMap\<rparr>\<lparr>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>\<rparr>\<close>
              and q=\<open>\<epsilon>\<lparr>NTMap\<rparr>\<lparr>b'\<rparr>\<close>
          ]
      }
      note [cat_Kan_cs_simps] = this \<epsilon>b_\<GG>f[symmetric]
      {
        fix a' b' f' A
        note \<TT>.HomCod.cat_assoc_helper
          [
            where h=\<open>
              ?UArr (\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>)\<lparr>NTMap\<rparr>\<lparr>
                a', b', \<CC>\<lparr>CId\<rparr>\<lparr>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>\<rparr>
                \<rparr>\<^sub>\<bullet>\<close>
            and g=\<open>\<sigma>\<lparr>NTMap\<rparr>\<lparr>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>\<rparr>\<close>
            and q=\<open>\<epsilon>\<lparr>NTMap\<rparr>\<lparr>b'\<rparr>\<close>
          ]
      }
      note [cat_Kan_cs_simps] = this

      show "\<sigma>' = \<sigma>"
      proof(rule ntcf_eqI)

        show "\<sigma>' : \<GG> \<mapsto>\<^sub>C\<^sub>F ?the_cf_rKe : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" by (rule prems'(1))
        show "\<sigma> : \<GG> \<mapsto>\<^sub>C\<^sub>F ?the_cf_rKe : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" by (rule \<sigma>)

        have dom_lhs: "\<D>\<^sub>\<circ> (\<sigma>\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>" 
          by (cs_concl cs_simp: cat_cs_simps)
        have dom_rhs: "\<D>\<^sub>\<circ> (\<sigma>'\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps)

        show "\<sigma>'\<lparr>NTMap\<rparr> = \<sigma>\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)

          fix c assume prems': "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"

          note lim_c = assms(3)[OF prems']
          interpret lim_c: is_cat_limit 
            \<alpha> \<open>c \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F c \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>?UObj c\<close> \<open>?UArr c\<close>
            by (rule lim_c)
          from prems' have CId_c: "\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr> : c \<mapsto>\<^bsub>\<CC>\<^esub> c"
            by (cs_concl cs_intro: cat_cs_intros)

          from lim_c.cat_lim_unique_cone'[OF \<tau>[OF CId_c]] obtain f 
            where f: "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj c"
              and "\<And>A. A \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr> \<Longrightarrow>
                \<tau> c c (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>)\<lparr>NTMap\<rparr>\<lparr>A\<rparr> = ?UArr c\<lparr>NTMap\<rparr>\<lparr>A\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f"
              and f_unique: "\<And>f'.
                \<lbrakk>
                  f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> ?UObj c;
                  \<And>A. A \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr> \<Longrightarrow>
                    \<tau> c c (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>)\<lparr>NTMap\<rparr>\<lparr>A\<rparr> = ?UArr c\<lparr>NTMap\<rparr>\<lparr>A\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f'
                \<rbrakk> \<Longrightarrow> f' = f"
            by metis

          note [symmetric, cat_cs_simps] =
            \<sigma>.ntcf_Comp_commute
            \<sigma>'.ntcf_Comp_commute

          show "\<sigma>'\<lparr>NTMap\<rparr>\<lparr>c\<rparr> = \<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
          proof(rule trans_sym[where s=f])

            show "\<sigma>'\<lparr>NTMap\<rparr>\<lparr>c\<rparr> = f"
            proof(rule f_unique)

              fix A assume prems'': "A \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"

              with prems' obtain b' f' 
                where A_def: "A = [0, b', f']\<^sub>\<circ>"
                  and b': "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
                  and f': "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
                by auto

              let ?\<KK>b' = \<open>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>\<close>

              from b' have \<KK>b': "?\<KK>b' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
                by (cs_concl cs_intro: cat_cs_intros)

              interpret lim_\<KK>b': is_cat_limit
                \<alpha> \<open>?\<KK>b' \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F ?\<KK>b' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>?UObj ?\<KK>b'\<close> \<open>?UArr ?\<KK>b'\<close>
                by (rule assms(3)[OF \<KK>b'])

              from \<KK>b' have CId_\<KK>b': "\<CC>\<lparr>CId\<rparr>\<lparr>?\<KK>b'\<rparr> : ?\<KK>b' \<mapsto>\<^bsub>\<CC>\<^esub> ?\<KK>b'"
                by (cs_concl cs_intro: cat_cs_intros)
              from CId_\<KK>b' b' have a'_b'_CId_\<KK>b':
                "[0, b', \<CC>\<lparr>CId\<rparr>\<lparr>?\<KK>b'\<rparr>]\<^sub>\<circ> \<in>\<^sub>\<circ> ?\<KK>b' \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
                by
                  (
                    cs_concl
                      cs_simp: cat_cs_simps cat_comma_cs_simps
                      cs_intro: cat_cs_intros cat_comma_cs_intros
                  )
              from 
                lim_Obj_the_cf_rKe_commute[
                  where lim_Obj=lim_Obj, 
                  OF assms(1,2) lim_c assms(3)[OF \<KK>b'] f' a'_b'_CId_\<KK>b'
                  ]
                f'
              have [cat_Kan_cs_simps]:
                "?UArr c\<lparr>NTMap\<rparr>\<lparr>0, b', f'\<rparr>\<^sub>\<bullet> =
                  ?UArr ?\<KK>b'\<lparr>NTMap\<rparr>\<lparr>0, b', \<CC>\<lparr>CId\<rparr>\<lparr>?\<KK>b'\<rparr>\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> 
                    ?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>"
                by (cs_prems cs_simp: cat_cs_simps)

              from prems' prems'' b' f' show
                "\<tau> c c (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>)\<lparr>NTMap\<rparr>\<lparr>A\<rparr> = ?UArr c\<lparr>NTMap\<rparr>\<lparr>A\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<sigma>'\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
                unfolding A_def (*very slow*)
                by
                  (
                    cs_concl
                      cs_simp:
                        cat_cs_simps cat_comma_cs_simps cat_Kan_cs_simps
                      cs_intro:
                        cat_cs_intros cat_comma_cs_intros cat_Kan_cs_intros
                  )

            qed
              (
                use prems' in
                  \<open>cs_concl cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros\<close>
              )

            show "\<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> = f"
            proof(rule f_unique)
              fix A assume prems'': "A \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
              from this prems' obtain b' f' 
                where A_def: "A = [0, b', f']\<^sub>\<circ>"
                  and b': "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
                  and f': "f' : c \<mapsto>\<^bsub>\<CC>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
                by auto
              let ?\<KK>b' = \<open>\<KK>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>\<close>
              from b' have \<KK>b': "?\<KK>b' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
                by (cs_concl cs_intro: cat_cs_intros)
              interpret lim_\<KK>b': is_cat_limit
                \<alpha> \<open>?\<KK>b' \<down>\<^sub>C\<^sub>F \<KK>\<close> \<AA> \<open>\<TT> \<circ>\<^sub>C\<^sub>F ?\<KK>b' \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<KK>\<close> \<open>?UObj ?\<KK>b'\<close> \<open>?UArr ?\<KK>b'\<close>
                by (rule assms(3)[OF \<KK>b'])
              from \<KK>b' have CId_\<KK>b': "\<CC>\<lparr>CId\<rparr>\<lparr>?\<KK>b'\<rparr> : ?\<KK>b' \<mapsto>\<^bsub>\<CC>\<^esub> ?\<KK>b'"
                by (cs_concl cs_intro: cat_cs_intros)
              from CId_\<KK>b' b' have a'_b'_CId_\<KK>b': 
                "[0, b', \<CC>\<lparr>CId\<rparr>\<lparr>?\<KK>b'\<rparr>]\<^sub>\<circ> \<in>\<^sub>\<circ> ?\<KK>b' \<down>\<^sub>C\<^sub>F \<KK>\<lparr>Obj\<rparr>"
                by
                  (
                    cs_concl
                      cs_simp: cat_cs_simps cat_comma_cs_simps
                      cs_intro: cat_cs_intros cat_comma_cs_intros
                  )

              from 
                lim_Obj_the_cf_rKe_commute
                  [
                    where lim_Obj=lim_Obj, 
                    OF assms(1,2) lim_c assms(3)[OF \<KK>b'] f' a'_b'_CId_\<KK>b'
                  ]
                f'
              have [cat_Kan_cs_simps]:
                "?UArr c\<lparr>NTMap\<rparr>\<lparr>0, b', f'\<rparr>\<^sub>\<bullet> =
                  ?UArr (?\<KK>b')\<lparr>NTMap\<rparr>\<lparr>0, b', \<CC>\<lparr>CId\<rparr>\<lparr>?\<KK>b'\<rparr>\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub>
                    ?the_cf_rKe\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>"
                by (cs_prems cs_simp: cat_cs_simps)
              from prems' prems'' b' f' show
                "\<tau> c c (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>)\<lparr>NTMap\<rparr>\<lparr>A\<rparr> = ?UArr c\<lparr>NTMap\<rparr>\<lparr>A\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
                unfolding A_def (*very slow*)
                by
                  (
                    cs_concl
                      cs_simp:
                        cat_cs_simps cat_comma_cs_simps cat_Kan_cs_simps 
                      cs_intro:
                        cat_cs_intros cat_comma_cs_intros cat_Kan_cs_intros
                  )
            qed
              (
                use prems' in
                  \<open>cs_concl cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros\<close>
              )
          qed

        qed auto

      qed simp_all

    qed

  qed (cs_concl cs_intro: cat_cs_intros)+

qed



subsection\<open>Preservation of Kan extension\<close>


text\<open>
The following definitions are similar to the definitions that can be 
found in \cite{riehl_category_2016} or \cite{lehner_all_2014}.
\<close>

locale is_cat_rKe_preserves =
  is_cat_rKe \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT> \<GG> \<epsilon> + is_functor \<alpha> \<AA> \<DD> \<HH>
  for \<alpha> \<BB> \<CC> \<AA> \<DD> \<KK> \<TT> \<GG> \<HH> \<epsilon> +
  assumes cat_rKe_preserves:
    "\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon> : (\<HH> \<circ>\<^sub>C\<^sub>F \<GG>) \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<HH> \<circ>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C \<DD>"

syntax "_is_cat_rKe_preserves" :: 
  "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (
    \<open>(_ :/ _ \<circ>\<^sub>C\<^sub>F _ \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<index> _ :/ _ \<mapsto>\<^sub>C _ \<mapsto>\<^sub>C _ : _ \<mapsto>\<mapsto>\<^sub>C _)\<close> 
    [51, 51, 51, 51, 51, 51, 51, 51, 51] 51
  )
translations "\<epsilon> : \<GG> \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT> : \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C (\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C \<DD>)" \<rightleftharpoons> 
  "CONST is_cat_rKe_preserves \<alpha> \<BB> \<CC> \<AA> \<DD> \<KK> \<TT> \<GG> \<HH> \<epsilon>"

locale is_cat_lKe_preserves =
  is_cat_lKe \<alpha> \<BB> \<CC> \<AA> \<KK> \<TT> \<FF> \<eta> + is_functor \<alpha> \<AA> \<DD> \<HH>
  for \<alpha> \<BB> \<CC> \<AA> \<DD> \<KK> \<TT> \<FF> \<HH> \<eta> +
  assumes cat_lKe_preserves:
    "\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta> : \<HH> \<circ>\<^sub>C\<^sub>F \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> (\<HH> \<circ>\<^sub>C\<^sub>F \<FF>) \<circ>\<^sub>C\<^sub>F \<KK> : \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C \<DD>"

syntax "_is_cat_lKe_preserves" :: 
  "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (
    \<open>(_ :/ _ \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<index> _ \<circ>\<^sub>C\<^sub>F _ :/ _ \<mapsto>\<^sub>C _ \<mapsto>\<^sub>C _ : _ \<mapsto>\<mapsto>\<^sub>C _)\<close> 
    [51, 51, 51, 51, 51, 51, 51, 51, 51] 51
  )
translations "\<eta> : \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<FF> \<circ>\<^sub>C\<^sub>F \<KK> : \<BB> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C (\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C \<DD>)" \<rightleftharpoons>
  "CONST is_cat_lKe_preserves \<alpha> \<BB> \<CC> \<AA> \<DD> \<KK> \<TT> \<FF> \<HH> \<eta>"


text\<open>Rules.\<close>

lemma (in is_cat_rKe_preserves) is_cat_rKe_preserves_axioms':
  assumes "\<alpha>' = \<alpha>"
    and "\<GG>' = \<GG>"
    and "\<KK>' = \<KK>"
    and "\<TT>' = \<TT>"
    and "\<HH>' = \<HH>"
    and "\<BB>' = \<BB>"
    and "\<AA>' = \<AA>"
    and "\<CC>' = \<CC>"
    and "\<DD>' = \<DD>"
  shows "\<epsilon> : \<GG>' \<circ>\<^sub>C\<^sub>F \<KK>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>'\<^esub> \<TT>' : \<BB>' \<mapsto>\<^sub>C \<CC>' \<mapsto>\<^sub>C (\<HH>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C \<DD>')"
  unfolding assms by (rule is_cat_rKe_preserves_axioms)

mk_ide rf is_cat_rKe_preserves_def[unfolded is_cat_rKe_preserves_axioms_def]
  |intro is_cat_rKe_preservesI|
  |dest is_cat_rKe_preservesD[dest]|
  |elim is_cat_rKe_preservesE[elim]|

lemmas [cat_Kan_cs_intros] = is_cat_rKeD(1-3)

lemma (in is_cat_lKe_preserves) is_cat_lKe_preserves_axioms':
  assumes "\<alpha>' = \<alpha>"
    and "\<FF>' = \<FF>"
    and "\<KK>' = \<KK>"
    and "\<TT>' = \<TT>"
    and "\<HH>' = \<HH>"
    and "\<BB>' = \<BB>"
    and "\<AA>' = \<AA>"
    and "\<CC>' = \<CC>"
    and "\<DD>' = \<DD>"
  shows "\<eta> : \<TT>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>' : \<BB>' \<mapsto>\<^sub>C \<CC>' \<mapsto>\<^sub>C (\<HH>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C \<DD>')"
  unfolding assms by (rule is_cat_lKe_preserves_axioms)

mk_ide rf is_cat_lKe_preserves_def[unfolded is_cat_lKe_preserves_axioms_def]
  |intro is_cat_lKe_preservesI|
  |dest is_cat_lKe_preservesD[dest]|
  |elim is_cat_lKe_preservesE[elim]|

lemmas [cat_Kan_cs_intros] = is_cat_lKe_preservesD(1-3)


text\<open>Duality.\<close>

lemma (in is_cat_rKe_preserves) is_cat_rKe_preserves_op:
  "op_ntcf \<epsilon> :
    op_cf \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> op_cf \<GG> \<circ>\<^sub>C\<^sub>F op_cf \<KK> :
    op_cat \<BB> \<mapsto>\<^sub>C op_cat \<CC> \<mapsto>\<^sub>C (op_cf \<HH> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C op_cat \<DD>)"
proof(intro is_cat_lKe_preservesI)
  from cat_rKe_preserves show "op_cf \<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf \<epsilon> :
    op_cf \<HH> \<circ>\<^sub>C\<^sub>F op_cf \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> (op_cf \<HH> \<circ>\<^sub>C\<^sub>F op_cf \<GG>) \<circ>\<^sub>C\<^sub>F op_cf \<KK> :
    op_cat \<BB> \<mapsto>\<^sub>C op_cat \<CC> \<mapsto>\<^sub>C op_cat \<DD>"
    by (cs_concl_step op_ntcf_cf_ntcf_comp[symmetric])
      (cs_concl cs_simp: cat_op_simps cs_intro: cat_op_intros)
qed (cs_concl cs_simp: cat_op_simps cs_intro: cat_op_intros)+

lemma (in is_cat_rKe_preserves) is_cat_lKe_preserves_op'[cat_op_intros]:
  assumes "\<TT>' = op_cf \<TT>"
    and "\<GG>' = op_cf \<GG>"
    and "\<KK>' = op_cf \<KK>"
    and "\<BB>' = op_cat \<BB>"
    and "\<AA>' = op_cat \<AA>"
    and "\<CC>' = op_cat \<CC>"
    and "\<DD>' = op_cat \<DD>"
    and "\<HH>' = op_cf \<HH>"
  shows "op_ntcf \<epsilon> :
    \<TT>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<GG>' \<circ>\<^sub>C\<^sub>F \<KK>' : \<BB>' \<mapsto>\<^sub>C \<CC>' \<mapsto>\<^sub>C (\<HH>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C \<DD>')"
  unfolding assms by (rule is_cat_rKe_preserves_op)

lemmas [cat_op_intros] = is_cat_rKe_preserves.is_cat_lKe_preserves_op'

lemma (in is_cat_lKe_preserves) is_cat_rKe_preserves_op:
  "op_ntcf \<eta> :
    op_cf \<FF> \<circ>\<^sub>C\<^sub>F op_cf \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> op_cf \<TT> :
    op_cat \<BB> \<mapsto>\<^sub>C op_cat \<CC> \<mapsto>\<^sub>C (op_cf \<HH> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C op_cat \<DD>)"
proof(intro is_cat_rKe_preservesI)
  from cat_lKe_preserves show "op_cf \<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf \<eta> :
    (op_cf \<HH> \<circ>\<^sub>C\<^sub>F op_cf \<FF>) \<circ>\<^sub>C\<^sub>F op_cf \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> op_cf \<HH> \<circ>\<^sub>C\<^sub>F op_cf \<TT> :
    op_cat \<BB> \<mapsto>\<^sub>C op_cat \<CC> \<mapsto>\<^sub>C op_cat \<DD>"
    by (cs_concl_step op_ntcf_cf_ntcf_comp[symmetric])
      (cs_concl cs_simp: cat_op_simps cs_intro: cat_op_intros)
qed (cs_concl cs_simp: cat_op_simps cs_intro: cat_op_intros)+

lemma (in is_cat_lKe_preserves) is_cat_rKe_preserves_op'[cat_op_intros]:
  assumes "\<TT>' = op_cf \<TT>"
    and "\<FF>' = op_cf \<FF>"
    and "\<KK>' = op_cf \<KK>"
    and "\<HH>' = op_cf \<HH>"
    and "\<BB>' = op_cat \<BB>"
    and "\<AA>' = op_cat \<AA>"
    and "\<CC>' = op_cat \<CC>"
    and "\<DD>' = op_cat \<DD>"
  shows "op_ntcf \<eta> :
    \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT>' : \<BB>' \<mapsto>\<^sub>C \<CC>' \<mapsto>\<^sub>C (\<HH>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C \<DD>')"
  unfolding assms by (rule is_cat_rKe_preserves_op)



subsection\<open>All concepts are Kan extensions\<close>


text\<open>
Background information for this subsection is provided in 
Chapter X-7 in \cite{mac_lane_categories_2010}
and section 6.5 in \cite{riehl_category_2016}. 
It should be noted that only the connections between the Kan extensions,
limits and adjunctions are exposed (an alternative proof of the Yoneda
lemma using Kan extensions is not provided in the context of this work).
\<close>


subsubsection\<open>Limits\<close>

lemma cat_rKe_is_cat_limit:
  \<comment>\<open>The statement of the theorem is similar to the statement of a part of
    Theorem 1 in Chapter X-7 in \cite{mac_lane_categories_2010}
    or Proposition 6.5.1 in \cite{riehl_category_2016}.\<close>
  assumes "\<epsilon> : \<GG> \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT> : \<BB> \<mapsto>\<^sub>C cat_1 \<aa> \<ff> \<mapsto>\<^sub>C \<AA>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "\<epsilon> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-

  interpret \<epsilon>: is_cat_rKe \<alpha> \<BB> \<open>cat_1 \<aa> \<ff>\<close> \<AA> \<KK> \<TT> \<GG> \<epsilon> by (rule assms(1))  
  interpret \<TT>: is_tm_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))
  
  from cat_1_components(1) have \<aa>: "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (auto simp: \<epsilon>.AG.HomCod.cat_in_Obj_in_Vset)
  from cat_1_components(2) have \<ff>: "\<ff> \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (auto simp: \<epsilon>.AG.HomCod.cat_in_Arr_in_Vset)

  have \<KK>_def: "\<KK> = cf_const \<BB> (cat_1 \<aa> \<ff>) \<aa>"
    by (rule cf_const_if_HomCod_is_cat_1) 
      (cs_concl cs_intro: cat_cs_intros)
  have \<GG>\<KK>_def: "\<GG> \<circ>\<^sub>C\<^sub>F \<KK> = cf_const \<BB> \<AA> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)"
    by
      (
        cs_concl
          cs_simp: cat_1_components(1) \<KK>_def cat_cs_simps 
          cs_intro: V_cs_intros cat_cs_intros
      )

  interpret \<epsilon>: is_tm_ntcf \<alpha> \<BB> \<AA> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<KK>\<close> \<TT> \<epsilon> 
    by 
      (
        intro is_tm_ntcfI' assms(2) \<epsilon>.ntcf_rKe.is_ntcf_axioms, 
        unfold \<GG>\<KK>_def
      )
      (
        cs_concl 
          cs_simp: cat_cs_simps cs_intro: cat_small_cs_intros cat_cs_intros
      )

  show "\<epsilon> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  proof(intro is_cat_limitI' is_cat_coneI)

    show "\<epsilon> : cf_const \<BB> \<AA> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
    proof(intro is_tm_ntcfI' \<epsilon>.ntcf_rKe.is_ntcf_axioms[unfolded \<GG>\<KK>_def])
      from assms(2) show "cf_const \<BB> \<AA> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>) : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
        by (cs_concl cs_intro: cat_small_cs_intros cat_cs_intros)
    qed (rule assms(2))

    fix u' r' assume prems: "u' : r' <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"

    interpret u': is_cat_cone \<alpha> r' \<BB> \<AA> \<TT> u' by (rule prems)

    have \<GG>_def: "\<GG> = cf_const (cat_1 \<aa> \<ff>) \<AA> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)"
      by (rule cf_const_if_HomDom_is_cat_1[OF \<epsilon>.Ran.is_functor_axioms])

    from prems have const_r': "cf_const (cat_1 \<aa> \<ff>) \<AA> r' : cat_1 \<aa> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps cs_intro: cat_lim_cs_intros cat_cs_intros
        )

    have cf_comp_cf_const_r_\<KK>_def: 
      "cf_const (cat_1 \<aa> \<ff>) \<AA> r' \<circ>\<^sub>C\<^sub>F \<KK> = cf_const \<BB> \<AA> r'"
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps \<KK>_def
            cs_intro: cat_cs_intros cat_lim_cs_intros
        )

    from \<epsilon>.cat_rKe_unique[
        OF const_r', unfolded cf_comp_cf_const_r_\<KK>_def, OF u'.is_ntcf_axioms
        ] 
    obtain \<sigma> 
      where \<sigma>: "\<sigma> : cf_const (cat_1 \<aa> \<ff>) \<AA> r' \<mapsto>\<^sub>C\<^sub>F \<GG> : cat_1 \<aa> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        and u'_def: "u' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)"
        and unique_\<sigma>: "\<And>\<sigma>'.
          \<lbrakk>
            \<sigma>' : cf_const (cat_1 \<aa> \<ff>) \<AA> r' \<mapsto>\<^sub>C\<^sub>F \<GG> : cat_1 \<aa> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>;
            u' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)
          \<rbrakk> \<Longrightarrow> \<sigma>' = \<sigma>"
      by auto

    interpret \<sigma>: is_ntcf \<alpha> \<open>cat_1 \<aa> \<ff>\<close> \<AA> \<open>cf_const (cat_1 \<aa> \<ff>) \<AA> r'\<close> \<GG> \<sigma>
      by (rule \<sigma>)
    
    show "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr> \<and> u' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<BB> \<AA> f'"
    proof(intro ex1I conjI; (elim conjE)?)
      fix f' assume prems': 
        "f' : r' \<mapsto>\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>" "u' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<BB> \<AA> f'"
      from prems'(1) have "ntcf_const (cat_1 \<aa> \<ff>) \<AA> f' :
        cf_const (cat_1 \<aa> \<ff>) \<AA> r' \<mapsto>\<^sub>C\<^sub>F \<GG> : cat_1 \<aa> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        by (subst \<GG>_def) 
          (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      moreover then have "u' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (ntcf_const (cat_1 \<aa> \<ff>) \<AA> f' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps prems'(2) \<KK>_def cs_intro: cat_cs_intros
          )
      ultimately have \<sigma>_def: "\<sigma> = ntcf_const (cat_1 \<aa> \<ff>) \<AA> f'"
        by (auto simp: unique_\<sigma>[symmetric])
      show "f' = \<sigma>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps \<sigma>_def cs_intro: cat_cs_intros)
    qed (cs_concl cs_simp: cat_cs_simps u'_def \<KK>_def cs_intro: cat_cs_intros)+

  qed (cs_concl cs_simp: \<KK>_def cs_intro: cat_cs_intros)

qed

lemma cat_lKe_is_cat_colimit:
  assumes "\<eta> : \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<FF> \<circ>\<^sub>C\<^sub>F \<KK> : \<BB> \<mapsto>\<^sub>C cat_1 \<aa> \<ff> \<mapsto>\<^sub>C \<AA>"
    and "\<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "\<eta> : \<TT> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  interpret \<eta>: is_cat_lKe \<alpha> \<BB> \<open>cat_1 \<aa> \<ff>\<close> \<AA> \<KK> \<TT> \<FF> \<eta> by (rule assms(1))  
  interpret \<TT>: is_tm_functor \<alpha> \<BB> \<AA> \<TT> by (rule assms(2))
  from cat_1_components(1) have \<aa>: "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (auto simp: \<eta>.AG.HomCod.cat_in_Obj_in_Vset)
  from cat_1_components(2) have \<ff>: "\<ff> \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (auto simp: \<eta>.AG.HomCod.cat_in_Arr_in_Vset)
  show ?thesis
    by 
      (
        rule is_cat_limit.is_cat_colimit_op
          [
            OF cat_rKe_is_cat_limit[
              OF \<eta>.is_cat_rKe_op[unfolded \<eta>.AG.cat_1_op[OF \<aa> \<ff>]] 
              \<TT>.is_tm_functor_op
              ], 
            unfolded cat_op_simps
          ]
      )
qed

lemma cat_limit_is_rKe:
  \<comment>\<open>The statement of the theorem is similar to the statement of a part of
    Theorem 1 in Chapter X-7 in \cite{mac_lane_categories_2010} 
    or Proposition 6.5.1 in \cite{riehl_category_2016}.\<close>
  assumes "\<epsilon> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>i\<^sub>m \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_1 \<aa> \<ff>"
    and "\<GG> : cat_1 \<aa> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "\<epsilon> : \<GG> \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT> : \<BB> \<mapsto>\<^sub>C cat_1 \<aa> \<ff> \<mapsto>\<^sub>C \<AA>"
proof-

  interpret \<epsilon>: is_cat_limit \<alpha> \<BB> \<AA> \<TT> \<open>\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>\<close> \<epsilon> by (rule assms)
  interpret \<KK>: is_functor \<alpha> \<BB> \<open>cat_1 \<aa> \<ff>\<close> \<KK> by (rule assms(2))
  interpret \<GG>: is_functor \<alpha> \<open>cat_1 \<aa> \<ff>\<close> \<AA> \<GG> by (rule assms(3))

  show ?thesis
  proof(rule is_cat_rKeI')

    note \<KK>_def = cf_const_if_HomCod_is_cat_1[OF assms(2)]
    note \<GG>_def = cf_const_if_HomDom_is_cat_1[OF assms(3)]

    have \<GG>\<KK>_def: "\<GG> \<circ>\<^sub>C\<^sub>F \<KK> = cf_const \<BB> \<AA> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)"
      by (subst \<KK>_def, use nothing in \<open>subst \<GG>_def\<close>)
        (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

    show "\<epsilon> : \<GG> \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
      by (cs_concl cs_simp: cat_cs_simps \<GG>\<KK>_def cs_intro: cat_cs_intros)
    fix \<GG>' \<epsilon>' assume prems: 
      "\<GG>' : cat_1 \<aa> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      "\<epsilon>' : \<GG>' \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"

    interpret is_functor \<alpha> \<open>cat_1 \<aa> \<ff>\<close> \<AA> \<GG>' by (rule prems(1))
  
    note \<GG>'_def = cf_const_if_HomDom_is_cat_1[OF prems(1)]

    from prems(2) have \<epsilon>': 
      "\<epsilon>' : cf_const \<BB> \<AA> (\<GG>'\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>) \<mapsto>\<^sub>C\<^sub>F \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      unfolding \<KK>_def 
      by (subst (asm) \<GG>'_def)
        (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from prems(2) have "\<epsilon>' : \<GG>'\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr> <\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>n\<^sub>e \<TT> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by (intro is_cat_coneI is_tm_ntcfI' \<epsilon>')
        (cs_concl cs_intro: cat_small_cs_intros cat_cs_intros)+

    from \<epsilon>.cat_lim_unique_cone[OF this] obtain f'
      where f': "f' : \<GG>'\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>"
        and \<epsilon>_def: "\<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<BB> \<AA> f'"
        and unique_f':
          "\<lbrakk>
            f'' : \<GG>'\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>;
            \<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<BB> \<AA> f''
          \<rbrakk> \<Longrightarrow> f'' = f'"
        for f''
      by metis

    show "\<exists>!\<sigma>.
      \<sigma> : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<GG> : cat_1 \<aa> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> \<and> \<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)"
    proof(intro ex1I conjI; (elim conjE)?)  
      from f' show 
        "ntcf_const (cat_1 \<aa> \<ff>) \<AA> f' : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<GG> : cat_1 \<aa> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        by (subst \<GG>'_def, use nothing in \<open>subst \<GG>_def\<close>) 
          (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      then show "\<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (ntcf_const (cat_1 \<aa> \<ff>) \<AA> f' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)"
        by (cs_concl cs_simp: cat_cs_simps \<epsilon>_def \<KK>_def cs_intro: cat_cs_intros)
      fix \<sigma> assume prems:
        "\<sigma> : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<GG> : cat_1 \<aa> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        "\<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)"
      interpret \<sigma>: is_ntcf \<alpha> \<open>cat_1 \<aa> \<ff>\<close> \<AA> \<GG>' \<GG> \<sigma> by (rule prems(1))
      have "\<sigma>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<rparr> : \<GG>'\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      moreover have "\<epsilon>' = \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<BB> \<AA> (\<sigma>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<rparr>)"
        by
          (
            cs_concl
              cs_simp: cat_cs_simps prems(2) \<KK>_def cs_intro: cat_cs_intros
          )
      ultimately have \<sigma>\<aa>: "\<sigma>\<lparr>NTMap\<rparr>\<lparr>\<aa>\<rparr> = f'" by (rule unique_f')
      show "\<sigma> = ntcf_const (cat_1 \<aa> \<ff>) \<AA> f'"
      proof(rule ntcf_eqI)
        from f' show 
          "ntcf_const (cat_1 \<aa> \<ff>) \<AA> f' : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<GG> : cat_1 \<aa> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
          by (subst \<GG>'_def, use nothing in \<open>subst \<GG>_def\<close>)
            (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        have dom_lhs: "\<D>\<^sub>\<circ> (\<sigma>\<lparr>NTMap\<rparr>) = cat_1 \<aa> \<ff>\<lparr>Obj\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro:cat_cs_intros)
        have dom_rhs: "\<D>\<^sub>\<circ> (ntcf_const (cat_1 \<aa> \<ff>) \<AA> f'\<lparr>NTMap\<rparr>) = cat_1 \<aa> \<ff>\<lparr>Obj\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro:cat_cs_intros)
        show "\<sigma>\<lparr>NTMap\<rparr> = ntcf_const (cat_1 \<aa> \<ff>) \<AA> f'\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          fix a assume prems: "a \<in>\<^sub>\<circ> cat_1 \<aa> \<ff>\<lparr>Obj\<rparr>"
          then have a_def: "a = \<aa>" unfolding cat_1_components by simp
          from f' show "\<sigma>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = ntcf_const (cat_1 \<aa> \<ff>) \<AA> f'\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
            unfolding a_def \<sigma>\<aa>
            by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        qed (auto intro: cat_cs_intros)
      qed (simp_all add: prems)
    qed
  qed (auto simp: assms)

qed

lemma cat_colimit_is_lKe:
  assumes "\<eta> : \<TT> >\<^sub>C\<^sub>F\<^sub>.\<^sub>c\<^sub>o\<^sub>l\<^sub>i\<^sub>m \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_1 \<aa> \<ff>"
    and "\<FF> : cat_1 \<aa> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "\<eta> : \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<FF> \<circ>\<^sub>C\<^sub>F \<KK> : \<BB> \<mapsto>\<^sub>C cat_1 \<aa> \<ff> \<mapsto>\<^sub>C \<AA>"
proof-
  interpret \<eta>: is_cat_colimit \<alpha> \<BB> \<AA> \<TT> \<open>\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>\<close> \<eta>
    by (rule assms(1))
  interpret \<KK>: is_functor \<alpha> \<BB> \<open>cat_1 \<aa> \<ff>\<close> \<KK> by (rule assms(2))
  interpret \<FF>: is_functor \<alpha> \<open>cat_1 \<aa> \<ff>\<close> \<AA> \<FF> by (rule assms(3))
  from cat_1_components(1) have \<aa>: "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (auto simp: \<KK>.HomCod.cat_in_Obj_in_Vset)
  from cat_1_components(2) have \<ff>: "\<ff> \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (auto simp: \<KK>.HomCod.cat_in_Arr_in_Vset)
  have \<FF>\<aa>: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr> = op_cf \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>" unfolding cat_op_simps by simp
  note cat_1_op = \<eta>.cat_1_op[OF \<aa> \<ff>]
  show ?thesis
    by 
      (
        rule is_cat_rKe.is_cat_lKe_op
          [
            OF cat_limit_is_rKe
              [
                OF 
                  \<eta>.is_cat_limit_op[unfolded \<FF>\<aa>]
                  \<KK>.is_functor_op[unfolded cat_1_op]
                  \<FF>.is_functor_op[unfolded cat_1_op]
              ],
            unfolded cat_op_simps cat_1_op
          ]
      )
qed


subsubsection\<open>Adjoints\<close>

lemma (in is_cf_adjunction) cf_adjunction_counit_is_rKe:
  \<comment>\<open>The statement of the theorem is similar to the statement of a part of
    Theorem 2 in Chapter X-7 in \cite{mac_lane_categories_2010}
    or Proposition 6.5.2 in \cite{riehl_category_2016}.
    The proof follows (approximately) the proof in \cite{riehl_category_2016}.\<close>
  shows "\<epsilon>\<^sub>C \<Phi> : \<FF> \<circ>\<^sub>C\<^sub>F \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> cf_id \<DD> : \<DD> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C \<DD>"
proof-

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp

  note exp_adj = cf_adj_exp_cf_cat_exp_cf_cat[OF \<beta> \<alpha>\<beta> R.category_axioms]

  let ?\<eta> = \<open>\<eta>\<^sub>C \<Phi>\<close>
  let ?\<epsilon> = \<open>\<epsilon>\<^sub>C \<Phi>\<close>
  let ?\<DD>\<eta> = \<open>exp_cat_ntcf \<alpha> \<DD> ?\<eta>\<close>
  let ?\<DD>\<FF> = \<open>exp_cat_cf \<alpha> \<DD> \<FF>\<close>
  let ?\<DD>\<GG> = \<open>exp_cat_cf \<alpha> \<DD> \<GG>\<close>
  let ?\<DD>\<DD> = \<open>cat_FUNCT \<alpha> \<DD> \<DD>\<close>
  let ?\<CC>\<DD> = \<open>cat_FUNCT \<alpha> \<CC> \<DD>\<close>
  let ?adj_\<DD>\<eta> = \<open>cf_adjunction_of_unit \<beta> ?\<DD>\<GG> ?\<DD>\<FF> ?\<DD>\<eta>\<close>

  interpret \<DD>\<eta>: is_cf_adjunction \<beta> ?\<CC>\<DD> ?\<DD>\<DD> ?\<DD>\<GG> ?\<DD>\<FF> ?adj_\<DD>\<eta> by (rule exp_adj)

  show ?thesis
  proof(intro is_cat_rKeI)
    have id_\<DD>: "cf_map (cf_id \<DD>) \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<DD> \<DD>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl
            cs_simp: cat_FUNCT_components(1)
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    then have exp_id_\<DD>: 
      "exp_cat_cf \<alpha> \<DD> \<FF>\<lparr>ObjMap\<rparr>\<lparr>cf_map (cf_id \<DD>)\<rparr> = cf_map \<FF>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps cs_intro: cat_cs_intros
        )
    have \<FF>: "cf_map \<FF> \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<CC> \<DD>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_FUNCT_components(1)
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    have \<epsilon>: "ntcf_arrow (\<epsilon>\<^sub>C \<Phi>) \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<DD> \<DD>"
      by (cs_concl cs_intro: cat_FUNCT_cs_intros adj_cs_intros)
    have \<DD>\<DD>: "category \<beta> (cat_FUNCT \<alpha> \<DD> \<DD>)"
      by (cs_concl cs_intro: cat_cs_intros)
    have \<CC>\<DD>: "category \<beta> (cat_FUNCT \<alpha> \<CC> \<DD>)"
      by (cs_concl cs_intro: cat_cs_intros)

    from 
      \<epsilon> \<FF> \<alpha>\<beta> id_\<DD> 
      \<DD>\<DD> \<CC>\<DD> LR.is_functor_axioms RL.is_functor_axioms R.cat_cf_id_is_functor
      NT.is_iso_ntcf_axioms 
    have \<epsilon>_id_\<DD>: "\<epsilon>\<^sub>C ?adj_\<DD>\<eta>\<lparr>NTMap\<rparr>\<lparr>cf_map (cf_id \<DD>)\<rparr> = ntcf_arrow ?\<epsilon>"
      by
        (
          cs_concl
            cs_simp:
              cat_Set_the_inverse[symmetric]
              cat_op_simps
              cat_cs_simps
              cat_FUNCT_cs_simps
              adj_cs_simps 
            cs_intro:
              \<DD>\<eta>.NT.iso_ntcf_is_arr_isomorphism''
              cat_op_intros
              adj_cs_intros
              cat_small_cs_intros
              cat_cs_intros
              cat_FUNCT_cs_intros
              cat_prod_cs_intros
        )      
   show "universal_arrow_fo ?\<DD>\<GG> (cf_map (cf_id \<DD>)) (cf_map \<FF>) (ntcf_arrow ?\<epsilon>)"
      by 
        (
          rule is_cf_adjunction.cf_adjunction_counit_component_is_ua_fo[
            OF exp_adj id_\<DD>, unfolded exp_id_\<DD> \<epsilon>_id_\<DD>
            ]
        )
  qed (cs_concl cs_intro: cat_cs_intros adj_cs_intros)+

qed

lemma (in is_cf_adjunction) cf_adjunction_unit_is_lKe:
  shows "\<eta>\<^sub>C \<Phi> : cf_id \<CC> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<^sub>C \<DD> \<mapsto>\<^sub>C \<CC>"
  by 
    (
      rule is_cat_rKe.is_cat_lKe_op
        [
          OF is_cf_adjunction.cf_adjunction_counit_is_rKe
            [
              OF is_cf_adjunction_op,
              folded op_ntcf_cf_adjunction_unit op_cf_cf_id
            ],
          unfolded 
            cat_op_simps ntcf_op_ntcf_op_ntcf[OF cf_adjunction_unit_is_ntcf]
        ]
    )

lemma cf_adjunction_if_lKe_preserves:
  \<comment>\<open>The statement of the theorem is similar to the statement of a part of
    Theorem 2 in Chapter X-7 in \cite{mac_lane_categories_2010}
    or Proposition 6.5.2 in \cite{riehl_category_2016}.\<close>
  assumes "\<eta> : cf_id \<DD> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<FF> \<circ>\<^sub>C\<^sub>F \<GG> : \<DD> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C (\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C \<CC>)"
  shows "cf_adjunction_of_unit \<alpha> \<GG> \<FF> \<eta> : \<GG> \<rightleftharpoons>\<^sub>C\<^sub>F \<FF> : \<DD> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-

  interpret \<eta>: is_cat_lKe_preserves \<alpha> \<DD> \<CC> \<DD> \<CC> \<GG> \<open>cf_id \<DD>\<close> \<FF> \<GG> \<eta> 
    by (rule assms)

  from \<eta>.cat_lKe_preserves interpret \<GG>\<eta>:
    is_cat_lKe \<alpha> \<DD> \<CC> \<CC> \<GG> \<GG> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> \<open>\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>\<close>
    by (cs_prems cs_simp: cat_cs_simps)

  from 
    \<GG>\<eta>.cat_lKe_unique
      [
        OF \<eta>.AG.HomCod.cat_cf_id_is_functor,
        unfolded \<eta>.AG.cf_cf_comp_cf_id_left,
        OF \<eta>.AG.cf_ntcf_id_is_ntcf
      ]
  obtain \<epsilon> where \<epsilon>: "\<epsilon> : \<GG> \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F cf_id \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and ntcf_id_\<GG>_def: "ntcf_id \<GG> = \<epsilon> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>)"
    by metis
  interpret \<epsilon>: is_ntcf \<alpha> \<CC> \<CC> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> \<open>cf_id \<CC>\<close> \<epsilon> by (rule \<epsilon>)
  
  show ?thesis
  proof(rule counit_unit_is_cf_adjunction)

    show [cat_cs_simps]: "\<epsilon> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>) = ntcf_id \<GG>"
      by (rule ntcf_id_\<GG>_def[symmetric])

    have \<eta>_def: "\<eta> = (ntcf_id \<FF> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps ntcf_id_cf_comp[symmetric] 
            cs_intro: cat_cs_intros
        )
    note [cat_cs_simps] = this[symmetric]

    let ?\<FF>\<epsilon>\<GG> = \<open>\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>\<close>
    let ?\<eta>\<FF>\<GG> = \<open>\<eta> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>\<close>
    let ?\<FF>\<GG>\<eta> = \<open>\<FF> \<circ>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>\<close>

    have "(?\<FF>\<epsilon>\<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<eta>\<FF>\<GG>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta> = (?\<FF>\<epsilon>\<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<FF>\<GG>\<eta>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>"
    proof(rule ntcf_eqI)
      have dom_lhs: "\<D>\<^sub>\<circ> (((?\<FF>\<epsilon>\<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<eta>\<FF>\<GG>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>)\<lparr>NTMap\<rparr>) = \<DD>\<lparr>Obj\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      have dom_rhs: "\<D>\<^sub>\<circ> (((?\<FF>\<epsilon>\<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<FF>\<GG>\<eta>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>)\<lparr>NTMap\<rparr>) = \<DD>\<lparr>Obj\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      note is_ntcf.ntcf_Comp_commute[cat_cs_simps del]
      note category.cat_Comp_assoc[cat_cs_simps del]
      show
        "((?\<FF>\<epsilon>\<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<eta>\<FF>\<GG>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>)\<lparr>NTMap\<rparr> =
          ((?\<FF>\<epsilon>\<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<FF>\<GG>\<eta>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>)\<lparr>NTMap\<rparr>"
      proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
        fix a assume "a \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
        then show
          "((?\<FF>\<epsilon>\<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<eta>\<FF>\<GG>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
            ((?\<FF>\<epsilon>\<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<FF>\<GG>\<eta>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
          by
            (
              cs_concl 
                cs_simp: cat_cs_simps \<eta>.ntcf_lKe.ntcf_Comp_commute[symmetric]
                cs_intro: cat_cs_intros
            )
      qed (cs_concl cs_intro: cat_cs_intros)+
    qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+
    also have "\<dots> = (ntcf_id \<FF> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>"
      by
        (
          cs_concl
            cs_simp:
              cat_cs_simps
              cf_comp_cf_ntcf_comp_assoc
              cf_ntcf_comp_ntcf_cf_comp_assoc
              cf_ntcf_comp_ntcf_vcomp[symmetric]
            cs_intro: cat_cs_intros
        )
    also have "\<dots> = \<eta>" by (cs_concl cs_simp: cat_cs_simps)
    finally have "(?\<FF>\<epsilon>\<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<eta>\<FF>\<GG>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta> = \<eta>" by simp
    then have \<eta>_def':
      "\<eta> = (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<eta> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>"
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps ntcf_vcomp_ntcf_cf_comp[symmetric] 
            cs_intro: cat_cs_intros
        )+
  
    have \<FF>\<epsilon>\<eta>\<FF>:
      "\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<eta> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>) : \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

    from \<eta>.cat_lKe_unique[OF \<eta>.Lan.is_functor_axioms \<eta>.ntcf_lKe.is_ntcf_axioms]
    obtain \<sigma> where
      "\<lbrakk> \<sigma>' : \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>; \<eta> = \<sigma>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta> \<rbrakk> \<Longrightarrow> 
        \<sigma>' = \<sigma>"
      for \<sigma>'
      by metis
  
    from this[OF \<eta>.Lan.cf_ntcf_id_is_ntcf \<eta>_def] this[OF \<FF>\<epsilon>\<eta>\<FF> \<eta>_def'] show
      "\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<eta> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>) = ntcf_id \<FF>"
      by simp

  qed (cs_concl cs_intro: cat_cs_intros)+

qed

lemma cf_adjunction_if_rKe_preserves:
  assumes "\<epsilon> : \<FF> \<circ>\<^sub>C\<^sub>F \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> cf_id \<DD> : \<DD> \<mapsto>\<^sub>C \<CC> \<mapsto>\<^sub>C (\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C \<CC>)"
  shows "cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
proof-
  interpret \<epsilon>: is_cat_rKe_preserves \<alpha> \<DD> \<CC> \<DD> \<CC> \<GG> \<open>cf_id \<DD>\<close> \<FF> \<GG> \<epsilon> 
    by (rule assms)
  have "op_cf (cf_id \<DD>) = cf_id (op_cat \<DD>)" unfolding cat_op_simps by simp
  show ?thesis
    by 
      (
        rule is_cf_adjunction.is_cf_adjunction_op
          [
            OF cf_adjunction_if_lKe_preserves[
              OF \<epsilon>.is_cat_rKe_preserves_op[unfolded op_cf_cf_id]
              ], 
            folded cf_adjunction_of_counit_def, 
            unfolded cat_op_simps
          ]
      )
qed

text\<open>\newpage\<close>

end