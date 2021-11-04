(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Adjoints\<close>
theory CZH_UCAT_Adjoints
  imports 
    CZH_UCAT_Universal
    CZH_Elementary_Categories.CZH_ECAT_Yoneda
begin



subsection\<open>Background\<close>

named_theorems adj_cs_simps
named_theorems adj_cs_intros
named_theorems adj_field_simps

definition AdjLeft :: V where [adj_field_simps]: "AdjLeft = 0"
definition AdjRight :: V where [adj_field_simps]: "AdjRight = 1\<^sub>\<nat>"
definition AdjNT :: V where [adj_field_simps]: "AdjNT = 2\<^sub>\<nat>"



subsection\<open>Definition and elementary properties\<close>


text\<open>
See subsection 2.1 in \cite{bodo_categories_1970} or Chapter IV-1 in
\cite{mac_lane_categories_2010}.
\<close>

locale is_cf_adjunction =
  \<Z> \<alpha> +
  vfsequence \<Phi> +
  L: category \<alpha> \<CC> +
  R: category \<alpha> \<DD> +
  LR: is_functor \<alpha> \<CC> \<DD> \<FF> +
  RL: is_functor \<alpha> \<DD> \<CC> \<GG> +
  NT: is_iso_ntcf 
    \<alpha> 
    \<open>op_cat \<CC> \<times>\<^sub>C \<DD>\<close> 
    \<open>cat_Set \<alpha>\<close> 
    \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>-,-)\<close> 
    \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<close> 
    \<open>\<Phi>\<lparr>AdjNT\<rparr>\<close>
    for \<alpha> \<CC> \<DD> \<FF> \<GG> \<Phi> +
  assumes cf_adj_length[adj_cs_simps]: "vcard \<Phi> = 3\<^sub>\<nat>"
    and cf_adj_AdjLeft[adj_cs_simps]: "\<Phi>\<lparr>AdjLeft\<rparr> = \<FF>"
    and cf_adj_AdjRight[adj_cs_simps]: "\<Phi>\<lparr>AdjRight\<rparr> = \<GG>"

syntax "_is_cf_adjunction" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ : _ \<rightleftharpoons>\<^sub>C\<^sub>F _ : _ \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<Phi> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" \<rightleftharpoons> 
  "CONST is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG> \<Phi>"

lemmas [adj_cs_simps] = 
  is_cf_adjunction.cf_adj_length
  is_cf_adjunction.cf_adj_AdjLeft
  is_cf_adjunction.cf_adj_AdjRight


text\<open>Components.\<close>

lemma cf_adjunction_components[adj_cs_simps]:
  "[\<FF>, \<GG>, \<phi>]\<^sub>\<circ>\<lparr>AdjLeft\<rparr> = \<FF>"
  "[\<FF>, \<GG>, \<phi>]\<^sub>\<circ>\<lparr>AdjRight\<rparr> = \<GG>"
  "[\<FF>, \<GG>, \<phi>]\<^sub>\<circ>\<lparr>AdjNT\<rparr> = \<phi>"
  unfolding AdjLeft_def AdjRight_def AdjNT_def 
  by (simp_all add: nat_omega_simps)


text\<open>Rules.\<close>

lemma (in is_cf_adjunction) is_cf_adjunction_axioms'[adj_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<CC>' = \<CC>" and "\<DD>' = \<DD>" and "\<FF>' = \<FF>" and "\<GG>' = \<GG>"
  shows "\<Phi> : \<FF>' \<rightleftharpoons>\<^sub>C\<^sub>F \<GG>' : \<CC>' \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<DD>'"  
  unfolding assms by (rule is_cf_adjunction_axioms)

lemmas (in is_cf_adjunction) [adj_cs_intros] = is_cf_adjunction_axioms

mk_ide rf is_cf_adjunction_def[unfolded is_cf_adjunction_axioms_def]
  |intro is_cf_adjunctionI|
  |dest is_cf_adjunctionD[dest]|
  |elim is_cf_adjunctionE[elim]|

lemmas [adj_cs_intros] = is_cf_adjunctionD(3-6)

lemma (in is_cf_adjunction) cf_adj_is_iso_ntcf':
  assumes "\<FF>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>-,-)"
    and "\<GG>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)"
    and "\<AA>' = op_cat \<CC> \<times>\<^sub>C \<DD>"
    and "\<BB>' = cat_Set \<alpha>"
  shows "\<Phi>\<lparr>AdjNT\<rparr> : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (auto intro: cat_cs_intros)

lemmas [adj_cs_intros] = is_cf_adjunction.cf_adj_is_iso_ntcf'

lemma cf_adj_eqI:
  assumes "\<Phi> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<Phi>' : \<FF>' \<rightleftharpoons>\<^sub>C\<^sub>F \<GG>' : \<CC>' \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>'"
    and "\<CC> = \<CC>'"
    and "\<DD> = \<DD>'"
    and "\<FF> = \<FF>'"
    and "\<GG> = \<GG>'"
    and "\<Phi>\<lparr>AdjNT\<rparr> = \<Phi>'\<lparr>AdjNT\<rparr>"
  shows "\<Phi> = \<Phi>'"
proof-
  interpret \<Phi>: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG> \<Phi> by (rule assms(1))
  interpret \<Phi>': is_cf_adjunction \<alpha> \<CC>' \<DD>' \<FF>' \<GG>' \<Phi>' by (rule assms(2))
  show ?thesis
  proof(rule vsv_eqI)
    have dom: "\<D>\<^sub>\<circ> \<Phi> = 3\<^sub>\<nat>" by (cs_concl cs_simp: V_cs_simps adj_cs_simps)
    show "\<D>\<^sub>\<circ> \<Phi> = \<D>\<^sub>\<circ> \<Phi>'" by (cs_concl cs_simp: V_cs_simps adj_cs_simps dom)
    from assms(4-7) have sup: 
      "\<Phi>\<lparr>AdjLeft\<rparr> = \<Phi>'\<lparr>AdjLeft\<rparr>" 
      "\<Phi>\<lparr>AdjRight\<rparr> = \<Phi>'\<lparr>AdjRight\<rparr>" 
      "\<Phi>\<lparr>AdjNT\<rparr> = \<Phi>'\<lparr>AdjNT\<rparr>"  
      by (simp_all add: adj_cs_simps)
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<Phi> \<Longrightarrow> \<Phi>\<lparr>a\<rparr> = \<Phi>'\<lparr>a\<rparr>" for a 
      by (unfold dom, elim_in_numeral, insert sup) 
        (auto simp: adj_field_simps)
  qed (auto simp: \<Phi>.L.vsv_axioms \<Phi>'.vsv_axioms)
qed



subsection\<open>Opposite adjunction\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See \cite{kan_adjoint_1958} for further information.\<close>

abbreviation op_cf_adj_nt :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "op_cf_adj_nt \<CC> \<DD> \<phi> \<equiv> inv_ntcf (bnt_flip (op_cat \<CC>) \<DD> \<phi>)"

definition op_cf_adj :: "V \<Rightarrow> V"
  where "op_cf_adj \<Phi> =
    [
      op_cf (\<Phi>\<lparr>AdjRight\<rparr>),
      op_cf (\<Phi>\<lparr>AdjLeft\<rparr>),
      op_cf_adj_nt (\<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomDom\<rparr>) (\<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomCod\<rparr>) (\<Phi>\<lparr>AdjNT\<rparr>)
    ]\<^sub>\<circ>"

lemma op_cf_adj_components:
  shows "op_cf_adj \<Phi>\<lparr>AdjLeft\<rparr> = op_cf (\<Phi>\<lparr>AdjRight\<rparr>)"
    and "op_cf_adj \<Phi>\<lparr>AdjRight\<rparr> = op_cf (\<Phi>\<lparr>AdjLeft\<rparr>)"
    and "op_cf_adj \<Phi>\<lparr>AdjNT\<rparr> = 
      op_cf_adj_nt (\<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomDom\<rparr>) (\<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomCod\<rparr>) (\<Phi>\<lparr>AdjNT\<rparr>)"
  unfolding op_cf_adj_def adj_field_simps by (simp_all add: nat_omega_simps)

lemma (in is_cf_adjunction) op_cf_adj_components:
  shows "op_cf_adj \<Phi>\<lparr>AdjLeft\<rparr> = op_cf \<GG>"
    and "op_cf_adj \<Phi>\<lparr>AdjRight\<rparr> = op_cf \<FF>"
    and "op_cf_adj \<Phi>\<lparr>AdjNT\<rparr> = inv_ntcf (bnt_flip (op_cat \<CC>) \<DD> (\<Phi>\<lparr>AdjNT\<rparr>))"
  unfolding op_cf_adj_components by (simp_all add: cat_cs_simps adj_cs_simps)

lemmas [cat_op_simps] = is_cf_adjunction.op_cf_adj_components


text\<open>The opposite adjunction is an adjunction.\<close>

lemma (in is_cf_adjunction) is_cf_adjunction_op:
  \<comment>\<open>See comments in subsection 2.1 in \cite{bodo_categories_1970}.\<close>
  "op_cf_adj \<Phi> : op_cf \<GG> \<rightleftharpoons>\<^sub>C\<^sub>F op_cf \<FF> : op_cat \<DD> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
proof(intro is_cf_adjunctionI, unfold cat_op_simps, unfold op_cf_adj_components)
  show "vfsequence (op_cf_adj \<Phi>)" unfolding op_cf_adj_def by simp
  show "vcard (op_cf_adj \<Phi>) = 3\<^sub>\<nat>"
    unfolding op_cf_adj_def by (simp add: nat_omega_simps)
  note adj = is_cf_adjunctionD[OF is_cf_adjunction_axioms]
  from adj have f_\<phi>: "bnt_flip (op_cat \<CC>) \<DD> (\<Phi>\<lparr>AdjNT\<rparr>) :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<DD>(-,op_cf \<FF>-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(op_cf \<GG>-,-) :
    \<DD> \<times>\<^sub>C op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)
  show "op_cf_adj_nt \<CC> \<DD> (\<Phi>\<lparr>AdjNT\<rparr>) :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(op_cf \<GG>-,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<DD>(-,op_cf \<FF>-) :
    \<DD> \<times>\<^sub>C op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (rule CZH_ECAT_NTCF.iso_ntcf_is_arr_isomorphism(1)[OF f_\<phi>])
qed (auto intro: cat_cs_intros cat_op_intros)

lemmas is_cf_adjunction_op = 
  is_cf_adjunction.is_cf_adjunction_op

lemma (in is_cf_adjunction) is_cf_adjunction_op'[cat_op_intros]:
  assumes "\<GG>' = op_cf \<GG>"
    and "\<FF>' = op_cf \<FF>"
    and "\<DD>' = op_cat \<DD>"
    and "\<CC>' = op_cat \<CC>"
  shows "op_cf_adj \<Phi> : \<GG>' \<rightleftharpoons>\<^sub>C\<^sub>F \<FF>' : \<DD>' \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule is_cf_adjunction_op)

lemmas [cat_op_intros] = is_cf_adjunction.is_cf_adjunction_op'


text\<open>The operation of taking the opposite adjunction is an involution.\<close>

lemma (in is_cf_adjunction) cf_adjunction_op_cf_adj_op_cf_adj[cat_op_simps]:
  "op_cf_adj (op_cf_adj \<Phi>) = \<Phi>"
proof(rule cf_adj_eqI)
  show \<Phi>': "op_cf_adj (op_cf_adj \<Phi>) : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  proof(intro is_cf_adjunctionI)
    show "vfsequence (op_cf_adj (op_cf_adj \<Phi>))" unfolding op_cf_adj_def by simp
    from is_cf_adjunction_axioms show "op_cf_adj (op_cf_adj \<Phi>)\<lparr>AdjNT\<rparr> : 
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>-,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-) : 
      op_cat \<CC> \<times>\<^sub>C \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by
        (
          cs_concl cs_ist_simple
            cs_intro: cat_cs_intros cat_op_intros adj_cs_intros
            cs_simp: cat_cs_simps cat_op_simps
        )
    show "vcard (op_cf_adj (op_cf_adj \<Phi>)) = 3\<^sub>\<nat>"
      unfolding op_cf_adj_def by (simp add: nat_omega_simps)
    from is_cf_adjunction_axioms show "op_cf_adj (op_cf_adj \<Phi>)\<lparr>AdjLeft\<rparr> = \<FF>"
      by (cs_concl cs_simp: cat_op_simps cs_intro: cat_op_intros)
    from is_cf_adjunction_axioms show "op_cf_adj (op_cf_adj \<Phi>)\<lparr>AdjRight\<rparr> = \<GG>"
      by (cs_concl cs_simp: cat_op_simps cs_intro: cat_op_intros)
  qed (auto intro: cat_cs_intros)
  interpret \<Phi>': is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG> \<open>op_cf_adj (op_cf_adj \<Phi>)\<close> 
    by (rule \<Phi>')
  show "op_cf_adj (op_cf_adj \<Phi>)\<lparr>AdjNT\<rparr> = \<Phi>\<lparr>AdjNT\<rparr>"
  proof(rule ntcf_eqI)
    show op_op_\<Phi>:
      "op_cf_adj (op_cf_adj \<Phi>)\<lparr>AdjNT\<rparr> :
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>-,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-) :
        op_cat \<CC> \<times>\<^sub>C \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by (rule \<Phi>'.NT.is_ntcf_axioms)
    show \<Phi>: "\<Phi>\<lparr>AdjNT\<rparr> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>-,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-) : 
      op_cat \<CC> \<times>\<^sub>C \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by (rule NT.is_ntcf_axioms)
    from op_op_\<Phi> have dom_lhs:
      "\<D>\<^sub>\<circ> (op_cf_adj (op_cf_adj \<Phi>)\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>) = (op_cat \<CC> \<times>\<^sub>C \<DD>)\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)
    show "op_cf_adj (op_cf_adj \<Phi>)\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr> = \<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold NT.ntcf_NTMap_vdomain dom_lhs)
      fix cd assume prems: "cd \<in>\<^sub>\<circ> (op_cat \<CC> \<times>\<^sub>C \<DD>)\<lparr>Obj\<rparr>"
      then obtain c d 
        where cd_def: "cd = [c, d]\<^sub>\<circ>"
          and c: "c \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
          and d: "d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
        by (elim cat_prod_2_ObjE[OF L.category_op R.category_axioms prems])
      from is_cf_adjunction_axioms c d L.category_axioms R.category_axioms \<Phi> 
      show 
        "op_cf_adj (op_cf_adj \<Phi>)\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>cd\<rparr> = \<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>cd\<rparr>"
        unfolding cd_def cat_op_simps
        by 
          (
            cs_concl
              cs_intro: 
                cat_arrow_cs_intros 
                ntcf_cs_intros 
                adj_cs_intros 
                cat_op_intros 
                cat_cs_intros 
                cat_prod_cs_intros 
             cs_simp: cat_cs_simps cat_op_simps
         )
    qed (auto intro: inv_ntcf_NTMap_vsv)
  qed simp_all
qed (auto intro: adj_cs_intros)

lemmas [cat_op_simps] = is_cf_adjunction.cf_adjunction_op_cf_adj_op_cf_adj



subsubsection\<open>Alternative form of the naturality condition\<close>


text\<open>
The lemmas in this subsection are based on the comments on page 81 in 
\cite{mac_lane_categories_2010}.
\<close>

lemma (in is_cf_adjunction) cf_adj_Comp_commute_RL:
  assumes "x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> a"
    and "k : a \<mapsto>\<^bsub>\<DD>\<^esub> a'"
  shows 
    "\<GG>\<lparr>ArrMap\<rparr>\<lparr>k\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> =
      (\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a'\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>k \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> f\<rparr>"
proof-
  from 
    assms 
    is_cf_adjunction_axioms 
    L.category_axioms R.category_axioms (*speedup*)
    L.category_op R.category_op (*speedup*)
  have \<phi>_x_a: "\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet> :
    Hom \<DD> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) a \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> x (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps
          cs_intro: cat_cs_intros cat_op_intros adj_cs_intros cat_prod_cs_intros
      )
  note \<phi>_x_a_f = 
    cat_Set_ArrVal_app_vrange[OF \<phi>_x_a, unfolded in_Hom_iff, OF assms(2)]
  from 
    is_cf_adjunction_axioms assms 
    L.category_axioms R.category_axioms (*speedup*)
    L.category_op R.category_op (*speedup*)
  have \<phi>_x_a': 
    "\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a'\<rparr>\<^sub>\<bullet> :
      Hom \<DD> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) a' \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> x (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>)"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros adj_cs_intros cat_prod_cs_intros
      )
  from is_cf_adjunction_axioms this assms have x_k:
    "[\<CC>\<lparr>CId\<rparr>\<lparr>x\<rparr>, k]\<^sub>\<circ> : [x, a]\<^sub>\<circ> \<mapsto>\<^bsub>op_cat \<CC> \<times>\<^sub>C \<DD>\<^esub> [x, a']\<^sub>\<circ>"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros adj_cs_intros cat_prod_cs_intros
      )
  from 
    NT.ntcf_Comp_commute[OF this] is_cf_adjunction_axioms assms 
    L.category_axioms R.category_axioms (*speedup*)
    L.category_op R.category_op (*speedup*)
  have
    "\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a'\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<DD> [\<DD>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>, k]\<^sub>\<circ> =
      cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>x\<rparr>, \<GG>\<lparr>ArrMap\<rparr>\<lparr>k\<rparr>]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> \<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet>"
    (is \<open>?lhs = ?rhs\<close>)
    by (*slow*)
      (
        cs_prems cs_ist_simple
          cs_simp: cat_cs_simps
          cs_intro: cat_cs_intros cat_op_intros adj_cs_intros cat_prod_cs_intros
      )
  moreover from 
    is_cf_adjunction_axioms assms \<phi>_x_a' 
    L.category_axioms R.category_axioms (*speedup*)
    L.category_op R.category_op (*speedup*)
  have
    "?lhs\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> = (\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a'\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>k \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> f\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros adj_cs_intros cat_prod_cs_intros
      )
  moreover from 
    is_cf_adjunction_axioms assms \<phi>_x_a_f 
    L.category_axioms R.category_axioms (*speedup*)
    L.category_op R.category_op (*speedup*)
  have
    "?rhs\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>k\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
    by 
      (
        cs_concl
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros adj_cs_intros cat_prod_cs_intros
      )
  ultimately show ?thesis by simp
qed

lemma (in is_cf_adjunction) cf_adj_Comp_commute_LR:
  assumes "x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> a"
    and "h : x' \<mapsto>\<^bsub>\<CC>\<^esub> x"
  shows
    "(\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h =
      (\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x', a\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>f \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>\<rparr>"
proof-
  from 
    is_cf_adjunction_axioms assms 
    L.category_axioms R.category_axioms (*speedup*)
    L.category_op R.category_op (*speedup*)
  have \<phi>_x_a: "\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet> :
    Hom \<DD> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) a \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> x (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)"
    by 
      (
        cs_concl
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros adj_cs_intros cat_prod_cs_intros
      )
  note \<phi>_x_a_f = 
    cat_Set_ArrVal_app_vrange[OF \<phi>_x_a, unfolded in_Hom_iff, OF assms(2)]
  from is_cf_adjunction_axioms assms have
    "[h, \<DD>\<lparr>CId\<rparr>\<lparr>a\<rparr>]\<^sub>\<circ> : [x, a]\<^sub>\<circ> \<mapsto>\<^bsub>op_cat \<CC> \<times>\<^sub>C \<DD>\<^esub> [x', a]\<^sub>\<circ>"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros adj_cs_intros cat_prod_cs_intros
      )
  from 
    NT.ntcf_Comp_commute[OF this] is_cf_adjunction_axioms assms 
    L.category_axioms R.category_axioms (*speedup*)
    L.category_op R.category_op (*speedup*)
  have
    "\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x', a\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<DD> [\<FF>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>, \<DD>\<lparr>CId\<rparr>\<lparr>a\<rparr>]\<^sub>\<circ> =
      cf_hom \<CC> [h, \<CC>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> \<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet>"
    (is \<open>?lhs = ?rhs\<close>)
    by (*slow*)
      (
        cs_prems
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros adj_cs_intros cat_prod_cs_intros
      )  
  moreover from 
    is_cf_adjunction_axioms assms 
    L.category_axioms R.category_axioms (*speedup*)
    L.category_op R.category_op (*speedup*)
  have
    "?lhs\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> = (\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x', a\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>f \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros adj_cs_intros cat_prod_cs_intros
      )
  moreover from 
    is_cf_adjunction_axioms assms \<phi>_x_a_f 
    L.category_axioms R.category_axioms (*speedup*)
    L.category_op R.category_op (*speedup*)
  have 
    "?rhs\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> = (\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros adj_cs_intros cat_prod_cs_intros
      )
  ultimately show ?thesis by simp
qed



subsection\<open>Unit\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter IV-1 in \cite{mac_lane_categories_2010}.\<close>

definition cf_adjunction_unit :: "V \<Rightarrow> V" (\<open>\<eta>\<^sub>C\<close>)
  where "\<eta>\<^sub>C \<Phi> =
    [
      (
        \<lambda>x\<in>\<^sub>\<circ>\<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr>.
          (\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, \<Phi>\<lparr>AdjLeft\<rparr>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>
            \<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomCod\<rparr>\<lparr>CId\<rparr>\<lparr>\<Phi>\<lparr>AdjLeft\<rparr>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>
          \<rparr>
      ),
      cf_id (\<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomDom\<rparr>),
      (\<Phi>\<lparr>AdjRight\<rparr>) \<circ>\<^sub>C\<^sub>F (\<Phi>\<lparr>AdjLeft\<rparr>),
      \<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomDom\<rparr>,
      \<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomDom\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_adjunction_unit_components:
  shows "\<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr> =
    (
      \<lambda>x\<in>\<^sub>\<circ>\<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr>.
        (\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, \<Phi>\<lparr>AdjLeft\<rparr>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>
          \<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomCod\<rparr>\<lparr>CId\<rparr>\<lparr>\<Phi>\<lparr>AdjLeft\<rparr>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>
        \<rparr>
    )"
    and "\<eta>\<^sub>C \<Phi>\<lparr>NTDom\<rparr> = cf_id (\<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomDom\<rparr>)"
    and "\<eta>\<^sub>C \<Phi>\<lparr>NTCod\<rparr> = (\<Phi>\<lparr>AdjRight\<rparr>) \<circ>\<^sub>C\<^sub>F (\<Phi>\<lparr>AdjLeft\<rparr>)"
    and "\<eta>\<^sub>C \<Phi>\<lparr>NTDGDom\<rparr> = \<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomDom\<rparr>"
    and "\<eta>\<^sub>C \<Phi>\<lparr>NTDGCod\<rparr> = \<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomDom\<rparr>"
  unfolding cf_adjunction_unit_def nt_field_simps 
  by (simp_all add: nat_omega_simps)

context is_cf_adjunction
begin

lemma cf_adjunction_unit_components':
  shows "\<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr> =
    (
      \<lambda>x\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>.
        (\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>\<DD>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>\<rparr>
    )"
    and "\<eta>\<^sub>C \<Phi>\<lparr>NTDom\<rparr> = cf_id \<CC>"
    and "\<eta>\<^sub>C \<Phi>\<lparr>NTCod\<rparr> = \<GG> \<circ>\<^sub>C\<^sub>F \<FF>"
    and "\<eta>\<^sub>C \<Phi>\<lparr>NTDGDom\<rparr> = \<CC>"
    and "\<eta>\<^sub>C \<Phi>\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding cf_adjunction_unit_components
  by (cs_concl cs_simp: cat_cs_simps adj_cs_simps)+

mk_VLambda cf_adjunction_unit_components'(1)
  |vdomain cf_adjunction_unit_NTMap_vdomain[adj_cs_simps]|
  |app cf_adjunction_unit_NTMap_app[adj_cs_simps]|

end

mk_VLambda cf_adjunction_unit_components(1)
  |vsv cf_adjunction_unit_NTMap_vsv[adj_cs_intros]|

lemmas [adj_cs_simps] = 
  is_cf_adjunction.cf_adjunction_unit_NTMap_vdomain
  is_cf_adjunction.cf_adjunction_unit_NTMap_app


subsubsection\<open>Natural transformation map\<close>

lemma (in is_cf_adjunction) cf_adjunction_unit_NTMap_is_arr: 
  assumes "x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "\<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr> : x \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>"
proof-
  from 
    is_cf_adjunction_axioms assms
    L.category_axioms R.category_axioms (*speedup*)
    L.category_op R.category_op (*speedup*)
  have \<phi>_x_\<FF>x: 
    "\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>\<^sub>\<bullet> :
      Hom \<DD> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> 
      Hom \<CC> x (\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>)"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros adj_cs_intros cat_prod_cs_intros
      ) 
  from is_cf_adjunction_axioms assms have CId_\<FF>x: 
    "\<DD>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>"
    by (cs_concl cs_simp: cs_intro: cat_cs_intros adj_cs_intros)   
  from 
    is_cf_adjunction_axioms 
    assms
    cat_Set_ArrVal_app_vrange[OF \<phi>_x_\<FF>x, unfolded in_Hom_iff, OF CId_\<FF>x]
  show "\<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr> : x \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>"
    by (cs_concl cs_simp: adj_cs_simps cs_intro: cat_cs_intros)
qed

lemma (in is_cf_adjunction) cf_adjunction_unit_NTMap_is_arr': 
  assumes "x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "a = x"
    and "b = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>"
    and "\<CC>' = \<CC>"
  shows "\<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr> : x \<mapsto>\<^bsub>\<CC>'\<^esub> b"
  using assms(1) unfolding assms(2-4) by (rule cf_adjunction_unit_NTMap_is_arr)

lemmas [adj_cs_intros] = is_cf_adjunction.cf_adjunction_unit_NTMap_is_arr'

lemma (in is_cf_adjunction) cf_adjunction_unit_NTMap_vrange: 
  "\<R>\<^sub>\<circ> (\<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold cf_adjunction_unit_NTMap_vdomain)
  fix x assume prems: "x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  from cf_adjunction_unit_NTMap_is_arr[OF prems] show "\<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    by auto
qed (auto intro: adj_cs_intros)


subsubsection\<open>Unit is a natural transformation\<close>

lemma (in is_cf_adjunction) cf_adjunction_unit_is_ntcf:
  "\<eta>\<^sub>C \<Phi> : cf_id \<CC> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_ntcfI')
  show "vfsequence (\<eta>\<^sub>C \<Phi>)" unfolding cf_adjunction_unit_def by simp
  show "vcard (\<eta>\<^sub>C \<Phi>) = 5\<^sub>\<nat>"
    unfolding cf_adjunction_unit_def by (simp add: nat_omega_simps)
  from is_cf_adjunction_axioms show "cf_id \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros adj_cs_intros)
  from is_cf_adjunction_axioms show "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros adj_cs_intros)
  from is_cf_adjunction_axioms show "\<D>\<^sub>\<circ> (\<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: adj_cs_simps cs_intro: cat_cs_intros)
  show "\<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : cf_id \<CC>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    if "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for a
    using is_cf_adjunction_axioms that 
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros adj_cs_intros)
  show
    "\<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> cf_id \<CC>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
      (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
    if "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for a b f
    using is_cf_adjunction_axioms that
    by 
      (
        cs_concl 
          cs_simp: 
            cf_adj_Comp_commute_RL cf_adj_Comp_commute_LR 
            cat_cs_simps  
            adj_cs_simps 
          cs_intro: cat_cs_intros adj_cs_intros
      )
qed (auto simp: cf_adjunction_unit_components')

lemma (in is_cf_adjunction) cf_adjunction_unit_is_ntcf':
  assumes "\<SS> = cf_id \<CC>"
    and "\<SS>' = \<GG> \<circ>\<^sub>C\<^sub>F \<FF>"
    and "\<AA> = \<CC>"
    and "\<BB> = \<CC>"
  shows "\<eta>\<^sub>C \<Phi> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  unfolding assms by (rule cf_adjunction_unit_is_ntcf)

lemmas [adj_cs_intros] = is_cf_adjunction.cf_adjunction_unit_is_ntcf'


subsubsection\<open>Every component of a unit is a universal arrow\<close>


text\<open>
The lemmas in this subsection are based on elements of the statement of 
Theorem 1 in Chapter IV-1 in \cite{mac_lane_categories_2010}.
\<close>

lemma (in is_cf_adjunction) cf_adj_umap_of_unit:
  assumes "x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "a \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
  shows "\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet> =
    umap_of \<GG> x (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) (\<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) a"
  (is \<open>\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet> = ?uof_a\<close>)
proof-

  from 
    is_cf_adjunction_axioms assms 
    L.category_axioms R.category_axioms (*speedup*)
    L.category_op R.category_op (*speedup*)
  have \<phi>_xa: "\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet> :
    Hom \<DD> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) a \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> x (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)"
    by
      (
        cs_concl
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros adj_cs_intros cat_prod_cs_intros
      )
  then have dom_lhs:
    "\<D>\<^sub>\<circ> ((\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>) = Hom \<DD> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) a"
    by (cs_concl cs_simp: cat_cs_simps)
  from is_cf_adjunction_axioms assms have uof_a:
    "?uof_a : Hom \<DD> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) a \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> x (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)"
    by (cs_concl cs_simp: cs_intro: cat_cs_intros adj_cs_intros)
  then have dom_rhs: "\<D>\<^sub>\<circ> (?uof_a\<lparr>ArrVal\<rparr>) = Hom \<DD> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) a"
    by (cs_concl cs_simp: cat_cs_simps)

  show ?thesis
  proof(rule arr_Set_eqI[of \<alpha>])
    from \<phi>_xa show arr_Set_\<phi>_xa: "arr_Set \<alpha> (\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet>)"
      by (auto dest: cat_Set_is_arrD(1))
    from uof_a show arr_Set_uof_a: "arr_Set \<alpha> ?uof_a" 
      by (auto dest: cat_Set_is_arrD(1))
    show "(\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr> = ?uof_a\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
      fix g assume prems: "g : \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> a"
      from is_cf_adjunction_axioms assms prems show
        "(\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>g\<rparr> = ?uof_a\<lparr>ArrVal\<rparr>\<lparr>g\<rparr>"
        by
          (
            cs_concl
              cs_simp:
                cf_adj_Comp_commute_RL
                adj_cs_simps
                cat_cs_simps
                cat_op_simps
                cat_prod_cs_simps
              cs_intro:
                adj_cs_intros
                ntcf_cs_intros
                cat_cs_intros
                cat_op_intros
                cat_prod_cs_intros
          )
    qed (use arr_Set_\<phi>_xa arr_Set_uof_a in auto)
  
  qed (use \<phi>_xa uof_a in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

qed

lemma (in is_cf_adjunction) cf_adj_umap_of_unit':
  assumes "x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "a \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    and "\<eta> = \<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>"
    and "\<FF>x = \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>"
  shows "\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet> = umap_of \<GG> x \<FF>x \<eta> a"
  using assms(1,2) unfolding assms(3,4) by (rule cf_adj_umap_of_unit)

lemma (in is_cf_adjunction) cf_adjunction_unit_component_is_ua_of:
  assumes "x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "universal_arrow_of \<GG> x (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) (\<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>)"
    (is \<open>universal_arrow_of \<GG> x (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) ?\<eta>x\<close>)
proof(rule RL.cf_ua_of_if_ntcf_ua_of_is_iso_ntcf)
  from is_cf_adjunction_axioms assms show "\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    by (cs_concl cs_intro: cat_cs_intros adj_cs_intros)
  from is_cf_adjunction_axioms assms show 
    "\<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr> : x \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>"
    by (cs_concl cs_simp: cs_intro: cat_cs_intros adj_cs_intros)
  show 
    "ntcf_ua_of \<alpha> \<GG> x (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) (\<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(x,-) \<circ>\<^sub>C\<^sub>F \<GG> :
      \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    (is \<open>?ntcf_ua_of : ?H\<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o ?H\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>\<close>)
  proof(rule is_iso_ntcfI)
    from is_cf_adjunction_axioms assms show 
      "?ntcf_ua_of : ?H\<FF> \<mapsto>\<^sub>C\<^sub>F ?H\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by (intro RL.cf_ntcf_ua_of_is_ntcf) 
        (cs_concl cs_simp: cs_intro: cat_cs_intros adj_cs_intros)+
    fix a assume prems: "a \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    from assms prems have 
      "\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet> = umap_of \<GG> x (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) ?\<eta>x a"
      (is \<open>\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet> = ?uof_a\<close>)
      by (rule cf_adj_umap_of_unit)
    from assms prems L.category_axioms R.category_axioms have
      "[x, a]\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<CC> \<times>\<^sub>C \<DD>)\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cs_intro:  cat_op_intros cat_prod_cs_intros)
    from 
      NT.iso_ntcf_is_arr_isomorphism[
        OF this, unfolded cf_adj_umap_of_unit[OF assms prems]
        ]
      is_cf_adjunction_axioms assms prems
      L.category_axioms R.category_axioms
    have "?uof_a :
      Hom \<DD> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> x (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)"
      by 
        (
          cs_prems 
            cs_simp: cat_cs_simps 
            cs_intro: 
              cat_cs_intros cat_op_intros adj_cs_intros cat_prod_cs_intros
        )
    with is_cf_adjunction_axioms assms prems show 
      "?ntcf_ua_of\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : ?H\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> ?H\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_cs_intros cat_op_intros adj_cs_intros
        )
  qed
qed



subsection\<open>Counit\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cf_adjunction_counit :: "V \<Rightarrow> V" (\<open>\<epsilon>\<^sub>C\<close>)
  where "\<epsilon>\<^sub>C \<Phi> =
    [
      (
        \<lambda>x\<in>\<^sub>\<circ>\<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomCod\<rparr>\<lparr>Obj\<rparr>.
          (\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>\<Phi>\<lparr>AdjRight\<rparr>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>, x\<rparr>\<^sub>\<bullet>)\<inverse>\<^sub>S\<^sub>e\<^sub>t\<lparr>ArrVal\<rparr>\<lparr>
            \<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomDom\<rparr>\<lparr>CId\<rparr>\<lparr>\<Phi>\<lparr>AdjRight\<rparr>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>
            \<rparr>
      ), 
      (\<Phi>\<lparr>AdjLeft\<rparr>) \<circ>\<^sub>C\<^sub>F (\<Phi>\<lparr>AdjRight\<rparr>),
      cf_id (\<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomCod\<rparr>),
      \<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomCod\<rparr>,
      \<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_adjunction_counit_components:
  shows "\<epsilon>\<^sub>C \<Phi>\<lparr>NTMap\<rparr> =
    (
      \<lambda>x\<in>\<^sub>\<circ>\<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomCod\<rparr>\<lparr>Obj\<rparr>.
        (\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>\<Phi>\<lparr>AdjRight\<rparr>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>, x\<rparr>\<^sub>\<bullet>)\<inverse>\<^sub>S\<^sub>e\<^sub>t\<lparr>ArrVal\<rparr>\<lparr>
          \<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomDom\<rparr>\<lparr>CId\<rparr>\<lparr>\<Phi>\<lparr>AdjRight\<rparr>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>
          \<rparr>
    )"
    and "\<epsilon>\<^sub>C \<Phi>\<lparr>NTDom\<rparr> = (\<Phi>\<lparr>AdjLeft\<rparr>) \<circ>\<^sub>C\<^sub>F (\<Phi>\<lparr>AdjRight\<rparr>)"
    and "\<epsilon>\<^sub>C \<Phi>\<lparr>NTCod\<rparr> = cf_id (\<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomCod\<rparr>)"
    and "\<epsilon>\<^sub>C \<Phi>\<lparr>NTDGDom\<rparr> = \<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomCod\<rparr>"
    and "\<epsilon>\<^sub>C \<Phi>\<lparr>NTDGCod\<rparr> = \<Phi>\<lparr>AdjLeft\<rparr>\<lparr>HomCod\<rparr>"
  unfolding cf_adjunction_counit_def nt_field_simps 
  by (simp_all add: nat_omega_simps)

context is_cf_adjunction
begin

lemma cf_adjunction_counit_components':
  shows "\<epsilon>\<^sub>C \<Phi>\<lparr>NTMap\<rparr> =
    (
      \<lambda>x\<in>\<^sub>\<circ>\<DD>\<lparr>Obj\<rparr>.
        (\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>, x\<rparr>\<^sub>\<bullet>)\<inverse>\<^sub>S\<^sub>e\<^sub>t\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>\<rparr>
    )"
    and "\<epsilon>\<^sub>C \<Phi>\<lparr>NTDom\<rparr> = \<FF> \<circ>\<^sub>C\<^sub>F \<GG>"
    and "\<epsilon>\<^sub>C \<Phi>\<lparr>NTCod\<rparr> = cf_id \<DD>"
    and "\<epsilon>\<^sub>C \<Phi>\<lparr>NTDGDom\<rparr> = \<DD>"
    and "\<epsilon>\<^sub>C \<Phi>\<lparr>NTDGCod\<rparr> = \<DD>"
  unfolding cf_adjunction_counit_components
  by (cs_concl cs_simp: cat_cs_simps adj_cs_simps)+

mk_VLambda cf_adjunction_counit_components'(1)
  |vdomain cf_adjunction_counit_NTMap_vdomain[adj_cs_simps]|
  |app cf_adjunction_counit_NTMap_app[adj_cs_simps]|

end

mk_VLambda cf_adjunction_counit_components(1)
  |vsv cf_adjunction_counit_NTMap_vsv[adj_cs_intros]|

lemmas [adj_cs_simps] = 
  is_cf_adjunction.cf_adjunction_counit_NTMap_vdomain
  is_cf_adjunction.cf_adjunction_counit_NTMap_app


subsubsection\<open>Duality for the unit and counit\<close>

lemma (in is_cf_adjunction) cf_adjunction_unit_NTMap_op:
  "\<eta>\<^sub>C (op_cf_adj \<Phi>)\<lparr>NTMap\<rparr> = \<epsilon>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>"
proof-
  interpret op_\<Phi>: 
    is_cf_adjunction \<alpha> \<open>op_cat \<DD>\<close> \<open>op_cat \<CC>\<close> \<open>op_cf \<GG>\<close> \<open>op_cf \<FF>\<close> \<open>op_cf_adj \<Phi>\<close>
    by (rule is_cf_adjunction_op)
  show ?thesis
  proof
    (
      rule vsv_eqI, 
      unfold 
        cf_adjunction_counit_NTMap_vdomain 
        op_\<Phi>.cf_adjunction_unit_NTMap_vdomain
    )
    fix a assume prems: "a \<in>\<^sub>\<circ> op_cat \<DD>\<lparr>Obj\<rparr>"
    then have a: "a \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>" unfolding cat_op_simps by simp
    from is_cf_adjunction_axioms a show 
      "\<eta>\<^sub>C (op_cf_adj \<Phi>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<epsilon>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by 
        (
          cs_concl
            cs_simp: cat_Set_cs_simps cat_cs_simps cat_op_simps adj_cs_simps 
            cs_intro: 
              cat_arrow_cs_intros cat_cs_intros cat_op_intros cat_prod_cs_intros
        )
  qed 
    (
      simp_all add: 
        cat_op_simps cf_adjunction_counit_NTMap_vsv cf_adjunction_unit_NTMap_vsv
    )
qed


lemmas [cat_op_simps] = is_cf_adjunction.cf_adjunction_unit_NTMap_op

lemma (in is_cf_adjunction) cf_adjunction_counit_NTMap_op:
  "\<epsilon>\<^sub>C (op_cf_adj \<Phi>)\<lparr>NTMap\<rparr> = \<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>"
  by 
    (
      rule is_cf_adjunction.cf_adjunction_unit_NTMap_op[
        OF is_cf_adjunction_op,
        unfolded is_cf_adjunction.cf_adjunction_op_cf_adj_op_cf_adj[
          OF is_cf_adjunction_axioms
          ],
        unfolded cat_op_simps,
        symmetric
      ]
   )

lemmas [cat_op_simps] = is_cf_adjunction.cf_adjunction_counit_NTMap_op

lemma (in is_cf_adjunction) op_ntcf_cf_adjunction_counit:
  "op_ntcf (\<epsilon>\<^sub>C \<Phi>) = \<eta>\<^sub>C (op_cf_adj \<Phi>)"
  (is \<open>?\<epsilon> = ?\<eta>\<close>)
proof(rule vsv_eqI)
  interpret op_\<Phi>: 
    is_cf_adjunction \<alpha> \<open>op_cat \<DD>\<close> \<open>op_cat \<CC>\<close> \<open>op_cf \<GG>\<close> \<open>op_cf \<FF>\<close> \<open>op_cf_adj \<Phi>\<close>
    by (rule is_cf_adjunction_op)
  have dom_lhs: "\<D>\<^sub>\<circ> ?\<epsilon> = 5\<^sub>\<nat>" unfolding op_ntcf_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> ?\<eta> = 5\<^sub>\<nat>" 
    unfolding cf_adjunction_unit_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> ?\<epsilon> = \<D>\<^sub>\<circ> ?\<eta>" unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ?\<epsilon> \<Longrightarrow> ?\<epsilon>\<lparr>a\<rparr> = ?\<eta>\<lparr>a\<rparr>" for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral, 
        fold nt_field_simps, 
        unfold cf_adjunction_unit_NTMap_op,
        unfold 
          cf_adjunction_counit_components' 
          cf_adjunction_unit_components'
          op_\<Phi>.cf_adjunction_counit_components' 
          op_\<Phi>.cf_adjunction_unit_components'
          cat_op_simps
      )
      simp_all
qed (auto simp: op_ntcf_def cf_adjunction_unit_def)

lemmas [cat_op_simps] = is_cf_adjunction.op_ntcf_cf_adjunction_counit

lemma (in is_cf_adjunction) op_ntcf_cf_adjunction_unit:
  "op_ntcf (\<eta>\<^sub>C \<Phi>) = \<epsilon>\<^sub>C (op_cf_adj \<Phi>)"
  (is \<open>?\<eta> = ?\<epsilon>\<close>)
proof(rule vsv_eqI)
  interpret op_\<Phi>: 
    is_cf_adjunction \<alpha> \<open>op_cat \<DD>\<close> \<open>op_cat \<CC>\<close> \<open>op_cf \<GG>\<close> \<open>op_cf \<FF>\<close> \<open>op_cf_adj \<Phi>\<close>
    by (rule is_cf_adjunction_op)
  have dom_lhs: "\<D>\<^sub>\<circ> ?\<eta> = 5\<^sub>\<nat>" 
    unfolding op_ntcf_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> ?\<epsilon> = 5\<^sub>\<nat>" 
    unfolding cf_adjunction_counit_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> ?\<eta> = \<D>\<^sub>\<circ> ?\<epsilon>" unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ?\<eta> \<Longrightarrow> ?\<eta>\<lparr>a\<rparr> = ?\<epsilon>\<lparr>a\<rparr>" for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral, 
        fold nt_field_simps, 
        unfold cf_adjunction_counit_NTMap_op,
        unfold 
          cf_adjunction_counit_components' 
          cf_adjunction_unit_components'
          op_\<Phi>.cf_adjunction_counit_components' 
          op_\<Phi>.cf_adjunction_unit_components'
          cat_op_simps
      )
      simp_all
qed (auto simp: op_ntcf_def cf_adjunction_counit_def)

lemmas [cat_op_simps] = is_cf_adjunction.op_ntcf_cf_adjunction_unit


subsubsection\<open>Natural transformation map\<close>

lemma (in is_cf_adjunction) cf_adjunction_counit_NTMap_is_arr: 
  assumes "x \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
  shows "\<epsilon>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> x"
proof-
  from assms have x: "x \<in>\<^sub>\<circ> op_cat \<DD>\<lparr>Obj\<rparr>" unfolding cat_op_simps by simp
  show ?thesis
    by 
      (
        rule is_cf_adjunction.cf_adjunction_unit_NTMap_is_arr[
          OF is_cf_adjunction_op x, 
          unfolded cf_adjunction_unit_NTMap_op cat_op_simps
          ]
      )
qed

lemma (in is_cf_adjunction) cf_adjunction_counit_NTMap_is_arr': 
  assumes "x \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    and "a = \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>"
    and "b = x"
    and "\<DD>' = \<DD>"
  shows "\<epsilon>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr> : a \<mapsto>\<^bsub>\<DD>'\<^esub> b"
  using assms(1) unfolding assms(2-4) by (rule cf_adjunction_counit_NTMap_is_arr)

lemmas [adj_cs_intros] = is_cf_adjunction.cf_adjunction_counit_NTMap_is_arr'

lemma (in is_cf_adjunction) cf_adjunction_counit_NTMap_vrange: 
  "\<R>\<^sub>\<circ> (\<epsilon>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Arr\<rparr>"
  by 
    (
      rule is_cf_adjunction.cf_adjunction_unit_NTMap_vrange[
        OF is_cf_adjunction_op,
        unfolded cf_adjunction_unit_NTMap_op cat_op_simps
        ]
    )


subsubsection\<open>Counit is a natural transformation\<close>

lemma (in is_cf_adjunction) cf_adjunction_counit_is_ntcf:
  "\<epsilon>\<^sub>C \<Phi> : \<FF> \<circ>\<^sub>C\<^sub>F \<GG> \<mapsto>\<^sub>C\<^sub>F cf_id \<DD> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
proof-
  from is_cf_adjunction.cf_adjunction_unit_is_ntcf[OF is_cf_adjunction_op] have 
    "\<epsilon>\<^sub>C \<Phi> :
      op_cf (op_cf \<FF> \<circ>\<^sub>C\<^sub>F op_cf \<GG>) \<mapsto>\<^sub>C\<^sub>F op_cf (cf_id (op_cat \<DD>)) :
      op_cat (op_cat \<DD>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat (op_cat \<DD>)"
    unfolding
      is_cf_adjunction.op_ntcf_cf_adjunction_unit[
        OF is_cf_adjunction_op, unfolded cat_op_simps, symmetric
        ]
    by (rule is_ntcf.is_ntcf_op)
  then show ?thesis unfolding cat_op_simps .
qed

lemma (in is_cf_adjunction) cf_adjunction_counit_is_ntcf':
  assumes "\<SS> = \<FF> \<circ>\<^sub>C\<^sub>F \<GG>"
    and "\<SS>' = cf_id \<DD>"
    and "\<AA> = \<DD>"
    and "\<BB> = \<DD>"
  shows "\<epsilon>\<^sub>C \<Phi> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  unfolding assms by (rule cf_adjunction_counit_is_ntcf)

lemmas [adj_cs_intros] = is_cf_adjunction.cf_adjunction_counit_is_ntcf'


subsubsection\<open>Every component of a counit is a universal arrow\<close>

text\<open>
The lemmas in this subsection are based on elements of the statement of 
Theorem 1 in Chapter IV-1 in \cite{mac_lane_categories_2010}.
\<close>

lemma (in is_cf_adjunction) cf_adj_umap_fo_counit:
  assumes "x \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>" and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "op_cf_adj \<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>x, a\<rparr>\<^sub>\<bullet> =
    umap_fo \<FF> x (\<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) (\<epsilon>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) a"
  by
    (
      rule is_cf_adjunction.cf_adj_umap_of_unit[
        OF is_cf_adjunction_op,
        unfolded cat_op_simps,
        OF assms,
        unfolded cf_adjunction_unit_NTMap_op
        ]
    )

lemma (in is_cf_adjunction) cf_adjunction_counit_component_is_ua_fo:
  assumes "x \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
  shows "universal_arrow_fo \<FF> x (\<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) (\<epsilon>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>)"
  by 
    (
      rule is_cf_adjunction.cf_adjunction_unit_component_is_ua_of[
        OF is_cf_adjunction_op, 
        unfolded cat_op_simps, 
        OF assms,
        unfolded cf_adjunction_unit_NTMap_op
        ]
    )



subsection\<open>Counit-unit equations\<close>


text\<open>
The following equations appear as part of the statement of 
Theorem 1 in Chapter IV-1 in \cite{mac_lane_categories_2010}.
These equations also appear in \cite{noauthor_wikipedia_2001},
where they are named \<open>counit-unit equations\<close>.
\<close>

lemma (in is_cf_adjunction) cf_adjunction_counit_unit:
  "(\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon>\<^sub>C \<Phi>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<eta>\<^sub>C \<Phi> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) = ntcf_id \<GG>"
  (is \<open>(\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<epsilon>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<eta> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) = ntcf_id \<GG>\<close>)
proof(rule ntcf_eqI)
  from is_cf_adjunction_axioms show 
    "(\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<epsilon>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<eta> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) : \<GG> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros adj_cs_intros)
  show "ntcf_id \<GG> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (rule is_functor.cf_ntcf_id_is_ntcf[OF RL.is_functor_axioms])
  from is_cf_adjunction_axioms have dom_lhs:
    "\<D>\<^sub>\<circ> (((\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<epsilon>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<eta> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>))\<lparr>NTMap\<rparr>) = \<DD>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros adj_cs_intros)
  from is_cf_adjunction_axioms have dom_rhs: "\<D>\<^sub>\<circ> (ntcf_id \<GG>\<lparr>NTMap\<rparr>) = \<DD>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: adj_cs_intros)
  show "((\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<epsilon>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<eta> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>))\<lparr>NTMap\<rparr> = ntcf_id \<GG>\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
    fix a assume prems: "a \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    let ?\<phi>_aa = \<open>\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>, a\<rparr>\<^sub>\<bullet>\<close>
    have "category \<alpha> (cat_Set \<alpha>)"
      by (rule category_cat_Set)
    from is_cf_adjunction_axioms prems
      L.category_axioms R.category_axioms (*speedup*)
      L.category_op R.category_op (*speedup*)
      LR.is_functor_axioms RL.is_functor_axioms (*speedup*)
      category_cat_Set (*speedup*)
    have
      "?\<phi>_aa\<lparr>ArrVal\<rparr>\<lparr>?\<epsilon>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> =
        (?\<phi>_aa \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>_aa\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub>)\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: 
              \<Z>.cat_Set_Comp_ArrVal 
              cat_Set_the_inverse[symmetric] 
              cat_cs_simps adj_cs_simps cat_prod_cs_simps 
            cs_intro:
              cat_arrow_cs_intros 
              cat_cs_intros 
              cat_op_intros 
              adj_cs_intros 
              cat_prod_cs_intros
        )
    also from is_cf_adjunction_axioms prems 
      L.category_axioms R.category_axioms (*speedup*)
      L.category_op R.category_op (*speedup*)
      LR.is_functor_axioms RL.is_functor_axioms (*speedup*)
      category_cat_Set (*speedup*)   
    have "\<dots> = \<CC>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
      by (
          cs_concl 
            cs_simp: cat_cs_simps category.cat_the_inverse_Comp_CId
            cs_intro: 
              cat_arrow_cs_intros cat_cs_intros cat_op_intros cat_prod_cs_intros
        )
    finally have [cat_cs_simps]: 
      "(\<Phi>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>, a\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>?\<epsilon>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> = 
        \<CC>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
      by simp
    from 
      prems is_cf_adjunction_axioms 
      L.category_axioms R.category_axioms (*speedup*)
    show "((\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<epsilon>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<eta> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>))\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = ntcf_id \<GG>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by
        (
          cs_concl
            cs_simp:
              cat_Set_the_inverse[symmetric]
              cf_adj_Comp_commute_RL
              cat_cs_simps
              adj_cs_simps
              cat_prod_cs_simps
              cat_op_simps
            cs_intro:
              cat_arrow_cs_intros
              cat_cs_intros
              adj_cs_intros
              cat_prod_cs_intros
              cat_op_intros
        )

  qed (auto intro: cat_cs_intros)

qed simp_all

lemmas [adj_cs_simps] = is_cf_adjunction.cf_adjunction_counit_unit

lemma (in is_cf_adjunction) cf_adjunction_unit_counit:
  "(\<epsilon>\<^sub>C \<Phi> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>\<^sub>C \<Phi>) = ntcf_id \<FF>"
  (is \<open>(?\<epsilon> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<eta>) = ntcf_id \<FF>\<close>)
proof-
  from is_cf_adjunction_axioms have \<FF>\<eta>:
    "\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<eta> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros adj_cs_intros)
  from is_cf_adjunction_axioms have \<epsilon>\<FF>:
    "?\<epsilon> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF> : \<FF> \<circ>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros adj_cs_intros)
  from \<FF>\<eta> \<epsilon>\<FF> have \<epsilon>\<FF>_\<FF>\<eta>: 
    "(?\<epsilon> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<eta>) : \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_intro: cat_cs_intros)
  from 
    is_cf_adjunction.cf_adjunction_counit_unit[
      OF is_cf_adjunction_op, 
      unfolded 
        op_ntcf_cf_adjunction_unit[symmetric]
        op_ntcf_cf_adjunction_counit[symmetric]
        op_ntcf_cf_ntcf_comp[symmetric]
        op_ntcf_ntcf_cf_comp[symmetric]
        op_ntcf_ntcf_vcomp[symmetric]
        op_ntcf_ntcf_vcomp[symmetric, OF \<epsilon>\<FF> \<FF>\<eta>]
        LR.cf_ntcf_id_op_cf
      ]
  have 
    "op_ntcf (op_ntcf ((?\<epsilon> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<eta>))) =
      op_ntcf (op_ntcf (ntcf_id \<FF>))"
    by simp
  from this is_cf_adjunction_axioms \<epsilon>\<FF>_\<FF>\<eta> show ?thesis
    by (cs_prems cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_prod_cs_intros)
qed

lemmas [adj_cs_simps] = is_cf_adjunction.cf_adjunction_unit_counit



subsection\<open>
Construction of an adjunction from universal morphisms 
from objects to functors
\<close>


text\<open>
The subsection presents the construction of an adjunction given 
a structured collection of universal morphisms from objects to functors.
The content of this subsection follows the statement and the proof
of Theorem 2-i in Chapter IV-1 in \cite{mac_lane_categories_2010}.
\<close>


subsubsection\<open>
The natural transformation associated with the adjunction
constructed from universal morphisms from objects to functors
\<close>

definition cf_adjunction_AdjNT_of_unit :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta> =
    [
      (\<lambda>cd\<in>\<^sub>\<circ>(op_cat (\<FF>\<lparr>HomDom\<rparr>) \<times>\<^sub>C \<FF>\<lparr>HomCod\<rparr>)\<lparr>Obj\<rparr>.
        umap_of \<GG> (cd\<lparr>0\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>cd\<lparr>0\<rparr>\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>cd\<lparr>0\<rparr>\<rparr>) (cd\<lparr>1\<^sub>\<nat>\<rparr>)),
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<FF>\<lparr>HomCod\<rparr>(\<FF>-,-),
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<FF>\<lparr>HomDom\<rparr>(-,\<GG>-),
      op_cat (\<FF>\<lparr>HomDom\<rparr>) \<times>\<^sub>C (\<FF>\<lparr>HomCod\<rparr>),
      cat_Set \<alpha>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_adjunction_AdjNT_of_unit_components:
  shows "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTMap\<rparr> =
    (
      \<lambda>cd\<in>\<^sub>\<circ>(op_cat (\<FF>\<lparr>HomDom\<rparr>) \<times>\<^sub>C \<FF>\<lparr>HomCod\<rparr>)\<lparr>Obj\<rparr>.
        umap_of \<GG> (cd\<lparr>0\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>cd\<lparr>0\<rparr>\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>cd\<lparr>0\<rparr>\<rparr>)  (cd\<lparr>1\<^sub>\<nat>\<rparr>)
    )"
    and "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTDom\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<FF>\<lparr>HomCod\<rparr>(\<FF>-,-)"
    and "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTCod\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<FF>\<lparr>HomDom\<rparr>(-,\<GG>-)"
    and "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTDGDom\<rparr> =
      op_cat (\<FF>\<lparr>HomDom\<rparr>) \<times>\<^sub>C (\<FF>\<lparr>HomCod\<rparr>)"
    and "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTDGCod\<rparr> = cat_Set \<alpha>"
  unfolding cf_adjunction_AdjNT_of_unit_def nt_field_simps
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

lemma cf_adjunction_AdjNT_of_unit_NTMap_vsv[adj_cs_intros]:
  "vsv (cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTMap\<rparr>)"
  unfolding cf_adjunction_AdjNT_of_unit_components by simp

lemma cf_adjunction_AdjNT_of_unit_NTMap_vdomain[adj_cs_simps]:
  assumes "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<D>\<^sub>\<circ> (cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTMap\<rparr>) = (op_cat \<CC> \<times>\<^sub>C \<DD>)\<lparr>Obj\<rparr>"
proof-
  interpret is_functor \<alpha> \<CC> \<DD> \<FF> by (rule assms(1))
  show ?thesis 
    unfolding cf_adjunction_AdjNT_of_unit_components 
    by (simp add: cat_cs_simps)
qed

lemma cf_adjunction_AdjNT_of_unit_NTMap_app[adj_cs_simps]:
  assumes "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
  shows 
    "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTMap\<rparr>\<lparr>c, d\<rparr>\<^sub>\<bullet> =
      umap_of \<GG> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>) d"
proof-
  interpret \<FF>: is_functor \<alpha> \<CC> \<DD> \<FF> by (rule assms(1))
  from assms have "[c, d]\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<CC> \<times>\<^sub>C \<DD>)\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_prod_cs_intros)
  then show "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTMap\<rparr> \<lparr>c, d\<rparr>\<^sub>\<bullet> = 
    umap_of \<GG> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>) d"
    unfolding cf_adjunction_AdjNT_of_unit_components 
    by (simp add: nat_omega_simps cat_cs_simps)
qed

lemma cf_adjunction_AdjNT_of_unit_NTMap_vrange:
  assumes "category \<alpha> \<CC>"
    and "category \<alpha> \<DD>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<eta> : cf_id \<CC> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Arr\<rparr>"
proof-
  interpret \<FF>: is_functor \<alpha> \<CC> \<DD> \<FF> by (rule assms(3))
  show ?thesis
  proof
    (
      rule vsv.vsv_vrange_vsubset, 
      unfold cf_adjunction_AdjNT_of_unit_NTMap_vdomain[OF assms(3)]
    )
    show "vsv (cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTMap\<rparr>)" 
      by (intro adj_cs_intros)
    fix cd assume prems: "cd \<in>\<^sub>\<circ> (op_cat \<CC> \<times>\<^sub>C \<DD>)\<lparr>Obj\<rparr>"
    then obtain c d where cd_def: "cd = [c, d]\<^sub>\<circ>"
      and c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
      and d: "d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
      by 
        (
          auto 
            simp: cat_op_simps 
            elim: 
              cat_prod_2_ObjE[OF \<FF>.HomDom.category_op \<FF>.HomCod.category_axioms]
        )
    from assms c d show 
      "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTMap\<rparr>\<lparr>cd\<rparr> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Arr\<rparr>"
      unfolding cd_def
      by (cs_concl cs_simp: cat_cs_simps adj_cs_simps cs_intro: cat_cs_intros)
  qed
qed


subsubsection\<open>
Adjunction constructed from universal morphisms 
from objects to functors is an adjunction
\<close>

lemma cf_adjunction_AdjNT_of_unit_is_ntcf:
  assumes "category \<alpha> \<CC>"
    and "category \<alpha> \<DD>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<eta> : cf_id \<CC> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta> :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>-,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-) :
    op_cat \<CC> \<times>\<^sub>C \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-

  interpret \<CC>: category \<alpha> \<CC> by (rule assms(1))
  interpret \<DD>: category \<alpha> \<DD> by (rule assms(2))
  interpret \<FF>: is_functor \<alpha> \<CC> \<DD> \<FF> by (rule assms(3))
  interpret \<GG>: is_functor \<alpha> \<DD> \<CC> \<GG> by (rule assms(4))
  interpret \<eta>: is_ntcf \<alpha> \<CC> \<CC> \<open>cf_id \<CC>\<close> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> \<eta> by (rule assms(5))

  show ?thesis
  proof(intro is_ntcfI')

    show "vfsequence (cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>)"
      unfolding cf_adjunction_AdjNT_of_unit_def by simp
    show "vcard (cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>) = 5\<^sub>\<nat>"
      unfolding cf_adjunction_AdjNT_of_unit_def by (simp add: nat_omega_simps)
    from assms(2,3) show 
      "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>-,-) : op_cat \<CC> \<times>\<^sub>C \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by (cs_concl cs_intro: cat_cs_intros)
    from assms show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-) : op_cat \<CC> \<times>\<^sub>C \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by (cs_concl cs_intro: cat_cs_intros)
    show "vsv (cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTMap\<rparr>)" 
      by (intro adj_cs_intros)
    from assms show 
      "\<D>\<^sub>\<circ> (cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTMap\<rparr>) = (op_cat \<CC> \<times>\<^sub>C \<DD>)\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps adj_cs_simps)

    show "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTMap\<rparr>\<lparr>cd\<rparr> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>-,-)\<lparr>ObjMap\<rparr>\<lparr>cd\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub>
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ObjMap\<rparr>\<lparr>cd\<rparr>"
      if "cd \<in>\<^sub>\<circ> (op_cat \<CC> \<times>\<^sub>C \<DD>)\<lparr>Obj\<rparr>" for cd
    proof-
      from that obtain c d 
        where cd_def: "cd = [c, d]\<^sub>\<circ>" and c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and d: "d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
        by 
          (
            auto 
              simp: cat_op_simps 
              elim: cat_prod_2_ObjE[OF \<CC>.category_op \<DD>.category_axioms]
          )
      from assms c d show ?thesis
        unfolding cd_def
        by 
          (
            cs_concl 
              cs_simp: adj_cs_simps cat_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
    qed

    show 
      "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTMap\<rparr>\<lparr>c'd'\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>-,-)\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> =
          Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
            cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>NTMap\<rparr>\<lparr>cd\<rparr>"
      if "gf : cd \<mapsto>\<^bsub>op_cat \<CC> \<times>\<^sub>C \<DD>\<^esub> c'd'" for cd c'd' gf 
    proof-
      from that obtain g f c c' d d'
        where gf_def: "gf = [g, f]\<^sub>\<circ>"
          and cd_def: "cd = [c, d]\<^sub>\<circ>"
          and c'd'_def: "c'd' = [c', d']\<^sub>\<circ>"
          and g: "g : c' \<mapsto>\<^bsub>\<CC>\<^esub> c" 
          and f: "f : d \<mapsto>\<^bsub>\<DD>\<^esub> d'"
        by 
          (
            auto 
              simp: cat_op_simps 
              elim: cat_prod_2_is_arrE[OF \<CC>.category_op \<DD>.category_axioms]
          ) 
      from assms g f that show ?thesis
        unfolding gf_def cd_def c'd'_def
        by 
          (
            cs_concl 
              cs_simp: cf_umap_of_cf_hom_unit_commute adj_cs_simps cat_cs_simps
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
    qed

  qed (auto simp: cf_adjunction_AdjNT_of_unit_components cat_cs_simps)

qed

lemma cf_adjunction_AdjNT_of_unit_is_ntcf'[adj_cs_intros]:
  assumes "category \<alpha> \<CC>"
    and "category \<alpha> \<DD>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<eta> : cf_id \<CC> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<SS> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>-,-)"
    and "\<SS>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)"
    and "\<AA> = op_cat \<CC> \<times>\<^sub>C \<DD>"
    and "\<BB> = cat_Set \<alpha>"
  shows "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms(1-5) unfolding assms(6-9) 
  by (rule cf_adjunction_AdjNT_of_unit_is_ntcf)


subsubsection\<open>
Adjunction constructed from universal morphisms from objects to functors
\<close>

definition cf_adjunction_of_unit :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta> =
    [\<FF>, \<GG>, cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_adjunction_of_unit_components:
  shows [adj_cs_simps]: "cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>AdjLeft\<rparr> = \<FF>"
    and [adj_cs_simps]: "cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>AdjRight\<rparr> = \<GG>"
    and "cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>AdjNT\<rparr> =
      cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>"
  unfolding cf_adjunction_of_unit_def adj_field_simps
  by (simp_all add: nat_omega_simps)


text\<open>Natural transformation map.\<close>

lemma cf_adjunction_of_unit_AdjNT_NTMap_vdomain[adj_cs_simps]:
  assumes "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<D>\<^sub>\<circ> (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>) = 
    (op_cat \<CC> \<times>\<^sub>C \<DD>)\<lparr>Obj\<rparr>"
  using assms 
  unfolding cf_adjunction_of_unit_components(3)
  by (rule cf_adjunction_AdjNT_of_unit_NTMap_vdomain)

lemma cf_adjunction_of_unit_AdjNT_NTMap_app[adj_cs_simps]:
  assumes "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
  shows 
    "cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>c, d\<rparr>\<^sub>\<bullet> =
      umap_of \<GG> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>) d"
  using assms 
  unfolding cf_adjunction_of_unit_components(3)
  by (rule cf_adjunction_AdjNT_of_unit_NTMap_app)


text\<open>
The adjunction constructed from universal morphisms from objects to 
functors is an adjunction.
\<close>

lemma cf_adjunction_of_unit_is_cf_adjunction:
  assumes "category \<alpha> \<CC>"
    and "category \<alpha> \<DD>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<eta> : cf_id \<CC> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>x. x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> universal_arrow_of \<GG> x (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>)"
  shows "cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<eta>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>) = \<eta>"
proof-

  interpret \<CC>: category \<alpha> \<CC> by (rule assms(1))
  interpret \<DD>: category \<alpha> \<DD> by (rule assms(2))
  interpret \<FF>: is_functor \<alpha> \<CC> \<DD> \<FF> by (rule assms(3))
  interpret \<GG>: is_functor \<alpha> \<DD> \<CC> \<GG> by (rule assms(4))
  interpret \<eta>: is_ntcf \<alpha> \<CC> \<CC> \<open>cf_id \<CC>\<close> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> \<eta> by (rule assms(5))

  show caou_\<eta>: "cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  proof
    (
      intro 
        is_cf_adjunctionI[OF _ _ assms(1-4)] 
        is_iso_ntcf_if_bnt_proj_snd_is_iso_ntcf[
          OF \<CC>.category_op \<DD>.category_axioms
          ],
      unfold cat_op_simps cf_adjunction_of_unit_components
    )
    show caou_\<eta>: "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>-,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-) :
      op_cat \<CC> \<times>\<^sub>C \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      unfolding cf_adjunction_of_unit_components
      by (rule cf_adjunction_AdjNT_of_unit_is_ntcf[OF assms(1-5)])
    fix a assume prems: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    have ua_of_\<eta>a:
      "ntcf_ua_of \<alpha> \<GG> a (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) :
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) \<circ>\<^sub>C\<^sub>F \<GG> :
        \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by 
        (
          rule is_functor.cf_ntcf_ua_of_is_iso_ntcf[
            OF assms(4) assms(6)[OF prems]
            ]
        )
    have [adj_cs_simps]:
      "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<^bsub>op_cat \<CC>,\<DD>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F =
        ntcf_ua_of \<alpha> \<GG> a (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
    proof(rule ntcf_eqI)
      from assms(1-5) caou_\<eta> prems show lhs: 
        "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<^bsub>op_cat \<CC>,\<DD>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F :
          Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) \<circ>\<^sub>C\<^sub>F \<GG> :
          \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros cat_op_intros
          )
      from ua_of_\<eta>a show rhs:
        "ntcf_ua_of \<alpha> \<GG> a (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) :
          Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) \<circ>\<^sub>C\<^sub>F \<GG> :
          \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
        by (cs_concl cs_intro: ntcf_cs_intros)
      from lhs have dom_lhs:
        "\<D>\<^sub>\<circ> ((cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<^bsub>op_cat \<CC>,\<DD>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>) =
          \<DD>\<lparr>Obj\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps)
      from lhs assms(4) have dom_rhs:
        "\<D>\<^sub>\<circ> (ntcf_ua_of \<alpha> \<GG> a (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)\<lparr>NTMap\<rparr>) = \<DD>\<lparr>Obj\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps)
      show 
        "(cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<^bsub>op_cat \<CC>,\<DD>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr> =
          ntcf_ua_of \<alpha> \<GG> a (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)\<lparr>NTMap\<rparr>"
      proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
        fix d assume prems': "d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
        from assms(3,4) prems prems' show 
          "(cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<^bsub>op_cat \<CC>,\<DD>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>\<lparr>d\<rparr> =
            ntcf_ua_of \<alpha> \<GG> a (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)\<lparr>NTMap\<rparr>\<lparr>d\<rparr>"
          by (cs_concl cs_simp: adj_cs_simps cat_cs_simps)
      qed (simp_all add: bnt_proj_snd_NTMap_vsv \<GG>.ntcf_ua_of_NTMap_vsv)
    qed simp_all
    from assms(1-5) assms(6)[OF prems] prems show 
      "cf_adjunction_AdjNT_of_unit \<alpha> \<FF> \<GG> \<eta>\<^bsub>op_cat \<CC>,\<DD>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F :
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(\<FF>-,-)\<^bsub>op_cat \<CC>,\<DD>\<^esub>(a,-)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)\<^bsub>op_cat \<CC>,\<DD>\<^esub>(a,-)\<^sub>C\<^sub>F :
        \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by (cs_concl cs_simp: adj_cs_simps cat_cs_simps cs_intro: cat_cs_intros)
  qed (auto simp: cf_adjunction_of_unit_def nat_omega_simps)

  show "\<eta>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>) = \<eta>"
  proof(rule ntcf_eqI)
    from caou_\<eta> show lhs:
      "\<eta>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>) :
        cf_id \<CC> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: adj_cs_intros)
    show rhs: "\<eta> : cf_id \<CC> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (auto intro: cat_cs_intros)
    from lhs have dom_lhs:
      "\<D>\<^sub>\<circ> (\<eta>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>)\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)
    have dom_rhs: "\<D>\<^sub>\<circ> (\<eta>\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>" by (auto simp: cat_cs_simps)
    show "\<eta>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>)\<lparr>NTMap\<rparr> = \<eta>\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a assume prems: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
      from assms(1-5) prems caou_\<eta> show 
        "\<eta>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: 
                adj_cs_simps cat_cs_simps cf_adjunction_of_unit_components(3) 
              cs_intro: cat_cs_intros
          )
    qed (auto intro: adj_cs_intros)
  qed simp_all

qed



subsection\<open>
Construction of an adjunction from a functor and universal morphisms 
from objects to functors
\<close>


text\<open>
The subsection presents the construction of an adjunction given 
a functor and a structured collection of universal morphisms 
from objects to functors.
The content of this subsection follows the statement and the proof
of Theorem 2-ii in Chapter IV-1 in \cite{mac_lane_categories_2010}.
\<close>


subsubsection\<open>Left adjoint\<close>

definition cf_la_of_ra :: "(V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_la_of_ra F \<GG> \<eta> =
    [
      (\<lambda>x\<in>\<^sub>\<circ>\<GG>\<lparr>HomCod\<rparr>\<lparr>Obj\<rparr>. F x),
      (
        \<lambda>h\<in>\<^sub>\<circ>\<GG>\<lparr>HomCod\<rparr>\<lparr>Arr\<rparr>. THE f'.
          f' : F (\<GG>\<lparr>HomCod\<rparr>\<lparr>Dom\<rparr>\<lparr>h\<rparr>) \<mapsto>\<^bsub>\<GG>\<lparr>HomDom\<rparr>\<^esub> F (\<GG>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>h\<rparr>) \<and>
            \<eta>\<lparr>NTMap\<rparr>\<lparr>\<GG>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>h\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<GG>\<lparr>HomCod\<rparr>\<^esub> h =
              (
                umap_of
                  \<GG>
                  (\<GG>\<lparr>HomCod\<rparr>\<lparr>Dom\<rparr>\<lparr>h\<rparr>)
                  (F (\<GG>\<lparr>HomCod\<rparr>\<lparr>Dom\<rparr>\<lparr>h\<rparr>))
                  (\<eta>\<lparr>NTMap\<rparr>\<lparr>\<GG>\<lparr>HomCod\<rparr>\<lparr>Dom\<rparr>\<lparr>h\<rparr>\<rparr>)
                  (F (\<GG>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>h\<rparr>))
              )\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
      ),
      \<GG>\<lparr>HomCod\<rparr>,
      \<GG>\<lparr>HomDom\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_la_of_ra_components:
  shows "cf_la_of_ra F \<GG> \<eta>\<lparr>ObjMap\<rparr> = (\<lambda>x\<in>\<^sub>\<circ>\<GG>\<lparr>HomCod\<rparr>\<lparr>Obj\<rparr>. F x)"
    and "cf_la_of_ra F \<GG> \<eta>\<lparr>ArrMap\<rparr> =
      (
        \<lambda>h\<in>\<^sub>\<circ>\<GG>\<lparr>HomCod\<rparr>\<lparr>Arr\<rparr>. THE f'.
          f' : F (\<GG>\<lparr>HomCod\<rparr>\<lparr>Dom\<rparr>\<lparr>h\<rparr>) \<mapsto>\<^bsub>\<GG>\<lparr>HomDom\<rparr>\<^esub> F (\<GG>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>h\<rparr>) \<and>
          \<eta>\<lparr>NTMap\<rparr>\<lparr>\<GG>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>h\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<GG>\<lparr>HomCod\<rparr>\<^esub> h =
            (
              umap_of
                \<GG> 
                (\<GG>\<lparr>HomCod\<rparr>\<lparr>Dom\<rparr>\<lparr>h\<rparr>)
                (F (\<GG>\<lparr>HomCod\<rparr>\<lparr>Dom\<rparr>\<lparr>h\<rparr>))
                (\<eta>\<lparr>NTMap\<rparr>\<lparr>\<GG>\<lparr>HomCod\<rparr>\<lparr>Dom\<rparr>\<lparr>h\<rparr>\<rparr>)
                (F (\<GG>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>h\<rparr>))
            )\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
      )"
    and "cf_la_of_ra F \<GG> \<eta>\<lparr>HomDom\<rparr> = \<GG>\<lparr>HomCod\<rparr>"
    and "cf_la_of_ra F \<GG> \<eta>\<lparr>HomCod\<rparr> = \<GG>\<lparr>HomDom\<rparr>"
  unfolding cf_la_of_ra_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda cf_la_of_ra_components(1)
  |vsv cf_la_of_ra_ObjMap_vsv[adj_cs_intros]|

mk_VLambda (in is_functor) 
  cf_la_of_ra_components(1)[where ?\<GG>=\<FF>, unfolded cf_HomCod]
  |vdomain cf_la_of_ra_ObjMap_vdomain[adj_cs_simps]|
  |app cf_la_of_ra_ObjMap_app[adj_cs_simps]|

lemmas [adj_cs_simps] =
  is_functor.cf_la_of_ra_ObjMap_vdomain
  is_functor.cf_la_of_ra_ObjMap_app
  

subsubsection\<open>Arrow map\<close>

mk_VLambda cf_la_of_ra_components(2)
  |vsv cf_la_of_ra_ArrMap_vsv[adj_cs_intros]|

mk_VLambda (in is_functor) 
  cf_la_of_ra_components(2)[where ?\<GG>=\<FF>, unfolded cf_HomCod cf_HomDom]
  |vdomain cf_la_of_ra_ArrMap_vdomain[adj_cs_simps]|
  |app cf_la_of_ra_ArrMap_app| (*not for general use*)

lemmas [adj_cs_simps] = is_functor.cf_la_of_ra_ArrMap_vdomain

lemma (in is_functor) cf_la_of_ra_ArrMap_app':
  assumes "h : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows 
    "cf_la_of_ra F \<FF> \<eta>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> =
      (
        THE f'.
          f' : F a \<mapsto>\<^bsub>\<AA>\<^esub> F b \<and>
          \<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> h = umap_of \<FF> a (F a) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) (F b)\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
      )"
proof-
  from assms have h: "h \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" by (simp add: cat_cs_intros)
  from assms have h_Dom: "\<BB>\<lparr>Dom\<rparr>\<lparr>h\<rparr> = a" and h_Cod: "\<BB>\<lparr>Cod\<rparr>\<lparr>h\<rparr> = b"
    by (simp_all add: cat_cs_simps)
  show ?thesis by (rule cf_la_of_ra_ArrMap_app[OF h, unfolded h_Dom h_Cod])
qed

lemma cf_la_of_ra_ArrMap_app_unique:
  assumes "\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "universal_arrow_of \<GG> a (cf_la_of_ra F \<GG> \<eta>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
    and "universal_arrow_of \<GG> b (cf_la_of_ra F \<GG> \<eta>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>)"
  shows "cf_la_of_ra F \<GG> \<eta>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : F a \<mapsto>\<^bsub>\<DD>\<^esub> F b"
    and "\<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = umap_of
      \<GG> a (F a) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) (F b)\<lparr>ArrVal\<rparr>\<lparr>cf_la_of_ra F \<GG> \<eta>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>"
    and "\<And>f'.
      \<lbrakk>
        f' : F a \<mapsto>\<^bsub>\<DD>\<^esub> F b;
        \<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = umap_of \<GG> a (F a) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) (F b)\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
      \<rbrakk> \<Longrightarrow> cf_la_of_ra F \<GG> \<eta>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = f'"
proof-

  interpret \<GG>: is_functor \<alpha> \<DD> \<CC> \<GG> by (rule assms(1))

  from assms(2) have a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    by (simp_all add: cat_cs_intros)
  note ua_\<eta>_a = \<GG>.universal_arrow_ofD[OF assms(3)]
  note ua_\<eta>_b = \<GG>.universal_arrow_ofD[OF assms(4)]
  from ua_\<eta>_b(2) have [cat_cs_intros]: 
    "\<lbrakk> c = b; c' = \<GG>\<lparr>ObjMap\<rparr>\<lparr>cf_la_of_ra F \<GG> \<eta>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr> \<rbrakk> \<Longrightarrow>
      \<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> : c \<mapsto>\<^bsub>\<CC>\<^esub> c'"
    for c c'
    by auto
  from assms(1,2) ua_\<eta>_a(2) have \<eta>a_f:
    "\<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>cf_la_of_ra F \<GG> \<eta>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms(1,2) have lara_a: "cf_la_of_ra F \<GG> \<eta>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = F a"
    and lara_b: "cf_la_of_ra F \<GG> \<eta>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> = F b"
    by (cs_concl cs_simp: adj_cs_simps cs_intro: cat_cs_intros)+

  from theD
    [
      OF 
        ua_\<eta>_a(3)[OF ua_\<eta>_b(1) \<eta>a_f, unfolded lara_a lara_b] 
        \<GG>.cf_la_of_ra_ArrMap_app'[OF assms(2), of F \<eta>]
    ]
  show "cf_la_of_ra F \<GG> \<eta>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : F a \<mapsto>\<^bsub>\<DD>\<^esub> F b"
    and "\<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = umap_of
      \<GG> a (F a) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) (F b)\<lparr>ArrVal\<rparr>\<lparr>cf_la_of_ra F \<GG> \<eta>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>"
    and "\<And>f'.
      \<lbrakk>
        f' : F a \<mapsto>\<^bsub>\<DD>\<^esub> F b;
        \<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = umap_of \<GG> a (F a) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) (F b)\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
      \<rbrakk> \<Longrightarrow> cf_la_of_ra F \<GG> \<eta>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = f'"
    by blast+

qed

lemma cf_la_of_ra_ArrMap_app_is_arr[adj_cs_intros]:
  assumes "\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "universal_arrow_of \<GG> a (cf_la_of_ra F \<GG> \<eta>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
    and "universal_arrow_of \<GG> b (cf_la_of_ra F \<GG> \<eta>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>)"
    and "Fa = F a"
    and "Fb = F b"
  shows "cf_la_of_ra F \<GG> \<eta>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : Fa \<mapsto>\<^bsub>\<DD>\<^esub> Fb"
  using assms(1-4) unfolding assms(5,6) by (rule cf_la_of_ra_ArrMap_app_unique)


subsubsection\<open>
An adjunction constructed from a functor and universal morphisms 
from objects to functors is an adjunction
\<close>

lemma cf_la_of_ra_is_functor:
  assumes "\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> F c \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow>
      universal_arrow_of \<GG> c (cf_la_of_ra F \<GG> \<eta>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>)"
    and "\<And>c c' h. h : c \<mapsto>\<^bsub>\<CC>\<^esub> c' \<Longrightarrow>
      \<GG>\<lparr>ArrMap\<rparr>\<lparr>cf_la_of_ra F \<GG> \<eta>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>) =
        (\<eta>\<lparr>NTMap\<rparr>\<lparr>c'\<rparr>) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h"
  shows "cf_la_of_ra F \<GG> \<eta> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" (is \<open>?\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>\<close>)
proof-

  interpret \<GG>: is_functor \<alpha> \<DD> \<CC> \<GG> by (rule assms(1))

  show "cf_la_of_ra F \<GG> \<eta> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  proof(rule is_functorI')

    show "vfsequence ?\<FF>" unfolding cf_la_of_ra_def by auto
    show "vcard ?\<FF> = 4\<^sub>\<nat>" 
      unfolding cf_la_of_ra_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (?\<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    proof(rule vsv.vsv_vrange_vsubset, unfold \<GG>.cf_la_of_ra_ObjMap_vdomain)
      fix x assume "x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
      with assms(1) show "?\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
        by (cs_concl cs_simp: adj_cs_simps cs_intro: assms(2))
    qed (auto intro: adj_cs_intros)

    show "?\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : ?\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> ?\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for a b f
    proof-
      from that have a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
        by (simp_all add: cat_cs_intros)
      have ua_\<eta>_a: "universal_arrow_of \<GG> a (?\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
        and ua_\<eta>_b: "universal_arrow_of \<GG> b (?\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>)"
        by (intro assms(3)[OF a] assms(3)[OF b])+
      from a b cf_la_of_ra_ArrMap_app_unique(1)[OF assms(1) that ua_\<eta>_a ua_\<eta>_b] 
      show ?thesis 
        by (cs_concl cs_simp: adj_cs_simps)
    qed

    show "?\<FF>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr> = ?\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> ?\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      if "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for b c g a f
    proof-

      from that have a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
        by (simp_all add: cat_cs_intros)
      from assms(1) that have gf: "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

      note ua_\<eta>_a = assms(3)[OF a]
        and ua_\<eta>_b = assms(3)[OF b]
        and ua_\<eta>_c = assms(3)[OF c]

      note lara_f = 
        cf_la_of_ra_ArrMap_app_unique[OF assms(1) that(2) ua_\<eta>_a ua_\<eta>_b]
      note lara_g = 
        cf_la_of_ra_ArrMap_app_unique[OF assms(1) that(1) ua_\<eta>_b ua_\<eta>_c]
      note lara_gf = 
        cf_la_of_ra_ArrMap_app_unique[OF assms(1) gf ua_\<eta>_a ua_\<eta>_c]

      note ua_\<eta>_a = \<GG>.universal_arrow_ofD[OF ua_\<eta>_a]
        and ua_\<eta>_b = \<GG>.universal_arrow_ofD[OF ua_\<eta>_b]
        and ua_\<eta>_c = \<GG>.universal_arrow_ofD[OF ua_\<eta>_c]
      
      from ua_\<eta>_a(2) assms(1) that have \<eta>a: 
        "\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>F a\<rparr>"
        by (cs_prems cs_simp: adj_cs_simps cs_intro: cat_cs_intros)
      from ua_\<eta>_b(2) assms(1) that have \<eta>b: 
        "\<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> : b \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>F b\<rparr>"
        by (cs_prems cs_simp: adj_cs_simps cs_intro: cat_cs_intros)
      from ua_\<eta>_c(2) assms(1) that have \<eta>c: 
        "\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : c \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>F c\<rparr>"
        by (cs_prems cs_simp: adj_cs_simps cs_intro: cat_cs_intros)

      from assms(1) that \<eta>c have
        "\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) = (\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      also from assms(1) lara_g(1) that(2) \<eta>b have "\<dots> =
        \<GG>\<lparr>ArrMap\<rparr>\<lparr>?\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)"
        by 
          (
            cs_concl 
              cs_simp: lara_g(2) cat_cs_simps 
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
      also from assms(1) lara_f(1) \<eta>a have "\<dots> =
        \<GG>\<lparr>ArrMap\<rparr>\<lparr>?\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> 
          (\<GG>\<lparr>ArrMap\<rparr>\<lparr>?\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
        by (cs_concl cs_simp: lara_f(2) cat_cs_simps)
      finally have [symmetric, cat_cs_simps]: 
        "\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) = \<dots>".
      from assms(1) this \<eta>a \<eta>b \<eta>c lara_g(1) lara_f(1) have 
        "\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) =
          umap_of \<GG> a (F a) (\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) (F c)\<lparr>ArrVal\<rparr>\<lparr>?\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub>
          ?\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>"
        by 
          ( 
            cs_concl 
              cs_simp: adj_cs_simps cat_cs_simps 
              cs_intro: adj_cs_intros cat_cs_intros
          )
      moreover from assms(1) lara_g(1) lara_f(1) have 
        "?\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> ?\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : F a \<mapsto>\<^bsub>\<DD>\<^esub> F c"
        by (cs_concl cs_intro: adj_cs_intros cat_cs_intros)
      ultimately show ?thesis by (intro lara_gf(3))

    qed

    show "?\<FF>\<lparr>ArrMap\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<DD>\<lparr>CId\<rparr>\<lparr>?\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>" if "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for c 
    proof-
      note lara_c = cf_la_of_ra_ArrMap_app_unique[
          OF 
            assms(1) 
            \<GG>.HomCod.cat_CId_is_arr[OF that] 
            assms(3)[OF that] 
            assms(3)[OF that]
          ]
      from assms(1) that have \<DD>c: "\<DD>\<lparr>CId\<rparr>\<lparr>F c\<rparr> : F c \<mapsto>\<^bsub>\<DD>\<^esub> F c "
        by (cs_concl cs_simp: cat_cs_simps cs_intro: assms(2) cat_cs_intros)
      from \<GG>.universal_arrow_ofD(2)[OF assms(3)[OF that]] assms(1) that have \<eta>c: 
        "\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> : c \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>F c\<rparr>"
        by (cs_prems cs_simp: adj_cs_simps cs_intro: cat_cs_intros)
      from assms(1) that \<eta>c have 
        "\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr> =
          umap_of \<GG> c (F c) (\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>) (F c)\<lparr>ArrVal\<rparr>\<lparr>\<DD>\<lparr>CId\<rparr>\<lparr>F c\<rparr>\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: assms(2) cat_cs_intros)
      note [cat_cs_simps] = lara_c(3)[OF \<DD>c this]
      from assms(1) that \<DD>c show ?thesis
        by (cs_concl cs_simp: adj_cs_simps cat_cs_simps cs_intro: cat_cs_intros)
    qed
  qed (auto simp: cf_la_of_ra_components cat_cs_intros cat_cs_simps)

qed

lemma cf_la_of_ra_is_ntcf:  
  fixes F \<GG> \<eta>
  defines "\<FF> \<equiv> cf_la_of_ra F \<GG> \<eta>"
  assumes "\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> F c \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow>
      universal_arrow_of \<GG> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>)"
    and "\<And>c c' h. h : c \<mapsto>\<^bsub>\<CC>\<^esub> c' \<Longrightarrow>
      \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>) = (\<eta>\<lparr>NTMap\<rparr>\<lparr>c'\<rparr>) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h"
    and "vfsequence \<eta>"
    and "vcard \<eta> = 5\<^sub>\<nat>"
    and "\<eta>\<lparr>NTDom\<rparr> = cf_id \<CC>"
    and "\<eta>\<lparr>NTCod\<rparr> = \<GG> \<circ>\<^sub>C\<^sub>F \<FF>"
    and "\<eta>\<lparr>NTDGDom\<rparr> = \<CC>"
    and "\<eta>\<lparr>NTDGCod\<rparr> = \<CC>"
    and "vsv (\<eta>\<lparr>NTMap\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<eta>\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
  shows "\<eta> : cf_id \<CC> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<GG>: is_functor \<alpha> \<DD> \<CC> \<GG> by (rule assms(2))
  have \<FF>: "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    unfolding \<FF>_def
    by (auto intro: cf_la_of_ra_is_functor[OF assms(2-5)[unfolded assms(1)]])
  show "\<eta> : cf_id \<CC> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  proof(rule is_ntcfI')
    from assms(2) show "cf_id \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms(2) \<FF> show "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    show "\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : cf_id \<CC>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for a
      using assms(2) \<FF> that \<GG>.universal_arrow_ofD(2)[OF assms(4)[OF that]]
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    show 
      "\<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> cf_id \<CC>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for a b f
      using assms(2) \<FF> that 
      by (cs_concl cs_simp: assms(5) cat_cs_simps cs_intro: cat_cs_intros)
  qed (auto intro: assms(6-13))
qed

lemma cf_la_of_ra_is_unit:  
  fixes F \<GG> \<eta>
  defines "\<FF> \<equiv> cf_la_of_ra F \<GG> \<eta>"
  assumes "category \<alpha> \<CC>"
    and "category \<alpha> \<DD>"
    and "\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> F c \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow>
      universal_arrow_of \<GG> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>)"
    and "\<And>c c' h. h : c \<mapsto>\<^bsub>\<CC>\<^esub> c' \<Longrightarrow>
      \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>) = (\<eta>\<lparr>NTMap\<rparr>\<lparr>c'\<rparr>) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h"
    and "vfsequence \<eta>"
    and "vcard \<eta> = 5\<^sub>\<nat>"
    and "\<eta>\<lparr>NTDom\<rparr> = cf_id \<CC>"
    and "\<eta>\<lparr>NTCod\<rparr> = \<GG> \<circ>\<^sub>C\<^sub>F \<FF>"
    and "\<eta>\<lparr>NTDGDom\<rparr> = \<CC>"
    and "\<eta>\<lparr>NTDGCod\<rparr> = \<CC>"
    and "vsv (\<eta>\<lparr>NTMap\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<eta>\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
  shows "cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<eta>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>) = \<eta>"
proof-
  note \<FF> = cf_la_of_ra_is_functor[
    where F=F and \<eta>=\<eta>, OF assms(4-7)[unfolded \<FF>_def], simplified
    ]
  note \<eta> = cf_la_of_ra_is_ntcf[OF assms(4-15)[unfolded \<FF>_def], simplified]
  show "cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<eta>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>) = \<eta>"
    by 
      (
        intro 
          cf_adjunction_of_unit_is_cf_adjunction
            [
              OF assms(2,3) \<FF> assms(4) \<eta> assms(6)[unfolded \<FF>_def], 
              simplified, 
              folded \<FF>_def
            ]
      )+
qed



subsection\<open>
Construction of an adjunction from universal morphisms 
from functors to objects
\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The subsection presents the construction of an adjunction given 
a structured collection of universal morphisms from functors to objects.
The content of this subsection follows the statement and the proof
of Theorem 2-iii in Chapter IV-1 in \cite{mac_lane_categories_2010}.
\<close>

definition cf_adjunction_of_counit :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon> =
    op_cf_adj (cf_adjunction_of_unit \<alpha> (op_cf \<GG>) (op_cf \<FF>) (op_ntcf \<epsilon>))"


text\<open>Components.\<close>

lemma cf_adjunction_of_counit_components:
  shows "cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>\<lparr>AdjLeft\<rparr> = op_cf (op_cf \<FF>)"
    and "cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>\<lparr>AdjRight\<rparr> = op_cf (op_cf \<GG>)"
    and "cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>\<lparr>AdjNT\<rparr> = op_cf_adj_nt
      (op_cf \<GG>\<lparr>HomDom\<rparr>)
      (op_cf \<GG>\<lparr>HomCod\<rparr>)
      (cf_adjunction_AdjNT_of_unit \<alpha> (op_cf \<GG>) (op_cf \<FF>) (op_ntcf \<epsilon>))"
  unfolding 
    cf_adjunction_of_counit_def 
    op_cf_adj_components 
    cf_adjunction_of_unit_components
  by (simp_all add: cat_op_simps)


subsubsection\<open>Natural transformation map\<close>

lemma cf_adjunction_of_counit_NTMap_vsv: 
  "vsv (cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>)"
  unfolding cf_adjunction_of_counit_components by (rule inv_ntcf_NTMap_vsv)
  


subsubsection\<open>
An adjunction constructed from universal morphisms 
from functors to objects is an adjunction
\<close>

lemma cf_adjunction_of_counit_is_cf_adjunction:
  assumes "category \<alpha> \<CC>"
    and "category \<alpha> \<DD>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<epsilon> : \<FF> \<circ>\<^sub>C\<^sub>F \<GG> \<mapsto>\<^sub>C\<^sub>F cf_id \<DD> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<And>x. x \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr> \<Longrightarrow> universal_arrow_fo \<FF> x (\<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>)"
  shows "cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<epsilon>\<^sub>C (cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>) = \<epsilon>"
    and "\<D>\<^sub>\<circ> (cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>) = 
      (op_cat \<CC> \<times>\<^sub>C \<DD>)\<lparr>Obj\<rparr>"
    and "\<And>c d. \<lbrakk> c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow>
      cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>c, d\<rparr>\<^sub>\<bullet> =
        (umap_fo \<FF> d (\<GG>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>) c)\<inverse>\<^sub>S\<^sub>e\<^sub>t"
proof-

  interpret \<CC>: category \<alpha> \<CC> by (rule assms(1))
  interpret \<DD>: category \<alpha> \<DD> by (rule assms(2))
  interpret \<FF>: is_functor \<alpha> \<CC> \<DD> \<FF> by (rule assms(3))
  interpret \<GG>: is_functor \<alpha> \<DD> \<CC> \<GG> by (rule assms(4))
  interpret \<epsilon>: is_ntcf \<alpha> \<DD> \<DD> \<open>\<FF> \<circ>\<^sub>C\<^sub>F \<GG>\<close> \<open>cf_id \<DD>\<close> \<epsilon> by (rule assms(5))
  
  note cf_adjunction_of_counit_def' = 
    cf_adjunction_of_counit_def[where \<FF>=\<FF>, unfolded \<FF>.cf_HomDom \<FF>.cf_HomCod]
  
  have ua:
    "universal_arrow_of (op_cf \<FF>) x (op_cf \<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) (op_ntcf \<epsilon>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>)"
    if "x \<in>\<^sub>\<circ> op_cat \<DD>\<lparr>Obj\<rparr>" for x
    using that unfolding cat_op_simps by (rule assms(6))
  
  let ?aou = \<open>cf_adjunction_of_unit \<alpha> (op_cf \<GG>) (op_cf \<FF>) (op_ntcf \<epsilon>)\<close>
  from 
    cf_adjunction_of_unit_is_cf_adjunction
      [
        OF 
          \<DD>.category_op
          \<CC>.category_op
          \<GG>.is_functor_op
          \<FF>.is_functor_op
          \<epsilon>.is_ntcf_op[unfolded cat_op_simps]
          ua,
        simplified cf_adjunction_of_counit_def[symmetric]
      ]
  have aou: "?aou : op_cf \<GG> \<rightleftharpoons>\<^sub>C\<^sub>F op_cf \<FF> : op_cat \<DD> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    and \<eta>_aou: "\<eta>\<^sub>C ?aou = op_ntcf \<epsilon>"
    by auto
  interpret aou: 
    is_cf_adjunction \<alpha> \<open>op_cat \<DD>\<close> \<open>op_cat \<CC>\<close> \<open>op_cf \<GG>\<close> \<open>op_cf \<FF>\<close> ?aou
    by (rule aou)
  from \<eta>_aou have
    "op_ntcf (\<eta>\<^sub>C ?aou) = op_ntcf (op_ntcf \<epsilon>)"
    by simp
  then show "\<epsilon>\<^sub>C (cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>) = \<epsilon>"
    unfolding 
      \<epsilon>.ntcf_op_ntcf_op_ntcf
      is_cf_adjunction.op_ntcf_cf_adjunction_unit[OF aou]
      cf_adjunction_of_counit_def'[symmetric]
    by (simp add: cat_op_simps)
  show aoc_\<epsilon>: "cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by 
      (
        rule 
          is_cf_adjunction_op[
            OF aou, folded cf_adjunction_of_counit_def', unfolded cat_op_simps
          ]
      )
  interpret aoc_\<epsilon>: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG> \<open>cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>\<close>
    by (rule aoc_\<epsilon>)

  from aoc_\<epsilon>.NT.is_ntcf_axioms show
    "\<D>\<^sub>\<circ> (cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>) = (op_cat \<CC> \<times>\<^sub>C \<DD>)\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)

  show "\<And>c d. \<lbrakk> c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow>
    cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>c, d\<rparr>\<^sub>\<bullet> =
      (umap_fo \<FF> d (\<GG>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>) c)\<inverse>\<^sub>S\<^sub>e\<^sub>t"
  proof-
    fix c d assume prems: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    from assms(1-4) prems have aou_dc:
      "cf_adjunction_AdjNT_of_unit 
        \<alpha> (op_cf \<GG>) (op_cf \<FF>) (op_ntcf \<epsilon>)\<lparr>NTMap\<rparr>\<lparr>d, c\<rparr>\<^sub>\<bullet> =
        umap_fo \<FF> d (\<GG>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>) c"
      by (cs_concl cs_simp: cat_op_simps adj_cs_simps cs_intro: cat_op_intros)
    from assms(1-4) aou prems have ufo_\<epsilon>_dc:
      "umap_fo \<FF> d (\<GG>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>) c :
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(op_cf \<GG>-,-)\<lparr>ObjMap\<rparr>\<lparr>d, c\<rparr>\<^sub>\<bullet> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub>
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<DD>(-,op_cf \<FF>-)\<lparr>ObjMap\<rparr>\<lparr>d, c\<rparr>\<^sub>\<bullet>"
      by 
        (
          cs_concl 
            cs_simp: 
              aou_dc[symmetric] cf_adjunction_of_unit_components(3)[symmetric]
            cs_intro: 
              is_iso_ntcf.iso_ntcf_is_arr_isomorphism' 
              adj_cs_intros 
              cat_cs_intros 
              cat_op_intros
              cat_prod_cs_intros
        )
    from 
      assms(1-4) 
      aoc_\<epsilon>[unfolded cf_adjunction_of_counit_def'] 
      aou 
      prems 
      ufo_\<epsilon>_dc
    show
      "cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>\<lparr>AdjNT\<rparr>\<lparr>NTMap\<rparr>\<lparr>c, d\<rparr>\<^sub>\<bullet> =
        (umap_fo \<FF> d (\<GG>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>) c)\<inverse>\<^sub>S\<^sub>e\<^sub>t"
      unfolding cf_adjunction_of_counit_def'
      by 
        ( 
          cs_concl 
            cs_simp: cat_op_simps adj_cs_simps cat_cs_simps cat_Set_cs_simps 
            cs_intro: adj_cs_intros cat_cs_intros cat_prod_cs_intros
        )
  qed

qed



subsection\<open>
Construction of an adjunction from a functor and universal morphisms
from functors to objects
\<close>


text\<open>
The subsection presents the construction of an adjunction given 
a functor and a structured collection of universal morphisms 
from functors to objects.
The content of this subsection follows the statement and the proof
of Theorem 2-iv in Chapter IV-1 in \cite{mac_lane_categories_2010}.
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cf_ra_of_la :: "(V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_ra_of_la F \<FF> \<epsilon> = op_cf (cf_la_of_ra F (op_cf \<FF>) (op_ntcf \<epsilon>))"


subsubsection\<open>Object map\<close>

lemma cf_ra_of_la_ObjMap_vsv[adj_cs_intros]: "vsv (cf_ra_of_la F \<FF> \<epsilon>\<lparr>ObjMap\<rparr>)"
  unfolding cf_ra_of_la_def op_cf_components by (auto intro: adj_cs_intros)

lemma (in is_functor) cf_ra_of_la_ObjMap_vdomain: 
  "\<D>\<^sub>\<circ> (cf_ra_of_la F \<FF> \<epsilon>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
  unfolding cf_ra_of_la_def cf_la_of_ra_components cat_op_simps 
  by (simp add: cat_cs_simps)

lemmas [adj_cs_simps] = is_functor.cf_ra_of_la_ObjMap_vdomain

lemma (in is_functor) cf_ra_of_la_ObjMap_app: 
  assumes "d \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "cf_ra_of_la F \<FF> \<epsilon>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr> = F d"
  using assms 
  unfolding cf_ra_of_la_def cf_la_of_ra_components cat_op_simps
  by (simp add: cat_cs_simps)

lemmas [adj_cs_simps] = is_functor.cf_ra_of_la_ObjMap_app


subsubsection\<open>Arrow map\<close>

lemma cf_ra_of_la_ArrMap_app_unique:
  assumes "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "f : a \<mapsto>\<^bsub>\<DD>\<^esub> b"
    and "universal_arrow_fo \<FF> a (cf_ra_of_la F \<FF> \<epsilon>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
    and "universal_arrow_fo \<FF> b (cf_ra_of_la F \<FF> \<epsilon>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>)"
  shows "cf_ra_of_la F \<FF> \<epsilon>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : F a \<mapsto>\<^bsub>\<CC>\<^esub> F b"
    and "f \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
      umap_fo \<FF> b (F b) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>) (F a)\<lparr>ArrVal\<rparr>\<lparr>cf_ra_of_la F \<FF> \<epsilon>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>"
    and "\<And>f'.
      \<lbrakk>
        f' : F a \<mapsto>\<^bsub>\<CC>\<^esub> F b;
        f \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = umap_fo \<FF> b (F b) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>) (F a)\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
      \<rbrakk> \<Longrightarrow> cf_ra_of_la F \<FF> \<epsilon>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = f'"
proof-
  interpret \<FF>: is_functor \<alpha> \<CC> \<DD> \<FF> by (rule assms(1))
  from assms(2) have op_f: "f : b \<mapsto>\<^bsub>op_cat \<DD>\<^esub> a" unfolding cat_op_simps by simp
  let ?lara = \<open>cf_la_of_ra F (op_cf \<FF>) (op_ntcf \<epsilon>)\<close>
  have lara_ObjMap_eq_op: "?lara\<lparr>ObjMap\<rparr> = (op_cf ?lara\<lparr>ObjMap\<rparr>)"
    and lara_ArrMap_eq_op: "?lara\<lparr>ArrMap\<rparr> = (op_cf ?lara\<lparr>ArrMap\<rparr>)"
    unfolding cat_op_simps by simp_all
  note ua_\<eta>_a = \<FF>.universal_arrow_foD[OF assms(3)]
    and ua_\<eta>_b = \<FF>.universal_arrow_foD[OF assms(4)]
  from assms(1,2) ua_\<eta>_a(2) have [cat_op_simps]:
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<DD>\<^esub> f = f \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cat_op_simps)
  show "cf_ra_of_la F \<FF> \<epsilon>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : F a \<mapsto>\<^bsub>\<CC>\<^esub> F b"
    and "f \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
      umap_fo \<FF> b (F b) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>) (F a)\<lparr>ArrVal\<rparr>\<lparr>cf_ra_of_la F \<FF> \<epsilon>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>"
    and "\<And>f'.
      \<lbrakk>
        f' : F a \<mapsto>\<^bsub>\<CC>\<^esub> F b;
        f \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = umap_fo \<FF> b (F b) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>) (F a)\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
      \<rbrakk> \<Longrightarrow> cf_ra_of_la F \<FF> \<epsilon>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = f'"
    by 
      (
        intro 
          cf_la_of_ra_ArrMap_app_unique
            [
              where \<eta>=\<open>op_ntcf \<epsilon>\<close> and F=F,
                OF \<FF>.is_functor_op op_f, 
                unfolded 
                  \<FF>.op_cf_universal_arrow_of 
                  lara_ObjMap_eq_op
                  lara_ArrMap_eq_op,
                folded cf_ra_of_la_def,
                unfolded cat_op_simps,
                OF assms(4,3)
            ]
      )+
qed

lemma cf_ra_of_la_ArrMap_app_is_arr[adj_cs_intros]:
  assumes "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "f : a \<mapsto>\<^bsub>\<DD>\<^esub> b"
    and "universal_arrow_fo \<FF> a (cf_ra_of_la F \<FF> \<epsilon>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
    and "universal_arrow_fo \<FF> b (cf_ra_of_la F \<FF> \<epsilon>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>)"
    and "Fa = F a"
    and "Fb = F b"
  shows "cf_ra_of_la F \<FF> \<epsilon>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : Fa \<mapsto>\<^bsub>\<CC>\<^esub> Fb"
  using assms(1-4) unfolding assms(5,6) by (rule cf_ra_of_la_ArrMap_app_unique)


subsubsection\<open>
An adjunction constructed from a functor and universal morphisms 
from functors to objects is an adjunction
\<close>

lemma op_cf_cf_la_of_ra_op[cat_op_simps]: 
  "op_cf (cf_la_of_ra F (op_cf \<FF>) (op_ntcf \<epsilon>)) = cf_ra_of_la F \<FF> \<epsilon>"
  unfolding cf_ra_of_la_def by simp

lemma cf_ra_of_la_commute_op:
  assumes "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<And>d. d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr> \<Longrightarrow>
      universal_arrow_fo \<FF> d (cf_ra_of_la F \<FF> \<epsilon>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>)"
    and "\<And>d d' h. h : d \<mapsto>\<^bsub>\<DD>\<^esub> d' \<Longrightarrow>
      \<epsilon>\<lparr>NTMap\<rparr>\<lparr>d'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>cf_ra_of_la F \<FF> \<epsilon>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>\<rparr> =
        h \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>"
    and "h : c' \<mapsto>\<^bsub>\<DD>\<^esub> c"
  shows "\<FF>\<lparr>ArrMap\<rparr>\<lparr>cf_ra_of_la F \<FF> \<epsilon>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<DD>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> =
    \<epsilon>\<lparr>NTMap\<rparr>\<lparr>c'\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<DD>\<^esub> h"
proof-
  interpret \<FF>: is_functor \<alpha> \<CC> \<DD> \<FF> by (rule assms(1))
  from assms(4) have c': "c' \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>" and c: "c \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>" by auto
  note ua_\<eta>_c' = \<FF>.universal_arrow_foD[OF assms(2)[OF c']]
    and ua_\<eta>_c = \<FF>.universal_arrow_foD[OF assms(2)[OF c]]
  note rala_f = cf_ra_of_la_ArrMap_app_unique[
      OF assms(1) assms(4) assms(2)[OF c'] assms(2)[OF c]
      ]
  from assms(1) assms(4) ua_\<eta>_c'(2) ua_\<eta>_c(2) rala_f(1) show ?thesis
    by 
      (
        cs_concl 
          cs_simp: assms(3) cat_op_simps adj_cs_simps cat_cs_simps 
          cs_intro: cat_cs_intros
      )
qed

lemma 
  assumes "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<And>d. d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr> \<Longrightarrow> F d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<And>d. d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr> \<Longrightarrow>
      universal_arrow_fo \<FF> d (cf_ra_of_la F \<FF> \<epsilon>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>)"
    and "\<And>d d' h. h : d \<mapsto>\<^bsub>\<DD>\<^esub> d' \<Longrightarrow>
      \<epsilon>\<lparr>NTMap\<rparr>\<lparr>d'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>cf_ra_of_la F \<FF> \<epsilon>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>\<rparr> =
        h \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>"
  shows cf_ra_of_la_is_functor: "cf_ra_of_la F \<FF> \<epsilon> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and cf_la_of_ra_op_is_functor:  
      "cf_la_of_ra F (op_cf \<FF>) (op_ntcf \<epsilon>) : op_cat \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
proof-
  interpret \<FF>: is_functor \<alpha> \<CC> \<DD> \<FF> by (rule assms(1))
  have \<FF>h_\<epsilon>c:
    "\<FF>\<lparr>ArrMap\<rparr>\<lparr>cf_ra_of_la F \<FF> \<epsilon>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<DD>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> =
      \<epsilon>\<lparr>NTMap\<rparr>\<lparr>c'\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<DD>\<^esub> h"
    if "h : c' \<mapsto>\<^bsub>\<DD>\<^esub> c" for c c' h
  proof-
    from that have c': "c' \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>" and c: "c \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>" by auto
    note ua_\<eta>_c' = \<FF>.universal_arrow_foD[OF assms(3)[OF c']]
      and ua_\<eta>_c = \<FF>.universal_arrow_foD[OF assms(3)[OF c]]
    note rala_f = cf_ra_of_la_ArrMap_app_unique[
        OF assms(1) that assms(3)[OF c'] assms(3)[OF c]
        ]
    from assms(1) that ua_\<eta>_c'(2) ua_\<eta>_c(2) rala_f(1) show ?thesis
      by 
        (
          cs_concl 
            cs_simp: assms(4) cat_op_simps adj_cs_simps cat_cs_simps 
            cs_intro: cat_cs_intros
        )
  qed
  let ?lara = \<open>cf_la_of_ra F (op_cf \<FF>) (op_ntcf \<epsilon>)\<close>
  have lara_ObjMap_eq_op: "?lara\<lparr>ObjMap\<rparr> = (op_cf ?lara\<lparr>ObjMap\<rparr>)"
    and lara_ArrMap_eq_op: "?lara\<lparr>ArrMap\<rparr> = (op_cf ?lara\<lparr>ArrMap\<rparr>)"
    by (simp_all add: cat_op_simps del: op_cf_cf_la_of_ra_op)
  show "cf_la_of_ra F (op_cf \<FF>) (op_ntcf \<epsilon>) : op_cat \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    by 
      (
        intro cf_la_of_ra_is_functor
          [
            where F=F and \<eta>=\<open>op_ntcf \<epsilon>\<close>,
            OF \<FF>.is_functor_op,
            unfolded cat_op_simps,
            OF assms(2),
            simplified,
            unfolded lara_ObjMap_eq_op lara_ArrMap_eq_op,
            folded cf_ra_of_la_def,
            OF assms(3) \<FF>h_\<epsilon>c
         ]
      )
  from 
    is_functor.is_functor_op[
      OF this, unfolded cat_op_simps, folded cf_ra_of_la_def
      ]
  show "cf_ra_of_la F \<FF> \<epsilon> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>".
qed

lemma cf_ra_of_la_is_ntcf:  
  fixes F \<FF> \<epsilon>
  defines "\<GG> \<equiv> cf_ra_of_la F \<FF> \<epsilon>"
  assumes "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<And>d. d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr> \<Longrightarrow> F d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<And>d. d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr> \<Longrightarrow>
      universal_arrow_fo \<FF> d (\<GG>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>)"
    and "\<And>d d' h. h : d \<mapsto>\<^bsub>\<DD>\<^esub> d' \<Longrightarrow>
      \<epsilon>\<lparr>NTMap\<rparr>\<lparr>d'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<GG>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>\<rparr> = h \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>"
    and "vfsequence \<epsilon>"
    and "vcard \<epsilon> = 5\<^sub>\<nat>"
    and "\<epsilon>\<lparr>NTDom\<rparr> = \<FF> \<circ>\<^sub>C\<^sub>F \<GG>"
    and "\<epsilon>\<lparr>NTCod\<rparr> = cf_id \<DD>"
    and "\<epsilon>\<lparr>NTDGDom\<rparr> = \<DD>"
    and "\<epsilon>\<lparr>NTDGCod\<rparr> = \<DD>"
    and "vsv (\<epsilon>\<lparr>NTMap\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<epsilon>\<lparr>NTMap\<rparr>) = \<DD>\<lparr>Obj\<rparr>"
  shows "\<epsilon> : \<FF> \<circ>\<^sub>C\<^sub>F \<GG> \<mapsto>\<^sub>C\<^sub>F cf_id \<DD> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
proof-

  interpret \<FF>: is_functor \<alpha> \<CC> \<DD> \<FF> by (rule assms(2))
  interpret \<GG>: is_functor \<alpha> \<DD> \<CC> \<GG> 
    unfolding \<GG>_def
    by (auto intro: cf_ra_of_la_is_functor[OF assms(2-5)[unfolded assms(1)]])
  interpret op_\<epsilon>: is_functor 
    \<alpha> \<open>op_cat \<DD>\<close> \<open>op_cat \<CC>\<close> \<open>cf_la_of_ra F (op_cf \<FF>) (op_ntcf \<epsilon>)\<close>
    by 
      (
        intro cf_la_of_ra_op_is_functor[
          where F=F and \<epsilon>=\<epsilon>, OF assms(2,3,4,5)[unfolded \<GG>_def], simplified
          ]
      )
  interpret \<epsilon>: vfsequence \<epsilon> by (rule assms(6))

  have [cat_op_simps]: "op_ntcf (op_ntcf \<epsilon>) = \<epsilon>"
  proof(rule vsv_eqI)
    have dom_lhs: "\<D>\<^sub>\<circ> (op_ntcf (op_ntcf \<epsilon>)) = 5\<^sub>\<nat>"
      unfolding op_ntcf_def by (simp add: nat_omega_simps)
    from assms(7) show "\<D>\<^sub>\<circ> (op_ntcf (op_ntcf \<epsilon>)) = \<D>\<^sub>\<circ> \<epsilon>" 
      by (simp add: dom_lhs \<epsilon>.vfsequence_vdomain)   
    have sup: 
      "op_ntcf (op_ntcf \<epsilon>)\<lparr>NTDom\<rparr> = \<epsilon>\<lparr>NTDom\<rparr>" 
      "op_ntcf (op_ntcf \<epsilon>)\<lparr>NTCod\<rparr> = \<epsilon>\<lparr>NTCod\<rparr>" 
      "op_ntcf (op_ntcf \<epsilon>)\<lparr>NTDGDom\<rparr> = \<epsilon>\<lparr>NTDGDom\<rparr>" 
      "op_ntcf (op_ntcf \<epsilon>)\<lparr>NTDGCod\<rparr> = \<epsilon>\<lparr>NTDGCod\<rparr>" 
      unfolding op_ntcf_components assms(8-11) cat_op_simps
      by simp_all
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (op_ntcf (op_ntcf \<epsilon>)) \<Longrightarrow> op_ntcf (op_ntcf \<epsilon>)\<lparr>a\<rparr> = \<epsilon>\<lparr>a\<rparr>" for a
      by (unfold dom_lhs, elim_in_numeral, fold nt_field_simps, unfold sup)
        (simp_all add: cat_op_simps)
  qed (auto simp: op_ntcf_def)

  let ?lara = \<open>cf_la_of_ra F (op_cf \<FF>) (op_ntcf \<epsilon>)\<close>
  have lara_ObjMap_eq_op: "?lara\<lparr>ObjMap\<rparr> = (op_cf ?lara\<lparr>ObjMap\<rparr>)"
    and lara_ArrMap_eq_op: "?lara\<lparr>ArrMap\<rparr> = (op_cf ?lara\<lparr>ArrMap\<rparr>)"
    by (simp_all add: cat_op_simps del: op_cf_cf_la_of_ra_op)

  have seq: "vfsequence (op_ntcf \<epsilon>)" unfolding op_ntcf_def by auto
  have card: "vcard (op_ntcf \<epsilon>) = 5\<^sub>\<nat>" 
    unfolding op_ntcf_def by (simp add: nat_omega_simps)
  have op_cf_NTCod: "op_cf (\<epsilon>\<lparr>NTCod\<rparr>) = cf_id (op_cat \<DD>)"
    unfolding assms(9) cat_op_simps by simp

  from assms(2) have op_cf_NTDom:
    "op_cf (\<epsilon>\<lparr>NTDom\<rparr>) = op_cf \<FF> \<circ>\<^sub>C\<^sub>F cf_la_of_ra F (op_cf \<FF>) (op_ntcf \<epsilon>)"
    unfolding assms(8) cat_op_simps \<GG>_def 
    by (simp_all add: cat_op_simps cf_ra_of_la_def del: op_cf_cf_la_of_ra_op)
  have "op_ntcf \<epsilon> :
    cf_id (op_cat \<DD>) \<mapsto>\<^sub>C\<^sub>F op_cf \<FF> \<circ>\<^sub>C\<^sub>F cf_la_of_ra F (op_cf \<FF>) (op_ntcf \<epsilon>) :
    op_cat \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<DD>"
    by 
      (
        auto intro: cf_la_of_ra_is_ntcf
          [
            where F=F and \<eta>=\<open>op_ntcf \<epsilon>\<close>,
            OF is_functor.is_functor_op[OF assms(2)],
            unfolded cat_op_simps,
            OF assms(3),
            simplified,
            unfolded 
              lara_ObjMap_eq_op 
              lara_ArrMap_eq_op 
              cf_ra_of_la_def[symmetric],
            OF assms(4)[unfolded \<GG>_def],
            simplified,
            OF cf_ra_of_la_commute_op[
              OF assms(2,4,5)[unfolded \<GG>_def], simplified
              ],
            simplified,
            OF seq card _ op_cf_NTDom _ _ assms(12),
            unfolded assms(8-11,13) cat_op_simps
          ]
      )
  from is_ntcf.is_ntcf_op[OF this, unfolded cat_op_simps \<GG>_def[symmetric]] show 
    "\<epsilon> : \<FF> \<circ>\<^sub>C\<^sub>F \<GG> \<mapsto>\<^sub>C\<^sub>F cf_id \<DD> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>".

qed

lemma cf_ra_of_la_is_counit: 
  fixes F \<FF> \<epsilon>
  defines "\<GG> \<equiv> cf_ra_of_la F \<FF> \<epsilon>"
  assumes "category \<alpha> \<CC>"
    and "category \<alpha> \<DD>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<And>d. d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr> \<Longrightarrow> F d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<And>d. d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr> \<Longrightarrow>
      universal_arrow_fo \<FF> d (\<GG>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>) (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>)"
    and "\<And>d d' h. h : d \<mapsto>\<^bsub>\<DD>\<^esub> d' \<Longrightarrow>
      \<epsilon>\<lparr>NTMap\<rparr>\<lparr>d'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<GG>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>\<rparr> = h \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>"
    and "vfsequence \<epsilon>"
    and "vcard \<epsilon> = 5\<^sub>\<nat>"
    and "\<epsilon>\<lparr>NTDom\<rparr> = \<FF> \<circ>\<^sub>C\<^sub>F \<GG>"
    and "\<epsilon>\<lparr>NTCod\<rparr> = cf_id \<DD>"
    and "\<epsilon>\<lparr>NTDGDom\<rparr> = \<DD>"
    and "\<epsilon>\<lparr>NTDGCod\<rparr> = \<DD>"
    and "vsv (\<epsilon>\<lparr>NTMap\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<epsilon>\<lparr>NTMap\<rparr>) = \<DD>\<lparr>Obj\<rparr>"
  shows "cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<epsilon>\<^sub>C (cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>) = \<epsilon>"
proof-
  note \<FF> = cf_ra_of_la_is_functor[
    where F=F and \<epsilon>=\<epsilon>, OF assms(4-7)[unfolded \<GG>_def], simplified
    ]
  note \<epsilon> = cf_ra_of_la_is_ntcf[OF assms(4-15)[unfolded \<GG>_def], simplified]
  show "cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<epsilon>\<^sub>C (cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>) = \<epsilon>"
    by 
      (
        intro 
          cf_adjunction_of_counit_is_cf_adjunction
            [
              OF assms(2,3,4) \<FF> \<epsilon> assms(6)[unfolded \<GG>_def], 
              simplified, 
              folded \<GG>_def
            ]
      )+
qed



subsection\<open>Construction of an adjunction from the counit-unit equations\<close>


text\<open>
The subsection presents the construction of an adjunction given 
two natural transformations satisfying counit-unit equations.
The content of this subsection follows the statement and the proof
of Theorem 2-v in Chapter IV-1 in \cite{mac_lane_categories_2010}.
\<close>

lemma counit_unit_is_cf_adjunction:
  assumes "category \<alpha> \<CC>"
    and "category \<alpha> \<DD>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<eta> : cf_id \<CC> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<epsilon> : \<FF> \<circ>\<^sub>C\<^sub>F \<GG> \<mapsto>\<^sub>C\<^sub>F cf_id \<DD> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "(\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<eta> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) = ntcf_id \<GG>"
    and "(\<epsilon> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>) = ntcf_id \<FF>"
  shows "cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<eta>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>) = \<eta>"
    and "\<epsilon>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>) = \<epsilon>"
proof-

  interpret \<CC>: category \<alpha> \<CC> by (rule assms(1))
  interpret \<DD>: category \<alpha> \<DD> by (rule assms(2))
  interpret \<FF>: is_functor \<alpha> \<CC> \<DD> \<FF> by (rule assms(3))
  interpret \<GG>: is_functor \<alpha> \<DD> \<CC> \<GG> by (rule assms(4))
  interpret \<eta>: is_ntcf \<alpha> \<CC> \<CC> \<open>cf_id \<CC>\<close> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> \<eta> by (rule assms(5))
  interpret \<epsilon>: is_ntcf \<alpha> \<DD> \<DD> \<open>\<FF> \<circ>\<^sub>C\<^sub>F \<GG>\<close> \<open>cf_id \<DD>\<close> \<epsilon> by (rule assms(6))

  have \<GG>\<epsilon>x_\<eta>\<GG>x[cat_cs_simps]:
    "\<GG>\<lparr>ArrMap\<rparr>\<lparr>\<epsilon>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<eta>\<lparr>NTMap\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>"
    if "x \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>" for x
  proof-
    from assms(7) have 
      "((\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<eta> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>))\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = ntcf_id \<GG>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>"
      by simp
    from this assms(1-6) that show 
      "\<GG>\<lparr>ArrMap\<rparr>\<lparr>\<epsilon>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<eta>\<lparr>NTMap\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr> = 
        \<CC>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>"
      by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed
  have [cat_cs_simps]:
    "\<GG>\<lparr>ArrMap\<rparr>\<lparr>\<epsilon>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<eta>\<lparr>NTMap\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) =
      \<CC>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    if "x \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>" for x f a
    using assms(1-6) that
    by (intro \<CC>.cat_assoc_helper)
      (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+

  have [cat_cs_simps]:
    "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>\<rparr> = \<DD>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>"
    if "x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for x
  proof-
    from assms(8) have 
      "((\<epsilon> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>))\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = ntcf_id \<FF>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>"
      by simp
    from this assms(1-6) that show
      "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>\<rparr> = \<DD>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>"
      by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed

  have ua_\<FF>x_\<eta>x: "universal_arrow_of \<GG> x (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>)"
    if "x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for x 
  proof(intro is_functor.universal_arrow_ofI)
    from assms(3) that show "\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
      by (cs_concl cs_intro: cat_cs_intros)
    from assms(3-6) that show "\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr> : x \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    fix r' u' assume prems': "r' \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>" "u' : x \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>"
    show "\<exists>!f'.
      f' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> r' \<and>
      u' = umap_of \<GG> x (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    proof(intro ex1I conjI; (elim conjE)?)
      from assms(3-6) that prems' show 
        "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>u'\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> r'"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      from assms(3-6) prems' have \<GG>\<FF>u':
        "(\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>u'\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>u'\<rparr>\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      note [cat_cs_simps] = 
        \<eta>.ntcf_Comp_commute[symmetric, OF prems'(2), unfolded \<GG>\<FF>u']
      from assms(3-6) that prems' show 
        "u' =
          umap_of \<GG> x (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) r'\<lparr>ArrVal\<rparr>\<lparr>\<epsilon>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub>
          \<FF>\<lparr>ArrMap\<rparr>\<lparr>u'\<rparr>\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
          )
      fix f' assume prems'':
        "f' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> r'"
        "u' = umap_of \<GG> x (\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>" 
      from prems''(2,1) assms(3-6) that have u'_def:
        "u' = \<GG>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>"
        by 
          (
            cs_prems 
              cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
          )
      from 
        \<epsilon>.ntcf_Comp_commute[OF prems''(1)] 
        assms(3-6) 
        prems''(1) 
      have [cat_cs_simps]:
        "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<GG>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>\<rparr> =
          f' \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>"
        by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      have [cat_cs_simps]:
        "\<epsilon>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> (\<FF>\<lparr>ArrMap\<rparr>\<lparr>\<GG>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> f) =
          (f' \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<epsilon>\<lparr>NTMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>) \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> f"
        if "f : a \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr>\<rparr>" for f a
        using assms(1-6) prems''(1) prems' that
        by (intro \<DD>.cat_assoc_helper)
          (
            cs_concl 
              cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
          )+
      from prems''(2,1) assms(3-6) that show 
        "f' = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>u'\<rparr>"
        unfolding u'_def 
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
          )
    qed
  qed (auto intro: cat_cs_intros)

  show aou: "cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by (intro cf_adjunction_of_unit_is_cf_adjunction ua_\<FF>x_\<eta>x assms(1-5))
  from \<CC>.category_axioms \<DD>.category_axioms show "\<eta>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>) = \<eta>"
    by (cs_concl cs_intro: cf_adjunction_of_unit_is_cf_adjunction assms(1-5) ua_\<FF>x_\<eta>x)

  interpret aou: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG> \<open>cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>\<close>
    by (rule aou)

  show "\<epsilon>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>) = \<epsilon>"
  proof(rule ntcf_eqI)
    show \<epsilon>_\<eta>: "\<epsilon>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>) :
      \<FF> \<circ>\<^sub>C\<^sub>F \<GG> \<mapsto>\<^sub>C\<^sub>F cf_id \<DD> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
      by (rule aou.cf_adjunction_counit_is_ntcf)
    from assms(1-6) \<epsilon>_\<eta> have dom_lhs:
      "\<D>\<^sub>\<circ> (\<epsilon>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>)\<lparr>NTMap\<rparr>) = \<DD>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)
    from assms(1-6) \<epsilon>_\<eta> have dom_rhs: "\<D>\<^sub>\<circ> (\<epsilon>\<lparr>NTMap\<rparr>) = \<DD>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)
    show "\<epsilon>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>)\<lparr>NTMap\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a assume "a \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
      with aou.is_cf_adjunction_axioms assms(1-6) show 
        "\<epsilon>\<^sub>C (cf_adjunction_of_unit \<alpha> \<FF> \<GG> \<eta>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<epsilon>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by 
          (
            cs_concl
              cs_intro:
                cat_arrow_cs_intros
                cat_op_intros
                cat_cs_intros
                cat_prod_cs_intros
              cs_simp: 
                aou.cf_adj_umap_of_unit'[symmetric]
                cat_Set_the_inverse[symmetric]
                adj_cs_simps cat_cs_simps cat_op_simps
          )
    qed (auto simp: adj_cs_intros)
  qed (auto simp: assms) 

qed

lemma counit_unit_cf_adjunction_of_counit_is_cf_adjunction:
  assumes "category \<alpha> \<CC>"
    and "category \<alpha> \<DD>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<eta> : cf_id \<CC> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<epsilon> : \<FF> \<circ>\<^sub>C\<^sub>F \<GG> \<mapsto>\<^sub>C\<^sub>F cf_id \<DD> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "(\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<epsilon>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<eta> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) = ntcf_id \<GG>"
    and "(\<epsilon> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>) = ntcf_id \<FF>"
  shows "cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<eta>\<^sub>C (cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>) = \<eta>"
    and "\<epsilon>\<^sub>C (cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>) = \<epsilon>"
proof-

  interpret \<CC>: category \<alpha> \<CC> by (rule assms(1))
  interpret \<DD>: category \<alpha> \<DD> by (rule assms(2))
  interpret \<FF>: is_functor \<alpha> \<CC> \<DD> \<FF> by (rule assms(3))
  interpret \<GG>: is_functor \<alpha> \<DD> \<CC> \<GG> by (rule assms(4))
  interpret \<eta>: is_ntcf \<alpha> \<CC> \<CC> \<open>cf_id \<CC>\<close> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> \<eta> by (rule assms(5))
  interpret \<epsilon>: is_ntcf \<alpha> \<DD> \<DD> \<open>\<FF> \<circ>\<^sub>C\<^sub>F \<GG>\<close> \<open>cf_id \<DD>\<close> \<epsilon> by (rule assms(6))

  have unit_op: "cf_adjunction_of_unit \<alpha> (op_cf \<GG>) (op_cf \<FF>) (op_ntcf \<epsilon>) :
    op_cf \<GG> \<rightleftharpoons>\<^sub>C\<^sub>F op_cf \<FF> : op_cat \<DD> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
    by (rule counit_unit_is_cf_adjunction(1)[where \<epsilon>=\<open>op_ntcf \<eta>\<close>])
      (
        cs_concl
          cs_simp:
            cat_op_simps cat_cs_simps 
            \<GG>.cf_ntcf_id_op_cf
            \<FF>.cf_ntcf_id_op_cf
            op_ntcf_ntcf_vcomp[symmetric]
            op_ntcf_ntcf_cf_comp[symmetric]
            op_ntcf_cf_ntcf_comp[symmetric]
            assms(7,8) 
          cs_intro: cat_op_intros cat_cs_intros
      )+
  then show aou: "cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    unfolding cf_adjunction_of_counit_def
    by
      (
        subst \<FF>.cf_op_cf_op_cf[symmetric],
        subst \<GG>.cf_op_cf_op_cf[symmetric],
        subst \<CC>.cat_op_cat_op_cat[symmetric],
        subst \<DD>.cat_op_cat_op_cat[symmetric],
        rule is_cf_adjunction_op
      )

  interpret aou: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG> \<open>cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>\<close>
    by (rule aou)

  show "\<eta>\<^sub>C (cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>) = \<eta>"
    unfolding cf_adjunction_of_counit_def
    by (*slow*)
      (
        cs_concl_step is_cf_adjunction.op_ntcf_cf_adjunction_counit[symmetric], 
        rule unit_op, 
        cs_concl_step counit_unit_is_cf_adjunction(3)[where \<epsilon>=\<open>op_ntcf \<eta>\<close>],
        insert \<CC>.category_op \<DD>.category_op
      )
      (
        cs_concl
          cs_simp:
            cat_op_simps cat_cs_simps 
            \<GG>.cf_ntcf_id_op_cf
            \<FF>.cf_ntcf_id_op_cf
            op_ntcf_ntcf_vcomp[symmetric]
            op_ntcf_ntcf_cf_comp[symmetric]
            op_ntcf_cf_ntcf_comp[symmetric]
            assms(7,8) 
          cs_intro: cat_op_intros cat_cs_intros
      )+ 

  show "\<epsilon>\<^sub>C (cf_adjunction_of_counit \<alpha> \<FF> \<GG> \<epsilon>) = \<epsilon>"
    unfolding cf_adjunction_of_counit_def
    by
      (
        cs_concl_step is_cf_adjunction.op_ntcf_cf_adjunction_unit[symmetric], 
        rule unit_op, 
        cs_concl_step counit_unit_is_cf_adjunction(2)[where \<epsilon>=\<open>op_ntcf \<eta>\<close>],
        insert \<CC>.category_op \<DD>.category_op
      )
      (
        cs_concl
          cs_simp:
            cat_op_simps cat_cs_simps 
            \<GG>.cf_ntcf_id_op_cf
            \<FF>.cf_ntcf_id_op_cf
            op_ntcf_ntcf_vcomp[symmetric]
            op_ntcf_ntcf_cf_comp[symmetric]
            op_ntcf_cf_ntcf_comp[symmetric]
            assms(7,8) 
          cs_intro: cat_op_intros cat_cs_intros
      )+

qed



subsection\<open>Adjoints are unique up to isomorphism\<close>


text\<open>
The content of the following subsection is based predominantly on
the statement and the proof of Corollary 1 in 
Chapter IV-1 in \cite{mac_lane_categories_2010}. However, similar 
results can also be found in section 4 in \cite{riehl_category_2016}
and in subsection 2.1 in \cite{bodo_categories_1970}.
\<close>


subsubsection\<open>Definitions and elementary properties\<close>

definition cf_adj_LR_iso :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi> =
    [
      (
        \<lambda>x\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. THE f'.
        let
          \<eta> = \<eta>\<^sub>C \<Phi>;
          \<eta>' = \<eta>\<^sub>C \<Psi>;
          \<FF>x = \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>;
          \<FF>'x = \<FF>'\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>
        in
          f' : \<FF>x \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'x \<and>
          \<eta>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_of \<GG> x (\<FF>x) (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) (\<FF>'x)\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
      ),
      \<FF>,
      \<FF>',
      \<CC>,
      \<DD>
    ]\<^sub>\<circ>"

definition cf_adj_RL_iso :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi> =
    [
      (
        \<lambda>x\<in>\<^sub>\<circ>\<DD>\<lparr>Obj\<rparr>. THE f'.
        let
          \<epsilon> = \<epsilon>\<^sub>C \<Phi>;
          \<epsilon>' = \<epsilon>\<^sub>C \<Psi>;
          \<GG>x = \<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>;
          \<GG>'x = \<GG>'\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>
        in
          f' : \<GG>'x \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>x \<and>
          \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_fo \<FF> x \<GG>x (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<GG>'x\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
      ),
      \<GG>',
      \<GG>,
      \<DD>,
      \<CC>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_adj_LR_iso_components:
  shows "cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>\<lparr>NTMap\<rparr> =
    (
      \<lambda>x\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. THE f'.
      let
        \<eta> = \<eta>\<^sub>C \<Phi>;
        \<eta>' = \<eta>\<^sub>C \<Psi>;
        \<FF>x = \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>;
        \<FF>'x = \<FF>'\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>
      in
        f' : \<FF>x \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'x \<and>
        \<eta>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_of \<GG> x \<FF>x (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<FF>'x\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
    )"
    and [adj_cs_simps]: "cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>\<lparr>NTDom\<rparr> = \<FF>"
    and [adj_cs_simps]: "cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>\<lparr>NTCod\<rparr> = \<FF>'"
    and [adj_cs_simps]: "cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>\<lparr>NTDGDom\<rparr> = \<CC>"
    and [adj_cs_simps]: "cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>\<lparr>NTDGCod\<rparr> = \<DD>"
  unfolding cf_adj_LR_iso_def nt_field_simps
  by (simp_all add: nat_omega_simps) (*slow*)

lemma cf_adj_RL_iso_components:
  shows "cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>\<lparr>NTMap\<rparr> =
    (
        \<lambda>x\<in>\<^sub>\<circ>\<DD>\<lparr>Obj\<rparr>. THE f'.
        let
          \<epsilon> = \<epsilon>\<^sub>C \<Phi>;
          \<epsilon>' = \<epsilon>\<^sub>C \<Psi>;
          \<GG>x = \<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>;
          \<GG>'x = \<GG>'\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>
        in
          f' : \<GG>'x \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>x \<and>
          \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_fo \<FF> x \<GG>x (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<GG>'x\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
    )"
    and [adj_cs_simps]: "cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>\<lparr>NTDom\<rparr> = \<GG>'"
    and [adj_cs_simps]: "cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>\<lparr>NTCod\<rparr> = \<GG>"
    and [adj_cs_simps]: "cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>\<lparr>NTDGDom\<rparr> = \<DD>"
    and [adj_cs_simps]: "cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding cf_adj_RL_iso_def nt_field_simps
  by (simp_all add: nat_omega_simps) (*slow*)


subsubsection\<open>Natural transformation map\<close>

lemma cf_adj_LR_iso_vsv[adj_cs_intros]: 
  "vsv (cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>\<lparr>NTMap\<rparr>)"
  unfolding cf_adj_LR_iso_components by simp

lemma cf_adj_RL_iso_vsv[adj_cs_intros]: 
  "vsv (cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>\<lparr>NTMap\<rparr>)"
  unfolding cf_adj_RL_iso_components by simp

lemma cf_adj_LR_iso_vdomain[adj_cs_simps]:
  "\<D>\<^sub>\<circ> (cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
  unfolding cf_adj_LR_iso_components by simp

lemma cf_adj_RL_iso_vdomain[adj_cs_simps]:
  "\<D>\<^sub>\<circ> (cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>\<lparr>NTMap\<rparr>) = \<DD>\<lparr>Obj\<rparr>"
  unfolding cf_adj_RL_iso_components by simp

lemma cf_adj_LR_iso_app:
  fixes \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>
  assumes "x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  defines "\<FF>x \<equiv> \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>"
    and "\<FF>'x \<equiv> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>"
    and "\<eta> \<equiv> \<eta>\<^sub>C \<Phi>" 
    and "\<eta>' \<equiv> \<eta>\<^sub>C \<Psi>"
  shows "cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr> =
    (
      THE f'.
        f' : \<FF>x \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'x \<and>
        \<eta>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_of \<GG> x \<FF>x (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<FF>'x\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
    )"
  using assms(1) unfolding cf_adj_LR_iso_components assms(2-5) by simp meson

lemma cf_adj_RL_iso_app:
  fixes \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>
  assumes "x \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
  defines "\<GG>x \<equiv> \<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>"
    and "\<GG>'x \<equiv> \<GG>'\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>"
    and "\<epsilon> \<equiv> \<epsilon>\<^sub>C \<Phi>" 
    and "\<epsilon>' \<equiv> \<epsilon>\<^sub>C \<Psi>"
  shows "cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr> =
    (
      THE f'.
        f' : \<GG>'x \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>x \<and>
        \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_fo \<FF> x \<GG>x (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<GG>'x\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>
    )"
  using assms(1) unfolding cf_adj_RL_iso_components assms(2-5) Let_def by simp

lemma cf_adj_LR_iso_app_unique:
  fixes \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>
  assumes "\<Phi> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    and "\<Psi> : \<FF>' \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    and "x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  defines "\<FF>x \<equiv> \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>"
    and "\<FF>'x \<equiv> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>"
    and "\<eta> \<equiv> \<eta>\<^sub>C \<Phi>" 
    and "\<eta>' \<equiv> \<eta>\<^sub>C \<Psi>"
    and "f \<equiv> cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>"
  shows
    "\<exists>!f'.
      f' : \<FF>x \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'x \<and>
      \<eta>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_of \<GG> x \<FF>x (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<FF>'x\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    "f : \<FF>x \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<DD>\<^esub> \<FF>'x"
    "\<eta>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_of \<GG> x \<FF>x (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<FF>'x\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
proof-
  interpret \<Phi>: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG> \<Phi> by (rule assms(1))
  interpret \<Psi>: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF>' \<GG> \<Psi> by (rule assms(2))
  note \<FF>a_\<eta> =
    is_cf_adjunction.cf_adjunction_unit_component_is_ua_of[
      OF assms(1) assms(3), folded assms(4-8)
      ]
  note \<FF>'a_\<eta> = 
    is_cf_adjunction.cf_adjunction_unit_component_is_ua_of[
      OF assms(2) assms(3), folded assms(4-8)
      ]
  from 
    is_functor.cf_universal_arrow_of_unique[
      OF \<Phi>.RL.is_functor_axioms \<FF>a_\<eta> \<FF>'a_\<eta>, folded assms(4-8)
      ]
  obtain f' 
    where f': "f' : \<FF>x \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'x"
      and \<eta>'_def: 
        "\<eta>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_of \<GG> x \<FF>x (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<FF>'x\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
      and unique_f': 
        "\<lbrakk>
          f'' : \<FF>x \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'x;
          \<eta>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_of \<GG> x \<FF>x (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<FF>'x\<lparr>ArrVal\<rparr>\<lparr>f''\<rparr>
        \<rbrakk> \<Longrightarrow> f'' = f'"
    for f''
    by metis
  show unique_f': "\<exists>!f'.
    f' : \<FF>x \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'x \<and>
    \<eta>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_of \<GG> x \<FF>x (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<FF>'x\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    by 
      (
        rule is_functor.cf_universal_arrow_of_unique[
          OF \<Phi>.RL.is_functor_axioms \<FF>a_\<eta> \<FF>'a_\<eta>, folded assms(4-8)
          ]
      )
  from
    theD
      [
        OF unique_f' cf_adj_LR_iso_app[
          OF assms(3), of \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>, folded assms(4-8)
          ]
      ]
  have f: "f : \<FF>x \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'x"
    and \<eta>': "\<eta>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_of \<GG> x \<FF>x (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<FF>'x\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
    by simp_all
  show "\<eta>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_of \<GG> x \<FF>x (\<eta>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<FF>'x\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>" by (rule \<eta>')
  show "f : \<FF>x \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<DD>\<^esub> \<FF>'x"
    by
      (
        rule 
          is_functor.cf_universal_arrow_of_is_arr_isomorphism[
            OF \<Phi>.RL.is_functor_axioms \<FF>a_\<eta> \<FF>'a_\<eta> f \<eta>'
            ]
      )
qed


subsubsection\<open>Main results\<close>

lemma cf_adj_LR_iso_is_iso_functor:
  \<comment>\<open>See Corollary 1 in Chapter IV-1 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<Phi> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "\<Psi> : \<FF>' \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
  shows "\<exists>!\<theta>.
    \<theta> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD> \<and>
    \<eta>\<^sub>C \<Psi> = (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<theta>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>\<^sub>C \<Phi>"
    and "cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<eta>\<^sub>C \<Psi> =
      (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>\<^sub>C \<Phi>"
proof-

  interpret \<Phi>: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG> \<Phi> by (rule assms(1))
  interpret \<Psi>: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF>' \<GG> \<Psi> by (rule assms(2))

  let ?\<eta> = \<open>\<eta>\<^sub>C \<Phi>\<close>
  let ?\<eta>' = \<open>\<eta>\<^sub>C \<Psi>\<close>
  let ?\<Phi>\<Psi> = \<open>cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>\<close>

  show \<FF>'\<Psi>: "?\<Phi>\<Psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  proof(intro is_iso_ntcfI is_ntcfI')

    show "vfsequence ?\<Phi>\<Psi>" unfolding cf_adj_LR_iso_def by auto
    show "vcard ?\<Phi>\<Psi> = 5\<^sub>\<nat>" 
      unfolding cf_adj_LR_iso_def by (simp add: nat_omega_simps)
    show "?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for a
      using cf_adj_LR_iso_app_unique(2)[OF assms that] by auto

    show "?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> ?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for a b f
    proof-

      from that have a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
      note unique_a = cf_adj_LR_iso_app_unique[OF assms a]
      note unique_b = cf_adj_LR_iso_app_unique[OF assms b]

      from unique_a(2) have a_is_arr:
        "?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by auto
      from unique_b(2) have b_is_arr:
        "?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by auto

      interpret \<eta>: is_ntcf \<alpha> \<CC> \<CC> \<open>cf_id \<CC>\<close> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> ?\<eta>
        by (rule \<Phi>.cf_adjunction_unit_is_ntcf)
      interpret \<eta>': is_ntcf \<alpha> \<CC> \<CC> \<open>cf_id \<CC>\<close> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>'\<close> ?\<eta>'
        by (rule \<Psi>.cf_adjunction_unit_is_ntcf)

      from unique_a(3) a_is_arr a b have \<eta>'_a_def: 
        "?\<eta>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by (cs_prems cs_simp: cat_cs_simps cs_intro: adj_cs_intros cat_cs_intros)
      from unique_b(3) b_is_arr a b have \<eta>'_b_def:
        "?\<eta>'\<lparr>NTMap\<rparr>\<lparr>b\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
        by (cs_prems cs_simp: cat_cs_simps cs_intro: adj_cs_intros cat_cs_intros)
      
      from that a b a_is_arr have 
        "\<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> 
          (\<GG>\<lparr>ArrMap\<rparr>\<lparr>?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) = 
          \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<eta>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps \<eta>'_a_def cs_intro: cat_cs_intros)
      also from \<eta>'.ntcf_Comp_commute[OF that, symmetric] that a b have 
        "\<dots> = ?\<eta>'\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
        by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      also from that a b b_is_arr have
        "\<dots> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
          (?\<eta>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)" 
        by (cs_concl cs_simp: cat_cs_simps \<eta>'_b_def cs_intro: cat_cs_intros)
      also from that have 
        "\<dots> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
          ((\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
        unfolding \<eta>.ntcf_Comp_commute[OF that, symmetric]
        by (cs_concl cs_simp: cat_cs_simps \<eta>'_b_def cs_intro: cat_cs_intros)
      also from that b_is_arr have 
        "\<dots> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
          (\<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      finally have [cat_cs_simps]:
        "\<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<GG>\<lparr>ArrMap\<rparr>\<lparr>?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> 
          ?\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) =
          \<GG>\<lparr>ArrMap\<rparr>\<lparr>?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
            (\<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
        by simp

      note unique_f_a = is_functor.universal_arrow_ofD
        [
          OF 
            \<Phi>.RL.is_functor_axioms 
            \<Phi>.cf_adjunction_unit_component_is_ua_of[OF a]
        ]

      from that a b a_is_arr b_is_arr have \<GG>\<FF>f_\<eta>a:
        "\<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>  \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<eta>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> :
          a \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

      from b have \<FF>'b: "\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

      from unique_f_a(3)[OF \<FF>'b \<GG>\<FF>f_\<eta>a] obtain f' 
        where f': "f' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
          and \<eta>a: "\<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<eta>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
          umap_of \<GG> a (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (?\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
          and unique_f':
            "\<lbrakk>
              f'' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>;
              \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<eta>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
                umap_of \<GG> a (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (?\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<lparr>ArrVal\<rparr>\<lparr>f''\<rparr>
             \<rbrakk> \<Longrightarrow> f'' = f'"
        for f''
        by metis
      have "?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = f'"
        by (rule unique_f', insert a b a_is_arr b_is_arr that)
          (cs_concl cs_simp: \<eta>'_a_def cat_cs_simps cs_intro: cat_cs_intros)
      moreover have "\<FF>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> ?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = f'"
        by (rule unique_f', insert a b a_is_arr b_is_arr that)
          (cs_concl cs_simp: \<eta>'_a_def cat_cs_simps cs_intro: cat_cs_intros)
      ultimately show ?thesis by simp
    qed 

  qed 
    (
      auto 
        intro: cat_cs_intros adj_cs_intros  
        simp: adj_cs_simps cf_adj_LR_iso_app_unique(2)[OF assms]
    )

  interpret \<FF>'\<Psi>: is_iso_ntcf \<alpha> \<CC> \<DD> \<FF> \<FF>' \<open>?\<Phi>\<Psi>\<close> by (rule \<FF>'\<Psi>)

  show \<eta>'_def: "?\<eta>' = \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<Phi>\<Psi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>\<^sub>C \<Phi>"
  proof(rule ntcf_eqI)
    have dom_lhs: "\<D>\<^sub>\<circ> (?\<eta>'\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: adj_cs_intros)
    have dom_rhs: "\<D>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<Phi>\<Psi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>\<^sub>C \<Phi>)\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: adj_cs_intros cat_cs_intros)
    show "?\<eta>'\<lparr>NTMap\<rparr> = (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<Phi>\<Psi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>\<^sub>C \<Phi>)\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a assume prems: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
      note unique_a = cf_adj_LR_iso_app_unique[OF assms prems]
      from unique_a(2) have a_is_arr:
        "?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by auto  
      interpret \<eta>: is_ntcf \<alpha> \<CC> \<CC> \<open>cf_id \<CC>\<close> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> ?\<eta>
        by (rule \<Phi>.cf_adjunction_unit_is_ntcf)
      from unique_a(3) a_is_arr prems have \<eta>'_a_def: 
        "?\<eta>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by (cs_prems cs_simp: cat_cs_simps cs_intro: adj_cs_intros cat_cs_intros)
      from prems a_is_arr show 
        "?\<eta>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =  (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<Phi>\<Psi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<eta>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by (cs_concl cs_simp: \<eta>'_a_def cat_cs_simps cs_intro: cat_cs_intros)
    qed (auto intro: cat_cs_intros adj_cs_intros)
  qed (cs_concl cs_simp: cat_cs_simps cs_intro: adj_cs_intros cat_cs_intros)+

  show "\<exists>!\<theta>. \<theta> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD> \<and> ?\<eta>' = (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<theta>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<eta>"
  proof(intro ex1I conjI; (elim conjE)?)
    from \<FF>'\<Psi> show "?\<Phi>\<Psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" by auto
    show "?\<eta>' = \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<Phi>\<Psi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>\<^sub>C \<Phi>" by (rule \<eta>'_def)
    fix \<theta> assume prems:
      "\<theta> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
      "?\<eta>' = \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<theta> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>\<^sub>C \<Phi>"
    interpret \<theta>: is_ntcf \<alpha> \<CC> \<DD> \<FF> \<FF>' \<theta> by (rule prems(1))
    from prems have \<eta>'_a: 
      "?\<eta>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<theta> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<eta>\<^sub>C \<Phi>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>" 
      for a
      by simp
    have \<eta>'a: "\<eta>\<^sub>C \<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
      \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<theta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for a
      using \<eta>'_a[where a=a] that
      by (cs_prems cs_simp: cat_cs_simps cs_intro: adj_cs_intros cat_cs_intros)
    show "\<theta> = ?\<Phi>\<Psi>"
    proof(rule ntcf_eqI)
      have dom_lhs: "\<D>\<^sub>\<circ> (\<theta>\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>" by (cs_concl cs_simp: cat_cs_simps)
      have dom_rhs: "\<D>\<^sub>\<circ> (?\<Phi>\<Psi>\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps)
      show "\<theta>\<lparr>NTMap\<rparr> = ?\<Phi>\<Psi>\<lparr>NTMap\<rparr>"
      proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
        fix a assume prems': "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        let ?uof = \<open>umap_of \<GG> a (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (?\<eta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)\<close>
        from cf_adj_LR_iso_app_unique[OF assms prems'] obtain f' 
          where f': "f' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
            and \<eta>_def: "?\<eta>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = ?uof\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
            and unique_f': "\<And>f''.
              \<lbrakk>
                f'' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>;
                ?\<eta>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = ?uof\<lparr>ArrVal\<rparr>\<lparr>f''\<rparr>
              \<rbrakk> \<Longrightarrow> f'' = f'"
          by metis
        from prems' have \<theta>a: "\<theta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
          by (cs_concl cs_simp: cs_intro: cat_cs_intros)
        from \<eta>_def f' prems' have 
          "\<eta>\<^sub>C \<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<eta>\<^sub>C \<Phi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
          by 
            (
              cs_prems 
                cs_simp: cat_cs_simps cs_intro: adj_cs_intros cat_cs_intros
            )
        from prems' have "\<eta>\<^sub>C \<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = ?uof\<lparr>ArrVal\<rparr>\<lparr>\<theta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr>"
          by 
            (
              cs_concl 
                cs_simp: cat_cs_simps \<eta>'a[OF prems'] 
                cs_intro: adj_cs_intros cat_cs_intros
            )
        from unique_f'[OF \<theta>a this] have \<theta>a: "\<theta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = f'".
        from prems' have \<Psi>a: 
          "?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        from prems' have "\<eta>\<^sub>C \<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = ?uof\<lparr>ArrVal\<rparr>\<lparr>?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr>"
          by 
            ( 
              cs_concl 
                cs_simp: cf_adj_LR_iso_app_unique(3)[OF assms] cat_cs_simps 
                cs_intro: adj_cs_intros cat_cs_intros
            )
        from unique_f'[OF \<Psi>a this] have \<FF>'\<Psi>_def: "?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = f'".
        show "\<theta>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = ?\<Phi>\<Psi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>" unfolding \<theta>a \<FF>'\<Psi>_def ..
      qed auto
    qed (cs_concl cs_simp: cs_intro: cat_cs_intros)+
  qed

qed

lemma op_ntcf_cf_adj_RL_iso[cat_op_simps]:
  assumes "\<Phi> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    and "\<Psi> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG>' : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
  defines "op_\<DD> \<equiv> op_cat \<DD>"
    and "op_\<CC> \<equiv> op_cat \<CC>"
    and "op_\<FF> \<equiv> op_cf \<FF>"
    and "op_\<GG> \<equiv> op_cf \<GG>"
    and "op_\<Phi> \<equiv> op_cf_adj \<Phi>"
    and "op_\<GG>' \<equiv> op_cf \<GG>'"
    and "op_\<Psi> \<equiv> op_cf_adj \<Psi>"
  shows
    "op_ntcf (cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>) =
      cf_adj_LR_iso op_\<DD> op_\<CC> op_\<FF> op_\<GG> op_\<Phi> op_\<GG>' op_\<Psi>"
proof-
  interpret \<Phi>: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG> \<Phi> by (rule assms(1))
  interpret \<Psi>: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG>' \<Psi> by (rule assms(2))
  interpret \<epsilon>: is_ntcf \<alpha> \<DD> \<DD> \<open>\<FF> \<circ>\<^sub>C\<^sub>F \<GG>\<close> \<open>cf_id \<DD>\<close> \<open>\<epsilon>\<^sub>C \<Phi>\<close>
    by (rule \<Phi>.cf_adjunction_counit_is_ntcf)
  have dom_lhs: "\<D>\<^sub>\<circ> (op_ntcf (cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>)) = 5\<^sub>\<nat>"
    unfolding op_ntcf_def by (simp add: nat_omega_simps)
  show ?thesis
  proof(rule vsv_eqI, unfold dom_lhs)
    fix a assume prems: "a \<in>\<^sub>\<circ> 5\<^sub>\<nat>"
    then have "a \<in>\<^sub>\<circ> 5\<^sub>\<nat>" unfolding dom_lhs by simp
    then show 
      "op_ntcf (cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>)\<lparr>a\<rparr> =
        cf_adj_LR_iso op_\<DD> op_\<CC> op_\<FF> op_\<GG> op_\<Phi> op_\<GG>' op_\<Psi>\<lparr>a\<rparr>"
      by 
        (
          elim_in_numeral, 
          fold nt_field_simps, 
          unfold 
            cf_adj_LR_iso_components 
            op_ntcf_components 
            cf_adj_RL_iso_components
            Let_def
            \<Phi>.cf_adjunction_unit_NTMap_op 
            \<Psi>.cf_adjunction_unit_NTMap_op
            assms(3-9)
            cat_op_simps
        )
        simp_all
  qed (auto simp: op_ntcf_def cf_adj_LR_iso_def nat_omega_simps)
qed

lemma op_ntcf_cf_adj_LR_iso[cat_op_simps]:
  assumes "\<Phi> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "\<Psi> : \<FF>' \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
  defines "op_\<DD> \<equiv> op_cat \<DD>"
    and "op_\<CC> \<equiv> op_cat \<CC>"
    and "op_\<FF> \<equiv> op_cf \<FF>"
    and "op_\<GG> \<equiv> op_cf \<GG>"
    and "op_\<Phi> \<equiv> op_cf_adj \<Phi>"
    and "op_\<FF>' \<equiv> op_cf \<FF>'"
    and "op_\<Psi> \<equiv> op_cf_adj \<Psi>"
  shows
    "op_ntcf (cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>) =
      cf_adj_RL_iso op_\<DD> op_\<CC> op_\<GG> op_\<FF> op_\<Phi> op_\<FF>' op_\<Psi>"
proof-
  interpret \<Phi>: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG> \<Phi> by (rule assms(1))
  interpret \<Psi>: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF>' \<GG> \<Psi> by (rule assms(2))
  interpret \<epsilon>: is_ntcf \<alpha> \<DD> \<DD> \<open>\<FF> \<circ>\<^sub>C\<^sub>F \<GG>\<close> \<open>cf_id \<DD>\<close> \<open>\<epsilon>\<^sub>C \<Phi>\<close>
    by (rule \<Phi>.cf_adjunction_counit_is_ntcf)
  have dom_lhs: "\<D>\<^sub>\<circ> (op_ntcf (cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>)) = 5\<^sub>\<nat>"
    unfolding op_ntcf_def by (simp add: nat_omega_simps)
  show ?thesis
  proof(rule vsv_eqI, unfold dom_lhs)
    fix a assume prems: "a \<in>\<^sub>\<circ> 5\<^sub>\<nat>"
    then show
      "op_ntcf (cf_adj_LR_iso \<CC> \<DD> \<GG> \<FF> \<Phi> \<FF>' \<Psi>)\<lparr>a\<rparr> =
        cf_adj_RL_iso op_\<DD> op_\<CC> op_\<GG> op_\<FF> op_\<Phi> op_\<FF>' op_\<Psi>\<lparr>a\<rparr>"
      by
        (
          elim_in_numeral, 
          use nothing in 
            \<open>
              fold nt_field_simps,
              unfold 
                cf_adj_LR_iso_components
                op_ntcf_components
                cf_adj_RL_iso_components
                Let_def
                \<Phi>.op_ntcf_cf_adjunction_unit[symmetric]
                \<Psi>.op_ntcf_cf_adjunction_unit[symmetric]
                assms(3-9)
                cat_op_simps
            \<close>
        )
        simp_all
  qed (auto simp: op_ntcf_def cf_adj_RL_iso_def nat_omega_simps)
qed

lemma cf_adj_RL_iso_app_unique:
  fixes \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>
  assumes "\<Phi> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    and "\<Psi> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG>' : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    and "x \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
  defines "\<GG>x \<equiv> \<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>"
    and "\<GG>'x \<equiv> \<GG>'\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>"
    and "\<epsilon> \<equiv> \<epsilon>\<^sub>C \<Phi>" 
    and "\<epsilon>' \<equiv> \<epsilon>\<^sub>C \<Psi>"
    and "f \<equiv> cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>"
  shows
    "\<exists>!f'.
      f' : \<GG>'x \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>x \<and>
      \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_fo \<FF> x \<GG>x (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<GG>'x\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    "f : \<GG>'x \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> \<GG>x"
    "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_fo \<FF> x \<GG>x (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<GG>'x\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
proof-
  interpret \<Phi>: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG> \<Phi> by (rule assms(1))
  interpret \<Psi>: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG>' \<Psi> by (rule assms(2))
  interpret \<epsilon>: is_ntcf \<alpha> \<DD> \<DD> \<open>\<FF> \<circ>\<^sub>C\<^sub>F \<GG>\<close> \<open>cf_id \<DD>\<close> \<open>\<epsilon>\<^sub>C \<Phi>\<close>
    by (rule \<Phi>.cf_adjunction_counit_is_ntcf)
  show
    "\<exists>!f'.
      f' : \<GG>'x \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>x \<and>
      \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_fo \<FF> x \<GG>x (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<GG>'x\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    "f : \<GG>'x \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> \<GG>x"
    "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>x\<rparr> = umap_fo \<FF> x \<GG>x (\<epsilon>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>) \<GG>'x\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
    by 
      (
        intro cf_adj_LR_iso_app_unique
          [
            OF \<Phi>.is_cf_adjunction_op \<Psi>.is_cf_adjunction_op,
            unfolded cat_op_simps,
            OF assms(3),
            unfolded \<Psi>.cf_adjunction_unit_NTMap_op,
            folded \<Phi>.op_ntcf_cf_adjunction_counit,
            folded op_ntcf_cf_adj_RL_iso[OF assms(1,2)],
            unfolded cat_op_simps,
            folded assms(4-8)
          ]
      )+
qed

lemma cf_adj_RL_iso_is_iso_functor:
  \<comment>\<open>See Corollary 1 in Chapter IV-1 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<Phi> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG> : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "\<Psi> : \<FF> \<rightleftharpoons>\<^sub>C\<^sub>F \<GG>' : \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
  shows "\<exists>!\<theta>.
    \<theta> : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<and>
    \<epsilon>\<^sub>C \<Psi> = \<epsilon>\<^sub>C \<Phi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<theta>)"
    and "cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi> : \<GG>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<epsilon>\<^sub>C \<Psi> =
      \<epsilon>\<^sub>C \<Phi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>)"
proof-
  interpret \<Phi>: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG> \<Phi> by (rule assms(1))
  interpret \<Psi>: is_cf_adjunction \<alpha> \<CC> \<DD> \<FF> \<GG>' \<Psi> by (rule assms(2))
  interpret \<epsilon>: is_ntcf \<alpha> \<DD> \<DD> \<open>\<FF> \<circ>\<^sub>C\<^sub>F \<GG>\<close> \<open>cf_id \<DD>\<close> \<open>\<epsilon>\<^sub>C \<Phi>\<close>
    by (rule \<Phi>.cf_adjunction_counit_is_ntcf)
  note cf_adj_LR_iso_is_iso_functor_op = cf_adj_LR_iso_is_iso_functor
    [
      OF \<Phi>.is_cf_adjunction_op \<Psi>.is_cf_adjunction_op,
      folded 
        \<Phi>.op_ntcf_cf_adjunction_counit 
        \<Psi>.op_ntcf_cf_adjunction_counit
        op_ntcf_cf_adj_RL_iso[OF assms]
    ]
  from cf_adj_LR_iso_is_iso_functor_op(1) obtain \<theta> 
    where \<theta>: "\<theta> : op_cf \<GG> \<mapsto>\<^sub>C\<^sub>F op_cf \<GG>' : op_cat \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
      and op_ntcf_\<epsilon>_def: "op_ntcf (\<epsilon>\<^sub>C \<Psi>) =
        op_cf \<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<theta> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf (\<epsilon>\<^sub>C \<Phi>)"
      and unique_\<theta>': 
        "\<lbrakk>
          \<theta>' : op_cf \<GG> \<mapsto>\<^sub>C\<^sub>F op_cf \<GG>' : op_cat \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>;
          op_ntcf (\<epsilon>\<^sub>C \<Psi>) = op_cf \<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<theta>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf (\<epsilon>\<^sub>C \<Phi>)
         \<rbrakk> \<Longrightarrow> \<theta>' = \<theta>"
      for \<theta>'
    by metis
  interpret \<theta>: is_ntcf \<alpha> \<open>op_cat \<DD>\<close> \<open>op_cat \<CC>\<close> \<open>op_cf \<GG>\<close> \<open>op_cf \<GG>'\<close> \<theta> 
    by (rule \<theta>)
  show "\<exists>!\<theta>. \<theta> : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<and> \<epsilon>\<^sub>C \<Psi> = \<epsilon>\<^sub>C \<Phi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<theta>)"
  proof(intro ex1I conjI; (elim conjE)?)
    show op_\<theta>: "op_ntcf \<theta> : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (rule \<theta>.is_ntcf_op[unfolded cat_op_simps])
    from op_ntcf_\<epsilon>_def have
      "op_ntcf (op_ntcf (\<epsilon>\<^sub>C \<Psi>)) =
        op_ntcf (op_cf \<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<theta> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf (\<epsilon>\<^sub>C \<Phi>))"
      by simp
    then show \<epsilon>_def: "\<epsilon>\<^sub>C \<Psi> = \<epsilon>\<^sub>C \<Phi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf \<theta>)"
      by 
        (
          cs_prems 
            cs_simp: cat_op_simps 
            cs_intro: adj_cs_intros cat_cs_intros cat_op_intros
        )
    fix \<theta>' assume prems: 
      "\<theta>' : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      "\<epsilon>\<^sub>C \<Psi> = \<epsilon>\<^sub>C \<Phi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<theta>')"
    interpret \<theta>': is_ntcf \<alpha> \<DD> \<CC> \<GG>' \<GG> \<theta>' by (rule prems(1))   
    have "op_ntcf (\<epsilon>\<^sub>C \<Psi>) = op_cf \<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf \<theta>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf (\<epsilon>\<^sub>C \<Phi>)"
      by 
        (
          cs_concl 
            cs_simp: 
              prems(2) 
              op_ntcf_cf_ntcf_comp[symmetric] 
              op_ntcf_ntcf_vcomp[symmetric] 
            cs_intro: cat_cs_intros
        )
    from unique_\<theta>'[OF \<theta>'.is_ntcf_op this, symmetric] have
      "op_ntcf \<theta> = op_ntcf (op_ntcf \<theta>')"
      by simp
    then show "\<theta>' = op_ntcf \<theta>"  
      by (cs_prems cs_simp: cat_cs_simps cat_op_simps) simp
  qed
  from is_iso_ntcf.is_iso_ntcf_op[OF cf_adj_LR_iso_is_iso_functor_op(2)] show 
    "cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi> : \<GG>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_prems cs_simp: cat_op_simps cs_intro: adj_cs_intros cat_op_intros)
  from cf_adj_LR_iso_is_iso_functor_op(3) have 
    "op_ntcf (op_ntcf (\<epsilon>\<^sub>C \<Psi>)) =
      op_ntcf
        (
          op_cf \<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf (cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F 
          op_ntcf (\<epsilon>\<^sub>C \<Phi>)
        )"
    by simp
  from 
    this 
    cf_adj_LR_iso_is_iso_functor_op(2)[ 
      unfolded op_ntcf_cf_adj_RL_iso[OF assms]
      ]
  show "\<epsilon>\<^sub>C \<Psi> = \<epsilon>\<^sub>C \<Phi> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F cf_adj_RL_iso \<CC> \<DD> \<FF> \<GG> \<Phi> \<GG>' \<Psi>)"
    by 
      (
        cs_prems
          cs_simp: cat_op_simps cat_op_simps 
          cs_intro: ntcf_cs_intros adj_cs_intros cat_cs_intros cat_op_intros
      )
qed



subsection\<open>Further properties of the adjoint functors\<close>

lemma (in is_cf_adjunction) cf_adj_exp_cf_cat:
  \<comment>\<open>See Proposition 4.4.6 in \cite{riehl_category_2016}.\<close>
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "category \<alpha> \<JJ>"
  shows
    "cf_adjunction_of_unit
      \<beta>
      (exp_cf_cat \<alpha> \<FF> \<JJ>)
      (exp_cf_cat \<alpha> \<GG> \<JJ>)
      (exp_ntcf_cat \<alpha> (\<eta>\<^sub>C \<Phi>) \<JJ>) :
      exp_cf_cat \<alpha> \<FF> \<JJ> \<rightleftharpoons>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<GG> \<JJ> :
      cat_FUNCT \<alpha> \<JJ> \<CC> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<JJ> \<DD>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<JJ>: category \<alpha> \<JJ> by (rule assms(3))
  show ?thesis
  proof
    (
      rule counit_unit_is_cf_adjunction(1)[
        where \<epsilon> = \<open>exp_ntcf_cat \<alpha> (\<epsilon>\<^sub>C \<Phi>) \<JJ>\<close>
        ]
    )
    from assms show "exp_ntcf_cat \<alpha> (\<eta>\<^sub>C \<Phi>) \<JJ> :
      cf_id (cat_FUNCT \<alpha> \<JJ> \<CC>) \<mapsto>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<GG> \<JJ> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<JJ> :
      cat_FUNCT \<alpha> \<JJ> \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<JJ> \<CC>"
      by 
        (
          cs_concl
            cs_simp:
              cat_cs_simps cat_FUNCT_cs_simps 
              exp_cf_cat_cf_id_cat[symmetric] exp_cf_cat_cf_comp[symmetric] 
            cs_intro:
              cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros adj_cs_intros
        )
    from assms show 
      "exp_ntcf_cat \<alpha> (\<epsilon>\<^sub>C \<Phi>) \<JJ> :
        exp_cf_cat \<alpha> \<FF> \<JJ> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<GG> \<JJ> \<mapsto>\<^sub>C\<^sub>F cf_id (cat_FUNCT \<alpha> \<JJ> \<DD>) :
        cat_FUNCT \<alpha> \<JJ> \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<JJ> \<DD>"
      by
        (
          cs_concl
            cs_simp:
              cat_cs_simps 
              cat_FUNCT_cs_simps 
              exp_cf_cat_cf_id_cat[symmetric] 
              exp_cf_cat_cf_comp[symmetric] 
            cs_intro:
              cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros adj_cs_intros
        )
    note [symmetric, cat_cs_simps] =
      ntcf_id_exp_cf_cat 
      exp_ntcf_cat_ntcf_vcomp 
      exp_ntcf_cat_ntcf_cf_comp
      exp_ntcf_cat_cf_ntcf_comp
    from assms show
      "(exp_cf_cat \<alpha> \<GG> \<JJ> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_ntcf_cat \<alpha> (\<epsilon>\<^sub>C \<Phi>) \<JJ>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
        (exp_ntcf_cat \<alpha> (\<eta>\<^sub>C \<Phi>) \<JJ> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<GG> \<JJ>) =
        ntcf_id (exp_cf_cat \<alpha> \<GG> \<JJ>)"
      by 
        (
          cs_concl 
            cs_simp: adj_cs_simps cat_cs_simps  
            cs_intro: adj_cs_intros cat_cs_intros
        )
    from assms show
      "exp_ntcf_cat \<alpha> (\<epsilon>\<^sub>C \<Phi>) \<JJ> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<JJ> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
      (exp_cf_cat \<alpha> \<FF> \<JJ> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_ntcf_cat \<alpha> (\<eta>\<^sub>C \<Phi>) \<JJ>) =
      ntcf_id (exp_cf_cat \<alpha> \<FF> \<JJ>)"
      by 
        (
          cs_concl 
            cs_simp: adj_cs_simps cat_cs_simps  
            cs_intro: adj_cs_intros cat_cs_intros
        )
  qed
    (
      use assms in 
        \<open>
          cs_concl
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        \<close>
    )+
qed

lemma (in is_cf_adjunction) cf_adj_exp_cf_cat_exp_cf_cat:
  \<comment>\<open>See Proposition 4.4.6 in \cite{riehl_category_2016}.\<close>
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "category \<alpha> \<AA>"
  shows
    "cf_adjunction_of_unit
      \<beta>
      (exp_cat_cf \<alpha> \<AA> \<GG>)
      (exp_cat_cf \<alpha> \<AA> \<FF>)
      (exp_cat_ntcf \<alpha> \<AA> (\<eta>\<^sub>C \<Phi>)) :
      exp_cat_cf \<alpha> \<AA> \<GG> \<rightleftharpoons>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<FF> :
      cat_FUNCT \<alpha> \<CC> \<AA> \<rightleftharpoons>\<rightleftharpoons>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<DD> \<AA>"
proof-

  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(3))

  show ?thesis
  proof
    (
      rule counit_unit_is_cf_adjunction(1)[
        where \<epsilon> = \<open>exp_cat_ntcf \<alpha> \<AA> (\<epsilon>\<^sub>C \<Phi>)\<close>
        ]
    )
    from assms is_cf_adjunction_axioms show
      "exp_cat_ntcf \<alpha> \<AA> (\<eta>\<^sub>C \<Phi>) :
        cf_id (cat_FUNCT \<alpha> \<CC> \<AA>) \<mapsto>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<FF> \<circ>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<GG> :
        cat_FUNCT \<alpha> \<CC> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<CC> \<AA>"
      by 
        (
          cs_concl
            cs_simp:
              exp_cat_cf_cat_cf_id[symmetric] exp_cat_cf_cf_comp[symmetric] 
            cs_intro: cat_small_cs_intros cat_FUNCT_cs_intros adj_cs_intros
        )
    from assms is_cf_adjunction_axioms show 
      "exp_cat_ntcf \<alpha> \<AA> (\<epsilon>\<^sub>C \<Phi>) :
        exp_cat_cf \<alpha> \<AA> \<GG> \<circ>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<FF> \<mapsto>\<^sub>C\<^sub>F cf_id (cat_FUNCT \<alpha> \<DD> \<AA>) :
        cat_FUNCT \<alpha> \<DD> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<DD> \<AA>"
      by
        (
          cs_concl
            cs_simp: 
              exp_cat_cf_cat_cf_id[symmetric] exp_cat_cf_cf_comp[symmetric] 
            cs_intro: cat_small_cs_intros cat_FUNCT_cs_intros adj_cs_intros
        )
    note [symmetric, cat_cs_simps] =
      ntcf_id_exp_cat_cf
      exp_cat_ntcf_ntcf_vcomp
      exp_cat_ntcf_ntcf_cf_comp
      exp_cat_ntcf_cf_ntcf_comp
    from assms show
      "exp_cat_cf \<alpha> \<AA> \<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_cat_ntcf \<alpha> \<AA> (\<epsilon>\<^sub>C \<Phi>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
        (exp_cat_ntcf \<alpha> \<AA> (\<eta>\<^sub>C \<Phi>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<FF>) =
        ntcf_id (exp_cat_cf \<alpha> \<AA> \<FF>)"
      by
        (
          cs_concl 
            cs_simp: adj_cs_simps cat_cs_simps
            cs_intro: adj_cs_intros cat_cs_intros
        )
    from assms show
      "exp_cat_ntcf \<alpha> \<AA> (\<epsilon>\<^sub>C \<Phi>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
        (exp_cat_cf \<alpha> \<AA> \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_cat_ntcf \<alpha> \<AA> (\<eta>\<^sub>C \<Phi>)) =
        ntcf_id (exp_cat_cf \<alpha> \<AA> \<GG>)"
      by 
        (
          cs_concl 
            cs_simp: adj_cs_simps cat_cs_simps
            cs_intro: adj_cs_intros cat_cs_intros
        )
  qed
    (
      use assms in 
        \<open>
          cs_concl
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        \<close>
    )+

qed

text\<open>\newpage\<close>

end