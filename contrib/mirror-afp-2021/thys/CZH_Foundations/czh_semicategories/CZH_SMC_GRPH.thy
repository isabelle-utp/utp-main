(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>GRPH\<close> as a semicategory\<close>
theory CZH_SMC_GRPH
  imports 
    CZH_DG_Simple
    CZH_DG_GRPH
    CZH_SMC_Small_Semicategory
begin



subsection\<open>Background\<close>

text\<open>
The methodology for the exposition 
of \<open>GRPH\<close> as a semicategory is analogous to the 
one used in the previous chapter
for the exposition of \<open>GRPH\<close> as a digraph.
\<close>

named_theorems smc_GRPH_cs_simps
named_theorems smc_GRPH_cs_intros



subsection\<open>Definition and elementary properties\<close>

definition smc_GRPH :: "V \<Rightarrow> V"
  where "smc_GRPH \<alpha> =
    [
      set {\<CC>. digraph \<alpha> \<CC>}, 
      all_dghms \<alpha>, 
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_dghms \<alpha>. \<FF>\<lparr>HomDom\<rparr>), 
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_dghms \<alpha>. \<FF>\<lparr>HomCod\<rparr>),
      (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (dg_GRPH \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smc_GRPH_components:
  shows "smc_GRPH \<alpha>\<lparr>Obj\<rparr> = set {\<CC>. digraph \<alpha> \<CC>}"
    and "smc_GRPH \<alpha>\<lparr>Arr\<rparr> = all_dghms \<alpha>"
    and "smc_GRPH \<alpha>\<lparr>Dom\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_dghms \<alpha>. \<FF>\<lparr>HomDom\<rparr>)"
    and "smc_GRPH \<alpha>\<lparr>Cod\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_dghms \<alpha>. \<FF>\<lparr>HomCod\<rparr>)"
    and "smc_GRPH \<alpha>\<lparr>Comp\<rparr> = 
      (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (dg_GRPH \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_GRPH_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smc_dg_GRPH: "smc_dg (smc_GRPH \<alpha>) = dg_GRPH \<alpha>"
proof(rule vsv_eqI)
  show "vsv (smc_dg (smc_GRPH \<alpha>))" unfolding smc_dg_def by auto
  show "vsv (dg_GRPH \<alpha>)" unfolding dg_GRPH_def by auto
  have dom_lhs: "\<D>\<^sub>\<circ> (smc_dg (smc_GRPH \<alpha>)) = 4\<^sub>\<nat>" 
    unfolding smc_dg_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (dg_GRPH \<alpha>) = 4\<^sub>\<nat>"
    unfolding dg_GRPH_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (smc_dg (smc_GRPH \<alpha>)) = \<D>\<^sub>\<circ> (dg_GRPH \<alpha>)"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_dg (smc_GRPH \<alpha>)) \<Longrightarrow> smc_dg (smc_GRPH \<alpha>)\<lparr>a\<rparr> = dg_GRPH \<alpha>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral, 
        unfold smc_dg_def dg_field_simps smc_GRPH_def dg_GRPH_def
      )
      (auto simp: nat_omega_simps)
qed

lemmas_with [folded smc_dg_GRPH, unfolded slicing_simps]: 
  smc_GRPH_ObjI = dg_GRPH_ObjI
  and smc_GRPH_ObjD = dg_GRPH_ObjD
  and smc_GRPH_ObjE = dg_GRPH_ObjE
  and smc_GRPH_Obj_iff[smc_GRPH_cs_simps] = dg_GRPH_Obj_iff  
  and smc_GRPH_Dom_app[smc_GRPH_cs_simps] = dg_GRPH_Dom_app
  and smc_GRPH_Cod_app[smc_GRPH_cs_simps] = dg_GRPH_Cod_app
  and smc_GRPH_is_arrI = dg_GRPH_is_arrI
  and smc_GRPH_is_arrD = dg_GRPH_is_arrD
  and smc_GRPH_is_arrE = dg_GRPH_is_arrE
  and smc_GRPH_is_arr_iff[smc_GRPH_cs_simps] = dg_GRPH_is_arr_iff



subsection\<open>Composable arrows\<close>

lemma smc_GRPH_composable_arrs_dg_GRPH: 
  "composable_arrs (dg_GRPH \<alpha>) = composable_arrs (smc_GRPH \<alpha>)"
  unfolding composable_arrs_def smc_dg_GRPH[symmetric] slicing_simps by auto

lemma smc_GRPH_Comp: 
  "smc_GRPH \<alpha>\<lparr>Comp\<rparr> = (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (smc_GRPH \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_GRPH_components smc_GRPH_composable_arrs_dg_GRPH ..



subsection\<open>Composition\<close>

lemma smc_GRPH_Comp_app:
  assumes "\<GG> : \<BB> \<mapsto>\<^bsub>smc_GRPH \<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<^bsub>smc_GRPH \<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>A\<^bsub>smc_GRPH \<alpha>\<^esub> \<FF> = \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>"
proof-
  from assms have "[\<GG>, \<FF>]\<^sub>\<circ> \<in>\<^sub>\<circ> composable_arrs (smc_GRPH \<alpha>)" 
    by (auto intro: smc_cs_intros)
  then show "\<GG> \<circ>\<^sub>A\<^bsub>smc_GRPH \<alpha>\<^esub> \<FF> = \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>"
    unfolding smc_GRPH_Comp by (simp add: nat_omega_simps)
qed 

lemma smc_GRPH_Comp_vdomain:
  "\<D>\<^sub>\<circ> (smc_GRPH \<alpha>\<lparr>Comp\<rparr>) = composable_arrs (smc_GRPH \<alpha>)" 
  unfolding smc_GRPH_Comp by auto                      



subsection\<open>\<open>GRPH\<close> is a semicategory\<close>

lemma (in \<Z>) tiny_semicategory_smc_GRPH:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_semicategory \<beta> (smc_GRPH \<alpha>)"
proof(intro tiny_semicategoryI, unfold smc_GRPH_is_arr_iff)
  show "vfsequence (smc_GRPH \<alpha>)" unfolding smc_GRPH_def by auto
  show "vcard (smc_GRPH \<alpha>) = 5\<^sub>\<nat>"
    unfolding smc_GRPH_def by (simp add: nat_omega_simps)
  show "(gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_GRPH \<alpha>\<lparr>Comp\<rparr>)) \<longleftrightarrow>
    (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> c \<and> f : a \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> b)"
    for gf
    unfolding smc_GRPH_Comp_vdomain
  proof
    show "gf \<in>\<^sub>\<circ> composable_arrs (smc_GRPH \<alpha>) \<Longrightarrow> 
      \<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> c \<and> f : a \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> b"
      by (elim composable_arrsE) (auto simp: smc_GRPH_is_arr_iff)
  next
    assume "\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> c \<and> f : a \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> b"
    with smc_GRPH_is_arr_iff show "gf \<in>\<^sub>\<circ> composable_arrs (smc_GRPH \<alpha>)"
      unfolding smc_GRPH_Comp_vdomain by (auto intro: smc_cs_intros)
  qed
  show "\<lbrakk> g : b \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> c; f : a \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> b \<rbrakk> \<Longrightarrow> 
    g \<circ>\<^sub>A\<^bsub>smc_GRPH \<alpha>\<^esub> f : a \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> c"
    for g b c f a
    by (auto simp: smc_GRPH_Comp_app dghm_comp_is_dghm smc_GRPH_cs_simps)
  fix h c d g b f a
  assume "h : c \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> d" "g : b \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> c" "f : a \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> b"
  moreover then have "g \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M f : a \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> c" "h \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M g : b \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> d" 
    by (auto simp: dghm_comp_is_dghm smc_GRPH_cs_simps)
  ultimately show 
    "h \<circ>\<^sub>A\<^bsub>smc_GRPH \<alpha>\<^esub> g \<circ>\<^sub>A\<^bsub>smc_GRPH \<alpha>\<^esub> f =
      h \<circ>\<^sub>A\<^bsub>smc_GRPH \<alpha>\<^esub> (g \<circ>\<^sub>A\<^bsub>smc_GRPH \<alpha>\<^esub> f)"
    by (simp add: smc_GRPH_is_arr_iff smc_GRPH_Comp_app dghm_comp_assoc)
qed (simp_all add: assms smc_dg_GRPH tiny_digraph_dg_GRPH smc_GRPH_components)



subsection\<open>Initial object\<close>

lemma (in \<Z>) smc_GRPH_obj_initialI: "obj_initial (smc_GRPH \<alpha>) dg_0"
  unfolding obj_initial_def
proof
  (
    intro obj_terminalI, 
    unfold smc_op_simps smc_GRPH_is_arr_iff smc_GRPH_Obj_iff
  )
  show "digraph \<alpha> dg_0" by (intro digraph_dg_0)
  fix \<AA> assume "digraph \<alpha> \<AA>"
  then interpret digraph \<alpha> \<AA> .
  show "\<exists>!f. f : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA>"
  proof
    show dghm_0: "dghm_0 \<AA> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA>"
      by (simp add: dghm_0_is_dghm digraph_axioms is_ft_dghm.axioms(1))
    fix \<FF> assume prems: "\<FF> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA>" 
    then interpret \<FF>: is_dghm \<alpha> dg_0 \<AA> \<FF> .
    show "\<FF> = dghm_0 \<AA>"
    proof(rule dghm_eqI)
      from dghm_0 show "dghm_0 \<AA> : dg_0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA>"
        unfolding smc_GRPH_is_arr_iff by simp
      have [simp]: "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = 0" by (simp add: dg_cs_simps dg_0_components)
      with \<FF>.ObjMap.vdomain_vrange_is_vempty show "\<FF>\<lparr>ObjMap\<rparr> = dghm_0 \<AA>\<lparr>ObjMap\<rparr>"
        by 
          (
            auto 
              intro: \<FF>.ObjMap.vsv_vrange_vempty 
              simp: dg_0_components dghm_0_components
          )
      from \<FF>.dghm_ObjMap_vdomain have "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = 0" 
        by 
          (
            auto
              simp: \<FF>.dghm_ArrMap_vdomain 
              intro: \<FF>.HomDom.dg_Arr_vempty_if_Obj_vempty
          )
      then show "\<FF>\<lparr>ArrMap\<rparr> = dghm_0 \<AA>\<lparr>ArrMap\<rparr>"
        by 
          (
            metis 
              \<FF>.ArrMap.vsv_axioms 
              dghm_0_components(2) 
              vsv.vdomain_vrange_is_vempty 
              vsv.vsv_vrange_vempty
          )
    qed (auto simp: dghm_0_components prems)
  qed
qed

lemma (in \<Z>) smc_GRPH_obj_initialD:
  assumes "obj_initial (smc_GRPH \<alpha>) \<AA>"
  shows "\<AA> = dg_0" 
  using assms unfolding obj_initial_def
proof
  (
    elim obj_terminalE,
    unfold smc_op_simps smc_GRPH_is_arr_iff smc_GRPH_Obj_iff
  )
  assume prems: "digraph \<alpha> \<AA>" "digraph \<alpha> \<BB> \<Longrightarrow> \<exists>!\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" for \<BB>
  from prems(2)[OF digraph_dg_0] obtain \<FF> where \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> dg_0" 
    by meson
  interpret \<FF>: is_dghm \<alpha> \<AA> dg_0 \<FF> by (rule \<FF>) 
  have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> 0"
    unfolding dg_0_components(1)[symmetric] by (simp add: \<FF>.dghm_ObjMap_vrange)
  then have "\<FF>\<lparr>ObjMap\<rparr> = 0" by (auto intro: \<FF>.ObjMap.vsv_vrange_vempty)
  with \<FF>.dghm_ObjMap_vdomain have Obj[simp]: "\<AA>\<lparr>Obj\<rparr> = 0" by auto
  have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> 0"
    unfolding dg_0_components(2)[symmetric]
    by (simp add: \<FF>.dghm_ArrMap_vrange)
  then have "\<FF>\<lparr>ArrMap\<rparr> = 0" by (auto intro: \<FF>.ArrMap.vsv_vrange_vempty)
  with \<FF>.dghm_ArrMap_vdomain have Arr[simp]: "\<AA>\<lparr>Arr\<rparr> = 0" by auto
  from Arr \<FF>.HomDom.dg_Dom_vempty_if_Arr_vempty have [simp]: "\<AA>\<lparr>Dom\<rparr> = []\<^sub>\<circ>" 
    by auto
  from Arr \<FF>.HomDom.dg_Cod_vempty_if_Arr_vempty have [simp]: "\<AA>\<lparr>Cod\<rparr> = []\<^sub>\<circ>"
    by auto
  show "\<AA> = dg_0"
    by (rule dg_eqI[of \<alpha>]) (simp_all add: prems(1) dg_0_components digraph_dg_0)
qed

lemma (in \<Z>) smc_GRPH_obj_initialE:
  assumes "obj_initial (smc_GRPH \<alpha>) \<AA>"
  obtains "\<AA> = dg_0" 
  using assms by (auto dest: smc_GRPH_obj_initialD)

lemma (in \<Z>) smc_GRPH_obj_initial_iff[smc_GRPH_cs_simps]: 
  "obj_initial (smc_GRPH \<alpha>) \<AA> \<longleftrightarrow> \<AA> = dg_0"
  using smc_GRPH_obj_initialI smc_GRPH_obj_initialD by auto



subsection\<open>Terminal object\<close>

lemma (in \<Z>) smc_GRPH_obj_terminalI[smc_GRPH_cs_intros]: 
  assumes "a \<in>\<^sub>\<circ> Vset \<alpha>" and "f \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "obj_terminal (smc_GRPH \<alpha>) (dg_1 a f)"
proof
  (
    intro obj_terminalI, 
    unfold smc_op_simps smc_GRPH_is_arr_iff smc_GRPH_Obj_iff
  )
  fix \<AA> assume "digraph \<alpha> \<AA>"
  then interpret digraph \<alpha> \<AA> .
  show "\<exists>!\<FF>'. \<FF>' : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> dg_1 a f"
  proof
    show dghm_1: "dghm_const \<AA> (dg_1 a f) a f : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> dg_1 a f"
      by 
        (
          auto simp:
            assms 
            dg_1_is_arr_iff 
            dghm_const_is_dghm 
            digraph_axioms' 
            digraph_dg_1
        )
    fix \<FF>' assume prems: "\<FF>' : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> dg_1 a f"
    then interpret \<FF>': is_dghm \<alpha> \<AA> \<open>dg_1 a f\<close> \<FF>' .
    show "\<FF>' = dghm_const \<AA> (dg_1 a f) a f"
    proof(rule dghm_eqI, unfold dghm_const_components)
      show "dghm_const \<AA> (dg_1 a f) a f : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> dg_1 a f" by (rule dghm_1)
      show "\<FF>'\<lparr>ObjMap\<rparr> = vconst_on (\<AA>\<lparr>Obj\<rparr>) a"
      proof(cases\<open>\<AA>\<lparr>Obj\<rparr> = 0\<close>)
        case True
        then have "\<FF>'\<lparr>ObjMap\<rparr> = 0"
          by 
            (
              simp add: 
                \<FF>'.ObjMap.vdomain_vrange_is_vempty 
                \<FF>'.dghm_ObjMap_vsv 
                vsv.vsv_vrange_vempty
            )
        with True show ?thesis by simp
      next
        case False
        then have "\<D>\<^sub>\<circ> (\<FF>'\<lparr>ObjMap\<rparr>) \<noteq> 0" by (auto simp: \<FF>'.dghm_ObjMap_vdomain)
        with False have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ObjMap\<rparr>) \<noteq> 0" by fastforce
        moreover from \<FF>'.dghm_ObjMap_vrange have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> set {a}"
          by (simp add: dg_1_components)
        ultimately have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ObjMap\<rparr>) = set {a}" by auto
        with \<FF>'.dghm_ObjMap_vdomain show ?thesis
          by (intro vsv.vsv_is_vconst_onI) blast+
      qed
      show "\<FF>'\<lparr>ArrMap\<rparr> = vconst_on (\<AA>\<lparr>Arr\<rparr>) f"
      proof(cases\<open>\<AA>\<lparr>Arr\<rparr> = 0\<close>)
        case True
        then have "\<FF>'\<lparr>ArrMap\<rparr> = 0"
          by 
            (
              simp add: 
                \<FF>'.ArrMap.vdomain_vrange_is_vempty 
                \<FF>'.dghm_ArrMap_vsv 
                vsv.vsv_vrange_vempty
            )
        with True show ?thesis by simp
      next
        case False
        then have "\<D>\<^sub>\<circ> (\<FF>'\<lparr>ArrMap\<rparr>) \<noteq> 0" by (auto simp: \<FF>'.dghm_ArrMap_vdomain)
        with False have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ArrMap\<rparr>) \<noteq> 0" 
          by (force simp: \<FF>'.ArrMap.vdomain_vrange_is_vempty)
        moreover from \<FF>'.dghm_ArrMap_vrange have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> set {f}"
          by (simp add: dg_1_components)
        ultimately have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ArrMap\<rparr>) = set {f}" by auto
        then show ?thesis 
          by (intro vsv.vsv_is_vconst_onI) (auto simp: \<FF>'.dghm_ArrMap_vdomain)
      qed
    qed (auto intro: prems)
  qed 
qed (simp add: assms digraph_dg_1)

lemma (in \<Z>) smc_GRPH_obj_terminalE: 
  assumes "obj_terminal (smc_GRPH \<alpha>) \<BB>"
  obtains a f where "a \<in>\<^sub>\<circ> Vset \<alpha>" and "f \<in>\<^sub>\<circ> Vset \<alpha>" and "\<BB> = dg_1 a f"
  using assms
proof
  (
    elim obj_terminalE; 
    unfold smc_op_simps smc_GRPH_is_arr_iff smc_GRPH_Obj_iff
  )  
  assume prems: "digraph \<alpha> \<BB>" "digraph \<alpha> \<AA> \<Longrightarrow> \<exists>!\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" for \<AA>
  then interpret \<BB>: digraph \<alpha> \<BB> by simp
  obtain a where \<BB>_Obj: "\<BB>\<lparr>Obj\<rparr> = set {a}" and a: "a \<in>\<^sub>\<circ> Vset \<alpha>"
  proof-
    have dg_10: "digraph \<alpha> (dg_10 0)" by (rule digraph_dg_10) auto
    from prems(2)[OF dg_10] obtain \<FF> 
      where \<FF>: "\<FF> : dg_10 0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" 
        and \<GG>\<FF>: "\<GG> : dg_10 0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB> \<Longrightarrow> \<GG> = \<FF>" for \<GG>
      by fastforce
    interpret \<FF>: is_dghm \<alpha> \<open>dg_10 0\<close> \<BB> \<FF> by (rule \<FF>)
    have "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = set {0}" 
      by (simp add: dg_cs_simps dg_10_components)
    then obtain a where vrange_\<FF>[simp]: "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = set {a}"
      by 
        (
          auto 
            simp: dg_cs_simps 
            intro: \<FF>.ObjMap.vsv_vdomain_vsingleton_vrange_vsingleton
        )
    with \<BB>.dg_Obj_vsubset_Vset \<FF>.dghm_ObjMap_vrange have [simp]: "a \<in>\<^sub>\<circ> Vset \<alpha>"
      by auto
    from \<FF>.dghm_ObjMap_vrange have "set {a} \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by simp
    moreover have "\<BB>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> set {a}"
    proof(rule ccontr)
      assume "\<not>\<BB>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> set {a}"
      then obtain b where ba: "b \<noteq> a" and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by force
      define \<GG> where "\<GG> = [set {\<langle>0, b\<rangle>}, 0, dg_10 0, \<BB>]\<^sub>\<circ>"
      have \<GG>_components: 
        "\<GG>\<lparr>ObjMap\<rparr> = set {\<langle>0, b\<rangle>}"
        "\<GG>\<lparr>ArrMap\<rparr> = 0"
        "\<GG>\<lparr>HomDom\<rparr> = dg_10 0"
        "\<GG>\<lparr>HomCod\<rparr> = \<BB>"
        unfolding \<GG>_def dghm_field_simps by (simp_all add: nat_omega_simps)
      have \<GG>: "\<GG> : dg_10 0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
        by (rule is_dghmI, unfold \<GG>_components dg_10_components)
          (
            auto simp: 
              dg_cs_intros
              nat_omega_simps 
              digraph_dg_10
              \<GG>_def 
              dg_10_is_arr_iff 
              b 
              vsubset_vsingleton_leftI
          )
      then have \<GG>_def: "\<GG> = \<FF>" by (rule \<GG>\<FF>)
      have "\<R>\<^sub>\<circ> (\<GG>\<lparr>ObjMap\<rparr>) = set {b}" unfolding \<GG>_components by simp
      with vrange_\<FF> ba show False unfolding \<GG>_def by simp  
    qed
    ultimately have "\<BB>\<lparr>Obj\<rparr> = set {a}" by simp
    with that show ?thesis by simp
  qed
  obtain f where \<BB>_Arr: "\<BB>\<lparr>Arr\<rparr> = set {f}" and f: "f \<in>\<^sub>\<circ> Vset \<alpha>"
  proof-
    from prems(2)[OF digraph_dg_1, of 0 0] obtain \<FF> 
      where \<FF>: "\<FF> : dg_1 0 0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" 
        and \<GG>\<FF>: "\<GG> : dg_1 0 0 \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB> \<Longrightarrow> \<GG> = \<FF>" for \<GG>
      by fastforce
    interpret \<FF>: is_dghm \<alpha> \<open>dg_1 0 0\<close> \<BB> \<FF> by (rule \<FF>)
    have "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = set {0}" 
      by (simp add: dg_cs_simps dg_1_components)
    then obtain a' where "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = set {a'}"
      by 
        (
          auto 
            simp: dg_cs_simps 
            intro: \<FF>.ObjMap.vsv_vdomain_vsingleton_vrange_vsingleton
        )
    with \<BB>_Obj \<FF>.dghm_ObjMap_vrange have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = set {a}" by auto
    have "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = set {0}" by (simp add: dg_cs_simps dg_1_components)
    then obtain f where vrange_\<FF>[simp]: "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = set {f}"
      by 
        (
          auto 
            simp: dg_cs_simps 
            intro: \<FF>.ArrMap.vsv_vdomain_vsingleton_vrange_vsingleton
        )
    with \<BB>.dg_Arr_vsubset_Vset \<FF>.dghm_ArrMap_vrange have [simp]: "f \<in>\<^sub>\<circ> Vset \<alpha>"
      by auto
    from \<FF>.dghm_ArrMap_vrange have "set {f} \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" by simp
    moreover have "\<BB>\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> set {f}"
    proof(rule ccontr)
      assume "\<not>\<BB>\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> set {f}"
      then obtain g where gf: "g \<noteq> f" and g: "g \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" by force
      have g: "g : a \<mapsto>\<^bsub>\<BB>\<^esub> a"
      proof(intro is_arrI)
        from g \<BB>_Obj show "\<BB>\<lparr>Dom\<rparr>\<lparr>g\<rparr> = a"
          by (metis \<BB>.dg_is_arrD(2) is_arr_def vsingleton_iff)
        from g \<BB>_Obj show "\<BB>\<lparr>Cod\<rparr>\<lparr>g\<rparr> = a"
          by (metis \<BB>.dg_is_arrD(3) is_arr_def vsingleton_iff)
      qed (auto simp: g)
      define \<GG> where "\<GG> = [set {\<langle>0, a\<rangle>}, set {\<langle>0, g\<rangle>}, dg_1 0 0, \<BB>]\<^sub>\<circ>"
      have \<GG>_components: 
        "\<GG>\<lparr>ObjMap\<rparr> = set {\<langle>0, a\<rangle>}"
        "\<GG>\<lparr>ArrMap\<rparr> = set {\<langle>0, g\<rangle>}"
        "\<GG>\<lparr>HomDom\<rparr> = dg_1 0 0"
        "\<GG>\<lparr>HomCod\<rparr> = \<BB>"
        unfolding \<GG>_def dghm_field_simps by (simp_all add: nat_omega_simps)
      have \<GG>: "\<GG> : dg_1 0 0  \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
        by (rule is_dghmI, unfold \<GG>_components dg_1_components)
          (
            auto simp: 
              dg_cs_intros nat_omega_simps \<GG>_def dg_1_is_arr_iff \<BB>_Obj g
          )
      then have \<GG>_def: "\<GG> = \<FF>" by (rule \<GG>\<FF>)
      have "\<R>\<^sub>\<circ> (\<GG>\<lparr>ArrMap\<rparr>) = set {g}" unfolding \<GG>_components by simp
      with vrange_\<FF> gf show False unfolding \<GG>_def by simp  
    qed
    ultimately have "\<BB>\<lparr>Arr\<rparr> = set {f}" by simp
    with that show ?thesis by simp
  qed
  have "\<BB> = dg_1 a f"
  proof(rule dg_eqI[of \<alpha>], unfold dg_1_components)
    show "\<BB>\<lparr>Obj\<rparr> = set {a}" by (simp add: \<BB>_Obj)
    moreover show "\<BB>\<lparr>Arr\<rparr> = set {f}" by (simp add: \<BB>_Arr)
    ultimately have "\<BB>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = a" "\<BB>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = a"
      by (metis \<BB>.dg_is_arrE is_arr_def vsingleton_iff)+
    have "\<D>\<^sub>\<circ> (\<BB>\<lparr>Dom\<rparr>) = set {f}" by (simp add: dg_cs_simps \<BB>_Arr)
    moreover from \<BB>.Dom.vsv_vrange_vempty \<BB>.dg_Dom_vdomain \<BB>.dg_Dom_vrange  
    have "\<R>\<^sub>\<circ> (\<BB>\<lparr>Dom\<rparr>) = set {a}" by (fastforce simp: \<BB>_Arr \<BB>_Obj)
    ultimately show "\<BB>\<lparr>Dom\<rparr> = set {\<langle>f, a\<rangle>}"  
      using \<BB>.Dom.vsv_vdomain_vrange_vsingleton by simp
    have "\<D>\<^sub>\<circ> (\<BB>\<lparr>Cod\<rparr>) = set {f}" by (simp add: dg_cs_simps \<BB>_Arr)
    moreover from \<BB>.Cod.vsv_vrange_vempty \<BB>.dg_Cod_vdomain \<BB>.dg_Cod_vrange  
    have "\<R>\<^sub>\<circ> (\<BB>\<lparr>Cod\<rparr>) = set {a}" 
      by (fastforce simp: \<BB>_Arr \<BB>_Obj)
    ultimately show "\<BB>\<lparr>Cod\<rparr> = set {\<langle>f, a\<rangle>}"  
      using assms \<BB>.Cod.vsv_vdomain_vrange_vsingleton by simp
  qed (auto simp: dg_cs_intros \<BB>_Obj digraph_dg_1 a f)
  with a f that show ?thesis by auto
qed

text\<open>\newpage\<close>

end