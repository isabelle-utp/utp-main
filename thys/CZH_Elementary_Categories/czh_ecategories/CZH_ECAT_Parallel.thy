(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>\<up>\<up>\<close>: category with parallel arrows between two objects\<close>
theory CZH_ECAT_Parallel
  imports CZH_ECAT_Small_Functor
begin



subsection\<open>Background\<close>

named_theorems cat_parallel_cs_simps
named_theorems cat_parallel_cs_intros

named_theorems cat_parallel_elem_simps

definition \<aa>\<^sub>P\<^sub>L where [cat_parallel_elem_simps]: "\<aa>\<^sub>P\<^sub>L = 1\<^sub>\<nat>"
definition \<bb>\<^sub>P\<^sub>L where [cat_parallel_elem_simps]: "\<bb>\<^sub>P\<^sub>L = 2\<^sub>\<nat>"
definition \<gg>\<^sub>P\<^sub>L where [cat_parallel_elem_simps]: "\<gg>\<^sub>P\<^sub>L = 3\<^sub>\<nat>"
definition \<ff>\<^sub>P\<^sub>L where [cat_parallel_elem_simps]: "\<ff>\<^sub>P\<^sub>L = 4\<^sub>\<nat>"

lemma cat_PL_ineq:
  shows cat_PL_\<aa>\<bb>[cat_parallel_cs_intros]: "\<aa>\<^sub>P\<^sub>L \<noteq> \<bb>\<^sub>P\<^sub>L"
    and cat_PL_\<aa>\<gg>[cat_parallel_cs_intros]: "\<aa>\<^sub>P\<^sub>L \<noteq> \<gg>\<^sub>P\<^sub>L"
    and cat_PL_\<aa>\<ff>[cat_parallel_cs_intros]: "\<aa>\<^sub>P\<^sub>L \<noteq> \<ff>\<^sub>P\<^sub>L"
    and cat_PL_\<bb>\<gg>[cat_parallel_cs_intros]: "\<bb>\<^sub>P\<^sub>L \<noteq> \<gg>\<^sub>P\<^sub>L"
    and cat_PL_\<bb>\<ff>[cat_parallel_cs_intros]: "\<bb>\<^sub>P\<^sub>L \<noteq> \<ff>\<^sub>P\<^sub>L"
    and cat_PL_\<gg>\<ff>[cat_parallel_cs_intros]: "\<gg>\<^sub>P\<^sub>L \<noteq> \<ff>\<^sub>P\<^sub>L"
  unfolding cat_parallel_elem_simps by simp_all

lemma (in \<Z>) 
  shows cat_PL_\<aa>[cat_parallel_cs_intros]: "\<aa>\<^sub>P\<^sub>L \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_PL_\<bb>[cat_parallel_cs_intros]: "\<bb>\<^sub>P\<^sub>L \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_PL_\<gg>[cat_parallel_cs_intros]: "\<gg>\<^sub>P\<^sub>L \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_PL_\<ff>[cat_parallel_cs_intros]: "\<ff>\<^sub>P\<^sub>L \<in>\<^sub>\<circ> Vset \<alpha>"
  unfolding cat_parallel_elem_simps by simp_all



subsection\<open>Composable arrows\<close>

abbreviation cat_parallel_composable :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cat_parallel_composable \<aa> \<bb> \<gg> \<ff> \<equiv>
    (set {\<bb>} \<times>\<^sub>\<bullet> set {\<bb>, \<gg>, \<ff>}) \<union>\<^sub>\<circ> (set {\<aa>, \<gg>, \<ff>} \<times>\<^sub>\<bullet> set {\<aa>})"


text\<open>Rules.\<close>

lemma cat_parallel_composable_\<aa>\<aa>[cat_parallel_cs_intros]:
  assumes "g = \<aa>" and "f = \<aa>"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
  unfolding assms by auto

lemma cat_parallel_composable_\<aa>\<gg>[cat_parallel_cs_intros]:
  assumes "g = \<bb>" and "f = \<gg>"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
  unfolding assms by auto

lemma cat_parallel_composable_\<aa>\<ff>[cat_parallel_cs_intros]:
  assumes "g = \<bb>" and "f = \<ff>"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
  unfolding assms by auto

lemma cat_parallel_composable_\<gg>\<aa>[cat_parallel_cs_intros]:
  assumes "g = \<gg>" and "f = \<aa>"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
  unfolding assms by auto

lemma cat_parallel_composable_\<ff>\<aa>[cat_parallel_cs_intros]:
  assumes "g = \<ff>" and "f = \<aa>"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
  unfolding assms by auto

lemma cat_parallel_composable_\<bb>\<bb>[cat_parallel_cs_intros]:
  assumes "g = \<bb>" and "f = \<bb>"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
  unfolding assms by auto

lemma cat_parallel_composableE:
  assumes "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
  obtains "g = \<bb>" and "f = \<bb>"
        | "g = \<bb>" and "f = \<gg>" 
        | "g = \<bb>" and "f = \<ff>"
        | "g = \<gg>" and "f = \<aa>"
        | "g = \<ff>" and "f = \<aa>"
        | "g = \<aa>" and "f = \<aa>"
  using assms that by auto


text\<open>Elementary properties.\<close>

lemma cat_parallel_composable_fconverse: 
  "(cat_parallel_composable \<aa> \<bb> \<gg> \<ff>)\<inverse>\<^sub>\<bullet> = cat_parallel_composable \<bb> \<aa> \<ff> \<gg>"
  by auto



subsection\<open>
Local assumptions for a category with parallel arrows between two objects
\<close>

locale cat_parallel = \<Z> \<alpha> for \<alpha> +  
  fixes \<aa> \<bb> \<gg> \<ff>
  assumes cat_parallel_\<aa>\<bb>[cat_parallel_cs_intros]: "\<aa> \<noteq> \<bb>"
    and cat_parallel_\<aa>\<gg>[cat_parallel_cs_intros]: "\<aa> \<noteq> \<gg>"
    and cat_parallel_\<aa>\<ff>[cat_parallel_cs_intros]: "\<aa> \<noteq> \<ff>"
    and cat_parallel_\<bb>\<gg>[cat_parallel_cs_intros]: "\<bb> \<noteq> \<gg>"
    and cat_parallel_\<bb>\<ff>[cat_parallel_cs_intros]: "\<bb> \<noteq> \<ff>"
    and cat_parallel_\<gg>\<ff>[cat_parallel_cs_intros]: "\<gg> \<noteq> \<ff>"
    and cat_parallel_\<aa>_in_Vset[cat_parallel_cs_intros]: "\<aa> \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_parallel_\<bb>_in_Vset[cat_parallel_cs_intros]: "\<bb> \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_parallel_\<gg>_in_Vset[cat_parallel_cs_intros]: "\<gg> \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_parallel_\<ff>_in_Vset[cat_parallel_cs_intros]: "\<ff> \<in>\<^sub>\<circ> Vset \<alpha>"

lemmas (in cat_parallel) cat_parallel_ineq =
  cat_parallel_\<aa>\<bb>
  cat_parallel_\<aa>\<gg>
  cat_parallel_\<aa>\<ff>
  cat_parallel_\<bb>\<gg>
  cat_parallel_\<bb>\<ff>
  cat_parallel_\<gg>\<ff> 


text\<open>Rules.\<close>

lemmas (in cat_parallel) [cat_parallel_cs_intros] = cat_parallel_axioms

mk_ide rf cat_parallel_def[unfolded cat_parallel_axioms_def]
  |intro cat_parallelI|
  |dest cat_parallelD[dest]|
  |elim cat_parallelE[elim]|


text\<open>Duality.\<close>

lemma (in cat_parallel) cat_parallel_op[cat_op_intros]: 
  "cat_parallel \<alpha> \<bb> \<aa> \<ff> \<gg>"
  by (intro cat_parallelI) 
    (auto intro!: cat_parallel_cs_intros cat_parallel_ineq[symmetric])



subsection\<open>\<open>\<up>\<up>\<close>: category with parallel arrows between two objects\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-2 and Chapter III-3 in \cite{mac_lane_categories_2010}.\<close>

definition the_cat_parallel :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>\<up>\<up>\<^sub>C\<close>)
  where "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff> =
    [
      set {\<aa>, \<bb>},
      set {\<aa>, \<bb>, \<gg>, \<ff>},
      (\<lambda>x\<in>\<^sub>\<circ>set {\<aa>, \<bb>, \<gg>, \<ff>}. (x = \<bb> ? \<bb> : \<aa>)),
      (\<lambda>x\<in>\<^sub>\<circ>set {\<aa>, \<bb>, \<gg>, \<ff>}. (x = \<aa> ? \<aa> : \<bb>)),
      (
        \<lambda>gf\<in>\<^sub>\<circ>cat_parallel_composable \<aa> \<bb> \<gg> \<ff>.
         if gf = [\<bb>, \<bb>]\<^sub>\<circ> \<Rightarrow> \<bb>
          | gf = [\<bb>, \<gg>]\<^sub>\<circ> \<Rightarrow> \<gg>
          | gf = [\<bb>, \<ff>]\<^sub>\<circ> \<Rightarrow> \<ff>
          | gf = [\<gg>, \<aa>]\<^sub>\<circ> \<Rightarrow> \<gg>
          | gf = [\<ff>, \<aa>]\<^sub>\<circ> \<Rightarrow> \<ff>
          | otherwise \<Rightarrow> \<aa>
      ),
      vid_on (set {\<aa>, \<bb>})
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma the_cat_parallel_components: 
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr> = set {\<aa>, \<bb>}"
    and "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr> = set {\<aa>, \<bb>, \<gg>, \<ff>}"
    and "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr> = (\<lambda>x\<in>\<^sub>\<circ>set {\<aa>, \<bb>, \<gg>, \<ff>}. (x = \<bb> ? \<bb> : \<aa>))"
    and "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr> = (\<lambda>x\<in>\<^sub>\<circ>set {\<aa>, \<bb>, \<gg>, \<ff>}. (x = \<aa> ? \<aa> : \<bb>))"
    and "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Comp\<rparr> =
      (
        \<lambda>gf\<in>\<^sub>\<circ>cat_parallel_composable \<aa> \<bb> \<gg> \<ff>.
         if gf = [\<bb>, \<bb>]\<^sub>\<circ> \<Rightarrow> \<bb>
          | gf = [\<bb>, \<gg>]\<^sub>\<circ> \<Rightarrow> \<gg>
          | gf = [\<bb>, \<ff>]\<^sub>\<circ> \<Rightarrow> \<ff>
          | gf = [\<gg>, \<aa>]\<^sub>\<circ> \<Rightarrow> \<gg>
          | gf = [\<ff>, \<aa>]\<^sub>\<circ> \<Rightarrow> \<ff>
          | otherwise \<Rightarrow> \<aa>
      )"
    and "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>CId\<rparr> = vid_on (set {\<aa>, \<bb>})"
  unfolding the_cat_parallel_def dg_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Objects\<close>

lemma the_cat_parallel_Obj_\<aa>I[cat_parallel_cs_intros]:
  assumes "a = \<aa>"
  shows "a \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>"
  using assms unfolding the_cat_parallel_components by simp

lemma the_cat_parallel_Obj_\<bb>I[cat_parallel_cs_intros]:
  assumes "a = \<bb>"
  shows "a \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>"
  using assms unfolding the_cat_parallel_components by simp

lemma the_cat_parallel_ObjE:
  assumes "a \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>"
  obtains "a = \<aa>" | "a = \<bb>" 
  using assms unfolding the_cat_parallel_components(1) by fastforce


subsubsection\<open>Arrows\<close>

lemma the_cat_parallel_Arr_\<aa>I[cat_parallel_cs_intros]:
  assumes "f = \<aa>"  
  shows "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_parallel_components by simp

lemma the_cat_parallel_Arr_\<bb>I[cat_parallel_cs_intros]:
  assumes "f = \<bb>"  
  shows "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_parallel_components by simp

lemma the_cat_parallel_Arr_\<gg>I[cat_parallel_cs_intros]:
  assumes "f = \<gg>"
  shows "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_parallel_components by simp

lemma the_cat_parallel_Arr_\<ff>I[cat_parallel_cs_intros]:
  assumes "f = \<ff>"
  shows "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_parallel_components by simp

lemma the_cat_parallel_ArrE:
  assumes "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
  obtains "f = \<aa>" | "f = \<bb>" | "f = \<gg>" | "f = \<ff>" 
  using assms that unfolding the_cat_parallel_components by auto


subsubsection\<open>Domain\<close>

mk_VLambda the_cat_parallel_components(3)
  |vsv the_cat_parallel_Dom_vsv[cat_parallel_cs_intros]|
  |vdomain the_cat_parallel_Dom_vdomain[cat_parallel_cs_simps]|

lemma (in cat_parallel) the_cat_parallel_Dom_app_\<bb>[cat_parallel_cs_simps]:
  assumes "f = \<bb>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<bb>"
  unfolding the_cat_parallel_components assms by simp

lemmas [cat_parallel_cs_simps] = cat_parallel.the_cat_parallel_Dom_app_\<bb>

lemma (in cat_parallel) the_cat_parallel_Dom_app_\<gg>[cat_parallel_cs_simps]:
  assumes "f = \<gg>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<aa>"
  unfolding the_cat_parallel_components assms using cat_parallel_ineq by auto

lemmas [cat_parallel_cs_simps] = cat_parallel.the_cat_parallel_Dom_app_\<gg>

lemma (in cat_parallel) the_cat_parallel_Dom_app_\<ff>[cat_parallel_cs_simps]:
  assumes "f = \<ff>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<aa>"
  unfolding the_cat_parallel_components assms using cat_parallel_ineq by auto

lemmas [cat_parallel_cs_simps] = cat_parallel.the_cat_parallel_Dom_app_\<ff>

lemma (in cat_parallel) the_cat_parallel_Dom_app_\<aa>[cat_parallel_cs_simps]:
  assumes "f = \<aa>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<aa>"
  unfolding the_cat_parallel_components assms by auto

lemmas [cat_parallel_cs_simps] = cat_parallel.the_cat_parallel_Dom_app_\<aa>


subsubsection\<open>Codomain\<close>

mk_VLambda the_cat_parallel_components(4)
  |vsv the_cat_parallel_Cod_vsv[cat_parallel_cs_intros]|
  |vdomain the_cat_parallel_Cod_vdomain[cat_parallel_cs_simps]|

lemma (in cat_parallel) the_cat_parallel_Cod_app_\<bb>[cat_parallel_cs_simps]:
  assumes "f = \<bb>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<bb>"
  unfolding the_cat_parallel_components assms by simp

lemmas [cat_parallel_cs_simps] = cat_parallel.the_cat_parallel_Cod_app_\<bb>

lemma (in cat_parallel) the_cat_parallel_Cod_app_\<gg>[cat_parallel_cs_simps]:
  assumes "f = \<gg>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<bb>"
  unfolding the_cat_parallel_components assms using cat_parallel_ineq by auto

lemmas [cat_parallel_cs_simps] = cat_parallel.the_cat_parallel_Cod_app_\<gg>

lemma (in cat_parallel) the_cat_parallel_Cod_app_\<ff>[cat_parallel_cs_simps]:
  assumes "f = \<ff>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<bb>"
  unfolding the_cat_parallel_components assms using cat_parallel_ineq by auto

lemmas [cat_parallel_cs_simps] = cat_parallel.the_cat_parallel_Cod_app_\<ff>

lemma (in cat_parallel) the_cat_parallel_Cod_app_\<aa>[cat_parallel_cs_simps]:
  assumes "f = \<aa>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<aa>"
  unfolding the_cat_parallel_components assms by auto

lemmas [cat_parallel_cs_simps] = cat_parallel.the_cat_parallel_Cod_app_\<aa>


subsubsection\<open>Composition\<close>

mk_VLambda the_cat_parallel_components(5)
  |vsv the_cat_parallel_Comp_vsv[cat_parallel_cs_intros]|
  |vdomain the_cat_parallel_Comp_vdomain[cat_parallel_cs_simps]|
  |app the_cat_parallel_Comp_app[cat_parallel_cs_simps]|

lemma the_cat_parallel_Comp_app_\<bb>\<bb>[cat_parallel_cs_simps]:
  assumes "g = \<bb>" and "f = \<bb>"
  shows "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f"
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
    by (cs_concl cs_intro: cat_parallel_cs_intros)
  then show "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f"
    unfolding the_cat_parallel_components(5) assms 
    by (auto simp: nat_omega_simps)
qed

lemma the_cat_parallel_Comp_app_\<aa>\<aa>[cat_parallel_cs_simps]:
  assumes "g = \<aa>" and "f = \<aa>"
  shows "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f"
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
    by (cs_concl cs_intro: cat_parallel_cs_intros)
  then show "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f"
    unfolding the_cat_parallel_components(5) assms 
    by (auto simp: nat_omega_simps)
qed

lemma the_cat_parallel_Comp_app_\<bb>\<gg>[cat_parallel_cs_simps]:
  assumes "g = \<bb>" and "f = \<gg>"
  shows "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f" 
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
    by (cs_concl cs_intro: cat_parallel_cs_intros)
  then show "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f"
    unfolding the_cat_parallel_components(5) assms 
    by (auto simp: nat_omega_simps)
qed

lemma the_cat_parallel_Comp_app_\<bb>\<ff>[cat_parallel_cs_simps]:
  assumes "g = \<bb>" and "f = \<ff>"
  shows "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f" 
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
    by (cs_concl cs_intro: cat_parallel_cs_intros)
  then show "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f"
    unfolding the_cat_parallel_components(5) assms 
    by (auto simp: nat_omega_simps)
qed

lemma (in cat_parallel) the_cat_parallel_Comp_app_\<gg>\<aa>[cat_parallel_cs_simps]:
  assumes "g = \<gg>" and "f = \<aa>"
  shows "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = g" 
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
    by (cs_concl cs_intro: cat_parallel_cs_intros)
  then show "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = g"
    unfolding the_cat_parallel_components(5) assms 
    using cat_parallel_ineq
    by (auto simp: nat_omega_simps)
qed

lemma (in cat_parallel) the_cat_parallel_Comp_app_\<ff>\<aa>[cat_parallel_cs_simps]:
  assumes "g = \<ff>" and "f = \<aa>"
  shows "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = g" 
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
    by (cs_concl cs_intro: cat_parallel_cs_intros)
  then show "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = g"
    unfolding the_cat_parallel_components(5) assms 
    using cat_parallel_ineq
    by (auto simp: nat_omega_simps)
qed


subsubsection\<open>Identity\<close>

mk_VLambda the_cat_parallel_components(6)[unfolded VLambda_vid_on[symmetric]]
  |vsv the_cat_parallel_CId_vsv[cat_parallel_cs_intros]|
  |vdomain the_cat_parallel_CId_vdomain[cat_parallel_cs_simps]|
  |app the_cat_parallel_CId_app|

lemma the_cat_parallel_CId_app_\<aa>[cat_parallel_cs_simps]: 
  assumes "a = \<aa>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>CId\<rparr>\<lparr>a\<rparr> = \<aa>"
  unfolding assms by (auto simp: the_cat_parallel_CId_app)

lemma the_cat_parallel_CId_app_\<bb>[cat_parallel_cs_simps]: 
  assumes "a = \<bb>"
  shows "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>CId\<rparr>\<lparr>a\<rparr> = \<bb>"
  unfolding assms by (auto simp: the_cat_parallel_CId_app)


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma (in cat_parallel) the_cat_parallel_is_arr_\<aa>\<aa>\<aa>[cat_parallel_cs_intros]:
  assumes "a' = \<aa>" and "b' = \<aa>" and "f = \<aa>"
  shows "f : a' \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b'"
proof(intro is_arrI, unfold assms)
  show "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>\<lparr>\<aa>\<rparr> = \<aa>" "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>\<lparr>\<aa>\<rparr> = \<aa>"
    by (cs_concl cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros)+
qed (auto simp: the_cat_parallel_components)

lemma (in cat_parallel) the_cat_parallel_is_arr_\<bb>\<bb>\<bb>[cat_parallel_cs_intros]:
  assumes "a' = \<bb>" and "b' = \<bb>" and "f = \<bb>"
  shows "f : a' \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b'"
proof(intro is_arrI, unfold assms)
  show "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>\<lparr>\<bb>\<rparr> = \<bb>" "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>\<lparr>\<bb>\<rparr> = \<bb>"
    by (cs_concl cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros)+
qed (auto simp: the_cat_parallel_components)

lemma (in cat_parallel) the_cat_parallel_is_arr_\<aa>\<bb>\<gg>[cat_parallel_cs_intros]:
  assumes "a' = \<aa>" and "b' = \<bb>" and "f = \<gg>"
  shows "f : a' \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b'"
proof(intro is_arrI, unfold assms(1,2))
  from assms(3) show "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<aa>" "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<bb>"
    by (cs_concl cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros)+
qed (auto simp: the_cat_parallel_components assms(3))

lemma (in cat_parallel) the_cat_parallel_is_arr_\<aa>\<bb>\<ff>[cat_parallel_cs_intros]:
  assumes "a' = \<aa>" and "b' = \<bb>" and "f = \<ff>"
  shows "f : a' \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b'"
proof(intro is_arrI, unfold assms(1,2))
  from assms(3) show "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<aa>" "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<bb>"
    by (cs_concl cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros)+
qed (auto simp: the_cat_parallel_components assms(3))

lemma (in cat_parallel) the_cat_parallel_is_arrE:
  assumes "f' : a' \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b'"
  obtains "a' = \<aa>" and "b' = \<aa>" and "f' = \<aa>"
        | "a' = \<bb>" and "b' = \<bb>" and "f' = \<bb>"
        | "a' = \<aa>" and "b' = \<bb>" and "f' = \<gg>"
        | "a' = \<aa>" and "b' = \<bb>" and "f' = \<ff>"
proof-
  note f = is_arrD[OF assms]
  from f(1) consider (\<aa>) "f' = \<aa>" | (\<bb>) "f' = \<bb>" | (\<gg>) "f' = \<gg>" | (\<ff>) "f' = \<ff>"
    unfolding the_cat_parallel_components(2) by auto
  then show ?thesis
  proof cases
    case \<aa>
    moreover from f(2)[unfolded \<aa>, symmetric] have "a' = \<aa>"
      by (cs_prems cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros)
    moreover from f(3)[unfolded \<aa>, symmetric] have "b' = \<aa>"
      by (cs_prems cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros)
    ultimately show ?thesis using that by auto
  next
    case \<bb>
    moreover from f(2)[unfolded \<bb>, symmetric] have "a' = \<bb>"
      by (cs_prems cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros)
    moreover from f(3)[unfolded \<bb>, symmetric] have "b' = \<bb>"
      by (cs_prems cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros)
    ultimately show ?thesis using that by auto
  next
    case \<gg>
    moreover from f(2)[symmetric] \<gg> have "a' = \<aa>"
      by (cs_prems cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros)
    moreover from f(3)[symmetric] \<gg> have "b' = \<bb>"
      by (cs_prems cs_simp: cat_parallel_cs_simps)
    ultimately show ?thesis using that by auto
  next
    case \<ff>
    moreover from f(2)[symmetric] \<ff> have "a' = \<aa>"
      by (cs_prems cs_simp: cat_parallel_cs_simps cs_intro: V_cs_intros)
    moreover from f(3)[symmetric] \<ff> have "b' = \<bb>"
      by (cs_prems cs_simp: cat_parallel_cs_simps)
    ultimately show ?thesis using that by auto
  qed
qed


subsubsection\<open>\<open>\<up>\<up>\<close> is a category\<close>

lemma (in cat_parallel) finite_category_the_cat_parallel[cat_parallel_cs_intros]:
  "finite_category \<alpha> (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>)"
proof(intro finite_categoryI'' tiny_categoryI'')
  show "vfsequence (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>)" unfolding the_cat_parallel_def by simp
  show "vcard (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>) = 6\<^sub>\<nat>"
    unfolding the_cat_parallel_def by (simp_all add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>" 
    by (auto simp: the_cat_parallel_components)
  show "\<R>\<^sub>\<circ> (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>" 
    by (auto simp: the_cat_parallel_components)
  show "(gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Comp\<rparr>)) =
    (
      \<exists>g f b c a.
        gf = [g, f]\<^sub>\<circ> \<and>
        g : b \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> c \<and>
        f : a \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b
    )"
    for gf
    unfolding the_cat_parallel_Comp_vdomain
  proof
    assume prems: "gf \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
    then obtain g f where gf_def: "gf = [g, f]\<^sub>\<circ>" by auto
    from prems show 
      "\<exists>g f b c a.
        gf = [g, f]\<^sub>\<circ> \<and>
        g : b \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> c \<and>
        f : a \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b"
      unfolding gf_def
      by (*slow*)
        (
          cases rule: cat_parallel_composableE; 
          (intro exI conjI)?; 
          cs_concl_step?;
          (simp only:)?,
          all\<open>intro is_arrI, unfold the_cat_parallel_components(2)\<close>
        )
        (
          cs_concl 
            cs_simp: cat_parallel_cs_simps V_cs_simps cs_intro: V_cs_intros
        )+
  next
    assume 
      "\<exists>g f b' c' a'.
        gf = [g, f]\<^sub>\<circ> \<and>
        g : b' \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> c' \<and>
        f : a' \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b'"
    then obtain g f b c a 
      where gf_def: "gf = [g, f]\<^sub>\<circ>" 
        and g: "g : b \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> c"
        and f: "f : a \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b" 
      by clarsimp
    from g f show "gf \<in>\<^sub>\<circ> cat_parallel_composable \<aa> \<bb> \<gg> \<ff>"
      unfolding gf_def 
      by (elim the_cat_parallel_is_arrE) (auto simp: cat_parallel_cs_intros)
  qed
  show "\<D>\<^sub>\<circ> (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>CId\<rparr>) = \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>"
    by (simp add: cat_parallel_cs_simps the_cat_parallel_components)
  show "g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f : a \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> c"
    if "g : b \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b" for b c g a f
    using that
    by (elim the_cat_parallel_is_arrE; simp only:)
      (
        all\<open>
          solves\<open>simp add: cat_parallel_ineq cat_parallel_ineq[symmetric]\<close> |
          cs_concl cs_simp: cat_parallel_cs_simps 
        \<close>
      )
  show 
    "h \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = 
      h \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> (g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f)"
    if "h : c \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> d" 
      and "g : b \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> c" 
      and "f : a \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b"
    for c d h b g a f
    using that 
    by (elim the_cat_parallel_is_arrE; simp only:) (*slow*)
      (
        all\<open>
          solves\<open>simp only: cat_parallel_ineq cat_parallel_ineq[symmetric]\<close> |
          cs_concl 
            cs_simp: cat_parallel_cs_simps cs_intro: cat_parallel_cs_intros
          \<close>
      )
  show "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> a" if "a \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>" 
    for a
  proof-
    from that consider "a = \<aa>" | "a = \<bb>"
      unfolding the_cat_parallel_components(1) by auto
    then show "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> a"
      by cases
        (
          cs_concl 
            cs_simp: cat_parallel_cs_simps cs_intro: cat_parallel_cs_intros
        )+
  qed
  show "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f = f" 
    if "f : a \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b" for a b f
    using that
    by (elim the_cat_parallel_is_arrE)
      (cs_concl cs_simp: cat_parallel_cs_simps cs_intro: cat_parallel_cs_intros)
  show "f \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>CId\<rparr>\<lparr>b\<rparr> = f" 
    if "f : b \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> c" for b c f
    using that
    by (elim the_cat_parallel_is_arrE)
      (cs_concl cs_simp: cat_parallel_cs_simps cs_intro: cat_parallel_cs_intros)
  show "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by 
      (
        cs_concl
          cs_simp: the_cat_parallel_components nat_omega_simps 
          cs_intro: V_cs_intros cat_parallel_cs_intros
      )
  show "vfinite (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>)" "vfinite (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>)"
    unfolding the_cat_parallel_components by auto
qed 
  (
    cs_concl 
      cs_simp: 
        nat_omega_simps cat_parallel_cs_simps the_cat_parallel_components(2) 
      cs_intro: 
        cat_cs_intros 
        cat_parallel_cs_intros 
        V_cs_intros 
        Limit_succ_in_VsetI
  )+

lemmas [cat_parallel_cs_intros] = cat_parallel.finite_category_the_cat_parallel


subsubsection\<open>Opposite parallel category\<close>

lemma (in cat_parallel) op_cat_the_cat_parallel[cat_op_simps]: 
  "op_cat (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>) = \<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>"
proof(rule cat_eqI)
  interpret \<bb>\<aa>: cat_parallel \<alpha> \<bb> \<aa> \<ff> \<gg> by (rule cat_parallel_op) 
  show \<bb>\<aa>: "category \<alpha> (\<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>)"
    by (cs_concl cs_intro: cat_small_cs_intros cat_parallel_cs_intros)
  show \<aa>\<bb>: "category \<alpha> (op_cat (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>))" 
    by 
      (
        cs_concl 
          cs_intro: cat_small_cs_intros cat_op_intros cat_parallel_cs_intros
      )
  interpret \<bb>\<aa>: category \<alpha> \<open>\<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>\<close> by (rule \<bb>\<aa>)
  interpret \<aa>\<bb>: category \<alpha> \<open>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<close>
    by (cs_concl cs_intro: cat_small_cs_intros cat_parallel_cs_intros)
  show "op_cat (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>)\<lparr>Comp\<rparr> = \<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>\<lparr>Comp\<rparr>"
  proof(rule vsv_eqI)
    show "vsv (op_cat (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>)\<lparr>Comp\<rparr>)"
      unfolding op_cat_components by (rule fflip_vsv)
    show "vsv (\<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>\<lparr>Comp\<rparr>)"
      by (cs_concl cs_intro: cat_parallel_cs_intros)
    show [cat_op_simps]: 
      "\<D>\<^sub>\<circ> (op_cat (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>)\<lparr>Comp\<rparr>) = \<D>\<^sub>\<circ> (\<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>\<lparr>Comp\<rparr>)"
      by 
        (
          cs_concl 
            cs_simp: 
              cat_parallel_composable_fconverse
              op_cat_components(5) 
              vdomain_fflip 
              cat_parallel_cs_simps 
            cs_intro: cat_cs_intros
        )
    fix gf assume "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (op_cat (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>)\<lparr>Comp\<rparr>)"
    then have "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>\<lparr>Comp\<rparr>)" unfolding cat_op_simps by simp
    then obtain g f a b c 
      where gf_def: "gf = [g, f]\<^sub>\<circ>" 
        and g: "g : b \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>\<^esub> c"
        and f: "f : a \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>\<^esub> b"
      by auto
    from g f show "op_cat (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>)\<lparr>Comp\<rparr>\<lparr>gf\<rparr> = \<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>\<lparr>Comp\<rparr>\<lparr>gf\<rparr>"
      unfolding gf_def
      by (elim \<bb>\<aa>.the_cat_parallel_is_arrE)
        (
          simp add: cat_parallel_cs_intros | 
          cs_concl 
            cs_simp: cat_op_simps cat_parallel_cs_simps 
            cs_intro: cat_cs_intros cat_parallel_cs_intros
        )+
  qed
  show "op_cat (\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>)\<lparr>CId\<rparr> = \<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>\<lparr>CId\<rparr>"
  proof(unfold cat_op_simps, rule vsv_eqI, unfold cat_parallel_cs_simps)  
    fix a assume "a \<in>\<^sub>\<circ> set {\<aa>, \<bb>}"
    then consider "a = \<aa>" | "a = \<bb>" by auto
    then show "\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>CId\<rparr>\<lparr>a\<rparr> = \<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
      by cases (cs_concl cs_simp: cat_parallel_cs_simps)+
  qed auto
qed (auto simp: the_cat_parallel_components op_cat_components)

lemmas [cat_op_simps] = cat_parallel.op_cat_the_cat_parallel



subsection\<open>Parallel functor\<close>


subsubsection\<open>Background\<close>


text\<open>
The concept of a parallel functor is introduced as a convenient abstraction
for the definition of the equalizers and co-equalizers (e.g., see
Chapter III-3 and Chapter III-4 in \cite{mac_lane_categories_2010}).
\<close>


subsubsection\<open>Local assumptions for the parallel functor\<close>

locale cf_parallel = cat_parallel \<alpha> \<aa> \<bb> \<gg> \<ff> + category \<alpha> \<CC> 
  for \<alpha> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>' \<CC> :: V +
  assumes cf_parallel_\<gg>'[cat_parallel_cs_intros]: "\<gg>' : \<aa>' \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>'"
    and cf_parallel_\<ff>'[cat_parallel_cs_intros]: "\<ff>' : \<aa>' \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>'"

lemma (in cf_parallel) cf_parallel_\<gg>''[cat_parallel_cs_intros]:
  assumes "a = \<aa>'" and "b = \<bb>'"
  shows "\<gg>' : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_parallel_\<gg>')

lemma (in cf_parallel) cf_parallel_\<gg>'''[cat_parallel_cs_intros]:
  assumes "g = \<gg>'" and "b = \<bb>'"
  shows "g : \<aa>' \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_parallel_\<gg>')

lemma (in cf_parallel) cf_parallel_\<gg>''''[cat_parallel_cs_intros]:
  assumes "g = \<gg>'" and "a = \<aa>'"
  shows "g : a \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>'"
  unfolding assms by (rule cf_parallel_\<gg>')

lemma (in cf_parallel) cf_parallel_\<ff>''[cat_parallel_cs_intros]:
  assumes "a = \<aa>'" and "b = \<bb>'"
  shows "\<ff>' : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_parallel_\<ff>') 

lemma (in cf_parallel) cf_parallel_\<ff>'''[cat_parallel_cs_intros]:
  assumes "f = \<ff>'" and "b = \<bb>'"
  shows "f : \<aa>' \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_parallel_\<ff>')

lemma (in cf_parallel) cf_parallel_\<ff>''''[cat_parallel_cs_intros]:
  assumes "f = \<ff>'" and "a = \<aa>'"
  shows "f : a \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>'"
  unfolding assms by (rule cf_parallel_\<ff>') 


text\<open>Rules.\<close>

lemma (in cf_parallel) cf_parallel_axioms[cat_parallel_cs_intros]:
  assumes "\<alpha>' = \<alpha>" 
    and "a = \<aa>" 
    and "b = \<bb>" 
    and "g = \<gg>" 
    and "f = \<ff>" 
    and "a' = \<aa>'" 
    and "b' = \<bb>'" 
    and "g' = \<gg>'" 
    and "f' = \<ff>'" 
  shows "cf_parallel \<alpha>' a b g f a' b' g' f' \<CC>"
  unfolding assms by (rule cf_parallel_axioms)

mk_ide rf cf_parallel_def[unfolded cf_parallel_axioms_def]
  |intro cf_parallelI|
  |dest cf_parallelD[dest]|
  |elim cf_parallelE[elim]|

lemmas [cat_parallel_cs_intros] = cf_parallelD(1,2)


text\<open>Duality.\<close>

lemma (in cf_parallel) cf_parallel_op[cat_op_intros]: 
  "cf_parallel \<alpha> \<bb> \<aa> \<ff> \<gg> \<bb>' \<aa>' \<ff>' \<gg>' (op_cat \<CC>)"
  by (intro cf_parallelI, unfold cat_op_simps)
    (
      cs_concl cs_simp: cs_intro: 
        cat_parallel_cs_intros cat_cs_intros cat_op_intros
    )

lemmas [cat_op_intros] = cf_parallel.cf_parallel_op


subsubsection\<open>Definition and elementary properties\<close>

definition the_cf_parallel :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" 
  (\<open>\<up>\<up>\<rightarrow>\<up>\<up>\<close>)
  where "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>' =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>. (a = \<aa> ? \<aa>' : \<bb>')),
      (
        \<lambda>f\<in>\<^sub>\<circ>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>.
          (
           if f = \<aa> \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>'\<rparr>
            | f = \<bb> \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>'\<rparr>
            | f = \<gg> \<Rightarrow> \<gg>'
            | otherwise \<Rightarrow> \<ff>'
          )
      ),
      \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>,
      \<CC>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma the_cf_parallel_components:
  shows "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr> =
      (\<lambda>a\<in>\<^sub>\<circ>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>. (a = \<aa> ? \<aa>' : \<bb>'))"
    and "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr> =
      (
        \<lambda>f\<in>\<^sub>\<circ>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>.
          (
           if f = \<aa> \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>'\<rparr>
            | f = \<bb> \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>'\<rparr>
            | f = \<gg> \<Rightarrow> \<gg>'
            | otherwise \<Rightarrow> \<ff>'
          )
      )"
    and [cat_parallel_cs_simps]: 
      "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>HomDom\<rparr> = \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>"
    and [cat_parallel_cs_simps]: 
      "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>HomCod\<rparr> = \<CC>"
  unfolding the_cf_parallel_def dghm_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda the_cf_parallel_components(1)
  |vsv the_the_cf_parallel_ObjMap_vsv[cat_parallel_cs_intros]|
  |vdomain the_cf_parallel_ObjMap_vdomain[cat_parallel_cs_simps]|
  |app the_cf_parallel_ObjMap_app|

lemma (in cf_parallel) the_cf_parallel_ObjMap_app_\<aa>[cat_parallel_cs_simps]:
  assumes "x = \<aa>"
  shows "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> = \<aa>'"
  by 
    (
      cs_concl 
        cs_simp: 
          assms the_cf_parallel_ObjMap_app cat_parallel_cs_simps V_cs_simps 
        cs_intro: cat_parallel_cs_intros
    )

lemmas [cat_parallel_cs_simps] = cf_parallel.the_cf_parallel_ObjMap_app_\<aa>

lemma (in cf_parallel) the_cf_parallel_ObjMap_app_\<bb>[cat_parallel_cs_simps]:
  assumes "x = \<bb>"
  shows "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> = \<bb>'"
  using cat_parallel_ineq
  by 
    (
      cs_concl 
        cs_simp: 
          assms the_cf_parallel_ObjMap_app cat_parallel_cs_simps V_cs_simps 
        cs_intro: cat_parallel_cs_intros
    )

lemmas [cat_parallel_cs_simps] = cf_parallel.the_cf_parallel_ObjMap_app_\<bb>

lemma (in cf_parallel) the_cf_parallel_ObjMap_vrange:
  "\<R>\<^sub>\<circ> (\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  unfolding the_cf_parallel_components
proof(intro vrange_VLambda_vsubset)
  fix a assume "a \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>"
  then consider "a = \<aa>" | "a = \<bb>" unfolding the_cat_parallel_components by auto
  then show "(a = \<aa> ? \<aa>' : \<bb>') \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by (auto intro: cat_cs_intros cat_parallel_cs_intros)
qed


subsubsection\<open>Arrow map\<close>

mk_VLambda the_cf_parallel_components(2)
  |vsv the_cf_parallel_ArrMap_vsv[cat_parallel_cs_intros]|
  |vdomain the_cf_parallel_ArrMap_vdomain[cat_parallel_cs_simps]|
  |app the_cf_parallel_ArrMap_app|

lemma (in cf_parallel) the_cf_parallel_ArrMap_app_\<gg>[cat_parallel_cs_simps]:
  assumes "f = \<gg>"
  shows "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<gg>'"
proof-
  from assms have "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
    by (cs_concl cs_intro: cat_parallel_cs_intros a_in_succ_xI)
  from this show ?thesis
    using cat_parallel_ineq
    by (elim the_cat_parallel_ArrE; simp only: assms) 
      (auto simp: the_cf_parallel_ArrMap_app)
qed

lemmas [cat_parallel_cs_simps] = cf_parallel.the_cf_parallel_ArrMap_app_\<gg>

lemma (in cf_parallel) the_cf_parallel_ArrMap_app_\<ff>[cat_parallel_cs_simps]:
  assumes "f = \<ff>"
  shows "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<ff>'"
proof-
  from assms have "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
    by (cs_concl cs_intro: cat_parallel_cs_intros a_in_succ_xI)
  from this show ?thesis
    using cat_parallel_ineq
    by (elim the_cat_parallel_ArrE; simp only: assms) 
      (auto simp: the_cf_parallel_ArrMap_app)
qed

lemmas [cat_parallel_cs_simps] = cf_parallel.the_cf_parallel_ArrMap_app_\<ff>

lemma (in cf_parallel) the_cf_parallel_ArrMap_app_\<aa>[cat_parallel_cs_simps]:
  assumes "f = \<aa>"
  shows "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>'\<rparr>"
proof-
  from assms have "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
    by (cs_concl cs_intro: cat_parallel_cs_intros a_in_succ_xI)
  from this show ?thesis
    using cat_parallel_ineq
    by (elim the_cat_parallel_ArrE; simp only: assms) 
      (auto simp: the_cf_parallel_ArrMap_app)
qed

lemmas [cat_parallel_cs_simps] = cf_parallel.the_cf_parallel_ArrMap_app_\<aa>

lemma (in cf_parallel) the_cf_parallel_ArrMap_app_\<bb>[cat_parallel_cs_simps]:
  assumes "f = \<bb>"
  shows "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>'\<rparr>"
proof-
  from assms have "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
    by (cs_concl cs_intro: cat_parallel_cs_intros a_in_succ_xI)
  from this show ?thesis
    using cat_parallel_ineq
    by (elim the_cat_parallel_ArrE; simp only: assms) 
      (auto simp: the_cf_parallel_ArrMap_app)
qed

lemmas [cat_parallel_cs_simps] = cf_parallel.the_cf_parallel_ArrMap_app_\<bb>

lemma (in cf_parallel) the_cf_parallel_ArrMap_vrange:
  "\<R>\<^sub>\<circ> (\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof(intro vsv.vsv_vrange_vsubset, unfold cat_parallel_cs_simps)
  show "vsv (\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>)" 
    by (cs_intro_step cat_parallel_cs_intros)
  fix f assume "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
  then show "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    by (elim the_cat_parallel_ArrE; simp only:)
      (
        cs_concl
          cs_simp: cat_parallel_cs_simps  
          cs_intro: cat_cs_intros cat_parallel_cs_intros 
      )+
qed


subsubsection\<open>Parallel functor is a functor\<close>

lemma (in cf_parallel) cf_parallel_the_cf_parallel_is_tm_functor:
  "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>' : \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_functor.cf_is_tm_functor_if_HomDom_finite_category is_functorI')
  show "vfsequence (\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>')" 
    unfolding the_cf_parallel_def by auto
  show "vcard (\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>') = 4\<^sub>\<nat>"
    unfolding the_cf_parallel_def by (simp add: nat_omega_simps)
  show "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> :
    \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub>
    \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    if "f : a \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b" for a b f
    using that
    by (cases rule: the_cat_parallel_is_arrE; simp only:)
      (
        cs_concl
          cs_simp: cat_parallel_cs_simps
          cs_intro: cat_cs_intros cat_parallel_cs_intros
      )+
  show
    "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> f\<rparr> =
      \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
      \<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
    if "g : b \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<^esub> b" for b c g a f
    using that
    by (elim the_cat_parallel_is_arrE) (*very slow*)
      (
        all\<open>simp only:\<close>, 
        all\<open>
          solves\<open>simp add: cat_parallel_ineq cat_parallel_ineq[symmetric]\<close> | 
          cs_concl 
            cs_simp: cat_cs_simps cat_parallel_cs_simps 
            cs_intro: cat_cs_intros cat_parallel_cs_intros
          \<close>
      )
  show 
    "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> =
      \<CC>\<lparr>CId\<rparr>\<lparr>\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
    if "c \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>" for c
    using that
    by (elim the_cat_parallel_ObjE; simp only:)
      (cs_concl cs_simp: cat_parallel_cs_simps)+
qed 
  (
    cs_concl 
      cs_simp: cat_parallel_cs_simps 
      cs_intro: 
        the_cf_parallel_ObjMap_vrange 
        cat_parallel_cs_intros 
        cat_cs_intros 
        cat_small_cs_intros
  )+

lemma (in cf_parallel) cf_parallel_the_cf_parallel_is_tm_functor':
  assumes "\<AA>' = \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>" and "\<CC>' = \<CC>"
  shows "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule cf_parallel_the_cf_parallel_is_tm_functor)

lemmas [cat_parallel_cs_intros] = 
  cf_parallel.cf_parallel_the_cf_parallel_is_tm_functor'


subsubsection\<open>Opposite parallel functor\<close>

lemma (in cf_parallel) cf_parallel_the_cf_parallel_op[cat_op_simps]:
  "op_cf (\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>') = \<up>\<up>\<rightarrow>\<up>\<up> (op_cat \<CC>) \<bb> \<aa> \<ff> \<gg> \<bb>' \<aa>' \<ff>' \<gg>'"
proof-
  interpret \<up>: is_tm_functor \<alpha> \<open>\<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<close> \<CC> \<open>\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<close>
    by (rule cf_parallel_the_cf_parallel_is_tm_functor)
  show ?thesis
  proof
    (
      rule cf_eqI[of \<alpha> \<open>\<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>\<close> \<open>op_cat \<CC>\<close> _ \<open>\<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg>\<close> \<open>op_cat \<CC>\<close>], 
      unfold cat_op_simps
    )
    show "op_cf (\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>') : \<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
      by (cs_concl cs_simp: cat_op_simps cs_intro: cat_op_intros)
    show "\<up>\<up>\<rightarrow>\<up>\<up> (op_cat \<CC>) \<bb> \<aa> \<ff> \<gg> \<bb>' \<aa>' \<ff>' \<gg>' : \<up>\<up>\<^sub>C \<bb> \<aa> \<ff> \<gg> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
      by 
        (
          cs_concl 
            cs_intro: cat_op_intros cat_small_cs_intros cat_parallel_cs_intros
        )
    show  
      "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr> = 
        \<up>\<up>\<rightarrow>\<up>\<up> (op_cat \<CC>) \<bb> \<aa> \<ff> \<gg> \<bb>' \<aa>' \<ff>' \<gg>'\<lparr>ObjMap\<rparr>"
    proof
      (
        rule vsv_eqI;
        (intro cat_parallel_cs_intros)?; 
        unfold cat_parallel_cs_simps
      )
      fix a assume "a \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Obj\<rparr>"
      then consider "a = \<aa>" | "a = \<bb>" by (elim the_cat_parallel_ObjE) simp
      then show 
        "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> =
          \<up>\<up>\<rightarrow>\<up>\<up> (op_cat \<CC>) \<bb> \<aa> \<ff> \<gg> \<bb>' \<aa>' \<ff>' \<gg>'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by cases
          (
            cs_concl 
              cs_simp: cat_parallel_cs_simps 
              cs_intro: cat_parallel_cs_intros cat_op_intros
          )
    qed (auto simp: the_cat_parallel_components)
    show 
      "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff> \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr> = 
        \<up>\<up>\<rightarrow>\<up>\<up> (op_cat \<CC>) \<bb> \<aa> \<ff> \<gg> \<bb>' \<aa>' \<ff>' \<gg>'\<lparr>ArrMap\<rparr>"
    proof
      (
        rule vsv_eqI; 
        (intro cat_parallel_cs_intros)?; 
        unfold cat_parallel_cs_simps
      )
      fix f assume "f \<in>\<^sub>\<circ> \<up>\<up>\<^sub>C \<aa> \<bb> \<gg> \<ff>\<lparr>Arr\<rparr>"
      then consider "f = \<aa>" | "f = \<bb>" | "f = \<gg>" | "f = \<ff>" 
        by (elim the_cat_parallel_ArrE) simp
      then show 
        "\<up>\<up>\<rightarrow>\<up>\<up> \<CC> \<aa> \<bb> \<gg> \<ff>  \<aa>' \<bb>' \<gg>' \<ff>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
          \<up>\<up>\<rightarrow>\<up>\<up> (op_cat \<CC>) \<bb> \<aa> \<ff> \<gg> \<bb>' \<aa>' \<ff>' \<gg>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
        by cases
          (
            cs_concl 
              cs_simp: cat_parallel_cs_simps cat_op_simps 
              cs_intro: cat_parallel_cs_intros cat_op_intros
          )+
    qed (auto simp: the_cat_parallel_components)
  qed simp_all
qed

lemmas [cat_op_simps] = cf_parallel.cf_parallel_the_cf_parallel_op

text\<open>\newpage\<close>

end