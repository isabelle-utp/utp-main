(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>\<rightarrow>\<bullet>\<leftarrow>\<close> and \<open>\<leftarrow>\<bullet>\<rightarrow>\<close>\<close>
theory CZH_ECAT_SS
  imports CZH_ECAT_Small_Functor
begin



subsection\<open>Background\<close>


text\<open>
General information about \<open>\<rightarrow>\<bullet>\<leftarrow>\<close> and \<open>\<leftarrow>\<bullet>\<rightarrow>\<close> (also known as 
cospans and spans, respectively) can be found in in Chapters III-3 and III-4 
in \cite{mac_lane_categories_2010}, as well as 
nLab \cite{noauthor_nlab_nodate}\footnote{
\url{https://ncatlab.org/nlab/show/cospan}
}\footnote{\url{https://ncatlab.org/nlab/show/span}}.
\<close>

named_theorems cat_ss_cs_simps
named_theorems cat_ss_cs_intros

named_theorems cat_ss_elem_simps

definition \<oo>\<^sub>S\<^sub>S where [cat_ss_elem_simps]: "\<oo>\<^sub>S\<^sub>S = 0"
definition \<aa>\<^sub>S\<^sub>S where [cat_ss_elem_simps]: "\<aa>\<^sub>S\<^sub>S = 1\<^sub>\<nat>"
definition \<bb>\<^sub>S\<^sub>S where [cat_ss_elem_simps]: "\<bb>\<^sub>S\<^sub>S = 2\<^sub>\<nat>"
definition \<gg>\<^sub>S\<^sub>S where [cat_ss_elem_simps]: "\<gg>\<^sub>S\<^sub>S = 3\<^sub>\<nat>"
definition \<ff>\<^sub>S\<^sub>S where [cat_ss_elem_simps]: "\<ff>\<^sub>S\<^sub>S = 4\<^sub>\<nat>"

lemma cat_ss_ineq:
  shows cat_ss_\<aa>\<bb>[cat_ss_cs_intros]: "\<aa>\<^sub>S\<^sub>S \<noteq> \<bb>\<^sub>S\<^sub>S"
    and cat_ss_\<aa>\<oo>[cat_ss_cs_intros]: "\<aa>\<^sub>S\<^sub>S \<noteq> \<oo>\<^sub>S\<^sub>S"
    and cat_ss_\<bb>\<oo>[cat_ss_cs_intros]: "\<bb>\<^sub>S\<^sub>S \<noteq> \<oo>\<^sub>S\<^sub>S"
    and cat_ss_\<gg>\<ff>[cat_ss_cs_intros]: "\<gg>\<^sub>S\<^sub>S \<noteq> \<ff>\<^sub>S\<^sub>S"
    and cat_ss_\<gg>\<aa>[cat_ss_cs_intros]: "\<gg>\<^sub>S\<^sub>S \<noteq> \<aa>\<^sub>S\<^sub>S"
    and cat_ss_\<gg>\<bb>[cat_ss_cs_intros]: "\<gg>\<^sub>S\<^sub>S \<noteq> \<bb>\<^sub>S\<^sub>S"
    and cat_ss_\<gg>\<oo>[cat_ss_cs_intros]: "\<gg>\<^sub>S\<^sub>S \<noteq> \<oo>\<^sub>S\<^sub>S"
    and cat_ss_\<ff>\<aa>[cat_ss_cs_intros]: "\<ff>\<^sub>S\<^sub>S \<noteq> \<aa>\<^sub>S\<^sub>S"
    and cat_ss_\<ff>\<bb>[cat_ss_cs_intros]: "\<ff>\<^sub>S\<^sub>S \<noteq> \<bb>\<^sub>S\<^sub>S"
    and cat_ss_\<ff>\<oo>[cat_ss_cs_intros]: "\<ff>\<^sub>S\<^sub>S \<noteq> \<oo>\<^sub>S\<^sub>S"
  unfolding cat_ss_elem_simps by simp_all

lemma (in \<Z>) 
  shows cat_ss_\<aa>[cat_ss_cs_intros]: "\<aa>\<^sub>S\<^sub>S \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_ss_\<bb>[cat_ss_cs_intros]: "\<bb>\<^sub>S\<^sub>S \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_ss_\<oo>[cat_ss_cs_intros]: "\<oo>\<^sub>S\<^sub>S \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_ss_\<gg>[cat_ss_cs_intros]: "\<gg>\<^sub>S\<^sub>S \<in>\<^sub>\<circ> Vset \<alpha>"
    and cat_ss_\<ff>[cat_ss_cs_intros]: "\<ff>\<^sub>S\<^sub>S \<in>\<^sub>\<circ> Vset \<alpha>"
  unfolding cat_ss_elem_simps by simp_all



subsection\<open>Composable arrows in \<open>\<rightarrow>\<bullet>\<leftarrow>\<close> and \<open>\<leftarrow>\<bullet>\<rightarrow>\<close>\<close>

abbreviation cat_scospan_composable :: V
  where "cat_scospan_composable \<equiv> 
    (set {\<oo>\<^sub>S\<^sub>S} \<times>\<^sub>\<bullet> set {\<oo>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S}) \<union>\<^sub>\<circ> 
    (set {\<gg>\<^sub>S\<^sub>S, \<aa>\<^sub>S\<^sub>S} \<times>\<^sub>\<bullet> set {\<aa>\<^sub>S\<^sub>S}) \<union>\<^sub>\<circ> 
    (set {\<ff>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S} \<times>\<^sub>\<bullet> set {\<bb>\<^sub>S\<^sub>S})"

abbreviation cat_sspan_composable :: V
  where "cat_sspan_composable \<equiv> (cat_scospan_composable)\<inverse>\<^sub>\<bullet>"


text\<open>Rules.\<close>

lemma cat_scospan_composable_\<oo>\<oo>[cat_ss_cs_intros]:
  assumes "g = \<oo>\<^sub>S\<^sub>S" and "f = \<oo>\<^sub>S\<^sub>S"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable"
  using assms by auto

lemma cat_scospan_composable_\<oo>\<gg>[cat_ss_cs_intros]:
  assumes "g = \<oo>\<^sub>S\<^sub>S" and "f = \<gg>\<^sub>S\<^sub>S"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable"
  using assms by auto

lemma cat_scospan_composable_\<oo>\<ff>[cat_ss_cs_intros]:
  assumes "g = \<oo>\<^sub>S\<^sub>S" and "f = \<ff>\<^sub>S\<^sub>S"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable"
  using assms by auto

lemma cat_scospan_composable_\<gg>\<aa>[cat_ss_cs_intros]:
  assumes "g = \<gg>\<^sub>S\<^sub>S" and "f = \<aa>\<^sub>S\<^sub>S"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable"
  using assms by auto

lemma cat_scospan_composable_\<ff>\<bb>[cat_ss_cs_intros]:
  assumes "g = \<ff>\<^sub>S\<^sub>S" and "f = \<bb>\<^sub>S\<^sub>S"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable"
  using assms by auto

lemma cat_scospan_composable_\<aa>\<aa>[cat_ss_cs_intros]:
  assumes "g = \<aa>\<^sub>S\<^sub>S" and "f = \<aa>\<^sub>S\<^sub>S"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable"
  using assms by auto

lemma cat_scospan_composable_\<bb>\<bb>[cat_ss_cs_intros]:
  assumes "g = \<bb>\<^sub>S\<^sub>S" and "f = \<bb>\<^sub>S\<^sub>S"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable"
  using assms by auto

lemma cat_scospan_composableE:
  assumes "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable"
  obtains "g = \<oo>\<^sub>S\<^sub>S" and "f = \<oo>\<^sub>S\<^sub>S" 
        | "g = \<oo>\<^sub>S\<^sub>S" and "f = \<gg>\<^sub>S\<^sub>S"
        | "g = \<oo>\<^sub>S\<^sub>S" and "f = \<ff>\<^sub>S\<^sub>S"
        | "g = \<gg>\<^sub>S\<^sub>S" and "f = \<aa>\<^sub>S\<^sub>S"
        | "g = \<ff>\<^sub>S\<^sub>S" and "f = \<bb>\<^sub>S\<^sub>S"
        | "g = \<aa>\<^sub>S\<^sub>S" and "f = \<aa>\<^sub>S\<^sub>S"
        | "g = \<bb>\<^sub>S\<^sub>S" and "f = \<bb>\<^sub>S\<^sub>S"
  using assms that by auto

lemma cat_sspan_composable_\<oo>\<oo>[cat_ss_cs_intros]:
  assumes "g = \<oo>\<^sub>S\<^sub>S" and "f = \<oo>\<^sub>S\<^sub>S"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable"
  using assms by auto

lemma cat_sspan_composable_\<gg>\<oo>[cat_ss_cs_intros]:
  assumes "g = \<gg>\<^sub>S\<^sub>S" and "f = \<oo>\<^sub>S\<^sub>S"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable"
  using assms by auto

lemma cat_sspan_composable_\<ff>\<oo>[cat_ss_cs_intros]:
  assumes "g = \<ff>\<^sub>S\<^sub>S" and "f = \<oo>\<^sub>S\<^sub>S"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable"
  using assms by auto

lemma cat_sspan_composable_\<aa>\<gg>[cat_ss_cs_intros]:
  assumes "g = \<aa>\<^sub>S\<^sub>S" and "f = \<gg>\<^sub>S\<^sub>S"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable"
  using assms by auto

lemma cat_sspan_composable_\<bb>\<ff>[cat_ss_cs_intros]:
  assumes "g = \<bb>\<^sub>S\<^sub>S" and "f = \<ff>\<^sub>S\<^sub>S"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable"
  using assms by auto

lemma cat_sspan_composable_\<aa>\<aa>[cat_ss_cs_intros]:
  assumes "g = \<aa>\<^sub>S\<^sub>S" and "f = \<aa>\<^sub>S\<^sub>S"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable"
  using assms by auto

lemma cat_sspan_composable_\<bb>\<bb>[cat_ss_cs_intros]:
  assumes "g = \<bb>\<^sub>S\<^sub>S" and "f = \<bb>\<^sub>S\<^sub>S"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable"
  using assms by auto

lemma cat_sspan_composableE:
  assumes "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable"
  obtains "g = \<oo>\<^sub>S\<^sub>S" and "f = \<oo>\<^sub>S\<^sub>S" 
        | "g = \<gg>\<^sub>S\<^sub>S" and "f = \<oo>\<^sub>S\<^sub>S"
        | "g = \<ff>\<^sub>S\<^sub>S" and "f = \<oo>\<^sub>S\<^sub>S"
        | "g = \<aa>\<^sub>S\<^sub>S" and "f = \<gg>\<^sub>S\<^sub>S"
        | "g = \<bb>\<^sub>S\<^sub>S" and "f = \<ff>\<^sub>S\<^sub>S"
        | "g = \<aa>\<^sub>S\<^sub>S" and "f = \<aa>\<^sub>S\<^sub>S"
        | "g = \<bb>\<^sub>S\<^sub>S" and "f = \<bb>\<^sub>S\<^sub>S"
  using assms that by auto



subsection\<open>Categories \<open>\<rightarrow>\<bullet>\<leftarrow>\<close> and \<open>\<leftarrow>\<bullet>\<rightarrow>\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter III-3 and Chapter III-4 in \cite{mac_lane_categories_2010}.\<close>

definition the_cat_scospan :: V (\<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close>)
  where "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C =
    [
      set {\<aa>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S},
      set {\<aa>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S},
      (
        \<lambda>x\<in>\<^sub>\<circ>set {\<aa>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S}. 
         if x = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<aa>\<^sub>S\<^sub>S
          | x = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<bb>\<^sub>S\<^sub>S
          | x = \<gg>\<^sub>S\<^sub>S \<Rightarrow> \<aa>\<^sub>S\<^sub>S
          | x = \<ff>\<^sub>S\<^sub>S \<Rightarrow> \<bb>\<^sub>S\<^sub>S
          | otherwise \<Rightarrow> \<oo>\<^sub>S\<^sub>S
      ),
      (
        \<lambda>x\<in>\<^sub>\<circ>set {\<aa>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S}. 
         if x = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<aa>\<^sub>S\<^sub>S
          | x = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<bb>\<^sub>S\<^sub>S
          | otherwise \<Rightarrow> \<oo>\<^sub>S\<^sub>S
      ),
      (
        \<lambda>gf\<in>\<^sub>\<circ>cat_scospan_composable. 
         if gf = [\<oo>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S]\<^sub>\<circ> \<Rightarrow> \<gg>\<^sub>S\<^sub>S
          | gf = [\<oo>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S]\<^sub>\<circ> \<Rightarrow> \<ff>\<^sub>S\<^sub>S
          | otherwise \<Rightarrow> gf\<lparr>0\<rparr>
      ),
      vid_on (set {\<aa>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S})
    ]\<^sub>\<circ>"

definition the_cat_sspan :: V (\<open>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<close>)
  where "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C =
    [
      set {\<aa>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S},
      set {\<aa>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S},
      (
        \<lambda>x\<in>\<^sub>\<circ>set {\<aa>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S}. 
         if x = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<aa>\<^sub>S\<^sub>S
          | x = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<bb>\<^sub>S\<^sub>S
          | otherwise \<Rightarrow> \<oo>\<^sub>S\<^sub>S
      ),
      (
        \<lambda>x\<in>\<^sub>\<circ>set {\<aa>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S}. 
         if x = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<aa>\<^sub>S\<^sub>S
          | x = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<bb>\<^sub>S\<^sub>S
          | x = \<gg>\<^sub>S\<^sub>S \<Rightarrow> \<aa>\<^sub>S\<^sub>S
          | x = \<ff>\<^sub>S\<^sub>S \<Rightarrow> \<bb>\<^sub>S\<^sub>S
          | otherwise \<Rightarrow> \<oo>\<^sub>S\<^sub>S
      ),
      (
        \<lambda>gf\<in>\<^sub>\<circ>cat_sspan_composable. 
         if gf = [\<aa>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S]\<^sub>\<circ> \<Rightarrow> \<gg>\<^sub>S\<^sub>S
          | gf = [\<bb>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S]\<^sub>\<circ> \<Rightarrow> \<ff>\<^sub>S\<^sub>S
          | otherwise \<Rightarrow> gf\<lparr>0\<rparr>
      ),
      vid_on (set {\<aa>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S})
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma the_cat_scospan_components: 
  shows "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr> = set {\<aa>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S}"
    and "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Arr\<rparr> = set {\<aa>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S}"
    and "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Dom\<rparr> = 
      (
        \<lambda>x\<in>\<^sub>\<circ>set {\<aa>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S}. 
         if x = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<aa>\<^sub>S\<^sub>S
          | x = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<bb>\<^sub>S\<^sub>S
          | x = \<gg>\<^sub>S\<^sub>S \<Rightarrow> \<aa>\<^sub>S\<^sub>S
          | x = \<ff>\<^sub>S\<^sub>S \<Rightarrow> \<bb>\<^sub>S\<^sub>S
          | otherwise \<Rightarrow> \<oo>\<^sub>S\<^sub>S
      )"
    and "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Cod\<rparr> = 
      (
        \<lambda>x\<in>\<^sub>\<circ>set {\<aa>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S}. 
         if x = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<aa>\<^sub>S\<^sub>S
          | x = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<bb>\<^sub>S\<^sub>S
          | otherwise \<Rightarrow> \<oo>\<^sub>S\<^sub>S
      )"
    and "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Comp\<rparr> =
      (
        \<lambda>gf\<in>\<^sub>\<circ>cat_scospan_composable. 
         if gf = [\<oo>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S]\<^sub>\<circ> \<Rightarrow> \<gg>\<^sub>S\<^sub>S
          | gf = [\<oo>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S]\<^sub>\<circ> \<Rightarrow> \<ff>\<^sub>S\<^sub>S
          | otherwise \<Rightarrow> gf\<lparr>0\<rparr>
      )"
    and "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>CId\<rparr> = vid_on (set {\<aa>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S})"
  unfolding the_cat_scospan_def dg_field_simps by (simp_all add: nat_omega_simps)

lemma the_cat_sspan_components: 
  shows "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Obj\<rparr> = set {\<aa>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S}"
    and "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Arr\<rparr> = set {\<aa>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S}"
    and "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Dom\<rparr> =
      (
        \<lambda>x\<in>\<^sub>\<circ>set {\<aa>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S}. 
         if x = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<aa>\<^sub>S\<^sub>S
          | x = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<bb>\<^sub>S\<^sub>S
          | otherwise \<Rightarrow> \<oo>\<^sub>S\<^sub>S
      )"
    and "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Cod\<rparr> =
      (
        \<lambda>x\<in>\<^sub>\<circ>set {\<aa>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S}. 
         if x = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<aa>\<^sub>S\<^sub>S
          | x = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<bb>\<^sub>S\<^sub>S
          | x = \<gg>\<^sub>S\<^sub>S \<Rightarrow> \<aa>\<^sub>S\<^sub>S
          | x = \<ff>\<^sub>S\<^sub>S \<Rightarrow> \<bb>\<^sub>S\<^sub>S
          | otherwise \<Rightarrow> \<oo>\<^sub>S\<^sub>S
      )"
    and "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Comp\<rparr> =
      (
        \<lambda>gf\<in>\<^sub>\<circ>cat_sspan_composable. 
         if gf = [\<aa>\<^sub>S\<^sub>S, \<gg>\<^sub>S\<^sub>S]\<^sub>\<circ> \<Rightarrow> \<gg>\<^sub>S\<^sub>S
          | gf = [\<bb>\<^sub>S\<^sub>S, \<ff>\<^sub>S\<^sub>S]\<^sub>\<circ> \<Rightarrow> \<ff>\<^sub>S\<^sub>S
          | otherwise \<Rightarrow> gf\<lparr>0\<rparr>
      )"
    and "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>CId\<rparr> = vid_on (set {\<aa>\<^sub>S\<^sub>S, \<bb>\<^sub>S\<^sub>S, \<oo>\<^sub>S\<^sub>S})"
  unfolding the_cat_sspan_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Elementary properties.\<close>

lemma the_cat_scospan_components_vsv[cat_ss_cs_intros]: "vsv (\<rightarrow>\<bullet>\<leftarrow>\<^sub>C)"
  unfolding the_cat_scospan_def by auto

lemma the_cat_sspan_components_vsv[cat_ss_cs_intros]: "vsv (\<leftarrow>\<bullet>\<rightarrow>\<^sub>C)"
  unfolding the_cat_sspan_def by auto


subsubsection\<open>Objects\<close>

lemma the_cat_scospan_Obj_\<oo>I[cat_ss_cs_intros]:
  assumes "a = \<oo>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
  using assms unfolding the_cat_scospan_components by simp

lemma the_cat_scospan_Obj_\<aa>I[cat_ss_cs_intros]:
  assumes "a = \<aa>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
  using assms unfolding the_cat_scospan_components by simp

lemma the_cat_scospan_Obj_\<bb>I[cat_ss_cs_intros]:
  assumes "a = \<bb>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
  using assms unfolding the_cat_scospan_components by simp

lemma the_cat_scospan_ObjE:
  assumes "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
  obtains \<open>a = \<oo>\<^sub>S\<^sub>S\<close> | \<open>a = \<aa>\<^sub>S\<^sub>S\<close> | \<open>a = \<bb>\<^sub>S\<^sub>S\<close>
  using assms unfolding the_cat_scospan_components by auto

lemma the_cat_sspan_Obj_\<oo>I[cat_ss_cs_intros]:
  assumes "a = \<oo>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Obj\<rparr>"
  using assms unfolding the_cat_sspan_components by simp

lemma the_cat_sspan_Obj_\<aa>I[cat_ss_cs_intros]:
  assumes "a = \<aa>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Obj\<rparr>"
  using assms unfolding the_cat_sspan_components by simp

lemma the_cat_sspan_Obj_\<bb>I[cat_ss_cs_intros]:
  assumes "a = \<bb>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Obj\<rparr>"
  using assms unfolding the_cat_sspan_components by simp

lemma the_cat_sspan_ObjE:
  assumes "a \<in>\<^sub>\<circ> \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Obj\<rparr>"
  obtains \<open>a = \<oo>\<^sub>S\<^sub>S\<close> | \<open>a = \<aa>\<^sub>S\<^sub>S\<close> | \<open>a = \<bb>\<^sub>S\<^sub>S\<close>
  using assms unfolding the_cat_sspan_components by auto


subsubsection\<open>Arrows\<close>

lemma the_cat_scospan_Arr_\<aa>I[cat_ss_cs_intros]:
  assumes "a = \<aa>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_scospan_components by simp

lemma the_cat_scospan_Arr_\<bb>I[cat_ss_cs_intros]:
  assumes "a = \<bb>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_scospan_components by simp

lemma the_cat_scospan_Arr_\<oo>I[cat_ss_cs_intros]:
  assumes "a = \<oo>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_scospan_components by simp

lemma the_cat_scospan_Arr_\<gg>I[cat_ss_cs_intros]:
  assumes "a = \<gg>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_scospan_components by simp

lemma the_cat_scospan_Arr_\<ff>I[cat_ss_cs_intros]:
  assumes "a = \<ff>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_scospan_components by simp

lemma the_cat_scospan_ArrE:
  assumes "f \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Arr\<rparr>"
  obtains \<open>f = \<aa>\<^sub>S\<^sub>S\<close> | \<open>f = \<bb>\<^sub>S\<^sub>S\<close> | \<open>f = \<oo>\<^sub>S\<^sub>S\<close> | \<open>f = \<gg>\<^sub>S\<^sub>S\<close> | \<open>f = \<ff>\<^sub>S\<^sub>S\<close> 
  using assms unfolding the_cat_scospan_components by auto

lemma the_cat_sspan_Arr_\<aa>I[cat_ss_cs_intros]:
  assumes "a = \<aa>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_sspan_components by simp

lemma the_cat_sspan_Arr_\<bb>I[cat_ss_cs_intros]:
  assumes "a = \<bb>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_sspan_components by simp

lemma the_cat_sspan_Arr_\<oo>I[cat_ss_cs_intros]:
  assumes "a = \<oo>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_sspan_components by simp

lemma the_cat_sspan_Arr_\<gg>I[cat_ss_cs_intros]:
  assumes "a = \<gg>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_sspan_components by simp

lemma the_cat_sspan_Arr_\<ff>I[cat_ss_cs_intros]:
  assumes "a = \<ff>\<^sub>S\<^sub>S"
  shows "a \<in>\<^sub>\<circ> \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Arr\<rparr>"
  using assms unfolding the_cat_sspan_components by simp

lemma the_cat_sspan_ArrE:
  assumes "f \<in>\<^sub>\<circ> \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Arr\<rparr>"
  obtains \<open>f = \<aa>\<^sub>S\<^sub>S\<close> | \<open>f = \<bb>\<^sub>S\<^sub>S\<close> | \<open>f = \<oo>\<^sub>S\<^sub>S\<close> | \<open>f = \<gg>\<^sub>S\<^sub>S\<close> | \<open>f = \<ff>\<^sub>S\<^sub>S\<close> 
  using assms unfolding the_cat_sspan_components by auto


subsubsection\<open>Domain\<close>

mk_VLambda the_cat_scospan_components(3)
  |vsv the_cat_scospan_Dom_vsv[cat_ss_cs_intros]|
  |vdomain the_cat_scospan_Dom_vdomain[cat_ss_cs_simps]|

lemma the_cat_scospan_Dom_app_\<aa>[cat_ss_cs_simps]:
  assumes "f = \<aa>\<^sub>S\<^sub>S"
  shows "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<aa>\<^sub>S\<^sub>S"
  unfolding the_cat_scospan_components assms by simp

lemma the_cat_scospan_Dom_app_\<bb>[cat_ss_cs_simps]:
  assumes "f = \<bb>\<^sub>S\<^sub>S"
  shows "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<bb>\<^sub>S\<^sub>S"
  unfolding the_cat_scospan_components assms by simp

lemma the_cat_scospan_Dom_app_\<oo>[cat_ss_cs_simps]:
  assumes "f = \<oo>\<^sub>S\<^sub>S"
  shows "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<oo>\<^sub>S\<^sub>S"
  unfolding the_cat_scospan_components assms using cat_ss_ineq by auto

lemma the_cat_scospan_Dom_app_\<gg>[cat_ss_cs_simps]:
  assumes "f = \<gg>\<^sub>S\<^sub>S"
  shows "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<aa>\<^sub>S\<^sub>S"
  unfolding the_cat_scospan_components assms using cat_ss_ineq by auto

lemma the_cat_scospan_Dom_app_\<ff>[cat_ss_cs_simps]:
  assumes "f = \<ff>\<^sub>S\<^sub>S"
  shows "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<bb>\<^sub>S\<^sub>S"
  unfolding the_cat_scospan_components assms using cat_ss_ineq by auto

mk_VLambda the_cat_sspan_components(3)
  |vsv the_cat_sspan_Dom_vsv[cat_ss_cs_intros]|
  |vdomain the_cat_sspan_Dom_vdomain[cat_ss_cs_simps]|

lemma the_cat_sspan_Dom_app_\<aa>[cat_ss_cs_simps]:
  assumes "f = \<aa>\<^sub>S\<^sub>S"
  shows "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<aa>\<^sub>S\<^sub>S"
  unfolding the_cat_sspan_components assms by simp

lemma the_cat_sspan_Dom_app_\<bb>[cat_ss_cs_simps]:
  assumes "f = \<bb>\<^sub>S\<^sub>S"
  shows "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<bb>\<^sub>S\<^sub>S"
  unfolding the_cat_sspan_components assms by simp

lemma the_cat_sspan_Dom_app_\<oo>[cat_ss_cs_simps]:
  assumes "f = \<oo>\<^sub>S\<^sub>S"
  shows "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<oo>\<^sub>S\<^sub>S"
  unfolding the_cat_sspan_components assms using cat_ss_ineq by auto

lemma the_cat_sspan_Dom_app_\<gg>[cat_ss_cs_simps]:
  assumes "f = \<gg>\<^sub>S\<^sub>S"
  shows "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<oo>\<^sub>S\<^sub>S"
  unfolding the_cat_sspan_components assms using cat_ss_ineq by auto

lemma the_cat_sspan_Dom_app_\<ff>[cat_ss_cs_simps]:
  assumes "f = \<ff>\<^sub>S\<^sub>S"
  shows "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<oo>\<^sub>S\<^sub>S"
  unfolding the_cat_sspan_components assms using cat_ss_ineq by auto


subsubsection\<open>Codomain\<close>

mk_VLambda the_cat_scospan_components(4)
  |vsv the_cat_scospan_Cod_vsv[cat_ss_cs_intros]|
  |vdomain the_cat_scospan_Cod_vdomain[cat_ss_cs_simps]|

lemma the_cat_scospan_Cod_app_\<aa>[cat_ss_cs_simps]:
  assumes "f = \<aa>\<^sub>S\<^sub>S"
  shows "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<aa>\<^sub>S\<^sub>S"
  unfolding the_cat_scospan_components assms by simp

lemma the_cat_scospan_Cod_app_\<bb>[cat_ss_cs_simps]:
  assumes "f = \<bb>\<^sub>S\<^sub>S"
  shows "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<bb>\<^sub>S\<^sub>S"
  unfolding the_cat_scospan_components assms by simp

lemma the_cat_scospan_Cod_app_\<oo>[cat_ss_cs_simps]:
  assumes "f = \<oo>\<^sub>S\<^sub>S"
  shows "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<oo>\<^sub>S\<^sub>S"
  unfolding the_cat_scospan_components assms using cat_ss_ineq by auto

lemma the_cat_scospan_Cod_app_\<gg>[cat_ss_cs_simps]:
  assumes "f = \<gg>\<^sub>S\<^sub>S"
  shows "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<oo>\<^sub>S\<^sub>S"
  unfolding the_cat_scospan_components assms using cat_ss_ineq by auto

lemma the_cat_scospan_Cod_app_\<ff>[cat_ss_cs_simps]:
  assumes "f = \<ff>\<^sub>S\<^sub>S"
  shows "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<oo>\<^sub>S\<^sub>S"
  unfolding the_cat_scospan_components assms using cat_ss_ineq by auto

mk_VLambda the_cat_sspan_components(4)
  |vsv the_cat_sspan_Cod_vsv[cat_ss_cs_intros]|
  |vdomain the_cat_sspan_Cod_vdomain[cat_ss_cs_simps]|

lemma the_cat_sspan_Cod_app_\<aa>[cat_ss_cs_simps]:
  assumes "f = \<aa>\<^sub>S\<^sub>S"
  shows "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<aa>\<^sub>S\<^sub>S"
  unfolding the_cat_sspan_components assms by simp

lemma the_cat_sspan_Cod_app_\<bb>[cat_ss_cs_simps]:
  assumes "f = \<bb>\<^sub>S\<^sub>S"
  shows "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<bb>\<^sub>S\<^sub>S"
  unfolding the_cat_sspan_components assms by simp

lemma the_cat_sspan_Cod_app_\<oo>[cat_ss_cs_simps]:
  assumes "f = \<oo>\<^sub>S\<^sub>S"
  shows "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<oo>\<^sub>S\<^sub>S"
  unfolding the_cat_sspan_components assms using cat_ss_ineq by auto

lemma the_cat_sspan_Cod_app_\<gg>[cat_ss_cs_simps]:
  assumes "f = \<gg>\<^sub>S\<^sub>S"
  shows "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<aa>\<^sub>S\<^sub>S"
  unfolding the_cat_sspan_components assms using cat_ss_ineq by auto

lemma the_cat_sspan_Cod_app_\<ff>[cat_ss_cs_simps]:
  assumes "f = \<ff>\<^sub>S\<^sub>S"
  shows "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<bb>\<^sub>S\<^sub>S"
  unfolding the_cat_sspan_components assms using cat_ss_ineq by auto


subsubsection\<open>Composition\<close>

mk_VLambda the_cat_scospan_components(5)
  |vsv the_cat_scospan_Comp_vsv[cat_ss_cs_intros]|
  |vdomain the_cat_scospan_Comp_vdomain[cat_ss_cs_simps]|

lemma the_cat_scospan_Comp_app_\<aa>\<aa>[cat_ss_cs_simps]:
  assumes "g = \<aa>\<^sub>S\<^sub>S" and "f = \<aa>\<^sub>S\<^sub>S"
  shows "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = f"
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable" by auto
  with assms show "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = f"
    unfolding the_cat_scospan_components(5) by (auto simp: nat_omega_simps)
qed

lemma the_cat_scospan_Comp_app_\<bb>\<bb>[cat_ss_cs_simps]:
  assumes "g = \<bb>\<^sub>S\<^sub>S" and "f = \<bb>\<^sub>S\<^sub>S"
  shows "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = f"
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable" by auto
  with assms show "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = f"
    unfolding the_cat_scospan_components(5) by (auto simp: nat_omega_simps)
qed

lemma the_cat_scospan_Comp_app_\<oo>\<oo>[cat_ss_cs_simps]:
  assumes "g = \<oo>\<^sub>S\<^sub>S" and "f = \<oo>\<^sub>S\<^sub>S"
  shows "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = f"
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable" by auto
  with assms show "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = f"
    unfolding the_cat_scospan_components(5) by (auto simp: nat_omega_simps)
qed

lemma the_cat_scospan_Comp_app_\<oo>\<gg>[cat_ss_cs_simps]:
  assumes "g = \<oo>\<^sub>S\<^sub>S" and "f = \<gg>\<^sub>S\<^sub>S"
  shows "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = f" 
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable" by auto
  then show "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = f" 
    unfolding the_cat_scospan_components(5) assms by (auto simp: nat_omega_simps)
qed

lemma the_cat_scospan_Comp_app_\<oo>\<ff>[cat_ss_cs_simps]:
  assumes "g = \<oo>\<^sub>S\<^sub>S" and "f = \<ff>\<^sub>S\<^sub>S"
  shows "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = f" 
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable" by auto
  then show "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = f" 
    unfolding the_cat_scospan_components(5) assms by (auto simp: nat_omega_simps)
qed

lemma the_cat_scospan_Comp_app_\<gg>\<aa>[cat_ss_cs_simps]:
  assumes "g = \<gg>\<^sub>S\<^sub>S" and "f = \<aa>\<^sub>S\<^sub>S"
  shows "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = g"  
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable" by auto
  then show "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = g" 
    unfolding the_cat_scospan_components(5) assms 
    using cat_ss_ineq
    by (auto simp: nat_omega_simps)
qed

lemma the_cat_scospan_Comp_app_\<ff>\<bb>[cat_ss_cs_simps]:
  assumes "g = \<ff>\<^sub>S\<^sub>S" and "f = \<bb>\<^sub>S\<^sub>S"
  shows "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = g"  
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable" by auto
  then show "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = g" 
    unfolding the_cat_scospan_components(5) assms 
    using cat_ss_ineq
    by (auto simp: nat_omega_simps)
qed

mk_VLambda the_cat_sspan_components(5)
  |vsv the_cat_sspan_Comp_vsv[cat_ss_cs_intros]|
  |vdomain the_cat_sspan_Comp_vdomain[cat_ss_cs_simps]|

lemma the_cat_sspan_Comp_app_\<aa>\<aa>[cat_ss_cs_simps]:
  assumes "g = \<aa>\<^sub>S\<^sub>S" and "f = \<aa>\<^sub>S\<^sub>S"
  shows "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = f"
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable" by auto
  with assms show "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = f"
    unfolding the_cat_sspan_components(5) by (auto simp: nat_omega_simps)
qed

lemma the_cat_sspan_Comp_app_\<bb>\<bb>[cat_ss_cs_simps]:
  assumes "g = \<bb>\<^sub>S\<^sub>S" and "f = \<bb>\<^sub>S\<^sub>S"
  shows "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = f"
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable" by auto
  with assms show "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = f"
    unfolding the_cat_sspan_components(5) by (auto simp: nat_omega_simps)
qed

lemma the_cat_sspan_Comp_app_\<oo>\<oo>[cat_ss_cs_simps]:
  assumes "g = \<oo>\<^sub>S\<^sub>S" and "f = \<oo>\<^sub>S\<^sub>S"
  shows "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = f"
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable" by auto
  with assms show "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = g" "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = f"
    unfolding the_cat_sspan_components(5) by (auto simp: nat_omega_simps)
qed

lemma the_cat_sspan_Comp_app_\<aa>\<gg>[cat_ss_cs_simps]:
  assumes "g = \<aa>\<^sub>S\<^sub>S" and "f = \<gg>\<^sub>S\<^sub>S"
  shows "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = f" 
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable" by auto
  then show "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = f" 
    unfolding the_cat_sspan_components(5) assms by (auto simp: nat_omega_simps)
qed

lemma the_cat_sspan_Comp_app_\<bb>\<ff>[cat_ss_cs_simps]:
  assumes "g = \<bb>\<^sub>S\<^sub>S" and "f = \<ff>\<^sub>S\<^sub>S"
  shows "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = f" 
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable" by auto
  then show "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = f" 
    unfolding the_cat_sspan_components(5) assms by (auto simp: nat_omega_simps)
qed

lemma the_cat_sspan_Comp_app_\<gg>\<oo>[cat_ss_cs_simps]:
  assumes "g = \<gg>\<^sub>S\<^sub>S" and "f = \<oo>\<^sub>S\<^sub>S"
  shows "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = g"  
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable" by auto
  then show "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = g" 
    unfolding the_cat_sspan_components(5) assms 
    using cat_ss_ineq
    by (auto simp: nat_omega_simps)
qed

lemma the_cat_sspan_Comp_app_\<ff>\<oo>[cat_ss_cs_simps]:
  assumes "g = \<ff>\<^sub>S\<^sub>S" and "f = \<oo>\<^sub>S\<^sub>S"
  shows "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = g"  
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_sspan_composable" by auto
  then show "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = g" 
    unfolding the_cat_sspan_components(5) assms 
    using cat_ss_ineq
    by (auto simp: nat_omega_simps)
qed


subsubsection\<open>Identity\<close>

mk_VLambda the_cat_scospan_components(6)[folded VLambda_vid_on]
  |vsv the_cat_scospan_CId_vsv[cat_ss_cs_intros]|
  |vdomain the_cat_scospan_CId_vdomain[cat_ss_cs_simps]|
  |app the_cat_scospan_CId_app[cat_ss_cs_simps]|

mk_VLambda the_cat_sspan_components(6)[folded VLambda_vid_on]
  |vsv the_cat_sspan_CId_vsv[cat_ss_cs_intros]|
  |vdomain the_cat_sspan_CId_vdomain[cat_ss_cs_simps]|
  |app the_cat_sspan_CId_app[cat_ss_cs_simps]|


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma the_cat_scospan_is_arr_\<aa>\<aa>\<aa>[cat_ss_cs_intros]:
  assumes "a' = \<aa>\<^sub>S\<^sub>S" and "b' = \<aa>\<^sub>S\<^sub>S" and "f = \<aa>\<^sub>S\<^sub>S"
  shows "f : a' \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b'"
proof(intro is_arrI, unfold assms)
  show "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = \<aa>\<^sub>S\<^sub>S" "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>\<aa>\<^sub>S\<^sub>S\<rparr> = \<aa>\<^sub>S\<^sub>S"
    by (cs_concl cs_simp: cat_ss_cs_simps)+
qed (auto simp: the_cat_scospan_components)

lemma the_cat_scospan_is_arr_\<bb>\<bb>\<bb>[cat_ss_cs_intros]:
  assumes "a' = \<bb>\<^sub>S\<^sub>S" and "b' = \<bb>\<^sub>S\<^sub>S" and "f = \<bb>\<^sub>S\<^sub>S"
  shows "f : a' \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b'"
proof(intro is_arrI, unfold assms)
  show "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = \<bb>\<^sub>S\<^sub>S" "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>\<bb>\<^sub>S\<^sub>S\<rparr> = \<bb>\<^sub>S\<^sub>S"
    by (cs_concl cs_simp: cat_ss_cs_simps)+
qed (auto simp: the_cat_scospan_components)

lemma the_cat_scospan_is_arr_\<oo>\<oo>\<oo>[cat_ss_cs_intros]:
  assumes "a' = \<oo>\<^sub>S\<^sub>S" and "b' = \<oo>\<^sub>S\<^sub>S" and "f = \<oo>\<^sub>S\<^sub>S"
  shows "f : a' \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b'"
proof(intro is_arrI, unfold assms)
  show "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = \<oo>\<^sub>S\<^sub>S" "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>\<oo>\<^sub>S\<^sub>S\<rparr> = \<oo>\<^sub>S\<^sub>S"
    by (cs_concl cs_simp: cat_ss_cs_simps)+
qed (auto simp: the_cat_scospan_components)

lemma the_cat_scospan_is_arr_\<aa>\<oo>\<gg>[cat_ss_cs_intros]:
  assumes "a' = \<aa>\<^sub>S\<^sub>S" and "b' = \<oo>\<^sub>S\<^sub>S" and "f = \<gg>\<^sub>S\<^sub>S"
  shows "f : a' \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b'"
proof(intro is_arrI, unfold assms)
  show "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>\<gg>\<^sub>S\<^sub>S\<rparr> = \<aa>\<^sub>S\<^sub>S" "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>\<gg>\<^sub>S\<^sub>S\<rparr> = \<oo>\<^sub>S\<^sub>S"
    by (cs_concl cs_simp: cat_ss_cs_simps)+
qed (auto simp: the_cat_scospan_components)

lemma the_cat_scospan_is_arr_\<bb>\<oo>\<ff>[cat_ss_cs_intros]:
  assumes "a' = \<bb>\<^sub>S\<^sub>S" and "b' = \<oo>\<^sub>S\<^sub>S" and "f = \<ff>\<^sub>S\<^sub>S"
  shows "f : a' \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b'"
proof(intro is_arrI, unfold assms)
  show "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Dom\<rparr>\<lparr>\<ff>\<^sub>S\<^sub>S\<rparr> = \<bb>\<^sub>S\<^sub>S" "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Cod\<rparr>\<lparr>\<ff>\<^sub>S\<^sub>S\<rparr> = \<oo>\<^sub>S\<^sub>S"
    by (cs_concl cs_simp: cat_ss_cs_simps)+
qed (auto simp: the_cat_scospan_components)

lemma the_cat_scospan_is_arrE:
  assumes "f' : a' \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b'"
  obtains "a' = \<aa>\<^sub>S\<^sub>S" and "b' = \<aa>\<^sub>S\<^sub>S" and "f' = \<aa>\<^sub>S\<^sub>S"
        | "a' = \<bb>\<^sub>S\<^sub>S" and "b' = \<bb>\<^sub>S\<^sub>S" and "f' = \<bb>\<^sub>S\<^sub>S"
        | "a' = \<oo>\<^sub>S\<^sub>S" and "b' = \<oo>\<^sub>S\<^sub>S" and "f' = \<oo>\<^sub>S\<^sub>S"
        | "a' = \<aa>\<^sub>S\<^sub>S" and "b' = \<oo>\<^sub>S\<^sub>S" and "f' = \<gg>\<^sub>S\<^sub>S"
        | "a' = \<bb>\<^sub>S\<^sub>S" and "b' = \<oo>\<^sub>S\<^sub>S" and "f' = \<ff>\<^sub>S\<^sub>S"
proof-
  note f = is_arrD[OF assms]
  from f(1) consider (\<aa>\<^sub>S\<^sub>S) \<open>f' = \<aa>\<^sub>S\<^sub>S\<close> 
                   | (\<bb>\<^sub>S\<^sub>S) \<open>f' = \<bb>\<^sub>S\<^sub>S\<close> 
                   | (\<oo>\<^sub>S\<^sub>S) \<open>f' = \<oo>\<^sub>S\<^sub>S\<close> 
                   | (\<gg>\<^sub>S\<^sub>S) \<open>f' = \<gg>\<^sub>S\<^sub>S\<close> 
                   | (\<ff>\<^sub>S\<^sub>S) \<open>f' = \<ff>\<^sub>S\<^sub>S\<close> 
    by (elim the_cat_scospan_ArrE)
  then show ?thesis
  proof cases
    case \<aa>\<^sub>S\<^sub>S
    moreover from f(2,3)[unfolded \<aa>\<^sub>S\<^sub>S, symmetric] have "a' = \<aa>\<^sub>S\<^sub>S" "b' = \<aa>\<^sub>S\<^sub>S"
      by (simp_all add: cat_ss_cs_simps)
    ultimately show ?thesis using that by auto
  next
    case \<bb>\<^sub>S\<^sub>S
    moreover from f(2,3)[unfolded \<bb>\<^sub>S\<^sub>S, symmetric] have "a' = \<bb>\<^sub>S\<^sub>S" "b' = \<bb>\<^sub>S\<^sub>S"
      by (simp_all add: cat_ss_cs_simps)
    ultimately show ?thesis using that by auto
  next
    case \<oo>\<^sub>S\<^sub>S
    moreover from f(2,3)[unfolded \<oo>\<^sub>S\<^sub>S, symmetric] have "a' = \<oo>\<^sub>S\<^sub>S" "b' = \<oo>\<^sub>S\<^sub>S"
      by (simp_all add: cat_ss_cs_simps)
    ultimately show ?thesis using that by auto
  next
    case \<gg>\<^sub>S\<^sub>S
    moreover have "a' = \<aa>\<^sub>S\<^sub>S" "b' = \<oo>\<^sub>S\<^sub>S"
      by (simp_all add: f(2,3)[unfolded \<gg>\<^sub>S\<^sub>S, symmetric] cat_ss_cs_simps)
    ultimately show ?thesis using that by auto
  next
    case \<ff>\<^sub>S\<^sub>S
    moreover have "a' = \<bb>\<^sub>S\<^sub>S" "b' = \<oo>\<^sub>S\<^sub>S"
      by (simp_all add: f(2,3)[unfolded \<ff>\<^sub>S\<^sub>S, symmetric] cat_ss_cs_simps)
    ultimately show ?thesis using that by auto
  qed
qed


subsubsection\<open>\<open>\<rightarrow>\<bullet>\<leftarrow>\<close> is a finite category\<close>

lemma (in \<Z>) finite_category_the_cat_scospan[cat_ss_cs_intros]:
  "finite_category \<alpha> (\<rightarrow>\<bullet>\<leftarrow>\<^sub>C)"
proof(intro finite_categoryI'' tiny_categoryI'')
  show "vfsequence (\<rightarrow>\<bullet>\<leftarrow>\<^sub>C)" unfolding the_cat_scospan_def by simp
  show "vcard (\<rightarrow>\<bullet>\<leftarrow>\<^sub>C) = 6\<^sub>\<nat>"
    unfolding the_cat_scospan_def by (simp_all add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" by (auto simp: the_cat_scospan_components)
  show "\<R>\<^sub>\<circ> (\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" by (auto simp: the_cat_scospan_components)
  show "(gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Comp\<rparr>)) =
    (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b)"
    for gf
    unfolding the_cat_scospan_Comp_vdomain
  proof
    assume prems: "gf \<in>\<^sub>\<circ> cat_scospan_composable"
    then obtain g f where gf_def: "gf = [g, f]\<^sub>\<circ>" by auto
    from prems show 
      "\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b"
      unfolding gf_def
      by (*slow*)
        (
          cases rule: cat_scospan_composableE; 
          (intro exI conjI)?; 
          cs_concl_step?;
          (simp only:)?,
          all\<open>intro is_arrI, unfold the_cat_scospan_components(2)\<close>
        )
        (cs_concl cs_simp: cat_ss_cs_simps V_cs_simps cs_intro: V_cs_intros)+
  next
    assume prems: 
      "\<exists>g f b' c' a'. gf = [g, f]\<^sub>\<circ> \<and> g : b' \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> c' \<and> f : a' \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b'"
    then obtain g f b c a
      where gf_def: "gf = [g, f]\<^sub>\<circ>"
        and g: "g : b \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> c"
        and f: "f : a \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b"
      by clarsimp
    from g f show "gf \<in>\<^sub>\<circ> cat_scospan_composable"
      unfolding gf_def 
      by (elim the_cat_scospan_is_arrE) (auto simp: cat_ss_cs_intros)
  qed
  show "\<D>\<^sub>\<circ> (\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>CId\<rparr>) = \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
    by (simp add: cat_ss_cs_simps the_cat_scospan_components)
  show "g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f : a \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> c"
    if "g : b \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> c" and "f : a \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b" for b c g a f
    using that
    by (elim the_cat_scospan_is_arrE; simp only:)
      (
        all\<open>
          solves\<open>simp add: cat_ss_ineq cat_ss_ineq[symmetric]\<close> |
          cs_concl cs_simp: cat_ss_cs_simps cs_intro: cat_ss_cs_intros
        \<close>
      )
  show "h \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = h \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> (g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f)"
    if "h : c \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> d" and "g : b \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> c" and "f : a \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b"
    for c d h b g a f
    using that 
    by (elim the_cat_scospan_is_arrE; simp only:) (*slow*)
      (
        all\<open>
          solves\<open>simp only: cat_ss_ineq cat_ss_ineq[symmetric]\<close> | 
          cs_concl cs_simp: cat_ss_cs_simps cs_intro: cat_ss_cs_intros
          \<close>
      )
  show "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> a" if "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" for a
    using that
    by (elim the_cat_scospan_ObjE) 
      (
        all\<open>
          cs_concl
            cs_simp: V_cs_simps cat_ss_cs_simps
            cs_intro: V_cs_intros cat_ss_cs_intros
        \<close>
      )
  show "\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f = f" if "f : a \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b" for a b f
    using that 
    by (elim the_cat_scospan_is_arrE) (*slow*)
      (
        cs_concl 
          cs_simp: V_cs_simps cat_ss_cs_simps 
          cs_intro: V_cs_intros cat_ss_cs_intros
      )+
  show "f \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>CId\<rparr>\<lparr>b\<rparr> = f" if "f : b \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> c" for b c f
    using that 
    by (elim the_cat_scospan_is_arrE)
      (
        cs_concl
          cs_simp: V_cs_simps cat_ss_cs_simps 
          cs_intro: V_cs_intros cat_ss_cs_intros
      )+
qed 
  (
    cs_concl
      cs_simp: V_cs_simps cat_ss_cs_simps the_cat_scospan_components(1,2) 
      cs_intro: cat_cs_intros cat_ss_cs_intros V_cs_intros 
  )+

lemmas [cat_ss_cs_intros] = \<Z>.finite_category_the_cat_scospan


subsubsection\<open>Duality for \<open>\<rightarrow>\<bullet>\<leftarrow>\<close> and \<open>\<leftarrow>\<bullet>\<rightarrow>\<close>\<close>

lemma the_cat_scospan_op[cat_op_simps]: "op_cat (\<rightarrow>\<bullet>\<leftarrow>\<^sub>C) = \<leftarrow>\<bullet>\<rightarrow>\<^sub>C"
proof-
  have dom_lhs: "\<D>\<^sub>\<circ> (op_cat (\<rightarrow>\<bullet>\<leftarrow>\<^sub>C)) = 6\<^sub>\<nat>" 
    unfolding op_cat_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (\<leftarrow>\<bullet>\<rightarrow>\<^sub>C) = 6\<^sub>\<nat>" 
    unfolding the_cat_sspan_def by (simp add: nat_omega_simps)
  show ?thesis
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
    show "a \<in>\<^sub>\<circ> 6\<^sub>\<nat> \<Longrightarrow> op_cat (\<rightarrow>\<bullet>\<leftarrow>\<^sub>C)\<lparr>a\<rparr> = \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>a\<rparr>" for a
    proof
      (
        elim_in_numeral,
        fold dg_field_simps,
        unfold op_cat_components;
        rule sym
      )
      show "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Comp\<rparr> = fflip (\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Comp\<rparr>)"
      proof(rule vsv_eqI, unfold cat_ss_cs_simps vdomain_fflip)
        fix gf assume prems: "gf \<in>\<^sub>\<circ> cat_sspan_composable"
        then obtain g f where gf_def: "gf = [g, f]\<^sub>\<circ>" by auto
        from prems have fg: "[f, g]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable"
          unfolding gf_def by auto
        have [cat_ss_cs_simps]: "g \<circ>\<^sub>A\<^bsub>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<^esub> f = f \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> g"
          if "[f, g]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_scospan_composable"
          using that
          by (elim cat_scospan_composableE; simp only:)
            (cs_concl cs_simp: cat_ss_cs_simps cs_intro: cat_ss_cs_intros)+
        from fg show 
          "\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Comp\<rparr>\<lparr>gf\<rparr> = fflip (\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Comp\<rparr>)\<lparr>gf\<rparr>"
          unfolding gf_def by (cs_concl cs_simp: cat_ss_cs_simps fflip_app)
      qed (auto intro: fflip_vsv cat_ss_cs_intros)
    qed (unfold the_cat_sspan_components the_cat_scospan_components, simp_all)
  qed (auto intro: cat_op_intros cat_ss_cs_intros)
qed

lemma (in \<Z>) the_cat_sspan_op[cat_op_simps]: "op_cat (\<leftarrow>\<bullet>\<rightarrow>\<^sub>C) = \<rightarrow>\<bullet>\<leftarrow>\<^sub>C"
proof-
  interpret scospan: finite_category \<alpha> \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close> 
    by (rule finite_category_the_cat_scospan)
  interpret sspan: finite_category \<alpha> \<open>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<close>
    by (rule scospan.finite_category_op[unfolded cat_op_simps])
  from the_cat_scospan_op have "op_cat (\<leftarrow>\<bullet>\<rightarrow>\<^sub>C) = op_cat (op_cat (\<rightarrow>\<bullet>\<leftarrow>\<^sub>C))" by simp
  also have "\<dots> = \<rightarrow>\<bullet>\<leftarrow>\<^sub>C" by (cs_concl cs_simp: cat_op_simps)
  finally show ?thesis by auto
qed

lemmas [cat_op_simps] = \<Z>.the_cat_sspan_op


subsubsection\<open>\<open>\<leftarrow>\<bullet>\<rightarrow>\<close> is a finite category\<close>

lemma (in \<Z>) finite_category_the_cat_sspan[cat_ss_cs_intros]:
  "finite_category \<alpha> (\<leftarrow>\<bullet>\<rightarrow>\<^sub>C)"
proof-
  interpret scospan: finite_category \<alpha> \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close>
    by (rule finite_category_the_cat_scospan)
  show ?thesis by (rule scospan.finite_category_op[unfolded cat_op_simps])
qed


subsection\<open>Local assumptions for functors from \<open>\<rightarrow>\<bullet>\<leftarrow>\<close> and \<open>\<leftarrow>\<bullet>\<rightarrow>\<close>\<close>


text\<open>
The functors from \<open>\<rightarrow>\<bullet>\<leftarrow>\<close> and \<open>\<leftarrow>\<bullet>\<rightarrow>\<close> are introduced as
convenient abstractions for the definition of the 
pullbacks and the pushouts (e.g., see Chapter III-3 and 
Chapter III-4 in \cite{mac_lane_categories_2010}).
\<close>


subsubsection\<open>Definitions and elementary properties\<close>

locale cf_scospan = category \<alpha> \<CC> for \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<CC> +
  assumes cf_scospan_\<gg>[cat_ss_cs_intros]: "\<gg> : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> \<oo>"
    and cf_scospan_\<ff>[cat_ss_cs_intros]: "\<ff> : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> \<oo>"

lemma (in cf_scospan) cf_scospan_\<gg>'[cat_ss_cs_intros]:
  assumes "a = \<aa>" and "b = \<oo>"
  shows "\<gg> : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_scospan_\<gg>)

lemma (in cf_scospan) cf_scospan_\<gg>''[cat_ss_cs_intros]:
  assumes "g = \<gg>" and "b = \<oo>"
  shows "g : \<aa> \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_scospan_\<gg>) 

lemma (in cf_scospan) cf_scospan_\<gg>'''[cat_ss_cs_intros]:
  assumes "g = \<gg>" and "a = \<aa>"
  shows "g : a \<mapsto>\<^bsub>\<CC>\<^esub> \<oo>"
  unfolding assms by (rule cf_scospan_\<gg>) 

lemma (in cf_scospan) cf_scospan_\<ff>'[cat_ss_cs_intros]:
  assumes "a = \<bb>" and "b = \<oo>"
  shows "\<ff> : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_scospan_\<ff>) 

lemma (in cf_scospan) cf_scospan_\<ff>''[cat_ss_cs_intros]:
  assumes "f = \<ff>" and "b = \<oo>"
  shows "f : \<bb> \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_scospan_\<ff>) 

lemma (in cf_scospan) cf_scospan_\<ff>'''[cat_ss_cs_intros]:
  assumes "g = \<ff>" and "b = \<bb>"
  shows "g : b \<mapsto>\<^bsub>\<CC>\<^esub> \<oo>"
  unfolding assms by (rule cf_scospan_\<ff>) 

locale cf_sspan = category \<alpha> \<CC> for \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> and \<CC> +
  assumes cf_sspan_\<gg>[cat_ss_cs_intros]: "\<gg> : \<oo> \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
    and cf_sspan_\<ff>[cat_ss_cs_intros]: "\<ff> : \<oo> \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"

lemma (in cf_sspan) cf_sspan_\<gg>'[cat_ss_cs_intros]:
  assumes "a = \<oo>" and "b = \<aa>"
  shows "\<gg> : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_sspan_\<gg>) 

lemma (in cf_sspan) cf_sspan_\<gg>''[cat_ss_cs_intros]:
  assumes "g = \<gg>" and "a = \<aa>"
  shows "g : \<oo> \<mapsto>\<^bsub>\<CC>\<^esub> a"
  unfolding assms by (rule cf_sspan_\<gg>) 

lemma (in cf_sspan) cf_sspan_\<gg>'''[cat_ss_cs_intros]:
  assumes "g = \<gg>" and "a = \<oo>"
  shows "g : a \<mapsto>\<^bsub>\<CC>\<^esub> \<aa>"
  unfolding assms by (rule cf_sspan_\<gg>) 

lemma (in cf_sspan) cf_sspan_\<ff>'[cat_ss_cs_intros]:
  assumes "a = \<oo>" and "b = \<bb>"
  shows "\<ff> : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_sspan_\<ff>) 

lemma (in cf_sspan) cf_sspan_\<ff>''[cat_ss_cs_intros]:
  assumes "f = \<ff>" and "b = \<bb>"
  shows "f : \<oo> \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding assms by (rule cf_sspan_\<ff>) 

lemma (in cf_sspan) cf_sspan_\<ff>'''[cat_ss_cs_intros]:
  assumes "f = \<ff>" and "b = \<oo>"
  shows "f : b \<mapsto>\<^bsub>\<CC>\<^esub> \<bb>"
  unfolding assms by (rule cf_sspan_\<ff>) 


text\<open>Rules.\<close>

lemmas (in cf_scospan) [cat_ss_cs_intros] = cf_scospan_axioms

mk_ide rf cf_scospan_def[unfolded cf_scospan_axioms_def]
  |intro cf_scospanI|
  |dest cf_scospanD[dest]|
  |elim cf_scospanE[elim]|

lemmas [cat_ss_cs_intros] = cf_scospanD(1)

lemmas (in cf_sspan) [cat_ss_cs_intros] = cf_sspan_axioms

mk_ide rf cf_sspan_def[unfolded cf_sspan_axioms_def]
  |intro cf_sspanI|
  |dest cf_sspanD[dest]|
  |elim cf_sspanE[elim]|


text\<open>Duality.\<close>

lemma (in cf_scospan) cf_sspan_op[cat_op_intros]: 
  "cf_sspan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> (op_cat \<CC>)"
  by (intro cf_sspanI, unfold cat_op_simps)
    (cs_concl cs_intro: cat_cs_intros cat_op_intros cat_ss_cs_intros)+ 

lemmas [cat_op_intros] = cf_scospan.cf_sspan_op

lemma (in cf_sspan) cf_scospan_op[cat_op_intros]: 
  "cf_scospan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> (op_cat \<CC>)"
  by (intro cf_scospanI, unfold cat_op_simps)
    (cs_concl cs_intro: cat_cs_intros cat_op_intros cat_ss_cs_intros)+ 

lemmas [cat_op_intros] = cf_sspan.cf_scospan_op



subsection\<open>Functors from \<open>\<rightarrow>\<bullet>\<leftarrow>\<close> and \<open>\<leftarrow>\<bullet>\<rightarrow>\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition the_cf_scospan :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" 
  (\<open>\<langle>_\<rightarrow>_\<rightarrow>_\<leftarrow>_\<leftarrow>_\<rangle>\<^sub>C\<^sub>F\<index>\<close> [51, 51, 51, 51, 51] 999)
  where "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> =
    [
      (
        \<lambda>a\<in>\<^sub>\<circ>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>.
         if a = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<aa>
          | a = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<bb>
          | otherwise \<Rightarrow> \<oo>
      ),
      (
        \<lambda>f\<in>\<^sub>\<circ>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Arr\<rparr>.
         if f = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>\<rparr>
          | f = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>\<rparr>
          | f = \<gg>\<^sub>S\<^sub>S \<Rightarrow> \<gg>
          | f = \<ff>\<^sub>S\<^sub>S \<Rightarrow> \<ff>
          | otherwise \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<oo>\<rparr>
      ),
      \<rightarrow>\<bullet>\<leftarrow>\<^sub>C,
      \<CC>
    ]\<^sub>\<circ>"

definition the_cf_sspan :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" 
  (\<open>\<langle>_\<leftarrow>_\<leftarrow>_\<rightarrow>_\<rightarrow>_\<rangle>\<^sub>C\<^sub>F\<index>\<close> [51, 51, 51, 51, 51] 999)
  where "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> =
    [
      (
        \<lambda>a\<in>\<^sub>\<circ>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Obj\<rparr>.
         if a = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<aa>
          | a = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<bb>
          | otherwise \<Rightarrow> \<oo>
      ),
      (
        \<lambda>f\<in>\<^sub>\<circ>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Arr\<rparr>.
         if f = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>\<rparr>
          | f = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>\<rparr>
          | f = \<gg>\<^sub>S\<^sub>S \<Rightarrow> \<gg>
          | f = \<ff>\<^sub>S\<^sub>S \<Rightarrow> \<ff>
          | otherwise \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<oo>\<rparr>
      ),
      \<leftarrow>\<bullet>\<rightarrow>\<^sub>C,
      \<CC>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma the_cf_scospan_components:
  shows "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr> =
    (
      \<lambda>a\<in>\<^sub>\<circ>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>.
       if a = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<aa>
        | a = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<bb>
        | otherwise \<Rightarrow> \<oo>
    )"
    and "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr> =
      (
        \<lambda>f\<in>\<^sub>\<circ>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Arr\<rparr>.
         if f = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>\<rparr>
          | f = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>\<rparr>
          | f = \<gg>\<^sub>S\<^sub>S \<Rightarrow> \<gg>
          | f = \<ff>\<^sub>S\<^sub>S \<Rightarrow> \<ff>
          | otherwise \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<oo>\<rparr>
      )"
    and [cat_ss_cs_simps]: "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>HomDom\<rparr> = \<rightarrow>\<bullet>\<leftarrow>\<^sub>C"
    and [cat_ss_cs_simps]: "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>HomCod\<rparr> = \<CC>"
  unfolding the_cf_scospan_def dghm_field_simps by (simp_all add: nat_omega_simps)

lemma the_cf_sspan_components:
  shows "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr> =
    (
      \<lambda>a\<in>\<^sub>\<circ>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Obj\<rparr>.
       if a = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<aa>
        | a = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<bb>
        | otherwise \<Rightarrow> \<oo>
    )"
    and "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr> =
      (
        \<lambda>f\<in>\<^sub>\<circ>\<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Arr\<rparr>.
         if f = \<aa>\<^sub>S\<^sub>S \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>\<rparr>
          | f = \<bb>\<^sub>S\<^sub>S \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>\<rparr>
          | f = \<gg>\<^sub>S\<^sub>S \<Rightarrow> \<gg>
          | f = \<ff>\<^sub>S\<^sub>S \<Rightarrow> \<ff>
          | otherwise \<Rightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>\<oo>\<rparr>
      )"
    and [cat_ss_cs_simps]: "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>HomDom\<rparr> = \<leftarrow>\<bullet>\<rightarrow>\<^sub>C"
    and [cat_ss_cs_simps]: "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>HomCod\<rparr> = \<CC>"
  unfolding the_cf_sspan_def dghm_field_simps 
  by (simp_all add: nat_omega_simps)


text\<open>Elementary properties.\<close>

lemma the_cf_scospan_components_vsv[cat_ss_cs_intros]: "vsv (\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>)"
  unfolding the_cf_scospan_def by auto

lemma the_cf_sspan_components_vsv[cat_ss_cs_intros]: "vsv (\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>)"
  unfolding the_cf_sspan_def by auto


subsubsection\<open>Object map.\<close>

mk_VLambda the_cf_scospan_components(1)
  |vsv the_cf_scospan_ObjMap_vsv[cat_ss_cs_intros]|
  |vdomain the_cf_scospan_ObjMap_vdomain[cat_ss_cs_simps]|
  |app the_cf_scospan_ObjMap_app|

lemma the_cf_scospan_ObjMap_app_\<aa>[cat_ss_cs_simps]:
  assumes "x = \<aa>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> = \<aa>"
  by 
    (
      cs_concl 
        cs_simp: the_cf_scospan_ObjMap_app V_cs_simps assms
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_scospan) the_cf_scospan_ObjMap_app_\<bb>[cat_ss_cs_simps]:
  assumes "x = \<bb>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> = \<bb>"
  using cat_ss_ineq
  by 
    (
      cs_concl 
        cs_simp: V_cs_simps the_cf_scospan_ObjMap_app assms 
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_scospan) the_cf_scospan_ObjMap_app_\<oo>[cat_ss_cs_simps]:
  assumes "x = \<oo>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> = \<oo>"
  using cat_ss_ineq
  by 
    (
      cs_concl 
        cs_simp: V_cs_simps the_cf_scospan_ObjMap_app assms 
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_scospan) the_cf_scospan_ObjMap_vrange:
  "\<R>\<^sub>\<circ> (\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
proof
  (
    intro vsv.vsv_vrange_vsubset, 
    unfold the_cf_scospan_ObjMap_vdomain, 
    intro the_cf_scospan_ObjMap_vsv
  )
  fix a assume "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>"
  then consider \<open>a = \<aa>\<^sub>S\<^sub>S\<close> | \<open>a = \<bb>\<^sub>S\<^sub>S\<close> | \<open>a = \<oo>\<^sub>S\<^sub>S\<close> 
    unfolding the_cat_scospan_components by auto
  then show "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by cases 
      (
        cs_concl
          cs_simp: cat_ss_cs_simps cs_intro: cat_cs_intros cat_ss_cs_intros
      )+
qed

mk_VLambda the_cf_sspan_components(1)
  |vsv the_cf_sspan_ObjMap_vsv[cat_ss_cs_intros]|
  |vdomain the_cf_sspan_ObjMap_vdomain[cat_ss_cs_simps]|
  |app the_cf_sspan_ObjMap_app|

lemma the_cf_sspan_ObjMap_app_\<aa>[cat_ss_cs_simps]:
  assumes "x = \<aa>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> = \<aa>"
  by 
    (
      cs_concl 
        cs_simp: the_cf_sspan_ObjMap_app V_cs_simps assms
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_sspan) the_cf_sspan_ObjMap_app_\<bb>[cat_ss_cs_simps]:
  assumes "x = \<bb>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> = \<bb>"
  using cat_ss_ineq
  by 
    (
      cs_concl 
        cs_simp: V_cs_simps the_cf_sspan_ObjMap_app assms 
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_sspan) the_cf_sspan_ObjMap_app_\<oo>[cat_ss_cs_simps]:
  assumes "x = \<oo>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> = \<oo>"
  using cat_ss_ineq
  by 
    (
      cs_concl 
        cs_simp: V_cs_simps the_cf_sspan_ObjMap_app assms 
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_sspan) the_cf_sspan_ObjMap_vrange:
  "\<R>\<^sub>\<circ> (\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
proof
  (
    intro vsv.vsv_vrange_vsubset, 
    unfold the_cf_sspan_ObjMap_vdomain, 
    intro the_cf_sspan_ObjMap_vsv
  )
  fix a assume "a \<in>\<^sub>\<circ> \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Obj\<rparr>"
  then consider \<open>a = \<aa>\<^sub>S\<^sub>S\<close> | \<open>a = \<bb>\<^sub>S\<^sub>S\<close> | \<open>a = \<oo>\<^sub>S\<^sub>S\<close> 
    unfolding the_cat_sspan_components by auto
  then show "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by cases 
      (
        cs_concl 
          cs_simp: cat_ss_cs_simps cs_intro: cat_cs_intros cat_ss_cs_intros
      )+
qed


subsubsection\<open>Arrow map.\<close>

mk_VLambda the_cf_scospan_components(2)
  |vsv the_cf_scospan_ArrMap_vsv[cat_ss_cs_intros]|
  |vdomain the_cf_scospan_ArrMap_vdomain[cat_ss_cs_simps]|
  |app the_cf_scospan_ArrMap_app|

lemma (in cf_scospan) the_cf_scospan_ArrMap_app_\<oo>[cat_ss_cs_simps]:
  assumes "f = \<oo>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>\<oo>\<rparr>"
  using cat_ss_ineq
  by 
    (
      cs_concl 
        cs_simp: V_cs_simps the_cf_scospan_ArrMap_app assms 
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_scospan) the_cf_scospan_ArrMap_app_\<aa>[cat_ss_cs_simps]:
  assumes "f = \<aa>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>\<rparr>"
  using cat_ss_ineq
  by 
    (
      cs_concl 
        cs_simp: V_cs_simps the_cf_scospan_ArrMap_app assms 
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_scospan) the_cf_scospan_ArrMap_app_\<bb>[cat_ss_cs_simps]:
  assumes "f = \<bb>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>\<rparr>"
  using cat_ss_ineq
  by 
    (
      cs_concl 
        cs_simp: V_cs_simps the_cf_scospan_ArrMap_app assms 
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_scospan) the_cf_scospan_ArrMap_app_\<gg>[cat_ss_cs_simps]:
  assumes "f = \<gg>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<gg>"
  using cat_ss_ineq
  by 
    (
      cs_concl 
        cs_simp: V_cs_simps the_cf_scospan_ArrMap_app assms 
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_scospan) the_cf_scospan_ArrMap_app_\<ff>[cat_ss_cs_simps]:
  assumes "f = \<ff>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<ff>"
  using cat_ss_ineq
  by 
    (
      cs_concl 
        cs_simp: V_cs_simps the_cf_scospan_ArrMap_app assms 
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_scospan) the_cf_scospan_ArrMap_vrange:
  "\<R>\<^sub>\<circ> (\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof
  (
    intro vsv.vsv_vrange_vsubset, 
    unfold the_cf_scospan_ArrMap_vdomain, 
    intro the_cf_scospan_ArrMap_vsv
  )
  fix a assume "a \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Arr\<rparr>"
  then consider \<open>a = \<aa>\<^sub>S\<^sub>S\<close> | \<open>a = \<bb>\<^sub>S\<^sub>S\<close> | \<open>a = \<oo>\<^sub>S\<^sub>S\<close> | \<open>a = \<gg>\<^sub>S\<^sub>S\<close> | \<open>a = \<ff>\<^sub>S\<^sub>S\<close> 
    unfolding the_cat_scospan_components by auto
  then show "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    by cases 
      (
        cs_concl 
          cs_simp: cat_ss_cs_simps cs_intro: cat_cs_intros cat_ss_cs_intros
      )+
qed

mk_VLambda the_cf_sspan_components(2)
  |vsv the_cf_sspan_ArrMap_vsv[cat_ss_cs_intros]|
  |vdomain the_cf_sspan_ArrMap_vdomain[cat_ss_cs_simps]|
  |app the_cf_sspan_ArrMap_app|

lemma (in cf_sspan) the_cf_sspan_ArrMap_app_\<oo>[cat_ss_cs_simps]:
  assumes "f = \<oo>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>\<oo>\<rparr>"
  using cat_ss_ineq
  by 
    (
      cs_concl 
        cs_simp: V_cs_simps the_cf_sspan_ArrMap_app assms 
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_sspan) the_cf_sspan_ArrMap_app_\<aa>[cat_ss_cs_simps]:
  assumes "f = \<aa>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>\<aa>\<rparr>"
  using cat_ss_ineq
  by 
    (
      cs_concl 
        cs_simp: V_cs_simps the_cf_sspan_ArrMap_app assms 
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_sspan) the_cf_sspan_ArrMap_app_\<bb>[cat_ss_cs_simps]:
  assumes "f = \<bb>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>\<bb>\<rparr>"
  using cat_ss_ineq
  by 
    (
      cs_concl 
        cs_simp: V_cs_simps the_cf_sspan_ArrMap_app assms 
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_sspan) the_cf_sspan_ArrMap_app_\<gg>[cat_ss_cs_simps]:
  assumes "f = \<gg>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<gg>"
  using cat_ss_ineq
  by 
    (
      cs_concl 
        cs_simp: V_cs_simps the_cf_sspan_ArrMap_app assms 
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_sspan) the_cf_sspan_ArrMap_app_\<ff>[cat_ss_cs_simps]:
  assumes "f = \<ff>\<^sub>S\<^sub>S"
  shows "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<ff>"
  using cat_ss_ineq
  by 
    (
      cs_concl 
        cs_simp: V_cs_simps the_cf_sspan_ArrMap_app assms 
        cs_intro: cat_ss_cs_intros
    )

lemma (in cf_sspan) the_cf_sspan_ArrMap_vrange:
  "\<R>\<^sub>\<circ> (\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof
  (
    intro vsv.vsv_vrange_vsubset,
    unfold the_cf_sspan_ArrMap_vdomain,
    intro the_cf_sspan_ArrMap_vsv
  )
  fix a assume "a \<in>\<^sub>\<circ> \<leftarrow>\<bullet>\<rightarrow>\<^sub>C\<lparr>Arr\<rparr>"
  then consider \<open>a = \<aa>\<^sub>S\<^sub>S\<close> | \<open>a = \<bb>\<^sub>S\<^sub>S\<close> | \<open>a = \<oo>\<^sub>S\<^sub>S\<close> | \<open>a = \<gg>\<^sub>S\<^sub>S\<close> | \<open>a = \<ff>\<^sub>S\<^sub>S\<close> 
    unfolding the_cat_sspan_components by auto
  then show "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    by cases
      (
        cs_concl
          cs_simp: cat_ss_cs_simps cs_intro: cat_cs_intros cat_ss_cs_intros
      )+
qed


subsubsection\<open>Functor from \<open>\<rightarrow>\<bullet>\<leftarrow>\<close> is a functor\<close>

lemma (in cf_scospan) cf_scospan_the_cf_scospan_is_tm_functor:
  "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<rightarrow>\<bullet>\<leftarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_functor.cf_is_tm_functor_if_HomDom_finite_category is_functorI')
  show "vfsequence (\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>)" 
    unfolding the_cf_scospan_def by auto
  show "vcard (\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>) = 4\<^sub>\<nat>"
    unfolding the_cf_scospan_def by (simp add: nat_omega_simps)
  show "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> :
    \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    if "f : a \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b" for a b f
    using that
    by (cases rule: the_cat_scospan_is_arrE; simp only:)
      (
        cs_concl 
          cs_simp: cat_ss_cs_simps cs_intro: cat_cs_intros cat_ss_cs_intros
      )+
  show "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> f\<rparr> =
    \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
    if "g : b \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> c" and "f : a \<mapsto>\<^bsub>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<^esub> b" for b c g a f
    using that
    by (elim the_cat_scospan_is_arrE) (*very slow*)
      (
        all\<open>simp only:\<close>, 
        all\<open>
          solves\<open>simp add: cat_ss_ineq cat_ss_ineq[symmetric]\<close> | 
          cs_concl 
            cs_simp: cat_cs_simps cat_ss_cs_simps 
            cs_intro: cat_cs_intros cat_ss_cs_intros
          \<close>
      )
  show 
    "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ArrMap\<rparr>\<lparr>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> =
      \<CC>\<lparr>CId\<rparr>\<lparr>\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
    if "c \<in>\<^sub>\<circ> \<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<lparr>Obj\<rparr>" for c
    using that
    by (elim the_cat_scospan_ObjE; simp only:)
      (
        cs_concl
          cs_simp: V_cs_simps cat_ss_cs_simps 
          cs_intro: V_cs_intros cat_ss_cs_intros
      )+

qed
  (
    cs_concl
      cs_simp: cat_ss_cs_simps
      cs_intro: 
        the_cf_scospan_ObjMap_vrange
        cat_ss_cs_intros cat_cs_intros cat_small_cs_intros
  )+

lemma (in cf_scospan) cf_scospan_the_cf_scospan_is_tm_functor':
  assumes "\<AA>' = \<rightarrow>\<bullet>\<leftarrow>\<^sub>C" and "\<CC>' = \<CC>"
  shows "\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule cf_scospan_the_cf_scospan_is_tm_functor)

lemmas [cat_ss_cs_intros] = cf_scospan.cf_scospan_the_cf_scospan_is_tm_functor


subsubsection\<open>Duality for the functors from \<open>\<rightarrow>\<bullet>\<leftarrow>\<close> and \<open>\<leftarrow>\<bullet>\<rightarrow>\<close>\<close>

lemma op_cf_cf_scospan[cat_op_simps]: 
  "op_cf (\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>) = \<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>op_cat \<CC>\<^esub>"
proof-
  have dom_lhs: "\<D>\<^sub>\<circ> (op_cf (\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>)) = 4\<^sub>\<nat>" 
    unfolding op_cf_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>op_cat \<CC>\<^esub>) = 4\<^sub>\<nat>" 
    unfolding the_cf_sspan_def by (simp add: nat_omega_simps)
  show ?thesis
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
    show "op_cf (\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>)\<lparr>a\<rparr> = \<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>op_cat \<CC>\<^esub>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> 4\<^sub>\<nat>" for a
      using that
      by 
        (
          elim_in_numeral, 
          fold dghm_field_simps, 
          unfold cat_op_simps the_cf_sspan_components the_cf_scospan_components
        )
        (
          simp_all add: 
            the_cat_scospan_components(1,2)
            the_cat_sspan_components(1,2)
            cat_op_simps
        )
  qed (auto intro: cat_op_intros cat_ss_cs_intros)
qed

lemma (in \<Z>) op_cf_cf_scospan[cat_op_simps]: 
  "op_cf (\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>) = \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>op_cat \<CC>\<^esub>"
proof-
  have dom_lhs: "\<D>\<^sub>\<circ> (op_cf (\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>)) = 4\<^sub>\<nat>" 
    unfolding op_cf_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>op_cat \<CC>\<^esub>) = 4\<^sub>\<nat>" 
    unfolding the_cf_scospan_def by (simp add: nat_omega_simps)
  show ?thesis
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
    show "op_cf (\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub>)\<lparr>a\<rparr> = \<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>op_cat \<CC>\<^esub>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> 4\<^sub>\<nat>" for a
      using that
      by 
        (
          elim_in_numeral, 
          fold dghm_field_simps, 
          unfold cat_op_simps the_cf_sspan_components the_cf_scospan_components
        )
        (
          simp_all add: 
            the_cat_scospan_components(1,2)
            the_cat_sspan_components(1,2)
            cat_op_simps
        )
  qed (auto intro: cat_op_intros cat_ss_cs_intros)
qed

lemmas [cat_op_simps] = \<Z>.op_cf_cf_scospan


subsubsection\<open>Functor from \<open>\<leftarrow>\<bullet>\<rightarrow>\<close> is a functor\<close>

lemma (in cf_sspan) cf_sspan_the_cf_sspan_is_tm_functor:
  "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<leftarrow>\<bullet>\<rightarrow>\<^sub>C \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret scospan: cf_scospan \<alpha> \<aa> \<gg> \<oo> \<ff> \<bb> \<open>op_cat \<CC>\<close> by (rule cf_scospan_op)
  interpret scospan:
    is_tm_functor \<alpha> \<open>\<rightarrow>\<bullet>\<leftarrow>\<^sub>C\<close> \<open>op_cat \<CC>\<close> \<open>\<langle>\<aa>\<rightarrow>\<gg>\<rightarrow>\<oo>\<leftarrow>\<ff>\<leftarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>op_cat \<CC>\<^esub>\<close>
    by (rule scospan.cf_scospan_the_cf_scospan_is_tm_functor)
  show ?thesis by (rule scospan.is_tm_functor_op[unfolded cat_op_simps])
qed

lemma (in cf_sspan) cf_sspan_the_cf_sspan_is_tm_functor':
  assumes "\<AA>' = \<leftarrow>\<bullet>\<rightarrow>\<^sub>C" and "\<CC>' = \<CC>"
  shows "\<langle>\<aa>\<leftarrow>\<gg>\<leftarrow>\<oo>\<rightarrow>\<ff>\<rightarrow>\<bb>\<rangle>\<^sub>C\<^sub>F\<^bsub>\<CC>\<^esub> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>'"
  unfolding assms by (rule cf_sspan_the_cf_sspan_is_tm_functor)

lemmas [cat_ss_cs_intros] = cf_sspan.cf_sspan_the_cf_sspan_is_tm_functor

text\<open>\newpage\<close>

end