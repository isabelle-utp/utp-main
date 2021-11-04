(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Semicategory\<close>
theory CZH_SMC_Semicategory
  imports 
    CZH_DG_Digraph
    CZH_SMC_Introduction
begin              



subsection\<open>Background\<close>

lemmas [smc_cs_simps] = dg_shared_cs_simps
lemmas [smc_cs_intros] = dg_shared_cs_intros


subsubsection\<open>Slicing\<close>


text\<open>
\<open>Slicing\<close> is a term that is introduced in this work for the description
of the process of the conversion of more specialized mathematical objects to 
their generalizations. 

The terminology was adapted from the informal imperative
object oriented programming, where the term slicing often refers to the
process of copying an object of a subclass type to an object of a 
superclass type \cite{noauthor_wikipedia_2001}\footnote{
\url{https://en.wikipedia.org/wiki/Object_slicing}
}.
However, it is important to note that the term has other meanings in 
programming and computer science.
\<close>

definition smc_dg :: "V \<Rightarrow> V"
  where "smc_dg \<CC> = [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Dom\<rparr>, \<CC>\<lparr>Cod\<rparr>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smc_dg_components[slicing_simps]:
  shows "smc_dg \<CC>\<lparr>Obj\<rparr> = \<CC>\<lparr>Obj\<rparr>"
    and "smc_dg \<CC>\<lparr>Arr\<rparr> = \<CC>\<lparr>Arr\<rparr>"
    and "smc_dg \<CC>\<lparr>Dom\<rparr> = \<CC>\<lparr>Dom\<rparr>"
    and "smc_dg \<CC>\<lparr>Cod\<rparr> = \<CC>\<lparr>Cod\<rparr>"
  unfolding smc_dg_def dg_field_simps by (auto simp: nat_omega_simps)


text\<open>Regular definitions.\<close>

lemma smc_dg_is_arr[slicing_simps]: "f : a \<mapsto>\<^bsub>smc_dg \<CC>\<^esub> b \<longleftrightarrow> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding is_arr_def slicing_simps ..

lemmas [slicing_intros] = smc_dg_is_arr[THEN iffD2]


subsubsection\<open>Composition and composable arrows\<close>


text\<open>
The definition of a set of \<open>composable_arrs\<close> is equivalent to the definition
of \<open>composable pairs\<close> presented on page 10 in \cite{mac_lane_categories_2010}
(see theorem \<open>dg_composable_arrs'\<close> below). 
Nonetheless, the definition is meant to be used sparingly. Normally,
the arrows are meant to be specified explicitly using the predicate 
\<^const>\<open>is_arr\<close>.
\<close>

definition Comp :: V
  where [dg_field_simps]: "Comp = 4\<^sub>\<nat>"

abbreviation Comp_app :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (infixl "\<circ>\<^sub>A\<index>" 55)
  where "Comp_app \<CC> a b \<equiv> \<CC>\<lparr>Comp\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>"

definition composable_arrs :: "V \<Rightarrow> V"
  where "composable_arrs \<CC> = set 
    {[g, f]\<^sub>\<circ> | g f. \<exists>a b c. g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b}"

lemma small_composable_arrs[simp]:
  "small {[g, f]\<^sub>\<circ> | g f. \<exists>a b c. g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b}"
proof(intro down[of _ \<open>\<CC>\<lparr>Arr\<rparr> ^\<^sub>\<times> 2\<^sub>\<nat>\<close>] subsetI)
  fix x assume "x \<in> {[g, f]\<^sub>\<circ> | g f. \<exists>a b c. g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b}"
  then obtain g f a b c 
    where x_def: "x = [g, f]\<^sub>\<circ>" and "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c"  and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    by clarsimp
  with vfsequence_vcpower_two_vpair show "x \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> ^\<^sub>\<times> 2\<^sub>\<nat>"
    unfolding x_def by auto
qed


text\<open>Rules.\<close>

lemma composable_arrsI[smc_cs_intros]:
  assumes "gf = [g, f]\<^sub>\<circ>" and "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "gf \<in>\<^sub>\<circ> composable_arrs \<CC>"
  using assms(2,3) small_composable_arrs 
  unfolding assms(1) composable_arrs_def 
  by auto

lemma composable_arrsE[elim!]:
  assumes "gf \<in>\<^sub>\<circ> composable_arrs \<CC>"
  obtains g f a b c where "gf = [g, f]\<^sub>\<circ>" and "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  using assms small_composable_arrs unfolding composable_arrs_def by clarsimp

lemma small_composable_arrs'[simp]:
  "small {[g, f]\<^sub>\<circ> | g f. g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<and> f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<and> \<CC>\<lparr>Dom\<rparr>\<lparr>g\<rparr> = \<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>}"
proof(intro down[of _ \<open>\<CC>\<lparr>Arr\<rparr> ^\<^sub>\<times> 2\<^sub>\<nat>\<close>] subsetI)
  fix gf assume 
    "gf \<in>{[g, f]\<^sub>\<circ> | g f. g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<and> f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<and> \<CC>\<lparr>Dom\<rparr>\<lparr>g\<rparr> = \<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>}"
  then obtain g f 
    where gf_def: "gf = [g, f]\<^sub>\<circ>" 
      and "g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" 
      and "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" 
      and "\<CC>\<lparr>Dom\<rparr>\<lparr>g\<rparr> = \<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>"
    by clarsimp
  with vfsequence_vcpower_two_vpair show "gf \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> ^\<^sub>\<times> 2\<^sub>\<nat>"
    unfolding gf_def by auto
qed

lemma dg_composable_arrs':
  "set {[g, f]\<^sub>\<circ> | g f. g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<and> f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<and> \<CC>\<lparr>Dom\<rparr>\<lparr>g\<rparr> = \<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>} = 
    composable_arrs \<CC>"
proof-
  have "{[g, f]\<^sub>\<circ> | g f. g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<and> f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<and> \<CC>\<lparr>Dom\<rparr>\<lparr>g\<rparr> = \<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>} = 
    {[g, f]\<^sub>\<circ> | g f. \<exists>a b c. g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b}"
  proof(intro subset_antisym subsetI, unfold mem_Collect_eq; elim exE conjE)
    fix gf g f 
    assume gf_def: "gf = [g, f]\<^sub>\<circ>" 
      and "g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
      and "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" 
      and gf: "\<CC>\<lparr>Dom\<rparr>\<lparr>g\<rparr> = \<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>"
    then obtain a b b' c where g: "g : b' \<mapsto>\<^bsub>\<CC>\<^esub> c" and f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
      by (auto intro!: is_arrI)
    moreover have "b' = b"
      unfolding is_arrD(2,3)[OF g, symmetric] is_arrD(2,3)[OF f, symmetric]
      by (rule gf)
    ultimately have "\<exists>a b c. g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" by auto
    then show "\<exists>g f. gf = [g, f]\<^sub>\<circ> \<and> (\<exists>a b c. g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b)"
      unfolding gf_def by auto
  next
    fix gf g f a b c 
    assume gf_def: "gf = [g, f]\<^sub>\<circ>" and "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    then have "g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" "\<CC>\<lparr>Dom\<rparr>\<lparr>g\<rparr> = \<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>" by auto
    then show 
      "\<exists>g f. gf = [g, f]\<^sub>\<circ> \<and> g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<and> f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<and> \<CC>\<lparr>Dom\<rparr>\<lparr>g\<rparr> = \<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>"
      unfolding gf_def by auto
  qed
  then show ?thesis unfolding composable_arrs_def by auto
qed



subsection\<open>Definition and elementary properties\<close>


text\<open>
The definition of a semicategory that is used in this work is
similar to the definition that was used in \cite{mitchell_dominion_1972}.
It is also a natural generalization of the definition of a category that is
presented in Chapter I-2 in \cite{mac_lane_categories_2010}. The generalization
is performed by omitting the identity and the axioms associated
with it. The amendments to the definitions that are associated with size 
have already been explained in the previous chapter.
\<close>

locale semicategory = \<Z> \<alpha> + vfsequence \<CC> + Comp: vsv \<open>\<CC>\<lparr>Comp\<rparr>\<close> for \<alpha> \<CC> +
  assumes smc_length[smc_cs_simps]: "vcard \<CC> = 5\<^sub>\<nat>"
    and smc_digraph[slicing_intros]: "digraph \<alpha> (smc_dg \<CC>)"
    and smc_Comp_vdomain: "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>) \<longleftrightarrow>
      (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b)"
    and smc_Comp_is_arr: 
      "\<lbrakk> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow> g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and smc_Comp_assoc[smc_cs_simps]:
      "\<lbrakk> h : c \<mapsto>\<^bsub>\<CC>\<^esub> d; g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow>
        (h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)"

lemmas [smc_cs_simps] =
  semicategory.smc_length
  semicategory.smc_Comp_assoc

lemma (in semicategory) smc_Comp_is_arr'[smc_cs_intros]:
  assumes "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "\<CC>' = \<CC>"
  shows "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>'\<^esub> c"
  using assms(1,2) unfolding assms(3) by (rule smc_Comp_is_arr)

lemmas [smc_cs_intros] = 
  semicategory.smc_Comp_is_arr'
  semicategory.smc_Comp_is_arr

lemmas [slicing_intros] = semicategory.smc_digraph


text\<open>Rules.\<close>

lemma (in semicategory) semicategory_axioms'[smc_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "semicategory \<alpha>' \<CC>"
  unfolding assms by (rule semicategory_axioms)

mk_ide rf semicategory_def[unfolded semicategory_axioms_def]
  |intro semicategoryI|
  |dest semicategoryD[dest]|
  |elim semicategoryE[elim]|

lemma semicategoryI':
  assumes "\<Z> \<alpha>"
    and "vfsequence \<CC>"
    and "vsv (\<CC>\<lparr>Comp\<rparr>)"
    and "vcard \<CC> = 5\<^sub>\<nat>"
    and "vsv (\<CC>\<lparr>Dom\<rparr>)"
    and "vsv (\<CC>\<lparr>Cod\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
    and "\<R>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<D>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
    and "\<R>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<And>gf. gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>) \<longleftrightarrow>
      (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b)"
    and "\<And>b c g a f. \<lbrakk> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow> g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and "\<And>c d h b g a f. \<lbrakk> h : c \<mapsto>\<^bsub>\<CC>\<^esub> d; g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow>
        (h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)"
    and "\<CC>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    and "\<And>A B. \<lbrakk> A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; A \<in>\<^sub>\<circ> Vset \<alpha>; B \<in>\<^sub>\<circ> Vset \<alpha> \<rbrakk> \<Longrightarrow>
      (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "semicategory \<alpha> \<CC>"
  by (intro semicategoryI digraphI, unfold slicing_simps)
    (simp_all add: assms  nat_omega_simps smc_dg_def)

lemma semicategoryD':
  assumes "semicategory \<alpha> \<CC>"
  shows "\<Z> \<alpha>"
    and "vfsequence \<CC>"
    and "vsv (\<CC>\<lparr>Comp\<rparr>)"
    and "vcard \<CC> = 5\<^sub>\<nat>"
    and "vsv (\<CC>\<lparr>Dom\<rparr>)"
    and "vsv (\<CC>\<lparr>Cod\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
    and "\<R>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<D>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
    and "\<R>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<And>gf. gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>) \<longleftrightarrow>
      (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b)"
    and "\<And>b c g a f. \<lbrakk> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow> g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and "\<And>c d h b g a f. \<lbrakk> h : c \<mapsto>\<^bsub>\<CC>\<^esub> d; g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow>
        (h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)"
    and "\<CC>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    and "\<And>A B. \<lbrakk> A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; A \<in>\<^sub>\<circ> Vset \<alpha>; B \<in>\<^sub>\<circ> Vset \<alpha> \<rbrakk> \<Longrightarrow>
      (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>"
  by 
    (
      simp_all add: 
        semicategoryD(2-8)[OF assms] 
        digraphD[OF semicategoryD(5)[OF assms], unfolded slicing_simps]
    )

lemma semicategoryE':
  assumes "semicategory \<alpha> \<CC>"
  obtains "\<Z> \<alpha>"
    and "vfsequence \<CC>"
    and "vsv (\<CC>\<lparr>Comp\<rparr>)"
    and "vcard \<CC> = 5\<^sub>\<nat>"
    and "vsv (\<CC>\<lparr>Dom\<rparr>)"
    and "vsv (\<CC>\<lparr>Cod\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
    and "\<R>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<D>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
    and "\<R>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<And>gf. gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>) \<longleftrightarrow>
      (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b)"
    and "\<And>b c g a f. \<lbrakk> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow> g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and "\<And>c d h b g a f. \<lbrakk> h : c \<mapsto>\<^bsub>\<CC>\<^esub> d; g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow>
        (h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)"
    and "\<CC>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    and "\<And>A B. \<lbrakk> A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; A \<in>\<^sub>\<circ> Vset \<alpha>; B \<in>\<^sub>\<circ> Vset \<alpha> \<rbrakk> \<Longrightarrow>
      (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by (simp add: semicategoryD')


text\<open>
While using the sublocale infrastructure in conjunction with the rewrite 
morphisms is plausible for achieving automation of slicing, this approach
has certain limitations. For example, the rewrite morphisms cannot be added to a 
given interpretation that was achieved using the
command @{command sublocale}\footnote{
\url{
https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2019-September/msg00074.html
}
}.
Thus, instead of using a partial solution based on the command 
@{command sublocale}, the rewriting is performed manually for 
selected theorems. However, it is hoped that better automation will be provided
in the future.
\<close>

context semicategory
begin

interpretation dg: digraph \<alpha> \<open>smc_dg \<CC>\<close> by (rule smc_digraph)

sublocale Dom: vsv \<open>\<CC>\<lparr>Dom\<rparr>\<close> by (rule dg.Dom.vsv_axioms[unfolded slicing_simps])
sublocale Cod: vsv \<open>\<CC>\<lparr>Cod\<rparr>\<close> by (rule dg.Cod.vsv_axioms[unfolded slicing_simps])

lemmas_with [unfolded slicing_simps]:
  smc_Dom_vdomain[smc_cs_simps] = dg.dg_Dom_vdomain
  and smc_Dom_vrange = dg.dg_Dom_vrange
  and smc_Cod_vdomain[smc_cs_simps] = dg.dg_Cod_vdomain
  and smc_Cod_vrange = dg.dg_Cod_vrange
  and smc_Obj_vsubset_Vset = dg.dg_Obj_vsubset_Vset
  and smc_Hom_vifunion_in_Vset[smc_cs_intros] = dg.dg_Hom_vifunion_in_Vset
  and smc_Obj_if_Dom_vrange = dg.dg_Obj_if_Dom_vrange
  and smc_Obj_if_Cod_vrange = dg.dg_Obj_if_Cod_vrange
  and smc_is_arrD = dg.dg_is_arrD
  and smc_is_arrE[elim] = dg.dg_is_arrE
  and smc_in_ArrE[elim] = dg.dg_in_ArrE
  and smc_Hom_in_Vset[smc_cs_intros] = dg.dg_Hom_in_Vset
  and smc_Arr_vsubset_Vset = dg.dg_Arr_vsubset_Vset
  and smc_Dom_vsubset_Vset = dg.dg_Dom_vsubset_Vset
  and smc_Cod_vsubset_Vset = dg.dg_Cod_vsubset_Vset
  and smc_Obj_in_Vset = dg.dg_Obj_in_Vset
  and smc_in_Obj_in_Vset[smc_cs_intros] = dg.dg_in_Obj_in_Vset
  and smc_Arr_in_Vset = dg.dg_Arr_in_Vset
  and smc_in_Arr_in_Vset[smc_cs_intros] = dg.dg_in_Arr_in_Vset
  and smc_Dom_in_Vset = dg.dg_Dom_in_Vset
  and smc_Cod_in_Vset = dg.dg_Cod_in_Vset
  and smc_digraph_if_ge_Limit = dg.dg_digraph_if_ge_Limit
  and smc_Dom_app_in_Obj = dg.dg_Dom_app_in_Obj
  and smc_Cod_app_in_Obj = dg.dg_Cod_app_in_Obj
  and smc_Arr_vempty_if_Obj_vempty = dg.dg_Arr_vempty_if_Obj_vempty
  and smc_Dom_vempty_if_Arr_vempty = dg.dg_Dom_vempty_if_Arr_vempty
  and smc_Cod_vempty_if_Arr_vempty = dg.dg_Cod_vempty_if_Arr_vempty

end

lemmas [smc_cs_intros] =
  semicategory.smc_is_arrD(1-3)
  semicategory.smc_Hom_in_Vset


text\<open>Elementary properties.\<close>

lemma smc_eqI:
  assumes "semicategory \<alpha> \<AA>" 
    and "semicategory \<alpha> \<BB>"
    and "\<AA>\<lparr>Obj\<rparr> = \<BB>\<lparr>Obj\<rparr>"
    and "\<AA>\<lparr>Arr\<rparr> = \<BB>\<lparr>Arr\<rparr>"
    and "\<AA>\<lparr>Dom\<rparr> = \<BB>\<lparr>Dom\<rparr>"
    and "\<AA>\<lparr>Cod\<rparr> = \<BB>\<lparr>Cod\<rparr>"
    and "\<AA>\<lparr>Comp\<rparr> = \<BB>\<lparr>Comp\<rparr>"
  shows "\<AA> = \<BB>"
proof-
  interpret \<AA>: semicategory \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: semicategory \<alpha> \<BB> by (rule assms(2))
  show ?thesis
  proof(rule vsv_eqI)
    have dom: "\<D>\<^sub>\<circ> \<AA> = 5\<^sub>\<nat>" by (cs_concl cs_simp: smc_cs_simps V_cs_simps)
    show "\<D>\<^sub>\<circ> \<AA> = \<D>\<^sub>\<circ> \<BB>" by (cs_concl cs_simp: dom smc_cs_simps V_cs_simps)
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<AA> \<Longrightarrow> \<AA>\<lparr>a\<rparr> = \<BB>\<lparr>a\<rparr>" for a 
      by (unfold dom, elim_in_numeral, insert assms) (auto simp: dg_field_simps)
  qed auto
qed

lemma smc_dg_eqI:
  assumes "semicategory \<alpha> \<AA>"
    and "semicategory \<alpha> \<BB>"
    and "\<AA>\<lparr>Comp\<rparr> = \<BB>\<lparr>Comp\<rparr>"
    and "smc_dg \<AA> = smc_dg \<BB>"
  shows "\<AA> = \<BB>"
proof(rule smc_eqI)
  from assms(4) have 
    "smc_dg \<AA>\<lparr>Obj\<rparr> = smc_dg \<BB>\<lparr>Obj\<rparr>"
    "smc_dg \<AA>\<lparr>Arr\<rparr> = smc_dg \<BB>\<lparr>Arr\<rparr>"
    "smc_dg \<AA>\<lparr>Dom\<rparr> = smc_dg \<BB>\<lparr>Dom\<rparr>"
    "smc_dg \<AA>\<lparr>Cod\<rparr> = smc_dg \<BB>\<lparr>Cod\<rparr>" 
    by auto
  then show
    "\<AA>\<lparr>Obj\<rparr> = \<BB>\<lparr>Obj\<rparr>" "\<AA>\<lparr>Arr\<rparr> = \<BB>\<lparr>Arr\<rparr>" "\<AA>\<lparr>Dom\<rparr> = \<BB>\<lparr>Dom\<rparr>" "\<AA>\<lparr>Cod\<rparr> = \<BB>\<lparr>Cod\<rparr>"
    unfolding slicing_simps by simp_all
qed (auto intro: assms)

lemma (in semicategory) smc_def: "\<CC> = [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Dom\<rparr>, \<CC>\<lparr>Cod\<rparr>, \<CC>\<lparr>Comp\<rparr>]\<^sub>\<circ>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> \<CC> = 5\<^sub>\<nat>" by (cs_concl cs_simp: smc_cs_simps V_cs_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Dom\<rparr>, \<CC>\<lparr>Cod\<rparr>, \<CC>\<lparr>Comp\<rparr>]\<^sub>\<circ> = 5\<^sub>\<nat>"
    by (simp add: nat_omega_simps)
  then show "\<D>\<^sub>\<circ> \<CC> = \<D>\<^sub>\<circ> [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Dom\<rparr>, \<CC>\<lparr>Cod\<rparr>, \<CC>\<lparr>Comp\<rparr>]\<^sub>\<circ>"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<CC> \<Longrightarrow> \<CC>\<lparr>a\<rparr> = [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Dom\<rparr>, \<CC>\<lparr>Cod\<rparr>, \<CC>\<lparr>Comp\<rparr>]\<^sub>\<circ>\<lparr>a\<rparr>" 
    for a
    unfolding dom_lhs
    by elim_in_numeral (simp_all add: dg_field_simps nat_omega_simps)
qed auto

lemma (in semicategory) smc_Comp_vdomainI[smc_cs_intros]: 
  assumes "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and "gf = [g, f]\<^sub>\<circ>"
  shows "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>)"
  using assms by (intro smc_Comp_vdomain[THEN iffD2]) auto

lemmas [smc_cs_intros] = semicategory.smc_Comp_vdomainI

lemma (in semicategory) smc_Comp_vdomainE[elim!]: 
  assumes "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>)" 
  obtains g f a b c where "gf = [g, f]\<^sub>\<circ>" and "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
proof-
  from smc_Comp_vdomain[THEN iffD1, OF assms(1)] obtain g f b c a
    where "gf = [g, f]\<^sub>\<circ>" and "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    by clarsimp
  with that show ?thesis by simp
qed

lemma (in semicategory) smc_Comp_vdomain_is_composable_arrs: 
  "\<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>) = composable_arrs \<CC>"
  by (intro vsubset_antisym vsubsetI) (auto intro!: smc_cs_intros)+

lemma (in semicategory) smc_Comp_vrange: "\<R>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof(rule Comp.vsv_vrange_vsubset)
  fix gf assume "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>)"
  from smc_Comp_vdomain[THEN iffD1, OF this] obtain g f b c a
    where gf_def: "gf = [g, f]\<^sub>\<circ>" 
      and g: "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" 
      and f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"  
    by clarsimp
  from semicategory_axioms g f show "\<CC>\<lparr>Comp\<rparr>\<lparr>gf\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: gf_def smc_cs_simps cs_intro: smc_cs_intros)
qed

sublocale semicategory \<subseteq> Comp: pbinop \<open>\<CC>\<lparr>Arr\<rparr>\<close> \<open>\<CC>\<lparr>Comp\<rparr>\<close>
proof unfold_locales
  show "\<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> ^\<^sub>\<times> 2\<^sub>\<nat>"
  proof(intro vsubsetI; unfold smc_Comp_vdomain)
    fix gf assume "\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    then obtain a b c g f 
      where x_def: "gf = [g, f]\<^sub>\<circ>" and "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
      by auto
    then have "g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by auto
    then show "gf \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> ^\<^sub>\<times> 2\<^sub>\<nat>" 
      unfolding x_def by (auto simp: nat_omega_simps)
  qed
  show "\<R>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by (rule smc_Comp_vrange)
qed auto


text\<open>Size.\<close>

lemma (in semicategory) smc_Comp_vsubset_Vset: "\<CC>\<lparr>Comp\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
proof(intro vsubsetI)
  fix gfh assume "gfh \<in>\<^sub>\<circ> \<CC>\<lparr>Comp\<rparr>"
  then obtain gf h 
    where gfh_def: "gfh = \<langle>gf, h\<rangle>" 
      and gf: "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>)" 
      and h: "h \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>)"
    by (blast elim: Comp.vbrelation_vinE)
  from gf obtain g f a b c
    where gf_def: "gf = [g, f]\<^sub>\<circ>" and g: "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"  
    by clarsimp
  from h smc_Comp_vrange have "h \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by auto
  with g f show "gfh \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding gfh_def gf_def 
    by (cs_concl cs_intro: smc_cs_intros V_cs_intros)
qed

lemma (in semicategory) smc_semicategory_in_Vset_4: "\<CC> \<in>\<^sub>\<circ> Vset (\<alpha> + 4\<^sub>\<nat>)"
proof-
  note [folded VPow_iff, folded Vset_succ[OF Ord_\<alpha>], smc_cs_intros] =
    smc_Obj_vsubset_Vset
    smc_Arr_vsubset_Vset
    smc_Dom_vsubset_Vset
    smc_Cod_vsubset_Vset
    smc_Comp_vsubset_Vset
  show ?thesis
    by (subst smc_def, succ_of_numeral)
      (
        cs_concl 
          cs_simp: plus_V_succ_right V_cs_simps 
          cs_intro: smc_cs_intros V_cs_intros
      )
qed

lemma (in semicategory) smc_Comp_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<CC>\<lparr>Comp\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
  using smc_Comp_vsubset_Vset by (meson Vset_in_mono assms(2) vsubset_in_VsetI)

lemma (in semicategory) smc_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<CC> \<in>\<^sub>\<circ> Vset \<beta>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  note [smc_cs_intros] = 
    smc_Obj_in_Vset 
    smc_Arr_in_Vset
    smc_Dom_in_Vset
    smc_Cod_in_Vset
    smc_Comp_in_Vset
  from assms(2) show ?thesis 
    by (subst smc_def) (cs_concl cs_intro: smc_cs_intros V_cs_intros)
qed

lemma (in semicategory) smc_semicategory_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "semicategory \<beta> \<CC>"
  by (rule semicategoryI)
    (
      auto 
        intro: smc_cs_intros 
        simp: smc_cs_simps assms vfsequence_axioms smc_digraph_if_ge_Limit 
    )

lemma small_semicategory[simp]: "small {\<CC>. semicategory \<alpha> \<CC>}"
proof(cases \<open>\<Z> \<alpha>\<close>)
  case True
  from semicategory.smc_in_Vset[of \<alpha>] show ?thesis
    by (intro down[of _ \<open>Vset (\<alpha> + \<omega>)\<close>]) 
      (auto simp: True \<Z>.\<Z>_Limit_\<alpha>\<omega> \<Z>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>.intro \<Z>.\<Z>_\<alpha>_\<alpha>\<omega>)
next
  case False
  then have "{\<CC>. semicategory \<alpha> \<CC>} = {}" by auto
  then show ?thesis by simp
qed

lemma (in \<Z>) semicategories_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "set {\<CC>. semicategory \<alpha> \<CC>} \<in>\<^sub>\<circ> Vset \<beta>"
proof(rule vsubset_in_VsetI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "set {\<CC>. semicategory \<alpha> \<CC>} \<subseteq>\<^sub>\<circ> Vset (\<alpha> + 4\<^sub>\<nat>)"
  proof(intro vsubsetI)
    fix \<CC> assume prems: "\<CC> \<in>\<^sub>\<circ> set {\<CC>. semicategory \<alpha> \<CC>}"
    interpret semicategory \<alpha> \<CC> using prems by simp
    show "\<CC> \<in>\<^sub>\<circ> Vset (\<alpha> + 4\<^sub>\<nat>)"
      unfolding VPow_iff by (rule smc_semicategory_in_Vset_4)
  qed
  from assms(2) show "Vset (\<alpha> + 4\<^sub>\<nat>) \<in>\<^sub>\<circ> Vset \<beta>"
    by (cs_concl cs_intro: V_cs_intros Ord_cs_intros)
qed

lemma semicategory_if_semicategory:
  assumes "semicategory \<beta> \<CC>"
    and "\<Z> \<alpha>"
    and "\<CC>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    and "\<And>A B. \<lbrakk> A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; A \<in>\<^sub>\<circ> Vset \<alpha>; B \<in>\<^sub>\<circ> Vset \<alpha> \<rbrakk> \<Longrightarrow>
      (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "semicategory \<alpha> \<CC>"
proof-
  interpret semicategory \<beta> \<CC> by (rule assms(1))
  interpret \<alpha>: \<Z> \<alpha> by (rule assms(2))
  show ?thesis
  proof(intro semicategoryI)
    show "vfsequence \<CC>" by (simp add: vfsequence_axioms)
    show "digraph \<alpha> (smc_dg \<CC>)"
      by (rule digraph_if_digraph, unfold slicing_simps)
        (auto intro!: assms(1,3,4) slicing_intros)
  qed (auto intro: smc_cs_intros simp: smc_cs_simps)
qed


text\<open>Further elementary properties.\<close>

lemma (in semicategory) smc_Comp_vempty_if_Arr_vempty:
  assumes "\<CC>\<lparr>Arr\<rparr> = 0"
  shows "\<CC>\<lparr>Comp\<rparr> = 0"
  using assms smc_Comp_vrange by (auto intro: Comp.vsv_vrange_vempty)



subsection\<open>Opposite semicategory\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-2 in \cite{mac_lane_categories_2010}.\<close>

definition op_smc :: "V \<Rightarrow> V"
  where "op_smc \<CC> = [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Cod\<rparr>, \<CC>\<lparr>Dom\<rparr>, fflip (\<CC>\<lparr>Comp\<rparr>)]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma op_smc_components:
  shows [smc_op_simps]: "op_smc \<CC>\<lparr>Obj\<rparr> = \<CC>\<lparr>Obj\<rparr>"
    and [smc_op_simps]: "op_smc \<CC>\<lparr>Arr\<rparr> = \<CC>\<lparr>Arr\<rparr>"
    and [smc_op_simps]: "op_smc \<CC>\<lparr>Dom\<rparr> = \<CC>\<lparr>Cod\<rparr>"
    and [smc_op_simps]: "op_smc \<CC>\<lparr>Cod\<rparr> = \<CC>\<lparr>Dom\<rparr>"
    and "op_smc \<CC>\<lparr>Comp\<rparr> = fflip (\<CC>\<lparr>Comp\<rparr>)"
  unfolding op_smc_def dg_field_simps by (auto simp: nat_omega_simps)

lemma op_smc_component_intros[smc_op_intros]:
  shows "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> a \<in>\<^sub>\<circ> op_smc \<CC>\<lparr>Obj\<rparr>"
    and "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<Longrightarrow> f \<in>\<^sub>\<circ> op_smc \<CC>\<lparr>Arr\<rparr>"
  unfolding smc_op_simps by simp_all


text\<open>Slicing.\<close>

lemma op_dg_smc_dg[slicing_commute]: "op_dg (smc_dg \<CC>) = smc_dg (op_smc \<CC>)"
  unfolding smc_dg_def op_smc_def op_dg_def dg_field_simps
  by (simp add: nat_omega_simps)


text\<open>Regular definitions.\<close>

lemma op_smc_Comp_vdomain[smc_op_simps]: 
  "\<D>\<^sub>\<circ> (op_smc \<CC>\<lparr>Comp\<rparr>) = (\<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>))\<inverse>\<^sub>\<bullet>"
  unfolding op_smc_components by simp

lemma op_smc_is_arr[smc_op_simps]: "f : b \<mapsto>\<^bsub>op_smc \<CC>\<^esub> a \<longleftrightarrow> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding smc_op_simps is_arr_def by auto

lemmas [smc_op_intros] = op_smc_is_arr[THEN iffD2]

lemma (in semicategory) op_smc_Comp_vrange[smc_op_simps]: 
  "\<R>\<^sub>\<circ> (op_smc \<CC>\<lparr>Comp\<rparr>) = \<R>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>)"
  using Comp.vrange_fflip unfolding op_smc_components by simp

lemmas [smc_op_simps] = semicategory.op_smc_Comp_vrange

lemma (in semicategory) op_smc_Comp[smc_op_simps]: 
  assumes "f : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "g : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "g \<circ>\<^sub>A\<^bsub>op_smc \<CC>\<^esub> f = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g"
  using assms 
  unfolding op_smc_components 
  by (auto intro!: fflip_app smc_cs_intros)

lemmas [smc_op_simps] = semicategory.op_smc_Comp

lemma op_smc_Hom[smc_op_simps]: "Hom (op_smc \<CC>) a b = Hom \<CC> b a"
  unfolding smc_op_simps by simp


subsubsection\<open>Further properties\<close>

lemma (in semicategory) semicategory_op[smc_op_intros]: 
  "semicategory \<alpha> (op_smc \<CC>)"
proof(intro semicategoryI)
  from semicategory_axioms smc_digraph show "digraph \<alpha> (smc_dg (op_smc \<CC>))"
    by (cs_concl cs_simp: slicing_commute[symmetric] cs_intro: dg_op_intros)
  show "vfsequence (op_smc \<CC>)" unfolding op_smc_def by simp
  show "vcard (op_smc \<CC>) = 5\<^sub>\<nat>"
    unfolding op_smc_def by (simp add: nat_omega_simps)
  show "(gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (op_smc \<CC>\<lparr>Comp\<rparr>)) \<longleftrightarrow>
    (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>op_smc \<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>op_smc \<CC>\<^esub> b)"
    for gf
  proof(rule iffI; unfold smc_op_simps)
    assume prems: "gf \<in>\<^sub>\<circ> (\<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>))\<inverse>\<^sub>\<bullet>"
    then obtain g' f' where gf_def: "gf = [g', f']\<^sub>\<circ>" by clarsimp
    with prems have "[f', g']\<^sub>\<circ> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>)" by (auto intro: smc_cs_intros)
    with smc_Comp_vdomain show 
      "\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : c \<mapsto>\<^bsub>\<CC>\<^esub> b \<and> f : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
      unfolding gf_def by auto
  next
    assume "\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : c \<mapsto>\<^bsub>\<CC>\<^esub> b \<and> f : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
    then obtain g f b c a 
      where gf_def: "gf = [g, f]\<^sub>\<circ>" and g: "g : c \<mapsto>\<^bsub>\<CC>\<^esub> b" and f: "f : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
      by clarsimp
    then have "g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" and "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by force+
    from g f have "[f, g]\<^sub>\<circ> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>)"
      unfolding gf_def by (intro smc_Comp_vdomainI) auto
    then show "gf \<in>\<^sub>\<circ> (\<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>))\<inverse>\<^sub>\<bullet>" 
      unfolding gf_def by (auto intro: smc_cs_intros)
  qed
  from semicategory_axioms show 
    "\<lbrakk> g : b \<mapsto>\<^bsub>op_smc \<CC>\<^esub> c; f : a \<mapsto>\<^bsub>op_smc \<CC>\<^esub> b \<rbrakk> \<Longrightarrow> 
      g \<circ>\<^sub>A\<^bsub>op_smc \<CC>\<^esub> f : a \<mapsto>\<^bsub>op_smc \<CC>\<^esub> c"
    for g b c f a
    unfolding smc_op_simps 
    by (cs_concl cs_simp: smc_op_simps cs_intro: smc_cs_intros)
  fix h c d g b f a
  assume "h : c \<mapsto>\<^bsub>op_smc \<CC>\<^esub> d" "g : b \<mapsto>\<^bsub>op_smc \<CC>\<^esub> c" "f : a \<mapsto>\<^bsub>op_smc \<CC>\<^esub> b"
  with semicategory_axioms show
    "(h \<circ>\<^sub>A\<^bsub>op_smc \<CC>\<^esub> g) \<circ>\<^sub>A\<^bsub>op_smc \<CC>\<^esub> f = h \<circ>\<^sub>A\<^bsub>op_smc \<CC>\<^esub> (g \<circ>\<^sub>A\<^bsub>op_smc \<CC>\<^esub> f)"
    unfolding smc_op_simps
    by (cs_concl cs_simp: smc_op_simps smc_cs_simps cs_intro: smc_cs_intros)
qed (auto simp: fflip_vsv op_smc_components(5))

lemmas semicategory_op[smc_op_intros] = semicategory.semicategory_op

lemma (in semicategory) smc_op_smc_op_smc[smc_op_simps]: "op_smc (op_smc \<CC>) = \<CC>"
  by (rule smc_eqI, unfold smc_op_simps op_smc_components)
    (
      auto simp: 
        Comp.pbinop_fflip_fflip 
        semicategory_axioms
        semicategory.semicategory_op semicategory_op
        intro: smc_cs_intros
    )

lemmas smc_op_smc_op_smc[smc_op_simps] = semicategory.smc_op_smc_op_smc

lemma eq_op_smc_iff[smc_op_simps]: 
  assumes "semicategory \<alpha> \<AA>" and "semicategory \<alpha> \<BB>"
  shows "op_smc \<AA> = op_smc \<BB> \<longleftrightarrow> \<AA> = \<BB>"
proof
  interpret \<AA>: semicategory \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: semicategory \<alpha> \<BB> by (rule assms(2))
  assume prems: "op_smc \<AA> = op_smc \<BB>" show "\<AA> = \<BB>"
  proof(rule smc_eqI)
    show 
      "\<AA>\<lparr>Obj\<rparr> = \<BB>\<lparr>Obj\<rparr>" 
      "\<AA>\<lparr>Arr\<rparr> = \<BB>\<lparr>Arr\<rparr>"
      "\<AA>\<lparr>Dom\<rparr> = \<BB>\<lparr>Dom\<rparr>" 
      "\<AA>\<lparr>Cod\<rparr> = \<BB>\<lparr>Cod\<rparr>"
      "\<AA>\<lparr>Comp\<rparr> = \<BB>\<lparr>Comp\<rparr>"
      by (metis prems \<AA>.smc_op_smc_op_smc \<BB>.smc_op_smc_op_smc)+
  qed (auto intro: assms)
qed auto



subsection\<open>Arrow with a domain and a codomain\<close>

lemma (in semicategory) smc_assoc_helper:
  assumes "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and "h : c \<mapsto>\<^bsub>\<CC>\<^esub> d"
    and "q : b \<mapsto>\<^bsub>\<CC>\<^esub> d"
    and "h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = q"
  shows "h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) = q \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
  using semicategory_axioms assms(1-4)
  by (cs_concl cs_simp: semicategory.smc_Comp_assoc[symmetric] assms(5))

lemma (in semicategory) smc_pattern_rectangle_right:
  assumes "aa' : a \<mapsto>\<^bsub>\<CC>\<^esub> a'" 
    and "a'a'' : a' \<mapsto>\<^bsub>\<CC>\<^esub> a''"
    and "a''b'' : a'' \<mapsto>\<^bsub>\<CC>\<^esub> b''"
    and "ab : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "bb' : b \<mapsto>\<^bsub>\<CC>\<^esub> b'"
    and "b'b'' : b' \<mapsto>\<^bsub>\<CC>\<^esub> b''"
    and "a'b' : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'"
    and "a'b' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> aa' = bb' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ab"
    and "b'b'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> a'b' = a''b'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> a'a''"
  shows "a''b'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (a'a'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> aa') = (b'b'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> bb') \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ab"
proof-
  from semicategory_axioms assms(3,2,1) have 
    "a''b'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (a'a'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> aa') = (a''b'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> a'a'') \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> aa'"
    by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  also have "\<dots> = (b'b'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> a'b') \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> aa'" unfolding assms(9) ..
  also from semicategory_axioms assms(1,6,7) have 
    "\<dots> = b'b'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (a'b' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> aa')"
    by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  also have "\<dots> = b'b'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (bb' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ab)" unfolding assms(8) ..
  also from semicategory_axioms assms(6,5,4) have 
    "\<dots> = (b'b'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> bb') \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ab" 
    by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  finally show ?thesis by simp
qed

lemmas (in semicategory) smc_pattern_rectangle_left = 
  smc_pattern_rectangle_right[symmetric]



subsection\<open>Monic arrow and epic arrow\<close>


text\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>

definition is_monic_arr :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_monic_arr \<CC> b c m \<longleftrightarrow>
    m : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and>
    (
      \<forall>f g a.
        f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<longrightarrow> g : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<longrightarrow> m \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = m \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g \<longrightarrow> f = g
    )"

syntax "_is_monic_arr" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>_ : _ \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<index> _\<close> [51, 51, 51] 51)
translations "m : b \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>\<CC>\<^esub> c" \<rightleftharpoons> "CONST is_monic_arr \<CC> b c m"

definition is_epic_arr :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_epic_arr \<CC> a b e \<equiv> e : b \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>op_smc \<CC>\<^esub> a"

syntax "_is_epic_arr" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>_ : _ \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<index> _\<close> [51, 51, 51] 51)
translations "e : a \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> b" \<rightleftharpoons> "CONST is_epic_arr \<CC> a b e"


text\<open>Rules.\<close>

mk_ide rf is_monic_arr_def
  |intro is_monic_arrI|
  |dest is_monic_arrD[dest]|
  |elim is_monic_arrE[elim!]|

lemmas [smc_arrow_cs_intros] = is_monic_arrD(1)

lemma (in semicategory) is_epic_arrI:
  assumes "e : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "\<And>f g c. \<lbrakk> f : b \<mapsto>\<^bsub>\<CC>\<^esub> c; g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> e = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> e \<rbrakk> \<Longrightarrow>
      f = g"
  shows "e : a \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> b"
  unfolding is_epic_arr_def
proof(intro is_monic_arrI, unfold smc_op_simps)
  fix f g a 
  assume prems:
    "f : b \<mapsto>\<^bsub>\<CC>\<^esub> a" "g : b \<mapsto>\<^bsub>\<CC>\<^esub> a" "e \<circ>\<^sub>A\<^bsub>op_smc \<CC>\<^esub> f = e \<circ>\<^sub>A\<^bsub>op_smc \<CC>\<^esub> g"
  show "f = g"
  proof-
    from prems(3,1,2) assms(1) semicategory_axioms have "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> e = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> e"
      by 
        (
          cs_prems 
            cs_simp: smc_cs_simps smc_op_simps
            cs_intro: smc_cs_intros smc_op_intros
        )
      simp
    from assms(2)[OF prems(2,1) this] show ?thesis ..
  qed
qed (rule assms(1))

lemma is_epic_arr_is_arr[smc_arrow_cs_intros, dest]:
  assumes "e : a \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> b"
  shows "e : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  using assms unfolding is_epic_arr_def is_monic_arr_def smc_op_simps by simp

lemma (in semicategory) is_epic_arrD[dest]:
  assumes "e : a \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> b"
  shows "e : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "\<And>f g c. \<lbrakk> f : b \<mapsto>\<^bsub>\<CC>\<^esub> c; g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> e = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> e \<rbrakk> \<Longrightarrow>
      f = g"
proof-
  note is_monic_arrD = 
    assms(1)[unfolded is_epic_arr_def is_monic_arr_def smc_op_simps] 
  from is_monic_arrD[THEN conjunct1] show e: "e : a \<mapsto>\<^bsub>\<CC>\<^esub> b" by simp
  fix f g c 
  assume prems: "f : b \<mapsto>\<^bsub>\<CC>\<^esub> c" "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> e = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> e"
  with semicategory_axioms e have "e \<circ>\<^sub>A\<^bsub>op_smc \<CC>\<^esub> f = e \<circ>\<^sub>A\<^bsub>op_smc \<CC>\<^esub> g"
    by (cs_concl cs_simp: smc_op_simps cs_intro: smc_cs_intros)
  then show "f = g" 
    by (rule is_monic_arrD[THEN conjunct2, rule_format, OF prems(1,2)])
qed

lemma (in semicategory) is_epic_arrE[elim!]:
  assumes "e : a \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> b"
  obtains "e : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "\<And>f g c. \<lbrakk> f : b \<mapsto>\<^bsub>\<CC>\<^esub> c; g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> e = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> e \<rbrakk> \<Longrightarrow> 
      f = g"
  using assms by auto


text\<open>Elementary properties.\<close>

lemma (in semicategory) op_smc_is_epic_arr[smc_op_simps]: 
  "f : b \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>op_smc \<CC>\<^esub> a \<longleftrightarrow> f : a \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>\<CC>\<^esub> b"
  unfolding is_monic_arr_def is_epic_arr_def smc_op_simps ..

lemma (in semicategory) op_smc_is_monic_arr[smc_op_simps]: 
  "f : b \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>op_smc \<CC>\<^esub> a \<longleftrightarrow> f : a \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> b"
  unfolding is_monic_arr_def is_epic_arr_def smc_op_simps ..

lemma (in semicategory) smc_Comp_is_monic_arr[smc_arrow_cs_intros]:
  assumes "g : b \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>\<CC>\<^esub> b"
  shows "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>\<CC>\<^esub> c"
proof(intro is_monic_arrI)
  from assms show "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c" by (auto intro: smc_cs_intros)
  fix f' g' a'
  assume f': "f' : a' \<mapsto>\<^bsub>\<CC>\<^esub> a"
    and g': "g' : a' \<mapsto>\<^bsub>\<CC>\<^esub> a"
    and "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g'"
  with assms have "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f') = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g')"
    by (force simp: smc_Comp_assoc)
  moreover from assms have "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' : a' \<mapsto>\<^bsub>\<CC>\<^esub> b" "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g' : a' \<mapsto>\<^bsub>\<CC>\<^esub> b" 
    by (auto intro: f' g' smc_cs_intros)
  ultimately have "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g'" using assms(1) by clarsimp
  with assms f' g' show "f' = g'" by clarsimp
qed

lemmas [smc_arrow_cs_intros] = semicategory.smc_Comp_is_monic_arr

lemma (in semicategory) smc_Comp_is_epic_arr[smc_arrow_cs_intros]: 
  assumes "g : b \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> b"
  shows "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> c"
proof-
  from assms op_smc_is_arr have "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
    unfolding is_epic_arr_def by auto
  with semicategory_axioms have "f \<circ>\<^sub>A\<^bsub>op_smc \<CC>\<^esub> g = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    by (cs_concl cs_simp: smc_op_simps)
  with 
    semicategory.smc_Comp_is_monic_arr[
      OF semicategory_op,
      OF assms(2,1)[unfolded is_epic_arr_def],
      folded is_epic_arr_def
      ]
  show ?thesis    
    by auto
qed

lemmas [smc_arrow_cs_intros] = semicategory.smc_Comp_is_epic_arr

lemma (in semicategory) smc_Comp_is_monic_arr_is_monic_arr:
  assumes "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>\<CC>\<^esub> c"
  shows "f : a \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>\<CC>\<^esub> b"
proof(intro is_monic_arrI)
  fix f' g' a'
  assume f': "f' : a' \<mapsto>\<^bsub>\<CC>\<^esub> a" 
    and g': "g' : a' \<mapsto>\<^bsub>\<CC>\<^esub> a" 
    and f'gg'g: "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g'"
  from assms(1,2) f' g' have "(g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f' = (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g'"
    by (auto simp: smc_Comp_assoc f'gg'g)
  with assms(3) f' g' show "f' = g'" by clarsimp
qed (simp add: assms(2))

lemma (in semicategory) smc_Comp_is_epic_arr_is_epic_arr:
  assumes "g : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and "f : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g : a \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> c"
  shows "f : b \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> c"
proof-
  from assms have "g : b \<mapsto>\<^bsub>op_smc \<CC>\<^esub> a" "f : c \<mapsto>\<^bsub>op_smc \<CC>\<^esub> b" 
    unfolding smc_op_simps by simp_all 
  moreover from semicategory_axioms assms have "g \<circ>\<^sub>A\<^bsub>op_smc \<CC>\<^esub> f : a \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> c"
    by (cs_concl cs_simp: smc_op_simps)
  ultimately show ?thesis 
    using 
      semicategory.smc_Comp_is_monic_arr_is_monic_arr[
        OF semicategory_op, folded is_epic_arr_def
        ]
    by auto
qed



subsection\<open>Idempotent arrow\<close>


text\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>

definition is_idem_arr :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_idem_arr \<CC> b f \<longleftrightarrow> f : b \<mapsto>\<^bsub>\<CC>\<^esub> b \<and> f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = f"

syntax "_is_idem_arr" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" (\<open>_ : \<mapsto>\<^sub>i\<^sub>d\<^sub>e\<index> _\<close> [51, 51] 51)
translations "f : \<mapsto>\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<CC>\<^esub> b" \<rightleftharpoons> "CONST is_idem_arr \<CC> b f"


text\<open>Rules.\<close>

mk_ide rf is_idem_arr_def
  |intro is_idem_arrI|
  |dest is_idem_arrD[dest]|
  |elim is_idem_arrE[elim!]|

lemmas [smc_cs_simps] = is_idem_arrD(2)


text\<open>Elementary properties.\<close>

lemma (in semicategory) op_smc_is_idem_arr[smc_op_simps]: 
  "f : \<mapsto>\<^sub>i\<^sub>d\<^sub>e\<^bsub>op_smc \<CC>\<^esub> b \<longleftrightarrow> f : \<mapsto>\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<CC>\<^esub> b"
  using op_smc_Comp unfolding is_idem_arr_def smc_op_simps by auto



subsection\<open>Terminal object and initial object\<close>


text\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>

definition obj_terminal :: "V \<Rightarrow> V \<Rightarrow> bool"
  where "obj_terminal \<CC> t \<longleftrightarrow> 
    t \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<and> (\<forall>a. a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<longrightarrow> (\<exists>!f. f : a \<mapsto>\<^bsub>\<CC>\<^esub> t))"

definition obj_initial :: "V \<Rightarrow> V \<Rightarrow> bool"
  where "obj_initial \<CC> \<equiv> obj_terminal (op_smc \<CC>)"


text\<open>Rules.\<close>

mk_ide rf obj_terminal_def
  |intro obj_terminalI|
  |dest obj_terminalD[dest]|
  |elim obj_terminalE[elim]|

lemma obj_initialI:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "\<And>b. b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<exists>!f. f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
  shows "obj_initial \<CC> a"
  unfolding obj_initial_def
  by (simp add: obj_terminalI[of _ \<open>op_smc \<CC>\<close>, unfolded smc_op_simps, OF assms])

lemma obj_initialD[dest]:
  assumes "obj_initial \<CC> a" 
  shows "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "\<And>b. b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<exists>!f. f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"   
  by 
    (
      simp_all add: 
        obj_terminalD[OF assms[unfolded obj_initial_def], unfolded smc_op_simps]
    )

lemma obj_initialE[elim]:
  assumes "obj_initial \<CC> a" 
  obtains "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "\<And>b. b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<exists>!f. f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"   
  using assms by (auto simp: obj_initialD)


text\<open>Elementary properties.\<close>

lemma op_smc_obj_initial[smc_op_simps]: 
  "obj_initial (op_smc \<CC>) = obj_terminal \<CC>"
  unfolding obj_initial_def obj_terminal_def smc_op_simps ..

lemma op_smc_obj_terminal[smc_op_simps]: 
  "obj_terminal (op_smc \<CC>) = obj_initial \<CC>"
  unfolding obj_initial_def obj_terminal_def smc_op_simps ..



subsection\<open>Null object\<close>


text\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>

definition obj_null :: "V \<Rightarrow> V \<Rightarrow> bool"
  where "obj_null \<CC> a \<longleftrightarrow> obj_initial \<CC> a \<and> obj_terminal \<CC> a"


text\<open>Rules.\<close>

mk_ide rf obj_null_def
  |intro obj_nullI|
  |dest obj_nullD[dest]|
  |elim obj_nullE[elim]|


text\<open>Elementary properties.\<close>

lemma op_smc_obj_null[smc_op_simps]: "obj_null (op_smc \<CC>) a = obj_null \<CC> a"
  unfolding obj_null_def smc_op_simps by auto



subsection\<open>Zero arrow\<close>

definition is_zero_arr :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_zero_arr \<CC> a b h \<longleftrightarrow>
    (\<exists>z g f. obj_null \<CC> z \<and> h = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> z \<and> g : z \<mapsto>\<^bsub>\<CC>\<^esub> b)"

syntax "_is_zero_arr" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>_ : _ \<mapsto>\<^sub>0\<index> _\<close> [51, 51, 51] 51)
translations "h : a \<mapsto>\<^sub>0\<^bsub>\<CC>\<^esub> b" \<rightleftharpoons> "CONST is_zero_arr \<CC> a b h"


text\<open>Rules.\<close>

lemma is_zero_arrI:
  assumes "obj_null \<CC> z" 
    and "h = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f" 
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> z" 
    and "g : z \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "h : a \<mapsto>\<^sub>0\<^bsub>\<CC>\<^esub> b"
  using assms unfolding is_zero_arr_def by auto

lemma is_zero_arrD[dest]:
  assumes "h : a \<mapsto>\<^sub>0\<^bsub>\<CC>\<^esub> b"
  shows "\<exists>z g f. obj_null \<CC> z \<and> h = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> z \<and> g : z \<mapsto>\<^bsub>\<CC>\<^esub> b"
  using assms unfolding is_zero_arr_def by simp

lemma is_zero_arrE[elim]:
  assumes "h : a \<mapsto>\<^sub>0\<^bsub>\<CC>\<^esub> b"
  obtains z g f 
    where "obj_null \<CC> z"
      and "h = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f" 
      and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> z" 
      and "g : z \<mapsto>\<^bsub>\<CC>\<^esub> b"
  using assms by auto


text\<open>Elementary properties.\<close>

lemma (in semicategory) op_smc_is_zero_arr[smc_op_simps]: 
  "f : b \<mapsto>\<^sub>0\<^bsub>op_smc \<CC>\<^esub> a \<longleftrightarrow> f : a \<mapsto>\<^sub>0\<^bsub>\<CC>\<^esub> b"
  using op_smc_Comp unfolding is_zero_arr_def smc_op_simps by metis

lemma (in semicategory) smc_is_zero_arr_Comp_right:
  assumes "h : b \<mapsto>\<^sub>0\<^bsub>\<CC>\<^esub> c" and "h' : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h' : a \<mapsto>\<^sub>0\<^bsub>\<CC>\<^esub> c"
proof-
  from assms(1) obtain z g f  
    where "obj_null \<CC> z" 
      and "h = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f" 
      and "f : b \<mapsto>\<^bsub>\<CC>\<^esub> z" 
      and "g : z \<mapsto>\<^bsub>\<CC>\<^esub> c"
    by auto 
  with assms show ?thesis 
    by (auto simp: smc_cs_simps intro: is_zero_arrI smc_cs_intros) 
qed

lemmas [smc_arrow_cs_intros] = semicategory.smc_is_zero_arr_Comp_right

lemma (in semicategory) smc_is_zero_arr_Comp_left:
  assumes "h' : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "h : a \<mapsto>\<^sub>0\<^bsub>\<CC>\<^esub> b" 
  shows "h' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h : a \<mapsto>\<^sub>0\<^bsub>\<CC>\<^esub> c"
proof-
  from assms(2) obtain z g f 
    where "obj_null \<CC> z" 
      and "h = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f" 
      and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> z" 
      and "g : z \<mapsto>\<^bsub>\<CC>\<^esub> b"
    by auto
  with assms(1) show ?thesis
    by (intro is_zero_arrI[of _ _ _ \<open>h' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g\<close>]) 
      (auto simp: smc_Comp_assoc intro: is_zero_arrI smc_cs_intros)
qed

lemmas [smc_arrow_cs_intros] = semicategory.smc_is_zero_arr_Comp_left

text\<open>\newpage\<close>

end