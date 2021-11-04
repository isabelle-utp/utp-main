(* Copyright 2020 (C) Mihails Milehins *)

section\<open>Ordinal numbers\<close>
theory CZH_ECAT_Ordinal
  imports CZH_ECAT_Small_Order
begin



subsection\<open>Background\<close>


text\<open>
The content of this section is based on the treatment of the ordinal numbers
from the perspective of category theory as exposed, for example,
in Chapter I-2 in \cite{mac_lane_categories_2010}.
\<close>

named_theorems cat_ordinal_cs_simps
named_theorems cat_ordinal_cs_intros



subsection\<open>Arrows associated with an ordinal number\<close>

definition ordinal_arrs :: "V \<Rightarrow> V"
  where "ordinal_arrs A \<equiv> set {[a, b]\<^sub>\<circ> | a b. a \<in>\<^sub>\<circ> A \<and> b \<in>\<^sub>\<circ> A \<and> a \<le> b}"

lemma small_ordinal_arrs[simp]: 
  "small {[a, b]\<^sub>\<circ> | a b. a \<in>\<^sub>\<circ> A \<and> b \<in>\<^sub>\<circ> A \<and> a \<le> b}"
  by (rule down[where x=\<open>A \<times>\<^sub>\<bullet> A\<close>]) auto


text\<open>Rules.\<close>

lemma ordinal_arrsI[cat_ordinal_cs_intros]:
  assumes "x = [a, b]\<^sub>\<circ>" and "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "a \<le> b" 
  shows "x \<in>\<^sub>\<circ> ordinal_arrs A"
  using assms unfolding ordinal_arrs_def by auto

lemma ordinal_arrsD[dest]:
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> ordinal_arrs A"
  shows "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "a \<le> b" 
  using assms unfolding ordinal_arrs_def by auto

lemma ordinal_arrsE[elim]:
  assumes "x \<in>\<^sub>\<circ> ordinal_arrs A"
  obtains a b where "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "a \<le> b" and "x = [a, b]\<^sub>\<circ>"
  using assms unfolding ordinal_arrs_def by clarsimp



subsection\<open>Composable arrows\<close>

abbreviation ordinal_composable :: "V \<Rightarrow> V"
  where "ordinal_composable A \<equiv> set
    {
      [[b, c]\<^sub>\<circ>, [a, b]\<^sub>\<circ>]\<^sub>\<circ> | a b c. 
        a \<in>\<^sub>\<circ> A \<and> b \<in>\<^sub>\<circ> A \<and> c \<in>\<^sub>\<circ> A \<and> a \<le> b \<and> b \<le> c
    }"

lemma small_ordinal_composable[simp]: 
  "small
    {
      [[b, c]\<^sub>\<circ>, [a, b]\<^sub>\<circ>]\<^sub>\<circ> | a b c.
        a \<in>\<^sub>\<circ> A \<and> b \<in>\<^sub>\<circ> A \<and> c \<in>\<^sub>\<circ> A \<and> a \<le> b \<and> b \<le> c
    }"
  by (rule down[where x=\<open>(A \<times>\<^sub>\<bullet> A) \<times>\<^sub>\<bullet> (A \<times>\<^sub>\<bullet> A)\<close>]) auto


text\<open>Rules.\<close>

lemma ordinal_composableI[cat_ordinal_cs_intros]:
  assumes "x = [[b, c]\<^sub>\<circ>, [a, b]\<^sub>\<circ>]\<^sub>\<circ>" 
    and "a \<in>\<^sub>\<circ> A"
    and "b \<in>\<^sub>\<circ> A"
    and "c \<in>\<^sub>\<circ> A"
    and "a \<le> b"
    and "b \<le> c"
  shows "x \<in>\<^sub>\<circ> ordinal_composable A"
  using assms by auto

lemma ordinal_composableD[dest]:
  assumes "[[b, c]\<^sub>\<circ>, [a, b]\<^sub>\<circ>]\<^sub>\<circ> \<in>\<^sub>\<circ> ordinal_composable A"
  shows "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "c \<in>\<^sub>\<circ> A" and "a \<le> b" and "b \<le> c"
  using assms by auto

lemma ordinal_composableE[elim]:
  assumes "x \<in>\<^sub>\<circ> ordinal_composable A"
  obtains a b c 
    where "x = [[b, c]\<^sub>\<circ>, [a, b]\<^sub>\<circ>]\<^sub>\<circ>"
      and "a \<in>\<^sub>\<circ> A" 
      and "b \<in>\<^sub>\<circ> A" 
      and "c \<in>\<^sub>\<circ> A"
      and "a \<le> b"
      and "b \<le> c"
  using assms by clarsimp



subsection\<open>Ordinal number as a category\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cat_ordinal :: "V \<Rightarrow> V"
  where "cat_ordinal A =
    [
      A,
      ordinal_arrs A,
      (\<lambda>f\<in>\<^sub>\<circ>ordinal_arrs A. f\<lparr>0\<rparr>),
      (\<lambda>f\<in>\<^sub>\<circ>ordinal_arrs A. f\<lparr>1\<^sub>\<nat>\<rparr>),
      (\<lambda>gf\<in>\<^sub>\<circ>ordinal_composable A. [gf\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>0\<rparr>, gf\<lparr>0\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>]\<^sub>\<circ>),
      (\<lambda>x\<in>\<^sub>\<circ>A. [x, x]\<^sub>\<circ>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_ordinal_components:
  shows [cat_ordinal_cs_simps]: "cat_ordinal A\<lparr>Obj\<rparr> = A"
    and [cat_ordinal_cs_simps]: "cat_ordinal A\<lparr>Arr\<rparr> = ordinal_arrs A"
    and "cat_ordinal A\<lparr>Dom\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>ordinal_arrs A. f\<lparr>0\<rparr>)"
    and "cat_ordinal A\<lparr>Cod\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>ordinal_arrs A. f\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "cat_ordinal A\<lparr>Comp\<rparr> =
      (\<lambda>gf\<in>\<^sub>\<circ>ordinal_composable A. [gf\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>0\<rparr>, gf\<lparr>0\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>]\<^sub>\<circ>)"
    and "cat_ordinal A\<lparr>CId\<rparr> = (\<lambda>x\<in>\<^sub>\<circ>A. [x, x]\<^sub>\<circ>)"
  unfolding cat_ordinal_def dg_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Domain\<close>

mk_VLambda cat_ordinal_components(3)
  |vsv cat_ordinal_Dom_vsv[cat_ordinal_cs_intros]|
  |vdomain 
    cat_ordinal_Dom_vdomain[
      folded cat_ordinal_components, cat_ordinal_cs_simps
      ]
  |

lemma cat_ordinal_Dom_app[cat_ordinal_cs_simps]:
  assumes "x \<in>\<^sub>\<circ> cat_ordinal A\<lparr>Arr\<rparr>" and "x = [a, b]\<^sub>\<circ>"
  shows "cat_ordinal A\<lparr>Dom\<rparr>\<lparr>x\<rparr> = a"
  using assms(1) unfolding assms(2) cat_ordinal_components by auto

lemma cat_ordinal_Dom_vrange: "\<R>\<^sub>\<circ> (cat_ordinal A\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> cat_ordinal A\<lparr>Obj\<rparr>"
  unfolding cat_ordinal_components
  by (intro vrange_VLambda_vsubset, elim ordinal_arrsE) simp


subsubsection\<open>Codomain\<close>

mk_VLambda cat_ordinal_components(4)
  |vsv cat_ordinal_Cod_vsv[cat_ordinal_cs_intros]|
  |vdomain 
    cat_ordinal_Cod_vdomain[
      folded cat_ordinal_components, cat_ordinal_cs_simps
      ]
  |

lemma cat_ordinal_Cod_app[cat_ordinal_cs_simps]:
  assumes "x \<in>\<^sub>\<circ> cat_ordinal A\<lparr>Arr\<rparr>" and "x = [a, b]\<^sub>\<circ>"
  shows "cat_ordinal A\<lparr>Cod\<rparr>\<lparr>x\<rparr> = b"
  using assms(1)
  unfolding assms(2) cat_ordinal_components 
  by (auto simp: nat_omega_simps)

lemma cat_ordinal_Cod_vrange: "\<R>\<^sub>\<circ> (cat_ordinal A\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> cat_ordinal A\<lparr>Obj\<rparr>"
  unfolding cat_ordinal_components
  by (intro vrange_VLambda_vsubset, elim ordinal_arrsE) 
    (simp add: nat_omega_simps)


subsubsection\<open>Arrow with a domain and a codomain\<close>


text\<open>Rules.\<close>

lemma cat_ordinal_is_arrI[cat_ordinal_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "a \<le> b" and "f = [a, b]\<^sub>\<circ>"
  shows "f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"
proof(intro is_arrI, unfold cat_ordinal_components(2))
  from assms show "f \<in>\<^sub>\<circ> ordinal_arrs A" by (intro ordinal_arrsI)
  then show "cat_ordinal A\<lparr>Dom\<rparr>\<lparr>f\<rparr> = a" "cat_ordinal A\<lparr>Cod\<rparr>\<lparr>f\<rparr> = b"
    by (cs_concl cs_simp: cat_ordinal_cs_simps assms(4))+
qed

lemma cat_ordinal_is_arrD[dest]:
  assumes "f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"
  shows "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "a \<le> b" and "f = [a, b]\<^sub>\<circ>"
proof-
  note f = is_arrD[OF assms, unfolded cat_ordinal_components(2)]
  from f(1) obtain a' b' 
    where a': "a' \<in>\<^sub>\<circ> A" 
      and b': "b' \<in>\<^sub>\<circ> A" 
      and a'b': "a' \<le> b'" 
      and f_def: "f = [a', b']\<^sub>\<circ>"
    unfolding ordinal_arrs_def by clarsimp
  from f(2) a' b' a'b' have a'_def: "a' = a" 
    by 
      (
        cs_prems 
          cs_simp: cat_ordinal_cs_simps f_def cs_intro: cat_ordinal_cs_intros
      )
  from f(3) a' b' a'b' have b'_def: "b' = b"
    by 
      (
        cs_prems 
          cs_simp: cat_ordinal_cs_simps f_def cs_intro: cat_ordinal_cs_intros
      )
  from a' b' a'b' f_def show "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "a \<le> b" and "f = [a, b]\<^sub>\<circ>"
    unfolding a'_def b'_def by auto
qed

lemma cat_ordinal_is_arrE[elim]:
  assumes "f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"
  obtains "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "a \<le> b" and "f = [a, b]\<^sub>\<circ>"
  using assms by auto


text\<open>Elementary properties.\<close>

lemma cat_ordinal_is_arr_not:
  assumes "\<not>a \<le> b"
  shows "\<not>f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"
proof(rule ccontr, unfold not_not)
  assume "f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"
  with cat_ordinal_is_arrD(3)[OF this] assms show False by simp
qed

lemma cat_ordinal_is_arr_is_unique:
  assumes "f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b" and "g : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"  
  shows "f = g"
  by 
    (
      simp add: 
        cat_ordinal_is_arrD(4)[OF assms(1)] 
        cat_ordinal_is_arrD(4)[OF assms(2)]
    )

lemma cat_ordinal_Hom_ne:
  assumes "f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"
  shows "Hom (cat_ordinal A) a b = set {f}"
  using assms cat_ordinal_is_arr_is_unique 
  by (intro vsubset_antisym vsubsetI) auto

lemma cat_ordinal_Hom_empty:
  assumes "\<not>a \<le> b"
  shows "Hom (cat_ordinal A) a b = 0"
  using assms by (intro vsubset_antisym vsubsetI) auto

lemma cat_ordinal_inj:
  assumes "cat_ordinal m = cat_ordinal n"
  shows "m = n"
  by (metis assms cat_ordinal_components(1))


subsubsection\<open>Composition\<close>

mk_VLambda cat_ordinal_components(5)
  |vsv cat_ordinal_Comp_vsv[cat_ordinal_cs_intros]|
  |vdomain cat_ordinal_Comp_vdomain[folded cat_ordinal_components, cat_cs_simps]|

lemma cat_ordinal_Comp_app[cat_ordinal_cs_simps]:
  assumes "g : b \<mapsto>\<^bsub>cat_ordinal A\<^esub> c" and "f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b" 
  shows "g \<circ>\<^sub>A\<^bsub>cat_ordinal A\<^esub> f = [a, c]\<^sub>\<circ>"
proof-
  from assms(2) have a: "a \<in>\<^sub>\<circ> A" 
    and b: "b \<in>\<^sub>\<circ> A" 
    and ab: "a \<le> b" 
    and f_def: "f = [a, b]\<^sub>\<circ>" 
    by auto
  from assms(1) have c: "c \<in>\<^sub>\<circ> A" and bc: "b \<le> c" and g_def: "g = [b, c]\<^sub>\<circ>" 
    by auto
  from a b c ab bc have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> ordinal_composable A"
    by (cs_concl cs_simp: g_def f_def cs_intro: cat_ordinal_cs_intros)
  then show "g \<circ>\<^sub>A\<^bsub>cat_ordinal A\<^esub> f = [a, c]\<^sub>\<circ>"
    unfolding cat_ordinal_components by (simp add: g_def f_def nat_omega_simps)
qed


subsubsection\<open>Identity\<close>

mk_VLambda cat_ordinal_components(6)
  |vsv cat_ordinal_CId_vsv[cat_ordinal_cs_intros]|
  |vdomain cat_ordinal_CId_vdomain[cat_ordinal_cs_simps]|
  |app cat_ordinal_CId_app[cat_ordinal_cs_simps]|


subsubsection\<open>Order relation\<close>

lemma cat_ordinal_is_leD[dest]:
  assumes "a \<le>\<^sub>O\<^bsub>cat_ordinal A\<^esub> b"
  shows "[a, b]\<^sub>\<circ> : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"
proof(intro cat_ordinal_is_arrI)
  from is_leD[OF assms] obtain f where "f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b" by fastforce
  then show "a \<in>\<^sub>\<circ> A" "b \<in>\<^sub>\<circ> A" "a \<subseteq>\<^sub>\<circ> b" by auto
qed simp

lemma cat_ordinal_is_leE[elim]:
  assumes "a \<le>\<^sub>O\<^bsub>cat_ordinal A\<^esub> b"
  obtains "[a, b]\<^sub>\<circ> : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"
  using assms by auto 

lemma cat_ordinal_is_le_iff:
  "a \<le>\<^sub>O\<^bsub>cat_ordinal A\<^esub> b \<longleftrightarrow> [a, b]\<^sub>\<circ> : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"
  using cat_ordinal_is_leD cat_ordinal_is_leE 
  by (metis HomI is_le_def vempty_nin)


subsubsection\<open>Every ordinal number is a category\<close>

lemma (in \<Z>) cat_linear_order_cat_ordinal[cat_ordinal_cs_intros]:
  assumes "Ord A" and "A \<subseteq>\<^sub>\<circ> \<alpha>"
  shows "cat_linear_order \<alpha> (cat_ordinal A)"
proof(intro cat_linear_orderI cat_partial_orderI cat_preorderI categoryI')
  show "vfsequence (cat_ordinal A)" unfolding cat_ordinal_def by auto
  show "vcard (cat_ordinal A) = 6\<^sub>\<nat>"
    unfolding cat_ordinal_def by (simp add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (cat_ordinal A\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> cat_ordinal A\<lparr>Obj\<rparr>"
    by (rule cat_ordinal_Dom_vrange)
  show "\<R>\<^sub>\<circ> (cat_ordinal A\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> cat_ordinal A\<lparr>Obj\<rparr>"
    by (rule cat_ordinal_Cod_vrange)
  show "(gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_ordinal A\<lparr>Comp\<rparr>)) \<longleftrightarrow>
    (
      \<exists>g f b c a.
        gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>cat_ordinal A\<^esub> c \<and> f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b
    )"
    for gf
    unfolding cat_ordinal_Comp_vdomain
  proof
    assume "gf \<in>\<^sub>\<circ> ordinal_composable A"
    then obtain a b c
      where gf_def: "gf = [[b, c]\<^sub>\<circ>, [a, b]\<^sub>\<circ>]\<^sub>\<circ>" 
        and a: "a \<in>\<^sub>\<circ> A" 
        and b: "b \<in>\<^sub>\<circ> A"
        and c: "c \<in>\<^sub>\<circ> A"
        and ab: "a \<le> b"
        and bc: "b \<le> c"
      by clarsimp
    from a b c ab bc show 
      "\<exists>g f b c a.
        gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>cat_ordinal A\<^esub> c \<and> f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"
      unfolding gf_def
      by (intro exI conjI)
        (
          cs_concl 
            cs_simp: cat_ordinal_cs_simps cs_intro: cat_ordinal_cs_intros
        )+
  next
    assume 
      "\<exists>g f b c a.
        gf = [g, f]\<^sub>\<circ> \<and>
        g : b \<mapsto>\<^bsub>cat_ordinal A\<^esub> c \<and> 
        f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"
    then obtain g f b c a
      where gf_def: "gf = [g, f]\<^sub>\<circ>"
        and g: "g : b \<mapsto>\<^bsub>cat_ordinal A\<^esub> c"
        and f: "f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"
      by clarsimp
    note g = cat_ordinal_is_arrD[OF g]
    note f = cat_ordinal_is_arrD[OF f]
    from g(1-3) f(1-3) show "gf \<in>\<^sub>\<circ> ordinal_composable A"
      unfolding gf_def g(4) f(4)
      by 
        (
          cs_concl 
            cs_simp: cat_ordinal_cs_simps cs_intro: cat_ordinal_cs_intros
        )
  qed
  show [cat_ordinal_cs_intros]: "g \<circ>\<^sub>A\<^bsub>cat_ordinal A\<^esub> f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> c"
    if "g : b \<mapsto>\<^bsub>cat_ordinal A\<^esub> c" and "f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b" for b c g a f
  proof-
    note g = cat_ordinal_is_arrD[OF that(1)]
    note f = cat_ordinal_is_arrD[OF that(2)]
    show ?thesis
    proof(intro cat_ordinal_is_arrI g(1,2) f(1,2), unfold g(4) f(4))
      from g(3) f(3) show "a \<subseteq>\<^sub>\<circ> c" by auto
      from g(1,2,3) f(1,2,3) show " [b, c]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_ordinal A\<^esub> [a, b]\<^sub>\<circ> = [a, c]\<^sub>\<circ>"
        by 
          (
            cs_concl 
              cs_simp: cat_ordinal_cs_simps cs_intro: cat_ordinal_cs_intros
          )
    qed
  qed
  show
    "h \<circ>\<^sub>A\<^bsub>cat_ordinal A\<^esub> g \<circ>\<^sub>A\<^bsub>cat_ordinal A\<^esub> f =
      h \<circ>\<^sub>A\<^bsub>cat_ordinal A\<^esub> (g \<circ>\<^sub>A\<^bsub>cat_ordinal A\<^esub> f)"
    if "h : c \<mapsto>\<^bsub>cat_ordinal A\<^esub> d"
      and "g : b \<mapsto>\<^bsub>cat_ordinal A\<^esub> c"
      and "f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"
    for c d h b g a f
  proof-
    note h = cat_ordinal_is_arrD[OF that(1)]
    note g = cat_ordinal_is_arrD[OF that(2)]
    note f = cat_ordinal_is_arrD[OF that(3)]
    from that(1-3) h(1-3) g(1-4) f(1-3) show ?thesis
      unfolding h(4) g(4) f(4) (*slow*)
      by (cs_concl cs_simp: cat_ordinal_cs_simps cs_intro: cat_ordinal_cs_intros)
  qed
  show "cat_ordinal A\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> a"
    if "a \<in>\<^sub>\<circ> cat_ordinal A\<lparr>Obj\<rparr>" for a
  proof- 
    from that have "a \<in>\<^sub>\<circ> A" unfolding cat_ordinal_components by simp
    then show "cat_ordinal A\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> a"
      by 
        (
          cs_concl 
            cs_simp: cat_ordinal_cs_simps
            cs_intro: cat_ordinal_cs_intros V_cs_intros
        )
  qed
  show "cat_ordinal A\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>cat_ordinal A\<^esub> f = f"
    if "f : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b" for a b f
  proof-
    note f = cat_ordinal_is_arrD[OF that]
    from f(1-3) show ?thesis
      by 
        (
          cs_concl 
            cs_simp: cat_ordinal_cs_simps f(4)
            cs_intro: cat_ordinal_cs_intros V_cs_intros
        )
  qed
  show "f \<circ>\<^sub>A\<^bsub>cat_ordinal A\<^esub> cat_ordinal A\<lparr>CId\<rparr>\<lparr>b\<rparr> = f"
    if "f : b \<mapsto>\<^bsub>cat_ordinal A\<^esub> c" for b c f
  proof-
    note f = cat_ordinal_is_arrD[OF that]
    from f(1-3) show ?thesis
      by 
        (
          cs_concl 
            cs_simp: cat_ordinal_cs_simps f(4)
            cs_intro: cat_ordinal_cs_intros V_cs_intros
        )
  qed
  from assms Ord_\<alpha> show "cat_ordinal A\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    unfolding cat_ordinal_components by auto
  show "(\<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. \<Union>\<^sub>\<circ>c\<in>\<^sub>\<circ>C. Hom (cat_ordinal A) b c) \<in>\<^sub>\<circ> Vset \<alpha>"
    if "B \<subseteq>\<^sub>\<circ> cat_ordinal A\<lparr>Obj\<rparr>" 
      and "C \<subseteq>\<^sub>\<circ> cat_ordinal A\<lparr>Obj\<rparr>"
      and "B \<in>\<^sub>\<circ> Vset \<alpha>"
      and "C \<in>\<^sub>\<circ> Vset \<alpha>"
    for B C
  proof-
    have "(\<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. \<Union>\<^sub>\<circ>c\<in>\<^sub>\<circ>C. Hom (cat_ordinal A) b c) \<subseteq>\<^sub>\<circ> B \<times>\<^sub>\<bullet> C"
    proof(rule vsubsetI)
      fix f assume "f \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. \<Union>\<^sub>\<circ>c\<in>\<^sub>\<circ>C. Hom (cat_ordinal A) b c)"
      then obtain b c 
        where b: "b \<in>\<^sub>\<circ> B" and c: "c \<in>\<^sub>\<circ> C" and f: "f : b \<mapsto>\<^bsub>cat_ordinal A\<^esub> c" 
        by auto
      note f = cat_ordinal_is_arrD[OF f]
      from b c show "f \<in>\<^sub>\<circ> B \<times>\<^sub>\<bullet> C"
        unfolding f(4) by auto
    qed
    moreover from that(3,4) have "B \<times>\<^sub>\<bullet> C \<in>\<^sub>\<circ> Vset \<alpha>"
      by (auto intro: Limit_ftimes_in_VsetI)
    ultimately show ?thesis by blast
  qed
  show "(\<exists>f. Hom (cat_ordinal A) a b = set {f}) \<or> Hom (cat_ordinal A) a b = 0"
    if "a \<in>\<^sub>\<circ> cat_ordinal A\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> cat_ordinal A\<lparr>Obj\<rparr>" for a b
  proof-
    from that have a: "a \<in>\<^sub>\<circ> A" and b: "b \<in>\<^sub>\<circ> A"
      unfolding cat_ordinal_components by simp_all
    then consider \<open>a \<le> b\<close> | \<open>\<not>a \<le> b\<close> by auto
    then show ?thesis
    proof cases
      case 1
      with a b have "[a, b]\<^sub>\<circ> : a \<mapsto>\<^bsub>cat_ordinal A\<^esub> b"
        by (auto intro: cat_ordinal_is_arrI)
      then show ?thesis by (simp add: cat_ordinal_Hom_ne)
    qed (simp add: cat_ordinal_Hom_empty)
  qed
  show "a = b"
    if "a \<in>\<^sub>\<circ> cat_ordinal A\<lparr>Obj\<rparr>"
      and "b \<in>\<^sub>\<circ> cat_ordinal A\<lparr>Obj\<rparr>"
      and "a \<le>\<^sub>O\<^bsub>cat_ordinal A\<^esub> b"
      and "b \<le>\<^sub>O\<^bsub>cat_ordinal A\<^esub> a"
    for a b
    using 
      that(3,4)[unfolded cat_ordinal_is_le_iff cat_ordinal_components]
      cat_ordinal_is_arr_is_unique
    by auto
  show "a \<le>\<^sub>O\<^bsub>cat_ordinal A\<^esub> b \<or> b \<le>\<^sub>O\<^bsub>cat_ordinal A\<^esub> a"
    if "a \<in>\<^sub>\<circ> cat_ordinal A\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> cat_ordinal A\<lparr>Obj\<rparr>" for a b
  proof-
    from that[unfolded cat_ordinal_components] have a: "a \<in>\<^sub>\<circ> A" and b: "b \<in>\<^sub>\<circ> A"
      by simp_all
    with assms have "Ord a" "Ord b" by auto
    then consider \<open>a \<le> b\<close> | \<open>b \<le> a\<close> by (meson Ord_linear_le)
    then show "a \<le>\<^sub>O\<^bsub>cat_ordinal A\<^esub> b \<or> b \<le>\<^sub>O\<^bsub>cat_ordinal A\<^esub> a"
      by cases (auto simp: a b cat_ordinal_is_le_iff intro: cat_ordinal_is_arrI)
  qed
qed (auto intro: cat_ordinal_cs_intros simp: cat_ordinal_cs_simps)

lemmas [cat_ordinal_cs_intros] = \<Z>.cat_linear_order_cat_ordinal

lemma (in \<Z>) cat_tiny_linear_order_cat_ordinal[cat_ordinal_cs_intros]:
  assumes "Ord A" and "A \<in>\<^sub>\<circ> \<alpha>"
  shows "cat_tiny_linear_order \<alpha> (cat_ordinal A)"
proof(intro cat_tiny_linear_orderI' cat_linear_order_cat_ordinal assms(1))
  from assms show "A \<subseteq>\<^sub>\<circ> \<alpha>"
    by (meson Ord_\<alpha> Ord_linear_le mem_not_refl vsubsetE)
  from assms(1) this interpret A: cat_linear_order \<alpha> \<open>cat_ordinal A\<close>
    by (intro cat_linear_order_cat_ordinal)
  from assms(2) have A_in_Vset: "A \<in>\<^sub>\<circ> Vset \<alpha>" by (simp add: Ord_\<alpha> Ord_in_in_VsetI)
  have "cat_ordinal A\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<bullet> A"
    unfolding ordinal_arrs_def cat_ordinal_components by clarsimp
  moreover from A_in_Vset have "A \<times>\<^sub>\<bullet> A \<in>\<^sub>\<circ> Vset \<alpha>"
    by (intro Limit_ftimes_in_VsetI) auto
  ultimately have "cat_ordinal A\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    using vsubset_in_VsetI unfolding cat_ordinal_components by simp
  moreover have "cat_ordinal A\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding cat_ordinal_components by (intro A_in_Vset)
  ultimately show "tiny_category \<alpha> (cat_ordinal A)"
    by (cs_concl cs_intro: cat_cs_intros tiny_categoryI')
qed

lemmas [cat_ordinal_cs_intros] = \<Z>.cat_linear_order_cat_ordinal

lemma (in \<Z>) finite_category_cat_ordinal[cat_ordinal_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> \<omega>"
  shows "finite_category \<alpha> (cat_ordinal a)"
proof-
  from assms have "Ord a" "a \<in>\<^sub>\<circ> \<alpha>" by (auto simp: Ord_\<alpha> Ord_trans)
  then interpret cat_ordinal: cat_tiny_linear_order \<alpha> \<open>cat_ordinal a\<close>
    by (cs_concl cs_intro: cat_ordinal_cs_intros)
  show ?thesis
  proof(intro finite_categoryI')
    from assms show "category \<alpha> (cat_ordinal a)"
      by (cs_concl cs_intro: cat_cs_intros)
    from assms show "vfinite (cat_ordinal a\<lparr>Obj\<rparr>)"
      unfolding cat_ordinal_components by auto
    from assms show "vfinite (cat_ordinal a\<lparr>Arr\<rparr>)"
    proof-
      have "cat_ordinal a\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> a \<times>\<^sub>\<bullet> a"
        unfolding cat_ordinal_components by auto
      moreover from assms have "vfinite (a \<times>\<^sub>\<bullet> a)"
        by (intro vfinite_ftimesI) auto
      ultimately show ?thesis by (auto simp: vfinite_vsubset)
    qed
  qed
qed

lemmas [cat_ordinal_cs_intros] = \<Z>.finite_category_cat_ordinal

end