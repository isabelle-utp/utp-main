(* Copyright 2020 (C) Mihails Milehins *)

section\<open>Simplicial category\<close>
theory CZH_ECAT_CSimplicial
  imports CZH_ECAT_Ordinal
begin



subsection\<open>Background\<close>


text\<open>
The content of this section is based, primarily, on the elements of the 
content of Chapter I-2 in \cite{mac_lane_categories_2010}.
\<close>

named_theorems cat_simplicial_cs_simps
named_theorems cat_simplicial_cs_intros



subsection\<open>Composable arrows for simplicial category\<close>

definition composable_cat_simplicial :: "V \<Rightarrow> V \<Rightarrow> V"
  where "composable_cat_simplicial \<alpha> A = set
    {
      [g, f]\<^sub>\<circ> | g f. \<exists>m n p.
        g : cat_ordinal n \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal p \<and>
        f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n \<and>
        m \<in>\<^sub>\<circ> A \<and> n \<in>\<^sub>\<circ> A \<and> p \<in>\<^sub>\<circ> A
    }"

lemma small_composable_cat_simplicial[simp]:
  "small
    {
      [g, f]\<^sub>\<circ> | g f. \<exists>m n p.
        g : cat_ordinal n \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal p \<and>
        f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n \<and>
        m \<in>\<^sub>\<circ> A \<and> n \<in>\<^sub>\<circ> A \<and> p \<in>\<^sub>\<circ> A
    }"
  (is \<open>small ?S\<close>)
proof(rule down)
  show "?S \<subseteq> elts (all_cfs \<alpha> \<times>\<^sub>\<bullet> all_cfs \<alpha>)"
  proof
    (
      intro subsetI, 
      unfold mem_Collect_eq, elim exE conjE; simp only:; intro ftimesI2
    )
    fix m n p g f 
    assume prems: 
      "m \<in>\<^sub>\<circ> A"
      "n \<in>\<^sub>\<circ> A"
      "p \<in>\<^sub>\<circ> A"
      "g : cat_ordinal n \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal p"
      "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n"
    interpret g: is_preorder_functor \<alpha> \<open>cat_ordinal n\<close> \<open>cat_ordinal p\<close> g
      by (rule prems(4))
    interpret f: is_preorder_functor \<alpha> \<open>cat_ordinal m\<close> \<open>cat_ordinal n\<close> f
      by (rule prems(5))
    from g.is_functor_axioms show "g \<in>\<^sub>\<circ> all_cfs \<alpha>" by auto
    from f.is_functor_axioms show "f \<in>\<^sub>\<circ> all_cfs \<alpha>" by auto
  qed
qed


text\<open>Rules.\<close>

lemma composable_cat_simplicialI:
  assumes "g : cat_ordinal n \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal p"
    and "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n"
    and "m \<in>\<^sub>\<circ> A" 
    and "n \<in>\<^sub>\<circ> A"
    and "p \<in>\<^sub>\<circ> A"
    and "gf = [g, f]\<^sub>\<circ>"
  shows "gf \<in>\<^sub>\<circ> composable_cat_simplicial \<alpha> A"
  using assms
  unfolding composable_cat_simplicial_def
  by (intro in_small_setI small_composable_cat_simplicial) auto

lemma composable_cat_simplicialE[elim]:
  assumes "gf \<in>\<^sub>\<circ> composable_cat_simplicial \<alpha> A"
  obtains g f m n p where "gf = [g, f]\<^sub>\<circ>" 
    and "g : cat_ordinal n \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal p"
    and "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n"
    and "m \<in>\<^sub>\<circ> A" 
    and "n \<in>\<^sub>\<circ> A"
    and "p \<in>\<^sub>\<circ> A"
proof-
  from assms obtain g f m n p where 
    "gf = [g, f]\<^sub>\<circ>"
    "g : cat_ordinal n \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal p"
    "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n"
    "m \<in>\<^sub>\<circ> A" 
    "n \<in>\<^sub>\<circ> A" 
    "p \<in>\<^sub>\<circ> A"
    unfolding composable_cat_simplicial_def
    by (elim in_small_setE, intro small_composable_cat_simplicial) auto
  with that show ?thesis by auto
qed



subsection\<open>Simplicial category\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cat_simplicial :: "V \<Rightarrow> V \<Rightarrow> V"
  where "cat_simplicial \<alpha> A =
    [
      set {cat_ordinal m | m. m \<in>\<^sub>\<circ> A},
      set
        {
          f. \<exists>m n.
            f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n \<and> m \<in>\<^sub>\<circ> A \<and> n \<in>\<^sub>\<circ> A
        },
      (
        \<lambda>f\<in>\<^sub>\<circ> set
          {
            f. \<exists>m n.
              f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n \<and> m \<in>\<^sub>\<circ> A \<and> n \<in>\<^sub>\<circ> A
          }. f\<lparr>HomDom\<rparr>
      ),
      (
        \<lambda>f\<in>\<^sub>\<circ> set
          {
            f. \<exists>m n.
              f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n \<and> m \<in>\<^sub>\<circ> A \<and> n \<in>\<^sub>\<circ> A
          }. f\<lparr>HomCod\<rparr>
      ),
      (\<lambda>gf\<in>\<^sub>\<circ>composable_cat_simplicial \<alpha> A. gf\<lparr>0\<rparr> \<circ>\<^sub>C\<^sub>F gf\<lparr>1\<^sub>\<nat>\<rparr>),
      (\<lambda>m\<in>\<^sub>\<circ>set {cat_ordinal m | m. m \<in>\<^sub>\<circ> A}. cf_id m)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_simplicial_components:
  shows "cat_simplicial \<alpha> A\<lparr>Obj\<rparr> = set {cat_ordinal m | m. m \<in>\<^sub>\<circ> A}"
    and "cat_simplicial \<alpha> A\<lparr>Arr\<rparr> = 
      set {f. \<exists>m n. f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n \<and> m \<in>\<^sub>\<circ> A \<and> n \<in>\<^sub>\<circ> A}"
    and "cat_simplicial \<alpha> A\<lparr>Dom\<rparr> =
      (
        \<lambda>f\<in>\<^sub>\<circ>set
          {
            f. \<exists>m n.
              f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n \<and> m \<in>\<^sub>\<circ> A \<and> n \<in>\<^sub>\<circ> A
          }. f\<lparr>HomDom\<rparr>
      )"
    and "cat_simplicial \<alpha> A\<lparr>Cod\<rparr> =
      (
        \<lambda>f\<in>\<^sub>\<circ>set
          {
            f. \<exists>m n.
              f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n \<and> m \<in>\<^sub>\<circ> A \<and> n \<in>\<^sub>\<circ> A
          }. f\<lparr>HomCod\<rparr>
      )"
    and "cat_simplicial \<alpha> A\<lparr>Comp\<rparr> =
      (\<lambda>gf\<in>\<^sub>\<circ>composable_cat_simplicial \<alpha> A. gf\<lparr>0\<rparr> \<circ>\<^sub>C\<^sub>F gf\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "cat_simplicial \<alpha> A\<lparr>CId\<rparr> =
      (\<lambda>m\<in>\<^sub>\<circ>set {cat_ordinal m | m. m \<in>\<^sub>\<circ> A}. cf_id m)"
  unfolding cat_simplicial_def dg_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Objects\<close>

lemma cat_simplicial_ObjI[cat_simplicial_cs_intros]:
  assumes "m \<in>\<^sub>\<circ> A" and "a = cat_ordinal m"
  shows "a \<in>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Obj\<rparr> "
  using assms unfolding cat_simplicial_components by auto

lemma cat_simplicial_ObjD:
  assumes "cat_ordinal m \<in>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Obj\<rparr> "
  shows "m \<in>\<^sub>\<circ> A" 
  using assms cat_ordinal_inj unfolding cat_simplicial_components by auto

lemma cat_simplicial_ObjE:
  assumes "M \<in>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Obj\<rparr> "
  obtains m where "M = cat_ordinal m" and "m \<in>\<^sub>\<circ> A" 
  using assms cat_ordinal_inj that unfolding cat_simplicial_components by auto


subsubsection\<open>Arrows\<close>

lemma small_cat_simplicial_Arr[simp]: 
  "small {f. \<exists>m n. f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n \<and> m \<in>\<^sub>\<circ> A \<and> n \<in>\<^sub>\<circ> A}"
  (is \<open>small ?S\<close>)
proof(rule down)
  show "?S \<subseteq> elts (all_cfs \<alpha>)" by auto
qed

lemma cat_simplicial_ArrI[cat_simplicial_cs_intros]:
  assumes "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n" and "m \<in>\<^sub>\<circ> A" and "n \<in>\<^sub>\<circ> A" 
  shows "f \<in>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Arr\<rparr>"
  using assms 
  unfolding cat_simplicial_components
  by (intro in_small_setI small_cat_simplicial_Arr) auto

lemma cat_simplicial_ArrE:
  assumes "f \<in>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Arr\<rparr>"
  obtains m n 
    where "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n" and "m \<in>\<^sub>\<circ> A" and "n \<in>\<^sub>\<circ> A" 
proof-
  from assms cat_ordinal_inj obtain m n 
    where "m \<in>\<^sub>\<circ> A" "n \<in>\<^sub>\<circ> A" "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n"
    unfolding cat_simplicial_components
    by (elim in_small_setE, intro small_cat_simplicial_Arr) auto
  with that show ?thesis by simp
qed


subsubsection\<open>Domain\<close>

mk_VLambda cat_simplicial_components(3)
  |vsv cat_simplicial_Dom_vsv[cat_simplicial_cs_intros]|
  |vdomain 
    cat_simplicial_Dom_vdomain[
      folded cat_simplicial_components, cat_simplicial_cs_simps
    ]
  |
  |app cat_simplicial_Dom_app[folded cat_simplicial_components]|

lemma cat_simplicial_Dom_app'[cat_simplicial_cs_simps]:
  assumes "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n" and "m \<in>\<^sub>\<circ> A" and "n \<in>\<^sub>\<circ> A" 
  shows "cat_simplicial \<alpha> A\<lparr>Dom\<rparr>\<lparr>f\<rparr> = cat_ordinal m"
proof-
  interpret f: is_preorder_functor \<alpha> \<open>cat_ordinal m\<close> \<open>cat_ordinal n\<close> f 
    by (rule assms(1))
  from assms show "cat_simplicial \<alpha> A\<lparr>Dom\<rparr>\<lparr>f\<rparr> = cat_ordinal m"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_simplicial_Dom_app 
          cs_intro: cat_simplicial_cs_intros
      )
qed


subsubsection\<open>Codomain\<close>

mk_VLambda cat_simplicial_components(4)
  |vsv cat_simplicial_Cod_vsv[cat_simplicial_cs_intros]|
  |vdomain 
    cat_simplicial_Cod_vdomain[
      folded cat_simplicial_components, cat_simplicial_cs_simps
    ]
  |
  |app cat_simplicial_Cod_app[folded cat_simplicial_components]|


lemma cat_simplicial_Cod_app'[cat_simplicial_cs_simps]:
  assumes "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n" and "m \<in>\<^sub>\<circ> A" and "n \<in>\<^sub>\<circ> A" 
  shows "cat_simplicial \<alpha> A\<lparr>Cod\<rparr>\<lparr>f\<rparr> = cat_ordinal n"
proof-
  interpret f: is_preorder_functor \<alpha> \<open>cat_ordinal m\<close> \<open>cat_ordinal n\<close> f 
    by (rule assms(1))
  from assms show "cat_simplicial \<alpha> A\<lparr>Cod\<rparr>\<lparr>f\<rparr> = cat_ordinal n"
    by 
      (
        cs_concl
          cs_simp: cat_cs_simps cat_simplicial_Cod_app 
          cs_intro: cat_simplicial_cs_intros
      )
qed


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma cat_simplicial_is_arrI: 
  assumes "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n"
    and "m \<in>\<^sub>\<circ> A" 
    and "n \<in>\<^sub>\<circ> A"
  shows "f : cat_ordinal m \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> cat_ordinal n"
proof(intro is_arrI cat_simplicial_ArrI, rule assms; (intro assms(2,3))?)
  from assms show 
    "cat_simplicial \<alpha> A\<lparr>Dom\<rparr>\<lparr>f\<rparr> = cat_ordinal m"
    "cat_simplicial \<alpha> A\<lparr>Cod\<rparr>\<lparr>f\<rparr> = cat_ordinal n"
    by (cs_concl cs_simp: cat_simplicial_cs_simps)+
qed

lemma cat_simplicial_is_arrI'[cat_simplicial_cs_intros]: 
  assumes "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n"
    and "m \<in>\<^sub>\<circ> A" 
    and "n \<in>\<^sub>\<circ> A"
    and "a = cat_ordinal m"
    and "b = cat_ordinal n"
  shows "f : a \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> b"
  using assms(1-3) unfolding assms(4-5) by (rule cat_simplicial_is_arrI)

lemma cat_simplicial_is_arrD[dest]: 
  assumes "f : cat_ordinal m \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> cat_ordinal n"
    and "m \<in>\<^sub>\<circ> A" 
    and "n \<in>\<^sub>\<circ> A"
  shows "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n"
proof-
  note f = is_arrD[OF assms(1)]
  from f(1) obtain m' n' 
    where f_is_preorder_functor: "f : cat_ordinal m' \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n'" 
      and "m' \<in>\<^sub>\<circ> A"
      and "n' \<in>\<^sub>\<circ> A"
    by (elim cat_simplicial_ArrE)  
  then have 
    "cat_simplicial \<alpha> A\<lparr>Dom\<rparr>\<lparr>f\<rparr> = cat_ordinal m'"
    "cat_simplicial \<alpha> A\<lparr>Cod\<rparr>\<lparr>f\<rparr> = cat_ordinal n'"
    by (cs_concl cs_simp: cat_simplicial_cs_simps)+
  with f(2,3) have 
    "cat_ordinal m' = cat_ordinal m" "cat_ordinal n' = cat_ordinal n"
    by auto
  with f(2,3) cat_ordinal_inj have [simp]: "m' = m" "n' = n" by auto
  from f_is_preorder_functor show ?thesis by simp
qed

lemma cat_simplicial_is_arrE[elim]: 
  assumes "f : a \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> b"
  obtains m n where "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n"
    and "m \<in>\<^sub>\<circ> A" 
    and "n \<in>\<^sub>\<circ> A"
    and "a = cat_ordinal m"
    and "b = cat_ordinal n"
proof-
  note f = is_arrD[OF assms(1)]
  from f(1) obtain m n
    where f_is_preorder_functor: "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n" 
      and m: "m \<in>\<^sub>\<circ> A"
      and n: "n \<in>\<^sub>\<circ> A"
    by (elim cat_simplicial_ArrE)  
  then have 
    "cat_simplicial \<alpha> A\<lparr>Dom\<rparr>\<lparr>f\<rparr> = cat_ordinal m"
    "cat_simplicial \<alpha> A\<lparr>Cod\<rparr>\<lparr>f\<rparr> = cat_ordinal n"
    by (cs_concl cs_simp: cat_simplicial_cs_simps)+
  with f(2,3) have "cat_ordinal m = a" "cat_ordinal n = b"
    by auto
  with f_is_preorder_functor m n that show ?thesis by auto
qed


subsubsection\<open>Composition\<close>

mk_VLambda cat_simplicial_components(5)
  |vsv cat_simplicial_Comp_vsv[cat_simplicial_cs_intros]|
  |vdomain cat_simplicial_Comp_vdomain[cat_simplicial_cs_simps]|

lemma cat_simplicial_Comp_app[cat_simplicial_cs_simps]:
  assumes "g : cat_ordinal n \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> cat_ordinal p"
    and "f : cat_ordinal m \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> cat_ordinal n"
    and "m \<in>\<^sub>\<circ> A" 
    and "n \<in>\<^sub>\<circ> A" 
    and "p \<in>\<^sub>\<circ> A"
  shows "g \<circ>\<^sub>A\<^bsub>cat_simplicial \<alpha> A\<^esub> f = g \<circ>\<^sub>C\<^sub>F f"
proof- 
  note g = cat_simplicial_is_arrD[OF assms(1,4,5)]
  note f = cat_simplicial_is_arrD[OF assms(2,3,4)]
  interpret g: is_preorder_functor \<alpha> \<open>cat_ordinal n\<close> \<open>cat_ordinal p\<close> g
    by (rule g)
  interpret f: is_preorder_functor \<alpha> \<open>cat_ordinal m\<close> \<open>cat_ordinal n\<close> f
    by (rule f)
  have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> composable_cat_simplicial \<alpha> A"
    by 
      (
        intro composable_cat_simplicialI, rule g, rule f; 
        (intro assms refl)?
      )
  then show "g \<circ>\<^sub>A\<^bsub>cat_simplicial \<alpha> A\<^esub> f = g \<circ>\<^sub>C\<^sub>F f"
    unfolding cat_simplicial_components by (simp add: nat_omega_simps)
qed


subsubsection\<open>Identity\<close>

context
  fixes \<alpha> A :: V
begin

mk_VLambda cat_simplicial_components(6)[where \<alpha>=\<alpha> and A=A]
  |vsv cat_simplicial_CId_vsv[cat_simplicial_cs_intros]|
  |vdomain 
    cat_simplicial_CId_vdomain'[
      folded cat_simplicial_components(1)[where \<alpha>=\<alpha> and A=A]
    ]
  |
  |app cat_simplicial_CId_app'[
    folded cat_simplicial_components(1)[where \<alpha>=\<alpha> and A=A]
    ]
  |

lemmas cat_simplicial_CId_vdomain[cat_simplicial_cs_simps] = 
  cat_simplicial_CId_vdomain'
lemmas cat_simplicial_CId_app[cat_simplicial_cs_simps] = 
  cat_simplicial_CId_app'

end


subsubsection\<open>Simplicial category is a category\<close>

lemma (in \<Z>) category_simplicial:
  assumes "Ord A" and "A \<subseteq>\<^sub>\<circ> \<alpha>"
  shows "category \<alpha> (cat_simplicial \<alpha> A)"
proof-

  show ?thesis 
  proof(intro categoryI')

    show "vfsequence (cat_simplicial \<alpha> A)" unfolding cat_simplicial_def by simp
    show "vcard (cat_simplicial \<alpha> A) = 6\<^sub>\<nat>"
      unfolding cat_simplicial_def by (simp add: nat_omega_simps)

    show "\<R>\<^sub>\<circ> (cat_simplicial \<alpha> A\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Obj\<rparr>"
    proof(rule vsv.vsv_vrange_vsubset, unfold cat_simplicial_cs_simps)
      fix f assume "f \<in>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Arr\<rparr>"
      then obtain m n 
        where "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n" 
          and "m \<in>\<^sub>\<circ> A" 
          and "n \<in>\<^sub>\<circ> A"
        by (elim cat_simplicial_ArrE)
      then show "cat_simplicial \<alpha> A\<lparr>Dom\<rparr>\<lparr>f\<rparr> \<in>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Obj\<rparr>"
        by (auto simp: cat_simplicial_Dom_app' intro: cat_simplicial_ObjI)
    qed (auto simp: cat_simplicial_components)

    show "\<R>\<^sub>\<circ> (cat_simplicial \<alpha> A\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Obj\<rparr>"
    proof(rule vsv.vsv_vrange_vsubset, unfold cat_simplicial_cs_simps)
      fix f assume "f \<in>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Arr\<rparr>"
      then obtain m n 
        where "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n" 
          and "m \<in>\<^sub>\<circ> A" 
          and "n \<in>\<^sub>\<circ> A"
        by (elim cat_simplicial_ArrE)
      then show "cat_simplicial \<alpha> A\<lparr>Cod\<rparr>\<lparr>f\<rparr> \<in>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Obj\<rparr>"
        by (auto simp: cat_simplicial_Cod_app' intro: cat_simplicial_ObjI)
    qed (auto simp: cat_simplicial_components)

    show "(gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_simplicial \<alpha> A\<lparr>Comp\<rparr>)) \<longleftrightarrow>
      (
        \<exists>g f b c a.
          gf = [g, f]\<^sub>\<circ> \<and>
          g : b \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> c \<and>
          f : a \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> b
      )"
      for gf
    proof(intro iffI; (elim exE conjE)?)
      assume "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_simplicial \<alpha> A\<lparr>Comp\<rparr>)"
      then have "gf \<in>\<^sub>\<circ> composable_cat_simplicial \<alpha> A"
        unfolding cat_simplicial_components by simp
      then obtain g f m n p 
        where gf_def: "gf = [g, f]\<^sub>\<circ>" 
          and g: "g : cat_ordinal n \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal p"
          and f: "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n"
          and m: "m \<in>\<^sub>\<circ> A" 
          and n: "n \<in>\<^sub>\<circ> A"
          and p: "p \<in>\<^sub>\<circ> A"
        by auto
      show "\<exists>g f b c a.
        gf = [g, f]\<^sub>\<circ> \<and>
        g : b \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> c \<and>
        f : a \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> b"
      proof(intro exI conjI)
        from g n p show "g : cat_ordinal n \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> cat_ordinal p"
          by (intro cat_simplicial_is_arrI) simp_all
        from f m n show "f : cat_ordinal m \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> cat_ordinal n"
          by (intro cat_simplicial_is_arrI) simp_all
      qed (simp add: gf_def)
    next
      fix g f a b c assume prems:
        "gf = [g, f]\<^sub>\<circ>" 
        "g : b \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> c"
        "f : a \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> b"
      from prems(2) obtain n p 
        where g: "g : cat_ordinal n \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal p"
          and n: "n \<in>\<^sub>\<circ> A" 
          and p: "p \<in>\<^sub>\<circ> A"
          and b_def: "b = cat_ordinal n" 
          and "c = cat_ordinal p"
        by auto
      from prems(3) obtain m n'
        where f: "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n'"
          and m: "m \<in>\<^sub>\<circ> A" 
          and n': "n' \<in>\<^sub>\<circ> A"
          and a_def: "a = cat_ordinal m" 
          and b_def': "b = cat_ordinal n'"
        by auto
      from b_def b_def' have n'n: "n' = n" by (auto simp: cat_ordinal_inj)
      show "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_simplicial \<alpha> A\<lparr>Comp\<rparr>)"
        unfolding prems(1) cat_simplicial_Comp_vdomain
        by (intro composable_cat_simplicialI, rule g, rule f[unfolded n'n])
          (simp_all add:  m n p)
    qed
    show "g \<circ>\<^sub>A\<^bsub>cat_simplicial \<alpha> A\<^esub> f : a \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> c"
      if "g : b \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> c" and "f : a \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> b"
      for b c g a f
      using that  
      by (elim cat_simplicial_is_arrE; simp only: cat_ordinal_inj)
        (
          cs_concl 
            cs_simp: cat_simplicial_cs_simps 
            cs_intro: cat_order_cs_intros cat_simplicial_cs_intros
        )

    show "h \<circ>\<^sub>A\<^bsub>cat_simplicial \<alpha> A\<^esub> g \<circ>\<^sub>A\<^bsub>cat_simplicial \<alpha> A\<^esub> f =
      h \<circ>\<^sub>A\<^bsub>cat_simplicial \<alpha> A\<^esub> (g \<circ>\<^sub>A\<^bsub>cat_simplicial \<alpha> A\<^esub> f)"
      if "h : c \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> d"
        and "g : b \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> c"
        and "f : a \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> b"
      for c d h b g a f
      using that
      apply(elim cat_simplicial_is_arrE; simp only:)
      subgoal for m n m' n' m'' n'' (*FIXME: investigate comp_no_flatten*)
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_simplicial_cs_simps 
              cs_intro: cat_order_cs_intros cat_simplicial_cs_intros
          )+
      done

    show "cat_simplicial \<alpha> A\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> a"
      if "a \<in>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Obj\<rparr>" for a
      using that
    proof(elim cat_simplicial_ObjE; simp only:)
      fix m assume prems: "m \<in>\<^sub>\<circ> A" "cat_ordinal m \<in>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Obj\<rparr>"
      moreover from prems(1) assms(1) have "Ord m" by auto
      moreover from prems assms have "m \<subseteq>\<^sub>\<circ> \<alpha>" 
        by (meson Ord_trans vsubsetI rev_vsubsetD)
      ultimately show "cat_simplicial \<alpha> A\<lparr>CId\<rparr>\<lparr>cat_ordinal m\<rparr> :
        cat_ordinal m \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> cat_ordinal m"
        by 
          (
            cs_concl 
              cs_simp: cat_simplicial_cs_simps 
              cs_intro: 
                cat_ordinal_cs_intros 
                cat_order_cs_intros
                cat_simplicial_cs_intros
          )
    qed
    show "cat_simplicial \<alpha> A\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>cat_simplicial \<alpha> A\<^esub> f = f"
      if "f : a \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> b" for a b f
      using that
      by (elim cat_simplicial_is_arrE; simp only:)
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_simplicial_cs_simps
            cs_intro: cat_order_cs_intros cat_simplicial_cs_intros
        )
    show "f \<circ>\<^sub>A\<^bsub>cat_simplicial \<alpha> A\<^esub> cat_simplicial \<alpha> A\<lparr>CId\<rparr>\<lparr>b\<rparr> = f"
      if "f : b \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> c" for b c f
      using that
      by (elim cat_simplicial_is_arrE; simp only:)
        (
          cs_concl
            cs_simp: cat_cs_simps cat_simplicial_cs_simps
            cs_intro: cat_order_cs_intros cat_simplicial_cs_intros
        )
    show "cat_simplicial \<alpha> A\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    proof(intro vsubsetI, elim cat_simplicial_ObjE; simp only:)
      fix m assume prems: "m \<in>\<^sub>\<circ> A"
      then have "Ord m" using assms(1) by auto
      moreover from prems have "m \<in>\<^sub>\<circ> \<alpha>" using assms(2) by auto
      ultimately interpret m: cat_tiny_linear_order \<alpha> \<open>cat_ordinal m\<close>
        by (intro cat_tiny_linear_order_cat_ordinal)
      show "cat_ordinal m \<in>\<^sub>\<circ> Vset \<alpha>" by (rule m.tiny_cat_in_Vset)
    qed

    show "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A'. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B'. Hom (cat_simplicial \<alpha> A) a b) \<in>\<^sub>\<circ> Vset \<alpha>"
      if "A' \<subseteq>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Obj\<rparr>"
        and "B' \<subseteq>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Obj\<rparr>"
        and "A' \<in>\<^sub>\<circ> Vset \<alpha>"
        and "B' \<in>\<^sub>\<circ> Vset \<alpha>"
      for A' B' 
    proof-
      define Q where "Q i =
        (
          if i = 0 \<Rightarrow> VPow ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B'. b'\<lparr>Obj\<rparr>))
           | i = 1\<^sub>\<nat> \<Rightarrow> VPow 
              (((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<bullet> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>)) \<times>\<^sub>\<circ>
              ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>B'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<bullet> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>B'. a'\<lparr>Obj\<rparr>)))
           | i = 2\<^sub>\<nat> \<Rightarrow> A'
           | i = 3\<^sub>\<nat> \<Rightarrow> B'
           | otherwise \<Rightarrow> 0
        )"
        for i
      let ?Q = 
        \<open>{
          [fo, fa, a, b]\<^sub>\<circ> | fo fa a b.
            fo \<subseteq>\<^sub>\<circ> ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B'. b'\<lparr>Obj\<rparr>)) \<and>
            fa \<subseteq>\<^sub>\<circ>
              ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<bullet> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>)) \<times>\<^sub>\<circ>
              ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>B'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<bullet> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>B'. a'\<lparr>Obj\<rparr>)) \<and>
            a \<in>\<^sub>\<circ> A' \<and>
            b \<in>\<^sub>\<circ> B'
         }\<close>

      have QQ: "?Q \<subseteq> elts (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>, 3\<^sub>\<nat>}. Q i)"
      proof(intro subsetI, unfold mem_Collect_eq, elim exE conjE)
        fix x fo fa a b assume prems: 
          "x = [fo, fa, a, b]\<^sub>\<circ>"
          "fo \<subseteq>\<^sub>\<circ> ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B'. b'\<lparr>Obj\<rparr>))"
          "fa \<subseteq>\<^sub>\<circ>
            ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<bullet> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>)) \<times>\<^sub>\<circ>
            ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>B'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<bullet> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>B'. a'\<lparr>Obj\<rparr>))"
          "a \<in>\<^sub>\<circ> A'"
          "b \<in>\<^sub>\<circ> B'"
        show "x \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>, 3\<^sub>\<nat>}. Q i)"
        proof(intro vproductI, unfold Ball_def; (intro allI impI)?)
          show "\<D>\<^sub>\<circ> x = set {[]\<^sub>\<circ>, 1\<^sub>\<nat>, 2\<^sub>\<nat>, 3\<^sub>\<nat>}"
            unfolding prems(1) by (force simp: nat_omega_simps)
          fix i assume "i \<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>, 3\<^sub>\<nat>}"
          then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> | \<open>i = 2\<^sub>\<nat>\<close> | \<open>i = 3\<^sub>\<nat>\<close> by auto
          then show "x\<lparr>i\<rparr> \<in>\<^sub>\<circ> Q i" 
            by cases (auto simp: Q_def prems nat_omega_simps)
        qed (auto simp: prems)
      qed
      then have small_Q[simp]: "small ?Q" by (intro down)

      have "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A'. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B'. Hom (cat_simplicial \<alpha> A) a b) \<subseteq>\<^sub>\<circ> set ?Q" 
      proof(intro vsubsetI in_small_setI small_Q)
        fix f assume "f \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A'. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B'. Hom (cat_simplicial \<alpha> A) a b)"
        then obtain a b 
          where a: "a \<in>\<^sub>\<circ> A'" 
            and b: "b \<in>\<^sub>\<circ> B'" 
            and "f : a \<mapsto>\<^bsub>cat_simplicial \<alpha> A\<^esub> b"
          by auto
        then obtain m n 
          where f: "f : cat_ordinal m \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^bsub>\<alpha>\<^esub> cat_ordinal n"
            and m: "m \<in>\<^sub>\<circ> A" 
            and n: "n \<in>\<^sub>\<circ> A" 
            and a_def: "a = cat_ordinal m" 
            and b_def: "b = cat_ordinal n"
          by auto
        interpret f: is_preorder_functor \<alpha> \<open>cat_ordinal m\<close> \<open>cat_ordinal n\<close> f 
          by (rule f)
        show "f \<in> ?Q"
        proof(unfold mem_Collect_eq, intro exI conjI)
          show "f\<lparr>ObjMap\<rparr> \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B'. b'\<lparr>Obj\<rparr>)"
          proof(intro vsubsetI)
            fix x assume prems: "x \<in>\<^sub>\<circ> f\<lparr>ObjMap\<rparr>"
            obtain xl xr 
              where x_def: "x = \<langle>xl, xr\<rangle>" 
                and xl: "xl \<in>\<^sub>\<circ> cat_ordinal m\<lparr>Obj\<rparr>" 
                and xr: "xr \<in>\<^sub>\<circ> (\<R>\<^sub>\<circ> (f\<lparr>ObjMap\<rparr>))"
              by (elim f.ObjMap.vbrelation_vinE[OF prems, unfolded cat_cs_simps])
            show "x \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B'. b'\<lparr>Obj\<rparr>)"
              unfolding x_def
            proof(standard; (intro vifunionI))
              from xr f.cf_ObjMap_vrange show "xr \<in>\<^sub>\<circ> cat_ordinal n\<lparr>Obj\<rparr>" by auto
            qed (use a b in \<open>auto intro: xl simp: a_def b_def\<close>)
          qed
          show "f\<lparr>ArrMap\<rparr> \<subseteq>\<^sub>\<circ>
            ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<bullet> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>)) \<times>\<^sub>\<circ>
            ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>B'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<bullet> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>B'. a'\<lparr>Obj\<rparr>))"
          proof(intro vsubsetI)
            fix x assume prems: "x \<in>\<^sub>\<circ> f\<lparr>ArrMap\<rparr>"
            obtain xl xr 
              where x_def: "x = \<langle>xl, xr\<rangle>" 
                and xl: "xl \<in>\<^sub>\<circ> cat_ordinal m\<lparr>Arr\<rparr>" 
                and xr: "xr \<in>\<^sub>\<circ> (\<R>\<^sub>\<circ> (f\<lparr>ArrMap\<rparr>))"
              by (elim f.ArrMap.vbrelation_vinE[OF prems, unfolded cat_cs_simps])
            from xr vsubsetD have xr: "xr \<in>\<^sub>\<circ> cat_ordinal n\<lparr>Arr\<rparr>"
              by (auto intro: f.cf_ArrMap_vrange)
            from xl obtain xll xlr where xl_def: "xl = [xll, xlr]\<^sub>\<circ>" 
              and xll_m: "xll \<in>\<^sub>\<circ> m" 
              and xlr_m: "xlr \<in>\<^sub>\<circ> m" 
              and "xll \<subseteq>\<^sub>\<circ> xlr" 
              unfolding ordinal_arrs_def cat_ordinal_components by clarsimp
            from xr obtain xrl xrr where xr_def: "xr = [xrl, xrr]\<^sub>\<circ>" 
              and xrl_n: "xrl \<in>\<^sub>\<circ> n"
              and xrr_n:"xrr \<in>\<^sub>\<circ> n"
              and "xrl \<subseteq>\<^sub>\<circ> xrr"
              unfolding ordinal_arrs_def cat_ordinal_components by clarsimp
            show "x \<in>\<^sub>\<circ>
              ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<bullet> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>)) \<times>\<^sub>\<circ>
              ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>B'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<bullet> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>B'. a'\<lparr>Obj\<rparr>))"
              unfolding x_def
              by (standard; (intro vifunionI ftimesI1)?)
                (
                  use a b in \<open>
                    auto
                      simp: xl_def xr_def a_def b_def cat_ordinal_components
                      intro: xrr_n xrl_n xlr_m xll_m
                    \<close>
                )
          qed 
        qed 
          (
            auto 
              simp: cat_cs_simps 
              intro: a[unfolded a_def] b[unfolded b_def] f.cf_def
          )
      qed
      moreover have "set ?Q \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>, 3\<^sub>\<nat>}. Q i)"
        by 
          (
            intro vsubset_if_subset, 
            unfold small_elts_of_set[OF small_Q], 
            intro QQ
          )
      moreover have "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>, 3\<^sub>\<nat>}. Q i) \<in>\<^sub>\<circ> Vset \<alpha>"
      proof(intro Limit_vproduct_in_VsetI)
        show "set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>, 3\<^sub>\<nat>} \<in>\<^sub>\<circ> Vset \<alpha>"
          unfolding four[symmetric] by simp
        have "(\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>) \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r\<in>\<^sub>\<circ>A'. \<R>\<^sub>\<circ> r)"
        proof(intro vsubsetI)
          fix x assume "x \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>)"
          then obtain a' where a': "a' \<in>\<^sub>\<circ> A'" and x: "x \<in>\<^sub>\<circ> a'\<lparr>Obj\<rparr>" by auto
          from a' that(1) have "a' \<in>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Obj\<rparr>" by auto
          then obtain m where a'_def: "a' = cat_ordinal m" and m: "m \<in>\<^sub>\<circ> A"
            unfolding cat_simplicial_components by clarsimp
          show "x \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r\<in>\<^sub>\<circ>A'. \<R>\<^sub>\<circ> r)"
          proof(rule VUnionI, rule vifunionI)
            from a'_def have "vsv a'" and "Obj \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> a'"
              unfolding a'_def cat_ordinal_def Obj_def by auto
            then show "a'\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> a'" by auto
          qed (auto simp: x a')
        qed
        moreover have "(\<Union>\<^sub>\<circ>r\<in>\<^sub>\<circ>A'. \<R>\<^sub>\<circ> r) \<in>\<^sub>\<circ> Vset \<alpha>"
          by (intro Limit_VUnion_vrange_in_VsetI[OF Limit_\<alpha>] that)
        ultimately have UA': "(\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>" by blast
        have B': "(\<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B'. b'\<lparr>Obj\<rparr>) \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r\<in>\<^sub>\<circ>B'. \<R>\<^sub>\<circ> r)"
          (*FIXME: code duplication*)
        proof(intro vsubsetI)
          fix x assume "x \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B'. b'\<lparr>Obj\<rparr>)"
          then obtain b' where b': "b' \<in>\<^sub>\<circ> B'" and x: "x \<in>\<^sub>\<circ> b'\<lparr>Obj\<rparr>" by auto
          from b' that(2) have "b' \<in>\<^sub>\<circ> cat_simplicial \<alpha> A\<lparr>Obj\<rparr>" by auto
          then obtain m where b'_def: "b' = cat_ordinal m" and m: "m \<in>\<^sub>\<circ> A"
            unfolding cat_simplicial_components by clarsimp
          show "x \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r\<in>\<^sub>\<circ>B'. \<R>\<^sub>\<circ> r)"
          proof(rule VUnionI, rule vifunionI)
            from b'_def have "vsv b'" and "Obj \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> b'"
              unfolding b'_def cat_ordinal_def Obj_def by auto
            then show "b'\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> b'" by auto
          qed (auto simp: x b')
        qed
        moreover have "(\<Union>\<^sub>\<circ>r\<in>\<^sub>\<circ>B'. \<R>\<^sub>\<circ> r) \<in>\<^sub>\<circ> Vset \<alpha>"
          by (intro Limit_VUnion_vrange_in_VsetI[OF Limit_\<alpha>] that)
        ultimately have UB': "(\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>B'. a'\<lparr>Obj\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>" by blast
        have [simp]: 
          "VPow ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>b'\<in>\<^sub>\<circ>B'. b'\<lparr>Obj\<rparr>)) \<in>\<^sub>\<circ> Vset \<alpha>"
          by (intro Limit_VPow_in_VsetI Limit_vtimes_in_VsetI UA' UB') auto
        have [simp]:
          "VPow
            (
              ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<bullet> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>A'. a'\<lparr>Obj\<rparr>)) \<times>\<^sub>\<circ>
              ((\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>B'. a'\<lparr>Obj\<rparr>) \<times>\<^sub>\<bullet> (\<Union>\<^sub>\<circ>a'\<in>\<^sub>\<circ>B'. a'\<lparr>Obj\<rparr>))
            ) \<in>\<^sub>\<circ> Vset \<alpha>"
          by 
            (
              intro 
                Limit_VPow_in_VsetI 
                Limit_vtimes_in_VsetI 
                Limit_ftimes_in_VsetI  
                UA' UB'
            )
            auto
        fix i assume "i \<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>, 3\<^sub>\<nat>}"
        then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> | \<open>i = 2\<^sub>\<nat>\<close> | \<open>i = 3\<^sub>\<nat>\<close> by auto
        then show "Q i \<in>\<^sub>\<circ> Vset \<alpha>" 
          by cases (simp_all add: Q_def that nat_omega_simps)
      qed auto
      ultimately show ?thesis by (simp add: vsubset_in_VsetI)
    qed
  qed (auto simp: cat_simplicial_components)

qed

text\<open>\newpage\<close>

end