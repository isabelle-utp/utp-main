(*
    File:     Group_Relations.thy
    Author:   Joseph Thommes, TU München
*)
section \<open>Group relations\<close>

theory Group_Relations
  imports Finite_Product_Extend
begin

text \<open>We introduce the notion of a relation of a set of elements: a way to express the neutral
element by using only powers of said elements. The following predicate describes the set of all the
relations that one can construct from a set of elements.\<close>

definition (in comm_group) relations :: "'a set \<Rightarrow> ('a \<Rightarrow> int) set" where
  "relations A = {f. finprod G (\<lambda>a. a [^] f a) A = \<one>} \<inter> extensional A"

text \<open>Now some basic lemmas about relations.\<close>

lemma (in comm_group) in_relationsI[intro]:
  assumes "finprod G (\<lambda>a. a [^] f a) A = \<one>" "f \<in> extensional A"
  shows "f \<in> relations A"
  unfolding relations_def using assms by blast

lemma (in comm_group) triv_rel:
  "restrict (\<lambda>_. 0::int) A \<in> relations A"
proof
  show "(\<Otimes>a\<in>A. a [^] (\<lambda>_\<in>A. 0::int) a) = \<one>" by (intro finprod_one_eqI, simp)
qed simp

lemma (in comm_group) not_triv_relI:
  assumes "a \<in> A" "f a \<noteq> (0::int)"
  shows "f \<noteq> (\<lambda>_\<in>A. 0::int)"
  using assms by auto

lemma (in comm_group) rel_in_carr:
  assumes "A \<subseteq> carrier G" "r \<in> relations A"
  shows "(\<lambda>a. a [^] r a) \<in> A \<rightarrow> carrier G"
  by (meson Pi_I assms(1) int_pow_closed subsetD)

text \<open>The following lemmas are of importance when proving the fundamental theorem of finitely
generated abelian groups in the case that there is just the trivial relation between a set of
generators. They all build up to the last lemma that then is actually used in the proof.\<close>

lemma (in comm_group) relations_zero_imp_pow_not_one:
  assumes "a \<in> A" "\<forall>f\<in>(relations A). f a = 0"
  shows "\<forall>z::int \<noteq> 0. a [^] z \<noteq> \<one>"
proof (rule ccontr; safe)
  fix z::int
  assume z: "z \<noteq> 0" "a [^] z = \<one>"
  have "restrict ((\<lambda>x. 0)(a := z)) A \<in> relations A"
    by (intro in_relationsI finprod_one_eqI, use z in auto)
  thus False using z assms by auto
qed

lemma (in comm_group) relations_zero_imp_ord_zero:
  assumes "a \<in> A" "\<forall>f\<in>(relations A). f a = 0"
  and "a \<in> carrier G"
  shows "ord a = 0"
  using assms relations_zero_imp_pow_not_one[OF assms(1, 2)]
  by (meson finite_cyclic_subgroup_int infinite_cyclic_subgroup_order)

lemma (in comm_group) finprod_relations_triv_harder_better_stronger:
  assumes "A \<subseteq> carrier G" "relations A = {(\<lambda>_\<in>A. 0::int)}"
  shows "\<forall>f \<in> Pi\<^sub>E A (\<lambda>a. generate G {a}). finprod G f A = \<one> \<longrightarrow> (\<forall>a\<in>A. f a = \<one>)"
proof(rule, rule)
  fix f
  assume f: "f \<in> (\<Pi>\<^sub>E a\<in>A. generate G {a})" "finprod G f A = \<one>"
  with generate_pow assms(1) have "\<forall>a\<in>A. \<exists>k::int. f a = a [^] k" by auto
  then obtain r::"'a \<Rightarrow> int" where r: "\<forall>a\<in>A. f a = a [^] r a" by metis
  have "restrict r A \<in> relations A"
  proof(intro in_relationsI)
    have "(\<Otimes>a\<in>A. a [^] restrict r A a) = finprod G f A"
      by (intro finprod_cong, use assms r in auto)
    thus "(\<Otimes>a\<in>A. a [^] restrict r A a) = \<one>" using f by simp
  qed simp
  with assms(2) have z: "restrict r A = (\<lambda>_\<in>A. 0)" by blast
  have "(restrict r A) a = r a" if "a \<in> A" for a using that by auto
  with r z show "\<forall>a\<in>A. f a = \<one>" by auto
qed

lemma (in comm_group) stronger_PiE_finprod_imp:
  assumes "A \<subseteq> carrier G" "\<forall>f \<in> Pi\<^sub>E A (\<lambda>a. generate G {a}). finprod G f A = \<one> \<longrightarrow> (\<forall>a\<in>A. f a = \<one>)"
  shows "\<forall>f \<in> Pi\<^sub>E ((\<lambda>a. generate G {a}) ` A) id.
         finprod G f ((\<lambda>a. generate G {a}) ` A) = \<one> \<longrightarrow> (\<forall>H\<in> (\<lambda>a. generate G {a}) ` A. f H = \<one>)"
proof(rule, rule)
  fix f
  assume f: "f \<in> Pi\<^sub>E ((\<lambda>a. generate G {a}) ` A) id" "finprod G f ((\<lambda>a. generate G {a}) ` A) = \<one>"
  define B where "B = inv_into A (\<lambda>a. generate G {a}) ` ((\<lambda>a. generate G {a}) ` A)"
  have Bs: "B \<subseteq> A"
  proof
    fix x
    assume x: "x \<in> B"
    then obtain C where C: "C \<in> ((\<lambda>a. generate G {a}) ` A)" "x = inv_into A (\<lambda>a. generate G {a}) C"
      unfolding B_def by blast
    then obtain c where c: "C = generate G {c}" "c \<in> A" by blast
    with C someI_ex[of "\<lambda>y. y \<in> A \<and> generate G {y} = C"] show "x \<in> A"
      unfolding inv_into_def by blast
  qed
  have sI: "(\<lambda>x. generate G {x}) ` B = (\<lambda>x. generate G {x}) ` A"
  proof
    show "(\<lambda>x. generate G {x}) ` B \<subseteq> (\<lambda>x. generate G {x}) ` A" using Bs by blast
    show "(\<lambda>x. generate G {x}) ` A \<subseteq> (\<lambda>x. generate G {x}) ` B"
    proof
      fix C
      assume C: "C \<in> (\<lambda>x. generate G {x}) ` A"
      then obtain x where x: "x = inv_into A (\<lambda>a. generate G {a}) C" unfolding B_def by blast
      then obtain c where c: "C = generate G {c}" "c \<in> A" using C by blast
      with C x someI_ex[of "\<lambda>y. y \<in> A \<and> generate G {y} = C"] have "generate G {x} = C"
        unfolding inv_into_def by blast
      with x C show "C \<in> (\<lambda>x. generate G {x}) ` B" unfolding B_def by blast
    qed
  qed
  have fBc: "f (generate G {b}) \<in> carrier G" if "b \<in> B" for b
  proof -
    have "f (generate G {b}) \<in> generate G {b}" using f(1)
      by (subst (asm) sI[symmetric], use that in fastforce)
    moreover have "generate G {b} \<subseteq> carrier G" using assms(1) that Bs generate_incl by blast
    ultimately show ?thesis by blast
  qed
  let ?r = "restrict (\<lambda>a. if a\<in>B then f (generate G {a}) else \<one>) A"
  have "?r \<in> Pi\<^sub>E A (\<lambda>a. generate G {a})"
  proof
    show "?r x = undefined" if "x \<notin> A" for x using that by simp
    show "?r x \<in> generate G {x}" if "x \<in> A" for x using that generate.one B_def f(1) by auto
  qed
  moreover have "finprod G ?r A = \<one>"
  proof (cases "finite A")
    case True
    have "A = B \<union> (A - B)" using Bs by auto
    then have "finprod G ?r A = finprod G ?r (B\<union>(A-B))" by auto
    moreover have "\<dots> = finprod G ?r B \<otimes> finprod G ?r (A - B)"
    proof(intro finprod_Un_disjoint)
      from True Bs finite_subset show "finite B" "finite (A - B)" "B \<inter> (A - B) = {}" by auto
      show "(\<lambda>a\<in>A. if a \<in> B then f (generate G {a}) else \<one>) \<in> A - B \<rightarrow> carrier G" using Bs by simp
      from fBc show "(\<lambda>a\<in>A. if a \<in> B then f (generate G {a}) else \<one>) \<in> B \<rightarrow> carrier G"
        using Bs by auto
    qed
    moreover have "finprod G ?r B = \<one>"
    proof -
      have "finprod G ?r B = finprod G (f \<circ> (\<lambda>a. generate G {a})) B"
      proof(intro finprod_cong')
        show "?r b = (f \<circ> (\<lambda>a. generate G {a})) b" if "b \<in> B" for b using that Bs by auto
        show "f \<circ> (\<lambda>a. generate G {a}) \<in> B \<rightarrow> carrier G" using fBc by simp
      qed simp
      also have "\<dots> = finprod G f ((\<lambda>a. generate G {a}) ` B)"
      proof(intro finprod_comp[symmetric])
        show "(f \<circ> (\<lambda>a. generate G {a})) ` B \<subseteq> carrier G" using fBc by auto
        show "inj_on (\<lambda>a. generate G {a}) B"
          by (intro inj_onI, unfold B_def, metis (no_types, lifting) f_inv_into_f inv_into_into)
      qed
      also have "\<dots> = finprod G f ((\<lambda>a. generate G {a}) ` A)" using sI by argo
      finally show ?thesis using f(2) by argo
    qed
    moreover have "finprod G ?r (A - B) = \<one>" by(intro finprod_one_eqI, simp)
    ultimately show ?thesis by fastforce
  next
    case False
    then show ?thesis unfolding finprod_def by simp
  qed
  ultimately have a: "\<forall>a\<in>A. ?r a = \<one>" using assms(2) by blast
  then have BA: "\<forall>a\<in>B\<inter>A. ?r a = \<one>" by blast
  from Bs sI have "\<forall>a\<in>A. (generate G {a}) \<in> ((\<lambda>x. generate G {x}) ` B)" by simp
  then have "\<forall>a\<in>A. \<exists>b\<in>B. f (generate G {a}) = f (generate G {b})" by force
  thus "\<forall>H\<in>(\<lambda>a. generate G {a}) ` A. f H = \<one>" using a BA Bs by fastforce
qed

lemma (in comm_group) finprod_relations_triv:
  assumes "A \<subseteq> carrier G" "relations A = {(\<lambda>_\<in>A. 0::int)}"
  shows "\<forall>f \<in> Pi\<^sub>E ((\<lambda>a. generate G {a}) ` A) id.
         finprod G f ((\<lambda>a. generate G {a}) ` A) = \<one> \<longrightarrow> (\<forall>H\<in> (\<lambda>a. generate G {a}) ` A. f H = \<one>)"
  using assms finprod_relations_triv_harder_better_stronger stronger_PiE_finprod_imp by presburger

lemma (in comm_group) ord_zero_strong_imp_rel_triv:
  assumes "A \<subseteq> carrier G" "\<forall>a \<in> A. ord a = 0"
  and "\<forall>f \<in> Pi\<^sub>E A (\<lambda>a. generate G {a}). finprod G f A = \<one> \<longrightarrow> (\<forall>a\<in>A. f a = \<one>)"
  shows "relations A = {(\<lambda>_\<in>A. 0::int)}"
proof -
  have "\<And>r. r \<in> relations A \<Longrightarrow> r = (\<lambda>_\<in>A. 0::int)"
  proof
    fix r x
    assume r: "r \<in> relations A"
    show "r x = (\<lambda>_\<in>A. 0::int) x"
    proof (cases "x \<in> A")
      case True
      let ?r = "restrict (\<lambda>a. a [^] r a) A"
      have rp: "?r \<in> Pi\<^sub>E A (\<lambda>a. generate G {a})"
      proof -
        have "?r \<in> extensional A" by blast
        moreover have "?r \<in> Pi A (\<lambda>a. generate G {a})"
        proof
          fix a
          assume a: "a \<in> A"
          then have sga: "subgroup (generate G {a}) G" using generate_is_subgroup assms(1) by auto
          show "a [^] r a \<in> generate G {a}"
            using generate.incl[of a "{a}" G] subgroup_int_pow_closed[OF sga] by simp
        qed
        ultimately show ?thesis unfolding PiE_def by blast
      qed
      have "finprod G ?r A = (\<Otimes>a\<in>A. a [^] r a)" by(intro finprod_cong, use assms(1) in auto)
      with r have "finprod G ?r A = \<one>" unfolding relations_def by simp
      with assms(3) rp have "\<forall>a\<in>A. ?r a = \<one>" by fast
      then have "\<forall>a\<in>A. a [^] r a = \<one>" by simp
      with assms(1, 2) True have "r x = 0"
        using finite_cyclic_subgroup_int infinite_cyclic_subgroup_order by blast
      thus ?thesis using True by simp
    next
      case False
      thus ?thesis using r unfolding relations_def extensional_def by simp
    qed
  qed
  thus ?thesis using triv_rel by blast
qed

lemma (in comm_group) compl_fam_iff_relations_triv:
  assumes "finite gs" "gs \<subseteq> carrier G" "\<forall>g\<in>gs. ord g = 0"
  shows "relations gs = {(\<lambda>_\<in>gs. 0::int)} \<longleftrightarrow> compl_fam (\<lambda>g. generate G {g}) gs"
  using triv_finprod_iff_compl_fam_PiE[of _ "\<lambda>g. generate G {g}", OF assms(1) generate_is_subgroup]
        ord_zero_strong_imp_rel_triv[OF assms(2, 3)]
        finprod_relations_triv_harder_better_stronger[OF assms(2)] assms by blast

end
