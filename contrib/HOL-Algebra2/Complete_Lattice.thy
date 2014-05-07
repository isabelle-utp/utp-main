theory Complete_Lattice
imports Lattice FType
begin

subsection {* Complete Lattices *}

locale weak_complete_lattice = weak_lattice +
  assumes sup_exists:
    "[| A \<subseteq> carrier L |] ==> EX s. least L s (Upper L A)"
    and inf_exists:
    "[| A \<subseteq> carrier L |] ==> EX i. greatest L i (Lower L A)"

text {* Introduction rule: the usual definition of complete lattice *}

lemma (in weak_partial_order) weak_complete_latticeI:
  assumes sup_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX s. least L s (Upper L A)"
    and inf_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX i. greatest L i (Lower L A)"
  shows "weak_complete_lattice L"
  by default (auto intro: sup_exists inf_exists)

lemma (in weak_complete_lattice) dual_weak_complete_lattice:
  "weak_complete_lattice (inv_gorder L)"
proof -
  interpret dual: weak_lattice "inv_gorder L"
    by (metis dual_weak_lattice)

  show ?thesis
    apply (unfold_locales)
    apply (simp_all add:inf_exists sup_exists)
  done
qed

lemma (in weak_complete_lattice) supI:
  "[| !!l. least L l (Upper L A) ==> P l; A \<subseteq> carrier L |]
  ==> P (\<Squnion>A)"
proof (unfold sup_def)
  assume L: "A \<subseteq> carrier L"
    and P: "!!l. least L l (Upper L A) ==> P l"
  with sup_exists obtain s where "least L s (Upper L A)" by blast
  with L show "P (SOME l. least L l (Upper L A))"
  by (fast intro: someI2 weak_least_unique P)
qed

lemma (in weak_complete_lattice) sup_closed [simp]:
  "A \<subseteq> carrier L ==> \<Squnion>A \<in> carrier L"
  by (rule supI) simp_all

sublocale weak_complete_lattice \<subseteq> weak_bounded_lattice
  apply (unfold_locales)
  apply (metis Upper_empty empty_subsetI sup_exists)
  apply (metis Lower_empty empty_subsetI inf_exists)
done

lemma (in weak_complete_lattice) infI:
  "[| !!i. greatest L i (Lower L A) ==> P i; A \<subseteq> carrier L |]
  ==> P (\<Sqinter>A)"
proof (unfold inf_def)
  assume L: "A \<subseteq> carrier L"
    and P: "!!l. greatest L l (Lower L A) ==> P l"
  with inf_exists obtain s where "greatest L s (Lower L A)" by blast
  with L show "P (SOME l. greatest L l (Lower L A))"
  by (fast intro: someI2 weak_greatest_unique P)
qed

lemma (in weak_complete_lattice) inf_closed [simp]:
  "A \<subseteq> carrier L ==> \<Sqinter>A \<in> carrier L"
  by (rule infI) simp_all

theorem (in weak_partial_order) weak_complete_lattice_criterion1:
  assumes top_exists: "EX g. greatest L g (carrier L)"
    and inf_exists:
      "!!A. [| A \<subseteq> carrier L; A ~= {} |] ==> EX i. greatest L i (Lower L A)"
  shows "weak_complete_lattice L"
proof (rule weak_complete_latticeI)
  from top_exists obtain top where top: "greatest L top (carrier L)" ..
  fix A
  assume L: "A \<subseteq> carrier L"
  let ?B = "Upper L A"
  from L top have "top \<in> ?B" by (fast intro!: Upper_memI intro: greatest_le)
  then have B_non_empty: "?B ~= {}" by fast
  have B_L: "?B \<subseteq> carrier L" by simp
  from inf_exists [OF B_L B_non_empty]
  obtain b where b_inf_B: "greatest L b (Lower L ?B)" ..
  have "least L b (Upper L A)"
apply (rule least_UpperI)
   apply (rule greatest_le [where A = "Lower L ?B"])
    apply (rule b_inf_B)
   apply (rule Lower_memI)
    apply (erule Upper_memD [THEN conjunct1])
     apply assumption
    apply (rule L)
   apply (fast intro: L [THEN subsetD])
  apply (erule greatest_Lower_below [OF b_inf_B])
  apply simp
 apply (rule L)
apply (rule greatest_closed [OF b_inf_B])
done
  then show "EX s. least L s (Upper L A)" ..
next
  fix A
  assume L: "A \<subseteq> carrier L"
  show "EX i. greatest L i (Lower L A)"
  proof (cases "A = {}")
    case True then show ?thesis
      by (simp add: top_exists)
  next
    case False with L show ?thesis
      by (rule inf_exists)
  qed
qed

(* TODO: prove dual version *)


text {* Supremum *}

declare (in partial_order) weak_sup_of_singleton [simp del]

lemma (in partial_order) sup_of_singleton [simp]:
  "x \<in> carrier L ==> \<Squnion>{x} = x"
  using weak_sup_of_singleton unfolding eq_is_equal .

lemma (in upper_semilattice) join_assoc_lemma:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<squnion> (y \<squnion> z) = \<Squnion>{x, y, z}"
  using weak_join_assoc_lemma L unfolding eq_is_equal .

lemma (in upper_semilattice) join_assoc:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
  using weak_join_assoc L unfolding eq_is_equal .

text {* Infimum *}

declare (in partial_order) weak_inf_of_singleton [simp del]

lemma (in partial_order) inf_of_singleton [simp]:
  "x \<in> carrier L ==> \<Sqinter>{x} = x"
  using weak_inf_of_singleton unfolding eq_is_equal .

text {* Condition on @{text A}: infimum exists. *}

lemma (in lower_semilattice) meet_assoc_lemma:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "x \<sqinter> (y \<sqinter> z) = \<Sqinter>{x, y, z}"
  using weak_meet_assoc_lemma L unfolding eq_is_equal .

lemma (in lower_semilattice) meet_assoc:
  assumes L: "x \<in> carrier L"  "y \<in> carrier L"  "z \<in> carrier L"
  shows "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
  using weak_meet_assoc L unfolding eq_is_equal .

text {* Infimum Laws *}

context weak_complete_lattice
begin

lemma inf_glb: 
  assumes "A \<subseteq> carrier L"
  shows "greatest L (\<Sqinter>A) (Lower L A)"
proof -
  obtain i where "greatest L i (Lower L A)"
    by (metis assms inf_exists)

  thus ?thesis
    apply (simp add:inf_def)
    apply (rule someI2[of _ "i"])
    apply (auto)
  done
qed

lemma inf_lower:
  assumes "A \<subseteq> carrier L" "x \<in> A"
  shows "\<Sqinter>A \<sqsubseteq> x"
  by (metis assms greatest_Lower_below inf_glb)

lemma inf_greatest: 
  assumes "A \<subseteq> carrier L" "z \<in> carrier L" 
          "(\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x)"
  shows "z \<sqsubseteq> \<Sqinter>A"
  by (metis Lower_memI assms greatest_le inf_glb)

lemma weak_inf_empty [simp]: "\<Sqinter>{} .= \<top>"
  by (metis Lower_empty empty_subsetI inf_glb top_greatest weak_greatest_unique)

lemma weak_inf_carrier [simp]: "\<Sqinter>carrier L .= \<bottom>"
  by (metis bottom_weak_eq inf_closed inf_lower subset_refl)

lemma weak_inf_insert [simp]: 
  "\<lbrakk> a \<in> carrier L; A \<subseteq> carrier L \<rbrakk> \<Longrightarrow> \<Sqinter>insert a A .= a \<sqinter> \<Sqinter>A"
  apply (rule weak_le_antisym)
  apply (force intro: weak_le_antisym meet_le inf_lower inf_greatest inf_lower inf_closed)
  apply (rule inf_greatest)
  apply (force)
  apply (force intro: inf_closed)
  apply (auto)
  apply (metis inf_closed meet_left)
  apply (force intro: le_trans inf_closed meet_right meet_left inf_lower)
done

text {* Supremum Laws *}

lemma sup_lub: 
  assumes "A \<subseteq> carrier L"
  shows "least L (\<Squnion>A) (Upper L A)"
    by (metis Upper_is_closed assms least_closed least_cong supI sup_closed sup_exists weak_least_unique)

lemma sup_upper: 
  assumes "A \<subseteq> carrier L" "x \<in> A"
  shows "x \<sqsubseteq> \<Squnion>A"
  by (metis assms least_Upper_above supI)

lemma sup_least:
  assumes "A \<subseteq> carrier L" "z \<in> carrier L" 
          "(\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> z)" 
  shows "\<Squnion>A \<sqsubseteq> z"
  by (metis Upper_memI assms least_le sup_lub)

lemma weak_sup_empty [simp]: "\<Squnion>{} .= \<bottom>"
  by (metis Upper_empty bottom_least empty_subsetI sup_lub weak_least_unique)

lemma weak_sup_carrier [simp]: "\<Squnion>carrier L .= \<top>"
  by (metis Lower_closed Lower_empty sup_closed sup_upper top_closed top_higher weak_le_antisym)

lemma weak_sup_insert [simp]: 
  "\<lbrakk> a \<in> carrier L; A \<subseteq> carrier L \<rbrakk> \<Longrightarrow> \<Squnion>insert a A .= a \<squnion> \<Squnion>A"
  apply (rule weak_le_antisym)
  apply (rule sup_least)
  apply (auto)
  apply (metis join_left sup_closed)
  apply (rule le_trans) defer
  apply (rule join_right)
  apply (auto)
  apply (rule join_le)
  apply (auto intro: sup_upper sup_least sup_closed)
done

text {* Least fixed points *}

lemma LFP_closed [intro, simp]:
  "\<mu> f \<in> carrier L"
  by (metis (lifting) LFP_def inf_closed mem_Collect_eq subsetI)

lemma LFP_lowerbound: 
  assumes "x \<in> carrier L" "f x \<sqsubseteq> x" 
  shows "\<mu> f \<sqsubseteq> x"
  by (auto intro:inf_lower assms simp add:LFP_def)

lemma LFP_greatest: 
  assumes "x \<in> carrier L" 
          "(\<And>u. \<lbrakk> u \<in> carrier L; f u \<sqsubseteq> u \<rbrakk> \<Longrightarrow> x \<sqsubseteq> u)"
  shows "x \<sqsubseteq> \<mu> f"
  by (auto simp add:LFP_def intro:inf_greatest assms)

lemma LFP_lemma2: 
  assumes "Mono f" "f \<in> carrier L \<rightarrow> carrier L"
  shows "f (\<mu> f) \<sqsubseteq> \<mu> f"
  using assms
  apply (auto simp add:ftype_def)
  apply (rule LFP_greatest)
  apply (metis LFP_closed)
  apply (metis LFP_closed LFP_lowerbound le_trans use_iso1)
done

lemma LFP_lemma3: 
  assumes "Mono f" "f \<in> carrier L \<rightarrow> carrier L"
  shows "\<mu> f \<sqsubseteq> f (\<mu> f)"
  using assms
  apply (auto simp add:ftype_def)
  apply (metis LFP_closed LFP_lemma2 LFP_lowerbound assms(2) use_iso2)
done

lemma ftype_carrier [intro]:
  "\<lbrakk> x \<in> carrier L; f \<in> carrier L \<rightarrow> carrier L \<rbrakk> \<Longrightarrow> f(x) \<in> carrier L"
  by (simp add: typed_application)

lemma LFP_weak_unfold: 
  "\<lbrakk> Mono f; f \<in> carrier L \<rightarrow> carrier L \<rbrakk> \<Longrightarrow> \<mu> f .= f (\<mu> f)"
  by (auto intro: LFP_closed LFP_lemma2 LFP_lemma3 weak_le_antisym)

lemma GFP_closed [intro, simp]:
  "\<nu> f \<in> carrier L"
  by (auto intro:sup_closed simp add:GFP_def)
  
lemma GFP_upperbound:
  assumes "x \<in> carrier L" "x \<sqsubseteq> f x"
  shows "x \<sqsubseteq> \<nu> f"
  by (auto intro:sup_upper assms simp add:GFP_def)

lemma GFP_least: 
  assumes "x \<in> carrier L" 
          "(\<And>u. \<lbrakk> u \<in> carrier L; u \<sqsubseteq> f u \<rbrakk> \<Longrightarrow> u \<sqsubseteq> x)"
  shows "\<nu> f \<sqsubseteq> x"
  by (auto simp add:GFP_def intro:sup_least assms)

lemma GFP_lemma2:
  assumes "Mono f" "f \<in> carrier L \<rightarrow> carrier L"
  shows "\<nu> f \<sqsubseteq> f (\<nu> f)"
  using assms
  apply (auto simp add:ftype_def)
  apply (rule GFP_least)
  apply (metis GFP_closed assms(2))
  apply (metis GFP_closed GFP_upperbound assms le_trans use_iso2)
done

lemma GFP_lemma3:
  assumes "Mono f" "f \<in> carrier L \<rightarrow> carrier L"
  shows "f (\<nu> f) \<sqsubseteq> \<nu> f"
  by (metis GFP_closed GFP_lemma2 GFP_upperbound assms ftype_carrier use_iso2)
  
lemma GFP_weak_unfold: 
  "\<lbrakk> Mono f; f \<in> carrier L \<rightarrow> carrier L \<rbrakk> \<Longrightarrow> \<nu> f .= f (\<nu> f)"
  by (auto intro: GFP_closed GFP_lemma2 GFP_lemma3 weak_le_antisym)

end

text {* Total orders are lattices. *}

sublocale total_order < weak: lattice
  by default (auto intro: sup_of_two_exists inf_of_two_exists)

text {* Complete lattices *}

locale complete_lattice = lattice +
  assumes sup_exists:
    "[| A \<subseteq> carrier L |] ==> EX s. least L s (Upper L A)"
    and inf_exists:
    "[| A \<subseteq> carrier L |] ==> EX i. greatest L i (Lower L A)"

sublocale complete_lattice < weak: weak_complete_lattice
  by default (auto intro: sup_exists inf_exists)

text {* Introduction rule: the usual definition of complete lattice *}

lemma (in partial_order) complete_latticeI:
  assumes sup_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX s. least L s (Upper L A)"
    and inf_exists:
    "!!A. [| A \<subseteq> carrier L |] ==> EX i. greatest L i (Lower L A)"
  shows "complete_lattice L"
  by default (auto intro: sup_exists inf_exists)

theorem (in partial_order) complete_lattice_criterion1:
  assumes top_exists: "EX g. greatest L g (carrier L)"
    and inf_exists:
      "!!A. [| A \<subseteq> carrier L; A ~= {} |] ==> EX i. greatest L i (Lower L A)"
  shows "complete_lattice L"
proof (rule complete_latticeI)
  from top_exists obtain top where top: "greatest L top (carrier L)" ..
  fix A
  assume L: "A \<subseteq> carrier L"
  let ?B = "Upper L A"
  from L top have "top \<in> ?B" by (fast intro!: Upper_memI intro: greatest_le)
  then have B_non_empty: "?B ~= {}" by fast
  have B_L: "?B \<subseteq> carrier L" by simp
  from inf_exists [OF B_L B_non_empty]
  obtain b where b_inf_B: "greatest L b (Lower L ?B)" ..
  have "least L b (Upper L A)"
apply (rule least_UpperI)
   apply (rule greatest_le [where A = "Lower L ?B"])
    apply (rule b_inf_B)
   apply (rule Lower_memI)
    apply (erule Upper_memD [THEN conjunct1])
     apply assumption
    apply (rule L)
   apply (fast intro: L [THEN subsetD])
  apply (erule greatest_Lower_below [OF b_inf_B])
  apply simp
 apply (rule L)
apply (rule greatest_closed [OF b_inf_B])
done
  then show "EX s. least L s (Upper L A)" ..
next
  fix A
  assume L: "A \<subseteq> carrier L"
  show "EX i. greatest L i (Lower L A)"
  proof (cases "A = {}")
    case True then show ?thesis
      by (simp add: top_exists)
  next
    case False with L show ?thesis
      by (rule inf_exists)
  qed
qed

(* TODO: prove dual version *)


context complete_lattice
begin

lemma LFP_unfold: 
  "\<lbrakk> Mono f; f \<in> carrier L \<rightarrow> carrier L \<rbrakk> \<Longrightarrow> \<mu> f = f (\<mu> f)"
  by (auto intro: LFP_closed LFP_lemma2 LFP_lemma3 le_antisym)

lemma GFP_unfold:
  "\<lbrakk> Mono f; f \<in> carrier L \<rightarrow> carrier L \<rbrakk> \<Longrightarrow> \<nu> f = f (\<nu> f)"
  by (auto intro: GFP_closed GFP_lemma2 GFP_lemma3 le_antisym)

end

subsection {* Examples *}

subsubsection {* The Powerset of a Set is a Complete Lattice *}

theorem powerset_is_complete_lattice:
  "complete_lattice (| carrier = Pow A, eq = op =, le = op \<subseteq> |)"
  (is "complete_lattice ?L")
proof (rule partial_order.complete_latticeI)
  show "partial_order ?L"
    by default auto
next
  fix B
  assume "B \<subseteq> carrier ?L"
  then have "least ?L (\<Union> B) (Upper ?L B)"
    by (fastforce intro!: least_UpperI simp: Upper_def)
  then show "EX s. least ?L s (Upper ?L B)" ..
next
  fix B
  assume "B \<subseteq> carrier ?L"
  then have "greatest ?L (\<Inter> B \<inter> A) (Lower ?L B)"
    txt {* @{term "\<Inter> B"} is not the infimum of @{term B}:
      @{term "\<Inter> {} = UNIV"} which is in general bigger than @{term "A"}! *}
    by (fastforce intro!: greatest_LowerI simp: Lower_def)
  then show "EX i. greatest ?L i (Lower ?L B)" ..
qed

text {* An other example, that of the lattice of subgroups of a group,
  can be found in Group theory (Section~\ref{sec:subgroup-lattice}). *}

end
