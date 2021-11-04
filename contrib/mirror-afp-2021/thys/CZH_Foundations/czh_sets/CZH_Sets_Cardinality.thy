(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Cardinality\<close>
theory CZH_Sets_Cardinality
  imports 
    CZH_Sets_Nat
    CZH_Sets_Equipollence
begin



subsection\<open>Background\<close>


text\<open>
The section presents further results about the cardinality of terms of the type
\<^typ>\<open>V\<close>. The emphasis of this work, however, is on the development of a theory of
finite sets internalized in the type \<^typ>\<open>V\<close>.

Many of the results that are presented in this section were carried over
(with amendments) from the theory \<open>Finite\<close> in the main library of Isabelle/HOL.
\<close>

declare One_nat_def[simp del]



subsection\<open>Cardinality of an arbitrary set\<close>


text\<open>Elementary properties.\<close>

lemma vcard_veqpoll: "vcard A = vcard B \<longleftrightarrow> A \<approx>\<^sub>\<circ> B"
  by (metis cardinal_cong cardinal_eqpoll eqpoll_sym eqpoll_trans)

lemma vcard_vlepoll: "vcard A \<le> vcard B \<longleftrightarrow> A \<lesssim>\<^sub>\<circ> B"
proof
  assume "vcard A \<le> vcard B"
  moreover have "vcard A \<approx>\<^sub>\<circ> A" by (rule cardinal_eqpoll)
  moreover have "vcard B \<approx>\<^sub>\<circ> B" by (rule cardinal_eqpoll)
  ultimately show "A \<lesssim>\<^sub>\<circ> B"
    by (meson eqpoll_sym lepoll_trans1 lepoll_trans2 vlepoll_vsubset)
qed (simp add: lepoll_imp_Card_le)

lemma vcard_vempty: "vcard A = 0 \<longleftrightarrow> A = 0"
proof-
  have vcard_A: "vcard A \<approx>\<^sub>\<circ> A" by (simp add: cardinal_eqpoll)
  then show ?thesis using eq0_iff eqpoll_iff_bijections by metis
qed

lemmas vcard_vemptyD = vcard_vempty[THEN iffD1]
  and vcard_vemptyI = vcard_vempty[THEN iffD2]

lemma vcard_neq_vempty: "vcard A \<noteq> 0\<^sub>\<nat> \<longleftrightarrow> A \<noteq> 0\<^sub>\<nat>"
  using vcard_vempty by auto

lemmas vcard_neq_vemptyD = vcard_neq_vempty[THEN iffD1]
  and vcard_neq_vemptyI = vcard_neq_vempty[THEN iffD2]


text\<open>Set operations.\<close>

lemma vcard_mono:
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "vcard A \<le> vcard B"
  using assms by (simp add: lepoll_imp_Card_le vlepoll_vsubset)

lemma vcard_vinsert_in[simp]:
  assumes "a \<in>\<^sub>\<circ> A"
  shows "vcard (vinsert a A) = vcard A"
  using assms by (simp add: cardinal_cong insert_absorb)

lemma vcard_vintersection_left: "vcard (A \<inter>\<^sub>\<circ> B) \<le> vcard A" 
  by (simp add: vcard_mono)

lemma vcard_vintersection_right: "vcard (A \<inter>\<^sub>\<circ> B) \<le> vcard B" 
  by (simp add: vcard_mono)

lemma vcard_vunion: 
  assumes "vdisjnt A B"
  shows "vcard (A \<union>\<^sub>\<circ> B) = vcard A \<oplus> vcard B"
  using assms by (rule vcard_disjoint_sup)

lemma vcard_vdiff[simp]: "vcard (A -\<^sub>\<circ> B) \<oplus> vcard (A \<inter>\<^sub>\<circ> B) = vcard A"
proof-
  have ABB: "vdisjnt (A -\<^sub>\<circ> B) (A \<inter>\<^sub>\<circ> B)" by auto
  have "A -\<^sub>\<circ> B \<union>\<^sub>\<circ> A \<inter>\<^sub>\<circ> B = A" by auto
  from vcard_vunion[OF ABB, unfolded this] show ?thesis ..
qed

lemma vcard_vdiff_vsubset:
  assumes "B \<subseteq>\<^sub>\<circ> A"
  shows "vcard (A -\<^sub>\<circ> B) \<oplus> vcard B = vcard A"
  by (metis assms inf.absorb_iff2 vcard_vdiff)


text\<open>Connections.\<close>

lemma (in vsv) vsv_vcard_vdomain: "vcard (\<D>\<^sub>\<circ> r) = vcard r"
  unfolding vcard_veqpoll 
proof-
  define f where "f x = \<langle>x, r\<lparr>x\<rparr>\<rangle>" for x
  have "bij_betw f (elts (\<D>\<^sub>\<circ> r)) (elts r)" 
    unfolding f_def bij_betw_def
  proof(intro conjI inj_onI subset_antisym subsetI)
    from vlrestriction_vdomain show 
      "x \<in>\<^sub>\<circ> r \<Longrightarrow> x \<in> (\<lambda>x. \<langle>x, r\<lparr>x\<rparr>\<rangle>) ` elts (\<D>\<^sub>\<circ> r)" 
      for x
      unfolding mem_Collect_eq by blast
  qed (auto simp: image_def)
  then show "\<D>\<^sub>\<circ> r \<approx>\<^sub>\<circ> r" unfolding eqpoll_def by auto
qed


text\<open>Special properties.\<close>

lemma vcard_vunion_vintersection: 
  "vcard (A \<union>\<^sub>\<circ> B) \<oplus> vcard (A \<inter>\<^sub>\<circ> B) = vcard A \<oplus> vcard B"
proof-
  have AB_ABB: "A \<union>\<^sub>\<circ> B = B \<union>\<^sub>\<circ> (A -\<^sub>\<circ> B)" by auto
  have ABB: "vdisjnt B (A -\<^sub>\<circ> B)" by auto
  show ?thesis
    unfolding vcard_vunion[OF ABB, folded AB_ABB] cadd_assoc vcard_vdiff
    by (simp add: cadd_commute)
qed



subsection\<open>Finite sets\<close>

abbreviation vfinite :: "V \<Rightarrow> bool" 
  where "vfinite A \<equiv> finite (elts A)"

lemma vfinite_def: "vfinite A \<longleftrightarrow> (\<exists>n\<in>\<^sub>\<circ>\<omega>. n \<approx>\<^sub>\<circ> A)"  
proof
  assume "finite (elts A)"
  then obtain n :: nat where eltsA: "elts A \<approx> {..<n}" 
    by (simp add: eqpoll_iff_card)
  have on: "ord_of_nat n = set (ord_of_nat ` {..<n})"
    by (simp add: ord_of_nat_eq_initial[symmetric])
  from eltsA have "elts A \<approx> elts (ord_of_nat n)" 
    unfolding on by (simp add: inj_on_def)
  moreover have "ord_of_nat n \<in>\<^sub>\<circ> \<omega>" by (simp add: \<omega>_def)
  ultimately show "\<exists>n\<in>\<^sub>\<circ>\<omega>. n \<approx>\<^sub>\<circ> A" by (auto intro: eqpoll_sym)
next
  assume "\<exists>n\<in>\<^sub>\<circ>\<omega>. n \<approx>\<^sub>\<circ> A" 
  then obtain n where "n \<in>\<^sub>\<circ> \<omega>" and "n \<approx>\<^sub>\<circ> A" by auto
  with eqpoll_finite_iff show "finite (elts A)"
    by (auto intro: finite_Ord_omega)
qed


text\<open>Rules.\<close>

lemmas vfiniteI[intro!] = vfinite_def[THEN iffD2]  

lemmas vfiniteD[dest!] = vfinite_def[THEN iffD1]

lemma vfiniteE1[elim!]:
  assumes "vfinite A" and "\<exists>n\<in>\<^sub>\<circ>\<omega>. n \<approx>\<^sub>\<circ> A \<Longrightarrow> P"
  shows P
  using assms by auto

lemma vfiniteE2[elim]:
  assumes "vfinite A" 
  obtains n where "n \<in>\<^sub>\<circ> \<omega>" and "n \<approx>\<^sub>\<circ> A"
  using assms by auto


text\<open>Elementary properties.\<close>

lemma veqpoll_omega_vcard[intro, simp]:
  assumes "n \<in>\<^sub>\<circ> \<omega>" and "n \<approx>\<^sub>\<circ> A" 
  shows "vcard A = n"
  using 
    nat_into_Card[OF assms(1), unfolded Card_def] 
    cardinal_cong[OF assms(2)] 
  by simp

lemma (in vsv) vfinite_vimage[intro]:
  assumes "vfinite A"
  shows "vfinite (r `\<^sub>\<circ> A)"
proof-
  have rA: "r `\<^sub>\<circ> A = r `\<^sub>\<circ> (\<D>\<^sub>\<circ> r \<inter>\<^sub>\<circ> A)" by fast
  have DrA: "\<D>\<^sub>\<circ> r \<inter>\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> r" by simp
  show ?thesis by (simp add: inf_V_def assms vimage_image[OF DrA, folded rA])
qed

lemmas [intro] = vsv.vfinite_vimage

lemma vfinite_veqpoll_trans:
  assumes "vfinite A" and "A \<approx>\<^sub>\<circ> B" 
  shows "vfinite B"
  using assms by (simp add: eqpoll_finite_iff)

lemma vfinite_vlepoll_trans:
  assumes "vfinite A" and "B \<lesssim>\<^sub>\<circ> A"   
  shows "vfinite B"
  by (meson assms eqpoll_finite_iff finite_lepoll_infinite lepoll_antisym)

lemma vfinite_vlesspoll_trans:
  assumes "vfinite A" and "B \<prec>\<^sub>\<circ> A"   
  shows "vfinite B"
  using assms by (auto simp: vlesspoll_def vfinite_vlepoll_trans)


text\<open>Induction.\<close>

lemma vfinite_induct[consumes 1, case_names vempty vinsert]:
  assumes "vfinite F"
    and "P 0"
    and "\<And>x F. \<lbrakk>vfinite F; x \<notin>\<^sub>\<circ> F; P F\<rbrakk> \<Longrightarrow> P (vinsert x F)"
  shows "P F"
proof-

  from assms(1) obtain n where n: "n \<in>\<^sub>\<circ> \<omega>" and "n \<approx>\<^sub>\<circ> F" by clarsimp
  then obtain f'' where bij: "bij_betw f'' (elts n) (elts F)" 
    unfolding eqpoll_def by clarsimp
  define f where "f = (\<lambda>a\<in>\<^sub>\<circ>n. f'' a)"
  interpret v11 f 
    unfolding f_def
  proof(intro v11I)
    show "vsv ((\<lambda>a\<in>\<^sub>\<circ>n. f'' a)\<inverse>\<^sub>\<circ>)"
    proof(intro vsvI)
      fix a b c 
      assume "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>n. f'' a)\<inverse>\<^sub>\<circ>" and "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>n. f'' a)\<inverse>\<^sub>\<circ>"
      then have "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>n. f'' a)" 
        and "\<langle>c, a\<rangle> \<in>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>n. f'' a)" 
        and "b \<in>\<^sub>\<circ> n" 
        and "c \<in>\<^sub>\<circ> n"
        by auto
      moreover then have "f'' b = f'' c" by auto
      ultimately show "b = c" using bij by (metis bij_betw_iff_bijections)
    qed auto
  qed auto
  have dom_f: "\<D>\<^sub>\<circ> f = n" unfolding f_def by clarsimp
  have ran_f: "\<R>\<^sub>\<circ> f = F"
  proof(intro vsubset_antisym vsubsetI)
    fix b assume "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> f"
    then obtain a where "a \<in>\<^sub>\<circ> n" and "b = f'' a" unfolding f_def by auto
    then show "b \<in>\<^sub>\<circ> F" by (meson bij bij_betw_iff_bijections)
  next
    fix b assume "b \<in>\<^sub>\<circ> F"
    then obtain a where "a \<in>\<^sub>\<circ> n" and "b = f'' a" 
      by (metis bij bij_betw_iff_bijections)
    then show "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> f" unfolding f_def by auto
  qed

  define f' where "f' n = f `\<^sub>\<circ> n" for n
  have F_def: "F = f' n" 
    unfolding f'_def using dom_f ran_f vimage_vdomain by clarsimp
  have "v11 (\<lambda>a\<in>\<^sub>\<circ>n. f' a)"
  proof(intro vsv.vsv_valneq_v11I, unfold vdomain_VLambda)
    show "vsv (\<lambda>a\<in>\<^sub>\<circ>n. f' a)" by simp
    fix x y assume xD: "x \<in>\<^sub>\<circ> n" and yD: "y \<in>\<^sub>\<circ> n" and xy: "x \<noteq> y"
    from \<open>x \<in>\<^sub>\<circ> n\<close> \<open>y \<in>\<^sub>\<circ> n\<close> \<open>n \<in>\<^sub>\<circ> \<omega>\<close> have xn: "x \<subseteq>\<^sub>\<circ> n" and yn: "y \<subseteq>\<^sub>\<circ> n"
      by (simp_all add: OrdmemD order.strict_implies_order)
    show "(\<lambda>a\<in>\<^sub>\<circ>n. f' a)\<lparr>x\<rparr> \<noteq> (\<lambda>a\<in>\<^sub>\<circ>n. f' a)\<lparr>y\<rparr>"
      unfolding beta[OF xD] beta[OF yD] f'_def
      using xn yn xy 
      by (simp add: dom_f v11_vimage_vpsubset_neq)
  qed

  define P' where "P' n' = (if n' \<le> n then P (f' n') else True)" for n'
  from n have "P' n"
  proof(induct rule: omega_induct)
    case 0 then show ?case 
      unfolding P'_def f'_def using assms(2) by auto
  next
    case (succ k) show ?case 
    proof(cases \<open>succ k \<le> n\<close>)
      case True
      then obtain x where xF: "vinsert x (f' k) = (f' (succ k))"
        by (simp add: f'_def succ_def vsubsetD dom_f vsv_vimage_vinsert)
      from True have "k \<le> n" by auto
      with \<open>P' k\<close> have "P (f' k)" unfolding P'_def by simp
      then have "f' k \<noteq> f' (succ k)"
        by (simp add: True f'_def \<open>k \<le> n\<close> dom_f v11_vimage_vpsubset_neq)
      with xF have "x \<notin>\<^sub>\<circ> f' k" by auto
      have "vfinite (f' k)" 
        by (simp add: \<open>k \<in>\<^sub>\<circ> \<omega>\<close> f'_def finite_Ord_omega vfinite_vimage)
      from assms(3)[OF \<open>vfinite (f' k)\<close> \<open>x \<notin>\<^sub>\<circ> f' k\<close> \<open>P (f' k)\<close>] show ?thesis 
        unfolding xF P'_def by simp
    qed (unfold P'_def, auto)
  qed  

  then show ?thesis unfolding P'_def F_def by simp

qed


text\<open>Set operations.\<close>

lemma vfinite_vempty[simp]: "vfinite (0\<^sub>\<nat>)" by simp

lemma vfinite_vsingleton[simp]: "vfinite (set {x})" by simp

lemma vfinite_vdoubleton[simp]: "vfinite (set {x, y})" by simp

lemma vfinite_vinsert:
  assumes "vfinite F"
  shows "vfinite (vinsert x F)"
  using assms by simp

lemma vfinite_vinsertD:
  assumes "vfinite (vinsert x F)"
  shows "vfinite F"
  using assms by simp

lemma vfinite_vsubset: 
  assumes "vfinite B" and "A \<subseteq>\<^sub>\<circ> B" 
  shows "vfinite A"
  using assms
  by (induct arbitrary: A rule: vfinite_induct)
    (simp_all add: less_eq_V_def finite_subset)

lemma vfinite_vunion: "vfinite (A \<union>\<^sub>\<circ> B) \<longleftrightarrow> vfinite A \<and> vfinite B" 
  by (auto simp: elts_sup_iff)

lemma vfinite_vunionI:
  assumes "vfinite A" and "vfinite B"
  shows "vfinite (A \<union>\<^sub>\<circ> B)"
  using assms by (simp add: elts_sup_iff)

lemma vfinite_vunionD:
  assumes "vfinite (A \<union>\<^sub>\<circ> B)" 
  shows "vfinite A" and "vfinite B"
  using assms by (auto simp: elts_sup_iff)

lemma vfinite_vintersectionI:
  assumes "vfinite A" and "vfinite B"
  shows "vfinite (A \<inter>\<^sub>\<circ> B)"
  using assms by (simp add: vfinite_vsubset)

lemma vfinite_VPowI: 
  assumes "vfinite A"
  shows "vfinite (VPow A)"
  using assms
proof(induct rule: vfinite_induct)
  case vempty then show ?case by simp
next
  case (vinsert x F)
  then show ?case 
    unfolding VPow_vinsert 
    using rel_VLambda.vfinite_vimage 
    by (intro vfinite_vunionI) metis+
qed


text\<open>Connections.\<close>

lemma vfinite_vcard_vfinite: "vfinite (vcard A) = vfinite A" 
  by (simp add: cardinal_eqpoll eqpoll_finite_iff)

lemma vfinite_vcard_omega_iff: "vfinite A \<longleftrightarrow> vcard A \<in>\<^sub>\<circ> \<omega>" 
   using vfinite_vcard_vfinite by auto

lemmas vcard_vfinite_omega = vfinite_vcard_omega_iff[THEN iffD2]
  and vfinite_vcard_omega = vfinite_vcard_omega_iff[THEN iffD1]

lemma vfinite_csucc[intro, simp]:
  assumes "vfinite A"
  shows "csucc (vcard A) = succ (vcard A)"
  using assms by (force simp: finite_csucc)

lemmas [intro, simp] = finite_csucc


text\<open>Previous connections.\<close>

lemma vcard_vsingleton[simp]: "vcard (set {a}) = 1\<^sub>\<nat>" by auto

lemma vfinite_vcard_vinsert_nin[simp]:
  assumes "vfinite A" and "a \<notin>\<^sub>\<circ> A"
  shows "vcard (vinsert a A) = csucc (vcard A)"
  using assms by (simp add: ZFC_in_HOL.vinsert_def)

text\<open>\newpage\<close>

end