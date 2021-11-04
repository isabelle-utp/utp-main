(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Finite sequences\<close>
theory CZH_Sets_FSequences
  imports CZH_Sets_Cardinality
begin



subsection\<open>Background\<close>


text\<open>
The section presents a theory of finite sequences internalized in the 
type \<^typ>\<open>V\<close>. The content of this subsection
was inspired by and draws on many ideas from the content
of the theory \<open>List\<close> in the main library of Isabelle/HOL.
\<close>



subsection\<open>Definition and common properties\<close>


text\<open>
A finite sequence is defined as a single-valued binary relation whose domain 
is an initial segment of the set of natural numbers.
\<close>

locale vfsequence = vsv xs for xs +
  assumes vfsequence_vdomain_in_omega: "\<D>\<^sub>\<circ> xs \<in>\<^sub>\<circ> \<omega>"

locale vfsequence_pair = r\<^sub>1: vfsequence xs\<^sub>1 + r\<^sub>2: vfsequence xs\<^sub>2 for xs\<^sub>1 xs\<^sub>2


text\<open>Rules.\<close>

lemmas [intro] = vfsequence.axioms(1)

lemma vfsequenceI[intro]:
  assumes "vsv xs" and "\<D>\<^sub>\<circ> xs \<in>\<^sub>\<circ> \<omega>"
  shows "vfsequence xs"
  using assms by (simp add: vfsequence.intro vfsequence_axioms_def)

lemma vfsequenceD[dest]:
  assumes "vfsequence xs"
  shows "\<D>\<^sub>\<circ> xs \<in>\<^sub>\<circ> \<omega>"
  using assms vfsequence.vfsequence_vdomain_in_omega by simp

lemma vfsequenceE[elim]:
  assumes "vfsequence xs" and "\<D>\<^sub>\<circ> xs \<in>\<^sub>\<circ> \<omega> \<Longrightarrow> P"
  shows P
  using assms by auto

lemma vfsequence_iff: "vfsequence xs \<longleftrightarrow> vsv xs \<and> \<D>\<^sub>\<circ> xs \<in>\<^sub>\<circ> \<omega>"
  using vfsequence_def by auto


text\<open>Elementary properties.\<close>

lemma (in vfsequence) vfsequence_vdomain: "\<D>\<^sub>\<circ> xs = vcard xs"
  unfolding vsv_vcard_vdomain[symmetric] using vfsequence_vdomain_in_omega by simp

lemma (in vfsequence) vfsequence_vcard_in_omega[simp]: "vcard xs \<in>\<^sub>\<circ> \<omega>"
  using vfsequence_vdomain_in_omega by (simp add: vfsequence_vdomain)


text\<open>Set operations.\<close>

lemma vfsequence_vempty[intro, simp]: "vfsequence 0" by (simp add: vfsequenceI)

lemma vfsequence_vsingleton[intro, simp]: "vfsequence (set {\<langle>0, a\<rangle>})"  
  using vone_in_omega 
  unfolding one_V_def 
  by (intro vfsequenceI) (auto simp: set_vzero_eq_ord_of_nat_vone)

lemma (in vfsequence) vfsequence_vinsert: 
  "vfsequence (vinsert \<langle>vcard xs, a\<rangle> xs)"
  using succ_def succ_in_omega by (auto simp: vfsequence_vdomain)


text\<open>Connections.\<close>

lemma (in vfsequence) vfsequence_vfinite[simp]: "vfinite xs"
  by (simp add: vfinite_vcard_omega_iff)

lemma (in vfsequence) vfsequence_vlrestriction[intro, simp]:
  assumes "k \<in>\<^sub>\<circ> \<omega>"
  shows "vfsequence (xs \<restriction>\<^sup>l\<^sub>\<circ> k)"
  using assms by (force simp: vfsequence_vdomain vdomain_vlrestriction)

lemma vfsequence_vproduct: 
  assumes "n \<in>\<^sub>\<circ> \<omega>" and "xs \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>n. A i)"
  shows "vfsequence xs"
  using assms by auto

lemma vfsequence_vcpower: 
  assumes "n \<in>\<^sub>\<circ> \<omega>" and "xs \<in>\<^sub>\<circ> A ^\<^sub>\<times> n"
  shows "vfsequence xs"
  using assms vfsequence_vproduct by auto


text\<open>Special properties.\<close>

lemma (in vfsequence) vfsequence_vdomain_vlrestriction[intro, simp]: 
  assumes "k \<in>\<^sub>\<circ> vcard xs"
  shows "\<D>\<^sub>\<circ> (xs \<restriction>\<^sup>l\<^sub>\<circ> k) = k"
  using assms
  by 
    (
      simp add: 
        OrdmemD 
        inf_absorb2   
        order.strict_implies_order 
        vdomain_vlrestriction 
        vfsequence_vdomain
    )

lemma (in vfsequence) vfsequence_vlrestriction_vcard[simp]: 
  "xs \<restriction>\<^sup>l\<^sub>\<circ> (vcard xs) = xs"
  by (rule vlrestriction_vdomain[unfolded vfsequence_vdomain])

lemma vfsequence_vfinite_vcardI:
  assumes "vsv xs" and "vfinite xs" and "\<D>\<^sub>\<circ> xs = vcard xs"
  shows "vfsequence xs"
  using assms by (intro vfsequenceI) (auto simp: vfinite_vcard_omega)

lemma (in vfsequence) vfsequence_vrangeE:
  assumes "a \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> xs" 
  obtains n where "n \<in>\<^sub>\<circ> vcard xs" and "xs\<lparr>n\<rparr> = a"
  using assms vfsequence_vdomain by auto

lemma (in vfsequence) vfsequence_vrange_vproduct:
  assumes "\<And>i. i \<in>\<^sub>\<circ> vcard xs \<Longrightarrow> xs\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i" 
  shows "xs \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>vcard xs. A i)"
  using vfsequence_vdomain vsv_axioms assms 
  by 
    (
      intro vproductI; 
      (intro vsv.vsv_vrange_vsubset_vifunion_app | tactic\<open>all_tac\<close>)
    ) auto

lemma (in vfsequence) vfsequence_vrange_vcpower:
  assumes "\<R>\<^sub>\<circ> xs \<subseteq>\<^sub>\<circ> A"
  shows "xs \<in>\<^sub>\<circ> A ^\<^sub>\<times> (vcard xs)"
  using assms
proof(elim vsubsetE; intro vcpowerI)
  assume hyp: "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> xs \<Longrightarrow> x \<in>\<^sub>\<circ> A" for x
  from vfsequence_vdomain show "xs \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>vcard xs. A)"
    by (intro vproductI) (blast intro: hyp elim: vdomain_atE)+
qed


text\<open>Alternative forms of existing results.\<close>

lemmas [intro, simp] = vfsequence.vfsequence_vcard_in_omega 
  and [intro, simp] = vfsequence.vfsequence_vfinite
  and [intro, simp] = vfsequence.vfsequence_vlrestriction
  and [intro, simp] = vfsequence.vfsequence_vdomain_vlrestriction
  and [intro, simp] = vfsequence.vfsequence_vlrestriction_vcard



subsection\<open>Appending an element to a finite sequence: \<open>vcons\<close>\<close>


subsubsection\<open>Definition and common properties\<close>

definition vcons :: "V \<Rightarrow> V \<Rightarrow> V"  (infixr \<open>#\<^sub>\<circ>\<close> 65) 
  where "xs #\<^sub>\<circ> x = vinsert \<langle>vcard xs, x\<rangle> xs"


text\<open>Syntax.\<close>

abbreviation vempty_vfsequence (\<open>[]\<^sub>\<circ>\<close>) where 
  "vempty_vfsequence \<equiv> 0::V"

notation vempty_vfsequence (\<open>[]\<^sub>\<circ>\<close>)

nonterminal fsfields
nonterminal vlist

syntax
  "" :: "V \<Rightarrow> fsfields" ("_")
  "_fsfields" :: "fsfields \<Rightarrow> V \<Rightarrow> fsfields" ("_,/ _")
  "_vlist" :: "fsfields \<Rightarrow> V" ("[(_)]\<^sub>\<circ>")
  "_vapp" :: "V \<Rightarrow> fsfields \<Rightarrow> V" ("_ \<lparr>(_)\<rparr>\<^sub>\<bullet>" [100, 100] 100)

translations
  "[xs, x]\<^sub>\<circ>" == "[xs]\<^sub>\<circ> #\<^sub>\<circ> x"
  "[x]\<^sub>\<circ>" == "[]\<^sub>\<circ> #\<^sub>\<circ> x"

translations
  "f\<lparr>xs, x\<rparr>\<^sub>\<bullet>" == "f\<lparr>[xs, x]\<^sub>\<circ>\<rparr>"
  "f\<lparr>x\<rparr>\<^sub>\<bullet>" == "f\<lparr>[x]\<^sub>\<circ>\<rparr>"


text\<open>Rules.\<close>

lemma vconsI[intro!]: 
  assumes "a \<in>\<^sub>\<circ> vinsert \<langle>vcard xs, x\<rangle> xs"
  shows "a \<in>\<^sub>\<circ> xs #\<^sub>\<circ> x"
  using assms unfolding vcons_def by clarsimp

lemma vconsD[dest!]:
  assumes "a \<in>\<^sub>\<circ> xs #\<^sub>\<circ> x"
  shows "a \<in>\<^sub>\<circ> vinsert \<langle>vcard xs, x\<rangle> xs"
  using assms unfolding vcons_def by clarsimp

lemma vconsE[elim!]:
  assumes "a \<in>\<^sub>\<circ> xs #\<^sub>\<circ> x"
  obtains a where "a \<in>\<^sub>\<circ> vinsert \<langle>vcard xs, x\<rangle> xs"
  using assms unfolding vcons_def by clarsimp


text\<open>Elementary properties.\<close>

lemma vcons_neq_vempty[simp]: "ys #\<^sub>\<circ> y \<noteq> []\<^sub>\<circ>" by auto


text\<open>Set operations.\<close>

lemma vcons_vsingleton: "[a]\<^sub>\<circ> = set {\<langle>0\<^sub>\<nat>, a\<rangle>}" unfolding vcons_def by simp

lemma vcons_vdoubleton: "[a, b]\<^sub>\<circ> = set {\<langle>0\<^sub>\<nat>, a\<rangle>, \<langle>1\<^sub>\<nat>, b\<rangle>}" 
  unfolding vcons_def 
  using vinsert_vsingleton 
  by (force simp: vinsert_set_insert_eq)

lemma vcons_vsubset: "xs \<subseteq>\<^sub>\<circ> xs #\<^sub>\<circ> x" by clarsimp

lemma vcons_vsubset':
  assumes "vcons xs x \<subseteq>\<^sub>\<circ> ys"
  shows "vcons xs x \<subseteq>\<^sub>\<circ> vcons ys y"
  using assms unfolding vcons_def by auto


text\<open>Connections.\<close>

lemma (in vfsequence) vfsequence_vcons[intro, simp]: "vfsequence (xs #\<^sub>\<circ> x)"
proof(intro vfsequenceI)
  from vfsequence_vdomain_in_omega vsv_vcard_vdomain have "vcard xs = \<D>\<^sub>\<circ> xs" 
    by (simp add: vcard_veqpoll)
  show "vsv (xs #\<^sub>\<circ> x)" 
  proof(intro vsvI)
    fix a b c assume ab: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> xs #\<^sub>\<circ> x" and ac: "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> xs #\<^sub>\<circ> x" 
    then consider (dom) "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> xs" | (ndom) "a = vcard xs"
      unfolding vcons_def by auto
    then show "b = c"
    proof cases
      case dom
      with ab have "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> xs" 
        unfolding vcons_def by (auto simp: \<open>vcard xs = \<D>\<^sub>\<circ> xs\<close>)
      moreover from dom ac have "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> xs" 
        unfolding vcons_def by (auto simp: \<open>vcard xs = \<D>\<^sub>\<circ> xs\<close>)
      ultimately show ?thesis using vsv by simp
    next
      case ndom
      from ab have "\<langle>a, b\<rangle> = \<langle>vcard xs, x\<rangle>" 
        unfolding ndom vcons_def using \<open>vcard xs = \<D>\<^sub>\<circ> xs\<close> mem_not_refl by blast
      moreover from ac have "\<langle>a, c\<rangle> = \<langle>vcard xs, x\<rangle>" 
        unfolding ndom vcons_def using \<open>vcard xs = \<D>\<^sub>\<circ> xs\<close> mem_not_refl by blast
      ultimately show ?thesis by simp
    qed
  next
    show "vbrelation (xs #\<^sub>\<circ> x)" unfolding vcons_def
      using vbrelation_vinsertI by auto
  qed                     
  show "\<D>\<^sub>\<circ> (xs #\<^sub>\<circ> x) \<in>\<^sub>\<circ> \<omega>"
    unfolding vcons_def 
    using succ_in_omega  
    by (auto simp: vfsequence_vdomain_in_omega succ_def \<open>vcard xs = \<D>\<^sub>\<circ> xs\<close>)
qed

lemma (in vfsequence) vfsequence_vcons_vdomain[simp]: 
  "\<D>\<^sub>\<circ> (xs #\<^sub>\<circ> x) = succ (vcard xs)"
  by (simp add: succ_def vcons_def vfsequence_vdomain)

lemma (in vfsequence) vfsequence_vcons_vrange[simp]: 
  "\<R>\<^sub>\<circ> (xs #\<^sub>\<circ> x) = vinsert x (\<R>\<^sub>\<circ> xs)"
  by (simp add: vcons_def)

lemma (in vfsequence) vfsequence_vrange_vconsI:
  assumes "\<R>\<^sub>\<circ> xs \<subseteq>\<^sub>\<circ> X" and "x \<in>\<^sub>\<circ> X"
  shows "\<R>\<^sub>\<circ> (xs #\<^sub>\<circ> x) \<subseteq>\<^sub>\<circ> X"
  using assms unfolding vcons_def by auto

lemmas vfsequence_vrange_vconsI = vfsequence.vfsequence_vrange_vconsI[rotated 1]


text\<open>Special properties.\<close>

lemma vcons_vrange_mono:
  assumes "xs \<subseteq>\<^sub>\<circ> ys"
  shows "\<R>\<^sub>\<circ> (xs #\<^sub>\<circ> x) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (ys #\<^sub>\<circ> x)"
  using assms 
  unfolding vcons_def 
  by (simp add: vrange_mono vsubset_vinsert_leftI vsubset_vinsert_rightI)

lemma (in vfsequence) vfsequence_vlrestriction_succ:
  assumes [simp]: "k \<in>\<^sub>\<circ> vcard xs"
  shows "xs \<restriction>\<^sup>l\<^sub>\<circ> succ k = xs \<restriction>\<^sup>l\<^sub>\<circ> k #\<^sub>\<circ> (xs\<lparr>k\<rparr>)"
proof-
  interpret vlr: vfsequence \<open>xs \<restriction>\<^sup>l\<^sub>\<circ> k\<close>
    using assms by (blast intro: vfsequence_vcard_in_omega Ord_trans)
  from vlr.vfsequence_vdomain[symmetric, simplified] show ?thesis 
    by 
      (
        simp add: 
          vcons_def succ_def vfsequence_vdomain vsv_vlrestriction_vinsert
      )
qed

lemma (in vfsequence) vfsequence_vremove_vcons_vfsequence: 
  assumes "xs = xs' #\<^sub>\<circ> x"
  shows "vfsequence xs'"
proof(cases\<open>\<langle>vcard xs', x\<rangle> \<in>\<^sub>\<circ> xs'\<close>)
  case True
  with assms[unfolded vcons_def] have "xs = xs'" by auto
  then show ?thesis using vfsequence_axioms by simp
next
  case False
  note x_def[simp] = assms[unfolded vcons_def]
  interpret xs': vsv xs' using vsv_axioms by (auto intro: vsv_vinsertD)
  have fin: "vfinite xs'" using vfsequence_vfinite by auto
  have vcard_xs: "vcard xs = succ (vcard xs')" by (simp add: fin False)
  have [simp]: "vcard xs' \<notin>\<^sub>\<circ> \<D>\<^sub>\<circ> xs'" using False vsv_axioms by auto
  have "vcard xs' \<in>\<^sub>\<circ> \<omega>" using fin vfinite_vcard_omega by auto
  have xs'_def: "xs' = xs \<restriction>\<^sup>l\<^sub>\<circ> (vcard xs')" 
    using vcard_xs fin vfsequence_vdomain 
    by (auto simp: vinsert_ident succ_def)
  from vfsequence_vlrestriction[OF \<open>vcard xs' \<in>\<^sub>\<circ> \<omega>\<close>] show ?thesis 
    unfolding xs'_def[symmetric] .
qed

lemma (in vfsequence) vfsequence_vcons_ex: 
  assumes "xs \<noteq> []\<^sub>\<circ>" 
  obtains xs' x where "xs = xs' #\<^sub>\<circ> x" and "vfsequence xs'"
proof-
  from vcard_vempty have "0 \<in>\<^sub>\<circ> vcard xs" by (simp add: assms mem_0_Ord)
  then obtain k where succk: "succ k = vcard xs"
    by (metis omega_prev vfsequence_vcard_in_omega) 
  then have "k \<in>\<^sub>\<circ> vcard xs" using elts_succ by blast
  from vfsequence_vlrestriction_succ[OF this, unfolded succk] show ?thesis
    by (simp add: vfsequence_vremove_vcons_vfsequence that)
qed


subsubsection\<open>Induction and case analysis\<close>

lemma vfsequence_induct[consumes 1, case_names 0 vcons]:
  assumes "vfsequence xs"
    and "P []\<^sub>\<circ>"
    and "\<And>xs x. \<lbrakk>vfsequence xs; P xs\<rbrakk> \<Longrightarrow> P (xs #\<^sub>\<circ> x)"
  shows "P xs"
proof-
  interpret vfsequence xs by (rule assms(1))
  from assms(1) obtain n where "n \<in>\<^sub>\<circ> \<omega>" and "\<D>\<^sub>\<circ> xs = n" by auto
  then have "n \<le> \<D>\<^sub>\<circ> xs" by auto
  define P' where "P' k = P (xs \<restriction>\<^sup>l\<^sub>\<circ> k)" for k
  from \<open>n \<in>\<^sub>\<circ> \<omega>\<close> and \<open>n \<le> \<D>\<^sub>\<circ> xs\<close> have "P' n"
  proof(induction rule: omega_induct)
    case (succ n') then show ?case
    proof-
      interpret vlr: vfsequence \<open>xs \<restriction>\<^sup>l\<^sub>\<circ> n'\<close> by (simp add: succ.hyps)
      have "P' n'" using succ.prems by (force intro: succ.IH)
      then have "P (xs \<restriction>\<^sup>l\<^sub>\<circ> n')" unfolding P'_def by assumption
      have "n' \<in>\<^sub>\<circ> vcard xs" 
        using succ.prems by (auto simp: vsubset_iff vfsequence_vdomain)
      from vfsequence_vlrestriction_succ[OF \<open>n' \<in>\<^sub>\<circ> vcard xs\<close>]
      show "P' (succ n')"
        by (simp add: P'_def \<open>P (xs \<restriction>\<^sup>l\<^sub>\<circ> n')\<close> assms(3) vlr.vfsequence_axioms)
    qed
  qed (simp add: P'_def assms(2))
  then show ?thesis unfolding P'_def \<open>\<D>\<^sub>\<circ> xs = n\<close>[symmetric] by simp
qed

lemma vfsequence_cases[consumes 1, case_names 0 vcons]: 
  assumes "vfsequence xs"
    and "xs = []\<^sub>\<circ> \<Longrightarrow> P"
    and "\<And>xs' x. \<lbrakk>xs = xs' #\<^sub>\<circ> x; vfsequence xs'\<rbrakk> \<Longrightarrow> P"
  shows P
proof-
  interpret vfsequence xs by (rule assms(1))
  show ?thesis
  proof(cases \<open>xs = 0\<close>)
    case False
    then obtain xs' x where "xs = xs' #\<^sub>\<circ> x"
      by (blast intro: vfsequence_vcons_ex)
    then show ?thesis by (auto simp: assms(3) intro: vfsequence_vcons_ex)
  qed (use assms(2) in auto)
qed


subsubsection\<open>Evaluation\<close>

lemma (in vfsequence) vfsequence_vcard_vcons[simp]: 
  "vcard (xs #\<^sub>\<circ> x) = succ (vcard xs)"
proof-
  interpret xsx: vfsequence \<open>xs #\<^sub>\<circ> x\<close> by simp
  have "vcard (xs #\<^sub>\<circ> x) = \<D>\<^sub>\<circ> (xs #\<^sub>\<circ> x)" 
    by (rule xsx.vfsequence_vdomain[symmetric])
  then show ?thesis
    by (subst vcons_def) (simp add: succ_def vcons_def vfsequence_vdomain)
qed

lemma (in vfsequence) vfsequence_at_last[intro, simp]:
  assumes "i = vcard xs"
  shows "(xs #\<^sub>\<circ> x)\<lparr>i\<rparr> = x"
  by (simp add: vfsequence_vdomain vcons_def assms)

lemma (in vfsequence) vfsequence_at_not_last[intro, simp]:
  assumes "i \<in>\<^sub>\<circ> vcard xs"
  shows "(xs #\<^sub>\<circ> x)\<lparr>i\<rparr> = xs\<lparr>i\<rparr>"
proof-
  from assms have [simp]: "\<D>\<^sub>\<circ> xs = vcard xs" by (auto simp: vfsequence_vdomain)
  from assms have "i \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> xs" by simp
  moreover have "i \<noteq> vcard xs" using assms mem_not_refl by blast
  ultimately show ?thesis
    unfolding vcons_def using vsv.vsv_vinsert vsvE vsv_axioms by auto 
qed


text\<open>Alternative forms of existing results.\<close>

lemmas [intro, simp] = vfsequence.vfsequence_vcons
  and [intro, simp] = vfsequence.vfsequence_vcard_vcons
  and [intro, simp] = vfsequence.vfsequence_at_last
  and [intro, simp] = vfsequence.vfsequence_at_not_last
  and [intro, simp] = vfsequence.vfsequence_vcons_vdomain
  and [intro, simp] = vfsequence.vfsequence_vcons_vrange



subsubsection\<open>Congruence-like properties\<close>

context vfsequence_pair
begin

lemma vcons_eq_vcard_eq:
  assumes "xs\<^sub>1 #\<^sub>\<circ> x\<^sub>1 = xs\<^sub>2 #\<^sub>\<circ> x\<^sub>2"
  shows "vcard xs\<^sub>1 = vcard xs\<^sub>2"
  by 
    (
      metis 
        assms 
        succ_inject_iff   
        vfsequence.vfsequence_vcons_vdomain
        r\<^sub>1.vfsequence_axioms 
        r\<^sub>2.vfsequence_axioms
    )

lemma vcons_eqD[dest]:
  assumes "xs\<^sub>1 #\<^sub>\<circ> x\<^sub>1 = xs\<^sub>2 #\<^sub>\<circ> x\<^sub>2"
  shows "xs\<^sub>1 = xs\<^sub>2" and "x\<^sub>1 = x\<^sub>2"
proof-

  have xsx1_last: "(xs\<^sub>1 #\<^sub>\<circ> x\<^sub>1)\<lparr>vcard xs\<^sub>1\<rparr> = x\<^sub>1" by simp
  have xsx2_last: "(xs\<^sub>2 #\<^sub>\<circ> x\<^sub>2)\<lparr>vcard xs\<^sub>2\<rparr> = x\<^sub>2" by simp

  from assms have vcard: "vcard xs\<^sub>1 = vcard xs\<^sub>2" by (rule vcons_eq_vcard_eq)
  from trans[OF xsx1_last xsx1_last[unfolded vcard assms, symmetric]]
  
  show "x\<^sub>1 = x\<^sub>2" unfolding xsx1_last xsx2_last .

  have nxs1: "\<langle>vcard xs\<^sub>1, x\<^sub>1\<rangle> \<notin>\<^sub>\<circ> xs\<^sub>1" 
    using mem_not_refl r\<^sub>1.vfsequence_vdomain by blast
  have nxs2: "\<langle>vcard xs\<^sub>2, x\<^sub>2\<rangle> \<notin>\<^sub>\<circ> xs\<^sub>2" 
    using mem_not_refl r\<^sub>2.vfsequence_vdomain by blast
  have xsx1_xsx2: "\<langle>vcard xs\<^sub>1, x\<^sub>1\<rangle> = \<langle>vcard xs\<^sub>2, x\<^sub>2\<rangle>" 
    unfolding vcons_eq_vcard_eq[OF assms(1)] \<open>x\<^sub>1 = x\<^sub>2\<close> by simp
  
  show "xs\<^sub>1 = xs\<^sub>2"
  proof(rule vinsert_identD[OF _ nxs1])
    from assms(1)[unfolded vcons_def] show 
      "vinsert \<langle>vcard xs\<^sub>1, x\<^sub>1\<rangle> xs\<^sub>1 = vinsert \<langle>vcard xs\<^sub>1, x\<^sub>1\<rangle> xs\<^sub>2"
      by (auto simp: xsx1_xsx2)
    show "\<langle>vcard xs\<^sub>1, x\<^sub>1\<rangle> \<notin>\<^sub>\<circ> xs\<^sub>2"
      by (rule nxs2[folded \<open>x\<^sub>1 = x\<^sub>2\<close> vcons_eq_vcard_eq[OF assms(1)]])
  qed

qed

lemma vcons_eqI:
  assumes "xs\<^sub>1 = xs\<^sub>2" and "x\<^sub>1 = x\<^sub>2"
  shows "xs\<^sub>1 #\<^sub>\<circ> x\<^sub>1 = xs\<^sub>2 #\<^sub>\<circ> x\<^sub>2"
  using assms by (rule arg_cong2)

lemma vcons_eq_iff[simp]: "(xs\<^sub>1 #\<^sub>\<circ> x\<^sub>1 = xs\<^sub>2 #\<^sub>\<circ> x\<^sub>2) \<longleftrightarrow> (xs\<^sub>1 = xs\<^sub>2 \<and> x\<^sub>1 = x\<^sub>2)" 
  by auto

end


text\<open>Alternative forms of existing results.\<close>

context
  fixes xs\<^sub>1 xs\<^sub>2
  assumes xs\<^sub>1: "vfsequence xs\<^sub>1"
    and xs\<^sub>2: "vfsequence xs\<^sub>2"
begin

lemmas_with[OF vfsequence_pair.intro[OF xs\<^sub>1 xs\<^sub>2]]:
  vcons_eqD' = vfsequence_pair.vcons_eqD
  and vcons_eq_iff[intro, simp] = vfsequence_pair.vcons_eq_iff

end

lemmas vcons_eqD[dest] = vcons_eqD'[rotated -1]



subsection\<open>Transfer between the type \<^typ>\<open>V list\<close> and finite sequences\<close>


subsubsection\<open>Initialization\<close>

primrec vfsequence_of_vlist :: "V list \<Rightarrow> V"
  where 
    "vfsequence_of_vlist [] = 0"
  | "vfsequence_of_vlist (x # xs) = vfsequence_of_vlist xs #\<^sub>\<circ> x"

definition vlist_of_vfsequence :: "V \<Rightarrow> V list"
  where "vlist_of_vfsequence = inv_into UNIV vfsequence_of_vlist"

lemma vfsequence_vfsequence_of_vlist: "vfsequence (vfsequence_of_vlist xs)"
  by (induction xs) auto

lemma inj_vfsequence_of_vlist: "inj vfsequence_of_vlist"
proof
  show "vfsequence_of_vlist x = vfsequence_of_vlist y \<Longrightarrow> x = y" 
    for x y
  proof(induction y arbitrary: x)
    case Nil then show ?case by (cases x) auto
  next
    case (Cons a ys)
    note Cons' = Cons
    show ?case 
    proof(cases x)
      case Nil with Cons show ?thesis by auto
    next
      case (Cons b zs)
      from Cons'[unfolded Cons vfsequence_of_vlist.simps] have 
        "vfsequence_of_vlist zs #\<^sub>\<circ> b = vfsequence_of_vlist ys #\<^sub>\<circ> a"
        by simp
      then have "vfsequence_of_vlist zs = vfsequence_of_vlist ys" and "b = a"
        by (auto simp: vfsequence_vfsequence_of_vlist)
      from Cons'(1)[OF this(1)] this(2) show ?thesis unfolding Cons by auto
    qed
  qed
qed

lemma range_vfsequence_of_vlist: 
  "range vfsequence_of_vlist = {xs. vfsequence xs}"
proof(intro subset_antisym subsetI; unfold mem_Collect_eq)
  show "xs \<in> range vfsequence_of_vlist \<Longrightarrow> vfsequence xs" for xs
    by (clarsimp simp: vfsequence_vfsequence_of_vlist)
  fix xs assume "vfsequence xs"
  then show "xs \<in> range vfsequence_of_vlist"
  proof(induction rule: vfsequence_induct)
    case 0 then show ?case 
      by (metis image_iff iso_tuple_UNIV_I vfsequence_of_vlist.simps(1))
  next
    case (vcons xs x) then show ?case 
      by (metis rangeE rangeI vfsequence_of_vlist.simps(2))
  qed 
qed

lemma vlist_of_vfsequence_vfsequence_of_vlist[simp]: 
  "vlist_of_vfsequence (vfsequence_of_vlist xs) = xs"
  by (simp add: inj_vfsequence_of_vlist vlist_of_vfsequence_def)

lemma (in vfsequence) vfsequence_of_vlist_vlist_of_vfsequence[simp]: 
  "vfsequence_of_vlist (vlist_of_vfsequence xs) = xs"
  using vfsequence_axioms range_vfsequence_of_vlist inj_vfsequence_of_vlist
  by (simp add: f_inv_into_f vlist_of_vfsequence_def)

lemmas vfsequence_of_vlist_vlist_of_vfsequence[intro, simp] =
  vfsequence.vfsequence_of_vlist_vlist_of_vfsequence

lemma vlist_of_vfsequence_vempty[simp]: "vlist_of_vfsequence []\<^sub>\<circ> = []"
  by 
    (
      metis 
        vfsequence_of_vlist.simps(1) 
        vlist_of_vfsequence_vfsequence_of_vlist
    )


text\<open>Transfer relation 1.\<close>

definition cr_vfsequence :: "V \<Rightarrow> V list \<Rightarrow> bool"
  where "cr_vfsequence a b \<longleftrightarrow> (a = vfsequence_of_vlist b)"

lemma cr_vfsequence_right_total[transfer_rule]: "right_total cr_vfsequence"
  unfolding cr_vfsequence_def right_total_def by simp

lemma cr_vfsequence_bi_unqie[transfer_rule]: "bi_unique cr_vfsequence"
  unfolding cr_vfsequence_def bi_unique_def
  by (simp add: inj_eq inj_vfsequence_of_vlist)

lemma cr_vfsequence_transfer_domain_rule[transfer_domain_rule]: 
  "Domainp cr_vfsequence = (\<lambda>xs. vfsequence xs)"
  unfolding cr_vfsequence_def
proof(intro HOL.ext, rule iffI)
  fix xs assume prems: "vfsequence xs"
  interpret vfsequence xs by (rule prems)
  have "\<exists>ys. xs = vfsequence_of_vlist ys"
    using prems
  proof(induction rule: vfsequence_induct)
    show "\<lbrakk> vfsequence xs; \<exists>ys. xs = vfsequence_of_vlist ys \<rbrakk> \<Longrightarrow>
      \<exists>ys. xs #\<^sub>\<circ> x = vfsequence_of_vlist ys"
      for xs x
      unfolding vfsequence_of_vlist_def by (metis list.simps(7))
  qed auto 
  then show "Domainp (\<lambda>a b. a = vfsequence_of_vlist b) xs" by auto
qed (clarsimp simp: vfsequence_vfsequence_of_vlist)

lemma cr_vfsequence_vconsD:
  assumes "cr_vfsequence (xs #\<^sub>\<circ> x) (y # ys)" 
  shows "cr_vfsequence xs ys" and "x = y"
proof-
  from assms[unfolded cr_vfsequence_def] have xs_x_def: 
    "xs #\<^sub>\<circ> x = vfsequence_of_vlist (y # ys)" .
  then have xs_x: "vfsequence (xs #\<^sub>\<circ> x)" 
    by (simp add: vfsequence_vfsequence_of_vlist)
  interpret vfsequence xs
    by (blast intro: vfsequence.vfsequence_vremove_vcons_vfsequence xs_x)
  from 
    assms[unfolded cr_vfsequence_def vfsequence_of_vlist.simps(2)]
    vfsequence_axioms 
  show "cr_vfsequence xs ys" and "x = y"
    unfolding cr_vfsequence_def by (auto simp: vfsequence_vfsequence_of_vlist)
qed


text\<open>Transfer relation 2.\<close>

definition cr_cr_vfsequence :: "V \<Rightarrow> V list list \<Rightarrow> bool"
  where "cr_cr_vfsequence a b \<longleftrightarrow> 
    (a = vfsequence_of_vlist (map vfsequence_of_vlist b))"

lemma cr_cr_vfsequence_right_total[transfer_rule]: 
  "right_total cr_cr_vfsequence"
  unfolding cr_cr_vfsequence_def right_total_def by simp

lemma cr_cr_vfsequence_bi_unqie[transfer_rule]: "bi_unique cr_cr_vfsequence"
  unfolding cr_cr_vfsequence_def bi_unique_def
  by (simp add: inj_eq inj_vfsequence_of_vlist)


text\<open>Transfer relation for scalars.\<close>

definition cr_scalar :: "(V \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> V \<Rightarrow> 'a \<Rightarrow> bool"
  where "cr_scalar R x y = (\<exists>a. x = [a]\<^sub>\<circ> \<and> R a y)"

lemma cr_scalar_bi_unique[transfer_rule]:
  assumes "bi_unique R"
  shows "bi_unique (cr_scalar R)"
  using assms unfolding cr_scalar_def bi_unique_def by auto

lemma cr_scalar_right_total[transfer_rule]:
  assumes "right_total R"
  shows "right_total (cr_scalar R)"
  using assms unfolding cr_scalar_def right_total_def by simp

lemma cr_scalar_transfer_domain_rule[transfer_domain_rule]: 
  "Domainp (cr_scalar R) = (\<lambda>x. \<exists>a. x = [a]\<^sub>\<circ> \<and> Domainp R a)"
  unfolding cr_scalar_def by auto


subsubsection\<open>Transfer rules for previously defined entities\<close>

context 
  includes lifting_syntax
begin

lemma vfsequence_vempty_transfer[transfer_rule]: "cr_vfsequence []\<^sub>\<circ> []"
  unfolding cr_vfsequence_def by simp

lemma vfsequence_vempty_ll_transfer[transfer_rule]: 
  "cr_cr_vfsequence [[]\<^sub>\<circ>]\<^sub>\<circ> [[]]"
  unfolding cr_cr_vfsequence_def by simp

lemma vcons_transfer[transfer_rule]:
  "((=) ===> cr_vfsequence ===> cr_vfsequence) (\<lambda>x xs. xs #\<^sub>\<circ> x) (\<lambda>x xs. x # xs)"
  by (intro rel_funI) (simp add: cr_vfsequence_def)

lemma vcons_ll_transfer[transfer_rule]:
  "(cr_vfsequence ===> cr_cr_vfsequence ===> cr_cr_vfsequence) 
    (\<lambda>x xs. xs #\<^sub>\<circ> x) (\<lambda>x xs. x # xs)"
  by (intro rel_funI) (simp add: cr_vfsequence_def cr_cr_vfsequence_def)

lemma vfsequence_vrange_transfer[transfer_rule]:
  "(cr_vfsequence ===> (=)) (\<lambda>xs. elts (\<R>\<^sub>\<circ> xs)) list.set"
proof(intro rel_funI)
  fix xs ys assume prems: "cr_vfsequence xs ys"
  then have "xs = vfsequence_of_vlist ys" unfolding cr_vfsequence_def by simp
  then have "vfsequence xs" by (simp add: vfsequence_vfsequence_of_vlist)
  from this prems show "elts (\<R>\<^sub>\<circ> xs) = list.set ys"
  proof(induction ys arbitrary: xs)
    case (Cons a ys)
    from Cons(2) show ?case 
    proof(cases xs rule: vfsequence_cases)
      case 0 with Cons show ?thesis by (simp add: Cons.IH cr_vfsequence_def)
    next
      case (vcons xs' x)
      interpret vfsequence xs' by (rule vcons(2))
      note vcons_transfer = cr_vfsequence_vconsD[OF Cons(3)[unfolded vcons(1)]]
      have a_ys: "list.set (a # ys) = insert a (list.set ys)" by simp
      from vcons(2) have R_xs'x: "\<R>\<^sub>\<circ> (xs' #\<^sub>\<circ> x) = vinsert x (\<R>\<^sub>\<circ> xs')" by simp
      show "elts (\<R>\<^sub>\<circ> xs) = (list.set (a # ys))"
        unfolding vcons(1) R_xs'x a_ys
        by 
          (
            auto simp: 
              vcons_transfer(2) Cons(1)[OF vfsequence_axioms vcons_transfer(1)]
          )
    qed
  qed (auto simp: cr_vfsequence_def)
qed

lemma vcard_transfer[transfer_rule]: 
  "(cr_vfsequence ===> cr_omega) vcard length"
proof(intro rel_funI)
  fix xs ys assume prems: "cr_vfsequence xs ys"
  then have "xs = vfsequence_of_vlist ys" unfolding cr_vfsequence_def by simp
  then have "vfsequence xs" by (simp add: vfsequence_vfsequence_of_vlist)
  from this prems show "cr_omega (vcard xs) (length ys)"
  proof(induction ys arbitrary: xs)
    case (Cons y ys)
    from Cons(2) show ?case 
    proof(cases xs rule: vfsequence_cases)
      case 0 with Cons show ?thesis by (simp add: Cons.IH cr_vfsequence_def)
    next
      case (vcons xs' x)
      interpret vfsequence xs' by (rule vcons(2))
      note vcons_transfer = cr_vfsequence_vconsD[OF Cons(3)[unfolded vcons(1)]]
      have vcard_xs_x: "vcard (xs' #\<^sub>\<circ> x) = succ (vcard xs')" by simp
      have vcard_y_ys: "length (y # ys) = Suc (length ys)" by simp
      from vfsequence_axioms have [transfer_rule]: 
        "cr_omega (vcard xs') (length ys)"
        by (simp add: vcons_transfer(1) Cons.IH)
      show ?thesis unfolding vcons(1) vcard_xs_x vcard_y_ys by transfer_prover
    qed
  qed (auto simp: cr_omega_def cr_vfsequence_def)
qed

lemma vcard_ll_transfer[transfer_rule]: 
  "(cr_cr_vfsequence ===> cr_omega) vcard length"
  unfolding cr_cr_vfsequence_def
  by (intro rel_funI)
    (metis cr_vfsequence_def length_map rel_funD vcard_transfer)

end


text\<open>Corollaries.\<close>

lemma vrange_vfsequence_of_vlist: 
  "\<R>\<^sub>\<circ> (vfsequence_of_vlist xs) = set (list.set xs)"
proof(intro vsubset_antisym vsubsetI)
  fix x assume prems: "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (vfsequence_of_vlist xs)" 
  define ys where "ys = vfsequence_of_vlist xs"
  have [transfer_rule]: "cr_vfsequence ys xs" "x = x" 
    unfolding ys_def cr_vfsequence_def by simp_all
  show "x \<in>\<^sub>\<circ> set (list.set xs)" by transfer (simp add: prems[folded ys_def])
next
  fix x assume prems: "x \<in>\<^sub>\<circ> set (list.set xs)"
  define ys where "ys = vfsequence_of_vlist xs"
  have [transfer_rule]: "cr_vfsequence ys xs" "x = x" 
    unfolding ys_def cr_vfsequence_def by simp_all
  from prems[untransferred] show "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (vfsequence_of_vlist xs)"
    unfolding ys_def by simp
qed

lemma cr_cr_vfsequence_transfer_domain_rule[transfer_domain_rule]: 
  "Domainp cr_cr_vfsequence = 
    (\<lambda>xss. vfsequence xss \<and> (\<forall>xs\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> xss. vfsequence xs))"
proof(intro HOL.ext, rule iffI; (elim conjE | intro conjI ballI))
  fix xss assume prems: "Domainp cr_cr_vfsequence xss"
  with vfsequence_vfsequence_of_vlist show xss: "vfsequence xss"
    unfolding cr_cr_vfsequence_def by clarsimp
  interpret vfsequence xss by (rule xss)
  fix xs assume prems': "xs \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> xss"
  from prems obtain yss where xss_def: 
    "xss = vfsequence_of_vlist (map vfsequence_of_vlist yss)"
    unfolding cr_cr_vfsequence_def by clarsimp
  from prems' have "xs \<in>\<^sub>\<circ> set (list.set (map vfsequence_of_vlist yss))"
    unfolding xss_def vrange_vfsequence_of_vlist by simp
  then obtain ys where xs_def: "xs = vfsequence_of_vlist ys" by clarsimp
  show "vfsequence xs"
    unfolding xs_def by (simp add: vfsequence_vfsequence_of_vlist)
next
  fix xss assume prems: "vfsequence xss" "\<forall>xs\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> xss. vfsequence xs"
  have "\<exists>yss. xss = vfsequence_of_vlist (map vfsequence_of_vlist yss)"
    using prems
  proof(induction rule: vfsequence_induct)
    case (vcons xss x)
    let ?y = \<open>vlist_of_vfsequence x\<close>
    from vcons(2,3) obtain yss where xss_def: 
      "xss = vfsequence_of_vlist (map vfsequence_of_vlist yss)"
      by auto
    from vcons(3) have "vfsequence x" by auto
    then have x_def: "x = vfsequence_of_vlist (vlist_of_vfsequence x)" by simp
    then have 
      "xss #\<^sub>\<circ> x = vfsequence_of_vlist (map vfsequence_of_vlist (?y # yss))"
      unfolding xss_def by simp
    then show ?case by blast
  qed (auto intro: exI[of _ \<open>[]\<close>])
  then show "Domainp cr_cr_vfsequence xss" 
    unfolding cr_cr_vfsequence_def by blast
qed


subsubsection\<open>Appending elements\<close>

definition vappend :: "V \<Rightarrow> V \<Rightarrow> V" (infixr "@\<^sub>\<circ>" 65)
  where "xs @\<^sub>\<circ> ys =
    vfsequence_of_vlist (vlist_of_vfsequence ys @ vlist_of_vfsequence xs)"


text\<open>Transfer.\<close>

lemma vappend_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vfsequence ===> cr_vfsequence ===> cr_vfsequence) 
    (\<lambda>xs ys. vappend ys xs) append"
  by (intro rel_funI, unfold cr_vfsequence_def) (simp add: vappend_def)

lemma vappend_ll_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_cr_vfsequence ===> cr_cr_vfsequence ===> cr_cr_vfsequence) 
    (\<lambda>xs ys. vappend ys xs) append"
  by (intro rel_funI, unfold cr_cr_vfsequence_def) (simp add: vappend_def)


text\<open>Elementary properties.\<close>

lemma (in vfsequence) vfsequence_vappend_vempty_vfsequence[simp]: 
  "[]\<^sub>\<circ> @\<^sub>\<circ> xs = xs"
  unfolding vappend_def by auto

lemmas vfsequence_vappend_vempty_vfsequence[simp] =
  vfsequence.vfsequence_vappend_vempty_vfsequence

lemma (in vfsequence) vfsequence_vappend_vfsequence_vempty[simp]:
  "xs @\<^sub>\<circ> []\<^sub>\<circ> = xs"
  unfolding vappend_def by auto

lemmas vfsequence_vappend_vfsequence_vempty[simp] =
  vfsequence.vfsequence_vappend_vfsequence_vempty

lemma vappend_vcons[simp]: 
  assumes "vfsequence xs" and "vfsequence ys"
  shows "xs @\<^sub>\<circ> (ys #\<^sub>\<circ> y) = (xs @\<^sub>\<circ> ys) #\<^sub>\<circ> y"
  using append_Cons[where 'a=V, untransferred, OF assms(2,1)] by simp


subsubsection\<open>Distinct elements\<close>

definition vdistinct :: "V \<Rightarrow> bool"
  where "vdistinct xs = distinct (vlist_of_vfsequence xs)"


text\<open>Transfer.\<close>

lemma vdistinct_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vfsequence ===> (=)) vdistinct distinct"
  by (intro rel_funI, unfold cr_vfsequence_def) (simp add: vdistinct_def)

lemma vdistinct_ll_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_cr_vfsequence ===> (=)) vdistinct distinct" 
  by (intro rel_funI, unfold cr_cr_vfsequence_def)
    (
      metis 
        vdistinct_def 
        distinct_map 
        inj_onI 
        vlist_of_vfsequence_vfsequence_of_vlist
    )


text\<open>Elementary properties.\<close>

lemma (in vfsequence) vfsequence_vdistinct_if_vcard_vrange_eq_vcard:
  assumes "vcard (\<R>\<^sub>\<circ> xs) = vcard xs"
  shows "vdistinct xs"
proof-
  have "finite (elts (\<R>\<^sub>\<circ> xs))" by (simp add: assms vcard_vfinite_omega)
  from vcard_finite_set[OF this] assms have "card (elts (\<R>\<^sub>\<circ> xs))\<^sub>\<nat> = vcard xs"
    by simp
  from card_distinct[where ?'a=V, untransferred, OF vfsequence_axioms this] 
  show ?thesis.
qed

lemma vdistinct_vempty[intro, simp]: "vdistinct []\<^sub>\<circ>"
proof-
  have t: "distinct ([]::V list)" by simp
  show ?thesis by (rule t[untransferred])
qed

lemma (in vfsequence) vfsequence_vcons_vdistinct:
  assumes "vdistinct (xs #\<^sub>\<circ> x)" 
  shows "vdistinct xs"
proof-
  from distinct.simps(2)[where 'a=V, THEN iffD1, THEN conjunct2, untransferred]
  show ?thesis
    using vfsequence_axioms assms by simp
qed

lemma (in vfsequence) vfsequence_vcons_nin_vrange:
  assumes "vdistinct (xs #\<^sub>\<circ> x)" 
  shows "x \<notin>\<^sub>\<circ> \<R>\<^sub>\<circ> xs"
proof-
  from distinct.simps(2)[where 'a=V, THEN iffD1, THEN conjunct1, untransferred]
  show ?thesis
    using vfsequence_axioms assms by simp
qed

lemma (in vfsequence) vfsequence_v11I[intro]:
  assumes "vdistinct xs"
  shows "v11 xs"
  using vfsequence_axioms assms
proof(induction xs rule: vfsequence_induct)
  case (vcons xs x)
  interpret vfsequence xs by (rule vcons(1))
  from vcons(3) have dxs: "vdistinct xs" by (rule vfsequence_vcons_vdistinct)
  interpret v11 xs using dxs by (rule vcons(2))
  from vfsequence_vcons_nin_vrange[OF vcons(3)] have "x \<notin>\<^sub>\<circ> \<R>\<^sub>\<circ> xs" .
  show "v11 (xs #\<^sub>\<circ> x)"
    by  
      ( 
        simp_all add: 
          vcons_def vfsequence_vdomain vfsequence_vcons_nin_vrange[OF vcons(3)]
      )
qed simp

lemma (in vfsequence) vfsequence_vcons_vdistinctI:
  assumes "vdistinct xs" and "x \<notin>\<^sub>\<circ> \<R>\<^sub>\<circ> xs"
  shows "vdistinct (xs #\<^sub>\<circ> x)"
proof-
  have t: "distinct xs \<Longrightarrow> x \<notin> list.set xs \<Longrightarrow> distinct (x # xs)" 
    for x ::V and xs 
    by simp
  from vfsequence_axioms assms show ?thesis by (rule t[untransferred])
qed

lemmas vfsequence_vcons_vdistinctI[intro] =
  vfsequence.vfsequence_vcons_vdistinctI 

lemma (in vfsequence) vfsequence_nin_vrange_vcons:
  assumes "y \<notin>\<^sub>\<circ> \<R>\<^sub>\<circ> xs" and "y \<noteq> x"
  shows "y \<notin>\<^sub>\<circ> \<R>\<^sub>\<circ> (xs #\<^sub>\<circ> x)"
proof-
  have t: "y \<notin> list.set xs \<Longrightarrow> y \<noteq> x \<Longrightarrow> y \<notin> list.set (x # xs)" 
    for x y :: V and xs
    by simp
  from vfsequence_axioms assms show ?thesis by (rule t[untransferred])
qed

lemmas vfsequence_nin_vrange_vcons[intro] = 
  vfsequence.vfsequence_nin_vrange_vcons


subsubsection\<open>Concatenation of sequences\<close>

definition vconcat :: "V \<Rightarrow> V"
  where "vconcat xss =
    vfsequence_of_vlist(
      concat (map vlist_of_vfsequence (vlist_of_vfsequence xss))
    )"


text\<open>Transfer.\<close>

lemma vconcat_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_cr_vfsequence ===> cr_vfsequence) vconcat concat"
proof(intro rel_funI)
  fix xs ys assume "cr_cr_vfsequence xs ys"
  then have xs_def: "xs = vfsequence_of_vlist (map vfsequence_of_vlist ys)"
    unfolding cr_cr_vfsequence_def by simp
  have main_eq: "map vlist_of_vfsequence (vlist_of_vfsequence xs) = ys"
    unfolding xs_def by (simp add: map_idI)
  show "cr_vfsequence (vconcat xs) (concat ys)"
    unfolding cr_vfsequence_def vconcat_def main_eq ..
qed


text\<open>Elementary properties.\<close>

lemma vconcat_vempty[simp]: "vconcat []\<^sub>\<circ> = []\<^sub>\<circ>"
  unfolding vconcat_def by simp

lemma vconcat_append[simp]: 
  assumes "vfsequence xss" 
    and "\<forall>xs\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> xss. vfsequence xs" 
    and "vfsequence yss"
    and "\<forall>xs\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> yss. vfsequence xs" 
  shows "vconcat (xss @\<^sub>\<circ> yss) = vconcat xss @\<^sub>\<circ> vconcat yss"
  using assms concat_append[where 'a=V, untransferred] by simp

lemma vconcat_vcons[simp]: 
  assumes "vfsequence xs" and "vfsequence xss" and "\<forall>xs\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> xss. vfsequence xs"
  shows "vconcat (xss #\<^sub>\<circ> xs) = vconcat xss @\<^sub>\<circ> xs"
  using assms concat.simps(2)[where 'a=V, untransferred] by simp

lemma (in vfsequence) vfsequence_vconcat_fsingleton[simp]: "vconcat [xs]\<^sub>\<circ> = xs"
  using vfsequence_axioms 
  by 
    (
      metis 
        vfsequence_vappend_vempty_vfsequence 
        vconcat_vcons 
        vconcat_vempty 
        vempty_nin 
        vfsequence_vempty 
        vrange_vempty
    )

lemmas vfsequence_vconcat_fsingleton[simp] = 
  vfsequence.vfsequence_vconcat_fsingleton



subsection\<open>Finite sequences and the Cartesian product\<close>

lemma vfsequence_vcons_vproductI[intro!]:
  assumes "n \<in>\<^sub>\<circ> \<omega>" 
    and "xs \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>vcard xs. A i)" 
    and "x \<in>\<^sub>\<circ> A (vcard xs)" 
    and "n = vcard (xs #\<^sub>\<circ> x)"
  shows "xs #\<^sub>\<circ> x \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>n. A i)"
proof
  interpret xs: vfsequence xs 
    using assms
    apply(intro vfsequenceI)
    subgoal by auto
    subgoal
      by 
        (
          metis 
            vcard_vfinite_omega 
            vcons_vsubset 
            vfinite_vcard_omega 
            vfinite_vsubset vproductD(2)
        )
    done
  interpret xsx: vfsequence \<open>xs #\<^sub>\<circ> x\<close> by auto
  show "vsv (xs #\<^sub>\<circ> x)" by (simp add: xsx.vsv_axioms)
  show D: "\<D>\<^sub>\<circ> (xs #\<^sub>\<circ> x) = n" unfolding assms(4) xsx.vfsequence_vdomain by auto
  from vproductD[OF assms(2)] have elem: "i \<in>\<^sub>\<circ> vcard xs \<Longrightarrow> xs\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i" for i
    by auto
  show "\<forall>i\<in>\<^sub>\<circ>n. (xs #\<^sub>\<circ> x)\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i" by (auto simp: elem assms(3,4))
qed

lemma vfsequence_vcons_vproductD[dest]:
  assumes "xs #\<^sub>\<circ> x \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>n. A i)" and "n \<in>\<^sub>\<circ> \<omega>"
  shows "xs \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>vcard xs. A i)" 
    and "x \<in>\<^sub>\<circ> A (vcard xs)" 
    and "n = vcard (xs #\<^sub>\<circ> x)" 
proof-

  interpret xsx: vfsequence \<open>xs #\<^sub>\<circ> x\<close> 
    by (meson assms succ_in_omega vfsequence_vproduct)
  interpret xs: vfsequence xs
    by (blast intro: xsx.vfsequence_vremove_vcons_vfsequence)

  show n_def: "n = vcard (xs #\<^sub>\<circ> x)"
    using assms using xsx.vfsequence_vdomain by blast
  from vproductD[OF assms(1), unfolded n_def] 
  have elem_xs_x: "i \<in>\<^sub>\<circ> vcard (xs #\<^sub>\<circ> x) \<Longrightarrow> (xs #\<^sub>\<circ> x)\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i" 
    for i
    by auto
  then have elem_xs[simp]: "i \<in>\<^sub>\<circ> vcard xs \<Longrightarrow> xs\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i" for i
    by (metis rev_vsubsetD vcard_mono vcons_vsubset xs.vfsequence_at_not_last)
  show "xs \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>vcard xs. A i)"
    by (auto simp: xs.vsv_axioms xs.vfsequence_vdomain)
  from elem_xs_x show "x \<in>\<^sub>\<circ> A (vcard xs)" by fastforce

qed

lemma vfsequence_vcons_vproductE[elim!]:
  assumes "xs #\<^sub>\<circ> x \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>n. A i)" and "n \<in>\<^sub>\<circ> \<omega>"
  obtains "xs \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>vcard xs. A i)" 
    and "x \<in>\<^sub>\<circ> A (vcard xs)" 
    and "n = vcard (xs #\<^sub>\<circ> x)" 
  using assms by (auto simp: vfsequence_vcons_vproductD)



subsection\<open>Binary Cartesian product based on finite sequences: \<open>ftimes\<close>\<close>

definition ftimes :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>\<times>\<^sub>\<bullet>\<close> 80)
  where "ftimes a b \<equiv> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. if i = 0 then a else b)"

lemma small_fpairs[simp]: "small {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"
  by (rule down[of _ r]) clarsimp


text\<open>Rules.\<close>

lemma ftimesI1[intro]: 
  assumes "x = [a, b]\<^sub>\<circ>" and "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> B"
  shows "x \<in>\<^sub>\<circ> A \<times>\<^sub>\<bullet> B"
  unfolding ftimes_def
proof
  show vsv: "vsv x" by (simp add: assms(1) vfsequence.axioms(1))
  then interpret vsv x .
  from assms show D: "\<D>\<^sub>\<circ> x = 2\<^sub>\<nat>" 
    unfolding nat_omega_simps two One_nat_def by auto
  from assms(2,3) have i: "i \<in>\<^sub>\<circ> 2\<^sub>\<nat> \<Longrightarrow> x\<lparr>i\<rparr> \<in>\<^sub>\<circ> (if i = 0\<^sub>\<nat> then A else B)" 
    for i
    unfolding assms(1) two nat_omega_simps One_nat_def by auto
  from i show "\<forall>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. x\<lparr>i\<rparr> \<in>\<^sub>\<circ> (if i = 0 then A else B)" by auto
qed

lemma ftimesI2[intro!]: 
  assumes "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> B"
  shows "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> A \<times>\<^sub>\<bullet> B"
  using assms ftimesI1 by auto

lemma fproductE1[elim!]:
  assumes "x \<in>\<^sub>\<circ> A \<times>\<^sub>\<bullet> B"
  obtains a b where "x = [a, b]\<^sub>\<circ>" and "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> B"
proof-
  from vproduct_vdoubletonD[OF assms[unfolded two ftimes_def]] 
  have x_def: "x = set {\<langle>0\<^sub>\<nat>, x\<lparr>0\<^sub>\<nat>\<rparr>\<rangle>, \<langle>1\<^sub>\<nat>, x\<lparr>1\<^sub>\<nat>\<rparr>\<rangle>}"
    and "x\<lparr>0\<^sub>\<nat>\<rparr> \<in>\<^sub>\<circ> A" 
    and "x\<lparr>1\<^sub>\<nat>\<rparr> \<in>\<^sub>\<circ> B" 
    by auto
  then show ?thesis using that using vcons_vdoubleton by simp
qed

lemma fproductE2[elim!]:
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> A \<times>\<^sub>\<bullet> B" obtains "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> B"
  using assms by blast


text\<open>Set operations.\<close>

lemma vfinite_0_left[simp]: "0 \<times>\<^sub>\<bullet> b = 0"
  by (meson eq0_iff fproductE1)

lemma vfinite_0_right[simp]: "a \<times>\<^sub>\<bullet> 0 = 0"
  by (meson eq0_iff fproductE1)

lemma fproduct_vintersection: "(a \<inter>\<^sub>\<circ> b) \<times>\<^sub>\<bullet> (c \<inter>\<^sub>\<circ> d) = (a \<times>\<^sub>\<bullet> c) \<inter>\<^sub>\<circ> (b \<times>\<^sub>\<bullet> d)"
  by auto

lemma fproduct_vdiff: "a \<times>\<^sub>\<bullet> (b -\<^sub>\<circ> c) = (a \<times>\<^sub>\<bullet> b) -\<^sub>\<circ> (a \<times>\<^sub>\<bullet> c)" by auto

lemma vfinite_ftimesI[intro!]:
  assumes "vfinite a" and "vfinite b"
  shows "vfinite (a \<times>\<^sub>\<bullet> b)"
  using assms(1,2) 
proof(induction arbitrary: b rule: vfinite_induct)
  case (vinsert x a')
  from vinsert(4) have "vfinite (set {x} \<times>\<^sub>\<bullet> b)"
  proof(induction rule: vfinite_induct)
    case (vinsert y b')
    have "set {x} \<times>\<^sub>\<bullet> vinsert y b' = vinsert [x, y]\<^sub>\<circ> (set {x} \<times>\<^sub>\<bullet> b')" by auto
    with vinsert(3) show ?case by simp
  qed simp
  moreover have "vinsert x a' \<times>\<^sub>\<bullet> b = (set {x} \<times>\<^sub>\<bullet> b) \<union>\<^sub>\<circ> (a' \<times>\<^sub>\<bullet> b)" by auto
  ultimately show ?case using vinsert by (auto simp: vfinite_vunionI)
qed simp


text\<open>\<open>ftimes\<close> and \<open>vcpower\<close>\<close>

lemma vproduct_vpair: "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. f i) \<longleftrightarrow> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> f (0\<^sub>\<nat>) \<times>\<^sub>\<circ> f (1\<^sub>\<nat>)"
proof
  interpret vfsequence \<open>[a, b]\<^sub>\<circ>\<close> by simp
  show "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. f i) \<Longrightarrow> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> f (0\<^sub>\<nat>) \<times>\<^sub>\<circ> f (1\<^sub>\<nat>)"
    unfolding vcons_vdoubleton two by (elim vproduct_vdoubletonE) auto
  assume hyp: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> f (0\<^sub>\<nat>) \<times>\<^sub>\<circ> f (1\<^sub>\<nat>)" 
  then have af: "a \<in>\<^sub>\<circ> f (0\<^sub>\<nat>)" and bf: "b \<in>\<^sub>\<circ> f (1\<^sub>\<nat>)" by auto
  have dom: "\<D>\<^sub>\<circ> [a, b]\<^sub>\<circ> = set {0\<^sub>\<nat>, 1\<^sub>\<nat>}" by (auto intro!: vsubset_antisym)
  have ran: "\<R>\<^sub>\<circ> [a, b]\<^sub>\<circ> \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. f i)"
    unfolding two using af bf vifunion_vdoubleton by auto  
  show "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. f i)"
    apply(intro vproductI)
    subgoal using dom ran vsv_axioms unfolding two by auto
    subgoal using af bf unfolding two by (auto intro!: vsubset_antisym)
    subgoal 
      unfolding two 
      using hyp VSigmaE2 small_empty vcons_vdoubleton 
      by (auto simp: vinsert_set_insert_eq)
    done
qed


text\<open>Connections.\<close>

lemma vcpower_two_ftimes: "A ^\<^sub>\<times> 2\<^sub>\<nat> = A \<times>\<^sub>\<bullet> A" 
  unfolding vcpower_def ftimes_def two by simp

lemma vcpower_two_ftimesI[intro]: 
  assumes "x \<in>\<^sub>\<circ> A \<times>\<^sub>\<bullet> A"
  shows "x \<in>\<^sub>\<circ> A ^\<^sub>\<times> 2\<^sub>\<nat>"
  using assms unfolding ftimes_def two by auto

lemma vcpower_two_ftimesD[dest]:
  assumes "x \<in>\<^sub>\<circ> A ^\<^sub>\<times> 2\<^sub>\<nat>"
  shows "x \<in>\<^sub>\<circ> A \<times>\<^sub>\<bullet> A"
  using assms unfolding vcpower_def ftimes_def two by simp

lemma vcpower_two_ftimesE[elim]:
  assumes "x \<in>\<^sub>\<circ> A ^\<^sub>\<times> 2\<^sub>\<nat>" and "x \<in>\<^sub>\<circ> A \<times>\<^sub>\<bullet> A \<Longrightarrow> P"
  shows P
  using assms unfolding vcpower_def ftimes_def two by simp

lemma vfsequence_vcpower_two_vpair: "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> A ^\<^sub>\<times> 2\<^sub>\<nat> \<longleftrightarrow> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> A"
proof(rule iffI)
  show "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> A ^\<^sub>\<times> 2\<^sub>\<nat> \<Longrightarrow> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> A"
    by (elim vcpowerE, unfold vproduct_vpair) 
qed (intro vcpowerI, unfold vproduct_vpair)

lemma vsv_vfsequence_two: 
  assumes "vsv gf" and "\<D>\<^sub>\<circ> gf = 2\<^sub>\<nat>"
  shows "[vpfst gf, vpsnd gf]\<^sub>\<circ> = gf"
proof-
  interpret gf: vsv gf by (auto intro: assms(1))
  show ?thesis
    by
      (
        rule sym,
        rule vsv_eqI, 
        blast, 
        blast, 
        simp add: assms(2) nat_omega_simps,
        unfold assms(2),
        elim_in_numeral,
        all\<open>simp add: nat_omega_simps\<close>
      )
qed

lemma vsv_vfsequence_three: 
  assumes "vsv hgf" and "\<D>\<^sub>\<circ> hgf = 3\<^sub>\<nat>"
  shows "[vpfst hgf, vpsnd hgf, vpthrd hgf]\<^sub>\<circ> = hgf"
proof-
  interpret hgf: vsv hgf by (auto intro: assms(1))
  show ?thesis
    by
      (
        rule sym,
        rule vsv_eqI, 
        blast, 
        blast, 
        simp add: assms(2) nat_omega_simps,
        unfold assms(2),
        elim_in_numeral,
        all\<open>simp add: nat_omega_simps\<close>
      )
qed



subsection\<open>Sequence as an element of a Cartesian power of a set\<close>

lemma vcons_in_vcpowerI[intro!]: 
  assumes "n \<in>\<^sub>\<circ> \<omega>" 
    and "xs \<in>\<^sub>\<circ> A ^\<^sub>\<times> vcard xs" 
    and "x \<in>\<^sub>\<circ> A" 
    and "n = vcard (xs #\<^sub>\<circ> x)" 
  shows "xs #\<^sub>\<circ> x \<in>\<^sub>\<circ> A ^\<^sub>\<times> n"
proof-
  interpret vfsequence xs
    using assms
    by
      (
        meson 
          vcons_vsubset 
          vfinite_vcard_omega_iff 
          vfinite_vsubset 
          vfsequence_vcpower
      )
  show ?thesis 
    by 
      (
        metis 
          assms(2,3,4)
          vcpower_vrange 
          vfsequence_vcons 
          vfsequence_vcons_vrange 
          vfsequence.vfsequence_vrange_vcpower 
          vsubset_vinsert_leftI
      )
qed

lemma vcons_in_vcpowerD[dest]: 
  assumes "xs #\<^sub>\<circ> x \<in>\<^sub>\<circ> A ^\<^sub>\<times> n" and "n \<in>\<^sub>\<circ> \<omega>"
  shows "xs \<in>\<^sub>\<circ> A ^\<^sub>\<times> vcard xs" 
    and "x \<in>\<^sub>\<circ> A" 
    and "n = vcard (xs #\<^sub>\<circ> x)" 
proof-
  interpret vfsequence xs 
    by 
      (
        meson 
          assms 
          vfsequence.vfsequence_vremove_vcons_vfsequence 
          vfsequence_vcpower
      )
  from assms vfsequence_vcard_vcons show "n = vcard (xs #\<^sub>\<circ> x)" by auto
  then show "xs \<in>\<^sub>\<circ> A ^\<^sub>\<times> vcard xs" 
    by 
      (
        metis 
          assms(1) 
          vcpower_vrange 
          vfsequence_vcons_vrange 
          vfsequence_vrange_vcpower 
          vsubset_vinsert_leftD
      )
  show "x \<in>\<^sub>\<circ> A"
    by 
      (
        metis 
          assms(1) 
          vcpower_vrange 
          vfsequence.vfsequence_vcons_vrange 
          vfsequence_axioms 
          vinsertI1 
          vsubsetE
      )
qed

lemma vcons_in_vcpowerE1[elim!]: 
  assumes "xs #\<^sub>\<circ> x \<in>\<^sub>\<circ> A ^\<^sub>\<times> n" and "n \<in>\<^sub>\<circ> \<omega>"
  obtains "xs \<in>\<^sub>\<circ> A ^\<^sub>\<times> vcard xs" and "x \<in>\<^sub>\<circ> A" and "n = vcard (xs #\<^sub>\<circ> x)" 
  using assms by blast

lemma vcons_in_vcpowerE2: 
  assumes "xs \<in>\<^sub>\<circ> A ^\<^sub>\<times> n" and "n \<in>\<^sub>\<circ> \<omega>" and "0 \<in>\<^sub>\<circ> n"
  obtains x xs' where "xs = xs' #\<^sub>\<circ> x"
    and "xs' \<in>\<^sub>\<circ> A ^\<^sub>\<times> vcard xs'" 
    and "x \<in>\<^sub>\<circ> A" 
    and "n = vcard (xs' #\<^sub>\<circ> x)" 
proof-
  interpret vfsequence xs using assms(1,2) by auto
  from assms obtain x xs' where xs_def: "xs = xs' #\<^sub>\<circ> x"
    by 
      (
        metis 
          eq0_iff vcard_0 vcpower_vdomain vfsequence_vcons_ex vfsequence_vdomain
      )
  from vcons_in_vcpowerE1[OF assms(1)[unfolded xs_def] assms(2)] have
    "xs' \<in>\<^sub>\<circ> A ^\<^sub>\<times> vcard xs'" and "x \<in>\<^sub>\<circ> A" and "n = vcard (xs' #\<^sub>\<circ> x)" 
    by blast+
  from xs_def this show ?thesis by (clarsimp simp: that)
qed

lemma vcons_vcpower1E: (*TODO: generalize*)
  assumes "xs \<in>\<^sub>\<circ> A ^\<^sub>\<times> 1\<^sub>\<nat>"  
  obtains x where "xs = [x]\<^sub>\<circ>" and "x \<in>\<^sub>\<circ> A"
proof-
  have 01: "0 \<in>\<^sub>\<circ> 1\<^sub>\<nat>" by simp
  from vcons_in_vcpowerE2[OF assms ord_of_nat_\<omega> 01] obtain x xs' 
    where xs_def: "xs = xs' #\<^sub>\<circ> x"
      and xs': "xs' \<in>\<^sub>\<circ> A ^\<^sub>\<times> vcard xs'" 
      and x: "x \<in>\<^sub>\<circ> A" 
      and one: "1\<^sub>\<nat> = vcard (xs' #\<^sub>\<circ> x)" 
    by metis
  interpret xs: vfsequence xs using assms by (auto intro: vfsequence_vcpower)
  interpret xs': vfsequence xs' 
    using xs' xs_def xs.vfsequence_vremove_vcons_vfsequence by blast
  from one have "vcard xs' = 0" 
    by (metis ord_of_nat_succ_vempty succ_inject_iff xs'.vfsequence_vcard_vcons)
  then have "xs = [x]\<^sub>\<circ>" unfolding xs_def by (simp add: vcard_vempty)
  with x that show ?thesis by simp
qed

text\<open>\newpage\<close>

end