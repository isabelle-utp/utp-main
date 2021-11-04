(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Equipollence\<close>
theory CZH_Sets_Equipollence
  imports CZH_Sets_IF
begin



subsection\<open>Background\<close>


text\<open>
The section presents an adaption of the existing framework \<open>Equipollence\<close>
in the main library of Isabelle/HOL to the type \<^typ>\<open>V\<close>.

Some of content of this theory was ported directly (with amendments) from the 
theory \<open>HOL-Library.Equipollence\<close> in the main library of Isabelle/HOL.
\<close>



subsection\<open>\<open>veqpoll\<close>\<close>

abbreviation veqpoll :: "V \<Rightarrow> V \<Rightarrow> bool" (infixl "\<approx>\<^sub>\<circ>" 50) 
  where "A \<approx>\<^sub>\<circ> B \<equiv> elts A \<approx> elts B"


text\<open>Rules\<close>

lemma (in v11) v11_veqpollI[intro]:
  assumes "\<D>\<^sub>\<circ> r = A" and "\<R>\<^sub>\<circ> r = B"
  shows "A \<approx>\<^sub>\<circ> B" 
  unfolding eqpoll_def 
proof(intro exI[of _ \<open>\<lambda>x. r\<lparr>x\<rparr>\<close>] bij_betw_imageI)
  from v11.v11_injective v11_axioms show "inj_on (app r) (elts A)"
    unfolding assms[symmetric] by (intro inj_onI) blast
  show "app r ` elts A = elts B" unfolding assms[symmetric] by force+
qed

lemmas v11_veqpollI[intro] = v11.v11_veqpollI

lemma v11_veqpollE[elim]: 
  assumes "A \<approx>\<^sub>\<circ> B" 
  obtains f where "v11 f" and "\<D>\<^sub>\<circ> f = A" and "\<R>\<^sub>\<circ> f = B"
proof-
  from assms obtain f where bij_f: "bij_betw f (elts A) (elts B)"
    unfolding eqpoll_def by auto
  then have "v11 (\<lambda>a\<in>\<^sub>\<circ>A. f a)" 
    and "\<D>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a) = A" 
    and "\<R>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a) = B"
    by (auto simp add: in_mono vrange_VLambda)
  then show ?thesis using that by simp
qed

  
text\<open>Set operations.\<close>

lemma veqpoll_vsingleton: "set {x} \<approx>\<^sub>\<circ> set {y}"
  by (simp add: singleton_eqpoll)

lemma veqpoll_vinsert:
  assumes "A \<approx>\<^sub>\<circ> B" and "a \<notin>\<^sub>\<circ> A" and "b \<notin>\<^sub>\<circ> B"
  shows "vinsert a A \<approx>\<^sub>\<circ> vinsert b B"
  using assms by (simp add: insert_eqpoll_insert_iff)

lemma veqpoll_pair: 
  assumes "a \<noteq> b" and "c \<noteq> d"
  shows "set {a, b} \<approx>\<^sub>\<circ> set {c, d}"
  using assms by (simp add: insert_eqpoll_cong)

lemma veqpoll_vpair: 
  assumes "a \<noteq> b" and "c \<noteq> d"
  shows "\<langle>a, b\<rangle> \<approx>\<^sub>\<circ> \<langle>c, d\<rangle>"
  using assms 
  unfolding vpair_def 
  by (metis doubleton_eq_iff insert_absorb2 veqpoll_pair)



subsection\<open>\<open>vlepoll\<close>\<close>

abbreviation vlepoll :: "V \<Rightarrow> V \<Rightarrow> bool" (infixl "\<lesssim>\<^sub>\<circ>" 50) 
  where "A \<lesssim>\<^sub>\<circ> B \<equiv> elts A \<lesssim> elts B"


text\<open>Set operations.\<close>

lemma vlepoll_vsubset: 
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "A \<lesssim>\<^sub>\<circ> B"
  using assms by (simp add: less_eq_V_def subset_imp_lepoll)


text\<open>Special properties.\<close>

lemma vlepoll_singleton_vinsert: "set {x} \<lesssim>\<^sub>\<circ> vinsert y A" 
  by (simp add: singleton_lepoll)

lemma vlepoll_vempty_iff[simp]: "A \<lesssim>\<^sub>\<circ> 0 \<longleftrightarrow> A = 0" by (rule iffI) fastforce+



subsection\<open>\<open>vlespoll\<close>\<close>

abbreviation vlesspoll :: "V \<Rightarrow> V \<Rightarrow> bool" (infixl \<open>\<prec>\<^sub>\<circ>\<close> 50)
  where "A \<prec>\<^sub>\<circ> B \<equiv> elts A \<prec> elts B"

lemma vlesspoll_def: "A \<prec>\<^sub>\<circ> B = (A \<lesssim>\<^sub>\<circ> B \<and> ~(A \<approx>\<^sub>\<circ> B))" by (simp add: lesspoll_def)


text\<open>Rules.\<close>

lemmas vlesspollI[intro] = vlesspoll_def[THEN iffD2]

lemmas vlesspollD[dest] = vlesspoll_def[THEN iffD1]

lemma vlesspollE[elim]:
  assumes "A \<prec>\<^sub>\<circ> B" and "A \<lesssim>\<^sub>\<circ> B \<Longrightarrow> ~(A \<approx>\<^sub>\<circ> B) \<Longrightarrow> P"
  shows P
  using assms by (simp add: vlesspoll_def)

lemma (in v11) v11_vlepollI[intro]: 
  assumes "\<D>\<^sub>\<circ> r = A" and "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> B"
  shows "A \<lesssim>\<^sub>\<circ> B" 
  unfolding lepoll_def 
proof(intro exI[of _ \<open>\<lambda>x. r\<lparr>x\<rparr>\<close>] conjI)
  show "inj_on (app r) (elts A)"
    using assms(1) v11.v11_injective v11_axioms by (intro inj_onI) blast
  show "app r ` elts A \<subseteq> elts B"
    by (intro subsetI) (metis assms(1,2) imageE rev_vsubsetD vdomain_atD)
qed

lemmas v11_vlepollI[intro] = v11.v11_vlepollI

lemma v11_vlepollE[elim]: 
  assumes "A \<lesssim>\<^sub>\<circ> B" 
  obtains f where "v11 f" and "\<D>\<^sub>\<circ> f = A" and "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> B"
proof-
  from assms obtain f where "inj_on f (elts A)" and "f ` elts A \<subseteq> elts B"
    unfolding lepoll_def by auto
  then have "v11 (\<lambda>a\<in>\<^sub>\<circ>A. f a)" 
    and "\<D>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a) = A" 
    and "\<R>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a) \<subseteq>\<^sub>\<circ> B"
    by (auto simp: in_mono vrange_VLambda)
  then show ?thesis using that by simp
qed

text\<open>\newpage\<close>

end