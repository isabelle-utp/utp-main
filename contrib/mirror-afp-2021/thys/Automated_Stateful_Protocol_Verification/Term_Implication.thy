(*
(C) Copyright Andreas Viktor Hess, DTU, 2020
(C) Copyright Sebastian A. Mödersheim, DTU, 2020
(C) Copyright Achim D. Brucker, University of Exeter, 2020
(C) Copyright Anders Schlichtkrull, DTU, 2020

All Rights Reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

- Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

- Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

- Neither the name of the copyright holder nor the names of its
  contributors may be used to endorse or promote products
  derived from this software without specific prior written
  permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(*  Title:      Term_Implication.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
*)

section\<open>Term Implication\<close>
theory Term_Implication
  imports Stateful_Protocol_Model Term_Variants
begin

subsection \<open>Single Term Implications\<close>
definition timpl_apply_term ("\<langle>_ --\<guillemotright> _\<rangle>\<langle>_\<rangle>") where
  "\<langle>a --\<guillemotright> b\<rangle>\<langle>t\<rangle> \<equiv> term_variants ((\<lambda>_. [])(Abs a := [Abs b])) t"

definition timpl_apply_terms ("\<langle>_ --\<guillemotright> _\<rangle>\<langle>_\<rangle>\<^sub>s\<^sub>e\<^sub>t") where
  "\<langle>a --\<guillemotright> b\<rangle>\<langle>M\<rangle>\<^sub>s\<^sub>e\<^sub>t \<equiv> \<Union>((set o timpl_apply_term a b) ` M)"

lemma timpl_apply_Fun:
  assumes "\<And>i. i < length T \<Longrightarrow> S ! i \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>T ! i\<rangle>"
    and "length T = length S"
  shows "Fun f S \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>Fun f T\<rangle>"
using assms term_variants_Fun term_variants_pred_iff_in_term_variants
by (metis timpl_apply_term_def)

lemma timpl_apply_Abs:
  assumes "\<And>i. i < length T \<Longrightarrow> S ! i \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>T ! i\<rangle>"
    and "length T = length S"
  shows "Fun (Abs b) S \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>Fun (Abs a) T\<rangle>"
using assms(1) term_variants_P[OF assms(2), of "(\<lambda>_. [])(Abs a := [Abs b])" "Abs b" "Abs a"]
unfolding timpl_apply_term_def term_variants_pred_iff_in_term_variants[symmetric]
by fastforce

lemma timpl_apply_refl: "t \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>t\<rangle>"
unfolding timpl_apply_term_def
by (metis term_variants_pred_refl term_variants_pred_iff_in_term_variants)

lemma timpl_apply_const: "Fun (Abs b) [] \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>Fun (Abs a) []\<rangle>"
using term_variants_pred_iff_in_term_variants term_variants_pred_const
unfolding timpl_apply_term_def by auto

lemma timpl_apply_const':
  "c = a \<Longrightarrow> set \<langle>a --\<guillemotright> b\<rangle>\<langle>Fun (Abs c) []\<rangle> = {Fun (Abs b) [], Fun (Abs c) []}"
  "c \<noteq> a \<Longrightarrow> set \<langle>a --\<guillemotright> b\<rangle>\<langle>Fun (Abs c) []\<rangle> = {Fun (Abs c) []}"
using term_variants_pred_const_cases[of "(\<lambda>_. [])(Abs a := [Abs b])" "Abs c"]
      term_variants_pred_iff_in_term_variants[of "(\<lambda>_. [])(Abs a := [Abs b])"]
unfolding timpl_apply_term_def by auto

lemma timpl_apply_term_subst:
  "s \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>t\<rangle> \<Longrightarrow> s \<cdot> \<delta> \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>t \<cdot> \<delta>\<rangle>"
by (metis term_variants_pred_iff_in_term_variants term_variants_pred_subst timpl_apply_term_def)

lemma timpl_apply_inv:
  assumes "Fun h S \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>Fun f T\<rangle>"
  shows "length T = length S"
    and "\<And>i. i < length T \<Longrightarrow> S ! i \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>T ! i\<rangle>"
    and "f \<noteq> h \<Longrightarrow> f = Abs a \<and> h = Abs b"
using assms term_variants_pred_iff_in_term_variants[of "(\<lambda>_. [])(Abs a := [Abs b])"]
unfolding timpl_apply_term_def
by (metis (full_types) term_variants_pred_inv(1),
    metis (full_types) term_variants_pred_inv(2),
    fastforce dest: term_variants_pred_inv(3))

lemma timpl_apply_inv':
  assumes "s \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>Fun f T\<rangle>"
  shows "\<exists>g S. s = Fun g S"
proof -
  have *: "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs b])) (Fun f T) s"
    using assms term_variants_pred_iff_in_term_variants[of "(\<lambda>_. [])(Abs a := [Abs b])"]
    unfolding timpl_apply_term_def by force
  show ?thesis using term_variants_pred.cases[OF *, of ?thesis] by fastforce
qed

lemma timpl_apply_term_Var_iff:
  "Var x \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>t\<rangle> \<longleftrightarrow> t = Var x"
using term_variants_pred_inv_Var term_variants_pred_iff_in_term_variants
unfolding timpl_apply_term_def by metis



subsection \<open>Term Implication Closure\<close>
inductive_set timpl_closure for t TI where
  FP: "t \<in> timpl_closure t TI"
| TI: "\<lbrakk>u \<in> timpl_closure t TI; (a,b) \<in> TI; term_variants_pred ((\<lambda>_. [])(Abs a := [Abs b])) u s\<rbrakk>
       \<Longrightarrow> s \<in> timpl_closure t TI"

definition "timpl_closure_set M TI \<equiv> (\<Union>t \<in> M. timpl_closure t TI)"

inductive_set timpl_closure'_step for TI where
  "\<lbrakk>(a,b) \<in> TI; term_variants_pred ((\<lambda>_. [])(Abs a := [Abs b])) t s\<rbrakk>
    \<Longrightarrow> (t,s) \<in> timpl_closure'_step TI"

definition "timpl_closure' TI \<equiv> (timpl_closure'_step TI)\<^sup>*"

definition comp_timpl_closure where
  "comp_timpl_closure FP TI \<equiv>
    let f = \<lambda>X. FP \<union> (\<Union>x \<in> X. \<Union>(a,b) \<in> TI. set \<langle>a --\<guillemotright> b\<rangle>\<langle>x\<rangle>)
    in while (\<lambda>X. f X \<noteq> X) f {}"

definition comp_timpl_closure_list where
  "comp_timpl_closure_list FP TI \<equiv>
    let f = \<lambda>X. remdups (concat (map (\<lambda>x. concat (map (\<lambda>(a,b). \<langle>a --\<guillemotright> b\<rangle>\<langle>x\<rangle>) TI)) X))
    in while (\<lambda>X. set (f X) \<noteq> set X) f FP"

lemma timpl_closure_setI:
  "t \<in> M \<Longrightarrow> t \<in> timpl_closure_set M TI"
unfolding timpl_closure_set_def by (auto intro: timpl_closure.FP)

lemma timpl_closure_set_empty_timpls:
  "timpl_closure t {} = {t}" (is "?A = ?B")
proof (intro subset_antisym subsetI)
  fix s show "s \<in> ?A \<Longrightarrow> s \<in> ?B"
    by (induct s rule: timpl_closure.induct) auto
qed (simp add: timpl_closure.FP)

lemmas timpl_closure_set_is_timpl_closure_union = meta_eq_to_obj_eq[OF timpl_closure_set_def]

lemma term_variants_pred_eq_case_Abs:
  fixes a b
  defines "P \<equiv> (\<lambda>_. [])(Abs a := [Abs b])"
  assumes "term_variants_pred P t s" "\<forall>f \<in> funs_term s. \<not>is_Abs f"
  shows "t = s"
using assms(2,3) P_def
proof (induction P t s rule: term_variants_pred.induct)
  case (term_variants_Fun T S f)
  have "\<not>is_Abs h" when i: "i < length S" and h: "h \<in> funs_term (S ! i)" for i h
    using i h term_variants_Fun.hyps(4) by auto
  hence "T ! i = S ! i" when i: "i < length T" for i using i term_variants_Fun.hyps(1,3) by auto
  hence "T = S" using term_variants_Fun.hyps(1) nth_equalityI[of T S] by fast
  thus ?case using term_variants_Fun.hyps(1) by blast
qed (simp_all add: term_variants_pred_refl)

lemma timpl_closure'_step_inv:
  assumes "(t,s) \<in> timpl_closure'_step TI"
  obtains a b where "(a,b) \<in> TI" "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs b])) t s"
using assms by (auto elim: timpl_closure'_step.cases)

lemma timpl_closure_mono:
  assumes "TI \<subseteq> TI'"
  shows "timpl_closure t TI \<subseteq> timpl_closure t TI'"
proof
  fix s show "s \<in> timpl_closure t TI \<Longrightarrow> s \<in> timpl_closure t TI'"
    apply (induct rule: timpl_closure.induct)
    using assms by (auto intro: timpl_closure.intros)
qed

lemma timpl_closure_set_mono:
  assumes "M \<subseteq> M'" "TI \<subseteq> TI'"
  shows "timpl_closure_set M TI \<subseteq> timpl_closure_set M' TI'"
using assms(1) timpl_closure_mono[OF assms(2)] unfolding timpl_closure_set_def by fast

lemma timpl_closure_idem:
  "timpl_closure_set (timpl_closure t TI) TI = timpl_closure t TI" (is "?A = ?B")
proof
  have "s \<in> timpl_closure t TI"
    when "s \<in> timpl_closure u TI" "u \<in> timpl_closure t TI"
    for s u
    using that
    by (induction rule: timpl_closure.induct)
       (auto intro: timpl_closure.intros)
  thus "?A \<subseteq> ?B" unfolding timpl_closure_set_def by blast

  show "?B \<subseteq> ?A"
    unfolding timpl_closure_set_def
    by (blast intro: timpl_closure.FP)
qed

lemma timpl_closure_set_idem:
  "timpl_closure_set (timpl_closure_set M TI) TI = timpl_closure_set M TI"
using timpl_closure_idem[of _ TI]unfolding timpl_closure_set_def by auto

lemma timpl_closure_set_mono_timpl_closure_set:
  assumes N: "N \<subseteq> timpl_closure_set M TI"
  shows "timpl_closure_set N TI \<subseteq> timpl_closure_set M TI"
using timpl_closure_set_mono[OF N, of TI TI] timpl_closure_set_idem[of M TI]
by simp

lemma timpl_closure_is_timpl_closure':
  "s \<in> timpl_closure t TI \<longleftrightarrow> (t,s) \<in> timpl_closure' TI"
proof
  show "s \<in> timpl_closure t TI \<Longrightarrow> (t,s) \<in> timpl_closure' TI"
    unfolding timpl_closure'_def
    by (induct rule: timpl_closure.induct)
       (auto intro: rtrancl_into_rtrancl timpl_closure'_step.intros)

  show "(t,s) \<in> timpl_closure' TI \<Longrightarrow> s \<in> timpl_closure t TI"
    unfolding timpl_closure'_def
    by (induct rule: rtrancl_induct)
       (auto dest: timpl_closure'_step_inv
             intro: timpl_closure.FP timpl_closure.TI)
qed

lemma timpl_closure'_mono:
  assumes "TI \<subseteq> TI'"
  shows "timpl_closure' TI \<subseteq> timpl_closure' TI'"
using timpl_closure_mono[OF assms]
      timpl_closure_is_timpl_closure'[of _ _ TI]
      timpl_closure_is_timpl_closure'[of _ _ TI']
by fast

lemma timpl_closureton_is_timpl_closure:
  "timpl_closure_set {t} TI = timpl_closure t TI"
by (simp add: timpl_closure_set_is_timpl_closure_union)

lemma timpl_closure'_timpls_trancl_subset:
  "timpl_closure' (c\<^sup>+) \<subseteq> timpl_closure' c"
unfolding timpl_closure'_def
proof
  fix s t::"(('a,'b,'c) prot_fun,'d) term"
  show "(s,t) \<in> (timpl_closure'_step (c\<^sup>+))\<^sup>* \<Longrightarrow> (s,t) \<in> (timpl_closure'_step c)\<^sup>*"
  proof (induction rule: rtrancl_induct)
    case (step u t)
    obtain a b where ab:
        "(a,b) \<in> c\<^sup>+" "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs b])) u t"
      using step.hyps(2) timpl_closure'_step_inv by blast
    hence "(u,t) \<in> (timpl_closure'_step c)\<^sup>*"
    proof (induction arbitrary: t rule: trancl_induct)
      case (step d e)
      obtain s where s:
          "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs d])) u s"
          "term_variants_pred ((\<lambda>_. [])(Abs d := [Abs e])) s t"
        using term_variants_pred_dense'[OF step.prems, of "Abs d"] by blast

      have "(u,s) \<in> (timpl_closure'_step c)\<^sup>*"
           "(s,t) \<in> timpl_closure'_step c"
        using step.hyps(2) s(2) step.IH[OF s(1)]
        by (auto intro: timpl_closure'_step.intros)
      thus ?case by simp
    qed (auto intro: timpl_closure'_step.intros)
    thus ?case using step.IH by simp
  qed simp
qed

lemma timpl_closure'_timpls_trancl_subset':
  "timpl_closure' {(a,b) \<in> c\<^sup>+. a \<noteq> b} \<subseteq> timpl_closure' c"
using timpl_closure'_timpls_trancl_subset
      timpl_closure'_mono[of "{(a,b) \<in> c\<^sup>+. a \<noteq> b}" "c\<^sup>+"]
by fast

lemma timpl_closure_set_timpls_trancl_subset:
  "timpl_closure_set M (c\<^sup>+) \<subseteq> timpl_closure_set M c"
using timpl_closure'_timpls_trancl_subset[of c]
      timpl_closure_is_timpl_closure'[of _ _ c]
      timpl_closure_is_timpl_closure'[of _ _ "c\<^sup>+"]
      timpl_closure_set_is_timpl_closure_union[of M c]
      timpl_closure_set_is_timpl_closure_union[of M "c\<^sup>+"]
by fastforce

lemma timpl_closure_set_timpls_trancl_subset':
  "timpl_closure_set M {(a,b) \<in> c\<^sup>+. a \<noteq> b} \<subseteq> timpl_closure_set M c"
using timpl_closure'_timpls_trancl_subset'[of c]
      timpl_closure_is_timpl_closure'[of _ _ c]
      timpl_closure_is_timpl_closure'[of _ _ "{(a,b) \<in> c\<^sup>+. a \<noteq> b}"]
      timpl_closure_set_is_timpl_closure_union[of M c]
      timpl_closure_set_is_timpl_closure_union[of M "{(a,b) \<in> c\<^sup>+. a \<noteq> b}"]
by fastforce

lemma timpl_closure'_timpls_trancl_supset':
  "timpl_closure' c \<subseteq> timpl_closure' {(a,b) \<in> c\<^sup>+. a \<noteq> b}"
unfolding timpl_closure'_def
proof
  let ?cl = "{(a,b) \<in> c\<^sup>+. a \<noteq> b}"

  fix s t::"(('e,'f,'c) prot_fun,'g) term"
  show "(s,t) \<in> (timpl_closure'_step c)\<^sup>* \<Longrightarrow> (s,t) \<in> (timpl_closure'_step ?cl)\<^sup>*"
  proof (induction rule: rtrancl_induct)
    case (step u t)
    obtain a b where ab:
        "(a,b) \<in> c" "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs b])) u t"
      using step.hyps(2) timpl_closure'_step_inv by blast
    hence "(a,b) \<in> c\<^sup>+" by simp
    hence "(u,t) \<in> (timpl_closure'_step ?cl)\<^sup>*" using ab(2)
    proof (induction arbitrary: t rule: trancl_induct)
      case (base d) show ?case
      proof (cases "a = d")
        case True thus ?thesis
          using base term_variants_pred_refl_inv[of _ u t]
          by force
      next
        case False thus ?thesis
          using base timpl_closure'_step.intros[of a d ?cl]
          by fast
      qed
    next
      case (step d e)
      obtain s where s:
          "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs d])) u s"
          "term_variants_pred ((\<lambda>_. [])(Abs d := [Abs e])) s t"
        using term_variants_pred_dense'[OF step.prems, of "Abs d"] by blast

      show ?case
      proof (cases "d = e")
        case True
        thus ?thesis
          using step.prems step.IH[of t]
          by blast
      next
        case False
        hence "(u,s) \<in> (timpl_closure'_step ?cl)\<^sup>*"
              "(s,t) \<in> timpl_closure'_step ?cl"
          using step.hyps(2) s(2) step.IH[OF s(1)]
          by (auto intro: timpl_closure'_step.intros)
        thus ?thesis by simp
      qed
    qed
    thus ?case using step.IH by simp
  qed simp
qed

lemma timpl_closure'_timpls_trancl_supset:
  "timpl_closure' c \<subseteq> timpl_closure' (c\<^sup>+)"
using timpl_closure'_timpls_trancl_supset'[of c]
      timpl_closure'_mono[of "{(a,b) \<in> c\<^sup>+. a \<noteq> b}" "c\<^sup>+"]
by fast

lemma timpl_closure'_timpls_trancl_eq:
  "timpl_closure' (c\<^sup>+) = timpl_closure' c"
using timpl_closure'_timpls_trancl_subset timpl_closure'_timpls_trancl_supset
by blast

lemma timpl_closure'_timpls_trancl_eq':
  "timpl_closure' {(a,b) \<in> c\<^sup>+. a \<noteq> b} = timpl_closure' c"
using timpl_closure'_timpls_trancl_subset' timpl_closure'_timpls_trancl_supset'
by blast

lemma timpl_closure'_timpls_rtrancl_subset:
  "timpl_closure' (c\<^sup>*) \<subseteq> timpl_closure' c"
unfolding timpl_closure'_def
proof
  fix s t::"(('a,'b,'c) prot_fun,'d) term"
  show "(s,t) \<in> (timpl_closure'_step (c\<^sup>*))\<^sup>* \<Longrightarrow> (s,t) \<in> (timpl_closure'_step c)\<^sup>*"
  proof (induction rule: rtrancl_induct)
    case (step u t)
    obtain a b where ab:
        "(a,b) \<in> c\<^sup>*" "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs b])) u t"
      using step.hyps(2) timpl_closure'_step_inv by blast
    hence "(u,t) \<in> (timpl_closure'_step c)\<^sup>*"
    proof (induction arbitrary: t rule: rtrancl_induct)
      case base
      hence "u = t" using term_variants_pred_refl_inv by fastforce
      thus ?case by simp
    next
      case (step d e)
      obtain s where s:
          "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs d])) u s"
          "term_variants_pred ((\<lambda>_. [])(Abs d := [Abs e])) s t"
        using term_variants_pred_dense'[OF step.prems, of "Abs d"] by blast

      have "(u,s) \<in> (timpl_closure'_step c)\<^sup>*"
           "(s,t) \<in> timpl_closure'_step c"
        using step.hyps(2) s(2) step.IH[OF s(1)]
        by (auto intro: timpl_closure'_step.intros)
      thus ?case by simp
    qed
    thus ?case using step.IH by simp
  qed simp
qed

lemma timpl_closure'_timpls_rtrancl_supset:
  "timpl_closure' c \<subseteq> timpl_closure' (c\<^sup>*)"
unfolding timpl_closure'_def
proof
  fix s t::"(('e,'f,'c) prot_fun,'g) term"
  show "(s,t) \<in> (timpl_closure'_step c)\<^sup>* \<Longrightarrow> (s,t) \<in> (timpl_closure'_step (c\<^sup>*))\<^sup>*"
  proof (induction rule: rtrancl_induct)
    case (step u t)
    obtain a b where ab:
        "(a,b) \<in> c" "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs b])) u t"
      using step.hyps(2) timpl_closure'_step_inv by blast
    hence "(a,b) \<in> c\<^sup>*" by simp
    hence "(u,t) \<in> (timpl_closure'_step (c\<^sup>*))\<^sup>*" using ab(2)
    proof (induction arbitrary: t rule: rtrancl_induct)
      case (base t) thus ?case using term_variants_pred_refl_inv[of _ u t] by fastforce
    next
      case (step d e)
      obtain s where s:
          "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs d])) u s"
          "term_variants_pred ((\<lambda>_. [])(Abs d := [Abs e])) s t"
        using term_variants_pred_dense'[OF step.prems, of "Abs d"] by blast

      show ?case
      proof (cases "d = e")
        case True
        thus ?thesis
          using step.prems step.IH[of t]
          by blast
      next
        case False
        hence "(u,s) \<in> (timpl_closure'_step (c\<^sup>*))\<^sup>*"
              "(s,t) \<in> timpl_closure'_step (c\<^sup>*)"
          using step.hyps(2) s(2) step.IH[OF s(1)]
          by (auto intro: timpl_closure'_step.intros)
        thus ?thesis by simp
      qed
    qed
    thus ?case using step.IH by simp
  qed simp
qed

lemma timpl_closure'_timpls_rtrancl_eq:
  "timpl_closure' (c\<^sup>*) = timpl_closure' c"
using timpl_closure'_timpls_rtrancl_subset timpl_closure'_timpls_rtrancl_supset
by blast

lemma timpl_closure_timpls_trancl_eq:
  "timpl_closure t (c\<^sup>+) = timpl_closure t c"
using timpl_closure'_timpls_trancl_eq[of c]
      timpl_closure_is_timpl_closure'[of _ _ c]
      timpl_closure_is_timpl_closure'[of _ _ "c\<^sup>+"]
by fastforce

lemma timpl_closure_set_timpls_trancl_eq:
  "timpl_closure_set M (c\<^sup>+) = timpl_closure_set M c"
using timpl_closure_timpls_trancl_eq
      timpl_closure_set_is_timpl_closure_union[of M c]
      timpl_closure_set_is_timpl_closure_union[of M "c\<^sup>+"]
by fastforce

lemma timpl_closure_set_timpls_trancl_eq':
  "timpl_closure_set M {(a,b) \<in> c\<^sup>+. a \<noteq> b} = timpl_closure_set M c"
using timpl_closure'_timpls_trancl_eq'[of c]
      timpl_closure_is_timpl_closure'[of _ _ c]
      timpl_closure_is_timpl_closure'[of _ _ "{(a,b) \<in> c\<^sup>+. a \<noteq> b}"]
      timpl_closure_set_is_timpl_closure_union[of M c]
      timpl_closure_set_is_timpl_closure_union[of M "{(a,b) \<in> c\<^sup>+. a \<noteq> b}"]
by fastforce

lemma timpl_closure_Var_in_iff:
  "Var x \<in> timpl_closure t TI \<longleftrightarrow> t = Var x" (is "?A \<longleftrightarrow> ?B")
proof
  have "s \<in> timpl_closure t TI \<Longrightarrow> s = Var x \<Longrightarrow> s = t" for s
    apply (induction rule: timpl_closure.induct)
    by (simp, metis term_variants_pred_inv_Var(2))
  thus "?A \<Longrightarrow> ?B" by blast
qed (blast intro: timpl_closure.FP)

lemma timpl_closure_set_Var_in_iff:
  "Var x \<in> timpl_closure_set M TI \<longleftrightarrow> Var x \<in> M"
unfolding timpl_closure_set_def by (simp add: timpl_closure_Var_in_iff[of x _ TI]) 

lemma timpl_closure_Var_inv:
  assumes "t \<in> timpl_closure (Var x) TI"
  shows "t = Var x"
using assms
proof (induction rule: timpl_closure.induct)
  case (TI u a b s) thus ?case using term_variants_pred_inv_Var by fast
qed simp

lemma timpls_Un_mono: "mono (\<lambda>X. FP \<union> (\<Union>x \<in> X. \<Union>(a,b) \<in> TI. set \<langle>a --\<guillemotright> b\<rangle>\<langle>x\<rangle>))"
by (auto intro!: monoI)

lemma timpl_closure_set_lfp:
  fixes M TI
  defines "f \<equiv> \<lambda>X. M \<union> (\<Union>x \<in> X. \<Union>(a,b) \<in> TI. set \<langle>a --\<guillemotright> b\<rangle>\<langle>x\<rangle>)"
  shows "lfp f = timpl_closure_set M TI"
proof
  note 0 = timpls_Un_mono[of M TI, unfolded f_def[symmetric]]

  let ?N = "timpl_closure_set M TI"

  show "lfp f \<subseteq> ?N"
  proof (induction rule: lfp_induct)
    case 2 thus ?case
    proof
      fix t assume "t \<in> f (lfp f \<inter> ?N)"
      hence "t \<in> M \<or> t \<in> (\<Union>x \<in> ?N. \<Union>(a,b) \<in> TI. set \<langle>a --\<guillemotright> b\<rangle>\<langle>x\<rangle>)" (is "?A \<or> ?B")
        unfolding f_def by blast
      thus "t \<in> ?N"
      proof
        assume ?B
        then obtain s a b where s: "s \<in> ?N" "(a,b) \<in> TI" "t \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>s\<rangle>" by moura
        thus ?thesis 
          using term_variants_pred_iff_in_term_variants[of "(\<lambda>_. [])(Abs a := [Abs b])" s]
          unfolding timpl_closure_set_def timpl_apply_term_def
          by (auto intro: timpl_closure.intros)
      qed (auto simp add: timpl_closure_set_def intro: timpl_closure.intros)
    qed
  qed (rule 0)

  have "t \<in> lfp f" when t: "t \<in> timpl_closure s TI" and s: "s \<in> M" for t s
    using t
  proof (induction t rule: timpl_closure.induct)
    case (TI u a b v) thus ?case 
      using term_variants_pred_iff_in_term_variants[of "(\<lambda>_. [])(Abs a := [Abs b])"]
            lfp_fixpoint[OF 0]
      unfolding timpl_apply_term_def f_def by fastforce
  qed (use s lfp_fixpoint[OF 0] f_def in blast)
  thus "?N \<subseteq> lfp f" unfolding timpl_closure_set_def by blast
qed

lemma timpl_closure_set_supset:
  assumes "\<forall>t \<in> FP. t \<in> closure"
  and "\<forall>t \<in> closure. \<forall>(a,b) \<in> TI. \<forall>s \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>t\<rangle>. s \<in> closure"
  shows "timpl_closure_set FP TI \<subseteq> closure"
proof -
  have "t \<in> closure" when t: "t \<in> timpl_closure s TI" and s: "s \<in> FP" for t s
    using t
  proof (induction rule: timpl_closure.induct)
    case FP thus ?case using s assms(1) by blast
  next
    case (TI u a b s') thus ?case
      using assms(2) term_variants_pred_iff_in_term_variants[of "(\<lambda>_. [])(Abs a := [Abs b])"]
      unfolding timpl_apply_term_def by fastforce
  qed
  thus ?thesis unfolding timpl_closure_set_def by blast
qed

lemma timpl_closure_set_supset':
  assumes "\<forall>t \<in> FP. \<forall>(a,b) \<in> TI. \<forall>s \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>t\<rangle>. s \<in> FP"
  shows "timpl_closure_set FP TI \<subseteq> FP"
using timpl_closure_set_supset[OF _ assms] by blast

lemma timpl_closure'_param:
  assumes "(t,s) \<in> timpl_closure' c"
    and fg: "f = g \<or> (\<exists>a b. (a,b) \<in> c \<and> f = Abs a \<and> g = Abs b)"
  shows "(Fun f (S@t#T), Fun g (S@s#T)) \<in> timpl_closure' c"
using assms(1) unfolding timpl_closure'_def
proof (induction rule: rtrancl_induct)
  case base thus ?case
  proof (cases "f = g")
    case False
    then obtain a b where ab: "(a,b) \<in> c" "f = Abs a" "g = Abs b"
      using fg by moura
    show ?thesis
      using term_variants_pred_param[OF term_variants_pred_refl[of "(\<lambda>_. [])(Abs a := [Abs b])" t]]
            timpl_closure'_step.intros[OF ab(1)] ab(2,3)
      by fastforce
  qed simp
next
  case (step u s)
  obtain a b where ab: "(a,b) \<in> c" "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs b])) u s"
    using timpl_closure'_step_inv[OF step.hyps(2)] by blast
  have "(Fun g (S@u#T), Fun g (S@s#T)) \<in> timpl_closure'_step c"
      using ab(1) term_variants_pred_param[OF ab(2), of g g S T]
      by (auto simp add: timpl_closure'_def intro: timpl_closure'_step.intros)
  thus ?case using rtrancl_into_rtrancl[OF step.IH] fg by blast
qed

lemma timpl_closure'_param':
  assumes "(t,s) \<in> timpl_closure' c"
  shows "(Fun f (S@t#T), Fun f (S@s#T)) \<in> timpl_closure' c"
using timpl_closure'_param[OF assms] by simp

lemma timpl_closure_FunI:
  assumes IH: "\<And>i. i < length T \<Longrightarrow> (T ! i, S ! i) \<in> timpl_closure' c"
    and len: "length T = length S"
    and fg: "f = g \<or> (\<exists>a b. (a,b) \<in> c\<^sup>+ \<and> f = Abs a \<and> g = Abs b)"
  shows "(Fun f T, Fun g S) \<in> timpl_closure' c"
proof -
  have aux: "(Fun f T, Fun g (take n S@drop n T)) \<in> timpl_closure' c"
    when "n \<le> length T" for n
    using that
  proof (induction n)
    case 0
    have "(T ! n, T ! n) \<in> timpl_closure' c" when n: "n < length T" for n
      using n unfolding timpl_closure'_def by simp
    hence "(Fun f T, Fun g T) \<in> timpl_closure' c"
    proof (cases "f = g")
      case False
      then obtain a b where ab: "(a, b) \<in> c\<^sup>+" "f = Abs a" "g = Abs b"
        using fg by moura
      show ?thesis
        using timpl_closure'_step.intros[OF ab(1), of "Fun f T" "Fun g T"] ab(2,3)
              term_variants_P[OF _ term_variants_pred_refl[of "(\<lambda>_. [])(Abs a := [Abs b])"],
                              of T g f]
              timpl_closure'_timpls_trancl_eq
        unfolding timpl_closure'_def
        by (metis fun_upd_same list.set_intros(1) r_into_rtrancl)
    qed (simp add: timpl_closure'_def)
    thus ?case by simp
  next
    case (Suc n)
    hence IH': "(Fun f T, Fun g (take n S@drop n T)) \<in> timpl_closure' c"
      and n: "n < length T" "n < length S"
      by (simp_all add: len)

    obtain T1 T2 where T: "T = T1@T ! n#T2" "length T1 = n"
      using length_prefix_ex'[OF n(1)] by auto

    obtain S1 S2 where S: "S = S1@S ! n#S2" "length S1 = n"
      using length_prefix_ex'[OF n(2)] by auto

    have "take n S@drop n T = S1@T ! n#T2" "take (Suc n) S@drop (Suc n) T = S1@S ! n#T2"
      using n T S append_eq_conv_conj
      by (metis, metis (no_types, hide_lams) Cons_nth_drop_Suc append.assoc append_Cons
                                             append_Nil take_Suc_conv_app_nth) 
    moreover have "(T ! n, S ! n) \<in> timpl_closure' c" using IH Suc.prems by simp
    ultimately show ?case
      using timpl_closure'_param IH'(1)
      by (metis (no_types, lifting) timpl_closure'_def rtrancl_trans)
  qed

  show ?thesis using aux[of "length T"] len by simp
qed

lemma timpl_closure_FunI':
  assumes IH: "\<And>i. i < length T \<Longrightarrow> (T ! i, S ! i) \<in> timpl_closure' c"
    and len: "length T = length S"
  shows "(Fun f T, Fun f S) \<in> timpl_closure' c"
using timpl_closure_FunI[OF IH len] by simp

lemma timpl_closure_FunI2:
  fixes f g::"('a, 'b, 'c) prot_fun"
  assumes IH: "\<And>i. i < length T \<Longrightarrow> \<exists>u. (T!i, u) \<in> timpl_closure' c \<and> (S!i, u) \<in> timpl_closure' c"
    and len: "length T = length S"
    and fg: "f = g \<or> (\<exists>a b d. (a, d) \<in> c\<^sup>+ \<and> (b, d) \<in> c\<^sup>+ \<and> f = Abs a \<and> g = Abs b)"
  shows "\<exists>h U. (Fun f T, Fun h U) \<in> timpl_closure' c \<and> (Fun g S, Fun h U) \<in> timpl_closure' c"
proof -
  let ?P = "\<lambda>i u. (T ! i, u) \<in> timpl_closure' c \<and> (S ! i, u) \<in> timpl_closure' c"

  define U where "U \<equiv> map (\<lambda>i. SOME u. ?P i u) [0..<length T]"

  have U1: "length U = length T"
    unfolding U_def by auto

  have U2: "(T ! i, U ! i) \<in> timpl_closure' c \<and> (S ! i, U ! i) \<in> timpl_closure' c"
    when i: "i < length U" for i
    using i someI_ex[of "?P i"] IH[of i] U1 len
    unfolding U_def by simp

  show ?thesis
  proof (cases "f = g")
    case False
    then obtain a b d where abd: "(a, d) \<in> c\<^sup>+" "(b, d) \<in> c\<^sup>+" "f = Abs a" "g = Abs b"
      using fg by moura

    define h::"('a, 'b, 'c) prot_fun" where "h = Abs d"

    have "f = h \<or> (\<exists>a b. (a, b) \<in> c\<^sup>+ \<and> f = Abs a \<and> h = Abs b)"
         "g = h \<or> (\<exists>a b. (a, b) \<in> c\<^sup>+ \<and> g = Abs a \<and> h = Abs b)"
      using abd unfolding h_def by blast+
    thus ?thesis by (metis timpl_closure_FunI len U1 U2)
  qed (metis timpl_closure_FunI' len U1 U2)
qed

lemma timpl_closure_FunI3:
  fixes f g::"('a, 'b, 'c) prot_fun"
  assumes IH: "\<And>i. i < length T \<Longrightarrow> \<exists>u. (T!i, u) \<in> timpl_closure' c \<and> (S!i, u) \<in> timpl_closure' c"
    and len: "length T = length S"
    and fg: "f = g \<or> (\<exists>a b d. (a, d) \<in> c \<and> (b, d) \<in> c \<and> f = Abs a \<and> g = Abs b)"
  shows "\<exists>h U. (Fun f T, Fun h U) \<in> timpl_closure' c \<and> (Fun g S, Fun h U) \<in> timpl_closure' c"
using timpl_closure_FunI2[OF IH len] fg unfolding timpl_closure'_timpls_trancl_eq by blast

lemma timpl_closure_fv_eq:
  assumes "s \<in> timpl_closure t T"
  shows "fv s = fv t"
using assms
by (induct rule: timpl_closure.induct)
   (metis, metis term_variants_pred_fv_eq)

lemma (in stateful_protocol_model) timpl_closure_subst:
  assumes t: "wf\<^sub>t\<^sub>r\<^sub>m t" "\<forall>x \<in> fv t. \<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a)"
    and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
  shows "timpl_closure (t \<cdot> \<delta>) T = timpl_closure t T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
proof
  have "s \<in> timpl_closure t T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
    when "s \<in> timpl_closure (t \<cdot> \<delta>) T" for s
    using that
  proof (induction s rule: timpl_closure.induct)
    case FP thus ?case using timpl_closure.FP[of t T] by simp
  next
    case (TI u a b s)
    then obtain u' where u': "u' \<in> timpl_closure t T" "u = u' \<cdot> \<delta>" by moura
    
    have u'_fv: "\<forall>x \<in> fv u'. \<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a)"
      using timpl_closure_fv_eq[OF u'(1)] t(2) by simp
    hence u_fv: "\<forall>x \<in> fv u. \<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a)"
      using u'(2) wt_subst_trm''[OF \<delta>(1)] wt_subst_const_fv_type_eq[OF _ \<delta>(1,2), of u']
      by fastforce

    have "\<forall>x \<in> fv u' \<union> fv s. (\<exists>y. \<delta> x = Var y) \<or> (\<exists>f. \<delta> x = Fun f [] \<and> Abs a \<noteq> f)"
    proof (intro ballI)
      fix x assume x: "x \<in> fv u' \<union> fv s"
      then obtain c where c: "\<Gamma>\<^sub>v x = TAtom (Atom c)"
        using u'_fv u_fv term_variants_pred_fv_eq[OF TI.hyps(3)]
        by blast

      show "(\<exists>y. \<delta> x = Var y) \<or> (\<exists>f. \<delta> x = Fun f [] \<and> Abs a \<noteq> f)"
      proof (cases "\<delta> x")
        case (Fun f T)
        hence **: "\<Gamma> (Fun f T) = TAtom (Atom c)" and "wf\<^sub>t\<^sub>r\<^sub>m (Fun f T)"
          using c wt_subst_trm''[OF \<delta>(1), of "Var x"] \<delta>(2)
          by fastforce+
        hence "\<delta> x = Fun f []" using Fun const_type_inv_wf by metis
        thus ?thesis using ** by force
      qed metis
    qed
    hence *: "\<forall>x \<in> fv u' \<union> fv s.
                (\<exists>y. \<delta> x = Var y) \<or> (\<exists>f. \<delta> x = Fun f [] \<and> ((\<lambda>_. [])(Abs a := [Abs b])) f = [])"
      by fastforce

    obtain s' where s': "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs b])) u' s'" "s = s' \<cdot> \<delta>"
      using term_variants_pred_subst'[OF _ *] u'(2) TI.hyps(3)
      by blast

    show ?case using timpl_closure.TI[OF u'(1) TI.hyps(2) s'(1)] s'(2) by blast
  qed
  thus "timpl_closure (t \<cdot> \<delta>) T \<subseteq> timpl_closure t T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>" by fast

  have "s \<in> timpl_closure (t \<cdot> \<delta>) T"
    when s: "s \<in> timpl_closure t T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>" for s
  proof -
    obtain s' where s': "s' \<in> timpl_closure t T" "s = s' \<cdot> \<delta>" using s by moura
    have "s' \<cdot> \<delta> \<in> timpl_closure (t \<cdot> \<delta>) T" using s'(1)
    proof (induction s' rule: timpl_closure.induct)
      case FP thus ?case using timpl_closure.FP[of "t \<cdot> \<delta>" T] by simp
    next
      case (TI u' a b s') show ?case
        using timpl_closure.TI[OF TI.IH TI.hyps(2)]
              term_variants_pred_subst[OF TI.hyps(3)]
        by blast
    qed
    thus ?thesis using s'(2) by metis
  qed
  thus "timpl_closure t T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> \<subseteq> timpl_closure (t \<cdot> \<delta>) T" by fast
qed

lemma (in stateful_protocol_model) timpl_closure_subst_subset:
  assumes t: "t \<in> M"
    and M: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M" "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M. \<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a)"
    and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)" "ground (subst_range \<delta>)" "subst_domain \<delta> \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M"
    and M_supset: "timpl_closure t T \<subseteq> M"
  shows "timpl_closure (t \<cdot> \<delta>) T \<subseteq> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
proof -
  have t': "wf\<^sub>t\<^sub>r\<^sub>m t" "\<forall>x \<in> fv t. \<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a)" using t M by auto
  show ?thesis using timpl_closure_subst[OF t' \<delta>(1,2), of T] M_supset by blast
qed

lemma (in stateful_protocol_model) timpl_closure_set_subst_subset:
  assumes M: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M" "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M. \<exists>a. \<Gamma>\<^sub>v x = TAtom (Atom a)"
    and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)" "ground (subst_range \<delta>)" "subst_domain \<delta> \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M"
    and M_supset: "timpl_closure_set M T \<subseteq> M"
  shows "timpl_closure_set (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>) T \<subseteq> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
using timpl_closure_subst_subset[OF _ M \<delta>, of _ T] M_supset
      timpl_closure_set_is_timpl_closure_union[of "M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>" T]
      timpl_closure_set_is_timpl_closure_union[of M T]
by auto

lemma timpl_closure_set_Union:
  "timpl_closure_set (\<Union>Ms) T = (\<Union>M \<in> Ms. timpl_closure_set M T)"
using timpl_closure_set_is_timpl_closure_union[of "\<Union>Ms" T]
      timpl_closure_set_is_timpl_closure_union[of _ T]
by force

lemma timpl_closure_set_Union_subst_set:
  assumes "s \<in> timpl_closure_set (\<Union>{M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> | \<delta>. P \<delta>}) T"
  shows "\<exists>\<delta>. P \<delta> \<and> s \<in> timpl_closure_set (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>) T"
using assms timpl_closure_set_is_timpl_closure_union[of "(\<Union>{M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> | \<delta>. P \<delta>})" T]
      timpl_closure_set_is_timpl_closure_union[of _ T]
by blast

lemma timpl_closure_set_Union_subst_singleton:
  assumes "s \<in> timpl_closure_set {t \<cdot> \<delta> | \<delta>. P \<delta>} T"
  shows "\<exists>\<delta>. P \<delta> \<and> s \<in> timpl_closure_set {t \<cdot> \<delta>} T"
using assms timpl_closure_set_is_timpl_closure_union[of "{t \<cdot> \<delta> |\<delta>. P \<delta>}" T]
      timpl_closureton_is_timpl_closure[of _ T]
by fast

lemma timpl_closure'_inv:
  assumes "(s, t) \<in> timpl_closure' TI"
  shows "(\<exists>x. s = Var x \<and> t = Var x) \<or> (\<exists>f g S T. s = Fun f S \<and> t = Fun g T \<and> length S = length T)"
using assms unfolding timpl_closure'_def
proof (induction rule: rtrancl_induct)
  case base thus ?case by (cases s) auto
next
  case (step t u)
  obtain a b where ab: "(a, b) \<in> TI" "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs b])) t u"
    using timpl_closure'_step_inv[OF step.hyps(2)] by blast
  show ?case using step.IH
  proof
    assume "\<exists>x. s = Var x \<and> t = Var x"
    thus ?case using step.hyps(2) term_variants_pred_inv_Var ab by fastforce
  next
    assume "\<exists>f g S T. s = Fun f S \<and> t = Fun g T \<and> length S = length T"
    then obtain f g S T where st: "s = Fun f S" "t = Fun g T" "length S = length T" by moura
    thus ?case
      using ab step.hyps(2) term_variants_pred_inv'[of "(\<lambda>_. [])(Abs a := [Abs b])" g T u]
      by auto
  qed
qed

lemma timpl_closure'_inv':
  assumes "(s, t) \<in> timpl_closure' TI"
  shows "(\<exists>x. s = Var x \<and> t = Var x) \<or>
         (\<exists>f g S T. s = Fun f S \<and> t = Fun g T \<and> length S = length T \<and>
                    (\<forall>i < length T. (S ! i, T ! i) \<in> timpl_closure' TI) \<and>
                    (f \<noteq> g \<longrightarrow> is_Abs f \<and> is_Abs g \<and> (the_Abs f, the_Abs g) \<in> TI\<^sup>+))"
    (is "?A s t \<or> ?B s t (timpl_closure' TI)")
using assms unfolding timpl_closure'_def
proof (induction rule: rtrancl_induct)
  case base thus ?case by (cases s) auto
next
  case (step t u)
  obtain a b where ab: "(a, b) \<in> TI" "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs b])) t u"
    using timpl_closure'_step_inv[OF step.hyps(2)] by blast
  show ?case using step.IH
  proof
    assume "?A s t"
    thus ?case using step.hyps(2) term_variants_pred_inv_Var ab by fastforce
  next
    assume "?B s t ((timpl_closure'_step TI)\<^sup>*)"
    then obtain f g S T where st:
        "s = Fun f S" "t = Fun g T" "length S = length T"
        "\<And>i. i < length T \<Longrightarrow> (S ! i, T ! i) \<in> (timpl_closure'_step TI)\<^sup>*"
        "f \<noteq> g \<Longrightarrow> is_Abs f \<and> is_Abs g \<and> (the_Abs f, the_Abs g) \<in> TI\<^sup>+"
      by moura
    obtain h U where u:
        "u = Fun h U" "length T = length U"
        "\<And>i. i < length T \<Longrightarrow> term_variants_pred ((\<lambda>_. [])(Abs a := [Abs b])) (T ! i) (U ! i)"
        "g \<noteq> h \<Longrightarrow> is_Abs g \<and> is_Abs h \<and> (the_Abs g, the_Abs h) \<in> TI\<^sup>+"
      using ab(2) st(2) r_into_trancl[OF ab(1)]
            term_variants_pred_inv'(1,2,3,4)[of "(\<lambda>_. [])(Abs a := [Abs b])" g T u]
            term_variants_pred_inv'(5)[of "(\<lambda>_. [])(Abs a := [Abs b])" g T u "Abs a" "Abs b"]
      unfolding is_Abs_def the_Abs_def by force

    have "(S ! i, U ! i) \<in> (timpl_closure'_step TI)\<^sup>*" when i: "i < length U" for i
      using u(2) i rtrancl.rtrancl_into_rtrancl[OF
              st(4)[of i] timpl_closure'_step.intros[OF ab(1) u(3)[of i]]]
      by argo
    moreover have "length S = length U" using st u by argo
    moreover have "is_Abs f \<and> is_Abs h \<and> (the_Abs f, the_Abs h) \<in> TI\<^sup>+" when fh: "f \<noteq> h"
      using fh st u by fastforce
    ultimately show ?case using st(1) u(1) by blast
  qed
qed

lemma timpl_closure'_inv'':
  assumes "(Fun f S, Fun g T) \<in> timpl_closure' TI"
  shows "length S = length T"
    and "\<And>i. i < length T \<Longrightarrow> (S ! i, T ! i) \<in> timpl_closure' TI"
    and "f \<noteq> g \<Longrightarrow> is_Abs f \<and> is_Abs g \<and> (the_Abs f, the_Abs g) \<in> TI\<^sup>+"
using assms timpl_closure'_inv' by auto

lemma timpl_closure_Fun_inv:
  assumes "s \<in> timpl_closure (Fun f T) TI"
  shows "\<exists>g S. s = Fun g S"
using assms timpl_closure_is_timpl_closure' timpl_closure'_inv
by fastforce

lemma timpl_closure_Fun_inv':
  assumes "Fun g S \<in> timpl_closure (Fun f T) TI"
  shows "length S = length T"
    and "\<And>i. i < length S \<Longrightarrow> S ! i \<in> timpl_closure (T ! i) TI"
    and "f \<noteq> g \<Longrightarrow> is_Abs f \<and> is_Abs g \<and> (the_Abs f, the_Abs g) \<in> TI\<^sup>+"
using assms timpl_closure_is_timpl_closure'
by (metis timpl_closure'_inv''(1), metis timpl_closure'_inv''(2), metis timpl_closure'_inv''(3))

lemma timpl_closure_Fun_not_Var[simp]:
  "Fun f T \<notin> timpl_closure (Var x) TI"
using timpl_closure_Var_inv by fast

lemma timpl_closure_Var_not_Fun[simp]:
  "Var x \<notin> timpl_closure (Fun f T) TI"
using timpl_closure_Fun_inv by fast

lemma (in stateful_protocol_model) timpl_closure_wf_trms:
  assumes m: "wf\<^sub>t\<^sub>r\<^sub>m m"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (timpl_closure m TI)"
proof
  fix t assume "t \<in> timpl_closure m TI"
  thus "wf\<^sub>t\<^sub>r\<^sub>m t"
  proof (induction t rule: timpl_closure.induct)
    case TI thus ?case using term_variants_pred_wf_trms by force
  qed (rule m)
qed

lemma (in stateful_protocol_model) timpl_closure_set_wf_trms:
  assumes M: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (timpl_closure_set M TI)"
proof
  fix t assume "t \<in> timpl_closure_set M TI"
  then obtain m where "t \<in> timpl_closure m TI" "m \<in> M" "wf\<^sub>t\<^sub>r\<^sub>m m"
    using M timpl_closure_set_is_timpl_closure_union by blast
  thus "wf\<^sub>t\<^sub>r\<^sub>m t" using timpl_closure_wf_trms by blast
qed

lemma timpl_closure_Fu_inv:
  assumes "t \<in> timpl_closure (Fun (Fu f) T) TI"
  shows "\<exists>S. length S = length T \<and> t = Fun (Fu f) S"
using assms
proof (induction t rule: timpl_closure.induct)
  case (TI u a b s)
  then obtain U where U: "length U = length T" "u = Fun (Fu f) U"
    by moura
  hence *: "term_variants_pred ((\<lambda>_. [])(Abs a := [Abs b])) (Fun (Fu f) U) s"
    using TI.hyps(3) by meson

  show ?case
    using term_variants_pred_inv'(1,2,4)[OF *] U
    by force
qed simp

lemma timpl_closure_Fu_inv':
  assumes "Fun (Fu f) T \<in> timpl_closure t TI"
  shows "\<exists>S. length S = length T \<and> t = Fun (Fu f) S"
using assms
proof (induction "Fun (Fu f) T" arbitrary: T rule: timpl_closure.induct)
  case (TI u a b)
  obtain g U where U:
      "u = Fun g U" "length U = length T"
      "Fu f \<noteq> g \<Longrightarrow> Abs a = g \<and> Fu f = Abs b"
    using term_variants_pred_inv''[OF TI.hyps(4)] by fastforce

  have g: "g = Fu f" using U(3) by blast
  
  show ?case using TI.hyps(2)[OF U(1)[unfolded g]] U(2) by auto
qed simp

lemma timpl_closure_no_Abs_eq:
  assumes "t \<in> timpl_closure s TI"
    and "\<forall>f \<in> funs_term t. \<not>is_Abs f"
  shows "t = s"
using assms
proof (induction t rule: timpl_closure.induct)
  case (TI t a b s) thus ?case
    using term_variants_pred_eq_case_Abs[of a b t s]
    unfolding timpl_apply_term_def term_variants_pred_iff_in_term_variants[symmetric]
    by metis
qed simp

lemma timpl_closure_set_no_Abs_in_set:
  assumes "t \<in> timpl_closure_set FP TI"
    and "\<forall>f \<in> funs_term t. \<not>is_Abs f"
  shows "t \<in> FP"
using assms timpl_closure_no_Abs_eq unfolding timpl_closure_set_def by blast

lemma timpl_closure_funs_term_subset:
  "\<Union>(funs_term ` (timpl_closure t TI)) \<subseteq> funs_term t \<union> Abs ` snd ` TI"
  (is "?A \<subseteq> ?B \<union> ?C")
proof
  fix f assume "f \<in> ?A"
  then obtain s where "s \<in> timpl_closure t TI" "f \<in> funs_term s" by moura
  thus "f \<in> ?B \<union> ?C"
  proof (induction s rule: timpl_closure.induct)
    case (TI u a b s)
    have "Abs b \<in> Abs ` snd ` TI" using TI.hyps(2) by force
    thus ?case using term_variants_pred_funs_term[OF TI.hyps(3) TI.prems] TI.IH by force
  qed blast
qed

lemma timpl_closure_set_funs_term_subset:
  "\<Union>(funs_term ` (timpl_closure_set FP TI)) \<subseteq> \<Union>(funs_term ` FP) \<union> Abs ` snd ` TI"
using timpl_closure_funs_term_subset[of _ TI]
      timpl_closure_set_is_timpl_closure_union[of FP TI]
by auto

lemma funs_term_OCC_TI_subset:
  defines "absc \<equiv> \<lambda>a. Fun (Abs a) []"
  assumes OCC1: "\<forall>t \<in> FP. \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` OCC"
    and OCC2: "snd ` TI \<subseteq> OCC"
  shows "\<forall>t \<in> timpl_closure_set FP TI. \<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> f \<in> Abs ` OCC" (is ?A)
    and "\<forall>t \<in> absc ` OCC. \<forall>(a,b) \<in> TI. \<forall>s \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>t\<rangle>. s \<in> absc ` OCC" (is ?B)
proof -
  let ?F = "\<Union>(funs_term ` FP)"
  let ?G = "Abs ` snd ` TI"

  show ?A
  proof (intro ballI impI)
    fix t f assume t: "t \<in> timpl_closure_set FP TI" and f: "f \<in> funs_term t" "is_Abs f"
    hence "f \<in> ?F \<or> f \<in> ?G" using timpl_closure_set_funs_term_subset[of FP TI] by auto
    thus "f \<in> Abs ` OCC"
    proof
      assume "f \<in> ?F" thus ?thesis using OCC1 f(2) by fast
    next
      assume "f \<in> ?G" thus ?thesis using OCC2 by auto
    qed
  qed

  { fix s t a b
    assume t: "t \<in> absc ` OCC"
      and ab: "(a, b) \<in> TI"
      and s: "s \<in> set \<langle>a --\<guillemotright> b\<rangle>\<langle>t\<rangle>"
    obtain c where c: "t = absc c" "c \<in> OCC" using t by moura
    hence "s = absc b \<or> s = absc c"
      using ab s timpl_apply_const'[of c a b] unfolding absc_def by auto
    moreover have "b \<in> OCC" using ab OCC2 by auto
    ultimately have "s \<in> absc ` OCC" using c(2) by blast
  } thus ?B by blast
qed

lemma (in stateful_protocol_model) intruder_synth_timpl_closure_set:
  fixes M::"('fun,'atom,'sets) prot_terms" and t::"('fun,'atom,'sets) prot_term"
  assumes "M \<turnstile>\<^sub>c t"
    and "s \<in> timpl_closure t TI"
  shows "timpl_closure_set M TI \<turnstile>\<^sub>c s"
using assms
proof (induction t arbitrary: s rule: intruder_synth_induct)
  case (AxiomC t)
  hence "s \<in> timpl_closure_set M TI"
    using timpl_closure_set_is_timpl_closure_union[of M TI]
    by blast
  thus ?case by simp
next
  case (ComposeC T f)
  obtain g S where s: "s = Fun g S"
    using timpl_closure_Fun_inv[OF ComposeC.prems] by moura
  hence s':
      "f = g" "length S = length T"
      "\<And>i. i < length S \<Longrightarrow> S ! i \<in> timpl_closure (T ! i) TI"
    using timpl_closure_Fun_inv'[of g S f T TI] ComposeC.prems ComposeC.hyps(2)
    unfolding is_Abs_def by fastforce+
  
  have "timpl_closure_set M TI \<turnstile>\<^sub>c u" when u: "u \<in> set S" for u
    using ComposeC.IH u s'(2,3) in_set_conv_nth[of _ T] in_set_conv_nth[of u S] by auto
  thus ?case
    using s s'(1,2) ComposeC.hyps(1,2) intruder_synth.ComposeC[of S g "timpl_closure_set M TI"]
    by argo
qed

lemma (in stateful_protocol_model) intruder_synth_timpl_closure':
  fixes M::"('fun,'atom,'sets) prot_terms" and t::"('fun,'atom,'sets) prot_term"
  assumes "timpl_closure_set M TI \<turnstile>\<^sub>c t"
    and "s \<in> timpl_closure t TI"
  shows "timpl_closure_set M TI \<turnstile>\<^sub>c s"
by (metis intruder_synth_timpl_closure_set[OF assms] timpl_closure_set_idem)

lemma timpl_closure_set_absc_subset_in:
  defines "absc \<equiv> \<lambda>a. Fun (Abs a) []"
  assumes A: "timpl_closure_set (absc ` A) TI \<subseteq> absc ` A"
    and a: "a \<in> A" "(a,b) \<in> TI\<^sup>+"
  shows "b \<in> A"
proof -
  have "timpl_closure (absc a) (TI\<^sup>+) \<subseteq> absc ` A"
    using a(1) A timpl_closure_timpls_trancl_eq
    unfolding timpl_closure_set_def by fast
  thus ?thesis
    using timpl_closure.TI[OF timpl_closure.FP[of "absc a"] a(2), of "absc b"]
          term_variants_P[of "[]" "[]" "(\<lambda>_. [])(Abs a := [Abs b])" "Abs b" "Abs a"]
    unfolding absc_def by auto
qed


subsection \<open>Composition-only Intruder Deduction Modulo Term Implication Closure of the Intruder Knowledge\<close>
context stateful_protocol_model
begin

fun in_trancl where
  "in_trancl TI a b = (
    if (a,b) \<in> set TI then True
    else list_ex (\<lambda>(c,d). c = a \<and> in_trancl (removeAll (c,d) TI) d b) TI)"

definition in_rtrancl where
  "in_rtrancl TI a b \<equiv> a = b \<or> in_trancl TI a b"

declare in_trancl.simps[simp del]

fun timpls_transformable_to where
  "timpls_transformable_to TI (Var x) (Var y) = (x = y)"
| "timpls_transformable_to TI (Fun f T) (Fun g S) = (
    (f = g \<or> (is_Abs f \<and> is_Abs g \<and> (the_Abs f, the_Abs g) \<in> set TI)) \<and>
    list_all2 (timpls_transformable_to TI) T S)"
| "timpls_transformable_to _ _ _ = False"

fun timpls_transformable_to' where
  "timpls_transformable_to' TI (Var x) (Var y) = (x = y)"
| "timpls_transformable_to' TI (Fun f T) (Fun g S) = (
    (f = g \<or> (is_Abs f \<and> is_Abs g \<and> in_trancl TI (the_Abs f) (the_Abs g))) \<and>
    list_all2 (timpls_transformable_to' TI) T S)"
| "timpls_transformable_to' _ _ _ = False"

fun equal_mod_timpls where
  "equal_mod_timpls TI (Var x) (Var y) = (x = y)"
| "equal_mod_timpls TI (Fun f T) (Fun g S) = (
    (f = g \<or> (is_Abs f \<and> is_Abs g \<and>
                ((the_Abs f, the_Abs g) \<in> set TI \<or>
                 (the_Abs g, the_Abs f) \<in> set TI \<or>
                 (\<exists>ti \<in> set TI. (the_Abs f, snd ti) \<in> set TI \<and> (the_Abs g, snd ti) \<in> set TI)))) \<and>
    list_all2 (equal_mod_timpls TI) T S)"
| "equal_mod_timpls _ _ _ = False"

fun intruder_synth_mod_timpls where
  "intruder_synth_mod_timpls M TI (Var x) = List.member M (Var x)"
| "intruder_synth_mod_timpls M TI (Fun f T) = (
    (list_ex (\<lambda>t. timpls_transformable_to TI t (Fun f T)) M) \<or>
    (public f \<and> length T = arity f \<and> list_all (intruder_synth_mod_timpls M TI) T))"

fun intruder_synth_mod_timpls' where
  "intruder_synth_mod_timpls' M TI (Var x) = List.member M (Var x)"
| "intruder_synth_mod_timpls' M TI (Fun f T) = (
    (list_ex (\<lambda>t. timpls_transformable_to' TI t (Fun f T)) M) \<or>
    (public f \<and> length T = arity f \<and> list_all (intruder_synth_mod_timpls' M TI) T))"

fun intruder_synth_mod_eq_timpls where
  "intruder_synth_mod_eq_timpls M TI (Var x) = (Var x \<in> M)"
| "intruder_synth_mod_eq_timpls M TI (Fun f T) = (
    (\<exists>t \<in> M. equal_mod_timpls TI t (Fun f T)) \<or>
    (public f \<and> length T = arity f \<and> list_all (intruder_synth_mod_eq_timpls M TI) T))"

definition analyzed_closed_mod_timpls where
  "analyzed_closed_mod_timpls M TI \<equiv>
    let f = list_all (intruder_synth_mod_timpls M TI);
        g = \<lambda>t. if f (fst (Ana t)) then f (snd (Ana t))
                else \<forall>s \<in> comp_timpl_closure {t} (set TI). case Ana s of (K,R) \<Rightarrow> f K \<longrightarrow> f R
    in list_all g M"

definition analyzed_closed_mod_timpls' where
  "analyzed_closed_mod_timpls' M TI \<equiv>
    let f = list_all (intruder_synth_mod_timpls' M TI);
        g = \<lambda>t. if f (fst (Ana t)) then f (snd (Ana t))
                else \<forall>s \<in> comp_timpl_closure {t} (set TI). case Ana s of (K,R) \<Rightarrow> f K \<longrightarrow> f R
    in list_all g M"
(* Alternative definition (allows for computing the closures beforehand which may be useful) *)
definition analyzed_closed_mod_timpls_alt where
  "analyzed_closed_mod_timpls_alt M TI timpl_cl_witness \<equiv>
    let f = \<lambda>R. \<forall>r \<in> set R. intruder_synth_mod_timpls M TI r;
        N = {t \<in> set M. f (fst (Ana t))};
        N' = set M - N
    in (\<forall>t \<in> N. f (snd (Ana t))) \<and>
       (N' \<noteq> {} \<longrightarrow> (N' \<union> (\<Union>x\<in>timpl_cl_witness. \<Union>(a,b)\<in>set TI. set \<langle>a --\<guillemotright> b\<rangle>\<langle>x\<rangle>) \<subseteq> timpl_cl_witness)) \<and>
       (\<forall>s \<in> timpl_cl_witness. case Ana s of (K,R) \<Rightarrow> f K \<longrightarrow> f R)"

lemma in_trancl_closure_iff_in_trancl_fun:
  "(a,b) \<in> (set TI)\<^sup>+ \<longleftrightarrow> in_trancl TI a b" (is "?A TI a b \<longleftrightarrow> ?B TI a b")
proof
  show "?A TI a b \<Longrightarrow> ?B TI a b"
  proof (induction rule: trancl_induct)
    case (step c d)
    show ?case using step.IH step.hyps(2)
    proof (induction TI a c rule: in_trancl.induct)
      case (1 TI a b) thus ?case using in_trancl.simps
        by (smt Bex_set case_prodE case_prodI member_remove prod.sel(2) remove_code(1))
    qed
  qed (metis in_trancl.simps)

  show "?B TI a b \<Longrightarrow> ?A TI a b"
  proof (induction TI a b rule: in_trancl.induct)
    case (1 TI a b)
    let ?P = "\<lambda>TI a b c d. in_trancl (List.removeAll (c,d) TI) d b"
    have *: "\<exists>(c,d) \<in> set TI. c = a \<and> ?P TI a b c d" when "(a,b) \<notin> set TI"
      using that "1.prems" list_ex_iff[of _ TI] in_trancl.simps[of TI a b]
      by auto
    show ?case
    proof (cases "(a,b) \<in> set TI")
      case False
      hence "\<exists>(c,d) \<in> set TI. c = a \<and> ?P TI a b c d" using * by blast
      then obtain d where d: "(a,d) \<in> set TI" "?P TI a b a d" by blast
      have "(d,b) \<in> (set (removeAll (a,d) TI))\<^sup>+" using "1.IH"[OF False d(1)] d(2) by blast
      moreover have "set (removeAll (a,d) TI) \<subseteq> set TI" by simp
      ultimately have "(d,b) \<in> (set TI)\<^sup>+" using trancl_mono by blast
      thus ?thesis using d(1) by fastforce
    qed simp
  qed
qed

lemma in_rtrancl_closure_iff_in_rtrancl_fun:
  "(a,b) \<in> (set TI)\<^sup>* \<longleftrightarrow> in_rtrancl TI a b"
by (metis rtrancl_eq_or_trancl in_trancl_closure_iff_in_trancl_fun in_rtrancl_def)

lemma in_trancl_mono:
  assumes "set TI \<subseteq> set TI'"
    and "in_trancl TI a b"
  shows "in_trancl TI' a b"
by (metis assms in_trancl_closure_iff_in_trancl_fun trancl_mono)

lemma equal_mod_timpls_refl:
  "equal_mod_timpls TI t t"
proof (induction t)
  case (Fun f T) thus ?case
    using list_all2_conv_all_nth[of "equal_mod_timpls TI" T T] by force
qed simp

lemma equal_mod_timpls_inv_Var:
  "equal_mod_timpls TI (Var x) t \<Longrightarrow> t = Var x" (is "?A \<Longrightarrow> ?C")
  "equal_mod_timpls TI t (Var x) \<Longrightarrow> t = Var x" (is "?B \<Longrightarrow> ?C")
proof -
  show "?A \<Longrightarrow> ?C" by (cases t) auto
  show "?B \<Longrightarrow> ?C" by (cases t) auto
qed

lemma equal_mod_timpls_inv:
  assumes "equal_mod_timpls TI (Fun f T) (Fun g S)"
  shows "length T = length S"
    and "\<And>i. i < length T \<Longrightarrow> equal_mod_timpls TI (T ! i) (S ! i)"
    and "f \<noteq> g \<Longrightarrow> (is_Abs f \<and> is_Abs g \<and> (
                      (the_Abs f, the_Abs g) \<in> set TI \<or> (the_Abs g, the_Abs f) \<in> set TI \<or>
                      (\<exists>ti \<in> set TI. (the_Abs f, snd ti) \<in> set TI \<and>
                                     (the_Abs g, snd ti) \<in> set TI)))"
using assms list_all2_conv_all_nth[of "equal_mod_timpls TI" T S]
by (auto elim: equal_mod_timpls.cases)

lemma equal_mod_timpls_inv':
  assumes "equal_mod_timpls TI (Fun f T) t"
  shows "is_Fun t"
    and "length T = length (args t)"
    and "\<And>i. i < length T \<Longrightarrow> equal_mod_timpls TI (T ! i) (args t ! i)"
    and "f \<noteq> the_Fun t \<Longrightarrow> (is_Abs f \<and> is_Abs (the_Fun t) \<and> (
                      (the_Abs f, the_Abs (the_Fun t)) \<in> set TI \<or>
                      (the_Abs (the_Fun t), the_Abs f) \<in> set TI \<or>
                      (\<exists>ti \<in> set TI. (the_Abs f, snd ti) \<in> set TI \<and>
                                     (the_Abs (the_Fun t), snd ti) \<in> set TI)))"
    and "\<not>is_Abs f \<Longrightarrow> f = the_Fun t"
using assms list_all2_conv_all_nth[of "equal_mod_timpls TI" T]
by (cases t; auto)+

lemma equal_mod_timpls_if_term_variants:
  fixes s t::"(('a, 'b, 'c) prot_fun, 'd) term" and a b::"'c set"
  defines "P \<equiv> (\<lambda>_. [])(Abs a := [Abs b])"
  assumes st: "term_variants_pred P s t"
    and ab: "(a,b) \<in> set TI"
  shows "equal_mod_timpls TI s t"
using st P_def
proof (induction rule: term_variants_pred.induct)
  case (term_variants_P T S f) thus ?case
    using ab list_all2_conv_all_nth[of "equal_mod_timpls TI" T S]
          in_trancl_closure_iff_in_trancl_fun[of _ _ TI]
    by auto
next
  case (term_variants_Fun T S f) thus ?case
    using ab list_all2_conv_all_nth[of "equal_mod_timpls TI" T S]
          in_trancl_closure_iff_in_trancl_fun[of _ _ TI]
    by auto
qed simp

lemma equal_mod_timpls_mono:
  assumes "set TI \<subseteq> set TI'"
    and "equal_mod_timpls TI s t"
  shows "equal_mod_timpls TI' s t"
  using assms
proof (induction TI s t rule: equal_mod_timpls.induct)
  case (2 TI f T g S)
  have *: "f = g \<or> (is_Abs f \<and> is_Abs g \<and> ((the_Abs f, the_Abs g) \<in> set TI \<or>
                 (the_Abs g, the_Abs f) \<in> set TI \<or>
                 (\<exists>ti \<in> set TI. (the_Abs f, snd ti) \<in> set TI \<and>
                                (the_Abs g, snd ti) \<in> set TI)))"
          "list_all2 (equal_mod_timpls TI) T S"
    using "2.prems" by simp_all

  show ?case
    using "2.IH" "2.prems"(1) list.rel_mono_strong[OF *(2)] *(1) in_trancl_mono[of TI TI']
    by (metis (no_types, lifting) equal_mod_timpls.simps(2) set_rev_mp)
qed auto

lemma equal_mod_timpls_refl_minus_eq:
  "equal_mod_timpls TI s t \<longleftrightarrow> equal_mod_timpls (filter (\<lambda>(a,b). a \<noteq> b) TI) s t"
  (is "?A \<longleftrightarrow> ?B")
proof
  show ?A when ?B using that equal_mod_timpls_mono[of "filter (\<lambda>(a,b). a \<noteq> b) TI" TI] by auto

  show ?B when ?A using that
  proof (induction TI s t rule: equal_mod_timpls.induct)
    case (2 TI f T g S)
    define TI' where "TI' \<equiv> filter (\<lambda>(a,b). a \<noteq> b) TI"

    let ?P = "\<lambda>X Y. f = g \<or> (is_Abs f \<and> is_Abs g \<and> ((the_Abs f, the_Abs g) \<in> set X \<or>
                 (the_Abs g, the_Abs f) \<in> set X \<or> (\<exists>ti \<in> set Y.
                 (the_Abs f, snd ti) \<in> set X \<and> (the_Abs g, snd ti) \<in> set X)))"

    have *: "?P TI TI" "list_all2 (equal_mod_timpls TI) T S"
      using "2.prems" by simp_all

    have "?P TI' TI"
      using *(1) unfolding TI'_def is_Abs_def by auto
    hence "?P TI' TI'"
      by (metis (no_types, lifting) snd_conv)
    moreover have "list_all2 (equal_mod_timpls TI') T S"
      using *(2) "2.IH" list.rel_mono_strong unfolding TI'_def by blast
    ultimately show ?case unfolding TI'_def by force
  qed auto
qed

lemma timpls_transformable_to_refl:
  "timpls_transformable_to TI t t" (is ?A)
  "timpls_transformable_to' TI t t" (is ?B)
by (induct t) (auto simp add: list_all2_conv_all_nth)

lemma timpls_transformable_to_inv_Var:
  "timpls_transformable_to TI (Var x) t \<Longrightarrow> t = Var x" (is "?A \<Longrightarrow> ?C")
  "timpls_transformable_to TI t (Var x) \<Longrightarrow> t = Var x" (is "?B \<Longrightarrow> ?C")
  "timpls_transformable_to' TI (Var x) t \<Longrightarrow> t = Var x" (is "?A' \<Longrightarrow> ?C")
  "timpls_transformable_to' TI t (Var x) \<Longrightarrow> t = Var x" (is "?B' \<Longrightarrow> ?C")
by (cases t; auto)+

lemma timpls_transformable_to_inv:
  assumes "timpls_transformable_to TI (Fun f T) (Fun g S)"
  shows "length T = length S"
    and "\<And>i. i < length T \<Longrightarrow> timpls_transformable_to TI (T ! i) (S ! i)"
    and "f \<noteq> g \<Longrightarrow> (is_Abs f \<and> is_Abs g \<and> (the_Abs f, the_Abs g) \<in> set TI)"
using assms list_all2_conv_all_nth[of "timpls_transformable_to TI" T S] by auto

lemma timpls_transformable_to'_inv:
  assumes "timpls_transformable_to' TI (Fun f T) (Fun g S)"
  shows "length T = length S"
    and "\<And>i. i < length T \<Longrightarrow> timpls_transformable_to' TI (T ! i) (S ! i)"
    and "f \<noteq> g \<Longrightarrow> (is_Abs f \<and> is_Abs g \<and> in_trancl TI (the_Abs f) (the_Abs g))"
using assms list_all2_conv_all_nth[of "timpls_transformable_to' TI" T S] by auto

lemma timpls_transformable_to_inv':
  assumes "timpls_transformable_to TI (Fun f T) t"
  shows "is_Fun t"
    and "length T = length (args t)"
    and "\<And>i. i < length T \<Longrightarrow> timpls_transformable_to TI (T ! i) (args t ! i)"
    and "f \<noteq> the_Fun t \<Longrightarrow> (
          is_Abs f \<and> is_Abs (the_Fun t) \<and> (the_Abs f, the_Abs (the_Fun t)) \<in> set TI)"
    and "\<not>is_Abs f \<Longrightarrow> f = the_Fun t"
using assms list_all2_conv_all_nth[of "timpls_transformable_to TI" T]
by (cases t; auto)+

lemma timpls_transformable_to'_inv':
  assumes "timpls_transformable_to' TI (Fun f T) t"
  shows "is_Fun t"
    and "length T = length (args t)"
    and "\<And>i. i < length T \<Longrightarrow> timpls_transformable_to' TI (T ! i) (args t ! i)"
    and "f \<noteq> the_Fun t \<Longrightarrow> (
          is_Abs f \<and> is_Abs (the_Fun t) \<and> in_trancl TI (the_Abs f) (the_Abs (the_Fun t)))"
    and "\<not>is_Abs f \<Longrightarrow> f = the_Fun t"
using assms list_all2_conv_all_nth[of "timpls_transformable_to' TI" T]
by (cases t; auto)+

lemma timpls_transformable_to_size_eq:
  fixes s t::"(('b, 'c, 'a) prot_fun, 'd) term"
  shows "timpls_transformable_to TI s t \<Longrightarrow> size s = size t" (is "?A \<Longrightarrow> ?C")
    and "timpls_transformable_to' TI s t \<Longrightarrow> size s = size t" (is "?B \<Longrightarrow> ?C")
proof -
  have *: "size_list size T = size_list size S"
    when "length T = length S" "\<And>i. i < length T \<Longrightarrow> size (T ! i) = size (S ! i)"
    for S T::"(('b, 'c, 'a) prot_fun, 'd) term list"
    using that
  proof (induction T arbitrary: S)
    case (Cons x T')
    then obtain y S' where y: "S = y#S'" by (cases S) auto
    hence "size_list size T' = size_list size S'" "size x = size y"
      using Cons.prems Cons.IH[of S'] by force+
    thus ?case using y by simp
  qed simp

  show ?C when ?A using that
  proof (induction rule: timpls_transformable_to.induct)
    case (2 TI f T g S)
    hence "length T = length S" "\<And>i. i < length T \<Longrightarrow> size (T ! i) = size (S ! i)"
      using timpls_transformable_to_inv(1,2)[of TI f T g S] by auto
    thus ?case using *[of S T] by simp
  qed simp_all

  show ?C when ?B using that
  proof (induction rule: timpls_transformable_to.induct)
    case (2 TI f T g S)
    hence "length T = length S" "\<And>i. i < length T \<Longrightarrow> size (T ! i) = size (S ! i)"
      using timpls_transformable_to'_inv(1,2)[of TI f T g S] by auto
    thus ?case using *[of S T] by simp
  qed simp_all
qed

lemma timpls_transformable_to_if_term_variants:
  fixes s t::"(('a, 'b, 'c) prot_fun, 'd) term" and a b::"'c set"
  defines "P \<equiv> (\<lambda>_. [])(Abs a := [Abs b])"
  assumes st: "term_variants_pred P s t"
    and ab: "(a,b) \<in> set TI"
  shows "timpls_transformable_to TI s t"
using st P_def
proof (induction rule: term_variants_pred.induct)
  case (term_variants_P T S f) thus ?case
    using ab list_all2_conv_all_nth[of "timpls_transformable_to TI" T S]
    by auto
next
  case (term_variants_Fun T S f) thus ?case
    using ab list_all2_conv_all_nth[of "timpls_transformable_to TI" T S]
    by auto
qed simp

lemma timpls_transformable_to'_if_term_variants:
  fixes s t::"(('a, 'b, 'c) prot_fun, 'd) term" and a b::"'c set"
  defines "P \<equiv> (\<lambda>_. [])(Abs a := [Abs b])"
  assumes st: "term_variants_pred P s t"
    and ab: "(a,b) \<in> (set TI)\<^sup>+"
  shows "timpls_transformable_to' TI s t"
using st P_def
proof (induction rule: term_variants_pred.induct)
  case (term_variants_P T S f) thus ?case
    using ab list_all2_conv_all_nth[of "timpls_transformable_to' TI" T S]
          in_trancl_closure_iff_in_trancl_fun[of _ _ TI]
    by auto
next
  case (term_variants_Fun T S f) thus ?case
    using ab list_all2_conv_all_nth[of "timpls_transformable_to' TI" T S]
          in_trancl_closure_iff_in_trancl_fun[of _ _ TI]
    by auto
qed simp

lemma timpls_transformable_to_trans:
  assumes TI_trancl: "\<forall>(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b \<longrightarrow> (a,b) \<in> set TI"
    and st: "timpls_transformable_to TI s t"
    and tu: "timpls_transformable_to TI t u"
  shows "timpls_transformable_to TI s u"
using st tu
proof (induction s arbitrary: t u)
  case (Var x) thus ?case using tu timpls_transformable_to_inv_Var(1) by fast
next
  case (Fun f T)
  obtain g S where t:
      "t = Fun g S" "length T = length S"
      "\<And>i. i < length T \<Longrightarrow> timpls_transformable_to TI (T ! i) (S ! i)"
      "f \<noteq> g \<Longrightarrow> is_Abs f \<and> is_Abs g \<and> (the_Abs f, the_Abs g) \<in> set TI"
    using timpls_transformable_to_inv'[OF Fun.prems(1)] TI_trancl by moura

  obtain h U where u:
      "u = Fun h U" "length S = length U"
      "\<And>i. i < length S \<Longrightarrow> timpls_transformable_to TI (S ! i) (U ! i)"
      "g \<noteq> h \<Longrightarrow> is_Abs g \<and> is_Abs h \<and> (the_Abs g, the_Abs h) \<in> set TI"
    using timpls_transformable_to_inv'[OF Fun.prems(2)[unfolded t(1)]] TI_trancl by moura

  have "list_all2 (timpls_transformable_to TI) T U"
    using t(1,2,3) u(1,2,3) Fun.IH
          list_all2_conv_all_nth[of "timpls_transformable_to TI" T S]
          list_all2_conv_all_nth[of "timpls_transformable_to TI" S U]
          list_all2_conv_all_nth[of "timpls_transformable_to TI" T U]
    by force
  moreover have "(the_Abs f, the_Abs h) \<in> set TI"
    when "(the_Abs f, the_Abs g) \<in> set TI" "(the_Abs g, the_Abs h) \<in> set TI"
         "f \<noteq> h" "is_Abs f" "is_Abs h"
    using that(3,4,5) TI_trancl trancl_into_trancl[OF r_into_trancl[OF that(1)] that(2)]
    unfolding is_Abs_def the_Abs_def
    by force
  hence "is_Abs f \<and> is_Abs h \<and> (the_Abs f, the_Abs h) \<in> set TI"
    when "f \<noteq> h"
    using that TI_trancl t(4) u(4) by fast
  ultimately show ?case using t(1) u(1) by force
qed

lemma timpls_transformable_to'_trans:
  assumes st: "timpls_transformable_to' TI s t"
    and tu: "timpls_transformable_to' TI t u"
  shows "timpls_transformable_to' TI s u"
using st tu
proof (induction s arbitrary: t u)
  case (Var x) thus ?case using tu timpls_transformable_to_inv_Var(3) by fast
next
  case (Fun f T)
  note 0 = in_trancl_closure_iff_in_trancl_fun[of _ _ TI]

  obtain g S where t:
      "t = Fun g S" "length T = length S"
      "\<And>i. i < length T \<Longrightarrow> timpls_transformable_to' TI (T ! i) (S ! i)"
      "f \<noteq> g \<Longrightarrow> is_Abs f \<and> is_Abs g \<and> (the_Abs f, the_Abs g) \<in> (set TI)\<^sup>+"
    using timpls_transformable_to'_inv'[OF Fun.prems(1)] 0 by moura

  obtain h U where u:
      "u = Fun h U" "length S = length U"
      "\<And>i. i < length S \<Longrightarrow> timpls_transformable_to' TI (S ! i) (U ! i)"
      "g \<noteq> h \<Longrightarrow> is_Abs g \<and> is_Abs h \<and> (the_Abs g, the_Abs h) \<in> (set TI)\<^sup>+"
    using timpls_transformable_to'_inv'[OF Fun.prems(2)[unfolded t(1)]] 0 by moura

  have "list_all2 (timpls_transformable_to' TI) T U"
    using t(1,2,3) u(1,2,3) Fun.IH
          list_all2_conv_all_nth[of "timpls_transformable_to' TI" T S]
          list_all2_conv_all_nth[of "timpls_transformable_to' TI" S U]
          list_all2_conv_all_nth[of "timpls_transformable_to' TI" T U]
    by force
  moreover have "(the_Abs f, the_Abs h) \<in> (set TI)\<^sup>+"
    when "(the_Abs f, the_Abs g) \<in> (set TI)\<^sup>+" "(the_Abs g, the_Abs h) \<in> (set TI)\<^sup>+"
    using that by simp
  hence "is_Abs f \<and> is_Abs h \<and> (the_Abs f, the_Abs h) \<in> (set TI)\<^sup>+"
    when "f \<noteq> h"
    by (metis that t(4) u(4))
  ultimately show ?case using t(1) u(1) 0 by force
qed

lemma timpls_transformable_to_mono:
  assumes "set TI \<subseteq> set TI'"
    and "timpls_transformable_to TI s t"
  shows "timpls_transformable_to TI' s t"
  using assms
proof (induction TI s t rule: timpls_transformable_to.induct)
  case (2 TI f T g S)
  have *: "f = g \<or> (is_Abs f \<and> is_Abs g \<and> (the_Abs f, the_Abs g) \<in> set TI)"
          "list_all2 (timpls_transformable_to TI) T S"
    using "2.prems" by simp_all

  show ?case
    using "2.IH" "2.prems"(1) list.rel_mono_strong[OF *(2)] *(1) in_trancl_mono[of TI TI']
    by (metis (no_types, lifting) timpls_transformable_to.simps(2) set_rev_mp)
qed auto

lemma timpls_transformable_to'_mono:
  assumes "set TI \<subseteq> set TI'"
    and "timpls_transformable_to' TI s t"
  shows "timpls_transformable_to' TI' s t"
  using assms
proof (induction TI s t rule: timpls_transformable_to'.induct)
  case (2 TI f T g S)
  have *: "f = g \<or> (is_Abs f \<and> is_Abs g \<and> in_trancl TI (the_Abs f) (the_Abs g))"
          "list_all2 (timpls_transformable_to' TI) T S"
    using "2.prems" by simp_all

  show ?case
    using "2.IH" "2.prems"(1) list.rel_mono_strong[OF *(2)] *(1) in_trancl_mono[of TI TI']
    by (metis (no_types, lifting) timpls_transformable_to'.simps(2))
qed auto

lemma timpls_transformable_to_refl_minus_eq:
  "timpls_transformable_to TI s t \<longleftrightarrow> timpls_transformable_to (filter (\<lambda>(a,b). a \<noteq> b) TI) s t"
  (is "?A \<longleftrightarrow> ?B")
proof
  let ?TI' = "\<lambda>TI. filter (\<lambda>(a,b). a \<noteq> b) TI"

  show ?A when ?B using that timpls_transformable_to_mono[of "?TI' TI" TI] by auto

  show ?B when ?A using that
  proof (induction TI s t rule: timpls_transformable_to.induct)
    case (2 TI f T g S)
    have *: "f = g \<or> (is_Abs f \<and> is_Abs g \<and> (the_Abs f, the_Abs g) \<in> set TI)"
            "list_all2 (timpls_transformable_to TI) T S"
      using "2.prems" by simp_all

    have "f = g \<or> (is_Abs f \<and> is_Abs g \<and> (the_Abs f, the_Abs g) \<in> set (?TI' TI))"
      using *(1) unfolding is_Abs_def by auto
    moreover have "list_all2 (timpls_transformable_to (?TI' TI)) T S"
      using *(2) "2.IH" list.rel_mono_strong by blast
    ultimately show ?case by force
  qed auto
qed

lemma timpls_transformable_to_iff_in_timpl_closure:
  assumes "set TI' = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
  shows "timpls_transformable_to TI' s t \<longleftrightarrow> t \<in> timpl_closure s (set TI)" (is "?A s t \<longleftrightarrow> ?B s t")
proof
  show "?A s t \<Longrightarrow> ?B s t" using assms
  proof (induction s t rule: timpls_transformable_to.induct)
    case (2 TI f T g S)
    note prems = "2.prems"
    note IH = "2.IH"

    have 1: "length T = length S" "\<forall>i<length T. timpls_transformable_to TI' (T ! i) (S ! i)"
      using prems(1) list_all2_conv_all_nth[of "timpls_transformable_to TI'" T S] by simp_all

    note 2 = timpl_closure_is_timpl_closure'
    note 3 = in_set_conv_nth[of _ T] in_set_conv_nth[of _ S]

    have 4: "timpl_closure' (set TI') = timpl_closure' (set TI)"
      using timpl_closure'_timpls_trancl_eq'[of "set TI"] prems(2) by simp

    have IH': "(T ! i, S ! i) \<in> timpl_closure' (set TI')" when i: "i < length S" for i
    proof -
      have "timpls_transformable_to TI' (T ! i) (S ! i)" using i 1 by presburger 
      hence "S ! i \<in> timpl_closure (T ! i) (set TI)"
        using IH[of "T ! i" "S ! i"] i 1(1) prems(2) by force
      thus ?thesis using 2[of "S ! i" "T ! i" "set TI"] 4 by blast
    qed

    have 5: "f = g \<or> (\<exists>a b. (a, b) \<in> (set TI')\<^sup>+ \<and> f = Abs a \<and> g = Abs b)"
      using prems(1) the_Abs_def[of f] the_Abs_def[of g] is_Abs_def[of f] is_Abs_def[of g] 
      by fastforce

    show ?case using 2 4 timpl_closure_FunI[OF IH' 1(1) 5] 1(1) by auto
  qed (simp_all add: timpl_closure.FP)

  show "?B s t \<Longrightarrow> ?A s t"
  proof (induction t rule: timpl_closure.induct)
    case (TI u a b v) show ?case
    proof (cases "a = b")
      case True thus ?thesis using TI.hyps(3) TI.IH term_variants_pred_refl_inv by fastforce
    next
      case False
      hence 1: "timpls_transformable_to TI' u v"
        using TI.hyps(2) assms timpls_transformable_to_if_term_variants[OF TI.hyps(3), of TI']
        by blast
      have 2: "(c,d) \<in> set TI'" when cd: "(c,d) \<in> (set TI')\<^sup>+" "c \<noteq> d" for c d
      proof -
        let ?cl = "\<lambda>X. {(a,b) \<in> X\<^sup>+. a \<noteq> b}"
        have "?cl (set TI') = ?cl (?cl (set TI))" using assms by presburger
        hence "set TI' = ?cl (set TI')" using assms trancl_minus_refl_idem[of "set TI"] by argo
        thus ?thesis using cd by blast
      qed
      show ?thesis using timpls_transformable_to_trans[OF _ TI.IH 1] 2 by blast
    qed
  qed (use timpls_transformable_to_refl in fast)
qed

lemma timpls_transformable_to'_iff_in_timpl_closure:
  "timpls_transformable_to' TI s t \<longleftrightarrow> t \<in> timpl_closure s (set TI)" (is "?A s t \<longleftrightarrow> ?B s t")
proof
  show "?A s t \<Longrightarrow> ?B s t"
  proof (induction s t rule: timpls_transformable_to'.induct)
    case (2 TI f T g S)
    note prems = "2.prems"
    note IH = "2.IH"

    have 1: "length T = length S" "\<forall>i<length T. timpls_transformable_to' TI (T ! i) (S ! i)"
      using prems list_all2_conv_all_nth[of "timpls_transformable_to' TI" T S] by simp_all

    note 2 = timpl_closure_is_timpl_closure'
    note 3 = in_set_conv_nth[of _ T] in_set_conv_nth[of _ S]

    have IH': "(T ! i, S ! i) \<in> timpl_closure' (set TI)" when i: "i < length S" for i
    proof -
      have "timpls_transformable_to' TI (T ! i) (S ! i)" using i 1 by presburger 
      hence "S ! i \<in> timpl_closure (T ! i) (set TI)" using IH[of "T ! i" "S ! i"] i 1(1) by force
      thus ?thesis using 2[of "S ! i" "T ! i" "set TI"] by blast
    qed

    have 4: "f = g \<or> (\<exists>a b. (a, b) \<in> (set TI)\<^sup>+ \<and> f = Abs a \<and> g = Abs b)"
      using prems the_Abs_def[of f] the_Abs_def[of g] is_Abs_def[of f] is_Abs_def[of g]
            in_trancl_closure_iff_in_trancl_fun[of _ _ TI]
      by auto

    show ?case using 2 timpl_closure_FunI[OF IH' 1(1) 4] 1(1) by auto
  qed (simp_all add: timpl_closure.FP)

  show "?B s t \<Longrightarrow> ?A s t"
  proof (induction t rule: timpl_closure.induct)
    case (TI u a b v) thus ?case
      using timpls_transformable_to'_trans
            timpls_transformable_to'_if_term_variants
      by blast
  qed (use timpls_transformable_to_refl(2) in fast)
qed

lemma equal_mod_timpls_iff_ex_in_timpl_closure:
  assumes "set TI' = {(a,b) \<in> TI\<^sup>+. a \<noteq> b}"
  shows "equal_mod_timpls TI' s t \<longleftrightarrow> (\<exists>u. u \<in> timpl_closure s TI \<and> u \<in> timpl_closure t TI)"
    (is "?A s t \<longleftrightarrow> ?B s t")
proof
  show "?A s t \<Longrightarrow> ?B s t" using assms
  proof (induction s t rule: equal_mod_timpls.induct)
    case (2 TI' f T g S)
    note prems = "2.prems"
    note IH = "2.IH"

    have 1: "length T = length S" "\<forall>i<length T. equal_mod_timpls (TI') (T ! i) (S ! i)"
      using prems list_all2_conv_all_nth[of "equal_mod_timpls TI'" T S] by simp_all

    note 2 = timpl_closure_is_timpl_closure'
    note 3 = in_set_conv_nth[of _ T] in_set_conv_nth[of _ S]

    have 4: "timpl_closure' (set TI') = timpl_closure' TI"
      using timpl_closure'_timpls_trancl_eq'[of TI] prems
      by simp

    have IH: "\<exists>u. (T ! i, u) \<in> timpl_closure' TI \<and> (S ! i, u) \<in> timpl_closure' TI"
      when i: "i < length S" for i
    proof -
      have "equal_mod_timpls TI' (T ! i) (S ! i)" using i 1 by presburger 
      hence "\<exists>u. u \<in> timpl_closure (T ! i) TI \<and> u \<in> timpl_closure (S ! i) TI"
        using IH[of "T ! i" "S ! i"] i 1(1) prems by force
      thus ?thesis using 4 unfolding 2 by blast
    qed

    let ?P = "\<lambda>G. f = g \<or> (\<exists>a b. (a, b) \<in> G \<and> f = Abs a \<and> g = Abs b) \<or>
                   (\<exists>a b. (a, b) \<in> G \<and> f = Abs b \<and> g = Abs a) \<or>
                   (\<exists>a b c. (a, c) \<in> G \<and> (b, c) \<in> G \<and> f = Abs a \<and> g = Abs b)"

    have "?P (set TI')"
      using prems the_Abs_def[of f] the_Abs_def[of g] is_Abs_def[of f] is_Abs_def[of g]
      by fastforce
    hence "?P (TI\<^sup>+)" unfolding prems by blast
    hence "?P (rtrancl TI)" by (metis (no_types, lifting) trancl_into_rtrancl)
    hence 5: "f = g \<or> (\<exists>a b c. (a, c) \<in> TI\<^sup>* \<and> (b, c) \<in> TI\<^sup>* \<and> f = Abs a \<and> g = Abs b)" by blast

    show ?case
      using timpl_closure_FunI3[OF _ 1(1) 5]  IH 1(1)
      unfolding timpl_closure'_timpls_rtrancl_eq 2
      by auto
  qed (use timpl_closure.FP in auto)

  show "?A s t" when B: "?B s t"
  proof -
    obtain u where u: "u \<in> timpl_closure s TI" "u \<in> timpl_closure t TI"
      using B by moura
    thus ?thesis using assms
    proof (induction u arbitrary: s t rule: term.induct)
      case (Var x s t) thus ?case
        using timpl_closure_Var_in_iff[of x s TI]
              timpl_closure_Var_in_iff[of x t TI]
              equal_mod_timpls.simps(1)[of TI' x x]
        by blast
    next
      case (Fun f U s t)
      obtain g S where s:
          "s = Fun g S" "length U = length S"
          "\<And>i. i < length U \<Longrightarrow> U ! i \<in> timpl_closure (S ! i) TI"
          "g \<noteq> f \<Longrightarrow> is_Abs g \<and> is_Abs f \<and> (the_Abs g, the_Abs f) \<in> TI\<^sup>+"
        using Fun.prems(1) timpl_closure_Fun_inv'[of f U _ _ TI]
        by (cases s) auto

      obtain h T where t:
          "t = Fun h T" "length U = length T"
          "\<And>i. i < length U \<Longrightarrow> U ! i \<in> timpl_closure (T ! i) TI"
          "h \<noteq> f \<Longrightarrow> is_Abs h \<and> is_Abs f \<and> (the_Abs h, the_Abs f) \<in> TI\<^sup>+"
        using Fun.prems(2) timpl_closure_Fun_inv'[of f U _ _ TI]
        by (cases t) auto

      have g: "(the_Abs g, the_Abs f) \<in> set TI'" "is_Abs f" "is_Abs g" when neq_f: "g \<noteq> f"
      proof -
        obtain ga fa where a: "g = Abs ga" "f = Abs fa"
          using s(4)[OF neq_f] unfolding is_Abs_def by presburger
        hence "the_Abs g \<noteq> the_Abs f" using neq_f by simp
        thus "(the_Abs g, the_Abs f) \<in> set TI'" "is_Abs f" "is_Abs g"
          using s(4)[OF neq_f] Fun.prems by blast+
      qed

      have h: "(the_Abs h, the_Abs f) \<in> set TI'" "is_Abs f" "is_Abs h" when neq_f: "h \<noteq> f"
      proof -
        obtain ha fa where a: "h = Abs ha" "f = Abs fa"
          using t(4)[OF neq_f] unfolding is_Abs_def by presburger
        hence "the_Abs h \<noteq> the_Abs f" using neq_f by simp
        thus "(the_Abs h, the_Abs f) \<in> set TI'" "is_Abs f" "is_Abs h"
          using t(4)[OF neq_f] Fun.prems by blast+
      qed

      have "equal_mod_timpls TI' (S ! i) (T ! i)"
        when i: "i < length U" for i
        using i Fun.IH s(1,2,3) t(1,2,3) nth_mem[OF i] Fun.prems by meson
      hence "list_all2 (equal_mod_timpls TI') S T"
        using list_all2_conv_all_nth[of "equal_mod_timpls TI'" S T] s(2) t(2) by presburger
      thus ?case using s(1) t(1) g h by fastforce
    qed
  qed
qed

(* lemma equal_mod_timpls_iff_ex_in_timpl_closure':
  "equal_mod_timpls (TI\<^sup>+) s t \<longleftrightarrow> (\<exists>u. u \<in> timpl_closure s TI \<and> u \<in> timpl_closure t TI)"
using equal_mod_timpls_iff_ex_in_timpl_closure equal_mod_timpls_refl_minus_eq
by blast *)

context
begin
private inductive timpls_transformable_to_pred where
  Var: "timpls_transformable_to_pred A (Var x) (Var x)"
| Fun: "\<lbrakk>\<not>is_Abs f; length T = length S;
         \<And>i. i < length T \<Longrightarrow> timpls_transformable_to_pred A (T ! i) (S ! i)\<rbrakk>
        \<Longrightarrow> timpls_transformable_to_pred A (Fun f T) (Fun f S)"
| Abs: "b \<in> A \<Longrightarrow> timpls_transformable_to_pred A (Fun (Abs a) []) (Fun (Abs b) [])"

private lemma timpls_transformable_to_pred_inv_Var:
  assumes "timpls_transformable_to_pred A (Var x) t"
  shows "t = Var x"
using assms by (auto elim: timpls_transformable_to_pred.cases)

private lemma timpls_transformable_to_pred_inv:
  assumes "timpls_transformable_to_pred A (Fun f T) t"
  shows "is_Fun t"
    and "length T = length (args t)"
    and "\<And>i. i < length T \<Longrightarrow> timpls_transformable_to_pred A (T ! i) (args t ! i)"
    and "\<not>is_Abs f \<Longrightarrow> f = the_Fun t"
    and "is_Abs f \<Longrightarrow> (is_Abs (the_Fun t) \<and> the_Abs (the_Fun t) \<in> A)"
using assms by (auto elim!: timpls_transformable_to_pred.cases[of A])

private lemma timpls_transformable_to_pred_finite_aux1:
  assumes f: "\<not>is_Abs f"
  shows "{s. timpls_transformable_to_pred A (Fun f T) s} \<subseteq>
          (\<lambda>S. Fun f S) ` {S. length T = length S \<and>
                              (\<forall>s \<in> set S. \<exists>t \<in> set T. timpls_transformable_to_pred A t s)}"
    (is "?B \<subseteq> ?C")
proof
  fix s assume s: "s \<in> ?B"
  hence *: "timpls_transformable_to_pred A (Fun f T) s" by blast

  obtain S where S:
      "s = Fun f S" "length T = length S" "\<And>i. i < length T \<Longrightarrow> timpls_transformable_to_pred A (T ! i) (S ! i)"
    using f timpls_transformable_to_pred_inv[OF *] unfolding the_Abs_def is_Abs_def by auto

  have "\<forall>s\<in>set S. \<exists>t\<in>set T. timpls_transformable_to_pred A t s" using S(2,3) in_set_conv_nth by metis
  thus "s \<in> ?C" using S(1,2) by blast
qed

private lemma timpls_transformable_to_pred_finite_aux2:
  "{s. timpls_transformable_to_pred A (Fun (Abs a) []) s} \<subseteq> (\<lambda>b. Fun (Abs b) []) ` A" (is "?B \<subseteq> ?C")
proof
  fix s assume s: "s \<in> ?B"
  hence *: "timpls_transformable_to_pred A (Fun (Abs a) []) s" by blast

  obtain b where b: "s = Fun (Abs b) []" "b \<in> A"
    using timpls_transformable_to_pred_inv[OF *] unfolding the_Abs_def is_Abs_def by auto
  thus "s \<in> ?C" by blast
qed

private lemma timpls_transformable_to_pred_finite:
  fixes t::"(('fun,'atom,'sets) prot_fun, 'a) term"
  assumes A: "finite A"
    and t: "wf\<^sub>t\<^sub>r\<^sub>m t"
  shows "finite {s. timpls_transformable_to_pred A t s}"
using t
proof (induction t)
  case (Var x)
  have "{s::(('fun,'atom,'sets) prot_fun, 'a) term. timpls_transformable_to_pred A (Var x) s} = {Var x}"
    by (auto intro: timpls_transformable_to_pred.Var elim: timpls_transformable_to_pred_inv_Var)
  thus ?case by simp
next
  case (Fun f T)
  have IH: "finite {s. timpls_transformable_to_pred A t s}" when t: "t \<in> set T" for t
    using Fun.IH[OF t] wf_trm_param[OF Fun.prems t] by blast

  show ?case
  proof (cases "is_Abs f")
    case True
    then obtain a where a: "f = Abs a" unfolding is_Abs_def by presburger
    hence "T = []" using wf_trm_arity[OF Fun.prems] by simp_all
    hence "{a. timpls_transformable_to_pred A (Fun f T) a} \<subseteq> (\<lambda>b. Fun (Abs b) []) ` A"
      using timpls_transformable_to_pred_finite_aux2[of A a] a by auto
    thus ?thesis using A finite_subset by fast
  next
    case False thus ?thesis
      using IH finite_lists_length_eq' timpls_transformable_to_pred_finite_aux1[of f A T] finite_subset
      by blast
  qed
qed

private lemma timpls_transformable_to_pred_if_timpls_transformable_to:
  assumes s: "timpls_transformable_to TI t s"
    and t: "wf\<^sub>t\<^sub>r\<^sub>m t" "\<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> the_Abs f \<in> A"
  shows "timpls_transformable_to_pred (A \<union> fst ` (set TI)\<^sup>+ \<union> snd ` (set TI)\<^sup>+) t s"
using s t
proof (induction rule: timpls_transformable_to.induct)
  case (2 TI f T g S)
  let ?A = "A \<union> fst ` (set TI)\<^sup>+ \<union> snd ` (set TI)\<^sup>+"

  note prems = "2.prems"
  note IH = "2.IH"

  note 0 = timpls_transformable_to_inv[OF prems(1)]

  have 1: "T = []" "S = []" when f: "f = Abs a" for a
    using f wf_trm_arity[OF prems(2)] 0(1) by simp_all

  have "\<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> the_Abs f \<in> A" when t: "t \<in> set T" for t
    using t prems(3) funs_term_subterms_eq(1)[of "Fun f T"] by blast
  hence 2: "timpls_transformable_to_pred ?A (T ! i) (S ! i)"
    when i: "i < length T" for i
    using i IH 0(1,2) wf_trm_param[OF prems(2)]
    by (metis (no_types) in_set_conv_nth)

  have 3: "the_Abs f \<in> ?A" when f: "is_Abs f" using prems(3) f by force

  show ?case
  proof (cases "f = g")
    case True
    note fg = True
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a where a: "f = Abs a" unfolding is_Abs_def by moura
      thus ?thesis using fg 1[OF a] timpls_transformable_to_pred.Abs[of a ?A a] 3 by simp
    qed (use fg timpls_transformable_to_pred.Fun[OF _ 0(1) 2, of f] in blast)
  next
    case False
    then obtain a b where ab: "f = Abs a" "g = Abs b" "(a, b) \<in> (set TI)\<^sup>+"
      using 0(3) in_trancl_closure_iff_in_trancl_fun[of _ _ TI]
      unfolding is_Abs_def the_Abs_def by fastforce
    hence "a \<in> ?A" "b \<in> ?A" by force+
    thus ?thesis using timpls_transformable_to_pred.Abs ab(1,2) 1[OF ab(1)] by metis
  qed
qed (simp_all add: timpls_transformable_to_pred.Var)

private lemma timpls_transformable_to_pred_if_timpls_transformable_to':
  assumes s: "timpls_transformable_to' TI t s"
    and t: "wf\<^sub>t\<^sub>r\<^sub>m t" "\<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> the_Abs f \<in> A"
  shows "timpls_transformable_to_pred (A \<union> fst ` (set TI)\<^sup>+ \<union> snd ` (set TI)\<^sup>+) t s"
using s t
proof (induction rule: timpls_transformable_to.induct)
  case (2 TI f T g S)
  let ?A = "A \<union> fst ` (set TI)\<^sup>+ \<union> snd ` (set TI)\<^sup>+"

  note prems = "2.prems"
  note IH = "2.IH"

  note 0 = timpls_transformable_to'_inv[OF prems(1)]

  have 1: "T = []" "S = []" when f: "f = Abs a" for a
    using f wf_trm_arity[OF prems(2)] 0(1) by simp_all

  have "\<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> the_Abs f \<in> A" when t: "t \<in> set T" for t
    using t prems(3) funs_term_subterms_eq(1)[of "Fun f T"] by blast
  hence 2: "timpls_transformable_to_pred ?A (T ! i) (S ! i)"
    when i: "i < length T" for i
    using i IH 0(1,2) wf_trm_param[OF prems(2)]
    by (metis (no_types) in_set_conv_nth)

  have 3: "the_Abs f \<in> ?A" when f: "is_Abs f" using prems(3) f by force

  show ?case
  proof (cases "f = g")
    case True
    note fg = True
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a where a: "f = Abs a" unfolding is_Abs_def by moura
      thus ?thesis using fg 1[OF a] timpls_transformable_to_pred.Abs[of a ?A a] 3 by simp
    qed (use fg timpls_transformable_to_pred.Fun[OF _ 0(1) 2, of f] in blast)
  next
    case False
    then obtain a b where ab: "f = Abs a" "g = Abs b" "(a, b) \<in> (set TI)\<^sup>+"
      using 0(3) in_trancl_closure_iff_in_trancl_fun[of _ _ TI]
      unfolding is_Abs_def the_Abs_def by fastforce
    hence "a \<in> ?A" "b \<in> ?A" by force+
    thus ?thesis using timpls_transformable_to_pred.Abs ab(1,2) 1[OF ab(1)] by metis
  qed
qed (simp_all add: timpls_transformable_to_pred.Var)

private lemma timpls_transformable_to_pred_if_equal_mod_timpls:
  assumes s: "equal_mod_timpls TI t s"
    and t: "wf\<^sub>t\<^sub>r\<^sub>m t" "\<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> the_Abs f \<in> A"
  shows "timpls_transformable_to_pred (A \<union> fst ` (set TI)\<^sup>+ \<union> snd ` (set TI)\<^sup>+) t s"
using s t
proof (induction rule: equal_mod_timpls.induct)
  case (2 TI f T g S)
  let ?A = "A \<union> fst ` (set TI)\<^sup>+ \<union> snd ` (set TI)\<^sup>+"

  note prems = "2.prems"
  note IH = "2.IH"

  note 0 = equal_mod_timpls_inv[OF prems(1)]

  have 1: "T = []" "S = []" when f: "f = Abs a" for a
    using f wf_trm_arity[OF prems(2)] 0(1) by simp_all

  have "\<forall>f \<in> funs_term t. is_Abs f \<longrightarrow> the_Abs f \<in> A" when t: "t \<in> set T" for t
    using t prems(3) funs_term_subterms_eq(1)[of "Fun f T"] by blast
  hence 2: "timpls_transformable_to_pred ?A (T ! i) (S ! i)"
    when i: "i < length T" for i
    using i IH 0(1,2) wf_trm_param[OF prems(2)]
    by (metis (no_types) in_set_conv_nth)

  have 3: "the_Abs f \<in> ?A" when f: "is_Abs f" using prems(3) f by force

  show ?case
  proof (cases "f = g")
    case True
    note fg = True
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a where a: "f = Abs a" unfolding is_Abs_def by moura
      thus ?thesis using fg 1[OF a] timpls_transformable_to_pred.Abs[of a ?A a] 3 by simp
    qed (use fg timpls_transformable_to_pred.Fun[OF _ 0(1) 2, of f] in blast)
  next
    case False
    then obtain a b where ab: "f = Abs a" "g = Abs b"
        "(a, b) \<in> (set TI)\<^sup>+ \<or> (b, a) \<in> (set TI)\<^sup>+ \<or>
         (\<exists>ti \<in> set TI. (a, snd ti) \<in> (set TI)\<^sup>+ \<and> (b, snd ti) \<in> (set TI)\<^sup>+)"
      using 0(3) in_trancl_closure_iff_in_trancl_fun[of _ _ TI]
      unfolding is_Abs_def the_Abs_def by fastforce
    hence "a \<in> ?A" "b \<in> ?A" by force+
    thus ?thesis using timpls_transformable_to_pred.Abs ab(1,2) 1[OF ab(1)] by metis
  qed
qed (simp_all add: timpls_transformable_to_pred.Var)

lemma timpls_transformable_to_finite:
  assumes t: "wf\<^sub>t\<^sub>r\<^sub>m t"
  shows "finite {s. timpls_transformable_to TI t s}" (is ?P)
    and "finite {s. timpls_transformable_to' TI t s}" (is ?Q)
proof -
  let ?A = "the_Abs ` {f \<in> funs_term t. is_Abs f} \<union> fst ` (set TI)\<^sup>+ \<union> snd ` (set TI)\<^sup>+"

  have 0: "finite ?A" by auto

  have 1: "{s. timpls_transformable_to TI t s} \<subseteq> {s. timpls_transformable_to_pred ?A t s}"
    using timpls_transformable_to_pred_if_timpls_transformable_to[OF _ t] by auto

  have 2: "{s. timpls_transformable_to' TI t s} \<subseteq> {s. timpls_transformable_to_pred ?A t s}"
    using timpls_transformable_to_pred_if_timpls_transformable_to'[OF _ t] by auto

  show ?P using timpls_transformable_to_pred_finite[OF 0 t] finite_subset[OF 1] by blast
  show ?Q using timpls_transformable_to_pred_finite[OF 0 t] finite_subset[OF 2] by blast
qed

lemma equal_mod_timpls_finite:
  assumes t: "wf\<^sub>t\<^sub>r\<^sub>m t"
  shows "finite {s. equal_mod_timpls TI t s}"
proof -
  let ?A = "the_Abs ` {f \<in> funs_term t. is_Abs f} \<union> fst ` (set TI)\<^sup>+ \<union> snd ` (set TI)\<^sup>+"

  have 0: "finite ?A" by auto

  have 1: "{s. equal_mod_timpls TI t s} \<subseteq> {s. timpls_transformable_to_pred ?A t s}"
    using timpls_transformable_to_pred_if_equal_mod_timpls[OF _ t] by auto

  show ?thesis using timpls_transformable_to_pred_finite[OF 0 t] finite_subset[OF 1] by blast
qed

end

lemma intruder_synth_mod_timpls_is_synth_timpl_closure_set:
  fixes t::"(('fun, 'atom, 'sets) prot_fun, 'a) term" and TI TI'
  assumes "set TI' = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
  shows "intruder_synth_mod_timpls M TI' t \<longleftrightarrow> timpl_closure_set (set M) (set TI) \<turnstile>\<^sub>c t"
      (is "?C t \<longleftrightarrow> ?D t")
proof -
  have *: "(\<exists>m \<in> M. timpls_transformable_to TI' m t) \<longleftrightarrow> t \<in> timpl_closure_set M (set TI)"
    when "set TI' = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    for M TI TI' and t::"(('fun, 'atom, 'sets) prot_fun, 'a) term"
    using timpls_transformable_to_iff_in_timpl_closure[OF that]
          timpl_closure_set_is_timpl_closure_union[of M "set TI"]
          timpl_closure_set_timpls_trancl_eq[of M "set TI"]
          timpl_closure_set_timpls_trancl_eq'[of M "set TI"]
    by auto

  show "?C t \<longleftrightarrow> ?D t"
  proof
    show "?C t \<Longrightarrow> ?D t" using assms
    proof (induction t arbitrary: M TI TI' rule: intruder_synth_mod_timpls.induct)
      case (1 M TI' x)
      hence "Var x \<in> timpl_closure_set (set M) (set TI)"
        using timpl_closure.FP member_def unfolding timpl_closure_set_def by force
      thus ?case by simp
    next
      case (2 M TI f T)
      show ?case
      proof (cases "\<exists>m \<in> set M. timpls_transformable_to TI' m (Fun f T)")
        case True thus ?thesis
          using "2.prems" *[of TI' TI "set M" "Fun f T"]
                intruder_synth.AxiomC[of "Fun f T" "timpl_closure_set (set M) (set TI)"]
          by blast
      next
        case False
        hence "\<not>(list_ex (\<lambda>t. timpls_transformable_to TI' t (Fun f T)) M)"
          unfolding list_ex_iff by blast
        hence "public f" "length T = arity f" "list_all (intruder_synth_mod_timpls M TI') T"
          using "2.prems"(1) by force+
        thus ?thesis using "2.IH"[OF _ _ "2.prems"(2)] unfolding list_all_iff by force
      qed
    qed
  
    show "?D t \<Longrightarrow> ?C t"
    proof (induction t rule: intruder_synth_induct)
      case (AxiomC t) thus ?case
        using timpl_closure_set_Var_in_iff[of _ "set M" "set TI"] *[OF assms, of "set M" t]
        by (cases t rule: term.exhaust) (force simp add: member_def list_ex_iff)+
    next
      case (ComposeC T f) thus ?case
        using list_all_iff[of "intruder_synth_mod_timpls M TI'" T]
              intruder_synth_mod_timpls.simps(2)[of M TI' f T]
        by blast
    qed
  qed
qed

lemma intruder_synth_mod_timpls'_is_synth_timpl_closure_set:
  fixes t::"(('fun, 'atom, 'sets) prot_fun, 'a) term" and TI
  shows "intruder_synth_mod_timpls' M TI t \<longleftrightarrow> timpl_closure_set (set M) (set TI) \<turnstile>\<^sub>c t"
      (is "?A t \<longleftrightarrow> ?B t")
proof -
  have *: "(\<exists>m \<in> M. timpls_transformable_to' TI m t) \<longleftrightarrow> t \<in> timpl_closure_set M (set TI)"
    for M TI and t::"(('fun, 'atom, 'sets) prot_fun, 'a) term"
    using timpls_transformable_to'_iff_in_timpl_closure[of TI _ t]
          timpl_closure_set_is_timpl_closure_union[of M "set TI"]
    by blast+

  show "?A t \<longleftrightarrow> ?B t"
  proof
    show "?A t \<Longrightarrow> ?B t"
    proof (induction t arbitrary: M TI rule: intruder_synth_mod_timpls'.induct)
      case (1 M TI x)
      hence "Var x \<in> timpl_closure_set (set M) (set TI)"
        using timpl_closure.FP List.member_def[of M] unfolding timpl_closure_set_def by auto
      thus ?case by simp
    next
      case (2 M TI f T)
      show ?case
      proof (cases "\<exists>m \<in> set M. timpls_transformable_to' TI m (Fun f T)")
        case True thus ?thesis
          using "2.prems" *[of "set M" TI "Fun f T"]
                intruder_synth.AxiomC[of "Fun f T" "timpl_closure_set (set M) (set TI)"]
          by blast
      next
        case False
        hence "public f" "length T = arity f" "list_all (intruder_synth_mod_timpls' M TI) T"
          using "2.prems" list_ex_iff[of _ M] by force+
        thus ?thesis
          using "2.IH"[of _ M TI] list_all_iff[of "intruder_synth_mod_timpls' M TI" T]
          by force
      qed
    qed
  
    show "?B t \<Longrightarrow> ?A t"
    proof (induction t rule: intruder_synth_induct)
      case (AxiomC t) thus ?case
        using AxiomC timpl_closure_set_Var_in_iff[of _ "set M" "set TI"] *[of "set M" TI t]
              list_ex_iff[of _ M] List.member_def[of M]
        by (cases t rule: term.exhaust) force+
    next
      case (ComposeC T f) thus ?case
        using list_all_iff[of "intruder_synth_mod_timpls' M TI" T]
              intruder_synth_mod_timpls'.simps(2)[of M TI f T]
        by blast
    qed
  qed
qed

lemma intruder_synth_mod_eq_timpls_is_synth_timpl_closure_set:
  fixes t::"(('fun, 'atom, 'sets) prot_fun, 'a) term" and TI
  defines "cl \<equiv> \<lambda>TI. {(a,b) \<in> TI\<^sup>+. a \<noteq> b}"
  shows (* "set TI' = (set TI)\<^sup>+ \<Longrightarrow>
         intruder_synth_mod_eq_timpls M TI' t \<longleftrightarrow>
         (\<exists>s \<in> timpl_closure t (set TI). timpl_closure_set M (set TI) \<turnstile>\<^sub>c s)"
      (is "?P TI TI' \<Longrightarrow> ?A t \<longleftrightarrow> ?B t")
    and *) "set TI' = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b} \<Longrightarrow>
         intruder_synth_mod_eq_timpls M TI' t \<longleftrightarrow>
         (\<exists>s \<in> timpl_closure t (set TI). timpl_closure_set M (set TI) \<turnstile>\<^sub>c s)"
      (is "?Q TI TI' \<Longrightarrow> ?C t \<longleftrightarrow> ?D t")
proof -
  (* have *: "(\<exists>m \<in> M. equal_mod_timpls TI' m t) \<longleftrightarrow>
           (\<exists>s \<in> timpl_closure t (set TI). s \<in> timpl_closure_set M (set TI))"
    when P: "?P TI TI'"
    for M TI TI' and t::"(('fun, 'atom, 'sets) prot_fun, 'a) term"
    using equal_mod_timpls_iff_ex_in_timpl_closure'[OF P]
          timpl_closure_set_is_timpl_closure_union[of M "set TI"]
          timpl_closure_set_timpls_trancl_eq[of M "set TI"]
    by blast *)

  have **: "(\<exists>m \<in> M. equal_mod_timpls TI' m t) \<longleftrightarrow>
            (\<exists>s \<in> timpl_closure t (set TI). s \<in> timpl_closure_set M (set TI))"
    when Q: "?Q TI TI'"
    for M TI TI' and t::"(('fun, 'atom, 'sets) prot_fun, 'a) term"
    using equal_mod_timpls_iff_ex_in_timpl_closure[OF Q]
          timpl_closure_set_is_timpl_closure_union[of M "set TI"]
          timpl_closure_set_timpls_trancl_eq'[of M "set TI"]
    by fastforce

(*   show "?A t \<longleftrightarrow> ?B t" when P: "?P TI TI'"
  proof
    show "?A t \<Longrightarrow> ?B t"
    proof (induction t arbitrary: M TI rule: intruder_synth_mod_eq_timpls.induct)
      case (1 M TI x)
      hence "Var x \<in> timpl_closure_set M TI" "Var x \<in> timpl_closure (Var x) TI"
        using timpl_closure.FP unfolding timpl_closure_set_def by auto
      thus ?case by force
    next
      case (2 M TI f T)
      show ?case
      proof (cases "\<exists>m \<in> M. equal_mod_timpls (TI\<^sup>+) m (Fun f T)")
        case True thus ?thesis
          using "2.prems" *[of M TI "Fun f T"] intruder_synth.AxiomC[of _ "timpl_closure_set M TI"]
          by blast
      next
        case False
        hence f: "public f" "length T = arity f" "list_all (intruder_synth_mod_eq_timpls M (TI\<^sup>+)) T"
          using "2.prems" by force+
  
        let ?sy = "intruder_synth (timpl_closure_set M TI)"

        have IH: "\<exists>u \<in> timpl_closure (T ! i) TI. ?sy u"
          when i: "i < length T" for i
          using "2.IH"[of _ M TI] f(3) nth_mem[OF i]
          unfolding list_all_iff by blast
  
        define S where "S \<equiv> map (\<lambda>u. SOME v. v \<in> timpl_closure u TI \<and> ?sy v) T"
  
        have S1: "length T = length S"
          unfolding S_def by simp
  
        have S2: "S ! i \<in> timpl_closure (T ! i) TI"
                 "timpl_closure_set M TI \<turnstile>\<^sub>c S ! i"
          when i: "i < length S" for i
          using i IH someI_ex[of "\<lambda>v. v \<in> timpl_closure (T ! i) TI \<and> ?sy v"]
          unfolding S_def by auto
  
        have "Fun f S \<in> timpl_closure (Fun f T) TI"
          using timpl_closure_FunI[of T S TI f f] S1 S2(1)
          unfolding timpl_closure_is_timpl_closure' by presburger
        thus ?thesis
          by (metis intruder_synth.ComposeC[of S f] f(1,2) S1 S2(2) in_set_conv_nth[of _ S])
      qed
    qed
  
    show "?A t" when B: "?B t"
    proof -
      obtain s where "timpl_closure_set M TI \<turnstile>\<^sub>c s" "s \<in> timpl_closure t TI"
        using B by moura
      thus ?thesis
      proof (induction s arbitrary: t rule: intruder_synth_induct)
        case (AxiomC s t)
        note 1 = timpl_closure_set_Var_in_iff[of _ M TI] timpl_closure_Var_inv[of s _ TI]
        note 2 = *[of M TI]
        show ?case
        proof (cases t)
          case Var thus ?thesis using 1 AxiomC by auto
        next
          case Fun thus ?thesis using 2 AxiomC by auto
        qed
      next
        case (ComposeC T f t)
        obtain g S where gS:
            "t = Fun g S" "length S = length T"
            "\<forall>i < length T. T ! i \<in> timpl_closure (S ! i) TI"
            "g \<noteq> f \<Longrightarrow> is_Abs g \<and> is_Abs f \<and> (the_Abs g, the_Abs f) \<in> TI\<^sup>+"
          using ComposeC.prems(1) timpl_closure'_inv'[of t "Fun f T" TI]
                timpl_closure_is_timpl_closure'[of _ _ TI]
          by fastforce
  
        have IH: "intruder_synth_mod_eq_timpls M (TI\<^sup>+) u" when u: "u \<in> set S" for u
          by (metis u gS(2,3) ComposeC.IH in_set_conv_nth)
  
        note 0 = list_all_iff[of "intruder_synth_mod_eq_timpls M (TI\<^sup>+)" S]
                 intruder_synth_mod_eq_timpls.simps(2)[of M "TI\<^sup>+" g S]
  
        have "f = g" using ComposeC.hyps gS(4) unfolding is_Abs_def by fastforce
        thus ?case by (metis ComposeC.hyps(1,2) gS(1,2) IH 0)
      qed
    qed
  qed *)

  show "?C t \<longleftrightarrow> ?D t" when Q: "?Q TI TI'"
  proof
    show "?C t \<Longrightarrow> ?D t" using Q
    proof (induction t arbitrary: M TI rule: intruder_synth_mod_eq_timpls.induct)
      case (1 M TI' x M TI)
      hence "Var x \<in> timpl_closure_set M (set TI)" "Var x \<in> timpl_closure (Var x) (set TI)"
        using timpl_closure.FP unfolding timpl_closure_set_def by auto
      thus ?case by force
    next
      case (2 M TI' f T M TI)
      show ?case
      proof (cases "\<exists>m \<in> M. equal_mod_timpls TI' m (Fun f T)")
        case True thus ?thesis
          using **[OF "2.prems"(2), of M "Fun f T"]
                intruder_synth.AxiomC[of _ "timpl_closure_set M (set TI)"]
          by blast
      next
        case False
        hence f: "public f" "length T = arity f" "list_all (intruder_synth_mod_eq_timpls M TI') T"
          using "2.prems" by force+
  
        let ?sy = "intruder_synth (timpl_closure_set M (set TI))"

        have IH: "\<exists>u \<in> timpl_closure (T ! i) (set TI). ?sy u"
          when i: "i < length T" for i
          using "2.IH"[of _ M TI] f(3) nth_mem[OF i] "2.prems"(2)
          unfolding list_all_iff by blast
  
        define S where "S \<equiv> map (\<lambda>u. SOME v. v \<in> timpl_closure u (set TI) \<and> ?sy v) T"
  
        have S1: "length T = length S"
          unfolding S_def by simp
  
        have S2: "S ! i \<in> timpl_closure (T ! i) (set TI)"
                  "timpl_closure_set M (set TI) \<turnstile>\<^sub>c S ! i"
          when i: "i < length S" for i
          using i IH someI_ex[of "\<lambda>v. v \<in> timpl_closure (T ! i) (set TI) \<and> ?sy v"]
          unfolding S_def by auto
  
        have "Fun f S \<in> timpl_closure (Fun f T) (set TI)"
          using timpl_closure_FunI[of T S "set TI" f f] S1 S2(1)
          unfolding timpl_closure_is_timpl_closure' by presburger
        thus ?thesis
          by (metis intruder_synth.ComposeC[of S f] f(1,2) S1 S2(2) in_set_conv_nth[of _ S])
      qed
    qed
  
    show "?C t" when D: "?D t"
    proof -
      obtain s where "timpl_closure_set M (set TI) \<turnstile>\<^sub>c s" "s \<in> timpl_closure t (set TI)"
        using D by moura
      thus ?thesis
      proof (induction s arbitrary: t rule: intruder_synth_induct)
        case (AxiomC s t)
        note 1 = timpl_closure_set_Var_in_iff[of _ M "set TI"] timpl_closure_Var_inv[of s _ "set TI"]
        note 2 = **[OF Q, of M]
        show ?case
        proof (cases t)
          case Var thus ?thesis using 1 AxiomC by auto
        next
          case Fun thus ?thesis using 2 AxiomC by auto
        qed
      next
        case (ComposeC T f t)
        obtain g S where gS:
            "t = Fun g S" "length S = length T"
            "\<forall>i < length T. T ! i \<in> timpl_closure (S ! i) (set TI)"
            "g \<noteq> f \<Longrightarrow> is_Abs g \<and> is_Abs f \<and> (the_Abs g, the_Abs f) \<in> (set TI)\<^sup>+"
          using ComposeC.prems(1) timpl_closure'_inv'[of t "Fun f T" "set TI"]
                timpl_closure_is_timpl_closure'[of _ _ "set TI"]
          by fastforce
  
        have IH: "intruder_synth_mod_eq_timpls M TI' u" when u: "u \<in> set S" for u
          by (metis u gS(2,3) ComposeC.IH in_set_conv_nth)
  
        note 0 = list_all_iff[of "intruder_synth_mod_eq_timpls M TI'" S]
                 intruder_synth_mod_eq_timpls.simps(2)[of M TI' g S]
  
        have "f = g" using ComposeC.hyps gS(4) unfolding is_Abs_def by fastforce
        thus ?case by (metis ComposeC.hyps(1,2) gS(1,2) IH 0)
      qed
    qed
  qed
qed

lemma timpl_closure_finite:
  assumes t: "wf\<^sub>t\<^sub>r\<^sub>m t"
  shows "finite (timpl_closure t (set TI))"
using timpls_transformable_to'_iff_in_timpl_closure[of TI t]
      timpls_transformable_to_finite[OF t, of TI]
by auto

lemma timpl_closure_set_finite:
  fixes TI::"('sets set \<times> 'sets set) list"
  assumes M_finite: "finite M"
    and M_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M"
  shows "finite (timpl_closure_set M (set TI))"
using timpl_closure_set_is_timpl_closure_union[of M "set TI"]
      timpl_closure_finite[of _ TI] M_finite M_wf finite
by auto

lemma comp_timpl_closure_is_timpl_closure_set:
  fixes M and TI::"('sets set \<times> 'sets set) list"
  assumes M_finite: "finite M"
    and M_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M"
  shows "comp_timpl_closure M (set TI) = timpl_closure_set M (set TI)"
using lfp_while''[OF timpls_Un_mono[of M "set TI"]]
      timpl_closure_set_finite[OF M_finite M_wf]
      timpl_closure_set_lfp[of M "set TI"]
unfolding comp_timpl_closure_def Let_def by presburger

context
begin

private lemma analyzed_closed_mod_timpls_is_analyzed_closed_timpl_closure_set_aux1:
  fixes M::"('fun,'atom,'sets) prot_terms"
  assumes f: "arity\<^sub>f f = length T" "arity\<^sub>f f > 0" "Ana\<^sub>f f = (K, R)"
    and i: "i < length R"
    and M: "timpl_closure_set M TI \<turnstile>\<^sub>c T ! (R ! i)"
    and m: "Fun (Fu f) T \<in> M"
    and t: "Fun (Fu f) S \<in> timpl_closure (Fun (Fu f) T) TI"
  shows "timpl_closure_set M TI \<turnstile>\<^sub>c S ! (R ! i)"
proof -
  have "R ! i < length T" using i Ana\<^sub>f_assm2_alt[OF f(3)] f(1) by simp
  thus ?thesis
    using timpl_closure_Fun_inv'(1,2)[OF t] intruder_synth_timpl_closure'[OF M]
    by presburger
qed

private lemma analyzed_closed_mod_timpls_is_analyzed_closed_timpl_closure_set_aux2:
  fixes M::"('fun,'atom,'sets) prot_terms"
  assumes M: "\<forall>s \<in> set (snd (Ana m)). timpl_closure_set M TI \<turnstile>\<^sub>c s"
    and m: "m \<in> M"
    and t: "t \<in> timpl_closure m TI"
    and s: "s \<in> set (snd (Ana t))"
  shows "timpl_closure_set M TI \<turnstile>\<^sub>c s"
proof -
  obtain f S K N where fS: "t = Fun (Fu f) S" "arity\<^sub>f f = length S" "0 < arity\<^sub>f f"
      and Ana_f: "Ana\<^sub>f f = (K, N)"
      and Ana_t: "Ana t = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) S, map ((!) S) N)"
    using Ana_nonempty_inv[of t] s by fastforce
  then obtain T where T: "m = Fun (Fu f) T" "length T = length S"
    using t timpl_closure_Fu_inv'[of f S m TI]
    by moura
  hence Ana_m: "Ana m = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T, map ((!) T) N)"
    using fS(2,3) Ana_f by auto

  obtain i where i: "i < length N" "s = S ! (N ! i)"
    using s[unfolded fS(1)] Ana_t[unfolded fS(1)] T(2)
          in_set_conv_nth[of s "map (\<lambda>i. S ! i) N"]
    by auto
  hence "timpl_closure_set M TI \<turnstile>\<^sub>c T ! (N ! i)"
    using M[unfolded T(1)] Ana_m[unfolded T(1)] T(2)
    by simp
  thus ?thesis
    using analyzed_closed_mod_timpls_is_analyzed_closed_timpl_closure_set_aux1[
            OF fS(2)[unfolded T(2)[symmetric]] fS(3) Ana_f
               i(1) _ m[unfolded T(1)] t[unfolded fS(1) T(1)]]
          i(2)
    by argo
qed

lemma analyzed_closed_mod_timpls_is_analyzed_timpl_closure_set:
  fixes M::"('fun,'atom,'sets) prot_term list"
  assumes TI': "set TI' = {(a,b) \<in> (set TI)\<^sup>+. a \<noteq> b}"
    and M_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)"
  shows "analyzed_closed_mod_timpls M TI' \<longleftrightarrow> analyzed (timpl_closure_set (set M) (set TI))"
    (is "?A \<longleftrightarrow> ?B")
proof
  let ?C = "\<forall>t \<in> timpl_closure_set (set M) (set TI).
              analyzed_in t (timpl_closure_set (set M) (set TI))"

  let ?P = "\<lambda>T. \<forall>t \<in> set T. timpl_closure_set (set M) (set TI) \<turnstile>\<^sub>c t"
  let ?Q = "\<lambda>t. \<forall>s \<in> comp_timpl_closure {t} (set TI'). case Ana s of (K, R) \<Rightarrow> ?P K \<longrightarrow> ?P R"
  
  note defs = analyzed_closed_mod_timpls_def analyzed_in_code
  note 0 = intruder_synth_mod_timpls_is_synth_timpl_closure_set[OF TI', of M]
  note 1 = timpl_closure_set_is_timpl_closure_union[of _ "set TI"]

  have 2: "comp_timpl_closure {t} (set TI') = timpl_closure_set {t} (set TI)"
    when t: "t \<in> set M" "wf\<^sub>t\<^sub>r\<^sub>m t" for t
    using t timpl_closure_set_timpls_trancl_eq'[of "{t}" "set TI"]
          comp_timpl_closure_is_timpl_closure_set[of "{t}" TI']
    unfolding TI'[symmetric]
    by blast
  hence 3: "comp_timpl_closure {t} (set TI') \<subseteq> timpl_closure_set (set M) (set TI)"
    when t: "t \<in> set M" "wf\<^sub>t\<^sub>r\<^sub>m t" for t
    using t timpl_closure_set_mono[of "{t}" "set M"]
    by fast

  have ?A when C: ?C
    unfolding analyzed_closed_mod_timpls_def
              intruder_synth_mod_timpls_is_synth_timpl_closure_set[OF TI']
              list_all_iff Let_def
  proof (intro ballI)
    fix t assume t: "t \<in> set M"
    show "if ?P (fst (Ana t)) then ?P (snd (Ana t)) else ?Q t" (is ?R)
    proof (cases "?P (fst (Ana t))")
      case True
      hence "?P (snd (Ana t))"
        using C timpl_closure_setI[OF t, of "set TI"] prod.exhaust_sel
        unfolding analyzed_in_def by blast
      thus ?thesis using True by simp
    next
      case False
      have "?Q t" using 3[OF t] C M_wf t unfolding analyzed_in_def by auto
      thus ?thesis using False by argo
    qed
  qed
  thus ?A when B: ?B using B analyzed_is_all_analyzed_in by metis

  have ?C when A: ?A unfolding analyzed_in_def Let_def
  proof (intro ballI allI impI; elim conjE)
    fix t K T s
    assume t: "t \<in> timpl_closure_set (set M) (set TI)"
      and s: "s \<in> set T"
      and Ana_t: "Ana t = (K, T)"
      and K: "\<forall>k \<in> set K. timpl_closure_set (set M) (set TI) \<turnstile>\<^sub>c k"

    obtain m where m: "m \<in> set M" "t \<in> timpl_closure m (set TI)"
      using timpl_closure_set_is_timpl_closure_union t by moura

    show "timpl_closure_set (set M) (set TI) \<turnstile>\<^sub>c s"
    proof (cases "\<forall>k \<in> set (fst (Ana m)). timpl_closure_set (set M) (set TI) \<turnstile>\<^sub>c k")
      case True
      hence *: "\<forall>r \<in> set (snd (Ana m)). timpl_closure_set (set M) (set TI) \<turnstile>\<^sub>c r"
        using m(1) A
        unfolding analyzed_closed_mod_timpls_def
                  intruder_synth_mod_timpls_is_synth_timpl_closure_set[OF TI']
                  list_all_iff
        by simp

      show ?thesis
        using K s Ana_t A
              analyzed_closed_mod_timpls_is_analyzed_closed_timpl_closure_set_aux2[OF * m]
        by simp
    next
      case False
      hence "?Q m"
        using m(1) A
        unfolding analyzed_closed_mod_timpls_def
                  intruder_synth_mod_timpls_is_synth_timpl_closure_set[OF TI']
                  list_all_iff Let_def
        by auto 
      moreover have "comp_timpl_closure {m} (set TI') = timpl_closure m (set TI)"
        using 2[OF m(1)] timpl_closureton_is_timpl_closure M_wf m(1)
        by blast
      ultimately show ?thesis
        using m(2) K s Ana_t
        unfolding Let_def by auto
    qed
  qed
  thus ?B when A: ?A using A analyzed_is_all_analyzed_in by metis
qed

lemma analyzed_closed_mod_timpls'_is_analyzed_timpl_closure_set:
  fixes M::"('fun,'atom,'sets) prot_term list"
  assumes M_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)"
  shows "analyzed_closed_mod_timpls' M TI \<longleftrightarrow> analyzed (timpl_closure_set (set M) (set TI))"
    (is "?A \<longleftrightarrow> ?B")
proof
  let ?C = "\<forall>t \<in> timpl_closure_set (set M) (set TI). analyzed_in t (timpl_closure_set (set M) (set TI))"

  let ?P = "\<lambda>T. \<forall>t \<in> set T. timpl_closure_set (set M) (set TI) \<turnstile>\<^sub>c t"
  let ?Q = "\<lambda>t. \<forall>s \<in> comp_timpl_closure {t} (set TI). case Ana s of (K, R) \<Rightarrow> ?P K \<longrightarrow> ?P R"
  
  note defs = analyzed_closed_mod_timpls'_def analyzed_in_code
  note 0 = intruder_synth_mod_timpls'_is_synth_timpl_closure_set[of M TI]
  note 1 = timpl_closure_set_is_timpl_closure_union[of _ "set TI"]

  have 2: "comp_timpl_closure {t} (set TI) = timpl_closure_set {t} (set TI)"
    when t: "t \<in> set M" "wf\<^sub>t\<^sub>r\<^sub>m t" for t
    using t timpl_closure_set_timpls_trancl_eq[of "{t}" "set TI"]
          comp_timpl_closure_is_timpl_closure_set[of "{t}"]
    by blast
  hence 3: "comp_timpl_closure {t} (set TI) \<subseteq> timpl_closure_set (set M) (set TI)"
    when t: "t \<in> set M" "wf\<^sub>t\<^sub>r\<^sub>m t" for t
    using t timpl_closure_set_mono[of "{t}" "set M"]
    by fast

  have ?A when C: ?C
    unfolding analyzed_closed_mod_timpls'_def
              intruder_synth_mod_timpls'_is_synth_timpl_closure_set
              list_all_iff Let_def
  proof (intro ballI)
    fix t assume t: "t \<in> set M"
    show "if ?P (fst (Ana t)) then ?P (snd (Ana t)) else ?Q t" (is ?R)
    proof (cases "?P (fst (Ana t))")
      case True
      hence "?P (snd (Ana t))"
        using C timpl_closure_setI[OF t, of "set TI"] prod.exhaust_sel
        unfolding analyzed_in_def by blast
      thus ?thesis using True by simp
    next
      case False
      have "?Q t" using 3[OF t] C M_wf t unfolding analyzed_in_def by auto
      thus ?thesis using False by argo
    qed
  qed
  thus ?A when B: ?B using B analyzed_is_all_analyzed_in by metis

  have ?C when A: ?A unfolding analyzed_in_def Let_def
  proof (intro ballI allI impI; elim conjE)
    fix t K T s
    assume t: "t \<in> timpl_closure_set (set M) (set TI)"
      and s: "s \<in> set T"
      and Ana_t: "Ana t = (K, T)"
      and K: "\<forall>k \<in> set K. timpl_closure_set (set M) (set TI) \<turnstile>\<^sub>c k"

    obtain m where m: "m \<in> set M" "t \<in> timpl_closure m (set TI)"
      using timpl_closure_set_is_timpl_closure_union t by moura

    show "timpl_closure_set (set M) (set TI) \<turnstile>\<^sub>c s"
    proof (cases "\<forall>k \<in> set (fst (Ana m)). timpl_closure_set (set M) (set TI) \<turnstile>\<^sub>c k")
      case True
      hence *: "\<forall>r \<in> set (snd (Ana m)). timpl_closure_set (set M) (set TI) \<turnstile>\<^sub>c r"
        using m(1) A
        unfolding analyzed_closed_mod_timpls'_def
                  intruder_synth_mod_timpls'_is_synth_timpl_closure_set
                  list_all_iff
        by simp

      show ?thesis
        using K s Ana_t A
              analyzed_closed_mod_timpls_is_analyzed_closed_timpl_closure_set_aux2[OF * m]
        by simp
    next
      case False
      hence "?Q m"
        using m(1) A
        unfolding analyzed_closed_mod_timpls'_def
                  intruder_synth_mod_timpls'_is_synth_timpl_closure_set
                  list_all_iff Let_def
        by auto 
      moreover have "comp_timpl_closure {m} (set TI) = timpl_closure m (set TI)"
        using 2[OF m(1)] timpl_closureton_is_timpl_closure M_wf m(1)
        by blast
      ultimately show ?thesis
        using m(2) K s Ana_t
        unfolding Let_def by auto
    qed
  qed
  thus ?B when A: ?A using A analyzed_is_all_analyzed_in by metis
qed

end

end

end
