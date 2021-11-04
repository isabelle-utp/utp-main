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

(*  Title:      Term_Variants.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
*)

section\<open>Term Variants\<close>
theory Term_Variants
  imports Stateful_Protocol_Composition_and_Typing.Intruder_Deduction
begin

fun term_variants where
  "term_variants P (Var x) = [Var x]"
| "term_variants P (Fun f T) = (
  let S = product_lists (map (term_variants P) T)
  in map (Fun f) S@concat (map (\<lambda>g. map (Fun g) S) (P f)))"

inductive term_variants_pred where
  term_variants_Var:
  "term_variants_pred P (Var x) (Var x)"
| term_variants_P:
  "\<lbrakk>length T = length S; \<And>i. i < length T \<Longrightarrow> term_variants_pred P (T ! i) (S ! i); g \<in> set (P f)\<rbrakk>
   \<Longrightarrow> term_variants_pred P (Fun f T) (Fun g S)"
| term_variants_Fun:
  "\<lbrakk>length T = length S; \<And>i. i < length T \<Longrightarrow> term_variants_pred P (T ! i) (S ! i)\<rbrakk>
   \<Longrightarrow> term_variants_pred P (Fun f T) (Fun f S)"

lemma term_variants_pred_inv:
  assumes "term_variants_pred P (Fun f T) (Fun h S)"
  shows "length T = length S"
    and "\<And>i. i < length T \<Longrightarrow> term_variants_pred P (T ! i) (S ! i)"
    and "f \<noteq> h \<Longrightarrow> h \<in> set (P f)"
using assms by (auto elim: term_variants_pred.cases)

lemma term_variants_pred_inv':
  assumes "term_variants_pred P (Fun f T) t"
  shows "is_Fun t"
    and "length T = length (args t)"
    and "\<And>i. i < length T \<Longrightarrow> term_variants_pred P (T ! i) (args t ! i)"
    and "f \<noteq> the_Fun t \<Longrightarrow> the_Fun t \<in> set (P f)"
    and "P \<equiv> (\<lambda>_. [])(g := [h]) \<Longrightarrow> f \<noteq> the_Fun t \<Longrightarrow> f = g \<and> the_Fun t = h"
using assms by (auto elim: term_variants_pred.cases)

lemma term_variants_pred_inv'':
  assumes "term_variants_pred P t (Fun f T)"
  shows "is_Fun t"
    and "length T = length (args t)"
    and "\<And>i. i < length T \<Longrightarrow> term_variants_pred P (args t ! i) (T ! i)"
    and "f \<noteq> the_Fun t \<Longrightarrow> f \<in> set (P (the_Fun t))"
    and "P \<equiv> (\<lambda>_. [])(g := [h]) \<Longrightarrow> f \<noteq> the_Fun t \<Longrightarrow> f = h \<and> the_Fun t = g"
using assms by (auto elim: term_variants_pred.cases)

lemma term_variants_pred_inv_Var:
  "term_variants_pred P (Var x) t \<longleftrightarrow> t = Var x"
  "term_variants_pred P t (Var x) \<longleftrightarrow> t = Var x"
by (auto intro: term_variants_Var elim: term_variants_pred.cases)

lemma term_variants_pred_inv_const:
  "term_variants_pred P (Fun c []) t \<longleftrightarrow> ((\<exists>g \<in> set (P c). t = Fun g []) \<or> (t = Fun c []))"
by (auto intro: term_variants_P term_variants_Fun elim: term_variants_pred.cases)

lemma term_variants_pred_refl: "term_variants_pred P t t"
by (induct t) (auto intro: term_variants_pred.intros)

lemma term_variants_pred_refl_inv:
  assumes st: "term_variants_pred P s t"
    and P: "\<forall>f. \<forall>g \<in> set (P f). f = g"
  shows "s = t"
  using st P
proof (induction s t rule: term_variants_pred.induct)
case (term_variants_Var P x) thus ?case by blast
next
  case (term_variants_P T S P g f)
  hence "T ! i = S ! i" when i: "i < length T" for i using i by blast
  hence "T = S" using term_variants_P.hyps(1) by (simp add: nth_equalityI)
  thus ?case using term_variants_P.prems term_variants_P.hyps(3) by fast
next
  case (term_variants_Fun T S P f)
  hence "T ! i = S ! i" when i: "i < length T" for i using i by blast
  hence "T = S" using term_variants_Fun.hyps(1) by (simp add: nth_equalityI)
  thus ?case by fast
qed

lemma term_variants_pred_const:
  assumes "b \<in> set (P a)"
  shows "term_variants_pred P (Fun a []) (Fun b [])"
using term_variants_P[of "[]" "[]"] assms by simp

lemma term_variants_pred_const_cases:
  "P a \<noteq> [] \<Longrightarrow> term_variants_pred P (Fun a []) t \<longleftrightarrow>
                 (t = Fun a [] \<or> (\<exists>b \<in> set (P a). t = Fun b []))"
  "P a = [] \<Longrightarrow> term_variants_pred P (Fun a []) t \<longleftrightarrow> t = Fun a []"
using term_variants_pred_inv_const[of P] by auto

lemma term_variants_pred_param:
  assumes "term_variants_pred P t s"
    and fg: "f = g \<or> g \<in> set (P f)"
  shows "term_variants_pred P (Fun f (S@t#T)) (Fun g (S@s#T))"
proof -
  have 1: "length (S@t#T) = length (S@s#T)" by simp
  
  have "term_variants_pred P (T ! i) (T ! i)" "term_variants_pred P (S ! i) (S ! i)" for i
    by (metis term_variants_pred_refl)+
  hence 2: "term_variants_pred P ((S@t#T) ! i) ((S@s#T) ! i)" for i
    by (simp add: assms nth_Cons' nth_append)

  show ?thesis by (metis term_variants_Fun[OF 1 2] term_variants_P[OF 1 2] fg)
qed

lemma term_variants_pred_Cons:
  assumes t: "term_variants_pred P t s"
    and T: "term_variants_pred P (Fun f T) (Fun f S)"
    and fg: "f = g \<or> g \<in> set (P f)"
  shows "term_variants_pred P (Fun f (t#T)) (Fun g (s#S))"
proof -
  have 1: "length (t#T) = length (s#S)"
       and "\<And>i. i < length T \<Longrightarrow> term_variants_pred P (T ! i) (S ! i)"
    using term_variants_pred_inv[OF T] by simp_all
  hence 2: "\<And>i. i < length (t#T) \<Longrightarrow> term_variants_pred P ((t#T) ! i) ((s#S) ! i)"
    by (metis t One_nat_def diff_less length_Cons less_Suc_eq less_imp_diff_less nth_Cons'
              zero_less_Suc) 

  show ?thesis using 1 2 fg by (auto intro: term_variants_pred.intros)
qed

lemma term_variants_pred_dense:
  fixes P Q::"'a set" and fs gs::"'a list"
  defines "P_fs x \<equiv> if x \<in> P then fs else []"
    and "P_gs x \<equiv> if x \<in> P then gs else []"
    and "Q_fs x \<equiv> if x \<in> Q then fs else []"
  assumes ut: "term_variants_pred P_fs u t"
    and g: "g \<in> Q" "g \<in> set gs"
  shows "\<exists>s. term_variants_pred P_gs u s \<and> term_variants_pred Q_fs s t"
proof -
  define F where "F \<equiv> \<lambda>(P::'a set) (fs::'a list) x. if x \<in> P then fs else []"

  show ?thesis using ut g P_fs_def unfolding P_gs_def Q_fs_def
  proof (induction P_fs u t arbitrary: g gs rule: term_variants_pred.induct)
    case (term_variants_Var P h x) thus ?case
      by (auto intro: term_variants_pred.term_variants_Var)
  next
    case (term_variants_P T S P' h' h g gs)
    note hyps = term_variants_P.hyps(1,2,4,5,6,7)
    note IH = term_variants_P.hyps(3)

    have "\<exists>s. term_variants_pred (F P gs) (T ! i) s \<and> term_variants_pred (F Q fs) s (S ! i)"
      when i: "i < length T" for i
      using IH[OF i hyps(4,5,6)] unfolding F_def by presburger
    then obtain U where U:
        "length T = length U" "\<And>i. i < length T \<Longrightarrow> term_variants_pred (F P gs) (T ! i) (U ! i)"
        "length U = length S" "\<And>i. i < length U \<Longrightarrow> term_variants_pred (F Q fs) (U ! i) (S ! i)"
      using hyps(1) Skolem_list_nth[of _ "\<lambda>i s. term_variants_pred (F P gs) (T ! i) s \<and>
                                                term_variants_pred (F Q fs) s (S ! i)"]
      by moura

    show ?case
      using term_variants_pred.term_variants_P[OF U(1,2), of g h]
            term_variants_pred.term_variants_P[OF U(3,4), of h' g]
            hyps(3)[unfolded hyps(6)] hyps(4,5)
      unfolding F_def by force
  next
    case (term_variants_Fun T S P' h' g gs)
    note hyps = term_variants_Fun.hyps(1,2,4,5,6)
    note IH = term_variants_Fun.hyps(3)

    have "\<exists>s. term_variants_pred (F P gs) (T ! i) s \<and> term_variants_pred (F Q fs) s (S ! i)"
      when i: "i < length T" for i
      using IH[OF i hyps(3,4,5)] unfolding F_def by presburger
    then obtain U where U:
        "length T = length U" "\<And>i. i < length T \<Longrightarrow> term_variants_pred (F P gs) (T ! i) (U ! i)"
        "length U = length S" "\<And>i. i < length U \<Longrightarrow> term_variants_pred (F Q fs) (U ! i) (S ! i)"
      using hyps(1) Skolem_list_nth[of _ "\<lambda>i s. term_variants_pred (F P gs) (T ! i) s \<and>
                                                term_variants_pred (F Q fs) s (S ! i)"]
      by moura
    
    thus ?case
      using term_variants_pred.term_variants_Fun[OF U(1,2)]
            term_variants_pred.term_variants_Fun[OF U(3,4)]
      unfolding F_def by meson
  qed
qed

lemma term_variants_pred_dense':
  assumes ut: "term_variants_pred ((\<lambda>_. [])(a := [b])) u t"
  shows "\<exists>s. term_variants_pred ((\<lambda>_. [])(a := [c])) u s \<and>
             term_variants_pred ((\<lambda>_. [])(c := [b])) s t"
using ut term_variants_pred_dense[of "{a}" "[b]" u t c "{c}" "[c]"]
unfolding fun_upd_def by simp

lemma term_variants_pred_eq_case:
  fixes t s::"('a,'b) term"
  assumes "term_variants_pred P t s" "\<forall>f \<in> funs_term t. P f = []"
  shows "t = s"
using assms
proof (induction P t s rule: term_variants_pred.induct)
  case (term_variants_Fun T S P f) thus ?case
    using subtermeq_imp_funs_term_subset[OF Fun_param_in_subterms[OF nth_mem], of _ T f]
          nth_equalityI[of T S]
    by blast
qed (simp_all add: term_variants_pred_refl)

lemma term_variants_pred_subst:
  assumes "term_variants_pred P t s"
  shows "term_variants_pred P (t \<cdot> \<delta>) (s \<cdot> \<delta>)"
using assms
proof (induction P t s rule: term_variants_pred.induct)
  case (term_variants_P T S P f g)
  have 1: "length (map (\<lambda>t. t \<cdot> \<delta>) T) = length (map (\<lambda>t. t \<cdot> \<delta>) S)"
    using term_variants_P.hyps
    by simp

  have 2: "term_variants_pred P ((map (\<lambda>t. t \<cdot> \<delta>) T) ! i) ((map (\<lambda>t. t \<cdot> \<delta>) S) ! i)"
    when "i < length (map (\<lambda>t. t \<cdot> \<delta>) T)" for i
    using term_variants_P that
    by fastforce

  show ?case
    using term_variants_pred.term_variants_P[OF 1 2 term_variants_P.hyps(3)]
    by fastforce
next
  case (term_variants_Fun T S P f)
  have 1: "length (map (\<lambda>t. t \<cdot> \<delta>) T) = length (map (\<lambda>t. t \<cdot> \<delta>) S)"
    using term_variants_Fun.hyps
    by simp

  have 2: "term_variants_pred P ((map (\<lambda>t. t \<cdot> \<delta>) T) ! i) ((map (\<lambda>t. t \<cdot> \<delta>) S) ! i)"
    when "i < length (map (\<lambda>t. t \<cdot> \<delta>) T)" for i
    using term_variants_Fun that
    by fastforce

  show ?case
    using term_variants_pred.term_variants_Fun[OF 1 2]
    by fastforce
qed (simp add: term_variants_pred_refl)

lemma term_variants_pred_subst':
  fixes t s::"('a,'b) term" and \<delta>::"('a,'b) subst"
  assumes "term_variants_pred P (t \<cdot> \<delta>) s"
    and "\<forall>x \<in> fv t \<union> fv s. (\<exists>y. \<delta> x = Var y) \<or> (\<exists>f. \<delta> x = Fun f [] \<and> P f = [])"
  shows "\<exists>u. term_variants_pred P t u \<and> s = u \<cdot> \<delta>"
using assms
proof (induction P "t \<cdot> \<delta>" s arbitrary: t rule: term_variants_pred.induct)
  case (term_variants_Var P x g) thus ?case using term_variants_pred_refl by fast
next
  case (term_variants_P T S P g f) show ?case
  proof (cases t)
    case (Var x) thus ?thesis
      using term_variants_P.hyps(4,5) term_variants_P.prems
      by fastforce
  next
    case (Fun h U)
    hence 1: "h = f" "T = map (\<lambda>s. s \<cdot> \<delta>) U" "length U = length T"
      using term_variants_P.hyps(5) by simp_all
    hence 2: "T ! i = U ! i \<cdot> \<delta>" when "i < length T" for i
      using that by simp

    have "\<forall>x \<in> fv (U ! i) \<union> fv (S ! i). (\<exists>y. \<delta> x = Var y) \<or> (\<exists>f. \<delta> x = Fun f [] \<and> P f = [])"
      when "i < length U" for i
      using that Fun term_variants_P.prems term_variants_P.hyps(1) 1(3)
      by force
    hence IH: "\<forall>i < length U. \<exists>u. term_variants_pred P (U ! i) u \<and> S ! i = u \<cdot> \<delta>"
      by (metis 1(3) term_variants_P.hyps(3)[OF _ 2])

    have "\<exists>V. length U = length V \<and> S = map (\<lambda>v. v \<cdot> \<delta>) V \<and>
               (\<forall>i < length U. term_variants_pred P (U ! i) (V ! i))"
      using term_variants_P.hyps(1) 1(3) subst_term_list_obtain[OF IH] by metis
    then obtain V where V: "length U = length V" "S = map (\<lambda>v. v \<cdot> \<delta>) V"
                           "\<And>i. i < length U \<Longrightarrow> term_variants_pred P (U ! i) (V ! i)"
      by moura

    have "term_variants_pred P (Fun f U) (Fun g V)"
      by (metis term_variants_pred.term_variants_P[OF V(1,3) term_variants_P.hyps(4)])
    moreover have "Fun g S = Fun g V \<cdot> \<delta>" using V(2) by simp
    ultimately show ?thesis using term_variants_P.hyps(1,4) Fun 1 by blast
  qed
next
  case (term_variants_Fun T S P f t) show ?case
  proof (cases t)
    case (Var x)
    hence "T = []" "P f = []" using term_variants_Fun.hyps(4) term_variants_Fun.prems by fastforce+
    thus ?thesis using term_variants_pred_refl Var term_variants_Fun.hyps(1,4) by fastforce
  next
    case (Fun h U)
    hence 1: "h = f" "T = map (\<lambda>s. s \<cdot> \<delta>) U" "length U = length T"
      using term_variants_Fun.hyps(4) by simp_all
    hence 2: "T ! i = U ! i \<cdot> \<delta>" when "i < length T" for i
      using that by simp

    have "\<forall>x \<in> fv (U ! i) \<union> fv (S ! i). (\<exists>y. \<delta> x = Var y) \<or> (\<exists>f. \<delta> x = Fun f [] \<and> P f = [])"
      when "i < length U" for i
      using that Fun term_variants_Fun.prems term_variants_Fun.hyps(1) 1(3)
      by force
    hence IH: "\<forall>i < length U. \<exists>u. term_variants_pred P (U ! i) u \<and> S ! i = u \<cdot> \<delta>"
      by (metis 1(3) term_variants_Fun.hyps(3)[OF _ 2 ])

    have "\<exists>V. length U = length V \<and> S = map (\<lambda>v. v \<cdot> \<delta>) V \<and>
               (\<forall>i < length U. term_variants_pred P (U ! i) (V ! i))"
      using term_variants_Fun.hyps(1) 1(3) subst_term_list_obtain[OF IH] by metis
    then obtain V where V: "length U = length V" "S = map (\<lambda>v. v \<cdot> \<delta>) V"
                           "\<And>i. i < length U \<Longrightarrow> term_variants_pred P (U ! i) (V ! i)"
      by moura

    have "term_variants_pred P (Fun f U) (Fun f V)"
      by (metis term_variants_pred.term_variants_Fun[OF V(1,3)])
    moreover have "Fun f S = Fun f V \<cdot> \<delta>" using V(2) by simp
    ultimately show ?thesis using term_variants_Fun.hyps(1) Fun 1 by blast
  qed
qed

lemma term_variants_pred_iff_in_term_variants:
  fixes t::"('a,'b) term"
  shows "term_variants_pred P t s \<longleftrightarrow> s \<in> set (term_variants P t)"
    (is "?A t s \<longleftrightarrow> ?B t s")
proof
  define U where "U \<equiv> \<lambda>P (T::('a,'b) term list). product_lists (map (term_variants P) T)"

  have a:
      "g \<in> set (P f) \<Longrightarrow> set (map (Fun g) (U P T)) \<subseteq> set (term_variants P (Fun f T))"
      "set (map (Fun f) (U P T)) \<subseteq> set (term_variants P (Fun f T))"
    for f P g and T::"('a,'b) term list"
    using term_variants.simps(2)[of P f T]
    unfolding U_def Let_def by auto

  have b: "\<exists>S \<in> set (U P T). s = Fun f S \<or> (\<exists>g \<in> set (P f). s = Fun g S)"
    when "s \<in> set (term_variants P (Fun f T))" for P T f s
    using that by (cases "P f") (auto simp add: U_def Let_def)

  have c: "length T = length S" when "S \<in> set (U P T)" for S P T
    using that unfolding U_def
    by (simp add: in_set_product_lists_length)

  show "?A t s \<Longrightarrow> ?B t s"
  proof (induction P t s rule: term_variants_pred.induct)
    case (term_variants_P T S P g f)
    note hyps = term_variants_P.hyps
    note IH = term_variants_P.IH

    have "S \<in> set (U P T)"
      using IH hyps(1) product_lists_in_set_nth'[of _ S]
      unfolding U_def by simp
    thus ?case using a(1)[of _ P, OF hyps(3)] by auto
  next
    case (term_variants_Fun T S P f)
    note hyps = term_variants_Fun.hyps
    note IH = term_variants_Fun.IH

    have "S \<in> set (U P T)"
      using IH hyps(1) product_lists_in_set_nth'[of _ S]
      unfolding U_def by simp
    thus ?case using a(2)[of f P T] by (cases "P f") auto
  qed (simp add: term_variants_Var)

  show "?B t s \<Longrightarrow> ?A t s"
  proof (induction P t arbitrary: s rule: term_variants.induct)
    case (2 P f T)
    obtain S where S:
        "s = Fun f S \<or> (\<exists>g \<in> set (P f). s = Fun g S)"
        "S \<in> set (U P T)" "length T = length S"
      using c b[OF "2.prems"] by moura

    have "\<forall>i < length T. term_variants_pred P (T ! i) (S ! i)"
      using "2.IH" S product_lists_in_set_nth by (fastforce simp add: U_def)
    thus ?case using S by (auto intro: term_variants_pred.intros)
  qed (simp add: term_variants_Var)
qed

lemma term_variants_pred_finite:
  "finite {s. term_variants_pred P t s}"
using term_variants_pred_iff_in_term_variants[of P t]
by simp

lemma term_variants_pred_fv_eq:
  assumes "term_variants_pred P s t"
  shows "fv s = fv t"
using assms
by (induct rule: term_variants_pred.induct)
   (metis, metis fv_eq_FunI, metis fv_eq_FunI)

lemma (in intruder_model) term_variants_pred_wf_trms:
  assumes "term_variants_pred P s t"
    and "\<And>f g. g \<in> set (P f) \<Longrightarrow> arity f = arity g"
    and "wf\<^sub>t\<^sub>r\<^sub>m s"
  shows "wf\<^sub>t\<^sub>r\<^sub>m t"
using assms
apply (induction rule: term_variants_pred.induct, simp)
by (metis (no_types) wf_trmI wf_trm_arity in_set_conv_nth wf_trm_param_idx)+

lemma term_variants_pred_funs_term:
  assumes "term_variants_pred P s t"
    and "f \<in> funs_term t"
  shows "f \<in> funs_term s \<or> (\<exists>g \<in> funs_term s. f \<in> set (P g))"
  using assms
proof (induction rule: term_variants_pred.induct)
  case (term_variants_P T S P g h) thus ?case
  proof (cases "f = g")
    case False
    then obtain s where "s \<in> set S" "f \<in> funs_term s"
      using funs_term_subterms_eq(1)[of "Fun g S"] term_variants_P.prems by auto
    thus ?thesis
      using term_variants_P.IH term_variants_P.hyps(1) in_set_conv_nth[of s S] by force
  qed simp
next
  case (term_variants_Fun T S P h) thus ?case
  proof (cases "f = h")
    case False
    then obtain s where "s \<in> set S" "f \<in> funs_term s"
      using funs_term_subterms_eq(1)[of "Fun h S"] term_variants_Fun.prems by auto
    thus ?thesis
      using term_variants_Fun.IH term_variants_Fun.hyps(1) in_set_conv_nth[of s S] by force
  qed simp
qed fast

end
