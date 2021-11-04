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

(*  Title:      Term_Abstraction.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
*)

section\<open>Term Abstraction\<close>
theory Term_Abstraction
  imports Transactions
begin

subsection \<open>Definitions\<close>
fun to_abs ("\<alpha>\<^sub>0") where
  "\<alpha>\<^sub>0 [] _ = {}"
| "\<alpha>\<^sub>0 ((Fun (Val m) [],Fun (Set s) S)#D) n =
    (if m = n then insert s (\<alpha>\<^sub>0 D n) else \<alpha>\<^sub>0 D n)"
| "\<alpha>\<^sub>0 (_#D) n = \<alpha>\<^sub>0 D n"

fun abs_apply_term (infixl "\<cdot>\<^sub>\<alpha>" 67) where
  "Var x \<cdot>\<^sub>\<alpha> \<alpha> = Var x"
| "Fun (Val n) T \<cdot>\<^sub>\<alpha> \<alpha> = Fun (Abs (\<alpha> n)) (map (\<lambda>t. t \<cdot>\<^sub>\<alpha> \<alpha>) T)"
| "Fun f T \<cdot>\<^sub>\<alpha> \<alpha> = Fun f (map (\<lambda>t. t \<cdot>\<^sub>\<alpha> \<alpha>) T)"

definition abs_apply_list (infixl "\<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t" 67) where
  "M \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha> \<equiv> map (\<lambda>t. t \<cdot>\<^sub>\<alpha> \<alpha>) M"

definition abs_apply_terms (infixl "\<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t" 67) where
  "M \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha> \<equiv> (\<lambda>t. t \<cdot>\<^sub>\<alpha> \<alpha>) ` M"

definition abs_apply_pairs (infixl "\<cdot>\<^sub>\<alpha>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s" 67) where
  "F \<cdot>\<^sub>\<alpha>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<alpha> \<equiv> map (\<lambda>(s,t). (s \<cdot>\<^sub>\<alpha> \<alpha>, t \<cdot>\<^sub>\<alpha> \<alpha>)) F"

definition abs_apply_strand_step (infixl "\<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>t\<^sub>p" 67) where
  "s \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>t\<^sub>p \<alpha> \<equiv> (case s of
    (l,send\<langle>t\<rangle>) \<Rightarrow> (l,send\<langle>t \<cdot>\<^sub>\<alpha> \<alpha>\<rangle>)
  | (l,receive\<langle>t\<rangle>) \<Rightarrow> (l,receive\<langle>t \<cdot>\<^sub>\<alpha> \<alpha>\<rangle>)
  | (l,\<langle>ac: t \<doteq> t'\<rangle>) \<Rightarrow> (l,\<langle>ac: (t \<cdot>\<^sub>\<alpha> \<alpha>) \<doteq> (t' \<cdot>\<^sub>\<alpha> \<alpha>)\<rangle>)
  | (l,insert\<langle>t,t'\<rangle>) \<Rightarrow> (l,insert\<langle>t \<cdot>\<^sub>\<alpha> \<alpha>,t' \<cdot>\<^sub>\<alpha> \<alpha>\<rangle>)
  | (l,delete\<langle>t,t'\<rangle>) \<Rightarrow> (l,delete\<langle>t \<cdot>\<^sub>\<alpha> \<alpha>,t' \<cdot>\<^sub>\<alpha> \<alpha>\<rangle>)
  | (l,\<langle>ac: t \<in> t'\<rangle>) \<Rightarrow> (l,\<langle>ac: (t \<cdot>\<^sub>\<alpha> \<alpha>) \<in> (t' \<cdot>\<^sub>\<alpha> \<alpha>)\<rangle>)
  | (l,\<forall>X\<langle>\<or>\<noteq>: F \<or>\<notin>: F'\<rangle>) \<Rightarrow> (l,\<forall>X\<langle>\<or>\<noteq>: (F \<cdot>\<^sub>\<alpha>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<alpha>) \<or>\<notin>: (F' \<cdot>\<^sub>\<alpha>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<alpha>)\<rangle>))"

definition abs_apply_strand (infixl "\<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>t" 67) where
  "S \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>t \<alpha> \<equiv> map (\<lambda>x. x \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>t\<^sub>p \<alpha>) S"


subsection \<open>Lemmata\<close>
lemma to_abs_alt_def:
  "\<alpha>\<^sub>0 D n = {s. \<exists>S. (Fun (Val n) [], Fun (Set s) S) \<in> set D}"
by (induct D n rule: to_abs.induct) auto

lemma abs_term_apply_const[simp]:
  "is_Val f \<Longrightarrow> Fun f [] \<cdot>\<^sub>\<alpha> a = Fun (Abs (a (the_Val f))) []"
  "\<not>is_Val f \<Longrightarrow> Fun f [] \<cdot>\<^sub>\<alpha> a = Fun f []"
by (cases f; auto)+

lemma abs_fv: "fv (t \<cdot>\<^sub>\<alpha> a) = fv t"
by (induct t a rule: abs_apply_term.induct) auto

lemma abs_eq_if_no_Val:
  assumes "\<forall>f \<in> funs_term t. \<not>is_Val f"
  shows "t \<cdot>\<^sub>\<alpha> a = t \<cdot>\<^sub>\<alpha> b"
using assms
proof (induction t)
  case (Fun f T) thus ?case by (cases f) simp_all
qed simp

lemma abs_list_set_is_set_abs_set: "set (M \<cdot>\<^sub>\<alpha>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<alpha>) = (set M) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>"
unfolding abs_apply_list_def abs_apply_terms_def by simp

lemma abs_set_empty[simp]: "{} \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha> = {}"
unfolding abs_apply_terms_def by simp

lemma abs_in:
  assumes "t \<in> M"
  shows "t \<cdot>\<^sub>\<alpha> \<alpha> \<in> M \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>"
using assms unfolding abs_apply_terms_def
by (induct t \<alpha> rule: abs_apply_term.induct) blast+

lemma abs_set_union: "(A \<union> B) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a = (A \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a) \<union> (B \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a)"
unfolding abs_apply_terms_def
by auto

lemma abs_subterms: "subterms (t \<cdot>\<^sub>\<alpha> \<alpha>) = subterms t \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t \<alpha>"
proof (induction t)
  case (Fun f T) thus ?case by (cases f) (auto simp add: abs_apply_terms_def)
qed (simp add: abs_apply_terms_def)

lemma abs_subterms_in: "s \<in> subterms t \<Longrightarrow> s \<cdot>\<^sub>\<alpha> a \<in> subterms (t \<cdot>\<^sub>\<alpha> a)"
proof (induction t)
  case (Fun f T) thus ?case by (cases f) auto
qed simp

lemma abs_ik_append: "(ik\<^sub>s\<^sub>s\<^sub>t (A@B) \<cdot>\<^sub>s\<^sub>e\<^sub>t I) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a = (ik\<^sub>s\<^sub>s\<^sub>t A \<cdot>\<^sub>s\<^sub>e\<^sub>t I) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a \<union> (ik\<^sub>s\<^sub>s\<^sub>t B \<cdot>\<^sub>s\<^sub>e\<^sub>t I) \<cdot>\<^sub>\<alpha>\<^sub>s\<^sub>e\<^sub>t a"
unfolding abs_apply_terms_def ik\<^sub>s\<^sub>s\<^sub>t_def
by auto

lemma to_abs_in:
  assumes "(Fun (Val n) [], Fun (Set s) []) \<in> set D"
  shows "s \<in> \<alpha>\<^sub>0 D n"
using assms by (induct rule: to_abs.induct) auto

lemma to_abs_empty_iff_notin_db:
  "Fun (Val n) [] \<cdot>\<^sub>\<alpha> \<alpha>\<^sub>0 D = Fun (Abs {}) [] \<longleftrightarrow> (\<nexists>s S. (Fun (Val n) [], Fun (Set s) S) \<in> set D)"
by (simp add: to_abs_alt_def)

lemma to_abs_list_insert:
  assumes "Fun (Val n) [] \<noteq> t"
  shows "\<alpha>\<^sub>0 D n = \<alpha>\<^sub>0 (List.insert (t,s) D) n"
using assms to_abs_alt_def[of D n] to_abs_alt_def[of "List.insert (t,s) D" n]
by auto

lemma to_abs_list_insert':
  "insert s (\<alpha>\<^sub>0 D n) = \<alpha>\<^sub>0 (List.insert (Fun (Val n) [], Fun (Set s) S) D) n"
using to_abs_alt_def[of D n]
      to_abs_alt_def[of "List.insert (Fun (Val n) [], Fun (Set s) S) D" n]
by auto

lemma to_abs_list_remove_all:
  assumes "Fun (Val n) [] \<noteq> t"
  shows "\<alpha>\<^sub>0 D n = \<alpha>\<^sub>0 (List.removeAll (t,s) D) n"
using assms to_abs_alt_def[of D n] to_abs_alt_def[of "List.removeAll (t,s) D" n]
by auto

lemma to_abs_list_remove_all':
  "\<alpha>\<^sub>0 D n - {s} = \<alpha>\<^sub>0 (filter (\<lambda>d. \<nexists>S. d = (Fun (Val n) [], Fun (Set s) S)) D) n"
using to_abs_alt_def[of D n]
      to_abs_alt_def[of "filter (\<lambda>d. \<nexists>S. d = (Fun (Val n) [], Fun (Set s) S)) D" n]
by auto

lemma to_abs_db\<^sub>s\<^sub>s\<^sub>t_append:
  assumes "\<forall>u s. insert\<langle>u, s\<rangle> \<in> set B \<longrightarrow> Fun (Val n) [] \<noteq> u \<cdot> \<I>"
    and "\<forall>u s. delete\<langle>u, s\<rangle> \<in> set B \<longrightarrow> Fun (Val n) [] \<noteq> u \<cdot> \<I>"
  shows "\<alpha>\<^sub>0 (db'\<^sub>s\<^sub>s\<^sub>t A \<I> D) n = \<alpha>\<^sub>0 (db'\<^sub>s\<^sub>s\<^sub>t (A@B) \<I> D) n"
using assms
proof (induction B rule: List.rev_induct)
  case (snoc b B)
  hence IH: "\<alpha>\<^sub>0 (db'\<^sub>s\<^sub>s\<^sub>t A \<I> D) n = \<alpha>\<^sub>0 (db'\<^sub>s\<^sub>s\<^sub>t (A@B) \<I> D) n" by auto
  have *: "\<forall>u s. b = insert\<langle>u,s\<rangle> \<longrightarrow> Fun (Val n) [] \<noteq> u \<cdot> \<I>"
          "\<forall>u s. b = delete\<langle>u,s\<rangle> \<longrightarrow> Fun (Val n) [] \<noteq> u \<cdot> \<I>"
    using snoc.prems by simp_all
  show ?case
  proof (cases b)
    case (Insert u s)
    hence **: "db'\<^sub>s\<^sub>s\<^sub>t (A@B@[b]) \<I> D = List.insert (u \<cdot> \<I>,s \<cdot> \<I>) (db'\<^sub>s\<^sub>s\<^sub>t (A@B) \<I> D)"
      using db\<^sub>s\<^sub>s\<^sub>t_append[of "A@B" "[b]"] by simp
    have "Fun (Val n) [] \<noteq> u \<cdot> \<I>" using *(1) Insert by auto
    thus ?thesis using IH ** to_abs_list_insert by metis
  next
    case (Delete u s)
    hence **: "db'\<^sub>s\<^sub>s\<^sub>t (A@B@[b]) \<I> D = List.removeAll (u \<cdot> \<I>,s \<cdot> \<I>) (db'\<^sub>s\<^sub>s\<^sub>t (A@B) \<I> D)"
      using db\<^sub>s\<^sub>s\<^sub>t_append[of "A@B" "[b]"] by simp
    have "Fun (Val n) [] \<noteq> u \<cdot> \<I>" using *(2) Delete by auto
    thus ?thesis using IH ** to_abs_list_remove_all by metis
  qed (simp_all add: db\<^sub>s\<^sub>s\<^sub>t_no_upd_append[of "[b]" "A@B"] IH)
qed simp

lemma to_abs_neq_imp_db_update:
  assumes "\<alpha>\<^sub>0 (db\<^sub>s\<^sub>s\<^sub>t A I) n \<noteq> \<alpha>\<^sub>0 (db\<^sub>s\<^sub>s\<^sub>t (A@B) I) n"
  shows "\<exists>u s. u \<cdot> I = Fun (Val n) [] \<and> (insert\<langle>u,s\<rangle> \<in> set B \<or> delete\<langle>u,s\<rangle> \<in> set B)"
proof -
  { fix D have ?thesis when "\<alpha>\<^sub>0 D n \<noteq> \<alpha>\<^sub>0 (db'\<^sub>s\<^sub>s\<^sub>t B I D) n" using that
    proof (induction B I D rule: db'\<^sub>s\<^sub>s\<^sub>t.induct)
      case 2 thus ?case
        by (metis db'\<^sub>s\<^sub>s\<^sub>t.simps(2) list.set_intros(1,2) subst_apply_pair_pair to_abs_list_insert)
    next
      case 3 thus ?case
        by (metis db'\<^sub>s\<^sub>s\<^sub>t.simps(3) list.set_intros(1,2) subst_apply_pair_pair to_abs_list_remove_all)
    qed simp_all
  } thus ?thesis using assms by (metis db\<^sub>s\<^sub>s\<^sub>t_append db\<^sub>s\<^sub>s\<^sub>t_def)
qed

lemma abs_term_subst_eq:
  fixes \<delta> \<theta>::"(('a,'b,'c) prot_fun, ('d,'e prot_atom) term \<times> nat) subst"
  assumes "\<forall>x \<in> fv t. \<delta> x \<cdot>\<^sub>\<alpha> a = \<theta> x \<cdot>\<^sub>\<alpha> b"
    and "\<nexists>n T. Fun (Val n) T \<in> subterms t"
  shows "t \<cdot> \<delta> \<cdot>\<^sub>\<alpha> a = t \<cdot> \<theta> \<cdot>\<^sub>\<alpha> b"
using assms
proof (induction t)
  case (Fun f T) thus ?case
  proof (cases f)
    case (Val n)
    hence False using Fun.prems(2) by blast
    thus ?thesis by metis
  qed auto
qed simp

lemma abs_term_subst_eq':
  fixes \<delta> \<theta>::"(('a,'b,'c) prot_fun, ('d,'e prot_atom) term \<times> nat) subst"
  assumes "\<forall>x \<in> fv t. \<delta> x \<cdot>\<^sub>\<alpha> a = \<theta> x"
    and "\<nexists>n T. Fun (Val n) T \<in> subterms t"
  shows "t \<cdot> \<delta> \<cdot>\<^sub>\<alpha> a = t \<cdot> \<theta>"
using assms
proof (induction t)
  case (Fun f T) thus ?case
  proof (cases f)
    case (Val n)
    hence False using Fun.prems(2) by blast
    thus ?thesis by metis
  qed auto
qed simp

lemma abs_val_in_funs_term:
  assumes "f \<in> funs_term t" "is_Val f"
  shows "Abs (\<alpha> (the_Val f)) \<in> funs_term (t \<cdot>\<^sub>\<alpha> \<alpha>)"
using assms by (induct t \<alpha> rule: abs_apply_term.induct) auto

end
