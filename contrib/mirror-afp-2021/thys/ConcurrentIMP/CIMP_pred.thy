(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CIMP_pred
imports
  Main
begin

(* Extra HOL *)

lemma triv: "P \<Longrightarrow> P"
by simp

lemma always_eventually_pigeonhole:
  "(\<forall>i. \<exists>n\<ge>i. \<exists>m\<le>k. P m n) \<longleftrightarrow> (\<exists>m\<le>k::nat. \<forall>i::nat. \<exists>n\<ge>i. P m n)"
proof(induct k)
  case (Suc k) then show ?case
    apply (auto 8 0)
    using le_SucI apply blast
    apply (metis (full_types) le_Suc_eq nat_le_linear order_trans)
    done
qed simp

(*>*)
section\<open> Point-free notation \<close>

text\<open>

\label{sec:cimp-lifted-predicates}

Typically we define predicates as functions of a state. The following
provide a somewhat comfortable point-free imitation of Isabelle/HOL's
operators.

\<close>

abbreviation (input)
  pred_K :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" ("\<langle>_\<rangle>") where
  "\<langle>f\<rangle> \<equiv> \<lambda>s. f"

abbreviation (input)
  pred_not :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("\<^bold>\<not> _" [40] 40) where
  "\<^bold>\<not>a \<equiv> \<lambda>s. \<not>a s"

abbreviation (input)
  pred_conj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "\<^bold>\<and>" 35) where
  "a \<^bold>\<and> b \<equiv> \<lambda>s. a s \<and> b s"

abbreviation (input)
  pred_disj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "\<^bold>\<or>" 30) where
  "a \<^bold>\<or> b \<equiv> \<lambda>s. a s \<or> b s"

abbreviation (input)
  pred_implies :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "\<^bold>\<longrightarrow>" 25) where
  "a \<^bold>\<longrightarrow> b \<equiv> \<lambda>s. a s \<longrightarrow> b s"

abbreviation (input)
  pred_iff :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "\<^bold>\<longleftrightarrow>" 25) where
  "a \<^bold>\<longleftrightarrow> b \<equiv> \<lambda>s. a s \<longleftrightarrow> b s"

abbreviation (input)
  pred_eq :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>=" 40) where
  "a \<^bold>= b \<equiv> \<lambda>s. a s = b s"

abbreviation (input)
  pred_member :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<in>" 40) where
  "a \<^bold>\<in> b \<equiv> \<lambda>s. a s \<in> b s"

abbreviation (input)
  pred_neq :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<noteq>" 40) where
  "a \<^bold>\<noteq> b \<equiv> \<lambda>s. a s \<noteq> b s"

abbreviation (input)
  pred_If :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("(If (_)/ Then (_)/ Else (_))" [0, 0, 10] 10)
  where "If P Then x Else y \<equiv> \<lambda>s. if P s then x s else y s"

abbreviation (input)
  pred_less :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold><" 40) where
  "a \<^bold>< b \<equiv> \<lambda>s. a s < b s"

abbreviation (input)
  pred_le :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<le>" 40) where
  "a \<^bold>\<le> b \<equiv> \<lambda>s. a s \<le> b s"

abbreviation (input)
  pred_plus :: "('a \<Rightarrow> 'b::plus) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "\<^bold>+" 65) where
  "a \<^bold>+ b \<equiv> \<lambda>s. a s + b s"

abbreviation (input)
  pred_minus :: "('a \<Rightarrow> 'b::minus) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "\<^bold>-" 65) where
  "a \<^bold>- b \<equiv> \<lambda>s. a s - b s"

abbreviation (input)
  fun_fanout :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'c" (infix "\<^bold>\<bowtie>" 35) where
  "f \<^bold>\<bowtie> g \<equiv> \<lambda>x. (f x, g x)"

abbreviation (input)
  pred_all :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (binder "\<^bold>\<forall>" 10) where
  "\<^bold>\<forall>x. P x \<equiv> \<lambda>s. \<forall>x. P x s"

abbreviation (input)
  pred_ex :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (binder "\<^bold>\<exists>" 10) where
  "\<^bold>\<exists>x. P x \<equiv> \<lambda>s. \<exists>x. P x s"

abbreviation (input)
  pred_app :: "('b \<Rightarrow> 'a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" (infixl "\<^bold>$" 100) where
  "f \<^bold>$ g \<equiv> \<lambda>s. f (g s) s"

abbreviation (input)
  pred_subseteq :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<subseteq>" 50) where
  "A \<^bold>\<subseteq> B \<equiv> \<lambda>s. A s \<subseteq> B s"

abbreviation (input)
  pred_union :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> 'b set" (infixl "\<^bold>\<union>" 65) where
  "a \<^bold>\<union> b \<equiv> \<lambda>s. a s \<union> b s"

abbreviation (input)
  pred_inter :: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> 'b set" (infixl "\<^bold>\<inter>" 65) where
  "a \<^bold>\<inter> b \<equiv> \<lambda>s. a s \<inter> b s"

text\<open>

More application specific.

\<close>

abbreviation (input)
  pred_conjoin :: "('a \<Rightarrow> bool) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "pred_conjoin xs \<equiv> foldr (\<^bold>\<and>) xs \<langle>True\<rangle>"

abbreviation (input)
  pred_disjoin :: "('a \<Rightarrow> bool) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "pred_disjoin xs \<equiv> foldr (\<^bold>\<or>) xs \<langle>False\<rangle>"

abbreviation (input)
  pred_is_none :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a \<Rightarrow> bool" ("NULL _" [40] 40) where
  "NULL a \<equiv> \<lambda>s. a s = None"

abbreviation (input)
  pred_empty :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> bool" ("EMPTY _" [40] 40) where
  "EMPTY a \<equiv> \<lambda>s. a s = {}"

abbreviation (input)
  pred_list_null :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> bool" ("LIST'_NULL _" [40] 40) where
  "LIST_NULL a \<equiv> \<lambda>s. a s = []"

abbreviation (input)
  pred_list_append :: "('a \<Rightarrow> 'b list) \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> 'b list" (infixr "\<^bold>@" 65) where
  "xs \<^bold>@ ys \<equiv> \<lambda>s. xs s @ ys s"

abbreviation (input)
  pred_pair :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'c" (infixr "\<^bold>\<otimes>" 60) where
  "a \<^bold>\<otimes> b \<equiv> \<lambda>s. (a s, b s)"

abbreviation (input)
  pred_singleton :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "pred_singleton x \<equiv> \<lambda>s. {x s}"
(*<*)

end
(*>*)
