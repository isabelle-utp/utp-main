(* Title: Examples/SML_Relativization/Foundations/SML_Relations.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Relativization of the results about relations\<close>
theory SML_Relations
  imports Main
begin



subsection\<open>Definitions and common properties\<close>

context 
  notes [[inductive_internals]]
begin

inductive_set trancl_on :: "['a set, ('a \<times> 'a) set] \<Rightarrow> ('a \<times> 'a) set"
  (\<open>on _/ (_\<^sup>+)\<close> [1000, 1000] 999)
  for U :: "'a set" and r :: "('a \<times> 'a) set" 
  where
    r_into_trancl[intro, Pure.intro]: 
      "\<lbrakk> a \<in> U; b \<in> U; (a, b) \<in> r \<rbrakk> \<Longrightarrow> (a, b) \<in> on U r\<^sup>+"
  | trancl_into_trancl[Pure.intro]: 
      "
      \<lbrakk> a \<in> U; b \<in> U; c \<in> U; (a, b) \<in> on U r\<^sup>+; (b, c) \<in> r \<rbrakk> \<Longrightarrow> 
        (a, c) \<in> on U r\<^sup>+
      "

abbreviation tranclp_on (\<open>on _/ (_\<^sup>+\<^sup>+)\<close> [1000, 1000] 1000) where
  "tranclp_on \<equiv> trancl_onp"

declare trancl_on_def[nitpick_unfold del]

lemmas tranclp_on_def = trancl_onp_def

end

definition transp_on :: "['a set, ['a, 'a] \<Rightarrow> bool] \<Rightarrow> bool"
  where "transp_on U = (\<lambda>r. (\<forall>x\<in>U. \<forall>y\<in>U. \<forall>z\<in>U. r x y \<longrightarrow> r y z \<longrightarrow> r x z))"

definition acyclic_on :: "['a set, ('a \<times> 'a) set] \<Rightarrow> bool"
  where "acyclic_on U = (\<lambda>r. (\<forall>x\<in>U. (x, x) \<notin> on U r\<^sup>+))"

lemma trancl_on_eq_tranclp_on:
  "on P (\<lambda>x y. (x, y) \<in> r)\<^sup>+\<^sup>+ x y = ((x, y) \<in> on (Collect P) r\<^sup>+)" 
  unfolding trancl_on_def tranclp_on_def Set.mem_Collect_eq by simp

lemma trancl_on_imp_U: "(x, y) \<in> on U r\<^sup>+  \<Longrightarrow> (x, y) \<in> U \<times> U"
  by (auto dest: trancl_on.cases)

lemmas tranclp_on_imp_P = trancl_on_imp_U[to_pred, simplified]

lemma trancl_on_imp_trancl: "(x, y) \<in> on U r\<^sup>+ \<Longrightarrow> (x, y) \<in> r\<^sup>+"
  by (induction rule: trancl_on.induct) auto

lemmas tranclp_on_imp_tranclp = trancl_on_imp_trancl[to_pred]

lemma tranclp_eq_tranclp_on: "r\<^sup>+\<^sup>+ = on (\<lambda>x. True) r\<^sup>+\<^sup>+"
  unfolding tranclp_def tranclp_on_def by simp

lemma trancl_eq_trancl_on: "r\<^sup>+ = on UNIV r\<^sup>+"
  unfolding trancl_def trancl_on_def by (simp add: tranclp_eq_tranclp_on)

lemma transp_on_empty[simp]: "transp_on {} r" unfolding transp_on_def by simp

lemma transp_eq_transp_on: "transp = transp_on UNIV"
  unfolding transp_def transp_on_def by simp

lemma acyclic_on_empty[simp]: "acyclic_on {} r" unfolding acyclic_on_def by simp

lemma acyclic_eq_acyclic_on: "acyclic = acyclic_on UNIV"
  unfolding acyclic_def acyclic_on_def 
  unfolding trancl_def tranclp_def trancl_on_def tranclp_on_def 
  by simp



subsection\<open>Transfer rules I: \<^const>\<open>lfp\<close> transfer\<close>


text\<open>
The following context contains code from \cite{immler_re_2019}.
\<close>

context
  includes lifting_syntax 
begin

lemma Inf_transfer[transfer_rule]: 
  "(rel_set (A ===> (=)) ===> A ===> (=)) Inf Inf"
  unfolding Inf_fun_def by transfer_prover

lemma less_eq_pred_transfer[transfer_rule]:
  assumes [transfer_rule]: "right_total A" 
  shows 
    "((A ===> (=)) ===> (A ===> (=)) ===> (=)) 
      (\<lambda>f g. \<forall>x\<in>Collect(Domainp A). f x \<le> g x) (\<le>)"
  unfolding le_fun_def by transfer_prover

lemma lfp_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  defines "R \<equiv> (((A ===> (=)) ===> (A ===> (=))) ===> (A ===> (=)))"
  shows "R (\<lambda>f. lfp (\<lambda>u x. if Domainp A x then f u x else bot)) lfp"
proof -
  have "R (\<lambda>f. Inf {u. \<forall>x\<in>Collect (Domainp A). f u x \<le> u x}) lfp"
    unfolding R_def lfp_def by transfer_prover
  thus ?thesis by (auto simp: le_fun_def lfp_def)
qed

lemma Inf2_transfer[transfer_rule]:
  "(rel_set (T ===> T ===> (=)) ===> T ===> T ===> (=)) Inf Inf"
  unfolding Inf_fun_def by transfer_prover

lemma less_eq2_pred_transfer[transfer_rule]:
  assumes [transfer_rule]: "right_total T" 
  shows 
    "((T ===> T ===> (=)) ===> (T ===> T ===> (=)) ===> (=)) 
      (\<lambda>f g. \<forall>x\<in>Collect(Domainp T). \<forall>y\<in>Collect(Domainp T). f x y \<le> g x y) (\<le>)"
  unfolding le_fun_def by transfer_prover

lemma lfp2_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  defines 
    "R \<equiv> 
      (((A ===> A ===> (=)) ===> (A ===> A ===> (=))) ===> (A ===> A ===> (=)))"
  shows 
    "R 
      (
        \<lambda>f. lfp 
          (
            \<lambda>u x y. 
              if Domainp A x 
              then if Domainp A y then (f u) x y else bot 
              else bot
          )
      ) 
      lfp"
proof -
  have 
    "R 
      (
        \<lambda>f. 
          Inf 
            {
              u. 
                \<forall>x\<in>Collect (Domainp A). \<forall>y\<in>Collect (Domainp A). 
                  (f u) x y \<le> u x y
            }
      ) 
      lfp"
    unfolding R_def lfp_def by transfer_prover 
  thus ?thesis by (auto simp: le_fun_def lfp_def)
qed

end



subsection\<open>Transfer rules II: application-specific rules\<close>

context
  includes lifting_syntax
begin

lemma transp_rt_transfer[transfer_rule]:
  assumes[transfer_rule]: "right_total A" 
  shows 
    "((A ===> A ===> (=)) ===> (=)) (transp_on (Collect (Domainp A))) transp"
  unfolding transp_def transp_on_def by transfer_prover

lemma tranclp_rt_bu_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> (=)) ===> (A ===> A ===> (=))) 
      (tranclp_on (Domainp A)) tranclp"
  unfolding tranclp_on_def tranclp_def 
  apply transfer_prover_start
  apply transfer_step+
proof 
  fix r
  have 
    "(
      \<lambda>p x y.
        (\<exists>a b. x = a \<and> y = b \<and> Domainp A a \<and> Domainp A b \<and> r a b) \<or> 
        (
          \<exists>a b c. 
            x = a \<and> y = c \<and> 
            Domainp A a \<and> Domainp A b \<and> Domainp A c \<and> 
            p a b \<and> r b c
        ) 
    ) = 
      (
        \<lambda>p x y.
          if Domainp A x
          then if Domainp A y
            then 
              (
                \<exists>a\<in>Collect (Domainp A). \<exists>b\<in>Collect (Domainp A). 
                  x = a \<and> y = b \<and> r a b) \<or>
                  (
                    \<exists>a\<in>Collect (Domainp A). 
                    \<exists>b\<in>Collect (Domainp A). 
                    \<exists>c\<in>Collect (Domainp A). 
                      x = a \<and> y = c \<and> p a b \<and> r b c
                  )
           else bot
         else bot
      )"
    (is "?lhs = ?rhs")
    by (intro ext) simp
  thus "lfp ?lhs = lfp ?rhs" by clarsimp
qed

lemma trancl_rt_bu_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(rel_set (rel_prod A A) ===> rel_set (rel_prod A A)) 
      (trancl_on (Collect (Domainp A))) trancl"
  unfolding trancl_on_def trancl_def
  apply transfer_prover_start
  apply transfer_step+
  by (auto simp: tranclp_on_imp_P[where U="Domainp A"])

lemma acyclic_rt_bu_transfer[transfer_rule]:
  assumes[transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((rel_set (rel_prod A A)) ===> (=)) 
      (acyclic_on (Collect (Domainp A))) acyclic"
  unfolding acyclic_on_def acyclic_def by transfer_prover

end

text\<open>\newpage\<close>

end