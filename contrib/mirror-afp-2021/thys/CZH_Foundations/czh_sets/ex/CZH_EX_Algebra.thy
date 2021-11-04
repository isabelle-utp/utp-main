(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Example III: abstract algebra\<close>
theory CZH_EX_Algebra
  imports CZH_EX_TS
begin



subsection\<open>Background\<close>


text\<open>
The section presents several examples of algebraic structures formalized
in \<open>ZFC in HOL\<close>. The definitions were adopted (with amendments) from the
main library of Isabelle/HOL.
\<close>

named_theorems sgrp_struct_field_simps

lemmas [sgrp_struct_field_simps] = \<A>_def



subsection\<open>Semigroup\<close>


subsubsection\<open>Foundations\<close>

definition mbinop where [sgrp_struct_field_simps]: "mbinop = 1\<^sub>\<nat>"

locale \<Z>_sgrp_basis = \<Z>_vfsequence \<alpha> \<SS> + op: binop \<open>\<SS>\<lparr>\<A>\<rparr>\<close> \<open>\<SS>\<lparr>mbinop\<rparr>\<close> 
  for \<alpha> \<SS> +
  assumes \<Z>_sgrp_length: "vcard \<SS> = 2\<^sub>\<nat>"
    and \<Z>_sgrp_binop: "binop (\<SS>\<lparr>\<A>\<rparr>) (\<SS>\<lparr>mbinop\<rparr>)"

abbreviation sgrp_app :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>\<odot>\<^sub>\<circ>\<index>\<close> 70)
  where "sgrp_app \<SS> a b \<equiv> \<SS>\<lparr>mbinop\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>"
notation sgrp_app (infixl \<open>\<odot>\<^sub>\<circ>\<close> 70)


text\<open>Rules.\<close>

lemma \<Z>_sgrp_basisI[intro]:
  assumes "\<Z>_vfsequence \<alpha> \<SS>"
    and "vcard \<SS> = 2\<^sub>\<nat>"
    and "binop (\<SS>\<lparr>\<A>\<rparr>) (\<SS>\<lparr>mbinop\<rparr>)"
  shows "\<Z>_sgrp_basis \<alpha> \<SS>"
  using assms unfolding \<Z>_sgrp_basis_def \<Z>_sgrp_basis_axioms_def by simp

lemma \<Z>_sgrp_basisD[dest]:
  assumes "\<Z>_sgrp_basis \<alpha> \<SS>"
  shows "\<Z>_vfsequence \<alpha> \<SS>"
    and "vcard \<SS> = 2\<^sub>\<nat>"
    and "binop (\<SS>\<lparr>\<A>\<rparr>) (\<SS>\<lparr>mbinop\<rparr>)"
  using assms unfolding \<Z>_sgrp_basis_def \<Z>_sgrp_basis_axioms_def by auto

lemma \<Z>_sgrp_basisE[elim]:
  assumes "\<Z>_sgrp_basis \<alpha> \<SS>"
  shows "\<Z>_vfsequence \<alpha> \<SS>"
    and "vcard \<SS> = 2\<^sub>\<nat>"
    and "binop (\<SS>\<lparr>\<A>\<rparr>) (\<SS>\<lparr>mbinop\<rparr>)"
  using assms unfolding \<Z>_sgrp_basis_def \<Z>_sgrp_basis_axioms_def by auto


subsubsection\<open>Simple semigroup\<close>

locale \<Z>_sgrp = \<Z>_sgrp_basis \<alpha> \<SS> for \<alpha> \<SS> +
  assumes \<Z>_sgrp_assoc: 
    "\<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; c \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow> 
      (a \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b) \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c = a \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (b \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c)"


text\<open>Rules.\<close>

lemma \<Z>_sgrpI[intro]:
  assumes "\<Z>_sgrp_basis \<alpha> \<SS>" 
    and "\<And>a b c. \<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; c \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow> 
      (a \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b) \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c = a \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (b \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c)"
  shows "\<Z>_sgrp \<alpha> \<SS>"
  using assms unfolding \<Z>_sgrp_def \<Z>_sgrp_axioms_def by simp

lemma \<Z>_sgrpD[dest]:
  assumes "\<Z>_sgrp \<alpha> \<SS>"
  shows "\<Z>_sgrp_basis \<alpha> \<SS>" 
    and "\<And>a b c. \<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; c \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow> 
      (a \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b) \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c = a \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (b \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c)"
  using assms unfolding \<Z>_sgrp_def \<Z>_sgrp_axioms_def by simp_all

lemma \<Z>_sgrpE[elim]:
  assumes "\<Z>_sgrp \<alpha> \<SS>"
  obtains "\<Z>_sgrp_basis \<alpha> \<SS>" 
    and "\<And>a b c. \<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; c \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow> 
      (a \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b) \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c = a \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (b \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c)"
  using assms by auto



subsection\<open>Commutative semigroup\<close>

locale \<Z>_csgrp = \<Z>_sgrp \<alpha> \<SS> for \<alpha> \<SS> +
  assumes \<Z>_csgrp_commutative: 
    "\<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow> a \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b = b \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> a"


text\<open>Rules.\<close>

lemma \<Z>_csgrpI[intro]:
  assumes "\<Z>_sgrp \<alpha> \<SS>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow> a \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b = b \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> a"
  shows "\<Z>_csgrp \<alpha> \<SS>"
  using assms unfolding \<Z>_csgrp_def \<Z>_csgrp_axioms_def by simp

lemma \<Z>_csgrpD[dest]:
  assumes "\<Z>_csgrp \<alpha> \<SS>"
  shows "\<Z>_sgrp \<alpha> \<SS>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow> a \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b = b \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> a"
  using assms unfolding \<Z>_csgrp_def \<Z>_csgrp_axioms_def by simp_all

lemma \<Z>_csgrpE[elim]:
  assumes "\<Z>_csgrp \<alpha> \<SS>"
  obtains "\<Z>_sgrp \<alpha> \<SS>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow> a \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b = b \<odot>\<^sub>\<circ>\<^bsub>\<SS>\<^esub> a"
  using assms by auto



subsection\<open>Semiring\<close>


subsubsection\<open>Foundations\<close>

definition vplus :: V where [sgrp_struct_field_simps]: "vplus = 1\<^sub>\<nat>"
definition vmult :: V where [sgrp_struct_field_simps]: "vmult = 2\<^sub>\<nat>"

abbreviation vplus_app :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>+\<^sub>\<circ>\<index>\<close> 65)
  where "a +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b \<equiv> \<SS>\<lparr>vplus\<rparr>\<lparr>a,b\<rparr>\<^sub>\<bullet>"
notation vplus_app (infixl \<open>+\<^sub>\<circ>\<index>\<close> 65)

abbreviation vmult_app :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>*\<^sub>\<circ>\<index>\<close> 70)
  where "a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b \<equiv> \<SS>\<lparr>vmult\<rparr>\<lparr>a,b\<rparr>\<^sub>\<bullet>"
notation vmult_app (infixl \<open>*\<^sub>\<circ>\<index>\<close> 70)


subsubsection\<open>Simple semiring\<close>

locale \<Z>_srng = \<Z>_vfsequence \<alpha> \<SS> for \<alpha> \<SS> +
  assumes \<Z>_srng_length: "vcard \<SS> = 3\<^sub>\<nat>"
    and \<Z>_srng_\<Z>_csgrp_vplus: "\<Z>_csgrp \<alpha> [\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vplus\<rparr>]\<^sub>\<circ>"
    and \<Z>_srng_\<Z>_sgrp_vmult: "\<Z>_sgrp \<alpha> [\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vmult\<rparr>]\<^sub>\<circ>"
    and \<Z>_srng_distrib_right: 
      "\<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; c \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow>
        (a +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b) *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c = (a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c) +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (b *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c)"
    and \<Z>_srng_distrib_left: 
      "\<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; c \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow>
        a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (b +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c) = (a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b) +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c)"
begin

sublocale vplus: \<Z>_csgrp \<alpha> \<open>[\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vplus\<rparr>]\<^sub>\<circ>\<close>
  rewrites "[\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vplus\<rparr>]\<^sub>\<circ>\<lparr>\<A>\<rparr> = \<SS>\<lparr>\<A>\<rparr>"
    and "[\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vplus\<rparr>]\<^sub>\<circ>\<lparr>mbinop\<rparr> = \<SS>\<lparr>vplus\<rparr>"
    and "sgrp_app [\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vplus\<rparr>]\<^sub>\<circ> = vplus_app \<SS>"
proof(rule \<Z>_srng_\<Z>_csgrp_vplus)
  show "[\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vplus\<rparr>]\<^sub>\<circ>\<lparr>\<A>\<rparr> = \<SS>\<lparr>\<A>\<rparr>"
    and [simp]: "[\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vplus\<rparr>]\<^sub>\<circ>\<lparr>mbinop\<rparr> = \<SS>\<lparr>vplus\<rparr>"
    by (auto simp: \<A>_def mbinop_def nat_omega_simps)
  show "(\<odot>\<^sub>\<circ>\<^bsub>[\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vplus\<rparr>]\<^sub>\<circ>\<^esub>) = (+\<^sub>\<circ>\<^bsub>\<SS>\<^esub>)" by simp
qed

sublocale vmult: \<Z>_sgrp \<alpha> \<open>[\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vmult\<rparr>]\<^sub>\<circ>\<close>
  rewrites "[\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vmult\<rparr>]\<^sub>\<circ>\<lparr>\<A>\<rparr> = \<SS>\<lparr>\<A>\<rparr>"
    and "[\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vmult\<rparr>]\<^sub>\<circ>\<lparr>mbinop\<rparr> = \<SS>\<lparr>vmult\<rparr>"
    and "sgrp_app [\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vmult\<rparr>]\<^sub>\<circ> = vmult_app \<SS>"
proof(rule \<Z>_srng_\<Z>_sgrp_vmult)
  show "[\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vmult\<rparr>]\<^sub>\<circ>\<lparr>\<A>\<rparr> = \<SS>\<lparr>\<A>\<rparr>"
    and [simp]: "[\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vmult\<rparr>]\<^sub>\<circ>\<lparr>mbinop\<rparr> = \<SS>\<lparr>vmult\<rparr>"
    by (auto simp: \<A>_def mbinop_def nat_omega_simps)
  show "(\<odot>\<^sub>\<circ>\<^bsub>[\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vmult\<rparr>]\<^sub>\<circ>\<^esub>) = (*\<^sub>\<circ>\<^bsub>\<SS>\<^esub>)" by simp
qed

end


text\<open>Rules.\<close>

lemma \<Z>_srngI[intro]:
  assumes "\<Z>_vfsequence \<alpha> \<SS>"
    and "vcard \<SS> = 3\<^sub>\<nat>"
    and "\<Z>_csgrp \<alpha> [\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vplus\<rparr>]\<^sub>\<circ>"
    and "\<Z>_sgrp \<alpha> [\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vmult\<rparr>]\<^sub>\<circ>"
    and "\<And>a b c. \<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; c \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow>
      (a +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b) *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c = (a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c) +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (b *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c)"
    and "\<And>a b c. \<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; c \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow>
      a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (b +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c) = (a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b) +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c)"
  shows "\<Z>_srng \<alpha> \<SS>"
  using assms unfolding \<Z>_srng_def \<Z>_srng_axioms_def by simp

lemma \<Z>_srngD[dest]:
  assumes "\<Z>_srng \<alpha> \<SS>"
  shows "\<Z>_vfsequence \<alpha> \<SS>"
    and "vcard \<SS> = 3\<^sub>\<nat>"
    and "\<Z>_csgrp \<alpha> [\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vplus\<rparr>]\<^sub>\<circ>"
    and "\<Z>_sgrp \<alpha> [\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vmult\<rparr>]\<^sub>\<circ>"
    and "\<And>a b c. \<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; c \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow>
      (a +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b) *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c = (a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c) +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (b *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c)"
    and "\<And>a b c. \<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; c \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow>
      a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (b +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c) = (a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b) +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c)"
  using assms unfolding \<Z>_srng_def \<Z>_srng_axioms_def by simp_all

lemma \<Z>_srngE[elim]:
  assumes "\<Z>_srng \<alpha> \<SS>"
  obtains "\<Z>_vfsequence \<alpha> \<SS>"
    and "vcard \<SS> = 3\<^sub>\<nat>"
    and "\<Z>_csgrp \<alpha> [\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vplus\<rparr>]\<^sub>\<circ>"
    and "\<Z>_sgrp \<alpha> [\<SS>\<lparr>\<A>\<rparr>, \<SS>\<lparr>vmult\<rparr>]\<^sub>\<circ>"
    and "\<And>a b c. \<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; c \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow>
      (a +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b) *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c = (a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c) +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (b *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c)"
    and "\<And>a b c. \<lbrakk> a \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; b \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr>; c \<in>\<^sub>\<circ> \<SS>\<lparr>\<A>\<rparr> \<rbrakk> \<Longrightarrow>
      a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (b +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c) = (a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> b) +\<^sub>\<circ>\<^bsub>\<SS>\<^esub> (a *\<^sub>\<circ>\<^bsub>\<SS>\<^esub> c)"
  using assms unfolding \<Z>_srng_def \<Z>_srng_axioms_def by auto



subsection\<open>Integer numbers form a semiring\<close>

definition vint_struct :: V (\<open>\<SS>\<^sub>\<int>\<close>)
  where "vint_struct = [\<int>\<^sub>\<circ>, vint_plus, vint_mult]\<^sub>\<circ>"

named_theorems vint_struct_simps

lemma vint_struct_\<A>[vint_struct_simps]: "\<SS>\<^sub>\<int>\<lparr>\<A>\<rparr> = \<int>\<^sub>\<circ>"
  unfolding vint_struct_def by (auto simp: sgrp_struct_field_simps)

lemma vint_struct_vplus[vint_struct_simps]: "\<SS>\<^sub>\<int>\<lparr>vplus\<rparr> = vint_plus"
  unfolding vint_struct_def 
  by (simp add: sgrp_struct_field_simps nat_omega_simps)

lemma vint_struct_vmult[vint_struct_simps]: "\<SS>\<^sub>\<int>\<lparr>vmult\<rparr> = vint_mult"
  unfolding vint_struct_def 
  by (simp add: sgrp_struct_field_simps nat_omega_simps)

context \<Z>
begin

lemma \<Z>_srng_vint: "\<Z>_srng \<alpha> \<SS>\<^sub>\<int>"
proof(intro \<Z>_srngI, unfold vint_struct_simps)

  interpret \<SS>: vfsequence \<open>\<SS>\<^sub>\<int>\<close> unfolding vint_struct_def by simp

  show vint_struct: "\<Z>_vfsequence \<alpha> \<SS>\<^sub>\<int>"
  proof(intro \<Z>_vfsequenceI)
    show "vfsequence \<SS>\<^sub>\<int>" unfolding vint_struct_def by simp
    show "\<R>\<^sub>\<circ> \<SS>\<^sub>\<int> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    proof(intro vsubsetI)
      fix x assume "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> \<SS>\<^sub>\<int>"
      then consider \<open>x = \<int>\<^sub>\<circ>\<close> | \<open>x = vint_plus\<close> | \<open>x = vint_mult\<close> 
        unfolding vint_struct_def by fastforce
      then show "x \<in>\<^sub>\<circ> Vset \<alpha>"
      proof cases
        case 1 with \<Z>_Vset_\<omega>2_vsubset_Vset vint_in_Vset_\<omega>2 show ?thesis by auto
      next
        case 2
        have "\<D>\<^sub>\<circ> vint_plus \<in>\<^sub>\<circ> Vset \<alpha>"
          unfolding vint_plus.nop_vdomain
        proof(rule Limit_vcpower_in_VsetI)
          from Axiom_of_Infinity show "2\<^sub>\<nat> \<in>\<^sub>\<circ> Vset \<alpha>" by auto
          from \<Z>_Vset_\<omega>2_vsubset_Vset show "\<int>\<^sub>\<circ> \<in>\<^sub>\<circ> Vset \<alpha>" 
            by (auto intro: vint_in_Vset_\<omega>2)
        qed auto
        moreover from \<Z>_Vset_\<omega>2_vsubset_Vset have "\<R>\<^sub>\<circ> vint_plus \<in>\<^sub>\<circ> Vset \<alpha>"
          unfolding vint_plus.nop_onto_vrange by (auto intro: vint_in_Vset_\<omega>2)
        ultimately show "x \<in>\<^sub>\<circ> Vset \<alpha>"
          unfolding 2
          by (simp add: rel_VLambda.vbrelation_Limit_in_VsetI vint_plus_def)
      next
        case 3
        have "\<D>\<^sub>\<circ> vint_mult \<in>\<^sub>\<circ> Vset \<alpha>"
          unfolding vint_mult.nop_vdomain
        proof(rule Limit_vcpower_in_VsetI)
          from Axiom_of_Infinity show "2\<^sub>\<nat> \<in>\<^sub>\<circ> Vset \<alpha>" by auto
          from \<Z>_Vset_\<omega>2_vsubset_Vset show "\<int>\<^sub>\<circ> \<in>\<^sub>\<circ> Vset \<alpha>" 
            by (auto intro: vint_in_Vset_\<omega>2)
        qed auto
        moreover from \<Z>_Vset_\<omega>2_vsubset_Vset Axiom_of_Infinity have 
          "\<R>\<^sub>\<circ> vint_mult \<in>\<^sub>\<circ> Vset \<alpha>"
          unfolding vint_mult.nop_onto_vrange by (auto intro: vint_in_Vset_\<omega>2)
        ultimately show "x \<in>\<^sub>\<circ> Vset \<alpha>"
          unfolding 3
          by (simp add: rel_VLambda.vbrelation_Limit_in_VsetI vint_mult_def)
      qed
    qed
  qed (simp add: \<Z>_axioms)

  interpret vint_struct: \<Z>_vfsequence \<alpha> \<open>\<SS>\<^sub>\<int>\<close> by (rule vint_struct)
  
  show "vcard \<SS>\<^sub>\<int> = 3\<^sub>\<nat>" 
    unfolding vint_struct_def by (simp add: nat_omega_simps)

  have [vint_struct_simps]:
    "[\<int>\<^sub>\<circ>, vint_plus]\<^sub>\<circ>\<lparr>\<A>\<rparr> = \<int>\<^sub>\<circ>" "[\<int>\<^sub>\<circ>, vint_plus]\<^sub>\<circ>\<lparr>mbinop\<rparr> = vint_plus"
    "[\<int>\<^sub>\<circ>, vint_mult]\<^sub>\<circ>\<lparr>\<A>\<rparr> = \<int>\<^sub>\<circ>" "[\<int>\<^sub>\<circ>, vint_mult]\<^sub>\<circ>\<lparr>mbinop\<rparr> = vint_mult"
    by (auto simp: sgrp_struct_field_simps nat_omega_simps)

  have [vint_struct_simps]:
    "sgrp_app [\<int>\<^sub>\<circ>, vint_plus]\<^sub>\<circ> = (+\<^sub>\<int>)"
    "sgrp_app [\<int>\<^sub>\<circ>, vint_mult]\<^sub>\<circ> = (*\<^sub>\<int>)"
    unfolding vint_struct_simps by simp_all

  show "\<Z>_csgrp \<alpha> [\<int>\<^sub>\<circ>, vint_plus]\<^sub>\<circ>"
  proof(intro \<Z>_csgrpI, unfold vint_struct_simps)
    show "\<Z>_sgrp \<alpha> [\<int>\<^sub>\<circ>, vint_plus]\<^sub>\<circ>"
    proof(intro \<Z>_sgrpI \<Z>_sgrp_basisI, unfold vint_struct_simps)
      show "\<Z>_vfsequence \<alpha> [\<int>\<^sub>\<circ>, vint_plus]\<^sub>\<circ>"
      proof(intro \<Z>_vfsequenceI)
        show "\<R>\<^sub>\<circ> [\<int>\<^sub>\<circ>, vint_plus]\<^sub>\<circ> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
        proof(intro vfsequence_vrange_vconsI)
          from \<Z>_Vset_\<omega>2_vsubset_Vset show [simp]: "\<int>\<^sub>\<circ> \<in>\<^sub>\<circ> Vset \<alpha>"
            by (auto intro: vint_in_Vset_\<omega>2)
          show "vint_plus \<in>\<^sub>\<circ> Vset \<alpha>"
          proof(rule vbrelation.vbrelation_Limit_in_VsetI)
            from Axiom_of_Infinity show "\<D>\<^sub>\<circ> vint_plus \<in>\<^sub>\<circ> Vset \<alpha>"
              unfolding vint_plus.nop_vdomain 
              by (intro Limit_vcpower_in_VsetI) auto
            from Axiom_of_Infinity show "\<R>\<^sub>\<circ> vint_plus \<in>\<^sub>\<circ> Vset \<alpha>" 
              unfolding vint_plus.nop_onto_vrange by auto
          qed (simp_all add: vint_plus_def)
        qed simp_all
      qed (simp_all add: \<Z>_axioms)
    qed 
      (
         auto simp:
          nat_omega_simps
          vint_plus.binop_axioms
          vint_assoc_law_addition
      ) 
  qed (simp add: vint_commutative_law_addition)

  show "\<Z>_sgrp \<alpha> [\<int>\<^sub>\<circ>, vint_mult]\<^sub>\<circ>"
  proof
    (
      intro \<Z>_sgrpI \<Z>_sgrp_basisI; 
      (unfold vint_struct_simps | tactic\<open>all_tac\<close>)
    )
    show "\<Z>_vfsequence \<alpha> [\<int>\<^sub>\<circ>, vint_mult]\<^sub>\<circ>"
    proof(intro \<Z>_vfsequenceI; (unfold vint_struct_simps | tactic\<open>all_tac\<close>))
      from \<Z>_axioms show "\<Z> \<alpha>" by simp
      show "\<R>\<^sub>\<circ> [\<int>\<^sub>\<circ>, vint_mult]\<^sub>\<circ> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
      proof(intro vfsequence_vrange_vconsI)
        from \<Z>_Vset_\<omega>2_vsubset_Vset show [simp]: "\<int>\<^sub>\<circ> \<in>\<^sub>\<circ> Vset \<alpha>"
          by (auto intro: vint_in_Vset_\<omega>2)
        show "vint_mult \<in>\<^sub>\<circ> Vset \<alpha>"
        proof(rule vbrelation.vbrelation_Limit_in_VsetI)
          from Axiom_of_Infinity show "\<D>\<^sub>\<circ> vint_mult \<in>\<^sub>\<circ> Vset \<alpha>"
            unfolding vint_mult.nop_vdomain 
            by (intro Limit_vcpower_in_VsetI) auto
          from Axiom_of_Infinity show "\<R>\<^sub>\<circ> vint_mult \<in>\<^sub>\<circ> Vset \<alpha>" 
            unfolding vint_mult.nop_onto_vrange by auto
        qed (simp_all add: vint_mult_def)
      qed simp_all
    qed auto
  qed
    (
      auto simp: 
        nat_omega_simps
        vint_mult.binop_axioms
        vint_assoc_law_multiplication
    )

qed
  (
    auto simp: 
      vint_commutative_law_multiplication 
      vint_plus_closed 
      vint_distributive_law
  )


text\<open>Interpretation.\<close>

interpretation vint: \<Z>_srng \<alpha> \<open>\<SS>\<^sub>\<int>\<close>
  rewrites "\<SS>\<^sub>\<int>\<lparr>\<A>\<rparr> = \<int>\<^sub>\<circ>"
    and "\<SS>\<^sub>\<int>\<lparr>vplus\<rparr> = vint_plus"
    and "\<SS>\<^sub>\<int>\<lparr>vmult\<rparr> = vint_mult"
    and "vplus_app (\<SS>\<^sub>\<int>) = vint_plus_app"
    and "vmult_app (\<SS>\<^sub>\<int>) = vint_mult_app"
  unfolding vint_struct_simps by (rule \<Z>_srng_vint) simp_all

thm vint.vmult.\<Z>_sgrp_assoc
thm vint.vplus.\<Z>_sgrp_assoc
thm vint.\<Z>_srng_distrib_left

end

text\<open>\newpage\<close>

end