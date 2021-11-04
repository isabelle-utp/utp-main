(*
(C) Copyright Andreas Viktor Hess, DTU, 2015-2020

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

(*
Based on src/HOL/ex/Unification.thy packaged with Isabelle/HOL 2015 having the following license:

ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.

Copyright (c) 1986-2015,
  University of Cambridge,
  Technische Universitaet Muenchen,
  and contributors.

  All rights reserved.

Redistribution and use in source and binary forms, with or without 
modification, are permitted provided that the following conditions are 
met:

* Redistributions of source code must retain the above copyright 
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright 
notice, this list of conditions and the following disclaimer in the 
documentation and/or other materials provided with the distribution.

* Neither the name of the University of Cambridge or the Technische
Universitaet Muenchen nor the names of their contributors may be used
to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS 
IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED 
TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A 
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT 
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, 
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT 
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, 
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY 
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT 
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE 
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)


(*  Title:      More_Unification.thy
    Author:     Andreas Viktor Hess, DTU

    Originally based on src/HOL/ex/Unification.thy (Isabelle/HOL 2015) by:
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Author:     Konrad Slind, TUM & Cambridge University Computer Laboratory
    Author:     Alexander Krauss, TUM
*)

section \<open>Definitions and Properties Related to Substitutions and Unification\<close>

theory More_Unification
  imports Messages "First_Order_Terms.Unification"
begin

subsection \<open>Substitutions\<close>

abbreviation subst_apply_list (infix "\<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t" 51) where
  "T \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<theta> \<equiv> map (\<lambda>t. t \<cdot> \<theta>) T"  

abbreviation subst_apply_pair (infixl "\<cdot>\<^sub>p" 60) where
  "d \<cdot>\<^sub>p \<theta> \<equiv> (case d of (t,t') \<Rightarrow> (t \<cdot> \<theta>, t' \<cdot> \<theta>))"

abbreviation subst_apply_pair_set (infixl "\<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t" 60) where
  "M \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta> \<equiv> (\<lambda>d. d \<cdot>\<^sub>p \<theta>) ` M"

definition subst_apply_pairs (infix "\<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s" 51) where
  "F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta> \<equiv> map (\<lambda>f. f \<cdot>\<^sub>p \<theta>) F"

abbreviation subst_more_general_than (infixl "\<preceq>\<^sub>\<circ>" 50) where
  "\<sigma> \<preceq>\<^sub>\<circ> \<theta> \<equiv> \<exists>\<gamma>. \<theta> = \<sigma> \<circ>\<^sub>s \<gamma>"

abbreviation subst_support (infix "supports" 50) where
  "\<theta> supports \<delta> \<equiv> (\<forall>x. \<theta> x \<cdot> \<delta> = \<delta> x)"

abbreviation rm_var where
  "rm_var v s \<equiv> s(v := Var v)"

abbreviation rm_vars where
  "rm_vars vs \<sigma> \<equiv> (\<lambda>v. if v \<in> vs then Var v else \<sigma> v)"

definition subst_elim where
  "subst_elim \<sigma> v \<equiv> \<forall>t. v \<notin> fv (t \<cdot> \<sigma>)"

definition subst_idem where
  "subst_idem s \<equiv> s \<circ>\<^sub>s s = s"

lemma subst_support_def: "\<theta> supports \<tau> \<longleftrightarrow> \<tau> = \<theta> \<circ>\<^sub>s \<tau>"
unfolding subst_compose_def by metis

lemma subst_supportD: "\<theta> supports \<delta> \<Longrightarrow> \<theta> \<preceq>\<^sub>\<circ> \<delta>"
using subst_support_def by auto

lemma rm_vars_empty[simp]: "rm_vars {} s = s" "rm_vars (set []) s = s"
by simp_all

lemma rm_vars_singleton: "rm_vars {v} s = rm_var v s"
by auto

lemma subst_apply_terms_empty: "M \<cdot>\<^sub>s\<^sub>e\<^sub>t Var = M"
by simp

lemma subst_agreement: "(t \<cdot> r = t \<cdot> s) \<longleftrightarrow> (\<forall>v \<in> fv t. Var v \<cdot> r = Var v \<cdot> s)"
by (induct t) auto

lemma repl_invariance[dest?]: "v \<notin> fv t \<Longrightarrow> t \<cdot> s(v := u) = t \<cdot> s"
by (simp add: subst_agreement)

lemma subst_idx_map:
  assumes "\<forall>i \<in> set I. i < length T"
  shows "(map ((!) T) I) \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta> = map ((!) (map (\<lambda>t. t \<cdot> \<delta>) T)) I"
using assms by auto

lemma subst_idx_map':
  assumes "\<forall>i \<in> fv\<^sub>s\<^sub>e\<^sub>t (set K). i < length T"
  shows "(K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t (!) T) \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta> = K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t ((!) (map (\<lambda>t. t \<cdot> \<delta>) T))" (is "?A = ?B")
proof -
  have "T ! i \<cdot> \<delta> = (map (\<lambda>t. t \<cdot> \<delta>) T) ! i"
    when "i < length T" for i
    using that by auto
  hence "T ! i \<cdot> \<delta> = (map (\<lambda>t. t \<cdot> \<delta>) T) ! i"
    when "i \<in> fv\<^sub>s\<^sub>e\<^sub>t (set K)" for i
    using that assms by auto
  hence "k \<cdot> (!) T \<cdot> \<delta> = k \<cdot> (!) (map (\<lambda>t. t \<cdot> \<delta>) T)"
    when "fv k \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (set K)" for k
    using that by (induction k) force+
  thus ?thesis by auto
qed

lemma subst_remove_var: "v \<notin> fv s \<Longrightarrow> v \<notin> fv (t \<cdot> Var(v := s))"
by (induct t) simp_all

lemma subst_set_map: "x \<in> set X \<Longrightarrow> x \<cdot> s \<in> set (map (\<lambda>x. x \<cdot> s) X)"
by simp

lemma subst_set_idx_map:
  assumes "\<forall>i \<in> I. i < length T"
  shows "(!) T ` I \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> = (!) (map (\<lambda>t. t \<cdot> \<delta>) T) ` I" (is "?A = ?B")
proof
  have *: "T ! i \<cdot> \<delta> = (map (\<lambda>t. t \<cdot> \<delta>) T) ! i"
    when "i < length T" for i
    using that by auto
  
  show "?A \<subseteq> ?B" using * assms by blast
  show "?B \<subseteq> ?A" using * assms by auto
qed

lemma subst_set_idx_map':
  assumes "\<forall>i \<in> fv\<^sub>s\<^sub>e\<^sub>t K. i < length T"
  shows "K \<cdot>\<^sub>s\<^sub>e\<^sub>t (!) T \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> = K \<cdot>\<^sub>s\<^sub>e\<^sub>t (!) (map (\<lambda>t. t \<cdot> \<delta>) T)" (is "?A = ?B")
proof
  have "T ! i \<cdot> \<delta> = (map (\<lambda>t. t \<cdot> \<delta>) T) ! i"
    when "i < length T" for i
    using that by auto
  hence "T ! i \<cdot> \<delta> = (map (\<lambda>t. t \<cdot> \<delta>) T) ! i"
    when "i \<in> fv\<^sub>s\<^sub>e\<^sub>t K" for i
    using that assms by auto
  hence *: "k \<cdot> (!) T \<cdot> \<delta> = k \<cdot> (!) (map (\<lambda>t. t \<cdot> \<delta>) T)"
    when "fv k \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t K" for k
    using that by (induction k) force+

  show "?A \<subseteq> ?B" using * by auto
  show "?B \<subseteq> ?A" using * by force
qed

lemma subst_term_list_obtain:
  assumes "\<forall>i < length T. \<exists>s. P (T ! i) s \<and> S ! i = s \<cdot> \<delta>"
    and "length T = length S"
  shows "\<exists>U. length T = length U \<and> (\<forall>i < length T. P (T ! i) (U ! i)) \<and> S = map (\<lambda>u. u \<cdot> \<delta>) U"
using assms
proof (induction T arbitrary: S)
  case (Cons t T S')
  then obtain s S where S': "S' = s#S" by (cases S') auto

  have "\<forall>i < length T. \<exists>s. P (T ! i) s \<and> S ! i = s \<cdot> \<delta>" "length T = length S"
    using Cons.prems S' by force+
  then obtain U where U:
      "length T = length U" "\<forall>i < length T. P (T ! i) (U ! i)" "S = map (\<lambda>u. u \<cdot> \<delta>) U"
    using Cons.IH by moura

  obtain u where u: "P t u" "s = u \<cdot> \<delta>"
    using Cons.prems(1) S' by auto

  have 1: "length (t#T) = length (u#U)"
    using Cons.prems(2) U(1) by fastforce

  have 2: "\<forall>i < length (t#T). P ((t#T) ! i) ((u#U) ! i)"
    using u(1) U(2) by (simp add: nth_Cons')

  have 3: "S' = map (\<lambda>u. u \<cdot> \<delta>) (u#U)"
    using U u S' by simp

  show ?case using 1 2 3 by blast
qed simp

lemma subst_mono: "t \<sqsubseteq> u \<Longrightarrow> t \<cdot> s \<sqsubseteq> u \<cdot> s"
by (induct u) auto

lemma subst_mono_fv: "x \<in> fv t \<Longrightarrow> s x \<sqsubseteq> t \<cdot> s"
by (induct t) auto

lemma subst_mono_neq:
  assumes "t \<sqsubset> u"
  shows "t \<cdot> s \<sqsubset> u \<cdot> s"
proof (cases u)
  case (Var v)
  hence False using \<open>t \<sqsubset> u\<close> by simp
  thus ?thesis ..
next
  case (Fun f X)
  then obtain x where "x \<in> set X" "t \<sqsubseteq> x" using \<open>t \<sqsubset> u\<close> by auto
  hence "t \<cdot> s \<sqsubseteq> x \<cdot> s" using subst_mono by metis

  obtain Y where "Fun f X \<cdot> s = Fun f Y" by auto
  hence "x \<cdot> s \<in> set Y" using \<open>x \<in> set X\<close> by auto
  hence "x \<cdot> s \<sqsubset> Fun f X \<cdot> s" using \<open>Fun f X \<cdot> s = Fun f Y\<close> Fun_param_is_subterm by simp
  hence "t \<cdot> s \<sqsubset> Fun f X \<cdot> s" using \<open>t \<cdot> s \<sqsubseteq> x \<cdot> s\<close> by (metis term.dual_order.trans term.eq_iff)
  thus ?thesis using \<open>u = Fun f X\<close> \<open>t \<sqsubset> u\<close> by metis
qed

lemma subst_no_occs[dest]: "\<not>Var v \<sqsubseteq> t \<Longrightarrow> t \<cdot> Var(v := s) = t"
by (induct t) (simp_all add: map_idI)

lemma var_comp[simp]: "\<sigma> \<circ>\<^sub>s Var = \<sigma>" "Var \<circ>\<^sub>s \<sigma> = \<sigma>"
unfolding subst_compose_def by simp_all

lemma subst_comp_all: "M \<cdot>\<^sub>s\<^sub>e\<^sub>t (\<delta> \<circ>\<^sub>s \<theta>) = (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
using subst_subst_compose[of _ \<delta> \<theta>] by auto

lemma subst_all_mono: "M \<subseteq> M' \<Longrightarrow> M \<cdot>\<^sub>s\<^sub>e\<^sub>t s \<subseteq> M' \<cdot>\<^sub>s\<^sub>e\<^sub>t s"
by auto

lemma subst_comp_set_image: "(\<delta> \<circ>\<^sub>s \<theta>) ` X = \<delta> ` X \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
using subst_compose by fastforce

lemma subst_ground_ident[dest?]: "fv t = {} \<Longrightarrow> t \<cdot> s = t"
by (induct t, simp, metis subst_agreement empty_iff subst_apply_term_empty)

lemma subst_ground_ident_compose:
  "fv (\<sigma> x) = {} \<Longrightarrow> (\<sigma> \<circ>\<^sub>s \<theta>) x = \<sigma> x"
  "fv (t \<cdot> \<sigma>) = {} \<Longrightarrow> t \<cdot> (\<sigma> \<circ>\<^sub>s \<theta>) = t \<cdot> \<sigma>"
using subst_subst_compose[of t \<sigma> \<theta>]
by (simp_all add: subst_compose_def subst_ground_ident)

lemma subst_all_ground_ident[dest?]: "ground M \<Longrightarrow> M \<cdot>\<^sub>s\<^sub>e\<^sub>t s = M"
proof -
  assume "ground M"
  hence "\<And>t. t \<in> M \<Longrightarrow> fv t = {}" by auto
  hence "\<And>t. t \<in> M \<Longrightarrow> t \<cdot> s = t" by (metis subst_ground_ident)
  moreover have "\<And>t. t \<in> M \<Longrightarrow> t \<cdot> s \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t s" by (metis imageI)
  ultimately show "M \<cdot>\<^sub>s\<^sub>e\<^sub>t s = M" by (simp add: image_cong)
qed

lemma subst_eqI[intro]: "(\<And>t. t \<cdot> \<sigma> = t \<cdot> \<theta>) \<Longrightarrow> \<sigma> = \<theta>"
proof -
  assume "\<And>t. t \<cdot> \<sigma> = t \<cdot> \<theta>"
  hence "\<And>v. Var v \<cdot> \<sigma> = Var v \<cdot> \<theta>" by auto
  thus "\<sigma> = \<theta>" by auto
qed

lemma subst_cong: "\<lbrakk>\<sigma> = \<sigma>'; \<theta> = \<theta>'\<rbrakk> \<Longrightarrow> (\<sigma> \<circ>\<^sub>s \<theta>) = (\<sigma>' \<circ>\<^sub>s \<theta>')"
by auto

lemma subst_mgt_bot[simp]: "Var \<preceq>\<^sub>\<circ> \<theta>"
by simp

lemma subst_mgt_refl[simp]: "\<theta> \<preceq>\<^sub>\<circ> \<theta>"
by (metis var_comp(1))

lemma subst_mgt_trans: "\<lbrakk>\<theta> \<preceq>\<^sub>\<circ> \<delta>; \<delta> \<preceq>\<^sub>\<circ> \<sigma>\<rbrakk> \<Longrightarrow> \<theta> \<preceq>\<^sub>\<circ> \<sigma>"
by (metis subst_compose_assoc)

lemma subst_mgt_comp: "\<theta> \<preceq>\<^sub>\<circ> \<theta> \<circ>\<^sub>s \<delta>"
by auto

lemma subst_mgt_comp': "\<theta> \<circ>\<^sub>s \<delta> \<preceq>\<^sub>\<circ> \<sigma> \<Longrightarrow> \<theta> \<preceq>\<^sub>\<circ> \<sigma>"
by (metis subst_compose_assoc)

lemma var_self: "(\<lambda>w. if w = v then Var v else Var w) = Var"
using subst_agreement by auto

lemma var_same[simp]: "Var(v := t) = Var \<longleftrightarrow> t = Var v"
by (intro iffI, metis fun_upd_same, simp add: var_self)

lemma subst_eq_if_eq_vars: "(\<And>v. (Var v) \<cdot> \<theta> = (Var v) \<cdot> \<sigma>) \<Longrightarrow> \<theta> = \<sigma>"
by (auto simp add: subst_agreement)

lemma subst_all_empty[simp]: "{} \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> = {}"
by simp

lemma subst_all_insert:"(insert t M) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta> = insert (t \<cdot> \<delta>) (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)"
by auto

lemma subst_apply_fv_subset: "fv t \<subseteq> V \<Longrightarrow> fv (t \<cdot> \<delta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V)"
by (induct t) auto

lemma subst_apply_fv_empty:
  assumes "fv t = {}"
  shows "fv (t \<cdot> \<sigma>) = {}"
using assms subst_apply_fv_subset[of t "{}" \<sigma>]
by auto

lemma subst_compose_fv:
  assumes "fv (\<theta> x) = {}"
  shows "fv ((\<theta> \<circ>\<^sub>s \<sigma>) x) = {}"
using assms subst_apply_fv_empty
unfolding subst_compose_def by fast

lemma subst_compose_fv':
  fixes \<theta> \<sigma>::"('a,'b) subst"
  assumes "y \<in> fv ((\<theta> \<circ>\<^sub>s \<sigma>) x)"
  shows "\<exists>z. z \<in> fv (\<theta> x)"
using assms subst_compose_fv
by fast

lemma subst_apply_fv_unfold: "fv (t \<cdot> \<delta>) = fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` fv t)"
by (induct t) auto

lemma subst_apply_fv_unfold': "fv (t \<cdot> \<delta>) = (\<Union>v \<in> fv t. fv (\<delta> v))"
using subst_apply_fv_unfold by simp

lemma subst_apply_fv_union: "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> fv (t \<cdot> \<delta>) = fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> fv t))"
proof -
  have "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (V \<union> fv t)) = fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` V) \<union> fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` fv t)" by auto
  thus ?thesis using subst_apply_fv_unfold by metis
qed

lemma subst_elimI[intro]: "(\<And>t. v \<notin> fv (t \<cdot> \<sigma>)) \<Longrightarrow> subst_elim \<sigma> v"
by (auto simp add: subst_elim_def)

lemma subst_elimI'[intro]: "(\<And>w. v \<notin> fv (Var w \<cdot> \<theta>)) \<Longrightarrow> subst_elim \<theta> v"
by (simp add: subst_elim_def subst_apply_fv_unfold') 

lemma subst_elimD[dest]: "subst_elim \<sigma> v \<Longrightarrow> v \<notin> fv (t \<cdot> \<sigma>)"
by (auto simp add: subst_elim_def)

lemma subst_elimD'[dest]: "subst_elim \<sigma> v \<Longrightarrow> \<sigma> v \<noteq> Var v"
by (metis subst_elim_def subst_apply_term.simps(1) term.set_intros(3))

lemma subst_elimD''[dest]: "subst_elim \<sigma> v \<Longrightarrow> v \<notin> fv (\<sigma> w)"
by (metis subst_elim_def subst_apply_term.simps(1))

lemma subst_elim_rm_vars_dest[dest]:
  "subst_elim (\<sigma>::('a,'b) subst) v \<Longrightarrow> v \<notin> vs \<Longrightarrow> subst_elim (rm_vars vs \<sigma>) v"
proof -
  assume assms: "subst_elim \<sigma> v" "v \<notin> vs"
  obtain f::"('a, 'b) subst \<Rightarrow> 'b \<Rightarrow> 'b" where
      "\<forall>\<sigma> v. (\<exists>w. v \<in> fv (Var w \<cdot> \<sigma>)) = (v \<in> fv (Var (f \<sigma> v) \<cdot> \<sigma>))"
    by moura
  hence *: "\<forall>a \<sigma>. a \<in> fv (Var (f \<sigma> a) \<cdot> \<sigma>) \<or> subst_elim \<sigma> a" by blast
  have "Var (f (rm_vars vs \<sigma>) v) \<cdot> \<sigma> \<noteq> Var (f (rm_vars vs \<sigma>) v) \<cdot> rm_vars vs \<sigma>
        \<or> v \<notin> fv (Var (f (rm_vars vs \<sigma>) v) \<cdot> rm_vars vs \<sigma>)"
    using assms(1) by fastforce
  moreover
  { assume "Var (f (rm_vars vs \<sigma>) v) \<cdot> \<sigma> \<noteq> Var (f (rm_vars vs \<sigma>) v) \<cdot> rm_vars vs \<sigma>"
    hence "rm_vars vs \<sigma> (f (rm_vars vs \<sigma>) v) \<noteq> \<sigma> (f (rm_vars vs \<sigma>) v)" by auto
    hence "f (rm_vars vs \<sigma>) v \<in> vs" by meson
    hence ?thesis using * assms(2) by force
  }
  ultimately show ?thesis using * by blast
qed

lemma occs_subst_elim: "\<not>Var v \<sqsubset> t \<Longrightarrow> subst_elim (Var(v := t)) v \<or> (Var(v := t)) = Var"
proof (cases "Var v = t")
  assume "Var v \<noteq> t" "\<not>Var v \<sqsubset> t"
  hence "v \<notin> fv t" by (simp add: vars_iff_subterm_or_eq)
  thus ?thesis by (auto simp add: subst_remove_var)
qed auto

lemma occs_subst_elim': "\<not>Var v \<sqsubseteq> t \<Longrightarrow> subst_elim (Var(v := t)) v"
proof -
  assume "\<not>Var v \<sqsubseteq> t"
  hence "v \<notin> fv t" by (auto simp add: vars_iff_subterm_or_eq)
  thus "subst_elim (Var(v := t)) v" by (simp add: subst_elim_def subst_remove_var)
qed

lemma subst_elim_comp: "subst_elim \<theta> v \<Longrightarrow> subst_elim (\<delta> \<circ>\<^sub>s \<theta>) v"
by (auto simp add: subst_elim_def)

lemma var_subst_idem: "subst_idem Var"
by (simp add: subst_idem_def)

lemma var_upd_subst_idem:
  assumes "\<not>Var v \<sqsubseteq> t" shows "subst_idem (Var(v := t))"
unfolding subst_idem_def
proof
  let ?\<theta> = "Var(v := t)"
  from assms have t_\<theta>_id: "t \<cdot> ?\<theta> = t" by blast
  fix s show "s \<cdot> (?\<theta> \<circ>\<^sub>s ?\<theta>) = s \<cdot> ?\<theta>"
    unfolding subst_compose_def
    by (induction s, metis t_\<theta>_id fun_upd_def subst_apply_term.simps(1), simp) 
qed


subsection \<open>Lemmata: Domain and Range of Substitutions\<close>
lemma range_vars_alt_def: "range_vars s \<equiv> fv\<^sub>s\<^sub>e\<^sub>t (subst_range s)"
unfolding range_vars_def by simp

lemma subst_dom_var_finite[simp]: "finite (subst_domain Var)" by simp

lemma subst_range_Var[simp]: "subst_range Var = {}" by simp

lemma range_vars_Var[simp]: "range_vars Var = {}" by fastforce

lemma finite_subst_img_if_finite_dom: "finite (subst_domain \<sigma>) \<Longrightarrow> finite (range_vars \<sigma>)"
unfolding range_vars_alt_def by auto

lemma finite_subst_img_if_finite_dom': "finite (subst_domain \<sigma>) \<Longrightarrow> finite (subst_range \<sigma>)"
by auto

lemma subst_img_alt_def: "subst_range s = {t. \<exists>v. s v = t \<and> t \<noteq> Var v}"
by (auto simp add: subst_domain_def)

lemma subst_fv_img_alt_def: "range_vars s = (\<Union>t \<in> {t. \<exists>v. s v = t \<and> t \<noteq> Var v}. fv t)"
unfolding range_vars_alt_def by (auto simp add: subst_domain_def)

lemma subst_domI[intro]: "\<sigma> v \<noteq> Var v \<Longrightarrow> v \<in> subst_domain \<sigma>"
by (simp add: subst_domain_def)

lemma subst_imgI[intro]: "\<sigma> v \<noteq> Var v \<Longrightarrow> \<sigma> v \<in> subst_range \<sigma>"
by (simp add: subst_domain_def)

lemma subst_fv_imgI[intro]: "\<sigma> v \<noteq> Var v \<Longrightarrow> fv (\<sigma> v) \<subseteq> range_vars \<sigma>"
unfolding range_vars_alt_def by auto

lemma subst_domain_subst_Fun_single[simp]:
  "subst_domain (Var(x := Fun f T)) = {x}" (is "?A = ?B")
unfolding subst_domain_def by simp

lemma subst_range_subst_Fun_single[simp]:
  "subst_range (Var(x := Fun f T)) = {Fun f T}" (is "?A = ?B")
by simp

lemma range_vars_subst_Fun_single[simp]:
  "range_vars (Var(x := Fun f T)) = fv (Fun f T)"
unfolding range_vars_alt_def by force

lemma var_renaming_is_Fun_iff:
  assumes "subst_range \<delta> \<subseteq> range Var"
  shows "is_Fun t = is_Fun (t \<cdot> \<delta>)"
proof (cases t)
  case (Var x)
  hence "\<exists>y. \<delta> x = Var y" using assms by auto
  thus ?thesis using Var by auto
qed simp

lemma subst_fv_dom_img_subset: "fv t \<subseteq> subst_domain \<theta> \<Longrightarrow> fv (t \<cdot> \<theta>) \<subseteq> range_vars \<theta>"
unfolding range_vars_alt_def by (induct t) auto

lemma subst_fv_dom_img_subset_set: "fv\<^sub>s\<^sub>e\<^sub>t M \<subseteq> subst_domain \<theta> \<Longrightarrow> fv\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<subseteq> range_vars \<theta>"
proof -
  assume assms: "fv\<^sub>s\<^sub>e\<^sub>t M \<subseteq> subst_domain \<theta>"
  obtain f::"'a set \<Rightarrow> (('b, 'a) term \<Rightarrow> 'a set) \<Rightarrow> ('b, 'a) terms \<Rightarrow> ('b, 'a) term" where
      "\<forall>x y z. (\<exists>v. v \<in> z \<and> \<not> y v \<subseteq> x) \<longleftrightarrow> (f x y z \<in> z \<and> \<not> y (f x y z) \<subseteq> x)"
    by moura
  hence *:
      "\<forall>T g A. (\<not> \<Union> (g ` T) \<subseteq> A \<or> (\<forall>t. t \<notin> T \<or> g t \<subseteq> A)) \<and>
               (\<Union> (g ` T) \<subseteq> A \<or> f A g T \<in> T \<and> \<not> g (f A g T) \<subseteq> A)"
    by (metis (no_types) SUP_le_iff)
  hence **: "\<forall>t. t \<notin> M \<or> fv t \<subseteq> subst_domain \<theta>" by (metis (no_types) assms fv\<^sub>s\<^sub>e\<^sub>t.simps)
  have "\<forall>t::('b, 'a) term. \<forall>f T. t \<notin> f ` T \<or> (\<exists>t'::('b, 'a) term. t = f t' \<and> t' \<in> T)" by blast
  hence "f (range_vars \<theta>) fv (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<notin> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> \<or>
         fv (f (range_vars \<theta>) fv (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)) \<subseteq> range_vars \<theta>"
    by (metis (full_types) ** subst_fv_dom_img_subset)
  thus ?thesis by (metis (no_types) * fv\<^sub>s\<^sub>e\<^sub>t.simps)
qed

lemma subst_fv_dom_ground_if_ground_img:
  assumes "fv t \<subseteq> subst_domain s" "ground (subst_range s)"
  shows "fv (t \<cdot> s) = {}"
using subst_fv_dom_img_subset[OF assms(1)] assms(2) by force

lemma subst_fv_dom_ground_if_ground_img':
  assumes "fv t \<subseteq> subst_domain s" "\<And>x. x \<in> subst_domain s \<Longrightarrow> fv (s x) = {}"
  shows "fv (t \<cdot> s) = {}"
using subst_fv_dom_ground_if_ground_img[OF assms(1)] assms(2) by auto

lemma subst_fv_unfold: "fv (t \<cdot> s) = (fv t - subst_domain s) \<union> fv\<^sub>s\<^sub>e\<^sub>t (s ` (fv t \<inter> subst_domain s))"
proof (induction t)
  case (Var v) thus ?case
  proof (cases "v \<in> subst_domain s")
    case True thus ?thesis by auto
  next
    case False
    hence "fv (Var v \<cdot> s) = {v}" "fv (Var v) \<inter> subst_domain s = {}" by auto
    thus ?thesis by auto
  qed
next
  case Fun thus ?case by auto
qed

lemma subst_fv_unfold_ground_img: "range_vars s = {} \<Longrightarrow> fv (t \<cdot> s) = fv t - subst_domain s"
using subst_fv_unfold[of t s] unfolding range_vars_alt_def by auto

lemma subst_img_update:
  "\<lbrakk>\<sigma> v = Var v; t \<noteq> Var v\<rbrakk> \<Longrightarrow> range_vars (\<sigma>(v := t)) = range_vars \<sigma> \<union> fv t"
proof -
  assume "\<sigma> v = Var v" "t \<noteq> Var v"
  hence "(\<Union>s \<in> {s. \<exists>w. (\<sigma>(v := t)) w = s \<and> s \<noteq> Var w}. fv s) = fv t \<union> range_vars \<sigma>"
    unfolding range_vars_alt_def by (auto simp add: subst_domain_def)
  thus "range_vars (\<sigma>(v := t)) = range_vars \<sigma> \<union> fv t"
    by (metis Un_commute subst_fv_img_alt_def)
qed

lemma subst_dom_update1: "v \<notin> subst_domain \<sigma> \<Longrightarrow> subst_domain (\<sigma>(v := Var v)) = subst_domain \<sigma>"
by (auto simp add: subst_domain_def)

lemma subst_dom_update2: "t \<noteq> Var v \<Longrightarrow> subst_domain (\<sigma>(v := t)) = insert v (subst_domain \<sigma>)"
by (auto simp add: subst_domain_def)

lemma subst_dom_update3: "t = Var v \<Longrightarrow> subst_domain (\<sigma>(v := t)) = subst_domain \<sigma> - {v}"
by (auto simp add: subst_domain_def)

lemma var_not_in_subst_dom[elim]: "v \<notin> subst_domain s \<Longrightarrow> s v = Var v"
by (simp add: subst_domain_def)

lemma subst_dom_vars_in_subst[elim]: "v \<in> subst_domain s \<Longrightarrow> s v \<noteq> Var v"
by (simp add: subst_domain_def)

lemma subst_not_dom_fixed: "\<lbrakk>v \<in> fv t; v \<notin> subst_domain s\<rbrakk> \<Longrightarrow> v \<in> fv (t \<cdot> s)" by (induct t) auto

lemma subst_not_img_fixed: "\<lbrakk>v \<in> fv (t \<cdot> s); v \<notin> range_vars s\<rbrakk> \<Longrightarrow> v \<in> fv t"
unfolding range_vars_alt_def by (induct t) force+

lemma ground_range_vars[intro]: "ground (subst_range s) \<Longrightarrow> range_vars s = {}"
unfolding range_vars_alt_def by metis

lemma ground_subst_no_var[intro]: "ground (subst_range s) \<Longrightarrow> x \<notin> range_vars s"
using ground_range_vars[of s] by blast

lemma ground_img_obtain_fun:
  assumes "ground (subst_range s)" "x \<in> subst_domain s"
  obtains f T where "s x = Fun f T" "Fun f T \<in> subst_range s" "fv (Fun f T) = {}"
proof -
  from assms(2) obtain t where t: "s x = t" "t \<in> subst_range s" by moura
  hence "fv t = {}" using assms(1) by auto
  thus ?thesis using t that by (cases t) simp_all
qed

lemma ground_term_subst_domain_fv_subset:
  "fv (t \<cdot> \<delta>) = {} \<Longrightarrow> fv t \<subseteq> subst_domain \<delta>"
by (induct t) auto

lemma ground_subst_range_empty_fv:
  "ground (subst_range \<theta>) \<Longrightarrow> x \<in> subst_domain \<theta> \<Longrightarrow> fv (\<theta> x) = {}"
by simp

lemma subst_Var_notin_img: "x \<notin> range_vars s \<Longrightarrow> t \<cdot> s = Var x \<Longrightarrow> t = Var x"
using subst_not_img_fixed[of x t s] by (induct t) auto

lemma fv_in_subst_img: "\<lbrakk>s v = t; t \<noteq> Var v\<rbrakk> \<Longrightarrow> fv t \<subseteq> range_vars s"
unfolding range_vars_alt_def by auto

lemma empty_dom_iff_empty_subst: "subst_domain \<theta> = {} \<longleftrightarrow> \<theta> = Var" by auto

lemma subst_dom_cong: "(\<And>v t. \<theta> v = t \<Longrightarrow> \<delta> v = t) \<Longrightarrow> subst_domain \<theta> \<subseteq> subst_domain \<delta>"
by (auto simp add: subst_domain_def)

lemma subst_img_cong: "(\<And>v t. \<theta> v = t \<Longrightarrow> \<delta> v = t) \<Longrightarrow> range_vars \<theta> \<subseteq> range_vars \<delta>"
unfolding range_vars_alt_def by (auto simp add: subst_domain_def)

lemma subst_dom_elim: "subst_domain s \<inter> range_vars s = {} \<Longrightarrow> fv (t \<cdot> s) \<inter> subst_domain s = {}"
proof (induction t)
  case (Var v) thus ?case
    using fv_in_subst_img[of s] 
    by (cases "s v = Var v") (auto simp add: subst_domain_def)
next
  case Fun thus ?case by auto
qed

lemma subst_dom_insert_finite: "finite (subst_domain s) = finite (subst_domain (s(v := t)))"
proof
  assume "finite (subst_domain s)"
  have "subst_domain (s(v := t)) \<subseteq> insert v (subst_domain s)" by (auto simp add: subst_domain_def)
  thus "finite (subst_domain (s(v := t)))"
    by (meson \<open>finite (subst_domain s)\<close> finite_insert rev_finite_subset)
next
  assume *: "finite (subst_domain (s(v := t)))"
  hence "finite (insert v (subst_domain s))"
  proof (cases "t = Var v")
    case True
    hence "finite (subst_domain s - {v})" by (metis * subst_dom_update3)
    thus ?thesis by simp
  qed (metis * subst_dom_update2[of t v s])
  thus "finite (subst_domain s)" by simp
qed

lemma trm_subst_disj: "t \<cdot> \<theta> = t \<Longrightarrow> fv t \<inter> subst_domain \<theta> = {}"
proof (induction t)
  case (Fun f X)
  hence "map (\<lambda>x. x \<cdot> \<theta>) X = X" by simp
  hence "\<And>x. x \<in> set X \<Longrightarrow> x \<cdot> \<theta> = x" using map_eq_conv by fastforce
  thus ?case using Fun.IH by auto
qed (simp add: subst_domain_def)

lemma trm_subst_ident[intro]: "fv t \<inter> subst_domain \<theta> = {} \<Longrightarrow> t \<cdot> \<theta> = t"
proof -
  assume "fv t \<inter> subst_domain \<theta> = {}"
  hence "\<forall>v \<in> fv t. \<forall>w \<in> subst_domain \<theta>. v \<noteq> w" by auto
  thus ?thesis
    by (metis subst_agreement subst_apply_term.simps(1) subst_apply_term_empty subst_domI)
qed

lemma trm_subst_ident'[intro]: "v \<notin> subst_domain \<theta> \<Longrightarrow> (Var v) \<cdot> \<theta> = Var v"
using trm_subst_ident by (simp add: subst_domain_def)

lemma trm_subst_ident''[intro]: "(\<And>x. x \<in> fv t \<Longrightarrow> \<theta> x = Var x) \<Longrightarrow> t \<cdot> \<theta> = t"
proof -
  assume "\<And>x. x \<in> fv t \<Longrightarrow> \<theta> x = Var x"
  hence "fv t \<inter> subst_domain \<theta> = {}" by (auto simp add: subst_domain_def)
  thus ?thesis using trm_subst_ident by auto
qed

lemma set_subst_ident: "fv\<^sub>s\<^sub>e\<^sub>t M \<inter> subst_domain \<theta> = {} \<Longrightarrow> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> = M"
proof -
  assume "fv\<^sub>s\<^sub>e\<^sub>t M \<inter> subst_domain \<theta> = {}"
  hence "\<forall>t \<in> M. t \<cdot> \<theta> = t" by auto
  thus ?thesis by force
qed

lemma trm_subst_ident_subterms[intro]:
  "fv t \<inter> subst_domain \<theta> = {} \<Longrightarrow> subterms t \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> = subterms t"
using set_subst_ident[of "subterms t" \<theta>] fv_subterms[of t] by simp

lemma trm_subst_ident_subterms'[intro]:
  "v \<notin> fv t \<Longrightarrow> subterms t \<cdot>\<^sub>s\<^sub>e\<^sub>t Var(v := s) = subterms t"
using trm_subst_ident_subterms[of t "Var(v := s)"]
by (meson subst_no_occs trm_subst_disj vars_iff_subtermeq) 

lemma const_mem_subst_cases:
  assumes "Fun c [] \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
  shows "Fun c [] \<in> M \<or> Fun c [] \<in> \<theta> ` fv\<^sub>s\<^sub>e\<^sub>t M"
proof -
  obtain m where m: "m \<in> M" "m \<cdot> \<theta> = Fun c []" using assms by auto
  thus ?thesis by (cases m) force+
qed

lemma const_mem_subst_cases':
  assumes "Fun c [] \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
  shows "Fun c [] \<in> M \<or> Fun c [] \<in> subst_range \<theta>"
using const_mem_subst_cases[OF assms] by force

lemma fv_subterms_substI[intro]: "y \<in> fv t \<Longrightarrow> \<theta> y \<in> subterms t \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
using image_iff vars_iff_subtermeq by fastforce 

lemma fv_subterms_subst_eq[simp]: "fv\<^sub>s\<^sub>e\<^sub>t (subterms (t \<cdot> \<theta>)) = fv\<^sub>s\<^sub>e\<^sub>t (subterms t \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
using fv_subterms by (induct t) force+

lemma fv_subterms_set_subst: "fv\<^sub>s\<^sub>e\<^sub>t (subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) = fv\<^sub>s\<^sub>e\<^sub>t (subterms\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>))"
using fv_subterms_subst_eq[of _ \<theta>] by auto

lemma fv_subterms_set_subst': "fv\<^sub>s\<^sub>e\<^sub>t (subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) = fv\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
using fv_subterms_set[of "M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"] fv_subterms_set_subst[of \<theta> M] by simp

lemma fv_subst_subset: "x \<in> fv t \<Longrightarrow> fv (\<theta> x) \<subseteq> fv (t \<cdot> \<theta>)"
by (metis fv_subset image_eqI subst_apply_fv_unfold)

lemma fv_subst_subset': "fv s \<subseteq> fv t \<Longrightarrow> fv (s \<cdot> \<theta>) \<subseteq> fv (t \<cdot> \<theta>)"
using fv_subst_subset by (induct s) force+

lemma fv_subst_obtain_var:
  fixes \<delta>::"('a,'b) subst"
  assumes "x \<in> fv (t \<cdot> \<delta>)"
  shows "\<exists>y \<in> fv t. x \<in> fv (\<delta> y)"
using assms by (induct t) force+

lemma set_subst_all_ident: "fv\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<inter> subst_domain \<delta> = {} \<Longrightarrow> M \<cdot>\<^sub>s\<^sub>e\<^sub>t (\<theta> \<circ>\<^sub>s \<delta>) = M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
by (metis set_subst_ident subst_comp_all)

lemma subterms_subst:
  "subterms (t \<cdot> d) = (subterms t \<cdot>\<^sub>s\<^sub>e\<^sub>t d) \<union> subterms\<^sub>s\<^sub>e\<^sub>t (d ` (fv t \<inter> subst_domain d))"
by (induct t) (auto simp add: subst_domain_def)

lemma subterms_subst':
  fixes \<theta>::"('a,'b) subst"
  assumes "\<forall>x \<in> fv t. (\<exists>f. \<theta> x = Fun f []) \<or> (\<exists>y. \<theta> x = Var y)"
  shows "subterms (t \<cdot> \<theta>) = subterms t \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
using assms
proof (induction t)
  case (Var x) thus ?case
  proof (cases "x \<in> subst_domain \<theta>")
    case True
    hence "(\<exists>f. \<theta> x = Fun f []) \<or> (\<exists>y. \<theta> x = Var y)" using Var by simp
    hence "subterms (\<theta> x) = {\<theta> x}" by auto
    thus ?thesis by simp
  qed auto
qed auto

lemma subterms_subst'':
  fixes \<theta>::"('a,'b) subst"
  assumes "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M. (\<exists>f. \<theta> x = Fun f []) \<or> (\<exists>y. \<theta> x = Var y)"
  shows "subterms\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) = subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
using subterms_subst'[of _ \<theta>] assms by auto

lemma subterms_subst_subterm:
  fixes \<theta>::"('a,'b) subst"
  assumes "\<forall>x \<in> fv a. (\<exists>f. \<theta> x = Fun f []) \<or> (\<exists>y. \<theta> x = Var y)"
    and "b \<in> subterms (a \<cdot> \<theta>)"
  shows "\<exists>c \<in> subterms a. c \<cdot> \<theta> = b"
using subterms_subst'[OF assms(1)] assms(2) by auto

lemma subterms_subst_subset: "subterms t \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> subterms (t \<cdot> \<sigma>)"
by (induct t) auto

lemma subterms_subst_subset': "subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>)"
using subterms_subst_subset by fast

lemma subterms\<^sub>s\<^sub>e\<^sub>t_subst:
  fixes \<theta>::"('a,'b) subst"
  assumes "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
  shows "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> \<or> (\<exists>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M. t \<in> subterms (\<theta> x))"
using assms subterms_subst[of _ \<theta>] by auto

lemma rm_vars_dom: "subst_domain (rm_vars V s) = subst_domain s - V"
by (auto simp add: subst_domain_def)

lemma rm_vars_dom_subset: "subst_domain (rm_vars V s) \<subseteq> subst_domain s"
by (auto simp add: subst_domain_def)

lemma rm_vars_dom_eq':
  "subst_domain (rm_vars (UNIV - V) s) = subst_domain s \<inter> V"
using rm_vars_dom[of "UNIV - V" s] by blast

lemma rm_vars_img: "subst_range (rm_vars V s) = s ` subst_domain (rm_vars V s)"
by (auto simp add: subst_domain_def)

lemma rm_vars_img_subset: "subst_range (rm_vars V s) \<subseteq> subst_range s"
by (auto simp add: subst_domain_def)

lemma rm_vars_img_fv_subset: "range_vars (rm_vars V s) \<subseteq> range_vars s"
unfolding range_vars_alt_def by (auto simp add: subst_domain_def)

lemma rm_vars_fv_obtain:
  assumes "x \<in> fv (t \<cdot> rm_vars X \<theta>) - X"
  shows "\<exists>y \<in> fv t - X. x \<in> fv (rm_vars X \<theta> y)"
using assms by (induct t) (fastforce, force)

lemma rm_vars_apply: "v \<in> subst_domain (rm_vars V s) \<Longrightarrow> (rm_vars V s) v = s v"
by (auto simp add: subst_domain_def)

lemma rm_vars_apply': "subst_domain \<delta> \<inter> vs = {} \<Longrightarrow> rm_vars vs \<delta> = \<delta>"
by force

lemma rm_vars_ident: "fv t \<inter> vs = {} \<Longrightarrow> t \<cdot> (rm_vars vs \<theta>) = t \<cdot> \<theta>"
by (induct t) auto

lemma rm_vars_fv_subset: "fv (t \<cdot> rm_vars X \<theta>) \<subseteq> fv t \<union> fv (t \<cdot> \<theta>)"
by (induct t) auto

lemma rm_vars_fv_disj:
  assumes "fv t \<inter> X = {}" "fv (t \<cdot> \<theta>) \<inter> X = {}"
  shows "fv (t \<cdot> rm_vars X \<theta>) \<inter> X = {}"
using rm_vars_ident[OF assms(1)] assms(2) by auto

lemma rm_vars_ground_supports:
  assumes "ground (subst_range \<theta>)"
  shows "rm_vars X \<theta> supports \<theta>"
proof
  fix x
  have *: "ground (subst_range (rm_vars X \<theta>))"
    using rm_vars_img_subset[of X \<theta>] assms
    by (auto simp add: subst_domain_def)
  show "rm_vars X \<theta> x \<cdot> \<theta> = \<theta> x "
  proof (cases "x \<in> subst_domain (rm_vars X \<theta>)")
    case True
    hence "fv (rm_vars X \<theta> x) = {}" using * by auto
    thus ?thesis using True by auto
  qed (simp add: subst_domain_def)
qed

lemma rm_vars_split:
  assumes "ground (subst_range \<theta>)"
  shows "\<theta> = rm_vars X \<theta> \<circ>\<^sub>s rm_vars (subst_domain \<theta> - X) \<theta>"
proof -
  let ?s1 = "rm_vars X \<theta>"
  let ?s2 = "rm_vars (subst_domain \<theta> - X) \<theta>"

  have doms: "subst_domain ?s1 \<subseteq> subst_domain \<theta>" "subst_domain ?s2 \<subseteq> subst_domain \<theta>"
    by (auto simp add: subst_domain_def)

  { fix x assume "x \<notin> subst_domain \<theta>"
    hence "\<theta> x = Var x" "?s1 x = Var x" "?s2 x = Var x" using doms by auto
    hence "\<theta> x = (?s1 \<circ>\<^sub>s ?s2) x" by (simp add: subst_compose_def)
  } moreover {
    fix x assume "x \<in> subst_domain \<theta>" "x \<in> X"
    hence "?s1 x = Var x" "?s2 x = \<theta> x" using doms by auto
    hence "\<theta> x = (?s1 \<circ>\<^sub>s ?s2) x" by (simp add: subst_compose_def)
  } moreover {
    fix x assume "x \<in> subst_domain \<theta>" "x \<notin> X"
    hence "?s1 x = \<theta> x" "fv (\<theta> x) = {}" using assms doms by auto
    hence "\<theta> x = (?s1 \<circ>\<^sub>s ?s2) x" by (simp add: subst_compose subst_ground_ident)
  } ultimately show ?thesis by blast
qed

lemma rm_vars_fv_img_disj:
  assumes "fv t \<inter> X = {}" "X \<inter> range_vars \<theta> = {}"
  shows "fv (t \<cdot> rm_vars X \<theta>) \<inter> X = {}"
using assms
proof (induction t)
  case (Var x)
  hence *: "(rm_vars X \<theta>) x = \<theta> x" by auto
  show ?case
  proof (cases "x \<in> subst_domain \<theta>")
    case True
    hence "\<theta> x \<in> subst_range \<theta>" by auto
    hence "fv (\<theta> x) \<inter> X = {}" using Var.prems(2) unfolding range_vars_alt_def by fastforce
    thus ?thesis using * by auto
  next
    case False thus ?thesis using Var.prems(1) by auto
  qed
next
  case Fun thus ?case by auto
qed

lemma subst_apply_dom_ident: "t \<cdot> \<theta> = t \<Longrightarrow> subst_domain \<delta> \<subseteq> subst_domain \<theta> \<Longrightarrow> t \<cdot> \<delta> = t"
proof (induction t)
  case (Fun f T) thus ?case by (induct T) auto
qed (auto simp add: subst_domain_def)

lemma rm_vars_subst_apply_ident:
  assumes "t \<cdot> \<theta> = t"
  shows "t \<cdot> (rm_vars vs \<theta>) = t"
using rm_vars_dom[of vs \<theta>] subst_apply_dom_ident[OF assms, of "rm_vars vs \<theta>"] by auto

lemma rm_vars_subst_eq:
  "t \<cdot> \<delta> = t \<cdot> rm_vars (subst_domain \<delta> - subst_domain \<delta> \<inter> fv t) \<delta>"
by (auto intro: term_subst_eq)

lemma rm_vars_subst_eq':
  "t \<cdot> \<delta> = t \<cdot> rm_vars (UNIV - fv t) \<delta>"
by (auto intro: term_subst_eq)

lemma rm_vars_comp:
  assumes "range_vars \<delta> \<inter> vs = {}"
  shows "t \<cdot> rm_vars vs (\<delta> \<circ>\<^sub>s \<theta>) = t \<cdot> (rm_vars vs \<delta> \<circ>\<^sub>s rm_vars vs \<theta>)"
using assms
proof (induction t)
  case (Var x) thus ?case
  proof (cases "x \<in> vs")
    case True thus ?thesis using Var by auto
  next
    case False
    have "subst_domain (rm_vars vs \<theta>) \<inter> vs = {}" by (auto simp add: subst_domain_def)
    moreover have "fv (\<delta> x) \<inter> vs = {}"
      using Var False unfolding range_vars_alt_def by force
    ultimately have "\<delta> x \<cdot> (rm_vars vs \<theta>) = \<delta> x \<cdot> \<theta>"
      using rm_vars_ident by (simp add: subst_domain_def)
    moreover have "(rm_vars vs (\<delta> \<circ>\<^sub>s \<theta>)) x = (\<delta> \<circ>\<^sub>s \<theta>) x" by (metis False)
    ultimately show ?thesis using subst_compose by auto
  qed
next
  case Fun thus ?case by auto
qed

lemma rm_vars_fv\<^sub>s\<^sub>e\<^sub>t_subst:
  assumes "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (rm_vars X \<theta> ` Y)"
  shows "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` Y) \<or> x \<in> X"
using assms by auto

lemma disj_dom_img_var_notin:
  assumes "subst_domain \<theta> \<inter> range_vars \<theta> = {}" "\<theta> v = t" "t \<noteq> Var v"
  shows "v \<notin> fv t" "\<forall>v \<in> fv (t \<cdot> \<theta>). v \<notin> subst_domain \<theta>"
proof -
  have "v \<in> subst_domain \<theta>" "fv t \<subseteq> range_vars \<theta>"
    using fv_in_subst_img[of \<theta> v t, OF assms(2)] assms(2,3)
    by (auto simp add: subst_domain_def)
  thus "v \<notin> fv t" using assms(1) by auto

  have *: "fv t \<inter> subst_domain \<theta> = {}"
    using assms(1) \<open>fv t \<subseteq> range_vars \<theta>\<close>
    by auto
  hence "t \<cdot> \<theta> = t" by blast
  thus "\<forall>v \<in> fv (t \<cdot> \<theta>). v \<notin> subst_domain \<theta>" using * by auto
qed

lemma subst_sends_dom_to_img: "v \<in> subst_domain \<theta> \<Longrightarrow> fv (Var v \<cdot> \<theta>) \<subseteq> range_vars \<theta>"
unfolding range_vars_alt_def by auto

lemma subst_sends_fv_to_img: "fv (t \<cdot> s) \<subseteq> fv t \<union> range_vars s"
proof (induction t)
  case (Var v) thus ?case
  proof (cases "Var v \<cdot> s = Var v")
    case True thus ?thesis by simp
  next
    case False
    hence "v \<in> subst_domain s" by (meson trm_subst_ident') 
    hence "fv (Var v \<cdot> s) \<subseteq> range_vars s"
      using subst_sends_dom_to_img by simp
    thus ?thesis by auto
  qed
next
  case Fun thus ?case by auto
qed 

lemma ident_comp_subst_trm_if_disj:
  assumes "subst_domain \<sigma> \<inter> range_vars \<theta> = {}" "v \<in> subst_domain \<theta>"
  shows "(\<theta> \<circ>\<^sub>s \<sigma>) v = \<theta> v"
proof -
  from assms have " subst_domain \<sigma> \<inter> fv (\<theta> v) = {}"
    using fv_in_subst_img unfolding range_vars_alt_def by auto
  thus "(\<theta> \<circ>\<^sub>s \<sigma>) v = \<theta> v" unfolding subst_compose_def by blast
qed

lemma ident_comp_subst_trm_if_disj': "fv (\<theta> v) \<inter> subst_domain \<sigma> = {} \<Longrightarrow> (\<theta> \<circ>\<^sub>s \<sigma>) v = \<theta> v"
unfolding subst_compose_def by blast

lemma subst_idemI[intro]: "subst_domain \<sigma> \<inter> range_vars \<sigma> = {} \<Longrightarrow> subst_idem \<sigma>"
using ident_comp_subst_trm_if_disj[of \<sigma> \<sigma>]
      var_not_in_subst_dom[of _ \<sigma>]
      subst_eq_if_eq_vars[of \<sigma>]
by (metis subst_idem_def subst_compose_def var_comp(2)) 

lemma subst_idemI'[intro]: "ground (subst_range \<sigma>) \<Longrightarrow> subst_idem \<sigma>"
proof (intro subst_idemI)
  assume "ground (subst_range \<sigma>)"
  hence "range_vars \<sigma> = {}" by (metis ground_range_vars)
  thus "subst_domain \<sigma> \<inter> range_vars \<sigma> = {}" by blast
qed

lemma subst_idemE: "subst_idem \<sigma> \<Longrightarrow> subst_domain \<sigma> \<inter> range_vars \<sigma> = {}"
proof -
  assume "subst_idem \<sigma>"
  hence "\<And>v. fv (\<sigma> v) \<inter> subst_domain \<sigma> = {}"
    unfolding subst_idem_def subst_compose_def by (metis trm_subst_disj)
  thus ?thesis
    unfolding range_vars_alt_def by auto
qed

lemma subst_idem_rm_vars: "subst_idem \<theta> \<Longrightarrow> subst_idem (rm_vars X \<theta>)"
proof -
  assume "subst_idem \<theta>"
  hence "subst_domain \<theta> \<inter> range_vars \<theta> = {}" by (metis subst_idemE)
  moreover have
      "subst_domain (rm_vars X \<theta>) \<subseteq> subst_domain \<theta>"
      "range_vars (rm_vars X \<theta>) \<subseteq> range_vars \<theta>"
    unfolding range_vars_alt_def by (auto simp add: subst_domain_def)
  ultimately show ?thesis by blast
qed

lemma subst_fv_bounded_if_img_bounded: "range_vars \<theta> \<subseteq> fv t \<union> V \<Longrightarrow> fv (t \<cdot> \<theta>) \<subseteq> fv t \<union> V"
proof (induction t)
  case (Var v) thus ?case unfolding range_vars_alt_def by (cases "\<theta> v = Var v") auto
qed (metis (no_types, lifting) Un_assoc Un_commute subst_sends_fv_to_img sup.absorb_iff2)

lemma subst_fv_bound_singleton: "fv (t \<cdot> Var(v := t')) \<subseteq> fv t \<union> fv t'"
using subst_fv_bounded_if_img_bounded[of "Var(v := t')" t "fv t'"]
unfolding range_vars_alt_def by (auto simp add: subst_domain_def)

lemma subst_fv_bounded_if_img_bounded':
  assumes "range_vars \<theta> \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M"
  shows "fv\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M"
proof
  fix v assume *:  "v \<in> fv\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
  
  obtain t where t: "t \<in> M" "t \<cdot> \<theta> \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>" "v \<in> fv (t \<cdot> \<theta>)"
  proof -
    assume **: "\<And>t. \<lbrakk>t \<in> M; t \<cdot> \<theta> \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>; v \<in> fv (t \<cdot> \<theta>)\<rbrakk> \<Longrightarrow> thesis"
    have "v \<in> \<Union> (fv ` ((\<lambda>t. t \<cdot> \<theta>) ` M))" using * by (metis fv\<^sub>s\<^sub>e\<^sub>t.simps)
    hence "\<exists>t. t \<in> M \<and> v \<in> fv (t \<cdot> \<theta>)" by blast
    thus ?thesis using ** imageI by blast
  qed

  from \<open>t \<in> M\<close> obtain M' where "t \<notin> M'" "M = insert t M'" by (meson Set.set_insert) 
  hence "fv\<^sub>s\<^sub>e\<^sub>t M = fv t \<union> fv\<^sub>s\<^sub>e\<^sub>t M'" by simp
  hence "fv (t \<cdot> \<theta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M" using subst_fv_bounded_if_img_bounded assms by simp
  thus "v \<in> fv\<^sub>s\<^sub>e\<^sub>t M" using assms \<open>v \<in> fv (t \<cdot> \<theta>)\<close> by auto
qed

lemma ground_img_if_ground_subst: "(\<And>v t. s v = t \<Longrightarrow> fv t = {}) \<Longrightarrow> range_vars s = {}"
unfolding range_vars_alt_def by auto

lemma ground_subst_fv_subset: "ground (subst_range \<theta>) \<Longrightarrow> fv (t \<cdot> \<theta>) \<subseteq> fv t"
using subst_fv_bounded_if_img_bounded[of \<theta>]
unfolding range_vars_alt_def by force

lemma ground_subst_fv_subset': "ground (subst_range \<theta>) \<Longrightarrow> fv\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M"
using subst_fv_bounded_if_img_bounded'[of \<theta> M]
unfolding range_vars_alt_def by auto

lemma subst_to_var_is_var[elim]: "t \<cdot> s = Var v \<Longrightarrow> \<exists>w. t = Var w"
using subst_apply_term.elims by blast

lemma subst_dom_comp_inI:
  assumes "y \<notin> subst_domain \<sigma>"
    and "y \<in> subst_domain \<delta>"
  shows "y \<in> subst_domain (\<sigma> \<circ>\<^sub>s \<delta>)"
using assms subst_domain_subst_compose[of \<sigma> \<delta>] by blast

lemma subst_comp_notin_dom_eq:
  "x \<notin> subst_domain \<theta>1 \<Longrightarrow> (\<theta>1 \<circ>\<^sub>s \<theta>2) x = \<theta>2 x"
unfolding subst_compose_def by fastforce

lemma subst_dom_comp_eq:
  assumes "subst_domain \<theta> \<inter> range_vars \<sigma> = {}"
  shows "subst_domain (\<theta> \<circ>\<^sub>s \<sigma>) = subst_domain \<theta> \<union> subst_domain \<sigma>"
proof (rule ccontr)
  assume "subst_domain (\<theta> \<circ>\<^sub>s \<sigma>) \<noteq> subst_domain \<theta> \<union> subst_domain \<sigma>"
  hence "subst_domain (\<theta> \<circ>\<^sub>s \<sigma>) \<subset> subst_domain \<theta> \<union> subst_domain \<sigma>"
    using subst_domain_compose[of \<theta> \<sigma>] by (simp add: subst_domain_def)
  then obtain v where "v \<notin> subst_domain (\<theta> \<circ>\<^sub>s \<sigma>)" "v \<in> subst_domain \<theta> \<union> subst_domain \<sigma>" by auto
  hence v_in_some_subst: "\<theta> v \<noteq> Var v \<or> \<sigma> v \<noteq> Var v" and "\<theta> v \<cdot> \<sigma> = Var v"
    unfolding subst_compose_def by (auto simp add: subst_domain_def)
  then obtain w where "\<theta> v = Var w" using subst_to_var_is_var by fastforce
  show False
  proof (cases "v = w")
    case True
    hence "\<theta> v = Var v" using \<open>\<theta> v = Var w\<close> by simp
    hence "\<sigma> v \<noteq> Var v" using v_in_some_subst by simp
    thus False using \<open>\<theta> v = Var v\<close> \<open>\<theta> v \<cdot> \<sigma> = Var v\<close> by simp
  next
    case False
    hence "v \<in> subst_domain \<theta>" using v_in_some_subst \<open>\<theta> v \<cdot> \<sigma> = Var v\<close> by auto 
    hence "v \<notin> range_vars \<sigma>" using assms by auto
    moreover have "\<sigma> w = Var v" using \<open>\<theta> v \<cdot> \<sigma> = Var v\<close> \<open>\<theta> v = Var w\<close> by simp
    hence "v \<in> range_vars \<sigma>" using \<open>v \<noteq> w\<close> subst_fv_imgI[of \<sigma> w] by simp
    ultimately show False ..
  qed
qed

lemma subst_img_comp_subset[simp]:
  "range_vars (\<theta>1 \<circ>\<^sub>s \<theta>2) \<subseteq> range_vars \<theta>1 \<union> range_vars \<theta>2"
proof
  let ?img = "range_vars"
  fix x assume "x \<in> ?img (\<theta>1 \<circ>\<^sub>s \<theta>2)"
  then obtain v t where vt: "x \<in> fv t" "t = (\<theta>1 \<circ>\<^sub>s \<theta>2) v" "t \<noteq> Var v"
    unfolding range_vars_alt_def subst_compose_def by (auto simp add: subst_domain_def)

  { assume "x \<notin> ?img \<theta>1" hence "x \<in> ?img \<theta>2"
      by (metis (no_types, hide_lams) fv_in_subst_img Un_iff subst_compose_def 
                vt subsetCE subst_apply_term.simps(1) subst_sends_fv_to_img) 
  }
  thus "x \<in> ?img \<theta>1 \<union> ?img \<theta>2" by auto
qed

lemma subst_img_comp_subset':
  assumes "t \<in> subst_range (\<theta>1 \<circ>\<^sub>s \<theta>2)"
  shows "t \<in> subst_range \<theta>2 \<or> (\<exists>t' \<in> subst_range \<theta>1. t = t' \<cdot> \<theta>2)"
proof -
  obtain x where x: "x \<in> subst_domain (\<theta>1 \<circ>\<^sub>s \<theta>2)" "(\<theta>1 \<circ>\<^sub>s \<theta>2) x = t" "t \<noteq> Var x"
    using assms by (auto simp add: subst_domain_def)
  { assume "x \<notin> subst_domain \<theta>1"
    hence "(\<theta>1 \<circ>\<^sub>s \<theta>2) x = \<theta>2 x" unfolding subst_compose_def by auto
    hence ?thesis using x by auto
  } moreover {
    assume "x \<in> subst_domain \<theta>1" hence ?thesis using subst_compose x(2) by fastforce 
  } ultimately show ?thesis by metis
qed

lemma subst_img_comp_subset'':
  "subterms\<^sub>s\<^sub>e\<^sub>t (subst_range (\<theta>1 \<circ>\<^sub>s \<theta>2)) \<subseteq>
   subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>2) \<union> ((subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>1)) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>2)"
proof
  fix t assume "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range (\<theta>1 \<circ>\<^sub>s \<theta>2))"
  then obtain x where x: "x \<in> subst_domain (\<theta>1 \<circ>\<^sub>s \<theta>2)" "t \<in> subterms ((\<theta>1 \<circ>\<^sub>s \<theta>2) x)"
    by auto
  show "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>2) \<union> (subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>1) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>2)"
  proof (cases "x \<in> subst_domain \<theta>1")
    case True thus ?thesis
      using subst_compose[of \<theta>1 \<theta>2] x(2) subterms_subst
      by fastforce
  next
    case False
    hence "(\<theta>1 \<circ>\<^sub>s \<theta>2) x = \<theta>2 x" unfolding subst_compose_def by auto
    thus ?thesis using x by (auto simp add: subst_domain_def)
  qed
qed

lemma subst_img_comp_subset''':
  "subterms\<^sub>s\<^sub>e\<^sub>t (subst_range (\<theta>1 \<circ>\<^sub>s \<theta>2)) - range Var \<subseteq>
   subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>2) - range Var \<union> ((subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>1) - range Var) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>2)"
proof
  fix t assume t: "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range (\<theta>1 \<circ>\<^sub>s \<theta>2)) - range Var"
  then obtain f T where fT: "t = Fun f T" by (cases t) simp_all
  then obtain x where x: "x \<in> subst_domain (\<theta>1 \<circ>\<^sub>s \<theta>2)" "Fun f T \<in> subterms ((\<theta>1 \<circ>\<^sub>s \<theta>2) x)"
    using t by auto
  have "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>2) \<union> (subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>1) - range Var \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>2)"
  proof (cases "x \<in> subst_domain \<theta>1")
    case True
    hence "Fun f T \<in> (subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>2)) \<union> (subterms (\<theta>1 x) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>2)"
      using x(2) subterms_subst[of "\<theta>1 x" \<theta>2]
      unfolding subst_compose[of \<theta>1 \<theta>2 x] by auto
    moreover have ?thesis when *: "Fun f T \<in> subterms (\<theta>1 x) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>2"
    proof -
      obtain s where s: "s \<in> subterms (\<theta>1 x)" "Fun f T = s \<cdot> \<theta>2" using * by moura
      show ?thesis
      proof (cases s)
        case (Var y)
        hence "Fun f T \<in> subst_range \<theta>2" using s by force
        thus ?thesis by blast
      next
        case (Fun g S)
        hence "Fun f T \<in> (subterms (\<theta>1 x) - range Var) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>2" using s by blast
        thus ?thesis using True by auto
      qed
    qed
    ultimately show ?thesis by blast
  next
    case False
    hence "(\<theta>1 \<circ>\<^sub>s \<theta>2) x = \<theta>2 x" unfolding subst_compose_def by auto
    thus ?thesis using x by (auto simp add: subst_domain_def)
  qed
  thus "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>2) - range Var \<union>
            (subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>1) - range Var \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>2)"
    using fT by auto
qed

lemma subst_img_comp_subset_const:
  assumes "Fun c [] \<in> subst_range (\<theta>1 \<circ>\<^sub>s \<theta>2)"
  shows "Fun c [] \<in> subst_range \<theta>2 \<or> Fun c [] \<in> subst_range \<theta>1 \<or>
         (\<exists>x. Var x \<in> subst_range \<theta>1 \<and> \<theta>2 x = Fun c [])"
proof (cases "Fun c [] \<in> subst_range \<theta>2")
  case False
  then obtain t where t: "t \<in> subst_range \<theta>1" "Fun c [] = t \<cdot> \<theta>2" 
    using subst_img_comp_subset'[OF assms] by auto
  thus ?thesis by (cases t) auto
qed (simp add: subst_img_comp_subset'[OF assms])

lemma subst_img_comp_subset_const':
  fixes \<delta> \<tau>::"('f,'v) subst"
  assumes "(\<delta> \<circ>\<^sub>s \<tau>) x = Fun c []"
  shows "\<delta> x = Fun c [] \<or> (\<exists>z. \<delta> x = Var z \<and> \<tau> z = Fun c [])"
proof (cases "\<delta> x = Fun c []")
  case False
  then obtain t where "\<delta> x = t" "t \<cdot> \<tau> = Fun c []" using assms unfolding subst_compose_def by auto
  thus ?thesis by (cases t) auto
qed simp

lemma subst_img_comp_subset_ground:
  assumes "ground (subst_range \<theta>1)"
  shows "subst_range (\<theta>1 \<circ>\<^sub>s \<theta>2) \<subseteq> subst_range \<theta>1 \<union> subst_range \<theta>2"
proof
  fix t assume t: "t \<in> subst_range (\<theta>1 \<circ>\<^sub>s \<theta>2)"
  then obtain x where x: "x \<in> subst_domain (\<theta>1 \<circ>\<^sub>s \<theta>2)" "t = (\<theta>1 \<circ>\<^sub>s \<theta>2) x" by auto

  show "t \<in> subst_range \<theta>1 \<union> subst_range \<theta>2"
  proof (cases "x \<in> subst_domain \<theta>1")
    case True
    hence "fv (\<theta>1 x) = {}" using assms ground_subst_range_empty_fv by fast
    hence "t = \<theta>1 x" using x(2) unfolding subst_compose_def by blast
    thus ?thesis using True by simp
  next
    case False
    hence "t = \<theta>2 x" "x \<in> subst_domain \<theta>2"
      using x subst_domain_compose[of \<theta>1 \<theta>2]
      by (metis subst_comp_notin_dom_eq, blast)
    thus ?thesis using x by simp
  qed
qed

lemma subst_fv_dom_img_single:
  assumes "v \<notin> fv t" "\<sigma> v = t" "\<And>w. v \<noteq> w \<Longrightarrow> \<sigma> w = Var w"
  shows "subst_domain \<sigma> = {v}" "range_vars \<sigma> = fv t"
proof -
  show "subst_domain \<sigma> = {v}" using assms by (fastforce simp add: subst_domain_def)
  have "fv t \<subseteq> range_vars \<sigma>" by (metis fv_in_subst_img assms(1,2) vars_iff_subterm_or_eq) 
  moreover have "\<And>v. \<sigma> v \<noteq> Var v \<Longrightarrow> \<sigma> v = t" using assms by fastforce
  ultimately show "range_vars \<sigma> = fv t"
    unfolding range_vars_alt_def
    by (auto simp add: subst_domain_def)
qed

lemma subst_comp_upd1:
  "\<theta>(v := t) \<circ>\<^sub>s \<sigma> = (\<theta> \<circ>\<^sub>s \<sigma>)(v := t \<cdot> \<sigma>)"
unfolding subst_compose_def by auto

lemma subst_comp_upd2:
  assumes "v \<notin> subst_domain s" "v \<notin> range_vars s"
  shows "s(v := t) = s \<circ>\<^sub>s (Var(v := t))"
unfolding subst_compose_def
proof -
  { fix w
    have "(s(v := t)) w = s w \<cdot> Var(v := t)"
    proof (cases "w = v")
      case True
      hence "s w = Var w" using \<open>v \<notin> subst_domain s\<close> by (simp add: subst_domain_def)
      thus ?thesis using \<open>w = v\<close> by simp
    next
      case False
      hence "(s(v := t)) w = s w" by simp
      moreover have "s w \<cdot> Var(v := t) = s w" using \<open>w \<noteq> v\<close> \<open>v \<notin> range_vars s\<close> 
        by (metis fv_in_subst_img fun_upd_apply insert_absorb insert_subset
                  repl_invariance subst_apply_term.simps(1) subst_apply_term_empty)
      ultimately show ?thesis ..
    qed
  }
  thus "s(v := t) = (\<lambda>w. s w \<cdot> Var(v := t))" by auto
qed

lemma ground_subst_dom_iff_img:
  "ground (subst_range \<sigma>) \<Longrightarrow> x \<in> subst_domain \<sigma> \<longleftrightarrow> \<sigma> x \<in> subst_range \<sigma>"
by (auto simp add: subst_domain_def)

lemma finite_dom_subst_exists:
  "finite S \<Longrightarrow> \<exists>\<sigma>::('f,'v) subst. subst_domain \<sigma> = S"
proof (induction S rule: finite.induct)
  case (insertI A a)
  then obtain \<sigma>::"('f,'v) subst" where "subst_domain \<sigma> = A" by blast
  fix f::'f
  have "subst_domain (\<sigma>(a := Fun f [])) = insert a A"
    using \<open>subst_domain \<sigma> = A\<close>
    by (auto simp add: subst_domain_def)
  thus ?case by metis
qed (auto simp add: subst_domain_def)

lemma subst_inj_is_bij_betw_dom_img_if_ground_img:
  assumes "ground (subst_range \<sigma>)"
  shows "inj \<sigma> \<longleftrightarrow> bij_betw \<sigma> (subst_domain \<sigma>) (subst_range \<sigma>)" (is "?A \<longleftrightarrow> ?B")
proof
  show "?A \<Longrightarrow> ?B" by (metis bij_betw_def injD inj_onI subst_range.simps)
next
  assume ?B
  hence "inj_on \<sigma> (subst_domain \<sigma>)" unfolding bij_betw_def by auto
  moreover have "\<And>x. x \<in> UNIV - subst_domain \<sigma> \<Longrightarrow> \<sigma> x = Var x" by auto
  hence "inj_on \<sigma> (UNIV - subst_domain \<sigma>)"
    using inj_onI[of "UNIV - subst_domain \<sigma>"]
    by (metis term.inject(1))
  moreover have "\<And>x y. x \<in> subst_domain \<sigma> \<Longrightarrow> y \<notin> subst_domain \<sigma> \<Longrightarrow> \<sigma> x \<noteq> \<sigma> y"
    using assms by (auto simp add: subst_domain_def)
  ultimately show ?A by (metis injI inj_onD subst_domI term.inject(1))
qed

lemma bij_finite_ground_subst_exists:
  assumes "finite (S::'v set)" "infinite (U::('f,'v) term set)" "ground U"
  shows "\<exists>\<sigma>::('f,'v) subst. subst_domain \<sigma> = S
                          \<and> bij_betw \<sigma> (subst_domain \<sigma>) (subst_range \<sigma>)
                          \<and> subst_range \<sigma> \<subseteq> U"
proof -
  obtain T' where "T' \<subseteq> U" "card T' = card S" "finite T'"
    by (meson assms(2) finite_Diff2 infinite_arbitrarily_large)
  then obtain f::"'v \<Rightarrow> ('f,'v) term" where f_bij: "bij_betw f S T'"
    using finite_same_card_bij[OF assms(1)] by metis
  hence *: "\<And>v. v \<in> S \<Longrightarrow> f v \<noteq> Var v"
    using \<open>ground U\<close> \<open>T' \<subseteq> U\<close> bij_betwE
    by fastforce

  let ?\<sigma> = "\<lambda>v. if v \<in> S then f v else Var v"
  have "subst_domain ?\<sigma> = S"
  proof
    show "subst_domain ?\<sigma> \<subseteq> S" by (auto simp add: subst_domain_def)

    { fix v assume "v \<in> S" "v \<notin> subst_domain ?\<sigma>"
      hence "f v = Var v" by (simp add: subst_domain_def)
      hence False using *[OF \<open>v \<in> S\<close>] by metis
    }
    thus "S \<subseteq> subst_domain ?\<sigma>" by blast
  qed
  hence "\<And>v w. \<lbrakk>v \<in> subst_domain ?\<sigma>; w \<notin> subst_domain ?\<sigma>\<rbrakk> \<Longrightarrow> ?\<sigma> w \<noteq> ?\<sigma> v"
    using \<open>ground U\<close> bij_betwE[OF f_bij] set_rev_mp[OF _ \<open>T' \<subseteq> U\<close>]
    by (metis (no_types, lifting) UN_iff empty_iff vars_iff_subterm_or_eq fv\<^sub>s\<^sub>e\<^sub>t.simps) 
  hence "inj_on ?\<sigma> (subst_domain ?\<sigma>)"
    using f_bij \<open>subst_domain ?\<sigma> = S\<close>
    unfolding bij_betw_def inj_on_def
    by metis
  hence "bij_betw ?\<sigma> (subst_domain ?\<sigma>) (subst_range ?\<sigma>)"
    using inj_on_imp_bij_betw[of ?\<sigma>] by simp
  moreover have "subst_range ?\<sigma> = T'"
    using \<open>bij_betw f S T'\<close> \<open>subst_domain ?\<sigma> = S\<close>
    unfolding bij_betw_def by auto 
  hence "subst_range ?\<sigma> \<subseteq> U" using \<open>T' \<subseteq> U\<close> by auto
  ultimately show ?thesis using \<open>subst_domain ?\<sigma> = S\<close> by (metis (lifting))
qed

lemma bij_finite_const_subst_exists:
  assumes "finite (S::'v set)" "finite (T::'f set)" "infinite (U::'f set)"
  shows "\<exists>\<sigma>::('f,'v) subst. subst_domain \<sigma> = S
                          \<and> bij_betw \<sigma> (subst_domain \<sigma>) (subst_range \<sigma>)
                          \<and> subst_range \<sigma> \<subseteq> (\<lambda>c. Fun c []) ` (U - T)"
proof -
  obtain T' where "T' \<subseteq> U - T" "card T' = card S" "finite T'"
    by (meson assms(2,3) finite_Diff2 infinite_arbitrarily_large)
  then obtain f::"'v \<Rightarrow> 'f" where f_bij: "bij_betw f S T'"
    using finite_same_card_bij[OF assms(1)] by metis

  let ?\<sigma> = "\<lambda>v. if v \<in> S then Fun (f v) [] else Var v"
  have "subst_domain ?\<sigma> = S" by (simp add: subst_domain_def)
  moreover have "\<And>v w. \<lbrakk>v \<in> subst_domain ?\<sigma>; w \<notin> subst_domain ?\<sigma>\<rbrakk> \<Longrightarrow> ?\<sigma> w \<noteq> ?\<sigma> v" by auto
  hence "inj_on ?\<sigma> (subst_domain ?\<sigma>)"
    using f_bij unfolding bij_betw_def inj_on_def
    by (metis \<open>subst_domain ?\<sigma> = S\<close> term.inject(2))
  hence "bij_betw ?\<sigma> (subst_domain ?\<sigma>) (subst_range ?\<sigma>)"
    using inj_on_imp_bij_betw[of ?\<sigma>] by simp
  moreover have "subst_range ?\<sigma> = ((\<lambda>c. Fun c []) ` T')"
    using \<open>bij_betw f S T'\<close> unfolding bij_betw_def inj_on_def by (auto simp add: subst_domain_def)
  hence "subst_range ?\<sigma> \<subseteq> ((\<lambda>c. Fun c []) ` (U - T))" using \<open>T' \<subseteq> U - T\<close> by auto
  ultimately show ?thesis by (metis (lifting))
qed

lemma bij_finite_const_subst_exists':
  assumes "finite (S::'v set)" "finite (T::('f,'v) terms)" "infinite (U::'f set)"
  shows "\<exists>\<sigma>::('f,'v) subst. subst_domain \<sigma> = S
                          \<and> bij_betw \<sigma> (subst_domain \<sigma>) (subst_range \<sigma>)
                          \<and> subst_range \<sigma> \<subseteq> ((\<lambda>c. Fun c []) ` U) - T"
proof -
  have "finite (\<Union>(funs_term ` T))" using assms(2) by auto
  then obtain \<sigma> where \<sigma>:
      "subst_domain \<sigma> = S" "bij_betw \<sigma> (subst_domain \<sigma>) (subst_range \<sigma>)"
      "subst_range \<sigma> \<subseteq> (\<lambda>c. Fun c []) ` (U - (\<Union>(funs_term ` T)))"
    using bij_finite_const_subst_exists[OF assms(1) _ assms(3)] by blast
  moreover have "(\<lambda>c. Fun c []) ` (U - (\<Union>(funs_term ` T))) \<subseteq> ((\<lambda>c. Fun c []) ` U) - T" by auto
  ultimately show ?thesis by blast
qed

lemma bij_betw_iteI:
  assumes "bij_betw f A B" "bij_betw g C D" "A \<inter> C = {}" "B \<inter> D = {}"
  shows "bij_betw (\<lambda>x. if x \<in> A then f x else g x) (A \<union> C) (B \<union> D)"
proof -
  have "bij_betw (\<lambda>x. if x \<in> A then f x else g x) A B"
    by (metis bij_betw_cong[of A f "\<lambda>x. if x \<in> A then f x else g x" B] assms(1))
  moreover have "bij_betw (\<lambda>x. if x \<in> A then f x else g x) C D"
    using bij_betw_cong[of C g "\<lambda>x. if x \<in> A then f x else g x" D] assms(2,3) by force
  ultimately show ?thesis using bij_betw_combine[OF _ _ assms(4)] by metis
qed

lemma subst_comp_split:
  assumes "subst_domain \<theta> \<inter> range_vars \<theta> = {}"
  shows "\<theta> = (rm_vars (subst_domain \<theta> - V) \<theta>) \<circ>\<^sub>s (rm_vars V \<theta>)" (is ?P)
    and "\<theta> = (rm_vars V \<theta>) \<circ>\<^sub>s (rm_vars (subst_domain \<theta> - V) \<theta>)" (is ?Q)
proof -
  let ?rm1 = "rm_vars (subst_domain \<theta> - V) \<theta>" and ?rm2 = "rm_vars V \<theta>"
  have "subst_domain ?rm2 \<inter> range_vars ?rm1 = {}"
       "subst_domain ?rm1 \<inter> range_vars ?rm2 = {}"
    using assms unfolding range_vars_alt_def by (force simp add: subst_domain_def)+
  hence *: "\<And>v. v \<in> subst_domain ?rm1 \<Longrightarrow> (?rm1 \<circ>\<^sub>s ?rm2) v = \<theta> v"
           "\<And>v. v \<in> subst_domain ?rm2 \<Longrightarrow> (?rm2 \<circ>\<^sub>s ?rm1) v = \<theta> v"
    using ident_comp_subst_trm_if_disj[of ?rm2 ?rm1]
          ident_comp_subst_trm_if_disj[of ?rm1 ?rm2]
    by (auto simp add: subst_domain_def)
  hence "\<And>v. v \<notin> subst_domain ?rm1 \<Longrightarrow> (?rm1 \<circ>\<^sub>s ?rm2) v = \<theta> v"
        "\<And>v. v \<notin> subst_domain ?rm2 \<Longrightarrow> (?rm2 \<circ>\<^sub>s ?rm1) v = \<theta> v"
    unfolding subst_compose_def by (auto simp add: subst_domain_def)
  hence "\<And>v. (?rm1 \<circ>\<^sub>s ?rm2) v = \<theta> v" "\<And>v. (?rm2 \<circ>\<^sub>s ?rm1) v = \<theta> v" using * by blast+
  thus ?P ?Q by auto
qed

lemma subst_comp_eq_if_disjoint_vars:
  assumes "(subst_domain \<delta> \<union> range_vars \<delta>) \<inter> (subst_domain \<gamma> \<union> range_vars \<gamma>) = {}"
  shows "\<gamma> \<circ>\<^sub>s \<delta> = \<delta> \<circ>\<^sub>s \<gamma>"
proof -
  { fix x assume "x \<in> subst_domain \<gamma>"
    hence "(\<gamma> \<circ>\<^sub>s \<delta>) x = \<gamma> x" "(\<delta> \<circ>\<^sub>s \<gamma>) x = \<gamma> x"
      using assms unfolding range_vars_alt_def by (force simp add: subst_compose)+
    hence "(\<gamma> \<circ>\<^sub>s \<delta>) x = (\<delta> \<circ>\<^sub>s \<gamma>) x" by metis
  } moreover
  { fix x assume "x \<in> subst_domain \<delta>"
    hence "(\<gamma> \<circ>\<^sub>s \<delta>) x = \<delta> x" "(\<delta> \<circ>\<^sub>s \<gamma>) x = \<delta> x"
      using assms
      unfolding range_vars_alt_def by (auto simp add: subst_compose subst_domain_def)
    hence "(\<gamma> \<circ>\<^sub>s \<delta>) x = (\<delta> \<circ>\<^sub>s \<gamma>) x" by metis
  } moreover
  { fix x assume "x \<notin> subst_domain \<gamma>" "x \<notin> subst_domain \<delta>"
    hence "(\<gamma> \<circ>\<^sub>s \<delta>) x = (\<delta> \<circ>\<^sub>s \<gamma>) x" by (simp add: subst_compose subst_domain_def)
  } ultimately show ?thesis by auto
qed

lemma subst_eq_if_disjoint_vars_ground:
  fixes \<xi> \<delta>::"('f,'v) subst"
  assumes "subst_domain \<delta> \<inter> subst_domain \<xi> = {}" "ground (subst_range \<xi>)" "ground (subst_range \<delta>)" 
  shows "t \<cdot> \<delta> \<cdot> \<xi> = t \<cdot> \<xi> \<cdot> \<delta>"
by (metis assms subst_comp_eq_if_disjoint_vars range_vars_alt_def
          subst_subst_compose sup_bot.right_neutral)

lemma subst_img_bound: "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv t \<Longrightarrow> range_vars \<delta> \<subseteq> fv (t \<cdot> \<delta>)"
proof -
  assume "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv t"
  hence "subst_domain \<delta> \<subseteq> fv t" by blast
  thus ?thesis
    by (metis (no_types) range_vars_alt_def le_iff_sup subst_apply_fv_unfold
              subst_apply_fv_union subst_range.simps)
qed

lemma subst_all_fv_subset: "fv t \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M \<Longrightarrow> fv (t \<cdot> \<theta>) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
proof -
  assume *: "fv t \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t M"
  { fix v assume "v \<in> fv t"
    hence "v \<in> fv\<^sub>s\<^sub>e\<^sub>t M" using * by auto
    then obtain t' where "t' \<in> M" "v \<in> fv t'" by auto
    hence "fv (\<theta> v) \<subseteq> fv (t' \<cdot> \<theta>)"
      by (metis subst_apply_term.simps(1) subst_apply_fv_subset subst_apply_fv_unfold
                subtermeq_vars_subset vars_iff_subtermeq) 
    hence "fv (\<theta> v) \<subseteq> fv\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)" using \<open>t' \<in> M\<close> by auto
  }
  thus ?thesis using subst_apply_fv_unfold[of t \<theta>] by auto
qed

lemma subst_support_if_mgt_subst_idem:
  assumes "\<theta> \<preceq>\<^sub>\<circ> \<delta>" "subst_idem \<theta>"
  shows "\<theta> supports \<delta>"
proof -
  from \<open>\<theta> \<preceq>\<^sub>\<circ> \<delta>\<close> obtain \<sigma> where \<sigma>: "\<delta> = \<theta> \<circ>\<^sub>s \<sigma>" by blast
  hence "\<And>v. \<theta> v \<cdot> \<delta> = Var v \<cdot> (\<theta> \<circ>\<^sub>s \<theta> \<circ>\<^sub>s \<sigma>)" by simp
  hence "\<And>v. \<theta> v \<cdot> \<delta> = Var v \<cdot> (\<theta> \<circ>\<^sub>s \<sigma>)" using \<open>subst_idem \<theta> \<close> unfolding subst_idem_def by simp
  hence "\<And>v. \<theta> v \<cdot> \<delta> = Var v \<cdot> \<delta>" using \<sigma> by simp
  thus "\<theta> supports \<delta>" by simp
qed

lemma subst_support_iff_mgt_if_subst_idem:
  assumes "subst_idem \<theta>"
  shows "\<theta> \<preceq>\<^sub>\<circ> \<delta> \<longleftrightarrow> \<theta> supports \<delta>"
proof
  show "\<theta> \<preceq>\<^sub>\<circ> \<delta> \<Longrightarrow> \<theta> supports \<delta>" by (fact subst_support_if_mgt_subst_idem[OF _ \<open>subst_idem \<theta>\<close>])
  show "\<theta> supports \<delta> \<Longrightarrow> \<theta> \<preceq>\<^sub>\<circ> \<delta>" by (fact subst_supportD)
qed

lemma subst_support_comp:
  fixes \<theta> \<delta> \<I>::"('a,'b) subst"
  assumes "\<theta> supports \<I>" "\<delta> supports \<I>"
  shows "(\<theta> \<circ>\<^sub>s \<delta>) supports \<I>"
by (metis (no_types) assms subst_agreement subst_apply_term.simps(1) subst_subst_compose)

lemma subst_support_comp':
  fixes \<theta> \<delta> \<sigma>::"('a,'b) subst"
  assumes "\<theta> supports \<delta>"
  shows "\<theta> supports (\<delta> \<circ>\<^sub>s \<sigma>)" "\<sigma> supports \<delta> \<Longrightarrow> \<theta> supports (\<sigma> \<circ>\<^sub>s \<delta>)"
using assms unfolding subst_support_def by (metis subst_compose_assoc, metis)

lemma subst_support_comp_split:
  fixes \<theta> \<delta> \<I>::"('a,'b) subst"
  assumes "(\<theta> \<circ>\<^sub>s \<delta>) supports \<I>"
  shows "subst_domain \<theta> \<inter> range_vars \<theta> = {} \<Longrightarrow> \<theta> supports \<I>"
  and "subst_domain \<theta> \<inter> subst_domain \<delta> = {} \<Longrightarrow> \<delta> supports \<I>"
proof -
  assume "subst_domain \<theta> \<inter> range_vars \<theta> = {}"
  hence "subst_idem \<theta>" by (metis subst_idemI)
  have "\<theta> \<preceq>\<^sub>\<circ> \<I>" using assms subst_compose_assoc[of \<theta> \<delta> \<I>] unfolding subst_compose_def by metis
  show "\<theta> supports \<I>" using subst_support_if_mgt_subst_idem[OF \<open>\<theta> \<preceq>\<^sub>\<circ> \<I>\<close> \<open>subst_idem \<theta>\<close>] by auto
next
  assume "subst_domain \<theta> \<inter> subst_domain \<delta> = {}"
  moreover have "\<forall>v \<in> subst_domain (\<theta> \<circ>\<^sub>s \<delta>). (\<theta> \<circ>\<^sub>s \<delta>) v \<cdot> \<I> = \<I> v" using assms by metis
  ultimately have "\<forall>v \<in> subst_domain \<delta>. \<delta> v \<cdot> \<I> = \<I> v"
    using var_not_in_subst_dom unfolding subst_compose_def
    by (metis IntI empty_iff subst_apply_term.simps(1))
  thus "\<delta> supports \<I>" by force
qed

lemma subst_idem_support: "subst_idem \<theta> \<Longrightarrow> \<theta> supports \<theta> \<circ>\<^sub>s \<delta>"
unfolding subst_idem_def by (metis subst_support_def subst_compose_assoc)

lemma subst_idem_iff_self_support: "subst_idem \<theta> \<longleftrightarrow> \<theta> supports \<theta>"
using subst_support_def[of \<theta> \<theta>] unfolding subst_idem_def by auto

lemma subterm_subst_neq: "t \<sqsubset> t' \<Longrightarrow> t \<cdot> s \<noteq> t' \<cdot> s"
by (metis subst_mono_neq)

lemma fv_Fun_subst_neq: "x \<in> fv (Fun f T) \<Longrightarrow> \<sigma> x \<noteq> Fun f T \<cdot> \<sigma>"
using subterm_subst_neq[of "Var x" "Fun f T"] vars_iff_subterm_or_eq[of x "Fun f T"] by auto

lemma subterm_subst_unfold:
  assumes "t \<sqsubseteq> s \<cdot> \<theta>"
  shows "(\<exists>s'. s' \<sqsubseteq> s \<and> t = s' \<cdot> \<theta>) \<or> (\<exists>x \<in> fv s. t \<sqsubset> \<theta> x)"
using assms
proof (induction s)
  case (Fun f T) thus ?case
  proof (cases "t = Fun f T \<cdot> \<theta>")
    case True thus ?thesis using Fun by auto
  next
    case False
    then obtain s' where s': "s' \<in> set T" "t \<sqsubseteq> s' \<cdot> \<theta>" using Fun by auto
    hence "(\<exists>s''. s'' \<sqsubseteq> s' \<and> t = s'' \<cdot> \<theta>) \<or> (\<exists>x \<in> fv s'. t \<sqsubset> \<theta> x)" by (metis Fun.IH)
    thus ?thesis using s'(1) by auto
  qed
qed simp

lemma subterm_subst_img_subterm:
  assumes "t \<sqsubseteq> s \<cdot> \<theta>" "\<And>s'. s' \<sqsubseteq> s \<Longrightarrow> t \<noteq> s' \<cdot> \<theta>"
  shows "\<exists>w \<in> fv s. t \<sqsubset> \<theta> w"
using subterm_subst_unfold[OF assms(1)] assms(2) by force

lemma subterm_subst_not_img_subterm:
  assumes "t \<sqsubseteq> s \<cdot> \<I>" "\<not>(\<exists>w \<in> fv s. t \<sqsubseteq> \<I> w)"
  shows "\<exists>f T. Fun f T \<sqsubseteq> s \<and> t = Fun f T \<cdot> \<I>"
proof (rule ccontr)
  assume "\<not>(\<exists>f T. Fun f T \<sqsubseteq> s \<and> t = Fun f T \<cdot> \<I>)"
  hence "\<And>f T. Fun f T \<sqsubseteq> s \<Longrightarrow> t \<noteq> Fun f T \<cdot> \<I>" by simp
  moreover have "\<And>x. Var x \<sqsubseteq> s \<Longrightarrow> t \<noteq> Var x \<cdot> \<I>"
    using assms(2) vars_iff_subtermeq by force
  ultimately have "\<And>s'. s' \<sqsubseteq> s \<Longrightarrow> t \<noteq> s' \<cdot> \<I>" by (metis "term.exhaust")
  thus False using assms subterm_subst_img_subterm by blast
qed

lemma subst_apply_img_var:
  assumes "v \<in> fv (t \<cdot> \<delta>)" "v \<notin> fv t"
  obtains w where "w \<in> fv t" "v \<in> fv (\<delta> w)"
using assms by (induct t) auto

lemma subst_apply_img_var':
  assumes "x \<in> fv (t \<cdot> \<delta>)" "x \<notin> fv t"
  shows "\<exists>y \<in> fv t. x \<in> fv (\<delta> y)"
by (metis assms subst_apply_img_var)

lemma nth_map_subst:
  fixes \<theta>::"('f,'v) subst" and T::"('f,'v) term list" and i::nat
  shows "i < length T \<Longrightarrow> (map (\<lambda>t. t \<cdot> \<theta>) T) ! i = (T ! i) \<cdot> \<theta>"
by (fact nth_map)

lemma subst_subterm:
  assumes "Fun f T \<sqsubseteq> t \<cdot> \<theta>"
  shows "(\<exists>S. Fun f S \<sqsubseteq> t \<and> Fun f S \<cdot> \<theta> = Fun f T) \<or>
         (\<exists>s \<in> subst_range \<theta>. Fun f T \<sqsubseteq> s)"
using assms subterm_subst_not_img_subterm by (cases "\<exists>s \<in> subst_range \<theta>. Fun f T \<sqsubseteq> s") fastforce+

lemma subst_subterm':
  assumes "Fun f T \<sqsubseteq> t \<cdot> \<theta>"
  shows "\<exists>S. length S = length T \<and> (Fun f S \<sqsubseteq> t \<or> (\<exists>s \<in> subst_range \<theta>. Fun f S \<sqsubseteq> s))"
using subst_subterm[OF assms] by auto

lemma subst_subterm'':
  assumes "s \<in> subterms (t \<cdot> \<theta>)"
  shows "(\<exists>u \<in> subterms t. s = u \<cdot> \<theta>) \<or> s \<in> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>)"
proof (cases s)
  case (Var x)
  thus ?thesis
    using assms subterm_subst_not_img_subterm vars_iff_subtermeq
    by (cases "s = t \<cdot> \<theta>") fastforce+
next
  case (Fun f T)
  thus ?thesis
    using subst_subterm[of f T t \<theta>] assms
    by fastforce
qed


subsection \<open>More Small Lemmata\<close>
lemma funs_term_subst: "funs_term (t \<cdot> \<theta>) = funs_term t \<union> (\<Union>x \<in> fv t. funs_term (\<theta> x))"
by (induct t) auto

lemma fv\<^sub>s\<^sub>e\<^sub>t_subst_img_eq:
  assumes "X \<inter> (subst_domain \<delta> \<union> range_vars \<delta>) = {}"
  shows "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` (Y - X)) = fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` Y) - X"
using assms unfolding range_vars_alt_def by force

lemma subst_Fun_index_eq:
  assumes "i < length T" "Fun f T \<cdot> \<delta> = Fun g T' \<cdot> \<delta>"
  shows "T ! i \<cdot> \<delta> = T' ! i \<cdot> \<delta>"
proof -
  have "map (\<lambda>x. x \<cdot> \<delta>) T = map (\<lambda>x. x \<cdot> \<delta>) T'" using assms by simp
  thus ?thesis by (metis assms(1) length_map nth_map)
qed

lemma fv_exists_if_unifiable_and_neq:
  fixes t t'::"('a,'b) term" and \<delta> \<theta>::"('a,'b) subst"
  assumes "t \<noteq> t'" "t \<cdot> \<theta> = t' \<cdot> \<theta>"
  shows "fv t \<union> fv t' \<noteq> {}"
proof
  assume "fv t \<union> fv t' = {}"
  hence "fv t = {}" "fv t' = {}" by auto
  hence "t \<cdot> \<theta> = t" "t' \<cdot> \<theta> = t'" by auto
  hence "t = t'" using assms(2) by metis
  thus False using assms(1) by auto
qed

lemma const_subterm_subst: "Fun c [] \<sqsubseteq> t \<Longrightarrow> Fun c [] \<sqsubseteq> t \<cdot> \<sigma>"
by (induct t) auto

lemma const_subterm_subst_var_obtain:
  assumes "Fun c [] \<sqsubseteq> t \<cdot> \<sigma>" "\<not>Fun c [] \<sqsubseteq> t"
  obtains x where "x \<in> fv t" "Fun c [] \<sqsubseteq> \<sigma> x"
using assms by (induct t) auto

lemma const_subterm_subst_cases:
  assumes "Fun c [] \<sqsubseteq> t \<cdot> \<sigma>"
  shows "Fun c [] \<sqsubseteq> t \<or> (\<exists>x \<in> fv t. x \<in> subst_domain \<sigma> \<and> Fun c [] \<sqsubseteq> \<sigma> x)"
proof (cases "Fun c [] \<sqsubseteq> t")
  case False
  then obtain x where "x \<in> fv t" "Fun c [] \<sqsubseteq> \<sigma> x"
    using const_subterm_subst_var_obtain[OF assms] by moura
  thus ?thesis by (cases "x \<in> subst_domain \<sigma>") auto
qed simp

lemma fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst_fv_subset:
  assumes "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"
  shows "fv (\<theta> x) \<subseteq> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>)"
  using assms
proof (induction F)
  case (Cons f F)
  then obtain t t' where f: "f = (t,t')" by (metis surj_pair)
  show ?case
  proof (cases "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F")
    case True thus ?thesis
      using Cons.IH
      unfolding subst_apply_pairs_def
      by auto
  next
    case False
    hence "x \<in> fv t \<union> fv t'" using Cons.prems f by simp
    hence "fv (\<theta> x) \<subseteq> fv (t \<cdot> \<theta>) \<union> fv (t' \<cdot> \<theta>)" using fv_subst_subset[of x] by force
    thus ?thesis using f unfolding subst_apply_pairs_def by auto
  qed
qed simp

lemma fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_step_subst: "fv\<^sub>s\<^sub>e\<^sub>t (\<delta> ` fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) = fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
proof (induction F)
  case (Cons f F)
  obtain t t' where "f = (t,t')" by moura
  thus ?case
    using Cons
    by (simp add: subst_apply_pairs_def subst_apply_fv_unfold)
qed (simp_all add: subst_apply_pairs_def)

lemma fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst_obtain_var:
  fixes \<delta>::"('a,'b) subst"
  assumes "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)"
  shows "\<exists>y \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F. x \<in> fv (\<delta> y)"
  using assms 
proof (induction F)
  case (Cons f F)
  then obtain t s where f: "f = (t,s)" by (metis surj_pair)

  from Cons.IH show ?case
  proof (cases "x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>)")
    case False
    hence "x \<in> fv (t \<cdot> \<delta>) \<or> x \<in> fv (s \<cdot> \<delta>)"
      using f Cons.prems
      by (simp add: subst_apply_pairs_def)
    hence "(\<exists>y \<in> fv t. x \<in> fv (\<delta> y)) \<or> (\<exists>y \<in> fv s. x \<in> fv (\<delta> y))" by (metis fv_subst_obtain_var)
    thus ?thesis using f by (auto simp add: subst_apply_pairs_def)
  qed (auto simp add: Cons.IH)
qed (simp add: subst_apply_pairs_def)

lemma pair_subst_ident[intro]: "(fv t \<union> fv t') \<inter> subst_domain \<theta> = {} \<Longrightarrow> (t,t') \<cdot>\<^sub>p \<theta> = (t,t')"
by auto

lemma pairs_substI[intro]:
  assumes "subst_domain \<theta> \<inter> (\<Union>(s,t) \<in> M. fv s \<union> fv t) = {}"
  shows "M \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta> = M"
proof -
  { fix m assume M: "m \<in> M"
    then obtain s t where m: "m = (s,t)" by (metis surj_pair)
    hence "(fv s \<union> fv t) \<inter> subst_domain \<theta> = {}" using assms M by auto
    hence "m \<cdot>\<^sub>p \<theta> = m" using m by auto
  } thus ?thesis by (simp add: image_cong) 
qed

lemma fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>) = fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` (fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F))"
proof (induction F)
  case (Cons g G)
  obtain t t' where "g = (t,t')" by (metis surj_pair)
  thus ?case
    using Cons.IH
    by (simp add: subst_apply_pairs_def subst_apply_fv_unfold)
qed (simp add: subst_apply_pairs_def)

lemma fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst_subset:
  assumes "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) \<subseteq> subst_domain \<sigma>"
  shows  "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F \<subseteq> subst_domain \<sigma> \<union> subst_domain \<delta>"
  using assms
proof (induction F)
  case (Cons g G)
  hence IH: "fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s G \<subseteq> subst_domain \<sigma> \<union> subst_domain \<delta>"
    by (simp add: subst_apply_pairs_def)
  obtain t t' where g: "g = (t,t')" by (metis surj_pair)
  hence "fv (t \<cdot> \<delta>) \<subseteq> subst_domain \<sigma>" "fv (t' \<cdot> \<delta>) \<subseteq> subst_domain \<sigma>"
    using Cons.prems by (simp_all add: subst_apply_pairs_def)
  hence "fv t \<subseteq> subst_domain \<sigma> \<union> subst_domain \<delta>" "fv t' \<subseteq> subst_domain \<sigma> \<union> subst_domain \<delta>"
    using subst_apply_fv_unfold[of _ \<delta>] by force+
  thus ?case using IH g by (simp add: subst_apply_pairs_def)
qed (simp add: subst_apply_pairs_def)

lemma pairs_subst_comp: "F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta> \<circ>\<^sub>s \<theta> = ((F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta>) \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>)"
by (induct F) (auto simp add: subst_apply_pairs_def)

lemma pairs_substI'[intro]:
  "subst_domain \<theta> \<inter> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F = {} \<Longrightarrow> F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta> = F"
by (induct F) (force simp add: subst_apply_pairs_def)+

lemma subst_pair_compose[simp]: "d \<cdot>\<^sub>p (\<delta> \<circ>\<^sub>s \<I>) = d \<cdot>\<^sub>p \<delta> \<cdot>\<^sub>p \<I>"
proof -
  obtain t s where "d = (t,s)" by moura
  thus ?thesis by auto
qed

lemma subst_pairs_compose[simp]: "D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t (\<delta> \<circ>\<^sub>s \<I>) = D \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<delta> \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<I>"
by auto

lemma subst_apply_pair_pair: "(t, s) \<cdot>\<^sub>p \<I> = (t \<cdot> \<I>, s \<cdot> \<I>)"
by (rule prod.case)

lemma subst_apply_pairs_nil[simp]: "[] \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta> = []"
unfolding subst_apply_pairs_def by simp

lemma subst_apply_pairs_singleton[simp]: "[(t,s)] \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<delta> = [(t \<cdot> \<delta>,s \<cdot> \<delta>)]"
unfolding subst_apply_pairs_def by simp

lemma subst_apply_pairs_Var[iff]: "F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s Var = F" by (simp add: subst_apply_pairs_def)

lemma subst_apply_pairs_pset_subst: "set (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s \<theta>) = set F \<cdot>\<^sub>p\<^sub>s\<^sub>e\<^sub>t \<theta>"
unfolding subst_apply_pairs_def by force


subsection \<open>Finite Substitutions\<close>
inductive_set fsubst::"('a,'b) subst set" where
  fvar:     "Var \<in> fsubst"
| FUpdate:  "\<lbrakk>\<theta> \<in> fsubst; v \<notin> subst_domain \<theta>; t \<noteq> Var v\<rbrakk> \<Longrightarrow> \<theta>(v := t) \<in> fsubst"

lemma finite_dom_iff_fsubst:
  "finite (subst_domain \<theta>) \<longleftrightarrow> \<theta> \<in> fsubst"
proof
  assume "finite (subst_domain \<theta>)" thus "\<theta> \<in> fsubst"
  proof (induction "subst_domain \<theta>" arbitrary: \<theta> rule: finite.induct)
    case emptyI
    hence "\<theta> = Var" using empty_dom_iff_empty_subst by metis
    thus ?case using fvar by simp
  next
    case (insertI \<theta>'\<^sub>d\<^sub>o\<^sub>m v) thus ?case
    proof (cases "v \<in> \<theta>'\<^sub>d\<^sub>o\<^sub>m")
      case True
      hence "\<theta>'\<^sub>d\<^sub>o\<^sub>m = subst_domain \<theta>" using \<open>insert v \<theta>'\<^sub>d\<^sub>o\<^sub>m = subst_domain \<theta>\<close> by auto
      thus ?thesis using insertI.hyps(2) by metis
    next
      case False
      let ?\<theta>' = "\<lambda>w. if w \<in> \<theta>'\<^sub>d\<^sub>o\<^sub>m then \<theta> w else Var w"
      have "subst_domain ?\<theta>' = \<theta>'\<^sub>d\<^sub>o\<^sub>m"
        using \<open>v \<notin> \<theta>'\<^sub>d\<^sub>o\<^sub>m\<close> \<open>insert v \<theta>'\<^sub>d\<^sub>o\<^sub>m = subst_domain \<theta>\<close>
        by (auto simp add: subst_domain_def)
      hence "?\<theta>' \<in> fsubst" using insertI.hyps(2) by simp
      moreover have "?\<theta>'(v := \<theta> v) = (\<lambda>w. if w \<in> insert v \<theta>'\<^sub>d\<^sub>o\<^sub>m then \<theta> w else Var w)" by auto
      hence "?\<theta>'(v := \<theta> v) = \<theta>"
        using \<open>insert v \<theta>'\<^sub>d\<^sub>o\<^sub>m = subst_domain \<theta>\<close>
        by (auto simp add: subst_domain_def)
      ultimately show ?thesis
        using FUpdate[of ?\<theta>' v "\<theta> v"] False insertI.hyps(3)
        by (auto simp add: subst_domain_def)
    qed
  qed
next
  assume "\<theta> \<in> fsubst" thus "finite (subst_domain \<theta>)"
  by (induct \<theta>, simp, metis subst_dom_insert_finite)
qed

lemma fsubst_induct[case_names fvar FUpdate, induct set: finite]:
  assumes "finite (subst_domain \<delta>)" "P Var"
  and "\<And>\<theta> v t. \<lbrakk>finite (subst_domain \<theta>); v \<notin> subst_domain \<theta>; t \<noteq> Var v; P \<theta>\<rbrakk> \<Longrightarrow> P (\<theta>(v := t))"
  shows "P \<delta>"
using assms finite_dom_iff_fsubst fsubst.induct by metis

lemma fun_upd_fsubst: "s(v := t) \<in> fsubst \<longleftrightarrow> s \<in> fsubst"
using subst_dom_insert_finite[of s] finite_dom_iff_fsubst by blast 

lemma finite_img_if_fsubst: "s \<in> fsubst \<Longrightarrow> finite (subst_range s)"
using finite_dom_iff_fsubst finite_subst_img_if_finite_dom' by blast


subsection \<open>Unifiers and Most General Unifiers (MGUs)\<close>

abbreviation Unifier::"('f,'v) subst \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool" where
  "Unifier \<sigma> t u \<equiv> (t \<cdot> \<sigma> = u \<cdot> \<sigma>)"

abbreviation MGU::"('f,'v) subst \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool" where
  "MGU \<sigma> t u \<equiv> Unifier \<sigma> t u \<and> (\<forall>\<theta>. Unifier \<theta> t u \<longrightarrow> \<sigma> \<preceq>\<^sub>\<circ> \<theta>)"

lemma MGUI[intro]:
  shows "\<lbrakk>t \<cdot> \<sigma> = u \<cdot> \<sigma>; \<And>\<theta>::('f,'v) subst. t \<cdot> \<theta> = u \<cdot> \<theta> \<Longrightarrow> \<sigma> \<preceq>\<^sub>\<circ> \<theta>\<rbrakk> \<Longrightarrow> MGU \<sigma> t u"
by auto

lemma UnifierD[dest]:
  fixes \<sigma>::"('f,'v) subst" and f g::'f and X Y::"('f,'v) term list"
  assumes "Unifier \<sigma> (Fun f X) (Fun g Y)"
  shows "f = g" "length X = length Y"
proof -
  from assms show "f = g" by auto

  from assms have "Fun f X \<cdot> \<sigma> = Fun g Y \<cdot> \<sigma>" by auto
  hence "length (map (\<lambda>x. x \<cdot> \<sigma>) X) = length (map (\<lambda>x. x \<cdot> \<sigma>) Y)" by auto
  thus "length X = length Y" by auto
qed

lemma MGUD[dest]:
  fixes \<sigma>::"('f,'v) subst" and f g::'f and X Y::"('f,'v) term list"
  assumes "MGU \<sigma> (Fun f X) (Fun g Y)"
  shows "f = g" "length X = length Y"
using assms by (auto intro!: UnifierD[of f X \<sigma> g Y])

lemma MGU_sym[sym]: "MGU \<sigma> s t \<Longrightarrow> MGU \<sigma> t s" by auto
lemma Unifier_sym[sym]: "Unifier \<sigma> s t \<Longrightarrow> Unifier \<sigma> t s" by auto

lemma MGU_nil: "MGU Var s t \<longleftrightarrow> s = t" by fastforce

lemma Unifier_comp: "Unifier (\<theta> \<circ>\<^sub>s \<delta>) t u \<Longrightarrow> Unifier \<delta> (t \<cdot> \<theta>) (u \<cdot> \<theta>)"
by simp

lemma Unifier_comp': "Unifier \<delta> (t \<cdot> \<theta>) (u \<cdot> \<theta>) \<Longrightarrow> Unifier (\<theta> \<circ>\<^sub>s \<delta>) t u"
by simp

lemma Unifier_excludes_subterm:
  assumes \<theta>: "Unifier \<theta> t u"
  shows "\<not>t \<sqsubset> u"
proof
  assume "t \<sqsubset> u"
  hence "t \<cdot> \<theta> \<sqsubset> u \<cdot> \<theta>" using subst_mono_neq by metis
  hence "t \<cdot> \<theta> \<noteq> u \<cdot> \<theta>" by simp
  moreover from \<theta> have "t \<cdot> \<theta> = u \<cdot> \<theta>" by auto
  ultimately show False ..
qed

lemma MGU_is_Unifier: "MGU \<sigma> t u \<Longrightarrow> Unifier \<sigma> t u" by (rule conjunct1)

lemma MGU_Var1:
  assumes "\<not>Var v \<sqsubset> t"
  shows "MGU (Var(v := t)) (Var v) t"
proof (intro MGUI exI)
  show "Var v \<cdot> (Var(v := t)) = t \<cdot> (Var(v := t))" using assms subst_no_occs by fastforce
next
  fix \<theta>::"('a,'b) subst" assume th: "Var v \<cdot> \<theta> = t \<cdot> \<theta>" 
  show "\<theta> = (Var(v := t)) \<circ>\<^sub>s \<theta>" 
  proof
    fix s show "s \<cdot> \<theta> = s \<cdot> ((Var(v := t)) \<circ>\<^sub>s \<theta>)" using th by (induct s) auto
  qed
qed

lemma MGU_Var2: "v \<notin> fv t \<Longrightarrow> MGU (Var(v := t)) (Var v) t"
by (metis (no_types) MGU_Var1 vars_iff_subterm_or_eq)

lemma MGU_Var3: "MGU Var (Var v) (Var w) \<longleftrightarrow> v = w" by fastforce

lemma MGU_Const1: "MGU Var (Fun c []) (Fun d []) \<longleftrightarrow> c = d" by fastforce

lemma MGU_Const2: "MGU \<theta> (Fun c []) (Fun d []) \<Longrightarrow> c = d" by auto

lemma MGU_Fun:
  assumes "MGU \<theta> (Fun f X) (Fun g Y)"
  shows "f = g" "length X = length Y"
proof -
  let ?F = "\<lambda>\<theta> X. map (\<lambda>x. x \<cdot> \<theta>) X"
  from assms have
    "\<lbrakk>f = g; ?F \<theta> X = ?F \<theta> Y; \<forall>\<theta>'. f = g \<and> ?F \<theta>' X = ?F \<theta>' Y \<longrightarrow> \<theta> \<preceq>\<^sub>\<circ> \<theta>'\<rbrakk> \<Longrightarrow> length X = length Y"
    using map_eq_imp_length_eq by auto
  thus "f = g" "length X = length Y" using assms by auto
qed

lemma Unifier_Fun:
  assumes "Unifier \<theta> (Fun f (x#X)) (Fun g (y#Y))"
  shows "Unifier \<theta> x y" "Unifier \<theta> (Fun f X) (Fun g Y)"
using assms by simp_all

lemma Unifier_subst_idem_subst: 
  "subst_idem r \<Longrightarrow> Unifier s (t \<cdot> r) (u \<cdot> r) \<Longrightarrow> Unifier (r \<circ>\<^sub>s s) (t \<cdot> r) (u \<cdot> r)"
by (metis (no_types, lifting) subst_idem_def subst_subst_compose)

lemma subst_idem_comp:
  "subst_idem r \<Longrightarrow> Unifier s (t \<cdot> r) (u \<cdot> r) \<Longrightarrow> 
    (\<And>q. Unifier q (t \<cdot> r) (u \<cdot> r) \<Longrightarrow> s \<circ>\<^sub>s q = q) \<Longrightarrow>
    subst_idem (r \<circ>\<^sub>s s)"
by (frule Unifier_subst_idem_subst, blast, metis subst_idem_def subst_compose_assoc)

lemma Unifier_mgt: "\<lbrakk>Unifier \<delta> t u; \<delta> \<preceq>\<^sub>\<circ> \<theta>\<rbrakk> \<Longrightarrow> Unifier \<theta> t u" by auto

lemma Unifier_support: "\<lbrakk>Unifier \<delta> t u; \<delta> supports \<theta>\<rbrakk> \<Longrightarrow> Unifier \<theta> t u"
using subst_supportD Unifier_mgt by metis

lemma MGU_mgt: "\<lbrakk>MGU \<sigma> t u; MGU \<delta> t u\<rbrakk> \<Longrightarrow> \<sigma> \<preceq>\<^sub>\<circ> \<delta>" by auto

lemma Unifier_trm_fv_bound:
  "\<lbrakk>Unifier s t u; v \<in> fv t\<rbrakk> \<Longrightarrow> v \<in> subst_domain s \<union> range_vars s \<union> fv u"
proof (induction t arbitrary: s u)
  case (Fun f X)
  hence "v \<in> fv (u \<cdot> s) \<or> v \<in> subst_domain s" by (metis subst_not_dom_fixed)
  thus ?case by (metis (no_types) Un_iff contra_subsetD subst_sends_fv_to_img)
qed (metis (no_types) UnI1 UnI2 subsetCE no_var_subterm subst_sends_dom_to_img
            subst_to_var_is_var trm_subst_ident' vars_iff_subterm_or_eq)

lemma Unifier_rm_var: "\<lbrakk>Unifier \<theta> s t; v \<notin> fv s \<union> fv t\<rbrakk> \<Longrightarrow> Unifier (rm_var v \<theta>) s t"
by (auto simp add: repl_invariance)

lemma Unifier_ground_rm_vars:
  assumes "ground (subst_range s)" "Unifier (rm_vars X s) t t'"
  shows "Unifier s t t'"
by (rule Unifier_support[OF assms(2) rm_vars_ground_supports[OF assms(1)]])

lemma Unifier_dom_restrict:
  assumes "Unifier s t t'" "fv t \<union> fv t' \<subseteq> S"
  shows "Unifier (rm_vars (UNIV - S) s) t t'"
proof -
  let ?s = "rm_vars (UNIV - S) s"
  show ?thesis using term_subst_eq_conv[of t s ?s] term_subst_eq_conv[of t' s ?s] assms by auto
qed


subsection \<open>Well-formedness of Substitutions and Unifiers\<close>
inductive_set wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set::"('a,'b) subst set" where
  Empty[simp]: "Var \<in> wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set"
| Insert[simp]:
    "\<lbrakk>\<theta> \<in> wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set; v \<notin> subst_domain \<theta>;
      v \<notin> range_vars \<theta>; fv t \<inter> (insert v (subst_domain \<theta>)) = {}\<rbrakk>
      \<Longrightarrow> \<theta>(v := t) \<in> wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set"

definition wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t::"('a,'b) subst \<Rightarrow> bool" where
  "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<equiv> subst_domain \<theta> \<inter> range_vars \<theta> = {} \<and> finite (subst_domain \<theta>)"

definition wf\<^sub>M\<^sub>G\<^sub>U::"('a,'b) subst \<Rightarrow> ('a,'b) term \<Rightarrow> ('a,'b) term \<Rightarrow> bool" where
  "wf\<^sub>M\<^sub>G\<^sub>U \<theta> s t \<equiv> wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<and> MGU \<theta> s t \<and> subst_domain \<theta> \<union> range_vars \<theta> \<subseteq> fv s \<union> fv t"

lemma wf_subst_subst_idem: "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<Longrightarrow> subst_idem \<theta>" using subst_idemI[of \<theta>] unfolding wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by fast

lemma wf_subst_properties: "\<theta> \<in> wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set = wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>"
proof
  show "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<Longrightarrow> \<theta> \<in> wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set" unfolding wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def
  proof -
    assume "subst_domain \<theta> \<inter> range_vars \<theta> = {} \<and> finite (subst_domain \<theta>)"
    hence "finite (subst_domain \<theta>)" "subst_domain \<theta> \<inter> range_vars \<theta> = {}"
      by auto
    thus "\<theta> \<in> wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set"
    proof (induction \<theta> rule: fsubst_induct)
      case fvar thus ?case by simp
    next
      case (FUpdate \<delta> v t)
      have "subst_domain \<delta> \<subseteq> subst_domain (\<delta>(v := t))" "range_vars \<delta> \<subseteq> range_vars (\<delta>(v := t))"
        using FUpdate.hyps(2,3) subst_img_update
        unfolding range_vars_alt_def by (fastforce simp add: subst_domain_def)+
      hence "subst_domain \<delta> \<inter> range_vars \<delta> = {}" using FUpdate.prems(1) by blast
      hence "\<delta> \<in> wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set" using FUpdate.IH by metis

      have *: "range_vars (\<delta>(v := t)) = range_vars \<delta> \<union> fv t"
        using FUpdate.hyps(2) subst_img_update[OF _ FUpdate.hyps(3)]
        by fastforce
      hence "fv t \<inter> insert v (subst_domain \<delta>) = {}"
        using FUpdate.prems subst_dom_update2[OF FUpdate.hyps(3)] by blast
      moreover have "subst_domain (\<delta>(v := t)) = insert v (subst_domain \<delta>)"
        by (meson FUpdate.hyps(3) subst_dom_update2)
      hence "v \<notin> range_vars \<delta>" using FUpdate.prems * by blast
      ultimately show ?case using Insert[OF \<open>\<delta> \<in> wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set\<close> \<open>v \<notin> subst_domain \<delta>\<close>] by metis
    qed
  qed

  show "\<theta> \<in> wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set \<Longrightarrow> wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" unfolding wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def
  proof (induction \<theta> rule: wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set.induct)
    case Empty thus ?case by simp
  next
    case (Insert \<sigma> v t)
    hence 1: "subst_domain \<sigma> \<inter> range_vars \<sigma> = {}" by simp
    hence 2: "subst_domain (\<sigma>(v := t)) \<inter> range_vars \<sigma> = {}"
      using Insert.hyps(3) by (auto simp add: subst_domain_def)
    have 3: "fv t \<inter> subst_domain (\<sigma>(v := t)) = {}"
      using Insert.hyps(4) by (auto simp add: subst_domain_def)
    have 4: "\<sigma> v = Var v" using \<open>v \<notin> subst_domain \<sigma>\<close> by (simp add: subst_domain_def)
  
    from Insert.IH have "finite (subst_domain \<sigma>)" by simp
    hence 5: "finite (subst_domain (\<sigma>(v := t)))" using subst_dom_insert_finite[of \<sigma>] by simp
  
    have "subst_domain (\<sigma>(v := t)) \<inter> range_vars (\<sigma>(v := t)) = {}"
    proof (cases "t = Var v")
      case True
      hence "range_vars (\<sigma>(v := t)) = range_vars \<sigma>"
        using 4 fun_upd_triv term.inject(1)
        unfolding range_vars_alt_def by (auto simp add: subst_domain_def) 
      thus "subst_domain (\<sigma>(v := t)) \<inter> range_vars (\<sigma>(v := t)) = {}"
        using 1 2 3 by auto
    next
      case False
      hence "range_vars (\<sigma>(v := t)) = fv t \<union> (range_vars \<sigma>)"
        using 4 subst_img_update[of \<sigma> v] by auto
      thus "subst_domain (\<sigma>(v := t)) \<inter> range_vars (\<sigma>(v := t)) = {}" using 1 2 3 by blast
    qed
    thus ?case using 5 by blast 
  qed
qed

lemma wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_induct[consumes 1, case_names Empty Insert]:
  assumes "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "P Var"
  and "\<And>\<theta> v t. \<lbrakk>wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>; P \<theta>; v \<notin> subst_domain \<theta>; v \<notin> range_vars \<theta>;
                fv t \<inter> insert v (subst_domain \<theta>) = {}\<rbrakk>
                \<Longrightarrow> P (\<theta>(v := t))"
  shows "P \<delta>"
proof -
  from assms(1,3) wf_subst_properties have
    "\<delta> \<in> wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set"
    "\<And>\<theta> v t. \<lbrakk>\<theta> \<in> wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set; P \<theta>; v \<notin> subst_domain \<theta>; v \<notin> range_vars \<theta>;
              fv t \<inter> insert v (subst_domain \<theta>) = {}\<rbrakk>
              \<Longrightarrow> P (\<theta>(v := t))"
    by blast+
  thus "P \<delta>" using wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set.induct assms(2) by blast
qed  

lemma wf_subst_fsubst: "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<Longrightarrow> \<delta> \<in> fsubst"
unfolding wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def using finite_dom_iff_fsubst by blast 

lemma wf_subst_nil: "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t Var" unfolding wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by simp

lemma wf_MGU_nil: "MGU Var s t \<Longrightarrow> wf\<^sub>M\<^sub>G\<^sub>U Var s t"
using wf_subst_nil subst_domain_Var range_vars_Var
unfolding wf\<^sub>M\<^sub>G\<^sub>U_def by fast

lemma wf_MGU_dom_bound: "wf\<^sub>M\<^sub>G\<^sub>U \<theta> s t \<Longrightarrow> subst_domain \<theta> \<subseteq> fv s \<union> fv t" unfolding wf\<^sub>M\<^sub>G\<^sub>U_def by blast

lemma wf_subst_single:
  assumes "v \<notin> fv t" "\<sigma> v = t" "\<And>w. v \<noteq> w \<Longrightarrow> \<sigma> w = Var w"
  shows "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>"
proof -
  have *: "subst_domain \<sigma> = {v}" by (metis subst_fv_dom_img_single(1)[OF assms])

  have "subst_domain \<sigma> \<inter> range_vars \<sigma> = {}"
    using * assms subst_fv_dom_img_single(2)
    by (metis inf_bot_left insert_disjoint(1))
  moreover have "finite (subst_domain \<sigma>)" using * by simp
  ultimately show ?thesis by (metis wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
qed

lemma wf_subst_reduction:
  "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t s \<Longrightarrow> wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (rm_var v s)"
proof -
  assume "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t s"
  moreover have "subst_domain (rm_var v s) \<subseteq> subst_domain s" by (auto simp add: subst_domain_def)
  moreover have "range_vars (rm_var v s) \<subseteq> range_vars s"
    unfolding range_vars_alt_def by (auto simp add: subst_domain_def)
  ultimately have "subst_domain (rm_var v s) \<inter> range_vars (rm_var v s) = {}"
    by (meson compl_le_compl_iff disjoint_eq_subset_Compl subset_trans wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
  moreover have "finite (subst_domain (rm_var v s))"
    using \<open>subst_domain (rm_var v s) \<subseteq> subst_domain s\<close> \<open>wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t s\<close> rev_finite_subset
    unfolding wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by blast
  ultimately show "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (rm_var v s)" by (metis wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
qed

lemma wf_subst_compose:
  assumes "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>1" "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>2"
    and "subst_domain \<theta>1 \<inter> subst_domain \<theta>2 = {}"
    and "subst_domain \<theta>1 \<inter> range_vars \<theta>2 = {}"
  shows "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<theta>1 \<circ>\<^sub>s \<theta>2)"
using assms
proof (induction \<theta>1 rule: wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_induct)
  case Empty thus ?case unfolding wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by simp
next
  case (Insert \<sigma>1 v t)
  have "t \<noteq> Var v" using Insert.hyps(4) by auto
  hence dom1v_unfold: "subst_domain (\<sigma>1(v := t)) = insert v (subst_domain \<sigma>1)"
    using subst_dom_update2 by metis
  hence doms_disj: "subst_domain \<sigma>1 \<inter> subst_domain \<theta>2 = {}" 
    using Insert.prems(2) disjoint_insert(1) by blast
  moreover have dom_img_disj: "subst_domain \<sigma>1 \<inter> range_vars \<theta>2 = {}"
    using Insert.hyps(2) Insert.prems(3)
    by (fastforce simp add: subst_domain_def)
  ultimately have "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<sigma>1 \<circ>\<^sub>s \<theta>2)" using Insert.IH[OF \<open>wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>2\<close>] by metis

  have dom_comp_is_union: "subst_domain (\<sigma>1 \<circ>\<^sub>s \<theta>2) = subst_domain \<sigma>1 \<union> subst_domain \<theta>2"
    using subst_dom_comp_eq[OF dom_img_disj] .

  have "v \<notin> subst_domain \<theta>2"
    using Insert.prems(2) \<open>t \<noteq> Var v\<close>
    by (fastforce simp add: subst_domain_def)
  hence "\<theta>2 v = Var v" "\<sigma>1 v = Var v" using Insert.hyps(2) by (simp_all add: subst_domain_def)
  hence "(\<sigma>1 \<circ>\<^sub>s \<theta>2) v = Var v" "(\<sigma>1(v := t) \<circ>\<^sub>s \<theta>2) v = t \<cdot> \<theta>2" "((\<sigma>1 \<circ>\<^sub>s \<theta>2)(v := t)) v = t"
    unfolding subst_compose_def by simp_all
  
  have fv_t2_bound: "fv (t \<cdot> \<theta>2) \<subseteq> fv t \<union> range_vars \<theta>2" by (meson subst_sends_fv_to_img)

  have 1: "v \<notin> subst_domain (\<sigma>1 \<circ>\<^sub>s \<theta>2)"
    using \<open>(\<sigma>1 \<circ>\<^sub>s \<theta>2) v = Var v\<close>
    by (auto simp add: subst_domain_def)

  have "insert v (subst_domain \<sigma>1) \<inter> range_vars \<theta>2 = {}"
    using Insert.prems(3) dom1v_unfold by blast
  hence "v \<notin> range_vars \<sigma>1 \<union> range_vars \<theta>2" using Insert.hyps(3) by blast
  hence 2: "v \<notin> range_vars (\<sigma>1 \<circ>\<^sub>s \<theta>2)" by (meson set_rev_mp subst_img_comp_subset)

  have "subst_domain \<theta>2 \<inter> range_vars \<theta>2 = {}"
    using \<open>wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>2\<close> unfolding wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by simp
  hence "fv (t \<cdot> \<theta>2) \<inter> subst_domain \<theta>2 = {}"
    using subst_dom_elim unfolding range_vars_alt_def by simp
  moreover have "v \<notin> range_vars \<theta>2" using Insert.prems(3) dom1v_unfold by blast
  hence "v \<notin> fv t \<union> range_vars \<theta>2" using Insert.hyps(4) by blast
  hence "v \<notin> fv (t \<cdot> \<theta>2)" using \<open>fv (t \<cdot> \<theta>2) \<subseteq> fv t \<union> range_vars \<theta>2\<close> by blast
  moreover have "fv (t \<cdot> \<theta>2) \<inter> subst_domain \<sigma>1 = {}"
    using dom_img_disj fv_t2_bound \<open>fv t \<inter> insert v (subst_domain \<sigma>1) = {}\<close> by blast
  ultimately have 3: "fv (t \<cdot> \<theta>2) \<inter> insert v (subst_domain (\<sigma>1 \<circ>\<^sub>s \<theta>2)) = {}"
    using dom_comp_is_union by blast

  have "\<sigma>1(v := t) \<circ>\<^sub>s \<theta>2 = (\<sigma>1 \<circ>\<^sub>s \<theta>2)(v := t \<cdot> \<theta>2)" using subst_comp_upd1[of \<sigma>1 v t \<theta>2] .
  moreover have "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t ((\<sigma>1 \<circ>\<^sub>s \<theta>2)(v := t \<cdot> \<theta>2))"
    using "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set.Insert"[OF _ 1 2 3] \<open>wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<sigma>1 \<circ>\<^sub>s \<theta>2)\<close> wf_subst_properties by metis
  ultimately show ?case by presburger
qed

lemma wf_subst_append:
  fixes \<theta>1 \<theta>2::"('f,'v) subst"
  assumes "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>1" "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>2"
    and "subst_domain \<theta>1 \<inter> subst_domain \<theta>2 = {}"
    and "subst_domain \<theta>1 \<inter> range_vars \<theta>2 = {}"
    and "range_vars \<theta>1 \<inter> subst_domain \<theta>2 = {}"
  shows "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<lambda>v. if \<theta>1 v = Var v then \<theta>2 v else \<theta>1 v)"
using assms
proof (induction \<theta>1 rule: wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_induct)
  case Empty thus ?case unfolding wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by simp
next
  case (Insert \<sigma>1 v t)
  let ?if = "\<lambda>w. if \<sigma>1 w = Var w then \<theta>2 w else \<sigma>1 w"
  let ?if_upd = "\<lambda>w. if (\<sigma>1(v := t)) w = Var w then \<theta>2 w else (\<sigma>1(v := t)) w"

  from Insert.hyps(4) have "?if_upd = ?if(v := t)" by fastforce

  have dom_insert: "subst_domain (\<sigma>1(v := t)) = insert v (subst_domain \<sigma>1)"
    using Insert.hyps(4) by (auto simp add: subst_domain_def)

  have "\<sigma>1 v = Var v" "t \<noteq> Var v" using Insert.hyps(2,4) by auto
  hence img_insert: "range_vars (\<sigma>1(v := t)) = range_vars \<sigma>1 \<union> fv t"
    using subst_img_update by metis

  from Insert.prems(2) dom_insert have "subst_domain \<sigma>1 \<inter> subst_domain \<theta>2 = {}"
    by (auto simp add: subst_domain_def)
  moreover have "subst_domain \<sigma>1 \<inter> range_vars \<theta>2 = {}"
    using Insert.prems(3) dom_insert
    by (simp add: subst_domain_def)
  moreover have "range_vars \<sigma>1 \<inter> subst_domain \<theta>2 = {}"
    using Insert.prems(4) img_insert
    by blast
  ultimately have "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t ?if" using Insert.IH[OF Insert.prems(1)] by metis
  
  have dom_union: "subst_domain ?if = subst_domain \<sigma>1 \<union> subst_domain \<theta>2"
    by (auto simp add: subst_domain_def)
  hence "v \<notin> subst_domain ?if"
    using Insert.hyps(2) Insert.prems(2) dom_insert
    by (auto simp add: subst_domain_def)
  moreover have "v \<notin> range_vars ?if"
    using Insert.prems(3) Insert.hyps(3) dom_insert
    unfolding range_vars_alt_def by (auto simp add: subst_domain_def)
  moreover have "fv t \<inter> insert v (subst_domain ?if) = {}"
    using Insert.hyps(4) Insert.prems(4) img_insert
    unfolding range_vars_alt_def by (fastforce simp add: subst_domain_def)
  ultimately show ?case
    using wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_set.Insert \<open>wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t ?if\<close> \<open>?if_upd = ?if(v := t)\<close> wf_subst_properties
    by (metis (no_types, lifting))  
qed

lemma wf_subst_elim_append:
  assumes "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "subst_elim \<theta> v" "v \<notin> fv t"
  shows "subst_elim (\<theta>(w := t)) v"
using assms
proof (induction \<theta> rule: wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_induct)
  case (Insert \<theta> v' t')
  hence "\<And>q. v \<notin> fv (Var q \<cdot> \<theta>(v' := t'))" using subst_elimD by blast
  hence "\<And>q. v \<notin> fv (Var q \<cdot> \<theta>(v' := t', w := t))" using \<open>v \<notin> fv t\<close> by simp
  thus ?case by (metis subst_elimI' subst_apply_term.simps(1)) 
qed (simp add: subst_elim_def)

lemma wf_subst_elim_dom:
  assumes "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>"
  shows "\<forall>v \<in> subst_domain \<theta>. subst_elim \<theta> v"
using assms
proof (induction \<theta> rule: wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_induct)
  case (Insert \<theta> w t)
  have dom_insert: "subst_domain (\<theta>(w := t)) \<subseteq> insert w (subst_domain \<theta>)"
    by (auto simp add: subst_domain_def)
  hence "\<forall>v \<in> subst_domain \<theta>. subst_elim (\<theta>(w := t)) v" using Insert.IH Insert.hyps(2,4)
    by (metis Insert.hyps(1) IntI disjoint_insert(2) empty_iff wf_subst_elim_append) 
  moreover have "w \<notin> fv t" using Insert.hyps(4) by simp
  hence "\<And>q. w \<notin> fv (Var q \<cdot> \<theta>(w := t))"
    by (metis fv_simps(1) fv_in_subst_img Insert.hyps(3) contra_subsetD 
              fun_upd_def singletonD subst_apply_term.simps(1)) 
  hence "subst_elim (\<theta>(w := t)) w" by (metis subst_elimI')
  ultimately show ?case using dom_insert by blast
qed simp

lemma wf_subst_support_iff_mgt: "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<Longrightarrow> \<theta> supports \<delta> \<longleftrightarrow> \<theta> \<preceq>\<^sub>\<circ> \<delta>"
using subst_support_def subst_support_if_mgt_subst_idem wf_subst_subst_idem by blast 


subsection \<open>Interpretations\<close>
abbreviation interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t::"('a,'b) subst \<Rightarrow> bool" where
  "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<equiv> subst_domain \<theta> = UNIV \<and> ground (subst_range \<theta>)"

lemma interpretation_substI:
  "(\<And>v. fv (\<theta> v) = {}) \<Longrightarrow> interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>"
proof -
  assume "\<And>v. fv (\<theta> v) = {}"
  moreover { fix v assume "fv (\<theta> v) = {}" hence "v \<in> subst_domain \<theta>" by auto }
  ultimately show ?thesis by auto
qed

lemma interpretation_grounds[simp]:
  "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<Longrightarrow> fv (t \<cdot> \<theta>) = {}"
using subst_fv_dom_ground_if_ground_img[of t \<theta>] by blast

lemma interpretation_grounds_all:
  "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<Longrightarrow> (\<And>v. fv (\<theta> v) = {})"
by (metis range_vars_alt_def UNIV_I fv_in_subst_img subset_empty subst_dom_vars_in_subst)

lemma interpretation_grounds_all':
  "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<Longrightarrow> ground (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
using subst_fv_dom_ground_if_ground_img[of _ \<theta>]
by simp

lemma interpretation_comp:
  assumes "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" 
  shows "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<sigma> \<circ>\<^sub>s \<theta>)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<theta> \<circ>\<^sub>s \<sigma>)"
proof -
  have \<theta>_fv: "fv (\<theta> v) = {}" for v using interpretation_grounds_all[OF assms] by simp
  hence \<theta>_fv': "fv (t \<cdot> \<theta>) = {}" for t
    by (metis all_not_in_conv subst_elimD subst_elimI' subst_apply_term.simps(1))

  from assms have "(\<sigma> \<circ>\<^sub>s \<theta>) v \<noteq> Var v" for v
    unfolding subst_compose_def by (metis fv_simps(1) \<theta>_fv' insert_not_empty)
  hence "subst_domain (\<sigma> \<circ>\<^sub>s \<theta>) = UNIV" by (simp add: subst_domain_def)
  moreover have "fv ((\<sigma> \<circ>\<^sub>s \<theta>) v) = {}" for v unfolding subst_compose_def using \<theta>_fv' by simp
  hence "ground (subst_range (\<sigma> \<circ>\<^sub>s \<theta>))" by simp
  ultimately show "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<sigma> \<circ>\<^sub>s \<theta>)" ..

  from assms have "(\<theta> \<circ>\<^sub>s \<sigma>) v \<noteq> Var v" for v
    unfolding subst_compose_def by (metis fv_simps(1) \<theta>_fv insert_not_empty subst_to_var_is_var)
  hence "subst_domain (\<theta> \<circ>\<^sub>s \<sigma>) = UNIV" by (simp add: subst_domain_def)
  moreover have "fv ((\<theta> \<circ>\<^sub>s \<sigma>) v) = {}" for v
    unfolding subst_compose_def by (simp add: \<theta>_fv trm_subst_ident) 
  hence "ground (subst_range (\<theta> \<circ>\<^sub>s \<sigma>))" by simp
  ultimately show "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<theta> \<circ>\<^sub>s \<sigma>)" ..
qed

lemma interpretation_subst_exists:
  "\<exists>\<I>::('f,'v) subst. interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>"
proof -
  obtain c::"'f" where "c \<in> UNIV" by simp
  then obtain \<I>::"('f,'v) subst" where "\<And>v. \<I> v = Fun c []" by simp
  hence "subst_domain \<I> = UNIV" "ground (subst_range \<I>)"
    by (simp_all add: subst_domain_def)
  thus ?thesis by auto
qed

lemma interpretation_subst_exists':
  "\<exists>\<theta>::('f,'v) subst. subst_domain \<theta> = X \<and> ground (subst_range \<theta>)"
proof -
  obtain \<I>::"('f,'v) subst" where \<I>: "subst_domain \<I> = UNIV" "ground (subst_range \<I>)"
    using interpretation_subst_exists by moura
  let ?\<theta> = "rm_vars (UNIV - X) \<I>"
  have 1: "subst_domain ?\<theta> = X" using \<I> by (auto simp add: subst_domain_def)
  hence 2: "ground (subst_range ?\<theta>)" using \<I> by force
  show ?thesis using 1 2 by blast
qed

lemma interpretation_subst_idem:
  "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<Longrightarrow> subst_idem \<theta>"
unfolding subst_idem_def
using interpretation_grounds_all[of \<theta>] trm_subst_ident subst_eq_if_eq_vars
by fastforce

lemma subst_idem_comp_upd_eq:
  assumes "v \<notin> subst_domain \<I>" "subst_idem \<theta>"
  shows "\<I> \<circ>\<^sub>s \<theta> = \<I>(v := \<theta> v) \<circ>\<^sub>s \<theta>"
proof -
  from assms(1) have "(\<I> \<circ>\<^sub>s \<theta>) v = \<theta> v" unfolding subst_compose_def by auto
  moreover have "\<And>w. w \<noteq> v \<Longrightarrow> (\<I> \<circ>\<^sub>s \<theta>) w = (\<I>(v := \<theta> v) \<circ>\<^sub>s \<theta>) w" unfolding subst_compose_def by auto
  moreover have "(\<I>(v := \<theta> v) \<circ>\<^sub>s \<theta>) v = \<theta> v" using assms(2) unfolding subst_idem_def subst_compose_def
    by (metis fun_upd_same) 
  ultimately show ?thesis by (metis fun_upd_same fun_upd_triv subst_comp_upd1)
qed

lemma interpretation_dom_img_disjoint:
  "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I> \<Longrightarrow> subst_domain \<I> \<inter> range_vars \<I> = {}"
unfolding range_vars_alt_def by auto


subsection \<open>Basic Properties of MGUs\<close>
lemma MGU_is_mgu_singleton: "MGU \<theta> t u = is_mgu \<theta> {(t,u)}"
unfolding is_mgu_def unifiers_def by auto

lemma Unifier_in_unifiers_singleton: "Unifier \<theta> s t \<longleftrightarrow> \<theta> \<in> unifiers {(s,t)}"
unfolding unifiers_def by auto

lemma subst_list_singleton_fv_subset:
  "(\<Union>x \<in> set (subst_list (subst v t) E). fv (fst x) \<union> fv (snd x))
    \<subseteq> fv t \<union> (\<Union>x \<in> set E. fv (fst x) \<union> fv (snd x))"
proof (induction E)
  case (Cons x E)
  let ?fvs = "\<lambda>L. \<Union>x \<in> set L. fv (fst x) \<union> fv (snd x)"
  let ?fvx = "fv (fst x) \<union> fv (snd x)"
  let ?fvxsubst = "fv (fst x \<cdot> Var(v := t)) \<union> fv (snd x \<cdot> Var(v := t))"
  have "?fvs (subst_list (subst v t) (x#E)) = ?fvxsubst \<union> ?fvs (subst_list (subst v t) E)"
    unfolding subst_list_def subst_def by auto
  hence "?fvs (subst_list (subst v t) (x#E)) \<subseteq> ?fvxsubst \<union> fv t \<union> ?fvs E"
    using Cons.IH by blast
  moreover have "?fvs (x#E) = ?fvx \<union> ?fvs E" by auto
  moreover have "?fvxsubst \<subseteq> ?fvx \<union> fv t" using subst_fv_bound_singleton[of _ v t] by blast
  ultimately show ?case unfolding range_vars_alt_def by auto
qed (simp add: subst_list_def)

lemma subst_of_dom_subset: "subst_domain (subst_of L) \<subseteq> set (map fst L)"
proof (induction L rule: List.rev_induct)
  case (snoc x L)
  then obtain v t where x: "x = (v,t)" by (metis surj_pair)
  hence "subst_of (L@[x]) = Var(v := t) \<circ>\<^sub>s subst_of L"
    unfolding subst_of_def subst_def by (induct L) auto
  hence "subst_domain (subst_of (L@[x])) \<subseteq> insert v (subst_domain (subst_of L))"
    using x subst_domain_compose[of "Var(v := t)" "subst_of L"]
    by (auto simp add: subst_domain_def)
  thus ?case using snoc.IH x by auto
qed simp

lemma wf_MGU_is_imgu_singleton: "wf\<^sub>M\<^sub>G\<^sub>U \<theta> s t \<Longrightarrow> is_imgu \<theta> {(s,t)}"
proof -
  assume 1: "wf\<^sub>M\<^sub>G\<^sub>U \<theta> s t"

  have 2: "subst_idem \<theta>" by (metis wf_subst_subst_idem 1 wf\<^sub>M\<^sub>G\<^sub>U_def)

  have 3: "\<forall>\<theta>' \<in> unifiers {(s,t)}. \<theta> \<preceq>\<^sub>\<circ> \<theta>'" "\<theta> \<in> unifiers {(s,t)}"
    by (metis 1 Unifier_in_unifiers_singleton wf\<^sub>M\<^sub>G\<^sub>U_def)+

  have "\<forall>\<tau> \<in> unifiers {(s,t)}. \<tau> = \<theta> \<circ>\<^sub>s \<tau>" by (metis 2 3 subst_idem_def subst_compose_assoc)
  thus "is_imgu \<theta> {(s,t)}" by (metis is_imgu_def \<open>\<theta> \<in> unifiers {(s,t)}\<close>)
qed

lemma mgu_subst_range_vars:
  assumes "mgu s t = Some \<sigma>" shows "range_vars \<sigma> \<subseteq> vars_term s \<union> vars_term t"
proof -
  obtain xs where *: "Unification.unify [(s, t)] [] = Some xs" and [simp]: "subst_of xs = \<sigma>"
    using assms by (simp split: option.splits)
  from unify_Some_UNIF [OF *] obtain ss
    where "compose ss = \<sigma>" and "UNIF ss {#(s, t)#} {#}" by auto
  with UNIF_range_vars_subset [of ss "{#(s, t)#}" "{#}"]
    show ?thesis by (metis vars_mset_singleton fst_conv snd_conv) 
qed

lemma mgu_subst_domain_range_vars_disjoint:
  assumes "mgu s t = Some \<sigma>" shows "subst_domain \<sigma> \<inter> range_vars \<sigma> = {}"
proof -
  have "is_imgu \<sigma> {(s, t)}" using assms mgu_sound by simp
  hence "\<sigma> = \<sigma> \<circ>\<^sub>s \<sigma>" unfolding is_imgu_def by blast
  thus ?thesis by (metis subst_idemp_iff) 
qed

lemma mgu_same_empty: "mgu (t::('a,'b) term) t = Some Var"
proof -
  { fix E::"('a,'b) equation list" and U::"('b \<times> ('a,'b) term) list"
    assume "\<forall>(s,t) \<in> set E. s = t"
    hence "Unification.unify E U = Some U"
    proof (induction E U rule: Unification.unify.induct)
      case (2 f S g T E U)
      hence *: "f = g" "S = T" by auto
      moreover have "\<forall>(s,t) \<in> set (zip T T). s = t" by (induct T) auto
      hence "\<forall>(s,t) \<in> set (zip T T@E). s = t" using "2.prems"(1) by auto
      moreover have "zip_option S T = Some (zip S T)" using \<open>S = T\<close> by auto
      hence **: "decompose (Fun f S) (Fun g T) = Some (zip S T)"
        using \<open>f = g\<close> unfolding decompose_def by auto
      ultimately have "Unification.unify (zip S T@E) U = Some U" using "2.IH" * by auto
      thus ?case using ** by auto
    qed auto
  }
  hence "Unification.unify [(t,t)] [] = Some []" by auto
  thus ?thesis by auto
qed

lemma mgu_var: assumes "x \<notin> fv t" shows "mgu (Var x) t = Some (Var(x := t))"
proof -
  have "unify [(Var x,t)] [] = Some [(x,t)]" using assms by (auto simp add: subst_list_def)
  moreover have "subst_of [(x,t)] = Var(x := t)" unfolding subst_of_def subst_def by simp
  ultimately show ?thesis by simp
qed

lemma mgu_gives_wellformed_subst:
  assumes "mgu s t = Some \<theta>" shows "wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>"
using mgu_finite_subst_domain[OF assms] mgu_subst_domain_range_vars_disjoint[OF assms]
unfolding wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def
by auto

lemma mgu_gives_wellformed_MGU:
  assumes "mgu s t = Some \<theta>" shows "wf\<^sub>M\<^sub>G\<^sub>U \<theta> s t"
using mgu_subst_domain[OF assms] mgu_sound[OF assms] mgu_subst_range_vars [OF assms]
      MGU_is_mgu_singleton[of s \<theta> t] is_imgu_imp_is_mgu[of \<theta> "{(s,t)}"]
      mgu_gives_wellformed_subst[OF assms]
unfolding wf\<^sub>M\<^sub>G\<^sub>U_def by blast

lemma mgu_vars_bounded[dest?]:
  "mgu M N = Some \<sigma> \<Longrightarrow> subst_domain \<sigma> \<union> range_vars \<sigma> \<subseteq> fv M \<union> fv N"
using mgu_gives_wellformed_MGU unfolding wf\<^sub>M\<^sub>G\<^sub>U_def by blast

lemma mgu_gives_subst_idem: "mgu s t = Some \<theta> \<Longrightarrow> subst_idem \<theta>"
using mgu_sound[of s t \<theta>] unfolding is_imgu_def subst_idem_def by auto

lemma mgu_always_unifies: "Unifier \<theta> M N \<Longrightarrow> \<exists>\<delta>. mgu M N = Some \<delta>"
using mgu_complete Unifier_in_unifiers_singleton by blast

lemma mgu_gives_MGU: "mgu s t = Some \<theta> \<Longrightarrow> MGU \<theta> s t"
using mgu_sound[of s t \<theta>, THEN is_imgu_imp_is_mgu] MGU_is_mgu_singleton by metis

lemma mgu_eliminates[dest?]:
  assumes "mgu M N = Some \<sigma>"
  shows "(\<exists>v \<in> fv M \<union> fv N. subst_elim \<sigma> v) \<or> \<sigma> = Var"
  (is "?P M N \<sigma>")
proof (cases "\<sigma> = Var")
  case False
  then obtain v where v: "v \<in> subst_domain \<sigma>" by auto
  hence "v \<in> fv M \<union> fv N" using mgu_vars_bounded[OF assms] by blast
  thus ?thesis using wf_subst_elim_dom[OF mgu_gives_wellformed_subst[OF assms]] v by blast
qed simp

lemma mgu_eliminates_dom:
  assumes "mgu x y = Some \<theta>" "v \<in> subst_domain \<theta>"
  shows "subst_elim \<theta> v"
using mgu_gives_wellformed_subst[OF assms(1)]
unfolding wf\<^sub>M\<^sub>G\<^sub>U_def wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def subst_elim_def
by (metis disjoint_iff_not_equal subst_dom_elim assms(2))

lemma unify_list_distinct:
  assumes "Unification.unify E B = Some U" "distinct (map fst B)"
  and "(\<Union>x \<in> set E. fv (fst x) \<union> fv (snd x)) \<inter> set (map fst B) = {}"
  shows "distinct (map fst U)"
using assms
proof (induction E B arbitrary: U rule: Unification.unify.induct)
  case 1 thus ?case by simp
next
  case (2 f X g Y E B U)
  let ?fvs = "\<lambda>L. \<Union>x \<in> set L. fv (fst x) \<union> fv (snd x)"
  from "2.prems"(1) obtain E' where *: "decompose (Fun f X) (Fun g Y) = Some E'"
    and [simp]: "f = g" "length X = length Y" "E' = zip X Y"
    and **: "Unification.unify (E'@E) B = Some U"
    by (auto split: option.splits)
  hence "\<And>t t'. (t,t') \<in> set E' \<Longrightarrow> fv t \<subseteq> fv (Fun f X) \<and> fv t' \<subseteq> fv (Fun g Y)"
    by (metis zip_arg_subterm subtermeq_vars_subset)
  hence "?fvs E' \<subseteq> fv (Fun f X) \<union> fv (Fun g Y)" by fastforce
  moreover have "fv (Fun f X) \<inter> set (map fst B) = {}" "fv (Fun g Y) \<inter> set (map fst B) = {}"
    using "2.prems"(3) by auto
  ultimately have "?fvs E' \<inter> set (map fst B) = {}" by blast
  moreover have "?fvs E \<inter> set (map fst B) = {}" using "2.prems"(3) by auto
  ultimately have "?fvs (E'@E) \<inter> set (map fst B) = {}" by auto
  thus ?case using "2.IH"[OF * ** "2.prems"(2)] by metis
next
  case (3 v t E B)
  let ?fvs = "\<lambda>L. \<Union>x \<in> set L. fv (fst x) \<union> fv (snd x)"
  let ?E' = "subst_list (subst v t) E"
  from "3.prems"(3) have "v \<notin> set (map fst B)" "fv t \<inter> set (map fst B) = {}" by force+
  hence *: "distinct (map fst ((v, t)#B))" using "3.prems"(2) by auto

  show ?case
  proof (cases "t = Var v")
    case True thus ?thesis using "3.prems" "3.IH"(1) by auto
  next
    case False
    hence "v \<notin> fv t" using "3.prems"(1) by auto
    hence "Unification.unify (subst_list (subst v t) E) ((v, t)#B) = Some U"
      using \<open>t \<noteq> Var v\<close> "3.prems"(1) by auto
    moreover have "?fvs ?E' \<inter> set (map fst ((v, t)#B)) = {}"
    proof -
      have "v \<notin> ?fvs ?E'"
        unfolding subst_list_def subst_def
        by (simp add: \<open>v \<notin> fv t\<close> subst_remove_var)
      moreover have "?fvs ?E' \<subseteq> fv t \<union> ?fvs E" by (metis subst_list_singleton_fv_subset)
      hence "?fvs ?E' \<inter> set (map fst B) = {}" using "3.prems"(3) by auto
      ultimately show ?thesis by auto
    qed 
    ultimately show ?thesis using "3.IH"(2)[OF \<open>t \<noteq> Var v\<close> \<open>v \<notin> fv t\<close> _ *] by metis
  qed
next
  case (4 f X v E B U)
  let ?fvs = "\<lambda>L. \<Union>x \<in> set L. fv (fst x) \<union> fv (snd x)"
  let ?E' = "subst_list (subst v (Fun f X)) E"
  have *: "?fvs E \<inter> set (map fst B) = {}" using "4.prems"(3) by auto
  from "4.prems"(1) have "v \<notin> fv (Fun f X)" by force
  from "4.prems"(3) have **: "v \<notin> set (map fst B)" "fv (Fun f X) \<inter> set (map fst B) = {}" by force+
  hence ***: "distinct (map fst ((v, Fun f X)#B))" using "4.prems"(2) by auto
  from "4.prems"(3) have ****: "?fvs ?E' \<inter> set (map fst ((v, Fun f X)#B)) = {}"
  proof -
    have "v \<notin> ?fvs ?E'"
      unfolding subst_list_def subst_def
      using \<open>v \<notin> fv (Fun f X)\<close> subst_remove_var[of v "Fun f X"] by simp
    moreover have "?fvs ?E' \<subseteq> fv (Fun f X) \<union> ?fvs E" by (metis subst_list_singleton_fv_subset)
    hence "?fvs ?E' \<inter> set (map fst B) = {}" using * ** by blast
    ultimately show ?thesis by auto
  qed
  have "Unification.unify (subst_list (subst v (Fun f X)) E) ((v, Fun f X) # B) = Some U"
    using \<open>v \<notin> fv (Fun f X)\<close> "4.prems"(1) by auto
  thus ?case using "4.IH"[OF \<open>v \<notin> fv (Fun f X)\<close> _ *** ****] by metis
qed

lemma mgu_None_is_subst_neq:
  fixes s t::"('a,'b) term" and \<delta>::"('a,'b) subst"
  assumes "mgu s t = None"
  shows "s \<cdot> \<delta> \<noteq> t \<cdot> \<delta>"
using assms mgu_always_unifies by force

lemma mgu_None_if_neq_ground:
  assumes "t \<noteq> t'" "fv t = {}" "fv t' = {}"
  shows "mgu t t' = None"
proof (rule ccontr)
  assume "mgu t t' \<noteq> None"
  then obtain \<delta> where \<delta>: "mgu t t' = Some \<delta>" by auto
  hence "t \<cdot> \<delta> = t" "t' \<cdot> \<delta> = t'" using assms subst_ground_ident by auto
  thus False using assms(1) MGU_is_Unifier[OF mgu_gives_MGU[OF \<delta>]] by auto
qed

lemma mgu_None_commutes:
  "mgu s t = None \<Longrightarrow> mgu t s = None"
using mgu_complete[of s t]
      Unifier_in_unifiers_singleton[of s _ t]
      Unifier_sym[of t _ s]
      Unifier_in_unifiers_singleton[of t _ s]
      mgu_sound[of t s]
unfolding is_imgu_def
by fastforce

lemma mgu_img_subterm_subst:
  fixes \<delta>::"('f,'v) subst" and s t u::"('f,'v) term"
  assumes "mgu s t = Some \<delta>" "u \<in> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<delta>) - range Var"
  shows "u \<in> ((subterms s \<union> subterms t) - range Var) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
proof -
  define subterms_tuples::"('f,'v) equation list \<Rightarrow> ('f,'v) terms" where subtt_def:
    "subterms_tuples \<equiv> \<lambda>E. subterms\<^sub>s\<^sub>e\<^sub>t (fst ` set E) \<union> subterms\<^sub>s\<^sub>e\<^sub>t (snd ` set E)"
  define subterms_img::"('f,'v) subst \<Rightarrow> ('f,'v) terms" where subti_def:
    "subterms_img \<equiv> \<lambda>d. subterms\<^sub>s\<^sub>e\<^sub>t (subst_range d)"

  define d where "d \<equiv> \<lambda>v t. subst v t::('f,'v) subst"
  define V where "V \<equiv> range Var::('f,'v) terms"
  define R where "R \<equiv> \<lambda>d::('f,'v) subst. ((subterms s \<union> subterms t) - V) \<cdot>\<^sub>s\<^sub>e\<^sub>t d"
  define M where "M \<equiv> \<lambda>E d. subterms_tuples E \<union> subterms_img d"
  define Q where "Q \<equiv> (\<lambda>E d. M E d - V \<subseteq> R d - V)"
  define Q' where "Q' \<equiv> (\<lambda>E d d'. (M E d - V) \<cdot>\<^sub>s\<^sub>e\<^sub>t d' \<subseteq> (R d - V) \<cdot>\<^sub>s\<^sub>e\<^sub>t (d'::('f,'v) subst))"

  have Q_subst: "Q (subst_list (subst v t') E) (subst_of ((v, t')#B))" 
    when v_fv: "v \<notin> fv t'" and Q_assm: "Q ((Var v, t')#E) (subst_of B)"
    for v t' E B
  proof -
    define E' where "E' \<equiv> subst_list (subst v t') E"
    define B' where "B' \<equiv> subst_of ((v, t')#B)"

    have E': "E' = subst_list (d v t') E"
        and B': "B' = subst_of B \<circ>\<^sub>s d v t'"
      using subst_of_simps(3)[of "(v, t')"]
      unfolding subst_def E'_def B'_def d_def by simp_all

    have vt_img_subt: "subterms\<^sub>s\<^sub>e\<^sub>t (subst_range (d v t')) = subterms t'"
         and vt_dom: "subst_domain (d v t') = {v}"
      using v_fv by (auto simp add: subst_domain_def d_def subst_def)

    have *: "subterms u1 \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (fst ` set E)" "subterms u2 \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (snd ` set E)"
      when "(u1,u2) \<in> set E" for u1 u2
      using that by auto

    have **: "subterms\<^sub>s\<^sub>e\<^sub>t (d v t' ` (fv u \<inter> subst_domain (d v t'))) \<subseteq> subterms t'"
      for u::"('f,'v) term"
      using vt_dom unfolding d_def by force

    have 1: "subterms_tuples E' - V \<subseteq> (subterms t' - V) \<union> (subterms_tuples E - V \<cdot>\<^sub>s\<^sub>e\<^sub>t d v t')"
      (is "?A \<subseteq> ?B")
    proof
      fix u assume "u \<in> ?A"
      then obtain u1 u2 where u12:
          "(u1,u2) \<in> set E"
          "u \<in> (subterms (u1 \<cdot> (d v t')) - V) \<union> (subterms (u2 \<cdot> (d v t')) - V)"
        unfolding subtt_def subst_list_def E'_def d_def by moura
      hence "u \<in> (subterms t' - V) \<union> (((subterms_tuples E) \<cdot>\<^sub>s\<^sub>e\<^sub>t d v t') - V)"
        using subterms_subst[of u1 "d v t'"] subterms_subst[of u2 "d v t'"]
              *[OF u12(1)] **[of u1] **[of u2]
        unfolding subtt_def subst_list_def by auto
      moreover have
          "(subterms_tuples E \<cdot>\<^sub>s\<^sub>e\<^sub>t d v t') - V \<subseteq>
           (subterms_tuples E - V \<cdot>\<^sub>s\<^sub>e\<^sub>t d v t') \<union> {t'}"
        unfolding subst_def subtt_def V_def d_def by force
      ultimately show "u \<in> ?B" using u12 v_fv by auto
    qed

    have 2: "subterms_img B' - V \<subseteq>
             (subterms t' - V) \<union> (subterms_img (subst_of B) - V \<cdot>\<^sub>s\<^sub>e\<^sub>t d v t')"
      using B' vt_img_subt subst_img_comp_subset'''[of "subst_of B" "d v t'"]
      unfolding subti_def subst_def V_def by argo

    have 3: "subterms_tuples ((Var v, t')#E) - V = (subterms t' - V) \<union> (subterms_tuples E - V)"
      by (auto simp add: subst_def subtt_def V_def)

    have "fv\<^sub>s\<^sub>e\<^sub>t (subterms t' - V) \<inter> subst_domain (d v t') = {}"
      using v_fv vt_dom fv_subterms[of t'] by fastforce
    hence 4: "subterms t' - V \<cdot>\<^sub>s\<^sub>e\<^sub>t d v t' = subterms t' - V"
      using set_subst_ident[of "subterms t' - range Var" "d v t'"] by (simp add: V_def)

    have "M E' B' - V \<subseteq> M ((Var v, t')#E) (subst_of B) - V \<cdot>\<^sub>s\<^sub>e\<^sub>t d v t'"
      using 1 2 3 4 unfolding M_def by blast
    moreover have "Q' ((Var v, t')#E) (subst_of B) (d v t')"
      using Q_assm unfolding Q_def Q'_def by auto
    moreover have "R (subst_of B) \<cdot>\<^sub>s\<^sub>e\<^sub>t d v t' = R (subst_of ((v,t')#B))"
      unfolding R_def d_def by auto 
    ultimately have
      "M (subst_list (d v t') E) (subst_of ((v, t')#B)) - V \<subseteq> R (subst_of ((v, t')#B)) - V"
      unfolding Q'_def E'_def B'_def d_def by blast
    thus ?thesis unfolding Q_def M_def R_def d_def by blast
  qed

  have "u \<in> subterms s \<union> subterms t - V \<cdot>\<^sub>s\<^sub>e\<^sub>t subst_of U"
    when assms':
      "unify E B = Some U"
      "u \<in> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range (subst_of U)) - V"
      "Q E (subst_of B)"
    for E B U and T::"('f,'v) term list"
    using assms'
  proof (induction E B arbitrary: U rule: Unification.unify.induct)
    case (1 B) thus ?case by (auto simp add: Q_def M_def R_def subti_def)
  next
    case (2 g X h Y E B U)
    from "2.prems"(1) obtain E' where E':
        "decompose (Fun g X) (Fun h Y) = Some E'"
        "g = h" "length X = length Y" "E' = zip X Y"
        "Unification.unify (E'@E) B = Some U"
      by (auto split: option.splits)
    moreover have "subterms_tuples (E'@E) \<subseteq> subterms_tuples ((Fun g X, Fun h Y)#E)"
    proof
      fix u assume "u \<in> subterms_tuples (E'@E)"
      then obtain u1 u2 where u12: "(u1,u2) \<in> set (E'@E)" "u \<in> subterms u1 \<union> subterms u2"
        unfolding subtt_def by fastforce
      thus "u \<in> subterms_tuples ((Fun g X, Fun h Y)#E)"
      proof (cases "(u1,u2) \<in> set E'")
        case True
        hence "subterms u1 \<subseteq> subterms (Fun g X)" "subterms u2 \<subseteq> subterms (Fun h Y)"
          using E'(4) subterms_subset params_subterms subsetCE
          by (metis set_zip_leftD, metis set_zip_rightD)
        thus ?thesis using u12 unfolding subtt_def by auto
      next
        case False thus ?thesis using u12 unfolding subtt_def by fastforce
      qed
     qed
    hence "Q (E'@E) (subst_of B)" using "2.prems"(3) unfolding Q_def M_def by blast
    ultimately show ?case using "2.IH"[of E' U] "2.prems" by meson
  next
    case (3 v t' E B)
    show ?case
    proof (cases "t' = Var v")
      case True thus ?thesis
        using "3.prems" "3.IH"(1) unfolding Q_def M_def V_def subtt_def by auto
    next
      case False
      hence 1: "v \<notin> fv t'" using "3.prems"(1) by auto
      hence "unify (subst_list (subst v t') E) ((v, t')#B) = Some U"
        using False "3.prems"(1) by auto
      thus ?thesis
        using Q_subst[OF 1 "3.prems"(3)]
              "3.IH"(2)[OF False 1 _ "3.prems"(2)]
        by metis
    qed
  next
    case (4 g X v E B U)
    have 1: "v \<notin> fv (Fun g X)" using "4.prems"(1) not_None_eq by fastforce
    hence 2: "unify (subst_list (subst v (Fun g X)) E) ((v, Fun g X)#B) = Some U"
      using "4.prems"(1) by auto

    have 3: "Q ((Var v, Fun g X)#E) (subst_of B)"
      using "4.prems"(3) unfolding Q_def M_def subtt_def by auto
    
    show ?case
      using Q_subst[OF 1 3] "4.IH"[OF 1 2 "4.prems"(2)]
      by metis
  qed
  moreover obtain D where "unify [(s, t)] [] = Some D" "\<delta> = subst_of D"
    using assms(1) by (auto split: option.splits)
  moreover have "Q [(s,t)] (subst_of [])"
    unfolding Q_def M_def R_def subtt_def subti_def
    by force
  ultimately show ?thesis using assms(2) unfolding V_def by auto
qed

lemma mgu_img_consts:
  fixes \<delta>::"('f,'v) subst" and s t::"('f,'v) term" and c::'f and z::'v
  assumes "mgu s t = Some \<delta>" "Fun c [] \<in> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<delta>)"
  shows "Fun c [] \<in> subterms s \<union> subterms t"
proof -
  obtain u where "u \<in> (subterms s \<union> subterms t) - range Var" "u \<cdot> \<delta> = Fun c []"
    using mgu_img_subterm_subst[OF assms(1), of "Fun c []"] assms(2) by force
  thus ?thesis by (cases u) auto
qed

lemma mgu_img_consts':
  fixes \<delta>::"('f,'v) subst" and s t::"('f,'v) term" and c::'f and z::'v
  assumes "mgu s t = Some \<delta>" "\<delta> z = Fun c []"
  shows "Fun c [] \<sqsubseteq> s \<or> Fun c [] \<sqsubseteq> t"
using mgu_img_consts[OF assms(1)] assms(2)
by (metis Un_iff in_subterms_Union subst_imgI term.distinct(1)) 

lemma mgu_img_composed_var_term:
  fixes \<delta>::"('f,'v) subst" and s t::"('f,'v) term" and f::'f and Z::"'v list"
  assumes "mgu s t = Some \<delta>" "Fun f (map Var Z) \<in> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<delta>)"
  shows "\<exists>Z'. map \<delta> Z' = map Var Z \<and> Fun f (map Var Z') \<in> subterms s \<union> subterms t"
proof -
  obtain u where u: "u \<in> (subterms s \<union> subterms t) - range Var" "u \<cdot> \<delta> = Fun f (map Var Z)"
    using mgu_img_subterm_subst[OF assms(1), of "Fun f (map Var Z)"] assms(2) by fastforce
  then obtain T where T: "u = Fun f T" "map (\<lambda>t. t \<cdot> \<delta>) T = map Var Z" by (cases u) auto
  have "\<forall>t \<in> set T. \<exists>x. t = Var x" using T(2) by (induct T arbitrary: Z) auto
  then obtain Z' where Z': "map Var Z' = T" by (metis ex_map_conv) 
  hence "map \<delta> Z' = map Var Z" using T(2) by (induct Z' arbitrary: T Z) auto
  thus ?thesis using u(1) T(1) Z' by auto
qed


subsection \<open>Lemmata: The "Inequality Lemmata"\<close>
text \<open>Subterm injectivity (a stronger injectivity property)\<close>
definition subterm_inj_on where
  "subterm_inj_on f A \<equiv> \<forall>x\<in>A. \<forall>y\<in>A. (\<exists>v. v \<sqsubseteq> f x \<and> v \<sqsubseteq> f y) \<longrightarrow> x = y"

lemma subterm_inj_on_imp_inj_on: "subterm_inj_on f A \<Longrightarrow> inj_on f A"
unfolding subterm_inj_on_def inj_on_def by fastforce

lemma subst_inj_on_is_bij_betw:
  "inj_on \<theta> (subst_domain \<theta>) = bij_betw \<theta> (subst_domain \<theta>) (subst_range \<theta>)"
unfolding inj_on_def bij_betw_def by auto

lemma subterm_inj_on_alt_def:
    "subterm_inj_on f A \<longleftrightarrow>
     (inj_on f A \<and> (\<forall>s \<in> f`A. \<forall>u \<in> f`A. (\<exists>v. v \<sqsubseteq> s \<and> v \<sqsubseteq> u) \<longrightarrow> s = u))"
    (is "?A \<longleftrightarrow> ?B")
unfolding subterm_inj_on_def inj_on_def by fastforce

lemma subterm_inj_on_alt_def':
    "subterm_inj_on \<theta> (subst_domain \<theta>) \<longleftrightarrow>
     (inj_on \<theta> (subst_domain \<theta>) \<and>
      (\<forall>s \<in> subst_range \<theta>. \<forall>u \<in> subst_range \<theta>. (\<exists>v. v \<sqsubseteq> s \<and> v \<sqsubseteq> u) \<longrightarrow> s = u))"
    (is "?A \<longleftrightarrow> ?B")
by (metis subterm_inj_on_alt_def subst_range.simps)

lemma subterm_inj_on_subset:
  assumes "subterm_inj_on f A"
    and "B \<subseteq> A"
  shows "subterm_inj_on f B"
proof -
  have "inj_on f A" "\<forall>s\<in>f ` A. \<forall>u\<in>f ` A. (\<exists>v. v \<sqsubseteq> s \<and> v \<sqsubseteq> u) \<longrightarrow> s = u"
    using subterm_inj_on_alt_def[of f A] assms(1) by auto
  moreover have "f ` B \<subseteq> f ` A" using assms(2) by auto
  ultimately have "inj_on f B" "\<forall>s\<in>f ` B. \<forall>u\<in>f ` B. (\<exists>v. v \<sqsubseteq> s \<and> v \<sqsubseteq> u) \<longrightarrow> s = u"
    using inj_on_subset[of f A] assms(2) by blast+
  thus ?thesis by (metis subterm_inj_on_alt_def)
qed

lemma inj_subst_unif_consts:
  fixes \<I> \<theta> \<sigma>::"('f,'v) subst" and s t::"('f,'v) term"
  assumes \<theta>: "subterm_inj_on \<theta> (subst_domain \<theta>)" "\<forall>x \<in> (fv s \<union> fv t) - X. \<exists>c. \<theta> x = Fun c []"
             "subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>) \<inter> (subterms s \<union> subterms t) = {}" "ground (subst_range \<theta>)"
             "subst_domain \<theta> \<inter> X = {}"
  and \<I>: "ground (subst_range \<I>)" "subst_domain \<I> = subst_domain \<theta>"
  and unif: "Unifier \<sigma> (s \<cdot> \<theta>) (t \<cdot> \<theta>)"
  shows "\<exists>\<delta>. Unifier \<delta> (s \<cdot> \<I>) (t \<cdot> \<I>)"
proof -
  let ?xs = "subst_domain \<theta>"
  let ?ys = "(fv s \<union> fv t) - ?xs"

  have "\<exists>\<delta>::('f,'v) subst. s \<cdot> \<delta> = t \<cdot> \<delta>" by (metis subst_subst_compose unif)
  then obtain \<delta>::"('f,'v) subst" where \<delta>: "mgu s t = Some \<delta>"
    using mgu_always_unifies by moura
  have 1: "\<exists>\<sigma>::('f,'v) subst. s \<cdot> \<theta> \<cdot> \<sigma> = t \<cdot> \<theta> \<cdot> \<sigma>" by (metis unif)
  have 2: "\<And>\<gamma>::('f,'v) subst. s \<cdot> \<theta> \<cdot> \<gamma> = t \<cdot> \<theta> \<cdot> \<gamma> \<Longrightarrow> \<delta> \<preceq>\<^sub>\<circ> \<theta> \<circ>\<^sub>s \<gamma>" using mgu_gives_MGU[OF \<delta>] by simp
  have 3: "\<And>(z::'v) (c::'f). \<delta> z = Fun c [] \<Longrightarrow> Fun c [] \<sqsubseteq> s \<or> Fun c [] \<sqsubseteq> t"
    by (rule mgu_img_consts'[OF \<delta>])
  have 4: "subst_domain \<delta> \<inter> range_vars \<delta> = {}"
    by (metis mgu_gives_wellformed_subst[OF \<delta>] wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
  have 5: "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv s \<union> fv t"
    by (metis mgu_gives_wellformed_MGU[OF \<delta>] wf\<^sub>M\<^sub>G\<^sub>U_def)

  { fix x and \<gamma>::"('f,'v) subst" assume "x \<in> subst_domain \<theta>"
    hence "(\<theta> \<circ>\<^sub>s \<gamma>) x = \<theta> x"
      using \<theta>(4) ident_comp_subst_trm_if_disj[of \<gamma> \<theta>]
      unfolding range_vars_alt_def by fast
  }
  then obtain \<tau>::"('f,'v) subst" where \<tau>: "\<forall>x \<in> subst_domain \<theta>. \<theta> x = (\<delta> \<circ>\<^sub>s \<tau>) x" using 1 2 by moura

  have *: "\<And>x. x \<in> subst_domain \<delta> \<inter> subst_domain \<theta> \<Longrightarrow> \<exists>y \<in> ?ys. \<delta> x = Var y"
  proof -
    fix x assume "x \<in> subst_domain \<delta> \<inter> ?xs"
    hence x: "x \<in> subst_domain \<delta>" "x \<in> subst_domain \<theta>" by auto
    then obtain c where c: "\<theta> x = Fun c []" using \<theta>(2,5) 5 by moura
    hence *: "(\<delta> \<circ>\<^sub>s \<tau>) x = Fun c []" using \<tau> x by fastforce
    hence **: "x \<in> subst_domain (\<delta> \<circ>\<^sub>s \<tau>)" "Fun c [] \<in> subst_range (\<delta> \<circ>\<^sub>s \<tau>)"
      by (auto simp add: subst_domain_def)
    have "\<delta> x = Fun c [] \<or> (\<exists>z. \<delta> x = Var z \<and> \<tau> z = Fun c [])"
      by (rule subst_img_comp_subset_const'[OF *])
    moreover have "\<delta> x \<noteq> Fun c []"
    proof (rule ccontr)
      assume "\<not>\<delta> x \<noteq> Fun c []"
      hence "Fun c [] \<sqsubseteq> s \<or> Fun c [] \<sqsubseteq> t" using 3 by metis
      moreover have "\<forall>u \<in> subst_range \<theta>. u \<notin> subterms s \<union> subterms t"
        using \<theta>(3) by force
      hence "Fun c [] \<notin> subterms s \<union> subterms t"
        by (metis c \<open>ground (subst_range \<theta>)\<close>x(2) ground_subst_dom_iff_img) 
      ultimately show False by auto
    qed
    moreover have "\<forall>x' \<in> subst_domain \<theta>. \<delta> x \<noteq> Var x'"
    proof (rule ccontr)
      assume "\<not>(\<forall>x' \<in> subst_domain \<theta>. \<delta> x \<noteq> Var x')"
      then obtain x' where x': "x' \<in> subst_domain \<theta>" "\<delta> x = Var x'" by moura
      hence "\<tau> x' = Fun c []" "(\<delta> \<circ>\<^sub>s \<tau>) x = Fun c []" using * unfolding subst_compose_def by auto
      moreover have "x \<noteq> x'"
        using x(1) x'(2) 4
        by (auto simp add: subst_domain_def)
      moreover have "x' \<notin> subst_domain \<delta>"
        using x'(2) mgu_eliminates_dom[OF \<delta>]
        by (metis (no_types) subst_elim_def subst_apply_term.simps(1) vars_iff_subterm_or_eq)
      moreover have "(\<delta> \<circ>\<^sub>s \<tau>) x = \<theta> x" "(\<delta> \<circ>\<^sub>s \<tau>) x' = \<theta> x'" using \<tau> x(2) x'(1) by auto
      ultimately show False
        using subterm_inj_on_imp_inj_on[OF \<theta>(1)] *
        by (simp add: inj_on_def subst_compose_def x'(2) subst_domain_def)
    qed
    ultimately show "\<exists>y \<in> ?ys. \<delta> x = Var y"
      by (metis 5 x(2) subtermeqI' vars_iff_subtermeq DiffI Un_iff subst_fv_imgI sup.orderE)
  qed

  have **: "inj_on \<delta> (subst_domain \<delta> \<inter> ?xs)"
  proof (intro inj_onI)
    fix x y assume *:
      "x \<in> subst_domain \<delta> \<inter> subst_domain \<theta>" "y \<in> subst_domain \<delta> \<inter> subst_domain \<theta>" "\<delta> x = \<delta> y"
    hence "(\<delta> \<circ>\<^sub>s \<tau>) x = (\<delta> \<circ>\<^sub>s \<tau>) y" unfolding subst_compose_def by auto
    hence "\<theta> x = \<theta> y" using \<tau> * by auto
    thus "x = y" using inj_onD[OF subterm_inj_on_imp_inj_on[OF \<theta>(1)]] *(1,2) by simp
  qed

  define \<alpha> where "\<alpha> = (\<lambda>y'. if Var y' \<in> \<delta> ` (subst_domain \<delta> \<inter> ?xs)
                            then Var ((inv_into (subst_domain \<delta> \<inter> ?xs) \<delta>) (Var y'))
                            else Var y'::('f,'v) term)"
  have a1: "Unifier (\<delta> \<circ>\<^sub>s \<alpha>) s t" using mgu_gives_MGU[OF \<delta>] by auto

  define \<delta>' where "\<delta>' = \<delta> \<circ>\<^sub>s \<alpha>"
  have d1: "subst_domain \<delta>' \<subseteq> ?ys"
  proof
    fix z assume z: "z \<in> subst_domain \<delta>'"
    have "z \<in> ?xs \<Longrightarrow> z \<notin> subst_domain \<delta>'"
    proof (cases "z \<in> subst_domain \<delta>")
      case True
      moreover assume "z \<in> ?xs"
      ultimately have z_in: "z \<in> subst_domain \<delta> \<inter> ?xs" by simp
      then obtain y where y: "\<delta> z = Var y" "y \<in> ?ys" using * by moura
      hence "\<alpha> y = Var ((inv_into (subst_domain \<delta> \<inter> ?xs) \<delta>) (Var y))"
        using \<alpha>_def z_in by simp
      hence "\<alpha> y = Var z" by (metis y(1) z_in ** inv_into_f_eq)
      hence "\<delta>' z = Var z" using \<delta>'_def y(1) subst_compose_def[of \<delta> \<alpha>] by simp
      thus ?thesis by (simp add: subst_domain_def)
    next
      case False
      hence "\<delta> z = Var z" by (simp add: subst_domain_def)
      moreover assume "z \<in> ?xs"
      hence "\<alpha> z = Var z" using \<alpha>_def * by force
      ultimately show ?thesis
        using \<delta>'_def subst_compose_def[of \<delta> \<alpha>]
        by (simp add: subst_domain_def)
    qed
    moreover have "subst_domain \<alpha> \<subseteq> range_vars \<delta>"
      unfolding \<delta>'_def \<alpha>_def range_vars_alt_def
      by (auto simp add: subst_domain_def)
    hence "subst_domain \<delta>' \<subseteq> subst_domain \<delta> \<union> range_vars \<delta>"
      using subst_domain_compose[of \<delta> \<alpha>] unfolding \<delta>'_def by blast
    ultimately show "z \<in> ?ys" using 5 z by auto
  qed
  have d2: "Unifier (\<delta>' \<circ>\<^sub>s \<I>) s t" using a1 \<delta>'_def by auto
  have d3: "\<I> \<circ>\<^sub>s \<delta>' \<circ>\<^sub>s \<I> = \<delta>' \<circ>\<^sub>s \<I>"
  proof -
    { fix z::'v assume z: "z \<in> ?xs"
      then obtain u where u: "\<I> z = u" "fv u = {}" using \<I> by auto
      hence "(\<I> \<circ>\<^sub>s \<delta>' \<circ>\<^sub>s \<I>) z = u" by (simp add: subst_compose subst_ground_ident)
      moreover have "z \<notin> subst_domain \<delta>'" using d1 z by auto
      hence "\<delta>' z = Var z" by (simp add: subst_domain_def)
      hence "(\<delta>' \<circ>\<^sub>s \<I>) z = u" using u(1) by (simp add: subst_compose)
      ultimately have "(\<I> \<circ>\<^sub>s \<delta>' \<circ>\<^sub>s \<I>) z = (\<delta>' \<circ>\<^sub>s \<I>) z" by metis
    } moreover {
      fix z::'v assume "z \<in> ?ys"
      hence "z \<notin> subst_domain \<I>" using \<I>(2) by auto
      hence "(\<I> \<circ>\<^sub>s \<delta>' \<circ>\<^sub>s \<I>) z = (\<delta>' \<circ>\<^sub>s \<I>) z" by (simp add: subst_compose subst_domain_def)
    } moreover {
      fix z::'v assume "z \<notin> ?xs" "z \<notin> ?ys"
      hence "\<I> z = Var z" "\<delta>' z = Var z" using \<I>(2) d1 by blast+
      hence "(\<I> \<circ>\<^sub>s \<delta>' \<circ>\<^sub>s \<I>) z = (\<delta>' \<circ>\<^sub>s \<I>) z" by (simp add: subst_compose)
    } ultimately show ?thesis by auto
  qed

  from d2 d3 have "Unifier (\<delta>' \<circ>\<^sub>s \<I>) (s \<cdot> \<I>) (t \<cdot> \<I>)" by (metis subst_subst_compose) 
  thus ?thesis by metis
qed

lemma inj_subst_unif_comp_terms:
  fixes \<I> \<theta> \<sigma>::"('f,'v) subst" and s t::"('f,'v) term"
  assumes \<theta>: "subterm_inj_on \<theta> (subst_domain \<theta>)" "ground (subst_range \<theta>)"
             "subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>) \<inter> (subterms s \<union> subterms t) = {}"
             "(fv s \<union> fv t) - subst_domain \<theta> \<subseteq> X"
  and tfr: "\<forall>f U. Fun f U \<in> subterms s \<union> subterms t \<longrightarrow> U = [] \<or> (\<exists>u \<in> set U. u \<notin> Var ` X)"
  and \<I>: "ground (subst_range \<I>)" "subst_domain \<I> = subst_domain \<theta>"
  and unif: "Unifier \<sigma> (s \<cdot> \<theta>) (t \<cdot> \<theta>)"
  shows "\<exists>\<delta>. Unifier \<delta> (s \<cdot> \<I>) (t \<cdot> \<I>)"
proof -
  let ?xs = "subst_domain \<theta>"
  let ?ys = "(fv s \<union> fv t) - ?xs"

  have "ground (subst_range \<theta>)" using \<theta>(2) by auto

  have "\<exists>\<delta>::('f,'v) subst. s \<cdot> \<delta> = t \<cdot> \<delta>" by (metis subst_subst_compose unif)
  then obtain \<delta>::"('f,'v) subst" where \<delta>: "mgu s t = Some \<delta>"
    using mgu_always_unifies by moura
  have 1: "\<exists>\<sigma>::('f,'v) subst. s \<cdot> \<theta> \<cdot> \<sigma> = t \<cdot> \<theta> \<cdot> \<sigma>" by (metis unif)
  have 2: "\<And>\<gamma>::('f,'v) subst. s \<cdot> \<theta> \<cdot> \<gamma> = t \<cdot> \<theta> \<cdot> \<gamma> \<Longrightarrow> \<delta> \<preceq>\<^sub>\<circ> \<theta> \<circ>\<^sub>s \<gamma>" using mgu_gives_MGU[OF \<delta>] by simp
  have 3: "\<And>(z::'v) (c::'f).  Fun c [] \<sqsubseteq> \<delta> z \<Longrightarrow> Fun c [] \<sqsubseteq> s \<or> Fun c [] \<sqsubseteq> t"
    using mgu_img_consts[OF \<delta>] by force
  have 4: "subst_domain \<delta> \<inter> range_vars \<delta> = {}"
    using mgu_gives_wellformed_subst[OF \<delta>]
    by (metis wf\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
  have 5: "subst_domain \<delta> \<union> range_vars \<delta> \<subseteq> fv s \<union> fv t"
    using mgu_gives_wellformed_MGU[OF \<delta>]
    by (metis wf\<^sub>M\<^sub>G\<^sub>U_def)

  { fix x and \<gamma>::"('f,'v) subst" assume "x \<in> subst_domain \<theta>"
    hence "(\<theta> \<circ>\<^sub>s \<gamma>) x = \<theta> x"
      using \<open>ground (subst_range \<theta>)\<close> ident_comp_subst_trm_if_disj[of \<gamma> \<theta> x]
      unfolding range_vars_alt_def by blast
  }
  then obtain \<tau>::"('f,'v) subst" where \<tau>: "\<forall>x \<in> subst_domain \<theta>. \<theta> x = (\<delta> \<circ>\<^sub>s \<tau>) x" using 1 2 by moura

  have ***: "\<And>x. x \<in> subst_domain \<delta> \<inter> subst_domain \<theta> \<Longrightarrow> fv (\<delta> x) \<subseteq> ?ys"
  proof -
    fix x assume "x \<in> subst_domain \<delta> \<inter> ?xs"
    hence x: "x \<in> subst_domain \<delta>" "x \<in> subst_domain \<theta>" by auto
    moreover have "\<not>(\<exists>x' \<in> ?xs. x' \<in> fv (\<delta> x))"
    proof (rule ccontr)
      assume "\<not>\<not>(\<exists>x' \<in> ?xs. x' \<in> fv (\<delta> x))"
      then obtain x' where x': "x' \<in> fv (\<delta> x)" "x' \<in> ?xs" by metis
      have "x \<noteq> x'" "x' \<notin> subst_domain \<delta>" "\<delta> x' = Var x'"
        using 4 x(1) x'(1) unfolding range_vars_alt_def by auto
      hence "(\<delta> \<circ>\<^sub>s \<tau>) x' \<sqsubseteq> (\<delta> \<circ>\<^sub>s \<tau>) x" "\<tau> x' = (\<delta> \<circ>\<^sub>s \<tau>) x'"
        using \<tau> x(2) x'(2)
        by (metis subst_compose subst_mono vars_iff_subtermeq x'(1),
            metis subst_apply_term.simps(1) subst_compose_def)
      hence "\<theta> x' \<sqsubseteq> \<theta> x" using \<tau> x(2) x'(2) by auto
      thus False
        using \<theta>(1) x'(2) x(2) \<open>x \<noteq> x'\<close>
        unfolding subterm_inj_on_def 
        by (meson subtermeqI') 
    qed
    ultimately show "fv (\<delta> x) \<subseteq> ?ys"
      using 5 subst_dom_vars_in_subst[of x \<delta>] subst_fv_imgI[of \<delta> x]
      by blast
  qed

  have **: "inj_on \<delta> (subst_domain \<delta> \<inter> ?xs)"
  proof (intro inj_onI)
    fix x y assume *:
      "x \<in> subst_domain \<delta> \<inter> subst_domain \<theta>" "y \<in> subst_domain \<delta> \<inter> subst_domain \<theta>" "\<delta> x = \<delta> y"
    hence "(\<delta> \<circ>\<^sub>s \<tau>) x = (\<delta> \<circ>\<^sub>s \<tau>) y" unfolding subst_compose_def by auto
    hence "\<theta> x = \<theta> y" using \<tau> * by auto
    thus "x = y" using inj_onD[OF subterm_inj_on_imp_inj_on[OF \<theta>(1)]] *(1,2) by simp
  qed

  have *: "\<And>x. x \<in> subst_domain \<delta> \<inter> subst_domain \<theta> \<Longrightarrow> \<exists>y \<in> ?ys. \<delta> x = Var y"
  proof (rule ccontr)
    fix xi assume xi_assms: "xi \<in> subst_domain \<delta> \<inter> subst_domain \<theta>" "\<not>(\<exists>y \<in> ?ys. \<delta> xi = Var y)"
    hence xi_\<theta>: "xi \<in> subst_domain \<theta>" and \<delta>_xi_comp: "\<not>(\<exists>y. \<delta> xi = Var y)"
      using ***[of xi] 5 by auto
    then obtain f T where f: "\<delta> xi = Fun f T" by (cases "\<delta> xi") moura

    have "\<exists>g Y'. Y' \<noteq> [] \<and> Fun g (map Var Y') \<sqsubseteq> \<delta> xi \<and> set Y' \<subseteq> ?ys"
    proof -
      have "\<forall>c. Fun c [] \<sqsubseteq> \<delta> xi \<longrightarrow> Fun c [] \<sqsubseteq> \<theta> xi"
        using \<tau> xi_\<theta> by (metis const_subterm_subst subst_compose)
      hence 1: "\<forall>c. \<not>(Fun c [] \<sqsubseteq> \<delta> xi)"
        using 3[of _ xi] xi_\<theta> \<theta>(3)
        by auto
      
      have "\<not>(\<exists>x. \<delta> xi = Var x)" using f by auto
      hence "\<exists>g S. Fun g S \<sqsubseteq> \<delta> xi \<and> (\<forall>s \<in> set S. (\<exists>c. s = Fun c []) \<or> (\<exists>x. s = Var x))"
        using nonvar_term_has_composed_shallow_term[of "\<delta> xi"] by auto
      then obtain g S where gS: "Fun g S \<sqsubseteq> \<delta> xi" "\<forall>s \<in> set S. (\<exists>c. s = Fun c []) \<or> (\<exists>x. s = Var x)"
        by moura

      have "\<forall>s \<in> set S. \<exists>x. s = Var x"
        using 1 term.order_trans gS
        by (metis (no_types, lifting) UN_I term.order_refl subsetCE subterms.simps(2) sup_ge2)
      then obtain S' where 2: "map Var S' = S" by (metis ex_map_conv)

      have "S \<noteq> []" using 1 term.order_trans[OF _ gS(1)] by fastforce
      hence 3: "S' \<noteq> []" "Fun g (map Var S') \<sqsubseteq> \<delta> xi" using gS(1) 2 by auto

      have "set S' \<subseteq> fv (Fun g (map Var S'))" by simp
      hence 4: "set S' \<subseteq> fv (\<delta> xi)" using 3(2) fv_subterms by force
      
      show ?thesis using ***[OF xi_assms(1)] 2 3 4 by auto
    qed
    then obtain g Y' where g: "Y' \<noteq> []" "Fun g (map Var Y') \<sqsubseteq> \<delta> xi" "set Y' \<subseteq> ?ys" by moura
    then obtain X where X: "map \<delta> X = map Var Y'" "Fun g (map Var X) \<in> subterms s \<union> subterms t"
      using mgu_img_composed_var_term[OF \<delta>, of g Y'] by force
    hence "\<exists>(u::('f,'v) term) \<in> set (map Var X). u \<notin> Var ` ?ys"
      using \<theta>(4) tfr g(1) by fastforce
    then obtain j where j: "j < length X" "X ! j \<notin> ?ys"
      by (metis image_iff[of _ Var "fv s \<union> fv t - subst_domain \<theta>"] nth_map[of _ X Var]
                in_set_conv_nth[of _ "map Var X"] length_map[of Var X])

    define yj' where yj': "yj' \<equiv> Y' ! j"
    define xj where xj: "xj \<equiv> X ! j"

    have "xj \<in> fv s \<union> fv t"
      using j X(1) g(3) 5 xj yj'
      by (metis length_map nth_map term.simps(1) in_set_conv_nth le_supE subsetCE subst_domI) 
    hence xj_\<theta>: "xj \<in> subst_domain \<theta>" using j unfolding xj by simp

    have len: "length X = length Y'" by (rule map_eq_imp_length_eq[OF X(1)])
    
    have "Var yj' \<sqsubseteq> \<delta> xi"
      using term.order_trans[OF _ g(2)] j(1) len unfolding yj' by auto
    hence "\<tau> yj' \<sqsubseteq> \<theta> xi"
      using \<tau> xi_\<theta> by (metis subst_apply_term.simps(1) subst_compose_def subst_mono) 
    moreover have \<delta>_xj_var: "Var yj' = \<delta> xj"
      using X(1) len j(1) nth_map
      unfolding xj yj' by metis
    hence "\<tau> yj' = \<theta> xj" using \<tau> xj_\<theta> by (metis subst_apply_term.simps(1) subst_compose_def) 
    moreover have "xi \<noteq> xj" using \<delta>_xi_comp \<delta>_xj_var by auto
    ultimately show False using \<theta>(1) xi_\<theta> xj_\<theta> unfolding subterm_inj_on_def by blast
  qed

  define \<alpha> where "\<alpha> = (\<lambda>y'. if Var y' \<in> \<delta> ` (subst_domain \<delta> \<inter> ?xs)
                            then Var ((inv_into (subst_domain \<delta> \<inter> ?xs) \<delta>) (Var y'))
                            else Var y'::('f,'v) term)"
  have a1: "Unifier (\<delta> \<circ>\<^sub>s \<alpha>) s t" using mgu_gives_MGU[OF \<delta>] by auto

  define \<delta>' where "\<delta>' = \<delta> \<circ>\<^sub>s \<alpha>"
  have d1: "subst_domain \<delta>' \<subseteq> ?ys"
  proof
    fix z assume z: "z \<in> subst_domain \<delta>'"
    have "z \<in> ?xs \<Longrightarrow> z \<notin> subst_domain \<delta>'"
    proof (cases "z \<in> subst_domain \<delta>")
      case True
      moreover assume "z \<in> ?xs"
      ultimately have z_in: "z \<in> subst_domain \<delta> \<inter> ?xs" by simp
      then obtain y where y: "\<delta> z = Var y" "y \<in> ?ys" using * by moura
      hence "\<alpha> y = Var ((inv_into (subst_domain \<delta> \<inter> ?xs) \<delta>) (Var y))"
        using \<alpha>_def z_in by simp
      hence "\<alpha> y = Var z" by (metis y(1) z_in ** inv_into_f_eq)
      hence "\<delta>' z = Var z" using \<delta>'_def y(1) subst_compose_def[of \<delta> \<alpha>] by simp
      thus ?thesis by (simp add: subst_domain_def)
    next
      case False
      hence "\<delta> z = Var z" by (simp add: subst_domain_def)
      moreover assume "z \<in> ?xs"
      hence "\<alpha> z = Var z" using \<alpha>_def * by force
      ultimately show ?thesis using \<delta>'_def subst_compose_def[of \<delta> \<alpha>] by (simp add: subst_domain_def)
    qed
    moreover have "subst_domain \<alpha> \<subseteq> range_vars \<delta>"
      unfolding \<delta>'_def \<alpha>_def range_vars_alt_def subst_domain_def
      by auto
    hence "subst_domain \<delta>' \<subseteq> subst_domain \<delta> \<union> range_vars \<delta>"
      using subst_domain_compose[of \<delta> \<alpha>]
      unfolding \<delta>'_def by blast
    ultimately show "z \<in> ?ys" using 5 z by blast
  qed
  have d2: "Unifier (\<delta>' \<circ>\<^sub>s \<I>) s t" using a1 \<delta>'_def by auto
  have d3: "\<I> \<circ>\<^sub>s \<delta>' \<circ>\<^sub>s \<I> = \<delta>' \<circ>\<^sub>s \<I>"
  proof -
    { fix z::'v assume z: "z \<in> ?xs"
      then obtain u where u: "\<I> z = u" "fv u = {}" using \<I> by auto
      hence "(\<I> \<circ>\<^sub>s \<delta>' \<circ>\<^sub>s \<I>) z = u" by (simp add: subst_compose subst_ground_ident)
      moreover have "z \<notin> subst_domain \<delta>'" using d1 z by auto
      hence "\<delta>' z = Var z" by (simp add: subst_domain_def)
      hence "(\<delta>' \<circ>\<^sub>s \<I>) z = u" using u(1) by (simp add: subst_compose)
      ultimately have "(\<I> \<circ>\<^sub>s \<delta>' \<circ>\<^sub>s \<I>) z = (\<delta>' \<circ>\<^sub>s \<I>) z" by metis
    } moreover {
      fix z::'v assume "z \<in> ?ys"
      hence "z \<notin> subst_domain \<I>" using \<I>(2) by auto
      hence "(\<I> \<circ>\<^sub>s \<delta>' \<circ>\<^sub>s \<I>) z = (\<delta>' \<circ>\<^sub>s \<I>) z" by (simp add: subst_compose subst_domain_def)
    } moreover {
      fix z::'v assume "z \<notin> ?xs" "z \<notin> ?ys"
      hence "\<I> z = Var z" "\<delta>' z = Var z" using \<I>(2) d1 by blast+
      hence "(\<I> \<circ>\<^sub>s \<delta>' \<circ>\<^sub>s \<I>) z = (\<delta>' \<circ>\<^sub>s \<I>) z" by (simp add: subst_compose)
    } ultimately show ?thesis by auto
  qed

  from d2 d3 have "Unifier (\<delta>' \<circ>\<^sub>s \<I>) (s \<cdot> \<I>) (t \<cdot> \<I>)" by (metis subst_subst_compose) 
  thus ?thesis by metis
qed

context
begin
private lemma sat_ineq_subterm_inj_subst_aux:
  fixes \<I>::"('f,'v) subst"
  assumes "Unifier \<sigma> (s \<cdot> \<I>) (t \<cdot> \<I>)" "ground (subst_range \<I>)"
          "(fv s \<union> fv t) - X \<subseteq> subst_domain \<I>" "subst_domain \<I> \<inter> X = {}"
  shows "\<exists>\<delta>::('f,'v) subst. subst_domain \<delta> = X \<and> ground (subst_range \<delta>) \<and> s \<cdot> \<delta> \<cdot> \<I> = t \<cdot> \<delta> \<cdot> \<I>"
proof -
  have "\<exists>\<sigma>. Unifier \<sigma> (s \<cdot> \<I>) (t \<cdot> \<I>) \<and> interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>"
  proof -
    obtain \<I>'::"('f,'v) subst" where *: "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>'"
      using interpretation_subst_exists by metis
    hence "Unifier (\<sigma> \<circ>\<^sub>s \<I>') (s \<cdot> \<I>) (t \<cdot> \<I>)" using assms(1) by simp
    thus ?thesis using * interpretation_comp by blast
  qed
  then obtain \<sigma>' where \<sigma>': "Unifier \<sigma>' (s \<cdot> \<I>) (t \<cdot> \<I>)" "interpretation\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>'" by moura
  
  define \<sigma>'' where "\<sigma>'' = rm_vars (UNIV - X) \<sigma>'"
  
  have *: "fv (s \<cdot> \<I>) \<subseteq> X" "fv (t \<cdot> \<I>) \<subseteq> X"
    using assms(2,3) subst_fv_unfold_ground_img[of \<I>]
    unfolding range_vars_alt_def
    by (simp_all add: Diff_subset_conv Un_commute)
  hence **: "subst_domain \<sigma>'' = X" "ground (subst_range \<sigma>'')"
    using rm_vars_img_subset[of "UNIV - X" \<sigma>'] rm_vars_dom[of "UNIV - X" \<sigma>'] \<sigma>'(2)
    unfolding \<sigma>''_def by auto
  hence "\<And>t. t \<cdot> \<I> \<cdot> \<sigma>'' = t \<cdot> \<sigma>'' \<cdot> \<I>"
    using subst_eq_if_disjoint_vars_ground[OF _ _ assms(2)] assms(4) by blast
  moreover have "Unifier \<sigma>'' (s \<cdot> \<I>) (t \<cdot> \<I>)"
    using Unifier_dom_restrict[OF \<sigma>'(1)] \<sigma>''_def * by blast
  ultimately show ?thesis using ** by auto
qed

text \<open>
  The "inequality lemma": This lemma gives sufficient syntactic conditions for finding substitutions
  \<open>\<theta>\<close> under which terms \<open>s\<close> and \<open>t\<close> are not unifiable.

  This is useful later when establishing the typing results since we there want to find well-typed
  solutions to inequality constraints / "negative checks" constraints, and this lemma gives
  conditions for protocols under which such constraints are well-typed satisfiable if satisfiable.
\<close>
lemma sat_ineq_subterm_inj_subst:
  fixes \<theta> \<I> \<delta>::"('f,'v) subst"
  assumes \<theta>: "subterm_inj_on \<theta> (subst_domain \<theta>)"
             "ground (subst_range \<theta>)"
             "subst_domain \<theta> \<inter> X = {}"
             "subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>) \<inter> (subterms s \<union> subterms t) = {}"
             "(fv s \<union> fv t) - subst_domain \<theta> \<subseteq> X"
  and tfr: "(\<forall>x \<in> (fv s \<union> fv t) - X. \<exists>c. \<theta> x = Fun c []) \<or>
            (\<forall>f U. Fun f U \<in> subterms s \<union> subterms t \<longrightarrow> U = [] \<or> (\<exists>u \<in> set U. u \<notin> Var ` X))"
  and \<I>: "\<forall>\<delta>::('f,'v) subst. subst_domain \<delta> = X \<and> ground (subst_range \<delta>) \<longrightarrow> s \<cdot> \<delta> \<cdot> \<I> \<noteq> t \<cdot> \<delta> \<cdot> \<I>"
         "(fv s \<union> fv t) - X \<subseteq> subst_domain \<I>" "subst_domain \<I> \<inter> X = {}" "ground (subst_range \<I>)"
         "subst_domain \<I> = subst_domain \<theta>"
  and \<delta>: "subst_domain \<delta> = X" "ground (subst_range \<delta>)"
  shows "s \<cdot> \<delta> \<cdot> \<theta> \<noteq> t \<cdot> \<delta> \<cdot> \<theta>"
proof -
  have "\<forall>\<sigma>. \<not>Unifier \<sigma> (s \<cdot> \<I>) (t \<cdot> \<I>)"
    by (metis \<I>(1) sat_ineq_subterm_inj_subst_aux[OF _ \<I>(4,2,3)])
  hence "\<not>Unifier \<delta> (s \<cdot> \<theta>) (t \<cdot> \<theta>)"
    using inj_subst_unif_consts[OF \<theta>(1) _ \<theta>(4,2,3) \<I>(4,5)]
          inj_subst_unif_comp_terms[OF \<theta>(1,2,4,5) _ \<I>(4,5)]
          tfr
    by metis
  moreover have "subst_domain \<delta> \<inter> subst_domain \<theta> = {}" using \<theta>(2,3) \<delta>(1) by auto
  ultimately show ?thesis using \<delta> subst_eq_if_disjoint_vars_ground[OF _ \<theta>(2) \<delta>(2)] by metis
qed
end

lemma ineq_subterm_inj_cond_subst:
  assumes "X \<inter> range_vars \<theta> = {}"
  and "\<forall>f T. Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t S \<longrightarrow> T = [] \<or> (\<exists>u \<in> set T. u \<notin> Var`X)"
  shows "\<forall>f T. Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<longrightarrow> T = [] \<or> (\<exists>u \<in> set T. u \<notin> Var`X)"
proof (intro allI impI)
  let ?M = "\<lambda>S. subterms\<^sub>s\<^sub>e\<^sub>t S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
  let ?N = "\<lambda>S. subterms\<^sub>s\<^sub>e\<^sub>t (\<theta> ` (fv\<^sub>s\<^sub>e\<^sub>t S \<inter> subst_domain \<theta>))"

  fix f T assume "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (S \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
  hence 1: "Fun f T \<in> ?M S \<or> Fun f T \<in> ?N S"
    using subterms_subst[of _ \<theta>] by auto

  have 2: "Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (subst_range \<theta>) \<Longrightarrow> \<forall>u \<in> set T. u \<notin> Var`X"
    using fv_subset_subterms[of "Fun f T" "subst_range \<theta>"] assms(1)
    unfolding range_vars_alt_def by force

  have 3: "\<forall>x \<in> subst_domain \<theta>. \<theta> x \<notin> Var`X"
  proof
    fix x assume "x \<in> subst_domain \<theta>"
    hence "fv (\<theta> x) \<subseteq> range_vars \<theta>"
      using subst_dom_vars_in_subst subst_fv_imgI
      unfolding range_vars_alt_def by auto
    thus "\<theta> x \<notin> Var`X" using assms(1) by auto
  qed

  show "T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var`X)" using 1
  proof
    assume "Fun f T \<in> ?M S"
    then obtain u where u: "u \<in> subterms\<^sub>s\<^sub>e\<^sub>t S" "u \<cdot> \<theta> = Fun f T" by fastforce
    show ?thesis
    proof (cases u)
      case (Var x)
      hence "Fun f T \<in> subst_range \<theta>" using u(2) by (simp add: subst_domain_def)
      hence "\<forall>u \<in> set T. u \<notin> Var`X" using 2 by force
      thus ?thesis by auto
    next
      case (Fun g S)
      hence "S = [] \<or> (\<exists>u \<in> set S. u \<notin> Var`X)" using assms(2) u(1) by metis
      thus ?thesis
      proof
        assume "S = []" thus ?thesis using u(2) Fun by simp
      next
        assume "\<exists>u \<in> set S. u \<notin> Var`X"
        then obtain u' where u': "u' \<in> set S" "u' \<notin> Var`X" by moura
        hence "u' \<cdot> \<theta> \<in> set T" using u(2) Fun by auto
        thus ?thesis using u'(2) 3 by (cases u') force+
      qed
    qed
  next
    assume "Fun f T \<in> ?N S"
    thus ?thesis using 2 by force
  qed
qed


subsection \<open>Lemmata: Sufficient Conditions for Term Matching\<close>
text \<open>Injective substitutions from variables to variables are invertible\<close>
definition subst_var_inv where
  "subst_var_inv \<delta> X \<equiv> (\<lambda>x. if Var x \<in> \<delta> ` X then Var ((inv_into X \<delta>) (Var x)) else Var x)"

lemma inj_var_ran_subst_is_invertible:
  assumes \<delta>_inj_on_t: "inj_on \<delta> (fv t)"
    and \<delta>_var_on_t: "\<delta> ` fv t \<subseteq> range Var"
  shows "t = t \<cdot> \<delta> \<circ>\<^sub>s subst_var_inv \<delta> (fv t)"
proof -
  have "\<delta> x \<cdot> subst_var_inv \<delta> (fv t) = Var x" when x: "x \<in> fv t" for x
  proof -
    obtain y where y: "\<delta> x = Var y" using x \<delta>_var_on_t by auto
    hence "Var y \<in> \<delta> ` (fv t)" using x by simp
    thus ?thesis using y inv_into_f_eq[OF \<delta>_inj_on_t x y] unfolding subst_var_inv_def by simp
  qed
  thus ?thesis by (simp add: subst_compose_def trm_subst_ident'')
qed

text \<open>Sufficient conditions for matching unifiable terms\<close>
lemma inj_var_ran_unifiable_has_subst_match:
  assumes "t \<cdot> \<delta> = s \<cdot> \<delta>" "inj_on \<delta> (fv t)" "\<delta> ` fv t \<subseteq> range Var"
  shows "t = s \<cdot> \<delta> \<circ>\<^sub>s subst_var_inv \<delta> (fv t)"
using assms inj_var_ran_subst_is_invertible by fastforce

end
