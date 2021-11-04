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

(*  Title:      Typed_Model.thy
    Author:     Andreas Viktor Hess, DTU
*)

section \<open>The Typed Model\<close>
theory Typed_Model
imports Lazy_Intruder
begin

text \<open>Term types\<close>
type_synonym ('f,'v) term_type = "('f,'v) term"

text \<open>Constructors for term types\<close>
abbreviation (input) TAtom::"'v \<Rightarrow> ('f,'v) term_type" where
  "TAtom a \<equiv> Var a"

abbreviation (input) TComp::"['f, ('f,'v) term_type list] \<Rightarrow> ('f,'v) term_type" where
  "TComp f T \<equiv> Fun f T"


text \<open>
  The typed model extends the intruder model with a typing function \<open>\<Gamma>\<close> that assigns types to terms.
\<close>
locale typed_model = intruder_model arity public Ana
  for arity::"'fun \<Rightarrow> nat"
    and public::"'fun \<Rightarrow> bool"
    and Ana::"('fun,'var) term \<Rightarrow> (('fun,'var) term list \<times> ('fun,'var) term list)"
  +
  fixes \<Gamma>::"('fun,'var) term \<Rightarrow> ('fun,'atom::finite) term_type"
  assumes const_type: "\<And>c. arity c = 0 \<Longrightarrow> \<exists>a. \<forall>T. \<Gamma> (Fun c T) = TAtom a"
    and fun_type: "\<And>f T. arity f > 0 \<Longrightarrow> \<Gamma> (Fun f T) = TComp f (map \<Gamma> T)"
    and infinite_typed_consts: "\<And>a. infinite {c. \<Gamma> (Fun c []) = TAtom a \<and> public c}"
    and \<Gamma>_wf: "\<And>t f T. TComp f T \<sqsubseteq> \<Gamma> t \<Longrightarrow> arity f > 0"
              "\<And>x. wf\<^sub>t\<^sub>r\<^sub>m (\<Gamma> (Var x))"
    and no_private_funs[simp]: "\<And>f. arity f > 0 \<Longrightarrow> public f"
begin

subsection \<open>Definitions\<close>
text \<open>The set of atomic types\<close>
abbreviation "\<TT>\<^sub>a \<equiv> UNIV::('atom set)"

text \<open>Well-typed substitutions\<close>
definition wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t where
  "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma> \<equiv> (\<forall>v. \<Gamma> (Var v) = \<Gamma> (\<sigma> v))"

text \<open>The set of sub-message patterns (SMP)\<close>
inductive_set SMP::"('fun,'var) terms \<Rightarrow> ('fun,'var) terms" for M where
  MP[intro]: "t \<in> M \<Longrightarrow> t \<in> SMP M"
| Subterm[intro]: "\<lbrakk>t \<in> SMP M; t' \<sqsubseteq> t\<rbrakk> \<Longrightarrow> t' \<in> SMP M"
| Substitution[intro]: "\<lbrakk>t \<in> SMP M; wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>; wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)\<rbrakk> \<Longrightarrow> (t \<cdot> \<delta>) \<in> SMP M"
| Ana[intro]: "\<lbrakk>t \<in> SMP M; Ana t = (K,T); k \<in> set K\<rbrakk> \<Longrightarrow> k \<in> SMP M"

text \<open>
  Type-flaw resistance for sets:
  Unifiable sub-message patterns must have the same type (unless they are variables)
\<close>
definition tfr\<^sub>s\<^sub>e\<^sub>t where
  "tfr\<^sub>s\<^sub>e\<^sub>t M \<equiv> (\<forall>s \<in> SMP M - (Var`\<V>). \<forall>t \<in> SMP M - (Var`\<V>). (\<exists>\<delta>. Unifier \<delta> s t) \<longrightarrow> \<Gamma> s = \<Gamma> t)"

text \<open>
  Type-flaw resistance for strand steps:
  - The terms in a satisfiable equality step must have the same types
  - Inequality steps must satisfy the conditions of the "inequality lemma"\<close>
fun tfr\<^sub>s\<^sub>t\<^sub>p where
  "tfr\<^sub>s\<^sub>t\<^sub>p (Equality a t t') = ((\<exists>\<delta>. Unifier \<delta> t t') \<longrightarrow> \<Gamma> t = \<Gamma> t')"
| "tfr\<^sub>s\<^sub>t\<^sub>p (Inequality X F) = (
      (\<forall>x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X. \<exists>a. \<Gamma> (Var x) = TAtom a) \<or>
      (\<forall>f T. Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) \<longrightarrow> T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X)))"
| "tfr\<^sub>s\<^sub>t\<^sub>p _ = True"

text \<open>
  Type-flaw resistance for strands:
  - The set of terms in strands must be type-flaw resistant
  - The steps of strands must be type-flaw resistant
\<close>
definition tfr\<^sub>s\<^sub>t where
  "tfr\<^sub>s\<^sub>t S \<equiv> tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S) \<and> list_all tfr\<^sub>s\<^sub>t\<^sub>p S"


subsection \<open>Small Lemmata\<close>
lemma tfr\<^sub>s\<^sub>t\<^sub>p_list_all_alt_def:
  "list_all tfr\<^sub>s\<^sub>t\<^sub>p S \<longleftrightarrow>
    ((\<forall>a t t'. Equality a t t' \<in> set S \<and> (\<exists>\<delta>. Unifier \<delta> t t') \<longrightarrow> \<Gamma> t = \<Gamma> t') \<and>
    (\<forall>X F. Inequality X F \<in> set S \<longrightarrow> 
      (\<forall>x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X. \<exists>a. \<Gamma> (Var x) = TAtom a)
    \<or> (\<forall>f T. Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) \<longrightarrow> T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X))))"
  (is "?P S \<longleftrightarrow> ?Q S")
proof
  show "?P S \<Longrightarrow> ?Q S"
  proof (induction S)
    case (Cons x S) thus ?case by (cases x) auto
  qed simp

  show "?Q S \<Longrightarrow> ?P S"
  proof (induction S)
    case (Cons x S) thus ?case by (cases x) auto
  qed simp
qed


lemma \<Gamma>_wf': "wf\<^sub>t\<^sub>r\<^sub>m t \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m (\<Gamma> t)"
proof (induction t)
  case (Fun f T)
  hence *: "arity f = length T" "\<And>t. t \<in> set T \<Longrightarrow> wf\<^sub>t\<^sub>r\<^sub>m (\<Gamma> t)" unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto
  { assume "arity f = 0" hence ?case using const_type[of f] by auto }
  moreover
  { assume "arity f > 0" hence ?case using fun_type[of f] * by force }
  ultimately show ?case by auto 
qed (metis \<Gamma>_wf(2))

lemma fun_type_inv: assumes "\<Gamma> t = TComp f T" shows "arity f > 0" "public f"
using \<Gamma>_wf(1)[of f T t] assms by simp_all

lemma fun_type_inv_wf: assumes "\<Gamma> t = TComp f T" "wf\<^sub>t\<^sub>r\<^sub>m t" shows "arity f = length T"
using \<Gamma>_wf'[OF assms(2)] assms(1) unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto

lemma const_type_inv: "\<Gamma> (Fun c X) = TAtom a \<Longrightarrow> arity c = 0"
by (rule ccontr, simp add: fun_type)

lemma const_type_inv_wf: assumes "\<Gamma> (Fun c X) = TAtom a" and "wf\<^sub>t\<^sub>r\<^sub>m (Fun c X)" shows "X = []"
by (metis assms const_type_inv length_0_conv subtermeqI' wf\<^sub>t\<^sub>r\<^sub>m_def)

lemma const_type': "\<forall>c \<in> \<C>. \<exists>a \<in> \<TT>\<^sub>a. \<forall>X. \<Gamma> (Fun c X) = TAtom a" using const_type by simp
lemma fun_type': "\<forall>f \<in> \<Sigma>\<^sub>f. \<forall>X. \<Gamma> (Fun f X) = TComp f (map \<Gamma> X)" using fun_type by simp

lemma infinite_public_consts[simp]: "infinite {c. public c \<and> arity c = 0}"
proof -
  fix a::'atom
  define A where "A \<equiv> {c. \<Gamma> (Fun c []) = TAtom a \<and> public c}"
  define B where "B \<equiv> {c. public c \<and> arity c = 0}"

  have "arity c = 0" when c: "c \<in> A" for c
    using c const_type_inv unfolding A_def by blast
  hence "A \<subseteq> B" unfolding A_def B_def by blast
  hence "infinite B"
    using infinite_typed_consts[of a, unfolded A_def[symmetric]]
    by (metis infinite_super)
  thus ?thesis unfolding B_def by blast
qed

lemma infinite_fun_syms[simp]:
  "infinite {c. public c \<and> arity c > 0} \<Longrightarrow> infinite \<Sigma>\<^sub>f"
  "infinite \<C>" "infinite \<C>\<^sub>p\<^sub>u\<^sub>b" "infinite (UNIV::'fun set)"
by (metis \<Sigma>\<^sub>f_unfold finite_Collect_conjI,
    metis infinite_public_consts finite_Collect_conjI,
    use infinite_public_consts \<C>pub_unfold in \<open>force simp add: Collect_conj_eq\<close>,
    metis UNIV_I finite_subset subsetI infinite_public_consts(1))

lemma id_univ_proper_subset[simp]: "\<Sigma>\<^sub>f \<subset> UNIV" "(\<exists>f. arity f > 0) \<Longrightarrow> \<C> \<subset> UNIV"
by (metis finite.emptyI inf_top.right_neutral top.not_eq_extremum disjoint_fun_syms
          infinite_fun_syms(2) inf_commute)
   (metis top.not_eq_extremum UNIV_I const_arity_eq_zero less_irrefl)

lemma exists_fun_notin_funs_term: "\<exists>f::'fun. f \<notin> funs_term t"
by (metis UNIV_eq_I finite_fun_symbols infinite_fun_syms(4))

lemma exists_fun_notin_funs_terms:
  assumes "finite M" shows "\<exists>f::'fun. f \<notin> \<Union>(funs_term ` M)"
by (metis assms finite_fun_symbols infinite_fun_syms(4) ex_new_if_finite finite_UN)

lemma exists_notin_funs\<^sub>s\<^sub>t: "\<exists>f. f \<notin> funs\<^sub>s\<^sub>t (S::('fun,'var) strand)"
by (metis UNIV_eq_I finite_funs\<^sub>s\<^sub>t infinite_fun_syms(4))

lemma infinite_typed_consts': "infinite {c. \<Gamma> (Fun c []) = TAtom a \<and> public c \<and> arity c = 0}"
proof -
  { fix c assume "\<Gamma> (Fun c []) = TAtom a" "public c"
    hence "arity c = 0" using const_type[of c] fun_type[of c "[]"] by auto
  } hence "{c. \<Gamma> (Fun c []) = TAtom a \<and> public c \<and> arity c = 0} =
           {c. \<Gamma> (Fun c []) = TAtom a \<and> public c}"
    by auto
  thus "infinite {c. \<Gamma> (Fun c []) = TAtom a \<and> public c \<and> arity c = 0}"
    using infinite_typed_consts[of a] by metis
qed

lemma atypes_inhabited: "\<exists>c. \<Gamma> (Fun c []) = TAtom a \<and> wf\<^sub>t\<^sub>r\<^sub>m (Fun c []) \<and> public c \<and> arity c = 0"
proof -
  obtain c where "\<Gamma> (Fun c []) = TAtom a" "public c" "arity c = 0"
    using infinite_typed_consts'(1)[of a] not_finite_existsD by blast
  thus ?thesis using const_type_inv[OF \<open>\<Gamma> (Fun c []) = TAtom a\<close>] unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto
qed

lemma atype_ground_term_ex: "\<exists>t. fv t = {} \<and> \<Gamma> t = TAtom a \<and> wf\<^sub>t\<^sub>r\<^sub>m t"
using atypes_inhabited[of a] by force

lemma fun_type_id_eq: "\<Gamma> (Fun f X) = TComp g Y \<Longrightarrow> f = g"
by (metis const_type fun_type neq0_conv "term.inject"(2) "term.simps"(4))

lemma fun_type_length_eq: "\<Gamma> (Fun f X) = TComp g Y \<Longrightarrow> length X = length Y"
by (metis fun_type fun_type_id_eq fun_type_inv(1) length_map term.inject(2))

lemma type_ground_inhabited: "\<exists>t'. fv t' = {} \<and> \<Gamma> t = \<Gamma> t'"
proof -
  { fix \<tau>::"('fun, 'atom) term_type" assume "\<And>f T. Fun f T \<sqsubseteq> \<tau> \<Longrightarrow> 0 < arity f"
    hence "\<exists>t'. fv t' = {} \<and> \<tau> = \<Gamma> t'"
    proof (induction \<tau>)
      case (Fun f T)
      hence "arity f > 0" by auto
    
      from Fun.IH Fun.prems(1) have "\<exists>Y. map \<Gamma> Y = T \<and> (\<forall>x \<in> set Y. fv x = {})"
      proof (induction T)
        case (Cons x X)
        hence "\<And>g Y. Fun g Y \<sqsubseteq> Fun f X \<Longrightarrow> 0 < arity g" by auto
        hence "\<exists>Y. map \<Gamma> Y = X \<and> (\<forall>x\<in>set Y. fv x = {})" using Cons by auto
        moreover have "\<exists>t'. fv t' = {} \<and> x = \<Gamma> t'" using Cons by auto
        ultimately obtain y Y where
            "fv y = {}" "\<Gamma> y = x" "map \<Gamma> Y = X" "\<forall>x\<in>set Y. fv x = {}" 
          using Cons by moura
        hence "map \<Gamma> (y#Y) = x#X \<and> (\<forall>x\<in>set (y#Y). fv x = {})" by auto
        thus ?case by meson 
      qed simp
      then obtain Y where "map \<Gamma> Y = T" "\<forall>x \<in> set Y. fv x = {}" by metis
      hence "fv (Fun f Y) = {}" "\<Gamma> (Fun f Y) = TComp f T" using fun_type[OF \<open>arity f > 0\<close>] by auto
      thus ?case by (metis exI[of "\<lambda>t. fv t = {} \<and> \<Gamma> t = TComp f T" "Fun f Y"])
    qed (metis atype_ground_term_ex)
  }
  thus ?thesis by (metis \<Gamma>_wf(1))
qed

lemma type_wfttype_inhabited:
  assumes "\<And>f T. Fun f T \<sqsubseteq> \<tau> \<Longrightarrow> 0 < arity f" "wf\<^sub>t\<^sub>r\<^sub>m \<tau>"
  shows "\<exists>t. \<Gamma> t = \<tau> \<and> wf\<^sub>t\<^sub>r\<^sub>m t"
using assms
proof (induction \<tau>)
  case (Fun f Y)
  have IH: "\<exists>t. \<Gamma> t = y \<and> wf\<^sub>t\<^sub>r\<^sub>m t" when y: "y \<in> set Y " for y
  proof -
    have "wf\<^sub>t\<^sub>r\<^sub>m y"
      using Fun y unfolding wf\<^sub>t\<^sub>r\<^sub>m_def
      by (metis Fun_param_is_subterm term.le_less_trans) 
    moreover have "Fun g Z \<sqsubseteq> y \<Longrightarrow> 0 < arity g" for g Z
      using Fun y by auto
    ultimately show ?thesis using Fun.IH[OF y] by auto
  qed

  from Fun have "arity f = length Y" "arity f > 0" unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by force+
  moreover from IH have "\<exists>X. map \<Gamma> X = Y \<and> (\<forall>x \<in> set X. wf\<^sub>t\<^sub>r\<^sub>m x)"
    by (induct Y, simp_all, metis list.simps(9) set_ConsD)
  ultimately show ?case by (metis fun_type length_map wf_trmI)
qed (use atypes_inhabited wf\<^sub>t\<^sub>r\<^sub>m_def in blast)

lemma type_pgwt_inhabited: "wf\<^sub>t\<^sub>r\<^sub>m t \<Longrightarrow> \<exists>t'. \<Gamma> t = \<Gamma> t' \<and> public_ground_wf_term t'"
proof -
  assume "wf\<^sub>t\<^sub>r\<^sub>m t"
  { fix \<tau> assume "\<Gamma> t = \<tau>"
    hence "\<exists>t'. \<Gamma> t = \<Gamma> t' \<and> public_ground_wf_term t'" using \<open>wf\<^sub>t\<^sub>r\<^sub>m t\<close>
    proof (induction \<tau> arbitrary: t)
      case (Var a t)
      then obtain c where "\<Gamma> t = \<Gamma> (Fun c [])" "arity c = 0" "public c"
        using const_type_inv[of _ "[]" a] infinite_typed_consts(1)[of a]  not_finite_existsD
        by force
      thus ?case using PGWT[OF \<open>public c\<close>, of "[]"] by auto
    next
      case (Fun f Y t)
      have *: "arity f > 0" "public f" "arity f = length Y"
        using fun_type_inv[OF \<open>\<Gamma> t = TComp f Y\<close>] fun_type_inv_wf[OF \<open>\<Gamma> t = TComp f Y\<close> \<open>wf\<^sub>t\<^sub>r\<^sub>m t\<close>]
        by auto
      have "\<And>y. y \<in> set Y \<Longrightarrow> \<exists>t'. y = \<Gamma> t' \<and> public_ground_wf_term t'"
        using Fun.prems(1) Fun.IH \<Gamma>_wf(1)[of _ _ t] \<Gamma>_wf'[OF \<open>wf\<^sub>t\<^sub>r\<^sub>m t\<close>] type_wfttype_inhabited
        by (metis Fun_param_is_subterm term.order_trans wf_trm_subtermeq) 
      hence "\<exists>X. map \<Gamma> X = Y \<and> (\<forall>x \<in> set X. public_ground_wf_term x)"
        by (induct Y, simp_all, metis list.simps(9) set_ConsD)
      then obtain X where X: "map \<Gamma> X = Y" "\<And>x. x \<in> set X \<Longrightarrow> public_ground_wf_term x" by moura
      hence "arity f = length X" using *(3) by auto
      have "\<Gamma> t = \<Gamma> (Fun f X)" "public_ground_wf_term (Fun f X)"
        using fun_type[OF *(1), of X] Fun.prems(1) X(1) apply simp
        using PGWT[OF *(2) \<open>arity f = length X\<close> X(2)] by metis
      thus ?case by metis
    qed
  }
  thus ?thesis using \<open>wf\<^sub>t\<^sub>r\<^sub>m t\<close> by auto
qed

lemma pgwt_type_map: 
  assumes "public_ground_wf_term t"
  shows "\<Gamma> t = TAtom a \<Longrightarrow> \<exists>f. t = Fun f []" "\<Gamma> t = TComp g Y \<Longrightarrow> \<exists>X. t = Fun g X \<and> map \<Gamma> X = Y"
proof -
  let ?A = "\<Gamma> t = TAtom a \<longrightarrow> (\<exists>f. t = Fun f [])"
  let ?B = "\<Gamma> t = TComp g Y \<longrightarrow> (\<exists>X. t = Fun g X \<and> map \<Gamma> X = Y)"
  have "?A \<and> ?B"
  proof (cases "\<Gamma> t")
    case (Var a)
    obtain f X where "t = Fun f X" "arity f = length X"
      using pgwt_fun[OF assms(1)] pgwt_arity[OF assms(1)] by fastforce+
    thus ?thesis using const_type_inv \<open>\<Gamma> t = TAtom a\<close> by auto
  next
    case (Fun g Y)
    obtain f X where *: "t = Fun f X" using pgwt_fun[OF assms(1)] by force
    hence "f = g" "map \<Gamma> X = Y"
      using fun_type_id_eq \<open>\<Gamma> t = TComp g Y\<close> fun_type[OF fun_type_inv(1)[OF \<open>\<Gamma> t = TComp g Y\<close>]]
      by fastforce+
    thus ?thesis using *(1) \<open>\<Gamma> t = TComp g Y\<close> by auto 
  qed
  thus "\<Gamma> t = TAtom a \<Longrightarrow> \<exists>f. t = Fun f []" "\<Gamma> t = TComp g Y \<Longrightarrow> \<exists>X. t = Fun g X \<and> map \<Gamma> X = Y"
    by auto
qed 

lemma wt_subst_Var[simp]: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t Var" by (metis wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)

lemma wt_subst_trm: "(\<And>v. v \<in> fv t \<Longrightarrow> \<Gamma> (Var v) = \<Gamma> (\<theta> v)) \<Longrightarrow> \<Gamma> t = \<Gamma> (t \<cdot> \<theta>)"
proof (induction t)
  case (Fun f X)
  hence *: "\<And>x. x \<in> set X \<Longrightarrow> \<Gamma> x = \<Gamma> (x \<cdot> \<theta>)" by auto
  show ?case
  proof (cases "f \<in> \<Sigma>\<^sub>f")
    case True
    hence "\<forall>X. \<Gamma> (Fun f X) = TComp f (map \<Gamma> X)" using fun_type' by auto
    thus ?thesis using * by auto
  next
    case False
    hence "\<exists>a \<in> \<TT>\<^sub>a. \<forall>X. \<Gamma> (Fun f X) = TAtom a" using const_type' by auto
    thus ?thesis by auto
  qed
qed auto

lemma wt_subst_trm': "\<lbrakk>wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>; \<Gamma> s = \<Gamma> t\<rbrakk> \<Longrightarrow> \<Gamma> (s \<cdot> \<sigma>) = \<Gamma> (t \<cdot> \<sigma>)"
by (metis wt_subst_trm wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)

lemma wt_subst_trm'': "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma> \<Longrightarrow> \<Gamma> t = \<Gamma> (t \<cdot> \<sigma>)"
by (metis wt_subst_trm wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)

lemma wt_subst_compose:
  assumes "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" shows "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<theta> \<circ>\<^sub>s \<delta>)"
proof -
  have "\<And>v. \<Gamma> (\<theta> v) = \<Gamma> (\<theta> v \<cdot> \<delta>)" using wt_subst_trm \<open>wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>\<close> unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by metis
  moreover have "\<And>v. \<Gamma> (Var v) = \<Gamma> (\<theta> v)" using \<open>wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>\<close> unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by metis
  ultimately have "\<And>v. \<Gamma> (Var v) = \<Gamma> (\<theta> v \<cdot> \<delta>)" by metis
  thus ?thesis unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def subst_compose_def by metis
qed

lemma wt_subst_TAtom_Var_cases:
  assumes \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
  and x: "\<Gamma> (Var x) = TAtom a"
  shows "(\<exists>y. \<theta> x = Var y) \<or> (\<exists>c. \<theta> x = Fun c [])"
proof (cases "(\<exists>y. \<theta> x = Var y)")
  case False
  then obtain c T where c: "\<theta> x = Fun c T"
    by (cases "\<theta> x") simp_all
  hence "wf\<^sub>t\<^sub>r\<^sub>m (Fun c T)"
    using \<theta>(2) by fastforce
  hence "T = []"
    using const_type_inv_wf[of c T a] x c wt_subst_trm''[OF \<theta>(1), of "Var x"]
    by fastforce
  thus ?thesis
    using c by blast
qed simp

lemma wt_subst_TAtom_fv:
  assumes \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "\<forall>x. wf\<^sub>t\<^sub>r\<^sub>m (\<theta> x)"
  and "\<forall>x \<in> fv t - X. \<exists>a. \<Gamma> (Var x) = TAtom a"
  shows "\<forall>x \<in> fv (t \<cdot> \<theta>) - fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` X). \<exists>a. \<Gamma> (Var x) = TAtom a"
using assms(3)
proof (induction t)
  case (Var x) thus ?case
  proof (cases "x \<in> X")
    case False
    with Var obtain a where "\<Gamma> (Var x) = TAtom a" by moura
    hence *: "\<Gamma> (\<theta> x) = TAtom a" "wf\<^sub>t\<^sub>r\<^sub>m (\<theta> x)" using \<theta> unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by auto
    show ?thesis
    proof (cases "\<theta> x")
      case (Var y) thus ?thesis using * by auto
    next
      case (Fun f T)
      hence "T = []" using * const_type_inv[of f T a] unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto
      thus ?thesis using Fun by auto
    qed
  qed auto
qed fastforce

lemma wt_subst_TAtom_subterms_subst:
  assumes "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "\<forall>x \<in> fv t. \<exists>a. \<Gamma> (Var x) = TAtom a" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (\<theta> ` fv t)"
  shows "subterms (t \<cdot> \<theta>) = subterms t \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
using assms(2,3)
proof (induction t)
  case (Var x)
  obtain a where a: "\<Gamma> (Var x) = TAtom a" using Var.prems(1) by moura
  hence "\<Gamma> (\<theta> x) = TAtom a" using wt_subst_trm''[OF assms(1), of "Var x"] by simp
  hence "(\<exists>y. \<theta> x = Var y) \<or> (\<exists>c. \<theta> x = Fun c [])"
    using const_type_inv_wf Var.prems(2) by (cases "\<theta> x") auto
  thus ?case by auto
next
  case (Fun f T)
  have "subterms (t \<cdot> \<theta>) = subterms t \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>" when "t \<in> set T" for t
    using that Fun.prems(1,2) Fun.IH[OF that]
    by auto
  thus ?case by auto
qed

lemma wt_subst_TAtom_subterms_set_subst: 
  assumes "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "\<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M. \<exists>a. \<Gamma> (Var x) = TAtom a" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (\<theta> ` fv\<^sub>s\<^sub>e\<^sub>t M)"
  shows "subterms\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) = subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
proof
  show "subterms\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>) \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
  proof
    fix t assume "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
    then obtain s where s: "s \<in> M" "t \<in> subterms (s \<cdot> \<theta>)" by auto
    thus "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
      using assms(2,3) wt_subst_TAtom_subterms_subst[OF assms(1), of s]
      by auto
  qed

  show "subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta> \<subseteq> subterms\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
  proof
    fix t assume "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
    then obtain s where s: "s \<in> M" "t \<in> subterms s \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>" by auto
    thus "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>)"
      using assms(2,3) wt_subst_TAtom_subterms_subst[OF assms(1), of s]
      by auto
  qed
qed

lemma wt_subst_subst_upd:
  assumes "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>"
    and "\<Gamma> (Var x) = \<Gamma> t"
  shows "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<theta>(x := t))"
using assms unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def
by (metis fun_upd_other fun_upd_same)

lemma wt_subst_const_fv_type_eq:
  assumes "\<forall>x \<in> fv t. \<exists>a. \<Gamma> (Var x) = TAtom a"
    and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
  shows "\<forall>x \<in> fv (t \<cdot> \<delta>). \<exists>y \<in> fv t. \<Gamma> (Var x) = \<Gamma> (Var y)"
using assms(1)
proof (induction t)
  case (Var x)
  then obtain a where a: "\<Gamma> (Var x) = TAtom a" by moura
  show ?case
  proof (cases "\<delta> x")
    case (Fun f T)
    hence "wf\<^sub>t\<^sub>r\<^sub>m (Fun f T)" "\<Gamma> (Fun f T) = TAtom a"
      using a wt_subst_trm''[OF \<delta>(1), of "Var x"] \<delta>(2) by fastforce+
    thus ?thesis using const_type_inv_wf Fun by fastforce
  qed (use a wt_subst_trm''[OF \<delta>(1), of "Var x"] in simp)
qed fastforce

lemma TComp_term_cases:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m t" "\<Gamma> t = TComp f T"
  shows "(\<exists>v. t = Var v) \<or> (\<exists>T'. t = Fun f T' \<and> T = map \<Gamma> T' \<and> T' \<noteq> [])"
proof (cases "\<exists>v. t = Var v")
  case False
  then obtain T' where T': "t = Fun f T'" "T = map \<Gamma> T'"
    using assms fun_type[OF fun_type_inv(1)[OF assms(2)]] fun_type_id_eq
    by (cases t) force+
  thus ?thesis using assms fun_type_inv(1) fun_type_inv_wf by fastforce
qed metis

lemma TAtom_term_cases:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m t" "\<Gamma> t = TAtom \<tau>"
  shows "(\<exists>v. t = Var v) \<or> (\<exists>f. t = Fun f [])"
using assms const_type_inv unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by (cases t) auto

lemma subtermeq_imp_subtermtypeeq:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m t" "s \<sqsubseteq> t"
  shows "\<Gamma> s \<sqsubseteq> \<Gamma> t"
using assms(2,1)
proof (induction t)
  case (Fun f T) thus ?case
  proof (cases "s = Fun f T")
    case False
    then obtain x where x: "x \<in> set T" "s \<sqsubseteq> x" using Fun.prems(1) by auto
    hence "wf\<^sub>t\<^sub>r\<^sub>m x" using wf_trm_subtermeq[OF Fun.prems(2)] Fun_param_is_subterm[of _ T f] by auto
    hence "\<Gamma> s \<sqsubseteq> \<Gamma> x" using Fun.IH[OF x] by simp
    moreover have "arity f > 0" using x fun_type_inv_wf Fun.prems
      by (metis length_pos_if_in_set term.order_refl wf\<^sub>t\<^sub>r\<^sub>m_def)
    ultimately show ?thesis using x Fun.prems fun_type[of f T] by auto
  qed simp
qed simp

lemma subterm_funs_term_in_type:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m t" "Fun f T \<sqsubseteq> t" "\<Gamma> (Fun f T) = TComp f (map \<Gamma> T)"
  shows "f \<in> funs_term (\<Gamma> t)"
using assms(2,1,3)
proof (induction t)
  case (Fun f' T')
  hence [simp]: "wf\<^sub>t\<^sub>r\<^sub>m (Fun f T)" by (metis wf_trm_subtermeq)
  { fix a assume \<tau>: "\<Gamma> (Fun f' T') = TAtom a"
    hence "Fun f T = Fun f' T'" using Fun TAtom_term_cases subtermeq_Var_const by metis
    hence False using Fun.prems(3) \<tau> by simp
  }
  moreover
  { fix g S assume \<tau>: "\<Gamma> (Fun f' T') = TComp g S"
    hence "g = f'" "S = map \<Gamma> T'"
      using Fun.prems(2) fun_type_id_eq[OF \<tau>] fun_type[OF fun_type_inv(1)[OF \<tau>]]
      by auto
    hence \<tau>': "\<Gamma> (Fun f' T') = TComp f' (map \<Gamma> T')" using \<tau> by auto
    hence "g \<in> funs_term (\<Gamma> (Fun f' T'))" using \<tau> by auto
    moreover {
      assume "Fun f T \<noteq> Fun f' T'"
      then obtain x where "x \<in> set T'" "Fun f T \<sqsubseteq> x" using Fun.prems(1) by auto
      hence "f \<in> funs_term (\<Gamma> x)"
        using Fun.IH[OF _ _ _ Fun.prems(3), of x] wf_trm_subtermeq[OF \<open>wf\<^sub>t\<^sub>r\<^sub>m (Fun f' T')\<close>, of x]
        by force
      moreover have "\<Gamma> x \<in> set (map \<Gamma> T')" using \<tau>' \<open>x \<in> set T'\<close> by auto
      ultimately have "f \<in> funs_term (\<Gamma> (Fun f' T'))" using \<tau>' by auto
    }
    ultimately have ?case by (cases "Fun f T = Fun f' T'") (auto simp add: \<open>g = f'\<close>)
  }
  ultimately show ?case by (cases "\<Gamma> (Fun f' T')") auto
qed simp

lemma wt_subst_fv_termtype_subterm:
  assumes "x \<in> fv (\<theta> y)"
    and "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>"
    and "wf\<^sub>t\<^sub>r\<^sub>m (\<theta> y)"
  shows "\<Gamma> (Var x) \<sqsubseteq> \<Gamma> (Var y)"
using subtermeq_imp_subtermtypeeq[OF assms(3) var_is_subterm[OF assms(1)]]
      wt_subst_trm''[OF assms(2), of "Var y"]
by auto

lemma wt_subst_fv\<^sub>s\<^sub>e\<^sub>t_termtype_subterm:
  assumes "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (\<theta> ` Y)"
    and "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>"
    and "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
  shows "\<exists>y \<in> Y. \<Gamma> (Var x) \<sqsubseteq> \<Gamma> (Var y)"
using wt_subst_fv_termtype_subterm[OF _ assms(2), of x] assms(1,3)
by fastforce

lemma funs_term_type_iff:
  assumes t: "wf\<^sub>t\<^sub>r\<^sub>m t"
    and f: "arity f > 0"
  shows "f \<in> funs_term (\<Gamma> t) \<longleftrightarrow> (f \<in> funs_term t \<or> (\<exists>x \<in> fv t. f \<in> funs_term (\<Gamma> (Var x))))"
    (is "?P t \<longleftrightarrow> ?Q t")
using t
proof (induction t)
  case (Fun g T)
  hence IH: "?P s \<longleftrightarrow> ?Q s" when "s \<in> set T" for s
    using that wf_trm_subterm[OF _ Fun_param_is_subterm]
    by blast
  have 0: "arity g = length T" using Fun.prems unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto
  show ?case
  proof (cases "f = g")
    case True thus ?thesis using fun_type[OF f] by simp
  next
    case False
    have "?P (Fun g T) \<longleftrightarrow> (\<exists>s \<in> set T. ?P s)"
    proof
      assume *: "?P (Fun g T)"
      hence "\<Gamma> (Fun g T) = TComp g (map \<Gamma> T)"
        using const_type[of g] fun_type[of g] by force
      thus "\<exists>s \<in> set T. ?P s" using False * by force
    next
      assume *: "\<exists>s \<in> set T. ?P s"
      hence "\<Gamma> (Fun g T) = TComp g (map \<Gamma> T)"
        using 0 const_type[of g] fun_type[of g] by force
      thus "?P (Fun g T)" using False * by force
    qed
    thus ?thesis using False f IH by auto
  qed
qed simp

lemma funs_term_type_iff':
  assumes M: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M"
    and f: "arity f > 0"
  shows "f \<in> \<Union>(funs_term ` \<Gamma> ` M) \<longleftrightarrow>
        (f \<in> \<Union>(funs_term ` M) \<or> (\<exists>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M. f \<in> funs_term (\<Gamma> (Var x))))" (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A
  then obtain t where "t \<in> M" "wf\<^sub>t\<^sub>r\<^sub>m t" "f \<in> funs_term (\<Gamma> t)" using M by moura
  thus ?B using funs_term_type_iff[OF _ f, of t] by auto
next
  assume ?B
  then obtain t where "t \<in> M" "wf\<^sub>t\<^sub>r\<^sub>m t" "f \<in> funs_term t \<or> (\<exists>x \<in> fv t. f \<in> funs_term (\<Gamma> (Var x)))"
    using M by auto
  thus ?A using funs_term_type_iff[OF _ f, of t] by blast
qed

lemma Ana_subterm_type:
  assumes "Ana t = (K,M)"
    and "wf\<^sub>t\<^sub>r\<^sub>m t"
    and "m \<in> set M"
  shows "\<Gamma> m \<sqsubseteq> \<Gamma> t"
proof -
  have "m \<sqsubseteq> t" using Ana_subterm[OF assms(1)] assms(3) by auto
  thus ?thesis using subtermeq_imp_subtermtypeeq[OF assms(2)] by simp
qed

lemma wf_trm_TAtom_subterms:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m t" "\<Gamma> t = TAtom \<tau>"
  shows "subterms t = {t}"
using assms const_type_inv unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by (cases t) force+

lemma wf_trm_TComp_subterm:
  assumes "wf\<^sub>t\<^sub>r\<^sub>m s" "t \<sqsubset> s"
  obtains f T where "\<Gamma> s = TComp f T"
proof (cases s)
  case (Var x) thus ?thesis using \<open>t \<sqsubset> s\<close> by simp
next
  case (Fun g S)
  hence "length S > 0" using assms Fun_subterm_inside_params[of t g S] by auto
  hence "arity g > 0" by (metis \<open>wf\<^sub>t\<^sub>r\<^sub>m s\<close> \<open>s = Fun g S\<close> term.order_refl wf\<^sub>t\<^sub>r\<^sub>m_def) 
  thus ?thesis using fun_type \<open>s = Fun g S\<close> that by auto
qed

lemma SMP_empty[simp]: "SMP {} = {}"
proof (rule ccontr)
  assume "SMP {} \<noteq> {}"
  then obtain t where "t \<in> SMP {}" by auto
  thus False by (induct t rule: SMP.induct) auto
qed

lemma SMP_I:
  assumes "s \<in> M" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "t \<sqsubseteq> s \<cdot> \<delta>" "\<And>v. wf\<^sub>t\<^sub>r\<^sub>m (\<delta> v)"
  shows "t \<in> SMP M"
using SMP.Substitution[OF SMP.MP[OF assms(1)] assms(2)] SMP.Subterm[of "s \<cdot> \<delta>" M t] assms(3,4)
by (cases "t = s \<cdot> \<delta>") simp_all

lemma SMP_wf_trm:
  assumes "t \<in> SMP M" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M"
  shows "wf\<^sub>t\<^sub>r\<^sub>m t"
using assms(1)
by (induct t rule: SMP.induct)
   (use assms(2) in blast,
    use wf_trm_subtermeq in blast,
    use wf_trm_subst in blast,
    use Ana_keys_wf' in blast)

lemma SMP_ikI[intro]: "t \<in> ik\<^sub>s\<^sub>t S \<Longrightarrow> t \<in> SMP (trms\<^sub>s\<^sub>t S)" by force

lemma MP_setI[intro]: "x \<in> set S \<Longrightarrow> trms\<^sub>s\<^sub>t\<^sub>p x \<subseteq> trms\<^sub>s\<^sub>t S" by force

lemma SMP_setI[intro]: "x \<in> set S \<Longrightarrow> trms\<^sub>s\<^sub>t\<^sub>p x \<subseteq> SMP (trms\<^sub>s\<^sub>t S)" by force

lemma SMP_subset_I:
  assumes M: "\<forall>t \<in> M. \<exists>s \<delta>. s \<in> N \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t = s \<cdot> \<delta>"
  shows "SMP M \<subseteq> SMP N"
proof
  fix t show "t \<in> SMP M \<Longrightarrow> t \<in> SMP N"
  proof (induction t rule: SMP.induct)
    case (MP t)
    then obtain s \<delta> where s: "s \<in> N" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)" "t = s \<cdot> \<delta>"
      using M by moura
    show ?case using SMP_I[OF s(1,2), of "s \<cdot> \<delta>"] s(3,4) wf_trm_subst_range_iff by fast
  qed (auto intro!: SMP.Substitution[of _ N])
qed

lemma SMP_union: "SMP (A \<union> B) = SMP A \<union> SMP B"
proof
  show "SMP (A \<union> B) \<subseteq> SMP A \<union> SMP B"
  proof
    fix t assume "t \<in> SMP (A \<union> B)"
    thus "t \<in> SMP A \<union> SMP B" by (induct rule: SMP.induct) blast+
  qed

  { fix t assume "t \<in> SMP A" hence "t \<in> SMP (A \<union> B)" by (induct rule: SMP.induct) blast+ }
  moreover { fix t assume "t \<in> SMP B" hence "t \<in> SMP (A \<union> B)" by (induct rule: SMP.induct) blast+ }
  ultimately show "SMP A \<union> SMP B \<subseteq> SMP (A \<union> B)" by blast
qed

lemma SMP_append[simp]: "SMP (trms\<^sub>s\<^sub>t (S@S')) = SMP (trms\<^sub>s\<^sub>t S) \<union> SMP (trms\<^sub>s\<^sub>t S')" (is "?A = ?B")
using SMP_union by simp

lemma SMP_mono: "A \<subseteq> B \<Longrightarrow> SMP A \<subseteq> SMP B"
proof -
  assume "A \<subseteq> B"
  then obtain C where "B = A \<union> C" by moura
  thus "SMP A \<subseteq> SMP B" by (simp add: SMP_union)
qed

lemma SMP_Union: "SMP (\<Union>m \<in> M. f m) = (\<Union>m \<in> M. SMP (f m))"
proof
  show "SMP (\<Union>m\<in>M. f m) \<subseteq> (\<Union>m\<in>M. SMP (f m))"
  proof
    fix t assume "t \<in> SMP (\<Union>m\<in>M. f m)"
    thus "t \<in> (\<Union>m\<in>M. SMP (f m))" by (induct t rule: SMP.induct) force+
  qed
  show "(\<Union>m\<in>M. SMP (f m)) \<subseteq> SMP (\<Union>m\<in>M. f m)"
  proof
    fix t assume "t \<in> (\<Union>m\<in>M. SMP (f m))"
    then obtain m where "m \<in> M" "t \<in> SMP (f m)" by moura
    thus "t \<in> SMP (\<Union>m\<in>M. f m)" using SMP_mono[of "f m" "\<Union>m\<in>M. f m"] by auto
  qed
qed

lemma SMP_singleton_ex:
  "t \<in> SMP M \<Longrightarrow> (\<exists>m \<in> M. t \<in> SMP {m})"
  "m \<in> M \<Longrightarrow> t \<in> SMP {m} \<Longrightarrow> t \<in> SMP M"
using SMP_Union[of "\<lambda>t. {t}" M] by auto

lemma SMP_Cons: "SMP (trms\<^sub>s\<^sub>t (x#S)) = SMP (trms\<^sub>s\<^sub>t [x]) \<union> SMP (trms\<^sub>s\<^sub>t S)"
using SMP_append[of "[x]" S] by auto

lemma SMP_Nil[simp]: "SMP (trms\<^sub>s\<^sub>t []) = {}" 
proof -
  { fix t assume "t \<in> SMP (trms\<^sub>s\<^sub>t [])" hence False by induct auto }
  thus ?thesis by blast
qed

lemma SMP_subset_union_eq: assumes "M \<subseteq> SMP N" shows "SMP N = SMP (M \<union> N)"
proof -
  { fix t assume "t \<in> SMP (M \<union> N)" hence "t \<in> SMP N"
      using assms by (induction rule: SMP.induct) blast+
  }
  thus ?thesis using SMP_union by auto
qed

lemma SMP_subterms_subset: "subterms\<^sub>s\<^sub>e\<^sub>t M \<subseteq> SMP M"
proof
  fix t assume "t \<in> subterms\<^sub>s\<^sub>e\<^sub>t M"
  then obtain m where "m \<in> M" "t \<sqsubseteq> m" by auto
  thus "t \<in> SMP M" using SMP_I[of _ _ Var] by auto
qed

lemma SMP_SMP_subset: "N \<subseteq> SMP M \<Longrightarrow> SMP N \<subseteq> SMP M"
by (metis SMP_mono SMP_subset_union_eq Un_commute Un_upper2)

lemma wt_subst_rm_vars: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<Longrightarrow> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (rm_vars X \<delta>)"
using rm_vars_dom unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by auto

lemma wt_subst_SMP_subset:
  assumes "trms\<^sub>s\<^sub>t S \<subseteq> SMP S'" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
  shows "trms\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>) \<subseteq> SMP S'"
proof
  fix t assume *: "t \<in> trms\<^sub>s\<^sub>t (S \<cdot>\<^sub>s\<^sub>t \<delta>)"
  show "t \<in> SMP S'" using trm_strand_subst_cong(2)[OF *]
  proof
    assume "\<exists>t'. t = t' \<cdot> \<delta> \<and> t' \<in> trms\<^sub>s\<^sub>t S"
    thus "t \<in> SMP S'" using assms SMP.Substitution by auto
  next
    assume "\<exists>X F. Inequality X F \<in> set S \<and> (\<exists>t'\<in>trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F. t = t' \<cdot> rm_vars (set X) \<delta>)"
    then obtain X F t' where **:
        "Inequality X F \<in> set S" "t'\<in>trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F" "t = t' \<cdot> rm_vars (set X) \<delta>"
      by force
    then obtain s where s: "s \<in> trms\<^sub>s\<^sub>t\<^sub>p (Inequality X F)" "t = s \<cdot> rm_vars (set X) \<delta>" by moura
    hence "s \<in> SMP (trms\<^sub>s\<^sub>t S)" using **(1) by force
    hence "t \<in> SMP (trms\<^sub>s\<^sub>t S)"
      using SMP.Substitution[OF _ wt_subst_rm_vars[OF assms(2)] wf_trms_subst_rm_vars'[OF assms(3)]]
      unfolding s(2) by blast
    thus "t \<in> SMP S'" by (metis SMP_union SMP_subset_union_eq UnCI assms(1))
  qed
qed

lemma MP_subset_SMP: "\<Union>(trms\<^sub>s\<^sub>t\<^sub>p ` set S) \<subseteq> SMP (trms\<^sub>s\<^sub>t S)" "trms\<^sub>s\<^sub>t S \<subseteq> SMP (trms\<^sub>s\<^sub>t S)" "M \<subseteq> SMP M"
by auto

lemma SMP_fun_map_snd_subset: "SMP (trms\<^sub>s\<^sub>t (map Send X)) \<subseteq> SMP (trms\<^sub>s\<^sub>t [Send (Fun f X)])"
proof
  fix t assume "t \<in> SMP (trms\<^sub>s\<^sub>t (map Send X))" thus "t \<in> SMP (trms\<^sub>s\<^sub>t [Send (Fun f X)])"
  proof (induction t rule: SMP.induct)
    case (MP t)
    hence "t \<in> set X" by auto
    hence "t \<sqsubset> Fun f X" by (metis subtermI')
    thus ?case using SMP.Subterm[of "Fun f X" "trms\<^sub>s\<^sub>t [Send (Fun f X)]" t] using SMP.MP by auto
  qed blast+
qed

lemma SMP_wt_subst_subset:
  assumes "t \<in> SMP (M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<I>)" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<I>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<I>)"
  shows "t \<in> SMP M"
using assms wf_trm_subst_range_iff[of \<I>] by (induct t rule: SMP.induct) blast+

lemma SMP_wt_instances_subset:
  assumes "\<forall>t \<in> M. \<exists>s \<in> N. \<exists>\<delta>. t = s \<cdot> \<delta> \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
    and "t \<in> SMP M"
  shows "t \<in> SMP N"
proof -
  obtain m where m: "m \<in> M" "t \<in> SMP {m}" using SMP_singleton_ex(1)[OF assms(2)] by blast
  then obtain n \<delta> where n: "n \<in> N" "m = n \<cdot> \<delta>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
    using assms(1) by fast

  have "t \<in> SMP (N \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>)" using n(1,2) SMP_singleton_ex(2)[of m "N \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>", OF _ m(2)] by fast
  thus ?thesis using SMP_wt_subst_subset[OF _ n(3,4)] by blast
qed

lemma SMP_consts:
  assumes "\<forall>t \<in> M. \<exists>c. t = Fun c []"
    and "\<forall>t \<in> M. Ana t = ([], [])"
  shows "SMP M = M"
proof
  show "SMP M \<subseteq> M"
  proof
    fix t show "t \<in> SMP M \<Longrightarrow> t \<in> M"
      apply (induction t rule: SMP.induct)
      by (use assms in auto)
  qed
qed auto

lemma SMP_subterms_eq:
  "SMP (subterms\<^sub>s\<^sub>e\<^sub>t M) = SMP M"
proof
  show "SMP M \<subseteq> SMP (subterms\<^sub>s\<^sub>e\<^sub>t M)" using SMP_mono[of M "subterms\<^sub>s\<^sub>e\<^sub>t M"] by blast
  show "SMP (subterms\<^sub>s\<^sub>e\<^sub>t M) \<subseteq> SMP M"
  proof
    fix t show "t \<in> SMP (subterms\<^sub>s\<^sub>e\<^sub>t M) \<Longrightarrow> t \<in> SMP M" by (induction t rule: SMP.induct) blast+
  qed
qed

lemma SMP_funs_term:
  assumes t: "t \<in> SMP M" "f \<in> funs_term t \<or> (\<exists>x \<in> fv t. f \<in> funs_term (\<Gamma> (Var x)))"
    and f: "arity f > 0"
    and M: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M"
    and Ana_f: "\<And>s K T. Ana s = (K,T) \<Longrightarrow> f \<in> \<Union>(funs_term ` set K) \<Longrightarrow> f \<in> funs_term s"
  shows "f \<in> \<Union>(funs_term ` M) \<or> (\<exists>x \<in> fv\<^sub>s\<^sub>e\<^sub>t M. f \<in> funs_term (\<Gamma> (Var x)))"
using t
proof (induction t rule: SMP.induct)
  case (Subterm t t')
  thus ?case by (metis UN_I vars_iff_subtermeq funs_term_subterms_eq(1) term.order_trans)
next
  case (Substitution t \<delta>)
  show ?case
    using M SMP_wf_trm[OF Substitution.hyps(1)] wf_trm_subst[of \<delta> t, OF Substitution.hyps(3)]
          funs_term_type_iff[OF _ f] wt_subst_trm''[OF Substitution.hyps(2), of t]
          Substitution.prems Substitution.IH
    by metis
next
  case (Ana t K T t')
  thus ?case
    using Ana_f[OF Ana.hyps(2)] Ana_keys_fv[OF Ana.hyps(2)]
    by fastforce
qed auto

lemma id_type_eq:
  assumes "\<Gamma> (Fun f X) = \<Gamma> (Fun g Y)"
  shows "f \<in> \<C> \<Longrightarrow> g \<in> \<C>" "f \<in> \<Sigma>\<^sub>f \<Longrightarrow> g \<in> \<Sigma>\<^sub>f"
using assms const_type' fun_type' id_union_univ(1)
by (metis UNIV_I UnE "term.distinct"(1))+

lemma fun_type_arg_cong:
  assumes "f \<in> \<Sigma>\<^sub>f" "g \<in> \<Sigma>\<^sub>f" "\<Gamma> (Fun f (x#X)) = \<Gamma> (Fun g (y#Y))"
  shows "\<Gamma> x = \<Gamma> y" "\<Gamma> (Fun f X) = \<Gamma> (Fun g Y)"
using assms fun_type' by auto

lemma fun_type_arg_cong':
  assumes "f \<in> \<Sigma>\<^sub>f" "g \<in> \<Sigma>\<^sub>f" "\<Gamma> (Fun f (X@x#X')) = \<Gamma> (Fun g (Y@y#Y'))" "length X = length Y"
  shows "\<Gamma> x = \<Gamma> y"
using assms
proof (induction X arbitrary: Y)
  case Nil thus ?case using fun_type_arg_cong(1)[of f g x X' y Y'] by auto
next
  case (Cons x' X Y'')
  then obtain y' Y where "Y'' = y'#Y" by (metis length_Suc_conv)
  hence "\<Gamma> (Fun f (X@x#X')) = \<Gamma> (Fun g (Y@y#Y'))" "length X = length Y"
    using Cons.prems(3,4) fun_type_arg_cong(2)[OF Cons.prems(1,2), of x' "X@x#X'"] by auto
  thus ?thesis using Cons.IH[OF Cons.prems(1,2)] by auto
qed

lemma fun_type_param_idx: "\<Gamma> (Fun f T) = Fun g S \<Longrightarrow> i < length T \<Longrightarrow> \<Gamma> (T ! i) = S ! i"
by (metis fun_type fun_type_id_eq fun_type_inv(1) nth_map term.inject(2))

lemma fun_type_param_ex:
  assumes "\<Gamma> (Fun f T) = Fun g (map \<Gamma> S)" "t \<in> set S"
  shows "\<exists>s \<in> set T. \<Gamma> s = \<Gamma> t"
using fun_type_length_eq[OF assms(1)] length_map[of \<Gamma> S] assms(2)
      fun_type_param_idx[OF assms(1)] nth_map in_set_conv_nth
by metis

lemma tfr_stp_all_split:
  "list_all tfr\<^sub>s\<^sub>t\<^sub>p (x#S) \<Longrightarrow> list_all tfr\<^sub>s\<^sub>t\<^sub>p [x]"
  "list_all tfr\<^sub>s\<^sub>t\<^sub>p (x#S) \<Longrightarrow> list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
  "list_all tfr\<^sub>s\<^sub>t\<^sub>p (S@S') \<Longrightarrow> list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
  "list_all tfr\<^sub>s\<^sub>t\<^sub>p (S@S') \<Longrightarrow> list_all tfr\<^sub>s\<^sub>t\<^sub>p S'"
  "list_all tfr\<^sub>s\<^sub>t\<^sub>p (S@x#S') \<Longrightarrow> list_all tfr\<^sub>s\<^sub>t\<^sub>p (S@S')"
by fastforce+

lemma tfr_stp_all_append:
  assumes "list_all tfr\<^sub>s\<^sub>t\<^sub>p S" "list_all tfr\<^sub>s\<^sub>t\<^sub>p S'"
  shows "list_all tfr\<^sub>s\<^sub>t\<^sub>p (S@S')"
using assms by fastforce

lemma tfr_stp_all_wt_subst_apply:
  assumes "list_all tfr\<^sub>s\<^sub>t\<^sub>p S"
    and \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
           "bvars\<^sub>s\<^sub>t S \<inter> range_vars \<theta> = {}"
  shows "list_all tfr\<^sub>s\<^sub>t\<^sub>p (S \<cdot>\<^sub>s\<^sub>t \<theta>)"
using assms(1,4)
proof (induction S)
  case (Cons x S)
  hence IH: "list_all tfr\<^sub>s\<^sub>t\<^sub>p (S \<cdot>\<^sub>s\<^sub>t \<theta>)"
    using tfr_stp_all_split(2)[of x S]
    unfolding range_vars_alt_def by fastforce
  thus ?case
  proof (cases x)
    case (Equality a t t')
    hence "(\<exists>\<delta>. Unifier \<delta> t t') \<longrightarrow> \<Gamma> t = \<Gamma> t'" using Cons.prems by auto
    hence "(\<exists>\<delta>. Unifier \<delta> (t \<cdot> \<theta>) (t' \<cdot> \<theta>)) \<longrightarrow> \<Gamma> (t \<cdot> \<theta>) = \<Gamma> (t' \<cdot> \<theta>)"
      by (metis Unifier_comp' wt_subst_trm'[OF assms(2)])
    moreover have "(x#S) \<cdot>\<^sub>s\<^sub>t \<theta> = Equality a (t \<cdot> \<theta>) (t' \<cdot> \<theta>)#(S \<cdot>\<^sub>s\<^sub>t \<theta>)"
      using \<open>x = Equality a t t'\<close> by auto
    ultimately show ?thesis using IH by auto
  next
    case (Inequality X F)
    let ?\<sigma> = "rm_vars (set X) \<theta>"
    let ?G = "F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<sigma>"

    let ?P = "\<lambda>F X. \<forall>x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X. \<exists>a. \<Gamma> (Var x) = TAtom a"
    let ?Q = "\<lambda>F X.
      \<forall>f T. Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) \<longrightarrow> T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X)"

    have 0: "set X \<inter> range_vars ?\<sigma> = {}"
      using Cons.prems(2) Inequality rm_vars_img_subset[of "set X"]
      by (auto simp add: subst_domain_def range_vars_alt_def)

    have 1: "?P F X \<or> ?Q F X" using Inequality Cons.prems by simp

    have 2: "fv\<^sub>s\<^sub>e\<^sub>t (?\<sigma> ` set X) = set X" by auto

    have "?P ?G X" when "?P F X" using that
    proof (induction F)
      case (Cons g G)
      obtain t t' where g: "g = (t,t')" by (metis surj_pair)
      
      have "\<forall>x \<in> (fv (t \<cdot> ?\<sigma>) \<union> fv (t' \<cdot> ?\<sigma>)) - set X. \<exists>a. \<Gamma> (Var x) = Var a"
      proof -
        have *: "\<forall>x \<in> fv t - set X. \<exists>a. \<Gamma> (Var x) = Var a"
               "\<forall>x \<in> fv t' - set X. \<exists>a. \<Gamma> (Var x) = Var a"
          using g Cons.prems by simp_all

        have **: "\<forall>x. wf\<^sub>t\<^sub>r\<^sub>m (?\<sigma> x)"
          using \<theta>(2) wf_trm_subst_range_iff[of \<theta>] wf_trm_subst_rm_vars'[of \<theta> _ "set X"] by simp

        show ?thesis
          using wt_subst_TAtom_fv[OF wt_subst_rm_vars[OF \<theta>(1)] ** *(1)]
                wt_subst_TAtom_fv[OF wt_subst_rm_vars[OF \<theta>(1)] ** *(2)]
                wt_subst_trm'[OF wt_subst_rm_vars[OF \<theta>(1), of "set X"]] 2
          by blast
      qed
      moreover have "\<forall>x\<in>fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s (G \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<sigma>) - set X. \<exists>a. \<Gamma> (Var x) = Var a"
        using Cons by auto
      ultimately show ?case using g by (auto simp add: subst_apply_pairs_def)
    qed (simp add: subst_apply_pairs_def)
    hence "?P ?G X \<or> ?Q ?G X"
      using 1 ineq_subterm_inj_cond_subst[OF 0, of "trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F"] trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s_subst[of F ?\<sigma>]
      by presburger
    moreover have "(x#S) \<cdot>\<^sub>s\<^sub>t \<theta> = Inequality X (F \<cdot>\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s ?\<sigma>)#(S \<cdot>\<^sub>s\<^sub>t \<theta>)"
      using \<open>x = Inequality X F\<close> by auto
    ultimately show ?thesis using IH by simp
  qed auto
qed simp

lemma tfr_stp_all_same_type:
  "list_all tfr\<^sub>s\<^sub>t\<^sub>p (S@Equality a t t'#S') \<Longrightarrow> Unifier \<delta> t t' \<Longrightarrow> \<Gamma> t = \<Gamma> t'"
by force+

lemma tfr_subset:
  "\<And>A B. tfr\<^sub>s\<^sub>e\<^sub>t (A \<union> B) \<Longrightarrow> tfr\<^sub>s\<^sub>e\<^sub>t A"
  "\<And>A B. tfr\<^sub>s\<^sub>e\<^sub>t B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> tfr\<^sub>s\<^sub>e\<^sub>t A"
  "\<And>A B. tfr\<^sub>s\<^sub>e\<^sub>t B \<Longrightarrow> SMP A \<subseteq> SMP B \<Longrightarrow> tfr\<^sub>s\<^sub>e\<^sub>t A"
proof -
  show 1: "tfr\<^sub>s\<^sub>e\<^sub>t (A \<union> B) \<Longrightarrow> tfr\<^sub>s\<^sub>e\<^sub>t A" for A B
    using SMP_union[of A B] unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by simp

  fix A B assume B: "tfr\<^sub>s\<^sub>e\<^sub>t B"

  show "A \<subseteq> B \<Longrightarrow> tfr\<^sub>s\<^sub>e\<^sub>t A"
  proof -
    assume "A \<subseteq> B"
    then obtain C where "B = A \<union> C" by moura
    thus ?thesis using B 1 by blast
  qed

  show "SMP A \<subseteq> SMP B \<Longrightarrow> tfr\<^sub>s\<^sub>e\<^sub>t A"
  proof -
    assume "SMP A \<subseteq> SMP B"
    then obtain C where "SMP B = SMP A \<union> C" by moura
    thus ?thesis using B unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by blast
  qed
qed

lemma tfr_empty[simp]: "tfr\<^sub>s\<^sub>e\<^sub>t {}"
unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by simp

lemma tfr_consts_mono:
  assumes "\<forall>t \<in> M. \<exists>c. t = Fun c []"
    and "\<forall>t \<in> M. Ana t = ([], [])"
    and "tfr\<^sub>s\<^sub>e\<^sub>t N"
  shows "tfr\<^sub>s\<^sub>e\<^sub>t (N \<union> M)"
proof -
  { fix s t
    assume *: "s \<in> SMP (N \<union> M) - range Var" "t \<in> SMP (N \<union> M) - range Var" "\<exists>\<delta>. Unifier \<delta> s t"
    hence **: "is_Fun s" "is_Fun t" "s \<in> SMP N \<or> s \<in> M" "t \<in> SMP N \<or> t \<in> M"
      using assms(3) SMP_consts[OF assms(1,2)] SMP_union[of N M] by auto
    moreover have "\<Gamma> s = \<Gamma> t" when "s \<in> SMP N" "t \<in> SMP N"
      using that assms(3) *(3) **(1,2) unfolding tfr\<^sub>s\<^sub>e\<^sub>t_def by blast
    moreover have "\<Gamma> s = \<Gamma> t" when st: "s \<in> M" "t \<in> M"
    proof -
      obtain c d where "s = Fun c []" "t = Fun d []" using st assms(1) by moura
      hence "s = t" using *(3) by fast
      thus ?thesis by metis
    qed
    moreover have "\<Gamma> s = \<Gamma> t" when st: "s \<in> SMP N" "t \<in> M"
    proof -
      obtain c where "t = Fun c []" using st assms(1) by moura
      hence "s = t" using *(3) **(1,2) by auto
      thus ?thesis by metis
    qed
    moreover have "\<Gamma> s = \<Gamma> t" when st: "s \<in> M" "t \<in> SMP N"
    proof -
      obtain c where "s = Fun c []" using st assms(1) by moura
      hence "s = t" using *(3) **(1,2) by auto
      thus ?thesis by metis
    qed
    ultimately have "\<Gamma> s = \<Gamma> t" by metis
  } thus ?thesis by (metis tfr\<^sub>s\<^sub>e\<^sub>t_def)
qed

lemma dual\<^sub>s\<^sub>t_tfr\<^sub>s\<^sub>t\<^sub>p: "list_all tfr\<^sub>s\<^sub>t\<^sub>p S \<Longrightarrow> list_all tfr\<^sub>s\<^sub>t\<^sub>p (dual\<^sub>s\<^sub>t S)"
proof (induction S)
  case (Cons x S)
  have "list_all tfr\<^sub>s\<^sub>t\<^sub>p S" using Cons.prems by simp
  hence IH: "list_all tfr\<^sub>s\<^sub>t\<^sub>p (dual\<^sub>s\<^sub>t S)" using Cons.IH by metis
  from Cons show ?case
  proof (cases x)
    case (Equality a t t')
    hence "(\<exists>\<delta>. Unifier \<delta> t t') \<Longrightarrow> \<Gamma> t = \<Gamma> t'" using Cons by auto
    thus ?thesis using Equality IH by fastforce
  next
    case (Inequality X F)
    have "set (dual\<^sub>s\<^sub>t (x#S)) = insert x (set (dual\<^sub>s\<^sub>t S))" using Inequality by auto
    moreover have "(\<forall>x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X. \<exists>a. \<Gamma> (Var x) = Var a) \<or>
            (\<forall>f T. Fun f T \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F) \<longrightarrow> T = [] \<or> (\<exists>s \<in> set T. s \<notin> Var ` set X))" 
      using Cons.prems Inequality by auto
    ultimately show ?thesis using Inequality IH by auto
  qed auto
qed simp

lemma subst_var_inv_wt:
  assumes "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>"
  shows "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (subst_var_inv \<delta> X)"
using assms f_inv_into_f[of _ \<delta> X]
unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def subst_var_inv_def
by presburger

lemma subst_var_inv_wf_trms:
  "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (subst_var_inv \<delta> X))"
using f_inv_into_f[of _ \<delta> X]
unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def subst_var_inv_def
by auto

lemma unify_list_wt_if_same_type:
  assumes "Unification.unify E B = Some U" "\<forall>(s,t) \<in> set E. wf\<^sub>t\<^sub>r\<^sub>m s \<and> wf\<^sub>t\<^sub>r\<^sub>m t \<and> \<Gamma> s = \<Gamma> t"
  and "\<forall>(v,t) \<in> set B. \<Gamma> (Var v) = \<Gamma> t"
  shows "\<forall>(v,t) \<in> set U. \<Gamma> (Var v) = \<Gamma> t"
using assms
proof (induction E B arbitrary: U rule: Unification.unify.induct)
  case (2 f X g Y E B U)
  hence "wf\<^sub>t\<^sub>r\<^sub>m (Fun f X)" "wf\<^sub>t\<^sub>r\<^sub>m (Fun g Y)" "\<Gamma> (Fun f X) = \<Gamma> (Fun g Y)" by auto

  from "2.prems"(1) obtain E' where *: "decompose (Fun f X) (Fun g Y) = Some E'"
    and [simp]: "f = g" "length X = length Y" "E' = zip X Y"
    and **: "Unification.unify (E'@E) B = Some U"
    by (auto split: option.splits)
  
  have "\<forall>(s,t) \<in> set E'. wf\<^sub>t\<^sub>r\<^sub>m s \<and> wf\<^sub>t\<^sub>r\<^sub>m t \<and> \<Gamma> s = \<Gamma> t"
  proof -
    { fix s t assume "(s,t) \<in> set E'"
      then obtain X' X'' Y' Y'' where "X = X'@s#X''" "Y = Y'@t#Y''" "length X' = length Y'"
        using zip_arg_subterm_split[of s t X Y] \<open>E' = zip X Y\<close> by metis
      hence "\<Gamma> (Fun f (X'@s#X'')) = \<Gamma> (Fun g (Y'@t#Y''))" by (metis \<open>\<Gamma> (Fun f X) = \<Gamma> (Fun g Y)\<close>)
      
      from \<open>E' = zip X Y\<close> have "\<forall>(s,t) \<in> set E'. s \<sqsubset> Fun f X \<and> t \<sqsubset> Fun g Y"
        using zip_arg_subterm[of _ _ X Y] by blast
      with \<open>(s,t) \<in> set E'\<close> have "wf\<^sub>t\<^sub>r\<^sub>m s" "wf\<^sub>t\<^sub>r\<^sub>m t"
        using wf_trm_subterm \<open>wf\<^sub>t\<^sub>r\<^sub>m (Fun f X)\<close> \<open>wf\<^sub>t\<^sub>r\<^sub>m (Fun g Y)\<close> by (blast,blast)
      moreover have "f \<in> \<Sigma>\<^sub>f"
      proof (rule ccontr)
        assume "f \<notin> \<Sigma>\<^sub>f"
        hence "f \<in> \<C>" "arity f = 0" using const_arity_eq_zero[of f] by simp_all
        thus False using \<open>wf\<^sub>t\<^sub>r\<^sub>m (Fun f X)\<close> * \<open>(s,t) \<in> set E'\<close> unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by auto
      qed
      hence "\<Gamma> s = \<Gamma> t"
        using fun_type_arg_cong' \<open>f \<in> \<Sigma>\<^sub>f\<close> \<open>\<Gamma> (Fun f (X'@s#X'')) = \<Gamma> (Fun g (Y'@t#Y''))\<close>
              \<open>length X' = length Y'\<close> \<open>f = g\<close>
        by metis
      ultimately have "wf\<^sub>t\<^sub>r\<^sub>m s" "wf\<^sub>t\<^sub>r\<^sub>m t" "\<Gamma> s = \<Gamma> t" by metis+
    }
    thus ?thesis by blast
  qed
  moreover have "\<forall>(s,t) \<in> set E. wf\<^sub>t\<^sub>r\<^sub>m s \<and> wf\<^sub>t\<^sub>r\<^sub>m t \<and> \<Gamma> s = \<Gamma> t" using "2.prems"(2) by auto
  ultimately show ?case using "2.IH"[OF * ** _ "2.prems"(3)] by fastforce
next
  case (3 v t E B U)
  hence "\<Gamma> (Var v) = \<Gamma> t" "wf\<^sub>t\<^sub>r\<^sub>m t" by auto
  hence "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (subst v t)"
      and *: "\<forall>(v, t) \<in> set ((v,t)#B). \<Gamma> (Var v) = \<Gamma> t"
             "\<And>t t'. (t,t') \<in> set E \<Longrightarrow> \<Gamma> t = \<Gamma> t'"
    using "3.prems"(2,3) unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def subst_def by auto

  show ?case
  proof (cases "t = Var v")
    assume "t = Var v" thus ?case using 3 by auto
  next
    assume "t \<noteq> Var v"
    hence "v \<notin> fv t" using "3.prems"(1) by auto
    hence **: "Unification.unify (subst_list (subst v t) E) ((v, t)#B) = Some U"
      using Unification.unify.simps(3)[of v t E B] "3.prems"(1) \<open>t \<noteq> Var v\<close> by auto
    
    have "\<forall>(s, t) \<in> set (subst_list (subst v t) E). wf\<^sub>t\<^sub>r\<^sub>m s \<and> wf\<^sub>t\<^sub>r\<^sub>m t"
      using wf_trm_subst_singleton[OF _ \<open>wf\<^sub>t\<^sub>r\<^sub>m t\<close>] "3.prems"(2)
      unfolding subst_list_def subst_def by auto
    moreover have "\<forall>(s, t) \<in> set (subst_list (subst v t) E). \<Gamma> s = \<Gamma> t"
      using *(2)[THEN wt_subst_trm'[OF \<open>wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (subst v t)\<close>]] by (simp add: subst_list_def)
    ultimately show ?thesis using "3.IH"(2)[OF \<open>t \<noteq> Var v\<close> \<open>v \<notin> fv t\<close> ** _ *(1)] by auto
  qed
next
  case (4 f X v E B U)
  hence "\<Gamma> (Var v) = \<Gamma> (Fun f X)" "wf\<^sub>t\<^sub>r\<^sub>m (Fun f X)" by auto
  hence "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (subst v (Fun f X))"
      and *: "\<forall>(v, t) \<in> set ((v,(Fun f X))#B). \<Gamma> (Var v) = \<Gamma> t"
             "\<And>t t'. (t,t') \<in> set E \<Longrightarrow> \<Gamma> t = \<Gamma> t'"
    using "4.prems"(2,3) unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def subst_def by auto

  have "v \<notin> fv (Fun f X)" using "4.prems"(1) by force
  hence **: "Unification.unify (subst_list (subst v (Fun f X)) E) ((v, (Fun f X))#B) = Some U"
    using Unification.unify.simps(3)[of v "Fun f X" E B] "4.prems"(1) by auto
  
  have "\<forall>(s, t) \<in> set (subst_list (subst v (Fun f X)) E). wf\<^sub>t\<^sub>r\<^sub>m s \<and> wf\<^sub>t\<^sub>r\<^sub>m t"
    using wf_trm_subst_singleton[OF _ \<open>wf\<^sub>t\<^sub>r\<^sub>m (Fun f X)\<close>] "4.prems"(2)
    unfolding subst_list_def subst_def by auto
  moreover have "\<forall>(s, t) \<in> set (subst_list (subst v (Fun f X)) E). \<Gamma> s = \<Gamma> t"
    using *(2)[THEN wt_subst_trm'[OF \<open>wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (subst v (Fun f X))\<close>]] by (simp add: subst_list_def)
  ultimately show ?case using "4.IH"[OF \<open>v \<notin> fv (Fun f X)\<close> ** _ *(1)] by auto
qed auto

lemma mgu_wt_if_same_type:
  assumes "mgu s t = Some \<sigma>" "wf\<^sub>t\<^sub>r\<^sub>m s" "wf\<^sub>t\<^sub>r\<^sub>m t" "\<Gamma> s = \<Gamma> t"
  shows "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>"
proof -
  let ?fv_disj = "\<lambda>v t S. \<not>(\<exists>(v',t') \<in> S - {(v,t)}. (insert v (fv t)) \<inter> (insert v' (fv t')) \<noteq> {})"

  from assms(1) obtain \<sigma>' where "Unification.unify [(s,t)] [] = Some \<sigma>'" "subst_of \<sigma>' = \<sigma>"
    by (auto split: option.splits)
  hence "\<forall>(v,t) \<in> set \<sigma>'. \<Gamma> (Var v) = \<Gamma> t" "distinct (map fst \<sigma>')"
    using assms(2,3,4) unify_list_wt_if_same_type unify_list_distinct[of "[(s,t)]"] by auto
  thus "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>" using \<open>subst_of \<sigma>' = \<sigma>\<close> unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def
  proof (induction \<sigma>' arbitrary: \<sigma> rule: List.rev_induct)
    case (snoc tt \<sigma>' \<sigma>)
    then obtain v t where tt: "tt = (v,t)" by (metis surj_pair)
    hence \<sigma>: "\<sigma> = subst v t \<circ>\<^sub>s subst_of \<sigma>'" using snoc.prems(3) by simp
    
    have "\<forall>(v,t) \<in> set \<sigma>'. \<Gamma> (Var v) = \<Gamma> t" "distinct (map fst \<sigma>')" using snoc.prems(1,2) by auto
    then obtain \<sigma>'' where \<sigma>'': "subst_of \<sigma>' = \<sigma>''" "\<forall>v. \<Gamma> (Var v) = \<Gamma> (\<sigma>'' v)" by (metis snoc.IH)
    hence "\<Gamma> t = \<Gamma> (t \<cdot> \<sigma>'')" for t using wt_subst_trm by blast
    hence "\<Gamma> (Var v) = \<Gamma> (\<sigma>'' v)" "\<Gamma> t = \<Gamma> (t \<cdot> \<sigma>'')" using \<sigma>''(2) by auto
    moreover have "\<Gamma> (Var v) = \<Gamma> t" using snoc.prems(1) tt by simp
    moreover have \<sigma>2: "\<sigma> = Var(v := t) \<circ>\<^sub>s \<sigma>'' " using \<sigma> \<sigma>''(1) unfolding subst_def by simp
    ultimately have "\<Gamma> (Var v) = \<Gamma> (\<sigma> v)" unfolding subst_compose_def by simp

    have "subst_domain (subst v t) \<subseteq> {v}" unfolding subst_def by (auto simp add: subst_domain_def)
    hence *: "subst_domain \<sigma> \<subseteq> insert v (subst_domain \<sigma>'')"
      using tt \<sigma> \<sigma>''(1) snoc.prems(2) subst_domain_compose[of _ \<sigma>'']
      by (auto simp add: subst_domain_def)
    
    have "v \<notin> set (map fst \<sigma>')" using tt snoc.prems(2) by auto
    hence "v \<notin> subst_domain \<sigma>''" using \<sigma>''(1) subst_of_dom_subset[of \<sigma>'] by auto

    { fix w assume "w \<in> subst_domain \<sigma>''"
      hence "\<sigma> w = \<sigma>'' w" using \<sigma>2 \<sigma>''(1) \<open>v \<notin> subst_domain \<sigma>''\<close> unfolding subst_compose_def by auto
      hence "\<Gamma> (Var w) = \<Gamma> (\<sigma> w)" using \<sigma>''(2) by simp
    }
    thus ?case using \<open>\<Gamma> (Var v) = \<Gamma> (\<sigma> v)\<close> * by force
  qed simp
qed

lemma wt_Unifier_if_Unifier:
  assumes s_t: "wf\<^sub>t\<^sub>r\<^sub>m s" "wf\<^sub>t\<^sub>r\<^sub>m t" "\<Gamma> s = \<Gamma> t"
    and \<delta>: "Unifier \<delta> s t"
  shows "\<exists>\<theta>. Unifier \<theta> s t \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
using mgu_always_unifies[OF \<delta>] mgu_gives_MGU[THEN MGU_is_Unifier[of s _ t]]
      mgu_wt_if_same_type[OF _ s_t] mgu_wf_trm[OF _ s_t(1,2)] wf_trm_subst_range_iff
by fast

end


subsection \<open>Automatically Proving Type-Flaw Resistance\<close>
subsubsection \<open>Definitions: Variable Renaming\<close>
abbreviation "max_var t \<equiv> Max (insert 0 (snd ` fv t))"
abbreviation "max_var_set X \<equiv> Max (insert 0 (snd ` X))"

definition "var_rename n v \<equiv> Var (fst v, snd v + Suc n)"
definition "var_rename_inv n v \<equiv> Var (fst v, snd v - Suc n)"


subsubsection \<open>Definitions: Computing a Finite Representation of the Sub-Message Patterns\<close>
text \<open>A sufficient requirement for a term to be a well-typed instance of another term\<close>
definition is_wt_instance_of_cond where
  "is_wt_instance_of_cond \<Gamma> t s \<equiv> (
    \<Gamma> t = \<Gamma> s \<and> (case mgu t s of
      None \<Rightarrow> False
    | Some \<delta> \<Rightarrow> inj_on \<delta> (fv t) \<and> (\<forall>x \<in> fv t. is_Var (\<delta> x))))"

definition has_all_wt_instances_of where
  "has_all_wt_instances_of \<Gamma> N M \<equiv> \<forall>t \<in> N. \<exists>s \<in> M. is_wt_instance_of_cond \<Gamma> t s"

text \<open>This function computes a finite representation of the set of sub-message patterns\<close>
definition SMP0 where
  "SMP0 Ana \<Gamma> M \<equiv> let
      f = \<lambda>t. Fun (the_Fun (\<Gamma> t)) (map Var (zip (args (\<Gamma> t)) [0..<length (args (\<Gamma> t))]));
      g = \<lambda>M'. map f (filter (\<lambda>t. is_Var t \<and> is_Fun (\<Gamma> t)) M')@
               concat (map (fst \<circ> Ana) M')@concat (map subterms_list M');
      h = remdups \<circ> g
    in while (\<lambda>A. set (h A) \<noteq> set A) h M"

text \<open>These definitions are useful to refine an SMP representation set\<close>
fun generalize_term where
  "generalize_term _ _ n (Var x) = (Var x, n)"
| "generalize_term \<Gamma> p n (Fun f T) = (let \<tau> = \<Gamma> (Fun f T)
    in if p \<tau> then (Var (\<tau>, n), Suc n)
       else let (T',n') = foldr (\<lambda>t (S,m). let (t',m') = generalize_term \<Gamma> p m t in (t'#S,m'))
                                T ([],n)
            in (Fun f T', n'))"

definition generalize_terms where
  "generalize_terms \<Gamma> p \<equiv> map (fst \<circ> generalize_term \<Gamma> p 0)"

definition remove_superfluous_terms where
  "remove_superfluous_terms \<Gamma> T \<equiv>
    let
      f = \<lambda>S t R. \<exists>s \<in> set S - R. s \<noteq> t \<and> is_wt_instance_of_cond \<Gamma> t s;
      g = \<lambda>S t (U,R). if f S t R then (U, insert t R) else (t#U, R);
      h = \<lambda>S. remdups (fst (foldr (g S) S ([],{})))
    in while (\<lambda>S. h S \<noteq> S) h T"


subsubsection \<open>Definitions: Checking Type-Flaw Resistance\<close>
definition is_TComp_var_instance_closed where
  "is_TComp_var_instance_closed \<Gamma> M \<equiv> \<forall>x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). is_Fun (\<Gamma> (Var x)) \<longrightarrow>
      list_ex (\<lambda>t. is_Fun t \<and> \<Gamma> t = \<Gamma> (Var x) \<and> list_all is_Var (args t) \<and> distinct (args t)) M"

definition finite_SMP_representation where
  "finite_SMP_representation arity Ana \<Gamma> M \<equiv>
    list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) M \<and>
    has_all_wt_instances_of \<Gamma> (subterms\<^sub>s\<^sub>e\<^sub>t (set M)) (set M) \<and>
    has_all_wt_instances_of \<Gamma> (\<Union>((set \<circ> fst \<circ> Ana) ` set M)) (set M) \<and>
    is_TComp_var_instance_closed \<Gamma> M"

definition comp_tfr\<^sub>s\<^sub>e\<^sub>t where
  "comp_tfr\<^sub>s\<^sub>e\<^sub>t arity Ana \<Gamma> M \<equiv>
    finite_SMP_representation arity Ana \<Gamma> M \<and>
    (let \<delta> = var_rename (max_var_set (fv\<^sub>s\<^sub>e\<^sub>t (set M)))
     in \<forall>s \<in> set M. \<forall>t \<in> set M. is_Fun s \<and> is_Fun t \<and> \<Gamma> s \<noteq> \<Gamma> t \<longrightarrow> mgu s (t \<cdot> \<delta>) = None)"

fun comp_tfr\<^sub>s\<^sub>t\<^sub>p where
  "comp_tfr\<^sub>s\<^sub>t\<^sub>p \<Gamma> (\<langle>_: t \<doteq> t'\<rangle>\<^sub>s\<^sub>t) = (mgu t t' \<noteq> None \<longrightarrow> \<Gamma> t = \<Gamma> t')"
| "comp_tfr\<^sub>s\<^sub>t\<^sub>p \<Gamma> (\<forall>X\<langle>\<or>\<noteq>: F\<rangle>\<^sub>s\<^sub>t) = (
    (\<forall>x \<in> fv\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F - set X. is_Var (\<Gamma> (Var x))) \<or>
    (\<forall>u \<in> subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F).
      is_Fun u \<longrightarrow> (args u = [] \<or> (\<exists>s \<in> set (args u). s \<notin> Var ` set X))))"
| "comp_tfr\<^sub>s\<^sub>t\<^sub>p _ _ = True"

definition comp_tfr\<^sub>s\<^sub>t where
  "comp_tfr\<^sub>s\<^sub>t arity Ana \<Gamma> M S \<equiv>
    list_all (comp_tfr\<^sub>s\<^sub>t\<^sub>p \<Gamma>) S \<and>
    list_all (wf\<^sub>t\<^sub>r\<^sub>m' arity) (trms_list\<^sub>s\<^sub>t S) \<and>
    has_all_wt_instances_of \<Gamma> (trms\<^sub>s\<^sub>t S) (set M) \<and>
    comp_tfr\<^sub>s\<^sub>e\<^sub>t arity Ana \<Gamma> M"


subsubsection \<open>Small Lemmata\<close>
lemma less_Suc_max_var_set:
  assumes z: "z \<in> X"
    and X: "finite X"
  shows "snd z < Suc (max_var_set X)"
proof -
  have "snd z \<in> snd ` X" using z by simp
  hence "snd z \<le> Max (insert 0 (snd ` X))" using X by simp
  thus ?thesis using X by simp
qed

lemma (in typed_model) finite_SMP_representationD:
  assumes "finite_SMP_representation arity Ana \<Gamma> M"
  shows "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)"
    and "has_all_wt_instances_of \<Gamma> (subterms\<^sub>s\<^sub>e\<^sub>t (set M)) (set M)"
    and "has_all_wt_instances_of \<Gamma> (\<Union>((set \<circ> fst \<circ> Ana) ` set M)) (set M)"
    and "is_TComp_var_instance_closed \<Gamma> M"
using assms unfolding finite_SMP_representation_def list_all_iff wf\<^sub>t\<^sub>r\<^sub>m_code by blast+

lemma (in typed_model) is_wt_instance_of_condD:
  assumes t_instance_s: "is_wt_instance_of_cond \<Gamma> t s"
  obtains \<delta> where
    "\<Gamma> t = \<Gamma> s" "mgu t s = Some \<delta>"
    "inj_on \<delta> (fv t)" "\<delta> ` (fv t) \<subseteq> range Var"
using t_instance_s unfolding is_wt_instance_of_cond_def Let_def by (cases "mgu t s") fastforce+

lemma (in typed_model) is_wt_instance_of_condD':
  assumes t_wf_trm: "wf\<^sub>t\<^sub>r\<^sub>m t"
    and s_wf_trm: "wf\<^sub>t\<^sub>r\<^sub>m s"
    and t_instance_s: "is_wt_instance_of_cond \<Gamma> t s"
  shows "\<exists>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t = s \<cdot> \<delta>"
proof -
  obtain \<delta> where s:
      "\<Gamma> t = \<Gamma> s" "mgu t s = Some \<delta>"
      "inj_on \<delta> (fv t)" "\<delta> ` (fv t) \<subseteq> range Var"
    by (metis is_wt_instance_of_condD[OF t_instance_s])

  have 0: "wf\<^sub>t\<^sub>r\<^sub>m t" "wf\<^sub>t\<^sub>r\<^sub>m s" using s(1) t_wf_trm s_wf_trm by auto

  note 1 = mgu_wt_if_same_type[OF s(2) 0 s(1)]

  note 2 = conjunct1[OF mgu_gives_MGU[OF s(2)]]

  show ?thesis
    using s(1) inj_var_ran_unifiable_has_subst_match[OF 2 s(3,4)]
          wt_subst_compose[OF 1 subst_var_inv_wt[OF 1, of "fv t"]]
          wf_trms_subst_compose[OF mgu_wf_trms[OF s(2) 0] subst_var_inv_wf_trms[of \<delta> "fv t"]]
    by auto
qed

lemma (in typed_model) is_wt_instance_of_condD'':
  assumes s_wf_trm: "wf\<^sub>t\<^sub>r\<^sub>m s"
    and t_instance_s: "is_wt_instance_of_cond \<Gamma> t s"
    and t_var: "t = Var x"
  shows "\<exists>y. s = Var y \<and> \<Gamma> (Var y) = \<Gamma> (Var x)"
proof -
  obtain \<delta> where \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" and s: "Var x = s \<cdot> \<delta>"
    using is_wt_instance_of_condD'[OF _ s_wf_trm t_instance_s] t_var by auto
  obtain y where y: "s = Var y" using s by (cases s) auto
  show ?thesis using wt_subst_trm''[OF \<delta>] s y by metis
qed

lemma (in typed_model) has_all_wt_instances_ofD:
  assumes N_instance_M: "has_all_wt_instances_of \<Gamma> N M"
    and t_in_N: "t \<in> N"
  obtains s \<delta> where
    "s \<in> M" "\<Gamma> t = \<Gamma> s" "mgu t s = Some \<delta>"
    "inj_on \<delta> (fv t)" "\<delta> ` (fv t) \<subseteq> range Var"
by (metis t_in_N N_instance_M is_wt_instance_of_condD has_all_wt_instances_of_def)

lemma (in typed_model) has_all_wt_instances_ofD':
  assumes N_wf_trms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s N"
    and M_wf_trms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M"
    and N_instance_M: "has_all_wt_instances_of \<Gamma> N M"
    and t_in_N: "t \<in> N"
  shows "\<exists>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t \<in> M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<delta>"
using assms is_wt_instance_of_condD' unfolding has_all_wt_instances_of_def by fast

lemma (in typed_model) has_all_wt_instances_ofD'':
  assumes N_wf_trms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s N"
    and M_wf_trms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M"
    and N_instance_M: "has_all_wt_instances_of \<Gamma> N M"
    and t_in_N: "Var x \<in> N"
  shows "\<exists>y. Var y \<in> M \<and> \<Gamma> (Var y) = \<Gamma> (Var x)"
using assms is_wt_instance_of_condD'' unfolding has_all_wt_instances_of_def by fast
  
lemma (in typed_model) has_all_instances_of_if_subset:
  assumes "N \<subseteq> M"
  shows "has_all_wt_instances_of \<Gamma> N M"
using assms inj_onI mgu_same_empty
unfolding has_all_wt_instances_of_def is_wt_instance_of_cond_def
by (smt option.case_eq_if option.discI option.sel subsetD term.discI(1) term.inject(1))

lemma (in typed_model) SMP_I':
  assumes N_wf_trms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s N"
    and M_wf_trms: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s M"
    and N_instance_M: "has_all_wt_instances_of \<Gamma> N M"
    and t_in_N: "t \<in> N"
  shows "t \<in> SMP M"
using has_all_wt_instances_ofD'[OF N_wf_trms M_wf_trms N_instance_M t_in_N]
      SMP.Substitution[OF SMP.MP[of _ M]]
by blast


subsubsection \<open>Lemma: Proving Type-Flaw Resistance\<close>
locale typed_model' = typed_model arity public Ana \<Gamma>
  for arity::"'fun \<Rightarrow> nat"
    and public::"'fun \<Rightarrow> bool"
    and Ana::"('fun,(('fun,'atom::finite) term_type \<times> nat)) term
              \<Rightarrow> (('fun,(('fun,'atom) term_type \<times> nat)) term list
                 \<times> ('fun,(('fun,'atom) term_type \<times> nat)) term list)"
    and \<Gamma>::"('fun,(('fun,'atom) term_type \<times> nat)) term \<Rightarrow> ('fun,'atom) term_type"
  +
  assumes \<Gamma>_Var_fst: "\<And>\<tau> n m. \<Gamma> (Var (\<tau>,n)) = \<Gamma> (Var (\<tau>,m))"
    and Ana_const: "\<And>c T. arity c = 0 \<Longrightarrow> Ana (Fun c T) = ([],[])"
    and Ana_subst'_or_Ana_keys_subterm:
      "(\<forall>f T \<delta> K R. Ana (Fun f T) = (K,R) \<longrightarrow> Ana (Fun f T \<cdot> \<delta>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>,R \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)) \<or>
       (\<forall>t K R k. Ana t = (K,R) \<longrightarrow> k \<in> set K \<longrightarrow> k \<sqsubset> t)"
begin

lemma var_rename_inv_comp: "t \<cdot> (var_rename n \<circ>\<^sub>s var_rename_inv n) = t"
proof (induction t)
  case (Fun f T)
  hence "map (\<lambda>t. t \<cdot> var_rename n \<circ>\<^sub>s var_rename_inv n) T = T" by (simp add: map_idI) 
  thus ?case by (metis subst_apply_term.simps(2)) 
qed (simp add: var_rename_def var_rename_inv_def)

lemma var_rename_fv_disjoint:
  "fv s \<inter> fv (t \<cdot> var_rename (max_var s)) = {}"
proof -
  have 1: "\<forall>v \<in> fv s. snd v \<le> max_var s" by simp
  have 2: "\<forall>v \<in> fv (t \<cdot> var_rename n). snd v > n" for n unfolding var_rename_def by (induct t) auto
  show ?thesis using 1 2 by force
qed

lemma var_rename_fv_set_disjoint:
  assumes "finite M" "s \<in> M"
  shows "fv s \<inter> fv (t \<cdot> var_rename (max_var_set (fv\<^sub>s\<^sub>e\<^sub>t M))) = {}"
proof -
  have 1: "\<forall>v \<in> fv s. snd v \<le> max_var_set (fv\<^sub>s\<^sub>e\<^sub>t M)" using assms
  proof (induction M rule: finite_induct)
    case (insert t M) thus ?case
    proof (cases "t = s")
      case False
      hence "\<forall>v \<in> fv s. snd v \<le> max_var_set (fv\<^sub>s\<^sub>e\<^sub>t M)" using insert by simp
      moreover have "max_var_set (fv\<^sub>s\<^sub>e\<^sub>t M) \<le> max_var_set (fv\<^sub>s\<^sub>e\<^sub>t (insert t M))"
        using insert.hyps(1) insert.prems
        by force
      ultimately show ?thesis by auto
    qed simp
  qed simp

  have 2: "\<forall>v \<in> fv (t \<cdot> var_rename n). snd v > n" for n unfolding var_rename_def by (induct t) auto

  show ?thesis using 1 2 by force
qed

lemma var_rename_fv_set_disjoint':
  assumes "finite M"
  shows "fv\<^sub>s\<^sub>e\<^sub>t M \<inter> fv\<^sub>s\<^sub>e\<^sub>t (N \<cdot>\<^sub>s\<^sub>e\<^sub>t var_rename (max_var_set (fv\<^sub>s\<^sub>e\<^sub>t M))) = {}"
using var_rename_fv_set_disjoint[OF assms] by auto

lemma var_rename_is_renaming[simp]:
  "subst_range (var_rename n) \<subseteq> range Var"
  "subst_range (var_rename_inv n) \<subseteq> range Var"
unfolding var_rename_def var_rename_inv_def by auto

lemma var_rename_wt[simp]:
  "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (var_rename n)"
  "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (var_rename_inv n)"
by (auto simp add: var_rename_def var_rename_inv_def wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def \<Gamma>_Var_fst)

lemma var_rename_wt':
  assumes "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "s = m \<cdot> \<delta>"
  shows "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (var_rename_inv n \<circ>\<^sub>s \<delta>)" "s = m \<cdot> var_rename n \<cdot> var_rename_inv n \<circ>\<^sub>s \<delta>"
using assms(2) wt_subst_compose[OF var_rename_wt(2)[of n] assms(1)] var_rename_inv_comp[of m n]
by force+

lemma var_rename_wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_range[simp]:
  "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (var_rename n))"
  "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (var_rename_inv n))"
using var_rename_is_renaming by fastforce+

lemma Fun_range_case:
  "(\<forall>f T. Fun f T \<in> M \<longrightarrow> P f T) \<longleftrightarrow> (\<forall>u \<in> M. case u of Fun f T \<Rightarrow> P f T | _ \<Rightarrow> True)"
  "(\<forall>f T. Fun f T \<in> M \<longrightarrow> P f T) \<longleftrightarrow> (\<forall>u \<in> M. is_Fun u \<longrightarrow> P (the_Fun u) (args u))"
by (auto split: "term.splits")

lemma is_TComp_var_instance_closedD:
  assumes x: "\<exists>y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). \<Gamma> (Var x) = \<Gamma> (Var y)" "\<Gamma> (Var x) = TComp f T"
    and closed: "is_TComp_var_instance_closed \<Gamma> M"
  shows "\<exists>g U. Fun g U \<in> set M \<and> \<Gamma> (Fun g U) = \<Gamma> (Var x) \<and> (\<forall>u \<in> set U. is_Var u) \<and> distinct U"
using assms unfolding is_TComp_var_instance_closed_def list_all_iff list_ex_iff by fastforce

lemma is_TComp_var_instance_closedD':
  assumes "\<exists>y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). \<Gamma> (Var x) = \<Gamma> (Var y)" "TComp f T \<sqsubseteq> \<Gamma> (Var x)"
    and closed: "is_TComp_var_instance_closed \<Gamma> M"
    and wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)"
  shows "\<exists>g U. Fun g U \<in> set M \<and> \<Gamma> (Fun g U) = TComp f T \<and> (\<forall>u \<in> set U. is_Var u) \<and> distinct U"
using assms(1,2)
proof (induction "\<Gamma> (Var x)" arbitrary: x)
  case (Fun g U)
  note IH = Fun.hyps(1)
  have g: "arity g > 0" "public g" using Fun.hyps(2) fun_type_inv[of "Var x"] \<Gamma>_Var_fst by simp_all
  then obtain V where V:
      "Fun g V \<in> set M" "\<Gamma> (Fun g V) = \<Gamma> (Var x)" "\<forall>v \<in> set V. \<exists>x. v = Var x"
      "distinct V" "length U = length V"
    using is_TComp_var_instance_closedD[OF Fun.prems(1) Fun.hyps(2)[symmetric] closed(1)]
    by (metis Fun.hyps(2) fun_type_id_eq fun_type_length_eq is_VarE)
  hence U: "U = map \<Gamma> V" using fun_type[OF g(1), of V] Fun.hyps(2) by simp
  hence 1: "\<Gamma> v \<in> set U" when v: "v \<in> set V" for v using v by simp

  have 2: "\<exists>y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). \<Gamma> (Var z) = \<Gamma> (Var y)" when z: "Var z \<in> set V" for z
    using V(1) fv_subset_subterms Fun_param_in_subterms[OF z] by fastforce

  show ?case
  proof (cases "TComp f T = \<Gamma> (Var x)")
    case False
    then obtain u where u: "u \<in> set U" "TComp f T \<sqsubseteq> u"
      using Fun.prems(2) Fun.hyps(2) by moura
    then obtain y where y: "Var y \<in> set V" "\<Gamma> (Var y) = u" using U V(3) \<Gamma>_Var_fst by auto
    show ?thesis using IH[OF _ 2[OF y(1)]] u y(2) by metis
  qed (use V in fastforce)
qed simp

lemma TComp_var_instance_wt_subst_exists:
  assumes gT: "\<Gamma> (Fun g T) = TComp g (map \<Gamma> U)" "wf\<^sub>t\<^sub>r\<^sub>m (Fun g T)"
    and U: "\<forall>u \<in> set U. \<exists>y. u = Var y" "distinct U"
  shows "\<exists>\<theta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>) \<and> Fun g T = Fun g U \<cdot> \<theta>"
proof -
  define the_i where "the_i \<equiv> \<lambda>y. THE x. x < length U \<and> U ! x = Var y"
  define \<theta> where \<theta>: "\<theta> \<equiv> \<lambda>y. if Var y \<in> set U then T ! the_i y else Var y"

  have g: "arity g > 0" using gT(1,2) fun_type_inv(1) by blast

  have UT: "length U = length T" using fun_type_length_eq gT(1) by fastforce

  have 1: "the_i y < length U \<and> U ! the_i y = Var y" when y: "Var y \<in> set U" for y
    using theI'[OF distinct_Ex1[OF U(2) y]] unfolding the_i_def by simp

  have 2: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>"
    using \<theta> 1 gT(1) fun_type[OF g] UT
    unfolding wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def
    by (metis (no_types, lifting) nth_map term.inject(2))

  have "\<forall>i<length T. U ! i \<cdot> \<theta> = T ! i"
    using \<theta> 1 U(1) UT distinct_Ex1[OF U(2)] in_set_conv_nth
    by (metis (no_types, lifting) subst_apply_term.simps(1))
  hence "T = map (\<lambda>t. t \<cdot> \<theta>) U" by (simp add: UT nth_equalityI)
  hence 3: "Fun g T = Fun g U \<cdot> \<theta>" by simp

  have "subst_range \<theta> \<subseteq> set T" using \<theta> 1 U(1) UT by (auto simp add: subst_domain_def)
  hence 4: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" using gT(2) wf_trm_param by auto

  show ?thesis by (metis 2 3 4)
qed

lemma TComp_var_instance_closed_has_Var:
  assumes closed: "is_TComp_var_instance_closed \<Gamma> M"
    and wf_M: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)"
    and wf_\<delta>x: "wf\<^sub>t\<^sub>r\<^sub>m (\<delta> x)"
    and y_ex: "\<exists>y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). \<Gamma> (Var x) = \<Gamma> (Var y)"
    and t: "t \<sqsubseteq> \<delta> x"
    and \<delta>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>"
  shows "\<exists>y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). \<Gamma> (Var y) = \<Gamma> t"
proof (cases "\<Gamma> (Var x)")
  case (Var a)
  hence "t = \<delta> x"
    using t wf_\<delta>x \<delta>_wt
    by (metis (full_types) const_type_inv_wf fun_if_subterm subtermeq_Var_const(2) wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
  thus ?thesis using y_ex wt_subst_trm''[OF \<delta>_wt, of "Var x"] by fastforce
next
  case (Fun f T)
  hence \<Gamma>_\<delta>x: "\<Gamma> (\<delta> x) = TComp f T" using wt_subst_trm''[OF \<delta>_wt, of "Var x"] by auto

  show ?thesis
  proof (cases "t = \<delta> x")
    case False
    hence t_subt_\<delta>x: "t \<sqsubset> \<delta> x" using t(1) \<Gamma>_\<delta>x by fastforce

    obtain T' where T': "\<delta> x = Fun f T'" using \<Gamma>_\<delta>x t_subt_\<delta>x fun_type_id_eq by (cases "\<delta> x") auto
    
    obtain g S where gS: "Fun g S \<sqsubseteq> \<delta> x" "t \<in> set S" using Fun_ex_if_subterm[OF t_subt_\<delta>x] by blast
  
    have gS_wf: "wf\<^sub>t\<^sub>r\<^sub>m (Fun g S)" by (rule wf_trm_subtermeq[OF wf_\<delta>x gS(1)])
    hence "arity g > 0" using gS(2) by (metis length_pos_if_in_set wf_trm_arity) 
    hence gS_\<Gamma>: "\<Gamma> (Fun g S) = TComp g (map \<Gamma> S)" using fun_type by blast
  
    obtain h U where hU:
        "Fun h U \<in> set M" "\<Gamma> (Fun h U) = Fun g (map \<Gamma> S)" "\<forall>u \<in> set U. is_Var u"
      using is_TComp_var_instance_closedD'[OF y_ex _ closed wf_M]
            subtermeq_imp_subtermtypeeq[OF wf_\<delta>x] gS \<Gamma>_\<delta>x Fun gS_\<Gamma>
      by metis
  
    obtain y where y: "Var y \<in> set U" "\<Gamma> (Var y) = \<Gamma> t"
      using hU(3) fun_type_param_ex[OF hU(2) gS(2)] by fast
  
    have "y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M)" using hU(1) y(1) by force
    thus ?thesis using y(2) closed by metis
  qed (metis y_ex Fun \<Gamma>_\<delta>x)
qed

lemma TComp_var_instance_closed_has_Fun:
  assumes closed: "is_TComp_var_instance_closed \<Gamma> M"
    and wf_M: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)"
    and wf_\<delta>x: "wf\<^sub>t\<^sub>r\<^sub>m (\<delta> x)"
    and y_ex: "\<exists>y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). \<Gamma> (Var x) = \<Gamma> (Var y)"
    and t: "t \<sqsubseteq> \<delta> x"
    and \<delta>_wt: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>"
    and t_\<Gamma>: "\<Gamma> t = TComp g T"
    and t_fun: "is_Fun t"
  shows "\<exists>m \<in> set M. \<exists>\<theta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>) \<and> t = m \<cdot> \<theta> \<and> is_Fun m"
proof -
  obtain T'' where T'': "t = Fun g T''" using t_\<Gamma> t_fun fun_type_id_eq by blast

  have g: "arity g > 0" using t_\<Gamma> fun_type_inv[of t] by simp_all

  have "TComp g T \<sqsubseteq> \<Gamma> (Var x)" using \<delta>_wt t t_\<Gamma>
    by (metis wf_\<delta>x subtermeq_imp_subtermtypeeq wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def) 
  then obtain U where U:
      "Fun g U \<in> set M" "\<Gamma> (Fun g U) = TComp g T" "\<forall>u \<in> set U. \<exists>y. u = Var y"
      "distinct U" "length T'' = length U"
    using is_TComp_var_instance_closedD'[OF y_ex _ closed wf_M]
    by (metis t_\<Gamma> T'' fun_type_id_eq fun_type_length_eq is_VarE)
  hence UT': "T = map \<Gamma> U" using fun_type[OF g, of U] by simp

  show ?thesis
    using TComp_var_instance_wt_subst_exists UT' T'' U(1,3,4) t t_\<Gamma> wf_\<delta>x wf_trm_subtermeq
    by (metis term.disc(2))
qed

lemma TComp_var_and_subterm_instance_closed_has_subterms_instances:
  assumes M_var_inst_cl: "is_TComp_var_instance_closed \<Gamma> M"
    and M_subterms_cl: "has_all_wt_instances_of \<Gamma> (subterms\<^sub>s\<^sub>e\<^sub>t (set M)) (set M)"
    and M_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)"
    and t: "t \<sqsubseteq>\<^sub>s\<^sub>e\<^sub>t set M"
    and s: "s \<sqsubseteq> t \<cdot> \<delta>"
    and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
  shows "\<exists>m \<in> set M. \<exists>\<theta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>) \<and> s = m \<cdot> \<theta>"
using subterm_subst_unfold[OF s]
proof
  assume "\<exists>s'. s' \<sqsubseteq> t \<and> s = s' \<cdot> \<delta>"
  then obtain s' where s': "s' \<sqsubseteq> t" "s = s' \<cdot> \<delta>" by blast
  then obtain \<theta> where \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" "s' \<in> set M \<cdot>\<^sub>s\<^sub>e\<^sub>t \<theta>"
    using t has_all_wt_instances_ofD'[OF wf_trms_subterms[OF M_wf] M_wf M_subterms_cl]
          term.order_trans[of s' t]
    by blast
  then obtain m where m: "m \<in> set M" "s' = m \<cdot> \<theta>" by blast

  have "s = m \<cdot> (\<theta> \<circ>\<^sub>s \<delta>)" using s'(2) m(2) by simp
  thus ?thesis
    using m(1) wt_subst_compose[OF \<theta>(1) \<delta>(1)] wf_trms_subst_compose[OF \<theta>(2) \<delta>(2)] by blast
next
  assume "\<exists>x \<in> fv t. s \<sqsubset> \<delta> x"
  then obtain x where x: "x \<in> fv t" "s \<sqsubset> \<delta> x" "s \<sqsubseteq> \<delta> x" by blast

  note 0 = TComp_var_instance_closed_has_Var[OF M_var_inst_cl M_wf]
  note 1 = has_all_wt_instances_ofD''[OF wf_trms_subterms[OF M_wf] M_wf M_subterms_cl]

  have \<delta>x_wf: "wf\<^sub>t\<^sub>r\<^sub>m (\<delta> x)" and s_wf_trm: "wf\<^sub>t\<^sub>r\<^sub>m s"
    using \<delta>(2) wf_trm_subterm[OF _ x(2)] by fastforce+

  have x_fv_ex: "\<exists>y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). \<Gamma> (Var x) = \<Gamma> (Var y)"
    using x(1) s fv_subset_subterms[OF t] by auto

  obtain y where y: "y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M)" "\<Gamma> (Var y) = \<Gamma> s"
    using 0[of \<delta> x s, OF \<delta>x_wf x_fv_ex x(3) \<delta>(1)] by metis
  then obtain z where z: "Var z \<in> set M" "\<Gamma> (Var z) = \<Gamma> s"
    using 1[of y] vars_iff_subtermeq_set[of y "set M"] by metis

  define \<theta> where "\<theta> \<equiv> Var(z := s)::('fun, ('fun, 'atom) term \<times> nat) subst"

  have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" "s = Var z \<cdot> \<theta>"
    using z(2) s_wf_trm unfolding \<theta>_def wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by force+
  thus ?thesis using z(1) by blast
qed

context
begin
private lemma SMP_D_aux1:
  assumes "t \<in> SMP (set M)"
    and closed: "has_all_wt_instances_of \<Gamma> (subterms\<^sub>s\<^sub>e\<^sub>t (set M)) (set M)"
                "is_TComp_var_instance_closed \<Gamma> M"
    and wf_M: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)"
  shows "\<forall>x \<in> fv t. \<exists>y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). \<Gamma> (Var y) = \<Gamma> (Var x)"
using assms(1)
proof (induction t rule: SMP.induct)
  case (MP t) show ?case
  proof
    fix x assume x: "x \<in> fv t"
    hence "Var x \<in> subterms\<^sub>s\<^sub>e\<^sub>t (set M)" using MP.hyps vars_iff_subtermeq by fastforce
    then obtain \<delta> s where \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
        and s: "s \<in> set M" "Var x = s \<cdot> \<delta>"
      using has_all_wt_instances_ofD'[OF wf_trms_subterms[OF wf_M] wf_M closed(1)] by blast
    then obtain y where y: "s = Var y" by (cases s) auto
    thus "\<exists>y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). \<Gamma> (Var y) = \<Gamma> (Var x)"
      using s wt_subst_trm''[OF \<delta>(1), of "Var y"] by force
  qed
next
  case (Subterm t t')
  hence "fv t' \<subseteq> fv t" using subtermeq_vars_subset by auto
  thus ?case using Subterm.IH by auto
next
  case (Substitution t \<delta>)
  note IH = Substitution.IH
  show ?case
  proof
    fix x assume x: "x \<in> fv (t \<cdot> \<delta>)"
    then obtain y where y: "y \<in> fv t" "\<Gamma> (Var x) \<sqsubseteq> \<Gamma> (Var y)"
      using Substitution.hyps(2,3)
      by (metis subst_apply_img_var subtermeqI' subtermeq_imp_subtermtypeeq
                vars_iff_subtermeq wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def wf_trm_subst_rangeD)
    let ?P = "\<lambda>x. \<exists>y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). \<Gamma> (Var y) = \<Gamma> (Var x)"
    show "?P x" using y IH
    proof (induction "\<Gamma> (Var y)" arbitrary: y t)
      case (Var a)
      hence "\<Gamma> (Var x) = \<Gamma> (Var y)" by auto
      thus ?case using Var(2,4) by auto
    next
      case (Fun f T)
      obtain z where z: "\<exists>w \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). \<Gamma> (Var z) = \<Gamma> (Var w)" "\<Gamma> (Var z) = \<Gamma> (Var y)"
        using Fun.prems(1,3) by blast
      show ?case
      proof (cases "\<Gamma> (Var x) = \<Gamma> (Var y)")
        case True thus ?thesis using Fun.prems by auto
      next
        case False
        then obtain \<tau> where \<tau>: "\<tau> \<in> set T" "\<Gamma> (Var x) \<sqsubseteq> \<tau>" using Fun.prems(2) Fun.hyps(2) by auto
        then obtain U where U:
            "Fun f U \<in> set M" "\<Gamma> (Fun f U) = \<Gamma> (Var z)" "\<forall>u \<in> set U. \<exists>v. u = Var v" "distinct U"
          using is_TComp_var_instance_closedD'[OF z(1) _ closed(2) wf_M] Fun.hyps(2) z(2)
          by (metis fun_type_id_eq subtermeqI' is_VarE)
        hence 1: "\<forall>x \<in> fv (Fun f U). \<exists>y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). \<Gamma> (Var y) = \<Gamma> (Var x)" by force

        have "arity f > 0" using U(2) z(2) Fun.hyps(2) fun_type_inv(1) by metis
        hence "\<Gamma> (Fun f U) = TComp f (map \<Gamma> U)" using fun_type by auto
        then obtain u where u: "Var u \<in> set U" "\<Gamma> (Var u) = \<tau>"
          using \<tau>(1) U(2,3) z(2) Fun.hyps(2) by auto
        show ?thesis
          using Fun.hyps(1)[of u "Fun f U"] u \<tau> 1
          by force
      qed
    qed
  qed
next
  case (Ana t K T k)
  have "fv k \<subseteq> fv t" using Ana_keys_fv[OF Ana.hyps(2)] Ana.hyps(3) by auto
  thus ?case using Ana.IH by auto
qed

private lemma SMP_D_aux2:
  fixes t::"('fun, ('fun, 'atom) term \<times> nat) term"
  assumes t_SMP: "t \<in> SMP (set M)"
    and t_Var: "\<exists>x. t = Var x"
    and M_SMP_repr: "finite_SMP_representation arity Ana \<Gamma> M"
  shows "\<exists>m \<in> set M. \<exists>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t = m \<cdot> \<delta>"
proof -
  have M_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)" 
      and M_var_inst_cl: "is_TComp_var_instance_closed \<Gamma> M"
      and M_subterms_cl: "has_all_wt_instances_of \<Gamma> (subterms\<^sub>s\<^sub>e\<^sub>t (set M)) (set M)"
      and M_Ana_cl: "has_all_wt_instances_of \<Gamma> (\<Union>((set \<circ> fst \<circ> Ana) ` set M)) (set M)"
    using finite_SMP_representationD[OF M_SMP_repr] by blast+

  have M_Ana_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (\<Union> ((set \<circ> fst \<circ> Ana) ` set M))"
  proof
    fix k assume "k \<in> \<Union>((set \<circ> fst \<circ> Ana) ` set M)"
    then obtain m where m: "m \<in> set M" "k \<in> set (fst (Ana m))" by force
    thus "wf\<^sub>t\<^sub>r\<^sub>m k" using M_wf Ana_keys_wf'[of m "fst (Ana m)" _ k] surjective_pairing by blast
  qed

  note 0 = has_all_wt_instances_ofD'[OF wf_trms_subterms[OF M_wf] M_wf M_subterms_cl]
  note 1 = has_all_wt_instances_ofD'[OF M_Ana_wf M_wf M_Ana_cl]

  obtain x y where x: "t = Var x" and y: "y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M)" "\<Gamma> (Var y) = \<Gamma> (Var x)"
    using t_Var SMP_D_aux1[OF t_SMP M_subterms_cl M_var_inst_cl M_wf] by fastforce
  then obtain m \<delta> where m: "m \<in> set M" "m \<cdot> \<delta> = Var y" and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>"
    using 0[of "Var y"] vars_iff_subtermeq_set[of y "set M"] by fastforce
  obtain z where z: "m = Var z" using m(2) by (cases m) auto

  define \<theta> where "\<theta> \<equiv> Var(z := Var x)::('fun, ('fun, 'atom) term \<times> nat) subst"

  have "\<Gamma> (Var z) = \<Gamma> (Var x)" using y(2) m(2) z wt_subst_trm''[OF \<delta>, of m] by argo
  hence "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" unfolding \<theta>_def wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by force+
  moreover have "t = m \<cdot> \<theta>" using x z unfolding \<theta>_def by simp
  ultimately show ?thesis using m(1) by blast
qed

private lemma SMP_D_aux3:
  assumes hyps: "t' \<sqsubseteq> t" and wf_t: "wf\<^sub>t\<^sub>r\<^sub>m t" and prems: "is_Fun t'"
    and IH:
      "((\<exists>f. t = Fun f []) \<and> (\<exists>m \<in> set M. \<exists>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t = m \<cdot> \<delta>)) \<or>
       (\<exists>m \<in> set M. \<exists>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t = m \<cdot> \<delta> \<and> is_Fun m)"
    and M_SMP_repr: "finite_SMP_representation arity Ana \<Gamma> M"
  shows "((\<exists>f. t' = Fun f []) \<and> (\<exists>m \<in> set M. \<exists>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t' = m \<cdot> \<delta>)) \<or>
         (\<exists>m \<in> set M. \<exists>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t' = m \<cdot> \<delta> \<and> is_Fun m)"
proof (cases "\<exists>f. t = Fun f [] \<or> t' = Fun f []")
  case True
  have M_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)" 
    and M_var_inst_cl: "is_TComp_var_instance_closed \<Gamma> M"
    and M_subterms_cl: "has_all_wt_instances_of \<Gamma> (subterms\<^sub>s\<^sub>e\<^sub>t (set M)) (set M)"
    and M_Ana_cl: "has_all_wt_instances_of \<Gamma> (\<Union>((set \<circ> fst \<circ> Ana) ` set M)) (set M)"
  using finite_SMP_representationD[OF M_SMP_repr] by blast+

  note 0 = has_all_wt_instances_ofD'[OF wf_trms_subterms[OF M_wf] M_wf M_subterms_cl]
  note 1 = TComp_var_instance_closed_has_Fun[OF M_var_inst_cl M_wf]
  note 2 = TComp_var_and_subterm_instance_closed_has_subterms_instances[
            OF M_var_inst_cl M_subterms_cl M_wf]

  have wf_t': "wf\<^sub>t\<^sub>r\<^sub>m t'" using hyps wf_t wf_trm_subterm by blast

  obtain c where "t = Fun c [] \<or> t' = Fun c []" using True by moura
  thus ?thesis
  proof
    assume c: "t' = Fun c []"
    show ?thesis
    proof (cases "\<exists>f. t = Fun f []")
      case True
      hence "t = t'" using c hyps by force
      thus ?thesis using IH by fast
    next
      case False
      note F = this
      then obtain m \<delta> where m: "m \<in> set M" "t = m \<cdot> \<delta>"
          and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
        using IH by blast

      show ?thesis using subterm_subst_unfold[OF hyps[unfolded m(2)]]
      proof
        assume "\<exists>m'. m' \<sqsubseteq> m \<and> t' = m' \<cdot> \<delta>"
        then obtain m' where m': "m' \<sqsubseteq> m" "t' = m' \<cdot> \<delta>" by moura
        obtain n \<theta> where n: "n \<in> set M" "m' = n \<cdot> \<theta>" and \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
          using 0[of m'] m(1) m'(1) by blast
        have "t' = n \<cdot> (\<theta> \<circ>\<^sub>s \<delta>)" using m'(2) n(2) by auto
        thus ?thesis
          using c n(1) wt_subst_compose[OF \<theta>(1) \<delta>(1)] wf_trms_subst_compose[OF \<theta>(2) \<delta>(2)] by blast
      next
        assume "\<exists>x \<in> fv m. t' \<sqsubset> \<delta> x"
        then obtain x where x: "x \<in> fv m" "t' \<sqsubset> \<delta> x" "t' \<sqsubseteq> \<delta> x" by moura
        have \<delta>x_wf: "wf\<^sub>t\<^sub>r\<^sub>m (\<delta> x)" using \<delta>(2) by fastforce
        
        have x_fv_ex: "\<exists>y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). \<Gamma> (Var x) = \<Gamma> (Var y)" using x m by auto

        show ?thesis
        proof (cases "\<Gamma> t'")
          case (Var a)
          show ?thesis
            using c m 2[OF _ hyps[unfolded m(2)] \<delta>]
            by fast
        next
          case (Fun g S)
          show ?thesis
            using c 1[of \<delta> x t', OF \<delta>x_wf x_fv_ex x(3) \<delta>(1) Fun]
            by blast
        qed
      qed
    qed
  qed (use IH hyps in simp)
next
  case False
  note F = False
  then obtain m \<delta> where m:
      "m \<in> set M" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "t = m \<cdot> \<delta>" "is_Fun m" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
    using IH by moura
  obtain f T where fT: "t' = Fun f T" "arity f > 0" "\<Gamma> t' = TComp f (map \<Gamma> T)"
    using F prems fun_type wf_trm_subtermeq[OF wf_t hyps]
    by (metis is_FunE length_greater_0_conv subtermeqI' wf\<^sub>t\<^sub>r\<^sub>m_def)

  have closed: "has_all_wt_instances_of \<Gamma> (subterms\<^sub>s\<^sub>e\<^sub>t (set M)) (set M)"
               "is_TComp_var_instance_closed \<Gamma> M"
    using M_SMP_repr unfolding finite_SMP_representation_def by metis+

  have M_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)" 
    using finite_SMP_representationD[OF M_SMP_repr] by blast

  show ?thesis
  proof (cases "\<exists>x \<in> fv m. t' \<sqsubseteq> \<delta> x")
    case True
    then obtain x where x: "x \<in> fv m" "t' \<sqsubseteq> \<delta> x" by moura
    have 1: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M)" using m(1) x(1) by auto
    have 2: "is_Fun (\<delta> x)" using prems x(2) by auto
    have 3: "wf\<^sub>t\<^sub>r\<^sub>m (\<delta> x)" using m(5) by (simp add: wf_trm_subst_rangeD)
    have "\<not>(\<exists>f. \<delta> x = Fun f [])" using F x(2) by auto
    hence "\<exists>f T. \<Gamma> (Var x) = TComp f T" using 2 3 m(2)
      by (metis (no_types) fun_type is_FunE length_greater_0_conv subtermeqI' wf\<^sub>t\<^sub>r\<^sub>m_def wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def)
    moreover have "\<exists>f T. \<Gamma> t' = Fun f T"
      using False prems wf_trm_subtermeq[OF wf_t hyps]
      by (metis (no_types) fun_type is_FunE length_greater_0_conv subtermeqI' wf\<^sub>t\<^sub>r\<^sub>m_def)
    ultimately show ?thesis
      using TComp_var_instance_closed_has_Fun 1 x(2) m(2) prems closed 3 M_wf
      by metis
  next
    case False
    then obtain m' where m': "m' \<sqsubseteq> m" "t' = m' \<cdot> \<delta>" "is_Fun m'"
      using hyps m(3) subterm_subst_not_img_subterm
      by blast
    then obtain \<theta> m'' where \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" "m'' \<in> set M" "m' = m'' \<cdot> \<theta>"
      using m(1) has_all_wt_instances_ofD'[OF wf_trms_subterms[OF M_wf] M_wf closed(1)] by blast
    hence t'_m'': "t' = m'' \<cdot> \<theta> \<circ>\<^sub>s \<delta>" using m'(2) by fastforce

    note \<theta>\<delta> = wt_subst_compose[OF \<theta>(1) m(2)] wf_trms_subst_compose[OF \<theta>(2) m(5)]

    show ?thesis
    proof (cases "is_Fun m''")
      case True thus ?thesis using \<theta>(3,4) m'(2,3) m(4) fT t'_m'' \<theta>\<delta> by blast
    next
      case False
      then obtain x where x: "m'' = Var x" by moura
      hence "\<exists>y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M). \<Gamma> (Var x) = \<Gamma> (Var y)" "t' \<sqsubseteq> (\<theta> \<circ>\<^sub>s \<delta>) x"
            "\<Gamma> (Var x) = Fun f (map \<Gamma> T)" "wf\<^sub>t\<^sub>r\<^sub>m ((\<theta> \<circ>\<^sub>s \<delta>) x)"
        using \<theta>\<delta> t'_m'' \<theta>(3) fv_subset[OF \<theta>(3)] fT(3) subst_apply_term.simps(1)[of x "\<theta> \<circ>\<^sub>s \<delta>"]
              wt_subst_trm''[OF \<theta>\<delta>(1), of "Var x"]
        by (fastforce, blast, argo, fastforce)
      thus ?thesis
        using x TComp_var_instance_closed_has_Fun[
                of M "\<theta> \<circ>\<^sub>s \<delta>" x t' f "map \<Gamma> T", OF closed(2) M_wf _ _ _ \<theta>\<delta>(1) fT(3) prems]
        by blast
    qed
  qed
qed

lemma SMP_D:
  assumes "t \<in> SMP (set M)" "is_Fun t"
    and M_SMP_repr: "finite_SMP_representation arity Ana \<Gamma> M"
  shows "((\<exists>f. t = Fun f []) \<and> (\<exists>m \<in> set M. \<exists>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t = m \<cdot> \<delta>)) \<or>
         (\<exists>m \<in> set M. \<exists>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t = m \<cdot> \<delta> \<and> is_Fun m)"
proof -
  have wf_M: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)"
      and closed: "has_all_wt_instances_of \<Gamma> (subterms\<^sub>s\<^sub>e\<^sub>t (set M)) (set M)"
                  "has_all_wt_instances_of \<Gamma> (\<Union>((set \<circ> fst \<circ> Ana) ` set M)) (set M)"
                  "is_TComp_var_instance_closed \<Gamma> M"
    using finite_SMP_representationD[OF M_SMP_repr] by blast+

  show ?thesis using assms(1,2)
  proof (induction t rule: SMP.induct)
    case (MP t)
    moreover have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t Var" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range Var)" "t = t \<cdot> Var" by simp_all
    ultimately show ?case by blast 
  next
    case (Subterm t t')
    hence t_fun: "is_Fun t" by auto
    note * = Subterm.hyps(2) SMP_wf_trm[OF Subterm.hyps(1) wf_M(1)]
             Subterm.prems Subterm.IH[OF t_fun] M_SMP_repr
    show ?case by (rule SMP_D_aux3[OF *])
  next
    case (Substitution t \<delta>)
    have wf: "wf\<^sub>t\<^sub>r\<^sub>m t" by (metis Substitution.hyps(1) wf_M(1) SMP_wf_trm)
    hence wf': "wf\<^sub>t\<^sub>r\<^sub>m (t \<cdot> \<delta>)" using Substitution.hyps(3) wf_trm_subst by blast
    show ?case
    proof (cases "\<Gamma> t")
      case (Var a)
      hence 1: "\<Gamma> (t \<cdot> \<delta>) = TAtom a" using Substitution.hyps(2) by (metis wt_subst_trm'') 
      then obtain c where c: "t \<cdot> \<delta> = Fun c []"
        using TAtom_term_cases[OF wf' 1] Substitution.prems by fastforce
      hence "(\<exists>x. t = Var x) \<or> t = t \<cdot> \<delta>" by (cases t) auto
      thus ?thesis
      proof
        assume t_Var: "\<exists>x. t = Var x"
        then obtain x where x: "t = Var x" "\<delta> x = Fun c []" "\<Gamma> (Var x) = TAtom a"
          using c 1 wt_subst_trm''[OF Substitution.hyps(2), of t] by force
        
        obtain m \<theta> where m: "m \<in> set M" "t = m \<cdot> \<theta>" and \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
          using SMP_D_aux2[OF Substitution.hyps(1) t_Var M_SMP_repr] by moura

        have "m \<cdot> (\<theta> \<circ>\<^sub>s \<delta>) = Fun c []" using c m(2) by auto
        thus ?thesis
          using c m(1) wt_subst_compose[OF \<theta>(1) Substitution.hyps(2)]
                wf_trms_subst_compose[OF \<theta>(2) Substitution.hyps(3)]
          by metis
      qed (use c Substitution.IH in auto)
    next
      case (Fun f T)
      hence 1: "\<Gamma> (t \<cdot> \<delta>) = TComp f T" using Substitution.hyps(2) by (metis wt_subst_trm'')
      have 2: "\<not>(\<exists>f. t = Fun f [])" using Fun TComp_term_cases[OF wf] by auto
      obtain T'' where T'': "t \<cdot> \<delta> = Fun f T''"
        using 1 2 fun_type_id_eq Fun Substitution.prems
        by fastforce
      have f: "arity f > 0" "public f" using fun_type_inv[OF 1] by metis+
  
      show ?thesis
      proof (cases t)
        case (Fun g U)
        then obtain m \<theta> where m:
            "m \<in> set M" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "t = m \<cdot> \<theta>" "is_Fun m" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
          using Substitution.IH Fun 2 by moura
        have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<theta> \<circ>\<^sub>s \<delta>)" "t \<cdot> \<delta> = m \<cdot> (\<theta> \<circ>\<^sub>s \<delta>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<theta> \<circ>\<^sub>s \<delta>))"
          using wt_subst_compose[OF m(2) Substitution.hyps(2)] m(3)
                wf_trms_subst_compose[OF m(5) Substitution.hyps(3)]
          by auto
        thus ?thesis using m(1,4) by metis
      next
        case (Var x)
        then obtain y where y: "y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M)" "\<Gamma> (Var y) = \<Gamma> (Var x)"
          using SMP_D_aux1[OF Substitution.hyps(1) closed(1,3) wf_M] Fun
          by moura
        hence 3: "\<Gamma> (Var y) = TComp f T" using Var Fun \<Gamma>_Var_fst by simp
        
        obtain h V where V:
            "Fun h V \<in> set M" "\<Gamma> (Fun h V) = \<Gamma> (Var y)" "\<forall>u \<in> set V. \<exists>z. u = Var z" "distinct V"
          by (metis is_VarE is_TComp_var_instance_closedD[OF _ 3 closed(3)] y(1))
        moreover have "length T'' = length V" using 3 V(2) fun_type_length_eq 1 T'' by metis
        ultimately have TV: "T = map \<Gamma> V"
          by (metis fun_type[OF f(1)] 3 fun_type_id_eq term.inject(2))
  
        obtain \<theta> where \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" "t \<cdot> \<delta> = Fun h V \<cdot> \<theta>"
          using TComp_var_instance_wt_subst_exists 1 3 T'' TV V(2,3,4) wf'
          by (metis fun_type_id_eq)
  
        have 9: "\<Gamma> (Fun h V) = \<Gamma> (\<delta> x)" using y(2) Substitution.hyps(2) V(2) 1 3 Var by auto
  
        show ?thesis using Var \<theta> 9 V(1) by force
      qed
    qed
  next
    case (Ana t K T k)
    have 1: "is_Fun t" using Ana.hyps(2,3) by auto
    then obtain f U where U: "t = Fun f U" by moura
  
    have 2: "fv k \<subseteq> fv t" using Ana_keys_fv[OF Ana.hyps(2)] Ana.hyps(3) by auto
  
    have wf_t: "wf\<^sub>t\<^sub>r\<^sub>m t"
      using SMP_wf_trm[OF Ana.hyps(1)] wf\<^sub>t\<^sub>r\<^sub>m_code wf_M
      by auto
    hence wf_k: "wf\<^sub>t\<^sub>r\<^sub>m k"
      using Ana_keys_wf'[OF Ana.hyps(2)] wf\<^sub>t\<^sub>r\<^sub>m_code Ana.hyps(3)
      by auto
  
    have wf_M_keys: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (\<Union>((set \<circ> fst \<circ> Ana) ` set M))"
    proof
      fix t assume "t \<in> (\<Union>((set \<circ> fst \<circ> Ana) ` set M))"
      then obtain s where s: "s \<in> set M" "t \<in> (set \<circ> fst \<circ> Ana) s" by blast
      obtain K R where KR: "Ana s = (K,R)" by (metis surj_pair)
      hence "t \<in> set K" using s(2) by simp
      thus "wf\<^sub>t\<^sub>r\<^sub>m t" using Ana_keys_wf'[OF KR] wf_M s(1) by blast
    qed
  
    show ?case using Ana_subst'_or_Ana_keys_subterm
    proof
      assume "\<forall>t K T k. Ana t = (K, T) \<longrightarrow> k \<in> set K \<longrightarrow> k \<sqsubset> t"
      hence *: "k \<sqsubseteq> t" using Ana.hyps(2,3) by auto
      show ?thesis by (rule SMP_D_aux3[OF * wf_t Ana.prems Ana.IH[OF 1] M_SMP_repr])
    next
      assume Ana_subst':
          "\<forall>f T \<delta> K M. Ana (Fun f T) = (K, M) \<longrightarrow> Ana (Fun f T \<cdot> \<delta>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>, M \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)"
  
      have "arity f > 0" using Ana_const[of f U] U Ana.hyps(2,3) by fastforce
      hence "U \<noteq> []" using wf_t U unfolding wf\<^sub>t\<^sub>r\<^sub>m_def by force
      then obtain m \<delta> where m: "m \<in> set M" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)" "t = m \<cdot> \<delta>" "is_Fun m"
        using Ana.IH[OF 1] U by auto
      hence "Ana (t \<cdot> \<delta>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>,T \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)" using Ana_subst' U Ana.hyps(2) by auto
      obtain Km Tm where Ana_m: "Ana m = (Km,Tm)" by moura
      hence "Ana (m \<cdot> \<delta>) = (Km \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>,Tm \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)"
        using Ana_subst' U m(4) is_FunE[OF m(5)] Ana.hyps(2)
        by metis
      then obtain km where km: "km \<in> set Km" "k = km \<cdot> \<delta>" using Ana.hyps(2,3) m(4) by auto
      then obtain \<theta> km' where \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
          and km': "km' \<in> set M" "km = km' \<cdot> \<theta>"
        using Ana_m m(1) has_all_wt_instances_ofD'[OF wf_M_keys wf_M closed(2), of km] by force
  
      have k\<theta>\<delta>: "k = km' \<cdot> \<theta> \<circ>\<^sub>s \<delta>" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t (\<theta> \<circ>\<^sub>s \<delta>)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range (\<theta> \<circ>\<^sub>s \<delta>))"
        using km(2) km' wt_subst_compose[OF \<theta>(1) m(2)] wf_trms_subst_compose[OF \<theta>(2) m(3)]
        by auto
  
      show ?case
      proof (cases "is_Fun km'")
        case True thus ?thesis using k\<theta>\<delta> km'(1) by blast
      next
        case False
        note F = False
        then obtain x where x: "km' = Var x" by auto
        hence 3: "x \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M)" using fv_subset[OF km'(1)] by auto
        obtain kf kT where kf: "k = Fun kf kT" using Ana.prems by auto
        show ?thesis
        proof (cases "kT = []")
          case True thus ?thesis using k\<theta>\<delta>(1) k\<theta>\<delta>(2) k\<theta>\<delta>(3) kf km'(1) by blast
        next
          case False
          hence 4: "arity kf > 0" using wf_k kf TAtom_term_cases const_type by fastforce
          then obtain kT' where kT': "\<Gamma> k = TComp kf kT'" by (simp add: fun_type kf) 
          then obtain V where V:
              "Fun kf V \<in> set M" "\<Gamma> (Fun kf V) = \<Gamma> (Var x)" "\<forall>u \<in> set V. \<exists>v. u = Var v"
              "distinct V" "is_Fun (Fun kf V)"
            using is_TComp_var_instance_closedD[OF _ _ closed(3), of x]
                  x m(2) k\<theta>\<delta>(1) 3 wt_subst_trm''[OF k\<theta>\<delta>(2)]
            by (metis fun_type_id_eq term.disc(2) is_VarE)
          have 5: "kT' = map \<Gamma> V"
            using fun_type[OF 4] x kT' k\<theta>\<delta> m(2) V(2)
            by (metis term.inject(2) wt_subst_trm'')
          thus ?thesis
            using TComp_var_instance_wt_subst_exists wf_k kf 4 V(3,4) kT' V(1,5)
            by metis
        qed
      qed
    qed
  qed
qed

lemma SMP_D':
  fixes M
  defines "\<delta> \<equiv> var_rename (max_var_set (fv\<^sub>s\<^sub>e\<^sub>t (set M)))"
  assumes M_SMP_repr: "finite_SMP_representation arity Ana \<Gamma> M"
    and s: "s \<in> SMP (set M)" "is_Fun s" "\<nexists>f. s = Fun f []"
    and t: "t \<in> SMP (set M)" "is_Fun t" "\<nexists>f. t = Fun f []"
  obtains \<sigma> s0 \<theta> t0
  where "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>)" "s0 \<in> set M" "is_Fun s0" "s = s0 \<cdot> \<sigma>" "\<Gamma> s = \<Gamma> s0"
    and "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" "t0 \<in> set M" "is_Fun t0" "t = t0 \<cdot> \<delta> \<cdot> \<theta>" "\<Gamma> t = \<Gamma> t0"
proof -
  obtain \<sigma> s0 where
      s0: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>)" "s0 \<in> set M" "s = s0 \<cdot> \<sigma>" "is_Fun s0"
    using s(3) SMP_D[OF s(1,2) M_SMP_repr] unfolding \<delta>_def by metis

  obtain \<theta> t0 where t0:
      "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" "t0 \<in> set M" "t = t0 \<cdot> \<delta> \<cdot> \<theta>" "is_Fun t0"
    using t(3) SMP_D[OF t(1,2) M_SMP_repr] var_rename_wt'[of _ t]
          wf_trms_subst_compose_Var_range(1)[OF _ var_rename_is_renaming(2)]
    unfolding \<delta>_def by metis

  have "\<Gamma> s = \<Gamma> s0" "\<Gamma> t = \<Gamma> (t0 \<cdot> \<delta>)" "\<Gamma> (t0 \<cdot> \<delta>) = \<Gamma> t0"
    using s0 t0 wt_subst_trm'' by (metis, metis, metis \<delta>_def var_rename_wt(1))
  thus ?thesis using s0 t0 that by simp
qed

lemma SMP_D'':
  fixes t::"('fun, ('fun, 'atom) term \<times> nat) term"
  assumes t_SMP: "t \<in> SMP (set M)"
    and M_SMP_repr: "finite_SMP_representation arity Ana \<Gamma> M"
  shows "\<exists>m \<in> set M. \<exists>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> t = m \<cdot> \<delta>"
proof (cases "(\<exists>x. t = Var x) \<or> (\<exists>c. t = Fun c [])")
  case True
  have M_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)" 
      and M_var_inst_cl: "is_TComp_var_instance_closed \<Gamma> M"
      and M_subterms_cl: "has_all_wt_instances_of \<Gamma> (subterms\<^sub>s\<^sub>e\<^sub>t (set M)) (set M)"
      and M_Ana_cl: "has_all_wt_instances_of \<Gamma> (\<Union>((set \<circ> fst \<circ> Ana) ` set M)) (set M)"
    using finite_SMP_representationD[OF M_SMP_repr] by blast+

  have M_Ana_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (\<Union> ((set \<circ> fst \<circ> Ana) ` set M))"
  proof
    fix k assume "k \<in> \<Union>((set \<circ> fst \<circ> Ana) ` set M)"
    then obtain m where m: "m \<in> set M" "k \<in> set (fst (Ana m))" by force
    thus "wf\<^sub>t\<^sub>r\<^sub>m k" using M_wf Ana_keys_wf'[of m "fst (Ana m)" _ k] surjective_pairing by blast
  qed

  show ?thesis using True
  proof
    assume "\<exists>x. t = Var x"
    then obtain x y where x: "t = Var x" and y: "y \<in> fv\<^sub>s\<^sub>e\<^sub>t (set M)" "\<Gamma> (Var y) = \<Gamma> (Var x)"
      using SMP_D_aux1[OF t_SMP M_subterms_cl M_var_inst_cl M_wf] by fastforce
    then obtain m \<delta> where m: "m \<in> set M" "m \<cdot> \<delta> = Var y" and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>"
      using has_all_wt_instances_ofD'[OF wf_trms_subterms[OF M_wf] M_wf M_subterms_cl, of "Var y"]
            vars_iff_subtermeq_set[of y "set M"]
      by fastforce

    obtain z where z: "m = Var z" using m(2) by (cases m) auto

    define \<theta> where "\<theta> \<equiv> Var(z := Var x)::('fun, ('fun, 'atom) term \<times> nat) subst"

    have "\<Gamma> (Var z) = \<Gamma> (Var x)" using y(2) m(2) z wt_subst_trm''[OF \<delta>, of m] by argo
    hence "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)" unfolding \<theta>_def wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t_def by force+
    moreover have "t = m \<cdot> \<theta>" using x z unfolding \<theta>_def by simp
    ultimately show ?thesis using m(1) by blast
  qed (use SMP_D[OF t_SMP _ M_SMP_repr] in blast)
qed (use SMP_D[OF t_SMP _ M_SMP_repr] in blast)
end

lemma tfr\<^sub>s\<^sub>e\<^sub>t_if_comp_tfr\<^sub>s\<^sub>e\<^sub>t:
  assumes "comp_tfr\<^sub>s\<^sub>e\<^sub>t arity Ana \<Gamma> M"
  shows "tfr\<^sub>s\<^sub>e\<^sub>t (set M)"
proof -
  let ?\<delta> = "var_rename (max_var_set (fv\<^sub>s\<^sub>e\<^sub>t (set M)))"
  have M_SMP_repr: "finite_SMP_representation arity Ana \<Gamma> M"
    by (metis comp_tfr\<^sub>s\<^sub>e\<^sub>t_def assms)

  have M_finite: "finite (set M)"
    using assms card_gt_0_iff unfolding comp_tfr\<^sub>s\<^sub>e\<^sub>t_def by blast

  show ?thesis
  proof (unfold tfr\<^sub>s\<^sub>e\<^sub>t_def; intro ballI impI)
    fix s t assume "s \<in> SMP (set M) - Var`\<V>" "t \<in> SMP (set M) - Var`\<V>"
    hence st: "s \<in> SMP (set M)" "is_Fun s" "t \<in> SMP (set M)" "is_Fun t" by auto
    have "\<not>(\<exists>\<delta>. Unifier \<delta> s t)" when st_type_neq: "\<Gamma> s \<noteq> \<Gamma> t"
    proof (cases "\<exists>f. s = Fun f [] \<or> t = Fun f []")
      case False
      then obtain \<sigma> s0 \<theta> t0 where
            s0: "s0 \<in> set M" "is_Fun s0" "s = s0 \<cdot> \<sigma>" "\<Gamma> s = \<Gamma> s0"
        and t0: "t0 \<in> set M" "is_Fun t0" "t = t0 \<cdot> ?\<delta> \<cdot> \<theta>" "\<Gamma> t = \<Gamma> t0"
        using SMP_D'[OF M_SMP_repr st(1,2) _ st(3,4)] by metis
      hence "\<not>(\<exists>\<delta>. Unifier \<delta> s0 (t0 \<cdot> ?\<delta>))"
        using assms mgu_None_is_subst_neq st_type_neq wt_subst_trm''[OF var_rename_wt(1)]
        unfolding comp_tfr\<^sub>s\<^sub>e\<^sub>t_def Let_def by metis
      thus ?thesis
        using vars_term_disjoint_imp_unifier[OF var_rename_fv_set_disjoint[OF M_finite]] s0(1) t0(1)
        unfolding s0(3) t0(3) by (metis (no_types, hide_lams) subst_subst_compose)
    qed (use st_type_neq st(2,4) in auto)
    thus "\<Gamma> s = \<Gamma> t" when "\<exists>\<delta>. Unifier \<delta> s t" by (metis that)
  qed
qed

lemma tfr\<^sub>s\<^sub>e\<^sub>t_if_comp_tfr\<^sub>s\<^sub>e\<^sub>t':
  assumes "let N = SMP0 Ana \<Gamma> M in set M \<subseteq> set N \<and> comp_tfr\<^sub>s\<^sub>e\<^sub>t arity Ana \<Gamma> N"
  shows "tfr\<^sub>s\<^sub>e\<^sub>t (set M)"
by (rule tfr_subset(2)[
          OF tfr\<^sub>s\<^sub>e\<^sub>t_if_comp_tfr\<^sub>s\<^sub>e\<^sub>t[OF conjunct2[OF assms[unfolded Let_def]]]
             conjunct1[OF assms[unfolded Let_def]]])

lemma tfr\<^sub>s\<^sub>t\<^sub>p_is_comp_tfr\<^sub>s\<^sub>t\<^sub>p: "tfr\<^sub>s\<^sub>t\<^sub>p a = comp_tfr\<^sub>s\<^sub>t\<^sub>p \<Gamma> a"
proof (cases a)
  case (Equality ac t t')
  thus ?thesis
    using mgu_always_unifies[of t _ t'] mgu_gives_MGU[of t t']
    by auto
next
  case (Inequality X F)
  thus ?thesis
    using tfr\<^sub>s\<^sub>t\<^sub>p.simps(2)[of X F]
          comp_tfr\<^sub>s\<^sub>t\<^sub>p.simps(2)[of \<Gamma> X F]
          Fun_range_case(2)[of "subterms\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>p\<^sub>a\<^sub>i\<^sub>r\<^sub>s F)"] 
    unfolding is_Var_def
    by auto
qed auto

lemma tfr\<^sub>s\<^sub>t_if_comp_tfr\<^sub>s\<^sub>t:
  assumes "comp_tfr\<^sub>s\<^sub>t arity Ana \<Gamma> M S"
  shows "tfr\<^sub>s\<^sub>t S"
unfolding tfr\<^sub>s\<^sub>t_def
proof
  have comp_tfr\<^sub>s\<^sub>e\<^sub>t_M: "comp_tfr\<^sub>s\<^sub>e\<^sub>t arity Ana \<Gamma> M"
    using assms unfolding comp_tfr\<^sub>s\<^sub>t_def by blast
  
  have wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_M: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)"
      and wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_S: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (trms\<^sub>s\<^sub>t S)"
      and S_trms_instance_M: "has_all_wt_instances_of \<Gamma> (trms\<^sub>s\<^sub>t S) (set M)"
    using assms wf\<^sub>t\<^sub>r\<^sub>m_code trms_list\<^sub>s\<^sub>t_is_trms\<^sub>s\<^sub>t
    unfolding comp_tfr\<^sub>s\<^sub>t_def comp_tfr\<^sub>s\<^sub>e\<^sub>t_def finite_SMP_representation_def list_all_iff
    by blast+

  show "tfr\<^sub>s\<^sub>e\<^sub>t (trms\<^sub>s\<^sub>t S)"
    using tfr_subset(3)[OF tfr\<^sub>s\<^sub>e\<^sub>t_if_comp_tfr\<^sub>s\<^sub>e\<^sub>t[OF comp_tfr\<^sub>s\<^sub>e\<^sub>t_M] SMP_SMP_subset]
          SMP_I'[OF wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_S wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s_M S_trms_instance_M]
    by blast

  have "list_all (comp_tfr\<^sub>s\<^sub>t\<^sub>p \<Gamma>) S" by (metis assms comp_tfr\<^sub>s\<^sub>t_def)
  thus "list_all tfr\<^sub>s\<^sub>t\<^sub>p S" by (induct S) (simp_all add: tfr\<^sub>s\<^sub>t\<^sub>p_is_comp_tfr\<^sub>s\<^sub>t\<^sub>p)
qed

lemma tfr\<^sub>s\<^sub>t_if_comp_tfr\<^sub>s\<^sub>t':
  assumes "comp_tfr\<^sub>s\<^sub>t arity Ana \<Gamma> (SMP0 Ana \<Gamma> (trms_list\<^sub>s\<^sub>t S)) S"
  shows "tfr\<^sub>s\<^sub>t S"
by (rule tfr\<^sub>s\<^sub>t_if_comp_tfr\<^sub>s\<^sub>t[OF assms])



subsubsection \<open>Lemmata for Checking Ground SMP (GSMP) Disjointness\<close>
context
begin
private lemma ground_SMP_disjointI_aux1:
  fixes M::"('fun, ('fun, 'atom) term \<times> nat) term set"
  assumes f_def: "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
    and g_def: "g \<equiv> \<lambda>M. {t \<in> M. fv t = {}}"
  shows "f (SMP M) = g (SMP M)"
proof
  have "t \<in> f (SMP M)" when t: "t \<in> SMP M" "fv t = {}" for t
  proof -
    define \<delta> where "\<delta> \<equiv> Var::('fun, ('fun, 'atom) term \<times> nat) subst"
    have "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)" "t = t \<cdot> \<delta>"
      using subst_apply_term_empty[of t] that(2) wt_subst_Var wf_trm_subst_range_Var
      unfolding \<delta>_def by auto
    thus ?thesis using SMP.Substitution[OF t(1), of \<delta>] t(2) unfolding f_def by fastforce
  qed
  thus "g (SMP M) \<subseteq> f (SMP M)" unfolding g_def by blast
qed (use f_def g_def in blast)

private lemma ground_SMP_disjointI_aux2:
  fixes M::"('fun, ('fun, 'atom) term \<times> nat) term list"
  assumes f_def: "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
    and M_SMP_repr: "finite_SMP_representation arity Ana \<Gamma> M"
  shows "f (set M) = f (SMP (set M))"
proof
  have M_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set M)" 
      and M_var_inst_cl: "is_TComp_var_instance_closed \<Gamma> M"
      and M_subterms_cl: "has_all_wt_instances_of \<Gamma> (subterms\<^sub>s\<^sub>e\<^sub>t (set M)) (set M)"
      and M_Ana_cl: "has_all_wt_instances_of \<Gamma> (\<Union>((set \<circ> fst \<circ> Ana) ` set M)) (set M)"
    using finite_SMP_representationD[OF M_SMP_repr] by blast+

  show "f (SMP (set M)) \<subseteq> f (set M)"
  proof
    fix t assume "t \<in> f (SMP (set M))"
    then obtain s \<delta> where s: "t = s \<cdot> \<delta>" "s \<in> SMP (set M)" "fv (s \<cdot> \<delta>) = {}"
        and \<delta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>)"
      unfolding f_def by blast

    have t_wf: "wf\<^sub>t\<^sub>r\<^sub>m t" using SMP_wf_trm[OF s(2) M_wf] s(1) wf_trm_subst[OF \<delta>(2)] by blast 

    obtain m \<theta> where m: "m \<in> set M" "s = m \<cdot> \<theta>" and \<theta>: "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
      using SMP_D''[OF s(2) M_SMP_repr] by blast

    have "t = m \<cdot> (\<theta> \<circ>\<^sub>s \<delta>)" "fv (m \<cdot> (\<theta> \<circ>\<^sub>s \<delta>)) = {}" using s(1,3) m(2) by simp_all
    thus "t \<in> f (set M)"
      using m(1) wt_subst_compose[OF \<theta>(1) \<delta>(1)] wf_trms_subst_compose[OF \<theta>(2) \<delta>(2)]
      unfolding f_def by blast
  qed
qed (auto simp add: f_def)

private lemma ground_SMP_disjointI_aux3:
  fixes A B C::"('fun, ('fun, 'atom) term \<times> nat) term set"
  defines "P \<equiv> \<lambda>t s. \<exists>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> Unifier \<delta> t s"
  assumes f_def: "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
    and Q_def: "Q \<equiv> \<lambda>t. intruder_synth' public arity {} t"
    and R_def: "R \<equiv> \<lambda>t. \<exists>u \<in> C. is_wt_instance_of_cond \<Gamma> t u"
    and AB: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s A" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s B" "fv\<^sub>s\<^sub>e\<^sub>t A \<inter> fv\<^sub>s\<^sub>e\<^sub>t B = {}"
    and C: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s C"
    and ABC: "\<forall>t \<in> A. \<forall>s \<in> B. P t s \<longrightarrow> (Q t \<and> Q s) \<or> (R t \<and> R s)"
  shows "f A \<inter> f B \<subseteq> f C \<union> {m. {} \<turnstile>\<^sub>c m}"
proof
  fix t assume "t \<in> f A \<inter> f B"
  then obtain ta tb \<delta>a \<delta>b where
          ta: "t = ta \<cdot> \<delta>a" "ta \<in> A" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>a" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>a)" "fv (ta \<cdot> \<delta>a) = {}"
      and tb: "t = tb \<cdot> \<delta>b" "tb \<in> B" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta>b" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>b)" "fv (tb \<cdot> \<delta>b) = {}"
    unfolding f_def by blast

  have ta_tb_wf: "wf\<^sub>t\<^sub>r\<^sub>m ta" "wf\<^sub>t\<^sub>r\<^sub>m tb" "fv ta \<inter> fv tb = {}" "\<Gamma> ta = \<Gamma> tb"
    using ta(1,2) tb(1,2) AB fv_subset_subterms
          wt_subst_trm''[OF ta(3), of ta] wt_subst_trm''[OF tb(3), of tb]
    by (fast, fast, blast, simp)

  obtain \<theta> where \<theta>: "Unifier \<theta> ta tb" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<theta>" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<theta>)"
    using vars_term_disjoint_imp_unifier[OF ta_tb_wf(3), of \<delta>a \<delta>b]
          ta(1) tb(1) wt_Unifier_if_Unifier[OF ta_tb_wf(1,2,4)]
    by blast
  hence "(Q ta \<and> Q tb) \<or> (R ta \<and> R tb)" using ABC ta(2) tb(2) unfolding P_def by blast+
  thus "t \<in> f C \<union> {m. {} \<turnstile>\<^sub>c m}"
  proof
    show "Q ta \<and> Q tb \<Longrightarrow> ?thesis"
      using ta(1) pgwt_ground[of ta] pgwt_is_empty_synth[of ta] subst_ground_ident[of ta \<delta>a]
      unfolding Q_def f_def intruder_synth_code[symmetric] by simp
  next
    assume "R ta \<and> R tb"
    then obtain ua \<sigma>a where ua: "ta = ua \<cdot> \<sigma>a" "ua \<in> C" "wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<sigma>a" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<sigma>a)"
      using \<theta> ABC ta_tb_wf(1,2) ta(2) tb(2) C is_wt_instance_of_condD'
      unfolding P_def R_def by metis
  
    have "t = ua \<cdot> (\<sigma>a \<circ>\<^sub>s \<delta>a)" "fv t = {}"
      using ua(1) ta(1,5) tb(1,5) by auto
    thus ?thesis
      using ua(2) wt_subst_compose[OF ua(3) ta(3)] wf_trms_subst_compose[OF ua(4) ta(4)]
      unfolding f_def by blast
  qed
qed

lemma ground_SMP_disjointI:
  fixes A B::"('fun, ('fun, 'atom) term \<times> nat) term list" and C
  defines "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
    and "g \<equiv> \<lambda>M. {t \<in> M. fv t = {}}"
    and "Q \<equiv> \<lambda>t. intruder_synth' public arity {} t"
    and "R \<equiv> \<lambda>t. \<exists>u \<in> C. is_wt_instance_of_cond \<Gamma> t u"
  assumes AB_fv_disj: "fv\<^sub>s\<^sub>e\<^sub>t (set A) \<inter> fv\<^sub>s\<^sub>e\<^sub>t (set B) = {}"
    and A_SMP_repr: "finite_SMP_representation arity Ana \<Gamma> A"
    and B_SMP_repr: "finite_SMP_representation arity Ana \<Gamma> B"
    and C_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s C"
    and ABC: "\<forall>t \<in> set A. \<forall>s \<in> set B. \<Gamma> t = \<Gamma> s \<and> mgu t s \<noteq> None \<longrightarrow> (Q t \<and> Q s) \<or> (R t \<and> R s)"
  shows "g (SMP (set A)) \<inter> g (SMP (set B)) \<subseteq> f C \<union> {m. {} \<turnstile>\<^sub>c m}"
proof -
  have AB_wf: "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set A)" "wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (set B)"
    using A_SMP_repr B_SMP_repr
    unfolding finite_SMP_representation_def wf\<^sub>t\<^sub>r\<^sub>m_code list_all_iff
    by blast+

  let ?P = "\<lambda>t s. \<exists>\<delta>. wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> Unifier \<delta> t s"
  have ABC': "\<forall>t \<in> set A. \<forall>s \<in> set B. ?P t s \<longrightarrow> (Q t \<and> Q s) \<or> (R t \<and> R s)"
    by (metis (no_types) ABC mgu_None_is_subst_neq wt_subst_trm'')

  show ?thesis
    using ground_SMP_disjointI_aux1[OF f_def g_def, of "set A"]
          ground_SMP_disjointI_aux1[OF f_def g_def, of "set B"]
          ground_SMP_disjointI_aux2[OF f_def A_SMP_repr]
          ground_SMP_disjointI_aux2[OF f_def B_SMP_repr]
          ground_SMP_disjointI_aux3[OF f_def Q_def R_def AB_wf AB_fv_disj C_wf ABC']
    by argo
qed

end

end

end
