section\<open>Cofinality\label{sec:cofinality}\<close>

theory Cofinality
  imports
    ZF_Library
begin


subsection\<open>Basic results and definitions\<close>

text\<open>A set \<^term>\<open>X\<close> is \<^emph>\<open>cofinal\<close> in \<^term>\<open>A\<close> (with respect to the relation
    \<^term>\<open>r\<close>) if every element of \<^term>\<open>A\<close> is “bounded
    above” by some element of \<^term>\<open>X\<close>. Note that \<^term>\<open>X\<close> does not need 
    to be a subset of \<^term>\<open>A\<close>.\<close>
definition
  cofinal :: "[i,i,i] \<Rightarrow> o" where
  "cofinal(X,A,r) \<equiv> \<forall>a\<in>A. \<exists>x\<in>X. \<langle>a,x\<rangle>\<in>r \<or> a = x"

(*
(* Alternative definitions *)
definition
  cofinal_predic :: "[i,i,[i,i]\<Rightarrow>o] \<Rightarrow> o" where
  "cofinal_predic(X,A,r) \<equiv> \<forall>a\<in>A. \<exists>x\<in>X. r(a,x) \<or> a = x"

definition
  f_cofinal :: "[i\<Rightarrow>i,i,i,i] \<Rightarrow> o" where
  "f_cofinal(f,C,A,r) \<equiv> \<forall>a\<in>A. \<exists>x\<in>C. \<langle>a,f(x)\<rangle>\<in>r \<or> a = f(x)"

(* The next definition doesn't work if 0 is the top element of A.
   But it works for limit ordinals. *)
definition
  cofinal_fun' :: "[i,i,i] \<Rightarrow> o" where
  "cofinal_fun'(f,A,r) == f_cofinal(\<lambda>x. f`x,domain(f),A, r)"
*)

text\<open>A function is cofinal if it range is.\<close>
definition
  cofinal_fun :: "[i,i,i] \<Rightarrow> o" where
  "cofinal_fun(f,A,r) \<equiv> \<forall>a\<in>A. \<exists>x\<in>domain(f). \<langle>a,f`x\<rangle>\<in>r \<or> a = f`x"

lemma cofinal_funI:
  assumes "\<And>a. a\<in>A \<Longrightarrow> \<exists>x\<in>domain(f). \<langle>a,f`x\<rangle>\<in>r \<or> a = f`x"
  shows "cofinal_fun(f,A,r)"
  using assms unfolding cofinal_fun_def by simp

lemma cofinal_funD:
  assumes "cofinal_fun(f,A,r)" "a\<in>A"
  shows "\<exists>x\<in>domain(f). \<langle>a,f`x\<rangle>\<in>r \<or> a = f`x"
  using assms unfolding cofinal_fun_def by simp

lemma cofinal_in_cofinal:
  assumes
    "trans(r)" "cofinal(Y,X,r)" "cofinal(X,A,r)"
  shows
    "cofinal(Y,A,r)"
  unfolding cofinal_def
proof
  fix a
  assume "a\<in>A"
  moreover from \<open>cofinal(X,A,r)\<close>
  have "b\<in>A\<Longrightarrow>\<exists>x\<in>X. \<langle>b,x\<rangle>\<in>r \<or> b=x" for b
    unfolding cofinal_def by simp
  ultimately
  obtain y where "y\<in>X" "\<langle>a,y\<rangle>\<in>r \<or> a=y" by auto
  moreover from \<open>cofinal(Y,X,r)\<close>
  have "c\<in>X\<Longrightarrow>\<exists>y\<in>Y. \<langle>c,y\<rangle>\<in>r \<or> c=y" for c
    unfolding cofinal_def by simp
  ultimately
  obtain x where "x\<in>Y" "\<langle>y,x\<rangle>\<in>r \<or> y=x" by auto
  with \<open>a\<in>A\<close> \<open>y\<in>X\<close> \<open>\<langle>a,y\<rangle>\<in>r \<or> a=y\<close> \<open>trans(r)\<close>
  show "\<exists>x\<in>Y. \<langle>a,x\<rangle>\<in>r \<or> a=x" unfolding trans_def by auto
qed

lemma codomain_is_cofinal:
  assumes "cofinal_fun(f,A,r)" "f:C \<rightarrow> D"
  shows "cofinal(D,A,r)"
  unfolding cofinal_def
proof
  fix b
  assume "b \<in> A"
  moreover from assms
  have "a\<in>A \<Longrightarrow> \<exists>x\<in>domain(f). \<langle>a, f ` x\<rangle> \<in> r \<or> a = f`x" for a
    unfolding cofinal_fun_def by simp
  ultimately
  obtain x where "x\<in>domain(f)" "\<langle>b, f ` x\<rangle> \<in> r \<or> b = f`x"
    by blast
  moreover from \<open>f:C \<rightarrow> D\<close>  \<open>x\<in>domain(f)\<close>
  have "f`x\<in>D"
    using domain_of_fun apply_rangeI by simp
  ultimately
  show  "\<exists>y\<in>D. \<langle>b, y\<rangle> \<in> r \<or> b = y" by auto
qed

lemma cofinal_range_iff_cofinal_fun:
  assumes "function(f)"
  shows "cofinal(range(f),A,r) \<longleftrightarrow> cofinal_fun(f,A,r)"
  unfolding cofinal_fun_def
proof (intro iffI ballI)
  fix a
  assume "a\<in>A" \<open>cofinal(range(f),A,r)\<close>
  then
  obtain y where "y\<in>range(f)" "\<langle>a,y\<rangle> \<in> r \<or> a = y"
    unfolding cofinal_def by blast
  moreover from this
  obtain x where "\<langle>x,y\<rangle>\<in>f"
    unfolding range_def domain_def converse_def by blast
  moreover
  note \<open>function(f)\<close>
  ultimately
  have "\<langle>a, f ` x\<rangle> \<in> r \<or> a = f ` x"
    using function_apply_equality by blast
  with \<open>\<langle>x,y\<rangle>\<in>f\<close>
  show "\<exists>x\<in>domain(f). \<langle>a, f ` x\<rangle> \<in> r \<or> a = f ` x"  by blast
next
  assume "\<forall>a\<in>A. \<exists>x\<in>domain(f). \<langle>a, f ` x\<rangle> \<in> r \<or> a = f ` x"
  with assms
  show "cofinal(range(f), A, r)"
    using function_apply_Pair[of f] unfolding cofinal_def by fast
qed

lemma cofinal_comp:
  assumes
    "f\<in> mono_map(C,s,D,r)" "cofinal_fun(f,D,r)" "h:B \<rightarrow> C"  "cofinal_fun(h,C,s)"
    "trans(r)"
  shows "cofinal_fun(f O h,D,r)"
  unfolding cofinal_fun_def
proof
  fix a
  from \<open>f\<in> mono_map(C,s,D,r)\<close>
  have "f:C \<rightarrow> D"
    using mono_map_is_fun by simp
  with \<open>h:B \<rightarrow> C\<close>
  have "domain(f) = C" "domain(h) = B"
    using domain_of_fun by simp_all
  moreover
  assume "a \<in> D"
  moreover
  note \<open>cofinal_fun(f,D,r)\<close>
  ultimately
  obtain c where "c\<in>C"  "\<langle>a, f ` c\<rangle> \<in> r \<or> a = f ` c"
    unfolding cofinal_fun_def by blast
  with \<open>cofinal_fun(h,C,s)\<close> \<open>domain(h) = B\<close>
  obtain b where "b \<in> B"  "\<langle>c, h ` b\<rangle> \<in> s \<or> c = h ` b"
    unfolding cofinal_fun_def by blast
  moreover from this and \<open>h:B \<rightarrow> C\<close>
  have "h`b \<in> C" by simp
  moreover
  note \<open>f \<in> mono_map(C,s,D,r)\<close>  \<open>c\<in>C\<close>
  ultimately
  have "\<langle>f`c, f` (h ` b)\<rangle> \<in> r \<or> f`c = f` (h ` b)"
    unfolding mono_map_def by blast
  with \<open>\<langle>a, f ` c\<rangle> \<in> r \<or> a = f ` c\<close> \<open>trans(r)\<close> \<open>h:B \<rightarrow> C\<close> \<open>b\<in>B\<close>
  have "\<langle>a, (f O h) ` b\<rangle> \<in> r \<or> a = (f O h) ` b"
    using transD by auto
  moreover from \<open>h:B \<rightarrow> C\<close> \<open>domain(f) = C\<close> \<open>domain(h) = B\<close>
  have "domain(f O h) = B"
    using range_fun_subset_codomain by blast
  moreover
  note \<open>b\<in>B\<close>
  ultimately
  show "\<exists>x\<in>domain(f O h). \<langle>a, (f O h) ` x\<rangle> \<in> r \<or> a = (f O h) ` x"  by blast
qed

definition
  cf_fun :: "[i,i] \<Rightarrow> o" where
  "cf_fun(f,\<alpha>) \<equiv> cofinal_fun(f,\<alpha>,Memrel(\<alpha>))"

lemma cf_funI[intro!]: "cofinal_fun(f,\<alpha>,Memrel(\<alpha>)) \<Longrightarrow> cf_fun(f,\<alpha>)"
  unfolding cf_fun_def by simp

lemma cf_funD[dest!]: "cf_fun(f,\<alpha>) \<Longrightarrow> cofinal_fun(f,\<alpha>,Memrel(\<alpha>))"
  unfolding cf_fun_def by simp

lemma cf_fun_comp:
  assumes
    "Ord(\<alpha>)" "f\<in> mono_map(C,s,\<alpha>,Memrel(\<alpha>))" "cf_fun(f,\<alpha>)"
    "h:B \<rightarrow> C" "cofinal_fun(h,C,s)"
  shows "cf_fun(f O h,\<alpha>)"
  using assms cofinal_comp[OF _ _ _ _ trans_Memrel] by auto

definition
  cf :: "i\<Rightarrow>i" where
  "cf(\<gamma>) \<equiv> \<mu> \<beta>.  \<exists>A. A\<subseteq>\<gamma> \<and> cofinal(A,\<gamma>,Memrel(\<gamma>)) \<and> \<beta> = ordertype(A,Memrel(\<gamma>))"

lemma Ord_cf [TC]: "Ord(cf(\<beta>))"
  unfolding cf_def using Ord_Least by simp

lemma gamma_cofinal_gamma:
  assumes "Ord(\<gamma>)"
  shows "cofinal(\<gamma>,\<gamma>,Memrel(\<gamma>))"
  unfolding cofinal_def by auto

lemma cf_is_ordertype:
  assumes "Ord(\<gamma>)"
  shows "\<exists>A. A\<subseteq>\<gamma> \<and> cofinal(A,\<gamma>,Memrel(\<gamma>)) \<and> cf(\<gamma>) = ordertype(A,Memrel(\<gamma>))"
    (is "?P(cf(\<gamma>))")
  using gamma_cofinal_gamma LeastI[of ?P \<gamma>] ordertype_Memrel[symmetric] assms
  unfolding cf_def by blast

lemma cf_fun_succ':
  assumes "Ord(\<beta>)" "Ord(\<alpha>)" "f:\<alpha>\<rightarrow>succ(\<beta>)"
  shows "(\<exists>x\<in>\<alpha>. f`x=\<beta>) \<longleftrightarrow> cf_fun(f,succ(\<beta>))"
proof (intro iffI)
  assume "(\<exists>x\<in>\<alpha>. f`x=\<beta>)"
  with assms
  show "cf_fun(f,succ(\<beta>))"
    using domain_of_fun[OF \<open>f:\<alpha>\<rightarrow>succ(\<beta>)\<close>]
    unfolding cf_fun_def cofinal_fun_def by auto
next
  assume "cf_fun(f,succ(\<beta>))"
  with assms
  obtain x where "x\<in>\<alpha>" "\<langle>\<beta>,f`x\<rangle> \<in> Memrel(succ(\<beta>)) \<or> \<beta> = f ` x"
    using domain_of_fun[OF \<open>f:\<alpha>\<rightarrow>succ(\<beta>)\<close>]
    unfolding cf_fun_def cofinal_fun_def by auto
  moreover from \<open>Ord(\<beta>)\<close>
  have "\<langle>\<beta>,y\<rangle> \<notin> Memrel(succ(\<beta>))" for y
    using foundation unfolding Memrel_def by blast
  ultimately
  show "\<exists>x\<in>\<alpha>. f ` x = \<beta>" by blast
qed

lemma cf_fun_succ:
  "Ord(\<beta>) \<Longrightarrow> f:1\<rightarrow>succ(\<beta>) \<Longrightarrow> f`0=\<beta> \<Longrightarrow> cf_fun(f,succ(\<beta>))"
  using cf_fun_succ' by blast

lemma ordertype_0_not_cofinal_succ:
  assumes "ordertype(A,Memrel(succ(i))) = 0"  "A\<subseteq>succ(i)" "Ord(i)"
  shows "\<not>cofinal(A,succ(i),Memrel(succ(i)))"
proof
  have 1:"ordertype(A,Memrel(succ(i))) = ordertype(0,Memrel(0))"
    using \<open>ordertype(A,Memrel(succ(i))) = 0\<close> ordertype_0 by simp
  from  \<open>A\<subseteq>succ(i)\<close> \<open>Ord(i)\<close>
  have "\<exists>f. f \<in> \<langle>A, Memrel(succ(i))\<rangle> \<cong> \<langle>0, Memrel(0)\<rangle>"
    using   well_ord_Memrel well_ord_subset
      ordertype_eq_imp_ord_iso[OF 1] Ord_0  by blast
  then
  have "A=0"
    using  ord_iso_is_bij bij_imp_eqpoll eqpoll_0_is_0 by blast
  moreover
  assume "cofinal(A, succ(i), Memrel(succ(i)))"
  moreover
  note \<open>Ord(i)\<close>
  ultimately
  show "False"
    using not_mem_empty unfolding cofinal_def by auto
qed

text\<open>I thank Edwin Pacheco Rodríguez for the following lemma.\<close>
lemma cf_succ:
  assumes "Ord(\<alpha>)"
  shows "cf(succ(\<alpha>)) = 1"
proof -
  define f where "f \<equiv> {\<langle>0,\<alpha>\<rangle>}"
  then
  have  "f : 1\<rightarrow>succ(\<alpha>)" "f`0 = \<alpha>"
    using fun_extend3[of 0 0 "succ(\<alpha>)" 0 \<alpha>] singleton_0 by auto
  with assms
  have "cf_fun(f,succ(\<alpha>))"
    using cf_fun_succ unfolding cofinal_fun_def by simp
  from \<open>f:1\<rightarrow>succ(\<alpha>)\<close>
  have "0\<in>domain(f)" using domain_of_fun by simp
  define A where "A={f`0}"
  with \<open>cf_fun(f,succ(\<alpha>))\<close> \<open>0\<in>domain(f)\<close> \<open>f`0=\<alpha>\<close>
  have "cofinal(A,succ(\<alpha>),Memrel(succ(\<alpha>)))"
    unfolding cofinal_def cofinal_fun_def by simp
  moreover from  \<open>f`0=\<alpha>\<close> \<open>A={f`0}\<close>
  have "A \<subseteq> succ(\<alpha>)" unfolding succ_def  by auto
  moreover from \<open>Ord(\<alpha>)\<close> \<open>A\<subseteq> succ(\<alpha>)\<close>
  have "well_ord(A,Memrel(succ(\<alpha>)))"
    using Ord_succ well_ord_Memrel  well_ord_subset relation_Memrel by blast
  moreover from \<open>Ord(\<alpha>)\<close>
  have "\<not>(\<exists>A. A \<subseteq> succ(\<alpha>) \<and> cofinal(A, succ(\<alpha>), Memrel(succ(\<alpha>))) \<and> 0 = ordertype(A, Memrel(succ(\<alpha>))))"
    (is "\<not>?P(0)")
    using ordertype_0_not_cofinal_succ  unfolding cf_def  by auto
  moreover
  have "1 = ordertype(A,Memrel(succ(\<alpha>)))"
  proof -
    from \<open>A={f`0}\<close>
    have "A\<approx>1" using singleton_eqpoll_1 by simp
    with \<open>well_ord(A,Memrel(succ(\<alpha>)))\<close>
    show ?thesis using nat_1I ordertype_eq_n by simp
  qed
  ultimately
  show "cf(succ(\<alpha>)) = 1" using Ord_1  Least_equality[of ?P 1]
    unfolding cf_def by blast
qed

lemma cf_zero [simp]:
  "cf(0) = 0"
  unfolding cf_def cofinal_def using
    ordertype_0 subset_empty_iff Least_le[of _ 0] by auto

lemma surj_is_cofinal: "f \<in> surj(\<delta>,\<gamma>) \<Longrightarrow> cf_fun(f,\<gamma>)"
  unfolding surj_def cofinal_fun_def cf_fun_def
  using domain_of_fun by force

lemma cf_zero_iff: "Ord(\<alpha>) \<Longrightarrow> cf(\<alpha>) = 0 \<longleftrightarrow> \<alpha> = 0"
proof (intro iffI)
  assume "\<alpha> = 0" "Ord(\<alpha>)"
  then
  show "cf(\<alpha>) = 0" using cf_zero by simp
next
  assume "cf(\<alpha>) = 0" "Ord(\<alpha>)"
  moreover from this
  obtain A where "A\<subseteq>\<alpha>" "cf(\<alpha>) = ordertype(A,Memrel(\<alpha>))"
    "cofinal(A,\<alpha>,Memrel(\<alpha>))"
    using cf_is_ordertype by blast
  ultimately
  have "cofinal(0,\<alpha>,Memrel(\<alpha>))"
    using ordertype_zero_imp_zero[of A "Memrel(\<alpha>)"] by simp
  then
  show "\<alpha>=0"
    unfolding cofinal_def by blast
qed

\<comment> \<open>TODO: define Succ (predicate for successor ordinals)\<close>
lemma cf_eq_one_iff:
  assumes "Ord(\<gamma>)"
  shows "cf(\<gamma>) = 1 \<longleftrightarrow> (\<exists>\<alpha>. Ord(\<alpha>) \<and> \<gamma>  = succ(\<alpha>))"
proof (intro iffI)
  assume "\<exists>\<alpha>. Ord(\<alpha>) \<and> \<gamma>  = succ(\<alpha>)"
  then
  show "cf(\<gamma>) = 1" using cf_succ by auto
next
  assume "cf(\<gamma>) = 1"
  moreover from assms
  obtain A where "A \<subseteq> \<gamma>" "cf(\<gamma>) = ordertype(A,Memrel(\<gamma>))"
    "cofinal(A,\<gamma>,Memrel(\<gamma>))"
    using cf_is_ordertype by blast
  ultimately
  have "ordertype(A,Memrel(\<gamma>)) = 1" by simp
  moreover
  define f where "f\<equiv>converse(ordermap(A,Memrel(\<gamma>)))"
  moreover from this \<open>ordertype(A,Memrel(\<gamma>)) = 1\<close> \<open>A \<subseteq> \<gamma>\<close> assms
  have "f \<in> surj(1,A)"
    using well_ord_subset[OF well_ord_Memrel, THEN ordermap_bij,
        THEN bij_converse_bij, of \<gamma> A] bij_is_surj
    by simp
  with \<open>cofinal(A,\<gamma>,Memrel(\<gamma>))\<close>
  have "\<forall>a\<in>\<gamma>. \<langle>a, f`0\<rangle> \<in> Memrel(\<gamma>) \<or> a = f`0"
    unfolding cofinal_def surj_def
    by auto
  with assms \<open>A \<subseteq> \<gamma>\<close> \<open>f \<in> surj(1,A)\<close>
  show "\<exists>\<alpha>. Ord(\<alpha>) \<and> \<gamma>  = succ(\<alpha>)"
    using Ord_has_max_imp_succ[of \<gamma> "f`0"]
      surj_is_fun[of f 1 A] apply_type[of f 1 "\<lambda>_.A" 0]
    unfolding lt_def
    by (auto intro:Ord_in_Ord)
qed

lemma ordertype_in_cf_imp_not_cofinal:
  assumes
    "ordertype(A,Memrel(\<gamma>)) \<in> cf(\<gamma>)"
    "A \<subseteq> \<gamma>"
  shows
    "\<not> cofinal(A,\<gamma>,Memrel(\<gamma>))"
proof
  note \<open>A \<subseteq> \<gamma>\<close>
  moreover
  assume "cofinal(A,\<gamma>,Memrel(\<gamma>))"
  ultimately
  have "\<exists>B. B \<subseteq> \<gamma> \<and> cofinal(B, \<gamma>, Memrel(\<gamma>)) \<and>  ordertype(A,Memrel(\<gamma>)) = ordertype(B, Memrel(\<gamma>))"
    (is "?P(ordertype(A,_))")
    by blast
  moreover from assms
  have "ordertype(A,Memrel(\<gamma>)) < cf(\<gamma>)"
    using Ord_cf ltI by blast
  ultimately
  show "False"
    unfolding cf_def using less_LeastE[of ?P  "ordertype(A,Memrel(\<gamma>))"]
    by auto
qed

lemma cofinal_mono_map_cf:
  assumes "Ord(\<gamma>)"
  shows "\<exists>j \<in> mono_map(cf(\<gamma>), Memrel(cf(\<gamma>)), \<gamma>, Memrel(\<gamma>)) . cf_fun(j,\<gamma>)"
proof -
  note assms
  moreover from this
  obtain A where "A \<subseteq> \<gamma>" "cf(\<gamma>) = ordertype(A,Memrel(\<gamma>))"
    "cofinal(A,\<gamma>,Memrel(\<gamma>))"
    using cf_is_ordertype by blast
  moreover
  define j where "j \<equiv> converse(ordermap(A,Memrel(\<gamma>)))"
  moreover from calculation
  have "j :cf(\<gamma>) \<rightarrow>\<^sub>< \<gamma>"
    using ordertype_ord_iso[THEN ord_iso_sym,
        THEN ord_iso_is_mono_map, THEN mono_map_mono,
        of A "Memrel(\<gamma>)" \<gamma>] well_ord_Memrel[THEN well_ord_subset]
    by simp
  moreover from calculation
  have "j \<in> surj(cf(\<gamma>),A)"
    using well_ord_Memrel[THEN well_ord_subset, THEN ordertype_ord_iso,
        THEN ord_iso_sym, of \<gamma> A, THEN ord_iso_is_bij,
        THEN bij_is_surj]
    by simp
  with \<open>cofinal(A,\<gamma>,Memrel(\<gamma>))\<close>
  have "cf_fun(j,\<gamma>)"
    using cofinal_range_iff_cofinal_fun[of j \<gamma> "Memrel(\<gamma>)"]
      surj_range[of j "cf(\<gamma>)" A] surj_is_fun fun_is_function
    by fastforce
  with \<open>j \<in> mono_map(_,_,_,_)\<close>
  show ?thesis by auto
qed


subsection\<open>The factorization lemma\<close>

text\<open>In this subsection we prove a factorization lemma for cofinal functions
into ordinals, which shows that any cofinal function between ordinals can be
“decomposed” in such a way that a commutative triangle of strictly increasing
maps arises.

The factorization lemma has a kind of
fundamental character, in that the rest of the basic results on cofinality
(for, instance, idempotence) follow easily from it, in a more algebraic way.

This is a consequence that the proof encapsulates uses of transfinite
recursion in the basic theory of cofinality; indeed, only one use is needed.
In the setting of Isabelle/ZF, this is convenient since the machinery of
recursion is pretty clumsy. On the downside, this way of presenting things 
results in a longer proof of the factorization lemma. This approach was
taken by the author in the notes \cite{apunte_st} for an introductory course
in Set Theory.

To organize the use of the hypotheses of the factorization lemma,
we set up a locale containing all the relevant ingredients.
\<close>
locale cofinal_factor =
  fixes j \<delta> \<xi> \<gamma> f
  assumes j_mono: "j :\<xi> \<rightarrow>\<^sub>< \<gamma>"
    and     ords: "Ord(\<delta>)" "Ord(\<xi>)" "Limit(\<gamma>)"
    and   f_type: "f: \<delta> \<rightarrow> \<gamma>"
begin

text\<open>Here, \<^term>\<open>f\<close> is cofinal function from \<^term>\<open>\<delta>\<close> to \<^term>\<open>\<gamma>\<close>, and the
ordinal \<^term>\<open>\<xi>\<close> is meant to be the cofinality of \<^term>\<open>\<gamma>\<close>. Hence, there exists
an increasing map \<^term>\<open>j\<close> from  \<^term>\<open>\<xi>\<close> to  \<^term>\<open>\<gamma>\<close> by the last lemma.

The main goal is to construct an increasing function \<^term>\<open>g:\<xi>\<rightarrow>\<delta>\<close> such that
the composition \<^term>\<open>f O g\<close> is still cofinal but also increasing.\<close>

definition
  factor_body :: "[i,i,i] \<Rightarrow> o" where
  "factor_body(\<beta>,h,x) \<equiv> (x\<in>\<delta> \<and> j`\<beta> \<le> f`x \<and> (\<forall>\<alpha><\<beta> . f`(h`\<alpha>) < f`x)) \<or> x=\<delta>"

definition
  factor_rec :: "[i,i] \<Rightarrow> i" where
  "factor_rec(\<beta>,h) \<equiv>  \<mu> x. factor_body(\<beta>,h,x)"

txt\<open>\<^term>\<open>factor_rec\<close> is the inductive step for the definition by transfinite
recursion of the \<^emph>\<open>factor\<close> function (called \<^term>\<open>g\<close> above), which in
turn is obtained by minimizing the predicate \<^term>\<open>factor_body\<close>. Next we show
that this predicate is monotonous.\<close>

lemma factor_body_mono:
  assumes
    "\<beta>\<in>\<xi>" "\<alpha><\<beta>"
    "factor_body(\<beta>,\<lambda>x\<in>\<beta>. G(x),x)"
  shows
    "factor_body(\<alpha>,\<lambda>x\<in>\<alpha>. G(x),x)"
proof -
  from \<open>\<alpha><\<beta>\<close>
  have "\<alpha>\<in>\<beta>" using ltD by simp
  moreover
  note \<open>\<beta>\<in>\<xi>\<close>
  moreover from calculation
  have "\<alpha>\<in>\<xi>" using ords ltD Ord_cf Ord_trans by blast
  ultimately
  have "j`\<alpha> \<in> j`\<beta>" using j_mono mono_map_increasing by blast
  moreover from \<open>\<beta>\<in>\<xi>\<close>
  have "j`\<beta>\<in>\<gamma>"
    using j_mono domain_of_fun apply_rangeI mono_map_is_fun by force
  moreover from this
  have "Ord(j`\<beta>)"
    using Ord_in_Ord ords Limit_is_Ord by auto
  ultimately
  have "j`\<alpha> \<le> j`\<beta>"  unfolding lt_def by blast
  then
  have "j`\<beta> \<le> f`\<theta> \<Longrightarrow> j`\<alpha> \<le> f`\<theta>" for \<theta> using le_trans by blast
  moreover
  have "f`((\<lambda>w\<in>\<alpha>. G(w))`y) < f`z" if "z\<in>\<delta>" "\<forall>x<\<beta>. f`((\<lambda>w\<in>\<beta>. G(w))`x) < f`z" "y<\<alpha>" for y z
  proof -
    note \<open>y<\<alpha>\<close>
    also
    note \<open>\<alpha><\<beta>\<close>
    finally
    have "y<\<beta>" by simp
    with \<open>\<forall>x<\<beta>. f`((\<lambda>w\<in>\<beta>. G(w))`x) < f`z\<close>
    have "f ` ((\<lambda>w\<in>\<beta>. G(w)) ` y) < f ` z" by simp
    moreover from \<open>y<\<alpha>\<close> \<open>y<\<beta>\<close>
    have "(\<lambda>w\<in>\<beta>. G(w)) ` y = (\<lambda>w\<in>\<alpha>. G(w)) ` y"
      using beta_if  by (auto dest:ltD)
    ultimately show ?thesis by simp
  qed
  moreover
  note \<open>factor_body(\<beta>,\<lambda>x\<in>\<beta>. G(x),x)\<close>
  ultimately
  show ?thesis
    unfolding factor_body_def by blast
qed

lemma factor_body_simp[simp]: "factor_body(\<alpha>,g,\<delta>)"
  unfolding factor_body_def by simp

lemma factor_rec_mono:
  assumes
    "\<beta>\<in>\<xi>" "\<alpha><\<beta>"
  shows
    "factor_rec(\<alpha>,\<lambda>x\<in>\<alpha>. G(x)) \<le> factor_rec(\<beta>,\<lambda>x\<in>\<beta>. G(x))"
  unfolding factor_rec_def
  using assms ords factor_body_mono Least_antitone by simp

text\<open>We now define the factor as higher-order function.
Later it will be restricted to a set to obtain a bona fide function of
type @{typ i}.\<close>
definition
  factor :: "i \<Rightarrow> i" where
  "factor(\<beta>) \<equiv> transrec(\<beta>,factor_rec)"

lemma factor_unfold:
  "factor(\<alpha>) = factor_rec(\<alpha>,\<lambda>x\<in>\<alpha>. factor(x))"
  using def_transrec[OF factor_def] .

lemma factor_mono:
  assumes "\<beta>\<in>\<xi>" "\<alpha><\<beta>" "factor(\<alpha>)\<noteq>\<delta>" "factor(\<beta>)\<noteq>\<delta>"
  shows "factor(\<alpha>) \<le> factor(\<beta>)"
proof -
  have "factor(\<alpha>) = factor_rec(\<alpha>, \<lambda>x\<in>\<alpha>. factor(x))"
    using factor_unfold .
  also from assms and factor_rec_mono
  have "... \<le> factor_rec(\<beta>, \<lambda>x\<in>\<beta>. factor(x))"
    by simp
  also
  have "factor_rec(\<beta>, \<lambda>x\<in>\<beta>. factor(x)) = factor(\<beta>)"
    using def_transrec[OF factor_def, symmetric] .
  finally show ?thesis .
qed

text\<open>The factor satisfies the predicate body of the minimization.\<close>

lemma factor_body_factor:
  "factor_body(\<alpha>,\<lambda>x\<in>\<alpha>. factor(x),factor(\<alpha>))"
  using ords factor_unfold[of \<alpha>]
    LeastI[of "factor_body(_,_)" \<delta>]
  unfolding factor_rec_def by simp

lemma factor_type [TC]: "Ord(factor(\<alpha>))"
  using ords factor_unfold[of \<alpha>]
  unfolding factor_rec_def by simp

text\<open>The value \<^term>\<open>\<delta>\<close> in \<^term>\<open>factor_body\<close> (and therefore, in
\<^term>\<open>factor\<close>) is meant to be a “default value”. Whenever it is not 
attained, the factor function behaves as expected: It is increasing
and its composition with \<^term>\<open>f\<close> also is.\<close>

lemma f_factor_increasing:
  assumes "\<beta>\<in>\<xi>" "\<alpha><\<beta>" "factor(\<beta>)\<noteq>\<delta>"
  shows "f`factor(\<alpha>) < f`factor(\<beta>)"
proof -
  from assms
  have "f ` ((\<lambda>x\<in>\<beta>. factor(x)) ` \<alpha>) < f ` factor(\<beta>)"
    using factor_unfold[of \<beta>] ords LeastI[of "factor_body(\<beta>,\<lambda>x\<in>\<beta>. factor(x))"]
    unfolding factor_rec_def factor_body_def
    by (auto simp del:beta_if)
  with \<open>\<alpha><\<beta>\<close>
  show ?thesis using ltD by auto
qed

lemma factor_increasing:
  assumes "\<beta>\<in>\<xi>" "\<alpha><\<beta>" "factor(\<alpha>)\<noteq>\<delta>" "factor(\<beta>)\<noteq>\<delta>"
  shows "factor(\<alpha>)<factor(\<beta>)"
  using assms f_factor_increasing factor_mono by (force intro:le_neq_imp_lt)

lemma factor_in_delta:
  assumes "factor(\<beta>) \<noteq> \<delta>"
  shows "factor(\<beta>) \<in> \<delta>"
  using assms factor_body_factor ords
  unfolding factor_body_def by auto

text\<open>Finally, we define the (set) factor function as the restriction of
factor to the ordinal  \<^term>\<open>\<xi>\<close>.\<close>

definition
  fun_factor :: "i" where
  "fun_factor \<equiv> \<lambda>\<beta>\<in>\<xi>. factor(\<beta>)"

lemma fun_factor_is_mono_map:
  assumes "\<And>\<beta>. \<beta> \<in> \<xi> \<Longrightarrow> factor(\<beta>) \<noteq> \<delta>"
  shows "fun_factor \<in> mono_map(\<xi>, Memrel(\<xi>), \<delta>, Memrel(\<delta>))"
  unfolding mono_map_def
proof (intro CollectI ballI impI)
  (* Proof that \<^term>\<open>fun_factor\<close> respects membership *)
  fix \<alpha> \<beta>
  assume "\<alpha>\<in>\<xi>" "\<beta>\<in>\<xi>"
  moreover
  note assms
  moreover from calculation
  have "factor(\<alpha>)\<noteq>\<delta>" "factor(\<beta>)\<noteq>\<delta>" "Ord(\<beta>)"
    using factor_in_delta Ord_in_Ord ords by auto
  moreover
  assume "\<langle>\<alpha>, \<beta>\<rangle> \<in> Memrel(\<xi>)"
  ultimately
  show "\<langle>fun_factor ` \<alpha>, fun_factor ` \<beta>\<rangle> \<in> Memrel(\<delta>)"
    unfolding fun_factor_def
    using ltI factor_increasing[THEN ltD] factor_in_delta
    by simp
next
  (* Proof of type *)
  from assms
  show "fun_factor : \<xi> \<rightarrow> \<delta>"
    unfolding fun_factor_def
    using ltI lam_type factor_in_delta by simp
qed

lemma f_fun_factor_is_mono_map:
  assumes "\<And>\<beta>. \<beta> \<in> \<xi> \<Longrightarrow> factor(\<beta>) \<noteq> \<delta>"
  shows "f O fun_factor \<in> mono_map(\<xi>, Memrel(\<xi>), \<gamma>, Memrel(\<gamma>))"
  unfolding mono_map_def
  using f_type
proof (intro CollectI ballI impI comp_fun[of _ _ \<delta>])
  from assms
  show "fun_factor : \<xi> \<rightarrow> \<delta>"
    using fun_factor_is_mono_map mono_map_is_fun by simp
      (* Proof that f O ?g respects membership *)
  fix \<alpha> \<beta>
  assume "\<langle>\<alpha>, \<beta>\<rangle> \<in> Memrel(\<xi>)"
  then
  have "\<alpha><\<beta>"
    using Ord_in_Ord[of "\<xi>"] ltI ords by blast
  assume "\<alpha>\<in>\<xi>" "\<beta>\<in>\<xi>"
  moreover from this and assms
  have "factor(\<alpha>)\<noteq>\<delta>" "factor(\<beta>)\<noteq>\<delta>" by auto
  moreover
  have "Ord(\<gamma>)" "\<gamma>\<noteq>0" using ords Limit_is_Ord by auto
  moreover
  note \<open>\<alpha><\<beta>\<close> \<open>fun_factor : \<xi> \<rightarrow> \<delta>\<close>
  ultimately
  show "\<langle>(f O fun_factor) ` \<alpha>, (f O fun_factor) ` \<beta>\<rangle> \<in> Memrel(\<gamma>)"
    using ltD[of "f ` factor(\<alpha>)" "f ` factor(\<beta>)"]
      f_factor_increasing apply_in_range f_type
    unfolding fun_factor_def by auto
qed

end (* cofinal_factor *)

text\<open>We state next the factorization lemma.\<close>

lemma cofinal_fun_factorization:
  notes le_imp_subset [dest] lt_trans2 [trans]
  assumes
    "Ord(\<delta>)" "Limit(\<gamma>)" "f: \<delta> \<rightarrow> \<gamma>" "cf_fun(f,\<gamma>)"
  shows
    "\<exists>g \<in> cf(\<gamma>) \<rightarrow>\<^sub>< \<delta>.  f O g : cf(\<gamma>) \<rightarrow>\<^sub>< \<gamma> \<and>
           cofinal_fun(f O g,\<gamma>,Memrel(\<gamma>))"
proof -
  from \<open>Limit(\<gamma>)\<close>
  have "Ord(\<gamma>)" using Limit_is_Ord by simp
  then
  obtain j where "j :cf(\<gamma>) \<rightarrow>\<^sub>< \<gamma>" "cf_fun(j,\<gamma>)"
    using cofinal_mono_map_cf by blast
  then
  have "domain(j) = cf(\<gamma>)"
    using domain_of_fun mono_map_is_fun by force
  from \<open>j \<in> _\<close> assms
  interpret cofinal_factor j \<delta> "cf(\<gamma>)"
    by (unfold_locales) (simp_all)
  text\<open>The core of the argument is to show that the factor function
  indeed maps into \<^term>\<open>\<delta>\<close>, therefore its values satisfy the first
  disjunct of \<^term>\<open>factor_body\<close>. This holds in turn because no
  restriction of the factor composed with \<^term>\<open>f\<close> to a proper initial
  segment of \<^term>\<open>cf(\<gamma>)\<close> can be cofinal in \<^term>\<open>\<gamma>\<close> by definition of
  cofinality. Hence there must be a witness that satisfies the first
  disjunct.\<close>
  have factor_not_delta: "factor(\<beta>)\<noteq>\<delta>" if "\<beta> \<in> cf(\<gamma>)" for \<beta>
    text\<open>For this, we induct on \<^term>\<open>\<beta>\<close> ranging over \<^term>\<open>cf(\<gamma>)\<close>.\<close>
  proof (induct \<beta> rule:Ord_induct[OF _ Ord_cf[of \<gamma>]])
    case 1 with that show ?case .
  next
    case (2 \<beta>)
    then
    have IH: "z\<in>\<beta> \<Longrightarrow> factor(z)\<noteq>\<delta>" for z by simp
    define h where "h \<equiv> \<lambda>x\<in>\<beta>. f`factor(x)"
    from IH
    have "z\<in>\<beta> \<Longrightarrow> factor(z) \<in> \<delta>" for z
      using factor_in_delta by blast
    with \<open>f:\<delta>\<rightarrow>\<gamma>\<close>
    have "h : \<beta> \<rightarrow> \<gamma>" unfolding h_def using apply_funtype lam_type by auto
    then
    have "h : \<beta> \<rightarrow>\<^sub>< \<gamma>"
      unfolding mono_map_def
    proof (intro CollectI ballI impI)
      fix x y
      assume "x\<in>\<beta>" "y\<in>\<beta>"
      moreover from this and IH
      have "factor(y) \<noteq> \<delta>" by simp
      moreover from calculation and \<open>h \<in> \<beta> \<rightarrow> \<gamma>\<close>
      have "h`x \<in> \<gamma>" "h`y \<in> \<gamma>" by simp_all
      moreover from \<open>\<beta>\<in>cf(\<gamma>)\<close> and \<open>y\<in>\<beta>\<close>
      have "y \<in> cf(\<gamma>)"
        using Ord_trans Ord_cf by blast
      moreover from this
      have "Ord(y)"
        using Ord_cf Ord_in_Ord by blast
      moreover
      assume "\<langle>x,y\<rangle> \<in> Memrel(\<beta>)"
      moreover from calculation
      have "x<y" by (blast intro:ltI)
      ultimately
      show "\<langle>h ` x, h ` y\<rangle> \<in> Memrel(\<gamma>)"
        unfolding h_def using f_factor_increasing ltD by (auto)
    qed
    with \<open>\<beta>\<in>cf(\<gamma>)\<close> \<open>Ord(\<gamma>)\<close>
    have "ordertype(h``\<beta>,Memrel(\<gamma>)) = \<beta>" (* Maybe should use range(h) *)
      using mono_map_ordertype_image[of \<beta>] Ord_cf Ord_in_Ord by blast
    also
    note \<open>\<beta> \<in>cf(\<gamma>)\<close>
    finally
    have "ordertype(h``\<beta>,Memrel(\<gamma>)) \<in> cf(\<gamma>)" by simp
    moreover from \<open>h \<in> \<beta> \<rightarrow> \<gamma>\<close>
    have "h``\<beta> \<subseteq> \<gamma>"
      using mono_map_is_fun Image_sub_codomain by blast
    ultimately
    have "\<not> cofinal(h``\<beta>,\<gamma>,Memrel(\<gamma>))"
      using ordertype_in_cf_imp_not_cofinal by simp
    then
    obtain \<alpha>_0 where "\<alpha>_0\<in>\<gamma>" "\<forall>x\<in>h `` \<beta>. \<not> \<langle>\<alpha>_0, x\<rangle> \<in> Memrel(\<gamma>) \<and> \<alpha>_0 \<noteq> x"
      unfolding cofinal_def by auto
    with \<open>Ord(\<gamma>)\<close> \<open>h``\<beta> \<subseteq> \<gamma>\<close>
    have "\<forall>x\<in>h `` \<beta>. x \<in> \<alpha>_0"
      using well_ord_Memrel[of \<gamma>] well_ord_is_linear[of \<gamma> "Memrel(\<gamma>)"]
      unfolding linear_def by blast
    from \<open>\<alpha>_0 \<in> \<gamma>\<close> \<open>j \<in> mono_map(_,_,\<gamma>,_)\<close> \<open>Ord(\<gamma>)\<close>
    have "j`\<beta> \<in> \<gamma>"
      using mono_map_is_fun apply_in_range by force
    with \<open>\<alpha>_0 \<in> \<gamma>\<close> \<open>Ord(\<gamma>)\<close>
    have "\<alpha>_0 \<union> j`\<beta> \<in> \<gamma>"
      using Un_least_mem_iff Ord_in_Ord by auto
    with \<open>cf_fun(f,\<gamma>)\<close>
    obtain \<theta> where "\<theta>\<in>domain(f)" "\<langle>\<alpha>_0 \<union> j`\<beta>, f ` \<theta>\<rangle> \<in> Memrel(\<gamma>) \<or>  \<alpha>_0 \<union> j`\<beta> = f ` \<theta>"
      by (auto simp add:cofinal_fun_def) blast
    moreover from this and \<open>f:\<delta>\<rightarrow>\<gamma>\<close>
    have "\<theta> \<in> \<delta>" using domain_of_fun by auto
    moreover
    note \<open>Ord(\<gamma>)\<close>
    moreover from this and \<open>f:\<delta>\<rightarrow>\<gamma>\<close>  \<open>\<alpha>_0 \<in> \<gamma>\<close>
    have "Ord(f`\<theta>)"
      using apply_in_range Ord_in_Ord by blast
    moreover from calculation and \<open>\<alpha>_0 \<in> \<gamma>\<close> and \<open>Ord(\<delta>)\<close> and \<open>j`\<beta> \<in> \<gamma>\<close>
    have "Ord(\<alpha>_0)" "Ord(j`\<beta>)" "Ord(\<theta>)"
      using Ord_in_Ord by auto
    moreover from \<open>\<forall>x\<in>h `` \<beta>. x \<in> \<alpha>_0\<close> \<open>Ord(\<alpha>_0)\<close> \<open>h:\<beta>\<rightarrow>\<gamma>\<close>
    have "x\<in>\<beta> \<Longrightarrow> h`x < \<alpha>_0" for x
      using fun_is_function[of h \<beta> "\<lambda>_. \<gamma>"]
        Image_subset_Ord_imp_lt domain_of_fun[of h \<beta> "\<lambda>_. \<gamma>"]
      by blast
    moreover
    have "x\<in>\<beta> \<Longrightarrow> h`x < f`\<theta>" for x
    proof -
      fix x
      assume "x\<in>\<beta>"
      with \<open>\<forall>x\<in>h `` \<beta>. x \<in> \<alpha>_0\<close> \<open>Ord(\<alpha>_0)\<close> \<open>h:\<beta>\<rightarrow>\<gamma>\<close>
      have "h`x < \<alpha>_0"
        using fun_is_function[of h \<beta> "\<lambda>_. \<gamma>"]
          Image_subset_Ord_imp_lt domain_of_fun[of h \<beta> "\<lambda>_. \<gamma>"]
        by blast
      also from \<open>\<langle>\<alpha>_0 \<union> _, f ` \<theta>\<rangle> \<in> Memrel(\<gamma>) \<or> \<alpha>_0 \<union> _= f ` \<theta>\<close>
        \<open>Ord(f`\<theta>)\<close> \<open>Ord(\<alpha>_0)\<close> \<open>Ord(j`\<beta>)\<close>
      have "\<alpha>_0 \<le> f`\<theta>"
        using Un_leD1[OF leI [OF ltI]] Un_leD1[OF le_eqI] by blast
      finally
      show "h`x < f`\<theta>" .
    qed
    ultimately
    have "factor_body(\<beta>,\<lambda>x\<in>\<beta>. factor(x),\<theta>)"
      unfolding h_def factor_body_def using ltD
      by (auto dest:Un_memD2 Un_leD2[OF le_eqI])
    with \<open>Ord(\<theta>)\<close>
    have "factor(\<beta>) \<le> \<theta>"
      using factor_unfold[of \<beta>] Least_le unfolding factor_rec_def by auto
    with \<open>\<theta>\<in>\<delta>\<close> \<open>Ord(\<delta>)\<close>
    have "factor(\<beta>) \<in> \<delta>"
      using leI[of \<theta>] ltI[of \<theta>]  by (auto dest:ltD)
    then
    show ?case by (auto elim:mem_irrefl)
  qed
  moreover
  have "cofinal_fun(f O fun_factor, \<gamma>, Memrel(\<gamma>))"
  proof (intro cofinal_funI)
    fix a
    assume "a \<in> \<gamma>"
    with \<open>cf_fun(j,\<gamma>)\<close> \<open>domain(j) = cf(\<gamma>)\<close>
    obtain x where "x\<in>cf(\<gamma>)" "a \<in> j`x \<or> a = j`x"
      by (auto simp add:cofinal_fun_def) blast
    with factor_not_delta
    have "x \<in> domain(f O fun_factor)"
      using f_fun_factor_is_mono_map mono_map_is_fun domain_of_fun by force
    moreover
    have "a \<in> (f O fun_factor) `x \<or> a = (f O fun_factor) `x"
    proof -
      from \<open>x\<in>cf(\<gamma>)\<close> factor_not_delta
      have "j ` x \<le> f ` factor(x)"
        using mem_not_refl factor_body_factor factor_in_delta
        unfolding factor_body_def by auto
      with \<open>a \<in> j`x \<or> a = j`x\<close>
      have "a \<in> f ` factor(x) \<or> a = f ` factor(x)"
        using ltD by blast
      with \<open>x\<in>cf(\<gamma>)\<close>
      show ?thesis using lam_funtype[of "cf(\<gamma>)" factor]
        unfolding fun_factor_def by auto
    qed
    moreover
    note \<open>a \<in> \<gamma>\<close>
    moreover from calculation and \<open>Ord(\<gamma>)\<close> and factor_not_delta
    have "(f O fun_factor) `x \<in> \<gamma>"
      using Limit_nonzero apply_in_range mono_map_is_fun[of "f O fun_factor"]
        f_fun_factor_is_mono_map by blast
    ultimately
    show "\<exists>x \<in> domain(f O fun_factor). \<langle>a, (f O fun_factor) ` x\<rangle> \<in> Memrel(\<gamma>)
                                       \<or> a = (f O fun_factor) `x"
      by blast
  qed
  ultimately
  show ?thesis
    using fun_factor_is_mono_map f_fun_factor_is_mono_map by blast
qed

text\<open>As a final observation in this part, we note that if the original
cofinal map was increasing, then the factor function is also cofinal.\<close>
lemma factor_is_cofinal:
  assumes
    "Ord(\<delta>)" "Ord(\<gamma>)"
    "f :\<delta> \<rightarrow>\<^sub>< \<gamma>"  "f O g \<in> mono_map(\<alpha>,r,\<gamma>,Memrel(\<gamma>))"
    "cofinal_fun(f O g,\<gamma>,Memrel(\<gamma>))" "g: \<alpha> \<rightarrow> \<delta>"
  shows
    "cf_fun(g,\<delta>)"
  unfolding cf_fun_def cofinal_fun_def
proof
  fix a
  assume "a \<in> \<delta>"
  with \<open>f \<in> mono_map(\<delta>,_,\<gamma>,_)\<close>
  have "f`a \<in> \<gamma>"
    using mono_map_is_fun by force
  with \<open>cofinal_fun(f O g,\<gamma>,_)\<close>
  obtain y where "y\<in>\<alpha>"  "\<langle>f`a, (f O g) ` y\<rangle> \<in> Memrel(\<gamma>) \<or> f`a = (f O g) ` y"
    unfolding cofinal_fun_def using domain_of_fun[OF \<open>g:\<alpha> \<rightarrow> \<delta>\<close>] by blast
  with \<open>g:\<alpha> \<rightarrow> \<delta>\<close>
  have "\<langle>f`a, f ` (g ` y)\<rangle> \<in> Memrel(\<gamma>) \<or> f`a = f ` (g ` y)" "g`y \<in> \<delta>"
    using comp_fun_apply[of g \<alpha> \<delta> y f] by auto
  with assms(1-3) and \<open>a\<in>\<delta>\<close>
  have "\<langle>a, g ` y\<rangle> \<in> Memrel(\<delta>) \<or> a = g ` y"
    using Memrel_mono_map_reflects Memrel_mono_map_is_inj[of \<delta> f \<gamma> \<gamma>]
      inj_apply_equality[of f \<delta> \<gamma>]  by blast
  with \<open>y\<in>\<alpha>\<close>
  show "\<exists>x\<in>domain(g). \<langle>a, g ` x\<rangle> \<in> Memrel(\<delta>) \<or> a = g ` x"
    using domain_of_fun[OF \<open>g:\<alpha> \<rightarrow> \<delta>\<close>] by blast
qed


subsection\<open>Classical results on cofinalities\<close>

text\<open>Now the rest of the results follow in a more algebraic way. The
next proof one invokes a case analysis on whether the argument is zero,
a successor ordinal or a limit one; the last case being the most
relevant one and is immediate from the factorization lemma.\<close>

lemma cf_le_domain_cofinal_fun:
  assumes
    "Ord(\<gamma>)" "Ord(\<delta>)" "f:\<delta> \<rightarrow> \<gamma>" "cf_fun(f,\<gamma>)"
  shows
    "cf(\<gamma>)\<le>\<delta>"
  using assms
proof (cases rule:Ord_cases)
  case 0
  with \<open>Ord(\<delta>)\<close>
  show ?thesis using Ord_0_le by simp
next
  case (succ \<gamma>)
  with assms
  obtain x where "x\<in>\<delta>" "f`x=\<gamma>" using cf_fun_succ' by blast
  then
  have "\<delta>\<noteq>0" by blast
  let ?f="{\<langle>0,f`x\<rangle>}"
  from \<open>f`x=\<gamma>\<close>
  have "?f:1\<rightarrow>succ(\<gamma>)"
    using singleton_0 singleton_fun[of 0 \<gamma>] singleton_subsetI fun_weaken_type by simp
  with \<open>Ord(\<gamma>)\<close>  \<open>f`x=\<gamma>\<close>
  have "cf(succ(\<gamma>)) = 1" using cf_succ by simp
  with \<open>\<delta>\<noteq>0\<close> succ
  show ?thesis using Ord_0_lt_iff succ_leI \<open>Ord(\<delta>)\<close> by simp
next
  case (limit)
  with assms
  obtain g where "g :cf(\<gamma>) \<rightarrow>\<^sub>< \<delta>"
    using cofinal_fun_factorization by blast
  with assms
  show ?thesis using mono_map_imp_le by simp
qed

lemma cf_ordertype_cofinal:
  assumes
    "Limit(\<gamma>)" "A\<subseteq>\<gamma>" "cofinal(A,\<gamma>,Memrel(\<gamma>))"
  shows
    "cf(\<gamma>) = cf(ordertype(A,Memrel(\<gamma>)))"
proof (intro le_anti_sym)
  from \<open>Limit(\<gamma>)\<close>
  have "Ord(\<gamma>)"
    using Limit_is_Ord by simp
  with \<open>A \<subseteq> \<gamma>\<close>
  have "well_ord(A,Memrel(\<gamma>))"
    using well_ord_Memrel well_ord_subset by blast
  then
  obtain f \<alpha> where "f:\<langle>\<alpha>, Memrel(\<alpha>)\<rangle> \<cong> \<langle>A,Memrel(\<gamma>)\<rangle>" "Ord(\<alpha>)" "\<alpha> = ordertype(A,Memrel(\<gamma>))"
    using ordertype_ord_iso Ord_ordertype ord_iso_sym by blast
  moreover from this
  have "f: \<alpha> \<rightarrow> A"
    using ord_iso_is_mono_map mono_map_is_fun[of f _ "Memrel(\<alpha>)"] by blast
  moreover from this
  have "function(f)"
    using fun_is_function by simp
  moreover from \<open>f:\<langle>\<alpha>, Memrel(\<alpha>)\<rangle> \<cong> \<langle>A,Memrel(\<gamma>)\<rangle>\<close>
  have "range(f) = A"
    using ord_iso_is_bij bij_is_surj surj_range by blast
  moreover note \<open>cofinal(A,\<gamma>,_)\<close>
  ultimately
  have "cf_fun(f,\<gamma>)"
    using cofinal_range_iff_cofinal_fun by blast
  moreover from \<open>Ord(\<alpha>)\<close>
  obtain h where "h :cf(\<alpha>) \<rightarrow>\<^sub>< \<alpha>" "cf_fun(h,\<alpha>)"
    using cofinal_mono_map_cf by blast
  moreover from \<open>Ord(\<gamma>)\<close>
  have "trans(Memrel(\<gamma>))"
    using trans_Memrel by simp
  moreover
  note \<open>A\<subseteq>\<gamma>\<close>
  ultimately
  have "cofinal_fun(f O h,\<gamma>,Memrel(\<gamma>))"
    using cofinal_comp ord_iso_is_mono_map[OF \<open>f:\<langle>\<alpha>,_\<rangle> \<cong> \<langle>A,_\<rangle>\<close>] mono_map_is_fun
      mono_map_mono by blast
  moreover from \<open>f:\<alpha>\<rightarrow>A\<close> \<open>A\<subseteq>\<gamma>\<close> \<open>h\<in>mono_map(cf(\<alpha>),_,\<alpha>,_)\<close>
  have "f O h : cf(\<alpha>) \<rightarrow> \<gamma>"
    using Pi_mono[of A \<gamma>] comp_fun  mono_map_is_fun by blast
  moreover
  note \<open>Ord(\<gamma>)\<close> \<open>Ord(\<alpha>)\<close> \<open>\<alpha> = ordertype(A,Memrel(\<gamma>))\<close>
  ultimately
  show "cf(\<gamma>) \<le> cf(ordertype(A,Memrel(\<gamma>)))"
    using cf_le_domain_cofinal_fun[of _ _ "f O h"]
    by (auto simp add:cf_fun_def)
      (********************************************************)
  from \<open>f:\<langle>\<alpha>, _\<rangle> \<cong> \<langle>A,_\<rangle>\<close> \<open>A\<subseteq>\<gamma>\<close>
  have "f :\<alpha> \<rightarrow>\<^sub>< \<gamma>"
    using mono_map_mono[OF ord_iso_is_mono_map] by simp
  then
  have "f: \<alpha> \<rightarrow> \<gamma>"
    using mono_map_is_fun by simp
  with \<open>cf_fun(f,\<gamma>)\<close> \<open>Limit(\<gamma>)\<close> \<open>Ord(\<alpha>)\<close>
  obtain g where "g :cf(\<gamma>) \<rightarrow>\<^sub>< \<alpha>"
    "f O g :cf(\<gamma>) \<rightarrow>\<^sub>< \<gamma>"
    "cofinal_fun(f O g,\<gamma>,Memrel(\<gamma>))"
    using cofinal_fun_factorization by blast
  moreover from this
  have "g:cf(\<gamma>)\<rightarrow>\<alpha>"
    using mono_map_is_fun by simp
  moreover
  note \<open>Ord(\<alpha>)\<close>
  moreover from calculation and \<open>f :\<alpha> \<rightarrow>\<^sub>< \<gamma>\<close> \<open>Ord(\<gamma>)\<close>
  have "cf_fun(g,\<alpha>)"
    using factor_is_cofinal by blast
  moreover
  note \<open>\<alpha> = ordertype(A,Memrel(\<gamma>))\<close>
  ultimately
  show "cf(ordertype(A,Memrel(\<gamma>))) \<le> cf(\<gamma>)"
    using cf_le_domain_cofinal_fun[OF _ Ord_cf mono_map_is_fun] by simp
qed

lemma cf_idemp:
  assumes "Limit(\<gamma>)"
  shows "cf(\<gamma>) = cf(cf(\<gamma>))"
proof -
  from assms
  obtain A where "A\<subseteq>\<gamma>" "cofinal(A,\<gamma>,Memrel(\<gamma>))" "cf(\<gamma>) = ordertype(A,Memrel(\<gamma>))"
    using Limit_is_Ord cf_is_ordertype by blast
  with assms
  have "cf(\<gamma>) = cf(ordertype(A,Memrel(\<gamma>)))" using cf_ordertype_cofinal by simp
  also
  have "... = cf(cf(\<gamma>))"
    using \<open>cf(\<gamma>) = ordertype(A,Memrel(\<gamma>))\<close> by simp
  finally
  show "cf(\<gamma>) = cf(cf(\<gamma>))"  .
qed

lemma cf_le_cardinal:
  assumes "Limit(\<gamma>)"
  shows "cf(\<gamma>) \<le> |\<gamma>|"
proof -
  from assms
  have \<open>Ord(\<gamma>)\<close> using Limit_is_Ord by simp
  then
  obtain f where "f \<in> surj(|\<gamma>|,\<gamma>)"
    using Ord_cardinal_eqpoll unfolding eqpoll_def bij_def by blast
  with \<open>Ord(\<gamma>)\<close>
  show ?thesis
    using Card_is_Ord[OF Card_cardinal] surj_is_cofinal
      cf_le_domain_cofinal_fun[of \<gamma>] surj_is_fun by blast
qed

lemma regular_is_Card:
  notes le_imp_subset [dest]
  assumes "Limit(\<gamma>)" "\<gamma> = cf(\<gamma>)"
  shows "Card(\<gamma>)"
proof -
  from assms
  have "|\<gamma>| \<subseteq> \<gamma>"
    using Limit_is_Ord Ord_cardinal_le by blast
  also from \<open>\<gamma> = cf(\<gamma>)\<close>
  have "\<gamma> \<subseteq> cf(\<gamma>)" by simp
  finally
  have "|\<gamma>| \<subseteq> cf(\<gamma>)" .
  with assms
  show ?thesis unfolding Card_def using cf_le_cardinal by force
qed

lemma Limit_cf: assumes "Limit(\<kappa>)" shows "Limit(cf(\<kappa>))"
  using Ord_cf[of \<kappa>, THEN Ord_cases]
    \<comment> \<open>\<^term>\<open>cf(\<kappa>)\<close> being 0 or successor leads to contradiction\<close>
proof (cases)
  case 1
  with \<open>Limit(\<kappa>)\<close>
  show ?thesis using cf_zero_iff Limit_is_Ord by simp
next
  case (2 \<alpha>)
  moreover
  note \<open>Limit(\<kappa>)\<close>
  moreover from calculation
  have "cf(\<kappa>) = 1"
    using cf_idemp cf_succ by fastforce
  ultimately
  show ?thesis
    using succ_LimitE cf_eq_one_iff Limit_is_Ord
    by auto
qed

lemma InfCard_cf: "Limit(\<kappa>) \<Longrightarrow> InfCard(cf(\<kappa>))"
  using regular_is_Card cf_idemp Limit_cf nat_le_Limit Limit_cf
  unfolding InfCard_def by simp

lemma cf_le_cf_fun:
  notes [dest] = Limit_is_Ord
  assumes "cf(\<kappa>) \<le> \<nu>" "Limit(\<kappa>)"
  shows "\<exists>f.  f:\<nu> \<rightarrow> \<kappa>  \<and>  cf_fun(f, \<kappa>)"
proof -
  note assms
  moreover from this
  obtain h where h_cofinal_mono: "cf_fun(h,\<kappa>)"
    "h :cf(\<kappa>) \<rightarrow>\<^sub>< \<kappa>"
    "h : cf(\<kappa>) \<rightarrow> \<kappa>"
    using cofinal_mono_map_cf mono_map_is_fun by force
  moreover from calculation
  obtain g where "g \<in> inj(cf(\<kappa>), \<nu>)"
    using le_imp_lepoll by blast
  from this and calculation(2,3,5)
  obtain f where "f \<in> surj(\<nu>, cf(\<kappa>))" "f: \<nu> \<rightarrow> cf(\<kappa>)"
    using inj_imp_surj[OF _ Limit_has_0[THEN ltD]]
      surj_is_fun Limit_cf by blast
  moreover from this
  have "cf_fun(f,cf(\<kappa>))"
    using surj_is_cofinal by simp
  moreover
  note h_cofinal_mono \<open>Limit(\<kappa>)\<close>
  moreover from calculation
  have "cf_fun(h O f,\<kappa>)"
    using cf_fun_comp by blast
  moreover from calculation
  have "h O f \<in> \<nu> -> \<kappa>"
    using comp_fun by simp
  ultimately
  show ?thesis by blast
qed

lemma Limit_cofinal_fun_lt:
  notes [dest] = Limit_is_Ord
  assumes "Limit(\<kappa>)" "f: \<nu> \<rightarrow> \<kappa>" "cf_fun(f,\<kappa>)" "n\<in>\<kappa>"
  shows "\<exists>\<alpha>\<in>\<nu>. n < f`\<alpha>"
proof -
  from \<open>Limit(\<kappa>)\<close> \<open>n\<in>\<kappa>\<close>
  have "succ(n) \<in> \<kappa>"
    using Limit_has_succ[OF _ ltI, THEN ltD] by auto
  moreover
  note \<open>f: \<nu> \<rightarrow> _\<close>
  moreover from this
  have "domain(f) = \<nu>"
    using domain_of_fun by simp
  moreover
  note \<open>cf_fun(f,\<kappa>)\<close>
  ultimately
  obtain \<alpha> where "\<alpha> \<in> \<nu>" "succ(n) \<in> f`\<alpha> \<or> succ(n) = f `\<alpha>"
    using cf_funD[THEN cofinal_funD] by blast
  moreover from this
  consider (1) "succ(n) \<in> f`\<alpha>" | (2) "succ(n) = f `\<alpha>"
    by blast
  then
  have "n < f`\<alpha>"
  proof (cases)
    case 1
    moreover
    have "n \<in> succ(n)" by simp
    moreover
    note \<open>Limit(\<kappa>)\<close> \<open>f: \<nu> \<rightarrow> _\<close> \<open>\<alpha> \<in> \<nu>\<close>
    moreover from this
    have "Ord(f ` \<alpha>)"
      using apply_type[of f \<nu> "\<lambda>_. \<kappa>", THEN [2] Ord_in_Ord]
      by blast
    ultimately
    show ?thesis
      using Ord_trans[of n "succ(n)" "f ` \<alpha>"] ltI  by blast
  next
    case 2
    have "n \<in> f ` \<alpha>" by (simp add:2[symmetric])
    with \<open>Limit(\<kappa>)\<close> \<open>f: \<nu> \<rightarrow> _\<close> \<open>\<alpha> \<in> \<nu>\<close>
    show ?thesis
      using ltI
        apply_type[of f \<nu> "\<lambda>_. \<kappa>", THEN [2] Ord_in_Ord]
      by blast
  qed
  ultimately
  show ?thesis by blast
qed

context
  includes Ord_dests Aleph_dests Aleph_intros Aleph_mem_dests mono_map_rules
begin

text\<open>We end this section by calculating the cofinality of Alephs, for
the zero and limit case. The successor case depends on $\AC$.\<close>

lemma cf_nat: "cf(\<omega>) = \<omega>"
  using Limit_nat[THEN InfCard_cf] cf_le_cardinal[of \<omega>]
    Card_nat[THEN Card_cardinal_eq] le_anti_sym
  unfolding InfCard_def by auto

lemma cf_Aleph_zero: "cf(\<aleph>\<^bsub>0\<^esub>) = \<aleph>\<^bsub>0\<^esub>" 
  using cf_nat unfolding Aleph_def by simp

lemma cf_Aleph_Limit:
  assumes "Limit(\<gamma>)"
  shows "cf(\<aleph>\<^bsub>\<gamma>\<^esub>) = cf(\<gamma>)" 
proof -
  note \<open>Limit(\<gamma>)\<close>
  moreover from this
  have "(\<lambda>x\<in>\<gamma>. \<aleph>\<^bsub>x\<^esub>) : \<gamma> \<rightarrow> \<aleph>\<^bsub>\<gamma>\<^esub>" (is "?f : _ \<rightarrow> _")
    using lam_funtype[of _ Aleph] fun_weaken_type[of _ _ _ "\<aleph>\<^bsub>\<gamma>\<^esub>"] by blast
  moreover from \<open>Limit(\<gamma>)\<close>
  have "x \<in> y \<Longrightarrow> \<aleph>\<^bsub>x\<^esub> \<in> \<aleph>\<^bsub>y\<^esub>" if "x \<in> \<gamma>" "y \<in> \<gamma>" for x y
    using that Ord_in_Ord[of \<gamma>] Ord_trans[of _ _ \<gamma>] by blast
  ultimately
  have "?f \<in> mono_map(\<gamma>,Memrel(\<gamma>),\<aleph>\<^bsub>\<gamma>\<^esub>, Memrel(\<aleph>\<^bsub>\<gamma>\<^esub>))"
    by auto
  with  \<open>Limit(\<gamma>)\<close> 
  have "?f \<in> \<langle>\<gamma>, Memrel(\<gamma>)\<rangle> \<cong> \<langle>?f``\<gamma>, Memrel(\<aleph>\<^bsub>\<gamma>\<^esub>)\<rangle>"
    using mono_map_imp_ord_iso_Memrel[of \<gamma> "\<aleph>\<^bsub>\<gamma>\<^esub>" ?f] 
      Card_Aleph (* Already an intro rule, but need it explicitly *)
    by blast
  then
  have "converse(?f) \<in> \<langle>?f``\<gamma>, Memrel(\<aleph>\<^bsub>\<gamma>\<^esub>)\<rangle> \<cong> \<langle>\<gamma>, Memrel(\<gamma>)\<rangle>"
    using ord_iso_sym by simp
  with \<open>Limit(\<gamma>)\<close>
  have "ordertype(?f``\<gamma>, Memrel(\<aleph>\<^bsub>\<gamma>\<^esub>)) = \<gamma>"
    using ordertype_eq[OF _ well_ord_Memrel]
    ordertype_Memrel by auto
  moreover from \<open>Limit(\<gamma>)\<close>
  have "cofinal(?f``\<gamma>, \<aleph>\<^bsub>\<gamma>\<^esub>, Memrel(\<aleph>\<^bsub>\<gamma>\<^esub>))" 
    unfolding cofinal_def 
  proof (standard, intro ballI)
    fix a
    assume "a\<in>\<aleph>\<^bsub>\<gamma>\<^esub>" "\<aleph>\<^bsub>\<gamma>\<^esub> = (\<Union>i<\<gamma>. \<aleph>\<^bsub>i\<^esub>)"
    moreover from this
    obtain i where "i<\<gamma>" "a\<in>\<aleph>\<^bsub>i\<^esub>"
      by auto
    moreover from this and \<open>Limit(\<gamma>)\<close>
    have "Ord(i)" using ltD Ord_in_Ord by blast
    moreover from \<open>Limit(\<gamma>)\<close> and calculation
    have "succ(i) \<in> \<gamma>" using ltD by auto
    moreover from this and \<open>Ord(i)\<close>
    have "\<aleph>\<^bsub>i\<^esub> < \<aleph>\<^bsub>succ(i)\<^esub>" 
      by (auto) 
    ultimately
    have "\<langle>a,\<aleph>\<^bsub>i\<^esub>\<rangle> \<in> Memrel(\<aleph>\<^bsub>\<gamma>\<^esub>)"
      using ltD by (auto dest:Aleph_increasing)
    moreover from \<open>i<\<gamma>\<close>
    have "\<aleph>\<^bsub>i\<^esub> \<in> ?f``\<gamma>" 
      using ltD apply_in_image[OF \<open>?f : _ \<rightarrow> _\<close>] by auto
    ultimately
    show "\<exists>x\<in>?f `` \<gamma>. \<langle>a, x\<rangle> \<in> Memrel(\<aleph>\<^bsub>\<gamma>\<^esub>) \<or> a = x" by blast
  qed
  moreover
  note \<open>?f: \<gamma> \<rightarrow> \<aleph>\<^bsub>\<gamma>\<^esub>\<close> \<open>Limit(\<gamma>)\<close>
  ultimately
  show "cf(\<aleph>\<^bsub>\<gamma>\<^esub>) =  cf(\<gamma>)"
    using cf_ordertype_cofinal[OF Limit_Aleph Image_sub_codomain, of \<gamma> ?f \<gamma> \<gamma> ] 
      Limit_is_Ord by simp 
qed

end (* includes *)

end