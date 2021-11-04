subsection\<open>Application to Cohen posets\label{sec:cohen}\<close>

theory Cohen_Posets
  imports 
    Delta_System

begin

text\<open>We end this session by applying DSL to the combinatorics of
finite function posets. We first define some basic concepts; we take
a different approach from \cite{2020arXiv200109715G}, in that the
order relation is presented as a predicate (of type @{typ \<open>[i,i] \<Rightarrow> o\<close>}). 

Two elements of a poset are \<^emph>\<open>compatible\<close> if they have a common lower
bound.\<close>

definition compat_in :: "[i,[i,i]\<Rightarrow>o,i,i]\<Rightarrow>o" where
  "compat_in(A,r,p,q) \<equiv> \<exists>d\<in>A . r(d,p) \<and> r(d,q)"

text\<open>An \<^emph>\<open>antichain\<close> is a subset of pairwise incompatible members.\<close>

definition
  antichain :: "[i,[i,i]\<Rightarrow>o,i]\<Rightarrow>o" where
  "antichain(P,leq,A) \<equiv> A\<subseteq>P \<and> (\<forall>p\<in>A. \<forall>q\<in>A.
                p\<noteq>q \<longrightarrow> \<not>compat_in(P,leq,p,q))"

text\<open>A poset has the  \<^emph>\<open>countable chain condition\<close> (ccc) if all of its
antichains are countable.\<close>

definition
  ccc :: "[i,[i,i]\<Rightarrow>o]\<Rightarrow>o" where
  "ccc(P,leq) \<equiv> \<forall>A. antichain(P,leq,A) \<longrightarrow> countable(A)"

text\<open>Finally, the \<^emph>\<open>Cohen poset\<close> is the set of finite partial functions
between two sets with the order of reverse inclusion.\<close>

definition
  Fn :: "[i,i] \<Rightarrow> i" where
  "Fn(I,J) \<equiv> \<Union>{(d\<rightarrow>J) . d \<in> {x \<in> Pow(I).  Finite(x)}}"

abbreviation
  Supset :: "i \<Rightarrow> i \<Rightarrow> o" (infixl \<open>\<supseteq>\<close> 50) where
  "f \<supseteq> g \<equiv> g \<subseteq> f"

lemma FnI[intro]:
  assumes "p : d \<rightarrow> J" "d \<subseteq> I" "Finite(d)"
  shows "p \<in> Fn(I,J)"
  using assms unfolding Fn_def by auto

lemma FnD[dest]:
  assumes "p \<in> Fn(I,J)"
  shows "\<exists>d. p : d \<rightarrow> J \<and> d \<subseteq> I \<and> Finite(d)"
  using assms unfolding Fn_def by auto

lemma Fn_is_function: "p \<in> Fn(I,J) \<Longrightarrow> function(p)"
  unfolding Fn_def using fun_is_function by auto

lemma restrict_eq_imp_compat:
  assumes "f \<in> Fn(I, J)" "g \<in> Fn(I, J)"
    "restrict(f, domain(f) \<inter> domain(g)) = restrict(g, domain(f) \<inter> domain(g))"
  shows "f \<union> g \<in> Fn(I, J)"
proof -
  from assms
  obtain d1 d2 where "f : d1 \<rightarrow> J" "d1 \<in> Pow(I)" "Finite(d1)"
    "g : d2 \<rightarrow> J" "d2 \<in> Pow(I)" "Finite(d2)"
    by blast
  with assms
  show ?thesis
    using domain_of_fun
      restrict_eq_imp_Un_into_Pi[of f d1 "\<lambda>_. J" g d2 "\<lambda>_. J"]
    by auto
qed

text\<open>We finally arrive to our application of DSL.\<close>

lemma ccc_Fn_2: "ccc(Fn(I,2), (\<supseteq>))"
proof -
  {
    fix A
    assume "\<not> countable(A)"
    assume "A \<subseteq> Fn(I, 2)"
    moreover from this
    have "countable({p\<in>A. domain(p) = d})" for d
    proof (cases "Finite(d) \<and> d \<subseteq> I")
      case True
      with \<open>A \<subseteq> Fn(I, 2)\<close>
      have "{p \<in> A . domain(p) = d} \<subseteq> d \<rightarrow> 2"
        using domain_of_fun by fastforce
      moreover from True
      have "Finite(d \<rightarrow> 2)"
        using Finite_Pi lesspoll_nat_is_Finite by auto
      ultimately
      show ?thesis using subset_Finite[of _ "d\<rightarrow>2" ] Finite_imp_countable
        by auto
    next
      case False
      with \<open>A \<subseteq> Fn(I, 2)\<close>
      have "{p \<in> A . domain(p) = d} = 0"
        by (intro equalityI) (auto dest!: domain_of_fun)
      then
      show ?thesis using empty_lepollI by auto
    qed
    moreover
    have "uncountable({domain(p) . p \<in> A})"
    proof
      from \<open>A \<subseteq> Fn(I, 2)\<close>
      have "A = (\<Union>d\<in>{domain(p) . p \<in> A}. {p\<in>A. domain(p) = d})"
        by auto
      moreover
      assume "countable({domain(p) . p \<in> A})"
      moreover
      note \<open>\<And>d. countable({p\<in>A. domain(p) = d})\<close> \<open>\<not>countable(A)\<close>
      ultimately
      show "False"
        using countable_imp_countable_UN[of "{domain(p). p\<in>A}"
            "\<lambda>d. {p \<in> A. domain(p) = d }"]
        by auto
    qed
    moreover from \<open>A \<subseteq> Fn(I, 2)\<close>
    have "p \<in> A \<Longrightarrow> Finite(domain(p))" for p
      using lesspoll_nat_is_Finite[of "domain(p)"]
        domain_of_fun[of p _ "\<lambda>_. 2"] by auto
    ultimately
    obtain D where "delta_system(D)" "D \<subseteq> {domain(p) . p \<in> A}" "D \<approx> \<aleph>\<^bsub>1\<^esub>"
      using delta_system_uncountable[of "{domain(p) . p \<in> A}"] by auto
    then
    have delta:"\<forall>d1\<in>D. \<forall>d2\<in>D. d1 \<noteq> d2 \<longrightarrow> d1 \<inter> d2 = \<Inter>D"
      using delta_system_root_eq_Inter
      by simp
    moreover from \<open>D \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
    have "uncountable(D)"
      using uncountable_iff_subset_eqpoll_Aleph1 by auto
    moreover from this and \<open>D \<subseteq> {domain(p) . p \<in> A}\<close>
    obtain p1 where "p1 \<in> A" "domain(p1) \<in> D"
      using uncountable_not_empty[of D] by blast
    moreover from this and \<open>p1 \<in> A \<Longrightarrow> Finite(domain(p1))\<close>
    have "Finite(domain(p1))" using Finite_domain by simp
    moreover
    define r where "r \<equiv> \<Inter>D"
    ultimately
    have "Finite(r)" using subset_Finite[of "r" "domain(p1)"] by auto
    have "countable({restrict(p,r) . p\<in>A})"
    proof -
      have "f \<in> Fn(I, 2) \<Longrightarrow> restrict(f,r) \<in> Pow(r \<times> 2)" for f
        using restrict_subset_Sigma[of f _ "\<lambda>_. 2" r]
        by (auto dest!:FnD simp: Pi_def) auto
      with \<open>A \<subseteq> Fn(I, 2)\<close>
      have "{restrict(f,r) . f \<in> A } \<subseteq> Pow(r \<times> 2)"
        by fast
      with \<open>Finite(r)\<close>
      show ?thesis
        using Finite_Sigma[THEN Finite_Pow, of r "\<lambda>_. 2"]
        by (intro Finite_imp_countable) (auto intro:subset_Finite)
    qed
    moreover
    have "uncountable({p\<in>A. domain(p) \<in> D})" (is "uncountable(?X)")
    proof
      from \<open>D \<subseteq> {domain(p) . p \<in> A}\<close>
      have "(\<lambda>p\<in>?X. domain(p)) \<in> surj(?X, D)"
        using lam_type unfolding surj_def by auto
      moreover
      assume "countable(?X)"
      moreover
      note \<open>uncountable(D)\<close>
      ultimately
      show False
        using surj_countable by auto
    qed
    moreover
    have "D = (\<Union>f\<in>Pow(r\<times>2) . {domain(p) . p\<in>{ x\<in>A. restrict(x,r) = f \<and> domain(x) \<in> D}})"
    proof -
      {
        fix z
        assume "z \<in> D"
        with \<open>D \<subseteq> _\<close>
        obtain p  where "domain(p) = z" "p \<in> A"
          by auto
        moreover from \<open>A \<subseteq> Fn(I, 2)\<close> and this
        have "p : z \<rightarrow> 2"
          using domain_of_fun by (auto dest!:FnD)
        moreover from this
        have "restrict(p,r) \<subseteq> r \<times> 2"
          using function_restrictI[of p r] fun_is_function[of p z "\<lambda>_. 2"]
            restrict_subset_Sigma[of p z "\<lambda>_. 2" r]
          by (auto simp:Pi_def)
        ultimately
        have "\<exists>p\<in>A.  restrict(p,r) \<in> Pow(r\<times>2) \<and> domain(p) = z" by auto
      }
      then
      show ?thesis
        by (intro equalityI) (force)+
    qed
    obtain f where "uncountable({domain(p) . p\<in>{x\<in>A. restrict(x,r) = f \<and> domain(x) \<in> D}})"
      (is "uncountable(?Y(f))")
    proof -
      {
        from \<open>Finite(r)\<close>
        have "countable(Pow(r\<times>2))"
          using Finite_Sigma[THEN Finite_Pow, THEN Finite_imp_countable]
          by simp
        moreover
        assume "countable(?Y(f))" for f
        moreover
        note \<open>D = (\<Union>f\<in>Pow(r\<times>2) .?Y(f))\<close>
        moreover
        note \<open>uncountable(D)\<close>
        ultimately
        have "False"
          using countable_imp_countable_UN[of "Pow(r\<times>2)" ?Y] by auto
      }
      with that
      show ?thesis by auto
    qed
    then
    obtain j where "j \<in> inj(nat, ?Y(f))"
      using uncountable_iff_nat_lt_cardinal[THEN iffD1, THEN leI,
          THEN cardinal_le_imp_lepoll, THEN lepollD]
      by auto
    then
    have "j`0 \<noteq> j`1" "j`0 \<in> ?Y(f)" "j`1 \<in> ?Y(f)"
      using inj_is_fun[THEN apply_type, of j nat "?Y(f)"]
      unfolding inj_def by auto
    then
    obtain p q where "domain(p) \<noteq> domain(q)" "p \<in> A" "q \<in> A"
      "domain(p) \<in> D" "domain(q) \<in> D"
      "restrict(p,r) = restrict(q,r)" by auto
    moreover from this and delta
    have "domain(p) \<inter> domain(q) = r" unfolding r_def by simp
    moreover
    note \<open>A \<subseteq> Fn(I, 2)\<close>
    moreover from calculation
    have "p \<union> q \<in> Fn(I, 2)"
      by (rule_tac restrict_eq_imp_compat) auto
    ultimately
    have "\<exists>p\<in>A. \<exists>q\<in>A. p \<noteq> q \<and> compat_in(Fn(I, 2), (\<supseteq>), p, q)"
      unfolding compat_in_def
      by (rule_tac bexI[of _ p], rule_tac bexI[of _ q]) blast
  }
  then
  show ?thesis unfolding ccc_def antichain_def by auto
qed

text\<open>The fact that a poset $P$ has the ccc has useful consequences for the
theory of forcing, since it implies that cardinals from the original
model are exactly the cardinals in any generic extension by $P$
\cite[Chap.~IV]{kunen2011set}.\<close>

end