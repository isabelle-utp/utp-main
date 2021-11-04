theory sse_boolean_algebra
  imports Main
begin

declare[[syntax_ambiguity_warning=false]]
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

section \<open>Shallow embedding of a Boolean algebra of propositions\<close>

text\<open>\noindent{In this section we present a shallow semantical embedding (SSE, cf. @{cite J41} and @{cite J23})
for a family of logics whose semantics is based upon extensions of (complete and atomic) Boolean algebras.
The range of such logics is indeed very wide, including, as we will see, quantified paraconsistent and
paracomplete (e.g. intuitionistic) logics. Aside from illustrating how the SSE approach works in practice
we show how it allows us to effectively harness theorem provers, model finders and `hammers' for reasoning
with quantified non-classical logics. Proof reconstructions have deliberately been avoided.
Most of the proofs (in fact, all one-liners) have been found using Sledgehammer.}\<close>

text\<open>\noindent{Two notions play a fundamental role in this work: propositions and propositional functions.
Propositions, qua sentence denotations, are modeled as objects of type @{text "w\<Rightarrow>bool"} (shortened as @{text "\<sigma>"}).
Propositional functions, as the name indicates, are basically anything with a (parametric) type @{text "'t\<Rightarrow>\<sigma>"}.}\<close>

text\<open>\noindent{We introduce a type @{text "w"} for the domain of points (aka. 'worlds', 'states', etc.).
@{text "\<sigma>"} is a type alias for sets of points (i.e. propositions) encoded as characteristic functions.}\<close>
typedecl w                  
type_synonym \<sigma> = "w\<Rightarrow>bool"

text\<open>\noindent{In the sequel, we introduce the following naming convention for variables:

(i) Latin letters (A, b, M, P, q, X, y, etc.) denote in general propositions (type @{text "\<sigma>"});
however, we reserve letters D and S to denote sets of propositions (aka. domains/spaces) and
the letters u, v and w to denote worlds/points.

(ii) Greek letters (in particular @{text "\<pi>"}) denote propositional functions (type @{text "'t\<Rightarrow>\<sigma>"});
among the latter we may employ the letters @{text "\<phi>"}, @{text "\<psi>"} and @{text "\<eta>"} to explicitly
name those corresponding to unary connectives/operations (type @{text "\<sigma>\<Rightarrow>\<sigma>"}).}\<close>

subsection \<open>Encoding Boolean operations\<close>

text\<open>\noindent{We start with an ordered algebra,}\<close>
abbreviation sequ::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infixr "\<^bold>\<approx>" 45) where "A \<^bold>\<approx> B \<equiv> \<forall>w. (A w) \<longleftrightarrow> (B w)"
abbreviation subs::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infixr "\<^bold>\<preceq>" 45) where "A \<^bold>\<preceq> B \<equiv> \<forall>w. (A w) \<longrightarrow> (B w)"
abbreviation sups::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" (infixr "\<^bold>\<succeq>" 45) where "B \<^bold>\<succeq> A \<equiv> A \<^bold>\<preceq> B"

text\<open>\noindent{define meet and join by reusing HOL metalogical conjunction and disjunction,}\<close>
definition meet::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<and>" 54) where "A \<^bold>\<and> B \<equiv> \<lambda>w. (A w) \<and> (B w)"
definition join::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<or>" 53) where "A \<^bold>\<or> B \<equiv> \<lambda>w. (A w) \<or> (B w)"

text\<open>\noindent{and introduce further operations to obtain a Boolean 'algebra of propositions'.}\<close>
definition top::"\<sigma>" ("\<^bold>\<top>")    where "\<^bold>\<top> \<equiv> \<lambda>w. True"
definition bottom::"\<sigma>" ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
definition impl::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<rightarrow>" 51) where "A \<^bold>\<rightarrow> B \<equiv> \<lambda>w. (A w)\<longrightarrow>(B w)"
definition dimp::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<leftrightarrow>" 51) where "A \<^bold>\<leftrightarrow> B \<equiv> \<lambda>w. (A w)\<longleftrightarrow>(B w)"
definition diff::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr "\<^bold>\<leftharpoonup>" 51) where "A \<^bold>\<leftharpoonup> B \<equiv> \<lambda>w. (A w) \<and> \<not>(B w)"
definition compl::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<midarrow>_" [57]58) where "\<^bold>\<midarrow>A  \<equiv> \<lambda>w. \<not>(A w)"

named_theorems conn (*algebraic connectives*)
declare meet_def[conn] join_def[conn] top_def[conn] bottom_def[conn]
        impl_def[conn] dimp_def[conn] diff_def[conn] compl_def[conn]

text\<open>\noindent{Quite trivially, we can verify that the algebra satisfies some essential lattice properties.}\<close>
lemma "a \<^bold>\<or> a \<^bold>\<approx> a" unfolding conn by simp
lemma "a \<^bold>\<and> a \<^bold>\<approx> a" unfolding conn by simp
lemma "a \<^bold>\<preceq> a \<^bold>\<or> b" unfolding conn by simp
lemma "a \<^bold>\<and> b \<^bold>\<preceq> a" unfolding conn by simp
lemma "(a \<^bold>\<and> b) \<^bold>\<or> b \<^bold>\<approx> b" unfolding conn by auto (*absorption 1*)
lemma "a \<^bold>\<and> (a \<^bold>\<or> b) \<^bold>\<approx> a" unfolding conn by auto (*absorption 2*)
lemma "a \<^bold>\<preceq> c \<Longrightarrow> b \<^bold>\<preceq> c \<Longrightarrow> a \<^bold>\<or> b \<^bold>\<preceq> c" unfolding conn by simp
lemma "c \<^bold>\<preceq> a \<Longrightarrow> c \<^bold>\<preceq> b \<Longrightarrow> c \<^bold>\<preceq> a \<^bold>\<and> b" unfolding conn by simp
lemma "a \<^bold>\<preceq> b \<equiv> (a \<^bold>\<or> b) \<^bold>\<approx> b" unfolding conn by smt
lemma "b \<^bold>\<preceq> a \<equiv> (a \<^bold>\<and> b) \<^bold>\<approx> b" unfolding conn by smt
lemma "a \<^bold>\<preceq> c \<Longrightarrow> b \<^bold>\<preceq> d \<Longrightarrow> (a \<^bold>\<or> b) \<^bold>\<preceq> (c \<^bold>\<or> d)" unfolding conn by simp
lemma "a \<^bold>\<preceq> c \<Longrightarrow> b \<^bold>\<preceq> d \<Longrightarrow> (a \<^bold>\<and> b) \<^bold>\<preceq> (c \<^bold>\<and> d)" unfolding conn by simp


subsection \<open>Second-order operations and fixed-points\<close>

text\<open>\noindent{We define equality for propositional functions as follows.}\<close>
definition equal_op::"('t\<Rightarrow>\<sigma>)\<Rightarrow>('t\<Rightarrow>\<sigma>)\<Rightarrow>bool" (infix "\<^bold>\<equiv>" 60) where "\<phi> \<^bold>\<equiv> \<psi> \<equiv> \<forall>X. \<phi> X \<^bold>\<approx> \<psi> X"

text\<open>\noindent{Moreover, we define some useful Boolean (2nd-order) operations on propositional functions,}\<close>
abbreviation unionOp::"('t\<Rightarrow>\<sigma>)\<Rightarrow>('t\<Rightarrow>\<sigma>)\<Rightarrow>('t\<Rightarrow>\<sigma>)" (infixr "\<^bold>\<squnion>" 61) where "\<phi> \<^bold>\<squnion> \<psi> \<equiv> \<lambda>X. \<phi> X \<^bold>\<or> \<psi> X"
abbreviation interOp::"('t\<Rightarrow>\<sigma>)\<Rightarrow>('t\<Rightarrow>\<sigma>)\<Rightarrow>('t\<Rightarrow>\<sigma>)" (infixr "\<^bold>\<sqinter>" 62) where "\<phi> \<^bold>\<sqinter> \<psi> \<equiv> \<lambda>X. \<phi> X \<^bold>\<and> \<psi> X"
abbreviation compOp::"('t\<Rightarrow>\<sigma>)\<Rightarrow>('t\<Rightarrow>\<sigma>)" ("(_\<^sup>c)") where "\<phi>\<^sup>c \<equiv> \<lambda>X. \<^bold>\<midarrow>\<phi> X"
text\<open>\noindent{some of them explicitly targeting operations,}\<close>
definition dual::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("(_\<^sup>d)") where "\<phi>\<^sup>d \<equiv> \<lambda>X. \<^bold>\<midarrow>(\<phi>(\<^bold>\<midarrow>X))"
text\<open>\noindent{and also define an useful operation (for technical purposes).}\<close>
definition id::"\<sigma>\<Rightarrow>\<sigma>" ("id") where "id A \<equiv> A"

text\<open>\noindent{We now prove some useful lemmas (some of them may help the provers in their hard work).}\<close>
lemma comp_symm: "\<phi>\<^sup>c = \<psi> \<Longrightarrow> \<phi> = \<psi>\<^sup>c" unfolding conn by blast
lemma comp_invol: "\<phi>\<^sup>c\<^sup>c = \<phi>" unfolding conn by blast
lemma dual_symm: "(\<phi> \<equiv> \<psi>\<^sup>d) \<Longrightarrow> (\<psi> \<equiv> \<phi>\<^sup>d)" unfolding dual_def conn by simp
lemma dual_comp: "\<phi>\<^sup>d\<^sup>c = \<phi>\<^sup>c\<^sup>d" unfolding dual_def by simp

lemma "id\<^sup>d \<^bold>\<equiv> id"  by (simp add: id_def dual_def equal_op_def conn)
lemma "id\<^sup>c \<^bold>\<equiv> compl"  by (simp add: id_def dual_def equal_op_def conn)
lemma "(A \<^bold>\<squnion> B)\<^sup>d \<^bold>\<equiv> (A\<^sup>d) \<^bold>\<sqinter> (B\<^sup>d)" by (simp add: dual_def equal_op_def conn)
lemma "(A \<^bold>\<squnion> B)\<^sup>c \<^bold>\<equiv> (A\<^sup>c) \<^bold>\<sqinter> (B\<^sup>c)" by (simp add: equal_op_def conn)
lemma "(A \<^bold>\<sqinter> B)\<^sup>d \<^bold>\<equiv> (A\<^sup>d) \<^bold>\<squnion> (B\<^sup>d)" by (simp add: dual_def equal_op_def conn)
lemma "(A \<^bold>\<sqinter> B)\<^sup>c \<^bold>\<equiv> (A\<^sup>c) \<^bold>\<squnion> (B\<^sup>c)" by (simp add: equal_op_def conn)

text\<open>\noindent{The notion of a fixed point is a fundamental one. We speak of propositions being fixed points of
operations. For a given operation we define in the usual way a fixed-point predicate for propositions.}\<close>
abbreviation fixedpoint::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>bool)" ("fp") where "fp \<phi> \<equiv> \<lambda>X. \<phi> X \<^bold>\<approx> X"

lemma fp_d: "(fp \<phi>\<^sup>d) X = (fp \<phi>)(\<^bold>\<midarrow>X)" unfolding dual_def conn by auto
lemma fp_c: "(fp \<phi>\<^sup>c) X = (X \<^bold>\<approx> \<^bold>\<midarrow>(\<phi> X))" unfolding conn by auto
lemma fp_dc:"(fp \<phi>\<^sup>d\<^sup>c) X = (X \<^bold>\<approx> \<phi>(\<^bold>\<midarrow>X))" unfolding dual_def conn by auto

text\<open>\noindent{Indeed, we can 'operationalize' this predicate by defining a fixed-point operator as follows:}\<close>
abbreviation fixedpoint_op::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("(_\<^sup>f\<^sup>p)") where "\<phi>\<^sup>f\<^sup>p  \<equiv> \<lambda>X. (\<phi> X) \<^bold>\<leftrightarrow> X"

lemma ofp_c: "(\<phi>\<^sup>c)\<^sup>f\<^sup>p \<^bold>\<equiv> (\<phi>\<^sup>f\<^sup>p)\<^sup>c" unfolding conn equal_op_def by auto
lemma ofp_d: "(\<phi>\<^sup>d)\<^sup>f\<^sup>p \<^bold>\<equiv> (\<phi>\<^sup>f\<^sup>p)\<^sup>d\<^sup>c" unfolding dual_def equal_op_def conn by auto
lemma ofp_dc:"(\<phi>\<^sup>d\<^sup>c)\<^sup>f\<^sup>p \<^bold>\<equiv> (\<phi>\<^sup>f\<^sup>p)\<^sup>d" unfolding dual_def equal_op_def conn by auto
lemma ofp_decomp: "\<phi>\<^sup>f\<^sup>p \<^bold>\<equiv> (id \<^bold>\<sqinter> \<phi>) \<^bold>\<squnion> ((id \<^bold>\<squnion> \<phi>)\<^sup>c)" unfolding equal_op_def id_def conn by auto
lemma ofp_invol: "(\<phi>\<^sup>f\<^sup>p)\<^sup>f\<^sup>p \<^bold>\<equiv> \<phi>" unfolding conn equal_op_def by auto

text\<open>\noindent{Fixed-point predicate and fixed-point operator are closely related.}\<close>
lemma fp_rel: "((fp \<phi>) X) = (\<phi>\<^sup>f\<^sup>p X \<^bold>\<approx> \<^bold>\<top>)" unfolding conn by auto
lemma fp_d_rel:  "((fp \<phi>\<^sup>d) X) = (\<phi>\<^sup>f\<^sup>p(\<^bold>\<midarrow>X) \<^bold>\<approx> \<^bold>\<top>)" unfolding dual_def conn by auto
lemma fp_c_rel: "((fp \<phi>\<^sup>c) X) = (\<phi>\<^sup>f\<^sup>p  X  \<^bold>\<approx> \<^bold>\<bottom>)" unfolding conn by auto
lemma fp_dc_rel: "((fp \<phi>\<^sup>d\<^sup>c) X) = (\<phi>\<^sup>f\<^sup>p(\<^bold>\<midarrow>X) \<^bold>\<approx> \<^bold>\<bottom>)" unfolding dual_def conn by auto


subsection \<open>Equality and atomicity\<close>

text\<open>\noindent{We prove some facts about equality (which may help improve prover's performance).}\<close>
lemma eq_ext: "a \<^bold>\<approx> b \<Longrightarrow>  a = b" using ext by blast
lemma eq_ext': "a \<^bold>\<equiv> b \<Longrightarrow>  a = b" using ext unfolding equal_op_def by blast
lemma meet_char: "a \<^bold>\<preceq> b \<longleftrightarrow> a \<^bold>\<and> b \<^bold>\<approx> a" unfolding conn by blast
lemma join_char: "a \<^bold>\<preceq> b \<longleftrightarrow> a \<^bold>\<or> b \<^bold>\<approx> b" unfolding conn  by blast
 
text\<open>\noindent{We can verify indeed that the algebra is atomic (in three different ways) by relying on the
presence of primitive equality in HOL. A more general class of Boolean algebras could in principle
be obtained in systems without primitive equality or by suitably restricting quantification over
propositions (e.g. defining a topology and restricting quantifiers to open/closed sets).}\<close>
definition "atom a \<equiv> \<not>(a \<^bold>\<approx> \<^bold>\<bottom>) \<and> (\<forall>p. a \<^bold>\<preceq> p \<or> a \<^bold>\<preceq> \<^bold>\<midarrow>p)"
lemma atomic1: "\<forall>w. \<exists>q. q w \<and> (\<forall>p. p w \<longrightarrow> q \<^bold>\<preceq> p)" using the_sym_eq_trivial by (metis (full_types))
lemma atomic2: "\<forall>w. \<exists>q. q w \<and> atom(q)" using the_sym_eq_trivial by (metis (full_types) atom_def compl_def bottom_def)
lemma atomic3: "\<forall>p. \<not>(p \<^bold>\<approx> \<^bold>\<bottom>) \<longrightarrow> (\<exists>q. atom(q) \<and> q \<^bold>\<preceq> p)" proof - (*using atom_def unfolding conn by fastforce*)
  { fix p
    { assume "\<not>(p \<^bold>\<approx> \<^bold>\<bottom>)"
      hence "\<exists>v. p v" unfolding conn by simp
      then obtain w where 1:"p w" by (rule exE)
      let ?q="\<lambda>v. v = w" (*using HOL primitive equality*)
      have 2: "atom ?q" unfolding atom_def unfolding conn by simp
      have "\<forall>v. ?q v \<longrightarrow> p v" using 1 by simp
      hence 3: "?q \<^bold>\<preceq> p" by simp
      from 2 3 have "\<exists>q. atom(q) \<and> q \<^bold>\<preceq> p" by blast
    } hence "\<not>(p \<^bold>\<approx> \<^bold>\<bottom>) \<longrightarrow> (\<exists>q. atom(q) \<and> q \<^bold>\<preceq> p)" by (rule impI)
  } thus ?thesis by (rule allI)
qed

end
