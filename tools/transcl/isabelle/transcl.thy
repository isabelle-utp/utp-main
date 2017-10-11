(******************************************************************************)
(* External Algorithm for Calculating the Transitive Closure in Isabelle/HOL  *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(* Email: frank.zeyda@york.ac.uk                                              *)
(******************************************************************************)

section {* Transitive Closure Algorithm *}

theory transcl
imports Main Eisbach "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

subsection {* Configuration *}

text \<open>
  The \<open>transcl_home\<close> option sets the home directory of the \<open>transcl\<close> tool:
  this is the location of the \<open>transcl\<close> executable binary. By default, that
  location is derived from the location of the \<open>transcl\<close> theory file. Hence,
  the latter should, if possible, not be compiled into a heap but manually
  imported. Alternatively, by changing the value of this option, a custom
  tool path can be easily configured if needed.
\<close>

ML \<open>
  val transcl_thy_dir = Path.implode (* Use Path.smart_implode? *)
    (Path.append (Resources.master_directory @{theory}) Path.parent);
\<close>

ML \<open>
  val (transcl_home, transcl_home_setup) =
    Attrib.config_string @{binding transcl_home} (K transcl_thy_dir);
\<close>

setup \<open>transcl_home_setup\<close>

text \<open>
  The \<open>transcl_algorithm\<close> option determines the algorithm to be used by the
  tool for computation of the transitive closure. Possible values here have
  to correspond to implemented algorithms inside the tool. For now, they are
  \<open>floyd-warshall\<close> and \<open>boost\<close>, the latter using the C++ Boost Library. The
  default is \<open>floyd-warshall\<close> which seems to work efficiently for graphs up
  to approximately 1024 vertices.
\<close>

ML \<open>
  val (transcl_algorithm, transcl_algorithm_setup) =
    Attrib.config_string @{binding transcl_algorithm} (K "floyd-warshall");
\<close>

setup \<open>transcl_algorithm_setup\<close>

text \<open>
  The \<open>transcl_robust\<close> option specifies whether a more robust way of encoding
  the relation for the external tool should be used. By default, the relation
  is communicated in its pretty-printed form. If, however, this option is set
  to true, the elements of the relation are communicated as ML ASTs. This may,
  in practice, be slower but is invariant to peculiarities of the term printer.
  The default for this option is false.
\<close>

ML \<open>
  val (transcl_robust, transcl_robust_setup) =
    Attrib.config_bool @{binding transcl_robust} (K false);
\<close>

setup \<open>transcl_robust_setup\<close>

subsection {* Pre-Simplifier *}

text \<open>
  The PreSimplifier is used to automatically unfold definitions of relations
  and simplify the result in order to obtain an enumerated set of pairs. The
  \<open>TRUE\<close> predicate below is used as a dummy in order to obtain a theorem for
  some term \<open>t\<close> that can then be transformed using Isabelle's simplifications
  and rules. Pre-simplification steps are automatically preformed before some
  term is submitted to the \<open>transcl\<close> tool.
\<close>

definition TRUE :: "'a::type \<Rightarrow> bool" where
"TRUE t = True"

text \<open>Introduction lemma of \<open>TRUE t\<close> for some arbitrary term \<open>t\<close>.\<close>

lemma TRUE_t:
"TRUE t"
apply (unfold TRUE_def)
apply (rule TrueI)
done

text \<open>Inclusion of the ML program code.\<close>

ML_file "presimplify.ML"

subsection {* Tool and Rewriter *}

text \<open>
  The following constants are pseudo-operators: they are replaced by the result
  of applying the external \<open>transcl\<close> C++ algorithm to their arguments during an
  automatic rewriting step that is carried out after parsing a term. Note that
  their argument has to simplify to an (enumerated) set of pairs, otherwise it
  is not possible to apply the external algorithm. Whereas \<open>transcl(R)\<close> yields
  the transitive (positive) closure of a relation, \<open>rangecl(R)\<close> calculates the
  range of the transitive (positive) closure.
\<close>

consts transcl :: "'a rel \<Rightarrow> 'a rel" ("transcl'(_')")
consts rangecl :: "'a rel \<Rightarrow> 'a set" ("rangecl'(_')")

text \<open>Inclusion of the ML program code.\<close>

ML_file "transcl.ML"

text \<open>Configuration of additional term checkers (rewrite procedures).\<close>

setup {*
  Context.theory_map
    (Syntax_Phases.term_check 2 "transcl" Transcl_Rewriter.transcl_tr)
*}

setup {*
  Context.theory_map
    (Syntax_Phases.term_check 2 "rangecl" Transcl_Rewriter.rangecl_tr)
*}

text \<open>The following prevents use of the constants on their own.\<close>

hide_const transcl
hide_const rangecl

subsection {* Laws and Tactics *}

text \<open>Can we apply the following laws via an Eisbach tactic?\<close>

definition acyclic_witness:
"acyclic_witness C R \<longleftrightarrow> R \<subseteq> C \<and> C O R \<subseteq> C \<and> irrefl C"

lemma acyclic_witnessI:
"(\<exists>C. acyclic_witness C R) \<Longrightarrow> acyclic R"
apply (unfold acyclic_witness)
apply (clarify)
apply (subgoal_tac "R\<^sup>+ \<subseteq> C")
apply (meson acyclicI irrefl_def subset_iff)
apply (erule trancl_Int_subset)
apply (auto)
done

text \<open>
  It turns out that the lemma below sadly is useless in practice generating too
  strong assumptions. Hence, remove \<open>rangecl(_)\<close> and all related functionality
  from the transcl tool.
\<close>

lemma useless_acyclic_witnessI:
"\<exists>S. Range R \<subseteq> S \<and> Domain R \<inter> S = {} \<and> R `` S \<subseteq> S \<Longrightarrow> acyclic R"
apply (clarify)
apply (unfold acyclic_def)
apply (unfold set_eq_iff subset_iff)
apply (clarsimp)
apply (metis Domain.DomainI Range.intros trancl_domain trancl_range)
done

(*<*)
(********************)
(* WORK IN PROGRESS *)
(********************)

method_setup transcl_ex = \<open>
  Args.term >> (fn term => (fn ctx => Method.rule ctx [@{thm exI}]))
\<close>

method acyclic_tac =
  (match conclusion in "acyclic R" for R \<Rightarrow> \<open>print_term R\<close>)

subsection {* Examples *}

term "transcl({(A, B), (B, C), (A, D), (B, E)})"

definition myrel1 :: "string rel" where
"myrel1 = {(''A'', ''B''), (''B'', ''C''), (''A'', ''D''), (''B'', ''E'')}"

definition myrel2 :: "string rel" where
"myrel2 = {(''D'', ''A'')}"

definition myrel3 :: "nat rel" where
"myrel3 = {(1, 2), (2, 3), (1, 4), (2, 5)}"

term "transcl(myrel1)"
term "transcl(myrel2)"
term "transcl(myrel1 \<union> myrel2)"
term "transcl(myrel3)" -- \<open>Note that \<open>transcl(R)\<close> forces \<open>R\<close> to be homogeneous.\<close>

term "rangecl(myrel1)"
term "rangecl(myrel2)"
term "rangecl(myrel1 \<union> myrel2)"
term "rangecl(myrel3)" -- \<open>Note that \<open>transcl(R)\<close> forces \<open>R\<close> to be homogeneous.\<close>

hide_const myrel1 myrel2 myrel3
(*>*)
end