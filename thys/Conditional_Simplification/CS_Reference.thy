(* Copyright 2021 (C) Mihails Milehins *)

theory CS_Reference
  imports
    IHOL_CS
    Reference_Prerequisites
begin




section\<open>Introduction\<close>



subsection\<open>Background\<close>


text\<open>
This document presents a reference manual for the framework CS. The framework CS
is a collection of experimental tactics and associated proof methods 
aimed at the automation of conditional simplification  
in the object logic Isabelle/HOL
of the formal proof assistant Isabelle. The methods
that are provided in the collection offer the functionality that is similar to
certain aspects of the functionality provided by the standard proof 
methods of Isabelle that combine classical reasoning and simplification 
(e.g., the method @{method auto} 
\cite{nipkow_isabellehol_2002, wenzel_isabelle/isar_2019-1}), 
but there are notable differences. More specifically, the methods provided in 
the collection allow for the side conditions of
the rewrite rules to be solved via intro-resolution.
\<close>



subsection\<open>Purpose and scope\<close>


text\<open>
The primary functionality of the framework is available via 
the proof methods @{method cs_concl_step}, @{method cs_prems_atom_step} and
@{method cs_intro_step}.
The methods @{method cs_concl_step} and @{method cs_prems_atom_step}
accept a collection of (conditional) rewrite rules and execute
one rewrite step on the conclusion or a premise of some goal, 
respectively. The application of the rewrite step produces new goals that
are associated with the premises of the rewrite rules. These 
goals are meant to be discharged via a recursive application 
of either @{method cs_intro_step} or @{method cs_concl_step}.
The procedure outlined above was automated and made available as part
of the proof methods @{method cs_concl} and @{method cs_prems}.
\<close>



subsection\<open>Related and previous work\<close>


text\<open>
No claim with regard to the originality of the algorithms used in the methods
implemented as part of the CS is made and, due to the experimental
and evolving nature of this work, a comprehensive literature review
is considered to be outside its scope. Therefore, the only contributions
claimed by the author are the implementation of the algorithms associated 
with the methods provided as part of the CS in 
\textit{Isabelle/ML} \cite{milner_definition_1997, wenzel_isabelle/isar_2019} 
and their integration with the Isabelle/Isar infrastructure.

The implementation of the methods associated with the framework builds 
upon the existing infrastructure of Isabelle and provides only a very 
thin layer of additional or alternative functionality. As such, it may be 
possible to achieve integration of the functionality offered by the CS with the 
standard infrastructure for classical reasoning and simplification 
in Isabelle.

It should also be mentioned that the Isabelle/ML code from the 
main distribution of Isabelle2020 and from
\textit{The Isabelle/ML Cookbook} \cite{urban_isabelle_2019} was frequently 
reused (with amendments) during the development of the library. Some particular
examples of such reuse include 
\begin{itemize}
\item The adoption of the code for the tactic \<open>remdups_tac\<close> from the file
\<open>~/Tools/Intuitionistic.ML\<close>.
\item The adoption of the code presented in subsection 3.3 of 
\cite{urban_isabelle_2019} for higher-order matching and unification.
\end{itemize}
\<close>

text\<open>\newpage\<close>



section\<open>Syntax\<close>


text\<open>
This section presents the syntactic categories that are associated with the 
methods @{method cs_concl_step}, @{method cs_intro_step}, 
@{method cs_intro_search}, @{method cs_concl},  
@{method cs_prems_atom_step} and @{method cs_prems}. 
It is important to note that the presentation is only approximate.
\<close>


text\<open>

\begin{matharray}{rcl}
  @{method_def cs_concl_step} & : & \<open>method\<close>\\
  @{method_def cs_intro_step} & : & \<open>method\<close>\\
  @{method_def cs_intro_search} & : & \<open>method\<close>\\
  @{method_def cs_concl} & : & \<open>method\<close>\\
  @{method_def cs_prems_atom_step} & : & \<open>method\<close>\\
  @{method_def cs_prems} & : & \<open>method\<close>
\end{matharray}

  \<^medskip>

  \<^rail>\<open>
    @@{method cs_concl_step} thms
    ;
    @@{method cs_intro_step} thms
    ;
    @@{method cs_intro_search} thms
    ;
    @@{method cs_concl}
      ((@'cs_full')?) ((@'cs_ist_simple')?) ((cs_simp cs_intro)*)
    ;
    @@{method cs_prems_atom_step} thms
    ;
    @@{method cs_prems} 
      ((@'cs_full')?) ((@'cs_ist_simple')?) ((cs_simp cs_intro)*)
    ;
    cs_simp: (@'cs_simp' @':' thms)? 
    ;
    cs_intro: (@'cs_intro' @':' thms)?
  \<close>

  \<^descr> @{method cs_concl_step} \<open>thms\<close> performs a single rewrite step of 
the conclusion of some goal using the collection of the rewrite rules \<open>thms\<close>.
The rewriting is performed via the intro-resolution with the 
rewrite rule stated in an altered form: the application of 
@{method cs_concl_step} may produce new subgoals that are associated with 
the premises of the applied rewrite rule.
  \<^descr> @{method cs_intro_step} \<open>thms\<close> performs a single refinement step 
via intro-resolution. 
  \<^descr> @{method cs_intro_search} \<open>thms\<close> attempts to solve a single goal 
using a search procedure based on the algorithm outlined
in the description of the method @{method cs_intro_step}.
  \<^descr> @{method cs_concl} 
(@{element "cs_full"}) (@{element "cs_ist_simple"}) 
@{element "cs_simp"} \<open>:\<close> \<open>simp_thms\<close> @{element "cs_intro"} \<open>:\<close> \<open>intro_thms\<close> 
attempts to solve a single goal using a search procedure that employs 
the method applications @{method cs_concl_step} \<open>simp_thms\<close> 
and @{method cs_intro_step} \<open>intro_thms\<close> as individual steps.
If the optional argument @{element "cs_full"} is provided during the
invocation of the proof method, all possible rule-term
matches are considered. Otherwise, only a single sensible default match
is used for every applicable rule-term pair. If the optional
argument @{element "cs_ist_simple"} is provided, then the search space
of the method is expanded by allowing backtracking after every atomic
step (the default behavior uses a tailor-made empirically established
routine that can be inferred from the implementation of the method).
  \<^descr> @{method cs_prems_atom_step} \<open>thms\<close> performs a single rewrite step of 
the first premise of some goal using the collection of the rewrite rules \<open>thms\<close>.
  \<^descr> @{method cs_prems} 
(@{element "cs_full"}) (@{element "cs_ist_simple"}) 
@{element "cs_simp"} \<open>:\<close> \<open>simp_thms\<close>
@{element "cs_intro"} \<open>:\<close> \<open>intro_thms\<close> 
repeatedly performs a single rewrite step of 
the first premise of some goal using the collection of the rewrite rules 
\<open>simp_thms\<close>, followed by an attempt to solve all but the final subgoal using
the method application 
\<open>(\<close>@{method cs_concl} @{element "cs_simp"} \<open>:\<close> \<open>simp_thms\<close> 
@{element "cs_intro"} \<open>:\<close> \<open>intro_thms\<close>\<open>)\<close>.
@{element "cs_full"} and @{element "cs_ist_simple"} serve a purpose that 
is similar to their purpose in @{method cs_concl}. 
\<close>

text\<open>\newpage\<close>



section\<open>Known issues and limitations\<close>


text\<open>
The collection of the proof methods that are associated with the framework CS  
is a result of experimentation during practical formalization 
work. The CS should be viewed as an idea or
a proposal for further development, rather than a finished product. 
The limitations and the performance of the methods associated with the CS 
have not been investigated and there is little guarantee that they will be 
suitable for any specific target application.
It is also important to note that the methods have only been tested 
extensively on the subgoals that do not contain any explicit occurrences 
of the \textit{Isabelle/Pure} \cite{paulson_foundation_1989}
universal quantifier. Only very limited and highly experimental
support for the first-/higher-order reasoning is provided by 
the CS.
\<close>

end