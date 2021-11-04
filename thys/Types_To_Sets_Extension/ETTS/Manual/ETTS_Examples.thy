(* Title: ETTS/Manual/ETTS_Examples.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)


section\<open>ETTS by example\<close>
theory ETTS_Examples
  imports 
    ETTS_Syntax
    Complex_Main
begin



subsection\<open>Background\<close>


text\<open>
In this section, some of the capabilities of the extension of the framework
Types-To-Sets are demonstrated by example. The examples that are presented 
in this section are expected to be sufficient to begin an independent 
exploration of the extension, but do not cover the entire spectrum of its 
functionality.
\<close>



subsection\<open>First steps\<close>


subsubsection\<open>Problem statement\<close>


text\<open>
Consider the task of the relativization of the type-based theorem 
@{thm [source] topological_space_class.closed_Un} from the standard library
of Isabelle/HOL:
\begin{center}
@{thm [names_short = true] topological_space_class.closed_Un[no_vars]},
\end{center}
where \<open>S::'a::topological_space set\<close> and \<open>T::'a::topological_space set\<close>.
\<close>


subsubsection\<open>Unoverloading\<close>


text\<open>
The constant @{const closed} that occurs in the theorem is an overloaded
constant defined as \mbox{@{thm [names_short = true] closed_def[no_vars]}}
for any @{term [show_sorts] "S::'a::topological_space set"}. 
The constant may be unoverloaded with 
the help of the command @{command ud} that is provided as part of 
the framework CTR:
\<close>
ud \<open>topological_space.closed\<close>
ud closed' \<open>closed\<close>
text\<open>
This invocation declares the constant @{const closed.with} that is defined as
\begin{center}
@{thm closed.with_def[no_vars]}
\end{center}
and provides the theorems @{thm [source] closed.with} given by
\begin{center}
@{thm closed.with[no_vars]}
\end{center}
and @{thm [source] closed'.with} given by 
\begin{center}
@{thm closed'.with[no_vars]}
\end{center}
These theorems
are automatically added to the dynamic fact @{thm [source] ud_with}.
\<close>


subsubsection\<open>Conditional transfer rules\<close>


text\<open>
Before the relativization can be performed, the transfer rules need to be 
available for each constant that occurs in the type-based theorem 
immediately after step 4 of the KERA. 
All binary relations that are used in the transfer rules must be 
at least right total and bi-unique (assuming the default order on predicates in 
Isabelle/HOL). For the theorem 
@{thm [source] topological_space_class.closed_Un}, there are two such constants:
@{const class.topological_space} and @{const closed.with}.
The transfer rules can be obtained with the help of the command @{command ctr} 
from the framework CTR. The process may involve
the synthesis of further relativized constants, as described in the
reference manual for the framework CTR.
\<close>
ctr
  relativization
  synthesis ctr_simps
  assumes [transfer_domain_rule]: "Domainp A = (\<lambda>x. x \<in> U)"
    and [transfer_rule]: "right_total A" "bi_unique A"
  trp (?'a A)
  in topological_space_ow: class.topological_space_def
    and closed_ow: closed.with_def


subsubsection\<open>Relativization\<close>


text\<open>
As mentioned previously, the relativization of theorems can only
be performed from within a suitable tts context. In setting up the tts context,
the users always need to provide the RI specification elements that are 
compatible with the theorems that are meant to be relativized in the 
tts context. The set of the schematic type variables that occur in the theorem 
@{thm [source] topological_space_class.closed_Un} is \<open>{\<close>\<open>?'a\<close>\<open>}\<close>. 
Thus, there needs to be exactly one RI specification element of the form 
(\<open>?'a\<close>, @{term [show_types] "U::'a set"}):
\<close>
tts_context
  tts: (?'a to \<open>U::'a set\<close>)
begin

text\<open>
The relativization can be performed by invoking the command 
@{command tts_lemmas} in the following manner:
\<close>
tts_lemmas? in closed_Un' = topological_space_class.closed_Un
text\<open>
In this case, the command was invoked in the active mode, providing
an active area that can be used to insert the following theorem directly
into the theory file:
\<close>

tts_lemma closed_Un':
  assumes "U \<noteq> {}"
    and "\<forall>x\<in>S. x \<in> U"
    and "\<forall>x\<in>T. x \<in> U"
    and "topological_space_ow U opena"
    and "closed_ow U opena S"
    and "closed_ow U opena T"
  shows "closed_ow U opena (S \<union> T)"
    is topological_space_class.closed_Un.

text\<open>
The invocation of the command @{command tts_lemmas} in the
active mode can be removed with no effect on the theorems that 
were generated using the command.
\<close>

end

text\<open>
While our goal was achieved, that is, the theorem 
@{thm [source] closed_Un'} is, indeed, a relativization
of the theorem @{thm [source] topological_space_class.closed_Un},
something does not appear right. Is the assumption \<open>U \<noteq> {}\<close> necessary?
Is it possible to simplify \<open>\<forall>x\<in>S. x \<in> U\<close>? Is it necessary to 
use such a contrived name for the denotation of the open set predicate? 
Of course, all of these 
issues can be resolved by restating the theorem in the form that we would like 
to see and using @{thm [source] closed_Un'} in the proof of this theorem, 
e.g.
\<close>
lemma closed_Un'':
  assumes "S \<subseteq> U"
    and "T \<subseteq> U"
    and "topological_space_ow U \<tau>"
    and "closed_ow U \<tau> S"
    and "closed_ow U \<tau> T"
  shows "closed_ow U \<tau> (S \<union> T)"
  using assms
  unfolding topological_space_ow_def 
  by (cases \<open>U = {}\<close>) (auto simp: assms(3) closed_Un' subset_iff)
text\<open>
However, having to restate the theorem presents a grave inconvenience.
This can be avoided by using a different format of the @{syntax tts_addendum}:
\<close>
tts_context
  tts: (?'a to \<open>U::'a set\<close>)
begin

tts_lemma closed_Un''':
  assumes "S \<subseteq> U"
    and "T \<subseteq> U"
    and "topological_space_ow U \<tau>"
    and "closed_ow U \<tau> S"
    and "closed_ow U \<tau> T"
  shows "closed_ow U \<tau> (S \<union> T)"
    given topological_space_class.closed_Un    
proof(cases \<open>U = {}\<close>)
  case False assume prems[OF False]:
    "\<lbrakk> 
      U \<noteq> {}; 
      \<forall>x\<in>S. x \<in> U;
      \<forall>x\<in>T. x \<in> U; 
      topological_space_ow U \<tau>;  
      closed_ow U \<tau> S;
      closed_ow U \<tau> T 
     \<rbrakk> \<Longrightarrow> closed_ow U \<tau> (S \<union> T)"
    for U :: "'a set" and S T \<tau>
  from prems show ?thesis using assms by blast
qed simp
  
end
text\<open>
Nevertheless, could there still be some space for improvement? 
It turns out that instead of having to state
the theorem in the desired form manually, often enough, it suffices 
to provide additional parameters for post-processing
of the raw set-based theorem, as demonstrated in the code below:
\<close>
tts_context
  tts: (?'a to \<open>U::'a set\<close>)
  rewriting ctr_simps
  eliminating \<open>?U\<noteq>{}\<close> through (auto simp: topological_space_ow_def)
  applying[of _ _ _ \<tau>]
begin

tts_lemma closed_Un'''':
  assumes "S \<subseteq> U"
    and "T \<subseteq> U"
    and "topological_space_ow U \<tau>"
    and "closed_ow U \<tau> S"
    and "closed_ow U \<tau> T"
  shows "closed_ow U \<tau> (S \<union> T)"
    is topological_space_class.closed_Un.

end

text\<open>
Finding the most suitable set of parameters for post-processing of the 
result of the relativization is an iterative process and requires practice 
before fluency can be achieved.
\<close>

text\<open>\newpage\<close>

end