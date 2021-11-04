(* Title: ETTS/Manual/ETTS_Syntax.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

section\<open>Syntax\<close>
theory ETTS_Syntax
  imports ETTS_Theory
begin



subsection\<open>Background\<close>


text \<open>
This section presents the syntactic categories that are associated with the 
commands @{command tts_context}, @{command tts_lemmas}, @{command tts_lemma}, 
and several other closely related auxiliary commands. 
It is important to note that the presentation of the syntax is approximate.
\<close>



subsection\<open>Registration of the set-based terms\<close>

text\<open>
\begin{matharray}{rcl}
  @{command_def "tts_register_sbts"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close> \\
  @{command_def "tts_find_sbts"} & : & \<open>context \<rightarrow>\<close>
\end{matharray}

  \<^medskip>

  \<^rail>\<open>
    @@{command tts_register_sbts} term @'|' (term + @'and')
    ;
    @@{command tts_find_sbts} (term + @'and')
  \<close>

  \<^descr> \<^theory_text>\<open>tts_register_sbts\<close> \<open>t\<close> \<open>|\<close> \<open>U\<^sub>1\<close> \<^theory_text>\<open>and\<close> \<open>\<dots>\<close> \<^theory_text>\<open>and\<close> \<open>U\<^sub>n\<close> allows for the
registration of the set-based terms in the sbt-database.
Generally, \<open>U\<^sub>i\<close> (\<open>1\<le>i\<le>n\<close>) must be distinct fixed variables with distinct types
of the form \<^typ>\<open>'a set\<close>, with the set of the type variables that occur in the
types of \<open>U\<^sub>i\<close> equivalent to the set of the type variables that occur in 
the type of \<open>t\<close>.

  \<^descr> \<^theory_text>\<open>tts_find_sbts\<close> \<open>t\<^sub>1\<close> \<^theory_text>\<open>and\<close> \<open>\<dots>\<close> \<^theory_text>\<open>and\<close> \<open>t\<^sub>n\<close> prints the
templates for the transfer rules for the set-based terms \<open>t\<^sub>1\<dots>t\<^sub>n\<close>
for some positive integer \<open>n\<close>. If no arguments are provided, then
the templates for all sbterms in the sbt-database are printed.  
\<close>



subsection\<open>Relativization of theorems\<close>


text\<open>
\begin{matharray}{rcl}
  @{command_def "tts_context"} & : & \<open>theory \<rightarrow> local_theory\<close> \\
  @{command_def "tts_lemmas"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
  @{command_def "tts_lemma"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close> \\
  @{command_def "tts_theorem"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close> \\
  @{command_def "tts_corollary"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close> \\
  @{command_def "tts_proposition"} & : & \<open>local_theory \<rightarrow> proof(prove)\<close> \\
\end{matharray}

The relativization of theorems should always be performed inside an
appropriately parameterized tts context. The tts context can be set up
using the command @{command tts_context}. The framework introduces two
types of interfaces for the application of the extended relativization
algorithm: @{command tts_lemmas} and the family of the commands with
the identical functionality: @{command tts_lemma}, @{command tts_theorem},
@{command tts_corollary}, @{command tts_proposition}. Nonetheless,
the primary purpose of the command @{command tts_lemmas} is the
experimentation and the automated generation of the relativized results stated
using the command @{command tts_lemma}. 

  \<^medskip>

  \<^rail>\<open>
    @@{command tts_context} param @'begin'
    ;
    @@{command tts_lemmas} ((@'!' | @'?')?) tts_facts
    ;
    (
      @@{command tts_lemma} |
      @@{command tts_theorem} |
      @@{command tts_corollary} |
      @@{command tts_proposition}
    )
    (tts_short_statement | tts_long_statement)
    ;
    param: (sets var rewriting subst eliminating app)
    ;
    sets: (@'tts' @':' ('(' type_var @'to' term ')' + @'and'))
    ;
    var: (@'sbterms' @':' vars)?
    ;
    vars: ('(' term @'to' term ')' + @'and')
    ;
    rewriting: (@'rewriting' thm)?
    ;
    subst: (@'substituting' (thm + @'and'))?
    ;
    eliminating: (@'eliminating' elpat? @'through' method)?
    ;
    elpat: (term + @'and')
    ;
    app: (@'applying' attributes)?
    ;
    tts_short_statement: short_statement tts_addendum
    ;
    tts_long_statement: thmdecl? context tts_conclusion
    ;
    tts_conclusion: 
      (
        @'shows' (props tts_addendum + @'and') | 
        @'obtains' obtain_clauses tts_addendum
      )
    ;
    tts_addendum: (@'given' thm | @'is' thm)
    ;
    tts_facts: @'in' (thmdef? thms + @'and')
    ;

  \<close>

  \<^descr> \<^theory_text>\<open>tts_context param begin\<close> provides means for the specification of a
new (unnamed) tts context.
    \<^descr> \<^theory_text>\<open>tts\<close>~\<open>:\<close>~\<open>(?a\<^sub>1\<close> \<^theory_text>\<open>to\<close> \<open>U\<^sub>1)\<close> \<^theory_text>\<open>and\<close> \<open>\<dots>\<close> \<^theory_text>\<open>and\<close> 
\<open>(?a\<^sub>n\<close> \<^theory_text>\<open>to\<close> \<open>U\<^sub>n)\<close> provides means for the declaration of the RI specification. 
For each \<open>i\<close> (\<open>1\<le>i\<le>n\<close>, \<open>n\<close> — positive integer), \<open>?a\<^sub>i\<close> must be a schematic type variable that
occurs in each theorem provided as an input to the commands
@{command tts_lemmas} and @{command tts_lemma} invoked inside the tts context
and \<open>U\<^sub>i\<close> can be any term of the type \<^typ>\<open>'a set\<close>, where \<^typ>\<open>'a\<close> 
is a fixed type variable.
    \<^descr> \<^theory_text>\<open>sbterms\<close>~\<open>:\<close>~\<open>(tbcv\<^sub>1\<close> \<^theory_text>\<open>to\<close> \<open>sbt\<^sub>1)\<close> \<^theory_text>\<open>and\<close> \<open>\<dots>\<close> \<^theory_text>\<open>and\<close>
\<open>(tbcv\<^sub>n\<close> \<^theory_text>\<open>to\<close> \<open>sbt\<^sub>n)\<close> can be used for the declaration of the 
sbterm specification.
For each individual entry \<open>i\<close>, such that \<open>1\<le>i\<le>n\<close> with \<open>n\<close> being a non-negative 
integer, \<open>tbcv\<^sub>i\<close> has to be either an overloaded operation that occurs in every
theorem that is provided as an input to the extended relativization algorithm 
or a schematic variable that occurs in every theorem that is provided as an 
input to the command, and \<open>sbt\<^sub>i\<close> has to be a term registered in the 
sbt-database.
    \<^descr> \<^theory_text>\<open>rewriting\<close> \<open>thm\<close> provides means for the declaration
of the rewrite rules for the set-based theorem.
    \<^descr> \<^theory_text>\<open>substituting\<close> \<open>thm\<^sub>1\<close> \<^theory_text>\<open>and\<close> \<open>\<dots>\<close> \<^theory_text>\<open>and\<close> \<open>thm\<^sub>n\<close> 
(\<open>n\<close> — non-negative integer) provides means for the declaration of the 
known premises for the set-based theorem.
    \<^descr> \<^theory_text>\<open>eliminating\<close> \<open>term\<^sub>1\<close> \<^theory_text>\<open>and\<close> \<open>\<dots>\<close> \<^theory_text>\<open>and\<close> \<open>term\<^sub>n\<close> 
\<^theory_text>\<open>through\<close> \<open>method\<close> (\<open>n\<close> — non-negative integer) provides means for the 
declaration of the specification of the elimination of premises in the 
set-based theorem.
    \<^descr> \<^theory_text>\<open>applying\<close> \<open>[attr\<^sub>1, \<dots>, attr\<^sub>n]\<close> (\<open>n\<close> — non-negative integer) 
provides means for the declaration of the attributes for the set-based theorem.

  \<^descr> \<^theory_text>\<open>tts_lemmas\<close> applies the ERA to a list 
of facts and saves the resulting set-based facts in the context. 
The command @{command tts_lemmas} should always be invoked from within a 
tts context. If the statement of the command is followed immediately by the
optional keyword \<^theory_text>\<open>!\<close>, then it operates in the verbose mode, 
printing the output of the application of the individual steps of the 
ERA. If the statement of the command 
is followed immediately by the optional keyword \<^theory_text>\<open>?\<close>, then 
the command operates in the active mode, outputting the set-based facts
in the form of the ``active areas'' that can be embedded in the Isabelle 
theory file inside the tts context from which the command @{command tts_lemmas}
was invoked. There is a further minor difference between the active mode
and the other two modes of operation that is elaborated upon within the 
description of the keyword \<^theory_text>\<open>in\<close> below. 

    \<^descr> \<^theory_text>\<open>in\<close> \<open>sbf\<^sub>1 = tbf\<^sub>1\<close> \<^theory_text>\<open>and\<close> \<open>\<dots>\<close> \<^theory_text>\<open>and\<close> \<open>sbf\<^sub>n = tbf\<^sub>n\<close> is used for
the specification of the type-based theorems and the output of the command.
For each individual entry \<open>i\<close>, such that \<open>1\<le>i\<le>n\<close> with \<open>n\<close> being a 
positive integer, \<open>tbf\<^sub>i\<close> is used for
the specification of the input of the extended relativization algorithm and
\<open>sbf\<^sub>i\<close> is used for the specification of the name binding for the output of
the extended relativization algorithm.
The specification of the output is optional: if \<open>sbf\<^sub>i\<close> is omitted, then a 
default specification of the output is inferred automatically. \<open>tbf\<^sub>i\<close> must 
be a schematic fact available in the context, whereas \<open>sbf\<^sub>i\<close> can be any
fresh name binding. Optionally, it is possible to provide attributes for 
each individual input and output, e.g., \<open>sbf\<^sub>i[sbf_attrb] = tbf\<^sub>i[tbf_attrb]\<close>. 
In this case, the list of the attributes \<open>tbf_attrb\<close> is applied to \<open>tbf\<^sub>i\<close> 
during the first part (initialization of the relativization context) 
of the ERA. If the command operates in the active
mode, then the attributes \<open>sbf_attrb\<close> are included in the active area output,
but not added to the list of the set-based attributes.
For other modes of operation, the attributes \<open>sbf_attrb\<close> are added to the list 
of the set-based attributes and applied during the third part (post-processing) 
of the ERA. 

  \<^descr> \<^theory_text>\<open>tts_lemma\<close>~\<open>a: \<phi>\<close> @{syntax "tts_addendum"}, enters proof mode with 
the main goal formed by an application of a tactic that depends on the 
settings specified in @{syntax "tts_addendum"} to \<open>\<phi>\<close>. Eventually, this results 
in some fact \<open>\<turnstile>\<phi>\<close> to be put back into the target context. The command
should always be invoked from within a tts context. 

    \<^descr> A @{syntax tts_long_statement} is similar to the standard  
@{syntax long_statement} in that it allows to build up an initial proof 
context for the subsequent claim incrementally. Similarly, 
@{syntax tts_short_statement} can be viewed as a natural extension of the 
standard @{syntax short_statement}.  

    \<^descr> @{syntax "tts_addendum"} is used for the specification of the 
pre-processing strategy of the goal \<open>\<phi>\<close>. \mbox{\<open>\<phi>\<close> \<^theory_text>\<open>is\<close> \<open>thm\<close>} applies the 
extended relativization algorithm to \<open>thm\<close>. If the term that is associated 
with the resulting set-based theorem is \<open>\<alpha>\<close>-equivalent to the term associated 
with the goal \<open>\<phi>\<close>, then a specialized tactic solves the main goal, leaving
only a trivial goal in its place (the trivial goal can be solved using the
terminal proof \mbox{step \textbf{.}}). \mbox{\<open>\<phi>\<close> \<^theory_text>\<open>given\<close> \<open>thm\<close>} also applies the 
extended relativization algorithm to \<open>thm\<close>, but the resulting set-based theorem
is merely added as a premise to the goal \<open>\<phi>\<close>. 
\<close>

text\<open>\newpage\<close>

end