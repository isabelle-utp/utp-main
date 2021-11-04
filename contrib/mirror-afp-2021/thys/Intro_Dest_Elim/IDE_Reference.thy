(* Copyright 2021 (C) Mihails Milehins *)

theory IDE_Reference
  imports
    IHOL_IDE
    Reference_Prerequisites
begin




section\<open>Introduction\<close>



subsection\<open>Background\<close>

text\<open>
This document presents a reference manual for the framework 
IDE. The framework IDE can be used for the automated synthesis of
the introduction, destruction and elimination rules from the definitions
of predicates stated in the object logic Isabelle/HOL 
of the proof assistant Isabelle.

The primary functionality of the framework is available via the 
\textit{Isabelle/Isar} \cite{bertot_isar_1999, wenzel_isabelleisar_2007} 
command @{command mk_ide}.
Given a definition of a predicate in Isabelle/HOL, the
command can synthesize introduction, destruction and elimination rules
for this definition. The rules are stated
in a certain predetermined format that is meant to be both natural and
convenient for the end user and the tools for classical reasoning
available in Isabelle/HOL.
\<close>



subsection\<open>Related and previous work\<close>

text\<open>
The standard distribution of Isabelle provides the \textit{attribute} 
@{attribute elim_format} \cite{wenzel_isabelle/isar_2019-1} 
that can be used for the conversion of the
destruction rules to the elimination rules. The primary functionality of this
attribute is reused in the implementation of the command @{command mk_ide}.

Furthermore, Isabelle offers several definitional packages 
that provide similar rules automatically for the constants created
by these definitional packages \cite{wenzel_isabelle/isar_2019-1}. 
However, to the best knowledge of the author,
none of these packages can generate such rules for arbitrary predicates.
Perhaps, in the future, the approaches can be unified or integrated in
some manner. 
\<close>

text\<open>\newpage\<close>



section\<open>Syntax\<close>

text\<open>
This subsection presents the syntactic categories that are associated with the 
command @{command mk_ide}. It is important to note that the presentation is 
only approximate.
\<close>

text\<open>

\begin{matharray}{rcl}
  @{command_def "mk_ide"} & : & \<open>local_theory \<rightarrow> local_theory\<close>
\end{matharray}

  \<^medskip>

  \<^rail>\<open>
    @@{command mk_ide} @{element "rf"}? thm ((intro | elim | dest)*)
    ;
    intro: @@{element "|intro"} (thmdef @'|')
    ;
    dest: @@{element "|dest"} (thmdef @'|')
    ;
    elim: @@{element "|elim"} (thmdef @'|')
  \<close>

  \<^descr> \<^theory_text>\<open>mk_ide\<close> (\<^theory_text>\<open>rf\<close>) \<open>def_thm\<close> \<^theory_text>\<open>|intro\<close> 
\<open>name[attrbs]\<close>\<^theory_text>\<open>|\<close> converts the
definition \<open>def_thm\<close> into an introduction rule, followed by the application of 
the functionality associated with the optional keyword \<^theory_text>\<open>rf\<close> and
the attributes \<open>attrbs\<close> to this rule. 
The result of the application of the attributes \<open>attrbs\<close> 
is stored in the local context under the name \<open>name\<close>. \<open>def_thm\<close> is meant to be 
a fact that consists of exactly one theorem of the form
\begin{center}
\<open>A a\<^sub>1 \<dots> a\<^sub>n \<simeq> f\<^sub>1 a\<^sub>1 \<dots> a\<^sub>n \<and> \<dots> \<and> f\<^sub>m a\<^sub>1 \<dots> a\<^sub>n\<close>,
\end{center}
where \<open>n\<close> and \<open>m\<close> are natural numbers,
\<open>A\<close> is a constant predicate in \<open>n\<close> arguments, \<open>\<simeq>\<close> is either the meta-logic 
equality or the object logic equality,
\<open>a\<^sub>1 \<dots> a\<^sub>n\<close> are schematic variables and \<open>f\<^sub>1 \<dots> f\<^sub>m\<close> are suitable predicates in \<open>n\<close>
arguments (however, there are further implicit restrictions). The resulting
introduction rule is expected to be stated in the format 
\begin{center}
\<open>f\<^sub>1 a\<^sub>1 \<dots> a\<^sub>n \<Longrightarrow> \<dots> \<Longrightarrow> f\<^sub>m a\<^sub>1 \<dots> a\<^sub>n \<Longrightarrow> A a\<^sub>1 \<dots> a\<^sub>n\<close>
\end{center}
prior to the application of the functionality associated with the keyword 
\<^theory_text>\<open>rf\<close> and the attributes \<open>attrbs\<close>. If the optional keyword
\<^theory_text>\<open>rf\<close> is passed as an argument to the command, 
then the output of the command 
(prior to the application of the attributes) is formatted using an algorithm
associated with the attribute @{attribute rule_format} 
\cite{wenzel_isabelle/isar_2019-1}. 
  \<^descr> \<^theory_text>\<open>mk_ide\<close> (\<^theory_text>\<open>rf\<close>) \<open>def_thm\<close> \<^theory_text>\<open>|dest\<close>
\<open>name[attrbs]\<close>\<^theory_text>\<open>|\<close> converts the definition
\<open>def_thm\<close> into one or more destruction rules, followed by the application of the
functionality associated with the optional keyword \<^theory_text>\<open>rf\<close> and the 
attributes \<open>attrbs\<close> to each destruction rule. 
Given the theorem \<open>def_thm\<close> in the format described above, 
the command provides \<open>m\<close> destruction rules of the form
\begin{center}
\<open>A a\<^sub>1 \<dots> a\<^sub>n \<Longrightarrow> f\<^sub>i a\<^sub>1 \<dots> a\<^sub>n\<close>
\end{center}
for each \<open>1\<le>i\<le>m\<close> prior to the application of the functionality associated with
the keyword \<^theory_text>\<open>rf\<close> and the attributes \<open>attrbs\<close>.
  \<^descr> \<^theory_text>\<open>mk_ide\<close> (\<^theory_text>\<open>rf\<close>) \<open>def_thm\<close> \<^theory_text>\<open>|elim\<close>  
\<open>name[attrbs]\<close>\<^theory_text>\<open>|\<close> converts the definition
\<open>def_thm\<close> into an elimination rule, followed by the application of the
functionality associated with the optional keyword \<^theory_text>\<open>rf\<close> and the 
attributes \<open>attrbs\<close> to each destruction rule. 
Given the theorem \<open>def_thm\<close> in the format
described above, the elimination rule has the format
\begin{center}
\<open>A a\<^sub>1 \<dots> a\<^sub>n \<Longrightarrow> (f\<^sub>1 a\<^sub>1 \<dots> a\<^sub>n \<Longrightarrow> \<dots> \<Longrightarrow> f\<^sub>m a\<^sub>1 \<dots> a\<^sub>n \<Longrightarrow> P) \<Longrightarrow> P\<close>
\end{center}
prior to the application of the functionality associated with
the keyword \<^theory_text>\<open>rf\<close> and the attributes \<open>attrbs\<close>.

It is possible to combine the keywords \<^theory_text>\<open>|intro\<close>, \<^theory_text>\<open>|dest\<close> and \<^theory_text>\<open>|elim\<close> in a 
single invocation of the command.
\<close>

text\<open>\newpage\<close>



section\<open>Examples\<close>

text\<open>
In this section, some of the capabilities of the framework IDE are demonstrated
by example. The example is based on the definition of the constant
\<^const>\<open>monoid\<close> from the standard library of 
Isabelle/HOL \cite{noauthor_isabellehol_2020} and given by 
\begin{center}
@{thm monoid_def[unfolded monoid_axioms_def, no_vars]}
\end{center}
\<close>
mk_ide rf monoid_def[unfolded monoid_axioms_def] 
  |intro monoidI|
  |dest monoidD|
  |elim monoidE|
  
text\<open>
The invocation of the command @{command mk_ide} provides the theorem
@{thm [source] monoidI} given by 
\begin{center}
@{thm monoidI[no_vars]},
\end{center}
the fact @{thm [source] monoidD} given by
\begin{center}
@{thm monoidD[no_vars]}
\end{center}
and the theorem
@{thm [source] monoidE} given by
\begin{center}
@{thm monoidE[no_vars]}.
\end{center}
\<close>
     
end