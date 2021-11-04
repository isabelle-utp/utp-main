(* Title: CTR/CTR_Reference.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Reference manual for the CTR.
*)

section\<open>CTR\<close>
theory CTR_Reference
  imports 
    CTR
    "../UD/UD_Reference"
begin



subsection\<open>Introduction\<close>


subsubsection\<open>Background\<close>

text\<open>
This section presents a reference manual for the sub-framework CTR
that can be used for the automated synthesis of 
conditional transfer rules.
The CTR evolved from the frameworks \textit{Conditional Parametricity} (CP) 
\cite{gilcher_conditional_2017} and Types-To-Sets
that are available as part of the main distribution of Isabelle.
However, it does not require either the axiom LT or the axiom UO
associated with the Types-To-Sets for its operation.
The CTR introduces the following Isabelle/Isar commands:
\[
\begin{array}{rcl}
  @{command ctr} & : &  \<open>local_theory \<rightarrow> local_theory\<close>\\
  @{command ctr_relator} & : &  \<open>local_theory \<rightarrow> local_theory\<close>\\
\end{array}
\]
\<close>


subsubsection\<open>Purpose and scope\<close>

text\<open>
The primary functionality of the CTR is available via the
command @{command ctr}. The command @{command ctr}, given a definition 
of a constant, attempts to provide a conditional transfer rule for this 
constant, possibly under arbitrary user-defined side conditions.
The process of the synthesis of a transfer rule for 
a constant may or may not involve the declaration and synthesis of a 
definition of a new (\textit{relativized}) constant.
The command provides an interface for the application of two 
plausible algorithms for the synthesis of the transfer rules
that have a restricted and overlapping scope of applicability. 
The first algorithm (\textit{CTR I}) was developed and implemented in 
\cite{gilcher_conditional_2017}. 
An outline of the second algorithm (\textit{CTR II}) 
was proposed in \cite{lammich_automatic_2013} and \cite{immler_smooth_2019}:
CTR II relies on the functionality of the 
@{method transfer_prover} 
(see subsection 4.6 in \cite{kuncar_types_2015}). 
More details about CTR II are given in the next subsection.

The command @{command ctr_relator} can be used for the 
registration of the, so-called, \textit{ctr-relators} that need to be provided 
for every non-nullary type constructor that occurs in the type of the 
constant-instance whose definition is passed as an argument to CTR II. 
However, as a fallback solution, the command @{command ctr} may 
use the \textit{relators} that are associated with the standard 
\textit{BNF} infrastructure
of Isabelle/HOL (e.g., see \cite{traytel_foundational_2012}).
The only necessary condition for the registration of the ctr-relators 
is that they must satisfy the type-constraint 
associated with the action of a BNF on relations (e.g., see 
\cite{traytel_foundational_2012} or \cite{blanchette_bindings_2019}).
\<close>


subsubsection\<open>Related and previous work\<close>

text\<open>
As already mentioned, the CTR evolved from the framework 
CP that is available as part of the main 
distribution of Isabelle. Furthermore, CTR provides an interface to the main 
functionality associated with the framework CP 
and builds upon many ideas that could be associated with it. 
The primary reason for the development of the command @{command ctr} instead 
of extending the implementation of the existing command
@{command parametric_constant} provided as part of the CP 
was the philosophy of non-intervention with the
development version of Isabelle that was adopted at the onset of the design of 
the CTR. Perhaps, in the future, the functionality of the aforementioned 
commands can be integrated.

It should also be mentioned that the Isabelle/ML code from the main 
distribution of Isabelle was frequently reused during the 
development of CTR.
\<close>



subsection\<open>Theory\<close>

text\<open>

Assume the existence of an underlying well-formed definitional theory $D$ and 
a context $\Gamma$; assume the existence of a map 
$\mathsf{ctr}_{\mathsf{Rel}}$ from a finite set of non-nullary type constructors 
to relators, mapping each non-nullary type constructor in its domain to a 
valid relator for this type constructor. The inputs to CTR II are a
constant-instance definition 
$\vdash c_{?\bar{\gamma}\ K} = \phi\left[?\bar{\gamma}\right] $ of the 
constant-instance $c_{?\bar{\gamma}\ K}$ and the map $\mathsf{trp}$ from the 
set of all schematic type variables in ?$\bar{\gamma}$ to the set 
of (fixed) binary relations 
$x_{\alpha\rightarrow\beta\rightarrow\mathbb{B}}$ in $\Gamma$ with 
non-overlapping type variables ($?\bar{\gamma}$ corresponds to a sequence 
of all distinct type variables that occur in the type 
$?\bar{\gamma}\ K$, while $K$, applied using a postfix notation, contains all 
information about the type constructors of the type $?\bar{\gamma}\ K$, 
such that the non-nullary type constructors associated with $K$ form a subset 
of the domain of $\mathsf{ctr}_{\mathsf{Rel}}$). CTR II consists of three parts: 
\textit{synthesis of a parametricity relation}, 
\textit{synthesis of a transfer rule} and \textit{post-processing}.

\textbf{Synthesis of a parametricity relation}. 
An outline of an algorithm for the conversion of a type to a 
\textit{parametricity relation} 
is given in subsection 4.1.1 in \cite{kuncar_types_2015}. 
Thus, every nullary type constructor in $?\bar{\gamma}\ K$ is replaced by the 
identity relation $=$, every non-nullary type constructor $\kappa$ 
in $?\bar{\gamma}\ K$ is replaced by its corresponding 
relator $\mathsf{ctr}_{\mathsf{Rel}}\left(\kappa\right)$ and every type 
variable $?\gamma$ in $?\bar{\gamma}\ K$ is replaced by 
$\mathsf{trp}\left(?\gamma\right)$, obtaining the parametricity 
relation $R_{\bar{\alpha}\ K \rightarrow \bar{\beta}\ K \rightarrow\mathbb{B}}$.

\textbf{Synthesis of a transfer rule}. First, the goal 
$R\ \phi\left[\bar{\alpha}\right]\ \phi\left[\bar{\beta}\right]$ is created 
in $\Gamma$ and an attempt to prove it is made using the algorithm associated 
with the method
@{method transfer_prover}. 
If the proof is successful, nothing else needs to be done in this part.
Otherwise, an attempt to find a solution for $?a$ 
in $R\ \left(?a_{\bar{\alpha}\ K}\right)\ \phi\left[\bar{\beta}\right]$ is made,
once again, using the
@{method transfer_prover}. 
The result of the successful completion of the synthesis is a transfer 
rule $\Gamma \vdash R\ \psi\left[\bar{\alpha},\bar{x}\right]\ \phi\left[\bar{\beta}\right]$, 
where $\bar{x}$ is used to denote a sequence of typed variables, each of 
which occurs free in the context $\Gamma$ (the success of this part 
is not guaranteed). 

\textbf{Post-processing}. 
If $\psi\left[\bar{\alpha},\bar{x}\right] = \phi\left[\bar{\alpha}\right]$ 
after the successful completion of part 2 of the algorithm, then the 
definitions of the constant-instances $c_{\bar{\alpha}\ K}$
and $c_{\bar{\beta}\ K}$ are folded, resulting in the 
deduction \mbox{$\Gamma \vdash R\ c_{\bar{\alpha}\ K}\ c_{\bar{\beta}\ K}$}. 
Otherwise, 
if \mbox{$\psi\left[\bar{\alpha},\bar{x}\right]\ \neq \phi\left[\bar{\alpha}\right]$}, 
then a new constant $d$ is declared such 
that \mbox{$\vdash d_{\sigma\left[?\bar{\alpha}\right]} = \left(\lambda \bar{x}.\ \psi\left[?\bar{\alpha},\bar{x}\right]\right)$}, 
where $\sigma$ is determined uniquely by $\bar{x}$ and $?\bar{\alpha}\ K$. 
In this case, \mbox{$\Gamma \vdash R\ \psi\left[\bar{\alpha},\bar{x}\right]\ \phi\left[\bar{\beta}\right]$} 
can be restated as \mbox{$\Gamma \vdash R\ \left(d_{\sigma\left[\bar{\alpha}\right]}\ \bar{x}\right)\ c_{\bar{\beta}\ K}$}. 
This result can be exported to the global theory context and forms a conditional 
transfer rule for $c_{?\bar{\gamma}\ K}$.

CTR II can perform the synthesis of the transfer rules for constants under 
arbitrary user-defined side conditions automatically. However, the algorithm 
guarantees neither that it can identify whether a transfer rule exists for 
a given constant under a given set of side conditions, 
nor that it will be found if it does exist. 
\<close>



subsection\<open>Syntax\<close>


subsubsection\<open>Background\<close>

text\<open>
This subsection presents the syntactic categories that are associated with the 
command @{command ctr} and closely related auxiliary commands and attributes. 
It is important to note that the presentation is only approximate.
\<close>


subsubsection\<open>\<open>ctr_relator\<close>\<close>

text\<open>
\begin{matharray}{rcl}
  @{command_def ctr_relator} & : &  \<open>local_theory \<rightarrow> local_theory\<close>
\end{matharray}

  \<^medskip>

  \<^rail>\<open>@@{command ctr_relator} term\<close>

  \<^descr> \<^theory_text>\<open>ctr_relator\<close> \<open>c\<close> saves the ctr-relator \<open>c\<close> to a database of 
ctr-relators for future reference. A ctr-relator is defined as any constant 
that has the type of the form
\begin{center} 
\<open>(\<alpha>\<^sub>1\<Rightarrow>\<beta>\<^sub>1\<Rightarrow>\<bool>)\<Rightarrow>\<dots>\<Rightarrow>(\<alpha>\<^sub>n\<Rightarrow>\<beta>\<^sub>n\<Rightarrow>\<bool>)\<Rightarrow>(\<alpha>\<^sub>1\<dots>\<alpha>\<^sub>n)\<kappa>\<Rightarrow>(\<beta>\<^sub>1\<dots>\<beta>\<^sub>n)\<kappa>\<Rightarrow>\<bool>\<close>,
\end{center}
where \<open>\<alpha>\<^sub>1\<dots>\<alpha>\<^sub>n\<close> and \<open>\<beta>\<^sub>1\<dots>\<beta>\<^sub>n\<close> are distinct type variables,
\<open>n\<close> is a positive integer and \<open>\<kappa>\<close> is a type constructor.
\<close>


subsubsection\<open>\<open>ctr\<close>\<close>

(*
Certain elements of the content presented below were copied from the theory 
Doc/Isar_Rel/Spec.thy in the main library of Isabelle. 
*)
text\<open>
\begin{matharray}{rcl}
  @{command_def ctr} & : &  \<open>local_theory \<rightarrow> local_theory\<close> \\
\end{matharray}

  \<^medskip>

  \<^rail>\<open>
    @@{command ctr} (@'parametricity' | @'relativization' rlt) in_def
    ;
    rlt: 
      (synthesis*) 
      (cce*)
      trp
    ;
    synthesis: @'synthesis' (thm*)
    ;
    cce:
      @'fixes' vars |
      @'assumes' (props + @'and')
    ;
    trp: (@'trp' ('(' type_var term ')' + @'and'))?
    ;
    in_def: ((binding @':')? thm mixfix?) + and
  \<close>

  \<^descr> \<^theory_text>\<open>ctr\<close> provides access to two algorithms for the automated synthesis of 
the transfer rules and the relativization of constants based on their 
definitions. 

    \<^descr> \<^theory_text>\<open>parametricity\<close> indicates that CTR I needs
to be invoked by the command.

    \<^descr> \<^theory_text>\<open>relativization\<close> indicates that CTR II needs to be 
invoked by the command. 

    \<^descr> \<^theory_text>\<open>synthesis\<close> \<open>thm\<close> indicates that the relativization of the 
inputs needs to be performed and post-processed using the simplifier with 
the collection of rewrite rules stated as the fact \<open>thm\<close>. If the optional 
argument \<open>thm\<close> is not provided, then the default \<open>simpset\<close> is used for 
post-processing. If the keyword \<^theory_text>\<open>synthesis\<close> is omitted, 
then no attempt to perform the relativization is made. 
The keyword \<^theory_text>\<open>synthesis\<close> is relevant only for CTR II.

    \<^descr> \<^theory_text>\<open>trp\<close> \<open>(?a\<^sub>1 A\<^sub>1)\<close> \<^theory_text>\<open>and\<close> \<open>\<dots>\<close> \<^theory_text>\<open>and\<close> \<open>(?a\<^sub>n A\<^sub>n)\<close> indicates 
that the type variable that has the indexname \<open>?a\<^sub>i\<close> (\<open>1\<le>i\<le>n\<close>, 
\<open>n\<close> is a non-negative integer) is meant to 
correspond to the binary relation \<open>A\<^sub>i\<close> in the parametricity relation constructed by 
the command prior to the statement of the transfer rule (for further 
information see subsection 4.1 in \cite{kuncar_types_2015}). This is relevant only
for CTR II.

    \<^descr> \<^theory_text>\<open>in\<close> \<open>(b:) def_thm (mixfix)\<close> is used for
the specification of the input to the algorithms that are associated with 
the command @{command ctr}. \<open>def_thm\<close> is meant to be a fact that 
consists of exactly one theorem of the form
\<open>A ?a\<^sub>1\<dots>?a\<^sub>n \<simeq> f ?a\<^sub>1\<dots>?a\<^sub>n\<close>,
where \<open>A\<close> is a constant, \<open>\<simeq>\<close> is either meta- or object-equality, 
\<open>n\<close> is a non-negative integer,
\<open>?a\<^sub>1\<dots>?a\<^sub>n\<close> are schematic variables and \<open>f\<close> is a suitable formula in \<open>n\<close> 
arguments (however, there are further implicit restrictions). 
If a new constant is introduced by the command, then the optional argument
\<open>mixfix\<close> is used for the specification 
of the concrete inner syntax for the constant in the usual manner
(e.g. see \cite{wenzel_isabelle/isar_2019-1}). The optional binding \<open>b\<close> is
used for the specification of the names of the entities that
are provided after the successful execution of the command. It is hoped
that the algorithm chosen for the specification of the names 
is sufficiently intuitive and does not require further explanation.
If either \<open>b\<close> or \<open>mixfix\<close> are not specified by the user, then the command
introduces sensible defaults.
Multiple theorems may be provided after the
keyword \<^theory_text>\<open>in\<close>, employing the keyword \<^theory_text>\<open>and\<close> as a separator.
In this case, the parameterized algorithm associated with the command is
applied repeatedly to each input theorem in the order of their specification
from left to right and the local context is augmented incrementally. 
\<close>



subsection\<open>Examples\label{sec:ctr_ex}\<close>

text\<open>
In this subsection, some of the capabilities of the CTR are 
demonstrated by example. The examples that are presented in this subsection are 
expected to be sufficient to begin an independent exploration of the framework, 
but do not cover the entire spectrum of the functionality and the problems that 
one may encounter while using it.

The examples that are presented in this subsection continue the example 
of the application of the command @{command ud}
to the definition of the constant @{const mono} that was presented in 
subsection \ref{sec:ud_ex}.
\<close>


subsubsection\<open>CTR I\<close>

text\<open>
As already explained, the command @{command ctr} can be used to invoke
the algorithm associated with the command @{command parametric_constant}
for the synthesis of a transfer rule for a given constant. For
example, the invocation of
\<close> 
ctr parametricity
  in mono: mono.with_def
text\<open>
generates the transfer rule @{thm [source] mono_transfer}: 
\begin{center}
@{thm [display, mode=IfThenNoBox] mono_transfer[no_vars]}
\end{center}
A detailed explanation of the underlying algorithm can be found in 
\cite{gilcher_conditional_2017}.
\<close>


subsubsection\<open>CTR II\<close>

text\<open>
The first example in this subsection demonstrates how CTR II can be 
used to produce a parametricity property identical 
to the one produced by CTR I above:
\<close>

ctr relativization
  fixes A1 :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and A2 :: "'c \<Rightarrow> 'd \<Rightarrow> bool"
  assumes [transfer_rule]: "bi_total A1" 
  trp (?'a A1) and (?'b A2)
  in mono': mono.with_def

text\<open>
This produces the theorem @{thm [source] mono'.transfer}:
@{thm [display, mode=IfThenNoBox] mono'.transfer[no_vars]}
which is identical to the theorem @{thm [source] mono_transfer} generated
by CTR I.
\<close>

text\<open>
Of course, there is very little value in trying to establish a parametricity
property using CTR II due to the availability of CTR I. However,
it is often the case that the constant is not parametric under a given
set of side conditions. Nonetheless, in this case, it is often possible to
define a new \textit{relativized constant} that is related to the original 
constant under the parametricity relation associated with the original constant. 
It is expected that the most common application of CTR II will be the
synthesis of the relativized constants.

For example, suppose one desires to find a conditional transfer rule for
the constant @{const mono.with} such that (using the conventions from the 
previous example) the relation \<open>A1\<close> is right total, but not, necessarily, 
left total. While, under such restriction on the involved relations, the 
constant @{const mono.with} is no longer conditionally parametric, its 
relativization exists and can be found using the transfer prover. To automate 
the relativization process, the user merely needs to add the keyword 
\<^theory_text>\<open>synthesis\<close> immediately after the keyword \<^theory_text>\<open>relativization\<close>:
\<close>

ctr relativization
  synthesis ctr_simps
  fixes A1 :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and A2 :: "'c \<Rightarrow> 'd \<Rightarrow> bool"
  assumes [transfer_domain_rule]: "Domainp A1 = (\<lambda>x. x \<in> U1)"
    and [transfer_rule]: "right_total A1" 
  trp (?'a A1) and (?'b A2)
  in mono_ow: mono.with_def

text\<open>
This produces the definition @{thm [source] mono_ow_def}:
@{thm [display, mode=IfThenNoBox] mono_ow_def[no_vars]}
and the theorem @{thm [source] mono_ow.transfer}:
@{thm [display, mode=IfThenNoBox] mono_ow.transfer[no_vars]}

It should be noted that, given that the keyword \<^theory_text>\<open>synthesis\<close> was
followed by the name of the named collection of theorems 
@{thm [source] ctr_simps}, this collection was used in post-processing of
the result of the relativization. The users can omit simplification
entirely by specifying the collection @{thm [source] ctr_blank} instead
of @{thm [source] ctr_simps}.
\<close>

text\<open>\newpage\<close>

end