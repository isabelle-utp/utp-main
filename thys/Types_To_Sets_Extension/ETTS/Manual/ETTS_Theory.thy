(* Title: ETTS/Manual/ETTS_Theory.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

section\<open>ETTS and ERA\<close>
theory ETTS_Theory
  imports ETTS_Introduction
begin



subsection\<open>Background\<close>


text\<open>
In this section, we describe our implementation of the prototype software 
framework ETTS that offers the integration of Types-To-Sets with the 
Isabelle/Isar infrastructure and full automation of the application of 
the ERA under favorable conditions. 
The design of the framework rests largely on our 
interpretation of several ideas expressed by the authors 
of \cite{kuncar_types_2019} and \cite{immler_smooth_2019}. 

It has already been mentioned that the primary functionality of the ETTS 
is available via the Isabelle/Isar 
\cite{bertot_isar_1999,wenzel_isabelleisar_2007}
commands @{command tts_context}, @{command tts_lemmas} and @{command tts_lemma}.
There also exist secondary commands aimed at resolving certain specific 
problems that one may encounter during relativization:
@{command tts_register_sbts} and @{command tts_find_sbts}.
More specifically, these commands provide means for using transfer rules 
stated in a local context during the step of the ERA that is similar 
to step 5 of the RA. The functionality of these commands is
explained in more detail in subsection \ref{sec:sbts} below.

It is important to note that the description of the ETTS presented
in this subsection is only a simplified model
of its programmatic implementation in
\textit{Isabelle/ML} \cite{milner_definition_1997,wenzel_isabelle/isar_2019}. 
\<close>



subsection\<open>Preliminaries\<close>


text\<open>
The ERA is an extension of the RA that 
provides means for the automation of a design pattern similar 
to the one that was proposed in \cite{immler_smooth_2019}, 
as well as several additional steps for pre-processing of the input 
and post-processing of the result of the relativization.
In a certain restricted sense the ERA can be seen as 
a localized form of the RA, as it provides additional infrastructure 
aimed specifically at making the relativization of theorems stated in the 
context of Isabelle's \textit{locales} 
\cite{kammuller_locales_1999, berardi_locales_2004, ballarin_locales_2014} 
more convenient.

In what follows, assume the existence of an underlying well-formed 
theory $D$ that contains all definitional axioms that appear in the 
standard library of Isabelle/HOL. 
If \mbox{$\Gamma \vdash {}_{\alpha}(\beta \approx U)_{\mathsf{Rep}}^{\mathsf{Abs}}$} 
and $\beta, U_{\alpha\ \mathsf{set}}, \mathsf{Rep}_{\beta\rightarrow\alpha}, \mathsf{Abs}_{\alpha\rightarrow\beta} \in \Gamma$, 
then the 4-tuple $(U_{\alpha\ \mathsf{set}}, \beta, \mathsf{Rep}_{\beta\rightarrow\alpha}, \mathsf{Abs}_{\alpha\rightarrow\beta})$, 
will be referred to as a \textit{relativization isomorphism} (RI) \textit{with respect to} $\Gamma$ (or RI, if $\Gamma$ can be inferred). 
Given the RI $(U_{\alpha\ \mathsf{set}},\beta,\mathsf{Rep}_{\beta\rightarrow\alpha},\mathsf{Abs}_{\alpha\rightarrow\beta})$, 
the term $U_{\alpha\ \mathsf{set}}$ will be referred to as 
the \textit{set associated with the RI}, $\beta$ will be referred to as 
the \textit{type variable associated with the RI}, 
$\mathsf{Rep}_{\beta\rightarrow\alpha}$ will be referred to as 
the \textit{representation associated with the RI} and $\mathsf{Abs}_{\alpha\rightarrow\beta}$ 
will be referred to as the \textit{abstraction associated with the RI}. 
Moreover, any typed term variable $T_{\alpha\rightarrow\beta\rightarrow\mathbb{B}}$ 
such that $\Gamma \vdash T = (\lambda x\ y.\ \mathsf{Rep}\ y = x)$ 
will be referred to as the \textit{transfer relation associated with the RI}. 
$\Gamma \vdash Domainp\ T = (\lambda x.\ x \in U)$ that holds for this transfer 
relation will be referred to as the \textit{transfer domain rule associated 
with the RI}, $\Gamma \vdash bi\_ unique\ T$ and $\Gamma \vdash right\_ total\ T$ 
will be referred to as the \textit{side conditions associated with the RI}.
For brevity, the abbreviation 
$\mathsf{dbr}[T_{\alpha\rightarrow\beta\rightarrow\mathbb{B}},U_{\alpha\ \mathsf{set}}]$ 
will be used to mean that $Domainp\ T = (\lambda x.\ x \in U)$, $bi\_ unique\ T$
and $right\_ total\ T$ for any $\alpha$, $\beta$, 
$T_{\alpha\rightarrow\beta\rightarrow\mathbb{B}}$ and $U_{\alpha\ \mathsf{set}}$.
\<close>



subsection\<open>Set-based terms and their registration\label{sec:sbts}\<close>


text\<open>
Perhaps, one of the most challenging aspects of the automation of the 
relativization process is related to the application of Transfer during 
step 5 of the RA: a suitable transfer rule for a given constant-instance 
may exist only under non-conventional side conditions:
an important example that showcases this issue is the built-in constant 
$\varepsilon$ (see \cite{kuncar_types_2019} and \cite{immler_smooth_2019}
for further information). 
Unfortunately, the ETTS does not offer a fundamental solution to this problem: 
the responsibility for providing suitable transfer rules for the application 
of the ERA remains at the discretion of the user. 
Nonetheless, the ETTS does provide
additional infrastructure that may improve the user experience when
dealing with the transfer rules that can only be conveniently stated in 
an explicitly relativized local context (usually a relativized
locale): a common problem that was already explored in 
\cite{immler_smooth_2019}.

The authors of \cite{immler_smooth_2019} choose to perform the relativization
of theorems that stem from their specifications in a locale context 
from within another dedicated relativized locale context.
The relativized operations that are represented either by the locale parameters
of the relativized locale or remain overloaded constants associated with 
a given class constraint are lifted to the type variables associated with the 
RIs that are used for the application of a variant of the relativization
algorithm. This variant includes a step during which the 
variables introduced during unoverloading are substituted (albeit implicitly) 
for the terms that represent the lifted locale parameters and constants.
The additional infrastructure and the additional step 
are needed, primarily, for the relativization of the constants 
whose transfer rules can only be stated conveniently in the context
of the relativized locale. 

A similar approach is used in the ETTS. However, instead of explicitly 
declaring the lifted constants in advance of the application of the RA, 
the user is expected to perform the registration of the so-called 
\textit{set-based term} (sbterm) for each term of interest that 
is a relativization of a given concept. 

The inputs to the algorithm that is associated with the registration of the 
sbterms are a context $\Gamma$, a term $t : \bar{\alpha}\ K$ 
($K$, applied using a postfix notation, contains all information about 
the type constructors of the type $\bar{\alpha}\ K$) and a 
sequence of $n$ distinct typed variables $\bar{U}$ with distinct types of the
form ${\alpha\ \mathsf{set}}$, such that $\bar{\alpha}$ is also of length $n$,
all free variables and free type variables that occur in 
$t : \bar{\alpha}\ K$ also appear free in $\Gamma$
and $\bar{U}_i : \bar{\alpha}_i\ \mathsf{set}$ for all $i$, 
$1 \leq i \leq n$.

Firstly, a term
$
\exists b.
\ R\left[\bar{A}\right]_{\bar{\alpha}\ K \rightarrow \bar{\beta}\ K\rightarrow \mathbb{B}}\ t\ b
$
is formed, such 
that $R\left[\bar{A}\right]$ is a parametricity relation associated with 
some type $\bar{\gamma}\ K$ for $\bar{\gamma}$ of length $n$, such that the sets 
of the elements of $\bar{\alpha}$, $\bar{\beta}$ and $\bar{\gamma}$ are pairwise 
disjoint, $\bar{A}$ and $\bar{\beta}$ are both of length $n$,
the elements of $\bar{A}$, $\bar{\beta}$ and $\bar{\gamma}$ 
are fresh for $\Gamma$ and 
$\bar{A}_i : \bar{\alpha}_i\rightarrow \bar{\beta}_i\rightarrow\mathbb{B}$ 
for all $i$ such that $1 \leq i \leq n$. Secondly, the context $\Gamma'$ is built  
incrementally starting from $\Gamma$ by adding the formulae 
$\mathsf{dbr}[\bar{A}_i, \bar{U}_i]$
for each $i$ such that $1 \leq i \leq n$.
The term presented above serves as a goal that is meant to be
discharged by the user in $\Gamma'$, resulting in the deduction
\[
\Gamma \vdash 
\mathsf{dbr}[?\bar{A}_i, \bar{U}_i] \longrightarrow
\exists b.
\ R\left[?\bar{A}\right]_{\bar{\alpha}\ K \rightarrow ?\bar{\beta}\ K\rightarrow \mathbb{B}}\ t\ b
\]
(the index $i$ is distributed over $n$)
after the export to the context $\Gamma$.
Once the proof is completed, the result is registered in the so-called
\textit{sbt-database} allowing a lookup of such results by the 
sbterm $t$ (the terms and results are allowed to morph
when the lookup is performed from within a context different 
from $\Gamma$ \cite{kauers_context_2007}).
\<close>



subsection\<open>Parameterization of the ERA\label{sec:par-ERA}\<close>


text\<open>
Assuming the existence of some context $\Gamma$, the ERA is parameterized by
the \textit{RI specification}, \textit{the sbterm specification},
the \textit{rewrite rules for the set-based theorem},
the \textit{known premises for the set-based theorem},
the \textit{specification of the elimination of premises 
in the set-based theorem} and
the \textit{attributes for the set-based theorem}.
A sequence of the entities in the list above will be
referred to as the \textit{ERA-parameterization for} $\Gamma$.

The RI Specification is a finite non-empty sequence of pairs of 
variables \mbox{$\left(?\gamma, U_{\alpha\ \mathsf{set}} \right)$}, 
such that $U_{\alpha\ \mathsf{set}} \in \Gamma$. The individual elements of 
the RI specification will be referred to as 
the \textit{RI specification elements}. 
The first element of the RI specification element will be referred to as 
the \textit{schematic type variable associated with the RI specification element}, 
the second element will be referred to as the 
\textit{set associated with the RI specification element}.

The sbterm specification is a finite sequence of 
pairs \mbox{$(t : ?\bar{\alpha}\ K,\ u : \bar{\beta}\ K)$}, 
where $t$ is either a constant-instance or a schematic typed term variable 
and $u$ is an sbterm with respect to $\Gamma$. The notation for the elements 
of the sbterm specification follows a convention similar to the one 
introduced for the RI specification elements.

The rewrite rules for the set-based theorem can be any set of 
valid rules for the Isabelle simplifier \cite{wenzel_isabelle/isar_2019-1}; 
the known premises for the set-based theorem can be any finite 
sequence of deductions in $\Gamma$; 
the specification of the elimination of premises in the set-based theorem 
is a pair $(\bar{t}, m)$, where $\bar{t}$ is a sequence of formulae and $m$ 
is a proof method; the attributes for the set-based theorem
is a sequence of attributes of Isabelle
(e.g., see \cite{wenzel_isabelle/isar_2019-1}).
\<close>



subsection\<open>Definition of the ERA\label{sec:def-ERA}\<close>


text\<open>
The relativization is performed inside a local context $\Gamma$ with an 
associated ERA-parameterization (such a context-parameterization pair will 
be called a \textit{tts context}). The ERA provides explicit support for 
handling the transfer rules local to the context through the infrastructure 
for the registration of sbterms, as explained in 
subsection \ref{sec:sbts}. Apart from this, the main part of 
the ERA largely follows the outline of the RA. However, 
the ERA also provides several tools for post-processing of the raw result 
of the relativization. The ERA also has an initialization stage, but this
stage is largely hidden from the end-user. Thus, the ERA can be divided 
in three distinct parts: 
\textit{initialization of the relativization context}, 
\textit{kernel of the ERA} (KERA) and \textit{post-processing}. 

Assume that the context $\Gamma$ contains the variable
$U_{\alpha\ \mathsf{set}}$ and the finite sequences of 
variables $\bar{g}$ and $\bar{f}$ indexed by $I$ and $J$, respectively, 
such that $\bar{g}_i : \alpha\ \bar{K}_i$ and 
$\bar{f}_j : \alpha\ \bar{L}_j$ for all $i \in I$ and $j \in J$ 
for some sequences of functions $\bar{K}$ and $\bar{L}$ also 
indexed by $I$ and $J$, respectively, representing the type constructors. 
Also, assume that the input to the relativization algorithm is 
the type-based theorem 
$\vdash\phi\left[?\alpha_{\Upsilon}, ?\bar{h}\left[?\alpha_{\Upsilon}\right]\right]$ 
such that $?\bar{h}$ is indexed by $I$ and $\Upsilon$ depends on the 
overloaded constants $\bar{*}$ indexed by $J$. Finally, assume that the 
ERA is parameterized by the RI specification 
$\left(?\alpha_{\Upsilon}, U_{\alpha\ \mathsf{set}}\right)$ 
and the sbterm specification elements 
$(?\bar{h}_i, \bar{g}_i)$ and $(\bar{*}_j, \bar{f}_j)$ 
for all $i \in I$ and $j \in J$. 

\textbf{Initialization of the relativization context}. 
Prior to the application of the relativization algorithm, the formula 
$\exists \mathsf{Rep}\ \mathsf{Abs}.\ {}_{\alpha}(\beta \approx U)_{\mathsf{Rep}}^{\mathsf{Abs}}$ 
is added to the context $\Gamma$, with the type variable $\beta$ being fresh for 
$\Gamma$, resulting in a new context $\Gamma'$ such that 
$\Gamma \subseteq \Gamma'$ and 
\mbox{$\exists \mathsf{Rep}\ \mathsf{Abs}.\ {}_{\alpha}(\beta \approx U)_{\mathsf{Rep}}^{\mathsf{Abs}} \in \Gamma'$}.
Then, the properties of the Hilbert choice $\varepsilon$ are used for the 
definition of $\mathsf{Rep}$ and $\mathsf{Abs}$ such that 
\mbox{$\Gamma' \vdash {}_{\alpha}(\beta \approx U)_{\mathsf{Rep}}^{\mathsf{Abs}}$} 
(e.g., see \cite{kuncar_types_2015}).
In this case, \mbox{$(U_{\alpha\ \mathsf{set}},\beta,\mathsf{Rep}_{\beta\rightarrow\alpha},\mathsf{Abs}_{\alpha\rightarrow\beta})$} 
is an RI with respect to $\Gamma'$. Furthermore, a fresh 
$T_{\alpha\rightarrow\beta\rightarrow\mathbb{B}}$ (for $\Gamma$) is defined as a transfer 
relation associated with the RI. Finally, the transfer domain rule associated 
with the RI and the side conditions associated with the RI are proved for $T$
with respect to $\Gamma'$. 
For each $\bar{g}_i$ such that $i \in I$, the sbt-database contains a deduction 
\mbox{$\Gamma \vdash\mathsf{dbr}[?A, U] \longrightarrow \exists a.\ R\left[?A\right]_{\alpha\ \bar{K}_i \rightarrow ?\delta\ \bar{K}_i\rightarrow \mathbb{B}}\ \bar{g}_i\ a$}. 
Thence, for each $i \in I$, $?\delta$ is instantiated as 
$\beta$ and $?A_{\alpha\rightarrow?\delta\rightarrow\mathbb{B}}$ is instantiated 
as $T_{\alpha\rightarrow\beta\rightarrow\mathbb{B}}$. The resulting theorems 
are used for the definition of a fresh (for $\Gamma$) sequence of variables $\bar{a}$ such that 
\mbox{$\Gamma' \vdash R\left[T_{\alpha\rightarrow\beta\rightarrow\mathbb{B}}\right]_{\alpha\ \bar{K}_i \rightarrow \beta\ \bar{K}_i\rightarrow \mathbb{B}}\ \bar{g}_i\ \bar{a}_i$}.
Similar deductions are also established for the sequence $\bar{f}$, with the 
sequence of the variables appearing on the right-hand side of the transfer rules 
denoted by $\bar{b}$. These deductions are meant to be used by the transfer 
infrastructure during the step of the ERA that is equivalent to step 5 of the RA,
as shown below. Thus, at the end of the initialization of the relativization context, 
the theorem is transformed into a deduction of the form 
\mbox{$\Gamma'\vdash\phi\left[?\alpha_{\Upsilon}, ?\bar{h}\left[?\alpha_{\Upsilon}\right]\right]$}, 
where the context $\Gamma'$ (called the \textit{relativization context}) 
is such that $\Gamma \subseteq \Gamma'$ 
and it has an associated relativization isomorphism 
$(U_{\alpha\ \mathsf{set}}, \beta, \mathsf{Rep}_{\beta\rightarrow\alpha}, \mathsf{Abs}_{\alpha\rightarrow\beta})$ 
for some fresh $\beta$, the associated fresh transfer relation $T$ and fresh
variables $\bar{a}$ and $\bar{b}$ indexed by $I$ and $J$
(with freshness being assessed with respect to $\Gamma$).
Also, the following transfer rules are provided for all $i \in I$ and $j \in J$: 
\mbox{$\Gamma' \vdash \bar{R}_i\left[T\right]\ \bar{g}_i\ \bar{a}_i$} and 
\mbox{$\Gamma' \vdash \bar{R'}_j\left[T\right]\ \bar{f}_j\ \bar{b}_j$} 
($\bar{R}$ and $\bar{R'}$ are sequences of parametricity relations indexed 
by $I$ and $J$, respectively).

\textbf{Kernel of ERA}. The KERA is similar to the RA: 
\[
\infer[(7)]
{
\Gamma\vdash U \neq\emptyset\longrightarrow
U\downarrow\bar{g},\bar{f}\longrightarrow
\Upsilon^{\mathsf{on}}_{\mathsf{with}}\ U\ \bar{f} \longrightarrow
\phi^{\mathsf{on}}_{\mathsf{with}}\left[\alpha,U,\bar{g},\bar{f}\right]
}
{
\infer[(6)]
{
\Gamma
\vdash \exists \mathsf{Rep}\ \mathsf{Abs}.{}_{\alpha}(\beta \approx U)_{\mathsf{Rep}}^{\mathsf{Abs}} 
\longrightarrow
U\downarrow\bar{g},\bar{f}\longrightarrow
\Upsilon^{\mathsf{on}}_{\mathsf{with}}\ U\ \bar{f}\longrightarrow
\phi^{\mathsf{on}}_{\mathsf{with}}\left[\alpha,U,\bar{g},\bar{f}\right]
}
{
\infer[(5)]
{
\Gamma'
\vdash U\downarrow\bar{g},\bar{f}\longrightarrow
\Upsilon^{\mathsf{on}}_{\mathsf{with}}\ U\ \bar{f}\longrightarrow
\phi^{\mathsf{on}}_{\mathsf{with}}\left[\alpha,U,\bar{g},\bar{f}\right]
}
{
\infer[(4)]
{
\Gamma'
\vdash\Upsilon_{\mathsf{with}}\ \bar{b}\longrightarrow
\phi_{\mathsf{with}}\left[\beta,\bar{a},\bar{b}\right]
}
{
\infer[(3)]
{
\Gamma'
\vdash\Upsilon_{\mathsf{with}}\ ?\bar{f}\left[\beta\right]\longrightarrow
\phi_{\mathsf{with}}\left[\beta,?\bar{h}\left[\beta\right],?\bar{f}\right]
}
{
\infer[(2)]
{
\Gamma'\vdash\Upsilon_{\mathsf{with}}\ ?\bar{f}\left[?\alpha\right]\longrightarrow
\phi_{\mathsf{with}}\left[?\alpha,?\bar{h}\left[?\alpha\right],?\bar{f}\right]
}
{
\infer[(1)]
{
\Gamma'\vdash\phi_{\mathsf{with}}\left[?\alpha_{\Upsilon}, ?\bar{h}\left[?\alpha_{\Upsilon}\right], \bar{*} \right]
}
{
\Gamma'\vdash\phi\left[?\alpha_{\Upsilon}, ?\bar{h}\left[?\alpha_{\Upsilon}\right]\right]
}
}
}
}
}
}
}
\]
Thus, step 1 will be referred to as the first step
of the dictionary construction (similar to step 1 of the RA); step 2 will 
be referred to as unoverloading of the type $?\alpha_{\Upsilon}$: 
it includes class internalization and the application of the 
UO (similar to step 2 of the RA); in step 3, $?\alpha$ is instantiated 
as $\beta$ using the RI specification (similar to step 4 in the RA); 
in step 4, the sbterm specification is used for the instantiation 
of $?\bar{h}$ as $\bar{a}$ and $?\bar{f}$ as $\bar{b}$; 
step 5 refers to the application of transfer, including the transfer rules 
associated with the sbterms (similar to step 5 in the RA); 
in step 6, the result is exported from $\Gamma'$ to $\Gamma$, providing the 
additional premise 
$\exists \mathsf{Rep}\ \mathsf{Abs}.\ {}_{\alpha}(\beta \approx U)_{\mathsf{Rep}}^{\mathsf{Abs}}$; 
step 7 is the application of the attribute 
@{attribute cancel_type_definition} 
(similar to step 6 in the RA).

The RI specification and the sbterm specification provide the information that 
is necessary to perform the type and term substitutions in steps 3 and 4 of 
the KERA. If the specifications are viewed as finite maps, their domains 
morph along the transformations that the theorem undergoes until step 4. 

\textbf{Post-processing}. The deduction that is obtained in the final step of 
the KERA can often be simplified further. The following post-processing steps 
were created to allow for the presentation 
of the set-based theorem in a format that is both desirable and convenient 
for the usual applications:
\begin{enumerate}
\item \textit{Simplification}. The rewriting is performed using the rewrite 
rules for the set-based theorem: the implementation relies on the 
functionality of the Isabelle's simplifier.
\item \textit{Substitution of known premises}. The known premises for the 
set-based theorem are matched with the premises of the set-based theorem, 
allowing for their elimination.
\item \textit{Elimination of premises}. Each premise is matched against each 
term in the specification of the elimination of premises in the 
set-based theorem; the associated method is applied in an attempt to eliminate 
the matching premises (this can be useful for the elimination of the 
premises of the form $U \neq \emptyset$).
\item \textit{Application of the attributes for the set-based theorem}. 
The attributes for the set-based theorem are applied as the final step 
during post-processing.
\end{enumerate}

Generally, the desired form of the result after a successful application 
of post-processing is similar to
\mbox{$\Gamma\vdash\phi^{\mathsf{on}}_{\mathsf{with}}\left[\alpha,U,\bar{g},\bar{f}\right]$}
with the premises \mbox{$U \neq \emptyset$, $U\downarrow\bar{g},\bar{f}$} and 
\mbox{$\Upsilon^{\mathsf{on}}_{\mathsf{with}}\ U\ \bar{f}$} eliminated completely 
(these premises can often be inferred from the context $\Gamma$).
\<close>

text\<open>\newpage\<close>

end