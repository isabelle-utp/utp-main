(* Title: ETTS/Manual/ETTS_Introduction.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

chapter\<open>ETTS: Reference Manual\<close>

section\<open>Introduction\<close>
theory ETTS_Introduction
  imports 
    Manual_Prerequisites  
    "HOL-Library.Conditional_Parametricity"
begin



subsection\<open>Background\<close>


text\<open>
The \textit{standard library} that is associated with the 
object logic Isabelle/HOL and provided as a part of 
the standard distribution of Isabelle \cite{noauthor_isabellehol_2020} 
contains a significant number of formalized results from a 
variety of fields of mathematics (e.g., order theory, algebra, topology). 
Nevertheless, using the argot that was promoted in the 
original publication of Types-To-Sets \cite{blanchette_types_2016}, 
the formalization is performed using a type-based approach. 
Thus, for example, the carrier sets associated with the algebraic structures 
and the underlying sets of the topological spaces, effectively, 
consist of all terms of an arbitrary type. This restriction can create 
an inconvenience when working with mathematical objects induced on a 
subset of the carrier set/underlying set associated with the original 
object (e.g., see \cite{immler_smooth_2019}).

To address this limitation, several additional libraries were developed 
upon the foundations of the standard library 
(e.g., \textit{HOL-Algebra} \cite{ballarin_isabellehol_2020} and 
\textit{HOL-Analysis} \cite{noauthor_isabellehol_2020-1}). 
In terms of the argot associated with Types-To-Sets, these libraries provide 
the set-based counterparts of many type-based theorems in the standard library,
along with a plethora of additional results. Nonetheless, the proofs of 
the majority of the theorems that are available in the standard library 
are restated explicitly in the libraries that contain the set-based results.
This unnecessary duplication of efforts is one of the primary problems 
that the framework Types-To-Sets is meant to address. 

The framework Types-To-Sets offers a unified approach to structuring 
mathematical knowledge formalized in Isabelle/HOL: potentially, 
every type-based theorem can be converted to a set-based theorem in 
a semi-automated manner and the relationship between such type-based 
and set-based theorems can be articulated clearly and explicitly 
\cite{blanchette_types_2016}. 
In this document, we describe a particular implementation of the framework 
Types-To-Sets in Isabelle/HOL that takes the form of a further extension 
of the language Isabelle/Isar with several new commands and attributes 
(e.g., see \cite{wenzel_isabelle/isar_2019-1}).
\<close>



subsection\<open>Prerequisites and conventions\<close>


text\<open>
A reader of this document is assumed to be familiar with 
the proof assistant Isabelle, the proof language Isabelle/Isar,
the meta-logic Isabelle/Pure and
the object logic Isabelle/HOL, as described in, 
\cite{paulson_natural_1986, wenzel_isabelle/isar_2019-1},
\cite{bertot_isar_1999, wenzel_isabelleisar_2007, wenzel_isabelle/isar_2019-1},
\cite{paulson_foundation_1989, wenzel_isabelle/isar_2019-1} and
\cite{yang_comprehending_2017}, respectively. Familiarity with the
content of the original articles about Types-To-Sets
\cite{blanchette_types_2016,kuncar_types_2019} and
the first large-scale application of Types-To-Sets
(as described in \cite{immler_smooth_2019}) 
is not essential but can be useful.

The notational conventions that are used in this document are
approximately equivalent to the conventions that were suggested in
\cite{blanchette_types_2016}, \cite{yang_comprehending_2017} and
\cite{kuncar_types_2019}. 
However, a disparity comes from our use of explicit notation 
for the \textit{schematic variables}. In Isabelle/HOL, free variables 
that occur in the theorems at the top-level in the theory context 
are generalized implicitly, which may be expressed by replacing 
fixed variables by schematic variables \cite{wenzel_isabelle/isar_2001}. 
In this article, the schematic variables will be prefixed with the 
question mark ``$?$'', like so: $?a$. Nonetheless, explicit 
quantification over the type variables at the top-level 
is also allowed: $\forall \alpha. \phi\left[\alpha\right]$. 
Lastly, the square brackets may be used either for the denotation 
of substitution or to indicate that certain types/terms are a part 
of a term: $t\left[?\alpha\right]$.
\<close>



subsection\<open>Previous work\<close>


subsubsection\<open>Relativization Algorithm\label{sec:ra}\<close>


text\<open>
Let ${}_{\alpha}(\beta \approx U)_{\mathsf{Rep}}^{\mathsf{Abs}}$ denote
\[
\begin{aligned}
& (\forall x_{\beta}. \mathsf{Rep}\ x \in U)\ \wedge\\
& (\forall x_{\beta}. \mathsf{Abs}\ (\mathsf{Rep}\ x) = x)\ \wedge\\
& (\forall y_{\alpha}. y \in U \longrightarrow \mathsf{Rep}\ (\mathsf{Abs}\ y) = y)
\end{aligned},
\]
let $\rightsquigarrow$ denote the constant/type \textit{dependency relation} 
(see subsection 2.3 in \cite{blanchette_types_2016}), 
let $\rightsquigarrow^{\downarrow}$ 
be a \textit{substitutive closure} of the constant/type dependency relation, 
let $R^{+}$ denote the transitive closure of 
the binary relation $R$, let $\Delta_c$ denote the set of all types for which 
$c$ is \textit{overloaded} and let $\sigma\not\leq S $ mean that $\sigma$ is not 
an instance of any type in $S$ (see \cite{blanchette_types_2016} and 
\cite{yang_comprehending_2017}).

The framework Types-To-Sets extends Isabelle/HOL with two axioms: 
\textit{Local Typedef Rule} (LT) and the \textit{Unoverloading Rule} (UO). 
The consistency of Isabelle/HOL augmented with the LT and
the UO is proved in Theorem 11 in \cite{yang_comprehending_2017}.

The LT is given by
\[
\begin{aligned}
\scalebox{1.0}{
\infer[\beta \not\in U, \phi, \Gamma]{\Gamma \vdash \phi}{%
\Gamma\vdash U \neq\emptyset
& \Gamma
  \vdash
  \left( 
    \exists \mathsf{Abs}\ \mathsf{Rep}. {}_{\sigma}(\beta\approx U)_{\mathsf{Rep}}^{\mathsf{Abs}}\longrightarrow\phi 
  \right)
} 
}
\end{aligned}
\]

Thus, if $\beta$ is fresh for the non-empty set $U_{\sigma\ \mathsf{set}}$, 
the formula $\phi$ and the context $\Gamma$, then $\phi$ can be proved in 
$\Gamma$ by assuming the existence of a type $\beta$ isomorphic to $U$.

The UO is given by
\[
\infer[\text{$\forall u$ in $\phi$}. \neg(u\rightsquigarrow^{\downarrow+}c_{\sigma});\ \sigma\not\leq\Delta_c]{\forall x_{\sigma}. \phi\left[x_{\sigma}/c_{\sigma}\right]}{\phi}
\]
Thus, a \textit{constant-instance} $c_{\sigma}$ may be replaced by a universally 
quantified variable $x_{\sigma}$ in $\phi$, if all types and 
constant-instances in $\phi$ do not semantically depend on $c_{\sigma}$ 
through a chain of constant and type definitions and there is no 
matching definition for $c_{\sigma}$.

The statement of the \textit{original relativization algorithm} (ORA) can be 
found in subsection 5.4 in \cite{blanchette_types_2016}. Here, we present
a variant of the algorithm that includes some of the amendments that were 
introduced in \cite{immler_smooth_2019}, which will be referred to as the 
\textit{relativization algorithm} (RA). 
The differences between the ORA and 
the RA are implementation-specific and have no effect on the output 
of the algorithm, if applied to a conventional input.
Let $\bar{a}$ denote a finite sequence $a_1,\ldots,a_n$ 
for some positive integer $n$; let $\Upsilon$ be a \textit{type class} 
\cite{nipkow_type_1991,wenzel_type_1997,altenkirch_constructive_2007} 
that depends on the overloaded constants $\bar{*}$ and 
let $U\downarrow\bar{f}$ be used 
to state that $U$ is closed under the operations $\bar{f}$; 
then the RA is given by 
\[
\infer[(7)]
{
\vdash ?U_{?\alpha\ \mathsf{set}} \neq\emptyset\longrightarrow
?U\downarrow?\bar{f}\left[?\alpha\right]\longrightarrow
\Upsilon^{\mathsf{on}}_{\mathsf{with}}\ ?U\ ?\bar{f}\longrightarrow
\phi^{\mathsf{on}}_{\mathsf{with}}\left[?\alpha,?U,?\bar{f}\right]
}
{
\infer[(6)]
{
U_{\alpha\ \mathsf{set}}\neq\emptyset
\vdash U\downarrow?\bar{f}\left[\alpha\right]\longrightarrow
\Upsilon^{\mathsf{on}}_{\mathsf{with}}\ U\ ?\bar{f}\longrightarrow
\phi^{\mathsf{on}}_{\mathsf{with}}\left[\alpha,U,?\bar{f}\right]
}
{
\infer[(5)]
{
U\neq\emptyset,{}_{\alpha}(\beta\approx U)_{\mathsf{Rep}}^{\mathsf{Abs}}
\vdash U\downarrow?\bar{f}\left[\alpha\right]\longrightarrow
\Upsilon^{\mathsf{on}}_{\mathsf{with}}\ U\ ?\bar{f}\longrightarrow
\phi^{\mathsf{on}}_{\mathsf{with}}\left[\alpha,U,?\bar{f}\right]
}
{
\infer[(4)]
{
U\neq\emptyset,{}_{\alpha}(\beta\approx U)_{\mathsf{Rep}}^{\mathsf{Abs}}
\vdash\Upsilon_{\mathsf{with}}\ ?\bar{f}\left[\beta\right]\longrightarrow
\phi_{\mathsf{with}}\left[\beta,?\bar{f}\right]
}
{
\infer[(3)]
{
U\neq\emptyset,{}_{\alpha}(\beta\approx U)_{\mathsf{Rep}}^{\mathsf{Abs}}
\vdash\Upsilon_{\mathsf{with}}\ ?\bar{f}\left[?\alpha\right]\longrightarrow
\phi_{\mathsf{with}}\left[?\alpha,?\bar{f}\right]
}
{
\infer[(2)]
{
\vdash\Upsilon_{\mathsf{with}}\ ?\bar{f}\left[?\alpha\right]\longrightarrow
\phi_{\mathsf{with}}\left[?\alpha,?\bar{f}\right]
}
{
\infer[(1)]
{\vdash\phi_{\mathsf{with}}\left[?\alpha_{\Upsilon},\bar{*}\right]}
{\vdash\phi\left[?\alpha_{\Upsilon}\right]}
}
}
}
}
}
}
\]
The input to the RA is assumed to be a theorem 
$\vdash\phi\left[?\alpha_{\Upsilon}\right]$. 
Step 1 will be referred to as the first step of the dictionary 
construction (subsection 5.2 in \cite{blanchette_types_2016}); 
step 2 as unoverloading of the type $?\alpha_{\Upsilon}$: 
it includes class internalization (subsection 5.1 in \cite{blanchette_types_2016}) 
and the application of the UO (it corresponds to the application 
of the attribute @{attribute unoverload_type} \cite{immler_smooth_2019}); 
step 3 provides the assumptions that are the prerequisites for 
the application of the LT; 
step 4 is reserved for the concrete type instantiation; 
step 5 is the application of \textit{Transfer} 
(section 6 in \cite{blanchette_types_2016}); 
step 6 refers to the application of the LT; 
step 7 is the export of the theorem from the local 
context \cite{wenzel_isabelle/isar_2019}.
\<close>


subsubsection\<open>Implementation of Types-To-Sets\label{subsec:ITTS}\<close>


text\<open>

In \cite{blanchette_types_2016}, the authors extended the implementation 
of Isabelle/HOL with the LT and UO. Also, they introduced the 
attributes @{attribute internalize_sort},
@{attribute unoverload} and @{attribute cancel_type_definition}  
that allowed for the execution of steps 1, 3 and 7 (respectively) of the ORA. 
Other steps could be performed using the technology that already existed. 
In \cite{immler_smooth_2019}, the implementation was augmented with the 
attribute @{attribute unoverload_type},
which largely subsumed the functionality of the attributes 
@{attribute internalize_sort} and @{attribute unoverload}.

The examples of the application of the ORA to theorems in 
Isabelle/HOL that were developed in \cite{blanchette_types_2016}
already contained an implicit suggestion that the constants and theorems 
needed for the first step of the dictionary construction in step 2 of 
the ORA and the \textit{transfer rules} \cite{kuncar_types_2015} 
needed for step 6 of the ORA can and should 
be obtained prior to the application of the algorithm. Thus, using the notation
from subsection \ref{sec:ra}, for each constant-instance $c_{\sigma}$ 
that occurs in the type-based theorem 
$\vdash\phi\left[?\alpha_{\Upsilon}\right]$
prior to the application of the ORA with respect to 
${}_{\alpha}(\beta \approx U)_{\mathsf{Rep}}^{\mathsf{Abs}}$, 
the users were expected to provide
an \textit{unoverloaded} constant $c_{\mathsf{with}}$ such that 
$c_{\sigma} = c_{\mathsf{with}}\ \bar{*}$, 
and a \textit{relativized} constant 
$c^{\mathsf{on}}_{\mathsf{with}}$ 
such that $R\left[T_{\alpha\rightarrow\beta\rightarrow\mathbb{B}}\right]
\ (c^{\mathsf{on}}_{\mathsf{with}}\ U_{\alpha\ \mathsf{set}})\ c_{\mathsf{with}}$ 
($\mathbb{B}$ denotes the built-in Isabelle/HOL type $bool$
\cite{kuncar_types_2015})
is a conditional transfer rule (e.g., see \cite{gonthier_lifting_2013}), 
with $T$ being a binary 
relation that is at least right-total and bi-unique, 
assuming the default order on predicates
in Isabelle/HOL (see \cite{kuncar_types_2015}).  

The unoverloading \cite{kaufmann_mechanized_2010} 
and relativization of constants for the application 
of the RA was performed manually in 
\cite{blanchette_types_2016,kuncar_types_2019,immler_smooth_2019}. 
Nonetheless, unoverloading could be performed using the 
\textit{classical overloading elimination algorithm} proposed 
in \cite{kaufmann_mechanized_2010}, but it is likely that an implementation
of this algorithm was not publicly available at the time of writing
of this document. In \cite{immler_automation_2019}, an alternative algorithm was 
implemented and made available via the command 
@{command unoverload_definition}, 
although it suffers from several limitations in comparison to the 
algorithm in \cite{kaufmann_mechanized_2010}. 
The transfer rules 
for the constants that are conditionally parametric 
can be synthesized automatically using the command 
@{command parametric_constant} 
\cite{gilcher_conditional_2017} from the standard distribution of Isabelle; 
the framework \textit{autoref} \cite{lammich_automatic_2013} allows 
for the synthesis of transfer rules $R\ t\ t'$, 
including both the \textit{parametricity relation} \cite{kuncar_types_2015}
$R$ and the term $t$, 
based on $t'$, under favorable conditions; 
lastly, in \cite{lammich_automatic_2013} and \cite{immler_smooth_2019}, 
the authors suggest an outline of another feasible algorithm for the 
synthesis of the transfer rules based on the functionality of the framework
Transfer \cite{gonthier_lifting_2013}, but do not provide an implementation.

Finally, the assumption 
${}_{\alpha}(\beta \approx U)_{\mathsf{Rep}}^{\mathsf{Abs}}$ 
can be stated using the constant @{const type_definition}
from the standard library of Isabelle/HOL as 
\<^term>\<open>type_definition Rep Abs U\<close>;
the instantiation of types required in step 4 of the RA can 
be performed using the standard attributes of Isabelle; 
step 6 can be performed using the attribute 
@{attribute cancel_type_definition} developed in 
\cite{blanchette_types_2016}; step 7 is expected to be performed manually
by the user.

\<close>



subsection\<open>Purpose and scope\<close>


text\<open>
The extension of the framework Types-To-Sets that is described in this manual
adds a further layer of automation to the existing implementation
of the framework Types-To-Sets. The primary functionality of the extension 
is available via the following Isar commands: 
@{command tts_context}, @{command tts_lemmas} and @{command tts_lemma} (and the
synonymous commands @{command tts_corollary}, @{command tts_proposition} and
@{command tts_theorem}\footnote{In what follows, any reference to the 
command @{command tts_lemma} should be viewed as a reference to the 
entire family of the commands with the identical functionality.}).
The commands @{command tts_lemmas} and @{command tts_lemma}, when invoked inside
an appropriately defined @{command tts_context} provide the 
functionality that is approximately equivalent to the application of all 
steps of the RA and several additional steps of 
pre-processing of the input and post-processing of the result
(collectively referred to as the \textit{extended relativization algorithm} 
or ERA).

As part of our work on the ETTS, we have also designed 
the auxiliary framework \textit{Conditional Transfer Rule} (CTR). 
The framework CTR provides the commands @{command ud} and @{command ctr} for
the automation of unoverloading of definitions and 
synthesis of conditional transfer rules from definitions, 
respectively. Further information about this framework can be found in its
reference manual \cite{milehins_conditional_2021}.

The extension was designed under a policy of non-intervention with the  
existing implementation of the framework Types-To-Sets. Therefore, it does
not reduce the scope of the applicability of the framework. 
However, the functionality that is provided by the commands associated with the 
extension is a proper subset of the functionality provided by the existing 
implementation. Nevertheless, the author of the extension believes that there 
exist very few practical applications of the relativization algorithm that 
can be solved using the original interface but cannot be solved using 
the commands that are introduced within the scope of the 
extension.
\<close>

text\<open>\newpage\<close>

end