(* Title: Examples/Introduction.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

chapter\<open>ETTS Case Studies: Introduction\<close>
theory Introduction
  imports Types_To_Sets_Extension.ETTS_Auxiliary
begin




section\<open>Background\<close>



subsection\<open>Purpose\<close>


text\<open>
The remainder of this document presents several examples of the application 
of the extension of the framework Types-To-Sets and provides the potential 
users of the extension with a plethora of design 
patterns to choose from for their own applied relativization needs. 
\<close>



subsection\<open>Related work\<close>


text\<open>
Since the publication of the framework Types-To-Sets in
\cite{blanchette_types_2016}, there has been a growing interest
in its use in applied formalization. Some 
of the examples of the application of the framework include
\cite{divason_perron-frobenius_2016}, 
\cite{maletzky_hilberts_2019} and \cite{immler_smooth_2019}. However, this
list is not exhaustive. Arguably, the most significant application example 
was developed in \cite{immler_smooth_2019}, where Fabian Immler and
Bohua Zhan performed the 
relativization of over 200 theorems from the standard mathematics library
of Isabelle/HOL.

Nonetheless, it is likely that the work presented in this document 
is the first significant application of the ETTS: 
unsurprisingly, the content of this document was developed 
in parallel with the extension of the framework itself. Also, perhaps, it is
the largest application of the framework Types-To-Sets 
at the time of writing: 
only one of the three libraries (SML Relativization) presented in the 
context of this work contains the relativization of over 800 theorems 
from the standard library of Isabelle/HOL.
\<close>




section\<open>Examples: overview\<close>



subsection\<open>Background\<close>


text\<open>
The examples that are presented in this document were developed for the 
demonstration of the impact of various aspects of the relativization process 
on the outcome of the relativization. 
Three libraries of relativized results were developed in the context 
of this work:
\begin{itemize}
\item \textit{SML Relativization}: a relativization 
of elements of the standard mathematics library of Isabelle/HOL
\item \textit{TTS Vector Spaces}: a renovation of the set-based
library that was developed in \cite{immler_smooth_2019} using the ETTS
instead of the existing interface for Types-To-Sets
\item \textit{TTS Foundations}: a relativization of a miniature type-based 
library with every constant being parametric under the side
conditions compatible with Types-To-Sets
\end{itemize}
\<close>



subsection\<open>SML Relativization\<close>


text\<open>
The standard library that is associated with the 
object logic Isabelle/HOL and provided as a part of the 
standard distribution of Isabelle \cite{noauthor_isabellehol_2020} 
contains a significant number of formalized results from a variety of 
fields of mathematics. However, the formalization is performed using a 
type-based approach: for example, the carrier sets associated with the 
algebraic structures and the underlying sets of the topological spaces 
consist of all terms of an arbitrary type.
The ETTS was applied to the relativization of a certain number of results from 
the standard library.

The results that are formalized in the library 
SML Relativization are taken from an array of topics that include 
order theory, group theory, ring theory and topology.
However, only the
results whose relativization could be nearly fully automated using 
the frameworks UD, CTR and ETTS with almost no additional proof effort
are included.
\<close>



subsection\<open>TTS Vector Spaces\<close>


text\<open>
The TTS Vector Spaces is a remake of the library of relativized results that 
was developed in \cite{immler_smooth_2019} using the ETTS.
The theorems that are provided in the library TTS Vector Spaces are nearly 
identical to the results that are provided in \cite{immler_smooth_2019}. 

A detailed description of the original library has already
been given in \cite{immler_smooth_2019} and will not be restated.
The definitional frameworks that are used in \cite{immler_smooth_2019}
and the TTS Vector Spaces are similar. While the unoverloading 
of most of the constants could be performed by using the 
command @{command ud}, the command @{command ctr} could not 
be used to establish that the unoverloaded constants are 
parametric under a suitable set of side conditions. Therefore,
like in \cite{immler_smooth_2019}, the proofs of the transfer rules were 
performed manually. However, the advantages 
of using the ETTS become apparent during the relativization of 
theorems: the complex infrastructure that was needed for 
compiling out dependencies on overloaded constants, the manual invocation of the 
attributes related to the individual steps of the relativization algorithm, 
the repeated explicit references to the theorem as it undergoes the 
transformations associated with the individual steps of 
the relativization algorithm, the explicitly stated names of the set-based 
theorems were no longer needed. Furthermore, the theorems synthesized by the 
ETTS in TTS Vector Spaces appear in the formal proof documents in a format 
that is similar to the canonical format of the Isabelle/Isar declarations
associated with the standard commands such as @{command lemma}.
\<close>



subsection\<open>TTS Foundations\<close>


text\<open>
The most challenging aspect of the relativization
process, perhaps, is related to the availability of the transfer rules for the
constants in the type-based theorems. Nonetheless, even if the transfer 
rules are available, having to use the relativized constants in the set-based 
theorems that are different from the original constants that are used in the 
type-based theorems can be seen as unnatural and inconvenient. 
Unfortunately, the library SML Relativization suffers from both 
of the aforementioned problems. The library that was 
developed in \cite{immler_smooth_2019} 
(hence, also the library TTS Vector Spaces) 
suffers, primarily, from the former problem, but, arguably, due to the methodology
that was chosen for the relativization, the library has a more restricted scope
of applicability.

The library TTS Foundations provides an example of a miniature 
type-based library such that all constants associated with the operations on
mathematical structures (effectively, this excludes the
constants associated with the locale predicates) 
in the library are parametric under the side conditions 
compatible with Types-To-Sets. The relativization is 
performed with respect to all possible type variables; in this case,
the type classes are not used in the type-based library. Currently,
the library includes the results from the areas of order theory and
semigroups. However, it is hoped that it can be seen
that the library can be extended to include most of the
content that is available in the main library of Isabelle/HOL.

The library TTS Foundations demonstrates that the development of a 
set-based library can be nearly fully automated using the 
existing infrastructure associated with the UD, CTR and ETTS, 
and requires almost no explicit proofs on
behalf of the users of these frameworks.
\<close>

end