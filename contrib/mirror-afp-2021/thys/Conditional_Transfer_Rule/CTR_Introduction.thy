(* Title: CTR_Introduction.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

section\<open>Introduction\<close>
theory CTR_Introduction
  imports Main
begin



subsection\<open>Background\<close>

text\<open>
The framework Conditional Transfer Rule (CTR) provides several experimental
\textit{Isabelle/Isar} 
\cite{wenzel_isabelle/isar_2001, wenzel_isabelle/isar_2019-1, bertot_isar_1999}
commands that are aimed at the automation of unoverloading
of definitions and synthesis of conditional transfer rules 
in the object logic Isabelle/HOL of the formal proof assistant Isabelle.
\<close>



subsection\<open>Structure and organization\<close>

text\<open>
The remainder of the reference manual is organized into two explicit sections,
one for each sub-framework of the CTR:
\begin{itemize}
\item \textit{Unoverload Definition} (UD): automated elimination of sort
constraints and unoverloading of definitions
\item \textit{Conditional Transfer Rule} (CTR): automated synthesis of 
conditional transfer rules from definitions
\end{itemize}
It should be noted that the abbreviation CTR will be used to 
refer both to the general framework and the sub-framework.
\<close>

text\<open>\newpage\<close>

end