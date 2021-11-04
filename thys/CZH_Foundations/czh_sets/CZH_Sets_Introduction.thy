(* Copyright 2021 (C) Mihails Milehins *)

chapter\<open>Set Theory for Category Theory\<close>

section\<open>Introduction\<close>
theory CZH_Sets_Introduction
  imports 
    CZH_Introduction
    CZH_Sets_MIF
    CZH_Utilities
    Intro_Dest_Elim.IHOL_IDE
    Conditional_Simplification.IHOL_CS
    ZFC_in_HOL.Cantor_NF
    "HOL-Eisbach.Eisbach"
begin



subsection\<open>Background\<close>


text\<open>
This chapter presents a formalization of the elements of set theory in 
the object logic \<open>ZFC in HOL\<close> (\cite{paulson_zermelo_2019}, also see
\cite{barkaoui_partizan_2006})
of the formal proof assistant Isabelle \cite{paulson_natural_1986}.
The emphasis of this work is on the improvement of the convenience of the 
formalization of abstract mathematics internalized in the type \<^typ>\<open>V\<close>.
\<close>



subsection\<open>References, related and previous work\<close>


text\<open>
The results that are presented in this chapter cannot be traced to a single
source of information. Nonetheless, the results are not original. 
A significant number of these results was carried over (with amendments) 
from the main library of Isabelle/HOL \cite{noauthor_isabellehol_2020}. 
Other results were inspired by elements of the content of the books 
\<open>Introduction to Axiomatic Set Theory\<close> by G. Takeuti 
and W. M. Zaring \cite{takeuti_introduction_1971}, \<open>Theory of Sets\<close> 
by N. Bourbaki \cite{bourbaki_elements_1970} and \<open>Algebra\<close> by 
T. W. Hungerford \cite{hungerford_algebra_2003}.
Furthermore, several online encyclopedias and forums 
(including Wikipedia \cite{noauthor_wikipedia_2001}, 
ProofWiki \cite{noauthor_proofwiki_nodate}, 
Encyclopedia of Mathematics \cite{noauthor_encyclopedia_nodate},
nLab \cite{noauthor_nlab_nodate} and Mathematics Stack Exchange) 
were used consistently throughout the development of this chapter. 
Inspiration for the work presented in this chapter has also been drawn 
from a similar ongoing project
in the formalization of mathematics in the system 
HOTG (Higher Order Tarski-Grothendieck) 
\cite{brown_higher-order_2019, chen_hotg_2021}.

It should also be mentioned that the Isabelle/HOL and the Isabelle/ML code 
from the main distribution of Isabelle2020 and certain posts on the 
mailing list of Isabelle were frequently reused
(with amendments) during the development of this chapter. Some of the 
specific examples of such reuse are 
\begin{itemize}
\item The adoption of the implementation of
the command @{command lemmas_with} that is available as part of 
the framework Types-To-Sets in the main distribution of Isabelle2020.
\item The notation for the ``multiway-if'' was written
by Manuel Eberl and appeared in a post on the mailing list of Isabelle:
\cite{eberl_syntax_2021}.
\end{itemize}
\<close>

hide_const (open) list.set Sum subset 

lemmas ord_of_nat_zero = ord_of_nat.simps(1)



subsection\<open>Notation\<close>

abbreviation (input) qm (\<open>(_ ? _ : _)\<close> [0, 0, 10] 10) 
  where "C ? A : B \<equiv> if C then A else B"
abbreviation (input) if2 where "if2 a b \<equiv> (\<lambda>i. (i = 0 ? a : b))"



subsection\<open>Further foundational results\<close>

lemma theD:
  assumes "\<exists>!x. P x" and "x = (THE x. P x)"
  shows "P x" and "P y \<Longrightarrow> x = y"
  using assms by (metis theI)+

lemmas [intro] = bij_betw_imageI

lemma bij_betwE[elim]:
  assumes "bij_betw f A B" and "\<lbrakk> inj_on f A; f ` A = B \<rbrakk> \<Longrightarrow> P"
  shows P
  using assms unfolding bij_betw_def by auto

lemma bij_betwD[dest]:
  assumes "bij_betw f A B"
  shows "inj_on f A" and "f ` A = B"
  using assms by auto

text\<open>\newpage\<close>

end