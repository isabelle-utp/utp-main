(* Copyright 2021 (C) Mihails Milehins *)

chapter\<open>Introduction\<close>
theory CZH_Introduction
  imports ZFC_in_HOL.ZFC_Typeclasses
begin



section\<open>Background\<close>


text\<open>
This article presents a foundational framework
that will be used for the formalization of
elements of the theory of 1-categories in the object logic 
\<open>ZFC in HOL\<close> (\cite{paulson_zermelo_2019}, also see
\cite{barkaoui_partizan_2006}) of the formal proof assistant 
\<open>Isabelle\<close> \cite{paulson_natural_1986} in future articles.
It is important to note that this chapter serves as 
an introduction to the entire development and not merely
its foundational part. 

There already exist several formalizations of the foundations of category 
theory in Isabelle. In the context of the work presented here, the most relevant
formalizations (listed in the chronological order) are 
\cite{okeefe_category_2005}, \cite{katovsky_category_2010} and 
\cite{stark_category_2016}. 
Arguably, the most well developed and maintained entry is 
\cite{stark_category_2016}: it subsumes the majority of the content of 
\cite{okeefe_category_2005} and \cite{katovsky_category_2010}.

From the perspective of the methodology that was chosen for the formalization, 
this work differs significantly from the aforementioned previous work.
In particular, the categories are modelled as terms of the type \<^typ>\<open>V\<close> 
and no attempt is made to generalize the concept of a category to arbitrary 
types. The inspiration for the chosen approach is drawn from  
\cite{feferman_set-theoretical_1969},
\cite{sica_doing_2006} and \cite{shulman_set_2008}.

The primary references for this work are 
\<open>Categories for the Working Mathematician\<close> \cite{mac_lane_categories_2010}
by Saunders Mac Lane, \<open>Category Theory in Context\<close> 
by Emily Riehl \cite{riehl_category_2016} and 
\<open>Categories and Functors\<close> by Bodo Pareigis \cite{bodo_categories_1970}. 
The secondary sources of information include the textbooks 
\cite{adamek_abstract_2006} and \cite{hungerford_algebra_2003}, 
as well as several online encyclopedias
(including \cite{noauthor_nlab_nodate}, 
\cite{noauthor_wikipedia_2001}, 
\cite{noauthor_proofwiki_nodate}
and \cite{noauthor_encyclopedia_nodate}). 
Of course, inspiration was also drawn from the previous formalizations of 
category theory in Isabelle. 

It is likely that none of the content that is formalized in this work
is original in nature. However, explicit citations
are not provided for many results that were deemed to be trivial.
\<close>



section\<open>Related and previous work\<close>


text\<open>
To the best knowledge of the author, this work is the first attempt
to develop a formalization of elements of category theory in the 
object logic ZFC in HOL by modelling categories as terms of the type \<^typ>\<open>V\<close>.
However, it should be noted that the formalization of category theory in
\cite{katovsky_category_2010} largely rested 
on the object logic HOL/ZF \cite{barkaoui_partizan_2006}, which is 
equiconsistent with the ZFC in HOL \cite{paulson_zermelo_2019}. 
Nonetheless, in \cite{katovsky_category_2010}, the objects and arrows
associated with categories were modelled as terms of arbitrary
types. The object logic HOL/ZF was used for the exposition of 
the category \<open>Set\<close> of all sets and functions between them 
and a variety of closely related concepts.
In this sense, the methodology employed in 
\cite{katovsky_category_2010} could be seen as a combination of the 
methodology employed in this work and the methodology followed in
\cite{okeefe_category_2005} and \cite{stark_category_2016}.
Furthermore, in \cite{chen_hotg_2021}, 
the authors have experimented with the formalization of category 
theory in Higher-Order Tarski-Grothendieck (HOTG)
theory \cite{brown_higher-order_2019} using a methodology that 
shares many similarities with the approach that was chosen in this study.

The formalizations of various elements of category theory 
in other proof assistants are abundant.
While a survey of such formalizations is outside of the scope of
this work, it is important to note that there exist at least two examples 
of the formalization of elements of category theory in a set-theoretic setting
similar to the one that is used in this work. 
More specifically, elements of category theory were formalized in
the Tarski-Grothendieck Set Theory in the Mizar proof assistant 
\cite{noauthor_association_nodate} (and
published in the associated electronic journal 
\cite{grabowski_preface_2014}) 
and the proof assistant Metamath
\cite{megill_metamath_2019}.
The following references contain some of the 
relevant articles in \cite{grabowski_preface_2014}, but the list may not be 
exhaustive: 
\cite{bylinski_introduction_1990, bylinski_subcategories_1990, 
bylinski_opposite_1991, trybulec_natural_1991, 
bylinski_category_1991, muzalewski_categories_1991,
trybulec_isomorphisms_1991, muzalewski_category_1991,
muzalewski_category_1991-1, bancerek_comma_1991,
bylinski_products_1991, trybulec_isomorphisms_1992, 
bylinski_cartesian_1992, bancerek_categorial_1996,
trybulec_categories_1996, bancerek_indexed_1996,
trybulec_functors_1996, nieszczerzewski_category_1997,
kornilowicz_categories_1997,
kornilowicz_composition_1998, 
bancerek_concrete_2001,
kornilowicz_products_2012,
riccardi_object-free_2013,
golinski_coproducts_2013, 
riccardi_categorical_2015,
riccardi_exponential_2015}.
\<close>

end