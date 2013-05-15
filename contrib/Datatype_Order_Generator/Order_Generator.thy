(*  Title:       Deriving class instances for datatypes
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2012 René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

header {* Generating linear orders for datatypes *}

theory Order_Generator
imports Derive_Manager
begin

subsection Introduction

text {*

The order generator registers itself at the derive-manager for the classes \texttt{ord},
\texttt{order}, and \texttt{linorder}.
To be more precise,
it automatically generates the two functions $\le$ and $<$ for some datatype 
\texttt{dtyp} and
proves the following instantiations.

\begin{itemize}
\item \texttt{instantiation dtyp :: (ord,\ldots,ord) ord}
\item \texttt{instantiation dtyp :: (order,\ldots,order) order}
\item \texttt{instantiation dtyp :: (linorder,\ldots,linorder) linorder}
\end{itemize}

All the non-recursive types that are used in the datatype must have similar instantiations.
For recursive type-dependencies this is automatically generated.

For example, for the \texttt{datatype tree = Leaf nat | Node "tree list"} we require that
\texttt{nat} is already in \texttt{linorder}, whereas for \texttt{list}s nothing is required, since for the 
\texttt{tree}
datatype the \texttt{list} is used recursively.

However, if we define \texttt{datatype tree = Leaf "nat list" | Node tree tree} then 
\texttt{list} must
provide the above instantiations.

Note that when calling the generator for \texttt{linorder}, it will automatically also derive the instantiations 
for \texttt{order}, which in turn invokes the generator for \texttt{ord}. A later invokation of \texttt{linorder}
after \texttt{order} or \texttt{ord} is not possible.
*}

subsection "Implementation Notes"

text {*
The generator uses the recursors from the datatype package to define a lexicographic order.
E.g., for a declaration 
\texttt{datatype 'a tree = Empty | Node "'a tree" 'a "'a tree"}
this will semantically result in
\begin{verbatim}
(Empty < Node _ _ _) = True
(Node l1 l2 l3 < Node r1 r2 r3) = 
  (l1 < r1 || l1 = r1 && (l2 < r2 || l2 = r2 && l3 < r3))
(_ < _) = False
(l <= r) = (l < r || l = r)
\end{verbatim}

The desired properties (like \texttt{x < y ==> y < z ==> x < z}) 
of the orders are all proven using induction (with the induction theorem from the datatype on \texttt{x}),
and afterwards there is a case distinction on the remaining variables, i.e., here \texttt{y} and \texttt{z}.
If the constructors of \texttt{x}, \texttt{y}, and \texttt{z} are different always some basic tactic is invoked. 
In the other case (identical constructors) for each property a dedicated tactic was designed.
*}

subsection "Features and Limitations"

text {*
The order generator has been developed mainly for datatypes without explicit mutual recursion. 
For mutual recursive datatypes---like
\texttt{datatype a = C b and b = D a a}---only
for the first mentioned datatype---here \texttt{a}---the instantiations of the order-classes are
derived.

Indirect recursion like in \texttt{datatype tree = Leaf nat | Node "tree list"} should work 
without problems.
*}

subsection "Installing the generator"

lemma linear_cases: "(x :: 'a :: linorder) = y \<or> x < y \<or> y < x" by auto

ML_file "order_generator.ML" 

setup {*
  Order_Generator.setup
*}

end
