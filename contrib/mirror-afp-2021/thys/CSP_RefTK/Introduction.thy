(*<*)
\<comment>\<open> ********************************************************************
 * Project         : CSP-RefTK - A Refinement Toolkit for HOL-CSP
 * Version         : 1.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye.
 *
 * This file       : An Introduction
 *
 * Copyright (c) 2020 Université Paris-Saclay, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)

chapter\<open>Context\<close>
(*<*)
theory Introduction
    imports HOLCF
begin
(*>*)

section\<open>Introduction\<close>

text\<open>
Communicating Sequential Processes CSP is a language 
to specify and verify patterns of interaction of concurrent systems.
Together with CCS and LOTOS, it belongs to the family of \<^emph>\<open>process algebras\<close>. 
CSP's rich theory comprises denotational, operational and algebraic semantic facets 
and has influenced programming languages such as Limbo, Crystal, Clojure and
most notably Golang @{cite "donovan2015go"}. CSP has been applied in 
industry as a tool for specifying and verifying the concurrent aspects of hardware 
systems, such as the T9000 transputer @{cite "Barret95"}. 

The theory of CSP, in particular the denotational Failure/Divergence Denotational Semantics,
has been initially proposed in the book by Tony Hoare @{cite "Hoare:1985:CSP:3921"}, but evolved
substantially since @{cite "BrookesHR84" and "brookes-roscoe85" and "roscoe:csp:1998"}.

Verification of CSP properties has been centered around the notion of \<^emph>\<open>process refinement orderings\<close>,
most notably \<open>_\<sqsubseteq>\<^sub>F\<^sub>D_\<close> and \<open>_\<sqsubseteq>_\<close>. The latter turns the denotational domain of CSP into a Scott cpo 
@{cite "scott:cpo:1972"}, which yields semantics for the fixed point operator \<open>\<mu>x. f(x)\<close> provided 
that \<open>f\<close> is continuous with respect to \<open>_\<sqsubseteq>_\<close>. Since it is possible to express deadlock-freeness and 
livelock-freeness as a refinement problem, the verification of properties has been reduced 
traditionally to a model-checking problem for a finite set of events \<open>A\<close>.

We are interested in verification techniques for arbitrary event sets \<open>A\<close> or arbitrarily 
parameterized processes. Such processes can be used to model dense-timed processes, processes 
with dynamic thread creation, and processes with unbounded thread-local variables and buffers.
Events may even be higher-order objects such as functions or again processes, paving the way
for the modeling of re-programmable compute servers or dynamic distributed computing architectures.
However, this adds substantial complexity to the process theory: when it comes to study the 
interplay of different denotational models, refinement-orderings, and side-conditions for 
continuity, paper-and-pencil proofs easily reach their limits of precision. 

Several attempts have been undertaken to develop the formal theory of CSP in an interactive proof system, 
mostly in Isabelle/HOL @{cite "Camilleri91" and "tej.ea:corrected:1997" and  "IsobeRoggenbach2010"}. 
This work is based on the most recent instance in this line, HOL-CSP 2.0, which has been published 
as AFP submission  @{cite "HOL-CSP-AFP"} and whose development is hosted at 
\<^url>\<open>https://gitlri.lri.fr/burkhart.wolff/hol-csp2.0\<close>. 

The present AFP Module is an add-on on this work and develops some support for 
\<^enum> advanced induction schemes (mutual fixed-point Induction, K-induction),
\<^enum> bridge-Lemmas between the classical refinement relations in the FD-semantics,
  which allow for reduced refinement proof complexity in certain cases, and
\<^enum> a theory of explicit state normalisation which allows for proofs over certain
  communicating networks of arbitrary size.

\newpage
\<close>



section\<open>The Global Architecture of CSP\_RefTk\<close>
text\<open>
\begin{figure}[ht]
  \centering
  \includegraphics[width=0.60\textwidth]{figures/session_graph.pdf}
	\caption{The overall architecture: HOLCF, HOL-CSP, and CSP\_RefTk}
	\label{fig:fig1}
\end{figure}
\<close>

text\<open>The global architecture of CSP\_RefTk is shown in \autoref{fig:fig1}.
The entire package resides on: 
\<^enum> \<^session>\<open>HOL-Eisbach\<close> from the Isabelle/HOL distribution,
\<^enum> \<^session>\<open>HOLCF\<close> from the Isabelle/HOL distribution, and
\<^enum> \<^session>\<open>HOL-CSP\<close> 2.0 from the Isabelle Archive of Formal Proofs.

\<^noindent> The theories \<^verbatim>\<open>Assertion_ext\<close> and \<^verbatim>\<open>Fixind_ext\<close> are extensions of the 
corresponding theories in \<^session>\<open>HOL-CSP\<close>.\<close>


(*<*)
end
(*>*)
