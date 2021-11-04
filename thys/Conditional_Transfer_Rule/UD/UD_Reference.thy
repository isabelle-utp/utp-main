(* Title: UD/UD_Reference.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Reference manual for the UD.
*)

section\<open>UD\<close>
theory UD_Reference
  imports 
    UD
    "../Reference_Prerequisites"
begin



subsection\<open>Introduction\<close>


subsubsection\<open>Background\<close>

text\<open>
This section presents a reference manual for the sub-framework UD. 
The UD can be used for the elimination of 
\textit{sort constraints} (e.g., see \cite{altenkirch_constructive_2007})
and unoverloading of definitions in the object logic Isabelle/HOL of the 
formal proof assistant Isabelle. 
The UD evolved from the author's work on an extension of the 
framework \textit{Types-To-Sets} 
(see 
\cite{blanchette_types_2016, kuncar_types_2019, immler_smooth_2019, immler_automation_2019},
for a description of the framework Types-To-Sets
and \cite{milehins_extension_2021} for a description of the author's extension)
and builds upon certain ideas expressed in \cite{kaufmann_mechanized_2010}.
\<close>


subsubsection\<open>Purpose and scope\<close>

text\<open>
The primary functionality of the framework is available via the Isabelle/Isar 
command @{command ud}. This command automates the processes of the 
elimination of sort constraints and unoverloading of definitions.
Thus, the command @{command ud} allows for the synthesis
of the convenience constants and theorems that are usually needed for the 
application of the derivation step 2 of the original relativization algorithm
of Types-To-Sets (see subsection 5.4 in \cite{blanchette_types_2016}). However, 
it is expected that the command can be useful for other purposes.
\<close>


subsubsection\<open>Related and previous work\<close>

text\<open>
The functionality provided by the command @{command ud} shares similarities
with the functionality provided by the algorithms for the elimination of
sort constraints and elimination of overloading that were 
presented in \cite{kaufmann_mechanized_2010}
and with the algorithm associated with the command 
\mbox{\textbf{unoverload\_definition}} that was proposed
in \cite{immler_automation_2019}. 
Nonetheless, technically, unlike \mbox{\textbf{unoverload\_definition}}, 
the command @{command ud} does
not require the additional axiom UO associated with Types-To-Sets for 
its operation (see \cite{blanchette_types_2016}, 
\cite{immler_automation_2019}), it uses 
the \textit{definitional axioms} (e.g., see \cite{kaufmann_mechanized_2010})
instead of arbitrary theorems supplied by the user
and it is independent of the infrastructure associated with
the \textit{axiomatic type classes} 
\cite{nipkow_type_1991,wenzel_type_1997,altenkirch_constructive_2007}.

It should also be mentioned that the Isabelle/ML code from the main 
distribution of Isabelle was frequently reused during the 
development of the UD.
\<close>



subsection\<open>Theory\label{sec:ud_theory}\<close>


text\<open>
The general references for this subsection are
\cite{kaufmann_mechanized_2010} and \cite{yang_comprehending_2017}.
The command @{command ud} relies 
on a restricted (non-recursive) variant of the 
\textit{classical overloading elimination algorithm}
that was originally proposed in \cite{kaufmann_mechanized_2010}.
It is assumed that there exists 
a variable $ud_{\mathsf{with}}$ that stores theorems of the 
form $c_{\tau} = c_{\mathsf{with}}\ \bar{*}$, where $c_{\tau}$ and 
$c_{\mathsf{with}}$ are distinct \textit{constant-instances} 
and $\bar{*}$ is a finite sequence of \textit{uninterpreted constant-instances},
such that, if $c_{\tau}$ depends on a type variable $\alpha_{\Upsilon}$, 
with $\Upsilon$ being a \textit{type class} 
\cite{nipkow_type_1991,wenzel_type_1997,altenkirch_constructive_2007}
that depends on the overloaded 
constants $\bar{*'}$, then $\bar{*}$ contains $\bar{*'}$ as a subsequence. 
Lastly, the binary operation $\cup$ is defined in a manner such that 
for any sequences $\bar{*}$ and $\bar{*'}$, $\bar{*} \cup \bar{*'}$ 
is a sequence that consists of all elements of the union of the 
elements of $\bar{*}$ and $\bar{*'}$ without duplication. 
Assuming an underlying 
\textit{well-formed definitional theory} $D$, 
the input to the algorithm is a constant-instance $c_{\sigma}$. 
Given the constant-instance $c_{\sigma}$, 
there exists at most one definitional axiom
$c_{\tau} = \phi_{\tau}\left[\bar{*}\right]$ 
in $D$ such that $c_{\sigma} \leq c_{\tau}$: otherwise 
the \textit{orthogonality} of $D$ and, 
therefore, the \textit{well-formedness}
of $D$ are violated ($\phi$ is assumed to be parameterized by 
the types that it can have with respect to the
type substitution operation, 
and $\bar{*}$ in $c_{\tau} = \phi_{\tau}\left[\bar{*}\right]$ 
is a list of all uninterpreted constant-instances that 
occur in $\phi_{\tau}\left[\bar{*}\right]$).

If a definitional axiom $c_{\tau}=\phi_{\tau}\left[\bar{*}\right]$ 
such that $c_{\sigma} \leq c_{\tau}$ 
exists for the constant-instance $c_{\sigma}$, 
then the following derivation is applied to it by the algorithm
\[
\infer[(6)]
{\vdash c_{\sigma} = c_{\mathsf{with}}\ \left(\bar{*} \cup \bar{*'}\right)}
{
\infer[(5)]
{
\vdash c_{\mathsf{with}}\ \left(\bar{*} \cup \bar{*'}\right) = 
\phi_{\mathsf{with}}\left[\bar{*} \cup \bar{*'}\right]
}
{
\infer[(4)]
{\vdash c_{\mathsf{with}}\ ?\bar{f} = \phi_{\mathsf{with}}\left[?\bar{f}\right]}
{
\infer[(3)]
{\vdash c_{\mathsf{with}} = (\lambda \bar{f}.\ \phi_{\mathsf{with}}\left[\bar{f}\right])}
{
\infer[(2)]
{\vdash c_{\sigma}=\phi_{\mathsf{with}}\left[\bar{*} \cup \bar{*'}\right]}
{
\infer[(1)]
{\vdash c_{\sigma}=\phi_{\sigma}\left[\bar{*}\right]}
{\vdash c_{\tau}=\phi_{\tau}\left[\bar{*}\right]}
}
}
}
}
}
\]
In step 1, the previously established 
property $c_{\sigma} \leq c_{\tau}$ is used to create the 
(extended variant of the) type substitution 
map $\rho$ such that $\sigma = \rho \left( \tau \right)$ 
(see \cite{kuncar_types_2015}) and perform the type
substitution in $c_{\tau}=\phi_{\tau}\left[\bar{*}\right]$ 
to obtain $c_{\sigma}=\phi_{\sigma}\left[\bar{*}\right]$; 
in step 2, the collection of theorems $ud_{\mathsf{with}}$ is unfolded,
using it as a term rewriting system, possibly introducing further uninterpreted
constants $\bar{*'}$; in step 3, the term on the right-hand side of the
theorem is processed by removing the sort constraints from all type
variables that occur in it, replacing every uninterpreted constant-instance 
(this excludes all built-in constants of Isabelle/HOL) that occurs in it by a 
fresh term variable, and applying the abstraction until the resulting term 
is closed: this term forms the right-hand side of a new definitional axiom 
of a fresh constant $c_{\mathsf{with}}$ (if the conditions associated with 
the definitional principles of Isabelle/HOL \cite{yang_comprehending_2017} 
are satisfied); step 4 is justified by the beta-contraction; 
step 5 is a substitution of the uninterpreted constants $\bar{*} \cup \bar{*'}$;
step 6 follows trivially from the results of the application of steps 2 and 5.

The implementation of the command @{command ud} closely follows the steps of 
the algorithm outlined above. Thus, at the end of the successful
execution, the command declares the constant $c_{\mathsf{with}}$ and stores the 
constant-instance definition that is obtained at the end of step 3 of
the algorithm UD; furthermore, the command adds the theorem that is 
obtained after the execution of step 6 of the algorithm
to $ud_{\mathsf{with}}$.

Unlike the classical overloading elimination algorithm, 
the algorithm employed in the implementation
of the command @{command ud} is not recursive. Thus, the users are responsible 
for maintaining an adequate collection of theorems $ud_{\mathsf{with}}$. 
Nonetheless, in this case, the users can provide their own 
unoverloaded constants $c_{\mathsf{with}}$ and the associated theorems 
$c_{\sigma} = c_{\mathsf{with}}\ \bar{*}$ for any constant-instance $c_{\sigma}$. 
From the perspective of the relativization algorithm associated with
Types-To-Sets this can be useful because there is no 
guarantee that the automatically synthesized constants $c_{\mathsf{with}}$ 
will possess desirable parametricity characteristics
(e.g., see \cite{kuncar_types_2015} and \cite{immler_smooth_2019}).
Unfortunately, the implemented algorithm still suffers from the fundamental 
limitation that was already outlined in \cite{kaufmann_mechanized_2010}, 
\cite{blanchette_types_2016} and \cite{kuncar_types_2019}: 
it does not offer a solution for handling the 
constants whose types contain occurrences of the type constructors whose 
type definitions contain occurrences of unresolvable overloading.
\<close>



subsection\<open>Syntax\<close>

text\<open>
This subsection presents the syntactic categories that are associated with the 
command @{command ud}. It is important to note that the presentation is 
only approximate.
\<close>

text\<open>

\begin{matharray}{rcl}
  @{command_def "ud"} & : & \<open>theory \<rightarrow> theory\<close>\\
\end{matharray}

  \<^medskip>

  \<^rail>\<open>@@{command ud} binding? const mixfix?\<close>

  \<^descr> \<^theory_text>\<open>ud\<close> (\<open>b\<close>) \<open>const\<close> (\<open>mixfix\<close>) provides access to the algorithm for
the elimination of sort constraints and unoverloading of definitions
that was described in subsection \ref{sec:ud_theory}.
The optional binding \<open>b\<close> is used for the specification
of the names of the entities added by the command to the theory and the 
optional argument \<open>mixfix\<close> is used for the specification 
of the concrete inner syntax for the constant in the usual manner
(e.g., see \cite{wenzel_isabelle/isar_2019-1}). 
If either \<open>b\<close> or \<open>mixfix\<close> are not specified by the user, then the command
introduces sensible defaults. Following the specification of the 
definition of the constant, an additional theorem that establishes
the relationship between the newly introduced constant and the 
constant provided by the user as an input is established and added 
to the dynamic fact @{thm [source] ud_with}.
\<close>



subsection\<open>Examples\label{sec:ud_ex}\<close>

text\<open>
In this subsection, some of the capabilities of the UD are 
demonstrated by example. The examples that are presented in this subsection are 
expected to be sufficient for beginning an independent exploration of the 
framework, but do not cover the entire spectrum of the functionality 
and the problems that one may encounter while using it.
\<close>


subsubsection\<open>Type classes\<close>

text\<open>
We begin the exploration of the capabilities of the framework by considering
the constant @{const mono}.
The constant @{const mono} is an overloaded constant that is defined 
in the standard library of Isabelle/HOL \cite{noauthor_isabellehol_2020} as  
\begin{center}
@{thm [names_short = true] mono_def[no_vars]} 
\end{center}
for any @{term [show_sorts] "f::'a::order\<Rightarrow>'b::order"}.
Technically, there exist two distinct constants that are associated with
the definition of the constant @{const mono} 
(see, e.g., \cite{berardi_local_2009} 
for further details): @{const order.mono} that is provided by the 
Isabelle system automatically and the constant @{const mono} itself.
The constants are unoverloaded successively using the command @{command ud}:
\<close>
ud \<open>order.mono\<close>
ud mono' \<open>mono\<close>
text\<open>
The invocation of the commands above declares the constant @{const mono.with} 
that is defined as
\begin{center}
@{thm mono.with_def[no_vars]}
\end{center}
and provides the theorem @{thm [source] mono.with} given by
\begin{center}
@{thm mono.with[no_vars]}
\end{center}
and the theorem @{thm [source] mono'.with} given by
\begin{center}
@{thm mono'.with[no_vars]}.
\end{center}
The theorems establish the relationship between the unoverloaded constant
@{const mono.with} and the overloaded constant @{const mono}:
both theorems are automatically added to the dynamic fact 
@{thm [source] ud_with}.
\<close>


subsubsection\<open>Low-level overloading\<close>

text\<open>
The following example closely follows Example 5 in section 5.2. in 
\cite{kaufmann_mechanized_2010}. 
\<close>

consts pls :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

overloading
pls_nat \<equiv> "pls::nat \<Rightarrow> nat \<Rightarrow> nat"
pls_times \<equiv> "pls::'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b"
begin
definition pls_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where "pls_nat a b = a + b"
definition pls_times :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b" 
  where "pls_times \<equiv> \<lambda>x y. (pls (fst x) (fst y), pls (snd x) (snd y))"
end

ud pls_nat \<open>pls::nat \<Rightarrow> nat \<Rightarrow> nat\<close>
ud pls_times \<open>pls::'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close>

text\<open>
As expected, two new unoverloaded constants are produced via
the invocations of the command @{command ud} above. The first constant,
\<^const>\<open>pls_nat.with\<close>, corresponds to \<open>pls::nat \<Rightarrow> nat \<Rightarrow> nat\<close> and is given by
\begin{center}
@{thm pls_nat.with_def[no_vars]},
\end{center}
the second constant, \<^const>\<open>pls_times.with\<close>, corresponds to
\begin{center}
\<open>pls::'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'a \<times> 'b\<close> 
\end{center}
and is given by 
\begin{center}
@{thm pls_times.with_def[no_vars]}.
\end{center}
The theorems that establish the relationship between the overloaded and
the unoverloaded constants are given by 
\begin{center}
@{thm pls_nat.with} 
\end{center}
and 
\begin{center}
@{thm pls_times.with}.
\end{center}
The definitions of the constants \<^const>\<open>pls_nat.with\<close> and 
\<^const>\<open>pls_times.with\<close> are consistent with the ones suggested in
\cite{kaufmann_mechanized_2010}. Nonetheless, of course, it is
important to keep in mind that the command @{command ud}
has a more restricted scope of applicability than the
algorithm suggested in \cite{kaufmann_mechanized_2010}.
\<close>

text\<open>\newpage\<close>

end