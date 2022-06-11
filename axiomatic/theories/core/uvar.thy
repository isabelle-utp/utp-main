(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uvar.thy                                                             *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Variables\<close>

theory uvar
imports uattrib uconsts uname utype
begin

text \<open>We are going to use the colon for model typing.\<close>

no_notation (ASCII)
  Set.member  ("'(:')") and
  Set.member  ("(_/ : _)" [51, 51] 50)

text \<open>We are going to use the converse symbol for undashing.\<close>

no_notation
  converse  ("(_\<inverse>)" [1000] 999)

default_sort typerep

text \<open>Avoids verbose printing of the prefix in @{text "'a uvar.var"}.\<close>

hide_type (open) var

subsection \<open>Monomorphic Variables\<close>

text \<open>Variables are encoded by records consisting of a name and type.\<close>

record uvar =
  name :: uname
  type :: utype

abbreviation UVAR :: "uvar set" where
"UVAR \<equiv> UNIV"

subsubsection \<open>Constructors\<close>

abbreviation MkVar :: "uname \<Rightarrow> utype \<Rightarrow> uvar" where
"MkVar n t \<equiv> \<lparr>name = n, type = t\<rparr>"

subsubsection \<open>Syntax\<close>

syntax "_MkVar" :: "id \<Rightarrow> type \<Rightarrow> uvar" ("$_:{_}\<^sub>u" [1000, 0] 1000)

translations "$n:{'a}\<^sub>u" \<rightleftharpoons> "(CONST MkVar) \<lfloor>n\<rfloor> UTYPE('a)"

subsubsection \<open>Typed Variables\<close>

definition typed_UVAR :: "'a itself \<Rightarrow> uvar set" where
[simp]: "typed_UVAR (t :: 'a itself) = {v. type v = UTYPE('a)}"

paragraph \<open>Syntax for sets of variables with a fixed type.\<close>

syntax "_UVAR" :: "type \<Rightarrow> uvar set" ("UVAR'(_')")

translations "UVAR('a)" \<rightleftharpoons> "(CONST typed_UVAR) TYPE('a)"

subsubsection \<open>Restrictions\<close>

definition UNDASHED_uvar :: "uvar set" where
[vars]: "UNDASHED_uvar = {v. name v \<in> UNDASHED}"

adhoc_overloading UNDASHED UNDASHED_uvar

definition DASHED_uvar :: "uvar set" where
[vars]: "DASHED_uvar = {v. name v \<in> DASHED}"

adhoc_overloading DASHED DASHED_uvar

subsubsection \<open>Operators\<close>

definition dash_uvar :: "uvar \<Rightarrow> uvar" where
[vars]: "dash_uvar = (name_update dash_uname)"

adhoc_overloading dash dash_uvar

definition undash_uvar :: "uvar \<Rightarrow> uvar" where
[vars]: "undash_uvar = (name_update undash_uname)"

adhoc_overloading undash undash_uvar

subsection \<open>Polymorphic Variables\<close>

typedef (overloaded) 'a var = "UVAR('a)"
apply (rule_tac x = "$x:{'a}\<^sub>u" in exI)
apply (simp)
done

lemmas Abs_var_inject_sym = sym [OF Abs_var_inject]
lemmas Rep_var_inject_sym = sym [OF Rep_var_inject]

text \<open>\fixme{Use the transfer tactic rather than default simplifications?}\<close>

declare Abs_var_inverse [simp, intro]
declare Rep_var_inverse [simp]
declare Abs_var_inject [simp, intro]
declare Rep_var_inject_sym [simp]

text \<open>\fixme{Is there a way to fix the warning about relators below?}\<close>

setup_lifting type_definition_var

subsubsection \<open>Constructors\<close>

lift_definition MkPVar :: "uname \<Rightarrow> 'a itself \<Rightarrow> 'a var"
is "\<lambda> (n :: uname) (t :: 'a itself). MkVar n UTYPE('a)"
apply (simp)
done

subsubsection \<open>Type Erasure and Coercion\<close>

text \<open>Intuitively, type erasure converts polymorphic into model variables.\<close>

notation Rep_var ("_\<down>" [1000] 1000)

text \<open>Type erasure may also be done implicitly by virtue of a coercion.\<close>

declare [[coercion Rep_var]]

declare MkPVar.rep_eq [simp]

subsubsection \<open>Syntax\<close>

text \<open>
  We introduce two notations that subtly differ in terms of their underlying
  encoding. The first one @{text "$n:{'a}"} introduces a hidden free variable
  with the same name as @{text n}. This is useful to harvest HOL type-checking
  in order to type-check polymorphic variables. It also causes unification of
  explicitly written variables and variables introduced implicitly by the HOL
  lifting parser (the latter being defined in the theory @{text ulift}).

  The second notation @{text "$n:{'a}\<hyphen>"}, in contrast, does not introduce a
  free variable but uses a @{term "TYPE('a)"} constant in place of it. This
  is useful in definitions as Isabelle will grumbles about free variables in
  the RHS of a definition.

  To reap the benefit of both approaches, we provide a custom rewrite engine
  that automatically rewrites @{text "$n:{'a}"} terms into @{text "$n:{'a}\<hyphen>"}
  \emph{after} type-checking has taken place. This engine can be disabled but
  usually there is no need for hidden HOL variables to be retained after type
  unification. The notation @{text "$n"} introduces a fresh type variable that
  becomes subject to unification, too.
\<close>

syntax "_MkPVar1" :: "id \<Rightarrow>         'a var" ("$_" [1000] 1000)
syntax "_MkPVar2" :: "id \<Rightarrow> type \<Rightarrow> 'a var" ("$_:{_}"  [1000, 0] 1000)
syntax "_MkPVar3" :: "id \<Rightarrow> type \<Rightarrow> 'a var" ("$_:{_}-" [1000, 0] 1000)

translations "$n" \<rightharpoonup> "(CONST MkPVar) \<lfloor>n\<rfloor> TERM_TYPE(n)"
translations "$n:{'a}" \<rightharpoonup> "(CONST MkPVar) \<lfloor>n\<rfloor> TERM_TYPE(n::'a)"
translations "$n:{'a}" \<leftharpoondown> "(CONST MkPVar) \<lfloor>n\<rfloor> TERM_TYPE(x::'a)"
translations "$n:{'a}-" \<rightleftharpoons> "(CONST MkPVar) \<lfloor>n\<rfloor> TYPE('a)"

paragraph \<open>Post-Processing\<close>

text \<open>
  As explained above, hidden HOL variables are injected when using the syntax
  @{term "$n:{'a}"}; this is purely for unification purposes. The option below
  controls whether they are replace by @{term "TYPE('a)"} constants during a
  custom post-processing rewrite step. Replacement is the default behaviour,
\<close>

ML \<open>
  val (remove_hidden_vars, remove_hidden_vars_setup) =
    Attrib.config_bool @{binding remove_hidden_vars} (K true);
\<close>

setup \<open>remove_hidden_vars_setup\<close>

text \<open>ML file that contains the code for the rewrite engine.\<close>

ML_file "uvar.ML"

text \<open>Configure the custom rewrite step as a term checker.\<close>

setup \<open>
  Context.theory_map (Syntax_Phases.term_check 3
    "remove hidden variables" Var_Rewriter.remove_hidden_vars_tr)
\<close>

subsubsection \<open>Restrictions\<close>

definition UNDASHED_var :: "'a var set" where
[vars]: "UNDASHED_var = {v::'a var. name v \<in> UNDASHED}"

adhoc_overloading UNDASHED UNDASHED_var

definition DASHED_var :: "'a var set" where
[vars]: "DASHED_var = {v::'a var. name v \<in> DASHED}"

adhoc_overloading DASHED DASHED_var

subsubsection \<open>Operators\<close>

definition dash_var :: "'a var \<Rightarrow> 'a var" where
[vars]: "dash_var v = MkPVar (name v)\<acute> TYPE('a)"

adhoc_overloading dash dash_var

definition undash_var :: "'a var \<Rightarrow> 'a var" where
[vars]: "undash_var v = MkPVar (name v)\<inverse> TYPE('a)"

adhoc_overloading undash undash_var

subsection \<open>Proof Support\<close>

text \<open>
  To facilitate proofs about variables, we configure tactics that automatically
  apply transfer laws for the types @{type var}, @{type uvar} and @{type uname}.
  While record-based types already generate the underlying splitting laws, for
  the @{type var} type being defined via a type definition, we make use of the
  utility theory @{text Typedef_extra} which generates those laws for us.
\<close>

subsubsection \<open>Transfer Laws\<close>

text \<open>Using a named attribute supports future extension.\<close>

named_theorems var_transfer "variable transfer"

lemmas var_typedef_transfer =
  type_definition.transfer [OF uvar.type_definition_var]

declare uname.uname.splits [var_transfer]
declare uvar.uvar.splits [var_transfer]
declare var_typedef_transfer [var_transfer]

subsubsection \<open>Proof Methods\<close>

text \<open>The below automates, in particular, laws about variable decorations.\<close>

method var_tac = (clarsimp simp add: var_transfer vars typing fun_eq_iff)
method var_auto = (var_tac; auto)
method var_blast = (var_tac; blast)

subsubsection \<open>Theorems\<close>

lemma p_type_of_Rep_var [simp]:
fixes x :: "'a"
fixes v :: "'a var"
shows "x : (type v\<down>)"
apply (transfer)
apply (simp add: typing)
done

lemma undash_uvar_inv [simp]:
"(v::uvar) \<in> DASHED \<Longrightarrow> v\<inverse>\<acute> = v"
apply (var_tac)
done

lemma dash_uvar_inv [simp]:
"(v::uvar) \<in> UNDASHED \<Longrightarrow> v\<acute>\<inverse> = v"
apply (var_tac)
done

lemma dash_erasure_commutes:
"v\<acute>\<down> = v\<down>\<acute>"
apply (unfold vars)
apply (induct v)
apply (clarsimp)
done
end