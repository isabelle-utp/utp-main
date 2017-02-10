(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uvar.thy                                                             *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 18 Jan 2016 *)

section {* Variables *}

theory uvar
imports uattrib uconsts uname utype
begin

text {* We are going to use the colon for model typing. *}

no_notation
  Set.member ("op :") and
  Set.member ("(_/ : _)" [51, 51] 50)

default_sort typerep

text {* Avoids verbose printing of the prefix in @{text "'a uvar.var"}. *}

hide_type (open) var

subsection {* Monomorphic Variables *}

text {* Variables are encoded by records consisting of a name and type. *}

record uvar =
  name :: uname
  type :: utype

abbreviation UVAR :: "uvar set" where
"UVAR \<equiv> UNIV"

subsubsection {* Constructors *}

abbreviation MkVar :: "uname \<Rightarrow> utype \<Rightarrow> uvar" where
"MkVar n t \<equiv> \<lparr>name = n, type = t\<rparr>"

subsubsection {* Syntax *}

syntax "_MkVar" :: "id \<Rightarrow> type \<Rightarrow> uvar" ("$_:{_}\<^sub>u" [1000, 0] 1000)

translations "$n:{'a}\<^sub>u" \<rightleftharpoons> "(CONST MkVar) \<lfloor>n\<rfloor> UTYPE('a)"

subsubsection {* Typed Variables *}

definition typed_UVAR :: "'a itself \<Rightarrow> uvar set" where
[simp]: "typed_UVAR (t :: 'a itself) = {v. type v = UTYPE('a)}"

paragraph {* Syntax for sets of variables with a fixed type. *}

syntax "_UVAR" :: "type \<Rightarrow> uvar set" ("UVAR'(_')")

translations "UVAR('a)" \<rightleftharpoons> "(CONST typed_UVAR) TYPE('a)"

subsubsection {* Restrictions *}

definition UNDASHED_uvar :: "uvar set" where
[vars]: "UNDASHED_uvar = {v. name v \<in> UNDASHED}"

adhoc_overloading UNDASHED UNDASHED_uvar

definition DASHED_uvar :: "uvar set" where
[vars]: "DASHED_uvar = {v. name v \<in> DASHED}"

adhoc_overloading DASHED DASHED_uvar

subsubsection {* Operators *}

definition dash_uvar :: "uvar \<Rightarrow> uvar" where
[vars]: "dash_uvar = (name_update dash_uname)"

adhoc_overloading dash dash_uvar

definition undash_uvar :: "uvar \<Rightarrow> uvar" where
[vars]: "undash_uvar = (name_update undash_uname)"

adhoc_overloading undash undash_uvar

subsection {* Polymorphic Variables *}

typedef (overloaded) 'a var = "UVAR('a)"
apply (rule_tac x = "$x:{'a}\<^sub>u" in exI)
apply (simp)
done

lemmas Abs_var_inject_sym = sym [OF Abs_var_inject]
lemmas Rep_var_inject_sym = sym [OF Rep_var_inject]

text {* \fixme{Use the transfer tactic rather than default simplifications?} *}

declare Abs_var_inverse [simp, intro]
declare Rep_var_inverse [simp]
declare Abs_var_inject [simp, intro]
declare Rep_var_inject_sym [simp]

text {* \fixme{Is there a way to fix the warning about relators below?} *}

setup_lifting type_definition_var

subsubsection {* Constructors *}

lift_definition MkPVar :: "uname \<Rightarrow> 'a itself \<Rightarrow> 'a var"
is "\<lambda> (n :: uname) (t :: 'a itself). MkVar n UTYPE('a)"
apply (simp)
done

subsubsection {* Type Erasure and Coercion *}

text {* Intuitively, type erasure converts polymorphic into model variables. *}

notation Rep_var ("_\<down>" [1000] 1000)

text {* Type erasure may also be done implicitly by virtue of a coercion. *}

declare [[coercion Rep_var]]

declare MkPVar.rep_eq [simp]

subsubsection {* Syntax *}

text {*
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
*}

syntax "_MkPVar1" :: "id \<Rightarrow>         'a var" ("$_" [1000] 1000)
syntax "_MkPVar2" :: "id \<Rightarrow> type \<Rightarrow> 'a var" ("$_:{_}"  [1000, 0] 1000)
syntax "_MkPVar3" :: "id \<Rightarrow> type \<Rightarrow> 'a var" ("$_:{_}-" [1000, 0] 1000)

translations "$n" \<rightharpoonup> "(CONST MkPVar) \<lfloor>n\<rfloor> TERM_TYPE(n)"
translations "$n:{'a}" \<rightharpoonup> "(CONST MkPVar) \<lfloor>n\<rfloor> TERM_TYPE(n::'a)"
translations "$n:{'a}" \<leftharpoondown> "(CONST MkPVar) \<lfloor>n\<rfloor> TERM_TYPE(x::'a)"
translations "$n:{'a}-" \<rightleftharpoons> "(CONST MkPVar) \<lfloor>n\<rfloor> TYPE('a)"

paragraph {* Post-Processing *}

text {*
  As explained above, hidden HOL variables are injected when using the syntax
  @{term "$n:{'a}"}; this is purely for unification purposes. The option below
  controls whether they are replace by @{term "TYPE('a)"} constants during a
  custom post-processing rewrite step. Replacement is the default behaviour,
*}

ML {*
  val (remove_hidden_vars, remove_hidden_vars_setup) =
    Attrib.config_bool @{binding remove_hidden_vars} (K true);
*}

setup {* remove_hidden_vars_setup *}

text {* ML file that contains the code for the rewrite engine. *}

ML_file "uvar.ML"

text {* Configure the custom rewrite step as a term checker. *}

setup {*
  Context.theory_map (Syntax_Phases.term_check 3
    "remove hidden variables" Var_Rewriter.remove_hidden_vars_tr)
*}

subsubsection {* Restrictions *}

definition UNDASHED_var :: "'a var set" where
[vars]: "UNDASHED_var = {v::'a var. name v \<in> UNDASHED}"

adhoc_overloading UNDASHED UNDASHED_var

definition DASHED_var :: "'a var set" where
[vars]: "DASHED_var = {v::'a var. name v \<in> DASHED}"

adhoc_overloading DASHED DASHED_var

subsubsection {* Operators *}

definition dash_var :: "'a var \<Rightarrow> 'a var" where
[vars]: "dash_var v = MkPVar (name v)\<acute> TYPE('a)"

adhoc_overloading dash dash_var

definition undash_var :: "'a var \<Rightarrow> 'a var" where
[vars]: "undash_var v = MkPVar (name v)\<inverse> TYPE('a)"

adhoc_overloading undash undash_var

subsection {* Proof Support *}

text {*
  To facilitate proofs about variables, we configure tactics that automatically
  apply transfer laws for the types @{type var}, @{type uvar} and @{type uname}.
  While record-based types already generate the underlying splitting laws, for
  the @{type var} type being defined via a type definition, we make use of the
  utility theory @{theory Typedef_transfer} which generates those laws for us.
*}

subsubsection {* Transfer Laws *}

text {* Using a named attribute supports future extension. *}

named_theorems var_transfer "variable transfer"

lemmas var_typedef_transfer =
  type_definition.typedef_transfer [OF uvar.type_definition_var]

declare uname.uname.splits [var_transfer]
declare uvar.uvar.splits [var_transfer]
declare var_typedef_transfer [var_transfer]

subsubsection {* Proof Methods *}

text {* The below automates, in particular, laws about variable decorations. *}

method var_tac =
  (clarsimp simp add: var_transfer vars typing fun_eq_iff)

method var_auto = (var_tac; auto)
method var_blast = (var_tac; blast)

subsubsection {* Theorems *}

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

declare [[show_types]]

lemma dash_erasure_commutes:
"v\<acute>\<down> = v\<down>\<acute>"
-- {* How do we deal with free variables in the goal? *}
(* apply (var_tac) *)
apply (unfold vars)
apply (induct v)
apply (clarsimp)
done
end