(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uexpr.thy                                                            *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 14 Feb 2017 *)

section \<open>Generic Expressions\<close>

theory uexpr
imports uvar ustate ustore ulens
keywords "declare_uvar" :: thy_decl
begin

default_sort type

subsection \<open>Expression Type\<close>

text \<open>
  Expressions are modelled by functions from states to HOL values. We make no
  assumptions about the state here, although operators may impose additional
  sort constraints on the state type such as membership to class @{class ust}.
  We note that if we \emph{did} require that the state types of expressions are
  always a member of class @{class ust}, there is actually the possibility of
  recording an alphabet i.e.~of axiomatic variables for the expression. This,
  however, turns out to require a notion of \emph{partial} lenses, because we
  would need to define monomorphic versions of the axiomatic variable lenses.
  Such is needed to formulate the unrestriction property of the state function.
  (Simon Foster is currently working on the integration of partial lenses.)
\<close>

typedef ('a, '\<sigma>(*::ust*)) expr = "UNIV::('\<sigma> \<Rightarrow> 'a) set"
apply (rule UNIV_witness)
done

notation Rep_expr ("\<lbrakk>_\<rbrakk>")

text \<open>
  The notation @{text "'a expr['\<sigma>]"} is introduced as a syntactic sugar for
  @{text "('a, '\<sigma>) expr"}. Moreover @{text "'a uexpr"} is synonymous for the
  type @{text "'a expr[ustate]"}.
\<close>

type_notation expr ("_ expr[_]" [1000, 0] 1000)

syntax "_uexpr" :: "type \<Rightarrow> type" ("_ uexpr" [1000] 1000)

translations (type) "'a uexpr" \<rightleftharpoons> (type) "'a expr[ustate]"

subsection \<open>Predicate Type\<close>

text \<open>Predicates are expressions instantiated with type @{type bool}.\<close>

syntax "_pred" :: "type \<Rightarrow> type" ("pred[_]")

translations (type) "pred['\<sigma>]" \<rightleftharpoons> (type) "bool expr['\<sigma>]"

syntax "_upred" :: "type" ("upred")

translations (type) "upred" \<rightleftharpoons> (type) "pred[ustate]"

subsection \<open>Lifted Constructors\<close>

setup_lifting type_definition_expr

lift_definition lit_expr :: "'a \<Rightarrow> 'a expr['\<sigma>]" ("\<guillemotleft>_\<guillemotright>")
is "\<lambda>c. (\<lambda>_. c)"
done

lift_definition var_expr :: "'a::injectable var \<Rightarrow> 'a uexpr"
is "\<lambda>v. (\<lambda>s. s\<star>v)"
done

lift_definition avar_expr :: "'a::injectable var \<Rightarrow> 'a expr['\<sigma>::ust]"
is "\<lambda>v. get\<^bsub>avar_ust\<^sub>L v\<^esub>"
done

lift_definition uop_expr ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('a expr['\<sigma>] \<Rightarrow> 'b expr['\<sigma>])"
is "\<lambda>f. \<lambda>e. (\<lambda>s. f (e s))"
done

lift_definition bop_expr ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a expr['\<sigma>] \<Rightarrow> 'b expr['\<sigma>] \<Rightarrow> 'c expr['\<sigma>])"
is "\<lambda>f. \<lambda>e\<^sub>1 e\<^sub>2. (\<lambda>s. f (e\<^sub>1 s) (e\<^sub>2 s))"
done

lift_definition trop_expr ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow>
    ('a expr['\<sigma>] \<Rightarrow> 'b expr['\<sigma>] \<Rightarrow> 'c expr['\<sigma>] \<Rightarrow> 'd expr['\<sigma>])"
is "\<lambda>f. \<lambda>e\<^sub>1 e\<^sub>2 e\<^sub>3. (\<lambda>s. f (e\<^sub>1 s) (e\<^sub>2 s) (e\<^sub>3 s))"
done

text \<open>
  The binding lifting functor can only deal with simple unary binders i.e.~of
  type @{typ "('a \<Rightarrow> 'b) \<Rightarrow> 'c"}. Fortunately, most Isabelle/HOL binders fall
  into that category, including various types of quantifiers. For instance, the
  functor @{const All}, being used in terms of the form @{term "\<forall>x. P x"}, has
  the type @{typ "('a \<Rightarrow> bool) \<Rightarrow> bool"}. Supporting potential other binders
  is an issue for future work.
\<close>

lift_definition binder_expr ::
  "(('a \<Rightarrow> 'b) \<Rightarrow> 'c) \<Rightarrow> (('a expr['\<sigma>] \<Rightarrow> 'b expr['\<sigma>]) \<Rightarrow> 'c expr['\<sigma>])"
is "\<lambda>bdr. \<lambda>f. (\<lambda>s. bdr (\<lambda>x. (f \<guillemotleft>x\<guillemotright> s)))"
done

text \<open>\todo{What about substitution?}\<close>

subsection \<open>Meta-logical Operators\<close>

definition taut :: "pred['\<sigma>] \<Rightarrow> bool" where
[transfer_unfold]: "taut e = (\<forall>s. \<lbrakk>e\<rbrakk> s)"

subsection \<open>Transfer Tactic\<close>

named_theorems expr_transfer "expr transfer theorems"

theorem expr_eq [expr_transfer]:
"e1 = e2 \<longleftrightarrow> (\<forall>s. \<lbrakk>e1\<rbrakk> s = \<lbrakk>e2\<rbrakk> s)"
apply (transfer')
apply (fold fun_eq_iff)
apply (rule refl)
done

declare lit_expr.rep_eq [expr_transfer]
declare var_expr.rep_eq [expr_transfer]
declare avar_expr.rep_eq [expr_transfer]
declare uop_expr.rep_eq [expr_transfer]
declare bop_expr.rep_eq [expr_transfer]
declare trop_expr.rep_eq [expr_transfer]
declare binder_expr.rep_eq [expr_transfer]

declare taut_def [expr_transfer]

method expr_transfer =
  (unfold expr_transfer)

method expr_simp =
  (expr_transfer, (* (ustate_transfer)?; *) simp?)

method expr_auto =
  (expr_transfer, (* (ustate_transfer)?; *) auto)

method expr_blast =
  (expr_transfer, (* (ustate_transfer)?; *) blast)

subsection \<open>Expression Parser\<close>

text \<open>
  We define a constant to tag terms to be processed by the parser. Note that
  this processing is done by a term-checker (rewrite step), and takes place
  after the term has already been parsed and type-checked by Isabelle/HOL.
  Hence typing information is readily available during the rewrite step and
  this allows us to correctly lift the various operators and free variables.
  (An solution using a syntax translations would need to look at the theory
  context to infer the types of literal constants and operators.)
\<close>

consts uparse :: "'a \<Rightarrow> 'a expr['\<sigma>]" ("'(_')\<^sub>u")

text \<open>The following tag protect inner terms from processing.\<close>

consts uprotect :: "'a expr['\<sigma>] \<Rightarrow> 'a" ("@'(_')")

text \<open>Configuration of the lifting parser and pretty-printer.\<close>

ML_file "uexpr.ML"

setup \<open>
  Context.theory_map (
    (Syntax_Phases.term_check 2 "ulift parser" Expr_Parser.uparse_tr))
\<close>

subsection \<open>Automatic Typing\<close>

text \<open>
  We lastly configure a convenience mechanism for automatic typing of free
  variables inside @{text "(_)\<^sub>u"} terms. Free variables without an explicit
  type constrain are thus automatically typed according to their `declared
  type' via the command @{command declare_uvar}. Or otherwise, if no type
  was declared for the variable name, any free type of a free variable is
  at least forced to be injectable. The mechanism is useful, for instance,
  to predetermine the types of auxiliary variables of a UTP theory. It also
  reduces the need for explicit typing e.g.~of terms like @{text "(x + 1)\<^sub>u"}.
\<close>

text \<open>
  We add an outer command to declare the type of lifted HOL variables. The
  command takes a variable name and a HOL type. For example, we may declare
  the type of HOL variable @{term ok} to be @{typ bool} using the following
  command invocation: @{text "declare_uvar ok \"bool\""}. As hinted above,
  this affects the way the parser performs its translation and lifting.
\<close>

ML \<open>
  Outer_Syntax.local_theory @{command_keyword "declare_uvar"} "declare uvar"
    (Parse.const_decl >>
      (fn (uvar, typ, _) => UVAR_Typing.mk_uvar_type_synonym uvar typ));
\<close>

text \<open>Automatic typing is achieved by the following syntax translation.\<close>

parse_translation \<open>
  [(@{const_syntax "uparse"}, UVAR_Typing.uvar_implicit_typing_tr)]
\<close>

subsection \<open>Expression Cartouche\<close>

text \<open>
  We additionally embed the expression parser into a cartouche. With this, we
  can use the syntax @{text "\<open>\<dots>\<close>"} synonymously for @{text "(\<dots>)\<^sub>u"}. There is
  a slight difference between these uses though, as with the cartouche we do
  not get unification of lifted variables beyond the inside of @{text "\<open>\<dots>\<close>"}.
  This is due to having to parse the content of the cartouche in isolation and
  not in the context of the entire HOL term. This perhaps makes the cartouche
  less attractive, although sometimes there may be benefit in taming the scope
  of unification.
\<close>

syntax "_expr_cartouche" :: "cartouche_position \<Rightarrow> 'a expr['\<sigma>]" ("_\<^sub>e")

parse_translation \<open>
  [(@{syntax_const "_expr_cartouche"}, Expr_Cartouche.uexpr_cartouche_tr)]
\<close>

declare [[show_types]]

text \<open>Observe the difference in the type of @{term f}.\<close>

term "taut (x = (1::nat) \<and> y = x + 1 \<longrightarrow> y = 2)\<^sub>u \<and> (f x)"
term "taut \<open>x = (1::nat) \<and> y = x + 1 \<longrightarrow> y = 2\<close>\<^sub>e \<and> (f x)"

declare [[show_types = false]]

theorem "taut \<open>x = 1 \<and> y = x + 1 \<longrightarrow> y = 2\<close>\<^sub>e"
apply (unfold expr_transfer)
apply (clarsimp)
done

theorem "taut \<open>ok \<and> x = 1 \<longrightarrow> ok' \<and> x' = 2\<close>\<^sub>e"
apply (expr_transfer)
(* Can we do something else transfer-wise here? *)
(* apply (ustate_transfer) *)
\<comment> \<open>TODO: Implement a conversion that carries out a renaming.\<close>
oops

subsection \<open>Parsing Tests\<close>

inject_type "fun"
inject_type set
inject_type list

text \<open>Automatic typing seems to work well in various scenarios.\<close>

declare [[show_types]]
declare [[show_sorts]]

term "(x)\<^sub>u"
term "(x::'a)\<^sub>u"
term "(x::nat)\<^sub>u"
(* term "(x::'a::zero)\<^sub>u" *)
term "(x::'a::{zero,injectable})\<^sub>u"
term "(x + 1)\<^sub>u"
term "(x = {})\<^sub>u"
term "(\<lambda>x. x + 1)\<^sub>u"
term "\<lambda>x. (x + 1)\<^sub>u"

(* declare [[show_types]] *)
(* declare [[show_sorts]] *)

declare_uvar ok :: "bool"
declare_uvar tr :: "'\<tau> list"
(* declare_ulens ok = "ok\<^sub>L" *)

term "(ok)\<^sub>u"
term "(tr)\<^sub>u"
term "(tr = [] \<and> x = 1)\<^sub>u"
term "(P \<and> ok \<longrightarrow> Q \<and> ok')\<^sub>u"

declare [[show_types=false]]
declare [[show_sorts=false]]

text \<open>Lambda expressions and binders are properly lifted too.\<close>

term "(x + 1)\<^sub>u"

term "(\<lambda>x::nat. x + 1 = 2)\<^sub>u"
term "\<lambda>x::nat. (x + 1 = 2)\<^sub>u"
term "(\<forall>x::nat. x + y = 1)\<^sub>u"

subsection \<open>Predicate Parser\<close>

text \<open>
  The expression parser exclusively deals with the lifting of HOL terms. We
  require further machinery to support the parsing of UTP predicates that may
  mix HOL and UTP operators. This is implemented at the level of syntax and
  translations rather than rewriting.

  There may in fact be an alternative solution that harnesses rewriting too,
  defining uninterpreted constants that act as tags for the rewriting engine
  to convert them into corresponding UTP operators. A downside then is that
  we lose information about state spaces, as the parsing of lift expressions
  only considers the underlying HOL types of the expression. Hence we cannot
  exploit unification of the state spaces in that setting easily.
\<close>

consts SkipR :: "pred['\<sigma>]" \<comment> \<open>Used for testing\<close>
consts SemiR :: "pred['\<sigma>\<^sub>1] \<Rightarrow> pred['\<sigma>\<^sub>2] \<Rightarrow> pred['\<sigma>\<^sub>3]"

nonterminal uterm

definition uterm :: "pred['\<sigma>] \<Rightarrow> pred['\<sigma>]" where
"uterm = id" \<comment> \<open>Used to tag a parsed predicate.\<close>

declare uterm_def [expr_transfer]

syntax "_uterm" :: "uterm \<Rightarrow> pred['\<sigma>]" ("`_`")
syntax "_ulift" :: "logic \<Rightarrow> uterm" ("_")
syntax "_uskip" :: "uterm" ("II")
syntax "_usemi" :: "uterm \<Rightarrow> uterm \<Rightarrow> uterm" (infixl ";" 100)
(* ...the grammar can be dynamically extended in sub-theories. *)

translations "_uterm p" \<rightleftharpoons> "(CONST uterm) p"
translations "_ulift t" \<rightharpoonup> "(CONST uparse) t"
translations "_uskip" \<rightleftharpoons> "(CONST SkipR)"
translations "_usemi p q" \<rightleftharpoons> "(CONST SemiR) p q"

term "`x' = x + (1::nat); y = x; @(P); II`"

subsection \<open>Proof Experiments\<close>

text \<open>We can prove equivalence laws with expression and state transfer.\<close>

theorem "(\<forall>x. y < x + 1)\<^sub>u = (y = (0::nat))\<^sub>u"
apply (expr_transfer)
\<comment> \<open>TODO: Let @{text ustate_transfer} retain the original variables names.\<close>
(* apply (ustate_transfer) *)
apply (auto)
done

theorem "(x + (1::nat))\<^sub>u = (1 + x)\<^sub>u"
apply (expr_transfer)
apply (simp)
done
end