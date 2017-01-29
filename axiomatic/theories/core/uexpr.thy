(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uexpr.thy                                                            *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 27 Jan 2017 *)

section {* Deep Expressions *}

theory uexpr
imports uvar ustate unrest_sf
begin

default_sort type

subsection {* Expression Type *}

text {*
  Expressions are modelled by a pair consisting of an alphabet and a function
  from (universal) states to values. The fact that expressions keep track of
  their alphabet facilitates proof tactics about (un)restriction of variables
  and furthermore enables us to instantiate the expression model, namely with
  type @{type bool} to obtain a suitable notion of alphabetised predicate. It
  would be nice to ensure that the alphabet is finite, however, this turns out
  to cause issues with the lifting functor for HOL binders such as @{const Ex}
  and @{const All}.
*}

text {*
  A major work to do is to make use of an abstract state type rather than the
  type @{type ustate} directly. In doing so, we shall only consider relational
  state spaces, since the UTP is effectively a relational calculus. Hence, our
  abstract state type may be @{typ"'\<sigma>\<^sub>1 \<times> '\<sigma>\<^sub>2"}; starting with relational as
  the ground-level predicate notion also allows us to unify the discrepancy of
  type between plain predicates and conditions in Isabelle/UTP. If we wanted
  to consider alphabetised predicates, we, however, would need to impose sort
  constraints @{text "'\<sigma>\<^sub>1::ust"} and @{text "'\<sigma>\<^sub>2::ust"}. This may be tricky in
  terms of the general Isabelle/UTP framework, as we do not like to upfront
  constrain the user to include the axiomatic value model. This is still an
  open problem, i.e. how can we encode the notion of alphabet more generally
  into Isabelle/UTP's expression model, talking advantage of the lens model.
*}

typedef 'a uexpr  =
  "{(a::uvar set, sf::ustate \<Rightarrow> 'a). (* finite a \<and> *) unrest_sf (UVAR - a) sf}"
apply (rule_tac x = "({}, (\<lambda>_. undefined))" in exI)
apply (clarsimp)
apply (rule unrest_sf_const)
done

text {* Nicely, predicates are just expressions instantiated as @{type bool}. *}

type_synonym upred = "bool uexpr"

text {* \fixme{Is there a way to fix the warning about relators below?} *}

setup_lifting type_definition_uexpr

subsection {* Alphabet and State Function *}

lift_definition alpha_uexpr :: "'a uexpr \<Rightarrow> uvar set" ("\<alpha>")
is "fst :: uvar set \<times> (ustate \<Rightarrow> 'a) \<Rightarrow> uvar set"
done

lift_definition sfun_uexpr :: "'a uexpr \<Rightarrow> (ustate \<Rightarrow> 'a)" ("\<lbrakk>_\<rbrakk>")
is "snd :: uvar set \<times> (ustate \<Rightarrow> 'a) \<Rightarrow> (ustate \<Rightarrow> 'a)"
done

subsection {* Unrestriction of Expressions *}

definition unrest :: "uvar set \<Rightarrow> 'a uexpr \<Rightarrow> bool" (infix "\<sharp>" 50) where
[transfer_unfold]: "unrest vs e = unrest_sf vs \<lbrakk>e\<rbrakk>"

theorem unrest_empty:
"{} \<sharp> e"
apply (transfer')
apply (rule unrest_sf_empty)
done

theorem unrest_subset:
"vs1 \<subseteq> vs2 \<Longrightarrow> vs2 \<sharp> e \<Longrightarrow> vs1 \<sharp> e"
apply (transfer')
apply (clarsimp)
apply (erule unrest_sf_subset)
apply (assumption)
done

theorem unrest_uexpr:
"-(\<alpha> e) \<sharp> e"
apply (transfer)
apply (clarsimp)
apply (unfold unrest_sf_def)
apply (clarsimp)
done

theorem unrestI [simp, intro]:
"vs \<inter> (\<alpha> e) = {} \<Longrightarrow> vs \<sharp> e"
apply (subgoal_tac "vs \<subseteq> -(\<alpha> e)")
apply (erule unrest_subset)
apply (rule unrest_uexpr)
apply (auto)
done

subsection {* Lifting Constructors *}

lift_definition lit_uexpr :: "'a \<Rightarrow> 'a uexpr"
is "\<lambda>c. ({}, (\<lambda>_. c))"
apply (clarsimp)
apply (rule unrest_sf_const)
done

notation (input) lit_uexpr ("\<guillemotleft>_\<guillemotright>") -- {* Do we really want this short-hand? *}

lift_definition uvar_uexpr :: "uvar \<Rightarrow> uval uexpr"
is "\<lambda>v. ({v}, (\<lambda>s. s\<cdot>v))"
apply (clarsimp)
apply (rule unrest_sf_uvar)
done

lift_definition var_uexpr :: "'a::injectable var \<Rightarrow> 'a uexpr"
is "\<lambda>v. ({v\<down>}, (\<lambda>s. s\<star>v))"
apply (clarsimp)
apply (rule unrest_sf_var)
done

lift_definition uop_uexpr :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a uexpr \<Rightarrow> 'b uexpr)"
is "\<lambda>f. \<lambda>(a, e). (a, (\<lambda>s. f (e s)))"
apply (clarsimp)
apply (unfold unrest_sf_def)
apply (clarsimp)
done

lift_definition bop_uexpr ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a uexpr \<Rightarrow> 'b uexpr \<Rightarrow> 'c uexpr)"
is "\<lambda>f. \<lambda>(a\<^sub>1, e\<^sub>1) (a\<^sub>2, e\<^sub>2). (a\<^sub>1 \<union> a\<^sub>2, (\<lambda>s. f (e\<^sub>1 s) (e\<^sub>2 s)))"
apply (clarsimp)
apply (unfold unrest_sf_def)
apply (clarsimp)
done

lift_definition trop_uexpr ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a uexpr \<Rightarrow> 'b uexpr \<Rightarrow> 'c uexpr \<Rightarrow> 'd uexpr)"
is "\<lambda>f. \<lambda>(a\<^sub>1, e\<^sub>1) (a\<^sub>2, e\<^sub>2) (a\<^sub>3, e\<^sub>3). (a\<^sub>1 \<union> a\<^sub>2 \<union> a\<^sub>3, (\<lambda>s. f (e\<^sub>1 s) (e\<^sub>2 s) (e\<^sub>3 s)))"
apply (clarsimp)
apply (unfold unrest_sf_def)
apply (clarsimp)
done

text {*
  Note that this lifting functor can only deal with simple unary binders of
  type @{typ "('a \<Rightarrow> 'b) \<Rightarrow> 'c"}. This applies to most Isabelle/HOL binders
  fortunately, including the various quantifiers. For instance, the functor
  @{const All} for @{term "\<forall>x. P x"} has type @{typ "('a \<Rightarrow> bool) \<Rightarrow> bool"}.
  Note that unfortunately we cannot prove closure of the lifting below if we
  insisted on alphabets being finite in the type definition of @{type uexpr}.
*}

lift_definition binder_uexpr ::
  "(('a \<Rightarrow> 'b) \<Rightarrow> 'c) \<Rightarrow> (('a uexpr \<Rightarrow> 'b uexpr) \<Rightarrow> 'c uexpr)"
is "\<lambda>bdr. \<lambda>f. ((\<Union>x. fst (f \<guillemotleft>x\<guillemotright>)), (\<lambda>s. bdr (\<lambda>x. (snd (f \<guillemotleft>x\<guillemotright>) s))))"
apply (rename_tac f g)
apply (atomize (full))
apply (clarsimp)
apply (unfold case_prod_unfold)
apply (unfold unrest_sf_def)
apply (clarsimp)
done

(* no_notation lit_uexpr ("\<guillemotleft>_\<guillemotright>") *)

text {* \todo{What about substitution?} *}

subsection {* Alphabet Theorems *}

lemma alpha_lit [alphas]:
"\<alpha> (lit_uexpr c) = {}"
apply (transfer')
apply (clarsimp)
done

lemma alpha_uvar [alphas]:
"\<alpha> (uvar_uexpr v) = {v}"
apply (transfer')
apply (clarsimp)
done

lemma alpha_var [alphas]:
"\<alpha> (var_uexpr v) = {v\<down>}"
apply (transfer')
apply (clarsimp)
done

lemma alpha_uop [alphas]:
"\<alpha> (uop_uexpr f e) = (\<alpha> e)"
apply (transfer')
apply (clarsimp)
done

lemma alpha_bop [alphas]:
"\<alpha> (bop_uexpr f e\<^sub>1 e\<^sub>2) = (\<alpha> e\<^sub>1) \<union> (\<alpha> e\<^sub>2)"
apply (transfer')
apply (clarsimp)
done

lemma alpha_trop [alphas]:
"\<alpha> (trop_uexpr f e\<^sub>1 e\<^sub>2 e\<^sub>3) = (\<alpha> e\<^sub>1) \<union> (\<alpha> e\<^sub>2) \<union> (\<alpha> e\<^sub>3)"
apply (transfer')
apply (clarsimp)
done

lemma alpha_binder [alphas]:
"\<alpha> (binder_uexpr b f) = (\<Union>x. \<alpha> (f \<guillemotleft>x\<guillemotright>))"
apply (transfer')
apply (clarsimp)
done

subsection {* Transfer Tactic *}

named_theorems uexpr_transfer "uexpr transfer theorems"

theorem uexpr_eq [uexpr_transfer]:
"e1 = e2 \<longleftrightarrow> (\<alpha> e1 = \<alpha> e2) \<and> (\<forall>s. \<lbrakk>e1\<rbrakk> s = \<lbrakk>e2\<rbrakk> s)"
apply (transfer')
apply (fold fun_eq_iff)
apply (clarsimp)
done

lemma sfun_lit [uexpr_transfer]:
"\<lbrakk>lit_uexpr c\<rbrakk> = (\<lambda>s. c)"
apply (transfer')
apply (clarsimp)
done

lemma sfun_uvar [uexpr_transfer]:
"\<lbrakk>uvar_uexpr v\<rbrakk> = (\<lambda>s. s\<cdot>v)"
apply (transfer')
apply (clarsimp)
done

lemma sfun_var [uexpr_transfer]:
"\<lbrakk>var_uexpr v\<rbrakk> = (\<lambda>s. s\<star>v)"
apply (transfer')
apply (transfer')
apply (clarsimp)
done

lemma sfun_uop [uexpr_transfer]:
"\<lbrakk>uop_uexpr f e\<rbrakk> = (\<lambda>s. f (\<lbrakk>e\<rbrakk> s))"
apply (transfer')
apply (clarsimp)
done

lemma sfun_bop [uexpr_transfer]:
"\<lbrakk>bop_uexpr f e1 e2\<rbrakk> = (\<lambda>s. f (\<lbrakk>e1\<rbrakk> s) (\<lbrakk>e2\<rbrakk> s))"
apply (transfer')
apply (clarsimp)
done

lemma sfun_trop [uexpr_transfer]:
"\<lbrakk>trop_uexpr f e1 e2 e3\<rbrakk> = (\<lambda>s. f (\<lbrakk>e1\<rbrakk> s) (\<lbrakk>e2\<rbrakk> s) (\<lbrakk>e3\<rbrakk> s))"
apply (transfer')
apply (clarsimp)
done

lemma sfun_binder [uexpr_transfer]:
"\<lbrakk>binder_uexpr f e\<rbrakk> = (\<lambda>s. f (\<lambda>x. \<lbrakk>e \<guillemotleft>x\<guillemotright>\<rbrakk> s))"
apply (transfer')
apply (clarsimp)
done

method uexpr_transfer =
  (unfold uexpr_transfer, simp add: alphas)

method uexpr_tac =
  (uexpr_transfer, (ustate_transfer)?)

method uexpr_auto =
  (uexpr_transfer, (ustate_transfer)?; auto)

method uexpr_blast =
  (uexpr_transfer, (ustate_transfer)?; blast)

subsection {* Expression Parser *}

text {*
  We define a constant to tag terms to be processed by the parser. Note that
  this processing is done by a term-checker (rewrite engine) and takes place
  \emph{after} the term has been parsed and type-checked by Isabelle/HOL.
  This means that typing information is available in the term to be parsed,
  which allows us to suitably lift the various operators and free variables.
*}

consts uparse :: "'a \<Rightarrow> 'a uexpr" ("'(_')\<^sub>u")

text {* The following enables us to protect inner terms from processing. *}

consts uprotect :: "'a uexpr \<Rightarrow> 'a" ("@'(_')")

subsection {* Configuration of the expression parser and pretty-Printer *}

ML_file "uexpr.ML"

setup {*
  Context.theory_map (
    (Syntax_Phases.term_check 2 "ulift parser" Expr_Parser.uparse_tr))
*}

paragraph {* Parsing Experiments *}

text {*
  The below fails because the type @{typ 'a} of the variables @{term x} and
  @{term x'} is not injectable. An improvement to the expression parser may
  be to automatically introduce a sort constraint on type variables. This is
  still a pending work to do but should not be incredibly difficult. Likewise
  the expression parser does not support implicit typing of variables yet.
*}

-- {* @{text "(x' = x + 1)\<^sub>u"} *}

term "(\<lambda>x::nat. x + 1 = 2)\<^sub>u"

text {* As can be seen, lambda expressions and binders are well supported. *}

term "(\<lambda>x::nat. x + 1 = 2)\<^sub>u"
term "\<lambda>x::nat. (x + 1 = 2)\<^sub>u"
term "(\<forall>x::nat. x + y = 1)\<^sub>u"

subsection {* Predicate Parser *}

text {*
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
*}

consts SkipR :: "upred" -- {* Used for testing! *}
consts SemiR :: "upred \<Rightarrow> upred \<Rightarrow> upred"

nonterminal uterm

definition uterm :: "upred \<Rightarrow> upred" where
"uterm = id" -- {* Used to tag a parsed predicate. *}

declare uterm_def [uexpr_transfer]

syntax "_uterm" :: "uterm \<Rightarrow> bool uexpr" ("`_`")
syntax "_ulift" :: "logic \<Rightarrow> uterm" ("_")
syntax "_uskip" :: "uterm" ("II")
syntax "_usemi" :: "uterm \<Rightarrow> uterm \<Rightarrow> uterm" (infixl ";" 100)
(* ...the grammar can be dynamically extended in sub-theories. *)

translations "_uterm p" \<rightleftharpoons> "(CONST uterm) p"
translations "_ulift t" \<rightharpoonup> "(CONST uparse) t"
translations "_uskip" \<rightleftharpoons> "(CONST SkipR)"
translations "_usemi p q" \<rightleftharpoons> "(CONST SemiR) p q"

term "`x' = x + (1::nat); y = x; @(P); II`"

subsection {* Proof Experiments *}

text {* We can prove equivalence laws with expression and state transfer. *}

theorem "(\<forall>x::nat. y < x + 1)\<^sub>u = (y = 0)\<^sub>u"
apply (uexpr_transfer)
-- {* Make @{text ustate_transfer} keep the original variables names! *}
apply (ustate_transfer)
apply (auto)
done

theorem
fixes x :: "nat"
shows "(x + 1)\<^sub>u = (1 + x)\<^sub>u"
apply (uexpr_transfer)
done

theorem
fixes x :: "nat"
shows "{$y\<down>} \<sharp> (x + 1)\<^sub>u"
apply (rule unrestI)
apply (simp add: alphas)
done
end