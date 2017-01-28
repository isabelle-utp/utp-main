(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uparser.thy                                                          *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 26 Jan 2017 *)

section {* Predicate Parser *}

theory uparser
imports upred ulift urel
begin

text {* The predicate parser may still require a bit more work and polishing. *}

subsection {* Parser Syntax *}

nonterminal uterm

syntax "_uterm" :: "uterm \<Rightarrow> upred" ("`_`")
syntax "_upred" :: "upred \<Rightarrow> uterm" ("{_}")
syntax "_ulift" :: "term \<Rightarrow> uterm" ("_")
syntax "_utrue" :: "uterm" ("true")
syntax "_ufalse" :: "uterm" ("false")
syntax "_uconj" :: "uterm \<Rightarrow> uterm \<Rightarrow> uterm" (infixr "\<and>" 35)
syntax "_udisj" :: "uterm \<Rightarrow> uterm \<Rightarrow> uterm" (infixr "\<or>" 30)
syntax "_uimp" :: "uterm \<Rightarrow> uterm \<Rightarrow> uterm" (infixr "\<Rightarrow>" 25)
syntax "_uiff" :: "uterm \<Rightarrow> uterm \<Rightarrow> uterm" (infixr "\<Leftrightarrow>" 25)
syntax "_uforall" :: "uvar set \<Rightarrow> uterm \<Rightarrow> uterm" ("(\<forall> _ ./ _)" [0, 100] 100)
syntax "_uexists" :: "uvar set \<Rightarrow> uterm \<Rightarrow> uterm" ("(\<exists> _ ./ _)" [0, 100] 100)
syntax "_uskip" :: "uterm" ("II")
syntax "_usemi" :: "uterm \<Rightarrow> uterm \<Rightarrow> uterm" (infixr ";" 20)
syntax "_ubracket" :: "uterm \<Rightarrow> uterm" ("'(_')")

subsection {* Translations *}

translations "_uterm p" \<rightharpoonup> "p"
translations "_upred p" \<rightharpoonup> "(p::upred)"
translations "_ulift t" \<rightharpoonup> "(CONST ulift) t"
translations "_utrue" \<rightharpoonup> "true\<^sub>p"
translations "_ufalse" \<rightharpoonup> "false\<^sub>p"
translations "_uconj p1 p2" \<rightharpoonup> "p1 \<and>\<^sub>p p2"
translations "_udisj p1 p2" \<rightharpoonup> "p1 \<or>\<^sub>p p2"
translations "_uimp p1 p2" \<rightharpoonup> "p1 \<Rightarrow>\<^sub>p p2"
translations "_uiff p1 p2" \<rightharpoonup> "p1 \<Leftrightarrow>\<^sub>p p2"
translations "_uforall vs p" \<rightharpoonup> "\<forall>\<^sub>p vs. p"
translations "_uexists vs p" \<rightharpoonup> "\<exists>\<^sub>p vs. p"
translations "_uskip" \<rightharpoonup> "II\<^sub>p"
translations "_usemi p1 p2" \<rightharpoonup> "p1 ;\<^sub>p p2"
translations "_ubracket t" \<rightharpoonup> "t"

subsection {* Disambiguation *}

text {*
  There is a need to resolve ambiguities that arise from parsing terms such as
  @{text "`x = y + 1 \<and> y = 2`"} in which the logical connectives can be parsed
  as both lifted boolean operators or UTP logical connectives. Such ambiguities
  arise since HOL connectives are automatically supported by lifting. A pending
  issue is whether we can avoid them already in the grammar, since they may in
  pathological cases considerably slow down the Isabelle parser. The current
  solution is hence a little bit of a hack but so far proved to work fine.
*}

(* Note that the following raises an error due to ambiguities. *)

(* term "`x = y + 1 \<and> y = (2::nat)`" *)

text {* The trick is to introduce a dummy node that causes parsing to fail. *}

syntax "_uinvalid" :: "term" ("\<star>")

text {* The ASTs on the LHS of the rules below are thus filtered out. *}

translations "(p \<and> q)\<^sub>p" \<rightharpoonup> "\<star>"
translations "(p \<or> q)\<^sub>p" \<rightharpoonup> "\<star>"

text {* This error should never be displayed. *}

parse_translation {*
  [(@{syntax_const "_uinvalid"}, K (fn _ =>
    error "Internal error: uparser failed to resolve ambiguities."))]
*}

text {* Finally, we configure Isabelle not to warn about syntax ambiguities. *}

declare [[syntax_ambiguity_warning=false]]

subsection {* Experiments *}

term "`\<not> x = (1::nat) \<and> true`"

term "`x = y + 1 \<and> y = (2::nat)`"

term "`(x = y + 1 ; y = 2) \<Rightarrow> x = (3::nat)`"

inject_type bool

term "`ok \<and> x = (1::nat) \<Rightarrow> ok' \<and> x' = x + 1`"

text {* Types are propagates through predicate connectives. *}

theorem "`x = y + 1 \<and> y = 2 \<Rightarrow> x = (3::nat)`"
apply (unfold evalp)
apply (clarify)
apply (simp)
done

text {* HOL quantifies can be used in lifted predicates too. *}

theorem "`\<exists> y . x = y + 1 \<Rightarrow> x > (0::nat)`"
apply (unfold evalp simp_thms)
apply (clarify)
apply (simp)
done

text {* Note that the following holds for arbitrary HOL sets! *}

theorem "`x < 3 \<and> s = {0::nat, 1, 2} \<Rightarrow> x \<in> s`"
apply (unfold evalp)
apply (safe)
apply (clarsimp)
done

text {* We even get unification between lifted and explicit variables. *}

term "`\<forall> {$x\<down>} . x' = x + (1::nat) ; x = 1 \<and> y = x`"
end