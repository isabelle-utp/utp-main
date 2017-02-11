section {* UTP variables *}

theory utp_var
  imports
  Deriv
  "~~/src/HOL/Library/Prefix_Order"
  "~~/src/HOL/Library/Char_ord"
  "~~/src/Tools/Adhoc_Overloading"
  "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/Countable"
  "~~/src/HOL/Eisbach/Eisbach"
  "../contrib/Algebra/Complete_Lattice"
  "../contrib/Algebra/Galois_Connection"
  "../lenses/Lenses"
  "../utils/Profiling"
  "../utils/Library_extra/Pfun"
  "../utils/Library_extra/Ffun"
  "../utils/Library_extra/List_lexord_alt"
  "../utils/Library_extra/Monoid_extra"
  utp_parser_utils
begin

text {* We will overload the square order relation with refinement and also the lattice operators so
  we will turn off these notations. *}

no_notation 
  le (infixl "\<sqsubseteq>\<index>" 50) and
  asup ("\<Squnion>\<index>_" [90] 90) and
  ainf ("\<Sqinter>\<index>_" [90] 90)

text {* We hide HOL's built-in relation type since we will replace it with our own *}

hide_type rel

declare fst_vwb_lens [simp]
declare snd_vwb_lens [simp]
declare lens_indep_left_comp [simp]
declare comp_vwb_lens [simp]
declare lens_indep_left_ext [simp]
declare lens_indep_right_ext [simp]

text {* This theory describes the foundational structure of UTP variables, upon which the rest
        of our model rests. We start by defining alphabets, which following~\cite{Feliachi2010,Feliachi2012} 
        in this shallow model are simply represented as types, though by convention usually a record 
        type where each field corresponds to a variable. *}

type_synonym '\<alpha> "alphabet"  = "'\<alpha>"

text {* UTP variables in this frame are simply modelled as lenses, where the view type
  @{typ "'a"} is the variable type, and the source type @{text "'\<alpha>"} is the state-space
  type. *}

type_synonym ('a, '\<alpha>) uvar = "('a, '\<alpha>) lens"

 text {* We also define some lifting functions for variables to create input and output variables.
        These simply lift the alphabet to a tuple type since relations will ultimately be defined
        to a tuple alphabet. *}

definition in_var :: "('a, '\<alpha>) uvar \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) uvar" where
[lens_defs]: "in_var x = x ;\<^sub>L fst\<^sub>L"

definition out_var :: "('a, '\<beta>) uvar \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) uvar" where
[lens_defs]: "out_var x = x ;\<^sub>L snd\<^sub>L"

definition pr_var :: "('a, '\<beta>) uvar \<Rightarrow> ('a, '\<beta>) uvar" where
[simp]: "pr_var x = x"

lemma in_var_semi_uvar [simp]:
  "mwb_lens x \<Longrightarrow> mwb_lens (in_var x)"
  by (simp add: comp_mwb_lens in_var_def)

lemma in_var_uvar [simp]:
  "vwb_lens x \<Longrightarrow> vwb_lens (in_var x)"
  by (simp add: in_var_def)

lemma out_var_semi_uvar [simp]:
  "mwb_lens x \<Longrightarrow> mwb_lens (out_var x)"
  by (simp add: comp_mwb_lens out_var_def)

lemma out_var_uvar [simp]:
  "vwb_lens x \<Longrightarrow> vwb_lens (out_var x)"
  by (simp add: out_var_def)

lemma in_out_indep [simp]:
  "in_var x \<bowtie> out_var y"
  by (simp add: lens_indep_def in_var_def out_var_def fst_lens_def snd_lens_def lens_comp_def)

lemma out_in_indep [simp]:
  "out_var x \<bowtie> in_var y"
  by (simp add: lens_indep_def in_var_def out_var_def fst_lens_def snd_lens_def lens_comp_def)

lemma in_var_indep [simp]:
  "x \<bowtie> y \<Longrightarrow> in_var x \<bowtie> in_var y"
  by (simp add: in_var_def out_var_def)

lemma out_var_indep [simp]:
  "x \<bowtie> y \<Longrightarrow> out_var x \<bowtie> out_var y"
  by (simp add: out_var_def)

lemma prod_lens_indep_in_var [simp]:
  "a \<bowtie> x \<Longrightarrow> a \<times>\<^sub>L b \<bowtie> in_var x"
  by (metis in_var_def in_var_indep out_in_indep out_var_def plus_pres_lens_indep prod_as_plus)

lemma prod_lens_indep_out_var [simp]:
  "b \<bowtie> x \<Longrightarrow> a \<times>\<^sub>L b \<bowtie> out_var x"
  by (metis in_out_indep in_var_def out_var_def out_var_indep plus_pres_lens_indep prod_as_plus)
    
text {* We also define some lookup abstraction simplifications. *}

lemma var_lookup_in [simp]: "lens_get (in_var x) (A, A') = lens_get x A"
  by (simp add: in_var_def fst_lens_def lens_comp_def)

lemma var_lookup_out [simp]: "lens_get (out_var x) (A, A') = lens_get x A'"
  by (simp add: out_var_def snd_lens_def lens_comp_def)

lemma var_update_in [simp]: "lens_put (in_var x) (A, A') v = (lens_put x A v, A')"
  by (simp add: in_var_def fst_lens_def lens_comp_def)

lemma var_update_out [simp]: "lens_put (out_var x) (A, A') v = (A, lens_put x A' v)"
  by (simp add: out_var_def snd_lens_def lens_comp_def)

text {* Variables can also be used to effectively define sets of variables. Here we define the
        the universal alphabet ($\Sigma$) to be a variable with identity for both the lookup
        and update functions. Effectively this is just a function directly on the alphabet type. *}

abbreviation (input) univ_alpha :: "('\<alpha>, '\<alpha>) uvar" ("\<Sigma>") where
"univ_alpha \<equiv> 1\<^sub>L"

(*
  Nonterminals:
    svid: is an identifier soely used for variables
    svar: is a potentially decorated variable (but does not need to be?!)
    salpha: is to construct alphabets (variable sets). This can only be done
    through lense composition due to typing restrictions.
*)

nonterminal svid and svar and salpha

syntax
  "_salphaid"    :: "id \<Rightarrow> salpha" ("_" [998] 998)
  "_salphavar"   :: "svar \<Rightarrow> salpha" ("_" [998] 998)
  "_salphacomp"  :: "salpha \<Rightarrow> salpha \<Rightarrow> salpha" (infixr ";" 75)
  "_svid"        :: "id \<Rightarrow> svid" ("_" [999] 999)
  "_svid_alpha"  :: "svid" ("\<Sigma>")
  "_svid_empty"  :: "svid" ("\<emptyset>")
  "_svid_dot"    :: "svid \<Rightarrow> svid \<Rightarrow> svid" ("_:_" [999,998] 999)
  "_spvar"       :: "svid \<Rightarrow> svar" ("&_" [998] 998)
  "_sinvar"      :: "svid \<Rightarrow> svar" ("$_" [998] 998)
  "_soutvar"     :: "svid \<Rightarrow> svar" ("$_\<acute>" [998] 998)

(*
  The functions below turn a representation of a variable (type 'v) including
  its name and type. And 'e is typically some lense type. So the functions
  below bridge between then model/encoding of the variable and its interpretation
  as a lense in order to integrate it into the general lense-based framework.
  Overriding the below is all we need to make use of any kind of variables in
  terms of interfacing it with the system.
*)

consts
  svar :: "'v \<Rightarrow> 'e"
  ivar :: "'v \<Rightarrow> 'e"
  ovar :: "'v \<Rightarrow> 'e"

adhoc_overloading
  svar pr_var and ivar in_var and ovar out_var

translations
  "_salphaid x" => "x"
  "_salphacomp x y" => "x +\<^sub>L y"
  "_salphavar x" => "x"
  "_svid_alpha" == "\<Sigma>"
  "_svid_empty" == "0\<^sub>L"
  "_svid_dot x y" => "y ;\<^sub>L x"
  "_svid x" => "x"
  "_sinvar (_svid_dot x y)" <= "CONST ivar (CONST lens_comp y x)"
  "_soutvar (_svid_dot x y)" <= "CONST ovar (CONST lens_comp y x)"
  "_spvar x" == "CONST svar x"
  "_sinvar x" == "CONST ivar x"
  "_soutvar x" == "CONST ovar x"

text {* Syntactic function to construct a uvar type given a return type *}

syntax
  "_uvar_ty"      :: "type \<Rightarrow> type \<Rightarrow> type"

parse_translation {*
let
  fun uvar_ty_tr [ty] = Syntax.const @{type_syntax uvar} $ ty $ Syntax.const @{type_syntax dummy}
    | uvar_ty_tr ts = raise TERM ("uvar_ty_tr", ts);
in [(@{syntax_const "_uvar_ty"}, K uvar_ty_tr)] end
*}

end
