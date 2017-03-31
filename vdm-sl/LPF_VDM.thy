(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: LPF_VDM.thy                                                          *)
(* Authors: Casper Thule, Frank Zeyda and Simon Foster                        *)
(* Emails: casper.thule@eng.au.dk and {frank.zeyda, simon.foster}@york.ac.uk  *) 
(******************************************************************************)
(* LAST REVIEWED: 22 Mar 2017 *)

section {* Embedding of VDM *}

theory LPF_VDM
imports LPF "../utp/models/utp_deep"
begin

text {* 
  A type synonym is set up for improved syntax. 
  A @{text vexpr} is a function that takes a state as argument and returns the 
  value of the expression evaluated in the given state. E.g. a state can be 
  @{text "{x \<leadsto> 2}"} and if an expression @{text "x + 2"} is evaluated in this 
  state, then it would yield 4.
*} 

type_synonym ('a, '\<alpha>) vexpr = "('a lpf, '\<alpha>) uexpr"

text {* 
  The translation below makes for pretty printing.
  Before: @{text "('a, '\<alpha>) vexpr"} prints @{text "('a lpf, '\<alpha>) uexpr"}.
  After: @{text "('a, '\<alpha>) vexpr"} prints @{text "('a, '\<alpha>) vexpr"}.
*}  

translations (type) "('a, '\<alpha>) vexpr" \<leftharpoondown> (type) "('a lpf, '\<alpha>) uexpr"

text {* The lifting of values into the type @{type uexpr} is set up next. *}

setup_lifting type_definition_uexpr

text {* 
  The function below determines undefinedness. It returns @{const lpf_None} 
  regardless of the argument.
*}

definition undefined_vdm :: "('a, '\<alpha>) vexpr" where
"undefined_vdm = \<guillemotleft>lpf_None\<guillemotright>"

text {* The function below determines definedness. Its argument is a function
  that takes an argument. If the value produced by appliying the argument to the 
  function is defined, then true is returned. Otherwise false is returned.
*}

definition defined_vdm :: "('a, '\<sigma>) vexpr \<Rightarrow> (bool, '\<sigma>) uexpr" where
"defined_vdm = (uop defined)"

text {*
  The function below takes a HOL variable and returns a binding. 
  When a value is applied to the binding it returns the HOL variable wrapped in 
  the LPF defined. It is not necessary to check for definedness, as HOL 
  variables are defined.
*}

definition lit_vdm :: "'a \<Rightarrow> ('a, '\<sigma>) vexpr" where
"lit_vdm c = \<guillemotleft>lpf_Some c\<guillemotright>"

text {*
  In the function below we lift a unary operator into the type @{type vexpr}.
  The function takes a predicate and the function to lift. It lifts the function 
  into a binding, which when given a value, returns the value produced by the 
  binding.
*}

definition lift1_vdm :: 
  "'a set \<Rightarrow> ('a \<Rightarrow> 'b)  \<Rightarrow> (('a, '\<sigma>) vexpr \<Rightarrow> ('b, '\<sigma>) vexpr)" where
"lift1_vdm A = uop o (lift1_lpf A)"

lift_definition lift1_vdm_new :: 
  "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b)  \<Rightarrow> (('a, '\<sigma>) vexpr \<Rightarrow> ('b, '\<sigma>) vexpr)" is
"(\<lambda>(p::'c\<Rightarrow>bool) (f::'c => 'd) (uf::'e=>'c lpf) (e::'e) .
  if ((defined \<circ> uf) e) \<and> (p \<circ> lpf_the \<circ> uf) e 
  then ((lift1_lpf' f) \<circ> uf) e 
  else lpf_None)" .

lift_definition lift1_vdm_new' :: 
  "('a \<Rightarrow> 'b)  \<Rightarrow> (('a, '\<sigma>) vexpr \<Rightarrow> ('b, '\<sigma>) vexpr)" is
" (\<lambda>(f::'c => 'd) . lift1_vdm_new (\<lambda>x . True) f)" .

lift_definition hd_vdm :: "('a list, '\<sigma>) vexpr \<Rightarrow> ('a, '\<sigma>) vexpr" is
"lift1_vdm_new (\<lambda>x . x\<noteq>[]) hd" .

lift_definition tl_vdm :: "('a list, '\<sigma>) vexpr \<Rightarrow> ('a list, '\<sigma>) vexpr" is
"lift1_vdm_new' tl" .

consts bop_vdm ::
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow>
   (('a, '\<sigma>) uexpr \<Rightarrow> ('b, '\<sigma>) vexpr \<Rightarrow> ('c, '\<sigma>) vexpr)"

consts trop_vdm ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow>
   (('a, '\<sigma>) vexpr \<Rightarrow> ('b, '\<sigma>) vexpr \<Rightarrow> ('c, '\<sigma>) vexpr \<Rightarrow> ('d, '\<sigma>) vexpr)"

text {* Finally, we also need to lift lenses into VDM expressions. *}

text {* Once we have done this, we have to reconfigure the proof strategy! *}
end