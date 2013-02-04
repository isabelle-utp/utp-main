theory utp_alpha_pred_parser
  imports
  "../alpha/utp_alpha_pred"
  "../alpha/utp_alpha_rel"
  "../alpha/utp_alpha_expr"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
  "../tactics/utp_rel_tac"
begin

nonterminal uapred and uaexpr and uzdecls and uzdecl

(* Predicate Parser *)

syntax
  "_uapred_top_clos" :: "uapred \<Rightarrow> bool" ("(1[_])")
  "_uapred_quote"    :: "uapred \<Rightarrow> 'a WF_ALPHA_PREDICATE" ("(1`_`)")
  "_uapred_brack"    :: "uapred \<Rightarrow> uapred" ("'(_')")
  "_uapred_true"     :: "'a ALPHABET \<Rightarrow> uapred" ("true\<^bsub>_\<^esub>")
  "_uapred_false"    :: "'a ALPHABET \<Rightarrow> uapred" ("false\<^bsub>_\<^esub>")
  "_uapred_var"      :: "pttrn \<Rightarrow> uapred" ("(_)")
  "_uapred_evar"     :: "'a VAR \<Rightarrow> uapred" ("$_")
  "_uapred_and"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<and>" 35)
  "_uapred_or"       :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<or>" 35)
  "_uapred_imp"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<Rightarrow>" 25)
  "_uapred_iff"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<Leftrightarrow>" 25)
  "_uapred_ref"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<sqsubseteq>" 25)
  "_uapred_clos"     :: "uapred \<Rightarrow> uapred" ("[_]")
  "_uapred_not"      :: "uapred \<Rightarrow> uapred" ("\<not> _" [40] 40)
  "_uapred_all1"     :: "pttrn \<Rightarrow> uapred \<Rightarrow> uapred"  ("(3\<forall> _./ _)" [0, 10] 10) 
  "_uapred_exists1"  :: "pttrn \<Rightarrow> uapred \<Rightarrow> uapred"  ("(3\<exists> _./ _)" [0, 10] 10) 
  "_uapred_equal"    :: "uaexpr \<Rightarrow> uaexpr \<Rightarrow> uapred" (infixl "=" 50)
  "_uapred_skip"     :: "'a ALPHABET \<Rightarrow> uapred" ("\<Pi>\<^bsub>_\<^esub>")
  "_uapred_seq"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr ";" 50)
  "_uapred_cond"     :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred \<Rightarrow> uapred" ("_ \<triangleleft> _ \<triangleright> _")
  "_uapred_assign"   :: "'a VAR \<Rightarrow> 'a ALPHABET \<Rightarrow> uaexpr \<Rightarrow> uapred" ("_ :=\<^bsub>_ \<^esub>_" [100] 100)
  "_uapred_zpara"    :: "uzdecls \<Rightarrow> uapred \<Rightarrow> uapred" ("[_|_]")
  "_uzdecl_basic"    :: "'a VAR \<Rightarrow> 'a VAR \<Rightarrow> uzdecl" (infix ":" 50)
  ""                 :: "uzdecl => uzdecls"             ("_")
  "_uzdecls"         :: "[uzdecl, uzdecls] => uzdecls" ("_,/ _")

abbreviation InSet :: 
  "('VALUE::SET_SORT) VAR \<Rightarrow> 'VALUE VAR \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" where
"InSet x A \<equiv> LiftA (finsert x (finsert A {}\<^sub>f)) (\<lambda> b. \<langle>b\<rangle>\<^sub>b x \<in>v \<langle>b\<rangle>\<^sub>b A)"

translations
  "_uapred_brack p"     => "p"
  "_uapred_quote p"     => "p"
  "_uapred_top_clos p"  == "CONST TautologyA p"
  "_uapred_true a"      == "CONST TrueA a"
  "_uapred_false a"     == "CONST FalseA a"
  "_uapred_var x"       => "x"
  "_uapred_evar x"      == "CONST VarA x"
  "_uapred_and p q"     == "CONST AndA p q"
  "_uapred_or p q"      == "CONST OrA p q"
  "_uapred_imp p q"     == "CONST ImpliesA p q"
  "_uapred_ref p q"     == "CONST RefA p q"
  "_uapred_iff p q"     == "CONST IffA p q"
  "_uapred_clos p"      == "CONST ClosureA p"
  "_uapred_not p"       == "CONST NotA p"
  "_uapred_all1 x p"    == "CONST ForallA {x} p"
  "_uapred_exists1 x p" == "CONST ExistsA {x} p"
  "_uapred_equal e f"   == "CONST EqualA e f"
  "_uapred_skip"        == "CONST SkipA"
  "_uapred_seq p q"     => "CONST SemiA p q"
  "_uapred_cond p q r"  == "CONST CondA p q r"
  "_uapred_assign x a e" == "CONST AssignA x a e"
  "_uapred_zpara ds p"  == "CONST AndA ds p"
  "_uzdecl_basic x A"   == "CONST InSet x A" 
  "_uzdecls d ds"       == "CONST AndA d ds"

(* Expression Parser *)

syntax
  "_uaexpr_true"     :: "uaexpr" ("true")
  "_uaexpr_false"    :: "uaexpr" ("false")
  "_uaexpr_var"      :: "pttrn \<Rightarrow> uaexpr" ("_")
  "_uaexpr_evar"     :: "'a VAR \<Rightarrow> uaexpr" ("$_")
  "_uaexpr_substp"   :: "uapred \<Rightarrow> uaexpr \<Rightarrow> pttrn \<Rightarrow> uapred" ("(_[_'/_])")

translations
  "_uaexpr_true"         == "CONST TrueAE"
  "_uaexpr_false"        == "CONST FalseAE"
  "_uaexpr_var x"        => "x" 
  "_uaexpr_evar x"       == "CONST VarAE x"
  "_uaexpr_substp p e x" == "CONST SubstA p e x"

lemma "[[x : A, y : B | $x = false ] \<sqsubseteq> TRUE]"
  oops

end


