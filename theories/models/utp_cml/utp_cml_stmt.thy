theory utp_cml_stmt
imports utp_cml_functions
begin

text {* A CML operation specification takes an input type, an output type,
        a precondition, a postcondition and the "body" of the operation. *}

definition CMLOpO :: 
  "'a set \<Rightarrow> 'b set \<Rightarrow> 
   ('a cmle \<Rightarrow> bool cmle) \<Rightarrow> 
   ('a cmle \<Rightarrow> 'b cmlvar \<Rightarrow> bool cmle) \<Rightarrow> 
   ('a, 'b) cmlop \<Rightarrow> ('a, 'b) cmlop" where 
"CMLOpO A B pre post body = (\<lambda> i x. VExprDefinedT (pre i) \<turnstile> 
                                   (if (snd x) then VExprDefinedT (post i (fst x)) 
                                               else TrueP) 
                                   \<and>\<^sub>p (body i x))"

declare CMLOpO_def [uop_defs]

definition NotYetSpecD :: "cmlp" where
"NotYetSpecD = `true`"

definition DclD :: "'a cmlvar \<Rightarrow> ('a cmlvar \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"DclD x F = (let p = F(x) in `var x; p; end x`)"

definition DclO :: "'t cmlvar \<Rightarrow> ('t cmlvar \<Rightarrow> 'a cmlopb) \<Rightarrow> 'a cmlopb" where
"DclO x F = (\<lambda> r. let p = F x r in `var x; p; end x`)"
term SpecD

definition SpecO :: "cmlv uvar set \<Rightarrow> bool cmle \<Rightarrow> bool cmle \<Rightarrow> 'a cmlopb" where
"SpecO vs p q = (\<lambda> r. SpecD vs (VTautHideT p) (VTautHideT q))"

no_syntax
  "_n_upred_spec" :: "'a uvar set \<Rightarrow> n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_:[_, _]" [999] 1000)
  "_n_upred_clos" :: "n_upred \<Rightarrow> n_upred" ("[_]")

syntax
  "_upred_nyscml"   :: "n_upred" ("is not yet specified")
  "_upred_speccml"  :: "idt_list \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_:[_, _]" [999] 1000)
  "_upred_especcml" :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("[_, _]")
  "_upred_precml"   :: "n_pexpr \<Rightarrow> n_upred" ("[_]")
  "_uop_speccml"    :: "idt_list \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_uproc" ("_:[_, _]" [999] 1000)
  "_uop_especcml"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_uproc" ("[_, _]")
  "_uop_precml"     :: "n_pexpr \<Rightarrow> n_uproc" ("[_]")
  "_idt_set"        :: "idt_list \<Rightarrow> logic"
  "_vexpr_dcl"      :: "id \<Rightarrow> vty \<Rightarrow> n_upred \<Rightarrow> n_upred" ("dcl _ : _ @  _")
  "_vop_dcl"        :: "id \<Rightarrow> vty \<Rightarrow> n_uproc \<Rightarrow> n_uproc" ("dcl _ : _ @  _")
  "_cml_var"        :: "id \<Rightarrow> vty \<Rightarrow> logic" ("CMLVAR'(_, _')")

ML_file "utp_cml_parser.ML"

parse_ast_translation {*
   [(@{syntax_const "_cml_var"}, K Cml_Parser.cml_var_ast_tr),
    (@{syntax_const "_vexpr_dcl"}, K Cml_Parser.cml_dcl_ast_tr),
    (@{syntax_const "_vop_dcl"}, K Cml_Parser.cml_op_dcl_ast_tr)]
*}

translations
  "_idt_set (_vidts x xs)" => "Set.insert x\<down> (_idt_set xs)"
  "_idt_set (_vidt x)"     => "Set.insert x\<down> {}"
  "_upred_speccml xs p q"  == "CONST SpecD (_idt_set xs) (CONST VTautHideT p) (CONST VTautHideT q)"
  "_upred_especcml p q"    == "CONST SpecD {} (CONST VTautHideT p) (CONST VTautHideT q)"
  "_upred_precml p"        == "CONST SpecD {} (CONST VTautHideT p) (CONST TrueP)"
  "_uop_speccml xs p q"    == "CONST SpecO (_idt_set xs) p q"
  "_uop_especcml p q"      == "CONST SpecO {} p q"
  "_uop_precml p"          == "CONST SpecO {} p CONST TrueDE"

  "_upred_nyscml" == "CONST NotYetSpecD"

term "`dcl x : @nat @ (x := 1; y := $x)`" 
term "`x,y:[$x > 0, $y = $y~ / $x]`"
term "`[$x > 0, true]`"
term "`[$x > 1]`"
term "`P ; is not yet specified`"

end
