theory utp_cml_stmt
imports utp_cml_functions
begin

no_syntax
  "_n_upred_ifthenelse" :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("if _ then _ else _")
  "_n_upred_while"      :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("while _ do _ od")

syntax
  "_n_upred_ifthencml" :: "n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("(if (_)/ then (_)/ else (_))" [0, 0, 10] 10)
  "_n_upred_whilecml"  :: "n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("while _ do _ od")

translations
  "_n_upred_ifthencml b P Q" == "CONST CondR P (CONST VTautHideT b) Q"
  "_n_upred_whilecml b P" == "CONST IterP (CONST VTautHideT b) P"

text {* A CML operation specification takes an input type, an output type,
        a precondition, a postcondition and the "body" of the operation. *}

definition CMLOpR :: 
  "'a set \<Rightarrow> 'b set \<Rightarrow> 
   ('a \<Rightarrow> bool cmle) \<Rightarrow> (('a * 'b) \<Rightarrow> bool cmle) \<Rightarrow> ('b cmlvar \<Rightarrow> 'a \<Rightarrow> cmlp) \<Rightarrow> ('b cmlvar \<Rightarrow> 'a \<Rightarrow> cmlp)" where
"CMLOpR A B pre post body v x = (let bd = body v x in `\<lparr> &x hasType @A \<rparr> \<and> \<lparr> pre(&x) \<rparr> 
                                                       \<turnstile> \<lparr> $v\<acute> hasType @B \<rparr> \<and> \<lparr> post(&x, $v) \<rparr>\<acute> \<and> bd`)"

declare CMLOpR_def [evalpp, evalpr]

definition CMLIOpR ::
  "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> bool cmle) \<Rightarrow> (('a * 'b) \<Rightarrow> bool cmle) \<Rightarrow> cmluvar fset \<Rightarrow> ('b cmlvar \<Rightarrow> 'a \<Rightarrow> cmlp)" where
"CMLIOpR A B pre post frm = CMLOpR A B pre post (\<lambda> v i. SkipRA (REL_VAR - (OKAY \<union> \<langle>frm\<rangle>\<^sub>f \<union> (dash ` \<langle>frm\<rangle>\<^sub>f))))"

declare CMLIOpR_def [evalpp, evalpr]

(*
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
*)

definition NotYetSpecD :: "cmlp" where
"NotYetSpecD = `true`"

definition DclD :: "'a cmlvar \<Rightarrow> ('a cmlvar \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"DclD x F = (let p = F(x) in `var x; p; end x`)"

definition DclO :: "'t cmlvar \<Rightarrow> ('t cmlvar \<Rightarrow> 'a cmlopb) \<Rightarrow> 'a cmlopb" where
"DclO x F = (\<lambda> r. let p = F x r in `var x; p; end x`)"
term SpecD

definition SpecO :: "cmlv uvar set \<Rightarrow> bool cmle \<Rightarrow> bool cmle \<Rightarrow> 'a cmlopb" where
"SpecO vs p q = (\<lambda> r. SpecD vs (VTautHideT p) (VTautHideT q))"

definition ReturnP :: "'a cmlvar \<Rightarrow> 'a cmle \<Rightarrow> cmlp" where
"ReturnP = (\<lambda> x e. PAssignR x e)"

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
  "_upred_sskip"    :: "n_upred" ("III")
  "_upred_return"   :: "n_pexpr \<Rightarrow> n_upred" ("return _" [100] 100)

(*
ML_file "utp_cml_parser.ML"

parse_ast_translation {*
   [(@{syntax_const "_cml_var"}, K Cml_Parser.cml_var_ast_tr),
    (@{syntax_const "_vexpr_dcl"}, K Cml_Parser.cml_dcl_ast_tr),
    (@{syntax_const "_vop_dcl"}, K Cml_Parser.cml_op_dcl_ast_tr)]
*}
*)

translations
  "_idt_set (_vidts x xs)" => "Set.insert x\<down> (_idt_set xs)"
  "_idt_set (_vidt x)"     => "Set.insert x\<down> {}"
  "_upred_speccml xs p q"  == "CONST SpecD (_idt_set xs) (CONST VTautHideT p) (CONST VTautHideT q)"
  "_upred_especcml p q"    == "CONST SpecD {} (CONST VTautHideT p) (CONST VTautHideT q)"
  "_upred_precml p"        == "CONST SpecD {} (CONST VTautHideT p) (CONST TrueP)"
  "_uop_speccml xs p q"    == "CONST SpecO (_idt_set xs) p q"
  "_uop_especcml p q"      == "CONST SpecO {} p q"
  "_uop_precml p"          == "CONST SpecO {} p CONST TrueDE"
  "_upred_nyscml"          == "CONST NotYetSpecD"
  "_cml_var x t"           == "CONST MkVarD IDSTR(x) t"
  "_vexpr_dcl x t p"       => "CONST DclD (_cml_var x t) (\<lambda> x. p)"
  "_vop_dcl x t p"         => "CONST DclO (_cml_var x t) (\<lambda> x. p)"

(* A return statement is just an assignment, but using the fresh variable RESULT *)

translations
  "_upred_return e" <= "CONST ReturnP x e"

parse_translation {* 
let
  val result = Free ("RESULT", dummyT)
  fun return_tr [e] = Syntax.const @{const_name ReturnP} $ result $ e
in
  [(@{syntax_const "_upred_return"}, K return_tr)]
end
*} 

term "`dcl x : @nat @ (x := 1; y := $x)`" 
term "{: dcl x : @nat @ (x := 1; y := $x) :}"
term "`x,y:[$x > 0, $y = $y~ / $x]`"
term "`[$x > 0, true]`"
term "`[$x > 1]`"
term "`P ; is not yet specified`"
term "`return ($x + 1)`"

term "`\<lparr> defn(@e) \<rparr> \<turnstile> true`"

thm CallRO_def

(* Guard a CML predicate by a CML expression *)

lift_definition GuardCmlP :: "'a cmle \<Rightarrow> ('a \<Rightarrow> cmlp) \<Rightarrow> cmlp"
is "\<lambda> e P. {b. case (e b) of None \<Rightarrow> False | Some v \<Rightarrow> \<lbrakk>P(v)\<rbrakk>b}" .

(* Call an operation when the parameter is defined *)

definition CallOp :: "('a, 'b) cmlop \<Rightarrow> 'a cmle \<Rightarrow> cmlp" where
"CallOp F e = `\<lparr> defn(@e) \<rparr>` \<turnstile> (GuardCmlP e (F undefined))"

definition AssignOp :: "'b cmlvar \<Rightarrow> ('a, 'b) cmlop \<Rightarrow> 'a cmle \<Rightarrow> cmlp" where
"AssignOp x F e = `\<lparr> defn(@e) \<rparr>` \<turnstile> (GuardCmlP e (F x))"

syntax
  "_n_upred_vcallpr"     :: "idt \<Rightarrow> n_pexprs \<Rightarrow> n_upred" ("call _'[_']")
  "_n_upred_vcallpr_nil" :: "idt \<Rightarrow> n_upred" ("call _'[']")
  "_n_upred_vassignpr"   :: 
    "idt \<Rightarrow> idt \<Rightarrow> n_pexprs \<Rightarrow> n_upred" ("_ := _'[_']" [100,0,0] 100)
  "_n_upred_vassignpr_nil" :: 
    "idt \<Rightarrow> idt \<Rightarrow> n_upred" ("_ := _'[']" [100] 100)

translations
  "_n_upred_vcallpr f ps" == "CONST CallOp f (_vexpr_prod ps)"
  "_n_upred_vcallpr_nil f" == "CONST CallOp f CONST UnitD"
  "_n_upred_vassignpr x f ps" == "CONST AssignOp x f (_vexpr_prod ps)"
  "_n_upred_vassignpr_nil x f" == "CONST AssignOp x f (CONST UnitD)"

end
