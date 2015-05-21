(*FIXME:  Statements are not yet fully developed in the translation*)

theory utp_vdm_stmt
imports utp_vdm_functions
begin

definition AssignC :: "'a vdmvar \<Rightarrow> 'a vdme \<Rightarrow> vdmp" where
"AssignC x v = `\<lparr> defn(@v) \<rparr> \<turnstile> x := @v`"

definition IndexD :: "('a \<Rightarrow> vdmp) \<Rightarrow> 'a vdme \<Rightarrow> vdmp"
where "IndexD F v = mkPRED {b. \<lbrakk>F(the(\<lbrakk>v\<rbrakk>\<^sub>*b))\<rbrakk>b}"

(* VDM assignment can be performed on various type of expression with a variable this
   overloaded constant implements this. *)

consts
  asgn_app :: "'a vdmvar \<Rightarrow> 'b vdme \<Rightarrow> 'c vdme \<Rightarrow> 'd vdme"

abbreviation "AssignC_app x v e \<equiv> AssignC x (asgn_app x v e)"

nonterminal
  vasgn_exp

no_syntax
  "_n_upred_index"      :: "('b \<Rightarrow> 'a upred) \<Rightarrow> 'b \<Rightarrow> n_upred" ("_<_>" 50)
  "_n_upred_assigns"    :: "n_pvars \<Rightarrow> n_pexprs \<Rightarrow> n_upred" ("_ := _" [100] 100)
  "_n_upred_ifthenelse" :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("if _ then _ else _")
  "_n_upred_while"      :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("while _ do _ od")

syntax
  "_n_upred_assignvdm" :: "vasgn_exp \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_ := _" [100] 100)
  "_n_upred_ifthenvdm" :: "n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("(if (_)/ then (_)/ else (_))" [0, 0, 10] 10)
  "_n_upred_whilevdm"  :: "n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("while _ do _ od")
  "_vasgn_id"          :: "idt \<Rightarrow> vasgn_exp" ("_")
  "_vasgn_app"         :: "idt \<Rightarrow> n_pexprs \<Rightarrow> vasgn_exp" ("_'(_')")
  "_n_upred_cindex"     :: "idt \<Rightarrow> n_pexprs \<Rightarrow> n_upred" ("_<_>" [999,0] 999)

translations
  "_n_upred_assignvdm (_vasgn_id x) e" == "CONST AssignC x e"
  "_n_upred_assignvdm (_vasgn_app x i) e" == "CONST AssignC_app x (_vexpr_prod i) e"
  "_n_upred_ifthenvdm b P Q" == "CONST CondR P (CONST VTautHideT b) Q"
  "_n_upred_whilevdm b P" == "CONST IterP (CONST VTautHideT b) P"
  "_n_upred_cindex F v"           == "CONST IndexD F (_vexpr_prod v)"

(*term "`MERGE2<($e2), ^r^> ||| P`"*)

term "`x := 5`"
term "`f(5) := 1`"

term "|@f ++ {@i |-> @v}|"

definition "vmap_asgn_app f i v = |$f ++ {@i |-> @v}|"

adhoc_overloading
  asgn_app vmap_asgn_app

text {* A VDM operation specification takes an input type, an output type,
        a precondition, a postcondition and the "body" of the operation. *}

definition VDMOpR :: 
  "'a set \<Rightarrow> 'b set \<Rightarrow> 
   ('a \<Rightarrow> bool vdme) \<Rightarrow> (('a * 'b) \<Rightarrow> bool vdme) \<Rightarrow> ('b vdmvar \<Rightarrow> 'a \<Rightarrow> vdmp) \<Rightarrow> ('b vdmvar \<Rightarrow> 'a \<Rightarrow> vdmp)" where
"VDMOpR A B pre post body v x = (let bd = body v x in `\<lparr> &x hasType @A \<rparr> \<and> \<lparr> pre(&x) \<rparr> 
                                                       \<turnstile> \<lparr> $v\<acute> hasType @B \<rparr> \<and> \<lparr> post(&x, $v) \<rparr>\<acute> \<and> bd`)"

declare VDMOpR_def [evalpp, evalpr]

definition VDMIOpR ::
  "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> bool vdme) \<Rightarrow> (('a * 'b) \<Rightarrow> bool vdme) \<Rightarrow> vdmuvar fset \<Rightarrow> ('b vdmvar \<Rightarrow> 'a \<Rightarrow> vdmp)" where
"VDMIOpR A B pre post frm = VDMOpR A B pre post (\<lambda> v i. SkipRA (REL_VAR - (OKAY \<union> \<langle>frm\<rangle>\<^sub>f \<union> (dash ` \<langle>frm\<rangle>\<^sub>f))))"

declare VDMIOpR_def [evalpp, evalpr]

(*
definition VDMOpO :: 
  "'a set \<Rightarrow> 'b set \<Rightarrow> 
   ('a vdme \<Rightarrow> bool vdme) \<Rightarrow> 
   ('a vdme \<Rightarrow> 'b vdmvar \<Rightarrow> bool vdme) \<Rightarrow> 
   ('a, 'b) vdmop \<Rightarrow> ('a, 'b) vdmop" where 
"VDMOpO A B pre post body = (\<lambda> i x. VExprDefinedT (pre i) \<turnstile> 
                                   (if (snd x) then VExprDefinedT (post i (fst x)) 
                                               else TrueP) 
                                   \<and>\<^sub>p (body i x))"

declare VDMOpO_def [uop_defs]
*)

definition LetC :: "'a vdme \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> vdmp) \<Rightarrow> vdmp" where
"LetC v A P = `\<lparr> defn(@v) and @v hasType A \<rparr> \<turnstile> P<@v>`"

definition NotYetSpecD :: "vdmp" where
"NotYetSpecD = `true`"

definition DclD :: "'a vdmvar \<Rightarrow> ('a vdmvar \<Rightarrow> vdmp) \<Rightarrow> vdmp" where
"DclD x F = (let p = F(x) in `var x; p; end x`)"

definition DclO :: "'t vdmvar \<Rightarrow> ('t vdmvar \<Rightarrow> 'a vdmopb) \<Rightarrow> 'a vdmopb" where
"DclO x F = (\<lambda> r. let p = F x r in `var x; p; end x`)"
term SpecD

definition SpecO :: "vdmm uvar set \<Rightarrow> bool vdme \<Rightarrow> bool vdme \<Rightarrow> 'a vdmopb" where
"SpecO vs p q = (\<lambda> r. SpecD vs (VTautHideT p) (VTautHideT q))"

definition ReturnP :: "'a vdmvar \<Rightarrow> 'a vdme \<Rightarrow> vdmp" where
"ReturnP = (\<lambda> x e. PAssignR x e)"

no_syntax
  "_n_upred_spec" :: "'a uvar set \<Rightarrow> n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_:[_, _]" [999] 1000)
  "_n_upred_clos" :: "n_upred \<Rightarrow> n_upred" ("[_]")

syntax
  "_upred_nysvdm"   :: "n_upred" ("is not yet specified")
  "_upred_specvdm"  :: "idt_list \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_:[_, _]" [999] 1000)
  "_upred_especvdm" :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("[_, _]")
  "_upred_prevdm"   :: "n_pexpr \<Rightarrow> n_upred" ("[_]")
  "_uop_specvdm"    :: "idt_list \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_uproc" ("_:[_, _]" [999] 1000)
  "_uop_especvdm"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_uproc" ("[_, _]")
  "_uop_prevdm"     :: "n_pexpr \<Rightarrow> n_uproc" ("[_]")
  "_idt_set"        :: "idt_list \<Rightarrow> logic"
  "_vexpr_dcl"      :: "id \<Rightarrow> vty \<Rightarrow> n_upred \<Rightarrow> n_upred" ("dcl _ : _ @  _")
  "_vop_dcl"        :: "id \<Rightarrow> vty \<Rightarrow> n_uproc \<Rightarrow> n_uproc" ("dcl _ : _ @  _")
  "_vdm_var"        :: "id \<Rightarrow> vty \<Rightarrow> logic" ("VDMVAR'(_, _')")
  "_upred_sskip"    :: "n_upred" ("III")
  "_upred_return"   :: "n_pexpr \<Rightarrow> n_upred" ("return _" [100] 100)
  "_n_upred_let"    :: "idt \<Rightarrow> vty \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("let _ : _ = _ in _")

(*
ML_file "utp_vdm_parser.ML"

parse_ast_translation {*
   [(@{syntax_const "_vdm_var"}, K Vdm_Parser.vdm_var_ast_tr),
    (@{syntax_const "_vexpr_dcl"}, K Vdm_Parser.vdm_dcl_ast_tr),
    (@{syntax_const "_vop_dcl"}, K Vdm_Parser.vdm_op_dcl_ast_tr)]
*}
*)

translations
  "_idt_set (_vidts x xs)" => "Set.insert x\<down> (_idt_set xs)"
  "_idt_set (_vidt x)"     => "Set.insert x\<down> {}"
  "_upred_specvdm xs p q"  == "CONST SpecD (_idt_set xs) (CONST VTautHideT p) (CONST VTautHideT q)"
  "_upred_especvdm p q"    == "CONST SpecD {} (CONST VTautHideT p) (CONST VTautHideT q)"
  "_upred_prevdm p"        == "CONST SpecD {} (CONST VTautHideT p) (CONST TrueP)"
  "_uop_specvdm xs p q"    == "CONST SpecO (_idt_set xs) p q"
  "_uop_especvdm p q"      == "CONST SpecO {} p q"
  "_uop_prevdm p"          == "CONST SpecO {} p CONST TrueDE"
  "_upred_nysvdm"          == "CONST NotYetSpecD"
  "_vdm_var x t"           == "CONST MkVarD IDSTR(x) t"
  "_vexpr_dcl x t p"       => "CONST DclD (_vdm_var x t) (\<lambda> x. p)"
  "_vop_dcl x t p"         => "CONST DclO (_vdm_var x t) (\<lambda> x. p)"
  "_n_upred_let x A e P"   == "CONST LetC e A (\<lambda> x. P)"

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

(* Guard a VDM predicate by a VDM expression *)

lift_definition GuardVdmP :: "'a vdme \<Rightarrow> ('a \<Rightarrow> vdmp) \<Rightarrow> vdmp"
is "\<lambda> e P. {b. case (e b) of None \<Rightarrow> False | Some v \<Rightarrow> \<lbrakk>P(v)\<rbrakk>b}" .

(* Call an operation when the parameter is defined *)

definition CallOp :: "('a, 'b) vdmop \<Rightarrow> 'a vdme \<Rightarrow> vdmp" where
"CallOp F e = `\<lparr> defn(@e) \<rparr>` \<turnstile> (GuardVdmP e (F undefined))"

definition AssignOp :: "'b vdmvar \<Rightarrow> ('a, 'b) vdmop \<Rightarrow> 'a vdme \<Rightarrow> vdmp" where
"AssignOp x F e = `\<lparr> defn(@e) \<rparr>` \<turnstile> (GuardVdmP e (F x))"

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

term "`let y : @int = 5 in P<&x,&y>`"

end
