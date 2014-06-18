(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_commands.thy                                                 *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Commands to construct CML definitions *}

theory utp_cml_commands
imports 
  utp_cml_functions
  utp_cml_stmt
keywords "cmlifun" "cmlefun" "cmleop" "cmliop" "cmlacts" :: thy_decl and "inp" "out" "pre" "post" "frame"
begin

abbreviation "swap \<equiv> \<lambda> (x,y). (y, x)"                                          

definition mk_ifun_body :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> bool cmle) \<Rightarrow> (('a * 'b) \<Rightarrow> bool cmle) \<Rightarrow> ('a * 'b) set" where
"mk_ifun_body A B pre post 
  = {(x,y) | x y. x \<in> A \<and> y \<in> B \<and> \<lbrakk>pre(x)\<rbrakk>\<^sub>*\<B> = Some True \<and> \<lbrakk>post(x,y)\<rbrakk>\<^sub>*\<B> = Some True}"

declare mk_ifun_body_def [evalp]


ML {*

signature CMLCOMMANDS =
sig
  val mk_efun: (string * ((string * string) list * string)) * ((string * string) * string) 
              -> Proof.context -> local_theory
  val mk_ifun: (string * ((string * string) list * (string * string))) * (string * string) 
               -> Proof.context -> local_theory
  val mk_eop: (string * ((string * string) list * string)) * ((string * string) * string) 
              -> Proof.context -> local_theory
  val mk_iop: ((string * ((string * string) list * (string * string))) * (string list * (string * string)))
              -> Proof.context -> local_theory
  val mk_acts: (string * string) list -> local_theory -> local_theory
  val efun_pr: Token.T list ->
      ((string * ((string * string) list * string)) * ((string * string) * string)) * Token.T list
  val ifun_pr: Token.T list ->
      ((string * ((string * string) list * (string * string))) * (string * string)) * Token.T list
  val eop_pr: Token.T list ->
      ((string * ((string * string) list * string)) * ((string * string) * string)) * Token.T list
  val iop_pr: Token.T list -> 
      ((string * ((string * string) list * (string * string))) * (string list * (string * string))) * Token.T list
  val acts_pr: Token.T list -> (string * string) list * Token.T list
end

structure CmlCommands : CMLCOMMANDS =
struct

open Syntax;
open Local_Theory;

fun split_dot x = case (String.tokens (fn x => x = #".") x) of
                    [_,y] => y
                  | _ => x;

(* Functions to get grammar categories from the context *)

fun n_upred ctxt = (Config.put root @{nonterminal "n_upred"} ctxt);
fun n_pexpr ctxt = (Config.put root @{nonterminal "n_pexpr"} ctxt);
fun vty ctxt = (Config.put root @{nonterminal "vty"} ctxt);

(* Substitute an expression for a given free name irrespective of the type *)

fun subst_free nm e (u $ t) = subst_free nm e u $ subst_free nm e t
  | subst_free nm e (Free (x, t)) = if (x = nm) then e else Free (x, t)
  | subst_free nm e (Abs (y, ty, tr)) = if (nm = y) then (Abs (y, ty, tr)) else (Abs (y, ty, subst_free nm e tr))
  | subst_free _ _ t = t;

(* Insert a lambda abstraction for a given free name, irrespective of the type *)
local
  fun absnm' x n (u $ t) = (absnm' x n u) $ (absnm' x n t)
    | absnm' x n (Const (y, t)) = if (x = split_dot y) then Bound n else Const (y, t) 
    (* FIXME: Slightly dangerous case: if we encounter a constant with the same local
       name part as the variable we're abstracting, treat it as a variable. Could we
       accidentally capture? *)
    | absnm' x n (Free (y, t)) = if (x = y) then Bound n else Free (y, t)
    | absnm' x n (Abs (y, ty, tr)) = if (x = y) then (Abs (y, ty, tr)) else (Abs (y, ty, absnm' x (n+1) tr))
    | absnm' _ _ e = e;
in fun absnm (x, ty) n tr = Abs (x, ty, absnm' x n tr) end;

(* Given a CML type, get the HOL "maximimal" type *)

fun get_cml_holty ty ctxt = 
  let val tctxt = vty ctxt in
  case (type_of (read_term tctxt ty)) of
    Type (_, [ty]) => ty
  | x => error (@{make_string} x)
 end;

(* Create a product-based lambda term from a list of names and types *)

fun mk_lambda [(id, ty)] term ctxt =
      absnm (id, get_cml_holty ty ctxt) 0 term
  | mk_lambda ((id, ty) :: xs) term ctxt =
      const @{const_name "prod_case"} 
        $ absnm (id, get_cml_holty ty ctxt) 0 (mk_lambda xs term ctxt)
  | mk_lambda [] term _ = term;

fun mk_act_lambda [id] term ctxt =
      absnm (id, @{typ "cmlp"}) 0 term
  | mk_act_lambda (id :: xs) term ctxt =
      const @{const_name "aprod_case"} 
        $ absnm (id, @{typ "cmlp"}) 0 (mk_act_lambda xs term ctxt)
  | mk_act_lambda [] term _ = term;

fun mk_n_of_m n m =
  if (m = 0) then const @{const_name id}
  else if (n = 0) then const @{const_name afst}
  else const @{const_name comp} $ mk_n_of_m (n - 1) (m - 1) $ const @{const_name asnd}

(* Attribute to add a theorem to the evalp theorem set *)

val add_evalp = Attrib.internal (K (Thm.declaration_attribute evalp.add_thm));

(* Make a product type from a list of type terms *)

fun mk_prod_ty ctxt [] = @{term UnitD}
  | mk_prod_ty ctxt ts = foldr1 (fn (x,y) => 
                           (check_term ctxt (const @{const_abbrev "vty_prod"} $ x $ y)))
                                            (map (read_term (vty ctxt) o snd) ts)

fun mk_defn id prefix t =
  ((Binding.name (prefix ^ id), NoSyn), ((Binding.name (prefix ^ id ^ "_def"), [add_evalp]), t))

fun mk_eop ((id, (inp, out)), ((pre, post), body)) ctxt =
  let val pre_term  = check_term (n_pexpr ctxt) (mk_lambda inp (parse_term (n_pexpr ctxt) pre) ctxt)
      val post_term = check_term (n_pexpr ctxt)
                          (const @{const_name "comp"} 
                            $ (mk_lambda (("RESULT", out) :: inp) (parse_term (n_pexpr ctxt) post) ctxt)
                            $ const @{const_abbrev "swap"})
      val body_term = absnm ("RESULT", Type (@{type_abbrev "cmlvar"}, [get_cml_holty out ctxt])) (length inp) (mk_lambda inp (parse_term (n_upred ctxt) body) ctxt)
      val op_term = check_term ctxt (
                        const @{const_name CMLOpR} 
                        $ mk_prod_ty ctxt inp 
                        $ read_term (vty ctxt) out
                        $ pre_term
                        $ post_term
                        $ body_term)
      val ((_,(_,thm1)), ctxt1) = define (mk_defn id "pre_" pre_term) ctxt
      val ((_,(_,thm2)), ctxt2) = define (mk_defn id "post_" post_term) ctxt1
      val ((_,(_,thm3)), ctxt3) = define (mk_defn id "" op_term) ctxt2
  in 
      ctxt3
  end;

fun mk_iop ((id, (inp, (outn, outt))), (frame, (pre, post))) ctxt =
let val pre_term  = check_term (n_pexpr ctxt) (mk_lambda inp (parse_term (n_pexpr ctxt) pre) ctxt)
    val post_term = check_term (n_pexpr ctxt)
                        (const @{const_name "comp"} 
                          $ (mk_lambda ((outn, outt) :: inp) (parse_term (n_pexpr ctxt) post) ctxt)
                          $ const @{const_abbrev "swap"})
    val frame_set = List.foldr (fn (x, xs) => const @{const_name "finsert"} $ (const @{const_name erase} $ x) $ xs) (const @{const_name "fempty"})
                               (map (parse_term ctxt) frame)
    val op_term = check_term ctxt (
                      const @{const_name CMLIOpR} 
                      $ mk_prod_ty ctxt inp 
                      $ read_term (vty ctxt) outt
                      $ pre_term
                      $ post_term
                      $ frame_set)
      val ((_,(_,thm1)), ctxt1) = define (mk_defn id "pre_" pre_term) ctxt
      val ((_,(_,thm2)), ctxt2) = define (mk_defn id "post_" post_term) ctxt1
      val ((_,(_,thm3)), ctxt3) = define (mk_defn id "" op_term) ctxt2
  in 
      ctxt3
  end;
  
fun mk_efun ((id, (inp, out)), ((pre, post), body)) ctxt =
  let val pre_term = check_term (n_pexpr ctxt) (mk_lambda inp (parse_term (n_pexpr ctxt) pre) ctxt)
      val body_type = parse_term (vty ctxt) out
      val body_inner = const @{const_name "CoerceD"} 
                       $ parse_term (n_pexpr ctxt) body (* FIXME: Do something with the postcondition *)
                       $ body_type
      val body_term = check_term (n_pexpr ctxt) (
                         mk_lambda inp (
                           (if (pre = "true") then body_inner
                                              else const @{const_name IfThenElseD}
                                                 $ parse_term (n_pexpr ctxt) pre
                                                 $ body_inner 
                                                 $ const @{const_name BotDE})) ctxt)
      val ((_,(_,thm1)), ctxt1) = define (mk_defn id "pre_" pre_term) ctxt
      val ((_,(_,thm2)), ctxt2) = define (mk_defn id "" body_term) ctxt1
  in 
      ctxt2
  end;

fun mk_ifun ((id, (inp, out)), (pre, post)) ctxt = 
  let val pctxt = (Config.put Syntax.root @{nonterminal "n_pexpr"} ctxt)
      val tctxt = (Config.put Syntax.root @{nonterminal "vty"} ctxt)
      val preb = (Binding.name ("pre_" ^ id), NoSyn)
      val preb_term = Syntax.check_term pctxt (mk_lambda inp (Syntax.parse_term pctxt pre) ctxt)
      val preb_type = type_of preb_term
      val preb_def = ( (Binding.name ("pre_" ^ id ^ "_def"), [add_evalp]), preb_term)
      val postb = (Binding.name ("post_" ^ id), NoSyn)
      val postb_term = (Syntax.check_term pctxt 
                          (Const (@{const_name "comp"}, dummyT) 
                            $ (mk_lambda (out :: inp) (Syntax.parse_term pctxt post) ctxt)
                            $ Const (@{const_abbrev "swap"}, dummyT)))
      val postb_def = ( (Binding.name ("post_" ^ id ^ "_def"), [add_evalp]), postb_term) 
      val inpt = mk_prod_ty ctxt inp
      val outt = read_term tctxt (snd out)
      val bodyb = (Binding.name id, NoSyn)
      val bodyb_def = ( (Binding.name (id ^ "_def"), [add_evalp])
                      ,  Syntax.check_term ctxt (Const (@{const_name mk_ifun_body}, dummyT)
                           $ inpt $ outt $ preb_term $ postb_term))
      val ((_,(_,thm1)), ctxt1) = Local_Theory.define (preb, preb_def) ctxt
      val ((_,(_,thm2)), ctxt2) = Local_Theory.define (postb, postb_def) ctxt1
      val ((_,(_,thm3)), ctxt3) = Local_Theory.define (bodyb, bodyb_def) ctxt2
  in 
     ctxt3
  end;

fun mk_acts acts ctxt = 
  let val act_tuple = (foldr1 (fn (x, y) => const @{const_name "Abs_aprod"} $ (const @{const_name Pair} $ x $ y)) 
                                      (map (parse_term (n_upred ctxt) o snd) acts))
      val block = check_term (n_upred ctxt) (const @{const_name "gfp"} $ (mk_act_lambda (map fst acts) act_tuple ctxt))
      val ((block_term, _), ctxt1) = define (mk_defn "ActionBlock" "" block) ctxt
      fun actfun (x :: xs) n = actfun xs (n + 1) o snd o (define (mk_defn x "" (check_term ctxt1 (mk_n_of_m n (length acts - 1) $ block_term))))
        | actfun [] _ = fn x => x
  in actfun (map fst acts) 0 ctxt1
  end

val inps1_pr = Parse.enum1 "and" (Parse.short_ident -- (@{keyword "::"} |-- Parse.term));
val outs_pr = Parse.short_ident -- (@{keyword "::"} |-- Parse.term)

val ifun_pr = Parse.short_ident 
                  -- ((@{keyword "inp"} |-- inps1_pr) -- (@{keyword "out"} |-- outs_pr))
                  -- (Scan.optional (@{keyword "pre"} |-- Parse.term) "true"
                      -- (@{keyword "post"} |-- Parse.term));

val efun_pr = Parse.short_ident 
                  -- ((@{keyword "inp"} |-- inps1_pr) -- (@{keyword "out"} |-- Parse.term))
                  -- ((Scan.optional (@{keyword "pre"} |-- Parse.term) "true"
                  --  (Scan.optional (@{keyword "post"} |-- Parse.term) "true"))
                  --  (@{keyword "is"} |-- Parse.term));



val eop_pr = Parse.short_ident 
                  -- ((Scan.optional (@{keyword "inp"} |-- inps1_pr) [("null_input", "()")])
                      -- (Scan.optional (@{keyword "out"} |-- Parse.term) "()"))
                  -- ((Scan.optional (@{keyword "pre"} |-- Parse.term) "true"
                  --  (Scan.optional (@{keyword "post"} |-- Parse.term) "true"))
                  --  (@{keyword "is"} |-- Parse.term));

val iop_pr = Parse.short_ident 
                  -- ((Scan.optional (@{keyword "inp"} |-- inps1_pr) [("null_input", "()")])
                      -- (Scan.optional (@{keyword "out"} |-- outs_pr) ("RESULT", "()")))
                  -- ((Scan.optional (@{keyword "frame"} |-- Scan.repeat1 Parse.short_ident) []) 
                  -- (Scan.optional (@{keyword "pre"} |-- Parse.term) "true"
                      -- (@{keyword "post"} |-- Parse.term)));

val acts_pr = Parse.enum1 "and" ((Parse.short_ident --| @{keyword "="}) -- Parse.term);

end;




Scan.optional;

Outer_Syntax.local_theory  @{command_spec "cmlefun"} 
"Explicit CML function" 
(CmlCommands.efun_pr >> CmlCommands.mk_efun);

Outer_Syntax.local_theory  @{command_spec "cmlifun"} 
"Implicit CML function" 
(CmlCommands.ifun_pr >> CmlCommands.mk_ifun);

Outer_Syntax.local_theory  @{command_spec "cmliop"} 
"Implicit CML operation" 
(CmlCommands.iop_pr >> CmlCommands.mk_iop);

Outer_Syntax.local_theory  @{command_spec "cmleop"} 
"Explicit CML operation" 
(CmlCommands.eop_pr >> CmlCommands.mk_eop);

Outer_Syntax.local_theory @{command_spec "cmlacts"}
"CML Action block"
(CmlCommands.acts_pr >> CmlCommands.mk_acts);

*}

end

