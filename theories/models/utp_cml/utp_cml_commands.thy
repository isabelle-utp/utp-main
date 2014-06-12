(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_commands.thy                                                 *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Commands to construct CML definitions *}

theory utp_cml_commands
imports 
  utp_cml_functions
keywords "cmlifun" :: thy_decl and "inps" "outs" "pre" "post"
begin



ML {* 
foldr1 (fn (x,y) => Syntax.const (unprefix "\<^const>" @{const_syntax vty_prod}) $ x $ y);


fun mk_fun ((id, (inp, out)), (pre, post)) ctxt = 
  let val pctxt = (Config.put Syntax.root (unprefix "\<^type>" @{type_syntax "n_pexpr"}) ctxt)
      val tctxt = (Config.put Syntax.root (unprefix "\<^type>" @{type_syntax "vty"}) ctxt)
      val preb = (Binding.name ("pre_" ^ id), NoSyn)
      val preb_def = ( (Binding.name ("pre_" ^ id ^ "_def"), [])
                     , Syntax.read_term pctxt pre)
      val postb = (Binding.name ("post_" ^ id), NoSyn)
      val postb_def = ( (Binding.name ("post_" ^ id ^ "_def"), [])
                      , Syntax.read_term pctxt post)
      val inpt = (Binding.name ("inp_" ^ id), NoSyn)
      val inpt_def = ( (Binding.name ("inp_" ^ id ^ "_def"), [])
                     , foldr1 (fn (x,y) => @{term "vty_prod"} $ x $ y) (map (Syntax.read_term tctxt o snd) inp))
  in
    ((Local_Theory.define (preb, preb_def) #> snd) o 
     (Local_Theory.define (postb, postb_def) #> snd) o
     (Local_Theory.define (inpt, inpt_def) #> snd)) ctxt
  end;

val inps_parser = Parse.enum1 "and" (Parse.short_ident -- (@{keyword "::"} |-- Parse.term));
val outs_parser = Parse.short_ident -- (@{keyword "::"} |-- Parse.term)

val cmlifun_parser = Parse.short_ident 
                  -- ((@{keyword "inps"} |-- inps_parser) -- (@{keyword "outs"} |-- outs_parser))
                  -- ((Parse.command_name "pre" |-- Parse.term)
                      -- (@{keyword "post"} |-- Parse.term));


Parse.short_ident -- (Parse.$$$ "pre");

Outer_Syntax.local_theory  @{command_spec "cmlifun"} 
"Implicit CML function" 
(cmlifun_parser >> mk_fun) 
*}

cmlifun mythang 
  inps x :: "@nat" 
  outs y :: "@nat"
  pre "forall x : @nat @ &x > 5" 
  post "1 + 1"

thm inp_mythang_def

end

