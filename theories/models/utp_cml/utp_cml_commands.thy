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

abbreviation "swap \<equiv> \<lambda> (x,y). (y, x)"

definition mk_ifun_body :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> bool cmle) \<Rightarrow> (('a * 'b) \<Rightarrow> bool cmle) \<Rightarrow> ('a * 'b) set" where
"mk_ifun_body A B pre post 
  = {(x,y) | x y. x \<in> A \<and> y \<in> B \<and> \<lbrakk>pre(x)\<rbrakk>\<^sub>*\<B> = Some True \<and> \<lbrakk>post(x,y)\<rbrakk>\<^sub>*\<B> = Some True}"

ML {*
local
  fun absnm' x n (u $ t) = (absnm' x n u) $ (absnm' x n t)
    | absnm' x n (Free (y, t)) = if (x = y) then Bound n else Free (y, t)
    | absnm' x n (Abs (y, ty, tr)) = if (x = y) then (Abs (y, ty, tr)) else (Abs (y, ty, absnm' x n tr))
    | absnm' _ _ e = e;
in fun absnm (x, ty) n tr = Abs (x, ty, absnm' x n tr) end;

fun get_cml_holty ty ctxt =
  let val tctxt = (Config.put Syntax.root @{nonterminal "vty"} ctxt) in
  case (type_of (Syntax.read_term tctxt ty)) of
    Type (_, [ty]) => ty
  | x => error (@{make_string} x)
 end;

local
  fun mk_lambda' [(id, ty)] n term ctxt =
        absnm (id, get_cml_holty ty ctxt) n term
    | mk_lambda' ((id, ty) :: xs) n term ctxt =
        Const (@{const_name "prod_case"}, dummyT) $ absnm (id, get_cml_holty ty ctxt) n (mk_lambda' xs (n - 1) term ctxt)
    | mk_lambda' [] _ term _ = term;
in
  fun mk_lambda xs term ctxt = mk_lambda' xs (length xs - 1) term ctxt
end;

fun mk_fun ((id, (inp, out)), (pre, post)) ctxt = 
  let val pctxt = (Config.put Syntax.root @{nonterminal "n_pexpr"} ctxt)
      val tctxt = (Config.put Syntax.root @{nonterminal "vty"} ctxt)
      val preb = (Binding.name ("pre_" ^ id), NoSyn)
      val preb_term = Syntax.check_term pctxt (mk_lambda inp (Syntax.parse_term pctxt pre) ctxt)
      val preb_type = type_of preb_term
      val preb_def = ( (Binding.name ("pre_" ^ id ^ "_def"), []), preb_term)
      val postb = (Binding.name ("post_" ^ id), NoSyn)
      val postb_term = (Syntax.check_term pctxt 
                          (Const (@{const_name "comp"}, dummyT) 
                            $ (mk_lambda (out :: inp) (Syntax.parse_term pctxt post) ctxt)
                            $ Const (@{const_abbrev "swap"}, dummyT)))
      val postb_def = ( (Binding.name ("post_" ^ id ^ "_def"), []), postb_term) 
      val inpt = foldr1 (fn (x,y) => 
            (Syntax.check_term ctxt (Syntax.const @{const_abbrev "vty_prod"} $ x $ y)))
                                     (map (Syntax.read_term tctxt o snd) inp)
      val outt = Syntax.read_term tctxt (snd out)
      val ppctxt = ((Local_Theory.define (preb, preb_def) #> snd) o
                    (Local_Theory.define (postb, postb_def) #> snd)) ctxt
      val bodyb = (Binding.name id, NoSyn)
      val bodyb_def = ( (Binding.name (id ^ "_def"), [])
                      ,  Syntax.check_term ctxt (Const (@{const_name mk_ifun_body}, dummyT)
                           $ inpt $ outt $ preb_term $ postb_term))
  in 
    (Local_Theory.define (bodyb, bodyb_def) #> snd) ppctxt
  end;

val inps_parser = Parse.enum1 "and" (Parse.short_ident -- (@{keyword "::"} |-- Parse.term));
val outs_parser = Parse.short_ident -- (@{keyword "::"} |-- Parse.term)

val cmlifun_parser = Parse.short_ident 
                  -- ((@{keyword "inps"} |-- inps_parser) -- (@{keyword "outs"} |-- outs_parser))
                  -- ((Parse.command_name "pre" |-- Parse.term)
                      -- (@{keyword "post"} |-- Parse.term));

Outer_Syntax.local_theory  @{command_spec "cmlifun"} 
"Implicit CML function" 
(cmlifun_parser >> mk_fun) 

*}

cmlifun divide 
  inps x :: "@nat" and y :: "@nat"
  outs z :: "@nat"
  pre "&y > 0" 
  post "&z = floor (&x / &y)"

thm "pre_divide_def"
thm "post_divide_def"

lemma "((5,2),2) \<in> divide"
  apply (simp add:divide_def mk_ifun_body_def evalp)
  sledgehammer

end

