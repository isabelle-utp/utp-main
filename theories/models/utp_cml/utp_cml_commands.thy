(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_commands.thy                                                 *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Commands to construct CML definitions *}

theory utp_cml_commands
imports 
  utp_cml_functions
keywords "cmlifun" "cmlefun" :: thy_decl and "inp" "out" "pre" "post"
begin

abbreviation "swap \<equiv> \<lambda> (x,y). (y, x)"                                          

definition mk_ifun_body :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> bool cmle) \<Rightarrow> (('a * 'b) \<Rightarrow> bool cmle) \<Rightarrow> ('a * 'b) set" where
"mk_ifun_body A B pre post 
  = {(x,y) | x y. x \<in> A \<and> y \<in> B \<and> \<lbrakk>pre(x)\<rbrakk>\<^sub>*\<B> = Some True \<and> \<lbrakk>post(x,y)\<rbrakk>\<^sub>*\<B> = Some True}"

declare mk_ifun_body_def [evalp]

ML {*
fun subst_free nm e (u $ t) = subst_free nm e u $ subst_free nm e t
  | subst_free nm e (Free (x, t)) = if (x = nm) then e else Free (x, t)
  | subst_free nm e (Abs (y, ty, tr)) = if (nm = y) then (Abs (y, ty, tr)) else (Abs (y, ty, subst_free nm e tr))
  | subst_free _ _ t = t;

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

val add_evalp = Attrib.internal (K (Thm.declaration_attribute evalp.add_thm));

fun mk_efun ((id, (inp, out)), ((pre, post), body)) ctxt =
  let val pctxt = (Config.put Syntax.root @{nonterminal "n_pexpr"} ctxt)
      val tctxt = (Config.put Syntax.root @{nonterminal "vty"} ctxt)
      val preb = (Binding.name ("pre_" ^ id), NoSyn)
      val preb_term = Syntax.check_term pctxt (mk_lambda inp (Syntax.parse_term pctxt pre) ctxt)
      val preb_type = type_of preb_term
      val preb_def = ( (Binding.name ("pre_" ^ id ^ "_def"), [add_evalp]), preb_term)
      val bodyb = (Binding.name id, NoSyn)
      val bodyb_type = Syntax.parse_term tctxt out
      val bodyb_inner = Syntax.const @{const_name "CoerceD"} 
                        $ Syntax.parse_term pctxt body (* FIXME: Do something with the postcondition *)
                        $ bodyb_type
      val bodyb_def = ( (Binding.name (id ^ "_def"), [add_evalp])
                      ,  Syntax.check_term pctxt (
                           mk_lambda inp (
                             (if (pre = "true") then bodyb_inner
                                                else Syntax.const @{const_name IfThenElseD}
                                                   $ Syntax.parse_term pctxt pre
                                                   $ bodyb_inner 
                                                   $ Syntax.const @{const_name BotDE})) ctxt))
      val ((_,(_,thm1)), ctxt1) = Local_Theory.define (preb, preb_def) ctxt
      val ((_,(_,thm2)), ctxt2) = Local_Theory.define (bodyb, bodyb_def) ctxt1
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
      val inpt = foldr1 (fn (x,y) => 
            (Syntax.check_term ctxt (Syntax.const @{const_abbrev "vty_prod"} $ x $ y)))
                                     (map (Syntax.read_term tctxt o snd) inp)
      val outt = Syntax.read_term tctxt (snd out)
      val ppctxt = ((Local_Theory.define (preb, preb_def) #> snd) o
                    (Local_Theory.define (postb, postb_def) #> snd)) ctxt
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

(*
fun mk_iop ((id, (inp, out)), (pre, post)) ctxt = 
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
      val inpt = foldr1 (fn (x,y) => 
            (Syntax.check_term ctxt (Syntax.const @{const_abbrev "vty_prod"} $ x $ y)))
                                     (map (Syntax.read_term tctxt o snd) inp)
      val outt = Syntax.read_term tctxt (snd out)
      val ppctxt = ((Local_Theory.define (preb, preb_def) #> snd) o
                    (Local_Theory.define (postb, postb_def) #> snd)) ctxt
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
*)

val inps_parser = Parse.enum1 "and" (Parse.short_ident -- (@{keyword "::"} |-- Parse.term));
val outs_parser = Parse.short_ident -- (@{keyword "::"} |-- Parse.term)

val cmlifun_parser = Parse.short_ident 
                  -- ((@{keyword "inp"} |-- inps_parser) -- (@{keyword "out"} |-- outs_parser))
                  -- (Scan.optional (@{keyword "pre"} |-- Parse.term) "true"
                      -- (@{keyword "post"} |-- Parse.term));

val cmlefun_parser = Parse.short_ident 
                  -- ((@{keyword "inp"} |-- inps_parser) -- (@{keyword "out"} |-- Parse.term))
                  -- ((Scan.optional (@{keyword "pre"} |-- Parse.term) "true"
                  --  (Scan.optional (@{keyword "post"} |-- Parse.term) "true"))
                  --  (@{keyword "is"} |-- Parse.term));

Outer_Syntax.local_theory  @{command_spec "cmlefun"} 
"Explicit CML function" 
(cmlefun_parser >> mk_efun);

Outer_Syntax.local_theory  @{command_spec "cmlifun"} 
"Implicit CML function" 
(cmlifun_parser >> mk_ifun);

*}

ML {*  *}

ML {* Attrib.internal (K Simplifier.simp_add) *}


cmlifun mydiv
  inp x :: "@nat" and y :: "@nat"
  out z :: "@nat"
  pre "&y > 0" 
  post "&z = floor (&x / &y)"

thm evalp

print_theorems

cmlefun myadd
  inp x :: "@nat" and y :: "@nat"
  out "@real"
  pre "&x > 0"
  is "&x + &y"

thm evalp

lemma "((4,2),2) \<in> mydiv"
  by (simp add:evalp)

end

