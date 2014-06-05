(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_process.thy                                                  *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* CML processes *}

theory utp_cml_process
imports 
  utp_cml_expr
  utp_cml_types
  utp_csp
begin


text {* Add a simple syntax translator for main actions in CML processes. The ML
        function simply appends .MainAction
        FIXME: We also need to support parameters. *}

syntax
  "_cml_proc_ref_0" :: "id \<Rightarrow> n_upred" ("@_'(')" [10] 10)
  "_cml_proc_ref_1" :: "id \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("@_'(_')" [10,10] 10)
  "_cml_proc_ref_2" :: "id \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("@_'(_,/ _')" [10,10,10] 10)
  "_cml_proc_ref_3" :: "id \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("@_'(_,/ _,/ _')" [10,10,10,10] 10)

parse_ast_translation {*
let
  fun cml_proc_ref_tr_0 [Ast.Variable full_name] =
    Ast.Variable (full_name ^ ".MainAction")
  | cml_proc_ref_tr_0 e = raise Match;
  fun cml_proc_ref_tr_1 [Ast.Variable full_name, p] =
    Ast.Appl [Ast.Constant @{const_syntax Op1PP}, Ast.Variable (full_name ^ ".MainAction"), p]
  | cml_proc_ref_tr_1 e = raise Match;
  fun cml_proc_ref_tr_2 [Ast.Variable full_name, p, q] =
    Ast.Appl [Ast.Constant @{const_syntax Op2PP}, Ast.Variable (full_name ^ ".MainAction"), p, q]
  | cml_proc_ref_tr_2 e = raise Match;
  fun cml_proc_ref_tr_3 [Ast.Variable full_name, p, q, r] =
    Ast.Appl [Ast.Constant @{const_syntax Op3PP}, Ast.Variable (full_name ^ ".MainAction"), p, q, r]
  | cml_proc_ref_tr_3 e = raise Match;
in
  [(@{syntax_const "_cml_proc_ref_0"}, K cml_proc_ref_tr_0)
  ,(@{syntax_const "_cml_proc_ref_1"}, K cml_proc_ref_tr_1)
  ,(@{syntax_const "_cml_proc_ref_2"}, K cml_proc_ref_tr_2)
  ,(@{syntax_const "_cml_proc_ref_3"}, K cml_proc_ref_tr_3)]
end
*}

definition ForLoopSetD :: "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"ForLoopSetD xs F = undefined"

definition ParallelD :: 
  "cmlp \<Rightarrow> cmlev set \<Rightarrow> cmlp \<Rightarrow> cmlp" where
"ParallelD p cs q = ParallelCSP p (LitPE (Abs_USET cs)) q"

definition ReplSeqSetD ::
  "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"ReplSeqSetD = undefined"

definition ReplIntSetD ::
  "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"ReplIntSetD = undefined"

definition ReplExtSetD ::
  "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"ReplExtSetD = undefined"

definition ReplExtTyD ::
  "'a set \<Rightarrow> ('a option \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"ReplExtTyD = undefined"

definition ReplParSetD ::
  "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"ReplParSetD = undefined"

definition ReplAlphaParSetD ::
  "'a fset cmle \<Rightarrow> cmlev set \<Rightarrow> ('a option \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"ReplAlphaParSetD = undefined"

definition ReplInlvSetD ::
  "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"ReplInlvSetD = undefined"

definition HideD ::
  "cmlp \<Rightarrow> cmlev set \<Rightarrow> cmlp" where
"HideD p cs = undefined"

definition InterruptD :: "cmlp \<Rightarrow> cmlp \<Rightarrow> cmlp" where
"InterruptD p q = undefined"

definition TimeoutD :: "cmlp \<Rightarrow> real cmle \<Rightarrow> cmlp \<Rightarrow> cmlp" where
"TimeoutD p n q = undefined"

definition WaitD :: "real cmle \<Rightarrow> cmlp" where
"WaitD n = undefined"

abbreviation MkChanD :: "string \<Rightarrow> 'a set \<Rightarrow> ('a option) CHAN" where
"MkChanD n xs \<equiv> MkCHAN (bName n, TYPE('a option))"

abbreviation CommD :: "unit option CHAN \<Rightarrow> cmlp \<Rightarrow> cmlp" where
"CommD x p \<equiv> OutputCSP x |()| p"


(* FIXME: Execution of CML operations needs to take care of undefinedness *)

(* FIXME: Surely these can all be unified into a single thing ... *)

definition AssignC :: "'a cmlvar \<Rightarrow> 'a cmle \<Rightarrow> cmlp" where
"AssignC x v = `\<lparr> defn(@v) \<rparr> \<turnstile> x := @v`"

definition Exec0D :: "cmlp \<Rightarrow> cmlp" where
"Exec0D p = p"

lift_definition Exec1D :: 
  "('a option \<Rightarrow> cmlp) \<Rightarrow> 'a cmle \<Rightarrow> cmlp" 
  is "\<lambda> P e. {b :: cmlv binding. b \<in> P (e b)}" .

lift_definition Exec2D :: 
  "('a option \<Rightarrow> 'b option \<Rightarrow> cmlp) \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> cmlp" 
  is "\<lambda> P e f. {b :: cmlv binding. b \<in> P (e b) (f b)}" .

lift_definition Exec3D :: 
  "('a option \<Rightarrow> 'b option \<Rightarrow> 'c option \<Rightarrow> cmlp) 
   \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> 'c cmle \<Rightarrow> cmlp" 
  is "\<lambda> P e f g. {b :: cmlv binding. b \<in> P (e b) (f b) (g b)}" .

lift_definition Exec4D :: 
  "('a option \<Rightarrow> 'b option \<Rightarrow> 'c option \<Rightarrow> 'd option \<Rightarrow> cmlp) 
   \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> 'c cmle \<Rightarrow> 'd cmle \<Rightarrow> cmlp" 
  is "\<lambda> P e f g h. {b :: cmlv binding. b \<in> P (e b) (f b) (g b) (h b)}" .

lift_definition Exec5D :: 
  "('a option \<Rightarrow> 'b option \<Rightarrow> 'c option \<Rightarrow> 'd option \<Rightarrow> 'e option \<Rightarrow> cmlp) 
   \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> 'c cmle \<Rightarrow> 'd cmle \<Rightarrow> 'e cmle \<Rightarrow> cmlp" 
  is "\<lambda> P e f g h i. {b :: cmlv binding. b \<in> P (e b) (f b) (g b) (h b) (i b)}" .

lift_definition Exec6D :: 
  "('a option \<Rightarrow> 'b option \<Rightarrow> 'c option \<Rightarrow> 'd option \<Rightarrow> 'e option \<Rightarrow> 'f option \<Rightarrow> cmlp) 
   \<Rightarrow> 'a cmle \<Rightarrow> 'b cmle \<Rightarrow> 'c cmle \<Rightarrow> 'd cmle \<Rightarrow> 'e cmle \<Rightarrow> 'f cmle \<Rightarrow> cmlp" 
  is "\<lambda> P e f g h i j. {b :: cmlv binding. b \<in> P (e b) (f b) (g b) (h b) (i b) (j b)}" .

definition IndexD :: "('a \<Rightarrow> cmlp) \<Rightarrow> 'a cmle \<Rightarrow> cmlp"
where "IndexD F v = mkPRED {b. \<lbrakk>F(the(\<lbrakk>v\<rbrakk>\<^sub>*b))\<rbrakk>b}"

(* We remove the standard definition of prefix and add one specific for CML *)

no_syntax
  "_n_upred_prefixed"  :: "n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_ -> _")
  "_n_upred_index"         :: "('b \<Rightarrow> 'a upred) \<Rightarrow> 'b \<Rightarrow> n_upred" ("_<_>" 50)
  "_n_upred_input"     :: "'a CHAN \<Rightarrow> pttrn \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_?_ -> _")
  "_n_upred_output"    :: "'a CHAN \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_!_ -> _")
  "_n_upred_event"     :: "'a CHAN \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_._ -> _")

no_syntax (xsymbols)
  "_n_upred_prefixed"  :: "n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_ \<rightarrow> _")

nonterminal n_chanset and n_chan and n_chans and n_comm and n_comms

term "SUP x:A. PrefixCSP x p"

syntax
  "_n_chan_ev"       :: "idt => idt => n_chan"  ("_@_")
  "_n_chan_ch"       :: "idt => n_chan" ("_")
  "_n_chan"          :: "n_chan => n_chans" ("_")
  "_n_chans"         :: "[n_chan, n_chans] => n_chans" ("_,/ _")
  "_n_chanset_id"    :: "idt \<Rightarrow> n_chanset" ("_")
  "_n_chanset_enum"  :: "n_chans => n_chanset" ("{|(_)|}")
  "_n_chanset_union" :: "n_chanset \<Rightarrow> n_chanset \<Rightarrow> n_chanset" (infixl "union" 65)
  "_n_chanset_inter" :: "n_chanset \<Rightarrow> n_chanset \<Rightarrow> n_chanset" (infixl "inter" 70)
  "_n_chanset_diff"  :: "n_chanset \<Rightarrow> n_chanset \<Rightarrow> n_chanset" (infixl "\\" 70)

translations
  "_n_chan_ev c v"   => "CONST insert (CONST PEV c v) {}"
  "_n_chan_ch c"     => "CONST MkEvents {c\<down>}"
  "_n_chan cs"       => "cs"
  "_n_chans cs1 cs2" => "cs1 \<union> cs2"
  "_n_chanset_id x"    => "x"
  "_n_chanset_enum cs" => "cs"
  "_n_chanset_union cs1 cs2" => "cs1 \<union> cs2"
  "_n_chanset_inter cs1 cs2" => "cs1 \<inter> cs2"
  "_n_chanset_diff  cs1 cs2" => "cs1 - cs2"

syntax
(*  "_n_upred_cml_prefix" :: "unit option CHAN \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_ -> _") *)
  "_n_upred_parcml"     :: "n_upred \<Rightarrow> n_chanset \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixl "[|_|]" 50)
  "_n_upred_aseqsetcml" :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("; _ in @set _ @ _" [0,0,10] 10)
  "_n_upred_aextsetcml" :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("[] _ in @set _ @ _" [0,0,10] 10)
  "_n_upred_aexttycml"  :: "idt \<Rightarrow> vty \<Rightarrow> n_upred \<Rightarrow> n_upred" ("[] _ : _ @ _" [0,0,10] 10)
  "_n_upred_aintsetcml" :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("|~| _ in @set _ @ _" [0,0,10] 10)
  "_n_upred_aparsetcml"   :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("|| _ in @set _ @ _" [0,0,10] 10)
  "_n_upred_aparsetevcml" :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_chanset \<Rightarrow> n_upred \<Rightarrow> n_upred" ("|| _ in @set _ @ [_] _" [0,0,0,10] 10)
  "_n_upred_ainlvsetcml" :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("||| _ in @set _ @ _" [0,0,10] 10)
  "_n_upred_hidecml"    :: "n_upred \<Rightarrow> n_chanset \<Rightarrow> n_upred" (infixl "\\" 60)
  "_n_upred_intrptcml"  :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixl "'/-\\" 50)
  "_n_upred_timeoutcml" :: "n_upred \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixl "['(_')>" 50)
  "_n_upred_waitcml"    :: "n_pexpr \<Rightarrow> n_upred" ("WAIT _")
  "_n_upred_cml_exec0"  :: "idt \<Rightarrow> n_upred" ("_'(')")
  "_n_upred_cml_exec1"  :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_'(_')")
  "_n_upred_cml_exec2"  :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_'(_, _')")
  "_n_upred_cml_exec3"  :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_'(_, _, _')")
  "_n_upred_cml_exec4"  :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_'(_, _, _, _')")
  "_n_upred_cml_exec5"  :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_'(_, _, _, _, _')")
  "_n_upred_cml_exec6"  :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_'(_, _, _, _, _, _')")
  "_n_upred_cindex"     :: "('b \<Rightarrow> 'a upred) \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_<_>" 50)

translations
  "_n_upred_parcml p vs q"        == "CONST ParallelD p vs q"
  "_n_upred_aseqsetcml x vs p"    == "CONST ReplSeqSetD vs (\<lambda> x. p)"
  "_n_upred_aintsetcml x vs p"    == "CONST ReplIntSetD vs (\<lambda> x. p)"
  "_n_upred_aextsetcml x vs p"    == "CONST ReplExtSetD vs (\<lambda> x. p)"
  "_n_upred_aexttycml x vs p"     == "CONST ReplExtTyD vs (\<lambda> x. p)"
  "_n_upred_aparsetcml x vs p"    == "CONST ReplParSetD vs (\<lambda> x. p)" 
  "_n_upred_aparsetevcml x vs es p" == "CONST ReplAlphaParSetD vs es (\<lambda> x. p)"
  "_n_upred_ainlvsetcml x vs p"   == "CONST ReplInlvSetD vs (\<lambda> x. p)"
  "_n_upred_hidecml p cs"         == "CONST HideD p cs"
  "_n_upred_intrptcml p q"        == "CONST InterruptD p q"
  "_n_upred_timeoutcml p n q"     == "CONST TimeoutD p n q"
  "_n_upred_waitcml n"            == "CONST WaitD n"
(*  "_n_upred_cml_prefix n p"       == "CONST CommD n p" *)
  "_n_upred_cml_exec0 s"          == "CONST RH (CONST Exec0D s)"
  "_n_upred_cml_exec1 f s"        == "CONST RH (CONST Exec1D f s)"
  "_n_upred_cml_exec2 v1 v2 s"    == "CONST RH (CONST Exec2D v1 v2 s)"
  "_n_upred_cml_exec3 v1 v2 v3 s" == "CONST RH (CONST Exec3D v1 v2 v3 s)"
  "_n_upred_cml_exec3 v1 v2 v3 v4 s" == "CONST RH (CONST Exec3D v1 v2 v3 v4 s)"
  "_n_upred_cml_exec3 v1 v2 v3 v4 v5 s" == "CONST RH (CONST Exec3D v1 v2 v3 v4 v5 s)"
  "_n_upred_cml_exec3 v1 v2 v3 v4 v5 v6 s" == "CONST RH (CONST Exec3D v1 v2 v3 v4 v5 v6 s)"
  "_n_upred_cindex F v"           == "CONST IndexD F v"

term "`([] i in @set {1,2,3} @ P) ; Q`"
term "`|| i in @set {1,2,3} @ P [(&i)> Q`"
term "`||| i in @set {1,2,3} @ (P [(&i)> Q)`"
term "`; i in @set {1,2,3} @ (P [(&i)> Q)`"
term "`[] i in @set {1,2,3} @ (P [(&i)> Q)`"
term "`[] i : @nat @ (P [(&i)> Q)`"
term "`|| i in @set {1,2,3} @ [{|v|}] (P [(&i)> Q)`"
term "`P [|{|x,y,z|}|] Q`"
term "`P \\ {|x,y,z|}`"
term "`P \\ {|x,y|} union {|z|}`"
term "`P \\ xs`"
term "`P /-\\ Q`"
term "`P [(5)> Q`"
term "`WAIT $x ; WAIT $y`"
term "`f()`"
term "`P<1>`"

text {* CML event prefix syntax *}

no_syntax
  "_n_upred_prefixed"      :: "n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_ -> _")
  "_n_upred_index"         :: "('b \<Rightarrow> 'a upred) \<Rightarrow> 'b \<Rightarrow> n_upred" ("_<_>" 50)
  "_n_upred_PrefixSkipCSP" :: "n_pexpr \<Rightarrow> n_upred" ("@_")

syntax
  "_n_comm_nil"      :: "n_comm" ("")
  "_n_comm_inp"      :: "idt \<Rightarrow> n_comm \<Rightarrow> n_comm" ("?'(_')_")
  "_n_comm_outp"     :: "n_pexpr \<Rightarrow> n_comm \<Rightarrow> n_comm" ("!'(_')_")
  "_n_comm_dot"      :: "n_pexpr \<Rightarrow> n_comm \<Rightarrow> n_comm" (".'(_')_")
  "_cml_comm"        :: "idt \<Rightarrow> n_comm \<Rightarrow> n_upred \<Rightarrow> n_upred" ("__ -> _" [20,50,50] 50)
  "_cml_comm_body"   :: "idt \<Rightarrow> n_comm \<Rightarrow> n_upred \<Rightarrow> n_upred"
  "_cml_comm_bind"   :: "n_comm \<Rightarrow> idt \<Rightarrow> n_comm \<Rightarrow> n_upred \<Rightarrow> n_upred \<Rightarrow> logic"
  "_cml_comm_prod"   :: "n_comm \<Rightarrow> logic"

translations
  "_cml_comm c _n_comm_nil (_n_upred_SkipCSP)" <= "CONST CommD c SKIP"

text {* This rather complex set of translations performs two passes over a list 
        of channel variables:
        - in the first pass, a big external choice is entered for each input, and all
          other kinds are ignored
        - in the second pass, each variable is inserted into a tuple and then composed
          with the channel. 
       FIXME: Currently we don't insert correct type data for the external choice,
              this should be extracted somehow from the channel.
*}

translations
  "_cml_comm_prod (_n_comm_nil)" => "CONST UnitD"
  "_cml_comm_prod (_n_comm_dot v _n_comm_nil)" => "CONST SingleD v"
  "_cml_comm_prod (_n_comm_dot v vs)"  => "CONST vexpr_prod v (_cml_comm_prod vs)"
  "_cml_comm_prod (_n_comm_inp v _n_comm_nil)" => "CONST SingleD (CONST LitPE v)"
  "_cml_comm_prod (_n_comm_inp x vs)"  => "CONST vexpr_prod (CONST LitPE x) (_cml_comm_prod vs)"
  "_cml_comm_prod (_n_comm_outp v _n_comm_nil)" => "CONST SingleD v"
  "_cml_comm_prod (_n_comm_outp v vs)" => "CONST vexpr_prod v (_cml_comm_prod vs)"
  "_cml_comm_bind (_n_comm_nil) c v p" => "_cml_comm_body c v p"
  "_cml_comm_bind (_n_comm_dot x _n_comm_nil) c v p" => "_cml_comm_body c v p"
  "_cml_comm_bind (_n_comm_dot x vs) c v p"  => "_cml_comm_bind vs c v p"
  "_cml_comm_bind (_n_comm_inp x _n_comm_nil) c v p" 
      => "CONST ReplExtTyD CONST UNIV (\<lambda> x. (_cml_comm_body c v p))"
  "_cml_comm_bind (_n_comm_inp x vs) c v p"  
      => "CONST ReplExtTyD CONST UNIV (\<lambda> x. (_cml_comm_bind vs c v p))"
  "_cml_comm_bind (_n_comm_outp x _n_comm_nil) c v p" => "_cml_comm_body c v p"
  "_cml_comm_bind (_n_comm_outp x vs) c v p"  => "_cml_comm_bind vs c v p"
  "_cml_comm_body c v p"               => "CONST OutputCSP c (_cml_comm_prod v) p"
  "_cml_comm c v p"                    => "_cml_comm_bind v c v p"

end