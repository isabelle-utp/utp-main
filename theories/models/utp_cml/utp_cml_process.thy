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

term "MkVarD"

definition ForLoopSetD :: "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"ForLoopSetD xs F = undefined"

definition ParallelD :: 
  "cmlp \<Rightarrow> cmlev set \<Rightarrow> cmlp \<Rightarrow> cmlp" where
"ParallelD p cs q = ParallelCSP p (LitPE (Abs_USET cs)) q"

definition AlphaSeqSetD ::
  "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"AlphaSeqSetD = undefined"

definition AlphaIntSetD ::
  "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"AlphaIntSetD = undefined"

definition AlphaExtSetD ::
  "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"AlphaExtSetD = undefined"

definition AlphaParSetD ::
  "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"AlphaParSetD = undefined"

definition AlphaInlvSetD ::
  "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> cmlp) \<Rightarrow> cmlp" where
"AlphaInlvSetD = undefined"

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

no_syntax (xsymbols)
  "_n_upred_prefixed"  :: "n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_ \<rightarrow> _")

nonterminal n_chanset and n_chan and n_chans

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
  "_n_upred_cml_prefix" :: "unit option CHAN \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_ -> _")
  "_n_upred_parcml"     :: "n_upred \<Rightarrow> n_chanset \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixl "[|_|]" 50)
  "_n_upred_aseqsetcml" :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("; _ in @set _ @ _")
  "_n_upred_aextsetcml" :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("[] _ in @set _ @ _")
  "_n_upred_aintsetcml" :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("|~| _ in @set _ @ _")
  "_n_upred_aparsetcml" :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("|| _ in @set _ @ _")
  "_n_upred_ainlvsetcml" :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("||| _ in @set _ @ _")
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
  "_n_upred_aseqsetcml x vs p"    == "CONST AlphaSeqSetD vs (\<lambda> x. p)"
  "_n_upred_aintsetcml x vs p"    == "CONST AlphaIntSetD vs (\<lambda> x. p)"
  "_n_upred_aextsetcml x vs p"    == "CONST AlphaExtSetD vs (\<lambda> x. p)"
  "_n_upred_aparsetcml x vs p"    == "CONST AlphaParSetD vs (\<lambda> x. p)" 
  "_n_upred_ainlvsetcml x vs p"   == "CONST AlphaInlvSetD vs (\<lambda> x. p)"
  "_n_upred_hidecml p cs"         == "CONST HideD p cs"
  "_n_upred_intrptcml p q"        == "CONST InterruptD p q"
  "_n_upred_timeoutcml p n q"     == "CONST TimeoutD p n q"
  "_n_upred_waitcml n"            == "CONST WaitD n"
  "_n_upred_cml_prefix n p"       == "CONST CommD n p"
  "_n_upred_cml_exec0 s"          == "CONST RH (CONST Exec0D s)"
  "_n_upred_cml_exec1 f s"        == "CONST RH (CONST Exec1D f s)"
  "_n_upred_cml_exec2 v1 v2 s"    == "CONST RH (CONST Exec2D v1 v2 s)"
  "_n_upred_cml_exec3 v1 v2 v3 s" == "CONST RH (CONST Exec3D v1 v2 v3 s)"
  "_n_upred_cml_exec3 v1 v2 v3 v4 s" == "CONST RH (CONST Exec3D v1 v2 v3 v4 s)"
  "_n_upred_cml_exec3 v1 v2 v3 v4 v5 s" == "CONST RH (CONST Exec3D v1 v2 v3 v4 v5 s)"
  "_n_upred_cml_exec3 v1 v2 v3 v4 v5 v6 s" == "CONST RH (CONST Exec3D v1 v2 v3 v4 v5 v6 s)"
  "_n_upred_cindex F v"           == "CONST IndexD F v"

term "`|| i in @set {1,2,3} @ (P [(&i)> Q)`"
term "`||| i in @set {1,2,3} @ (P [(&i)> Q)`"
term "`; i in @set {1,2,3} @ (P [(&i)> Q)`"
term "`[] i in @set {1,2,3} @ (P [(&i)> Q)`"
term "`P [|{|x,y,z|}|] Q`"
term "`P \\ {|x,y,z|}`"
term "`P \\ {|x,y|} union {|z|}`"
term "`P \\ xs`"
term "`P /-\\ Q`"
term "`P [(5)> Q`"
term "`WAIT $x ; WAIT $y`"
term "`f()`"
term "`P<1>`"


end