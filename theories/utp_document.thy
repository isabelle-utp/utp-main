(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_document.thy                                                     *)
(* Authors: Simon Foster and Frank Zeyda, University of York (UK)             *)
(******************************************************************************)

header {* Document Support *}

theory utp_document
imports Pure
keywords "paragraph" :: thy_heading4
begin
ML {*
  val _ =
    Outer_Syntax.markup_command Thy_Output.Markup
      @{command_spec "paragraph"} "paragraph heading"
      (Parse.opt_target -- Parse.document_source >> Isar_Cmd.local_theory_markup);
*}
end
