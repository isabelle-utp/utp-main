(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_document.thy                                                     *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 2 September 2014 *)

header {* Document Support *}

theory utp_document
imports Pure
keywords "paragraph" :: thy_heading4
begin

text {*
  We introduce and additional markup command @{text paragraph} for paragraphs.
  Please note that the style file \texttt{document.sty} is now required for
  compilation of the {\LaTeX} files.
*}

ML {*
  val _ =
    Outer_Syntax.markup_command Thy_Output.Markup
      @{command_spec "paragraph"} "paragraph heading"
      (Parse.opt_target -- Parse.document_source >> Isar_Cmd.local_theory_markup);
*}
end
