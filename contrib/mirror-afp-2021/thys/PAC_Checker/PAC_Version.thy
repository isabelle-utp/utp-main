(*
  File:         PAC_Version.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Version
  imports Main
begin

text \<open>This code was taken from IsaFoR. However, for the AFP, we use the version name \<^text>\<open>AFP\<close>,
instead of a mercurial version. \<close>
local_setup \<open>
  let
    val version = "AFP"
  in
    Local_Theory.define
      ((\<^binding>\<open>version\<close>, NoSyn),
        ((\<^binding>\<open>version_def\<close>, []), HOLogic.mk_literal version)) #> #2
  end
\<close>

declare version_def [code]

end
