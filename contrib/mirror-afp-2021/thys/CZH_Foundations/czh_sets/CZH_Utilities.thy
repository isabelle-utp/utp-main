(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Utilities\<close>
theory CZH_Utilities
  imports Main
  keywords "lemmas_with" :: thy_decl
begin


text\<open>
Then command \<^text>\<open>lemmas_with\<close> is a copy (with minor amendments to formatting) 
of the command with the identical name that was introduced by Ondřej Kunčar in
\<^text>\<open>HOL-Types_To_Sets.Prerequisites\<close>. A copy of the function was produced, 
primarily, to avoid the unnecessary dependency of this work on the 
axioms associated with the framework \<open>Types-To-Sets\<close>.
\<close>

ML\<open>
val _ =
  Outer_Syntax.local_theory'
    \<^command_keyword>\<open>lemmas_with\<close> 
    "note theorems with (the same) attributes"
    (
      Parse.attribs --| \<^keyword>\<open>:\<close> --
      Parse_Spec.name_facts -- 
      Parse.for_fixes >> 
      (
        fn (((attrs),facts), fixes) =>
          #2 oo Specification.theorems_cmd Thm.theoremK
          (map (apsnd (map (apsnd (fn xs => attrs@xs)))) facts) fixes
      )
    )
\<close>

text\<open>\newpage\<close>

end