section \<open> Enumeration Types \<close>

theory Enum_Type
  imports Main
  keywords "enumtype" :: "thy_defn"
begin

ML_file \<open>Enum_Type.ML\<close>

ML \<open> 
val _ =
  Outer_Syntax.command @{command_keyword enumtype} "define enumeration types"
   ((Parse.name -- (@{keyword "="} |-- Scan.repeat (Parse.name --| @{keyword "|"}) -- Parse.name)) >> (fn (tname, (cs, c)) => Toplevel.theory (Enum_Type.enum_type tname (cs @ [c]))));
\<close>

end