theory Record_Default_Instance
  imports Main
  keywords "record_default" :: "thy_defn"
begin

ML_file \<open>Record_Default_Instance.ML\<close>

ML \<open>
val _ =
  Outer_Syntax.command @{command_keyword record_default} "define default instances for records"
   (Parse.name >> (fn tname => Toplevel.theory (Record_Default_Instance.mk_rec_default_instance tname)));
\<close>

end