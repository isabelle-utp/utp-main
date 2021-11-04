section \<open>Parser\<close>

theory X86_Parse
  imports X86_InstructionSemantics
  keywords "x86_64_parser" :: thy_decl
begin

ML_file \<open>X86_Parse.ML\<close>

end
