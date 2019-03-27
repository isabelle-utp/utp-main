section \<open> Easy to use Circus-M parser \<close>

theory utp_circus_easy_parser
  imports "utp_circus" "UTP.utp_easy_parser"
begin recall_syntax

text \<open> We change := so that it refers to the Circus operator \<close>

no_adhoc_overloading
  uassigns assigns_r

adhoc_overloading
  uassigns AssignsCSP

syntax
  "_GuardCSP" :: "uexp \<Rightarrow> logic \<Rightarrow> logic" (infixr "&&" 60)

no_translations
  "_uwhile_top b P" == "CONST while_top b P"

translations
  "_uwhile_top b P" == "CONST WhileC b P"

end