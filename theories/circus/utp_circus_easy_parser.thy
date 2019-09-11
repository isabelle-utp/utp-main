section \<open> Easy to use Circus-M parser \<close>

theory utp_circus_easy_parser
  imports "utp_circus"
begin recall_syntax

text \<open> We change := so that it refers to the Circus operator \<close>

no_adhoc_overloading
  uassigns assigns_r

adhoc_overloading
  uassigns AssignsCSP

notation GuardCSP (infixr "&&" 60)

utp_lift_notation GuardCSP (0)

purge_notation while_top ("while _ do _ od")

notation WhileC ("while _ do _ od")

utp_lift_notation WhileC (0)

end