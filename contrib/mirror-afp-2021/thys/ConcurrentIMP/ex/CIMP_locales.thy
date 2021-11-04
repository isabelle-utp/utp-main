(*<*)
theory CIMP_locales
imports
 "../CIMP"
begin

(*>*)
section\<open> One locale per process \<close>

text\<open>

A sketch of what we're doing in \<open>ConcurrentGC\<close>, for quicker testing.

FIXME write some lemmas that further exercise the generated thms.

\<close>

locale P1
begin

definition com :: "(unit, string, unit, nat) com" where
  "com = \<lbrace>''A''\<rbrace> WHILE ((<) 0) DO \<lbrace>''B''\<rbrace> \<lfloor>\<lambda>s. s - 1\<rfloor> OD"

intern_com com_def
print_theorems (* P1.com_interned, P1.loc_defs *)

locset_definition "loop = {B}"
print_theorems (* P1.loop.memb, P1.loop_def *)
thm locset_cache (* the two facts in P1.loop.memb *)

definition "assertion = atS False loop"

end

thm locset_cache (* the two facts in P1.loop.memb *)

locale P2
begin

thm locset_cache (* the two facts in P1.loop.memb *)

definition com :: "(unit, string, unit, nat) com" where
  "com = \<lbrace>''C''\<rbrace> WHILE ((<) 0) DO \<lbrace>''A''\<rbrace> \<lfloor>Suc\<rfloor> OD"

intern_com com_def
locset_definition "loop = {A}"
print_theorems

end

thm locset_cache (* four facts: P1.loop.memb, P2.loop.memb *)

primrec coms :: "bool \<Rightarrow> (unit, string, unit, nat) com" where
  "coms False = P1.com"
| "coms True = P2.com"

(*<*)

end
(*>*)
