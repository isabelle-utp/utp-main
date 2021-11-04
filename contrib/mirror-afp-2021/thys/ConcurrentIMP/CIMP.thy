(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CIMP
imports
  CIMP_pred
  CIMP_lang
  CIMP_vcg
  CIMP_vcg_rules
keywords
      "locset_definition" :: thy_defn
  and "intern_com" :: thy_decl
begin

text\<open>

Infrastructure for reasoning about CIMP programs. See AFP entry \<open>ConcurrentGC\<close> for examples
of use.

\<close>

named_theorems locset_cache "Location set membership cache"

lemmas cleanup_simps =
  atomize_eq
  simp_thms

ML_file\<open>cimp.ML\<close>
(*<*)

end
(*>*)
