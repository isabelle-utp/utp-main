(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Transfer_Plus.thy                                                    *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Unfolding Transfer\<close>

theory Transfer_Plus
imports HOL.Transfer
begin

text \<open>
  This theory makes a slight improvement to Isabelle/HOL's transfer tactics.
  Below, we declare a theorem attribute @{text transfer_unfold} in which the
  user may collection theorems that are automatically used in rewriting prior
  to execution of the transfer tactics @{text transfer} and @{text transfer'}.
\<close>

named_theorems transfer_unfold "theorems to unfold before transfer"

text \<open>
  ML code that provides the improved transfer tactic. Unfortunately, as the
  Isabelle/HOL transfer tool does not expose the proof method for transfer,
  a small amount of code had to be copied and duplicated here. This code is
  unlikely to change though in future versions of Isabelle/HOL. Maybe get in
  touch with the developers and ask if @{text Transfer.transfer_method} could
  be exposed in the signature @{text Transfer} in future versions if Isabelle.
\<close>

ML_file "Transfer_Plus.ML"

text \<open>
  We next override the existing tactics @{text transfer} and @{text transfer'}
  to use our improved method. This completes the implementation.
\<close>

setup \<open>
    Method.setup @{binding transfer}
      (Transfer_Plus.unfolding_transfer_method true)
      "generic theorem transfer method with unfolding"
\<close>

setup \<open>
  Method.setup @{binding transfer'}
    (Transfer_Plus.unfolding_transfer_method false)
    "generic theorem transfer method with unfolding"
\<close>
end