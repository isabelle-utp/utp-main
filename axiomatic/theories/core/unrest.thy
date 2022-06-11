(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: unrest.thy                                                           *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Unrestriction\<close>

theory unrest
imports upred
begin

subsection \<open>Definition\<close>

lift_definition unrest :: "uvar set \<Rightarrow> upred \<Rightarrow> bool" (infix "\<sharp>" 50)
is "\<lambda>vs bs. \<forall>b1\<in>bs. \<forall>b2. b1 \<oplus>\<^sub>s b2 on vs \<in> bs"
done

subsection \<open>Theorems\<close>

theorem TrueP_unrest (*[unrest]*):
"v \<sharp> TrueP"
apply (transfer)
apply (simp)
done

theorem FalseP_unrest (*[unrest]*):
"v \<sharp> FalseP"
apply (transfer)
apply (simp)
done
end