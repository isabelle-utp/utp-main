(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_common.thy                                                       *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Common Definitions *}

theory utp_common
imports Main
begin

subsection {* Configuration *}

text {* We want to use the colon for type membership in our model. *}

no_notation
  Set.member ("op :") and
  Set.member ("(_/ : _)" [50, 51] 50)

text {* This prevents Isabelle from automatically splitting pairs. *}

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

declaration {* fn _ =>
  Classical.map_cs (fn cs => cs delSWrapper "split_all_tac")
*}

subsection {* Theorem Attributes *}

ML {*
  structure closure =
    Named_Thms (val name = "closure" val description = "closure theorems")
*}

setup closure.setup

subsection {* Function Override *}

text {* We introduce a neater syntax for function overriding. *}

notation override_on ("_ \<oplus> _ on _" [56, 56, 0] 55)

theorem override_on_assoc :
"(f \<oplus> g on a) \<oplus> h on b = f \<oplus> (g \<oplus> h on b) on (a \<union> b)"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

theorem override_on_singleton :
"(f \<oplus> g on {x}) = f(x := g x)"
apply (rule ext)
apply (auto)
done

theorem override_on_chain [simp] :
"(f \<oplus> g on a) \<oplus> g on b = f \<oplus> g on (a \<union> b)"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

theorem override_on_cancel1 [simp] :
"f \<oplus> f on a = f"
apply (simp add: override_on_def)
done

theorem override_on_cancel2 [simp] :
"(f \<oplus> g on a) \<oplus> h on a = f \<oplus> h on a"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done
end