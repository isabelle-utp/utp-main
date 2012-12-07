(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_common.thy                                                       *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Common Definitions *}

theory utp_common
imports Main Real HOLCF
  "~~/src/HOL/Library/Countable"
  "~~/src/HOL/Algebra/Lattice"
begin

subsection {* Configuration *}

default_sort type

hide_const (open) partial_object.carrier

text {* We are going to use the colon for type membership in our model. *}

no_notation
  Set.member ("op :") and
  Set.member ("(_/ : _)" [50, 51] 50)

(*
no_notation (xsymbols)
  ord_class.less_eq  ("op \<le>") and
  ord_class.less_eq  ("(_/ \<le> _)"  [51, 51] 50)
*)

text {* This prevents Isabelle from automatically splitting pairs. *}

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

declaration {* fn _ =>
  Classical.map_cs (fn cs => cs delSWrapper "split_all_tac")
*}

text {* Needed for the proofs in the higher-order model. *}

declare One_nat_def [simp del]

text {* Temporary hack, comment out when there are no sorrys. *}

ML {*
  quick_and_dirty := true
*}

subsection {* Theorem Attributes *}

ML {*
  structure closure =
    Named_Thms (val name = @{binding closure} val description = "closure theorems")
*}

setup closure.setup

ML {*
  structure typing =
    Named_Thms (val name = @{binding typing} val description = "typing theorems")
*}

setup typing.setup

text {* Type Definitions *}

theorem bij_betw_type_definition :
"bij_betw Abs A UNIV \<Longrightarrow> type_definition (the_inv_into A Abs) Abs A"
apply (simp add: bij_betw_def)
apply (clarify)
apply (simp add: type_definition_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule the_inv_into_into)
apply (assumption)
apply (simp_all)
-- {* Subgoal 2 *}
apply (simp add: f_the_inv_into_f)
-- {* Subgoal 2 *}
apply (simp add: the_inv_into_f_f)
done

context type_definition
begin
theorem Rep_inject_sym [simp, intro!] :
"(x = y) \<longleftrightarrow> (Rep x = Rep y)"
apply (simp only: Rep_inject)
done

theorem Abs_inj_on [simp] :
"inj_on Abs A"
apply (rule inj_onI)
apply (simp only: Abs_inject)
done

theorem Abs_image_UNIV [simp] :
"Abs ` A = UNIV"
apply (simp add: image_def)
apply (simp add: set_eq_iff)
apply (clarify)
apply (rule_tac x = "Rep x" in bexI)
apply (simp add: Rep_inverse)
apply (simp add: Rep)
done
end

subsection {* Uncurrying *}

text {* Isabelle provides a currying operator but it seems none for uncurrying. *}

definition uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'c)" where
"uncurry f = (\<lambda> p . f (fst p) (snd p))"

declare uncurry [simp]

subsection {* Function Override *}

text {* We introduce a neater syntax for function overriding. *}

notation override_on ("_ \<oplus> _ on _" [56, 56, 0] 55)

theorem override_on_eq :
"f1 \<oplus> g1 on a = f2 \<oplus> g2 on a \<longleftrightarrow>
 (\<forall> x . x \<in> a \<longrightarrow> g1 x = g2 x) \<and>
 (\<forall> x . x \<notin> a \<longrightarrow> f1 x = f2 x)"
apply (simp add: fun_eq_iff)
apply (safe)
apply (drule_tac x = "x" in spec)
apply (simp)
apply (drule_tac x = "x" in spec)
apply (simp)
apply (drule_tac x = "x" in spec)
apply (case_tac "x \<in> a")
apply (simp_all)
done

theorem override_on_assoc :
"(f \<oplus> g on a) \<oplus> h on b = f \<oplus> (g \<oplus> h on b) on (a \<union> b)"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

text {* Maybe the next theorem should be a default simplification? *}

theorem override_on_singleton :
"(f \<oplus> g on {x}) = f(x := g x)"
apply (rule ext)
apply (auto)
done

theorem override_on_fun_upd [simp] :
"(f \<oplus> g on a)(x := v) = f(x := v) \<oplus> g on (a - {x})"
apply (rule ext)
apply (simp add: override_on_def)
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

theorem override_on_cancel3 [simp] :
"f \<oplus> (g \<oplus> h on a) on a = f \<oplus> h on a"
apply (rule ext)
apply (case_tac "x \<in> a")
apply (auto)
done

theorem override_on_cancel4 [simp] :
"f \<oplus> (g \<oplus> f on b) on a = f \<oplus> g on a - b"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

subsection {* Transfer Strategy *}

theorem inj_on_eval_simp :
"inj_on f s \<Longrightarrow>
 \<lbrakk>x1 \<in> s; x2 \<in> s\<rbrakk> \<Longrightarrow> x1 = x2 \<longleftrightarrow> (f x1 = f x2)"
apply (simp add: inj_on_def)
apply (auto)
done

theorem inj_on_eval_intro :
"inj_on f s \<Longrightarrow>
 \<lbrakk>x1 \<in> s; x2 \<in> s; f x1 = f x2\<rbrakk> \<Longrightarrow> x1 = x2"
apply (simp add: inj_on_eval_simp)
done

subsection {* Miscellaneous *}

theorem meta_sym : "(A \<equiv> B) \<Longrightarrow> (B = A)"
apply (auto)
done
end
