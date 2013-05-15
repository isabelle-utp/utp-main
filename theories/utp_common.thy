(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_common.thy                                                       *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Common Definitions *}

theory utp_common
imports Main Real Kleene_Algebra_Models
  "~~/src/HOL/Library/Countable"
(*  "~~/src/HOL/Library/Kleene_Algebra" *)
  "~~/src/Tools/Adhoc_Overloading"
  "utils/Library_extra"
begin

subsection {* Configuration *}

default_sort type

text {* We are going to use the colon for type membership in our model. *}

no_notation
  Set.member  ("op :") and
  Set.member  ("(_/ : _)" [51, 51] 50)

text {* This prevents Isabelle from automatically splitting pairs. *}

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

declaration {* fn _ =>
  Classical.map_cs (fn cs => cs delSWrapper "split_all_tac")
*}

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

text {* Type Definitions *}

lemma (in type_definition) Rep_inject_sym [simp, intro!] :
"(x = y) \<longleftrightarrow> (Rep x = Rep y)"
apply (simp only: Rep_inject)
done

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

lemma override_on_subset: 
"\<lbrakk> f = f \<oplus> g on vs1; vs2 \<subseteq> vs1 \<rbrakk> \<Longrightarrow> f = f \<oplus> g on vs2"
apply (auto simp add:override_on_def)
apply (rule ext)
apply (auto)
apply (drule_tac x="a" and y="a" in cong)
apply (auto)
done

text {* Maybe the next theorem should be a default simplification? *}

theorem override_on_singleton :
"(f \<oplus> g on {x}) = f(x := g x)"
apply (rule ext)
apply (auto)
done

theorem override_on_assign [simp]:
"(f \<oplus> g on a)(x := v) = f(x := v) \<oplus> g on (a - {x})"
apply (rule ext)
apply (simp add:override_on_def)
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

theorem override_on_cancel5 [simp] : 
"f \<oplus> (f \<oplus> g on a) on b = f \<oplus> g on a \<inter> b"
  by (auto simp add:override_on_def)

theorem override_on_reorder :
"\<lbrakk> a \<inter> b = {} \<rbrakk> \<Longrightarrow>
 (f \<oplus> g on a) \<oplus> h on b = (f \<oplus> h on b) \<oplus> g on a"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

theorem override_on_minus [simp]:
"v \<in> vs2 \<Longrightarrow> (b \<oplus> b' on vs1 - vs2) v = b v"
  by (simp add:override_on_def)

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

subsection {* Overloaded constants *}

text {* Ad-hoc overloading allows the binding of symbols to multiple
  constructs.  This adds the @{text "\<alpha>"} symbol as an overloaded constant for
  alphabets *}

consts
  alphabet  :: "'r \<Rightarrow> 'a" ("\<alpha>")

notation
  Some ("\<lfloor>_\<rfloor>")

setup {*
  Adhoc_Overloading.add_overloaded @{const_name alphabet}
*}

end
