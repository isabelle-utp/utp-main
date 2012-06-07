(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/utp_common.thy                                                   *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Common Definitions *}

theory utp_common
imports "utp_config" "utils/utp_sets"
begin

subsection {* Uncurrying *}

text {* Isabelle provides a currying operator but it seems none for uncurrying. *}

definition uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'c)" where
"uncurry f = (\<lambda> p . f (fst p) (snd p))"

declare uncurry [simp]

subsection {* Application of Relations *}

text {* It would be nice to have a neater syntax here. *}

definition RelApp :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b" where
"RelApp r x = (THE y . y \<in> r `` {x})"

declare RelApp_def [simp]

subsection {* Coercion *}

definition Coerce :: "'a \<Rightarrow> ('a set) \<Rightarrow> 'a" (infix "\<hookrightarrow>" 100) where
"x \<hookrightarrow> s = (if x \<in> s then x else (SOME x . x \<in> s))"

text {* Fundamental Theorem *}

theorem Coerce_member :
"\<lbrakk>s \<noteq> {}\<rbrakk> \<Longrightarrow> x \<hookrightarrow> s \<in> s"
apply (simp add: Coerce_def)
apply (clarify)
apply (subgoal_tac "\<exists> x . x \<in> s")
apply (clarify)
apply (rule_tac a = "xa" in someI2)
apply (auto)
done

subsection {* Theorems *}

subsubsection {* Logic *}

theorem some_member_rule [simp, intro!]:
"s \<noteq> {} \<Longrightarrow> (SOME x . x \<in> s) \<in> s"
apply (auto)
apply (rule_tac Q = "(SOME x. x \<in> s) \<notin> s" in contrapos_pp)
apply (assumption)
apply (rule_tac a = "x" in someI2)
apply (simp_all)
done

subsubsection {* Sets and Pairs *}

theorem pairI :
"p = (fst p, snd p)"
apply (auto)
done

theorem non_empty_exists :
"s \<noteq> {} \<longleftrightarrow> (\<exists> x . x \<in> s)"
apply (auto)
done

subsubsection {* Functions *}

text {* Function Update *}

theorem fun_upd_cancel [simp] :
"f (x := f x) = f"
apply (auto)
done

theorem fun_upd_comm :
"x \<noteq> y \<Longrightarrow> f (x := a, y := b) = f (y := b, x := a)"
apply (rule ext)
apply (simp)
done

theorem image_chain_elim :
"f ` g ` a = {y . \<exists> x . x \<in> a \<and> y = f (g x)}"
apply (auto)
done

text {* Function Override *}

text {* We first define a neater syntax for function overriding. *}

notation override_on ("_ \<oplus> _ on _" [56, 56, 0] 55)

theorem override_on_idem [simp]:
"f \<oplus> f on a = f"
apply (simp add: override_on_def)
done

theorem override_on_comm :
"f \<oplus> g on a = g \<oplus> f on (- a)"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

theorem override_on_comm_sym :
"f \<oplus> g on (- a) = g \<oplus> f on a"
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
"(f \<oplus> g on {x})(x := y) = f (x := y)"
apply (rule ext)
apply (auto)
done

theorem override_on_cancel2 [simp] :
"f \<oplus> (g \<oplus> f on a) on a = f"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

theorem override_on_cancel3 [simp] :
"(f \<oplus> g on a) \<oplus> f on a = f"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

theorem override_on_cancel4 [simp] :
"f \<oplus> (g \<oplus> h on a) on (b - a) = f \<oplus> g on (b - a)"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

subsubsection {* Miscellaneous *}

theorem let_pair_simp [simp] :
"(let (a, b) = p in e a b) = e (fst p) (snd p)"
apply (auto)
apply (simp add: prod_case_beta)
done

theorem case_pair_simp [simp] :
"(case p of (x, y) \<Rightarrow> f x y) = f (fst p) (snd p)"
apply (subst pairI)
apply (simp add: prod_case_beta)
done

subsection {* Proof Experiments *}

theorem relapp_test_lemma :
"RelApp {(1::nat, 2::nat)} 1 = 2"
apply (simp)
done
end
