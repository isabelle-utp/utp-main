(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_common.thy                                                       *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 2 September 2014 *)

header {* Common Definitions *}

theory utp_common
imports utp_imports
  utp_document
  "core/utp_constants"
  "utils/typedef_extra"
  "utils/infinity"
  "utils/maxset"
begin

default_sort type

subsection {* Configuration *}

text {* \fixme{Why do we need to hide the following constant? Check.} *}

hide_const Wellorder_Relation.supr

text {* We are going to use the colon for type membership in UTP models. *}

no_notation
  Set.member ("op :") and
  Set.member ("(_/ : _)" [51, 51] 50)

text {*
  The following prevents Isabelle from splitting pairs in proofs by default.
*}

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

setup {* map_theory_claset (fn ctxt => ctxt delSWrapper "split_all_tac") *}

subsection {* Theorem Attributes *}

ML {*
  structure closure = Named_Thms
    (val name = @{binding closure} val description = "closure theorems")
*}

setup closure.setup

ML {*
  structure defined = Named_Thms
    (val name = @{binding defined} val description = "definedness theorems")
*}

setup defined.setup

ML {*
  structure typing = Named_Thms
    (val name = @{binding typing} val description = "typing theorems")
*}

setup typing.setup

ML {*
  structure urename = Named_Thms
    (val name = @{binding urename} val description = "renaming theorems")
*}

setup urename.setup

ML {*
  structure usubst = Named_Thms
    (val name = @{binding usubst} val description = "substitution theorems")
*}

setup usubst.setup

ML {*
  structure refine = Named_Thms
    (val name = @{binding refine} val description = "refinement theorems")
*}

setup refine.setup

subsection {* Total Predicates *}

text {* Total predicates are everywhere true. *}

definition is_total :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
"is_total p = (\<forall> x . p x)"

theorem is_totalI [intro] :
"(\<And> x . p x) \<Longrightarrow> is_total p"
apply (simp add: is_total_def)
done

theorem is_totalD [dest] :
"is_total p \<Longrightarrow> p x"
apply (simp add: is_total_def)
done

text {*
  \note{Note that we cannot have @{thm [source] is_totalD} as a default
  simplification as it seems to cause the simplifier to loop.}
*}

subsection {* Uncurrying *}

text {*
  Isabelle provides a currying operator @{const curry} but none for uncurrying.
*}

definition uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'c)" where
"uncurry = (\<lambda> f p . f (fst p) (snd p))"

lemma uncurry_app [simp] :
"uncurry f (x, y) = f x y"
apply (simp add: uncurry_def)
done

subsection {* Function Override *}

text {* We first introduce a neater syntax for function override. *}

notation override_on ("_ \<oplus> _ on _" [56, 56, 51] 55)

lemma override_on_eq :
"f1 \<oplus> g1 on a1 = f2 \<oplus> g2 on a2 \<longleftrightarrow>
 (\<forall> x . x \<notin> a1 \<and> x \<notin> a2 \<longrightarrow> f1 x = f2 x) \<and>
 (\<forall> x . x \<notin> a1 \<and> x \<in> a2 \<longrightarrow> f1 x = g2 x) \<and>
 (\<forall> x . x \<in> a1 \<and> x \<notin> a2 \<longrightarrow> g1 x = f2 x) \<and>
 (\<forall> x . x \<in> a1 \<and> x \<in> a2 \<longrightarrow> g1 x = g2 x)"
apply (unfold fun_eq_iff)
apply (safe)
apply (drule_tac x = "x" in spec)
apply (simp)
apply (drule_tac x = "x" in spec)
apply (simp)
apply (drule_tac x = "x" in spec)
apply (simp)
apply (drule_tac x = "x" in spec)
apply (simp)
apply (drule_tac x = "x" in spec)+
apply (case_tac "x \<in> a1", case_tac[!] "x \<in> a2")
apply (simp_all)
done

lemma override_on_eq2 :
"f1 \<oplus> g1 on a = f2 \<oplus> g2 on a \<longleftrightarrow>
 (\<forall> x . x \<notin> a \<longrightarrow> f1 x = f2 x) \<and>
 (\<forall> x . x \<in> a \<longrightarrow> g1 x = g2 x)"
apply (subst override_on_eq)
apply (clarsimp)
done

theorem override_on_idem [simp] :
"f \<oplus> f on a = f"
apply (rule ext)
apply (case_tac "x \<in> a")
apply (simp_all)
done

theorem override_on_assoc :
"(f \<oplus> g on a) \<oplus> h on b = f \<oplus> (g \<oplus> h on b) on (a \<union> b)"
apply (rule ext)
apply (case_tac "x \<in> a", case_tac[!] "x \<in> b")
apply (simp_all)
done

text {*
  The theorem @{thm [source] override_on_emptyset} is already a default
  simplification.
*}

theorem override_on_empty (* [simp] *) :
"f \<oplus> g on {} = f"
apply (rule ext)
apply (simp)
done

theorem override_on_UNIV [simp] :
"f \<oplus> g on UNIV = g"
apply (rule ext)
apply (simp)
done

theorem override_on_subset :
"\<lbrakk>f = f \<oplus> g on a; b \<subseteq> a\<rbrakk> \<Longrightarrow> f = f \<oplus> g on b"
apply (simp add: fun_eq_iff)
apply (clarify)
apply (drule_tac x = "x" in spec)
apply (case_tac "x \<in> a", case_tac[!] "x \<in> b")
apply (simp_all)
apply (auto)
done

text {* \fixme{Should the next theorem be a default simplification?} *}

theorem override_on_singleton (* [simp] *) :
"f \<oplus> g on {x} = f(x := g x)"
apply (rule ext)
apply (simp)
done

theorem override_on_assign [simp] :
"(f \<oplus> g on a)(x := y) = f(x := y) \<oplus> g on (a - {x})"
apply (rule ext)
apply (rename_tac z)
apply (case_tac "z \<in> a")
apply (simp_all)
done

theorem override_on_chain [simp] :
"(f \<oplus> g on a) \<oplus> g on b = f \<oplus> g on (a \<union> b)"
apply (rule ext)
apply (case_tac "x \<in> a", case_tac[!] "x \<in> b")
apply (simp_all)
done

text {* \fixme{Perhaps a few useful cancellation theorems are missing here.} *}

theorem override_on_cancel [simp] :
"(f \<oplus> g on a) \<oplus> h on a = f \<oplus> h on a"
"f \<oplus> (g \<oplus> h on a) on a = f \<oplus> h on a"
"f \<oplus> (f \<oplus> g on a) on b = f \<oplus> g on a \<inter> b"
"f \<oplus> (g \<oplus> f on b) on a = f \<oplus> g on a - b"
apply (unfold fun_eq_iff)
apply (safe)
apply (case_tac "x \<in> a", case_tac[1-2] "x \<in> b", simp_all)+
done

theorem override_on_reorder :
"a \<inter> b = {} \<Longrightarrow>
 (f \<oplus> g on a) \<oplus> h on b = (f \<oplus> h on b) \<oplus> g on a"
apply (rule ext)
apply (case_tac "x \<in> a", case_tac[!] "x \<in> b")
apply (simp_all)
apply (auto)
done

theorem override_on_minus_app [simp] :
"x \<in> b \<Longrightarrow> (f \<oplus> g on a - b) x = f x"
apply (simp_all)
done

subsection {* Transfer Strategy *}

theorem inj_on_eval_simp :
"inj_on f s \<Longrightarrow>
 \<lbrakk>x \<in> s; y \<in> s\<rbrakk> \<Longrightarrow> x = y \<longleftrightarrow> f x = f y"
apply (simp add: inj_on_def)
apply (auto)
done

theorem inj_on_eval_intro :
"inj_on f s \<Longrightarrow>
 \<lbrakk>x \<in> s; y \<in> s; f x = f y\<rbrakk> \<Longrightarrow> x = y"
apply (simp add: inj_on_eval_simp)
done

subsection {* Miscellaneous *}

theorems asmE = rev_mp
end
