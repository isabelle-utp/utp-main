(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uval.thy                                                             *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Universal Values\<close>

theory uval
imports utype "../utils/Typedep"
keywords "inject_type" :: thy_decl
begin

text \<open>We are going to use the colon for model typing.\<close>

no_notation (ASCII)
  Set.member  ("'(:')") and
  Set.member  ("(_/ : _)" [51, 51] 50)

default_sort typedep

subsection \<open>Value Type\<close>

text \<open>The universal value type is introduced by a type declaration.\<close>

typedecl uval

subsection \<open>Instantiations\<close>

text \<open>Instantiation of @{class typerep}\<close>

instantiation uval :: typerep
begin
definition typerep_uval :: "uval itself \<Rightarrow> typerep" where
[typing]: "typerep_uval (t :: uval itself) =
  typerep.Typerep (STR ''uval.uval'') []"
instance ..
end

text \<open>Instantiation of @{class typedep}\<close>

instantiation uval :: typedep
begin
definition typedep_uval :: "uval itself \<Rightarrow> typerep set" where
[typing]: "typedep_uval (t :: uval itself) = {TYPEREP(uval)}"
instance ..
end

subsection \<open>Injectability\<close>

text \<open>
  We introduce a class @{text injectable} to tag types that we permit to be
  injected into the unified value type @{type uval}. This is to ensure that
  @{type uval} does not occur \emph{itself} in such types, as this leads to
  unsoundness in conjunction with set and function types. A sufficient caveat
  for soundness is that neither @{type uval} nor any type depending on type
  @{type uval} must be a member of @{text injectable}. The assumptions of
  the @{text injectable} class guarantee that this is the case. Soundness is,
  however, contingent on correct instantiation of the class @{class typedep}.
  As the latter is done automatically upon defining new types, the user has
  no way of interfering with it. This justifies our claim that the axiomatic
  value model is definitionally sound.
\<close>

class injectable = typedep +
  assumes utype_is_not_uval : "TYPEREP('a) \<noteq> TYPEREP(uval)"
  assumes utype_not_dep_uval : "TYPEREP(uval) \<notin> TYPEDEP('a)"
begin
theorem  utype_is_not_uval_simp [simp]:
"TYPEREP('a) = TYPEREP(uval) \<longleftrightarrow> False"
apply (simp add: utype_is_not_uval)
done

theorem  utype_not_dep_uval_simp [simp]:
"TYPEREP(uval) \<in> TYPEDEP('a) \<longleftrightarrow> False"
apply (simp add: utype_not_dep_uval)
done
end

subsection \<open>Command @{text "inject_type"}\<close>

text \<open>
  We next configure a command to inject a HOL type into @{type uval}. This
  automatically performs instantiation of the class @{class injectable} for
  the type to be injected, and attempts to discharge the proof obligations
  thus arising. If the proof of the latter fails, an error is displayed to
  the user; in that case, the type is most likely not injectable due to some
  dependency on the type @{type uval}.
\<close>

ML_file "uval.ML"

ML \<open>
  Outer_Syntax.command @{command_keyword "inject_type"} "inject type"
    (Parse.type_const >> (Toplevel.theory o Inject_Type.inject_type));
\<close>

subsection \<open>Axiomatisation\<close>

text \<open>
  We next axiomatise the universal abstraction and representation functions.
  The axioms are guarded by membership to the sort @{class injectable}. This
  is to ensure that they only hold for injectable values and types. A special
  case is the axiom for non-emptiness of types: it implicitly also constrains
  non-injectable model types to have at least one value. This is important to
  ensure the existence of a well-typed total binding and should not raise any
  concerns of soundness, as we know nothing else about such types and their
  values.
\<close>

axiomatization
\<comment> \<open>Universal Abstraction Function\<close>
  InjU :: "'a::injectable \<Rightarrow> uval" and
\<comment> \<open>Universal Representation Function\<close>
  ProjU :: "uval \<Rightarrow> 'a::injectable" and
\<comment> \<open>Model Typing Relation\<close>
  utype_rel :: "uval \<Rightarrow> utype \<Rightarrow> bool" (infix ":\<^sub>u" 50) where
\<comment> \<open>Injection Inverse\<close>
  InjU_inverse [simp]: "ProjU (InjU x) = x" and
\<comment> \<open>Projection Inverse\<close>
  ProjU_inverse [simp]: "y :\<^sub>u UTYPE('a) \<Longrightarrow> InjU (ProjU y) = y" and
\<comment> \<open>Definition of Model Typing\<close>
  utype_rel_def [simp]: "(InjU x) :\<^sub>u t \<longleftrightarrow> x : t" and
\<comment> \<open>Non-emptiness of all model types, even non-injectable ones!\<close>
  utypes_non_empty : "\<exists> y. y :\<^sub>u t"

subsection \<open>Derived Laws\<close>

theorem InjU_inject :
"InjU x = InjU y \<Longrightarrow> x = y"
apply (metis InjU_inverse)
done

theorem InjU_eq [simp]:
"(InjU x) = (InjU y) \<longleftrightarrow> (x = y)"
apply (rule iffI)
apply (erule InjU_inject)
apply (clarsimp)
done

theorem ProjU_inject :
"\<lbrakk>x :\<^sub>u UTYPE('a); y :\<^sub>u UTYPE('a)\<rbrakk> \<Longrightarrow>
 (ProjU :: uval \<Rightarrow> 'a::injectable) x =
 (ProjU :: uval \<Rightarrow> 'a::injectable) y \<Longrightarrow> x = y"
apply (metis ProjU_inverse)
done

subsection \<open>Definitions\<close>

text \<open>We includes several useful derived operators in this section.\<close>

subsubsection \<open>Some Value\<close>

definition some_uval :: "utype \<Rightarrow> uval" where
"some_uval t = (SOME x. x :\<^sub>u t)"

theorem some_uval_typed [typing]:
"(some_uval t) :\<^sub>u t"
apply (unfold some_uval_def)
apply (rule someI_ex)
apply (rule utypes_non_empty)
done

subsubsection \<open>Carrier Set\<close>

definition ucarrier :: "utype \<Rightarrow> uval set" where
"ucarrier t = {x. x :\<^sub>u t}"

syntax "_UVAL" :: "type \<Rightarrow> uval set" ("UVAL'(_')")

translations "UVAL('t)" \<rightleftharpoons> "(CONST ucarrier) TYPEREP('t)"

theorem ucarrier_member [iff]:
"(x \<in> ucarrier t) \<longleftrightarrow> x :\<^sub>u t"
apply (unfold ucarrier_def)
apply (clarsimp)
done

theorem InjU_ucarrier_member :
fixes x :: "'a::injectable"
shows "(InjU x) \<in> UVAL('a)"
apply (unfold ucarrier_member)
apply (unfold utype_rel_def)
apply (unfold p_type_rel_def)
apply (rule refl)
done

subsection \<open>Type Definition\<close>

text \<open>
  For a particular value type @{typ 'a}, @{const InjU} and @{const ProjU}
  fulfil the axioms of a type definition. Hence, we can think of any
  injectable HOL type @{typ 'a} as a subtype of @{type uval}. Note that I
  previously had am interpretation of the @{text type_definition} locale
  here but this caused some strange behaviours in proofs due to additional
  cases and induct rules being implicitly used after the interpretation.
\<close>

theorem type_definition_uval:
"type_definition (InjU :: 'a::injectable \<Rightarrow> uval) ProjU UVAL('a)"
apply (unfold_locales)
apply (simp add: typing)
apply (rule InjU_inverse)
apply (rule ProjU_inverse)
apply (clarsimp)
done

subsection \<open>Experiments\<close>

inject_type nat
inject_type bool

theorem "ProjU (InjU (1::nat)) = (1::nat)"
apply (simp)
done

theorem "InjU (1::nat) :\<^sub>u UTYPE(nat)"
apply (simp add: typing)
done

theorem "\<not> InjU (1::nat) :\<^sub>u UTYPE(int)"
apply (simp add: typing)
done
end