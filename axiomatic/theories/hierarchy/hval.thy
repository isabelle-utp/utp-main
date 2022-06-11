(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: hval.thy                                                             *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Hierarchical Values\<close>

theory hval
imports ranks
  "../core/utype"
begin

text \<open>We are going to use the colon for model typing.\<close>

no_notation (ASCII)
  Set.member  ("'(:')") and
  Set.member  ("(_/ : _)" [51, 51] 50)

default_sort "{typerep,rank}"

text \<open>
  The constraints for injectability in the original theory @{text uval} are
  rather strong as excluding any dependency to type @{text uval} itself. Our
  aim here is to mitigate that constraint by introducing an indexed family of
  unified value types where each @{text uval} type possesses a rank. We may
  then weaken the injectability caveat to permit higher-rank HOL types to be
  injected into lower-rank @{text uval} types; this indeed retains soundness.
\<close>

text \<open>
  To mechanise this idea, we strictly-speaking require dependent typing. We
  attempt a work-around here that makes use of a type class @{text rank} (see
  theory @{text ranks}) to determine the rank of a HOL type, and (ab)uses
  the type parameter @{text "'idx"} of our new value type @{text "'idx uval"}
  to add information to the value universe to determine its rank within the
  hierarchy of universes. Ranks are treated uniformly, meaning that every HOL
  type including type @{text "uval"} possesses a rank.
\<close>

subsection \<open>Type Declaration\<close>

text \<open>
  Below we introduce the universe hierarchy of the hierarchical value model as
  a family of types. While HOL does not offer support for dependent typing, we
  (ab)use a type parameter @{typ "'idx"} to distinguish value universes with
  different ranks. We assume that @{typ "'idx"} is of sort @{class rank}, so
  that we are able to attribute a rank to each @{text uval} instance. The rank
  will later be used in the @{text axiomatization} to guard value injections.
\<close>

typedecl 'idx(*::rank*) uval

text \<open>We configure the syntax @{text "uval['a]"} for @{text "'a uval"}.\<close>

type_notation uval ("uval[_]")

text \<open>
  Together with the support for dynamic construction of index types in theory
  @{text ranks}, this enables us to write types such as the following ones.
\<close>

typ "uval[0]"
typ "uval[1]"
typ "uval[2]"
typ "uval[3]"

typ "uval[0>'a]"
typ "uval[1>'b]"
typ "uval[2>'c]"
typ "uval[3>'d]"

subsection \<open>Instantiations\<close>

text \<open>
  For type declarations we have to instantiate class @{class typerep} manually.
\<close>

instantiation uval :: (typerep) typerep
begin
definition typerep_uval :: "uval['a] itself \<Rightarrow> typerep" where
[typing]: "typerep_uval (t :: uval['a] itself) =
  typerep.Typerep (STR ''uval.uval'') [TYPEREP('a)]"
instance ..
end

text \<open>
  Like any other HOL type, @{typ "uval['idx]"} has a rank which is albeit
  determined by the type parameter @{typ "'idx"}. We increment the rank of
  @{typ "'a"} by one since there is no point in value universes with a zero
  rank since no HOL type can be injected into them.
\<close>

instantiation uval :: (rank) rank
begin
definition rank_uval :: "uval['a] itself \<Rightarrow> nat" where
[ranks]: "rank_uval t = RANK('a) + 1"
instance ..
end

lemma RANK_le_uval [simp]:
"RANK('a) < RANK(uval['idx]) \<longleftrightarrow> RANK('a) \<le> RANK('idx)"
apply (unfold ranks)
apply (linarith)
done

subsection \<open>Axiomatisation\<close>

text \<open>
  We now axiomatise the universal abstraction and representation functions.
  The axioms are guarded by constraints on the ranks of the HOL type to be
  injected, as well as the target type @{typ "uval['idx]"} of the injection.
  A special case is the axiom for non-emptiness of types: it moreover says
  something about types that are inherently not injectable into a particular
  value universe within the hierarchy. This is important to ensure existence
  of a well-typed total binding and does not raise any concerns of soundness
  since we know nothing else about the values of such non-injectable types.
  An open question is whether additional axioms and functions may be needed
  towards developing a workable basis for a HO UTP reasoning framework.
\<close>

axiomatization
\<comment> \<open>Abstraction Function\<close>
  InjU :: "'a \<Rightarrow> uval['idx]" and
\<comment> \<open>Representation Function\<close>
  ProjU :: "uval['idx] \<Rightarrow> 'a" and
\<comment> \<open>Value Coercion Function\<close>
  CoerceU :: "uval['idx1] \<Rightarrow> uval['idx2]" and
\<comment> \<open>Model Typing Relation\<close>
  utype_rel :: "'idx uval \<Rightarrow> utype \<Rightarrow> bool" (infix ":\<^sub>u" 50) where
\<comment> \<open>Injection Inverse\<close>
  InjU_inverse [simplified, simp]:
    "RANK('a) < RANK(uval['idx]) \<Longrightarrow> ProjU (InjU x) = x" and
\<comment> \<open>Projection Inverse\<close>
  ProjU_inverse [simplified, simp]:
    "RANK('a) < RANK(uval['idx]) \<Longrightarrow> y :\<^sub>u UTYPE('a) \<Longrightarrow> InjU (ProjU y) = y" and
\<comment> \<open>Definition of Model Typing\<close>
  utype_rel_def [simplified, simp]:
    "RANK('a) < RANK(uval['idx]) \<Longrightarrow> (InjU x) :\<^sub>u t \<longleftrightarrow> x : t" and
\<comment> \<open>Non-emptiness of all model types, even non-injectable ones.\<close>
  utypes_non_empty : "\<exists> y. y :\<^sub>u t"

text \<open>
  The coercion functions allows us to coerce values between different layers
  of the hierarchy. It needs to be axiomatised too, namely if we like to avoid
  the type @{typ "'a"} of the injected value to crop up in the parametrisation
  of @{text "CoerceU"} (this would be the case if using a @{text definition}).
  Does the axiom below raise any issues of soundness? I do not believe so but
  perhaps discuss this with colleagues and Isabelle/HOL experts.
\<close>

axiomatization where
\<comment> \<open>Definition of Coercion\<close>
  CoerceU_def: "CoerceU = InjU o ProjU"

subsection \<open>Derived Laws\<close>

lemma CoerceU_InjU [simp]:
"RANK('a) \<le> RANK('idx1) \<Longrightarrow>
 RANK('idx1) \<le> RANK('idx2) \<Longrightarrow>
  (CoerceU ((InjU :: 'a \<Rightarrow> uval['idx1]) x)) = (InjU :: 'a \<Rightarrow> uval['idx2]) x"
apply (subst CoerceU_def)
apply (clarsimp)
apply (subst InjU_inverse)
\<comment> \<open>Subgoal 1\<close>
apply (simp add: ranks)
\<comment> \<open>Subgoal 2\<close>
apply (rule refl)
done

lemma ProjU_CoerceU [simp]:
"RANK('a) \<le> RANK('idx1) \<Longrightarrow>
 RANK('idx1) \<le> RANK('idx2) \<Longrightarrow>
  (ProjU :: uval['idx2] \<Rightarrow> 'a) (CoerceU y) = (ProjU :: uval['idx1] \<Rightarrow> 'a) y"
apply (subst CoerceU_def)
apply (clarsimp)
apply (subst InjU_inverse)
\<comment> \<open>Subgoal 1\<close>
apply (simp add: ranks)
\<comment> \<open>Subgoal 2\<close>
apply (rule refl)
done

\<comment> \<open>TODO: What about coercion and model typing?\<close>

subsection \<open>Extended Syntax\<close>

text \<open>
  We lastly add support for the following four notations: @{text "InjU[n]"},
  @{text "ProjU[n]"}, @{text "CoerceU[n1,n2]"} and @{text "x :[n]\<^sub>u t"}, where
  @{text n} is the underlying rank of the type instantiation of the function.
\<close>

syntax "_InjU"  :: "type \<Rightarrow> 'a \<Rightarrow> uval['idx]" ("InjU[_]")
syntax "_ProjU" :: "type \<Rightarrow> uval['idx] \<Rightarrow> 'a" ("ProjU[_]")
syntax "_CoerceU" :: "type \<Rightarrow> type \<Rightarrow> uval['idx1] \<Rightarrow> uval['idx2]" ("CoerceU[_,_]")
syntax "_utype_rel" :: "uval['idx] \<Rightarrow> type \<Rightarrow> utype \<Rightarrow> bool" ("(_ :[_]\<^sub>u/ _)" [51, 0, 51] 50)

translations
   "InjU['idx]" \<rightharpoonup> "(CONST InjU) :: (_ \<Rightarrow> uval['idx])"
   "ProjU['idx]" \<rightharpoonup> "(CONST ProjU) :: (uval['idx] \<Rightarrow> _)"
   "CoerceU['idx1,'idx2]" \<rightharpoonup> "(CONST CoerceU) :: (uval['idx1] \<Rightarrow> uval['idx2])"
   "x :['idx]\<^sub>u t" \<rightharpoonup> "x :\<^sub>u t :: (uval['idx] \<Rightarrow> utype \<Rightarrow> bool)"

\<comment> \<open>TODO: Only issue left to-do is to print the above abbreviations too.\<close>

subsection \<open>Injectability\<close>

text \<open>
  As in the previous model, it is possible to define the property of a HOL
  type being universally injectable. Here, this means it can be injected into
  every universe within our hierarchical family. As before, we can specify
  this as a type class and recover our initial (unguarded) axioms, albeit as
  provable laws. Whether the below gives us much in terms of proof automation
  is an open issue.
\<close>

class injectable = rank +
  assumes rank_is_zero [ranks]: "RANK('a) = 0"
begin

theorem injectable_rank_leq
[simp]: "RANK('a) \<le> r"
apply (simp add: ranks)
done

text \<open>Below, we recover the original axioms for injectability as laws.\<close>

theorem InjU_inverse' [simp]:
fixes x :: "'a"
shows "ProjU (InjU x) = x"
apply (simp)
done

theorem ProjU_inverse' [simp]:
fixes y :: "uval['idx]"
shows "y :\<^sub>u UTYPE('a) \<Longrightarrow>
  (InjU :: 'a \<Rightarrow> uval['idx]) ((ProjU :: uval['idx] \<Rightarrow> 'a) y) = y"
apply (simp)
done

theorem utype_rel_def' [simp]:
fixes x :: "'a"
shows "(InjU x) :\<^sub>u t \<longleftrightarrow> x : t"
apply (simp)
done
end

subsection \<open>Proof Experiments\<close>

theorem "RANK(nat) = 0"
apply (rank_tac)
done

theorem "RANK(nat set) = 0"
apply (rank_tac)
done

theorem "RANK(uval[0] set) = 1"
apply (rank_tac)
done

theorem "RANK(uval[0] set \<times> uval[1]) = 2"
apply (rank_tac)
done

typedef 'idx my_type =
  "UNIV :: (uval['idx] \<times> uval[1] set) set"
apply (rule UNIV_witness)
done

theorem "RANK(0 my_type) = 2"
apply (rank_tac)
done

theorem "RANK(2 my_type) = 3"
apply (rank_tac)
done

hide_type my_type
end