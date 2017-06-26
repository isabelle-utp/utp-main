(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: fmi.thy                                                              *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 8 Feb 2017 *)

section {* FMI {\Circus} Model *}

theory fmi
imports "../utp/models/utp_axm"
  "../theories/utp_circus"
  "../utils/Positive_New"
begin recall_syntax

type_synonym 'a relation = "'a Relation.rel"

translations (type) "'a relation" \<rightleftharpoons> (type)"'a Relation.rel"

hide_type Relation.rel -- {* TODO: Let the recall package hide types too! *}

text {* The following adjustment is needed... *}

syntax
  "_csp_sync" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow>\<^sub>u _" [81, 80] 80)

declare [[typedef_overloaded]]
declare [[quick_and_dirty]]

declare [[syntax_ambiguity_warning=false]]

default_sort type

subsection {* Preliminaries *}

lemma card_gt_two_exists:
"finite S \<Longrightarrow> 2 \<le> card S \<Longrightarrow> (\<exists>a\<in>S. \<exists>b\<in>S. a \<noteq> b)"
apply (atomize (full))
apply (rule impI)
apply (erule finite.induct)
apply (simp_all)
apply (safe; clarsimp)
apply (metis
  One_nat_def Suc_1 card_Suc_eq card_insert_if le_SucE nat.inject singletonI)
apply (auto)
done

text {* By default, the product type did not instantiate class @{class two}. *}

theorem card_ge_two_witness:
"finite S \<Longrightarrow> 2 \<le> card S = (\<exists>x y. x \<in> S \<and> y \<in> S \<and> x \<noteq> y)"
apply (rule iffI)
-- {* Subgoal 1 *}
using card_gt_two_exists apply (blast)
-- {* Subgoal 2 *}
apply (case_tac "card S = 0")
apply (clarsimp)
apply (case_tac "card S = 1")
apply (clarsimp)
apply (metis card_Suc_eq singletonD)
apply (clarsimp)
apply (meson Finite_Set.card_0_eq less_2_cases not_le)
done

lemma instance_twoI:
"(\<exists>(x::'a) (y::'a). x \<noteq> y) \<Longrightarrow> \<not> finite (UNIV::'a set) \<or> 2 \<le> card (UNIV::'a set)"
apply (case_tac "finite (UNIV::'a set)")
apply (simp_all)
apply (subst card_ge_two_witness)
apply (simp_all)
done

instance prod :: (two, two) two
apply (intro_classes)
apply (rule instance_twoI)
apply (subgoal_tac "\<exists>(a::'a) (b::'a). a \<noteq> b")
apply (subgoal_tac "\<exists>(c::'b) (d::'b). c \<noteq> d")
apply (clarsimp)
apply (rule two_diff)
apply (rule two_diff)
done

instantiation prod :: (vst, vst) vst
begin
definition vstore_lens_prod :: "vstore \<Longrightarrow> 'a \<times> 'b" where
"vstore_lens_prod = vstore_lens ;\<^sub>L fst\<^sub>L"
instance
apply (intro_classes)
apply (unfold vstore_lens_prod_def)
apply (simp)
done
end

text {* TODO: Find a better place to carry out the instantiation below. *}

subclass (in infinite) two
apply (intro_classes)
apply (rule disjI1)
apply (auto)
done

subsection {* Well-defined Values *}

text {*
  We declare a type class that introduces a notion of well-definedness of
  values for some HOL type @{typ 'a} for which it is instantiated. With this,
  we can carry out the generic construction of subtypes that include defined
  values only. We may use this later to obtain types for well-formed events.
*}

class wf =
fixes wf :: "'a \<Rightarrow> bool"
assumes wf_value_exists: "\<exists>x. wf x"
begin
definition WF_UNIV :: "'a itself \<Rightarrow> 'a set" where
"WF_UNIV t = (Collect wf)"
end

text {* Generic construction of a subtype comprising of defined values only. *}

typedef (overloaded) 'a::wf wf = "WF_UNIV TYPE('a)"
apply (unfold WF_UNIV_def)
apply (clarsimp)
apply (rule wf_value_exists)
done

setup_lifting type_definition_wf

subsection {* Lists as Tables *}

type_synonym ('a, 'b) table = "('a \<times> 'b) list"

fun lookup :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b" where
"lookup ((x, y) # t) v = (if v = x then y else (lookup t x))" |
"lookup [] x = undefined"

syntax "_ulookup" ::
  "('a \<times> 'b, '\<sigma>) uexpr \<Rightarrow> ('a, '\<sigma>) uexpr \<Rightarrow> ('b, '\<sigma>) uexpr" ("lookup\<^sub>u")

translations "lookup\<^sub>u t x" \<rightleftharpoons> "(CONST bop) (CONST lookup) t x"

subsection {* Positive Subtype (Laws) *}

text {* \todo{Move the following to the theory @{theory utp_expr}.} *}

syntax "_uRep_pos" :: "('a pos, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<section>'(_')")

translations "_uRep_pos p" \<rightleftharpoons> "(CONST uop) (CONST Rep_pos) p"

text {* \todo{Move the following to the theory @{theory Positive_New}.} *}

lemma ge_num_infinite_if_no_top:
"infinite {x::'a::{zero, linorder, no_top}. n \<le> x}"
apply (clarsimp)
-- {* From the assumption that the set is finite. *}
apply (subgoal_tac "\<exists>y::'a. Max {x. n \<le> x} < y")
apply (clarsimp)
apply (metis Max_ge leD mem_Collect_eq order.strict_implies_order order_refl order_trans)
using gt_ex apply (blast)
done

lemma less_zero_ordLeq_ge_zero:
"|{x::'a::{ordered_ab_group_add}. x < 0}| \<le>o |{x::'a. 0 \<le> x}|"
apply (rule_tac f = "uminus" in surj_imp_ordLeq)
apply (simp add: image_def)
apply (clarsimp)
apply (rule_tac x = "- x" in exI)
apply (simp)
done

text {* The next theorem is not totally trivial to prove! *}

instance pos :: ("{linordered_ab_group_add, no_top, continuum}") continuum
apply (intro_classes)
apply (case_tac "countable (UNIV :: 'a set)")
-- {* Subgoal 1 (Easy Case) *}
apply (rule disjI1)
apply (subgoal_tac "\<exists>to_nat::'a \<Rightarrow> nat. inj to_nat")
-- {* Subgoal 1.1 *}
apply (clarsimp)
apply (thin_tac "countable UNIV")
apply (rule_tac x = "to_nat o Rep_pos" in exI)
apply (rule inj_comp)
apply (assumption)
apply (meson Positive_New.pos.Rep_pos_inject injI)
-- {* Subgoal 1.2 *}
apply (blast)
-- {* Subgoal 2 (Difficult Case) *}
apply (rule disjI2)
apply (subst sym [OF equal_card_bij_betw])
apply (rule equal_card_intro)
apply (subgoal_tac "|UNIV::'a pos set| =o |{x::'a. 0 \<le> x}|")
-- {* Subgoal 2.1 *}
apply (erule ordIso_transitive)
apply (rule ordIso_symmetric)
apply (subgoal_tac "|UNIV::nat set set| =o |UNIV::'a set|")
-- {* Subgoal 2.1.1 *}
apply (erule ordIso_transitive)
apply (subgoal_tac "(UNIV::'a set) = {x.0 \<le> x} \<union> {x. x < 0}")
-- {* Subgoal 2.1.1.1 *}
apply (erule ssubst)
apply (rule card_of_Un_infinite_simps(1))
apply (rule ge_num_infinite_if_no_top)
apply (rule less_zero_ordLeq_ge_zero)
-- {* Subgoal 2.1.1.2 *}
apply (auto)
-- {* Subgoal 2.1.2 *}
apply (rule_tac f = "from_nat_set" in card_of_ordIsoI)
apply (rule_tac bij_betwI'; clarsimp?)
-- {* This is the only place where @{term "countable UNIV"} is needed. *}
apply (metis bij_betw_imp_surj from_nat_set_def surj_f_inv_f to_nat_set_bij)
apply (rule_tac x = "to_nat_set y" in exI)
apply (clarsimp)
-- {* Subgoal 2.2 *}
apply (rule_tac f = "Rep_pos" in card_of_ordIsoI)
apply (rule_tac bij_betwI'; clarsimp?)
apply (simp add: Positive_New.pos.Rep_pos_inject)
using Positive_New.pos.Rep_pos apply (blast)
apply (rule_tac x = "Abs_pos y" in exI)
apply (simp add: Positive_New.pos.Abs_pos_inverse)
done

subsection {* Time Model *}

text {*
  The rationale in this section is to define an abstract model of time that
  identifies reasonable assumptions that are sufficient for reasoning about
  model without having to specify in detail whether we are dealing with, for
  instance, discrete, continuous or super-dense time.
*}

subsubsection {* Abstract Time *}

text {*
  We introduce permissible time domains abstractly as a type class. Clearly,
  the elements of the type have to be linearly ordered, and membership to
  the class @{class semidom_divide} entails many key properties of addition,
  subtraction, multiplication and division. Note that we cannot require time
  to form a field as there may not be an additive inverse i.e.~if we confine
  ourselves to positive time instants. Lastly, we also assume that time does
  not stop, meaning that the order must have no top (class @{class no_top});
  it might have a bottom though which, if so, must be the same as @{term 0}.
*}

class time = linorder + semidom_divide + no_top

class pos_time = time + zero + order_bot +
assumes zero_is_bot: "0 = bot"

text {*
  I wonder if we can get away with weaker assumptions below. That would mean
  that we could also instantiate type @{typ "int pos"} as @{class time} and
  @{class pos_time}. If not, this is not an issue since we would typically
  use type @{typ nat} here in any case.
*}

instance pos :: (linordered_field) time
apply (intro_classes)
done

instantiation pos :: (linordered_field) pos_time
begin
lift_definition bot_pos :: "'a pos"
is "0" ..
instance
apply (intro_classes)
apply (transfer; simp)
apply (transfer; simp)
done
end

subsubsection {* Discrete Time *}

text {* Naturals, integers and rationals are used to model discrete time. *}

instance nat :: time
apply (intro_classes)
done

instance int :: time
apply (intro_classes)
done

instance rat :: time
apply (intro_classes)
done

instantiation nat :: pos_time
begin
instance
apply (intro_classes)
apply (unfold bot_nat_def)
apply (rule refl)
done
end

subsubsection {* Continuous Time *}

text {* Reals and positive reals are used to model continuous time. *}

type_notation real ("\<real>")

type_synonym pos_real = "real pos" ("\<real>\<^sup>+")

translations (type) "\<real>\<^sup>+" \<leftharpoondown> (type) "real pos"

instance real :: time
apply (intro_classes)
done

text {*
  Membership of @{typ "pos_real"} to the sort @{class time} follows from the
  earlier-on instantiation of @{typ "'a pos"} as @{class time}m provided the
  type parameter @{typ "'a"} constitutes a @{class linordered_field} instance.
*}

subsubsection {* Verifying Instantiations *}

text {* Instantiation of class @{class time}. *}

theorem "OFCLASS(nat, time_class)" ..
theorem "OFCLASS(int, time_class)" ..
theorem "OFCLASS(rat, time_class)" ..
theorem "OFCLASS(real, time_class)" ..
theorem "OFCLASS(rat pos, time_class)" ..
theorem "OFCLASS(real pos, time_class)" ..

text {* Instantiation of class @{class pos_time}. *}

theorem "OFCLASS(nat, pos_time_class)" ..
theorem "OFCLASS(rat pos, pos_time_class)" ..
theorem "OFCLASS(real pos, pos_time_class)" ..

text {* Instantiation of class @{class continuum}. *}

theorem "OFCLASS(nat, continuum_class)" ..
theorem "OFCLASS(int, continuum_class)" ..
theorem "OFCLASS(rat, continuum_class)" ..
theorem "OFCLASS(real, continuum_class)" ..
theorem "OFCLASS(int pos, continuum_class)" ..
theorem "OFCLASS(rat pos, continuum_class)" ..
theorem "OFCLASS(real pos, continuum_class)" ..

subsection {* FMI Types  *}

text {* In this section, we encode the various FMI types in HOL. *}

subsubsection {* TIME and NZTIME *}

text {*
  Our aim is to treat time abstractly in the FMI model via some arbitrary type
  @{typ "'\<tau>"} that is a member of class @{class time} or @{class pos_time}. We
  thus introduce some additional syntax here to facilitate obtaining the value
  universe of a time domain provided through a type @{typ "'\<tau>"}. This is just a
  syntactic sugar allowing us to write @{text "TIME('\<tau>)"} and @{text "NZTIME('\<tau>)"}
  while imposing the appropriate sort constraints on the free type @{typ "'\<tau>"}.
*}

class ctime = time + linordered_ab_group_add + continuum + two (* + injectable *)

syntax   "_TIME" :: "type \<Rightarrow> type" ("TIME'(_')")
syntax "_NZTIME" :: "type \<Rightarrow> type" ("NZTIME'(_')")

translations (type) "TIME('\<tau>)" \<rightleftharpoons> (type) "'\<tau>::ctime"
translations (type) "NZTIME('\<tau>)" \<rightleftharpoons> (type) "'\<tau>::ctime pos"

subsubsection {* FMI2COMP *}

text {*
  The type @{text FMI2COMP} of FMI component identifiers is introduced as a
  given (deferred) type. We can later change this i.e.~to give an explicit
  model that encodes FMI component identifiers as strings or natural numbers,
  for instance.
*}

typedecl FMI2COMP

-- {* Syntactic sugar for @{term "UNIV::FMI2COMP set"}. *}

abbreviation FMI2COMP :: "FMI2COMP set" where
"FMI2COMP \<equiv> UNIV"

text {* Instantiation the relevant classes for the axiomatic value model. *}

instantiation FMI2COMP :: typerep
begin
definition typerep_FMI2COMP :: "FMI2COMP itself \<Rightarrow> utype" where
[typing]: "typerep_FMI2COMP t = typerep.Typerep (STR ''fmi.FMI2COMP'') []"
instance ..
end

instantiation FMI2COMP :: typedep
begin
definition typedep_FMI2COMP :: "FMI2COMP itself \<Rightarrow> utype set" where
[typing]: "typedep_FMI2COMP t = {TYPEREP(FMI2COMP)}"
instance ..
end

-- {* The below facilitates evaluation of the transitive closure of the PDG. *}

instantiation FMI2COMP :: equal
begin
definition equal_FMI2COMP ::"FMI2COMP \<Rightarrow> FMI2COMP \<Rightarrow> bool" where
"equal_FMI2COMP x y = (x = y)"
instance
apply (intro_classes)
apply (unfold equal_FMI2COMP_def)
apply (rule refl)
done
end

inject_type FMI2COMP

text {* Instantiation the relevant classes for the deep value model. *}

text {*
  Clearly, this is not possible unless we endow the type with a concrete model
  using a @{text typedef} instead of a @{text typedecl}. On the other hand, the
  axiom introduced by the @{text sorry} below ought not lead to unsoundness.
*}

-- {* \todo{Introduce a concrete model for FMI components in order to be able
  to prove the instantiations below and remove the @{text sorry}.} *}

instance FMI2COMP :: "{continuum, two}"
sorry

subsubsection {* FMUSTATE *}

text {*
  Likewise, @{text FMUSTATE} is introduced as a given type for now. We may
  need to reviewing this in the future; for instance, the universal value
  model could be used to encode a generic (monomorphic) state type that can
  encode the state of arbitrary FMUs.
*}

typedecl FMUSTATE

text {* Instantiation the relevant classes for the axiomatic value model. *}

instantiation FMUSTATE :: typerep
begin
definition typerep_FMUSTATE :: "FMUSTATE itself \<Rightarrow> utype" where
[typing]: "typerep_FMUSTATE t = typerep.Typerep (STR ''fmi.FMUSTATE'') []"
instance ..
end

instantiation FMUSTATE :: typedep
begin
definition typedep_FMUSTATE :: "FMUSTATE itself \<Rightarrow> utype set" where
[typing]: "typedep_FMUSTATE t = {TYPEREP(FMUSTATE)}"
instance ..
end

inject_type FMUSTATE

text {* Instantiation the relevant classes for the deep value model. *}

text {*
  Clearly, this is not possible unless we endow the type with a concrete model
  using a @{text typedef} instead of a @{text typedecl}. On the other hand, the
  axiom introduced by the @{text sorry} below ought not lead to unsoundness.
*}

-- {* \todo{Introduce a concrete model for FMI states in order to be able to
  prove the instantiations below and remove the @{text sorry}.} *}

instance FMUSTATE :: "{continuum, two}"
sorry

subsubsection {* VAR and VAL *}

text {*
  The types of @{text VAR} and @{text VAL} are next equated with the unified
  variable and value types of the axiomatic value model. While we could have
  alternatively used deep variables here, an approach via axiomatic variables
  implies that there are no restrictions on modelling FMI types. An issue is
  that @{text VAL} is clearly not injectable, at least in the original model.
  The ranked axiomatic model, however, solves that problem.
*}

type_synonym VAR = "uvar.uvar" ("VAR")
type_synonym VAL = "uval.uval" ("VAL")

text {* Hack: there are still issues with supporting axiomatic variables. *}

instance uval     ::        "{continuum, two}" sorry
instance uvar_ext :: (type) "{continuum, two}" sorry

subsubsection {* FMIST and FMISTF *}

text {* We here declare datatypes for @{text fmi2Status} of the FMI API. *}

datatype FMI2ST =
  fmi2OK |
  fmi2Error |
  fmi2Fatal
  (*fmi2Warning *)
  (*fmi2Penidng *)

text {* Instantiation the relevant classes for the axiomatic value model. *}

inject_type FMI2ST

text {* Instantiation the relevant classes for the deep value model. *}

text {* We note that countability implies membership to @{class continuum} *}

instance FMI2ST :: countable
apply (countable_datatype)
done

instance FMI2ST :: continuum
apply (intro_classes)
done

instance FMI2ST :: two
apply (intro_classes)
apply (rule instance_twoI)
apply (rule_tac x = "fmi2OK" in exI)
apply (rule_tac x = "fmi2Error" in exI)
apply (clarsimp)
done

subsubsection {* FMUSTF *}

datatype FMI2STF =
  fmi2Status "FMI2ST" |
  fmi2Discard

text {* Instantiation the relevant classes for the axiomatic value model. *}

inject_type FMI2STF

text {* Instantiation the relevant classes for the deep value model. *}

text {* We note that countability implies membership to @{class continuum} *}

instance FMI2STF :: countable
apply (countable_datatype)
done

instance FMI2STF :: continuum
apply (intro_classes)
done

instance FMI2STF :: two
apply (intro_classes)
apply (rule instance_twoI)
apply (rule_tac x = "fmi2Status _" in exI)
apply (rule_tac x = "fmi2Discard" in exI)
apply (clarsimp)
done

subsubsection {* ErrorFlags *}

typedef ErrorFlags = "{fmi2Error, fmi2Fatal}"
apply (rule_tac x = "fmi2Error" in exI)
apply (clarsimp)
done

text {* TODO: Complete the proof below, should not be too difficult. *}

instance ErrorFlags :: "{continuum, two}" sorry

subsection {* FMI Events *}

text {*
  While the trace type for CSP is fixed to @{typ "'a list"}, we still have to
  define the event type @{typ "'a"}. Generally, we can think of events as sum
  types. Since events may be parametric, there is once again the issue of how
  to model events with different (HOL) types as a single unified type. A deep
  model may encode them as pairs consisting of a name \& type. Below, we adopt
  a shallow model that uses a datatype construction. Similar to the more field
  of extensible records, we endow the datatype with an extension field. It is
  still an open issue how we conveniently support compositional declarations
  of new channels; Simon mentioned \emph{prisms} as an analogue of lenses for
  sum types. As somewhat \textit{ad hoc} solution is presented below.
*}

subsubsection {* FMI API Channels *}

text {*
  We note that all constructor functions are of type @{type chan}. To obtain
  extensible events types, we introduce a prefixing (scoping) operator for each
  channel type that lifts the underlying datatype into a @{type sum} type with
  an open slot for later extension. Eventually, those prefix operators will be
  introduced automatically by the tool, namely through a custom @{text events}
  command for defining channel events.
*}

datatype '\<tau>::ctime fmi_event =
  fmi2Get "FMI2COMP \<times> VAR \<times> VAL \<times> FMI2ST" |
  fmi2Set "FMI2COMP \<times> VAR \<times> VAL \<times> FMI2STF" |
  fmi2DoStep "FMI2COMP \<times> TIME('\<tau>) \<times> NZTIME('\<tau>) \<times> FMI2STF" |
  fmi2Instantiate "FMI2COMP \<times> bool" |
  fmi2SetUpExperiment "FMI2COMP \<times> TIME('\<tau>) \<times> bool \<times> TIME('\<tau>) \<times> FMI2ST" |
  fmi2EnterInitializationMode "FMI2COMP \<times> FMI2ST" |
  fmi2ExitInitializationMode "FMI2COMP \<times> FMI2ST" |
  fmi2GetBooleanStatusfmi2Terminated "FMI2COMP \<times> bool \<times> FMI2ST" |
  fmi2GetMaxStepSize "FMI2COMP \<times> TIME('\<tau>) \<times> FMI2ST" |
  fmi2Terminate "FMI2COMP \<times> FMI2ST" |
  fmi2FreeInstance "FMI2COMP \<times> FMI2ST" |
  fmi2GetFMUState "FMI2COMP \<times> FMUSTATE \<times> FMI2ST" |
  fmi2SetFMUState "FMI2COMP \<times> FMUSTATE \<times> FMI2ST"

abbreviation fmi_prefix ::
  "('a, '\<tau>::ctime fmi_event) chan \<Rightarrow>
   ('a, ('\<tau>::ctime fmi_event) + 'ext) chan" where
"fmi_prefix c \<equiv> Inl o c"

notation fmi_prefix ("fmi:_" [1000] 1000)

abbreviation "fmi_events \<equiv>
  \<epsilon>(fmi:fmi2Get) \<union>
  \<epsilon>(fmi:fmi2Set) \<union>
  \<epsilon>(fmi:fmi2DoStep) \<union>
  \<epsilon>(fmi:fmi2Instantiate) \<union>
  \<epsilon>(fmi:fmi2SetUpExperiment) \<union>
  \<epsilon>(fmi:fmi2EnterInitializationMode) \<union>
  \<epsilon>(fmi:fmi2ExitInitializationMode) \<union>
  \<epsilon>(fmi:fmi2GetBooleanStatusfmi2Terminated) \<union>
  \<epsilon>(fmi:fmi2GetMaxStepSize) \<union>
  \<epsilon>(fmi:fmi2Terminate) \<union>
  \<epsilon>(fmi:fmi2FreeInstance) \<union>
  \<epsilon>(fmi:fmi2GetFMUState) \<union>
  \<epsilon>(fmi:fmi2SetFMUState)"

subsubsection {* Timer Process Channels *}

datatype '\<tau>::ctime timer_event =
  setT "TIME('\<tau>)" |
  updateSS "NZTIME('\<tau>)" |
  step "TIME('\<tau>) \<times> NZTIME('\<tau>)" |
  endc "unit"

abbreviation timer_prefix ::
  "('a, '\<tau>::ctime timer_event) chan \<Rightarrow>
   ('a, ('\<tau>::ctime fmi_event) + ('\<tau>::ctime timer_event) + 'ext) chan" where
"timer_prefix c \<equiv> Inr o Inl o c"

notation timer_prefix ("tm:_" [1000] 1000)

abbreviation "tm_events \<equiv>
  \<epsilon>(tm:step) \<union> \<epsilon>(tm:endc) \<union> \<epsilon>(tm:setT) \<union> \<epsilon>(tm:updateSS)"

subsubsection {* Interaction Process Channels *}

datatype control_event =
  stepToComplete "unit" |
  stepAnalysed "unit" |
  stepComplete "unit" |
  endsimulation "unit" |
  error (* "ErrorFlags" *) "FMI2ST"

abbreviation control_prefix ::
  "('a, control_event) chan \<Rightarrow>
    ('a, ('\<tau>::ctime fmi_event) + ('\<tau>::ctime timer_event) + (control_event)
      + 'ext) chan" where
"control_prefix c \<equiv> Inr o Inr o Inl o c"

notation control_prefix ("ctr:_" [1000] 1000)

abbreviation "ctr_events \<equiv>
  \<epsilon>(ctr:stepToComplete) \<union>
  \<epsilon>(ctr:stepAnalysed) \<union>
  \<epsilon>(ctr:stepComplete) \<union>
  \<epsilon>(ctr:endsimulation)"

subsection {* FMI Ports *}

text {*
  For readability, we introduce a @{command type_synonym} for ports. A port is
  encoded by a pair consisting of an FMI component (type @{type FMI2COMP}) and
  a variable (type @{type VAR}). We do not distinguish input and output ports.
*}

type_synonym port = "FMI2COMP \<times> VAR"

abbreviation FMU :: "port \<Rightarrow> FMI2COMP" where
"FMU port \<equiv> (fst port)"

abbreviation name :: "port \<Rightarrow> VAR" where
"name port \<equiv> (snd port)"

subsection {* FMI Configuration *}

text {*
  The configuration for a particular FMI system is introduced abstractly via
  HOL constants. A concrete model can provide overloaded definitions to give
  concrete meanings to them; this may allow us to potentially prove additional
  properties. An open question is whether some additional caveats need to be
  specified already here e.g.~that the port dependency graph is acyclic. This
  could possibly be done through a type definitions. We note that we encode
  the Z type @{text "seq"} by HOL's list type @{typ "'a list"}.
*}

text {*
  In line with the example in the deliverable D2.2d, I introduced a function
  @{text initialValues} rather than using the @{text inputs} sequence in order
  to provide initial values. This also proves to be slightly more convenient
  in terms of mechanisation. Also, I changed the type of the port-dependency
  graph to become a function rather than a relation, associating a list of
  inputs with each outputs. The advantage of this is that it facilitates the
  definition of the @{text DistributeInputs} action since currently, iterated
  sequence of actions is only define by lists but not for (finite) sets.
*}

consts FMUs :: "FMI2COMP list"
consts parameters :: "(FMI2COMP \<times> VAR \<times> VAL) list"
consts initialValues :: "(FMI2COMP \<times> VAR \<times> VAL) list"
-- {* Before: @{text "consts inputs :: \"(FMI2COMP \<times> VAR \<times> VAL) list\""} *}
consts inputs :: "port list"
consts outputs :: "port list"
-- {* Before: @{text "consts pdg :: \"port relation\""}. *}
consts pdg :: "port \<Rightarrow> (port list)"

(* TODO: The below should go into a separate file! *)

(*
subsubsection {* Instantiation with the Example in D2.2d *}

text {*
  Instead of using natural numbers to name variables, I am using actual names
  @{text x}, @{text y} and @{text z} below. Perhaps more meaningful names can
  be chosen, for this I would need to understand in more details that nature
  of the example.
*}

paragraph {* FMU Components *}

axiomatization
  pdsgfmu1 :: "FMI2COMP" and
  pdsgfmu2 :: "FMI2COMP" and
  samplerfmu :: "FMI2COMP" and
  checkequalityfmu :: "FMI2COMP" where
  fmus_distinct : "distinct [pdsgfmu1, pdsgfmu2, samplerfmu, checkequalityfmu]" and
  FMI2COMP_def : "FMI2COMP = {pdsgfmu1, pdsgfmu2, samplerfmu, checkequalityfmu}"

paragraph {* Parameters *}

text {* I am not sure about the below. Perhaps ask Ana and/or Jim. *}

overloading
  D2_2d_parameters \<equiv> "parameters :: (FMI2COMP \<times> VAR \<times> VAL) list"
begin
  definition D2_2d_parameters :: "(FMI2COMP \<times> VAR \<times> VAL) list" where
  "D2_2d_parameters = [
    (pdsgfmu1, $x:{nat}\<^sub>u, InjU (1::nat)),
    (pdsgfmu1, $y:{nat}\<^sub>u, InjU (1::nat)),
    (pdsgfmu2, $x:{nat}\<^sub>u, InjU (1::nat)),
    (pdsgfmu2, $y:{nat}\<^sub>u, InjU (1::nat))]"
end

paragraph {* Inputs *}

overloading
  D2_2d_inputs \<equiv> "inputs :: (FMI2COMP \<times> VAR) list"
begin
  definition D2_2d_inputs :: "(FMI2COMP \<times> VAR) list" where
  "D2_2d_inputs = [
    (samplerfmu, $x:{nat}\<^sub>u),
    (samplerfmu, $y:{nat}\<^sub>u),
    (checkequalityfmu, $y:{nat}\<^sub>u),
    (checkequalityfmu, $z:{nat}\<^sub>u)]"
end

overloading
  D2_2d_initialValues \<equiv> "initialValues :: (FMI2COMP \<times> VAR \<times> VAL) list"
begin
  definition D2_2d_initialValues :: "(FMI2COMP \<times> VAR \<times> VAL) list" where
  "D2_2d_initialValues = [
    (samplerfmu, $x:{nat}\<^sub>u, InjU (1::nat)),
    (samplerfmu, $y:{nat}\<^sub>u, InjU (1::nat)),
    (checkequalityfmu, $y:{nat}\<^sub>u, InjU (1::nat)),
    (checkequalityfmu, $z:{nat}\<^sub>u, InjU (1::nat))]"
end

paragraph {* Outputs *}

overloading
  D2_2d_outputs \<equiv> "outputs :: (FMI2COMP \<times> VAR) list"
begin
  definition D2_2d_outputs :: "(FMI2COMP \<times> VAR) list" where
  "D2_2d_outputs = [
    (pdsgfmu1, $x:{nat}\<^sub>u),
    (pdsgfmu2, $y:{nat}\<^sub>u),
    (samplerfmu, $z:{nat}\<^sub>u)]"
end
*)

subsection {* Simulation Parameters *}

text {* For now, I added the following as global constants too. *}

consts startTime :: "TIME('\<tau>)"
consts stopTimeDefined :: "bool"
consts stopTime :: "TIME('\<tau>)"

text {* We can instantiate them as in the example of the  D2.2d deliverable. *}

overloading D2_2d_startTime \<equiv> "startTime :: TIME('\<tau>)"
begin
  definition D2_2d_startTime :: "TIME('\<tau>)" where
  "D2_2d_startTime = 0"
end

overloading D2_2d_stopTimeDefined \<equiv> "stopTimeDefined :: bool"
begin
  definition D2_2d_stopTimeDefined :: "bool" where
  "D2_2d_stopTimeDefined = True"
end

overloading D2_2d_stopTime \<equiv> "stopTime :: TIME('\<tau>)"
begin
  definition D2_2d_stopTime :: "TIME('\<tau>)" where
  "D2_2d_stopTime = 5"
end

subsection {* FMI Processes *}

text {*
  A problem with the {\Circus} process encoding below is that, currently, it
  is not possible to write prefixes that mix inputs and outputs. Hence, I had
  to adopt a trick which converts everything into a single input prefix. That
  input imposes constraints so that some parts of the communication effectively
  behave like outputs. A second issue is that, referring to page 16 of D2.2d,
  we see that the @{text AllowGetsAndSets} action is actually parametric. My
  translation currently does not support parametric actions; hence I adopted
  a solution that encodes procedure parameters by local variables. Due to the
  proper treatment of scope by Isabelle/UTP, we generally get away with this.
  Both issues can thus be overcome; an integration of syntax translations that
  conceals the manual rewrites and adjustments done below is pending work.
*}

subsubsection {* General Timer *}

text {* \todo{Write the same process as below with axiomatic variables.} *}

definition
"process Timer(ct::TIME('\<tau>), hc::NZTIME('\<tau>), tN::TIME('\<tau>)) \<triangleq> begin
  state(vstore)
  Step =
    (tm:setT?(t : \<guillemotleft>t \<le> tN\<guillemotright>) \<rightarrow>\<^sub>\<C> (<currentTime> := \<guillemotleft>t\<guillemotright>) ;; Step) \<box>
    (tm:updateSS?(ss : true) \<rightarrow>\<^sub>\<C> (<stepSize> := \<guillemotleft>ss\<guillemotright>) ;; Step) \<box>
    (tm:step![out]((&<currentTime>, &<stepsize>)\<^sub>u) \<rightarrow>\<^sub>\<C>
      (<currentTime::'\<tau>> :=
        min\<^sub>u(&<currentTime> + \<section>(&<stepSize::'\<tau> pos>), \<guillemotleft>tN\<guillemotright>)) ;; Step) \<box>
    ((&<currentTime> =\<^sub>u \<guillemotleft>tN\<guillemotright>) &\<^sub>u tm:endc \<rightarrow>\<^sub>\<C> Stop)
  \<bullet> (<currentTime>, <stepSize> := \<guillemotleft>ct\<guillemotright>, \<guillemotleft>hc\<guillemotright>) ;; Step
end"

definition
"process TimerNew(ct::TIME('\<tau>), hc::NZTIME('\<tau>), tN::TIME('\<tau>)) \<triangleq> begin
  state(vstore)
  Step =
    (tm:setT?(t : \<guillemotleft>t \<le> tN\<guillemotright>) \<rightarrow>\<^sub>\<C> (<currentTime> := \<guillemotleft>t\<guillemotright>) ;; Step) \<box>
    (tm:updateSS?(ss) \<rightarrow>\<^sub>\<C> (<stepSize> := \<guillemotleft>ss\<guillemotright>) ;; Step) \<box>
    (tm:step![out\<^sub>1]($<currentTime>)![out\<^sub>2]($<stepsize>) \<rightarrow>\<^sub>\<C>
      (<currentTime::'\<tau>> :=
        min\<^sub>u(&<currentTime> + \<section>(&<stepSize::'\<tau> pos>), \<guillemotleft>tN\<guillemotright>)) ;; Step) \<box>
    ((&<currentTime> =\<^sub>u \<guillemotleft>tN\<guillemotright>) &\<^sub>u tm:endc \<rightarrow>\<^sub>\<C> Stop)
  \<bullet> (<currentTime>, <stepSize> := \<guillemotleft>ct\<guillemotright>, \<guillemotleft>hc\<guillemotright>) ;; Step
end"

subsubsection {* Interaction *}

text {*
  Note that I changed the type of @{text rinps} with respect to the tentative
  model given in the deliverable D2.2d. That is, instead of using the partial
  function type @{typ "FMI2COMP \<rightharpoonup> (VAR \<rightharpoonup> VAL)"} for @{text rinps}, I decided
  to use the list @{typ "((FMI2COMP \<times> VAR) \<times> VAL) list"}. This is (currently)
  a technicality since there are issues with using function types in prefixes,
  to do with Simon's embedding of shallow variables. Using lists circumvents
  the issue for and ought not limit generality since we may reasonably assume
  that the port-dependency graph is a finite relation.
*}

text {* Process State: @{term "rinps :: (port \<times> VAL) list"}. *}

definition
"process Interaction \<triangleq> begin
  state(vstore)
  Instantiation = (;; i : FMUs \<bullet>
    fmi:fmi2Instantiate?\<^sub>u(i_sc : \<pi>\<^sub>1(\<guillemotleft>i_sc\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow> Skip) and

  InstantiationMode =
    (if\<^sub>\<C> \<guillemotleft>parameters = []\<guillemotright> then\<^sub>\<C>
      (;; i : FMUs \<bullet>
        fmi:fmi2SetUpExperiment?\<^sub>u(i_startTime_stopTimeDefined_stopTime_st :
          \<pi>\<^sub>1(\<guillemotleft>i_startTime_stopTimeDefined_stopTime_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright> \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_startTime_stopTimeDefined_stopTime_st\<guillemotright>)) =\<^sub>u \<guillemotleft>startTime\<guillemotright> \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_startTime_stopTimeDefined_stopTime_st\<guillemotright>))) =\<^sub>u \<guillemotleft>stopTimeDefined\<guillemotright> \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_startTime_stopTimeDefined_stopTime_st\<guillemotright>)))) =\<^sub>u \<guillemotleft>stopTime\<guillemotright>)
            \<rightarrow> Skip) ;;
      (;; i : FMUs \<bullet>
        fmi:fmi2EnterInitializationMode?\<^sub>u(i_st : \<pi>\<^sub>1(\<guillemotleft>i_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow> Skip)
    else\<^sub>\<C>
      (;; i_x_v : parameters \<bullet>
        fmi:fmi2Set?\<^sub>u(i_x_v_st :
          \<pi>\<^sub>1(\<guillemotleft>i_x_v_st\<guillemotright>) =\<^sub>u \<pi>\<^sub>1(\<guillemotleft>i_x_v\<guillemotright>) \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_x_v_st\<guillemotright>)) =\<^sub>u \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_x_v\<guillemotright>)) \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_x_v_st\<guillemotright>))) =\<^sub>u \<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_x_v\<guillemotright>))) \<rightarrow> Skip) ;;
      (;; i : FMUs \<bullet>
        fmi:fmi2SetUpExperiment?\<^sub>u(i_startTime_stopTimeDefined_stopTime_st :
          \<pi>\<^sub>1(\<guillemotleft>i_startTime_stopTimeDefined_stopTime_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright> \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_startTime_stopTimeDefined_stopTime_st\<guillemotright>)) =\<^sub>u \<guillemotleft>startTime\<guillemotright> \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_startTime_stopTimeDefined_stopTime_st\<guillemotright>))) =\<^sub>u \<guillemotleft>stopTimeDefined\<guillemotright> \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_startTime_stopTimeDefined_stopTime_st\<guillemotright>)))) =\<^sub>u \<guillemotleft>stopTime\<guillemotright>)
            \<rightarrow> Skip) ;;
      (;; i : FMUs \<bullet>
        fmi:fmi2EnterInitializationMode?\<^sub>u(i_st : \<pi>\<^sub>1(\<guillemotleft>i_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow> Skip)) and

  InitializationMode =
    (if\<^sub>\<C> \<guillemotleft>initialValues = []\<guillemotright> then\<^sub>\<C>
      (;; i : FMUs \<bullet>
        fmi:fmi2ExitInitializationMode?\<^sub>u(i_st : \<pi>\<^sub>1(\<guillemotleft>i_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow> Skip)
    else\<^sub>\<C>
      (;; i_x_v : initialValues \<bullet>
        fmi:fmi2Set?\<^sub>u(i_x_v_st :
          \<pi>\<^sub>1(\<guillemotleft>i_x_v_st\<guillemotright>) =\<^sub>u \<pi>\<^sub>1(\<guillemotleft>i_x_v\<guillemotright>) \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_x_v_st\<guillemotright>)) =\<^sub>u \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_x_v\<guillemotright>)) \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_x_v_st\<guillemotright>))) =\<^sub>u \<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_x_v\<guillemotright>))) \<rightarrow> Skip) ;;
      (;; i : FMUs \<bullet>
        fmi:fmi2ExitInitializationMode?\<^sub>u(i_st : \<pi>\<^sub>1(\<guillemotleft>i_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow> Skip)) and

  Terminated = (;; i : FMUs \<bullet>
    fmi:fmi2Terminate?\<^sub>u(i_st : \<pi>\<^sub>1(\<guillemotleft>i_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow>
    fmi:fmi2FreeInstance?\<^sub>u(i_st : \<pi>\<^sub>1(\<guillemotleft>i_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow> Skip) ;;
    ctr:endsimulation \<rightarrow>\<^sub>u Skip and

  TakeOutputs = <rinp::(port \<times> VAL) list> := \<langle>\<rangle> ;;
    (;; out : outputs \<bullet> fmi:fmi2Get?\<^sub>u(i_x_v_st :
      \<pi>\<^sub>1(\<guillemotleft>i_x_v_st\<guillemotright>) =\<^sub>u \<guillemotleft>FMU out\<guillemotright> \<and>
      \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_x_v_st\<guillemotright>)) =\<^sub>u \<guillemotleft>name out\<guillemotright>) \<rightarrow>
        (;; inp : pdg out \<bullet>
          <rinp> := &<rinp> ^\<^sub>u \<langle>(\<guillemotleft>inp\<guillemotright>, \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(&i_x_v_st))))\<^sub>u\<rangle>)) and

  DistributeInputs = (;; inp : inputs \<bullet>
    fmi:fmi2Set?\<^sub>u(i_x_v_st :
      \<pi>\<^sub>1(\<guillemotleft>i_x_v_st\<guillemotright>) =\<^sub>u \<guillemotleft>FMU inp\<guillemotright> \<and>
      \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_x_v_st\<guillemotright>)) =\<^sub>u \<guillemotleft>name inp\<guillemotright> \<and>
      \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_x_v_st\<guillemotright>))) =\<^sub>u (lookup\<^sub>u $<rinp> \<guillemotleft>inp\<guillemotright>)) \<rightarrow> Skip) and

  Step = (;; i : [0..(length FMUs)] \<bullet>
    (if (i::int) = 0 then
      ctr:stepToComplete \<rightarrow>\<^sub>u
        (fmi:fmi2DoStep?\<^sub>u(i_t_hc_st :
          \<pi>\<^sub>1(\<guillemotleft>i_t_hc_st\<guillemotright>) =\<^sub>u \<guillemotleft>nth FMUs 1\<guillemotright> \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_t_hc_st\<guillemotright>)) =\<^sub>u $<t> \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_t_hc_st\<guillemotright>))) =\<^sub>u $<hc>) \<rightarrow> Skip)
    else if (i::int) < (length FMUs) then
      (\<mu> X \<bullet>
        (fmi:fmi2GetBooleanStatusfmi2Terminated?\<^sub>u(i_b_st :
          \<pi>\<^sub>1(\<guillemotleft>i_b_st\<guillemotright>) =\<^sub>u \<guillemotleft>nth FMUs (nat i)\<guillemotright>) \<rightarrow> X) \<box>
        (fmi:fmi2GetMaxStepSize?\<^sub>u(i_t_st :
          \<pi>\<^sub>1(\<guillemotleft>i_t_st\<guillemotright>) =\<^sub>u \<guillemotleft>nth FMUs (nat i)\<guillemotright>) \<rightarrow> X)) \<box>
        (fmi:fmi2DoStep?\<^sub>u(i_t_hc_st :
          \<pi>\<^sub>1(\<guillemotleft>i_t_hc_st\<guillemotright>) =\<^sub>u \<guillemotleft>nth FMUs (nat (i+1))\<guillemotright> \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_t_hc_st\<guillemotright>)) =\<^sub>u $<t> \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_t_hc_st\<guillemotright>))) =\<^sub>u $<hc>) \<rightarrow> Skip)
    else
      (\<mu> X \<bullet>
        (fmi:fmi2GetBooleanStatusfmi2Terminated?\<^sub>u(i_b_st :
          \<pi>\<^sub>1(\<guillemotleft>i_b_st\<guillemotright>) =\<^sub>u \<guillemotleft>nth FMUs (nat i)\<guillemotright>) \<rightarrow> X) \<box>
        (fmi:fmi2GetMaxStepSize?\<^sub>u(i_t_st :
          \<pi>\<^sub>1(\<guillemotleft>i_t_st\<guillemotright>) =\<^sub>u \<guillemotleft>nth FMUs (nat i)\<guillemotright>) \<rightarrow> X)) \<box>
        (ctr:stepAnalysed \<rightarrow>\<^sub>u Skip))) and

  slaveInitialized =
    (tm:endc \<rightarrow>\<^sub>u Terminated) \<box>
    (tm:step?\<^sub>u(t_hc : true) \<rightarrow>
      (* Used local variables to pass action parameters! *)
      (<t>, <hc> := \<pi>\<^sub>1(&t_hc), \<pi>\<^sub>2(&t_hc)) ;;
      TakeOutputs ;; DistributeInputs ;; Step) and

  NextStep =
    (tm:updateSS?\<^sub>u(d : true) \<rightarrow> NextStep) \<box>
    (tm:setT?\<^sub>u(t : true) \<rightarrow> NextStep) \<box>
    (slaveInitialized ;; NextStep) \<box>
    (Terminated)

  \<bullet> Instantiation ;; InstantiationMode ;; InitializationMode ;; slaveInitialized
end"

theorem "P Interaction"
apply (unfold Interaction_def)
apply (simp add: circus_syntax Let_def)
oops

text {* A simplified definition of the same (?) process is given below. *}

definition
"process InteractionSimplified \<triangleq> begin
  state(vstore)
  Instantiation = (;; i : FMUs \<bullet>
    fmi:fmi2Instantiate?\<^sub>u(i_sc : \<pi>\<^sub>1(\<guillemotleft>i_sc\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow> Skip) and

  InstantiationMode =
    (;; i_x_v : parameters \<bullet>
      fmi:fmi2Set?\<^sub>u(i_x_v_st :
        \<pi>\<^sub>1(\<guillemotleft>i_x_v_st\<guillemotright>) =\<^sub>u \<pi>\<^sub>1(\<guillemotleft>i_x_v\<guillemotright>) \<and>
        \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_x_v_st\<guillemotright>)) =\<^sub>u \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_x_v\<guillemotright>)) \<and>
        \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_x_v_st\<guillemotright>))) =\<^sub>u \<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_x_v\<guillemotright>))) \<rightarrow> Skip) ;;
    (;; i : FMUs \<bullet>
      fmi:fmi2SetUpExperiment?\<^sub>u(i_startTime_stopTimeDefined_stopTime_st :
        \<pi>\<^sub>1(\<guillemotleft>i_startTime_stopTimeDefined_stopTime_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright> \<and>
        \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_startTime_stopTimeDefined_stopTime_st\<guillemotright>)) =\<^sub>u \<guillemotleft>startTime\<guillemotright> \<and>
        \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_startTime_stopTimeDefined_stopTime_st\<guillemotright>))) =\<^sub>u \<guillemotleft>stopTimeDefined\<guillemotright> \<and>
        \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_startTime_stopTimeDefined_stopTime_st\<guillemotright>)))) =\<^sub>u \<guillemotleft>stopTime\<guillemotright>)
          \<rightarrow> Skip) ;;
    (;; i : FMUs \<bullet>
      fmi:fmi2EnterInitializationMode?\<^sub>u(i_st : \<pi>\<^sub>1(\<guillemotleft>i_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow> Skip) and

  InitializationMode =
    (;; i_x_v : initialValues \<bullet>
      fmi:fmi2Set?\<^sub>u(i_x_v_st :
        \<pi>\<^sub>1(\<guillemotleft>i_x_v_st\<guillemotright>) =\<^sub>u \<pi>\<^sub>1(\<guillemotleft>i_x_v\<guillemotright>) \<and>
        \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_x_v_st\<guillemotright>)) =\<^sub>u \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_x_v\<guillemotright>)) \<and>
        \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_x_v_st\<guillemotright>))) =\<^sub>u \<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_x_v\<guillemotright>))) \<rightarrow> Skip) ;;
    (;; i : FMUs \<bullet>
      fmi:fmi2ExitInitializationMode?\<^sub>u(i_st : \<pi>\<^sub>1(\<guillemotleft>i_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow> Skip) and

  Terminated = (;; i : FMUs \<bullet>
    fmi:fmi2Terminate?\<^sub>u(i_st : \<pi>\<^sub>1(\<guillemotleft>i_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow>
    fmi:fmi2FreeInstance?\<^sub>u(i_st : \<pi>\<^sub>1(\<guillemotleft>i_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow> Skip) ;;
    ctr:endsimulation \<rightarrow>\<^sub>u Skip and

  TakeOutputs = <rinp::(port \<times> VAL) list> := \<langle>\<rangle> ;;
    (;; out : outputs \<bullet> fmi:fmi2Get?\<^sub>u(i_x_v_st :
      \<pi>\<^sub>1(\<guillemotleft>i_x_v_st\<guillemotright>) =\<^sub>u \<guillemotleft>FMU out\<guillemotright> \<and>
      \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_x_v_st\<guillemotright>)) =\<^sub>u \<guillemotleft>name out\<guillemotright>) \<rightarrow>
        (;; inp : pdg out \<bullet>
          <rinp> := &<rinp> ^\<^sub>u \<langle>(\<guillemotleft>inp\<guillemotright>, \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(&i_x_v_st))))\<^sub>u\<rangle>)) and

  DistributeInputs = (;; inp : inputs \<bullet>
    fmi:fmi2Set?\<^sub>u(i_x_v_st :
      \<pi>\<^sub>1(\<guillemotleft>i_x_v_st\<guillemotright>) =\<^sub>u \<guillemotleft>FMU inp\<guillemotright> \<and>
      \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_x_v_st\<guillemotright>)) =\<^sub>u \<guillemotleft>name inp\<guillemotright> \<and>
      \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_x_v_st\<guillemotright>))) =\<^sub>u (lookup\<^sub>u $<rinp> \<guillemotleft>inp\<guillemotright>)) \<rightarrow> Skip) and

  Step = (;; i : [0..(length FMUs)] \<bullet>
    (if (i::int) = 0 then
      ctr:stepToComplete \<rightarrow>\<^sub>u
        (fmi:fmi2DoStep?\<^sub>u(i_t_hc_st :
          \<pi>\<^sub>1(\<guillemotleft>i_t_hc_st\<guillemotright>) =\<^sub>u \<guillemotleft>nth FMUs 1\<guillemotright> \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_t_hc_st\<guillemotright>)) =\<^sub>u $<t> \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_t_hc_st\<guillemotright>))) =\<^sub>u $<hc>) \<rightarrow> Skip)
    else if (i::int) < (length FMUs) then
      (\<mu> X \<bullet>
        (fmi:fmi2GetBooleanStatusfmi2Terminated?\<^sub>u(i_b_st :
          \<pi>\<^sub>1(\<guillemotleft>i_b_st\<guillemotright>) =\<^sub>u \<guillemotleft>nth FMUs (nat i)\<guillemotright>) \<rightarrow> X) \<box>
        (fmi:fmi2GetMaxStepSize?\<^sub>u(i_t_st :
          \<pi>\<^sub>1(\<guillemotleft>i_t_st\<guillemotright>) =\<^sub>u \<guillemotleft>nth FMUs (nat i)\<guillemotright>) \<rightarrow> X)) \<box>
        (fmi:fmi2DoStep?\<^sub>u(i_t_hc_st :
          \<pi>\<^sub>1(\<guillemotleft>i_t_hc_st\<guillemotright>) =\<^sub>u \<guillemotleft>nth FMUs (nat (i+1))\<guillemotright> \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_t_hc_st\<guillemotright>)) =\<^sub>u $<t> \<and>
          \<pi>\<^sub>1(\<pi>\<^sub>2(\<pi>\<^sub>2(\<guillemotleft>i_t_hc_st\<guillemotright>))) =\<^sub>u $<hc>) \<rightarrow> Skip)
    else
      (\<mu> X \<bullet>
        (fmi:fmi2GetBooleanStatusfmi2Terminated?\<^sub>u(i_b_st :
          \<pi>\<^sub>1(\<guillemotleft>i_b_st\<guillemotright>) =\<^sub>u \<guillemotleft>nth FMUs (nat i)\<guillemotright>) \<rightarrow> X) \<box>
        (fmi:fmi2GetMaxStepSize?\<^sub>u(i_t_st :
          \<pi>\<^sub>1(\<guillemotleft>i_t_st\<guillemotright>) =\<^sub>u \<guillemotleft>nth FMUs (nat i)\<guillemotright>) \<rightarrow> X)) \<box>
        (ctr:stepAnalysed \<rightarrow>\<^sub>u Skip))) and

  slaveInitialized =
    (tm:endc \<rightarrow>\<^sub>u Terminated) \<box>
    (tm:step?\<^sub>u(t_hc : true) \<rightarrow>
      (* Used local variables to pass action parameters! *)
      (<t>, <hc> := \<pi>\<^sub>1(&t_hc), \<pi>\<^sub>2(&t_hc)) ;;
      TakeOutputs ;; DistributeInputs ;; Step) and

  NextStep =
    (tm:updateSS?\<^sub>u(d : true) \<rightarrow> NextStep) \<box>
    (tm:setT?\<^sub>u(t : true) \<rightarrow> NextStep) \<box>
    (slaveInitialized ;; NextStep) \<box>
    (Terminated)

  \<bullet> Instantiation ;; InstantiationMode ;; InitializationMode ;; slaveInitialized
end"

definition
"process InteractionNew \<triangleq> begin
  state(vstore)
  Instantiation = (;; i : FMUs \<bullet>
    fmi:fmi2Instantiate.[out\<^sub>1](\<guillemotleft>i\<guillemotright>)?(sc) \<rightarrow>\<^sub>\<C> Skip) and

  InstantiationMode =
    (;; (i, x, v) : parameters \<bullet>
      fmi:fmi2Set![out\<^sub>1](\<guillemotleft>i\<guillemotright>)![out\<^sub>2](\<guillemotleft>x\<guillemotright>)![out\<^sub>3](\<guillemotleft>v\<guillemotright>)?(st) \<rightarrow>\<^sub>\<C> Skip) ;;
    (;; i : FMUs \<bullet>
      fmi:fmi2SetUpExperiment![out\<^sub>1](\<guillemotleft>i\<guillemotright>)![out\<^sub>2](\<guillemotleft>startTime\<guillemotright>)
        ![out\<^sub>3](\<guillemotleft>stopTimeDefined\<guillemotright>)![out\<^sub>4](\<guillemotleft>stopTime\<guillemotright>)?(st) \<rightarrow>\<^sub>\<C> Skip) ;;
    (;; i : FMUs \<bullet>
      fmi:fmi2EnterInitializationMode.[out\<^sub>1](\<guillemotleft>i\<guillemotright>)?(sc) \<rightarrow>\<^sub>\<C> Skip) and

  InitializationMode =
    (;; (i, x, v) : initialValues \<bullet>
      fmi:fmi2Set![out\<^sub>1](\<guillemotleft>i\<guillemotright>)![out\<^sub>2](\<guillemotleft>x\<guillemotright>)![out\<^sub>3](\<guillemotleft>v\<guillemotright>)?(st) \<rightarrow>\<^sub>\<C> Skip) ;;
    (;; i : FMUs \<bullet>
      fmi:fmi2ExitInitializationMode![out\<^sub>1](\<guillemotleft>i\<guillemotright>)?(sc) \<rightarrow>\<^sub>\<C> Skip) and

  Terminated =
    (;; i : FMUs \<bullet>
      fmi:fmi2Terminate.[out\<^sub>1](\<guillemotleft>i\<guillemotright>)?(sc) \<rightarrow>\<^sub>\<C>
      fmi:fmi2FreeInstance.[out\<^sub>1](\<guillemotleft>i\<guillemotright>)?(sc) \<rightarrow>\<^sub>\<C> Skip) ;;
    ctr:endsimulation \<rightarrow>\<^sub>\<C> Skip and

  TakeOutputs = <rinp::(port \<times> VAL) list> := \<langle>\<rangle> ;;
    (;; out : outputs \<bullet>
      fmi:fmi2Get.[out\<^sub>1](\<guillemotleft>FMU out\<guillemotright>).[out\<^sub>2](\<guillemotleft>name out\<guillemotright>)?(v)?(st) \<rightarrow>\<^sub>\<C>
        (;; inp : pdg out \<bullet> <rinp> := &<rinp> ^\<^sub>u \<langle>(\<guillemotleft>inp\<guillemotright>, \<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>)) and

  DistributeInputs = (;; inp : inputs \<bullet>
    fmi:fmi2Set.[out\<^sub>1](\<guillemotleft>FMU inp\<guillemotright>).[out\<^sub>2](\<guillemotleft>name inp\<guillemotright>)
      ![out\<^sub>3](lookup\<^sub>u $<rinp> \<guillemotleft>inp\<guillemotright>)?(st) \<rightarrow>\<^sub>\<C> Skip) and

  Step = (;; i : [0..(length FMUs)] \<bullet>
    (if (i::int) = 0 then
      ctr:stepToComplete \<rightarrow>\<^sub>\<C>
        (fmi:fmi2DoStep.[out\<^sub>1](\<guillemotleft>FMUs!0\<guillemotright>).[out\<^sub>2]($<t>).[out\<^sub>3]($<hc>)?(st) \<rightarrow>\<^sub>\<C> Skip)
    else if (i::int) < (length FMUs) then
      (\<mu> X \<bullet>
        (fmi:fmi2GetBooleanStatusfmi2Terminated.[out\<^sub>1](\<guillemotleft>FMUs!(nat (i-1))\<guillemotright>)?(b)?(st) \<rightarrow>\<^sub>\<C> X) \<box>
        (fmi:fmi2GetMaxStepSize.[out\<^sub>1](\<guillemotleft>FMUs!(nat (i-1))\<guillemotright>)?(t)?(st) \<rightarrow>\<^sub>\<C> X)) \<box>
        (fmi:fmi2DoStep.[out\<^sub>1](\<guillemotleft>FMUs!(nat i)\<guillemotright>).[out\<^sub>2]($<t>).[out\<^sub>3]($<hc>)?(st) \<rightarrow>\<^sub>\<C> Skip)
    else
      (\<mu> X \<bullet>
        (fmi:fmi2GetBooleanStatusfmi2Terminated.[out\<^sub>1](\<guillemotleft>FMUs!(nat (i-1))\<guillemotright>)?(b)?(st) \<rightarrow>\<^sub>\<C> X) \<box>
        (fmi:fmi2GetMaxStepSize.[out\<^sub>1](\<guillemotleft>FMUs!(nat (i-1))\<guillemotright>)?(t)?(st) \<rightarrow>\<^sub>\<C> X)) \<box>
        (ctr:stepAnalysed \<rightarrow>\<^sub>\<C> Skip))) and

  slaveInitialized =
    (tm:endc \<rightarrow>\<^sub>\<C> Terminated) \<box>
    (tm:step?(t)?(hc) \<rightarrow>\<^sub>\<C>
      (* We use local variables to pass action parameters! *)
      (<t>, <hc> := \<guillemotleft>t\<guillemotright>, \<guillemotleft>hc\<guillemotright>) ;;
      TakeOutputs ;; DistributeInputs ;; Step) and

  NextStep =
    (tm:updateSS?(d) \<rightarrow>\<^sub>\<C> NextStep) \<box>
    (tm:setT?(t) \<rightarrow>\<^sub>\<C> NextStep) \<box>
    (slaveInitialized ;; NextStep) \<box>
    (Terminated)

  \<bullet> Instantiation ;; InstantiationMode ;; InitializationMode ;; slaveInitialized
end"

theorem "P InteractionNew"
apply (unfold InteractionNew_def)
apply (simp add: circus_syntax Let_def)
oops

subsubsection {* End Simulation *}

definition
"endSimulation = ctr:endsimulation \<rightarrow>\<^sub>u Skip"

subsubsection {* States Managers *}

text {* \todo{Write the same process as below with axiomatic variables.} *}

definition
"process FMUStatesManager(i::FMI2COMP) \<triangleq> begin
  state(vstore)
  AllowsGetsAndSets =
    (fmi:fmi2GetFMUState?\<^sub>u(i_s_st : \<pi>\<^sub>1(\<guillemotleft>i_s_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow>
      (<s> := \<pi>\<^sub>1(\<pi>\<^sub>2(&i_s_st)) ;; AllowsGetsAndSets)) \<box>
    (fmi:fmi2SetFMUState?\<^sub>u(i_s_st : \<pi>\<^sub>1(\<guillemotleft>i_s_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright> \<and> \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_s_st\<guillemotright>)) =\<^sub>u $<s>) \<rightarrow>
      (<s> := \<pi>\<^sub>1(\<pi>\<^sub>2(&i_s_st)) ;; AllowsGetsAndSets)) and
  AllowAGet =
    (fmi:fmi2GetFMUState?\<^sub>u(i_s_st : \<pi>\<^sub>1(\<guillemotleft>i_s_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow>
      (<s> := \<pi>\<^sub>1(\<pi>\<^sub>2(&i_s_st)) ;; AllowsGetsAndSets))
  \<bullet> fmi:fmi2Instantiate?\<^sub>u(i_b : \<pi>\<^sub>1(\<guillemotleft>i_b\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow> AllowAGet
end"

definition
"process FMUStatesManagerNew(i::FMI2COMP) \<triangleq> begin
  state(vstore)
  AllowsGetsAndSets =
    (fmi:fmi2GetFMUState![out](\<guillemotleft>i\<guillemotright>)?(s)?(st) \<rightarrow>\<^sub>\<C> (<s> := \<guillemotleft>s\<guillemotright>) ;; AllowsGetsAndSets) \<box>
    (fmi:fmi2SetFMUState![out\<^sub>1](\<guillemotleft>i\<guillemotright>)![out\<^sub>2](&<s>) \<rightarrow>\<^sub>\<C> AllowsGetsAndSets) and
  AllowAGet =
    (fmi:fmi2GetFMUState![out](\<guillemotleft>i\<guillemotright>)?(s)?(st) \<rightarrow>\<^sub>\<C> (<s> := \<guillemotleft>s\<guillemotright>) ;; AllowsGetsAndSets)
  \<bullet> fmi:fmi2Instantiate![out](\<guillemotleft>i\<guillemotright>)?(b) \<rightarrow>\<^sub>\<C> AllowAGet
end"

definition
"process NoStatesManager \<triangleq>
  ( ||| i : FMUs \<bullet> fmi:fmi2Instantiate?\<^sub>u(i_b : \<pi>\<^sub>1(\<guillemotleft>i_b\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow> Stop) \<triangle>
    endSimulation"

theorem "FMUStatesManager i = ABC"
apply (unfold FMUStatesManager_def)
apply (simp add: circus_syntax)
oops

subsubsection {* Error Handling *}

definition
"process ErrorMonitor(mst::FMI2ST) \<triangleq>
begin
  state(vstore)
  StopError =
    ((&<st> =\<^sub>u \<guillemotleft>mst\<guillemotright>) &\<^sub>u ctr:error!\<^sub>u(\<guillemotleft>mst\<guillemotright>) \<rightarrow> (*Monitor*) Skip) \<box>
    ((&<st> \<noteq>\<^sub>u \<guillemotleft>mst\<guillemotright>) &\<^sub>u ctr:error!\<^sub>u(\<guillemotleft>mst\<guillemotright>) \<rightarrow> (*Monitor*) Skip) and

  Monitor =
    (fmi:fmi2Get?\<^sub>u(i_n_v_st : true) \<rightarrow>
      (<st> := \<pi>\<^sub>2(\<pi>\<^sub>2(\<pi>\<^sub>2(&i_n_v_st))) ;; StopError))

  \<bullet> Monitor \<triangle> (ctr:endsimulation \<rightarrow>\<^sub>u Skip)
end"

subsubsection {* Master Algorithm *}

definition
"process FMUStatesManagers \<triangleq>
  ||| i : FMUs \<bullet> FMUStatesManager(i) \<triangle> endSimulation"

definition
"process TimedInteraction(t0, tN) \<triangleq>
  ((Timer(t0, Abs_pos 2, tN) \<triangle> endSimulation)
    [| tm_events \<union> \<epsilon>(ctr:endsimulation) |]
  Interaction) \\ (\<epsilon>(ctr:stepAnalysed) \<union> \<epsilon>(ctr:stepComplete)) \\ tm_events"

definition
"process MAlgorithm(t0, tN) \<triangleq>
  (TimedInteraction(t0, tN)
    [| \<epsilon>(ctr:endsimulation) \<union> \<epsilon>(fmi:fmi2Instantiate) |]
  FMUStatesManagers)"

subsubsection {* General Behaviour of an FMU *}

definition RUN :: "'\<epsilon> set \<Rightarrow> ('\<sigma>, '\<epsilon>) action" where
"RUN evts = undefined"

(* I think the problem below is that the state space of i_b includes the whole
   of the reactive alphabet whereas the guard operator only expects a predicate
   on the state variables...
*)

(*
definition
"process FMUInterface(i::FMI2COMP) \<triangleq>
begin
  Instantiated =
    (&<st> =\<^sub>u \<guillemotleft>fmi2Fatal\<guillemotright>) &\<^sub>u RUN(fmi_events) and
  Instantiation =
    (fmi:fmi2Instantiate?\<^sub>u(i_b : \<pi>\<^sub>1(\<guillemotleft>i_b\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow>
      ((\<pi>\<^sub>2(&i_b) =\<^sub>u \<guillemotleft>True\<guillemotright>) &\<^sub>u Instantiated))
  \<bullet> Instantiation \<triangle> endSimulation
end"
*)

subsection {* Proof Experiments *}

term "setT!\<^sub>u(\<guillemotleft>0\<guillemotright>) \<rightarrow> SKIP"
term "InputCSP setT x"
term "\<lceil>''x''\<rceil>\<^sub>d"
term "(dvar_lens \<lceil>''x''\<rceil>\<^sub>d)"
term "\<lceil>''x''\<rceil>\<^sub>d\<up>"
term "InputCircus setT (\<lceil>''x''\<rceil>\<^sub>d\<up>)"
end