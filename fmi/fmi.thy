(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: fmi.thy                                                              *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 8 Feb 2017 *)

section {* FMI {\Circus} Model *}

theory fmi
imports
  "../utp/utp_circus"
begin

hide_type Positive.pos -- {* I am using my revised version of that type here. *}

declare [[typedef_overloaded]]
declare [[quick_and_dirty]]

declare [[syntax_ambiguity_warning=false]]

default_sort type

subsection {* Preliminaries *}

text {* By default, the product type did not instantiate class @{class two}. *}

theorem card_ge_two_witness:
"finite S \<Longrightarrow> 2 \<le> card S = (\<exists>x y. x \<in> S \<and> y \<in> S \<and> x \<noteq> y)"
apply (rule iffI)
-- {* Subgoal 1 *}
apply (meson card_2_exists ex_card subsetCE)
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

subsection {* FMI Configuration *}

text {*
  The configuration for a particular FMI system is introduced abstractly via
  HOL constants. A concrete model can provide overloaded definitions of them
  to give concrete meanings, after which we will be able to potentially prove
  additional properties. An open question is whether some additional caveats
  need to be specified already here, such as that the port dependency graph is
  acyclic. This could possibly be done through type definitions. We note that
  we encode the Z type @{text "seq"} by HOL's list type @{typ "'a list"}.
*}

consts
  FMUs :: "FMI2COMP list"
  parameters :: "(FMI2COMP \<times> VAR \<times> VAL) list"
  inputs :: "(FMI2COMP \<times> VAR \<times> VAL) list"
  outputs :: "(FMI2COMP \<times> VAR) list"
  pdg :: "(VAR \<times> (FMI2COMP \<times> VAR)) set"

text_raw {* \clearpage *}

subsection {* FMI Processes *}

text {* \todo{Write the same process as below with axiomatic variables.} *}

definition
"process Timer(ct::TIME('\<tau>), hc::NZTIME('\<tau>), tN::TIME('\<tau>)) \<triangleq> begin
  Step =
    (tm:setT?\<^sub>u(t : \<guillemotleft>t \<le> tN\<guillemotright>) \<rightarrow> (<currentTime> := &t) ;; Step) \<box>
    (tm:updateSS?\<^sub>u(ss : true) \<rightarrow> (<stepSize> := &ss) ;; Step) \<box>
    (tm:step!\<^sub>u((&<currentTime>, &<stepsize>)\<^sub>u) \<rightarrow>
      (<currentTime::'\<tau>> := &<currentTime> + \<section>(&<stepSize::'\<tau> pos>)) ;; Step) \<box>
    (($<currentTime> =\<^sub>u \<guillemotleft>tN\<guillemotright>) &\<^sub>u tm:endc \<rightarrow>\<^sub>u Stop)
  \<bullet> (<currentTime>, <stepSize> := \<guillemotleft>ct\<guillemotright>, \<guillemotleft>hc\<guillemotright>) ;; Step
end"

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

text {* \todo{Write the same process as below with axiomatic variables.} *}

definition
"process FMUStatesManager(i::FMI2COMP) \<triangleq> begin
  AllowsGetsAndSets =
    (fmi:fmi2GetFMUState?\<^sub>u(i_t_st : \<pi>\<^sub>1(\<guillemotleft>i_t_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow>
      (<s> := \<pi>\<^sub>1(\<pi>\<^sub>2(&i_t_st)) ;; AllowsGetsAndSets)) \<box>
    (fmi:fmi2SetFMUState?\<^sub>u(i_s_st : \<pi>\<^sub>1(\<guillemotleft>i_s_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright> \<and> \<pi>\<^sub>1(\<pi>\<^sub>2(\<guillemotleft>i_s_st\<guillemotright>)) =\<^sub>u $<s>) \<rightarrow>
      (<s> := \<pi>\<^sub>1(\<pi>\<^sub>2(&i_s_st)) ;; AllowsGetsAndSets)) and
  AllowAGet = fmi:fmi2GetFMUState?\<^sub>u(i_s_st : \<pi>\<^sub>1(\<guillemotleft>i_s_st\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow>
    (<s> := \<pi>\<^sub>1(\<pi>\<^sub>2(&i_s_st)) ;; AllowsGetsAndSets)
  \<bullet> fmi:fmi2Instantiate?\<^sub>u(i_b : \<pi>\<^sub>1(\<guillemotleft>i_b\<guillemotright>) =\<^sub>u \<guillemotleft>i\<guillemotright>) \<rightarrow> AllowAGet
end"

theorem "FMUStatesManager i = ABC"
apply (unfold FMUStatesManager_def)
apply (simp add: circus_syntax)
oops

subsection {* Example from D2.2d (Appendix A) *}

subsubsection {* FMU Configuration *}

text {*
  Since FMUs are introduced by virtue of a given type (type declaration), we
  require an axiomatisation to define a concrete model for that type; this is
  unless we \emph{a priori} define a model for FMU identifiers, for instance,
  using natural numbers. The axiomatic approach is, however, not unusual and
  used, for instance, in the B Method to introduce new types.
*}

axiomatization
  sourcefmu :: "FMI2COMP" and
  dfspecfmu :: "FMI2COMP" and
  sinkfmu :: "FMI2COMP" where
  FMI2COMP_def: "FMI2COMP = {sourcefmu, dfspecfmu, sinkfmu}" and
  fmus_distinct: "distinct [sourcefmu, dfspecfmu, sinkfmu]"

overloading FMUs_ex \<equiv> "FMUs :: FMI2COMP list"
begin
definition [simp]:
  "FMUs_ex \<equiv> [sourcefmu, dfspecfmu, sinkfmu]"
end

text {*
  It appears there exist two output variables variables in the D2.2 example,
  which are given anonymous identities through numbers 1 and 2. It further
  appears that variable 1 is ranging over naturals, and variable two over
  characters. For readability, where here call them @{text x} and @{text y}.
*}

inject_type nat
inject_type char

overloading outputs_ex \<equiv> "outputs :: (FMI2COMP \<times> VAR) list"
begin
definition [simp]:
  "outputs_ex \<equiv> [(sourcefmu, $x:{nat}\<^sub>u), (dfspecfmu, $y:{char}\<^sub>u)]"
end

abbreviation outputset :: "(FMI2COMP \<times> VAR) set" where
"outputset \<equiv> set outputs"

overloading pdg_ex \<equiv> "pdg :: (VAR \<times> (FMI2COMP \<times> VAR)) set"
begin
definition [simp]:
  "pdg_ex \<equiv>
    {($x:{nat}\<^sub>u, (sourcefmu, $x:{nat}\<^sub>u)),
     ($y:{char}\<^sub>u, (dfspecfmu, $y:{char}\<^sub>u))}"
end

text {* Does this need to be a constant of the model too? *}

consts canGetAndSetFMUState :: "FMI2COMP \<Rightarrow> bool"

overloading canGetAndSetFMUState_ex \<equiv>
  "canGetAndSetFMUState :: FMI2COMP \<Rightarrow> bool"
begin
definition [simp]: "canGetAndSetFMUState_ex \<equiv> (\<lambda>_::FMI2COMP. False)"
end

overloading parameters_ex \<equiv> "parameters :: (FMI2COMP \<times> VAR \<times> VAL) list"
begin
definition [simp]:
  "parameters_ex \<equiv> [
    (sourcefmu, $x:{nat}\<^sub>u, InjU (1::nat)),
    (dfspecfmu, $x:{char}\<^sub>u, InjU (CHR ''a'')),
    (sinkfmu, $y:{char}\<^sub>u, InjU (CHR ''b''))]"
end

text {* Cannot quite make sense of what is in the deliverable. *}

overloading inputs_ex \<equiv> "inputs :: (FMI2COMP \<times> VAR \<times> VAL) list"
begin
definition [simp]:
  "inputs_ex \<equiv> []::(FMI2COMP \<times> VAR \<times> VAL) list"
end

subsection {* Proof Experiments *}

term "setT!\<^sub>u(\<guillemotleft>0\<guillemotright>) \<rightarrow> SKIP"
term "InputCSP setT x"
term "\<lceil>''x''\<rceil>\<^sub>d"
term "(dvar_lens \<lceil>''x''\<rceil>\<^sub>d)"
term "\<lceil>''x''\<rceil>\<^sub>d\<up>"
term "InputCSP setT (\<lceil>''x''\<rceil>\<^sub>d\<up>)"
end