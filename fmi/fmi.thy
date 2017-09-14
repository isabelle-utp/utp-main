(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: fmi.thy                                                              *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: TODO *)

section {* FMI {\Circus} Model *}

theory fmi
imports Positive_New Time
  "../utp/models/utp_axm"
  "../theories/utp_circus"
  "../theories/utp_circus_prefix"
begin recall_syntax

subsection {* Configuration Options *}

declare [[typedef_overloaded]]
declare [[quick_and_dirty]]
declare [[syntax_ambiguity_warning=false]]

default_sort type

subsection {* Adjustments *}

text {* TODO: Let the recall package hide types too! *}

hide_type (open) Relation.rel

type_synonym 'a hol_rel = "('a \<times> 'a) set"

text {* The below cause ambiguities wrt their CSP definitions. *}

hide_const utp_cml.Skip
hide_const utp_cml.Stop

text {* The following adjustment is moreover required... *}

syntax
  "_csp_sync" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow>\<^sub>u _" [81, 80] 80)

text {* Undeclaring Simon's notation for for prefixes. *}

purge_syntax
  "_output_prefix" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" ("!'(_')")
  "_output_prefix" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" (".'(_')")

subsection {* Preliminaries *}

subsubsection {* Class Instantiations *}

lemma card_gt_two_witness:
"finite S \<Longrightarrow> 2 \<le> card S \<Longrightarrow> (\<exists>a\<in>S. \<exists>b\<in>S. a \<noteq> b)"
apply (atomize (full))
apply (rule impI)
apply (erule finite.induct)
-- {* Subgoal 1 *}
apply (simp)
-- {* Subgoal 2 *}
apply (clarify)
apply (case_tac "a \<in> A")
-- {* Subgoal 2.1 *}
apply (simp add: insert_absorb)
-- {* Subgoal 2.2 *}
apply (rule_tac x = "a" in bexI)
apply (clarsimp)
using card_le_Suc_iff apply (blast)
apply (simp)
done

theorem card_ge_two_unfold:
"finite S \<Longrightarrow> 2 \<le> card S = (\<exists>x y. x \<in> S \<and> y \<in> S \<and> x \<noteq> y)"
apply (rule iffI)
-- {* Subgoal 1 *}
using card_gt_two_witness apply (blast)
-- {* Subgoal 2 *}
apply (case_tac "card S = 0")
apply (clarsimp)
apply (case_tac "card S = 1")
apply (clarsimp)
using card_eq_SucD apply (blast)
apply (clarsimp)
apply (meson card_eq_0_iff less_2_cases not_less)
done

theorem instance_twoI:
"\<exists>x y. x \<in> S \<and> y \<in> S \<and> x \<noteq> y \<Longrightarrow> \<not> finite S \<or> 2 \<le> card S"
apply (case_tac "finite S")
apply (simp_all)
apply (subst card_ge_two_unfold)
apply (assumption)
apply (clarsimp)
done

text {* By default, the product type did not instantiate class @{class two}. *}

instance prod :: (two, two) two
apply (intro_classes)
apply (rule instance_twoI)
apply (subgoal_tac "\<exists>(a::'a) (b::'a). a \<noteq> b")
apply (subgoal_tac "\<exists>(c::'b) (d::'b). c \<noteq> d")
apply (clarsimp)
apply (rule two_diff)
apply (rule two_diff)
done

text {* By default, the product type did not instantiate class @{class vst}. *}

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

subsubsection {* Lists as Tables *}

type_synonym ('a, 'b) table = "('a \<times> 'b) list"

fun lookup :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b" where
"lookup ((x, y) # t) v = (if v = x then y else (lookup t x))" |
"lookup [] x = undefined"

syntax "_ulookup" ::
  "('a \<times> 'b, '\<sigma>) uexpr \<Rightarrow> ('a, '\<sigma>) uexpr \<Rightarrow> ('b, '\<sigma>) uexpr" ("lookup\<^sub>u")

translations "lookup\<^sub>u t x" \<rightleftharpoons> "(CONST bop) (CONST lookup) t x"

subsubsection {* Positive Subtype *}

text {* \todo{Move the following to the theory @{theory utp_expr}.} *}

syntax "_uRep_pos" :: "('a pos, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<section>'(_')")

translations "_uRep_pos p" \<rightleftharpoons> "(CONST uop) (CONST Rep_pos) p"

subsection {* FMI Types  *}

text {* In this section, we encode the various FMI types in HOL. *}

subsubsection {* \<open>TIME\<close> and \<open>NZTIME\<close> *}

text {*
  Our aim is to treat time abstractly in the FMI model via some arbitrary type
  @{typ "'\<tau>"} that is a member of class @{class time}. We thus introduce some
  additional syntax below to facilitate obtaining the value universe of a time
  domain provided by way of the type @{typ "'\<tau>"}. It is just a syntactic sugar
  allowing us to write \<open>TIME('\<tau>)\<close> and \<open>NZTIME('\<tau>)\<close> while imposing the necessary
  sort constraints on the free type @{typ "'\<tau>"}.
*}

class ctime = time + linordered_ab_group_add + continuum + two (* + injectable *)

syntax   "_TIME" :: "type \<Rightarrow> type" ("TIME'(_')")
syntax "_NZTIME" :: "type \<Rightarrow> type" ("NZTIME'(_')")

translations (type) "TIME('\<tau>)" \<rightleftharpoons> (type) "'\<tau>::ctime"
translations (type) "NZTIME('\<tau>)" \<rightleftharpoons> (type) "'\<tau>::ctime pos"

subsubsection {* \<open>FMI2COMP\<close> *}

text {*
  The type @{text FMI2COMP} of FMI component identifiers is introduced as a
  given (deferred) type. Concrete co-simulation models have to introduced an
  axiomatisation in order to determine the elements of this type, along with
  the additional property that they are distinct.
*}

typedecl FMI2COMP

text {* Syntactic sugar for \<open>UNIV::FMI2COMP set\<close>. *}

abbreviation FMI2COMP :: "FMI2COMP set" where
"FMI2COMP \<equiv> UNIV"

text {*
  We require the type @{type FMI2COMP} to be finite and containing at least two
  elements. This is important so that we can later on instantiate it as members
  of @{class two} and @{class continuum} for injection into the deep value model
  as the FMI processes use state variables involving the type @{type FMI2COMP}.
*}

axiomatization where
  FMI2COMP_finite: "finite FMI2COMP" and
  FMI2COMP_gt_two: "card FMI2COMP \<ge> 2"

text {* Instantiation of relevant classes for the axiomatic value model. *}

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

text {* Injection into the axiomatic value model. *}

inject_type FMI2COMP

text {* The below facilitates evaluation of the transitive closure of PDGs. *}

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

text {* Instantiation of relevant classes for the deep value model. *}

instance FMI2COMP :: finite
apply (intro_classes)
apply (rule FMI2COMP_finite)
done

-- {* The above already guarantees membership to class @{class continuum}. *}

instance FMI2COMP :: "{continuum, two}"
apply (intro_classes)
apply (rule disjI2)
apply (rule FMI2COMP_gt_two)
done

subsubsection {* \<open>FMUSTATE\<close> *}

text {*
  Likewise, @{text FMUSTATE} is introduced as a given type for now. We may
  need to review this in the future; for instance, the universal value model
  could be used to encode a generic (monomorphic) state type that can encode
  the state of any concrete FMU.
*}

typedecl FMUSTATE

text {* Instantiation of relevant classes for the axiomatic value model. *}

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

text {* Injection into the axiomatic value model. *}

inject_type FMUSTATE

text {* Instantiation of relevant classes for the deep value model. *}

text {*
  Clearly, it is not possible to prove that @{type FMUSTATE} is an instance of
  either class @{class two} or @{class continuum}. Once again, the only thing
  we can do is to encapsulate the axioms of those lasses as global axioms of
  the deferred @{type FMUSTATE} type.
*}

axiomatization where
   FMUSTATE_continuum: "OFCLASS(FMUSTATE, continuum_class)" and
   FMUSTATE_two:       "OFCLASS(FMUSTATE, two_class)"

text {* The instantiation below is proved by virtue of the axioms above. *}

instance FMUSTATE :: "{continuum, two}"
apply (rule FMUSTATE_continuum)
apply (rule FMUSTATE_two)
done

subsubsection {* \<open>VAR\<close> and \<open>VAL\<close> *}

text {* Type synonyms for permissible FMI 2.0 port types. *}

type_synonym fmi2Real = "real"
type_synonym fmi2Integer = "int"
type_synonym fmi2String = "string"
type_synonym fmi2Boolean = "bool"

text {*
  The FMI types of @{text VAR} and @{text VAL} are equated with the unified
  variable and value types of the axiomatic value model. While we could have
  alternatively used deep variables here, an approach via axiomatic variables
  implies that there are no restrictions on modelling FMI types. An issue is
  that @{text VAL} is clearly not injectable, at least in the original model.
  The ranked axiomatic model, however, solves that problem.
*}

type_synonym VAR = "uvar.uvar" ("VAR")
type_synonym VAL = "uval.uval" ("VAL")

text {*
  The below is clearly not tru, namely the type @{typ uval} of the axiomatic
  model might have a higher cardinality than the continuum, depending on what
  HOL types we inject. To solve this issue, either fully integrate axiomatic
  variables into {\Circus} processes or otherwise resort to using shallow or
  deep variables in the state of the \<open>Interaction\<close> process. Strictly speaking,
  axiomatic values are probably not needed since the only types that FMI 2.0
  allows to be exchanged between FMUs are Real, Integer, String and Boolean,
  all of which can be injected into the deep value model too. We may hence
  define a union type (datatype) that aggregates those four types. [TODO]
*}

instance uval     ::        "{continuum, two}" sorry
instance uvar_ext :: (type) "{continuum, two}" sorry

subsubsection {* \<open>FMIST\<close> and \<open>FMISTF\<close> *}

text {* We declare a datatype for \<open>fmi2Status\<close> flags the FMI API. *}

datatype FMI2ST =
  fmi2OK |
  fmi2Error |
  fmi2Fatal
  (*fmi2Warning *)
  (*fmi2Penidng *)

text {* Instantiation of relevant classes for the axiomatic value model. *}

inject_type FMI2ST

text {* Instantiation of relevant classes for the deep value model. *}

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

subsubsection {* \<open>FMUSTF\<close> *}

datatype FMI2STF =
  fmi2Status "FMI2ST" |
  fmi2Discard

text {* Instantiation of relevant classes for the axiomatic value model. *}

inject_type FMI2STF

text {* Instantiation of relevant classes for the deep value model. *}

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

subsubsection {* Error Flags *}

typedef ErrorFlag = "{fmi2Error, fmi2Fatal}"
apply (rule_tac x = "fmi2Error" in exI)
apply (clarsimp)
done

text {* Instantiation of relevant classes for the axiomatic value model. *}

inject_type ErrorFlag

text {* Instantiation of relevant classes for the deep value model. *}

text {* We note that countability implies membership to @{class continuum} *}

instance ErrorFlag :: countable
apply (intro_classes)
apply (rule_tac x = "to_nat o Rep_ErrorFlag" in exI)
apply (rule inj_comp)
-- {* Subgoal 1 *}
apply (simp)
-- {* Subgoal 2 *}
apply (rule inj_onI; clarsimp)
apply (simp add: Rep_ErrorFlag_inject)
done

instance ErrorFlag :: continuum
apply (intro_classes)
done

instance ErrorFlag :: two
apply (intro_classes)
apply (rule instance_twoI)
apply (rule_tac x = "Abs_ErrorFlag fmi2Error" in exI)
apply (rule_tac x = "Abs_ErrorFlag fmi2Fatal" in exI)
apply (simp add: Abs_ErrorFlag_inject)
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
  still an open issue how we conveniently support compositional declarations of
  new channels; Simon mentioned \emph{prisms} as an analogue of lenses for sum
  types. A working but somewhat \textit{ad hoc} solution is presented below.
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

subsubsection {* Timer Channels *}

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

subsubsection {* Control Channels *}

datatype ctrl_event =
  stepToComplete "unit" |
  stepAnalysed "unit" |
  stepComplete "unit" |
  endsimulation "unit" |
  error (* "ErrorFlags" *) "FMI2ST"

abbreviation ctrl_prefix ::
  "('a, ctrl_event) chan \<Rightarrow>
   ('a, ('\<tau>::ctime fmi_event) + ('\<tau>::ctime timer_event) + (ctrl_event) + 'ext) chan" where
"ctrl_prefix c \<equiv> Inr o Inr o Inl o c"

notation ctrl_prefix ("ctr:_" [1000] 1000)

abbreviation "ctrl_events \<equiv>
  \<epsilon>(ctr:stepToComplete) \<union>
  \<epsilon>(ctr:stepAnalysed) \<union>
  \<epsilon>(ctr:stepComplete) \<union>
  \<epsilon>(ctr:endsimulation) \<union>
  \<epsilon>(ctr:error)"

subsection {* FMI Ports *}

text {*
  For readability, we introduce a @{command type_synonym} for ports. A port is
  encoded by a pair consisting of an FMI component (of type @{type FMI2COMP})
  and a variable (of type @{type VAR}). We do not distinguish input and output
  ports at the level of the encoding.
*}

type_synonym port = "FMI2COMP \<times> VAR"

text \<open>Getter function to obtain the FMU and name of a port.\<close>

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
  specified already here (e.g.~acyclicity  of the port dependency graph). This
  could possibly be done through a type definition. We note that we encode the
  Z type @{text "seq"} by HOL's list type @{typ "'a list"}.
*}

text {*
  In line with the CSP model of Deliverable D2.2d, I added a separate list
  @{term initialValues} rather than using the \<open>inputs\<close> sequence to provide
  initial values for inputs. This also proves to be slightly more convenient
  in terms of mechanisation. Also, I changed the type of the port-dependency
  graph to become a function rather than a relation, mapping each outputs to
  a list of connected inputs. The advantage of this is that it facilitates the
  definition of the @{text DistributeInputs} action since currently, iterated
  sequence of actions is only define over lists but not for (finite) sets.
  Lastly, I included another relation \<open>idd\<close> to record the internal direct
  dependencies of the FMI system. Conceptually, it turns out that it is not
  the \<open>pdg\<close> that has to be acyclic but the union of the \<open>pdg\<close> and \<open>idd\<close>.
*}

-- {* In D2.2d: \<open>inputs :: FMI2COMP \<times> VAR \<times> VAL\<close> and \<open>pdg :: port relation\<close>. *}

consts
  FMUs :: "FMI2COMP list"
  parameters :: "(FMI2COMP \<times> VAR \<times> VAL) list"
  initialValues :: "(FMI2COMP \<times> VAR \<times> VAL) list"
  inputs :: "port list"
  outputs :: "port list"
  pdg :: "port \<Rightarrow> (port list)" -- \<open>Port Dependency Graph\<close>
  idd :: "port \<Rightarrow> (port list)" -- \<open>Internal Direct Dependencies\<close>

subsection {* Simulation Parameters *}

text {* As per the example in D2.2d, I added these as global constants too. *}

consts startTime :: "TIME('\<tau>)"
consts stopTimeDefined :: "bool"
consts stopTime :: "TIME('\<tau>)"

(***********************)
(* REVIEWED UNTIL HERE *)
(***********************)

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
    (tm:step![out]((&<currentTime>, &<stepSize>)\<^sub>u) \<rightarrow>\<^sub>\<C>
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
    (tm:step![out\<^sub>1]($<currentTime>)![out\<^sub>2]($<stepSize>) \<rightarrow>\<^sub>\<C>
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

subsubsection {* States Manager *}

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

subsubsection {* FMU Wrapping *}

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