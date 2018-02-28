(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: fmi.thy                                                              *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 20 Sep 2017 *)

section {* FMI {\Circus} Model *}

theory fmi
imports "UTP-Toolkit.Positive" Time
  "UTP-Axm.utp_axm"
  "../theories/utp_circus"
begin recall_syntax

declare [[typedef_overloaded]]
declare [[quick_and_dirty]]

default_sort type

subsection {* Preliminaries *}

subsubsection {* Syntax Extensions *}

paragraph \<open>Application and update of HOL partial functions.\<close>

definition map_apply :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
"map_apply f = the o f"

adhoc_overloading uapply map_apply

definition map_upd :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"map_upd m x y = m(x \<mapsto> y)"

text \<open>The commented-out overloading causes parsing ambiguities.\<close>

adhoc_overloading (* uupd fun_upd and *) uupd map_upd

paragraph {* Positive Subtype *}

text \<open>Lifted coercion operator from @{typ "'a pos"} to @{typ "'a"}.\<close>

syntax "_uRep_pos" :: "('a pos, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<section>'(_')")

translations "_uRep_pos p" \<rightleftharpoons> "(CONST uop) (CONST Rep_pos) p"

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

text {* By default, the product type did not instantiate @{class vst}. *}

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

subsection {* FMI Types  *}

text {* In this section, we encode the various FMI types in HOL. *}

subsubsection {* \<open>TIME\<close> and \<open>NZTIME\<close> *}

text {*
  Our aim is to treat time abstractly in the FMI model via some arbitrary type
  @{typ "'\<tau>"} that must be a member of class @{class time}. We thus introduce
  additional syntax below to impose the respective sort constraint(s). We also
  require that time can be injected into deep variable stores. In particular,
  membership to @{class linordered_ab_group_add} ensures @{class continuum}
  closure under the @{typ "'a pos"} type.
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
  the additional property that they are distinct and partition the type.
*}

typedecl FMI2COMP

text {* Syntactic sugar for \<open>UNIV::FMI2COMP set\<close>. *}

abbreviation FMI2COMP :: "FMI2COMP set" where
"FMI2COMP \<equiv> UNIV"

text {*
  We require the type @{type FMI2COMP} to be finite and containing at least two
  elements. This is important so that we can later on instantiate it as members
  of @{class two} and @{class continuum} for injection into the deep variable
  model. We observe that FMI {\Circus} processes use state and local variables
  involving the type @{type FMI2COMP}. To avoid the need for axioms, locales
  could perhaps be used.
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
  could be used to encode a generic (monomorphic) state type able to encode
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
  either class @{class two} or @{class continuum} due to its abstract nature.
  The only solution is once again to encapsulate the instantiation axioms as
  global axiomatic properties of the @{type FMUSTATE} type. Likewise, it may
  be safer to use a @{command locale} instead of an @{command axiomatization}.
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
  The FMI types of \<open>VAR\<close> and \<open>VAL\<close> are equated with the unified variable and
  value types of the axiomatic value model. While we could have alternatively
  used deep variables here, an approach via axiomatic variables means that we
  are not restricted to the standard FMI types. An issue is thought that \<open>VAL\<close>
  itself is clearly not injectable. The ranked axiomatic model may provide a
  solution to this problem, but this is work in progress for now.
*}

type_synonym VAR = "uvar.uvar" ("VAR")
type_synonym VAL = "uval.uval" ("VAL")

text {* Translations for pretty-printing. *}

translations (type) "VAR" \<leftharpoondown> (type) "uvar.uvar"
translations (type) "VAL" \<leftharpoondown> (type) "uval.uval"

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
  fmi2Status (fmi2StatusOf: "FMI2ST") |
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
  types. Since events may be parametric, as with states there is an issue how
  to model events with different (HOL) types as a single unified type. A deep
  model may encode them as pairs consisting of a name \& type. Below, we adopt
  a shallow model that uses a datatype construction wrapped into a @{type sum}
  type as to make the datatype extensible. As an alternative, Simon mentioned
  \emph{prisms} as an analogue of lenses for sum types.
*}

subsubsection {* FMI API Channels *}

text {*
  We note that all constructor functions are of type @{type chan}. To obtain
  extensible event types, we introduce a prefixing (scoping) operator for each
  channel type that lifts the underlying datatype into a @{type sum} type with
  an open slot for later extension. Eventually, those prefix operators will be
  introduced automatically by the tool, namely through a custom @{text events}
  command for defining channel events (future work).
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

abbreviation "FMIAPI \<equiv>
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

type_synonym error = (* "ErrorFlag" *) "FMI2ST"

datatype ctrl_event =
  stepToComplete "unit" |
  stepAnalysed "unit" |
  stepComplete "unit" |
  endsimulation "unit" |
  error "error"

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

subsubsection {* FMI Process Type *}

type_synonym ('\<sigma>, '\<tau>, 'ext) fmi_action =
  "('\<sigma>, '\<tau> fmi_event + '\<tau> timer_event + ctrl_event + 'ext) action"

type_synonym ('\<tau>, 'ext) fmi_process = "(unit, '\<tau>, 'ext) fmi_action"

subsection {* FMI Ports *}

text {*
  For readability, we introduce a @{command type_synonym} for FMI ports. A port
  is encoded by a pair consisting of an FMI component (of type @{type FMI2COMP})
  and a variable (of type @{type VAR}). We do not distinguish input and output
  ports at the level of the encoding.
*}

type_synonym port = "FMI2COMP \<times> VAR" ("PORT")

text {* Shall we pretty-print the @{typ PORT} type too? *}

(* translations (type) "PORT" \<leftharpoondown> (type) "FMI2COMP \<times> VAR" *)

text \<open>Getter function to obtain the FMU and name of a port object.\<close>

abbreviation FMU :: "PORT \<Rightarrow> FMI2COMP" where
"FMU port \<equiv> (fst port)"

abbreviation name :: "PORT \<Rightarrow> VAR" where
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
  \<open>initialValues\<close> rather than using the \<open>inputs\<close> sequence to provide initial
  values for inputs. This also proves to be slightly more convenient in terms
  of the mechanised model. Further, I changed the type of the port dependency
  graph to bee a function rather than a relation, mapping each outputs to a
  list of connected inputs. The advantage of this is that it facilitates the
  definition of the @{text DistributeInputs} action since currently, iterated
  sequence e.g.~of actions is only define for lists but not for (finite) sets.
  Lastly, I included another relation \<open>idd\<close> to record the internal direct
  dependencies of the FMI system. Conceptually, it turns out that it is not
  the \<open>pdg\<close> that has to be acyclic but the union of the \<open>pdg\<close> and \<open>idd\<close> to
  guarantee the absence of algebraic loops.
*}

-- \<open>In D2.2d: \<open>inputs :: FMI2COMP \<times> VAR \<times> VAL\<close> and \<open>pdg :: PORT relation\<close>.\<close>

consts
  FMUs :: "FMI2COMP list"
  parameters :: "(FMI2COMP \<times> VAR \<times> VAL) list"
  initialValues :: "(PORT \<times> VAL) list"
  inputs :: "PORT list"
  outputs :: "PORT list"
  pdg :: "PORT \<Rightarrow> (PORT list)" -- \<open>Port Dependency Graph\<close>
  idd :: "PORT \<Rightarrow> (PORT list)" -- \<open>Internal Direct Dependencies\<close>

subsection {* Simulation Parameters *}

-- {* In line with the D2.2d example, I added these as global constants, too. *}

consts startTime :: "TIME('\<tau>)"
consts stopTimeDefined :: "bool"
consts stopTime :: "TIME('\<tau>)"

subsection {* FMI Processes *}

subsubsection {* \<open>Timer\<close> Process *}

alphabet '\<tau>::ctime timer_state =
  currentTime :: "TIME('\<tau>)"
  stepSize :: "NZTIME('\<tau>)"

type_synonym '\<tau> timer_action =
  "('\<tau> timer_state, '\<tau> timer_event) action"

definition
"process Timer(ct::TIME('\<tau>), hc::NZTIME('\<tau>), tN::TIME('\<tau>)) \<triangleq> begin
  state('\<tau> timer_state)
  Step = (
    (tm:setT?(t : \<guillemotleft>t \<le> tN\<guillemotright>) \<^bold>\<rightarrow> currentTime :=\<^sub>C \<guillemotleft>t\<guillemotright>) \<box>
    (tm:updateSS?(ss) \<^bold>\<rightarrow> stepSize :=\<^sub>C \<guillemotleft>ss\<guillemotright>) \<box>
    (tm:step!(&currentTime)!(&stepSize) \<^bold>\<rightarrow>
      currentTime :=\<^sub>C min\<^sub>u(&currentTime + \<section>(&stepSize), \<guillemotleft>tN\<guillemotright>)) \<box>
    (&currentTime =\<^sub>u \<guillemotleft>tN\<guillemotright>) &\<^sub>u tm:endc \<^bold>\<rightarrow> Stop) ;; Step
  \<bullet> (currentTime, stepSize) :=\<^sub>C (\<guillemotleft>ct\<guillemotright>, \<guillemotleft>hc\<guillemotright>) ;; Step
end"

text \<open>The same process definition using deep variables.\<close>

definition
"process DvarTimer(ct::TIME('\<tau>), hc::NZTIME('\<tau>), tN::TIME('\<tau>)) \<triangleq> begin
  state(vstore)
  Step = (
    (tm:setT?(t : \<guillemotleft>t \<le> tN\<guillemotright>) \<^bold>\<rightarrow> <currentTime> :=\<^sub>C \<guillemotleft>t\<guillemotright>) \<box>
    (tm:updateSS?(ss) \<^bold>\<rightarrow> <stepSize> :=\<^sub>C \<guillemotleft>ss\<guillemotright>) \<box>
    (tm:step!(&<currentTime>)!(&<stepSize>) \<^bold>\<rightarrow>
      <currentTime> :=\<^sub>C min\<^sub>u(&<currentTime> + \<section>(&<stepSize>), \<guillemotleft>tN\<guillemotright>)) \<box>
    (&<currentTime> =\<^sub>u \<guillemotleft>tN\<guillemotright>) &\<^sub>u tm:endc \<^bold>\<rightarrow> Stop) ;; Step
  \<bullet> (<currentTime>, <stepSize>) :=\<^sub>C (\<guillemotleft>ct\<guillemotright>, \<guillemotleft>hc\<guillemotright>) ;; Step
end"

(*<*)
(*
text \<open>The same process definition using axiomatic variables. FIX!\<close>

definition
"process AvarTimer(ct::TIME('\<tau>), hc::NZTIME('\<tau>), tN::TIME('\<tau>)) \<triangleq> begin
  state(ust_store)
  Step = (
    (tm:setT?(t : \<guillemotleft>t \<le> tN\<guillemotright>) \<^bold>\<rightarrow> {currentTime} :=\<^sub>C \<guillemotleft>t\<guillemotright>) \<box>
    (tm:updateSS?(ss) \<^bold>\<rightarrow> {stepSize} :=\<^sub>C \<guillemotleft>ss\<guillemotright>) \<box>
    (tm:step!(&{currentTime})!(&{stepSize}) \<^bold>\<rightarrow>
      {currentTime} :=\<^sub>C min\<^sub>u(&{currentTime} + \<section>(&{stepSize}), \<guillemotleft>tN\<guillemotright>)) \<box>
    (&{currentTime} =\<^sub>u \<guillemotleft>tN\<guillemotright>) &\<^sub>u tm:endc \<^bold>\<rightarrow> Stop) ;; Step
  \<bullet> ({currentTime}, {stepSize}) :=\<^sub>C (\<guillemotleft>ct\<guillemotright>, \<guillemotleft>hc\<guillemotright>) ;; Step
end"
*)
(*>*)

text \<open>Prove that @{const Timer} and @{const DvarTimer} do not diverge.\<close>

lemma "pre\<^sub>R(Timer(ct, hc, tN)) = true\<^sub>r"
apply (unfold Timer_def)
apply (rdes_calc)
apply (rel_simp)
done

lemma "pre\<^sub>R(DvarTimer(ct, hc, tN)) = true\<^sub>r"
apply (unfold DvarTimer_def)
apply (rdes_calc)
apply (rel_simp)
done

subsubsection {* \<open>Interaction\<close> Process *}

text \<open>
  We here use the type @{typ "PORT \<rightharpoonup> VAL"} for \<open>rinps\<close>, rather than the type
  @{typ "FMI2COMP \<rightharpoonup> (VAR \<rightharpoonup> VAL)"} as in Figure 4 of D2.2d. Simon developed a
  separate embedding of partial maps in theory @{theory Pfun}); it may be worth
  considering using it here too. Importantly, the state space also includes a
  store for local (deep) variables. I wonder if there is another solution for
  integrating deep variables into alphabets. We could have, of course, also
  encoded \<open>rinps\<close> as a deep variable, but this would then constrain its type
  to be a member of the classes @{class "continuum"} and @{class "two"}.
\<close>

alphabet ia_state =
  rinps :: "PORT \<rightharpoonup> VAL"
  ia_locals :: "vstore"

instantiation ia_state_ext :: (type) vst
begin
definition vstore_lens_ia_state_ext :: "vstore \<Longrightarrow> 'a ia_state_scheme" where
"\<V> = ia_locals"
instance
apply (intro_classes)
apply (simp add: vstore_lens_ia_state_ext_def)
done
end

definition
"process Interaction \<triangleq> begin
  state(ia_state)

  Instantiation = (;;\<^sub>C i : FMUs \<bullet>
    fmi:fmi2Instantiate.(\<guillemotleft>i\<guillemotright>)?(sc) \<^bold>\<rightarrow> Skip) and

  InstantiationMode =
    (;;\<^sub>C (i, x, v) : parameters \<bullet>
      fmi:fmi2Set!(\<guillemotleft>i\<guillemotright>)!(\<guillemotleft>x\<guillemotright>)!(\<guillemotleft>v\<guillemotright>)?(st) \<^bold>\<rightarrow> Skip) ;;
    (;;\<^sub>C i : FMUs \<bullet>
      fmi:fmi2SetUpExperiment!(\<guillemotleft>i\<guillemotright>)!(\<guillemotleft>startTime\<guillemotright>)
        !(\<guillemotleft>stopTimeDefined\<guillemotright>)!(\<guillemotleft>stopTime\<guillemotright>)?(st) \<^bold>\<rightarrow> Skip) ;;
    (;;\<^sub>C i : FMUs \<bullet>
      fmi:fmi2EnterInitializationMode.(\<guillemotleft>i\<guillemotright>)?(st) \<^bold>\<rightarrow> Skip) and

  InitializationMode =
    (;;\<^sub>C ((i, x), v) : initialValues \<bullet>
      fmi:fmi2Set!(\<guillemotleft>i\<guillemotright>)!(\<guillemotleft>x\<guillemotright>)!(\<guillemotleft>v\<guillemotright>)?(st) \<^bold>\<rightarrow> Skip) ;;
    (;;\<^sub>C i : FMUs \<bullet>
      fmi:fmi2ExitInitializationMode!(\<guillemotleft>i\<guillemotright>)?(st) \<^bold>\<rightarrow> Skip) and

  TakeOutputs = rinps :=\<^sub>C \<guillemotleft>empty\<guillemotright> ;;
    (;;\<^sub>C out : outputs \<bullet>
      fmi:fmi2Get.(\<guillemotleft>FMU out\<guillemotright>).(\<guillemotleft>name out\<guillemotright>)?(v)?(st) \<^bold>\<rightarrow>
        (;;\<^sub>C inp : pdg out \<bullet> rinps :=\<^sub>C &rinps(\<guillemotleft>inp\<guillemotright> \<mapsto> \<guillemotleft>v\<guillemotright>)\<^sub>u)) and

  DistributeInputs = (;;\<^sub>C inp : inputs \<bullet>
    fmi:fmi2Set.(\<guillemotleft>FMU inp\<guillemotright>).(\<guillemotleft>name inp\<guillemotright>)!(&rinps(\<guillemotleft>inp\<guillemotright>)\<^sub>a)?(st) \<^bold>\<rightarrow> Skip) and

  (* Review the function below, Casper hinted some possible issues. I recall
   * this has to do with the use of fmi2GetMaxStepSize(_). Such ought to be
   * called before the simulation step is performed via fmi2DoStep(_). Also,
   * master algorithms may want to enquire the maximum predicted step size of
   * all FMUs first, before performing any simulation steps. Lastly, it is
   * not part of the FMI 2.0 Standard, hence should be model it here at all? *)

  Step = (;;\<^sub>C i : [0..(length FMUs)] \<bullet>
    (if i = 0 then
      ctr:stepToComplete \<^bold>\<rightarrow>
        (fmi:fmi2DoStep.(\<guillemotleft>FMUs!0\<guillemotright>).(&<t>).(&<hc>)?(st) \<^bold>\<rightarrow> Skip)
    else if i < (length FMUs) then
      (\<mu>\<^sub>C X \<bullet>
        (fmi:fmi2GetBooleanStatusfmi2Terminated.(\<guillemotleft>FMUs!nat (i-1)\<guillemotright>)?(b)?(st) \<^bold>\<rightarrow> X) \<box>
        (fmi:fmi2GetMaxStepSize.(\<guillemotleft>FMUs!nat (i-1)\<guillemotright>)?(t)?(st) \<^bold>\<rightarrow> X)) \<box>
        (fmi:fmi2DoStep.(\<guillemotleft>FMUs!nat i\<guillemotright>).(&<t>).(&<hc>)?(st) \<^bold>\<rightarrow> Skip)
    else
      (\<mu>\<^sub>C X \<bullet>
        (fmi:fmi2GetBooleanStatusfmi2Terminated.(\<guillemotleft>FMUs!nat (i-1)\<guillemotright>)?(b)?(st) \<^bold>\<rightarrow> X) \<box>
        (fmi:fmi2GetMaxStepSize.(\<guillemotleft>FMUs!nat (i-1)\<guillemotright>)?(t)?(st) \<^bold>\<rightarrow> X)) \<box>
        (ctr:stepAnalysed \<^bold>\<rightarrow> Skip)))
    (* ;; NextStep *) and

  Terminated =
    (;;\<^sub>C i : FMUs \<bullet>
      fmi:fmi2Terminate.(\<guillemotleft>i\<guillemotright>)?(st) \<^bold>\<rightarrow> fmi:fmi2FreeInstance.(\<guillemotleft>i\<guillemotright>)?(st) \<^bold>\<rightarrow> Skip) ;;
    ctr:endsimulation \<^bold>\<rightarrow> Skip and

  slaveInitialized =
    (tm:endc \<^bold>\<rightarrow> Terminated) \<box>
    (tm:step?(t)?(hc) \<^bold>\<rightarrow> (
      (<t>, <hc>) :=\<^sub>C (\<guillemotleft>t::TIME('\<tau>)\<guillemotright>, \<guillemotleft>hc::NZTIME('\<tau>)\<guillemotright>));;
    TakeOutputs ;; DistributeInputs ;; Step) and

  (* I had to add the sequence ... ;; NextStep below to get around the issue of
   * mutual recursion in the original CSP model of the Interaction process. *)

  NextStep =
    (tm:updateSS?(d) \<^bold>\<rightarrow> NextStep) \<box>
    (tm:setT?(t) \<^bold>\<rightarrow> NextStep) \<box>
    (slaveInitialized ;; NextStep) \<box>
    (Terminated)

  \<bullet> Instantiation ;; InstantiationMode ;; InitializationMode ;; slaveInitialized ;; NextStep
end"

theorem "P Interaction"
apply (unfold Interaction_def)
apply (simp add: circus_syntax Let_def)
oops

lemma "pre\<^sub>R(Interaction) = true\<^sub>r"
apply (unfold Interaction_def)
apply (simp add: circus_syntax Let_def)
apply (rdes_calc)
oops

subsubsection {* End Simulation Process *}

definition
"process endSimulation \<triangleq> ctr:endsimulation \<^bold>\<rightarrow> Skip"

subsubsection {* \<open>FMUStatesManager\<close> Process *}

text {* Since we only have a single state component. *}

abbreviation fmu_state :: "FMUSTATE \<Longrightarrow> FMUSTATE" where
"fmu_state \<equiv> 1\<^sub>L"

definition
"process FMUStateManager(i::FMI2COMP) \<triangleq> begin
  state(FMUSTATE)

  AllowsGetsAndSets =
    (fmi:fmi2GetFMUState!(\<guillemotleft>i\<guillemotright>)?(s)?(st) \<^bold>\<rightarrow>
      (fmu_state :=\<^sub>C \<guillemotleft>s\<guillemotright>) ;; AllowsGetsAndSets) \<box>
    (fmi:fmi2SetFMUState!(\<guillemotleft>i\<guillemotright>)!(&fmu_state)?(st) \<^bold>\<rightarrow> AllowsGetsAndSets) and

  AllowAGet =
    (fmi:fmi2GetFMUState!(\<guillemotleft>i\<guillemotright>)?(s)?(st) \<^bold>\<rightarrow>
      (fmu_state :=\<^sub>C \<guillemotleft>s\<guillemotright>) ;; AllowsGetsAndSets)

  \<bullet> fmi:fmi2Instantiate!(\<guillemotleft>i\<guillemotright>)?(b) \<^bold>\<rightarrow> AllowAGet
end"

text \<open>The same process definition using deep variables.\<close>

definition
"process DVarFMUStateManager(i::FMI2COMP) \<triangleq> begin
  state(vstore)

  AllowsGetsAndSets =
    (fmi:fmi2GetFMUState!(\<guillemotleft>i\<guillemotright>)?(s)?(st) \<^bold>\<rightarrow>
      (<fmu_state> :=\<^sub>C \<guillemotleft>s\<guillemotright>) ;; AllowsGetsAndSets) \<box>
    (fmi:fmi2SetFMUState!(\<guillemotleft>i\<guillemotright>)!(&<fmu_state>)?(st) \<^bold>\<rightarrow> AllowsGetsAndSets) and

  AllowAGet =
    (fmi:fmi2GetFMUState!(\<guillemotleft>i\<guillemotright>)?(s)?(st) \<^bold>\<rightarrow>
      (<fmu_state> :=\<^sub>C \<guillemotleft>s\<guillemotright>) ;; AllowsGetsAndSets)

  \<bullet> fmi:fmi2Instantiate!(\<guillemotleft>i\<guillemotright>)?(b) \<^bold>\<rightarrow> AllowAGet
end"

text {* \todo{Write the same process using the axiomatic model.} *}

definition
"process FMUStatesManager \<triangleq>
  (||| i : FMUs \<bullet> FMUStateManager(i)) \<triangle> endSimulation"

subsubsection {* Error Handling *}

text {*
  The encoding of the \<open>ErrorMonitor\<close> is a bit more tricky due to the presence
  of mutual recursion and parametrised actions. Parameters of actions are dealt
  with through a state component \<open>st_arg\<close> to pass the argument. This works as
  all calls are tail recursive. Mutual recursion is dealt with by defining one
  of the mutually-recursive actions i.e.~\<open>StopError\<close> as a higher-order function
  \emph{outside} the scope of the process. Effectively, this mirrors expanding
  \<open>StopError\<close> within the process definition, turning the mutual recursion into
  a single-recursive action.
*}

hide_const (open) utp_rea_designs.st -- \<open>Conflicts with the use of \<open>st\<close> below.\<close>

text {* Since we only have a single state component. *}

abbreviation st_arg :: "error \<Longrightarrow> error" where
"st_arg \<equiv> 1\<^sub>L"

text {*
  To break the mutual recursion in the process definition, we encode the local
  action \<open>StopError\<close> as a higher-order action. State component @{const st_arg}
  is used to pass an argument back to the \<open>Monitor\<close> action.
*}

definition
"process StopError(Monitor, st, mst) \<triangleq>
  (let MonitorCall = (\<lambda>st. st_arg :=\<^sub>C \<guillemotleft>st\<guillemotright> ;; Monitor) in
    (\<guillemotleft>st = mst\<guillemotright> &\<^sub>u ctr:error!(\<guillemotleft>mst\<guillemotright>) \<^bold>\<rightarrow> MonitorCall(st)) \<box>
    (\<guillemotleft>st \<noteq> mst\<guillemotright> &\<^sub>u MonitorCall(st)))"

definition
"process ErrorMonitor(mst) \<triangleq> begin
  Monitor = (
    (fmi:fmi2Get?(i)?(n)?(v)?(st) \<^bold>\<rightarrow> StopError(Monitor, st, mst)) \<box>
    (fmi:fmi2Set?(i)?(n)?(v)?(st) \<^bold>\<rightarrow> StopError(Monitor, (fmi2StatusOf st), mst)) \<box>
    (fmi:fmi2GetFMUState?(i)?(s)?(st) \<^bold>\<rightarrow> StopError(Monitor, st, mst)) \<box>
    (fmi:fmi2SetFMUState?(i)?(s)?(st) \<^bold>\<rightarrow> StopError(Monitor, st, mst)) \<box>
    (fmi:fmi2SetUpExperiment?(i)?(t)?(b)?(hc)?(st) \<^bold>\<rightarrow> StopError(Monitor, st, mst)) \<box>
    (fmi:fmi2EnterInitializationMode?(i)?(st) \<^bold>\<rightarrow> StopError(Monitor, st, mst)) \<box>
    (fmi:fmi2ExitInitializationMode?(i)?(st) \<^bold>\<rightarrow> StopError(Monitor, st, mst)) \<box>
    (fmi:fmi2GetBooleanStatusfmi2Terminated?(i)?(b)?(st) \<^bold>\<rightarrow> StopError(Monitor, st, mst)) \<box>
    (fmi:fmi2DoStep?(i)?(t)?(hc)?(st) \<^bold>\<rightarrow> StopError(Monitor, (fmi2StatusOf st), mst)) \<box>
    (fmi:fmi2Terminate?(i)?(st) \<^bold>\<rightarrow> StopError(Monitor, st, mst)) \<box>
    (fmi:fmi2GetMaxStepSize?(i)?(t)?(st) \<^bold>\<rightarrow> StopError(Monitor, st, mst)) \<box>
    (fmi:fmi2Instantiate?(i)?(b) \<^bold>\<rightarrow>
      (if b then StopError(Monitor, fmi2OK, mst)
            else StopError(Monitor, fmi2Fatal, mst))) \<box>
    (fmi:fmi2FreeInstance?(i)?(st) \<^bold>\<rightarrow> StopError(Monitor, st, mst)))

  \<bullet> Monitor \<triangle> (ctr:endsimulation \<^bold>\<rightarrow> Skip)
end"

definition
"process ErrorHandler \<triangleq>
  ErrorMonitor(fmi2Error)
    \<lbrakk>(FMIAPI \<union> \<epsilon>(ctr:endsimulation))\<rbrakk>\<^sub>C
  ErrorMonitor(fmi2Fatal)"

definition
"process FatalError \<triangleq>
  ctr:error.(\<guillemotleft>fmi2Fatal\<guillemotright>) \<^bold>\<rightarrow> ctr:endsimulation \<^bold>\<rightarrow> Skip"

definition
"process ShutdownCreated(i) \<triangleq>
  (ctr:error.(\<guillemotleft>fmi2Error\<guillemotright>) \<^bold>\<rightarrow> fmi:fmi2FreeInstance.(\<guillemotleft>i\<guillemotright>)?(st) \<^bold>\<rightarrow> Skip) \<box>
  (fmi:fmi2FreeInstance.(\<guillemotleft>i\<guillemotright>)?(st) \<^bold>\<rightarrow> Skip)"

definition
"process Shutdown(i) \<triangleq>
  (fmi:fmi2Instantiate.(\<guillemotleft>i\<guillemotright>)?(b) \<^bold>\<rightarrow> ShutdownCreated(i) ;; ctr:endsimulation \<^bold>\<rightarrow> Skip) \<box>
  (ctr:error.(\<guillemotleft>fmi2Error\<guillemotright>) \<^bold>\<rightarrow> ctr:endsimulation \<^bold>\<rightarrow> Skip)"

definition
"process ErrorManagement \<triangleq>
  (|| i : FMUs \<bullet> [\<epsilon>(ctr:error) \<union> \<epsilon>(ctr:endsimulation)] Shutdown(i))"

definition
"process ErrorManager \<triangleq> FatalError \<box> ErrorManagement"

subsubsection {* Master Algorithm *}

-- {* \todo{Check why the below does not pretty-print correctly.} *}

definition
"process TimedInteraction(t0, hc, tN) \<triangleq>
  (Timer(t0, hc, tN) \<triangle> endSimulation
    \<lbrakk>(tm_events \<union> \<epsilon>(ctr:endsimulation))\<rbrakk>\<^sub>C Interaction) \\
  tm_events \<union> \<epsilon>(ctr:stepAnalysed) \<union> \<epsilon>(ctr:stepComplete)"

(* print_theorems *)

definition
"process MAlgorithm(t0, hc, tN) \<triangleq>
  (((TimedInteraction(t0, hc, tN)
    \<lbrakk>(\<epsilon>(ctr:endsimulation) \<union> \<epsilon>(fmi:fmi2Instantiate))\<rbrakk>\<^sub>C
      FMUStatesManager) \<triangle> ErrorManager)
    \<lbrakk>(FMIAPI \<union> \<epsilon>(ctr:endsimulation) \<union> \<epsilon>(ctr:error))\<rbrakk>\<^sub>C ErrorHandler)
  \\ \<epsilon>(ctr:error)"

subsection {* Concrete MAs *}

definition
"process NoStatesManager \<triangleq>
  (||| i : FMUs \<bullet> fmi:fmi2Instantiate!(\<guillemotleft>i\<guillemotright>)?(b) \<^bold>\<rightarrow> Stop) \<triangle> endSimulation"

theorem "FMUStatesManager \<sqsubseteq> NoStatesManager"
apply (simp add: FMUStatesManager_def NoStatesManager_def)
-- {* Need monotonicity of interrupt and iterated interleaving to continue. *}
oops

(*<*)
(*
subsection {* FMU Wrapping (TODO) *}

definition RUN :: "'\<epsilon> set \<Rightarrow> ('\<sigma>, '\<epsilon>) action" where
"RUN evts = undefined"

(* I think the problem below is that the state space of i_b includes the whole
   of the reactive alphabet whereas the guard operator only expects a predicate
   on the state variables... *)

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
(*>*)
end