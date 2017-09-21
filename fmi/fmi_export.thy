(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: fmi_export.thy                                                       *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 18 Sep 2017 *)

section {* FMI {\Circus} Model *}

theory fmi_export
imports fmi
  "../theories/utp_circus_prefix"
begin recall_syntax

declare [[syntax_ambiguity_warning = false]]

subsection {* Preliminaries *}

text {* The below cause ambiguities wrt their CSP definitions. *}

hide_const utp_cml.Skip
hide_const utp_cml.Stop

(*
text {* I believe the following adjustments are not required anymore. *}

syntax
  "_csp_sync" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow>\<^sub>u _" [81, 80] 80)
*)

text {* Undeclaring Simon's prefix notation (need to parse \<open>Interaction\<close>. *}

purge_syntax
  "_output_prefix" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" ("!'(_')")
  "_output_prefix" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" (".'(_')")

subsection {* Lists as Tables *}

type_synonym ('a, 'b) table = "('a \<times> 'b) list"

fun lookup :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b" where
"lookup ((x, y) # t) v = (if v = x then y else (lookup t x))" |
"lookup [] x = undefined"

syntax "_ulookup" ::
  "('a \<times> 'b, '\<sigma>) uexpr \<Rightarrow> ('a, '\<sigma>) uexpr \<Rightarrow> ('b, '\<sigma>) uexpr" ("lookup\<^sub>u")

translations "lookup\<^sub>u t x" \<rightleftharpoons> "(CONST bop) (CONST lookup) t x"

subsection {* Instantiations *}

text {*
  The instantiations below are unsafe since the type @{typ uval} may actually
  have a higher cardinality than the continuum, depending on what HOL types we
  inject into it! This is why I decided to adopt a shallow state model for the
  \<open>Interaction\<close> process. (An alternative would be to adopt an axiomatic model,
  which requires some remaining more work on integrating axiomatic variables.)
  Strictly speaking, axiomatic values are probably not needed since the only
  types that FMI 2.0 allows to be exchanged between FMUs are Real, Integer,
  String and Boolean, all of which can be injected into the deep model, too.
*}

instance uval     ::        "{continuum, two}" sorry
instance uvar_ext :: (type) "{continuum, two}" sorry

subsection {* {\Circus} Constructs *}

syntax "_if_then_else" ::
  "'a upred \<Rightarrow> ('a, 'b) rel \<Rightarrow> ('a, 'b) rel \<Rightarrow> ('a, 'b) rel"
    ("(if\<^sub>\<C> (_)/ then\<^sub>\<C> (_)/ else\<^sub>\<C> (_))" [0, 0, 10] 10)

translations "if\<^sub>\<C> b then\<^sub>\<C> P else\<^sub>\<C> Q" \<rightleftharpoons> "P \<triangleleft> b \<triangleright>\<^sub>r Q"

subsection {* \<open>Timer\<close> Process *}

text {*
  A problem with the {\Circus} process encoding below is that, currently, it
  is not possible to write mixed prefixes with both inputs and outputs. Hence,
  I had to use a trick converting everything into a single input prefix. That
  input imposes constraints so that some parts of the communication effectively
  behave like outputs. A second issue is that, referring to page 16 of D2.2d,
  we see that the @{text AllowGetsAndSets} action is actually parametric. My
  translation currently does not support parametric actions; hence I adopted
  a solution that encodes procedure parameters by local variables. Due to the
  proper treatment of scope by Isabelle/UTP, we generally get away with this.
  Both issues can thus be overcome; an integration of syntax translations that
  conceal the manual adjustments done below is pending work.
*}

text {* \todo{Write the same process as below with axiomatic variables.} *}

definition
"process TimerOld1(ct::TIME('\<tau>), hc::NZTIME('\<tau>), tN::TIME('\<tau>)) \<triangleq> begin
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
"process TimerOld2(ct::TIME('\<tau>), hc::NZTIME('\<tau>), tN::TIME('\<tau>)) \<triangleq> begin
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

subsubsection {* \<open>Interaction\<close> Process *}

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

text {* Process State: \<open>rinps :: (port \<times> VAL) list\<close>. *}

definition
"process InteractionOld \<triangleq> begin
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

theorem "P InteractionOld"
apply (unfold InteractionOld_def)
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

subsubsection {* \<open>FMUStatesManager\<close> Process *}

definition
"process FMUStatesManagerOld1(i::FMI2COMP) \<triangleq> begin
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
"process FMUStatesManagerOld2(i::FMI2COMP) \<triangleq> begin
  state(vstore)
  AllowsGetsAndSets =
    (fmi:fmi2GetFMUState![out](\<guillemotleft>i\<guillemotright>)?(s)?(st) \<rightarrow>\<^sub>\<C> (<s> := \<guillemotleft>s\<guillemotright>) ;; AllowsGetsAndSets) \<box>
    (fmi:fmi2SetFMUState![out\<^sub>1](\<guillemotleft>i\<guillemotright>)![out\<^sub>2](&<s>) \<rightarrow>\<^sub>\<C> AllowsGetsAndSets) and
  AllowAGet =
    (fmi:fmi2GetFMUState![out](\<guillemotleft>i\<guillemotright>)?(s)?(st) \<rightarrow>\<^sub>\<C> (<s> := \<guillemotleft>s\<guillemotright>) ;; AllowsGetsAndSets)
  \<bullet> fmi:fmi2Instantiate![out](\<guillemotleft>i\<guillemotright>)?(b) \<rightarrow>\<^sub>\<C> AllowAGet
end"

subsection {* Proof Experiments *}

term "setT!\<^sub>u(\<guillemotleft>0\<guillemotright>) \<rightarrow> SKIP"
term "InputCSP setT x"
term "\<lceil>''x''\<rceil>\<^sub>d"
term "(dvar_lens \<lceil>''x''\<rceil>\<^sub>d)"
term "\<lceil>''x''\<rceil>\<^sub>d\<up>"
term "InputCircus setT (\<lceil>''x''\<rceil>\<^sub>d\<up>)"
end