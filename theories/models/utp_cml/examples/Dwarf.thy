(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: Dwarf.thy                                                            *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* CML Dwarf Signal Example *}

(*<*)
theory Dwarf
imports 
  "../utp_cml"
begin
(*>*)

subsubsection {* Dwarf Signal Types *}

text {* A \emph{Dwarf Signal} is a kind of railway signal which is
used at the side of track when space is limited. An illustration is
shown in Figure \ref{fig:dwarfsignal}. It has three lamps which are
displayed in different configurations to give instructions to train
drivers. The signal's three lamps are named L1--L3, as illustrated,
and different configurations of a signal can be written using set
notation, for instance this signal is in $\{L1, L2\}$ which means
\textbf{Stop}. We begin by setting up three abbreviations to represent
these three strings. *}

abbreviation "L1 \<equiv> ''L1''"
abbreviation "L2 \<equiv> ''L2''"
abbreviation "L3 \<equiv> ''L3''"

text {* Next we start to construct the basic types for the Dwarf
signal, including the \texttt{LampId}, an enumeration of the three
signal states, and \texttt{Signal} which a (finite) set of
\texttt{LampId}s.*}

abbreviation "LampId   \<equiv> \<parallel><L1> | <L2> | <L3>\<parallel>"
abbreviation "Signal   \<equiv> \<parallel>@set of @LampId\<parallel>"

text {* The signal has a total of four \emph{proper states} which are
the well-defined commands a signal can convey to a driver. When all
lamps are off (indicated by the empty set $\{\}$) the signal is in the
\textbf{Dark} state, which is a power saving mode for when the signal
is not in use. The three remaining proper states \textbf{Stop},
\textbf{Warning} and \textbf{Drive} are indicated by a combination of
two lamps and correspond to the positions of an old-style semaphore
signal. We define these possible values below: *}

definition "dark     \<equiv> +|{}|+"
definition "stop     \<equiv> +|{<L1>, <L2>}|+"
definition "warning  \<equiv> +|{<L1>, <L3>}|+"
definition "drive    \<equiv> +|{<L2>, <L3>}|+"

text {* We also add the definitional equations for these values to the
evaluation tactics, so that proofs can be performed about them: *}

declare dark_def [eval,evalp]
declare stop_def [eval,evalp]
declare warning_def [eval,evalp]
declare drive_def [eval,evalp]

text {* Next we set up the datatype for proper states. It consists of
a signal which is in one of the four states: \textbf{Dark},
\textbf{Stop}, \textbf{Warning} and \textbf{Drive}, specified through
an invariant. *}

abbreviation 
  "ProperState \<equiv> 
     \<parallel>@Signal inv ps == (^ps^ in @set {&dark, &stop, &warning, &drive})\<parallel>"

text {* Next we create a datatype to represent the state of the entire
Dwarf Signal, which we specify as a CML record. Setting up a record
type is currently a little complicated, though the CML tool
automatically generates them. First we create a new unit type to act
as the "tag" for this record so that it can be distinguished from
others. We create an instance of the tag class which proves its a unit
type and associates a string with it (the name of the type). *}

typedef DwarfType_Tag = "{True}" by auto
instantiation DwarfType_Tag :: tag
begin
definition "tagName_DwarfType_Tag (x::DwarfType_Tag) = ''DwarfType''"
instance 
  by (intro_classes, metis (full_types) Abs_DwarfType_Tag_cases singleton_iff)
end

text {* Next we create a collection of fields associated with the tag, and give each
        the position in record and its CML type. *}

abbreviation "lastproperstate_fld \<equiv> 
  MkField TYPE(DwarfType_Tag) #1 \<parallel>@ProperState\<parallel>"

abbreviation "desiredproperstate_fld \<equiv> 
  MkField TYPE(DwarfType_Tag) #2 \<parallel>@ProperState\<parallel>"

abbreviation "turnoff_fld \<equiv> 
  MkField TYPE(DwarfType_Tag) #3 \<parallel>@set of @LampId\<parallel>"

abbreviation "turnon_fld \<equiv> 
  MkField TYPE(DwarfType_Tag) #4 \<parallel>@set of @LampId\<parallel>"

abbreviation "laststate_fld \<equiv> 
  MkField TYPE(DwarfType_Tag) #5 \<parallel>@Signal\<parallel>"

abbreviation "currentstate_fld \<equiv> 
  MkField TYPE(DwarfType_Tag) #6 \<parallel>@Signal\<parallel>"

text {* Then we use these fields to create selector functions for the record, which
        can be used directly in UTP/CML predicates *}

abbreviation "lastproperstate \<equiv> SelectRec lastproperstate_fld"
abbreviation "desiredproperstate \<equiv> SelectRec desiredproperstate_fld"
abbreviation "turnoff \<equiv> SelectRec turnoff_fld"
abbreviation "turnon \<equiv> SelectRec turnon_fld"
abbreviation "laststate \<equiv> SelectRec laststate_fld"
abbreviation "currentstate \<equiv> SelectRec currentstate_fld"

text {* Finally we create the actual type by giving the list of fields and the associated
        invariant. We also create a record constructor, \texttt{mk\_DwarfType}. *}

definition 
  "DwarfType \<equiv> 
     \<parallel>[ lastproperstate_fld
      , desiredproperstate_fld
      , turnoff_fld
      , turnon_fld
      , laststate_fld
      , currentstate_fld] 
     inv d == ((^d^.currentstate setminus ^d^.turnoff) union ^d^.turnon 
               = ^d^.desiredproperstate)
              and 
              (^d^.turnon inter ^d^.turnoff = {})\<parallel>"

declare DwarfType_def [eval,evalp]

definition "mk_DwarfType \<equiv> MkRec DwarfType"

declare mk_DwarfType_def [eval,evalp]

(*<*)
lemma mkd: "|mk_DwarfType(&stop, &stop, {}, {}, &stop, &stop) hasType @DwarfType| = |true|"
  by (cml_tac)
(*>*)
 
subsubsection {* Safety Properties *}

text {* We specify the safety properties of the Dwarf signal. These
are specified by use of CML functions from the Dwarf Signal type to a
boolean. *}

definition 
  "NeverShowAll = 
    |lambda d @ ^d^.#1.currentstate <> {<L1>,<L2>,<L3>}|"

declare NeverShowAll_def [eval,evalp]

definition 
  "MaxOneLampChange = 
    |lambda d @ card ((^d^.#1.currentstate setminus ^d^.#1.laststate) 
                      union (^d^.#1.laststate setminus ^d^.#1.currentstate)) 
                      <= 1|"

declare MaxOneLampChange_def [eval,evalp]

definition
  "ForbidStopToDrive = 
     |lambda d @ (^d^.#1.lastproperstate = &stop) 
               => ^d^.#1.desiredproperstate <> &drive|"
  
declare ForbidStopToDrive_def [eval,evalp]

definition
  "DarkOnlyToStop = 
     |lambda d @ (^d^.#1.lastproperstate = &dark) 
               => ^d^.#1.desiredproperstate in @set {&dark,&stop}|" 
  
declare DarkOnlyToStop_def [eval,evalp]

definition
  "DarkOnlyFromStop = 
     |lambda d @ (^d^.#1.desiredproperstate = &dark) 
               => ^d^.#1.lastproperstate in @set {&dark,&stop}|"

declare DarkOnlyFromStop_def [eval,evalp]

definition 
  "DwarfSignal = \<parallel>@DwarfType inv d == NeverShowAll(^d^) 
                                   and MaxOneLampChange(^d^)
                                   and ForbidStopToDrive(^d^)
                                   and DarkOnlyToStop(^d^)
                                   and DarkOnlyFromStop(^d^)\<parallel>"

declare DwarfSignal_def [eval,evalp]

text {* To exemplify CML proof goals, we show that an initialised
state of the signal satisfies the safety invariants. *}

lemma NeverShowAll_Init:
  "|NeverShowAll(mk_DwarfType(&stop, &stop, {}, {}, &stop, &stop))| = |true|"
  by (cml_tac)

lemma MaxOneLampChange_Init:
  "|MaxOneLampChange(mk_DwarfType(&stop, &stop, {}, {}, &stop, &stop))| = |true|"
  by (cml_tac)

lemma ForbidStopToDrive_Init:
  "|ForbidStopToDrive(mk_DwarfType(&stop, &stop, {}, {}, &stop, &stop))| = |true|"
  by (cml_tac)

lemma DarkOnlyToStop_Init:
  "|DarkOnlyToStop(mk_DwarfType(&stop, &stop, {}, {}, &stop, &stop))| = |true|"
  by (cml_tac)

lemma DarkOnlyFromStop_Init:
  "|DarkOnlyFromStop(mk_DwarfType(&stop, &stop, {}, {}, &stop, &stop))| = |true|"
  by (cml_tac)

(*<*)
lemma sdty: "|mk_DwarfType(&stop, &stop, {}, {}, &stop, &stop) hasType @DwarfSignal| = |true|"
  by (cml_tac)
(*>*)

subsubsection {* Reactive Behaviour *}

text {* We first define the channels with to specify the interaction
of the Dwarf signal. Channels can carry data so they all take a CML
type to specify this. *}

definition "init = MkChanD ''init'' \<parallel>()\<parallel>"
definition "light = MkChanD ''light'' \<parallel>@LampId\<parallel>"
definition "extinguish = MkChanD ''extinguish'' \<parallel>@LampId\<parallel>"
definition "setPS = MkChanD ''setPS'' \<parallel>@ProperState\<parallel>"
definition "shine = MkChanD ''shine'' \<parallel>@Signal\<parallel>"

text {* The Dwarf Signal process defines a namespace to avoid clashes
with state variables, operations and actions in other processes. We
provide the namespace in Isabelle by way of an Isabelle locale. *}

locale DwarfProcess
begin

text {* The Dwarf Signal has a single state variable which gives 
        the state of the signal. *}

abbreviation "dw \<equiv> MkVarD ''dw'' DwarfType"

text {* We also specify the invariant of the Dwarf Signal as a UTP
design. *}

definition "DwarfInv \<equiv> 
  `\<lparr> $dw hasType @DwarfType \<rparr> \<turnstile> \<lparr> $dw\<acute> hasType @DwarfType \<rparr>`"

text {* Next we specify the operations for the Dwarf Signal process. *}

definition "Init = 
  `true \<turnstile> (dw := mk_DwarfType(&stop, &stop, {}, {}, &stop, &stop))`"

(*<*)
lemma UNREST_vexpr_empty [unrest]: 
  "UNREST_PEXPR vs vexpr_empty"
  by (simp add:UNREST_PEXPR_def vexpr_empty_def evalp)

lemma "DwarfInv \<sqsubseteq> Init"
  apply (unfold DwarfInv_def Init_def)
  apply (rule refine)
  prefer 6
  apply (rule AndP_refines_2)
  apply (rule RefineP_equal_right_trans)
  defer
  apply (rule sym)
  apply (rule AssignR_alt_def)
  apply (rule typing)
  apply (simp add:typing)
  apply (simp add:defined evalp)
  apply (simp add:closure MkVarD_def)
  prefer 6
  apply (rule AndP_refines_1)
  apply (rule refine)
  apply (subgoal_tac "|mk_DwarfType(&stop, &stop, {}, {}, &stop, &stop)| \<rhd>\<^sub>* dw\<acute>")
  apply (subgoal_tac "UNREST_PEXPR {def\<down>} |mk_DwarfType(&stop, &stop, {}, {}, &stop, &stop)|")
  apply (simp add:usubst typing defined closure unrest)
  apply (simp add:mkd)
  apply (utp_pred_tac)
  apply (rule unrest)
  apply (rule unrest)
  apply (rule unrest)
  apply (rule unrest)
  apply (rule unrest)
  apply (rule unrest)
  apply (rule unrest)
  apply (rule unrest)
  apply (rule unrest)
  apply (rule unrest)
  apply (rule unrest)
oops
(*>*)

definition 
  "SetNewProperState st = 
      `\<lparr>($dw).currentstate = ($dw).desiredproperstate 
        and ^st^ <> ($dw).currentstate\<rparr> 
       \<turnstile> dw := mk_DwarfType( ($dw).currentstate
                           , ($dw).currentstate setminus ^st^
                           , ^st^ setminus ($dw).currentstate
                           , ($dw).laststate
                           , ($dw).currentstate
                           , ^st^)`"

definition
  "TurnOn l =
     `\<lparr> ^l^ in @set ($dw).turnon \<rparr> 
      \<turnstile> dw := mk_DwarfType( ($dw).lastproperstate
                          , ($dw).turnoff setminus {^l^}
                          , ($dw).turnon setminus {^l^}
                          , ($dw).currentstate
                          , ($dw).currentstate union {^l^}
                          , ($dw).desiredproperstate)`"

definition
  "TurnOff l =
     `\<lparr> ^l^ in @set ($dw).turnoff \<rparr> 
      \<turnstile> dw := mk_DwarfType( ($dw).lastproperstate
                          , ($dw).turnoff setminus {^l^}
                          , ($dw).turnon setminus {^l^}
                          , ($dw).currentstate
                          , ($dw).currentstate setminus {^l^}
                          , ($dw).desiredproperstate)`"


text {* Actions *}

definition 
  "DWARF = `\<mu> DWARF. 
          (((light?(l) -> TurnOn(&l)) ; DWARF) 
       [] ((extinguish?(l) -> TurnOff(&l)); DWARF)
       [] ((setPS?(s) -> SetNewProperState(&s)); DWARF)
       [] (shine!(($dw).currentstate) -> DWARF))`"

text {* Working test *}
definition
  "TEST1 = `setPS!&warning -> extinguish!<L2> -> light!<L3> 
           -> setPS!&drive -> extinguish!<L1> -> light!<L2> -> STOP`"

text {* Tries to turn on 3 lights simulaneously *}
definition
  "TEST2 = `setPS!&warning -> light!<L3> -> extinguish!<L2> 
           -> setPS!&drive -> extinguish!<L1> -> light!<L2> -> STOP`"

text {* Tries to go from dark to warning *}
definition
  "TEST3 = `setPS!&dark -> extinguish!<L1> -> extinguish!<L2> -> setPS!&warning -> 
            light!<L1> -> light!<L2> -> STOP`"

text {* Tries to go from stop to drive *}
definition
  "TEST4 = `setPS!&drive -> extinguish!<L1> -> light!<L3> -> STOP`"

definition "DWARF_TEST1 = `DWARF [|{setPS\<down>,light\<down>,extinguish\<down>}|] TEST1`"
definition "DWARF_TEST2 = `DWARF [|{setPS\<down>,light\<down>,extinguish\<down>}|] TEST2`"
definition "DWARF_TEST3 = `DWARF [|{setPS\<down>,light\<down>,extinguish\<down>}|] TEST3`"
definition "DWARF_TEST4 = `DWARF [|{setPS\<down>,light\<down>,extinguish\<down>}|] TEST4`"

text {* The main action of the process. *}
definition 
  "MainAction = DWARF"

end

end