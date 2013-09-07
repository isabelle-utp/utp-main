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
     \<parallel>@Signal 
      inv ps == (&ps in @set {&dark, &stop, &warning, &drive})\<parallel>"

text {* We then create a datatype to represent the state of the entire
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
  by ( intro_classes
     , metis (full_types) Abs_DwarfType_Tag_cases singleton_iff)
end

text {* Next we create a collection of fields associated with the
        tag. The @{term MkField} function constructs a record field
        from a record tag, position in the field and a CML type. There
        are six fields in \texttt{DwarfType}. *}

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
        can be used directly in UTP/CML predicates. *}

abbreviation "lastproperstate \<equiv> SelectRec lastproperstate_fld"
abbreviation "desiredproperstate\<equiv> SelectRec desiredproperstate_fld"
abbreviation "turnoff \<equiv> SelectRec turnoff_fld"
abbreviation "turnon \<equiv> SelectRec turnon_fld"
abbreviation "laststate \<equiv> SelectRec laststate_fld"
abbreviation "currentstate \<equiv> SelectRec currentstate_fld"

text {* Finally we create the actual type by giving the list of fields
        and the associated invariant. We also create a record
        constructor, \texttt{mk\_DwarfType}. *}

definition 
  "DwarfType \<equiv> 
     \<parallel>[ lastproperstate_fld
      , desiredproperstate_fld
      , turnoff_fld
      , turnon_fld
      , laststate_fld
      , currentstate_fld] 
     inv d == ((^d^.currentstate setminus ^d^.turnoff) 
                  union ^d^.turnon 
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
boolean. There are five proper states. The first property ensure that
all three lights are never enabled simulaneously. *}

definition 
  "NeverShowAll = 
    |lambda d @ ^d^.#1.currentstate <> {<L1>,<L2>,<L3>}|"

declare NeverShowAll_def [eval,evalp]

text {* The second ensure that only one lamp can change in any given
transition, either from lit to dark \emph{or} dark to lit. *}

definition 
  "MaxOneLampChange = 
  |lambda d @ card ((^d^.#1.currentstate setminus ^d^.#1.laststate)
                    union 
                    (^d^.#1.laststate setminus ^d^.#1.currentstate)) 
                    <= 1|"

declare MaxOneLampChange_def [eval,evalp]

text {* The third ensures that the signal cannot transition directly
from the stop state the drive state -- it must transition via the
\textsf{warning} state. *}

definition
  "ForbidStopToDrive = 
     |lambda d @ (^d^.#1.lastproperstate = &stop) 
               => ^d^.#1.desiredproperstate <> &drive|"
  
declare ForbidStopToDrive_def [eval,evalp]

text {* The fourth ensures that the signal can only transition from
\textsf{dark} to \textsf{stop} -- it cannot transition directly to any
other proper state. *}

definition
  "DarkOnlyToStop = 
     |lambda d @ (^d^.#1.lastproperstate = &dark) 
               => ^d^.#1.desiredproperstate in @set {&dark,&stop}|" 
  
declare DarkOnlyToStop_def [eval,evalp]

text {* The fifth and final property ensures that the previous proper
state before \textsf{dark} can only be \textsf{stop}. *}

definition
  "DarkOnlyFromStop = 
     |lambda d @ (^d^.#1.desiredproperstate = &dark) 
               => ^d^.#1.lastproperstate in @set {&dark,&stop}|"

declare DarkOnlyFromStop_def [eval,evalp]

text {* We then create the \texttt{DwarfSignal} type to the subset of
\texttt{DwarfType} where all the safety properties are true. *}

definition 
  "DwarfSignal = \<parallel>@DwarfType inv d == NeverShowAll(^d^) 
                                   and MaxOneLampChange(^d^)
                                   and ForbidStopToDrive(^d^)
                                   and DarkOnlyToStop(^d^)
                                   and DarkOnlyFromStop(^d^)\<parallel>"

declare DwarfSignal_def [eval,evalp]

subsubsection {* Reactive Behaviour *}

text {* We first define the five channels with which to specify the
interaction of the Dwarf signal. Channels can carry data so they all
take a CML type to specify this. Channels which carry no data simply
carry the unit type \texttt{()}. *}

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
design. It states that if the previous state was within the
\texttt{DwarfSignal} type then the operation must ensure it remains in
the \texttt{DwarfSignal} type afterwards. *}

definition "DwarfInv \<equiv> 
  `\<lparr> $dw hasType @DwarfSignal \<rparr> \<turnstile> \<lparr> $dw\<acute> hasType @DwarfSignal \<rparr>`"

text {* Next we specify the operations for the Dwarf Signal process,
all of which are specified use UTP designs to specify the pre- and
post-conditions. The first operation, \texttt{Init}, initialises the
dwarf signal in a stable \textsf{stop} state. It has a \texttt{true}
precondition because it can always be executed. *}

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
oops
(*>*)

text {* \texttt{SetNewProperState} sets a new proper state for the
signal to transition to. The precondition states that the signal must
be stable -- the current state must be the desired proper state -- and
that the desired state is not the current state. The postcondition
sets the desired properstate to the new state and calculates the lamps
which must be lit and extinguished to reach this state. *}

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

text {* \texttt{TurnOn} turns a given lamp on, under the precondition
that the lamp needs to be turned on to reached the desired proper state. *}

definition
  "TurnOn l =
     `\<lparr> ^l^ in @set ($dw).turnon \<rparr> 
      \<turnstile> dw := mk_DwarfType( ($dw).lastproperstate
                          , ($dw).turnoff setminus {^l^}
                          , ($dw).turnon setminus {^l^}
                          , ($dw).currentstate
                          , ($dw).currentstate union {^l^}
                          , ($dw).desiredproperstate)`"

text {* \texttt{TurnOff} turns a given lamp off, under the precondition
that the lamp needs to be turned off to reached the desired proper state. *}

definition
  "TurnOff l =
     `\<lparr> ^l^ in @set ($dw).turnoff \<rparr> 
      \<turnstile> dw := mk_DwarfType( ($dw).lastproperstate
                          , ($dw).turnoff setminus {^l^}
                          , ($dw).turnon setminus {^l^}
                          , ($dw).currentstate
                          , ($dw).currentstate setminus {^l^}
                          , ($dw).desiredproperstate)`"

subsubsection {* Actions *}

text {* With the state and operations for the Dwarf signal specified
we can proceed to define the reactive components of the the Dwarf
process. We first create an action called \texttt{DWARF}, which can
perform several behaviours. If a message is received on channel
\texttt{light}, the \texttt{TurnOn} operation is executed with the
given lamp, and the action then recurses. If a message is received on
the \texttt{extinguish} channel, the given lamp is extinguished. If a
message is received on \texttt{setPS}, a new proper state is
selected. Additionally the Dwarf signal is always capable of
communicating its current state on the \texttt{shine} channel -- this
can be seen as observing the signal. *}



definition 
  "DWARF = `init -> (Init() ; 
       (\<mu> DWARF. 
          (((light?(l) -> TurnOn(&l)) ; DWARF) 
       [] ((extinguish?(l) -> TurnOff(&l)); DWARF)
       [] ((setPS?(s) -> SetNewProperState(&s)); DWARF)
       [] (shine!(($dw).currentstate) -> DWARF))))`"

text {* Next we define some simple test actions for the Dwarf
signal. The first is a working test which, when composed with the
\texttt{DWARF} action, will cause the signal to transition, first to
\texttt{warning}, and then to \texttt{drive}, turning appropriate
lights on and off on the way. This is a valid behaviour. *}

text {* Working test *}
definition
  "TEST1 = `setPS!&warning -> extinguish!<L2> -> light!<L3> 
         -> setPS!&drive -> extinguish!<L1> -> light!<L2> -> STOP`"

text {* The second test tries to turn on 3 lights simulaneously. This
violates the \texttt{NeverShowAll} invariant. *}

definition
  "TEST2 = `setPS!&warning -> light!<L3> -> extinguish!<L2> 
         -> setPS!&drive -> extinguish!<L1> -> light!<L2> -> STOP`"

text {* The third test tries to go straight from \textsf{dark} to \textsf{warning}, which
violates the \texttt{DarkOnlyToStop} variant. *}

definition
  "TEST3 = `setPS!&dark -> extinguish!<L1> -> extinguish!<L2> 
           -> setPS!&warning -> light!<L1> -> light!<L2> -> STOP`"

text {* The fourth test action tries to go from stop to drive, which violates the
\texttt{ForbidStopToDrive} invariant. *}

definition
  "TEST4 = `setPS!&drive -> extinguish!<L1> -> light!<L3> -> STOP`"

text {* We could execute these tests by composing them with the
\texttt{DWARF} action, which is done below: *}

definition "DWARF_CHAN = {setPS\<down>,light\<down>,extinguish\<down>}"

definition "DWARF_TEST1 = `DWARF [|DWARF_CHAN|] TEST1`"
definition "DWARF_TEST2 = `DWARF [|DWARF_CHAN|] TEST2`"
definition "DWARF_TEST3 = `DWARF [|DWARF_CHAN|] TEST3`"
definition "DWARF_TEST4 = `DWARF [|DWARF_CHAN|] TEST4`"

text {* Finally we specify the main action of this process. It waits
for an initialisation signal, sets the initial state for the Dwarf
signal and then enters the main event loop. \texttt{DWARF} could also
be substituted with one of the tests above, to explore a particular
behaviour of the system. *}

definition
  "MainAction = `init -> (Init() ; DWARF)`"

end

subsubsection {* Proof Goals *}

text {* To exemplify CML proof goals, we show that an initialised
state of the signal satisfies the safety invariants. All of these
are discharged by application of the \textsf{cml-tac} proof tactic. *}

lemma NeverShowAll_Init:
"|NeverShowAll(mk_DwarfType(&stop,&stop,{},{},&stop,&stop))| 
 = |true|"
  by (cml_tac)

lemma MaxOneLampChange_Init:
"|MaxOneLampChange(mk_DwarfType(&stop,&stop,{},{},&stop,&stop))| 
 = |true|"
  by (cml_tac)

lemma ForbidStopToDrive_Init:
"|ForbidStopToDrive(mk_DwarfType(&stop,&stop,{},{},&stop,&stop))| 
 = |true|"
  by (cml_tac)

lemma DarkOnlyToStop_Init:
"|DarkOnlyToStop(mk_DwarfType(&stop,&stop,{},{},&stop,&stop))| 
 = |true|"
  by (cml_tac)

lemma DarkOnlyFromStop_Init:
"|DarkOnlyFromStop(mk_DwarfType(&stop,&stop,{},{},&stop,&stop))| 
 = |true|"
  by (cml_tac)

(*<*)
lemma sdty: "|mk_DwarfType(&stop, &stop, {}, {}, &stop, &stop) hasType @DwarfSignal| = |true|"
  by (cml_tac)

end
(*>*)