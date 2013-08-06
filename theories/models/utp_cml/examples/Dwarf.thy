theory Dwarf
imports 
  "../utp_cml"
begin

ML {*
  structure dwarf_simps =
    Named_Thms (val name = @{binding dwarf_simps} val description = "dwarf simps")
*}

setup dwarf_simps.setup


abbreviation "L1 \<equiv> ''L1''"
abbreviation "L2 \<equiv> ''L2''"
abbreviation "L3 \<equiv> ''L3''"

text {* First set of VDM types, which depend on nothing else *}

abbreviation "LampId   \<equiv> \<parallel><L1> | <L2> | <L3>\<parallel>"
abbreviation "Signal   \<equiv> \<parallel>@set of @LampId\<parallel>"

text {* Next define the "proper states" for the signal *}

definition "dark     \<equiv> +|{}|+"
definition "stop     \<equiv> +|{<L1>, <L2>}|+"
definition "warning  \<equiv> +|{<L1>, <L3>}|+"
definition "drive    \<equiv> +|{<L2>, <L3>}|+"

declare dark_def [dwarf_simps]
declare stop_def [dwarf_simps]
declare warning_def [dwarf_simps]
declare drive_def [dwarf_simps]

text {* A proper state is a signal which falls within this set *}

abbreviation 
  "ProperState \<equiv> \<parallel>@Signal inv ps == (^ps^ in @set {&dark, &stop, &warning, &drive})\<parallel>"

text {* Setting up a record type is currently a little complicated, though could
        easily be automatically generated. First we create a new unit type to act
        as the "tag" for this record so that it can be distinguished from others. We
        create an instance of the tag class which proves its a unit type and associates
        a string with it (the name of the type). *}

typedef DwarfType_Tag = "{True}" by auto
instantiation DwarfType_Tag :: tag
begin
definition "tagName_DwarfType_Tag (x::DwarfType_Tag) = ''DwarfType''"
instance 
  by (intro_classes, metis (full_types) Abs_DwarfType_Tag_cases singleton_iff)
end

text {* Next we create a collection of fields associated with the tag, and give each
        the position in record and its VDM type. *}

abbreviation "lastproperstate_fld    \<equiv> MkField TYPE(DwarfType_Tag) #1 \<parallel>@ProperState\<parallel>"
abbreviation "desiredproperstate_fld \<equiv> MkField TYPE(DwarfType_Tag) #2 \<parallel>@ProperState\<parallel>"
abbreviation "turnoff_fld            \<equiv> MkField TYPE(DwarfType_Tag) #3 \<parallel>@set of @LampId\<parallel>"
abbreviation "turnon_fld             \<equiv> MkField TYPE(DwarfType_Tag) #4 \<parallel>@set of @LampId\<parallel>"
abbreviation "laststate_fld          \<equiv> MkField TYPE(DwarfType_Tag) #5 \<parallel>@Signal\<parallel>"
abbreviation "currentstate_fld       \<equiv> MkField TYPE(DwarfType_Tag) #6 \<parallel>@Signal\<parallel>"

text {* Then we use these fields to create selector functions for the record, which
        can be used directly in UTP/VDM predicates *}

abbreviation "lastproperstate    \<equiv> SelectRec lastproperstate_fld"
abbreviation "desiredproperstate \<equiv> SelectRec desiredproperstate_fld"
abbreviation "turnoff            \<equiv> SelectRec turnoff_fld"
abbreviation "turnon             \<equiv> SelectRec turnon_fld"
abbreviation "laststate          \<equiv> SelectRec laststate_fld"
abbreviation "currentstate       \<equiv> SelectRec currentstate_fld"

text {* Finally we create the actual type by giving the list of fields and the associated
        invariant. We also create a record constructor, mk_DwarfType. *}

definition 
  "DwarfType \<equiv> \<parallel>[ lastproperstate_fld
                , desiredproperstate_fld
                , turnoff_fld
                , turnon_fld
                , laststate_fld
                , currentstate_fld] 
                inv d == ((^d^.currentstate setminus ^d^.turnoff) union ^d^.turnon 
                            = ^d^.desiredproperstate)
                         and 
                         (^d^.turnon inter ^d^.turnoff = {})\<parallel>"

declare DwarfType_def [dwarf_simps]

definition "mk_DwarfType \<equiv> MkRec DwarfType"

declare mk_DwarfType_def [dwarf_simps]

text {* Safety Properties *}


term "|mk_DwarfType(&stop, {}, {}, &stop, &stop, &stop)|"

definition 
  "NeverShowAll = |lambda d & ^d^.#1.currentstate <> {<L1>,<L2>,<L3>}|"

definition 
  "MaxOneLampChange = 
    |lambda d & card ((^d^.#1.currentstate setminus ^d^.#1.laststate) 
                      union (^d^.#1.laststate setminus ^d^.#1.currentstate)) 
                      <= 1|"

definition
  "ForbidStopToDrive = 
     |lambda d & (^d^.#1.lastproperstate = &stop) => ^d^.#1.desiredproperstate <> &drive|"
  
definition
  "DarkOnlyToStop = 
     |lambda d & (^d^.#1.lastproperstate = &dark) => ^d^.#1.desiredproperstate in @set {&dark,&stop}|" 
  
definition
  "DarkOnlyFromStop = 
     |lambda d & (^d^.#1.desiredproperstate = &dark) => ^d^.#1.lastproperstate in @set {&dark,&stop}|"

definition 
  "DwarfSignal = \<parallel>@DwarfType inv d == NeverShowAll(^d^) 
                                   and MaxOneLampChange(^d^)
                                   and ForbidStopToDrive(^d^)
                                   and DarkOnlyToStop(^d^)
                                   and DarkOnlyFromStop(^d^)\<parallel>"

text {* The Dwarf Signal has a single state variable which gives 
        the state of the signal. *}

text {* Channels *}

definition "init = MkChanD ''init'' \<parallel>()\<parallel>"
definition "light = MkChanD ''light'' \<parallel>@LampId\<parallel>"
definition "extinguish = MkChanD ''extinguish'' \<parallel>@LampId\<parallel>"
definition "setPS = MkChanD ''setPS'' \<parallel>@ProperState\<parallel>"
definition "shine = MkChanD ''shine'' \<parallel>@Signal\<parallel>"

locale DwarfProcess
begin

text {* State *}

definition "dw \<equiv> MkVarD ''dw'' DwarfType"

definition "DwarfInv \<equiv> `\<lparr> $dw hasType @DwarfType \<rparr> \<turnstile> \<lparr> $dw\<acute> hasType @DwarfType \<rparr>`"

text {* Operations *}

definition "Init = `true \<turnstile> (dw := mk_DwarfType(&stop, {}, {}, &stop, &stop, &stop))`"

(*
lemma "|mk_DwarfType(&stop, {}, {}, &stop, &stop, &stop) hasType @DwarfType| = |true|"
  apply (simp add:evalp dwarf_simps)
  apply (simp add:EvalD_Op1D)


lemma "DwarfInv \<sqsubseteq> Init"
  apply (unfold DwarfInv_def Init_def)
  apply (rule refine)
  prefer 6
  apply (rule_tac RefineP_seperation_refine)
  apply (auto intro!: refine unrest)
*)

definition 
  "SetNewProperState st = 
      `\<lparr>($dw).currentstate = ($dw).desiredproperstate and ^st^ <> ($dw).currentstate\<rparr> 
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

(* Working test *)
definition
  "TEST1 = `setPS!&warning -> extinguish!<L2> -> light!<L3> 
           -> setPS!&drive -> extinguish!<L1> -> light!<L2> -> STOP`"

(* Tries to turn on 3 lights simulaneously *)
definition
  "TEST2 = `setPS!&warning -> light!<L3> -> extinguish!<L2> 
           -> setPS!&drive -> extinguish!<L1> -> light!<L2> -> STOP`"

(* Tries to go from dark to warning *)
definition
  "TEST3 = `setPS!&dark -> extinguish!<L1> -> extinguish!<L2> -> setPS!&warning -> 
            light!<L1> -> light!<L2> -> STOP`"

(* Tries to go from stop to drive *)
definition
  "TEST4 = `setPS!&drive -> extinguish!<L1> -> light!<L3> -> STOP`"

definition "DWARF_TEST1 = `DWARF [|{setPS\<down>,light\<down>,extinguish\<down>}|] TEST1`"
definition "DWARF_TEST2 = `DWARF [|{setPS\<down>,light\<down>,extinguish\<down>}|] TEST2`"
definition "DWARF_TEST3 = `DWARF [|{setPS\<down>,light\<down>,extinguish\<down>}|] TEST3`"
definition "DWARF_TEST4 = `DWARF [|{setPS\<down>,light\<down>,extinguish\<down>}|] TEST4`"

definition 
  "MainAction = DWARF"

end

end