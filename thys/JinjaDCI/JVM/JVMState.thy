(*  Title:      Jinja/JVM/JVMState.thy

    Author:     Cornelia Pusch, Gerwin Klein, Susannah Mansky
    Copyright   1999 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory JVM/JVMState.thy by Cornelia Pusch and Gerwin Klein
*)

chapter \<open> Jinja Virtual Machine \label{cha:jvm} \<close>

section \<open> State of the JVM \<close>

theory JVMState imports "../Common/Objects" begin


type_synonym 
  pc = nat

abbreviation start_sheap :: "sheap"
where "start_sheap \<equiv> (\<lambda>x. None)(Start \<mapsto> (Map.empty,Done))"

definition start_sheap_preloaded :: "'m prog \<Rightarrow> sheap"
where
  "start_sheap_preloaded P \<equiv> fold (\<lambda>(C,cl) f. f(C := Some (sblank P C, Prepared))) P (\<lambda>x. None)"

subsection \<open> Frame Stack \<close>

datatype init_call_status = No_ics | Calling cname "cname list"
                          | Called "cname list" | Throwing "cname list" addr
	\<comment> \<open>@{text "No_ics"} = not currently calling or waiting for the result of an initialization procedure call\<close>
  \<comment> \<open>@{text "Calling C Cs"} = current instruction is calling for initialization of classes @{text "C#Cs"} (last class
      is the original) -- still collecting classes to be initialized, @{text "C"} most recently collected\<close>
  \<comment> \<open>@{text "Called Cs"} = current instruction called initialization and is waiting for the result
      -- now initializing classes in the list\<close>
  \<comment> \<open>@{text "Throwing Cs a"} = frame threw or was thrown an error causing erroneous end of initialization
        procedure for classes @{text "Cs"}\<close>

type_synonym
  frame = "val list \<times> val list \<times> cname \<times> mname \<times> pc \<times> init_call_status"
  \<comment> \<open>operand stack\<close> 
  \<comment> \<open>registers (including this pointer, method parameters, and local variables)\<close>
  \<comment> \<open>name of class where current method is defined\<close>
  \<comment> \<open>current method\<close>
  \<comment> \<open>program counter within frame\<close>
  \<comment> \<open>indicates frame's initialization call status\<close>

translations
  (type) "frame" <= (type) "val list \<times> val list \<times> char list \<times> char list \<times> nat \<times> init_call_status"

fun curr_stk :: "frame \<Rightarrow> val list" where
"curr_stk (stk, loc, C, M, pc, ics) = stk"

fun curr_class :: "frame \<Rightarrow> cname" where
"curr_class (stk, loc, C, M, pc, ics) = C"

fun curr_method :: "frame \<Rightarrow> mname" where
"curr_method (stk, loc, C, M, pc, ics) = M"

fun curr_pc :: "frame \<Rightarrow> nat" where
"curr_pc (stk, loc, C, M, pc, ics) = pc"

fun init_status :: "frame \<Rightarrow> init_call_status" where
 "init_status (stk, loc, C, M, pc, ics) = ics"

fun ics_of :: "frame \<Rightarrow> init_call_status" where
 "ics_of fr = snd(snd(snd(snd(snd fr))))"


subsection \<open> Runtime State \<close>

type_synonym
  jvm_state = "addr option \<times> heap \<times> frame list \<times> sheap"  
  \<comment> \<open>exception flag, heap, frames, static heap\<close>

translations
  (type) "jvm_state" <= (type) "nat option \<times> heap \<times> frame list \<times> sheap"

fun frames_of :: "jvm_state \<Rightarrow> frame list" where
"frames_of (xp, h, frs, sh) = frs"

abbreviation sheap :: "jvm_state \<Rightarrow> sheap" where
"sheap js \<equiv> snd (snd (snd js))"

end
