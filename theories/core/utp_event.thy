(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_event.thy                                                        *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Events *}

theory utp_event
imports 
  utp_names
  utp_value
begin

type_synonym 'a CHANNEL = "NAME * 'a UTYPE"

abbreviation chan_name :: "'a CHANNEL \<Rightarrow> NAME" where
"chan_name c \<equiv> fst c"

abbreviation chan_type :: "'a CHANNEL \<Rightarrow> 'a UTYPE" where
"chan_type c \<equiv> snd c"

typedef 'a EVENT = "{(c::'a CHANNEL, v :: 'a). v : chan_type c}"
  by (auto)

setup_lifting type_definition_EVENT

lift_definition EVENT_channel :: "'a EVENT \<Rightarrow> 'a CHANNEL" is "fst"
  by simp

lift_definition EVENT_value :: "'a EVENT \<Rightarrow> 'a" is "snd"
  by simp

end
