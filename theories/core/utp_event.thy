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

declare Rep_EVENT [simp]
declare Rep_EVENT_inverse [simp]
declare Abs_EVENT_inverse [simp]

lemma Rep_EVENT_intro [intro]:
  "Rep_EVENT x = Rep_EVENT y \<Longrightarrow> x = y"
  by (auto simp add: Rep_EVENT_inject[THEN sym])

abbreviation EV :: "NAME \<Rightarrow> 'a UTYPE \<Rightarrow> 'a \<Rightarrow> 'a EVENT" where
"EV n t v \<equiv> Abs_EVENT ((n, t), v)"

type_synonym 'a PEvent = "(NAME * 'a)"

setup_lifting type_definition_EVENT

lift_definition EVENT_channel :: "'a EVENT \<Rightarrow> 'a CHANNEL" is "fst"
  by simp

lift_definition EVENT_value :: "'a EVENT \<Rightarrow> 'a" is "snd"
  by simp

lemma EVENT_channel_EV [simp]: 
  "v : t \<Longrightarrow> EVENT_channel (EV n t v) = (n, t)"
  by (auto simp add:EVENT_channel_def)

lemma EVENT_value_EV [simp]:
  "v : t \<Longrightarrow> EVENT_value (EV n t v) = v"
  by (auto simp add:EVENT_value_def)

end
