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

type_synonym 'a CHANNEL  = "NAME * 'a itself"

abbreviation MkCHAN :: "NAME \<Rightarrow> 'a itself \<Rightarrow> 'a CHANNEL" where
"MkCHAN n t \<equiv> (n, t)"

type_synonym 'a UCHANNEL = "NAME * 'a UTYPE"

abbreviation chan_name :: "'a UCHANNEL \<Rightarrow> NAME" where
"chan_name c \<equiv> fst c"

abbreviation chan_type :: "'a UCHANNEL \<Rightarrow> 'a UTYPE" where
"chan_type c \<equiv> snd c"

subsection {* Event Sort *}

text {* Events carry values, and therefore before we can introduce the
        type we need to define the permissible types which can event
        can contain in class EVENT_PERM. We then use this to constrain 
        the EVENT typedef *}

class EVENT_PERM = VALUE +
  fixes   EventPerm :: "'a UTYPE set"
  assumes EventPerm_exists: "\<exists> x. x \<in> EventPerm"

typedef 'm::EVENT_PERM EVENT = 
  "{(c::'m UCHANNEL, v :: 'm). chan_type c \<in> EventPerm \<and> v : chan_type c}"
  apply (auto)
  apply (metis (lifting) EventPerm_exists fst_eqD prod_caseI2 snd_eqD type_non_empty_defined)
done

declare Rep_EVENT [simp]
declare Rep_EVENT_inverse [simp]
declare Abs_EVENT_inverse [simp]

lemma Rep_EVENT_intro [intro]:
  "Rep_EVENT x = Rep_EVENT y \<Longrightarrow> x = y"
  by (auto simp add: Rep_EVENT_inject[THEN sym])

setup_lifting type_definition_EVENT

instantiation EVENT :: (VALUE) DEFINED_NE
begin

definition "Defined_EVENT (x::'a EVENT) = True"

instance
  by (intro_classes, auto simp add:Defined_EVENT_def)
end

lemma Defined_EVENT [defined]:
  "\<D> (x :: 'a EVENT) = True"
  by (simp add:Defined_EVENT_def)

abbreviation EV :: "NAME \<Rightarrow> ('a::EVENT_PERM) UTYPE \<Rightarrow> 'a \<Rightarrow> 'a EVENT" where
"EV n t v \<equiv> Abs_EVENT ((n, t), v)"

(*
definition MkEVENT :: "NAME \<Rightarrow> ('a::EVENT_PERM) UTYPE \<Rightarrow> 'a \<Rightarrow> 'a EVENT" where
"MkEVENT n t v = (if (t \<in> EventPerm \<and> v :! t) 
                  then (Abs_EVENT ((n, t), v))
                  else (Abs_EVENT ((n, (SOME t. t \<in> EventPerm)), default (SOME t. t \<in> EventPerm))))"

rep_datatype "MkEVENT"
  apply (auto simp add:MkEVENT_def)
apply (metis Rep_EVENT_inverse pair_collapse)
*)

class EVENT_SORT = EVENT_PERM +
  fixes MkEvent   :: "'a EVENT \<Rightarrow> 'a"
  and   DestEvent :: "'a \<Rightarrow> 'a EVENT"
  and   EventType :: "'a UTYPE"

  assumes Inverse [simp] : 
    "DestEvent (MkEvent v) = v"
  and     EventType_dcarrier: 
    "dcarrier EventType = range MkEvent"
  and     EventType_monotype [typing]: "monotype EventType"
begin

lemma MkEvent_defined [defined] : 
  "\<D> (MkEvent e)"
  by (metis EventType_dcarrier dcarrier_defined rangeI)

lemma MkEvent_type [typing]: "MkEvent b : EventType"
  by (metis EventType_dcarrier dcarrier_type rangeI)

lemma MkEvent_dtype [typing]: 
  "MkEvent e :! EventType"
  by (metis EventType_dcarrier dcarrier_dtype rangeI)

lemma MkEvent_inj: "inj MkEvent"
  by (metis Inverse injI)

lemma DestEvent_inv [simp]: "x :! EventType \<Longrightarrow> MkEvent (DestEvent x) = x"
  by (smt EventType_dcarrier Inverse dtype_as_dcarrier image_iff)

end

lift_definition EVENT_channel :: "'a::EVENT_PERM EVENT \<Rightarrow> 'a UCHANNEL" is "fst"
  by simp

lift_definition EVENT_value :: "'a::EVENT_PERM EVENT \<Rightarrow> 'a" is "snd"
  by simp

lemma EVENT_channel_EV [simp]: 
  "\<lbrakk> v : t; t \<in> EventPerm \<rbrakk> \<Longrightarrow> EVENT_channel (EV n t v) = (n, t)"
  by (auto simp add:EVENT_channel_def)

lemma EVENT_value_EV [simp]:
  "\<lbrakk> v : t; t \<in> EventPerm \<rbrakk> \<Longrightarrow> EVENT_value (EV n t v) = v"
  by (auto simp add:EVENT_value_def)

end
