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

typedef 'a::type CHAN  = "UNIV :: (NAME * 'a itself) set"
  morphisms DestCHAN MkCHAN
  by simp

declare DestCHAN_inverse [simp]
declare MkCHAN_inverse[simplified,simp]

abbreviation chan_name :: "'a::type CHAN \<Rightarrow> NAME" where
"chan_name c \<equiv> fst (DestCHAN c)"

abbreviation chan_type :: "'a::type CHAN \<Rightarrow> 'a itself" where
"chan_type c \<equiv> snd (DestCHAN c)"

typedef 'a UCHAN = "UNIV :: (NAME * 'a UTYPE) set"
  morphisms DestUCHAN MkUCHAN
  by (simp)

declare DestUCHAN_inverse [simp]
declare MkUCHAN_inverse[simplified,simp]

abbreviation uchan_name :: "'a UCHAN \<Rightarrow> NAME" where
"uchan_name c \<equiv> fst (DestUCHAN c)"

abbreviation uchan_type :: "'a UCHAN \<Rightarrow> 'a UTYPE" where
"uchan_type c \<equiv> snd (DestUCHAN c)"

subsection {* Event Sort *}

text {* Events carry values, and therefore before we can introduce the
        type we need to define the permissible types which can event
        can contain in class EVENT_PERM. We then use this to constrain 
        the EVENT typedef *}

class EVENT_PERM = VALUE +
  fixes   EventPerm :: "'a UTYPE set"
  assumes EventPerm_exists: "\<exists> x. x \<in> EventPerm"

typedef ('m::EVENT_PERM) EVENT = 
  "{(c :: 'm UCHAN, v :: 'm). uchan_type c \<in> EventPerm 
                            \<and> v : uchan_type c}"
  morphisms DestEVENT MkEVENT
  apply (auto)
  apply (metis (mono_tags) DestUCHAN_cases EventPerm_exists 
               UNIV_I default_type snd_def split_conv)
done

declare DestEVENT [simp]
declare DestEVENT_inverse [simp]
declare MkEVENT_inverse [simp]

lemma DestEVENT_intro [intro]:
  "DestEVENT x = DestEVENT y \<Longrightarrow> x = y"
  by (auto simp add: DestEVENT_inject[THEN sym])

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
"EV n t v \<equiv> MkEVENT (MkUCHAN (n, t), v)"

text {* Make all possible events over a set of channels *}

abbreviation MkEvents :: "'a::EVENT_PERM UCHAN set \<Rightarrow> 'a EVENT set" where
"MkEvents cs \<equiv> {MkEVENT (c,v) | c v. c \<in> cs}"

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

lemma map_EventList [simp]:
  assumes "set xs \<subseteq> dcarrier EventType"
  shows "map (MkEvent \<circ> DestEvent) xs = xs"
proof -
  have "map (MkEvent \<circ> DestEvent) xs = map id xs"
    apply (subst map_eq_conv)
    apply (auto)
    apply (metis (full_types) DestEvent_inv assms dtype_as_dcarrier set_mp)
  done

  thus ?thesis
    by auto
qed

lemma DestEvent_inj [simp]:
  "inj_on DestEvent (dcarrier EventType)"
  by (metis (hide_lams, no_types) DestEvent_inv dtype_as_dcarrier inj_on_def)

end

lift_definition EVENT_chan :: "'a::EVENT_PERM EVENT \<Rightarrow> 'a UCHAN" is "fst"
  by simp

lift_definition EVENT_value :: "'a::EVENT_PERM EVENT \<Rightarrow> 'a" is "snd"
  by simp

lemma MkEVENT_inv [simp]:
  "\<lbrakk> v : uchan_type c; uchan_type c \<in> EventPerm \<rbrakk> \<Longrightarrow> DestEVENT (MkEVENT (c, v)) = (c, v)"
  by (metis (lifting) MkEVENT_inverse mem_Collect_eq splitI)

lemma EVENT_chan_MkEVENT [simp]: 
  "\<lbrakk> v : uchan_type c; uchan_type c \<in> EventPerm \<rbrakk> \<Longrightarrow> EVENT_chan (MkEVENT (c, v)) = c"
  by (simp add:EVENT_chan_def)

lemma EVENT_value_MkEVENT [simp]:
  "\<lbrakk> v : uchan_type c; uchan_type c \<in> EventPerm \<rbrakk> \<Longrightarrow> EVENT_value (MkEVENT (c, v)) = v"
  by (simp add:EVENT_value_def)

lemma MkEVENT_eta [simp]: 
  "MkEVENT (EVENT_chan e, EVENT_value e) = e"
  by (case_tac e, auto)

lemma EVENT_chan_EV [simp]: 
  "\<lbrakk> v : t; t \<in> EventPerm \<rbrakk> \<Longrightarrow> EVENT_chan (EV n t v) = MkUCHAN (n, t)"
  by (auto simp add:EVENT_chan_def)

lemma EVENT_value_EV [simp]:
  "\<lbrakk> v : t; t \<in> EventPerm \<rbrakk> \<Longrightarrow> EVENT_value (EV n t v) = v"
  by (auto simp add:EVENT_value_def)

end
