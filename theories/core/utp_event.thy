(******************************************************************************)
(* Project: Unifying Theories of Programming in Isabelle/HOL                  *)
(* File: utp_event.thy                                                        *)
(* Author: Simon Foster & Frank Zeyda, University of York (UK)                *)
(******************************************************************************)
(* LAST REVIEWED: 6 August 2014 *)

header {* Communication Events *}

theory utp_event
imports utp_defined
  utp_name
  utp_model
  utp_sorts_new
begin

subsection {* Channel Type (HOL) *}

text {* Do we really need the following type? Remove if not... *}

default_sort type

typedef 'a chan  = "UNIV :: (name * 'a itself) set"
  morphisms RepChan AbsChan
apply (rule UNIV_witness)
done

declare AbsChan_inverse [simplified, simp]
declare RepChan_inverse [simp]

subsubsection {* Destructors *}

abbreviation chan_name :: "'a chan \<Rightarrow> name" where
"chan_name c \<equiv> fst (RepChan c)"

abbreviation chan_type :: "'a chan \<Rightarrow> 'a itself" where
"chan_type c \<equiv> snd (RepChan c)"

subsection {* Channel Type (UTP) *}

default_sort TYPED_MODEL

typedef 'm uchan = "UNIV :: (name * 'm utype) set"
  morphisms RepUChan AbsUChan
apply (rule UNIV_witness)
done

declare AbsUChan_inverse [simplified, simp]
declare RepUChan_inverse [simp]

subsubsection {* Destructors *}

abbreviation uchan_name :: "'m uchan \<Rightarrow> name" where
"uchan_name c \<equiv> fst (RepUChan c)"

abbreviation uchan_type :: "'m uchan \<Rightarrow> 'm utype" where
"uchan_type c \<equiv> snd (RepUChan c)"

subsection {* Event Type *}

typedef 'm event = "{(c :: 'm uchan, v :: 'm uval). v : uchan_type c}"
  morphisms RepEvent AbsEvent
apply (rule_tac x =
  "(AbsUChan (bName ''x'', some_type), some_value some_type)" in exI)
apply (clarsimp)
done

setup_lifting type_definition_event

declare AbsEvent_inverse [simp]
declare RepEvent_inverse [simp]
declare RepEvent [simp]

lemma RepEvent_intro [intro] :
"RepEvent x = RepEvent y \<Longrightarrow> x = y"
apply (metis RepEvent_inverse)
done

subsubsection {* Constructors *}

abbreviation Event :: "name \<Rightarrow> 'a utype \<Rightarrow> 'a uval \<Rightarrow> 'a event" where
"Event n t v \<equiv> AbsEvent (AbsUChan (n, t), v)"

abbreviation EventSet :: "'a uchan set \<Rightarrow> 'a event set" where
"EventSet cs \<equiv> {AbsEvent (c, v) | c v . c \<in> cs \<and> v : uchan_type c}"

subsubsection {* Destructors *}

lift_definition EventChan :: "'a event \<Rightarrow> 'a uchan" is "fst" .

lift_definition EventValue :: "'a event \<Rightarrow> 'a uval" is "snd" .

subsubsection {* Theorems *}

lemma AbsEvent_inverse2 [simp] :
"v : uchan_type c \<Longrightarrow> RepEvent (AbsEvent (c, v)) = (c, v)"
  by (metis AbsEvent_inverse mem_Collect_eq prod.case)

lemma EventChan_AbsEvent [simp] :
"v : uchan_type c \<Longrightarrow> EventChan (AbsEvent (c, v)) = c"
  by (metis AbsEvent_inverse2 EventChan.rep_eq fst_conv)

lemma EventValue_AbsEvent [simp] :
"v : uchan_type c \<Longrightarrow> EventValue (AbsEvent (c, v)) = v"
  by (metis AbsEvent_inverse2 EventValue.rep_eq snd_conv)

lemma MkEvent_eta [simp] :
  "AbsEvent (EventChan e, EventValue e) = e"
  by (case_tac e, auto)

lemma EventChan_Event [simp] :
  "v : t \<Longrightarrow> EventChan (Event n t v) = AbsUChan (n, t)"
  by (metis AbsUChan_inverse EventChan_AbsEvent UNIV_I snd_conv)

lemma EventValue_Event [simp] :
"v : t \<Longrightarrow> EventValue (Event n t v) = v"
  by (metis AbsUChan_inverse EventValue_AbsEvent UNIV_I snd_conv)

subsubsection {* Definedness *}

instantiation event :: (TYPED_MODEL) DEFINED_NE
begin
definition defined_event :: "'a event \<Rightarrow> bool" where
"\<D> (x :: 'a event) = True"
instance
  by (intro_classes, unfold defined_event_def, simp)

theorem defined_event [defined] :
"\<D> (x :: 'a event) = True"
apply (simp add: defined_event_def)
done
end

subsection {* Event Sort *}

class EVENT_SORT =
  fixes MkEvent :: "'a::TYPED_MODEL event \<Rightarrow> 'a uval"
  fixes DestEvent :: "'a uval \<Rightarrow> 'a event"
  fixes EventType :: "'a utype"
  assumes INSTANCE : "UTP_BASIC_SORT MkEvent DestEvent UNIV EventType"
  assumes EventType_monotype [typing] : "monotype EventType"
begin

subsubsection {* Locale Imports *}

abbreviation IsEvent :: "'a uval \<Rightarrow> bool" where
"IsEvent \<equiv> UTP_BASIC_SORT.IsVal EventType"

theorems
  IsEvent_def [simp] = UTP_BASIC_SORT.IsVal_def [OF INSTANCE]

theorems
  MkEvent_defined [defined] = UTP_BASIC_SORT.MkVal_defined [OF INSTANCE] and
  MkEvent_typed [simplified, typing] = UTP_BASIC_SORT.MkVal_typed [OF INSTANCE] and
  MkEvent_inverse [simplified, simp] = UTP_BASIC_SORT.MkVal_inverse [OF INSTANCE] and
  DestEvent_inverse [simp] = UTP_BASIC_SORT.DestVal_inverse [OF INSTANCE] and
  MkEvent_inj_on [simp] = UTP_BASIC_SORT.MkVal_inj_on [OF INSTANCE] and
  DestEvent_inj_on [simp] = UTP_BASIC_SORT.DestVal_inj_on [OF INSTANCE]

theorems
  dcarrier_EventType = UTP_BASIC_SORT.dcarrier_Type [OF INSTANCE] and
  DestEvent_dcarrier_image = UTP_BASIC_SORT.DestVal_dcarrier_image [OF INSTANCE] and
  in_image_EventVal = UTP_BASIC_SORT.in_image_MkVal [OF INSTANCE]

subsubsection {* Event Values *}

definition EVENT_VALUE :: "'a uval set" where
"EVENT_VALUE = dcarrier EventType"

theorem defined_MkEvent [defined] :
"\<D> (MkEvent e)"
apply (metis MkEvent_defined UNIV_I defined_uval_def)
done

theorem MkEvent_strictly_typed [typing] :
  "MkEvent e :! EventType"
apply (simp add: defined typing)
done

theorem MkEvent_inj :
"inj MkEvent"
apply (rule injI)
apply (metis MkEvent_inverse)
done

theorem map_EventList [simp] :
  assumes "set xs \<subseteq> dcarrier EventType"
  shows "map (MkEvent \<circ> DestEvent) xs = xs"
proof -
  have "map (MkEvent \<circ> DestEvent) xs = map id xs"
    apply (subst map_eq_conv)
    apply (clarsimp)
    apply (metis DestEvent_inverse assms dcarrier_member set_rev_mp)
  done

  thus ?thesis by auto
qed
end
end
