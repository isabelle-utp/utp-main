(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: thiago.thy                                                           *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 26 Jan 2016 *)

section {* A Modular Theory of Object Orientation *}

theory thiago
imports utheory designs thiago_prel
begin

subsection {* Theory Types *}

datatype cname = Object | Class "string"
datatype aname = Attr "string"
datatype prim = int | bool
datatype atype = PType "prim" | CType "cname"

subsection {* Refinement Orders *}

flat_order cname
flat_order aname
flat_order prim
flat_order atype

subsection {* Type Injections *}

inject_type cname
inject_type aname
inject_type prim
inject_type atype

subsection {* Theory Variables *}

declare_uvar cls :: "cname set"
declare_uvar sc :: "(cname, cname) rel"
declare_uvar atts :: "(cname, (aname, atype) rel) rel"

subsection {* Utility Definitions *}

definition prim :: "atype set" where
"prim \<equiv> range PType"

subsection {* Healthiness Conditions *}

definition OO1 :: "upred" where
"OO1 = (Object \<in> cls)\<^sub>p"

definition OO2 :: "upred" where
"OO2 = (dom sc = (cls - {Object}))\<^sub>p"

definition OO3 :: "upred" where
"OO3 = (\<forall> C \<in> dom sc . (C, Object) \<in> sc\<^sup>+)\<^sub>p"

definition OO4 :: "upred" where
"OO4 = (dom atts = cls)\<^sub>p"

definition OO5 :: "upred" where
"OO5 = (\<forall> C1 \<in> dom atts .
        \<forall> C2 \<in> dom atts . C1 \<noteq> C2 |
          dom (atts\<cdot>C1) \<inter> dom (atts\<cdot>C2) = {})\<^sub>p"

definition OO6 :: "upred" where
"OO6 = (ran (\<Union> (ran atts)) \<subseteq> prim \<union> (CType ` cls))\<^sub>p"

subsection {* Proof Experiments *}

theorem "`{OO1} \<Rightarrow> cls \<noteq> {}`"
apply (unfold OO1_def)
apply (unfold evalp simp_thms)
apply (subst ustate_transfer)
apply (auto)
done
end