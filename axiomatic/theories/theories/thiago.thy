(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: thiago.thy                                                           *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>A Modular Theory of Object Orientation\<close>

theory thiago
imports utheory designs thiago_prel
begin

subsection \<open>Theory Types\<close>

datatype cname = Object | Class "string"
datatype aname = Attr "string"
datatype prim = int | bool
datatype atype = PType "prim" | CType "cname"

subsection \<open>Refinement Orders\<close>

flat_order cname
flat_order aname
flat_order prim
flat_order atype

subsection \<open>Type Injections\<close>

inject_type cname
inject_type aname
inject_type prim
inject_type atype

subsection \<open>Theory Variables\<close>

declare_uvar cls :: "cname set"
declare_uvar sc :: "(cname, cname) rel"
declare_uvar atts :: "(cname, (aname, atype) rel) rel"

subsection \<open>Utility Definitions\<close>

definition prim :: "atype set" where
"prim \<equiv> range PType"

subsection \<open>Healthiness Conditions\<close>

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

subsection \<open>Proof Experiments\<close>

theorem "`{OO1} \<Rightarrow> cls \<noteq> {}`"
apply (unfold OO1_def)
apply (unfold evalp simp_thms)
apply (subst ustate_transfer)
apply (auto)
done
end