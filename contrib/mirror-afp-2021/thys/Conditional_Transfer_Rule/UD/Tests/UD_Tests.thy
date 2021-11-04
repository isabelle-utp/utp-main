(* Title: UD/Tests/UD_Tests.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

A test suite for the framework UD.
*)

section\<open>Test suite for UD\<close>
theory UD_Tests
  imports
    "../UD"
    "../../IML_UT/IML_UT"
    Complex_Main
begin



subsection\<open>Background\<close>

(* 
The following two definitions were copied from 
HOL-Analysis.Elementary_Topology with minor amendments
to avoid unnecessary dependencies
*)
definition (in topological_space) islimpt:: "'a \<Rightarrow> 'a set \<Rightarrow> bool"
  where "islimpt x S \<longleftrightarrow> (\<forall>T. x\<in>T \<longrightarrow> open T \<longrightarrow> (\<exists>y\<in>S. y\<in>T \<and> y\<noteq>x))"
definition closure :: "('a::topological_space) set \<Rightarrow> 'a set" 
  where "closure S = S \<union> {x. islimpt x S}"

ud \<open>topological_space.closed\<close>
ud \<open>islimpt\<close>

lemma closed_with: "closed \<equiv> closed.with open"
  unfolding closed_def closed.with_def .

definition closure_with :: "('a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "closure_with \<tau> \<equiv> \<lambda>S. S \<union> {x. islimpt.with \<tau> x S}"

lemma closure_with: "closure \<equiv> closure_with open"
  unfolding closure_def islimpt.with closure_with_def .



subsection\<open>Tests\<close>

ML_file\<open>UD_TEST_UNOVERLOAD_DEFINITION.ML\<close>

ML\<open>
val ud_test_unoverload_definition_test_results =
  ud_test_unoverload_definition.execute_test_suite_unoverload_definition
    @{theory}
\<close>
ML\<open>
val _ = ud_test_unoverload_definition_test_results
  |> UT_Test_Suite.output_test_results true
\<close>

end