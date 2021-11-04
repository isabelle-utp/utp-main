(* Title: CTR/Tests/CTR_Tests.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

A test suite for the sub-framework CTR.
*)

section\<open>A test suite for CTR\<close>
theory CTR_Tests
  imports
    "../CTR"
    "../../IML_UT/IML_UT"
    Complex_Main
  keywords "ctr_test" :: thy_defn
begin



subsection\<open>Background\<close>

ML\<open>

type ctr_test_data =
  {
    ctr_type : string,
    synthesis : (string * thm list option) option,
    elems: (string, string, Facts.ref) Element.ctxt list,
    type_specs : (string * string) list,
    thm_specs : ((binding option * thm) * mixfix) list
  };

structure CTRTestData = Generic_Data
  (
    type T = ctr_test_data Symtab.table
    val empty = Symtab.empty
    val extend = I
    val merge = Symtab.merge (K true)
  );

val get_ctr_test_data_generic = CTRTestData.get;
val get_ctr_test_data_proof = Context.Proof #> get_ctr_test_data_generic;
val get_ctr_test_data_global = Context.Theory #> get_ctr_test_data_generic;
fun test_data_of_generic context = context
  |> get_ctr_test_data_generic
  |> Symtab.lookup;
val ctr_test_data_of_proof = Context.Proof #> test_data_of_generic;

(*oversimplified: to be used with care*)
fun update_ctr_test_data k ctr_test_data =
  Local_Theory.declaration
    {pervasive=true, syntax=false}
    (fn _ => (k, ctr_test_data) |> Symtab.update |> CTRTestData.map);

fun process_ctr_test_data (k, args) (lthy : local_theory) =
  let
    fun preprocess_thm_specs lthy =
      map (apfst (apsnd (singleton (Attrib.eval_thms lthy))))
    fun process_ctrs_impl (CTR.ALG_PP _) (lthy : local_theory) = lthy
      | process_ctrs_impl
          (CTR.ALG_RP (((synthesis, elems), type_specs), thm_specs))
          (lthy : local_theory) =
          let
            val thm_specs' = preprocess_thm_specs lthy thm_specs
            val synthesis' = Option.map
              (apsnd (Option.map ((single #> Attrib.eval_thms lthy))))
              synthesis
            val data : ctr_test_data =
              {
                ctr_type = "relativization",
                synthesis = synthesis',
                elems = elems,
                type_specs = type_specs,
                thm_specs = thm_specs'
              }
          in update_ctr_test_data k data lthy end
  in process_ctrs_impl args lthy end;

val ctr_test_parser = Parse.string -- CTR.ctr_parser;

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>ctr_test\<close>
    "test setup for the command ctr"
    (ctr_test_parser >> process_ctr_test_data);

\<close>

ud \<open>order.mono\<close>
ud mono' \<open>mono\<close> 

definition mono_ow :: 
  "'a set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "mono_ow UB leb lea f \<equiv> \<forall>x\<in>UB. \<forall>y\<in>UB. lea x y \<longrightarrow> leb (f x) (f y)"

typedef 'a K = \<open>{xs::'a list. length xs = 2}\<close>
  by (simp add: Ex_list_of_length)

definition KK :: "'a K \<Rightarrow> 'a K \<Rightarrow> bool" 
  where "KK k1 k2 \<equiv> k1 = k2"

typedef 'a L = \<open>{xs::'a list. length xs = 2}\<close>
  by (simp add: Ex_list_of_length)

definition LL :: "'a L \<Rightarrow> 'a L \<Rightarrow> bool" 
  where "LL k1 k2 \<equiv> k1 = k2"

definition rel_L :: 
  "('a::group_add \<Rightarrow> 'b::group_add \<Rightarrow> bool) \<Rightarrow> 'a::group_add L \<Rightarrow> 'b::group_add L \<Rightarrow> bool" 
  where "rel_L A b c = True"

ctr_relator rel_L

definition not_binders_binrelT :: 
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  where "not_binders_binrelT R1 R2 a b = True"

definition no_dup_binrelT :: 
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  where "no_dup_binrelT R1 R2 a b = True"

definition not_binders_binrelT_ftv_stv :: 
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
  where "not_binders_binrelT_ftv_stv R1 R2 a b = True"

definition not_type_constructor_lhs :: 
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a K \<Rightarrow> bool"
  where "not_type_constructor_lhs R1 R2 a b = True"

definition not_type_constructor_rhs :: 
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'a K \<Rightarrow> 'e \<Rightarrow> bool"
  where "not_type_constructor_rhs R1 R2 a b = True"

definition not_identical_type_constructors ::
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'a K \<Rightarrow> 'e L \<Rightarrow> bool"
  where "not_identical_type_constructors R1 R2 a b = True"

definition not_identical_type_constructors_lhs ::
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> 'a K \<Rightarrow> 'b K \<Rightarrow> bool"
  where "not_identical_type_constructors_lhs R1 R2 a b = True"

definition not_identical_type_constructors_rhs ::
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a K \<Rightarrow> 'c K \<Rightarrow> bool"
  where "not_identical_type_constructors_rhs R1 a b = True"



subsection\<open>Test data\<close>

lemma mono_ow_transfer':
  includes lifting_syntax
  assumes [transfer_domain_rule, transfer_rule]: "Domainp B = (\<lambda>x. x \<in> UB)" 
    and [transfer_rule]: "right_total B" 
  shows
    "((A ===> A ===> (=)) ===> (B ===> B ===> (=)) ===> (B ===> A) ===> (=))
      (mono_ow UB) mono.with"
  unfolding mono_ow_def mono.with_def
  by (transfer_prover_start, transfer_step+) simp

ctr_test "mono_with" relativization
  synthesis ctr_simps_Collect_mem_eq
  assumes [transfer_domain_rule, transfer_rule]:
    "Domainp (B::'c\<Rightarrow>'d\<Rightarrow>bool) = (\<lambda>x. x \<in> UB)"
    and [transfer_rule]: "right_total B" 
  trp (?'b \<open>A::'a\<Rightarrow>'b\<Rightarrow>bool\<close>) and (?'a B)
  in mono_ow': mono.with_def 

ctr_test "exI" relativization
  in mono_ow'': exI

ctr_test "binrel" relativization
  synthesis ctr_simps_Collect_mem_eq
  assumes [transfer_domain_rule, transfer_rule]:
    "Domainp (B::'c\<Rightarrow>'d\<Rightarrow>bool) = (\<lambda>x. x \<in> UB)"
    and [transfer_rule]: "right_total B" 
  trp (?'b A) and (?'a B)
  in mono_ow': mono.with_def 

ctr_test "binrel_ftv" relativization
  synthesis ctr_simps_Collect_mem_eq
  assumes [transfer_domain_rule, transfer_rule]:
    "Domainp (B::'c\<Rightarrow>'d\<Rightarrow>bool) = (\<lambda>x. x \<in> UB)"
    and [transfer_rule]: "right_total B" 
  trp (?'b \<open>A::nat\<Rightarrow>'b\<Rightarrow>bool\<close>) and (?'a B)
  in mono_ow': mono.with_def 

ctr_test "dup_stvs" relativization
  synthesis ctr_simps_Collect_mem_eq
  assumes [transfer_domain_rule, transfer_rule]:
    "Domainp (B::'c\<Rightarrow>'d\<Rightarrow>bool) = (\<lambda>x. x \<in> UB)"
    and [transfer_rule]: "right_total B" 
  trp (?'b \<open>A::'a\<Rightarrow>'b\<Rightarrow>bool\<close>) and (?'b B)
  in mono_ow': mono.with_def 

ctr_test "dup_binrel_ftvs" relativization
  synthesis ctr_simps_Collect_mem_eq
  assumes [transfer_domain_rule, transfer_rule]:
    "Domainp (B::'c\<Rightarrow>'d\<Rightarrow>bool) = (\<lambda>x. x \<in> UB)"
    and [transfer_rule]: "right_total B" 
  trp (?'b \<open>A::'a\<Rightarrow>'d\<Rightarrow>bool\<close>) and (?'a B)
  in mono_ow': mono.with_def 

ctr_test "no_relator" relativization
  synthesis ctr_simps_Collect_mem_eq
  assumes [transfer_domain_rule, transfer_rule]:
    "Domainp (B::'c\<Rightarrow>'d\<Rightarrow>bool) = (\<lambda>x. x \<in> UB)"
    and [transfer_rule]: "right_total B" 
  trp (?'b \<open>A::'a\<Rightarrow>'b\<Rightarrow>bool\<close>) and (?'a B) 
  in KK_def

ctr_test "invalid_relator" relativization
  synthesis ctr_simps_Collect_mem_eq
  assumes [transfer_domain_rule, transfer_rule]:
    "Domainp (B::'c\<Rightarrow>'d\<Rightarrow>bool) = (\<lambda>x. x \<in> UB)"
    and [transfer_rule]: "right_total B" 
  trp (?'b \<open>A::'a\<Rightarrow>'b\<Rightarrow>bool\<close>) and (?'a B)
  in LL_def



subsection\<open>Tests\<close>


subsubsection\<open>\<open>process_relativization\<close>\<close>

ML_file\<open>CTR_TEST_PROCESS_RELATIVIZATION.ML\<close>

context
  includes lifting_syntax
begin

ML\<open>
val ctr_test_process_relativization_test_results =
  ctr_test_process_relativization.execute_test_suite_process_relativization
    @{context}
\<close>
ML\<open>
val _ = ctr_test_process_relativization_test_results
  |> UT_Test_Suite.output_test_results true
\<close>

end


subsubsection\<open>\<open>process_ctr_relator\<close>\<close>

ML_file\<open>CTR_TEST_PROCESS_CTR_RELATOR.ML\<close>
ML\<open>
val ctr_test_process_ctr_relator_test_results =
  ctr_test_process_ctr_relator.execute_test_suite_process_ctr_relator
    @{context}
\<close>
ML\<open>
val _ = ctr_test_process_ctr_relator_test_results
  |> UT_Test_Suite.output_test_results true
\<close>

end