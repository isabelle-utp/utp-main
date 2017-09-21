(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Topology.thy                                                         *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)

section {* Railway Topology *}

theory Topology
imports Main
begin

subsection {* Permissible Routes *}

text \<open>Available routes and their corresponding relay index.\<close>

abbreviation (input) "V1Q1 \<equiv> 1"
abbreviation (input) "V1Q2 \<equiv> 2"
abbreviation (input) "Q2V2 \<equiv> 3"
abbreviation (input) "V1Q3 \<equiv> 4"
abbreviation (input) "Q3V2 \<equiv> 5"

type_synonym path = "int list"

definition void :: "'a" where
"void = undefined"

definition routes :: "path list" where
"routes = [void,
  [3, 4, 5],
  [3, 4, 12, 8, 9, 10, 1],
  [1, 10, 9, 8, 7, 6],
  [3, 4, 12, 8, 9, 11, 2],
  [2, 11, 9, 8, 7, 6]
]"

(*
primrec trains_on_path :: "ilock_state \<Rightarrow> path \<Rightarrow> nat" where
"trains_on_path ilock [] = 0" |
"trains_on_path ilock (x # t) =
  (if (cdv ilock)\<^bold>[x\<^bold>] then 0 else 1) + (trains_on_path ilock t)"

definition path_is_safe :: "ilock_state \<Rightarrow> path \<Rightarrow> bool" where
"path_is_safe ilock path \<longleftrightarrow> trains_on_path ilock path \<le> 1"

definition all_paths_safe :: "ilock_state \<Rightarrow> bool" where
"all_paths_safe ilock \<longleftrightarrow> (list_all (\<lambda>path. path_is_safe ilock path) paths)"
*)
end