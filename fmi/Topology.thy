(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Topology.thy                                                         *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Oct 2017 *)

section {* Railway Topology *}

theory Topology
imports Main Vector
begin

consts void :: "'a"

subsection {* Type Definitions *}

text \<open>Possible alignments of railway switches.\<close>

datatype switch =
  STRAIGHT |
  DIVERGING

text \<open>Possible states of the interlocking relays.\<close>

abbreviation (input) "ON  \<equiv> True"
abbreviation (input) "OFF \<equiv> False"

subsection {* Track Layout *}

definition NextTrackQV :: "switch vector \<Rightarrow> int \<Rightarrow> int" where
"NextTrackQV sw = undefined (
   1 := 10,
   2 := 11,
   3 := 0,
   4 := if sw\<^bold>[1\<^bold>] = STRAIGHT then 3 else 13,
   5 := if sw\<^bold>[3\<^bold>] = STRAIGHT then 4 else -1,
   6 := 0,
   7 := if sw\<^bold>[4\<^bold>] = STRAIGHT then 6 else -1,
   8 := if sw\<^bold>[2\<^bold>] = STRAIGHT then 7 else 12,
   9 := 8,
   10 := if sw\<^bold>[5\<^bold>] = STRAIGHT then 9  else -1,
   11 := if sw\<^bold>[5\<^bold>] = DIVERGING then 9 else -1,
   12 := if sw\<^bold>[3\<^bold>] = DIVERGING then 4 else -1,
   13 := if sw\<^bold>[4\<^bold>] = DIVERGING then 6 else -1
)"

definition NextTrackVQ :: "switch vector \<Rightarrow> int \<Rightarrow> int" where
"NextTrackVQ sw = undefined (
   1 := 0,
   2 := 0,
   3 := if sw\<^bold>[1\<^bold>] = STRAIGHT then 4 else -1,
   4 := if sw\<^bold>[3\<^bold>] = STRAIGHT then 5 else 12,
   5 := 0,
   6 := if sw\<^bold>[4\<^bold>] = STRAIGHT then 7 else 13,
   7 := if sw\<^bold>[2\<^bold>] = STRAIGHT then 8 else -1,
   8 := 9,
   9 := if sw\<^bold>[5\<^bold>] = STRAIGHT then 10 else 11,
   10 := 1,
   11 := 2,
   12 := if sw\<^bold>[2\<^bold>] = DIVERGING then 8 else -1,
   13 := if sw\<^bold>[1\<^bold>] = DIVERGING then 4 else -1
)"

subsection {* Permissible Routes *}

text \<open>Available routes and their corresponding relay index.\<close>

abbreviation (input) "V1Q1 \<equiv> (1::nat)"
abbreviation (input) "V1Q2 \<equiv> (2::nat)"
abbreviation (input) "Q2V2 \<equiv> (3::nat)"
abbreviation (input) "V1Q3 \<equiv> (4::nat)"
abbreviation (input) "Q3V2 \<equiv> (5::nat)"

abbreviation (input) "ROUTES \<equiv> {V1Q1, V1Q2, Q2V2, V1Q3, Q3V2}"

datatype direction = QtoV | VtoQ

definition directions :: "direction list" where
"directions = [void, VtoQ, VtoQ, QtoV, VtoQ, QtoV]"

type_synonym path = "int list"

definition routes :: "path list" where
"routes = [void, (* So that we can used one-based indices *)
  [3, 4, 5],
  [3, 4, 12, 8, 9, 10, 1],
  [1, 10, 9, 8, 7, 6],
  [3, 4, 12, 8, 9, 11, 2],
  [2, 11, 9, 8, 7, 6]]"

abbreviation routes_tl :: "path list" where
"routes_tl \<equiv> map tl routes"

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