(******************************************************************************)
(* External Algorithm for Calculating the Transitive Closure in Isabelle/HOL  *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(* Email: frank.zeyda@york.ac.uk                                              *)
(******************************************************************************)

section {* Transcl Tests *}

theory transcl_tests
imports transcl
begin

(* Tool Invocation Test *)

ML \<open>
  val input = "{(A, B), (B, C), (A, D), (B, E)}";
  val result = Transcl.transcl_run @{context} input "";
  val Transcl.Data data = result;
  val (ginit, gfini) = Transcl.parse_rel_data data;
\<close>

(* Reconstruction Tests *)

ML \<open>
  val term = @{term "{(A, B), (B, C), (A, D), (B, E)}"};
  val r1  = Transcl.transcl1 @{context} term;
  val r2 = Transcl.transcl2 @{context} @{term "{(A, B), (B, C)}"};
  val r3 = Transcl.transcl2 @{context} @{term "{(1, 2), (2, 3)}"};
\<close>

ML \<open>
  val _ = Output.writeln (Syntax.string_of_term @{context} term);
  val _ = Output.writeln (Syntax.string_of_term @{context} r1);
  val _ = Output.writeln (Syntax.string_of_term @{context} r2);
  (* Does not give the expected result as the relation is non-homogeneous. *)
  val _ = Output.writeln (Syntax.string_of_term @{context} r3);
\<close>

definition myrel1:
"myrel1 = {(''A'', ''B''), (''B'', ''C''), (''A'', ''D''), (''B'', ''E'')}"

definition myrel2:
"myrel2 = {(''D'', ''A'')}"

definition myrel3:
"myrel3 = {(1, 2), (2, 3), (1, 4), (2, 5)}"

(* PreSimplifier Tests *)

ML \<open>
  val _ = Output.writeln
    (Syntax.string_of_term @{context}
      (PreSimplifier.presimplify @{context}
        Transcl_Rewriter.is_rel_const @{term "myrel1 \<union> myrel2"}));

  val _ = Output.writeln
    (Syntax.string_of_term @{context}
      (PreSimplifier.presimplify @{context}
        Transcl_Rewriter.is_rel_const @{term "myrel3"}));
\<close>

value "myrel1 \<union> myrel2"

value "myrel3" -- {* In contrast, this does not give us quite what we want! *}

(* Miscellaneous Experiments *)

find_theorems name:"Set." name:"insert"

lemma "TRUE (myrel1 \<union> myrel2)"
apply (unfold myrel1 myrel2)
apply (simp only: Set.Un_insert_left Set.Un_empty_left)
oops

hide_const myrel1 myrel2 myrel3
end