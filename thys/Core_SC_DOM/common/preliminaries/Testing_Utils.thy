(***********************************************************************************
 * Copyright (c) 2016-2018 The University of Sheffield, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

theory Testing_Utils
  imports Main
begin
ML \<open>
val _ = Theory.setup 
  (Method.setup @{binding timed_code_simp}
    (Scan.succeed (SIMPLE_METHOD' o (CHANGED_PROP oo (fn a => fn b => fn tac =>
      let 
        val start = Time.now ();
        val result = Code_Simp.dynamic_tac a b tac;
        val t = Time.now() - start;
      in
        (if length (Seq.list_of result) > 0 then Output.information ("Took " ^ (Time.toString t)) else ());
        result
      end))))
    "timed simplification with code equations");

val _ = Theory.setup
  (Method.setup @{binding timed_eval}
    (Scan.succeed (SIMPLE_METHOD' o (fn a => fn b => fn tac =>
      let
        val eval = CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1 (Code_Runtime.dynamic_holds_conv a))) a) THEN'
          resolve_tac a [TrueI];
        val start = Time.now ();
        val result = eval b tac
        val t = Time.now() - start;
      in
        (if length (Seq.list_of result) > 0 then Output.information ("Took " ^ (Time.toString t)) else ());
        result
      end)))
    "timed evaluation");

val _ = Theory.setup
  (Method.setup @{binding timed_eval_and_code_simp}
    (Scan.succeed (SIMPLE_METHOD' o (fn a => fn b => fn tac =>
      let
        val eval = CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1 (Code_Runtime.dynamic_holds_conv a))) a) THEN'
          resolve_tac a [TrueI];
        val start = Time.now ();
        val result = eval b tac
        val t = Time.now() - start;

        val start2 = Time.now ();
        val result2_opt =
          Timeout.apply (seconds 600.0) (fn _ => SOME (Code_Simp.dynamic_tac a b tac)) ()
          handle Timeout.TIMEOUT _ => NONE;
        val t2 = Time.now() - start2;
      in
        if length (Seq.list_of result) > 0 then (Output.information ("eval took " ^ (Time.toString t));
File.append (Path.explode "/tmp/isabellebench") (Time.toString t ^ ",")) else ();
        (case result2_opt of
          SOME result2 => 
            (if length (Seq.list_of result2) > 0 then (Output.information ("code_simp took " ^ (Time.toString t2));
File.append (Path.explode "/tmp/isabellebench") (Time.toString t2 ^ "\n")) else ())
        | NONE => (Output.information "code_simp timed out after 600s"; File.append (Path.explode "/tmp/isabellebench") (">600.000\n")));
        result
      end)))
    "timed evaluation and simplification with code equations with file output");
\<close>

(* To run the DOM test cases with timing information output, simply replace the use *)
(* of "eval" with either "timed_code_simp", "timed_eval", or, to run both and write the results *)
(* to /tmp/isabellebench, "timed_eval_and_code_simp". *)

end
