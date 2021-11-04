(*
(C) Copyright Andreas Viktor Hess, DTU, 2020
(C) Copyright Sebastian A. Mödersheim, DTU, 2020
(C) Copyright Achim D. Brucker, University of Exeter, 2020
(C) Copyright Anders Schlichtkrull, DTU, 2020

All Rights Reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

- Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

- Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

- Neither the name of the copyright holder nor the names of its
  contributors may be used to endorse or promote products
  derived from this software without specific prior written
  permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(*  Title:      trac_fp_parser.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
*)

section\<open>Parser for Trac FP definitions\<close>
theory
  trac_fp_parser
  imports
    "trac_term"
begin

ML_file "trac_parser/trac_fp.grm.sig"
ML_file "trac_parser/trac_fp.lex.sml"
ML_file "trac_parser/trac_fp.grm.sml"

ML\<open>
structure TracFpParser : sig  
		   val parse_file: string -> (Trac_Term.cMsg) list
       val parse_str: string -> (Trac_Term.cMsg) list
       (* val term_of_trac: Trac_Term.cMsg -> term *)
       val attack: Trac_Term.cMsg list -> bool
end = 
struct

  open Trac_Term

  structure TracLrVals =
    TracLrValsFun(structure Token = LrParser.Token)

  structure TracLex =
    TracLexFun(structure Tokens = TracLrVals.Tokens)

  structure TracParser =
    Join(structure LrParser = LrParser
	 structure ParserData = TracLrVals.ParserData
	 structure Lex = TracLex)
  
  fun invoke lexstream =
      let fun print_error (s,i:(int * int * int),_) =
	      TextIO.output(TextIO.stdOut,
			    "Error, line .... " ^ (Int.toString (#1 i)) ^"."^(Int.toString (#2 i ))^ ", " ^ s ^ "\n")
       in TracParser.parse(0,lexstream,print_error,())
      end

 fun parse_fp lexer =  let
	  val dummyEOF = TracLrVals.Tokens.EOF((0,0,0),(0,0,0))
    fun certify (m,t) = Trac_Term.certifyMsg t [] m 
	  fun loop lexer =
	      let 
		  val _ = (TracLex.UserDeclarations.pos := (0,0,0);())
		  val (res,lexer) = invoke lexer
		  val (nextToken,lexer) = TracParser.Stream.get lexer
	       in if TracParser.sameToken(nextToken,dummyEOF) then ((),res)
		  else loop lexer
	      end
       in  map certify (#2(loop lexer))
      end

 fun parse_file tracFile = let
	     val infile = TextIO.openIn tracFile
	     val lexer = TracParser.makeLexer  (fn _ => case ((TextIO.inputLine) infile) of
                                                   SOME s => s
                                                 | NONE   => "")
     in
       parse_fp lexer
     end

 fun parse_str trac_fp_str = let  
       val parsed = Unsynchronized.ref false 
       fun input_string _  = if !parsed then "" else (parsed := true ;trac_fp_str)
	     val lexer = TracParser.makeLexer input_string
     in
       parse_fp lexer
     end
  fun attack fp = List.exists (fn e => e = cAttack) fp 

(*   fun term_of_trac (Trac_Term.cVar (n,t)) = @{const "cVar"}$(HOLogic.mk_tuple[HOLogic.mk_string n,
                                                                                HOLogic.mk_string t])
    | term_of_trac (Trac_Term.cConst n)   = @{const "cConst"}$HOLogic.mk_string n
    | term_of_trac (Trac_Term.cFun (n,l))   = @{const "cFun"}
                           $(HOLogic.mk_tuple[HOLogic.mk_string n, HOLogic.mk_list @{typ "cMsg"} 
                              (map term_of_trac l)]) *)
end
\<close>


end
