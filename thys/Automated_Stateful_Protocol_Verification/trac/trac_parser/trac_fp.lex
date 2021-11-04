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

structure Tokens = Tokens
open Trac_Term
  
type pos = int * int * int
type svalue = Tokens.svalue

type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token


val pos = ref (0,0,0)

  fun eof () = Tokens.EOF((!pos,!pos))
  fun error (e,p : (int * int * int),_) = TextIO.output (TextIO.stdOut, 
							 String.concat[
								       "line ", (Int.toString (#1 p)), "/",
								       (Int.toString (#2 p - #3 p)),": ", e, "\n"
								       ])
  
 fun inputPos yypos = ((#1 (!pos), yypos - (#3(!pos)), (#3 (!pos))),
		     (#1 (!pos), yypos - (#3(!pos)), (#3 (!pos)))) 
 fun inputPos_half yypos = (#1 (!pos), yypos - (#3(!pos)), (#3 (!pos)))



%%
%header (functor TracLexFun(structure Tokens: Trac_TOKENS));
alpha=[A-Za-z_];
upper=[A-Z];
lower=[a-z];
digit=[0-9];
ws = [\ \t];
%%

\n       => (pos := ((#1 (!pos)) + 1, yypos - (#3(!pos)),yypos  ); lex());
{ws}+    => (pos := (#1 (!pos), yypos - (#3(!pos)), (#3 (!pos))); lex()); 

(#)[^\n]*\n                    => (pos := ((#1 (!pos)) + 1, yypos - (#3(!pos)),yypos  ); lex());

"/*""/"*([^*/]|[^*]"/"|"*"[^/])*"*"*"*/" => (lex());


","          => (Tokens.COMMA(yytext,inputPos_half yypos,inputPos_half yypos));
"Fixedpoint" => (Tokens.FIXEDPOINT(yytext,inputPos_half yypos,inputPos_half yypos));
"where"      => (Tokens.WHERE(yytext,inputPos_half yypos,inputPos_half yypos));
":"          => (Tokens.COLON(yytext,inputPos_half yypos,inputPos_half yypos));
"("          => (Tokens.PAREN_OPEN(yytext,inputPos_half yypos,inputPos_half yypos));
")"          => (Tokens.PAREN_CLOSE(yytext,inputPos_half yypos,inputPos_half yypos));
"**"         => (Tokens.DOUBLE_ASTERISK(yytext,inputPos_half yypos,inputPos_half yypos));
"*"          => (Tokens.ASTERISK(yytext,inputPos_half yypos,inputPos_half yypos));
"=>"         => (Tokens.DOUBLE_RARROW(yytext,inputPos_half yypos,inputPos_half yypos));
"one"        => (Tokens.ONE(yytext,inputPos_half yypos,inputPos_half yypos));
"zero"       => (Tokens.ZERO(yytext,inputPos_half yypos,inputPos_half yypos));
"attack"       => (Tokens.ATTACK(yytext,inputPos_half yypos,inputPos_half yypos));


{digit}+                          => (Tokens.INTEGER_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));
"'"({alpha}|{ws}|{digit})*(("."|"_"|"/"|"-")*({alpha}|{ws}|{digit})*)*"'"  => (Tokens.STRING_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));
{upper}({alpha}|{digit})*("'")*   => (Tokens.UPPER_STRING_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));
{lower}({alpha}|{digit})*("'")*   => (Tokens.LOWER_STRING_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));


.      => (error ("ignoring bad character "^yytext,
		    ((#1 (!pos), yypos - (#3(!pos)), (#3 (!pos)))),
		    ((#1 (!pos), yypos - (#3(!pos)), (#3 (!pos)))));
             lex());
