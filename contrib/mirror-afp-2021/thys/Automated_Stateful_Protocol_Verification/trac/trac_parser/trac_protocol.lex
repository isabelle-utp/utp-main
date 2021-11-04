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
open TracProtocol
  
type pos = int * int * int
type svalue = Tokens.svalue

type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token


val pos = ref (0,0,0)

  fun eof () = Tokens.EOF((!pos,!pos))
  fun error (e,p : (int * int * int),_) = TextIO.output (TextIO.stdOut, 
							 String.concat[
								       "Line ", (Int.toString (#1 p)), "/",
								       (Int.toString (#2 p - #3 p)),": ", e, "\n"
								       ])
  
 fun inputPos yypos = ((#1 (!pos), yypos - (#3(!pos)), (#3 (!pos))),
		     (#1 (!pos), yypos - (#3(!pos)), (#3 (!pos)))) 
 fun inputPos_half yypos = (#1 (!pos), yypos - (#3(!pos)), (#3 (!pos)))



%%
%header (functor TracTransactionLexFun(structure Tokens: TracTransaction_TOKENS));
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

"("             => (Tokens.OPENP(yytext,inputPos_half yypos,inputPos_half yypos));
")"             => (Tokens.CLOSEP(yytext,inputPos_half yypos,inputPos_half yypos));
"{"             => (Tokens.OPENB(yytext,inputPos_half yypos,inputPos_half yypos));
"}"             => (Tokens.CLOSEB(yytext,inputPos_half yypos,inputPos_half yypos));
"{|"            => (Tokens.OPENSCRYPT(yytext,inputPos_half yypos,inputPos_half yypos));
"|}"            => (Tokens.CLOSESCRYPT(yytext,inputPos_half yypos,inputPos_half yypos));
":"             => (Tokens.COLON(yytext,inputPos_half yypos,inputPos_half yypos));
";"             => (Tokens.SEMICOLON(yytext,inputPos_half yypos,inputPos_half yypos));
"->"            => (Tokens.ARROW(yytext,inputPos_half yypos,inputPos_half yypos));
"%"             => (Tokens.PERCENT(yytext,inputPos_half yypos,inputPos_half yypos));
"!="            => (Tokens.UNEQUAL(yytext,inputPos_half yypos,inputPos_half yypos));
"!"             => (Tokens.EXCLAM (yytext,inputPos_half yypos,inputPos_half yypos));
"."             => (Tokens.DOT(yytext,inputPos_half yypos,inputPos_half yypos));
","             => (Tokens.COMMA(yytext,inputPos_half yypos,inputPos_half yypos));
"["             => (Tokens.OPENSQB(yytext,inputPos_half yypos,inputPos_half yypos));
"]"             => (Tokens.CLOSESQB(yytext,inputPos_half yypos,inputPos_half yypos));
"++"            => (Tokens.UNION(yytext,inputPos_half yypos,inputPos_half yypos));
"Protocol"      => (Tokens.PROTOCOL(yytext,inputPos_half yypos,inputPos_half yypos));
"Knowledge"     => (Tokens.KNOWLEDGE(yytext,inputPos_half yypos,inputPos_half yypos));
"where"         => (Tokens.WHERE(yytext,inputPos_half yypos,inputPos_half yypos));
"Types"         => (Tokens.TYPES(yytext,inputPos_half yypos,inputPos_half yypos));
"Actions"       => (Tokens.ACTIONS(yytext,inputPos_half yypos,inputPos_half yypos));
"Abstraction"   => (Tokens.ABSTRACTION(yytext,inputPos_half yypos,inputPos_half yypos));
"Goals"         => (Tokens.GOALS(yytext,inputPos_half yypos,inputPos_half yypos));
"authenticates" => (Tokens.AUTHENTICATES(yytext,inputPos_half yypos,inputPos_half yypos));
"weakly"        => (Tokens.WEAKLY(yytext,inputPos_half yypos,inputPos_half yypos));
"on"            => (Tokens.ON(yytext,inputPos_half yypos,inputPos_half yypos));
"secret"        => (Tokens.TSECRET(yytext,inputPos_half yypos,inputPos_half yypos));
"between"       => (Tokens.TBETWEEN(yytext,inputPos_half yypos,inputPos_half yypos));
"Sets"          => (Tokens.SETS(yytext,inputPos_half yypos,inputPos_half yypos));
"Functions"     => (Tokens.FUNCTIONS(yytext,inputPos_half yypos,inputPos_half yypos));
"Public"        => (Tokens.PUBLIC(yytext,inputPos_half yypos,inputPos_half yypos));
"Private"       => (Tokens.PRIVATE(yytext,inputPos_half yypos,inputPos_half yypos));
"Analysis"      => (Tokens.ANALYSIS(yytext,inputPos_half yypos,inputPos_half yypos));
"Transactions"  => (Tokens.TRANSACTIONS(yytext,inputPos_half yypos,inputPos_half yypos));
"receive"       => (Tokens.RECEIVE(yytext,inputPos_half yypos,inputPos_half yypos));
"send"          => (Tokens.SEND(yytext,inputPos_half yypos,inputPos_half yypos));
"in"            => (Tokens.IN(yytext,inputPos_half yypos,inputPos_half yypos));
"notin"         => (Tokens.NOTIN(yytext,inputPos_half yypos,inputPos_half yypos));
"insert"        => (Tokens.INSERT(yytext,inputPos_half yypos,inputPos_half yypos));
"delete"        => (Tokens.DELETE(yytext,inputPos_half yypos,inputPos_half yypos));
"new"           => (Tokens.NEW(yytext,inputPos_half yypos,inputPos_half yypos));
"attack"        => (Tokens.ATTACK(yytext,inputPos_half yypos,inputPos_half yypos));
"/"             => (Tokens.slash(yytext,inputPos_half yypos,inputPos_half yypos));
"?"             => (Tokens.QUESTION(yytext,inputPos_half yypos,inputPos_half yypos));
"="             => (Tokens.equal(yytext,inputPos_half yypos,inputPos_half yypos));
"_"             => (Tokens.UNDERSCORE(yytext,inputPos_half yypos,inputPos_half yypos));
"*"             => (Tokens.STAR(yytext,inputPos_half yypos,inputPos_half yypos));
"of"           => (Tokens.OF(yytext,inputPos_half yypos,inputPos_half yypos));


{digit}+                          => (Tokens.INTEGER_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));
"'"({alpha}|{ws}|{digit})*(("."|"_"|"/"|"-")*({alpha}|{ws}|{digit})*)*"'"  => (Tokens.STRING_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));
{lower}({alpha}|{digit})*("'")*   => (Tokens.LOWER_STRING_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));
{upper}({alpha}|{digit})*("'")*   => (Tokens.UPPER_STRING_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));


.      => (error ("ignoring bad character "^yytext,
		    ((#1 (!pos), yypos - (#3(!pos)), (#3 (!pos)))),
		    ((#1 (!pos), yypos - (#3(!pos)), (#3 (!pos)))));
             lex());
