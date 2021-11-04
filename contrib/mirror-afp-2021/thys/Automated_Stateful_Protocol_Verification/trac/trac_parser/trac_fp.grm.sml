 (***** GENERATED FILE -- DO NOT EDIT ****)
functor TracLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : Trac_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct
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

open Trac_Term

exception NotYetSupported of string 



end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\000\000\000\000\
\\001\000\003\000\013\000\009\000\012\000\010\000\011\000\012\000\010\000\
\\013\000\009\000\000\000\
\\001\000\005\000\038\000\000\000\
\\001\000\005\000\047\000\000\000\
\\001\000\007\000\036\000\000\000\
\\001\000\008\000\028\000\012\000\010\000\013\000\009\000\014\000\027\000\
\\015\000\026\000\016\000\025\000\000\000\
\\001\000\008\000\032\000\012\000\010\000\000\000\
\\001\000\009\000\012\000\010\000\011\000\012\000\010\000\013\000\009\000\000\000\
\\001\000\010\000\019\000\000\000\
\\001\000\012\000\010\000\013\000\009\000\000\000\
\\001\000\012\000\010\000\013\000\009\000\017\000\018\000\000\000\
\\001\000\014\000\027\000\015\000\026\000\016\000\025\000\000\000\
\\051\000\000\000\
\\052\000\000\000\
\\053\000\000\000\
\\054\000\009\000\012\000\010\000\011\000\012\000\010\000\013\000\009\000\000\000\
\\055\000\000\000\
\\056\000\000\000\
\\057\000\000\000\
\\058\000\000\000\
\\059\000\000\000\
\\060\000\004\000\015\000\000\000\
\\061\000\004\000\033\000\000\000\
\\062\000\004\000\042\000\000\000\
\\063\000\000\000\
\\064\000\006\000\014\000\000\000\
\\065\000\000\000\
\\066\000\002\000\035\000\000\000\
\\067\000\000\000\
\\068\000\000\000\
\\069\000\000\000\
\\070\000\000\000\
\\071\000\008\000\032\000\012\000\010\000\000\000\
\\072\000\000\000\
\\073\000\000\000\
\\074\000\000\000\
\\075\000\000\000\
\\076\000\000\000\
\\077\000\000\000\
\\078\000\000\000\
\\079\000\000\000\
\\080\000\000\000\
\\081\000\000\000\
\"
val actionRowNumbers =
"\001\000\025\000\024\000\021\000\
\\015\000\014\000\012\000\037\000\
\\036\000\010\000\008\000\007\000\
\\005\000\006\000\016\000\022\000\
\\017\000\009\000\013\000\031\000\
\\027\000\004\000\029\000\041\000\
\\042\000\040\000\011\000\002\000\
\\032\000\018\000\011\000\006\000\
\\023\000\005\000\026\000\030\000\
\\009\000\033\000\003\000\019\000\
\\006\000\028\000\039\000\038\000\
\\035\000\009\000\020\000\034\000\
\\000\000"
val gotoT =
"\
\\001\000\048\000\002\000\006\000\003\000\005\000\004\000\004\000\
\\005\000\003\000\011\000\002\000\012\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\003\000\014\000\004\000\004\000\005\000\003\000\011\000\002\000\
\\012\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\015\000\011\000\002\000\012\000\001\000\000\000\
\\000\000\
\\003\000\018\000\004\000\004\000\005\000\003\000\011\000\002\000\
\\012\000\001\000\000\000\
\\005\000\022\000\006\000\021\000\007\000\020\000\011\000\002\000\
\\012\000\001\000\013\000\019\000\000\000\
\\008\000\029\000\009\000\028\000\011\000\027\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\032\000\011\000\002\000\012\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\013\000\035\000\000\000\
\\000\000\
\\008\000\037\000\009\000\028\000\011\000\027\000\000\000\
\\000\000\
\\013\000\038\000\000\000\
\\008\000\039\000\009\000\028\000\011\000\027\000\000\000\
\\000\000\
\\005\000\022\000\006\000\041\000\007\000\020\000\011\000\002\000\
\\012\000\001\000\013\000\019\000\000\000\
\\000\000\
\\000\000\
\\010\000\044\000\011\000\043\000\012\000\042\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\046\000\009\000\028\000\011\000\027\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\010\000\047\000\011\000\043\000\012\000\042\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 49
val numrules = 31
val s = Unsynchronized.ref "" and index = Unsynchronized.ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle General.Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(List.map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos =  ( int * int * int ) 
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit ->  unit
 | ATTACK of unit ->  (string) | ZERO of unit ->  (string)
 | ONE of unit ->  (string) | INTEGER_LITERAL of unit ->  (string)
 | LOWER_STRING_LITERAL of unit ->  (string)
 | UPPER_STRING_LITERAL of unit ->  (string)
 | STRING_LITERAL of unit ->  (string)
 | DOUBLE_RARROW of unit ->  (string)
 | DOUBLE_ASTERISK of unit ->  (string)
 | ASTERISK of unit ->  (string) | PAREN_CLOSE of unit ->  (string)
 | PAREN_OPEN of unit ->  (string) | COLON of unit ->  (string)
 | WHERE of unit ->  (string) | FIXEDPOINT of unit ->  (string)
 | COMMA of unit ->  (string) | int_literal of unit ->  (string)
 | lower_literal of unit ->  (string)
 | upper_literal of unit ->  (string)
 | string_literal of unit ->  (string)
 | type_exp of unit ->  (TypeDecl)
 | type_list_exp of unit ->  (TypeDecl list)
 | arg_exp of unit ->  (Msg) | arg_list_exp of unit ->  (Msg list)
 | rule_exp of unit ->  (Msg)
 | symfact_exp of unit ->  (Msg*TypeDecl list)
 | symfact_list_exp of unit ->  ( ( Msg * TypeDecl list )  list)
 | trac_file of unit ->  ( ( Msg * TypeDecl list )  list)
 | START of unit ->  ( ( Msg * TypeDecl list )  list)
end
type svalue = MlyValue.svalue
type result =  ( Msg * TypeDecl list )  list
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 0) => true | _ => false
val showTerminal =
fn (T 0) => "EOF"
  | (T 1) => "COMMA"
  | (T 2) => "FIXEDPOINT"
  | (T 3) => "WHERE"
  | (T 4) => "COLON"
  | (T 5) => "PAREN_OPEN"
  | (T 6) => "PAREN_CLOSE"
  | (T 7) => "ASTERISK"
  | (T 8) => "DOUBLE_ASTERISK"
  | (T 9) => "DOUBLE_RARROW"
  | (T 10) => "STRING_LITERAL"
  | (T 11) => "UPPER_STRING_LITERAL"
  | (T 12) => "LOWER_STRING_LITERAL"
  | (T 13) => "INTEGER_LITERAL"
  | (T 14) => "ONE"
  | (T 15) => "ZERO"
  | (T 16) => "ATTACK"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 0)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.trac_file trac_file1, trac_file1left, 
trac_file1right)) :: rest671)) => let val  result = MlyValue.START (fn
 _ => let val  (trac_file as trac_file1) = trac_file1 ()
 in (trac_file)
end)
 in ( LrTable.NT 0, ( result, trac_file1left, trac_file1right), 
rest671)
end
|  ( 1, ( ( _, ( MlyValue.symfact_list_exp symfact_list_exp1, _, 
symfact_list_exp1right)) :: ( _, ( MlyValue.FIXEDPOINT FIXEDPOINT1, 
FIXEDPOINT1left, _)) :: rest671)) => let val  result = 
MlyValue.trac_file (fn _ => let val  FIXEDPOINT1 = FIXEDPOINT1 ()
 val  (symfact_list_exp as symfact_list_exp1) = symfact_list_exp1 ()
 in (symfact_list_exp)
end)
 in ( LrTable.NT 1, ( result, FIXEDPOINT1left, symfact_list_exp1right)
, rest671)
end
|  ( 2, ( ( _, ( MlyValue.symfact_list_exp symfact_list_exp1, 
symfact_list_exp1left, symfact_list_exp1right)) :: rest671)) => let
 val  result = MlyValue.trac_file (fn _ => let val  (symfact_list_exp
 as symfact_list_exp1) = symfact_list_exp1 ()
 in (symfact_list_exp)
end)
 in ( LrTable.NT 1, ( result, symfact_list_exp1left, 
symfact_list_exp1right), rest671)
end
|  ( 3, ( ( _, ( MlyValue.symfact_exp symfact_exp1, symfact_exp1left, 
symfact_exp1right)) :: rest671)) => let val  result = 
MlyValue.symfact_list_exp (fn _ => let val  (symfact_exp as 
symfact_exp1) = symfact_exp1 ()
 in ([symfact_exp])
end)
 in ( LrTable.NT 2, ( result, symfact_exp1left, symfact_exp1right), 
rest671)
end
|  ( 4, ( ( _, ( MlyValue.symfact_list_exp symfact_list_exp1, _, 
symfact_list_exp1right)) :: ( _, ( MlyValue.symfact_exp symfact_exp1, 
symfact_exp1left, _)) :: rest671)) => let val  result = 
MlyValue.symfact_list_exp (fn _ => let val  (symfact_exp as 
symfact_exp1) = symfact_exp1 ()
 val  (symfact_list_exp as symfact_list_exp1) = symfact_list_exp1 ()
 in ([symfact_exp]@symfact_list_exp)
end)
 in ( LrTable.NT 2, ( result, symfact_exp1left, symfact_list_exp1right
), rest671)
end
|  ( 5, ( ( _, ( MlyValue.ATTACK ATTACK1, _, ATTACK1right)) :: ( _, ( 
MlyValue.DOUBLE_RARROW DOUBLE_RARROW1, DOUBLE_RARROW1left, _)) :: 
rest671)) => let val  result = MlyValue.symfact_exp (fn _ => let val  
DOUBLE_RARROW1 = DOUBLE_RARROW1 ()
 val  ATTACK1 = ATTACK1 ()
 in ((Attack,[]))
end)
 in ( LrTable.NT 3, ( result, DOUBLE_RARROW1left, ATTACK1right), 
rest671)
end
|  ( 6, ( ( _, ( MlyValue.type_list_exp type_list_exp1, _, 
type_list_exp1right)) :: ( _, ( MlyValue.WHERE WHERE1, _, _)) :: ( _, 
( MlyValue.rule_exp rule_exp1, rule_exp1left, _)) :: rest671)) => let
 val  result = MlyValue.symfact_exp (fn _ => let val  (rule_exp as 
rule_exp1) = rule_exp1 ()
 val  WHERE1 = WHERE1 ()
 val  (type_list_exp as type_list_exp1) = type_list_exp1 ()
 in ((rule_exp,type_list_exp))
end)
 in ( LrTable.NT 3, ( result, rule_exp1left, type_list_exp1right), 
rest671)
end
|  ( 7, ( ( _, ( MlyValue.type_list_exp type_list_exp1, _, 
type_list_exp1right)) :: ( _, ( MlyValue.WHERE WHERE1, _, _)) :: ( _, 
( MlyValue.rule_exp rule_exp1, _, _)) :: ( _, ( MlyValue.DOUBLE_RARROW
 DOUBLE_RARROW1, DOUBLE_RARROW1left, _)) :: rest671)) => let val  
result = MlyValue.symfact_exp (fn _ => let val  DOUBLE_RARROW1 = 
DOUBLE_RARROW1 ()
 val  (rule_exp as rule_exp1) = rule_exp1 ()
 val  WHERE1 = WHERE1 ()
 val  (type_list_exp as type_list_exp1) = type_list_exp1 ()
 in ((rule_exp,type_list_exp))
end)
 in ( LrTable.NT 3, ( result, DOUBLE_RARROW1left, type_list_exp1right)
, rest671)
end
|  ( 8, ( ( _, ( MlyValue.type_list_exp type_list_exp1, _, 
type_list_exp1right)) :: ( _, ( MlyValue.WHERE WHERE1, _, _)) :: ( _, 
( MlyValue.rule_exp rule_exp1, _, _)) :: ( _, ( MlyValue.DOUBLE_RARROW
 DOUBLE_RARROW1, _, _)) :: ( _, ( MlyValue.DOUBLE_ASTERISK 
DOUBLE_ASTERISK1, DOUBLE_ASTERISK1left, _)) :: rest671)) => let val  
result = MlyValue.symfact_exp (fn _ => let val  DOUBLE_ASTERISK1 = 
DOUBLE_ASTERISK1 ()
 val  DOUBLE_RARROW1 = DOUBLE_RARROW1 ()
 val  (rule_exp as rule_exp1) = rule_exp1 ()
 val  WHERE1 = WHERE1 ()
 val  (type_list_exp as type_list_exp1) = type_list_exp1 ()
 in ((rule_exp,type_list_exp))
end)
 in ( LrTable.NT 3, ( result, DOUBLE_ASTERISK1left, 
type_list_exp1right), rest671)
end
|  ( 9, ( ( _, ( MlyValue.rule_exp rule_exp1, rule_exp1left, 
rule_exp1right)) :: rest671)) => let val  result = 
MlyValue.symfact_exp (fn _ => let val  (rule_exp as rule_exp1) = 
rule_exp1 ()
 in ((rule_exp,[]))
end)
 in ( LrTable.NT 3, ( result, rule_exp1left, rule_exp1right), rest671)

end
|  ( 10, ( ( _, ( MlyValue.rule_exp rule_exp1, _, rule_exp1right)) :: 
( _, ( MlyValue.DOUBLE_RARROW DOUBLE_RARROW1, DOUBLE_RARROW1left, _))
 :: rest671)) => let val  result = MlyValue.symfact_exp (fn _ => let
 val  DOUBLE_RARROW1 = DOUBLE_RARROW1 ()
 val  (rule_exp as rule_exp1) = rule_exp1 ()
 in ((rule_exp,[]))
end)
 in ( LrTable.NT 3, ( result, DOUBLE_RARROW1left, rule_exp1right), 
rest671)
end
|  ( 11, ( ( _, ( MlyValue.rule_exp rule_exp1, _, rule_exp1right)) :: 
( _, ( MlyValue.DOUBLE_RARROW DOUBLE_RARROW1, _, _)) :: ( _, ( 
MlyValue.DOUBLE_ASTERISK DOUBLE_ASTERISK1, DOUBLE_ASTERISK1left, _))
 :: rest671)) => let val  result = MlyValue.symfact_exp (fn _ => let
 val  DOUBLE_ASTERISK1 = DOUBLE_ASTERISK1 ()
 val  DOUBLE_RARROW1 = DOUBLE_RARROW1 ()
 val  (rule_exp as rule_exp1) = rule_exp1 ()
 in ((rule_exp,[]))
end)
 in ( LrTable.NT 3, ( result, DOUBLE_ASTERISK1left, rule_exp1right), 
rest671)
end
|  ( 12, ( ( _, ( MlyValue.upper_literal upper_literal1, 
upper_literal1left, upper_literal1right)) :: rest671)) => let val  
result = MlyValue.rule_exp (fn _ => let val  (upper_literal as 
upper_literal1) = upper_literal1 ()
 in (Var (upper_literal))
end)
 in ( LrTable.NT 4, ( result, upper_literal1left, upper_literal1right)
, rest671)
end
|  ( 13, ( ( _, ( MlyValue.lower_literal lower_literal1, 
lower_literal1left, lower_literal1right)) :: rest671)) => let val  
result = MlyValue.rule_exp (fn _ => let val  (lower_literal as 
lower_literal1) = lower_literal1 ()
 in (Fun (lower_literal,[]))
end)
 in ( LrTable.NT 4, ( result, lower_literal1left, lower_literal1right)
, rest671)
end
|  ( 14, ( ( _, ( MlyValue.PAREN_CLOSE PAREN_CLOSE1, _, 
PAREN_CLOSE1right)) :: ( _, ( MlyValue.arg_list_exp arg_list_exp1, _,
 _)) :: ( _, ( MlyValue.PAREN_OPEN PAREN_OPEN1, _, _)) :: ( _, ( 
MlyValue.lower_literal lower_literal1, lower_literal1left, _)) :: 
rest671)) => let val  result = MlyValue.rule_exp (fn _ => let val  (
lower_literal as lower_literal1) = lower_literal1 ()
 val  PAREN_OPEN1 = PAREN_OPEN1 ()
 val  (arg_list_exp as arg_list_exp1) = arg_list_exp1 ()
 val  PAREN_CLOSE1 = PAREN_CLOSE1 ()
 in (Fun (lower_literal,arg_list_exp))
end)
 in ( LrTable.NT 4, ( result, lower_literal1left, PAREN_CLOSE1right), 
rest671)
end
|  ( 15, ( ( _, ( MlyValue.arg_exp arg_exp1, arg_exp1left, 
arg_exp1right)) :: rest671)) => let val  result = 
MlyValue.arg_list_exp (fn _ => let val  (arg_exp as arg_exp1) = 
arg_exp1 ()
 in ([arg_exp])
end)
 in ( LrTable.NT 5, ( result, arg_exp1left, arg_exp1right), rest671)

end
|  ( 16, ( ( _, ( MlyValue.arg_list_exp arg_list_exp1, _, 
arg_list_exp1right)) :: ( _, ( MlyValue.COMMA COMMA1, _, _)) :: ( _, (
 MlyValue.arg_exp arg_exp1, arg_exp1left, _)) :: rest671)) => let val 
 result = MlyValue.arg_list_exp (fn _ => let val  (arg_exp as arg_exp1
) = arg_exp1 ()
 val  COMMA1 = COMMA1 ()
 val  (arg_list_exp as arg_list_exp1) = arg_list_exp1 ()
 in ([arg_exp]@arg_list_exp)
end)
 in ( LrTable.NT 5, ( result, arg_exp1left, arg_list_exp1right), 
rest671)
end
|  ( 17, ( ( _, ( MlyValue.rule_exp rule_exp1, rule_exp1left, 
rule_exp1right)) :: rest671)) => let val  result = MlyValue.arg_exp
 (fn _ => let val  (rule_exp as rule_exp1) = rule_exp1 ()
 in (rule_exp)
end)
 in ( LrTable.NT 6, ( result, rule_exp1left, rule_exp1right), rest671)

end
|  ( 18, ( ( _, ( MlyValue.int_literal int_literal1, _, 
int_literal1right)) :: ( _, ( MlyValue.ASTERISK ASTERISK1, 
ASTERISK1left, _)) :: rest671)) => let val  result = MlyValue.arg_exp
 (fn _ => let val  ASTERISK1 = ASTERISK1 ()
 val  (int_literal as int_literal1) = int_literal1 ()
 in (Var (int_literal))
end)
 in ( LrTable.NT 6, ( result, ASTERISK1left, int_literal1right), 
rest671)
end
|  ( 19, ( ( _, ( MlyValue.int_literal int_literal1, int_literal1left,
 int_literal1right)) :: rest671)) => let val  result = 
MlyValue.arg_exp (fn _ => let val  (int_literal as int_literal1) = 
int_literal1 ()
 in (Const (int_literal))
end)
 in ( LrTable.NT 6, ( result, int_literal1left, int_literal1right), 
rest671)
end
|  ( 20, ( ( _, ( MlyValue.type_exp type_exp1, type_exp1left, 
type_exp1right)) :: rest671)) => let val  result = 
MlyValue.type_list_exp (fn _ => let val  (type_exp as type_exp1) = 
type_exp1 ()
 in ([type_exp])
end)
 in ( LrTable.NT 7, ( result, type_exp1left, type_exp1right), rest671)

end
|  ( 21, ( ( _, ( MlyValue.type_list_exp type_list_exp1, _, 
type_list_exp1right)) :: ( _, ( MlyValue.type_exp type_exp1, 
type_exp1left, _)) :: rest671)) => let val  result = 
MlyValue.type_list_exp (fn _ => let val  (type_exp as type_exp1) = 
type_exp1 ()
 val  (type_list_exp as type_list_exp1) = type_list_exp1 ()
 in ([type_exp]@type_list_exp)
end)
 in ( LrTable.NT 7, ( result, type_exp1left, type_list_exp1right), 
rest671)
end
|  ( 22, ( ( _, ( MlyValue.string_literal string_literal1, _, 
string_literal1right)) :: ( _, ( MlyValue.COLON COLON1, _, _)) :: ( _,
 ( MlyValue.int_literal int_literal1, _, _)) :: ( _, ( 
MlyValue.ASTERISK ASTERISK1, ASTERISK1left, _)) :: rest671)) => let
 val  result = MlyValue.type_exp (fn _ => let val  ASTERISK1 = 
ASTERISK1 ()
 val  (int_literal as int_literal1) = int_literal1 ()
 val  COLON1 = COLON1 ()
 val  (string_literal as string_literal1) = string_literal1 ()
 in ((int_literal,string_literal))
end)
 in ( LrTable.NT 8, ( result, ASTERISK1left, string_literal1right), 
rest671)
end
|  ( 23, ( ( _, ( MlyValue.string_literal string_literal1, _, 
string_literal1right)) :: ( _, ( MlyValue.COLON COLON1, _, _)) :: ( _,
 ( MlyValue.upper_literal upper_literal1, upper_literal1left, _)) :: 
rest671)) => let val  result = MlyValue.type_exp (fn _ => let val  (
upper_literal as upper_literal1) = upper_literal1 ()
 val  COLON1 = COLON1 ()
 val  (string_literal as string_literal1) = string_literal1 ()
 in ((upper_literal,string_literal))
end)
 in ( LrTable.NT 8, ( result, upper_literal1left, string_literal1right
), rest671)
end
|  ( 24, ( ( _, ( MlyValue.UPPER_STRING_LITERAL UPPER_STRING_LITERAL1,
 UPPER_STRING_LITERAL1left, UPPER_STRING_LITERAL1right)) :: rest671))
 => let val  result = MlyValue.upper_literal (fn _ => let val  (
UPPER_STRING_LITERAL as UPPER_STRING_LITERAL1) = UPPER_STRING_LITERAL1
 ()
 in (UPPER_STRING_LITERAL)
end)
 in ( LrTable.NT 10, ( result, UPPER_STRING_LITERAL1left, 
UPPER_STRING_LITERAL1right), rest671)
end
|  ( 25, ( ( _, ( MlyValue.LOWER_STRING_LITERAL LOWER_STRING_LITERAL1,
 LOWER_STRING_LITERAL1left, LOWER_STRING_LITERAL1right)) :: rest671))
 => let val  result = MlyValue.lower_literal (fn _ => let val  (
LOWER_STRING_LITERAL as LOWER_STRING_LITERAL1) = LOWER_STRING_LITERAL1
 ()
 in (LOWER_STRING_LITERAL)
end)
 in ( LrTable.NT 11, ( result, LOWER_STRING_LITERAL1left, 
LOWER_STRING_LITERAL1right), rest671)
end
|  ( 26, ( ( _, ( MlyValue.upper_literal upper_literal1, 
upper_literal1left, upper_literal1right)) :: rest671)) => let val  
result = MlyValue.string_literal (fn _ => let val  (upper_literal as 
upper_literal1) = upper_literal1 ()
 in (upper_literal)
end)
 in ( LrTable.NT 9, ( result, upper_literal1left, upper_literal1right)
, rest671)
end
|  ( 27, ( ( _, ( MlyValue.lower_literal lower_literal1, 
lower_literal1left, lower_literal1right)) :: rest671)) => let val  
result = MlyValue.string_literal (fn _ => let val  (lower_literal as 
lower_literal1) = lower_literal1 ()
 in (lower_literal)
end)
 in ( LrTable.NT 9, ( result, lower_literal1left, lower_literal1right)
, rest671)
end
|  ( 28, ( ( _, ( MlyValue.INTEGER_LITERAL INTEGER_LITERAL1, 
INTEGER_LITERAL1left, INTEGER_LITERAL1right)) :: rest671)) => let val 
 result = MlyValue.int_literal (fn _ => let val  (INTEGER_LITERAL as 
INTEGER_LITERAL1) = INTEGER_LITERAL1 ()
 in (INTEGER_LITERAL)
end)
 in ( LrTable.NT 12, ( result, INTEGER_LITERAL1left, 
INTEGER_LITERAL1right), rest671)
end
|  ( 29, ( ( _, ( MlyValue.ZERO ZERO1, ZERO1left, ZERO1right)) :: 
rest671)) => let val  result = MlyValue.int_literal (fn _ => let val  
ZERO1 = ZERO1 ()
 in ("0")
end)
 in ( LrTable.NT 12, ( result, ZERO1left, ZERO1right), rest671)
end
|  ( 30, ( ( _, ( MlyValue.ONE ONE1, ONE1left, ONE1right)) :: rest671)
) => let val  result = MlyValue.int_literal (fn _ => let val  ONE1 = 
ONE1 ()
 in ("1")
end)
 in ( LrTable.NT 12, ( result, ONE1left, ONE1right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.START x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : Trac_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun COMMA (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.COMMA (fn () => i),p1,p2))
fun FIXEDPOINT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.FIXEDPOINT (fn () => i),p1,p2))
fun WHERE (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.WHERE (fn () => i),p1,p2))
fun COLON (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.COLON (fn () => i),p1,p2))
fun PAREN_OPEN (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.PAREN_OPEN (fn () => i),p1,p2))
fun PAREN_CLOSE (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.PAREN_CLOSE (fn () => i),p1,p2))
fun ASTERISK (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.ASTERISK (fn () => i),p1,p2))
fun DOUBLE_ASTERISK (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.DOUBLE_ASTERISK (fn () => i),p1,p2))
fun DOUBLE_RARROW (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.DOUBLE_RARROW (fn () => i),p1,p2))
fun STRING_LITERAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.STRING_LITERAL (fn () => i),p1,p2))
fun UPPER_STRING_LITERAL (i,p1,p2) = Token.TOKEN (
ParserData.LrTable.T 11,(ParserData.MlyValue.UPPER_STRING_LITERAL
 (fn () => i),p1,p2))
fun LOWER_STRING_LITERAL (i,p1,p2) = Token.TOKEN (
ParserData.LrTable.T 12,(ParserData.MlyValue.LOWER_STRING_LITERAL
 (fn () => i),p1,p2))
fun INTEGER_LITERAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.INTEGER_LITERAL (fn () => i),p1,p2))
fun ONE (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.ONE (fn () => i),p1,p2))
fun ZERO (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.ZERO (fn () => i),p1,p2))
fun ATTACK (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.ATTACK (fn () => i),p1,p2))
end
end
