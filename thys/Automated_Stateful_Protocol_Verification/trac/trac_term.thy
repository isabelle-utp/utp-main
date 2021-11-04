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

(*  Title:      trac_term.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
*)

section \<open>Abstract Syntax for Trac Terms\<close>
theory
  trac_term
  imports
    "First_Order_Terms.Term"
    "ml_yacc_lib"
    (* Alternatively (provides, as a side-effect,  ml-yacc-lib):
      "HOL-TPTP.TPTP_Parser" 
    *)
begin
datatype cMsg = cVar "string * string"
              | cConst string
              | cFun "string * cMsg list"

ML\<open>
structure Trac_Utils = 
struct
  
  fun list_find p ts =
    let
      fun aux _ [] = NONE
        | aux n (t::ts) =
            if p t
            then SOME (t,n)
            else aux (n+1) ts
    in
      aux 0 ts
    end
  
  fun map_prod f (a,b) = (f a, f b)
  
  
  
  fun list_product [] = [[]]
    | list_product (xs::xss) =
        List.concat (map (fn x => map (fn ys => x::ys) (list_product xss)) xs)
  
  fun list_toString elem_toString xs =
    let
      fun aux [] = ""
        | aux [x] = elem_toString x
        | aux (x::y::xs) = elem_toString x ^ ", " ^ aux (y::xs)
    in
      "[" ^ aux xs ^ "]"
    end
  
  val list_to_str = list_toString (fn x => x)
  
  fun list_triangle_product _ [] = []
    | list_triangle_product f (x::xs) = map (f x) xs@list_triangle_product f xs
  
  fun list_subseqs [] = [[]]
    | list_subseqs (x::xs) = let val xss = list_subseqs xs in map (cons x) xss@xss end
  
  fun list_intersect xs ys =
      List.exists (fn x => member (op =) ys x) xs orelse
      List.exists (fn y => member (op =) xs y) ys
  
  fun list_partitions xs constrs =
    let
      val peq = eq_set (op =)
      val pseq = eq_set peq
      val psseq = eq_set pseq
  
      fun illegal p q =
        let
          val pq = union (op =) p q
          fun f (a,b) = member (op =) pq a andalso member (op =) pq b
        in
          List.exists f constrs
        end
  
      fun merges _ [] = []
        | merges q (p::ps) =
            if illegal p q then map (cons p) (merges q ps)
            else (union (op =) p q::ps)::(map (cons p) (merges q ps))
  
      fun merges_all [] = []
        | merges_all (p::ps) = merges p ps@map (cons p) (merges_all ps)
  
      fun step pss = fold (union pseq) (map merges_all pss) []
  
      fun loop pss pssprev =
        let val pss' = step pss
        in if psseq (pss,pss') then pssprev else loop pss' (union pseq pss' pssprev)
        end
  
      val init = [map single xs]
    in
      loop init init
    end
  
  fun mk_unique  [] = []
    | mk_unique (x::xs) = x::mk_unique(List.filter (fn y => y <> x) xs)
  
  fun list_rm_pair sel l x = filter (fn e => sel e <> x) l
  
  fun list_minus list_rm l m = List.foldl (fn (a,b) => list_rm b a) l m

  fun list_upto n =
    let
      fun aux m = if m >= n then [] else m::aux (m+1)
    in
      aux 0
    end
end
\<close>

ML\<open>
structure Trac_Term (* : TRAC_TERM *) =
struct
open Trac_Utils
exception TypeError

type TypeDecl = string * string

datatype Msg = Var of string
             | Const of string
             | Fun of string * Msg list
             | Attack

datatype VarType = EnumType of string
                 | ValueType
                 | Untyped

datatype cMsg = cVar of string * VarType
              | cConst of string
              | cFun of string * cMsg list
              | cAttack
              | cSet of string * cMsg list
              | cAbs of (string * string list) list
              | cOccursFact of cMsg
              | cPrivFunSec
              | cEnum of string

fun type_of et vt n =
  case List.find (fn (v,_) => v = n) et of
    SOME (_,t) => EnumType t
  | NONE =>
      if List.exists (fn v => v = n) vt
      then ValueType
      else Untyped

fun certifyMsg et vt (Var n)       = cVar (n, type_of et vt n)
  | certifyMsg _  _  (Const c)     = cConst c
  | certifyMsg et vt (Fun (f, ts)) = cFun (f, map (certifyMsg et vt) ts)
  | certifyMsg _  _  Attack        = cAttack

fun mk_Value_cVar x = cVar (x,ValueType)

val fv_Msg =
  let
    fun aux (Var x) = [x]
      | aux (Fun (_,ts)) = List.concat (map aux ts)
      | aux _ = []
  in
    mk_unique o  aux
  end

val fv_cMsg =
  let
    fun aux (cVar x) = [x]
      | aux (cFun (_,ts)) = List.concat (map aux ts)
      | aux (cSet (_,ts)) = List.concat (map aux ts)
      | aux (cOccursFact bs) = aux bs
      | aux _ = []
  in
    mk_unique o aux
  end

fun subst_apply' (delta:(string * VarType) -> cMsg) (t:cMsg) =
  case t of
    cVar x => delta x
  | cFun (f,ts) => cFun (f, map (subst_apply' delta) ts)
  | cSet (s,ts) => cSet (s, map (subst_apply' delta) ts)
  | cOccursFact bs => cOccursFact (subst_apply' delta bs)
  | c => c

fun subst_apply (delta:(string * cMsg) list) =
  subst_apply' (fn (n,tau) => (
      case List.find (fn x => fst x = n) delta of
        SOME x => snd x
      | NONE => cVar (n,tau)))
end
\<close>

ML\<open>

structure TracProtocol (* : TRAC_TERM *) =
struct
open Trac_Utils
datatype type_spec_elem =
  Consts of string list
| Union of string list

fun is_Consts t = case t of Consts _ => true | _ => false
fun the_Consts t = case t of Consts cs => cs | _ => error "Consts"

type type_spec = (string * type_spec_elem) list
type set_spec  = (string * string)

fun extract_Consts (tspec:type_spec) =
  (List.concat o map the_Consts o filter is_Consts o map snd) tspec

type funT = (string * string)
type fun_spec = {private: funT list, public: funT list}

type ruleT = (string * string list) * Trac_Term.Msg list * string list
type anaT = ruleT list

datatype prot_label = LabelN | LabelS

datatype action = RECEIVE of Trac_Term.Msg
                | SEND of Trac_Term.Msg
                | IN of Trac_Term.Msg * (string * Trac_Term.Msg list)
                | NOTIN of Trac_Term.Msg * (string * Trac_Term.Msg list)
                | NOTINANY of Trac_Term.Msg * string
                | INSERT of Trac_Term.Msg * (string * Trac_Term.Msg list)
                | DELETE of Trac_Term.Msg * (string * Trac_Term.Msg list)
                | NEW of string
                | ATTACK

datatype cAction = cReceive of Trac_Term.cMsg
                 | cSend of Trac_Term.cMsg
                 | cInequality of Trac_Term.cMsg * Trac_Term.cMsg
                 | cInSet of Trac_Term.cMsg * Trac_Term.cMsg
                 | cNotInSet of Trac_Term.cMsg * Trac_Term.cMsg
                 | cNotInAny of Trac_Term.cMsg * string
                 | cInsert of Trac_Term.cMsg * Trac_Term.cMsg
                 | cDelete of Trac_Term.cMsg * Trac_Term.cMsg
                 | cNew of string
                 | cAssertAttack

type transaction_name = string * (string * string) list * (string * string) list

type transaction={transaction:transaction_name,actions:(prot_label * action) list}

type cTransaction={
  transaction:transaction_name,
  receive_actions:(prot_label * cAction) list,
  checksingle_actions:(prot_label * cAction) list,
  checkall_actions:(prot_label * cAction) list,
  fresh_actions:(prot_label * cAction) list,
  update_actions:(prot_label * cAction) list,
  send_actions:(prot_label * cAction) list,
  attack_actions:(prot_label * cAction) list}

fun mkTransaction transaction actions = {transaction=transaction,
                                        actions=actions}:transaction

fun is_RECEIVE a = case a of RECEIVE _ => true | _ => false
fun is_SEND a = case a of SEND _ => true | _ => false
fun is_IN a = case a of IN _ => true | _ => false
fun is_NOTIN a = case a of NOTIN _ => true | _ => false
fun is_NOTINANY a = case a of NOTINANY _ => true | _ => false
fun is_INSERT a = case a of INSERT _ => true | _ => false
fun is_DELETE a = case a of DELETE _ => true | _ => false
fun is_NEW a = case a of NEW _ => true | _ => false
fun is_ATTACK a = case a of ATTACK => true | _ => false

fun the_RECEIVE a = case a of RECEIVE t => t | _ => error "RECEIVE"
fun the_SEND a = case a of SEND t => t | _ => error "SEND"
fun the_IN a = case a of IN t => t | _ => error "IN"
fun the_NOTIN a = case a of NOTIN t => t | _ => error "NOTIN"
fun the_NOTINANY a = case a of NOTINANY t => t | _ => error "NOTINANY"
fun the_INSERT a = case a of INSERT t => t | _ => error "INSERT"
fun the_DELETE a = case a of DELETE t => t | _ => error "DELETE"
fun the_NEW a = case a of NEW t => t | _ => error "FRESH"

fun maybe_the_RECEIVE a = case a of RECEIVE t => SOME t | _ => NONE
fun maybe_the_SEND a = case a of SEND t => SOME t | _ => NONE
fun maybe_the_IN a = case a of IN t => SOME t | _ => NONE
fun maybe_the_NOTIN a = case a of NOTIN t => SOME t | _ => NONE
fun maybe_the_NOTINANY a = case a of NOTINANY t => SOME t | _ => NONE
fun maybe_the_INSERT a = case a of INSERT t => SOME t | _ => NONE
fun maybe_the_DELETE a = case a of DELETE t => SOME t | _ => NONE
fun maybe_the_NEW a = case a of NEW t => SOME t | _ => NONE

fun is_Receive a = case a of cReceive _ => true | _ => false
fun is_Send a = case a of cSend _ => true | _ => false
fun is_Inequality a = case a of cInequality _ => true | _ => false
fun is_InSet a = case a of cInSet _ => true | _ => false
fun is_NotInSet a = case a of cNotInSet _ => true | _ => false
fun is_NotInAny a = case a of cNotInAny _ => true | _ => false
fun is_Insert a = case a of cInsert _ => true | _ => false
fun is_Delete a = case a of cDelete _ => true | _ => false
fun is_Fresh a = case a of cNew _ => true | _ => false
fun is_Attack a = case a of cAssertAttack => true | _ => false

fun the_Receive a = case a of cReceive t => t | _ => error "Receive"
fun the_Send a = case a of cSend t => t | _ => error "Send"
fun the_Inequality a = case a of cInequality t => t | _ => error "Inequality"
fun the_InSet a = case a of cInSet t => t | _ => error "InSet"
fun the_NotInSet a = case a of cNotInSet t => t | _ => error "NotInSet"
fun the_NotInAny a = case a of cNotInAny t => t | _ => error "NotInAny"
fun the_Insert a = case a of cInsert t => t | _ => error "Insert"
fun the_Delete a = case a of cDelete t => t | _ => error "Delete"
fun the_Fresh a = case a of cNew t => t | _ => error "New"

fun maybe_the_Receive a = case a of cReceive t => SOME t | _ => NONE
fun maybe_the_Send a = case a of cSend t => SOME t | _ => NONE
fun maybe_the_Inequality a = case a of cInequality t => SOME t | _ => NONE
fun maybe_the_InSet a = case a of cInSet t => SOME t | _ => NONE
fun maybe_the_NotInSet a = case a of cNotInSet t => SOME t | _ => NONE
fun maybe_the_NotInAny a = case a of cNotInAny t => SOME t | _ => NONE
fun maybe_the_Insert a = case a of cInsert t => SOME t | _ => NONE
fun maybe_the_Delete a = case a of cDelete t => SOME t | _ => NONE
fun maybe_the_Fresh a = case a of cNew t => SOME t | _ => NONE

fun certifyAction et vt (lbl,SEND t)            = (lbl,cSend    (Trac_Term.certifyMsg et vt t))
  | certifyAction et vt (lbl,RECEIVE t)         = (lbl,cReceive (Trac_Term.certifyMsg et vt t))
  | certifyAction et vt (lbl,IN (x,(s,ps)))     = (lbl,cInSet
      (Trac_Term.certifyMsg et vt x, Trac_Term.cSet (s, map (Trac_Term.certifyMsg et vt) ps)))
  | certifyAction et vt (lbl,NOTIN (x,(s,ps)))  = (lbl,cNotInSet
      (Trac_Term.certifyMsg et vt x, Trac_Term.cSet (s, map (Trac_Term.certifyMsg et vt) ps)))
  | certifyAction et vt (lbl,NOTINANY (x,s))    = (lbl,cNotInAny (Trac_Term.certifyMsg et vt x, s))
  | certifyAction et vt (lbl,INSERT (x,(s,ps))) = (lbl,cInsert
      (Trac_Term.certifyMsg et vt x, Trac_Term.cSet (s, map (Trac_Term.certifyMsg et vt) ps)))
  | certifyAction et vt (lbl,DELETE (x,(s,ps))) = (lbl,cDelete
      (Trac_Term.certifyMsg et vt x, Trac_Term.cSet (s, map (Trac_Term.certifyMsg et vt) ps)))
  | certifyAction _  _  (lbl,NEW x)             = (lbl,cNew x)
  | certifyAction _  _  (lbl,ATTACK)            = (lbl,cAssertAttack)

fun certifyTransaction (tr:transaction) =
  let
    val mk_cOccurs = Trac_Term.cOccursFact
    fun mk_Value_cVar x = Trac_Term.cVar (x,Trac_Term.ValueType)
    fun mk_cInequality x y = cInequality (mk_Value_cVar x, mk_Value_cVar y)
    val mk_cInequalities = list_triangle_product mk_cInequality

    val fresh_vals = map_filter (maybe_the_NEW o snd) (#actions tr)
    val decl_vars = map fst (#2 (#transaction tr))
    val neq_constrs = #3 (#transaction tr)

    val _ = if     List.exists (fn x => List.exists (fn y => x = y) fresh_vals) decl_vars
            orelse List.exists (fn x => List.exists (fn y => x = y) decl_vars)  fresh_vals
            then error "the fresh and the declared variables must not overlap"
            else ()

    val _ = case List.find (fn (x,y) => x = y) neq_constrs of
              SOME (x,y) => error ("illegal inequality constraint: " ^ x ^ " != " ^ y)
            | NONE => ()

    val nonfresh_vals = map fst (filter (fn x => snd x = "value") (#2 (#transaction tr)))
    val enum_vars = filter (fn x => snd x <> "value") (#2 (#transaction tr))

    fun lblS t = (LabelS,t)

    val cactions = map (certifyAction enum_vars (nonfresh_vals@fresh_vals)) (#actions tr)

    val nonfresh_occurs = map (lblS o cReceive o mk_cOccurs o mk_Value_cVar) nonfresh_vals
    val receives = filter (is_Receive o snd) cactions
    val value_inequalities = map lblS (mk_cInequalities nonfresh_vals)
    val checksingles = filter (fn (_,a) => is_InSet a orelse is_NotInSet a) cactions
    val checkalls = filter (is_NotInAny o snd) cactions
    val updates = filter (fn (_,a) => is_Insert a orelse is_Delete a) cactions
    val fresh = filter (is_Fresh o snd) cactions
    val sends = filter (is_Send o snd) cactions
    val fresh_occurs = map (lblS o cSend o mk_cOccurs o mk_Value_cVar) fresh_vals
    val attack_signals = filter (is_Attack o snd) cactions
  in
    {transaction = #transaction tr,
     receive_actions = nonfresh_occurs@receives,
     checksingle_actions = value_inequalities@checksingles,
     checkall_actions = checkalls,
     fresh_actions = fresh,
     update_actions = updates,
     send_actions = sends@fresh_occurs,
     attack_actions = attack_signals}:cTransaction
  end

fun subst_apply_action (delta:(string * Trac_Term.cMsg) list) (lbl:prot_label,a:cAction) =
  let
    val apply = Trac_Term.subst_apply delta
  in
    case a of
      cReceive t => (lbl,cReceive (apply t))
    | cSend t => (lbl,cSend (apply t))
    | cInequality (x,y) => (lbl,cInequality (apply x, apply y))
    | cInSet (x,s) => (lbl,cInSet (apply x, apply s))
    | cNotInSet (x,s) => (lbl,cNotInSet (apply x, apply s))
    | cNotInAny (x,s) => (lbl,cNotInAny (apply x, s))
    | cInsert (x,s) => (lbl,cInsert (apply x, apply s))
    | cDelete (x,s) => (lbl,cDelete (apply x, apply s))
    | cNew x => (lbl,cNew x)
    | cAssertAttack => (lbl,cAssertAttack)
  end

fun subst_apply_actions delta =
  map (subst_apply_action delta)


type protocol = {
  name:string
 ,type_spec:type_spec 
 ,set_spec:set_spec list
 ,function_spec:fun_spec option
 ,analysis_spec:anaT
 ,transaction_spec:(string option * transaction list) list
 ,fixed_point: (Trac_Term.cMsg list * (string * string list) list list *
                ((string * string list) list * (string * string list) list) list) option
}

exception TypeError

val fun_empty = {
                  public=[] 
                 ,private=[]
                }:fun_spec

fun update_fun_public (fun_spec:fun_spec) public =
    ({public = public
     ,private = #private fun_spec 
    }):fun_spec      

fun update_fun_private (fun_spec:fun_spec) private =
    ({public = #public fun_spec
     ,private = private 
    }):fun_spec      


val empty={
            name=""
           ,type_spec=[]
           ,set_spec=[]
           ,function_spec=NONE
           ,analysis_spec=[]
           ,transaction_spec=[]
           ,fixed_point = NONE
          }:protocol

fun update_name (protocol_spec:protocol) name =
    ({name = name
     ,type_spec = #type_spec protocol_spec
     ,set_spec = #set_spec protocol_spec
     ,function_spec = #function_spec protocol_spec
     ,analysis_spec = #analysis_spec protocol_spec
     ,transaction_spec = #transaction_spec protocol_spec
     ,fixed_point = #fixed_point protocol_spec
    }):protocol     
fun update_sets (protocol_spec:protocol) set_spec =
    ({name = #name protocol_spec
     ,type_spec = #type_spec protocol_spec
     ,set_spec =
        if has_duplicates (op =) (map fst set_spec)
        then error "Multiple declarations of the same set family"
        else set_spec
     ,function_spec = #function_spec protocol_spec
     ,analysis_spec = #analysis_spec protocol_spec
     ,transaction_spec = #transaction_spec protocol_spec
     ,fixed_point = #fixed_point protocol_spec
    }):protocol     
fun update_type_spec (protocol_spec:protocol) type_spec =
    ({name = #name protocol_spec
     ,type_spec =
        if has_duplicates (op =) (map fst type_spec)
        then error "Multiple declarations of the same enumeration type"
        else type_spec
     ,set_spec = #set_spec protocol_spec
     ,function_spec = #function_spec protocol_spec
     ,analysis_spec = #analysis_spec protocol_spec
     ,transaction_spec = #transaction_spec protocol_spec
     ,fixed_point = #fixed_point protocol_spec
    }):protocol     
fun update_functions (protocol_spec:protocol) function_spec =
    ({name = #name protocol_spec
     ,type_spec = #type_spec protocol_spec
     ,set_spec = #set_spec protocol_spec
     ,function_spec = case function_spec of
          SOME fs =>
            if has_duplicates (op =) (map fst ((#public fs)@(#private fs)))
            then error "Multiple declarations of the same constant or function symbol"
            else SOME fs
        | NONE => NONE
     ,analysis_spec = #analysis_spec protocol_spec
     ,transaction_spec = #transaction_spec protocol_spec
     ,fixed_point = #fixed_point protocol_spec
    }):protocol      
fun update_analysis (protocol_spec:protocol) analysis_spec =
    ({name = #name protocol_spec
     ,type_spec = #type_spec protocol_spec
     ,set_spec = #set_spec protocol_spec
     ,function_spec = #function_spec protocol_spec
     ,analysis_spec =
        if has_duplicates (op =) (map (#1 o #1) analysis_spec)
        then error "Multiple analysis rules declared for the same function symbol"
        else if List.exists (has_duplicates (op =)) (map (#2 o #1) analysis_spec)
        then error "The heads of the analysis rules must be linear terms"
        else if let fun f ((_,xs),ts,ys) =
                            subset (op =) (ys@List.concat (map Trac_Term.fv_Msg ts), xs)
                in List.exists (not o f) analysis_spec end
        then error "Variables occurring in the body of an analysis rule should also occur in its head"
        else analysis_spec
     ,transaction_spec = #transaction_spec protocol_spec
     ,fixed_point = #fixed_point protocol_spec
    }):protocol
fun update_transactions (prot_name:string option) (protocol_spec:protocol) transaction_spec =
    ({name = #name protocol_spec
     ,type_spec = #type_spec protocol_spec
     ,set_spec = #set_spec protocol_spec
     ,function_spec = #function_spec protocol_spec
     ,analysis_spec = #analysis_spec protocol_spec
     ,transaction_spec = (prot_name,transaction_spec)::(#transaction_spec protocol_spec)
     ,fixed_point = #fixed_point protocol_spec
    }):protocol     
fun update_fixed_point (protocol_spec:protocol) fixed_point =
    ({name = #name protocol_spec
     ,type_spec = #type_spec protocol_spec
     ,set_spec = #set_spec protocol_spec
     ,function_spec = #function_spec protocol_spec
     ,analysis_spec = #analysis_spec protocol_spec
     ,transaction_spec = #transaction_spec protocol_spec
     ,fixed_point = fixed_point
    }):protocol     
           
           
end
\<close>


end
