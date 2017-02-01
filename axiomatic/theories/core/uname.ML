(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uname.ML                                                             *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 27 Jan 2017 *)

(* Utility Functions *)

signature NAME_UTILS =
sig
  val deep_unmark_const : term -> term
  val right_crop_by : int -> string -> string
  val last_char_str : string -> string
  val repeat_char : char -> int -> string
  val mk_id : string -> term
end;

structure Name_Utils : NAME_UTILS =
struct
  fun unmark_const_term (Const (name, typ)) =
    Const (Lexicon.unmark_const name, typ)
  | unmark_const_term term = term;

  val deep_unmark_const =
    (map_aterms unmark_const_term);

  fun right_crop_by n s =
    String.substring (s, 0, (String.size s) - n);

  fun last_char_str s =
    String.str (String.sub (s, (String.size s) - 1));

  fun repeat_char c n =
    if n > 0 then (String.str c) ^ (repeat_char c (n - 1)) else "";

  fun mk_id name = Free (name, dummyT);
  end;

(* Name Parser *)

signature NAME_PARSER =
sig
  val strip_dashes : string -> string * int
  val strip_subscript : string -> string * string
  val dest_name : string -> string * int * string
  val uname_tr : term list -> term
end;

structure Name_Parser : NAME_PARSER =
struct
  open Name_Utils;

  local
  fun strip_dashes_aux dashes name =
    if (String.isSuffix "'" name) andalso
        (* The following is to support dashes in subscripts. *)
        not (String.isSuffix "\<^sub>" (right_crop_by 1 name)) then
      strip_dashes_aux (dashes + 1) (right_crop_by 1 name)
    else (name, dashes);
  in
    val strip_dashes = strip_dashes_aux 0;
  end;

  local
  val sub_size = String.size "\<^sub>";
  fun strip_subscript_aux subscript name =
    if (String.size name) > 0 andalso
        (String.isSuffix "\<^sub>" (right_crop_by 1 name)) then
      (strip_subscript_aux
        ((last_char_str name) ^ subscript) (right_crop_by (sub_size + 1) name))
    else (name, subscript);
  in
    val strip_subscript = strip_subscript_aux "";
  end;

  fun dest_name name =
  let val (name_aux1, dashes) = (strip_dashes name);
      val (name_aux2, subscript) = (strip_subscript name_aux1) in
    (name_aux2, dashes, subscript)
  end;

  fun uname_tr [Free (name, _)] =
    (let val (base_name, dashes, subscript) = dest_name name in
      if dashes <= 1 then
        @{term "MkName"}
          $ (HOLogic.mk_string base_name)
          (* $ (HOLogic.mk_number HOLogic.natT dashes) *)
          $ (Term_Utils.mk_bool (dashes = 1))
          $ (HOLogic.mk_string subscript)
       else error("Error parsing uname: multiple dashes are not allowed.")
     end handle Fail _ => raise Match)
  | uname_tr _ = raise Match;
end;

(* Name Printer *)

signature NAME_PRINTER =
sig
  val add_dashes : string -> int -> string
  val add_subscript : string -> string -> string
  val assemble_name : string -> int -> string -> string
  val name_from_terms : term * term * term -> string
  val mk_uname : term -> term -> term -> term
  val MkName_tr' : Proof.context -> term list -> term
end;

structure Name_Printer : NAME_PRINTER =
struct
  open Name_Utils;

  fun add_dashes name dashes =
    name ^ (repeat_char #"'" dashes);

  fun add_subscript name subscript =
    let val subs_list = (map String.str (String.explode subscript)) in
      (fold (fn sub => fn s => (s ^ "\<^sub>" ^ sub)) subs_list name)
    end;

  fun assemble_name base_name dashes subscript =
    (add_dashes (add_subscript base_name subscript) dashes);

  (* fun dest_number_robust term =
      (snd o HOLogic.dest_number) term
    handle TERM _ => (HOLogic.dest_nat term); *)

  fun name_from_terms (base_name, dashed, subscript) =
    (assemble_name
      (HOLogic.dest_string base_name)
      (* (dest_number_robust dashes) *)
      (if (Term_Utils.dest_bool dashed) then 1 else 0)
      (HOLogic.dest_string subscript));

  fun mk_uname base_name dashed subscript =
    Const (@{syntax_const "_uname"}, dummyT) $
      mk_id (name_from_terms (base_name, dashed, subscript));

  fun MkName_tr' ctx [base_name, dashed, subscript] =
    if not (Config.get ctx disable_uname_pp) then
      let val base_name' = deep_unmark_const base_name;
      val dashes' = deep_unmark_const dashed;
      val subscript' = deep_unmark_const subscript in
        (mk_uname base_name' dashes' subscript')
      end handle Fail _ => raise Match
               | TERM _ => raise Match
    else raise Match
    | MkName_tr' _ _ = raise Match;
end;