(******************************************************************************)
(* External Algorithm for Calculating the Transitive Closure in Isabelle/HOL  *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(* Email: frank.zeyda@york.ac.uk                                              *)
(******************************************************************************)

(* GRAPH Signature *)

signature GRAPH =
sig
  type vertex;
  type graph = {num_verts : int, edges : (vertex * vertex) list};
  type verts = {num_verts : int, vlist : vertex list};
  val mk_graph : int list -> graph;
  val mk_verts : int list -> verts;
end;

(* Graph Structure *)

structure Graph : GRAPH =
struct
  type vertex = int;
  type graph = {num_verts : int, edges : (vertex * vertex) list};
  type verts = {num_verts : int, vlist : vertex list};

  fun map_pair f (x, y) = (f x, f y);

  fun mk_edges nvs (x :: y :: r) =
      if x < nvs andalso y < nvs then
        (x, y) :: (mk_edges nvs r)
      else let val (xs, ys) = map_pair Int.toString (x, y) in
        error("mk_graph: invalid edge (" ^ xs ^ ", " ^ ys  ^ ")")
      end
    | mk_edges _ [] = []
    | mk_edges _ _ = error("mk_graph: odd-length edge data");

  fun mk_vlist vns (x :: r) =
      if x < vns then
        x :: (mk_vlist vns r)
      else let val xs = Int.toString x in
        error("mk_verts: invalid edge " ^ xs)
      end
    | mk_vlist _ [] = [];

  fun mk_graph (nvs :: edges) : graph =
    {num_verts = nvs, edges = mk_edges nvs edges}
    | mk_graph [] = error("mk_graph: empty input data");

  fun mk_verts (nvs :: vlist) : verts =
    {num_verts = nvs, vlist = mk_vlist nvs vlist}
    | mk_verts [] = error("mk_verts: empty input data");
end;

(* TRANSCL_UTILS Signature *)

signature TRANSCL_UTILS =
sig
  val is_relT : typ -> bool;
  val is_rel : term -> bool;
  val dest_rel : term -> (term * term) list;
  val escape_quotes : string -> string;
  val assign_once : (''a array * int * ''a) -> ''a -> unit;
  val read_if_set : (''a array * int) -> ''a -> ''a;
  val ml_print_pair : (term * term) -> string;
  val ml_print_rel : term -> string;
end;

(* Transcl_Utils Structure *)

structure Transcl_Utils : TRANSCL_UTILS =
struct
  fun is_relT typ =
    (HOLogic.dest_prodT (HOLogic.dest_setT typ); true)
    handle TYPE _ => false;

  fun is_rel term =
    (map HOLogic.dest_prod (HOLogic.dest_set term); true)
    handle TERM _ => false;

  fun dest_rel term =
    (map HOLogic.dest_prod (HOLogic.dest_set term))
    handle TERM _ =>
      raise TERM("dest_rel: not a set of pairs", [term]);

  val escape_quotes =
    String.translate (fn c => if c = #"\"" then "\\\"" else String.str c)

  fun assign_once (arr : ''a array, i : int, x : ''a) (default : ''a) =
    let val y = Array.sub (arr, i) in
      if y = default then
        Array.update (arr, i, x)
      else if x = y then () else
        raise General.Subscript
    end;

  fun read_if_set (arr : ''a array, i : int) (default : ''a) =
    let val x = Array.sub (arr, i) in
      if not (x = default) then x else
        raise General.Subscript
    end;

  fun to_str_list (left, sep, right) to_str list =
    let fun to_str_list_aux [] = ""
      | to_str_list_aux [x] = (to_str x)
      | to_str_list_aux (h :: t) = (to_str h) ^ sep ^ (to_str_list_aux t);
    in left ^ (to_str_list_aux list) ^ right
    end;

  fun ml_print_pair (t1, t2) =
    "(" ^ (ML_Syntax.print_term t1) ^ ", " ^ (ML_Syntax.print_term t2) ^ ")";

  fun ml_print_rel rel_term =
    to_str_list ("{", ", ", "}") ml_print_pair (dest_rel rel_term);
end;

(* TRANSCL Signature *)

signature TRANSCL =
sig
  (* Result Data *)
  datatype transcl_res =
    Data of string | Error of string;

  (* Algorithm Specifiers *)
  datatype algorithm =
    Floyd_Warhsall | Boost;

  (* Tool Invocation *)
  val algorithm_specifier : algorithm -> string;
  val transcl_cmd : Proof.context -> string -> string -> string;
  val transcl_run : Proof.context -> string -> string -> transcl_res;
  val parse_rel_data : string -> Graph.graph * Graph.graph;
  val parse_set_data : string -> Graph.graph * Graph.verts;

  (* Term Reconstruction *)
  val mk_vmap : term -> Graph.graph -> term array;
  val reconstr_rel : term -> Graph.graph -> Graph.graph -> term;
  val reconstr_set : term -> Graph.graph -> Graph.verts -> term;

  (* Top-level Commands *)
  val transcl1 : Proof.context -> term -> term;
  val transcl2 : Proof.context -> term -> term;
  val rangecl1 : Proof.context -> term -> term;
  val rangecl2 : Proof.context -> term -> term;
end;

(* Transcl Structure *)

structure Transcl : TRANSCL =
struct
  open Graph;
  open Transcl_Utils;

  (* Result Data *)
  datatype transcl_res =
    Data of string |
    Error of string;

  (* Algorithm Specifiers *)
  datatype algorithm =
    Floyd_Warhsall | Boost;

  fun algorithm_specifier Floyd_Warhsall = "floyd-warshall"
    | algorithm_specifier Boost = "boost";

  (* Tool Invocation *)
  fun transcl_tool (ctx : Proof.context) =
    let val home = (Config.get ctx transcl_home); in
      (* Use Path.smart_implode instead? *)
      Path.implode (Path.append (Path.explode home) (Path.basic "transcl"))
    end;

  fun transcl_cmd (ctx : Proof.context) (input : string) (encoding : string) =
    let (* Linux echo seems to be troublesome. Better create a tempfile! *)
      val esc_input = (escape_quotes input);
      (* val _ = Output.writeln esc_input; *)
      val algorithm = (Config.get ctx transcl_algorithm);
    in
      ("echo '" ^ esc_input ^ "' | " ^
        (transcl_tool ctx) ^ " -a " ^ algorithm ^ " -e" ^ encoding)
    end;

  fun transcl_run (ctx : Proof.context) (input : string) (encoding : string) =
    let val {out = res, err = err, ...} =
      Bash.process (transcl_cmd ctx input encoding);
    in
      if err = "[OK]" then (Data res) else (Error err)
    end;

  fun tokenize_reldata (data : string) =
    (map (Option.valOf o Int.fromString)
      (String.tokens (fn c => c = #";") data));

  fun parse_rel_data data = let
      val split = String.tokens (fn c => c = #"\n") data;
      val data1 = (nth split 0);
      val data2 = (nth split 1);
      val ginit = mk_graph (tokenize_reldata data1);
      val gfini = mk_graph (tokenize_reldata data2);
    in (ginit, gfini) end;

  fun parse_set_data data = let
      val split = String.tokens (fn c => c = #"\n") data;
      val data1 = (nth split 0);
      val data2 = (nth split 1);
      val ginit = mk_graph (tokenize_reldata data1);
      val sfini = mk_verts (tokenize_reldata data2);
    in (ginit, sfini) end;

  (* Term Reconstruction *)
  fun reconstr_error msg = error("transcl reconstruction error: " ^ msg);

  local
    (* Arrays are mutable objects. May this cause issues in Isabelle? *)
    fun mk_vmap_aux [] [] (_ : term array) = ()
      | mk_vmap_aux ((t1, t2) :: terms) ((i, j) :: edges) arr = (
      let val _ = (assign_once (arr, i, t1) Term.dummy);
          val _ = (assign_once (arr, j, t2) Term.dummy);
      in (mk_vmap_aux terms edges arr)
      end handle General.Subscript =>
        reconstr_error("entry in vmap array set twice"))
      | mk_vmap_aux _ [] _ =
        reconstr_error("more elements in HOL relation than edges in graph")
      | mk_vmap_aux [] _ _ =
        reconstr_error("more edges in graph than elements in HOL relation");
  in
    fun mk_vmap (rel_term : term) (g : graph) =
      let val vert_map = Array.array (#num_verts g, Term.dummy) in
        (mk_vmap_aux (dest_rel rel_term) (#edges g) vert_map; vert_map)
      end;
  end;

  fun reconstr_rel (rel_term : term) (ginit : graph) (gfini : graph) =
    let val vmap = (mk_vmap rel_term ginit);
      fun mk_elem (i, j) = let
        val t1 = read_if_set (vmap, i) Term.dummy;
        val t2 = read_if_set (vmap, j) Term.dummy;
      in HOLogic.mk_prod (t1, t2) end
      handle General.Subscript =>
        reconstr_error("entry in vmap array unassigned");
      val setT = HOLogic.dest_setT (type_of rel_term);
    in
      HOLogic.mk_set setT (map mk_elem (#edges gfini))
    end;

  fun reconstr_set (rel_term : term) (ginit : graph) (sfini : verts) =
    let val vmap = (mk_vmap rel_term ginit);
      fun mk_elem i = (read_if_set (vmap, i) Term.dummy)
      handle General.Subscript =>
        reconstr_error("entry in vmap array unassigned");
      val setT = (snd o HOLogic.dest_prodT o HOLogic.dest_setT)
        (type_of rel_term);
    in
      HOLogic.mk_set setT (map mk_elem (#vlist sfini))
    end;

  (* Top-level Commands *)

  (* We implement two versions of each command:          *)
  (*  1. A faster one using term-based pretty-printing;  *)
  (*  2. A robust one using ML printing of the term AST. *)

  fun transcl1 (ctx : Proof.context) (rel_term : term) =
    let val input = (* YXML.content_of removes the PIDE markup! *)
        YXML.content_of (Syntax.string_of_term ctx rel_term);
      val result = (transcl_run ctx input "rel");
      val data = (case result of Data data => data
        | Error err => error("transcl: " ^ err));
      val (ginit, gfini) = (parse_rel_data data);
    in (reconstr_rel rel_term ginit gfini) end;

  fun transcl2 (ctx : Proof.context) (rel_term : term) =
      let val input = (ml_print_rel rel_term);
      val result = (transcl_run ctx input "rel");
      val data = (case result of Data data => data
        | Error err => error("transcl: " ^ err));
      val (ginit, gfini) = (parse_rel_data data);
    in (reconstr_rel rel_term ginit gfini) end;

  fun rangecl1 (ctx : Proof.context) (rel_term : term) =
    let val input = (* YXML.content_of removes the PIDE markup! *)
        YXML.content_of (Syntax.string_of_term ctx rel_term);
      val result = (transcl_run ctx input "set");
      val data = (case result of Data data => data
        | Error err => error("transcl: " ^ err));
      val (ginit, sfini) = (parse_set_data data);
    in (reconstr_set rel_term ginit sfini) end;

  fun rangecl2 (ctx : Proof.context) (rel_term : term) =
      let val input = (ml_print_rel rel_term);
      val result = (transcl_run ctx input "set");
      val data = (case result of Data data => data
        | Error err => error("transcl: " ^ err));
      val (ginit, sfini) = (parse_set_data data);
    in (reconstr_set rel_term ginit sfini) end;
end;

(* TRANSCL_REWRITER Signature *)

signature TRANSCL_REWRITER =
sig
  val map_top_down : (term -> term) -> term -> term;
  val is_rel_const : term -> bool;
  val transcl_term_tr : Proof.context -> term -> term;
  val rangecl_term_tr : Proof.context -> term -> term;
  val transcl_tr : Proof.context -> term list -> term list;
  val rangecl_tr : Proof.context -> term list -> term list;
end;

(* Transcl_Rewriter structure *)

structure Transcl_Rewriter : TRANSCL_REWRITER =
struct
  open Transcl_Utils;

  fun map_top_down f t =
    (f t) handle Match =>
      (case t of (t1 $ t2) =>
        (map_top_down f t1) $
        (map_top_down f t2)
      | Abs (v, typ, t) =>
        Abs (v, typ, map_top_down f t)
      | _ => t);

  fun is_rel_const (Const (_, typ)) = (is_relT typ)
    | is_rel_const _ = false;

  fun transcl_term_tr ctx (Const (@{const_name transcl}, _) $ arg) =
    let val simp_arg = PreSimplifier.presimplify ctx is_rel_const arg in
      if (is_rel simp_arg) then
        if (Config.get ctx transcl_robust)
        then (Transcl.transcl2 ctx simp_arg)
        else (Transcl.transcl1 ctx simp_arg)
      else raise TERM(
        "Term did not simplify to an enumerated set of pairs", [simp_arg])
    end
  | transcl_term_tr _ _ = raise Match;

  fun rangecl_term_tr ctx (Const (@{const_name rangecl}, _) $ arg) =
    let val simp_arg = PreSimplifier.presimplify ctx is_rel_const arg in
      if (is_rel simp_arg) then
        if (Config.get ctx transcl_robust)
        then (Transcl.rangecl2 ctx simp_arg)
        else (Transcl.rangecl1 ctx simp_arg)
      else raise TERM(
        "Term did not simplify to an enumerated set of pairs", [simp_arg])
    end
  | rangecl_term_tr _ _ = raise Match;

  fun transcl_tr ctx = (map (map_top_down (transcl_term_tr ctx)));
  fun rangecl_tr ctx = (map (map_top_down (rangecl_term_tr ctx)));
end;