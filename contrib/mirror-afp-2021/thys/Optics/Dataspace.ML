structure Dataspace =
struct

  val achanT = TFree ("'ch", ["HOL.type"])

  fun mk_constant_elements cds =
    let
    open Syntax;
    val cfixes = map (fn (n, t) => (Binding.name n, SOME t, NoSyn)) cds
    in [ Element.Fixes cfixes ] end;

  (* Produce a list of new elements for a locale to characterise the channels *)
  fun mk_channel_elements exts chds thy = 
  let
    open Lens_Lib;
    open Prism_Lib;
    open Syntax;
    val ctx = Named_Target.theory_init thy
    val chns = map fst chds 
    val chfixes = map (fn (n, t) => (Binding.name n, SOME (prismT t achanT), NoSyn)) chds
    val wbs    = map (mk_wb_prism o free) chns;
    val simp   = Attrib.check_src ctx (Token.make_src ("simp", Position.none) [])
    val imps   = map (fn e => Locale.check thy (e, Position.none)) exts
    (* List of prisms imported *)
    val ilnsls = map (filter (isPrismT o snd) o map fst o Locale.params_of thy) imps
    (* Codependence axioms from imports *)
    val impind = List.concat (map (pairsWith chns) (map (map fst) ilnsls))
    val codeps = map (fn (x, y) => mk_codep (free x) (free y)) 
                     (pairings (chns) @ impind)
  in 
  (* Fix each of the channels as prisms *)
  [ Element.Fixes chfixes 
  (* Assume that all prisms are well-behaved and codependent (as in an algebraic datatype) *)
  , Element.Assumes [((Binding.name "prisms", [simp])
                     , map (fn wb => (wb, [])) wbs),
                     ((Binding.name "codeps", [simp])
                     , map (fn dp => (dp, [])) codeps)]
  ]
  end

  val STATE = "STATE_TYPE"
  val CHAN = "CHAN_TYPE"

  fun compile_dataspace nm exts cds assms vds chds thy =
  let
    open Lens_Lib;
    open Syntax;
    val imps   = map (fn e => Locale.check thy (e, Position.none)) exts
    (* When extending existing dataspaces, we instantiate their respective state and channel
       types to avoid ambiguity (via a locale "where" clause) *)
    val pinsts = Expression.Named 
                    [(STATE, Logic.mk_type astateT)
                    ,(CHAN, Logic.mk_type achanT)]
    val locexs = map (fn i => (i, (("", false), (pinsts, [])))) imps
    (* We also create fixed parameters for the types so they can be instantiated later *)
    val st_par = (Binding.name STATE, SOME (Term.itselfT astateT), NoSyn)
    val ch_par = (Binding.name CHAN, SOME (Term.itselfT achanT), NoSyn)
  in
  (Local_Theory.exit_global o snd o 
  Expression.add_locale (Binding.name nm) Binding.empty [] (locexs, []) 
  (mk_constant_elements cds 
   @ [Element.Assumes assms]
   @ Lens_Statespace.mk_statespace_elements vds exts thy
   @ mk_channel_elements exts chds thy
   @ [Element.Fixes [st_par, ch_par]])) thy
  end
  
  fun dataspace_cmd nm exts cds rassms vds chds thy = 
  let 
    open Syntax; open HOLogic;
    val ctx = Named_Target.theory_init thy 
    val assms = map (fn (b, td) => (b, map (fn (t, ts) => (mk_Trueprop (parse_term ctx t), map (mk_Trueprop o parse_term ctx) ts)) td)) rassms in
    compile_dataspace nm exts (map (fn (n, t) => (n, read_typ ctx t)) cds) assms (map (fn (n, t) => (n, read_typ ctx t)) vds) (map (fn (n, t) => (n, read_typ ctx t)) chds)  thy
  end

end;

let open Parse; open Parse_Spec; open Scan in
  Outer_Syntax.command @{command_keyword dataspace} "define reactive contexts"
    ((name --
      ((@{keyword "="} |-- repeat (Parse.name --| @{keyword "+"}))
       -- optional (@{keyword "constants"} |-- repeat1 (name -- ($$$ "::" |-- !!! typ))) []
       -- optional (@{keyword "assumes"} |-- !!! (and_list1 (opt_thm_name ":" -- repeat1 propp))) []
       -- optional (@{keyword "variables"} |-- repeat1 (name -- ($$$ "::" |-- !!! typ))) []
       -- optional (@{keyword "channels"} |-- repeat1 (name -- ($$$ "::" |-- !!! typ))) [])
    >> (fn (nm, ((((exts, cds), assms), vds), chds)) => Toplevel.theory (Dataspace.dataspace_cmd nm exts cds assms vds chds))))
end;
