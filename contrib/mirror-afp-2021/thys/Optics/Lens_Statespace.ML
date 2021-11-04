signature LENS_STATESPACE =
sig
  val mk_statespace_elements: bstring -> (bstring * typ) list -> xstring list -> theory -> Element.context_i list
  val compile_statespace: bstring -> (bstring * typ) list -> xstring list -> theory -> theory
  val statespace_cmd: bstring -> xstring list -> (bstring * string) list -> theory -> theory
end

structure Lens_Statespace =
struct
  (* Produce a list of new elements for a locale to characterise a state space *)
  fun mk_statespace_elements vds exts thy = 
  let
    open Lens_Lib;
    open Syntax;
    val ctx = Named_Target.theory_init thy
    val vns = map fst vds 
    val vfixes = map (fn (n, t) => (Binding.name n, SOME (lensT t astateT), NoSyn)) vds
    val vwbs   = map (mk_vwb_lens o free) vns;
    val simp   = Attrib.check_src ctx (Token.make_src ("simp", Position.none) [])
    val imps   = map (fn e => Locale.check thy (e, Position.none)) exts
    (* List of lenses imported *)
    val ilnsls = map (filter (isLensT o snd) o map fst o Locale.params_of thy) imps
    (* Independence axioms from imports *)
    val impind = List.concat (map (pairsWith vns) (map (map fst) ilnsls))
    val indeps = map (fn (x, y) => mk_indep (free x) (free y)) 
                     (pairings (vns) @ impind)
  in 
  (* Fix each of the variables as lenses *)
  [ Element.Fixes vfixes 
  (* Assume that all lenses are very well-behaved and independent (as in a product space) *)
  , Element.Assumes [((Binding.name "vwbs", [simp])
                     , map (fn vwb => (vwb, [])) vwbs),
                     ((Binding.name "indeps", [simp])
                     , map (fn vwb => (vwb, [])) indeps)]
  ]
  end


  (* Compile a state space from a given state space name and list of variable declarations *)
  fun compile_statespace ssn vds exts thy =
  let
    open Lens_Lib;
    open Syntax;
    val imps   = map (fn e => Locale.check thy (e, Position.none)) exts
    val locexs = map (fn i => (i, (("", false), (Expression.Positional [], [])))) imps
  in
  (Local_Theory.exit_global o snd o 
  Expression.add_locale (Binding.name ssn) Binding.empty [] (locexs,[]) 
  (mk_statespace_elements vds exts thy)) thy
  end

  fun statespace_cmd n exts vds thy = 
  let 
    open Syntax
    val ctx = Named_Target.theory_init thy in
    compile_statespace n (map (fn (n, t) => (n, read_typ ctx t)) vds) exts thy
  end
end;

let open Parse in
  Outer_Syntax.command @{command_keyword statespace} "define locale-based statespace with lenses"
    ((Parse.name --
      (@{keyword "="} |-- Scan.repeat (Parse.name --| @{keyword "+"}) --
        Scan.repeat (Parse.name -- ($$$ "::" |-- !!! typ))))
    >> (fn (n, (exts, vds)) => Toplevel.theory (Lens_Statespace.statespace_cmd n exts vds)))
end
