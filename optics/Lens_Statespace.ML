signature LENS_STATESPACE =
sig
  val compile_statespace: bstring -> (bstring * typ) list -> xstring list -> theory -> theory
  val statespace_cmd: bstring -> xstring list -> (bstring * string) list -> theory -> theory
end

structure Lens_Statespace =
struct
(* Compile a state space from a given state space name and list of variable declarations *)
fun compile_statespace ssn vds exts thy =
  let
    open Lens_Lib;
    open Syntax;
    val ctx = Named_Target.theory_init thy
    val vns = map fst vds 
    val vfixes = map (fn (n, t) => (Binding.name n, SOME (lensT t astateT), NoSyn)) vds
    val vwbs   = map (mk_vwb_lens o free) vns;
    val simp   = Attrib.check_src ctx (Token.make_src ("simp", Position.none) [])
    val indeps = map (fn (x, y) => mk_indep (free x) (free y)) (pairings vns)
    val locexs = map (fn e => (Locale.check thy (e, Position.none), (("", false), (Expression.Positional [], [])))) exts
  in
  (Local_Theory.exit_global o snd o 
  Expression.add_locale (Binding.name ssn) Binding.empty (locexs,[]) 
  (* Fix each of the variables as lenses *)
  [ Element.Fixes vfixes 
  (* Assume that all lenses are very well-behaved and independent (as in a product space) *)
  , Element.Assumes [((Binding.name "vwbs", [simp])
                     , map (fn vwb => (vwb, [])) vwbs),
                     ((Binding.name "indeps", [simp])
                     , map (fn vwb => (vwb, [])) indeps)]
  ]) thy
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
