(* Create enumeration types *)

signature ENUM_TYPE =
sig
  val enum_type : bstring -> bstring list -> theory -> theory
end

structure Enum_Type : ENUM_TYPE =
struct

(* code copied from HOL/SPARK/TOOLS *)
fun define_overloaded_generic (binding,eq) lthy =
  let
    val ((c, _), rhs) = eq |> Syntax.check_term lthy |>
      Logic.dest_equals |>> dest_Free;
    val ((_, (_, thm)), lthy') = Local_Theory.define
      ((Binding.name c, NoSyn), (binding, rhs)) lthy
    val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy');
    val thm' = singleton (Proof_Context.export lthy' ctxt_thy) thm
  in (thm', lthy')
end;
fun define_overloaded (name,eq) = define_overloaded_generic ((Binding.name name, @{attributes [code]}),eq);

(* val enum_type = fn: bstring -> bstring list -> theory -> theory *)

fun enum_type tname cs thy =
  let 
    open BNF_FP_Def_Sugar; open BNF_FP_Rec_Sugar_Util; open BNF_LFP; open Ctr_Sugar; open Syntax; open Logic; open Specification; open HOLogic
    val thy0 = Named_Target.theory_map (co_datatype_cmd Least_FP construct_lfp ((K Plugin_Name.default_filter, true), 
        [((((([],Binding.name tname), Mixfix.NoSyn), map (fn n => (((Binding.empty, Binding.name n), []), Mixfix.NoSyn)) cs), (Binding.empty, Binding.empty, Binding.empty)),[])])) thy;
    val ctx2 = Class.instantiation_cmd ([tname], [], "enum") thy0;
    val ty = Syntax.read_typ ctx2 tname;
    val cs' = map (Syntax.read_term ctx2) cs;
    fun mk_def ty x v = Const ("Pure.eq", ty --> ty --> Term.propT) $ Const (x, ty) $ v;
    val (thm1, ctx3) = define_overloaded ("enum_" ^ tname, mk_def (HOLogic.listT ty) (@{const_name "enum_class.enum"}) (HOLogic.mk_list dummyT cs')) ctx2
    val (thm2, ctx4) = define_overloaded ("enum_all_" ^ tname, mk_def dummyT (@{const_name "enum_class.enum_all"}) (Abs ("P", dummyT, foldl1 HOLogic.mk_conj (map (fn c => Bound 0 $ c) cs')))) ctx3
    val (thm3, ctx5) = define_overloaded ("enum_ex_" ^ tname, mk_def dummyT (@{const_name "enum_class.enum_ex"}) (Abs ("P", dummyT, foldl1 HOLogic.mk_disj (map (fn c => Bound 0 $ c) cs')))) ctx4
    val exhaust = Proof_Context.get_thm ctx5 (tname ^ ".exhaust");
    fun mk_def ty x v = Const ("Pure.eq", ty --> ty --> Term.propT) $ Free (x, ty) $ v;
    (* FIXME: The following proof relies on the splitting variable being called "x"; if it breaks this is probably why *)
    val thy1 = Class.prove_instantiation_exit
          (fn _ => EVERY [Class.intro_classes_tac ctx5 [], auto_tac (fold Simplifier.add_simp ([thm1, thm2, thm3]) ctx5), ALLGOALS (fn i => Induct_Tacs.case_tac ctx5 "x" [] NONE i THEN auto_tac ctx5)]) ctx5;
    val ctx6 = Class.instantiation_cmd ([tname], [], "default") thy1;
    val (_, ctx7) = Specification.definition (SOME (Binding.name ("default_" ^ tname), NONE, NoSyn)) [] [] ((Binding.empty, []), mk_def dummyT ("default_" ^ tname) (nth cs' 0)) ctx6
        
  in
    Class.prove_instantiation_exit (fn _ => Class.intro_classes_tac ctx7 []) ctx7
  end
end