(* Create instance of the type class default for records where every field has a default instance. *)

signature RECORD_DEFAULT_INSTANCE =
sig
  val mk_rec_default_instance: string -> theory -> theory
end

structure Record_Default_Instance : RECORD_DEFAULT_INSTANCE =
struct

open Syntax
open Term
open Proof_Context

fun mk_rec_default_instance tname thy = 
let
  val (Type (qname, _)) = read_type_name {proper = false, strict = false} (init_global thy) tname
  val info = Record.the_info thy qname
  val r_ext = fst (#extension info)
  fun mk_def ty x v = Const ("Pure.eq", ty --> ty --> Term.propT) $ Free (x, ty) $ v;
  val ctx0 = Class.instantiation_cmd ([r_ext], ["default"], "default") thy;
  val Const (make, t) = read_term ctx0 (tname ^ ".make");
  val args = length (Term.binder_types t);
  val Const (extend, _) = read_term ctx0 (tname ^ ".extend");
  val default = @{const_name "default"};
  val def_tm = Syntax.const extend $ (foldl1 (op $) ((const make) :: (replicate args (const default)))) $ const default;
  (* If the chosen record extends a parent, then select the contents of the more field. *)
  val def_tm_ext =
    (case #parent info of
       NONE => def_tm |
       SOME (ts, pname) => Syntax.const (pname ^ ".more") $ def_tm)
  val def_ty = Syntax.read_typ ctx0 ("'a " ^ r_ext);
  val (_, ctx1) = Specification.definition (SOME (Binding.name ("default_" ^ tname ^ "_ext"), NONE, NoSyn)) [] [] ((Binding.empty, []), mk_def def_ty ("default_" ^ tname ^ "_ext") def_tm_ext) ctx0
in Class.prove_instantiation_exit (fn _ => Class.intro_classes_tac ctx1 []) ctx1 end

end