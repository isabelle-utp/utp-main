(* Pollutes the global namespace, but we use them everywhere *)
fun ss_only thms ctxt = clear_simpset (put_simpset HOL_basic_ss ctxt) addsimps thms;
fun HOL_ss_only thms ctxt = clear_simpset (put_simpset HOL_ss ctxt) addsimps thms;

signature CIMP =
sig
    val com_locs_fold : (term * 'b -> 'b) -> 'b -> term -> 'b
    val com_locs_map : (term -> 'b) -> term -> 'b list
    val com_locs_fold_no_response : (term * 'b -> 'b) -> 'b -> term -> 'b
    val com_locs_map_no_response : (term -> 'b) -> term -> 'b list
    val intern_com : Facts.ref -> local_theory -> local_theory
    val def_locset : thm -> local_theory -> local_theory
end;

structure Cimp : CIMP =
struct

fun com_locs_fold f x (Const (@{const_name Request}, _) $ l $ _ $ _ )    = f (l, x)
  | com_locs_fold f x (Const (@{const_name Response}, _) $ l $ _)        = f (l, x)
  | com_locs_fold f x (Const (@{const_name LocalOp}, _) $ l $ _)         = f (l, x)
  | com_locs_fold f x (Const (@{const_name Cond1}, _) $ l $ _ $ c)       = com_locs_fold f (f (l, x)) c
  | com_locs_fold f x (Const (@{const_name Cond2}, _) $ l $ _ $ c1 $ c2) = com_locs_fold f (com_locs_fold f (f (l, x)) c1) c2
  | com_locs_fold f x (Const (@{const_name Loop}, _) $ c)                = com_locs_fold f x c
  | com_locs_fold f x (Const (@{const_name While}, _) $ l $ _ $ c)       = com_locs_fold f (f (l, x)) c
  | com_locs_fold f x (Const (@{const_name Seq}, _) $ c1 $ c2)           = com_locs_fold f (com_locs_fold f x c1) c2
  | com_locs_fold f x (Const (@{const_name Choose}, _) $ c1 $ c2)        = com_locs_fold f (com_locs_fold f x c1) c2
  | com_locs_fold _ x _ = x;

fun com_locs_map f com = com_locs_fold (fn (l, acc) => f l :: acc) [] com

fun com_locs_fold_no_response f x (Const (@{const_name Request}, _) $ l $ _ $ _ )    = f (l, x)
  | com_locs_fold_no_response _ x (Const (@{const_name Response}, _) $ _ $ _)        = x (* can often ignore \<open>Response\<close> *)
  | com_locs_fold_no_response f x (Const (@{const_name LocalOp}, _) $ l $ _)         = f (l, x)
  | com_locs_fold_no_response f x (Const (@{const_name Cond1}, _) $ l $ _ $ c)       = com_locs_fold_no_response f (f (l, x)) c
  | com_locs_fold_no_response f x (Const (@{const_name Cond2}, _) $ l $ _ $ c1 $ c2) = com_locs_fold_no_response f (com_locs_fold_no_response f (f (l, x)) c1) c2
  | com_locs_fold_no_response f x (Const (@{const_name Loop}, _) $ c)                = com_locs_fold_no_response f x c
  | com_locs_fold_no_response f x (Const (@{const_name While}, _) $ l $ _ $ c)       = com_locs_fold_no_response f (f (l, x)) c
  | com_locs_fold_no_response f x (Const (@{const_name Seq}, _) $ c1 $ c2)           = com_locs_fold_no_response f (com_locs_fold_no_response f x c1) c2
  | com_locs_fold_no_response f x (Const (@{const_name Choose}, _) $ c1 $ c2)        = com_locs_fold_no_response f (com_locs_fold_no_response f x c1) c2
  | com_locs_fold_no_response _ x _ = x;

fun com_locs_map_no_response f com = com_locs_fold_no_response (fn (l, acc) => f l :: acc) [] com

fun cprop_of_equality ctxt : thm -> cterm =
  Local_Defs.meta_rewrite_rule ctxt (* handle `=` or `\<equiv>` *)
  #> Thm.cprop_of

fun equality_lhs ctxt : thm -> term =
  cprop_of_equality ctxt #> Thm.dest_equals_lhs #> Thm.term_of

fun equality_rhs ctxt : thm -> term =
  cprop_of_equality ctxt #> Thm.dest_equals_rhs #> Thm.term_of

(* Intern all labels mentioned in CIMP programs \<open>facts\<close>

FIXME can only use \<open>com_intern\<close> once per locale
FIXME forces all labels to be unique and distinct from other constants in the locale.
FIXME assumes the labels are character strings
*)
fun intern_com facts ctxt : local_theory =
  let
    val thms = Proof_Context.get_fact ctxt facts
    (* Define constants with defs of the form loc.XXX_def: "XXX \<equiv> ''XXX''. *)
    val attrs = []
    fun add_literal_def (literal, (loc_defs, ctxt)) : thm list * local_theory =
      let
        val literal_name = HOLogic.dest_string literal (* FIXME might not be a nice name, but the error is readable so shrug. FIXME generalise to other label types *)
        val literal_def_binding = Binding.empty (* Binding.qualify true "loc" (Binding.name (Thm.def_name literal_name)) No need to name individual defs *)
        val ((_, (_, loc_def)), ctxt) = Local_Theory.define ((Binding.name literal_name, Mixfix.NoSyn), ((literal_def_binding, attrs), literal)) ctxt
      in
        (loc_def :: loc_defs, ctxt)
      end;
    val (loc_defs, ctxt) = List.foldl (fn (com, acc) => com_locs_fold add_literal_def acc (equality_rhs ctxt com)) ([], ctxt) thms

    val coms_interned = List.map (Local_Defs.fold ctxt loc_defs) thms
    val attrs = []
    val (_, ctxt) = Local_Theory.note ((@{binding "loc_defs"}, attrs), loc_defs) ctxt
    val (_, ctxt) = Local_Theory.note ((@{binding "com_interned"}, attrs), coms_interned) ctxt
  in
    ctxt
  end;

(* Cache location set membership facts.

Decide membership in the given set for each label in the CIMP programs
in the Named_Theorems "com".

If the label set and com types differ, we probably get a nasty error.

*)

fun def_locset thm ctxt =
  let
    val set_name = equality_lhs ctxt thm
    val set_name_str = case set_name of Const (c, _) => c | Free (c, _) => c | _ => error ("Not an equation of the form x = set: " ^ Thm.string_of_thm ctxt thm)
    val memb_thm_name = Binding.qualify true set_name_str (Binding.name "memb")
    fun mk_memb l = Thm.cterm_of ctxt (HOLogic.mk_mem (l, set_name))
(*
1. solve atomic membership yielding \<open>''label'' \<in> set\<close> or \<open>''label'' \<notin> set\<close>.
2. fold \<open>loc_defs\<close>
3. cleanup with the existing \<open>locset_cache\<close>.
FIXME trim simpsets: 1: sets 2: not much 3: not much
*)
    val loc_defs = Proof_Context.get_fact ctxt (Facts.named "loc_defs")
    val membership_ctxt = ctxt addsimps ([thm] @ loc_defs)
    val cleanup_ctxt = HOL_ss_only (@{thms cleanup_simps} @ Named_Theorems.get ctxt \<^named_theorems>\<open>locset_cache\<close>) ctxt
    val rewrite_tac =
          Simplifier.rewrite membership_ctxt
          #> Local_Defs.fold ctxt loc_defs
          #> Simplifier.simplify cleanup_ctxt
    val coms = Proof_Context.get_fact ctxt (Facts.named "com_interned")
(* Parallel *)
    fun mk_thms coms : thm list = Par_List.map rewrite_tac (maps (equality_rhs ctxt #> com_locs_map_no_response mk_memb) coms)
(* Sequential *)
(*    fun mk_thms coms = List.foldl (fn (c, thms) => com_locs_fold (fn l => fn thms => rewrite_tac (mk_memb l) :: thms) thms c) [] coms *)
    val attrs = []
    val (_, ctxt) = ctxt |> Local_Theory.note ((memb_thm_name, attrs), mk_thms coms)
(* Add \<open>memb_thms\<close> to the global (and inherited by locales) \<open>locset_cache\<close> *)
    val memb_thm_full_name = Local_Theory.full_name ctxt memb_thm_name
    val (finish, ctxt) = Target_Context.switch_named_cmd (SOME ("-", Position.none)) (Context.Proof ctxt) (* switch to the "root" local theory *)
    val memb_thms = Proof_Context.get_fact ctxt (Facts.named memb_thm_full_name)
    val attrs = [Attrib.internal (K (Named_Theorems.add \<^named_theorems>\<open>locset_cache\<close>))]
    val (_, ctxt) = ctxt |> Local_Theory.note ((Binding.empty, attrs), memb_thms)
    val ctxt = case finish ctxt of Context.Proof ctxt => ctxt | _ => error "Context.generic failure" (* Return to the locale we were in *)
  in
    ctxt
  end;

end;

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>intern_com\<close> "intern labels in CIMP commands"
    (Parse.thms1 >> (fn facts => fn ctxt => List.foldl (fn ((f, _), ctxt) => Cimp.intern_com f ctxt) ctxt facts));

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>locset_definition\<close> "constant definition for sets of locations"
    (Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
      Parse_Spec.if_assumes -- Parse.for_fixes >> (fn (((decl, spec), prems), params) => fn b => fn lthy =>
        Specification.definition_cmd decl params prems spec b lthy
        |> (fn ((_, (_, thm)), lthy) => (thm, lthy)) |> uncurry Cimp.def_locset));
