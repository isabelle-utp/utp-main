signature LENS_UTILS =
sig
  val add_alphabet_cmd : {overloaded: bool} ->
     (string * string option) list * binding ->
       string option -> (binding * string * mixfix) list -> theory -> theory
end;

structure Lens_Utils : LENS_UTILS =
struct

fun read_parent NONE ctxt = (NONE, ctxt)
  | read_parent (SOME raw_T) ctxt =
      (case Proof_Context.read_typ_abbrev ctxt raw_T of
        Type (name, Ts) => (SOME (Ts, name), fold Variable.declare_typ Ts ctxt)
      | T => error ("Bad parent record specification: " ^ Syntax.string_of_typ ctxt T));

fun read_fields raw_fields ctxt =
  let
    val Ts = Syntax.read_typs ctxt (map (fn (_, raw_T, _) => raw_T) raw_fields);
    val fields = map2 (fn (x, _, mx) => fn T => (x, T, mx)) raw_fields Ts;
    val ctxt' = fold Variable.declare_typ Ts ctxt;
  in (fields, ctxt') end;

fun add_record_cmd overloaded (raw_params, binding) raw_parent raw_fields thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val params = map (apsnd (Typedecl.read_constraint ctxt)) raw_params;
    val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
    val (parent, ctxt2) = read_parent raw_parent ctxt1;
    val (fields, ctxt3) = read_fields raw_fields ctxt2;
    val params' = map (Proof_Context.check_tfree ctxt3) params;
  in thy |> Record.add_record overloaded (params', binding) parent fields end;

fun lens_proof x thm =
      Goal.prove_global thm [] [] 
      (hd (Type_Infer_Context.infer_types 
              (Proof_Context.init_global thm) 
              [ Const ("HOL.Trueprop", dummyT) 
              $ (Const ("Lenses.vwb_lens", dummyT) $ Const (Context.theory_name thm ^ "." ^ x, dummyT))]))
      (fn {context, prems} => EVERY [ Locale.intro_locales_tac true context []
                                    , PARALLEL_ALLGOALS (asm_simp_tac (Simplifier.add_simp (Global_Theory.get_thm thm (x ^ "_def")) context))])

fun indep_proof thy (x, y) =
  Goal.prove_global thy [] []
      (hd (Type_Infer_Context.infer_types 
              (Proof_Context.init_global thy) 
              [ Const ("HOL.Trueprop", dummyT) 
              $ ( Const ("Lenses.lens_indep", dummyT) 
                $ Const (Context.theory_name thy ^ "." ^ x, dummyT)
                $ Const (Context.theory_name thy ^ "." ^ y, dummyT)
                )]))
      (fn {context, prems} => EVERY [ Locale.intro_locales_tac true context []
                                    , PARALLEL_ALLGOALS 
                                        (asm_simp_tac (Simplifier.add_simp (Global_Theory.get_thm thy (x ^ "_def")) (Simplifier.add_simp (Global_Theory.get_thm thy (y ^ "_def")) context)))])

fun pairWith _ [] = []
  | pairWith x (y :: ys) = [(x, y), (y, x)] @ pairWith x ys;

fun pairings [] = [] 
  | pairings (x :: xs) = pairWith x xs @ pairings xs;

fun add_alphabet_cmd overloaded (raw_params, binding) raw_parent raw_fields thy =
  let
    val fields = map (fn (x, y, z) => (Binding.suffix_name "_lens" x, y, z)) raw_fields
    val lnames = map (fn (x, _, _) => Binding.name_of x) raw_fields
    val ldefs = map (fn x => x ^ " = FLDLENS " ^ x ^ "_lens") lnames
  in thy |> add_record_cmd overloaded (raw_params, binding) raw_parent fields 
         |> Named_Target.theory_map 
              (fold (fn x => snd o Specification.definition_cmd (NONE, ((Attrib.empty_binding, x))) true) ldefs)
         |> fold (fn x => fn thy => snd (Global_Theory.add_thm ((Binding.make (x ^ "_vwb_lens", Position.none), lens_proof x thy), [Simplifier.simp_add]) thy)) lnames
         |> (fn thy => snd (Global_Theory.add_thmss [((Binding.make (Binding.name_of binding ^ "_indeps", Position.none), map (indep_proof thy) (pairings lnames)), [Simplifier.simp_add])] thy))
         
  end;

val _ =
  Outer_Syntax.command @{command_keyword alphabet} "define record with lenses"
    (Parse_Spec.overloaded -- (Parse.type_args_constrained -- Parse.binding) --
      (@{keyword "="} |-- Scan.option (Parse.typ --| @{keyword "+"}) --
        Scan.repeat1 Parse.const_binding)
    >> (fn ((overloaded, x), (y, z)) =>
        Toplevel.theory (add_alphabet_cmd {overloaded = overloaded} x y z)));
end
