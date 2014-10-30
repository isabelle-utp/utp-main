header {* Automation for Record Based Interfaces *}
theory Record_Intf
  imports Main ICF_Tools Ord_Code_Preproc
begin

text {* The ICF uses coercions to simulate multiple inheritance of
  operation records *}
declare [[coercion_enabled]]

lemma icf_rec_def_rule: "\<lbrakk>sel B = x; A\<equiv>B \<rbrakk> \<Longrightarrow> sel A = x " by auto

ML_val Context.mapping


ML {*
signature RECORD_INTF = sig
  val get_unf_ss: Context.generic -> simpset
  val get_unf_thms: Context.generic -> thm list

  val add_unf_thms: thm list -> Context.generic -> Context.generic
  val add_unf_thms_global: thm list -> theory -> theory

  val icf_rec_def: thm -> Context.generic -> Context.generic
  val icf_rec_def_attr: attribute context_parser

  val icf_locales_tac: Proof.context -> tactic

  val setup: theory -> theory
end;

structure Record_Intf: RECORD_INTF = struct
  open ICF_Tools;

  structure Data = Generic_Data
  (
    type T = simpset;
    val empty = HOL_basic_ss (*addsimprocs 
      [Record.simproc, Record.upd_simproc]*);
    val extend = I;
    val merge = Raw_Simplifier.merge_ss;
  );

  structure CppSS = Oc_Simpset (
    val prio = 2;
    val name = "Record_Intf";
  );

  fun get_unf_ss context = Data.get context
  val get_unf_thms = Data.get #> Raw_Simplifier.dest_ss #> #simps #> map #2

  fun add_unf_thms thms context = let
    val ctxt = Context.proof_of context
    fun add ss = simpset_of (put_simpset ss ctxt addsimps thms)
  in
    context 
    |> Data.map add
    |> Context.mapping (CppSS.map add) I
  end

  fun add_unf_thms_global thms = Context.theory_map (add_unf_thms thms);
  
  (* Gather select_conv-, defs- and simps-theorems for given type *)
  fun gather_conv_thms thy typ = let
    val infos = Record.dest_recTs typ 
      |> map fst |> map Long_Name.qualifier |> map (Record.the_info thy);
    val cs = map #select_convs infos |> flat |> map (Thm.transfer thy);
    val ds = map #defs infos @ map #simps infos |> flat 
      |> map (Thm.transfer thy);
  in (cs,ds) end

  (* Gather select_conv theorems type of constant defined by def_thm *)
  fun gather_conv_thms_dt thy def_thm =
    def_thm |> prop_of |> Logic.dest_equals |> fst 
    |> fastype_of |> gather_conv_thms thy;

  (* Generate code-unfold theorems for definition
    and remove definition from
    code equations. *)

  local
    fun unf_thms_of def_thm context = let
      val ctxt = Context.proof_of context;
      val thy = Context.theory_of context;
      
      val def_thm = norm_def_thm def_thm;

      val (conv_thms, simp_thms) = gather_conv_thms_dt thy def_thm;
      val ss = put_simpset (get_unf_ss context) ctxt addsimps simp_thms
      (*val simp_thms = icf_rec_unf.get ctxt @ simp_thms;*)

      val unf_thms = conv_thms 
        |> map (
          chead_of_thm 
          #> inst_meta_cong 
          #> (fn thm => thm OF [def_thm])
          #> simplify ss
        )
        |> filter (not o Thm.is_reflexive);

    in unf_thms end;

  in
    fun icf_rec_def def_thm context = let
      val unf_thms = unf_thms_of def_thm context;
  
      val context = add_unf_thms unf_thms context
        |> Context.mapping (Code.del_eqn def_thm) I;
    in
      context
    end;
  
  end

  val icf_rec_def_attr : attribute context_parser = 
    Scan.succeed (Thm.declaration_attribute icf_rec_def);


  fun icf_locales_tac ctxt = let
    val ss = put_simpset (get_unf_ss (Context.Proof ctxt)) ctxt
    val wits = Locale.get_witnesses ctxt
    val thms = map (simplify ss) wits;
  in ALLGOALS (TRY o (simp_tac ss THEN' resolve_tac thms)) end


  fun setup_simprocs thy = let
    val ctxt = Proof_Context.init_global thy
    val ss = put_simpset HOL_basic_ss ctxt
      addsimprocs [Record.simproc, Record.upd_simproc]
      |> simpset_of

  in
    Data.map (K ss) (Context.Theory thy) |> Context.the_theory
  end


  val setup = Global_Theory.add_thms_dynamic 
    (@{binding icf_rec_unf}, get_unf_thms)
  #> CppSS.setup
  #> setup_simprocs;


end;
*}

setup {* Record_Intf.setup *}

text {*
  Sets up unfolding for an operation record definition.
  New operation record definitions should be declared as 
  @{text "[icf_rec_def]"}.
*}
attribute_setup icf_rec_def = {* Record_Intf.icf_rec_def_attr *} 
  "ICF: Setup unfolding for record definition"

method_setup icf_locales = {*
  Scan.succeed (fn ctxt => SIMPLE_METHOD (Record_Intf.icf_locales_tac ctxt))
*} "ICF: Normalize records and discharge locale subgoals"

end

