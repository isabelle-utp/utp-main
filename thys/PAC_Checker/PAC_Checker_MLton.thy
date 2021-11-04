(*
  File:         PAC_Checker_MLton.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Checker_MLton
  imports PAC_Checker_Synthesis
begin

export_code PAC_checker_l_impl PAC_update_impl PAC_empty_impl the_error is_cfailed is_cfound
  int_of_integer Del Add Mult nat_of_integer String.implode remap_polys_l_impl
  fully_normalize_poly_impl union_vars_poly_impl empty_vars_impl
  full_checker_l_impl check_step_impl CSUCCESS
  Extension hashcode_literal' version
  in SML_imp module_name PAC_Checker
  file_prefix "checker"

text \<open>Here is how to compile it:\<close>
compile_generated_files _
  external_files
    \<open>code/parser.sml\<close>
    \<open>code/pasteque.sml\<close>
    \<open>code/pasteque.mlb\<close>
  where \<open>fn dir =>
    let
      val exec = Generated_Files.execute (dir + Path.basic "code");
      val _ =
        exec \<open>Compilation\<close>
          (File.bash_path \<^path>\<open>$ISABELLE_MLTON\<close> ^ " " ^
            "-const 'MLton.safe false' -verbose 1 -default-type int64 -output pasteque " ^
            "-codegen native -inline 700 -cc-opt -O3 pasteque.mlb");
    in () end\<close>

end