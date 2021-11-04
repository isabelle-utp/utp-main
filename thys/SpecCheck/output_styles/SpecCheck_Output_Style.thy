\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Output Styles\<close>
theory SpecCheck_Output_Style
imports
  SpecCheck_Base
  SpecCheck_Show
begin


paragraph \<open>Summary\<close>
text \<open>Output styles for SpecCheck take the result of a test run and process it accordingly,
e.g. by printing it or storing it to a file.\<close>


ML_file \<open>output_style_types.ML\<close>
ML_file \<open>output_style_perl.ML\<close>
ML_file \<open>output_style_custom.ML\<close>
ML_file \<open>output_style.ML\<close>

end
