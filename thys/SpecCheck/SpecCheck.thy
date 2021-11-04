\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>SpecCheck\<close>
theory SpecCheck
imports
  SpecCheck_Generators
  SpecCheck_Show
  SpecCheck_Shrink
  SpecCheck_Output_Style
begin

paragraph \<open>Summary\<close>
text \<open>The SpecCheck (specification based) testing environment and Lecker testing framework.\<close>

ML_file \<open>speccheck.ML\<close>
ML_file \<open>lecker.ML\<close>

end
