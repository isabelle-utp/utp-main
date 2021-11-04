\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Shrinkers\<close>
theory SpecCheck_Shrink
imports SpecCheck_Generators
begin

paragraph \<open>Summary\<close>
text \<open>Shrinkers for SpecCheck take a value and return a sequence of smaller values derived from it.
Refer to @{file "shrink_base.ML"} for some basic examples.\<close>

ML_file \<open>shrink_types.ML\<close>
ML_file \<open>shrink_base.ML\<close>
ML_file \<open>shrink.ML\<close>

end
