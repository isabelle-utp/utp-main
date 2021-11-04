\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Generators\<close>
theory SpecCheck_Generators
imports SpecCheck_Base
begin

paragraph \<open>Summary\<close>
text \<open>Generators for SpecCheck take a state and return a pair consisting of a generated value and
a new state. Refer to @{file "gen_base.ML"} for the most basic combinators.\<close>

ML_file \<open>gen_types.ML\<close>
ML_file \<open>gen_base.ML\<close>
ML_file \<open>gen_text.ML\<close>
ML_file \<open>gen_int.ML\<close>
ML_file \<open>gen_real.ML\<close>
ML_file \<open>gen_function.ML\<close>
ML_file \<open>gen_term.ML\<close>
ML_file \<open>gen.ML\<close>

end
