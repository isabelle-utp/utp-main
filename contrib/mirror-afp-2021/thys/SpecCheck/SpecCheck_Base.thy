\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>SpecCheck Base\<close>
theory SpecCheck_Base
imports Pure
begin

paragraph \<open>Summary\<close>
text \<open>Basic setup for SpecCheck.\<close>

ML_file \<open>util.ML\<close>

ML_file \<open>speccheck_base.ML\<close>
ML_file \<open>property.ML\<close>
ML_file \<open>configuration.ML\<close>

ML_file \<open>random.ML\<close>

end
