\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Show\<close>
theory SpecCheck_Show
imports Pure
begin

paragraph \<open>Summary\<close>
text \<open>Show functions (pretty-printers) for SpecCheck take a value and return a @{ML_type Pretty.T}
representation of the value. Refer to @{file "show_base.ML"} for some basic examples.\<close>

ML_file \<open>show_types.ML\<close>
ML_file \<open>show_base.ML\<close>
ML_file \<open>show.ML\<close>

end
