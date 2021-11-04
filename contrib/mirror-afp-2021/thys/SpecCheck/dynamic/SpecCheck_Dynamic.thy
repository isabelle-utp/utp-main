\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Dynamic Generators\<close>
theory SpecCheck_Dynamic
imports SpecCheck
begin

paragraph \<open>Summary\<close>
text \<open>Generators and show functions for SpecCheck that are dynamically derived from a given ML input
string. This approach can be handy to quickly test a function during development, but it lacks
customisability and is very brittle. See @{file "../examples/SpecCheck_Examples.thy"} for some
examples contrasting this approach to the standard one (specifying generators as ML code).\<close>

ML_file \<open>dynamic_construct.ML\<close>
ML_file \<open>speccheck_dynamic.ML\<close>

end
