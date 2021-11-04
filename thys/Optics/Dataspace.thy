section \<open> Data spaces \<close>

theory Dataspace
  imports Lenses Prisms
  keywords "dataspace" :: "thy_defn" and "constants" "variables" "channels"
begin

text \<open> A data space is like a more sophisticated version of a locale-based state space. It 
  allows us to introduce both variables, modelled by lenses, and channels, modelled by
  prisms. It also allows local constants, and assumptions over them. \<close>

ML_file "Dataspace.ML"

end