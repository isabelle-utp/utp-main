(*  Title:      SpecCheck/configuration.ML
    Author:     Kevin Kappelmann

Configuration options for SpecCheck.
*)

signature SPECCHECK_CONFIGURATION =
sig

  (*maximum number of successful tests before succeeding*)
  val max_success : int Config.T
  (*maximum number of discarded tests per successful test before giving up*)
  val max_discard_ratio : int Config.T
  (*maximum number of shrinks per counterexample*)
  val max_shrinks : int Config.T
  (*number of counterexamples shown*)
  val num_counterexamples : int Config.T
  (*sort counterexamples by size*)
  val sort_counterexamples : bool Config.T
  (*print timing etc. depending on style*)
  val show_stats : bool Config.T

end

structure SpecCheck_Configuration : SPECCHECK_CONFIGURATION =
struct

val max_success = Attrib.setup_config_int \<^binding>\<open>speccheck_max_success\<close> (K 100)

val max_discard_ratio = Attrib.setup_config_int \<^binding>\<open>speccheck_max_discard_ratio\<close> (K 10)

val max_shrinks = Attrib.setup_config_int \<^binding>\<open>speccheck_max_shrinks\<close> (K 10000)

val num_counterexamples = Attrib.setup_config_int \<^binding>\<open>speccheck_num_counterexamples\<close> (K 1)

val sort_counterexamples =
  Attrib.setup_config_bool \<^binding>\<open>speccheck_sort_counterexamples\<close> (K true)

val show_stats = Attrib.setup_config_bool \<^binding>\<open>speccheck_show_stats\<close> (K true)

end
