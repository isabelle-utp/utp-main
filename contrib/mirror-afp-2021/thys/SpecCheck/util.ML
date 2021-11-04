(*  Title:      SpecCheck/util.ML
    Author:     Kevin Kappelmann

General utility functions for SpecCheck.
*)

signature SPECCHECK_UTIL =
sig

val spaces : string list -> string

end

structure SpecCheck_Util : SPECCHECK_UTIL =
struct

val spaces = space_implode " "

end
