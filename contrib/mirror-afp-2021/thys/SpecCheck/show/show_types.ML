(*  Title:      SpecCheck/show/show_types.ML
    Author:     Kevin Kappelmann

Shared type definitions for SpecCheck showable types.
*)

signature SPECCHECK_SHOW_TYPES =
sig
  type 'a show = 'a -> Pretty.T
end

structure SpecCheck_Show_Types : SPECCHECK_SHOW_TYPES =
struct

type 'a show = 'a -> Pretty.T

end
