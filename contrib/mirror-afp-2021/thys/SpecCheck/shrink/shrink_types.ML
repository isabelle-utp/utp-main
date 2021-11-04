(*  Title:      SpecCheck/shrink/shrink_types.ML
    Author:     Kevin Kappelmann

Shared type definitions for SpecCheck shrinkable types.
*)

signature SPECCHECK_SHRINK_TYPES =
sig
  type 'a shrink = 'a -> 'a Seq.seq
end

structure SpecCheck_Shrink_Types : SPECCHECK_SHRINK_TYPES =
struct

type 'a shrink = 'a -> 'a Seq.seq

end
