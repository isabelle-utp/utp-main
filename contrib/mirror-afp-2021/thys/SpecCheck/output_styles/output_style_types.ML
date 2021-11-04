(*  Title:      SpecCheck/output_styles/output_style_types.ML
    Author:     Lukas Bulwahn and Nicolai Schaffroth, TU Muenchen
    Author:     Christopher League

Shared types for SpecCheck output styles.
*)
signature SPECCHECK_OUTPUT_STYLE_TYPES =
sig
  type 'a output_style = 'a SpecCheck_Show.show option -> Proof.context -> string ->
    Timing.timing -> 'a SpecCheck_Base.result -> unit
end

structure SpecCheck_Output_Style_Types : SPECCHECK_OUTPUT_STYLE_TYPES =
struct

type 'a output_style = 'a SpecCheck_Show.show option -> Proof.context -> string -> Timing.timing ->
  'a SpecCheck_Base.result -> unit

end

signature SPECCHECK_OUTPUT_STYLE =
sig
  val style : 'a SpecCheck_Output_Style_Types.output_style
end
