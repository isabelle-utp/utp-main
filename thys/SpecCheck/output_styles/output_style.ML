(*  Title:      SpecCheck/output_styles/output_style.ML
    Author:     Lukas Bulwahn and Nicolai Schaffroth, TU Muenchen
    Author:     Christopher League

Output styles for presenting SpecCheck results.
*)

signature SPECCHECK_DEFAULT_OUTPUT_STYLE =
sig
  include SPECCHECK_OUTPUT_STYLE_TYPES
  val default : 'a output_style
end

structure SpecCheck_Default_Output_Style : SPECCHECK_DEFAULT_OUTPUT_STYLE =
struct

open SpecCheck_Output_Style_Types
val default = SpecCheck_Output_Style_Custom.style

end
