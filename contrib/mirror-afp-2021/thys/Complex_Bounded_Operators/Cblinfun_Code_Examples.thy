section \<open>\<open>Cblinfun_Code_Examples\<close> -- Examples and test cases for code generation\<close>

theory Cblinfun_Code_Examples
  imports
    "Complex_Bounded_Operators.Extra_Pretty_Code_Examples"
    Jordan_Normal_Form.Matrix_Impl
    "HOL-Library.Code_Target_Numeral"
    Cblinfun_Code
begin

hide_const (open) Order.bottom Order.top
no_notation Lattice.join (infixl "\<squnion>\<index>" 65)
no_notation Lattice.meet (infixl "\<sqinter>\<index>" 70)

unbundle cblinfun_notation

section \<open>Examples\<close>

subsection \<open>Operators\<close>

value "id_cblinfun :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "1 :: unit ell2 \<Rightarrow>\<^sub>C\<^sub>L unit ell2"

value "id_cblinfun + id_cblinfun :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "0 :: (bool ell2 \<Rightarrow>\<^sub>C\<^sub>L Enum.finite_3 ell2)"

value "- id_cblinfun :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "id_cblinfun - id_cblinfun :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "classical_operator (\<lambda>b. Some (\<not> b))"

value "id_cblinfun = (0 :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2)"

value "2 *\<^sub>R id_cblinfun :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "imaginary_unit *\<^sub>C id_cblinfun :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "id_cblinfun o\<^sub>C\<^sub>L 0 :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "id_cblinfun* :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

subsection \<open>Vectors\<close>

value "0 :: bool ell2"

value "1 :: unit ell2"

value "ket False"

value "2 *\<^sub>C ket False"

value "2 *\<^sub>R ket False"

value "ket True + ket False"

value "ket True - ket True"

value "ket True = ket True"

value "- ket True"

value "cinner (ket True) (ket True)"

value "norm (ket True)"

value "ket () * ket ()"

value "1 :: unit ell2"

value "(1::unit ell2) * (1::unit ell2)"

subsection \<open>Vector/Matrix\<close>

value "id_cblinfun *\<^sub>V ket True"

value \<open>vector_to_cblinfun (ket True) :: unit ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>

subsection \<open>Subspaces\<close>

value "ccspan {ket False}"

value "Proj (ccspan {ket False})"

value "top :: bool ell2 ccsubspace"

value "bot :: bool ell2 ccsubspace"

value "0 :: bool ell2 ccsubspace"

value "ccspan {ket False} \<squnion> ccspan {ket True}"

value "ccspan {ket False} + ccspan {ket True}"

value "ccspan {ket False} \<sqinter> ccspan {ket True}"

value "id_cblinfun *\<^sub>S ccspan {ket False}"

value "id_cblinfun *\<^sub>S (top :: bool ell2 ccsubspace)" (* Special case, using range_cblinfun_code for efficiency *)

value "- ccspan {ket False}"

value "ccspan {ket False, ket True} = top"

value "ccspan {ket False} \<le> ccspan {ket True}"

value "cblinfun_image id_cblinfun (ccspan {ket True})"

value "kernel id_cblinfun :: bool ell2 ccsubspace"

value "eigenspace 1 id_cblinfun :: bool ell2 ccsubspace"

value "Inf {ccspan {ket False}, top}"

value "Sup {ccspan {ket False}, top}"

end
