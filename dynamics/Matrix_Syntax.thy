section \<open> Matrix Syntax \<close>

theory Matrix_Syntax
  imports "HOL-Analysis.Analysis"
begin

text \<open> This theory introduces nice syntax for concrete matrices, in the style of MATLAB or SAGE. \<close>

translations
  (type) "'a^'n" <= (type) "('a, 'n) vec"

notation transpose ("_\<^sup>T" [999] 999)

definition scalar :: "real \<Rightarrow> real^1" where "scalar x = (\<chi> i. x)" 

declare [[coercion scalar]]

definition of_scalar :: "real^1 \<Rightarrow> real" where "of_scalar M = M$1"

lemma [simp]: "of_scalar (scalar x) = x"
  by (simp add: scalar_def of_scalar_def)

class nat = finite +
  fixes nat_of :: "'a \<Rightarrow> nat"
  assumes nat_of: "nat_of ` UNIV = {0..<CARD('a)}"
begin

abbreviation "of_nat' \<equiv> inv nat_of"

lemma inj_nat_of: "inj nat_of"
  using nat_of
  apply (rule_tac inj_onI)
  apply (auto)
  by (simp add: eq_card_imp_inj_on inj_eq)

lemma "of_nat' (nat_of x) = x"
  by (simp add: inj_nat_of)

lemma bij_nat_of: "bij_betw nat_of UNIV {0..<CARD('a)} "
  using bij_betw_def inj_nat_of local.nat_of by blast

end

abbreviation "Abs_bit0n \<equiv> (\<lambda> x. Abs_bit0 (int x))"
abbreviation "Rep_bit0n \<equiv> (\<lambda> x. nat (Rep_bit0 x))"

abbreviation "Abs_bit1n \<equiv> (\<lambda> x. Abs_bit1 (int x))"
abbreviation "Rep_bit1n \<equiv> (\<lambda> x. nat (Rep_bit1 x))"

lemma Rep_bit1n:
  fixes x :: "'a::finite bit1"
  shows "Rep_bit1n x \<in> {0..<1 + 2 * CARD('a)}"
  by (auto, metis (full_types) bit1.Rep_0 bit1.Rep_less_n card_bit1 int_nat_eq nat_less_as_int)

interpretation bit0n_type:
  type_definition "Rep_bit0n :: 'a::finite bit0 \<Rightarrow> nat" Abs_bit0n "{0..<2 * CARD('a)}"
proof
  fix x :: "'a bit0"
  show "Rep_bit0n x \<in> {0::nat..<(2::nat) * CARD('a)}"
    by (auto, metis bit0.Rep_0 bit0.Rep_less_n card_bit0 int_nat_eq nat_less_as_int)
  show "Abs_bit0n (Rep_bit0n x) = x"
    using Rep_bit0 Rep_bit0_inverse by auto
  show "\<And>y::nat. y \<in> {0::nat..<(2::nat) * CARD('a)} \<Longrightarrow> Rep_bit0n (Abs_bit0n y :: 'a bit0) = y"
    by (auto simp add: bit0.Abs_inverse)
qed

interpretation bit1n_type:
  type_definition "Rep_bit1n :: 'a::finite bit1 \<Rightarrow> nat" Abs_bit1n "{0..<1 + 2 * CARD('a)}"
proof
  fix x :: "'a bit1"
  show "Rep_bit1n x \<in> {0::nat..<1 + (2::nat) * CARD('a)}"
    by (auto, metis (full_types) bit1.Rep_0 bit1.Rep_less_n card_bit1 int_nat_eq nat_less_as_int)
  show "Abs_bit1n (Rep_bit1n x) = x"
    using Rep_bit1 Rep_bit1_inverse by auto    
  show "\<And> y. y \<in> {0..<1 + 2 * CARD('a)} \<Longrightarrow> Rep_bit1n (Abs_bit1n y :: 'a bit1) = y"
    by (auto simp add: bit1.Abs_inverse)
qed

instantiation num1 :: nat
begin
definition "nat_of_num1 (x::num1) = (0::nat)"
instance
  by (intro_classes, simp add: nat_of_num1_def)
end

instantiation bit0 :: (finite) nat
begin
definition "nat_of_bit0 = Rep_bit0n"
instance
  by (intro_classes, simp add: nat_of_bit0_def bit0n_type.Rep_range)
end

instantiation bit1 :: (finite) nat
begin
definition "nat_of_bit1 = Rep_bit1n"
instance
  by (intro_classes, simp add: nat_of_bit1_def bit1n_type.Rep_range)
end

definition Mat :: "'a list list \<Rightarrow> 'a^'m::nat^'n::nat" where
"Mat M = (\<chi> i j. M!nat_of i!nat_of j)"

abbreviation MatT :: "'m::nat itself \<Rightarrow> 'n::nat itself \<Rightarrow> 'a list list \<Rightarrow> 'a^'m::nat^'n::nat" where
"MatT m n \<equiv> Mat"

ML \<open>

structure Matrix_Utils =
struct

    fun mk_bintype n =
      let
        fun mk_bit 0 = \<^type_name>\<open>bit0\<close>
          | mk_bit 1 = \<^type_name>\<open>bit1\<close>;
        fun bin_of n =
          if n = 1 then Type (\<^type_name>\<open>num1\<close>, [])
          else if n = 0 then Type (\<^type_name>\<open>num0\<close>, [])
          else if n = ~1 then raise TERM ("negative type numeral", [])
          else
            let val (q, r) = Integer.div_mod n 2;
            in Type (mk_bit r, [bin_of q]) end;
      in bin_of n end;


fun dest_list_syn (Const (\<^const_syntax>\<open>List.list.Nil\<close>, _)) = []
  | dest_list_syn (Const (\<^const_syntax>\<open>List.list.Cons\<close>, _) $ t $ u) = t :: dest_list_syn u
  | dest_list_syn t = raise TERM ("Matrix rows must be concrete lists", [t]);

  fun check_dim n (Const (\<^const_syntax>\<open>List.list.Cons\<close>, _) $ t $ u) =
    let val cols = (length (dest_list_syn t)) 
    in if (cols = n) then check_dim n u else raise (TERM ("All matrix rows must have the same length", []))
    end |
  check_dim _ (Const (\<^const_syntax>\<open>List.list.Nil\<close>, _)) = 0 |
  check_dim _ _ = raise (TERM ("Matrix rows must be concrete lists", []));

  fun proc_matrix (x as Const (\<^const_syntax>\<open>List.list.Cons\<close>, _) $ t $ u) =
    let val rows = (1 + length (dest_list_syn u))
        val cols = (length (dest_list_syn t))
        val matT = Type (\<^type_name>\<open>vec\<close>, [Type (\<^type_name>\<open>vec\<close>, [Type (\<^type_name>\<open>real\<close>, []), mk_bintype cols]), mk_bintype rows])
        
    in check_dim cols u; if (cols = 0) then raise TERM ("Empty matrix rows are invalid", [])
       else (Const(\<^const_syntax>\<open>Mat\<close>, dummyT --> matT) $ x)
    end |
  proc_matrix (Const (\<^const_syntax>\<open>List.list.Nil\<close>, _)) = raise (TERM ("Empty matrices are invalid", [])) |
  proc_matrix _ = raise Match;
end  
\<close>

syntax 
  "_Matrix"  :: "logic \<Rightarrow> logic" ("Matrix")
  "_MatList" :: "args \<Rightarrow> logic" ("\<^bold>[_\<^bold>]")

parse_translation \<open> 
let fun matrix_tr [t] = Matrix_Utils.proc_matrix (Term_Position.strip_positions t)
      | matrix_tr _ = raise Match in
  [(\<^syntax_const>\<open>_Matrix\<close>, K matrix_tr)] 
  end
\<close>

translations
  "\<^bold>[x\<^bold>]" => "Matrix[x]"
  "\<^bold>[x\<^bold>]" <= "CONST Mat [x]"

term "\<^bold>[[1,2]\<^bold>]"

term "Matrix[[1,2]] ** Matrix[[1],[1]]"

term "\<^bold>[[1,2], [1,2]\<^bold>]"

term "\<^bold>[[1, 2]\<^bold>]\<^sup>T = \<^bold>[[1], [2]\<^bold>]"

end
