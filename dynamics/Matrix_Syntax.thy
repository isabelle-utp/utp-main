section \<open> Matrix Syntax \<close>

theory Matrix_Syntax
  imports Derivative_extra "Differential_Dynamic_Logic.Lib"
begin

text \<open> This theory introduces nice syntax for concrete matrices, in the style of MATLAB or SAGE. 
  We first introduce syntax for matrix and vector types. Vectors are column matrices. \<close>

syntax
  "_MatType" :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type" ("_ mat[_, _]" [999, 0, 0] 999)
  "_VecType" :: "type \<Rightarrow> type \<Rightarrow> type" ("_ vec[_]" [999, 0] 999)

translations
  (type) "'a^'n" <= (type) "('a, 'n) vec"
  (type) "'a mat['m, 'n]" == (type) "'a^'n^'m"
  (type) "'a vec['n]" == (type) "'a mat[1, 'n]"

text \<open> We add standard syntax for some matrix / vector operators. \<close>

notation norm ("\<parallel>_\<parallel>") and infnorm ("\<parallel>_\<parallel>\<^sub>\<infinity>") and transpose ("_\<^sup>T" [999] 999)

text \<open> The following class allows us to link natural numbers and numeral indices. Essentially
  this shows an isomorphism between a numeral type and a finite range of naturals. \<close>

class nat = finite + numeral + zero +
  fixes nat_of :: "'a \<Rightarrow> nat"
  assumes nat_of: "nat_of ` UNIV = {0..<CARD('a)}"
  and nat_of_0 [simp]: "nat_of 0 = 0"
  and nat_of_1 [simp]: "CARD('a) > 1 \<Longrightarrow> nat_of 1 = 1"
  and nat_of_numeral: "nat_of (numeral n) = numeral n mod CARD('a)"
begin

abbreviation "of_nat' \<equiv> inv nat_of"

lemma nat_of_less_CARD [simp]: "nat_of x < CARD('a)"
  using nat_of by auto

lemma nat_of_range: "nat_of i \<in> {0..<CARD('a)}"
  using nat_of by auto

lemma inj_nat_of: "inj nat_of"
  using nat_of
  apply (rule_tac inj_onI)
  apply (auto)
  by (simp add: eq_card_imp_inj_on inj_eq)

lemma nat_of_inv [simp]: "of_nat' (nat_of x) = x"
  by (simp add: inj_nat_of)

lemma of_nat'_inv [simp]: "x < CARD('a) \<Longrightarrow> nat_of (of_nat' x) = x"
  by (simp add: f_inv_into_f local.nat_of)

lemma bij_nat_of: "bij_betw nat_of UNIV {0..<CARD('a)} "
  using bij_betw_def inj_nat_of local.nat_of by blast

lemma nat_of_numeral' [simp]: "numeral n < CARD('a) \<Longrightarrow> nat_of (numeral n) = numeral n"
  by (simp add: local.nat_of_numeral)

end

text \<open> Instances of the @{class nat} class for concrete numerals. \<close>

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
  by (intro_classes, simp_all add: nat_of_num1_def)
end

instantiation bit0 :: (finite) nat
begin
definition "nat_of_bit0 = Rep_bit0n"
instance
  by (intro_classes, simp_all add: nat_of_bit0_def bit0n_type.Rep_range bit0.Rep_0 bit0.Rep_1
     ,simp add: bit0.Rep_numeral nat_int_comparison(1) of_nat_mod)
end

instantiation bit1 :: (finite) nat
begin
definition "nat_of_bit1 = Rep_bit1n"
instance
  by (intro_classes, simp_all add: nat_of_bit1_def bit1n_type.Rep_range bit1.Rep_0 bit1.Rep_1
     ,metis bit1.Rep_numeral card_bit1 int_ops(3) nat_int of_nat_mod)
end

text \<open> Construct a matrix from a list of lists. \<close>

definition Mat :: "'a list list \<Rightarrow> 'a^'m::nat^'n::nat" where
"Mat M = (\<chi> i j. M!nat_of i!nat_of j)"

abbreviation map_mat :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list list \<Rightarrow> 'b list list" where
"map_mat f \<equiv> map (map f)"

lemma Mat_lookup [simp]: "(Mat M)$i$j = M!nat_of i!nat_of j"
  by (simp add: Mat_def)

definition vec_list :: "'a^'n::nat \<Rightarrow> 'a list" where
"vec_list V = map (vec_nth V \<circ> of_nat') [0..<CARD('n)]"

lemma length_vec_list [simp]: "length (vec_list (V::'a^'n::nat)) = CARD('n)"
  by (simp add: vec_list_def)

definition of_Mat :: "'a^'m::nat^'n::nat \<Rightarrow> 'a list list" where
"of_Mat M = map (vec_list \<circ> vec_nth M \<circ> of_nat') [0..<CARD('n)]"

lemma Mat_inverse [simp]:
  assumes "length M = CARD('n)" "\<forall> x \<in> set M. length x = CARD('m)"
  shows "of_Mat (Mat M :: 'a^'m::nat^'n::nat) = M"
  by (auto simp add: Mat_def of_Mat_def comp_def vec_list_def list_eq_iff_nth_eq assms)

lemma matrix_eq_iff: "M = N \<longleftrightarrow> (\<forall> i j. M$i$j = N$i$j)"
  by (auto simp add: vec_eq_iff)

lemma of_Mat_inverse [simp]: "Mat (of_Mat M) = M"
  by (simp add: matrix_eq_iff Mat_def of_Mat_def vec_list_def comp_def)

lemma Mat_eq_iff: "M = N \<longleftrightarrow> of_Mat M = of_Mat N"
  by (metis of_Mat_inverse) 

lemma Mat_eq_iff': 
  "((Mat M)::'a mat['m::nat,'n::nat]) = Mat N \<longleftrightarrow> (\<forall> i < CARD('m). \<forall> j < CARD('n). M!i!j = N!i!j)"
  apply (simp add: matrix_eq_iff)
  apply (auto)
   apply (rename_tac i j)
  apply (drule_tac x="of_nat' i :: 'm" in spec)
   apply (drule_tac x="of_nat' j :: 'n" in spec)
  apply (simp)
  done

text \<open> Can we find a clever way to formulate these? \<close>

lemma scaleR_Mat:
  assumes "length M \<ge> CARD('j)" "\<And> x. x \<in> set(M) \<Longrightarrow> length(x) \<ge> CARD('i)"
  shows "x *\<^sub>R (Mat M :: 'a::real_vector^'i::nat^'j::nat) = Mat (map_mat (scaleR x) M)"
  apply (auto simp add: Mat_def scaleR_vec_def fun_eq_iff)
  apply (subst nth_map)
  apply (simp_all add: assms)
  using assms less_le_trans nat_of_less_CARD apply blast
  apply (subst nth_map)
  apply (meson assms(1) assms(2) less_le_trans nat_of_less_CARD nth_mem)
  apply (simp)
  done

lemma plus_Mat:
  assumes "length M \<ge> CARD('j)" "\<And> x. x \<in> set(M) \<Longrightarrow> length(x) \<ge> CARD('i)"
    "length N \<ge> CARD('j)" "\<And> x. x \<in> set(N) \<Longrightarrow> length(x) \<ge> CARD('i)"
  shows "(Mat M :: 'a::real_vector^'i::nat^'j::nat) + Mat N = Mat (map2 (map2 (+)) M N)"
  apply (simp add: Mat_def plus_vec_def fun_eq_iff)
  apply (subst nth_map)
  apply (simp)
  using assms less_le_trans nat_of_less_CARD apply blast
  apply (subst nth_zip)
  using assms less_le_trans nat_of_less_CARD apply blast
  using assms less_le_trans nat_of_less_CARD apply blast
  apply (simp)
  apply (subst nth_map)
  apply (simp)
   apply (meson assms less_le_trans nat_of_less_CARD nth_mem)
  apply (subst nth_zip)
    apply (auto)
   apply (meson assms less_le_trans nat_of_less_CARD nth_mem)
   apply (meson assms less_le_trans nat_of_less_CARD nth_mem)
  done

text \<open> Matrix derivatives \<close>

lemma frechet_derivative_list_vec:
  assumes "\<And>i. i \<in> {0..<CARD('a::nat)} \<Longrightarrow> (\<lambda>x. M x ! i) differentiable at t"
  shows "\<partial> (\<lambda> x. (\<chi> i::'a. M x!nat_of i)) (at t) = (\<lambda>x. \<chi> i. \<partial> (\<lambda>x. M x ! nat_of i) (at t) x)"
proof -
  have "\<And>i::'a. (\<lambda>x. M x ! nat_of i) differentiable at t"
    using assms nat_of_range by blast
  thus ?thesis
    by (simp add: frechet_derivative_vec)
qed

lemma frechet_derivative_list_mat:
  assumes "\<And>i j. \<lbrakk> i \<in> {0..<CARD('i::nat)}; j \<in> {0..<CARD('j::nat)} \<rbrakk> \<Longrightarrow> (\<lambda>x. M x ! i ! j) differentiable at t"
  shows "\<partial> (\<lambda> x. (\<chi> (i::'i) (j::'j). M x!nat_of i!nat_of j)) (at t) = (\<lambda>x. \<chi> i j. \<partial> (\<lambda>x. M x ! nat_of i ! nat_of j) (at t) x)"
proof -
  have "\<And>(i::'i) (j::'j). (\<lambda>x. M x ! nat_of i ! nat_of j) differentiable at t"
    by (simp add: assms)
  thus ?thesis
    by (simp add: differentiable_vec frechet_derivative_vec)
qed

definition abs_mat ::  "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'b list list) \<Rightarrow> ('a \<Rightarrow> 'b) list list" where
"abs_mat m n M = map (\<lambda> j. map (\<lambda> i x. (M :: 'a \<Rightarrow> 'b list list) x ! j ! i) [0..<n]) [0..<m]"

definition deriv_mat :: 
  "nat \<Rightarrow> nat \<Rightarrow> ('b::real_normed_vector \<Rightarrow> 'a::real_normed_vector list list) \<Rightarrow> 'b filter \<Rightarrow> 'b \<Rightarrow> 'a list list" 
  ("\<partial>\<^sub>M")
  where
    "deriv_mat m n M F x = map_mat (\<lambda> f. \<partial> f F x) (abs_mat m n M)"

syntax
  "_deriv_mat" :: "type \<Rightarrow> type \<Rightarrow> logic" ("\<partial>\<^sub>M'(_, _')")

translations
  "\<partial>\<^sub>M('i, 'j)" == "CONST deriv_mat CARD('i) CARD('j)"

lemma frechet_derivative_mat:
  fixes i :: "'i::nat" and j :: "'j::nat"
  shows "\<partial> (\<lambda>x. M x ! nat_of i ! nat_of j) (at t) = 
         (\<lambda> x. \<partial>\<^sub>M('i,'j) M (at t) x ! nat_of i ! nat_of j)"
  by (simp add: deriv_mat_def abs_mat_def)

lemma frechet_derivative_Mat:
  assumes "\<And>i j. \<lbrakk> i \<in> {0..<CARD('i::nat)}; j \<in> {0..<CARD('j::nat)} \<rbrakk> \<Longrightarrow> (\<lambda>x. M x ! i ! j) differentiable at t"
  shows "\<partial> (\<lambda> x. (Mat (M x) :: _^'j::nat^'i::nat)) (at t) = (\<lambda>x. Mat (\<partial>\<^sub>M('i,'j) M (at t) x))"
  apply (simp add: Mat_def)
  apply (subst frechet_derivative_list_mat)
   apply (simp add: assms)
  apply (subst frechet_derivative_mat)
  apply (simp)
  done

lemma differentiable_Mat:
  assumes "\<And>i j. \<lbrakk> i \<in> {0..<CARD('i::nat)}; j \<in> {0..<CARD('j::nat)} \<rbrakk> \<Longrightarrow> (\<lambda>x. M x ! i ! j) differentiable at t"
  shows "(\<lambda> x. (Mat (M x) :: _^'j::nat^'i::nat)) differentiable (at t)"
proof -
  have "\<And>(i::'i) (j::'j). (\<lambda>x. M x ! nat_of i ! nat_of j) differentiable at t"
    by (simp add: assms)
  thus ?thesis
    by (simp add: Mat_def differentiable_vec frechet_derivative_vec)
qed

text \<open> The following code infers the dimension of the list of lists, checking it corresponds to
  a matrix, and then uses these to construct the type of the matrix -- providing concrete numeral
  dimensions. \<close>

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
        val matT = Type (\<^type_name>\<open>vec\<close>, [Type (\<^type_name>\<open>vec\<close>, [dummyT, mk_bintype cols]), mk_bintype rows])
        
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

text \<open> We can construct matrices either using the form @{term "Matrix[[1,2],[3,4]]"} or alternatively
  using emboldened bracket @{term "\<^bold>[[1,2],[3,4]\<^bold>]"}. Further examples are given below. \<close>

term "\<^bold>[[1::real,2]\<^bold>]"

term "\<^bold>[[1 , 9, -13], 
       [20, 6, 6  ]\<^bold>]" 

term "(**)"

term "Matrix[[1::real,2]] ** Matrix[[1],[1]]"

term "\<^bold>[[1,2], [1,2]\<^bold>]"

term "\<^bold>[[1, 2]\<^bold>]\<^sup>T = \<^bold>[[1], [2]\<^bold>]"

lemma "\<^bold>[[1,2]\<^bold>]$0$0 = 1" "\<^bold>[[1,2]\<^bold>]$0$1 = 2"
  by (simp_all)

end
