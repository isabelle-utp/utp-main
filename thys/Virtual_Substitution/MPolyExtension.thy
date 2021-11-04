section "Multivariate Polynomials Extension"
theory MPolyExtension
  imports Polynomials.Polynomials (*MPoly_Type_Efficient_Code*) Polynomials.MPoly_Type_Class_FMap
begin

subsection "Definition Lifting"

lift_definition coeff_code::"'a::zero mpoly \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a" is
  "lookup" .

lemma coeff_code[code]: "coeff = coeff_code"
  unfolding coeff_def apply(transfer) by auto

lemma coeff_transfer[transfer_rule]:\<comment> \<open>TODO: coeff should be defined via
lifting, this gives us the illusion\<close>
  "rel_fun cr_mpoly (=) lookup coeff" using coeff_code.transfer[folded
      coeff_code] .

lemmas coeff_add = coeff_add[symmetric]

lemma plus_monom_zero[simp]: "p + MPoly_Type.monom m 0 = p"
  by transfer auto

lift_definition monomials::"'a::zero mpoly \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) set" is
  "Poly_Mapping.keys::((nat\<Rightarrow>\<^sub>0nat) \<Rightarrow>\<^sub>0 'a) \<Rightarrow> _ set" .

lemma mpoly_induct [case_names monom sum]:\<comment> \<open>TODO: overwrites @{thm
mpoly_induct}\<close>
  assumes monom:"\<And>m a. P (MPoly_Type.monom m a)"
    and sum:"(\<And>p1 p2 m a. P p1 \<Longrightarrow> P p2 \<Longrightarrow> p2 = (MPoly_Type.monom m a) \<Longrightarrow> m \<notin> monomials p1
\<Longrightarrow> a \<noteq> 0 \<Longrightarrow> P (p1+p2))"
  shows "P p" using assms
proof (induction p rule: mpoly_induct)
  case (sum p1 p2 m a)
  then show ?case
    by (cases "a = 0") (auto simp: monomials.rep_eq)
qed simp

value "monomials ((Var 0 + Const (3::int) * Var 1)^2)"

lemma Sum_any_lookup_times_eq:
  "(\<Sum>k. ((lookup (x::'a\<Rightarrow>\<^sub>0('b::comm_semiring_1)) (k::'a)) * ((f:: 'a\<Rightarrow>('b::comm_semiring_1)) k))) = (\<Sum>k\<in>keys
x. (lookup x (k::'a)) * (f k))"
  by (subst Sum_any.conditionalize) (auto simp: in_keys_iff intro!:
      Sum_any.cong)

lemma Prod_any_power_lookup_eq:
  "(\<Prod>k::'a. f k ^ lookup (x::'a\<Rightarrow>\<^sub>0nat) k) = (\<Prod>k\<in>keys x. f k ^ lookup x k)"
  by (subst Prod_any.conditionalize) (auto simp: in_keys_iff intro!:
      Prod_any.cong)

lemma insertion_monom: "insertion i (monom m a) = a * (\<Prod>k\<in>keys m. i k ^
lookup m k)"
  by transfer (auto simp: insertion_aux_def insertion_fun_def
      Sum_any_lookup_times_eq Prod_any_power_lookup_eq)

lemma monomials_monom[simp]: "monomials (monom m a) = (if a = 0 then {}
else {m})"
  by transfer auto

lemma finite_monomials[simp]: "finite (monomials m)"
  by transfer auto

lemma monomials_add_disjoint:
  "monomials (a + b) = monomials a \<union> monomials b" if "monomials a \<inter>
monomials b = {}"
  using that
  by transfer (auto simp add: keys_plus_eqI)

lemma coeff_monom[simp]: "coeff (monom m a) m = a"
  by transfer simp

lemma coeff_not_in_monomials[simp]: "coeff m x = 0" if "x \<notin> monomials m"
  using that
  by transfer (simp add: in_keys_iff)

code_thms insertion

lemma insertion_code[code]: "insertion i mp =
   (\<Sum>m\<in>monomials mp. (coeff mp m) * (\<Prod>k\<in>keys m. i k ^ lookup m k))"
proof (induction mp rule: mpoly_induct)
  case (monom m a)
  show ?case
    by (simp add: insertion_monom)
next
  case (sum p1 p2 m a)
  have monomials_add: "monomials (p1 + p2) = insert m (monomials p1)"
    using sum.hyps
    by (auto simp: monomials_add_disjoint)
  have *: "coeff (monom m a) x = 0" if "x \<in> monomials p1" for x
    using sum.hyps that
    by (subst coeff_not_in_monomials) auto
  show ?case
    unfolding insertion_add monomials_add sum.IH
    using sum.hyps
    by (auto simp: coeff_add * algebra_simps)
qed


(* insertion f p
  takes in a mapping from natural numbers to the type of the polynomial and substitutes in
  the constant (f var) for each var variable in polynomial p
*)
code_thms insertion

value "insertion (nth [1, 2.3]) ((Var 0 + Const (3::int) * Var 1)^2)"


(* isolate_variable_sparse p var degree
    returns the coefficient of the term a*var^degree in polynomial p
 *)
lift_definition isolate_variable_sparse::"'a::comm_monoid_add mpoly \<Rightarrow>
nat \<Rightarrow> nat \<Rightarrow> 'a mpoly" is
  "\<lambda>(mp::'a mpoly) x d. sum
     (\<lambda>m. monomial (coeff mp m) (Poly_Mapping.update x 0 m))
     {m \<in> monomials mp. lookup m x = d}" .

lemma Poly_Mapping_update_code[code]: "Poly_Mapping.update a b (Pm_fmap
fm) = Pm_fmap (fmupd a b fm)"
  by (auto intro!: poly_mapping_eqI simp: update.rep_eq
      fmlookup_default_def)


lemma monom_zero [simp] : "monom m 0 = 0"
  by (simp add: coeff_all_0)


lemma remove_key_code[code]: "remove_key v (Pm_fmap fm) = Pm_fmap
(fmdrop v fm)"
  by (auto simp: remove_key_lookup fmlookup_default_def intro!:
      poly_mapping_eqI)
lemma extract_var_code[code]:
  "extract_var p v =
     (\<Sum>m\<in>monomials p. monom (remove_key v m) (monom (Poly_Mapping.single
v (lookup m v)) (coeff p m)))"
  apply (rule extract_var_finite_set[where S="monomials p"])
  using coeff_not_in_monomials by auto
value "extract_var ((Var 0 + Const (3::real) * Var 1)^2) 0"



(* degree p var
  takes in polynomial p and a variable var and finds the degree of that variable in the polynomial
  missing code theorems? still manages to evaluate
*)
code_thms degree
value "degree ((Var 0 + Const (3::real) * Var 1)^2) 0"


(* this function gives a set of all the variables in the polynomial
*)
lemma vars_code[code]: "vars p = \<Union> (keys ` monomials p)"
  unfolding monomials.rep_eq vars_def ..

value "vars ((Var 0 + Const (3::real) * Var 1)^2)"


(* return true if the polynomial contains no variables
*)
fun is_constant :: "'a::zero mpoly \<Rightarrow> bool" where
  "is_constant p = Set.is_empty (vars p)"

value "is_constant (Const (0::int))"


(*
  if the polynomial is constant, returns the real value associated with the polynomial,
  otherwise returns none
*)
fun get_if_const :: "real mpoly \<Rightarrow> real option" where
  "get_if_const p = (if is_constant p then Some (coeff p 0) else None)"

term "coeff p 0"


lemma insertionNegative : "insertion f p = - insertion f (-p)"
  by (metis (no_types, hide_lams) add_eq_0_iff cancel_comm_monoid_add_class.diff_cancel insertion_add insertion_zero uminus_add_conv_diff)  


definition derivative :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly" where
  "derivative x p = (\<Sum>i\<in>{0..degree p x-1}. isolate_variable_sparse p x (i+1) * (Var x)^i * (Const (i+1)))"

text "get\\_coeffs $x$ $p$
  gets the tuple of coefficients $a$ $b$ $c$ of the term $a*x^2+b*x+c$ in polynomial $p$"
fun get_coeffs :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly * real mpoly * real mpoly" where
  "get_coeffs var x = (
  isolate_variable_sparse x var 2,
  isolate_variable_sparse x var 1,
  isolate_variable_sparse x var 0)
"

end
