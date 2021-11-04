subsection "Top-Level Algorithms"
theory Exports
  imports Heuristic VSAlgos Optimizations
    (*"HOL-Library.Code_Real_Approx_By_Float"*)
    HOL.String "HOL-Library.Code_Target_Int" "HOL-Library.Code_Target_Nat" PrettyPrinting Show.Show_Real
begin


definition "opt = (push_forall \<circ> nnf \<circ> unpower 0 o clearQuantifiers)"
definition "opt_group = (push_forall \<circ> nnf \<circ> unpower 0 o groupQuantifiers o clearQuantifiers)"

definition "VSLuckiest = opt o (QE_dnf opt (\<lambda>amount. luckiestFind)) o opt"
definition "VSLuckiestBlocks =opt_group o (QE_dnf' opt_group (the_real_step_augment luckiestFind)) o  opt_group"
definition "VSEquality =opt o (QE_dnf opt(\<lambda>x. qe_eq_repeat)) o VSLuckiest o opt "
definition "VSEqualityBlocks =opt_group o (QE_dnf' opt_group (the_real_step_augment qe_eq_repeat)) o VSLuckiestBlocks o opt_group"
definition "VSGeneralBlocks =opt_group o (QE_dnf' opt_group (the_real_step_augment gen_qe))o VSLuckiestBlocks o opt_group"
definition "VSLuckyBlocks =opt_group o (QE_dnf' opt_group (the_real_step_augment luckyFind'))o VSLuckiestBlocks o opt_group"
definition "VSLEGBlocks = VSGeneralBlocks o VSEqualityBlocks o VSLuckyBlocks"
definition "VSEqualityBlocksLimited =opt_group o (QE_dnf opt_group (step_augment qe_eq_repeat IdentityHeuristic)) o VSLuckiestBlocks o opt_group"
definition "VSEquality_3_times = VSEquality o VSEquality o VSEquality"
definition "VSGeneral = opt o (QE_dnf opt (\<lambda>x. gen_qe)) o VSLuckiest o opt"
definition "VSGeneralBlocksLimited = opt_group o (QE_dnf opt_group (step_augment gen_qe IdentityHeuristic)) o VSLuckiestBlocks o opt_group"
definition "VSBrowns = opt_group o (QE_dnf opt_group (step_augment gen_qe brownsHeuristic)) o VSLuckiestBlocks o opt_group"
definition "VSGeneral_3_times = VSGeneral o VSGeneral o VSGeneral"
definition "VSLucky = opt o (QE_dnf opt (\<lambda>amount. luckyFind')) o VSLuckiest o opt"
definition "VSLuckyBlocksLimited = opt_group o (QE_dnf opt_group (step_augment luckyFind' IdentityHeuristic)) o VSLuckiestBlocks o opt_group"
definition "VSLEG = VSGeneral o VSEquality o VSLucky"
definition "VSHeuristic = opt_group o (QE_dnf opt_group (superPicker)) o VSLuckiestBlocks o opt_group"
definition "VSLuckiestRepeat = repeatAmountOfQuantifiers VSLuckiest"


definition add :: "real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly" where
  "add p q = p + q"

definition minus :: "real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly" where
  "minus p q = p - q"

definition mult :: "real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly" where
  "mult p q = p * q"

definition pow :: "real mpoly \<Rightarrow> integer \<Rightarrow> real mpoly" where
  "pow p n = p ^ (nat_of_integer n)"

definition C :: "real \<Rightarrow> real mpoly" where 
  "C r = Const r"

definition V :: "integer \<Rightarrow> real mpoly" where 
  "V n = Var (nat_of_integer n)"

definition real_of_int :: "integer \<Rightarrow> real"
  where "real_of_int n = real (nat_of_integer n)"

definition real_mult :: "real \<Rightarrow> real \<Rightarrow> real"
  where "real_mult n m = n * m"

definition real_div :: "real \<Rightarrow> real \<Rightarrow> real"
  where "real_div n m = n / m"

definition real_plus :: "real \<Rightarrow> real \<Rightarrow> real"
  where "real_plus n m = n + m"

definition real_minus :: "real \<Rightarrow> real \<Rightarrow> real"
  where "real_minus n m = n - m"

fun is_quantifier_free :: "atom fm \<Rightarrow> bool" where
  "is_quantifier_free (ExQ x) =False"|
  "is_quantifier_free (AllQ x) =False"|
  "is_quantifier_free (And a b) =(is_quantifier_free a \<and> is_quantifier_free b)"|
  "is_quantifier_free (Or a b) =(is_quantifier_free a \<and> is_quantifier_free b)"|
  "is_quantifier_free (Neg a) =is_quantifier_free a"|
  "is_quantifier_free a = True"

fun is_solved :: "atom fm \<Rightarrow> bool" where
  "is_solved TrueF = True"|
  "is_solved FalseF = True"|
  "is_solved A = False"

definition print_mpoly :: "(real \<Rightarrow> String.literal)\<Rightarrow> real mpoly \<Rightarrow> String.literal" where
  "print_mpoly f p = String.implode ((shows_mpoly True (\<lambda>x.\<lambda>y. (String.explode o f) x @ y)) p '''')"

definition "Unpower = unpower 0"

export_code
  print_mpoly
  VSGeneral VSEquality VSLucky VSLEG VSLuckiest
  VSGeneralBlocksLimited VSEqualityBlocksLimited VSLuckyBlocksLimited 
  VSGeneralBlocks VSEqualityBlocks VSLuckyBlocks VSLEGBlocks VSLuckiestBlocks
  QE_dnf
  gen_qe qe_eq_repeat
  simpfm push_forall nnf Unpower
  is_quantifier_free is_solved
  add mult C V pow minus
  Eq Or is_quantifier_free 

real_of_int real_mult real_div real_plus real_minus

VSGeneral_3_times VSEquality_3_times VSHeuristic VSLuckiestRepeat VSBrowns
in SML module_name VS

end