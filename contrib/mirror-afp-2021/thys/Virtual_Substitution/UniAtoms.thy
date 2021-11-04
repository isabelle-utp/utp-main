section "General VS Proofs"
subsection "Univariate Atoms"
theory UniAtoms
  imports Debruijn
begin

datatype atomUni = LessUni "real * real * real" | EqUni "real * real * real" | LeqUni "real * real * real" | NeqUni "real * real * real"
datatype (atoms: 'a) fmUni =
  TrueFUni | FalseFUni | AtomUni 'a | AndUni "'a fmUni" "'a fmUni" | OrUni "'a fmUni" "'a fmUni" 

fun aEvalUni :: "atomUni \<Rightarrow> real \<Rightarrow> bool" where
  "aEvalUni (EqUni (a,b,c)) x = (a*x^2+b*x+c = 0)" |
  "aEvalUni (LessUni (a,b,c)) x = (a*x^2+b*x+c < 0)" |
  "aEvalUni (LeqUni (a,b,c)) x = (a*x^2+b*x+c \<le> 0)" |
  "aEvalUni (NeqUni (a,b,c)) x = (a*x^2+b*x+c \<noteq> 0)"

fun aNegUni :: "atomUni \<Rightarrow> atomUni" where
  "aNegUni (LessUni (a,b,c)) = LeqUni (-a,-b,-c)" |
  "aNegUni (EqUni p) = NeqUni p" |
  "aNegUni (LeqUni (a,b,c)) = LessUni (-a,-b,-c)" |
  "aNegUni (NeqUni p) = EqUni p"


fun evalUni :: "atomUni fmUni \<Rightarrow> real \<Rightarrow> bool" where
  "evalUni (AtomUni a) x = aEvalUni a x" |
  "evalUni (TrueFUni) _ = True" |
  "evalUni (FalseFUni) _ = False" |
  "evalUni (AndUni \<phi> \<psi>) x = ((evalUni \<phi> x) \<and> (evalUni \<psi> x))" |
  "evalUni (OrUni \<phi> \<psi>) x = ((evalUni \<phi> x) \<or> (evalUni \<psi> x))"


fun negUni :: "atomUni fmUni \<Rightarrow> atomUni fmUni" where
  "negUni (AtomUni a) = AtomUni(aNegUni a)" |
  "negUni (TrueFUni) = FalseFUni" |
  "negUni (FalseFUni) = TrueFUni" |
  "negUni (AndUni \<phi> \<psi>) = (OrUni (negUni \<phi>) (negUni \<psi>))" |
  "negUni (OrUni \<phi> \<psi>) = (AndUni (negUni \<phi>) (negUni \<psi>))"

fun convert_poly :: "nat \<Rightarrow> real mpoly \<Rightarrow> real list \<Rightarrow> (real * real * real) option" where
  "convert_poly var p xs = (
  if MPoly_Type.degree p var < 3
  then let (A,B,C) = get_coeffs var p in Some(insertion (nth_default 0 (xs)) A,insertion (nth_default 0 (xs)) B,insertion (nth_default 0 (xs)) C)
 else None)"

fun convert_atom :: "nat \<Rightarrow> atom \<Rightarrow> real list \<Rightarrow> atomUni option" where
  "convert_atom var (Less p) xs = map_option LessUni (convert_poly var p xs)"|
  "convert_atom var (Eq p) xs = map_option EqUni (convert_poly var p xs)"|
  "convert_atom var (Leq p) xs = map_option LeqUni (convert_poly var p xs)"|
  "convert_atom var (Neq p) xs = map_option NeqUni (convert_poly var p xs)"

lemma convert_atom_change :
  assumes "length xs' = var"
  shows "convert_atom var At (xs' @ x # \<Gamma>) = convert_atom var At (xs' @ x' # \<Gamma>)"
  apply(cases At)using assms apply simp_all
  by (metis insertion_lowerPoly1 not_in_isovarspar)+

lemma degree_convert_eq : 
  assumes "convert_poly var p xs = Some(a)"
  shows "MPoly_Type.degree p var < 3"
  using assms apply(cases "MPoly_Type.degree p var < 3") by auto

lemma poly_to_univar :
  assumes "MPoly_Type.degree p var < 3"
  assumes "get_coeffs var p = (A,B,C)"
  assumes "a = insertion (nth_default 0 (xs'@y#xs)) A"
  assumes "b = insertion (nth_default 0 (xs'@y#xs)) B"
  assumes "c = insertion (nth_default 0 (xs'@y#xs)) C"
  assumes "length xs' = var"
  shows "insertion (nth_default 0 (xs'@x#xs)) p = (a*x^2)+(b*x)+c"
proof-
  have ha: "\<And>x. a = insertion (nth_default 0 (xs'@x # xs)) A" using assms(2) apply auto
    by (metis assms(3) assms(6) insertion_lowerPoly1 not_in_isovarspar)
  have hb: "\<And>x. b = insertion (nth_default 0 (xs'@x # xs)) B" using assms(2) apply auto
    by (metis assms(4) assms(6) insertion_lowerPoly1 not_in_isovarspar)
  have hc: "\<And>x. c = insertion (nth_default 0 (xs'@x # xs)) C" using assms(2) apply auto
    by (metis assms(5) assms(6) insertion_lowerPoly1 not_in_isovarspar)
  show ?thesis
  proof(cases "MPoly_Type.degree p var = 0")
    case True
    have h1 : "var < length (xs'@x#xs)" using assms by auto
    show ?thesis using assms ha hb hc sum_over_degree_insertion[OF h1 True, of y] apply(simp add: isovar_greater_degree[of p ] True)
      using True degree0isovarspar by force
  next
    case False
    then have notzero : "MPoly_Type.degree p var \<noteq> 0" by auto
    show ?thesis proof(cases "MPoly_Type.degree p var = 1" )
      case True
      have h1 : "var < length (xs'@x#xs)" using assms by auto
      show ?thesis using  sum_over_degree_insertion[OF h1 True, of x,  symmetric] unfolding assms(6)[symmetric] list_update_length unfolding assms(6) apply simp using ha hb hc assms apply auto
        by (smt (verit, ccfv_threshold) One_nat_def True express_poly h1 insertion_add insertion_mult insertion_pow insertion_var list_update_length)    
    next
      case False
      then have deg2 : "MPoly_Type.degree p var = 2" using notzero assms by auto
      have h1 : "var < length (xs'@x#xs)" using assms by auto
      have two : "2 = Suc(Suc 0)" by auto
      show ?thesis
        using  sum_over_degree_insertion[OF h1 deg2, of x,  symmetric] unfolding assms(6)[symmetric] list_update_length unfolding assms(6) two apply simp using ha hb hc assms apply auto
        using deg2 express_poly h1 insertion_add insertion_mult insertion_pow insertion_var list_update_length
        by (smt (verit, best) numeral_2_eq_2)
    qed
  qed
qed

lemma "aEval_aEvalUni":
  assumes "convert_atom var a (xs'@x#xs) = Some a'"
  assumes "length xs' = var"
  shows "aEval a (xs'@x#xs) = aEvalUni a' x"
proof(cases a)
  case (Less x)
  then show ?thesis
  proof(cases "MPoly_Type.degree x var < 3")
    case True
    then show ?thesis
      using assms apply(simp add:Less)
      using poly_to_univar[OF True]
      by (metis One_nat_def aEvalUni.simps(2) get_coeffs.elims) 
  next
    case False
    then show ?thesis using assms Less by auto
  qed
next
  case (Eq x)
  then show ?thesis
  proof(cases "MPoly_Type.degree x var < 3")
    case True
    then show ?thesis
      using assms apply(simp add:Eq)
      using poly_to_univar[OF True]
      by (metis One_nat_def aEvalUni.simps(1) get_coeffs.elims) 
  next
    case False
    then show ?thesis using assms Eq by auto
  qed
next
  case (Leq x)
  then show ?thesis
  proof(cases "MPoly_Type.degree x var < 3")
    case True
    then show ?thesis
      using assms apply(simp add:Leq)
      using poly_to_univar[OF True]
      by (metis One_nat_def aEvalUni.simps(3) get_coeffs.elims) 
  next
    case False
    then show ?thesis using assms Leq by auto
  qed
next
  case (Neq x)
  then show ?thesis
  proof(cases "MPoly_Type.degree x var < 3")
    case True
    then show ?thesis
      using assms apply(simp add:Neq)
      using poly_to_univar[OF True]
      by (metis One_nat_def aEvalUni.simps(4) get_coeffs.elims) 
  next
    case False
    then show ?thesis using assms Neq by auto
  qed
qed


fun convert_fm :: "nat \<Rightarrow> atom fm \<Rightarrow> real list \<Rightarrow> (atomUni fmUni) option" where
  "convert_fm var (Atom a) \<Gamma> = map_option (AtomUni) (convert_atom var a \<Gamma>)" |
  "convert_fm var (TrueF) _ = Some TrueFUni" |
  "convert_fm var (FalseF) _ = Some FalseFUni" |
  "convert_fm var (And \<phi> \<psi>) \<Gamma> = (case ((convert_fm var \<phi> \<Gamma>),(convert_fm var \<psi> \<Gamma>)) of (Some a, Some b) \<Rightarrow> Some (AndUni a b) | _ \<Rightarrow> None)" |
  "convert_fm var (Or \<phi> \<psi>) \<Gamma> = (case ((convert_fm var \<phi> \<Gamma>),(convert_fm var \<psi> \<Gamma>)) of (Some a, Some b) \<Rightarrow> Some (OrUni a b) | _ \<Rightarrow> None)" |
  "convert_fm var (Neg \<phi>) \<Gamma> = None " |
  "convert_fm var (ExQ \<phi>) \<Gamma> = None" |
  "convert_fm var (AllQ \<phi>) \<Gamma> = None"|
  "convert_fm var (AllN i \<phi>) \<Gamma> = None"|
  "convert_fm var (ExN i \<phi>) \<Gamma> = None"


lemma "eval_evalUni":
  assumes "convert_fm var F (xs'@x#xs) = Some F'"
  assumes "length xs' = var"
  shows "eval F (xs'@x#xs) = evalUni F' x"
  using assms
proof(induction F arbitrary: F')
  case TrueF
  then show ?case by auto
next
  case FalseF
  then show ?case by auto
next
  case (Atom x)
  then show ?case using aEval_aEvalUni by auto
next
  case (And F1 F2)
  then show ?case apply(cases "convert_fm var F1 (xs'@x#xs)") apply simp apply(cases "convert_fm var F2 (xs'@x#xs)") by auto
next
  case (Or F1 F2)
  then show ?case apply(cases "convert_fm var F1 (xs'@x#xs)") apply simp apply(cases "convert_fm var F2 (xs'@x#xs)") by auto
next
  case (Neg F)
  then show ?case by auto
next
  case (ExQ F)
  then show ?case by auto
next
  case (AllQ F)
  then show ?case by auto
next
  case (ExN x1 \<phi>)
  then show ?case by auto
next
  case (AllN x1 \<phi>)
  then show ?case by auto
qed

fun grab_atoms :: "nat \<Rightarrow> atom fm \<Rightarrow> atom list option" where
  "grab_atoms var TrueF = Some([])" |
  "grab_atoms var FalseF = Some([])" |
  "grab_atoms var (Atom(Eq p)) = (if MPoly_Type.degree p var < 3 then (if MPoly_Type.degree p var > 0 then Some([Eq p]) else Some([])) else None)"|
  "grab_atoms var (Atom(Less p)) = (if MPoly_Type.degree p var < 3 then (if MPoly_Type.degree p var > 0 then Some([Less p]) else Some([])) else None)"|
  "grab_atoms var (Atom(Leq p)) = (if MPoly_Type.degree p var < 3 then (if MPoly_Type.degree p var > 0 then Some([Leq p]) else Some([])) else None)"|
  "grab_atoms var (Atom(Neq p)) = (if MPoly_Type.degree p var < 3 then (if MPoly_Type.degree p var > 0 then Some([Neq p]) else Some([])) else None)"|
  "grab_atoms var (And a b) = (
case grab_atoms var a of 
  Some(al) \<Rightarrow> (
    case grab_atoms var b of
      Some(bl) \<Rightarrow> Some(al@bl)
    | None \<Rightarrow> None
  )
| None \<Rightarrow> None
)"|
  "grab_atoms var (Or a b) = (
case grab_atoms var a of 
  Some(al) \<Rightarrow> (
    case grab_atoms var b of
      Some(bl) \<Rightarrow> Some(al@bl)
    | None \<Rightarrow> None
  )
| None \<Rightarrow> None
)"|

"grab_atoms var (Neg _) = None"|
"grab_atoms var (ExQ _) = None"|
"grab_atoms var (AllQ _) = None"|
"grab_atoms var (AllN i _) = None"|
"grab_atoms var (ExN i _) = None"



lemma nil_grab : "(grab_atoms var F = Some []) \<Longrightarrow> (freeIn var F)"
proof(induction F)
  case TrueF
  then show ?case by auto
next
  case FalseF
  then show ?case by auto
next
  case (Atom x)
  then show ?case proof(cases x)
    case (Less p)
    then show ?thesis using Atom apply(cases "MPoly_Type.degree p var < 3") apply auto apply(cases "MPoly_Type.degree p var > 0") apply auto
      using degree0isovarspar not_in_isovarspar by blast
  next
    case (Eq p)
    then show ?thesis using Atom apply(cases "MPoly_Type.degree p var < 3") apply auto apply(cases "MPoly_Type.degree p var > 0") apply auto
      using degree0isovarspar not_in_isovarspar by blast
  next
    case (Leq p)
    then show ?thesis using Atom apply(cases "MPoly_Type.degree p var < 3") apply auto apply(cases "MPoly_Type.degree p var > 0") apply auto
      using degree0isovarspar not_in_isovarspar by blast
  next
    case (Neq p)
    then show ?thesis using Atom apply(cases "MPoly_Type.degree p var < 3") apply auto apply(cases "MPoly_Type.degree p var > 0") apply auto
      using degree0isovarspar not_in_isovarspar by blast
  qed
next
  case (And F1 F2)
  then show ?case apply(cases "grab_atoms var F1")
    apply(cases "grab_atoms var F2") apply(auto)
    apply(cases "grab_atoms var F2") apply(auto)
    apply(cases "grab_atoms var F2") by(auto)
next
  case (Or F1 F2)
  then show ?case apply(cases "grab_atoms var F1")
    apply(cases "grab_atoms var F2") apply(auto)
    apply(cases "grab_atoms var F2") apply(auto)
    apply(cases "grab_atoms var F2") by(auto)
next
  case (Neg F)
  then show ?case by auto
next
  case (ExQ F)
  then show ?case by auto
next
  case (AllQ F)
  then show ?case by auto
next
  case (ExN x1 F)
  then show ?case by auto
next
  case (AllN x1 F)
  then show ?case by auto
qed

fun isSome :: "'a option \<Rightarrow> bool" where
  "isSome (Some _) = True" |
  "isSome None = False"

lemma "grab_atoms_convert" : "(isSome (grab_atoms var F)) = (isSome (convert_fm var F xs))"
proof(induction F)
  case TrueF
  then show ?case by auto
next
  case FalseF
  then show ?case by auto
next
  case (Atom a)
  then show ?case apply(cases a) by auto
next
  case (And F1 F2)
  then show ?case
    by (smt convert_fm.simps(4) grab_atoms.simps(7) isSome.elims(2) isSome.elims(3) option.distinct(1) option.simps(5) option.split_sel_asm prod.simps(2)) 
next
  case (Or F1 F2)
  then show ?case
    by (smt convert_fm.simps(5) grab_atoms.simps(8) isSome.elims(2) isSome.elims(3) option.distinct(1) option.simps(5) option.split_sel_asm prod.simps(2))
next
  case (Neg F)
  then show ?case by auto
next
  case (ExQ F)
  then show ?case by auto
next
  case (AllQ F)
  then show ?case by auto
next
  case (ExN x1 F)
  then show ?case by auto
next
  case (AllN x1 F)
  then show ?case by auto
qed

lemma convert_aNeg :
  assumes "convert_atom var A (xs'@x#xs) = Some(A')"
  assumes "length xs' = var"
  shows "aEval (aNeg A) (xs'@x#xs) = aEvalUni (aNegUni A') x"
proof-
  have "aEval (aNeg A) (xs'@x#xs) = (\<not> aEval A (xs'@x#xs))"
    using aNeg_aEval[of A "(xs'@x#xs)"] by auto
  also have "... = (\<not> aEvalUni A' x)"
    using assms aEval_aEvalUni by auto
  also have "... = aEvalUni (aNegUni A') x"
    by(cases A')(auto)
  finally show ?thesis .
qed

lemma convert_neg : 
  assumes "convert_fm var F (xs'@x#xs) = Some(F')"
  assumes "length xs' = var"
  shows "eval (Neg F) (xs'@x#xs) = evalUni (negUni F') x"
  using assms
proof(induction F arbitrary:F')
  case TrueF
  then show ?case by auto
next
  case FalseF
  then show ?case by auto
next
  case (Atom p)
  then show ?case
    using convert_aNeg[of _ p]
    by (smt aNeg_aEval convert_fm.simps(1) evalUni.simps(1) eval.simps(1) eval.simps(6) map_option_eq_Some negUni.simps(1)) 
next
  case (And F1 F2)
  then show ?case apply auto
    apply (metis (no_types, lifting) evalUni.simps(5) negUni.simps(4) option.case_eq_if option.collapse option.distinct(1) option.sel)
    apply (smt (verit, del_insts) evalUni.simps(5) isSome.elims(1) negUni.simps(4) option.inject option.simps(4) option.simps(5))
    by (smt (verit, del_insts) evalUni.simps(5) isSome.elims(1) negUni.simps(4) option.inject option.simps(4) option.simps(5))
next
  case (Or F1 F2)
  then show ?case apply auto
    apply (smt (verit, del_insts) evalUni.simps(4) isSome.elims(1) negUni.simps(5) option.inject option.simps(4) option.simps(5))
    apply (smt (verit, del_insts) evalUni.simps(4) isSome.elims(1) negUni.simps(5) option.inject option.simps(4) option.simps(5))
    by (smt (verit, del_insts) evalUni.simps(4) isSome.elims(1) negUni.simps(5) option.inject option.simps(4) option.simps(5))
next
  case (Neg F)
  then show ?case by auto
next
  case (ExQ F)
  then show ?case by auto
next
  case (AllQ F)
  then show ?case by auto
next
  case (ExN x1 F)
  then show ?case by auto
next
  case (AllN x1 F)
  then show ?case by auto
qed


fun list_disj_Uni :: "'a fmUni list \<Rightarrow> 'a fmUni" where
  "list_disj_Uni [] = FalseFUni"|
  "list_disj_Uni (x#xs) = OrUni x (list_disj_Uni xs)"

fun list_conj_Uni :: "'a fmUni list \<Rightarrow> 'a fmUni" where
  "list_conj_Uni [] = TrueFUni"|
  "list_conj_Uni (x#xs) = AndUni x (list_conj_Uni xs)"

lemma eval_list_disj_Uni : "evalUni (list_disj_Uni L) x = (\<exists>l\<in>set(L). evalUni l x)"
  by(induction L)(auto)

lemma eval_list_conj_Uni : "evalUni (list_conj_Uni A) x = (\<forall>l\<in>set A. evalUni l x)"
  apply(induction A)by auto

lemma eval_list_conj_Uni_append : "evalUni (list_conj_Uni (A @ B)) x = (evalUni (list_conj_Uni (A)) x \<and> evalUni (list_conj_Uni (B)) x)"
  apply(induction A)by auto

fun map_atomUni :: "('a \<Rightarrow> 'a fmUni) \<Rightarrow> 'a fmUni \<Rightarrow> 'a fmUni" where
  "map_atomUni f (AtomUni a) = f a" |
  "map_atomUni f (TrueFUni) = TrueFUni" |
  "map_atomUni f (FalseFUni) = FalseFUni" |
  "map_atomUni f (AndUni \<phi> \<psi>) = (AndUni (map_atomUni f \<phi>) (map_atomUni f \<psi>))" |
  "map_atomUni f (OrUni \<phi> \<psi>) = (OrUni (map_atomUni f \<phi>) (map_atomUni f \<psi>))"

fun map_atom :: "(atom \<Rightarrow> atom fm) \<Rightarrow> atom fm \<Rightarrow> atom fm" where
  "map_atom f TrueF = TrueF"|
  "map_atom f FalseF = FalseF"|
  "map_atom f (Atom a) = f a"|
  "map_atom f (And \<phi> \<psi>) = And (map_atom f \<phi>) (map_atom f \<psi>)"|
  "map_atom f (Or \<phi> \<psi>) = Or (map_atom f \<phi>) (map_atom f \<psi>)"|
  "map_atom f (Neg \<phi>) = TrueF"|
  "map_atom f (ExQ \<phi>) = TrueF"|
  "map_atom f (AllQ \<phi>) = TrueF"|
  "map_atom f (ExN i \<phi>) = TrueF"|
  "map_atom f (AllN i \<phi>) = TrueF"

fun getPoly :: "atomUni => real * real * real" where
  "getPoly (EqUni p) = p"|
  "getPoly (LeqUni p) = p"|
  "getPoly (NeqUni p) = p"|
  "getPoly (LessUni p) = p"

lemma liftatom_map_atom : 
  assumes "\<exists>F'. convert_fm var F xs = Some F'"
  shows "liftmap f F 0 = map_atom (f 0) F"
  using assms
  apply(induction F)
  apply(auto)
  apply fastforce
  apply (metis (no_types, lifting) isSome.elims(2) isSome.elims(3) option.case_eq_if)
  apply fastforce
  by (metis (no_types, lifting) isSome.elims(2) isSome.elims(3) option.case_eq_if)


lemma eval_map : "(\<exists>l\<in>set(map f L). evalUni l x) = (\<exists>l\<in>set(L). evalUni (f l) x)"
  by auto

lemma eval_map_all : "(\<forall>l\<in>set(map f L). evalUni l x) = (\<forall>l\<in>set(L). evalUni (f l) x)"
  by auto

lemma eval_append : "(\<exists>l\<in>set (A#B).evalUni l x) = (evalUni A x \<or> (\<exists>l\<in>set (B).evalUni l x))"
  by auto

lemma eval_conj_atom : "evalUni (list_conj_Uni (map AtomUni L)) x = (\<forall>l\<in>set(L). aEvalUni l x)"
  unfolding eval_list_conj_Uni
  by auto
end