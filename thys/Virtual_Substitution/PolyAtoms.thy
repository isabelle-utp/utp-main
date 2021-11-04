section "Atoms"
theory PolyAtoms
  imports ExecutiblePolyProps
begin

subsection "Definition"

datatype (atoms: 'a) fm =
  TrueF | FalseF | Atom 'a | And "'a fm" "'a fm" | Or "'a fm" "'a fm" |
  Neg "'a fm" | ExQ "'a fm" | AllQ "'a fm" | ExN "nat" "'a fm" | AllN "nat" "'a fm"

definition neg where
  "neg \<phi> = (if \<phi>=TrueF then FalseF else if \<phi>=FalseF then TrueF else Neg \<phi>)"

definition "and" :: "'a fm \<Rightarrow> 'a fm \<Rightarrow> 'a fm" where
  "and \<phi>\<^sub>1 \<phi>\<^sub>2 =
 (if \<phi>\<^sub>1=TrueF then \<phi>\<^sub>2 else if \<phi>\<^sub>2=TrueF then \<phi>\<^sub>1 else
  if \<phi>\<^sub>1=FalseF \<or> \<phi>\<^sub>2=FalseF then FalseF else And \<phi>\<^sub>1 \<phi>\<^sub>2)"

definition or :: "'a fm \<Rightarrow> 'a fm \<Rightarrow> 'a fm" where
  "or \<phi>\<^sub>1 \<phi>\<^sub>2 =
 (if \<phi>\<^sub>1=FalseF then \<phi>\<^sub>2 else if \<phi>\<^sub>2=FalseF then \<phi>\<^sub>1 else
  if \<phi>\<^sub>1=TrueF \<or> \<phi>\<^sub>2=TrueF then TrueF else Or \<phi>\<^sub>1 \<phi>\<^sub>2)"

definition list_conj :: "'a fm list \<Rightarrow> 'a fm" where
  "list_conj fs = foldr and fs TrueF"

definition list_disj :: "'a fm list \<Rightarrow> 'a fm" where
  "list_disj fs = foldr or fs FalseF"

text "
The atom datatype corresponds to the defined in Tobias's LinearQuantifierElim.
"

datatype atom = Less "real mpoly" | Eq "real mpoly" | Leq "real mpoly" | Neq "real mpoly"

text
  "
For each atom, the real mpoly corresponds to a polynomial from the Polynomials library where
we allow for real valued coefficients.

The variables in the polynomials are in De Bruijn notation where variable 0 corresponds to the
variable of the innermost quantifier, then variable 1 is the next quantifier out from that, and
so on. Any variable number greater than the number of quantifiers is a free variable. This means
that we have a list of infinite free variables we can pick from and if we want to refer to the
ith free variable (indexed at 0)  within an atom that is bound in j quantifiers, then we would use
var (i+j).

The polynomials are all standardized so that they are compared to a 0 on the right. This means 
the atom Less p corresponds to $p\\leq0$ and the atom Eq p corresponds to $p=0$ and so on. This
restriction doesn't lose any generality and having all 4 of these kinds of atoms prevents loss
of efficiency as the negation of these atoms do not introduce additional logical connectives. The
following aNeg function demonstrates this.
"

fun aNeg :: "atom \<Rightarrow> atom" where
  "aNeg (Less p) = Leq (-p)" |
  "aNeg (Eq p) = Neq p" |
  "aNeg (Leq p) = Less (-p)" |
  "aNeg (Neq p) = Eq p"

subsection "Evaluation"

text "
In order to do any proofs with these atoms, we need a method of comparing two atoms to check if they
are equal. Instead of trying to manipulate the polynomials to a standard form to compare them, it
is a lot easier to plug in values for every variable and check if the results are equal. If every
single real value input for each variable matches in truth value for both atoms, then they are equal.

aEval a l corresponds to plugging in the real value list l into the variables of atom a and then
evaluating the truth value of it
"
fun aEval :: "atom \<Rightarrow> real list \<Rightarrow> bool" where
  "aEval (Eq p) L = (insertion (nth_default 0 L) p = 0)" |
  "aEval (Less p) L = (insertion (nth_default 0 L) p < 0)" |
  "aEval (Leq p) L = (insertion (nth_default 0 L) p \<le> 0)" |
  "aEval (Neq p) L = (insertion (nth_default 0 L) p \<noteq> 0)"


text "
aNeg\\_aEval shows the general format for how things are proven equal. Plugging in the values to an
original atom a will results in the opposite truth value if we transformed with the aNeg function.
"
lemma aNeg_aEval : "aEval a L \<longleftrightarrow> (\<not> aEval (aNeg a) L)"
  apply(cases a)
     apply(auto)
     apply(smt insertionNegative)
    apply(smt insertionNegative)
   apply(smt insertionNegative)
  apply(smt insertionNegative)
  done

text "
We can extend this to formulas instead of just atoms. Given a formula in prenex normal form,
we simply iterate through and apply the quantifiers
"


fun eval :: "atom fm \<Rightarrow> real list \<Rightarrow> bool" where
  "eval (Atom a) \<Gamma> = aEval a \<Gamma>" |
  "eval (TrueF) _ = True" |
  "eval (FalseF) _ = False" |
  "eval (And \<phi> \<psi>) \<Gamma> = ((eval \<phi> \<Gamma>) \<and> (eval \<psi> \<Gamma>))" |
  "eval (Or \<phi> \<psi>) \<Gamma> = ((eval \<phi> \<Gamma>) \<or> (eval \<psi> \<Gamma>))" |
  "eval (Neg \<phi>) \<Gamma> = (\<not> (eval \<phi> \<Gamma>))" |
  "eval (ExQ \<phi>) \<Gamma> = (\<exists>x. (eval \<phi> (x#\<Gamma>)))" |
  "eval (AllQ \<phi>) \<Gamma> = (\<forall>x. (eval \<phi> (x#\<Gamma>)))"|
  "eval (AllN i \<phi>) \<Gamma> = (\<forall>l. length l = i \<longrightarrow> (eval \<phi> (l @ \<Gamma>)))"|
  "eval (ExN i \<phi>) \<Gamma> = (\<exists>l. length l = i \<and> (eval \<phi> (l @ \<Gamma>)))"


lemma "eval (ExQ (Or (Atom A) (Atom B))) xs =  eval (Or (ExQ(Atom A)) (ExQ(Atom B))) xs"
  by(auto)


lemma eval_neg_neg : "eval (neg (neg f)) L \<longleftrightarrow> eval f L"
  by (simp add: neg_def)

lemma eval_neg : "(\<not> eval (neg f) L) \<longleftrightarrow> eval f L"
  by (simp add: neg_def)

lemma eval_and : "eval (and a b) L \<longleftrightarrow> (eval a L \<and> eval b L)"
  by (simp add: and_def)

lemma eval_or : "eval (or a b) L \<longleftrightarrow> (eval a L \<or> eval b L)"
  by (simp add: or_def)

lemma eval_Or : "eval (Or a b) L \<longleftrightarrow> (eval a L \<or> eval b L)"
  by (simp)

lemma eval_And : "eval (And a b) L \<longleftrightarrow> (eval a L \<and> eval b L)"
  by (simp)

lemma eval_not : "eval (neg a) L \<longleftrightarrow> \<not>(eval a L)"
  by (simp add: neg_def)

lemma eval_true : "eval TrueF L"
  by simp

lemma eval_false : "\<not>(eval FalseF L)"
  by simp

lemma eval_Neg : "eval (Neg \<phi>) L = eval (neg \<phi>) L"
  by (simp add: eval_not)

lemma eval_Neg_Neg : "eval (Neg (Neg \<phi>)) L = eval \<phi> L"
  by (simp add: eval_not)


lemma eval_Neg_And : "eval (Neg (And \<phi> \<psi>)) L = eval (Or (Neg \<phi>) (Neg \<psi>)) L"
  by simp

lemma aEval_leq : "aEval (Leq p) L = (aEval (Less p) L \<or> aEval (Eq p) L)"
  by auto

text "This function is misleading because it is true iff 
  the variable given doesn't occur as a free variable in the atom fm"
fun freeIn :: "nat \<Rightarrow> atom fm \<Rightarrow> bool" where
  "freeIn var (Atom(Eq p)) = (var \<notin> (vars p))"|
  "freeIn var (Atom(Less p)) = (var \<notin> (vars p))"|
  "freeIn var (Atom(Leq p)) = (var \<notin> (vars p))"|
  "freeIn var (Atom(Neq p)) = (var \<notin> (vars p))"|
  "freeIn var (TrueF) = True"|
  "freeIn var (FalseF) = True"|
  "freeIn var (And a b) = ((freeIn var a) \<and> (freeIn var b))"|
  "freeIn var (Or a b) = ((freeIn var a) \<and> (freeIn var b))"|
  "freeIn var (Neg a) = freeIn var a"|
  "freeIn var (ExQ a) = freeIn (var+1) a"|
  "freeIn var (AllQ a) = freeIn (var+1) a"|
  "freeIn var (AllN i a) = freeIn (var+i) a"|
  "freeIn var (ExN i a) = freeIn (var+i) a"



fun liftmap :: "(nat \<Rightarrow> atom \<Rightarrow> atom fm) \<Rightarrow> atom fm \<Rightarrow> nat \<Rightarrow> atom fm" where
  "liftmap f TrueF var = TrueF"|
  "liftmap f FalseF var = FalseF"|
  "liftmap f (Atom a) var = f var a"|
  "liftmap f (And \<phi> \<psi>) var = And (liftmap f \<phi> var) (liftmap f \<psi> var)"|
  "liftmap f (Or \<phi> \<psi>) var = Or (liftmap f \<phi> var) (liftmap f \<psi> var)"|
  "liftmap f (Neg \<phi>) var = Neg (liftmap f \<phi> var)"|
  "liftmap f (ExQ \<phi>) var = ExQ (liftmap f \<phi> (var+1))"|
  "liftmap f (AllQ \<phi>) var = AllQ (liftmap f \<phi> (var+1))"|
  "liftmap f (AllN i \<phi>) var = AllN i (liftmap f \<phi> (var+i))"|
  "liftmap f (ExN i \<phi>) var = ExN i (liftmap f \<phi> (var+i))"

(*
fun greatestFreeVariable :: "atom fm \<Rightarrow> nat option" where
"greatestFreeVariable F = None"

fun is_closed :: "atom fm \<Rightarrow> real list \<Rightarrow> bool" where
"is_closed F xs = (case greatestFreeVariable F of Some x \<Rightarrow> (x = length xs) | None \<Rightarrow> (0=length xs))"
*)

fun depth :: "'a fm \<Rightarrow> nat"where
  "depth TrueF = 1"|
  "depth FalseF = 1"|
  "depth (Atom _) = 1"|
  "depth (And \<phi> \<psi>) = max (depth \<phi>) (depth \<psi>) + 1"|
  "depth (Or \<phi> \<psi>) = max (depth \<phi>) (depth \<psi>) + 1"|
  "depth (Neg \<phi>) = depth \<phi> + 1"|
  "depth (ExQ \<phi>) = depth \<phi> + 1"|
  "depth (AllQ \<phi>) = depth \<phi> + 1"|
  "depth (AllN i \<phi>) = depth \<phi> + 1"|
  "depth (ExN i \<phi>) = depth \<phi> + 1"

value "AllQ (And 
    (ExQ (Atom (Eq (Var 1 * Var 2 - (Var 0)^2 * Var 3))))
    (Neg (AllQ (Atom (Leq (Const 5 * (Var 1)^2 - Var 0)))))
)"

fun negation_free :: "atom fm \<Rightarrow> bool" where 
  "negation_free TrueF = True" |
  "negation_free FalseF = True " |
  "negation_free (Atom a) = True" |
  "negation_free (And \<phi>\<^sub>1 \<phi>\<^sub>2) = ((negation_free \<phi>\<^sub>1) \<and> (negation_free \<phi>\<^sub>2))" |
  "negation_free (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = ((negation_free \<phi>\<^sub>1) \<and> (negation_free \<phi>\<^sub>2))" |
  "negation_free (ExQ \<phi>) = negation_free \<phi>" |
  "negation_free (AllQ \<phi>) = negation_free \<phi>" |
  "negation_free (AllN i \<phi>) = negation_free \<phi>" |
  "negation_free (ExN i \<phi>) = negation_free \<phi>" |
  "negation_free (Neg _) = False"

subsection "Useful Properties"

lemma sum_eq : "eval (Atom(Eq p)) L \<longrightarrow> eval (Atom(Eq q)) L \<longrightarrow> eval (Atom(Eq(p + q))) L"
  by (simp add: insertion_add)

lemma freeIn_list_conj : "(\<forall>f\<in>set(F). freeIn var f) \<Longrightarrow> freeIn var (list_conj F)"
proof(induct F)
  case Nil
  then show ?case by(simp add: list_conj_def)
next
  case (Cons a F)
  then show ?case by (simp add: PolyAtoms.and_def list_conj_def)
qed

lemma freeIn_list_disj : 
  assumes "\<forall>f\<in>set (L::atom fm list). freeIn var f"
  shows "freeIn var (list_disj L)"
  using assms
proof(induction L)
  case Nil
  then show ?case unfolding list_disj_def  by auto
next
  case (Cons a L)
  then show ?case unfolding list_disj_def or_def by simp
qed

lemma var_not_in_aEval : "freeIn var (Atom \<phi>) \<Longrightarrow> (\<exists>x. aEval \<phi> (list_update L var x)) = (\<forall>x. aEval \<phi> (list_update L var x))"
proof(induction \<phi>)
  case (Less p)
  then show ?case
    apply(auto)
    using not_contains_insertion 
    by metis
next
  case (Eq p)
  then show ?case
    apply(auto)
    using not_contains_insertion
    by blast 
next
  case (Leq p)
  then show ?case
    apply(auto)
    using not_contains_insertion
    by metis
next
  case (Neq p)
  then show ?case 
    apply(auto)
    using not_contains_insertion
    by metis
qed

lemma var_not_in_aEval2 : "freeIn 0 (Atom \<phi>) \<Longrightarrow> (\<exists>x. aEval \<phi> (x#L)) = (\<forall>x. aEval \<phi> (x#L))"
  by (metis list_update_code(2) var_not_in_aEval) 

lemma plugInLinear :
  assumes lLength : "length L>var"
  assumes nonzero : "B\<noteq>0"
  assumes hb : "\<forall>v. insertion (nth_default 0 (list_update L var v)) b = B"
  assumes hc : "\<forall>v. insertion (nth_default 0 (list_update L var v)) c = C"
  shows "aEval (Eq(b*Var var + c)) (list_update L var (-C/B))"
  by(simp add: lLength insertion_add insertion_mult nonzero hb hc insertion_var)


subsection "Some eval results"
lemma doubleExist : "eval (ExN 2 A) L = eval (ExQ (ExQ A)) L"
  apply(simp)
proof(safe)
  fix l
  assume h : "length l = 2" "eval A (l @ L)"
  show "\<exists>x xa. eval A (xa # x # L)"
  proof(cases l)
    case Nil
    then show ?thesis using h by auto
  next
    case (Cons a list)
    then have Cons' : "l = a # list" by auto
    then show ?thesis proof(cases list)
      case Nil
      then show ?thesis using h Cons  by auto
    next
      case (Cons b list)
      show ?thesis
        apply(rule exI[where x=b])apply(rule exI[where x=a])
        using h Cons' Cons  by auto
    qed
  qed
next
  fix x xa
  assume h : "eval A (xa # x # L)"
  show "\<exists>l. length l = 2 \<and> eval A (l @ L)"
    apply(rule exI[where x="[xa,x]"]) using h by simp
qed

lemma doubleForall : "eval (AllN 2 A) L = eval (AllQ (AllQ A)) L"
  apply(simp)using doubleExist eval_neg by fastforce

lemma unwrapExist : "eval (ExN (j + 1) A) L = eval (ExQ (ExN j A)) L"
  apply simp
  apply safe
  subgoal for l
    apply(rule exI[where x="nth l j"])
    apply(rule exI[where x="take j l"])
    apply auto
    by (metis Cons_nth_drop_Suc append.assoc append_Cons append_eq_append_conv_if append_take_drop_id lessI)
  subgoal for x l
    apply(rule exI[where x="l @ [x]"])
    by auto
  done

lemma unwrapExist' : "eval (ExN (j + 1) A) L =  eval (ExN j (ExQ A)) L"
  apply simp
  apply safe
  subgoal for l
    apply(rule exI[where x="drop 1 l"])
    apply auto
    apply(rule exI[where x="nth l 0"])
    by (metis Cons_nth_drop_Suc append_Cons drop0 zero_less_Suc)
  subgoal for l x
    apply(rule exI[where x="x#l"])
    by auto
  done

lemma unwrapExist'' : "eval (ExN (i + j) A) L = eval (ExN i(ExN j A)) L"
  apply simp
  apply safe
  subgoal for l
    apply(rule exI[where x="drop j l"])
    apply auto
    apply(rule exI[where x="take j l"])
    apply auto
    by (metis append.assoc append_take_drop_id)
  subgoal for l la
    apply(rule exI[where x="la@l"])
    by auto
  done

lemma unwrapForall : "eval (AllN (j + 1) A) L = eval (AllQ (AllN j A)) L"
  using unwrapExist[of j "neg A" L] eval_neg by fastforce

lemma unwrapForall' : "eval (AllN (j + 1) A) L =  eval (AllN j (AllQ A)) L"
  using unwrapExist'[of j "neg A" L] eval_neg by fastforce

lemma unwrapForall'' : "eval (AllN (i + j) A) L = eval (AllN i(AllN j A)) L"
  using unwrapExist''[of i j "neg A" L] eval_neg by fastforce

lemma var_not_in_eval : "\<forall>var. \<forall>L. (freeIn var \<phi> \<longrightarrow> ((\<exists>x. eval \<phi> (list_update L var x)) = (\<forall>x. eval \<phi> (list_update L var x))))"
proof(induction \<phi>)
  case TrueF
  then show ?case by(auto)
next
  case FalseF
  then show ?case by(auto)
next
  case (Atom x)
  then show ?case
    using var_not_in_aEval eval.simps(1) by blast
next
  case (And \<phi>1 \<phi>2)
  then show ?case by (meson eval.simps(4) freeIn.simps(7)) 
next
  case (Or \<phi>1 \<phi>2)
  then show ?case by fastforce 
next
  case (Neg \<phi>)
  then show ?case by (meson eval.simps(6) freeIn.simps(9))
next
  case (ExQ \<phi>)
  fix xa L var x
  have  "(xa::real) # L[var := x] = (xa#L)[var+1:=x]"
    by simp
  then show ?case using ExQ
    by (metis Suc_eq_plus1 eval.simps(7) freeIn.simps(10) list_update_code(3))
next
  case (AllQ \<phi>)
  fix xa L var x
  have  "(xa::real) # L[var := x] = (xa#L)[var+1:=x]"
    by simp
  then show ?case using AllQ
    by (metis Suc_eq_plus1 eval.simps(8) freeIn.simps(11) list_update_code(3))
next
  case (ExN i \<phi>)
  {fix xa L var x
    assume "length (xa::real list) = i"
    have  "xa @ L[var := x] = (xa@L)[var+i:=x]"
      by (simp add: \<open>length xa = i\<close> list_update_append)
  }
  then show ?case using ExN
    by (metis eval.simps(10) freeIn.simps(13))
next
  case (AllN i \<phi>)
  {fix xa L var x
    assume "length (xa::real list) = i"
    have  "xa @ L[var := x] = (xa@L)[var+i:=x]"
      by (simp add: \<open>length xa = i\<close> list_update_append)
  }
  then show ?case using AllN
    by (metis eval.simps(9) freeIn.simps(12))
qed

lemma var_not_in_eval2 : "\<forall>L. (freeIn 0 \<phi> \<longrightarrow> ((\<exists>x. eval \<phi> (x#L)) = (\<forall>x. eval \<phi> (x#L))))"
  by (metis list_update_code(2) var_not_in_eval)

lemma var_not_in_eval3 :
  assumes "freeIn var \<phi>"
  assumes "length xs' = var"
  shows "((\<exists>x. eval \<phi> (xs'@x#L)) = (\<forall>x. eval \<phi> (xs'@x#L)))"
  using assms
  by (metis list_update_length var_not_in_eval) 

lemma eval_list_conj : "eval (list_conj F) L = (\<forall>f\<in>set(F). eval f L)"
proof -
  { fix f F
    have h : "eval (foldr and F f) L = (eval f L \<and> (\<forall>f \<in> set F. eval f L))"
      apply(induct F)
       apply simp
      using eval_and by auto
  } then show ?thesis
    by(simp add:list_conj_def)
qed


lemma eval_list_disj : "eval (list_disj F) L = (\<exists>f\<in>set(F). eval f L)"
proof -
  { fix f F
    have h : "eval (foldr or F f) L = (eval f L \<or> (\<exists>f \<in> set F. eval f L))"
      apply(induct F)
       apply simp
      using eval_or by auto
  } then show ?thesis
    by(simp add:list_disj_def)
qed
end