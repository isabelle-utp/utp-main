chapter \<open>Partial recursive functions\<close>

theory Partial_Recursive
  imports Main "HOL-Library.Nat_Bijection"
begin

text \<open>This chapter lays the foundation for Chapter~\ref{c:iirf}.
Essentially it develops recursion theory up to the point of certain
fixed-point theorems. This in turn requires standard results such as the
existence of a universal function and the $s$-$m$-$n$ theorem. Besides these,
the chapter contains some results, mostly regarding decidability and the
Kleene normal form, that are not strictly needed later. They are included as
relatively low-hanging fruits to round off the chapter.

The formalization of partial recursive functions is very much inspired by the
Universal Turing Machine AFP entry by Xu
et~al.~\cite{Universal_Turing_Machine-AFP}. It models partial recursive
functions as algorithms whose semantics is given by an evaluation function.
This works well for most of this chapter. For the next chapter, however, it
is beneficial to regard partial recursive functions as ``proper'' partial
functions. To that end, Section~\ref{s:alternative} introduces more
conventional and convenient notation for the common special cases of unary
and binary partial recursive functions.

Especially for the nontrivial proofs I consulted the classical textbook by
Rogers~\cite{Rogers87}, which also partially explains my preferring the
traditional term ``recursive'' to the more modern ``computable''.\<close>


section \<open>Basic definitions\<close>


subsection \<open>Partial recursive functions\<close>

text \<open>To represent partial recursive functions we start from the same
datatype as Xu et~al.~\cite{Universal_Turing_Machine-AFP}, more specifically
from Urban's version of the formalization. In fact the datatype @{text recf}
and the function @{text arity} below have been copied verbatim from it.\<close>

datatype recf =
  Z
| S
| Id nat nat
| Cn nat recf "recf list"
| Pr nat recf recf
| Mn nat recf

fun arity :: "recf \<Rightarrow> nat" where
  "arity Z = 1"
| "arity S = 1"
| "arity (Id m n) = m"
| "arity (Cn n f gs) = n"
| "arity (Pr n f g) = Suc n"
| "arity (Mn n f) = n"

text \<open>Already we deviate from Xu et~al.\ in that we define a
well-formedness predicate for partial recursive functions. Well-formedness
essentially means arity constraints are respected when combining @{typ
recf}s.\<close>

fun wellf :: "recf \<Rightarrow> bool" where
  "wellf Z = True"
| "wellf S = True"
| "wellf (Id m n) = (n < m)"
| "wellf (Cn n f gs) =
    (n > 0 \<and> (\<forall>g \<in> set gs. arity g = n \<and> wellf g) \<and> arity f = length gs \<and> wellf f)"
| "wellf (Pr n f g) =
    (arity g = Suc (Suc n) \<and> arity f = n \<and> wellf f \<and> wellf g)"
| "wellf (Mn n f) = (n > 0 \<and> arity f = Suc n \<and> wellf f)"

lemma wellf_arity_nonzero: "wellf f \<Longrightarrow> arity f > 0"
  by (induction f rule: arity.induct) simp_all

lemma wellf_Pr_arity_greater_1: "wellf (Pr n f g) \<Longrightarrow> arity (Pr n f g) > 1"
  using wellf_arity_nonzero by auto

text \<open>For the most part of this chapter this is the meaning of ``$f$
is an $n$-ary partial recursive function'':\<close>

abbreviation recfn :: "nat \<Rightarrow> recf \<Rightarrow> bool" where
  "recfn n f \<equiv> wellf f \<and> arity f = n"

text \<open>Some abbreviations for working with @{typ "nat option"}:\<close>

abbreviation divergent :: "nat option \<Rightarrow> bool" ("_ \<up>" [50] 50) where
  "x \<up> \<equiv> x = None"

abbreviation convergent :: "nat option \<Rightarrow> bool" ("_ \<down>" [50] 50) where
  "x \<down> \<equiv> x \<noteq> None"

abbreviation convergent_eq :: "nat option \<Rightarrow> nat \<Rightarrow> bool" (infix "\<down>=" 50) where
  "x \<down>= y \<equiv> x = Some y"

abbreviation convergent_neq :: "nat option \<Rightarrow> nat \<Rightarrow> bool" (infix "\<down>\<noteq>" 50) where
  "x \<down>\<noteq> y \<equiv> x \<down> \<and> x \<noteq> Some y"

text \<open>In prose the terms ``halt'', ``terminate'', ``converge'', and
``defined'' will be used interchangeably; likewise for ``not halt'',
``diverge'', and ``undefined''. In names of lemmas, the abbreviations @{text
converg} and @{text diverg} will be used consistently.\<close>

text \<open>Our second major deviation from Xu
et~al.~\cite{Universal_Turing_Machine-AFP} is that we model the semantics of
a @{typ recf} by combining the value and the termination of a function into
one evaluation function with codomain @{typ "nat option"}, rather than
separating both aspects into an evaluation function with codomain @{typ nat}
and a termination predicate.

The value of a well-formed partial recursive function applied to a
correctly-sized list of arguments:\<close>

fun eval_wellf :: "recf \<Rightarrow> nat list \<Rightarrow> nat option" where
  "eval_wellf Z xs \<down>= 0"
| "eval_wellf S xs \<down>= Suc (xs ! 0)"
| "eval_wellf (Id m n) xs \<down>= xs ! n"
| "eval_wellf (Cn n f gs) xs =
   (if \<forall>g \<in> set gs. eval_wellf g xs \<down>
    then eval_wellf f (map (\<lambda>g. the (eval_wellf g xs)) gs)
    else None)"
| "eval_wellf (Pr n f g) [] = undefined"
| "eval_wellf (Pr n f g) (0 # xs) = eval_wellf f xs"
| "eval_wellf (Pr n f g) (Suc x # xs) =
   Option.bind (eval_wellf (Pr n f g) (x # xs)) (\<lambda>v. eval_wellf g (x # v # xs))"
| "eval_wellf (Mn n f) xs =
   (let E = \<lambda>z. eval_wellf f (z # xs)
    in if \<exists>z. E z \<down>= 0 \<and> (\<forall>y<z. E y \<down>)
       then Some (LEAST z. E z \<down>= 0 \<and> (\<forall>y<z. E y \<down>))
       else None)"

text \<open>We define a function value only if the @{typ recf} is well-formed
and its arity matches the number of arguments.\<close>

definition eval :: "recf \<Rightarrow> nat list \<Rightarrow> nat option" where
  "recfn (length xs) f \<Longrightarrow> eval f xs \<equiv> eval_wellf f xs"

lemma eval_Z [simp]: "eval Z [x] \<down>= 0"
  by (simp add: eval_def)

lemma eval_Z' [simp]: "length xs = 1 \<Longrightarrow> eval Z xs \<down>= 0"
  by (simp add: eval_def)

lemma eval_S [simp]: "eval S [x] \<down>= Suc x"
  by (simp add: eval_def)

lemma eval_S' [simp]: "length xs = 1 \<Longrightarrow> eval S xs \<down>= Suc (hd xs)"
  using eval_def hd_conv_nth[of xs] by fastforce

lemma eval_Id [simp]:
  assumes "n < m" and "m = length xs"
  shows "eval (Id m n) xs \<down>= xs ! n"
  using assms by (simp add: eval_def)

lemma eval_Cn [simp]:
  assumes "recfn (length xs) (Cn n f gs)"
  shows "eval (Cn n f gs) xs =
    (if \<forall>g\<in>set gs. eval g xs \<down>
     then eval f (map (\<lambda>g. the (eval g xs)) gs)
     else None)"
proof -
  have "eval (Cn n f gs) xs = eval_wellf (Cn n f gs) xs"
    using assms eval_def by blast
  moreover have "\<And>g. g \<in> set gs \<Longrightarrow> eval_wellf g xs = eval g xs"
    using assms eval_def by simp
  ultimately have "eval (Cn n f gs) xs =
    (if \<forall>g\<in>set gs. eval g xs \<down>
     then eval_wellf f (map (\<lambda>g. the (eval g xs)) gs)
     else None)"
    using map_eq_conv[of "\<lambda>g. the (eval_wellf g xs)" gs "\<lambda>g. the (eval g xs)"]
    by (auto, metis)
  moreover have "\<And>ys. length ys = length gs \<Longrightarrow> eval f ys = eval_wellf f ys"
    using assms eval_def by simp
  ultimately show ?thesis by auto
qed

lemma eval_Pr_0 [simp]:
  assumes "recfn (Suc n) (Pr n f g)" and "n = length xs"
  shows "eval (Pr n f g) (0 # xs) = eval f xs"
  using assms by (simp add: eval_def)

lemma eval_Pr_diverg_Suc [simp]:
  assumes "recfn (Suc n) (Pr n f g)"
    and "n = length xs"
    and "eval (Pr n f g) (x # xs) \<up>"
  shows "eval (Pr n f g) (Suc x # xs) \<up>"
  using assms by (simp add: eval_def)

lemma eval_Pr_converg_Suc [simp]:
  assumes "recfn (Suc n) (Pr n f g)"
    and "n = length xs"
    and "eval (Pr n f g) (x # xs) \<down>"
  shows "eval (Pr n f g) (Suc x # xs) = eval g (x # the (eval (Pr n f g) (x # xs)) # xs)"
  using assms eval_def by auto

lemma eval_Pr_diverg_add:
  assumes "recfn (Suc n) (Pr n f g)"
    and "n = length xs"
    and "eval (Pr n f g) (x # xs) \<up>"
  shows "eval (Pr n f g) ((x + y) # xs) \<up>"
  using assms by (induction y) auto

lemma eval_Pr_converg_le:
  assumes "recfn (Suc n) (Pr n f g)"
    and "n = length xs"
    and "eval (Pr n f g) (x # xs) \<down>"
    and "y \<le> x"
  shows "eval (Pr n f g) (y # xs) \<down>"
  using assms eval_Pr_diverg_add le_Suc_ex by metis

lemma eval_Pr_Suc_converg:
  assumes "recfn (Suc n) (Pr n f g)"
    and "n = length xs"
    and "eval (Pr n f g) (Suc x # xs) \<down>"
  shows "eval g (x # (the (eval (Pr n f g) (x # xs))) # xs) \<down>"
    and "eval (Pr n f g) (Suc x # xs) = eval g (x # the (eval (Pr n f g) (x # xs)) # xs)"
  using eval_Pr_converg_Suc[of n f g xs x, OF assms(1,2)]
    eval_Pr_converg_le[of n f g xs "Suc x" x, OF assms] assms(3)
  by simp_all

lemma eval_Mn [simp]:
  assumes "recfn (length xs) (Mn n f)"
  shows "eval (Mn n f) xs =
   (if (\<exists>z. eval f (z # xs) \<down>= 0 \<and> (\<forall>y<z. eval f (y # xs) \<down>))
    then Some (LEAST z. eval f (z # xs) \<down>= 0 \<and> (\<forall>y<z. eval f (y # xs) \<down>))
    else None)"
  using assms eval_def by auto

text \<open>For $\mu$-recursion, the condition @{term "(\<forall>y<z. eval_wellf f (y # xs) \<down>)"}
inside @{text LEAST} in the definition of @{term eval_wellf} is redundant.\<close>

lemma eval_wellf_Mn:
  "eval_wellf (Mn n f) xs =
    (if (\<exists>z. eval_wellf f (z # xs) \<down>= 0 \<and> (\<forall>y<z. eval_wellf f (y # xs) \<down>))
     then Some (LEAST z. eval_wellf f (z # xs) \<down>= 0)
     else None)"
proof -
  let ?P = "\<lambda>z. eval_wellf f (z # xs) \<down>= 0 \<and> (\<forall>y<z. eval_wellf f (y # xs) \<down>)"
  {
    assume "\<exists>z. ?P z"
    moreover define z where "z = Least ?P"
    ultimately have "?P z"
      using LeastI[of ?P] by blast
    have "(LEAST z. eval_wellf f (z # xs) \<down>= 0) = z"
    proof (rule Least_equality)
      show "eval_wellf f (z # xs) \<down>= 0"
        using \<open>?P z\<close> by simp
      show "z \<le> y" if "eval_wellf f (y # xs) \<down>= 0" for y
      proof (rule ccontr)
        assume "\<not> z \<le> y"
        then have "y < z" by simp
        moreover from this have "?P y"
          using that \<open>?P z\<close> by simp
        ultimately show False
          using that not_less_Least z_def by blast
      qed
    qed
  }
  then show ?thesis by simp
qed

lemma eval_Mn':
  assumes "recfn (length xs) (Mn n f)"
  shows "eval (Mn n f) xs =
   (if (\<exists>z. eval f (z # xs) \<down>= 0 \<and> (\<forall>y<z. eval f (y # xs) \<down>))
    then Some (LEAST z. eval f (z # xs) \<down>= 0)
    else None)"
  using assms eval_def eval_wellf_Mn by auto

text \<open>Proving that $\mu$-recursion converges is easier if one does not
have to deal with @{text LEAST} directly.\<close>

lemma eval_Mn_convergI:
  assumes "recfn (length xs) (Mn n f)"
    and "eval f (z # xs) \<down>= 0"
    and "\<And>y. y < z \<Longrightarrow> eval f (y # xs) \<down>\<noteq> 0"
  shows "eval (Mn n f) xs \<down>= z"
proof -
  let ?P = "\<lambda>z. eval f (z # xs) \<down>= 0 \<and> (\<forall>y<z. eval f (y # xs) \<down>)"
  have "z = Least ?P"
    using Least_equality[of ?P z] assms(2,3) not_le_imp_less by blast
  moreover have "?P z" using assms(2,3) by simp
  ultimately show "eval (Mn n f) xs \<down>= z"
    using eval_Mn[OF assms(1)] by meson
qed

text \<open>Similarly, reasoning from a $\mu$-recursive function is
simplified somewhat by the next lemma.\<close>

lemma eval_Mn_convergE:
  assumes "recfn (length xs) (Mn n f)" and "eval (Mn n f) xs \<down>= z"
  shows "z = (LEAST z. eval f (z # xs) \<down>= 0 \<and> (\<forall>y<z. eval f (y # xs) \<down>))"
    and "eval f (z # xs) \<down>= 0"
    and "\<And>y. y < z \<Longrightarrow> eval f (y # xs) \<down>\<noteq> 0"
proof -
  let ?P = "\<lambda>z. eval f (z # xs) \<down>= 0 \<and> (\<forall>y<z. eval f (y # xs) \<down>)"
  show "z = Least ?P"
    using assms eval_Mn[OF assms(1)]
    by (metis (no_types, lifting) option.inject option.simps(3))
  moreover have "\<exists>z. ?P z"
    using assms eval_Mn[OF assms(1)] by (metis option.distinct(1))
  ultimately have "?P z"
    using LeastI[of ?P] by blast
  then have "eval f (z # xs) \<down>= 0 \<and> (\<forall>y<z. eval f (y # xs) \<down>)"
    by simp
  then show "eval f (z # xs) \<down>= 0" by simp
  show "\<And>y. y < z \<Longrightarrow> eval f (y # xs) \<down>\<noteq> 0"
    using not_less_Least[of _ ?P] \<open>z = Least ?P\<close> \<open>?P z\<close> less_trans by blast
qed

lemma eval_Mn_diverg:
  assumes "recfn (length xs) (Mn n f)"
  shows "\<not> (\<exists>z. eval f (z # xs) \<down>= 0 \<and> (\<forall>y<z. eval f (y # xs) \<down>)) \<longleftrightarrow> eval (Mn n f) xs \<up>"
  using assms eval_Mn[OF assms(1)] by simp


subsection \<open>Extensional equality\<close>

definition exteq :: "recf \<Rightarrow> recf \<Rightarrow> bool" (infix "\<simeq>" 55) where
  "f \<simeq> g \<equiv> arity f = arity g \<and> (\<forall>xs. length xs = arity f \<longrightarrow> eval f xs = eval g xs)"

lemma exteq_refl: "f \<simeq> f"
  using exteq_def by simp

lemma exteq_sym: "f \<simeq> g \<Longrightarrow> g \<simeq> f"
  using exteq_def by simp

lemma exteq_trans: "f \<simeq> g \<Longrightarrow> g \<simeq> h \<Longrightarrow> f \<simeq> h"
  using exteq_def by simp

lemma exteqI:
  assumes "arity f = arity g" and "\<And>xs. length xs = arity f \<Longrightarrow> eval f xs = eval g xs"
  shows "f \<simeq> g"
  using assms exteq_def by simp

lemma exteqI1:
  assumes "arity f = 1" and "arity g = 1" and "\<And>x. eval f [x] = eval g [x]"
  shows "f \<simeq> g"
  using assms exteqI by (metis One_nat_def Suc_length_conv length_0_conv)

text \<open>For every partial recursive function @{term f} there are
infinitely many extensionally equal ones, for example, those that wrap @{term
f} arbitrarily often in the identity function.\<close>

fun wrap_Id :: "recf \<Rightarrow> nat \<Rightarrow> recf" where
  "wrap_Id f 0 = f"
| "wrap_Id f (Suc n) = Cn (arity f) (Id 1 0) [wrap_Id f n]"

lemma recfn_wrap_Id: "recfn a f \<Longrightarrow> recfn a (wrap_Id f n)"
  using wellf_arity_nonzero by (induction n) auto

lemma exteq_wrap_Id: "recfn a f \<Longrightarrow> f \<simeq> wrap_Id f n"
proof (induction n)
  case 0
  then show ?case by (simp add: exteq_refl)
next
  case (Suc n)
  have "wrap_Id f n \<simeq> wrap_Id f (Suc n) "
  proof (rule exteqI)
    show "arity (wrap_Id f n) = arity (wrap_Id f (Suc n))"
      using Suc by (simp add: recfn_wrap_Id)
    show "eval (wrap_Id f n) xs = eval (wrap_Id f (Suc n)) xs"
      if "length xs = arity (wrap_Id f n)" for xs
    proof -
      have "recfn (length xs) (Cn (arity f) (Id 1 0) [wrap_Id f n])"
        using that Suc recfn_wrap_Id by (metis wrap_Id.simps(2))
      then show "eval (wrap_Id f n) xs = eval (wrap_Id f (Suc n)) xs"
        by auto
    qed
  qed
  then show ?case using Suc exteq_trans by fast
qed

fun depth :: "recf \<Rightarrow> nat" where
  "depth Z = 0"
| "depth S = 0"
| "depth (Id m n) = 0"
| "depth (Cn n f gs) = Suc (max (depth f) (Max (set (map depth gs))))"
| "depth (Pr n f g) = Suc (max (depth f) (depth g))"
| "depth (Mn n f) = Suc (depth f)"

lemma depth_wrap_Id: "recfn a f \<Longrightarrow> depth (wrap_Id f n) = depth f + n"
  by (induction n) simp_all

lemma wrap_Id_injective:
  assumes "recfn a f" and "wrap_Id f n\<^sub>1 = wrap_Id f n\<^sub>2"
  shows "n\<^sub>1 = n\<^sub>2"
  using assms by (metis add_left_cancel depth_wrap_Id)

lemma exteq_infinite:
  assumes "recfn a f"
  shows "infinite {g. recfn a g \<and> g \<simeq> f}" (is "infinite ?R")
proof -
  have "inj (wrap_Id f)"
    using wrap_Id_injective \<open>recfn a f\<close> by (meson inj_onI)
  then have "infinite (range (wrap_Id f))"
    using finite_imageD by blast
  moreover have "range (wrap_Id f) \<subseteq> ?R"
    using assms exteq_sym exteq_wrap_Id recfn_wrap_Id by blast
  ultimately show ?thesis by (simp add: infinite_super)
qed


subsection \<open>Primitive recursive and total functions\<close>

fun Mn_free :: "recf \<Rightarrow> bool" where
  "Mn_free Z = True"
| "Mn_free S = True"
| "Mn_free (Id m n) = True"
| "Mn_free (Cn n f gs) = ((\<forall>g \<in> set gs. Mn_free g) \<and> Mn_free f)"
| "Mn_free (Pr n f g) = (Mn_free f \<and> Mn_free g)"
| "Mn_free (Mn n f) = False"

text \<open>This is our notion of $n$-ary primitive recursive function:\<close>

abbreviation prim_recfn :: "nat \<Rightarrow> recf \<Rightarrow> bool" where
  "prim_recfn n f \<equiv> recfn n f \<and> Mn_free f"

definition total :: "recf \<Rightarrow> bool" where
  "total f \<equiv> \<forall>xs. length xs = arity f \<longrightarrow> eval f xs \<down>"

lemma totalI [intro]:
  assumes "\<And>xs. length xs = arity f \<Longrightarrow> eval f xs \<down>"
  shows "total f"
  using assms total_def by simp

lemma totalE [simp]:
  assumes "total f" and "recfn n f" and "length xs = n"
  shows "eval f xs \<down>"
  using assms total_def by simp

lemma totalI1 :
  assumes "recfn 1 f" and "\<And>x. eval f [x] \<down>"
  shows "total f"
  using assms totalI[of f] by (metis One_nat_def length_0_conv length_Suc_conv)

lemma totalI2:
  assumes "recfn 2 f" and "\<And>x y. eval f [x, y] \<down>"
  shows "total f"
  using assms totalI[of f] by (smt length_0_conv length_Suc_conv numeral_2_eq_2)

lemma totalI3:
  assumes "recfn 3 f" and "\<And>x y z. eval f [x, y, z] \<down>"
  shows "total f"
  using assms totalI[of f] by (smt length_0_conv length_Suc_conv numeral_3_eq_3)

lemma totalI4:
  assumes "recfn 4 f" and "\<And>w x y z. eval f [w, x, y, z] \<down>"
  shows "total f"
proof (rule totalI[of f])
  fix xs :: "nat list"
  assume "length xs = arity f"
  then have "length xs = Suc (Suc (Suc (Suc 0)))"
    using assms(1) by simp
  then obtain w x y z where "xs = [w, x, y, z]"
    by (smt Suc_length_conv length_0_conv)
  then show "eval f xs \<down>" using assms(2) by simp
qed

lemma Mn_free_imp_total [intro]:
  assumes "wellf f" and "Mn_free f"
  shows "total f"
  using assms
proof (induction f rule: Mn_free.induct)
  case (5 n f g)
  have "eval (Pr n f g) (x # xs) \<down>" if "length (x # xs) = arity (Pr n f g)" for x xs
    using 5 that by (induction x) auto
  then show ?case by (metis arity.simps(5) length_Suc_conv totalI)
qed (auto simp add: total_def eval_def)

lemma prim_recfn_total: "prim_recfn n f \<Longrightarrow> total f"
  using Mn_free_imp_total by simp

lemma eval_Pr_prim_Suc:
  assumes "h = Pr n f g" and "prim_recfn (Suc n) h" and "length xs = n"
  shows "eval h (Suc x # xs) = eval g (x # the (eval h (x # xs)) # xs)"
  using assms eval_Pr_converg_Suc prim_recfn_total by simp

lemma Cn_total:
  assumes "\<forall>g\<in>set gs. total g" and "total f" and "recfn n (Cn n f gs)"
  shows "total (Cn n f gs)"
  using assms by (simp add: totalI)

lemma Pr_total:
  assumes "total f" and "total g" and "recfn (Suc n) (Pr n f g)"
  shows "total (Pr n f g)"
proof -
  have "eval (Pr n f g) (x # xs) \<down>" if "length xs = n" for x xs
    using that assms by (induction x) auto
  then show ?thesis
    using assms(3) totalI by (metis Suc_length_conv arity.simps(5))
qed

lemma eval_Mn_total:
  assumes "recfn (length xs) (Mn n f)" and "total f"
  shows "eval (Mn n f) xs =
    (if (\<exists>z. eval f (z # xs) \<down>= 0)
     then Some (LEAST z. eval f (z # xs) \<down>= 0)
     else None)"
  using assms by auto


section \<open>Simple functions\<close>

text \<open>This section, too, bears some similarity to Urban's formalization
in Xu et~al.~\cite{Universal_Turing_Machine-AFP}, but is more minimalistic in
scope.

As a general naming rule, instances of @{typ recf} and functions
returning such instances get names starting with @{text r_}. Typically, for
an @{text r_xyz} there will be a lemma @{text r_xyz_recfn} or @{text
r_xyz_prim} establishing its (primitive) recursiveness, arity, and
well-formedness. Moreover there will be a lemma @{text r_xyz} describing its
semantics, for which we will sometimes introduce an Isabelle function @{text
xyz}.\<close>


subsection \<open>Manipulating parameters\<close>

text \<open>Appending dummy parameters:\<close>

definition r_dummy :: "nat \<Rightarrow> recf \<Rightarrow> recf" where
  "r_dummy n f \<equiv> Cn (arity f + n) f (map (\<lambda>i. Id (arity f + n) i) [0..<arity f])"

lemma r_dummy_prim [simp]:
  "prim_recfn a f \<Longrightarrow> prim_recfn (a + n) (r_dummy n f)"
  using wellf_arity_nonzero by (auto simp add: r_dummy_def)

lemma r_dummy_recfn [simp]:
  "recfn a f \<Longrightarrow> recfn (a + n) (r_dummy n f)"
  using wellf_arity_nonzero by (auto simp add: r_dummy_def)

lemma r_dummy [simp]:
  "r_dummy n f = Cn (arity f + n) f (map (\<lambda>i. Id (arity f + n) i) [0..<arity f])"
  unfolding r_dummy_def by simp

lemma r_dummy_append:
  assumes "recfn (length xs) f" and "length ys = n"
  shows "eval (r_dummy n f) (xs @ ys) = eval f xs"
proof -
  let ?r = "r_dummy n f"
  let ?gs = "map (\<lambda>i. Id (arity f + n) i) [0..<arity f]"
  have "length ?gs = arity f" by simp
  moreover have "?gs ! i = (Id (arity f + n) i)" if "i < arity f" for i
    by (simp add: that)
  moreover have *: "eval_wellf (?gs ! i) (xs @ ys) \<down>= xs ! i" if "i < arity f" for i
    using that assms by (simp add: nth_append)
  ultimately have "map (\<lambda>g. the (eval_wellf g (xs @ ys))) ?gs = xs"
    by (metis (no_types, lifting) assms(1) length_map nth_equalityI nth_map option.sel)
  moreover have "\<forall>g \<in> set ?gs. eval_wellf g (xs @ ys) \<down>"
    using * by simp
  moreover have "recfn (length (xs @ ys)) ?r"
    using assms r_dummy_recfn by fastforce
  ultimately show ?thesis
    by (auto simp add: assms eval_def)
qed

text \<open>Shrinking a binary function to a unary one is useful when we want
to define a unary function via the @{term Pr} operation, which can only
construct @{typ recf}s of arity two or higher.\<close>

definition r_shrink :: "recf \<Rightarrow> recf" where
  "r_shrink f \<equiv> Cn 1 f [Id 1 0, Id 1 0]"

lemma r_shrink_prim [simp]: "prim_recfn 2 f \<Longrightarrow> prim_recfn 1 (r_shrink f)"
  by (simp add: r_shrink_def)

lemma r_shrink_recfn [simp]: "recfn 2 f \<Longrightarrow> recfn 1 (r_shrink f)"
  by (simp add: r_shrink_def)

lemma r_shrink [simp]: "recfn 2 f \<Longrightarrow> eval (r_shrink f) [x] = eval f [x, x]"
  by (simp add: r_shrink_def)

definition r_swap :: "recf \<Rightarrow> recf" where
  "r_swap f \<equiv> Cn 2 f [Id 2 1, Id 2 0]"

lemma r_swap_recfn [simp]: "recfn 2 f \<Longrightarrow> recfn 2 (r_swap f)"
  by (simp add: r_swap_def)

lemma r_swap_prim [simp]: "prim_recfn 2 f \<Longrightarrow> prim_recfn 2 (r_swap f)"
  by (simp add: r_swap_def)

lemma r_swap [simp]: "recfn 2 f \<Longrightarrow> eval (r_swap f) [x, y] = eval f [y, x]"
  by (simp add: r_swap_def)

text \<open>Prepending one dummy parameter:\<close>

definition r_shift :: "recf \<Rightarrow> recf" where
  "r_shift f \<equiv> Cn (Suc (arity f)) f (map (\<lambda>i. Id (Suc (arity f)) (Suc i)) [0..<arity f])"

lemma r_shift_prim [simp]: "prim_recfn a f \<Longrightarrow> prim_recfn (Suc a) (r_shift f)"
  by (simp add: r_shift_def)

lemma r_shift_recfn [simp]: "recfn a f \<Longrightarrow> recfn (Suc a) (r_shift f)"
  by (simp add: r_shift_def)

lemma r_shift [simp]:
  assumes "recfn (length xs) f"
  shows "eval (r_shift f) (x # xs) = eval f xs"
proof -
  let ?r = "r_shift f"
  let ?gs = "map (\<lambda>i. Id (Suc (arity f)) (Suc i)) [0..<arity f]"
  have "length ?gs = arity f" by simp
  moreover have "?gs ! i = (Id (Suc (arity f)) (Suc i))" if "i < arity f" for i
    by (simp add: that)
  moreover have *: "eval (?gs ! i) (x # xs) \<down>= xs ! i" if "i < arity f" for i
    using assms nth_append that by simp
  ultimately have "map (\<lambda>g. the (eval g (x # xs))) ?gs = xs"
    by (metis (no_types, lifting) assms length_map nth_equalityI nth_map option.sel)
  moreover have "\<forall>g \<in> set ?gs. eval g (x # xs) \<noteq> None"
    using * by simp
  ultimately show ?thesis using r_shift_def assms by simp
qed


subsection \<open>Arithmetic and logic\<close>

text \<open>The unary constants:\<close>

fun r_const :: "nat \<Rightarrow> recf" where
  "r_const 0 = Z"
| "r_const (Suc c) = Cn 1 S [r_const c]"

lemma r_const_prim [simp]: "prim_recfn 1 (r_const c)"
  by (induction c) (simp_all)

lemma r_const [simp]: "eval (r_const c) [x] \<down>= c"
  by (induction c) simp_all

text \<open>Constants of higher arities:\<close>

definition "r_constn n c \<equiv> if n = 0 then r_const c else r_dummy n (r_const c)"

lemma r_constn_prim [simp]: "prim_recfn (Suc n) (r_constn n c)"
  unfolding r_constn_def by simp

lemma r_constn [simp]: "length xs = Suc n \<Longrightarrow> eval (r_constn n c) xs \<down>= c"
  unfolding r_constn_def
  by simp (metis length_0_conv length_Suc_conv r_const)

text \<open>We introduce addition, subtraction, and multiplication, but
interestingly enough we can make do without division.\<close>

definition "r_add \<equiv> Pr 1 (Id 1 0) (Cn 3 S [Id 3 1])"

lemma r_add_prim [simp]: "prim_recfn 2 r_add"
  by (simp add: r_add_def)

lemma r_add [simp]: "eval r_add [a, b] \<down>= a + b"
  unfolding r_add_def by (induction a) simp_all

definition "r_mul \<equiv> Pr 1 Z (Cn 3 r_add [Id 3 1, Id 3 2])"

lemma r_mul_prim [simp]: "prim_recfn 2 r_mul"
  unfolding r_mul_def by simp

lemma r_mul [simp]: "eval r_mul [a, b] \<down>= a * b"
  unfolding r_mul_def by (induction a) simp_all

definition "r_dec \<equiv> Cn 1 (Pr 1 Z (Id 3 0)) [Id 1 0, Id 1 0]"

lemma r_dec_prim [simp]: "prim_recfn 1 r_dec"
  by (simp add: r_dec_def)

lemma r_dec [simp]: "eval r_dec [a] \<down>= a - 1"
proof -
  have "eval (Pr 1 Z (Id 3 0)) [x, y] \<down>= x - 1" for x y
    by (induction x) simp_all
  then show ?thesis by (simp add: r_dec_def)
qed

definition "r_sub \<equiv> r_swap (Pr 1 (Id 1 0) (Cn 3 r_dec [Id 3 1]))"

lemma r_sub_prim [simp]: "prim_recfn 2 r_sub"
  unfolding r_sub_def by simp

lemma r_sub [simp]: "eval r_sub [a, b] \<down>= a - b"
proof -
  have "eval (Pr 1 (Id 1 0) (Cn 3 r_dec [Id 3 1])) [x, y] \<down>= y - x" for x y
    by (induction x) simp_all
  then show ?thesis unfolding r_sub_def by simp
qed

definition "r_sign \<equiv> r_shrink (Pr 1 Z (r_constn 2 1))"

lemma r_sign_prim [simp]: "prim_recfn 1 r_sign"
  unfolding r_sign_def by simp

lemma r_sign [simp]: "eval r_sign [x] \<down>= (if x = 0 then 0 else 1)"
proof -
  have "eval (Pr 1 Z (r_constn 2 1)) [x, y] \<down>= (if x = 0 then 0 else 1)" for x y
    by (induction x) simp_all
  then show ?thesis unfolding r_sign_def by simp
qed

text \<open>In the logical functions, true will be represented by zero, and
false will be represented by non-zero as argument and by one as
result.\<close>

definition "r_not \<equiv> Cn 1 r_sub [r_const 1, r_sign]"

lemma r_not_prim [simp]: "prim_recfn 1 r_not"
  unfolding r_not_def by simp

lemma r_not [simp]: "eval r_not [x] \<down>= (if x = 0 then 1 else 0)"
  unfolding r_not_def by simp

definition "r_nand \<equiv> Cn 2 r_not [r_add]"

lemma r_nand_prim [simp]: "prim_recfn 2 r_nand"
  unfolding r_nand_def by simp

lemma r_nand [simp]: "eval r_nand [x, y] \<down>= (if x = 0 \<and> y = 0 then 1 else 0)"
  unfolding r_nand_def by simp

definition "r_and \<equiv> Cn 2 r_not [r_nand]"

lemma r_and_prim [simp]: "prim_recfn 2 r_and"
  unfolding r_and_def by simp

lemma r_and [simp]: "eval r_and [x, y] \<down>= (if x = 0 \<and> y = 0 then 0 else 1)"
  unfolding r_and_def by simp

definition "r_or \<equiv> Cn 2 r_sign [r_mul]"

lemma r_or_prim [simp]: "prim_recfn 2 r_or"
  unfolding r_or_def by simp

lemma r_or [simp]: "eval r_or [x, y] \<down>= (if x = 0 \<or> y = 0 then 0 else 1)"
  unfolding r_or_def by simp


subsection \<open>Comparison and conditions\<close>

definition "r_ifz \<equiv>
  let ifzero = (Cn 3 r_mul [r_dummy 2 r_not, Id 3 1]);
      ifnzero = (Cn 3 r_mul [r_dummy 2 r_sign, Id 3 2])
  in Cn 3 r_add [ifzero, ifnzero]"

lemma r_ifz_prim [simp]: "prim_recfn 3 r_ifz"
  unfolding r_ifz_def by simp

lemma r_ifz [simp]: "eval r_ifz [cond, val0, val1] \<down>= (if cond = 0 then val0 else val1)"
  unfolding r_ifz_def by (simp add: Let_def)

definition "r_eq \<equiv> Cn 2 r_sign [Cn 2 r_add [r_sub, r_swap r_sub]]"

lemma r_eq_prim [simp]: "prim_recfn 2 r_eq"
  unfolding r_eq_def by simp

lemma r_eq [simp]: "eval r_eq [x, y] \<down>= (if x = y then 0 else 1)"
  unfolding r_eq_def by simp

definition "r_ifeq \<equiv> Cn 4 r_ifz [r_dummy 2 r_eq, Id 4 2, Id 4 3]"

lemma r_ifeq_prim [simp]: "prim_recfn 4 r_ifeq"
  unfolding r_ifeq_def by simp

lemma r_ifeq [simp]: "eval r_ifeq [a, b, v\<^sub>0, v\<^sub>1] \<down>= (if a = b then v\<^sub>0 else v\<^sub>1)"
  unfolding r_ifeq_def using r_dummy_append[of r_eq "[a, b]" "[v\<^sub>0, v\<^sub>1]" 2]
  by simp

definition "r_neq \<equiv> Cn 2 r_not [r_eq]"

lemma r_neq_prim [simp]: "prim_recfn 2 r_neq"
  unfolding r_neq_def by simp

lemma r_neq [simp]: "eval r_neq [x, y] \<down>= (if x = y then 1 else 0)"
  unfolding r_neq_def by simp

definition "r_ifle \<equiv> Cn 4 r_ifz [r_dummy 2 r_sub, Id 4 2, Id 4 3]"

lemma r_ifle_prim [simp]: "prim_recfn 4 r_ifle"
  unfolding r_ifle_def by simp

lemma r_ifle [simp]: "eval r_ifle [a, b, v\<^sub>0, v\<^sub>1] \<down>= (if a \<le> b then v\<^sub>0 else v\<^sub>1)"
  unfolding r_ifle_def using r_dummy_append[of r_sub "[a, b]" "[v\<^sub>0, v\<^sub>1]" 2]
  by simp

definition "r_ifless \<equiv> Cn 4 r_ifle [Id 4 1, Id 4 0, Id 4 3, Id 4 2]"

lemma r_ifless_prim [simp]: "prim_recfn 4 r_ifless"
  unfolding r_ifless_def by simp

lemma r_ifless [simp]: "eval r_ifless [a, b, v\<^sub>0, v\<^sub>1] \<down>= (if a < b then v\<^sub>0 else v\<^sub>1)"
  unfolding r_ifless_def by simp

definition "r_less \<equiv> Cn 2 r_ifle [Id 2 1, Id 2 0, r_constn 1 1, r_constn 1 0]"

lemma r_less_prim [simp]: "prim_recfn 2 r_less"
  unfolding r_less_def by simp

lemma r_less [simp]: "eval r_less [x, y] \<down>= (if x < y then 0 else 1)"
  unfolding r_less_def by simp

definition "r_le \<equiv> Cn 2 r_ifle [Id 2 0, Id 2 1, r_constn 1 0, r_constn 1 1]"

lemma r_le_prim [simp]: "prim_recfn 2 r_le"
  unfolding r_le_def by simp

lemma r_le [simp]: "eval r_le [x, y] \<down>= (if x \<le> y then 0 else 1)"
  unfolding r_le_def by simp

text \<open>Arguments are evaluated eagerly. Therefore @{term "r_ifz"}, etc.
cannot be combined with a diverging function to implement a conditionally
diverging function in the naive way. The following function implements a
special case needed in the next section. A \hyperlink{p:r_lifz}{general lazy
version} of @{term "r_ifz"} will be introduced later with the help of a
universal function.\<close>

definition "r_ifeq_else_diverg \<equiv>
  Cn 3 r_add [Id 3 2, Mn 3 (Cn 4 r_add [Id 4 0, Cn 4 r_eq [Id 4 1, Id 4 2]])]"

lemma r_ifeq_else_diverg_recfn [simp]: "recfn 3 r_ifeq_else_diverg"
  unfolding r_ifeq_else_diverg_def by simp

lemma r_ifeq_else_diverg [simp]:
  "eval r_ifeq_else_diverg [a, b, v] = (if a = b then Some v else None)"
  unfolding r_ifeq_else_diverg_def by simp


section \<open>The halting problem\label{s:halting}\<close>

text \<open>Decidability will be treated more thoroughly in
Section~\ref{s:decidable}. But the halting problem is prominent enough to
deserve an early mention.\<close>

definition decidable :: "nat set \<Rightarrow> bool" where
  "decidable X \<equiv> \<exists>f. recfn 1 f \<and> (\<forall>x. eval f [x] \<down>= (if x \<in> X then 1 else 0))"

text \<open>No matter how partial recursive functions are encoded as natural
numbers, the set of all codes of functions halting on their own code is
undecidable.\<close>

theorem halting_problem_undecidable:
  fixes code :: "nat \<Rightarrow> recf"
  assumes "\<And>f. recfn 1 f \<Longrightarrow> \<exists>i. code i = f"
  shows "\<not> decidable {x. eval (code x) [x] \<down>}" (is "\<not> decidable ?K")
proof
  assume "decidable ?K"
  then obtain f where "recfn 1 f" and f: "\<forall>x. eval f [x] \<down>= (if x \<in> ?K then 1 else 0)"
    using decidable_def by auto
  define g where "g \<equiv> Cn 1 r_ifeq_else_diverg [f, Z, Z]"
  then have "recfn 1 g"
    using \<open>recfn 1 f\<close> r_ifeq_else_diverg_recfn by simp
  with assms obtain i where i: "code i = g" by auto
  from g_def have "eval g [x] = (if x \<notin> ?K then Some 0 else None)" for x
    using r_ifeq_else_diverg_recfn \<open>recfn 1 f\<close> f by simp
  then have "eval g [i] \<down> \<longleftrightarrow> i \<notin> ?K" by simp
  also have "... \<longleftrightarrow> eval (code i) [i] \<up>" by simp
  also have "... \<longleftrightarrow> eval g [i] \<up>"
    using i by simp
  finally have "eval g [i] \<down> \<longleftrightarrow> eval g [i] \<up>" .
  then show False by auto
qed


section \<open>Encoding tuples and lists\<close>

text \<open>This section is based on the Cantor encoding for pairs. Tuples
are encoded by repeated application of the pairing function, lists by pairing
their length with the code for a tuple. Thus tuples have a fixed length that
must be known when decoding, whereas lists are dynamically sized and know
their current length.\<close>


subsection \<open>Pairs and tuples\<close>


subsubsection \<open>The Cantor pairing function\<close>

definition "r_triangle \<equiv> r_shrink (Pr 1 Z (r_dummy 1 (Cn 2 S [r_add])))"

lemma r_triangle_prim: "prim_recfn 1 r_triangle"
  unfolding r_triangle_def by simp

lemma r_triangle: "eval r_triangle [n] \<down>= Sum {0..n}"
proof -
  let ?r = "r_dummy 1 (Cn 2 S [r_add])"
  have "eval ?r [x, y, z] \<down>= Suc (x + y)" for x y z
    using r_dummy_append[of "Cn 2 S [r_add]" "[x, y]" "[z]" 1] by simp
  then have "eval (Pr 1 Z ?r) [x, y] \<down>= Sum {0..x}" for x y
    by (induction x) simp_all
  then show ?thesis unfolding r_triangle_def by simp
qed

lemma r_triangle_eq_triangle [simp]: "eval r_triangle [n] \<down>= triangle n"
  using r_triangle gauss_sum_nat triangle_def by simp

definition "r_prod_encode \<equiv> Cn 2 r_add [Cn 2 r_triangle [r_add], Id 2 0]"

lemma r_prod_encode_prim [simp]: "prim_recfn 2 r_prod_encode"
  unfolding r_prod_encode_def using r_triangle_prim by simp

lemma r_prod_encode [simp]: "eval r_prod_encode [m, n] \<down>= prod_encode (m, n)"
  unfolding r_prod_encode_def prod_encode_def using r_triangle_prim by simp

text \<open>These abbreviations are just two more things borrowed from
Xu~et~al.~\cite{Universal_Turing_Machine-AFP}.\<close>

abbreviation "pdec1 z \<equiv> fst (prod_decode z)"

abbreviation "pdec2 z \<equiv> snd (prod_decode z)"

lemma pdec1_le: "pdec1 i \<le> i"
  by (metis le_prod_encode_1 prod.collapse prod_decode_inverse)

lemma pdec2_le: "pdec2 i \<le> i"
  by (metis le_prod_encode_2 prod.collapse prod_decode_inverse)

lemma pdec_less: "pdec2 i < Suc i"
  using pdec2_le by (simp add: le_imp_less_Suc)

lemma pdec1_zero: "pdec1 0 = 0"
  using pdec1_le by auto

definition "r_maxletr \<equiv>
  Pr 1 Z (Cn 3 r_ifle [r_dummy 2 (Cn 1 r_triangle [S]), Id 3 2, Cn 3 S [Id 3 0], Id 3 1])"

lemma r_maxletr_prim: "prim_recfn 2 r_maxletr"
  unfolding r_maxletr_def using r_triangle_prim by simp

lemma not_Suc_Greatest_not_Suc:
  assumes "\<not> P (Suc x)" and "\<exists>x. P x"
  shows "(GREATEST y. y \<le> x \<and> P y) = (GREATEST y. y \<le> Suc x \<and> P y)"
  using assms by (metis le_SucI le_Suc_eq)

lemma r_maxletr: "eval r_maxletr [x\<^sub>0, x\<^sub>1] \<down>= (GREATEST y. y \<le> x\<^sub>0 \<and> triangle y \<le> x\<^sub>1)"
proof -
  let ?g = "Cn 3 r_ifle [r_dummy 2 (Cn 1 r_triangle [S]), Id 3 2, Cn 3 S [Id 3 0], Id 3 1]"
  have greatest:
    "(if triangle (Suc x\<^sub>0) \<le> x\<^sub>1 then Suc x\<^sub>0 else (GREATEST y. y \<le> x\<^sub>0 \<and> triangle y \<le> x\<^sub>1)) =
     (GREATEST y. y \<le> Suc x\<^sub>0 \<and> triangle y \<le> x\<^sub>1)"
    for x\<^sub>0 x\<^sub>1
  proof (cases "triangle (Suc x\<^sub>0) \<le> x\<^sub>1")
    case True
    then show ?thesis
      using Greatest_equality[of "\<lambda>y. y \<le> Suc x\<^sub>0 \<and> triangle y \<le> x\<^sub>1"] by fastforce
  next
    case False
    then show ?thesis
      using not_Suc_Greatest_not_Suc[of "\<lambda>y. triangle y \<le> x\<^sub>1" x\<^sub>0] by fastforce
  qed
  show ?thesis
    unfolding r_maxletr_def using r_triangle_prim 
  proof (induction x\<^sub>0)
    case 0
    then show ?case
      using Greatest_equality[of "\<lambda>y. y \<le> 0 \<and> triangle y \<le> x\<^sub>1" 0] by simp
  next
    case (Suc x\<^sub>0)
    then show ?case using greatest by simp
  qed
qed

definition "r_maxlt \<equiv> r_shrink r_maxletr"

lemma r_maxlt_prim: "prim_recfn 1 r_maxlt"
  unfolding r_maxlt_def using r_maxletr_prim by simp

lemma r_maxlt: "eval r_maxlt [e] \<down>= (GREATEST y. triangle y \<le> e)"
proof -
  have "y \<le> triangle y" for y
    by (induction y) auto
  then have "triangle y \<le> e \<Longrightarrow> y \<le> e" for y e
    using order_trans by blast
  then have "(GREATEST y. y \<le> e \<and> triangle y \<le> e) = (GREATEST y. triangle y \<le> e)"
    by metis
  moreover have "eval r_maxlt [e] \<down>= (GREATEST y. y \<le> e \<and> triangle y \<le> e)"
    using r_maxletr r_shrink r_maxlt_def r_maxletr_prim by fastforce
  ultimately show ?thesis by simp
qed

definition "pdec1' e \<equiv> e - triangle (GREATEST y. triangle y \<le> e)"

definition "pdec2' e \<equiv> (GREATEST y. triangle y \<le> e) - pdec1' e"

lemma max_triangle_bound: "triangle z \<le> e \<Longrightarrow> z \<le> e"
  by (metis Suc_pred add_leD2 less_Suc_eq triangle_Suc zero_le zero_less_Suc)

lemma triangle_greatest_le: "triangle (GREATEST y. triangle y \<le> e) \<le> e"
  using max_triangle_bound GreatestI_nat[of "\<lambda>y. triangle y \<le> e" 0 e] by simp

lemma prod_encode_pdec': "prod_encode (pdec1' e, pdec2' e) = e"
proof -
  let ?P = "\<lambda>y. triangle y \<le> e"
  let ?y = "GREATEST y. ?P y"
  have "pdec1' e \<le> ?y"
  proof (rule ccontr)
    assume "\<not> pdec1' e \<le> ?y"
    then have "e - triangle ?y > ?y"
      using pdec1'_def by simp
    then have "?P (Suc ?y)" by simp
    moreover have "\<forall>z. ?P z \<longrightarrow> z \<le> e"
      using max_triangle_bound by simp
    ultimately have "Suc ?y \<le> ?y"
      using Greatest_le_nat[of ?P "Suc ?y" e] by blast
    then show False by simp
  qed
  then have "pdec1' e + pdec2' e = ?y"
    using pdec1'_def pdec2'_def by simp
  then have "prod_encode (pdec1' e, pdec2' e) = triangle ?y + pdec1' e"
    by (simp add: prod_encode_def)
  then show ?thesis using pdec1'_def triangle_greatest_le by simp
qed

lemma pdec':
  "pdec1' e = pdec1 e"
  "pdec2' e = pdec2 e"
  using prod_encode_pdec' prod_encode_inverse by (metis fst_conv, metis snd_conv)

definition "r_pdec1 \<equiv> Cn 1 r_sub [Id 1 0, Cn 1 r_triangle [r_maxlt]]"

lemma r_pdec1_prim [simp]: "prim_recfn 1 r_pdec1"
  unfolding r_pdec1_def using r_triangle_prim r_maxlt_prim by simp

lemma r_pdec1 [simp]: "eval r_pdec1 [e] \<down>= pdec1 e"
  unfolding r_pdec1_def using r_triangle_prim r_maxlt_prim pdec' pdec1'_def
  by (simp add: r_maxlt)

definition "r_pdec2 \<equiv> Cn 1 r_sub [r_maxlt, r_pdec1]"

lemma r_pdec2_prim [simp]: "prim_recfn 1 r_pdec2"
  unfolding r_pdec2_def using r_maxlt_prim by simp

lemma r_pdec2 [simp]: "eval r_pdec2 [e] \<down>= pdec2 e"
  unfolding r_pdec2_def using r_maxlt_prim r_maxlt pdec' pdec2'_def by simp

abbreviation "pdec12 i \<equiv> pdec1 (pdec2 i)"
abbreviation "pdec22 i \<equiv> pdec2 (pdec2 i)"
abbreviation "pdec122 i \<equiv> pdec1 (pdec22 i)"
abbreviation "pdec222 i \<equiv> pdec2 (pdec22 i)"

definition "r_pdec12 \<equiv> Cn 1 r_pdec1 [r_pdec2]"

lemma r_pdec12_prim [simp]: "prim_recfn 1 r_pdec12"
  unfolding r_pdec12_def by simp

lemma r_pdec12 [simp]: "eval r_pdec12 [e] \<down>= pdec12 e"
  unfolding r_pdec12_def by simp

definition "r_pdec22 \<equiv> Cn 1 r_pdec2 [r_pdec2]"

lemma r_pdec22_prim [simp]: "prim_recfn 1 r_pdec22"
  unfolding r_pdec22_def by simp

lemma r_pdec22 [simp]: "eval r_pdec22 [e] \<down>= pdec22 e"
  unfolding r_pdec22_def by simp

definition "r_pdec122 \<equiv> Cn 1 r_pdec1 [r_pdec22]"

lemma r_pdec122_prim [simp]: "prim_recfn 1 r_pdec122"
  unfolding r_pdec122_def by simp

lemma r_pdec122 [simp]: "eval r_pdec122 [e] \<down>= pdec122 e"
  unfolding r_pdec122_def by simp

definition "r_pdec222 \<equiv> Cn 1 r_pdec2 [r_pdec22]"

lemma r_pdec222_prim [simp]: "prim_recfn 1 r_pdec222"
  unfolding r_pdec222_def by simp

lemma r_pdec222 [simp]: "eval r_pdec222 [e] \<down>= pdec222 e"
  unfolding r_pdec222_def by simp


subsubsection \<open>The Cantor tuple function\<close>

text \<open>The empty tuple gets no code, whereas singletons are encoded by their
only element and other tuples by recursively applying the pairing function.
This yields, for every $n$, the function @{term "tuple_encode n"}, which is a
bijection between the natural numbers and the lists of length $(n + 1)$.\<close>

fun tuple_encode :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "tuple_encode n [] = undefined"
| "tuple_encode 0 (x # xs) = x"
| "tuple_encode (Suc n) (x # xs) = prod_encode (x, tuple_encode n xs)"

lemma tuple_encode_prod_encode: "tuple_encode 1 [x, y] = prod_encode (x, y)"
  by simp

fun tuple_decode where
  "tuple_decode 0 i = [i]"
| "tuple_decode (Suc n) i = pdec1 i # tuple_decode n (pdec2 i)"

lemma tuple_encode_decode [simp]:
  "tuple_encode (length xs - 1) (tuple_decode (length xs - 1) i) = i"
proof (induction "length xs - 1" arbitrary: xs i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "length xs - 1 > 0" by simp
  with Suc have *: "tuple_encode n (tuple_decode n j) = j" for j
    by (metis diff_Suc_1 length_tl)
  from Suc have "tuple_decode (Suc n) i = pdec1 i # tuple_decode n (pdec2 i)"
    using tuple_decode.simps(2) by blast
  then have "tuple_encode (Suc n) (tuple_decode (Suc n) i) =
      tuple_encode (Suc n) (pdec1 i # tuple_decode n (pdec2 i))"
    using Suc by simp
  also have "... = prod_encode (pdec1 i, tuple_encode n (tuple_decode n (pdec2 i)))"
    by simp
  also have "... = prod_encode (pdec1 i, pdec2 i)"
    using Suc * by simp
  also have "... = i" by simp
  finally have "tuple_encode (Suc n) (tuple_decode (Suc n) i) = i" .
  then show ?case by (simp add: Suc.hyps(2))
qed

lemma tuple_encode_decode' [simp]: "tuple_encode n (tuple_decode n i) = i"
  using tuple_encode_decode by (metis Ex_list_of_length diff_Suc_1 length_Cons)

lemma tuple_decode_encode:
  assumes "length xs > 0"
  shows "tuple_decode (length xs - 1) (tuple_encode (length xs - 1) xs) = xs"
  using assms
proof (induction "length xs - 1" arbitrary: xs)
  case 0
  moreover from this have "length xs = 1" by linarith
  ultimately show ?case
    by (metis One_nat_def length_0_conv length_Suc_conv tuple_decode.simps(1)
      tuple_encode.simps(2))
next
  case (Suc n)
  let ?t = "tl xs"
  let ?i = "tuple_encode (Suc n) xs"
  have "length ?t > 0" and "length ?t - 1 = n"
    using Suc by simp_all
  then have "tuple_decode n (tuple_encode n ?t) = ?t"
    using Suc by blast
  moreover have "?i = prod_encode (hd xs, tuple_encode n ?t)"
    using Suc by (metis hd_Cons_tl length_greater_0_conv tuple_encode.simps(3))
  moreover have "tuple_decode (Suc n) ?i = pdec1 ?i # tuple_decode n (pdec2 ?i)"
    using tuple_decode.simps(2) by blast
  ultimately have "tuple_decode (Suc n) ?i = xs"
    using Suc.prems by simp
  then show ?case by (simp add: Suc.hyps(2))
qed

lemma tuple_decode_encode' [simp]:
  assumes "length xs = Suc n"
  shows "tuple_decode n (tuple_encode n xs) = xs"
  using assms tuple_decode_encode by (metis diff_Suc_1 zero_less_Suc)

lemma tuple_decode_length [simp]: "length (tuple_decode n i) = Suc n"
  by (induction n arbitrary: i) simp_all

lemma tuple_decode_nonzero:
  assumes "n > 0"
  shows "tuple_decode n i = pdec1 i # tuple_decode (n - 1) (pdec2 i)"
  using assms by (metis One_nat_def Suc_pred tuple_decode.simps(2))

text \<open>The tuple encoding functions are primitive recursive.\<close>

fun r_tuple_encode :: "nat \<Rightarrow> recf" where
  "r_tuple_encode 0 = Id 1 0"
| "r_tuple_encode (Suc n) =
     Cn (Suc (Suc n)) r_prod_encode [Id (Suc (Suc n)) 0, r_shift (r_tuple_encode n)]"

lemma r_tuple_encode_prim [simp]: "prim_recfn (Suc n) (r_tuple_encode n)"
  by (induction n) simp_all

lemma r_tuple_encode:
  assumes "length xs = Suc n"
  shows "eval (r_tuple_encode n) xs \<down>= tuple_encode n xs"
  using assms
proof (induction n arbitrary: xs)
  case 0
  then show ?case
    by (metis One_nat_def eval_Id length_Suc_conv nth_Cons_0
      r_tuple_encode.simps(1) tuple_encode.simps(2) zero_less_one)
next
  case (Suc n)
  then obtain y ys where y_ys: "y # ys = xs"
    by (metis length_Suc_conv)
  with Suc have "eval (r_tuple_encode n) ys \<down>= tuple_encode n ys"
    by auto
  with y_ys have "eval (r_shift (r_tuple_encode n)) xs \<down>= tuple_encode n ys"
    using Suc.prems r_shift_prim r_tuple_encode_prim by auto
  moreover have "eval (Id (Suc (Suc n)) 0) xs \<down>= y"
    using y_ys Suc.prems by auto
  ultimately have "eval (r_tuple_encode (Suc n)) xs \<down>= prod_encode (y, tuple_encode n ys)"
    using Suc.prems by simp
  then show ?case using y_ys by auto
qed


subsubsection \<open>Functions on encoded tuples\<close>

text \<open>The function for accessing the $n$-th element of a tuple returns
$0$ for out-of-bounds access.\<close>

definition e_tuple_nth :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "e_tuple_nth a i n \<equiv> if n \<le> a then (tuple_decode a i) ! n else 0"

lemma e_tuple_nth_le [simp]: "n \<le> a \<Longrightarrow> e_tuple_nth a i n = (tuple_decode a i) ! n"
  using e_tuple_nth_def by simp

lemma e_tuple_nth_gr [simp]: "n > a \<Longrightarrow> e_tuple_nth a i n = 0"
  using e_tuple_nth_def by simp

lemma tuple_decode_pdec2: "tuple_decode a (pdec2 es) = tl (tuple_decode (Suc a) es)"
  by simp

fun iterate :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "iterate 0 f = id"
| "iterate (Suc n) f = f \<circ> (iterate n f)"

lemma iterate_additive:
  assumes "iterate t\<^sub>1 f x = y" and "iterate t\<^sub>2 f y = z"
  shows "iterate (t\<^sub>1 + t\<^sub>2) f x = z"
  using assms by (induction t\<^sub>2 arbitrary: z) auto

lemma iterate_additive': "iterate (t\<^sub>1 + t\<^sub>2) f x = iterate t\<^sub>2 f (iterate t\<^sub>1 f x)"
  using iterate_additive by metis

lemma e_tuple_nth_elementary:
  assumes "k \<le> a"
  shows "e_tuple_nth a i k = (if a = k then (iterate k pdec2 i) else (pdec1 (iterate k pdec2 i)))"
proof -
  have *: "tuple_decode (a - k) (iterate k pdec2 i) = drop k (tuple_decode a i)"
    using assms
    by (induction k) (simp, simp add: Suc_diff_Suc tuple_decode_pdec2 drop_Suc tl_drop)
  show ?thesis
  proof (cases "a = k")
    case True
    then have "tuple_decode 0 (iterate k pdec2 i) = drop k (tuple_decode a i)"
      using assms * by simp
    moreover from this have "drop k (tuple_decode a i) = [tuple_decode a i ! k]"
      using assms True by (metis nth_via_drop tuple_decode.simps(1))
    ultimately show ?thesis using True by simp
  next
    case False
    with assms have "a - k > 0" by simp
    with * have "tuple_decode (a - k) (iterate k pdec2 i) = drop k (tuple_decode a i)"
      by simp
    then have "pdec1 (iterate k pdec2 i) = hd (drop k (tuple_decode a i))"
      using tuple_decode_nonzero \<open>a - k > 0\<close> by (metis list.sel(1))
    with \<open>a - k > 0\<close> have "pdec1 (iterate k pdec2 i) = (tuple_decode a i) ! k"
      by (simp add: hd_drop_conv_nth)
    with False assms show ?thesis by simp
  qed
qed

definition "r_nth_inbounds \<equiv>
  let r = Pr 1 (Id 1 0) (Cn 3 r_pdec2 [Id 3 1])
  in Cn 3 r_ifeq
       [Id 3 0,
        Id 3 2,
        Cn 3 r [Id 3 2, Id 3 1],
        Cn 3 r_pdec1 [Cn 3 r [Id 3 2, Id 3 1]]]"

lemma r_nth_inbounds_prim: "prim_recfn 3 r_nth_inbounds"
  unfolding r_nth_inbounds_def by (simp add: Let_def)

lemma r_nth_inbounds:
  "k \<le> a \<Longrightarrow> eval r_nth_inbounds [a, i, k] \<down>= e_tuple_nth a i k"
  "eval r_nth_inbounds [a, i, k] \<down>"
proof -
  let ?r = "Pr 1 (Id 1 0) (Cn 3 r_pdec2 [Id 3 1])"
  let ?h = "Cn 3 ?r [Id 3 2, Id 3 1]"
  have "eval ?r [k, i] \<down>= iterate k pdec2 i" for k i
    using r_pdec2_prim by (induction k) (simp_all)
  then have "eval ?h [a, i, k] \<down>= iterate k pdec2 i"
    using r_pdec2_prim by simp
  then have "eval r_nth_inbounds [a, i, k] \<down>=
      (if a = k then iterate k pdec2 i else pdec1 (iterate k pdec2 i))"
    unfolding r_nth_inbounds_def by (simp add: Let_def)
  then show "k \<le> a \<Longrightarrow> eval r_nth_inbounds [a, i, k] \<down>= e_tuple_nth a i k"
    and "eval r_nth_inbounds [a, i, k] \<down>"
    using e_tuple_nth_elementary by simp_all
qed

definition "r_tuple_nth \<equiv>
  Cn 3 r_ifle [Id 3 2, Id 3 0, r_nth_inbounds, r_constn 2 0]"

lemma r_tuple_nth_prim: "prim_recfn 3 r_tuple_nth"
  unfolding r_tuple_nth_def using r_nth_inbounds_prim by simp

lemma r_tuple_nth [simp]: "eval r_tuple_nth [a, i, k] \<down>= e_tuple_nth a i k"
  unfolding r_tuple_nth_def using r_nth_inbounds_prim r_nth_inbounds by simp


subsection \<open>Lists\<close>


subsubsection \<open>Encoding and decoding\<close>

text \<open>Lists are encoded by pairing the length of the list with the code
for the tuple made up of the list's elements. Then all these codes are
incremented in order to make room for the empty list
(cf.~Rogers~\cite[p.~71]{Rogers87}).\<close>

fun list_encode :: "nat list \<Rightarrow> nat" where
  "list_encode [] = 0"
| "list_encode (x # xs) = Suc (prod_encode (length xs, tuple_encode (length xs) (x # xs)))"

lemma list_encode_0 [simp]: "list_encode xs = 0 \<Longrightarrow> xs = []"
  using list_encode.elims by blast

lemma list_encode_1: "list_encode [0] = 1"
  by (simp add: prod_encode_def)

fun list_decode :: "nat \<Rightarrow> nat list" where
  "list_decode 0 = []"
| "list_decode (Suc n) = tuple_decode (pdec1 n) (pdec2 n)"

lemma list_encode_decode [simp]: "list_encode (list_decode n) = n"
proof (cases n)
  case 0
  then show ?thesis by simp
next
  case (Suc k)
  then have *: "list_decode n = tuple_decode (pdec1 k) (pdec2 k)" (is "_ = ?t")
    by simp
  then obtain x xs where xxs: "x # xs = ?t"
    by (metis tuple_decode.elims)
  then have "list_encode ?t = list_encode (x # xs)" by simp
  then have 1: "list_encode ?t = Suc (prod_encode (length xs, tuple_encode (length xs) (x # xs)))"
    by simp
  have 2: "length xs = length ?t - 1"
    using xxs by (metis length_tl list.sel(3))
  then have 3: "length xs = pdec1 k"
    using * by simp
  then have "tuple_encode (length ?t - 1) ?t = pdec2 k"
    using 2 tuple_encode_decode by metis
  then have "list_encode ?t = Suc (prod_encode (pdec1 k, pdec2 k))"
    using 1 2 3 xxs by simp
  with * Suc show ?thesis by simp
qed

lemma list_decode_encode [simp]: "list_decode (list_encode xs) = xs"
proof (cases xs)
  case Nil
  then show ?thesis by simp
next
  case (Cons y ys)
  then have "list_encode xs =
      Suc (prod_encode (length ys, tuple_encode (length ys) xs))"
      (is "_ = Suc ?i")
    by simp
  then have "list_decode (Suc ?i) = tuple_decode (pdec1 ?i) (pdec2 ?i)" by simp
  moreover have "pdec1 ?i = length ys" by simp
  moreover have "pdec2 ?i = tuple_encode (length ys) xs" by simp
  ultimately have "list_decode (Suc ?i) =
      tuple_decode (length ys) (tuple_encode (length ys) xs)"
    by simp
  moreover have "length ys = length xs - 1"
    using Cons by simp
  ultimately have "list_decode (Suc ?i) =
      tuple_decode (length xs - 1) (tuple_encode (length xs - 1) xs)"
    by simp
  then show ?thesis using Cons by simp
qed

abbreviation singleton_encode :: "nat \<Rightarrow> nat" where
  "singleton_encode x \<equiv> list_encode [x]"

lemma list_decode_singleton: "list_decode (singleton_encode x) = [x]"
  by simp

definition "r_singleton_encode \<equiv> Cn 1 S [Cn 1 r_prod_encode [Z, Id 1 0]]"

lemma r_singleton_encode_prim [simp]: "prim_recfn 1 r_singleton_encode"
  unfolding r_singleton_encode_def by simp

lemma r_singleton_encode [simp]: "eval r_singleton_encode [x] \<down>= singleton_encode x"
  unfolding r_singleton_encode_def by simp

definition r_list_encode :: "nat \<Rightarrow> recf" where
  "r_list_encode n \<equiv> Cn (Suc n) S [Cn (Suc n) r_prod_encode [r_constn n n, r_tuple_encode n]]"

lemma r_list_encode_prim [simp]: "prim_recfn (Suc n) (r_list_encode n)"
  unfolding r_list_encode_def by simp

lemma r_list_encode:
  assumes "length xs = Suc n"
  shows "eval (r_list_encode n) xs \<down>= list_encode xs"
proof -
  have "eval (r_tuple_encode n) xs \<down>"
    by (simp add: assms r_tuple_encode)
  then have "eval (Cn (Suc n) r_prod_encode [r_constn n n, r_tuple_encode n]) xs \<down>"
    using assms by simp
  then have "eval (r_list_encode n) xs =
      eval S [the (eval (Cn (Suc n) r_prod_encode [r_constn n n, r_tuple_encode n]) xs)]"
    unfolding r_list_encode_def using assms r_tuple_encode by simp
  moreover from assms obtain y ys where "xs = y # ys"
    by (meson length_Suc_conv)
  ultimately show ?thesis
    unfolding r_list_encode_def using assms r_tuple_encode by simp
qed


subsubsection \<open>Functions on encoded lists\<close>

text \<open>The functions in this section mimic those on type @{typ "nat
list"}. Their names are prefixed by @{text e_} and the names of the
corresponding @{typ recf}s by @{text r_}.\<close>

abbreviation e_tl :: "nat \<Rightarrow> nat" where
  "e_tl e \<equiv> list_encode (tl (list_decode e))"

text \<open>In order to turn @{term e_tl} into a partial recursive function
we first represent it in a more elementary way.\<close>

lemma e_tl_elementary:
  "e_tl e =
    (if e = 0 then 0
     else if pdec1 (e - 1) = 0 then 0
     else Suc (prod_encode (pdec1 (e - 1) - 1, pdec22 (e - 1))))"
proof (cases e)
  case 0
  then show ?thesis by simp
next
  case Suc_d: (Suc d)
  then show ?thesis
  proof (cases "pdec1 d")
    case 0
    then show ?thesis using Suc_d by simp
  next
    case (Suc a)
    have *: "list_decode e = tuple_decode (pdec1 d) (pdec2 d)"
      using Suc_d by simp
    with Suc obtain x xs where xxs: "list_decode e = x # xs" by simp
    then have **: "e_tl e = list_encode xs" by simp
    have "list_decode (Suc (prod_encode (pdec1 (e - 1) - 1, pdec22 (e - 1)))) =
        tuple_decode (pdec1 (e - 1) - 1) (pdec22 (e - 1))"
        (is "?lhs = _")
      by simp
    also have "... = tuple_decode a (pdec22 (e - 1))"
      using Suc Suc_d by simp
    also have "... = tl (tuple_decode (Suc a) (pdec2 (e - 1)))"
      using tuple_decode_pdec2 Suc by presburger
    also have "... = tl (tuple_decode (pdec1 (e - 1)) (pdec2 (e - 1)))"
      using Suc Suc_d by auto
    also have "... = tl (list_decode e)"
      using * Suc_d by simp
    also have "... = xs"
      using xxs by simp
    finally have "?lhs = xs" .
    then have "list_encode ?lhs = list_encode xs" by simp
    then have "Suc (prod_encode (pdec1 (e - 1) - 1, pdec22 (e - 1))) = list_encode xs"
      using list_encode_decode by metis
    then show ?thesis using ** Suc_d Suc by simp
  qed
qed

definition "r_tl \<equiv>
 let r = Cn 1 r_pdec1 [r_dec]
 in Cn 1 r_ifz
     [Id 1 0,
      Z,
      Cn 1 r_ifz
       [r, Z, Cn 1 S [Cn 1 r_prod_encode [Cn 1 r_dec [r], Cn 1 r_pdec22 [r_dec]]]]]"

lemma r_tl_prim [simp]: "prim_recfn 1 r_tl"
  unfolding r_tl_def by (simp add: Let_def)

lemma r_tl [simp]: "eval r_tl [e] \<down>= e_tl e"
  unfolding r_tl_def using e_tl_elementary by (simp add: Let_def)

text \<open>We define the head of the empty encoded list to be zero.\<close>

definition e_hd :: "nat \<Rightarrow> nat" where
  "e_hd e \<equiv> if e = 0 then 0 else hd (list_decode e)"

lemma e_hd [simp]:
  assumes "list_decode e = x # xs"
  shows "e_hd e = x"
  using e_hd_def assms by auto

lemma e_hd_0 [simp]: "e_hd 0 = 0"
  using e_hd_def by simp

lemma e_hd_neq_0 [simp]:
  assumes "e \<noteq> 0"
  shows "e_hd e = hd (list_decode e)"
  using e_hd_def assms by simp

definition "r_hd \<equiv>
  Cn 1 r_ifz [Cn 1 r_pdec1 [r_dec], Cn 1 r_pdec2 [r_dec], Cn 1 r_pdec12 [r_dec]]"

lemma r_hd_prim [simp]: "prim_recfn 1 r_hd"
  unfolding r_hd_def by simp

lemma r_hd [simp]: "eval r_hd [e] \<down>= e_hd e"
proof -
  have "e_hd e = (if pdec1 (e - 1) = 0 then pdec2 (e - 1) else pdec12 (e - 1))"
  proof (cases e)
    case 0
    then show ?thesis using pdec1_zero pdec2_le by auto
  next
    case (Suc d)
    then show ?thesis by (cases "pdec1 d") (simp_all add: pdec1_zero)
  qed
  then show ?thesis unfolding r_hd_def by simp
qed

abbreviation e_length :: "nat \<Rightarrow> nat" where
  "e_length e \<equiv> length (list_decode e)"

lemma e_length_0: "e_length e = 0 \<Longrightarrow> e = 0"
  by (metis list_encode.simps(1) length_0_conv list_encode_decode)

definition "r_length \<equiv> Cn 1 r_ifz [Id 1 0, Z, Cn 1 S [Cn 1 r_pdec1 [r_dec]]]"

lemma r_length_prim [simp]: "prim_recfn 1 r_length"
  unfolding r_length_def by simp

lemma r_length [simp]: "eval r_length [e] \<down>= e_length e"
  unfolding r_length_def by (cases e) simp_all

text \<open>Accessing an encoded list out of bounds yields zero.\<close>

definition e_nth :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "e_nth e n \<equiv> if e = 0 then 0 else e_tuple_nth (pdec1 (e - 1)) (pdec2 (e - 1)) n"

lemma e_nth [simp]:
  "e_nth e n = (if n < e_length e then (list_decode e) ! n else 0)"
  by (cases e) (simp_all add: e_nth_def e_tuple_nth_def)

lemma e_hd_nth0: "e_hd e = e_nth e 0"
  by (simp add: e_hd_def e_length_0 hd_conv_nth)

definition "r_nth \<equiv>
  Cn 2 r_ifz
   [Id 2 0,
    r_constn 1 0,
    Cn 2 r_tuple_nth
     [Cn 2 r_pdec1 [r_dummy 1 r_dec], Cn 2 r_pdec2 [r_dummy 1 r_dec], Id 2 1]]"

lemma r_nth_prim [simp]: "prim_recfn 2 r_nth"
  unfolding r_nth_def using r_tuple_nth_prim by simp

lemma r_nth [simp]: "eval r_nth [e, n] \<down>= e_nth e n"
  unfolding r_nth_def e_nth_def using r_tuple_nth_prim by simp

definition "r_rev_aux \<equiv>
  Pr 1 r_hd (Cn 3 r_prod_encode [Cn 3 r_nth [Id 3 2, Cn 3 S [Id 3 0]], Id 3 1])"

lemma r_rev_aux_prim: "prim_recfn 2 r_rev_aux"
  unfolding r_rev_aux_def by simp

lemma r_rev_aux:
  assumes "list_decode e = xs" and "length xs > 0" and "i < length xs"
  shows "eval r_rev_aux [i, e] \<down>= tuple_encode i (rev (take (Suc i) xs))"
  using assms(3)
proof (induction i)
  case 0
  then show ?case
    unfolding r_rev_aux_def using assms e_hd_def r_hd by (auto simp add: take_Suc)
next
  case (Suc i)
  let ?g = "Cn 3 r_prod_encode [Cn 3 r_nth [Id 3 2, Cn 3 S [Id 3 0]], Id 3 1]"
  from Suc have "eval r_rev_aux [Suc i, e] = eval ?g [i, the (eval r_rev_aux [i, e]), e]"
    unfolding r_rev_aux_def by simp
  also have "... \<down>= prod_encode (xs ! (Suc i), tuple_encode i (rev (take (Suc i) xs)))"
    using Suc by (simp add: assms(1))
  finally show ?case by (simp add: Suc.prems take_Suc_conv_app_nth)
qed

corollary r_rev_aux_full:
  assumes "list_decode e = xs" and "length xs > 0"
  shows "eval r_rev_aux [length xs - 1, e] \<down>= tuple_encode (length xs - 1) (rev xs)"
  using r_rev_aux assms by simp

lemma r_rev_aux_total: "eval r_rev_aux [i, e] \<down>"
  using r_rev_aux_prim totalE by fastforce

definition "r_rev \<equiv>
  Cn 1 r_ifz
   [Id 1 0,
    Z,
    Cn 1 S
     [Cn 1 r_prod_encode
      [Cn 1 r_dec [r_length], Cn 1 r_rev_aux [Cn 1 r_dec [r_length], Id 1 0]]]]"

lemma r_rev_prim [simp]: "prim_recfn 1 r_rev"
  unfolding r_rev_def using r_rev_aux_prim by simp

lemma r_rev [simp]: "eval r_rev [e] \<down>= list_encode (rev (list_decode e))"
proof -
  let ?d = "Cn 1 r_dec [r_length]"
  let ?a = "Cn 1 r_rev_aux [?d, Id 1 0]"
  let ?p = "Cn 1 r_prod_encode [?d, ?a]"
  let ?s = "Cn 1 S [?p]"
  have eval_a: "eval ?a [e] = eval r_rev_aux [e_length e - 1, e]"
    using r_rev_aux_prim by simp
  then have "eval ?s [e] \<down>"
    using r_rev_aux_prim by (simp add: r_rev_aux_total)
  then have *: "eval r_rev [e] \<down>= (if e = 0 then 0 else the (eval ?s [e]))"
    using r_rev_aux_prim by (simp add: r_rev_def)
  show ?thesis
  proof (cases "e = 0")
    case True
    then show ?thesis using * by simp
  next
    case False
    then obtain xs where xs: "xs = list_decode e" "length xs > 0"
      using e_length_0 by auto
    then have len: "length xs = e_length e" by simp
    with eval_a have "eval ?a [e] = eval r_rev_aux [length xs - 1, e]"
      by simp
    then have "eval ?a [e] \<down>= tuple_encode (length xs - 1) (rev xs)"
      using xs r_rev_aux_full by simp
    then have "eval ?s [e] \<down>=
        Suc (prod_encode (length xs - 1, tuple_encode (length xs - 1) (rev xs)))"
      using len r_rev_aux_prim by simp
    then have "eval ?s [e] \<down>=
        Suc (prod_encode
              (length (rev xs) - 1, tuple_encode (length (rev xs) - 1) (rev xs)))"
      by simp
    moreover have "length (rev xs) > 0"
      using xs by simp
    ultimately have "eval ?s [e] \<down>= list_encode (rev xs)"
      by (metis list_encode.elims diff_Suc_1 length_Cons length_greater_0_conv)
    then show ?thesis using xs * by simp
  qed
qed

abbreviation e_cons :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "e_cons e es \<equiv> list_encode (e # list_decode es)"

lemma e_cons_elementary:
  "e_cons e es =
    (if es = 0 then Suc (prod_encode (0, e))
     else Suc (prod_encode (e_length es, prod_encode (e, pdec2 (es - 1)))))"
proof (cases "es = 0")
  case True
  then show ?thesis by simp
next
  case False
  then have "e_length es = Suc (pdec1 (es - 1))"
    by (metis list_decode.elims diff_Suc_1 tuple_decode_length)
  moreover have "es = e_tl (list_encode (e # list_decode es))"
    by (metis list.sel(3) list_decode_encode list_encode_decode)
  ultimately show ?thesis
    using False e_tl_elementary 
    by (metis list_decode.simps(2) diff_Suc_1 list_encode_decode prod.sel(1)
      prod_encode_inverse snd_conv tuple_decode.simps(2))
qed

definition "r_cons_else \<equiv>
  Cn 2 S
   [Cn 2 r_prod_encode
     [Cn 2 r_length
       [Id 2 1], Cn 2 r_prod_encode [Id 2 0, Cn 2 r_pdec2 [Cn 2 r_dec [Id 2 1]]]]]"

lemma r_cons_else_prim: "prim_recfn 2 r_cons_else"
  unfolding r_cons_else_def by simp

lemma r_cons_else:
  "eval r_cons_else [e, es] \<down>=
    Suc (prod_encode (e_length es, prod_encode (e, pdec2 (es - 1))))"
  unfolding r_cons_else_def by simp

definition "r_cons \<equiv>
  Cn 2 r_ifz
    [Id 2 1, Cn 2 S [Cn 2 r_prod_encode [r_constn 1 0, Id 2 0]], r_cons_else]"

lemma r_cons_prim [simp]: "prim_recfn 2 r_cons"
  unfolding r_cons_def using r_cons_else_prim by simp

lemma r_cons [simp]: "eval r_cons [e, es] \<down>= e_cons e es"
  unfolding r_cons_def using r_cons_else_prim r_cons_else e_cons_elementary by simp

abbreviation e_snoc :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "e_snoc es e \<equiv> list_encode (list_decode es @ [e])"

lemma e_nth_snoc_small [simp]:
  assumes "n < e_length b"
  shows "e_nth (e_snoc b z) n = e_nth b n"
  using assms by (simp add: nth_append)

lemma e_hd_snoc [simp]:
  assumes "e_length b > 0"
  shows "e_hd (e_snoc b x) = e_hd b"
proof -
  from assms have "b \<noteq> 0"
    using less_imp_neq by force
  then have hd: "e_hd b = hd (list_decode b)" by simp
  have "e_length (e_snoc b x) > 0" by simp
  then have "e_snoc b x \<noteq> 0"
    using not_gr_zero by fastforce
  then have "e_hd (e_snoc b x) = hd (list_decode (e_snoc b x))" by simp
  with assms hd show ?thesis by simp
qed

definition "r_snoc \<equiv> Cn 2 r_rev [Cn 2 r_cons [Id 2 1, Cn 2 r_rev [Id 2 0]]]"

lemma r_snoc_prim [simp]: "prim_recfn 2 r_snoc"
  unfolding r_snoc_def by simp

lemma r_snoc [simp]: "eval r_snoc [es, e] \<down>= e_snoc es e"
  unfolding r_snoc_def by simp

abbreviation e_butlast :: "nat \<Rightarrow> nat" where
  "e_butlast e \<equiv> list_encode (butlast (list_decode e))"

abbreviation e_take :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "e_take n x \<equiv> list_encode (take n (list_decode x))"

definition "r_take \<equiv>
  Cn 2 r_ifle
   [Id 2 0, Cn 2 r_length [Id 2 1],
    Pr 1 Z (Cn 3 r_snoc [Id 3 1, Cn 3 r_nth [Id 3 2, Id 3 0]]),
    Id 2 1]"

lemma r_take_prim [simp]: "prim_recfn 2 r_take"
  unfolding r_take_def by simp_all

lemma r_take:
  assumes "x = list_encode es"
  shows "eval r_take [n, x] \<down>= list_encode (take n es)"
proof -
  let ?g = "Cn 3 r_snoc [Id 3 1, Cn 3 r_nth [Id 3 2, Id 3 0]]"
  let ?h = "Pr 1 Z ?g"
  have "total ?h" using Mn_free_imp_total by simp
  have "m \<le> length es \<Longrightarrow> eval ?h [m, x] \<down>= list_encode (take m es)" for m
  proof (induction m)
    case 0
    then show ?case using assms r_take_def by (simp add: r_take_def)
  next
    case (Suc m)
    then have "m < length es" by simp
    then have "eval ?h [Suc m, x] = eval ?g [m, the (eval ?h [m, x]), x]"
      using Suc r_take_def by simp
    also have "... = eval ?g [m, list_encode (take m es), x]"
      using Suc by simp
    also have "... \<down>= e_snoc (list_encode (take m es)) (es ! m)"
      by (simp add: \<open>m < length es\<close> assms)
    also have "... \<down>= list_encode ((take m es) @ [es ! m])"
      using list_decode_encode by simp
    also have "... \<down>= list_encode (take (Suc m) es)"
      by (simp add: \<open>m < length es\<close> take_Suc_conv_app_nth)
    finally show ?case .
  qed
  moreover have "eval (Id 2 1) [m, x] \<down>= list_encode (take m es)" if "m > length es" for m
    using that assms by simp
  moreover have "eval r_take [m, x] \<down>=
      (if m \<le> e_length x then the (eval ?h [m, x]) else the (eval (Id 2 1) [m, x]))"
      for m
    unfolding r_take_def using \<open>total ?h\<close> by simp
  ultimately show ?thesis unfolding r_take_def by fastforce
qed

corollary r_take' [simp]: "eval r_take [n, x] \<down>= e_take n x"
  by (simp add: r_take)

definition "r_last \<equiv> Cn 1 r_hd [r_rev]"

lemma r_last_prim [simp]: "prim_recfn 1 r_last"
  unfolding r_last_def by simp

lemma r_last [simp]:
  assumes "e = list_encode xs" and "length xs > 0"
  shows "eval r_last [e] \<down>= last xs"
proof -
  from assms(2) have "length (rev xs) > 0" by simp
  then have "list_encode (rev xs) > 0"
    by (metis gr0I list.size(3) list_encode_0)
  moreover have "eval r_last [e] = eval r_hd [the (eval r_rev [e])]"
    unfolding r_last_def by simp
  ultimately show ?thesis using assms hd_rev by auto
qed

definition "r_update_aux \<equiv>
  let
    f = r_constn 2 0;
    g = Cn 5 r_snoc
         [Id 5 1, Cn 5 r_ifeq [Id 5 0, Id 5 3, Id 5 4, Cn 5 r_nth [Id 5 2, Id 5 0]]]
  in Pr 3 f g"

lemma r_update_aux_recfn: "recfn 4 r_update_aux"
  unfolding r_update_aux_def by simp

lemma r_update_aux:
  assumes "n \<le> e_length b"
  shows "eval r_update_aux [n, b, j, v] \<down>= list_encode ((take n (list_decode b))[j:=v])"
  using assms
proof (induction n)
  case 0
    then show ?case unfolding r_update_aux_def by simp
next
  case (Suc n)
  then have n: "n < e_length b"
    by simp
  let ?a = "Cn 5 r_nth [Id 5 2, Id 5 0]"
  let ?b = "Cn 5 r_ifeq [Id 5 0, Id 5 3, Id 5 4, ?a]"
  define g where "g \<equiv> Cn 5 r_snoc [Id 5 1, ?b]"
  then have g: "eval g [n, r, b, j, v] \<down>= e_snoc r (if n = j then v else e_nth b n)" for r
    by simp

  have "Pr 3 (r_constn 2 0) g = r_update_aux"
    using r_update_aux_def g_def by simp
  then have "eval r_update_aux [Suc n, b, j, v] =
      eval g [n, the (eval r_update_aux [n, b, j, v]), b, j, v]"
    using r_update_aux_recfn Suc n eval_Pr_converg_Suc
    by (metis arity.simps(5) length_Cons list.size(3) nat_less_le
      numeral_3_eq_3 option.simps(3))
  then have *: "eval r_update_aux [Suc n, b, j, v] \<down>= e_snoc
      (list_encode ((take n (list_decode b))[j:=v]))
      (if n = j then v else e_nth b n)"
    using g Suc by simp

  consider (j_eq_n) "j = n" | (j_less_n) "j < n" | (j_gt_n) "j > n"
    by linarith
  then show ?case
  proof (cases)
    case j_eq_n
    moreover from this have "(take (Suc n) (list_decode b))[j:=v] =
        (take n (list_decode b))[j:=v] @ [v]"
      using n
      by (metis length_list_update nth_list_update_eq take_Suc_conv_app_nth take_update_swap)
    ultimately show ?thesis using * by simp
  next
    case j_less_n
    moreover from this have "(take (Suc n) (list_decode b))[j:=v] =
        (take n (list_decode b))[j:=v] @ [(list_decode b) ! n]"
      using n
      by (simp add: le_eq_less_or_eq list_update_append min_absorb2 take_Suc_conv_app_nth)
    ultimately show ?thesis using * by auto
  next
    case j_gt_n
    moreover from this have "(take (Suc n) (list_decode b))[j:=v] =
        (take n (list_decode b))[j:=v] @ [(list_decode b) ! n]"
      using n take_Suc_conv_app_nth by auto
    ultimately show ?thesis using * by auto
  qed
qed

abbreviation e_update :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "e_update b j v \<equiv> list_encode ((list_decode b)[j:=v])"

definition "r_update \<equiv>
  Cn 3 r_update_aux [Cn 3 r_length [Id 3 0], Id 3 0, Id 3 1, Id 3 2]"

lemma r_update_recfn [simp]: "recfn 3 r_update"
  unfolding r_update_def using r_update_aux_recfn by simp

lemma r_update [simp]: "eval r_update [b, j, v] \<down>= e_update b j v"
  unfolding r_update_def using r_update_aux r_update_aux_recfn by simp

lemma e_length_update [simp]: "e_length (e_update b k v) = e_length b"
  by simp

definition e_append :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "e_append xs ys \<equiv> list_encode (list_decode xs @ list_decode ys)"

lemma e_length_append: "e_length (e_append xs ys) = e_length xs + e_length ys"
  using e_append_def by simp

lemma e_nth_append_small:
  assumes "n < e_length xs"
  shows "e_nth (e_append xs ys) n = e_nth xs n"
  using e_append_def assms by (simp add: nth_append)

lemma e_nth_append_big:
  assumes "n \<ge> e_length xs"
  shows "e_nth (e_append xs ys) n = e_nth ys (n - e_length xs)"
  using e_append_def assms e_nth by (simp add: less_diff_conv2 nth_append)

definition "r_append \<equiv>
  let
    f = Id 2 0;
    g = Cn 4 r_snoc [Id 4 1, Cn 4 r_nth [Id 4 3, Id 4 0]]
  in Cn 2 (Pr 2 f g) [Cn 2 r_length [Id 2 1], Id 2 0, Id 2 1]"

lemma r_append_prim [simp]: "prim_recfn 2 r_append"
  unfolding r_append_def by simp

lemma r_append [simp]: "eval r_append [a, b] \<down>= e_append a b"
proof -
  define g where "g = Cn 4 r_snoc [Id 4 1, Cn 4 r_nth [Id 4 3, Id 4 0]]"
  then have g: "eval g [j, r, a, b] \<down>= e_snoc r (e_nth b j)" for j r
    by simp
  let ?h = "Pr 2 (Id 2 0) g"
  have "eval ?h [n, a, b] \<down>= list_encode (list_decode a @ (take n (list_decode b)))"
      if "n \<le> e_length b" for n
    using that g g_def by (induction n) (simp_all add: take_Suc_conv_app_nth)
  then show ?thesis
    unfolding r_append_def g_def e_append_def by simp
qed

definition e_append_zeros :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "e_append_zeros b z \<equiv> e_append b (list_encode (replicate z 0))"

lemma e_append_zeros_length: "e_length (e_append_zeros b z) = e_length b + z"
  using e_append_def e_append_zeros_def by simp

lemma e_nth_append_zeros: "e_nth (e_append_zeros b z) i = e_nth b i"
  using e_append_zeros_def e_nth_append_small e_nth_append_big by auto

lemma e_nth_append_zeros_big:
  assumes "i \<ge> e_length b"
  shows "e_nth (e_append_zeros b z) i = 0"
  unfolding e_append_zeros_def
  using e_nth_append_big[of b i "list_encode (replicate z 0)", OF assms(1)]
  by simp

definition "r_append_zeros \<equiv>
  r_swap (Pr 1 (Id 1 0) (Cn 3 r_snoc [Id 3 1, r_constn 2 0]))"

lemma r_append_zeros_prim [simp]: "prim_recfn 2 r_append_zeros"
  unfolding r_append_zeros_def by simp

lemma r_append_zeros: "eval r_append_zeros [b, z] \<down>= e_append_zeros b z"
proof -
  let ?r = "Pr 1 (Id 1 0) (Cn 3 r_snoc [Id 3 1, r_constn 2 0])"
  have "eval ?r [z, b] \<down>= e_append_zeros b z"
    using e_append_zeros_def e_append_def
    by (induction z) (simp_all add: replicate_append_same)
  then show ?thesis by (simp add: r_append_zeros_def)
qed

end