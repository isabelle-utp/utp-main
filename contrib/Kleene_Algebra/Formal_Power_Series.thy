(* Title:      Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

header {* Formal Power Series *}

theory Formal_Power_Series
imports Finite_Suprema
begin

subsection {* The Type of Formal Power Series*}

text {* Formal powerseries are functions from a free monoid into a
dioid. They have applications in formal language theory, e.g.,
weighted automata.

We show that formal power series with suitably defined operations and
functions form a dioid. Many of the underlying properties already hold
in weaker settings, where the target algebra is a semilattice or
semiring. We currently ignore this fact.

As usual, we represent free dioids by sets of lists.

Alternatively, the same result could also be obtained for formal power
series from finite monoids.

This theory generalises Amine Chaieb's development of formal power
series as functions from natural numbers, which may be found in {\em
HOL/Library/Formal\_Power\_Series.thy}. *}

typedef (open) ('a, 'b) fps = "{f::'a list \<Rightarrow> 'b. True}"
  morphisms fps_nth Abs_fps
  by simp

declare fps_nth_inverse [simp]

notation fps_nth (infixl "$" 75)

lemma expand_fps_eq: "p = q \<longleftrightarrow> (\<forall>n. p $ n = q $ n)"
by (simp add: fps_nth_inject [symmetric] fun_eq_iff)

lemma fps_ext: "(\<And>n. p $ n = q $ n) \<Longrightarrow> p = q"
by (simp add: expand_fps_eq)

lemma fps_nth_Abs_fps [simp]: "Abs_fps f $ n = f n"
by (simp add: Abs_fps_inverse)


subsection {* Definition of the Basic Elements~0 and~1 and the Basic
Operations of Addition and Multiplication *}

text {* The zero formal power series maps all elements of the monoid
(all lists) to zero. *}

instantiation fps :: (type,zero) zero
begin
  definition zero_fps where
    "0 = Abs_fps (\<lambda>n. 0)"
  instance ..
end

lemma fps_zero_nth [simp]: "0 $ n = 0"
unfolding zero_fps_def by simp

text {* The unit formal power series maps the monoidal unit (the empty
list) to one and all other elements to zero. *}

instantiation fps :: (type,"{one,zero}") one
begin
  definition one_fps where
    "1 = Abs_fps (\<lambda>n. if n = [] then 1 else 0)"
  instance ..
end

lemma fps_one_nth_Nil [simp]: "1 $ [] = 1"
unfolding one_fps_def by simp

lemma fps_one_nth_Cons [simp]: "1 $ (x # xs) = 0"
unfolding one_fps_def by simp

text {* Addition of formal power series is the usual pointwise
addition of functions. *}

instantiation fps :: (type,plus) plus
begin
  definition plus_fps where
    "f + g = Abs_fps (\<lambda>n. f $ n + g $ n)"
  instance ..
end

lemma fps_add_nth [simp]: "(f + g) $ n = f $ n + g $ n"
unfolding plus_fps_def by simp

text {* This directly shows that formal power series form a
semilattice with zero. *}

lemma fps_add_assoc: "((f::('a,'b::semigroup_add) fps) + g) + h = f + (g + h)"
unfolding plus_fps_def by (simp add: add_assoc)

lemma fps_add_comm [simp]: "(f::('a,'b::ab_semigroup_add) fps) + g = g + f"
unfolding plus_fps_def by (simp add: add_commute)

lemma fps_add_idem [simp]: "(f::('a,'b::join_semilattice) fps) + f = f"
unfolding plus_fps_def by simp

lemma fps_zerol [simp]: "(f::('a,'b::monoid_add) fps) + 0 = f"
unfolding plus_fps_def by simp

lemma fps_zeror [simp]: "0 + (f::('a,'b::monoid_add) fps) = f"
unfolding plus_fps_def by simp

text {* The product of formal power series is convolution. The product
of two formal powerseries at a list is obtained by splitting the list
into all possible prefix/suffix pairs, taking the product of the first
series applied to the first coordinate and the second series applied
to the second coordinate of each pair, and then adding the results. *}

instantiation fps :: (type,"{comm_monoid_add,times}") times
begin
  definition times_fps where
    "f * g = Abs_fps (\<lambda>n. \<Sum>{f $ y * g $ z |y z. n = y @ z})"
  instance ..
end

text {* We call the set of all prefix/suffix splittings of a
list~@{term xs} the \emph{splitset} of~@{term xs}. *}

definition splitset where
  "splitset xs \<equiv> {(p, q) | p q. xs = p @ q}"

text {* Altenatively, splitsets can be defined recursively, which
yields convenient simplification rules in Isabelle. *}

fun splitset_fun where
  "splitset_fun []       = {([], [])}"
| "splitset_fun (x # xs) = insert ([], x # xs) (apfst (Cons x) ` splitset_fun xs)"

lemma splitset_consl:
  "splitset (x # xs) = insert ([], x # xs) (apfst (Cons x) ` splitset xs)"
by (auto simp add: image_def splitset_def) (metis append_eq_Cons_conv)+

lemma splitset_eq_splitset_fun: "splitset xs = splitset_fun xs"
apply (induct xs)
 apply (simp add: splitset_def)
apply (simp add: splitset_consl)
done

text {* The definition of multiplication is now more precise. *}

lemma fps_mult_var:
  "(f * g) $ n = \<Sum>{f $ (fst p) * g $ (snd p) | p. p \<in> splitset n}"
by (simp add: times_fps_def splitset_def)

lemma fps_mult_image:
  "(f * g) $ n = \<Sum>((\<lambda>p. f $ (fst p) * g $ (snd p)) ` splitset n)"
by (simp only: Collect_mem_eq fps_mult_var fun_im)

text {* Next we show that splitsets are finite and non-empty. *}

lemma splitset_fun_finite [simp]: "finite (splitset_fun xs)"
  by (induct xs, simp_all)

lemma splitset_finite [simp]: "finite (splitset xs)"
  by (simp add: splitset_eq_splitset_fun)

lemma splitset_fun_nonempty [simp]: "splitset_fun xs \<noteq> {}"
  by (cases xs, simp_all)

lemma splitset_nonempty [simp]: "splitset xs \<noteq> {}"
  by (simp add: splitset_eq_splitset_fun)

text {* We now proceed with proving algebraic properties of formal
power series. *}

lemma fps_annil [simp]:
  "0 * (f::('a::type,'b::{comm_monoid_add,mult_zero}) fps) = 0"
by (rule fps_ext) (simp add: times_fps_def setsum_0')

lemma fps_annir [simp]:
  "(f::('a::type,'b::{comm_monoid_add,mult_zero}) fps) * 0 = 0"
by (simp add: fps_ext times_fps_def setsum_0')

lemma fps_distl:
  "(f::('a::type,'b::{join_semilattice_zero,semiring}) fps) * (g + h) = (f * g) + (f * h)"
by (simp add: fps_ext fps_mult_image right_distrib setsum_fun_sum)

lemma fps_distr:
  "((f::('a::type,'b::{join_semilattice_zero,semiring}) fps) + g) * h = (f * h) + (g * h)"
by (simp add: fps_ext fps_mult_image left_distrib setsum_fun_sum)

text {* The multiplicative unit laws are surprisingly tedious. For the
proof of the left unit law we use the recursive definition, which we
could as well have based on splitlists instead of splitsets.

However, a right unit law cannot simply be obtained along the lines of
this proofs. The reason is that an alternative recursive definition
that produces a unit with coordinates flipped would be needed. But
this is difficult to obtain without snoc lists. We therefore prove the
right unit law more directly by using properties of suprema. *}

lemma fps_onel [simp]:
  "1 * (f::('a::type,'b::{join_semilattice_zero,monoid_mult,mult_zero}) fps) = f"
proof (rule fps_ext)
  fix n :: "'a list"
  show "(1 * f) $ n = f $ n"
  proof (cases n)
    case Nil thus ?thesis
      by (simp add: times_fps_def)
  next
    case Cons thus ?thesis
      by (simp add: fps_mult_image splitset_eq_splitset_fun image_compose[symmetric] one_fps_def comp_def image_constant_conv)
  qed
qed

lemma fps_oner [simp]:
  "(f::('a::type,'b::{join_semilattice_zero,monoid_mult,mult_zero}) fps) * 1 = f"
proof (rule fps_ext)
  fix n :: "'a list"
  {
    fix z :: 'b
    have "(f * 1) $ n \<le> z \<longleftrightarrow> (\<forall>p \<in> splitset n. f $ (fst p) * 1 $ (snd p) \<le> z)"
      by (simp add: fps_mult_image setsum_fun_image_sup)
    also have "... \<longleftrightarrow> (\<forall>a b. n = a @ b \<longrightarrow> f $ a * 1 $ b \<le> z)"
      unfolding splitset_def by simp
    also have "... \<longleftrightarrow> (f $ n * 1 $ [] \<le> z)"
      by (metis append_Nil2 fps_one_nth_Cons fps_one_nth_Nil mult_zero_right neq_Nil_conv zero_least)
    finally have "(f * 1) $ n \<le> z \<longleftrightarrow> f $ n \<le> z"
      by simp
  }
  thus "(f * 1) $ n = f $ n"
    by (metis eq_iff)
qed

text {* Finally we prove associativity of convolution. This requires
splitting lists into three parts and rearranging these parts in two
different ways into splitsets. This rearrangement is captured by the
following technical lemma. *}

lemma splitset_rearrange:
  fixes F :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'b::join_semilattice_zero"
  shows "\<Sum>{\<Sum>{F (fst p) (fst q) (snd q) | q. q \<in> splitset (snd p)} | p. p \<in> splitset x} =
         \<Sum>{\<Sum>{F (fst q) (snd q) (snd p) | q. q \<in> splitset (fst p)} | p. p \<in> splitset x}"
    (is "?lhs = ?rhs")
proof -
  {
    fix z :: 'b
    have "?lhs \<le> z \<longleftrightarrow> (\<forall>p q r. x = p @ q @ r \<longrightarrow> F p q r \<le> z)"
      by (simp only: fset_to_im setsum_fun_image_sup splitset_finite)
         (auto simp add: splitset_def)
    hence "?lhs \<le> z \<longleftrightarrow> ?rhs \<le> z"
      by (simp only: fset_to_im setsum_fun_image_sup splitset_finite)
         (auto simp add: splitset_def)
  }
  thus ?thesis
    by (simp add: eq_iff)
qed

lemma fps_mult_assoc: "(f::('a::type,'b::dioid_one_zero) fps) * (g * h) = (f * g) * h"
proof (rule fps_ext)
  fix n :: "'a list"
  have "(f * (g * h)) $ n = \<Sum>{\<Sum>{f $ (fst p) * g $ (fst q) * h $ (snd q) | q. q \<in> splitset (snd p)} | p. p \<in> splitset n}"
    by (simp add: fps_mult_image setsum_sum_distl_fun mult_assoc)
  also have "... = \<Sum>{\<Sum>{f $ (fst q) * g $ (snd q) * h $ (snd p) | q. q \<in> splitset (fst p)} | p. p \<in> splitset n}"
    by (fact splitset_rearrange)
  finally show "(f * (g * h)) $ n = ((f * g) * h) $ n"
    by (simp add: fps_mult_image setsum_sum_distr_fun mult_assoc)
qed


subsection {* The Dioid Model of Formal Power Series *}

text {* We can now prove that formal power series form dioids. *}

subclass (in dioid_one_zero) mult_zero
proof
  fix x :: 'a
  show "0 * x = 0"
    by (fact annil)
  show "x * 0 = 0"
    by (fact annir)
qed

instantiation fps :: (type,dioid_one_zero) dioid_one_zero
begin

  definition less_eq_fps where
    "(f::('a,'b) fps) \<le> g \<longleftrightarrow> f + g = g"

  definition less_fps where
    "(f::('a,'b) fps) < g \<longleftrightarrow> f \<le> g \<and> f \<noteq> g"

  instance
  proof
    fix f g h :: "('a,'b) fps"
    show "f + g + h = f + (g + h)"
      by (fact fps_add_assoc)
    show "f + g = g + f"
      by (fact fps_add_comm)
    show "f * g * h = f * (g * h)"
      by (metis fps_mult_assoc)
    show "(f + g) * h = f * h + g * h"
      by (fact fps_distr)
    show "1 * f = f"
      by (fact fps_onel)
    show "f * 1 = f"
      by (fact fps_oner)
    show "0 + f = f"
      by (fact fps_zeror)
    show "0 * f = 0"
      by (fact fps_annil)
    show "f * 0 = 0"
      by (fact fps_annir)
    show "f \<le> g \<longleftrightarrow> f + g = g"
      by (fact less_eq_fps_def)
    show "f < g \<longleftrightarrow> f \<le> g \<and> f \<noteq> g"
      by (fact less_fps_def)
    show "f + f = f"
      by (fact fps_add_idem)
    show "f * (g + h) = f \<cdot> g + f \<cdot> h"
      by (fact fps_distl)
  qed

end (* instantiation *)

text {* We currently do not prove that formal power series form Kleene
algebras, since this is complicated. *}

end

