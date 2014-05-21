(* Title:      Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

header {* Dioids *}

theory Dioid
imports Signatures
begin

subsection {* Join Semilattices *}

text {* Join semilattices can be axiomatised order-theoretically or
algebraically. A join semilattice (or upper semilattice) is either a
poset in which every pair of elements has a join (or least upper
bound), or a set endowed with an associative, commutative, idempotent
binary operation. It is well known that the order-theoretic definition
induces the algebraic one and vice versa. We start from the algebraic
axiomatisation because it is easily expandable to dioids, using
Isabelle's type class mechanism.

In Isabelle/HOL, a type class @{class semilattice_sup} is available.
Alas, we cannot use this type class because we need the symbol~@{text
"+"} for the join operation in the dioid expansion and subclass
proofs in Isabelle/HOL require the two type classes involved to have
the same fixed signature.

Using {\em add\_assoc} as a name for the first assumption in class
{\em join\_semilattice} would lead to name clashes: we will later
define classes that inherit from @{class semigroup_add}, which
provides its own assumption {\em add\_assoc}, and prove that these are
subclasses of {\em join\_semilattice}. Hence the primed name.
*}

class join_semilattice = plus_ord +
  assumes add_assoc' [simp]: "(x + y) + z = x + (y + z)"
  and add_comm [simp]: "x + y = y + x"
  and add_idem [simp]: "x + x = x"
begin

text {* The definition @{term "x \<le> y \<longleftrightarrow> x + y = y"} of the order is
hidden in class @{class plus_ord}.

We show some simple order-based properties of semilattices. The
first one states that every semilattice is a partial order. *}

subclass order
proof
  fix x y z :: 'a
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (metis add_comm less_def less_eq_def)
  show "x \<le> x"
    by (metis add_idem less_eq_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (metis add_assoc' less_eq_def)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (metis add_comm less_eq_def)
qed

text {* Next we show that joins are least upper bounds. *}

lemma add_ub1 [simp]: "x \<le> x + y"
  by (metis add_assoc' add_idem less_eq_def)

lemma add_ub2 [simp]: "y \<le> x + y"
  by (metis add_assoc' add_comm add_idem less_eq_def)

lemma add_lub_var: "x \<le> z \<longrightarrow> y \<le> z \<longrightarrow> x + y \<le> z"
  by (metis add_assoc' less_eq_def)

lemma add_lub: "x + y \<le> z \<longleftrightarrow> x \<le> z \<and> y \<le> z"
  by (metis add_lub_var add_ub1 add_ub2 order_trans)

text {* Next we prove that joins are isotone (order preserving). *}

lemma add_iso: "x \<le> y \<longrightarrow> x + z \<le> y + z"
  by (metis add_lub add_ub2 less_eq_def)

lemma add_iso_var: "x \<le> y \<longrightarrow> u \<le> v \<longrightarrow> x + u \<le> y + v"
  by (metis add_comm add_iso add_lub)

text {* The next lemma links the definition of order as @{term "x \<le> y
\<longleftrightarrow> x + y = y"}
with a perhaps more conventional one known, e.g., from
arithmetics. *}

lemma order_prop: "x \<le> y \<longleftrightarrow> (\<exists>z. x + z = y)"
proof
  assume "x \<le> y"
  hence "x + y = y"
    by (metis less_eq_def)
  thus "\<exists>z. x + z = y"
    by auto
next
  assume "\<exists>z. x + z = y"
  then obtain c where "x + c = y"
    by auto
  also have "x + c \<le> y"
    by (metis calculation eq_refl)
  thus "x \<le> y"
    by (metis add_ub1 calculation)
qed

end (* join_semilattice *)



subsection {* Join Semilattices with an Additive Unit *}

text {* We now expand join semilattices by an additive unit~$0$. Is
the least element with respect to the order, and therefore often
denoted by~@{text \<bottom>}. Semilattices with a least element are often
called \emph{bounded}. *}

class join_semilattice_zero = join_semilattice + zero +
  assumes add_zero_l [simp]: "0 + x = x"
begin

subclass comm_monoid_add
  by (unfold_locales, auto, metis add_assoc' add_comm, metis add_comm add_zero_l)

lemma zero_least [simp]: "0 \<le> x"
  by (metis add_zero_l less_eq_def)

lemma add_zero_r [simp]: "x + 0 = x"
  by (metis add_comm add_zero_l)

lemma zero_unique [simp]: "x \<le> 0 \<longleftrightarrow> x = 0"
  by (metis zero_least eq_iff)

lemma no_trivial_inverse: "x \<noteq> 0 \<longrightarrow> \<not>(\<exists>y. x + y = 0)"
  by (metis zero_unique order_prop)

end (* join_semilattice_zero *)



subsection {* Near Semirings *}

text {* \emph{Near semirings} (also called seminearrings) are
generalisations of near rings to the semiring case. They have been
studied, for instance, in G.~Pilz's book~\cite{pilz83nearrings} on
near rings. According to his definition, a near semiring consists of
an additive and a multiplicative semigroup that interact via a single
distributivity law (left or right). The additive semigroup is not
required to be commutative. The definition is influenced by partial
transformation semigroups.

We only consider near semirings in which addition is commutative, and
in which the right distributivity law holds. We call such near
semirings \emph{abelian}. *}

class ab_near_semiring = ab_semigroup_add + semigroup_mult +
  assumes distrib_right': "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"

subclass (in semiring) ab_near_semiring
  by (unfold_locales, metis distrib_right)


subsection {* Variants of Dioids *}

text {* A \emph{near dioid} is an abelian near semiring in which
addition is idempotent. This generalises the notion of (additively)
idempotent semirings by dropping one distributivity law. Near dioids
are a starting point for process algebras.

By modelling variants of dioids as variants of semirings in which
addition is idempotent we follow the tradition of
Birkhoff~\cite{birkhoff67lattices}, but deviate from the definitions
in Gondran and Minoux's book~\cite{gondran10graphs}. *}

class near_dioid = ab_near_semiring + plus_ord +
  assumes add_idem' [simp]: "x + x = x"
begin

text {* Since addition is idempotent, the additive (commutative)
semigroup reduct of a near dioid is a semilattice. Near dioids are
therefore ordered by the semilattice order. *}

subclass join_semilattice
by unfold_locales (auto simp add: add_commute add_left_commute)

text {* It follows that multiplication is right-isotone (but not
necessarily left-isotone). *}

lemma mult_isor: "x \<le> y \<longrightarrow> x \<cdot> z \<le> y \<cdot> z"
proof
  assume "x \<le> y"
  hence "x + y = y"
    by (metis less_eq_def)
  also have "x \<cdot> z + y \<cdot> z = (x + y) \<cdot> z"
    by (metis distrib_right')
  moreover have "... = y \<cdot> z"
    by (metis calculation)
  thus "x \<cdot> z \<le> y \<cdot> z"
    by (metis calculation less_eq_def)
qed

lemma "x \<le> y \<longrightarrow> z \<cdot> x \<le> z \<cdot> y"
  nitpick [expect=genuine] -- "3-element counterexample"
oops

text {* The next lemma states that, in every near dioid, left
isotonicity and left subdistributivity are equivalent. *}

lemma mult_isol_equiv_subdistl:
  "(\<forall>x y z. x \<le> y \<longrightarrow> z \<cdot> x \<le> z \<cdot> y) \<longleftrightarrow> (\<forall>x y z. z \<cdot> x \<le> z \<cdot> (x + y))"
  by (metis add_ub1 less_eq_def)

end (* near_dioid *)

text {* We now make multiplication in near dioids left isotone, which
is equivalent to left subdistributivity, as we have seen. The
corresponding structures form the basis of probabilistic Kleene
algebras~\cite{mciverweber05pka} and game
algebras~\cite{venema03gamealgebra}. We are not aware that these
structures have a special name, so we baptise them \emph{pre-dioids}.

We do not explicitly define pre-semirings since we have no application
for them. *}

class pre_dioid = near_dioid +
  assumes subdistl: "z \<cdot> x \<le> z \<cdot> (x + y)"
begin

text {* Now, obviously, left isotonicity follows from left
subdistributivity. *}

lemma subdistl_var: "z \<cdot> x + z \<cdot> y \<le> z \<cdot> (x + y)"
  by (metis add.commute add_lub subdistl)

lemma mult_isol: "x \<le> y \<longrightarrow> z \<cdot> x \<le> z \<cdot> y"
proof
  assume "x \<le> y"
  hence "x + y = y"
    by (metis less_eq_def)
  also have "z \<cdot> x + z \<cdot> y \<le> z \<cdot> (x + y)"
    by (metis subdistl_var)
  moreover have "... = z \<cdot> y"
    by (metis calculation)
  thus "z \<cdot> x \<le> z \<cdot> y"
    by (metis add_ub1 calculation order_trans)
qed

lemma mult_isol_var: "u \<le> x \<and> v \<le> y \<longrightarrow> u \<cdot> v \<le> x \<cdot> y"
  by (metis mult_isol mult_isor order_trans)

lemma mult_double_iso: "x \<le> y \<longrightarrow> w \<cdot> x \<cdot> z \<le> w \<cdot> y \<cdot> z"
  by (metis mult_isol mult_isor)

end (* pre_dioid *)

text {* By adding a full left distributivity law we obtain semirings
(which are already available in Isabelle/HOL as @{class semiring})
from near semirings, and dioids from near dioids. Dioids are therefore
idempotent semirings. *}

class dioid = near_dioid + semiring

subclass (in dioid) pre_dioid
  by (unfold_locales, metis order_prop distrib_left)


subsection {* Families of Nearsemirings with a Multiplicative Unit *}

text {* Multiplicative units are important, for instance, for defining
an operation of finite iteration or Kleene star on dioids. We do not
introduce left and right units separately since we have no application
for this. *}

class ab_near_semiring_one = ab_near_semiring + one +
  assumes mult_onel [simp]: "1 \<cdot> x = x"
  and mult_oner [simp]: "x \<cdot> 1 = x"
begin

subclass monoid_mult
by (unfold_locales, simp_all)

end (* ab_near_semiring_one *)

class near_dioid_one = near_dioid + ab_near_semiring_one

text {* For near dioids with one, it would be sufficient to require
$1+1=1$. This implies @{term "x+x=x"} for arbitray~@{term x} (but that
would lead to annoying redundant proof obligations in mutual
subclasses of @{class near_dioid_one} and @{class near_dioid} later).
*}

class pre_dioid_one = pre_dioid + near_dioid_one

class dioid_one = dioid + near_dioid_one

subclass (in dioid_one) pre_dioid_one ..


subsection {* Families of Nearsemirings with Additive Units *}

text {*
We now axiomatise an additive unit~$0$ for nearsemirings. The zero is
usually required to satisfy annihilation properties with respect to
multiplication. Due to applications we distinguish a zero which is
only a left annihilator from one that is also a right annihilator.
More briefly, we call zero either a left unit or a unit.

Semirings and dioids with a right zero only can be obtained from those
with a left unit by duality.
*}

class ab_near_semiring_one_zerol = ab_near_semiring_one + zero +
  assumes add_zerol [simp]: "0 + x = x"
  and annil [simp]: "0 \<cdot> x = 0"

begin (* ab_near_semiring_one_zerol *)

text {* Note that we do not require~$0 \neq 1$.  *}

lemma add_zeror [simp]: "x + 0 = x"
  by (metis add.commute add_zerol)

end (* ab_near_semiring_one_zerol *)

class near_dioid_one_zerol = near_dioid_one + ab_near_semiring_one_zerol

subclass (in near_dioid_one_zerol) join_semilattice_zero
  by (unfold_locales, metis add_zerol)

class pre_dioid_one_zerol = pre_dioid_one + ab_near_semiring_one_zerol

subclass (in pre_dioid_one_zerol) near_dioid_one_zerol ..

class semiring_one_zerol = semiring + ab_near_semiring_one_zerol

class dioid_one_zerol = dioid_one + ab_near_semiring_one_zerol

subclass (in dioid_one_zerol) pre_dioid_one_zerol ..

text {* We now make zero also a right annihilator. *}

class ab_near_semiring_one_zero = ab_near_semiring_one_zerol +
  assumes annir [simp]: "x \<cdot> 0 = 0"

class semiring_one_zero = semiring + ab_near_semiring_one_zero

class near_dioid_one_zero = near_dioid_one_zerol + ab_near_semiring_one_zero

class pre_dioid_one_zero = pre_dioid_one_zerol + ab_near_semiring_one_zero

subclass (in pre_dioid_one_zero) near_dioid_one_zero ..

class dioid_one_zero = dioid_one_zerol + ab_near_semiring_one_zero

subclass (in dioid_one_zero) pre_dioid_one_zero ..

subclass (in dioid_one_zero) semiring_one_zero ..


subsection {* Duality by Opposition *}

text {*
Swapping the order of multiplication in a semiring (or dioid) gives
another semiring (or dioid), called its \emph{dual} or
\emph{opposite}.
*}

definition (in times) opp_mult (infixl "\<odot>" 70)
  where "x \<odot> y \<equiv> y \<cdot> x"

lemma (in semiring_1) dual_semiring_1:
  "class.semiring_1 1 (op \<odot>) (op +) 0"
by unfold_locales (auto simp add: opp_mult_def mult_assoc distrib_right distrib_left)

lemma (in dioid_one_zero) dual_dioid_one_zero:
  "class.dioid_one_zero (op +) (op \<odot>) 1 0 (op \<le>) (op <)"
by unfold_locales (auto simp add: opp_mult_def mult_assoc distrib_right distrib_left)

subsection {* Selective Near Semirings *}

text {* In this section we briefly sketch a generalisation of the
notion of \emph{dioid}. Some important models, e.g. max-plus and
min-plus semirings, have that property. *}

class selective_near_semiring = ab_near_semiring + plus_ord +
  assumes select: "x + y = x \<or> x + y = y"
begin

lemma select_alt: "x + y \<in> {x,y}"
  by (metis insert_iff select)

text {* It follows immediately that every selective near semiring is a
near dioid. *}

subclass near_dioid
  by (unfold_locales, metis select)

text {* Moreover, the order in a selective near semiring is obviously
linear. *}

subclass linorder
  by (unfold_locales, metis add.commute add_ub1 select)

end (*selective_near_semiring*)

class selective_semiring = selective_near_semiring + semiring_one_zero
begin

subclass dioid_one_zero ..

end (* selective_semiring *)

end
