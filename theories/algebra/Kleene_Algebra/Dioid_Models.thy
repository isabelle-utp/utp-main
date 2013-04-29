(* Title:      Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

header {* Models of Dioids *}

theory Dioid_Models
imports Dioid Real
begin

text {* In this section we consider some well known models of
dioids. These so far include the powerset dioid over a monoid,
languages, binary relations, sets of traces, sets paths (in a graph),
as well as the min-plus and the max-plus semirings. Most of these
models are taken from an article about Kleene algebras with
domain~\cite{desharnaismoellerstruth06kad}.

The advantage of formally linking these models with the abstract
axiomatisations of dioids is that all abstract theorems are
automatically available in all models. It therefore makes sense to
establish models for the strongest possible axiomatisations (whereas
theorems should be proved for the weakest ones). *}


subsection {* The Powerset Dioid over a Monoid *}

text {* We assume a multiplicative monoid and define the usual complex
product on sets of elements. We formalise the well known result that
this lifting induces a dioid. *}

instantiation set :: (monoid_mult) monoid_mult
begin

  definition one_set_def:
    "1 = {1}"

  definition c_prod_def: -- "the complex product"
    "A \<cdot> B = {u * v | u v. u \<in> A \<and> v \<in> B}"

  instance
  proof
    fix X Y Z :: "'a set"
     show "X \<cdot> Y \<cdot> Z = X \<cdot> (Y \<cdot> Z)"
      by (auto simp add: c_prod_def) (metis mult_assoc)+
    show "1 \<cdot> X = X"
      by (simp add: one_set_def c_prod_def)
    show "X \<cdot> 1 = X"
      by (simp add: one_set_def c_prod_def)
  qed

end (* instantiation *)

instantiation set :: (monoid_mult) dioid_one_zero
begin

  definition zero_set_def:
    "0 = {}"

  definition plus_set_def:
    "A + B = A \<union> B"

  instance
  proof
    fix X Y Z :: "'a set"
    show "X + Y + Z = X + (Y + Z)"
      by (simp add: Un_assoc plus_set_def)
    show "X + Y = Y + X"
      by (simp add: Un_commute plus_set_def)
    show "(X + Y) \<cdot> Z = X \<cdot> Z + Y \<cdot> Z"
      by (auto simp add: plus_set_def c_prod_def)
    show "1 \<cdot> X = X"
      by (simp add: one_set_def c_prod_def)
    show "X \<cdot> 1 = X"
      by (simp add: one_set_def c_prod_def)
    show "0 + X = X"
      by (simp add: plus_set_def zero_set_def)
    show "0 \<cdot> X = 0"
      by (simp add: c_prod_def zero_set_def)
    show "X \<cdot> 0 = 0"
      by (simp add: c_prod_def zero_set_def)
    show "X \<subseteq> Y \<longleftrightarrow> X + Y = Y"
      by (simp add: plus_set_def subset_Un_eq)
    show "X \<subset> Y \<longleftrightarrow> X \<subseteq> Y \<and> X \<noteq> Y"
      by (fact psubset_eq)
    show "X + X = X"
      by (simp add: Un_absorb plus_set_def)
    show "X \<cdot> (Y + Z) = X \<cdot> Y + X \<cdot> Z"
      by (auto simp add: plus_set_def c_prod_def)
  qed

end (* instantiation *)


subsection {* Language Dioids *}

text {* Language dioids arise as special cases of the monoidal lifting
because sets of words form free monoids. Moreover, monoids of words
are isomorphic to monoids of lists under append.

To show that languages form dioids it therefore suffices to show that
sets of lists closed under append and multiplication with the empty
word form a (multiplicative) monoid. Isabelle then does the rest of the work
automatically. Infix~@{text @} denotes word
concatenation. *}

instantiation list :: (type) monoid_mult
begin

  definition times_list_def:
    "xs * ys \<equiv> xs @ ys"

  definition one_list_def:
    "1 \<equiv> []"

  instance proof
    fix xs ys zs :: "'a list"
    show "xs * ys * zs = xs * (ys * zs)"
      by (simp add: times_list_def)
    show "1 * xs = xs"
      by (simp add: one_list_def times_list_def)
    show "xs * 1 = xs"
      by (simp add: one_list_def times_list_def)
  qed

end  (* instantiation *)

text {* Languages as sets of lists have already been formalised in
Isabelle in various places. We can now obtain much of their algebra
for free. *}

type_synonym 'a lan = "'a list set"

interpretation lan_dioid: dioid_one_zero "op +" "op \<cdot>" "1::'a lan" "0" "op \<subseteq>" "op \<subset>" ..


subsection {* Relation Dioids *}

text {* We now show that binary relations under union, relational
composition, the identity relation, the empty relation and set
inclusion form dioids. Due to the well developed relation library of
Isabelle this is entirely trivial. *}

interpretation rel_dioid: dioid_one_zero "op \<union>" "op O" Id "{}" "op \<subseteq>" "op \<subset>"
  by (unfold_locales, auto)

interpretation rel_monoid: monoid_mult Id "op O" ..


subsection {* Trace Dioids *}

text {* Traces have been considered, for instance, by
Kozen~\cite{kozen00hoare} in the context of Kleene algebras with
tests. Intuitively, a trace is an execution sequence of a labelled
transition system from some state to some other state, in which state
labels and action labels alternate, and which begin and end with a
state label.

Traces generalise words: words can be obtained from traces by
forgetting state labels. Similarly, sets of traces generalise
languages.

In this section we show that sets of traces under union, an
appropriately defined notion of complex product, the set of all traces
of length zero, the empty set of traces and set inclusion form a
dioid.

We first define the notion of trace and the product of traces, which
has been called \emph{fusion product} by Kozen. *}

type_synonym ('p, 'a) trace = "'p \<times> ('a \<times> 'p) list"

definition first :: "('p, 'a) trace \<Rightarrow> 'p" where
  "first = fst"

lemma first_conv [simp]: "first (p, xs) = p"
  by (unfold first_def, simp)

fun last :: "('p, 'a) trace \<Rightarrow> 'p" where
  "last (p, []) = p"
| "last (_, xs) = snd (List.last xs)"

lemma last_append [simp]: "last (p, xs @ ys) = last (last (p, xs), ys)"
proof (cases xs)
  show "xs = [] \<Longrightarrow> last (p, xs @ ys) = last (last (p, xs), ys)"
    by simp
  show "\<And>a list. xs = a # list \<Longrightarrow>
    last (p, xs @ ys) = last (last (p, xs), ys)"
  proof (cases ys)
    show "\<And>a list. \<lbrakk>xs = a # list; ys = []\<rbrakk>
      \<Longrightarrow> last (p, xs @ ys) = last (last (p, xs), ys)"
      by simp
    show "\<And>a list aa lista. \<lbrakk>xs = a # list; ys = aa # lista\<rbrakk>
      \<Longrightarrow> last (p, xs @ ys) = last (last (p, xs), ys)"
      by simp
  qed
qed

text {* The fusion product is a partial operation. It is undefined if
the last element of the first trace and the first element of the
second trace are different. If these elements are the same, then the
fusion product removes the first element from the second trace and
appends the resulting object to the first trace. *}

definition t_fusion :: "('p, 'a) trace \<Rightarrow> ('p, 'a) trace \<Rightarrow> ('p, 'a) trace" where
  "t_fusion x y \<equiv> if last x = first y then (fst x, snd x @ snd y) else undefined"

text {* We now show that the first element and the last element of a
trace are a left and right unit for that trace and prove some other
auxiliary lemmas. *}

lemma t_fusion_leftneutral [simp]: "t_fusion (first x, []) x = x"
  by (cases x, simp add: t_fusion_def)

lemma fusion_rightneutral [simp]: "t_fusion x (last x, []) = x"
  by (simp add: t_fusion_def)

lemma first_t_fusion [simp]: "last x = first y \<Longrightarrow> first (t_fusion x y) = first x"
  by (simp add: first_def t_fusion_def)

lemma last_t_fusion [simp]: "last x = first y \<Longrightarrow> last (t_fusion x y) = last y"
  by (metis (lifting) Dioid_Models.last_append first_def t_fusion_def pair_collapse)

text {* Next we show that fusion of traces is associative. *}

lemma t_fusion_assoc [simp]:
  "\<lbrakk> last x = first y; last y = first z \<rbrakk> \<Longrightarrow> t_fusion x (t_fusion y z) = t_fusion (t_fusion x y) z"
  by (cases x, cases y, cases z, simp add: t_fusion_def)


subsection {* Sets of Traces *}

text {* We now lift the fusion product to a complex product on sets of
traces. This operation is total. *}

no_notation
  times (infixl "\<cdot>" 70)

definition t_prod :: "('p, 'a) trace set \<Rightarrow> ('p, 'a) trace set \<Rightarrow> ('p, 'a) trace set" (infixl "\<cdot>" 70)
where "X \<cdot> Y = {t_fusion u v| u v. u \<in> X \<and> v \<in> Y \<and> last u = first v}"

text {* Next we define the empty set of traces and the set of traces
of length zero as the multiplicative unit of the trace dioid. *}

definition t_zero :: "('p, 'a) trace set" where
  "t_zero \<equiv> {}"

definition t_one :: "('p, 'a) trace set" where
  "t_one \<equiv> \<Union>p. {(p, [])}"

text {* We now provide elimination rules for trace products.*}

lemma t_prod_iff:
  "w \<in> X\<cdot>Y \<longleftrightarrow> (\<exists>u v. w = t_fusion u v \<and> u \<in> X \<and> v \<in> Y \<and> last u = first v)"
  by (unfold t_prod_def) auto

lemma t_prod_intro [simp, intro]:
  "\<lbrakk> u \<in> X; v \<in> Y; last u = first v \<rbrakk> \<Longrightarrow> t_fusion u v \<in> X\<cdot>Y"
  by (metis t_prod_iff)

lemma t_prod_elim [elim]:
  "w \<in> X\<cdot>Y \<Longrightarrow> \<exists>u v. w = t_fusion u v \<and> u \<in> X \<and> v \<in> Y \<and> last u = first v"
  by (metis t_prod_iff)

text {* Finally we prove the interpretation statement that sets of traces
under union and the complex product based on trace fusion together
with the empty set of traces and the set of traces of length one forms
a dioid. *}

interpretation trace_dioid: dioid_one_zero "op \<union>" t_prod t_one t_zero "op \<subseteq>" "op \<subset>"
apply unfold_locales
apply (auto simp add: t_prod_def t_one_def t_zero_def t_fusion_def)
apply (metis last_append)
apply (metis last_append append_assoc)
done

no_notation
  t_prod (infixl "\<cdot>" 70)


subsection {* The Path Diod *}

text {* The next model we consider are sets of paths in a graph. We
consider two variants, one that contains the empty path and one that
doesn't. The former leads to more difficult proofs and a more involved
specification of the complex product. We start with paths that include
the empty path. In this setting, a path is a list of nodes. *}

subsection {* Path Models with the Empty Path *}

type_synonym 'a path = "'a list"

text {* Path fusion is defined similarly to trace
fusion. Mathematically it should be a partial operation. The fusion of
two empty paths yields the empty path; the fusion between a non-empty
path and an empty one is undefined; the fusion of two non-empty paths
appends the tail of the second path to the first one.

We need to use a total alternative and make sure that undefined paths
do not contribute to the complex product.  *}

fun p_fusion :: "'a path \<Rightarrow> 'a path \<Rightarrow> 'a path" where
  "p_fusion [] _ = []"
| "p_fusion _ [] = []"
| "p_fusion ps (q # qs) = ps @ qs"

lemma p_fusion_assoc:
  "p_fusion ps (p_fusion qs rs) = p_fusion (p_fusion ps qs) rs"
proof (induct rs)
  case Nil show ?case
    by (metis list.exhaust p_fusion.simps(1) p_fusion.simps(2))
  case Cons show ?case
  proof (induct qs)
    case Nil show ?case
      by (metis neq_Nil_conv p_fusion.simps(1) p_fusion.simps(2))
    case Cons show ?case
      by (metis append_Cons append_assoc list.exhaust p_fusion.simps(1) p_fusion.simps(3))
  qed
qed

text {* This lemma overapproximates the real situation, but it holds
in all cases where path fusion should be defined. *}

lemma p_fusion_last:
  assumes "List.last ps = hd qs"
  and "ps \<noteq> []"
  and "qs \<noteq> []"
  shows "List.last (p_fusion ps qs) = List.last qs"
  by (metis (hide_lams, no_types) List.last.simps List.last_append append_Nil2 assms hd.simps neq_Nil_conv p_fusion.simps(3))

lemma p_fusion_hd: "\<lbrakk>ps \<noteq> []; qs \<noteq> []\<rbrakk> \<Longrightarrow> hd (p_fusion ps qs) = hd ps"
  by (metis list.exhaust p_fusion.simps(3) append_Cons hd.simps)

lemma nonempty_p_fusion: "\<lbrakk>ps \<noteq> []; qs \<noteq> []\<rbrakk> \<Longrightarrow> p_fusion ps qs \<noteq> []"
  by (metis list.exhaust append_Cons p_fusion.simps(3) list.simps(2))

text {* We now define a condition that filters out undefined paths in
the complex product. *}

abbreviation p_filter :: "'a path \<Rightarrow> 'a path \<Rightarrow> bool" where
"p_filter ps qs \<equiv> ((ps = [] \<and> qs = []) \<or> (ps \<noteq> [] \<and> qs \<noteq> [] \<and> (List.last ps) = hd qs))"

no_notation
  times (infixl "\<cdot>" 70)

definition p_prod :: "'a path set \<Rightarrow> 'a path set \<Rightarrow> 'a path set" (infixl "\<cdot>" 70)
where "X \<cdot> Y = {rs . \<exists>ps \<in> X. \<exists>qs \<in> Y. rs = p_fusion ps qs \<and> p_filter ps qs}"

lemma p_prod_iff:
  "ps \<in> X \<cdot> Y \<longleftrightarrow> (\<exists>qs rs. ps = p_fusion qs rs \<and> qs \<in> X \<and> rs \<in> Y \<and> p_filter qs rs)"
  by (unfold p_prod_def) auto

text {* Due to the complexity of the filter condition, proving
properties of complex products can be tedious. *}

lemma p_prod_assoc: "(X \<cdot> Y) \<cdot> Z = X \<cdot> (Y \<cdot> Z)"
proof (rule set_eqI)
  fix ps
  show "ps \<in> (X \<cdot> Y) \<cdot> Z \<longleftrightarrow> ps \<in> X \<cdot> (Y \<cdot> Z)"
  proof (cases ps)
    case Nil thus ?thesis
      by auto (metis nonempty_p_fusion p_prod_iff)+
  next
    case Cons thus ?thesis
      by (auto simp add: p_prod_iff) (metis (hide_lams, mono_tags) nonempty_p_fusion p_fusion_assoc p_fusion_hd p_fusion_last)+
  qed
qed

text {* We now define the multiplicative unit of the path dioid as the
set of all paths of length one, including the empty path, and show the
unit laws with respect to the path product. *}

definition p_one :: "'a path set" where
  "p_one \<equiv> {p . \<exists>q::'a. p = [q]} \<union> {[]}"

lemma p_prod_onel [simp]: "p_one \<cdot> X = X"
proof (rule set_eqI)
    fix ps
    show "ps \<in> p_one \<cdot> X \<longleftrightarrow> ps \<in> X"
    proof (cases ps)
      case Nil thus ?thesis
        by (auto simp add: p_one_def p_prod_def, metis nonempty_p_fusion not_Cons_self)
    next
      case Cons thus ?thesis
        by (auto simp add: p_one_def p_prod_def, metis append_Cons append_Nil hd.simps neq_Nil_conv p_fusion.simps(3), metis Cons_eq_appendI hd.simps last_ConsL list.simps(3) p_fusion.simps(3) self_append_conv2)
    qed
qed

lemma p_prod_oner [simp]: "X \<cdot> p_one = X"
proof (rule set_eqI)
    fix ps
    show "ps \<in> X \<cdot> p_one \<longleftrightarrow> ps \<in> X"
    proof (cases ps)
      case Nil thus ?thesis
        by (auto simp add: p_one_def p_prod_def, metis nonempty_p_fusion not_Cons_self2, metis p_fusion.simps(1))
    next
      case Cons thus ?thesis
        by (auto simp add: p_one_def p_prod_def, metis append_Nil2 neq_Nil_conv p_fusion.simps(3), metis hd.simps list.simps(2) p_fusion.simps(3) self_append_conv)
    qed
qed

text {* Next we show distributivity laws at the powerset level. *}

lemma p_prod_distl: "X \<cdot> (Y \<union> Z) = X \<cdot> Y \<union> X \<cdot> Z"
proof (rule set_eqI)
  fix ps
  show "ps \<in> X \<cdot> (Y \<union> Z) \<longleftrightarrow> ps \<in> X \<cdot> Y \<union> X \<cdot> Z"
  by (cases ps) (auto simp add: p_prod_iff)
qed


lemma p_prod_distr: "(X \<union> Y) \<cdot> Z = X \<cdot> Z \<union> Y \<cdot> Z"
proof (rule set_eqI)
  fix ps
  show "ps \<in> (X \<union> Y) \<cdot> Z \<longleftrightarrow> ps \<in> X \<cdot> Z \<union> Y \<cdot> Z"
    by (cases ps) (auto simp add: p_prod_iff)
qed

text {* Finally we show that sets of paths under union, the complex
product, the unit set and the empty set form a dioid. *}

interpretation path_dioid: dioid_one_zero "op \<union>" "op \<cdot>" p_one "{}" "op \<subseteq>" "op \<subset>"
proof
  fix x y z :: "'a path set"
  show  "x \<union> y \<union> z = x \<union> (y \<union> z)"
    by auto
  show "x \<union> y = y \<union> x"
    by auto
  show "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    by (fact p_prod_assoc)
  show "(x \<union> y) \<cdot> z = x \<cdot> z \<union> y \<cdot> z"
    by (fact p_prod_distr)
  show "p_one \<cdot> x = x"
    by (fact p_prod_onel)
  show "x \<cdot> p_one = x"
    by (fact p_prod_oner)
  show "{} \<union> x = x"
    by auto
  show "{} \<cdot> x = {}"
    by (metis all_not_in_conv p_prod_iff)
  show "x \<cdot> {} = {}"
    by (metis all_not_in_conv p_prod_iff)
  show "(x \<subseteq> y) = (x \<union> y = y)"
    by auto
  show "(x \<subset> y) = (x \<subseteq> y \<and> x \<noteq> y)"
    by auto
  show "x \<union> x = x"
    by auto
  show "x \<cdot> (y \<union> z) = x \<cdot> y \<union> x \<cdot> z"
    by (metis p_prod_distl)
qed

no_notation
  p_prod (infixl "\<cdot>" 70)


subsection {* Path Models without the Empty Path *}

text {* We now build a model of paths that does not include the empty
path and therefore leads to a simpler complex product. *}

datatype 'a ppath = Node 'a | Cons 'a "'a ppath"

primrec pp_first :: "'a ppath \<Rightarrow> 'a" where
  "pp_first (Node x)   = x"
| "pp_first (Cons x _) = x"

primrec pp_last :: "'a ppath \<Rightarrow> 'a" where
  "pp_last (Node x)    = x"
| "pp_last (Cons _ xs) = pp_last xs"

text {* The path fusion product (although we define it as a total
funcion) should only be applied when the last element of the first
argument is equal to the first element of the second argument. *}

primrec pp_fusion :: "'a ppath \<Rightarrow> 'a ppath \<Rightarrow> 'a ppath" where
  "pp_fusion (Node x) ys = ys"
| "pp_fusion (Cons x xs) ys = Cons x (pp_fusion xs ys)"

text {* We now go through the same steps as for traces and paths
before, showing that the first and last element of a trace a left or
right unit for that trace and that the fusion product on traces is
associative. *}

lemma pp_fusion_leftneutral [simp]: "pp_fusion (Node (pp_first x)) x = x"
  by simp

lemma pp_fusion_rightneutral [simp]: "pp_fusion x (Node (pp_last x)) = x"
  by (induct x) simp_all

lemma pp_first_pp_fusion [simp]:
  "pp_last x = pp_first y \<Longrightarrow> pp_first (pp_fusion x y) = pp_first x"
  by (induct x) simp_all

lemma pp_last_pp_fusion [simp]:
  "pp_last x = pp_first y \<Longrightarrow> pp_last (pp_fusion x y) = pp_last y"
  by (induct x) simp_all

lemma pp_fusion_assoc [simp]:
  "\<lbrakk> pp_last x = pp_first y; pp_last y = pp_first z \<rbrakk> \<Longrightarrow> pp_fusion x (pp_fusion y z) = pp_fusion (pp_fusion x y) z"
  by (induct x) simp_all

text {* We now lift the path fusion product to a complex product on
sets of paths. This operation is total. *}

definition pp_prod :: "'a ppath set \<Rightarrow> 'a ppath set \<Rightarrow> 'a ppath set" (infixl "\<cdot>" 70)
  where "X\<cdot>Y = {pp_fusion u v| u v. u \<in> X \<and> v \<in> Y \<and> pp_last u = pp_first v}"

text {* Next we define the set of paths of length one as the
multiplicative unit of the path dioid. *}

definition pp_one :: "'a ppath set" where
  "pp_one \<equiv> range Node"

text {* We again provide an
elimination rule. *}

lemma pp_prod_iff:
  "w \<in> X\<cdot>Y \<longleftrightarrow> (\<exists>u v. w = pp_fusion u v \<and> u \<in> X \<and> v \<in> Y \<and> pp_last u = pp_first v)"
  by (unfold pp_prod_def) auto

interpretation ppath_dioid: dioid_one_zero "op \<union>" "op \<cdot>" pp_one "{}" "op \<subseteq>" "op \<subset>"
proof
  fix x y z :: "'a ppath set"
  show "x \<union> y \<union> z = x \<union> (y \<union> z)"
    by auto
  show "x \<union> y = y \<union> x"
    by auto
  show "x \<cdot> y \<cdot> z = x \<cdot> (y \<cdot> z)"
    by (auto simp add: pp_prod_def, metis pp_first_pp_fusion pp_fusion_assoc, metis pp_last_pp_fusion)
  show "(x \<union> y) \<cdot> z = x \<cdot> z \<union> y \<cdot> z"
    by (auto simp add: pp_prod_def)
  show "pp_one \<cdot> x = x"
    by (auto simp add: pp_one_def pp_prod_def, metis pp_fusion.simps(1) pp_last.simps(1) rangeI)
  show "x \<cdot> pp_one = x"
    by (auto simp add: pp_one_def pp_prod_def, metis pp_first.simps(1) pp_fusion_rightneutral rangeI)
  show "{} \<union> x = x"
    by auto
  show "{} \<cdot> x = {}"
    by (simp add: pp_prod_def)
  show "x \<cdot> {} = {}"
    by (simp add: pp_prod_def)
  show "x \<subseteq> y \<longleftrightarrow> x \<union> y = y"
    by auto
   show "x \<subset> y \<longleftrightarrow> x \<subseteq> y \<and> x \<noteq> y"
     by auto
  show "x \<union> x = x"
    by auto
  show "x \<cdot> (y \<union> z) = x \<cdot> y \<union> x \<cdot> z"
    by (auto simp add: pp_prod_def)
qed

no_notation
  pp_prod (infixl "\<cdot>" 70)

subsection {* The Distributive Lattice Dioid *}

text {* A bounded distributive lattice is a distributive lattice with
a least and a greatest element. Using Isabelle's lattice theory file
we define a bounded distributive lattice as an axiomatic type class
and show, using a sublocale statement, that every bounded distributive
lattice is a dioid with one and zero. *}

class bounded_distributive_lattice = bounded_lattice + distrib_lattice

sublocale bounded_distributive_lattice \<subseteq> dioid_one_zero sup inf top bot less_eq
proof
  fix x y z
  show "sup (sup x y) z = sup x (sup y z)"
    by (fact sup_assoc)
  show "sup x y = sup y x"
    by (fact sup.commute)
  show "inf (inf x y) z = inf x (inf y z)"
    by (metis inf.commute inf.left_commute)
  show "inf (sup x y) z = sup (inf x z) (inf y z)"
    by (fact inf_sup_distrib2)
  show "inf top x = x"
    by simp
  show "inf x top = x"
    by simp
  show "sup bot x = x"
    by simp
  show "inf bot x = bot"
    by simp
  show "inf x bot = bot"
    by simp
  show "(x \<le> y) = (sup x y = y)"
    by (fact le_iff_sup)
  show "(x < y) = (x \<le> y \<and> x \<noteq> y)"
    by auto
  show "sup x x = x"
    by simp
  show "inf x (sup y z) = sup (inf x y) (inf x z)"
    by (fact inf_sup_distrib1)
qed


subsection {* The Boolean Dioid *}

text {* In this section we show that the booleans form a dioid,
because the booleans form a bounded distributive lattice.  *}

instantiation bool :: bounded_distributive_lattice
begin

  instance ..

end (* instantiation *)

interpretation boolean_dioid: dioid_one_zero sup inf True False less_eq less
  by (unfold_locales, simp_all add: inf_bool_def sup_bool_def)


subsection {* The Max-Plus Dioid *}

text {* The following dioids have important applications in
combinatorial optimisations, control theory, algorithm design and
computer networks. *}

text {* A definition of reals extended with~@{text "+\<infinity>"} {\em
and}~@{text "-\<infinity>"} may be found in {\em
HOL/Library/Extended\_Real.thy}. Alas, we require separate extensions
with either~@{text "+\<infinity>"} or~@{text "-\<infinity>"}. *}

text {* The carrier set of the max-plus semiring is the set of real
numbers extended by minus infinity. The operation of addition is
maximum, the operation of multiplication is addition, the additive
unit is minus infinity and the multiplicative unit is zero. *}

datatype mreal = mreal real | MInfty  -- "minus infinity"

fun mreal_max where
  "mreal_max (mreal x) (mreal y) = mreal (max x y)"
| "mreal_max x MInfty = x"
| "mreal_max MInfty y = y"

lemma mreal_max_simp_3 [simp]: "mreal_max MInfty y = y"
  by (cases y, simp_all)

fun mreal_plus where
  "mreal_plus (mreal x) (mreal y) = mreal (x + y)"
| "mreal_plus _ _ = MInfty"

text {* We now show that the max plus-semiring satisfies the axioms of
selective semirings, from which it follows that it satisfies the dioid
axioms. *}

instantiation mreal :: selective_semiring
begin

  definition zero_mreal_def:
    "0 \<equiv> MInfty"

  definition one_mreal_def:
    "1 \<equiv> mreal 0"

  definition plus_mreal_def:
    "x + y \<equiv> mreal_max x y"

  definition times_mreal_def:
    "x * y \<equiv> mreal_plus x y"

  definition less_eq_mreal_def:
    "(x::mreal) \<le> y \<equiv> x + y = y"

  definition less_mreal_def:
    "(x::mreal) < y \<equiv> x \<le> y \<and> x \<noteq> y"

  instance
  proof
    fix x y z :: mreal
    show "x + y + z = x + (y + z)"
      by (cases x, cases y, cases z, simp_all add: plus_mreal_def)
    show "x + y = y + x"
      by (cases x, cases y, simp_all add: plus_mreal_def)
    show "x * y * z = x * (y * z)"
      by (cases x, cases y, cases z, simp_all add: times_mreal_def)
    show "(x + y) * z = x * z + y * z"
      by (cases x, cases y, cases z, simp_all add: plus_mreal_def times_mreal_def)
    show "1 * x = x"
      by (cases x, simp_all add: one_mreal_def times_mreal_def)
    show "x * 1 = x"
      by (cases x, simp_all add: one_mreal_def times_mreal_def)
    show "0 + x = x"
      by (cases x, simp_all add: plus_mreal_def zero_mreal_def)
    show "0 * x = 0"
      by (cases x, simp_all add: times_mreal_def zero_mreal_def)
    show "x * 0 = 0"
      by (cases x, simp_all add: times_mreal_def zero_mreal_def)
    show "x \<le> y \<longleftrightarrow> x + y = y"
      by (metis less_eq_mreal_def)
    show "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
      by (metis less_mreal_def)
    show "x + y = x \<or> x + y = y"
      by (cases x, cases y, simp_all add: plus_mreal_def, metis linorder_le_cases min_max.le_iff_sup min_max.sup_absorb1)
    show "x * (y + z) = x * y + x * z"
      by (cases x, cases y, cases z, simp_all add: plus_mreal_def times_mreal_def)     qed

end (* instantiation *)

instantiation mreal :: dioid_one_zero
begin

  instance ..

end (* instantiation *)


subsection {* The Min-Plus Dioid *}

text {* The min-plus dioid is also known as {\em tropical
semiring}. Here we need to add a positive infinity to the real
numbers. The procedere follows that of max-plus semirings.  *}

datatype preal = preal real | PInfty  -- "plus infinity"

fun preal_min where
  "preal_min (preal x) (preal y) = preal (min x y)"
| "preal_min x PInfty = x"
| "preal_min PInfty y = y"

lemma preal_min_simp_3 [simp]: "preal_min PInfty y = y"
  by (cases y, simp_all)

fun preal_plus where
  "preal_plus (preal x) (preal y) = preal (x + y)"
| "preal_plus _ _ = PInfty"

instantiation preal :: selective_semiring
begin

  definition zero_preal_def:
    "0 \<equiv> PInfty"

  definition one_preal_def:
    "1 \<equiv> preal 0"

  definition plus_preal_def:
    "x + y \<equiv> preal_min x y"

  definition times_preal_def:
    "x * y \<equiv> preal_plus x y"

  definition less_eq_preal_def:
    "(x::preal) \<le> y \<equiv> x + y = y"

  definition less_preal_def:
    "(x::preal) < y \<equiv> x \<le> y \<and> x \<noteq> y"

  instance
  proof
    fix x y z :: preal
    show "x + y + z = x + (y + z)"
      by (cases x, cases y, cases z, simp_all add: plus_preal_def)
    show "x + y = y + x"
      by (cases x, cases y, simp_all add: plus_preal_def)
    show "x * y * z = x * (y * z)"
      by (cases x, cases y, cases z, simp_all add: times_preal_def)
    show "(x + y) * z = x * z + y * z"
      by (cases x, cases y, cases z, simp_all add: plus_preal_def times_preal_def)
    show "1 * x = x"
      by (cases x, simp_all add: one_preal_def times_preal_def)
    show "x * 1 = x"
      by (cases x, simp_all add: one_preal_def times_preal_def)
    show "0 + x = x"
      by (cases x, simp_all add: plus_preal_def zero_preal_def)
    show "0 * x = 0"
      by (cases x, simp_all add: times_preal_def zero_preal_def)
    show "x * 0 = 0"
      by (cases x, simp_all add: times_preal_def zero_preal_def)
    show "x \<le> y \<longleftrightarrow> x + y = y"
      by (metis less_eq_preal_def)
    show "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
      by (metis less_preal_def)
    show "x + y = x \<or> x + y = y"
     by (cases x, cases y, simp_all add: plus_preal_def, metis linorder_le_cases min_max.inf_absorb2 min_max.le_iff_inf)
    show "x * (y + z) = x * y + x * z"
      by (cases x, cases y, cases z, simp_all add: plus_preal_def times_preal_def)   qed

end (* instantiation *)

instantiation preal :: dioid_one_zero
begin

  instance ..

end (* instantiation *)

text {* Variants of min-plus and max-plus semirings can easily be
obtained. Here we formalise the min-plus semiring over the natural
numbers as an example. *}

datatype pnat = pnat nat | PInfty  -- "plus infinity"

fun pnat_min where
  "pnat_min (pnat x) (pnat y) = pnat (min x y)"
| "pnat_min x PInfty = x"
| "pnat_min PInfty x = x"

lemma pnat_min_simp_3 [simp]: "pnat_min PInfty y = y"
  by (cases y, simp_all)

fun pnat_plus where
  "pnat_plus (pnat x) (pnat y) = pnat (x + y)"
| "pnat_plus _ _ = PInfty"

instantiation pnat :: selective_semiring
begin

  definition zero_pnat_def:
    "0 \<equiv> PInfty"

  definition one_pnat_def:
    "1 \<equiv> pnat 0"

  definition plus_pnat_def:
    "x + y \<equiv> pnat_min x y"

  definition times_pnat_def:
    "x * y \<equiv> pnat_plus x y"

  definition less_eq_pnat_def:
    "(x::pnat) \<le> y \<equiv> x + y = y"

  definition less_pnat_def:
    "(x::pnat) < y \<equiv> x \<le> y \<and> x \<noteq> y"

  lemma zero_pnat_top: "(x::pnat) \<le> 1"
  by (cases x, simp_all add: less_eq_pnat_def plus_pnat_def one_pnat_def)

  instance
  proof
    fix x y z :: pnat
    show "x + y + z = x + (y + z)"
      by (cases x, cases y, cases z, simp_all add: plus_pnat_def)
    show "x + y = y + x"
      by (cases x, cases y, simp_all add: plus_pnat_def)
    show "x * y * z = x * (y * z)"
      by (cases x, cases y, cases z, simp_all add: times_pnat_def)
    show "(x + y) * z = x * z + y * z"
      by (cases x, cases y, cases z, simp_all add: plus_pnat_def times_pnat_def)
    show "1 * x = x"
      by (cases x, simp_all add: one_pnat_def times_pnat_def)
    show "x * 1 = x"
      by (cases x, simp_all add: one_pnat_def times_pnat_def)
    show "0 + x = x"
      by (cases x, simp_all add: plus_pnat_def zero_pnat_def)
    show "0 * x = 0"
      by (cases x, simp_all add: times_pnat_def zero_pnat_def)
    show "x * 0 = 0"
      by (cases x, simp_all add: times_pnat_def zero_pnat_def)
    show "x \<le> y \<longleftrightarrow> x + y = y"
      by (metis less_eq_pnat_def)
    show "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
      by (metis less_pnat_def)
    show "x + y = x \<or> x + y = y"
      by (cases x, cases y, simp_all add: plus_pnat_def, metis linorder_le_cases min_max.inf_absorb2 min_max.le_iff_inf)
    show "x * (y + z) = x * y + x * z"
      by (cases x, cases y, cases z, simp_all add: plus_pnat_def times_pnat_def)
  qed

end (* instantiation *)

instantiation pnat :: dioid_one_zero
begin

  instance ..

end (* instantiation *)

end
