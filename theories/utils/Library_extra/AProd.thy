(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: AProd.thy                                                            *)
(* Author:Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Alternative Product type *}

theory AProd 
imports Main
begin

text {* Type classes only support one instantiation per type. For a type as important as products
        this is unfortunate as we frequently want two versions, e.g. orders, lattices. So to work
        around this problem we here create an isomorphic alternative product type and derive
        necessary laws. *}

typedef ('a, 'b) aprod = "UNIV :: ('a * 'b) set" ..

setup_lifting type_definition_aprod

lift_definition afst :: "('a, 'b) aprod \<Rightarrow> 'a" is fst .
lift_definition asnd :: "('a, 'b) aprod \<Rightarrow> 'b" is snd .
lift_definition aprod_case :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) aprod \<Rightarrow> 'c" is prod_case .

nonterminal atuple_args and apatterns

syntax
  "_atuple"      :: "'a => atuple_args => 'a * 'b"        ("(1<_,/ _>)")
  "_atuple_arg"  :: "'a => atuple_args"                   ("_")
  "_atuple_args" :: "'a => atuple_args => atuple_args"     ("_,/ _")
  "_apattern"    :: "[pttrn, apatterns] => pttrn"         ("'<_,/ _>")
  ""            :: "pttrn => apatterns"                  ("_")
  "_apatterns"   :: "[pttrn, apatterns] => apatterns"      ("_,/ _")

translations
  "<x,y>" == "CONST Abs_aprod (x, y)"
  "_apattern x y" => "CONST Abs_aprod x y"
  "_apatterns x y" => "CONST Abs_aprod x y"
  "_atuple x (_atuple_args y z)" == "_atuple x (_atuple_arg (_atuple y z))"
  "%<x, y, zs>. b" == "CONST aprod_case (%x <y, zs>. b)"
  "%<x, y>. b" == "CONST aprod_case (%x y. b)"
  "_abs (CONST Abs_aprod x y) t" => "%<x, y>. t"

lemma afst [simp]: "afst <x,y> = x"
  by (transfer, simp)

lemma asnd [simp]: "asnd <x,y> = y"
  by (transfer, simp)

lemma surjective_aprod: "x = <afst x, asnd x>"
  by (transfer, simp)

lemma aprod_case [simp]:
  "aprod_case f <x, y> = f x y"
  by (transfer, simp)


instantiation aprod :: (minus, minus) minus
begin

definition minus_aprod_def:
  "x - y = <afst x - afst y, asnd x - asnd y>"

instance ..
end

instantiation aprod :: (uminus, uminus) uminus
begin

definition uminus_aprod_def:
  "- x = < - afst x, - asnd x>"

instance ..
end

instantiation aprod :: (ord, ord) ord
begin

definition
  "x \<le> y \<longleftrightarrow> afst x \<le> afst y \<and> asnd x \<le> asnd y"

definition
  "(x::('a, 'b) aprod) < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

instance ..

end

instance aprod :: (order, order) order
  apply (intro_classes)
  apply (simp_all add: less_eq_aprod_def less_aprod_def)
  apply (transfer, auto)+
done

lemma afst_mono: "x \<le> y \<Longrightarrow> afst x \<le> afst y"
  unfolding less_eq_aprod_def by simp

lemma asnd_mono: "x \<le> y \<Longrightarrow> asnd x \<le> asnd y"
  unfolding less_eq_aprod_def by simp

lemma Pair_mono: "x \<le> x' \<Longrightarrow> y \<le> y' \<Longrightarrow> <x, y> \<le> <x', y'>"
  unfolding less_eq_aprod_def by (transfer, simp)

lemma Pair_le [simp]: "<a, b> \<le> <c, d> \<longleftrightarrow> a \<le> c \<and> b \<le> d"
  unfolding less_eq_aprod_def by (transfer, simp)

instantiation aprod :: (semilattice_inf, semilattice_inf) semilattice_inf
begin

definition
  "inf x y = <inf (afst x) (afst y), inf (asnd x) (asnd y)>"

lemma inf_Pair_Pair [simp]: "inf <a, b> <c, d> = <inf a c, inf b d>"
  unfolding inf_aprod_def by (transfer, simp)

lemma fst_inf [simp]: "afst (inf x y) = inf (afst x) (afst y)"
  unfolding inf_aprod_def by (transfer, simp)

lemma snd_inf [simp]: "asnd (inf x y) = inf (asnd x) (asnd y)"
  unfolding inf_aprod_def by (transfer, simp)

instance
  by (intro_classes, simp_all add: inf_aprod_def less_eq_aprod_def)

end

instantiation aprod :: (semilattice_sup, semilattice_sup) semilattice_sup
begin

definition
  "sup x y = <sup (afst x) (afst y), sup (asnd x) (asnd y)>"

lemma sup_Pair_Pair [simp]: "sup <a, b> <c, d> = <sup a c, sup b d>"
  unfolding sup_aprod_def by (transfer, simp)

lemma fst_sup [simp]: "afst (sup x y) = sup (afst x) (afst y)"
  unfolding sup_aprod_def by simp

lemma snd_sup [simp]: "asnd (sup x y) = sup (asnd x) (asnd y)"
  unfolding sup_aprod_def by simp

instance
  by (intro_classes, simp_all add: sup_aprod_def less_eq_aprod_def)

end

instance aprod :: (lattice, lattice) lattice ..

instance aprod :: (distrib_lattice, distrib_lattice) distrib_lattice
  apply (intro_classes)
  apply (simp_all add:sup_aprod_def inf_aprod_def)
  apply (transfer)
  apply (auto simp add: sup_inf_distrib1)
done

instantiation aprod :: (top, top) top
begin

definition
  "top = <top, top>"

instance ..

end

lemma afst_top [simp]: "afst top = top"
  unfolding top_aprod_def by simp

lemma asnd_top [simp]: "asnd top = top"
  unfolding top_aprod_def by simp

lemma aprod_top_top: "<top, top> = top"
  unfolding top_aprod_def by simp

instance aprod :: (order_top, order_top) order_top
  by default (auto simp add: top_aprod_def less_eq_aprod_def)

instantiation aprod :: (bot, bot) bot
begin

definition
  "bot = <bot, bot>"

instance ..

end

lemma afst_bot [simp]: "afst bot = bot"
  unfolding bot_aprod_def by simp

lemma asnd_bot [simp]: "asnd bot = bot"
  unfolding bot_aprod_def by simp

lemma aprod_bot_bot: "<bot, bot> = bot"
  unfolding bot_aprod_def by simp

instance aprod :: (order_bot, order_bot) order_bot
  by default (auto simp add: bot_aprod_def less_eq_aprod_def)

instance aprod :: (bounded_lattice, bounded_lattice) bounded_lattice ..

instance aprod :: (boolean_algebra, boolean_algebra) boolean_algebra
  apply (intro_classes, simp_all add: inf_aprod_def sup_aprod_def bot_aprod_def top_aprod_def)
  apply (metis afst asnd.abs_eq inf_compl_bot snd_conv uminus_aprod_def)
  apply (metis afst asnd sup_compl_top uminus_aprod_def)
  proof -
    fix x :: "('a, 'b) aprod" and y :: "('a, 'b) aprod"
    have "<afst x - afst y, inf (asnd x) (- asnd y)> = x - y"
      by (metis diff_eq minus_aprod_def)
      thus "  x - y = <inf (afst x) (afst (- y)), inf (asnd x) (asnd (- y))>"
        by (metis afst asnd diff_eq uminus_aprod_def)
  qed




subsection {* Complete lattice operations *}

instantiation aprod :: (complete_lattice, complete_lattice) complete_lattice
begin

definition
  "Sup A = <SUP x:A. afst x, SUP x:A. asnd x>"

definition
  "Inf A = <INF x:A. afst x, INF x:A. asnd x>"

instance
  by default (simp_all add: less_eq_aprod_def Inf_aprod_def Sup_aprod_def
    INF_lower SUP_upper le_INF_iff SUP_le_iff bot_aprod_def top_aprod_def)

end

lemma afst_Sup: "afst (Sup A) = (SUP x:A. afst x)"
  unfolding Sup_aprod_def by simp

lemma asnd_Sup: "asnd (Sup A) = (SUP x:A. asnd x)"
  unfolding Sup_aprod_def by simp

lemma afst_Inf: "afst (Inf A) = (INF x:A. afst x)"
  unfolding Inf_aprod_def by simp

lemma asnd_Inf: "asnd (Inf A) = (INF x:A. asnd x)"
  unfolding Inf_aprod_def by simp

lemma afst_SUP: "afst (SUP x:A. f x) = (SUP x:A. afst (f x))"
  by (simp add: SUP_def afst_Sup image_image)

lemma asnd_SUP: "asnd (SUP x:A. f x) = (SUP x:A. asnd (f x))"
  by (simp add: SUP_def asnd_Sup image_image)

lemma afst_INF: "afst (INF x:A. f x) = (INF x:A. afst (f x))"
  by (simp add: INF_def afst_Inf image_image)

lemma asnd_INF: "asnd (INF x:A. f x) = (INF x:A. asnd (f x))"
  by (simp add: INF_def asnd_Inf image_image)

lemma SUP_aprod: "(SUP x:A. <f x, g x>) = <SUP x:A. f x, SUP x:A. g x>"
  by (simp add: SUP_def Sup_aprod_def image_image)

lemma INF_aprod: "(INF x:A. <f x, g x>) = <INF x:A. f x, INF x:A. g x>"
  by (simp add: INF_def Inf_aprod_def image_image)

text {* Alternative formulations for set infima and suprema over the product
of two complete lattices: *}

lemma Inf_aprod_alt_def: "Inf A = <Inf (afst ` A), Inf (asnd ` A)>"
by (auto simp: Inf_aprod_def INF_def)

lemma Sup_aprod_alt_def: "Sup A = <Sup (afst ` A), Sup (asnd ` A)>"
by (auto simp: Sup_aprod_def SUP_def)

lemma INFI_prod_alt_def: "INFI A f = <INFI A (afst o f), INFI A (asnd o f)>"
by (auto simp: INF_def Inf_aprod_def image_compose)

lemma SUPR_aprod_alt_def: "SUPR A f = <SUPR A (afst o f), SUPR A (asnd o f)>"
by (auto simp: SUP_def Sup_aprod_def image_compose)

lemma INF_aprod_alt_def:
  "(INF x:A. f x) = <INF x:A. afst (f x), INF x:A. asnd (f x)>"
by (metis afst_INF asnd_INF surjective_aprod)

lemma SUP_aprod_alt_def:
  "(SUP x:A. f x) = <SUP x:A. afst (f x), SUP x:A. asnd (f x)>"
by (metis afst_SUP asnd_SUP surjective_aprod)

subsection {* Complete distributive lattices *}

(* Contribution: Alessandro Coglio *)

instance aprod ::
  (complete_distrib_lattice, complete_distrib_lattice) complete_distrib_lattice
proof
  case goal1 thus ?case
    by (auto simp: sup_aprod_def Inf_aprod_def INF_aprod_alt_def sup_Inf sup_INF)
next
  case goal2 thus ?case
    by (auto simp: inf_aprod_def Sup_aprod_def SUP_aprod_alt_def inf_Sup inf_SUP)
qed

end
