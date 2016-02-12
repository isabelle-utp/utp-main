section {* UTP expressions *}

theory utp_expr
imports 
  utp_var
  utp_dvar
begin

text {* Before building the predicate model, we will build a model of expressions that generalise
        alphabetised predicates. Expressions are represented semantically as mapping from
        the alphabet to the expression's type. This general model will allow us to unify
        all constructions under one type. All definitions in the file are given using
        the \emph{lifting} package. 

        Since we have two kinds of variable (deep and shallow) in the model, we will also need
        two versions of each construct that takes a variable. We make use of adhoc-overloading
        to ensure the correct instance is automatically chosen, within the user noticing a difference. *}

typedef ('t, '\<alpha>) uexpr = "UNIV :: ('\<alpha> alphabet \<Rightarrow> 't) set" ..

notation Rep_uexpr ("\<lbrakk>_\<rbrakk>\<^sub>e")

lemma uexpr_eq_iff:
  "e = f \<longleftrightarrow> (\<forall> b. \<lbrakk>e\<rbrakk>\<^sub>e b = \<lbrakk>f\<rbrakk>\<^sub>e b)"
  using Rep_uexpr_inject[of e f, THEN sym] by (auto)

setup_lifting type_definition_uexpr

text {* A variable expression corresponds to the lookup function of the variable. *}

lift_definition var :: "('t, '\<alpha>) uvar \<Rightarrow> ('t, '\<alpha>) uexpr" is var_lookup .

declare [[coercion_enabled]]
declare [[coercion var]]

definition dvar_exp :: "'t::continuum dvar \<Rightarrow> ('t, '\<alpha>::vst) uexpr"
where "dvar_exp x = var (dvar_lift x)"

text {* We can then define specific cases for input and output variables, that simply perform
        tuple lifting. We also have variants for deep variables. *}

definition iuvar :: "('t, '\<alpha>) uvar \<Rightarrow> ('t, '\<alpha> \<times> '\<beta>) uexpr" 
where "iuvar x = var (in_var x)"

definition ouvar :: "('t, '\<beta>) uvar \<Rightarrow> ('t, '\<alpha> \<times> '\<beta>) uexpr" 
where "ouvar x = var (out_var x)"

definition idvar :: "'t::continuum dvar \<Rightarrow> ('t, '\<alpha>::vst \<times> '\<beta>) uexpr"
where "idvar x = var (in_var (dvar_lift x))"

definition odvar :: "'t::continuum dvar \<Rightarrow> ('t, '\<alpha> \<times> '\<beta>::vst) uexpr"
where "odvar x = var (out_var (dvar_lift x))"

text {* A literal is simply a constant function expression, always returning the same value. *}

lift_definition lit :: "'t \<Rightarrow> ('t, '\<alpha>) uexpr" 
  is "\<lambda> v b. v" .

text {* We define lifting for unary, binary, and ternary functions, that simply apply
        the function to all possible results of the expressions. *}

lift_definition uop :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr" 
  is "\<lambda> f e b. f (e b)" .
lift_definition bop :: 
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr" 
  is "\<lambda> f u v b. f (u b) (v b)" .
lift_definition trop :: 
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr \<Rightarrow> ('d, '\<alpha>) uexpr" 
  is "\<lambda> f u v w b. f (u b) (v b) (w b)" .

text {* We define syntax for expressions using adhoc overloading -- this allows us to later define
        operators on different types if necessary (e.g. when adding types for new UTP theories). *}

consts
  ulit   :: "'t \<Rightarrow> 'e" ("\<guillemotleft>_\<guillemotright>")
  ueq    :: "'a \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "=\<^sub>u" 50)
  ueuvar :: "'v \<Rightarrow> 'p" 
  uiuvar :: "'v \<Rightarrow> 'p"
  uouvar :: "'v \<Rightarrow> 'p"

adhoc_overloading
  ulit lit and
  ueuvar var and
  ueuvar dvar_exp and
  uiuvar iuvar and
  uiuvar idvar and
  uouvar ouvar and
  uouvar odvar

syntax 
  "_uuvar"  :: "('t, '\<alpha>) uvar \<Rightarrow> logic" ("&_" [999] 999)
  "_uiuvar" :: "('t, '\<alpha>) uvar \<Rightarrow> logic" ("$_" [999] 999)
  "_uouvar" :: "('t, '\<alpha>) uvar \<Rightarrow> logic" ("$_\<acute>" [999] 999)

translations
  "&x"  == "CONST ueuvar x"
  "$x"  == "CONST uiuvar x"
  "$x\<acute>" == "CONST uouvar x"

text {* We also set up some useful standard arithmetic operators for Isabelle by lifting
        the functions to binary operators. *}

instantiation uexpr :: (plus, type) plus
begin
  definition plus_uexpr_def: "u + v = bop (op +) u v"
instance ..
end

text {* Instantiating uminus also provides negation for predicates later *}

instantiation uexpr :: (uminus, type) uminus
begin
  definition uminus_uexpr_def: "- u = uop uminus u"
instance ..
end

instantiation uexpr :: (minus, type) minus
begin
  definition minus_uexpr_def: "u - v = bop (op -) u v"
instance ..
end

instantiation uexpr :: (times, type) times
begin
  definition times_uexpr_def: "u * v = bop (op *) u v"
instance ..
end

instantiation uexpr :: (Divides.div, type) Divides.div
begin
  definition div_uexpr_def: "u div v = bop (op div) u v"
  definition mod_uexpr_def: "u mod v = bop (op mod) u v"
instance ..
end

instantiation uexpr :: (zero, type) zero
begin
  definition zero_uexpr_def: "0 = lit 0"
instance ..
end

instantiation uexpr :: (one, type) one
begin
  definition one_uexpr_def: "1 = lit 1"
instance ..

end

instance uexpr :: (semigroup_mult, type) semigroup_mult
  by (intro_classes) (simp add: times_uexpr_def one_uexpr_def, transfer, simp add: mult.assoc)+

instance uexpr :: (monoid_mult, type) monoid_mult
  by (intro_classes) (simp add: times_uexpr_def one_uexpr_def, transfer, simp)+

instance uexpr :: (semigroup_add, type) semigroup_add
  by (intro_classes) (simp add: plus_uexpr_def zero_uexpr_def, transfer, simp add: add.assoc)+

instance uexpr :: (monoid_add, type) monoid_add
  by (intro_classes) (simp add: plus_uexpr_def zero_uexpr_def, transfer, simp)+

instance uexpr :: (numeral, type) numeral
  by (intro_classes, simp add: plus_uexpr_def, transfer, simp add: add.assoc)

text {* Set up automation for numerals *}

lemma numeral_uexpr_rep_eq: "\<lbrakk>numeral x\<rbrakk>\<^sub>e b = numeral x"
  by (induct x, simp_all add: plus_uexpr_def one_uexpr_def numeral.simps lit.rep_eq bop.rep_eq)

lemma numeral_uexpr_simp: "numeral x = \<guillemotleft>numeral x\<guillemotright>"
  by (simp add: uexpr_eq_iff numeral_uexpr_rep_eq lit.rep_eq)

definition eq_upred :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr"
where "eq_upred x y = bop HOL.eq x y"

adhoc_overloading
  ueq eq_upred

abbreviation seq_filter :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"seq_filter A \<equiv> filter (\<lambda> x. x \<in> A)"

nonterminal utuple_args and umaplet and umaplets

syntax
  "_unil"       :: "('a list, '\<alpha>) uexpr" ("\<langle>\<rangle>")
  "_ulist"      :: "args => ('a list, '\<alpha>) uexpr"    ("\<langle>(_)\<rangle>")
  "_uappend"    :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (infixr "^\<^sub>u" 80)
  "_ulast"      :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("last\<^sub>u'(_')")
  "_ufilter"    :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (infixl "\<restriction>\<^sub>u" 75)
  "_uless"      :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "<\<^sub>u" 50)
  "_uleq"       :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<le>\<^sub>u" 50)
  "_ugreat"     :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix ">\<^sub>u" 50)
  "_ugeq"       :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<ge>\<^sub>u" 50)
  "_uempset"    :: "('a set, '\<alpha>) uexpr" ("{}\<^sub>u")
  "_uset"       :: "args => ('a set, '\<alpha>) uexpr" ("{(_)}\<^sub>u")
  "_uunion"     :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" (infixl "\<union>\<^sub>u" 65)
  "_uinter"     :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" (infixl "\<inter>\<^sub>u" 70)
  "_umem"       :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<in>\<^sub>u" 50)
  "_unmem"      :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<notin>\<^sub>u" 50)
  "_usubset"    :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<subset>\<^sub>u" 50)
  "_usubseteq"  :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<subseteq>\<^sub>u" 50)
  "_utuple"     :: "('a, '\<alpha>) uexpr \<Rightarrow> utuple_args \<Rightarrow> ('a * 'b, '\<alpha>) uexpr" ("(1'(_,/ _')\<^sub>u)")
  "_utuple_arg"  :: "('a, '\<alpha>) uexpr \<Rightarrow> utuple_args" ("_")
  "_utuple_args" :: "('a, '\<alpha>) uexpr => utuple_args \<Rightarrow> utuple_args"     ("_,/ _")
  "_uunit"      :: "('a, '\<alpha>) uexpr" ("'(')\<^sub>u")
  "_ufst"       :: "('a \<times> 'b, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<pi>\<^sub>1'(_')")
  "_usnd"       :: "('a \<times> 'b, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr" ("\<pi>\<^sub>2'(_')")
  "_uapply"     :: "('a \<Rightarrow> 'b, '\<alpha>) uexpr \<Rightarrow> utuple_args \<Rightarrow> ('b, '\<alpha>) uexpr" ("_\<lparr>_\<rparr>\<^sub>u" [999,0] 999)
  "_udom"       :: "logic \<Rightarrow> logic" ("dom\<^sub>u'(_')")
  "_uran"       :: "logic \<Rightarrow> logic" ("ran\<^sub>u'(_')")
  "_uinl"       :: "logic \<Rightarrow> logic" ("inl\<^sub>u'(_')")
  "_uinr"       :: "logic \<Rightarrow> logic" ("inr\<^sub>u'(_')")
  "_umap_empty" :: "logic" ("[]\<^sub>u")
  "_umap_apply" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<lparr>_\<rparr>\<^sub>m" [999,0] 999)
  "_umap_plus"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<oplus>\<^sub>m" 85)
  "_umap_minus" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<ominus>\<^sub>m" 85)
  "_umaplet"    :: "[logic, logic] => umaplet" ("_ /\<mapsto>\<^sub>u/ _")
  ""            :: "umaplet => umaplets"             ("_")
  "_UMaplets"   :: "[umaplet, umaplets] => umaplets" ("_,/ _")
  "_UMapUpd"    :: "[logic, umaplets] => logic" ("_/'(_')" [900,0] 900)
  "_UMap"       :: "umaplets => logic" ("(1[_])")

definition "fun_apply f x = f x"
declare fun_apply_def [simp]

definition "map_upd = (\<lambda> f x v. fun_upd f x (Some v))"

definition map_apply :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("_'(_')\<^sub>m" [999,0] 999) where
"map_apply = (\<lambda> f x. the (f x))"

definition map_minus :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" (infixl "--" 100) 
where "map_minus f g = (\<lambda> x. if (f x = g x) then None else f x)" 

translations
  "\<langle>\<rangle>"       == "\<guillemotleft>[]\<guillemotright>"
  "\<langle>x, xs\<rangle>"  == "CONST bop (op #) x \<langle>xs\<rangle>"
  "\<langle>x\<rangle>"      == "CONST bop (op #) x \<guillemotleft>[]\<guillemotright>"
  "x ^\<^sub>u y"   == "CONST bop (op @) x y"
  "last\<^sub>u(xs)" == "CONST uop CONST last xs"
  "xs \<restriction>\<^sub>u A"   == "CONST bop CONST seq_filter A xs"
  "x <\<^sub>u y"   == "CONST bop (op <) x y"
  "x \<le>\<^sub>u y"   == "CONST bop (op \<le>) x y" 
  "x >\<^sub>u y"   == "y <\<^sub>u x"
  "x \<ge>\<^sub>u y"   == "y \<le>\<^sub>u x" 
  "{}\<^sub>u"      == "\<guillemotleft>{}\<guillemotright>"
  "{x, xs}\<^sub>u" == "CONST bop (CONST insert) x {xs}\<^sub>u"
  "{x}\<^sub>u"     == "CONST bop (CONST insert) x \<guillemotleft>{}\<guillemotright>"
  "A \<union>\<^sub>u B"   == "CONST bop Set.union A B"
  "A \<inter>\<^sub>u B"   == "CONST bop Set.inter A B"
  "x \<in>\<^sub>u A"   == "CONST bop (op \<in>) x A"
  "x \<notin>\<^sub>u A"   == "CONST bop (op \<notin>) x A"
  "A \<subset>\<^sub>u B"   == "CONST bop (op \<subset>) A B"
  "A \<subseteq>\<^sub>u B"   == "CONST bop (op \<subseteq>) A B"
  "()\<^sub>u"      == "\<guillemotleft>()\<guillemotright>"
  "(x, y)\<^sub>u"  == "CONST bop (CONST Pair) x y"
  "_utuple x (_utuple_args y z)" == "_utuple x (_utuple_arg (_utuple y z))"
  "\<pi>\<^sub>1(x)"    == "CONST uop CONST fst x"
  "\<pi>\<^sub>2(x)"    == "CONST uop CONST snd x"
  "f\<lparr>x\<rparr>\<^sub>u"    == "CONST bop CONST fun_apply f x"
  "dom\<^sub>u(f)" == "CONST uop CONST dom f"
  "ran\<^sub>u(f)" == "CONST uop CONST ran f"
  "inl\<^sub>u(x)" == "CONST uop CONST Inl x"
  "inr\<^sub>u(x)" == "CONST uop CONST Inr x"
  "f\<lparr>x\<rparr>\<^sub>m"   == "CONST bop CONST map_apply f x"
  "f \<oplus>\<^sub>m g" == "CONST bop CONST map_add f g"
  "f \<ominus>\<^sub>m g" == "CONST bop CONST map_minus f g"
  "[]\<^sub>u"     == "\<guillemotleft>Map.empty\<guillemotright>"
  "_UMapUpd m (_UMaplets xy ms)" == "_UMapUpd (_UMapUpd m xy) ms"
  "_UMapUpd m (_umaplet  x y)"   == "CONST trop CONST map_upd m x y"
  "_UMap ms"                      == "_UMapUpd (CONST lit CONST empty) ms"
  "_UMap (_UMaplets ms1 ms2)"     <= "_UMapUpd (_UMap ms1) ms2"
  "_UMaplets ms1 (_UMaplets ms2 ms3)" <= "_UMaplets (_UMaplets ms1 ms2) ms3"
  "f\<lparr>x,y\<rparr>\<^sub>u"  == "CONST bop CONST fun_apply f (x,y)\<^sub>u"

text {* Lifting set intervals *}

syntax
  "_uset_atLeastLessThan" :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" ("(1{_..<_}\<^sub>u)")
  "_uset_compr" :: "id \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('b set, '\<alpha>) uexpr" ("(1{_ :/ _ |/ _ \<bullet>/ _}\<^sub>u)")

lift_definition ZedSetCompr :: 
  "('a set, '\<alpha>) uexpr \<Rightarrow> ('a \<Rightarrow> (bool, '\<alpha>) uexpr \<times> ('b, '\<alpha>) uexpr) \<Rightarrow> ('b set, '\<alpha>) uexpr"
is "\<lambda> A PF b. { snd (PF x) b | x. x \<in> A b \<and> fst (PF x) b}" .

translations
  "{x..<y}\<^sub>u" == "CONST bop CONST atLeastLessThan x y"
  "{x : A | P \<bullet> F}\<^sub>u" == "CONST ZedSetCompr A (\<lambda> x. (P, F))" 

lemmas uexpr_defs =
  iuvar_def
  ouvar_def
  zero_uexpr_def
  one_uexpr_def
  plus_uexpr_def
  uminus_uexpr_def
  minus_uexpr_def
  times_uexpr_def
  div_uexpr_def
  mod_uexpr_def
  eq_upred_def
  numeral_uexpr_simp
  map_upd_def

lemma var_in_var: "var (in_var x) = $x"
  by (simp add: iuvar_def)

lemma var_out_var: "var (out_var x) = $x\<acute>"
  by (simp add: ouvar_def)

(* Map lemmas. TODO: Move to Map extra *)

declare map_member.simps [simp del]

lemma map_minus_apply [simp]: "y \<in> dom(f -- g) \<Longrightarrow> (f -- g)(y)\<^sub>m = f(y)\<^sub>m"
  by (auto simp add: map_minus_def dom_def map_apply_def)

lemma map_add_restrict:
  "f ++ g = (f |` (- dom g)) ++ g"
  by (rule ext, auto simp add: map_add_def restrict_map_def)

lemma map_ext:
  "\<lbrakk> \<And> x y. (x, y) \<in>\<^sub>m A \<longleftrightarrow> (x, y) \<in>\<^sub>m B \<rbrakk> \<Longrightarrow> A = B"
  by (rule ext, auto simp add: map_member.simps, metis not_Some_eq)

lemma map_member_alt_def:
  "(x, y) \<in>\<^sub>m A \<longleftrightarrow> (x \<in> dom A \<and> A(x)\<^sub>m = y)"
  by (auto simp add: map_member.simps map_apply_def)

lemma map_member_plus:
  "(x, y) \<in>\<^sub>m f ++ g \<longleftrightarrow> ((x \<notin> dom(g) \<and> (x, y) \<in>\<^sub>m f) \<or> (x, y) \<in>\<^sub>m g)"
  by (auto simp add: map_member.simps map_add_Some_iff)

lemma map_member_minus:
  "(x, y) \<in>\<^sub>m f -- g \<longleftrightarrow> (x, y) \<in>\<^sub>m f \<and> (\<not> (x, y) \<in>\<^sub>m g)"
  by (auto simp add: map_member.simps map_minus_def)

lemma map_minus_plus_commute:
  "dom(g) \<inter> dom(h) = {} \<Longrightarrow> (f -- g) ++ h = (f ++ h) -- g"
  apply (rule map_ext)
  apply (auto simp add: map_member_plus map_member_minus)
  apply (auto simp add: map_member_alt_def)
done
 
lemma map_le_member:
  "f \<subseteq>\<^sub>m g \<longleftrightarrow> (\<forall> x y. (x,y) \<in>\<^sub>m f \<longrightarrow> (x,y) \<in>\<^sub>m g)"
  by (force simp add: map_le_def map_member.simps)

lemma map_le_graph: "f \<subseteq>\<^sub>m g \<longleftrightarrow> map_graph f \<subseteq> map_graph g"
  by (force simp add: map_le_def map_graph_def)

lemma map_graph_minus: "map_graph (f -- g) = map_graph f - map_graph g"
  by (auto simp add: map_minus_def map_graph_def, (meson option.distinct(1))+)

lemma map_graph_inj:
  "inj map_graph"
  by (metis injI map_graph_inv)

lemma map_eq_graph: "f = g \<longleftrightarrow> map_graph f = map_graph g"
  by (auto simp add: inj_eq map_graph_inj)

lemma map_minus_common_subset:
  "\<lbrakk> h \<subseteq>\<^sub>m f; h \<subseteq>\<^sub>m g \<rbrakk> \<Longrightarrow> (f -- h = g -- h) = (f = g)"
  by (auto simp add: map_eq_graph map_graph_minus map_le_graph)

end