section {* UTP expressions *}

theory utp_expr
imports
  utp_var
  utp_dvar
  Profiling
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

named_theorems ueval

setup_lifting type_definition_uexpr

text {* Get the alphabet of an expression *}

definition alpha_of :: "('a, '\<alpha>) uexpr \<Rightarrow> ('\<alpha>, '\<alpha>) lens" ("\<alpha>'(_')") where
"alpha_of e = 1\<^sub>L"

text {* A variable expression corresponds to the lookup function of the variable. *}

lift_definition var :: "('t, '\<alpha>) uvar \<Rightarrow> ('t, '\<alpha>) uexpr" is lens_get .

declare [[coercion_enabled]]
declare [[coercion var]]

definition dvar_exp :: "'t::continuum dvar \<Rightarrow> ('t, '\<alpha>::vst) uexpr"
where "dvar_exp x = var (dvar_lift x)"

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

text {* We also define a UTP expression version of function abstract *}

lift_definition ulambda :: "('a \<Rightarrow> ('b, '\<alpha>) uexpr) \<Rightarrow> ('a \<Rightarrow> 'b, '\<alpha>) uexpr"
is "\<lambda> f A x. f x A" .

text {* We define syntax for expressions using adhoc overloading -- this allows us to later define
        operators on different types if necessary (e.g. when adding types for new UTP theories). *}

consts
  ulit   :: "'t \<Rightarrow> 'e" ("\<guillemotleft>_\<guillemotright>")
  ueq    :: "'a \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "=\<^sub>u" 50)

adhoc_overloading
  ulit lit

syntax
  "_uuvar" :: "svar \<Rightarrow> logic"

translations
  "_uuvar x" == "CONST var x"

syntax
  "_uuvar" :: "svar \<Rightarrow> logic" ("_")

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

instance uexpr :: (Rings.dvd, type) Rings.dvd ..

instantiation uexpr :: (divide, type) divide
begin
  definition divide_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr" where
  "divide_uexpr u v = bop divide u v"
instance ..
end

instantiation uexpr :: (inverse, type) inverse
begin
  definition inverse_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr"
  where "inverse_uexpr u = uop inverse u"
instance ..
end

instantiation uexpr :: (Divides.div, type) Divides.div
begin
  definition mod_uexpr_def: "u mod v = bop (op mod) u v"
instance ..
end

instantiation uexpr :: (sgn, type) sgn
begin
  definition sgn_uexpr_def: "sgn u = uop sgn u"
instance ..
end

instantiation uexpr :: (abs, type) abs
begin
  definition abs_uexpr_def: "abs u = uop abs u"
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

instance uexpr :: (ab_semigroup_add, type) ab_semigroup_add
  by (intro_classes) (simp add: plus_uexpr_def, transfer, simp add: add.commute)+

instance uexpr :: (cancel_semigroup_add, type) cancel_semigroup_add
  by (intro_classes) (simp add: plus_uexpr_def, transfer, simp add: fun_eq_iff)+

instance uexpr :: (cancel_ab_semigroup_add, type) cancel_ab_semigroup_add
  by (intro_classes) (simp add: plus_uexpr_def minus_uexpr_def, transfer, simp add: fun_eq_iff add.commute diff_diff_add)+

instance uexpr :: (cancel_monoid_add, type) cancel_monoid_add
  by (intro_classes, simp_all add: plus_uexpr_def minus_uexpr_def zero_uexpr_def) (transfer, auto)+

instance uexpr :: (group_add, type) group_add
  by (intro_classes)
     (simp add: plus_uexpr_def uminus_uexpr_def minus_uexpr_def zero_uexpr_def, transfer, simp)+

instance uexpr :: (ab_group_add, type) ab_group_add
  by (intro_classes)
     (simp add: plus_uexpr_def uminus_uexpr_def minus_uexpr_def zero_uexpr_def, transfer, simp)+

instantiation uexpr :: (order, type) order
begin
  lift_definition less_eq_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> bool"
  is "\<lambda> P Q. (\<forall> A. P A \<le> Q A)" .
  definition less_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> bool"
  where "less_uexpr P Q = (P \<le> Q \<and> \<not> Q \<le> P)"
instance proof
  fix x y z :: "('a, 'b) uexpr"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by (simp add: less_uexpr_def)
  show "x \<le> x" by (transfer, auto)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (transfer, blast intro:order.trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (transfer, rule ext, simp add: eq_iff)
qed
end

instance uexpr :: (ordered_ab_group_add, type) ordered_ab_group_add
  by (intro_classes) (simp add: plus_uexpr_def, transfer, simp)

instance uexpr :: (ordered_ab_group_add_abs, type) ordered_ab_group_add_abs
  apply (intro_classes)
  apply (simp add: abs_uexpr_def zero_uexpr_def plus_uexpr_def uminus_uexpr_def, transfer, simp add: abs_ge_self abs_le_iff abs_triangle_ineq)+
  apply (metis ab_group_add_class.ab_diff_conv_add_uminus abs_ge_minus_self abs_ge_self add_mono_thms_linordered_semiring(1))
done

instance uexpr :: (semiring, type) semiring
  by (intro_classes) (simp add: plus_uexpr_def times_uexpr_def, transfer, simp add: fun_eq_iff add.commute semiring_class.distrib_right semiring_class.distrib_left)+

instance uexpr :: (ring_1, type) ring_1
  by (intro_classes) (simp add: plus_uexpr_def uminus_uexpr_def minus_uexpr_def times_uexpr_def zero_uexpr_def one_uexpr_def, transfer, simp add: fun_eq_iff)+

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

definition "fun_apply f x = f x"
declare fun_apply_def [simp]

consts
  uempty  :: "'f"
  uapply  :: "'f \<Rightarrow> 'k \<Rightarrow> 'v"
  uupd    :: "'f \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 'f"
  udom    :: "'f \<Rightarrow> 'a set"
  uran    :: "'f \<Rightarrow> 'b set"
  udomres :: "'a set \<Rightarrow> 'f \<Rightarrow> 'f"
  uranres :: "'f \<Rightarrow> 'b set \<Rightarrow> 'f"
  ucard   :: "'f \<Rightarrow> nat"

definition "LNil = Nil"
definition "LZero = 0"

adhoc_overloading
  uempty LZero and uempty LNil and
  uapply fun_apply and uapply nth and uapply pfun_app and
  uapply ffun_app and uapply cgf_apply and uapply tt_apply and
  uupd pfun_upd and uupd ffun_upd and uupd list_update and
  udom Domain and udom pdom and udom fdom and udom seq_dom and
  udom Range and uran pran and uran fran and uran set and
  udomres pdom_res and udomres fdom_res and
  uranres pran_res and udomres fran_res and
  ucard card and ucard pcard and ucard length

nonterminal utuple_args and umaplet and umaplets

syntax
  "_ucoerce"    :: "('a, '\<alpha>) uexpr \<Rightarrow> type \<Rightarrow> ('a, '\<alpha>) uexpr" (infix ":\<^sub>u" 50)
  "_unil"       :: "('a list, '\<alpha>) uexpr" ("\<langle>\<rangle>")
  "_ulist"      :: "args => ('a list, '\<alpha>) uexpr"    ("\<langle>(_)\<rangle>")
  "_uappend"    :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (infixr "^\<^sub>u" 80)
  "_ulast"      :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("last\<^sub>u'(_')")
  "_ufront"     :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" ("front\<^sub>u'(_')")
  "_uhead"      :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("head\<^sub>u'(_')")
  "_utail"      :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" ("tail\<^sub>u'(_')")
  "_utake"      :: "(nat, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" ("take\<^sub>u'(_,/ _')")
  "_udrop"      :: "(nat, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" ("drop\<^sub>u'(_,/ _')")
  "_ucard"      :: "('a list, '\<alpha>) uexpr \<Rightarrow> (nat, '\<alpha>) uexpr" ("#\<^sub>u'(_')")
  "_ufilter"    :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (infixl "\<restriction>\<^sub>u" 75)
  "_uextract"   :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (infixl "\<upharpoonleft>\<^sub>u" 75)
  "_uelems"     :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" ("elems\<^sub>u'(_')")
  "_usorted"    :: "('a list, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" ("sorted\<^sub>u'(_')")
  "_udistinct"  :: "('a list, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" ("distinct\<^sub>u'(_')")
  "_uless"      :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "<\<^sub>u" 50)
  "_uleq"       :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<le>\<^sub>u" 50)
  "_ugreat"     :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix ">\<^sub>u" 50)
  "_ugeq"       :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<ge>\<^sub>u" 50)
  "_umin"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("min\<^sub>u'(_, _')")
  "_umax"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("max\<^sub>u'(_, _')")
  "_ugcd"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("gcd\<^sub>u'(_, _')")
  "_ufinite"    :: "logic \<Rightarrow> logic" ("finite\<^sub>u'(_')")
  "_uempset"    :: "('a set, '\<alpha>) uexpr" ("{}\<^sub>u")
  "_uset"       :: "args => ('a set, '\<alpha>) uexpr" ("{(_)}\<^sub>u")
  "_uunion"     :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" (infixl "\<union>\<^sub>u" 65)
  "_uinter"     :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" (infixl "\<inter>\<^sub>u" 70)
  "_umem"       :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<in>\<^sub>u" 50)
  "_usubset"    :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<subset>\<^sub>u" 50)
  "_usubseteq"  :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<subseteq>\<^sub>u" 50)
  "_utuple"     :: "('a, '\<alpha>) uexpr \<Rightarrow> utuple_args \<Rightarrow> ('a * 'b, '\<alpha>) uexpr" ("(1'(_,/ _')\<^sub>u)")
  "_utuple_arg"  :: "('a, '\<alpha>) uexpr \<Rightarrow> utuple_args" ("_")
  "_utuple_args" :: "('a, '\<alpha>) uexpr => utuple_args \<Rightarrow> utuple_args"     ("_,/ _")
  "_uunit"      :: "('a, '\<alpha>) uexpr" ("'(')\<^sub>u")
  "_ufst"       :: "('a \<times> 'b, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<pi>\<^sub>1'(_')")
  "_usnd"       :: "('a \<times> 'b, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr" ("\<pi>\<^sub>2'(_')")
  "_uapply"     :: "('a \<Rightarrow> 'b, '\<alpha>) uexpr \<Rightarrow> utuple_args \<Rightarrow> ('b, '\<alpha>) uexpr" ("_\<lparr>_\<rparr>\<^sub>u" [999,0] 999)
  "_ulamba"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<lambda> _ \<bullet> _" [0, 10] 10)
  "_udom"       :: "logic \<Rightarrow> logic" ("dom\<^sub>u'(_')")
  "_uran"       :: "logic \<Rightarrow> logic" ("ran\<^sub>u'(_')")
  "_uinl"       :: "logic \<Rightarrow> logic" ("inl\<^sub>u'(_')")
  "_uinr"       :: "logic \<Rightarrow> logic" ("inr\<^sub>u'(_')")
  "_umap_empty" :: "logic" ("[]\<^sub>u")
  "_umap_plus"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<oplus>\<^sub>u" 85)
  "_umap_minus" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<ominus>\<^sub>u" 85)
  "_udom_res"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<lhd>\<^sub>u" 85)
  "_uran_res"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<rhd>\<^sub>u" 85)
  "_umaplet"    :: "[logic, logic] => umaplet" ("_ /\<mapsto>/ _")
  ""            :: "umaplet => umaplets"             ("_")
  "_UMaplets"   :: "[umaplet, umaplets] => umaplets" ("_,/ _")
  "_UMapUpd"    :: "[logic, umaplets] => logic" ("_/'(_')\<^sub>u" [900,0] 900)
  "_UMap"       :: "umaplets => logic" ("(1[_]\<^sub>u)")

translations
  "f\<lparr>v\<rparr>\<^sub>u" <= "CONST uapply f v"
  "dom\<^sub>u(f)" <= "CONST udom f"
  "ran\<^sub>u(f)" <= "CONST uran f"
  "A \<lhd>\<^sub>u f" <= "CONST udomres A f"
  "f \<rhd>\<^sub>u A" <= "CONST uranres f A"
  "#\<^sub>u(f)" <= "CONST ucard f"
  "f(k \<mapsto> v)\<^sub>u" <= "CONST uupd f k v"

translations
  "x :\<^sub>u 'a" == "x :: ('a, _) uexpr"
  "\<langle>\<rangle>"       == "\<guillemotleft>[]\<guillemotright>"
  "\<langle>x, xs\<rangle>"  == "CONST bop (op #) x \<langle>xs\<rangle>"
  "\<langle>x\<rangle>"      == "CONST bop (op #) x \<guillemotleft>[]\<guillemotright>"
  "x ^\<^sub>u y"   == "CONST bop (op @) x y"
  "last\<^sub>u(xs)" == "CONST uop CONST last xs"
  "front\<^sub>u(xs)" == "CONST uop CONST butlast xs"
  "head\<^sub>u(xs)" == "CONST uop CONST hd xs"
  "tail\<^sub>u(xs)" == "CONST uop CONST tl xs"
  "drop\<^sub>u(n,xs)" == "CONST bop CONST drop n xs"
  "take\<^sub>u(n,xs)" == "CONST bop CONST take n xs"
  "#\<^sub>u(xs)" == "CONST uop CONST ucard xs"
  "elems\<^sub>u(xs)" == "CONST uop CONST set xs"
  "sorted\<^sub>u(xs)" == "CONST uop CONST sorted xs"
  "distinct\<^sub>u(xs)" == "CONST uop CONST distinct xs"
  "xs \<restriction>\<^sub>u A"   == "CONST bop CONST seq_filter xs A"
  "A \<upharpoonleft>\<^sub>u xs"   == "CONST bop (op \<upharpoonleft>\<^sub>l) A xs"
  "x <\<^sub>u y"   == "CONST bop (op <) x y"
  "x \<le>\<^sub>u y"   == "CONST bop (op \<le>) x y"
  "x >\<^sub>u y"   == "y <\<^sub>u x"
  "x \<ge>\<^sub>u y"   == "y \<le>\<^sub>u x"
  "min\<^sub>u(x, y)"  == "CONST bop (CONST min) x y"
  "max\<^sub>u(x, y)"  == "CONST bop (CONST max) x y"
  "gcd\<^sub>u(x, y)"  == "CONST bop (CONST gcd) x y"
  "finite\<^sub>u(x)" == "CONST uop (CONST finite) x"
  "{}\<^sub>u"      == "\<guillemotleft>{}\<guillemotright>"
  "{x, xs}\<^sub>u" == "CONST bop (CONST insert) x {xs}\<^sub>u"
  "{x}\<^sub>u"     == "CONST bop (CONST insert) x \<guillemotleft>{}\<guillemotright>"
  "A \<union>\<^sub>u B"   == "CONST bop (op \<union>) A B"
  "A \<inter>\<^sub>u B"   == "CONST bop (op \<inter>) A B"
  "f \<oplus>\<^sub>u g"   => "(f :: ((_, _) pfun, _) uexpr) + g"
  "f \<ominus>\<^sub>u g"   => "(f :: ((_, _) pfun, _) uexpr) - g"
  "x \<in>\<^sub>u A"   == "CONST bop (op \<in>) x A"
  "A \<subset>\<^sub>u B"   == "CONST bop (op <) A B"
  "A \<subset>\<^sub>u B"   <= "CONST bop (op \<subset>) A B"
  "f \<subset>\<^sub>u g"   <= "CONST bop (op \<subset>\<^sub>p) f g"
  "f \<subset>\<^sub>u g"   <= "CONST bop (op \<subset>\<^sub>f) f g"
  "A \<subseteq>\<^sub>u B"   == "CONST bop (op \<le>) A B"
  "A \<subseteq>\<^sub>u B"   <= "CONST bop (op \<subseteq>) A B"
  "f \<subseteq>\<^sub>u g"   <= "CONST bop (op \<subseteq>\<^sub>p) f g"
  "f \<subseteq>\<^sub>u g"   <= "CONST bop (op \<subseteq>\<^sub>f) f g"
  "()\<^sub>u"      == "\<guillemotleft>()\<guillemotright>"
  "(x, y)\<^sub>u"  == "CONST bop (CONST Pair) x y"
  "_utuple x (_utuple_args y z)" == "_utuple x (_utuple_arg (_utuple y z))"
  "\<pi>\<^sub>1(x)"    == "CONST uop CONST fst x"
  "\<pi>\<^sub>2(x)"    == "CONST uop CONST snd x"
  "f\<lparr>x\<rparr>\<^sub>u"    == "CONST bop CONST uapply f x"
  "\<lambda> x \<bullet> p" == "CONST ulambda (\<lambda> x. p)"
  "dom\<^sub>u(f)" == "CONST uop CONST udom f"
  "ran\<^sub>u(f)" == "CONST uop CONST uran f"
  "inl\<^sub>u(x)" == "CONST uop CONST Inl x"
  "inr\<^sub>u(x)" == "CONST uop CONST Inr x"
  "[]\<^sub>u"     == "\<guillemotleft>CONST uempty\<guillemotright>"
  "A \<lhd>\<^sub>u f" == "CONST bop (CONST udomres) A f"
  "f \<rhd>\<^sub>u A" == "CONST bop (CONST uranres) f A"
  "_UMapUpd m (_UMaplets xy ms)" == "_UMapUpd (_UMapUpd m xy) ms"
  "_UMapUpd m (_umaplet  x y)"   == "CONST trop CONST uupd m x y"
  "_UMap ms"                      == "_UMapUpd []\<^sub>u ms"
  "_UMap (_UMaplets ms1 ms2)"     <= "_UMapUpd (_UMap ms1) ms2"
  "_UMaplets ms1 (_UMaplets ms2 ms3)" <= "_UMaplets (_UMaplets ms1 ms2) ms3"
  "f\<lparr>x,y\<rparr>\<^sub>u"  == "CONST bop CONST uapply f (x,y)\<^sub>u"

text {* Lifting set intervals *}

syntax
  "_uset_atLeastAtMost" :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" ("(1{_.._}\<^sub>u)")
  "_uset_atLeastLessThan" :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" ("(1{_..<_}\<^sub>u)")
  "_uset_compr" :: "id \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('b set, '\<alpha>) uexpr" ("(1{_ :/ _ |/ _ \<bullet>/ _}\<^sub>u)")

lift_definition ZedSetCompr ::
  "('a set, '\<alpha>) uexpr \<Rightarrow> ('a \<Rightarrow> (bool, '\<alpha>) uexpr \<times> ('b, '\<alpha>) uexpr) \<Rightarrow> ('b set, '\<alpha>) uexpr"
is "\<lambda> A PF b. { snd (PF x) b | x. x \<in> A b \<and> fst (PF x) b}" .

translations
  "{x..y}\<^sub>u" == "CONST bop CONST atLeastAtMost x y"
  "{x..<y}\<^sub>u" == "CONST bop CONST atLeastLessThan x y"
  "{x : A | P \<bullet> F}\<^sub>u" == "CONST ZedSetCompr A (\<lambda> x. (P, F))"

text {* Lifting limits *}

definition "ulim_left = (\<lambda> p f. Lim (at_left p) f)"
definition "ulim_right = (\<lambda> p f. Lim (at_right p) f)"
definition "ucont_on = (\<lambda> f A. continuous_on A f)"

syntax
  "_ulim_left"  :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("lim\<^sub>u'(_ \<rightarrow> _\<^sup>-')'(_')")
  "_ulim_right" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("lim\<^sub>u'(_ \<rightarrow> _\<^sup>+')'(_')")
  "_ucont_on"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "cont-on\<^sub>u" 90)

translations
  "lim\<^sub>u(x \<rightarrow> p\<^sup>-)(e)" == "CONST bop CONST ulim_left p (\<lambda> x \<bullet> e)"
  "lim\<^sub>u(x \<rightarrow> p\<^sup>+)(e)" == "CONST bop CONST ulim_right p (\<lambda> x \<bullet> e)"
  "f cont-on\<^sub>u A"     == "CONST bop CONST continuous_on A f"

lemmas uexpr_defs =
  alpha_of_def
  zero_uexpr_def
  one_uexpr_def
  plus_uexpr_def
  uminus_uexpr_def
  minus_uexpr_def
  times_uexpr_def
  inverse_uexpr_def
  divide_uexpr_def
  sgn_uexpr_def
  abs_uexpr_def
  mod_uexpr_def
  eq_upred_def
  numeral_uexpr_simp
  ulim_left_def
  ulim_right_def
  ucont_on_def
  LNil_def
  LZero_def
  plus_list_def

subsection {* Evaluation laws for expressions *}

lemma lit_ueval [ueval]: "\<lbrakk>\<guillemotleft>x\<guillemotright>\<rbrakk>\<^sub>eb = x"
  by (transfer, simp)

lemma var_ueval [ueval]: "\<lbrakk>var x\<rbrakk>\<^sub>eb = get\<^bsub>x\<^esub> b"
  by (transfer, simp)

lemma uop_ueval [ueval]: "\<lbrakk>uop f x\<rbrakk>\<^sub>eb = f (\<lbrakk>x\<rbrakk>\<^sub>eb)"
  by (transfer, simp)

lemma bop_ueval [ueval]: "\<lbrakk>bop f x y\<rbrakk>\<^sub>eb = f (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb)"
  by (transfer, simp)

lemma trop_ueval [ueval]: "\<lbrakk>trop f x y z\<rbrakk>\<^sub>eb = f (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb) (\<lbrakk>z\<rbrakk>\<^sub>eb)"
  by (transfer, simp)

declare uexpr_defs [ueval]

subsection {* Misc laws *}

lemma tail_cons [simp]: "tail\<^sub>u(\<langle>x\<rangle> ^\<^sub>u xs) = xs"
  by (transfer, simp)

lemma lit_num_simps: "\<guillemotleft>0\<guillemotright> = 0" "\<guillemotleft>1\<guillemotright> = 1" "\<guillemotleft>numeral n\<guillemotright> = numeral n" "\<guillemotleft>- x\<guillemotright> = - \<guillemotleft>x\<guillemotright>"
  by (simp_all add: ueval, transfer, simp)

end
