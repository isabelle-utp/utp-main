section \<open> UTP expressions \<close>

theory utp_expr
imports
  utp_var
begin

subsection \<open> Expression type \<close>
  
purge_notation BNF_Def.convol ("\<langle>(_,/ _)\<rangle>")

text \<open> Before building the predicate model, we will build a model of expressions that generalise
  alphabetised predicates. Expressions are represented semantically as mapping from
  the alphabet @{typ "'\<alpha>"} to the expression's type @{typ "'a"}. This general model will allow us to unify
  all constructions under one type. The majority definitions in the file are given using
  the \emph{lifting} package~\cite{Huffman13}, which allows us to reuse much of the existing
  library of HOL functions. \<close>

typedef ('t, '\<alpha>) uexpr = "UNIV :: ('\<alpha> \<Rightarrow> 't) set" ..

setup_lifting type_definition_uexpr
    
notation Rep_uexpr ("\<lbrakk>_\<rbrakk>\<^sub>e")

lemma uexpr_eq_iff:
  "e = f \<longleftrightarrow> (\<forall> b. \<lbrakk>e\<rbrakk>\<^sub>e b = \<lbrakk>f\<rbrakk>\<^sub>e b)"
  using Rep_uexpr_inject[of e f, THEN sym] by (auto)

text \<open> The term @{term "\<lbrakk>e\<rbrakk>\<^sub>e b"} effectively refers to the semantic interpretation of the expression
  under the state-space valuation (or variables binding) @{term b}. It can be used, in concert
  with the lifting package, to interpret UTP constructs to their HOL equivalents. We create some
  theorem sets to store such transfer theorems. \<close>
    
named_theorems ueval and lit_simps and lit_norm

subsection \<open> Core expression constructs \<close>
  
text \<open> A variable expression corresponds to the lens $get$ function associated with a variable. 
  Specifically, given a lens the expression always returns that portion of the state-space
  referred to by the lens. \<close>

lift_definition var :: "('t \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t, '\<alpha>) uexpr" is lens_get .

text \<open> A literal is simply a constant function expression, always returning the same value
  for any binding. \<close>

lift_definition lit :: "'t \<Rightarrow> ('t, '\<alpha>) uexpr" is "\<lambda> v b. v" .

text \<open> We define lifting for unary, binary, ternary, and quaternary expression constructs, that 
  simply take a HOL function with correct number of arguments and apply it function to all possible 
  results of the expressions. \<close>

lift_definition uop :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr"
  is "\<lambda> f e b. f (e b)" .
lift_definition bop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr"
  is "\<lambda> f u v b. f (u b) (v b)" .
lift_definition trop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr \<Rightarrow> ('d, '\<alpha>) uexpr"
  is "\<lambda> f u v w b. f (u b) (v b) (w b)" .
lift_definition qtop ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow>
   ('a, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('c, '\<alpha>) uexpr \<Rightarrow> ('d, '\<alpha>) uexpr \<Rightarrow>
   ('e, '\<alpha>) uexpr"
  is "\<lambda> f u v w x b. f (u b) (v b) (w b) (x b)" .

text \<open> We also define a UTP expression version of function ($\lambda$) abstraction, that takes
  a function producing an expression and produces an expression producing a function. \<close>

lift_definition ulambda :: "('a \<Rightarrow> ('b, '\<alpha>) uexpr) \<Rightarrow> ('a \<Rightarrow> 'b, '\<alpha>) uexpr"
is "\<lambda> f A x. f x A" .

text \<open> We set up syntax for the conditional. This is effectively an infix version of
  if-then-else where the condition is in the middle. \<close>
  
abbreviation cond ::
  "('a,'\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr \<Rightarrow> ('a,'\<alpha>) uexpr \<Rightarrow> ('a,'\<alpha>) uexpr"
  ("(3_ \<triangleleft> _ \<triangleright>/ _)" [52,0,53] 52)
where "P \<triangleleft> b \<triangleright> Q \<equiv> trop If b P Q"

text \<open> UTP expression is equality is simply HOL equality lifted using the @{term bop} binary 
  expression constructor. \<close>
    
definition eq_upred :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr"
where "eq_upred x y = bop HOL.eq x y"
    
text \<open> We define syntax for expressions using adhoc-overloading -- this allows us to later define
        operators on different types if necessary (e.g. when adding types for new UTP theories). \<close>

consts
  ulit   :: "'t \<Rightarrow> 'e" ("\<guillemotleft>_\<guillemotright>")
  ueq    :: "'a \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "=\<^sub>u" 50)
  
adhoc_overloading
  ulit lit and
  ueq eq_upred

text \<open> A literal is the expression @{term "\<guillemotleft>v\<guillemotright>"}, where @{term v} is any HOL term. Actually, the
  literal construct is very versatile and also allows us to refer to HOL variables within UTP
  expressions, and has a variety of other uses. It can therefore also be considered as a kind
  of quotation mechanism. 

  We also set up syntax for UTP variable expressions. \<close>
  
syntax
  "_uuvar" :: "svar \<Rightarrow> logic" ("_")

translations
  "_uuvar x" == "CONST var x"
  
text \<open> Since we already have a parser for variables, we can directly reuse it and simply apply
  the @{term var} expression construct to lift the resulting variable to an expression. \<close>
  
subsection \<open> Type class instantiations \<close>
  
text \<open> Isabelle/HOL of course provides a large hierarchy of type classes that provide constructs
  such as numerals and the arithmetic operators. Fortunately we can directly make use of these
  for UTP expressions, and thus we now perform a long list of appropriate instantiations. We
  first lift the core arithemtic constants and operators using a mixture of literals, unary, and binary
  expression constructors. \<close>
  
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

instantiation uexpr :: (plus, type) plus
begin
  definition plus_uexpr_def: "u + v = bop (op +) u v"
instance ..
end

text \<open> It should be noted that instantiating the unary minus class, @{class uminus}, will also 
  provide negation UTP predicates later. \<close>

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

instantiation uexpr :: (modulo, type) modulo
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

text \<open> Once we've set up all the core constructs for arithmetic, we can also instantiate the 
  type classes for various algebras, including groups and rings. The proofs are done by 
  definitional expansion, the \emph{transfer} tactic, and then finally the theorems of the underlying
  HOL operators. This is mainly routine, so we don't comment further. \<close>
  
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
  by (intro_classes, (simp add: plus_uexpr_def minus_uexpr_def, transfer, simp add: fun_eq_iff add.commute cancel_ab_semigroup_add_class.diff_diff_add)+)

instance uexpr :: (group_add, type) group_add
  by (intro_classes)
     (simp add: plus_uexpr_def uminus_uexpr_def minus_uexpr_def zero_uexpr_def, transfer, simp)+

instance uexpr :: (ab_group_add, type) ab_group_add
  by (intro_classes)
     (simp add: plus_uexpr_def uminus_uexpr_def minus_uexpr_def zero_uexpr_def, transfer, simp)+

instance uexpr :: (semiring, type) semiring
  by (intro_classes) (simp add: plus_uexpr_def times_uexpr_def, transfer, simp add: fun_eq_iff add.commute semiring_class.distrib_right semiring_class.distrib_left)+

instance uexpr :: (ring_1, type) ring_1
  by (intro_classes) (simp add: plus_uexpr_def uminus_uexpr_def minus_uexpr_def times_uexpr_def zero_uexpr_def one_uexpr_def, transfer, simp add: fun_eq_iff)+
     
text \<open> We can also define the order relation on expressions. Now, unlike the previous group and ring 
  constructs, the order relations @{term "op \<le>"} and @{term "op \<le>"} return a @{type bool} type.
  This order is not therefore the lifted order which allows us to compare the valuation of two
  expressions, but rather the order on expressions themselves. Notably, this instantiation will
  later allow us to talk about predicate refinements and complete lattices. \<close>
     
instantiation uexpr :: (ord, type) ord
begin
  lift_definition less_eq_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> bool"
  is "\<lambda> P Q. (\<forall> A. P A \<le> Q A)" .
  definition less_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> bool"
  where "less_uexpr P Q = (P \<le> Q \<and> \<not> Q \<le> P)"
instance ..
end

text \<open> UTP expressions whose return type is a partial ordered type, are also partially ordered
  as the following instantiation demonstrates. \<close>
  
instance uexpr :: (order, type) order
proof
  fix x y z :: "('a, 'b) uexpr"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by (simp add: less_uexpr_def)
  show "x \<le> x" by (transfer, auto)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (transfer, blast intro:order.trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (transfer, rule ext, simp add: eq_iff)
qed

text \<open> We also lift the properties from certain ordered groups. \<close>
  
instance uexpr :: (ordered_ab_group_add, type) ordered_ab_group_add
  by (intro_classes) (simp add: plus_uexpr_def, transfer, simp)

instance uexpr :: (ordered_ab_group_add_abs, type) ordered_ab_group_add_abs
  apply (intro_classes)
      apply (simp add: abs_uexpr_def zero_uexpr_def plus_uexpr_def uminus_uexpr_def, transfer, simp add: abs_ge_self abs_le_iff abs_triangle_ineq)+
  apply (metis ab_group_add_class.ab_diff_conv_add_uminus abs_ge_minus_self abs_ge_self add_mono_thms_linordered_semiring(1))
  done

text \<open> The following instantiation sets up numerals. This will allow us to have Isabelle number
  representations (i.e. 3,7,42,198 etc.) to UTP expressions directly. \<close>

instance uexpr :: (numeral, type) numeral
  by (intro_classes, simp add: plus_uexpr_def, transfer, simp add: add.assoc)
  
text \<open> The following two theorems also set up interpretation of numerals, meaning a UTP numeral
  can always be converted to a HOL numeral. \<close>
    
lemma numeral_uexpr_rep_eq: "\<lbrakk>numeral x\<rbrakk>\<^sub>e b = numeral x"
  apply (induct x)
    apply (simp add: lit.rep_eq one_uexpr_def)
   apply (simp add: bop.rep_eq numeral_Bit0 plus_uexpr_def)
  apply (simp add: bop.rep_eq lit.rep_eq numeral_code(3) one_uexpr_def plus_uexpr_def)
  done

lemma numeral_uexpr_simp: "numeral x = \<guillemotleft>numeral x\<guillemotright>"
  by (simp add: uexpr_eq_iff numeral_uexpr_rep_eq lit.rep_eq)

text \<open> The next theorem lifts powers. \<close>

lemma power_rep_eq: "\<lbrakk>P ^ n\<rbrakk>\<^sub>e = (\<lambda> b. \<lbrakk>P\<rbrakk>\<^sub>e b ^ n)"
  by (induct n, simp_all add: lit.rep_eq one_uexpr_def bop.rep_eq times_uexpr_def)

(*
text \<open> We can also lift a few arithmetic properties from the class instantiations above using
  \emph{transfer}. \<close>

lemma uexpr_diff_zero [simp]:
  fixes a :: "('\<alpha>::trace, 'a) uexpr"
  shows "a - 0 = a"
  by (simp add: minus_uexpr_def zero_uexpr_def, transfer, auto)

lemma uexpr_add_diff_cancel_left [simp]:
  fixes a b :: "('\<alpha>::trace, 'a) uexpr"
  shows "(a + b) - a = b"
  by (simp add: minus_uexpr_def plus_uexpr_def, transfer, auto)
*)

subsection \<open> Overloaded expression constructors \<close>
    
text \<open> For convenience, we often want to utilise the same expression syntax for multiple constructs.
  This can be achieved using ad-hoc overloading. We create a number of polymorphic constants and then
  overload their definitions using appropriate implementations. In order for this to work,
  each collection must have its own unique type. Thus we do not use the HOL map type directly,
  but rather our own partial function type, for example. \<close>
  
consts
  -- \<open> Empty elements, for example empty set, nil list, 0... \<close> 
  uempty     :: "'f"
  -- \<open> Function application, map application, list application... \<close>
  uapply     :: "'f \<Rightarrow> 'k \<Rightarrow> 'v"
  -- \<open> Function update, map update, list update... \<close>
  uupd       :: "'f \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 'f"
  -- \<open> Domain of maps, lists... \<close>
  udom       :: "'f \<Rightarrow> 'a set"
  -- \<open> Range of maps, lists... \<close>
  uran       :: "'f \<Rightarrow> 'b set"
  -- \<open> Domain restriction \<close>
  udomres    :: "'a set \<Rightarrow> 'f \<Rightarrow> 'f"
  -- \<open> Range restriction \<close>
  uranres    :: "'f \<Rightarrow> 'b set \<Rightarrow> 'f"
  -- \<open> Collection cardinality \<close>
  ucard      :: "'f \<Rightarrow> nat"
  -- \<open> Collection summation \<close>
  usums      :: "'f \<Rightarrow> 'a"
  -- \<open> Construct a collection from a list of entries \<close>
  uentries   :: "'k set \<Rightarrow> ('k \<Rightarrow> 'v) \<Rightarrow> 'f"
  
text \<open> We need a function corresponding to function application in order to overload. \<close>
  
definition fun_apply :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
where "fun_apply f x = f x"

declare fun_apply_def [simp]

definition ffun_entries :: "'k set \<Rightarrow> ('k \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) ffun" where
"ffun_entries d f = graph_ffun {(k, f k) | k. k \<in> d}"

text \<open> We then set up the overloading for a number of useful constructs for various collections. \<close>
  
adhoc_overloading
  uempty 0 and
  uapply fun_apply and uapply nth and uapply pfun_app and
  uapply ffun_app and
  uupd pfun_upd and uupd ffun_upd and uupd list_augment and
  udom Domain and udom pdom and udom fdom and udom seq_dom and
  udom Range and uran pran and uran fran and uran set and
  udomres pdom_res and udomres fdom_res and
  uranres pran_res and udomres fran_res and
  ucard card and ucard pcard and ucard length and
  usums list_sum and usums Sum and usums pfun_sum and
  uentries pfun_entries and uentries ffun_entries
  
subsection \<open> Syntax translations \<close>

text \<open> The follows a large number of translations that lift HOL functions to UTP expressions
  using the various expression constructors defined above. Much of the time we try to keep
  the HOL syntax but add a "u" subscript. \<close>
  
abbreviation (input) "ulens_override x f g \<equiv> lens_override f g x"
  
translations
  "0" <= "CONST uempty" -- {* We have to do this so we don't see uempty. Is there a better way of printing? *}
    
text \<open> We add new non-terminals for UTP tuples and maplets. \<close>
  
nonterminal utuple_args and umaplet and umaplets

syntax -- \<open> Core expression constructs \<close>
  "_ucoerce"    :: "logic \<Rightarrow> type \<Rightarrow> logic" (infix ":\<^sub>u" 50)
  "_ulambda"    :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<lambda> _ \<bullet> _" [0, 10] 10)
  "_ulens_ovrd" :: "logic \<Rightarrow> logic \<Rightarrow> salpha \<Rightarrow> logic" ("_ \<oplus> _ on _" [85, 0, 86] 86)
  "_ulens_get"  :: "logic \<Rightarrow> svar \<Rightarrow> logic" ("_:_" [900,901] 901)

translations
  "\<lambda> x \<bullet> p" == "CONST ulambda (\<lambda> x. p)"
  "x :\<^sub>u 'a" == "x :: ('a, _) uexpr"
  "_ulens_ovrd f g a" => "CONST bop (CONST ulens_override a) f g"
  "_ulens_ovrd f g a" <= "CONST bop (\<lambda>x y. CONST lens_override x1 y1 a) f g"
  "_ulens_get x y" == "CONST uop (CONST lens_get y) x"

syntax -- \<open> Tuples \<close>
  "_utuple"     :: "('a, '\<alpha>) uexpr \<Rightarrow> utuple_args \<Rightarrow> ('a * 'b, '\<alpha>) uexpr" ("(1'(_,/ _')\<^sub>u)")
  "_utuple_arg"  :: "('a, '\<alpha>) uexpr \<Rightarrow> utuple_args" ("_")
  "_utuple_args" :: "('a, '\<alpha>) uexpr => utuple_args \<Rightarrow> utuple_args"     ("_,/ _")
  "_uunit"      :: "('a, '\<alpha>) uexpr" ("'(')\<^sub>u")
  "_ufst"       :: "('a \<times> 'b, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<pi>\<^sub>1'(_')")
  "_usnd"       :: "('a \<times> 'b, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr" ("\<pi>\<^sub>2'(_')")

translations
  "()\<^sub>u"      == "\<guillemotleft>()\<guillemotright>"
  "(x, y)\<^sub>u"  == "CONST bop (CONST Pair) x y"
  "_utuple x (_utuple_args y z)" == "_utuple x (_utuple_arg (_utuple y z))"
  "\<pi>\<^sub>1(x)"    == "CONST uop CONST fst x"
  "\<pi>\<^sub>2(x)"    == "CONST uop CONST snd x"
    
syntax -- \<open> Polymorphic constructs \<close>
  "_uundef"     :: "logic" ("\<bottom>\<^sub>u")
  "_umap_empty" :: "logic" ("[]\<^sub>u")
  "_uapply"     :: "('a \<Rightarrow> 'b, '\<alpha>) uexpr \<Rightarrow> utuple_args \<Rightarrow> ('b, '\<alpha>) uexpr" ("_'(_')\<^sub>a" [999,0] 999)
  "_umaplet"    :: "[logic, logic] => umaplet" ("_ /\<mapsto>/ _")
  ""            :: "umaplet => umaplets"             ("_")
  "_UMaplets"   :: "[umaplet, umaplets] => umaplets" ("_,/ _")
  "_UMapUpd"    :: "[logic, umaplets] => logic" ("_/'(_')\<^sub>u" [900,0] 900)
  "_UMap"       :: "umaplets => logic" ("(1[_]\<^sub>u)")
  "_ucard"      :: "logic \<Rightarrow> logic" ("#\<^sub>u'(_')")
  "_uless"      :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "<\<^sub>u" 50)
  "_uleq"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<le>\<^sub>u" 50)
  "_ugreat"     :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix ">\<^sub>u" 50)
  "_ugeq"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<ge>\<^sub>u" 50)
  "_uceil"      :: "logic \<Rightarrow> logic" ("\<lceil>_\<rceil>\<^sub>u")
  "_ufloor"     :: "logic \<Rightarrow> logic" ("\<lfloor>_\<rfloor>\<^sub>u")
  "_udom"       :: "logic \<Rightarrow> logic" ("dom\<^sub>u'(_')")
  "_uran"       :: "logic \<Rightarrow> logic" ("ran\<^sub>u'(_')")
  "_usum"       :: "logic \<Rightarrow> logic" ("sum\<^sub>u'(_')")
  "_udom_res"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<lhd>\<^sub>u" 85)
  "_uran_res"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<rhd>\<^sub>u" 85)
  "_umin"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("min\<^sub>u'(_, _')")
  "_umax"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("max\<^sub>u'(_, _')")
  "_ugcd"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("gcd\<^sub>u'(_, _')")
  "_uentries"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("entr\<^sub>u'(_,_')")
  
translations
  -- \<open> Pretty printing for adhoc-overloaded constructs \<close>
  "f(x)\<^sub>a"    <= "CONST uapply f x"
  "dom\<^sub>u(f)" <= "CONST udom f"
  "ran\<^sub>u(f)" <= "CONST uran f"  
  "A \<lhd>\<^sub>u f" <= "CONST udomres A f"
  "f \<rhd>\<^sub>u A" <= "CONST uranres f A"
  "#\<^sub>u(f)" <= "CONST ucard f"
  "f(k \<mapsto> v)\<^sub>u" <= "CONST uupd f k v"

  -- \<open> Overloaded construct translations \<close>
  "f(x,y,z,u)\<^sub>a" == "CONST bop CONST uapply f (x,y,z,u)\<^sub>u"
  "f(x,y,z)\<^sub>a" == "CONST bop CONST uapply f (x,y,z)\<^sub>u"
  "f(x,y)\<^sub>a"  == "CONST bop CONST uapply f (x,y)\<^sub>u"  
  "f(x)\<^sub>a"    == "CONST bop CONST uapply f x"
  "#\<^sub>u(xs)"  == "CONST uop CONST ucard xs"
  "sum\<^sub>u(A)" == "CONST uop CONST usums A"
  "dom\<^sub>u(f)" == "CONST uop CONST udom f"
  "ran\<^sub>u(f)" == "CONST uop CONST uran f"
  "[]\<^sub>u"     == "\<guillemotleft>CONST uempty\<guillemotright>"
  "\<bottom>\<^sub>u"     == "\<guillemotleft>CONST undefined\<guillemotright>"
  "A \<lhd>\<^sub>u f" == "CONST bop (CONST udomres) A f"
  "f \<rhd>\<^sub>u A" == "CONST bop (CONST uranres) f A"
  "entr\<^sub>u(d,f)" == "CONST bop CONST uentries d \<guillemotleft>f\<guillemotright>"
  "_UMapUpd m (_UMaplets xy ms)" == "_UMapUpd (_UMapUpd m xy) ms"
  "_UMapUpd m (_umaplet  x y)"   == "CONST trop CONST uupd m x y"
  "_UMap ms"                      == "_UMapUpd []\<^sub>u ms"
  "_UMap (_UMaplets ms1 ms2)"     <= "_UMapUpd (_UMap ms1) ms2"
  "_UMaplets ms1 (_UMaplets ms2 ms3)" <= "_UMaplets (_UMaplets ms1 ms2) ms3"
  
  -- \<open> Type-class polymorphic constructs \<close>
  "x <\<^sub>u y"   == "CONST bop (op <) x y"
  "x \<le>\<^sub>u y"   == "CONST bop (op \<le>) x y"
  "x >\<^sub>u y"   => "y <\<^sub>u x"
  "x \<ge>\<^sub>u y"   => "y \<le>\<^sub>u x"
  "min\<^sub>u(x, y)"  == "CONST bop (CONST min) x y"
  "max\<^sub>u(x, y)"  == "CONST bop (CONST max) x y"
  "gcd\<^sub>u(x, y)"  == "CONST bop (CONST gcd) x y"
  "\<lceil>x\<rceil>\<^sub>u" == "CONST uop CONST ceiling x"
  "\<lfloor>x\<rfloor>\<^sub>u" == "CONST uop CONST floor x"

syntax -- \<open> Lists / Sequences \<close>
  "_unil"       :: "('a list, '\<alpha>) uexpr" ("\<langle>\<rangle>")
  "_ulist"      :: "args => ('a list, '\<alpha>) uexpr"    ("\<langle>(_)\<rangle>")
  "_uappend"    :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (infixr "^\<^sub>u" 80)
  "_ulast"      :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("last\<^sub>u'(_')")
  "_ufront"     :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" ("front\<^sub>u'(_')")
  "_uhead"      :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("head\<^sub>u'(_')")
  "_utail"      :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" ("tail\<^sub>u'(_')")
  "_utake"      :: "(nat, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" ("take\<^sub>u'(_,/ _')")
  "_udrop"      :: "(nat, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" ("drop\<^sub>u'(_,/ _')")
  "_ufilter"    :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (infixl "\<restriction>\<^sub>u" 75)
  "_uextract"   :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (infixl "\<upharpoonleft>\<^sub>u" 75)
  "_uelems"     :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" ("elems\<^sub>u'(_')")
  "_usorted"    :: "('a list, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" ("sorted\<^sub>u'(_')")
  "_udistinct"  :: "('a list, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" ("distinct\<^sub>u'(_')")
  "_uupto"      :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("\<langle>_.._\<rangle>")
  "_uupt"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("\<langle>_..<_\<rangle>")
  "_umap"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("map\<^sub>u")
  "_uzip"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("zip\<^sub>u")
  
translations
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
  "elems\<^sub>u(xs)" == "CONST uop CONST set xs"
  "sorted\<^sub>u(xs)" == "CONST uop CONST sorted xs"
  "distinct\<^sub>u(xs)" == "CONST uop CONST distinct xs"
  "xs \<restriction>\<^sub>u A"   == "CONST bop CONST seq_filter xs A"
  "A \<upharpoonleft>\<^sub>u xs"   == "CONST bop (op \<upharpoonleft>\<^sub>l) A xs"
  "\<langle>n..k\<rangle>" == "CONST bop CONST upto n k"
  "\<langle>n..<k\<rangle>" == "CONST bop CONST upt n k"
  "map\<^sub>u f xs" == "CONST bop CONST map f xs"
  "zip\<^sub>u xs ys" == "CONST bop CONST zip xs ys"
  
syntax -- \<open> Sets \<close>
  "_ufinite"    :: "logic \<Rightarrow> logic" ("finite\<^sub>u'(_')")
  "_uempset"    :: "('a set, '\<alpha>) uexpr" ("{}\<^sub>u")
  "_uset"       :: "args => ('a set, '\<alpha>) uexpr" ("{(_)}\<^sub>u")
  "_uunion"     :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" (infixl "\<union>\<^sub>u" 65)
  "_uinter"     :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" (infixl "\<inter>\<^sub>u" 70)
  "_umem"       :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<in>\<^sub>u" 50)
  "_usubset"    :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<subset>\<^sub>u" 50)
  "_usubseteq"  :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<subseteq>\<^sub>u" 50)

translations
  "finite\<^sub>u(x)" == "CONST uop (CONST finite) x"
  "{}\<^sub>u"      == "\<guillemotleft>{}\<guillemotright>"
  "{x, xs}\<^sub>u" == "CONST bop (CONST insert) x {xs}\<^sub>u"
  "{x}\<^sub>u"     == "CONST bop (CONST insert) x \<guillemotleft>{}\<guillemotright>"
  "A \<union>\<^sub>u B"   == "CONST bop (op \<union>) A B"
  "A \<inter>\<^sub>u B"   == "CONST bop (op \<inter>) A B"
  "x \<in>\<^sub>u A"   == "CONST bop (op \<in>) x A"
  "A \<subset>\<^sub>u B"   == "CONST bop (op \<subset>) A B"
  "f \<subset>\<^sub>u g"   <= "CONST bop (op \<subset>\<^sub>p) f g"
  "f \<subset>\<^sub>u g"   <= "CONST bop (op \<subset>\<^sub>f) f g"
  "A \<subseteq>\<^sub>u B"   == "CONST bop (op \<subseteq>) A B"
  "f \<subseteq>\<^sub>u g"   <= "CONST bop (op \<subseteq>\<^sub>p) f g"
  "f \<subseteq>\<^sub>u g"   <= "CONST bop (op \<subseteq>\<^sub>f) f g"
  
syntax -- \<open> Partial functions \<close>
  "_umap_plus"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<oplus>\<^sub>u" 85)
  "_umap_minus" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<ominus>\<^sub>u" 85)

translations
  "f \<oplus>\<^sub>u g"   => "(f :: ((_, _) pfun, _) uexpr) + g"
  "f \<ominus>\<^sub>u g"   => "(f :: ((_, _) pfun, _) uexpr) - g"
  
syntax -- \<open> Sum types \<close>
  "_uinl"       :: "logic \<Rightarrow> logic" ("inl\<^sub>u'(_')")
  "_uinr"       :: "logic \<Rightarrow> logic" ("inr\<^sub>u'(_')")
  
translations
  "inl\<^sub>u(x)" == "CONST uop CONST Inl x"
  "inr\<^sub>u(x)" == "CONST uop CONST Inr x"

subsection \<open> Lifting set collectors \<close>

text \<open> We provide syntax for various types of set collectors, including intervals and the Z-style
  set comprehension which is purpose built as a new lifted definition. \<close>
  
syntax
  "_uset_atLeastAtMost" :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" ("(1{_.._}\<^sub>u)")
  "_uset_atLeastLessThan" :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" ("(1{_..<_}\<^sub>u)")
  "_uset_compr" :: "pttrn \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('b set, '\<alpha>) uexpr" ("(1{_ :/ _ |/ _ \<bullet>/ _}\<^sub>u)")
  "_uset_compr_nset" :: "pttrn \<Rightarrow> (bool, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('b set, '\<alpha>) uexpr" ("(1{_ |/ _ \<bullet>/ _}\<^sub>u)")

lift_definition ZedSetCompr ::
  "('a set, '\<alpha>) uexpr \<Rightarrow> ('a \<Rightarrow> (bool, '\<alpha>) uexpr \<times> ('b, '\<alpha>) uexpr) \<Rightarrow> ('b set, '\<alpha>) uexpr"
is "\<lambda> A PF b. { snd (PF x) b | x. x \<in> A b \<and> fst (PF x) b}" .

translations
  "{x..y}\<^sub>u" == "CONST bop CONST atLeastAtMost x y"
  "{x..<y}\<^sub>u" == "CONST bop CONST atLeastLessThan x y"
  "{x | P \<bullet> F}\<^sub>u" == "CONST ZedSetCompr (CONST ulit CONST UNIV) (\<lambda> x. (P, F))"
  "{x : A | P \<bullet> F}\<^sub>u" == "CONST ZedSetCompr A (\<lambda> x. (P, F))"

subsection \<open> Lifting limits \<close>
  
text \<open> We also lift the following functions on topological spaces for taking function limits,
  and describing continuity. \<close>

definition ulim_left :: "'a::order_topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b::t2_space" where
"ulim_left = (\<lambda> p f. Lim (at_left p) f)"

definition ulim_right :: "'a::order_topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b::t2_space" where
"ulim_right = (\<lambda> p f. Lim (at_right p) f)"

definition ucont_on :: "('a::topological_space \<Rightarrow> 'b::topological_space) \<Rightarrow> 'a set \<Rightarrow> bool" where
"ucont_on = (\<lambda> f A. continuous_on A f)"

syntax
  "_ulim_left"  :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("lim\<^sub>u'(_ \<rightarrow> _\<^sup>-')'(_')")
  "_ulim_right" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("lim\<^sub>u'(_ \<rightarrow> _\<^sup>+')'(_')")
  "_ucont_on"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "cont-on\<^sub>u" 90)

translations
  "lim\<^sub>u(x \<rightarrow> p\<^sup>-)(e)" == "CONST bop CONST ulim_left p (\<lambda> x \<bullet> e)"
  "lim\<^sub>u(x \<rightarrow> p\<^sup>+)(e)" == "CONST bop CONST ulim_right p (\<lambda> x \<bullet> e)"
  "f cont-on\<^sub>u A"     == "CONST bop CONST continuous_on A f"

subsection \<open> Evaluation laws for expressions \<close>

text \<open> We now collect together all the definitional theorems for expression constructs, and use
  them to build an evaluation strategy for expressions that we will later use to construct
  proof tactics for UTP predicates. \<close>
  
lemmas uexpr_defs =
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
(*  plus_list_def *)
  
text \<open> The following laws show how to evaluate the core expressions constructs in terms of which
  the above definitions are defined. Thus, using these theorems together, we can convert any UTP 
  expression into a pure HOL expression. All these theorems are marked as \emph{ueval} theorems
  which can be used for evaluation. \<close>
  
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

lemma qtop_ueval [ueval]: "\<lbrakk>qtop f x y z w\<rbrakk>\<^sub>eb = f (\<lbrakk>x\<rbrakk>\<^sub>eb) (\<lbrakk>y\<rbrakk>\<^sub>eb) (\<lbrakk>z\<rbrakk>\<^sub>eb) (\<lbrakk>w\<rbrakk>\<^sub>eb)"
  by (transfer, simp)

text \<open> We also add all the definitional expressions to the evaluation theorem set. \<close>
    
declare uexpr_defs [ueval]

subsection \<open> Misc laws \<close>

text \<open> We also prove a few useful algebraic and expansion laws for expressions. \<close>
  
lemma uop_const [simp]: "uop id u = u"
  by (transfer, simp)

lemma bop_const_1 [simp]: "bop (\<lambda>x y. y) u v = v"
  by (transfer, simp)

lemma bop_const_2 [simp]: "bop (\<lambda>x y. x) u v = u"
  by (transfer, simp)

lemma uinter_empty_1 [simp]: "x \<inter>\<^sub>u {}\<^sub>u = {}\<^sub>u"
  by (transfer, simp)

lemma uinter_empty_2 [simp]: "{}\<^sub>u \<inter>\<^sub>u x = {}\<^sub>u"
  by (transfer, simp)

lemma uunion_empty_1 [simp]: "{}\<^sub>u \<union>\<^sub>u x = x"
  by (transfer, simp)

lemma uset_minus_empty [simp]: "x - {}\<^sub>u = x"
  by (simp add: uexpr_defs, transfer, simp)

lemma ulist_filter_empty [simp]: "x \<restriction>\<^sub>u {}\<^sub>u = \<langle>\<rangle>"
  by (transfer, simp)

lemma tail_cons [simp]: "tail\<^sub>u(\<langle>x\<rangle> ^\<^sub>u xs) = xs"
  by (transfer, simp)

lemma ufun_apply_lit [simp]: 
  "\<guillemotleft>f\<guillemotright>(\<guillemotleft>x\<guillemotright>)\<^sub>a = \<guillemotleft>f(x)\<guillemotright>"
  by (transfer, simp)
    
subsection \<open> Literalise tactics \<close>

text \<open> The following tactic converts literal HOL expressions to UTP expressions and vice-versa
        via a collection of simplification rules. The two tactics are called "literalise", which
        converts UTP to expressions to HOL expressions -- i.e. it pushes them into literals --
        and unliteralise that reverses this. We collect the equations in a theorem attribute
        called "lit\_simps". \<close>

lemma lit_zero [lit_simps]: "\<guillemotleft>0\<guillemotright> = 0" by (simp add: ueval)
lemma lit_one [lit_simps]: "\<guillemotleft>1\<guillemotright> = 1" by (simp add: ueval)
lemma lit_numeral [lit_simps]: "\<guillemotleft>numeral n\<guillemotright> = numeral n" by (simp add: ueval)
lemma lit_uminus [lit_simps]: "\<guillemotleft>- x\<guillemotright> = - \<guillemotleft>x\<guillemotright>" by (simp add: ueval, transfer, simp)
lemma lit_plus [lit_simps]: "\<guillemotleft>x + y\<guillemotright> = \<guillemotleft>x\<guillemotright> + \<guillemotleft>y\<guillemotright>" by (simp add: ueval, transfer, simp)
lemma lit_minus [lit_simps]: "\<guillemotleft>x - y\<guillemotright> = \<guillemotleft>x\<guillemotright> - \<guillemotleft>y\<guillemotright>" by (simp add: ueval, transfer, simp)
lemma lit_times [lit_simps]: "\<guillemotleft>x * y\<guillemotright> = \<guillemotleft>x\<guillemotright> * \<guillemotleft>y\<guillemotright>" by (simp add: ueval, transfer, simp)
lemma lit_divide [lit_simps]: "\<guillemotleft>x / y\<guillemotright> = \<guillemotleft>x\<guillemotright> / \<guillemotleft>y\<guillemotright>" by (simp add: ueval, transfer, simp)
lemma lit_div [lit_simps]: "\<guillemotleft>x div y\<guillemotright> = \<guillemotleft>x\<guillemotright> div \<guillemotleft>y\<guillemotright>" by (simp add: ueval, transfer, simp)
lemma lit_power [lit_simps]: "\<guillemotleft>x ^ n\<guillemotright> = \<guillemotleft>x\<guillemotright> ^ n" by (simp add: lit.rep_eq power_rep_eq uexpr_eq_iff)
    
lemma lit_plus_appl [lit_norm]: "\<guillemotleft>op +\<guillemotright>(x)\<^sub>a(y)\<^sub>a = x + y" by (simp add: ueval, transfer, simp)
lemma lit_minus_appl [lit_norm]: "\<guillemotleft>op -\<guillemotright>(x)\<^sub>a(y)\<^sub>a = x - y" by (simp add: ueval, transfer, simp)
lemma lit_mult_appl [lit_norm]: "\<guillemotleft>op *\<guillemotright>(x)\<^sub>a(y)\<^sub>a = x * y" by (simp add: ueval, transfer, simp)
lemma lit_divide_apply [lit_norm]: "\<guillemotleft>op /\<guillemotright>(x)\<^sub>a(y)\<^sub>a = x / y" by (simp add: ueval, transfer, simp)
    
lemma lit_fun_simps [lit_simps]:
  "\<guillemotleft>i x y z u\<guillemotright> = qtop i \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright> \<guillemotleft>z\<guillemotright> \<guillemotleft>u\<guillemotright>"
  "\<guillemotleft>h x y z\<guillemotright> = trop h \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright> \<guillemotleft>z\<guillemotright>"
  "\<guillemotleft>g x y\<guillemotright> = bop g \<guillemotleft>x\<guillemotright> \<guillemotleft>y\<guillemotright>"
  "\<guillemotleft>f x\<guillemotright> = uop f \<guillemotleft>x\<guillemotright>"
  by (transfer, simp)+

text \<open> In general unliteralising converts function applications to corresponding expression
  liftings. Since some operators, like + and *, have specific operators we also have to
  use @{thm uexpr_defs} in reverse to correctly interpret these. Moreover, numerals must be handled
  separately by first simplifying them and then converting them into UTP expression numerals;
  hence the following two simplification rules. \<close>

lemma lit_numeral_1: "uop numeral x = Abs_uexpr (\<lambda>b. numeral (\<lbrakk>x\<rbrakk>\<^sub>e b))"
  by (simp add: uop_def)

lemma lit_numeral_2: "Abs_uexpr (\<lambda> b. numeral v) = numeral v"
  by (metis lit.abs_eq lit_numeral)
  
method literalise = (unfold lit_simps[THEN sym])
method unliteralise = (unfold lit_simps uexpr_defs[THEN sym];
                     (unfold lit_numeral_1 ; (unfold ueval); (unfold lit_numeral_2))?)+
                   
text {* The following tactic can be used to evaluate literal expressions. It first literalises UTP 
  expressions, that is pushes as many operators into literals as possible. Then it tries to simplify,
  and final unliteralises at the end. *}

method uexpr_simp uses simps = ((literalise)?, simp add: lit_norm simps, (unliteralise)?)

(* Example *)
  
lemma "(1::(int, '\<alpha>) uexpr) + \<guillemotleft>2\<guillemotright> = 4 \<longleftrightarrow> \<guillemotleft>3\<guillemotright> = 4"
  apply (uexpr_simp) oops
  
end