theory utp_expr_funcs
  imports utp_expr_insts utp_lift_parser
begin

\<comment> \<open> Polymorphic constructs \<close>

abbreviation (input) uceil  ("\<lceil>_\<rceil>\<^sub>u") where "\<lceil>x\<rceil>\<^sub>u \<equiv> uop ceiling x"
abbreviation (input) ufloor ("\<lfloor>_\<rfloor>\<^sub>u") where "\<lfloor>x\<rfloor>\<^sub>u \<equiv> uop floor x"
abbreviation (input) umin   ("min\<^sub>u'(_, _')") where "min\<^sub>u(x, y) \<equiv> bop min x y"
abbreviation (input) umax   ("max\<^sub>u'(_, _')") where "max\<^sub>u(x, y) \<equiv> bop max x y"
abbreviation (input) ugcd   ("gcd\<^sub>u'(_, _')") where "gcd\<^sub>u(x, y) \<equiv> bop gcd x y"

\<comment> \<open> Lists / Sequences \<close>

abbreviation (input) ucons    (infixr "#\<^sub>u" 65) where "x #\<^sub>u xs \<equiv> bop (#) x xs"
abbreviation (input) uappend  (infixr "^\<^sub>u" 80) where "x ^\<^sub>u y \<equiv> bop (@) x y"
abbreviation (input) udconcat (infixr "\<^sup>\<frown>\<^sub>u" 90) where "x \<^sup>\<frown>\<^sub>u y \<equiv> bop (\<^sup>\<frown>) x y"
abbreviation (input) ulast    ("last\<^sub>u'(_')") where "last\<^sub>u(x) \<equiv> uop last x"
abbreviation (input) ufront   ("front\<^sub>u'(_')") where "front\<^sub>u(x) \<equiv> uop butlast x"
abbreviation (input) uhead    ("head\<^sub>u'(_')") where "head\<^sub>u(x) \<equiv> uop hd x"
abbreviation (input) utail    ("tail\<^sub>u'(_')") where "tail\<^sub>u(x) \<equiv> uop tl x"
abbreviation (input) utake    ("take\<^sub>u'(_,/ _')") where "take\<^sub>u(n, xs) \<equiv> bop take n xs"
abbreviation (input) udrop    ("drop\<^sub>u'(_,/ _')") where "drop\<^sub>u(n, xs) \<equiv> bop drop n xs"
abbreviation (input) ufilter  (infixl "\<restriction>\<^sub>u" 75) where "xs \<restriction>\<^sub>u A \<equiv> bop seq_filter xs A"
abbreviation (input) uextract (infixl "\<upharpoonleft>\<^sub>u" 75) where "xs \<upharpoonleft>\<^sub>u A \<equiv> bop (\<upharpoonleft>\<^sub>l) A xs"
abbreviation (input) uelems   ("elems\<^sub>u'(_')") where "elems\<^sub>u(xs) \<equiv> uop set xs"
abbreviation (input) usorted   ("sorted\<^sub>u'(_')") where "sorted\<^sub>u(xs) \<equiv> uop sorted xs"
abbreviation (input) udistinct ("distinct\<^sub>u'(_')") where "distinct\<^sub>u(xs) \<equiv> uop set xs"
abbreviation (input) uupto     ("\<langle>_.._\<rangle>") where "\<langle>n..k\<rangle> \<equiv> bop upto n k"
abbreviation (input) uupt      ("\<langle>_..<_\<rangle>") where "\<langle>n..<k\<rangle> \<equiv> bop upt n k"
abbreviation (input) umap      ("map\<^sub>u") where "map\<^sub>u \<equiv> bop map"
abbreviation (input) uzip      ("zip\<^sub>u") where "zip\<^sub>u \<equiv> bop zip"

abbreviation (input) ufinite ("finite\<^sub>u'(_')") where "finite\<^sub>u(x) \<equiv> uop finite x"
abbreviation (input) uempset ("{}\<^sub>u") where "{}\<^sub>u \<equiv> \<guillemotleft>{}\<guillemotright>"
abbreviation (input) uunion  (infixl "\<union>\<^sub>u" 65) where "A \<union>\<^sub>u B \<equiv> bop (\<union>) A B"
abbreviation (input) uinter  (infixl "\<inter>\<^sub>u" 70) where "A \<inter>\<^sub>u B \<equiv> bop (\<inter>) A B"
abbreviation (input) uimage ("_\<lparr>_\<rparr>\<^sub>u" [10,0] 10) where "f\<lparr>A\<rparr>\<^sub>u \<equiv> bop image f A"
abbreviation (input) uinsert ("insert\<^sub>u") where "insert\<^sub>u x xs \<equiv> bop insert x xs"
abbreviation (input) usubset (infix "\<subset>\<^sub>u" 50) where "A \<subset>\<^sub>u B \<equiv> bop (\<subset>) A B"
abbreviation (input) usubseteq (infix "\<subseteq>\<^sub>u" 50) where "A \<subseteq>\<^sub>u B \<equiv> bop (\<subseteq>) A B"
abbreviation (input) uconverse ("(_\<^sup>~)" [1000] 999) where "P\<^sup>~ \<equiv> uop converse P"

syntax \<comment> \<open> Sets \<close>
  "_uset"       :: "args => ('a set, '\<alpha>) uexpr" ("{(_)}\<^sub>u")
  "_ucarrier"   :: "type \<Rightarrow> logic" ("[_]\<^sub>T")
  "_uid"        :: "type \<Rightarrow> logic" ("id[_]")
  "_uproduct"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr "\<times>\<^sub>u" 80)
  "_urelcomp"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr ";\<^sub>u" 75)

translations
  "{x, xs}\<^sub>u" => "insert\<^sub>u x {xs}\<^sub>u"
  "{x}\<^sub>u"     => "insert\<^sub>u x \<guillemotleft>{}\<guillemotright>"
  "['a]\<^sub>T"     == "\<guillemotleft>CONST set_of TYPE('a)\<guillemotright>"
  "id['a]"    == "\<guillemotleft>CONST Id_on (CONST set_of TYPE('a))\<guillemotright>"
  "A \<times>\<^sub>u B"    == "CONST bop CONST Product_Type.Times A B"
  "A ;\<^sub>u B"    == "CONST bop CONST relcomp A B"

\<comment> \<open> Sum types \<close>

abbreviation (input) uinl ("inl\<^sub>u'(_')") where "inl\<^sub>u(x) \<equiv> uop Inl x"
abbreviation (input) uinr ("inr\<^sub>u'(_')") where "inr\<^sub>u(x) \<equiv> uop Inr x"

subsection \<open> Lifting set collectors \<close>

text \<open> We provide syntax for various types of set collectors, including intervals and the Z-style
  set comprehension which is purpose built as a new lifted definition. \<close>
  
syntax
  "_uset_atLeastAtMost" :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" ("(1{_.._}\<^sub>u)")
  "_uset_atLeastLessThan" :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" ("(1{_..<_}\<^sub>u)")
  "_uset_compr" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(1{_ :/ _ |/ _ \<bullet>/ _})")
  "_uset_compr_nset" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(1{_ |/ _ \<bullet>/ _})")
  "_uset_compr_nfun" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(1{_ :/ _ |/ _})")
  "_uset_compr_nset_nfun" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("(1{_ |/ _})")
  "_uset_compr_nvar" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("(1{_ \<bullet>/ _})")

lift_definition ZedSetCompr ::
  "('a set, '\<alpha>) uexpr \<Rightarrow> ('a \<Rightarrow> (bool \<times> 'b, '\<alpha>) uexpr) \<Rightarrow> ('b set, '\<alpha>) uexpr"
is "\<lambda> A PF b. { snd (PF x b) | x. x \<in> A b \<and> fst (PF x b)}" .

abbreviation ZedImage :: 
  "(bool \<times> 'b, '\<alpha>) uexpr \<Rightarrow> ('b set, '\<alpha>) uexpr" where
"ZedImage PF \<equiv> ZedSetCompr \<guillemotleft>UNIV\<guillemotright> (\<lambda> x::unit. PF)"

translations
  "{x..y}\<^sub>u" => "CONST bop CONST atLeastAtMost x y"
  "{x..<y}\<^sub>u" => "CONST bop CONST atLeastLessThan x y"
  "{x | P \<bullet> F}" == "CONST ZedSetCompr (CONST lit CONST UNIV) (\<lambda> x. (P, F)\<^sub>u)"
  "{x : A | P \<bullet> F}" == "CONST ZedSetCompr A (\<lambda> x. (P, F)\<^sub>u)"
  "{x : A | P}" => "{x : A | P \<bullet> \<guillemotleft>x\<guillemotright>}"
  "{x | P}" == "{x : \<guillemotleft>CONST UNIV\<guillemotright> | P}"
  "{P \<bullet> F}" == "CONST ZedImage (P, F)\<^sub>u"

subsection \<open> Lifting limits \<close>
  
text \<open> We also lift the following functions on topological spaces for taking function limits,
  and describing continuity. \<close>

definition ulim_left :: "'a::order_topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b::t2_space" where
[uexpr_defs]: "ulim_left = (\<lambda> p f. Lim (at_left p) f)"

definition ulim_right :: "'a::order_topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b::t2_space" where
[uexpr_defs]: "ulim_right = (\<lambda> p f. Lim (at_right p) f)"

definition ucont_on :: "('a::topological_space \<Rightarrow> 'b::topological_space) \<Rightarrow> 'a set \<Rightarrow> bool" where
[uexpr_defs]: "ucont_on = (\<lambda> f A. continuous_on A f)"

syntax
  "_ulim_left"  :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("lim\<^sub>u'(_ \<rightarrow> _\<^sup>-')'(_')")
  "_ulim_right" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("lim\<^sub>u'(_ \<rightarrow> _\<^sup>+')'(_')")
  "_ucont_on"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "cont-on\<^sub>u" 90)

translations
  "lim\<^sub>u(x \<rightarrow> p\<^sup>-)(e)" == "CONST bop CONST ulim_left p (\<lambda> x \<bullet> e)"
  "lim\<^sub>u(x \<rightarrow> p\<^sup>+)(e)" == "CONST bop CONST ulim_right p (\<lambda> x \<bullet> e)"
  "f cont-on\<^sub>u A"     == "CONST bop CONST continuous_on A f"

lemma uset_minus_empty [simp]: "x - {}\<^sub>u = x"
  by (simp add: uexpr_defs, transfer, simp)

lemma uinter_empty_1 [simp]: "x \<inter>\<^sub>u {}\<^sub>u = {}\<^sub>u"
  by (transfer, simp)

lemma uinter_empty_2 [simp]: "{}\<^sub>u \<inter>\<^sub>u x = {}\<^sub>u"
  by (transfer, simp)

lemma uunion_empty_1 [simp]: "{}\<^sub>u \<union>\<^sub>u x = x"
  by (transfer, simp)

lemma uunion_insert [simp]: "(bop insert x A) \<union>\<^sub>u B = bop insert x (A \<union>\<^sub>u B)"
  by (transfer, simp)

lemma ulist_filter_empty [simp]: "x \<restriction>\<^sub>u {}\<^sub>u = \<guillemotleft>[]\<guillemotright>"
  by (transfer, simp)

lemma tail_cons [simp]: "tail\<^sub>u(x #\<^sub>u \<guillemotleft>[]\<guillemotright> ^\<^sub>u xs) = xs"
  by (transfer, simp)

lemma uconcat_units [simp]: "\<guillemotleft>[]\<guillemotright> ^\<^sub>u xs = xs" "xs ^\<^sub>u \<guillemotleft>[]\<guillemotright> = xs"
  by (transfer, simp)+

end