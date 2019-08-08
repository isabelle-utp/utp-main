section \<open> UTP Easy Expression Parser \<close>

theory utp_easy_parser
  imports "utp_full"
begin

subsection \<open> Replacing the Expression Grammar \<close>

text \<open> The following theory provides an easy to use expression parser that is primarily targetted
  towards expressing programs. Unlike the built-in UTP expression syntax, this uses a closed grammar
  separate to the HOL \emph{logic} nonterminal, that gives more freedom in what can be expressed.
  In particular, identifiers are interpreted as UTP variables rather than HOL variables and functions
  do not require subscripts and other strange decorations. 

  The first step is to remove the from the UTP parse the following grammar rule that uses arbitrary
  HOL logic to represent expressions. Instead, we will populate the \emph{uexp} grammar manually.
\<close>

purge_syntax
  "_uexp_l"  :: "logic \<Rightarrow> uexp" ("_" [64] 64)

subsection \<open> Expression Operators \<close>

syntax
  "_ue_quote" :: "uexp \<Rightarrow> logic" ("'(_')\<^sub>e")
  "_ue_tuple" :: "uexprs \<Rightarrow> uexp" ("'(_')")
  "_ue_lit"   :: "logic \<Rightarrow> uexp" ("\<guillemotleft>_\<guillemotright>")
  "_ue_var"   :: "svid \<Rightarrow> uexp" ("_")
  "_ue_ivar"  :: "svid \<Rightarrow> uexp" ("$_" [990] 990)
  "_ue_ovar"  :: "svid \<Rightarrow> uexp" ("$_\<acute>" [990] 990)
  "_ue_nexp"  :: "id \<Rightarrow> uexp" ("@_" [990] 990)
  "_ue_nexp_p":: "logic \<Rightarrow> uexp" ("@'(_')" [990] 990)
  "_ue_eq"    :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix "=" 150)
  "_ue_neq"   :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix "\<noteq>" 150)
  "_ue_uop"   :: "id   \<Rightarrow> uexp \<Rightarrow> uexp" ("_'(_')" [999,0] 999)
  "_ue_bop"   :: "id   \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("_'(_, _')" [999,0,0] 999)
  "_ue_trop"  :: "id   \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("_'(_, _, _')" [999,0,0,0] 999)
  "_ue_apply" :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("_[_]" [999,0] 999)
  "_ue_image" :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("_\<lparr>_\<rparr>" [999,0] 999)
  "_ue_aext" :: "uexp \<Rightarrow> salpha \<Rightarrow> uexp" (infixr "\<oplus>\<^sub>p" 195)
  "_ue_ifthenelse" :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("(3_ \<triangleleft> _ \<triangleright>/ _)" [52,0,53] 52)
  "_ue_ovrd"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixl "\<oplus>" 65)

translations
  "_ue_quote e" => "e"
  "_ue_tuple (_uexprs x (_uexprs y z))" => "_ue_tuple (_uexprs x (_ue_tuple (_uexprs y z)))"
  "_ue_tuple (_uexprs x y)" => "CONST bop CONST Pair x y"
  "_ue_tuple x" => "x"
  "_ue_lit x"    => "CONST lit x"
  "_ue_nexp P"   => "P"
  "_ue_nexp_p P" => "P"
  "_ue_var x"    => "CONST utp_expr.var (CONST pr_var x)"
  "_ue_ivar x"   => "CONST utp_expr.var (CONST in_var x)"
  "_ue_ovar x"   => "CONST utp_expr.var (CONST out_var x)"
  "_ue_eq x y"   => "x =\<^sub>u y"
  "_ue_neq x y"  => "x \<noteq>\<^sub>u y"
  "_ue_uop f x"   => "CONST uop f x"
  "_ue_bop f x y" => "CONST bop f x y"
  "_ue_trop f x y" => "CONST trop f x y"
  "_ue_apply f x" => "f(x)\<^sub>a"
  "_ue_image f A" => "f\<lparr>A\<rparr>\<^sub>u"
  "_ue_ifthenelse P b Q" => "CONST cond P b Q"
  "_ue_aext P a" => "CONST aext P a"
  "_ue_ovrd x y" => "_uovrd x y"

subsection \<open> Predicate Operators \<close>

syntax
  "_ue_true"  :: "uexp" ("true")
  "_ue_false" :: "uexp" ("false")
  "_ue_not"   :: "uexp \<Rightarrow> uexp" ("\<not> _" [40] 40)
  "_ue_conj"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr "\<and>" 135)
  "_ue_disj"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr "\<or>" 130)
  "_ue_impl"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr "\<Rightarrow>" 125)
  "_ue_iff"   :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr "\<Leftrightarrow>" 125)
  "_ue_mem"   :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("(_/ \<in> _)" [151, 151] 150)
  "_ue_nmem"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("(_/ \<notin> _)" [151, 151] 150)
  "_ue_shEx"  :: "pttrn \<Rightarrow> uexp \<Rightarrow> uexp"   ("\<^bold>\<exists> _ \<bullet> _" [0, 10] 10)
  "_ue_shAll":: "pttrn \<Rightarrow> uexp \<Rightarrow> uexp"   ("\<^bold>\<forall> _ \<bullet> _" [0, 10] 10)
  "_ue_shBEx" :: "pttrn \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp"   ("\<^bold>\<exists> _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  "_ue_shBAll" :: "pttrn \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp"   ("\<^bold>\<forall> _ \<in> _ \<bullet> _" [0, 0, 10] 10)

translations
  "_ue_true" => "CONST true_upred"
  "_ue_false" => "CONST false_upred"
  "_ue_not p" => "CONST not_upred p"
  "_ue_conj p q" => "p \<and>\<^sub>p q"
  "_ue_disj p q" => "p \<or>\<^sub>p q"
  "_ue_impl p q" => "p \<Rightarrow> q"
  "_ue_iff p q"  => "p \<Leftrightarrow> q"
  "_ue_mem x A"  => "x \<in>\<^sub>u A"
  "_ue_nmem x A" => "x \<notin>\<^sub>u A"
  "_ue_shEx x P" => "_ushEx x P"
  "_ue_shAll x P" => "_ushAll x P"
  "_ue_shBEx x A P" => "_ushBEx x A P"
  "_ue_shBAll x A P" => "_ushBAll x A P"

subsection \<open> Arithmetic Operators \<close>

syntax
  "_ue_num"    :: "num_const \<Rightarrow> uexp" ("_")
  "_ue_size"   :: "uexp \<Rightarrow> uexp" ("#_" [999] 999)
  "_ue_eq"     :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix "=" 150)
  "_ue_le"     :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix "\<le>" 150)
  "_ue_lt"     :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix "<" 150)
  "_ue_ge"     :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix "\<ge>" 150)
  "_ue_gt"     :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix ">" 150)
  "_ue_zero"   :: "uexp" ("0")
  "_ue_one"    :: "uexp" ("1")
  "_ue_plus"   :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixl "+" 165)
  "_ue_uminus" :: "uexp \<Rightarrow> uexp" ("- _" [181] 180)
  "_ue_minus"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixl "-" 165)
  "_ue_times"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixl "*" 170)
  "_ue_div"    :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixl "div" 170)

translations
  "_ue_num x"    => "_Numeral x"
  "_ue_size e"   => "#\<^sub>u(e)"
  "_ue_le x y"   => "x \<le>\<^sub>u y"
  "_ue_lt x y"   => "x <\<^sub>u y"
  "_ue_ge x y"   => "x \<ge>\<^sub>u y"
  "_ue_gt x y"   => "x >\<^sub>u y"
  "_ue_zero"     => "0" 
  "_ue_one"      => "1"
  "_ue_plus x y" => "x + y"
  "_ue_uminus x" => "- x"
  "_ue_minus x y" => "x - y"
  "_ue_times x y" => "x * y"
  "_ue_div x y"   => "CONST divide x y"

subsection \<open> Sets \<close>

syntax
  "_ue_empset"          :: "uexp" ("{}")
  "_ue_union"           :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixl "\<union>" 165)
  "_ue_inter"           :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixl "\<inter>" 170)
  "_ue_setprod"         :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr "\<times>" 180)
  "_ue_setenum"         :: "uexprs \<Rightarrow> uexp" ("{_}")
  "_ue_subseteq"        :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix "\<subseteq>" 150)
  "_ue_subset"          :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix "\<subset>" 150)
  "_ue_atLeastAtMost"   :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("(1{_.._})")
  "_ue_atLeastLessThan" :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("(1{_..<_})")
  "_ue_compr"           :: "pttrn \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("(1{_ :/ _ |/ _ \<bullet>/ _})")
  "_ue_compr_nset"      :: "pttrn \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("(1{_ |/ _ \<bullet>/ _})")
  "_ue_compr_nfun"      :: "pttrn \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("(1{_ :/ _ |/ _ })")
  "_ue_compr_nset_nfun" :: "pttrn \<Rightarrow> uexp \<Rightarrow> uexp" ("(1{_ |/ _ })")

translations
  "_ue_empset" => "{}\<^sub>u"
  "_ue_union x y" => "x \<union>\<^sub>u y"
  "_ue_inter x y" => "x \<inter>\<^sub>u y"
  "_ue_setprod e f" =>  "CONST bop (CONST Product_Type.Times) e f"
  "_ue_setenum (_uexprs x xs)" => "insert\<^sub>u x (_ue_setenum xs)"
  "_ue_setenum x" => "insert\<^sub>u x {}\<^sub>u"
  "_ue_subseteq x y" => "x \<subseteq>\<^sub>u y"
  "_ue_subset x y" => "x \<subset>\<^sub>u y"
  "_ue_atLeastAtMost m n" => "{m..n}\<^sub>u"
  "_ue_atLeastLessThan m n" => "{m..<n}\<^sub>u"
  "_ue_compr x A P F" => "_uset_compr x A P F"
  "_ue_compr_nset x P F" => "_uset_compr_nset x P F"
  "_ue_compr_nfun x A P" => "_uset_compr_nfun x A P"
  "_ue_compr_nset_nfun x P" => "_uset_compr_nset_nfun x P"

subsection \<open> Lists \<close>

syntax
  "_ue_nil"          :: "uexp" ("[]")
  "_ue_listenum"     :: "uexprs \<Rightarrow> uexp" ("[_]")
  "_ue_append"       :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr "@" 65)

translations
  "_ue_nil" => "\<langle>\<rangle>"
  "_ue_listenum (_uexprs x xs)" => "x #\<^sub>u (_ue_listenum xs)"
  "_ue_listenum x" => "\<langle>x\<rangle>"
  "_ue_append xs ys" => "xs ^\<^sub>u ys"

subsection \<open> Imperative Program Syntax \<close>

syntax
  "_ue_hoare"      :: "uexp \<Rightarrow> logic \<Rightarrow> uexp \<Rightarrow> logic" ("{{_}} / _ / {{_}}")
  "_ue_wp"         :: "logic \<Rightarrow> uexp \<Rightarrow> uexp" (infix "wp" 60)

translations
  "_ue_hoare b P c" => "\<lbrace>b\<rbrace>P\<lbrace>c\<rbrace>\<^sub>u"
  "_ue_wp P b" => "P wp b" 

end
