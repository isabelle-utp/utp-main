section \<open> UTP Easy Expression Parser \<close>
theory utp_easy_parser
  imports "utp"
begin

no_notation 
  while_top ("while _ do _ od") and
  while_inv ("while _ invr _ do _ od")

no_syntax
  "_uexp_l"  :: "logic \<Rightarrow> uexp" ("_" [75] 75)

syntax
  "_ue_true"  :: "uexp" ("true")
  "_ue_false" :: "uexp" ("false")
  "_ue_not"   :: "uexp \<Rightarrow> uexp" ("\<not> _" [40] 40)
  "_ue_conj"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr "\<and>" 35)
  "_ue_disj"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr "\<or>" 30)

translations
  "_ue_true" => "CONST true_upred"
  "_ue_false" => "CONST false_upred"
  "_ue_not p" => "CONST not_upred p"
  "_ue_conj p q" => "p \<and>\<^sub>p q"
  "_ue_disj p q" => "p \<or>\<^sub>p q"

syntax
  "_ue_paren" :: "uexp \<Rightarrow> uexp" ("'(_')")
  "_ue_lit"   :: "logic \<Rightarrow> uexp" ("\<guillemotleft>_\<guillemotright>")
  "_ue_num"   :: "num_const \<Rightarrow> uexp" ("_")
  "_ue_var"   :: "id \<Rightarrow> uexp" ("_")
  "_ue_size"  :: "uexp \<Rightarrow> uexp" ("#_" [999] 999)
  "_ue_eq"    :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix "=" 150)
  "_ue_le"    :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix "\<le>" 150)
  "_ue_lt"    :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix "<" 150)
  "_ue_ge"    :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix "\<ge>" 150)
  "_ue_gt"    :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix ">" 150)
  "_ue_zero"  :: "uexp" ("0")
  "_ue_one"   :: "uexp" ("1")
  "_ue_plus"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixl "+" 165)
  "_ue_minus" :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixl "-" 165)
  "_ue_uop"   :: "id   \<Rightarrow> uexp \<Rightarrow> uexp" ("_'(_')" [999,0] 999)
  "_ue_bop"   :: "id   \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("_'(_, _')" [999,0,0] 999)
  "_ue_trop"  :: "id   \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("_'(_, _, _')" [999,0,0,0] 999)
  "_ue_apply" :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("_[_]" [999] 999)

translations
  "_ue_paren x"  => "x"
  "_ue_lit x"    => "CONST lit x"
  "_ue_num x"    => "_Numeral x"
  "_ue_var x"    => "CONST utp_expr.var (CONST pr_var x)"
  "_ue_size e"   => "#\<^sub>u(e)"
  "_ue_eq x y"   => "x =\<^sub>u y"
  "_ue_le x y"   => "x \<le>\<^sub>u y"
  "_ue_lt x y"   => "x <\<^sub>u y"
  "_ue_ge x y"   => "x \<ge>\<^sub>u y"
  "_ue_gt x y"   => "x >\<^sub>u y"
  "_ue_zero"     => "0" 
  "_ue_one"      => "1"
  "_ue_plus x y" => "x + y"
  "_ue_minus x y" => "x - y"
  "_ue_uop f x"   => "CONST uop f x"
  "_ue_bop f x y" => "CONST bop f x y"
  "_ue_trop f x y" => "CONST trop f x y"
  "_ue_apply f x" => "f(x)\<^sub>a"

syntax
  "_ue_if_then"    :: "uexp \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("if _ then _ else _ fi")
  "_ue_while"      :: "uexp \<Rightarrow> logic \<Rightarrow> logic" ("while _ do _ od")
  "_ue_while_inv"  :: "uexp \<Rightarrow> uexp \<Rightarrow> logic \<Rightarrow> logic" ("while _ invr _ do _ od")
  "_ue_hoare"      :: "uexp \<Rightarrow> logic \<Rightarrow> uexp \<Rightarrow> logic" ("{{_}} / _ / {{_}}")

translations
  "_ue_if_then b P Q" => "P \<triangleleft> b \<triangleright>\<^sub>r Q"
  "_ue_while b P" == "CONST while_top b P"
  "_ue_while_inv b c P" == "CONST while_inv b c P"
  "_ue_hoare b P c" => "\<lbrace>b\<rbrace>P\<lbrace>c\<rbrace>\<^sub>u"

term "x := 5"

end