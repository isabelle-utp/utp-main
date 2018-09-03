section \<open> UTP Easy Expression Parser \<close>
theory utp_easy_parser
  imports "utp"
begin

no_notation 
  while_top ("while _ do _ od") and
  while_inv ("while _ invr _ do _ od")

no_syntax
  "_uexp_l"  :: "logic \<Rightarrow> uexp" ("_")

syntax
  "_ue_conj"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr "\<and>" 35)
  "_ue_disj"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr "\<or>" 30)

translations
  "_ue_conj p q" => "p \<and>\<^sub>p q"
  "_ue_disj p q" => "p \<or>\<^sub>p q"

syntax
  "_ue_paren" :: "uexp \<Rightarrow> uexp" ("'(_')")
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
  "_ue_apply" :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("_[_]" [999] 999)

translations
  "_ue_paren x"  => "x"
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
  "_ue_apply f x" => "f(x)\<^sub>a"


syntax
  "_ue_sum"        :: "uexp \<Rightarrow> uexp" ("sum'(_')")
  "_ue_take"       :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" ("take'(_, _')")

translations
  "_ue_sum x" => "sum\<^sub>u(x)"
  "_ue_take x y" => "take\<^sub>u(x, y)"


syntax
  "_ue_while"      :: "uexp \<Rightarrow> logic \<Rightarrow> logic" ("while _ do _ od")
  "_ue_while_inv"  :: "uexp \<Rightarrow> uexp \<Rightarrow> logic \<Rightarrow> logic" ("while _ invr _ do _ od")

translations
  "_ue_while b P" == "CONST while_top b P"
  "_ue_while_inv b c P" == "CONST while_inv b c P"

end