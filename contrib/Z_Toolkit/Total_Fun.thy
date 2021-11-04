theory Total_Fun
  imports Partial_Fun
begin

subsection \<open> Total function type and operations \<close>

text \<open> It may seem a little strange to create this, given we already have @{type fun}, but it's
  necessary to implement Z's type hierarchy. \<close>

typedef ('a, 'b) tfun = "{f :: 'a \<Zpfun> 'b. pdom(f) = UNIV}" 
  morphisms pfun_of_tfun Abs_tfun
  by (rule_tac x="pfun_entries UNIV (\<lambda> _. True) undefined" in exI, simp)

type_notation tfun (infixr "\<Rightarrow>\<^sub>t" 0)

setup_lifting type_definition_tfun

lift_definition mk_tfun :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>t 'b)" is
"\<lambda> f. fun_pfun f" by simp

lemma pfun_of_tfun_mk_tfun [simp]: "pfun_of_tfun (mk_tfun f) = fun_pfun f"
  by (transfer, simp)

end