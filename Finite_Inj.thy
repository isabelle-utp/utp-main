subsection \<open> Finite Injections \<close>

theory Finite_Inj
  imports Partial_Inj Finite_Fun
begin

typedef ('a, 'b) finj = "{f :: 'a \<Zpinj> 'b. finite(pidom(f))}"
  morphisms pinj_of_finj finj_of_pinj
  by (rule_tac x="{}\<^sub>\<rho>" in exI, simp)

setup_lifting type_definition_ffun
setup_lifting type_definition_finj

type_notation finj (infixr "\<Zfinj>" 1)

lift_definition ffun_of_finj :: "'a \<Zfinj> 'b \<Rightarrow> 'a \<Zffun> 'b" is "\<lambda> x. pfun_of_pinj (pinj_of_finj x)"
  by (transfer, simp, metis mem_Collect_eq pidom.rep_eq pinj_of_finj)

text \<open> Hide implementation details for finite functions and injections \<close>

lifting_update ffun.lifting
lifting_forget ffun.lifting

lifting_update finj.lifting
lifting_forget finj.lifting

end