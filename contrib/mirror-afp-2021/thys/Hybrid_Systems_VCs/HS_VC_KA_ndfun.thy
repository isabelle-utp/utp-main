(*  Title:       Verification components with relational MKA 
    Author:      Jonathan Julián Huerta y Munive, 2020
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

subsection \<open> State transformer model \<close>

text \<open> We show that Kleene algebras have a state transformer model. For this we use the type of 
non-deterministic functions of the Transformer\_Semantics.Kleisli\_Quantale theory. Below we 
prove some auxiliary lemmas for them and show this instantiation. \<close>

theory HS_VC_KA_ndfun
  imports 
    Kleene_Algebra.Kleene_Algebra
    "Transformer_Semantics.Kleisli_Quantale"

begin

notation Abs_nd_fun ("_\<^sup>\<bullet>" [101] 100) 
     and Rep_nd_fun ("_\<^sub>\<bullet>" [101] 100)

declare Abs_nd_fun_inverse [simp]

lemma nd_fun_ext: "(\<And>x. (f\<^sub>\<bullet>) x = (g\<^sub>\<bullet>) x) \<Longrightarrow> f = g"
  apply(subgoal_tac "Rep_nd_fun f = Rep_nd_fun g")
  using Rep_nd_fun_inject 
   apply blast
  by(rule ext, simp)

lemma nd_fun_eq_iff: "(f = g) = (\<forall>x. (f\<^sub>\<bullet>) x = (g\<^sub>\<bullet>) x)"
  by (auto simp: nd_fun_ext)

instantiation nd_fun :: (type) kleene_algebra
begin

definition "0 = \<zeta>\<^sup>\<bullet>"

definition "star_nd_fun f = qstar f" for f::"'a nd_fun"

definition "f + g = ((f\<^sub>\<bullet>) \<squnion> (g\<^sub>\<bullet>))\<^sup>\<bullet>"

thm sup_nd_fun_def sup_fun_def

named_theorems nd_fun_ka "kleene algebra properties for nondeterministic functions."

lemma nd_fun_plus_assoc[nd_fun_ka]: "x + y + z = x + (y + z)"
  and nd_fun_plus_comm[nd_fun_ka]: "x + y = y + x"
  and nd_fun_plus_idem[nd_fun_ka]: "x + x = x" for x::"'a nd_fun"
  unfolding plus_nd_fun_def by (simp add: ksup_assoc, simp_all add: ksup_comm)

lemma nd_fun_distr[nd_fun_ka]: "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
  and nd_fun_distl[nd_fun_ka]: "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z" for x::"'a nd_fun"
  unfolding plus_nd_fun_def times_nd_fun_def by (simp_all add: kcomp_distr kcomp_distl)

lemma nd_fun_plus_zerol[nd_fun_ka]: "0 + x = x" 
  and nd_fun_mult_zerol[nd_fun_ka]: "0 \<cdot> x = 0"
  and nd_fun_mult_zeror[nd_fun_ka]: "x \<cdot> 0 = 0" for x::"'a nd_fun"
  unfolding plus_nd_fun_def zero_nd_fun_def times_nd_fun_def by auto

lemma nd_fun_leq[nd_fun_ka]: "(x \<le> y) = (x + y = y)"
  and nd_fun_less[nd_fun_ka]: "(x < y) = (x + y = y \<and> x \<noteq> y)"
  and nd_fun_leq_add[nd_fun_ka]: "z \<cdot> x \<le> z \<cdot> (x + y)" for x::"'a nd_fun"
  unfolding less_eq_nd_fun_def less_nd_fun_def plus_nd_fun_def times_nd_fun_def sup_fun_def
  by (unfold nd_fun_eq_iff le_fun_def, auto simp: kcomp_def)

lemma nd_star_one[nd_fun_ka]: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and nd_star_unfoldl[nd_fun_ka]: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  and nd_star_unfoldr[nd_fun_ka]: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y" for x::"'a nd_fun"
  unfolding plus_nd_fun_def star_nd_fun_def
    apply(simp_all add: fun_star_inductl sup_nd_fun.rep_eq fun_star_inductr)
  by (metis order_refl sup_nd_fun.rep_eq uwqlka.conway.dagger_unfoldl_eq)

instance
  apply intro_classes
  using nd_fun_ka by simp_all

end

end