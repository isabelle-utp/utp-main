section \<open> Ordinary Differential Equation Systems \<close>

theory utp_hyprog_ode
  imports utp_hyprog_prelim
begin

subsection \<open> Relational ODEs \<close>

text \<open> An ODE consists of equations @{term \<F>'} and a boundary condition @{term B}. It states that
  there exists a solution function @{term \<F>} and non-zero duration @{term l}, such that for 
  every @{term \<tau>} in the interval $[0, l]$ @{term \<F>'} is the derivative of @{term \<F>}, @{term B}
  holds on at each instant, and the before and after value of variable $x$ is equal to 
  @{term "\<F>(0)"} and @{term "\<F>(l)"}, respectively. \<close>

abbreviation solves :: 
  "(real \<Rightarrow> 'a::executable_euclidean_space) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a, 's) hybs_scheme upred \<Rightarrow> 's \<Rightarrow> real \<Rightarrow> bool" where
  "solves F F' B s l \<equiv>  (\<forall>x. 0 \<le> x \<and> x \<le> l \<longrightarrow> (F has_vector_derivative F' (F x)) (at x) \<and> (\<lbrakk>B\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F x, \<dots> = s\<rparr>)))"

definition solves\<^sub>u :: "(real \<Rightarrow> 'c::executable_euclidean_space) \<Rightarrow> 'c usubst \<Rightarrow> ('c, 's) hypred \<Rightarrow>  real \<Rightarrow> _" where
[upred_defs]:
"solves\<^sub>u \<F> \<F>' B l \<equiv> (\<^bold>\<forall> \<tau> \<in> {0..\<guillemotleft>l\<guillemotright>}\<^sub>u \<bullet> \<guillemotleft>(\<F> has_vector_derivative (\<lambda> _. \<lbrakk>\<F>'\<rbrakk>\<^sub>e) \<tau> (\<F> \<tau>)) (at \<tau>)
                      \<guillemotright> \<and> \<lceil>B\<lbrakk>\<guillemotleft>\<F>(\<tau>)\<guillemotright>/&cvec\<rbrakk>\<rceil>\<^sub><)"

definition ode :: "'c::executable_euclidean_space usubst \<Rightarrow> ('c, 's) hypred \<Rightarrow> ('c, 's) hyrel" where
[upred_defs]: "ode \<F>' B = cvec:[\<^bold>\<exists> (\<F>, l) \<bullet> \<guillemotleft>l\<guillemotright> \<ge>\<^sub>u 0 \<and> solves\<^sub>u \<F> \<F>' B l \<and> $cvec =\<^sub>u \<guillemotleft>\<F>(0)\<guillemotright> \<and> $cvec\<acute> =\<^sub>u \<guillemotleft>\<F>(l)\<guillemotright>]"

lemma ode_alt_def: "ode \<F>' B = ((\<^bold>\<exists> (\<F>, l) \<bullet> \<guillemotleft>l\<guillemotright> \<ge>\<^sub>u 0 \<and> solves\<^sub>u \<F> \<F>' B l \<and> $cvec =\<^sub>u \<guillemotleft>\<F>(0)\<guillemotright> \<and> $cvec\<acute> =\<^sub>u \<guillemotleft>\<F>(l)\<guillemotright>) \<and> U($\<^bold>d\<acute> = $\<^bold>d))"
  by (rel_auto)

text \<open> A framed ODE allows us to explicitly specify only certain continuous variables using a
  suitable lens that selects those variables we are interested in. The remainder are held constant
  by assigning them deriative 0. \<close>

definition fode :: 
  "('a::executable_euclidean_space \<Longrightarrow> 'b::executable_euclidean_space) \<Rightarrow> 'b usubst \<Rightarrow> 'b usubst" where
[upred_defs]: "fode x F = F \<circ>\<^sub>s [&\<^bold>v \<mapsto>\<^sub>s 0]"

subsection \<open> ODE Parser \<close>

text \<open> We set up a parser and pretty printer so that an ODE relation can be written using the
  familiar $\dot{x} = f(x)$ style syntax. \<close>

nonterminal sode and sodes

syntax
  "_ode"        :: "id \<Rightarrow> logic \<Rightarrow> sode" ("der'(_') = _")
  "_ode"        :: "id \<Rightarrow> logic \<Rightarrow> sode" ("_\<^sup>\<bullet> = _")
  "_ode_last"   :: "sode \<Rightarrow> sodes" ("_")
  "_ode_cons"   :: "sode \<Rightarrow> sodes \<Rightarrow> sodes" ("_,/ _")
  "_sys_ode"    :: "sodes \<Rightarrow> logic \<Rightarrow> logic" ("\<langle>_ | _\<rangle>")
  "_sys_ode_s"  :: "sodes \<Rightarrow> logic" ("\<langle>_\<rangle>")
  "_ode_lens"   :: "sodes \<Rightarrow> logic"
  "_ode_tuple"  :: "sodes \<Rightarrow> logic"
  "_ode_expr"   :: "sodes \<Rightarrow> logic"

translations
  "_ode_lens (_ode_cons (_ode x f) fs)" => "x +\<^sub>L (_ode_lens fs)"
  "_ode_lens (_ode_last (_ode x f))" => "x"
  "_ode_tuple (_ode_cons (_ode x f) fs)" => "(x, (_ode_tuple fs))"
  "_ode_tuple (_ode_last (_ode x f))" => "x"
  "_ode_expr (_ode_cons (_ode x f) fs)" => "(f, (_ode_expr fs))"
  "_ode_expr (_ode_last (_ode x f))" => "f"
  "_sys_ode fs B" => "CONST ode (CONST fode (_ode_lens fs /\<^sub>L CONST cvec) (_abs (_ode_tuple fs) (_ode_expr fs))) B"
  "_sys_ode_s fs" == "_sys_ode fs true"
  "_sys_ode (_ode y f) B" <= "CONST ode (CONST fode x (_abs y f)) B"
  "_ode_cons (_ode x f) (_ode y g)" <= "_ode (_pattern x y) (f, g)"


(*
term "\<langle>der(h) = v, der(v) = -9.81 | (&h \<ge>\<^sub>u 0)\<rangle>"
term "\<langle>x\<^sup>\<bullet> = f(x)\<rangle>"
*)

subsection \<open> ODE laws \<close>

lemma solves_le: "\<lbrakk> solves F F' B s l; l' \<le> l \<rbrakk> \<Longrightarrow> solves F F' B s l'"
  by (meson atLeastatMost_subset_iff has_vector_derivative_within_subset order_refl order_trans)

lemma ode_post: "ode F' B ;; ?[B] = ode F' B"
  by (rel_auto', metis (no_types), metis hybs.select_convs(1) order_refl)

lemma ode_mono:
  "`(C \<Rightarrow> B)` \<Longrightarrow> ode F' B \<sqsubseteq> ode F' C"
  by (rel_blast)

lemma frame_nmods_indep [closure]: "\<lbrakk> vwb_lens b; a \<bowtie> b \<rbrakk> \<Longrightarrow> a:[P] nmods b"
  by (rel_auto, metis lens_indep.lens_put_comm vwb_lens_wb wb_lens.get_put)

text \<open> ODE evolutions do not modify discrete variables \<close>

lemma ode_nmods_discrete: "ode F' B nmods \<^bold>d"
  by (simp add: ode_def closure)

text \<open> If a continuous variable has a zero derivative then it is not modified. \<close>

lemma ode_nmods_constant_cvar:
  assumes "cont_lens x" "\<langle>F'\<rangle>\<^sub>s x = 0"
  shows "ode F' B nmods \<^bold>c:x"
proof (rel_simp', auto)
  fix m f t
  assume a: "0 \<le> t" "\<forall>x. 0 \<le> x \<and> x \<le> t \<longrightarrow> (f has_vector_derivative \<lbrakk>F'\<rbrakk>\<^sub>e (f x)) (at x) \<and> \<lbrakk>B\<rbrakk>\<^sub>e \<lparr>cvec\<^sub>v = f x, \<dots> = m\<rparr>"
  from assms(2) have "\<forall>t. get\<^bsub>x\<^esub> (\<lbrakk>F'\<rbrakk>\<^sub>e t) = 0"
    by (rel_simp)
  hence b: "\<forall>y. 0 \<le> y \<and> y \<le> t \<longrightarrow> ((get\<^bsub>x\<^esub> \<circ> f) has_vector_derivative 0) (at y)"
    by (metis (no_types, lifting) a(2) assms(1) bounded_linear_imp_has_derivative cont_lens_bounded_linear vector_derivative_diff_chain_within)
  have "\<exists> c. \<forall>y. 0 \<le> y \<and> y \<le> t \<longrightarrow> get\<^bsub>x\<^esub> (f y) = c"
    using b has_vector_derivative_at_within 
    by (rule_tac has_vector_derivative_zero_constant[of "{0..t}" "(get\<^bsub>x\<^esub> \<circ> f)", simplified]; blast)
  hence "get\<^bsub>x\<^esub> (f t) = get\<^bsub>x\<^esub> (f 0)"
    using a(1) by blast
  thus "f t = put\<^bsub>x\<^esub> (f t) (get\<^bsub>x\<^esub> (f 0))"
    using assms(1) cont_lens_vwb vwb_lens.put_eq by force
qed

lemma ode_nuses_constant_cvar:
  fixes x :: "'b::real_normed_vector \<Longrightarrow> 'c::executable_euclidean_space"
  assumes "cont_lens x" "\<langle>F'\<rangle>\<^sub>s x = 0" "x \<sharp> F'" "\<^bold>c:x \<sharp> B"
  shows "ode F' B nuses \<^bold>c:x"
using assms proof (rule_tac nuses_nmods_intro, simp_all add: ode_nmods_constant_cvar)
  from assms show "\<forall>v. \<^bold>c:x := \<guillemotleft>v\<guillemotright> ;; ode F' B ;; \<^bold>c:x := \<guillemotleft>v\<guillemotright> = ode F' B ;; \<^bold>c:x := \<guillemotleft>v\<guillemotright>"
    apply (rel_auto')
     apply (rename_tac v s d F l)
     apply (rule_tac x="\<lparr>cvec\<^sub>v = put\<^bsub>x\<^esub> (F l) (get\<^bsub>x\<^esub> s), \<dots> = d\<rparr>" in exI)
     apply (simp)
     apply (rule_tac x="(\<lambda> t. put\<^bsub>x\<^esub> (F t) (get\<^bsub>x\<^esub> s))" in exI)
     apply (rule_tac x="l" in exI)
     apply (simp)
     apply (auto)[1]
     apply (rename_tac v s d F l t)
       apply (simp add: has_vector_derivative_def)
       apply (rule_tac f'="\<lambda> n. put\<^bsub>x\<^esub> (n *\<^sub>R \<lbrakk>F'\<rbrakk>\<^sub>e (F t)) 0" in has_derivative_eq_rhs)
        apply (rule_tac g="(\<lambda>a. put\<^bsub>x\<^esub> a (get\<^bsub>x\<^esub> s))" and g'="(\<lambda>a. put\<^bsub>x\<^esub> a 0)" in has_derivative_compose)
         apply blast
        apply (rule cont_lens.has_derivative_put'[OF assms(1)])
    using bounded_linear_ident apply blast
        apply (rule has_derivative_const)
    apply (metis (no_types, hide_lams) cont_lens_axioms_def cont_lens_def linear_simps(5) scale_zero_right vwb_lens_wb wb_lens.get_put)
    apply (metis hybs.select_convs(1) hybs.update_convs(1))
    apply (metis cont_lens_vwb vwb_lens.put_eq)
    apply (rename_tac v d F l)
    apply (rule_tac x="\<lparr>cvec\<^sub>v = put\<^bsub>x\<^esub> (F l) v, \<dots> = d\<rparr>" in exI)
    apply (simp)
    apply (rule_tac x="(\<lambda> t. put\<^bsub>x\<^esub> (F t) v)" in exI)
    apply (rule_tac x="l" in exI)
    apply (auto)
    apply (rename_tac v d F l t)
     apply (simp add: has_vector_derivative_def)
     apply (rule_tac f'="\<lambda> n. put\<^bsub>x\<^esub> (n *\<^sub>R \<lbrakk>F'\<rbrakk>\<^sub>e (F t)) 0" in has_derivative_eq_rhs)
      apply (rule_tac g="(\<lambda>a. put\<^bsub>x\<^esub> a v)" and g'="(\<lambda>a. put\<^bsub>x\<^esub> a 0)" in has_derivative_compose)
       apply (blast)
        apply (rule cont_lens.has_derivative_put'[OF assms(1)])
        using bounded_linear_ident apply blast
        apply (rule has_derivative_const)
    apply (metis (no_types, hide_lams) cont_lens_axioms_def cont_lens_def linear_simps(5) scale_zero_right vwb_lens_wb wb_lens.source_stability wb_lens_def weak_lens.put_get)    
    apply (metis hybs.select_convs(1) hybs.update_convs(1))
    done
qed      

lemma ode_nuses_constant_cvar_eucl:
  assumes "\<langle>F'\<rangle>\<^sub>s (vec_lens i) = 0" "\<pi>[i] \<sharp> F'" "\<^bold>c:\<pi>[i] \<sharp> B"
  shows "ode F' B nuses \<^bold>c:\<pi>[i]"
  by (rule ode_nuses_constant_cvar, simp_all add: assms)

lemma disc_nmods_invar:
  "\<lbrakk> \<^bold>c \<sharp> b; P nmods \<^bold>d \<rbrakk> \<Longrightarrow> \<^bold>{b\<^bold>}P\<^bold>{b\<^bold>}"
  by (rel_simp', force)

lemma cont_nmods_invar:
  "\<lbrakk> \<^bold>d \<sharp> b; P nmods \<^bold>c \<rbrakk> \<Longrightarrow> \<^bold>{b\<^bold>}P\<^bold>{b\<^bold>}"
  by (rel_simp', force)

end