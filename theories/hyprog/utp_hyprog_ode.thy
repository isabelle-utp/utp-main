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
  assumes "vwb_lens x" "bounded_linear get\<^bsub>x\<^esub>" "\<langle>F'\<rangle>\<^sub>s x = 0"
  shows "ode F' B nmods \<^bold>c:x"
proof (rel_simp', auto)
  fix m f t
  assume a: "0 \<le> t" "\<forall>x. 0 \<le> x \<and> x \<le> t \<longrightarrow> (f has_vector_derivative \<lbrakk>F'\<rbrakk>\<^sub>e (f x)) (at x) \<and> \<lbrakk>B\<rbrakk>\<^sub>e \<lparr>cvec\<^sub>v = f x, \<dots> = m\<rparr>"
  from assms(3) have "\<forall>t. get\<^bsub>x\<^esub> (\<lbrakk>F'\<rbrakk>\<^sub>e t) = 0"
    by (rel_simp)
  hence b: "\<forall>y. 0 \<le> y \<and> y \<le> t \<longrightarrow> ((get\<^bsub>x\<^esub> \<circ> f) has_vector_derivative 0) (at y)"
    by (metis a(2) assms(2) bounded_linear_imp_has_derivative vector_derivative_diff_chain_within)
  have "\<exists> c. \<forall>y. 0 \<le> y \<and> y \<le> t \<longrightarrow> get\<^bsub>x\<^esub> (f y) = c"
    using b has_vector_derivative_at_within 
    by (rule_tac has_vector_derivative_zero_constant[of "{0..t}" "(get\<^bsub>x\<^esub> \<circ> f)", simplified]; blast)
  hence "get\<^bsub>x\<^esub> (f t) = get\<^bsub>x\<^esub> (f 0)"
    using a(1) by blast
  thus "f t = put\<^bsub>x\<^esub> (f t) (get\<^bsub>x\<^esub> (f 0))"
    by (metis assms(1) vwb_lens_wb wb_lens.get_put)
qed

lemma usubst_in_var_frame [usubst]:"\<lbrakk> vwb_lens a; x \<subseteq>\<^sub>L a; out\<alpha> \<sharp> e \<rbrakk> \<Longrightarrow> (a:[P])\<lbrakk>e/$x\<rbrakk> = (a:[P\<lbrakk>e/$x\<rbrakk>])"
  by (rel_auto)

lemma solves_unrest_in_var:
  shows "$\<^bold>c:x \<sharp> (solves\<^sub>u \<F> \<F>' B l)"
  by (rel_simp')

lemma solves_unrest_out_var:
  shows "$\<^bold>c:x\<acute> \<sharp> (solves\<^sub>u \<F> \<F>' B l)"
  by (rel_simp')

utp_const solves\<^sub>u (0 3)

lemma has_derivative_vec_upd:
  "((\<lambda>f. vec_upd f i x) has_derivative (\<lambda>f. vec_upd f i 0)) F"
  apply (simp add: vec_upd_def)
  apply (rule has_derivative_vec)
  apply (rename_tac v)
  apply (case_tac "v = i")
   apply (simp_all)
  apply (rule bounded_linear_imp_has_derivative, simp add: bounded_linear_vec_nth)
  done

lemma vec_upd_prop:
  "\<lbrakk> \<forall>b. get\<^bsub>vec_lens i\<^esub> (\<lbrakk>F'\<rbrakk>\<^sub>e b) = 0 \<rbrakk> \<Longrightarrow> vec_upd (n *\<^sub>R \<lbrakk>F'\<rbrakk>\<^sub>e (F x)) i 0 = n *\<^sub>R \<lbrakk>F'\<rbrakk>\<^sub>e (F x)"
  by (smt fun_upd_apply lens.simps(1) scale_zero_right vec_lambda_unique vec_lens_def vec_upd_def vector_component(7))

lemma ode_nuses_constant_cvar:
  assumes "\<langle>F'\<rangle>\<^sub>s (vec_lens i) = 0" "\<pi>[i] \<sharp> F'" "\<^bold>c:\<pi>[i] \<sharp> B"
  shows "ode F' B nuses \<^bold>c:\<pi>[i]"
proof (rule nuses_nmods_intro, simp_all add: assms ode_nmods_constant_cvar)
  from assms show "\<forall>v. \<^bold>c:\<pi>[i] := \<guillemotleft>v\<guillemotright> ;; ode F' B ;; \<^bold>c:\<pi>[i] := \<guillemotleft>v\<guillemotright> = ode F' B ;; \<^bold>c:\<pi>[i] := \<guillemotleft>v\<guillemotright>"
    apply (rel_auto')
     apply (rename_tac v s d F l)
     apply (rule_tac x="\<lparr>cvec\<^sub>v = vec_upd (F l) i (vec_nth s i), \<dots> = d\<rparr>" in exI)
     apply (simp)
     apply (rule_tac x="(\<lambda> t. vec_upd (F t) i (vec_nth s i))" in exI)
     apply (rule_tac x="l" in exI)
     apply (simp)
     apply (auto)[1]
       apply (simp add: has_vector_derivative_def)
       apply (rule_tac f'="\<lambda> n. vec_upd (n *\<^sub>R \<lbrakk>F'\<rbrakk>\<^sub>e (F x)) i 0" in has_derivative_eq_rhs)
        apply (rule_tac g="(\<lambda>a. vec_upd a i (vec_nth s i))" and g'="(\<lambda>a. vec_upd a i 0)" in has_derivative_compose)
         apply blast
        apply (simp add: has_derivative_vec_upd vec_lens_def)
       apply (metis (mono_tags, lifting) scale_zero_right vec_upd_nth vector_scaleR_component)
      apply (metis (mono_tags) hybs.select_convs(1) hybs.update_convs(1))
     apply (metis vec_upd_nth vec_upd_upd)
    apply (rename_tac v d F l)
    apply (rule_tac x="\<lparr>cvec\<^sub>v = vec_upd (F l) i v, \<dots> = d\<rparr>" in exI)
    apply (simp)
    apply (rule_tac x="(\<lambda> t. vec_upd (F t) i v)" in exI)
    apply (rule_tac x="l" in exI)
    apply (auto)
     apply (simp add: has_vector_derivative_def)
     apply (rule_tac f'="\<lambda> n. vec_upd (n *\<^sub>R \<lbrakk>F'\<rbrakk>\<^sub>e (F x)) i 0" in has_derivative_eq_rhs)
      apply (rule_tac g="(\<lambda>a. vec_upd a i v)" and g'="(\<lambda>a. vec_upd a i 0)" in has_derivative_compose)
       apply (blast)
    using has_derivative_vec_upd apply blast
     apply (metis (no_types, hide_lams) scale_zero_right vec_upd_nth vector_scaleR_component)
    apply (metis hybs.select_convs(1) hybs.update_convs(1))
    done
qed

lemma disc_nmods_invar:
  "\<lbrakk> \<^bold>c \<sharp> b; P nmods \<^bold>d \<rbrakk> \<Longrightarrow> \<^bold>{b\<^bold>}P\<^bold>{b\<^bold>}"
  by (rel_simp', force)

lemma cont_nmods_invar:
  "\<lbrakk> \<^bold>d \<sharp> b; P nmods \<^bold>c \<rbrakk> \<Longrightarrow> \<^bold>{b\<^bold>}P\<^bold>{b\<^bold>}"
  by (rel_simp', force)


end