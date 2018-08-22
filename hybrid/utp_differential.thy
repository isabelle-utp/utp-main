section {* Differential Equations and their Solutions *}

theory utp_differential
  imports utp_hyrel
begin
  
type_synonym 'c ODE = "real \<Rightarrow> 'c \<Rightarrow> 'c"

text {* An ordinary differential equation, @{typ "'c ODE"} is Isabelle is specified as a function
  from a real number, denoting the present time, and the continuous state @{typ "'c"} to the
  continuous state. Intuitively, the input @{typ "'c"} is the present value of the continuous
  variables, and that output @{typ "'c"} gives the derivative, that is the rate at which
  the continuous state is changing. For example, the ODE $\dot{x} = 5 \cdot x$, which states
  that $x$ is changing at a rate of $5 \cdot x$, is written in Isabelle as
  @{term "\<lambda> (t::real) (x::real). 5 * x"}. Of course we can only quantify this for certain kinds of
  type @{typ "'c"} and so we will usually require that @{typ "'c"} is a vector of real numbers,
  or some isomorphic structure. For more information on ODEs in Isabelle, please see~\cite{Immler2012}
  for a paper on an Isabelle analysis library for ODEs that this work depends on.
  *}

abbreviation hasDerivAtBefore ::
  "(real \<Rightarrow> 'a :: real_normed_vector, '\<alpha>) uexpr \<Rightarrow>
   ('a, '\<alpha>) uexpr \<Rightarrow>
   (real, '\<alpha>) uexpr \<Rightarrow>
   (real, '\<alpha>) uexpr \<Rightarrow>
   '\<alpha> upred" ("_ has-deriv _ at _ < _" [90, 0, 0, 91] 90) where  
"hasDerivAtBefore \<equiv> qtop (\<lambda> f f' t l. (f has_vector_derivative f') (at t within {0..l}))"

abbreviation hasDerivAll :: 
  "(real \<Rightarrow> 'a::real_normed_vector, 'd, 'c::t2_space) hyexpr \<Rightarrow> 
  (real \<Rightarrow> 'a, 'd, 'c) hyexpr \<Rightarrow> ('d,'c) hyrel" ("_ has-vderiv _" [90, 91] 90) where
"hasDerivAll \<equiv> trop (\<lambda> l f f'. (f has_vderiv_on f') ({0..l})) \<^bold>l"
  
translations
  "x has-vderiv y" <= 
  "CONST trop (\<lambda>l f f'. CONST Vector_Derivative_On.has_vderiv_on f1 f1' {0..l2}) \<^bold>l x y"

abbreviation hasOdeDerivAt ::
  "((real \<Rightarrow> 'c :: real_normed_vector), '\<alpha>) uexpr \<Rightarrow>
   ('c ODE, '\<alpha>) uexpr \<Rightarrow>
   (real, '\<alpha>) uexpr \<Rightarrow>
   (real, '\<alpha>) uexpr \<Rightarrow> '\<alpha> upred" ("_ has-ode-deriv _ at _ < _" [90, 0, 0, 91] 90)
where "hasOdeDerivAt \<F> \<F>' \<tau> l \<equiv>
       qtop (\<lambda> \<F> \<F>' \<tau> l. (\<F> has_vector_derivative \<F>' \<tau> (\<F> \<tau>)) (at \<tau> within {0..l})) \<F> \<F>' \<tau> l"
  
definition lensHasDeriv :: 
  "('a::real_normed_vector \<Longrightarrow> 'c::topological_space) \<Rightarrow> (real \<Rightarrow> ('a, 'c) uexpr) \<Rightarrow> ('d, 'c) hyrel" where
[upred_defs]: "lensHasDeriv x f = ($tr <\<^sub>u $tr\<acute> \<and> (\<^bold>\<forall> t \<in> {0..<\<^bold>l}\<^sub>u \<bullet> x~ has-deriv \<lceil>f(t)\<rceil>\<^sub>> @\<^sub>u t at \<guillemotleft>t\<guillemotright> < \<^bold>l))"

syntax
  "_has_der" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_ has-der _" [90, 91] 90)

translations
  "_has_der a f" => "CONST lensHasDeriv a (\<lambda> _time_var. f)"
  "_has_der a f" <= "CONST lensHasDeriv a (\<lambda> t. f)"

lemma lensHasDeriv_RR_closed [closure]: "(x has-der v(ti)) is RR"
  by (rel_auto)
    
lemma unrest_st'_lensHasDeriv [unrest]: "$st\<acute> \<sharp> (x has-der v(ti))"
  by (rel_auto)
  
text {* We introduce the notation @{term "\<F> has-ode-deriv \<F>' at t < \<tau>"} to mean that the derivative
  of a function @{term "\<F>"} is given by the ODE @{term "\<F>'"} at a point $t$ in the time domain
  $[0,\tau]$. Note, that unlike for our hybrid relational calculus we deal with ODEs over closed
  intervals; the final value at $\tau$ will correspond to the after value of the continuous
  state and justify that our timed trace is piecewise convergent. *}
 
definition hODE ::
  "('a::ordered_euclidean_space \<Longrightarrow> 'c::t2_space) \<Rightarrow>
   'a ODE \<Rightarrow> ('d, 'c) hyrel" where
[urel_defs]: "hODE x \<F>' = (\<^bold>\<exists> (\<F>, l) \<bullet> \<guillemotleft>l\<guillemotright> =\<^sub>u \<^bold>l \<and> ll(x) \<and> $tr <\<^sub>u $tr\<acute> \<and> \<lceil> \<guillemotleft>\<F>\<guillemotright> has-ode-deriv \<guillemotleft>\<F>'\<guillemotright> at \<guillemotleft>ti\<guillemotright> < \<guillemotleft>l\<guillemotright> \<and> $x\<acute> =\<^sub>u \<guillemotleft>\<F>\<guillemotright>(\<guillemotleft>ti\<guillemotright>)\<^sub>a \<rceil>\<^sub>h)"
        
syntax
  "_hODE" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<langle>_ \<bullet> _\<rangle>\<^sub>h")

translations
  "_hODE a P" => "CONST hODE a (\<lambda> _time_var. P)"
  "_hODE a P" <= "CONST hODE a (\<lambda> t. P)"    
  
lemma hODE_RR_closed [closure]: "\<langle>x \<bullet> F(ti)\<rangle>\<^sub>h is RR"
  by (rel_auto)
  
lemma hODE_unrests [unrest]:
  "$ok \<sharp> \<langle>x \<bullet> F(ti)\<rangle>\<^sub>h" "$ok\<acute> \<sharp> \<langle>x \<bullet> F(ti)\<rangle>\<^sub>h"
  "$wait \<sharp> \<langle>x \<bullet> F(ti)\<rangle>\<^sub>h" "$wait\<acute> \<sharp> \<langle>x \<bullet> F(ti)\<rangle>\<^sub>h"
  "$st\<acute> \<sharp> \<langle>x \<bullet> F(ti)\<rangle>\<^sub>h"  
  by (rel_auto)+
  
text {* We next introduce the construct @{term "\<langle>x \<bullet> \<F>'\<rangle>\<^sub>h"}, which states that continuous state lens
  $x$ evolves according the ODE described by @{term "\<F>'"}. The lens $x$ identifies a portion of
  the continuous state; that is it is not necessary that this construct define evolution for
  all continuous variables, only those specified. The others will evolve arbitrarily. The definition states that there is a function
  @{term "\<F>"} and evolution length @{term "l"}, such that at each instant $\tau$ in the time
  domain, @{term "\<F>'"} is the derivative @{term "\<F>"} and the continuous state $x$ is given by
  @{term "\<F>"}. Function @{term "\<F>"} is thus the solution of the ODE, and the definition states
  that such a solution exists. This actually may not always be the case, and if not such solution
  exists then the predicate will have the value @{term "false"}, the miraculous program. Note
  that since we use the hybrid interval operator here, the ODE will automatically pick up its
  initial value from the before value of $x$; thus an initial value problem is posed by this
  construct. Moreover, the final value of $x$ will be the value that the ODE tends toward at
  the limit, which is always defined as per our previous definition. *}

abbreviation hODE_IVP ("\<langle>_ := _ \<bullet> _\<rangle>\<^sub>h") where
"\<langle>x := x\<^sub>0 \<bullet> \<F>'\<rangle>\<^sub>h \<equiv> (st:\<^bold>c:x := x\<^sub>0 ;; \<langle>x \<bullet> \<F>'\<rangle>\<^sub>h)"

text {* We also set up notation that explicitly sets up the initial value for the continuous state,
  @{term "\<langle>x := x\<^sub>0 \<bullet> \<F>'\<rangle>\<^sub>h"}, which states that the initial value of @{term "x"} in the ODE
  @{term "\<F>'"} takes its value from @{term "x\<^sub>0"}. We next prove some important theorems about
  solutions to ODEs. *}

abbreviation hODE_frame ::
  "('a::ordered_euclidean_space \<Longrightarrow> 'c::t2_space) \<Rightarrow>
   'a ODE \<Rightarrow> ('d, 'c) hyrel" where
"hODE_frame x \<F>' \<equiv> hFrame x (hODE x \<F>')"
        
syntax
  "_hODE_frame" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<langle>_ : _\<rangle>\<^sub>h")

translations
  "_hODE_frame a P" => "CONST hODE_frame a (\<lambda> _time_var. P)"
  "_hODE_frame a P" <= "CONST hODE_frame a (\<lambda> t. P)"    

text {* ODEs can also have a frame attached, which the above operator provides. It implicitly
  contains the assumption that all variables not mentioned in the ODE are held constant
  during evolution. *}  
  
lemma at_has_deriv [simp]:
  "(f has-ode-deriv f' at ti < l) @\<^sub>u t = (f @\<^sub>u t) has-ode-deriv (f' @\<^sub>u t) at (ti @\<^sub>u t) < (l @\<^sub>u t)"
  by (simp add: at_def usubst alpha)
  
lemma at_within_closed_open:
  "\<lbrakk> 0 \<le> (t::real); t < l \<rbrakk> \<Longrightarrow> (at t within {0..l}) = (at t within {0..<l})"
  by (rule at_within_nhd[where S="{..<l}"], auto)

lemma hODE_as_has_der:
  assumes "vwb_lens x"
  shows "hODE x F' = (ll(x) \<and> x has-der \<guillemotleft>F' ti\<guillemotright>(&x)\<^sub>a)"
proof (rule antisym)
  show "hODE x F' \<sqsubseteq> (ll(x) \<and> x has-der \<guillemotleft>F' ti\<guillemotright>(&x)\<^sub>a)"
    by (rel_simp, metis tt_apply_minus)
  show "(ll(x) \<and> x has-der \<guillemotleft>F' ti\<guillemotright>(&x)\<^sub>a) \<sqsubseteq> hODE x F'"
  proof (rel_simp)
    fix tr b tr' t F
    assume a:
       "get\<^bsub>x\<^esub> b = get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(end\<^sub>t tr))" "tr < tr'"
       "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow>
            (F has_vector_derivative F' t (F t)) (at t within {0..end\<^sub>t (tr' - tr)}) \<and> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) = F t"
       "0 \<le> t" "t < end\<^sub>t (tr' - tr)"
              
    from a(3) have b: "\<And> t. t \<in> {0..<end\<^sub>t (tr' - tr)} \<Longrightarrow> F(t) = get\<^bsub>x\<^esub> (\<langle>tr' - tr\<rangle>\<^sub>t(t))"
      apply (auto)
      apply (drule_tac x="t" in spec)
      apply (simp)
      using a(2) apply auto
    done
        
    have c: "(F has_vector_derivative F' t (F t)) (at t within {0..<end\<^sub>t (tr' - tr)})" (is "?P")
      using a(3) a(4) a(5) at_within_closed_open by auto
            
    let ?G = "(\<lambda>t. get\<^bsub>x\<^esub> (\<langle>tr' - tr\<rangle>\<^sub>t(t)))"
        
    from a(4,5) b have "?P \<longleftrightarrow> (?G has_vector_derivative F' t (F t)) (at t within {0..<end\<^sub>t (tr' - tr)})"
      by (rule_tac has_vector_derivative_cong_ev, auto)
      
    with a(4,5) c show "(?G has_vector_derivative F' t (F t)) (at t within {0..end\<^sub>t (tr' - tr)})"
      by (simp add: at_within_closed_open)
  qed
qed
    
lemma ode_to_ivp:
  "vwb_lens x \<Longrightarrow> \<langle>x \<bullet> \<F>'\<rangle>\<^sub>h = (\<^bold>\<exists> x\<^sub>0 \<bullet> \<guillemotleft>x\<^sub>0\<guillemotright> =\<^sub>u $st:\<^bold>c:x \<and> \<langle>x := \<guillemotleft>x\<^sub>0\<guillemotright> \<bullet> \<F>'\<rangle>\<^sub>h)"
  by (rel_auto)

lemma ode_solution_refine:
  "\<lbrakk> vwb_lens x;
     \<forall> x. \<forall> l > 0. (\<F>(x) usolves_ode \<F>' from 0) {0..l} UNIV;
     \<forall> x. \<F>(x)(0) = x \<rbrakk>
   \<Longrightarrow> \<langle>x \<bullet> \<F>'(ti)\<rangle>\<^sub>h \<sqsubseteq> x \<leftarrow>\<^sub>h \<guillemotleft>\<F>\<guillemotright>($x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a"
  apply (rel_auto)    
  apply (rename_tac tr b tr')    
  apply (rule_tac x="\<F> (get\<^bsub>x\<^esub>b)" in exI)
  apply (auto simp add: usolves_ode_from_def solves_ode_def has_vderiv_on_def)[1]
done

lemma usolves_ode_subset:
  "\<lbrakk> (f usolves_ode f' from t\<^sub>0) T A; S \<subseteq> T; t\<^sub>0 \<in> S; is_interval S \<rbrakk> \<Longrightarrow> (f usolves_ode f' from t\<^sub>0) S A"
  apply (auto simp add: usolves_ode_from_def solves_ode_def has_vderiv_on_def)
  apply (meson has_vector_derivative_within_subset subset_iff)
  apply (meson dual_order.trans)
done
  
lemma ode_uniq_solution_refine:
  assumes
    "vwb_lens x" "\<forall> x. \<forall> l > 0. (\<F>(x) usolves_ode \<F>' from 0) {0..l} UNIV" "\<forall> x. \<F>(x)(0) = x"
  shows "x \<leftarrow>\<^sub>h \<guillemotleft>\<F>\<guillemotright>($x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a \<sqsubseteq> \<langle>x \<bullet> \<F>'(ti)\<rangle>\<^sub>h"
proof (rel_simp)
  fix tr b tr' \<G> t

  assume a:
    "tr < tr'"
    "get\<^bsub>x\<^esub> b = get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t (end\<^sub>t tr))"
    "tr \<le> tr'"
    "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow>
         (\<G> has_vector_derivative \<F>' t (\<G> t)) (at t within {0..end\<^sub>t (tr' - tr)}) \<and> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) = \<G> t"
    "0 \<le> t" "t < end\<^sub>t (tr' - tr)"
    
  let ?l = "end\<^sub>t (tr' - tr)"

  have l_nz: "?l > 0"
    using a by linarith
    
  from assms a have F_sol:"(\<F> (get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(end\<^sub>t tr))) usolves_ode \<F>' from 0) {0..?l} UNIV"
    by auto
    
  have G_sol: "(\<G> solves_ode \<F>') {0..<?l} UNIV"
  proof (rule solves_odeI, simp_all)
    from a show "(\<G> has_vderiv_on (\<lambda>x. \<F>' x (\<G> x))) {0..<?l}"
      apply (auto intro: has_vector_derivative_within_subset simp add: has_vderiv_on_def)
      apply (rename_tac t')
      apply (drule_tac x="t'" in spec)
      apply (auto intro: has_vector_derivative_within_subset)
    done
  qed
          
  have G_init: "\<G> 0 = \<F> (get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(end\<^sub>t tr))) 0"
    using a(4) assms(3) l_nz by auto
    
  show "\<G> t = \<F> (get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(end\<^sub>t tr))) t"
    by (rule_tac usolves_odeD(4)[OF F_sol, of "{0..<end\<^sub>t (tr' - tr)}"], auto simp add: l_nz G_sol G_init a)   
qed
    
theorem ode_solution:
  assumes 
    "vwb_lens x" "\<forall> x. \<forall> l > 0. (\<F>(x) usolves_ode \<F>' from 0) {0..l} UNIV" "\<forall> x. \<F>(x)(0) = x"
  shows "\<langle>x \<bullet> \<F>'(ti)\<rangle>\<^sub>h = x \<leftarrow>\<^sub>h \<guillemotleft>\<F>\<guillemotright>($x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a"
  using ode_solution_refine[of x \<F> \<F>'] ode_uniq_solution_refine[of x \<F> \<F>']
  by (auto intro: antisym simp add: assms)

theorem ode_solution':
  assumes 
    "vwb_lens x" 
    "\<And> x l. l > 0 \<Longrightarrow> (\<F>(x) usolves_ode \<F>' from 0) {0..l} UNIV" 
    "\<And> x. \<F>(x)(0) = x"
  shows "\<langle>x \<bullet> \<F>'(ti)\<rangle>\<^sub>h = x \<leftarrow>\<^sub>h \<guillemotleft>\<F>\<guillemotright>($x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a"
  by (simp add: assms(1) assms(2) assms(3) ode_solution)
    
theorem ode_frame_solution:
  assumes 
    "vwb_lens x" 
    "\<And> x l. l > 0 \<Longrightarrow> (\<F>(x) usolves_ode \<F>' from 0) {0..l} UNIV"
    "\<And> x. \<F>(x)(0) = x"
  shows "\<langle>x : \<F>'(ti)\<rangle>\<^sub>h = {[x \<mapsto>\<^sub>s \<guillemotleft>\<F>\<guillemotright>(&x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a]}\<^sub>h"
proof -
  have "\<langle>x : \<F>'(ti)\<rangle>\<^sub>h = x:[x \<leftarrow>\<^sub>h \<guillemotleft>\<F>\<guillemotright>($x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a]\<^sub>h"
    by (simp add: ode_solution'[where \<F>=\<F>] assms)
  also from assms(1) have "... = (\<lceil>$x\<acute> =\<^sub>u \<guillemotleft>\<F>\<guillemotright>($x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a \<and> x:[true]\<rceil>\<^sub>h \<and> 0 <\<^sub>u \<^bold>l)"
    by (rel_auto)
  also from assms(1) have "... = (\<lceil>x:[$x\<acute> =\<^sub>u \<guillemotleft>\<F>\<guillemotright>($x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a]\<rceil>\<^sub>h \<and> 0 <\<^sub>u \<^bold>l)"      
    by (simp add: frame_conj_true unrest)
  also have "... = (\<lceil>x:[$x\<acute> =\<^sub>u \<lceil>\<guillemotleft>\<F>\<guillemotright>(&x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a\<rceil>\<^sub><]\<rceil>\<^sub>h \<and> 0 <\<^sub>u \<^bold>l)"
    by (rel_auto)
  also from assms(1) have "... = {[x \<mapsto>\<^sub>s \<guillemotleft>\<F>\<guillemotright>(&x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a]}\<^sub>h"
    by (simp add: frame_is_assign hEvolves_def, rel_auto)
  finally show ?thesis .
qed
    
lemma uos_impl_uniq_sol:
  assumes "unique_on_strip t0 T f' L" "is_interval T"
  and "(f solves_ode f') T UNIV"
shows "(f usolves_ode f' from t0) T UNIV"
proof -
  interpret uos: unique_on_strip t0 T f' L
    by (simp add: assms)
  thm uos.solution_usolves_ode
  have "\<forall> t \<in> T. f t = uos.solution (f t0) t"
  proof (auto)
    fix t
    assume "t \<in> T"
    thus "f t = uos.solution (f t0) t"
      using usolves_odeD(4)[where T'="T" and z="f" and t="t", OF uos.solution_usolves_ode[of "f t0"]]
      by (simp add: assms)
  qed
  thus ?thesis
    using assms(3) uos.solution_usolves_ode usolves_ode_solves_odeI by blast
qed
 
text {* \emph{ode\_cert} is a simple tactic for certifying solutions to systems of differential equations *}

method ode_cert = (rule_tac solves_odeI, simp_all add: has_vderiv_on_def, safe intro!: has_vector_derivative_Pair, (rule has_vector_derivative_eq_rhs, (rule derivative_intros; (simp)?)+, simp)+)

text {* \emph{linear\_ode} certifies unique solutions for linears ODEs. *}

method linear_ode = 
  (rule_tac uos_impl_uniq_sol[where L=1], (unfold_locales, auto intro!: continuous_on_Pair continuous_on_const Topological_Spaces.continuous_on_fst Topological_Spaces.continuous_on_snd continuous_on_snd simp add: lipschitz_on_def dist_Pair_Pair prod.case_eq_if)[1], (auto)[1], ode_cert)  

text {* \emph{ode\_solve} tries to rewrite an ODE to a solution. The solution must be passed
  as a mandatory term parameter. *}

method ode_solve
  for sol :: "'a::ordered_euclidean_space \<Rightarrow> real \<Rightarrow> 'a" 
  = ((subst ode_solution'[where \<F> = "sol"]; (simp add: prod.case_eq_if)?), linear_ode)
  
text {* Version of above with frame *}
  
method ode_fsolve
  for sol :: "'a::ordered_euclidean_space \<Rightarrow> real \<Rightarrow> 'a" 
  = ((subst ode_frame_solution[where \<F> = "sol"]; (simp add: prod.case_eq_if)?), linear_ode)
  
text {* Example illustrating the relationship between derivative constrains and ordinary differential
  equations. If a variable has a constant derivative then this is equivalent to a trivial ODE. *}
    
lemma der_const_ode:
  assumes "vwb_lens x" "continuous_on UNIV get\<^bsub>x\<^esub>"
  shows "(ll(x) \<and> x has-der \<guillemotleft>n\<guillemotright>) = \<langle>x \<bullet> \<lambda> x. n\<rangle>\<^sub>h" (is "?lhs = ?rhs")
proof (rule antisym)
  show "?lhs \<sqsubseteq> ?rhs"
  proof (rel_simp)
    fix tr tr' f b t
    assume a:
      "get\<^bsub>x\<^esub> b = get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(end\<^sub>t tr))"
       "tr < tr'"
       "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow>
             (f has_vector_derivative n) (at t within {0..end\<^sub>t (tr' - tr)}) \<and> 
             get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) = f t"
       "0 \<le> t" "t < end\<^sub>t (tr' - tr)"
    from a(3)
    have b: "(f has_vector_derivative n) (at t within {0..end\<^sub>t (tr' - tr)})"
      using a(4) a(5) by blast
    have c: "(\<And>t. t \<in> {0..<end\<^sub>t (tr' - tr)} \<Longrightarrow> f t = get\<^bsub>x\<^esub> (\<langle>tr'-tr\<rangle>\<^sub>tt))"
      by (simp add: a(2) a(3) dual_order.strict_implies_order)
        
    have "(f has_vector_derivative n) (at t within {0..<end\<^sub>t (tr' - tr)}) \<longleftrightarrow>
          ((\<lambda>t. get\<^bsub>x\<^esub> (\<langle>tr'-tr\<rangle>\<^sub>tt)) has_vector_derivative n) (at t within {0..<end\<^sub>t (tr' - tr)})"
      by (rule has_vector_derivative_cong_ev, simp_all add: a c)

    with b show "((\<lambda>t. get\<^bsub>x\<^esub> (\<langle>tr'-tr\<rangle>\<^sub>tt)) has_vector_derivative n) (at t within {0..end\<^sub>t (tr' - tr)})"
      using a(4) a(5) at_within_closed_open b by auto
  qed
  show "?rhs \<sqsubseteq> ?lhs"  
    by (rel_auto)
qed
   
lemma hODE_conj:
  "(\<langle>x \<bullet> F'(ti)\<rangle>\<^sub>h \<and> \<langle>y \<bullet> G'(ti)\<rangle>\<^sub>h) = \<langle>{&x,&y} \<bullet> (\<lambda> (x, y). (F' ti x, G' ti y))\<rangle>\<^sub>h"
  apply (rel_auto)
    apply (rename_tac tr b tr' F G)
    apply (rule_tac x="\<lambda> t. (F t, G t)" in exI)
    apply (clarsimp)
    apply (rename_tac tr b tr' F G t)
    apply (drule_tac x="t" in spec)
    apply (simp)
    apply (drule_tac x="t" in spec)
        apply (simp)
  using Pair_has_vector_derivative apply blast
   apply (rename_tac tr b tr' FG)
   apply (rule_tac x="fst \<circ> FG" in exI)
   apply (clarsimp)
   apply (rename_tac tr b tr' FG t)
   apply (drule_tac x="t" in spec)
    apply (auto intro:derivative_intros)
   apply (metis fst_conv)
  apply (rename_tac tr b tr' FG)
   apply (rule_tac x="snd \<circ> FG" in exI)
   apply (clarsimp)
   apply (rename_tac tr b tr' FG t)
    apply (auto intro:derivative_intros)
  apply (metis snd_conv)
done
  
end