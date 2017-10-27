section {* Hybrid Relational Calculus *}

theory utp_hyrel
imports
  "../utp/utp"
  "../theories/utp_csp"
  "../theories/utp_rea_designs"
  "../theories/utp_time_rel"
  "../contrib/Ordinary_Differential_Equations/ODE_Analysis"
  "../dynamics/Derivative_extra"
  "../dynamics/Timed_Traces"
  Topology_Euclidean_Space
begin recall_syntax
  
subsection {* Continuous Lenses and Preliminaries *}

lemma continuous_on_Pair_first:
  "\<lbrakk> continuous_on (A \<times> B) f; y \<in> B \<rbrakk> \<Longrightarrow> continuous_on A (\<lambda> x. f (x, y))"
  apply (rule continuous_on_compose[of _ "\<lambda> x. (x, y)" f, simplified])
   apply (rule continuous_on_Pair)
   apply (simp_all add: continuous_on_const continuous_on_id)
  apply (subgoal_tac "(\<lambda>x. (x, y)) ` A = A \<times> {y}")
   apply (auto intro: continuous_on_subset)
done

lemma continuous_on_Pair_second:
  "\<lbrakk> continuous_on (A \<times> B) f; x \<in> A \<rbrakk> \<Longrightarrow> continuous_on B (\<lambda> y. f (x, y))"
  apply (rule continuous_on_compose[of _ "\<lambda> y. (x, y)" f, simplified])
   apply (rule continuous_on_Pair)
   apply (simp_all add: continuous_on_const continuous_on_id)
  apply (subgoal_tac "(\<lambda>y. (x, y)) ` B = {x} \<times> B")
   apply (auto intro: continuous_on_subset)
done
  
lemma continuous_on_pairwise:
  "\<lbrakk> continuous_on A f; continuous_on B g \<rbrakk> \<Longrightarrow> continuous_on (A \<times> B) (\<lambda> (x, y). (f x, g y))"
  apply (simp add: prod.case_eq_if)
  apply (rule continuous_on_Pair)
  apply (rule continuous_on_compose[of "A \<times> B" fst f, simplified])
  apply (simp_all add: ODE_Auxiliarities.continuous_on_fst)
  apply (rule continuous_on_compose[of "A \<times> B" snd g, simplified])
  apply (simp_all add: ODE_Auxiliarities.continuous_on_snd)
done
  
locale continuous_lens = 
  vwb_lens x for x :: "'a::topological_space \<Longrightarrow> 'b::topological_space" (structure) +
  assumes get_continuous: "continuous_on A get"
  and put_continuous: "continuous_on B (uncurry put)"
begin
  
  lemma put_continuous_s: "continuous_on A (\<lambda> s. put s v)"
    apply (rule continuous_on_Pair_first[of _ UNIV "uncurry put", simplified])
    using put_continuous[of "A \<times> UNIV"]
    apply (simp add: prod.case_eq_if)
  done
  
  lemma put_continuous_v: "continuous_on B (\<lambda> v. put s v)"
    apply (rule continuous_on_Pair_second[of UNIV _ "uncurry put", simplified])
    using put_continuous[of "UNIV \<times> B"]
    apply (simp add: prod.case_eq_if)
  done

end
      
declare continuous_lens.get_continuous [simp]
declare continuous_lens.put_continuous_s [simp]
declare continuous_lens.put_continuous_v [simp]  
  
lemma continuous_lens_vwb [simp]: 
  "continuous_lens x \<Longrightarrow> vwb_lens x"
  by (simp_all add: continuous_lens_def)
  
lemma continuous_lens_intro:
  assumes 
    "vwb_lens x" 
    "\<And> A. continuous_on A get\<^bsub>x\<^esub>" 
    "\<And> B. continuous_on B (uncurry put\<^bsub>x\<^esub>)"
  shows "continuous_lens x"
  using assms
  by (auto simp add: continuous_lens_def continuous_lens_axioms_def assms)
        
lemma fst_continuous_lens [closure]: 
  "continuous_lens fst\<^sub>L"
  apply (unfold_locales, simp_all, simp_all add: lens_defs prod.case_eq_if continuous_on_fst)
  apply (rule continuous_on_Pair)
  using ODE_Auxiliarities.continuous_on_snd apply blast
  apply (simp add: ODE_Auxiliarities.continuous_on_fst Topological_Spaces.continuous_on_snd)
done
  
text {* The one lens is continuous *}
  
lemma one_lens_continuous [simp]:
  "continuous_on UNIV get\<^bsub>1\<^sub>L\<^esub>"
  by (simp add: lens_defs continuous_on_id)
  
text {* Lens summation of two continuous lenses is continuous *}
  
lemma continuous_on_plus_lens [continuous_intros]:
  "\<lbrakk> continuous_on A get\<^bsub>x\<^esub>; continuous_on A get\<^bsub>y\<^esub> \<rbrakk> \<Longrightarrow> continuous_on A get\<^bsub>x +\<^sub>L y\<^esub>"
  by (simp add: lens_defs ODE_Auxiliarities.continuous_on_Pair)

declare plus_vwb_lens [simp]
   
lemma lens_plus_continuous [closure]:
  assumes "continuous_lens x" "continuous_lens y" "x \<bowtie> y"
  shows "continuous_lens (x +\<^sub>L y)"
proof (rule continuous_lens_intro)
  show "vwb_lens (x +\<^sub>L y)"
    by (simp add: assms)
  show "\<And>A. continuous_on A get\<^bsub>x +\<^sub>L y\<^esub>"
    by (simp add: lens_defs ODE_Auxiliarities.continuous_on_Pair assms)  
  show "\<And>B. continuous_on B (uncurry put\<^bsub>x +\<^sub>L y\<^esub>)"
  proof -
    fix A v
    have "continuous_on A (uncurry put\<^bsub>x\<^esub> \<circ> (\<lambda>(s, v2, v1). (put\<^bsub>y\<^esub> s v1, v2)))"
    proof (rule continuous_on_compose[where s="A" and f="(\<lambda> (s, v2, v1). (put\<^bsub>y\<^esub> s v1, v2))" and g="uncurry put\<^bsub>x\<^esub>"])
      have "continuous_on A (uncurry put\<^bsub>y\<^esub> \<circ> (\<lambda>(x, y). (x, snd y)))"
        
        apply (rule continuous_on_compose[where s="A" and f="\<lambda> (x, y). (x, snd y)" and g="uncurry put\<^bsub>y\<^esub>"])
         apply (simp add: prod.case_eq_if)
          apply (rule continuous_on_Pair)
        apply (simp add: ODE_Auxiliarities.continuous_on_fst)
        apply (simp add: ODE_Auxiliarities.continuous_on_snd Topological_Spaces.continuous_on_snd)
        using assms(2) continuous_lens.put_continuous apply blast
      done
      thus "continuous_on A (\<lambda>(s, v2, v1). (put\<^bsub>y\<^esub> s v1, v2))"
       apply (simp add: prod.case_eq_if)
        apply (rule continuous_on_Pair)
        apply (auto)
        using ODE_Auxiliarities.continuous_on_snd Topological_Spaces.continuous_on_fst by blast
    next
      show "continuous_on ((\<lambda>(s, v2, v1). (put\<^bsub>y\<^esub> s v1, v2)) ` A) (uncurry put\<^bsub>x\<^esub>)"
        using assms(1) continuous_lens.put_continuous by auto
    qed

    thus "continuous_on A (uncurry put\<^bsub>x +\<^sub>L y\<^esub>)"
      by (simp add: lens_defs ODE_Auxiliarities.continuous_on_Pair assms prod.case_eq_if)
  qed
qed

no_notation inner (infix "\<bullet>" 70)

text {* We set up adhoc overloading to apply timed traces and contiguous functions *}

adhoc_overloading uapply cgf_apply and uapply tt_apply

text {* This section contains a mechanisation of the hybrid relational calculus described
  in~\cite{Foster16b}, though with a new semantic model based on generalised reactive processes
  and timed traces~\cite{Hayes2006, Hayes2010, Hofner2009}. *}

subsection {* Types and Preliminaries *}

text {* We first set up some types to represent hybrid relations. *}

type_synonym ('d,'c) hybs = "('d \<times> 'c, 'c ttrace, unit) rsp"
type_synonym ('d,'c) hyrel  = "('d,'c) hybs hrel"
type_synonym ('a,'d,'c) hycond = "('a,('d,'c) hybs) uexpr"
type_synonym ('a,'d,'c) hyexpr = "('a,('d,'c) hybs \<times> ('d,'c) hybs) uexpr"
  
translations
  (type) "('d,'c) hybs" <= (type) "('d \<times> 'c, 'c1 ttrace, unit) rsp"
  (type) "('d,'c) hyrel" <= (type) "('d, 'c) hybs hrel"
  (type) "('a,'d,'c) hyexpr" <= (type) "('a, ('d, 'c) hybs) hexpr"
  
text {* Type @{typ "('d, 'c) hybs"} represents a hybrid state, where the discrete part is stored
  in @{typ "'d"} and the continuous part in @{typ "'c"}. It is defined in terms of
  @{typ "('s, 't, '\<alpha>) rsp"}, the type of reactive stateful process which includes the observational
  variables like @{term ok} and @{term tr}. The type @{typ "'s"} corresponds to the state space of
  the process and @{typ "'t"} refers to the trace model of the process.

  In our case, the state space is a product of the discrete and continuous state, @{typ "'d \<times> 'c"},
  and the trace  is instantiated to be @{typ "'c ttrace"}, a timed trace over the continuous state
  @{typ 'c}. It must be emphasised that the continuous state is present both in the flat relational
  state and also in the timed trace. This is so that we can both manipulate the continuous state
  at a point through assignment, but also evolve it continuously using differential equations.

  Type @{typ "('d, 'c) hyrel"} is a hybrid relation -- a homogeneous relation over the hybrid
  state. Finally, @{typ "('a,'d, 'c) hyexpr"} is an expression over the hybrid state.

  Next we set up some necessary syntax and operators.
*}

syntax
  "_ulens_expr" :: "logic \<Rightarrow> svid \<Rightarrow> logic" ("_:'(_')" [100,100] 100)

translations
  "_ulens_expr e x" == "CONST uop get\<^bsub>x\<^esub> e"

text {* The syntax annotation @{term "e:(x)"} allows us to apply a variable lens $x$ to an
  expression $e$. This can be used, for example, to lookup a field of the given record or
  variable of a given state space. *}

abbreviation time_length :: "(real, 'd, 'c::topological_space) hyexpr" ("\<^bold>l")
  where "\<^bold>l \<equiv> uop end\<^sub>t (&tt)"
    
text {* @{term "\<^bold>l"} refers to the length of the time length of the current computation, and is
  obtained by taking length of the trace contribution. *}
  
abbreviation cvar ::
  "('a \<Longrightarrow> 'c::topological_space) \<Rightarrow> (real \<Rightarrow> 'a, 'd, 'c) hyexpr"
  ("_~" [999] 999)
where "x~ \<equiv> (\<lambda> t \<bullet> (&tt(\<guillemotleft>t\<guillemotright>)\<^sub>a:(x)))"
  
abbreviation cvar_app ::
  "('a \<Longrightarrow> 'c::topological_space) \<Rightarrow> (real, 'd, 'c) hyexpr \<Rightarrow> ('a, 'd, 'c) hyexpr"
  ("_~'(_')" [999,0] 999)
where "x~(t) \<equiv> &tt(t)\<^sub>a:(x)"
  
text {* The syntax @{term "x~(t)"} is a convenient way of refer to the value of a continuous
  variable $x$ at a particular instant $t$. *}

text {* We also set up some useful syntax to refer to the end of a continuous trace. *}

syntax
  "_uend" :: "logic \<Rightarrow> logic" ("end\<^sub>u'(_')")
  
translations
  "x~(t)" <= "CONST uop (CONST lens_get x) (CONST bop (CONST uapply) (CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr))) t)"
  "x~" <= "CONST ulambda (\<lambda> t. CONST uop (CONST lens_get x) (CONST bop (CONST uapply) (CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr))) (CONST ulit t2)))"
  "\<^bold>l" <= "CONST uop (CONST tt_end) (CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr)))"
  "\<^bold>l" <= "CONST uop CONST tt_end (&tt)"
  "end\<^sub>u(t)" == "CONST uop end\<^sub>t t"
  
definition disc_alpha :: "'d \<Longrightarrow> ('d \<times> 'c::topological_space)" ("\<^bold>d") where
[lens_defs]: "disc_alpha = fst\<^sub>L"

definition cont_alpha :: "'c \<Longrightarrow> ('d \<times> 'c::topological_space)" ("\<^bold>c") where
[lens_defs]: "cont_alpha = snd\<^sub>L"

text {* We also set up some lenses to focus on the discrete and continuous parts of the state,
  which we call @{term "\<^bold>d"} and @{term "\<^bold>c"}, respectively. We then prove some of the key lens
  theorems about these. *}

lemma disc_alpha_vwb_lens [simp]: "vwb_lens \<^bold>d"
  by (simp add: comp_vwb_lens disc_alpha_def fst_vwb_lens)

lemma cont_alpha_uvar [simp]: "vwb_lens \<^bold>c"
  by (simp add: comp_vwb_lens cont_alpha_def snd_vwb_lens)

lemma cont_indep_disc [simp]: "\<^bold>c \<bowtie> \<^bold>d" "\<^bold>d \<bowtie> \<^bold>c"
   by (simp_all add: disc_alpha_def cont_alpha_def)

 syntax
  "_cont_alpha" :: "svid" ("\<^bold>c")
  "_disc_alpha" :: "svid" ("\<^bold>d")

translations
  "_cont_alpha" == "CONST cont_alpha"
  "_disc_alpha" == "CONST disc_alpha"

lemma var_in_var_prod [simp]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "utp_expr.var ((in_var x) ;\<^sub>L X \<times>\<^sub>L Y) = $X:(x)"
  by (pred_auto)

lemma var_out_var_prod [simp]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "utp_expr.var ((out_var x) ;\<^sub>L X \<times>\<^sub>L Y) = $Y\<acute>:(x)"
  by (pred_auto)

text {* We next define some useful "lifting" operators. These operators effectively extend the state
  space of an expression by adding additional variables. This is useful, for instance, to lift an
  expression only on discrete variables to a hybrid expression. *}

abbreviation disc_lift :: "('a, 'd \<times> 'd) uexpr \<Rightarrow> ('a, 'd, 'c::topological_space) hyexpr" ("\<lceil>_\<rceil>\<^sub>\<delta>") where
"\<lceil>P\<rceil>\<^sub>\<delta> \<equiv> \<lceil>P \<oplus>\<^sub>p (\<^bold>d \<times>\<^sub>L \<^bold>d)\<rceil>\<^sub>S"

abbreviation cont_lift :: "('a, 'c \<times> 'c) uexpr \<Rightarrow> ('a, 'd, 'c::topological_space) hyexpr" ("\<lceil>_\<rceil>\<^sub>C") where
"\<lceil>P\<rceil>\<^sub>C \<equiv> \<lceil>P \<oplus>\<^sub>p (\<^bold>c \<times>\<^sub>L \<^bold>c)\<rceil>\<^sub>S"

abbreviation cont_drop :: "('a, 'd, 'c::topological_space) hyexpr \<Rightarrow> ('a, 'c \<times> 'c) uexpr" ("\<lfloor>_\<rfloor>\<^sub>C") where
"\<lfloor>P\<rfloor>\<^sub>C \<equiv> \<lfloor>P\<rfloor>\<^sub>S \<restriction>\<^sub>p (\<^bold>c \<times>\<^sub>L \<^bold>c)"

abbreviation cont_pre_lift :: "('a, 'c) uexpr \<Rightarrow> ('a,'d,'c::topological_space) hyexpr" ("\<lceil>_\<rceil>\<^sub>C\<^sub><") where
"\<lceil>P\<rceil>\<^sub>C\<^sub>< \<equiv> \<lceil>P \<oplus>\<^sub>p \<^bold>c\<rceil>\<^sub>S\<^sub><"

abbreviation cont_post_lift :: "('a, 'c) uexpr \<Rightarrow> ('a,'d,'c::topological_space) hyexpr" ("\<lceil>_\<rceil>\<^sub>C\<^sub>>") where
"\<lceil>P\<rceil>\<^sub>C\<^sub>> \<equiv> \<lceil>P \<oplus>\<^sub>p \<^bold>c\<rceil>\<^sub>S\<^sub>>"

abbreviation cont_pre_drop :: "('a,'d,'c::topological_space) hyexpr \<Rightarrow> ('a, 'c) uexpr" ("\<lfloor>_\<rfloor>\<^sub>C\<^sub><") where
"\<lfloor>P\<rfloor>\<^sub>C\<^sub>< \<equiv> \<lfloor>P\<rfloor>\<^sub>S \<restriction>\<^sub>p (ivar \<^bold>c)"

abbreviation cont_post_drop :: "('a,'d,'c::topological_space) hyexpr \<Rightarrow> ('a, 'c) uexpr" ("\<lfloor>_\<rfloor>\<^sub>C\<^sub>>") where
"\<lfloor>P\<rfloor>\<^sub>C\<^sub>> \<equiv> \<lfloor>P\<rfloor>\<^sub>S \<restriction>\<^sub>p (ovar \<^bold>c)"

translations
  "\<lceil>P\<rceil>\<^sub>C\<^sub><" <= "CONST aext P (CONST ivar CONST cont_alpha)"
  "\<lceil>P\<rceil>\<^sub>C\<^sub>>" <= "CONST aext P (CONST ovar CONST cont_alpha)"
  "\<lfloor>P\<rfloor>\<^sub>C\<^sub><" <= "CONST arestr P (CONST ivar CONST cont_alpha)"
  "\<lfloor>P\<rfloor>\<^sub>C\<^sub>>" <= "CONST arestr P (CONST ovar CONST cont_alpha)"

lemma unrest_lift_cont_subst [unrest]:
  "\<lbrakk> vwb_lens x; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> (\<lceil>P\<rceil>\<^sub>C\<^sub><)\<lbrakk>v/$st:\<^bold>c\<rbrakk>"
  by (rel_auto)
 
lemma lift_cont_subst [usubst]:
  "\<sigma>($st:\<^bold>c:x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> \<lceil>P\<rceil>\<^sub>C = \<sigma> \<dagger> (\<lceil>P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>\<rceil>\<^sub>C)"
  by (rel_simp)    
   
lemma unrest_lift_cont_disc [unrest]: 
  "$st:\<^bold>d \<sharp> \<lceil>P\<rceil>\<^sub>C" "$st:\<^bold>d\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>C"
  by (rel_auto)+
    
text {* @{term "\<lceil>P\<rceil>\<^sub>\<delta>"} takes an expression @{term "P"}, whose state space is the relational on
  the discrete state @{typ "'d"}, that is @{typ "'d \<times> 'd"} and lifts it into the hybrid state
  space, @{typ "('d, 'c) hybs"}. Note that following this lifting all continuous variables will
  be unconstrained -- this operator simply extends the alphabet. Similarly, @{term "\<lceil>P\<rceil>\<^sub>C"} lifts
  an expression on the relational continuous state to one on the whole hybrid state. Finally,
  @{term "\<lceil>P\<rceil>\<^sub>C\<^sub><"} lifts an expression on a scalar continuous state space @{typ "'c"} to one
  on the hybrid state. Effectively this is building a precondition, since it can only
  refer to unprimed continuous variables. *}

definition cont_st_post :: "'c::topological_space upred \<Rightarrow> ('d, 'c) hyrel" ("[_]\<^sub>C\<^sub>>") where
[upred_defs]: "cont_st_post b = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>b\<rceil>\<^sub>C\<^sub>>)"

definition cont_st_rel :: "'c::topological_space hrel \<Rightarrow> ('d, 'c) hyrel" ("[_]\<^sub>C") where
[upred_defs]: "cont_st_rel b = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>b\<rceil>\<^sub>C)"

lemma cont_st_post_RR [closure]: "[b]\<^sub>C\<^sub>> is RR"
  using minus_zero_eq by (rel_auto)

lemma cont_st_rel_RR [closure]: "[b]\<^sub>C is RR"
  using minus_zero_eq by (rel_auto)
    
lemma cont_st_post_false [rpred]: 
  "[false]\<^sub>C\<^sub>> = false"
  by rel_auto
    
lemma cont_st_post_true [rpred]: 
  "[true]\<^sub>C\<^sub>> = ($tr\<acute> =\<^sub>u $tr)"
  by (rel_auto)
    
lemma zero_least_uexpr [simp]:
  "0 \<le>\<^sub>u (x::('a::trace, '\<alpha>) uexpr) = true"
  by (rel_auto)
    
text {* The next properties states that the end point of an empty timed trace is 0. *}

lemma uend_0 [simp]: "end\<^sub>u(0) = 0"
  by (simp add: upred_defs lit_def uop_def Abs_uexpr_inverse)

subsection {* Instant Predicates *}

definition at ::
  "('a, 'c::topological_space \<times> 'c) uexpr \<Rightarrow> real \<Rightarrow> ('a, 'd, 'c) hyexpr"
  (infix "@\<^sub>u" 60) where
[upred_defs]: "P @\<^sub>u t = [$st:\<^bold>c\<acute> \<mapsto>\<^sub>s &tt(\<guillemotleft>t\<guillemotright>)\<^sub>a] \<dagger> \<lceil>P\<rceil>\<^sub>C"

text {* The expression @{term "P @\<^sub>u t"} asserts that the predicate @{term "P"} is satisfied by
  the continuous state at time instant @{term "t"}. Here, @{term "P"} is a predicate only
  on the flat continuous state. The operator is implemented by first extending the alphabet
  of @{term "P"} to include all the hybrid variables, and then substituting the continuous
  state for the continuous state at @{term "t"}. *}

lemma R2c_at: "R2c(P @\<^sub>u t) = P @\<^sub>u t"
  by (simp add: at_def R2c_def cond_idem usubst unrest R2s_def, rel_auto)

lemma R2c_time_length: "R2c (\<guillemotleft>t\<guillemotright> \<in>\<^sub>u {0..<\<^bold>l}\<^sub>u) = (\<guillemotleft>t\<guillemotright> \<in>\<^sub>u {0..<\<^bold>l}\<^sub>u)"
  by (rel_auto ; simp add: tt_end_minus)

text {* @{term "P @\<^sub>u t"} always satisfies healthiness condition @{term "R2c"}, meaning that it
  is history independent -- it does not refer to the variable @{term "tr"}, and only refers
  to the contribution of the present trace contained in @{term "&tt"}. This in an important
  property of hybrid predicates, since in a sequential hybrid program @{term "P ;; Q ;; R"}
  satisfaction of @{term "R2c"} ensures that $P$, $Q$, and $R$ all refer to different parts
  of the trace and cannot interfere with each other. We can show this is also the case of
  the predicate @{term "\<guillemotleft>t\<guillemotright> \<in>\<^sub>u {0..<\<^bold>l}\<^sub>u"}, since this only refers to @{term "\<^bold>l"}, which
  denotes the length of the present computation, and does not depend on the history. *}

lemma at_unrest_cont [unrest]: "$st:\<^bold>c\<acute> \<sharp> (P @\<^sub>u t)"
  by (simp_all add: at_def unrest)
  
lemma at_unrest_dis [unrest]: "$st:\<^bold>d \<sharp> (P @\<^sub>u t)" "$st:\<^bold>d\<acute> \<sharp> (P @\<^sub>u t)"
  by (simp_all add: at_def unrest)
    
lemma at_unrest_ok [unrest]: "$ok \<sharp> (P @\<^sub>u t)" "$ok\<acute> \<sharp> (P @\<^sub>u t)"
  by (simp_all add: at_def unrest alpha)

lemma at_unrest_wait [unrest]: "$wait \<sharp> (P @\<^sub>u t)" "$wait\<acute> \<sharp> (P @\<^sub>u t)"
  by (simp_all add: at_def unrest alpha)

text {* The above results tell us that the continuous state, @{term "ok"}, and @{term "wait"} are
  all not referred to by @{term "P @\<^sub>u t"}. We also prove some distributivity properties for
  the operator. *}

lemma at_true [simp]: "true @\<^sub>u t = true"
  by (simp add: at_def alpha usubst)

lemma at_false [simp]: "false @\<^sub>u t = false"
  by (simp add: at_def alpha usubst)

lemma at_conj [simp]: "(P \<and> Q) @\<^sub>u t = (P @\<^sub>u t \<and> Q @\<^sub>u t)"
  by (simp add: at_def alpha usubst)

lemma at_disj [simp]: "(P \<or> Q) @\<^sub>u t = (P @\<^sub>u t \<or> Q @\<^sub>u t)"
  by (simp add: at_def alpha usubst)

lemma at_ueq [simp]: "(x =\<^sub>u y) @\<^sub>u t = (x @\<^sub>u t =\<^sub>u y @\<^sub>u t)"
  by (simp add: at_def usubst alpha)

lemma at_plus [simp]:
  "(x + y) @\<^sub>u t = ((x @\<^sub>u t) + (y @\<^sub>u t))"
  by (simp add: at_def alpha usubst)

lemma at_lit [simp]:
  "\<guillemotleft>x\<guillemotright> @\<^sub>u t = \<guillemotleft>x\<guillemotright>"
  by (simp add: at_def usubst alpha)

lemma at_lambda [simp]:
  "(\<lambda> x \<bullet> f(x)) @\<^sub>u t = (\<lambda> x \<bullet> (f(x) @\<^sub>u t))"
  by (simp add: at_def usubst alpha)

lemma at_bop [simp]:
  "(bop f x y) @\<^sub>u t = bop f (x @\<^sub>u t) (y @\<^sub>u t)"
  by (simp add: at_def usubst alpha)
    
lemma at_subst_init_cont [usubst]:
  "\<sigma>($st:\<^bold>c:x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> (P @\<^sub>u t) = \<sigma> \<dagger> (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk> @\<^sub>u t)"
  by (rel_simp)
    
lemma at_var [simp]:
  fixes x :: "('a \<Longrightarrow> 'c::topological_space)"
  shows "$x\<acute> @\<^sub>u t = &tt(\<guillemotleft>t\<guillemotright>)\<^sub>a:(x)"
  by (pred_auto)

text {* Lemma @{thm [source] "at_var"} tells us the result of lifting a flat continuous variable
  @{term "x"}. It results in an expression which refers to that particular variable within the
  timed trace at instant @{term "t"}. *}

lemma subst_cvar_traj [usubst]: "\<langle>[$st:\<^bold>c \<mapsto>\<^sub>s &tt(\<guillemotleft>t\<guillemotright>)\<^sub>a]\<rangle>\<^sub>s (x ;\<^sub>L \<^bold>c ;\<^sub>L in_var st) = x~(\<guillemotleft>t\<guillemotright>)"
  by (pred_auto)

subsection {* The Interval Operator *}

definition hInt :: "(real \<Rightarrow> 'c::topological_space hrel) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "hInt P = ($tr \<le>\<^sub>u $tr\<acute> \<and> (\<^bold>\<forall> t \<in> {0..<\<^bold>l}\<^sub>u \<bullet> (P t) @\<^sub>u t))"

definition hInt_at :: "(real \<Rightarrow> 'c::topological_space hrel) \<Rightarrow> real \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "hInt_at P n = ($tr \<le>\<^sub>u $tr\<acute> \<and> (\<^bold>\<forall> t \<in> {0..<\<guillemotleft>n\<guillemotright>}\<^sub>u \<bullet> (P t) @\<^sub>u t))"

text {* The interval operator, @{term "hInt P"}, asserts that a predicate on the continuous state
  is satisfied at every instant between the beginning and end of the evolution, that is on the
  right-open interval $[0, \textbf{l})$. This is specified using the instant operator,
  @{term "(P t) @\<^sub>u t"}. Note that in this version of the interval operator we also allow that
  $P$ itself can depend on the instant $t$. We also require that the trace is \emph{strictly}
  increasing, meaning that the trace cannot be over an empty interval. The next couple of
  results that the interval does not constrain the $ok$, $wait$, or discrete variables. *}

lemma hInt_unrest_ok [unrest]: "$ok \<sharp> hInt P" "$ok\<acute> \<sharp> hInt P"
  by (simp_all add: hInt_def unrest)

lemma hInt_unrest_wait [unrest]: "$wait \<sharp> hInt P" "$wait\<acute> \<sharp> hInt P"
  by (simp_all add: hInt_def unrest)

lemma hInt_unrest_dis [unrest]: "$st:\<^bold>d \<sharp> hInt P" "$st:\<^bold>d\<acute> \<sharp> hInt P"
  by (simp_all add: hInt_def unrest)
    
definition init_cont :: "('a \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "init_cont x = ($tr \<le>\<^sub>u $tr\<acute> \<and> $st:\<^bold>c:x =\<^sub>u &tt(0)\<^sub>a:(x))"

text {* Take the continuous state space at the limit. If the duration is 0 then take the initial
  value of the continuous state instead. *}

definition tt_final :: "('c::t2_space, 'd, 'c) hyexpr" ("\<^bold>t\<^sup>\<rightarrow>") where
[upred_defs]: "tt_final = lim\<^sub>u(t \<rightarrow> \<^bold>l\<^sup>-)(&tt(\<guillemotleft>t\<guillemotright>)\<^sub>a) \<triangleleft> \<^bold>l >\<^sub>u 0 \<triangleright> $st:\<^bold>c\<acute>"

definition final_cont :: "('a \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "final_cont x = ($tr \<le>\<^sub>u $tr\<acute> \<and> $st:\<^bold>c:x\<acute> =\<^sub>u \<^bold>t\<^sup>\<rightarrow>:(x))"
  
syntax
  "_init_cont"  :: "salpha \<Rightarrow> logic" ("ll'(_')")
  "_final_cont" :: "salpha \<Rightarrow> logic" ("rl'(_')")

translations
  "_init_cont x" == "CONST init_cont x"
  "_final_cont x" == "CONST final_cont x"  
  
lemma init_cont_unrests [unrest]:
  "$ok \<sharp> ll(x)" "$ok\<acute> \<sharp> ll(x)" "$wait \<sharp> ll(x)" "$wait\<acute> \<sharp> ll(x)" "$st\<acute> \<sharp> ll(x)"
  by (rel_auto)+

lemma final_cont_unrests [unrest]:
  "$ok \<sharp> rl(x)" "$ok\<acute> \<sharp> rl(x)" "$wait \<sharp> rl(x)" "$wait\<acute> \<sharp> rl(x)"
  by (rel_auto)+

lemma trace_expr: "&tt = $tr\<acute> - $tr"
  by (rel_auto)
    
lemma usubst_final_cont [usubst]:
  "\<lbrakk> $tr \<sharp> \<sigma>; out\<alpha> \<sharp> \<sigma>; $st:\<^bold>c \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> rl(x) = rl(x)"
  by (simp add: final_cont_def tt_final_def trace_expr usubst unrest)
    
lemma R1_init_cont: "R1(ll(x)) = ll(x)"
  by (rel_auto)

lemma R1_final_cont: "R1(rl(x)) = rl(x)"
  by rel_auto
    
lemma R2c_init_cont: "R2c(ll(x)) = ll(x)"
  by (rel_auto)

lemma R2c_final_cont: "R2c(rl(x)) = rl(x)"
  by (rel_auto)
    
lemma ll_RR_closed [closure]: "ll(x) is RR"
  by (rel_auto)

lemma rl_RR_closed [closure]: "rl(x) is RR"
  by (rel_auto)

definition hDisInt :: "(real \<Rightarrow> 'c::t2_space hrel) \<Rightarrow> ('d, 'c) hyrel" where
[upred_defs]: "hDisInt P = (hInt P \<and> \<^bold>l >\<^sub>u 0 \<and> ll(&\<^bold>v) \<and> rl(&\<^bold>v) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d)"

text {* We also set up the adapted version of the interval operator, @{term "hDisInt P"}, that
  conjoins an interval specification with three predicates, which also happen to be coupling
  invariants, and yield what we might call a ``hybrid interval''. The first invariant
  states that the continuous state within the trace at instant 0 must
  correspond to the before value of the continuous state. The second
  states that the after value of the continuous state must take on the limit of the continuous
  state as the trace approaches the end value @{term "\<^bold>l"}, i.e. @{term "$st:\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> \<^bold>l\<^sup>-)(&tt(\<guillemotleft>x\<guillemotright>)\<^sub>a)"}.
  This second constraint requires that the timed trace must converge to a point at @{term "\<^bold>l"},
  which is true because our timed trace is piecewise convergent. The last two constraints are what
  makes our model a hybrid computational model, since we link together discrete assignments to
  continuous variables in the before and after state, and continuous evolution in the timed trace.
  The final predicate states that the discrete state does not change during a continuous evolution.

  We next set up some useful syntax translations for the interval operator. *}

syntax
  "_time_var" :: "logic"
  "_hInt"     :: "logic \<Rightarrow> logic" ("\<lceil>_\<rceil>\<^sub>h")
  "_hInt_at"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lceil>_\<rceil>\<^sub>h'(_')")
  "_hDisInt"  :: "logic \<Rightarrow> logic" ("\<^bold>\<lceil>_\<^bold>\<rceil>\<^sub>h")

parse_translation {*
let
  fun time_var_tr [] = Syntax.free "ti"
    | time_var_tr _  = raise Match;
in
[(@{syntax_const "_time_var"}, K time_var_tr)]
end
*}

translations
  "\<lceil>P\<rceil>\<^sub>h"    => "CONST hInt (\<lambda> _time_var. P)"
  "\<lceil>P\<rceil>\<^sub>h"    <= "CONST hInt (\<lambda> x. P)"
  "\<lceil>P\<rceil>\<^sub>h(n)" => "CONST hInt_at (\<lambda> _time_var. P) n"
  "\<lceil>P\<rceil>\<^sub>h(n)" <= "CONST hInt_at (\<lambda> x. P) n"
  "\<^bold>\<lceil>P\<^bold>\<rceil>\<^sub>h"    => "CONST hDisInt (\<lambda> _time_var. P)"
  "\<^bold>\<lceil>P\<^bold>\<rceil>\<^sub>h"    <= "CONST hDisInt (\<lambda> x. P)"
  
text {* A regular interval can be written using the notation @{term "\<lceil>P(ti)\<rceil>\<^sub>h"}, where $ti$ is
  a free variable denoting the present time. Having the present time as a free variable means
  we can write algebraic equations that depend on time, such as @{term "\<lceil>&x =\<^sub>u 2 * \<guillemotleft>ti\<guillemotright>\<rceil>\<^sub>h"} for
  example. Similarly, a hybrid interval can be written using a boldface as @{term "\<^bold>\<lceil>P(ti)\<^bold>\<rceil>\<^sub>h"}. *}

lemma hInt_unrest_cont [unrest]: "$st:\<^bold>c\<acute> \<sharp> \<lceil>P(ti)\<rceil>\<^sub>h"
  by (simp add: hInt_def unrest)

lemma st'_unrest_hInt [unrest]: 
  "$st\<acute> \<sharp> \<lceil>P(ti)\<rceil>\<^sub>h"
  by (rel_auto)
    
lemma R1_hInt: "R1(\<lceil>P(ti)\<rceil>\<^sub>h) = \<lceil>P(ti)\<rceil>\<^sub>h"
  by (rel_auto)

lemma R2s_hInt: "R2c(\<lceil>P(ti)\<rceil>\<^sub>h) = \<lceil>P(ti)\<rceil>\<^sub>h"
  by (rel_auto)

lemma R2_hInt: "R2(\<lceil>P(ti)\<rceil>\<^sub>h) = \<lceil>P(ti)\<rceil>\<^sub>h"
  by (metis R1_R2c_is_R2 R1_hInt R2s_hInt)

lemma hInt_RR_closed [closure]: "\<lceil>P(ti)\<rceil>\<^sub>h is RR"
  by (rel_auto)

text {* The following theorem demonstrates that we can use an interval specification in a reactive
  design precondition. *}
    
lemma neg_hInt_R1_true: "(\<not>\<^sub>r \<lceil>P(ti)\<rceil>\<^sub>h) ;; R1(true) = (\<not>\<^sub>r \<lceil>P(ti)\<rceil>\<^sub>h)"
proof (rel_auto)
  fix tr tr' tr'' :: "'a ttrace" and b :: "'a" and t :: real
  assume a: "tr \<le> tr''" "tr'' \<le> tr'" "0 \<le> t" "t < end\<^sub>t(tr'' - tr)" "\<not> \<lbrakk>P t\<rbrakk>\<^sub>e (b, \<langle>tr''\<rangle>\<^sub>t (t + end\<^sub>t tr))"
  hence "tr'' - tr \<le> tr' - tr"
    by (simp add: minus_cancel_le)
  with a show "\<exists>x. 0 \<le> x \<and> x < end\<^sub>t (tr' - tr) \<and> \<not> \<lbrakk>P x\<rbrakk>\<^sub>e (b, \<langle>tr' - tr\<rangle>\<^sub>t x)"
    apply (rule_tac x="t" in exI, auto)
    using tt_sub_end apply fastforce
    apply (metis dual_order.trans trace_class.le_iff_add tt_apply_minus tt_cat_ext_first)
  done
qed
    
lemma hInt_RC_closed [closure]: "\<lceil>P(ti)\<rceil>\<^sub>h is RC"
  by (rule RC_intro, simp_all add: closure neg_hInt_R1_true rpred)
    
text {* Theorem @{thm [source] "hInt_unrest_cont"} states that no continuous before variable
  is fixed by the regular interval operator. This is because the regular interval operator
  does not refer to state variables but only the evolution of the trajectory. We can also
  show that the interval operator is both @{term "R1"} healthy, since the trajectory can
  only get longer, and also @{term "R2c"} healthy, since it does not refer to the history.

  We also prove some laws about intervals. *}

lemma hInt_subst_init_cont [usubst]:
  "\<sigma>($st:\<^bold>c:x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> \<lceil>P(ti)\<rceil>\<^sub>h = \<sigma> \<dagger> \<lceil>P(ti)\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>\<rceil>\<^sub>h"
  by (simp add: hInt_def usubst)
  
lemma hInt_false [rpred]: "\<lceil>false\<rceil>\<^sub>h = ($tr\<acute> =\<^sub>u $tr)"
  by (rel_auto, meson eq_iff leI minus_zero_eq tt_end_0_iff tt_end_ge_0)

lemma hInt_true [rpred]: "\<lceil>true\<rceil>\<^sub>h = true\<^sub>r"
  by (rel_auto)

lemma hInt_conj [rpred]: "\<lceil>P(ti) \<and> Q(ti)\<rceil>\<^sub>h = (\<lceil>P(ti)\<rceil>\<^sub>h \<and> \<lceil>Q(ti)\<rceil>\<^sub>h)"
  by (rel_auto)

lemma hInt_disj: "\<lceil>P(ti) \<or> Q(ti)\<rceil>\<^sub>h \<sqsubseteq> (\<lceil>P(ti)\<rceil>\<^sub>h \<or> \<lceil>Q(ti)\<rceil>\<^sub>h)"
  by (rel_auto)

lemma hInt_refine: "`\<^bold>\<forall> ti \<bullet> P(ti) \<Rightarrow> Q(ti)` \<Longrightarrow> \<lceil>Q(ti)\<rceil>\<^sub>h \<sqsubseteq> \<lceil>P(ti)\<rceil>\<^sub>h"
  by (rel_auto)
        
text {* Theorem @{thm [source] hInt_false} and @{thm [source] hInt_true} give us obvious results
  about intervals over false and true. Theorem @{thm [source] hInt_conj} allows us to rewrite
  and interval conjunction as a conjunction of intervals. The same is not true of disjunction,
  as @{thm [source] hInt_disj} shows, because at each instant each $P$ or $Q$ may hold, and thus an
  inequality is present in the rule. Finally, theorem @{thm [source] hInt_refine} tells us that
  an interval can be refined to another is we can show that an implication between the two interval
  predicates. Additionally we prove the following law about sequential composition of
  time-independent intervals. *}

(*
lemma hInt_seq_r: "(\<lceil>P\<rceil>\<^sub>h ;; \<lceil>P\<rceil>\<^sub>h) = \<lceil>P\<rceil>\<^sub>h"
proof -
  have "(\<lceil>P\<rceil>\<^sub>h ;; \<lceil>P\<rceil>\<^sub>h) = (R2(\<lceil>P\<rceil>\<^sub>h) ;; R2(\<lceil>P\<rceil>\<^sub>h))"
    by (simp add: R2_hInt)
  also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((\<lceil>P\<rceil>\<^sub>h)\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; (\<lceil>P\<rceil>\<^sub>h)\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    by (simp add: R2_seqr_form)
  also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((\<guillemotleft>tt\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>)) ;;
                                     (\<guillemotleft>tt\<^sub>2\<guillemotright> \<ge>\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>))) \<and>
                         $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    by (simp add: hInt_def at_def usubst unrest)
  also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((\<guillemotleft>tt\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>)) \<and>
                                     (\<guillemotleft>tt\<^sub>2\<guillemotright> \<ge>\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>))) \<and>
                         $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    by (simp add: seqr_to_conj unrest)
  also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((\<guillemotleft>tt\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>tt\<^sub>2\<guillemotright> \<ge>\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>(\<guillemotleft>tt\<^sub>1\<guillemotright>+\<guillemotleft>tt\<^sub>2\<guillemotright>)\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>))) \<and>
                         $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    apply (rule shEx_cong)
    apply (rule shEx_cong)
    apply (rel_simp robust)
    apply (auto simp add: tt_end_cat)
    apply (rename_tac x xa P xb)
    apply (case_tac "xb < end\<^sub>t x")
    apply (auto simp add: tt_cat_ext_first tt_cat_ext_last)
    apply (metis add.right_neutral add_less_le_mono tt_cat_ext_first tt_end_ge_0)
    apply (rename_tac x xa P xb)
    apply (drule_tac x="end\<^sub>t x + xb" in spec)
    apply (simp)
  done
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> ((\<guillemotleft>tt\<^sub>0\<guillemotright> \<ge>\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>(\<guillemotleft>tt\<^sub>0\<guillemotright>)\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>))) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>)"
    apply (rel_auto)
    using add.assoc apply blast
    by (metis add.assoc add.left_neutral)
  also have "... = R2(\<lceil>P\<rceil>\<^sub>h)"
    by (simp add: R2_form hInt_def at_def usubst unrest)
  also have "... = \<lceil>P\<rceil>\<^sub>h"
    by (simp add: R2_hInt)
  finally show ?thesis .
qed
*)

text {* The proof of the theorem is quite long, but the theorem intuitively tells us that an interval
  can always be split into two intervals where the property holds of both. *}

lemma seq_var_ident_liftr:
  assumes "vwb_lens x" "$x\<acute> \<sharp> P" "$x \<sharp> Q"
  shows "((P \<and> $x\<acute> =\<^sub>u $x) ;; (Q \<and> $x\<acute> =\<^sub>u $x)) = ((P ;; Q) \<and> $x\<acute> =\<^sub>u $x)"
  using assms apply (rel_auto)
  by (metis (no_types, lifting) vwb_lens_wb wb_lens_weak weak_lens.put_get)

subsection {* Somewhere operator *}
  
text {* Dual of the interval operator *}
  
definition hSomewhere :: "(real \<Rightarrow> 'c::topological_space hrel) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "hSomewhere P = ($tr <\<^sub>u $tr\<acute> \<and> (\<^bold>\<exists> t \<in> {0..<\<^bold>l}\<^sub>u \<bullet> (P t) @\<^sub>u t))"

syntax
  "_hSomewhere"     :: "logic \<Rightarrow> logic" ("\<lfloor>_\<rfloor>\<^sub>h")

translations
  "\<lfloor>P\<rfloor>\<^sub>h"    => "CONST hSomewhere (\<lambda> _time_var. P)"
  "\<lfloor>P\<rfloor>\<^sub>h"    <= "CONST hSomewhere (\<lambda> x. P)"
  
lemma hSomewhere_RR_closed [closure]:
  "\<lfloor>P(ti)\<rfloor>\<^sub>h is RR"
  by (rel_auto)

lemma st'_unrest_hSomewhere [unrest]: 
  "$st\<acute> \<sharp> \<lfloor>P(ti)\<rfloor>\<^sub>h"
  by (rel_auto)

lemma hSomewhere_false [rpred]: "\<lfloor>false\<rfloor>\<^sub>h = false"
  by (rel_auto)

lemma hSomewhere_true [rpred]: "\<lfloor>true\<rfloor>\<^sub>h = ($tr <\<^sub>u $tr\<acute>)"
  by (rel_auto)
    
lemma rea_not_hInt [rpred]:
  "(\<not>\<^sub>r \<lceil>P(ti)\<rceil>\<^sub>h) = \<lfloor>\<not> P(ti)\<rfloor>\<^sub>h"
  apply (rel_auto) using tt_end_gr_zero_iff by fastforce

lemma rea_not_hSomewhere [rpred]:
  "(\<not>\<^sub>r \<lfloor>P(ti)\<rfloor>\<^sub>h) = \<lceil>\<not> P(ti)\<rceil>\<^sub>h"
  apply (rel_auto) using tt_end_gr_zero_iff by fastforce
    
subsection {* At Limit *}

text {* Predicate evaluated at the limit of the trajectory. *}
  
definition hAtLimit :: "'c::t2_space hrel \<Rightarrow> ('d,'c) hyrel" ("\<lceil>_\<rceil>\<^sup>\<rightarrow>") where
[upred_defs]: "hAtLimit P = ($tr <\<^sub>u $tr\<acute> \<and> [$st:\<^bold>c\<acute> \<mapsto>\<^sub>s \<^bold>t\<^sup>\<rightarrow>] \<dagger> \<lceil>P\<rceil>\<^sub>C)"
    
lemma hAtLimit_RR_closed [closure]: "\<lceil>P\<rceil>\<^sup>\<rightarrow> is RR"
  by (rel_auto)

subsection {* Evolve by continuous function *}
 
definition hEvolve :: "('a::t2_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> (real \<Rightarrow> ('a, 'c) hexpr) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "hEvolve x f = (\<lceil>$x\<acute> =\<^sub>u f(ti)\<rceil>\<^sub>h \<and> \<^bold>l >\<^sub>u 0)"

definition hEvolveUpTo :: 
  "('a::t2_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> 
   (real, 'd \<times> 'c) uexpr \<Rightarrow> 
   (real \<Rightarrow> ('a, 'c) hexpr) \<Rightarrow> 
   ('d,'c) hyrel" where
[upred_defs]: "hEvolveUpTo x l f = (hEvolve x f \<and> \<^bold>l \<le>\<^sub>u \<lceil>l\<rceil>\<^sub>S\<^sub>< )"

definition hEvolveBounds :: 
  "('a::t2_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> 
   (real, 'd \<times> 'c) uexpr \<Rightarrow>
   (real, 'd \<times> 'c) uexpr \<Rightarrow> 
   (real \<Rightarrow> ('a, 'c) hexpr) \<Rightarrow> 
   ('d,'c) hyrel" where
[upred_defs]: "hEvolveBounds x l u f = (hEvolve x f \<and> \<lceil>l\<rceil>\<^sub>S\<^sub>< \<le>\<^sub>u \<^bold>l  \<and> \<^bold>l \<le>\<^sub>u \<lceil>u\<rceil>\<^sub>S\<^sub>< \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d \<and> rl(&\<^bold>v))"

abbreviation hEvolveAt :: "('a::t2_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> (real, 'd \<times> 'c) uexpr \<Rightarrow> (real \<Rightarrow> ('a, 'c) hexpr) \<Rightarrow> ('d,'c) hyrel" where
"hEvolveAt x t f \<equiv> hEvolveBounds x t t f"

syntax
  "_hEvolve"       :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_ \<leftarrow>\<^sub>h _" [90,91] 90)
  "_hEvolveUpTo"   :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<leftarrow>\<^sub>h\<le>'(_') _" [90,0,91] 90)
  "_hEvolveBounds" :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<leftarrow>[_,_]\<^sub>h _" [90,0,0,91] 90)
  "_hEvolveAt"     :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<leftarrow>\<^sub>h'(_') _" [90,0,91] 90)  
  
translations
  "_hEvolve a f" => "CONST hEvolve a (\<lambda> _time_var. f)"
  "_hEvolve a f" <= "CONST hEvolve a (\<lambda> ti. f)"
  "_hEvolveUpTo a t f" => "CONST hEvolveUpTo a t (\<lambda> _time_var. f)"
  "_hEvolveUpTo a t f" <= "CONST hEvolveUpTo a t (\<lambda> ti. f)"
  "_hEvolveBounds a l u f" => "CONST hEvolveBounds a l u (\<lambda> _time_var. f)"
  "_hEvolveBounds a l u f" <= "CONST hEvolveBounds a l u (\<lambda> ti. f)"
  "_hEvolveAt a t f" => "CONST hEvolveAt a t (\<lambda> _time_var. f)"
  "_hEvolveAt a t f" <= "CONST hEvolveAt a t (\<lambda> ti. f)"

lemma hEvolve_unrests [unrest]:
  "$ok \<sharp> x \<leftarrow>\<^sub>h f(ti)" "$ok\<acute> \<sharp> x \<leftarrow>\<^sub>h f(ti)" "$wait \<sharp> x \<leftarrow>\<^sub>h f(ti)" "$wait\<acute> \<sharp> x \<leftarrow>\<^sub>h f(ti)" "$st\<acute> \<sharp> x \<leftarrow>\<^sub>h f(ti)"
  by (simp_all add: hEvolve_def unrest)

lemma hEvolveUpTo_st'_unrest [unrest]:
  "$st\<acute> \<sharp> x \<leftarrow>\<^sub>h\<le>(l) f(ti)"
  by (rel_auto)
    
lemma hEvolve_usubst [usubst]:
  "\<sigma>($st:\<^bold>c:x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> y \<leftarrow>\<^sub>h f(ti) = \<sigma> \<dagger> y \<leftarrow>\<^sub>h ((f ti)\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  by (simp add: hEvolve_def usubst unrest)
    
lemma hEvolve_RR_closed [closure]: "x \<leftarrow>\<^sub>h f(ti) is RR"
  by (rel_auto)

lemma hEvolveBounds_RR_closed [closure]: "(x \<leftarrow>[m,n]\<^sub>h f(ti)) is RR"
  by (rel_auto)
    
lemma hEvolveUpTo_RR_closed [closure]: "(x \<leftarrow>\<^sub>h\<le>(l) f(ti)) is RR"
  by (rel_auto)

lemma hEvolveAt_RR_closed [closure]: "x \<leftarrow>\<^sub>h(l) f(ti) is RR"
  by (rel_auto)
    
lemma hEvolve_conj [rpred]: 
  "(x \<leftarrow>\<^sub>h f(ti) \<and> y \<leftarrow>\<^sub>h g(ti)) = ({&x, &y} \<leftarrow>\<^sub>h (f ti, g ti)\<^sub>u)"
  by (rel_auto)
    
lemma hEvolve_spec_refine:
  assumes "vwb_lens x" "\<forall> ti\<ge>0. `P(ti)\<lbrakk>f(ti)/$x\<acute>\<rbrakk>`"
  shows "\<lceil>P(ti)\<rceil>\<^sub>h \<sqsubseteq> x \<leftarrow>\<^sub>h f(ti)"
  using assms
  apply (simp add: hEvolve_def)
  apply (rel_simp)
  apply (metis vwb_lens.put_eq)
done

subsection {* Pre-emption *}

definition hUntil ::
  "('d, 'c::t2_space) hyrel \<Rightarrow> (real \<Rightarrow> 'c hrel) \<Rightarrow> (real \<Rightarrow> 'c hrel) \<Rightarrow> ('d,'c) hyrel"  where
[upred_defs]: "hUntil P b c = (P \<and> \<lceil>b(ti)\<rceil>\<^sub>h \<and> $tr <\<^sub>u $tr\<acute> \<and> rl(&\<^bold>v) \<and> (\<^bold>\<exists> l \<bullet> \<guillemotleft>l\<guillemotright> =\<^sub>u \<^bold>l \<and> \<lceil>c(l)\<rceil>\<^sub>C) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d)"

syntax
  "_hUntil_inv" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ inv _ until\<^sub>h _" [74,0,75] 74)
  "_hUntil"     :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ until\<^sub>h _" [74,75] 74)

translations
  "_hUntil P b" => "CONST hUntil P (\<lambda> _time_var. \<not> b) (\<lambda> _time_var. b)"
  "_hUntil_inv P b c" => "CONST hUntil P (\<lambda> _time_var . b) (\<lambda> _time_var. c)"
  "_hUntil_inv P b c" <= "CONST hUntil P (\<lambda> t. b) (\<lambda> t'. c)"

definition hPreempt ::
  "('d, 'c::t2_space) hyrel \<Rightarrow> 'c hrel \<Rightarrow>
    ('d,'c) hyrel \<Rightarrow> ('d,'c) hyrel" ("_ [_]\<^sub>h _" [64,0,65] 64)
where [upred_defs]: "P [b]\<^sub>h Q = (((Q \<triangleleft> \<lceil>b\<lbrakk>$\<^bold>v/$\<^bold>v\<acute>\<rbrakk>\<rceil>\<^sub>C \<triangleright> (P \<and> \<lceil>\<not> b\<rceil>\<^sub>h)) \<sqinter> ((P \<and> \<lceil>\<not> b\<rceil>\<^sub>h \<and> $tr <\<^sub>u $tr\<acute> \<and> rl(&\<^bold>v) \<and> \<lceil>b\<rceil>\<^sub>C) ;; (Q))))"

text {* The pre-emption operator @{term "P [b]\<^sub>h Q"} states that $P$ is active until $b$ is satisfied
  by the continuous variables. At this point $Q$ will be activated. Usually $P$ will be an evolution
  of the continuous variables, and $b$ some kind of barrier condition. The operator can be used
  to write hybrid systems where an evolution occurs until some condition is satisfied, e.g. a
  particular temperature or other quantity is reached, and then some discrete activity is executed.
  We prove a few simple properties about this operator. *}

lemma hPreempt_false:
  "P is R1 \<Longrightarrow> P [false]\<^sub>h Q = P"
  by (simp add: hPreempt_def usubst alpha hInt_true, rel_auto)

lemma hPreempt_true:
  "P [true]\<^sub>h Q = Q"
  by (simp add: hPreempt_def usubst alpha hInt_false, rel_auto)
  
lemma at_left_from_zero:
  "n > 0 \<Longrightarrow> at_left n = at n within {0::real ..< n}"
  by (rule at_within_nhd[of _ "{0<..<n+1}"], auto)
  
lemma Limit_continuous: 
  assumes "x > 0" "continuous_on {0..x::real} f"
  shows "Lim (at x within {0..<x}) f = f(x)"
proof -
  have "(f \<longlongrightarrow> f x) (at x within {0..<x})"
    by (meson assms(1) assms(2) atLeastLessThan_subseteq_atLeastAtMost_iff continuous_on_imp_continuous_within continuous_within dual_order.refl intervalE less_imp_le)
  with assms(1) show ?thesis
    apply (rule_tac tendsto_Lim)     
    apply (auto)
    using at_left_from_zero apply force
  done
qed

lemma Limit_solve:
  assumes "x > 0" "continuous_on {0..x::real} g" "\<forall> x\<in>{0..<x}. f x = g x"
  shows "Lim (at x within {0..<x}) f = g(x)"
proof -
  from assms have "Lim (at x within {0..<x}) f = Lim (at x within {0..<x}) g"
    apply (simp add: Topological_Spaces.Lim_def)
    apply (rule cong[of The], auto simp add:)
    apply (clarsimp simp add: fun_eq_iff)
    apply (rule Lim_cong_within)
    apply (auto)
  done
  also have "... = g(x)"
    using Limit_continuous assms(1) assms(2) by blast  
  finally show ?thesis .
qed

lemma Limit_solve_at_left:
  assumes "x > 0" "continuous_on {0..x::real} g" "\<forall> x\<in>{0..<x}. f x = g x"
  shows "Lim (at_left x) f = g(x)"
  by (simp add: Limit_solve assms(1) assms(2) assms(3) at_left_from_zero)

lemma Lim_continuous_lens:
  fixes x :: "'a::t2_space \<Longrightarrow> 'c::t2_space"
  assumes "T > 0" "vwb_lens x" "continuous_on UNIV get\<^bsub>x\<^esub>" 
          "continuous_on {0..end\<^sub>t(T)} f" 
          "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t(T) \<longrightarrow> get\<^bsub>x\<^esub> (\<langle>T\<rangle>\<^sub>t t) = f t"
  shows "get\<^bsub>x\<^esub> (Lim (at_left (end\<^sub>t T)) \<langle>T\<rangle>\<^sub>t) = f (end\<^sub>t T)"
proof -
  let ?l = "end\<^sub>t T"

  have lnz: "end\<^sub>t(T) > 0"
    by (metis assms(1) trace_class.diff_zero tt_end_gr_zero_iff)
    
  obtain L where L:"(\<langle>T\<rangle>\<^sub>t \<longlongrightarrow> L) (at_left ?l)"
    by (metis assms(1) trace_class.diff_zero tt_end_gr_zero_iff ttrace_convergent_end)

  from L have gL: "((get\<^bsub>x\<^esub> \<circ> \<langle>T\<rangle>\<^sub>t) \<longlongrightarrow> get\<^bsub>x\<^esub> L) (at_left ?l)"
    by (simp add: comp_def, rule_tac continuous_on_tendsto_compose[of UNIV "get\<^bsub>x\<^esub>"], simp_all add: assms)
      
  moreover have "((get\<^bsub>x\<^esub> \<circ> \<langle>T\<rangle>\<^sub>t) \<longlongrightarrow> get\<^bsub>x\<^esub> L) (at_left ?l)
                 \<longleftrightarrow>
                 (f \<longlongrightarrow> get\<^bsub>x\<^esub> L) (at_left ?l)"
    using assms by (simp add: at_left_from_zero lnz, rule_tac Lim_cong_within, auto)
      
  moreover have "(f \<longlongrightarrow> f ?l) (at_left ?l)"
    using assms(4)
    by (auto simp add: continuous_on at_left_from_zero lnz, meson atLeastAtMost_iff atLeastLessThan_subseteq_atLeastAtMost_iff order_refl tendsto_within_subset tt_end_ge_0)
      
  ultimately have gL: "get\<^bsub>x\<^esub> L = f (end\<^sub>t (T))"
    by (metis tendsto_Lim trivial_limit_at_left_real)
      
  thus ?thesis
    using L tendsto_Lim trivial_limit_at_left_real by blast
qed
  
lemma hUntil_false [rpred]:
  "P inv b(ti) until\<^sub>h false = false"
  by (simp add: hUntil_def alpha)
  
lemma hUntil_expand_lemma:
  "P until\<^sub>h b(ti) = (P \<and> \<lceil>\<not> b ti\<rceil>\<^sub>h \<and> $tr <\<^sub>u $tr\<acute> \<and> $st:\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(t \<rightarrow> \<^bold>l\<^sup>-)(&tt(\<guillemotleft>t\<guillemotright>)\<^sub>a) \<and> (\<^bold>\<exists> l \<bullet> \<guillemotleft>l\<guillemotright> =\<^sub>u \<^bold>l \<and> \<lceil>b l\<rceil>\<^sub>C) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d)"
  by (rel_auto)
  
lemma hUntil_subst_init_cont [usubst]:
  "\<lbrakk> $tr \<sharp> \<sigma>; out\<alpha> \<sharp> \<sigma>; $st:\<^bold>c \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<sigma>($st:\<^bold>c:x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> (P until\<^sub>h b(ti)) = \<sigma> \<dagger> (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$st:\<^bold>c:x\<rbrakk> until\<^sub>h b(ti)\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  by (simp add: hUntil_expand_lemma usubst unrest)
  
lemma hUntil_RR_closed [closure]:
  assumes "P is RR"
  shows "P inv b(ti) until\<^sub>h c(ti) is RR"
proof -
  have "RR (RR(P) inv b(ti) until\<^sub>h c(ti)) = RR(P) inv b(ti) until\<^sub>h c(ti)"
    by (rel_auto)
  with assms show ?thesis
    by (simp add: Healthy_def)
qed

lemma hUntil_lemma1:
  fixes tr tr' :: "'a::topological_space ttrace"
  assumes
    "vwb_lens x" "k > 0" "tr < tr'"
    "\<forall>t\<in>{0..<k}. \<forall>a b. \<not> \<lbrakk>c\<rbrakk>\<^sub>e (a, put\<^bsub>x\<^esub> b (f t))"
    "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr'-tr) \<longrightarrow> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) = f t"
    "0 \<le> t" "t < end\<^sub>t(tr'-tr)" "end\<^sub>t(tr'-tr) \<le> k"
  shows 
    "\<not> \<lbrakk>c\<rbrakk>\<^sub>e (a, \<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr))"
  using assms
  apply (drule_tac x="t" in bspec, simp)
  apply (drule_tac x="t" in spec)
  apply (metis assms(1) vwb_lens.put_eq)
done
    
lemma hUntil_lemma2:
  fixes tr tr' :: "'a::topological_space ttrace"
  assumes
    "vwb_lens x" "k > 0" "tr < tr'"
    "\<forall>t\<in>{0..<k}. \<forall>a b. \<not> \<lbrakk>c\<rbrakk>\<^sub>e (a, put\<^bsub>x\<^esub> b (f t))"
    "\<forall>a b. \<lbrakk>c\<rbrakk>\<^sub>e (a, put\<^bsub>x\<^esub> b (f k))"
    "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr'-tr) \<longrightarrow> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) = f t"
    "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr'-tr) \<longrightarrow> \<not> \<lbrakk>c\<rbrakk>\<^sub>e (b, \<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr))"
  shows "end\<^sub>t (tr'-tr) \<le> k"
proof -
  let ?l = "end\<^sub>t (tr' - tr)"
    
  have etr_nz: "?l > 0"
    by (simp add: assms)
    
  have tr_f: "\<forall>t. 0 \<le> t \<and> t < ?l \<longrightarrow> (get\<^bsub>x\<^esub> \<circ> \<langle>tr'-tr\<rangle>\<^sub>t) t = f t"
    by (simp add: assms less_imp_le)

  show "end\<^sub>t (tr'-tr) \<le> k"
  proof (rule ccontr)
    assume less: "\<not> end\<^sub>t (tr' - tr) \<le> k"
    with assms have 1:"\<not> \<lbrakk>c\<rbrakk>\<^sub>e (b, \<langle>tr' - tr\<rangle>\<^sub>t k)"
      by (auto)
    from assms tr_f less have "get\<^bsub>x\<^esub> (\<langle>tr' - tr\<rangle>\<^sub>t k) = f k"
      by auto
    with assms have 2:"\<lbrakk>c\<rbrakk>\<^sub>e (b, \<langle>tr' - tr\<rangle>\<^sub>t k)"
      apply (drule_tac x="b" in spec)
      apply (drule_tac x="\<langle>tr' - tr\<rangle>\<^sub>t k" in spec)
      apply (metis vwb_lens.put_eq)
    done
    from 1 2 show False
      by blast
  qed      
qed  

lemma hUntil_lemma3:
  fixes tr tr' :: "'a::t2_space ttrace"
  and x :: "'c::t2_space \<Longrightarrow> 'a::t2_space"
  assumes
    "vwb_lens x" "k > 0" "tr < tr'"
    "continuous_on {0..k} f" "continuous_on UNIV get\<^bsub>x\<^esub>"
    "\<forall>t\<in>{0..<k}. \<forall>a b. \<not> \<lbrakk>c\<rbrakk>\<^sub>e (a, put\<^bsub>x\<^esub> b (f t))"
    "\<forall>a b. \<lbrakk>c\<rbrakk>\<^sub>e (a, put\<^bsub>x\<^esub> b (f k))"
    "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr'-tr) \<longrightarrow> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) = f t"
    "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr'-tr) \<longrightarrow> \<not> \<lbrakk>c\<rbrakk>\<^sub>e (b, \<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr))"
    "\<lbrakk>c\<rbrakk>\<^sub>e (b, Lim (at_left (end\<^sub>t (tr'-tr))) \<langle>tr'-tr\<rangle>\<^sub>t)"
  shows "end\<^sub>t (tr'-tr) = k"
proof -
  let ?l = "end\<^sub>t (tr' - tr)"

  have tr_f: "\<forall>t. 0 \<le> t \<and> t < ?l \<longrightarrow> (get\<^bsub>x\<^esub> \<circ> \<langle>tr'-tr\<rangle>\<^sub>t) t = f t"
    by (simp add: assms less_imp_le)
    
  have k:"end\<^sub>t (tr'-tr) \<le> k"
    by (rule hUntil_lemma2[of x k tr tr' c f b], simp_all add: assms)
      
  have gL: "get\<^bsub>x\<^esub> (Lim (at_left ?l) \<langle>tr'-tr\<rangle>\<^sub>t) = f (end\<^sub>t (tr' - tr))"
    using assms tr_f k 
    by (rule_tac Lim_continuous_lens, auto simp add: continuous_on_subset)

  show "end\<^sub>t (tr'-tr) = k"
  proof (cases k "end\<^sub>t (tr'-tr)" rule:linorder_cases)
    case less show ?thesis
      using k less by auto
  next
    case equal
    then show ?thesis by simp
  next
    case greater
    with assms have "\<not> \<lbrakk>c\<rbrakk>\<^sub>e (b, put\<^bsub>x\<^esub> (Lim (at_left ?l) \<langle>tr'-tr\<rangle>\<^sub>t) (f ?l))"
      by simp
    then show ?thesis
      using assms(10) assms(1) gL vwb_lens.put_eq by force 
  qed
qed

lemma hUntil_lemma4:
  fixes tr tr' b
  and x :: "'c::t2_space \<Longrightarrow> 'a::t2_space"    
  assumes
    "vwb_lens x" "k > 0" "continuous_on {0..k} f" "continuous_on UNIV get\<^bsub>x\<^esub>"
    "\<forall>t\<in>{0..<end\<^sub>t (tr' - tr)}. \<forall>a b. \<not> \<lbrakk>c\<rbrakk>\<^sub>e (a, put\<^bsub>x\<^esub> b (f t))"
    "\<forall>a b. \<lbrakk>c\<rbrakk>\<^sub>e (a, put\<^bsub>x\<^esub> b (f (end\<^sub>t (tr'-tr))))"
    "\<forall>xa. 0 \<le> xa \<and> xa < end\<^sub>t (tr'-tr) \<longrightarrow> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(xa + end\<^sub>t tr)) = f xa"
    "tr < tr'"
    "k = end\<^sub>t (tr'-tr)"
  shows "\<lbrakk>c\<rbrakk>\<^sub>e (b, Lim (at_left (end\<^sub>t (tr' - tr))) \<langle>tr'-tr\<rangle>\<^sub>t)"  
proof -
  let ?l = "end\<^sub>t (tr' - tr)"
    
  have etr_nz: "?l > 0"
    by (simp add: assms)
    
  have tr_f: "\<forall>t. 0 \<le> t \<and> t < ?l \<longrightarrow> (get\<^bsub>x\<^esub> \<circ> \<langle>tr'-tr\<rangle>\<^sub>t) t = f t"
    by (simp add: assms less_imp_le)
      
  have gL: "get\<^bsub>x\<^esub> (Lim (at_left ?l) \<langle>tr'-tr\<rangle>\<^sub>t) = f ?l"
    using assms(1-4) assms tr_f 
    by (rule_tac Lim_continuous_lens, auto simp add: continuous_on_subset)
    
  have c: "\<lbrakk>c\<rbrakk>\<^sub>e (b, put\<^bsub>x\<^esub> (Lim (at_left ?l) \<langle>tr'-tr\<rangle>\<^sub>t) (f (end\<^sub>t (tr'-tr))))"
    by (simp add: assms)
    
  show "\<lbrakk>c\<rbrakk>\<^sub>e (b, Lim (at_left ?l) \<langle>tr'-tr\<rangle>\<^sub>t)"
    using assms(1) c gL vwb_lens.put_eq by fastforce    
qed
    
text {* The following theorem can be used to ascertain the bounds on when a hybrid evolution can
  terminate. We require two time instants, $k$ and $l$, such that $k \le l$. Up until $l$, the 
  invariant of the evolution ($b$) holds, but it becomes false at this point. Up until $k$,
  condition $c$ does not hold, but it becomes true and stays true from $k$ through to $l$. Thus,
  the evolution can terminate at any point between $k$ and $l$. *}
  
theorem hUntil_inv_solve:
  assumes 
    "vwb_lens x" "0 < k" "k \<le> l" "continuous_on {0..l} f" "continuous_on UNIV get\<^bsub>x\<^esub>"
    "\<forall> t \<in> {0..<l}. b\<lbrakk>\<guillemotleft>f(t)\<guillemotright>/$x\<acute>\<rbrakk> = true" "b\<lbrakk>\<guillemotleft>f(l)\<guillemotright>/$x\<acute>\<rbrakk> = false"
    "\<forall> t \<in> {0..<k}. c\<lbrakk>\<guillemotleft>f(t)\<guillemotright>/$x\<acute>\<rbrakk> = false" "\<forall> t \<in> {k..l}. c\<lbrakk>\<guillemotleft>f(t)\<guillemotright>/$x\<acute>\<rbrakk> = true"
  shows "(x \<leftarrow>\<^sub>h \<guillemotleft>f(ti)\<guillemotright>) inv b until\<^sub>h c = x \<leftarrow>[\<guillemotleft>k\<guillemotright>,\<guillemotleft>l\<guillemotright>]\<^sub>h \<guillemotleft>f(ti)\<guillemotright>"
proof -
  from assms(6-9) 
  have a: 
    "\<forall>t\<in>{0..<l}. \<forall>s s'. \<lbrakk>b\<rbrakk>\<^sub>e (s, put\<^bsub>x\<^esub> s' (f t))"
    "\<forall>s s'. \<not> \<lbrakk>b\<rbrakk>\<^sub>e (s, put\<^bsub>x\<^esub> s' (f l))"
    "\<forall>t\<in>{0..<k}. \<forall>s s'. \<not> \<lbrakk>c\<rbrakk>\<^sub>e (s, put\<^bsub>x\<^esub> s' (f t))"
    "\<forall>t\<in>{k..l}. \<forall>s s'. \<lbrakk>c\<rbrakk>\<^sub>e (s, put\<^bsub>x\<^esub> s' (f t))"
    by (rel_auto)+
  show ?thesis
  proof (rule antisym)
    show "x \<leftarrow>[\<guillemotleft>k\<guillemotright>,\<guillemotleft>l\<guillemotright>]\<^sub>h \<guillemotleft>f ti\<guillemotright> \<sqsubseteq> (x \<leftarrow>\<^sub>h \<guillemotleft>f ti\<guillemotright>) inv b until\<^sub>h c"
    proof (rel_simp)
      fix tr tr' s
      assume b:
        "tr < tr'"
        "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t (t + end\<^sub>t tr)) = f t"
        "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow> \<lbrakk>b\<rbrakk>\<^sub>e (s, \<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr))"
        "\<lbrakk>c\<rbrakk>\<^sub>e (s, Lim (at_left (end\<^sub>t (tr' - tr))) \<langle>tr' - tr\<rangle>\<^sub>t)"
      let ?l = "end\<^sub>t (tr' - tr)"
    
      have etr_nz: "?l > 0"
        by (simp add: b)
    
      have tr_f: "\<forall>t. 0 \<le> t \<and> t < ?l \<longrightarrow> (get\<^bsub>x\<^esub> \<circ> \<langle>tr'-tr\<rangle>\<^sub>t) t = f t"
        by (simp add: b less_imp_le)          
          
      show "k \<le> end\<^sub>t (tr' - tr) \<and> end\<^sub>t (tr' - tr) \<le> l"
      proof
        show l: "end\<^sub>t (tr' - tr) \<le> l"
        proof (rule ccontr)
          assume less: "\<not> end\<^sub>t (tr' - tr) \<le> l"
          with assms(2,3) b(1,3) have 1:"\<lbrakk>b\<rbrakk>\<^sub>e (s, \<langle>tr' - tr\<rangle>\<^sub>t l)"
            by (auto)
          from assms(2,3) tr_f less have "get\<^bsub>x\<^esub> (\<langle>tr' - tr\<rangle>\<^sub>t l) = f l"
            by auto
          with a(2) have 2:"\<not> \<lbrakk>b\<rbrakk>\<^sub>e (s, \<langle>tr' - tr\<rangle>\<^sub>t l)"
            apply (drule_tac x="s" in spec)
            apply (drule_tac x="\<langle>tr' - tr\<rangle>\<^sub>t l" in spec)
            using assms(1) vwb_lens.put_eq apply fastforce
          done
          from 1 2 show False
            by blast
        qed
        have gL: "get\<^bsub>x\<^esub> (Lim (at_left ?l) \<langle>tr'-tr\<rangle>\<^sub>t) = f (end\<^sub>t (tr' - tr))"
          using assms(1-5) b(1) tr_f l
          by (rule_tac Lim_continuous_lens, auto simp add: continuous_on_subset)
        show "k \<le> end\<^sub>t (tr' - tr)"
        proof (rule ccontr)
          assume "\<not> k \<le> end\<^sub>t (tr' - tr)"
          hence "\<not> \<lbrakk>c\<rbrakk>\<^sub>e (s, put\<^bsub>x\<^esub> (Lim (at_left ?l) \<langle>tr' - tr\<rangle>\<^sub>t) (f ?l))"
            using a(3) by auto
          moreover have "\<lbrakk>c\<rbrakk>\<^sub>e (s, put\<^bsub>x\<^esub> (Lim (at_left ?l) \<langle>tr' - tr\<rangle>\<^sub>t) (f ?l))"
            using assms(1) b(4) gL vwb_lens.put_eq by fastforce
          ultimately show False
            by blast
        qed
      qed
    qed
    show "(x \<leftarrow>\<^sub>h \<guillemotleft>f ti\<guillemotright>) inv b until\<^sub>h c \<sqsubseteq> x \<leftarrow>[\<guillemotleft>k\<guillemotright>,\<guillemotleft>l\<guillemotright>]\<^sub>h \<guillemotleft>f ti\<guillemotright>"
    proof (rel_simp)
      fix tr tr' s\<^sub>0 s\<^sub>1
      assume b: 
        "tr < tr'"
        "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) = f t"
        "k \<le> end\<^sub>t (tr' - tr)"
        "end\<^sub>t (tr' - tr) \<le> l"
      show "(\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow> \<lbrakk>b\<rbrakk>\<^sub>e (s\<^sub>0, \<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr))) \<and>
            (\<lbrakk>c\<rbrakk>\<^sub>e (s\<^sub>0, Lim (at_left (end\<^sub>t (tr' - tr))) \<langle>tr' - tr\<rangle>\<^sub>t))"
      proof (safe)
        fix t
        assume c: "0 \<le> t" "t < end\<^sub>t (tr' - tr)"
        show "\<lbrakk>b\<rbrakk>\<^sub>e (s\<^sub>0, \<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr))"
        proof -
          have "\<lbrakk>b\<rbrakk>\<^sub>e (s\<^sub>0, put\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) (f t))"
            using c a(1) b(4) by auto
          moreover have "get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) = f t"
            by (simp add: b(2) c(1) c(2))
          ultimately show ?thesis
            by (metis assms(1) vwb_lens.put_eq) 
        qed
      next
        have c:"\<lbrakk>c\<rbrakk>\<^sub>e (s\<^sub>0, put\<^bsub>x\<^esub> (Lim (at_left (end\<^sub>t (tr' - tr))) \<langle>tr' - tr\<rangle>\<^sub>t) (f (end\<^sub>t (tr' - tr))))"
          by (simp add: a(4) b(3) b(4))
        have tr_f: "\<forall>t. 0 \<le> t \<and> t < (end\<^sub>t (tr' - tr)) \<longrightarrow> (get\<^bsub>x\<^esub> \<circ> \<langle>tr'-tr\<rangle>\<^sub>t) t = f t"
          by (metis (no_types, hide_lams) approximation_preproc_push_neg(2) b(2) comp_apply not_le_minus tt_apply_minus tt_end_empty)
        have gL: "get\<^bsub>x\<^esub> (Lim (at_left (end\<^sub>t (tr' - tr))) \<langle>tr'-tr\<rangle>\<^sub>t) = f (end\<^sub>t (tr' - tr))"
          using assms(1-5) b(1) tr_f b(4)
          by (rule_tac Lim_continuous_lens, auto simp add: continuous_on_subset)   
        hence "put\<^bsub>x\<^esub> (Lim (at_left (end\<^sub>t (tr' - tr))) \<langle>tr' - tr\<rangle>\<^sub>t) (f (end\<^sub>t (tr' - tr))) =(Lim (at_left (end\<^sub>t (tr' - tr))) \<langle>tr' - tr\<rangle>\<^sub>t)"
          using assms(1) vwb_lens.put_eq by force            
        with c show "\<lbrakk>c\<rbrakk>\<^sub>e (s\<^sub>0, Lim (at_left (end\<^sub>t (tr' - tr))) \<langle>tr' - tr\<rangle>\<^sub>t)"
          by (simp)
      qed
    qed
  qed
qed
        
lemma hUntil_solve:
  assumes 
    "vwb_lens x" "k > 0" "continuous_on {0..k} f" "continuous_on UNIV get\<^bsub>x\<^esub>"
    "\<forall> t \<in> {0..<k}. c\<lbrakk>\<guillemotleft>f(t)\<guillemotright>/$x\<acute>\<rbrakk> = false" "c\<lbrakk>\<guillemotleft>f(k)\<guillemotright>/$x\<acute>\<rbrakk> = true"
  shows "(x \<leftarrow>\<^sub>h \<guillemotleft>f(ti)\<guillemotright>) until\<^sub>h c = x \<leftarrow>\<^sub>h(\<guillemotleft>k\<guillemotright>) \<guillemotleft>f(ti)\<guillemotright>"
  using assms
  by (rule_tac hUntil_inv_solve, simp_all, (rel_auto)+)
    
definition hyrel2trel :: "(unit, 'c::t2_space) hyrel \<Rightarrow> 'c trel" ("H2T'(_')") where
[upred_defs]: "hyrel2trel P = R1(\<^bold>\<exists> l \<bullet> ((P \<and> \<^bold>l =\<^sub>u \<guillemotleft>l\<guillemotright> \<and> rl(&\<^bold>v) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d) \<restriction>\<^sub>r (&st:\<^bold>c)) \<oplus>\<^sub>r st \<and> &tt =\<^sub>u \<guillemotleft>mk_pos(l)\<guillemotright>)"

lemma hyrel2trel_skip: "H2T(II\<^sub>r) = II\<^sub>r"
  apply (rel_auto)
  using minus_zero_eq apply blast
  using minus_zero_eq apply blast
  apply fastforce
done

definition hyrel_assign :: "'c::t2_space usubst \<Rightarrow> ('d, 'c) hyrel" ("\<langle>_\<rangle>\<^sub>h") where
[upred_defs]: "hyrel_assign \<sigma> = rea_assigns (\<sigma> \<oplus>\<^sub>s \<^bold>c)"
 
abbreviation hyrel_cond :: 
  "('d, 'c::t2_space) hyrel \<Rightarrow> 'c upred \<Rightarrow> ('d, 'c) hyrel \<Rightarrow> ('d, 'c) hyrel" ("(3_ \<triangleleft> _ \<triangleright>\<^sub>h/ _)" [52,0,53] 52) where
"hyrel_cond P b Q \<equiv> (P \<triangleleft> b \<oplus>\<^sub>p \<^bold>c \<triangleright>\<^sub>R Q)"

lemma hyrel2trl_cond: "H2T(P \<triangleleft> b \<triangleright>\<^sub>h Q) = H2T(P) \<triangleleft> b \<triangleright>\<^sub>R H2T(Q)"
  by (rel_auto)

lemma hyrel2trel_assigns: "H2T(\<langle>\<sigma>\<rangle>\<^sub>h) = \<langle>\<sigma>\<rangle>\<^sub>r"
  apply (rel_auto)
  using minus_zero_eq apply blast
  using minus_zero_eq apply blast
  apply fastforce
done

lemma hyrel2trel_hEvolve:
  fixes x :: "'a::t2_space \<Longrightarrow> 'c::t2_space"
  assumes "continuous_on {0..} f"
  shows "H2T(&\<^bold>v \<leftarrow>\<^sub>h \<guillemotleft>f(ti)\<guillemotright>  :: (unit,'c) hyrel) = 
         (\<Sqinter> t | \<guillemotleft>t\<guillemotright> >\<^sub>u 0 \<bullet> wait\<^sub>r(\<guillemotleft>t\<guillemotright>) ;; \<^bold>v :=\<^sub>r \<guillemotleft>f(real_of_pos t)\<guillemotright>)" (is "?lhs = ?rhs")
proof -
  from assms(1) 
  have "?lhs = R1(\<^bold>\<exists> l \<bullet> (&\<^bold>v \<leftarrow>\<^sub>h \<guillemotleft>f ti\<guillemotright> \<and> end\<^sub>u(&tt) =\<^sub>u \<guillemotleft>l\<guillemotright> \<and> rl(&\<^bold>v) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d :: (unit,'c) hyrel) \<restriction>\<^sub>r &st:\<^bold>c \<oplus>\<^sub>r st \<and> &tt =\<^sub>u \<guillemotleft>mk_pos l\<guillemotright>)"
    by (simp add: hyrel2trel_def)
  also have "... = R1(\<^bold>\<exists> l \<bullet> (&\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright> :: (unit,'c) hyrel) \<restriction>\<^sub>r &st:\<^bold>c \<oplus>\<^sub>r st \<and> &tt =\<^sub>u \<guillemotleft>mk_pos l\<guillemotright>)"
    by (rel_auto, blast)
  also have "... = R1(\<^bold>\<exists> l \<bullet> ((\<^bold>v := \<guillemotleft>f(l)\<guillemotright>) \<oplus>\<^sub>r st) \<and> \<guillemotleft>l\<guillemotright> >\<^sub>u 0 \<and> &tt =\<^sub>u \<guillemotleft>mk_pos l\<guillemotright>)" (is "?P = ?Q")
  proof (rule antisym)
    show "?P \<sqsubseteq> ?Q"
      apply (rel_simp)
      apply (rename_tac tr tr' n)
      apply (rule_tac x="n" in exI)
      apply (auto)
      apply (rule_tac x="0" in exI)
      apply (rule_tac x="tt_mk n f" in exI)
      apply (subgoal_tac "continuous_on {0..n} f")
       apply (auto simp add: assms Limit_solve at_left_from_zero)
      apply (meson Icc_subset_Ici_iff assms continuous_on_subset order_refl)
    done
    show "?Q \<sqsubseteq> ?P"
      apply (rel_simp)
      apply (rename_tac tr tr' tr'' tr''')
      apply (rule_tac x="end\<^sub>t (tr''' - tr'')" in exI)
      apply (auto)
      apply (subgoal_tac "continuous_on {0..end\<^sub>t (tr''' - tr'')} f")
       apply (subst Limit_solve_at_left)
          apply (auto)
      apply (meson Icc_subset_Ici_iff assms continuous_on_subset order_refl)
    done
  qed
  also have "... = ?rhs"
    apply (rel_auto)
     apply (rename_tac tr tr' x)
     apply (rule_tac x="mk_pos x" in exI)
     apply (simp)
     apply (subgoal_tac "mk_pos x > 0")
    apply (metis le_add_diff_inverse)
    using mk_pos_less apply force
    apply (rule_tac x="(real_of_pos x)" in exI)
    apply (simp add: Rep_pos_inverse less_pos.rep_eq mk_pos.abs_eq real_of_pos.rep_eq zero_pos.rep_eq)
  done
  finally show ?thesis .
qed
  
subsection {* Stepping a Hybrid Relation Forward *}
  
definition hStepRel :: "real \<Rightarrow> ('d, 'c::t2_space) hyrel \<Rightarrow> 'c hrel" ("HyStep[_]'(_')") where
[upred_defs]: "hStepRel t P = ((((P \<and> \<^bold>l =\<^sub>u \<guillemotleft>t\<guillemotright> \<and> rl(&\<^bold>v) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d) \<restriction>\<^sub>v (&st:\<^bold>c \<times> &st:\<^bold>c)) \<restriction>\<^sub>p ((\<^bold>c ;\<^sub>L st) \<times>\<^sub>L (\<^bold>c ;\<^sub>L st))) \<triangleleft> \<guillemotleft>t\<guillemotright> >\<^sub>u 0 \<triangleright>\<^sub>r II)"
  
lemma HyStep_hEvolve:
  fixes x :: "'a::t2_space \<Longrightarrow> 'c::t2_space"
  assumes "n > 0" "continuous_on {0..n} f"
  shows "HyStep[n](&\<^bold>v \<leftarrow>\<^sub>h \<guillemotleft>f(ti)\<guillemotright>  :: ('d,'c) hyrel) = (\<^bold>v := \<guillemotleft>f(n)\<guillemotright>)" (is "?lhs = ?rhs")
proof -
  from assms(1) have "?lhs = \<lfloor>(&\<^bold>v \<leftarrow>\<^sub>h \<guillemotleft>f ti\<guillemotright> \<and> \<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> rl(&\<^bold>v) :: ('d,'c) hyrel) \<restriction>\<^sub>v (&st:\<^bold>c \<times> &st:\<^bold>c)\<rfloor>\<^sub>C"
    by (simp add: hStepRel_def, rel_auto)
  also have "... = \<lfloor>(&\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>n\<guillemotright>) \<guillemotleft>f ti\<guillemotright> :: ('d,'c) hyrel) \<restriction>\<^sub>v (&st:\<^bold>c \<times> &st:\<^bold>c)\<rfloor>\<^sub>C"
    by (rel_auto, blast)  
  also have "... = ?rhs"
  proof (rel_auto)
    fix tr tr'
    assume "n = end\<^sub>t (tr' - tr)" "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) = f t" "tr < tr'"
    with assms have "get\<^bsub>\<Sigma>\<^esub> (Lim (at_left (end\<^sub>t (tr' - tr))) (\<langle>tr' - tr\<rangle>\<^sub>t)) = f (end\<^sub>t (tr' - tr))"
      by (rule_tac Lim_continuous_lens, simp_all, simp add: lens_defs)
    thus "(Lim (at_left (end\<^sub>t (tr' - tr))) (\<langle>tr' - tr\<rangle>\<^sub>t)) = f (end\<^sub>t (tr' - tr))"
      by (simp add: lens_defs)
  next
    from assms
    show "(\<exists>tr tr'.
           (tr < tr' \<longrightarrow>
            tr \<le> tr' \<and>
            (\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow> (\<langle>tr'\<rangle>\<^sub>t (t + end\<^sub>t tr)) = f t) \<and>
            n \<le> end\<^sub>t (tr' - tr) \<and> end\<^sub>t (tr' - tr) \<le> n \<and> tr \<le> tr' \<and> f n = Lim (at_left (end\<^sub>t (tr' - tr))) \<langle>tr' - tr\<rangle>\<^sub>t) \<and>
           tr < tr')"
      by (rule_tac x="[]\<^sub>t" in exI, rule_tac x="mk\<^sub>t n f" in exI)
         (auto simp add: Limit_solve at_left_from_zero)
  qed
  finally show ?thesis .
qed
  
lemma HyStep_hEvolveAt:
  fixes P :: "('d,'c :: t2_space) hyrel"
  assumes "0 < m" "m \<le> n" "continuous_on {0..n} f"
  shows "HyStep[n](&\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>m\<guillemotright>) \<guillemotleft>f(ti)\<guillemotright> ;; RR(P)) = ($\<^bold>v\<acute> =\<^sub>u \<guillemotleft>f(m)\<guillemotright>) ;; HyStep[n-m](RR(P))" (is "?lhs = ?rhs")
  oops
    
subsection {* Pertubation *}
    
abbreviation (input) "lens_upd s k v \<equiv> lens_put k s v"

adhoc_overloading
  uupd lens_upd
 
text {* The following function take a hybrid relation and makes it more non-deterministic by allowing
  that each continuous variable need only be within eps of its original value at each instant. *}
  
definition perturb :: "('d, 'c :: t2_space) hyrel \<Rightarrow> ('a :: metric_space \<Longrightarrow> 'c) \<Rightarrow> real \<Rightarrow> ('d, 'c) hyrel"
  where [upred_defs]:
  "perturb P x eps = 
  P \<triangleleft> \<guillemotleft>eps\<guillemotright> \<le>\<^sub>u 0 \<triangleright>
  (\<^bold>\<exists> f \<bullet> P\<lbrakk>\<guillemotleft>f\<guillemotright>/&tt\<rbrakk> \<and> $tr \<le>\<^sub>u $tr\<acute> \<and>  \<^bold>l =\<^sub>u end\<^sub>u(\<guillemotleft>f\<guillemotright>) \<and> 
       (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>f\<guillemotright>)}\<^sub>u \<bullet> \<^bold>\<exists> v \<bullet> \<guillemotleft>dist\<guillemotright>(\<guillemotleft>f\<guillemotright>(\<guillemotleft>t\<guillemotright>)\<^sub>a:(x))\<^sub>a(\<guillemotleft>v\<guillemotright>)\<^sub>a <\<^sub>u \<guillemotleft>eps\<guillemotright> \<and> 
                                       &tt(\<guillemotleft>t\<guillemotright>)\<^sub>a =\<^sub>u (\<guillemotleft>f\<guillemotright>(\<guillemotleft>t\<guillemotright>)\<^sub>a)(\<guillemotleft>x\<guillemotright> \<mapsto> \<guillemotleft>v\<guillemotright>)\<^sub>u))"
  
lemma perturb_RR_closed [closure]:
  assumes "P is RR"
  shows "perturb P x n is RR"
proof -
  have "RR (perturb (RR P) x n) = perturb (RR P) x n"
    by (rel_blast)
  thus ?thesis
    by (metis Healthy_def assms)
qed
    
lemma perturb_0:
  "perturb P x 0 = P"
  by (rel_auto)
  
lemma perturb_weakens:
  assumes "vwb_lens x" "n \<ge> 0" "P is RR"
  shows "perturb P x n \<sqsubseteq> P"
proof -
  from assms(1,2) have "perturb (RR P) x n \<sqsubseteq> (RR P)"
    apply (rel_simp)
    apply (rename_tac tr d c tr' d' c' ok ok' wait wait')
    apply (rule_tac x="tr' - tr" in exI)
    apply (auto)
    apply (rename_tac tr d c tr' d' c' ok ok' wait wait' t)    
    apply (rule_tac x="get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr))" in exI)
    apply (auto)
  done
  thus ?thesis
    by (simp add: assms Healthy_if)
qed

  
(*
lemma tt_apply_continuous:
  "continuous_on {0..<end\<^sub>t(f)} \<langle>f\<rangle>\<^sub>t"
  sorry
  
lemma tt_apply_mk [simp]: 
  "\<lbrakk> 0 \<le> t; t < l; continuous_on {0..<l} f \<rbrakk> \<Longrightarrow> \<langle>mk\<^sub>t l f\<rangle>\<^sub>t t = f t"
  sorry
    
lemma 
  fixes x :: "real \<Longrightarrow> 'c::t2_space"
  assumes "continuous_lens x"
  shows "perturb \<lceil>$x\<acute> =\<^sub>u 0\<rceil>\<^sub>h x 1 = \<lceil>-1 \<le>\<^sub>u $x\<acute> \<and> $x\<acute> \<le>\<^sub>u 1\<rceil>\<^sub>h"
proof (rule antisym)
  show "perturb \<lceil>$x\<acute> =\<^sub>u 0\<rceil>\<^sub>h x 1 \<sqsubseteq> \<lceil>-1 \<le>\<^sub>u $x\<acute> \<and> $x\<acute> \<le>\<^sub>u 1\<rceil>\<^sub>h"
  proof (rel_simp)
    fix tr tr'
    assume a:
      "tr \<le> tr'"
      "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow> - 1 \<le> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) \<and> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) \<le> 1"
    have "continuous_on {0..<end\<^sub>t (tr' - tr)} (\<lambda>t. put\<^bsub>x\<^esub> (\<langle>tr'-tr\<rangle>\<^sub>t t) 0)"
      by (rule continuous_on_compose[where g="(\<lambda> s. put\<^bsub>x\<^esub> s 0)" and f="\<langle>tr'-tr\<rangle>\<^sub>t" and s="{0..<end\<^sub>t (tr' - tr)}", simplified])
         (auto simp add: tt_apply_continuous assms)
    with assms a show
      "\<exists>f. (\<forall>t. 0 \<le> t \<and> t < end\<^sub>t f \<longrightarrow> get\<^bsub>x\<^esub> (\<langle>f\<rangle>\<^sub>tt) = 0) \<and>
            end\<^sub>t (tr' - tr) = end\<^sub>t f \<and>
            (\<forall>t. 0 \<le> t \<and> t < end\<^sub>t f \<longrightarrow> (\<exists>xc. dist (get\<^bsub>x\<^esub> (\<langle>f\<rangle>\<^sub>tt)) xc \<le> 1 \<and> \<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr) = put\<^bsub>x\<^esub> (\<langle>f\<rangle>\<^sub>tt) xc))"
      apply (rule_tac x="mk\<^sub>t (end\<^sub>t(tr'-tr)) (\<lambda> t. put\<^bsub>x\<^esub> (\<langle>tr'-tr\<rangle>\<^sub>t t) 0)" in exI)
      apply (auto)
      apply (rename_tac t)
       apply (drule_tac x="t" in spec)
        apply (subst tt_apply_mk)
      apply (auto)
      apply (rule_tac x="get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr))" in exI)
      apply (simp)
    done
  qed     
  from assms show "\<lceil>-1 \<le>\<^sub>u $x\<acute> \<and> $x\<acute> \<le>\<^sub>u 1\<rceil>\<^sub>h \<sqsubseteq> perturb \<lceil>$x\<acute> =\<^sub>u 0\<rceil>\<^sub>h x 1"
    by (rel_auto)
qed
*)  

definition nearly :: "('d \<times> 'c::t2_space) upred \<Rightarrow> ('a::real_normed_vector \<Longrightarrow> 'c) \<Rightarrow> real \<Rightarrow> ('d \<times> 'c::t2_space) upred" where
[upred_defs]: "nearly p x eps = p \<triangleleft> \<guillemotleft>eps\<guillemotright> \<le>\<^sub>u 0 \<triangleright> (\<^bold>\<exists> v \<bullet> p\<lbrakk>\<guillemotleft>v\<guillemotright>/&\<^bold>c:x\<rbrakk> \<and> \<guillemotleft>dist\<guillemotright>(&\<^bold>c:x)\<^sub>a(\<guillemotleft>v\<guillemotright>)\<^sub>a <\<^sub>u \<guillemotleft>eps\<guillemotright>)"
  
lemma nearly_weaken: 
  "\<lbrakk> vwb_lens x; eps \<ge> 0 \<rbrakk> \<Longrightarrow> `p \<Rightarrow> nearly p x eps`"
  apply (rel_simp)
  apply (metis dist_self less_eq_real_def vwb_lens.put_eq)
  done

lemma nearly_example: 
  "vwb_lens x \<Longrightarrow> nearly (&\<^bold>c:x \<ge>\<^sub>u \<guillemotleft>0::real\<guillemotright>) x 1 = (&\<^bold>c:x >\<^sub>u -1)"
  apply (rel_auto)
   apply (rename_tac b v)
   apply (case_tac "0 \<le> get\<^bsub>x\<^esub> b")
    apply (auto)
    apply (subgoal_tac "v - get\<^bsub>x\<^esub> b < 1")
    apply linarith
   apply (simp add: dist_real_def)
  apply (case_tac "0 \<le> get\<^bsub>x\<^esub> b")
    apply (auto)
done
    
lemma nearly_false: 
  "nearly false x eps = false"
  by (rel_auto)

lemma nearly_true: 
  "nearly true x eps = true"
  by (rel_simp, metis approximation_preproc_push_neg(1) dist_self)

lemma nearly_conj:
  "nearly (p \<or> q) x eps = (nearly p x eps \<or> nearly q x eps)"
  by (rel_auto)
    
end
  