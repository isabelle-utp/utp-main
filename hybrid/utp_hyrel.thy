section {* Hybrid Relational Calculus *}

theory utp_hyrel
imports
  "../utp/utp"
  "../theories/utp_csp"
  "../theories/utp_rea_designs"
  "../contrib/Ordinary_Differential_Equations/ODE_Analysis"
  "../dynamics/Derivative_extra"
  "../dynamics/Timed_Traces"
begin recall_syntax
  
subsection {* Preliminaries *}

text {* The one lens is continuous *}
  
lemma one_lens_continuous [simp]:
  "continuous_on UNIV get\<^bsub>1\<^sub>L\<^esub>"
  by (simp add: lens_defs continuous_on_id)
  
text {* Lens summation of two continuous lenses is continuous *}
  
lemma continuous_on_plus_lens [continuous_intros]:
  "\<lbrakk> continuous_on A get\<^bsub>x\<^esub>; continuous_on A get\<^bsub>y\<^esub> \<rbrakk> \<Longrightarrow> continuous_on A get\<^bsub>x +\<^sub>L y\<^esub>"
  by (simp add: lens_defs ODE_Auxiliarities.continuous_on_Pair)
  
declare plus_vwb_lens [simp]
    
hide_type rel

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
  
abbreviation trace :: "('c::topological_space ttrace, 'd, 'c) hyexpr" ("\<^bold>t") where
"\<^bold>t \<equiv> $tr\<acute> - $tr"

text {* The syntax @{term "\<^bold>t"} refers to the part of the trace that the present process can
  contribute to. *}

abbreviation time_length :: "(real, 'd, 'c::topological_space) hyexpr" ("\<^bold>l")
  where "\<^bold>l \<equiv> uop end\<^sub>t \<^bold>t"

text {* @{term "\<^bold>l"} refers to the length of the time length of the current computation, and is
  obtained by taking length of the trace contribution. *}
  
abbreviation cvar ::
  "('a \<Longrightarrow> 'c::topological_space) \<Rightarrow> (real \<Rightarrow> 'a, 'd, 'c) hyexpr"
  ("_~" [999] 999)
where "x~ \<equiv> (\<lambda> t \<bullet> (\<^bold>t(\<guillemotleft>t\<guillemotright>)\<^sub>a:(x)))"
  
abbreviation cvar_app ::
  "('a \<Longrightarrow> 'c::topological_space) \<Rightarrow> (real, 'd, 'c) hyexpr \<Rightarrow> ('a, 'd, 'c) hyexpr"
  ("_~'(_')" [999,0] 999)
where "x~(t) \<equiv> \<^bold>t(t)\<^sub>a:(x)"
  
text {* The syntax @{term "x~(t)"} is a convenient way of refer to the value of a continuous
  variable $x$ at a particular instant $t$. *}

text {* We also set up some useful syntax to refer to the end of a continuous trace. *}

syntax
  "_uend" :: "logic \<Rightarrow> logic" ("end\<^sub>u'(_')")

translations
  "\<^bold>t" <= "CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr))"
  "x~(t)" <= "CONST uop (CONST lens_get x) (CONST bop (CONST uapply) (CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr))) t)"
  "x~" <= "CONST ulambda (\<lambda> t. CONST uop (CONST lens_get x) (CONST bop (CONST uapply) (CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr))) (CONST ulit t2)))"
  "\<^bold>l" <= "CONST uop (CONST tt_end) (CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr)))"
  "\<^bold>l" <= "CONST uop CONST tt_end \<^bold>t"
  "end\<^sub>u(t)" == "CONST uop end\<^sub>t t"
  
definition disc_alpha :: "'d \<Longrightarrow> ('d, 'c::topological_space) hybs" ("\<^bold>d") where
[lens_defs]: "disc_alpha = fst\<^sub>L ;\<^sub>L st"

definition cont_alpha :: "'c \<Longrightarrow> ('d, 'c::topological_space) hybs" ("\<^bold>c") where
[lens_defs]: "cont_alpha = snd\<^sub>L ;\<^sub>L st"

text {* We also set up some lenses to focus on the discrete and continuous parts of the state,
  which we call @{term "\<^bold>d"} and @{term "\<^bold>c"}, respectively. We then prove some of the key lens
  theorems about these. *}

lemma disc_alpha_vwb_lens [simp]: "vwb_lens \<^bold>d"
  by (simp add: comp_vwb_lens disc_alpha_def fst_vwb_lens)

lemma cont_alpha_uvar [simp]: "vwb_lens \<^bold>c"
  by (simp add: comp_vwb_lens cont_alpha_def snd_vwb_lens)

lemma cont_indep_disc [simp]: "\<^bold>c \<bowtie> \<^bold>d" "\<^bold>d \<bowtie> \<^bold>c"
   by (simp_all add: disc_alpha_def cont_alpha_def)

text {* Both lenses are very well-behaved, effectively meaning they are valid variables. Moreover
  they are also independent, @{term "\<^bold>c \<bowtie> \<^bold>d"}, meaning they refer to disjoint parts of the
  state space, as expected. We also show some similar independence theorems with some of the other
  observational variables. *}

lemma disc_indep_ok [simp]: "\<^bold>d \<bowtie> ok" "ok \<bowtie> \<^bold>d"
  by (simp_all add: disc_alpha_def lens_indep_sym)

lemma disc_indep_wait [simp]: "\<^bold>d \<bowtie> wait" "wait \<bowtie> \<^bold>d"
  by (simp_all add: disc_alpha_def lens_indep_sym)

lemma disc_indep_tr [simp]: "\<^bold>d \<bowtie> tr" "tr \<bowtie> \<^bold>d"
  by (simp_all add: disc_alpha_def lens_indep_sym)

lemma cont_indep_ok [simp]: "\<^bold>c \<bowtie> ok" "ok \<bowtie> \<^bold>c"
  by (simp_all add: cont_alpha_def lens_indep_left_ext lens_indep_sym)

lemma cont_indep_wait [simp]: "\<^bold>c \<bowtie> wait" "wait \<bowtie> \<^bold>c"
  by (simp_all add: cont_alpha_def lens_indep_left_ext lens_indep_sym)

lemma cont_indep_tr [simp]: "\<^bold>c \<bowtie> tr" "tr \<bowtie> \<^bold>c"
  by (simp_all add: cont_alpha_def lens_indep_left_ext lens_indep_sym)

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

lemma rea_var_ords [usubst]:
  "$\<^bold>c \<prec>\<^sub>v $tr" "$\<^bold>c \<prec>\<^sub>v $tr\<acute>" "$\<^bold>c\<acute> \<prec>\<^sub>v $tr" "$\<^bold>c\<acute> \<prec>\<^sub>v $tr\<acute>"
  by (simp_all add: var_name_ord_def)

text {* We next define some useful "lifting" operators. These operators effectively extend the state
  space of an expression by adding additional variables. This is useful, for instance, to lift an
  expression only on discrete variables to a hybrid expression. *}

abbreviation disc_lift :: "('a, 'd \<times> 'd) uexpr \<Rightarrow> ('a, 'd, 'c::topological_space) hyexpr" ("\<lceil>_\<rceil>\<^sub>\<delta>") where
"\<lceil>P\<rceil>\<^sub>\<delta> \<equiv> P \<oplus>\<^sub>p (\<^bold>d \<times>\<^sub>L \<^bold>d)"

abbreviation cont_lift :: "('a, 'c \<times> 'c) uexpr \<Rightarrow> ('a, 'd, 'c::topological_space) hyexpr" ("\<lceil>_\<rceil>\<^sub>C") where
"\<lceil>P\<rceil>\<^sub>C \<equiv> P \<oplus>\<^sub>p (\<^bold>c \<times>\<^sub>L \<^bold>c)"

abbreviation cont_drop :: "('a, 'd, 'c::topological_space) hyexpr \<Rightarrow> ('a, 'c \<times> 'c) uexpr" ("\<lfloor>_\<rfloor>\<^sub>C") where
"\<lfloor>P\<rfloor>\<^sub>C \<equiv> P \<restriction>\<^sub>p (\<^bold>c \<times>\<^sub>L \<^bold>c)"

abbreviation cont_pre_lift :: "('a, 'c) uexpr \<Rightarrow> ('a,'d,'c::topological_space) hyexpr" ("\<lceil>_\<rceil>\<^sub>C\<^sub><") where
"\<lceil>P\<rceil>\<^sub>C\<^sub>< \<equiv> P \<oplus>\<^sub>p (ivar \<^bold>c)"

abbreviation cont_post_lift :: "('a, 'c) uexpr \<Rightarrow> ('a,'d,'c::topological_space) hyexpr" ("\<lceil>_\<rceil>\<^sub>C\<^sub>>") where
"\<lceil>P\<rceil>\<^sub>C\<^sub>> \<equiv> P \<oplus>\<^sub>p (ovar \<^bold>c)"

abbreviation cont_pre_drop :: "('a,'d,'c::topological_space) hyexpr \<Rightarrow> ('a, 'c) uexpr" ("\<lfloor>_\<rfloor>\<^sub>C\<^sub><") where
"\<lfloor>P\<rfloor>\<^sub>C\<^sub>< \<equiv> P \<restriction>\<^sub>p (ivar \<^bold>c)"

abbreviation cont_post_drop :: "('a,'d,'c::topological_space) hyexpr \<Rightarrow> ('a, 'c) uexpr" ("\<lfloor>_\<rfloor>\<^sub>C\<^sub>>") where
"\<lfloor>P\<rfloor>\<^sub>C\<^sub>> \<equiv> P \<restriction>\<^sub>p (ovar \<^bold>c)"

translations
  "\<lceil>P\<rceil>\<^sub>C\<^sub><" <= "CONST aext P (CONST ivar CONST cont_alpha)"
  "\<lceil>P\<rceil>\<^sub>C\<^sub>>" <= "CONST aext P (CONST ovar CONST cont_alpha)"
  "\<lfloor>P\<rfloor>\<^sub>C\<^sub><" <= "CONST arestr P (CONST ivar CONST cont_alpha)"
  "\<lfloor>P\<rfloor>\<^sub>C\<^sub>>" <= "CONST arestr P (CONST ovar CONST cont_alpha)"

lemma unrest_lift_cont_subst [unrest]:
  "\<lbrakk> vwb_lens x; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> (\<lceil>P\<rceil>\<^sub>C\<^sub><)\<lbrakk>v/$\<^bold>c\<rbrakk>"
  by (rel_auto)
 
lemma lift_cont_subst [usubst]:
  "\<sigma>($\<^bold>c:x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> \<lceil>P\<rceil>\<^sub>C = \<sigma> \<dagger> (\<lceil>P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>\<rceil>\<^sub>C)"
  by (rel_simp)    

text {* @{term "\<lceil>P\<rceil>\<^sub>\<delta>"} takes an expression @{term "P"}, whose state space is the relational on
  the discrete state @{typ "'d"}, that is @{typ "'d \<times> 'd"} and lifts it into the hybrid state
  space, @{typ "('d, 'c) hybs"}. Note that following this lifting all continuous variables will
  be unconstrained -- this operator simply extends the alphabet. Similarly, @{term "\<lceil>P\<rceil>\<^sub>C"} lifts
  an expression on the relational continuous state to one on the whole hybrid state. Finally,
  @{term "\<lceil>P\<rceil>\<^sub>C\<^sub><"} lifts an expression on a scalar continuous state space @{typ "'c"} to one
  on the hybrid state. Effectively this is building a precondition, since it can only
  refer to unprimed continuous variables. *}

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
[upred_defs]: "P @\<^sub>u t = [$\<^bold>c\<acute> \<mapsto>\<^sub>s \<^bold>t(\<guillemotleft>t\<guillemotright>)\<^sub>a] \<dagger> \<lceil>P\<rceil>\<^sub>C"

text {* The expression @{term "P @\<^sub>u t"} asserts that the predicate @{term "P"} is satisfied by
  the continuous state at time instant @{term "t"}. Here, @{term "P"} is a predicate only
  on the flat continuous state. The operator is implemented by first extending the alphabet
  of @{term "P"} to include all the hybrid variables, and then substituting the continuous
  state for the continuous state at @{term "t"}, denoted by @{term "\<^bold>t(\<guillemotleft>t\<guillemotright>)\<^sub>a"}. *}

lemma R2c_at: "R2c(P @\<^sub>u t) = P @\<^sub>u t"
  by (simp add: at_def R2c_def cond_idem usubst unrest R2s_def)

lemma R2c_time_length: "R2c (\<guillemotleft>t\<guillemotright> \<in>\<^sub>u {0..<\<^bold>l}\<^sub>u) = (\<guillemotleft>t\<guillemotright> \<in>\<^sub>u {0..<\<^bold>l}\<^sub>u)"
  by (rel_auto ; simp add: tt_end_minus)

text {* @{term "P @\<^sub>u t"} always satisfies healthiness condition @{term "R2c"}, meaning that it
  is history independent -- it does not refer to the variable @{term "tr"}, and only refers
  to the contribution of the present trace contained in @{term "\<^bold>t"}. This in an important
  property of hybrid predicates, since in a sequential hybrid program @{term "P ;; Q ;; R"}
  satisfaction of @{term "R2c"} ensures that $P$, $Q$, and $R$ all refer to different parts
  of the trace and cannot interfere with each other. We can show this is also the case of
  the predicate @{term "\<guillemotleft>t\<guillemotright> \<in>\<^sub>u {0..<\<^bold>l}\<^sub>u"}, since this only refers to @{term "\<^bold>l"}, which
  denotes the length of the present computation, and does not depend on the history. *}

lemma at_unrest_cont [unrest]: "$\<^bold>c\<acute> \<sharp> (P @\<^sub>u t)"
  by (simp_all add: at_def unrest)

lemma at_unrest_dis [unrest]: "$\<^bold>d \<sharp> (P @\<^sub>u t)" "$\<^bold>d\<acute> \<sharp> (P @\<^sub>u t)"
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
  "\<sigma>($\<^bold>c:x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> (P @\<^sub>u t) = \<sigma> \<dagger> (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk> @\<^sub>u t)"
  by (rel_simp)
    
lemma at_var [simp]:
  fixes x :: "('a \<Longrightarrow> 'c::topological_space)"
  shows "$x\<acute> @\<^sub>u t = \<^bold>t(\<guillemotleft>t\<guillemotright>)\<^sub>a:(x)"
  by (pred_auto)

text {* Lemma @{thm [source] "at_var"} tells us the result of lifting a flat continuous variable
  @{term "x"}. It results in an expression which refers to that particular variable within the
  timed trace at instant @{term "t"}. *}

lemma subst_cvar_traj [usubst]: "\<langle>[$\<^bold>c \<mapsto>\<^sub>s \<^bold>t(\<guillemotleft>t\<guillemotright>)\<^sub>a]\<rangle>\<^sub>s (x ;\<^sub>L in_var \<^bold>c) = x~(\<guillemotleft>t\<guillemotright>)"
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

lemma hInt_unrest_dis [unrest]: "$\<^bold>d \<sharp> hInt P" "$\<^bold>d\<acute> \<sharp> hInt P"
  by (simp_all add: hInt_def unrest)
    
definition init_cont :: "('a \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "init_cont x = ($tr <\<^sub>u $tr\<acute> \<and> $\<^bold>c:x =\<^sub>u \<^bold>t(0)\<^sub>a:(x))"

definition final_cont :: "('a \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "final_cont x = ($tr <\<^sub>u $tr\<acute> \<and> $\<^bold>c:x\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> \<^bold>l\<^sup>-)(\<^bold>t(\<guillemotleft>x\<guillemotright>)\<^sub>a):(x))"

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
  "$ok \<sharp> rl(x)" "$ok\<acute> \<sharp> rl(x)" "$wait \<sharp> rl(x)" "$wait\<acute> \<sharp> rl(x)" "$st \<sharp> rl(x)"
  by (rel_auto)+

lemma usubst_final_cont [usubst]:
  "\<lbrakk> $tr \<sharp> \<sigma>; out\<alpha> \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> rl(x) = rl(x)"
  by (simp add: final_cont_def usubst unrest)
    
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
[upred_defs]: "hDisInt P = (hInt P \<and> \<^bold>l >\<^sub>u 0 \<and> ll(&\<Sigma>) \<and> rl(&\<Sigma>) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)"

text {* We also set up the adapted version of the interval operator, @{term "hDisInt P"}, that
  conjoins an interval specification with three predicates, which also happen to be coupling
  invariants, and yield what we might call a ``hybrid interval''. The first invariant
  states that the continuous state within the trace at instant 0 must
  correspond to the before value of the continuous state, i.e. @{term "$\<^bold>c =\<^sub>u \<^bold>t(0)\<^sub>a"}. The second
  states that the after value of the continuous state must take on the limit of the continuous
  state as the trace approaches the end value @{term "\<^bold>l"}, i.e. @{term "$\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> \<^bold>l\<^sup>-)(\<^bold>t(\<guillemotleft>x\<guillemotright>)\<^sub>a)"}.
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
  fun time_var_tr [] = Syntax.free "time"
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
  
text {* A regular interval can be written using the notation @{term "\<lceil>P(time)\<rceil>\<^sub>h"}, where $time$ is
  a free variable denoting the present time. Having the present time as a free variable means
  we can write algebraic equations that depend on time, such as @{term "\<lceil>&x =\<^sub>u 2 * \<guillemotleft>time\<guillemotright>\<rceil>\<^sub>h"} for
  example. Similarly, a hybrid interval can be written using a boldface as @{term "\<^bold>\<lceil>P(time)\<^bold>\<rceil>\<^sub>h"}. *}

lemma hInt_unrest_cont [unrest]: "$\<^bold>c\<acute> \<sharp> \<lceil>P(time)\<rceil>\<^sub>h"
  by (simp add: hInt_def unrest)

lemma st'_unrest_hInt [unrest]: 
  "$st\<acute> \<sharp> \<lceil>P(time)\<rceil>\<^sub>h"
  by (rel_auto)
    
lemma R1_hInt: "R1(\<lceil>P(time)\<rceil>\<^sub>h) = \<lceil>P(time)\<rceil>\<^sub>h"
  by (rel_auto)

lemma R2s_hInt: "R2c(\<lceil>P(time)\<rceil>\<^sub>h) = \<lceil>P(time)\<rceil>\<^sub>h"
  by (rel_auto)

lemma R2_hInt: "R2(\<lceil>P(time)\<rceil>\<^sub>h) = \<lceil>P(time)\<rceil>\<^sub>h"
  by (metis R1_R2c_is_R2 R1_hInt R2s_hInt)

lemma hInt_RR_closed [closure]: "\<lceil>P(time)\<rceil>\<^sub>h is RR"
  by (rel_auto)

text {* The following theorem demonstrates that we can use an interval specification in a reactive
  design precondition. *}
    
lemma neg_hInt_R1_true: "(\<not>\<^sub>r \<lceil>P(time)\<rceil>\<^sub>h) ;; R1(true) = (\<not>\<^sub>r \<lceil>P(time)\<rceil>\<^sub>h)"
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
    
lemma hInt_RC_closed [closure]: "\<lceil>P(time)\<rceil>\<^sub>h is RC"
  by (rule RC_intro, simp_all add: closure neg_hInt_R1_true rpred)
    
text {* Theorem @{thm [source] "hInt_unrest_cont"} states that no continuous before variable
  is fixed by the regular interval operator. This is because the regular interval operator
  does not refer to state variables but only the evolution of the trajectory. We can also
  show that the interval operator is both @{term "R1"} healthy, since the trajectory can
  only get longer, and also @{term "R2c"} healthy, since it does not refer to the history.

  We also prove some laws about intervals. *}

lemma hInt_subst_init_cont [usubst]:
  "\<sigma>($\<^bold>c:x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> \<lceil>P(time)\<rceil>\<^sub>h = \<sigma> \<dagger> \<lceil>P(time)\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>\<rceil>\<^sub>h"
  by (simp add: hInt_def usubst)
  
lemma hInt_false [rpred]: "\<lceil>false\<rceil>\<^sub>h = ($tr\<acute> =\<^sub>u $tr)"
  by (rel_auto, meson eq_iff leI minus_zero_eq tt_end_0_iff tt_end_ge_0)

lemma hInt_true [rpred]: "\<lceil>true\<rceil>\<^sub>h = true\<^sub>r"
  by (rel_auto)

lemma hInt_conj [rpred]: "\<lceil>P(time) \<and> Q(time)\<rceil>\<^sub>h = (\<lceil>P(time)\<rceil>\<^sub>h \<and> \<lceil>Q(time)\<rceil>\<^sub>h)"
  by (rel_auto)

lemma hInt_disj: "\<lceil>P(time) \<or> Q(time)\<rceil>\<^sub>h \<sqsubseteq> (\<lceil>P(time)\<rceil>\<^sub>h \<or> \<lceil>Q(time)\<rceil>\<^sub>h)"
  by (rel_auto)

lemma hInt_refine: "`\<^bold>\<forall> time \<bullet> P(time) \<Rightarrow> Q(time)` \<Longrightarrow> \<lceil>Q(time)\<rceil>\<^sub>h \<sqsubseteq> \<lceil>P(time)\<rceil>\<^sub>h"
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
  "\<lfloor>P(time)\<rfloor>\<^sub>h is RR"
  by (rel_auto)

lemma st'_unrest_hSomewhere [unrest]: 
  "$st\<acute> \<sharp> \<lfloor>P(time)\<rfloor>\<^sub>h"
  by (rel_auto)

lemma hSomewhere_false [rpred]: "\<lfloor>false\<rfloor>\<^sub>h = false"
  by (rel_auto)

lemma hSomewhere_true [rpred]: "\<lfloor>true\<rfloor>\<^sub>h = ($tr <\<^sub>u $tr\<acute>)"
  by (rel_auto)
    
lemma rea_not_hInt [rpred]:
  "(\<not>\<^sub>r \<lceil>P(time)\<rceil>\<^sub>h) = \<lfloor>\<not> P(time)\<rfloor>\<^sub>h"
  apply (rel_auto) using tt_end_gr_zero_iff by fastforce

lemma rea_not_hSomewhere [rpred]:
  "(\<not>\<^sub>r \<lfloor>P(time)\<rfloor>\<^sub>h) = \<lceil>\<not> P(time)\<rceil>\<^sub>h"
  apply (rel_auto) using tt_end_gr_zero_iff by fastforce
    
subsection {* Evolve by continuous function *}
 
definition hEvolve :: "('a::t2_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> (real \<Rightarrow> ('a, 'c) uexpr) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "hEvolve x f = (\<lceil>$x\<acute> =\<^sub>u \<lceil>f(time)\<rceil>\<^sub><\<rceil>\<^sub>h \<and> \<^bold>l >\<^sub>u 0)"

definition hEvolveBound :: "('a::t2_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> (real, 'd \<times> 'c) uexpr \<Rightarrow> (real \<Rightarrow> ('a, 'c) uexpr) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "hEvolveBound x t f = (hEvolve x f \<and> \<^bold>l \<le>\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub><)"

definition hEvolveAt :: "('a::t2_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> (real, 'd \<times> 'c) uexpr \<Rightarrow> (real \<Rightarrow> ('a, 'c) uexpr) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "hEvolveAt x t f = (hEvolve x f \<and> \<^bold>l =\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d \<and> rl(&\<Sigma>))"

syntax
  "_hEvolve"   :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_ \<leftarrow>\<^sub>h _" [90,91] 90)
  "_hEvolveBound"   :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<leftarrow>\<^sub>h\<le>'(_') _" [90,0,91] 90)
  "_hEvolveAt" :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<leftarrow>\<^sub>h'(_') _" [90,0,91] 90)  
  
translations
  "_hEvolve a f" => "CONST hEvolve a (\<lambda> _time_var. f)"
  "_hEvolve a f" <= "CONST hEvolve a (\<lambda> time. f)"
  "_hEvolveBound a t f" => "CONST hEvolveBound a t (\<lambda> _time_var. f)"
  "_hEvolveBound a t f" <= "CONST hEvolveBound a t (\<lambda> time. f)"
  "_hEvolveAt a t f" => "CONST hEvolveAt a t (\<lambda> _time_var. f)"
  "_hEvolveAt a t f" <= "CONST hEvolveAt a t (\<lambda> time. f)"

lemma hEvolve_unrests [unrest]:
  "$ok \<sharp> x \<leftarrow>\<^sub>h f(time)" "$ok\<acute> \<sharp> x \<leftarrow>\<^sub>h f(time)" "$wait \<sharp> x \<leftarrow>\<^sub>h f(time)" "$wait\<acute> \<sharp> x \<leftarrow>\<^sub>h f(time)" "$st\<acute> \<sharp> x \<leftarrow>\<^sub>h f(time)"
  by (simp_all add: hEvolve_def unrest)

lemma hEvolveBound_st'_unrest [unrest]:
  "$st\<acute> \<sharp> x \<leftarrow>\<^sub>h\<le>(n) f(time)"
  by (rel_auto)
    
lemma hEvolve_usubst [usubst]:
  "\<sigma>($\<^bold>c:x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> y \<leftarrow>\<^sub>h f(time) = \<sigma> \<dagger> y \<leftarrow>\<^sub>h ((f time)\<lbrakk>\<guillemotleft>v\<guillemotright>/&x\<rbrakk>)"
  by (simp add: hEvolve_def usubst unrest)
    
lemma hEvolve_RR_closed [closure]: "x \<leftarrow>\<^sub>h f(time) is RR"
  by (rel_auto)

lemma hEvolveBound_RR_closed [closure]: "x \<leftarrow>\<^sub>h\<le>(l) f(time) is RR"
  by (rel_auto)
    
lemma hEvolveAt_RR_closed [closure]: "x \<leftarrow>\<^sub>h(l) f(time) is RR"
  by (rel_auto)
    
lemma hEvolve_spec_refine:
  assumes "vwb_lens x" "\<forall> time\<ge>0. `P(time)\<lbrakk>\<lceil>f(time)\<rceil>\<^sub></$x\<acute>\<rbrakk>`"
  shows "\<lceil>P(time)\<rceil>\<^sub>h \<sqsubseteq> x \<leftarrow>\<^sub>h f(time)"
  using assms
  apply (simp add: hEvolve_def)
  apply (rel_simp)
  apply (metis vwb_lens.put_eq)
done    

subsection {* Pre-emption *}

definition hUntil ::
  "('d, 'c::t2_space) hyrel \<Rightarrow> 'c hrel \<Rightarrow> ('d,'c) hyrel" ("_ until\<^sub>h _" [74,75] 74) where
[upred_defs]: "P until\<^sub>h b = (P \<and> \<lceil>\<not> b\<rceil>\<^sub>h \<and> rl(&\<Sigma>) \<and> \<lceil>b\<rceil>\<^sub>C \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)"

definition hPreempt ::
  "('d, 'c::t2_space) hyrel \<Rightarrow> 'c hrel \<Rightarrow>
    ('d,'c) hyrel \<Rightarrow> ('d,'c) hyrel" ("_ [_]\<^sub>h _" [64,0,65] 64)
where [upred_defs]: "P [b]\<^sub>h Q = (((Q \<triangleleft> \<lceil>b\<lbrakk>$\<Sigma>/$\<Sigma>\<acute>\<rbrakk>\<rceil>\<^sub>C \<triangleright> (P \<and> \<lceil>\<not> b\<rceil>\<^sub>h)) \<sqinter> ((P \<and> \<lceil>\<not> b\<rceil>\<^sub>h \<and> rl(&\<Sigma>) \<and> \<lceil>b\<rceil>\<^sub>C) ;; (Q))))"

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

lemma hUntil_subst_init_cont [usubst]:
  "\<lbrakk> $tr \<sharp> \<sigma>; out\<alpha> \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<sigma>($\<^bold>c:x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> (P until\<^sub>h b) = \<sigma> \<dagger> (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$\<^bold>c:x\<rbrakk> until\<^sub>h b\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  by (simp add: hUntil_def usubst unrest)
  
lemma hUntil_RR_closed [closure]:
  assumes "P is RR"
  shows "P until\<^sub>h b is RR"
proof -
  have "RR (RR(P) until\<^sub>h b) = RR(P) until\<^sub>h b"
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
    
(* FIXME: Try and convert this to a pure Isar proof, or couple of lemmas *)
  
lemma hUntil_solve:
  assumes 
    "vwb_lens x" "k > 0" "continuous_on {0..k} f" "continuous_on UNIV get\<^bsub>x\<^esub>"
    "\<forall> t \<in> {0..<k}. c\<lbrakk>\<guillemotleft>f(t)\<guillemotright>/$x\<acute>\<rbrakk> = false" "c\<lbrakk>\<guillemotleft>f(k)\<guillemotright>/$x\<acute>\<rbrakk> = true"
  shows "(x \<leftarrow>\<^sub>h \<guillemotleft>f(time)\<guillemotright>) until\<^sub>h c = x \<leftarrow>\<^sub>h(\<guillemotleft>k\<guillemotright>) \<guillemotleft>f(time)\<guillemotright>"
  using assms(5,6) 
  apply (fast_uexpr_transfer)
  apply (rel_simp)
  apply (safe, simp_all)
  defer
  apply (metis assms(1) atLeastLessThan_iff vwb_lens.put_eq)
proof -
  fix tr tr' b
  assume a:
    "\<forall>t\<in>{0..<k}. \<forall>a b. \<not> \<lbrakk>c\<rbrakk>\<^sub>e (a, put\<^bsub>x\<^esub> b (f t))"
    "\<forall>a b. \<lbrakk>c\<rbrakk>\<^sub>e (a, put\<^bsub>x\<^esub> b (f k))"
    "\<forall>xa. 0 \<le> xa \<and> xa < end\<^sub>t (tr'-tr) \<longrightarrow> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(xa + end\<^sub>t tr)) = f xa"
    "tr < tr'"
    "\<forall>x. 0 \<le> x \<and> x < end\<^sub>t (tr'-tr) \<longrightarrow> \<not> \<lbrakk>c\<rbrakk>\<^sub>e (b, \<langle>tr'\<rangle>\<^sub>t(x + end\<^sub>t tr))"
    "\<lbrakk>c\<rbrakk>\<^sub>e (b, Lim (at_left (end\<^sub>t (tr'-tr))) \<langle>tr'-tr\<rangle>\<^sub>t)"
    
  let ?l = "end\<^sub>t (tr' - tr)"
    
  have etr_nz: "?l > 0"
    by (simp add: a(4))
    
  have tr_f: "\<forall>t. 0 \<le> t \<and> t < ?l \<longrightarrow> (get\<^bsub>x\<^esub> \<circ> \<langle>tr'-tr\<rangle>\<^sub>t) t = f t"
    by (simp add: a less_imp_le)

  have k:"end\<^sub>t (tr'-tr) \<le> k"
  proof (rule ccontr)
    assume less: "\<not> end\<^sub>t (tr' - tr) \<le> k"
    with assms(2) a(4,5) have 1:"\<not> \<lbrakk>c\<rbrakk>\<^sub>e (b, \<langle>tr' - tr\<rangle>\<^sub>t k)"
      by (auto)
    from assms(2) tr_f less have "get\<^bsub>x\<^esub> (\<langle>tr' - tr\<rangle>\<^sub>t k) = f k"
      by auto
    with a(2) have 2:"\<lbrakk>c\<rbrakk>\<^sub>e (b, \<langle>tr' - tr\<rangle>\<^sub>t k)"
      apply (drule_tac x="b" in spec)
      apply (drule_tac x="\<langle>tr' - tr\<rangle>\<^sub>t k" in spec)
      using assms(1) vwb_lens.put_eq apply fastforce
    done
    from 1 2 show False
      by blast
  qed      
      
  have gL: "get\<^bsub>x\<^esub> (Lim (at_left ?l) \<langle>tr'-tr\<rangle>\<^sub>t) = f (end\<^sub>t (tr' - tr))"
    using assms(1-4) a(4) tr_f k 
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
    with a(1) have "\<not> \<lbrakk>c\<rbrakk>\<^sub>e (b, put\<^bsub>x\<^esub> (Lim (at_left ?l) \<langle>tr'-tr\<rangle>\<^sub>t) (f ?l))"
      by simp
    then show ?thesis
      using a(6) assms(1) gL vwb_lens.put_eq by force 
  qed
next
  fix tr tr' b
  assume a:
    "\<forall>t\<in>{0..<end\<^sub>t (tr' - tr)}. \<forall>a b. \<not> \<lbrakk>c\<rbrakk>\<^sub>e (a, put\<^bsub>x\<^esub> b (f t))"
    "\<forall>a b. \<lbrakk>c\<rbrakk>\<^sub>e (a, put\<^bsub>x\<^esub> b (f (end\<^sub>t (tr'-tr))))"
    "\<forall>xa. 0 \<le> xa \<and> xa < end\<^sub>t (tr'-tr) \<longrightarrow> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(xa + end\<^sub>t tr)) = f xa"
    "tr < tr'"
    "k = end\<^sub>t (tr'-tr)"
    
  let ?l = "end\<^sub>t (tr' - tr)"
    
  have etr_nz: "?l > 0"
    by (simp add: a(4))
    
  have tr_f: "\<forall>t. 0 \<le> t \<and> t < ?l \<longrightarrow> (get\<^bsub>x\<^esub> \<circ> \<langle>tr'-tr\<rangle>\<^sub>t) t = f t"
    by (simp add: a less_imp_le)
      
  have gL: "get\<^bsub>x\<^esub> (Lim (at_left ?l) \<langle>tr'-tr\<rangle>\<^sub>t) = f ?l"
    using assms(1-4) a tr_f 
    by (rule_tac Lim_continuous_lens, auto simp add: continuous_on_subset)
    
  have c: "\<lbrakk>c\<rbrakk>\<^sub>e (b, put\<^bsub>x\<^esub> (Lim (at_left ?l) \<langle>tr'-tr\<rangle>\<^sub>t) (f (end\<^sub>t (tr'-tr))))"
    by (simp add: a(2))
    
  show "\<lbrakk>c\<rbrakk>\<^sub>e (b, Lim (at_left ?l) \<langle>tr'-tr\<rangle>\<^sub>t)"
    using assms(1) c gL vwb_lens.put_eq by fastforce    
qed

subsection {* Stepping a Hybrid Relation Forward *}
  
definition hStepRel :: "real \<Rightarrow> ('d, 'c::t2_space) hyrel \<Rightarrow> 'c hrel" ("HyStep[_]'(_')") where
[upred_defs]: "hStepRel t P = ((((P \<and> \<^bold>l =\<^sub>u \<guillemotleft>t\<guillemotright> \<and> rl(&\<Sigma>) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) \<restriction>\<^sub>v (&\<^bold>c \<times> &\<^bold>c)) \<restriction>\<^sub>p (\<^bold>c \<times>\<^sub>L \<^bold>c)) \<triangleleft> \<guillemotleft>t\<guillemotright> >\<^sub>u 0 \<triangleright>\<^sub>r II)"
  
lemma HyStep_hEvolve:
  fixes x :: "'a::t2_space \<Longrightarrow> 'c::t2_space"
  assumes "n > 0" "continuous_on {0..n} f"
  shows "HyStep[n](&\<Sigma> \<leftarrow>\<^sub>h \<guillemotleft>f(time)\<guillemotright>  :: ('d,'c) hyrel) = (\<Sigma> := \<guillemotleft>f(n)\<guillemotright>)" (is "?lhs = ?rhs")
proof -
  from assms(1) have "?lhs = \<lfloor>(&\<Sigma> \<leftarrow>\<^sub>h \<guillemotleft>f time\<guillemotright> \<and> \<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> rl(&\<Sigma>) :: ('d,'c) hyrel) \<restriction>\<^sub>v (&\<^bold>c \<times> &\<^bold>c)\<rfloor>\<^sub>C"
    by (simp add: hStepRel_def, rel_auto)
  also have "... = \<lfloor>(&\<Sigma> \<leftarrow>\<^sub>h(\<guillemotleft>n\<guillemotright>) \<guillemotleft>f time\<guillemotright> :: ('d,'c) hyrel) \<restriction>\<^sub>v (&\<^bold>c \<times> &\<^bold>c)\<rfloor>\<^sub>C"
    by (rel_auto)           
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
    show "\<exists>tr tr'.
            tr \<le> tr' \<and>
            (\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow> (\<langle>tr' - tr\<rangle>\<^sub>t t) = f t) \<and>
            tr < tr' \<and> end\<^sub>t (tr' - tr) = n \<and> tr < tr' \<and> f n = Lim (at_left (end\<^sub>t (tr' - tr))) (\<langle>tr' - tr\<rangle>\<^sub>t)"
      by (rule_tac x="[]\<^sub>t" in exI, rule_tac x="mk\<^sub>t n f" in exI)
         (auto simp add: Limit_solve at_left_from_zero)
  qed
  finally show ?thesis .
qed
  
end