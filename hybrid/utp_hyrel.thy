section {* Hybrid Relational Calculus *}

theory utp_hyrel
imports
  "../utp/utp"
  "../theories/utp_rea_designs"
  "../contrib/Ordinary_Differential_Equations/ODE_Analysis"
  "../dynamics/Derivative_extra"
  "../dynamics/Timed_Traces"
begin recall_syntax

hide_type rel

no_notation inner (infix "\<bullet>" 70)

text {* We also set up adhoc overloading to apply timed traces and contiguous functions *}

adhoc_overloading uapply cgf_apply and uapply tt_apply

text {* This section contains a mechanisation of the hybrid relational calculus described
  in~\cite{Foster16b}, though with a new semantic model based on generalised reactive processes
  and timed traces~\cite{Hayes2006, Hayes2010, Hofner2009}. *}

subsection {* Types and Preliminaries *}

text {* We first set up some types to represent hybrid relations. *}

type_synonym ('d,'c) hybs = "('d \<times> 'c, 'c ttrace, unit) rsp"
type_synonym ('d,'c) hyrel  = "('d,'c) hybs hrel"
type_synonym ('a,'d,'c) hyexpr = "('a,('d,'c) hybs \<times> ('d,'c) hybs) uexpr"

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
  "('a \<Longrightarrow> 'c::topological_space) \<Rightarrow> (real, 'd, 'c) hyexpr \<Rightarrow> ('a, 'd, 'c) hyexpr"
  ("_~'(_')" [999,0] 999)
where "x~(t) \<equiv> \<^bold>t\<lparr>t\<rparr>\<^sub>u:(x)"

text {* The syntax @{term "x~(t)"} is a convenient way of refer to the value of a continuous
  variable $x$ at a particular instant $t$. *}

translations
  "\<^bold>t" <= "CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr))"
  "x~(t)" <= "CONST uop (CONST lens_get x) (CONST bop (CONST uapply) (CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr))) t)"
  "\<^bold>l" <= "CONST uop end\<^sub>t (CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr)))"

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
  by (simp_all add: disc_alpha_def lens_indep_left_ext lens_indep_sym)

lemma disc_indep_wait [simp]: "\<^bold>d \<bowtie> wait" "wait \<bowtie> \<^bold>d"
  by (simp_all add: disc_alpha_def lens_indep_left_ext lens_indep_sym)

lemma disc_indep_tr [simp]: "\<^bold>d \<bowtie> tr" "tr \<bowtie> \<^bold>d"
  by (simp_all add: disc_alpha_def lens_indep_left_ext lens_indep_sym)

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

abbreviation cont_pre_lift :: "('a, 'c) uexpr \<Rightarrow> ('a,'d,'c::topological_space) hyexpr" ("\<lceil>_\<rceil>\<^sub>C\<^sub><") where
"\<lceil>P\<rceil>\<^sub>C\<^sub>< \<equiv> P \<oplus>\<^sub>p (ivar \<^bold>c)"

abbreviation cont_post_lift :: "('a, 'c) uexpr \<Rightarrow> ('a,'d,'c::topological_space) hyexpr" ("\<lceil>_\<rceil>\<^sub>C\<^sub>>") where
"\<lceil>P\<rceil>\<^sub>C\<^sub>> \<equiv> P \<oplus>\<^sub>p (ovar \<^bold>c)"

translations
  "\<lceil>P\<rceil>\<^sub>C\<^sub><" <= "CONST aext P (CONST ivar CONST cont_alpha)"
  "\<lceil>P\<rceil>\<^sub>C\<^sub>>" <= "CONST aext P (CONST ovar CONST cont_alpha)"

lemma unrest_lift_cont_subst [unrest]:
  "\<lbrakk> vwb_lens x; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> (\<lceil>P\<rceil>\<^sub>C\<^sub><)\<lbrakk>v/$\<^bold>c\<rbrakk>"
  by (rel_auto)

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

text {* We also set up some useful syntax to refer to the end of a continuous trace. *}

syntax
  "_uend" :: "logic \<Rightarrow> logic" ("end\<^sub>u'(_')")

translations
  "end\<^sub>u(t)" == "CONST uop end\<^sub>t t"

text {* The next properties states that the end point of an empty timed trace is 0. *}

lemma uend_0 [simp]: "end\<^sub>u(0) = 0"
  by (simp add: upred_defs lit_def uop_def Abs_uexpr_inverse)

subsection {* Instant Predicates *}

definition at ::
  "('a, 'c::topological_space) uexpr \<Rightarrow> real \<Rightarrow> ('a, 'd, 'c) hyexpr"
  (infix "@\<^sub>u" 60) where
[upred_defs]: "P @\<^sub>u t = [$\<^bold>c \<mapsto>\<^sub>s \<^bold>t\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u] \<dagger> \<lceil>P\<rceil>\<^sub>C\<^sub><"

text {* The expression @{term "P @\<^sub>u t"} asserts that the predicate @{term "P"} is satisfied by
  the continuous state at time instant @{term "t"}. Here, @{term "P"} is a predicate only
  on the flat continuous state. The operator is implemented by first extending the alphabet
  of @{term "P"} to include all the hybrid variables, and then substituting the continuous
  state for the continuous state at @{term "t"}, denoted by @{term "\<^bold>t\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u"}. *}

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

lemma at_unrest_cont [unrest]: "$\<^bold>c \<sharp> (P @\<^sub>u t)" "$\<^bold>c\<acute> \<sharp> (P @\<^sub>u t)"
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

lemma at_var [simp]:
  fixes x :: "('a \<Longrightarrow> 'c::topological_space)"
  shows "utp_expr.var x @\<^sub>u t = \<^bold>t\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u:(x)"
  by (pred_auto)

text {* Lemma @{thm [source] "at_var"} tells us the result of lifting a flat continuous variable
  @{term "x"}. It results in an expression which refers to that particular variable within the
  timed trace at instant @{term "t"}. *}

lemma subst_cvar_traj [usubst]: "\<langle>[$\<^bold>c \<mapsto>\<^sub>s \<^bold>t\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u]\<rangle>\<^sub>s (x ;\<^sub>L in_var \<^bold>c) = x~(\<guillemotleft>t\<guillemotright>)"
  by (pred_auto)

subsection {* The Interval Operator *}

definition hInt :: "(real \<Rightarrow> 'c::topological_space upred) \<Rightarrow> ('d,'c) hyrel" where
[urel_defs]: "hInt P = ($tr \<le>\<^sub>u $tr\<acute> \<and> (\<^bold>\<forall> t \<in> {0..<\<^bold>l}\<^sub>u \<bullet> (P t) @\<^sub>u t))"

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

definition hDisInt :: "(real \<Rightarrow> 'c::t2_space upred) \<Rightarrow> ('d, 'c) hyrel" where
[urel_defs]: "hDisInt P = (hInt P \<and> \<^bold>l >\<^sub>u 0 \<and> $\<^bold>c =\<^sub>u \<^bold>t\<lparr>0\<rparr>\<^sub>u \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> \<^bold>l\<^sup>-)(\<^bold>t\<lparr>\<guillemotleft>x\<guillemotright>\<rparr>\<^sub>u) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)"

text {* We also set up the adapted version of the interval operator, @{term "hDisInt P"}, that
  conjoins an interval specification with three predicates, which also happen to be coupling
  invariants, and yield what we might call a ``hybrid interval''. The first invariant
  states that the continuous state within the trace at instant 0 must
  correspond to the before value of the continuous state, i.e. @{term "$\<^bold>c =\<^sub>u \<^bold>t\<lparr>0\<rparr>\<^sub>u"}. The second
  states that the after value of the continuous state must take on the limit of the continuous
  state as the trace approaches the end value @{term "\<^bold>l"}, i.e. @{term "$\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> \<^bold>l\<^sup>-)(\<^bold>t\<lparr>\<guillemotleft>x\<guillemotright>\<rparr>\<^sub>u)"}.
  This second constraint requires that the timed trace must converge to a point at @{term "\<^bold>l"},
  which is true because our timed trace is piecewise convergent. The last two constraints are what
  makes our model a hybrid computational model, since we link together discrete assignments to
  continuous variables in the before and after state, and continuous evolution in the timed trace.
  The final predicate states that the discrete state does not change during a continuous evolution.

  We next set up some useful syntax translations for the interval operator. *}

syntax
  "_time_var" :: "logic"
  "_hInt"     :: "logic \<Rightarrow> logic" ("\<lceil>_\<rceil>\<^sub>h")
  "_hDisInt"  :: "logic \<Rightarrow> logic" ("\<^bold>\<lceil>_\<^bold>\<rceil>\<^sub>h")

parse_translation {*
let
  fun time_var_tr [] = Syntax.free "\<tau>"
    | time_var_tr _  = raise Match;
in
[(@{syntax_const "_time_var"}, K time_var_tr)]
end
*}

translations
  "\<lceil>P\<rceil>\<^sub>h" => "CONST hInt (\<lambda> _time_var. P)"
  "\<lceil>P\<rceil>\<^sub>h" <= "CONST hInt (\<lambda> x. P)"
  "\<^bold>\<lceil>P\<^bold>\<rceil>\<^sub>h" => "CONST hDisInt (\<lambda> _time_var. P)"
  "\<^bold>\<lceil>P\<^bold>\<rceil>\<^sub>h" <= "CONST hDisInt (\<lambda> x. P)"
  
text {* A regular interval can be written using the notation @{term "\<lceil>P(\<tau>)\<rceil>\<^sub>h"}, where $\tau$ is
  a free variable denoting the present time. Having the present time as a free variable means
  we can write algebraic equations that depend on time, such as @{term "\<lceil>&x =\<^sub>u 2 * \<guillemotleft>\<tau>\<guillemotright>\<rceil>\<^sub>h"} for
  example. Similarly, a hybrid interval can be written using a boldface as @{term "\<^bold>\<lceil>P(\<tau>)\<^bold>\<rceil>\<^sub>h"}. *}

lemma hInt_unrest_cont [unrest]: "$\<^bold>c \<sharp> \<lceil>P(\<tau>)\<rceil>\<^sub>h"
  by (simp add: hInt_def unrest)

lemma R1_hInt: "R1(\<lceil>P(\<tau>)\<rceil>\<^sub>h) = \<lceil>P(\<tau>)\<rceil>\<^sub>h"
  by (rel_auto)

lemma R2s_hInt: "R2c(\<lceil>P(\<tau>)\<rceil>\<^sub>h) = \<lceil>P(\<tau>)\<rceil>\<^sub>h"
  by (rel_auto)

lemma R2_hInt: "R2(\<lceil>P(\<tau>)\<rceil>\<^sub>h) = \<lceil>P(\<tau>)\<rceil>\<^sub>h"
  by (metis R1_R2c_is_R2 R1_hInt R2s_hInt)

text {* Theorem @{thm [source] "hInt_unrest_cont"} states that no continuous before variable
  is fixed by the regular interval operator. This is because the regular interval operator
  does not refer to state variables but only the evolution of the trajectory. We can also
  show that the interval operator is both @{term "R1"} healthy, since the trajectory can
  only get longer, and also @{term "R2c"} healthy, since it does not refer to the history.

  We also prove some laws about intervals. *}

lemma hInt_false: "\<lceil>false\<rceil>\<^sub>h = ($tr\<acute> =\<^sub>u $tr)"
  by (rel_auto, meson eq_iff leI minus_zero_eq tt_end_0_iff tt_end_ge_0)

lemma hInt_true: "\<lceil>true\<rceil>\<^sub>h = R1(true)"
  by (rel_auto)

lemma hInt_conj: "\<lceil>P(\<tau>) \<and> Q(\<tau>)\<rceil>\<^sub>h = (\<lceil>P(\<tau>)\<rceil>\<^sub>h \<and> \<lceil>Q(\<tau>)\<rceil>\<^sub>h)"
  by (rel_auto)

lemma hInt_disj: "\<lceil>P(\<tau>) \<or> Q(\<tau>)\<rceil>\<^sub>h \<sqsubseteq> (\<lceil>P(\<tau>)\<rceil>\<^sub>h \<or> \<lceil>Q(\<tau>)\<rceil>\<^sub>h)"
  by (rel_auto)

lemma hInt_refine: "`\<^bold>\<forall> \<tau> \<bullet> P(\<tau>) \<Rightarrow> Q(\<tau>)` \<Longrightarrow> \<lceil>Q(\<tau>)\<rceil>\<^sub>h \<sqsubseteq> \<lceil>P(\<tau>)\<rceil>\<^sub>h"
  by (rel_auto)
  
lemma neg_hInt_R1_true: "R1(\<not> \<lceil>P\<rceil>\<^sub>h) ;; R1(true) = R1(\<not> \<lceil>P\<rceil>\<^sub>h)"
proof (rel_auto)
  fix tr tr' tr'' :: "'a ttrace" and t :: real
  assume a: "tr \<le> tr''" "tr'' \<le> tr'" "0 \<le> t" "t < end\<^sub>t(tr'' - tr)" "\<not> \<lbrakk>P\<rbrakk>\<^sub>e (\<langle>tr''\<rangle>\<^sub>t (t + end\<^sub>t tr))"
  hence "tr'' - tr \<le> tr' - tr"
    by (simp add: minus_cancel_le)
  with a show "\<exists>x. 0 \<le> x \<and> x < end\<^sub>t (tr' - tr) \<and> \<not> \<lbrakk>P\<rbrakk>\<^sub>e (\<langle>tr' - tr\<rangle>\<^sub>t x)"
    apply (rule_tac x="t" in exI, auto)
    using tt_sub_end apply fastforce
    apply (metis dual_order.trans pre_trace_class.le_iff_add tt_apply_minus tt_cat_ext_first)
    done
qed
        
text {* Theorem @{thm [source] hInt_false} and @{thm [source] hInt_true} give us obvious results
  about intervals over false and true. Theorem @{thm [source] hInt_conj} allows us to rewrite
  and interval conjunction as a conjunction of intervals. The same is not true of disjunction,
  as @{thm [source] hInt_disj} shows, because at each instant each $P$ or $Q$ may hold, and thus an
  inequality is present in the rule. Finally, theorem @{thm [source] hInt_refine} tells us that
  an interval can be refined to another is we can show that an implication between the two interval
  predicates. Additionally we prove the following law about sequential composition of
  time-independent intervals. *}

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

text {* The proof of the theorem is quite long, but the theorem intuitively tells us that an interval
  can always be split into two intervals where the property holds of both. *}

lemma seq_var_ident_liftr:
  assumes "vwb_lens x" "$x\<acute> \<sharp> P" "$x \<sharp> Q"
  shows "((P \<and> $x\<acute> =\<^sub>u $x) ;; (Q \<and> $x\<acute> =\<^sub>u $x)) = ((P ;; Q) \<and> $x\<acute> =\<^sub>u $x)"
  using assms apply (rel_auto)
  by (metis (no_types, lifting) vwb_lens_wb wb_lens_weak weak_lens.put_get)

(*
lemma hInt_seq_r: "(\<^bold>\<lceil>P\<^bold>\<rceil>\<^sub>H ;; \<^bold>\<lceil>P\<^bold>\<rceil>\<^sub>H) = \<^bold>\<lceil>P\<^bold>\<rceil>\<^sub>H"
proof -
  have "((\<lceil>P\<rceil>\<^sub>H \<and> $\<^bold>c =\<^sub>u \<^bold>t\<lparr>0\<rparr>\<^sub>u \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> end\<^sub>u(\<^bold>t)\<^sup>-)(\<^bold>t\<lparr>\<guillemotleft>x\<guillemotright>\<rparr>\<^sub>u) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) ;;
         (\<lceil>P\<rceil>\<^sub>H \<and> $\<^bold>c =\<^sub>u \<^bold>t\<lparr>0\<rparr>\<^sub>u \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> end\<^sub>u(\<^bold>t)\<^sup>-)(\<^bold>t\<lparr>\<guillemotleft>x\<guillemotright>\<rparr>\<^sub>u) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)) =
        (((\<lceil>P\<rceil>\<^sub>H \<and> $\<^bold>c =\<^sub>u \<^bold>t\<lparr>0\<rparr>\<^sub>u \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> end\<^sub>u(\<^bold>t)\<^sup>-)(\<^bold>t\<lparr>\<guillemotleft>x\<guillemotright>\<rparr>\<^sub>u)) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) ;;
         ((\<lceil>P\<rceil>\<^sub>H \<and> $\<^bold>c =\<^sub>u \<^bold>t\<lparr>0\<rparr>\<^sub>u \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> end\<^sub>u(\<^bold>t)\<^sup>-)(\<^bold>t\<lparr>\<guillemotleft>x\<guillemotright>\<rparr>\<^sub>u)) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d))"
    by (rel_auto)

  also
  have "... =
        (((\<lceil>P\<rceil>\<^sub>H \<and> $\<^bold>c =\<^sub>u \<^bold>t\<lparr>0\<rparr>\<^sub>u \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> end\<^sub>u(\<^bold>t)\<^sup>-)(\<^bold>t\<lparr>\<guillemotleft>x\<guillemotright>\<rparr>\<^sub>u)) ;;
          (\<lceil>P\<rceil>\<^sub>H \<and> $\<^bold>c =\<^sub>u \<^bold>t\<lparr>0\<rparr>\<^sub>u \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> end\<^sub>u(\<^bold>t)\<^sup>-)(\<^bold>t\<lparr>\<guillemotleft>x\<guillemotright>\<rparr>\<^sub>u))) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)"
    by (subst seq_var_ident_liftr, simp_all add: unrest)
  also
  have "... =
        (((\<lceil>P\<rceil>\<^sub>H \<and> $\<^bold>c =\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright>\<lparr>0\<rparr>\<^sub>u \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> end\<^sub>u(\<guillemotleft>t\<^sub>0\<guillemotright>)\<^sup>-)(\<guillemotleft>t\<^sub>0\<guillemotright>\<lparr>\<guillemotleft>x\<guillemotright>\<rparr>\<^sub>u)) ;;
          (\<lceil>P\<rceil>\<^sub>H \<and> $\<^bold>c =\<^sub>u \<guillemotleft>t\<^sub>1\<guillemotright>\<lparr>0\<rparr>\<^sub>u \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> end\<^sub>u(\<guillemotleft>t\<^sub>1\<guillemotright>)\<^sup>-)(\<guillemotleft>t\<^sub>1\<guillemotright>\<lparr>\<guillemotleft>x\<guillemotright>\<rparr>\<^sub>u))) \<and>  \<and>  $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)"
    by (subst seq_var_ident_liftr, simp_all add: unrest)

  also
  have "... =
        (((\<lceil>P\<rceil>\<^sub>H \<and> $\<^bold>c =\<^sub>u \<^bold>t\<lparr>0\<rparr>\<^sub>u \<and> $\<^bold>c\<acute> =\<^sub>u \<^bold>t\<lparr>end\<^sub>u(\<^bold>t)\<rparr>\<^sub>u) ;;
          (\<lceil>P\<rceil>\<^sub>H \<and> $\<^bold>c =\<^sub>u \<^bold>t\<lparr>0\<rparr>\<^sub>u \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> end\<^sub>u(\<^bold>t)\<^sup>-)(\<^bold>t\<lparr>\<guillemotleft>x\<guillemotright>\<rparr>\<^sub>u))) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)"
    apply (rel_auto)
*)

subsection {* Pre-emption *}

definition hPreempt ::
  "('d, 'c::topological_space) hyrel \<Rightarrow> 'c upred \<Rightarrow>
    ('d,'c) hyrel \<Rightarrow> ('d,'c) hyrel" ("_ [_]\<^sub>h _" [64,0,65] 64)
where "P [b]\<^sub>h Q = (((Q \<triangleleft> \<lceil>b\<rceil>\<^sub>C\<^sub>< \<triangleright> (P \<and> \<lceil>\<not> b\<rceil>\<^sub>h)) \<sqinter> ((\<lceil>\<not> b\<rceil>\<^sub>h \<and> P) ;; (\<lceil>b\<rceil>\<^sub>C\<^sub>< \<and> Q))))"

text {* The pre-emption operator @{term "P [b]\<^sub>h Q"} states that $P$ is active until $b$ is satisfied
  by the continuous variables. At this point $Q$ will be activated. Usually $P$ will be an evolution
  of the continuous variables, and $b$ some kind of barrier condition. The operator can be used
  to write hybrid systems where an evolution occurs until some condition is satisfied, e.g. a
  particular temperature or other quantity is reached, and then some discrete activity is executed.
  We prove a few simple properties about this operator. *}

end