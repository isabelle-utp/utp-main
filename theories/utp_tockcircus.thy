section \<open> tock-Circus \<close>

theory utp_tockcircus
imports "UTP-Reactive-Designs.utp_rea_designs" "rcircus/Refusal_Tests"
begin recall_syntax

subsection \<open> Foundations \<close>

text \<open> We try and characterise a tock-CSP like model using the standard Circus pattern and adapting
  the CML model and bits of the refusal testing model. First we represent traces. \<close>

datatype ('t, 'e) teva = Tock "'t" | Evt 'e

type_synonym 'e tev = "('e set, 'e) teva"

text \<open> We don't need a tick event, because this is handled by the $wait$ flag. Nor do we need to
  separate refusals and tocks. A refusal in tock-CSP (as I understand) can occur either (1) just
  before a tock occurs, or (2) at the end of a trace. We gain the former by embedding refusals
  in a tock (as in CML). We gain the latter by including the $ref'$ variable as in Circus. We encode
  the healthiness condition that a tock can't occur in a refusal before a tock event using
  the type system. \<close>

alphabet ('s, 'e) tc_vars = "('e tev list, 's) rsp_vars" +
  ref :: "(unit, 'e) teva refusal"

text \<open> The $ref$ variable is not simply a set, but a set augmented with the @{term "\<^bold>\<bullet>"} that denotes
  stability. We need this because tick-tock traces can end without a refusal. Note that unlike
  in the trace this is a refusal over @{typ "'e tev"} so that we can refuse tocks at the end. \<close>

text \<open> The interpretation of $wait$ changes to there being both stable (quiescent) and unstable.
  Extra information is needed for refusals. What is the meaning pericondition? \<close>

type_synonym ('s,'e) taction  = "('s, 'e tev) tc_vars hrel"

definition tocks :: "'e set \<Rightarrow> 'e tev list set" where
"tocks X = {t. \<forall> e \<in> set(t). \<exists> Y. e = Tock Y \<and> Y \<subseteq> X}"

lemma tocks_Nil [simp]: "[] \<in> tocks X"
  by (simp add: tocks_def)

lemma tocks_Cons: "\<lbrakk> Y \<subseteq> X; t \<in> tocks X \<rbrakk> \<Longrightarrow> Tock Y # t \<in> tocks X"
  by (simp add: tocks_def)

lemma tocks_append: "\<lbrakk> s \<in> tocks X; t \<in> tocks X \<rbrakk> \<Longrightarrow> s @ t \<in> tocks X"
  by (auto simp add: tocks_def)

definition "mk_tocks n = replicate n (Tock {})"

lemma mk_tocks: "mk_tocks n \<in> tocks X"
  by (simp add: mk_tocks_def tocks_def)

lemma length_mk_tocks [simp]: "length (mk_tocks n) = n"
  by (simp add: mk_tocks_def)

subsection \<open> Reactive Relation Constructs \<close>

no_utp_lift lift_state_rel

definition tc_stable :: "'s upred \<Rightarrow> ('e tev list, 's) uexpr \<Rightarrow> ((unit, 'e) teva set, 's) uexpr \<Rightarrow> _" ("\<E>'(_, _, _')") where
[upred_defs]: "\<E>(s,t,E) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> = $tr @ \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> (\<forall> e\<in>\<lceil>E\<rceil>\<^sub>S\<^sub><. \<guillemotleft>e\<guillemotright> \<notin>\<^sub>\<R> $ref\<acute>))"

definition tc_unstable :: "'s upred \<Rightarrow> ('e tev list, 's) uexpr \<Rightarrow> _" ("\<U>'(_, _')") where
[upred_defs]: "\<U>(s,t) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> = $tr @ \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> $ref\<acute> = \<^bold>\<bullet>)"

definition tc_final :: "'s upred \<Rightarrow> ('e tev list, 's) uexpr \<Rightarrow> 's usubst \<Rightarrow> _" ("\<F>'(_, _, _')") where
[upred_defs]: "\<F>(s,t,\<sigma>) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> = $tr @ \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S)" 

definition tc_time ("\<T>'(_,_')") where 
[upred_defs]: "tc_time X A = U(\<exists> t \<in> tocks \<guillemotleft>X\<guillemotright>. $tr\<acute> = $tr @ t \<and> length(t) \<in> \<lceil>A\<rceil>\<^sub>S\<^sub><)"

utp_lift_notation tc_stable
utp_lift_notation tc_unstable
utp_lift_notation tc_final (2)
utp_lift_notation tc_time

lemma [closure]: "\<E>(s, t, E) is RR"
  by (rel_auto)

lemma [closure]: "\<U>(s, t) is RR"
  by (rel_auto)

lemma [closure]: "\<F>(s, t, \<sigma>) is RR"
  by (rel_auto)

lemma [unrest]: "$st\<acute> \<sharp> \<E>(s, t, E)"
  by (rel_auto)

lemma [unrest]: "$st\<acute> \<sharp> \<U>(s, t)"
  by (rel_auto)

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>\<^sub>1) ;; \<F>(s\<^sub>2, t\<^sub>2, \<sigma>\<^sub>2) = \<F>(s\<^sub>1 \<and> \<sigma>\<^sub>1 \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma>\<^sub>1 \<dagger> t\<^sub>2, \<sigma>\<^sub>2 \<circ>\<^sub>s \<sigma>\<^sub>1)"
  by (rel_auto)

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>) ;; \<E>(s\<^sub>2, t\<^sub>2, E) = \<E>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma> \<dagger> t\<^sub>2, \<sigma> \<dagger> E)"
  by (rel_auto)

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>) ;; \<U>(s\<^sub>2, t\<^sub>2) = \<U>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma> \<dagger> t\<^sub>2)"
  by (rel_auto)

subsection \<open> Basic Constructs \<close>

definition Div :: "('s,'e) taction" where
[rdes_def]: "Div = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> \<U>(true, []) \<diamondop> false)"

text \<open> This is the same as Circus $Skip$, except that it includes a quiescent state. \<close>

definition Skip :: "('s,'e) taction" where
[rdes_def]: "Skip = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> \<U>(true, []) \<diamondop> \<F>(true, [], id\<^sub>s))"

definition AssignsT :: "'s usubst \<Rightarrow> ('s,'e) taction" ("\<langle>_\<rangle>\<^sub>T") where
[upred_defs]: "AssignsT \<sigma> = \<^bold>R\<^sub>s(true \<turnstile> \<U>(true, []) \<diamondop> \<F>(true, [], \<sigma>))" 

definition Stop :: "('s,'e) taction" where
[rdes_def]: "Stop = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> U(R1(&tt \<in> tocks UNIV) \<and> Tock () \<notin>\<^sub>\<R> $ref\<acute>) \<diamondop> false)"

definition Stop\<^sub>U :: "('s,'e) taction" where
[rdes_def]: "Stop\<^sub>U = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> U($tr\<acute> = $tr) \<diamondop> false)"

utp_const R2

term "\<E>(true, [], {Tock ()})"

term "(\<Sqinter> X \<bullet> \<U>(true, [Tock \<guillemotleft>X\<guillemotright>]))"

definition Pause :: "('s,'e) taction" where
"Pause = 
  \<^bold>R\<^sub>s(true\<^sub>r 
  \<turnstile> \<E>(true, [], {Tock ()}) \<or> (\<Sqinter> X \<bullet> \<U>(true, [Tock X])) 
  \<diamondop> (\<Sqinter> X \<bullet> \<F>(true, [Tock X], id\<^sub>s)))"

lemma "((\<Sqinter> t \<bullet> \<E>(\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> length(\<guillemotleft>t\<guillemotright>) < n, \<guillemotleft>t\<guillemotright>, {Tock ()})) 
       \<or> (\<Sqinter> t \<bullet> \<U>(\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> length(\<guillemotleft>t\<guillemotright>) = n, \<guillemotleft>t\<guillemotright>))) is RR"
  by (simp add: closure)

lemma "(\<Sqinter> t \<bullet> \<F>(\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> length(\<guillemotleft>t\<guillemotright>) = n, \<guillemotleft>t\<guillemotright>, id\<^sub>s)) is RR"
  by (simp add: closure)


definition Wait :: "(nat, 's) uexpr \<Rightarrow> ('s,'e) taction" where
[rdes_def]: "Wait n = 
  \<^bold>R\<^sub>s(true\<^sub>r 
    \<turnstile> ((\<Sqinter> t \<bullet> \<E>(\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> length(\<guillemotleft>t\<guillemotright>) < n, \<guillemotleft>t\<guillemotright>, {Tock ()})) 
       \<or> (\<Sqinter> t \<bullet> \<U>(\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> length(\<guillemotleft>t\<guillemotright>) = n, \<guillemotleft>t\<guillemotright>)))
    \<diamondop> (\<Sqinter> t \<bullet> \<F>(\<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> length(\<guillemotleft>t\<guillemotright>) = n, \<guillemotleft>t\<guillemotright>, id\<^sub>s)))"


lemma [closure]: "U(R2(&tt \<in> tocks UNIV \<and> length(&tt) = \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st)) is RR"
  by (rel_auto)


lemma [closure]: "U($tr\<acute> = $tr \<and> $st\<acute> = $st) is RR"
  apply (rel_auto)
  using minus_zero_eq by blast

lemma [closure]: "U(R1(&tt \<in> tocks UNIV) \<and> Tock () \<notin>\<^sub>\<R> $ref\<acute>) is RR"
  by (rel_auto)

lemma "Div ;; Skip = Div"
  by (rdes_simp)

lemma "Skip ;; Skip = Skip"
  by (rdes_eq)

lemma "Skip ;; Stop = Stop"
  by (rdes_eq)

lemma "Stop \<sqsubseteq> Div"
  by (rdes_refine)

utp_const lift_state_pre

lemma "Wait 0 = Skip"
  by (rdes_eq)

lemma "Wait m ;; Wait n = Wait(m + n)"
  apply (rdes_eq_split)
  oops

lemma "\<^U>(R2 (&tt \<in> tocks UNIV \<and> length (&tt) = \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st)) ;; \<^U>(R2 (&tt \<in> tocks UNIV \<and> length (&tt) = \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st)) =
       U(R2 (&tt \<in> tocks UNIV \<and> length (&tt) = \<lceil>m\<rceil>\<^sub>S\<^sub>< + \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st))"
  apply (simp add: R2_form usubst unrest)
  apply (rel_auto)
   apply (simp add: tocks_append)
  oops

text \<open> Pedro Comment: Renaming should be a relation rather than a function. \<close>

end