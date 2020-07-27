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

text \<open> The $ref$ variable is not simply a set, but a set augmented with the @{term \<bullet>} that denotes
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

subsection \<open> Basic Constructs \<close>

definition Div :: "('s,'e) taction" where
[rdes_def]: "Div = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> U($tr\<acute> = $tr \<and> $ref\<acute> = \<bullet>) \<diamondop> false)"

text \<open> This is the same as Circus $Skip$, except that it includes a quiescent state. \<close>

definition Skip :: "('s,'e) taction" where
[rdes_def]: "Skip = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> U($tr\<acute> = $tr \<and> $ref\<acute> = \<bullet>) \<diamondop> U($tr\<acute> = $tr \<and> $st\<acute> = $st))"

no_utp_lift lift_state_rel

definition AssignsT :: "'s usubst \<Rightarrow> ('s,'e) taction" ("\<langle>_\<rangle>\<^sub>T") where
[upred_defs]: "AssignsT \<sigma> = \<^bold>R\<^sub>s(true \<turnstile> U($tr\<acute> = $tr \<and> $ref\<acute> = \<bullet>) \<diamondop> U($tr\<acute> = $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S))" 

definition Stop :: "('s,'e) taction" where
[rdes_def]: "Stop = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> U(R1(&tt \<in> tocks UNIV)) \<diamondop> false)" \<comment> \<open> FIXME: tock is not in ref' \<close>

definition Stop\<^sub>U :: "('s,'e) taction" where
[rdes_def]: "Stop\<^sub>U = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> U($tr\<acute> = $tr) \<diamondop> false)"

utp_const R2

definition Wait :: "(nat, 's) uexpr \<Rightarrow> ('s,'e) taction" where
[rdes_def]: "Wait n = 
  \<^bold>R\<^sub>s(true\<^sub>r 
    \<turnstile> U(R2(&tt \<in> tocks UNIV \<and> length(&tt) \<le> \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> (length(&tt) = \<lceil>n\<rceil>\<^sub>S\<^sub>< \<Rightarrow> $ref\<acute> = \<bullet>))) \<comment> \<open> FIXME: tock not in ref' \<close>
    \<diamondop> U(R2(&tt \<in> tocks UNIV \<and> length(&tt) = \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st)))"

lemma [closure]: "U(R2(&tt \<in> tocks UNIV \<and> length(&tt) \<le> \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> (length(&tt) = \<lceil>n\<rceil>\<^sub>S\<^sub>< \<Rightarrow> $ref\<acute> = \<bullet>))) is RR"
  by (rel_auto)

lemma [closure]: "U(R2(&tt \<in> tocks UNIV \<and> length(&tt) = \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st)) is RR"
  by (rel_auto)

lemma [closure]: "U($tr\<acute> = $tr \<and> $ref\<acute> = \<bullet>) is RR"
  by (rel_auto)

lemma [closure]: "U($tr\<acute> = $tr \<and> $st\<acute> = $st) is RR"
  apply (rel_auto)
  using minus_zero_eq by blast

lemma [closure]: "U(R1(&tt \<in> tocks UNIV)) is RR"
  by (rel_auto)

lemma "Div ;; Skip = Div"
  by (rdes_eq)

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
  apply (rdes_simp)
  oops

lemma "\<^U>(R2 (&tt \<in> tocks UNIV \<and> length (&tt) = \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st)) ;; \<^U>(R2 (&tt \<in> tocks UNIV \<and> length (&tt) = \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st)) =
       U(R2 (&tt \<in> tocks UNIV \<and> length (&tt) = \<lceil>m\<rceil>\<^sub>S\<^sub>< + \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st))"
  apply (simp add: R2_form usubst unrest)
  apply (rel_auto)
   apply (simp add: tocks_append)
  oops

text \<open> Pedro Comment: Renaming should be a relation rather than a function. \<close>

end