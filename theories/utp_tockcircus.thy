section \<open> tock-Circus \<close>

theory utp_tockcircus
imports "UTP-Reactive-Designs.utp_rea_designs" "rcircus/Refusal_Tests"
begin recall_syntax

text \<open> We try and characterise a tock-CSP like model using the standard Circus pattern and adapting
  the CML model. First we represent traces. \<close>

datatype '\<theta> tev = Tock "'\<theta> set" | Evt '\<theta>

text \<open> We don't need a tick event, because this is handled by the $ok$ flag. Nor do we need to
  separate refusals and tocks. A refusal in tock-CSP (as I understand) can occur either (1) just
  before a tock occurs, or (2) at the end of a trace. We gain the former by embedding refusals
  in a tock (as in CML). We gain the latter by including the $ref'$ variable as in Circus. We encode
  the healthiness condition that a tock can't occur in a refusal before a tock event using
  the type system. \<close>

alphabet ('\<sigma>, '\<phi>) tc_vars = "('\<phi> list, '\<sigma>) rsp_vars" +
  ref :: "'\<phi> refusal"

text \<open> The $ref$ variable is not simply a set, but a set augmented with the @{term \<bullet>} that denotes
  stability. We need this because tick-tock traces can end without a refusal. \<close>

type_synonym ('\<sigma>,'\<theta>) taction  = "('\<sigma>, '\<theta> tev) tc_vars hrel"

fun events :: "'\<theta> tev list \<Rightarrow> '\<theta> tev list" where
"events [] = []" |
"events (Tock A # t) = events t" |
"events (Evt x # t) = (Evt x # events t)"

lemma events_append [simp]: "events (xs @ ys) = events(xs) @ events(ys)"
  apply (induct xs, simp_all)
  apply (rename_tac x xs)
  apply (case_tac x)
  apply (simp_all)
done

fun tocks :: "'\<theta> tev list \<Rightarrow> '\<theta> tev list" where
"tocks [] = []" |
"tocks (Tock A # xs) = Tock A # tocks xs" |
"tocks (Evt x # xs) = tocks xs"

fun refusals :: "'\<theta> tev list \<Rightarrow> '\<theta> set" where
"refusals [] = {}" |
"refusals (Tock A # t) = A \<union> refusals t" |
"refusals (Evt x # t) = refusals t"

fun idleprefix :: "'\<theta> tev list \<Rightarrow> '\<theta> tev list" where
"idleprefix [] = []" |
"idleprefix (Tock A # t) = (Tock A # idleprefix t)" |
"idleprefix (Evt x # t) = []"

definition "idlesuffix = idleprefix \<circ> rev"

syntax
  "_events"     :: "logic \<Rightarrow> logic" ("events\<^sub>u'(_')")
  "_tocks"      :: "logic \<Rightarrow> logic" ("tocks\<^sub>u'(_')")
  "_refusals"   :: "logic \<Rightarrow> logic" ("refusals\<^sub>u'(_')")
  "_idleprefix" :: "logic \<Rightarrow> logic" ("idleprefix\<^sub>u'(_')")
  "_idlesuffix" :: "logic \<Rightarrow> logic" ("idlesuffix\<^sub>u'(_')")
  "_ev"         :: "logic \<Rightarrow> logic" ("ev\<^sub>u'(_')")
  "_tock"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("tock\<^sub>u'(_,_')")

translations
  "events\<^sub>u(t)" == "CONST uop CONST events t"
  "tocks\<^sub>u(t)" == "CONST uop CONST tocks t"
  "refusals\<^sub>u(t)" == "CONST uop CONST refusals t"
  "idleprefix\<^sub>u(t)" == "CONST uop CONST idleprefix t"
  "idlesuffix\<^sub>u(t)" == "CONST uop CONST idlesuffix t"
  "ev\<^sub>u(e)" == "CONST uop CONST Evt e"
  "tock\<^sub>u(t,A)" == "CONST bop CONST Tock t A"

definition Div :: "('\<sigma>,'\<theta>) taction" where
[rdes_def]: "Div = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> U($tr\<acute> = $tr \<and> $ref\<acute> = \<bullet>) \<diamondop> false)"

text \<open> This is the same as Circus $Skip$, except that it includes a quiescent state. \<close>

definition Skip :: "('\<sigma>,'\<theta>) taction" where
[rdes_def]: "Skip = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> U($tr\<acute> = $tr \<and> $ref\<acute> = \<bullet>) \<diamondop> U($tr\<acute> = $tr \<and> $st\<acute> = $st))"

definition Stop :: "('\<sigma>,'\<theta>) taction" where
[rdes_def]: "Stop = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> U(R1(events(&tt) = [])) \<diamondop> false)"

definition Stop\<^sub>U :: "('\<sigma>,'\<theta>) taction" where
[rdes_def]: "Stop\<^sub>U = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> U($tr\<acute> = $tr) \<diamondop> false)"

lemma [closure]: "U($tr\<acute> = $tr \<and> $ref\<acute> = \<bullet>) is RR"
  by (rel_auto)

lemma [closure]: "U($tr\<acute> = $tr \<and> $st\<acute> = $st) is RR"
  apply (rel_auto)
  using minus_zero_eq by blast

lemma [closure]: "U(R1(events(&tt) = [])) is RR"
  by (rel_auto)

lemma "Div ;; Skip = Div"
  by (rdes_eq)

lemma "Skip ;; Skip = Skip"
  by (rdes_eq)

lemma "Skip ;; Stop = Stop"
  by (rdes_eq)

lemma "Stop \<sqsubseteq> Div"
  by (rdes_refine)

end