section {* Timed Reactive Designs *}

theory utp_timed_rea_designs
  imports utp_rea_designs
begin

subsection {* Traces with time constraints *}

text {* Timed traces extend the trace algebra with a constant \emph{dur} that gives the duration
  of a trace. *}

class time_trace = trace +
  fixes dur :: "'a \<Rightarrow> real"
  and idle :: "'a \<Rightarrow> bool"
  assumes dur_non_zero [simp]: "dur(t) \<ge> 0"
  and dur_empty [simp]: "dur(0) = 0"
  and dur_concat [simp]: "dur(x + y) = dur(x) + dur(y)"
  and idle_empty [simp]: "idle(0)"
  and idle_concat: "idle(x + y) \<longleftrightarrow> (idle(x) \<and> idle(y))"
begin

  lemma dur_mono: "x \<le> y \<Longrightarrow> dur(x) \<le> dur(y)"
    using local.le_iff_add by auto

  lemma dur_minus [simp]: "y \<le> x \<Longrightarrow> dur(x - y) = dur(x) - dur(y)"
    by (metis add.commute add_diff_cancel_right' diff_add_cancel_left' dur_concat)

end

class dtime_trace = time_trace +
  assumes dur_discrete: "dur(t) \<in> \<nat>"
begin

  definition ddur :: "'a \<Rightarrow> nat" where
  "ddur(x) = nat(floor(dur(x)))"

  lemma dur_via_ddur: "dur(x) = real(ddur(x))"
    by (metis Nats_cases ddur_def floor_of_nat local.dur_discrete nat_int)

  lemma ddur_empty [simp]: "ddur(0) = 0"
    by (simp add: ddur_def)

  lemma ddur_concat [simp]: "ddur(x + y) = ddur(x) + ddur(y)"
    by (metis dur_via_ddur local.dur_concat of_nat_add of_nat_eq_iff)

  lemma ddur_mono: "x \<le> y \<Longrightarrow> ddur(x) \<le> ddur(y)"
    using dur_via_ddur local.dur_mono by auto

  lemma ddur_minus [simp]: "y \<le> x \<Longrightarrow> ddur(x - y) = ddur(x) - ddur(y)"
    by (metis cancel_ab_semigroup_add_class.add_diff_cancel_left' ddur_concat local.diff_add_cancel_left')

end

subsection {* Time expressions *}

syntax
  "_dur"         :: "logic \<Rightarrow> logic" ("dur\<^sub>u'(_')")
  "_time_length" :: "logic" ("\<^bold>l")
  "_idle"        :: "logic" ("is-idle")

translations
  "dur\<^sub>u(t)" == "CONST uop CONST dur t"
  "\<^bold>l"       == "dur\<^sub>u(tt)"
  "is-idle" == "CONST uop CONST idle tt"

subsection {* Signature *}

definition Wait :: "(real, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>,'t::time_trace,'\<alpha>) hrel_rsp" where
[upred_defs]: "Wait n = \<^bold>R\<^sub>s(true \<turnstile> (\<^bold>l <\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> is-idle) \<diamondop> (\<^bold>l =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> is-idle \<and> $st\<acute> =\<^sub>u $st))"

definition Interrupt :: "('\<sigma>,'t::time_trace,'\<alpha>) hrel_rsp \<Rightarrow> (real, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>,'t,'\<alpha>) hrel_rsp \<Rightarrow> ('\<sigma>,'t,'\<alpha>) hrel_rsp" (infixl "\<triangle>'(_')" 85) where
"P \<triangle>(n) Q = \<^bold>R\<^sub>s(((\<^bold>l \<le>\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R(P)) \<and> (\<^bold>l =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<Rightarrow> post\<^sub>R(P) wp\<^sub>R pre\<^sub>R(Q)))
               \<turnstile> ((peri\<^sub>R(P) \<and> \<^bold>l \<le>\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub><) \<or> ((peri\<^sub>R(P) \<and> \<^bold>l =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub><) ;; peri\<^sub>R(Q)))
               \<diamondop> ((post\<^sub>R(P) \<and> \<^bold>l \<le>\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub><) \<or> ((peri\<^sub>R(P) \<and> \<^bold>l =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub><) ;; post\<^sub>R(Q))))"

definition Deadline :: "('\<sigma>,'t::time_trace,'\<alpha>) hrel_rsp \<Rightarrow> (real, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>,'t,'\<alpha>) hrel_rsp" ("_ endsby'(_')" [90,0] 91) where
"P endsby(n) = P \<triangle>(n) Miracle"

end