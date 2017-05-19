section {* Timed Reactive Designs *}

theory utp_timed_rea_designs
  imports utp_rea_designs
begin

subsection {* Traces with time constraints *}

text {* Timed traces extend the trace algebra with a constant \emph{dur} that gives the duration
  of a trace. *}

class time_trace = ordered_cancel_monoid_diff +
  fixes dur :: "'a \<Rightarrow> real"
  and idle :: "'a \<Rightarrow> bool"
  assumes dur_non_zero [simp]: "dur(t) \<ge> 0"
  and dur_empty [simp]: "dur(0) = 0"
  and dur_concat [simp]: "dur(x + y) = dur(x) + dur(y)"
  (*and idle_empty [simp]: "idle(0)"*)
  and idle_concat: "idle(x + y) \<longleftrightarrow> (idle(x) \<and> idle(y))"(* \<longleftrightarrow> "*)
  and dur_idle_eq: "idle(x) \<equiv> \<forall>y. dur(x) = dur(y) \<longrightarrow> x \<le> y"
  (*and dur_idle_eq: "x \<le> y \<and> dur(x) = dur(y) \<and> idle(x) \<and> idle(y) \<Longrightarrow> x = y"*)
begin

  lemma dur_mono: "x \<le> y \<Longrightarrow> dur(x) \<le> dur(y)"
    using local.le_iff_add by auto

  lemma dur_minus [simp]: "y \<le> x \<Longrightarrow> dur(x - y) = dur(x) - dur(y)"
    by (metis add.commute add_diff_cancel_right' diff_add_cancel_left' dur_concat)

  lemma idle_diff: "x \<le> y \<and> idle(x) \<and> idle(y) \<Longrightarrow> idle(y - x)"
    using local.diff_add_cancel_left' local.idle_concat by fastforce
  
  lemma idle_empty[simp]: "idle(0)"
    by (simp add: local.dur_idle_eq)

  lemma dur_idle_imp: "x \<le> y \<and> dur(x) = dur(y) \<and> idle(x) \<and> idle(y) \<Longrightarrow> x = y"
    by (metis local.dur_idle_eq local.le_is_monoid_le local.monoid_le_antisym)

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
  
abbreviation Skip :: "('\<sigma>,'t::time_trace,'\<alpha>) hrel_rsp" where
"Skip \<equiv> II\<^sub>R"
  
definition Wait :: "(real, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>,'t::time_trace,'\<alpha>) hrel_rsp" where
[upred_defs]: "Wait n = \<^bold>R\<^sub>s(true \<turnstile> (\<^bold>l <\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> is-idle) \<diamondop> (\<^bold>l =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> is-idle \<and> $st\<acute> =\<^sub>u $st \<and> \<lceil>II\<rceil>\<^sub>R ))"
  
definition Interrupt :: "('\<sigma>,'t::time_trace,'\<alpha>) hrel_rsp \<Rightarrow> (real, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>,'t,'\<alpha>) hrel_rsp \<Rightarrow> ('\<sigma>,'t,'\<alpha>) hrel_rsp" (infixl "\<triangle>'(_')" 85) where
"P \<triangle>(n) Q = \<^bold>R\<^sub>s(((\<^bold>l \<le>\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R(P)) \<and> (\<^bold>l =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<Rightarrow> post\<^sub>R(P) wp\<^sub>R pre\<^sub>R(Q)))
               \<turnstile> ((peri\<^sub>R(P) \<and> \<^bold>l \<le>\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub><) \<or> ((peri\<^sub>R(P) \<and> \<^bold>l =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub><) ;; peri\<^sub>R(Q)))
               \<diamondop> ((post\<^sub>R(P) \<and> \<^bold>l \<le>\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub><) \<or> ((peri\<^sub>R(P) \<and> \<^bold>l =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub><) ;; post\<^sub>R(Q))))"

definition Deadline :: "('\<sigma>,'t::time_trace,'\<alpha>) hrel_rsp \<Rightarrow> (real, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>,'t,'\<alpha>) hrel_rsp" ("_ endsby'(_')" [90,0] 91) where
"P endsby(n) = P \<triangle>(n) Miracle"


lemma Skip_def: "Skip = \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st \<and> \<lceil>II\<rceil>\<^sub>R ))"
  by (simp add: srdes_skip_def, rel_auto)
      
lemma l_zero_is_idle_eq_tr:
  fixes P :: "('\<sigma>,'t::time_trace,'\<alpha>) hrel_rsp"
  assumes "P is R1"
  shows "`(P \<and> \<^bold>l =\<^sub>u \<lceil>0\<rceil>\<^sub>S\<^sub>< \<and> is-idle) \<Rightarrow> ($tr\<acute> =\<^sub>u $tr)`"
  using assms 
  apply pred_auto
  by (metis (no_types, lifting) dur_empty dur_idle_eq dur_idle_imp idle_empty minus_zero_eq)

lemma Wait_0: "Wait 0 = Skip"
proof -
  have "Wait 0 = \<^bold>R\<^sub>s(true \<turnstile> (\<^bold>l <\<^sub>u \<lceil>0\<rceil>\<^sub>S\<^sub>< \<and> is-idle) \<diamondop> (\<^bold>l =\<^sub>u \<lceil>0\<rceil>\<^sub>S\<^sub>< \<and> is-idle \<and> $st\<acute> =\<^sub>u $st \<and> \<lceil>II\<rceil>\<^sub>R ))"
    by pred_auto
  also have "... = \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> (\<^bold>l =\<^sub>u \<lceil>0\<rceil>\<^sub>S\<^sub>< \<and> is-idle \<and> $st\<acute> =\<^sub>u $st \<and> \<lceil>II\<rceil>\<^sub>R ))"
    apply pred_simp
    using dur_mono by fastforce
  also have "... = \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st \<and> \<lceil>II\<rceil>\<^sub>R ))"
    apply pred_auto
    apply (simp add: dur_idle_eq dur_idle_imp)
    using minus_zero_eq by blast
  also have "... = Skip"
    by (simp add: SRD_srdes_skip Skip_def)
  finally show ?thesis .
qed
  
lemma Wait_is_R2: "Wait m is R2"
  by (simp add: Healthy_def' R1_R2c_is_R2 R2_idem RHS_def Wait_def)
  
lemma P_seq_R1_false: "P ;; R1 false = false"
  by (simp add: R1_false)
    
lemma R1_false_seq_P: "R1 false ;; P = false"
  by (simp add: R1_false)
    
end