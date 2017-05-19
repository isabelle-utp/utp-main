section {* COMPASS Modelling Language *}

theory utp_cml
imports utp_rea_designs
begin

subsection {* Preliminaries *}

datatype '\<theta> tevent = Tock "'\<theta> set" | Event '\<theta>

type_synonym ('\<sigma>,'\<theta>) st_cml      = "('\<sigma>, '\<theta> tevent list, unit) rsp"
type_synonym ('\<sigma>,'\<theta>) cmlact      = "('\<sigma>,'\<theta>) st_cml hrel"
type_synonym ('a,'\<sigma>,'\<theta>) expr_cml = "('a, ('\<sigma>,'\<theta>) st_cml \<times> ('\<sigma>,'\<theta>) st_cml) uexpr"

fun events :: "'\<theta> tevent list \<Rightarrow> '\<theta> tevent list" where
"events [] = []" |
"events (Tock A # t) = events t" |
"events (Event x # t) = (Event x # events t)"

lemma events_append [simp]: "events (xs @ ys) = events(xs) @ events(ys)"
  apply (induct xs, simp_all)
  apply (rename_tac x xs)
  apply (case_tac x)
  apply (simp_all)
  done
    
lemma events_mono: "(P \<le> Q) \<Longrightarrow> (events(P) \<le> events(Q))"
  apply (induct P rule:events.induct)
  apply simp+
  apply auto
  apply (metis (no_types, lifting) Prefix_Order.prefixE Prefix_Order.prefix_prefix events.simps(2) events_append order_refl)
  by (metis (mono_tags, lifting) Prefix_Order.prefixE Prefix_Order.prefix_prefix events.simps(3) events_append order_refl)    

fun tocks :: "'\<theta> tevent list \<Rightarrow> '\<theta> tevent list" where
"tocks [] = []" |
"tocks (Tock A # xs) = Tock A # tocks xs" |
"tocks (Event x # xs) = tocks xs"

fun refusals :: "'\<theta> tevent list \<Rightarrow> '\<theta> set" where
"refusals [] = {}" |
"refusals (Tock A # t) = A \<union> refusals t" |
"refusals (Event x # t) = refusals t"

lemma refusals_dist: "refusals(a @ t) = (refusals(a) \<union> refusals(t))"
  apply (induct a)
  apply (simp_all)
  apply (case_tac a1)
  apply simp_all
  by auto
    
lemma refusals_ord_subset: "(P \<le> Q) \<Longrightarrow> (refusals(P) \<subseteq> refusals(Q))"
  apply (induct P)
  apply (simp_all)
  apply (case_tac a)
  apply simp_all
  apply auto
  apply (metis Prefix_Order.prefixE UnI1 refusals.simps(2) refusals_dist)
  apply (metis Prefix_Order.prefixE UnCI refusals.simps(2) refusals_dist)
  by (metis Prefix_Order.prefixE UnI1 refusals.simps(3) refusals_dist)
 
lemma refusals_prefix: "t \<le> u \<and> a \<in> refusals(t) \<Longrightarrow> a \<in> refusals(u)"
  using refusals_ord_subset by auto

fun idleprefix :: "'\<theta> tevent list \<Rightarrow> '\<theta> tevent list" where
"idleprefix [] = []" |
"idleprefix (Tock A # t) = (Tock A # idleprefix t)" |
"idleprefix (Event x # t) = []"

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
  "ev\<^sub>u(e)" == "CONST uop CONST Event e"
  "tock\<^sub>u(t,A)" == "CONST bop CONST Tock t A" (* Why does this take two parameters?*)

subsection {* Signature *}

abbreviation time_length :: "(nat,'\<sigma>,'\<theta>) expr_cml" ("\<^bold>l")
where "\<^bold>l \<equiv> #\<^sub>u(tocks\<^sub>u(tt))"

abbreviation CML :: "(('\<sigma>, '\<phi>) st_cml \<times> ('\<sigma>, '\<phi>) st_cml) health"
where "CML \<equiv> SRD"

abbreviation Skip :: "('\<sigma>,'\<theta>) cmlact" where
"Skip \<equiv> II\<^sub>R"

abbreviation Assigns :: "'\<sigma> usubst \<Rightarrow> ('\<sigma>,'\<theta>) cmlact" ("\<langle>_\<rangle>\<^sub>C") where
"Assigns \<sigma> \<equiv> \<langle>\<sigma>\<rangle>\<^sub>R"

definition Stop :: "('\<sigma>,'\<theta>) cmlact" where
[upred_defs]: "Stop = \<^bold>R\<^sub>s(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle>) \<diamondop> false)"

definition DoCML :: "('\<theta>, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>,'\<theta>) cmlact" where
  [upred_defs]:
  "DoCML a = \<^bold>R\<^sub>s(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u refusals\<^sub>u(tt))
                      \<diamondop> (tt =\<^sub>u idleprefix\<^sub>u(tt) ^\<^sub>u \<langle>ev\<^sub>u(\<lceil>a\<rceil>\<^sub>S\<^sub><)\<rangle>
                         \<and> $st\<acute> =\<^sub>u $st \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u refusals\<^sub>u(tt)))"

definition Wait :: "(nat, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>,'\<theta>) cmlact" where
  [upred_defs]:
  "Wait n = \<^bold>R\<^sub>s(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) <\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub><)
                    \<diamondop> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub><
                       \<and> $st\<acute> =\<^sub>u $st))"

lemma length_list_minus [simp]: "ys \<le> xs \<Longrightarrow> length(xs - ys) = length(xs) - length(ys)"
  by (auto simp add: minus_list_def less_eq_list_def)

lemma Skip_def: "Skip = \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st))"
  by (simp add: srdes_skip_def, rel_auto)

lemma Wait_0: "Wait 0 = Skip"
proof -
  have "Wait 0 = \<^bold>R\<^sub>s(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> 0 >\<^sub>u #\<^sub>u(tt)) \<diamondop> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u 0 \<and> $st\<acute> =\<^sub>u $st))"
    (is "?lhs = \<^bold>R\<^sub>s(?P \<turnstile> ?Q \<diamondop> ?R)")
    by (simp add: Wait_def alpha)
  also have "... = \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st))"
  proof -
    have 1:"?Q = false"
      by (pred_auto)
    have 2:"R1(?R) = ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)"
      by (rel_auto, simp_all add: minus_zero_eq zero_list_def)
    show ?thesis
      by (metis (no_types, lifting) "1" "2" RHS_design_post_R1)
  qed
  also have "... = Skip"
    by (simp add: Skip_def)
  finally show ?thesis .
qed

lemma skip_lift_state [alpha]: "\<lceil>II\<rceil>\<^sub>S = ($st\<acute> =\<^sub>u $st)"
  by (rel_auto)

lemma Stop_left_zero:
  assumes "P is CML"
  shows "Stop ;; P = Stop"
proof -
  have "Stop ;; P = \<^bold>R\<^sub>s(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle>) \<diamondop> false) ;; \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    by (simp add: SRD_reactive_tri_design Stop_def assms)
  also have "... = \<^bold>R\<^sub>s (true \<turnstile> (\<exists> $st\<acute> \<bullet> events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle>) \<diamondop> false)"
    by (subst RHS_tri_design_composition, simp_all add: unrest R2s_true R1_false R2s_false)
  also have "... = \<^bold>R\<^sub>s (true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle>) \<diamondop> false)"
    by (simp add: ex_unrest unrest)
  finally show ?thesis
    by (simp add: Stop_def)
qed

lemma Wait_m_plus_n: "(Wait m ;; Wait n) = (Wait (m + n))"
proof -
  have 1: "(R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st) ;; R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(tt))) =
         R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<rceil>\<^sub>S\<^sub>< \<le>\<^sub>u #\<^sub>u(tt) \<and> #\<^sub>u(tt) <\<^sub>u \<lceil>m + n\<rceil>\<^sub>S\<^sub><)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (((events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st) ;;\<^sub>h
                                   (events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>))) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>))"
      by (simp add: R2_seqr_form usubst unrest)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> (#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st) ;;\<^sub>h
                                       (\<lceil>n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle>))) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: seqr_pre_out unrest conj_assoc, simp add: conj_comm)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> ((#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st) ;;\<^sub>h
                                  (\<lceil>n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>))) \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: seqr_post_out unrest conj_assoc)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st) ;;\<^sub>h (\<lceil>n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>))) \<and>
                                      events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (meson shEx_cong utp_pred.inf.left_commute)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (\<lceil>(\<lceil>#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u m\<rceil>\<^sub>< \<and> II) ;;\<^sub>h (\<lceil>n\<rceil>\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>))\<rceil>\<^sub>S) \<and>
                                      events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: alpha)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (\<lceil>(II \<and> \<lceil>#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u m\<rceil>\<^sub>>) ;;\<^sub>h (\<lceil>n\<rceil>\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>))\<rceil>\<^sub>S) \<and>
                                      events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: pre_skip_post)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (\<lceil>\<lceil>#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u m\<rceil>\<^sub>< \<and> \<lceil>n\<rceil>\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)\<rceil>\<^sub>S) \<and>
                                      events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: seqr_pre_transfer unrest)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)) \<and>
                                      events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: alpha)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tt\<^sub>0 \<bullet> #\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(drop\<^sub>u(#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>), \<guillemotleft>tt\<^sub>0\<guillemotright>)) \<and>
                                      events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and>
                                      \<guillemotleft>tt\<^sub>1\<guillemotright> =\<^sub>u take\<^sub>u(#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>), \<guillemotleft>tt\<^sub>0\<guillemotright>) \<and> \<guillemotleft>tt\<^sub>2\<guillemotright> =\<^sub>u drop\<^sub>u(#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>), \<guillemotleft>tt\<^sub>0\<guillemotright>))"
      by ((rule shEx_cong)+, rel_auto)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tt\<^sub>0 \<bullet> \<lceil>n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(drop\<^sub>u(\<lceil>m\<rceil>\<^sub>S\<^sub><, \<guillemotleft>tt\<^sub>0\<guillemotright>)) \<and>
                                      events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and>
                                      \<guillemotleft>tt\<^sub>1\<guillemotright> =\<^sub>u take\<^sub>u(\<lceil>m\<rceil>\<^sub>S\<^sub><, \<guillemotleft>tt\<^sub>0\<guillemotright>) \<and> \<guillemotleft>tt\<^sub>2\<guillemotright> =\<^sub>u drop\<^sub>u(\<lceil>m\<rceil>\<^sub>S\<^sub><, \<guillemotleft>tt\<^sub>0\<guillemotright>) \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub><)"
      by ((rule shEx_cong)+, rel_auto, simp_all add: min_absorb2)
    also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> \<lceil>m + n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub><)"
      by (rel_auto)
    also have "... = R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<rceil>\<^sub>S\<^sub>< \<le>\<^sub>u #\<^sub>u(tt) \<and> #\<^sub>u(tt) <\<^sub>u \<lceil>m + n\<rceil>\<^sub>S\<^sub><)"
      by (simp add: R2_form usubst unrest, rel_auto)
    finally show ?thesis .
  qed
  have 2:"(R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st) ;; R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st)) =
                 R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m + n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st) ;;\<^sub>h
                                   (events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st))
                         \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: R2_seqr_form usubst unrest)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st) ;;\<^sub>h (#\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st)) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (rel_auto)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (\<lceil>(\<lceil>#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u m\<rceil>\<^sub>< \<and> II) ;;\<^sub>h (#\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<lceil>n\<rceil>\<^sub>< \<and> II)\<rceil>\<^sub>S) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: alpha)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (\<lceil>\<lceil>#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u m\<rceil>\<^sub>< \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<lceil>n\<rceil>\<^sub>< \<and> II\<rceil>\<^sub>S) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: pre_skip_post, simp add: seqr_pre_transfer unrest)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: alpha)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tt\<^sub>0 \<bullet> (#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (rel_auto)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tt\<^sub>0 \<bullet> (#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and>
                            \<guillemotleft>tt\<^sub>1\<guillemotright> =\<^sub>u take\<^sub>u(\<lceil>m\<rceil>\<^sub>S\<^sub><, \<guillemotleft>tt\<^sub>0\<guillemotright>) \<and> \<guillemotleft>tt\<^sub>2\<guillemotright> =\<^sub>u drop\<^sub>u(\<lceil>m\<rceil>\<^sub>S\<^sub><, \<guillemotleft>tt\<^sub>0\<guillemotright>))"
      by ((rule shEx_cong)+, rel_auto)
    also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (#\<^sub>u(drop\<^sub>u(\<lceil>m\<rceil>\<^sub>S\<^sub><, \<guillemotleft>tt\<^sub>0\<guillemotright>)) =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub><)"
      by (rel_auto)
    also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (#\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) - \<lceil>m\<rceil>\<^sub>S\<^sub>< =\<^sub>u \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub><)"
      by (rel_auto)
    also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (#\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< + \<lceil>n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub><)"
      by (rel_auto)
    also have "... = ?rhs"
      by (simp add: R2_form usubst unrest, rel_auto)
    finally show ?thesis .
  qed
  show ?thesis
  proof -
    have "(Wait m ;; Wait n) =
          \<^bold>R\<^sub>s (true \<turnstile> ((\<exists> $st\<acute> \<bullet> events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(tt)) \<or> R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>m + n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(tt)))
                   \<diamondop> R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m + n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st))"
      by (simp add: Wait_def RHS_tri_design_composition unrest R2s_true R1_false R2_def[THEN sym] 1 2)
    also have "... =
          \<^bold>R\<^sub>s (true \<turnstile> R2(((\<exists> $st\<acute> \<bullet> events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(tt)) \<or> R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>m + n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(tt)))
                   \<diamondop> R2(events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m + n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st)))"
      using RHS_design_export_R2 by blast
    also have "... =
          \<^bold>R\<^sub>s (true \<turnstile> R2((events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(tt) \<or> R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>m + n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(tt)))
                   \<diamondop> R2(events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m + n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st)))"
      by (simp add: ex_unrest unrest)
    also have "... =
          \<^bold>R\<^sub>s (true \<turnstile> R2((events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(tt) \<or> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>m + n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(tt)))
                   \<diamondop> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m + n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st)))"
      by (simp add: R2_wait'_cond R2_idem R2_disj)
    also have "... =
          \<^bold>R\<^sub>s (true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(tt) \<or> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>m + n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(tt)))
                   \<diamondop> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m + n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st))" (is "?lhs = \<^bold>R\<^sub>s(?P \<turnstile> ?Q \<diamondop> ?R)")
      by (metis (mono_tags, hide_lams) R2_def RHS_design_export_R1 RHS_design_export_R2s)
    also have "... = \<^bold>R\<^sub>s (true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m + n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(tt)) \<diamondop> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m + n\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> =\<^sub>u $st))"
    proof -
      have 1:"?Q = (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m + n\<rceil>\<^sub>S\<^sub>< >\<^sub>u #\<^sub>u(tt))"
        by (pred_auto)
      show ?thesis
        by (simp add: 1)
    qed
    also have "... = Wait (m + n)"
      by (simp add: Wait_def)
    finally show ?thesis .
  qed
qed

end