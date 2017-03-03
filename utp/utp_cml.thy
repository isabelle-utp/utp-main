section {* COMPASS Modelling Language *}

theory utp_cml
imports utp_rea_designs
begin

subsection {* Preliminaries *}

datatype '\<theta> tevent = Tock "'\<theta> set" | Event '\<theta>

type_synonym ('\<theta>, '\<alpha>) alpha_cml_scheme = "('\<theta> tevent list, '\<alpha>) alpha_rp_scheme"

type_synonym ('\<theta>,'\<alpha>) alphabet_cml  = "('\<theta>,'\<alpha>) alpha_cml_scheme alphabet"
type_synonym ('\<theta>,'\<alpha>,'\<beta>) relation_cml  = "(('\<theta>,'\<alpha>) alphabet_cml, ('\<theta>,'\<beta>) alphabet_cml) relation"
type_synonym ('a,'\<theta>,'\<alpha>,'\<beta>) expr_cml  = "('a, ('\<theta>,'\<alpha>) alphabet_cml \<times> ('\<theta>,'\<beta>) alphabet_cml) uexpr"
type_synonym ('\<theta>,'\<alpha>) hrelation_cml  = "(('\<theta>,'\<alpha>) alphabet_cml, ('\<theta>,'\<alpha>) alphabet_cml) relation"
type_synonym ('\<theta>,'\<sigma>) predicate_cml  = "('\<theta>,'\<sigma>) alphabet_cml upred"


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

fun tocks :: "'\<theta> tevent list \<Rightarrow> '\<theta> tevent list" where
"tocks [] = []" |
"tocks (Tock A # xs) = Tock A # tocks xs" |
"tocks (Event x # xs) = tocks xs"

fun refusals :: "'\<theta> tevent list \<Rightarrow> '\<theta> set" where
"refusals [] = {}" |
"refusals (Tock A # t) = A \<union> refusals t" |
"refusals (Event x # t) = refusals t"

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
  "tock\<^sub>u(t,A)" == "CONST bop CONST Tock t A"

subsection {* Signature *}

abbreviation trace :: "('\<theta> tevent list,'\<theta>,'\<alpha>,'\<beta>) expr_cml" ("tt") where
"tt \<equiv> $tr\<acute> - $tr"

abbreviation time_length :: "_" ("\<^bold>l")
where "\<^bold>l \<equiv> #\<^sub>u(tocks\<^sub>u(tt))"

translations
  "tt" <= "CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr))"

definition "Stop = RH(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle>) \<diamondop> false)"

definition "Prefix a = RH(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> a \<notin>\<^sub>u refusals\<^sub>u(tt))
                               \<diamondop> (tt =\<^sub>u idleprefix\<^sub>u(tt) ^\<^sub>u \<langle>ev\<^sub>u(a)\<rangle>
                                  \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R \<and> a \<notin>\<^sub>u refusals\<^sub>u(tt)))"

definition "Wait n = RH(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) <\<^sub>u \<lceil>n\<rceil>\<^sub>R\<^sub><)
                             \<diamondop> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>n\<rceil>\<^sub>R\<^sub><
                                 \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))"

abbreviation hseqr :: "'\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" (infixr ";;\<^sub>h" 15) where
"(P ;;\<^sub>h Q) \<equiv> ((P::'\<alpha> hrelation) ;; (Q::'\<alpha> hrelation))"

lemma rea_lift_skip_alpha [alpha]: "\<lceil>II\<rceil>\<^sub>R = ($\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)"
  by (rel_auto)

lemma length_list_minus [simp]: "ys \<le> xs \<Longrightarrow> length(xs - ys) = length(xs) - length(ys)"
  by (auto simp add: minus_list_def less_eq_list_def)

lemma Wait_0: "Wait 0 = II\<^sub>r"
proof -
  have "Wait 0 = RH (true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> 0 >\<^sub>u #\<^sub>u(tt)) \<diamondop> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u 0 \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))"
    (is "?lhs = RH(?P \<turnstile> ?Q \<diamondop> ?R)")
    by (simp add: Wait_def alpha)
  also have "... = RH (true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))"
  proof -
    have 1:"?Q = false"
      by (pred_auto)
    have 2:"R1(?R) = ($tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)"
      apply (rel_auto) using list_minus_anhil by blast
    show ?thesis
      by (metis (no_types, lifting) "1" "2" R1_false R1_wait'_cond RH_design_export_R1)
  qed
  also have "... = II\<^sub>r"
    by (simp add: skip_rea_reactive_tri_design')
  finally show ?thesis .
qed

lemma Wait_m_plus_n: "(Wait m ;; Wait n) = (Wait (m + n))"
proof -
  have 1: "(R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) ;;\<^sub>h R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(tt))) =
         R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<rceil>\<^sub>R\<^sub>< \<le>\<^sub>u #\<^sub>u(tt) \<and> #\<^sub>u(tt) <\<^sub>u \<lceil>m + n\<rceil>\<^sub>R\<^sub><)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R ;;\<^sub>h
                                  events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: R2_seqr_form usubst unrest)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> (#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R ;;\<^sub>h
                                  \<lceil>n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle>) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: seqr_pre_out unrest conj_assoc, simp add: conj_comm)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> (#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R ;;\<^sub>h
                                  \<lceil>n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)) \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: seqr_post_out unrest conj_assoc)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R ;;\<^sub>h \<lceil>n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)) \<and>
                                      events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (meson shEx_cong utp_pred.inf.left_commute)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (\<lceil>\<lceil>#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u m\<rceil>\<^sub>< \<and> II ;;\<^sub>h \<lceil>n\<rceil>\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)\<rceil>\<^sub>R) \<and>
                                      events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: alpha)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (\<lceil>II \<and> \<lceil>#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u m\<rceil>\<^sub>> ;;\<^sub>h \<lceil>n\<rceil>\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)\<rceil>\<^sub>R) \<and>
                                      events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: pre_skip_post)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (\<lceil>\<lceil>#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u m\<rceil>\<^sub>< \<and> \<lceil>n\<rceil>\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)\<rceil>\<^sub>R) \<and>
                                      events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: seqr_pre_transfer unrest)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> \<lceil>n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)) \<and>
                                      events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: alpha)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tt\<^sub>0 \<bullet> #\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> \<lceil>n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(drop\<^sub>u(#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>), \<guillemotleft>tt\<^sub>0\<guillemotright>)) \<and>
                                      events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright> \<and>
                                      \<guillemotleft>tt\<^sub>1\<guillemotright> =\<^sub>u take\<^sub>u(#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>), \<guillemotleft>tt\<^sub>0\<guillemotright>) \<and> \<guillemotleft>tt\<^sub>2\<guillemotright> =\<^sub>u drop\<^sub>u(#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>), \<guillemotleft>tt\<^sub>0\<guillemotright>))"
      by ((rule shEx_cong)+, rel_auto)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tt\<^sub>0 \<bullet> \<lceil>n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(drop\<^sub>u(\<lceil>m\<rceil>\<^sub>R\<^sub><, \<guillemotleft>tt\<^sub>0\<guillemotright>)) \<and>
                                      events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and>
                                      \<guillemotleft>tt\<^sub>1\<guillemotright> =\<^sub>u take\<^sub>u(\<lceil>m\<rceil>\<^sub>R\<^sub><, \<guillemotleft>tt\<^sub>0\<guillemotright>) \<and> \<guillemotleft>tt\<^sub>2\<guillemotright> =\<^sub>u drop\<^sub>u(\<lceil>m\<rceil>\<^sub>R\<^sub><, \<guillemotleft>tt\<^sub>0\<guillemotright>) \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub><)"
      by ((rule shEx_cong)+, rel_auto, simp_all add: min_absorb2)
    also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> \<lceil>m + n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub><)"
      by (rel_auto)
    also have "... = R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<rceil>\<^sub>R\<^sub>< \<le>\<^sub>u #\<^sub>u(tt) \<and> #\<^sub>u(tt) <\<^sub>u \<lceil>m + n\<rceil>\<^sub>R\<^sub><)"
      by (simp add: R2_form usubst unrest, rel_auto)
    finally show ?thesis .
  qed
  have 2:"(R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) ;; R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)) =
                 R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m + n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R ;;\<^sub>h events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<lceil>n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)
                         \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: R2_seqr_form usubst unrest)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R ;;\<^sub>h #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<lceil>n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (rel_auto)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (\<lceil>\<lceil>#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u m\<rceil>\<^sub>< \<and> II ;;\<^sub>h #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<lceil>n\<rceil>\<^sub>< \<and> II\<rceil>\<^sub>R) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: alpha)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (\<lceil>\<lceil>#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u m\<rceil>\<^sub>< \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<lceil>n\<rceil>\<^sub>< \<and> II\<rceil>\<^sub>R) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: pre_skip_post, simp add: seqr_pre_transfer unrest)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<lceil>n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: alpha)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tt\<^sub>0 \<bullet> (#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<lceil>n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (rel_auto)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tt\<^sub>0 \<bullet> (#\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<lceil>n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and>
                            \<guillemotleft>tt\<^sub>1\<guillemotright> =\<^sub>u take\<^sub>u(\<lceil>m\<rceil>\<^sub>R\<^sub><, \<guillemotleft>tt\<^sub>0\<guillemotright>) \<and> \<guillemotleft>tt\<^sub>2\<guillemotright> =\<^sub>u drop\<^sub>u(\<lceil>m\<rceil>\<^sub>R\<^sub><, \<guillemotleft>tt\<^sub>0\<guillemotright>))"
      by ((rule shEx_cong)+, rel_auto)
    also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (#\<^sub>u(drop\<^sub>u(\<lceil>m\<rceil>\<^sub>R\<^sub><, \<guillemotleft>tt\<^sub>0\<guillemotright>)) =\<^sub>u \<lceil>n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub><)"
      by (rel_auto)
    also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (#\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) - \<lceil>m\<rceil>\<^sub>R\<^sub>< =\<^sub>u \<lceil>n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub><)"
      by (rel_auto)
    also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (#\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< + \<lceil>n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) \<and>
                            events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> #\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub><)"
      by (rel_auto)
    also have "... = ?rhs"
      by (simp add: R2_form usubst unrest, rel_auto)
    finally show ?thesis .
  qed
  show ?thesis
  proof -
    have "(Wait m ;; Wait n) =
          RH (true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(tt) \<or> R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> \<lceil>m + n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(tt)))
                   \<diamondop> R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m + n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))"
      by (simp add: Wait_def RH_tri_design_composition unrest R2s_true R1_false R2_def[THEN sym] 1 2)
    also have "... =
          RH (true \<turnstile> R2((events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(tt) \<or> R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> \<lceil>m + n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(tt)))
                   \<diamondop> R2(events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m + n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)))"
      using RH_design_export_R2 by blast
    also have "... =
          RH (true \<turnstile> R2((events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(tt) \<or> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> \<lceil>m + n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(tt)))
                   \<diamondop> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m + n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)))"
      by (simp add: R2_wait'_cond R2_idem R2_disj)
    also have "... =
          RH (true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(tt) \<or> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> \<lceil>m + n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(tt)))
                   \<diamondop> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m + n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))" (is "?lhs = RH(?P \<turnstile> ?Q \<diamondop> ?R)")
      by (metis (mono_tags, hide_lams) R2_def RH_design_export_R1 RH_design_export_R2s)
    also have "... = RH (true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m + n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(tt)) \<diamondop> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>m + n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))"
    proof -
      have 1:"?Q = (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m + n\<rceil>\<^sub>R\<^sub>< >\<^sub>u #\<^sub>u(tt))"
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