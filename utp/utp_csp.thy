(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_cps.thy                                                          *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 8/12/2016 *)

section {* Theory of CSP *}

theory utp_csp
  imports utp_rea_designs utp_procedure
begin

subsection {* Preliminaries *}

record '\<phi> alpha_csp' =
  ref\<^sub>v :: "'\<phi> set"

declare alpha_csp'.splits [alpha_splits]

text {*
  The two locale interpretations below are a technicality to improve automatic
  proof support via the predicate and relational tactics. This is to enable the
  (re-)interpretation of state spaces to remove any occurrences of lens types
  after the proof tactics @{method pred_simp} and @{method rel_simp}, or any
  of their derivatives have been applied. Eventually, it would be desirable to
  automate both interpretations as part of a custom outer command for defining
  alphabets.
*}

interpretation alphabet_csp_prd:
  lens_interp "\<lambda>(ok, wait, tr, r). (ok, wait, tr, ref\<^sub>v r, more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation alphabet_csp_rel:
  lens_interp "\<lambda>(ok, ok', wait, wait', tr, tr', r, r'). (ok, ok',
  wait, wait', tr, tr', ref\<^sub>v r, ref\<^sub>v r', more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

type_synonym ('\<phi>, '\<alpha>) alpha_csp_scheme = "('\<phi> list, ('\<phi>, '\<alpha>) alpha_csp'_scheme) alpha_rp_scheme"

type_synonym ('\<phi>,'\<alpha>) alphabet_csp  = "('\<phi>,'\<alpha>) alpha_csp_scheme alphabet"
type_synonym ('\<phi>,'\<alpha>,'\<beta>) relation_csp  = "(('\<phi>,'\<alpha>) alphabet_csp, ('\<phi>,'\<beta>) alphabet_csp) relation"
type_synonym ('\<phi>,'\<alpha>) hrelation_csp  = "(('\<phi>,'\<alpha>) alphabet_csp, ('\<phi>,'\<alpha>) alphabet_csp) relation"
type_synonym ('\<phi>,'\<sigma>) predicate_csp  = "('\<phi>,'\<sigma>) alphabet_csp upred"
type_synonym '\<phi> csp = "('\<phi>, unit) hrelation_csp"

translations
  (type) "('\<phi>,'\<alpha>) alphabet_csp" <= (type) "('\<phi> list, ('b, '\<alpha>) alpha_csp'_scheme) alphabet_rp"

definition [uvar_defs]: "ref\<^sub>c = VAR ref\<^sub>v"
definition [uvar_defs]: "\<Sigma>\<^sub>c = VAR more"

declare alpha_csp'.splits [alpha_splits]

lemma ref\<^sub>c_vwb_lens [simp]: "vwb_lens ref\<^sub>c"
  by (unfold_locales, simp_all add: ref\<^sub>c_def)

lemma csp_vwb_lens [simp]: "vwb_lens \<Sigma>\<^sub>c"
  by (unfold_locales, simp_all add: \<Sigma>\<^sub>c_def)

definition [uvar_defs]: "ref = (ref\<^sub>c ;\<^sub>L \<Sigma>\<^sub>R)"
definition [uvar_defs]: "ref\<^sub>r = (ref\<^sub>c ;\<^sub>L \<Sigma>\<^sub>r)"
definition [uvar_defs]: "\<Sigma>\<^sub>C   = (\<Sigma>\<^sub>c ;\<^sub>L \<Sigma>\<^sub>R)"

lemma ref_vwb_lens [simp]: "vwb_lens ref"
  by (simp add: ref_def)

lemma csp_lens_vwb_lens [simp]: "vwb_lens \<Sigma>\<^sub>C"
  by (simp add: \<Sigma>\<^sub>C_def)

lemma ok_indep_ref [simp]: "ok \<bowtie> ref" "ok \<bowtie> tr"
  by (simp_all add: ref_def)

lemma tr_indep_ref [simp]: "tr \<bowtie> ref" "ref \<bowtie> tr"
  by (simp_all add: ref_def)

lemma csp_lens_indep_ok [simp]: "\<Sigma>\<^sub>C \<bowtie> ok" "ok \<bowtie> \<Sigma>\<^sub>C"
  by (simp_all add: \<Sigma>\<^sub>C_def)

lemma csp_lens_indep_wait [simp]: "\<Sigma>\<^sub>C \<bowtie> wait" "wait \<bowtie> \<Sigma>\<^sub>C"
  by (simp_all add: \<Sigma>\<^sub>C_def)

abbreviation lift_csp :: "_ \<Rightarrow> _" ("\<lceil>_\<rceil>\<^sub>C") where
"\<lceil>P\<rceil>\<^sub>C \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>C \<times>\<^sub>L \<Sigma>\<^sub>C)"

(* Instantiate the vstore for CSP alphabets *)

instantiation alpha_csp'_ext :: (type,vst) vst
begin
  definition vstore_lens_alpha_csp'_ext :: "vstore \<Longrightarrow> ('a, 'b) alpha_csp'_scheme" where
  "vstore_lens_alpha_csp'_ext = \<V> ;\<^sub>L \<Sigma>\<^sub>c"
instance
  by (intro_classes, simp add: vstore_lens_alpha_csp'_ext_def)
end

text {* The following function defines the parallel composition of two CSP event traces *}

fun tr_par ::
  "'\<theta> event set \<Rightarrow> '\<theta> event list \<Rightarrow> '\<theta> event list \<Rightarrow> '\<theta> event list set" where
"tr_par cs [] [] = {[]}" |
"tr_par cs (e # t) [] = (if e \<in> cs then {[]} else {[e]} \<^sup>\<frown> (tr_par cs t []))" |
"tr_par cs [] (e # t) = (if e \<in> cs then {[]} else {[e]} \<^sup>\<frown> (tr_par cs [] t))" |
"tr_par cs (e\<^sub>1 # t\<^sub>1) (e\<^sub>2 # t\<^sub>2) =
  (if e\<^sub>1 = e\<^sub>2
    then
      if e\<^sub>1 \<in> cs (* \<and> e\<^sub>2 \<in> cs *)
        then {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 t\<^sub>2)
        else
          ({[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2))) \<union>
          ({[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2))
    else
      if e\<^sub>1 \<in> cs then
        if e\<^sub>2 \<in> cs then {[]}
        else
          {[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2)
      else
        if e\<^sub>2 \<in> cs then
          {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2))
        else
          {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2)) \<union>
          {[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2))"

syntax
  "_utrpar" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("trpar\<^sub>u'(_,_,_')")

translations
  "trpar\<^sub>u(cs,t1,t2)" == "CONST trop CONST tr_par cs t1 t2"

subsection {* Extra healthiness conditions and dependencies *}

definition [upred_defs]: "STOP = CSP1($ok\<acute> \<and> R3c($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition SKIP :: "'\<phi> csp" where
[upred_defs]: "SKIP = RH(\<exists> $ref \<bullet> CSP1(II))"

definition [upred_defs]: "CSP3(P) = (SKIP ;; P)"

definition [upred_defs]: "CSP4(P) = (P ;; SKIP)"

subsection {* Process constructs *}

definition [upred_defs]: "Stop = RH(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition [upred_defs]: "Skip = RH(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> (\<not> $wait\<acute>) \<and> \<lceil>II\<rceil>\<^sub>R))"

definition Guard :: "('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp" (infix "&\<^sub>u" 65)
where "g &\<^sub>u A = RH((g \<Rightarrow> \<not> A\<^sup>f\<^sub>f) \<turnstile> ((g \<and> A\<^sup>t\<^sub>f) \<or> ((\<not> g) \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"

definition ExtChoice :: "('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp" (infixl "\<box>" 65)
where "A\<^sub>1 \<box> A\<^sub>2 = RH(\<not> A\<^sub>1\<^sup>f\<^sub>f \<and> \<not> A\<^sub>2\<^sup>f\<^sub>f \<turnstile> (A\<^sub>1\<^sup>t\<^sub>f \<and> A\<^sub>2\<^sup>t\<^sub>f) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> (A\<^sub>1\<^sup>t\<^sub>f \<or> A\<^sub>2\<^sup>t\<^sub>f))"

definition do\<^sub>u :: "('\<theta> event, ('\<theta>,'\<alpha>) alphabet_csp \<times> ('\<theta>,'\<alpha>) alphabet_csp) uexpr \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp" where
"do\<^sub>u(e) = ($tr\<acute> =\<^sub>u $tr \<and> e \<notin>\<^sub>u $ref\<acute> \<triangleleft> $wait\<acute> \<triangleright> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>e\<rangle>)"

definition OutputCSP ::
  "('a, '\<theta>) chan \<Rightarrow>
    ('a, ('\<theta>,'\<alpha>) alphabet_csp \<times> ('\<theta>,'\<alpha>) alphabet_csp) uexpr \<Rightarrow>
    ('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow>
    ('\<theta>, '\<alpha>) hrelation_csp" where
"OutputCSP c v A = (RH(true \<turnstile> do\<^sub>u (c, v)\<^sub>e) ;; A)"

definition do\<^sub>I ::
  "('a, '\<theta>) chan \<Rightarrow>
    ('a, ('\<theta>,'\<alpha>) alphabet_csp) uvar \<Rightarrow>
    ('a \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp) \<Rightarrow>
    ('\<theta>, '\<alpha>) hrelation_csp"
where "do\<^sub>I c x P = (($tr\<acute> =\<^sub>u $tr \<and> {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> (c,\<guillemotleft>e\<guillemotright>)\<^sub>e}\<^sub>u \<inter>\<^sub>u $ref\<acute> =\<^sub>u {}\<^sub>u)
                   \<triangleleft> $wait\<acute> \<triangleright>
                   (($tr\<acute> - $tr) \<in>\<^sub>u {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> \<langle>(c,\<guillemotleft>e\<guillemotright>)\<^sub>e\<rangle>}\<^sub>u \<and> (c, $x\<acute>)\<^sub>e =\<^sub>u last\<^sub>u($tr\<acute>)))"

definition InputCSP ::
  "('a::{continuum,two}, '\<theta>) chan \<Rightarrow> _ \<Rightarrow>
    ('a \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp) \<Rightarrow>
    (_ \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp) \<Rightarrow>
    ('\<theta>, '\<alpha>) hrelation_csp"
where "InputCSP c x P A = (var\<^bsub>RDES\<^esub> x \<bullet> RH(true \<turnstile> do\<^sub>I c x P \<and> \<lceil>II\<rceil>\<^sub>R) ;; A(x))"

syntax
  "_csp_event"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow>\<^sub>u _" [80,79] 80)
  "_csp_output" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_!\<^sub>u'(_') \<rightarrow> _" [80,0,79] 80)
  "_csp_input"  :: "('a, '\<theta>) chan \<Rightarrow> id \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" ("_?\<^sub>u'(_ :/ _') \<rightarrow> _" [80,0,0,79] 80)

translations
  "c!\<^sub>u(v) \<rightarrow> A"     == "CONST OutputCSP c v A"
  "c \<rightarrow>\<^sub>u A"         == "CONST OutputCSP c ()\<^sub>u A"
  "c?\<^sub>u(x : P) \<rightarrow> A" => "CONST InputCSP c (CONST top_var (CONST MkDVar IDSTR(x))) (\<lambda> x. P) (\<lambda> x. A)"

term "c?\<^sub>u(x : true) \<rightarrow> (x := 1)"

text {* Merge predicate for CSP *}

definition CSPMerge' ("N\<^sub>C\<^sub>S\<^sub>P") where
  [upred_defs]:
  "CSPMerge'(cs) = (
      $ok\<acute> =\<^sub>u ($0-ok \<and> $1-ok) \<and>
      $wait\<acute> =\<^sub>u ($0-wait \<or> $1-wait) \<and>
      $ref\<acute> =\<^sub>u ($0-ref \<union>\<^sub>u $1-ref) \<and>
      ($tr\<acute> - $tr\<^sub><) \<in>\<^sub>u trpar\<^sub>u(\<guillemotleft>cs\<guillemotright>, $0-tr - $tr\<^sub><, $1-tr - $tr\<^sub><) \<and> 
      $0-tr \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u $1-tr \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and>
      $\<Sigma>\<^sub>C\<acute> =\<^sub>u $0-\<Sigma>\<^sub>C \<and> $\<Sigma>\<^sub>C\<acute> =\<^sub>u $1-\<Sigma>\<^sub>C)"

definition CSPMerge ("M\<^sub>C\<^sub>S\<^sub>P") where
  [upred_defs]: "CSPMerge(cs) = (N\<^sub>C\<^sub>S\<^sub>P(cs) ;; SKIP)"

definition ParCSP :: "'\<theta> csp \<Rightarrow> '\<theta> event set \<Rightarrow> '\<theta> csp \<Rightarrow> '\<theta> csp" (infixl "\<parallel>[_]\<^sub>C\<^sub>S\<^sub>P" 85)
where [upred_defs]: "P \<parallel>[cs]\<^sub>C\<^sub>S\<^sub>P Q = P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q"

definition [upred_defs]: "M_CSP_ok(cs) = (M\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>true,true,true/$ok\<^sub><,$0-ok,$1-ok\<rbrakk>"
definition [upred_defs]: "M_CSP_not_ok(cs) = (M\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>false,false,false/$ok\<^sub><,$0-ok,$1-ok\<rbrakk>"

(*
lemma 
  assumes "P is CSP2" "Q is CSP2"
  shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>t\<^sub>f = (P\<^sup>t\<^sub>f \<parallel>\<^bsub>M_CSP_ok(cs)\<^esub> Q\<^sup>t\<^sub>f)"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>t\<^sub>f = (((P ;; U0) \<and> (Q ;; U1) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<^sub>f"
    by (simp add: ParCSP_def par_by_merge_def)
  also have "... = (((P ;; U0) \<and> (Q ;; U1) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) \<^sub>f ;; M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t"
    by (simp add: ok'_t_seqr_right wait_f_seqr_left)
  also have "... = (((P ;; U0) \<^sub>f \<and> (Q ;; U1) \<^sub>f \<and> ($\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) \<^sub>f) ;; M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t"
    by subst_tac
  also have "... = (((P \<^sub>f ;; U0)  \<and> (Q \<^sub>f ;; U1) \<and> ($\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) \<^sub>f) ;; M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t"
    by (simp add: wait_f_seqr_left)
  also have "... = (((P \<^sub>f ;; U0)  \<and> (Q \<^sub>f ;; U1) \<and> ($\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) \<^sub>f) ;; (N\<^sub>C\<^sub>S\<^sub>P cs ;; SKIP))\<^sup>t"
    by (simp add: CSPMerge_def)
  also from assms have "... = ((((CSP2 P) \<^sub>f ;; U0)  \<and> ((CSP2 Q) \<^sub>f ;; U1) \<and> ($\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) \<^sub>f) ;; (N\<^sub>C\<^sub>S\<^sub>P cs ;; SKIP))\<^sup>t"
    by (simp add: Healthy_def')
  also have "... = ((((P\<^sup>f \<or> P\<^sup>t \<and> $ok\<acute>) \<^sub>f ;; U0)  \<and> ((Q\<^sup>f \<or> Q\<^sup>t \<and> $ok\<acute>) \<^sub>f ;; U1) \<and> ($\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) \<^sub>f) ;; (N\<^sub>C\<^sub>S\<^sub>P cs ;; SKIP))\<^sup>t"
    by (simp add: CSP2_def H2_split)


    by (simp add: wait_f_seqr_left)

  also have "... = (P\<^sup>t\<^sub>f \<parallel>\<^bsub>M_CSP_ok(cs)\<^esub> Q\<^sup>t\<^sub>f)"
    apply (rel_tac)

  also have "... = (((P \<^sub>f ;; U0)  \<and> (Q \<^sub>f ;; U1) \<and> ($\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) \<^sub>f)\<lbrakk>true,true/$0-ok\<acute>,$1-ok\<acute>\<rbrakk> ;; M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t"
  
  also have "... = (((P \<^sub>f ;; U0)  \<and> (Q \<^sub>f ;; U1) \<and> ($\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) \<^sub>f) ;; (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t)"
    by (simp add: ok'_t_seqr_right)
  also have "... = (((P \<^sub>f ;; U0)  \<and> (Q \<^sub>f ;; U1) \<and> ($\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) \<^sub>f) ;; (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t)"

  apply (rel_tac)
*)

subsection {* CSP laws *}

theorem STOP_is_Stop: "STOP = Stop"
  apply (rel_auto)
  using minus_zero_eq apply blast+
done

lemma Skip_is_rea_skip: "Skip = II\<^sub>r"
  apply (rel_auto) using minus_zero_eq by blast+
  
lemma SKIP_alt_def: "SKIP = \<^bold>R(\<exists> $ref \<bullet> II\<^sub>r)"
  by rel_auto

lemma SKIP_rea_des: "SKIP = \<^bold>R(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute>))"
  by rel_auto

lemma wait_f_seqr_left: "(P ;; Q) \<^sub>f  = (P \<^sub>f ;; Q)"
  by (rel_auto)

lemma wait_t_seqr_left: "(P ;; Q) \<^sub>t  = (P \<^sub>t ;; Q)"
  by (rel_auto) 

lemma ok'_f_seqr_right: "(P ;; Q)\<^sup>f = (P ;; Q\<^sup>f)"
  by (rel_auto)

lemma ok'_t_seqr_right: "(P ;; Q)\<^sup>t = (P ;; Q\<^sup>t)"
  by (rel_auto)

(*
(* TODO : Circus merge predicate: *)

finition "MSt = undefined"

definition "M(cs) = ((($tr\<acute> - $\<^sub><tr) \<in>\<^sub>u (trpar\<^sub>u(\<guillemotleft>cs\<guillemotright>, $0.tr - $\<^sub><tr, $1.tr - $\<^sub><tr)) \<and> $0.tr \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u $1.tr \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<and>
                    (  (($0.wait \<or> $1.wait) \<and> $ref\<acute> \<subseteq>\<^sub>u (($0.ref \<union>\<^sub>u $1.ref) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u (($0.ref \<inter>\<^sub>u $1.ref) - \<guillemotleft>cs\<guillemotright>))
                       \<triangleleft> $wait\<acute> \<triangleright>
                       (\<not> $1.wait \<and> \<not> $2.wait \<and> MSt)
                    ))"
*)
end