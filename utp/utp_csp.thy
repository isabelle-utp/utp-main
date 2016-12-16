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

lemma ok_indep_ref [simp]: "ok \<bowtie> ref" "ref \<bowtie> ok"
  by (simp_all add: ref_def)

lemma wait_indep_ref [simp]: "wait \<bowtie> ref" "ref \<bowtie> wait"
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

definition N0 :: "'\<psi> set \<Rightarrow> (('\<psi>, unit) alphabet_csp) merge" where
  [upred_defs]:
  "N0(cs) =
     ($wait\<acute> =\<^sub>u ($0-wait \<or> $1-wait) \<and>
      $ref\<acute> =\<^sub>u ($0-ref \<union>\<^sub>u $1-ref) \<and>
      $tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<and>
      ($tr\<acute> - $tr\<^sub><) \<in>\<^sub>u trpar\<^sub>u(\<guillemotleft>cs\<guillemotright>, $0-tr - $tr\<^sub><, $1-tr - $tr\<^sub><) \<and> 
      ($0-tr - $tr\<^sub><) \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u ($1-tr - $tr\<^sub><) \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>)"

definition CSPMerge' ("N\<^sub>C\<^sub>S\<^sub>P") where
  [upred_defs]:
  "CSPMerge'(cs) = ($ok\<acute> =\<^sub>u ($0-ok \<and> $1-ok) \<and> N0(cs))"

definition CSPMerge ("M\<^sub>C\<^sub>S\<^sub>P") where
  [upred_defs]: "CSPMerge(cs) = (N\<^sub>C\<^sub>S\<^sub>P(cs) ;; SKIP)"

definition ParCSP :: "'\<theta> csp \<Rightarrow> '\<theta> event set \<Rightarrow> '\<theta> csp \<Rightarrow> '\<theta> csp" (infixl "\<parallel>[_]\<^sub>C\<^sub>S\<^sub>P" 85)
where [upred_defs]: "P \<parallel>[cs]\<^sub>C\<^sub>S\<^sub>P Q = P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q"

lemma SKIP_no_start: "(SKIP\<lbrakk>false/$ok\<rbrakk>) = R1(true)"
  by (rel_auto)

subsection {* CSP laws *}

text {* Jim's merge predicate lemmas *}

lemma JL1: "(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk> = (N0(cs) ;; R1(true))"
  by rel_auto

lemma JL2: "(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk> = (N0(cs) ;; R1(true))"
  by rel_auto

lemma JL3: "(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk> = (N0(cs) ;; R1(true))"
  by rel_auto

lemma seqr_ok'_true [usubst]: "(P ;; Q)\<^sup>t = (P ;; Q\<^sup>t)"
  by rel_auto

lemma seqr_ok'_false [usubst]: "(P ;; Q)\<^sup>f = (P ;; Q\<^sup>f)"
  by rel_auto

lemma seqr_wait_true [usubst]: "(P ;; Q) \<^sub>t = (P \<^sub>t ;; Q)"
  by rel_auto

lemma seqr_wait_false [usubst]: "(P ;; Q) \<^sub>f = (P \<^sub>f ;; Q)"
  by rel_auto

lemma SKIP_pre: "SKIP\<^sup>f = R1(\<not> $ok)"
  by (rel_auto)

lemma parallel_ok_cases:
  "((P \<parallel>\<^sub>s Q) ;; M) = (((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
                            ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk>)) \<or>
                            ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk>)) \<or>
                            ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk>)))"
proof -
  have "((P \<parallel>\<^sub>s Q) ;; M) = (\<^bold>\<exists> ok\<^sub>0 \<bullet> (P \<parallel>\<^sub>s Q)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$0-ok\<acute>\<rbrakk> ;; M\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$0-ok\<rbrakk>)"
    by (subst seqr_middle[of "left_uvar ok"], simp_all)
  also have "... = (\<^bold>\<exists> ok\<^sub>0 \<bullet> \<^bold>\<exists> ok\<^sub>1 \<bullet> ((P \<parallel>\<^sub>s Q)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$0-ok\<acute>\<rbrakk>\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>/$1-ok\<acute>\<rbrakk>) ;; (M\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$0-ok\<rbrakk>\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>/$1-ok\<rbrakk>))"
    by (subst seqr_middle[of "right_uvar ok"], simp_all)
  also have "... = (\<^bold>\<exists> ok\<^sub>0 \<bullet> \<^bold>\<exists> ok\<^sub>1 \<bullet> (P\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<acute>\<rbrakk> \<parallel>\<^sub>s Q\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>/$ok\<acute>\<rbrakk>) ;; (M\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>ok\<^sub>1\<guillemotright>/$0-ok,$1-ok\<rbrakk>))" 
    by (rel_auto)
  also have "... = (((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
                    ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk>)) \<or>
                    ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk>)) \<or>
                    ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk>)))"
    by (simp add: true_alt_def[THEN sym] false_alt_def[THEN sym] disj_assoc utp_pred.sup.left_commute utp_pred.sup_commute usubst)
  finally show ?thesis .
qed

lemma SKIP_alt_def: "SKIP = \<^bold>R(\<exists> $ref \<bullet> II\<^sub>r)"
  by rel_auto

lemma SKIP_rea_des: "SKIP = \<^bold>R(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute>))"
  by rel_auto

lemma SKIP_is_R1: "SKIP is R1"
  by (rel_auto)

lemma SKIP_is_R2: "SKIP is R2"
  by (rel_auto)

lemma SKIP_is_R3c: "SKIP is R3c"
  apply (rel_auto)
  apply (simp_all add: zero_list_def)
  using list_minus_anhil by blast

lemma SKIP_is_CSP1: "SKIP is CSP1"
  by (rel_auto)

lemma SKIP_is_CSP2: "SKIP is CSP2"
  by (rel_auto)

definition [upred_defs]: "R1m(M) = (M \<and> $tr\<^sub>< \<le>\<^sub>u $tr\<acute>)"
definition [upred_defs]: "R1m'(M) = (M \<and> $tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<and> $tr\<^sub>< \<le>\<^sub>u $0-tr \<and> $tr\<^sub>< \<le>\<^sub>u $1-tr)"
definition [upred_defs]: "R2m(M) = R1m(M\<lbrakk>0,$tr\<acute> - $tr\<^sub><,$0-tr - $tr\<^sub><,$1-tr - $tr\<^sub></$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>)"
definition [upred_defs]: "R2m'(M) = R1m'(M\<lbrakk>0,$tr\<acute> - $tr\<^sub><,$0-tr - $tr\<^sub><,$1-tr - $tr\<^sub></$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>)"
definition [upred_defs]: "R3m(M) = (($\<Sigma>\<acute> =\<^sub>u $\<Sigma>\<^sub>< \<or> \<not> $ok\<^sub>< \<and> $tr\<acute> \<ge>\<^sub>u $tr\<^sub><) \<triangleleft> $wait\<^sub>< \<triangleright> M)"

lemma R2m'_form: "R2m'(M) = (\<^bold>\<exists> tt, tt\<^sub>0, tt\<^sub>1 \<bullet> M\<lbrakk>0,\<guillemotleft>tt\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk> 
                                          \<and> $tr\<acute> =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<guillemotright> \<and> $0-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> $1-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>1\<guillemotright>)"
  apply (rel_auto)
  apply (metis diff_add_cancel_left')
  using ordered_cancel_monoid_diff_class.le_iff_add apply blast+
done

lemma R1_par_by_merge:
  "M is R1m \<Longrightarrow> (P \<parallel>\<^bsub>M\<^esub> Q) is R1"
  by (rel_blast)

lemma R2_par_by_merge:
  assumes "P is R2" "Q is R2" "M is R2m"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R2"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = (P \<parallel>\<^bsub>R2m(M)\<^esub> Q)"
    by (metis Healthy_def' assms(3))
  also have "... = (R2(P) \<parallel>\<^bsub>R2m(M)\<^esub> R2(Q))"
    using assms by (simp add: Healthy_def')
  also have "... = (R2(P) \<parallel>\<^bsub>R2m'(M)\<^esub> R2(Q))"
    by (rel_blast)
  also have "... = (P \<parallel>\<^bsub>R2m'(M)\<^esub> Q)"
    using assms by (simp add: Healthy_def')
  also have "... = ((P \<parallel>\<^sub>s Q) ;;
                   (\<^bold>\<exists> tt, tt\<^sub>0, tt\<^sub>1 \<bullet> M\<lbrakk>0,\<guillemotleft>tt\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk> 
                                     \<and> $tr\<acute> =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<guillemotright> 
                                     \<and> $0-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>0\<guillemotright> 
                                     \<and> $1-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>1\<guillemotright>))"
    by (simp add: par_by_merge_def R2m'_form)
  also have "... = (\<^bold>\<exists> tt, tt\<^sub>0, tt\<^sub>1 \<bullet> ((P \<parallel>\<^sub>s Q) ;; (M\<lbrakk>0,\<guillemotleft>tt\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk> 
                                                  \<and> $tr\<acute> =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<guillemotright> 
                                                  \<and> $0-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>0\<guillemotright> 
                                                  \<and> $1-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>1\<guillemotright>)))"
    by (rel_blast)
  also have "... = (\<^bold>\<exists> tt, tt\<^sub>0, tt\<^sub>1 \<bullet> ((P \<parallel>\<^sub>s Q) \<and> $0-tr\<acute> =\<^sub>u $tr\<^sub><\<acute> + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> $1-tr\<acute> =\<^sub>u $tr\<^sub><\<acute> + \<guillemotleft>tt\<^sub>1\<guillemotright> ;; 
                                      (M\<lbrakk>0,\<guillemotleft>tt\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<guillemotright>)))"
    by (rel_blast)
  also have "... = (\<^bold>\<exists> tt, tt\<^sub>0, tt\<^sub>1 \<bullet> ((P \<parallel>\<^sub>s Q) \<and> $0-tr\<acute> =\<^sub>u $tr\<^sub><\<acute> + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> $1-tr\<acute> =\<^sub>u $tr\<^sub><\<acute> + \<guillemotleft>tt\<^sub>1\<guillemotright> ;; 
                                      (M\<lbrakk>0,\<guillemotleft>tt\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>)) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<guillemotright>)"
    by (rel_blast)
  also have "... = (\<^bold>\<exists> tt, tt\<^sub>0, tt\<^sub>1 \<bullet> (((P \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>) \<parallel>\<^sub>s (Q \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright>)) ;; 
                                      (M\<lbrakk>0,\<guillemotleft>tt\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>)) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<guillemotright>)"
    by (rel_blast)
  also have "... = (\<^bold>\<exists> tt, tt\<^sub>0, tt\<^sub>1 \<bullet> (((R2(P) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>) \<parallel>\<^sub>s (R2(Q) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright>)) ;; 
                                      (M\<lbrakk>0,\<guillemotleft>tt\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>)) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<guillemotright>)"
    using assms(1-2) by (simp add: Healthy_def')                                      
  also have "... = (\<^bold>\<exists> tt, tt\<^sub>0, tt\<^sub>1 \<bullet> ((   ((\<^bold>\<exists> tt\<^sub>0' \<bullet> P\<lbrakk>0,\<guillemotleft>tt\<^sub>0'\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0'\<guillemotright>) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>) 
                                       \<parallel>\<^sub>s ((\<^bold>\<exists> tt\<^sub>1' \<bullet> Q\<lbrakk>0,\<guillemotleft>tt\<^sub>1'\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1'\<guillemotright>) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright>)) ;; 
                                      (M\<lbrakk>0,\<guillemotleft>tt\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>)) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<guillemotright>)"
    by (simp add: R2_form usubst)
  also have "... = (\<^bold>\<exists> tt, tt\<^sub>0, tt\<^sub>1 \<bullet> ((   (P\<lbrakk>0,\<guillemotleft>tt\<^sub>0\<guillemotright>/$tr,$tr\<acute>\<rbrakk>  \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>) 
                                       \<parallel>\<^sub>s (Q\<lbrakk>0,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright>)) ;; 
                                      (M\<lbrakk>0,\<guillemotleft>tt\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<^sub><,$tr\<acute>,$0-tr,$1-tr\<rbrakk>)) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<guillemotright>)"
    apply (rel_auto)
    apply (metis cancel_monoid_add_class.add_left_imp_eq)
    apply blast
  done
  also have "... = R2(P \<parallel>\<^bsub>M\<^esub> Q)"
    apply (rel_auto)
    apply blast
    using ordered_cancel_monoid_diff_class.le_iff_add apply blast
    using diff_add_cancel_left' by fastforce

  finally show ?thesis
    by (simp add: Healthy_def)
qed
  
(* definition [upred_defs]: "CSP1m(P) = (P \<or> \<not> ($0-ok \<and> $1-ok) \<and> $tr\<^sub>< \<le>\<^sub>u $tr\<acute>)" *)
(* definition [upred_defs]: "CSP1m(M) = (M \<triangleleft> $0-ok \<and> $1-ok \<triangleright> (\<^bold>\<exists> tr\<^sub>0 \<bullet> (M\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; true) \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>))" *)
definition [upred_defs]: "CSP1m(M) = (M \<or> (\<not> ($0-ok \<and> $1-ok) \<and> (\<^bold>\<exists> tr\<^sub>0 \<bullet> (M\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; true) \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>)))"

lemma R1_true_left_zero_R: "(R1(true) ;; \<^bold>R(P)) = R1(true)"
  by (rel_auto)

lemma CSP1_R1_H1: "CSP1(R1(P)) = R1(H1(R1(P)))"
  by (rel_auto)

lemma skip_rea_R1_lemma: "II\<^sub>r = R1($ok \<Rightarrow> II)"
  by (rel_auto)

lemma CSP1_algebraic_intro:
  assumes 
    "P is R1" "(R1(true\<^sub>h) ;; P) = R1(true\<^sub>h)" "(II\<^sub>r ;; P) = P"
  shows "P is CSP1"
proof -
  have "P = (II\<^sub>r ;; P)"
    by (simp add: assms(3))
  also have "... = (R1($ok \<Rightarrow> II) ;; P)"
    by (simp add: skip_rea_R1_lemma)
  also have "... = (((\<not> $ok \<and> R1(true)) ;; P) \<or> P)"
    by (metis (no_types, lifting) R1_def seqr_left_unit seqr_or_distl skip_rea_R1_lemma skip_rea_def utp_pred.inf_top_left utp_pred.sup_commute)
  also have "... = (((R1(\<not> $ok) ;; R1(true\<^sub>h)) ;; P) \<or> P)"
    by (rel_auto, metis order_trans)
  also have "... = ((R1(\<not> $ok) ;; (R1(true\<^sub>h) ;; P)) \<or> P)"
    by (simp add: seqr_assoc)
  also have "... = ((R1(\<not> $ok) ;; R1(true\<^sub>h)) \<or> P)"
    by (simp add: assms(2))
  also have "... = (R1(\<not> $ok) \<or> P)"
    by (rel_auto)
  also have "... = CSP1(P)"
    by (rel_auto)
  finally show ?thesis 
    by (simp add: Healthy_def)
qed

theorem CSP1_left_zero:
  assumes "P is R1" "P is CSP1"
  shows "(R1(true) ;; P) = R1(true)"
proof -
  have "(R1(true) ;; R1(CSP1(P))) = R1(true)"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms(1) assms(2))
qed

theorem CSP1_left_unit:
  assumes "P is R1" "P is CSP1"
  shows "(II\<^sub>r ;; P) = P"
proof -
  have "(II\<^sub>r ;; R1(CSP1(P))) = R1(CSP1(P))"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms(1) assms(2))
qed

lemma CSP1_alt_def: 
  assumes "P is R1"
  shows "CSP1(P) = (P \<triangleleft> $ok \<triangleright> R1(true))"
  using assms
proof -
  have "CSP1(R1(P)) = (R1(P) \<triangleleft> $ok \<triangleright> R1(true))"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

theorem CSP1_algebraic:
  assumes "P is R1"
  shows "P is CSP1 \<longleftrightarrow> (R1(true\<^sub>h) ;; P) = R1(true\<^sub>h) \<and> (II\<^sub>r ;; P) = P"
  using CSP1_algebraic_intro CSP1_left_unit CSP1_left_zero assms by blast

lemma R3_cases: "R3(P) = (II \<triangleleft> $wait \<triangleright> P)"
  by (rel_auto)

lemma R3c_R3_left_seq_closure:
  assumes "P is R3" "Q is R3c"
  shows "(P ;; Q) is R3c"
proof -
  have "(P ;; Q) = ((P ;; Q)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis cond_var_split cond_var_subst_right in_var_uvar wait_vwb_lens)
  also have "... = (((II \<triangleleft> $wait \<triangleright> P) ;; Q)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis Healthy_def' R3_def assms(1))
  also have "... = ((II\<lbrakk>true/$wait\<rbrakk> ;; Q) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (subst_tac)
  also have "... = ((II \<and> $wait\<acute> ;; Q) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis (no_types, lifting) cond_def conj_pos_var_subst seqr_pre_var_out skip_var utp_pred.inf_left_idem wait_vwb_lens)
  also have "... = ((II\<lbrakk>true/$wait\<acute>\<rbrakk> ;; Q\<lbrakk>true/$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis seqr_pre_transfer seqr_right_one_point true_alt_def uovar_convr upred_eq_true utp_rel.unrest_ouvar vwb_lens_mwb wait_vwb_lens)
  also have "... = ((II\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (II\<^sub>r \<triangleleft> $wait \<triangleright> Q)\<lbrakk>true/$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis Healthy_def' R3c_def assms(2))
  also have "... = ((II\<lbrakk>true/$wait\<acute>\<rbrakk> ;; II\<^sub>r\<lbrakk>true/$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (subst_tac)
  also have "... = ((II \<and> $wait\<acute> ;; II\<^sub>r) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis seqr_pre_transfer seqr_right_one_point true_alt_def uovar_convr upred_eq_true utp_rel.unrest_ouvar vwb_lens_mwb wait_vwb_lens)
  also have "... = ((II ;; II\<^sub>r) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (simp add: cond_def seqr_pre_transfer utp_rel.unrest_ouvar)
  also have "... = (II\<^sub>r \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by simp
  also have "... = R3c(P ;; Q)"
    by (simp add: R3c_def)
  finally show ?thesis
    by (simp add: Healthy_def') 
qed


lemma R3c_cases: "R3c(P) = ((II \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> P)"
  by (rel_auto)

definition [upred_defs]: "skip\<^sub>m = ($0-\<Sigma>\<acute> =\<^sub>u $\<Sigma> \<and> $1-\<Sigma>\<acute> =\<^sub>u $\<Sigma> \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>)"

lemma CSP1_R3c_comm: "CSP1(R3c(P)) = R3c(CSP1(P))"
  by (rel_auto)

lemma CSP1_R3_is_R3c: "CSP1(R3(P)) = R3c(CSP1(P))"
  by (rel_auto)

definition [upred_defs]: "nil\<^sub>m = ($\<Sigma>\<acute> =\<^sub>u $\<Sigma>\<^sub><)"
definition [upred_defs]: "nil\<^sub>r\<^sub>m = (nil\<^sub>m \<triangleleft> $0-ok \<and> $1-ok \<triangleright> $tr\<^sub>< \<le>\<^sub>u $tr\<acute>)"

definition [upred_defs]: "R3Mc(M) = (M \<or> ((\<not> $0-ok \<or> \<not> $1-ok) \<and> $tr\<^sub>< \<le>\<^sub>u $tr\<acute>) \<or> (($0-wait \<or> $1-wait) \<and> nil\<^sub>m))"

lemma R3_par_by_merge:
  assumes 
    "P is R3" "Q is R3" "(skip\<^sub>m ;; M) = II"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R3"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = ((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (metis cond_L6 cond_var_split in_var_uvar wait_vwb_lens)
  also have "... = ((P\<lbrakk>true/$wait\<rbrakk> \<parallel>\<^bsub>M\<^esub> Q\<lbrakk>true/$wait\<rbrakk>)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (rel_auto)
  also have "... = ((P\<lbrakk>true/$wait\<rbrakk> \<parallel>\<^bsub>M\<^esub> Q\<lbrakk>true/$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (metis cond_var_subst_left wait_vwb_lens)
  also have "... = (((II \<triangleleft> $wait \<triangleright> P)\<lbrakk>true/$wait\<rbrakk> \<parallel>\<^bsub>M\<^esub> (II \<triangleleft> $wait \<triangleright> Q)\<lbrakk>true/$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (metis Healthy_if R3_def assms(1) assms(2))
  also have "... = ((II\<lbrakk>true/$wait\<rbrakk> \<parallel>\<^bsub>M\<^esub> II\<lbrakk>true/$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (subst_tac)
  also have "... = ((II \<parallel>\<^bsub>M\<^esub> II) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (rel_auto)
  also have "... = ((skip\<^sub>m ;; M) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (rel_auto)
  also have "... = (II \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (simp add: assms(3))
  also have "... = R3(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: R3_def)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

definition [upred_defs]: "div\<^sub>m = ($tr \<le>\<^sub>u $0-tr\<acute> \<and> $tr \<le>\<^sub>u $1-tr\<acute> \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>)"

definition [upred_defs]: "wait\<^sub>m = skip\<^sub>m\<lbrakk>true,true/$ok,$wait\<rbrakk>"

lemma R3c_par_by_merge:
  assumes 
    "P is R1" "Q is R1" "P is CSP1" "Q is CSP1" "P is R3c" "Q is R3c" 
    "(wait\<^sub>m ;; M) = II\<lbrakk>true,true/$ok,$wait\<rbrakk>" "(div\<^sub>m ;; M) = R1(true)"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R3c"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = (((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true/$ok\<rbrakk> \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (metis cond_idem cond_var_subst_left cond_var_subst_right vwb_lens_ok wait_vwb_lens)
  also have "... = (((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk> \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (subst_tac)
  also have "... = (((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk> \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk>) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (metis cond_var_subst_left wait_vwb_lens)
  also have "... = ((II\<lbrakk>true,true/$ok,$wait\<rbrakk> \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
  proof -
    have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk> = R1(true)"
    proof -
      have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk> = ((P \<triangleleft> $ok \<triangleright> R1(true)) \<parallel>\<^bsub>M\<^esub> (Q \<triangleleft> $ok \<triangleright> R1(true)))\<lbrakk>false/$ok\<rbrakk>"
        by (metis CSP1_alt_def Healthy_if assms)
      also have "... = (R1(true) \<parallel>\<^bsub>M\<lbrakk>false/$ok\<^sub><\<rbrakk>\<^esub> R1(true))"
        by (rel_auto, metis, metis)
      also have "... = (div\<^sub>m ;; M)\<lbrakk>false/$ok\<rbrakk>"
        by (rel_auto, metis, metis)
      also have "... = (R1(true))\<lbrakk>false/$ok\<rbrakk>"
        by (simp add: assms(8))
      also have "... = (R1(true))"
        by rel_auto
      finally show ?thesis
        by simp
    qed
    moreover have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk> = II\<lbrakk>true,true/$ok,$wait\<rbrakk>"
    proof -
      have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk> = (P\<lbrakk>true,true/$ok,$wait\<rbrakk> \<parallel>\<^bsub>M\<^esub> Q\<lbrakk>true,true/$ok,$wait\<rbrakk>)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (rel_auto)
      also have "... = (((II \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> P)\<lbrakk>true,true/$ok,$wait\<rbrakk> \<parallel>\<^bsub>M\<^esub> ((II \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk>)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (metis Healthy_def' R3c_cases assms(5) assms(6))
      also have "... = (II\<lbrakk>true,true/$ok,$wait\<rbrakk> \<parallel>\<^bsub>M\<^esub> II\<lbrakk>true,true/$ok,$wait\<rbrakk>)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (subst_tac)
      also have "... = (wait\<^sub>m ;; M)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (rel_auto)
      also have "... = II\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (simp add: assms usubst)
      finally show ?thesis .
    qed
    ultimately show ?thesis by simp
  qed
  also have "... = ((II \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (rel_auto)
  also have "... = R3c(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: R3c_cases)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma CSP1_par_by_merge:
  assumes "P is R1" "Q is R1" "P is CSP1" "Q is CSP1" "M is R1m" "(div\<^sub>m ;; M) = R1(true)"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is CSP1"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = ((P \<parallel>\<^bsub>M\<^esub> Q) \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk>)"
    by (metis cond_idem cond_var_subst_right vwb_lens_ok)
  also have "... = ((P \<parallel>\<^bsub>M\<^esub> Q) \<triangleleft> $ok \<triangleright> R1(true))"
  proof -
    have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk> = ((P \<triangleleft> $ok \<triangleright> R1(true)) \<parallel>\<^bsub>M\<^esub> (Q \<triangleleft> $ok \<triangleright> R1(true)))\<lbrakk>false/$ok\<rbrakk>"
      by (metis CSP1_alt_def Healthy_if assms)
    also have "... = (R1(true) \<parallel>\<^bsub>M\<lbrakk>false/$ok\<^sub><\<rbrakk>\<^esub> R1(true))"
      by (rel_auto, metis, metis)
    also have "... = (div\<^sub>m ;; M)\<lbrakk>false/$ok\<rbrakk>"
      by (rel_auto, metis, metis)
    also have "... = (R1(true))\<lbrakk>false/$ok\<rbrakk>"
      by (simp add: assms(6))
    also have "... = (R1(true))"
      by rel_auto
    finally show ?thesis
      by simp
  qed
  finally show ?thesis
    by (metis CSP1_alt_def Healthy_def R1_par_by_merge assms(5))
qed

lemma CSP2_par_by_merge:
  assumes "M is CSP2"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is CSP2"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = ((P \<parallel>\<^sub>s Q) ;; M)"
    by (simp add: par_by_merge_def)
  also from assms have "... = ((P \<parallel>\<^sub>s Q) ;; (M ;; J))"
    by (simp add: Healthy_def' CSP2_def H2_def)
  also from assms have "... = (((P \<parallel>\<^sub>s Q) ;; M) ;; J)"
    by (meson seqr_assoc)
  also from assms have "... = CSP2(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: CSP2_def H2_def par_by_merge_def)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma CSPMerge'_is_R1m:
  "CSPMerge'(cs) is R1m"
  by rel_auto

lemma CSPMerge_is_R1m:
  "CSPMerge(cs) is R1m"
  by (rel_auto)

lemma parallel'_is_R1:
  "(P \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R1"
  by (simp add: CSPMerge'_is_R1m R1_par_by_merge)

lemma CSPMerge'_alt_def:
  "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) = ((P \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) ;; SKIP)"
  by (simp add: par_by_merge_def CSPMerge_def seqr_assoc)

lemma parallel_is_R1:
  "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R1"
  by (simp add: CSPMerge'_alt_def R1_seqr_closure SKIP_is_R1 parallel'_is_R1)

lemma parallel'_is_R2:
  assumes "P is R2" "Q is R2"
  shows "(P \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R2"
proof -
  have "N\<^sub>C\<^sub>S\<^sub>P cs is R2m"
    by (rel_auto)
  thus ?thesis
    using R2_par_by_merge assms(1) assms(2) by blast
qed

theorem parallel_is_R2:
  assumes "P is R2" "Q is R2"
  shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R2"
  by (simp add: CSPMerge'_alt_def R2_seqr_closure SKIP_is_R2 assms(1) assms(2) parallel'_is_R2)

lemma R3c_CSP1_form:
  "P is R1 \<Longrightarrow> R3c(CSP1(P)) = (R1(true) \<triangleleft> \<not>$ok \<triangleright> (II \<triangleleft> $wait \<triangleright> P))"
  by (rel_blast)

lemma parallel'_is_R3:
  assumes "P is R3" "Q is R3"
  shows "(P \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R3"
proof -
  have "(skip\<^sub>m ;; N\<^sub>C\<^sub>S\<^sub>P(cs)) = II"
    apply (rel_auto) using list_minus_anhil by blast
  thus ?thesis
    by (simp add: R3_par_by_merge assms)
qed

lemma R3c_via_CSP1_R3:
  "\<lbrakk> P is CSP1; P is R3 \<rbrakk> \<Longrightarrow> P is R3c"
  by (metis CSP1_R3c Healthy_def')

lemma CSPMerge_div_prop: "(div\<^sub>m ;; CSPMerge(cs)) = R1 true"
  apply (rel_auto)
  apply (rename_tac cs ok wait tr ref ok' wait' tr' ref')
  apply (rule_tac x="ok" in exI)
  apply (rule_tac x="wait" in exI)
  apply (rule_tac x="tr" in exI)
  apply (rule_tac x="ref" in exI)
  apply (simp)
  apply (metis minus_cancel order_refl singletonI tr_par.simps(1))
done

lemma skip_rea_form: "II\<^sub>r = (II \<triangleleft> $ok \<triangleright> R1(true))"
  by rel_auto

lemma CSPMerge_wait_prop: "(wait\<^sub>m ;; M\<^sub>C\<^sub>S\<^sub>P(cs)) = II\<lbrakk>true,true/$ok,$wait\<rbrakk>"
  apply (rel_auto)
  apply (metis list_minus_anhil zero_list_def)
  using zero_list_def apply auto
done

lemma parallel_is_R3c:
  assumes "P is R1" "Q is R1" "P is CSP1" "Q is CSP1" "P is R3c" "Q is R3c"
  shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R3c"
  by (simp add: CSPMerge_div_prop CSPMerge_wait_prop R3c_par_by_merge assms)

lemma parallel_is_CSP1:
  assumes "P is R1" "Q is R1" "P is CSP1" "Q is CSP1"
  shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is CSP1"
  by (simp add: CSP1_par_by_merge CSPMerge_div_prop CSPMerge_is_R1m assms)

lemma parallel_is_CSP2:
  "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is CSP2"
proof -
  have "M\<^sub>C\<^sub>S\<^sub>P(cs) is CSP2"
  proof -
    have "CSP2(M\<^sub>C\<^sub>S\<^sub>P(cs)) = (M\<^sub>C\<^sub>S\<^sub>P(cs) ;; J)"
      by (simp add: CSP2_def H2_def)
    also have "... = ((N\<^sub>C\<^sub>S\<^sub>P(cs) ;; SKIP) ;; J)"
      by (simp add: CSPMerge_def)
    also have "... = (N\<^sub>C\<^sub>S\<^sub>P(cs) ;; (SKIP ;; J))"
      by (simp add: seqr_assoc)
    also have "... = (N\<^sub>C\<^sub>S\<^sub>P(cs) ;; (CSP2(SKIP)))"
      by (simp add: CSP2_def H2_def)
    also have "... = (N\<^sub>C\<^sub>S\<^sub>P(cs) ;; SKIP)"
      by (simp add: Healthy_if SKIP_is_CSP2)
    finally show ?thesis
      by (simp add: Healthy_def' CSPMerge_def)
  qed
  thus ?thesis
    using CSP2_par_by_merge by blast
qed

lemma CSP2_R3c_commute: "CSP2(R3c(P)) = R3c(CSP2(P))"
  by (rel_auto)

lemma R3c_CSP: "R3c(CSP(P)) = CSP(P)"
  by (simp add: CSP1_R3c_commute CSP2_R3c_commute R2_R3c_commute R3c_idem RH_alt_def')

lemma CSP_healths:
  assumes "P is CSP"
  shows "P is R1" "P is R2" "P is R3c" "P is CSP1" "P is CSP2"
  apply (metis (mono_tags) CSP_R1_R2s Healthy_def' R1_idem assms(1))
  apply (metis CSP_R1_R2s Healthy_def R2_def assms)
  apply (metis Healthy_def R3c_CSP assms)
  apply (metis CSP1_idem Healthy_def' assms)
  apply (metis CSP1_CSP2_commute CSP2_idem Healthy_def' assms)
done

lemma CSP_intro:
  assumes "P is R1" "P is R2" "P is R3c" "P is CSP1" "P is CSP2"
  shows "P is CSP"
  by (metis Healthy_def RH_alt_def' assms(2) assms(3) assms(4) assms(5))

lemma parallel_is_CSP:
  assumes "P is CSP" "Q is CSP"
  shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is CSP"
  by (metis CSP_healths CSP_intro assms parallel_is_CSP1 parallel_is_CSP2 parallel_is_R1 parallel_is_R2 parallel_is_R3c)
    
lemma parallel_precondition:
  assumes "P is CSP2"
  shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>f\<^sub>f = ((P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<or> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))"
proof -

  have "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>f\<^sub>f = ((P \<parallel>\<^sub>s Q) ;; M\<^sub>C\<^sub>S\<^sub>P(cs))\<^sup>f\<^sub>f"
    by (simp add: par_by_merge_def)
  also have "... = (((P \<^sub>f \<parallel>\<^sub>s Q \<^sub>f) ;; N\<^sub>C\<^sub>S\<^sub>P cs) ;; R1(\<not> $ok))"
    by rel_blast
  also have "... = ((((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
                     ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk>)) \<or>
                     ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk>)) \<or>
                     ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk>))) ;; R1(\<not> $ok))"
    by (subst parallel_ok_cases, subst_tac)
  also have "... = ((((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk> ;; R1(\<not> $ok))) \<or>
                     ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk> ;; R1(\<not> $ok))) \<or>
                     ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk> ;; R1(\<not> $ok))) \<or>
                     ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk> ;; R1(\<not> $ok)))) )"
    (is "_ = (?C1 \<or>\<^sub>p ?C2 \<or>\<^sub>p ?C3 \<or>\<^sub>p ?C4)")
    by (simp add: seqr_or_distl seqr_assoc)
  also have "... = (?C2 \<or> ?C3)"
  proof -
    have "?C1 = false"
      by (rel_auto)
    moreover have "`?C4 \<Rightarrow> ?C3`" (is "`(?A ;; ?B) \<Rightarrow> (?C ;; ?D)`")
    proof -
      from assms have "`P\<^sup>f \<Rightarrow> P\<^sup>t`"
        by (metis CSP2_def H2_equivalence Healthy_def')
      hence P: "`P\<^sup>f\<^sub>f \<Rightarrow> P\<^sup>t\<^sub>f`"
        by (rel_auto)
      have "`?A \<Rightarrow> ?C`"
        using P by rel_auto
      moreover have "`?B \<Rightarrow> ?D`"
        by (rel_auto)
      ultimately show ?thesis
        by (simp add: impl_seqr_mono)
    qed
    ultimately show ?thesis
      by (simp add: subsumption2)
  qed
  also have "... = (((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((N0 cs ;; R1(\<not> $ok)))) \<or>
                    ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((N0 cs ;; R1(\<not> $ok)))))"
    by (rel_blast)
  also have "... = ((P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(\<not> $ok)\<^esub> Q\<^sup>t\<^sub>f) \<or>
                    (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(\<not> $ok)\<^esub> Q\<^sup>f\<^sub>f))"
    (is "_ = ((P\<^sup>f\<^sub>f \<parallel>\<^bsub>?M1\<^esub> Q\<^sup>t\<^sub>f) \<or> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>?M2\<^esub> Q\<^sup>f\<^sub>f))")
    by (simp add: par_by_merge_def)
  also have "... = ((P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<or>
                    (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))"
  proof -
    have "?M1 = (N0 cs ;; R1(true))"
      by (rel_auto)
    moreover have "?M2 = (N0 cs ;; R1(true))"
      by (rel_auto)
    ultimately show ?thesis by simp
  qed

  finally show ?thesis .
qed

lemma parallel_postcondition:
  assumes "P is CSP2"
  shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>t\<^sub>f = ((P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f) 
                             \<or> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0(cs) ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f)
                             \<or> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0(cs) ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>t\<^sub>f = ((P \<parallel>\<^sub>s Q) ;; M\<^sub>C\<^sub>S\<^sub>P(cs))\<^sup>t\<^sub>f"
    by (simp add: par_by_merge_def)
  also have "... = ((P \<^sub>f \<parallel>\<^sub>s Q \<^sub>f) ;; (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t)"
    by (rel_blast)
  also have "... = (((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
                    ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk>)) \<or>
                    ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk>)) \<or>
                    ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk>)))"
    by (subst parallel_ok_cases, subst_tac)
  also have "... = (((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
                    ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; (N0(cs) ;; R1(true))) \<or>
                    ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; (N0(cs) ;; R1(true))) \<or>
                    ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; (N0(cs) ;; R1(true))))"
     (is "_ = (?C1 \<or>\<^sub>p ?C2 \<or>\<^sub>p ?C3 \<or>\<^sub>p ?C4)") 
    by (simp add: JL1 JL2 JL3)
  also have "... = (((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
                    ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; (N0(cs) ;; R1(true))) \<or>
                    ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; (N0(cs) ;; R1(true))))"
  proof -
    from assms have "`P\<^sup>f \<Rightarrow> P\<^sup>t`"
      by (metis CSP2_def H2_equivalence Healthy_def')
    hence P:"`P\<^sup>f\<^sub>f \<Rightarrow> P\<^sup>t\<^sub>f`"
      by (rel_auto)
    have "`?C4 \<Rightarrow> ?C3`" (is "`(?A ;; ?B) \<Rightarrow> (?C ;; ?D)`")
    proof -
      have "`?A \<Rightarrow> ?C`"
        using P by rel_auto
      thus ?thesis
        by (simp add: impl_seqr_mono)
    qed
    thus ?thesis
      by (simp add: subsumption2)
  qed
  finally show ?thesis
    by (simp add: par_by_merge_def)
qed

lemma design_export_pre: "P \<turnstile> (P \<and> Q) = P \<turnstile> Q"
  by (rel_auto)

lemma neg_conj_cancel1: "(\<not> P \<and> (P \<or> Q)) = (\<not> P \<and> Q :: '\<alpha> upred)"
  by (pred_auto)

lemma neg_conj_cancel2: "(\<not> Q \<and> (P \<or> Q)) = (\<not> Q \<and> P :: '\<alpha> upred)"
  by (pred_auto)

theorem parallel_reactive_design:
  assumes "P is CSP" "Q is CSP"
  shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) = \<^bold>R((\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<and> \<not> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f)) \<turnstile>
                                 (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f))"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) = \<^bold>R((\<not> (P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>f\<^sub>f) \<turnstile> (P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>t\<^sub>f)"
    by (simp add: CSP_reactive_design assms parallel_is_CSP)
  also have "... = \<^bold>R((\<not> ((P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 (true)\<^esub> Q\<^sup>t\<^sub>f) \<or> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 (true)\<^esub> Q\<^sup>f\<^sub>f))) \<turnstile>
                      (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f \<or>
                       P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>t\<^sub>f \<or> 
                       P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>f\<^sub>f))"
    by (simp add: parallel_precondition parallel_postcondition CSP_healths(5) assms(1))
  also have "... = \<^bold>R((\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 (true)\<^esub> Q\<^sup>t\<^sub>f) \<and> \<not> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f)) \<turnstile>
                      ((\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 (true)\<^esub> Q\<^sup>t\<^sub>f \<or> P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f)) \<and>
                      (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f \<or>
                       P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>t\<^sub>f \<or> 
                       P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>f\<^sub>f)))"
    by (simp add: design_export_pre)
  also have "... = \<^bold>R((\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<and> \<not> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f)) \<turnstile>
                      ((\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f \<or> P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f)) \<and>
                      (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f)))"
    by (subst neg_conj_cancel2, simp)
  also have "... = \<^bold>R((\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<and> \<not> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f)) \<turnstile>
                        (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f))"
    by (simp add: design_export_pre)
  finally show ?thesis by simp
qed 

theorem STOP_is_Stop: "STOP = Stop"
  apply (rel_auto)
  using minus_zero_eq apply blast+
done

lemma Skip_is_rea_skip: "Skip = II\<^sub>r"
  apply (rel_auto) using minus_zero_eq by blast+
  
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