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

thm R2_def

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
  

lemma "((II\<^sub>r \<parallel>\<^bsub>CSPMerge'(cs)\<^esub> II\<^sub>r)) = II\<^sub>r"
  apply (rel_auto)
  using list_minus_anhil apply blast
  apply (rename_tac cs ok wait tr ref)
  apply (rule_tac x="ok" in exI)
  apply (rule_tac x="wait" in exI)
  apply (rule_tac x="tr" in exI)
  apply (rule_tac x="ref" in exI)
  apply (rule_tac x="ok" in exI)
  apply (rule_tac x="wait" in exI)
  apply (rule_tac x="tr" in exI)
  apply (rule_tac x="ref" in exI)
  apply (simp)
  apply (rule_tac x="ok" in exI)
  apply (rule_tac x="wait" in exI)
  apply (rule_tac x="tr" in exI)
  apply (rule_tac x="ref" in exI)
  apply (simp)
  apply (rename_tac cs ok wait tr ref ok' wait' tr' ref')
  apply (rule_tac x="False" in exI)
  apply (simp)
  apply (rule_tac x="wait" in exI)
  apply (rule_tac x="tr" in exI)
  apply (rule_tac x="ref" in exI)
  apply (simp)
oops

lemma R3c_par_by_merge:
  assumes "P is R3c" "Q is R3c"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R3c"
  oops

lemma CSP1_par_by_merge:
  assumes "P is CSP1" "Q is CSP1"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is CSP1"
  oops

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
  



lemma parallel'_is_R1:
  "(P \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R1"
  by (rule R1_par_by_merge, rel_auto)

lemma CSPMerge'_alt_def:
  "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) = ((P \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) ;; SKIP)"
  by (simp add: par_by_merge_def CSPMerge_def seqr_assoc)

lemma parallel_is_R1:
  "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R1"
  by (simp add: CSPMerge'_alt_def R1_seqr_closure SKIP_is_R1 parallel'_is_R1)

lemma parallel_R2_lemma_1:
  "($0-tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> $1-tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) = 
   ($0-tr\<acute> =\<^sub>u $tr\<^sub><\<acute> + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> $1-tr\<acute> =\<^sub>u $tr\<^sub><\<acute> + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>)"
  by (rel_auto)

lemma parallel'_is_R2:
  assumes "P is R2" "Q is R2"
  shows "(P \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R2"
proof -
  have "P \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q = (\<^bold>\<exists> tt\<^sub>0 \<bullet> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>)
                         \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub>
                         (\<^bold>\<exists> tt\<^sub>1 \<bullet> Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright>)"
    by (metis (mono_tags, lifting) Healthy_def R2_form assms)
  also have "... = (\<^bold>\<exists> tt\<^sub>0, tt\<^sub>1 \<bullet>
                   ((P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>)
                    \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub>
                    (Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright>)))"
    by (simp add: shEx_pbm_right shEx_pbm_left, subst shEx_commute, simp)
  also have "... = (\<^bold>\<exists> tt\<^sub>0, tt\<^sub>1 \<bullet>
                   (  (P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>) 
                   \<parallel>\<^sub>s (Q\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright>))
                    ;; N\<^sub>C\<^sub>S\<^sub>P(cs))"
    by (simp add: par_by_merge_def)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> ((\<lceil>P\<rceil>\<^sub>0\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$0-tr\<acute>\<rbrakk> \<and> $0-tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>) \<and>
                                     (\<lceil>Q\<rceil>\<^sub>1\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$1-tr\<acute>\<rbrakk> \<and> $1-tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<and> 
                                      $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; N\<^sub>C\<^sub>S\<^sub>P cs)"
    by (simp add: U0_as_alpha U1_as_alpha alpha)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> (\<lceil>P\<rceil>\<^sub>0\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$0-tr\<acute>\<rbrakk> \<and> (($0-tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and>
                                     \<lceil>Q\<rceil>\<^sub>1\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$1-tr\<acute>\<rbrakk>) \<and> $1-tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<and> 
                                      $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; N\<^sub>C\<^sub>S\<^sub>P cs)"
    by (simp add: conj_assoc)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> (\<lceil>P\<rceil>\<^sub>0\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$0-tr\<acute>\<rbrakk> \<and> ((\<lceil>Q\<rceil>\<^sub>1\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$1-tr\<acute>\<rbrakk> \<and>
                                     $0-tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>) \<and> $1-tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<and> 
                                      $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; N\<^sub>C\<^sub>S\<^sub>P cs)"
    by (simp add: conj_comm)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> ((\<lceil>P\<rceil>\<^sub>0\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$0-tr\<acute>\<rbrakk> \<and> \<lceil>Q\<rceil>\<^sub>1\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$1-tr\<acute>\<rbrakk>) \<and>
                                     ($0-tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> $1-tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>)) 
                                     ;; N\<^sub>C\<^sub>S\<^sub>P cs)"
    by (simp add: conj_assoc)
  also have "... =  (\<^bold>\<exists> tt\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> ((\<lceil>P\<rceil>\<^sub>0\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$0-tr\<acute>\<rbrakk> \<and> \<lceil>Q\<rceil>\<^sub>1\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$1-tr\<acute>\<rbrakk>) \<and>
                                     ($0-tr\<acute> =\<^sub>u $tr\<^sub><\<acute> + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> $1-tr\<acute> =\<^sub>u $tr\<^sub><\<acute> + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>)) 
                                     ;; N\<^sub>C\<^sub>S\<^sub>P cs)"
    by (simp add: parallel_R2_lemma_1)
  also have "... =  (\<^bold>\<exists> tt\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> ((\<lceil>P\<rceil>\<^sub>0\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$0-tr\<acute>\<rbrakk> \<and> \<lceil>Q\<rceil>\<^sub>1\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$1-tr\<acute>\<rbrakk> \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) \<and>
                                      ($0-tr\<acute> =\<^sub>u $tr\<^sub><\<acute> + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> $1-tr\<acute> =\<^sub>u $tr\<^sub><\<acute> + \<guillemotleft>tt\<^sub>1\<guillemotright>))
                                     ;; N\<^sub>C\<^sub>S\<^sub>P cs)"
    by (rel_blast)
  also have "... =  (\<^bold>\<exists> tt\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> ((\<lceil>P\<rceil>\<^sub>0\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$0-tr\<acute>\<rbrakk> \<and> \<lceil>Q\<rceil>\<^sub>1\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$1-tr\<acute>\<rbrakk> \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) \<and>
                                      (\<lceil>&0-tr =\<^sub>u &tr\<^sub>< + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> &1-tr =\<^sub>u &tr\<^sub>< + \<guillemotleft>tt\<^sub>1\<guillemotright>\<rceil>\<^sub>>))
                                     ;; N\<^sub>C\<^sub>S\<^sub>P cs)"
    by (simp add: alpha)
  also have "... =  (\<^bold>\<exists> tt\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> ((\<lceil>P\<rceil>\<^sub>0\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$0-tr\<acute>\<rbrakk> \<and> \<lceil>Q\<rceil>\<^sub>1\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$1-tr\<acute>\<rbrakk> \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>)
                                     ;; (($0-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> $1-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<and> N\<^sub>C\<^sub>S\<^sub>P cs)))"
    by (subst seqr_pre_transfer', simp add: alpha)

  have "\<And> tt\<^sub>0 tt\<^sub>1.
     (($0-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> $1-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>1\<guillemotright>) \<and> N\<^sub>C\<^sub>S\<^sub>P cs) = 
     ($0-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> $1-tr =\<^sub>u $tr\<^sub>< + \<guillemotleft>tt\<^sub>1\<guillemotright> \<and>
      $ok\<acute> =\<^sub>u ($0-ok \<and> $1-ok) \<and>
      $wait\<acute> =\<^sub>u ($0-wait \<or> $1-wait) \<and>
      $ref\<acute> =\<^sub>u ($0-ref \<union>\<^sub>u $1-ref) \<and>
      $tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<and>
      ($tr\<acute> - $tr\<^sub><) \<in>\<^sub>u trpar\<^sub>u(\<guillemotleft>cs\<guillemotright>, \<guillemotleft>tt\<^sub>0\<guillemotright>, \<guillemotleft>tt\<^sub>1\<guillemotright>) \<and> 
      \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and>
      $\<Sigma>\<^sub>C\<acute> =\<^sub>u $0-\<Sigma>\<^sub>C \<and> $\<Sigma>\<^sub>C\<acute> =\<^sub>u $1-\<Sigma>\<^sub>C)"
    by (rel_auto)
oops
    
lemma parallel_precondition:
  assumes "P is CSP2"
  shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>f\<^sub>f = ((P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(\<not> $ok)\<^esub> Q\<^sup>t\<^sub>f) \<or> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(\<not> $ok)\<^esub> Q\<^sup>f\<^sub>f))"
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
    by (simp add: par_by_merge_def)
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