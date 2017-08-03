(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_csp.thy                                                          *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 31 Jan 2017 *)

section {* Theory of CSP *}

theory utp_csp
  imports utp_rea_designs
begin

subsection {* CSP Alphabet *}

alphabet '\<phi> csp_vars = "'\<sigma> rsp_vars" +
  ref :: "'\<phi> set"

text {*
  The following two locale interpretations are a technicality to improve the
  behaviour of the automatic tactics. They enable (re)interpretation of state
  spaces in order to remove any occurrences of lens types, replacing them by
  tuple types after the tactics @{method pred_simp} and @{method rel_simp}
  are applied. Eventually, it would be desirable to automate preform these
  interpretations automatically as part of the @{command alphabet} command.
*}

interpretation alphabet_csp_prd:
  lens_interp "\<lambda>(ok, wait, tr, m). (ok, wait, tr, ref\<^sub>v m, more m)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation alphabet_csp_rel:
  lens_interp "\<lambda>(ok, ok', wait, wait', tr, tr', m, m').
    (ok, ok', wait, wait', tr, tr', ref\<^sub>v m, ref\<^sub>v m', more m, more m')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

type_synonym ('\<sigma>,'\<phi>) st_csp = "('\<sigma>, '\<phi> list, ('\<phi>, unit) csp_vars_scheme) rsp"
type_synonym ('\<sigma>,'\<phi>) action  = "('\<sigma>,'\<phi>) st_csp hrel"
type_synonym '\<phi> csp = "(unit,'\<phi>) st_csp"
type_synonym '\<phi> rel_csp  = "'\<phi> csp hrel"
  
text {* There is some slight imprecision with the translations, in that we don't bother to check
  if the trace event type and refusal set event types are the same. Essentially this is because
  its very difficult to construct processes where this would be the case. However, it may
  be better to add a proper ML print translation in the future. *}
  
translations
  (type) "('\<sigma>,'\<phi>) st_csp" <= (type) "('\<sigma>, '\<phi> list, '\<phi>1 csp_vars) rsp"
  (type) "('\<sigma>,'\<phi>) action" <= (type) "('\<sigma>, '\<phi>) st_csp hrel"
  
notation csp_vars_child_lens\<^sub>a ("\<Sigma>\<^sub>c")
notation csp_vars_child_lens ("\<Sigma>\<^sub>C")

subsection {* CSP Trace Merge *}

fun tr_par ::
  "'\<theta> set \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> list set" where
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

subsubsection {* Lifted Trace Merge *}

syntax "_utr_par" ::
  "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(_ \<star>\<^bsub>_\<^esub>/ _)" [100, 0, 101] 100)

text {* The function @{const trop} is used to lift ternary operators. *}

translations
  "t1 \<star>\<^bsub>cs\<^esub> t2" == "(CONST trop) (CONST tr_par) cs t1 t2"

subsubsection {* Trace Merge Lemmas *}

lemma tr_par_empty:
"tr_par cs t1 [] = {takeWhile (\<lambda>x. x \<notin> cs) t1}"
"tr_par cs [] t2 = {takeWhile (\<lambda>x. x \<notin> cs) t2}"
-- {* Subgoal 1 *}
apply (induct t1; simp)
-- {* Subgoal 2 *}
apply (induct t2; simp)
done

lemma tr_par_sym:
"tr_par cs t1 t2 = tr_par cs t2 t1"
apply (induct t1 arbitrary: t2)
-- {* Subgoal 1 *}
apply (simp add: tr_par_empty)
-- {* Subgoal 2 *}
apply (induct_tac t2)
-- {* Subgoal 2.1 *}
apply (clarsimp)
-- {* Subgoal 2.2 *}
apply (clarsimp)
apply (blast)
done

lemma trace_merge_nil: "x \<star>\<^bsub>{}\<^sub>u\<^esub> \<langle>\<rangle> = {x}\<^sub>u"
  by (pred_auto, simp_all add: tr_par_empty, metis takeWhile_eq_all_conv)

subsection {* Healthiness Conditions *}

text {* We here define extra healthiness conditions for CSP processes. *}

abbreviation CSP1 :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health"
where "CSP1(P) \<equiv> RD1(P)"

abbreviation CSP2 :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health"
where "CSP2(P) \<equiv> RD2(P)"

abbreviation CSP :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health"
where "CSP(P) \<equiv> SRD(P)"

definition STOP :: "'\<phi> rel_csp" where
[upred_defs]: "STOP = CSP1($ok\<acute> \<and> R3c($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition SKIP :: "'\<phi> rel_csp" where
[upred_defs]: "SKIP = \<^bold>R\<^sub>s(\<exists> $ref \<bullet> CSP1(II))"

definition Stop :: "('\<sigma>, '\<phi>) action" where
[upred_defs]: "Stop = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition Skip :: "('\<sigma>, '\<phi>) action" where
[upred_defs]: "Skip = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> $st\<acute> =\<^sub>u $st))"

definition CSP3 :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health" where
[upred_defs]: "CSP3(P) = (Skip ;; P)"

definition CSP4 :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health" where
[upred_defs]: "CSP4(P) = (P ;; Skip)"

definition NCSP :: "(('\<sigma>, '\<phi>) st_csp \<times> ('\<sigma>, '\<phi>) st_csp) health" where
[upred_defs]: "NCSP = CSP3 \<circ> CSP4 \<circ> CSP"

subsection {* Healthiness condition properties *}

text {* @{term SKIP} is the same as @{term Skip}, and @{term STOP} is the same as @{term Stop},
  when we consider stateless CSP processes. This is because any reference to the @{term st}
  variable degenerates when the alphabet type coerces its type to be empty. We therefore
  need not consider @{term SKIP} and @{term STOP} actions. *}

theorem SKIP_is_Skip: "SKIP = Skip"
  by (rel_auto)

theorem STOP_is_Stop: "STOP = Stop"
  by (rel_auto, simp_all add: zero_list_def minus_zero_eq)

theorem Skip_UTP_form: "Skip = \<^bold>R\<^sub>s(\<exists> $ref \<bullet> CSP1(II))"
  by (rel_auto)

lemma Skip_is_CSP [closure]:
  "Skip is CSP"
  by (simp add: Skip_def RHS_design_is_SRD unrest)

lemma Skip_RHS_tri_design [rdes_def]: "Skip = \<^bold>R\<^sub>s(true \<turnstile> (false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)))"
  by (rel_auto)

lemma Stop_is_CSP [closure]:
  "Stop is CSP"
  by (simp add: Stop_def RHS_design_is_SRD unrest)

lemma Stop_RHS_tri_design [rdes_def]: "Stop = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr) \<diamondop> false)"
  by (rel_auto)

lemma pre_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> pre\<^sub>R(P)"
  by (simp add: pre\<^sub>R_def unrest)

lemma peri_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> peri\<^sub>R(P)"
  by (simp add: peri\<^sub>R_def unrest)

lemma post_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> post\<^sub>R(P)"
  by (simp add: post\<^sub>R_def unrest)

lemma cmt_unrest_ref [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> cmt\<^sub>R(P)"
  by (simp add: cmt\<^sub>R_def unrest)

lemma st_lift_unrest_ref' [unrest]: "$ref\<acute> \<sharp> \<lceil>b\<rceil>\<^sub>S\<^sub><"
  by (rel_auto)

lemma RHS_design_ref_unrest [unrest]:
  "\<lbrakk>$ref \<sharp> P; $ref \<sharp> Q \<rbrakk> \<Longrightarrow> $ref \<sharp> (\<^bold>R\<^sub>s(P \<turnstile> Q))\<lbrakk>false/$wait\<rbrakk>"
  by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)

lemma preR_Skip [rdes]: "pre\<^sub>R(Skip) = true\<^sub>r"
  by (rel_auto)

lemma periR_Skip [rdes]: "peri\<^sub>R(Skip) = false"
  by (rel_auto)

lemma postR_Skip [rdes]: "post\<^sub>R(Skip) = ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)"
  apply (rel_auto) using minus_zero_eq by blast
        
lemma Skip_left_lemma:
  assumes "P is CSP"
  shows "Skip ;; P = \<^bold>R\<^sub>s ((\<forall> $ref \<bullet> pre\<^sub>R P) \<turnstile> (\<exists> $ref \<bullet> cmt\<^sub>R P))"
proof -
  have "Skip ;; P = 
        \<^bold>R\<^sub>s (($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st) wp\<^sub>R pre\<^sub>R P \<turnstile> 
            ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st) ;; peri\<^sub>R P \<diamondop> 
            ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st) ;; post\<^sub>R P)"
    by (simp add: SRD_composition_wp rdes closure wp assms rpred C1)
  also have "... = \<^bold>R\<^sub>s ((\<forall> $ref \<bullet> pre\<^sub>R P) \<turnstile>
                      ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> $st\<acute> =\<^sub>u $st) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> cmt\<^sub>R P))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)      
  also have "... = \<^bold>R\<^sub>s ((\<forall> $ref \<bullet> pre\<^sub>R P) \<turnstile> (\<exists> $ref \<bullet> cmt\<^sub>R P))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma Skip_left_unit:
  assumes "P is CSP" "$ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>"
  shows "Skip ;; P = P"
  using assms
  by (simp add: Skip_left_lemma)
     (metis SRD_reactive_design_alt all_unrest cmt_unrest_ref cmt_wait_false ex_unrest pre_unrest_ref pre_wait_false)

lemma CSP3_intro:
  "\<lbrakk> P is CSP; $ref \<sharp> P\<lbrakk>false/$wait\<rbrakk> \<rbrakk> \<Longrightarrow> P is CSP3"
  by (simp add: CSP3_def Healthy_def' Skip_left_unit)

lemma ref_unrest_RHS_design:
  assumes "$ref \<sharp> P" "$ref \<sharp> Q\<^sub>1" "$ref \<sharp> Q\<^sub>2"
  shows "$ref \<sharp> (\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2)) \<^sub>f"
  by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def design_def unrest usubst assms)

lemma CSP3_SRD_intro:
  assumes "P is CSP" "$ref \<sharp> pre\<^sub>R(P)" "$ref \<sharp> peri\<^sub>R(P)" "$ref \<sharp> post\<^sub>R(P)"
  shows "P is CSP3"
proof -
  have P: "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = P"
    by (simp add: SRD_reactive_design_alt assms(1) wait'_cond_peri_post_cmt[THEN sym])
  have "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) is CSP3"
    by (rule CSP3_intro, simp add: assms P, simp add: ref_unrest_RHS_design assms)
  thus ?thesis
    by (simp add: P)
qed

lemma Skip_unrest_ref [unrest]: "$ref \<sharp> Skip\<lbrakk>false/$wait\<rbrakk>"
  by (simp add: Skip_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)

lemma Skip_unrest_ref' [unrest]: "$ref\<acute> \<sharp> Skip\<lbrakk>false/$wait\<rbrakk>"
  by (simp add: Skip_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)

lemma CSP3_iff:
  assumes "P is CSP"
  shows "P is CSP3 \<longleftrightarrow> ($ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>)"
proof
  assume 1: "P is CSP3"
  have "$ref \<sharp> (Skip ;; P)\<lbrakk>false/$wait\<rbrakk>"
    by (simp add: usubst unrest)
  with 1 show "$ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>"
    by (metis CSP3_def Healthy_def)
next
  assume 1:"$ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>"
  show "P is CSP3"
    by (simp add: 1 CSP3_intro assms)
qed

lemma CSP3_unrest_ref [unrest]:
  assumes "P is CSP" "P is CSP3"
  shows "$ref \<sharp> pre\<^sub>R(P)" "$ref \<sharp> peri\<^sub>R(P)" "$ref \<sharp> post\<^sub>R(P)"
proof -
  have a:"($ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>)"
    using CSP3_iff assms by blast
  from a show "$ref \<sharp> pre\<^sub>R(P)"
    by (rel_blast)
  from a show "$ref \<sharp> peri\<^sub>R(P)"
    by (rel_auto)
  from a show "$ref \<sharp> post\<^sub>R(P)"
    by (rel_auto)
qed

lemma CSP3_Skip [closure]:
  "Skip is CSP3"
  by (rule CSP3_intro, simp add: Skip_is_CSP, simp add: Skip_def unrest)

lemma CSP3_Stop [closure]:
  "Stop is CSP3"
  by (rule CSP3_intro, simp add: Stop_is_CSP, simp add: Stop_def unrest)

lemma CSP3_Idempotent [closure]: "Idempotent CSP3"
  by (metis (no_types, lifting) CSP3_Skip CSP3_def Healthy_if Idempotent_def seqr_assoc)

lemma CSP3_Continuous: "Continuous CSP3"
  by (simp add: Continuous_def CSP3_def seq_Sup_distl)

lemma Skip_right_lemma:
  assumes "P is CSP"
  shows "P ;; Skip = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)))"
proof -
  have "P ;; Skip = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> (\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> post\<^sub>R P ;; ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st))"
    by (simp add: SRD_composition_wp closure assms wp rdes rpred)
  also have "... = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile>
                       ((cmt\<^sub>R P ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)) \<triangleleft> $wait\<acute> \<triangleright> (cmt\<^sub>R P ;; ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait \<and> $st\<acute> =\<^sub>u $st))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile>
                       ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (cmt\<^sub>R P ;; ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait \<and> $st\<acute> =\<^sub>u $st))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma Skip_right_tri_lemma:
  assumes "P is CSP"
  shows "P ;; Skip = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R P)))"
proof -
  have "((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)) = ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R P))"
    by (rel_auto)
  thus ?thesis by (simp add: Skip_right_lemma[OF assms])
qed

lemma CSP4_intro:
  assumes "P is CSP" "(\<not>\<^sub>r pre\<^sub>R(P)) ;; R1(true) = (\<not>\<^sub>r pre\<^sub>R(P))"
          "$st\<acute> \<sharp> (cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk>" "$ref\<acute> \<sharp> (cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>"
  shows "P is CSP4"
proof -
  have "CSP4(P) = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)))"
    by (simp add: CSP4_def Skip_right_lemma assms(1))
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R(P) \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk> \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>))"
    by (simp add: wpR_def assms(2) rpred closure cond_var_subst_left cond_var_subst_right)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R(P) \<turnstile> ((\<exists> $st\<acute> \<bullet> (cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk>) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> (cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>)))"
    by (simp add: usubst unrest)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> ((cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk> \<triangleleft> $wait\<acute> \<triangleright> (cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>))"
    by (simp add: ex_unrest assms)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> cmt\<^sub>R P)"
    by (simp add: cond_var_split)
  also have "... = P"
    by (simp add: SRD_reactive_design_alt assms(1))
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma CSP4_RC_intro:
  assumes "P is CSP" "(\<not>\<^sub>r pre\<^sub>R(P)) is RC"
          "$st\<acute> \<sharp> (cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk>" "$ref\<acute> \<sharp> (cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>"
  shows "P is CSP4"
proof -
  have "(\<not>\<^sub>r pre\<^sub>R(P)) ;; R1(true) = (\<not>\<^sub>r pre\<^sub>R(P))"
    by (metis Healthy_def RC1_def RC_implies_RC1 assms(2))
  thus ?thesis
    by (simp add: CSP4_intro assms)
qed
      
lemma Skip_srdes_right_unit:
  "(Skip :: ('\<sigma>,'\<phi>) action) ;; II\<^sub>R = Skip"
proof -
  have "($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st) ;; ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R)
         = (($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st) :: ('\<sigma>,'\<phi>) action)"
    by (rel_auto)
  thus ?thesis
    by (simp add: Skip_RHS_tri_design srdes_skip_tri_design RHS_tri_normal_design_composition
                  unrest R2c_true Healthy_def R1_false R2c_false R1_extend_conj R1_tr'_eq_tr R2c_and
                  R2c_tr'_minus_tr R2c_st'_eq_st wp R2c_lift_rea)
qed

lemma Skip_srdes_left_unit:
  "II\<^sub>R ;; (Skip :: ('\<sigma>,'\<phi>) action) = Skip"
proof -
  have "($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R) ;; ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)
         = (($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st) :: ('\<sigma>,'\<phi>) action)"
    by (rel_auto)
  thus ?thesis
    by (simp add: Skip_RHS_tri_design srdes_skip_tri_design RHS_tri_normal_design_composition
                  unrest R2c_true Healthy_def R1_false R2c_false R1_extend_conj R1_tr'_eq_tr R2c_and
                  R2c_tr'_minus_tr R2c_st'_eq_st wp R2c_lift_rea)
qed

lemma CSP4_right_subsumes_RD3: "RD3(CSP4(P)) = CSP4(P)"
  by (metis (no_types, hide_lams) CSP4_def RD3_def Skip_srdes_right_unit seqr_assoc)

lemma CSP4_implies_RD3: "P is CSP4 \<Longrightarrow> P is RD3"
  by (metis CSP4_right_subsumes_RD3 Healthy_def)

lemma CSP4_tri_intro:
  assumes "P is CSP" "(\<not>\<^sub>r pre\<^sub>R(P)) ;; R1(true) = (\<not>\<^sub>r pre\<^sub>R(P))" "$st\<acute> \<sharp> peri\<^sub>R(P)" "$ref\<acute> \<sharp> post\<^sub>R(P)"
  shows "P is CSP4"
  using assms
  by (rule_tac CSP4_intro, simp_all add: pre\<^sub>R_def peri\<^sub>R_def post\<^sub>R_def usubst cmt\<^sub>R_def)

lemma CSP4_NSRD_intro:
  assumes "P is NSRD" "$ref\<acute> \<sharp> post\<^sub>R(P)"
  shows "P is CSP4"
  by (simp add: CSP4_tri_intro NSRD_is_SRD NSRD_neg_pre_unit NSRD_st'_unrest_peri assms)

lemma CSP3_commutes_CSP4: "CSP3(CSP4(P)) = CSP4(CSP3(P))"
  by (simp add: CSP3_def CSP4_def seqr_assoc)

lemma NCSP_implies_CSP [closure]: "P is NCSP \<Longrightarrow> P is CSP"
  by (metis (no_types, hide_lams) CSP3_def CSP4_def Healthy_def NCSP_def SRD_idem SRD_seqr_closure Skip_is_CSP comp_apply)

lemma NCSP_implies_CSP3 [closure]:
  "P is NCSP \<Longrightarrow> P is CSP3"
  by (metis (no_types, lifting) CSP3_def Healthy_def' NCSP_def Skip_is_CSP Skip_left_unit Skip_unrest_ref comp_apply seqr_assoc)

lemma NCSP_implies_CSP4 [closure]:
  "P is NCSP \<Longrightarrow> P is CSP4"
  by (metis (no_types, hide_lams) CSP3_commutes_CSP4 Healthy_def NCSP_def NCSP_implies_CSP NCSP_implies_CSP3 comp_apply)

lemma NCSP_implies_RD3 [closure]: "P is NCSP \<Longrightarrow> P is RD3"
  by (metis CSP3_commutes_CSP4 CSP4_right_subsumes_RD3 Healthy_def NCSP_def comp_apply)

lemma NCSP_implies_NSRD [closure]: "P is NCSP \<Longrightarrow> P is NSRD"
  by (simp add: NCSP_implies_CSP NCSP_implies_RD3 SRD_RD3_implies_NSRD)

lemma NCSP_subset_implies_CSP [closure]:
  "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<Longrightarrow> A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  using NCSP_implies_CSP by blast

lemma NCSP_subset_implies_NSRD [closure]:
  "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<Longrightarrow> A \<subseteq> \<lbrakk>NSRD\<rbrakk>\<^sub>H"
  using NCSP_implies_NSRD by blast

lemma CSP_Healthy_subset_member: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is CSP"
  by (simp add: is_Healthy_subset_member)

lemma CSP3_Healthy_subset_member: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>CSP3\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is CSP3"
  by (simp add: is_Healthy_subset_member)

lemma CSP4_Healthy_subset_member: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is CSP4"
  by (simp add: is_Healthy_subset_member)

lemma NCSP_Healthy_subset_member: "\<lbrakk> P \<in> A; A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> P is NCSP"
  by (simp add: is_Healthy_subset_member)

lemma NCSP_intro:
  assumes "P is CSP" "P is CSP3" "P is CSP4"
  shows "P is NCSP"
  by (metis Healthy_def NCSP_def assms comp_eq_dest_lhs)

lemma NCSP_NSRD_intro:
  assumes "P is NSRD" "$ref \<sharp> pre\<^sub>R(P)" "$ref \<sharp> peri\<^sub>R(P)" "$ref \<sharp> post\<^sub>R(P)" "$ref\<acute> \<sharp> post\<^sub>R(P)"
  shows "P is NCSP"
  by (simp add: CSP3_SRD_intro CSP4_NSRD_intro NCSP_intro NSRD_is_SRD assms)

lemma CSP4_neg_pre_unit:
  assumes "P is CSP" "P is CSP4"
  shows "(\<not>\<^sub>r pre\<^sub>R(P)) ;; R1(true) = (\<not>\<^sub>r pre\<^sub>R(P))"
  by (simp add: CSP4_implies_RD3 NSRD_neg_pre_unit SRD_RD3_implies_NSRD assms(1) assms(2))

lemma NSRD_CSP4_intro:
  assumes "P is CSP" "P is CSP4"
  shows "P is NSRD"
  by (simp add: CSP4_implies_RD3 SRD_RD3_implies_NSRD assms(1) assms(2))

lemma CSP4_st'_unrest_peri [unrest]:
  assumes "P is CSP" "P is CSP4"
  shows "$st\<acute> \<sharp> peri\<^sub>R(P)"
  by (simp add: NSRD_CSP4_intro NSRD_st'_unrest_peri assms)

lemma CSP4_healthy_form:
  assumes "P is CSP" "P is CSP4"
  shows "P = \<^bold>R\<^sub>s((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R(P))))"
proof -
  have "P = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)))"
    by (metis CSP4_def Healthy_def Skip_right_lemma assms(1) assms(2))
  also have "... = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P)\<lbrakk>true/$wait\<acute>\<rbrakk> \<triangleleft> $wait\<acute> \<triangleright> (\<exists> $ref\<acute> \<bullet> cmt\<^sub>R P)\<lbrakk>false/$wait\<acute>\<rbrakk>))"
    by (metis (no_types, hide_lams) subst_wait'_left_subst subst_wait'_right_subst wait'_cond_def)
  also have "... = \<^bold>R\<^sub>s((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R(P))))"
    by (simp add: wait'_cond_def usubst peri\<^sub>R_def post\<^sub>R_def cmt\<^sub>R_def unrest)
  finally show ?thesis .
qed

lemma CSP4_ref'_unrest_pre [unrest]:
  assumes "P is CSP" "P is CSP4"
  shows "$ref\<acute> \<sharp> pre\<^sub>R(P)"
proof -
  have "pre\<^sub>R(P) = pre\<^sub>R(\<^bold>R\<^sub>s((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R(P)))))"
    using CSP4_healthy_form assms(1) assms(2) by fastforce
  also have "... = (\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false"
    by (simp add: rea_pre_RHS_design wpR_def usubst unrest
        CSP4_neg_pre_unit R1_rea_not R2c_preR R2c_rea_not assms)
  also have "$ref\<acute> \<sharp> ..."
    by (simp add: wpR_def unrest)
  finally show ?thesis .
qed

lemma CSP4_ref'_unrest_post [unrest]:
  assumes "P is CSP" "P is CSP4"
  shows "$ref\<acute> \<sharp> post\<^sub>R(P)"
proof -
  have "post\<^sub>R(P) = post\<^sub>R(\<^bold>R\<^sub>s((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> (\<exists> $ref\<acute> \<bullet> post\<^sub>R(P)))))"
    using CSP4_healthy_form assms(1) assms(2) by fastforce
  also have "... = R1 (R2c ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>R false \<Rightarrow>\<^sub>r (\<exists> $ref\<acute> \<bullet> post\<^sub>R P)))"
    by (simp add: rea_post_RHS_design usubst unrest wpR_def)
  also have "$ref\<acute> \<sharp> ..."
    by (simp add: R1_def R2c_def wpR_def unrest)
  finally show ?thesis .
qed

lemma CSP3_Chaos [closure]: "Chaos is CSP3"
  by (simp add: Chaos_def, rule CSP3_intro, simp_all add: RHS_design_is_SRD unrest)

lemma CSP4_Chaos [closure]: "Chaos is CSP4"
  by (rule CSP4_tri_intro, simp_all add: closure rdes unrest)

lemma NCSP_Chaos [closure]: "Chaos is NCSP"
  by (simp add: NCSP_intro closure) 
    
lemma CSP3_Miracle [closure]: "Miracle is CSP3"
  by (simp add: Miracle_def, rule CSP3_intro, simp_all add: RHS_design_is_SRD unrest)

lemma CSP4_Miracle [closure]: "Miracle is CSP4"
  by (rule CSP4_tri_intro, simp_all add: closure rdes unrest)

lemma NCSP_Miracle [closure]: "Miracle is NCSP"
  by (simp add: NCSP_intro closure) 
    
lemma NCSP_seqr_closure [closure]:
  assumes "P is NCSP" "Q is NCSP"
  shows "P ;; Q is NCSP"
  by (metis (no_types, lifting) CSP3_def CSP4_def Healthy_def' NCSP_implies_CSP NCSP_implies_CSP3
      NCSP_implies_CSP4 NCSP_intro SRD_seqr_closure assms(1) assms(2) seqr_assoc)

lemma R1_ref_unrest [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> R1(P)"
  by (simp add: R1_def unrest)

lemma R2c_ref_unrest [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma R1_ref'_unrest [unrest]: "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> R1(P)"
  by (simp add: R1_def unrest)

lemma R2c_ref'_unrest [unrest]: "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma R2s_notin_ref': "R2s(\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) = (\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)"
  by (pred_auto)

lemma CSP4_Skip [closure]: "Skip is CSP4"
  apply (rule CSP4_intro, simp_all add: Skip_is_CSP)
  apply (simp_all add: Skip_def rea_pre_RHS_design rea_cmt_RHS_design usubst unrest R2c_true)
done

lemma NCSP_Skip [closure]: "Skip is NCSP"
  by (metis CSP3_Skip CSP4_Skip Healthy_def NCSP_def Skip_is_CSP comp_apply)

lemma CSP4_Stop [closure]: "Stop is CSP4"
  apply (rule CSP4_intro, simp_all add: Stop_is_CSP)
  apply (simp_all add: Stop_def rea_pre_RHS_design rea_cmt_RHS_design usubst unrest R2c_true)
done

lemma NCSP_Stop [closure]: "Stop is NCSP"
  by (metis CSP3_Stop CSP4_Stop Healthy_def NCSP_def Stop_is_CSP comp_apply)

lemma CSP4_Idempotent: "Idempotent CSP4"
  by (metis (no_types, lifting) CSP3_Skip CSP3_def CSP4_def Healthy_if Idempotent_def seqr_assoc)

lemma CSP4_Continuous: "Continuous CSP4"
  by (simp add: Continuous_def CSP4_def seq_Sup_distr)

lemma preR_Stop [rdes]: "pre\<^sub>R(Stop) = true\<^sub>r"
  by (simp add: Stop_def Stop_is_CSP rea_pre_RHS_design unrest usubst R2c_true)

lemma periR_Stop [rdes]: "peri\<^sub>R(Stop) = ($tr\<acute> =\<^sub>u $tr)"
  apply (rel_auto) using minus_zero_eq by blast

lemma postR_Stop [rdes]: "post\<^sub>R(Stop) = false"
  by (rel_auto)

lemma cmtR_Stop [rdes]: "cmt\<^sub>R(Stop) = ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)"
  apply (rel_auto) using minus_zero_eq by blast

lemma NCSP_Idempotent [closure]: "Idempotent NCSP"
  by (clarsimp simp add: NCSP_def Idempotent_def)
     (metis (no_types, hide_lams) CSP3_Idempotent CSP3_def CSP4_Idempotent CSP4_def Healthy_def Idempotent_def SRD_idem SRD_seqr_closure Skip_is_CSP seqr_assoc)

lemma NCSP_Continuous [closure]: "Continuous NCSP"
  by (simp add: CSP3_Continuous CSP4_Continuous Continuous_comp NCSP_def SRD_Continuous)

subsection {* CSP theories *}

typedecl TCSP

abbreviation "TCSP \<equiv> UTHY(TCSP, ('\<sigma>,'\<phi>) st_csp)"

overloading
  tcsp_hcond   == "utp_hcond :: (TCSP, ('\<sigma>,'\<phi>) st_csp) uthy \<Rightarrow> (('\<sigma>,'\<phi>) st_csp \<times> ('\<sigma>,'\<phi>) st_csp) health"
begin
  definition tcsp_hcond :: "(TCSP, ('\<sigma>,'\<phi>) st_csp) uthy \<Rightarrow> (('\<sigma>,'\<phi>) st_csp \<times> ('\<sigma>,'\<phi>) st_csp) health" where
  [upred_defs]: "tcsp_hcond T = NCSP"
end

interpretation csp_theory: utp_theory_continuous "UTHY(TCSP, ('\<sigma>,'\<phi>) st_csp)"
  rewrites "\<And> P. P \<in> carrier (uthy_order TCSP) \<longleftrightarrow> P is NCSP"
  and "P is \<H>\<^bsub>TCSP\<^esub> \<longleftrightarrow> P is NCSP"
  and "carrier (uthy_order TCSP) \<rightarrow> carrier (uthy_order TCSP) \<equiv> \<lbrakk>NCSP\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>NCSP\<rbrakk>\<^sub>H"
  and "A \<subseteq> carrier (uthy_order TCSP) \<longleftrightarrow> A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H"
  and "le (uthy_order TCSP) = op \<sqsubseteq>"
  by (unfold_locales, simp_all add: tcsp_hcond_def NCSP_Continuous Healthy_Idempotent Healthy_if NCSP_Idempotent)

declare csp_theory.top_healthy [simp del]
declare csp_theory.bottom_healthy [simp del]

lemma csp_bottom_Chaos: "\<^bold>\<bottom>\<^bsub>TCSP\<^esub> = Chaos"
proof -
  have 1: "\<^bold>\<bottom>\<^bsub>TCSP\<^esub> = CSP3 (CSP4 (CSP true))"
    by (simp add: csp_theory.healthy_bottom, simp add: tcsp_hcond_def NCSP_def)
  also have 2:"... = CSP3 (CSP4 Chaos)"
    by (metis srdes_hcond_def srdes_theory_continuous.healthy_bottom)
  also have 3:"... = Chaos"
    by (metis CSP3_Chaos CSP4_Chaos Healthy_def')
  finally show ?thesis .
qed

lemma csp_top_Miracle: "\<^bold>\<top>\<^bsub>TCSP\<^esub> = Miracle"
proof -
  have 1: "\<^bold>\<top>\<^bsub>TCSP\<^esub> = CSP3 (CSP4 (CSP false))"
    by (simp add: csp_theory.healthy_top, simp add: tcsp_hcond_def NCSP_def)
  also have 2:"... = CSP3 (CSP4 Miracle)"
    by (metis srdes_hcond_def srdes_theory_continuous.healthy_top)
  also have 3:"... = Miracle"
    by (metis CSP3_Miracle CSP4_Miracle Healthy_def')
  finally show ?thesis .
qed
  
subsection {* CSP Constructs *}

definition AssignsCSP :: "'\<sigma> usubst \<Rightarrow> ('\<sigma>, '\<phi>) action" ("\<langle>_\<rangle>\<^sub>C") where
[upred_defs]: "AssignsCSP \<sigma> = \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S))"

syntax
  "_assigns_csp" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  ("'(_') :=\<^sub>C '(_')")  
  "_assigns_csp" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=\<^sub>C" 90)

translations
  "_assigns_csp xs vs" => "CONST AssignsCSP (_mk_usubst (CONST id) xs vs)"
  "x :=\<^sub>C v" <= "CONST AssignsCSP (CONST subst_upd (CONST id) (CONST svar x) v)"
  "x :=\<^sub>C v" <= "CONST AssignsCSP (CONST subst_upd (CONST id) x v)"
  "x,y :=\<^sub>C u,v" <= "CONST AssignsCSP (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"

text {* There are different collections that we would like to assign to, but they all have different
  types and perhaps more importantly different conditions on the update being well defined. For example,
  for a list well-definedness equates to the index being less than the length etc. Thus we here set
  up a polymorphic constant for CSP assignment updates that can be specialised to different types. *}
  
consts
  csp_assign_upd :: "('f \<Longrightarrow> '\<sigma>) \<Rightarrow> ('k, '\<sigma>) uexpr \<Rightarrow> ('v, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action"
  
definition AssignCSP_list_update :: 
  "('a list \<Longrightarrow> '\<sigma>) \<Rightarrow> (nat, '\<sigma>) uexpr \<Rightarrow> ('a, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "AssignCSP_list_update x k v = \<^bold>R\<^sub>s(\<lceil>k \<in>\<^sub>u dom\<^sub>u(&x)\<rceil>\<^sub>S\<^sub>< \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>x[k] := v\<rceil>\<^sub>S))"

definition AssignCSP_pfun_update :: 
  "(('k, 'v) pfun \<Longrightarrow> '\<sigma>) \<Rightarrow> ('k, '\<sigma>) uexpr \<Rightarrow> ('v, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "AssignCSP_pfun_update x k v = \<^bold>R\<^sub>s(\<lceil>k \<in>\<^sub>u dom\<^sub>u(&x)\<rceil>\<^sub>S\<^sub>< \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>x[k] := v\<rceil>\<^sub>S))"

adhoc_overloading
  csp_assign_upd AssignCSP_list_update and csp_assign_upd AssignCSP_pfun_update
  
text {* All different assignment updates have the same syntax; the type resolves which implementation
  to use. *}
  
syntax
  "_csp_assign_upd" :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("{_[_]} :=\<^sub>C _" [0,0,72] 72)

translations
  "{x[k]} :=\<^sub>C v" == "CONST csp_assign_upd x k v"
  
text {* The CSP weakest fixed-point is obtained simply by precomposing the body with the CSP
  healthiness condition. *}

abbreviation mu_CSP :: "(('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action) \<Rightarrow> ('\<sigma>, '\<phi>) action" ("\<mu>\<^sub>C") where
"\<mu>\<^sub>C F \<equiv> \<mu> (F \<circ> CSP)"

syntax
  "_mu_CSP" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu>\<^sub>C _ \<bullet> _" [0, 10] 10)

translations
  "\<mu>\<^sub>C X \<bullet> P" == "CONST mu_CSP (\<lambda> X. P)"

declare comp_def [rdes]

lemma mu_CSP_equiv:
  assumes "Monotonic F" "F \<in> \<lbrakk>CSP\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  shows "(\<mu>\<^sub>R F) = (\<mu>\<^sub>C F)"
  by (simp add: srd_mu_equiv assms comp_def)
    
lemma mu_CSP_unfold:
  "P is CSP \<Longrightarrow> (\<mu>\<^sub>C X \<bullet> P ;; X) = P ;; (\<mu>\<^sub>C X \<bullet> P ;; X)"
  apply (subst gfp_unfold)
  apply (simp_all add: closure Healthy_if)
done
    
definition Guard ::
  "'\<sigma> cond \<Rightarrow>
   ('\<sigma>, '\<phi>) action \<Rightarrow>
   ('\<sigma>, '\<phi>) action" (infixr "&\<^sub>u" 70) where
[upred_defs]: "g &\<^sub>u A = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R(A)) \<turnstile> ((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R(A)) \<or> (\<lceil>\<not> g\<rceil>\<^sub>S\<^sub><) \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition ExtChoice ::
  "('\<sigma>, '\<phi>) action set \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "ExtChoice A = \<^bold>R\<^sub>s((\<Squnion> P\<in>A \<bullet> pre\<^sub>R(P)) \<turnstile> ((\<Squnion> P\<in>A \<bullet> cmt\<^sub>R(P)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R(P))))"

syntax
  "_ExtChoice" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<box> _\<in>_ \<bullet>/ _)" [0, 0, 10] 10)
  "_ExtChoice_simp" :: "pttrn \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<box> _ \<bullet>/ _)" [0, 10] 10)

translations
  "\<box>P\<in>A \<bullet> B"   \<rightleftharpoons> "CONST ExtChoice ((\<lambda>P. B) ` A)"
  "\<box>P \<bullet> B"     \<rightleftharpoons> "CONST ExtChoice (CONST range (\<lambda>P. B))"

definition extChoice ::
  "('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" (infixl "\<box>" 65) where
[upred_defs]: "P \<box> Q \<equiv> ExtChoice {P, Q}"

definition do\<^sub>u ::
  "('\<phi>, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "do\<^sub>u e = (($tr\<acute> =\<^sub>u $tr \<and> \<lceil>e\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) \<triangleleft> $wait\<acute> \<triangleright> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>e\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st))"

definition DoCSP :: "('\<phi>, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action" ("do\<^sub>C") where
[upred_defs]: "DoCSP a = \<^bold>R\<^sub>s(true \<turnstile> do\<^sub>u a)"

definition PrefixCSP ::
  "('\<phi>, '\<sigma>) uexpr \<Rightarrow>
  ('\<sigma>, '\<phi>) action \<Rightarrow>
  ('\<sigma>, '\<phi>) action" where
[upred_defs]: "PrefixCSP a P = (do\<^sub>C(a) ;; CSP(P))"

abbreviation "OutputCSP c v P \<equiv> PrefixCSP (c\<cdot>v)\<^sub>u P"

abbreviation GuardedChoiceCSP :: "'\<theta> set \<Rightarrow> ('\<theta> \<Rightarrow> ('\<sigma>, '\<theta>) action) \<Rightarrow> ('\<sigma>, '\<theta>) action" where
"GuardedChoiceCSP A P \<equiv> (\<box> x\<in>A \<bullet> PrefixCSP \<guillemotleft>x\<guillemotright> (P(x)))"

syntax
  "_GuardedChoiceCSP" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<box> _ \<in> _ \<^bold>\<rightarrow> _" [0,0,85] 86)

translations
  "\<box> x\<in>A \<^bold>\<rightarrow> P" == "CONST GuardedChoiceCSP A (\<lambda> x. P)"

text {* This version of input prefix is implemented using iterated external choice and so does not
  depend on the existence of local variables. *}

definition InputCSP ::
  "('a, '\<theta>) chan \<Rightarrow> ('a \<Rightarrow> '\<sigma> upred) \<Rightarrow> ('a \<Rightarrow> ('\<sigma>, '\<theta>) action) \<Rightarrow> ('\<sigma>, '\<theta>) action" where
[upred_defs]: "InputCSP c A P = (\<box> x\<in>UNIV \<bullet> A(x) &\<^sub>u PrefixCSP (c\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u (P x))"

definition InputVarCSP :: "('a, '\<theta>) chan \<Rightarrow> ('a \<Rightarrow> '\<sigma> upred) \<Rightarrow> ('a \<Longrightarrow> '\<sigma>) \<Rightarrow> ('\<sigma>, '\<theta>) action \<Rightarrow> ('\<sigma>, '\<theta>) action" where
"InputVarCSP c A x P = InputCSP c A (\<lambda> v. \<langle>[x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>]\<rangle>\<^sub>C) ;; CSP(P)"

definition do\<^sub>I :: "
  ('a, '\<theta>) chan \<Rightarrow>
  ('a \<Longrightarrow> ('\<sigma>, '\<theta>) st_csp) \<Rightarrow>
  ('a \<Rightarrow> ('\<sigma>, '\<theta>) action) \<Rightarrow>
  ('\<sigma>, '\<theta>) action" where
"do\<^sub>I c x P = (
  ($tr\<acute> =\<^sub>u $tr \<and> {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> (c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u}\<^sub>u \<inter>\<^sub>u $ref\<acute> =\<^sub>u {}\<^sub>u)
    \<triangleleft> $wait\<acute> \<triangleright>
  (($tr\<acute> - $tr) \<in>\<^sub>u {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> \<langle>(c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u\<rangle>}\<^sub>u \<and> (c\<cdot>$x\<acute>)\<^sub>u =\<^sub>u last\<^sub>u($tr\<acute>)))"

subsection {* Syntax and Translations for Prefix *}

syntax
  "_simple_prefix" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<^bold>\<rightarrow> _" [81, 80] 80)

translations
  "a \<^bold>\<rightarrow> P" == "CONST PrefixCSP \<guillemotleft>a\<guillemotright> P"

text {* We next configure a syntax for mixed prefixes. *}

nonterminal prefix_elem' and mixed_prefix'

syntax "_end_prefix" :: "prefix_elem' \<Rightarrow> mixed_prefix'" ("_")

text {* Input Prefix: @{text "\<dots>?(x)"} *}

syntax "_simple_input_prefix" :: "id \<Rightarrow> prefix_elem'"  ("?'(_')")

text {* Input Prefix with Constraint: @{text "\<dots>?(x : P)"} *}

syntax "_input_prefix" :: "id \<Rightarrow> ('\<sigma>, '\<epsilon>) action \<Rightarrow> prefix_elem'" ("?'(_ :/ _')")

text {* Output Prefix: @{text "\<dots>![v]e"} *}

text {* A variable name must currently be provided for outputs, too. Fix?! *}

syntax "_output_prefix" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" ("!'(_')")
syntax "_output_prefix" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" (".'(_')")

syntax (output) "_output_prefix_pp" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" ("!'(_')")

syntax
  "_prefix_aux" :: "pttrn \<Rightarrow> logic \<Rightarrow> prefix_elem'"

text {* Mixed-Prefix Action: @{text "c\<dots>(prefix) \<^bold>\<rightarrow> A"} *}

syntax "_mixed_prefix" :: "prefix_elem' \<Rightarrow> mixed_prefix' \<Rightarrow> mixed_prefix'" ("__")

syntax
  "_prefix_action" ::
  "('a, '\<epsilon>) chan \<Rightarrow> mixed_prefix' \<Rightarrow> ('\<sigma>, '\<epsilon>) action \<Rightarrow> ('\<sigma>, '\<epsilon>) action"
  ("(__ \<^bold>\<rightarrow>/ _)" [81, 81, 80] 80)

text {* Syntax translations *}

abbreviation lconj :: "('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('b \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<times> 'b \<Rightarrow> '\<alpha> upred)" (infixr "\<and>\<^sub>l" 35)
where "(P \<and>\<^sub>l Q) \<equiv> (\<lambda> (x,y). P x \<and> Q y)"

definition [upred_defs]: "outp_constraint v \<equiv> (\<lambda> x. \<guillemotleft>x\<guillemotright> =\<^sub>u v)"

translations
  "_simple_input_prefix x" \<rightleftharpoons> "_input_prefix x true"
  "_mixed_prefix (_input_prefix x P) (_prefix_aux y Q)" \<rightharpoonup>
  "_prefix_aux (_pattern x y) ((\<lambda> x. P) \<and>\<^sub>l Q)"
  "_mixed_prefix (_output_prefix P) (_prefix_aux y Q)" \<rightharpoonup>
  "_prefix_aux (_pattern _idtdummy y) ((CONST outp_constraint P) \<and>\<^sub>l Q)"
  "_end_prefix (_input_prefix x P)" \<rightharpoonup> "_prefix_aux x (\<lambda> x. P)"
  "_end_prefix (_output_prefix P)" \<rightharpoonup> "_prefix_aux _idtdummy (CONST outp_constraint P)"
  "_prefix_action c (_prefix_aux x P) A" == "(CONST InputCSP) c P (\<lambda>x. A)"

text {* Basic print translations; more work needed *}

translations
  "_simple_input_prefix x" <= "_input_prefix x true"
  "_output_prefix v" <= "_prefix_aux p (CONST outp_constraint v)"
  "_output_prefix u (_output_prefix v)" 
    <= "_prefix_aux p (\<lambda>(x1, y1). CONST outp_constraint u x2 \<and> CONST outp_constraint v y2)"
  "_input_prefix x P" <= "_prefix_aux v (\<lambda>x. P)"
  "x!(v) \<^bold>\<rightarrow> P" <= "CONST OutputCSP x v P"
  
term "x!(1)!(y) \<^bold>\<rightarrow> P"  
term "x?(v) \<^bold>\<rightarrow> P"
term "x?(v:false) \<^bold>\<rightarrow> P"
term "x!(\<langle>1\<rangle>) \<^bold>\<rightarrow> P"
term "x?(v)!(1) \<^bold>\<rightarrow> P"
term "x!(\<langle>1\<rangle>)!(2)?(v:true) \<^bold>\<rightarrow> P"

text {* Basic translations for state variable communications *}

syntax
  "_csp_input_var"  :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>?$_:_ \<^bold>\<rightarrow> _" [81, 0, 0, 80] 80)
  "_csp_inputu_var" :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>?$_ \<^bold>\<rightarrow> _" [81, 0, 80] 80)

translations
  "c\<^bold>?$x:A \<^bold>\<rightarrow> P" \<rightleftharpoons> "CONST InputVarCSP c x A P"
  "c\<^bold>?$x \<^bold>\<rightarrow> P"   \<rightharpoonup> "CONST InputVarCSP c x (CONST UNIV) P"
  "c\<^bold>?$x \<^bold>\<rightarrow> P"   <= "c\<^bold>?$x:true \<^bold>\<rightarrow> P"

text {* Reactive design contracts for CSP/Circus with refusals *}
  
definition mk_CRD :: "'s upred \<Rightarrow> ('e list \<Rightarrow> 'e set \<Rightarrow> 's upred) \<Rightarrow> ('e list \<Rightarrow> 's hrel) \<Rightarrow> ('s, 'e) action" where
"mk_CRD P Q R = \<^bold>R\<^sub>s(\<lceil>P\<rceil>\<^sub>S\<^sub>< \<turnstile> \<lceil>Q x r\<rceil>\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk> \<diamondop> \<lceil>R(x)\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk>)"

syntax
  "_ref_var" :: "logic"
  "_mk_CRD"  :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("[_/ \<turnstile> _/ | _]\<^sub>C")

parse_translation {*
let
  fun ref_var_tr [] = Syntax.free "refs"
    | ref_var_tr _  = raise Match;
in
[(@{syntax_const "_ref_var"}, K ref_var_tr)]
end
*}

translations
  "[P \<turnstile> Q | R]\<^sub>C" => "CONST mk_CRD P (\<lambda> _trace_var _ref_var. Q) (\<lambda> _trace_var. R)"
  "[P \<turnstile> Q | R]\<^sub>C" <= "CONST mk_CRD P (\<lambda> x r. Q) (\<lambda> y. R)"
  
subsection {* Closure properties *}

lemma CSP3_Sup_closure [closure]:
  "A \<subseteq> \<lbrakk>CSP3\<rbrakk>\<^sub>H \<Longrightarrow> (\<Sqinter> A) is CSP3"
  apply (auto simp add: CSP3_def Healthy_def seq_Sup_distl)
  apply (rule cong[of Sup])
  apply (simp)
  using image_iff apply force
done

lemma CSP4_Sup_closure [closure]:
  "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H \<Longrightarrow> (\<Sqinter> A) is CSP4"
  apply (auto simp add: CSP4_def Healthy_def seq_Sup_distr)
  apply (rule cong[of Sup])
  apply (simp)
  using image_iff apply force
done
  
lemma NCSP_Sup_closure [closure]: "\<lbrakk> A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H; A \<noteq> {} \<rbrakk> \<Longrightarrow> (\<Sqinter> A) is NCSP"
  apply (rule NCSP_intro, simp_all add: closure)
  apply (metis (no_types, lifting) Ball_Collect CSP3_Sup_closure NCSP_implies_CSP3)
  apply (metis (no_types, lifting) Ball_Collect CSP4_Sup_closure NCSP_implies_CSP4)
done

lemma NCSP_SUP_closure [closure]: "\<lbrakk> \<And> i. P(i) is NCSP; A \<noteq> {} \<rbrakk> \<Longrightarrow> (\<Sqinter> i\<in>A. P(i)) is NCSP"
  by (metis (mono_tags, lifting) Ball_Collect NCSP_Sup_closure image_iff image_is_empty)

lemma NCSP_cond_srea [closure]:
  assumes "P is NCSP" "Q is NCSP"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is NCSP"
  by (rule NCSP_NSRD_intro, simp_all add: closure rdes assms unrest)

lemma AssignsCSP_CSP [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP"
  by (simp add: AssignsCSP_def RHS_tri_design_is_SRD unrest)

lemma AssignsCSP_CSP3 [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP3"
  by (rule CSP3_intro, simp add: closure, rel_auto)

lemma AssignsCSP_CSP4 [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP4"
  by (rule CSP4_intro, simp add: closure, rel_auto+)

lemma AssignsCSP_NCSP [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is NCSP"
  by (simp add: AssignsCSP_CSP AssignsCSP_CSP3 AssignsCSP_CSP4 NCSP_intro)

lemma preR_AssignsCSP [rdes]: "pre\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = true\<^sub>r"
  by (rel_auto)

lemma periR_AssignsCSP [rdes]: "peri\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = false"
  by (rel_auto)

lemma postR_AssignsCSP [rdes]: "post\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S)"
  apply (rel_auto) using minus_zero_eq by auto

lemma R2c_tr_ext: "R2c ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>) = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>)"
  apply (rel_auto)
  apply (metis append_Nil diff_add_cancel_left' plus_list_def zero_list_def)
  apply (simp add: zero_list_def)
done

lemma AssignCSP_list_update_CSP [closure]:
  "AssignCSP_list_update x k v is CSP"
  by (simp add: AssignCSP_list_update_def RHS_tri_design_is_SRD unrest)
    
lemma preR_AssignCSP_list_update [rdes]: 
  "pre\<^sub>R(AssignCSP_list_update x k v) = R1(\<lceil>k \<in>\<^sub>u dom\<^sub>u(&x)\<rceil>\<^sub>S\<^sub><)"
  by (rel_auto)

lemma periR_AssignCSP_list_update [rdes]:
  "peri\<^sub>R(AssignCSP_list_update x k v) = R1(\<not> \<lceil>k \<in>\<^sub>u dom\<^sub>u(&x)\<rceil>\<^sub>S\<^sub><)"
  by (rel_auto)

lemma post_AssignCSP_list_update [rdes]:
  "post\<^sub>R(AssignCSP_list_update x k v) = (($tr\<acute> =\<^sub>u $tr \<and> \<lceil>x[k] := v\<rceil>\<^sub>S) \<triangleleft> \<lceil>k \<in>\<^sub>u dom\<^sub>u(&x)\<rceil>\<^sub>S\<^sub>< \<triangleright> R1(true))"
  by (rel_auto, simp_all add: minus_zero_eq zero_list_def) 

lemma AssignCSP_list_update_NCSP [closure]:
  "(AssignCSP_list_update x k v) is NCSP"
proof (rule NCSP_intro)
  show "{x[k]} :=\<^sub>C v is CSP"
    by (simp add: closure)
  show "{x[k]} :=\<^sub>C v is CSP3"
    by (rule CSP3_SRD_intro, simp_all add: closure rdes unrest)
  show "{x[k]} :=\<^sub>C v is CSP4"
    by (rule CSP4_tri_intro, simp_all add: closure rdes unrest, rel_auto)
qed
  
lemma ref_unrest_abs_st [unrest]:
  "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> [P]\<^sub>S"
  "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> [P]\<^sub>S"
  by (rel_simp, auto simp add: des_vars.defs rp_vars.defs)+
  
lemma NCSP_state_srea [closure]: "P is NCSP \<Longrightarrow> state 'a \<bullet> P is NCSP"
  apply (rule NCSP_NSRD_intro)
  apply (simp_all add: closure rdes)
  apply (simp_all add: state_srea_def unrest closure)
done
    
lemma R1_DoAct: "R1(do\<^sub>u(a)) = do\<^sub>u(a)"
  by (rel_auto)

lemma R2c_DoAct: "R2c(do\<^sub>u(a)) = do\<^sub>u(a)"
  by (rel_auto, simp_all add: zero_list_def minus_zero_eq, (metis less_eq_list_def prefix_concat_minus)+)

lemma DoCSP_alt_def: "do\<^sub>C(a) = R3h(CSP1($ok\<acute> \<and> do\<^sub>u(a)))"
  apply (simp add: DoCSP_def RHS_def design_def impl_alt_def  R1_R3h_commute R2c_R3h_commute R2c_disj
                   R2c_not R2c_ok R2c_ok' R2c_and R2c_DoAct R1_disj R1_extend_conj' R1_DoAct)
  apply (rel_auto)
done

lemma DoAct_unrests [unrest]:
  "$ok \<sharp> do\<^sub>u(a)" "$wait \<sharp> do\<^sub>u(a)"
  by (pred_auto)+

lemma DoCSP_RHS_tri [rdes_def]:
  "do\<^sub>C(a) = \<^bold>R\<^sub>s(true \<turnstile> (($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) \<diamondop> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st)))"
  by (simp add: DoCSP_def do\<^sub>u_def wait'_cond_def)

lemma CSP_DoCSP [closure]: "do\<^sub>C(a) is CSP"
  by (simp add: DoCSP_def do\<^sub>u_def RHS_design_is_SRD unrest)

lemma preR_DoCSP [rdes]: "pre\<^sub>R(do\<^sub>C(a)) = true\<^sub>r"
  by (simp add: DoCSP_def rea_pre_RHS_design unrest usubst R2c_true)

lemma periR_DoCSP [rdes]: "peri\<^sub>R(do\<^sub>C(a)) = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)"
  apply (rel_auto) using minus_zero_eq by blast

lemma postR_DoCSP [rdes]: "post\<^sub>R(do\<^sub>C(a)) = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st)"
  apply (rel_auto)
  using Prefix_Order.prefixE zero_list_def apply fastforce
  apply (simp add: zero_list_def)
done

lemma CSP3_DoCSP [closure]: "do\<^sub>C(a) is CSP3"
  by (rule CSP3_intro[OF CSP_DoCSP])
     (simp add: DoCSP_def do\<^sub>u_def RHS_def design_def R1_def R2c_def R2s_def R3h_def unrest usubst)

lemma CSP4_DoCSP [closure]: "do\<^sub>C(a) is CSP4"
  by (rule CSP4_tri_intro[OF CSP_DoCSP], simp_all add: preR_DoCSP periR_DoCSP postR_DoCSP unrest)

lemma NCSP_DoCSP [closure]: "do\<^sub>C(a) is NCSP"
  by (metis CSP3_DoCSP CSP4_DoCSP CSP_DoCSP Healthy_def NCSP_def comp_apply)

lemma CSP_PrefixCSP [closure]: "PrefixCSP a P is CSP"
  by (simp add: PrefixCSP_def closure)

lemma CSP3_PrefixCSP [closure]:
  "PrefixCSP a P is CSP3"
  by (metis (no_types, hide_lams) CSP3_DoCSP CSP3_def Healthy_def PrefixCSP_def seqr_assoc)

lemma CSP4_PrefixCSP [closure]:
  assumes "P is CSP" "P is CSP4"
  shows "PrefixCSP a P is CSP4"
  by (metis (no_types, hide_lams) CSP4_def Healthy_def PrefixCSP_def assms(1) assms(2) seqr_assoc)

lemma NCSP_PrefixCSP [closure]:
  assumes "P is NCSP"
  shows "PrefixCSP a P is NCSP"
  by (metis (no_types, hide_lams) CSP3_PrefixCSP CSP3_commutes_CSP4 CSP4_Idempotent CSP4_PrefixCSP
            CSP_PrefixCSP Healthy_Idempotent Healthy_def NCSP_def NCSP_implies_CSP assms comp_apply)

lemma PrefixCSP_type [closure]: "PrefixCSP a \<in> \<lbrakk>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  using CSP_PrefixCSP by blast

lemma PrefixCSP_Continuous [closure]: "Continuous (PrefixCSP a)"
   by (simp add: Continuous_def PrefixCSP_def ContinuousD[OF SRD_Continuous] seq_Sup_distl)

lemma Guard_tri_design [rdes_def]:
  "g &\<^sub>u P = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<turnstile> (peri\<^sub>R(P) \<triangleleft> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R(P)))"
proof -
  have "(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R P \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>) = (peri\<^sub>R(P) \<triangleleft> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R(P))"
    by (rel_auto)
  thus ?thesis by (simp add: Guard_def)
qed

lemma CSP_Guard [closure]: "b &\<^sub>u P is CSP"
  by (simp add: Guard_def, rule RHS_design_is_SRD, simp_all add: unrest)

lemma preR_Guard [rdes]: "P is CSP \<Longrightarrow> pre\<^sub>R(b &\<^sub>u P) = (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P)"
  by (simp add: Guard_tri_design rea_pre_RHS_design usubst unrest R2c_preR R2c_lift_state_pre
      R2c_rea_impl R1_rea_impl R1_preR Healthy_if)

lemma periR_Guard:
  "\<lbrakk> P is CSP; $wait\<acute> \<sharp> pre\<^sub>R(P) \<rbrakk> \<Longrightarrow> peri\<^sub>R(b &\<^sub>u P) = ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<Rightarrow>\<^sub>r (peri\<^sub>R P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)))"
  apply (simp add: Guard_tri_design rea_peri_RHS_design usubst unrest R1_rea_impl R2c_rea_not R2c_rea_impl R2c_preR R2c_periR R2c_tr'_minus_tr R2c_lift_state_pre R2c_condr)
  apply (rel_blast)
done
    
lemma periR_Guard' [rdes]:
  "P is NCSP \<Longrightarrow> peri\<^sub>R(b &\<^sub>u P) = ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<Rightarrow>\<^sub>r (peri\<^sub>R P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)))"
  by (simp add: NCSP_implies_CSP NCSP_implies_NSRD NSRD_wait'_unrest_pre periR_Guard)

lemma postR_Guard:
  "\<lbrakk> P is CSP; $wait\<acute> \<sharp> pre\<^sub>R(P) \<rbrakk> \<Longrightarrow> post\<^sub>R(b &\<^sub>u P) = ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<Rightarrow>\<^sub>r (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R P))"
  by (simp add: Guard_tri_design rea_post_RHS_design usubst unrest R2c_rea_not R2c_and R2c_rea_impl
      R2c_preR R2c_postR R2c_tr'_minus_tr R2c_lift_state_pre R2c_condr R1_rea_impl R1_extend_conj'
      R1_post_SRD)

lemma postR_Guard' [rdes]:
  "P is NCSP \<Longrightarrow> post\<^sub>R(b &\<^sub>u P) = ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<Rightarrow>\<^sub>r (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R P))"
  by (simp add: NCSP_implies_CSP NCSP_implies_NSRD NSRD_wait'_unrest_pre postR_Guard)
  
lemma CSP3_Guard [closure]:
  assumes "P is CSP" "P is CSP3"
  shows "b &\<^sub>u P is CSP3"
proof -
  from assms have 1:"$ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>"
    by (simp add: CSP_Guard CSP3_iff)
  hence "$ref \<sharp> pre\<^sub>R (P\<lbrakk>0/$tr\<rbrakk>)" "$ref \<sharp> pre\<^sub>R P" "$ref \<sharp> cmt\<^sub>R P"
    by (pred_blast)+
  hence "$ref \<sharp> (b &\<^sub>u P)\<lbrakk>false/$wait\<rbrakk>"
    by (simp add: CSP3_iff Guard_def RHS_def R1_def R2c_def R2s_def R3h_def design_def unrest usubst)
  thus ?thesis
    by (metis CSP3_intro CSP_Guard)
qed

lemma CSP4_Guard [closure]:
  assumes "P is CSP" "P is CSP4"
  shows "b &\<^sub>u P is CSP4"
proof (rule CSP4_tri_intro[OF CSP_Guard])
  show "(\<not>\<^sub>r pre\<^sub>R (b &\<^sub>u P)) ;; R1 true = (\<not>\<^sub>r pre\<^sub>R (b &\<^sub>u P))"
  proof -
    have a:"(\<not>\<^sub>r pre\<^sub>R P) ;; R1 true = (\<not>\<^sub>r pre\<^sub>R P)"
      by (simp add: CSP4_neg_pre_unit assms(1) assms(2))
    have "(\<not>\<^sub>r (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P)) ;; R1 true = (\<not>\<^sub>r (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P))"
    proof -
      have 1:"(\<not>\<^sub>r (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P)) = (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> (\<not>\<^sub>r pre\<^sub>R P))"
        by (rel_auto)
      also have 2:"... = (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> ((\<not>\<^sub>r pre\<^sub>R P) ;; R1 true))"
        by (simp add: a)
      also have 3:"... = (\<not>\<^sub>r (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P)) ;; R1 true"
        by (rel_auto)
      finally show ?thesis ..
    qed
    thus ?thesis
      by (simp add: preR_Guard periR_Guard NSRD_CSP4_intro assms unrest)
  qed
  show "$st\<acute> \<sharp> peri\<^sub>R (b &\<^sub>u P)"
    by (simp add: preR_Guard periR_Guard NSRD_CSP4_intro assms unrest)
  show "$ref\<acute> \<sharp> post\<^sub>R (b &\<^sub>u P)"
    by (simp add: preR_Guard postR_Guard NSRD_CSP4_intro assms unrest)
qed

lemma NCSP_Guard [closure]:
  assumes "P is NCSP"
  shows "b &\<^sub>u P is NCSP"
proof -
  have "P is CSP"
    using NCSP_implies_CSP assms by blast
  then show ?thesis
    by (metis (no_types) CSP3_Guard CSP3_commutes_CSP4 CSP4_Guard CSP4_Idempotent CSP_Guard Healthy_Idempotent Healthy_def NCSP_def assms comp_apply)
qed
  
subsection {* Sequential Process Laws *}

lemma Stop_left_zero:
  assumes "P is CSP"
  shows "Stop ;; P = Stop"
  by (simp add: NSRD_seq_post_false assms NCSP_implies_NSRD NCSP_Stop postR_Stop)

lemma AssignsCSP_id: "\<langle>id\<rangle>\<^sub>C = Skip"
  by (rel_auto)

lemma Guard_rdes_def:
  assumes "$ok\<acute> \<sharp> P"
  shows "g &\<^sub>u (\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> Q \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
proof -
  have "g &\<^sub>u (\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
    by (simp add: Guard_def)
  also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> R1(R2c(cmt\<^sub>s \<dagger> (P \<Rightarrow> Q))) \<or>  \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
    by (simp add: rea_pre_RHS_design rea_cmt_RHS_design)
  also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> R1(R2c(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> R1(R2c(cmt\<^sub>s \<dagger> (P \<Rightarrow> Q))) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> R1(R2c(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"
     by (simp add: R1_R2c_commute R1_disj R1_extend_conj' R1_idem R2c_and R2c_disj R2c_idem)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> cmt\<^sub>s \<dagger> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_cmt)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> cmt\<^sub>s \<dagger> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: usubst)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_cmt)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r (pre\<^sub>s \<dagger> P)) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (rel_auto)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>s \<dagger> P)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_pre)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (rel_auto)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_pre)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> Q \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
   finally show ?thesis .
qed

lemma Guard_comp:
  "g &\<^sub>u h &\<^sub>u P = (g \<and> h) &\<^sub>u P"
  by (rule antisym, rel_blast, rel_blast)

lemma Guard_false [simp]: "false &\<^sub>u P = Stop"
  by (simp add: Guard_def Stop_def rpred closure alpha)

lemma Guard_true [simp]:
  "P is CSP \<Longrightarrow> true &\<^sub>u P = P"
  by (simp add: Guard_def alpha SRD_reactive_design_alt)

lemma ExtChoice_rdes:
  assumes "\<And> i. $ok\<acute> \<sharp> P(i)" "A \<noteq> {}"
  shows "(\<box>i\<in>A \<bullet> \<^bold>R\<^sub>s(P(i) \<turnstile> Q(i))) = \<^bold>R\<^sub>s((\<Squnion>i\<in>A \<bullet> P(i)) \<turnstile> ((\<Squnion>i\<in>A \<bullet> Q(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> Q(i))))"
proof -
  have "(\<box>i\<in>A \<bullet> \<^bold>R\<^sub>s(P(i) \<turnstile> Q(i))) =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> pre\<^sub>R (\<^bold>R\<^sub>s (P i \<turnstile> Q i))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> cmt\<^sub>R (\<^bold>R\<^sub>s (P i \<turnstile> Q i)))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> cmt\<^sub>R (\<^bold>R\<^sub>s (P i \<turnstile> Q i)))))"
    by (simp add: ExtChoice_def)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))))"
    by (simp add: rea_pre_RHS_design rea_cmt_RHS_design)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            R1(R2c
            ((\<Squnion>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))))))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            R1(R2c
            ((\<Squnion>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))))"
    by (simp add: R2c_UINF R2c_condr R1_cond R1_idem R1_R2c_commute R2c_idem R1_UINF assms R1_USUP R2c_USUP)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            cmt\<^sub>s \<dagger>
            ((\<Squnion>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c rdes_export_cmt)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            cmt\<^sub>s \<dagger>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: usubst)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: rdes_export_cmt)
  also have "... =
        \<^bold>R\<^sub>s ((R1(R2c(\<Squnion>i\<in>A \<bullet> (pre\<^sub>s \<dagger> P(i))))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: not_UINF R1_UINF R2c_UINF assms)
  also have "... =
        \<^bold>R\<^sub>s ((R2c(\<Squnion>i\<in>A \<bullet> (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp)
  also have "... =
        \<^bold>R\<^sub>s (((\<Squnion>i\<in>A \<bullet> (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (metis (no_types, lifting) RHS_design_R2c_pre)
  also have "... =
        \<^bold>R\<^sub>s (([$ok \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false] \<dagger> (\<Squnion>i\<in>A \<bullet> P(i))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
  proof -
    from assms have "\<And> i. pre\<^sub>s \<dagger> P(i) = [$ok \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false] \<dagger> P(i)"
      by (rel_auto)
    thus ?thesis
      by (simp add: usubst)
  qed
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> P(i)) \<turnstile> ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: rdes_export_pre not_UINF)
  also have "... = \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> P(i)) \<turnstile> ((\<Squnion>i\<in>A \<bullet> Q(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> Q(i))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto, blast+)

  finally show ?thesis .
qed

lemma ExtChoice_tri_rdes [rdes_def]:
  assumes "\<And> i . $ok\<acute> \<sharp> P\<^sub>1(i)" "A \<noteq> {}"
  shows "(\<box> i\<in>A \<bullet> \<^bold>R\<^sub>s(P\<^sub>1(i) \<turnstile> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> (((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i))) \<diamondop> (\<Sqinter> i\<in>A \<bullet> P\<^sub>3(i))))"
proof -
  have "(\<box> i\<in>A \<bullet> \<^bold>R\<^sub>s(P\<^sub>1(i) \<turnstile> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> ((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))))"
    by (simp add: ExtChoice_rdes assms)
  also
  have "... =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> ((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i)) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))))"
    by (simp add: conj_comm)
  also
  have "... =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> (((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) \<diamondop> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))))"
    by (simp add: cond_conj wait'_cond_def)
  also
  have "... = \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> (((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i))) \<diamondop> (\<Sqinter> i\<in>A \<bullet> P\<^sub>3(i))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma ExtChoice_tri_rdes_def [rdes_def]:
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  shows "ExtChoice A = \<^bold>R\<^sub>s ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<turnstile> (((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<diamondop> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)))"
proof -
  have "((\<Squnion> P\<in>A \<bullet> cmt\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R P)) =
        (((\<Squnion> P\<in>A \<bullet> cmt\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R P)) \<diamondop> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R P))"
    by (rel_auto)
  also have "... = (((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<diamondop> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P))"
    by (rel_auto)
  finally show ?thesis
    by (simp add: ExtChoice_def)
qed

lemma ExtChoice_empty: "ExtChoice {} = Stop"
  by (simp add: ExtChoice_def cond_def Stop_def)

lemma ExtChoice_single:
  "P is CSP \<Longrightarrow> ExtChoice {P} = P"
  by (simp add: ExtChoice_def usup_and uinf_or SRD_reactive_design_alt cond_idem)

(* Small external choice as an indexed big external choice *)

lemma extChoice_alt_def:
  "P \<box> Q = (\<box>i::nat\<in>{0,1} \<bullet> P \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> Q)"
  by (simp add: extChoice_def ExtChoice_def, unliteralise, simp)

lemma extChoice_rdes:
  assumes "$ok\<acute> \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>1"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)))"
proof -
  have "(\<box>i::nat\<in>{0, 1} \<bullet> \<^bold>R\<^sub>s (P\<^sub>1 \<turnstile> P\<^sub>2) \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> \<^bold>R\<^sub>s (Q\<^sub>1 \<turnstile> Q\<^sub>2)) = (\<box>i::nat\<in>{0, 1} \<bullet> \<^bold>R\<^sub>s ((P\<^sub>1 \<turnstile> P\<^sub>2) \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> (Q\<^sub>1 \<turnstile> Q\<^sub>2)))"
    by (simp only: RHS_cond R2c_lit)
  also have "... = (\<box>i::nat\<in>{0, 1} \<bullet> \<^bold>R\<^sub>s ((P\<^sub>1 \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> Q\<^sub>2)))"
    by (simp add: design_condr)
  also have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)))"
    apply (subst ExtChoice_rdes, simp_all add: assms unrest)
    apply unliteralise
    apply (simp add: uinf_or usup_and)
  done
  finally show ?thesis by (simp add: extChoice_alt_def)
qed

lemma extChoice_tri_rdes [rdes_def]:
  assumes "$ok\<acute> \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>1"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
         \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3)))"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
        \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<diamondop> P\<^sub>3 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)))"
    by (simp add: extChoice_rdes assms)
  also
  have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<diamondop> P\<^sub>3 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)))"
    by (simp add: conj_comm)
  also
  have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile>
               (((P\<^sub>2 \<diamondop> P\<^sub>3 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)) \<diamondop> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)))"
    by (simp add: cond_conj wait'_cond_def)
  also
  have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma CSP_ExtChoice [closure]:
  "ExtChoice A is CSP"
  by (simp add: ExtChoice_def RHS_design_is_SRD unrest)

lemma CSP_extChoice [closure]:
  "P \<box> Q is CSP"
  by (simp add: CSP_ExtChoice extChoice_def)

lemma preR_ExtChoice [rdes]:
  assumes "A \<noteq> {}" "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  shows "pre\<^sub>R(ExtChoice A) = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R(P))"
proof -
  have "pre\<^sub>R (ExtChoice A) = (R1 (R2c ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P))))"
    by (simp add: ExtChoice_def rea_pre_RHS_design usubst unrest)
  also from assms have "... = (R1 (R2c (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R(CSP(P))))))"
    by (metis USUP_healthy)
  also from assms have "... = (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R(CSP(P))))"
    by (rel_auto)
  also from assms have "... = (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R(P)))"
    by (metis USUP_healthy)
  finally show ?thesis .
qed

lemma preR_ExtChoice' [rdes]:
  assumes "A \<noteq> {}" "\<And> P. P\<in>A \<Longrightarrow> F(P) is CSP"
  shows "pre\<^sub>R(\<box> P\<in>A \<bullet> F(P)) = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R(F(P)))"
  using assms by (subst preR_ExtChoice, auto)

lemma periR_ExtChoice [rdes]:
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "peri\<^sub>R(ExtChoice A) = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R(P)) \<Rightarrow>\<^sub>r ((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)))"
proof -
  have "peri\<^sub>R (ExtChoice A) = peri\<^sub>R (\<^bold>R\<^sub>s ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R P) \<turnstile>
                                       ((\<Squnion> P \<in> A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P \<in> A \<bullet> peri\<^sub>R P)) \<diamondop>
                                       (\<Sqinter> P \<in> A \<bullet> post\<^sub>R P)))"
    by (simp add: ExtChoice_tri_rdes_def assms)

  also have "... = peri\<^sub>R (\<^bold>R\<^sub>s ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R (CSP P)) \<turnstile>
                             ((\<Squnion> P \<in> A \<bullet> peri\<^sub>R (CSP P)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P \<in> A \<bullet> peri\<^sub>R (CSP P))) \<diamondop>
                              (\<Sqinter> P \<in> A \<bullet> post\<^sub>R P)))"
    by (simp add: UINF_healthy[OF assms(1), THEN sym] USUP_healthy[OF assms(1), THEN sym])

  also have "... = R1 (R2c ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P)) \<Rightarrow>\<^sub>r
                            (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (CSP P))
                             \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                            (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (CSP P))))"
  proof -
    have "(\<Squnion> P\<in>A \<bullet> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false, $wait\<acute> \<mapsto>\<^sub>s true] \<dagger> pre\<^sub>R (CSP P))
         = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P))"
      by (rule USUP_cong, simp add: usubst unrest assms)
    thus ?thesis
      by (simp add: rea_peri_RHS_design Healthy_Idempotent SRD_Idempotent usubst unrest assms)
  qed
  also have "... = R1 ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P)) \<Rightarrow>\<^sub>r
                       (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (CSP P))
                          \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                       (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (CSP P)))"
    by (simp add: R2c_rea_impl R2c_condr R2c_UINF R2c_preR R2c_periR Healthy_Idempotent SRD_Idempotent
                  R2c_tr'_minus_tr R2c_USUP)
  also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P)) \<Rightarrow>\<^sub>r (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (CSP P)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (CSP P)))"
    by (rel_blast)
  finally show ?thesis
    by (simp add: UINF_healthy[OF assms(1), THEN sym] USUP_healthy[OF assms(1), THEN sym])
qed
  
lemma periR_ExtChoice' [rdes]:
  assumes "\<And> P. P\<in>A \<Longrightarrow> F(P) is NCSP"
  shows "peri\<^sub>R(\<box> P\<in>A \<bullet> F(P)) = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R(F(P))) \<Rightarrow>\<^sub>r ((\<Squnion> P\<in>A \<bullet> peri\<^sub>R(F(P))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R(F(P)))))"
  using assms by (subst periR_ExtChoice, auto simp add: closure unrest)

lemma postR_ExtChoice [rdes]:
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "post\<^sub>R(ExtChoice A) = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R(P)) \<Rightarrow>\<^sub>r (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P))"
proof -
  have "post\<^sub>R (ExtChoice A) = post\<^sub>R (\<^bold>R\<^sub>s ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R P) \<turnstile>
                                       ((\<Squnion> P \<in> A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P \<in> A \<bullet> peri\<^sub>R P)) \<diamondop>
                                       (\<Sqinter> P \<in> A \<bullet> post\<^sub>R P)))"
    by (simp add: ExtChoice_tri_rdes_def assms)

  also have "... = post\<^sub>R (\<^bold>R\<^sub>s ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R (CSP P)) \<turnstile>
                             ((\<Squnion> P \<in> A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P \<in> A \<bullet> peri\<^sub>R P)) \<diamondop>
                              (\<Sqinter> P \<in> A \<bullet> post\<^sub>R (CSP P))))"
    by (simp add: UINF_healthy[OF assms(1), THEN sym] USUP_healthy[OF assms(1), THEN sym])

  also have "... = R1 (R2c ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P)) \<Rightarrow>\<^sub>r (\<Sqinter> P\<in>A \<bullet> post\<^sub>R (CSP P))))"
  proof -
    have "(\<Squnion> P\<in>A \<bullet> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false, $wait\<acute> \<mapsto>\<^sub>s false] \<dagger> pre\<^sub>R (CSP P))
         = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P))"
      by (rule USUP_cong, simp add: usubst unrest assms)
    thus ?thesis
      by (simp add: rea_post_RHS_design Healthy_Idempotent SRD_Idempotent usubst unrest assms)
  qed
  also have "... = R1 ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P)) \<Rightarrow>\<^sub>r (\<Sqinter> P\<in>A \<bullet> post\<^sub>R (CSP P)))"
    by (simp add: R2c_rea_impl R2c_condr R2c_UINF R2c_preR R2c_postR Healthy_Idempotent SRD_Idempotent
                  R2c_tr'_minus_tr R2c_USUP)
  also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (CSP P)) \<Rightarrow>\<^sub>r (\<Sqinter> P\<in>A \<bullet> post\<^sub>R (CSP P)))"
    by (rel_blast)
  finally show ?thesis
    by (simp add: UINF_healthy[OF assms(1), THEN sym] USUP_healthy[OF assms(1), THEN sym])
qed

lemma postR_ExtChoice' [rdes]:
  assumes "\<And> P. P\<in>A \<Longrightarrow> F(P) is NCSP"
  shows "post\<^sub>R(\<box> P\<in>A \<bullet> F(P)) = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R(F(P))) \<Rightarrow>\<^sub>r (\<Sqinter> P\<in>A \<bullet> post\<^sub>R(F(P))))"
  using assms by (subst postR_ExtChoice, auto simp add: closure unrest)

lemma preR_extChoice:
  assumes "P is CSP" "Q is CSP" "$wait\<acute> \<sharp> pre\<^sub>R(P)" "$wait\<acute> \<sharp> pre\<^sub>R(Q)"
  shows "pre\<^sub>R(P \<box> Q) = (pre\<^sub>R(P) \<and> pre\<^sub>R(Q))"
  by (simp add: extChoice_def preR_ExtChoice assms usup_and)

lemma preR_extChoice' [rdes]:
  assumes "P is NCSP" "Q is NCSP"  
  shows "pre\<^sub>R(P \<box> Q) = (pre\<^sub>R(P) \<and> pre\<^sub>R(Q))"  
  by (simp add: preR_extChoice closure assms unrest)
    
lemma periR_extChoice:
  assumes "P is CSP" "Q is CSP" "$wait\<acute> \<sharp> pre\<^sub>R(P)" "$wait\<acute> \<sharp> pre\<^sub>R(Q)"
  shows "peri\<^sub>R(P \<box> Q) = (pre\<^sub>R(P) \<and> pre\<^sub>R(Q) \<Rightarrow>\<^sub>r (peri\<^sub>R(P) \<and> peri\<^sub>R(Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (peri\<^sub>R(P) \<or> peri\<^sub>R(Q)))"
  using assms
  by (simp add: extChoice_def, subst periR_ExtChoice, auto simp add: usup_and uinf_or)

lemma periR_extChoice' [rdes]:
  assumes "P is NCSP" "Q is NCSP"
  shows "peri\<^sub>R(P \<box> Q) = (pre\<^sub>R(P) \<and> pre\<^sub>R(Q) \<Rightarrow>\<^sub>r (peri\<^sub>R(P) \<and> peri\<^sub>R(Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (peri\<^sub>R(P) \<or> peri\<^sub>R(Q)))"
  by (simp add: periR_extChoice closure unrest assms)
  
lemma postR_extChoice:
  assumes "P is CSP" "Q is CSP" "$wait\<acute> \<sharp> pre\<^sub>R(P)" "$wait\<acute> \<sharp> pre\<^sub>R(Q)"
  shows "post\<^sub>R(P \<box> Q) = (pre\<^sub>R(P) \<and> pre\<^sub>R(Q) \<Rightarrow>\<^sub>r (post\<^sub>R(P) \<or> post\<^sub>R(Q)))"
  using assms
  by (simp add: extChoice_def, subst postR_ExtChoice, auto simp add: usup_and uinf_or)

lemma postR_extChoice' [rdes]:
  assumes "P is NCSP" "Q is NCSP"
  shows "post\<^sub>R(P \<box> Q) = (pre\<^sub>R(P) \<and> pre\<^sub>R(Q) \<Rightarrow>\<^sub>r (post\<^sub>R(P) \<or> post\<^sub>R(Q)))"
  by (simp add: postR_extChoice closure unrest assms)
    
lemma ExtChoice_cong:
  assumes "\<And> P. P \<in> A \<Longrightarrow> F(P) = G(P)"
  shows "(\<box> P\<in>A \<bullet> F(P)) = (\<box> P\<in>A \<bullet> G(P))"
  using assms image_cong by force

lemma ref_unrest_ExtChoice:
  assumes
    "\<And> P. P \<in> A \<Longrightarrow> $ref \<sharp> pre\<^sub>R(P)"
    "\<And> P. P \<in> A \<Longrightarrow> $ref \<sharp> cmt\<^sub>R(P)"
  shows "$ref \<sharp> (ExtChoice A)\<lbrakk>false/$wait\<rbrakk>"
proof -
  have "\<And> P. P \<in> A \<Longrightarrow> $ref \<sharp> pre\<^sub>R(P\<lbrakk>0/$tr\<rbrakk>)"
    using assms by (rel_auto, (meson least_zero)+)
  with assms show ?thesis
    by (simp add: ExtChoice_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)
qed

lemma CSP4_set_unrest_wait':
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H"
  shows "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
proof -
  fix P
  assume "P \<in> A"
  hence "P is NSRD"
    using NSRD_CSP4_intro assms(1) assms(2) by blast
  thus "$wait\<acute> \<sharp> pre\<^sub>R(P)"
    using NSRD_wait'_unrest_pre by blast
qed

lemma CSP4_set_unrest_st':
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H"
  shows "\<And> P. P \<in> A \<Longrightarrow> $st\<acute> \<sharp> pre\<^sub>R(P)"
proof -
  fix P
  assume "P \<in> A"
  hence "P is NSRD"
    using NSRD_CSP4_intro assms(1) assms(2) by blast
  thus "$st\<acute> \<sharp> pre\<^sub>R(P)"
    using NSRD_st'_unrest_pre by blast
qed

lemma CSP4_ExtChoice:
  assumes "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H"
  shows "ExtChoice A is CSP4"
proof (cases "A = {}")
  case True thus ?thesis
    by (simp add: ExtChoice_empty Healthy_def CSP4_def, simp add: Skip_is_CSP Stop_left_zero)
next
  case False
  have 1:"(\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R (ExtChoice A)) ;;\<^sub>h R1 true) = pre\<^sub>R (ExtChoice A)"
  proof -
    have "\<And> P. P \<in> A \<Longrightarrow> (\<not>\<^sub>r pre\<^sub>R(P)) ;; R1 true = (\<not>\<^sub>r pre\<^sub>R(P))"
      by (metis (no_types, lifting) Ball_Collect CSP4_neg_pre_unit assms(1) assms(2))
    thus ?thesis
      apply (simp add: False preR_ExtChoice CSP4_set_unrest_wait' assms not_UINF seq_UINF_distr not_USUP)
      apply (rule USUP_cong)
      apply (simp add: rpred assms closure)
    done
  qed
  have 2: "$st\<acute> \<sharp> peri\<^sub>R (ExtChoice A)"
  proof -
    have a: "\<And> P. P \<in> A \<Longrightarrow> $st\<acute> \<sharp> pre\<^sub>R(P)"
      using CSP4_set_unrest_st' assms(1) assms(2) by blast
    have b: "\<And> P. P \<in> A \<Longrightarrow> $st\<acute> \<sharp> peri\<^sub>R(P)"
      using CSP4_st'_unrest_peri assms(1) assms(2) by blast
    from a b show ?thesis
      apply (subst periR_ExtChoice)
      apply (simp_all add: assms CSP4_set_unrest_st' CSP4_set_unrest_wait')
      apply (rule CSP4_set_unrest_wait'[of A], simp_all add: unrest assms)
    done
  qed
  have 3: "$ref\<acute> \<sharp> post\<^sub>R (ExtChoice A)"
  proof -
    have a: "\<And> P. P \<in> A \<Longrightarrow> $ref\<acute> \<sharp> pre\<^sub>R(P)"
      by (metis (no_types, lifting) Ball_Collect CSP4_ref'_unrest_pre assms(1) assms(2))
    have b: "\<And> P. P \<in> A \<Longrightarrow> $ref\<acute> \<sharp> post\<^sub>R(P)"
      by (metis (no_types, lifting) Ball_Collect CSP4_ref'_unrest_post assms(1) assms(2))
    from a b show ?thesis
      apply (subst postR_ExtChoice)
      apply (simp_all add: assms CSP4_set_unrest_st' CSP4_set_unrest_wait')
      apply (rule CSP4_set_unrest_wait'[of A], simp_all add: unrest assms)
    done
  qed
  show ?thesis
    by (rule CSP4_tri_intro, simp_all add: 1 2 3 assms closure)
       (metis "1" R1_seqr_closure rea_not_R1 rea_not_not rea_true_R1)
qed

lemma CSP4_extChoice [closure]:
  assumes "P is CSP" "Q is CSP" "P is CSP4" "Q is CSP4"
  shows "P \<box> Q is CSP4"
  by (simp add: extChoice_def, rule CSP4_ExtChoice, simp_all add: assms)

lemma NCSP_ExtChoice [closure]:
  assumes "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H"
  shows "ExtChoice A is NCSP"
proof (cases "A = {}")
  case True
  then show ?thesis by (simp add: ExtChoice_empty closure)
next
  case False
  show ?thesis
  proof (rule NCSP_intro)
    from assms have cls: "A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>CSP3\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>CSP4\<rbrakk>\<^sub>H"
      using NCSP_implies_CSP NCSP_implies_CSP3 NCSP_implies_CSP4 by blast+
    have wu: "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
      using NCSP_implies_NSRD NSRD_wait'_unrest_pre assms by force
    show 1:"ExtChoice A is CSP"
      by (metis (mono_tags) Ball_Collect CSP_ExtChoice NCSP_implies_CSP assms)
    from cls show "ExtChoice A is CSP3"
      by (rule_tac CSP3_SRD_intro, simp_all add: CSP_Healthy_subset_member CSP3_Healthy_subset_member closure rdes unrest wu assms 1 False) 
    from cls show "ExtChoice A is CSP4"
      by (simp add: CSP4_ExtChoice)
  qed
qed

lemma NCSP_extChoice [closure]:
  assumes "P is NCSP" "Q is NCSP"
  shows "P \<box> Q is NCSP"
  by (simp add: NCSP_ExtChoice assms extChoice_def)

lemma ExtChoice_comm:
  "P \<box> Q = Q \<box> P"
  by (unfold extChoice_def, simp add: insert_commute)

lemma ExtChoice_idem:
  "P is CSP \<Longrightarrow> P \<box> P = P"
  by (unfold extChoice_def, simp add: ExtChoice_single)

lemma ExtChoice_assoc:
  assumes "P is CSP" "Q is CSP" "R is CSP"
  shows "P \<box> Q \<box> R = P \<box> (Q \<box> R)"
proof -
  have "P \<box> Q \<box> R = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(R) \<turnstile> cmt\<^sub>R(R))"
    by (simp add: SRD_reactive_design_alt assms(1) assms(2) assms(3))
  also have "... =
    \<^bold>R\<^sub>s (((pre\<^sub>R P \<and> pre\<^sub>R Q) \<and> pre\<^sub>R R) \<turnstile>
          (((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q) \<and> cmt\<^sub>R R)
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
           ((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q) \<or> cmt\<^sub>R R)))"
    by (simp add: extChoice_rdes unrest)
  also have "... =
    \<^bold>R\<^sub>s (((pre\<^sub>R P \<and> pre\<^sub>R Q) \<and> pre\<^sub>R R) \<turnstile>
          (((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<and> cmt\<^sub>R R)
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
            ((cmt\<^sub>R P \<or> cmt\<^sub>R Q) \<or> cmt\<^sub>R R)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... =
    \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> pre\<^sub>R Q \<and> pre\<^sub>R R) \<turnstile>
          ((cmt\<^sub>R P \<and> (cmt\<^sub>R Q \<and> cmt\<^sub>R R) )
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
           (cmt\<^sub>R P \<or> (cmt\<^sub>R Q \<or> cmt\<^sub>R R))))"
    by (simp add: conj_assoc disj_assoc)
  also have "... =
    \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> pre\<^sub>R Q \<and> pre\<^sub>R R) \<turnstile>
          ((cmt\<^sub>R P \<and> (cmt\<^sub>R Q \<and> cmt\<^sub>R R) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R Q \<or> cmt\<^sub>R R))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
           (cmt\<^sub>R P \<or> (cmt\<^sub>R Q \<and> cmt\<^sub>R R) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R Q \<or> cmt\<^sub>R R))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> (\<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(R) \<turnstile> cmt\<^sub>R(R)))"
    by (simp add: extChoice_rdes unrest)
  also have "... = P \<box> (Q \<box> R)"
    by (simp add: SRD_reactive_design_alt assms(1) assms(2) assms(3))
  finally show ?thesis .
qed

lemma ExtChoice_Stop:
  assumes "Q is CSP"
  shows "Stop \<box> Q = Q"
  using assms
proof -
  have "Stop \<box> Q = \<^bold>R\<^sub>s (true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q))"
    by (simp add: Stop_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> ((($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>) \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<or> cmt\<^sub>R Q)))"
    by (simp add: extChoice_rdes unrest)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> (cmt\<^sub>R Q \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> cmt\<^sub>R Q))"
    by (metis (no_types, lifting) cond_def eq_upred_sym neg_conj_cancel1 utp_pred_laws.inf.left_idem)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> cmt\<^sub>R Q)"
    by (simp add: cond_idem)
  also have "... = Q"
    by (simp add: SRD_reactive_design_alt assms)
  finally show ?thesis .
qed

lemma ExtChoice_Chaos:
  assumes "Q is CSP"
  shows "Chaos \<box> Q = Chaos"
proof -
  have "Chaos \<box> Q = \<^bold>R\<^sub>s (false \<turnstile> true) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q))"
    by (simp add: Chaos_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s (false \<turnstile> (cmt\<^sub>R Q \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> true))"
    by (simp add: extChoice_rdes unrest)
  also have "... = \<^bold>R\<^sub>s (false \<turnstile> true)"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = Chaos"
    by (simp add: Chaos_def)
  finally show ?thesis .
qed

lemma Guard_conditional:
  assumes "P is NCSP"
  shows "b &\<^sub>u P = P \<triangleleft> b \<triangleright>\<^sub>R Stop"
  using assms by (rdes_eq)

lemma Conditional_as_Guard:
  assumes "P is NCSP" "Q is NCSP"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q = b &\<^sub>u P \<box> (\<not> b) &\<^sub>u Q"
  using assms by (rdes_eq)

lemma InputCSP_CSP [closure]: "x?(v:A(v)) \<^bold>\<rightarrow> P(v) is CSP"
  by (simp add: CSP_ExtChoice InputCSP_def)

lemma InputCSP_NCSP [closure]: "\<lbrakk> \<And> v. P(v) is NCSP \<rbrakk> \<Longrightarrow> x?(v:A(v)) \<^bold>\<rightarrow> P(v) is NCSP"
  apply (simp add: InputCSP_def)
  apply (rule NCSP_ExtChoice)
  apply (simp add: NCSP_Guard NCSP_PrefixCSP image_Collect_subsetI top_set_def)
done

lemma PrefixCSP_RHS_tri_lemma1:
  "R1 (R2s ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> \<lceil>II\<rceil>\<^sub>R)) = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> \<lceil>II\<rceil>\<^sub>R)"
  apply (rel_auto)
  apply (metis append.left_neutral less_eq_list_def prefix_concat_minus zero_list_def)
  apply (simp add: zero_list_def)
  done

lemma PrefixCSP_RHS_tri_lemma2:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P"
  shows "(($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) \<and> \<not> $wait\<acute>) ;; P = (\<exists> $ref \<bullet> P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  using assms
  by (rel_auto, meson, fastforce)

lemma PrefixCSP_RHS_tri_lemma3:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = (\<exists> $ref \<bullet> P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  using assms
  by (rel_auto, meson)

lemma tr_extend_seqr [rdes]:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
  using assms by (simp add: PrefixCSP_RHS_tri_lemma3 assms unrest ex_unrest)

(*
lemma tr_extend_seqr [rdes]:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P" "P is R2"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>,$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> ^\<^sub>u &tt/$tr,$tr\<acute>\<rbrakk>"
proof -
  have "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
    by (simp add: tr_extend_seqr assms)
  also have "... = (R2 P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"   
    by (simp add: Healthy_if assms)
  also have "... = R1((R2 P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>,$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> ^\<^sub>u ($tr\<acute> - $tr)/$tr,$tr\<acute>\<rbrakk>)"
    apply (simp add: R2_def R2s_def R1_def usubst)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
    by (simp add: R2_form)
  also have "... = R1((\<^bold>\<exists> tt\<^sub>0 \<bullet> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>,$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> ^\<^sub>u &tt/$tr,$tr\<acute>\<rbrakk>)"      
    apply (simp add: usubst)

    
lemma tr_extend_seqr' [rdes]:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P" "P is R2"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = undefined"
proof -
  have "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
    by (simp add: tr_extend_seqr assms)
  also have "... = (R2 P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"   
    by (simp add: Healthy_if assms)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> P\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>0\<guillemotright>)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
    by (simp add: R2_form)
  also have "... = undefined"      
    apply (simp add: usubst)
*)

(* Can the following double negation be simplified? *)

lemma wpR_DoCSP [wp]:
  assumes "P is NCSP"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) wp\<^sub>R pre\<^sub>R P = 
         (\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  by (simp add: wpR_def PrefixCSP_RHS_tri_lemma3 unrest usubst ex_unrest assms closure)    
    
lemma wpR_DoCSP_alt:
  assumes "P is NCSP"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) wp\<^sub>R pre\<^sub>R P = 
         ($tr\<acute> \<ge>\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<Rightarrow>\<^sub>r (pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"  
  by (simp add: wpR_DoCSP assms rea_not_def R1_def usubst unrest, rel_auto)
        
lemma preR_PrefixCSP:
  assumes "P is CSP" "$ref \<sharp> pre\<^sub>R P"
  shows "pre\<^sub>R(PrefixCSP a P) = (\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
proof -
  have "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) wp\<^sub>R pre\<^sub>R P = (\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
    by (simp add: wpR_def PrefixCSP_RHS_tri_lemma3 unrest ex_unrest assms)  
  thus ?thesis
    by (simp add: PrefixCSP_def assms closure rdes rpred Healthy_if)
qed

lemma preR_PrefixCSP_NCSP [rdes]:
  assumes "P is NCSP"
  shows "pre\<^sub>R(PrefixCSP a P) = (\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  by (simp add: CSP3_unrest_ref(1) NCSP_implies_CSP NCSP_implies_CSP3 assms preR_PrefixCSP)

lemma periR_PrefixCSP [rdes]:
  assumes "P is CSP" "P is CSP3" "P is CSP4"
  shows "peri\<^sub>R(PrefixCSP a P) =
         ((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<Rightarrow>\<^sub>r ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> (peri\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>))"
  apply (simp add: PrefixCSP_def assms Healthy_if)
  apply (simp add: assms NSRD_CSP4_intro closure rdes PrefixCSP_RHS_tri_lemma3 unrest ex_unrest usubst rpred wpR_def)
done

lemma postR_PrefixCSP [rdes]:
  assumes "P is CSP" "P is CSP3" "P is CSP4"
  shows "post\<^sub>R(PrefixCSP a P) = ((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<Rightarrow>\<^sub>r (post\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  by (simp add: PrefixCSP_def assms Healthy_if) (simp add: assms NSRD_CSP4_intro closure rdes rpred PrefixCSP_RHS_tri_lemma3 unrest ex_unrest usubst wpR_def)

lemma PrefixCSP_RHS_tri [rdes_def]:
  assumes "P is NCSP"
  shows "PrefixCSP a P =
         \<^bold>R\<^sub>s ((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<turnstile>
             ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> (peri\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<diamondop> (post\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  by (simp add: PrefixCSP_def Healthy_if unrest assms closure NSRD_composition_wp rdes rpred wp)

lemma preR_InputCSP [rdes]:
  assumes "\<And> v. P(v) is NCSP"
  shows "pre\<^sub>R(a?(v:A(v)) \<^bold>\<rightarrow> P(v)) = (\<Squnion> v \<bullet> (\<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R (P(v)))\<lbrakk>$tr ^\<^sub>u \<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>))"
  by (simp add: InputCSP_def rdes closure assms alpha usubst unrest)

lemma periR_InputCSP [rdes]:
  assumes "\<And> v. P(v) is NCSP"
  shows "peri\<^sub>R(a?(v:A(v)) \<^bold>\<rightarrow> P(v)) =
          (pre\<^sub>R(a?(v:A(v)) \<^bold>\<rightarrow> P(v)) \<Rightarrow>\<^sub>r
            (\<Squnion> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<Rightarrow> ((a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u \<notin>\<^sub>u $ref\<acute> \<or> peri\<^sub>R (P(v))\<lbrakk>$tr^\<^sub>u\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
            (\<Sqinter> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<and> (peri\<^sub>R(P(v))\<lbrakk>$tr^\<^sub>u\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>)))"
  using assms by (simp add: InputCSP_def rdes closure assms usubst unrest, rel_blast)

lemma postR_InputCSP [rdes]:
  assumes "\<And> v. P(v) is NCSP"
  shows "post\<^sub>R(a?(v:A(v)) \<^bold>\<rightarrow> P(v)) =
          (pre\<^sub>R(a?(v:A(v)) \<^bold>\<rightarrow> P(v)) \<Rightarrow>\<^sub>r (\<Sqinter> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<and> (post\<^sub>R(P(v))\<lbrakk>$tr^\<^sub>u\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>)))"
  using assms by (simp add: InputCSP_def rdes closure assms usubst unrest, rel_blast)

(*
lemma InputCSP_RHS_tri [rdes_def]:
  assumes "\<And> v. P(v) is NCSP"
  shows "a?(v:A(v)) \<^bold>\<rightarrow> P(v) =
        \<^bold>R\<^sub>s((\<Squnion> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R (P v)\<lbrakk>$tr ^\<^sub>u \<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>)

          \<turnstile>  ((\<Squnion> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<Rightarrow> ((a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u \<notin>\<^sub>u $ref\<acute> \<or> peri\<^sub>R (P(v))\<lbrakk>$tr^\<^sub>u\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>))
               \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
              (\<Sqinter> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<and> (peri\<^sub>R(P(v))\<lbrakk>$tr^\<^sub>u\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>)))

          \<diamondop> (\<Sqinter> v \<bullet> \<lceil>A(v)\<rceil>\<^sub>S\<^sub>< \<and> (post\<^sub>R(P(v))\<lbrakk>$tr^\<^sub>u\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>/$tr\<rbrakk>)))"
*)

lemma outp_constraint_prod:
  "(outp_constraint \<guillemotleft>a\<guillemotright> x \<and> outp_constraint \<guillemotleft>b\<guillemotright> y) =
    outp_constraint \<guillemotleft>(a, b)\<guillemotright> (x, y)"
  by (simp add: outp_constraint_def, pred_auto)
  
text {* Proofs that the input constrained parser versions of output is the same as the regular definition. *}

lemma output_prefix_is_OutputCSP [simp]:
  assumes "A is NCSP"
  shows "x!(P) \<^bold>\<rightarrow> A = OutputCSP x P A" (is "?lhs = ?rhs")
  by (rule SRD_eq_intro, simp_all add: assms closure rdes, rel_auto+)

lemma OutputCSP_pair_simp [simp]:
  "P is NCSP \<Longrightarrow> a.(\<guillemotleft>i\<guillemotright>).(\<guillemotleft>j\<guillemotright>) \<^bold>\<rightarrow> P = OutputCSP a \<guillemotleft>(i,j)\<guillemotright> P"
  using output_prefix_is_OutputCSP[of "P" a]
  by (simp add: outp_constraint_prod InputCSP_def closure del: output_prefix_is_OutputCSP)
    
lemma OutputCSP_triple_simp [simp]:
  "P is NCSP \<Longrightarrow> a.(\<guillemotleft>i\<guillemotright>).(\<guillemotleft>j\<guillemotright>).(\<guillemotleft>k\<guillemotright>) \<^bold>\<rightarrow> P = OutputCSP a \<guillemotleft>(i,j,k)\<guillemotright> P"
  using output_prefix_is_OutputCSP[of "P" a]
  by (simp add: outp_constraint_prod InputCSP_def closure del: output_prefix_is_OutputCSP)
    
text {* Useful laws for reducing assignments and identities within peri and postconditions *}
  
lemma tr_extend_seqr_lit [rdes]:
  fixes P :: "('s, 'e) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = P\<lbrakk>$tr ^\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle>/$tr\<rbrakk>"
  using assms by (rel_auto, meson)

lemma tr_assign_comp [rdes]:
  fixes P :: "('s, 'e) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S) ;; P = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P"
  using assms by (rel_auto, meson)    
    
lemma extChoice_Dist:
  assumes "P is CSP" "S \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "S \<noteq> {}"
  shows "P \<box> (\<Sqinter> S) = (\<Sqinter> Q\<in>S. P \<box> Q)"
proof -
  let ?S1 = "pre\<^sub>R ` S" and ?S2 = "cmt\<^sub>R ` S"
  have "P \<box> (\<Sqinter> S) = P \<box> (\<Sqinter> Q\<in>S \<bullet> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)))"
    by (simp add: SRD_as_reactive_design[THEN sym] Healthy_SUPREMUM UINF_as_Sup_collect assms)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> \<^bold>R\<^sub>s((\<Squnion> Q \<in> S \<bullet> pre\<^sub>R(Q)) \<turnstile> (\<Sqinter> Q \<in> S \<bullet> cmt\<^sub>R(Q)))"
    by (simp add: RHS_design_USUP SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R(P) \<and> (\<Squnion> Q \<in> S \<bullet> pre\<^sub>R(Q))) \<turnstile>
                       ((cmt\<^sub>R(P) \<and> (\<Sqinter> Q \<in> S \<bullet> cmt\<^sub>R(Q)))
                         \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
                        (cmt\<^sub>R(P) \<or> (\<Sqinter> Q \<in> S \<bullet> cmt\<^sub>R(Q)))))"
    by (simp add: extChoice_rdes unrest)
  also have "... = \<^bold>R\<^sub>s ((\<Squnion> Q\<in>S \<bullet> pre\<^sub>R P \<and> pre\<^sub>R Q) \<turnstile>
                       (\<Sqinter> Q\<in>S \<bullet> (cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q)))"
    by (simp add: conj_USUP_dist conj_UINF_dist disj_UINF_dist cond_UINF_dist assms)
  also have "... = (\<Sqinter> Q \<in> S \<bullet> \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> pre\<^sub>R Q) \<turnstile>
                                  ((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q))))"
    by (simp add: assms RHS_design_USUP)
  also have "... = (\<Sqinter> Q\<in>S \<bullet> \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)))"
    by (simp add: extChoice_rdes unrest)
  also have "... = (\<Sqinter> Q\<in>S. P \<box> CSP(Q))"
    by (simp add: UINF_as_Sup_collect, metis (no_types, lifting) Healthy_if SRD_as_reactive_design assms(1))
  also have "... = (\<Sqinter> Q\<in>S. P \<box> Q)"
    by (rule SUP_cong, simp_all add: Healthy_subset_member[OF assms(2)])
  finally show ?thesis .
qed

lemma extChoice_dist:
  assumes "P is CSP" "Q is CSP" "R is CSP"
  shows "P \<box> (Q \<sqinter> R) = (P \<box> Q) \<sqinter> (P \<box> R)"
  using assms extChoice_Dist[of P "{Q, R}"] by simp

lemma GuardedChoiceCSP [rdes_def]:
  assumes "\<And> x. P(x) is NCSP" "A \<noteq> {}"
  shows "(\<box> x\<in>A \<^bold>\<rightarrow> P(x)) =
                   \<^bold>R\<^sub>s ((\<Squnion> x\<in>A \<bullet> \<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R (P x))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<turnstile>
                        ((\<Squnion> x\<in>A \<bullet> \<guillemotleft>x\<guillemotright> \<notin>\<^sub>u $ref\<acute>)
                           \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                         (\<Sqinter> x\<in>A \<bullet> peri\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<guillemotleft>x\<guillemotright>\<rangle>/$tr\<rbrakk>))) \<diamondop>
                      (\<Sqinter> x\<in>A \<bullet> post\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<guillemotleft>x\<guillemotright>\<rangle>/$tr\<rbrakk>)))"
proof -
  have "(\<box> x\<in>A \<^bold>\<rightarrow> P(x))
        = \<^bold>R\<^sub>s ((\<Squnion> x\<in>A \<bullet> \<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R (P x))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<turnstile>
              ((\<Squnion> x\<in>A \<bullet> $tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> (peri\<^sub>R(P x))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
              (\<Sqinter> x\<in>A \<bullet> $tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> (peri\<^sub>R(P x))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)) \<diamondop>
              (\<Sqinter> x\<in>A \<bullet> (post\<^sub>R(P x))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>))"
    by (simp add: PrefixCSP_RHS_tri assms ExtChoice_tri_rdes unrest)
  also
  have "...
        = \<^bold>R\<^sub>s ((\<Squnion> x\<in>A \<bullet> \<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R (P x))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<turnstile>
              ((\<Squnion> x\<in>A \<bullet> \<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> peri\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
               (\<Sqinter> x\<in>A \<bullet> peri\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>))) \<diamondop>
               (\<Sqinter> x\<in>A \<bullet> post\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also
  have "...
        = \<^bold>R\<^sub>s ((\<Squnion> x\<in>A \<bullet> \<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R (P x))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<turnstile>
              ((\<Squnion> x\<in>A \<bullet> \<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> peri\<^sub>R((R1(P x))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
               (\<Sqinter> x\<in>A \<bullet> peri\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>))) \<diamondop>
               (\<Sqinter> x\<in>A \<bullet> post\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)))"
  proof -
    from assms(1) have "\<And> x. R1(P x) = P x"
      by (simp add: Healthy_if closure SRD_healths(1))
     thus ?thesis by (simp)
  qed
  also
  have "...
        = \<^bold>R\<^sub>s ((\<Squnion> x\<in>A \<bullet> \<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R (P x))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>) \<turnstile>
              ((\<Squnion> x\<in>A \<bullet> \<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> x\<in>A \<bullet> peri\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>))) \<diamondop>
               (\<Sqinter> x\<in>A \<bullet> post\<^sub>R((P x)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis
    by (simp add: alpha)
qed

(*
lemma wpR_thing [wp]:
  assumes "\<And> a. P(a) is NCSP"
  shows "(($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) wp\<^sub>R (pre\<^sub>R (P(last\<^sub>u($tr))))) = (pre\<^sub>R(P last\<^sub>u($tr)))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<not> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; (\<not> pre\<^sub>R (P last\<^sub>u($tr))))"
    by (simp add: wpR_def R1_neg_preR closure assms)
  also have "... = (\<not> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; (\<exists> $ref \<bullet> (\<not> pre\<^sub>R (P last\<^sub>u($tr)))))"
    by (simp add: ex_unrest unrest assms closure)
  also have "... = (\<not> (\<exists> $ref \<bullet> (\<not> pre\<^sub>R (P last\<^sub>u($tr))))\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>\<guillemotleft>a\<guillemotright>\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
    by (rel_auto)
  also have "... = ?rhs"
    by (simp add: ex_unrest unrest assms closure usubst)
  finally show ?thesis .
qed

lemma "\<lbrakk> \<And> a. P(a) is NCSP \<rbrakk> \<Longrightarrow> (\<box> x\<in>A \<^bold>\<rightarrow> P(x)) = (\<box> x\<in>A \<^bold>\<rightarrow> Skip) ;; (P x)\<lbrakk>x\<rightarrow>last\<^sub>u($tr)\<rbrakk>"
*)

lemma CSP_mk_CRD [closure]: "[P \<turnstile> Q trace refs | R(trace)]\<^sub>C is CSP"
  by (simp add: mk_CRD_def closure unrest)

lemma preR_mk_CRD [rdes]: "pre\<^sub>R([P \<turnstile> Q trace refs | R(trace) ]\<^sub>C) = R1(\<lceil>P\<rceil>\<^sub>S\<^sub><)"
  by (simp add: mk_CRD_def rea_pre_RHS_design usubst unrest R2c_not R2c_lift_state_pre)

lemma periR_mk_CRD [rdes]: "peri\<^sub>R([P \<turnstile> Q trace refs | R(trace) ]\<^sub>C) = (\<lceil>P\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1((\<lceil>Q trace refs\<rceil>\<^sub>S\<^sub><)\<lbrakk>(trace,refs)\<rightarrow>(&tt,$ref\<acute>)\<^sub>u\<rbrakk>))"
  by (simp add: mk_CRD_def rea_peri_RHS_design usubst unrest R2c_not R2c_lift_state_pre
                impl_alt_def R2c_disj R2c_msubst_tt R1_disj, rel_auto)

lemma postR_mk_CRD [rdes]: "post\<^sub>R([P \<turnstile> Q trace refs | R(trace) ]\<^sub>C) = (\<lceil>P\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1((\<lceil>R(trace)\<rceil>\<^sub>S)\<lbrakk>trace\<rightarrow>&tt\<rbrakk>))"
  by (simp add: mk_CRD_def rea_post_RHS_design usubst unrest R2c_not R2c_lift_state_pre
                impl_alt_def R2c_disj R2c_msubst_tt R1_disj, rel_auto)

text {* Refinement introduction law for contracts *}

lemma CRD_contract_refine:
  assumes
    "Q is CSP" "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R Q`"
    "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> peri\<^sub>R Q \<Rightarrow> \<lceil>P\<^sub>2 t r\<rceil>\<^sub>S\<^sub><\<lbrakk>t\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>`"
    "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R Q \<Rightarrow> \<lceil>P\<^sub>3 x\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk>`"
  shows "[P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3(trace)]\<^sub>C \<sqsubseteq> Q"
proof -
  have "[P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3(trace)]\<^sub>C \<sqsubseteq> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q))"
    using assms by (simp add: mk_CRD_def, rule_tac srdes_tri_refine_intro, simp_all)
  thus ?thesis
    by (simp add: SRD_reactive_tri_design assms(1))
qed

lemma CRD_contract_refine':
  assumes
    "Q is CSP" "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R Q`"
    "\<lceil>P\<^sub>2 t r\<rceil>\<^sub>S\<^sub><\<lbrakk>t\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk> \<sqsubseteq> (\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> peri\<^sub>R Q)"
    "\<lceil>P\<^sub>3 x\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk> \<sqsubseteq> (\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R Q)"
  shows "[P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3(trace)]\<^sub>C \<sqsubseteq> Q"
  using assms by (rule_tac CRD_contract_refine, simp_all add: refBy_order)
  
lemma CRD_refine_CRD: 
  assumes 
    "`\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<Rightarrow> (\<lceil>Q\<^sub>1\<rceil>\<^sub>S\<^sub>< :: ('e,'s) action)`"
    "(\<lceil>P\<^sub>2 x r\<rceil>\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>) \<sqsubseteq> (\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>Q\<^sub>2 x r\<rceil>\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk> :: ('e,'s) action)"
    "\<lceil>P\<^sub>3 x\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk> \<sqsubseteq> (\<lceil>P\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>Q\<^sub>3 x\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>&tt\<rbrakk> :: ('e,'s) action)"
  shows "([P\<^sub>1 \<turnstile> P\<^sub>2 trace refs | P\<^sub>3 trace]\<^sub>C :: ('e,'s) action) \<sqsubseteq> [Q\<^sub>1 \<turnstile> Q\<^sub>2 trace refs | Q\<^sub>3 trace]\<^sub>C"
  using assms
  by (simp add: mk_CRD_def, rule_tac srdes_tri_refine_intro, simp_all add: refBy_order)
    
text {* A healthiness condition for weakly guarded CSP processes *}

definition [upred_defs]: "Productive(P) = P \<parallel>\<^sub>R \<^bold>R\<^sub>s(true \<turnstile> true \<diamondop> ($tr <\<^sub>u $tr\<acute>))"

lemma Productive_RHS_design_form:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R"
  shows "Productive(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> (R \<and> $tr <\<^sub>u $tr\<acute>))"
  using assms by (simp add: Productive_def RHS_tri_design_par unrest)

lemma Productive_form:
  "Productive(SRD(P)) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))"
proof -
  have "Productive(SRD(P)) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) \<parallel>\<^sub>R \<^bold>R\<^sub>s(true \<turnstile> true \<diamondop> ($tr <\<^sub>u $tr\<acute>))"
    by (simp add: Productive_def SRD_as_reactive_tri_design)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))"
    by (simp add: RHS_tri_design_par unrest)
  finally show ?thesis .
qed

lemma Productive_post_refines_tr_increase:
  assumes "P is SRD" "P is Productive" "$wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "($tr <\<^sub>u $tr\<acute>) \<sqsubseteq> (pre\<^sub>R(P) \<and> post\<^sub>R(P))"
proof -
  have "post\<^sub>R(P) = post\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (metis Healthy_def Productive_form assms(1) assms(2))
  also have "... = R1(R2c(pre\<^sub>R(P) \<Rightarrow> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (simp add: rea_post_RHS_design unrest usubst assms, rel_auto)
  also have "... = R1((pre\<^sub>R(P) \<Rightarrow> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (simp add: R2c_impl R2c_preR R2c_postR R2c_and R2c_tr_less_tr' assms)
  also have "($tr <\<^sub>u $tr\<acute>) \<sqsubseteq> (pre\<^sub>R(P) \<and> ...)"
    by (rel_auto)
  finally show ?thesis .
qed

lemma Continuous_Productive [closure]: "Continuous Productive"
  by (simp add: Continuous_def Productive_def, rel_auto)
  
lemma Productive_Miracle [closure]:
  "Miracle is Productive"
  unfolding Miracle_tri_def Healthy_def
  by (subst Productive_RHS_design_form, simp_all add: unrest)

lemma Productive_Stop [closure]:
  "Stop is Productive"
  by (simp add: Stop_RHS_tri_design Healthy_def Productive_RHS_design_form unrest)

lemma Productive_DoCSP [closure]:
  "(do\<^sub>C a :: ('\<sigma>, '\<psi>) action) is Productive"
proof -
  have "(($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) \<and> $tr\<acute> >\<^sub>u $tr :: ('\<sigma>, '\<psi>) action)
        = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st)"
    by (rel_auto, simp add: Prefix_Order.strict_prefixI')
  hence "Productive(do\<^sub>C a) = do\<^sub>C a"
    by (simp add: Productive_RHS_design_form DoCSP_RHS_tri unrest)
  thus ?thesis
    by (simp add: Healthy_def)
qed

lemma Productive_Guard [closure]:
  assumes "P is CSP" "P is Productive" "$wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "b &\<^sub>u P is Productive"
proof -
  have "b &\<^sub>u P = b &\<^sub>u \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))"
    by (metis Healthy_def Productive_form assms(1) assms(2))
  also have "... =
        \<^bold>R\<^sub>s ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<turnstile>
          ((pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)))"
    by (simp add: Guard_tri_design rea_pre_RHS_design rea_peri_RHS_design rea_post_RHS_design unrest assms
        usubst R1_preR Healthy_if R1_rea_impl R1_peri_SRD R1_extend_conj' R2c_preR R2c_not R2c_rea_impl 
        R2c_periR R2c_postR R2c_and R2c_tr_less_tr' R1_tr_less_tr')             
  also have "... = \<^bold>R\<^sub>s ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<turnstile> (peri\<^sub>R P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R P) \<and> $tr\<acute> >\<^sub>u $tr))"
    by (rel_auto)
  also have "... = Productive(b &\<^sub>u P)"
    by (simp add: Productive_def Guard_tri_design RHS_tri_design_par unrest)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma Productive_intro:
  assumes "P is SRD" "($tr <\<^sub>u $tr\<acute>) \<sqsubseteq> (pre\<^sub>R(P) \<and> post\<^sub>R(P))" "$wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "P is Productive"
proof -
  have P:"\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)) = P"
  proof -
    have "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> (pre\<^sub>R(P) \<and> peri\<^sub>R(P)) \<diamondop> (pre\<^sub>R(P) \<and> post\<^sub>R(P)))"
      by (metis (no_types, hide_lams) design_export_pre wait'_cond_conj_exchange wait'_cond_idem)
    also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> (pre\<^sub>R(P) \<and> peri\<^sub>R(P)) \<diamondop> (pre\<^sub>R(P) \<and> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
      by (metis assms(2) utp_pred_laws.inf.absorb1 utp_pred_laws.inf.assoc)
    also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))"
      by (metis (no_types, hide_lams) design_export_pre wait'_cond_conj_exchange wait'_cond_idem)
    finally show ?thesis
      by (simp add: SRD_reactive_tri_design assms(1))
  qed
  thus ?thesis
    by (metis Healthy_def RHS_tri_design_par Productive_def ok'_pre_unrest unrest_true utp_pred_laws.inf_right_idem utp_pred_laws.inf_top_right)
qed

lemma Productive_rdes_intro:
  assumes "($tr <\<^sub>u $tr\<acute>) \<sqsubseteq> R" "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R" "$wait \<sharp> P" "$wait\<acute> \<sharp> P"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) is Productive"
proof (rule Productive_intro)
  show "\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R) is SRD"
    by (simp add: RHS_tri_design_is_SRD assms)

  from assms(1) show "($tr\<acute> >\<^sub>u $tr) \<sqsubseteq> (pre\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R)) \<and> post\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R)))"
    apply (simp add: rea_pre_RHS_design rea_post_RHS_design usubst assms unrest)
    using assms(1) apply (rel_auto)
    apply fastforce
  done

  show "$wait\<acute> \<sharp> pre\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R))"
    by (simp add: rea_pre_RHS_design rea_post_RHS_design usubst R1_def R2c_def R2s_def assms unrest)
qed

lemma Productive_cond_rea [closure]:
  assumes "P is CSP" "P is Productive" "Q is CSP" "Q is Productive"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is Productive"
proof -
  have "P \<triangleleft> b \<triangleright>\<^sub>R Q =
        \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)) \<triangleleft> b \<triangleright>\<^sub>R \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> (post\<^sub>R(Q) \<and> $tr <\<^sub>u $tr\<acute>))"
    by (metis Healthy_if Productive_form assms)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R peri\<^sub>R Q) \<diamondop> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) \<triangleleft> b \<triangleright>\<^sub>R (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr)))"
    by (simp add: cond_srea_form)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R peri\<^sub>R Q) \<diamondop> (((post\<^sub>R P) \<triangleleft> b \<triangleright>\<^sub>R (post\<^sub>R Q)) \<and> $tr\<acute> >\<^sub>u $tr))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... is Productive"
    by (simp add: Healthy_def Productive_RHS_design_form  unrest)
  finally show ?thesis .
qed

lemma Productive_seq_1 [closure]:
  assumes "P is NCSP" "P is Productive" "Q is NCSP"
  shows "P ;; Q is Productive"
proof -
  have "P ;; Q = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)) ;; \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> (post\<^sub>R(Q)))"
    by (metis Healthy_def NCSP_implies_CSP SRD_reactive_tri_design Productive_form assms(1) assms(2) assms(3))
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) wp\<^sub>R pre\<^sub>R Q) \<turnstile>
                       (peri\<^sub>R P \<or> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; peri\<^sub>R Q)) \<diamondop> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; post\<^sub>R Q))"
    by (simp add: RHS_tri_design_composition_wp rpred unrest closure assms wp NSRD_neg_pre_left_zero  SRD_healths ex_unrest wpR_def disj_upred_def)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) wp\<^sub>R pre\<^sub>R Q) \<turnstile>
                       (peri\<^sub>R P \<or> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; peri\<^sub>R Q)) \<diamondop> ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr))"
  proof -
    have "((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; R1(post\<^sub>R Q)) = ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; R1(post\<^sub>R Q) \<and> $tr\<acute> >\<^sub>u $tr)"
      by (rel_auto)
    thus ?thesis
      by (simp add: NCSP_implies_NSRD NSRD_is_SRD R1_post_SRD assms)
  qed
  also have "... is Productive"
    by (rule Productive_rdes_intro, simp_all add: unrest assms closure wpR_def)
  finally show ?thesis .
qed

lemma Productive_seq_2 [closure]:
  assumes "P is NCSP" "Q is NCSP" "Q is Productive"
  shows "P ;; Q is Productive"
proof -
  have "P ;; Q = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P))) ;; \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> (post\<^sub>R(Q) \<and> $tr <\<^sub>u $tr\<acute>))"
    by (metis Healthy_def NCSP_implies_CSP SRD_reactive_tri_design Productive_form assms)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr)))"
    by (simp add: RHS_tri_design_composition_wp rpred unrest closure assms wp NSRD_neg_pre_left_zero  SRD_healths ex_unrest wpR_def disj_upred_def)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr) \<and> $tr\<acute> >\<^sub>u $tr))"
  proof -
    have "(R1(post\<^sub>R P) ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr) \<and> $tr\<acute> >\<^sub>u $tr) = (R1(post\<^sub>R P) ;; (post\<^sub>R Q \<and> $tr\<acute> >\<^sub>u $tr))"
      by (rel_auto)
    thus ?thesis
      by (simp add: NCSP_implies_NSRD NSRD_is_SRD R1_post_SRD assms)
  qed
  also have "... is Productive"
    by (rule Productive_rdes_intro, simp_all add: unrest assms closure wpR_def)
  finally show ?thesis .
qed

lemma Productive_ExtChoice [closure]:
  assumes "A \<noteq> {}" "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>Productive\<rbrakk>\<^sub>H"
  shows "ExtChoice A is Productive"
proof -
  have 1: "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
    using NCSP_implies_NSRD NSRD_wait'_unrest_pre assms(2) by blast
  show ?thesis
  proof (rule Productive_intro, simp_all add: assms closure rdes 1 unrest)
    have "((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) =
          ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Sqinter> P\<in>A \<bullet> (pre\<^sub>R P \<and> post\<^sub>R P)))"
      by (rel_auto)
    moreover have "(\<Sqinter> P\<in>A \<bullet> (pre\<^sub>R P \<and> post\<^sub>R P)) = (\<Sqinter> P\<in>A \<bullet> ((pre\<^sub>R P \<and> post\<^sub>R P) \<and> $tr <\<^sub>u $tr\<acute>))"
      by (rule UINF_cong, metis (no_types, lifting) "1" Ball_Collect NCSP_implies_CSP Productive_post_refines_tr_increase assms utp_pred_laws.inf.absorb1)

    ultimately show "($tr\<acute> >\<^sub>u $tr) \<sqsubseteq> ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R P) \<and> ((\<Squnion> P \<in> A \<bullet> pre\<^sub>R P) \<Rightarrow>\<^sub>r (\<Sqinter> P \<in> A \<bullet> post\<^sub>R P)))"
      by (simp, rel_auto, blast)
  qed
qed

lemma Productive_extChoice [closure]:
  assumes "P is NCSP" "Q is NCSP" "P is Productive" "Q is Productive"
  shows "P \<box> Q is Productive"
  by (simp add: extChoice_def Productive_ExtChoice assms)

lemma Productive_PrefixCSP [closure]: "P is NCSP \<Longrightarrow> PrefixCSP a P is Productive"
  by (simp add: Healthy_if NCSP_DoCSP NCSP_implies_NSRD NSRD_is_SRD PrefixCSP_def Productive_DoCSP Productive_seq_1)

lemma Productive_InputCSP [closure]:
  "\<lbrakk> \<And> v. P(v) is NCSP \<rbrakk> \<Longrightarrow> x?(v:A(v)) \<^bold>\<rightarrow> P(v) is Productive"
  by (auto simp add: InputCSP_def unrest closure intro: Productive_ExtChoice)

lemma preR_Productive [rdes]:
  assumes "P is CSP"
  shows "pre\<^sub>R(Productive(P)) = pre\<^sub>R(P)"
proof -
  have "pre\<^sub>R(Productive(P)) = pre\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (metis Healthy_def Productive_form assms)
  thus ?thesis
    by (simp add: rea_pre_RHS_design usubst unrest R2c_not R2c_preR R1_preR Healthy_if assms)
qed

lemma periR_Productive [rdes]:
  assumes "P is NCSP"
  shows "peri\<^sub>R(Productive(P)) = peri\<^sub>R(P)"
proof -
  have "peri\<^sub>R(Productive(P)) = peri\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (metis Healthy_def NCSP_implies_CSP Productive_form assms)
  also have "... = R1 (R2c (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P))"
    by (simp add: rea_peri_RHS_design usubst unrest R2c_not assms closure)
  also have "... = (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)"
    by (simp add: R1_rea_impl R2c_rea_impl R2c_preR R2c_peri_SRD
                  R1_peri_SRD assms closure R1_tr_less_tr' R2c_tr_less_tr')
  finally show ?thesis
    by (simp add: SRD_peri_under_pre assms unrest closure)
qed

lemma postR_Productive [rdes]:
  assumes "P is NCSP"
  shows "post\<^sub>R(Productive(P)) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)"
proof -
  have "post\<^sub>R(Productive(P)) = post\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))"
    by (metis Healthy_def NCSP_implies_CSP Productive_form assms)
  also have "... = R1 (R2c (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr))"
    by (simp add: rea_post_RHS_design usubst unrest assms closure)
  also have "... = (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)"
    by (simp add: R1_rea_impl R2c_rea_impl R2c_preR R2c_and R1_extend_conj' R2c_post_SRD
             R1_post_SRD assms closure R1_tr_less_tr' R2c_tr_less_tr')
  finally show ?thesis .
qed
  
lemma preR_frame_seq_export:
  assumes "P is NCSP" "P is Productive" "Q is NCSP"
  shows "(pre\<^sub>R P \<and> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q) = (pre\<^sub>R P \<and> (post\<^sub>R P ;; Q))"
proof -
  have "(pre\<^sub>R P \<and> (post\<^sub>R P ;; Q)) = (pre\<^sub>R P \<and> ((pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) ;; Q))"
    by (simp add: SRD_post_under_pre assms closure unrest)
  also have "... = (pre\<^sub>R P \<and> (((\<not>\<^sub>r pre\<^sub>R P) ;; Q \<or> (pre\<^sub>R P \<Rightarrow>\<^sub>r R1(post\<^sub>R P)) ;; Q)))"
    by (simp add: NCSP_implies_NSRD NSRD_is_SRD R1_post_SRD assms(1) rea_impl_def seqr_or_distl R1_preR Healthy_if)
  also have "... = (pre\<^sub>R P \<and> (((\<not>\<^sub>r pre\<^sub>R P) ;; Q \<or> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q)))"
  proof -
    have "(pre\<^sub>R P \<or> \<not>\<^sub>r pre\<^sub>R P) = R1 true"
      by (simp add: R1_preR rea_not_or)
    then show ?thesis
      by (metis (no_types) R1_def conj_comm disj_comm disj_conj_distr rea_impl_def seqr_or_distl utp_pred_laws.inf_top.left_neutral utp_pred_laws.sup_left_idem)
  qed
  also have "... = (pre\<^sub>R P \<and> (((\<not>\<^sub>r pre\<^sub>R P) \<or> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q)))"
    by (simp add: NSRD_neg_pre_left_zero assms closure SRD_healths)
  also have "... = (pre\<^sub>R P \<and> (pre\<^sub>R P \<and> post\<^sub>R P) ;; Q)"
    by (rel_blast)
  finally show ?thesis ..
qed

(*
lemma ExtChoice_seq_distr:
  assumes "A \<subseteq> \<lbrakk>NCSP\<rbrakk>\<^sub>H" "A \<subseteq> \<lbrakk>Productive\<rbrakk>\<^sub>H" "A \<noteq> {}" "Q is NCSP"
  shows "(\<box> P\<in>A \<bullet> P) ;; Q = (\<box> P\<in>A \<bullet> P ;; Q)"
proof -
  have [closure]: "\<And> P. P \<in> A \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P)"
    by (simp add: NCSP_Healthy_subset_member NCSP_implies_NSRD NSRD_wait'_unrest_pre assms(1))
  have [closure]: "(\<lambda>P. NCSP(P) ;; Q) ` A \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H"
    by (auto simp add: Healthy_if closure assms(1) assms(4))
  have nc2: "(\<box> P\<in>A \<bullet> P ;; Q) = (\<box> P\<in>A \<bullet> NCSP(P) ;; Q)"
    by (rule_tac ExtChoice_cong, simp add: Healthy_if closure assms)

  have p1: "((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) wp\<^sub>R pre\<^sub>R Q =
            (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R P \<Rightarrow> post\<^sub>R P) wp\<^sub>R pre\<^sub>R Q)"
      by (simp add: UINF_impl[THEN sym] wp)
    also have "... = (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q)"
      by (rule USUP_cong, simp add: SRD_post_under_pre closure assms Healthy_if)
    finally show ?thesis .
  qed

  have p2: "((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) = (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)"
  proof -
    have "((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) = (\<Sqinter> P\<in>A \<bullet> pre\<^sub>R P \<Rightarrow> post\<^sub>R P)"
      by (rel_auto)
    also have "... = (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)"
      by (rule UINF_cong, simp add:  SRD_post_under_pre assms(1) closure)
    finally show ?thesis .
  qed

  -- {* We perform the proof by showing the pre-, peri- and postconditions are the same *}

  have pre: "pre\<^sub>R((\<box> P\<in>A \<bullet> P) ;; Q) = pre\<^sub>R (\<box> P\<in>A \<bullet> P ;; Q)"
  proof -
    have "pre\<^sub>R((\<box> P\<in>A \<bullet> P) ;; Q) = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) wp\<^sub>R pre\<^sub>R Q)"
      by (simp add: rdes closure assms wp)
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q))"
      by (simp add: p1)
    also have "... = (\<Squnion> P\<in>A \<bullet> (pre\<^sub>R P \<and> (post\<^sub>R P wp\<^sub>R pre\<^sub>R Q)))"
      by (rel_blast)
    also have "... = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R (NCSP P) \<and> post\<^sub>R (NCSP P) wp\<^sub>R pre\<^sub>R Q)"
      by (rule USUP_cong, simp add: closure assms Healthy_if)
    also have "... = pre\<^sub>R (\<box> P\<in>A \<bullet> P ;; Q)"
      by (simp add: rdes closure assms nc2)
    finally show ?thesis .
  qed

  have peri: "peri\<^sub>R((\<box> P\<in>A \<bullet> P) ;; Q) = peri\<^sub>R (\<box> P\<in>A \<bullet> P ;; Q)" (is "?lhs = ?rhs")
    apply (simp_all add: rdes nc2 closure assms p1 spec_cond_dist)
  proof -
    have "?rhs = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                  (\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q \<Rightarrow> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                  ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                   (\<Sqinter> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q \<Rightarrow> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
        apply (simp_all add: rdes nc2 closure assms p1 spec_cond_dist unrest)
        apply (subst USUP_healthy[of "A" "NCSP", THEN sym], simp add: assms)+
        apply (subst UINF_healthy[of "A" "NCSP", THEN sym], simp add: assms)+
        apply (simp)
    done
    also
    have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                  (\<Squnion> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                  ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                   (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
      by (rel_blast)
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                      (\<Squnion> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                      (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
      by (simp add: spec_cond_dist[THEN sym] UINF_conj_UINF)
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                      (\<Squnion> P\<in>A \<bullet> peri\<^sub>R P \<or> pre\<^sub>R P \<and> (post\<^sub>R P ;; peri\<^sub>R Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                      (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
      by (rel_auto)
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                      (\<Squnion> P\<in>A \<bullet> peri\<^sub>R P \<or> pre\<^sub>R P \<and> ((post\<^sub>R P \<and> $tr <\<^sub>u $tr\<acute>) ;; peri\<^sub>R Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
                      (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q))"
      oops
    also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                  ((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<or>
                  ((\<Sqinter> P\<in>A \<bullet> post\<^sub>R P) ;; peri\<^sub>R Q))"
      apply (rel_simp, safe)
      apply blast+
      apply meson+



    have "?lhs = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
                  ((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<or>
                  ((\<Sqinter> P\<in>A \<bullet> post\<^sub>R P) ;; peri\<^sub>R Q))"
      by (simp_all add: rdes nc2 closure assms p1 spec_cond_dist, simp add: p2, rel_auto)
    (*
"     ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R P) \<and> (\<Squnion> P\<in>A \<bullet> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<Rightarrow>
     ((\<Squnion> P\<in>A \<bullet> peri\<^sub>R P) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R P)) \<or>
     ((\<Sqinter> P\<in>A \<bullet> post\<^sub>R P)) ;; peri\<^sub>R Q)" *)


    apply (subst rdes)
    apply (simp_all add: closure assms)
*)

lemma PrefixCSP_dist:
  "PrefixCSP a (P \<sqinter> Q) = (PrefixCSP a P) \<sqinter> (PrefixCSP a Q)"
  using Continuous_Disjunctous Disjunctuous_def PrefixCSP_Continuous by auto

lemma DoCSP_is_Prefix:
  "do\<^sub>C(a) = PrefixCSP a Skip"
  by (simp add: PrefixCSP_def Healthy_if closure, metis CSP4_DoCSP CSP4_def Healthy_def)

lemma Prefix_CSP_seq:
  assumes "P is CSP" "Q is CSP"
  shows "(PrefixCSP a P) ;; Q = (PrefixCSP a (P ;; Q))"
  by (simp add: PrefixCSP_def seqr_assoc Healthy_if assms closure)

subsection {* Guarded recursion *}

text {* Proofs that guarded recursion yields a unique fixed-point *}

text {* Guardedness variant *}

abbreviation gvrt :: "(('\<sigma>,'\<phi>) st_csp \<times> ('\<sigma>,'\<phi>) st_csp) chain" where
"gvrt(n) \<equiv> ($tr \<le>\<^sub>u $tr\<acute> \<and> #\<^sub>u(&tt) <\<^sub>u \<guillemotleft>n\<guillemotright>)"

lemma gvrt_chain: "chain gvrt"
  apply (simp add: chain_def, safe)
  apply (rel_simp)
  apply (rel_simp)+
done

lemma gvrt_limit: "\<Sqinter> (range gvrt) = ($tr \<le>\<^sub>u $tr\<acute>)"
  by (rel_auto)

definition Guarded :: "(('\<sigma>,'\<phi>) action \<Rightarrow> ('\<sigma>,'\<phi>) action) \<Rightarrow> bool" where
"Guarded(F) = (\<forall> X n. (F(X) \<and> gvrt(n+1)) = (F(X \<and> gvrt(n)) \<and> gvrt(n+1)))"

lemma GuardedI: "\<lbrakk> \<And> X n. (F(X) \<and> gvrt(n+1)) = (F(X \<and> gvrt(n)) \<and> gvrt(n+1)) \<rbrakk> \<Longrightarrow> Guarded F"
  by (simp add: Guarded_def)

theorem guarded_fp_uniq:
  assumes "mono F" "F \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H" "Guarded F"
  shows "\<mu> F = \<nu> F"
proof -
  have "constr F gvrt"
    using assms apply (auto simp add: constr_def gvrt_chain Guarded_def tcontr_alt_def')
  hence "($tr \<le>\<^sub>u $tr\<acute> \<and> \<mu> F) = ($tr \<le>\<^sub>u $tr\<acute> \<and> \<nu> F)"
    apply (rule constr_fp_uniq)
    apply (simp add: assms)
    using gvrt_limit apply blast
  done
  moreover have "($tr \<le>\<^sub>u $tr\<acute> \<and> \<mu> F) = \<mu> F"
  proof -
    have "\<mu> F is R1"
      by (rule SRD_healths(1), rule Healthy_mu, simp_all add: assms)
    thus ?thesis
      by (metis Healthy_def R1_def conj_comm)
  qed
  moreover have "($tr \<le>\<^sub>u $tr\<acute> \<and> \<nu> F) = \<nu> F"
  proof -
    have "\<nu> F is R1"
      by (rule SRD_healths(1), rule Healthy_nu, simp_all add: assms)
    thus ?thesis
      by (metis Healthy_def R1_def conj_comm)
  qed
  ultimately show ?thesis
    by (simp)
qed

lemma Guarded_const [closure]: "Guarded (\<lambda> X. P)"
  by (simp add: Guarded_def)

lemma Guarded_if_Productive [closure]:
  fixes P :: "('\<sigma>,'\<phi>) action"
  assumes "P is NSRD" "P is Productive"
  shows "Guarded (\<lambda> X. P ;; CSP(X))"
proof (clarsimp simp add: Guarded_def)
  -- {* We split the proof into three cases corresponding to valuations for ok, wait, and wait'
        respectively. *}
  fix X n
  have a:"(P ;; CSP(X) \<and> gvrt (Suc n))\<lbrakk>false/$ok\<rbrakk> =
        (P ;; CSP(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>false/$ok\<rbrakk>"
    by (simp add: usubst closure SRD_left_zero_1 assms)
  have b:"((P ;; CSP(X) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk> =
          ((P ;; CSP(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk>"
    by (simp add: usubst closure SRD_left_zero_2 assms)
  have c:"((P ;; CSP(X) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>false/$wait\<rbrakk> =
          ((P ;; CSP(X \<and> gvrt n) \<and> gvrt (Suc n))\<lbrakk>true/$ok\<rbrakk>)\<lbrakk>false/$wait\<rbrakk>"
  proof -
    have 1:"(P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP X)\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
          (P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
      by (metis (no_types, lifting) Healthy_def R3h_wait_true SRD_healths(3) SRD_idem)
    have 2:"(P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP X)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
          (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
    proof -
      have exp:"\<And> Y::('\<sigma>,'\<phi>) action. (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
                  ((((\<not>\<^sub>r pre\<^sub>R P) ;; (CSP(Y))\<lbrakk>false/$wait\<rbrakk> \<or> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>true,false/$ok,$wait\<rbrakk>))
                     \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
      proof -
        fix Y :: "('\<sigma>,'\<phi>) action"

        have "(P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
              ((\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (metis (no_types) Healthy_def Productive_form assms(1) assms(2) NSRD_is_SRD)
        also have "... =
             ((R1(R2c(pre\<^sub>R(P) \<Rightarrow> ($ok\<acute> \<and> post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (simp add: RHS_def R1_def R2c_def R2s_def R3h_def RD1_def RD2_def usubst unrest assms closure design_def)
        also have "... =
             (((\<not>\<^sub>r pre\<^sub>R(P) \<or> ($ok\<acute> \<and> post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>)))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (simp add: impl_alt_def R2c_disj R1_disj R2c_not  assms closure R2c_and
              R2c_preR rea_not_def R1_extend_conj' R2c_ok' R2c_post_SRD R1_tr_less_tr' R2c_tr_less_tr')
        also have "... =
             ((((\<not>\<^sub>r pre\<^sub>R P) ;; (CSP(Y))\<lbrakk>false/$wait\<rbrakk> \<or> ($ok\<acute> \<and> post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk>)) \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
          by (simp add: usubst unrest assms closure seqr_or_distl NSRD_neg_pre_left_zero SRD_healths)
        also have "... =
             ((((\<not>\<^sub>r pre\<^sub>R P) ;; (CSP(Y))\<lbrakk>false/$wait\<rbrakk> \<or> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>true,false/$ok,$wait\<rbrakk>)) \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
        proof -
          have "($ok\<acute> \<and> post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> =
                ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) \<and> $ok\<acute> =\<^sub>u true) ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk>"
            by (rel_blast)
          also have "... = (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)\<lbrakk>true/$ok\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk>\<lbrakk>true/$ok\<rbrakk>"
            using seqr_left_one_point[of ok "(post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)" True "(CSP Y)\<lbrakk>false/$wait\<rbrakk>"]
            by (simp add: true_alt_def[THEN sym])
          finally show ?thesis by (simp add: usubst unrest)
        qed
        finally
        show "(P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP Y)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
                 ((((\<not>\<^sub>r pre\<^sub>R P) ;; (CSP(Y))\<lbrakk>false/$wait\<rbrakk> \<or> (post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP Y)\<lbrakk>true,false/$ok,$wait\<rbrakk>))
                 \<and> gvrt (Suc n))\<lbrakk>true,false/$ok,$wait\<rbrakk>" .
      qed

      have 1:"((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP X)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<and> gvrt (Suc n)) =
              ((post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr) ;; (CSP (X \<and> gvrt n))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<and> gvrt (Suc n))"
          apply (rel_auto)
          apply (rename_tac tr st ref ok wait tr' st' ref' tr\<^sub>0 st\<^sub>0 ref\<^sub>0 ok')
          apply (rule_tac x="tr\<^sub>0" in exI, rule_tac x="st\<^sub>0" in exI, rule_tac x="ref\<^sub>0" in exI)
          apply (simp)
          apply (erule Prefix_Order.strict_prefixE')
          apply (rename_tac tr st ref ok wait tr' st' ref' tr\<^sub>0 st\<^sub>0 ref\<^sub>0 ok' z zs)
          apply (simp add: length_minus_list)
          apply (subgoal_tac "length(tr) + length(z # zs) \<le> length(tr')")
          apply auto[1]
          apply (metis diff_add_cancel_left' length_append nat_le_iff_add plus_list_def)
          apply (rename_tac tr st ref ok wait tr' st' ref' tr\<^sub>0 st\<^sub>0 ref\<^sub>0 ok')
          apply (rule_tac x="tr\<^sub>0" in exI, rule_tac x="st\<^sub>0" in exI, rule_tac x="ref\<^sub>0" in exI)
          apply (simp)
          apply (erule Prefix_Order.strict_prefixE')
          apply (rename_tac tr st ref ok wait tr' st' ref' tr\<^sub>0 st\<^sub>0 ref\<^sub>0 ok' z zs)
          apply (simp add: length_minus_list)
          apply (subgoal_tac "length(tr) + length(z # zs) \<le> length(tr')")
          apply auto[1]
          apply (metis Prefix_Order.prefix_length_le length_append)
        done
        have 2:"(\<not>\<^sub>r pre\<^sub>R P) ;; (CSP X)\<lbrakk>false/$wait\<rbrakk> = (\<not>\<^sub>r pre\<^sub>R P) ;; (CSP(X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk>"
          by (simp add: NSRD_neg_pre_left_zero closure assms SRD_healths)
        show ?thesis
          by (simp add: exp 1 2 utp_pred_laws.inf_sup_distrib2)
      qed

      show ?thesis
      proof -
      have "(P ;; (CSP X) \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk> =
          ((P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP X)\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<or>
          (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP X)\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
      by (subst seqr_bool_split[of wait], simp_all add: usubst utp_pred_laws.distrib(4))
      also
      have "... = ((P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>true/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<or>
                 (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk> \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
        by (simp add: 1 2)
      also
      have "... = ((P\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>true/$wait\<rbrakk> \<or>
                    P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (CSP (X \<and> gvrt n))\<lbrakk>false/$wait\<rbrakk>) \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
        by (simp add: usubst utp_pred_laws.distrib(4))
      also have "... = (P ;; (CSP (X \<and> gvrt n)) \<and> gvrt (n+1))\<lbrakk>true,false/$ok,$wait\<rbrakk>"
        by (subst seqr_bool_split[of wait], simp_all add: usubst)
      finally show ?thesis by (simp add: usubst)
    qed

  qed
  show "(P ;; CSP(X) \<and> gvrt (Suc n)) = (P ;; CSP(X \<and> gvrt n) \<and> gvrt (Suc n))"
    apply (rule_tac bool_eq_splitI[of "in_var ok"])
    apply (simp_all add: a)
    apply (rule_tac bool_eq_splitI[of "in_var wait"])
    apply (simp_all add: b c)
  done
qed

lemma PrefixCSP_Guarded [closure]: "Guarded (PrefixCSP a)"
proof -
  have "PrefixCSP a = (\<lambda> X. do\<^sub>C(a) ;; CSP(X))"
    by (simp add: fun_eq_iff PrefixCSP_def)
  thus ?thesis
    using Guarded_if_Productive NCSP_DoCSP NCSP_implies_NSRD Productive_DoCSP by auto
qed

lemma ExtChoice_Guarded [closure]:
  assumes  "\<And> P. P \<in> A \<Longrightarrow> Guarded P"
  shows "Guarded (\<lambda> X. \<box>P\<in>A \<bullet> P(X))"
proof (rule GuardedI)
  fix X n
  have "\<And> Y. ((\<box>P\<in>A \<bullet> P Y) \<and> gvrt(n+1)) = ((\<box>P\<in>A \<bullet> (P Y \<and> gvrt(n+1))) \<and> gvrt(n+1))"
  proof -
    fix Y
    let ?lhs = "((\<box>P\<in>A \<bullet> P Y) \<and> gvrt(n+1))" and ?rhs = "((\<box>P\<in>A \<bullet> (P Y \<and> gvrt(n+1))) \<and> gvrt(n+1))"
    have a:"?lhs\<lbrakk>false/$ok\<rbrakk> = ?rhs\<lbrakk>false/$ok\<rbrakk>"
      by (rel_auto)
    have b:"?lhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>true/$wait\<rbrakk> = ?rhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>true/$wait\<rbrakk>"
      by (rel_auto)
    have c:"?lhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>false/$wait\<rbrakk> = ?rhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>false/$wait\<rbrakk>"
      by (simp add: ExtChoice_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest, rel_blast)
    show "?lhs = ?rhs"
      using a b c
      by (rule_tac bool_eq_splitI[of "in_var ok"], simp, rule_tac bool_eq_splitI[of "in_var wait"], simp_all)
  qed
  moreover have "((\<box>P\<in>A \<bullet> (P X \<and> gvrt(n+1))) \<and> gvrt(n+1)) =  ((\<box>P\<in>A \<bullet> (P (X \<and> gvrt(n)) \<and> gvrt(n+1))) \<and> gvrt(n+1))"
  proof -
    have "(\<box>P\<in>A \<bullet> (P X \<and> gvrt(n+1))) = (\<box>P\<in>A \<bullet> (P (X \<and> gvrt(n)) \<and> gvrt(n+1)))"
    proof (rule ExtChoice_cong)
      fix P assume "P \<in> A"
      thus "(P X \<and> gvrt(n+1)) = (P (X \<and> gvrt(n)) \<and> gvrt(n+1))"
        using Guarded_def assms by blast
    qed
    thus ?thesis by simp
  qed
  ultimately show "((\<box>P\<in>A \<bullet> P X) \<and> gvrt(n+1)) = ((\<box>P\<in>A \<bullet> (P (X \<and> gvrt(n)))) \<and> gvrt(n+1))"
    by simp
qed

lemma extChoice_Guarded [closure]:
  assumes "Guarded P" "Guarded Q"
  shows "Guarded (\<lambda> X. P(X) \<box> Q(X))"
proof -
  have "Guarded (\<lambda> X. \<box>F\<in>{P,Q} \<bullet> F(X))"
    by (rule ExtChoice_Guarded, auto simp add: assms)
  thus ?thesis
    by (simp add: extChoice_def)
qed

lemma Continuous_mu_CSP_form_1 [closure]: "Continuous (\<lambda>X. P ;; CSP X)"
  using SRD_Continuous
  by (clarsimp simp add: Continuous_def seq_SUP_distl[THEN sym], rename_tac A, drule_tac x="A" in spec, simp)

lemma mu_CSP_form_1_type [closure]:
  assumes "P is CSP"
  shows "(\<lambda>X. P ;; CSP X) \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  by (blast intro: funcsetI closure assms)

text {* Example fixed-point calculation *}

lemma mu_csp_form_1 [rdes]:
  assumes "P is NSRD" "P is Productive"
  shows "(\<mu> X \<bullet> P ;; CSP(X)) = (\<Sqinter>i \<bullet> P \<^bold>^ (i+1)) ;; Miracle"
proof -
  have 1:"Continuous (\<lambda>X. P ;; CSP X)"
    using SRD_Continuous
    by (clarsimp simp add: Continuous_def seq_SUP_distl[THEN sym], drule_tac x="A" in spec, simp)
  have 2: "(\<lambda>X. P ;; CSP X) \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
    by (blast intro: funcsetI closure assms)
  with 1 2 have "(\<mu> X \<bullet> P ;; CSP(X)) = (\<nu> X \<bullet> P ;; CSP(X))"
    by (simp add: guarded_fp_uniq Guarded_if_Productive[OF assms] Continuous_Monotonic funcsetI closure)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P ;; CSP X) ^^ i) false)"
    by (simp add: sup_continuous_lfp 1 sup_continuous_Continuous false_upred_def)
  also have "... = ((\<lambda>X. P ;; CSP X) ^^ 0) false \<sqinter> (\<Sqinter>i. ((\<lambda>X. P ;; CSP X) ^^ (i+1)) false)"
    by (subst Sup_power_expand, simp)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P ;; CSP X) ^^ (i+1)) false)"
    by (simp)
  also have "... = (\<Sqinter>i. P \<^bold>^ (i+1) ;; Miracle)"
  proof (rule SUP_cong,simp_all)
    fix i
    show "P ;; CSP (((\<lambda>X. P ;; CSP X) ^^ i) false) = (P ;; P \<^bold>^ i) ;; Miracle"
    proof (induct i)
      case 0
      then show ?case
        by (simp, metis srdes_hcond_def srdes_theory_continuous.healthy_top)
    next
      case (Suc i)
      then show ?case
        by (simp add: Healthy_if NSRD_is_SRD SRD_power_Suc SRD_seqr_closure assms(1) seqr_assoc srdes_theory_continuous.weak.top_closed)
    qed
  qed
  also have "... = (\<Sqinter>i. P \<^bold>^ (i+1)) ;; Miracle"
    by (simp add: seq_Sup_distr)
  finally show ?thesis
    by (simp add: UINF_as_Sup[THEN sym])
qed

lemma mu_csp_form_NSRD [closure]:
  assumes "P is NCSP" "P is Productive"
  shows "(\<mu> X \<bullet> P ;; CSP(X)) is NSRD"
  by (simp add: mu_csp_form_1 assms closure)

lemma mu_csp_form_1':
  assumes "P is NCSP" "P is Productive"
  shows "(\<mu> X \<bullet> P ;; CSP(X)) = (P ;; P\<^sup>\<star>) ;; Miracle"
proof -
  have "(\<mu> X \<bullet> P ;; CSP(X)) = (\<Sqinter> i\<in>UNIV \<bullet> P ;; P \<^bold>^ i) ;; Miracle"
    by (simp add: mu_csp_form_1 assms closure ustar_def)
  also have "... = (P ;; P\<^sup>\<star>) ;; Miracle"
    by (simp only: seq_UINF_distl[THEN sym], simp add: ustar_def)
  finally show ?thesis .
qed

lemma mu_example1: "(\<mu> X \<bullet> a \<^bold>\<rightarrow> X) = (\<Sqinter>i \<bullet> do\<^sub>C(\<guillemotleft>a\<guillemotright>) \<^bold>^ (i+1)) ;; Miracle"
  by (simp add: PrefixCSP_def mu_csp_form_1 closure)
    
lemma preR_mu_example1 [rdes]: "pre\<^sub>R(\<mu> X \<bullet> a \<^bold>\<rightarrow> X) = true\<^sub>r"
  by (simp add: mu_example1 rdes closure unrest wp)

lemma periR_mu_example1 [rdes]:
  "peri\<^sub>R(\<mu> X \<bullet> a \<^bold>\<rightarrow> X) =
   (\<Sqinter>x\<in>{0..} \<bullet> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<and> $st\<acute> =\<^sub>u $st) \<^bold>^ x ;; ($tr\<acute> =\<^sub>u $tr \<and> \<guillemotleft>a\<guillemotright> \<notin>\<^sub>u $ref\<acute>))"
  by (simp add: mu_example1 rdes closure unrest wp seq_UINF_distr alpha)

lemma postR_mu_example1 [rdes]:
  "post\<^sub>R(\<mu> X \<bullet> a \<^bold>\<rightarrow> X) = false"
  by (simp add: mu_example1 rdes closure unrest wp)

lemma SRD_refine_intro':
  assumes
    "P is SRD" "Q is SRD"
    "`pre\<^sub>R(P) \<Rightarrow> pre\<^sub>R(Q)`" "peri\<^sub>R(P) \<sqsubseteq> (pre\<^sub>R(P) \<and> peri\<^sub>R(Q))" "post\<^sub>R(P) \<sqsubseteq> (pre\<^sub>R(P) \<and> post\<^sub>R(Q))"
  shows "P \<sqsubseteq> Q"
  using assms by (rule_tac SRD_refine_intro, simp_all add: refBy_order)
    
lemma UINF_ind_R1_closed [closure]:
  "\<lbrakk> \<And> i. P(i) is R1 \<rbrakk> \<Longrightarrow> (\<Sqinter> i \<bullet> P(i)) is R1"
  by (rel_blast)
    
lemma mu_csp_basic_refine:
  assumes 
    "P is CSP" "Q is NCSP" "Q is Productive" "pre\<^sub>R(P) = true\<^sub>r" "pre\<^sub>R(Q) = true\<^sub>r"
    "peri\<^sub>R P \<sqsubseteq> peri\<^sub>R Q"
    "peri\<^sub>R P \<sqsubseteq> post\<^sub>R Q ;; peri\<^sub>R P"
  shows "P \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> Q ;; X)"
proof (rule SRD_refine_intro', simp_all add: closure usubst alpha rpred rdes unrest wp seq_UINF_distr assms)
  show "peri\<^sub>R P \<sqsubseteq> (\<Sqinter> i \<bullet> post\<^sub>R Q \<^bold>^ i ;; peri\<^sub>R Q)"
  proof (rule UINF_refines')
    fix i
    show "peri\<^sub>R P \<sqsubseteq> post\<^sub>R Q \<^bold>^ i ;; peri\<^sub>R Q"
    proof (induct i)
      case 0
      then show ?case by (simp add: assms)
    next
      case (Suc i)
      then show ?case
        by (meson assms(6) assms(7) semilattice_sup_class.le_sup_iff upower_inductl)
    qed
  qed
qed
  
lemma CRD_mu_basic_refine:
  fixes P :: "'e list \<Rightarrow> 'e set \<Rightarrow> 's upred"
  assumes
    "Q is NCSP" "Q is Productive" "pre\<^sub>R(Q) = true\<^sub>r"
    "\<lceil>P t r\<rceil>\<^sub>S\<^sub><\<lbrakk>(t, r)\<rightarrow>(tt, $ref\<acute>)\<^sub>u\<rbrakk> \<sqsubseteq> peri\<^sub>R Q"
    "\<lceil>P t r\<rceil>\<^sub>S\<^sub><\<lbrakk>(t, r)\<rightarrow>(tt, $ref\<acute>)\<^sub>u\<rbrakk> \<sqsubseteq> (post\<^sub>R Q ;;\<^sub>h R1(\<lceil>P t r\<rceil>\<^sub>S\<^sub><\<lbrakk>(t, r)\<rightarrow>(tt, $ref\<acute>)\<^sub>u\<rbrakk>))"
  shows "[true \<turnstile> P trace refs | R]\<^sub>C \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> Q ;; X)"
proof (rule mu_csp_basic_refine, simp_all add: assms closure alpha rdes R1_false)
  show "R1 (\<lceil>P trace refs\<rceil>\<^sub>S\<^sub><\<lbrakk>(trace, refs)\<rightarrow>(tt, $ref\<acute>)\<^sub>u\<rbrakk>) \<sqsubseteq> peri\<^sub>R Q"
    using NCSP_implies_CSP R1_mono R1_peri_SRD assms(1) assms(4) by fastforce
  show "R1 (\<lceil>P trace refs\<rceil>\<^sub>S\<^sub><\<lbrakk>(trace, refs)\<rightarrow>(tt, $ref\<acute>)\<^sub>u\<rbrakk>) \<sqsubseteq> post\<^sub>R Q ;; R1 (\<lceil>P trace refs\<rceil>\<^sub>S\<^sub><\<lbrakk>(trace, refs)\<rightarrow>(tt, $ref\<acute>)\<^sub>u\<rbrakk>)"
    (is "?lhs \<sqsubseteq> ?rhs")
  proof -
    have 1:"?lhs \<sqsubseteq> R1(post\<^sub>R Q ;;\<^sub>h R1(\<lceil>P t r\<rceil>\<^sub>S\<^sub><\<lbrakk>(t, r)\<rightarrow>(tt, $ref\<acute>)\<^sub>u\<rbrakk>))"
      by (rule R1_mono, rule assms(5))
    have 2:"R1(post\<^sub>R Q ;;\<^sub>h R1(\<lceil>P t r\<rceil>\<^sub>S\<^sub><\<lbrakk>(t, r)\<rightarrow>(tt, $ref\<acute>)\<^sub>u\<rbrakk>)) = 
            R1(R1(post\<^sub>R Q) ;;\<^sub>h R1(\<lceil>P t r\<rceil>\<^sub>S\<^sub><\<lbrakk>(t, r)\<rightarrow>(tt, $ref\<acute>)\<^sub>u\<rbrakk>))"
      by (simp add: R1_post_SRD assms closure)
    have 3: "... = post\<^sub>R Q ;; R1 (\<lceil>P t r\<rceil>\<^sub>S\<^sub><\<lbrakk>(t, r)\<rightarrow>(tt, $ref\<acute>)\<^sub>u\<rbrakk>)"
      by (simp add: R1_seqr, simp add: R1_post_SRD assms closure)
    show ?thesis
      using "1" "2" "3" by auto
  qed
qed
    
subsection {* Merge predicate *}

definition CSPMerge' :: "('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> '\<psi> set \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> (('\<sigma>,'\<psi>) st_csp) merge" ("N\<^sub>C") where
  [upred_defs]:
  "CSPMerge' ns1 cs ns2 = (
    $ref\<acute> \<subseteq>\<^sub>u (($0-ref \<union>\<^sub>u $1-ref) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u (($0-ref \<inter>\<^sub>u $1-ref) - \<guillemotleft>cs\<guillemotright>) \<and>
    $tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<and>
    ($tr\<acute> - $tr\<^sub><) \<in>\<^sub>u ($0-tr - $tr\<^sub><) \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> ($1-tr - $tr\<^sub><) \<and>
    ($0-tr - $tr\<^sub><) \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u ($1-tr - $tr\<^sub><) \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> \<and>
    $st\<acute> =\<^sub>u ($st\<^sub>< \<oplus> $0-st on &ns1) \<oplus> $1-st on &ns2)"
  
lemma CSPMerge'_R2m [closure]: "N\<^sub>C ns1 cs ns2 is R2m"
  by (rel_auto)

lemma CSPMerge'_RDM [closure]: "N\<^sub>C ns1 cs ns2 is RDM"
  by (rule RDM_intro, simp add: closure, simp_all add: CSPMerge'_def unrest)

definition CSPMerge :: "('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> '\<psi> set \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> (('\<sigma>,'\<psi>) st_csp) merge" ("M\<^sub>C") where
[upred_defs]: "M\<^sub>C ns1 cs ns2 = M\<^sub>R(N\<^sub>C ns1 cs ns2) ;; Skip"

lemma CSPMerge'_calc:
  assumes "$ok\<acute> \<sharp> P" "$wait\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$wait\<acute> \<sharp> Q" "P is R2" "Q is R2"
  shows "P \<parallel>\<^bsub>N\<^sub>B\<^esub> Q = ((\<exists> $st\<acute> \<bullet> P) \<and> (\<exists> $st\<acute> \<bullet> Q) \<and> $st\<acute> =\<^sub>u $st)"
  using assms
proof -
  have P:"(\<exists> {$ok\<acute>,$wait\<acute>} \<bullet> R2(P)) = P" (is "?P' = _")
    by (simp add: ex_unrest ex_plus Healthy_if assms)
  have Q:"(\<exists> {$ok\<acute>,$wait\<acute>} \<bullet> R2(Q)) = Q" (is "?Q' = _")
    by (simp add: ex_unrest ex_plus Healthy_if assms)
  have "?P' \<parallel>\<^bsub>N\<^sub>B\<^esub> ?Q' = ((\<exists> $st\<acute> \<bullet> ?P') \<and> (\<exists> $st\<acute> \<bullet> ?Q') \<and> $st\<acute> =\<^sub>u $st)"
    by (simp add: par_by_merge_alt_def, rel_auto, blast+)
  thus ?thesis
    by (simp add: P Q)
qed 

text {* Important theorem that shows the form of a parallel process *}
  
lemma CSPMerge'_form:
  fixes P Q :: "('\<sigma>,'\<phi>) action"
  assumes "vwb_lens ns1" "vwb_lens ns2" "$wait\<acute> \<sharp> P" "$wait\<acute> \<sharp> Q" "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "P is R2" "Q is R2" 
  shows
  "P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $ref\<acute> \<subseteq>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
proof -
  have P:"(\<exists> {$ok\<acute>,$wait\<acute>} \<bullet> R2(P)) = P" (is "?P' = _")
    by (simp add: ex_unrest ex_plus Healthy_if assms)
  have Q:"(\<exists> {$ok\<acute>,$wait\<acute>} \<bullet> R2(Q)) = Q" (is "?Q' = _")
    by (simp add: ex_unrest ex_plus Healthy_if assms)
  from assms(1,2)
  have "?P' \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> ?Q' = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             ?P'\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk> \<and> ?Q'\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>1\<guillemotright>/$ref\<acute>,$st\<acute>,$tr,$tr\<acute>\<rbrakk>
           \<and> $ref\<acute> \<subseteq>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr \<le>\<^sub>u $tr\<acute>
           \<and> tt \<in>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>
           \<and> $st\<acute> =\<^sub>u ($st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1) \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    apply (simp add: par_by_merge_alt_def, rel_auto, blast)
    apply (rename_tac ok wait tr st ref tr' ref' ref\<^sub>0 ref\<^sub>1 st\<^sub>0 st\<^sub>1 tr\<^sub>0 ok\<^sub>0 tr\<^sub>1 wait\<^sub>0 ok\<^sub>1 wait\<^sub>1)
    apply (rule_tac x="ok" in exI)
    apply (rule_tac x="wait" in exI)
    apply (rule_tac x="tr" in exI)      
    apply (rule_tac x="st" in exI)
    apply (rule_tac x="ref" in exI)
    apply (rule_tac x="tr @ tr\<^sub>0" in exI)      
    apply (rule_tac x="st\<^sub>0" in exI)
    apply (rule_tac x="ref\<^sub>0" in exI)      
    apply (auto)
    apply (metis Prefix_Order.prefixI append_minus)
  done
  thus ?thesis
    by (simp add: P Q)
qed
    
subsection {* Parallel Operator *}

abbreviation ParCSP ::
  "('\<sigma>, '\<theta>) action \<Rightarrow> ('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> '\<theta> event set \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> ('\<sigma>, '\<theta>) action \<Rightarrow> ('\<sigma>, '\<theta>) action" (infixr "[|_\<parallel>_\<parallel>_|]" 75) where
"P [|ns1\<parallel>cs\<parallel>ns2|] Q \<equiv> P \<parallel>\<^bsub>M\<^sub>C ns1 cs ns2\<^esub> Q"

abbreviation ParCSP_NS ::
  "('\<sigma>, '\<theta>) action \<Rightarrow> '\<theta> event set \<Rightarrow> ('\<sigma>, '\<theta>) action \<Rightarrow> ('\<sigma>, '\<theta>) action" (infixr "[|_|]" 75) where
"P [|cs|] Q \<equiv> P [|0\<^sub>L\<parallel>cs\<parallel>0\<^sub>L|] Q"

abbreviation InterleaveCSP ::
  "('\<sigma>, '\<theta>) action \<Rightarrow> ('\<sigma>, '\<theta>) action \<Rightarrow> ('\<sigma>, '\<theta>) action" (infixr "|||" 75) where
"P ||| Q \<equiv> P [|0\<^sub>L\<parallel>{}\<parallel>0\<^sub>L|] Q"

definition CSP5 :: "('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "CSP5(P) = (P ||| Skip)"

definition C2 :: "('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "C2(P) = (P [|1\<^sub>L\<parallel>{}\<parallel>0\<^sub>L|] Skip)"

subsubsection {* CSP Parallel Laws *}

lemma swap_CSPMerge':
  "ns1 \<bowtie> ns2 \<Longrightarrow> swap\<^sub>m ;; (N\<^sub>C ns1 cs ns2) = (N\<^sub>C ns2 cs ns1)"
  apply (rel_auto)
  using tr_par_sym apply blast
  apply (simp add: lens_indep_comm)
  using tr_par_sym apply blast
  apply (simp add: lens_indep_comm)
done

lemma SymMerge_CSP_NS [closure]: "N\<^sub>C 0\<^sub>L cs 0\<^sub>L is SymMerge"
  by (simp add: Healthy_def swap_CSPMerge')

lemma ParCSP_expand:
  "P [|ns1\<parallel>cs\<parallel>ns2|] Q = (P \<parallel>\<^sub>R\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q) ;; Skip"
  by (simp add: CSPMerge_def par_by_merge_seq_add)
    
lemma parallel_is_CSP [closure]:
  assumes "P is CSP" "Q is CSP"
  shows "(P [|ns1\<parallel>cs\<parallel>ns2|] Q) is CSP"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> Q) is CSP"
    by (simp add: closure assms)
  hence "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> Q) ;; Skip is CSP"
    by (simp add: closure)
  thus ?thesis
    by (simp add: CSPMerge_def par_by_merge_seq_add)
qed
  
lemma preR_parallel:
  assumes "P is NCSP" "Q is NCSP"
  shows "pre\<^sub>R(P [|ns1\<parallel>cs\<parallel>ns2|] Q) =  undefined"
  apply (simp add: ParCSP_expand rdes  closure assms unrest wp)
  oops
    
lemma parallel_is_CSP3 [closure]:
  assumes "P is CSP" "P is CSP3" "Q is CSP" "Q is CSP3"
  shows "(P [|ns1\<parallel>cs\<parallel>ns2|] Q) is CSP3"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> Q) is CSP"
    by (simp add: closure assms)
  hence "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> Q) ;; Skip is CSP"
    by (simp add: closure)
  thus ?thesis
    oops

theorem parallel_commutative:
  assumes "ns1 \<bowtie> ns2"
  shows "(P [|ns1\<parallel>cs\<parallel>ns2|] Q) = (Q [|ns2\<parallel>cs\<parallel>ns1|] P)"
proof -
  have "(P [|ns1\<parallel>cs\<parallel>ns2|] Q) = P \<parallel>\<^bsub>swap\<^sub>m ;; (M\<^sub>C ns2 cs ns1)\<^esub> Q"
    by (simp add: CSPMerge_def seqr_assoc swap_merge_rd swap_CSPMerge' lens_indep_sym assms)
  also have "... = Q [|ns2\<parallel>cs\<parallel>ns1|] P"
    by (metis par_by_merge_commute_swap)
  finally show ?thesis .
qed

lemma interleave_commute:
  "P ||| Q = Q ||| P"
  using parallel_commutative zero_lens_indep by blast

(*
lemma 
  assumes "a \<in> cs" "P is NCSP" "Q is NCSP"
  shows "(a \<^bold>\<rightarrow> P [|ns1\<parallel>cs\<parallel>ns2|] a \<^bold>\<rightarrow> Q) = a \<^bold>\<rightarrow> (P [|ns1\<parallel>cs\<parallel>ns2|] Q)" (is "?lhs = ?rhs")
proof -
  have "pre\<^sub>R(?lhs) = pre\<^sub>R(?rhs)"
    apply (subst rdes)
      apply (simp_all add: rdes closure assms unrest)
    apply (rule unrest) back back
    apply (simp_all add: closure assms unrest)
*)

lemma preR_CSP5:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "P is NCSP"
  shows "pre\<^sub>R(CSP5(P)) = pre\<^sub>R(P)"
proof -
  have "pre\<^sub>R(P ||| Skip) =
        (\<not>\<^sub>r (\<lceil>\<not>\<^sub>rpre\<^sub>R P\<rceil>\<^sub>0 \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;;
        ($ref\<acute> \<subseteq>\<^sub>u $0-ref \<inter>\<^sub>u $1-ref \<and> $tr\<acute> \<ge>\<^sub>u $tr\<^sub>< \<and> $tr\<acute> - $tr\<^sub>< \<in>\<^sub>u ($0-tr - $tr\<^sub><) \<star>\<^bsub>{}\<^sub>u\<^esub> \<langle>\<rangle> :: (('\<sigma>, '\<phi>) st_csp) merge) ;; R1 true)"
    by (simp add: ParCSP_expand rdes closure unrest wp assms, simp add: wrR_def par_by_merge_alt_def CSPMerge'_def alpha)
       (rel_auto, simp_all add: zero_list_def)
  also have "... =
        (\<not>\<^sub>r (\<lceil>\<not>\<^sub>r pre\<^sub>R P\<rceil>\<^sub>0 \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; ($tr\<acute> \<ge>\<^sub>u $tr\<^sub>< \<and> $tr\<acute> - $tr\<^sub>< =\<^sub>u ($0-tr - $tr\<^sub><) :: (('\<sigma>, '\<phi>) st_csp) merge) ;; R1 true)"
    by (simp add: trace_merge_nil, rel_blast)
  also have "... = (\<not>\<^sub>r ((\<not>\<^sub>r pre\<^sub>R P) ;; R1 true))"
    by (rel_auto, metis diff_add_cancel_left')
  also have "... = pre\<^sub>R(P)"
    by (simp add: closure alpha rpred NSRD_neg_pre_unit assms)
  finally show ?thesis by (simp add: CSP5_def)
qed
  
lemma CSP5_Skip [closure]: "Skip is CSP5"
  unfolding CSP5_def Healthy_def
  by (rule SRD_eq_intro)
     (simp_all add: ParCSP_expand rdes closure wp rpred, rel_auto+, simp_all add: minus_zero_eq zero_list_def)

lemma wppR_rea_true [wp]: "P wr\<^sub>R(M) true\<^sub>r = true\<^sub>r"
  by (simp add: wrR_def)
    
lemma CSP5_Stop [closure]: "Stop is CSP5"
  unfolding CSP5_def Healthy_def
  by (rule SRD_eq_intro)
     (simp_all add: ParCSP_expand rdes closure wp rpred, rel_auto, simp_all add: minus_zero_eq zero_list_def)
     
subsection {* Failures-Divergences Semantics *}

definition divergences :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> '\<phi> list set" ("dv\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "divergences P s = {t | t. `(\<not>\<^sub>r pre\<^sub>R(P))\<lbrakk>(\<guillemotleft>s\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>)\<^sub>u/{$st,$tr,$tr\<acute>}\<rbrakk>`}"
  
definition traces :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> ('\<phi> list \<times> '\<sigma>) set" ("tr\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "traces P s = {(t,s') | t s'. `(pre\<^sub>R(P) \<and> post\<^sub>R(P))\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>/$st,$st\<acute>,$tr,$tr\<acute>\<rbrakk>`}"

definition failures :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> ('\<phi> list \<times> '\<phi> set) set" ("fl\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "failures P s = {(t,r) | t r. `(pre\<^sub>R(P) \<and> peri\<^sub>R(P))\<lbrakk>\<guillemotleft>r\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>/$ref\<acute>,$st,$tr,$tr\<acute>\<rbrakk>`}"

(*
lemma bij_lens_in_out:
  "bij_lens (in\<alpha> +\<^sub>L out\<alpha>)"
  by (simp add: bij_lens_equiv_id lens_equiv_sym alpha_in_out)
  
lemma bij_lens_comp: "\<lbrakk> bij_lens X; bij_lens Y \<rbrakk> \<Longrightarrow> bij_lens (X ;\<^sub>L Y)"
  by (unfold_locales, simp_all add: lens_comp_def)
  
    
lemma   
  assumes "bij_lens X"
  shows "bij_lens ((X ;\<^sub>L fst\<^sub>L) +\<^sub>L (X ;\<^sub>L snd\<^sub>L))"
proof -
  have "X \<approx>\<^sub>L 1\<^sub>L"
    

lemma 
  assumes "P is NCSP" "Q is NCSP" "\<And> s. divergences P s \<subseteq> divergences Q s"
  shows "pre\<^sub>R(Q) \<sqsubseteq> pre\<^sub>R(P)"
proof (rule refine_by_obs[of "{$st,$tr,$tr\<acute>}\<^sub>\<alpha>" "{$ok,$ok\<acute>,$wait,$wait\<acute>,$st\<acute>,$ref,$ref\<acute>}\<^sub>\<alpha>"],
       simp_all add: unrest assms closure)
  oops
*)  
   
lemma traces_Skip:
  "tr\<lbrakk>Skip\<rbrakk>s = {([], s)}"
  by (simp add: traces_def rdes alpha closure, rel_simp)

lemma failures_Skip:
  "fl\<lbrakk>Skip\<rbrakk>s = {}"
  by (simp add: failures_def, rdes_calc)

lemma divergences_Skip:
  "dv\<lbrakk>Skip\<rbrakk>s = {}"
  by (simp add: divergences_def, rdes_calc)

lemma traces_AssignsCSP:
  "tr\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>C\<rbrakk>s = {([], \<sigma>(s))}"
  by (simp add: traces_def rdes closure usubst alpha, rel_simp)

lemma failures_AssignsCSP:
  "fl\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>C\<rbrakk>s = {}"
  by (simp add: failures_def, rdes_calc)

lemma divergences_AssignsCSP:
  "dv\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>C\<rbrakk>s = {}"
  by (simp add: divergences_def, rdes_calc)

lemma "fl\<lbrakk>Miracle\<rbrakk>s = {}"
  by (simp add: failures_def rdes closure usubst)

lemma "dv\<lbrakk>Miracle\<rbrakk>s = {}"
  by (simp add: divergences_def rdes closure usubst)

lemma "dv\<lbrakk>Chaos\<rbrakk>s = UNIV"
  by (simp add: divergences_def rdes, rel_auto)

lemma "tr\<lbrakk>Chaos\<rbrakk>s = {}"
  by (simp add: traces_def rdes closure usubst)

subsection {* Deadlock Freedom *}
  
definition DF :: "'e set \<Rightarrow> ('s, 'e) action" where
"DF(A) = (\<mu>\<^sub>C X \<bullet> (\<Sqinter> a\<in>A \<bullet> a \<^bold>\<rightarrow> Skip) ;; X)"
 
lemma DF_CSP [closure]: "A \<noteq> {} \<Longrightarrow> DF(A) is CSP"
  by (simp add: DF_def closure unrest)
  
lemma preR_DF [rdes]:
  "A \<noteq> {} \<Longrightarrow> pre\<^sub>R(DF(A)) = true\<^sub>r"
  by (simp add: DF_def rdes closure unrest wp usubst)
      
lemma periR_DF_lemma:
  fixes P :: "('s, 'e) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "(\<Sqinter> a \<in> A \<bullet> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<and> $st\<acute> =\<^sub>u $st) \<^bold>^ i ;; P = 
         ($tr \<le>\<^sub>u $tr\<acute> \<and> elems\<^sub>u(tt) \<subseteq>\<^sub>u \<guillemotleft>A\<guillemotright> \<and> #\<^sub>u(tt) =\<^sub>u \<guillemotleft>i\<guillemotright> \<and> $st\<acute> =\<^sub>u $st) ;; P"
proof (induct i)
  case 0
  with assms show ?case
    apply (simp, rel_auto)
    apply (metis (no_types, hide_lams) list.set(1) minus_cancel order_bot_class.bot.extremum order_refl)
    apply (metis (no_types, lifting) less_eq_list_def strict_prefix_diff_minus)
  done
next
  case (Suc i)
  show ?case 
    apply (simp add: seqr_assoc[THEN sym] seq_UINF_distr tr_extend_seqr unrest usubst Suc)
    apply (rel_auto)
    apply (rename_tac tr st ok wait tr' st' ref x ok' wait' tr'' ref')
    apply (rule_tac x="ok'" in exI)
    apply (rule_tac x="wait'" in exI)
     apply (rule_tac x="tr''" in exI)
    apply (auto)
    apply (auto simp add: less_eq_list_def prefix_def)[1]
      apply (metis append_Cons append_Nil append_minus list_concat_minus_list_concat subsetCE)
    apply (auto simp add: less_eq_list_def prefix_def)[1]
    apply (metis append_Cons append_Nil append_minus list_concat_minus_list_concat)      
    apply (rename_tac tr st ok wait tr' st' ref ok' wait' tr'' ref')
    apply (rule_tac x="hd(tr'' - tr)" in exI)
    apply (auto)
    apply (rule_tac x="ok'" in exI)
     apply (rule_tac x="wait'" in exI)
     apply (rule_tac x="tr''" in exI)      
    apply (auto)
    apply (metis Prefix_Order.Cons_prefix_Cons Prefix_Order.Nil_prefix Prefix_Order.same_prefix_prefix hd_Cons_tl length_greater_0_conv less_eq_list_def prefix_concat_minus zero_less_Suc)
    apply (auto simp add: less_eq_list_def prefix_def)[1]
    apply (metis Suc_length_conv append_Cons append_Nil append_minus hd_Cons_tl list.distinct(1) list_concat_minus_list_concat set_subset_Cons subsetCE)
    apply (auto simp add: less_eq_list_def prefix_def)[1]
    apply (metis Suc_length_conv append_Nil append_one_prefix cancel_comm_monoid_add_class.diff_zero diff_Suc_Suc length_drop list.sel(1) list.size(3) list_concat_minus_list_concat minus_list_def nth_Cons_0 prefix_code(1) zero_less_Suc)
    apply (metis contra_subsetD hd_in_set length_greater_0_conv zero_less_Suc)
  done
qed

lemma periR_DF [rdes]:
  "A \<noteq> {} \<Longrightarrow> peri\<^sub>R(DF(A)) = ($tr \<le>\<^sub>u $tr\<acute> \<and> elems\<^sub>u(tt) \<subseteq>\<^sub>u \<guillemotleft>A\<guillemotright> \<and> (\<^bold>\<exists> a \<in> \<guillemotleft>A\<guillemotright> \<bullet> \<guillemotleft>a\<guillemotright> \<notin>\<^sub>u $ref\<acute>))"
  apply (simp add: DF_def rdes closure unrest wp usubst alpha)  
  apply (simp add: seq_UINF_distr periR_DF_lemma unrest)
  apply (rel_auto)
done
    
lemma postR_DF [rdes]:
  "A \<noteq> {} \<Longrightarrow> post\<^sub>R(DF(A)) = false"
  by (simp add: DF_def rdes closure unrest wp usubst alpha)
    
text {* Example deadlock freedom proof *}
  
lemma "DF(UNIV) \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> (a \<^bold>\<rightarrow> Skip) ;; X)"
  apply (rule_tac mu_csp_basic_refine)
  apply (simp_all add: closure rdes wp usubst alpha)
  apply (rel_auto)
  apply (rel_blast)
done
    
subsection {* CSP Action Type and Lifted Definitions *}
   
typedef ('e, 's) Action = "{P :: ('e, 's) action. P is NCSP}"
  by (rule_tac x="Skip" in exI, simp add: closure)
  
setup_lifting type_definition_Action
  
lift_definition skip :: "('e, 's) Action" is Skip
  by (simp add: closure)
    
lift_definition stop :: "('e, 's) Action" is Stop
  by (simp add: closure)

lift_definition seqCircus :: "('e, 's) Action \<Rightarrow> ('e, 's) Action \<Rightarrow> ('e, 's) Action" (infixr ";\<^sub>C" 71)
  is "op ;;"
  by (simp add: closure)
   
lemma stop_left_zero: "stop ;\<^sub>C P = stop"
  by (transfer, simp add: NCSP_implies_CSP Stop_left_zero)
    
instantiation Action :: (type, type) order
begin
  lift_definition less_eq_Action :: "('a, 'b) Action \<Rightarrow> ('a, 'b) Action \<Rightarrow> bool" is "op \<le>" .
  lift_definition less_Action :: "('a, 'b) Action \<Rightarrow> ('a, 'b) Action \<Rightarrow> bool" is "op <" .
instance by (intro_classes) (transfer, simp add: less_uexpr_def)+
end
  
instance Action :: (type, type) refine ..

instantiation Action :: (type, type) complete_lattice
begin
  lift_definition sup_Action :: "('a, 'b) Action \<Rightarrow> ('a, 'b) Action \<Rightarrow> ('a, 'b) Action" is Lattices.sup
    by (simp add: closure)
  lift_definition inf_Action :: "('a, 'b) Action \<Rightarrow> ('a, 'b) Action \<Rightarrow> ('a, 'b) Action" 
    is "\<lambda> P Q. P \<^bold>\<squnion>\<^bsub>TCSP\<^esub> Q" by simp
  lift_definition bot_Action :: "('a, 'b) Action" is Miracle
    by (simp add: closure)
  lift_definition top_Action :: "('a, 'b) Action" is Chaos
    by (simp add: closure)
  lift_definition Sup_Action :: "('a, 'b) Action set \<Rightarrow> ('a, 'b) Action" 
    is "\<lambda> A. \<^bold>\<Sqinter>\<^bsub>TCSP\<^esub> A"
    by (rule csp_theory.weak.inf_closed, auto)
  lift_definition Inf_Action :: "('a, 'b) Action set \<Rightarrow> ('a, 'b) Action"
    is "\<lambda> A. \<^bold>\<Squnion>\<^bsub>TCSP\<^esub> A" 
    by (rule csp_theory.weak.sup_closed, auto)
instance 
  apply (intro_classes)
             apply (transfer, simp add: csp_theory.join_left)
            apply (transfer, simp add: csp_theory.join_right)
           apply (transfer, simp add: csp_theory.join_le)
          apply (transfer, simp add: csp_theory.meet_left)
         apply (transfer, simp add: csp_theory.meet_right)
        apply (transfer, simp add: csp_theory.meet_le)
       apply (transfer, metis csp_theory.sup_upper mem_Collect_eq subsetI tcsp_hcond_def utp_order_carrier)
      apply (transfer, force intro: csp_theory.sup_least)
     apply (transfer, simp add: Ball_Collect csp_theory.inf_lower)
    apply (transfer, force intro: csp_theory.inf_greatest)
   apply (transfer, metis (full_types) csp_bottom_Chaos csp_theory.eq_is_equal csp_theory.weak_sup_empty)
  apply (transfer, metis (full_types) csp_top_Miracle csp_theory.eq_is_equal csp_theory.weak_inf_empty)
done
    
end
  
end