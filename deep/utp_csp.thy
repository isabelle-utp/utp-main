(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_csp.thy                                                          *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 31 Jan 2017 *)

section {* Theory of CSP *}

theory utp_csp
  imports utp_procedure utp_event
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

type_synonym ('\<sigma>,'\<phi>) circus = "('\<sigma>, '\<phi> list, ('\<phi>, unit) csp_vars_scheme) rsp"
type_synonym ('\<sigma>,'\<phi>) rel_circus  = "('\<sigma>,'\<phi>) circus hrel"

translations
  (type) "('\<sigma>,'\<phi>) circus" <= (type) "('\<sigma>, ('\<phi> list, ('a, 'd) csp_vars_scheme) rsp_vars_ext) rp"
 
  
type_synonym '\<phi> csp = "(unit,'\<phi>) circus"
type_synonym '\<phi> rel_csp  = "'\<phi> csp hrel"

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

subsection {* Healthiness Conditions *}

text {* We here define extra healthiness conditions for CSP processes. *}

abbreviation CSP1 :: "(('\<sigma>, '\<phi>) circus \<times> ('\<sigma>, '\<phi>) circus) health"
where "CSP1(P) \<equiv> RD1(P)"

abbreviation CSP2 :: "(('\<sigma>, '\<phi>) circus \<times> ('\<sigma>, '\<phi>) circus) health"
where "CSP2(P) \<equiv> RD2(P)"
  
abbreviation CSP :: "(('\<sigma>, '\<phi>) circus \<times> ('\<sigma>, '\<phi>) circus) health"
where "CSP(P) \<equiv> SRD(P)"

text {*
  Simon, the definition below did not explicitly include type information. I
  think it is good practice to specify types in all definitions, I thus added
  the type @{typ "'\<phi> csp"}. Is that correct? I suppose pure CSP processes do
  not consider program state?!
*}

definition STOP :: "'\<phi> rel_csp" where
[upred_defs]: "STOP = CSP1($ok\<acute> \<and> R3c($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition SKIP :: "'\<phi> rel_csp" where
[upred_defs]: "SKIP = \<^bold>R\<^sub>s(\<exists> $ref \<bullet> CSP1(II))"

definition [upred_defs]: "CSP3(P) = (SKIP ;; P)"
definition [upred_defs]: "CSP4(P) = (P ;; SKIP)"

subsection {* CSP Constructs *}

translations
  (type) "('\<sigma>, '\<phi>) circus" <= (type) "(_ list, ('\<sigma>, (_, '\<phi>) csp_vars) rsp_vars_ext) rp"
  
definition Stop :: "('\<sigma>, '\<phi>) rel_circus" where
[upred_defs]: "Stop = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition [upred_defs]:
"Skip = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R))"
  
definition Guard ::
  "'\<sigma> cond \<Rightarrow>
   ('\<sigma>, '\<phi>) rel_circus \<Rightarrow>
   ('\<sigma>, '\<phi>) rel_circus" (infixr "&\<^sub>u" 65) where
[upred_defs]: "g &\<^sub>u A = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R(A)) \<turnstile> ((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R(A)) \<or> (\<not> \<lceil>g\<rceil>\<^sub>S\<^sub><) \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition ExtChoice ::
  "('\<sigma>, '\<phi>) rel_circus \<Rightarrow> ('\<sigma>, '\<phi>) rel_circus \<Rightarrow> ('\<sigma>, '\<phi>) rel_circus" (infixl "\<box>" 65) where 
[upred_defs]: "A\<^sub>1 \<box> A\<^sub>2 = \<^bold>R\<^sub>s((pre\<^sub>R(A\<^sub>1) \<and> pre\<^sub>R(A\<^sub>2)) \<turnstile> ((cmt\<^sub>R(A\<^sub>1) \<and> cmt\<^sub>R(A\<^sub>2)) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R(A\<^sub>1) \<or> cmt\<^sub>R(A\<^sub>2))))"

text {*
  Simon, I changed the type of the parameter @{term e} of @{text "do\<^sub>u"} to
  an expression over undashed variable only rather then relational ones. I
  considered changing it to @{typ "'\<alpha>"} but realised that this causes some
  inconveniences as increasing the need for explicit coercions of alphabet
  types, for instance, if variables used in @{term e} have a state-space
  type consistent with the theory of CSP rather than plain program states.
  Intuitively, we may want to exclude that expression @{term e} refers to
  dashed or auxiliary variables though, which motivated my use @{typ "'\<alpha>"}.
*}
  
definition do\<^sub>u ::
  "_ \<Rightarrow> ('\<sigma>, '\<phi>) rel_circus" where
[upred_defs]: "do\<^sub>u e = ((($tr\<acute> =\<^sub>u $tr) \<and> \<lceil>e\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) \<triangleleft> $wait\<acute> \<triangleright> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>e\<rceil>\<^sub>S\<^sub><\<rangle>))"

text {*
  Simon, I believe we need a conjunction with @{term "\<lceil>II\<rceil>\<^sub>R"} here too, namely
  if we assume the operator will be used in the context of stateful processes.
  Otherwise, anything might happen to the program variables after the output
  communication was performed. Do you agree with this? If yes, just remove the
  comment with the next commit. If not, perhaps catch me and we talk about it!
*}

definition OutputCSP ::
  "('a, '\<phi>) chan \<Rightarrow>
  ('a, '\<sigma>) uexpr \<Rightarrow>
  ('\<sigma>, '\<phi>) rel_circus \<Rightarrow>
  ('\<sigma>, '\<phi>) rel_circus" where
[upred_defs]: "OutputCSP c v A = (\<^bold>R\<^sub>s(true \<turnstile> (do\<^sub>u (c\<cdot>v)\<^sub>u \<and> \<lceil>II\<rceil>\<^sub>R)) ;; A)"

definition do\<^sub>I :: "
  ('a, '\<theta>) chan \<Rightarrow>
  _ \<Rightarrow>
  ('a \<Rightarrow> ('\<sigma>, '\<theta>) rel_circus) \<Rightarrow>
  ('\<sigma>, '\<theta>) rel_circus" where
"do\<^sub>I c x P = (
  ($tr\<acute> =\<^sub>u $tr \<and> {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> (c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u}\<^sub>u \<inter>\<^sub>u $ref\<acute> =\<^sub>u {}\<^sub>u)
    \<triangleleft> $wait\<acute> \<triangleright>
  (($tr\<acute> - $tr) \<in>\<^sub>u {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> \<langle>(c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u\<rangle>}\<^sub>u \<and> (c\<cdot>$x\<acute>)\<^sub>u =\<^sub>u last\<^sub>u($tr\<acute>)))"

text {*
  Simon, I believe there was an earlier problem here due to the conjunction
  with @{term "\<lceil>II\<rceil>\<^sub>R"} as this also puts a constraint on variable @{term x}.
  If you agree with the fix below, feel free to remove this comments. Below
  I also highlighted places where we could consider using the plain program
  state type @{typ "'\<alpha>"}. I did not adopt this for the same reason as noted
  above, making usage more error-prone due to additional need for coercions.
*}

definition InputCSP ::
  "('a::{continuum, two}, '\<theta>) chan \<Rightarrow>
    ('a, (*'\<alpha>*) ('\<sigma>, '\<theta>) circus) lvar \<Rightarrow>
    ('a \<Rightarrow> (*'\<alpha>*) ('\<sigma>, '\<theta>) rel_circus) \<Rightarrow>
    (('a, ('\<sigma>, '\<theta>) circus) uvar \<Rightarrow> ('\<sigma>, '\<theta>) rel_circus) \<Rightarrow>
    ('\<sigma>, '\<theta>) rel_circus" where
"InputCSP c x P A = (var\<^bsub>RDES\<^esub> x \<bullet> \<^bold>R\<^sub>s(true \<turnstile> ((do\<^sub>I c x P) \<and> (\<exists> $x\<acute> \<bullet> II))) ;; A(x))"

syntax
  "_csp_sync" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<^bold>\<rightarrow> _" [81, 80] 80)
  "_csp_output" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"
    ("_!\<^sub>u'(_') \<rightarrow> _" [81, 0, 80] 80)
  "_csp_input"  :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"
    ("_?\<^sub>u'(_ :/ _') \<rightarrow> _" [81, 0, 0, 80] 80)

text {*
  Simon, I think @{text "(CONST top_var \<dots>"} below was a bug since the result
  is not a type instance of @{typ "('a, '\<alpha>) lvar"} but @{typ "('a, '\<alpha>) uvar"}.
  Could you perhaps check with the previous version of the translation rules?
  Pretty-printing of input prefixes now soft of works, although there is still
  an issue with eta-contractions (@{text "Syntax_Trans.preserve_binder_abs_\<dots>"}
  only handles the suppression of eta-contraction up to the second argument.
*}

translations
  "c \<^bold>\<rightarrow> A"         \<rightleftharpoons> "(CONST OutputCSP) c ()\<^sub>u A"
  "c!\<^sub>u(v) \<rightarrow> A"     \<rightleftharpoons> "(CONST OutputCSP) c v A"
  "c?\<^sub>u(x : P) \<rightarrow> A" \<rightharpoonup> "(CONST InputCSP) c
    (*(CONST top_var \<dots>*) (CONST MkDVar IDSTR(x)) (\<lambda>x. P) (\<lambda>x. A)"
  "c?\<^sub>u(x : P) \<rightarrow> A" \<leftharpoondown> "(CONST InputCSP) c x (\<lambda>v. P) (\<lambda>w. A)"

subsection {* Sequential Process Laws *}

theorem STOP_is_Stop: "STOP = Stop"
  by (rel_simp, meson minus_zero_eq order_refl ordered_cancel_monoid_diff_class.diff_cancel)
  
lemma rdes_export_cmt: "\<^bold>R\<^sub>s(P \<turnstile> cmt\<^sub>s \<dagger> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (rel_auto)
  
lemma rdes_export_pre: "\<^bold>R\<^sub>s((P\<lbrakk>true,false/$ok,$wait\<rbrakk>) \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (rel_auto)
    
lemma Guard_rdes_def:
  assumes "$ok\<acute> \<sharp> P"
  shows "g &\<^sub>u (\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> Q \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
proof -
  have "g &\<^sub>u (\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q)) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
    by (simp add: Guard_def)
  also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P)))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> R1(R2c(cmt\<^sub>s \<dagger> (P \<Rightarrow> Q))) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
    by (simp add: rea_pre_RHS_design rea_cmt_RHS_design)
  also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P)))) \<turnstile> R1(R2c(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> R1(R2c(cmt\<^sub>s \<dagger> (P \<Rightarrow> Q))) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P)))) \<turnstile> R1(R2c(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"
     by (simp add: R1_R2c_commute R1_disj R1_extend_conj' R1_idem R2c_and R2c_disj R2c_idem)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P)))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P)))) \<turnstile> cmt\<^sub>s \<dagger> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_cmt)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P)))) \<turnstile> cmt\<^sub>s \<dagger> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: usubst)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P)))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_cmt)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> (pre\<^sub>s \<dagger> (\<not> P))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (rel_auto)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<not> (pre\<^sub>s \<dagger> (\<not> P)))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_pre)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> P)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
   proof -
     from assms have "(\<not> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s false, $wait \<mapsto>\<^sub>s false] \<dagger> P) = (\<not> [$ok \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false] \<dagger> P)"
       by (rel_auto)
     thus ?thesis by (simp add: usubst)
   qed
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_pre)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> Q \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"  
     by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
   finally show ?thesis .
qed
  
lemma Guard_comp: 
  assumes "P is CSP"
  shows "g &\<^sub>u h &\<^sub>u P = (g \<and> h) &\<^sub>u P"
proof -
  have "g &\<^sub>u h &\<^sub>u P = g &\<^sub>u h &\<^sub>u \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    by (simp add: SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s ((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<lceil>h\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R P) \<turnstile>
                       (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (\<lceil>h\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R P \<or> \<not> \<lceil>h\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>) \<or> \<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
    by (simp add: Guard_rdes_def unrest)
  also have "... = \<^bold>R\<^sub>s (((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>h\<rceil>\<^sub>S\<^sub><) \<Rightarrow> pre\<^sub>R P) \<turnstile>
                       ((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>h\<rceil>\<^sub>S\<^sub><) \<and> cmt\<^sub>R P \<or> (\<not> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<or> \<not> \<lceil>h\<rceil>\<^sub>S\<^sub><) \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = \<^bold>R\<^sub>s (((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>h\<rceil>\<^sub>S\<^sub><) \<Rightarrow> pre\<^sub>R P) \<turnstile>
                       ((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>h\<rceil>\<^sub>S\<^sub><) \<and> cmt\<^sub>R P \<or> (\<not> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>h\<rceil>\<^sub>S\<^sub><) \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"
    by simp
  also have "... = (g \<and> h) &\<^sub>u \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    by (simp add: Guard_rdes_def aext_and ok'_pre_unrest)
  also have "... = (g \<and> h) &\<^sub>u P"
    by (simp add: SRD_reactive_design_alt assms)
  finally show ?thesis .
qed
  
lemma Guard_false [simp]: "false &\<^sub>u P = Stop"
  by (simp add: Guard_def Stop_def alpha)

lemma Guard_true [simp]: 
  "P is CSP \<Longrightarrow> true &\<^sub>u P = P"
  by (simp add: Guard_def alpha SRD_reactive_design_alt)
    
lemma RHS_design_neg_R2c_pre:
  "\<^bold>R\<^sub>s(R2c(P) \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (rel_auto)
  
lemma ExtChoice_rdes:
  assumes "$ok\<acute> \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>1"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)))"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2) =      
        \<^bold>R\<^sub>s ((pre\<^sub>R (\<^bold>R\<^sub>s (P\<^sub>1 \<turnstile> P\<^sub>2)) \<and> pre\<^sub>R (\<^bold>R\<^sub>s (Q\<^sub>1 \<turnstile> Q\<^sub>2))) \<turnstile>
            ((cmt\<^sub>R (\<^bold>R\<^sub>s (P\<^sub>1 \<turnstile> P\<^sub>2)) \<and> cmt\<^sub>R (\<^bold>R\<^sub>s (Q\<^sub>1 \<turnstile> Q\<^sub>2))) 
                  \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright>
             (cmt\<^sub>R (\<^bold>R\<^sub>s (P\<^sub>1 \<turnstile> P\<^sub>2)) \<or> cmt\<^sub>R (\<^bold>R\<^sub>s (Q\<^sub>1 \<turnstile> Q\<^sub>2)))))"
    by (simp add: ExtChoice_def)  
  also have "... =
        \<^bold>R\<^sub>s (((\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> P\<^sub>1)))) \<and> (\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> Q\<^sub>1))))) \<turnstile>
            ((R1(R2c(cmt\<^sub>s \<dagger> (P\<^sub>1 \<Rightarrow> P\<^sub>2))) \<and> R1(R2c(cmt\<^sub>s \<dagger> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)))) 
                  \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright>
             (R1(R2c(cmt\<^sub>s \<dagger> (P\<^sub>1 \<Rightarrow> P\<^sub>2))) \<or> R1(R2c(cmt\<^sub>s \<dagger> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2))))))"
      by (simp add: rea_pre_RHS_design rea_cmt_RHS_design)
  also have "... =
        \<^bold>R\<^sub>s (((\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> P\<^sub>1)))) \<and> (\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> Q\<^sub>1))))) \<turnstile>
            R1(R2c
            ((R1(R2c(cmt\<^sub>s \<dagger> (P\<^sub>1 \<Rightarrow> P\<^sub>2))) \<and> R1(R2c(cmt\<^sub>s \<dagger> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)))) 
                  \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright>
             (R1(R2c(cmt\<^sub>s \<dagger> (P\<^sub>1 \<Rightarrow> P\<^sub>2))) \<or> R1(R2c(cmt\<^sub>s \<dagger> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)))))))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
  also have "... =
        \<^bold>R\<^sub>s (((\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> P\<^sub>1)))) \<and> (\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> Q\<^sub>1))))) \<turnstile>
            R1(R2c
            (((cmt\<^sub>s \<dagger> (P\<^sub>1 \<Rightarrow> P\<^sub>2)) \<and> (cmt\<^sub>s \<dagger> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2))) 
                  \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright>
             ((cmt\<^sub>s \<dagger> (P\<^sub>1 \<Rightarrow> P\<^sub>2)) \<or> (cmt\<^sub>s \<dagger> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2))))))"
    by (simp add: R1_R2c_commute R1_cond R1_conj R1_disj R1_idem R2c_and R2c_condr R2c_disj R2c_idem)
  also have "... =
        \<^bold>R\<^sub>s (((\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> P\<^sub>1)))) \<and> (\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> Q\<^sub>1))))) \<turnstile>
            (((cmt\<^sub>s \<dagger> (P\<^sub>1 \<Rightarrow> P\<^sub>2)) \<and> (cmt\<^sub>s \<dagger> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2))) 
                  \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright>
             ((cmt\<^sub>s \<dagger> (P\<^sub>1 \<Rightarrow> P\<^sub>2)) \<or> (cmt\<^sub>s \<dagger> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)))))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
  also have "... =
        \<^bold>R\<^sub>s (((\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> P\<^sub>1)))) \<and> (\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> Q\<^sub>1))))) \<turnstile>
            cmt\<^sub>s \<dagger>
            (((cmt\<^sub>s \<dagger> (P\<^sub>1 \<Rightarrow> P\<^sub>2)) \<and> (cmt\<^sub>s \<dagger> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2))) 
                  \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright>
             ((cmt\<^sub>s \<dagger> (P\<^sub>1 \<Rightarrow> P\<^sub>2)) \<or> (cmt\<^sub>s \<dagger> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)))))"
    by (simp add: rdes_export_cmt)
  also have "... =
        \<^bold>R\<^sub>s (((\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> P\<^sub>1)))) \<and> (\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> Q\<^sub>1))))) \<turnstile>
            cmt\<^sub>s \<dagger>
            (((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<and> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> ((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<or> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2))))"
    by (simp add: usubst)
  also have "... =
        \<^bold>R\<^sub>s (((\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> P\<^sub>1)))) \<and> (\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> Q\<^sub>1))))) \<turnstile>
            (((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<and> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> ((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<or> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2))))"
    by (simp add: rdes_export_cmt)
  also have "... =
        \<^bold>R\<^sub>s ((\<not> (R1 (R2c (pre\<^sub>s \<dagger> (\<not> P\<^sub>1))) \<or> R1 (R2c (pre\<^sub>s \<dagger> (\<not> Q\<^sub>1))))) \<turnstile>
            (((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<and> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> ((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<or> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2))))"
    by simp
  also have "... =
        \<^bold>R\<^sub>s ((\<not> R1 (R2c (pre\<^sub>s \<dagger> (\<not> P\<^sub>1 \<or> \<not> Q\<^sub>1)))) \<turnstile>
            (((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<and> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> ((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<or> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2))))"
    by (simp add: R1_R2c_is_R2 R2_disj subst_disj)    
  also have "... =
        \<^bold>R\<^sub>s ((\<not> R2c (pre\<^sub>s \<dagger> (\<not> P\<^sub>1 \<or> \<not> Q\<^sub>1))) \<turnstile>
            (((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<and> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> ((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<or> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2))))"
    by (metis (no_types, lifting) RHS_design_neg_R1_pre conj_disj_abs utp_pred.compl_sup_top)
  also have "... =
        \<^bold>R\<^sub>s ((\<not> pre\<^sub>s \<dagger> (\<not> P\<^sub>1 \<or> \<not> Q\<^sub>1)) \<turnstile>
            (((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<and> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> ((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<or> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2))))"
    by (metis (no_types, hide_lams) R2c_not RHS_design_neg_R2c_pre)
  also from assms have "... =
        \<^bold>R\<^sub>s ((\<not> (\<not> P\<^sub>1 \<or> \<not> Q\<^sub>1))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile>
            (((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<and> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> ((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<or> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2))))"
  proof -
    from assms have "(\<not> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s false, $wait \<mapsto>\<^sub>s false] \<dagger> P\<^sub>1) = (\<not> [$ok \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false] \<dagger> P\<^sub>1)"
      by (rel_auto)
    moreover from assms have "(\<not> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s false, $wait \<mapsto>\<^sub>s false] \<dagger> Q\<^sub>1) = (\<not> [$ok \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false] \<dagger> Q\<^sub>1)"
      by (rel_auto)
    ultimately show ?thesis by (simp add: usubst)
  qed
  also have "... =
        \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<and> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> ((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<or> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2))))"
    by (simp add: rdes_export_pre)
  also have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)      
  finally show ?thesis .
qed

lemma ExtChoice_comm:
  "P \<box> Q = Q \<box> P"
  by (simp add: ExtChoice_def conj_comm disj_comm)

lemma ExtChoice_Stop:
  assumes "Q is CSP"
  shows "Stop \<box> Q = Q"
proof -
  have "Stop \<box> Q = \<^bold>R\<^sub>s (true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q))"
    by (simp add: Stop_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> ((($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>) \<and> cmt\<^sub>R Q) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<or> cmt\<^sub>R Q)))"
    by (simp add: ExtChoice_rdes unrest)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> (cmt\<^sub>R Q \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> cmt\<^sub>R Q))"
    by (metis (no_types, lifting) cond_def eq_upred_sym neg_conj_cancel1 utp_pred.inf.left_idem)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> cmt\<^sub>R Q)"
    by (simp add: cond_idem)
  also have "... = Q"
    by (simp add: SRD_reactive_design_alt assms)
  finally show ?thesis .
qed
  
subsection {* Parallel Composition *}

subsection {* Merge Predicates *}

text {*
  Simon, why @{term "$tr\<acute> \<le>\<^sub>u $tr\<^sub><"} and not @{term "$tr\<^sub>< \<le>\<^sub>u $tr\<acute>"} below?
  Also as the function appears to be the merge operation for reactive designs
  (subscript @{text "R"}), would it conceptually not be better placed in the
  theory @{theory utp_rea_designs}? Strangely, the function below appears not
  to be used anywhere else. Is it redundant now? If so, perhaps remove it!
*}

definition merge_rd ("M\<^sub>R") where
[upred_defs]: "M\<^sub>R(M) =
  ($ok\<acute> =\<^sub>u ($0-ok \<and> $1-ok) \<and> $wait\<acute> =\<^sub>u ($0-wait \<and> $1-wait) \<and> $tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<and> M)"

text {*
  I wonder if there is a possibility that the terms @{term "$0-tr - $tr\<^sub><"} and
  @{term "$1-tr - $tr\<^sub><"} could be undefined. What ensures, for instance, that
  @{term "$tr\<^sub>< \<le>\<^sub>u $0-tr"} holds? I presume this is guaranteed by both operand
  processes of the parallel composition being healthy, right? So maybe we do
  not have to worry about it here. Another issues may be the constraint on the
  refusal set. Do we not need to take into account @{term cs} as well in order
  to calculate the refusals @{term "$ref\<acute>"} of the composition? Ask Simon!
*}

definition N0 :: "'\<psi> set \<Rightarrow> ((unit,'\<psi>) circus) merge" where
[upred_defs]: "N0(cs) = (
  $wait\<acute> =\<^sub>u ($0-wait \<or> $1-wait) \<and>
  (* Not sure about the next line... (Frank) *)
  $ref\<acute> =\<^sub>u ($0-ref \<union>\<^sub>u $1-ref) \<and>
  $tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<and>
  ($tr\<acute> - $tr\<^sub><) \<in>\<^sub>u ($0-tr - $tr\<^sub><) \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> ($1-tr - $tr\<^sub><) \<and>
  ($0-tr - $tr\<^sub><) \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u ($1-tr - $tr\<^sub><) \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>)"

text {* The definition below does not seem to be used anywhere... Remove? *}

definition M0 :: "'\<psi> set \<Rightarrow> ((unit,'\<psi>) circus) merge" where
[upred_defs]: "M0(cs) = (N0(cs) ;; SKIP)"

definition CSPMerge' ("N\<^sub>C\<^sub>S\<^sub>P") where
[upred_defs]: "CSPMerge'(cs) = ($ok\<acute> =\<^sub>u ($0-ok \<and> $1-ok) \<and> N0(cs))"

text {*
  I suppose composition with @{term SKIP} is to remove and constraints on the
  refusal set after termination, and thus make the process CSP-healthy.
*}

definition CSPMerge ("M\<^sub>C\<^sub>S\<^sub>P") where
[upred_defs]: "CSPMerge(cs) = (N\<^sub>C\<^sub>S\<^sub>P(cs) ;; SKIP)"

subsection {* Parallel Operator *}

text {*
  So we are not considering processes with program state. Is there a way to
  generalise the definition below to cater fro state too? Or are there some
  semantic issues associated with this, beyond merging the state spaces?
*}

abbreviation ParCSP ::
  "'\<theta> rel_csp \<Rightarrow> '\<theta> event set \<Rightarrow> '\<theta> rel_csp \<Rightarrow> '\<theta> rel_csp" (infixl "[|_|]" 85) where
"P [|cs|] Q \<equiv> P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q"

subsubsection {* CSP Merge Laws *}

text {* Jim's merge predicate lemmas. *}

lemma JL1: "(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk> = (N0(cs) ;; R1(true))"
  by (rel_auto)

lemma JL2: "(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk> = (N0(cs) ;; R1(true))"
  by (rel_auto)

lemma JL3: "(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk> = (N0(cs) ;; R1(true))"
  by (rel_auto)

lemma SKIP_no_start: "(SKIP\<lbrakk>false/$ok\<rbrakk>) = R1(true)"
  by (rel_auto)

lemma SKIP_pre: "SKIP\<^sup>f = R1(\<not> $ok)"
  by (rel_auto)

lemma parallel_ok_cases:
"((P \<parallel>\<^sub>s Q) ;; M) = (
  ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
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
  also have "... = (
      ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk>)))"
    by (simp add: true_alt_def[THEN sym] false_alt_def[THEN sym] disj_assoc
      utp_pred.sup.left_commute utp_pred.sup_commute usubst)
  finally show ?thesis .
qed

lemma SKIP_alt_def: "SKIP = \<^bold>R\<^sub>s(\<exists> $ref \<bullet> II\<^sub>r)"
  by (rel_auto)

lemma SKIP_rea_des: "SKIP = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute>))"
  by (rel_auto)

lemma SKIP_is_R1: "SKIP is R1"
  by (rel_auto)

lemma SKIP_is_R2: "SKIP is R2"
  by (rel_auto)

lemma SKIP_is_R3c: "SKIP is R3h"
apply (rel_auto)
apply (simp_all add: zero_list_def)
apply (metis less_eq_list_def strict_prefix_diff_minus)
done

lemma SKIP_is_CSP1: "SKIP is CSP1"
  by (rel_auto)

lemma SKIP_is_CSP2: "SKIP is CSP2"
  by (rel_auto)

lemma CSPMerge'_is_R1m:
"CSPMerge'(cs) is R1m"
  by (rel_auto)

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

(*
lemma parallel'_is_R3:
assumes "P is R3" "Q is R3"
shows "(P \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R3"
proof -
  have "(skip\<^sub>m ;; N\<^sub>C\<^sub>S\<^sub>P(cs)) = II"
    apply (rel_auto) 
  thus ?thesis
    by (simp add: R3_par_by_merge assms)
qed
*)


lemma CSPMerge_div_prop:
"(div\<^sub>m ;; CSPMerge(cs)) = R1 true"
apply (rel_auto)
apply (rename_tac ok wait tr ref ok' wait' tr' ref')
apply (rule_tac x = "ok" in exI)
apply (rule_tac x = "wait" in exI)
apply (rule_tac x = "tr" in exI)
apply (rule_tac x = "ref" in exI)
apply (simp)
apply (metis minus_cancel order_refl singletonI tr_par.simps(1))
done

lemma CSPMerge_wait_prop:
"(wait\<^sub>m ;; M\<^sub>C\<^sub>S\<^sub>P(cs)) = (\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
  apply (rel_auto)
  apply (metis minus_zero_eq singletonD tr_par.simps(1) zero_list_def)
  apply (metis (full_types) insert_iff order_refl ordered_cancel_monoid_diff_class.diff_cancel tr_par.simps(1) zero_list_def)
done

lemma parallel_is_R3c:
assumes "P is R1" "Q is R1" "P is CSP1" "Q is CSP1" "P is R3h" "Q is R3h"
shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R3h"
  by (simp add: CSPMerge_div_prop CSPMerge_wait_prop R3h_par_by_merge assms)

lemma parallel_is_CSP1:
assumes "P is R1" "Q is R1" "P is CSP1" "Q is CSP1"
shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is CSP1"
  by (simp add: RD1_par_by_merge CSPMerge_div_prop CSPMerge_is_R1m assms)

lemma parallel_is_CSP2:
"(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is CSP2"
proof -
  have "M\<^sub>C\<^sub>S\<^sub>P(cs) is RD2"
  proof -
    have "RD2(M\<^sub>C\<^sub>S\<^sub>P(cs)) = (M\<^sub>C\<^sub>S\<^sub>P(cs) ;; J)"
      by (simp add: RD2_def H2_def)
    also have "... = ((N\<^sub>C\<^sub>S\<^sub>P(cs) ;; SKIP) ;; J)"
      by (simp add: CSPMerge_def)
    also have "... = (N\<^sub>C\<^sub>S\<^sub>P(cs) ;; (SKIP ;; J))"
      by (simp add: seqr_assoc)
    also have "... = (N\<^sub>C\<^sub>S\<^sub>P(cs) ;; (CSP2(SKIP)))"
      by (simp add: RD2_def H2_def)
    also have "... = (N\<^sub>C\<^sub>S\<^sub>P(cs) ;; SKIP)"
      by (simp add: Healthy_if SKIP_is_CSP2)
    finally show ?thesis
      by (simp add: Healthy_def' CSPMerge_def)
  qed
  thus ?thesis
    using RD2_par_by_merge by blast
qed

lemma parallel_is_CSP:
assumes "P is CSP" "Q is CSP"
shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is CSP"
  by (metis SRD_healths(1-4) SRD_intro assms parallel_is_CSP1 parallel_is_CSP2
    parallel_is_R1 parallel_is_R2 parallel_is_R3c)

lemma parallel_precondition:
assumes "P is CSP2"
shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>f\<^sub>f = ((P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0(cs) ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<or> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0(cs) ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>f\<^sub>f = ((P \<parallel>\<^sub>s Q) ;; M\<^sub>C\<^sub>S\<^sub>P(cs))\<^sup>f\<^sub>f"
    by (simp add: par_by_merge_def)
  also have "... = (((P \<^sub>f \<parallel>\<^sub>s Q \<^sub>f) ;; N\<^sub>C\<^sub>S\<^sub>P(cs)) ;; R1(\<not> $ok))"
    by rel_blast
  also have "... = ((
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk>))) ;; R1(\<not> $ok))"
    by (subst parallel_ok_cases, subst_tac)
  also have "... = ((
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk> ;; R1(\<not> $ok))) \<or>
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
        by (metis RD2_def H2_equivalence Healthy_def')
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
  also have "... = (
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((N0 cs ;; R1(\<not> $ok)))) \<or>
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((N0 cs ;; R1(\<not> $ok)))))"
    by (rel_auto, blast+)
  also have "... = (
      (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(\<not> $ok)\<^esub> Q\<^sup>t\<^sub>f) \<or>
      (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(\<not> $ok)\<^esub> Q\<^sup>f\<^sub>f))"
    (is "_ = ((P\<^sup>f\<^sub>f \<parallel>\<^bsub>?M1\<^esub> Q\<^sup>t\<^sub>f) \<or> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>?M2\<^esub> Q\<^sup>f\<^sub>f))")
    by (simp add: par_by_merge_def)
  also have "... = (
      (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<or>
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
shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>t\<^sub>f = (
  (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f) \<or>
  (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0(cs) ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<or>
  (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0(cs) ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>t\<^sub>f = ((P \<parallel>\<^sub>s Q) ;; M\<^sub>C\<^sub>S\<^sub>P(cs))\<^sup>t\<^sub>f"
    by (simp add: par_by_merge_def)
  also have "... = ((P \<^sub>f \<parallel>\<^sub>s Q \<^sub>f) ;; (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t)"
    by (rel_blast)
  also have "... = (
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk>)))"
    by (subst parallel_ok_cases, subst_tac)
  also have "... = (
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; (N0(cs) ;; R1(true))) \<or>
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; (N0(cs) ;; R1(true))) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; (N0(cs) ;; R1(true))))"
      (is "_ = (?C1 \<or>\<^sub>p ?C2 \<or>\<^sub>p ?C3 \<or>\<^sub>p ?C4)")
    by (simp add: JL1 JL2 JL3)
  also have "... = (
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; (N0(cs) ;; R1(true))) \<or>
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; (N0(cs) ;; R1(true))))"
  proof -
    from assms have "`P\<^sup>f \<Rightarrow> P\<^sup>t`"
      by (metis RD2_def H2_equivalence Healthy_def')
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

theorem parallel_reactive_design:
assumes "P is CSP" "Q is CSP"
shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) = \<^bold>R\<^sub>s(
  (\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<and> \<not> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))
    \<turnstile>
  (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f))"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) = \<^bold>R\<^sub>s((\<not> (P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>f\<^sub>f) \<turnstile> (P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>t\<^sub>f)"
    by (simp add: SRD_reactive_design assms parallel_is_CSP)
  also have "... = \<^bold>R\<^sub>s(
    (\<not> ((P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 (true)\<^esub> Q\<^sup>t\<^sub>f) \<or> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 (true)\<^esub> Q\<^sup>f\<^sub>f)))
      \<turnstile>
    (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f \<or>
     P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>t\<^sub>f \<or>
     P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>f\<^sub>f))"
    by (simp add: parallel_precondition parallel_postcondition SRD_healths(5) assms(1))
  also have "... = \<^bold>R\<^sub>s(
    (\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 (true)\<^esub> Q\<^sup>t\<^sub>f) \<and> \<not> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f)) 
      \<turnstile>
    ((\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 (true)\<^esub> Q\<^sup>t\<^sub>f \<or> P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f)) \<and>
    (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f \<or>
     P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>t\<^sub>f \<or>
     P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>f\<^sub>f)))"
    by (simp add: design_export_pre)
  also have "... = \<^bold>R\<^sub>s(
    (\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<and> \<not> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))
      \<turnstile>
    ((\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f \<or> P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f)) \<and>
      (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f)))"
    by (subst neg_conj_cancel2, simp)
  also have "... = \<^bold>R\<^sub>s(
    (\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<and> \<not> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))
      \<turnstile>
    (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f))"
    by (simp add: design_export_pre)
  finally show ?thesis by simp
qed

lemma design_subst_ok_ok: "(P\<lbrakk>true/$ok\<rbrakk> \<turnstile> Q\<lbrakk>true/$ok\<rbrakk>) = (P \<turnstile> Q)"
  by (rel_auto)

theorem parallel_reactive_design':
  assumes "P is CSP" "Q is CSP"
  shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) = \<^bold>R\<^sub>s(
    (\<not> ((\<not> pre\<^sub>R(P)) \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> cmt\<^sub>R(Q)) \<and>
     \<not> (cmt\<^sub>R(P) \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> (\<not> pre\<^sub>R(Q)))) \<turnstile>
    (cmt\<^sub>R(P) \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> cmt\<^sub>R(Q)))"
proof -
  have 1:"(P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>t\<^sub>f)\<lbrakk>true/$ok\<rbrakk> = (\<not> pre\<^sub>R(P)) \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> cmt\<^sub>R(Q)"
    by (rel_blast)

  have 2:"(P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>f\<^sub>f)\<lbrakk>true/$ok\<rbrakk> = (cmt\<^sub>R(P) \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> (\<not> pre\<^sub>R(Q)))"
    by (rel_blast)

  have 3:"(P\<^sup>t\<^sub>f \<parallel>\<^bsub>[$0-ok \<mapsto>\<^sub>s true, $1-ok \<mapsto>\<^sub>s true] \<dagger> (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<^esub> Q\<^sup>t\<^sub>f)\<lbrakk>true/$ok\<rbrakk> =
      cmt\<^sub>R P \<parallel>\<^bsub>[$0-ok \<mapsto>\<^sub>s true, $1-ok \<mapsto>\<^sub>s true] \<dagger> (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<^esub> cmt\<^sub>R Q"
    by (rel_blast)

  have "\<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>t\<^sub>f \<and> \<not> P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>f\<^sub>f) \<turnstile>
             P\<^sup>t\<^sub>f \<parallel>\<^bsub>[$0-ok \<mapsto>\<^sub>s true, $1-ok \<mapsto>\<^sub>s true] \<dagger> (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<^esub> Q\<^sup>t\<^sub>f) =
        \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>t\<^sub>f \<and> \<not> P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>f\<^sub>f)\<lbrakk>true/$ok\<rbrakk> \<turnstile>
            (P\<^sup>t\<^sub>f \<parallel>\<^bsub>[$0-ok \<mapsto>\<^sub>s true, $1-ok \<mapsto>\<^sub>s true] \<dagger> (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<^esub> Q\<^sup>t\<^sub>f)\<lbrakk>true/$ok\<rbrakk>)"
    by (simp add: design_subst_ok_ok)

  also have "... =
      \<^bold>R\<^sub>s((\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>t\<^sub>f)\<lbrakk>true/$ok\<rbrakk> \<and>
         \<not> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>f\<^sub>f)\<lbrakk>true/$ok\<rbrakk>) \<turnstile>
        (P\<^sup>t\<^sub>f \<parallel>\<^bsub>[$0-ok \<mapsto>\<^sub>s true, $1-ok \<mapsto>\<^sub>s true] \<dagger> (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<^esub> Q\<^sup>t\<^sub>f)\<lbrakk>true/$ok\<rbrakk>)"
    by (simp add: usubst)

  also have "... =
      \<^bold>R\<^sub>s((\<not> ((\<not> pre\<^sub>R(P)) \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> cmt\<^sub>R(Q)) \<and>
         \<not> (cmt\<^sub>R(P) \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> (\<not> pre\<^sub>R(Q)))) \<turnstile>
        (cmt\<^sub>R(P) \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> cmt\<^sub>R(Q)))"
    by (simp add: 1 2 3)

  finally show ?thesis
    by (simp add: parallel_reactive_design assms)
qed

lemma swap_CSPMerge': "(swap\<^sub>m ;; N\<^sub>C\<^sub>S\<^sub>P cs) = N\<^sub>C\<^sub>S\<^sub>P cs"
  by (rel_auto, (metis tr_par_sym)+)

lemma swap_CSPMerge: "(swap\<^sub>m ;; M\<^sub>C\<^sub>S\<^sub>P cs) = M\<^sub>C\<^sub>S\<^sub>P cs"
  by (simp add: CSPMerge_def seqr_assoc swap_CSPMerge')

theorem parallel_commutative:
  "(P [|cs|] Q) = (Q [|cs|] P)"
  by (simp add: par_by_merge_commute swap_CSPMerge)

    
end