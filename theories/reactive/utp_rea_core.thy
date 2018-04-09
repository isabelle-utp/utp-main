section \<open> Reactive Processes Core Definitions \<close>

theory utp_rea_core
  imports
  "../../toolkit/Trace_Algebra_Hierarchy"
  (*"UTP-Toolkit.Trace_Algebra"*)
  "UTP.utp_concurrency"
  "UTP-Designs.utp_designs"
begin recall_syntax

subsection \<open> Alphabet and Signature \<close>

text \<open> The alphabet of reactive processes contains a boolean variable $wait$, which denotes whether
  a process is exhibiting an intermediate observation. It also has the variable $tr$ which denotes
  the trace history of a process. The type parameter @{typ "'t"} represents the trace model being
  used, which must form a trace algebra~\cite{Foster17b}, and thus provides the theory of ``generalised 
  reactive processes''~\cite{Foster17b}. The reactive process alphabet also extends
  the design alphabet, and thus includes the $ok$ variable. For more information on these, see
  the UTP book~\cite{Hoare&98}, or the associated tutorial~\cite{Cavalcanti&06}. \<close>

alphabet 't::fzero_weak_trace rp_vars = des_vars +
  wait :: bool
  tr   :: "'t"

type_synonym ('t, '\<alpha>) rp = "('t, '\<alpha>) rp_vars_scheme des"

type_synonym ('t,'\<alpha>,'\<beta>) rel_rp  = "(('t,'\<alpha>) rp, ('t,'\<beta>) rp) urel"
type_synonym ('t,'\<alpha>) hrel_rp  = "('t,'\<alpha>) rp hrel"

translations
  (type) "('t,'\<alpha>) rp" <= (type) "('t, '\<alpha>) rp_vars_scheme des"
  (type) "('t,'\<alpha>) rp" <= (type) "('t, '\<alpha>) rp_vars_ext des"
  (type) "('t,'\<alpha>,'\<beta>) rel_rp" <= (type) "(('t,'\<alpha>) rp, ('\<gamma>,'\<beta>) rp) urel"
  (type) "('t, '\<alpha>) hrel_rp"  <= (type) "('t, '\<alpha>) rp hrel"

text \<open> As for designs, we set up various types to represent reactive processes. The main types
  to be used are @{typ "('t,'\<alpha>,'\<beta>) rel_rp"} and @{typ "('t,'\<alpha>) hrel_rp"}, which correspond
  to heterogeneous/homogeneous reactive processes whose trace model is @{typ "'t"} and alphabet 
  types are @{typ "'\<alpha>"} and @{typ "'\<beta>"}. We also set up some useful syntax translations for these. \<close>

notation rp_vars_child_lens\<^sub>a ("\<Sigma>\<^sub>r")
notation rp_vars_child_lens ("\<Sigma>\<^sub>R")

syntax
  "_svid_rea_alpha"  :: "svid" ("\<Sigma>\<^sub>R")

translations
  "_svid_rea_alpha" => "CONST rp_vars_child_lens"

text \<open> Lens @{term "\<Sigma>\<^sub>R"} exists because reactive alphabets are extensible. @{term "\<Sigma>\<^sub>R"} points
  to the portion of the alphabet / state space that is neither $ok$, $wait$, or $tr$. \<close>

declare rp_vars.splits [alpha_splits]
declare rp_vars.defs [lens_defs]
declare zero_list_def [upred_defs]
declare plus_list_def [upred_defs]
declare prefixE [elim]
  
text \<open>
  The two locale interpretations below are a technicality to improve automatic
  proof support via the predicate and relational tactics. This is to enable the
  (re-)interpretation of state spaces to remove any occurrences of lens types
  after the proof tactics @{method pred_simp} and @{method rel_simp}, or any
  of their derivatives have been applied. Eventually, it would be desirable to
  automate both interpretations as part of a custom outer command for defining
  alphabets.
\<close>

interpretation rp_vars:
  lens_interp "\<lambda>(ok, r). (ok, wait\<^sub>v r, tr\<^sub>v r, more r)"
  apply (unfold_locales)
  apply (rule injI)
  apply (clarsimp)
  done

interpretation rp_vars_rel: lens_interp "\<lambda>(ok, ok', r, r').
  (ok, ok', wait\<^sub>v r, wait\<^sub>v r', tr\<^sub>v r, tr\<^sub>v r', more r, more r')"
  apply (unfold_locales)
  apply (rule injI)
  apply (clarsimp)
  done

text \<open> The following syntactic orders exist to help to order lens names when, for example, 
  performing substitution, to achieve normalisation of terms. \<close>

lemma rea_var_ords [usubst]:
  "$tr \<prec>\<^sub>v $tr\<acute>" "$wait \<prec>\<^sub>v $wait\<acute>"
  "$ok \<prec>\<^sub>v $tr" "$ok\<acute> \<prec>\<^sub>v $tr\<acute>" "$ok \<prec>\<^sub>v $tr\<acute>" "$ok\<acute> \<prec>\<^sub>v $tr"
  "$ok \<prec>\<^sub>v $wait" "$ok\<acute> \<prec>\<^sub>v $wait\<acute>" "$ok \<prec>\<^sub>v $wait\<acute>" "$ok\<acute> \<prec>\<^sub>v $wait"
  "$tr \<prec>\<^sub>v $wait" "$tr\<acute> \<prec>\<^sub>v $wait\<acute>" "$tr \<prec>\<^sub>v $wait\<acute>" "$tr\<acute> \<prec>\<^sub>v $wait"
  by (simp_all add: var_name_ord_def)

abbreviation wait_f::"('t::fzero_weak_trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp"
where "wait_f R \<equiv> R\<lbrakk>false/$wait\<rbrakk>"

abbreviation wait_t::"('t::fzero_weak_trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('t, '\<alpha>, '\<beta>) rel_rp"
where "wait_t R \<equiv> R\<lbrakk>true/$wait\<rbrakk>"
  
syntax
  "_wait_f"  :: "logic \<Rightarrow> logic" ("_\<^sub>f" [1000] 1000)
  "_wait_t"  :: "logic \<Rightarrow> logic" ("_\<^sub>t" [1000] 1000)

translations
  "P \<^sub>f" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST wait) false) P"
  "P \<^sub>t" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ivar CONST wait) true) P"

abbreviation lift_rea :: "_ \<Rightarrow> _" ("\<lceil>_\<rceil>\<^sub>R") where
"\<lceil>P\<rceil>\<^sub>R \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>R \<times>\<^sub>L \<Sigma>\<^sub>R)"

abbreviation drop_rea :: "('t::fzero_weak_trace, '\<alpha>, '\<beta>) rel_rp \<Rightarrow> ('\<alpha>, '\<beta>) urel" ("\<lfloor>_\<rfloor>\<^sub>R") where
"\<lfloor>P\<rfloor>\<^sub>R \<equiv> P \<restriction>\<^sub>e (\<Sigma>\<^sub>R \<times>\<^sub>L \<Sigma>\<^sub>R)"

abbreviation rea_pre_lift :: "_ \<Rightarrow> _" ("\<lceil>_\<rceil>\<^sub>R\<^sub><") where "\<lceil>n\<rceil>\<^sub>R\<^sub>< \<equiv> \<lceil>\<lceil>n\<rceil>\<^sub><\<rceil>\<^sub>R"

subsection \<open> Reactive Lemmas \<close>

lemma unrest_ok_lift_rea [unrest]:
  "$ok \<sharp> \<lceil>P\<rceil>\<^sub>R" "$ok\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>R"
  by (pred_auto)+

lemma unrest_wait_lift_rea [unrest]:
  "$wait \<sharp> \<lceil>P\<rceil>\<^sub>R" "$wait\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>R"
  by (pred_auto)+

lemma unrest_tr_lift_rea [unrest]:
  "$tr \<sharp> \<lceil>P\<rceil>\<^sub>R" "$tr\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>R"
  by (pred_auto)+

lemma wait_tr_bij_lemma: "bij_lens (wait\<^sub>a +\<^sub>L tr\<^sub>a +\<^sub>L \<Sigma>\<^sub>r)"
  by (unfold_locales, auto simp add: lens_defs)

lemma des_lens_equiv_wait_tr_rest: "\<Sigma>\<^sub>D \<approx>\<^sub>L wait +\<^sub>L tr +\<^sub>L \<Sigma>\<^sub>R"
proof -
  have "wait +\<^sub>L tr +\<^sub>L \<Sigma>\<^sub>R = (wait\<^sub>a +\<^sub>L tr\<^sub>a +\<^sub>L \<Sigma>\<^sub>r) ;\<^sub>L \<Sigma>\<^sub>D"
    by (simp add: plus_lens_distr wait_def tr_def rp_vars_child_lens_def)
  also have "... \<approx>\<^sub>L 1\<^sub>L ;\<^sub>L \<Sigma>\<^sub>D"
    using lens_equiv_via_bij wait_tr_bij_lemma by auto
  also have "... = \<Sigma>\<^sub>D"
    by (simp)
  finally show ?thesis
    using lens_equiv_sym by blast
qed

lemma rea_lens_bij: "bij_lens (ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L \<Sigma>\<^sub>R)"
proof -
  have "ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L \<Sigma>\<^sub>R \<approx>\<^sub>L ok +\<^sub>L \<Sigma>\<^sub>D"
    using des_lens_equiv_wait_tr_rest des_vars_indeps lens_equiv_sym lens_plus_eq_right by blast
  also have "... \<approx>\<^sub>L 1\<^sub>L"
    using bij_lens_equiv_id[of "ok +\<^sub>L \<Sigma>\<^sub>D"] by (simp add: ok_des_bij_lens)
  finally show ?thesis
    by (simp add: bij_lens_equiv_id)
qed

lemma seqr_wait_true [usubst]: "(P ;; Q) \<^sub>t = (P \<^sub>t ;; Q)"
  by (rel_auto)

lemma seqr_wait_false [usubst]: "(P ;; Q) \<^sub>f = (P \<^sub>f ;; Q)"
  by (rel_auto)

subsection {* Trace contribution lens *}

text \<open> The following lens represents the portion of the state-space that is the difference
  between $tr'$ and $tr$, that is the contribution that a process is making to the trace
  history. \<close>

consts g :: "'t \<Rightarrow> 't"

definition tcontr :: "'t::fzero_weak_trace \<Longrightarrow> ('t, '\<alpha>) rp \<times> ('t, '\<alpha>) rp" ("tt") where
  [lens_defs]:
  "tcontr = \<lparr> lens_get = (\<lambda> s. get\<^bsub>($tr\<acute>)\<^sub>v\<^esub> s - get\<^bsub>($tr)\<^sub>v\<^esub> s) , 
              lens_put = (\<lambda> s v. put\<^bsub>($tr\<acute>)\<^sub>v\<^esub> s (get\<^bsub>($tr)\<^sub>v\<^esub> s + v)) \<rparr>"

definition itrace :: "'t::fzero_weak_trace \<Longrightarrow> ('t, '\<alpha>) rp \<times> ('t, '\<alpha>) rp" ("\<^bold>i\<^bold>t") where
  [lens_defs]:
  "itrace = \<lparr> lens_get = get\<^bsub>($tr)\<^sub>v\<^esub>, 
              lens_put = (\<lambda> s v. put\<^bsub>($tr\<acute>)\<^sub>v\<^esub> (put\<^bsub>($tr)\<^sub>v\<^esub> s v) v) \<rparr>"

(* Without this it is not possible to have that:
   tr'-tr=v \<longleftrightarrow> tr' = tr + v
   In the new experiment this only holds if 'v' is 'disjoint' with tr. So we 
   would need an entirely different concept of a mwb_lens wrt. this disjointed property 
lemma tcontr_mwb_lens [simp]: "mwb_lens tt"
  apply unfold_locales
   apply (simp only:tcontr_def)
  apply (simp add:fzero_subtract_def)
   apply (simp_all add: lens_defs prod.case_eq_if fzero_subtract_def)
  nitpick
  by (unfold_locales, simp_all add: lens_defs prod.case_eq_if)*)

lemma itrace_mwb_lens [simp]: "mwb_lens \<^bold>i\<^bold>t"
  by (unfold_locales, simp_all add: lens_defs prod.case_eq_if)
    
syntax
  "_svid_tcontr"  :: "svid" ("tt")
  "_svid_itrace"  :: "svid" ("\<^bold>i\<^bold>t")

translations
  "_svid_tcontr" == "CONST tcontr"
  "_svid_itrace" == "CONST itrace"
  
lemma tcontr_alt_def: "&tt = ($tr\<acute> - $tr)"
  by (rel_auto)

lemma tcontr_alt_def': "utp_expr.var tt = ($tr\<acute> - $tr)"
  by (rel_auto)

lemma tt_indeps [simp]:
  assumes "x \<bowtie> ($tr)\<^sub>v" "x \<bowtie> ($tr\<acute>)\<^sub>v"
  shows "x \<bowtie> tt" "tt \<bowtie> x"
  using assms
  by (unfold lens_indep_def, safe, simp_all add: tcontr_def, (metis lens_indep_get var_update_out)+)

end