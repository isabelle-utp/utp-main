subsection {* Variable blocks *}

theory utp_local
imports utp_theory
begin

text {* Local variables are represented as lenses whose view type is a list of values. A variable
  therefore effectively records the stack of values that variable has had, if any. This allows
  us to denote variable scopes using assignments that push and pop this stack to add or delete
  a particular local variable. *}

type_synonym ('a, '\<alpha>) lvar = "('a list \<Longrightarrow> '\<alpha>)"

text {* Different UTP theories have different assignment operators; consequently in order to
  generically characterise variable blocks we need to abstractly characterise assignments.
  We first create two polymorphic constants that characterise the underlying program state model
  of a UTP theory. *}

consts
  pvar         :: "('\<T>, '\<alpha>) uthy \<Rightarrow> '\<beta> \<Longrightarrow> '\<alpha>" ("\<^bold>v\<index>")
  pvar_assigns :: "('\<T>, '\<alpha>) uthy \<Rightarrow> '\<beta> usubst \<Rightarrow> '\<alpha> hrel" ("\<^bold>\<langle>_\<^bold>\<rangle>\<index>")

text {* @{const pvar} is a lens from the program state, @{typ "'\<beta>"}, to the overall global state
  @{typ "'\<alpha>"}, which also contains none user-space information, such as observational variables.
  @{const pvar_assigns} takes as parameter a UTP theory and returns an assignment operator
  which maps a substitution over the program state to a homogeneous relation on the global
  state. We now set up some syntax translations for these operators. *}

syntax
  "_svid_pvar" :: "('\<T>, '\<alpha>) uthy \<Rightarrow> svid" ("\<^bold>v\<index>")
  "_thy_asgn"  :: "('\<T>, '\<alpha>) uthy \<Rightarrow> svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr "::=\<index>" 72)

translations
  "_svid_pvar T" => "CONST pvar T"
  "_thy_asgn T xs vs" => "CONST pvar_assigns T (_mk_usubst (CONST id) xs vs)"

text {* Next, we define constants to represent the top most variable on the local variable stack,
  and the remainder after this. We define these in terms of the list lens, and so for each
  another lens is produced. *}

definition top_var :: "('a::two, '\<alpha>) lvar \<Rightarrow> ('a \<Longrightarrow> '\<alpha>)" where
[upred_defs]: "top_var x = (list_lens 0 ;\<^sub>L x)"

text {* The remainder of the local variable stack (the tail) *}

definition rest_var :: "('a::two, '\<alpha>) lvar \<Rightarrow> ('a list \<Longrightarrow> '\<alpha>)" where
[upred_defs]: "rest_var x = (tl_lens ;\<^sub>L x)"

text {* We can show that the top variable is a mainly well-behaved lense, and that the top most
  variable lens is independent of the rest of the stack. *}

lemma top_mwb_lens [simp]: "mwb_lens x \<Longrightarrow> mwb_lens (top_var x)"
  by (simp add: list_mwb_lens top_var_def)

lemma top_rest_var_indep [simp]:
  "mwb_lens x \<Longrightarrow> top_var x \<bowtie> rest_var x"
  by (simp add: lens_indep_left_comp rest_var_def top_var_def)

lemma top_var_pres_indep [simp]:
  "x \<bowtie> y \<Longrightarrow> top_var x \<bowtie> y"
  by (simp add: lens_indep_left_ext top_var_def)

syntax
  "_top_var"             :: "svid \<Rightarrow> svid" ("@_" [999] 999)
  "_rest_var"            :: "svid \<Rightarrow> svid" ("\<down>_" [999] 999)

translations
  "_top_var x" == "CONST top_var x"
  "_rest_var x" == "CONST rest_var x"

text {* With operators to represent local variables, assignments, and stack manipulation defined,
  we can go about defining variable blocks themselves. *}

definition var_begin :: "('\<T>, '\<alpha>) uthy \<Rightarrow> ('a, '\<beta>) lvar \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "var_begin T x = x ::=\<^bsub>T\<^esub> \<langle>\<guillemotleft>undefined\<guillemotright>\<rangle> ^\<^sub>u &x"

definition var_end :: "('\<T>, '\<alpha>) uthy \<Rightarrow> ('a, '\<beta>) lvar \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "var_end T x = (x ::=\<^bsub>T\<^esub> tail\<^sub>u(&x))"

text {* @{const var_begin} takes as parameters a UTP theory and a local variable, and uses the
  theory assignment operator to push and undefined value onto the variable stack. @{const var_end}
  removes the top most variable from the stack in a similar way. *}

definition var_vlet :: "('\<T>, '\<alpha>) uthy \<Rightarrow> ('a, '\<alpha>) lvar \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "var_vlet T x = (($x \<noteq>\<^sub>u \<langle>\<rangle>) \<and> \<I>\<I>\<^bsub>T\<^esub>)"

text {* Next we set up the typical UTP variable block syntax, though with a suitable subscript index
  to represent the UTP theory parameter. *}

syntax
  "_var_begin"     :: "logic \<Rightarrow> svid \<Rightarrow> logic" ("var\<index> _" [100] 100)
  "_var_begin_asn" :: "logic \<Rightarrow> svid \<Rightarrow> logic \<Rightarrow> logic" ("var\<index> _ := _")
  "_var_end"       :: "logic \<Rightarrow> svid \<Rightarrow> logic" ("end\<index> _" [100] 100)
  "_var_vlet"      :: "logic \<Rightarrow> svid \<Rightarrow> logic" ("vlet\<index> _" [100] 100)
  "_var_scope"           :: "logic \<Rightarrow> svid \<Rightarrow> logic \<Rightarrow> logic" ("var\<index> _ \<bullet> _" [0,10] 10)
  "_var_scope_ty"        :: "logic \<Rightarrow> svid \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic" ("var\<index> _ :: _ \<bullet> _" [0,0,10] 10)
  "_var_scope_ty_assign" :: "logic \<Rightarrow> svid \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("var\<index> _ :: _ := _ \<bullet> _" [0,0,0,10] 10)

translations
  "_var_begin T x"       == "CONST var_begin T x"
  "_var_begin_asn T x e" => "var\<^bsub>T\<^esub> x ;; @x ::=\<^bsub>T\<^esub> e"
  "_var_end T x"         == "CONST var_end T x"
  "_var_vlet T x"        == "CONST var_vlet T x"
  "var\<^bsub>T\<^esub> x \<bullet> P" => "var\<^bsub>T\<^esub> x ;; ((\<lambda> x. P) (CONST top_var x)) ;; end\<^bsub>T\<^esub> x"
  "var\<^bsub>T\<^esub> x \<bullet> P" => "var\<^bsub>T\<^esub> x ;; ((\<lambda> x. P) (CONST top_var x)) ;; end\<^bsub>T\<^esub> x"

text {* In order to substantiate standard variable block laws, we need some underlying laws about
  assignments, which is the purpose of the following locales. *}

locale utp_prog_var = utp_theory \<T> for \<T> :: "('\<T>, '\<alpha>) uthy" (structure) +
  fixes \<V>\<T> :: "'\<beta> itself"
  assumes pvar_uvar: "vwb_lens (\<^bold>v :: '\<beta> \<Longrightarrow> '\<alpha>)"
  and Healthy_pvar_assigns [closure]: "\<^bold>\<langle>\<sigma> :: '\<beta> usubst\<^bold>\<rangle> is \<H>"
  and pvar_assigns_comp: "(\<^bold>\<langle>\<sigma>\<^bold>\<rangle> ;; \<^bold>\<langle>\<rho>\<^bold>\<rangle>) = \<^bold>\<langle>\<rho> \<circ> \<sigma>\<^bold>\<rangle>"

text {* We require that (1) the user-space variable is a very well-behaved lens, (2) that the
  assignment operator is healthy, and (3) that composing two assignments is equivalent to
  composing their substitutions. The next locale extends this with a left unit. *}

locale utp_local_var = utp_prog_var \<T> V + utp_theory_left_unital \<T> for \<T> :: "('\<T>, '\<alpha>) uthy" (structure) and V :: "'\<beta> itself" +
  assumes pvar_assign_unit: "\<^bold>\<langle>id :: '\<beta> usubst\<^bold>\<rangle> = \<I>\<I>"
begin

text {* If a left unit exists then an assignment with an identity substitution should yield the
  identity relation, as the above assumption requires. With these laws available, we can
  prove the main laws of variable blocks. *}

lemma var_begin_healthy [closure]:
  fixes x :: "('a, '\<beta>) lvar"
  shows "var x is \<H>"
  by (simp add: var_begin_def Healthy_pvar_assigns)

lemma var_end_healthy [closure]:
  fixes x :: "('a, '\<beta>) lvar"
  shows "end x is \<H>"
  by (simp add: var_end_def Healthy_pvar_assigns)

text {* The beginning and end of a variable block are both healthy theory elements. *}

lemma var_open_close:
  fixes x :: "('a, '\<beta>) lvar"
  assumes "vwb_lens x"
  shows "(var x ;; end x) = \<I>\<I>"
  by (simp add: var_begin_def var_end_def shEx_lift_seq_1 Healthy_pvar_assigns pvar_assigns_comp pvar_assign_unit usubst assms)

text {* Opening and then immediately closing a variable blocks yields a skip. *}
    
lemma var_open_close_commute:
  fixes x :: "('a, '\<beta>) lvar" and y :: "('b, '\<beta>) lvar"
  assumes "vwb_lens x" "vwb_lens y" "x \<bowtie> y"
  shows "(var x ;; end y) = (end y ;; var x)"
  by (simp add: var_begin_def var_end_def shEx_lift_seq_1 shEx_lift_seq_2
                Healthy_pvar_assigns pvar_assigns_comp
                assms usubst unrest  lens_indep_sym, simp add: assms usubst_upd_comm)

text {* The beginning and end of variable blocks from different variables commute. *}

lemma var_block_vacuous:
  fixes x :: "('a::two, '\<beta>) lvar"
  assumes "vwb_lens x"
  shows "(var x \<bullet> \<I>\<I>) = \<I>\<I>"
  by (simp add: Left_Unit assms var_end_healthy var_open_close)

text {* A variable block with a skip inside results in a skip. *}
end

text {* Example instantiation for the theory of relations *}

overloading
  rel_pvar == "pvar :: (REL, '\<alpha>) uthy \<Rightarrow> '\<alpha> \<Longrightarrow> '\<alpha>"
  rel_pvar_assigns == "pvar_assigns :: (REL, '\<alpha>) uthy \<Rightarrow> '\<alpha> usubst \<Rightarrow> '\<alpha> hrel"
begin
  definition rel_pvar :: "(REL, '\<alpha>) uthy \<Rightarrow> '\<alpha> \<Longrightarrow> '\<alpha>" where
  [upred_defs]: "rel_pvar T = 1\<^sub>L"
  definition rel_pvar_assigns :: "(REL, '\<alpha>) uthy \<Rightarrow> '\<alpha> usubst \<Rightarrow> '\<alpha> hrel" where
  [upred_defs]: "rel_pvar_assigns T \<sigma> = \<langle>\<sigma>\<rangle>\<^sub>a"
end

interpretation rel_local_var: utp_local_var "UTHY(REL, '\<alpha>)" "TYPE('\<alpha>)"
proof -
  interpret vw: vwb_lens "pvar REL :: '\<alpha> \<Longrightarrow> '\<alpha>"
    by (simp add: rel_pvar_def id_vwb_lens)
  show "utp_local_var TYPE('\<alpha>) UTHY(REL, '\<alpha>)"
  proof
    show "\<And>\<sigma>::'\<alpha> \<Rightarrow> '\<alpha>. \<^bold>\<langle>\<sigma>\<^bold>\<rangle>\<^bsub>REL\<^esub> is \<H>\<^bsub>REL\<^esub>"
      by (simp add: rel_pvar_assigns_def rel_hcond_def Healthy_def)
    show "\<And>(\<sigma>::'\<alpha> \<Rightarrow> '\<alpha>) \<rho>. \<^bold>\<langle>\<sigma>\<^bold>\<rangle>\<^bsub>UTHY(REL, '\<alpha>)\<^esub> ;; \<^bold>\<langle>\<rho>\<^bold>\<rangle>\<^bsub>REL\<^esub> = \<^bold>\<langle>\<rho> \<circ> \<sigma>\<^bold>\<rangle>\<^bsub>REL\<^esub>"
      by (simp add: rel_pvar_assigns_def assigns_comp)
    show "\<^bold>\<langle>id::'\<alpha> \<Rightarrow> '\<alpha>\<^bold>\<rangle>\<^bsub>UTHY(REL, '\<alpha>)\<^esub> = \<I>\<I>\<^bsub>REL\<^esub>"
      by (simp add: rel_pvar_assigns_def rel_unit_def skip_r_def)
  qed
qed
end