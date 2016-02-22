subsection {* Procedures *}

theory utp_procedure
imports utp_rel utp_dvar utp_designs
begin

subsection {* (Pseudo) Variable scopes *}

text {* In our shallow embedding it is not possible to generically remove a variable from the
        alphabet, since we use the type system to approximate alphabets and this is beyond
        the type systems scope. As a result, our variable block operator abstract the variables
        but does not remove them from the alphabet. This means we can identify more predicates
        then perhaps we should. *}

definition var_open :: "('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> hrelation" ("var\<^sub>u") where
"var_open x = (\<exists> $x \<bullet> II)"

definition var_close :: "('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> hrelation" ("end\<^sub>u") where
"var_close x = (\<exists> $x\<acute> \<bullet> II)"

declare var_open_def [urel_defs] and var_close_def [urel_defs]

text {* An interesting, if slightly unsettling property provable as a consequence of not handling
        alphabets explicitly in var open/close. We can prove that opening and closing a scope
        is the same construct, which is true if you don't consider the alphabets. *}

lemma var_open_eq_var_close:
  assumes "uvar x"
  shows "var\<^sub>u x = end\<^sub>u x"
proof -
  have "var\<^sub>u x = (\<exists> $x \<bullet> II)"
    by (simp add: var_open_def)
  also have "... = (\<exists> $x \<bullet> $x =\<^sub>u $x\<acute> \<and> II\<restriction>\<^sub>\<alpha>x)"
    by (metis assms eq_upred_sym skip_r_unfold)
  also from assms have "... = (II\<restriction>\<^sub>\<alpha>x) \<lbrakk>$x\<acute>/$x\<rbrakk>"
    by (metis conj_comm in_var_uvar one_point unrest_iuvar_ouvar var_in_var)
  also from assms have "... = (II\<restriction>\<^sub>\<alpha>x) \<lbrakk>$x/$x\<acute>\<rbrakk>"
    by subst_tac
  also have "... = (\<exists> $x\<acute> \<bullet> $x\<acute> =\<^sub>u $x \<and> II\<restriction>\<^sub>\<alpha>x)"
    by (metis assms conj_comm one_point out_var_uvar unrest_out\<alpha>_var utp_rel.unrest_iuvar var_out_var)
  also have "... = (\<exists> $x\<acute> \<bullet> II)"
    using assms skip_r_unfold by fastforce
  also have "... = end\<^sub>u x"
    by (simp add: var_close_def)
  finally show ?thesis .
qed

lemma var_block_expand:
  assumes "uvar x"
  shows "(var\<^sub>u x ;; P ;; end\<^sub>u x) = (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P)"
  by (metis assms seqr_exists_left seqr_exists_right upred_quantale.mult.left_neutral upred_quantale.mult.right_neutral var_close_def var_open_def)

lemma var_open_twice:
  assumes "uvar x"
  shows "(var\<^sub>u x ;; var\<^sub>u x) = var\<^sub>u x"
proof -
  have "(var\<^sub>u x ;; var\<^sub>u x) = ((\<exists> $x \<bullet> II) ;; (\<exists> $x \<bullet> II))"
    by (rel_tac)
  also from assms have "... =  (\<exists> $x \<bullet> (II ;; (\<exists> $x \<bullet> II)))"
    using seqr_exists_left by blast
  also have "... = (\<exists> $x \<bullet> (\<exists> $x \<bullet> II))"
    by simp
  also from assms have "... = (\<exists> $x \<bullet> II)"
    by (simp add: exists_twice)
  finally show ?thesis
    by (simp add: var_open_def)
qed

lemma var_close_twice:
  assumes "uvar x"
  shows "(end\<^sub>u x ;; end\<^sub>u x) = end\<^sub>u x"
    by (simp add: assms exists_twice seqr_exists_right var_close_def)

lemma var_block_vacuous:
  assumes "uvar x"
  shows "(var\<^sub>u x ;; end\<^sub>u x) = II \<restriction>\<^sub>\<alpha> x"
  using assms by (simp add: rel_var_res_def seqr_exists_left var_close_def var_open_def)

lemma var_open_close_commute:
  assumes "uvar x" "uvar y" "x \<bowtie> y"
  shows "(var\<^sub>u x ;; end\<^sub>u y) = (end\<^sub>u y ;; var\<^sub>u x)"
  using assms
  by (simp add: ex_commute seqr_exists_right var_close_def var_open_eq_var_close)

lemma var_close_assign:
  assumes "uvar x" "x \<sharp> v"
  shows "(end\<^sub>u x ;; x := v) = (x := v)"
proof -
  have "(end\<^sub>u x ;; x := v) = ((\<exists> $x \<bullet> II) ;; (x := v))"
    by (metis assms(1) var_open_def var_open_eq_var_close)
  also have "... = (\<exists> $x \<bullet> (II ;; (x := v)))"
    by (simp add: assms(1) seqr_exists_left)
  also have "... = (\<exists> $x \<bullet> x := v)"
    by simp
  also have "... = (x := v)"
    by (metis assms(1) assms(2) exists_twice in_var_uvar one_point subst_skip_r unrest_pre_in_var)
  finally show ?thesis .
qed

lemma assign_var_close:
  assumes "uvar x"
  shows "(x := v ;; end\<^sub>u x) = end\<^sub>u x"
proof -
  from assms have "(x := v ;; end\<^sub>u x) = (\<exists> $x\<acute> \<bullet> x := v)"
    by (simp add: assigns_r_comp var_close_def usubst unrest)
  also have "... = (\<exists> $x\<acute> \<bullet> ($x\<acute> =\<^sub>u \<lceil>v\<rceil>\<^sub>< \<and> II\<restriction>\<^sub>\<alpha>x))"
    by (simp add: assign_unfold assms)
  also from assms have "... = (II\<restriction>\<^sub>\<alpha>x) \<lbrakk>\<lceil>v\<rceil>\<^sub></$x\<acute>\<rbrakk>"
    by (metis conj_comm one_point out_var_uvar unrest_out\<alpha>_var unrest_pre_out\<alpha> var_out_var)
  also from assms have "... = (II\<restriction>\<^sub>\<alpha>x)"
    by subst_tac
  also from assms have "... = (II\<restriction>\<^sub>\<alpha>x) \<lbrakk>$x/$x\<acute>\<rbrakk>"
    by subst_tac
  also have "... = (\<exists> $x\<acute> \<bullet> ($x\<acute> =\<^sub>u $x \<and> II\<restriction>\<^sub>\<alpha>x))"
    by (simp add: assms conj_comm one_point ouvar_def unrest_out\<alpha>_var utp_rel.unrest_iuvar)
  also from assms have "... = (\<exists> $x\<acute> \<bullet> II)"
    using skip_r_unfold by force
  also have "... = end\<^sub>u x"
    by (simp add: var_close_def)
  finally show ?thesis .
qed

subsection {* Variable blocks and constant parameters *}

text {* Procedures are based solely on deep variables since shallow variables cannot be dynamically created *}

definition var_block :: 
  "('a :: continuum) dvar \<Rightarrow> 
   ('a dvar \<Rightarrow> ('\<alpha>::vst, '\<alpha>) relation) \<Rightarrow> 
   ('\<alpha>, '\<alpha>) relation"
where "var_block x P = (var\<^sub>u (x\<up>) ;; P x ;; end\<^sub>u (x\<up>))"

definition
  cnt_parm :: "('a \<Rightarrow> ('\<alpha>, '\<beta>) relation) \<Rightarrow> 'a \<Rightarrow> ('\<alpha>, '\<beta>) relation"
where "cnt_parm P = (\<lambda> x. P(x))"

syntax
  "_var_block" :: "id \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" ("var _ \<bullet>/ _" [0,999] 999)
  "_var_block_ty" :: "id \<Rightarrow> type \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" ("var _ :: _ \<bullet>/ _" [0,999] 999)
  "_cnt_block"     :: "id \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" ("cnt _ \<bullet>/ _" [0,999] 999)
  "_cnt_block_ty"  :: "id \<Rightarrow> type \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" ("cnt _ :: _ \<bullet>/ _" [0,0,999] 999)

translations
  "var x \<bullet> P" => "CONST var_block \<lceil>IDSTR(x)\<rceil>\<^sub>d (\<lambda> x. P)"
  "var x :: 'a \<bullet> P" => "CONST var_block \<lceil>IDSTR(x)\<rceil>\<^sub>d (\<lambda> x :: 'a dvar. P)"
  "var x \<bullet> P" <= "CONST var_block z (\<lambda> x. P)"
  "cnt x \<bullet> P" == "CONST cnt_parm (\<lambda> x. P)"
  "cnt x :: 'a \<bullet> P" == "CONST cnt_parm (\<lambda> x :: 'a. P)"

declare var_block_def [urel_defs]
declare cnt_parm_def [urel_defs]

lemma subst_var_block: 
  fixes v :: "('a, '\<alpha> :: vst \<times> '\<alpha>) uexpr"
  and   x :: "'b::continuum dvar"
  assumes "x\<up> \<bowtie> y" "$x \<sharp> v" "$x\<acute> \<sharp> v"
  shows "(var_block x P)\<lbrakk>v/$y\<rbrakk> = var_block x (\<lambda> x :: 'b dvar. (P x)\<lbrakk>v/$y\<rbrakk>)"
  using assms
  by (simp add: var_block_def var_block_expand uvar_dvar usubst uvar_indep_sym)

subsection {* Relational procedures *}

type_synonym ('a, '\<alpha>) uproc = "'a \<Rightarrow> '\<alpha> hrelation"

definition 
  val_parm :: "'a dvar \<Rightarrow> ('a::continuum dvar \<Rightarrow> '\<alpha>::vst hrelation) 
               \<Rightarrow> (('a, '\<alpha>) uexpr, '\<alpha>) uproc"
where "val_parm x P = (\<lambda> v. (var_block x (\<lambda> x. x := v ;; P x)))"

definition 
  val_parm_comp :: "'a dvar \<Rightarrow> ('a::continuum dvar \<Rightarrow> ('b, '\<alpha>::vst) uproc) 
               \<Rightarrow> (('a, '\<alpha>) uexpr \<times> 'b, '\<alpha>) uproc"
where "val_parm_comp x P = (\<lambda> (u, v). (var_block x (\<lambda> x. x := u ;; P x v)))"

definition 
  res_parm :: "'a dvar \<Rightarrow> ('a::continuum dvar \<Rightarrow> '\<alpha>::vst hrelation) 
               \<Rightarrow> (('a, '\<alpha>) uvar, '\<alpha>) uproc"
where "res_parm x P = (\<lambda> y. (var_block x (\<lambda> x. P x ;; y := &x)))"

definition 
  res_parm_comp :: "'a dvar \<Rightarrow> ('a::continuum dvar \<Rightarrow> ('b, '\<alpha>::vst) uproc) 
               \<Rightarrow> (('a, '\<alpha>) uvar \<times> 'b, '\<alpha>) uproc"
where "res_parm_comp x P = (\<lambda> (u, v). (var_block x (\<lambda> x. P x v ;; u := &x)))"

definition 
  vres_parm :: "'a dvar \<Rightarrow> ('a::continuum dvar \<Rightarrow> '\<alpha>::vst hrelation) 
               \<Rightarrow> (('a, '\<alpha>) uvar, '\<alpha>) uproc"
where "vres_parm x P = (\<lambda> y. (var_block x (\<lambda> x. x := &y ;; P x ;; y := &x)))"

definition 
  vres_parm_comp :: "'a dvar \<Rightarrow> ('a::continuum dvar \<Rightarrow> ('b, '\<alpha>::vst) uproc) 
               \<Rightarrow> (('a, '\<alpha>) uvar \<times> 'b, '\<alpha>) uproc"
where "vres_parm_comp x P = (\<lambda> (u, v). (var_block x (\<lambda> x. x := &u ;; P x v ;; u := &x)))"

nonterminal parm and parm_list

syntax
  "_uvar_ty"      :: "type \<Rightarrow> type"
  "_parm"         :: "parm \<Rightarrow> parm_list" ("(_)")
  "_parm_list"    :: "parm \<Rightarrow> parm_list \<Rightarrow> parm_list" ("_ ,/ _")
  "_tparm"        :: "parm_list \<Rightarrow> logic" ("_")
  "_proc_block"   :: "parm_list \<Rightarrow> logic \<Rightarrow> ('a, '\<alpha>) uproc" ("_ \<bullet>/ _" [0,999] 999)
  "_val_parm"     :: "id \<Rightarrow> parm" ("val _" [999] 999)
  "_val_parm_ty"  :: "id \<Rightarrow> type \<Rightarrow> parm" ("val _ :: _")
  "_res_parm"     :: "id \<Rightarrow> parm" ("res _" [999] 999)
  "_res_parm_ty"  :: "id \<Rightarrow> type \<Rightarrow> parm" ("res _ :: _")
  "_vres_parm"    :: "id \<Rightarrow> parm" ("vres _" [999] 999)
  "_vres_parm_ty" :: "id \<Rightarrow> type \<Rightarrow> parm" ("vres _ :: _" [0,999] 999)

text {* We build a little function for constructing a uvar type given the result type *}

parse_translation {*
let
  fun uvar_ty_tr [ty] = Syntax.const @{type_syntax dvar} $ ty
    | uvar_ty_tr ts = raise TERM ("uvar_ty_tr", ts);
in [(@{syntax_const "_uvar_ty"}, K uvar_ty_tr)] end
*}

translations
  (* Parse translations for value parameters *)
  "_proc_block (_parm (_val_parm x)) P" => "CONST val_parm \<lceil>IDSTR(x)\<rceil>\<^sub>d (\<lambda> x. P)"
  "_proc_block (_parm (_val_parm_ty x a)) P" => "CONST val_parm \<lceil>IDSTR(x)\<rceil>\<^sub>d (_abs (_constrain x (_uvar_ty a)) P)"
  "_proc_block (_parm_list (_val_parm_ty x a) ps) P" 
  => "CONST val_parm_comp \<lceil>IDSTR(x)\<rceil>\<^sub>d (_abs (_constrain x (_uvar_ty a)) (_proc_block ps P))"
  "_proc_block (_parm_list (_val_parm x) ps) P" 
  => "CONST val_parm_comp \<lceil>IDSTR(x)\<rceil>\<^sub>d (\<lambda> x. (_proc_block ps P))"
  (* Parse translations for result parameters *)
  "_proc_block (_parm (_res_parm x)) P" => "CONST res_parm \<lceil>IDSTR(x)\<rceil>\<^sub>d (\<lambda> x. P)"
  "_proc_block (_parm (_res_parm_ty x a)) P" => "CONST res_parm \<lceil>IDSTR(x)\<rceil>\<^sub>d (_abs (_constrain x (_uvar_ty a)) P)"
  "_proc_block (_parm_list (_res_parm_ty x a) ps) P" 
  => "CONST res_parm_comp \<lceil>IDSTR(x)\<rceil>\<^sub>d (_abs (_constrain x (_uvar_ty a)) (_proc_block ps P))"
  "_proc_block (_parm_list (_res_parm x) ps) P" 
  => "CONST res_parm_comp \<lceil>IDSTR(x)\<rceil>\<^sub>d (\<lambda> x. (_proc_block ps P))"
  (* Parse translations for value-result parameters *)
  "_proc_block (_parm (_vres_parm x)) P" => "CONST vres_parm \<lceil>IDSTR(x)\<rceil>\<^sub>d (\<lambda> x. P)"
  "_proc_block (_parm (_vres_parm_ty x a)) P" => "CONST vres_parm \<lceil>IDSTR(x)\<rceil>\<^sub>d (_abs (_constrain x (_uvar_ty a)) P)"
  "_proc_block (_parm_list (_vres_parm_ty x a) ps) P" 
  => "CONST vres_parm_comp \<lceil>IDSTR(x)\<rceil>\<^sub>d (_abs (_constrain x (_uvar_ty a)) (_proc_block ps P))"
  "_proc_block (_parm_list (_res_parm x) ps) P" 
  => "CONST vres_parm_comp \<lceil>IDSTR(x)\<rceil>\<^sub>d (\<lambda> x. (_proc_block ps P))"

lemma val_parm_apply [simp]: 
  "val_parm x P v = var_block x (\<lambda> x. (P x)\<lbrakk>\<lceil>v\<rceil>\<^sub></$x\<rbrakk>)"
  by (simp add: val_parm_def var_block_def Let_def assign_r_comp uvar_dvar subst_upd_dvar_def)

lemma val_parm_comp_apply:
  "(val_parm_comp x P) (u, v) = var_block x (\<lambda> x. (P x v)\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>)"
  by (simp add: val_parm_comp_def var_block_def Let_def assign_r_comp uvar_dvar subst_upd_dvar_def)

lemma val_parm_apply_2 [simp]:
  fixes x y :: "'a::continuum dvar" and u :: "('a, '\<alpha>::vst) uexpr"
  assumes "(x\<up> :: ('a, '\<alpha>) uvar) \<bowtie> y\<up>" "unrest (x\<up>) v" "unrest (y\<up>) u"
  shows "val_parm_comp x (\<lambda> x. val_parm y (P x)) (u, v) = 
         var_block x (\<lambda> x. var_block y (\<lambda> y. (P x y)\<lbrakk>\<lceil>u\<rceil>\<^sub><,\<lceil>v\<rceil>\<^sub></$x,$y\<rbrakk>))"
  using assms
  by (simp add: val_parm_comp_apply var_block_def var_block_expand uvar_dvar usubst unrest uvar_indep_sym)

lemma res_parm_apply [simp]: 
  "res_parm x P v = var_block x (\<lambda> x. P x ;; v := &x)"
  by (simp add: res_parm_def)

lemma res_parm_comp_apply [simp]: 
  "(res_parm_comp x P) (u, v) = var_block x (\<lambda> x. P x v ;; u := &x)"
  by (simp add: res_parm_comp_def)

lemma vres_parm_apply [simp]: 
  "vres_parm x P v = var_block x (\<lambda> x. x := &v ;; P x ;; v := &x)"
  by (simp add: vres_parm_def)

lemma vres_parm_comp_apply [simp]: 
  "(vres_parm_comp x P) (u, v) = var_block x (\<lambda> x. x := &u ;; P x v ;; u := &x)"
  by (simp add: vres_parm_comp_def)

text {* Instantiate vstore for design alphabets *}

instantiation alpha_d_ext :: (vst) vst
begin
  definition [simp]: "get_vstore_alpha_d_ext x = get_vstore (more x)"
  definition [simp]: "upd_vstore_alpha_d_ext = more_update \<circ> upd_vstore"
instance
  by (intro_classes, auto simp add: upd_store_parm[THEN sym])
end

end
