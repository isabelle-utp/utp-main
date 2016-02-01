subsection {* Procedures *}

theory utp_procedure
imports utp_rel utp_dvar utp_designs
begin

subsection {* Variable blocks and constant parameters *}

text {* Procedures are based solely on deep variables since shallow variables cannot be dynamically created *}

definition var_block :: 
  "string \<Rightarrow> 
   (('a :: continuum) dvar \<Rightarrow> ('\<alpha>::vst, '\<alpha>) relation) \<Rightarrow> 
   ('\<alpha>, '\<alpha>) relation"
where "var_block x P = 
  (let v = mk_dvar x; u = (v\<up> :: ('a, '\<alpha>) uvar) in \<exists> $u \<bullet> \<exists> $u\<acute> \<bullet> P v)"

definition
  cnt_parm :: "('a \<Rightarrow> ('\<alpha>, '\<beta>) relation) \<Rightarrow> 'a \<Rightarrow> ('\<alpha>, '\<beta>) relation"
where "cnt_parm P = (\<lambda> x. P(x))"

syntax
  "_var_block" :: "id \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" ("var _ \<bullet>/ _" [0,999] 999)
  "_var_block_ty" :: "id \<Rightarrow> type \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" ("var _ :: _ \<bullet>/ _" [0,999] 999)
  "_cnt_block"     :: "id \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" ("cnt _ \<bullet>/ _" [0,999] 999)
  "_cnt_block_ty"  :: "id \<Rightarrow> type \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" ("cnt _ :: _ \<bullet>/ _" [0,0,999] 999)

translations
  "var x \<bullet> P" => "CONST var_block IDSTR(x) (\<lambda> x. P)"
  "var x :: 'a \<bullet> P" => "CONST var_block IDSTR(x) (\<lambda> x :: 'a dvar. P)"
  "var x \<bullet> P" <= "CONST var_block z (\<lambda> x. P)"
  "cnt x \<bullet> P" == "CONST cnt_parm (\<lambda> x. P)"
  "cnt x :: 'a \<bullet> P" == "CONST cnt_parm (\<lambda> x :: 'a. P)"

declare var_block_def [urel_defs]
declare cnt_parm_def [urel_defs]
  
subsection {* Relational procedures *}

type_synonym ('a, '\<alpha>) uproc = "'a \<Rightarrow> '\<alpha> hrelation"

definition 
  val_parm :: "string \<Rightarrow> ('a::continuum dvar \<Rightarrow> '\<alpha>::vst hrelation) 
               \<Rightarrow> ('a, '\<alpha>) uproc"
where "val_parm x P = (\<lambda> v. (var_block x (\<lambda> x. x := \<guillemotleft>v\<guillemotright> ;; P x)))"

definition 
  val_parm_comp :: "string \<Rightarrow> ('a::continuum dvar \<Rightarrow> ('b, '\<alpha>::vst) uproc) 
               \<Rightarrow> ('a \<times> 'b, '\<alpha>) uproc"
where "val_parm_comp x P = (\<lambda> (u, v). (var_block x (\<lambda> x. x := \<guillemotleft>u\<guillemotright> ;; P x v)))"

definition 
  res_parm :: "string \<Rightarrow> ('a::continuum dvar \<Rightarrow> '\<alpha>::vst hrelation) 
               \<Rightarrow> (('a, '\<alpha>) uvar, '\<alpha>) uproc"
where "res_parm x P = (\<lambda> y. (var_block x (\<lambda> x. P x ;; y := &x)))"

definition 
  res_parm_comp :: "string \<Rightarrow> ('a::continuum dvar \<Rightarrow> ('b, '\<alpha>::vst) uproc) 
               \<Rightarrow> (('a, '\<alpha>) uvar \<times> 'b, '\<alpha>) uproc"
where "res_parm_comp x P = (\<lambda> (u, v). (var_block x (\<lambda> x. P x v ;; u := &x)))"

definition 
  vres_parm :: "string \<Rightarrow> ('a::continuum dvar \<Rightarrow> '\<alpha>::vst hrelation) 
               \<Rightarrow> (('a, '\<alpha>) uvar, '\<alpha>) uproc"
where "vres_parm x P = (\<lambda> y. (var_block x (\<lambda> x. x := &y ;; P x ;; y := &x)))"

definition 
  vres_parm_comp :: "string \<Rightarrow> ('a::continuum dvar \<Rightarrow> ('b, '\<alpha>::vst) uproc) 
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
  "_proc_block (_parm (_val_parm x)) P" => "CONST val_parm IDSTR(x) (\<lambda> x. P)"
  "_proc_block (_parm (_val_parm_ty x a)) P" => "CONST val_parm IDSTR(x) (_abs (_constrain x (_uvar_ty a)) P)"
  "_proc_block (_parm_list (_val_parm_ty x a) ps) P" 
  => "CONST val_parm_comp IDSTR(x) (_abs (_constrain x (_uvar_ty a)) (_proc_block ps P))"
  "_proc_block (_parm_list (_val_parm x) ps) P" 
  => "CONST val_parm_comp IDSTR(x) (\<lambda> x. (_proc_block ps P))"
  (* Parse translations for result parameters *)
  "_proc_block (_parm (_res_parm x)) P" => "CONST res_parm IDSTR(x) (\<lambda> x. P)"
  "_proc_block (_parm (_res_parm_ty x a)) P" => "CONST res_parm IDSTR(x) (_abs (_constrain x (_uvar_ty a)) P)"
  "_proc_block (_parm_list (_res_parm_ty x a) ps) P" 
  => "CONST res_parm_comp IDSTR(x) (_abs (_constrain x (_uvar_ty a)) (_proc_block ps P))"
  "_proc_block (_parm_list (_res_parm x) ps) P" 
  => "CONST res_parm_comp IDSTR(x) (\<lambda> x. (_proc_block ps P))"
  (* Parse translations for value-result parameters *)
  "_proc_block (_parm (_vres_parm x)) P" => "CONST vres_parm IDSTR(x) (\<lambda> x. P)"
  "_proc_block (_parm (_vres_parm_ty x a)) P" => "CONST vres_parm IDSTR(x) (_abs (_constrain x (_uvar_ty a)) P)"
  "_proc_block (_parm_list (_vres_parm_ty x a) ps) P" 
  => "CONST vres_parm_comp IDSTR(x) (_abs (_constrain x (_uvar_ty a)) (_proc_block ps P))"
  "_proc_block (_parm_list (_res_parm x) ps) P" 
  => "CONST vres_parm_comp IDSTR(x) (\<lambda> x. (_proc_block ps P))"

lemma val_parm_apply [simp]: 
  "val_parm x P v = var_block x (\<lambda> x. x := \<guillemotleft>v\<guillemotright> ;; P x)"
  by (simp add: val_parm_def)

lemma val_parm_comp_apply [simp]: 
  "(val_parm_comp x P) (u, v) = var_block x (\<lambda> x. x := \<guillemotleft>u\<guillemotright> ;; P x v)"
  by (simp add: val_parm_comp_def)

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
