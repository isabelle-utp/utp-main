subsection {* Procedures *}

theory utp_procedure
imports utp_rel utp_dvar utp_designs utp_local
begin

type_synonym ('a, '\<alpha>) uproc = "'a \<Rightarrow> '\<alpha> hrelation"

definition 
  val_parm :: "('a::two, '\<alpha>) lvar \<Rightarrow> (('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> hrelation) 
               \<Rightarrow> (('a, '\<alpha>) uexpr, '\<alpha>) uproc"
where "val_parm x P = (\<lambda> v. (var x \<bullet> (x := v ;; P x)))"

definition 
  val_parm_comp :: "('a::two, '\<alpha>) lvar \<Rightarrow> (('a, '\<alpha>) uvar \<Rightarrow> ('b, '\<alpha>) uproc) 
               \<Rightarrow> (('a, '\<alpha>) uexpr \<times> 'b, '\<alpha>) uproc"
where "val_parm_comp x P = (\<lambda> (u, v). (var x \<bullet> (x := u ;; P x v)))"

definition 
  res_parm :: "('a::two, '\<alpha>) lvar \<Rightarrow> (('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> hrelation) 
               \<Rightarrow> (('a, '\<alpha>) uvar, '\<alpha>) uproc"
where "res_parm x P = (\<lambda> y. (var x \<bullet> (P x ;; y := &x)))"

definition 
  res_parm_comp :: "('a::two, '\<alpha>) lvar \<Rightarrow> (('a, '\<alpha>) uvar \<Rightarrow> ('b, '\<alpha>) uproc) 
               \<Rightarrow> (('a, '\<alpha>) uvar \<times> 'b, '\<alpha>) uproc"
where "res_parm_comp x P = (\<lambda> (u, v). (var x \<bullet> (P x v ;; u := &x)))"

definition
  vres_parm :: "('a::two, '\<alpha>) lvar \<Rightarrow> (('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> hrelation) 
               \<Rightarrow> (('a, '\<alpha>) uvar, '\<alpha>) uproc"
where "vres_parm x P = (\<lambda> y. (var x \<bullet> (x := &y ;; P x ;; y := &x)))"

definition 
  vres_parm_comp :: "('a::two, '\<alpha>) lvar \<Rightarrow> (('a, '\<alpha>) uvar \<Rightarrow> ('b, '\<alpha>) uproc) 
               \<Rightarrow> (('a, '\<alpha>) uvar \<times> 'b, '\<alpha>) uproc"
where "vres_parm_comp x P = (\<lambda> (u, v). (var x \<bullet> (x := &u ;; P x v ;; u := &x)))"

nonterminal parm and parm_list

syntax
  "_uvar_ty"      :: "type \<Rightarrow> type"
  "_parm"         :: "parm \<Rightarrow> parm_list" ("(_)")
  "_parm_list"    :: "parm \<Rightarrow> parm_list \<Rightarrow> parm_list" ("_ ,/ _")
  "_tparm"        :: "parm_list \<Rightarrow> logic" ("_")
  "_proc_block"   :: "parm_list \<Rightarrow> logic \<Rightarrow> ('a, '\<alpha>) uproc" ("_ \<bullet>/ _" [0,10] 10)
  "_val_parm"     :: "id \<Rightarrow> parm" ("val _" [999] 999)
  "_val_parm_ty"  :: "id \<Rightarrow> type \<Rightarrow> parm" ("val _ :: _")
  "_res_parm"     :: "id \<Rightarrow> parm" ("res _" [999] 999)
  "_res_parm_ty"  :: "id \<Rightarrow> type \<Rightarrow> parm" ("res _ :: _")
  "_vres_parm"    :: "id \<Rightarrow> parm" ("vres _" [999] 999)
  "_vres_parm_ty" :: "id \<Rightarrow> type \<Rightarrow> parm" ("vres _ :: _" [0,999] 999)

translations
  (* Parse translations for value parameters *)
  "_proc_block (_parm (_val_parm x)) P" => "CONST val_parm <x>\<^sub>d (\<lambda> x. P)"
  "_proc_block (_parm (_val_parm_ty x a)) P" => "CONST val_parm <x>\<^sub>d (_abs (_constrain x (_uvar_ty a)) P)"
  "_proc_block (_parm_list (_val_parm_ty x a) ps) P" 
  => "CONST val_parm_comp <x>\<^sub>d (_abs (_constrain x (_uvar_ty a)) (_proc_block ps P))"
  "_proc_block (_parm_list (_val_parm x) ps) P" 
  => "CONST val_parm_comp <x>\<^sub>d (\<lambda> x. (_proc_block ps P))"
  (* Parse translations for result parameters *)
  "_proc_block (_parm (_res_parm x)) P" => "CONST res_parm <x>\<^sub>d (\<lambda> x. P)"
  "_proc_block (_parm (_res_parm_ty x a)) P" => "CONST res_parm <x>\<^sub>d (_abs (_constrain x (_uvar_ty a)) P)"
  "_proc_block (_parm_list (_res_parm_ty x a) ps) P" 
  => "CONST res_parm_comp <x>\<^sub>d (_abs (_constrain x (_uvar_ty a)) (_proc_block ps P))"
  "_proc_block (_parm_list (_res_parm x) ps) P" 
  => "CONST res_parm_comp <x>\<^sub>d (\<lambda> x. (_proc_block ps P))"
  (* Parse translations for value-result parameters *)
  "_proc_block (_parm (_vres_parm x)) P" => "CONST vres_parm <x>\<^sub>d (\<lambda> x. P)"
  "_proc_block (_parm (_vres_parm_ty x a)) P" => "CONST vres_parm <x>\<^sub>d (_abs (_constrain x (_uvar_ty a)) P)"
  "_proc_block (_parm_list (_vres_parm_ty x a) ps) P" 
  => "CONST vres_parm_comp <x>\<^sub>d (_abs (_constrain x (_uvar_ty a)) (_proc_block ps P))"
  "_proc_block (_parm_list (_res_parm x) ps) P" 
  => "CONST vres_parm_comp <x>\<^sub>d (\<lambda> x. (_proc_block ps P))"

lemma val_parm_apply [simp]: 
  "val_parm x P v = (var x \<bullet> (P x)\<lbrakk>\<lceil>v\<rceil>\<^sub></$x\<rbrakk>)"
  by (simp add: assigns_r_comp subst_lift_id subst_lift_upd val_parm_def)

lemma val_parm_comp_apply:
  "(val_parm_comp x P) (u, v) = (var x \<bullet> (P x v)\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>)"
  by (simp add: assigns_r_comp subst_lift_id subst_lift_upd val_parm_comp_def)

lemma res_parm_apply [simp]: 
  "res_parm x P v = (var x \<bullet> P x ;; v := &x)"
  by (simp add: res_parm_def)

lemma res_parm_comp_apply [simp]: 
  "(res_parm_comp x P) (u, v) = (var x \<bullet> P x v ;; u := &x)"
  by (simp add: res_parm_comp_def)

lemma vres_parm_apply [simp]: 
  "vres_parm x P v = (var x \<bullet> x := &v ;; P x ;; v := &x)"
  by (simp add: vres_parm_def)

lemma vres_parm_comp_apply [simp]: 
  "(vres_parm_comp x P) (u, v) = (var x \<bullet> x := &u ;; P x v ;; u := &x)"
  by (simp add: vres_parm_comp_def)

text {* Instantiate vstore for design alphabets *}

instantiation alpha_d_ext :: (vst) vst
begin
  definition "vstore_lens_alpha_d_ext = \<V> ;\<^sub>L \<Sigma>\<^sub>D"
instance
  by (intro_classes, auto simp add: vstore_lens_alpha_d_ext_def comp_vwb_lens)
end

end
