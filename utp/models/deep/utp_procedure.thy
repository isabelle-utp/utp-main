subsection \<open> Procedures \<close>

theory utp_procedure
imports utp_dvar
begin

type_synonym ('a, '\<alpha>) uproc = "'a \<Rightarrow> '\<alpha> hrel"

definition
  val_parm :: "('\<T> \<times> '\<alpha> \<times> '\<beta>) itself \<Rightarrow> ('a::two, '\<beta>) lvar \<Rightarrow> (('a \<Longrightarrow> '\<beta>) \<Rightarrow> '\<alpha> hrel)
               \<Rightarrow> (('a, '\<beta>) uexpr, '\<alpha>) uproc"
where [upred_defs]: "val_parm T x P = (\<lambda> v. (var\<^bsub>UTHY('\<T>, '\<alpha>)\<^esub> x \<bullet> (x ::=\<^bsub>UTHY('\<T>, '\<alpha>)\<^esub> v ;; P x)))"

definition
  val_parm_comp :: "('\<T> \<times> '\<alpha> \<times> '\<beta>) itself \<Rightarrow> ('a::two, '\<beta>) lvar \<Rightarrow> (('a \<Longrightarrow> '\<beta>) \<Rightarrow> ('b, '\<alpha>) uproc)
               \<Rightarrow> (('a, '\<beta>) uexpr \<times> 'b, '\<alpha>) uproc"
where [upred_defs]: "val_parm_comp T x P = (\<lambda> (u, v). (var\<^bsub>UTHY('\<T>, '\<alpha>)\<^esub> x \<bullet> (x ::=\<^bsub>UTHY('\<T>, '\<alpha>)\<^esub> u ;; P x v)))"

definition
  res_parm :: "('\<T> \<times> '\<alpha> \<times> '\<beta>) itself \<Rightarrow> ('a::two, '\<beta>) lvar \<Rightarrow> (('a \<Longrightarrow> '\<beta>) \<Rightarrow> '\<alpha> hrel)
               \<Rightarrow> (('a \<Longrightarrow> '\<beta>), '\<alpha>) uproc"
where [upred_defs]: "res_parm T x P = (\<lambda> y. (var\<^bsub>UTHY('\<T>, '\<alpha>)\<^esub> x \<bullet> (P x ;; y ::=\<^bsub>UTHY('\<T>, '\<alpha>)\<^esub> &x)))"

definition
  res_parm_comp :: "('\<T> \<times> '\<alpha> \<times> '\<beta>) itself \<Rightarrow> ('a::two, '\<beta>) lvar \<Rightarrow> (('a \<Longrightarrow> '\<beta>) \<Rightarrow> ('b, '\<alpha>) uproc)
               \<Rightarrow> (('a \<Longrightarrow> '\<beta>) \<times> 'b, '\<alpha>) uproc"
where [upred_defs]: "res_parm_comp T x P = (\<lambda> (u, v). (var\<^bsub>UTHY('\<T>, '\<alpha>)\<^esub> x \<bullet> (P x v ;; u ::=\<^bsub>UTHY('\<T>, '\<alpha>)\<^esub> &x)))"

definition
  vres_parm :: "('\<T> \<times> '\<alpha> \<times> '\<beta>) itself \<Rightarrow> ('a::two, '\<beta>) lvar \<Rightarrow> (('a \<Longrightarrow> '\<beta>) \<Rightarrow> '\<alpha> hrel)
               \<Rightarrow> (('a \<Longrightarrow> '\<beta>), '\<alpha>) uproc"
where [upred_defs]: "vres_parm T x P = (\<lambda> y. (var\<^bsub>UTHY('\<T>, '\<alpha>)\<^esub> x \<bullet> (x ::=\<^bsub>UTHY('\<T>, '\<alpha>)\<^esub> &y ;; P x ;; y ::=\<^bsub>UTHY('\<T>, '\<alpha>)\<^esub> &x)))"

definition
  vres_parm_comp :: "('\<T> \<times> '\<alpha> \<times> '\<beta>) itself \<Rightarrow> ('a::two, '\<beta>) lvar \<Rightarrow> (('a \<Longrightarrow> '\<beta>) \<Rightarrow> ('b, '\<alpha>) uproc)
               \<Rightarrow> (('a \<Longrightarrow> '\<beta>) \<times> 'b, '\<alpha>) uproc"
where [upred_defs]: "vres_parm_comp T x P = (\<lambda> (u, v). (var\<^bsub>UTHY('\<T>, '\<alpha>)\<^esub> x \<bullet> (x ::=\<^bsub>UTHY('\<T>, '\<alpha>)\<^esub> &u ;; P x v ;; u ::=\<^bsub>UTHY('\<T>, '\<alpha>)\<^esub> &x)))"

nonterminal parm and parm_list

syntax
  "_uvar_ty"      :: "type \<Rightarrow> type"
  "_parm"         :: "parm \<Rightarrow> parm_list" ("(_)")
  "_parm_list"    :: "parm \<Rightarrow> parm_list \<Rightarrow> parm_list" ("_ ,/ _")
  "_tparm"        :: "parm_list \<Rightarrow> logic" ("_")
  "_proc_block"   :: "logic \<Rightarrow> parm_list \<Rightarrow> logic \<Rightarrow> ('a, '\<alpha>) uproc" ("_ \<bullet>\<index>/ _" [0,10] 10)
  "_val_parm"     :: "id \<Rightarrow> parm" ("val _" [999] 999)
  "_val_parm_ty"  :: "id \<Rightarrow> type \<Rightarrow> parm" ("val _ :: _")
  "_res_parm"     :: "id \<Rightarrow> parm" ("res _" [999] 999)
  "_res_parm_ty"  :: "id \<Rightarrow> type \<Rightarrow> parm" ("res _ :: _")
  "_vres_parm"    :: "id \<Rightarrow> parm" ("vres _" [999] 999)
  "_vres_parm_ty" :: "id \<Rightarrow> type \<Rightarrow> parm" ("vres _ :: _" [0,999] 999)

translations
  (* Parse translations for value parameters *)
  "_proc_block T (_parm (_val_parm x)) P" => "CONST val_parm T <x>\<^sub>d (\<lambda> x. P)"
  "_proc_block T (_parm (_val_parm_ty x a)) P" => "CONST val_parm T <x>\<^sub>d (_abs (_constrain x (_uvar_ty a)) P)"
  "_proc_block T (_parm_list (_val_parm_ty x a) ps) P"
  => "CONST val_parm_comp T <x>\<^sub>d (_abs (_constrain x (_uvar_ty a)) (_proc_block T ps P))"
  "_proc_block T (_parm_list (_val_parm x) ps) P"
  => "CONST val_parm_comp T <x>\<^sub>d (\<lambda> x. (_proc_block T ps P))"
  (* Parse translations for result parameters *)
  "_proc_block T (_parm (_res_parm x)) P" => "CONST res_parm T <x>\<^sub>d (\<lambda> x. P)"
  "_proc_block T (_parm (_res_parm_ty x a)) P" => "CONST res_parm T <x>\<^sub>d (_abs (_constrain x (_uvar_ty a)) P)"
  "_proc_block T (_parm_list (_res_parm_ty x a) ps) P"
  => "CONST res_parm_comp T <x>\<^sub>d (_abs (_constrain x (_uvar_ty a)) (_proc_block T ps P))"
  "_proc_block T (_parm_list (_res_parm x) ps) P"
  => "CONST res_parm_comp T <x>\<^sub>d (\<lambda> x. (_proc_block T ps P))"
  (* Parse translations for value-result parameters *)
  "_proc_block T (_parm (_vres_parm x)) P" => "CONST vres_parm T <x>\<^sub>d (\<lambda> x. P)"
  "_proc_block T (_parm (_vres_parm_ty x a)) P" => "CONST vres_parm T <x>\<^sub>d (_abs (_constrain x (_uvar_ty a)) P)"
  "_proc_block T (_parm_list (_vres_parm_ty x a) ps) P"
  => "CONST vres_parm_comp T <x>\<^sub>d (_abs (_constrain x (_uvar_ty a)) (_proc_block T ps P))"
  "_proc_block T (_parm_list (_res_parm x) ps) P"
  => "CONST vres_parm_comp T <x>\<^sub>d (\<lambda> x. (_proc_block T ps P))"

context utp_local_var
begin

lemma val_parm_healthy [closure]:
  fixes x :: "('a::two, '\<beta>) lvar"
  assumes "\<And> x. P x is \<H>"
  shows "val_parm (T :: ('\<T> \<times> '\<alpha> \<times> '\<beta>) itself) x P v is \<H>"
  by (simp add: val_parm_def uthy_simp closure assms)

lemma val_parm_comp_healthy [closure]:
  fixes x :: "('a::two, '\<beta>) lvar"
  assumes "\<And> x y. P x y is \<H>"
  shows "val_parm_comp (T :: ('\<T> \<times> '\<alpha> \<times> '\<beta>) itself) x P v is \<H>"
  by (simp add: val_parm_comp_def uthy_simp prod.case_eq_if closure assms)

end

(*
context utp_local_var
begin

declare [[show_types]]
declare [[show_sorts]]

term "val_parm (MkDVar ''x'')"

term "val x :: real \<bullet> P"

lemma val_parm_apply [simp]:
  "val_parm \<T> x P v = (var x \<bullet> (P x)\<lbrakk>\<lceil>v\<rceil>\<^sub></$x\<rbrakk>)"
 apply (simp add: assigns_r_comp  subst_lift_upd val_parm_def)

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
*)
end