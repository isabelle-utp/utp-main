(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_poly_binding.thy                                                 *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Typed Bindings *}

theory utp_poly_binding
imports 
  "../core/utp_binding"
  "../tactics/utp_rel_tac"
  utp_poly_var
  utp_poly_tac
begin

definition Rep_binding_ty :: 
  "'m WF_BINDING \<Rightarrow> ('a :: DEFINED, 'm :: VALUE) PVAR \<Rightarrow> 'a" ("\<langle>_\<rangle>\<^sub>*") where
"Rep_binding_ty b x = ProjU (\<langle>b\<rangle>\<^sub>b x\<down>)"

definition binding_upd_ty :: 
  "'m WF_BINDING \<Rightarrow>
   ('a :: DEFINED, 'm :: VALUE) PVAR \<Rightarrow>
   'a \<Rightarrow>
   'm WF_BINDING" where
"binding_upd_ty b x v = binding_upd b (x\<down>) (InjU v)"

nonterminal tbupdbinds and tbupdbind

syntax
  "_tbupdbind" :: "['a, 'a] => tbupdbind"               ("(2_ :=\<^sub>*/ _)")
  ""         :: "tbupdbind => tbupdbinds"               ("_")
  "_tbupdbinds":: "[tbupdbind, tbupdbinds] => tbupdbinds" ("_,/ _")
  "_TBUpdate"  :: "['a, tbupdbinds] => 'a"              ("_/'((_)')" [1000, 0] 900)

translations
  "_TBUpdate f (_tbupdbinds b bs)" == "_TBUpdate (_TBUpdate f b) bs"
  "f(x:=\<^sub>*y)" == "CONST binding_upd_ty f x y"

(* Note: ProjU (InjU v) effectively performs a cast and will yield v when applied
   to identical sound types. *)

lemma binding_upd_apply_ty [simp]: 
  fixes x :: "('a :: DEFINED , 'm :: VALUE) PVAR"
  and   y :: "('b :: DEFINED, 'm) PVAR"
  shows "\<langle>f(x:=\<^sub>*v)\<rangle>\<^sub>* y = (if (x\<down>)=(y\<down>) then ProjU (vcoerce (InjU v :: 'm) x\<down>) else \<langle>f\<rangle>\<^sub>* y)"
  by (auto simp add:Rep_binding_ty_def binding_upd_ty_def typing assms)

lemma binding_upd_upd_ty [simp]: 
  fixes x :: "('a :: DEFINED , 'm :: VALUE) PVAR"
  shows "f(x:=\<^sub>*y,x:=\<^sub>*z) = f(x:=\<^sub>*z)"
  by (simp add:binding_upd_ty_def)

lemma WF_REL_BINDING_binding_upd_ty [closure]:
  "\<lbrakk> b \<in> WF_REL_BINDING; x \<in> PUNDASHED \<rbrakk> \<Longrightarrow> b(x :=\<^sub>* v) \<in> WF_REL_BINDING"
  by (simp add:binding_upd_ty_def closure typing)

lemma Rep_WF_BINDING_ty_pvaux_defined [defined]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "pvaux x"
  shows "\<D> (\<langle>b\<rangle>\<^sub>* x)"
  by (auto intro:defined typing assms simp add:Rep_binding_ty_def)

(* Some useful simplifications *)

lemma binding_override_ty_UNDASHED [simp]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "x \<in> PUNDASHED"
  shows "\<langle>b \<oplus>\<^sub>b b' on D\<^sub>2\<rangle>\<^sub>* x = \<langle>b\<rangle>\<^sub>* x"
  apply (simp add:Rep_binding_ty_def)
  apply (metis DASHED_TWICE_dash_elim PVAR_VAR_PUNDASHED_UNDASHED UNDASHED_eq_dash_contra assms(2) override_on_def)
done

lemma binding_override_ty_dash [simp]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "x \<in> PUNDASHED"
  shows "\<langle>b \<oplus>\<^sub>b b' on D\<^sub>2\<rangle>\<^sub>* x\<acute> = \<langle>b\<rangle>\<^sub>* x\<acute>"
  apply (simp add:Rep_binding_ty_def)
  apply (metis PVAR_VAR_PUNDASHED_UNDASHED UNDASHED_not_DASHED assms(2) dash_DASHED_TWICE_elim override_on_def)
done

lemma binding_override_ty_dash_dash [simp]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "x \<in> PUNDASHED"
  shows "\<langle>b \<oplus>\<^sub>b b' on D\<^sub>2\<rangle>\<^sub>* x\<acute>\<acute> = \<langle>b'\<rangle>\<^sub>* x\<acute>\<acute>"
  apply (simp add:Rep_binding_ty_def)
  apply (metis (full_types) DASHED_dash_DASHED_TWICE PVAR_VAR_PUNDASHED_UNDASHED UNDASHED_dash_DASHED assms(2) override_on_def)
done

lemma binding_override_ty_left [simp]: 
  "x\<down> \<notin> vs \<Longrightarrow> \<langle>b1 \<oplus>\<^sub>b b2 on vs\<rangle>\<^sub>* x = \<langle>b1\<rangle>\<^sub>* x"
  by (simp add:Rep_binding_ty_def)

lemma binding_override_ty_right [simp]: 
  "x\<down> \<in> vs \<Longrightarrow> \<langle>b1 \<oplus>\<^sub>b b2 on vs\<rangle>\<^sub>* x = \<langle>b2\<rangle>\<^sub>* x"
  by (simp add:Rep_binding_ty_def)

lemma binding_equiv_ty_reduce_left [simp]:
  "\<lbrakk> x\<down> \<notin> vs \<rbrakk> \<Longrightarrow> b1(x :=\<^sub>* v) \<cong> b2 on vs \<longleftrightarrow> b1 \<cong> b2 on vs"
  by (simp add:binding_upd_ty_def typing defined)

lemma binding_equiv_ty_reduce_right [simp]:
  "\<lbrakk> x\<down> \<notin> vs \<rbrakk> \<Longrightarrow> b1 \<cong> b2(x :=\<^sub>* v) on vs \<longleftrightarrow> b1 \<cong> b2 on vs"
  by (auto simp add:binding_upd_ty_def typing defined)

lemma EvalP_UNREST_binding_upd_ty [evalp]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "vs \<sharp> P" "x\<down> \<in> vs"
  shows "\<lbrakk>P\<rbrakk>(b(x :=\<^sub>* v)) = \<lbrakk>P\<rbrakk>b"
  using assms
  by (simp add: binding_upd_ty_def eval UNREST_subset typing defined)

lemma binding_upd_ty_twist [intro]:
  assumes "x\<down> \<noteq> y\<down>"
  shows "b(x :=\<^sub>* e, y :=\<^sub>* f) = b(y :=\<^sub>* f, x :=\<^sub>* e)"
  using assms by (simp add:binding_upd_ty_def typing binding_upd_twist)

end