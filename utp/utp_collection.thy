section \<open> Collections \<close>

theory utp_collection
  imports utp_lift_pretty utp_pred
begin

subsection \<open> Partial Lens Definedness \<close>

definition src_pred :: "('a \<Longrightarrow> 's) \<Rightarrow> 's upred" ("\<^bold>S'(_')") where
[upred_defs]: "src_pred x = (&\<^bold>v \<in>\<^sub>u \<guillemotleft>\<S>\<^bsub>x\<^esub>\<guillemotright>)"

lemma wb_lens_src_true [simp]: "wb_lens x \<Longrightarrow> \<^bold>S(x) = true"
  by (rel_simp, simp add: wb_lens.source_UNIV)
  
subsection \<open> Indexed Lenses \<close>

definition ind_lens :: "('i \<Rightarrow> ('a \<Longrightarrow> 's)) \<Rightarrow> ('i, 's) uexpr \<Rightarrow> ('a \<Longrightarrow> 's)" where
[lens_defs]: "ind_lens f x = \<lparr> lens_get = (\<lambda> s. get\<^bsub>f (\<lbrakk>x\<rbrakk>\<^sub>e s)\<^esub> s), lens_put = (\<lambda> s v. put\<^bsub>f (\<lbrakk>x\<rbrakk>\<^sub>e s)\<^esub> s v) \<rparr>"

lemma ind_lens_mwb [simp]: "\<lbrakk> \<And> i. mwb_lens (F i); \<And> i. unrest (F i) x \<rbrakk> \<Longrightarrow> mwb_lens (ind_lens F x)"
  by (unfold_locales, auto simp add: lens_defs lens_indep.lens_put_irr2 unrest_uexpr.rep_eq)

lemma ind_lens_vwb [simp]: "\<lbrakk> \<And> i. vwb_lens (F i); \<And> i. unrest (F i) x \<rbrakk> \<Longrightarrow> vwb_lens (ind_lens F x)"
  by (unfold_locales, auto simp add: lens_defs lens_indep.lens_put_irr2 unrest_uexpr.rep_eq)

lemma src_ind_lens: "\<lbrakk> \<And> i. unrest (f i) e \<rbrakk> \<Longrightarrow> \<S>\<^bsub>ind_lens f e\<^esub> = {s. s \<in> \<S>\<^bsub>f (\<lbrakk>e\<rbrakk>\<^sub>e s)\<^esub>}"
  apply (auto simp add: lens_defs lens_source_def unrest unrest_uexpr.rep_eq)
  apply (blast)
  apply metis
  done

(*
lemma "\<^bold>S(src_pred (ind_lens x = U(&x \<in> \<S>\<^bsub>x\<^esub>)"
*)

subsection \<open> Overloaded Collection Lens \<close>

consts collection_lens :: "'k \<Rightarrow> ('a \<Longrightarrow> 's)"

definition [lens_defs]: "fun_collection_lens = fun_lens"
definition [lens_defs]: "pfun_collection_lens = pfun_lens"
definition [lens_defs]: "ffun_collection_lens = ffun_lens"
definition [lens_defs]: "list_collection_lens = list_lens"

lemma vwb_fun_collection_lens [simp]: "vwb_lens (fun_collection_lens k)"
  by (simp add: fun_collection_lens_def fun_vwb_lens)

lemma mwb_pfun_collection_lens [simp]: "mwb_lens (pfun_collection_lens k)"
  by (simp add: pfun_collection_lens_def)

lemma mwb_ffun_collection_lens [simp]: "mwb_lens (ffun_collection_lens k)"
  by (simp add: ffun_collection_lens_def)

lemma mwb_list_collection_lens [simp]: "mwb_lens (list_collection_lens i)"
  by (simp add: list_collection_lens_def list_mwb_lens)

lemma source_list_collection_lens: "\<S>\<^bsub>list_collection_lens i\<^esub> = {xs. i < length xs}"
  by (simp add: list_collection_lens_def source_list_lens)

adhoc_overloading 
  collection_lens fun_collection_lens and
  collection_lens pfun_collection_lens and
  collection_lens ffun_collection_lens and
  collection_lens list_collection_lens  

subsection \<open> Syntax for Collection Lens \<close>

abbreviation "ind_lens_poly f x i \<equiv> ind_lens (\<lambda> k. f k ;\<^sub>L x) i"

utp_lift_notation ind_lens_poly (0 1)

syntax
  "_svid_collection" :: "svid \<Rightarrow> logic \<Rightarrow> svid" ("_[_]" [999, 0] 999)

translations
  "_svid_collection x i" == "CONST ind_lens_poly CONST collection_lens x i"

lemma src_list_collection_lens [simp]:
  "\<lbrakk> vwb_lens x; x \<sharp> i \<rbrakk> \<Longrightarrow> \<^bold>S(ind_lens_poly list_collection_lens x i) = U(i < length(&x))"
  apply (simp add: upred_defs src_ind_lens unrest source_list_collection_lens source_lens_comp)
  apply (transfer, auto simp add: fun_eq_iff lens_defs wb_lens.source_UNIV)
  done

end