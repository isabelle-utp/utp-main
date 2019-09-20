section \<open> Collections \<close>

theory utp_collection
  imports utp_rel_laws
begin

subsection \<open> Indexed Lenses \<close>

definition ind_lens :: "('i \<Rightarrow> ('a \<Longrightarrow> 's)) \<Rightarrow> ('i, 's) uexpr \<Rightarrow> ('a \<Longrightarrow> 's)" where
[lens_defs]: "ind_lens f x = \<lparr> lens_get = (\<lambda> s. get\<^bsub>f (\<lbrakk>x\<rbrakk>\<^sub>e s)\<^esub> s), lens_put = (\<lambda> s v. put\<^bsub>f (\<lbrakk>x\<rbrakk>\<^sub>e s)\<^esub> s v) \<rparr>"

lemma ind_lens_mwb [simp]: "\<lbrakk> \<And> i. mwb_lens (F i); \<And> i. unrest (F i) x \<rbrakk> \<Longrightarrow> mwb_lens (ind_lens F x)"
  by (unfold_locales, auto simp add: lens_defs lens_indep.lens_put_irr2 unrest_uexpr.rep_eq)

lemma ind_lens_vwb [simp]: "\<lbrakk> \<And> i. vwb_lens (F i); \<And> i. unrest (F i) x \<rbrakk> \<Longrightarrow> vwb_lens (ind_lens F x)"
  by (unfold_locales, auto simp add: lens_defs lens_indep.lens_put_irr2 unrest_uexpr.rep_eq)

subsection \<open> Overloaded Collection Lens \<close>

consts collection_lens :: "'k \<Rightarrow> ('a \<Longrightarrow> 's)"

definition [lens_defs]: "list_collection_lens = list_lens"

lemma vwb_list_collection_lens [simp]: "mwb_lens (list_collection_lens i)"
  by (simp add: list_collection_lens_def list_mwb_lens)

adhoc_overloading collection_lens list_collection_lens

subsection \<open> Syntax for Collection Lens \<close>

abbreviation "ind_lens_poly f x i \<equiv> ind_lens (\<lambda> k. f k ;\<^sub>L x) i"

utp_lift_notation ind_lens_poly (2)

syntax
  "_svid_collection" :: "svid \<Rightarrow> logic \<Rightarrow> svid" ("_[_]" [999, 0] 999)

translations
  "_svid_collection x i" == "CONST ind_lens_poly CONST collection_lens x i"

end
