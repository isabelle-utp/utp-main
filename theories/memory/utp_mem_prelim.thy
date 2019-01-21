section \<open> Memory Preliminaries \<close>

theory utp_mem_prelim
  imports 
    Partial_Monoids
    Partial_Monoids_Instances
    "UTP-Undef.utp_undef" 
    "Continuum.Lightweight_Cardinals"
    "UTP.utp_full"
begin recall_syntax

subsection \<open> State space \<close>

text \<open> As usual, the memory consists of the store and the heap. The store is an abstract
  type, and will usually be another alphabet. \<close>

alphabet 'h mem =
  hp :: "'h"

abbreviation str :: "'s \<Longrightarrow> ('a :: sep_alg, 's) mem_ext" where
"str \<equiv> mem.more\<^sub>L"

text \<open> We define an order on memory by lifting of the containment order on finite functions. \<close>

instantiation mem_ext :: (order, type) order
begin
  definition less_eq_mem_ext :: "('a, 'b) mem_scheme \<Rightarrow> ('a, 'b) mem_scheme \<Rightarrow> bool" where
  [upred_defs]: "less_eq_mem_ext x y = (hp\<^sub>v x \<le> hp\<^sub>v y \<and> mem.more x = mem.more y)"

  definition less_mem_ext :: "('a, 'b) mem_scheme \<Rightarrow> ('a, 'b) mem_scheme \<Rightarrow> bool" where
  [upred_defs]: "less_mem_ext x y = (hp\<^sub>v x < hp\<^sub>v y \<and> mem.more x = mem.more y)"

  instance by (intro_classes, (rel_auto)+)
end

text \<open> We set up some useful syntax \<close>

syntax
  "_ucompat" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "##\<^sub>u" 60)

translations
  "f ##\<^sub>u g" == "CONST bop (##) f g"

type_synonym ('h, 's) spred = "('h, 's) mem_ext upred"
type_synonym ('h, 's) sprog = "('h, 's) mem_ext hrel_des"

text \<open> For now we represent addresses and data as naturals. We can therefore inject
  countable data structures into our memory model. \<close>

type_synonym addr = nat
type_synonym data = nat

type_synonym 's mpred = "((addr, data) ffun, 's) spred"
type_synonym 's mprog = "((addr, data) ffun, 's) sprog"
type_synonym ('a, 's) mexpr = "('a, ((addr, data) ffun, 's) mem_ext) pexpr"

subsection \<open> Dereferencing Lens \<close>

definition ind_lens :: "('i \<Rightarrow> ('a \<Longrightarrow> 's)) \<Rightarrow> ('i \<Longrightarrow> 's) \<Rightarrow> ('a \<Longrightarrow> 's)" where
[lens_defs]: "ind_lens f x = \<lparr> lens_get = (\<lambda> s. get\<^bsub>f (get\<^bsub>x\<^esub> s)\<^esub> s), lens_put = (\<lambda> s v. put\<^bsub>f (get\<^bsub>x\<^esub> s)\<^esub> s v) \<rparr>"

lemma ind_lens_mwb [simp]: "\<lbrakk> \<And> i. mwb_lens (F i); \<And> i. (F i) \<bowtie> x \<rbrakk> \<Longrightarrow> mwb_lens (ind_lens F x)"
  by (unfold_locales, auto simp add: lens_defs lens_indep.lens_put_irr2)

lemma ind_lens_vwb [simp]: "\<lbrakk> \<And> i. vwb_lens (F i); \<And> i. (F i) \<bowtie> x \<rbrakk> \<Longrightarrow> vwb_lens (ind_lens F x)"
  by (unfold_locales, auto simp add: lens_defs lens_indep.lens_put_irr2)

text \<open> We first create a bijective lens that extracts a countable type from a natural number. \<close>

definition to_nat_lens :: "'a::{countable,infinite} \<Longrightarrow> nat" ("to-nat\<^sub>L") where
[lens_defs]: "to_nat_lens = \<lparr> lens_get = \<lambda> s. from_nat_bij s, lens_put = \<lambda> s v. to_nat_bij v \<rparr>"

lemma to_nat_lens_bij [simp]: "bij_lens to_nat_lens"
  by (unfold_locales, simp_all add: lens_defs)

text \<open> The dereferencing lens obtains the heap, applies the finite function lens with the given
  address, and finally obtains the typed data. \<close>

definition deref :: "(addr \<Longrightarrow> 's) \<Rightarrow> ('a::{countable,infinite} \<Longrightarrow> ((nat, nat) ffun, 's) mem_ext)" where
[lens_defs]: "deref a = to-nat\<^sub>L ;\<^sub>L ind_lens (\<lambda> i. ffun_lens i ;\<^sub>L hp) (a ;\<^sub>L str)"

syntax \<comment> \<open> Dereferencing Variable Identifier \<close>
  "_spderef"       :: "id \<Rightarrow> svid" ("*_")

translations
  "_spderef a" == "CONST deref a"

lemma src_deref: "vwb_lens a \<Longrightarrow> \<S>\<^bsub>deref a\<^esub> = {s. get\<^bsub>a ;\<^sub>L str\<^esub> s \<in> fdom(get\<^bsub>hp\<^esub> s)}"
  apply (simp add: deref_def source_lens_comp wb_lens.source_UNIV ffun_lens_src)
  apply (auto simp add: lens_defs lens_source_def)
  apply (metis ffun_upd_ext mem.surjective mem.update_convs(1))
  done

lemma src_pred_deref [simp]: "vwb_lens a \<Longrightarrow> \<^bold>S(deref a) = (&str:a \<in>\<^sub>u dom\<^sub>u(&hp))"
  by (simp add: src_pred_def src_deref, rel_auto)

end