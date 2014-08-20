(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_memory.thy                                                       *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* A Simple Memory Model *}

theory utp_memory
imports
  "../core/utp_model"
  "../poly/utp_poly_var"
begin

default_sort TYPED_MODEL

typedef ADDR = "UNIV :: nat set"
apply (rule UNIV_witness)
done

declare Abs_ADDR_inverse [simp]
declare Rep_ADDR_inverse [simp]
declare Rep_ADDR [simp]

text {* I think these assumptions only hold in @{class COUNTABLE_MODEL}s. *}

class ADDR_SORT =
  fixes MkAddr   :: "ADDR \<Rightarrow> 'a::TYPED_MODEL uval"
  fixes DestAddr :: "'a uval \<Rightarrow> ADDR"
  fixes AddrType :: "'a utype"
  fixes refs :: "'a uval \<Rightarrow> ADDR fset"
  assumes Inverse [simp] : "DestAddr (MkAddr x) = x"
  assumes AddrType_dcarrier : "dcarrier AddrType = range MkAddr"
-- {* Why is the following an axiom? It looks like a derived function. *}
  assumes refs_MkAddr : "refs (MkAddr x) = \<lbrace>x\<rbrace>"
begin

lemma Defined [defined] : "\<D>\<^sub>v (MkAddr i)"
  by (metis AddrType_dcarrier dcarrier_member range_eqI strict_type_rel_def)

lemma MkAddr_type [typing] : "MkAddr n : AddrType"
  by (metis AddrType_dcarrier dcarrier_member rangeI strict_type_rel_def)

lemma MkAddr_dtype [typing] : "MkAddr n :! AddrType"
  by (metis Defined MkAddr_type strict_type_rel_def)

lemma MkAddr_cases [elim] :
"x :! AddrType \<Longrightarrow> \<lbrakk>\<And> i . x = MkAddr i \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (metis AddrType_dcarrier dcarrier_member image_iff)

lemma MkAddr_inj_simp [simp] :
"(MkAddr x = MkAddr y) \<longleftrightarrow> x = y"
  by (metis Inverse)
end

(* default_sort DEFINED *)

instantiation ADDR :: DEFINED_NE
begin
definition defined_ADDR :: "ADDR \<Rightarrow> bool" where
"defined_ADDR x = True"
instance
  by (intro_classes, auto simp add: defined_ADDR_def)
end

lemma Defined_ADDR [defined] :
"\<D> (x :: ADDR)" by (simp add: defined_ADDR_def)

defs (overloaded)
  InjU_ADDR [inju]:  "InjU (x :: ADDR) \<equiv> MkAddr x"
  ProjU_ADDR [inju]: "ProjU (v :: 'm::ADDR_SORT uval) \<equiv> DestAddr v"
  TypeU_ADDR [simp]: "TypeU (t :: ADDR itself) \<equiv> AddrType"

lemma TypeUSound_ADDR [typing] :
"TYPEUSOUND(ADDR, 'm::ADDR_SORT)"
apply (rule UTypedef_intro)
apply (simp_all add: typing defined inju)
apply (metis Inverse MkAddr_cases strict_type_rel_def)
done

typedef 'a::type PADDR = "UNIV :: ADDR set"
apply (rule UNIV_witness)
done

declare Abs_PADDR_inverse [simp]
declare Rep_PADDR_inverse [simp]
declare Rep_PADDR [simp]

instantiation PADDR :: (type) DEFINED_NE
begin
definition defined_PADDR :: "'a PADDR \<Rightarrow> bool" where
"defined_PADDR x = True"
instance
  by (intro_classes, auto simp add: defined_PADDR_def)
end

lemma Defined_PADDR [defined] :
"\<D> (x :: 'a::DEFINED PADDR)"
  by (simp add: defined_PADDR_def)

defs (overloaded)
  InjU_PADDR [inju]:  "InjU (x :: 'a::DEFINED PADDR) \<equiv> MkAddr (Rep_PADDR x)"
  ProjU_PADDR [inju]: "ProjU (v :: 'a::ADDR_SORT uval) \<equiv> Abs_PADDR (DestAddr v)"
  TypeU_PADDR [simp]: "TypeU (t :: 'a::DEFINED PADDR itself) \<equiv> AddrType"

lemma TypeUSound_PADDR [typing] :
"TYPEUSOUND('a::DEFINED PADDR, 'm::ADDR_SORT)"
apply (rule UTypedef_intro)
apply (simp_all add: typing defined inju)
apply (metis Inverse MkAddr_cases strict_type_rel_def)
done

adhoc_overloading
  erase Rep_PADDR

definition prefs :: "'a::DEFINED \<Rightarrow> 'm::ADDR_SORT itself \<Rightarrow> ADDR fset" where
"prefs x t = refs (InjU x :: 'm uval)"

(* Does this type need to avoid cyclicity? *)

typedef 'm::ADDR_SORT STORE =
  "{f :: (ADDR, 'm sigtype) fmap . \<Union>\<^sub>f (refs `\<^sub>f sigvalue `\<^sub>f fran f) \<subseteq>\<^sub>f fdom f}"
  by (rule_tac x = "0" in exI, simp add: fran.rep_eq zero_fmap.rep_eq)

setup_lifting type_definition_STORE

declare Abs_STORE_inverse [simp]
declare Rep_STORE_inverse [simp]
declare Rep_STORE [simp]

lemma Rep_STORE_intro [intro!] :
"Rep_STORE x = Rep_STORE y \<Longrightarrow> x = y"
  by (simp add:Rep_STORE_inject)

lemma Rep_STORE_elim [elim] :
"\<lbrakk>x = y; Rep_STORE x = Rep_STORE y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto)

lift_definition st_graph ::
  "'m::ADDR_SORT STORE \<Rightarrow> (ADDR \<times> 'm sigtype) fset"
is "fmap_graph :: (ADDR, 'm sigtype) fmap \<Rightarrow> (ADDR \<times> 'm sigtype) fset" ..

lemma st_graph_inj :
  "st_graph(s1) = st_graph(s2) \<Longrightarrow> s1 = s2"
apply (erule Rep_fset_elim)
apply (auto simp add: st_graph.rep_eq fmap_graph.rep_eq)
apply (metis map_graph_inv)
done

instantiation STORE :: (ADDR_SORT) order
begin
definition less_eq_STORE :: "'a STORE \<Rightarrow> 'a STORE \<Rightarrow> bool" where
"s1 \<le> s2 \<longleftrightarrow> st_graph s1 \<subseteq>\<^sub>f st_graph s2"

definition less_STORE :: "'a STORE \<Rightarrow> 'a STORE \<Rightarrow> bool" where
"s1 < s2 \<longleftrightarrow> st_graph s1 \<subset>\<^sub>f st_graph s2"

instance
apply (intro_classes)
apply (auto intro: st_graph_inj simp add: less_eq_STORE_def less_STORE_def)
apply (metis Rep_fset_inject st_graph_inj)
done
end

lift_definition st_lookup ::
  "'m::ADDR_SORT STORE \<Rightarrow> ADDR \<Rightarrow> 'm sigtype" ("\<langle>_\<rangle>\<^sub>\<mu>")
is "(\<lambda> s k. the (Rep_fmap s k)) ::
   (ADDR, 'm sigtype) fmap \<Rightarrow> ADDR \<Rightarrow> 'm sigtype" ..

definition st_lookup_ty ::
  "('m::ADDR_SORT) STORE \<Rightarrow> 'a PADDR \<Rightarrow> 'a" ("\<langle>_\<rangle>\<^sub>&") where
"st_lookup_ty s k =
  (if (TYPEU('a) = sigtype(\<langle>s\<rangle>\<^sub>\<mu> (k\<down>)))
    then ProjU(sigvalue(\<langle>s\<rangle>\<^sub>\<mu> (k\<down>))) else undefined)"

lift_definition sdom :: "'m::ADDR_SORT STORE \<Rightarrow> ADDR fset"
is "fdom :: (ADDR, 'm sigtype) fmap \<Rightarrow> ADDR fset" ..

lift_definition sran :: "'m::ADDR_SORT STORE \<Rightarrow> 'm uval fset"
is "\<lambda> x . (sigvalue `\<^sub>f fran x)" ..

lift_definition srefs :: "('m::ADDR_SORT) STORE \<Rightarrow> ADDR fset"
is "\<lambda> f. \<Union>\<^sub>f (refs `\<^sub>f sigvalue `\<^sub>f fran f)" by (auto)

lift_definition st_upd ::
  "'m::ADDR_SORT STORE \<Rightarrow> ADDR \<Rightarrow> 'm sigtype \<Rightarrow> 'm STORE" is
"\<lambda> f k v. if (refs(sigvalue(v)) \<subseteq>\<^sub>f fdom(f) \<union>\<^sub>f \<lbrace>k\<rbrace>) then fmap_upd f k (Some v) else f"
  apply (auto)
  apply (metis (no_types) UN_I fupd_None_fran_subset less_eq_fset.rep_eq subsetD)
done

definition st_upd_ty ::
  "'m::ADDR_SORT STORE \<Rightarrow> 'a::DEFINED PADDR \<Rightarrow> 'a \<Rightarrow> 'm STORE" where
"st_upd_ty s k v = st_upd s (k\<down>) (psigma v)"

nonterminal supdbinds and supdbind and tsupdbinds and tsupdbind

syntax
  "_supdbind" :: "['a, 'a] => supdbind"               ("(2_ :=\<^sub>\<mu>/ _)")
  ""          :: "supdbind => supdbinds"              ("_")
  "_supdbinds":: "[supdbind, supdbinds] => supdbinds" ("_,/ _")
  "_SUpdate"  :: "['a, supdbinds] => 'a"              ("_/'((_)')" [1000, 0] 900)

  "_tsupdbind" :: "['a, 'a] => tsupdbind"                 ("(2_ :=\<^sub>&/ _)")
  ""           :: "tsupdbind => tsupdbinds"               ("_")
  "_tsupdbinds":: "[tsupdbind, tsupdbinds] => tsupdbinds" ("_,/ _")
  "_TSUpdate"  :: "['a, tsupdbinds] => 'a"                ("_/'((_)')" [1000, 0] 900)

translations
  "_SUpdate f (_supdbinds b bs)" == "_SUpdate (_SUpdate f b) bs"
  "f(x:=\<^sub>\<mu>y)" == "CONST st_upd f x y"

  "_TSUpdate f (_tsupdbinds b bs)" == "_TSUpdate (_TSUpdate f b) bs"
  "f(x:=\<^sub>&y)" == "CONST st_upd_ty f x y"

lemma st_upd_closed:
  "\<lbrakk> refs(sigvalue(v)) \<subseteq>\<^sub>f sdom(s) \<union>\<^sub>f \<lbrace>k\<rbrace> \<rbrakk> \<Longrightarrow> Rep_STORE (st_upd s k v) = fmap_upd (Rep_STORE s) k (Some v)"
  by (auto simp add: st_upd.rep_eq sdom.rep_eq)

lemma st_lookup_upd_1: "refs(sigvalue(v)) \<subseteq>\<^sub>f sdom(s) \<union>\<^sub>f \<lbrace>k\<rbrace> \<Longrightarrow> \<langle>s(k :=\<^sub>\<mu> v)\<rangle>\<^sub>\<mu> k = v"
  by (auto simp add:st_lookup_def st_upd_closed)

lemma st_lookup_upd_2: "\<lbrakk> refs(sigvalue(v)) \<subseteq>\<^sub>f sdom(s) \<union>\<^sub>f \<lbrace>k\<rbrace>; k \<noteq> k' \<rbrakk> \<Longrightarrow> \<langle>s(k :=\<^sub>\<mu> v)\<rangle>\<^sub>\<mu> k' = \<langle>s\<rangle>\<^sub>\<mu> k'"
  by (simp add:st_lookup_def st_upd_closed)

lemma st_lookup_upd_ty_1:
  fixes s :: "'m::ADDR_SORT STORE" and k :: "'a::{DEFINED,TYPED_MODEL} PADDR"
  assumes "TYPEUSOUND('a, 'm)" "prefs v TYPE('m) \<subseteq>\<^sub>f sdom(s) \<union>\<^sub>f \<lbrace>k\<down>\<rbrace>"
  shows "\<langle>s(k :=\<^sub>& v)\<rangle>\<^sub>& k = v"
  using assms
apply (simp add:
  st_lookup_ty_def st_upd_ty_def st_lookup_upd_1 prefs_def UTypedef.axm4)
done

lemma st_lookup_upd_ty_2:
  fixes s :: "('m::ADDR_SORT) STORE" and k :: "'a::{DEFINED,TYPED_MODEL} PADDR"
    and k' :: "'b PADDR"
  assumes "TYPEUSOUND('a, 'm)" "prefs v TYPE('m) \<subseteq>\<^sub>f sdom(s) \<union>\<^sub>f \<lbrace>k\<down>\<rbrace>" "k\<down> = k'\<down>"
  shows "\<langle>s(k :=\<^sub>& v)\<rangle>\<^sub>& k' = \<langle>s\<rangle>\<^sub>& k'"
  using assms apply (simp add:st_lookup_ty_def st_upd_ty_def)
oops

instantiation STORE :: (ADDR_SORT) monoid_add
begin

lift_definition zero_STORE :: "'m::ADDR_SORT STORE"
is "fmempty :: (ADDR, 'm sigtype) fmap"
  by (simp add:fran.rep_eq zero_fmap.rep_eq)

lift_definition plus_STORE :: "'a STORE \<Rightarrow> 'a STORE \<Rightarrow> 'a STORE"
is "\<lambda> x y. (x + y :: (ADDR, 'a sigtype) fmap)"
apply (simp add:fran.rep_eq fdom.rep_eq plus_fmap.rep_eq)
apply (subgoal_tac
  "(\<Union>a\<in>ran (\<langle>fmap1\<rangle>\<^sub>m ++ \<langle>fmap2\<rangle>\<^sub>m). \<langle>refs(sigvalue(a))\<rangle>\<^sub>f) \<subseteq>
    (\<Union>a\<in>ran \<langle>fmap1\<rangle>\<^sub>m. \<langle>refs(sigvalue(a))\<rangle>\<^sub>f) \<union>
    (\<Union>a\<in>ran \<langle>fmap2\<rangle>\<^sub>m. \<langle>refs(sigvalue(a))\<rangle>\<^sub>f)")
defer
apply (auto) [1]
apply (metis (full_types) Un_iff ran_map_add_subset set_rev_mp)
apply (auto)
apply (force)
done

instance
apply (intro_classes)
apply (auto simp add:zero_STORE.rep_eq plus_STORE.rep_eq)
apply (metis map_add_assoc plus_fmap.rep_eq)
done

end

lemma map_graph_add:
"dom(x) \<inter> dom(y) = {} \<Longrightarrow> map_graph(x ++ y) = map_graph(x) \<union> map_graph(y)"
apply (auto simp add:map_graph_def)
apply (metis map_add_comm map_add_find_right)
done

lemma fmap_graph_add:
"fdom(x) \<inter>\<^sub>f fdom(y) = \<lbrace>\<rbrace> \<Longrightarrow> fmap_graph(x + y) = fmap_graph(x) \<union>\<^sub>f fmap_graph(y)"
  by (force simp add:fdom.rep_eq fmap_graph.rep_eq plus_fmap.rep_eq map_graph_add)

lemma st_graph_add:
"sdom(x) \<inter>\<^sub>f sdom(y) = \<lbrace>\<rbrace> \<Longrightarrow> st_graph(x + y) = st_graph(x) \<union>\<^sub>f st_graph(y)"
  by (metis fmap_graph_add plus_STORE.rep_eq sdom.rep_eq st_graph.rep_eq)

lemma st_leq_lub:
  fixes x :: "('m::ADDR_SORT) STORE"
  assumes "sdom(x) \<inter>\<^sub>f sdom(y) = \<lbrace>\<rbrace>"
  shows "x \<le> y \<longleftrightarrow> x + y \<le> y"
  using assms by (simp add:less_eq_STORE_def st_graph_add)

lemma srefs_subset_sdom : "srefs(\<Gamma>) \<subseteq>\<^sub>f sdom(\<Gamma>)"
apply (insert Rep_STORE[of "\<Gamma>"])
apply (auto simp add: sdom.rep_eq srefs.rep_eq)
done

lemma STORE_add_comm :
"sdom(s1) \<inter>\<^sub>f sdom(s2) = \<lbrace>\<rbrace> \<Longrightarrow> s1 + s2 = s2 + s1"
apply (rule Rep_STORE_intro)
apply (erule Rep_fset_elim)
apply (simp add:plus_STORE.rep_eq)
apply (metis Rep_fset_intro fempty.rep_eq finter.rep_eq fmap_add_comm sdom.rep_eq)
done

lemma sdom_0 [simp] : "sdom(0) = \<lbrace>\<rbrace>"
  by (metis fdom_fmempty sdom.rep_eq zero_STORE.rep_eq)

lemma sran_0 [simp] : "sran(0) = \<lbrace>\<rbrace>"
  by (auto simp add:sran.rep_eq zero_STORE.rep_eq fran.rep_eq zero_fmap.rep_eq)

lemma sdom_plus [simp] : "sdom(x + y) = sdom(x) \<union>\<^sub>f sdom(y)"
  by (metis (hide_lams, no_types) fdom_plus plus_STORE.rep_eq sdom.rep_eq)

default_sort TYPED_MODEL

class STORE_SORT = ADDR_SORT +
  fixes MkStore :: "'a STORE \<Rightarrow> 'a uval"
  fixes DestStore :: "'a uval \<Rightarrow> 'a STORE"
  fixes StoreType :: "'a utype"
  assumes Inverse [simp] : "DestStore (MkStore x) = x"
  assumes StoreType_dcarrier : "dcarrier StoreType = range MkStore"
begin

lemma Defined [defined] : "\<D>\<^sub>v (MkStore i)"
  by (metis StoreType_dcarrier dcarrier_member rangeI strict_type_rel_def)

lemma MkStore_type [typing] : "MkStore n : StoreType"
  by (metis StoreType_dcarrier dcarrier_member rangeI strict_type_rel_def)

lemma MkStore_dtype [typing] : "MkStore n :! StoreType"
  by (metis Defined MkStore_type strict_type_rel_def)

lemma MkStore_cases [elim] :
  "x :! StoreType \<Longrightarrow> \<lbrakk>\<And> i. x = MkStore i \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (metis StoreType_dcarrier dcarrier_member image_iff)

lemma MkStore_inj_simp [simp] :
"(MkStore x = MkStore y) \<longleftrightarrow> x = y"
  by (metis Inverse)
end

instantiation STORE :: (TYPED_MODEL) DEFINED_NE
begin
definition "defined_STORE (x :: 'a STORE) = True"
instance
  by (intro_classes, auto simp add: defined_STORE_def)
end

lemma Defined_STORE [defined] :
"\<D> (x :: 'a STORE)"
  by (simp add: defined_STORE_def)

defs (overloaded)
  InjU_STORE [inju]:  "InjU (x :: 'a::STORE_SORT STORE) \<equiv> MkStore x"
  ProjU_STORE [inju]: "ProjU (v :: 'a::STORE_SORT uval) \<equiv> DestStore v"
  TypeU_STORE [simp]: "TypeU (t :: 'a::STORE_SORT STORE itself) \<equiv> StoreType"

lemma TypeUSound_STORE [typing] :
"TYPEUSOUND('m STORE, 'm::STORE_SORT)"
apply (rule UTypedef_intro)
apply (simp_all add: typing defined inju)
apply (clarify)
apply (metis MkStore_cases STORE_SORT_class.Inverse strict_type_rel_def)
done
end
