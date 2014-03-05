(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_memory.thy                                                       *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Simple memory model *}

theory utp_memory
imports 
  "../core/utp_value"
  "../poly/utp_poly_var"
begin

default_sort VALUE

typedef ADDR = "UNIV :: nat set" ..

declare Rep_ADDR [simp]
declare Rep_ADDR_inverse [simp]
declare Abs_ADDR_inverse [simplified, simp]

class ADDR_SORT = VALUE +
  fixes MkAddr   :: "ADDR \<Rightarrow> 'a"
  and   DestAddr :: "'a \<Rightarrow> ADDR"
  and   AddrType :: "'a UTYPE"
  and   refs     :: "'a \<Rightarrow> ADDR fset"

  assumes Inverse [simp] : "DestAddr (MkAddr x) = x"
  and     AddrType_dcarrier: "dcarrier AddrType = range MkAddr"
  and     refs_MkAddr: "refs (MkAddr x) = \<lbrace>x\<rbrace>"
begin

lemma Defined [defined]: "\<D> (MkAddr i)"
  by (metis AddrType_dcarrier dcarrier_defined rangeI)

lemma MkAddr_type [typing]: "MkAddr n : AddrType"
  by (metis AddrType_dcarrier dcarrier_type rangeI)

lemma MkAddr_dtype [typing]: "MkAddr n :! AddrType"
  by (metis Defined MkAddr_type dtype_relI)

lemma MkAddr_cases [elim]: 
  "\<lbrakk> x :! AddrType; \<And> i. x = MkAddr i \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis AddrType_dcarrier dtype_as_dcarrier image_iff)

lemma MkAddr_inj_simp [simp]: 
  "(MkAddr x = MkAddr y) \<longleftrightarrow> x = y"
  by (metis Inverse)

end

default_sort DEFINED

instantiation ADDR :: DEFINED_NE
begin
definition "Defined_ADDR (x::ADDR) = True"
instance 
  by (intro_classes, auto simp add:Defined_ADDR_def)
end

lemma Defined_ADDR [defined]: "\<D> (x :: ADDR)" by (simp add:Defined_ADDR_def)

defs (overloaded)
  InjU_ADDR [inju]:  "InjU (x::ADDR) \<equiv> MkAddr x"
  ProjU_ADDR [inju]: "ProjU (x::('a::ADDR_SORT)) \<equiv> DestAddr x"
  TypeU_ADDR [simp]: "TypeU (x::ADDR itself) \<equiv> AddrType"

lemma TypeUSound_ADDR [typing]: "TYPEUSOUND(ADDR, 'm :: ADDR_SORT)"
  by (force simp add: typing defined inju)

typedef ('a::type) PADDR = "UNIV :: ADDR set" ..

declare Rep_PADDR [simp]
declare Rep_PADDR_inverse [simp]
declare Abs_PADDR_inverse [simplified, simp]

instantiation PADDR :: (type) DEFINED_NE
begin
definition "Defined_PADDR (x::'a PADDR) = True"
instance 
  by (intro_classes, auto simp add:Defined_PADDR_def)
end

lemma Defined_PADDR [defined]: "\<D> (x :: ('a::DEFINED) PADDR)" by (simp add:Defined_PADDR_def)

defs (overloaded)
  InjU_PADDR [inju]:  "InjU (x::('a::DEFINED) PADDR) \<equiv> MkAddr (Rep_PADDR x)"
  ProjU_PADDR [inju]: "ProjU (x::('a::ADDR_SORT)) \<equiv> Abs_PADDR (DestAddr x)"
  TypeU_PADDR [simp]: "TypeU (x::('a::DEFINED) PADDR itself) \<equiv> AddrType"

lemma TypeUSound_PADDR [typing]: "TYPEUSOUND(('a::DEFINED) PADDR, 'm :: ADDR_SORT)"
  by (force simp add: typing defined inju)

setup {*
Adhoc_Overloading.add_variant @{const_name erase} @{const_name Rep_PADDR}
*}

definition prefs :: "'a \<Rightarrow> ('m::ADDR_SORT) itself \<Rightarrow> ADDR fset" where
"prefs x t = refs (InjU x :: 'm)"

(* Does this type need to avoid cyclicity? *)

typedef ('m::ADDR_SORT) STORE = "{f :: (ADDR, 'm SIGTYPE) fmap. \<Union>\<^sub>f (refs `\<^sub>f sigvalue `\<^sub>f fran f) \<subseteq>\<^sub>f fdom f}"
  by (rule_tac x="0" in exI, simp add:fran.rep_eq zero_fmap.rep_eq)

setup_lifting type_definition_STORE

declare Rep_STORE [simp]
declare Rep_STORE_inverse [simp]
declare Abs_STORE_inverse [simp]

lemma Rep_STORE_intro [intro!]:
  "Rep_STORE x = Rep_STORE y \<Longrightarrow> x = y"
  by (simp add:Rep_STORE_inject)

lemma Rep_STORE_elim [elim]:
  "\<lbrakk> x = y; Rep_STORE x = Rep_STORE y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

lift_definition st_lookup :: "('m::ADDR_SORT) STORE \<Rightarrow> ADDR \<Rightarrow> 'm SIGTYPE" ("\<langle>_\<rangle>\<^sub>\<mu>") is "\<lambda> s k. the (Rep_fmap s k)" ..

definition st_lookup_ty :: "('m::ADDR_SORT) STORE \<Rightarrow> 'a PADDR \<Rightarrow> 'a" ("\<langle>_\<rangle>\<^sub>&") where
"st_lookup_ty s k = (if (TYPEU('a) = sigtype(\<langle>s\<rangle>\<^sub>\<mu> (k\<down>))) then ProjU(sigvalue(\<langle>s\<rangle>\<^sub>\<mu> (k\<down>))) else undefined)"

lift_definition sdom :: "('m::ADDR_SORT) STORE \<Rightarrow> ADDR fset" is "fdom" ..
lift_definition sran :: "('m::ADDR_SORT) STORE \<Rightarrow> 'm fset" is "\<lambda> x. (sigvalue `\<^sub>f fran x)" ..

lift_definition srefs :: "('m::ADDR_SORT) STORE \<Rightarrow> ADDR fset" 
is "\<lambda> f. \<Union>\<^sub>f (refs `\<^sub>f sigvalue `\<^sub>f fran f)" by (auto)

lift_definition st_upd :: "('m::ADDR_SORT) STORE \<Rightarrow> ADDR \<Rightarrow> 'm SIGTYPE \<Rightarrow> 'm STORE" is
"\<lambda> f k v. if (refs(sigvalue(v)) \<subseteq>\<^sub>f fdom(f) \<union>\<^sub>f \<lbrace>k\<rbrace>) then fmap_upd f k (Some v) else f"
  apply (auto)
  apply (metis (no_types) UN_I fupd_None_fran_subset less_eq_fset.rep_eq subsetD)
done

definition st_upd_ty :: "('m::ADDR_SORT) STORE \<Rightarrow> 'a PADDR \<Rightarrow> 'a \<Rightarrow> 'm STORE" where
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
  fixes s :: "('m::ADDR_SORT) STORE" and k :: "'a PADDR"
  assumes "TYPEUSOUND('a, 'm)" "prefs v TYPE('m) \<subseteq>\<^sub>f sdom(s) \<union>\<^sub>f \<lbrace>k\<down>\<rbrace>"
  shows "\<langle>s(k :=\<^sub>& v)\<rangle>\<^sub>& k = v"
  using assms by (simp add:st_lookup_ty_def st_upd_ty_def st_lookup_upd_1 prefs_def)

lemma st_lookup_upd_ty_2: 
  fixes s :: "('m::ADDR_SORT) STORE" and k :: "'a PADDR" and k' :: "'b PADDR"
  assumes "TYPEUSOUND('a, 'm)" "prefs v TYPE('m) \<subseteq>\<^sub>f sdom(s) \<union>\<^sub>f \<lbrace>k\<down>\<rbrace>" "k\<down> = k'\<down>"
  shows "\<langle>s(k :=\<^sub>& v)\<rangle>\<^sub>& k' = \<langle>s\<rangle>\<^sub>& k'"
  using assms apply (simp add:st_lookup_ty_def st_upd_ty_def)
oops

instantiation STORE :: (ADDR_SORT) monoid_add
begin

lift_definition zero_STORE :: "'a STORE" is "fmempty"
  by (simp add:fran.rep_eq zero_fmap.rep_eq)

lift_definition plus_STORE :: "'a STORE \<Rightarrow> 'a STORE \<Rightarrow> 'a STORE" is 
"\<lambda> x y. (x + y :: (ADDR, 'a SIGTYPE) fmap)"
  apply (simp add:fran.rep_eq fdom.rep_eq plus_fmap.rep_eq)
  apply (subgoal_tac "(\<Union>a\<in>ran (\<langle>fmap1\<rangle>\<^sub>m ++ \<langle>fmap2\<rangle>\<^sub>m). \<langle>refs(sigvalue(a))\<rangle>\<^sub>f) 
                       \<subseteq> (\<Union>a\<in>ran \<langle>fmap1\<rangle>\<^sub>m. \<langle>refs(sigvalue(a))\<rangle>\<^sub>f) \<union> (\<Union>a\<in>ran \<langle>fmap2\<rangle>\<^sub>m. \<langle>refs(sigvalue(a))\<rangle>\<^sub>f)")
  defer
  apply (auto)[1]
  apply (metis Un_iff ran_map_add_subset set_mp sup_set_def)
  apply (auto)
  apply (force)
done

instance
  apply (intro_classes)
  apply (auto simp add:zero_STORE.rep_eq plus_STORE.rep_eq)
  apply (metis add_assoc)
done

end

lemma srefs_subset_sdom: "srefs(\<Gamma>) \<subseteq>\<^sub>f sdom(\<Gamma>)"
  apply (insert Rep_STORE[of "\<Gamma>"])
  apply (auto simp add: sdom.rep_eq srefs.rep_eq)
done

lemma STORE_add_comm: "sdom(s1) \<inter>\<^sub>f sdom(s2) = \<lbrace>\<rbrace> \<Longrightarrow> s1 + s2 = s2 + s1"
  apply (rule Rep_STORE_intro)
  apply (erule Rep_fset_elim)
  apply (simp add:plus_STORE.rep_eq)
  apply (metis Rep_fset_intro fempty.rep_eq finter.rep_eq fmap_add_comm sdom.rep_eq)
done

default_sort VALUE

class STORE_SORT = ADDR_SORT +
  fixes MkStore   :: "'a STORE \<Rightarrow> 'a"
  and   DestStore :: "'a \<Rightarrow> 'a STORE"
  and   StoreType :: "'a UTYPE"

  assumes Inverse [simp] : "DestStore (MkStore x) = x"
  and     StoreType_dcarrier: "dcarrier StoreType = range MkStore"
begin

lemma Defined [defined]: "\<D> (MkStore i)"
  by (metis StoreType_dcarrier dcarrier_defined rangeI)

lemma MkStore_type [typing]: "MkStore n : StoreType"
  by (metis StoreType_dcarrier dcarrier_type rangeI)

lemma MkStore_dtype [typing]: "MkStore n :! StoreType"
  by (metis Defined MkStore_type dtype_relI)

lemma MkStore_cases [elim]: 
  "\<lbrakk> x :! StoreType; \<And> i. x = MkStore i \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis StoreType_dcarrier dtype_as_dcarrier image_iff)

lemma MkStore_inj_simp [simp]: 
  "(MkStore x = MkStore y) \<longleftrightarrow> x = y"
  by (metis Inverse)

end

instantiation STORE :: (VALUE) DEFINED_NE
begin
definition "Defined_STORE (x::'a STORE) = True"
instance 
  by (intro_classes, auto simp add:Defined_STORE_def)
end

lemma Defined_STORE [defined]: "\<D> (x :: 'a STORE)" by (simp add:Defined_STORE_def)

defs (overloaded)
  InjU_STORE [inju]:  "InjU (x::('a::STORE_SORT) STORE) \<equiv> MkStore x"
  ProjU_STORE [inju]: "ProjU (x::('a::STORE_SORT)) \<equiv> DestStore x"
  TypeU_STORE [simp]: "TypeU (x::('a::STORE_SORT) STORE itself) \<equiv> StoreType"

lemma TypeUSound_STORE [typing]: "TYPEUSOUND('m STORE, 'm :: STORE_SORT)"
  by (force simp add: typing defined inju)

end