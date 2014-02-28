(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_names_ext.thy                                                    *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Extensible Variable Names *}

theory utp_names_ext
imports "../utp_common"
begin

datatype NmAtT = NABoolT | NANatT | NAIntT | NACharT | NAPairT NmAtT NmAtT | NAListT NmAtT

datatype NmAtV = NABoolV bool | NANatV nat | NAIntV int | NACharV char
               | NAPairV NmAtV NmAtV | NAListV "NmAtV list"

type_synonym NmAtN = "(string * NmAtT)"

inductive nm_ty :: "NmAtV \<Rightarrow> NmAtT \<Rightarrow> bool" (infix ":\<^sub>n" 50) where
"NABoolV x :\<^sub>n NABoolT" |
"NANatV n :\<^sub>n NANatT" |
"NAIntV n :\<^sub>n NAIntT" |
"NACharV x :\<^sub>n NACharT" |
"\<lbrakk> x :\<^sub>n a; y :\<^sub>n b \<rbrakk> \<Longrightarrow> NAPairV x y :\<^sub>n NAPairT a b" |
"\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>n a \<rbrakk> \<Longrightarrow> NAListV xs :\<^sub>n NAListT a"

class nm_at =
  fixes nma_inj :: "'a \<Rightarrow> NmAtV"
  and   nma_prj :: "NmAtV \<Rightarrow> 'a"
  and   nma_ty  :: "'a itself \<Rightarrow> NmAtT"
  assumes nma_ty_sound: "nma_inj x :\<^sub>n nma_ty TYPE('a)"
  and nma_inv [simp]: "nma_prj (nma_inj x) = x"

instantiation bool :: nm_at
begin

definition nma_inj_bool :: "bool \<Rightarrow> NmAtV" where "nma_inj_bool = NABoolV"
fun nma_prj_bool :: "NmAtV \<Rightarrow> bool" where  "nma_prj_bool(NABoolV x) = x"
definition nma_ty_bool :: "bool itself \<Rightarrow> NmAtT" where "nma_ty_bool(t) = NABoolT"

instance
  by (intro_classes, simp_all add: nma_ty_bool_def nma_ty_sound nma_inj_bool_def nm_ty.intros)
end

instantiation nat :: nm_at
begin

definition nma_inj_nat :: "nat \<Rightarrow> NmAtV" where "nma_inj_nat = NANatV"
fun nma_prj_nat :: "NmAtV \<Rightarrow> nat" where  "nma_prj_nat(NANatV x) = x"
definition nma_ty_nat :: "nat itself \<Rightarrow> NmAtT" where "nma_ty_nat(t) = NANatT"

instance
  by (intro_classes, simp_all add: nma_ty_nat_def nma_ty_sound nma_inj_nat_def nm_ty.intros)
end

instantiation int :: nm_at
begin

definition nma_inj_int :: "int \<Rightarrow> NmAtV" where "nma_inj_int = NAIntV"
fun nma_prj_int :: "NmAtV \<Rightarrow> int" where  "nma_prj_int(NAIntV x) = x"
definition nma_ty_int :: "int itself \<Rightarrow> NmAtT" where "nma_ty_int(t) = NAIntT"

instance
  by (intro_classes, simp_all add: nma_ty_int_def nma_ty_sound nma_inj_int_def nm_ty.intros)
end

instantiation char :: nm_at
begin

definition nma_inj_char :: "char \<Rightarrow> NmAtV" where "nma_inj_char = NACharV"
fun nma_prj_char :: "NmAtV \<Rightarrow> char" where  "nma_prj_char(NACharV x) = x"
definition nma_ty_char :: "char itself \<Rightarrow> NmAtT" where "nma_ty_char(t) = NACharT"

instance
  by (intro_classes, simp_all add: nma_ty_char_def nma_ty_sound nma_inj_char_def nm_ty.intros)
end

instantiation list :: (nm_at) nm_at
begin

definition nma_inj_list :: "'a list \<Rightarrow> NmAtV" where 
"nma_inj_list xs = NAListV (map nma_inj xs)"

fun nma_prj_list :: "NmAtV \<Rightarrow> 'a list" where
"nma_prj_list (NAListV xs) = map nma_prj xs"

definition nma_ty_list :: "'a list itself \<Rightarrow> NmAtT" where 
"nma_ty_list t = NAListT (nma_ty TYPE('a))"

instance
  apply (intro_classes)
  apply (simp_all add:nma_inj_list_def nma_ty_list_def)
  apply (rule nm_ty.intros)
  apply (force intro: nm_ty.intros nma_ty_sound)
  apply (metis (full_types) comp_def map_idI nma_inv)
done
end

type_synonym UNAME_SCHEMA = "(string, NmAtT) fmap"

typedef UNAME = "{f :: (NmAtN, NmAtV) fmap. \<forall> x \<in>\<^sub>f fdom f. the (\<langle>f\<rangle>\<^sub>m x) :\<^sub>n snd x}"
  by (rule_tac x="fmempty" in exI, simp)

setup_lifting type_definition_UNAME

typedef ('a::nm_at) UNAME_ATT = "UNIV :: string set" 
  by auto

setup_lifting type_definition_UNAME_ATT

declare Rep_UNAME_ATT [simp]
declare Rep_UNAME_ATT_inverse [simp]
declare Abs_UNAME_ATT_inverse [simp]

lift_definition nm_nil :: "UNAME" is "fmempty"
  by (auto)

lift_definition nm_set :: "'a::nm_at UNAME_ATT \<Rightarrow> 'a option \<Rightarrow> UNAME \<Rightarrow> UNAME"
is "\<lambda> (k::string) (v::'a option) n. fmap_upd n (k, nma_ty(TYPE('a::nm_at))) (Option.map nma_inj v)"
  apply (case_tac option)
  apply (auto intro:nma_ty_sound simp add:fdom.rep_eq)
  apply (metis domI the.simps)
done

definition nm_lookup :: "'a::nm_at UNAME_ATT \<Rightarrow> UNAME \<Rightarrow> 'a option"
where "nm_lookup k n = (\<langle>Rep_UNAME n\<rangle>\<^sub>m (Rep_UNAME_ATT k, nma_ty(TYPE('a::nm_at))) \<guillemotright>= Some \<circ> nma_prj)"

lemma nm_lookup_nm_set [simp]:
  "nm_lookup k (nm_set k v n) = v"
  apply (case_tac v)
  apply (auto simp add:nm_lookup_def nm_set.rep_eq)
done

lemma nm_lookup_nm_ne [simp]:
  "Rep_UNAME_ATT k \<noteq> Rep_UNAME_ATT k' \<Longrightarrow> nm_lookup k (nm_set k' v n) = nm_lookup k n"
  by (auto simp add:nm_lookup_def nm_set.rep_eq)

abbreviation "nm_label_attr     \<equiv> (Abs_UNAME_ATT ''label'' :: string UNAME_ATT)"
abbreviation "nm_dashes_attr    \<equiv> (Abs_UNAME_ATT ''dashes'' :: nat UNAME_ATT)"
abbreviation "nm_subscript_attr \<equiv> (Abs_UNAME_ATT ''subscript'' :: nat UNAME_ATT)"

definition MkUName :: "string \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> UNAME" where
"MkUName n d s = nm_set nm_label_attr (Some n) 
                 (nm_set nm_dashes_attr (Some d) 
                  (nm_set nm_subscript_attr s nm_nil))"

abbreviation uname_str :: "UNAME \<Rightarrow> string" where
"uname_str n \<equiv> the (nm_lookup nm_label_attr n)"

abbreviation uname_dashes :: "UNAME \<Rightarrow> nat" where
"uname_dashes n \<equiv> the (nm_lookup nm_dashes_attr n)"

lemma "uname_str (MkUName n d s) = n"
  by (simp add:MkUName_def)

lemma "uname_dashes (MkUName n d s) = d"
  by (simp add:MkUName_def)

end