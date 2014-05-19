(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_names_ext.thy                                                    *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Extensible Variable Names *}

theory utp_names_ext
imports "../utp_common" Derive
begin

datatype NmAtT = NABoolT | NANatT | NAIntT | NACharT | NAOptT NmAtT | NAPairT NmAtT NmAtT | NAListT NmAtT

derive linorder  NmAtT
derive countable NmAtT

datatype NmAtV = NABoolV bool | NANatV nat | NAIntV int | NACharV char
               | NAOptV "NmAtV option" | NAPairV NmAtV NmAtV | NAListV NmAtT "NmAtV list"

derive linorder  NmAtV
derive countable NmAtV

type_synonym NmAtN = "(string * NmAtT)"

inductive nm_ty :: "NmAtV \<Rightarrow> NmAtT \<Rightarrow> bool" (infix ":\<^sub>a" 50) where
"NABoolV x :\<^sub>a NABoolT" |
"NANatV n :\<^sub>a NANatT" |
"NAIntV n :\<^sub>a NAIntT" |
"NACharV x :\<^sub>a NACharT" |
"\<lbrakk> x :\<^sub>a a \<rbrakk> \<Longrightarrow> NAOptV (Some x) :\<^sub>a NAOptT a" |
"\<lbrakk> x :\<^sub>a a; y :\<^sub>a b \<rbrakk> \<Longrightarrow> NAPairV x y :\<^sub>a NAPairT a b" |
"\<lbrakk> \<forall>x\<in>set xs. x :\<^sub>a a \<rbrakk> \<Longrightarrow> NAListV a xs :\<^sub>a NAListT a"

inductive_cases 
   [elim!]: "x :\<^sub>a NABoolT" and
   [elim!]: "x :\<^sub>a NANatT" and
   [elim!]: "x :\<^sub>a NAIntT" and
   [elim!]: "x :\<^sub>a NACharT" and
   [elim!]: "x :\<^sub>a NAOptT a" and
   [elim!]: "x :\<^sub>a NAPairT a b" and
   [elim!]: "x :\<^sub>a NAListT a"

class nm_at =
  fixes nma_inj :: "'a \<Rightarrow> NmAtV"
  and   nma_prj :: "NmAtV \<Rightarrow> 'a"
  and   nma_ty  :: "'a itself \<Rightarrow> NmAtT"
  assumes nma_ty_sound: "nma_inj x :\<^sub>a nma_ty TYPE('a)"
  and nma_inj_inv [simp]: "nma_prj (nma_inj x) = x"
  and nma_prj_inv [simp]: "\<lbrakk> y :\<^sub>a  nma_ty TYPE('a) \<rbrakk> \<Longrightarrow> nma_inj (nma_prj y) = y" 

instantiation bool :: nm_at
begin

definition nma_inj_bool :: "bool \<Rightarrow> NmAtV" where "nma_inj_bool = NABoolV"
fun nma_prj_bool :: "NmAtV \<Rightarrow> bool" where  "nma_prj_bool(NABoolV x) = x"
definition nma_ty_bool :: "bool itself \<Rightarrow> NmAtT" where "nma_ty_bool(t) = NABoolT"

instance
  by (intro_classes, auto simp add: nma_ty_bool_def nma_ty_sound nma_inj_bool_def nm_ty.intros)
end

instantiation nat :: nm_at
begin

definition nma_inj_nat :: "nat \<Rightarrow> NmAtV" where "nma_inj_nat = NANatV"
fun nma_prj_nat :: "NmAtV \<Rightarrow> nat" where  "nma_prj_nat(NANatV x) = x"
definition nma_ty_nat :: "nat itself \<Rightarrow> NmAtT" where "nma_ty_nat(t) = NANatT"

instance
  by (intro_classes, auto simp add: nma_ty_nat_def nma_ty_sound nma_inj_nat_def nm_ty.intros)
end

instantiation int :: nm_at
begin

definition nma_inj_int :: "int \<Rightarrow> NmAtV" where "nma_inj_int = NAIntV"
fun nma_prj_int :: "NmAtV \<Rightarrow> int" where  "nma_prj_int(NAIntV x) = x"
definition nma_ty_int :: "int itself \<Rightarrow> NmAtT" where "nma_ty_int(t) = NAIntT"

instance
  by (intro_classes, auto simp add: nma_ty_int_def nma_ty_sound nma_inj_int_def nm_ty.intros)
end

instantiation char :: nm_at
begin

definition nma_inj_char :: "char \<Rightarrow> NmAtV" where "nma_inj_char = NACharV"
fun nma_prj_char :: "NmAtV \<Rightarrow> char" where  "nma_prj_char(NACharV x) = x"
definition nma_ty_char :: "char itself \<Rightarrow> NmAtT" where "nma_ty_char(t) = NACharT"

instance
  by (intro_classes, auto simp add: nma_ty_char_def nma_ty_sound nma_inj_char_def nm_ty.intros)
end

instantiation list :: (nm_at) nm_at
begin

definition nma_inj_list :: "'a list \<Rightarrow> NmAtV" where 
"nma_inj_list xs = NAListV (nma_ty TYPE('a)) (map nma_inj xs)"

fun nma_prj_list :: "NmAtV \<Rightarrow> 'a list" where
"nma_prj_list (NAListV a xs) = map nma_prj xs"

definition nma_ty_list :: "'a list itself \<Rightarrow> NmAtT" where 
"nma_ty_list t = NAListT (nma_ty TYPE('a))"

instance
  apply (intro_classes)
  apply (simp_all add:nma_inj_list_def nma_ty_list_def)
  apply (rule nm_ty.intros)
  apply (force intro: nm_ty.intros nma_ty_sound)
  apply (metis (full_types) comp_def map_idI nma_inj_inv)
  apply (auto)
  apply (metis comp_def map_idI nma_prj_inv)
done
end

type_synonym NAME_SCHEMA = "NmAtN fset"

typedef NAME = "{f :: (NmAtN, NmAtV) fmap. \<forall> x \<in>\<^sub>f fdom f. the (\<langle>f\<rangle>\<^sub>m x) :\<^sub>a snd x}"
  by (rule_tac x="fmempty" in exI, simp)

declare Rep_NAME [simp]
declare Rep_NAME_inverse [simp]
declare Abs_NAME_inverse [simp]

lemma Rep_NAME_intro [intro]:
  "Rep_NAME x = Rep_NAME y \<Longrightarrow> x = y"
  by (simp add:Rep_NAME_inject)

lemma Rep_NAME_type:
  "x \<in>\<^sub>f fdom (Rep_NAME n) \<Longrightarrow> the (\<langle>Rep_NAME n\<rangle>\<^sub>m x) :\<^sub>a snd x"
  by (metis (lifting, no_types) Rep_NAME mem_Collect_eq)

lemma Rep_NAME_type':
  "\<langle>Rep_NAME n\<rangle>\<^sub>m (k, a) = \<lfloor>x\<rfloor> \<Longrightarrow> x :\<^sub>a a"
  apply (insert Rep_NAME[of n])
  apply (simp)
  apply (drule_tac x="k" in spec)
  apply (drule_tac x="a" in spec)
  apply (auto simp add:fdom.rep_eq)
done

setup_lifting type_definition_NAME

definition NAME_type_rel :: "NAME \<Rightarrow> NAME_SCHEMA \<Rightarrow> bool" (infix ":\<^sub>n" 50) where
"NAME_type_rel n ns = (ns \<subseteq>\<^sub>f fdom (Rep_NAME n))"

typedef ('a::nm_at) NAME_ATT = "UNIV :: string set" 
  by auto

setup_lifting type_definition_NAME_ATT

declare Rep_NAME_ATT [simp]
declare Rep_NAME_ATT_inverse [simp]
declare Abs_NAME_ATT_inverse [simp]

abbreviation nm_erase :: "('a::nm_at) NAME_ATT \<Rightarrow> (string * NmAtT)"
where "nm_erase k \<equiv> (Rep_NAME_ATT k, nma_ty(TYPE('a::nm_at)))"

lift_definition nm_nil :: "NAME" is "fmempty"
  by (auto)

lift_definition nm_set :: "'a::nm_at NAME_ATT \<Rightarrow> 'a option \<Rightarrow> NAME \<Rightarrow> NAME"
is "\<lambda> (k::string) (v::'a option) n. fmap_upd n (k, nma_ty(TYPE('a::nm_at))) (Option.map nma_inj v)"
  apply (case_tac option)
  apply (auto intro:nma_ty_sound simp add:fdom.rep_eq)
  apply (metis domI the.simps)
  apply (metis domI)
done

definition nm_lookup :: "'a::nm_at NAME_ATT \<Rightarrow> NAME \<Rightarrow> 'a option"
where "nm_lookup k n = (\<langle>Rep_NAME n\<rangle>\<^sub>m (nm_erase k) \<guillemotright>= Some \<circ> nma_prj)"

lemma nm_lookup_nm_set [simp]:
  "nm_lookup k (nm_set k v n) = v"
  apply (case_tac v)
  apply (auto simp add:nm_lookup_def nm_set.rep_eq)
done

lemma nm_set_lookup [simp]:
  "nm_set k (nm_lookup k f) f = f"
  apply (rule)
  apply (auto simp add:nm_set.rep_eq nm_lookup_def)
  apply (rule ext)
  apply (case_tac "\<langle>Rep_NAME f\<rangle>\<^sub>m (nm_erase k)")
  apply (simp_all)
  apply (metis Rep_NAME_type' nma_prj_inv)
done

lemma nm_lookup_nm_ne [simp]:
  "Rep_NAME_ATT k \<noteq> Rep_NAME_ATT k' \<Longrightarrow> nm_lookup k (nm_set k' v n) = nm_lookup k n"
  by (auto simp add:nm_lookup_def nm_set.rep_eq)

abbreviation "nm_str_attr     \<equiv> (Abs_NAME_ATT ''str'' :: string NAME_ATT)"
abbreviation "nm_dashes_attr    \<equiv> (Abs_NAME_ATT ''dashes'' :: nat NAME_ATT)"
abbreviation "nm_subscript_attr \<equiv> (Abs_NAME_ATT ''subscript'' :: nat NAME_ATT)"

abbreviation "NameStd \<equiv> \<lbrace>nm_erase nm_str_attr, nm_erase nm_dashes_attr, nm_erase nm_subscript_attr\<rbrace>"

definition MkName :: "string \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> NAME" where
"MkName n d s = nm_set nm_str_attr (Some n) 
                (nm_set nm_dashes_attr (Some d) 
                 (nm_set nm_subscript_attr s nm_nil))"

term "Rep_NAME f"

term "nm_set k"

abbreviation name_str :: "NAME \<Rightarrow> string" where
"name_str n \<equiv> the (nm_lookup nm_str_attr n)"

abbreviation dashes :: "NAME \<Rightarrow> nat" where
"dashes n \<equiv> the (nm_lookup nm_dashes_attr n)"

type_synonym SUBSCRIPT = "nat option"

abbreviation subscript :: "NAME \<Rightarrow> SUBSCRIPT" where
"subscript n \<equiv> nm_lookup nm_subscript_attr n"

lemma name_str_simp [simp]: "name_str (MkName n d s) = n"
  by (simp add:MkName_def)

lemma dashes_simp [simp]: "dashes (MkName n d s) = d"
  by (simp add:MkName_def)

lemma subscript_simp [simp]: "subscript (MkName n d s) = s"
  by (simp add:MkName_def)

fun chsub :: "nat \<Rightarrow> SUBSCRIPT \<Rightarrow> SUBSCRIPT" where
"chsub n None = Some n" |
"chsub n (Some n') = (if (n = n') then None else Some n')"

lemma chsub_inv [simp]: 
  "chsub n (chsub n x) = x"
  by (case_tac x, simp_all)

lemma chsub_inj:
  "inj (chsub n)"
  apply (rule injI)
  apply (metis chsub_inv)
done

lemma chsub_surj:
  "surj (chsub n)"
  by (metis chsub_inv surj_def)

lemma chsub_bij [closure]:
  "bij (chsub n)"
  by (rule bijI, fact chsub_inj, fact chsub_surj)  

(*
lemma MkName_inverse [simp]: 
  "n :\<^sub>n NameStd \<Longrightarrow> MkName (name_str n) (dashes n) (subscript n) = n"
  apply (auto simp add:NAME_type_rel_def MkName_def nm_set.rep_eq fmap_upd.rep_eq)
  sledgehammer
oops
*)

end