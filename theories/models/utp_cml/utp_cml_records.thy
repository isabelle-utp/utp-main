(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_records.thy                                                  *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* CML records *}

theory utp_cml_records
imports 
  utp_cml_expr
  utp_cml_functions
  utp_cml_types
begin

default_sort type

text {* CML records are formalised as tagged types, unit types which carry a string. *}

class tag =
  fixes tagName :: "'a \<Rightarrow> string"
  assumes tagUnit: "(x::'a) = y"
begin

definition tag :: "'a" where
"tag = (THE x. True)"

end

text {* A CML field over a given tag, field type and record type consists of
        an accessor function and CML type. The CML type must not be empty. *}

typedef ('t::tag, 'a::vbasic, 'r) field =
  "UNIV :: (('r \<Rightarrow> 'a) * 'a set) set"
  by (auto)

declare Abs_field_inverse [simp]

setup_lifting type_definition_field

lift_definition FieldProj :: 
  "('t::tag, 'a::vbasic, 'r) field \<Rightarrow> ('r \<Rightarrow> 'a)" is "fst" .

declare FieldProj.rep_eq [simp]

lift_definition FieldType ::
  "('t::tag, 'a::vbasic, 'r) field \<Rightarrow> 'a set" is "snd" .

declare FieldType.rep_eq [simp]

(* declare MkField_def [eval,evalp] *)

typedef ('t, 'a, 'r) tagged = "UNIV :: 'a set set"
  by (auto)

declare Rep_tagged [simp]
declare Abs_tagged_inverse [simp]
declare Abs_tagged_inject [simp]
declare Rep_tagged_inverse [simp]
declare Rep_tagged_inject [simp]

typedef ('t, 'r) rec = "UNIV :: 'r set"
  by (auto)

declare Rep_rec [simp]
declare Abs_rec_inverse [simp]
declare Abs_rec_inject [simp]
declare Rep_rec_inverse [simp]
declare Rep_rec_inject [simp]

(* setup_lifting type_definition_rec *)

instantiation rec :: (tag, vbasic) vbasic
begin

definition Inject_rec :: "('a, 'b) rec \<Rightarrow> vbasic" where
"Inject_rec r = TagI (tagName (tag :: 'a)) (Inject (Rep_rec r))"

definition Type_rec :: "('a, 'b) rec itself \<Rightarrow> vbasict" where
"Type_rec rt = TagBT (tagName (tag :: 'a)) BTYPE('b)"

instance 
  apply (intro_classes)
  apply (auto simp add:Inject_rec_def Type_rec_def Rep_rec_inject image_def)
  apply (metis Project_Inject Rep_rec_cases UNIV_I)
done
end

instantiation rec :: (type, linorder) linorder
begin

definition less_eq_rec :: "('a, 'b) rec \<Rightarrow> ('a, 'b) rec \<Rightarrow> bool" where
"r1 \<le> r2 = (Rep_rec r1 \<le> Rep_rec r2)"

definition less_rec :: "('a, 'b) rec \<Rightarrow> ('a, 'b) rec \<Rightarrow> bool" where
"r1 < r2 = (Rep_rec r1 < Rep_rec r2)"

instance
  apply (intro_classes)
  apply (auto simp add:less_eq_rec_def less_rec_def)
  apply (metis Rep_rec_inject less_le)
done
end

definition UnitField :: "('t::tag, 'a::vbasic, 'r) field \<Rightarrow> ('t, 'a, 'r) tagged" where
"UnitField f = Abs_tagged (FieldType f)"

(* declare UnitField_def [eval,evalp] *)

definition ConsField :: 
  "('t::tag, 'a::vbasic, 'r) field \<Rightarrow> 
   ('t, 'b, 'r) tagged \<Rightarrow>  
   ('t, ('a * 'b), 'r) tagged" where
"ConsField f t = Abs_tagged (FieldType f \<times> Rep_tagged t)"

(* declare ConsField_def [eval,evalp] *)

definition MkTagRec :: "('t::tag, 'r::vbasic, 'r) tagged \<Rightarrow> 'r \<Rightarrow> ('t, 'r) rec" where
"MkTagRec t = Abs_rec"

(* declare MkTagRec_def [eval,evalp] *)

definition MkField :: "('t::tag, 'r) rec set \<Rightarrow> ('r \<Rightarrow> 'a) \<Rightarrow> 'a::vbasic set \<Rightarrow> ('t,'a,'r) field" where
"MkField t f x = Abs_field (f, x)"

definition TermField :: "('t::tag, 'r::vbasic, 's) tagged \<Rightarrow> ('t, 'r) rec set" where
"TermField t \<equiv> Abs_rec ` Rep_tagged t"

abbreviation FinishField :: "('t::tag, 'r::vbasic, 'r) tagged \<Rightarrow> ('t, 'r) rec set" where
"FinishField \<equiv> TermField"

definition RecMaximalType :: "'a set \<Rightarrow> 't::tag itself \<Rightarrow> ('t, 'a) rec set"
where "RecMaximalType xs t = Abs_rec ` xs"

(*
definition FinishField :: "('t::tag, 'r::vbasic, 'r) tagged \<Rightarrow> ('t, 'r) rec set" where
"FinishField t \<equiv> MkTagRec t ` Rep_tagged t"
*)

(* declare FinishField_def [eval,evalp] *)

definition MkRec :: "('t::tag, 'r::vbasic) rec set \<Rightarrow> 'r \<Rightarrow> ('t, 'r) rec cmle" where
"MkRec t r = LitD (Abs_rec r)"

declare MkRec_def [eval, evalp]

definition SelectRec :: 
  "('t::tag, 'a::vbasic, 'r) field \<Rightarrow> 
   ('t, 'r) rec \<Rightarrow> 'a" where
"SelectRec f r = (fst (Rep_field f)) (Rep_rec r)"

(* declare SelectRec_def [eval,evalp] *)

nonterminal vty_fields and vrec

syntax
  "_vty_fields"    :: "('t, 'a, 'r) field \<Rightarrow> vty_fields => vty_fields" ("_,/ _")
  "_vty_field"     :: "('t, 'a, 'r) field \<Rightarrow> vty_fields" ("_")
  "_vty_record"    :: "vty_fields => vty"    ("[(_)]")

translations
  "_vty_fields x xs" == "CONST ConsField x xs"
  "_vty_field x" == "CONST UnitField x"
  "_vty_record x" == "CONST FinishField x"

lemma Abs_rec_cons_type [simp]:
  "Abs_rec (x, y) \<in> TermField (ConsField a b)
   \<longleftrightarrow> (x \<in> FieldType a \<and> Abs_rec y \<in> TermField b)"
  by (auto simp add:TermField_def MkTagRec_def ConsField_def UnitField_def)

lemma Abs_rec_unit_type [simp]:
  "Abs_rec x \<in> TermField (UnitField a)
   \<longleftrightarrow> x \<in> FieldType a"
  by (auto simp add:TermField_def MkTagRec_def ConsField_def UnitField_def)

lemma [simp]: "Rep_field (MkField t f x) = (f, x)"
  by (simp add:MkField_def)

lemma SelectRec_simp [simp]:
  "SelectRec (MkField t f u) (Abs_rec x) = f x"
  by (simp add:SelectRec_def)

(*
lemma SelectRec_1_2 [simp]: 
  "SelectRec (MkField g #[1] t u) (Abs_rec (v1, r)) = v1"
  by (simp add:SelectRec_def vprod_simps)

lemma SelectRec_2 [simp]: 
  "SelectRec (MkField g #[2] t u) (Abs_rec (v1, v2, r)) = v2"
  by (simp add:SelectRec_def vprod_simps)

lemma SelectRec_3 [simp]: 
  "SelectRec (MkField g #[3] t u) (Abs_rec (v1, v2, v3, r)) = v3"
  by (simp add:SelectRec_def vprod_simps)

lemma SelectRec_4 [simp]: 
  "SelectRec (MkField g #[4] t u) (Abs_rec (v1, v2, v3, v4, r)) = v4"
  by (simp add:SelectRec_def vprod_simps)

lemma SelectRec_5 [simp]: 
  "SelectRec (MkField g #[5] t u) (Abs_rec (v1, v2, v3, v4, v5, r)) = v5"
  by (simp add:SelectRec_def vprod_simps)

lemma SelectRec_6 [simp]: 
  "SelectRec (MkField g #[6] t u) (Abs_rec (v1, v2, v3, v4, v5, v6, r)) = v6"
  by (simp add:SelectRec_def vprod_simps)

lemma SelectRec_7 [simp]: 
  "SelectRec (MkField g #[7] t u) (Abs_rec (v1, v2, v3, v4, v5, v6, v7, r)) = v7"
  by (simp add:SelectRec_def vprod_simps)

lemma SelectRec_8 [simp]: 
  "SelectRec (MkField g #[8] t u) (Abs_rec (v1, v2, v3, v4, v5, v6, v7, v8, r)) = v8"
  by (simp add:SelectRec_def vprod_simps)
*)

(*
typedef MyRec_Tag = "{True}" by auto
instantiation MyRec_Tag :: tag
begin
definition "tagName_MyRec_Tag (x::MyRec_Tag) = ''MyRec''"
instance 
  by (intro_classes, metis (full_types) Abs_MyRec_Tag_cases singleton_iff)
end

text {* Next we create a collection of fields associated with the tag, and give each
        the position in record and its VDM type. *}

abbreviation "maxty_MyRec \<equiv> RecMaximalType \<parallel>@nat*@nat\<parallel> TYPE(MyRec_Tag)"

abbreviation "hgr_fld \<equiv> MkField maxty_MyRec #[1] \<parallel>@nat\<parallel>"
abbreviation "lwr_fld \<equiv> MkField maxty_MyRec #[2] \<parallel>@nat\<parallel>"

abbreviation "hgr \<equiv> SelectRec hgr_fld"
abbreviation "lwr  \<equiv> SelectRec lwr_fld"

definition "MyType = \<parallel>[ hgr_fld, lwr_fld] inv x == ^x^.hgr > ^x^.lwr\<parallel>"

term "MyType"

definition "mk_MyType \<equiv> MkRec MyType"

term "|mk_MyType(2,1)|"
term "|mk_MyType(2,1).lwr|"

lemma "|mk_MyType(2,1) hasType @MyType| = |true|"
  by (simp add:evalp mk_MyType_def MyType_def vprod_simps)

lemma "|forall x:@nat @ mk_MyType(^x^,0) hasType @MyType| = |false|"
  by (auto simp add:evalp mk_MyType_def MyType_def vprod_simps)
*)

end