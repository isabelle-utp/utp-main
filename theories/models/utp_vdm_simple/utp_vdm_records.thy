(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_records.thy                                                  *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* VDM records *}

theory utp_vdm_records
imports 
  utp_vdm_expr
  utp_vdm_types
begin

default_sort type

text {* VDM records are formalised as tagged types, unit types which carry a string. *}

class tag =
  fixes tagName :: "'a \<Rightarrow> string"
  assumes tagUnit: "(x::'a) = y"
begin

definition tag :: "'a" where
"tag = (THE x. True)"

end

text {* A VDM field over a given tag, field type and record type consists of
        an accessor function and VDM type. The VDM type must not be empty. *}

typedef ('t::tag, 'a::vbasic, 'r) field =
  "UNIV :: (('r \<Rightarrow> 'a) * 'a set) set"
  by (auto)

declare Abs_field_inverse [simp]

setup_lifting type_definition_field

lift_definition FieldProj :: 
  "('t::tag, 'a::vbasic, 'r) field \<Rightarrow> ('r \<Rightarrow> 'a)" is "fst" .

lift_definition FieldType ::
  "('t::tag, 'a::vbasic, 'r) field \<Rightarrow> 'a set" is "snd" .

definition MkField :: "'t::tag itself \<Rightarrow> ('r \<Rightarrow> 'a) \<Rightarrow> 'a::vbasic set \<Rightarrow> ('t,'a,'r) field" where
"MkField t f x = Abs_field (f, x)"

declare MkField_def [eval,evalp]

typedef ('t, 'a, 'r) tagged = "{xs :: 'a set. \<exists> x. x \<in> xs}"
  by (auto)

typedef ('t, 'r) rec = "UNIV :: 'r set"
  by (auto)

declare Abs_rec_inverse [simp]

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

definition UnitField :: "('t::tag, 'a::vbasic, 'r) field \<Rightarrow> ('t, ('a * unit), 'r) tagged" where
"UnitField f = Abs_tagged (FieldType f \<times> UNIV)"

declare UnitField_def [eval,evalp]

definition ConsField :: 
  "('t::tag, 'a::vbasic, 'r) field \<Rightarrow> 
   ('t, 'b, 'r) tagged \<Rightarrow>  
   ('t, ('a * 'b), 'r) tagged" where
"ConsField f t = Abs_tagged (FieldType f \<times> Rep_tagged t)"

declare ConsField_def [eval,evalp]

definition MkTagRec :: "('t::tag, 'r::vbasic, 'r) tagged \<Rightarrow> 'r \<Rightarrow> ('t, 'r) rec" where
"MkTagRec t = Abs_rec"

declare MkTagRec_def [eval,evalp]

definition FinishField :: "('t::tag, 'r::vbasic, 'r) tagged \<Rightarrow> ('t, 'r) rec set" where
"FinishField t \<equiv> MkTagRec t ` Rep_tagged t"

declare FinishField_def [eval,evalp]

definition MkRec :: "('t, 'r) rec set \<Rightarrow> 'r \<Rightarrow> ('t, 'r) rec" where
"MkRec t = Abs_rec"

definition SelectRec :: 
  "('t::tag, 'a::vbasic, 'r) field \<Rightarrow> 
   ('t, 'r) rec \<Rightarrow> 'a" where
"SelectRec f r = (fst (Rep_field f)) (Rep_rec r)"

declare SelectRec_def [eval,evalp]

nonterminal vty_fields and vrec

syntax
  "_vty_fields"    :: "('t, 'a, 'r) field \<Rightarrow> vty_fields => vty_fields" ("_,/ _")
  "_vty_field"     :: "('t, 'a, 'r) field \<Rightarrow> vty_fields" ("_")
  "_vty_record"    :: "vty_fields => vty"    ("[(_)]")

translations
  "_vty_fields x xs" == "CONST ConsField x xs"
  "_vty_field x" == "CONST UnitField x"
  "_vty_record x" == "CONST FinishField x"


(*
lemma "|mk_Expert(1,{}).expertid|= |1|"
  apply (auto simp add:evalp)
*)


(*
term "|(mk_Expert(1, {}) : [expertid,quali])|"
term "\<parallel>[expertid, quali]\<parallel>"
*)

end