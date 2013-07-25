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

class tag =
  fixes tagName :: "'a \<Rightarrow> string"
  assumes tagUnit: "(x::'a) = y"
begin

definition tag :: "'a" where
"tag = (THE x. True)"

end

typedef ('t::tag, 'a::vbasic, 'r) field =
  "{(f :: 'r \<Rightarrow> 'a, t :: 'a set). \<exists> x. x \<in> t}"
  by (auto)

setup_lifting type_definition_field

lift_definition FieldProj :: 
  "('t::tag, 'a::vbasic, 'r) field \<Rightarrow> ('r \<Rightarrow> 'a)" is "fst"
  by (simp)

lift_definition FieldType ::
  "('t::tag, 'a::vbasic, 'r) field \<Rightarrow> 'a set" is "snd"
  by (simp)

definition MkField :: "'t::tag itself \<Rightarrow> ('r \<Rightarrow> 'a) \<Rightarrow> 'a::vbasic set \<Rightarrow> ('t,'a,'r) field" where
"MkField t f x = Abs_field (f, x)"

type_synonym ('t, 'a, 'r) tagged = "('t itself * 'a set * 'r itself)"

definition UnitField :: "('t::tag, 'a::vbasic, 'r) field \<Rightarrow> ('t, ('a * unit), 'r) tagged" where
"UnitField f = (TYPE('t), (FieldType f \<times> UNIV), TYPE('r))"

definition ConsField :: 
  "('t::tag, 'a::vbasic, 'r) field \<Rightarrow> ('t, 'b, 'r) tagged \<Rightarrow>  ('t, ('a*'b), 'r) tagged" where
"ConsField f t = (TYPE('t), FieldType f \<times> fst (snd t), TYPE('r))"

definition FinishField :: "('t, 'r, 'r) tagged \<Rightarrow> 'r set" where
"FinishField \<equiv> fst \<circ> snd"

abbreviation "field1  \<equiv> fst"
abbreviation "field2  \<equiv> fst \<circ> snd"
abbreviation "field3  \<equiv> fst \<circ> snd \<circ> snd"
abbreviation "field4  \<equiv> fst \<circ> snd \<circ> snd \<circ> snd"
abbreviation "field5  \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "field6  \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "field7  \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "field8  \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "field9  \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "field10 \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "field11 \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"
abbreviation "field12 \<equiv> fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd"

definition MkRec :: "('t, 'a, 'r) tagged \<Rightarrow> 'r vdme \<Rightarrow> 'r vdme" where
"MkRec t r = r"

nonterminal vty_fields and vrec

syntax
  "_vty_fields"    :: "('t, 'a, 'r) field \<Rightarrow> vty_fields => vty_fields" ("_,/ _")
  "_vty_field"     :: "('t, 'a, 'r) field \<Rightarrow> vty_fields" ("_")
  "_vty_record"    :: "vty_fields => vty"    ("[(_)]")
  "_vexpr_rproj"   :: "pexpr \<Rightarrow> ('t, 'a, 'r) field \<Rightarrow> pexpr" ("_\<cdot>_")
  "_vexpr_mk_rec"  :: "('t, 'a, 'r) tagged \<Rightarrow> pexprs \<Rightarrow> pexpr" ("mk~_'(_')") 

translations
  "_vty_fields x xs" == "CONST ConsField x xs"
  "_vty_field x" == "CONST UnitField x"
  "_vty_record x" == "CONST FinishField x"
  "_vexpr_rproj r f" == "CONST Op1D' (CONST FieldProj f) r"
  "_vexpr_mk_rec t e" == "CONST MkRec t (_vexpr_prod e)"

abbreviation "Period   \<equiv> \<parallel>@nat\<parallel>"
abbreviation "ExpertId \<equiv> \<parallel>@nat\<parallel>"
abbreviation "Qualification \<equiv> \<parallel><''Elec''> | <''Mech''> | <''Bio''> | <''Chem''>\<parallel>"

typedef Expert_Tag = "{True}" by auto
instantiation Expert_Tag :: tag
begin

definition "tagName_Expert_Tag (x::Expert_Tag) = ''Expert''"

instance 
  by (intro_classes, metis (full_types) Abs_Expert_Tag_cases singleton_iff)
end

abbreviation "expertid \<equiv> MkField TYPE(Expert_Tag) field1 \<parallel>@ExpertId\<parallel>"
abbreviation "quali    \<equiv> MkField TYPE(Expert_Tag) field2 \<parallel>@set of @Qualification\<parallel>"
abbreviation "Expert \<equiv> ConsField expertid (UnitField quali)"

term "MkRec Expert"

term "|mk~Expert(1,{})|"

term "|(mk_(1, {}) : [expertid,quali])|"

term "\<parallel>[expertid, quali]\<parallel>"

end