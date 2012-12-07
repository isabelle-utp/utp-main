(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_value.thy                                                        *)
(* Authors: Frank Zeyda & Simon Foster, University of York (UK)               *)
(******************************************************************************)

header {* Value Locales *}

theory utp_value
imports "../utp_common" utp_sorts utp_types
begin

subsection {* Abstract Values *}

locale VALUE =
-- {* Typing Relation *}
  fixes type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)
-- {* A type must not be empty. *}
  assumes type_non_empty : "\<exists> x . x : t"
begin

subsection {* Universe *}

definition VALUE :: "'VALUE set" where
"VALUE = UNIV"

subsection {* Well-formed Values *}

definition WF_VALUE :: "'VALUE set" where
"WF_VALUE = {v . \<exists> t . v : t}"

theorem WF_VALUE_non_empty :
"WF_VALUE \<noteq> {}"
apply (simp add: WF_VALUE_def)
apply (insert type_non_empty)
apply (drule_tac x = "t" in meta_spec)
apply (clarify)
apply (rule_tac x = "x" in exI)
apply (rule_tac x = "t" in exI)
apply (assumption)
done

theorem WF_VALUE_member :
"(x \<in> WF_VALUE) \<longleftrightarrow> (\<exists> t . x : t)"
apply (simp add: WF_VALUE_def)
done

subsection {* Carrier Sets *}

definition carrier :: "'TYPE \<Rightarrow> 'VALUE set" where
"carrier t = {x . x : t}"

theorem carrier_non_empty :
"\<forall> t . carrier t \<noteq> {}"
apply (simp add: carrier_def type_non_empty)
done

theorem carrier_member :
"x \<in> (carrier t) \<longleftrightarrow> (x : t)"
apply (simp add: carrier_def)
done

theorem carrier_intro [intro] :
"(x : t) \<Longrightarrow> (x \<in> carrier t)"
apply (simp add: carrier_def)
done

theorem carrier_dest [dest] :
"(x \<in> carrier t) \<Longrightarrow> (x : t)"
apply (simp add: carrier_def)
done

theorem WF_VALUE_carrier_member [intro] :
"x \<in> carrier t \<Longrightarrow> x \<in> WF_VALUE"
apply (simp add: WF_VALUE_member)
apply (simp add: carrier_def)
apply (rule_tac x = "t" in exI)
apply (assumption)
done

subsection {* Type Set Carriers *}

definition carrier_types :: "'TYPE set \<Rightarrow> 'VALUE set" where
"carrier_types ts = \<Union> {carrier t | t . t \<in> ts}"

theorem carrier_types_member :
"x \<in> (carrier_types ts) \<longleftrightarrow> (\<exists> t \<in> ts . x \<in> carrier t)"
apply (simp add: carrier_types_def)
apply (safe)
apply (rule_tac x = "t" in bexI)
apply (assumption)+
apply (rule_tac x = "carrier t" in exI)
apply (simp)
apply (rule_tac x = "t" in exI)
apply (simp)
done

theorem carrier_types_monotonic :
"ts1 \<subseteq> ts2 \<Longrightarrow> (carrier_types ts1) \<subseteq> (carrier_types ts2)"
apply (simp add: carrier_types_def)
apply (clarsimp)
apply (rule_tac x = "carrier t" in exI)
apply (simp)
apply (rule_tac x = "t" in exI)
apply (simp)
apply (auto)
done

theorem WF_VALUE_carrier_types_member [intro] :
"x \<in> carrier_types ts \<Longrightarrow> x \<in> WF_VALUE"
apply (simp add: carrier_types_member)
apply (clarify)
apply (erule WF_VALUE_carrier_member)
done

theorem WF_VALUE_carrier_types :
"WF_VALUE = carrier_types UNIV"
apply (simp add: set_eq_iff)
apply (simp add: WF_VALUE_member)
apply (simp add: carrier_types_member)
apply (simp add: carrier_member)
done

subsection {* Value Sets *}

definition set_type_rel :: "'VALUE set \<Rightarrow> 'TYPE \<Rightarrow> bool" where
"set_type_rel s t = (\<forall> x \<in> s . x : t)"

notation set_type_rel (infix ":\<subseteq>" 50)

theorem set_type_rel_empty [simp] :
"{} :\<subseteq> t"
apply (simp add: set_type_rel_def)
done

theorem set_type_rel_insert [simp] :
"(insert x s) :\<subseteq> t \<longleftrightarrow> (x : t \<and> s :\<subseteq> t)"
apply (simp add: set_type_rel_def)
done

subsection {* Default Value *}

definition SomeValue :: "'TYPE \<Rightarrow> 'VALUE" where
"SomeValue t = (SOME x . x : t)"

theorem SomeValue_well_typed [simp] :
"(SomeValue t) : t"
apply (insert type_non_empty [where t = "t"])
apply (simp add: SomeValue_def)
apply (erule someI_ex)
done
end

subsection {* Bottom Values *}

locale BOT_VALUE =
  VALUE "type_rel"
-- {* Additional constraints are imposed via sort membership. *}
for type_rel :: "'VALUE :: BOT_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50) +
assumes bot_type [typing] : "bot : t"

subsection {* Boolean Values *}

locale BOOL_VALUE =
  BOT_VALUE "type_rel"
-- {* Additional constraints are imposed via sort membership. *}
for type_rel :: "'VALUE :: {BOOL_SORT, BOT_SORT} \<Rightarrow>
    'TYPE :: BOOL_TYPE \<Rightarrow> bool" (infix ":" 50) +
  assumes TypeLink : "\<And> x. \<lbrakk>\<D> x\<rbrakk> \<Longrightarrow> x : BoolType \<longleftrightarrow> x \<in> range MkBool"
begin

theorem MkBool_type [typing] :
"MkBool x : BoolType"
  by (simp add: Defined TypeLink)

theorem in_range_MkBool :
"\<lbrakk>x : BoolType; \<D> x\<rbrakk> \<Longrightarrow> x \<in> range MkBool"
  by (simp add: TypeLink)

theorem MkBool_cases :
"\<lbrakk>x : BoolType; \<D> x\<rbrakk> \<Longrightarrow> x = MkBool True \<or> x = MkBool False"
  by (metis (full_types) in_range_MkBool DestBool_inverse)

theorem DestBool_inverse :
"\<lbrakk>x : BoolType; \<D> x\<rbrakk> \<Longrightarrow> MkBool (DestBool x) = x"
  by (metis in_range_MkBool DestBool_inverse)
end
end