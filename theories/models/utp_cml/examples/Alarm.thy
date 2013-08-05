theory Alarm
imports "../utp_vdm"
begin

abbreviation "Period   \<equiv> \<parallel>@token\<parallel>"
abbreviation "ExpertId \<equiv> \<parallel>@token\<parallel>"
abbreviation "Qualification \<equiv> \<parallel><''Elec''> | <''Mech''> | <''Bio''> | <''Chem''>\<parallel>"

text {* Expert Record *}

typedef Expert_Tag = "{True}" by auto
instantiation Expert_Tag :: tag
begin

definition "tagName_Expert_Tag (x::Expert_Tag) = ''Expert''"

instance 
  by (intro_classes, metis (full_types) Abs_Expert_Tag_cases singleton_iff)
end

abbreviation "expertid_fld \<equiv> MkField TYPE(Expert_Tag) #1 \<parallel>@ExpertId\<parallel>"
abbreviation "expertid     \<equiv> SelectRec expertid_fld"
abbreviation "quali_fld    \<equiv> MkField TYPE(Expert_Tag) #2 \<parallel>@set of @Qualification\<parallel>"
abbreviation "quali        \<equiv> SelectRec quali_fld"

abbreviation "Expert \<equiv> \<parallel>[expertid_fld, quali_fld] inv ex == ^ex^.quali <> {}\<parallel>"

abbreviation "mk_Expert      \<equiv> MkRec Expert"

text {* Alarm Record *}

typedef Alarm_Tag = "{True}" by auto
instantiation Alarm_Tag :: tag
begin

definition "tagName_Alarm_Tag (x::Alarm_Tag) = ''Alarm''"

instance 
  by (intro_classes, metis (full_types) Abs_Alarm_Tag_cases singleton_iff)
end

abbreviation "alarmtext_fld \<equiv> MkField TYPE(Alarm_Tag) #1 \<parallel>@seq of @char\<parallel>"
abbreviation "alarmtext     \<equiv> SelectRec expertid_fld"
abbreviation "quali'_fld    \<equiv> MkField TYPE(Alarm_Tag) #2 \<parallel>@set of @Qualification\<parallel>"
abbreviation "quali'        \<equiv> SelectRec quali'_fld"

abbreviation "Alarm \<equiv> \<parallel>[alarmtext_fld, quali'_fld]\<parallel>"

abbreviation "mk_Alarm      \<equiv> MkRec Alarm"


term "|mk_Expert(mk_token({1,2}),{}).expertid|"

(*
definition "Schedule = \<parallel>(@map @Period to @set of @Expert) 
                         inv sch == forall x & true\<parallel>\<^sub>t"
*)

end