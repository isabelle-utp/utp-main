(*  Title:      JinjaDCI/Common/Type.thy

    Author:     David von Oheimb, Tobias Nipkow, Susannah Mansky
    Copyright   1999 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory Common/Type.thy by David von Oheimb and Tobias Nipkow
*)

section \<open> Jinja types \<close>        

theory Type imports Auxiliary begin

type_synonym cname = string \<comment> \<open>class names\<close>
type_synonym mname = string \<comment> \<open>method name\<close>
type_synonym vname = string \<comment> \<open>names for local/field variables\<close>

definition Object :: cname
where
  "Object \<equiv> ''Object''"

definition this :: vname
where
  "this \<equiv> ''this''"

definition clinit :: "string" where "clinit = ''<clinit>''"
definition init :: "string" where "init = ''<init>''"

definition start_m :: "string" where "start_m = ''<start>''"
definition Start :: "string" where "Start = ''<Start>''"

lemma start_m_neq_clinit [simp]: "start_m \<noteq> clinit" by(simp add: start_m_def clinit_def)
lemma Object_neq_Start [simp]: "Object \<noteq> Start" by(simp add: Object_def Start_def)
lemma Start_neq_Object [simp]: "Start \<noteq> Object" by(simp add: Object_def Start_def)

\<comment> \<open>field/method static flag\<close>

datatype staticb = Static | NonStatic

\<comment> \<open>types\<close>
datatype ty
  = Void          \<comment> \<open>type of statements\<close>
  | Boolean
  | Integer
  | NT            \<comment> \<open>null type\<close>
  | Class cname   \<comment> \<open>class type\<close>

definition is_refT :: "ty \<Rightarrow> bool"
where
  "is_refT T  \<equiv>  T = NT \<or> (\<exists>C. T = Class C)"

lemma [iff]: "is_refT NT"
(*<*)by(simp add:is_refT_def)(*>*)

lemma [iff]: "is_refT(Class C)"
(*<*)by(simp add:is_refT_def)(*>*)

lemma refTE:
  "\<lbrakk>is_refT T; T = NT \<Longrightarrow> P; \<And>C. T = Class C \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
(*<*)by (auto simp add: is_refT_def)(*>*)

lemma not_refTE:
  "\<lbrakk> \<not>is_refT T; T = Void \<or> T = Boolean \<or> T = Integer \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
(*<*)by (cases T, auto simp add: is_refT_def)(*>*)

end
