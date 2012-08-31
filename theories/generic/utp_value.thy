(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/generic/utp_value.thy                                            *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Abstract Values *}

theory utp_value
imports "../utp_common" "../utp_sorts2"
begin

subsection {* Locale @{term "VALUE"} *}

locale VALUE =
-- {* Typing Relation *}
  fixes type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)
-- {* A type must not be empty. *}
  assumes type_non_empty : "\<exists> x . x : t"
  and     type_rel_total : "\<exists> t . x : t"
begin

subsection {* Universe *}

definition VALUE :: "'VALUE set" where
"VALUE = UNIV"

subsection {* Carrier Set *}

definition carrier :: "'TYPE \<Rightarrow> 'VALUE set" where
"carrier t = {x . x : t}"

theorem carrier_non_empty :
"\<forall> t . carrier t \<noteq> {}"
apply (auto simp: carrier_def type_non_empty)
done

theorem carrier_member [intro!] :
"x : t \<Longrightarrow> x \<in> carrier t"
apply (auto simp: carrier_def type_non_empty)
done

subsection {* Type Coercion *}

definition coerce_type :: "'TYPE \<Rightarrow> 'VALUE \<Rightarrow> 'VALUE" where
"coerce_type t v \<equiv> if (v : t) then v else (SOME v. v : t)"

lemma coerce_type: "coerce_type t v : t"
  apply(simp add:coerce_type_def)
  apply(clarify)
  apply(rule someI_ex)
  apply(rule type_non_empty)
done

lemma coerce_value: "v : t \<Longrightarrow> coerce_type t v = v"
  by (simp add:coerce_type_def)

subsection {* Set Coercion *}

definition coerce_set :: "'VALUE set \<Rightarrow> 'VALUE \<Rightarrow> 'VALUE" where
"coerce_set s v \<equiv> if (v \<in> s) then v else (SOME v. v \<in> s)"

lemma coerce_set: "\<exists>v. v \<in> s \<Longrightarrow> coerce_set s x \<in> s"
  by (auto simp add:coerce_set_def)

lemma coerce_set_type: "\<lbrakk> \<forall>x \<in> s. x : t; \<exists>x. x \<in> s \<rbrakk>  \<Longrightarrow> (coerce_set s v) : t"
  by (auto simp add:coerce_set_def)

subsection {* Value Sets *}

definition set_type_rel :: "'VALUE set \<Rightarrow> 'TYPE \<Rightarrow> bool" where
"set_type_rel s t = (\<forall> x \<in> s . x : t)"

notation set_type_rel (infix ":\<subseteq>" 50)

theorem set_type_rel_empty [simp] :
"{} :\<subseteq> t"
apply (auto simp: set_type_rel_def)
done

theorem set_type_rel_insert [simp] :
"(insert x s) :\<subseteq> t \<longleftrightarrow> (x : t \<and> s :\<subseteq> t)"
apply (auto simp: set_type_rel_def)
done

subsection {* Indexable Types *}

definition IdxType :: "'TYPE \<Rightarrow> bool" where
"IdxType t \<longleftrightarrow> IdxSet (carrier t)"

subsection {* Theorems *}

theorem IdxType_IdxSet [simp] :
"\<lbrakk>s :\<subseteq> t; IdxType t\<rbrakk> \<Longrightarrow> IdxSet s"
apply (simp add: IdxType_def)
apply (simp add: set_type_rel_def)
apply (subgoal_tac "s \<subseteq> carrier t")
apply (simp)
apply (auto simp: carrier_def)
done
end

locale BOOL_VALUE = VALUE "type_rel" 
  for     type_rel :: "'VALUE :: BOOL_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50) +  
  fixes   BoolType :: "'TYPE" ("\<bool>") 
  assumes BoolSort_type: "y : \<bool> \<longleftrightarrow> y \<in> BoolSort"

locale INT_VALUE  = VALUE "type_rel"
  for     type_rel :: "'VALUE :: INT_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50) + 
  fixes   IntType :: "'TYPE" ("\<int>")
  assumes IntSort_type: "y : \<int> \<longleftrightarrow> y \<in> IntSort"

(*
locale STRING_VALUE  = VALUE "type_rel"
  for     type_rel :: "'VALUE :: STRING_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50) + 
  fixes   StringType :: "'TYPE"
  assumes IsString_type: "y : StringType \<longleftrightarrow> IsString y"
*)

locale FUNCTION_VALUE = VALUE "type_rel"
  for     type_rel ::  "'VALUE :: FUNCTION_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50) + 
  fixes   FuncType ::  "'TYPE \<Rightarrow> 'TYPE \<Rightarrow> 'TYPE" (infixr "=p\<Rightarrow>" 60)
  and     in_type  ::  "'TYPE \<Rightarrow> 'TYPE"
  and     out_type ::  "'TYPE \<Rightarrow> 'TYPE"
  assumes WF_FUNC_type: "\<And> f a b. \<lbrakk> MkFunc f : a =p\<Rightarrow> b \<rbrakk> \<Longrightarrow> f \<in> WF_FUNC"
  and     MkFunc_type: "f ` carrier a \<subseteq> carrier b \<Longrightarrow> MkFunc f : a =p\<Rightarrow> b"
  and     FuncApp_type: "\<And> f. \<lbrakk> f : a =p\<Rightarrow> b; x : a \<rbrakk> \<Longrightarrow> f $ x : b"
  and     FuncType_in[simp]:  "in_type  (a =p\<Rightarrow> b) = a"
  and     FuncType_out[simp]: "out_type (a =p\<Rightarrow> b) = b"

locale PARTIAL_FUNCTION_VALUE = VALUE "type_rel"
  for     type_rel  :: "'VALUE :: PARTIAL_FUNCTION_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50) + 
  fixes   PFuncType :: "'TYPE \<Rightarrow> 'TYPE \<Rightarrow> 'TYPE" (infixr "~p\<Rightarrow>" 60)
  and     pin_type  :: "'TYPE \<Rightarrow> 'TYPE"
  and     pout_type :: "'TYPE \<Rightarrow> 'TYPE"
  assumes WF_PFUNC_type: "\<And> f a b. \<lbrakk> MkPFunc f : a ~p\<Rightarrow> b \<rbrakk> \<Longrightarrow> f \<in> WF_PFUNC"
(*  and     MkPFunc_type: "ran (f |` carrier a) \<subseteq> carrier b \<Longrightarrow> MkPFunc f : a ~p\<Rightarrow> b" *)
  and     MkPFunc_type: "\<lbrakk> dom f \<subseteq> carrier a; ran f \<subseteq> carrier b \<rbrakk>  \<Longrightarrow> MkPFunc f : a ~p\<Rightarrow> b"
  and     AppPFunc_type: "\<And> f. \<lbrakk> f : a ~p\<Rightarrow> b; x \<in> dom (DestPFunc f)  \<rbrakk> 
                          \<Longrightarrow> f $$ x : b"
  and     AppPFunc_ntype: "\<And> f. \<lbrakk> f : a ~p\<Rightarrow> b;  \<not> (v : a) \<rbrakk> \<Longrightarrow> DestPFunc f v = None"
  and     PFuncType_in[simp]:  "pin_type  (a ~p\<Rightarrow> b) = a"
  and     PFuncType_out[simp]: "pout_type (a ~p\<Rightarrow> b) = b"

locale BASIC_VALUE = FUNCTION_VALUE "type_rel" + PARTIAL_FUNCTION_VALUE "type_rel" + BOOL_VALUE "type_rel" (* + INT_VALUE "type_rel" + STRING_VALUE "type_rel" *)
  for type_rel :: "'VALUE :: CORE_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)

end
