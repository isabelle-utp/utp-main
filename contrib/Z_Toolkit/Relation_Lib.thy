section \<open> Meta-theory for Relation Library \<close>

theory Relation_Lib
  imports
    Countable_Set_Extra Positive Infinity Enum_Type Record_Default_Instance Def_Const
    Relation_Extra Partial_Fun Partial_Inj Finite_Fun Finite_Inj Total_Fun List_Extra
begin 

text \<open> This theory marks the boundary between reusable library utilities and the creation of the
  Z notation. We avoid overriding any HOL syntax up until this point, but we do supply some optional 
  bundles. \<close>

lemma if_eqE [elim!]: "\<lbrakk> (if b then e else f) = v; \<lbrakk> b; e = v \<rbrakk> \<Longrightarrow> P; \<lbrakk> \<not> b; f = v \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (cases b, auto)

bundle Z_Type_Syntax
begin

type_notation bool ("\<bool>")
type_notation nat ("\<nat>")
type_notation int ("\<int>")
type_notation rat ("\<rat>")
type_notation real ("\<real>")

type_notation set ("\<bbbP> _" [999] 999)

type_notation tfun (infixr "\<rightarrow>" 0)

notation Pow ("\<bbbP>")
notation Fpow ("\<bbbF>")

end

end