(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_records.thy                                                  *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* VDM records *}

theory utp_vdm_records
imports 
  utp_vdm_expr
begin

definition SelectRec :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b option" where
"SelectRec f r = Some (f r)"

abbreviation "SelectD f r \<equiv> Op1D (SelectRec f) r"

lemma EvalPE_SelectD [eval, evalp]: 
  "\<D> (\<lbrakk>r\<rbrakk>\<^sub>* b) \<Longrightarrow> \<lbrakk>SelectD f r\<rbrakk>\<^sub>*b = Some (f (the (\<lbrakk>r\<rbrakk>\<^sub>* b)))"
  by (simp add:evalp SelectRec_def)

definition MakeD :: "('a \<times> unit \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b option" where
"MakeD f = (\<lambda> x. Some (f (x, ())))"

lemma MakeD_defined [defined]:
  "\<D> (MakeD f x)"
  by (simp add:MakeD_def)

syntax
  "_vexpr_rproj"   :: "pexpr \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> pexpr" ("_\<cdot>_")

translations
  "_vexpr_rproj r f"           == "(CONST SelectD f) r"

record myrec1 =
  tr1f1 :: nat
  tr1f2 :: string
  tr1f3 :: "char fset"

syntax
  "_vexpr_mk_rec1"   :: "pexpr \<Rightarrow> pexpr" ("mk'_myrec1 _")



translations
  "_vexpr_mk_rec1 x" == "CONST Op1D (CONST MakeD (CONST Abs_myrec1_ext)) x"

record test_record2 =
  tr2f1 :: nat
  tr2f2 :: string
  tr2f3 :: "char fset"
  tr2f4 :: "int"
  tr2f5 :: "string"

term "Rep_myrec1_ext"
term "Rep_test_record2_ext"


print_theorems

term "Rep_test_record_ext"

typ "myrec1"

typ "int * (nat * string)"

abbreviation TypeOf :: "'a \<Rightarrow> 'a itself" where
"TypeOf x \<equiv> TYPE('a)"

(*
locale tag_type_definition = type_definition Rep Abs UNIV
  for Rep :: "'a \<Rightarrow> 'b::vbasic" 
  and Abs :: "'b \<Rightarrow> 'a" 
begin

definition "Inject_typedef n x = TagI n (Inject (Rep x))"
definition "Type_typedef n = TagBT n (Type(TypeOf(Rep (undefined :: 'a)) :: 'b itself))"

lemma Inject_typedef_inj [intro]:
  "Inject_typedef n x = Inject_typedef n y \<Longrightarrow> x = y"
  by (simp add:Inject_typedef_def)

lemma range_Inject_typedef [simp]:
  "range (Inject_typedef n) = {x. x :\<^sub>b Type_typedef n \<and> \<D> x}"
  apply (auto simp add:Inject_typedef_def Type_typedef_def image_def)
  apply (rule_tac x="Abs (the (Project xa))" in exI)
  apply (metis Abs_inverse Project_Inject UNIV_I)
done
end

interpretation tag_type_definition "Rep_myrec1_ext" "Abs_myrec1_ext"
  by (intro_locales, simp add:type_definition_myrec1_ext)
*)

definition Inject_rec :: "string \<Rightarrow> 'a :: type \<Rightarrow> ('a \<Rightarrow> 'b :: vbasic) \<Rightarrow> vbasic" where
"Inject_rec n x Rep = TagI n (Inject (Rep x))"

definition Type_rec :: "char list \<Rightarrow> ('a :: type) itself \<Rightarrow> ('a \<Rightarrow> 'b :: vbasic) \<Rightarrow> vbasict" where
"Type_rec n (t :: 'a itself) Rep = TagBT n BTYPE('b)"

lemma Inject_rec_inj: 
  "\<lbrakk> Inject_rec n x Rep = Inject_rec n y Rep; \<And> x y. Rep x = Rep y \<Longrightarrow> x = y \<rbrakk> \<Longrightarrow>
     x = y"
  by (simp add:Inject_rec_def)

instantiation myrec1_ext :: (vbasic) vbasic
begin

definition "Inject_myrec1_ext x = Inject_rec ''myrec1'' x Rep_myrec1_ext"
definition "Type_myrec1_ext x = Type_rec ''myrec1'' x Rep_myrec1_ext"

instance
  apply (intro_classes)
  apply (auto simp add:Inject_myrec1_ext_def Type_myrec1_ext_def Type_rec_def Inject_rec_def Rep_myrec1_ext_inject image_def)
  apply (rule_tac x="Abs_myrec1_ext (the (Project xa))" in exI)
  apply (simp add: Abs_myrec1_ext_inverse[simplified])
done
end

instantiation myrec1_ext :: (DEFINED) DEFINED
begin

definition Defined_myrec1_ext :: "'a myrec1_scheme \<Rightarrow> bool" where
"Defined_myrec1_ext x = True"

instance ..

end

instantiation unit :: DEFINED
begin

definition "Defined_unit (x :: unit) = True"

instance ..

end

term "\<parallel>$x\<cdot>tr1f2\<parallel>"
term "\<parallel>($x,$y)\<parallel>"

end