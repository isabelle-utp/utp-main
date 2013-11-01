theory utp_simple
imports 
  utp_base 
  Derive
begin

datatype SimpT = NtT | BlT
datatype SimpV = NtV nat | BlV bool | UdV SimpT

derive countable SimpT

type_synonym svar = "string * SimpT"

datatype SimpE = 
  PlE SimpE SimpE | MlE SimpE SimpE | LqE SimpE SimpE | LiE SimpV | VrE svar

datatype SimpP =
  AsP svar SimpE | SqP SimpP SimpP | WhP SimpE SimpP | SkP

fun typeV :: "SimpV \<Rightarrow> SimpT" where
"typeV (NtV x) = NtT" | 
"typeV (BlV x) = BlT" |
"typeV (UdV t) = t"

instantiation SimpV :: VALUE
begin

fun Defined_SimpV :: "SimpV \<Rightarrow> bool" where
"Defined_SimpV (NtV x) = True" |
"Defined_SimpV (BlV x) = True" |
"Defined_SimpV (UdV t) = False"

definition utype_rel_SimpV :: "SimpV \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_SimpV v t = (t = to_nat (typeV v))"

instance
  apply (intro_classes)
  apply (simp add: utype_rel_SimpV_def)
  apply (rule_tac x="NtV 0" in exI)
  apply (simp)
done
end

lemma [simp]: "x : t \<longleftrightarrow> t = embTYPE (typeV x)"
  apply (case_tac x, simp_all)
  apply (metis (full_types) Abs_UTYPE_inv Defined_SimpV.simps(1) Rep_UTYPE_inverse embTYPE_def typeV.simps(1) type_rel_def utype_rel_SimpV_def)
  apply (metis (full_types) Abs_UTYPE_inv Defined_SimpV.simps(2) Rep_UTYPE_inverse embTYPE_def typeV.simps(2) type_rel_def utype_rel_SimpV_def)
  apply (auto simp add:type_rel_def utype_rel_SimpV_def embTYPE_def)
  apply (metis Rep_UTYPE_inverse)
  apply (metis Abs_UTYPE_inv Defined_SimpV.simps(1) Defined_SimpV.simps(2) SimpT.exhaust typeV.simps(1) typeV.simps(2) utype_rel_SimpV_def)
done

instantiation SimpV :: BOOL_SORT
begin

fun MkBool_SimpV :: "bool \<Rightarrow> SimpV" where
"MkBool_SimpV x = BlV x"

fun DestBool_SimpV :: "SimpV \<Rightarrow> bool" where
"DestBool_SimpV (BlV x) = x"

definition BoolType_SimpV :: "SimpV UTYPE" where
"BoolType_SimpV = embTYPE BlT"

instance
  apply (intro_classes)
  apply (auto simp add:dcarrier_def BoolType_SimpV_def)
  apply (case_tac x)
  apply (simp_all add:image_def embTYPE_def)
  apply (metis Abs_UTYPE_inv Defined_SimpV.simps(1) Defined_SimpV.simps(2) SimpT.distinct(1) to_nat_split typeV.simps(1) typeV.simps(2) utype_rel_SimpV_def)
  apply (simp_all add:monotype_def)
done
end

fun typeE :: "SimpE \<Rightarrow> SimpT option" where
"typeE (PlE x y) = (case (typeE x, typeE y) of 
                      (Some NtT, Some NtT) \<Rightarrow> Some NtT |
                      (_, _) \<Rightarrow> None)" |
"typeE (MlE x y) = (case (typeE x, typeE y) of 
                      (Some NtT, Some NtT) \<Rightarrow> Some NtT |
                      (_, _) \<Rightarrow> None)" |
"typeE (LqE x y) = (case (typeE x, typeE y) of 
                      (Some NtT, Some NtT) \<Rightarrow> Some BlT |
                      (_, _) \<Rightarrow> None)" |
"typeE (LiE x) = Some (typeV x)" |
"typeE (VrE (n, t)) = Some t"

fun liftNNF :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> SimpV \<Rightarrow> SimpV \<Rightarrow> SimpV" where
"liftNNF f (NtV x) (NtV y) = NtV (f x y)" |
"liftNNF f _ _ = UdV NtT"

fun liftNBF :: "(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> SimpV \<Rightarrow> SimpV \<Rightarrow> SimpV" where
"liftNBF f (NtV x) (NtV y) = BlV (f x y)" |
"liftNBF f _ _ = UdV BlT"

fun sem_svar :: "svar \<Rightarrow> SimpV VAR" ("\<lbrakk>_\<rbrakk>\<^sub>v") where
"\<lbrakk>(n,t)\<rbrakk>\<^sub>v = MkPlain n (embTYPE t) False"

fun sem_SimpE :: "SimpE \<Rightarrow> SimpV WF_EXPRESSION" ("\<lbrakk>_\<rbrakk>\<^sub>e") where
"\<lbrakk>LiE v\<rbrakk>\<^sub>e = LitE v" |
"\<lbrakk>PlE x y\<rbrakk>\<^sub>e = Op2E (liftNNF (op +)) \<lbrakk>x\<rbrakk>\<^sub>e \<lbrakk>y\<rbrakk>\<^sub>e" |
"\<lbrakk>MlE x y\<rbrakk>\<^sub>e = Op2E (liftNNF (op *)) \<lbrakk>x\<rbrakk>\<^sub>e \<lbrakk>y\<rbrakk>\<^sub>e" |
"\<lbrakk>LqE x y\<rbrakk>\<^sub>e = Op2E (liftNBF (op \<le>)) \<lbrakk>x\<rbrakk>\<^sub>e \<lbrakk>y\<rbrakk>\<^sub>e" |
"\<lbrakk>VrE v\<rbrakk>\<^sub>e = VarE \<lbrakk>v\<rbrakk>\<^sub>v"

fun sem_SimpP :: "SimpP \<Rightarrow> SimpV WF_PREDICATE" ("\<lbrakk>_\<rbrakk>\<^sub>p") where
"\<lbrakk>SkP\<rbrakk>\<^sub>p = II" |
"\<lbrakk>SqP P Q\<rbrakk>\<^sub>p = \<lbrakk>P\<rbrakk>\<^sub>p ; \<lbrakk>Q\<rbrakk>\<^sub>p" |
"\<lbrakk>AsP x e\<rbrakk>\<^sub>p = \<lbrakk>x\<rbrakk>\<^sub>v :=\<^sub>R \<lbrakk>e\<rbrakk>\<^sub>e" |
"\<lbrakk>WhP e P\<rbrakk>\<^sub>p = IterP (ExprP \<lbrakk>e\<rbrakk>\<^sub>e) \<lbrakk>P\<rbrakk>\<^sub>p"

abbreviation "nv \<equiv> MkPlainP ''pv'' False TYPE(int) TYPE('m :: INT_SORT)"

lemma "`nv := \<guillemotleft>5\<guillemotright>; nv := $nv * \<guillemotleft>5\<guillemotright>` = `nv := \<guillemotleft>25\<guillemotright>`"
  apply (utp_rel_tac)
  apply (auto simp add: EvalR_AssignR_typed evalp closure typing defined unrest relcomp_unfold)
done

abbreviation "nv1 \<equiv> MkPlainP ''nv1'' False TYPE(int) TYPE('m :: INT_SORT)"
abbreviation "nv2 \<equiv> MkPlainP ''nv2'' False TYPE(int) TYPE('m :: INT_SORT)"


abbreviation 
  "prog1 \<equiv> `while ($nv1 < \<guillemotleft>5\<guillemotright>) do 
              (nv1 := $nv1 + \<guillemotleft>1\<guillemotright>)
            od`"
 
abbreviation "fv \<equiv> MkPlainP ''fact'' False TYPE(int) TYPE('m :: INT_SORT)"
abbreviation "cv \<equiv> MkPlainP ''c'' False TYPE(int) TYPE('m :: INT_SORT)"

(*
definition uv :: 
  "'a WF_PREDICATE \<Rightarrow> ('a VAR) set" where
"uv p = \<Union> {vs. UNREST vs p}"

lemma UNREST_uv_upper: 
  "xs \<sharp> P \<Longrightarrow> xs \<subseteq> uv P"
  by (auto simp add:uv_def)

lemma UNREST_uv_least:
  "(\<And>xs. xs \<sharp> P \<Longrightarrow> xs \<subseteq> zs) \<Longrightarrow> uv P \<subseteq> zs"
  by (auto simp add:uv_def)

fun enc_nat_set :: "nat set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"enc_nat_set xs lim n 0 = "

lemma "\<exists> f :: nat \<Rightarrow> nat. range f = vs"

lemma "\<lbrakk> \<forall> x \<in> xs. {x} \<sharp> P \<rbrakk> \<Longrightarrow> xs \<sharp> (P :: 'a WF_PREDICATE)"
  apply (subgoal_tac "(\<forall>x\<in>xs. \<forall>b1\<in>destPRED P. \<forall>b2. b1(x :=\<^sub>b \<langle>b2\<rangle>\<^sub>b x) \<in> destPRED P) 
       \<longleftrightarrow> (\<forall>b1\<in>destPRED P. \<forall>b2. \<forall>x\<in>xs. b1(x :=\<^sub>b \<langle>b2\<rangle>\<^sub>b x) \<in> destPRED P)")
  apply (auto simp add:UNREST_def)
  apply (drule_tac x="b1" in bspec, simp)
  apply (drule_tac x="b2" in spec)

proof -
  have 
    by (auto)
  apply (simp add:binding_override_on_def)

lemma UNREST_uv_upper: 
  "xs \<sharp> P \<longleftrightarrow> xs \<subseteq> uv P"
  apply (auto simp add:uv_def)
  apply (auto simp add:subset_eq)
  apply (auto simp add:UNREST_def)
  apply (auto simp add:binding_override_on_def override_on_def)


done
*)

(*
lemma 
  fixes P :: "'a WF_PREDICATE"
  assumes "\<forall>vs\<in>vss. vs \<sharp> P"
  shows "(\<Union> vss) \<sharp> P"
  using assms
  apply (auto simp add:UNREST_def binding_override_on_def override_on_def)
  apply (auto simp add:)
  apply (rule) back back back
  apply (drule bspec)
  defer
*)


abbreviation 
  "fact_prog \<equiv> 
     `cv := \<guillemotleft>0\<guillemotright>; fv := \<guillemotleft>0\<guillemotright>; while ($cv \<le> $nv) do ((fv := $fv * $cv); (cv := $cv + \<guillemotleft>1\<guillemotright>)) od`"

lemma "`nv1 := \<guillemotleft>0\<guillemotright> ; prog1` = `nv1 := \<guillemotleft>5\<guillemotright>`"
  apply (subst AssignR_SemiR_ty)
  apply (simp_all add:typing defined closure unrest)
  apply (subst IterP_unfold)
  apply (simp_all add:typing defined closure unrest usubst CondR_true AssignR_SemiR_ty)
  apply (subst IterP_unfold)
  apply (simp_all add:typing defined closure unrest usubst CondR_true AssignR_SemiR_ty)
  apply (subst IterP_unfold)
  apply (simp_all add:typing defined closure unrest usubst CondR_true AssignR_SemiR_ty)
  apply (subst IterP_unfold)
  apply (simp_all add:typing defined closure unrest usubst CondR_true AssignR_SemiR_ty)
  apply (subst IterP_unfold)
  apply (simp_all add:typing defined closure unrest usubst CondR_true AssignR_SemiR_ty)
  apply (subst IterP_unfold)
  apply (simp_all add:typing defined closure unrest usubst CondR_false AssignR_SemiR_ty)
done


lemma "`nv := \<guillemotleft>1\<guillemotright>; fact_prog` = undefined"
  apply (simp add:AssignR_SemiR_ty typing defined closure unrest)
  apply (subst IterP_unfold)
  apply (simp add:typing defined closure unrest usubst CondR_true AssignR_SemiR_ty)
  apply (simp add:typing defined closure unrest usubst CondR_true AssignR_SemiR_ty)
  apply (simp add:typing defined closure unrest usubst)


lemma "`nv1 := \<guillemotleft>0\<guillemotright> ; prog1` = `nv1 := \<guillemotleft>5\<guillemotright>`"
  apply (subst AssignR_SemiR_ty)
  apply (simp_all add:typing defined closure unrest)
  apply (subst IterP_unfold)
  apply (simp_all add:typing defined closure unrest usubst CondR_true AssignR_SemiR_ty)
  apply (subst IterP_unfold)
  apply (simp_all add:typing defined closure unrest usubst CondR_true AssignR_SemiR_ty)
  apply (subst IterP_unfold)
  apply (simp_all add:typing defined closure unrest usubst CondR_true AssignR_SemiR_ty)
  apply (subst IterP_unfold)
  apply (simp_all add:typing defined closure unrest usubst CondR_true AssignR_SemiR_ty)
  apply (subst IterP_unfold)
  apply (simp_all add:typing defined closure unrest usubst CondR_true AssignR_SemiR_ty)
  apply (subst IterP_unfold)
  apply (simp_all add:typing defined closure unrest usubst CondR_false AssignR_SemiR_ty)
done




  apply (subst SubstP_AssignR_simple)
  apply (simp_all add
  apply (subst usubst) back back back
  apply (subgoal_tac "|<0 :: int> < <5>| = (|true| :: (bool, 'a) WF_PEXPRESSION)")
  apply (simp)

  thm AssignR_one_point


  apply (utp_rel_tac)
  apply (simp add: EvalR_AssignR_typed evalp closure typing defined unrest relcomp_unfold)
  apply (simp add: evalr closure typing defined)


lemma "\<lbrakk>SqP (AsP (''x'', NtT) (LiE (NtV 5))) (AsP (''x'', NtT) (LiE (NtV 6)))\<rbrakk>\<^sub>p =
       \<lbrakk>AsP (''x'', NtT) (LiE (NtV 6))\<rbrakk>\<^sub>p"
  apply (auto simp add:evale evalr typing defined unrest relcomp_unfold)
  apply (subst EvalR_AssignR)
  apply (simp_all add:typing defined closure unrest)

end