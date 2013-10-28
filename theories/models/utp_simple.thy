theory utp_simple
imports utp_base Derive
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

fun sem_svar :: "svar \<Rightarrow> SimpV VAR" where
"sem_svar (n,t) = MkPlain n (embTYPE t) False"

fun sem_SimpE :: "SimpE \<Rightarrow> SimpV WF_EXPRESSION" where
"sem_SimpE (LiE v) = LitE v" |
"sem_SimpE (PlE x y) = Op2E (liftNNF (op +)) (sem_SimpE x) (sem_SimpE y)" |
"sem_SimpE (MlE x y) = Op2E (liftNNF (op *)) (sem_SimpE x) (sem_SimpE y)" |
"sem_SimpE (LqE x y) = Op2E (liftNBF (op \<le>)) (sem_SimpE x) (sem_SimpE y)" |
"sem_SimpE (VrE v) = VarE (sem_svar v)"

fun sem_SimpP :: "SimpP \<Rightarrow> SimpV WF_PREDICATE" where
"sem_SimpP SkP = II" |
"sem_SimpP (SqP P Q) = (sem_SimpP P) ; (sem_SimpP Q)" |
"sem_SimpP (AsP x e) = (sem_svar x) :=\<^sub>R (sem_SimpE e)" |
"sem_SimpP (WhP e P) = IterP (ExprP (sem_SimpE e)) (sem_SimpP P)"

end