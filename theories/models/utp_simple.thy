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

theorem SubstP_rel_UNDASHED_ty [evalr] :
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes 
    "TYPEUSOUND('a, 'm)"
    "x \<in> PUNDASHED" 
    "e \<rhd>\<^sub>* x" 
    "DASHED \<sharp> e"
  shows "\<lbrakk>p[e\<down>/\<^sub>px\<down>]\<rbrakk>R = {(b1, b2) | b1 b2. (b1(x :=\<^sub>* \<lbrakk>e\<rbrakk>\<^sub>*b1), b2) \<in> \<lbrakk>p\<rbrakk>R}"
  apply (subst SubstP_rel_UNDASHED)
  apply (simp_all add:evale typing closure defined assms unrest binding_upd_ty_def)
done

theorem AssignR_SemiR_ty:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes 
    "TYPEUSOUND('a, 'm)"
    "x \<in> PUNDASHED" 
    "e \<rhd>\<^sub>* x" 
    "DASHED \<sharp> e"
  shows "`(x := e) ; p` = `p[e/x]`"
  apply (utp_rel_tac)
  apply (simp add: EvalR_AssignR_typed evalp closure typing defined unrest relcomp_unfold assms SubstP_rel_UNDASHED_ty)
  apply (auto simp add: binding_upd_ty_def)
  apply (metis InjU_EvalPE_compat PVAR_VAR_PUNDASHED_UNDASHED WF_REL_BINDING_binding_upd_remove WF_REL_BINDING_member1 assms(2) assms(3))
done

lemma [simp]: "(x::int) < y \<Longrightarrow> `<x> < <y>` = true"
  by (simp add:eval)

lemma [simp]: "\<not> (x::int) < y \<Longrightarrow> `<x> < <y>` = false"
  by (simp add:eval)

lemma [simp]: "|<x :: int> + <y>| = |<x + y>|"
  by (simp add:evalp)

abbreviation 
  "prog1 \<equiv> `while ($nv1 < \<guillemotleft>5\<guillemotright>) do 
              (nv1 := $nv1 + \<guillemotleft>1\<guillemotright>)
            od`"
 
abbreviation "fv \<equiv> MkPlainP ''fact'' False TYPE(int) TYPE('m :: INT_SORT)"
abbreviation "cv \<equiv> MkPlainP ''c'' False TYPE(int) TYPE('m :: INT_SORT)"

type_synonym 'a WF_STATE = "('a WF_PREDICATE * 'a WF_PREDICATE)"

fun StepP :: "'a WF_STATE \<Rightarrow> 'a WF_STATE \<Rightarrow> bool" (infix "~>" 50) where
"(s,P) ~> (t,Q) \<longleftrightarrow> (s\<acute>;P) \<sqsubseteq> (t\<acute>;Q)"

lemma SkipR_step:
  "(s, II; P) ~> (s, P)"
  by simp

lemma SeqR_step:
  "(s,P) ~> (t,P') \<Longrightarrow> (s, P;Q) ~> (t, P';Q)"
  apply (simp)
  apply (simp add:SemiR_assoc)
  apply (rule refine)
  apply (assumption)
  apply (rule order_refl)
done

lemma ChoiceP_step1:
  "(s, P \<sqinter> Q) ~> (s, P)"
  apply (simp)
  apply (metis RefineP_choice1 SemiR_mono_refine order_refl)
done

lemma ChoiceP_step2:
  "(s, P \<sqinter> Q) ~> (s, Q)"
  apply (simp)
  apply (metis RefineP_choice2 SemiR_mono_refine order_refl)
done

lemma UNREST_SemiR_UNDASHED [unrest]:
  "\<lbrakk> vs \<sharp> P; vs \<subseteq> UNDASHED; P \<in> WF_RELATION; Q \<in> WF_RELATION \<rbrakk> \<Longrightarrow> vs \<sharp> (P ; Q)"
  apply (simp add:SemiR_algebraic_rel)
  apply (rule unrest)
  apply (rule unrest)
  apply (rule unrest)
  apply (simp)
  apply (simp add:urename)
  apply (rule unrest)
  apply (simp add:WF_RELATION_def)
  apply (auto simp add:urename)
done

lemma UNREST_SemiR_DASHED [unrest]:
  "\<lbrakk> vs \<sharp> Q; vs \<subseteq> DASHED; P \<in> WF_RELATION; Q \<in> WF_RELATION \<rbrakk> \<Longrightarrow> vs \<sharp> (P ; Q)"
  apply (simp add:SemiR_algebraic_rel)
  apply (rule unrest)
  apply (rule unrest)
  apply (rule unrest)
  apply (simp add:WF_RELATION_def)
  apply (auto simp add:urename)
  apply (rule unrest)
  apply (simp)
  apply (simp add:urename)
done

lemma WF_RELATION_CONDITION_true: 
  assumes "P \<in> WF_RELATION" "(P ; true) = P"
  shows "P \<in> WF_CONDITION"
proof -
  have "D\<^sub>1 \<sharp> (P ; true)"
    by (simp add:unrest closure assms(1))

  thus ?thesis
    by (simp add:WF_CONDITION_def assms)
qed

lemma WF_RELATION_POSTCOND_true: 
  assumes "P \<in> WF_RELATION" "(true ; P) = P"
  shows "P \<in> WF_POSTCOND"
proof -
  have "D\<^sub>0 \<sharp> (true ; P)"
    by (simp add:unrest closure assms(1))

  thus ?thesis
    by (simp add:WF_POSTCOND_def assms)
qed

lemma SemiR_first_POSTCOND [closure]:
  "\<lbrakk> p \<in> WF_POSTCOND; Q \<in> WF_RELATION \<rbrakk> \<Longrightarrow> p ; Q \<in> WF_POSTCOND"
  by (metis (full_types) SemiR_TrueP_postcond SemiR_assoc SemiR_closure WF_POSTCOND_WF_RELATION WF_RELATION_POSTCOND_true)

lemma SemiR_second_CONDITION [closure]:
  "\<lbrakk> P \<in> WF_RELATION; q \<in> WF_CONDITION \<rbrakk> \<Longrightarrow> P ; q \<in> WF_CONDITION"
  by (metis SemiR_TrueP_precond SemiR_assoc SemiR_closure WF_CONDITION_WF_RELATION WF_RELATION_CONDITION_true)

definition uv :: 
  "'a WF_PREDICATE \<Rightarrow> ('a VAR) set" where
"uv p = \<Union> {vs. UNREST vs p}"

lemma UNREST_uv_upper: 
  "xs \<sharp> P \<Longrightarrow> xs \<subseteq> uv P"
  by (auto simp add:uv_def)

lemma UNREST_uv_least:
  "(\<And>xs. xs \<sharp> P \<Longrightarrow> xs \<subseteq> zs) \<Longrightarrow> uv P \<subseteq> zs"
  by (auto simp add:uv_def)

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

lemma "uv P \<sharp> P"
  apply (simp add:uv_def)




lemma 
  assumes 
    "s \<in> WF_POSTCOND"
    "P \<in> WF_RELATION"
    "Q \<in> WF_RELATION"
  shows "`s ; (P \<and> Q)` = `(s ; P) \<and> (s ; Q)`"
  apply (simp add:closure SemiR_algebraic_rel assms urename)
proof -
  have "`s ; (P \<and> Q)` = `true ; (s\<acute> \<and> P \<and> Q)`"
    by (metis AndP_rel_closure SemiR_AndP_left_postcond TrueP_rel_closure assms(1) assms(2) assms(3) utp_pred_simps(6))

  have "... = `true ; ((s\<acute> \<and> P) \<and> (s\<acute> \<and> Q))`"
    by (smt AndP_comm AndP_idem AndP_assoc)

  using assms
  

  apply (frule_tac SemiR_TrueP_postcond)
  apply (utp_xrel_auto_tac)
  apply (utp_rel_auto_tac)

lemma CondR_true_step:
  "[s\<acute>;b] \<Longrightarrow> (s, P \<lhd> b \<rhd> Q) ~> (s, P)"
  apply (simp add:CondR_def SemiR_OrP_distl)
  apply (utp_rel_auto_tac)
  apply (rule refine)

  by (simp)

lemma CondR_false_step:
  "[\<not>(s\<acute>;b)] \<Longrightarrow> (s, P \<lhd> b \<rhd> Q) ~> (s, Q)"
  by (simp)


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