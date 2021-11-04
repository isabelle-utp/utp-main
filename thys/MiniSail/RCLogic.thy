(*<*)
theory RCLogic
  imports Wellformed
begin
  (*>*)

hide_const Syntax.dom

chapter \<open>Refinement Constraint Logic\<close>

text \<open> Semantics for the logic we use in the refinement constraints. It is a multi-sorted, quantifier free
logic with polymorphic datatypes and linear arithmetic. We could have modelled by using one of the 
encodings to FOL however we wanted to explore using a more direct model. \<close>

section \<open>Evaluation and Satisfiability\<close>

subsection \<open>Valuation\<close>

text \<open> Refinement constraint logic values. SUt is a value for the uninterpreted 
       sort that corresponds to basic type variables. For now we only need one of these universes.
       We wrap an smt\_val inside it during a process we call 'boxing' 
       which is introduced in the RCLogicL theory \<close>
nominal_datatype rcl_val = SBitvec "bit list" | SNum int | SBool bool | SPair rcl_val rcl_val | 
  SCons tyid string rcl_val | SConsp tyid string b rcl_val |
  SUnit | SUt rcl_val 

text \<open> RCL sorts. Represent our domains. The universe is the union of all of the these.
        S\_Ut is the single uninterpreted sort. These map almost directly to basic type 
        but we have them to distinguish syntax (basic types) and semantics (RCL sorts) \<close>
nominal_datatype rcl_sort = S_bool | S_int | S_unit | S_pair rcl_sort rcl_sort | S_id tyid | S_app tyid rcl_sort | S_bitvec | S_ut 

type_synonym valuation = "(x,rcl_val) map"

type_synonym type_valuation = "(bv,rcl_sort) map"

text \<open>Well-sortedness for RCL values\<close>
inductive wfRCV:: "\<Theta> \<Rightarrow> rcl_val \<Rightarrow> b \<Rightarrow> bool" ( " _  \<turnstile> _ : _" [50,50] 50) where
  wfRCV_BBitvecI:  "P \<turnstile> (SBitvec bv)  : B_bitvec"
| wfRCV_BIntI:  "P \<turnstile> (SNum n)  : B_int"
| wfRCV_BBoolI: "P \<turnstile> (SBool b) : B_bool"
| wfRCV_BPairI: "\<lbrakk> P \<turnstile> s1 : b1 ; P \<turnstile> s2 : b2 \<rbrakk> \<Longrightarrow> P \<turnstile> (SPair s1 s2) : (B_pair b1 b2)"
| wfRCV_BConsI: "\<lbrakk>  AF_typedef s dclist \<in> set \<Theta>;
      (dc, \<lbrace> x : b  | c \<rbrace>) \<in> set dclist ;
     \<Theta> \<turnstile> s1 : b \<rbrakk> \<Longrightarrow> \<Theta> \<turnstile>(SCons s dc s1) : (B_id s)"
| wfRCV_BConsPI:"\<lbrakk> AF_typedef_poly s bv dclist \<in> set \<Theta>;
      (dc, \<lbrace> x : b  | c \<rbrace>) \<in> set dclist ;
       atom bv \<sharp> (\<Theta>, SConsp s dc b' s1, B_app s b');
     \<Theta> \<turnstile> s1 : b[bv::=b']\<^sub>b\<^sub>b \<rbrakk> \<Longrightarrow> \<Theta> \<turnstile>(SConsp s dc b' s1) : (B_app s b')"
| wfRCV_BUnitI: "P \<turnstile> SUnit : B_unit"
| wfRCV_BVarI: "P \<turnstile> (SUt n) : (B_var bv)"
equivariance wfRCV
nominal_inductive wfRCV 
  avoids wfRCV_BConsPI: bv
proof(goal_cases)
  case (1 s bv dclist \<Theta> dc x b c b' s1)
  then show ?case using fresh_star_def by auto
next
  case (2 s bv dclist \<Theta> dc x b c s1 b')
  then show ?case by auto
qed

inductive_cases wfRCV_elims :
  "wfRCV P s  B_bitvec"
  "wfRCV P s (B_pair b1 b2)"
  "wfRCV P s (B_int)"
  "wfRCV P s (B_bool)"
  "wfRCV P s (B_id ss)"
  "wfRCV P s (B_var bv)"
  "wfRCV P s (B_unit)"
  "wfRCV P s (B_app tyid b)"
  "wfRCV P (SBitvec bv) b"
  "wfRCV P (SNum n)  b"
  "wfRCV P (SBool n)  b"
  "wfRCV P (SPair s1 s2) b"
  "wfRCV P (SCons s dc s1) b"
  "wfRCV P (SConsp s dc b' s1) b"
  "wfRCV P SUnit b"
  "wfRCV P (SUt s1) b"

text \<open> Sometimes we want to assert @{text "P \<turnstile> s ~ b[bv=b']"} and we want to know what b is 
however substitution is not injective so we can't write this in terms of @{text "wfRCV"}. 
So we define a relation that makes the components of the substitution explicit. \<close>

inductive wfRCV_subst:: "\<Theta> \<Rightarrow> rcl_val \<Rightarrow> b \<Rightarrow> (bv*b) option \<Rightarrow> bool" where
  wfRCV_subst_BBitvecI:  "wfRCV_subst P (SBitvec bv) B_bitvec  sub "
| wfRCV_subst_BIntI:  "wfRCV_subst P (SNum n)  B_int sub "
| wfRCV_subst_BBoolI: "wfRCV_subst P (SBool b)  B_bool sub  "
| wfRCV_subst_BPairI: "\<lbrakk> wfRCV_subst P s1 b1 sub ; wfRCV_subst P s2 b2 sub \<rbrakk> \<Longrightarrow> wfRCV_subst P (SPair s1 s2) (B_pair b1 b2) sub"
| wfRCV_subst_BConsI: "\<lbrakk>  AF_typedef s dclist \<in> set \<Theta>;
      (dc, \<lbrace> x : b  | c \<rbrace>) \<in> set dclist ;
     wfRCV_subst \<Theta> s1 b None \<rbrakk> \<Longrightarrow> wfRCV_subst \<Theta> (SCons s dc s1) (B_id s) sub"
| wfRCV_subst_BConspI: "\<lbrakk>  AF_typedef_poly s bv dclist \<in> set \<Theta>;
      (dc, \<lbrace> x : b  | c \<rbrace>) \<in> set dclist ;
     wfRCV_subst \<Theta> s1 (b[bv::=b']\<^sub>b\<^sub>b) sub  \<rbrakk> \<Longrightarrow> wfRCV_subst \<Theta> (SConsp s dc b' s1) (B_app s b') sub"
| wfRCV_subst_BUnitI: "wfRCV_subst P SUnit B_unit sub "
| wfRCV_subst_BVar1I: "bvar \<noteq> bv \<Longrightarrow> wfRCV_subst P (SUt n) (B_var bv)  (Some (bvar,bin))"
| wfRCV_subst_BVar2I: "\<lbrakk> bvar = bv; wfRCV_subst P s bin None \<rbrakk> \<Longrightarrow> wfRCV_subst P s (B_var bv)  (Some (bvar,bin))"
| wfRCV_subst_BVar3I: "wfRCV_subst P (SUt n) (B_var bv)  None"
equivariance wfRCV_subst
nominal_inductive wfRCV_subst .

subsection \<open>Evaluation base-types\<close>

inductive eval_b :: "type_valuation \<Rightarrow> b \<Rightarrow> rcl_sort \<Rightarrow> bool"  ( "_ \<lbrakk> _ \<rbrakk> ~ _ " ) where
  "v \<lbrakk> B_bool \<rbrakk> ~ S_bool"
| "v \<lbrakk> B_int \<rbrakk> ~ S_int"
| "Some s = v bv \<Longrightarrow> v \<lbrakk> B_var bv \<rbrakk> ~ s"
equivariance eval_b
nominal_inductive eval_b .

subsection \<open>Wellformed vvaluations\<close>

definition wfI ::  "\<Theta> \<Rightarrow> \<Gamma> \<Rightarrow> valuation \<Rightarrow> bool" ( " _ ; _ \<turnstile> _" )  where
  "\<Theta> ; \<Gamma> \<turnstile> i = (\<forall> (x,b,c) \<in> toSet \<Gamma>. \<exists>s. Some s = i x \<and> \<Theta> \<turnstile> s : b)"

subsection \<open>Evaluating Terms\<close>

nominal_function eval_l :: "l \<Rightarrow> rcl_val" ( "\<lbrakk> _ \<rbrakk> " ) where
  "\<lbrakk> L_true \<rbrakk> = SBool True"
|  "\<lbrakk> L_false \<rbrakk> = SBool False"
|  "\<lbrakk> L_num n \<rbrakk> = SNum n"
|  "\<lbrakk> L_unit \<rbrakk> = SUnit"
|  "\<lbrakk> L_bitvec n \<rbrakk> = SBitvec n"
                   apply(auto simp: eqvt_def eval_l_graph_aux_def)
  by (metis l.exhaust)
nominal_termination (eqvt) by lexicographic_order

inductive eval_v :: "valuation \<Rightarrow> v \<Rightarrow> rcl_val \<Rightarrow> bool"  ( "_ \<lbrakk> _ \<rbrakk> ~ _ " ) where
  eval_v_litI:   "i \<lbrakk> V_lit l \<rbrakk> ~ \<lbrakk> l \<rbrakk> "
| eval_v_varI: "Some sv = i x  \<Longrightarrow> i \<lbrakk> V_var x \<rbrakk> ~ sv"
| eval_v_pairI: "\<lbrakk> i \<lbrakk> v1 \<rbrakk> ~ s1 ; i \<lbrakk> v2 \<rbrakk> ~ s2 \<rbrakk> \<Longrightarrow> i \<lbrakk> V_pair v1 v2 \<rbrakk> ~ SPair s1 s2"
| eval_v_consI: "i \<lbrakk> v \<rbrakk> ~ s \<Longrightarrow> i \<lbrakk> V_cons tyid dc v \<rbrakk> ~ SCons tyid dc s"
| eval_v_conspI: "i \<lbrakk> v \<rbrakk> ~ s \<Longrightarrow> i \<lbrakk> V_consp tyid dc b v \<rbrakk> ~ SConsp tyid dc b s"
equivariance eval_v
nominal_inductive eval_v .

inductive_cases eval_v_elims:
  "i \<lbrakk> V_lit l \<rbrakk> ~  s"
  "i \<lbrakk> V_var x \<rbrakk> ~  s"
  "i \<lbrakk> V_pair v1 v2 \<rbrakk> ~ s"
  "i \<lbrakk> V_cons tyid dc v \<rbrakk> ~ s"
  "i \<lbrakk> V_consp tyid dc b v \<rbrakk> ~ s"

inductive eval_e :: "valuation \<Rightarrow> ce \<Rightarrow> rcl_val \<Rightarrow> bool" ( "_ \<lbrakk> _ \<rbrakk> ~ _ " )  where
  eval_e_valI: "i \<lbrakk> v \<rbrakk> ~  sv \<Longrightarrow> i \<lbrakk> CE_val v \<rbrakk> ~ sv"
| eval_e_plusI: "\<lbrakk> i \<lbrakk> v1 \<rbrakk> ~ SNum n1; i \<lbrakk> v2 \<rbrakk> ~ SNum n2  \<rbrakk>  \<Longrightarrow> i \<lbrakk> (CE_op Plus v1 v2) \<rbrakk> ~ (SNum (n1+n2))"
| eval_e_leqI: "\<lbrakk> i \<lbrakk> v1 \<rbrakk> ~ (SNum n1); i \<lbrakk> v2 \<rbrakk> ~ (SNum n2) \<rbrakk>  \<Longrightarrow> i \<lbrakk> (CE_op LEq v1 v2) \<rbrakk> ~ (SBool (n1 \<le> n2))"
| eval_e_eqI: "\<lbrakk> i \<lbrakk> v1 \<rbrakk> ~ s1; i \<lbrakk> v2 \<rbrakk> ~ s2 \<rbrakk>  \<Longrightarrow> i \<lbrakk> (CE_op Eq v1 v2) \<rbrakk> ~ (SBool (s1 = s2))"
| eval_e_fstI: "\<lbrakk> i \<lbrakk> v \<rbrakk> ~ SPair v1 v2  \<rbrakk> \<Longrightarrow> i \<lbrakk> (CE_fst v) \<rbrakk> ~ v1"
| eval_e_sndI: "\<lbrakk> i \<lbrakk> v \<rbrakk> ~ SPair v1 v2  \<rbrakk> \<Longrightarrow> i \<lbrakk> (CE_snd v) \<rbrakk> ~ v2"
| eval_e_concatI:"\<lbrakk> i \<lbrakk> v1 \<rbrakk> ~ (SBitvec bv1); i \<lbrakk> v2 \<rbrakk> ~ (SBitvec bv2) \<rbrakk> \<Longrightarrow> i \<lbrakk> (CE_concat v1 v2) \<rbrakk> ~ (SBitvec (bv1@bv2))"
| eval_e_lenI:"\<lbrakk> i \<lbrakk> v \<rbrakk>  ~ (SBitvec bv) \<rbrakk> \<Longrightarrow> i \<lbrakk> (CE_len v) \<rbrakk> ~ (SNum (int (List.length bv)))"
equivariance eval_e
nominal_inductive eval_e .

inductive_cases eval_e_elims:
  "i \<lbrakk> (CE_val v) \<rbrakk> ~ s"
  "i \<lbrakk> (CE_op Plus v1 v2) \<rbrakk> ~ s"
  "i \<lbrakk> (CE_op LEq v1 v2) \<rbrakk> ~ s"
  "i \<lbrakk> (CE_op Eq v1 v2) \<rbrakk> ~ s"
  "i \<lbrakk> (CE_fst v) \<rbrakk> ~ s"
  "i \<lbrakk> (CE_snd v) \<rbrakk> ~ s"
  "i \<lbrakk> (CE_concat v1 v2) \<rbrakk> ~ s"
  "i \<lbrakk> (CE_len v) \<rbrakk> ~ s"

inductive eval_c :: "valuation \<Rightarrow> c \<Rightarrow> bool \<Rightarrow> bool" ( " _ \<lbrakk> _ \<rbrakk> ~ _ ")  where
  eval_c_trueI:  "i \<lbrakk> C_true \<rbrakk> ~ True"
| eval_c_falseI:"i \<lbrakk> C_false \<rbrakk> ~ False"
| eval_c_conjI: "\<lbrakk> i \<lbrakk> c1 \<rbrakk> ~ b1 ; i \<lbrakk> c2 \<rbrakk> ~ b2 \<rbrakk> \<Longrightarrow>  i \<lbrakk> (C_conj c1 c2) \<rbrakk> ~  (b1 \<and> b2)"
| eval_c_disjI: "\<lbrakk> i \<lbrakk> c1 \<rbrakk> ~ b1 ; i \<lbrakk> c2 \<rbrakk> ~ b2 \<rbrakk> \<Longrightarrow>  i \<lbrakk> (C_disj c1 c2) \<rbrakk> ~ (b1 \<or> b2)"
| eval_c_impI:"\<lbrakk> i \<lbrakk> c1 \<rbrakk> ~ b1 ; i \<lbrakk> c2 \<rbrakk> ~ b2 \<rbrakk> \<Longrightarrow>  i \<lbrakk> (C_imp c1 c2) \<rbrakk> ~ (b1 \<longrightarrow> b2)"
| eval_c_notI:"\<lbrakk> i \<lbrakk> c \<rbrakk> ~ b \<rbrakk> \<Longrightarrow> i \<lbrakk> (C_not c) \<rbrakk> ~ (\<not> b)"
| eval_c_eqI:"\<lbrakk> i \<lbrakk> e1 \<rbrakk> ~ sv1; i \<lbrakk> e2 \<rbrakk> ~ sv2 \<rbrakk> \<Longrightarrow> i \<lbrakk> (C_eq e1 e2) \<rbrakk> ~ (sv1=sv2)"
equivariance eval_c
nominal_inductive eval_c .

inductive_cases eval_c_elims:
  "i \<lbrakk> C_true \<rbrakk> ~  True"
  "i \<lbrakk> C_false \<rbrakk> ~ False"
  "i \<lbrakk> (C_conj c1 c2)\<rbrakk> ~ s"
  "i \<lbrakk> (C_disj c1 c2)\<rbrakk> ~ s"
  "i \<lbrakk> (C_imp c1 c2)\<rbrakk> ~ s"
  "i \<lbrakk> (C_not c) \<rbrakk> ~ s"
  "i \<lbrakk> (C_eq e1 e2)\<rbrakk> ~ s"
  "i \<lbrakk> C_true \<rbrakk> ~ s"
  "i \<lbrakk> C_false \<rbrakk> ~ s"

subsection \<open>Satisfiability\<close>

inductive  is_satis :: "valuation \<Rightarrow> c \<Rightarrow> bool" ( " _ \<Turnstile> _ " ) where
  "i \<lbrakk> c \<rbrakk> ~ True \<Longrightarrow> i \<Turnstile> c"
equivariance is_satis
nominal_inductive is_satis .

nominal_function is_satis_g :: "valuation \<Rightarrow> \<Gamma> \<Rightarrow> bool" ( " _ \<Turnstile> _ " ) where
  "i \<Turnstile> GNil = True"
| "i \<Turnstile> ((x,b,c) #\<^sub>\<Gamma> G) = ( i \<Turnstile> c \<and>  i \<Turnstile> G)"
       apply(auto simp: eqvt_def is_satis_g_graph_aux_def)
  by (metis \<Gamma>.exhaust old.prod.exhaust)
nominal_termination (eqvt) by lexicographic_order

section \<open>Validity\<close>

nominal_function  valid :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> c \<Rightarrow> bool"  ("_ ; _ ; _  \<Turnstile> _ " [50, 50] 50)  where
  "P ; B ; G \<Turnstile> c = ( (P ; B ; G \<turnstile>\<^sub>w\<^sub>f c) \<and> (\<forall>i. (P ; G \<turnstile> i) \<and>  i \<Turnstile> G \<longrightarrow> i \<Turnstile> c))"
  by (auto simp: eqvt_def wfI_def valid_graph_aux_def)
nominal_termination (eqvt) by lexicographic_order

section \<open>Lemmas\<close>
text \<open>Lemmas needed for Examples\<close>

lemma valid_trueI [intro]:
  fixes G::\<Gamma>
  assumes "P ; B \<turnstile>\<^sub>w\<^sub>f G"
  shows "P ; B ; G \<Turnstile> C_true"
proof -
  have "\<forall>i. i \<Turnstile> C_true" using is_satis.simps eval_c_trueI by simp
  moreover have "P ; B ; G \<turnstile>\<^sub>w\<^sub>f C_true" using wfC_trueI assms by simp
  ultimately show ?thesis using valid.simps by simp
qed

end