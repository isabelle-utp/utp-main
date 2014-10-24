(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/theories/utp_theory.thy                                          *)
(* Author: Simon Foster and Frank Zeyda, University of York                   *)
(******************************************************************************)

header {* UTP Theories *}

theory utp_theory
imports 
  "../core/utp_pred"
  "../core/utp_unrest"
  "../tactics/utp_pred_tac"
  "../tactics/utp_rel_tac"
  "../tactics/utp_xrel_tac"
  "../poly/utp_poly_tac"
  "../alpha/utp_alpha_rel"
  "../alpha/utp_alpha_lattice"
  "../parser/utp_alpha_pred_parser"
begin

subsection {* UTP theories definitions *}

definition is_healthy :: 
  "'a::type \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" (infix "is" 50) where
"is_healthy p H \<equiv> H p = p"

definition IDEMPOTENT_OVER ::
  "'a alpha set \<Rightarrow> 'a ALPHA_FUNCTION set" where
"IDEMPOTENT_OVER vs = {f . \<forall> p. \<alpha> p \<in> vs \<longrightarrow> f (f p) = f p}"

declare is_healthy_def [eval,evalr,evalrx,evalp,evala]

lemma Healthy_intro [intro]:
  "H(P) = P \<Longrightarrow> P is H"
  by (simp add: is_healthy_def)

lemma Healthy_elim [elim]:
  "\<lbrakk> Q is H; \<lbrakk> H(Q) = Q \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add: is_healthy_def)

lemma Healthy_comp [closure]:
  "\<lbrakk> H2(P) is H1; P is H2 \<rbrakk> \<Longrightarrow> P is (H1 \<circ> H2)"
  by (simp add:is_healthy_def)

lemma Healthy_simp:
  "P is H \<Longrightarrow> H(P) = P"
  by (simp add:is_healthy_def)

lemma Healthy_apply [closure]:
  "\<lbrakk> H \<in> IDEMPOTENT_OVER vs; \<alpha> P \<in> vs \<rbrakk> \<Longrightarrow> H(P) is H"
  by (simp add:is_healthy_def IDEMPOTENT_OVER_def)

lemma Healthy_id [closure]:
  "p is id"
  by (simp add:is_healthy_def)

record 'a THEORY =
  alphas :: "'a alpha set" ("\<A>\<index>")
  health :: "'a ALPHA_FUNCTION " ("\<H>\<index>")

locale UTP_THEORY =
  fixes T (structure)
  assumes alpha_lattice: "a \<in> \<A> \<Longrightarrow> complete_lattice (fset_order \<langle>a\<rangle>\<^sub>f)"
  and     health_idem: "\<H> \<in> IDEMPOTENT_OVER \<A>"

definition THEORY_PRED :: "('a, 'b :: type) THEORY_scheme \<Rightarrow> 'a uapred set" ("\<lbrakk>_\<rbrakk>\<T>") where
"THEORY_PRED T = {p. \<alpha> p \<in> \<A>\<^bsub>T\<^esub> \<and> p is \<H>\<^bsub>T\<^esub>}"

definition THEORY_PRED_OVER :: 
  "('a, 'b :: type) THEORY_scheme \<Rightarrow> 'a alpha \<Rightarrow> 'a uapred set" ("\<lbrakk>_\<rbrakk>[_]\<T>") where
"THEORY_PRED_OVER T a \<equiv> {p \<in> \<lbrakk>T\<rbrakk>\<T>. \<alpha> p = a}"

lemma THEORY_PRED_OVER_closure [closure]:
  "\<lbrakk> p \<in> \<lbrakk>T\<rbrakk>\<T>; \<alpha> p = a \<rbrakk> \<Longrightarrow> p \<in> \<lbrakk>T\<rbrakk>[a]\<T>"
  by (simp add:THEORY_PRED_OVER_def)

definition THEORY_CLOSED_OP :: 
  "('a uapred \<Rightarrow> 'a uapred \<Rightarrow> 'a uapred) \<Rightarrow>
   ('a, 'b :: type) THEORY_scheme \<Rightarrow> bool" (infix "closed-under" 50) where
"THEORY_CLOSED_OP f T = (\<forall> p \<in> \<lbrakk>T\<rbrakk>\<T>. \<forall> q \<in> \<lbrakk>T\<rbrakk>\<T>. f p q \<in> \<lbrakk>T\<rbrakk>\<T>)"

lemma THEORY_PRED_intro [intro]:
  "\<lbrakk> \<alpha> p \<in> \<A>\<^bsub>T\<^esub>; p is \<H>\<^bsub>T\<^esub> \<rbrakk> \<Longrightarrow> p \<in> \<lbrakk>T\<rbrakk>\<T>"
  by (simp add:THEORY_PRED_def)

lemma THEORY_PRED_elim [elim]:
  "\<lbrakk> p \<in> \<lbrakk>T\<rbrakk>\<T>; \<lbrakk> \<alpha> p \<in> \<A>\<^bsub>T\<^esub>; p is \<H>\<^bsub>T\<^esub> \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add:THEORY_PRED_def)

lemma THEORY_PRED_OVER_alphabet :
  "p \<in> \<lbrakk>T\<rbrakk>[a]\<T> \<Longrightarrow> \<alpha> p = a"
  by (metis (lifting, full_types) THEORY_PRED_OVER_def mem_Collect_eq)

lemma THEORY_PRED_OVER_intro [intro]:
  "\<lbrakk> p \<in> \<lbrakk>T\<rbrakk>\<T>; \<alpha> p = a \<rbrakk> \<Longrightarrow> p \<in> \<lbrakk>T\<rbrakk>[a]\<T>"
  by (simp add:THEORY_PRED_OVER_def)

lemma THEORY_PRED_OVER_elim [elim]:
  "\<lbrakk> p \<in> \<lbrakk>T\<rbrakk>[a]\<T>; \<lbrakk> p \<in> \<lbrakk>T\<rbrakk>\<T>; \<alpha> p = a \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add:THEORY_PRED_OVER_def)

abbreviation "OrderTA T \<equiv> \<lparr> partial_object.carrier = \<lbrakk>T\<rbrakk>\<T>, eq = op =, le = op \<sqsubseteq> \<rparr>"

theorem THEORYA_partial_order: "partial_order (OrderTA T)"
  by (unfold_locales, simp_all)

(*
interpretation THEORYA_partial_orderder: partial_order "(OrderTA T)"
  where "partial_object.carrier (OrderTA T) = \<lbrakk>T\<rbrakk>\<T>"
(*    and "eq (OrderTA T) = op =" *)
    and "le (OrderTA T) = op \<sqsubseteq>"
  by (unfold_locales, simp_all)
*)

abbreviation "OrderT T a \<equiv> \<lparr> partial_object.carrier = \<lbrakk>T\<rbrakk>[a]\<T>, eq = op =, le = op \<sqsubseteq> \<rparr>"

theorem THEORY_partial_order: "partial_order (OrderT T a)"
  by (unfold_locales, simp_all)

(*
interpretation THEORY_partial_order: partial_order "(OrderT T a)"
  where "partial_object.carrier (OrderT T a) = \<lbrakk>T\<rbrakk>[a]\<T>"
(*    and "eq (OrderT T a) = op =" *)
    and "le (OrderT T a) = op \<sqsubseteq>"
  by (unfold_locales, simp_all)
*)

subsection {* UTP theory lattice operators *}

abbreviation JoinT :: 
  "'a uapred \<Rightarrow> 
   ('a, 'b :: type) THEORY_scheme \<Rightarrow> 
   'a alpha \<Rightarrow> 
   'a uapred \<Rightarrow> 
   'a uapred"  (infixl "\<squnion>\<^bsub>_[_]\<^esub>" 65) where
"P \<squnion>\<^bsub>T[a]\<^esub> Q \<equiv> join (OrderT T a) P Q"

abbreviation MeetT :: 
  "'a uapred \<Rightarrow> 
   ('a, 'b :: type) THEORY_scheme \<Rightarrow> 
   'a alpha \<Rightarrow> 
   'a uapred \<Rightarrow> 
   'a uapred"  (infixl "\<sqinter>\<^bsub>_[_]\<^esub>" 70) where
"P \<sqinter>\<^bsub>T[a]\<^esub> Q \<equiv> meet (OrderT T a) P Q"

abbreviation SupT ::
  "('a, 'b :: type) THEORY_scheme \<Rightarrow> 'a alpha \<Rightarrow> 
   'a uapred set \<Rightarrow> 
   'a uapred" ("\<Squnion>\<^bsub>_[_]\<^esub>_" [90] 90) where
"\<Squnion>\<^bsub>T[a]\<^esub> A \<equiv> sup (OrderT T a) A"

abbreviation InfT ::
  "('a, 'b :: type) THEORY_scheme \<Rightarrow> 'a alpha \<Rightarrow> 
   'a uapred set \<Rightarrow> 
   'a uapred" ("\<Sqinter>\<^bsub>_[_]\<^esub>_" [90] 90) where
"\<Sqinter>\<^bsub>T[a]\<^esub> A \<equiv> inf (OrderT T a) A"

abbreviation TopT :: "('a, 'b :: type) THEORY_scheme \<Rightarrow> 'a alpha \<Rightarrow> 'a uapred" ("\<top>\<^bsub>_[_]\<^esub>") where
"\<top>\<^bsub>T[a]\<^esub> \<equiv> top (OrderT T a)"

abbreviation BotT :: "('a, 'b :: type) THEORY_scheme \<Rightarrow> 'a alpha \<Rightarrow> 'a uapred" ("\<bottom>\<^bsub>_[_]\<^esub>") where
"\<bottom>\<^bsub>T[a]\<^esub> \<equiv> bottom (OrderT T a)"

abbreviation LfpT :: 
  "('a, 'b :: type) THEORY_scheme \<Rightarrow> 'a alpha \<Rightarrow> 
   'a ALPHA_FUNCTION \<Rightarrow> 'a uapred" ("\<mu>\<^bsub>_[_]\<^esub>") where
"\<mu>\<^bsub>T[a]\<^esub> f \<equiv> LFP (OrderT T a) f"

abbreviation GfpT :: 
  "('a, 'b :: type) THEORY_scheme \<Rightarrow> 'a alpha \<Rightarrow> 
   'a ALPHA_FUNCTION \<Rightarrow> 'a uapred" ("\<nu>\<^bsub>_[_]\<^esub>") where
"\<nu>\<^bsub>T[a]\<^esub> f \<equiv> GFP (OrderT T a) f"

syntax
  "_uapred_top"      :: "'a THEORY \<Rightarrow> 'a alpha \<Rightarrow> n_uapred" ("\<top>\<^bsub>_[_]\<^esub>")
  "_uapred_bot"      :: "'a THEORY \<Rightarrow> 'a alpha \<Rightarrow> n_uapred" ("\<bottom>\<^bsub>_[_]\<^esub>")
  "_uapred_joint"    :: "n_uapred \<Rightarrow> 'a THEORY \<Rightarrow> 'a alpha \<Rightarrow> n_uapred \<Rightarrow> n_uapred" (infixl "\<squnion>\<^bsub>_[_]\<^esub>" 65)
  "_uapred_meett"    :: "n_uapred \<Rightarrow> 'a THEORY \<Rightarrow> 'a alpha \<Rightarrow> n_uapred \<Rightarrow> n_uapred" (infixl "\<sqinter>\<^bsub>_[_]\<^esub>" 70)

translations
  "_uapred_top T a"     == "CONST TopT T a"
  "_uapred_bot T a"     == "CONST BotT T a"
  "_uapred_joint T a"   == "CONST JoinT T a"
  "_uapred_meett T a"   == "CONST MeetT T a"

abbreviation 
  "GaloisT T1 T2 f g \<equiv> (\<forall> a \<in> \<A>\<^bsub>T1\<^esub>. \<forall> b \<in> \<A>\<^bsub>T2\<^esub>. 
                         galois_connection \<lparr> orderA = (OrderT T1 a)
                                           , orderB = (OrderT T2 b)
                                           , lower = f, upper = g \<rparr>)"

lemma AndA_RefineA_below:
  "\<lbrakk> P \<sqsubseteq> R; Q \<sqsubseteq> R \<rbrakk> \<Longrightarrow> P \<and>\<^sub>\<alpha> Q \<sqsubseteq> R"
  by (utp_alpha_tac, utp_pred_tac)

lemma OrA_RefineA_above:
  "\<lbrakk> R \<sqsubseteq> P; R \<sqsubseteq> Q \<rbrakk> \<Longrightarrow> R \<sqsubseteq> P \<or>\<^sub>\<alpha> Q"
  by (utp_alpha_tac, utp_pred_tac)

context UTP_THEORY
begin

theorem THEORY_AndA_lub:
  assumes 
    "P \<in> \<lbrakk>T\<rbrakk>[a]\<T>" "Q \<in> \<lbrakk>T\<rbrakk>[a]\<T>" 
    "(op \<and>\<^sub>\<alpha>) closed-under T"
  shows "least (OrderT T a) (P \<and>\<^sub>\<alpha> Q) (Upper (OrderT T a) {P, Q})"
  using assms
  apply (rule_tac least_UpperI)
  apply (simp_all)
  apply (safe)[1]
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (simp add:Upper_def, clarify)
  apply (metis AndA_RefineA_below)
  apply (metis (erased, hide_lams) AndA_alphabet THEORY_CLOSED_OP_def THEORY_PRED_OVER_closure THEORY_PRED_OVER_elim fsubset_funion_eq order_refl)
done

theorem THEORY_join_AndA:
  assumes 
    "P \<in> \<lbrakk>T\<rbrakk>[a]\<T>" "Q \<in> \<lbrakk>T\<rbrakk>[a]\<T>" 
    "(op \<and>\<^sub>\<alpha>) closed-under T"
  shows "P \<squnion>\<^bsub>T[a]\<^esub> Q = P \<and>\<^sub>\<alpha> Q"
  using assms
  apply (auto simp add:join_def sup_def)
  apply (rule some_equality)
  apply (metis THEORY_AndA_lub)
  apply (simp add:Upper_def least_def, safe)
  apply (rule antisym)
  apply (metis AndA_RefineA_below)
  apply (drule_tac x="P \<and>\<^sub>\<alpha> Q" in bspec)
  apply (safe)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (metis sup.idem)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (metis sup.idem)
  apply (rule THEORY_PRED_OVER_intro)
  apply (erule THEORY_PRED_OVER_elim)
  apply (erule THEORY_PRED_OVER_elim)
  apply (metis THEORY_CLOSED_OP_def)
  apply (simp add:alphabet)
  apply (metis THEORY_PRED_OVER_alphabet sup.idem)
done

lemma THEORY_OrA_glb:
  assumes 
    "P \<in> \<lbrakk>T\<rbrakk>[a]\<T>" "Q \<in> \<lbrakk>T\<rbrakk>[a]\<T>" 
    "(op \<or>\<^sub>\<alpha>) closed-under T"
  shows "greatest (OrderT T a) (P \<or>\<^sub>\<alpha> Q) (Lower (OrderT T a) {P, Q})"
  using assms
  apply (rule_tac greatest_LowerI)
  apply (simp_all)
  apply (safe)[1]
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (simp add:Lower_def, clarify)
  apply (metis OrA_RefineA_above)
  apply (metis OrA_alphabet THEORY_CLOSED_OP_def THEORY_PRED_OVER_elim THEORY_PRED_OVER_intro sup.idem)
done

theorem OrderT_lattice:
  assumes "(op \<or>\<^sub>\<alpha>) closed-under T" "(op \<and>\<^sub>\<alpha>) closed-under T"
  shows "lattice (OrderT T a)"
  using assms
  by (unfold_locales, auto intro: THEORY_AndA_lub THEORY_OrA_glb)

theorem MeetT_OrA:
  assumes 
    "P \<in> \<lbrakk>T\<rbrakk>[a]\<T>" "Q \<in> \<lbrakk>T\<rbrakk>[a]\<T>" 
    "(op \<or>\<^sub>\<alpha>) closed-under T"
  shows "P \<sqinter>\<^bsub>T[a]\<^esub> Q = P \<or>\<^sub>\<alpha> Q"
  using assms
  apply (auto simp add:meet_def inf_def)
  apply (rule some_equality)
  apply (metis THEORY_OrA_glb)
  apply (simp add:Lower_def greatest_def, safe)
  apply (rule antisym)
  apply (drule_tac x="P \<or>\<^sub>\<alpha> Q" in bspec)
  apply (safe)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (metis sup.idem)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (metis sup.idem)
  apply (rule THEORY_PRED_OVER_intro)
  apply (erule THEORY_PRED_OVER_elim)
  apply (erule THEORY_PRED_OVER_elim)
  apply (metis THEORY_CLOSED_OP_def)
  apply (simp add:alphabet)
  apply (metis THEORY_PRED_OVER_alphabet sup.idem)
  apply (metis OrA_RefineA_above)
done

(*

instantiation WF_THEORY :: (VALUE) join_semilattice_zero
begin

lift_definition zero_WF_THEORY :: "'a WF_THEORY" is "(UNIV, {}) :: 'a THEORY"
  by (simp add:WF_THEORY_def)

lift_definition plus_WF_THEORY :: "'a::VALUE WF_THEORY \<Rightarrow> 'a WF_THEORY \<Rightarrow> 'a WF_THEORY" 
is "(\<lambda> (A1,HC1) (A2,HC2). (A1\<inter>A2,HC1\<union>HC2)) :: 'a THEORY \<Rightarrow> 'a THEORY \<Rightarrow> 'a THEORY"
  by (auto simp add:WF_THEORY_def IDEMPOTENT_OVER_def)

definition less_eq_WF_THEORY :: "'a WF_THEORY \<Rightarrow> 'a WF_THEORY \<Rightarrow> bool" where
"less_eq_WF_THEORY x y \<longleftrightarrow> x + y = y"

definition less_WF_THEORY :: "'a WF_THEORY \<Rightarrow> 'a WF_THEORY \<Rightarrow> bool" where
"less_WF_THEORY x y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

instance
  apply (intro_classes)
  apply (simp add:less_eq_WF_THEORY_def)
  apply (simp add:less_WF_THEORY_def)
  apply (rule DestTheory_intro)
  apply (auto simp add:plus_WF_THEORY.rep_eq zero_WF_THEORY.rep_eq)
  apply (case_tac "DestTheory x", case_tac "DestTheory y", case_tac "DestTheory z")
  apply (auto)
  apply (rule DestTheory_intro)
  apply (auto simp add:plus_WF_THEORY.rep_eq zero_WF_THEORY.rep_eq)
  apply (case_tac "DestTheory x", case_tac "DestTheory y")
  apply (auto)
  apply (rule DestTheory_intro)
  apply (auto simp add:plus_WF_THEORY.rep_eq zero_WF_THEORY.rep_eq)
  apply (case_tac "DestTheory x")
  apply (auto)
done
end

*)

lemma TopT_eq:
  assumes 
    "bounded_lattice (OrderT T a)"
    "t \<in> \<lbrakk>T\<rbrakk>[a]\<T>" "\<And> x. \<lbrakk> x \<in> \<lbrakk>T\<rbrakk>[a]\<T> \<rbrakk> \<Longrightarrow> x \<sqsubseteq> t"
  shows "\<top>\<^bsub>T[a]\<^esub> = t"
proof -
  interpret blat: bounded_lattice "OrderT T a"   
    where "partial_object.carrier (OrderT T a) = \<lbrakk>T\<rbrakk>[a]\<T>"
    and "eq (OrderT T a) = op ="
    and "le (OrderT T a) = op \<sqsubseteq>"
    by (simp_all add:assms)
  show ?thesis
    by (auto intro: blat.le_antisym simp add:blat.top_higher blat.top_closed assms)
qed  

lemma BotT_eq:
  assumes 
    "bounded_lattice (OrderT T a)"
    "t \<in> \<lbrakk>T\<rbrakk>[a]\<T>" "\<And> x. \<lbrakk> x \<in> \<lbrakk>T\<rbrakk>[a]\<T> \<rbrakk> \<Longrightarrow> t \<sqsubseteq> x"
  shows "\<bottom>\<^bsub>T[a]\<^esub> = t"
proof -
  interpret blat: bounded_lattice "OrderT T a"   
    where "partial_object.carrier (OrderT T a) = \<lbrakk>T\<rbrakk>[a]\<T>"
    and "eq (OrderT T a) = op ="
    and "le (OrderT T a) = op \<sqsubseteq>"
    by (simp_all add:assms)
  show ?thesis
    by (auto intro: blat.le_antisym simp add:blat.bottom_lower blat.bottom_closed assms)
qed  

end

subsection {* Theory of predicates *}

abbreviation "PREDT \<equiv> \<lparr> alphas = UNIV, health = id \<rparr>"

interpretation PREDT_theory: UTP_THEORY PREDT
  by (unfold_locales, simp add:IDEMPOTENT_OVER_def)

subsection {* Theory of relations *}

lift_definition RELH :: "'a ALPHA_FUNCTION"
is "\<lambda> p. (Abs_fset (\<langle>\<alpha> p\<rangle>\<^sub>f - NON_REL_VAR), \<exists>\<^sub>p NON_REL_VAR. \<pi> p)"
  by (auto simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def unrest)

lemma RELH_alphabet [alphabet]:
  "\<alpha> (RELH p) = Abs_fset (\<langle>\<alpha> p\<rangle>\<^sub>f - NON_REL_VAR)"
  by (simp add:pred_alphabet_def RELH.rep_eq)

lemma RELH_in_REL_ALPHABET [closure]:
  "\<alpha> (RELH p) \<in> REL_ALPHABET"
  by (auto simp add:alphabet REL_ALPHABET_def)

lemma EvalA_RELH [evala]:
  "\<lbrakk>RELH p\<rbrakk>\<pi> = (\<exists>\<^sub>p NON_REL_VAR. \<lbrakk>p\<rbrakk>\<pi>)"
  by (simp add:EvalA_def RELH.rep_eq)

theorem RELH_idem:
  "RELH (RELH p) = RELH p"
  by (utp_alpha_tac, utp_pred_tac)

lemma REL_ALPHABET_UNREST_NON_REL_VAR [unrest]:
  "\<alpha> p \<in> REL_ALPHABET \<Longrightarrow> NON_REL_VAR \<sharp> \<lbrakk>p\<rbrakk>\<pi>"
  by (metis UNREST_NON_REL_VAR_WF_RELATION WF_ALPHA_REL_EvalA_WF_RELATION WF_ALPHA_REL_def mem_Collect_eq)

lemma RELH_REL_ALPHABET:
  "p is RELH \<longleftrightarrow> \<alpha> p \<in> REL_ALPHABET"
  apply (rule iffI)
  apply (metis Healthy_simp RELH_in_REL_ALPHABET)
  apply (utp_alpha_tac)
  apply (simp add:ExistsP_ident unrest)
  apply (metis Diff_Compl NON_REL_VAR_UNDASHED_DASHED REL_ALPHABET_UNDASHED_DASHED Rep_fset_inverse le_iff_inf)
done

abbreviation "RELT \<equiv> \<lparr> alphas = REL_ALPHABET, health = RELH \<rparr>"

interpretation RELT_theory: UTP_THEORY RELT
  by (unfold_locales, auto simp add: IDEMPOTENT_OVER_def RELH.rep_eq RELH_idem)

lemma RELT_WF_ALPHA_REL:https://www.facebook.com/
  "\<lbrakk>RELT\<rbrakk>\<T> = WF_ALPHA_REL"
  by (simp add: THEORY_PRED_def RELH_REL_ALPHABET WF_ALPHA_REL_def)

lemma RELT_WF_ALPHA_REL_closure:
  "P \<in> WF_ALPHA_REL \<Longrightarrow> P \<in> \<lbrakk>RELT\<rbrakk>\<T>"
  by (metis RELT_WF_ALPHA_REL)
  
lemma RELT_AndP_closed:
  "(op \<and>\<^sub>\<alpha>) closed-under RELT"
  by (auto simp add:THEORY_CLOSED_OP_def closure RELT_WF_ALPHA_REL)

lemma RELT_OrP_closed:
  "(op \<or>\<^sub>\<alpha>) closed-under RELT"
  by (auto simp add:THEORY_CLOSED_OP_def closure RELT_WF_ALPHA_REL)

sublocale lattice \<subseteq> weak_partial_order ..

interpretation RELT_lattice: lattice "OrderT RELT a"
  where "partial_object.carrier (OrderT RELT a) = \<lbrakk>RELT\<rbrakk>[a]\<T>"
(*    and "eq (OrderT RELT a) = op =" *)
    and "le (OrderT RELT a) = op \<sqsubseteq>"
  apply (metis RELT_AndP_closed RELT_OrP_closed RELT_theory.OrderT_lattice)
  apply (simp_all)
done

lemma RELT_bounded_lattice:
  "a \<in> REL_ALPHABET \<Longrightarrow> bounded_lattice (OrderT RELT a)"
  apply (unfold_locales)
  apply (rule_tac x="true\<^bsub>a\<^esub>" in exI)
  apply (simp add:least_def alphabet, safe)
  apply (metis RELT_WF_ALPHA_REL_closure THEORY_PRED_OVER_intro TrueA_WF_ALPHA_REL TrueA_alphabet)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (metis THEORY_PRED_OVER_alphabet)
  apply (rule_tac x="false\<^bsub>a\<^esub>" in exI)
  apply (simp add:greatest_def alphabet)
  apply (safe)
  apply (rule THEORY_PRED_OVER_intro)
  apply (metis FalseA_WF_ALPHA_REL RELT_WF_ALPHA_REL)
  apply (simp add:alphabet)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (metis THEORY_PRED_OVER_elim)
done

lemma TopT_RELT:
  "a \<in> REL_ALPHABET \<Longrightarrow> \<top>\<^bsub>RELT[a]\<^esub> = false\<^bsub>a\<^esub>"
  apply (rule RELT_theory.TopT_eq)
  apply (metis RELT_bounded_lattice)
  apply (metis FalseA_WF_ALPHA_REL FalseA_alphabet RELT_WF_ALPHA_REL_closure THEORY_PRED_OVER_closure)
  apply (utp_alpha_tac, utp_pred_auto_tac)
done

lemma BotT_RELT:
  "a \<in> REL_ALPHABET \<Longrightarrow> \<bottom>\<^bsub>RELT[a]\<^esub> = true\<^bsub>a\<^esub>"
  apply (rule RELT_theory.BotT_eq)
  apply (metis RELT_bounded_lattice)
  apply (metis RELT_WF_ALPHA_REL_closure THEORY_PRED_OVER_closure TrueA_WF_ALPHA_REL TrueA_alphabet)
  apply (utp_alpha_tac, utp_pred_auto_tac)
done

default_sort type

class unitary =
  assumes one_elem: "\<And> x y :: 'a. x = y"

instance unit :: unitary
  by (intro_classes, auto)

instantiation THEORY_ext :: (TYPED_MODEL,type) preorder
begin

definition less_eq_THEORY_ext :: "('a, 'b) THEORY_scheme \<Rightarrow> ('a, 'b) THEORY_scheme \<Rightarrow> bool" where
"less_eq_THEORY_ext T1 T2 \<longleftrightarrow> (\<A>\<^bsub>T1\<^esub> \<subseteq> \<A>\<^bsub>T2\<^esub> \<and> (\<forall> p. \<alpha>(p) \<in> \<A>\<^bsub>T1\<^esub> \<longrightarrow> p is \<H>\<^bsub>T1\<^esub> \<longrightarrow> p is \<H>\<^bsub>T2\<^esub>))"

definition less_THEORY_ext :: "('a, 'b) THEORY_scheme \<Rightarrow> ('a, 'b) THEORY_scheme \<Rightarrow> bool" where
"less_THEORY_ext T1 T2 = (T1 \<le> T2 \<and> \<not> T2 \<le> T1)"

instance
  by (intro_classes, auto simp add:less_eq_THEORY_ext_def less_THEORY_ext_def)
end

lemma THEORY_PRED_subseteq [intro]: "T1 \<le> T2 \<Longrightarrow> \<lbrakk>T1\<rbrakk>\<T> \<subseteq> \<lbrakk>T2\<rbrakk>\<T>"
  by (auto simp add: less_eq_THEORY_ext_def THEORY_PRED_def)

lemma RELT_leq_PREDT [intro]: "RELT \<le> PREDT"
  by (simp add: less_eq_THEORY_ext_def closure)

end
