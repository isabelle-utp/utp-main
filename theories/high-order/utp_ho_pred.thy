(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_ho_pred.thy                                                      *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* HO Predicates *}

theory utp_ho_pred
imports "../alpha/utp_alpha" "../tactics/utp_alpha_tac"
  utp_ho_value
  utp_ho_model
  utp_ho_prog
begin

subsection {* Undeclaring Notations *}

text {* Having to undeclare the global typing operator here is an issue. *}

no_notation global_type_rel (infix ":" 50)

no_notation ho_alphabet ("\<alpha>")
no_notation ho_predicate ("\<pi>")

subsection {* Locale @{term HO_PRED} *}

locale HO_PRED = HO_VALUE + ALPHA_PRED "type_rel"
for type_rel :: "HO_VALUE \<Rightarrow> HO_TYPE \<Rightarrow> bool" (infix ":" 50) +
assumes fix_type_rel : "type_rel = ho_type_rel"
begin

text {* Alphabet of HO Variables *}

definition var_alphabet ::
  "HO_TYPE VAR \<Rightarrow> HO_TYPE ALPHABET" where
"var_alphabet v = set (ProgTypeOf (type v))"

notation var_alphabet ("\<alpha>")

subsubsection {* Program Quotes *}

definition MkProg ::
  "(HO_VALUE, HO_TYPE) ALPHA_PREDICATE \<Rightarrow> HO_VALUE" where
"MkProg p \<equiv> ProgVal (Abs_PROG_VALUE p)"

notation MkProg ("\<lbrace>_\<rbrace>")

definition DestProg ::
  "HO_VALUE \<Rightarrow> (HO_VALUE, HO_TYPE) ALPHA_PREDICATE" where
"DestProg p \<equiv> Rep_PROG_VALUE (ProgValOf p)"

notation DestProg ("\<sim>_" [1000] 1000)

subsubsection {* Call Operator *}

definition CallP ::
  "HO_TYPE VAR \<Rightarrow> (HO_VALUE, HO_TYPE) PREDICATE" where
"IsProgVar m \<longrightarrow>
 CallP m = {b \<in> WF_BINDING . b \<in> \<pi> \<sim>(b m)}"

notation CallP ("callp")

definition CallA ::
  "HO_TYPE VAR \<Rightarrow> (HO_VALUE, HO_TYPE) ALPHA_PREDICATE" where
"IsProgVar m \<longrightarrow>
 CallA m = ({m} \<union> (\<alpha> m), CallP m)"

notation CallA ("call")

subsection {* Theorems *}

subsubsection {* HO Model Link *}

-- {* Should all these theorems be default simplifications? *}

theorem HO_ALPHABET_simp [simp] :
"HO_ALPHABET = WF_ALPHABET"
apply (simp add: HO_ALPHABET_def)
done

theorem HO_BINDING_simp [simp] :
"HO_BINDING = WF_BINDING"
apply (simp add: HO_BINDING_def)
apply (simp add: WF_BINDING_def)
apply (simp add: fix_type_rel)
done

theorem HO_PREDICATE_simp [simp] :
"HO_PREDICATE = WF_PREDICATE"
apply (simp add: HO_PREDICATE_def)
apply (simp add: WF_PREDICATE_def)
done

theorem HO_UNREST_simp [simp] :
"HO_UNREST = UNREST"
apply (rule ext)
apply (rule ext)
apply (simp add: HO_UNREST_def)
apply (simp add: UNREST_def)
done

theorem HO_PREDICATE_OVER [simp] :
"HO_PREDICATE_OVER = WF_PREDICATE_OVER"
apply (rule ext)
apply (simp add: HO_PREDICATE_OVER_def)
apply (simp add: WF_PREDICATE_OVER_def)
done

theorem HO_ALPHA_PREDICATE [simp] :
"HO_ALPHA_PREDICATE = WF_ALPHA_PREDICATE"
apply (simp add: HO_ALPHA_PREDICATE_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
done

subsubsection {* Program Values *}

theorem MkProg_inverse [simp] :
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> \<sim>\<lbrace>p\<rbrace> = p"
apply (simp add: MkProg_def DestProg_def)
done

theorem DestProg_inverse [simp] :
"IsProgVal v \<Longrightarrow> \<lbrace>\<sim>v\<rbrace> = v"
apply (simp add: MkProg_def DestProg_def)
apply (atomize (full))
apply (induct_tac v)
apply (simp_all)
done

theorem DestProg_WF_ALPHA_PREDICATE [closure] :
"IsProgVal v \<Longrightarrow> (\<sim> v) \<in> WF_ALPHA_PREDICATE"
apply (simp add: DestProg_def)
apply (atomize (full))
apply (induct_tac v)
apply (simp_all)
apply (simp only: sym [OF HO_ALPHA_PREDICATE])
apply (simp only: PROG_VALUE.Rep)
done

text {* It is interesting to note that the following conjecture does not hold. *}

theorem MkProg_DestProg_type_definition :
"type_definition DestProg MkProg WF_ALPHA_PREDICATE"
apply (simp add: type_definition_def)
apply (safe)
-- {* Subgoal 1 *}
apply (simp add: DestProg_def)
apply (simp only: sym [OF HO_ALPHA_PREDICATE])
apply (simp only: PROG_VALUE.Rep)
-- {* Subgoal 2 *}
apply (simp add: MkProg_def DestProg_def)
-- {* The proof of this subgoal fails! *}
oops

theorem DestProg_alphabet [alphabet] :
"\<lbrakk>IsProgType t; v : t\<rbrakk> \<Longrightarrow>
 \<alpha> (\<sim>v) = set (ProgTypeOf t)"
apply (atomize (full))
apply (induct_tac t)
apply (simp_all)
apply (induct_tac v)
apply (simp_all add: DestProg_def)
apply (simp_all add: fix_type_rel)
done

subsection {* Program Variables *}

theorem WF_ALPHABET_var_alphabet [closure] :
"IsProgVar m \<Longrightarrow> (\<alpha> m) \<in> WF_ALPHABET"
apply (simp add: var_alphabet_def)
apply (simp add: WF_ALPHABET_def)
done

theorem var_alphabet_simp [alphabet] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 IsProgVar m;
 \<lbrace>p\<rbrace> : (type m)\<rbrakk> \<Longrightarrow>
 (\<alpha> m) = (\<alpha> p)"
apply (atomize (full))
apply (induct_tac m)
apply (induct_tac b)
apply (simp_all add: MkProg_def var_alphabet_def)
apply (simp_all add: fix_type_rel)
done

subsubsection {* Binding Theorems *}

theorem IsProgVal_binding_app [simp, intro] :
"\<lbrakk>IsProgVar m; b \<in> WF_BINDING\<rbrakk> \<Longrightarrow> IsProgVal (b m)"
apply (simp add: WF_BINDING_def)
apply (drule_tac x = "m" in spec)
apply (simp add: IsProgVar_def)
apply (simp add: fix_type_rel)
done

theorem DestProg_binding_app_alphabet [alphabet] :
"\<lbrakk>IsProgVar m; b \<in> WF_BINDING\<rbrakk> \<Longrightarrow> \<alpha> \<sim>(b m) = (\<alpha> m)"
apply (subst var_alphabet_simp [where p = "\<sim>(b m)"])
apply (simp_all add: WF_BINDING_app_type closure)
done

subsubsection {* Alphabet Theorems *}

theorem CallP_alphabet [alphabet] :
"IsProgVar m \<Longrightarrow>
 \<alpha> (call m) = {m} \<union> (\<alpha> m)"
apply (simp add: CallA_def)
done

subsubsection {* @{const UNREST}  Theorems *}

theorem pi_WF_PREDICATE_OVER :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE; (\<alpha> p) \<subseteq> a\<rbrakk> \<Longrightarrow>
 \<pi> p \<in> WF_PREDICATE_OVER a"
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (auto intro: unrest)
done

theorem UNREST_CallP [unrest] :
"IsProgVar m \<Longrightarrow>
 UNREST (VAR - insert m (\<alpha> m)) (callp m)"
apply (simp add: CallP_def)
apply (simp add: UNREST_def closure)
apply (clarify)
apply (subgoal_tac "\<pi> \<sim>(b1 m) \<in> WF_PREDICATE_OVER (\<alpha> m)")
apply (simp add: WF_PREDICATE_OVER_def)
apply (clarify)
apply (subgoal_tac "UNREST (VAR - insert m (\<alpha> m)) (\<pi> \<sim>(b1 m))")
apply (simp add: UNREST_binding_override)
apply (erule UNREST_subset)
apply (auto) [1]
apply (assumption)
apply (rule pi_WF_PREDICATE_OVER)
apply (simp add: closure)
apply (simp add: alphabet closure)
done

subsubsection {* Closure Theorems *}

theorem CallP_closure [closure] :
"IsProgVar m \<Longrightarrow>
 callp m \<in> WF_PREDICATE"
apply (simp add: CallP_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

theorem CallA_closure [simp] :
"IsProgVar m \<Longrightarrow>
 call m \<in> WF_ALPHA_PREDICATE"
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (rule conjI)
-- {* Subgoal 1 *}
apply (simp add: alphabet closure)
-- {* Subgoal 2 *}
apply (simp add: CallA_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

subsubsection {* Evaluation Theorems *}

theorem EvalP_CallP [eval] :
"\<lbrakk>IsProgVar m; b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>callp m\<rbrakk>b = \<lbrakk>\<lbrakk>\<sim>(b m)\<rbrakk>\<pi>\<rbrakk>b"
apply (simp add: EvalP_def)
apply (simp add: EvalA_def)
apply (simp add: CallP_def)
done

theorem EvalP_CallA [evala] :
"\<lbrakk>IsProgVar m\<rbrakk> \<Longrightarrow>
 \<lbrakk>call m\<rbrakk>\<pi> = (callp m)"
apply (simp add: EvalA_def)
apply (simp add: CallA_def)
done

theorem EvalP_EvalA (* [eval] *) :
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow>
 \<lbrakk>\<lbrakk>p\<rbrakk>\<pi>\<rbrakk>b = (b \<in> \<pi> p)"
apply (simp add: EvalP_def)
apply (simp add: EvalA_def)
done
end

subsection {* Proof Tactics *}

ML {*
  fun utp_ho_simpset ctxt =
    (simpset_of ctxt)
      addsimps (evala.get ctxt)
      addsimps (eval.get ctxt)
      addsimps (closure.get ctxt)
      (* Closure alone seems not enough e.g. to simplify (p1 \<or>\<alpha> p2) \<sqsubseteq> p2. *)
      addsimps (alphabet.get ctxt);
*}

ML {*
  fun utp_ho_tac thms ctxt i =
    CHANGED (asm_full_simp_tac (utp_ho_simpset ctxt) i)
*}

method_setup utp_ho_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_ho_tac thms ctxt))
*} "proof tactic for higher-order predicates"

subsection {* Proof Experiments *}

context HO_PRED
begin

text {* Variation of a law in Chapter 9 (page 235) of the UTP book. *}

theorem CallP_lemma1 :
"\<lbrakk>IsProgVar m;
 p \<in> WF_ALPHA_PREDICATE;
 \<lbrace>p\<rbrace> : (type m)\<rbrakk> \<Longrightarrow>
 (m =\<alpha> \<lbrace>p\<rbrace> \<and>\<alpha> (call m)) = (m =\<alpha> \<lbrace>p\<rbrace> \<and>\<alpha> p)"
apply (utp_alpha_tac)
apply (utp_pred_auto_tac)
done

theorem CallP_lemma2 :
"\<lbrakk>IsProgVar m;
 p \<in> WF_ALPHA_PREDICATE;
 q \<in> WF_ALPHA_PREDICATE;
 \<lbrace>p\<rbrace> : (type m);
 \<lbrace>q\<rbrace> : (type m)\<rbrakk> \<Longrightarrow>
 (m =\<alpha> \<lbrace>p \<and>\<alpha> q\<rbrace> \<and>\<alpha> (call m)) = (p \<and>\<alpha> m =\<alpha> \<lbrace>p \<and>\<alpha> q\<rbrace> \<and>\<alpha> q)"
apply (utp_ho_tac)
apply (safe)
apply (simp_all add: closure)
-- {* Subgoal 1 *}
apply (simp add: sym [OF var_alphabet_simp])
-- {* Subgoal 2 *}
-- {* Subgoal 3 *}
-- {* Subgoal 4 *}
apply (utp_ho_tac)+
done
end
end