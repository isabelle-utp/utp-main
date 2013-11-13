(******************************************************************************)
(* Project: Mechanation of the UTP                                          *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* CSP Processes *}

theory utp_csp
imports 
  utp_acp
begin

definition CSP1 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CSP1 P = `P \<or> (\<not> ok \<and> ($tr \<le> $tr\<acute>))`"

abbreviation "CSP2 \<equiv> H2"

definition R3c :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R3c P = `CSP1(II) \<lhd> $wait \<rhd> P`"

definition RHc :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"RHc P = (R1 \<circ> R2 \<circ> R3c) P"

definition CSP :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CSP P = (CSP1 \<circ> CSP2 \<circ> RHc) P"

definition StopCSP :: "'a WF_PREDICATE" ("STOP") where
"STOP = `CSP1( ok' \<and> \<delta>)`"

definition PrefixSkipCSP :: "('m EVENT, 'm) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE" ("_ \<rightarrow> SKIP") where
"a \<rightarrow> SKIP = `CSP1(ok' \<and> do\<A>(a))`"

definition SkipCSP :: "'a WF_PREDICATE" ("SKIP") where 
"SKIP = `RHc(\<exists> ref . CSP1(II))`"

syntax
  "_upred_StopCSP" :: "upred" ("STOP")
  "_upred_PrefixSkipCSP" :: "uexpr \<Rightarrow> upred" ("@_")
  "_upred_SkipCSP" :: "upred" ("SKIP")
  
translations
  "_upred_StopCSP" == "CONST StopCSP"
  "_upred_PrefixSkipCSP a" == "CONST PrefixSkipCSP a"
  "_upred_SkipCSP" == "CONST SkipCSP"

definition ChaosCSP :: "'a WF_PREDICATE" ("CHAOS") where
"CHAOS = `CSP(true)`"

definition PrefixCSP :: 
  "('a EVENT, 'a) WF_PEXPRESSION \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_\<rightarrow>_") where
"a\<rightarrow>P = `@a ; P`"

definition InputCSP :: "'b::type CHAN \<Rightarrow> ('b \<Rightarrow> 'a WF_PREDICATE) \<Rightarrow> 'a WF_PREDICATE" where
"InputCSP n P = ExistsShP (\<lambda> v. PrefixCSP (LitPE (PEV n v)) (P v))"

definition OutputCSP :: 
  "'b::type CHAN \<Rightarrow> ('b, 'a) WF_PEXPRESSION \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"OutputCSP n v P = PrefixCSP (EventPE n v) P"

definition ExternalChoiceCSP :: 
  "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" (infixl "\<box>" 65) where
"P \<box> Q = `CSP2((P \<and> Q)\<lhd> STOP \<rhd>(P \<or> Q))`"

definition MergeCSP :: 
  "('a EVENT USET, 'a) WF_PEXPRESSION \<Rightarrow> 
   ('a VAR set * 'a WF_PREDICATE)" where
  "MergeCSP A = ( {okay\<down>\<acute>, wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>}
              , `(($okay\<acute> = $okay\<^bsub>0\<^esub>\<acute> \<and> $okay\<^bsub>1\<^esub>\<acute>) \<and> 
                 ($wait\<acute> = $wait\<^bsub>0\<^esub>\<acute> \<or> $wait\<^bsub>1\<^esub>\<acute>) \<and> 
                 ($ref\<acute> = $ref\<^bsub>0\<^esub>\<acute> \<union> $ref\<^bsub>1\<^esub>\<acute>) \<and> 
                 (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>A \<^esub>($tr\<^bsub>1 \<^esub>- $tr))) ; SKIP`)"

definition HideCSP ::
  "'m WF_PREDICATE \<Rightarrow>
   ('m EVENT USET, 'm) WF_PEXPRESSION \<Rightarrow>
   'm WF_PREDICATE" where
"HideCSP P A = `RHc(\<exists> tr\<acute>\<acute>. P[$tr\<acute>\<acute>/tr\<acute>][($ref\<acute> \<union> A)/ref\<acute>] 
                   \<and> $tr\<acute> = $tr ^ (($tr\<acute>\<acute> - $tr)\<upharpoonright>A)) ; SKIP`"

definition GuardCSP ::
  "'a WF_PREDICATE \<Rightarrow>
   'a WF_PREDICATE \<Rightarrow>
   'a WF_PREDICATE" where
"GuardCSP g P = P \<lhd> g \<rhd> STOP"

definition ParallelCSP :: 
  "'a WF_PREDICATE \<Rightarrow> 
   ('a EVENT USET, 'a) WF_PEXPRESSION \<Rightarrow> 
   'a WF_PREDICATE \<Rightarrow> 
   'a WF_PREDICATE" (infix "\<parallel>\<^bsub>CSP'(_')\<^esub>" 100) where
"P \<parallel>\<^bsub>CSP(A)\<^esub> Q = P \<parallel>\<^bsub>MergeCSP A\<^esub> Q"

definition InterleaveCSP 
  :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" (infix "|||\<^bsub>CSP\<^esub>" 100) where
"P |||\<^bsub>CSP\<^esub> Q = ParallelCSP P |{}| Q"

syntax
  "_upred_ChaosCSP" :: "upred" ("CHAOS")
  "_upred_prefixed"  :: "pexpr \<Rightarrow> upred \<Rightarrow> upred" ("_ -> _")
  "_upred_input"     :: "'a CHAN \<Rightarrow> pttrn \<Rightarrow> upred \<Rightarrow> upred" ("_?_ -> _")
  "_upred_output"    :: "'a CHAN \<Rightarrow> pexpr \<Rightarrow> upred \<Rightarrow> upred" ("_!_ -> _")
  "_upred_extchoice" :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixl "[]" 65)
  "_upred_guardcsp"  :: "upred \<Rightarrow> upred \<Rightarrow> upred" ("[_] & _" [0, 100] 100)
  "_upred_parallel"  :: "upred \<Rightarrow> pexpr \<Rightarrow> upred \<Rightarrow> upred" (infixr "||\<^bsub>_\<^esub>" 100)

syntax (xsymbols)
  "_upred_prefixed"  :: "pexpr \<Rightarrow> upred \<Rightarrow> upred" ("_ \<rightarrow> _")
  "_upred_input"     :: "'a CHAN \<Rightarrow> pttrn \<Rightarrow> upred \<Rightarrow> upred" ("_?_ \<rightarrow> _")
  "_upred_output"    :: "'a CHAN \<Rightarrow> pexpr \<Rightarrow> upred \<Rightarrow> upred" ("_!_ \<rightarrow> _")
  "_upred_extchoice" :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixl "\<box>" 65)
  "_upred_parallel"  :: "upred \<Rightarrow> pexpr \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<parallel>\<^bsub>_\<^esub>" 100)
  "_upred_interleave" :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infix "|||" 100)

translations
  "_upred_ChaosCSP" == "CONST ChaosCSP"
  "_upred_prefixed a P"   == "CONST PrefixCSP a P"
  "_upred_input n v p"    == "CONST InputCSP n (\<lambda> v. p)"
  "_upred_output n v p"   == "CONST OutputCSP n v p"
  "_upred_extchoice P Q"  == "CONST ExternalChoiceCSP P Q"
  "_upred_guardcsp b P"   == "CONST GuardCSP b P"
  "_upred_parallel P A Q" == "CONST ParallelCSP P A Q"
  "_upred_interleave P Q" == "CONST InterleaveCSP P Q"

definition CSP_Pre
  :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE " where
"CSP_Pre P = `\<not>P\<^sup>f[true/okay]\<^sub>f`"

definition CSP_Post
  :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE " where
"CSP_Post P = `P\<^sup>t[true/okay]\<^sub>f`"

declare CSP1_def [eval, evalr, evalrr, evalrx, evalp]
declare CSP_def [eval, evalr, evalrr, evalrx, evalp]
declare StopCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare PrefixSkipCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare SkipCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare ChaosCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare PrefixCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare ExternalChoiceCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare MergeCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare ParallelCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare InterleaveCSP_def [eval, evalr, evalrr, evalrx, evalp]

lemma CSP1_rel_closure[closure]:
  "P \<in> WF_RELATION \<Longrightarrow> CSP1(P) \<in> WF_RELATION"
by (metis CSP1_def DesignD_extreme_point_nok(2) OrP_rel_closure R1_def R1_rel_closure TopD_rel_closure)

lemma CSP2_rel_closure[closure]: 
  "P \<in> WF_RELATION \<Longrightarrow> CSP2(P) \<in> WF_RELATION"
by (metis H2_def J_closure SemiR_closure)

subsection {* CSP1 laws *}

lemma CSP1_idempotent: "`CSP1(CSP1(P))` = `CSP1(P)`" 
  by (utp_pred_auto_tac)

lemma CSP1_monotonic: 
  "P \<sqsubseteq> Q \<Longrightarrow> CSP1(P) \<sqsubseteq> CSP1(Q)"
  by (utp_pred_tac)

lemma CSP1_R1_commute: "CSP1 (R1 P) = R1 (CSP1 (P))"by utp_pred_auto_tac
lemma CSP1_R2_commute: "CSP1 (R2 P) = R2 (CSP1 (P))"by(simp add:CSP1_def R2_def R2s_def usubst typing defined closure, utp_pred_auto_tac)
lemma CSP1_R3c_commute: "CSP1 (R3c P) = R3c (CSP1 (P))"by(simp add:CSP1_def R3c_def, utp_poly_auto_tac)

lemma CSP1_AndP: 
  "`CSP1(P \<and> Q)` = `CSP1(P) \<and> CSP1(Q)`"
  by utp_pred_auto_tac

lemma CSP1_OrP: 
  "`CSP1(P \<or> Q)` = `CSP1(P) \<or> CSP1(Q)`"
  by utp_pred_auto_tac

lemma CSP1_CondR: 
  "`CSP1(P \<lhd> b \<rhd> Q)` = `CSP1(P) \<lhd> b \<rhd> CSP1(Q)`"
  by utp_pred_auto_tac

lemma CSP1_Extend_OrP: 
  "`CSP1(P) \<or> Q` = `CSP1(P \<or> Q)`"
  by utp_pred_auto_tac

lemma CSP1_R1_compose: 
  assumes "P is R1"
  shows "CSP1(P) = `CSP1(ok \<and> P)`"
proof -
  have "CSP1(P) = CSP1 (R1 P)" 
    by (metis Healthy_simp assms)
  thus ?thesis 
    by(utp_pred_auto_tac)
qed

lemma ok_AndP:
  "`ok \<and> P` = `ok \<and> P[true/okay]`"
apply(subst PVarPE_PSubstPE)
apply(simp_all add:typing closure)
done

lemma CSP1_R1_form: 
  assumes "P is R1"
  shows "CSP1(P) = `CSP1(ok \<and> P[true/okay])`"
by (metis CSP1_R1_compose assms ok_AndP)

lemma CSP1_R1_form_2: 
  assumes "P is R1"
  shows "CSP1(P) = `CSP1(ok \<and> P)`"
by (metis CSP1_R1_compose assms)


lemma R3c_form : "`R3c(P)` = `(\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait  \<and> II) \<or> (\<not>$wait \<and> P\<^sub>f)`"
  sorry

lemma R3c_form_2 : "`R3c(P)` = `(\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait  \<and> II) \<or> (\<not>$wait \<and> P)`"
  apply(simp add:R3c_def)
  apply(subst CSP1_R1_form_2)
  apply (metis Healthy_intro R1_SkipR)
  apply(utp_poly_auto_tac)
  done

lemma CSP1_R1_R3c_compose: 
  assumes "P is R1"
  shows "R3c(CSP1(P)) = `(\<not>ok \<and> ($tr\<le>$tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and> P[true/okay][false/wait])`"
  apply(subst CSP1_R1_form)
  apply(metis assms)
  apply(simp add:R3c_form CSP1_def)
  apply(utp_poly_auto_tac)
done

lemma CSP1_R1_R3c_compose_2: 
  assumes "P is R1"
  shows "R3c(CSP1(P)) = `(\<not>ok \<and> ($tr\<le>$tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and> P)`"
  apply(subst CSP1_R1_form_2)
  apply(metis assms)
  apply(simp add:R3c_form_2 CSP1_def)
  apply(utp_pred_auto_tac)
done

lemma CSP1_R3_okay': 
"`CSP1(ok' \<and> R3c(P))` = `CSP1(R3c(ok' \<and> P))`"
apply(simp add:R3c_form CSP1_def SkipR_as_SkipRA)
apply(subst SkipRA_unfold[of "okay \<down>"])
apply(simp_all add:closure)
apply(subst SkipRA_unfold[of "okay \<down>"]) back
apply(simp_all add:closure)
apply(utp_poly_auto_tac)
sorry

subsection {* CSP2 laws *}

lemma CSP2_idempotent: "`CSP2(CSP2(P))` = `CSP2(P)`"
  by (metis H2_idempotent)

lemma CSP2_monotonic:
  "P \<sqsubseteq> Q \<Longrightarrow> CSP2(P) \<sqsubseteq> CSP2(Q)"
  by (metis H2_monotone)

lemma CSP1_CSP2_commute:
  assumes "P \<in> WF_RELATION"
  shows "CSP1 (CSP2 P) = CSP2 (CSP1 P)" 
  apply (simp add: CSP1_def usubst typing defined closure H2_def SemiR_OrP_distr)
  sorry
  
lemma CSP2_form:  
  assumes "P \<in> WF_RELATION"
  shows "`CSP2(P)` = `P\<^sup>f \<or> ok'\<and> P\<^sup>t`"
    apply(simp add:H2_def)
    apply(subst J_split)
    apply (metis assms)
    apply(simp add:AndP_comm)
    done

lemma CSP2_R1_commute: 
  assumes "P \<in> WF_RELATION"
  shows "CSP2 (R1 P) = R1 (CSP2 (P))"
sorry
(*
lemma CSP2_R2_commute:
  assumes "P \<in> WF_RELATION"
  shows"CSP2 (R2 P) = R2 (CSP2 (P))"
by (metis H2_R2_commute assms) *)

lemma CSP2_R3_commute: 
  assumes "P \<in> WF_RELATION"
  shows "CSP2 (R3 P) = R3 (CSP2 (P))"
sorry

subsection {* CSP laws *}
  
lemma CSP_form: 
assumes "P is CSP" "P \<in> WF_RELATION"
shows "P = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P))) \<or> (ok \<and> \<not>$wait \<and>  ok' \<and> R2(CSP_Post(P)))`"
proof-
  have "P = CSP P" 
    by(metis assms(1) is_healthy_def)
  also have "... = `R3(CSP1(R1(CSP2(R2(P)))))`"
  sorry (*
    by (metis CSP1_CSP2_commute CSP1_R2_commute CSP1_R3_commute CSP1_idempotent CSP_def H2_R2_commute H2_R3_commute R1_R3_commute R1_idempotent R2_R3_commute R2_def R2_rel_closure RH_def assms(2) calculation comp_apply)
   also have "...  = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and> ($tr \<le> $tr\<acute>) \<and> R2s(P)\<^sup>f[true/okay]\<^sub>f) \<or> (ok \<and> \<not>$wait \<and> ($tr \<le> $tr\<acute>) \<and> ok' \<and> R2s(P)\<^sup>t[true/okay]\<^sub>f)`" 
    apply(subst CSP1_R1_R3_compose)
    apply (metis Healthy_intro R1_idempotent)
    apply(subst CSP2_form)
    apply(metis assms(2) R2_rel_closure)
    apply(simp add:R1_def usubst typing defined closure)
    apply(utp_pred_auto_tac)
    done
  also have "... =  `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and>  R2(P)\<^sup>f[true/okay]\<^sub>f) \<or> (ok \<and> \<not>$wait \<and> ok' \<and> R2(P)\<^sup>t[true/okay]\<^sub>f)`" 
    apply(simp add:R2_def R1_def usubst typing defined closure)
    apply(utp_pred_auto_tac)
    done
  finally show ?thesis 
  apply(simp add:CSP_Pre_def CSP_Post_def R2_wait_false[THEN sym] R2_okay_true[THEN sym])
  by (smt PVAR_VAR_pvdash R2_okay'_false R2_okay'_true)
qed *) show ?thesis sorry qed

lemma CSP_is_RH: 
assumes "P is CSP" "P \<in> WF_RELATION"
shows "P is RH" sorry (*
proof -
  have "RH (P) = RH (CSP (P))" 
    by (metis Healthy_simp assms(1))
  also have "... = CSP P"
    apply(simp add:CSP_def RH_def)
    apply(subst CSP2_R1_commute)
    apply(metis assms(2) R2_rel_closure R3_rel_closure) 
    sorry show ?thesis sorry qed 
    (*
    apply(subst CSP2_R2_commute)
    apply(metis assms(2) R3_rel_closure)
    apply(subst CSP2_R3_commute)
    apply(metis assms(2))
    apply(subst CSP2_R1_commute)
    apply(metis assms(2) R2_rel_closure R3_rel_closure)
    apply(subst CSP2_R2_commute)
    apply(metis assms(2) R3_rel_closure)
    apply(subst CSP2_R3_commute)
    apply(metis assms(2))
    apply(simp add: CSP1_R1_commute CSP1_R2_commute CSP1_R3_commute)
    apply(simp add:R2_R3_commute R1_R3_commute R3_idempotent R1_R2_commute R2_idempotent R1_idempotent)
    done
  finally show ?thesis
    by (metis Healthy_intro Healthy_simp assms(1))
qed*) *)

lemma CSP_Design: 
assumes "P is CSP" "P \<in> WF_RELATION"
shows "P = `RHc ( CSP_Pre(P) \<turnstile> CSP_Post(P))`"
sorry
(*
subsection {* Stop laws *}

lemma Stop_form : "`STOP`= `CSP1(R3c(ok' \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>))`" 
  apply(simp add:StopCSP_def \<delta>_def)

lemma Stop_expansion  :  "`STOP`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok \<and> II) \<or> (\<not> $wait \<and> ok \<and> ok' \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>)`" 
  apply(simp add:Stop_form CSP1_R3_commute)
  apply(subst CSP1_R1_R3_compose)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
done

lemma Stop_is_R1 : "R1 STOP = STOP "
apply(simp add:Stop_form CSP1_R3_commute R1_R3_commute)
apply(utp_pred_auto_tac)
done

lemma Stop_is_R2 : "R2 STOP = STOP"
proof - 
have "R2 STOP = `CSP1(R3(R2(ok' \<and> ($tr \<acute>=$tr) \<and> $wait \<acute>)))`"
  by(simp add:Stop_form CSP1_R2_commute CSP1_R3_commute R2_R3_commute)
also have "... = `CSP1(R3(ok' \<and> R1(($tr \<acute>-$tr)=\<langle>\<rangle>) \<and> $wait \<acute>))`" 
  by(simp add:R2_def R2s_def usubst typing defined closure, utp_pred_auto_tac)
finally show ?thesis
  by(simp add:R1_def tr_prefix_as_nil Stop_form)
qed

lemma Stop_is_R3 : "R3 STOP = STOP" 
  by(simp add:Stop_form CSP1_R3_commute R3_idempotent)
  
lemma Stop_is_CSP1 : "CSP1 STOP = STOP" 
  by(simp add:Stop_form CSP1_idempotent)

lemma Stop_is_CSP2 :
"CSP2 STOP = STOP"
proof -
  have "CSP2 STOP = `CSP1(CSP2(ok' \<and> \<delta>))`"
    apply(subst CSP1_CSP2_commute)
    apply(subst AndP_rel_closure)
    apply(utp_pred_auto_tac)
    apply(simp add:\<delta>_rel_closure)
    apply(simp_all add:StopCSP_def)
    done
  moreover have "`CSP2(ok' \<and> \<delta>)` = `ok' \<and> \<delta>`"
    by (metis AndP_comm CSP2_okay' \<delta>_rel_closure is_healthy_def)
  ultimately show ?thesis
    by(metis StopCSP_def)
qed

lemma Stop_rel_closure[closure]: 
  "STOP \<in> WF_RELATION"
by(simp add:StopCSP_def closure)

lemma Stop_Design_form:
  "STOP = `RH( true \<turnstile> $wait\<acute> \<and> ($tr\<acute> = $tr))`"
  apply(subst CSP_Design)
  apply (metis CSP_def Healthy_intro RH_def Stop_is_CSP1 Stop_is_CSP2 Stop_is_R1 Stop_is_R2 Stop_is_R3 comp_apply)
  apply (metis Stop_rel_closure)
  apply (subst Stop_expansion)
  apply (subst Stop_expansion)
  apply(simp add:usubst typing defined closure)
  apply( simp add:DesignD_def CSP_Pre_def CSP_Post_def)
  apply(utp_pred_auto_tac)
done

lemma Stop_precondition: 
  "`\<not>STOP\<^sup>f\<^sub>f` = `\<not>CSP1(false)`"
  by(simp add:Stop_expansion usubst typing defined closure CSP1_def)

lemma Stop_postcondition: 
  "`STOP\<^sup>t\<^sub>f` = `CSP1($wait\<acute> \<and> ($tr\<acute> = $tr))`"
  apply(simp add:Stop_expansion usubst typing defined closure CSP1_def)
  apply(utp_pred_auto_tac)
  done

lemma Stop_precondition_2: 
  "`CSP_Pre(STOP)` = `true`"
  by(simp add:CSP_Pre_def Stop_expansion usubst typing defined closure CSP1_def)

lemma Stop_postcondition_2: 
  "`CSP_Post(STOP)` = `($tr\<acute> = $tr) \<and> $wait\<acute>`"
 by(simp add:CSP_Post_def Stop_expansion usubst typing defined closure)

subsection {* Skip laws *}

lemma Skip_form : "`SKIP`= `CSP1(R3(II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>))`" 
proof- 
have "`SKIP`= ` RH (CSP1( \<exists> ref. ok \<and> ($ref\<acute> = $ref) \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>))`"
  apply(simp add:SkipCSP_def SkipREA_CondR_SkipR CondR_def SkipR_as_SkipRA)
  apply(subst SkipRA_unfold[of "ref \<down>"])
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac) 
  apply(utp_pred_auto_tac)
  apply(simp add:ExistsP_OrP_dist)
  apply(subst ExistsP_ident) back
  apply(simp add:unrest closure typing defined)
  apply(simp add:CSP1_def closure typing defined erasure)
  done
also have "... = ` RH (CSP1( \<exists> ref. ($ref\<acute> = $ref) \<and> (ok \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>)))`"
  by(utp_pred_auto_tac)
also have "... = ` RH (CSP1( (\<exists> ref. ($ref\<acute> = $ref)) \<and> (ok \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>)))`"
  proof-
  have "`\<exists> ref. ($ref\<acute> = $ref) \<and> (ok \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>)` = `(\<exists> ref. ($ref\<acute> = $ref)) \<and> (ok \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>)`"
    apply(subst ExistsP_AndP_expand1[THEN sym])
    apply (rule unrest) back
    apply(simp_all add:unrest)
    apply (rule UNREST_subset)
    apply (rule UNREST_SkipRA)
    apply (auto)
  done
  thus ?thesis 
    by metis
  qed
also have "... = ` RH (CSP1(ok \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>))`"
  proof-
  have "`\<exists> ref. ($ref\<acute> = $ref)` = `true`"
    sorry
    thus ?thesis by (metis utp_pred_simps(6))
  qed
also have "... = ` RH (CSP1(II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>))`"
  apply(subst CSP1_R1_compose) back
  apply(simp_all)
  apply(subst SkipRA_unfold[of "tr \<down>"])
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp add:is_healthy_def R1_def)
  apply(utp_pred_auto_tac)
  done
also have "... = `CSP1(RH (II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>))`"
  by(simp add:RH_def CSP1_R1_commute CSP1_R2_commute CSP1_R3_commute)
also have "... =  `CSP1 (R3 (R1 (($tr\<acute> - $tr) = \<langle>\<rangle>) \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}\<^esub>))`"
  apply(subst SkipRA_unfold[of "tr \<down>"])
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp add:RH_def R2_R3_commute R1_R3_commute)
  apply(simp add:R2_def R1_idempotent R2s_def)
  apply(simp add:usubst typing defined closure)
  apply(simp add:R1_def)
  apply(utp_pred_auto_tac)
  done
also have "... = `CSP1 (R3 (($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}\<^esub>))`"
  by(simp add:R1_def tr_prefix_as_nil)
finally show ?thesis
  apply(subst SkipRA_unfold[of "tr \<down>"])
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp add:erasure closure typing defined)
  done
qed

lemma Skip_expansion: 
  "`SKIP`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>)`"
apply(simp add:Skip_form CSP1_R3_commute)
apply(subst CSP1_R1_R3_compose_2)
apply(subst SkipRA_unfold[of "tr \<down>"])
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(simp add:is_healthy_def)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
done


lemma Skip_expansion_2:
  "SKIP = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> ok' \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - REA\<^esub>)`"
  apply(simp add:Skip_expansion)
  apply(subst SkipRA_unfold[of "tr \<down>"])
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(subst SkipRA_unfold[of "wait \<down>"])
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(subst SkipRA_unfold[of "okay \<down>"])
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  sorry

lemma Skip_is_R1: 
  "SKIP is R1"
by(utp_pred_auto_tac)

lemma Skip_is_R2: 
  "SKIP is R2"
proof -
have "`R2(SKIP)` = `R1 (\<not>ok) \<or> 
  (ok \<and> $wait \<and> R1(($tr\<acute> - $tr) = \<langle>\<rangle>) \<and> II\<^bsub>REL_VAR - {tr\<down>, tr\<down>\<acute>}\<^esub>) \<or> 
  (ok \<and> \<not> $wait \<and> R1(($tr\<acute> - $tr) = \<langle>\<rangle>) \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}\<^esub>)`"
apply(simp add:Skip_expansion R2_def R2s_def SkipR_as_SkipRA)
apply(subst SkipRA_unfold[of "tr \<down>"])
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(subst SkipRA_unfold[of "tr \<down>"]) back
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(simp add:usubst typing defined closure)
apply(utp_pred_auto_tac)
done
also have "... = `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> 
  (ok \<and> $wait \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {tr\<down>, tr\<down>\<acute>}\<^esub>) \<or> 
  (ok \<and> \<not> $wait \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}\<^esub>)`"
by(simp add:R1_def tr_prefix_as_nil)
also have "... =`(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> 
  (ok \<and> $wait \<and> II\<^bsub>REL_VAR\<^esub>) \<or> 
  (ok \<and> \<not> $wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>)`"
apply(subst SkipRA_unfold[of "tr \<down>"])back back
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(subst SkipRA_unfold[of "tr \<down>"])back back back
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(simp add:erasure closure typing defined)
done
finally show ?thesis 
  by(simp add:is_healthy_def Skip_expansion SkipR_as_SkipRA)
qed

lemma Skip_is_R3: 
  "SKIP is R3"
by(simp add:Skip_form is_healthy_def CSP1_R3_commute R3_idempotent)

lemma Skip_is_CSP1: 
  "SKIP is CSP1"
by(simp add:Skip_form is_healthy_def CSP1_idempotent)

lemma Skip_rel_closure: 
  "SKIP \<in> WF_RELATION"
sorry

lemma Skip_is_CSP2: 
  "SKIP is CSP2"
proof -
have "CSP2 SKIP = `CSP1((ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<or> (ok \<and> \<not>$wait \<and> ($tr\<acute>=$tr) \<and> ok' \<and> \<not>$wait\<acute> \<and> II\<^bsub>REL_VAR - REA\<^esub>))`"
apply(simp add: CSP1_def H2_def)
apply(subst J_split)
apply(simp add:Skip_rel_closure)
apply(simp add:Skip_expansion_2 usubst typing defined closure)
apply(simp add:SkipR_as_SkipRA)
apply(subst SkipRA_unfold[of "okay \<down>"])
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(subst SkipRA_unfold[of "okay \<down>"]) back
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(simp add:usubst typing defined closure erasure unrest urename)

sorry
thus ?thesis sorry qed

lemma Skip_Design_form: 
  "SKIP = `RH( true \<turnstile> \<not>$wait\<acute> \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - REA\<^esub>)`"
  apply(subst CSP_Design)
  apply (metis (full_types) CSP_def R1_idempotent R2_def RH_def Skip_is_CSP1 Skip_is_CSP2 Skip_is_R2 Skip_is_R3 comp_def is_healthy_def)
  apply (metis Skip_rel_closure)
  apply (subst Skip_expansion_2)
  apply (subst Skip_expansion_2)
  apply(simp add:usubst typing defined closure CSP_Pre_def CSP_Post_def)
  done

lemma Skip_precondition: 
  "CSP_Pre(SKIP) = true"
by(simp add:CSP_Pre_def Skip_expansion_2 usubst typing defined closure)

lemma Skip_postcondition: 
  "CSP_Post(SKIP) = `\<not>$wait\<acute> \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - REA\<^esub>`"
by(simp add:CSP_Post_def Skip_expansion_2 usubst typing defined closure)

subsection {* Chaos laws *}

lemma Chaos_form : "`CHAOS`= `CSP1(R3(R1(true)))`"
  apply(simp add:ChaosCSP_def RH_def R2_R3_commute R1_R3_commute)
  apply(simp add:R2_def R2s_def R1_idempotent usubst typing closure defined)
  done

lemma Chaos_expansion : "`CHAOS`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok \<and> II) \<or> (\<not> $wait \<and> ($tr \<le> $tr\<acute>))`"
apply(simp add:Chaos_form CSP1_R3_commute)
apply(simp add:R1_def)
apply(subst CSP1_R1_R3_compose)
apply (metis R1_by_refinement order_refl)
apply(utp_pred_auto_tac)
done

lemma Chaos_is_R1: 
  "CHAOS is R1"
by(utp_pred_auto_tac)

lemma Chaos_is_R2: 
  "CHAOS is R2"
apply(simp add:is_healthy_def Chaos_form R1_def CSP1_R3_commute R2_R3_commute)
apply(simp add:R2_def CSP1_def R2s_def usubst typing defined closure)
apply(utp_pred_auto_tac)
done

lemma Chaos_is_R3: 
  "CHAOS is R3"
by(simp add:Chaos_form R1_def is_healthy_def CSP1_R3_commute R3_idempotent)

lemma Chaos_is_CSP1: 
  "CHAOS is CSP1"
by(simp add:Chaos_form is_healthy_def CSP1_idempotent)

lemma Chaos_is_CSP2: 
  "CHAOS is CSP2"
apply(simp add:Chaos_form is_healthy_def CSP1_CSP2_commute[THEN sym] closure CSP2_R3_commute CSP2_R1_commute)
by (metis H1_left_zero H3_absorbs_H2_1 H3_def SkipD_is_H1 SkipD_rel_closure)

lemma Chaos_rel_closure: 
  "CHAOS \<in> WF_RELATION"
by(simp add:ChaosCSP_def closure)

lemma Chaos_Design_form: 
  "CHAOS = `RH (false \<turnstile> true )`"
apply(subst CSP_Design)
apply (metis (full_types) CSP_def Chaos_is_CSP1 Chaos_is_CSP2 Chaos_is_R1 Chaos_is_R2 Chaos_is_R3 RH_def comp_def is_healthy_def)
apply(metis Chaos_rel_closure)
apply(simp add:Chaos_expansion)
apply(simp add:usubst typing defined closure CSP_Pre_def CSP_Post_def)
apply(simp add:DesignD_def)
apply(simp add:RH_def R2_R3_commute R1_R3_commute)
apply(simp add:R2_def R1_idempotent R2s_def)
apply(simp add:usubst typing defined closure)
done

lemma Chaos_precondition: 
  "CSP_Pre(CHAOS) = `\<not> R1(true)`"
by(simp add:CSP_Pre_def Chaos_expansion usubst typing defined closure R1_def)

lemma Chaos_postcondition: 
  "CSP_Post(CHAOS) = R1 true"
by(simp add:CSP_Post_def Chaos_expansion usubst typing defined closure R1_def) 

subsection {*Prefix laws *}

lemma Prefix_form :  
  assumes "TR \<sharp> a" 
  shows "`@a`= `CSP1(R3(ok' \<and> (((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))))`"
apply(simp add:PrefixSkipCSP_def)
apply(subst doA_form)
apply(metis assms)
apply (metis (hide_lams, no_types) CSP1_R3_okay' PVAR_VAR_pvdash)
done

lemma Prefix_expansion: 
  assumes "TR \<sharp> a"
  shows "`@a`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> ok' \<and> $wait\<acute>\<and> \<not> $wait \<and> (a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> ok' \<and> \<not> $wait\<acute> \<and> \<not> $wait \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))`" 
proof -
have 1:"`($tr ^ \<langle>a\<rangle> = $tr\<acute>)` =`($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr \<le> $tr\<acute>)` "
by (metis tr_prefix_app)
show ?thesis
apply(subst Prefix_form)
apply(metis assms)
apply(simp add:CSP1_R3_commute)
apply(subst CSP1_R1_R3_compose_2)
apply(subst 1)
apply(utp_pred_auto_tac)
apply(simp add:R1_def CondR_def)
apply(utp_pred_auto_tac)
done
qed

lemma Prefix_is_R1: 
  "`@a` is R1"
by(utp_pred_auto_tac)

lemma Prefix_is_R2:
  assumes "TR \<sharp> a" 
  shows "`@a` is R2"
oops

lemma Prefix_is_R3: 
  "`@a` is R3"
proof -
  have 1: "`do\<A>(a)` = `R3 ( do\<A>(a) )`" by(simp add:doA_is_R3)
  have 2: "`@a` = `CSP1(R3(ok' \<and>do\<A>(a))) `"
    apply(simp add:PrefixSkipCSP_def is_healthy_def)
    apply(subst 1)
    apply (metis CSP1_R3_okay' PVAR_VAR_pvdash)
    done
  show ?thesis 
    apply(simp add:is_healthy_def)
    apply(subst 2)
    apply(subst 2)
    apply(simp add:CSP1_R3_commute R3_idempotent)
    done
qed

lemma Prefix_is_CSP1: 
  "`@a` is CSP1"
by(simp add:PrefixSkipCSP_def is_healthy_def CSP1_idempotent)

lemma Prefix_is_CSP2: 
  assumes "TR \<sharp> a" 
  shows "`@a` is CSP2"
sorry

lemma Prefix_rel_closure: 
  assumes "TR \<sharp> a" 
  shows "`@a` \<in> WF_RELATION"
sorry

lemma Prefix_is_CSP: "`@a` is CSP" 
sorry

lemma Prefix_Design_form:
  assumes "TR \<sharp> a" "{okay\<down>\<acute>,okay\<down>, wait\<down>} \<sharp> a"
  shows "`@a` = `RH ( true \<turnstile> (((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)))`"
proof -
  have 2: "`($tr ^ \<langle>a\<rangle> = $tr\<acute>)\<^sup>t[true/okay]\<^sub>f` = `($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"
    using assms
    apply(simp add:usubst typing defined closure UNREST_subset unrest)
    sorry
  have 3: "`(a \<notin> $ref\<acute>)\<^sup>t[true/okay]\<^sub>f` = `(a \<notin> $ref\<acute>)`" 
    sorry
  have "`@a` =  `RH (true \<turnstile> ($wait\<acute> \<and> (a \<notin> $ref\<acute>)\<^sup>t[true/okay]\<^sub>f \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not> $wait\<acute> \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)\<^sup>t[true/okay]\<^sub>f))`"
apply(subst CSP_Design)
apply(metis Prefix_is_CSP)
apply(metis Prefix_rel_closure assms)
apply(subst Prefix_expansion)
apply(metis assms)
apply(subst Prefix_expansion)
apply(metis assms)
apply(simp add:usubst typing defined closure)
sorry
also have "... = `RH (true \<turnstile> ($wait\<acute> \<and> (a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not> $wait\<acute> \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)))`"
  by (metis "2" "3")
finally have 4: "`@a` =  `RH (true \<turnstile> (((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)))`"
  by(utp_pred_auto_tac)
show ?thesis
  by(subst 4,simp)
qed

lemma Prefix_precondition: 
assumes "TR \<sharp> a"
shows "CSP_Pre `@a` = true"
by(simp add:CSP_Pre_def Prefix_expansion assms usubst typing defined closure)

lemma Prefix_postcondition: 
assumes "TR \<sharp> a"
shows "CSP_Post `@a` = `((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"
sorry

subsection {* Sequential composition *}

lemma Seq_comp_closure: 
assumes "P is CSP" "Q is CSP"
shows "(P ; Q) is CSP"
oops


lemma Seq_comp_form: 
assumes "P is CSP" "Q is CSP" "P \<in> WF_RELATION" "Q\<in> WF_RELATION"
shows "(P ; Q) = `RH (\<not>(\<not>CSP_Pre(P);R1(true)) \<and> \<not>(CSP_Post(P)[false/wait\<acute>];(\<not>CSP_Pre(Q))) \<turnstile> CSP_Post(P);(II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> CSP_Post(Q)))`"
 sorry (* proof -
have 1: "`(\<not>ok \<and> ($tr \<le> $tr\<acute>));Q` = `(\<not>ok \<and> ($tr \<le> $tr\<acute>))`"
proof-
have "Q = CSP1(R1(Q))"
  by (metis CSP1_idempotent CSP_def CSP_is_RH RH_is_R1 assms(2) assms(4) comp_apply is_healthy_def)
hence "`(\<not>ok \<and> ($tr \<le> $tr\<acute>));Q` = `(\<not>ok \<and> ($tr \<le> $tr\<acute>));CSP1(R1(Q))`"
  by metis
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>));(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not>ok \<and> ($tr \<le> $tr\<acute>));(Q \<and> ($tr \<le> $tr\<acute>))`" 
  by (metis (hide_lams, no_types) CSP1_R1_commute CSP1_def OrP_comm R1_def SemiR_OrP_distl)
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not>ok \<and> ($tr \<le> $tr\<acute>));(Q \<and> ($tr \<le> $tr\<acute>))`" 
  apply(subst SemiR_remove_middle_unrest1[of "`\<not>ok \<and> ($tr \<le> $tr\<acute>)`" "`($tr \<le> $tr\<acute>)`" "{okay \<down>}" "`\<not>ok`"])
  apply(simp_all add:closure typing defined unrest)
  apply (metis R1_def R1_rel_closure TopD_def TopD_rel_closure) 
  apply (smt R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
  apply(subst SemiR_AndP_left_precond)
  apply (smt R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6)) sorry
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not>ok \<and> ($tr \<le> $tr\<acute>);(Q \<and> ($tr \<le> $tr\<acute>)))`"
  apply(subst SemiR_AndP_left_precond)
  apply(simp_all add:closure)
  defer
  apply(subst AndP_rel_closure)
  apply(simp_all add:assms)
  by (metis (full_types) R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not>ok \<and> R1(true);R1(Q))`"
  by(utp_pred_auto_tac)
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not>ok \<and> R1(R1(true);R1(Q)))`"
  proof - 
    have "`R1(true);R1(Q)` is R1" 
      apply(subst R1_SemiR_closure)
      apply(simp_all add:closure assms is_healthy_def R1_idempotent)
      done
   thus ?thesis 
      by(metis is_healthy_def)
   qed
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>))`"
  by(utp_pred_auto_tac)
finally show ?thesis 
  ..
qed
have 2: " `(ok \<and> $wait \<and> II);Q` = `ok \<and> $wait \<and> II`"
proof -
have "`(ok \<and> $wait \<and> II);Q` = `ok \<and> $wait \<and> R3(Q)`" 
  apply(subst SemiR_AndP_left_precond)
  apply(simp_all add:closure assms(4))
  apply(subst SemiR_AndP_left_precond)
  apply(simp_all add:closure assms(4))
  apply (metis CSP_is_RH Healthy_simp RH_is_R3 assms(2) assms(4))
  done
also have "... = `ok \<and> $wait \<and> II`"
  apply(simp add:R3_form)
  apply(utp_pred_auto_tac)
  done
finally show ?thesis 
  ..
qed
have 3: " `(ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));Q` = `ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P);R1(true))`"
proof -
have "`(ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));Q` = `(ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));CSP1(R1(Q))`" sorry
also have "... = `(ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));(ok \<and> Q \<and> ($tr \<le> $tr \<acute>))`" sorry
show ?thesis sorry qed
have 4:  "`(ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (\<not>ok \<and> ($tr \<le> $tr\<acute>))`  = `false`"
proof -
have "`(ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (\<not>ok \<and> ($tr \<le> $tr\<acute>))`  = `(ok \<and> \<not> $wait \<and> R2 (CSP_Post(P)) \<and> ok') ; (\<not>ok \<and> ($tr \<le> $tr\<acute>))`"
  by (metis AndP_comm)
also have "... = `(ok \<and> \<not> $wait \<and> R2 (CSP_Post(P)) \<and> ok' \<and> \<not>ok') ; ($tr \<le> $tr\<acute>)`" 
  apply(subst SemiR_AndP_right_precond)
  apply(simp_all add:closure urename AndP_assoc)
  apply(subst AndP_rel_closure)
  apply(subst AndP_rel_closure)
  apply(simp_all add:closure)
  apply(subst R2_rel_closure)
  apply(simp_all add:CSP_Post_def)
  defer 
  apply (smt R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
  apply(subst SubstP_rel_closure)
  apply(subst SubstP_rel_closure)
  apply(subst SubstP_rel_closure)
  apply(simp_all add:closure assms typing defined)
  apply (metis TruePE_erasure UNREST_EXPR_TrueE)
  apply (metis FalsePE_erasure UNREST_EXPR_FalseE)
  done
also have "... = false" 
  apply(subst AndP_contra)
  apply(utp_pred_auto_tac)
  done
finally show ?thesis 
  ..
qed
have 5: "`(ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (ok \<and> \<not> $wait \<and> R2 (\<not> CSP_Pre(Q)))` = `ok \<and> \<not>$wait \<and> R2(CSP_Post(P)[false/wait\<acute>];R2(\<not>CSP_Pre(Q)))`"
proof - 
have "`(ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (ok \<and> \<not> $wait \<and> R2 (\<not> CSP_Pre(Q)))` = `ok \<and> \<not> $wait \<and> R2(\<not>$wait\<acute> \<and> CSP_Post(P)) ; R2 (ok \<and> \<not> CSP_Pre(Q))`"
  sorry
also have "... = `ok \<and> \<not>$wait \<and> R2(CSP_Post(P)[false/wait\<acute>];R2(\<not>CSP_Pre(Q)))`" sorry (*
  apply(subst R2_sequential_composition)
  apply(simp_all add:CSP_Post_def CSP_Pre_def closure)
  apply(subst AndP_rel_closure)
  apply(simp_all add:closure)
  apply(subst SubstP_rel_closure)
  apply(subst SubstP_rel_closure)
  apply(subst SubstP_rel_closure)
  apply(simp_all add:closure assms typing defined)
  apply (metis TruePE_erasure UNREST_EXPR_TrueE)
  apply (metis FalsePE_erasure UNREST_EXPR_FalseE)
  apply(subst AndP_rel_closure)
  apply(simp_all add:closure)
  apply(subst SubstP_rel_closure)
  apply(subst SubstP_rel_closure)
  apply(subst SubstP_rel_closure)
  apply(simp_all add:closure assms typing defined)
  apply (metis FalsePE_erasure UNREST_EXPR_FalseE)
  apply (metis TruePE_erasure UNREST_EXPR_TrueE)
  apply(subst NotP_PVarPE_PSubstPE[of "wait \<acute>"])
sorry *)
have 6: "`(ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(Q)))` = `(ok \<and> \<not>$wait \<and> ok' \<and> R2(CSP_Post(P);(II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> CSP_Post(Q))))`"
sorry
have "P ; Q = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P);R1(true))) \<or> ((ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (\<not>ok \<and> ($tr \<le> $tr\<acute>))) \<or> ((ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (ok \<and> \<not> $wait \<and> R2 (\<not> CSP_Pre(Q)))) \<or> ((ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(Q))))`"
apply(subst CSP_Design)
apply(metis assms(1))
apply(metis assms(3))
apply(subst RH_expansion)
apply(simp add:SemiR_OrP_distr)
apply(simp add:1 2 3)
apply(subst CSP_Design[of "Q"])
apply(metis assms(2))
apply(metis assms(4))
apply(subst RH_expansion)
apply(simp add:SemiR_OrP_distl)
apply(utp_pred_auto_tac)
done
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P);R1(true))) \<or> (ok \<and> \<not>$wait \<and> R2(CSP_Post(P)[false/wait\<acute>];\<not>CSP_Pre(Q))) \<or> (ok \<and> \<not>$wait \<and> ok' \<and> R2(CSP_Post(P);(II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> CSP_Post(Q))))`"
apply(subst 4)
apply(subst 5)
apply(subst 6)
apply(utp_pred_auto_tac)
done 
also have "... = `RH (\<not>(\<not>CSP_Pre(P);R1(true)) \<and> \<not>(CSP_Post(P)[false/wait\<acute>];(\<not>CSP_Pre(Q))) \<turnstile> CSP_Post(P);(II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> CSP_Post(Q)))`"
apply(simp add:RH_expansion)
apply(utp_pred_auto_tac)
done
finally show ?thesis ..
qed*)

subsection {* Prefixed laws *}

lemma 
  assumes "TR \<sharp> a" "{okay\<down>\<acute>, okay\<down>, wait\<down>} \<sharp> a"
  shows "`a \<rightarrow> SKIP` = `@a`" 
apply(simp add:PrefixCSP_def)
apply(subst Prefix_Design_form) back
apply(metis assms(1))
apply(metis assms(2))
apply(subst Seq_comp_form)
apply(metis Prefix_is_CSP)
apply (metis (full_types) CSP_def Healthy_intro Healthy_simp R1_idempotent R2_R3_commute R2_def RH_def Skip_is_CSP1 Skip_is_CSP2 Skip_is_R2 Skip_is_R3 o_eq_dest_lhs)
apply(subst Prefix_rel_closure)
apply(simp_all add:assms Skip_rel_closure)
apply(subst Prefix_expansion)
apply(metis assms(1))
apply(subst Prefix_expansion)
apply(metis assms(1))
apply(subst Prefix_expansion)
apply(metis assms(1))
apply(simp add:Skip_expansion_2)
oops

subsection {*CSP laws*}
(*
lemma L1 : 
  assumes "P is CSP" "P \<in> WF_RELATION"
  shows "`CHAOS ; P` = `CHAOS`"
proof -
  have a: "`((\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($tr \<le> $tr\<acute>)) ; R1 (true)` = `($tr \<le> $tr\<acute>)`"
  proof -
    have 1: "`(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($tr \<le> $tr\<acute>)` = `($tr \<le> $tr\<acute>)`" 
      by(utp_pred_auto_tac)
    have "`((\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($tr \<le> $tr\<acute>)) ; R1 (true)` =`($tr \<le> $tr\<acute>);($tr \<le> $tr\<acute>)`"
      by(simp add: R1_def "1")
    thus ?thesis 
      by(simp add: tr_leq_trans)
  qed
show ?thesis
apply(subst Chaos_Design_form) back
apply(subst Seq_comp_form)
apply (metis CSP_def Chaos_is_CSP1 Chaos_is_CSP2 Chaos_is_R1 Chaos_is_R2 Chaos_is_R3 Healthy_comp R_intro is_healthy_def)
apply(metis assms(1))
apply (metis Chaos_rel_closure)
apply (metis assms(2))
apply(simp add:Chaos_expansion)
apply(simp add:usubst typing defined closure)
apply(simp add:DesignD_def)
apply(subst "a")
apply(simp add:RH_def R1_R2_commute R1_R3_commute)
apply(simp add:R1_def)
apply(utp_pred_auto_tac)
done
qed

thm DesignD_composition

lemma L2 : 
assumes "P is CSP" "P \<in> WF_RELATION"
shows "`STOP ; P` = `STOP`"



proof -
  have 1: "`STOP\<^sup>f[true/okay]\<^sub>f` = `false`" by (metis Stop_precondition_2 utp_pred_simps(2) utp_pred_simps(3))
  have 2: "`STOP\<^sup>t[true/okay]\<^sub>f` = `($tr = $tr\<acute>) \<and> $wait\<acute>`" by (metis EqualP_sym Stop_postcondition_2)
  have " `STOP ; P` = `RH (true \<turnstile> (($tr = $tr\<acute>) \<and> $wait\<acute>) ; (II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> (P\<^sup>t[true/okay]\<^sub>f)))`"
    apply(subst Seq_comp_form_2)
    apply (metis CSP_def Healthy_intro RH_def Stop_is_CSP1 Stop_is_CSP2 Stop_is_R1 Stop_is_R2 Stop_is_R3 comp_apply)
    apply(metis assms(1))
    apply(metis Stop_rel_closure)
    apply(metis assms(2))
    apply(subst 1)
    apply(subst 2)
    apply(subst 2)
    apply(subst SemiR_FalseP_left)
    apply(simp add:usubst typing defined closure)
    done
  also have "... = `RH (true \<turnstile> ($tr = $tr\<acute>) ; ($wait \<and> (II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> (P\<^sup>t[true/okay]\<^sub>f))))`"
    apply(subst SemiR_AndP_right_precond)
    apply(simp add:closure unrest typing defined)
    defer
    apply(utp_pred_auto_tac)
    apply (simp add:urename typing defined closure)
    apply(subst CondR_rel_closure)
    apply(simp_all add:closure)
    sorry
  also have "... = `RH (true \<turnstile> ($tr = $tr\<acute>) ; ($wait \<and> II\<^bsub>REL_VAR-OKAY\<^esub>))`"
    proof -
      have "`($wait \<and> (II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> (P\<^sup>t[true/okay]\<^sub>f)))` = `$wait \<and> II\<^bsub>REL_VAR-OKAY\<^esub>`"by utp_pred_auto_tac
      thus ?thesis by metis
    qed
  also have "... = `RH (true \<turnstile> (($tr = $tr\<acute>) \<and> $wait\<acute>) ; II)`"
    apply(subst SemiR_AndP_right_precond)
    sorry
  also have "... =`RH (true \<turnstile> ($tr = $tr\<acute>) \<and> $wait\<acute>)`"
    by (metis SemiR_SkipR_right)
  also have "... = STOP" 
    by (metis AndP_comm EqualP_sym Stop_Design_form)
  finally show ?thesis
    ..
qed

lemma L3 : "(P \<sqinter> Q) \<box> S = (P \<box> S) \<sqinter> (Q \<box> S)"
oops

lemma L4 : "P \<sqinter> (Q \<box> S) = (P \<sqinter> Q) \<box> (P \<sqinter> S)"
oops

lemma L5 : 
  assumes "P is CSP1" 
  shows "`P \<box> SKIP` \<sqsubseteq> `SKIP` "
oops

lemma L6sub : "`((a1\<rightarrow>P1) \<box> (a2\<rightarrow>P2)); Q` = `(a1\<rightarrow>(P1;Q)) \<box> (a2\<rightarrow>(P2;Q))`"
oops
*)
lemma Prefixed_precondition: "`\<not>(a \<rightarrow> P)\<^sup>f[true/okay]\<^sub>f` = undefined"oops
lemma Prefixed_postcondition: "`(a \<rightarrow> P)\<^sup>t[true/okay]\<^sub>f` = undefined"oops

lemma External_precondition: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows"`CSP_Pre(P \<box> Q)` = `CSP_Pre(P) \<and> CSP_Pre(Q)`"
apply(simp add:ExternalChoiceCSP_def H2_def CSP_Pre_def)
apply(subst J_split)
apply(simp add:assms closure)
apply(simp add:CondR_def Stop_expansion usubst typing defined closure)
apply(utp_pred_auto_tac)
done

lemma External_postcondition:
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows "`CSP_Post(P \<box> Q)` = `\<not>CSP_Pre(P) \<or> \<not>CSP_Pre(Q) \<or> (CSP_Post(P) \<and> CSP_Post(Q) \<and> ($tr\<acute>=$tr) \<and> $wait\<acute>) \<or> ((CSP_Post(P) \<or> CSP_Post(Q)) \<and> \<not>(($tr\<acute>=$tr) \<and> $wait\<acute>))`"
apply(simp add:ExternalChoiceCSP_def H2_def CSP_Post_def CSP_Pre_def)
apply(subst J_split)
apply(simp add:assms closure)
apply(simp add:CondR_def Stop_expansion)
apply(simp add:usubst typing defined closure erasure)
apply(utp_pred_auto_tac)
done

lemma External_is_R1: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is R1" "Q is R1"
shows "P \<box> Q is R1"
apply(simp add:is_healthy_def ExternalChoiceCSP_def)
apply(subst CSP2_R1_commute[THEN sym])
apply(simp add:closure assms)
apply(simp add:R1_CondR R1_AndP R1_OrP)
apply(metis assms is_healthy_def)
done

lemma External_is_R2: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is R2" "Q is R2"
shows "P \<box> Q is R2"
apply(simp add:is_healthy_def ExternalChoiceCSP_def) sorry (*
apply(subst CSP2_R2_commute[THEN sym])
apply(simp add:closure assms)
apply(simp add:R2_CondR_alt R2_AndP R2_OrP)
apply(metis assms is_healthy_def Stop_is_R2)
done *)

lemma External_is_R3: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is R3" "Q is R3"
shows "P \<box> Q is R3"
apply(simp add:is_healthy_def ExternalChoiceCSP_def)
apply(subst CSP2_R3_commute[THEN sym])
apply(simp add:closure assms)
apply(simp add:R3_CondR R3_AndP R3_OrP)
apply(metis assms is_healthy_def)
done

lemma External_is_CSP1: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is CSP1" "Q is CSP1"
shows "P \<box> Q is CSP1"
apply(simp add:is_healthy_def ExternalChoiceCSP_def)
apply(subst CSP1_CSP2_commute)
apply(simp add:closure assms)
apply(simp add:CSP1_CondR CSP1_AndP CSP1_OrP)
apply(metis assms is_healthy_def)
done

lemma External_is_CSP2: 
  "P \<box> Q is CSP2"
by(simp add:ExternalChoiceCSP_def is_healthy_def CSP2_idempotent)

lemma External_rel_closure: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows "P \<box> Q \<in> WF_RELATION"
by(simp add:ExternalChoiceCSP_def closure assms)

lemma External_is_CSP:
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is CSP" "Q is CSP" 
shows  "P \<box> Q is CSP"
proof -
  have "CSP(P \<box> Q) = CSP1 (CSP2 (R1 (R2 (R3 (P \<box> Q)))))"
    by(simp add:CSP_def RH_def)
  also from External_is_R3[of "P" "Q"]  have "... =  CSP1 (CSP2 (R1 (R2 (P \<box> Q))))"
    by(metis is_healthy_def assms CSP_is_RH RH_is_R3)
  also from External_is_R2[of "P" "Q"]  have "... =  CSP1 (CSP2 (R1 (P \<box> Q)))"
    by(metis is_healthy_def assms CSP_is_RH RH_is_R2)
  also from External_is_R1[of "P" "Q"]  have "... =  CSP1 (CSP2 (P \<box> Q))"
    by(metis is_healthy_def assms CSP_is_RH RH_is_R1)
  also from External_is_CSP2[of "P" "Q"] have "... = CSP1 (P \<box> Q)"
    by(simp add:is_healthy_def)
  also from External_is_CSP1[of "P" "Q"] have "... = P \<box> Q"
    by (metis CSP1_idempotent CSP_def assms comp_apply is_healthy_def)
  finally show ?thesis
    by(simp add:is_healthy_def)
qed

lemma External_form: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is CSP" "Q is CSP"
shows "P \<box> Q = `RH((CSP_Pre(P) \<and> CSP_Pre(Q)) \<turnstile> ((CSP_Post(P) \<and> CSP_Post(Q)) \<lhd> ($tr\<acute>=$tr) \<and> $wait\<acute> \<rhd> (CSP_Post(P) \<or> CSP_Post(Q))))`"
apply(subst CSP_Design[of "P \<box> Q"])
apply(simp add: External_is_CSP assms)
apply(simp add: External_rel_closure assms(1) assms(2))
apply(subst External_precondition)
apply(metis assms(1))
apply(metis assms(2))
apply(subst External_postcondition)
apply(metis assms(1))
apply(metis assms(2))
apply(simp add:DesignD_def CSP_Pre_def CSP_Post_def)
apply(utp_pred_auto_tac)
done

lemma Parallel_precondition: "`\<not>(P \<parallel>\<^bsub>vs\<^esub> Q)\<^sup>f[true/okay]\<^sub>f` = undefined"oops
lemma Parallel_postcondition: "`(P \<parallel>\<^bsub>vs\<^esub> Q)\<^sup>t[true/okay]\<^sub>f` = undefined"oops

lemma Law_1: 
  assumes "`P \<box> Q` = `P`" 
  shows "`P\<^sup>f[true/okay]\<^sub>f \<Rightarrow> Q\<^sup>f[true/okay]\<^sub>f \<and> (P\<^sup>t[true/okay]\<^sub>f \<and> STOP) \<Rightarrow> Q\<^sup>t[true/okay]\<^sub>f`" "`(Q\<^sup>t[true/okay]\<^sub>f \<and> \<not>STOP) \<Rightarrow> P\<^sup>t[true/okay]\<^sub>f`"
oops

lemma Law_2: 
  assumes "`P\<^sup>f[true/okay]\<^sub>f \<Rightarrow> Q\<^sup>f[true/okay]\<^sub>f \<and> (P\<^sup>t[true/okay]\<^sub>f \<and> STOP) \<Rightarrow> Q\<^sup>t[true/okay]\<^sub>f \<and> (Q\<^sup>t[true/okay]\<^sub>f \<and> \<not>STOP) \<Rightarrow> P\<^sup>t[true/okay]\<^sub>f`"
  shows "`P \<box> Q` = `P`" 
sorry

lemma Law_3: 
  "`P \<box> Q` = `P` \<longleftrightarrow> `P\<^sup>f[true/okay]\<^sub>f \<Rightarrow> Q\<^sup>f[true/okay]\<^sub>f` \<and> `(P\<^sup>t[true/okay]\<^sub>f \<and> STOP) \<Rightarrow> Q\<^sup>t[true/okay]\<^sub>f` \<and> `(Q\<^sup>t[true/okay]\<^sub>f \<and> \<not>STOP) \<Rightarrow> P\<^sup>t[true/okay]\<^sub>f`"
sorry

lemma Law_4: 
  assumes "`P` = `(a \<rightarrow> R) \<box> S`" "`[Q \<Rightarrow> a \<notin> elems ($tr\<acute>-$tr) \<union> $ref \<union> $ref\<acute>]`" "(VAR - aa) \<sharp> a" "aa \<sharp> P" "aa \<sharp> Q" 
  shows "`P \<parallel>\<^bsub>vs\<^esub> Q` = `(P \<parallel>\<^bsub>vs\<^esub> Q) \<box> (a \<rightarrow> (R \<parallel>\<^bsub>vs\<^esub> Q)) `"
apply(subst Law_2)
sorry
*)
end