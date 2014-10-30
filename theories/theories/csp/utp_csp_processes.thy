(******************************************************************************)
(* Project: Mechanation of the UTP                                            *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* CSP Processes *}

theory utp_csp_processes
imports 
  utp_csp_laws
begin

section {*Process definitions *}

subsection {* Primitive process definitions *}

text {* The deadlocked process STOP is always waiting and engages in no events *}

definition StopCSP :: "'a upred" ("STOP") where
"STOP = `CSP1( $ok\<acute> \<and> R3c($tr\<acute> = $tr \<and> $wait\<acute>))`"

text {* The terminating process SKIP has arbitrary refusals but otherwise leaves all variables unchanged *}

definition SkipCSP :: "'a upred" ("SKIP") where 
"SKIP = `RHc(\<exists> ref . CSP1(II))`"

text {* The divergent process CHAOS allows any healthy behaviour *}

definition ChaosCSP :: "'a upred" ("CHAOS") where
"CHAOS = `CSP(true)`"

text {* The simple prefix @a initially waits to engage in an a event which it can't refuse. After the event occurs, it terminates. *}

definition PrefixSkipCSP :: "('m event, 'm) pexpr \<Rightarrow> 'm upred" ("@_") where
"@a = `CSP1($ok\<acute> \<and> R3c((a \<notin> $ref\<acute> \<and> $tr\<acute>=$tr)\<lhd> $wait\<acute> \<rhd> (($tr^\<langle>a\<rangle> =$tr\<acute>) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>)))`"

syntax
  "_upred_StopCSP" :: "n_upred" ("STOP")
  "_upred_SkipCSP" :: "n_upred" ("SKIP")
  "_upred_ChaosCSP" :: "n_upred" ("CHAOS")
  "_upred_PrefixSkipCSP" :: "n_pexpr \<Rightarrow> n_upred" ("@_")
  
translations
  "_upred_ChaosCSP" == "CONST ChaosCSP"
  "_upred_StopCSP" == "CONST StopCSP"
  "_upred_SkipCSP" == "CONST SkipCSP"
  "_upred_PrefixSkipCSP a" == "CONST PrefixSkipCSP a"

declare StopCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare PrefixSkipCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare SkipCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare ChaosCSP_def [eval, evalr, evalrr, evalrx, evalp]

subsection {* Composite process definitions *}

text {*The prefixed process a \<rightarrow> P first waits for an a which it cannot refuse. After the a occurs, it behaves as P *}

definition PrefixCSP :: 
  "('a event, 'a) pexpr \<Rightarrow> 'a upred \<Rightarrow> 'a upred" ("_\<rightarrow>_") where
"a\<rightarrow>P = `@a ; P`"

definition InputCSP :: "'b::DEFINED chan \<Rightarrow> ('b \<Rightarrow> 'a upred) \<Rightarrow> 'a upred" where
"InputCSP n P = ExistsShP (\<lambda> v. PrefixCSP (LitPE (PEvent n v)) (P v))"

definition OutputCSP :: 
  "'b::DEFINED chan \<Rightarrow> ('b, 'a) pexpr \<Rightarrow> 'a upred \<Rightarrow> 'a upred" where
"OutputCSP n v P = PrefixCSP (EventPE n v) P"

text {* The external choice A \<box> B can behave as A or B, but cannot refuse the initial behaviours of either *}

definition ExternalChoiceCSP :: 
  "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" (infixl "\<box>" 65) where
"P \<box> Q = `CSP2((P \<and> Q)\<lhd> STOP \<rhd>(P \<or> Q))`"

text {* The guarded process g & P behaves like P if condition g holds, but is otherwise deadlocked. *}

definition GuardCSP ::
  "'a upred \<Rightarrow>
   'a upred \<Rightarrow>
   'a upred" where
"GuardCSP g P = P \<lhd> g \<rhd> STOP"

syntax
  "_upred_prefixed"  :: "n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_ -> _")
  "_upred_input"     :: "'a chan \<Rightarrow> pttrn \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_?_ -> _")
  "_upred_output"    :: "'a chan \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_!_ -> _")
  "_upred_extchoice" :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixl "[]" 65)
  "_upred_guardcsp"  :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("[_] & _" [0, 100] 100)

syntax (xsymbols)
  "_upred_prefixed"  :: "n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_ \<rightarrow> _")
  "_upred_input"     :: "'a chan \<Rightarrow> pttrn \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_?_ \<rightarrow> _")
  "_upred_output"    :: "'a chan \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_!_ \<rightarrow> _")
  "_upred_extchoice" :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixl "\<box>" 65)

translations
  "_upred_prefixed a P"   == "CONST PrefixCSP a P"
  "_upred_input n v p"    == "CONST InputCSP n (\<lambda> v. p)"
  "_upred_output n v p"   == "CONST OutputCSP n v p"
  "_upred_extchoice P Q"  == "CONST ExternalChoiceCSP P Q"
  "_upred_guardcsp b P"   == "CONST GuardCSP b P"

declare PrefixCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare ExternalChoiceCSP_def [eval, evalr, evalrr, evalrx, evalp]

section {* Operator closure and design forms *}

subsection {* Stop laws *}

lemma Stop_R1 : "STOP is R1"
apply(simp add:StopCSP_def is_healthy_def CSP1_R1_commute[THEN sym])
apply(subst AndP_comm, simp add:R1_extend_AndP[THEN sym] R1_R3c_commute)
apply(simp add:R1_def tr_eq_is_R1, subst AndP_comm) back
apply(simp)
done

lemma Stop_R2 : "STOP is R2"
apply(simp add:StopCSP_def is_healthy_def CSP1_R2_commute[THEN sym])
apply(subst AndP_comm, simp add:R2_def R2s_AndP R1_extend_AndP[THEN sym], simp add:R2_def[THEN sym] R2_R3c_commute)
apply(simp add:R2_def R2s_def usubst typing defined closure R1_extend_AndP[THEN sym], subst AndP_comm) back
apply(simp add:R1_def tr_prefix_as_nil)
done

lemma Stop_R3c : "STOP is R3c"
apply(simp add:StopCSP_def is_healthy_def CSP1_R3c_commute[THEN sym] R3c_def CSP1_SkipR)
apply(utp_pred_auto_tac)
done

lemma Stop_CSP1 : "STOP is CSP1"
by(simp add:StopCSP_def is_healthy_def CSP1_idempotent)

lemma Stop_CSP2: "STOP is CSP2"
apply(simp add:StopCSP_def is_healthy_def)
apply(simp add:R3c_def CSP1_SkipR)
apply(simp add:CSP1_def H2_split usubst typing defined closure)
apply(utp_pred_auto_tac)
done

lemma Stop_CSP : "STOP is CSP"
proof -
  have 1: "CSP2 STOP = STOP"
    by(metis is_healthy_def Stop_CSP2)
  have 2: "CSP1 STOP = STOP"
    by(metis is_healthy_def Stop_CSP1)
  have 3: "R3c STOP = STOP" 
    by(metis is_healthy_def Stop_R3c)
  have 4: "R2 STOP = STOP" 
    by(metis is_healthy_def Stop_R2)
  have 5: "R1 STOP = STOP" 
    by(metis is_healthy_def Stop_R1)
  show ?thesis 
  apply(simp add: is_healthy_def CSP_def RHc_def)
  apply (metis 1 2 3 4 5)
  done
qed

lemma Stop_rel_closure[closure] : "STOP \<in> WF_RELATION"
by(simp add:StopCSP_def closure)

lemma Stop_pre: "`CSP_Pre(STOP)` = `true`"
apply(simp add:StopCSP_def CSP_Pre_def R3c_def CSP1_SkipR)
apply(simp add:CSP1_def usubst typing defined closure)
done

lemma Stop_post: "`CSP_Post(STOP)` = `($tr \<acute>=$tr) \<and> $wait \<acute>`"
apply(simp add:StopCSP_def CSP_Post_def R3c_def CSP1_SkipR)
apply(simp add:CSP1_def usubst typing defined closure)
done

lemma Stop_design : "`STOP` = `RHc ( true \<turnstile> ($tr\<acute>=$tr) \<and> $wait\<acute>)`"
by(subst CSP_Design, simp_all add:Stop_pre Stop_post Stop_CSP Stop_rel_closure)

subsection {* Skip laws *}

lemma Skip_R1 : "SKIP is R1"
by(simp add:SkipCSP_def is_healthy_def RHc_def R1_idempotent)

lemma Skip_R2 : "SKIP is R2"
by(simp add:SkipCSP_def is_healthy_def RHc_def R1_R2_commute R2_idempotent)

lemma Skip_R3c : "SKIP is R3c"
by(simp add:SkipCSP_def is_healthy_def RHc_def R2_R3c_commute R1_R3c_commute R3c_idempotent)

lemma Skip_form: "SKIP = `R3c ( CSP1 ( II\<^bsub> REL_VAR - {ref \<down>,ref \<down>\<acute>}\<^esub>))`"
proof -
  have "SKIP = `RHc (CSP1 ( II\<^bsub>REL_VAR - {ref \<down>, ref \<down>\<acute>}\<^esub>))`"
apply(simp add:SkipCSP_def SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "ref "])
apply(simp_all add:closure typing CSP1_def ExistsP_OrP_dist)
apply(subst ExistsP_ident,simp add:unrest)
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(subst UNREST_subset[of "- (REL_VAR - {ref \<down>,ref \<down>\<acute>})"])
apply(subst UNREST_SkipRA)
apply(simp_all add:closure CSP1_def[THEN sym])
  apply(subst PEqualP_sym)
  apply(simp add:erasure closure typing defined)
  apply(subst ExistsP_has_value[of _ "ref \<down>"])
  apply(simp_all add:typing defined unrest)
done
also have "... = `R3c (CSP1 (II\<^bsub>REL_VAR - {ref \<down>, ref \<down>\<acute>}\<^esub>))`"
apply(simp add: RHc_def R2_def R1_idempotent)
apply(simp add:R2_def[THEN sym] R2_R3c_commute CSP1_R2_commute[THEN sym])
apply(subst SkipRA_unfold[of "tr \<down>"], simp_all add:closure)
apply(simp add:R2_def R2s_def usubst typing closure defined R1_extend_AndP[THEN sym])
apply(simp add:R1_def tr_prefix_as_nil)
apply(subst SkipRA_unfold_aux_ty[of "tr "],simp_all add:typing closure defined) back
apply(subst tr_prefix_as_nil[THEN sym])
apply(utp_poly_tac)
done
finally show ?thesis by this
qed

lemma Skip_CSP1 : "SKIP is CSP1"
by(simp add:Skip_form is_healthy_def CSP1_R3c_commute CSP1_idempotent)

lemma Skip_CSP2: "SKIP is CSP2"
apply(simp add:Skip_form is_healthy_def)
apply(simp add: CSP2_R3c_commute closure)
apply(subst CSP1_R1_form_2) defer
apply(simp add: CSP1_CSP2_commute[THEN sym] closure)
apply(subst SkipRA_unfold_aux_ty[of "ok "], simp_all add:closure typing)
apply(simp add:H2_split usubst typing defined closure)
apply(subst CSP1_R1_form_2) back defer
apply(subst SkipRA_unfold_aux_ty[of "ok "], simp_all add:closure typing) back back
apply(utp_poly_auto_tac)
apply(simp add:is_healthy_def R1_def)
apply(subst SkipRA_unfold_aux_ty[of "tr"], simp_all add:closure typing)
apply(subst SkipRA_unfold_aux_ty[of "tr"], simp_all add:closure typing AndP_assoc[THEN sym]) back
apply(subst AndP_comm, simp add:AndP_assoc tr_eq_is_R1)
done

lemma Skip_CSP : "SKIP is CSP"
proof -
  have 1: "CSP2 SKIP = SKIP"
    by(metis is_healthy_def Skip_CSP2)
  have 2: "CSP1 SKIP = SKIP"
    by(metis is_healthy_def Skip_CSP1)
  have 3: "R3c SKIP = SKIP" 
    by(metis is_healthy_def Skip_R3c)
  have 4: "R2 SKIP = SKIP" 
    by(metis is_healthy_def Skip_R2)
  have 5: "R1 SKIP = SKIP" 
    by(metis is_healthy_def Skip_R1)
  show ?thesis 
  apply(simp add: is_healthy_def CSP_def RHc_def)
  apply (metis 1 2 3 4 5)
  done
qed

lemma Skip_rel_closure[closure] : "SKIP \<in> WF_RELATION"
by(simp add:Skip_form closure)

(* FIXME: Sorried the proof below (Frank Zeyda). Fix it! *)

lemma Skip_expansion: "SKIP =   `(\<not>$ok \<and> ($tr \<le> $tr \<acute>)) \<or> 
  ($ok \<and> $wait \<and> $ref \<acute>=$ref \<and> $wait \<acute> \<and> $tr \<acute>=$tr \<and> $ok\<acute> \<and> II\<^bsub>REL_VAR -REA - OKAY\<^esub>) \<or> 
  ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> $tr \<acute>=$tr\<and> $ok\<acute> \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>)`"
proof-
have "SKIP =
  `(\<not>$ok \<and> ($tr \<le> $tr \<acute>)) \<or> 
  ($ok \<and> $wait \<and> II\<^bsub>REL_VAR\<^esub>) \<or> 
  ($ok \<and> \<not>$wait \<and> II\<^bsub>REL_VAR - {ref \<down>, ref \<down>\<acute>}\<^esub>)`"
apply(simp add:Skip_form)
apply(subst CSP1_R1_form_2) 
apply(subst SkipRA_unfold_aux_ty[of "tr"], simp_all add:typing closure is_healthy_def R1_def)
apply(subst AndP_comm,simp_all add: AndP_assoc[THEN sym] tr_eq_is_R1)
apply(metis AndP_comm)
apply(simp add: R3c_form SkipR_as_SkipRA CSP1_def)
apply(utp_poly_auto_tac)
done
also have "... =
  `(\<not>$ok \<and> ($tr \<le> $tr \<acute>)) \<or> 
  ($ok \<and> $wait \<and> $ref \<acute>=$ref \<and> $wait \<acute>=$wait \<and> $tr \<acute>=$tr \<and> $ok \<acute>=$ok \<and> II\<^bsub>REL_VAR -{ref \<down>,ref \<down>\<acute>} - {wait \<down>, wait \<down>\<acute>} - {tr \<down>,tr \<down>\<acute>} - {ok \<down>,ok \<down>\<acute>}\<^esub>) \<or> 
  ($ok \<and> \<not>$wait \<and> $wait \<acute>=$wait \<and> $tr \<acute>=$tr\<and> $ok \<acute>=$ok \<and> II\<^bsub>REL_VAR - {ref \<down>, ref \<down>\<acute>} - {wait \<down>, wait \<down>\<acute>} - {tr \<down>,tr \<down>\<acute>} - {ok \<down>,ok \<down>\<acute>}\<^esub>)`"
  apply(subst SkipRA_unfold_aux_ty[of "ref"], simp_all add:typing closure)
  apply(subst SkipRA_unfold_aux_ty[of "wait"], simp_all add:typing closure)
  apply(subst SkipRA_unfold_aux_ty[of "wait"], simp_all add:typing closure) back
  apply(subst SkipRA_unfold_aux_ty[of "tr"], simp_all add:typing closure)
  apply(subst SkipRA_unfold_aux_ty[of "tr"], simp_all add:typing closure) back
  apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:typing closure)
  apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:typing closure) back
  done
also have "... =
  `(\<not>$ok \<and> ($tr \<le> $tr \<acute>)) \<or> 
  ($ok \<and> $wait \<and> $ref \<acute>=$ref \<and> $wait \<acute> \<and> $tr \<acute>=$tr \<and> $ok\<acute> \<and> II\<^bsub>REL_VAR -{ref \<down>,ref \<down>\<acute>} - {wait \<down>, wait \<down>\<acute>} - {tr \<down>,tr \<down>\<acute>} - {ok \<down>,ok \<down>\<acute>}\<^esub>) \<or> 
  ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> $tr \<acute>=$tr\<and> $ok\<acute> \<and> II\<^bsub>REL_VAR - {ref \<down>, ref \<down>\<acute>} - {wait \<down>, wait \<down>\<acute>} - {tr \<down>,tr \<down>\<acute>} - {ok \<down>,ok \<down>\<acute>}\<^esub>)`"
by(utp_poly_auto_tac)
also have "... =
  `(\<not>$ok \<and> ($tr \<le> $tr \<acute>)) \<or> 
  ($ok \<and> $wait \<and> $ref \<acute>=$ref \<and> $wait \<acute> \<and> $tr \<acute>=$tr \<and> $ok\<acute> \<and> II\<^bsub>REL_VAR -REA - OKAY\<^esub>) \<or> 
  ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> $tr \<acute>=$tr\<and> $ok\<acute> \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>)`"
proof -
  have 1: "`II\<^bsub>REL_VAR -{ref \<down>,ref \<down>\<acute>} - {wait \<down>, wait \<down>\<acute>} - {tr \<down>,tr \<down>\<acute>} - {ok \<down>,ok \<down>\<acute>}\<^esub>` = `II\<^bsub>REL_VAR -REA - OKAY\<^esub>`" 
    by (smt Diff_insert2 insert_commute)
  show ?thesis
    by(metis 1)
qed
finally show ?thesis sorry
qed

lemma Skip_pre: "`CSP_Pre(SKIP)` = `true`"
apply(simp add:Skip_expansion CSP_Pre_def)
apply(simp add:usubst typing defined closure)
done

lemma Skip_post: "`CSP_Post(SKIP)` = `($tr \<acute>=$tr) \<and> \<not>$wait\<acute> \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub> `"
apply(simp add:Skip_expansion CSP_Post_def)
apply(simp add:SubstP_AndP SubstP_OrP)
apply(simp add:usubst typing defined closure)
by (smt AndP_assoc AndP_comm ParallelD_assoc ParallelD_comm SemiR_assoc SkipRA.rep_eq Un_def inf_sup_aci(5) insert_commute insert_compr set_diff_eq sup_assoc utp_pred_simps(15))

lemma Skip_design : "`SKIP` = `RHc ( true \<turnstile> ($tr\<acute>=$tr) \<and> \<not>$wait\<acute> \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>)`"
by(subst CSP_Design, simp_all add:Skip_pre Skip_post Skip_CSP Skip_rel_closure)


lemma Skipform2: "`SKIP` = `(\<not>$ok \<and> ($tr\<le>$tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> II\<^bsub>REL_VAR - {ref\<down>,ref\<down>\<acute>}\<^esub>)`"
proof - 
have a: "REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>} 
        =REL_VAR - {wait\<down>, wait\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>} - {ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}"
by(utp_poly_auto_tac)
have b:  "REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>} 
         =REL_VAR - {ref\<down>, ref\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}"
by(utp_poly_auto_tac)
show ?thesis
apply(simp add:Skip_expansion SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing defined closure) back back
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure) back back
apply(subst SkipRA_unfold_aux_ty[of "ref"],simp_all add:typing defined closure) back back
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing defined closure) back back
apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing defined closure) back back back
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure) back back back
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing defined closure) back back back
apply(subst a)
apply(subst b)
apply(utp_poly_auto_tac)
done
qed

subsection {* Chaos laws *}

lemma Chaos_form : "`CHAOS`= `CSP1(R3c(R1(true)))`"
  apply(simp add:ChaosCSP_def CSP_def RHc_def R2_R3c_commute R1_R3c_commute)
  apply(simp add:R2_def R2s_def R1_idempotent usubst typing closure defined)  
  apply(simp add:CSP2_R1_commute CSP2_R3c_commute closure)
  apply(simp add:H2_split usubst typing defined closure)
  done

lemma Chaos_expansion : "`CHAOS`= `(\<not> $ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> $ok \<and> II) \<or> ($ok \<and> \<not> $wait \<and> ($tr \<le> $tr\<acute>))`"
apply(simp add:Chaos_form CSP1_R3c_commute)
apply(simp add:R1_def)
apply(subst CSP1_R1_R3c_compose)
apply (metis R1_by_refinement order_refl)
apply(simp add:usubst typing defined closure)
apply(utp_pred_auto_tac)
done

lemma Chaos_R1: 
  "CHAOS is R1"
by(simp add:ChaosCSP_def is_healthy_def CSP_def RHc_def CSP1_R1_commute[THEN sym] CSP2_R1_commute[THEN sym] closure R1_idempotent)

lemma Chaos_R2: 
  "CHAOS is R2"
by(simp add:ChaosCSP_def is_healthy_def CSP_def RHc_def CSP1_R2_commute[THEN sym] CSP2_R2_commute[THEN sym] closure R1_R2_commute R2_idempotent)

lemma Chaos_R3c: 
  "CHAOS is R3c"
by(simp add:Chaos_form CSP1_R3c_commute R3c_idempotent is_healthy_def)

lemma Chaos_CSP1: 
  "CHAOS is CSP1"
by(simp add:Chaos_form is_healthy_def CSP1_idempotent)

lemma Chaos_CSP2: 
  "CHAOS is CSP2"
by(simp add:ChaosCSP_def CSP_def is_healthy_def CSP1_CSP2_commute[THEN sym] closure RHc_def CSP2_idempotent)

lemma Chaos_CSP: 
  "CHAOS is CSP"
proof -
  have 1: "CSP2 CHAOS = CHAOS"
    by(metis is_healthy_def Chaos_CSP2)
  have 2: "CSP1 CHAOS = CHAOS"
    by(metis is_healthy_def Chaos_CSP1)
  have 3: "R3c CHAOS = CHAOS" 
    by(metis is_healthy_def Chaos_R3c)
  have 4: "R2 CHAOS = CHAOS" 
    by(metis is_healthy_def Chaos_R2)
  have 5: "R1 CHAOS = CHAOS" 
    by(metis is_healthy_def Chaos_R1)
  show ?thesis 
  apply(simp add: is_healthy_def CSP_def RHc_def)
  apply (metis 1 2 3 4 5)
  done
qed

lemma Chaos_rel_closure[closure]: 
  "CHAOS \<in> WF_RELATION"
by(simp add:ChaosCSP_def CSP_def RHc_def closure)

lemma Chaos_pre: 
  "CSP_Pre(CHAOS) = `\<not> R1(true)`"
by(simp add:CSP_Pre_def Chaos_expansion usubst typing defined closure R1_def)

lemma Chaos_post: 
  "CSP_Post(CHAOS) = R1 true"
by(simp add:CSP_Post_def Chaos_expansion usubst typing defined closure R1_def) 

lemma Chaos_design: 
  "CHAOS = `RHc ( false \<turnstile> true )`"
apply(subst CSP_Design, simp_all add: Chaos_rel_closure Chaos_pre Chaos_post Chaos_CSP) 
apply(simp add:DesignD_form RHc_def R1_R2_commute R1_R3c_commute)
apply(utp_poly_auto_tac)
done

subsection {*Prefix laws *}

lemma Prefix_form: 
  "@a = `CSP1 (R3c ($ok\<acute> \<and> ((a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<lhd> $wait\<acute> \<rhd> (($tr ^ \<langle>a\<rangle> = $tr\<acute>)\<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>))))`"
apply(simp add:PrefixSkipCSP_def R3c_def SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:typing closure)
apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:typing closure) back back
apply(subst SkipRA_unfold_aux_ty[of "tr"], simp_all add:typing closure)
apply(subst SkipRA_unfold_aux_ty[of "tr"], simp_all add:typing closure) back back
apply(utp_poly_auto_tac)
done

lemma Prefix_R1: 
  "@a is R1"
    apply(simp add:PrefixSkipCSP_def is_healthy_def CSP1_R1_commute[THEN sym])
    apply(subst AndP_comm)
    apply(subst AndP_comm) back 
    apply(simp add:R1_extend_AndP[THEN sym] R1_R3c_commute CondR_def)
    apply(simp add:R1_OrP)
    apply(simp add:R1_def AndP_assoc[THEN sym] tr_eq_is_R1 tr_prefix_app)
    apply(simp add:CondR_def[THEN sym])
    apply(subst AndP_comm) back back
    apply(subst AndP_comm) back back
    apply(simp)
  done

lemma Prefix_R2:
  assumes "{tr \<down>} \<sharp> a" "{tr \<down>\<acute>} \<sharp> a" 
  shows "@a is R2"
apply(simp add:is_healthy_def Prefix_form CSP1_R2_commute[THEN sym] R2_R3c_commute)
apply(subst AndP_comm)
apply(simp add:R2_def R2s_AndP R1_extend_AndP[THEN sym] SubstP_AndP)
apply(simp add:R2_def R2s_def usubst typing closure defined assms PSubstPE_VarP_single_UNREST)
apply(simp add:R1_CondR)
apply(subst AndP_comm) back 
apply(simp add:R1_def AndP_assoc[THEN sym] tr_prefix_as_nil tr_prefix_as_a)
apply(metis AndP_comm)
done

lemma Prefix_R3c: 
  "@a is R3c"
by(simp add:Prefix_form is_healthy_def CSP1_R3c_commute R3c_idempotent)

lemma Prefix_CSP1: 
  "@a is CSP1"
by(simp add:PrefixSkipCSP_def is_healthy_def CSP1_idempotent)

lemma Prefix_CSP2: 
  assumes "{ok \<down>\<acute>} \<sharp> a" 
  shows "@a is CSP2"
apply(simp add:is_healthy_def Prefix_form)
apply(subst CSP1_CSP2_commute[THEN sym])
apply(subst CSP2_R3c_commute)
apply(simp add:H2_split usubst typing defined closure assms PSubstPE_VarP_single_UNREST)
apply(metis AndP_comm)
done

lemma Prefix_rel_closure[closure]: 
  assumes "NON_REL_VAR \<sharp> a"
  shows "@a \<in> WF_RELATION"
by(simp_all add:closure typing defined PrefixSkipCSP_def assms tr_eq_rel_closure a_notin_ref_closure tr_prefix_a_closure)

lemma Prefix_CSP: 
  assumes "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a"
  shows "@a is CSP" 
proof -
  have 0: "{tr \<down>} \<sharp> a" "{tr \<down> \<acute>} \<sharp> a" "{ok \<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
  have 1: "CSP2 `@a` = `@a`"
  by(metis is_healthy_def Prefix_CSP2 0)
  have 2: "CSP1 `@a` = `@a`"
    by(metis is_healthy_def Prefix_CSP1)
  have 3: "R3c `@a` = `@a`" 
    by(metis is_healthy_def Prefix_R3c)
  have 4: "R2 `@a` = `@a`" 
    by(metis is_healthy_def Prefix_R2 0)
  have 5: "R1 `@a` = `@a`" 
    by(metis is_healthy_def Prefix_R1)
  show ?thesis 
  apply(simp add: is_healthy_def CSP_def RHc_def)
  apply (metis 1 2 3 4 5)
  done
qed

lemma Prefix_pre: 
"`CSP_Pre(@a)` = `true`"
by(simp add:Prefix_form CSP_Pre_def CSP1_def R3c_def usubst typing defined closure)

lemma Prefix_post: 
  assumes "{ok \<down>,wait \<down>,ok \<down>\<acute>} \<sharp> a" 
  shows "CSP_Post `@a` = `(a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<lhd> $wait\<acute> \<rhd> (($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>)`"
proof -
  have 0: "{ok \<down>} \<sharp> a" "{wait \<down>} \<sharp> a" "{ok \<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
show ?thesis
by(simp add:Prefix_form CSP_Post_def CSP1_def R3c_def usubst typing defined closure 0  PSubstPE_VarP_single_UNREST)
qed 

lemma Prefix_design: 
  assumes "NON_REL_VAR \<sharp> a" "{tr \<down>,tr \<down>\<acute>,ok \<down>,ok \<down>\<acute>,wait \<down>} \<sharp> a"
  shows "`@a` = `RHc ( true \<turnstile> ((a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<lhd> $wait\<acute> \<rhd> (($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>)))`"
proof -
have  0: "{ok \<down>,wait \<down>,ok \<down>\<acute>} \<sharp> a" "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
show ?thesis
by(subst CSP_Design, simp_all add: Prefix_rel_closure Prefix_pre Prefix_post Prefix_CSP assms 0) 
qed

subsection {* External Choice laws *}

lemma External_R1: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is R1" "Q is R1"
shows "P \<box> Q is R1"
apply(simp add:is_healthy_def ExternalChoiceCSP_def)
apply(subst CSP2_R1_commute[THEN sym])
apply(simp add:R1_CondR R1_AndP R1_OrP)
apply(metis assms is_healthy_def)
done

lemma External_R2: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is R2" "Q is R2"
shows "P \<box> Q is R2"
apply(simp add:is_healthy_def ExternalChoiceCSP_def)
apply(subst CSP2_R2_commute[THEN sym])
apply(simp add:R2_CondR_alt R2_AndP R2_OrP)
apply(metis assms Stop_R2 is_healthy_def)
done

lemma External_R3c: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is R3c" "Q is R3c"
shows "P \<box> Q is R3c"
apply(simp add:is_healthy_def ExternalChoiceCSP_def)
apply(subst CSP2_R3c_commute[THEN sym])
apply(simp add: R3c_CondR R3c_AndP R3c_OrP)
apply(metis assms is_healthy_def)
done

lemma External_CSP1: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is CSP1" "Q is CSP1"
shows "P \<box> Q is CSP1"
apply(simp add:is_healthy_def ExternalChoiceCSP_def)
apply(subst CSP1_CSP2_commute)
apply(simp add:CSP1_CondR CSP1_AndP CSP1_OrP)
apply(metis assms is_healthy_def)
done

lemma External_CSP2: 
  "P \<box> Q is CSP2"
by(simp add:ExternalChoiceCSP_def is_healthy_def CSP2_idempotent)

lemma External_closure[closure]: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows "P \<box> Q \<in> WF_RELATION"
by(simp add:ExternalChoiceCSP_def closure assms)

lemma External_CSP:
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is CSP" "Q is CSP" 
shows  "P \<box> Q is CSP"
proof -
  have 1: "CSP2 (P \<box> Q) = (P \<box> Q)"
    by(metis is_healthy_def External_CSP2 assms)
  have 2: "CSP1 (P \<box> Q) = (P \<box> Q)"
    by(metis is_healthy_def External_CSP1 assms CSP_is_CSP1)
  have 3: "R3c (P \<box> Q) = (P \<box> Q)" 
    by(metis is_healthy_def External_R3c assms CSP_is_RHc RHc_is_R3c)
  have 4: "R2 (P \<box> Q) = (P \<box> Q)" 
    by(metis is_healthy_def External_R2 assms CSP_is_RHc RHc_is_R2)
  have 5: "R1 (P \<box> Q) = (P \<box> Q)" 
    by(metis is_healthy_def External_R1 assms CSP_is_RHc RHc_is_R1)
  show ?thesis 
  apply(simp add: is_healthy_def CSP_def RHc_def)
  apply (metis 1 2 3 4 5)
  done
qed

lemma External_pre: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows"`CSP_Pre(P \<box> Q)` = `CSP_Pre(P) \<and> CSP_Pre(Q)`"
apply(simp add:ExternalChoiceCSP_def H2_split Stop_design DesignREA_form SkipR_as_SkipRA R2_def R1_def R2s_def)
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing closure)
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing closure)back
apply(simp add:usubst typing defined closure CSP_Pre_def)
apply (metis demorgan1)
done

lemma External_post:
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows "`CSP_Post(P \<box> Q)` = `\<not>CSP_Pre(P) \<or> \<not>CSP_Pre(Q) \<or> ((CSP_Post(P) \<and> CSP_Post(Q)) \<lhd> ($tr\<acute>=$tr) \<and> $wait\<acute> \<rhd> (CSP_Post(P) \<or> CSP_Post(Q)))`"

apply(simp add:ExternalChoiceCSP_def H2_split Stop_design DesignREA_form SkipR_as_SkipRA R2_def R1_def R2s_def)
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing closure)
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing closure)back
apply(simp add:usubst typing defined closure CSP_Post_def CSP_Pre_def)
apply(subst AndP_comm) back
apply(simp add:AndP_assoc[THEN sym] tr_prefix_as_nil CondR_def)
apply(utp_poly_auto_tac)
done

lemma External_design: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is CSP" "Q is CSP"
shows "P \<box> Q = `RHc((CSP_Pre(P) \<and> CSP_Pre(Q)) \<turnstile> ((CSP_Post(P) \<and> CSP_Post(Q)) \<lhd> ($tr\<acute>=$tr) \<and> $wait\<acute> \<rhd> (CSP_Post(P) \<or> CSP_Post(Q))))`"
apply(subst CSP_Design[of "P \<box> Q"],simp_all add: External_CSP closure assms)
apply(simp add:External_pre External_post assms)
apply(simp add:DesignD_form AndP_OrP_distr AndP_OrP_distl AndP_assoc[THEN sym] CondR_def)
apply(subst AndP_comm) back back back
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_comm) back back back back back
apply(subst AndP_comm) back back back back back back back back back
apply(subst AndP_assoc) back back back back back
apply(simp add:AndP_contra)
done

subsection {* Sequential composition *}

lemma Seq_comp_form: 
assumes "P is CSP" "Q is CSP" "P \<in> WF_RELATION" "Q\<in> WF_RELATION"
shows "`P ; Q` = 
`RHc (
          \<not>(\<not> CSP_Pre(P) ; ($tr \<le> $tr\<acute>)) \<and> \<not>(CSP_Post(P) ; (\<not> $wait \<and> \<not> CSP_Pre(Q)))
                                                \<turnstile>
                  CSP_Post(P) ; (II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> CSP_Post(Q))
                                                                                                       )`"
proof - have "`P;Q` = `
     (\<not> $ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     ($ok \<and> $wait \<and> II) \<or>
     ($ok \<and> \<not> $wait \<and> R2 (\<not> CSP_Pre (P)) ; ($tr \<le> $tr\<acute>)) \<or>
     ($ok \<and> \<not> $wait \<and> R2 (CSP_Post (P)) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     ($ok \<and> \<not> $wait \<and> R2 (CSP_Post (P)) ; ($ok \<and> \<not>$wait \<and> R2 (\<not> CSP_Pre (Q)))) \<or>
     ($ok \<and> \<not> $wait \<and> R2 (CSP_Post (P)) ; ($ok \<and> \<not>$wait \<and> R2 (CSP_Post (Q))) \<and> $ok\<acute>) `"
apply(subst CSP_Design,simp add: assms(1))
apply(simp add:DesignREA_form SemiR_OrP_distr Seq_comp_1 assms Seq_comp_2 Seq_comp_3)
apply(simp add: SemiR_AndP_left_precond assms typing defined closure)
apply(subst CSP_Design[of "Q"],simp add:assms(2))
apply(simp add:DesignREA_form AndP_OrP_distl SemiR_OrP_distl SemiR_AndP_right_precond typing defined closure urename AndP_assoc[THEN sym] AndP_contra)
apply(subst SemiR_AndP_right_postcond,simp_all add:typing closure defined)
done
also have "... =`
     (\<not> $ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     ($ok \<and> $wait \<and> II) \<or>
     ($ok \<and> \<not> $wait \<and> R2 (\<not>CSP_Pre(P)) ; ($tr \<le> $tr\<acute>)) \<or>
     ($ok \<and> \<not> $wait \<and> R2 (CSP_Post(P)) ; (\<not> $wait \<and> R2 (\<not>CSP_Pre(Q)))) \<or>
     ($ok \<and> \<not> $wait \<and> (R2 (CSP_Post(P)) \<and> $wait\<acute>) \<and> $ok\<acute>) \<or>
     ($ok \<and> \<not> $wait \<and> R2 (CSP_Post(P)) ; (\<not> $wait \<and> R2 (CSP_Post(Q))) \<and> $ok\<acute>)`"
apply(simp add: SemiR_remove_middle_unrest1[of _ _ "{ok\<down>}"] typing defined closure assms unrest CSP_Post_def CSP_Pre_def)+
apply(subst OrP_assoc) back back back
apply(subst OrP_comm) back back back
apply(subst AndP_comm) back back back back back back back back back back back
apply(subst AndP_assoc) back back back back back
apply(simp add:AndP_OrP_distl AndP_OrP_distr SemiR_OrP_distl SemiR_OrP_distr OrP_assoc[THEN sym] AndP_assoc[THEN sym])
done
also have "...=`
     (\<not> $ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     ($ok \<and> $wait \<and> II) \<or>
     ($ok \<and> \<not> $wait \<and> R2(\<not>(\<not>((\<not>CSP_Pre(P)) ; R2($tr \<le> $tr\<acute>)) \<and> \<not> (CSP_Post(P) ; R2(\<not>CSP_Pre(Q) \<and> \<not>$wait))))) \<or>
     ($ok \<and> \<not> $wait \<and> R2((CSP_Post(P) \<and> $wait\<acute>) \<or> CSP_Post(P) ; R2(CSP_Post(Q)\<and>\<not>$wait)) \<and> $ok\<acute>)`"
apply(simp add:R2_OrP AndP_OrP_distl AndP_OrP_distr demorgan2)
apply(subst R2_sequential_composition[THEN sym],simp_all add:typing closure defined assms)+
apply(simp add:R2_def R2s_AndP R1_extend_AndP[THEN sym])
apply(simp add:R2_def[THEN sym] CSP_Pre_R2_commute[THEN sym] CSP_Post_R2_commute[THEN sym])
apply(simp add:R2s_def usubst typing defined closure OrP_assoc[THEN sym])
apply(subst R2_def,simp_all add:R2s_def R1_def usubst typing defined closure tr_prefix_as_nil) back back back back back back back
apply(subst AndP_comm) back back back back back back back
apply(subst AndP_comm) back back back back back back back back back back back back back back
apply(simp)
done
also have "... = `RHc (\<not> ((\<not> CSP_Pre (P)) ; ($tr \<le> $tr\<acute>)) \<and> \<not> (CSP_Post (P) ; (\<not> $wait \<and> \<not> CSP_Pre ( Q))) \<turnstile>
         (CSP_Post(P) \<and> $wait\<acute>) \<or> CSP_Post (P) ; (\<not> $wait \<and> CSP_Post ( Q)))`"
 apply(subst DesignREA_form[THEN sym])
 apply(simp add:R2_def R2s_AndP R1_extend_AndP[THEN sym])
 apply(simp add:R2_def[THEN sym] CSP_Post_R2_commute[THEN sym] CSP_Pre_R2_commute[THEN sym])
 apply(subst R2_def,simp_all add:R2s_def R1_def usubst typing defined closure tr_prefix_as_nil)
apply(subst AndP_comm) back
apply(subst AndP_comm) back back back
apply(metis assms is_healthy_def CSP_is_RHc RHc_is_R2)
done
also have "... = `RHc (
          \<not>(\<not> CSP_Pre(P) ; ($tr \<le> $tr\<acute>)) \<and> \<not>(CSP_Post(P) ; (\<not> $wait \<and> \<not> CSP_Pre(Q)))
                                                \<turnstile>
                  CSP_Post(P) ; (II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> CSP_Post(Q))
                                                                                                       )`"
apply(simp add:CondR_def SemiR_OrP_distl SemiR_AndP_right_precond typing closure defined urename)
apply(subst SemiR_SkipRA_right,simp_all add:typing defined closure unrest)
apply(rule unrest,simp_all add:typing closure defined unrest CSP_Post_def)
apply(rule unrest) defer 
apply(rule unrest) defer 
apply(rule unrest) defer
apply(subst UNREST_subset[of "{}"])
apply(simp_all add:typing closure defined unrest)
apply(utp_poly_auto_tac)
done
finally show ?thesis .
qed

section {* Prefixed laws *}

lemma Prefixed_pre: 
  assumes "P \<in> WF_RELATION" "P is CSP" "NON_REL_VAR \<sharp> a" "{tr \<down>,tr \<down>\<acute>,ok \<down>,ok \<down>\<acute>,wait \<down>,wait \<down>\<acute>} \<sharp> a"
  shows "CSP_Pre(a \<rightarrow> P) = `\<not>((($tr^\<langle>a\<rangle>=$tr\<acute>) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>);\<not>CSP_Pre(P))`" 
proof - 
have 0:  "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a" "{ok \<down>,wait \<down>,ok \<down>\<acute>} \<sharp> a" "{wait \<down>} \<sharp> a" "{wait \<down>\<acute>} \<sharp> a" "{ok \<down>} \<sharp> a" "{tr \<down>} \<sharp> a""{tr \<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
show ?thesis
apply(simp add:PrefixCSP_def)
apply(subst Seq_comp_form,simp_all add:assms closure Prefix_CSP 0)
apply(simp add:DesignREA_pre Prefix_pre Prefix_post 0 assms)
apply(subst SemiR_AndP_right_precond,simp_all add:typing closure defined urename)
apply(subst AndP_comm) back back
apply(subst CondR_false_cond)
apply(subst AndP_comm)
apply(subst SemiR_AndP_left_UNDASHED,simp_all add:typing defined closure unrest urename)
apply(subst SemiR_remove_middle_unrest1[of _ _ "{wait\<down>}"],simp_all add:typing defined closure unrest assms 0)
apply(subst unrest) back
apply(simp add:typing closure defined unrest assms 0)
apply(subst UNREST_subset[of "-(REL_VAR - REA - OKAY)"])
apply(subst UNREST_SkipRA,simp_all add:typing closure defined)
apply(simp add:assms typing closure defined unrest CSP_Pre_def)
apply(subst CSP_Pre_def,simp add:SubstP_SemiR_left SubstP_SemiR_right typing defined closure unrest)
apply(simp add:typing closure defined usubst PSubstPE_VarP_single_UNREST 0)
apply(subst SubstP_VarP_single_UNREST,simp add:CSP_Pre_def typing defined closure unrest)
apply(subst Healthy_simp[of _ "R2"])
apply(subst R2_SemiR_closure)
apply(simp add:is_healthy_def R2_def R2s_def R1_extend_AndP[THEN sym] usubst typing defined closure)
apply(simp add:R1_def tr_prefix_as_a PSubstPE_VarP_single_UNREST 0)
apply(simp add:is_healthy_def)
apply(subst CSP_Pre_R2_commute[THEN sym])
apply(metis assms is_healthy_def CSP_is_RHc RHc_is_R2)
apply(simp_all add:typing defined closure assms)
done
qed

lemma Prefixed_post: 
  assumes "P \<in> WF_RELATION" "P is CSP" "NON_REL_VAR \<sharp> a" "{tr \<down>,tr \<down>\<acute>,ok \<down>,ok \<down>\<acute>,wait \<down>,wait \<down>\<acute>} \<sharp> a"
  shows "CSP_Post(a \<rightarrow> P) = `
     ((($tr^\<langle>a\<rangle>=$tr\<acute>) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>) ;\<not> CSP_Pre(P)) \<or>
     ($wait\<acute> \<and> a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<or> 
     ((($tr^\<langle>a\<rangle>=$tr\<acute>) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>) ; CSP_Post(P))`" 
proof -
have 0:  "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a" "{ok \<down>,wait \<down>,ok \<down>\<acute>} \<sharp> a" "{wait \<down>} \<sharp> a" "{wait \<down>\<acute>} \<sharp> a" "{ok \<down>} \<sharp> a" "{ok \<down>\<acute>} \<sharp> a" "{tr \<down>} \<sharp> a""{tr \<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
show ?thesis 
apply(simp add:PrefixCSP_def,subst Seq_comp_form,simp_all add:assms closure 0 Prefix_CSP)
apply(simp add:DesignREA_post ImpliesP_def CSP_Post_AndP CSP_Post_NotP CSP_Post_OrP CSP_Post_twice CSP_Post_Pre demorgan1 demorgan2 Prefix_pre Prefix_post 0 assms)
apply(subst CondR_def) back back
apply(simp add:SemiR_OrP_distl)
apply(subst SemiR_AndP_right_precond,simp_all add:typing defined closure urename)
apply(subst SemiR_AndP_right_precond,simp_all add:typing defined closure urename)
apply(subst SemiR_AndP_right_precond,simp_all add:typing defined closure urename)
apply(subst AndP_comm) back back
apply(simp add:CondR_false_cond)
apply(subst AndP_comm)
apply(subst SemiR_AndP_left_UNDASHED,simp_all add:typing defined closure urename unrest)
apply(subst SemiR_remove_middle_unrest1[of _ _ "{wait\<down>}"],simp_all add:typing defined closure unrest assms 0)defer defer
apply(subst OrP_comm)
apply(subst AndP_comm) back back
apply(subst CondR_true_cond)
apply(subst SemiR_SkipRA_right,simp_all add:typing defined closure unrest)
apply(subst UNREST_subset[of "{ok\<down>\<acute>}"],simp_all add:typing defined closure unrest 0)
apply(utp_poly_auto_tac)
apply(subst OrP_comm)
apply(subst AndP_comm) back back
apply(subst CondR_false_cond)
apply(subst AndP_comm)
apply(subst SemiR_AndP_left_UNDASHED,simp_all add:typing closure defined unrest urename)
apply(subst SemiR_remove_middle_unrest1[of _ _ "{wait\<down>}"],simp_all add:typing defined closure unrest assms 0)
apply(rule unrest) back defer
apply(subst UNREST_subset[of "-(REL_VAR - REA - OKAY)"],subst UNREST_SkipRA)
apply(simp_all add:typing defined closure unrest)
apply(simp add:typing defined closure unrest CSP_Post_def)
apply(simp add:CSP_Post_OrP[THEN sym])
apply(subst CSP_Post_def,simp add:SubstP_OrP)
apply(simp add:SubstP_SemiR_left SubstP_SemiR_right typing defined closure unrest)
apply(simp add:usubst typing defined closure PSubstPE_VarP_single_UNREST 0)
apply(subst SubstP_VarP_single_UNREST,simp add:CSP_Post_def unrest typing closure defined)
apply(subst SubstP_VarP_single_UNREST,simp add:CSP_Pre_def unrest typing closure defined)
apply(subst OrP_comm) back
apply(subst OrP_comm) back
apply(subst Healthy_simp[of _ "R2"]) defer
apply(simp)
apply(rule unrest) back defer
apply(subst UNREST_subset[of "-(REL_VAR - REA - OKAY)"],subst UNREST_SkipRA)
apply(simp_all add:typing closure defined unrest assms 0)
apply(simp add:unrest typing closure defined CSP_Pre_def)
apply(subst R2_OrP_closure)
apply(subst R2_SemiR_closure)
apply(simp add:is_healthy_def R2s_def usubst typing defined closure R2_def R1_extend_AndP[THEN sym])
apply(simp add:R1_def tr_prefix_as_a PSubstPE_VarP_single_UNREST 0)
apply(simp add:is_healthy_def CSP_Pre_R2_commute[THEN sym])
apply(metis assms is_healthy_def CSP_is_RHc RHc_is_R2)
apply(simp_all add:closure typing defined assms 0)
apply(subst R2_OrP_closure)
apply(simp add:R2_def R2s_def usubst typing closure defined is_healthy_def R1_def tr_prefix_as_nil PSubstPE_VarP_single_UNREST 0 AndP_assoc[THEN sym])
apply(subst R2_SemiR_closure)
apply(simp add:is_healthy_def R2s_def usubst typing defined closure R2_def R1_extend_AndP[THEN sym])
apply(simp add:R1_def tr_prefix_as_a PSubstPE_VarP_single_UNREST 0)
apply(simp add:CSP_Post_R2_commute[THEN sym] is_healthy_def)
apply(metis assms is_healthy_def CSP_is_RHc RHc_is_R2)
apply(simp_all add:closure typing defined assms 0)
done
qed

lemma Prefixed_CSP: 
  assumes "P is CSP" "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a" "NON_REL_VAR \<sharp> a" "P \<in> WF_RELATION"
  shows "a \<rightarrow> P is CSP" 
apply(simp add:PrefixCSP_def)
apply(subst CSP_SemiR_closure,simp_all add:closure assms Prefix_CSP)
done

lemma Prefixed_design: 
  assumes "P \<in> WF_RELATION" "P is CSP" "NON_REL_VAR \<sharp> a" "{tr \<down>,tr \<down>\<acute>,ok \<down>,ok \<down>\<acute>,wait \<down>,wait \<down>\<acute>} \<sharp> a"
  shows "a \<rightarrow> P = 
    `RHc (
                     \<not>((($tr^\<langle>a\<rangle>=$tr\<acute>) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>);\<not>CSP_Pre(P)) 
                                                 \<turnstile> 
       ($wait\<acute> \<and> a \<notin> $ref\<acute> \<and> $tr\<acute> = $tr) \<or> (($tr^\<langle>a\<rangle>=$tr\<acute>) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>) ; CSP_Post(P)
                                                                                     )`"
proof -
have 0:  "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a" "{ok \<down>,wait \<down>,ok \<down>\<acute>} \<sharp> a" "{wait \<down>} \<sharp> a" "{wait \<down>\<acute>} \<sharp> a" "{ok \<down>} \<sharp> a" "{ok \<down>\<acute>} \<sharp> a" "{tr \<down>} \<sharp> a""{tr \<down>\<acute>} \<sharp> a" "{tr \<down>,tr \<down>\<acute>,ok \<down>,ok \<down>\<acute>,wait \<down>,wait \<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
show ?thesis
apply(subst CSP_Design)
apply(simp add: Prefixed_CSP 0 assms)  
apply(simp add:Prefixed_pre Prefixed_post assms 0)
apply(subst DesignREA_Pre_Post)
apply(simp add:AndP_OrP_distl)
apply(subst AndP_comm) back back
apply(subst AndP_contra,simp add:AndP_OrP_distl[THEN sym])
apply(subst DesignREA_Pre_Post[THEN sym])
apply(simp)
done
qed

subsection {*Internal laws *}

lemma Internal_pre:
  assumes "P is CSP" "Q is CSP" "P \<in>REL" "Q \<in> REL"
  shows "`CSP_Pre(P  \<sqinter> Q)` = `CSP_Pre(P) \<and> CSP_Pre(Q)`"
by(subst eval,simp add:CSP_Pre_def SubstP_OrP demorgan1)

lemma Internal_post:
  assumes "P is CSP" "Q is CSP" "P \<in> REL" "Q \<in> REL"
  shows "`CSP_Post(P  \<sqinter> Q)` = `CSP_Post(P) \<or> CSP_Post(Q)`"
by(subst eval,simp add:CSP_Post_def SubstP_OrP)

lemma Internal_CSP:
  assumes "P is CSP" "Q is CSP" "P \<in> REL" "Q \<in> REL"
  shows "`P \<sqinter> Q` is CSP"
apply(simp add:is_healthy_def)
apply(subst eval) back
apply(subst eval) back
apply(simp add:CSP_def RHc_def R3c_OrP R2_OrP R1_OrP H2_OrP CSP1_OrP)
apply(metis assms is_healthy_def CSP_is_CSP1 CSP_is_CSP2 CSP_is_RHc RHc_is_R3c RHc_is_R2 RHc_is_R1)
done

lemma Internal_design:
  assumes "P is CSP" "Q is CSP" "P \<in> REL" "Q \<in> REL"
  shows "`P \<sqinter> Q` = `RHc( CSP_Pre(P) \<and> CSP_Pre(Q) \<turnstile> CSP_Post(P) \<or> CSP_Post(Q) )`"
by(subst CSP_Design,simp_all add:assms Internal_pre Internal_post Internal_CSP) 

subsection {* Guard laws *}

lemma Guard_R1: 
  assumes "P is R1"
  shows "`[g] & P` is R1"
apply(simp add: GuardCSP_def is_healthy_def)
apply(subst R1_CondR,metis assms is_healthy_def Stop_R1)
done

lemma Guard_R2: 
  assumes "P is R2" "g is R2s"
  shows "`[g] & P` is R2"
apply(simp add: GuardCSP_def is_healthy_def)
apply(subst R2_CondR)
apply(metis assms is_healthy_def Stop_R2)
done

lemma Guard_R3c: 
  assumes "P is R3c"
  shows "`[g] & P` is R3c"
apply(simp add: GuardCSP_def is_healthy_def)
apply(subst R3c_CondR)
apply(metis assms is_healthy_def Stop_R3c)
done

lemma Guard_CSP1: 
  assumes "P is CSP1"
  shows "`[g] & P` is CSP1"
apply(simp add: GuardCSP_def is_healthy_def)
apply(subst CSP1_CondR)
apply(metis assms is_healthy_def Stop_CSP1)
done

lemma Guard_CSP2: 
  assumes "P is CSP2" "{ok\<down>\<acute>} \<sharp> g"
  shows "`[g] & P` is CSP2"
proof -
have 0: "P = CSP2(P)" by (metis assms is_healthy_def)
have 1: "STOP = CSP2(STOP)" by (metis Stop_CSP2 is_healthy_def)
show ?thesis
apply(simp add: GuardCSP_def is_healthy_def CondR_def)
apply(subst 0) back
apply(subst 1) back
apply(simp add:H2_split Stop_design DesignREA_form R2_def R2s_def R1_extend_AndP[THEN sym] usubst SkipR_as_SkipRA typing defined closure)
apply(simp add:R1_def usubst typing defined closure tr_prefix_as_nil)
apply(subst SubstP_VarP_single_UNREST,simp add:assms)+
apply(utp_poly_auto_tac)
done
qed

lemma Guard_CSP:
assumes "P \<in> WF_RELATION" "P is CSP" "{ok\<down>\<acute>} \<sharp> g" "g is R2s"
shows  "`[g] & P` is CSP"
proof -
  have 1: "`CSP2 ([g] & P)` = `([g] & P)`"
    by(metis is_healthy_def Guard_CSP2 assms CSP_is_CSP2)
  have 2: "`CSP1 ([g] & P)` = `([g] & P)`"
    by(metis is_healthy_def Guard_CSP1 assms CSP_is_CSP1)
  have 3: "`R3c ([g] & P)` = `([g] & P)`" 
    by(metis is_healthy_def Guard_R3c assms CSP_is_RHc RHc_is_R3c)
  have 4: "`R2 ([g] & P)` = `([g] & P)`" 
    by(metis is_healthy_def Guard_R2 assms CSP_is_RHc RHc_is_R2)
  have 5: "`R1([g] & P)` = `([g] & P)`" 
    by(metis is_healthy_def Guard_R1 assms CSP_is_RHc RHc_is_R1)
  show ?thesis 
  apply(simp add: is_healthy_def CSP_def RHc_def)
  apply (metis 1 2 3 4 5)
  done
qed

lemma Guard_pre:
  assumes "{ok\<down>\<acute>} \<sharp> g"
  shows "`CSP_Pre([g] & P)` = `g[true/ok][false/wait] \<Rightarrow> CSP_Pre(P)`"
apply(simp add:GuardCSP_def CondR_def CSP_Pre_OrP CSP_Pre_AndP Stop_pre)
apply(subst CSP_Pre_def)
apply(subst SubstP_VarP_single_UNREST,simp add:assms)
apply(simp add:ImpliesP_def[THEN sym])
done

lemma Guard_post:
  assumes "{ok\<down>\<acute>} \<sharp> g"
  shows "`CSP_Post([g] & P)` = `CSP_Post(P) \<lhd> g[true/ok][false/wait] \<rhd> (($tr\<acute> = $tr) \<and> $wait\<acute>)`"
apply(simp add:GuardCSP_def CondR_def CSP_Post_OrP CSP_Post_AndP Stop_post)
apply(subst CSP_Post_def)
apply(subst SubstP_VarP_single_UNREST,simp add:assms)
apply(subst CSP_Post_def) back
apply(subst SubstP_VarP_single_UNREST,simp add:assms unrest)
apply(simp add:usubst CondR_def[THEN sym])
done

lemma Guard_design:
  assumes "P \<in> WF_RELATION" "P is CSP" "{ok\<down>\<acute>} \<sharp> g" "g is R2s"
  shows "`[g] & P` = ` RHc ((g[true/ok][false/wait] \<Rightarrow> CSP_Pre(P)) \<turnstile>
         (CSP_Post(P) \<lhd> g[true/ok][false/wait] \<rhd> (($tr\<acute> = $tr) \<and> $wait\<acute>)))`"
apply(subst CSP_Design,subst Guard_CSP,simp_all add:assms)
apply(simp add:Guard_pre Guard_post assms) 
done

end